#!/usr/bin/env julia
# replay.jl — Read a JSON proof trace and emit a .lean file
#
# Usage:
#   julia replay.jl trace.json > lean/Generated.lean
#   julia replay.jl trace.json theorem_name > lean/Generated.lean
#   julia replay.jl trace.json theorem_name Namespace > lean/Generated.lean

using JSON

# ─────────────────────────────────────────────────────────────
# Read trace
# ─────────────────────────────────────────────────────────────

function read_trace(io::IO)
    JSON.parse(io)
end

function read_trace(path::String)
    open(read_trace, path)
end

# ─────────────────────────────────────────────────────────────
# Lean code generation helpers
# ─────────────────────────────────────────────────────────────

"""Convert a JSON index to Lean syntax: ⟨"name", .up/.down⟩"""
function lean_index(idx::Dict)
    pos = idx["position"] == "up" ? ".up" : ".down"
    """⟨"$(idx["name"])", $pos⟩"""
end

"""Convert a JSON TExpr to Lean syntax using idx_* def names."""
function lean_expr(e::Dict)
    t = e["type"]
    if t == "zero"
        "zero"
    elseif t == "scalar"
        "scalar $(e["num"]) $(e["den"])"
    elseif t == "tensor"
        idxs = join([lean_idx_name(i["name"]) for i in e["indices"]], ", ")
        """tensor "$(e["name"])" [$idxs]"""
    elseif t == "smul"
        "smul $(e["num"]) $(e["den"]) ($(lean_expr(e["expr"])))"
    elseif t == "sum"
        "sum ($(lean_expr(e["left"]))) ($(lean_expr(e["right"])))"
    else
        error("Unknown TExpr type: $t")
    end
end

"""Collect all unique indices from a TExpr JSON."""
function collect_indices(e::Dict)
    idxs = Dict{String, Dict}()
    _collect!(idxs, e)
    idxs
end

function _collect!(idxs::Dict, e::Dict)
    t = e["type"]
    if t == "tensor"
        for idx in e["indices"]
            idxs[idx["name"]] = idx
        end
    elseif t == "smul"
        _collect!(idxs, e["expr"])
    elseif t == "sum"
        _collect!(idxs, e["left"])
        _collect!(idxs, e["right"])
    end
end

"""Generate a sanitized Lean identifier for an index name."""
lean_idx_name(name::String) = "idx_$name"

"""Generate Lean expr using idx_name refs (for theorem statement)."""
function lean_expr_with_names(e::Dict)
    t = e["type"]
    if t == "zero"
        "zero"
    elseif t == "scalar"
        "scalar $(e["num"]) $(e["den"])"
    elseif t == "tensor"
        idxs = join([lean_idx_name(i["name"]) for i in e["indices"]], ", ")
        """tensor "$(e["name"])" [$idxs]"""
    elseif t == "smul"
        "smul $(e["num"]) $(e["den"]) ($(lean_expr_with_names(e["expr"])))"
    elseif t == "sum"
        "sum ($(lean_expr_with_names(e["left"]))) ($(lean_expr_with_names(e["right"])))"
    else
        error("Unknown TExpr type: $t")
    end
end

# ─────────────────────────────────────────────────────────────
# Tree navigation
# ─────────────────────────────────────────────────────────────

"""Get subtree at path in a JSON expr."""
function get_at_path(e::Dict, path::Vector)
    isempty(path) && return e
    p = path[1]
    rest = path[2:end]
    t = e["type"]
    if t == "sum"
        get_at_path(p == 0 ? e["left"] : e["right"], rest)
    elseif t == "smul"
        get_at_path(e["expr"], rest)
    else
        error("Cannot descend into $t")
    end
end

"""Replace subtree at path in JSON expr."""
function replace_at_path(e::Dict, path::Vector, new_node::Dict)
    isempty(path) && return new_node
    p = path[1]
    rest = path[2:end]
    t = e["type"]
    if t == "sum"
        if p == 0
            Dict("type" => "sum", "left" => replace_at_path(e["left"], rest, new_node), "right" => e["right"])
        else
            Dict("type" => "sum", "left" => e["left"], "right" => replace_at_path(e["right"], rest, new_node))
        end
    elseif t == "smul"
        Dict("type" => "smul", "num" => e["num"], "den" => e["den"],
             "expr" => replace_at_path(e["expr"], rest, new_node))
    else
        error("Cannot descend into $t at path $path")
    end
end

"""Get the tensor at a swap step target."""
function get_swap_info(expr::Dict, step::Dict)
    path = Int.(step["path"])
    target = get_at_path(expr, path)
    s1, s2 = step["slot1"], step["slot2"]  # already 0-indexed

    if target["type"] == "tensor"
        swapped_idxs = target["indices"]
    elseif target["type"] == "smul"
        swapped_idxs = target["expr"]["indices"]
    else
        error("SwapSlots target is not a tensor or smul: $(target["type"])")
    end

    # The canonical indices are the swapped-back version
    canon_idxs = copy(swapped_idxs)
    canon_idxs[s1+1], canon_idxs[s2+1] = canon_idxs[s2+1], canon_idxs[s1+1]

    return swapped_idxs, canon_idxs, s1, s2
end

# ─────────────────────────────────────────────────────────────
# Lean proof generation
# ─────────────────────────────────────────────────────────────

function generate_lean(trace::Dict; theorem_name::String="generated_proof",
                       namespace::Union{String,Nothing}=nothing)
    lines = String[]

    push!(lines, "import MicroTensor")
    push!(lines, "import Rules")
    push!(lines, "")
    push!(lines, "open TExpr")
    push!(lines, "")
    if namespace !== nothing
        push!(lines, "namespace $namespace")
        push!(lines, "")
    end

    # Collect all indices and generate defs
    indices = collect_indices(trace["expr"])
    for name in sort(collect(keys(indices)))
        idx = indices[name]
        pos = idx["position"] == "up" ? ".up" : ".down"
        push!(lines, """def $(lean_idx_name(name)) : Index := ⟨"$name", $pos⟩""")
    end
    push!(lines, "")

    # Generate theorem statement
    lhs = lean_expr_with_names(trace["expr"])
    rhs = lean_expr_with_names(trace["result"])
    push!(lines, "theorem $theorem_name :")
    push!(lines, "    $lhs = $rhs := by")

    # Pre-process: find bare tensors that need tensor_as_smul before a swap.
    # If there's a swap followed by collect, the collect's tensor_as_smul must
    # come BEFORE the swap (when indices differ) to avoid rw clobbering nested terms.
    steps = trace["steps"]
    current_expr = trace["expr"]
    tensor_as_smul_emitted = Set{String}()  # track which paths got tensor_as_smul

    for (i, step) in enumerate(steps)
        rule = step["rule"]

        if rule == "swap_slots"
            swapped_idxs, canon_idxs, s1, s2 = get_swap_info(current_expr, step)
            tensor_name = step["tensor"]
            swap_path = Int.(step["path"])

            # Look ahead: if next step is collect at the parent, emit tensor_as_smul
            # for the sibling summand BEFORE the swap
            if i < length(steps) && steps[i+1]["rule"] == "collect"
                collect_path = Int.(steps[i+1]["path"])
                sum_node = get_at_path(current_expr, collect_path)
                if sum_node["type"] == "sum"
                    # The swap targets one child. Find the other.
                    # swap_path relative to collect_path tells us which child
                    rel = swap_path[length(collect_path)+1:end]
                    if length(rel) >= 1
                        sibling_idx = 1 - rel[1]  # 0→1, 1→0
                        sibling = sibling_idx == 0 ? sum_node["left"] : sum_node["right"]
                        if sibling["type"] == "tensor"
                            idxs_lean = "[" * join([lean_idx_name(idx["name"]) for idx in sibling["indices"]], ", ") * "]"
                            push!(lines, "  -- Normalize bare tensor to smul form (before swap, indices differ)")
                            push!(lines, """  rw [tensor_as_smul "$(sibling["name"])" $idxs_lean]""")
                            # Update the expression
                            sibling_path = vcat(collect_path, [sibling_idx])
                            current_expr = replace_at_path(current_expr, sibling_path,
                                Dict("type" => "smul", "num" => 1, "den" => 1, "expr" => sibling))
                            tensor_as_smul_emitted = true
                        end
                    end
                end
            end

            # Emit the swap step
            swapped_lean = "[" * join([lean_idx_name(idx["name"]) for idx in swapped_idxs], ", ") * "]"
            canon_lean = "[" * join([lean_idx_name(idx["name"]) for idx in canon_idxs], ", ") * "]"

            push!(lines, "  -- Step $i: swap slots $s1,$s2 of $tensor_name")
            push!(lines, "  have h$i : $swapped_lean = ($canon_lean).swap $s1 $s2 := by native_decide")
            push!(lines, "  rw [h$i]")
            push!(lines, """  rw [antisym_swap "$tensor_name" $canon_lean $s1 $s2 (by decide) (by decide)]""")

            # Update current expr
            target = get_at_path(current_expr, swap_path)
            if target["type"] == "tensor"
                new_node = Dict("type" => "smul", "num" => -1, "den" => 1,
                    "expr" => Dict("type" => "tensor", "name" => tensor_name, "indices" => canon_idxs))
            elseif target["type"] == "smul"
                new_node = Dict("type" => "smul", "num" => target["num"] * -1, "den" => target["den"],
                    "expr" => Dict("type" => "tensor", "name" => tensor_name, "indices" => canon_idxs))
            end
            current_expr = replace_at_path(current_expr, swap_path, new_node)

        elseif rule == "collect"
            path = Int.(step["path"])
            sum_node = get_at_path(current_expr, path)
            left = sum_node["left"]
            right = sum_node["right"]

            push!(lines, "  -- Step $i: collect")

            # If left is still a bare tensor (tensor_as_smul wasn't hoisted), handle it
            if left["type"] == "tensor"
                idxs_lean = "[" * join([lean_idx_name(idx["name"]) for idx in left["indices"]], ", ") * "]"
                push!(lines, """  conv_lhs => arg 1; rw [tensor_as_smul "$(left["name"])" $idxs_lean]""")
                left = Dict("type" => "smul", "num" => 1, "den" => 1, "expr" => left)
            end

            a_n = left["num"]
            a_d = left["den"]
            b_n = right["num"]
            b_d = right["den"]
            inner = lean_expr(left["expr"])
            push!(lines, "  rw [collect_smul $a_n $a_d ($b_n) $b_d ($inner)]")

            # Update current expr
            new_num = a_n * b_d + b_n * a_d
            new_den = a_d * b_d
            current_expr = replace_at_path(current_expr, path,
                Dict("type" => "smul", "num" => new_num, "den" => new_den, "expr" => left["expr"]))

        elseif rule == "zero_elim"
            push!(lines, "  -- Step $i: zero elimination")
            path = Int.(step["path"])
            node = get_at_path(current_expr, path)
            # Use exact instead of rw — the kernel reduces the arithmetic
            den = node["den"]
            inner = lean_expr(node["expr"])
            push!(lines, "  exact smul_zero ($den) ($inner)")
            current_expr = replace_at_path(current_expr, path, Dict("type" => "zero"))

        elseif rule == "sum_zero"
            push!(lines, "  -- Step $i: sum with zero")
            path = Int.(step["path"])
            sum_node = get_at_path(current_expr, path)
            if sum_node["left"]["type"] == "zero"
                push!(lines, "  rw [sum_zero_left]")
                current_expr = replace_at_path(current_expr, path, sum_node["right"])
            else
                push!(lines, "  rw [sum_zero_right]")
                current_expr = replace_at_path(current_expr, path, sum_node["left"])
            end
        end
    end

    if namespace !== nothing
        push!(lines, "")
        push!(lines, "end $namespace")
    end

    push!(lines, "")
    join(lines, "\n") * "\n"
end

# ─────────────────────────────────────────────────────────────
# Main
# ─────────────────────────────────────────────────────────────

function main()
    trace = if length(ARGS) >= 1
        read_trace(ARGS[1])
    else
        read_trace(stdin)
    end

    name = length(ARGS) >= 2 ? ARGS[2] : "generated_proof"
    ns = length(ARGS) >= 3 ? ARGS[3] : nothing
    print(generate_lean(trace; theorem_name=name, namespace=ns))
end

main()
