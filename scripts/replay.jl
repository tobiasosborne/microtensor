#!/usr/bin/env julia
# replay.jl — Read a JSON proof trace and emit a .lean file
#
# Usage:
#   julia replay.jl trace.json > lean/Generated.lean
#   julia replay.jl < trace.json > lean/Generated.lean

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

"""Convert a JSON TExpr to Lean syntax."""
function lean_expr(e::Dict)
    t = e["type"]
    if t == "zero"
        "zero"
    elseif t == "scalar"
        "scalar $(e["num"]) $(e["den"])"
    elseif t == "tensor"
        idxs = join([lean_index(i) for i in e["indices"]], ", ")
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

# ─────────────────────────────────────────────────────────────
# Track expression state through proof steps
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

"""Apply a swap step to get the canonical (un-swapped) indices."""
function get_swap_info(expr::Dict, step::Dict)
    path = Int.(step["path"])
    target = get_at_path(expr, path)
    s1, s2 = step["slot1"], step["slot2"]  # already 0-indexed

    # Get the indices of the target tensor
    if target["type"] == "tensor"
        swapped_idxs = target["indices"]
    elseif target["type"] == "smul"
        swapped_idxs = target["expr"]["indices"]
    else
        error("SwapSlots target is not a tensor or smul: $(target["type"])")
    end

    # The canonical indices are the swapped-back version
    canon_idxs = copy(swapped_idxs)
    canon_idxs[s1+1], canon_idxs[s2+1] = canon_idxs[s2+1], canon_idxs[s1+1]  # +1 for Julia indexing

    return swapped_idxs, canon_idxs, s1, s2
end

# ─────────────────────────────────────────────────────────────
# Generate the .lean file
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
    lhs = lean_expr_with_idx_names(trace["expr"])
    rhs = lean_expr_with_idx_names(trace["result"])
    push!(lines, "theorem $theorem_name :")
    push!(lines, "    $lhs = $rhs := by")

    # Generate proof steps
    current_expr = trace["expr"]
    for (i, step) in enumerate(trace["steps"])
        rule = step["rule"]
        if rule == "swap_slots"
            swapped_idxs, canon_idxs, s1, s2 = get_swap_info(current_expr, step)
            tensor_name = step["tensor"]

            # Emit: have h : [swapped] = [canon].swap s1 s2 := by native_decide
            swapped_lean = "[" * join([lean_index(i) for i in swapped_idxs], ", ") * "]"
            canon_lean = "[" * join([lean_index(i) for i in canon_idxs], ", ") * "]"

            push!(lines, "  -- Step $i: swap slots $s1,$s2 of $tensor_name")
            push!(lines, "  have h$i : $swapped_lean = $canon_lean |>.swap $s1 $s2 := by native_decide")
            push!(lines, "  rw [h$i]")
            push!(lines, """  rw [antisym_swap "$tensor_name" $canon_lean $s1 $s2 (by omega) (by omega)]""")

            # Update current expr: replace the target with smul(-1, 1, tensor(name, canon_idxs))
            current_expr = apply_swap_to_json(current_expr, step, canon_idxs)

        elseif rule == "collect"
            # First normalize the bare tensor to smul form
            path = Int.(step["path"])
            sum_node = get_at_path(current_expr, path)

            # Check if left needs tensor_as_smul
            left = sum_node["left"]
            right = sum_node["right"]

            if left["type"] == "tensor"
                idxs_lean = "[" * join([lean_index(i) for i in left["indices"]], ", ") * "]"
                push!(lines, "  -- Step $i: collect")
                push!(lines, """  rw [tensor_as_smul "$(left["name"])" $idxs_lean]""")
                # Update left to smul form
                left = Dict("type" => "smul", "num" => 1, "den" => 1, "expr" => left)
            else
                push!(lines, "  -- Step $i: collect")
            end

            # Now emit collect_smul
            a_n = left["num"]
            a_d = left["den"]
            b_n = right["num"]
            b_d = right["den"]
            inner = lean_expr_raw(left["expr"])
            push!(lines, "  rw [collect_smul $a_n $a_d ($b_n) $b_d ($inner)]")

            # Update current expr
            new_num = a_n * b_d + b_n * a_d
            new_den = a_d * b_d
            current_expr = replace_at_path(current_expr, path,
                Dict("type" => "smul", "num" => new_num, "den" => new_den, "expr" => left["expr"]))

        elseif rule == "zero_elim"
            push!(lines, "  -- Step $i: zero elimination")
            push!(lines, "  rw [smul_zero]")
            path = Int.(step["path"])
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

"""Generate Lean expr using idx_name refs (for theorem statement)."""
function lean_expr_with_idx_names(e::Dict)
    t = e["type"]
    if t == "zero"
        "zero"
    elseif t == "scalar"
        "scalar $(e["num"]) $(e["den"])"
    elseif t == "tensor"
        idxs = join([lean_idx_name(i["name"]) for i in e["indices"]], ", ")
        """tensor "$(e["name"])" [$idxs]"""
    elseif t == "smul"
        "smul $(e["num"]) $(e["den"]) ($(lean_expr_with_idx_names(e["expr"])))"
    elseif t == "sum"
        "sum ($(lean_expr_with_idx_names(e["left"]))) ($(lean_expr_with_idx_names(e["right"])))"
    else
        error("Unknown TExpr type: $t")
    end
end

"""Generate raw Lean expr (inline index literals)."""
function lean_expr_raw(e::Dict)
    t = e["type"]
    if t == "zero"
        "zero"
    elseif t == "scalar"
        "scalar $(e["num"]) $(e["den"])"
    elseif t == "tensor"
        idxs = join([lean_index(i) for i in e["indices"]], ", ")
        """tensor "$(e["name"])" [$idxs]"""
    elseif t == "smul"
        "smul $(e["num"]) $(e["den"]) ($(lean_expr_raw(e["expr"])))"
    elseif t == "sum"
        "sum ($(lean_expr_raw(e["left"]))) ($(lean_expr_raw(e["right"])))"
    else
        error("Unknown TExpr type: $t")
    end
end

"""Apply swap step to JSON expr (track state)."""
function apply_swap_to_json(expr::Dict, step::Dict, canon_idxs)
    path = Int.(step["path"])
    target = get_at_path(expr, path)
    tensor_name = step["tensor"]

    if target["type"] == "tensor"
        new_node = Dict("type" => "smul", "num" => -1, "den" => 1,
            "expr" => Dict("type" => "tensor", "name" => tensor_name, "indices" => canon_idxs))
    elseif target["type"] == "smul"
        old_num = target["num"]
        old_den = target["den"]
        new_node = Dict("type" => "smul", "num" => old_num * -1, "den" => old_den * 1,
            "expr" => Dict("type" => "tensor", "name" => tensor_name, "indices" => canon_idxs))
    end

    replace_at_path(expr, path, new_node)
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

# ─────────────────────────────────────────────────────────────
# Main
# ─────────────────────────────────────────────────────────────

function main()
    trace = if length(ARGS) >= 1
        read_trace(ARGS[1])
    else
        read_trace(stdin)
    end

    # Use theorem name and optional namespace from CLI
    name = length(ARGS) >= 2 ? ARGS[2] : "generated_proof"
    ns = length(ARGS) >= 3 ? ARGS[3] : nothing
    print(generate_lean(trace; theorem_name=name, namespace=ns))
end

main()
