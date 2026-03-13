#!/usr/bin/env julia
# replay.jl — Read a JSON proof trace and emit a .lean file
#
# The generated proof works by evaluating tensor expressions into a ℚ-module
# via TExpr.eval, then using the environment's antisymmetry constraints and
# Mathlib's module algebra to close the goal.
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

"""Convert a JSON TExpr to Lean syntax using idx_* def names."""
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

"""Compute cyclic permutation of 3 positions (0-indexed): i←k, j←i, k←j."""
function cyclic_perm3_indices(indices::Vector, s1::Int, s2::Int, s3::Int)
    # s1, s2, s3 are 0-indexed here (from JSON)
    result = copy(indices)
    result[s1+1] = indices[s3+1]
    result[s2+1] = indices[s1+1]
    result[s3+1] = indices[s2+1]
    return result
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
# Lean proof generation (eval-based)
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

    # Module variable
    push!(lines, "variable {M : Type*} [AddCommGroup M] [Module ℚ M] (env : TEnv M)")
    push!(lines, "")

    # Generate theorem statement with eval
    lhs = lean_expr_with_names(trace["expr"])
    rhs = lean_expr_with_names(trace["result"])
    push!(lines, "theorem $theorem_name :")
    push!(lines, "    ($lhs).eval env =")
    push!(lines, "    ($rhs).eval env := by")

    # Step 1: Unfold eval to module operations
    push!(lines, "  simp only [TExpr.eval]")

    # Step 2: Process swap steps — emit swap_neg rewrites
    steps = trace["steps"]
    current_expr = trace["expr"]
    swap_count = 0

    bianchi_used = false

    for (i, step) in enumerate(steps)
        rule = step["rule"]

        if rule == "swap_slots"
            swap_count += 1
            swapped_idxs, canon_idxs, s1, s2 = get_swap_info(current_expr, step)
            tensor_name = step["tensor"]
            n = length(canon_idxs)

            swapped_lean = "[" * join([lean_idx_name(idx["name"]) for idx in swapped_idxs], ", ") * "]"
            canon_lean = "[" * join([lean_idx_name(idx["name"]) for idx in canon_idxs], ", ") * "]"

            push!(lines, "  have hs$swap_count : $swapped_lean = ($canon_lean).swap $s1 $s2 := by native_decide")
            push!(lines, """  rw [hs$swap_count, env.swap_neg "$tensor_name" $canon_lean $s1 $s2 (by decide) (by decide)]""")

            # Update current expr (swap applied)
            path = Int.(step["path"])
            target = get_at_path(current_expr, path)
            if target["type"] == "tensor"
                new_node = Dict("type" => "smul", "num" => -1, "den" => 1,
                    "expr" => Dict("type" => "tensor", "name" => tensor_name, "indices" => canon_idxs))
            elseif target["type"] == "smul"
                new_node = Dict("type" => "smul", "num" => target["num"] * -1, "den" => target["den"],
                    "expr" => Dict("type" => "tensor", "name" => tensor_name, "indices" => canon_idxs))
            end
            current_expr = replace_at_path(current_expr, path, new_node)

        elseif rule == "bianchi_cyclic"
            bianchi_used = true
            tensor_name = step["tensor"]
            s1, s2, s3 = step["slot1"], step["slot2"], step["slot3"]

            # Get the three terms from the sum structure
            path = Int.(step["path"])
            target = get_at_path(current_expr, path)

            # Extract the original (first) term's indices
            first_term = target["left"]
            if first_term["type"] == "tensor"
                orig_idxs = first_term["indices"]
            elseif first_term["type"] == "smul"
                orig_idxs = first_term["expr"]["indices"]
            end

            orig_lean = "[" * join([lean_idx_name(idx["name"]) for idx in orig_idxs], ", ") * "]"

            # Compute the cyclic permutations
            perm1_idxs = cyclic_perm3_indices(orig_idxs, s1, s2, s3)
            perm2_idxs = cyclic_perm3_indices(perm1_idxs, s1, s2, s3)

            perm1_lean = "[" * join([lean_idx_name(idx["name"]) for idx in perm1_idxs], ", ") * "]"
            perm2_lean = "[" * join([lean_idx_name(idx["name"]) for idx in perm2_idxs], ", ") * "]"

            push!(lines, "  have h1 : $perm1_lean = ($orig_lean).cyclicPerm3 $s1 $s2 $s3 := by native_decide")
            push!(lines, "  have h2 : $perm2_lean = (($orig_lean).cyclicPerm3 $s1 $s2 $s3).cyclicPerm3 $s1 $s2 $s3 := by native_decide")
            push!(lines, "  rw [h1, h2]")
            push!(lines, """  exact env.bianchi "$tensor_name" $orig_lean $s1 $s2 $s3 (by decide) (by decide) (by decide)""")
        end
        # collect, zero_elim, sum_zero are handled by the closing tactic
    end

    # Step 3: Close the goal (not needed if bianchi was used — it closes directly)
    if !bianchi_used
        if swap_count == 1 && length(steps) <= 3
            push!(lines, "  exact add_neg_cancel _")
        else
            push!(lines, "  simp [ratCoeff, add_neg_cancel, neg_add_cancel]")
        end
    end

    if namespace !== nothing
        push!(lines, "")
        push!(lines, "end $namespace")
    end

    push!(lines, "")
    join(lines, "\n") * "\n"
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

    name = length(ARGS) >= 2 ? ARGS[2] : "generated_proof"
    ns = length(ARGS) >= 3 ? ARGS[3] : nothing
    print(generate_lean(trace; theorem_name=name, namespace=ns))
end

main()
