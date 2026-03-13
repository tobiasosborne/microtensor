"""
    MicroTensor

Minimal tensor expression IR with proof trace emission.
Prototype for the Theoria Julia↔Lean4 verified algebra pipeline.
"""
module MicroTensor

using JSON

export Index, TExpr, Te, up, down
export te_zero, te_scalar, te_tensor, te_smul, te_sum
export Symmetry, Antisym, Sym, BianchiSym, Registry
export simplify_traced, to_json, emit_trace

# ─────────────────────────────────────────────────────────────
# IR types (must match shared/ir.md exactly)
# ─────────────────────────────────────────────────────────────

@enum Position Up Down
up(s::Symbol) = Index(s, Up)
down(s::Symbol) = Index(s, Down)

struct Index
    name::Symbol
    position::Position
end

"""Abstract type for tensor expressions."""
abstract type TExpr end

struct TeZero <: TExpr end
struct TeScalar <: TExpr; value::Rational{Int}; end
struct TeTensor <: TExpr; name::Symbol; indices::Vector{Index}; end
struct TeSMul <: TExpr; coeff::Rational{Int}; expr::TExpr; end
struct TeSum <: TExpr; left::TExpr; right::TExpr; end

# Smart constructors ──────────────────────────────────────────

te_zero() = TeZero()
te_scalar(v) = TeScalar(Rational{Int}(v))
te_tensor(name, idxs) = TeTensor(name, idxs)

function te_smul(c, e::TExpr)
    c == 0 && return te_zero()
    c == 1 && return e
    e isa TeZero && return te_zero()
    e isa TeSMul && return te_smul(c * e.coeff, e.expr)
    TeSMul(Rational{Int}(c), e)
end

function te_sum(a::TExpr, b::TExpr)
    a isa TeZero && return b
    b isa TeZero && return a
    TeSum(a, b)
end

# Equality ────────────────────────────────────────────────────

Base.:(==)(a::Index, b::Index) = a.name == b.name && a.position == b.position
Base.:(==)(::TeZero, ::TeZero) = true
Base.:(==)(a::TeScalar, b::TeScalar) = a.value == b.value
Base.:(==)(a::TeTensor, b::TeTensor) = a.name == b.name && a.indices == b.indices
Base.:(==)(a::TeSMul, b::TeSMul) = a.coeff == b.coeff && a.expr == b.expr
Base.:(==)(a::TeSum, b::TeSum) = a.left == b.left && a.right == b.right
Base.:(==)(::TExpr, ::TExpr) = false

# Display ─────────────────────────────────────────────────────

function Base.show(io::IO, idx::Index)
    s = string(idx.name)
    print(io, idx.position == Up ? "^$s" : "_$s")
end

Base.show(io::IO, ::TeZero) = print(io, "0")
Base.show(io::IO, e::TeScalar) = print(io, e.value)
function Base.show(io::IO, e::TeTensor)
    print(io, e.name)
    for idx in e.indices; print(io, idx); end
end
function Base.show(io::IO, e::TeSMul)
    if e.coeff == -1
        print(io, "-(", e.expr, ")")
    else
        print(io, e.coeff, "·(", e.expr, ")")
    end
end
function Base.show(io::IO, e::TeSum)
    print(io, "(", e.left, " + ", e.right, ")")
end

# ─────────────────────────────────────────────────────────────
# Registry (tensor metadata — symmetries etc.)
# ─────────────────────────────────────────────────────────────

abstract type Symmetry end
struct Antisym <: Symmetry; tensor::Symbol; slot1::Int; slot2::Int; end
struct Sym <: Symmetry; tensor::Symbol; slot1::Int; slot2::Int; end
struct BianchiSym <: Symmetry; tensor::Symbol; slot1::Int; slot2::Int; slot3::Int; end

struct Registry
    symmetries::Vector{Symmetry}
end
Registry() = Registry(Symmetry[])

function has_antisym(reg::Registry, name::Symbol, s1::Int, s2::Int)
    any(reg.symmetries) do sym
        sym isa Antisym && sym.tensor == name && sym.slot1 == s1 && sym.slot2 == s2
    end
end

function has_sym(reg::Registry, name::Symbol, s1::Int, s2::Int)
    any(reg.symmetries) do sym
        sym isa Sym && sym.tensor == name && sym.slot1 == s1 && sym.slot2 == s2
    end
end

function has_bianchi(reg::Registry, name::Symbol, s1::Int, s2::Int, s3::Int)
    any(reg.symmetries) do sym
        sym isa BianchiSym && sym.tensor == name && sym.slot1 == s1 && sym.slot2 == s2 && sym.slot3 == s3
    end
end

# ─────────────────────────────────────────────────────────────
# Proof trace types
# ─────────────────────────────────────────────────────────────

abstract type ProofStep end

struct SwapSlots <: ProofStep
    tensor::Symbol
    slot1::Int
    slot2::Int
    path::Vector{Int}
end

struct Collect <: ProofStep
    path::Vector{Int}
end

struct ZeroElim <: ProofStep
    path::Vector{Int}
end

struct SumZero <: ProofStep
    path::Vector{Int}
end

struct BianchiCyclic <: ProofStep
    tensor::Symbol
    slot1::Int
    slot2::Int
    slot3::Int
    path::Vector{Int}
end

struct ProofTrace
    registry::Registry
    expr::TExpr         # original expression
    steps::Vector{ProofStep}
    result::TExpr       # final expression
end

# ─────────────────────────────────────────────────────────────
# Tree navigation (access subtree at path)
# ─────────────────────────────────────────────────────────────

"""Get the subtree at the given path (0 = left/expr child, 1 = right child)."""
function subtree(e::TExpr, path::Vector{Int})
    isempty(path) && return e
    p, rest = path[1], path[2:end]
    if e isa TeSum
        subtree(p == 0 ? e.left : e.right, rest)
    elseif e isa TeSMul
        p == 0 || error("TeSMul only has child 0")
        subtree(e.expr, rest)
    else
        error("Cannot descend into $(typeof(e))")
    end
end

"""Replace the subtree at the given path."""
function replace_at(e::TExpr, path::Vector{Int}, new::TExpr)
    isempty(path) && return new
    p, rest = path[1], path[2:end]
    if e isa TeSum
        if p == 0
            TeSum(replace_at(e.left, rest, new), e.right)
        else
            TeSum(e.left, replace_at(e.right, rest, new))
        end
    elseif e isa TeSMul
        TeSMul(e.coeff, replace_at(e.expr, rest, new))
    else
        error("Cannot descend into $(typeof(e)) at path $path")
    end
end

# ─────────────────────────────────────────────────────────────
# Rule application (each returns transformed expr)
# ─────────────────────────────────────────────────────────────

"""Apply slot swap: for Antisym, result is -1 × tensor with swapped slots."""
function apply_swap(e::TExpr, reg::Registry, tensor::Symbol, s1::Int, s2::Int)
    if e isa TeTensor && e.name == tensor
        new_idxs = copy(e.indices)
        new_idxs[s1], new_idxs[s2] = new_idxs[s2], new_idxs[s1]
        if has_antisym(reg, tensor, s1, s2)
            return TeSMul(-1//1, TeTensor(tensor, new_idxs))
        elseif has_sym(reg, tensor, s1, s2)
            return TeTensor(tensor, new_idxs)
        end
    elseif e isa TeSMul && e.expr isa TeTensor && e.expr.name == tensor
        inner = apply_swap(e.expr, reg, tensor, s1, s2)
        if inner isa TeSMul
            return te_smul(e.coeff * inner.coeff, inner.expr)
        else
            return te_smul(e.coeff, inner)
        end
    end
    error("Cannot apply swap to $(e)")
end

"""Normalise an expr to SMul form: Tensor(R,...) → SMul(1, Tensor(R,...))."""
function to_smul(e::TExpr)
    e isa TeSMul && return e
    e isa TeTensor && return TeSMul(1//1, e)
    e isa TeZero && return TeSMul(0//1, te_zero())
    error("Cannot normalise $(typeof(e)) to SMul")
end

"""Collect: Sum(a·e, b·e) → (a+b)·e. Compares the inner exprs."""
function apply_collect(e::TExpr)
    e isa TeSum || error("Collect requires a Sum")
    l = to_smul(e.left)
    r = to_smul(e.right)
    l.expr == r.expr || error("Collect: inner expressions don't match: $(l.expr) ≠ $(r.expr)")
    TeSMul(l.coeff + r.coeff, l.expr)
end

"""ZeroElim: SMul(0, e) → Zero."""
function apply_zero_elim(e::TExpr)
    (e isa TeSMul && e.coeff == 0) && return te_zero()
    e isa TeZero && return te_zero()
    error("ZeroElim: not a zero expression: $e")
end

"""SumZero: Sum(Zero, e) → e or Sum(e, Zero) → e."""
function apply_sum_zero(e::TExpr)
    e isa TeSum || error("SumZero requires a Sum")
    e.left isa TeZero && return e.right
    e.right isa TeZero && return e.left
    error("SumZero: neither side is zero")
end

"""Cyclic permutation of 3 positions: i←k, j←i, k←j."""
function cyclic_perm3(indices::Vector{Index}, s1::Int, s2::Int, s3::Int)
    result = copy(indices)
    result[s1] = indices[s3]
    result[s2] = indices[s1]
    result[s3] = indices[s2]
    return result
end

# ─────────────────────────────────────────────────────────────
# Traced simplification
# ─────────────────────────────────────────────────────────────

"""Flatten a right-associated sum into a list of terms."""
function flatten_sum(e::TExpr)
    e isa TeSum || return [e]
    vcat(flatten_sum(e.left), flatten_sum(e.right))
end

"""Get the tensor name and indices from a term (plain tensor or smul of tensor)."""
function tensor_info(e::TExpr)
    if e isa TeTensor
        return e.name, e.indices
    elseif e isa TeSMul && e.expr isa TeTensor
        return e.expr.name, e.expr.indices
    end
    return nothing
end

function simplify_traced(expr::TExpr, reg::Registry)
    steps = ProofStep[]
    current = expr

    # Try Bianchi simplification first (3-term sums)
    current, steps = _simplify_bianchi(current, reg, steps, Int[])

    # Then try pairwise swap simplification
    if current == expr  # no Bianchi simplification happened
        current, steps = _simplify_sum(current, reg, steps, Int[])
    end

    ProofTrace(reg, expr, steps, current)
end

"""Check if three tensor terms form a Bianchi pattern (cyclic permutation of 3 slots)."""
function _simplify_bianchi(e::TeSum, reg::Registry, steps::Vector{ProofStep}, path::Vector{Int})
    terms = flatten_sum(e)
    length(terms) == 3 || return e, steps

    # All terms must be the same tensor
    infos = [tensor_info(t) for t in terms]
    all(i -> i !== nothing, infos) || return e, steps
    names = [i[1] for i in infos]
    all(n -> n == names[1], names) || return e, steps

    name = names[1]
    idxs = [i[2] for i in infos]
    n = length(idxs[1])
    all(idx -> length(idx) == n, idxs) || return e, steps

    # Try all triples of slots to find a cyclic permutation
    for s1 in 1:n, s2 in 1:n, s3 in 1:n
        s1 == s2 && continue
        s1 == s3 && continue
        s2 == s3 && continue

        perm1 = cyclic_perm3(idxs[1], s1, s2, s3)
        perm2 = cyclic_perm3(perm1, s1, s2, s3)

        if perm1 == idxs[2] && perm2 == idxs[3]
            if has_bianchi(reg, name, s1, s2, s3)
                push!(steps, BianchiCyclic(name, s1, s2, s3, path))
                return TeZero(), steps
            end
        end
    end

    return e, steps
end

function _simplify_bianchi(e::TExpr, reg::Registry, steps::Vector{ProofStep}, path::Vector{Int})
    return e, steps
end

function _simplify_sum(e::TeSum, reg::Registry, steps::Vector{ProofStep}, path::Vector{Int})
    # Try to find a slot swap that makes right match left
    l, r = e.left, e.right

    # Normalise both to SMul form for comparison
    ln = to_smul(l)
    rn = to_smul(r)

    if ln.expr isa TeTensor && rn.expr isa TeTensor && ln.expr.name == rn.expr.name
        name = ln.expr.name
        # Find which slots differ
        lidx = ln.expr.indices
        ridx = rn.expr.indices
        if length(lidx) == length(ridx)
            diffs = findall(i -> lidx[i] != ridx[i], 1:length(lidx))
            if length(diffs) == 2
                s1, s2 = diffs
                # Check if swapping s1,s2 in right makes it match left
                test = copy(ridx)
                test[s1], test[s2] = test[s2], test[s1]
                if test == lidx
                    # Apply swap to right child (path 1 = right)
                    swap_path = vcat(path, [1])
                    push!(steps, SwapSlots(name, s1, s2, swap_path))
                    new_right = apply_swap(r, reg, name, s1, s2)
                    current = TeSum(l, new_right)

                    # Now collect
                    push!(steps, Collect(path))
                    current = apply_collect(current)

                    # If zero, eliminate
                    if current isa TeSMul && current.coeff == 0
                        push!(steps, ZeroElim(path))
                        current = apply_zero_elim(current)
                    end

                    return current, steps
                end
            end
        end
    end

    # If no simplification found, try recursing
    return e, steps
end

function _simplify_sum(e::TExpr, reg::Registry, steps::Vector{ProofStep}, path::Vector{Int})
    # Non-sum expressions: nothing to do in MVP
    return e, steps
end

# ─────────────────────────────────────────────────────────────
# JSON serialisation
# ─────────────────────────────────────────────────────────────

function expr_to_dict(e::TeZero)
    Dict("type" => "zero")
end
function expr_to_dict(e::TeScalar)
    Dict("type" => "scalar", "num" => numerator(e.value), "den" => denominator(e.value))
end
function expr_to_dict(e::TeTensor)
    Dict("type" => "tensor", "name" => string(e.name),
         "indices" => [Dict("name" => string(i.name),
                           "position" => i.position == Up ? "up" : "down")
                      for i in e.indices])
end
function expr_to_dict(e::TeSMul)
    Dict("type" => "smul", "num" => numerator(e.coeff), "den" => denominator(e.coeff),
         "expr" => expr_to_dict(e.expr))
end
function expr_to_dict(e::TeSum)
    Dict("type" => "sum", "left" => expr_to_dict(e.left), "right" => expr_to_dict(e.right))
end

function step_to_dict(s::SwapSlots)
    # Convert 1-indexed Julia slots to 0-indexed for JSON/Lean
    Dict("rule" => "swap_slots", "tensor" => string(s.tensor),
         "slot1" => s.slot1 - 1, "slot2" => s.slot2 - 1, "path" => s.path)
end
function step_to_dict(s::Collect)
    Dict("rule" => "collect", "path" => s.path)
end
function step_to_dict(s::ZeroElim)
    Dict("rule" => "zero_elim", "path" => s.path)
end
function step_to_dict(s::SumZero)
    Dict("rule" => "sum_zero", "path" => s.path)
end
function step_to_dict(s::BianchiCyclic)
    # Convert 1-indexed Julia slots to 0-indexed for JSON/Lean
    Dict("rule" => "bianchi_cyclic", "tensor" => string(s.tensor),
         "slot1" => s.slot1 - 1, "slot2" => s.slot2 - 1, "slot3" => s.slot3 - 1,
         "path" => s.path)
end

function sym_to_dict(s::Antisym)
    # Convert 1-indexed Julia slots to 0-indexed for JSON/Lean
    Dict("type" => "antisym", "tensor" => string(s.tensor),
         "slot1" => s.slot1 - 1, "slot2" => s.slot2 - 1)
end
function sym_to_dict(s::Sym)
    Dict("type" => "sym", "tensor" => string(s.tensor),
         "slot1" => s.slot1 - 1, "slot2" => s.slot2 - 1)
end
function sym_to_dict(s::BianchiSym)
    Dict("type" => "bianchi", "tensor" => string(s.tensor),
         "slot1" => s.slot1 - 1, "slot2" => s.slot2 - 1, "slot3" => s.slot3 - 1)
end

function trace_to_json(trace::ProofTrace)
    Dict(
        "registry" => [sym_to_dict(s) for s in trace.registry.symmetries],
        "expr" => expr_to_dict(trace.expr),
        "steps" => [step_to_dict(s) for s in trace.steps],
        "result" => expr_to_dict(trace.result)
    )
end

function emit_trace(trace::ProofTrace; io::IO=stdout)
    JSON.print(io, trace_to_json(trace), 2)
    println(io)
end

end # module
