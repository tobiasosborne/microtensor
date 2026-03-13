#!/usr/bin/env julia
# test_emit.jl — Emit proof trace for R_{abcd} + R_{abdc} = 0

include("MicroTensor.jl")
using .MicroTensor

# Set up registry: Riemann tensor has antisymmetry in slots (3,4)
# Using 1-indexed slots: R_{1 2 3 4} → antisym in positions 3,4
reg = Registry([
    Antisym(:R, 3, 4),   # R_{ab[cd]} = -R_{abdc}
    Antisym(:R, 1, 2),   # R_{[ab]cd} = -R_{bacd}  (not used in this proof, but realistic)
])

# Build expression: R_{abcd} + R_{abdc}
a, b, c, d = down(:a), down(:b), down(:c), down(:d)

R_abcd = te_tensor(:R, [a, b, c, d])
R_abdc = te_tensor(:R, [a, b, d, c])  # note: c,d swapped in last two slots

expr = te_sum(R_abcd, R_abdc)

println(stderr, "Input:  ", expr)

# Simplify with proof trace
trace = simplify_traced(expr, reg)

println(stderr, "Output: ", trace.result)
println(stderr, "Steps:  ", length(trace.steps))
for (i, step) in enumerate(trace.steps)
    println(stderr, "  $i. $step")
end

# Emit JSON trace to stdout
emit_trace(trace)

# Verify it actually simplified to zero
@assert trace.result isa MicroTensor.TeZero "Expected zero, got $(trace.result)"
println(stderr, "\n✓ R_{abcd} + R_{abdc} = 0 (proof trace emitted)")
