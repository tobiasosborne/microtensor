#!/usr/bin/env julia
# test_emit2.jl — Emit proof trace for R_{abcd} + R_{bacd} = 0
# Tests antisymmetry in slots 1,2 (first pair).

include("MicroTensor.jl")
using .MicroTensor

# Set up registry: Riemann tensor has antisymmetry in slots (1,2) and (3,4)
reg = Registry([
    Antisym(:R, 3, 4),
    Antisym(:R, 1, 2),
])

# Build expression: R_{abcd} + R_{bacd}
a, b, c, d = down(:a), down(:b), down(:c), down(:d)

R_abcd = te_tensor(:R, [a, b, c, d])
R_bacd = te_tensor(:R, [b, a, c, d])  # slots 1,2 swapped

expr = te_sum(R_abcd, R_bacd)

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
println(stderr, "\n✓ R_{abcd} + R_{bacd} = 0 (proof trace emitted)")
