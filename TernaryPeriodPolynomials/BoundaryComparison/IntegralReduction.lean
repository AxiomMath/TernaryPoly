module

public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.IntegralReduction

@[expose] public section


/-!
# Reduction modulo `N` on `Ẑ` and `GL_n(Ẑ)`

Formalized by Claude Sonnet 5.5.  `integralReductionN N : Ẑ →+* ℤ/N` (Chinese remainder theorem over the primes dividing `N`), `reductionGL N n : GL_n(Ẑ) →* GL_n(ℤ/N)`, its kernel `levelKernel N n = K(N)`,
and the compatibility with integer matrices (`reductionGL_mapGL`, `mapGL_mem_levelKernel_iff`).
-/

namespace TernaryPeriodPolynomials.Argument.Statements.IntegralReduction

open TernaryPeriodPolynomials.Argument.IntegralReduction

alias integral_reduction := integralReductionN
alias integral_reduction_int := integralReductionN_int
alias integral_reduction_surjective := integralReductionN_surjective
alias reduction_gl := reductionGL
alias level_kernel := levelKernel
alias mem_level_kernel_iff := mem_levelKernel_iff
alias reduction_gl_map_int := reductionGL_map_intCast
alias reduction_gl_map_gl := reductionGL_mapGL
alias map_gl_mem_level_kernel_iff := mapGL_mem_levelKernel_iff

end TernaryPeriodPolynomials.Argument.Statements.IntegralReduction
