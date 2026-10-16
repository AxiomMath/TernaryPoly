module

public import TernaryPeriodPolynomials.ModularForm.Period.Injective
public import TernaryPeriodPolynomials.PeriodPolynomial.BinaryPeriodDimension
public import TernaryPeriodPolynomials.PeriodPolynomial.BinaryPeriodTensor

@[expose] public section


noncomputable section
namespace TernaryPoly.BinaryCuspPeriodInjective
open BinaryCuspPeriod

/-- The source and target of the actual analytic period map have exactly equal dimensions. -/
theorem periodMap_finrank_eq (d : ℕ) (hd : Even d) :
    Module.finrank ℂ (Forms d)=Module.finrank ℂ (BinaryComplexPeriod.space ℂ d) := by
  rw [BinaryComplexPeriod.complex_finrank_eq,BinaryComplexPeriod.rational_finrank_eq_cusp d hd]

/-- The actual period map becomes a linear equivalence from its explicit kernel stability,
using the proved dimensions of the actual source and actual period space. -/
def periodEquivOfKernelStable (d : ℕ) (hd : Even d) (hs : KernelStable d hd) :
    Forms d ≃ₗ[ℂ] BinaryComplexPeriod.space ℂ d :=
  LinearEquiv.ofInjectiveOfFinrankEq (periodMap d hd)
    (periodMap_injective_of_kernel_stable d hd hs) (periodMap_finrank_eq d hd)

@[simp] theorem periodEquivOfKernelStable_apply (d : ℕ) (hd : Even d)
    (hs : KernelStable d hd) (f : Forms d) :
    periodEquivOfKernelStable d hd hs f=periodMap d hd f := rfl

/-- Injectivity and exact dimension give bijectivity of the actual map, still with precisely
the explicit kernel-stability gate. -/
theorem periodMap_bijective_of_kernel_stable (d : ℕ) (hd : Even d) (hs : KernelStable d hd) :
    Function.Bijective (periodMap d hd) :=
  (periodEquivOfKernelStable d hd hs).bijective

end TernaryPoly.BinaryCuspPeriodInjective
