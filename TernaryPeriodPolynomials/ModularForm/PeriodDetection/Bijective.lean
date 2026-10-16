module

public import TernaryPeriodPolynomials.ModularForm.PeriodDetection.Intertwining
public import TernaryPeriodPolynomials.ModularForm.Period.InjectiveDimension

@[expose] public section


noncomputable section
namespace TernaryPoly.BinaryCuspPeriodDetection
open BinaryCuspPeriod BinaryCuspPeriodInjective

/-- Literal scalar intertwining closes both injectivity and surjectivity, using actual dimensions. -/
theorem periodMap_bijective_of_intertwines (d : ℕ) (hd : Even d)
    (U : Nat.Primes → Module.End ℂ (BinaryComplexPeriod.space ℂ d))
    (c : Nat.Primes → ℂ) (h : Intertwines d hd U c) :
    Function.Bijective (periodMap d hd) :=
  periodMap_bijective_of_kernel_stable d hd (kernelStable_of_intertwines d hd U c h)

/-- The actual dimension theorem makes the eigenperiod detection conclusion depend only on
literal intertwining; an independent period-surjectivity assumption is unnecessary. -/
theorem extreme_ne_zero_of_intertwining_eigenperiod (d : ℕ) (hd : Even d)
    (U : Nat.Primes → Module.End ℂ (BinaryComplexPeriod.space ℂ d))
    (c : Nat.Primes → ℂ) (h : Intertwines d hd U c)
    (q : BinaryComplexPeriod.space ℂ d) (hq0 : q≠0)
    (a : Nat.Primes → ℂ) (hq : ∀ p,U p q=a p • q) :
    BinaryComplexPeriod.extreme ℂ d q≠0 :=
  extreme_ne_zero_of_common_eigenperiod d hd (periodMap_bijective_of_intertwines d hd U c h)
    U c h q hq0 a hq

end TernaryPoly.BinaryCuspPeriodDetection
