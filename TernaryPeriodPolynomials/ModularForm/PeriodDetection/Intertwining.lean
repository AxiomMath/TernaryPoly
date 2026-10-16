module

public import TernaryPeriodPolynomials.ModularForm.Period.Injective

@[expose] public section


noncomputable section
namespace TernaryPoly.BinaryCuspPeriodDetection
open BinaryCuspPeriod BinaryCuspPeriodInjective

/-- A literal scalar intertwining identity for the actual cusp-to-period map.
The scalar is explicitly oriented: P(T_p f)=c_p U_p(P(f)). -/
def Intertwines (d : ℕ) (hd : Even d)
    (U : Nat.Primes → Module.End ℂ (BinaryComplexPeriod.space ℂ d))
    (c : Nat.Primes → ℂ) : Prop :=
  ∀ p f, periodMap d hd (primeHecke d p f)=c p • U p (periodMap d hd f)

/-- Literal intertwining forces stability of the actual kernel; this direction needs no
nonvanishing hypothesis on the scalar. -/
theorem kernelStable_of_intertwines (d : ℕ) (hd : Even d)
    (U : Nat.Primes → Module.End ℂ (BinaryComplexPeriod.space ℂ d))
    (c : Nat.Primes → ℂ) (h : Intertwines d hd U c) : KernelStable d hd := by
  intro p f hf
  rw [h p f,hf,map_zero,smul_zero]

/-- Any exact scalar intertwining identity therefore proves injectivity of the actual map. -/
theorem periodMap_injective_of_intertwines (d : ℕ) (hd : Even d)
    (U : Nat.Primes → Module.End ℂ (BinaryComplexPeriod.space ℂ d))
    (c : Nat.Primes → ℂ) (h : Intertwines d hd U c) :
    Function.Injective (periodMap d hd) :=
  periodMap_injective_of_kernel_stable d hd (kernelStable_of_intertwines d hd U c h)

/-- Common eigenperiods lift through an actual period bijection with the exact scaled eigenvalues. -/
theorem inverse_common_eigenform (d : ℕ) (hd : Even d)
    (hbij : Function.Bijective (periodMap d hd))
    (U : Nat.Primes → Module.End ℂ (BinaryComplexPeriod.space ℂ d))
    (c : Nat.Primes → ℂ) (h : Intertwines d hd U c)
    (q : BinaryComplexPeriod.space ℂ d) (a : Nat.Primes → ℂ)
    (hq : ∀ p,U p q=a p • q) :
    ∃ f : Forms d, periodMap d hd f=q ∧
      BinaryCuspHecke.IsPrimeEigenform f (fun p => c p*a p) := by
  obtain ⟨f,hf⟩ := hbij.surjective q
  refine ⟨f,hf,(isPrimeEigenform_iff f _).mpr ?_⟩
  intro p
  apply hbij.injective
  rw [h p f,hf,hq p,map_smul,hf,smul_smul]

/-- Every nonzero common eigenperiod has nonzero actual extreme coefficient, once the actual
period bijection and literal scalar intertwining are supplied. The small-degree case is handled
by actual cusp vanishing. The forward scalar orientation makes nonzero scalars unnecessary. -/
theorem extreme_ne_zero_of_common_eigenperiod (d : ℕ) (hd : Even d)
    (hbij : Function.Bijective (periodMap d hd))
    (U : Nat.Primes → Module.End ℂ (BinaryComplexPeriod.space ℂ d))
    (c : Nat.Primes → ℂ) (h : Intertwines d hd U c)
    (q : BinaryComplexPeriod.space ℂ d) (hq0 : q≠0)
    (a : Nat.Primes → ℂ) (hq : ∀ p,U p q=a p • q) :
    BinaryComplexPeriod.extreme ℂ d q≠0 := by
  obtain ⟨f,hf,he⟩ := inverse_common_eigenform d hd hbij U c h q a hq
  have hf0 : f≠0 := by
    intro hz
    apply hq0
    rw [←hf,hz,map_zero]
  have hlarge : 10≤d := by
    by_contra hn
    exact hf0 (forms_eq_zero_of_lt_ten (by omega) f)
  rw [←hf]
  exact extreme_periodMap_eigen_ne_zero hd (by omega) f _ he hf0

/-- Reverse-oriented intertwining can be converted without losing its exact nonzero scalar. -/
theorem intertwines_of_reverse (d : ℕ) (hd : Even d)
    (U : Nat.Primes → Module.End ℂ (BinaryComplexPeriod.space ℂ d))
    (c : Nat.Primes → ℂ) (hc : ∀ p,c p≠0)
    (h : ∀ p f,U p (periodMap d hd f)=c p • periodMap d hd (primeHecke d p f)) :
    Intertwines d hd U (fun p => (c p)⁻¹) := by
  intro p f
  rw [h p f,smul_smul,inv_mul_cancel₀ (hc p),one_smul]

end TernaryPoly.BinaryCuspPeriodDetection
