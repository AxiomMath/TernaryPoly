module

public import TernaryPeriodPolynomials.ModularForm.ThreeTerm.Consumer
public import TernaryPeriodPolynomials.ModularForm.Hecke.Commute
public import TernaryPeriodPolynomials.ModularForm.BinaryCuspDimension
public import TernaryPeriodPolynomials.ModularForm.CommutingEigenvector
public import Mathlib.Analysis.Complex.Polynomial.Basic

@[expose] public section


noncomputable section
namespace TernaryPoly.BinaryCuspPeriodInjective
open BinaryCuspPeriod

/-- The genuine prime Hecke endomorphisms, indexed by the actual type of primes. -/
def primeHecke (d : ℕ) (p : Nat.Primes) : Module.End ℂ (Forms d) :=
  let : Fact p.val.Prime := ⟨(Nat.irreducible_iff_nat_prime _).mp p.property⟩
  BinaryCuspHeckeEndomorphism.T d p.val

/-- The indexed genuine Hecke has exactly the original standard pointwise normalization. -/
theorem primeHecke_apply (d : ℕ) (p : Nat.Primes) (f : Forms d) (z : UpperHalfPlane) :
    primeHecke d p f z = BinaryCuspHecke.primeOperator p.val (BinaryCuspHecke.prime_pos p) f z := by
  let : Fact p.val.Prime := ⟨(Nat.irreducible_iff_nat_prime _).mp p.property⟩
  exact BinaryCuspHeckeEndomorphism.T_apply d p.val f z

/-- The actual prime family commutes on the actual cusp space. -/
theorem primeHecke_commute (d : ℕ) (p q : Nat.Primes) :
    Commute (primeHecke d p) (primeHecke d q) := by
  let : Fact p.val.Prime := ⟨(Nat.irreducible_iff_nat_prime _).mp p.property⟩
  let : Fact q.val.Prime := ⟨(Nat.irreducible_iff_nat_prime _).mp q.property⟩
  exact BinaryCuspHeckeEndomorphism.T_commute d p.val q.val

/-- Actual endomorphism eigenidentities are the actual pointwise prime eigenform equations. -/
theorem isPrimeEigenform_iff {d : ℕ} (f : Forms d) (ev : Nat.Primes → ℂ) :
    BinaryCuspHecke.IsPrimeEigenform f ev ↔ ∀ p, primeHecke d p f=ev p • f := by
  constructor
  · intro hf p
    apply DFunLike.ext
    intro z
    rw [primeHecke_apply]
    exact hf p z
  · intro hf p z
    have h := congrArg (fun g : Forms d => g z) (hf p)
    simpa only [primeHecke_apply,smul_apply,smul_eq_mul] using h

/-- The remaining explicit stability condition concerns the kernel of the actual analytic map. -/
def KernelStable (d : ℕ) (hd : Even d) : Prop :=
  ∀ p f, periodMap d hd f=0 → periodMap d hd (primeHecke d p f)=0

/-- Kernel stability under genuine commuting Hecke operators makes the actual period map injective.
The small-degree case uses vanishing of actual cusp forms, and the large-degree case uses
nonvanishing of the actual period of a genuine common prime eigenform. -/
theorem periodMap_injective_of_kernel_stable (d : ℕ) (hd : Even d) (hs : KernelStable d hd) :
    Function.Injective (periodMap d hd) := by
  classical
  by_cases hsmall : d<10
  · intro f g _
    rw [forms_eq_zero_of_lt_ten hsmall f,forms_eq_zero_of_lt_ten hsmall g]
  · apply LinearMap.ker_eq_bot.mp
    by_contra hker
    obtain ⟨f,hf,hne,he⟩ := CommutingEigenvector.exists_common (primeHecke d)
      (primeHecke_commute d) (periodMap d hd).ker hker (fun p f hf => hs p f hf)
    choose ev hev using he
    exact periodMap_eigen_ne_zero hd (by omega) f ev ((isPrimeEigenform_iff f ev).mpr hev) hne hf

/-- The exact actual kernel vanishes under its explicit Hecke stability hypothesis. -/
theorem periodMap_ker_eq_bot_of_stable (d : ℕ) (hd : Even d) (hs : KernelStable d hd) :
    (periodMap d hd).ker=⊥ :=
  LinearMap.ker_eq_bot.mpr (periodMap_injective_of_kernel_stable d hd hs)

end TernaryPoly.BinaryCuspPeriodInjective
