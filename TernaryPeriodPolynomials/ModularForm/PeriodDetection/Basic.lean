module

public import TernaryPeriodPolynomials.ModularForm.PeriodDetection.Bijective
public import TernaryPeriodPolynomials.ModularForm.PeriodDetection.Commuting
public import TernaryPeriodPolynomials.PeriodPolynomial.BinaryPeriodTensorHecke
public import TernaryPeriodPolynomials.PeriodPolynomial.RationalHecke.Prime.Diagonal

@[expose] public section


noncomputable section
namespace TernaryPoly.BinaryCuspPeriodDetection
open BinaryCuspPeriod BinaryCuspPeriodInjective

/-- The genuine rational modular-symbol prime Hecke, extended to the actual complex period space. -/
def primePeriodHecke (d : ℕ) (p : Nat.Primes) :
    Module.End ℂ (BinaryComplexPeriod.space ℂ d) :=
  let : Fact p.val.Prime := ⟨(Nat.irreducible_iff_nat_prime _).mp p.property⟩
  BinaryComplexPeriod.complexHecke d (BinaryRationalHeckePrime.primeDiagonal p.val)

/-- The predicted exact Hecke scalar, recorded as a definition rather than an assumed identity. -/
def primeScalar (d : ℕ) (p : Nat.Primes) : ℂ := (p.val : ℂ)^(d+1)

/-- The explicit prime scalar is nonzero in every degree. -/
theorem primeScalar_ne_zero (d : ℕ) (p : Nat.Primes) : primeScalar d p≠0 := by
  apply pow_ne_zero
  exact_mod_cast (Nat.ne_of_gt (BinaryCuspHecke.prime_pos p))

/-- The precise actual analytic compatibility to be supplied, with its normalization visible. -/
def ActualIntertwining (d : ℕ) (hd : Even d) : Prop :=
  Intertwines d hd (primePeriodHecke d) (primeScalar d)

/-- The genuine cusp-to-period bijection follows once the exact actual intertwining is supplied. -/
theorem actual_periodMap_bijective (d : ℕ) (hd : Even d) (h : ActualIntertwining d hd) :
    Function.Bijective (periodMap d hd) :=
  periodMap_bijective_of_intertwines d hd (primePeriodHecke d) (primeScalar d) h

/-- Detection of every genuine common prime eigenperiod, with the exact analytic intertwining
hypothesis retained explicitly until it is proved. -/
theorem actual_eigenperiod_extreme_ne_zero (d : ℕ) (hd : Even d)
    (h : ActualIntertwining d hd) (q : BinaryComplexPeriod.space ℂ d) (hq0 : q≠0)
    (a : Nat.Primes → ℂ) (hq : ∀ p,primePeriodHecke d p q=a p • q) :
    BinaryComplexPeriod.extreme ℂ d q≠0 :=
  extreme_ne_zero_of_intertwining_eigenperiod d hd (primePeriodHecke d) (primeScalar d)
    h q hq0 a hq

/-- The genuine complex prime period-Hecke family commutes after exact actual compatibility. -/
theorem actual_primePeriodHecke_commute (d : ℕ) (hd : Even d) (h : ActualIntertwining d hd)
    (p q : Nat.Primes) : Commute (primePeriodHecke d p) (primePeriodHecke d q) :=
  commute_of_intertwines d hd (actual_periodMap_bijective d hd h).surjective
    (primePeriodHecke d) (primeScalar d) (primeScalar_ne_zero d) h p q

/-- A genuinely stable actual period subspace annihilated by the extreme coefficient is zero,
under the explicit exact analytic intertwining gate. -/
theorem actual_stable_extreme_kernel_eq_bot (d : ℕ) (hd : Even d) (h : ActualIntertwining d hd)
    (L : Submodule ℂ (BinaryComplexPeriod.space ℂ d))
    (hs : ∀ p q,q∈L → primePeriodHecke d p q∈L)
    (hz : ∀ q∈L,BinaryComplexPeriod.extreme ℂ d q=0) : L=⊥ := by
  apply CommutingEigenvector.eq_bot_of_functional (primePeriodHecke d)
    (actual_primePeriodHecke_commute d hd h) (BinaryComplexPeriod.extreme ℂ d) ?_ L hs hz
  intro q hq he
  choose a ha using he
  exact actual_eigenperiod_extreme_ne_zero d hd h q hq a ha

end TernaryPoly.BinaryCuspPeriodDetection
