module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Obstructions
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.AdelicSplit
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.REVector
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.RESupply

@[expose] public section


/-!
# The normal inducing character of a nonzero associate pair

The paper shows that the normal inducing character at the bad plane is globally trivial: trivial on the units
`u ≡ 1 (3)` and at the places `p ≠ 3` because the finite level is maximal there (a nonzero induced section at the
reference frame forces this), trivial on the remaining unit class `u ≡ -1 (3)` because the sign `χ_∞(-1)` of the
real place is `+1` (the reflection `diag(I₂, -1)`, available because `-I_3` acts trivially on `E_n` for odd `n`), and then
globally trivial by class number one (the positive rational primes).

Proved here:

* `chi_units_eq_one_of_pair`: for `D` with a nonzero associate pair, `χ(u) = 1` for every integral unit `u` provided
  `χ_∞(-1) = 1`.  The units `u ≡ 1 (3)` are `Obstructions.associatePair_eq_bot_of_character` (a unit moved into the
  finite level by the reference frames of the four cusps); the class `u ≡ -1 (3)` is the product formula
  `χ(-1_{∞})·χ(-1_{fin}) = 1`.
* `eq_trivialCharacter_of_units`: a rank-one character trivial on all integral units is the trivial character
  (`character_split`, `character_real_eq_one`, `REVector.character_finite_eq_one`).
* `chi_eq_trivial_of_pair_even`: the combination.

**Scope.** The hypothesis `χ_∞(-1) = 1` is the reflection sign.  It is *not* a consequence of the `K†`-level strata alone
(the central `-I₃` acts on a source by `(-1)^{n+1}ω_σ(-1_f)`, independent of `χ`); the paper obtains it from the
extension of the class to `⟨K†, -I₃⟩`.  That extension is formalized in `ManuscriptC6/ReflectionSign.lean`
(`reflLevel`, `IsReflExtended`), where `chi_eq_trivial_of_extended_bad_plane` derives `χ_∞(-1) = 1` and
`D.chi = trivialCharacter` for any datum with an extended bad-plane class, using `chi_eq_trivial_of_pair_even` from here.
The theorems of this file keep `heven` as an explicit hypothesis so that they can be used with or without the extension.

Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry (character_finite_eq_one)

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.FiniteEntries

/-- **A rank-one character trivial on the integral units is trivial** (class number one). -/
theorem eq_trivialCharacter_of_units (χ : RankOneCharacter)
    (hχ : ∀ u : IntegralAdelesˣ, χ.toMonoidHom (integralAdeleUnit u) = 1) : χ = trivialCharacter := by
  have hone : χ.toMonoidHom = 1 := by
    ext t
    rw [character_split, character_real_eq_one χ hχ, character_finite_eq_one χ hχ]
    simp
  cases χ
  simp only [trivialCharacter]
  congr


theorem integralAdeleUnit_mul (u v : IntegralAdelesˣ) :
    integralAdeleUnit (u * v) = integralAdeleUnit u * integralAdeleUnit v := by
  apply Units.ext
  change ((1 : ℝ), integralEmbedding (u * v).val) = ((1 : ℝ) * 1, integralEmbedding u.val * integralEmbedding v.val)
  rw [Units.val_mul, map_mul, mul_one]

/-- The value at the integral unit `-1` is the inverse of the real sign (product formula for the rational `-1`). -/
theorem chi_neg_one_integral (χ : RankOneCharacter) (heven : χ.toMonoidHom (realAdeleUnit (-1)) = 1) :
    χ.toMonoidHom (integralAdeleUnit (-1)) = 1 := by
  have hrat := χ.rational (-1)
  have hsplit : Units.map rationalAdele (-1 : ℚˣ) = realAdeleUnit (-1) * integralAdeleUnit (-1) := by
    apply Units.ext
    change (rationalAdele (-1 : ℚ)) = ((-1 : ℝ) * 1, (1 : FiniteAdeles) * integralEmbedding (-1))
    rw [map_neg, map_one, mul_one, one_mul]
    apply Prod.ext
    · simp
    · simp
  rw [hsplit, map_mul, heven, one_mul] at hrat
  exact hrat

/-- **The units of a character with a nonzero associate pair**: trivial on `u ≡ 1 (3)` by the
reference frames of the cusps, and on `u ≡ -1 (3)` by the real sign. -/
theorem chi_units_eq_one_of_pair {n : ℕ} (D : InducingData n) (hne : associatePair D ≠ ⊥)
    (heven : D.chi.toMonoidHom (realAdeleUnit (-1)) = 1) (u : IntegralAdelesˣ) :
    D.chi.toMonoidHom (integralAdeleUnit u) = 1 := by
  have key : ∀ v : IntegralAdelesˣ, integralReduction v.val = 1 → D.chi.toMonoidHom (integralAdeleUnit v) = 1 := by
    intro v hv
    by_contra h
    exact hne (associatePair_eq_bot_of_character D v hv h)
  have hunit : integralReduction u.val ≠ 0 := by
    intro h0
    have h1 : integralReduction u.val * integralReduction u.inv = 1 := by
      rw [← map_mul, u.val_inv, map_one]
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  by_cases h1 : integralReduction u.val = 1
  · exact key u h1
  · have h2 : integralReduction u.val = 2 := by
      generalize integralReduction u.val = r at hunit h1
      revert r
      decide
    have hneg : integralReduction (-u).val = 1 := by
      rw [Units.val_neg, map_neg, h2]
      decide
    have hk := key (-u) hneg
    have hmul : -u = (-1) * u := by simp
    rw [hmul, integralAdeleUnit_mul, map_mul, chi_neg_one_integral D.chi heven, one_mul] at hk
    exact hk

/-- **The inducing character of a nonzero associate pair with even sign is trivial.** -/
theorem chi_eq_trivial_of_pair_even {n : ℕ} (D : InducingData n) (hne : associatePair D ≠ ⊥)
    (heven : D.chi.toMonoidHom (realAdeleUnit (-1)) = 1) : D.chi = trivialCharacter :=
  eq_trivialCharacter_of_units D.chi (chi_units_eq_one_of_pair D hne heven)

/-- **The entry package for a nonzero associate pair of even sign**: `exists_sphericalEntryPackage` with its character
hypothesis `D.chi = trivialCharacter` replaced by the nonvanishing of the pair and the real sign `χ_∞(-1) = 1`. -/
theorem exists_sphericalEntryPackage_of_pair {n : ℕ} (D : InducingData n) (hodd : Odd n)
    (hsph : SphericalCusp D.cusp) (hne : associatePair D ≠ ⊥)
    (heven : D.chi.toMonoidHom (realAdeleUnit (-1)) = 1) :
    Nonempty (Entry.SphericalEntryPackage D) :=
  Entry.exists_sphericalEntryPackage D hodd (chi_eq_trivial_of_pair_even D hne heven) hsph

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.FiniteEntries
