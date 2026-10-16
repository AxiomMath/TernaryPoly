module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Level.OneNontrivial
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.LocalUniqueness
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Eigen.Satake.ThreeComponent

@[expose] public section


/-!
# The sign of the odd quadratic character at the prime two

For the odd quadratic character `χ` of conductor three, the away-from-three idele of the rational
unit `2` has three-adic component an integral unit congruent to `-1` modulo three, so
`χ(sAd 2) = -1` (`chi_sAd_two_eq_neg_one`).  Consequently the `T₂`-eigenvalue of the pair character
is within `3/4` of `-1` for `n ≥ 3` (`pairCharacter_two_add_one_norm_le`).

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.HeckeEigen.Satake
open TernaryPeriodPolynomials.Spectral

namespace TernaryPeriodPolynomials.Twisted

/-- The map `k ↦ 1_∞ × k_f` on integral units is multiplicative. -/
theorem integralAdeleUnit_mul (a b : IntegralAdelesˣ) :
    integralAdeleUnit (a * b) = integralAdeleUnit a * integralAdeleUnit b := by
  apply Units.ext
  change ((1 : ℝ), integralEmbedding (a.val * b.val)) =
    ((1 : ℝ) * 1, integralEmbedding a.val * integralEmbedding b.val)
  rw [map_mul, mul_one]

/-- A rational unit that is a three-adic unit has a three-component idele which is the image of an
integral unit whose three-adic component is the unit. -/
theorem exists_integralUnit_threeUnit {q : ℚˣ} (h1 : Int3 q) (h2 : Int3 (q : ℚ)⁻¹) :
    ∃ u : IntegralAdelesˣ, finiteAdeleUnit (threeUnit q) = integralAdeleUnit u ∧
      ((integralThree u.val : ℤ_[3]) : ℚ_[3]) = ((q : ℚ) : ℚ_[3]) := by
  obtain ⟨a, ha⟩ := threeAdele_integral (x := ((q : ℚ) : ℚ_[3])) h1
  obtain ⟨b, hb⟩ := threeAdele_integral (x := (((q : ℚ)⁻¹ : ℚ) : ℚ_[3])) h2
  have hab : a * b = 1 := by
    apply integralEmbedding_injective
    rw [map_mul, ha, hb, map_one]
    exact (threeUnit q).val_inv
  have hba : b * a = 1 := by rw [mul_comm]; exact hab
  refine ⟨⟨a, b, hab, hba⟩, ?_, ?_⟩
  · apply Units.ext
    change ((1 : ℝ), threeAdele (q : ℚ)) = ((1 : ℝ), integralEmbedding a)
    rw [ha]
  · change ((integralThree a : ℤ_[3]) : ℚ_[3]) = _
    rw [← finiteThree_integral, ha, threeAdele_three]

/-- The three-component idele of `2` is the image of an integral unit congruent to `-1` modulo
three. -/
theorem exists_integralUnit_two :
    ∃ u : IntegralAdelesˣ,
      finiteAdeleUnit (threeUnit (pUnit Nat.prime_two)) = integralAdeleUnit u ∧
        integralReduction u.val = -1 := by
  have hnorm : ‖((2 : ℕ) : ℚ_[3])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.mpr (by norm_num)
  have h1 : Int3 ((pUnit Nat.prime_two : ℚˣ) : ℚ) := by
    unfold Int3
    rw [pUnit_val, Rat.cast_natCast, hnorm]
  have h2 : Int3 ((pUnit Nat.prime_two : ℚˣ) : ℚ)⁻¹ := by
    unfold Int3
    rw [pUnit_val, Rat.cast_inv, Rat.cast_natCast, norm_inv, hnorm]
    simp
  obtain ⟨u, hu, hcast⟩ := exists_integralUnit_threeUnit h1 h2
  refine ⟨u, hu, ?_⟩
  have hcoe : ((integralThree u.val : ℤ_[3]) : ℚ_[3]) = (((2 : ℕ) : ℤ_[3]) : ℚ_[3]) := by
    rw [hcast, pUnit_val, Rat.cast_natCast, PadicInt.coe_natCast]
  have h3 : integralThree u.val = ((2 : ℕ) : ℤ_[3]) := PadicInt.ext hcoe
  rw [integralReduction, RingHom.comp_apply, h3, map_natCast]
  decide

/-- The value of an odd character of conductor three on the integral unit `-1`. -/
theorem chi_integralAdeleUnit_neg_one {chi : RankOneCharacter}
    (hneg : chi.toMonoidHom (realAdeleUnit (-1)) = -1) :
    chi.toMonoidHom (integralAdeleUnit (-1)) = -1 := by
  have hsplit : Units.map rationalAdele (-1 : ℚˣ) =
      realAdeleUnit (-1) * integralAdeleUnit (-1) := by
    apply Units.ext
    refine Prod.ext ?_ ?_
    · simp [realAdeleUnit, integralAdeleUnit]
    · simp [realAdeleUnit, integralAdeleUnit]
  have hrat := chi.rational (-1)
  rw [hsplit, map_mul, hneg] at hrat
  linear_combination (-1 : ℂ) * hrat

/-- **The odd quadratic character of conductor three at the prime two:** `χ(sAd 2) = -1`. -/
theorem chi_sAd_two_eq_neg_one {chi : RankOneCharacter}
    (hcond : LevelOneNontrivial.ConductorThree chi)
    (hneg : chi.toMonoidHom (realAdeleUnit (-1)) = -1) :
    chi.toMonoidHom (sAd (pUnit Nat.prime_two)) = -1 := by
  obtain ⟨u, hu, hred⟩ := exists_integralUnit_two
  have hpos : 0 < (((pUnit Nat.prime_two : ℚˣ)) : ℚ) := by
    rw [pUnit_val]
    norm_num
  rw [chi_sAd_eq_inv_three chi hpos, hu]
  have h1 : chi.toMonoidHom (integralAdeleUnit (u * -1)) = 1 := by
    apply hcond
    rw [Units.val_mul, Units.val_neg, Units.val_one, map_mul, map_neg, map_one, hred]
    decide
  rw [integralAdeleUnit_mul, map_mul, chi_integralAdeleUnit_neg_one hneg] at h1
  have hx : chi.toMonoidHom (integralAdeleUnit u) = -1 := by
    linear_combination (-1 : ℂ) * h1
  rw [hx, inv_neg, inv_one]

/-- The same statement at the prime `2 : Nat.Primes`. -/
theorem chi_sAd_two_eq_neg_one' {chi : RankOneCharacter}
    (hcond : LevelOneNontrivial.ConductorThree chi)
    (hneg : chi.toMonoidHom (realAdeleUnit (-1)) = -1) :
    chi.toMonoidHom (sAd (pUnit LocalUniqueness.two.property)) = -1 :=
  chi_sAd_two_eq_neg_one hcond hneg

variable {n : ℕ}

/-- For `n ≥ 3` and the odd quadratic character of conductor three, the pair character at `T_2` is
within `3/4` of `-1`. -/
theorem pairCharacter_two_add_one_norm_le (D : InducingData n)
    (hcond : LevelOneNontrivial.ConductorThree D.chi)
    (hneg : D.chi.toMonoidHom (realAdeleUnit (-1)) = -1)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke) (hn : 3 ≤ n)
    (hne : associatePair D ≠ ⊥) :
    ‖pairCharacter D hecke hhecke (TpExistence.tp LocalUniqueness.two) + 1‖ ≤ 3 / 4 := by
  have h := PairCharacterBound.pairCharacter_tp_sub_norm_le D hecke hhecke hne
    LocalUniqueness.two LocalUniqueness.two_ne_three
  rw [chi_sAd_two_eq_neg_one' hcond hneg, sub_neg_eq_add] at h
  refine h.trans ?_
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hexp : Real.exp (-(((n : ℝ) + 3) / 2 * Real.log ((LocalUniqueness.two.val : ℕ) : ℝ))) ≤
      1 / 8 := by
    have h8 : Real.exp (-(3 * Real.log 2)) = 1 / 8 := by
      rw [Real.exp_neg, ← Real.log_rpow (by norm_num), Real.exp_log (by positivity)]
      norm_num
    rw [← h8]
    apply Real.exp_le_exp.mpr
    have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
    change -(((n : ℝ) + 3) / 2 * Real.log ((2 : ℕ) : ℝ)) ≤ -(3 * Real.log 2)
    push_cast
    nlinarith
  change ((((2 : ℕ) : ℝ)) ^ 2 + ((2 : ℕ) : ℝ)) *
      Real.exp (-(((n : ℝ) + 3) / 2 * Real.log ((2 : ℕ) : ℝ))) ≤ 3 / 4
  have : (((2 : ℕ) : ℝ)) ^ 2 + ((2 : ℕ) : ℝ) = 6 := by norm_num
  rw [this]
  change (6 : ℝ) * Real.exp (-(((n : ℝ) + 3) / 2 * Real.log ((LocalUniqueness.two.val : ℕ) : ℝ))) ≤
    3 / 4
  linarith

end TernaryPeriodPolynomials.Twisted
