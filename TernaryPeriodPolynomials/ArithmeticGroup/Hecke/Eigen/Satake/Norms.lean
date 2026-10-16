module

public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Eigen.Satake.RationalFormula
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.RationalNorm
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Adelic.Norm

@[expose] public section


/-!
# Norms of away-from-three ideles and the plane/line weight comparison

For a rational three-adic unit `q`, the away-from-three idele of `q` has adelic norm `|q|⁻¹`
(product formula). Consequently the line weight of `(d, A)` is the plane weight of `(Aᵀ, d)`
times the modulus ratio `|det A| / d²`.

Original work (AxiomDeep, Claude Opus 5.5).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.RepresentationTheory
open TernaryPeriodPolynomials.HeckeEigen

namespace TernaryPeriodPolynomials.HeckeEigen.Satake

/-- Three-adic integrality of a rational number. -/
def Int3 (q : ℚ) : Prop := ‖(q : ℚ_[3])‖ ≤ 1

/-- The idele equal to `x` at three and one elsewhere. -/
def threeAdele (x : ℚ_[3]) : FiniteAdeles := 1 - finiteAtThreeScalar 1 + finiteAtThreeScalar x

theorem threeAdele_three (x : ℚ_[3]) : finiteThree (threeAdele x) = x := by
  simp only [threeAdele, map_add, map_sub, map_one, finiteAtThreeScalar_three, sub_self, zero_add]

theorem threeAdele_away (x : ℚ_[3]) {v : FinitePlace} (hv : v ≠ placeThree) :
    finiteEvaluation v (threeAdele x) = 1 := by
  simp only [threeAdele, map_add, map_sub, map_one, finiteAtThreeScalar_away _ _ hv, sub_zero,
    add_zero]

theorem threeAdele_mul (x y : ℚ_[3]) : threeAdele x * threeAdele y = threeAdele (x * y) := by
  apply finiteAdeles_eq_of_three_and_away
  · rw [map_mul, threeAdele_three, threeAdele_three, threeAdele_three]
  · intro v hv
    rw [map_mul, threeAdele_away _ hv, threeAdele_away _ hv, threeAdele_away _ hv, one_mul]

theorem threeAdele_one : threeAdele 1 = 1 := by
  simp [threeAdele]

theorem rat3_ne {q : ℚˣ} : ((q : ℚ) : ℚ_[3]) ≠ 0 := by
  exact_mod_cast q.ne_zero

/-- The three-component idele of a rational unit. -/
def threeUnit (q : ℚˣ) : FiniteAdelesˣ where
  val := threeAdele (q : ℚ)
  inv := threeAdele ((q : ℚ)⁻¹ : ℚ)
  val_inv := by
    rw [threeAdele_mul, Rat.cast_inv, mul_inv_cancel₀ rat3_ne, threeAdele_one]
  inv_val := by
    rw [threeAdele_mul, Rat.cast_inv, inv_mul_cancel₀ rat3_ne, threeAdele_one]

theorem threeAdele_integral {x : ℚ_[3]} (hx : ‖x‖ ≤ 1) :
    threeAdele x ∈ integralEmbedding.range := by
  have h1 : (1 : FiniteAdeles) ∈ integralEmbedding.range := Subring.one_mem _
  have h2 : finiteAtThreeScalar 1 ∈ integralEmbedding.range := by
    have := finiteAtThreeScalar_integral (1 : ℤ_[3])
    rw [PadicInt.coe_one] at this
    exact this
  have h3 : finiteAtThreeScalar x ∈ integralEmbedding.range :=
    finiteAtThreeScalar_integral (⟨x, hx⟩ : ℤ_[3])
  exact Subring.add_mem _ (Subring.sub_mem _ h1 h2) h3

theorem threeUnit_norm {q : ℚˣ} (h1 : Int3 q) (h2 : Int3 (q : ℚ)⁻¹) :
    adeleNorm (SphericalDetection.Helpers.finiteAdeleUnit (threeUnit q)) = 1 := by
  obtain ⟨a, ha⟩ := threeAdele_integral (x := ((q : ℚ) : ℚ_[3])) h1
  obtain ⟨b, hb⟩ := threeAdele_integral (x := (((q : ℚ)⁻¹ : ℚ) : ℚ_[3])) h2
  have hab : a * b = 1 := by
    apply integralEmbedding_injective
    rw [map_mul, ha, hb, map_one]
    exact (threeUnit q).val_inv
  have hba : b * a = 1 := by rw [mul_comm]; exact hab
  have : SphericalDetection.Helpers.finiteAdeleUnit (threeUnit q) =
      integralAdeleUnit ⟨a, b, hab, hba⟩ := by
    apply Units.ext
    change ((1 : ℝ), threeAdele (q : ℚ)) = ((1 : ℝ), integralEmbedding a)
    rw [ha]
  rw [this]
  exact EisensteinRegularization.Helpers.adeleNorm_integralAdeleUnit _

theorem finiteThree_rat (q : ℚ) : finiteThree (algebraMap ℚ FiniteAdeles q) = (q : ℚ_[3]) := by
  change threeCompletionEquiv (finiteEvaluation placeThree (algebraMap ℚ FiniteAdeles q)) = _
  rw [finiteEvaluation_rational, eq_ratCast (algebraMap ℚ _) q, map_ratCast]

theorem unitF_split (q : ℚˣ) : unitF q = unitAway (unitF q) * threeUnit q := by
  apply Units.ext
  apply finiteAdeles_eq_of_three_and_away
  · change finiteThree (algebraMap ℚ FiniteAdeles (q : ℚ)) =
      finiteThree (adeleAway (algebraMap ℚ FiniteAdeles (q : ℚ)) 1 * threeAdele (q : ℚ))
    rw [map_mul, threeAdele_three, finiteThree_rat]
    change _ = threeCompletionEquiv (finiteEvaluation placeThree _) * _
    rw [adeleAway_three, map_one, one_mul]
  · intro v hv
    change finiteEvaluation v (algebraMap ℚ FiniteAdeles (q : ℚ)) =
      finiteEvaluation v (adeleAway (algebraMap ℚ FiniteAdeles (q : ℚ)) 1 * threeAdele (q : ℚ))
    rw [map_mul, adeleAway_away _ _ hv, threeAdele_away _ hv, mul_one]

theorem finiteAdeleUnit_mul (a b : FiniteAdelesˣ) :
    SphericalDetection.Helpers.finiteAdeleUnit (a * b) =
      SphericalDetection.Helpers.finiteAdeleUnit a * SphericalDetection.Helpers.finiteAdeleUnit b := by
  apply Units.ext
  change ((1 : ℝ), (a * b).val) = ((1 : ℝ) * 1, a.val * b.val)
  simp

theorem rational_split (q : ℚˣ) :
    Units.map rationalAdele q =
      realAdeleUnit (Units.map (algebraMap ℚ ℝ : ℚ →* ℝ) q) *
        SphericalDetection.Helpers.finiteAdeleUnit (unitF q) := by
  apply Units.ext
  change rationalAdele (q : ℚ) = (((q : ℚ) : ℝ) * 1, 1 * algebraMap ℚ FiniteAdeles (q : ℚ))
  simp [rationalAdele]

/-- **Product formula for away-from-three ideles.** -/
theorem adeleNorm_sAd {q : ℚˣ} (h1 : Int3 q) (h2 : Int3 (q : ℚ)⁻¹) :
    (adeleNorm (sAd q) : ℝ) = |(q : ℝ)|⁻¹ := by
  have h := congrArg adeleNorm (rational_split q)
  rw [EisensteinRegularization.Helpers.adeleNorm_rational, map_mul, unitF_split,
    finiteAdeleUnit_mul, map_mul, threeUnit_norm h1 h2, mul_one] at h
  have hr := congrArg (fun x : NNReal => (x : ℝ)) h
  simp only [NNReal.coe_one, NNReal.coe_mul,
    EisensteinRegularization.Helpers.adeleNorm_realAdeleUnit] at hr
  have hq : |((q : ℚ) : ℝ)| ≠ 0 := by
    rw [abs_ne_zero]; exact_mod_cast q.ne_zero
  rw [sAd]
  field_simp
  change (1 : ℝ) = _ at hr
  rw [hr]
  simp [Units.coe_map, mul_comm]

theorem np_add (t : Adelesˣ) (a b : ℂ) : normPower t (a + b) = normPower t a * normPower t b := by
  simp only [normPower, add_mul, Complex.exp_add]

theorem np_real_two {t : Adelesˣ} {x : ℝ} (hx : 0 < x) (ht : (adeleNorm t : ℝ) = x) :
    normPower t 2 = ((x ^ 2 : ℝ) : ℂ) := by
  rw [normPower, ht]
  have : (2 : ℂ) * (Real.log x : ℂ) = ((Real.log (x ^ 2) : ℝ) : ℂ) := by
    rw [Real.log_pow]; push_cast; ring
  rw [this, ← Complex.ofReal_exp, Real.exp_log (by positivity)]

theorem np_real_neg_one {t : Adelesˣ} {x : ℝ} (hx : 0 < x) (ht : (adeleNorm t : ℝ) = x) :
    normPower t (-1) = ((x⁻¹ : ℝ) : ℂ) := by
  rw [normPower, ht]
  have : (-1 : ℂ) * (Real.log x : ℂ) = ((Real.log x⁻¹ : ℝ) : ℂ) := by
    rw [Real.log_inv]; push_cast; ring
  rw [this, ← Complex.ofReal_exp, Real.exp_log (by positivity)]

/-- The determinant of the away part of a rational `GL₂` element. -/
theorem det_atFinite_Bo (A : GeneralLinearGroup (Fin 2) ℚ) :
    GeneralLinearGroup.det (atFinite (Bo A)) = sAd (GeneralLinearGroup.det A) := by
  apply Units.ext
  apply Prod.ext
  · change (RingHom.fst ℝ FiniteAdeles) ((atFinite (Bo A)).val.det) = 1
    rw [RingHom.map_det]
    have : (RingHom.fst ℝ FiniteAdeles).mapMatrix (atFinite (Bo A)).val = 1 := by
      ext i j
      simp [atFinite, combineGL, pairMatrix, Matrix.one_apply]
    rw [this, det_one]
  · change (RingHom.snd ℝ FiniteAdeles) ((atFinite (Bo A)).val.det) =
      adeleAway (algebraMap ℚ FiniteAdeles A.val.det) 1
    rw [RingHom.map_det]
    have : (RingHom.snd ℝ FiniteAdeles).mapMatrix (atFinite (Bo A)).val = (Bo A).val := by
      ext i j
      simp [atFinite, combineGL, pairMatrix]
    rw [this]
    apply finiteAdele_ext
    intro v
    rw [RingHom.map_det]
    by_cases hv : v = placeThree
    · subst hv
      rw [adeleAway_three]
      have h3 := congrArg Units.val (glAway2_three (glF A))
      change (finiteEvaluation placeThree).mapMatrix (Bo A).val = 1 at h3
      rw [h3, det_one]
    · rw [adeleAway_away _ _ hv]
      have h3 := congrArg Units.val (glAway2_away (glF A) hv)
      change (finiteEvaluation v).mapMatrix (Bo A).val =
        (finiteEvaluation v).mapMatrix (glF A).val at h3
      rw [h3, ← RingHom.map_det]
      congr 1
      change ((algebraMap ℚ FiniteAdeles).mapMatrix A.val).det = _
      rw [← RingHom.map_det]

theorem det_transposeGL {R : Type*} [CommRing R] (x : GeneralLinearGroup (Fin 2) R) :
    GeneralLinearGroup.det (transposeGL x) = GeneralLinearGroup.det x := by
  apply Units.ext
  change (transposeGL x).val.det = x.val.det
  simp [transposeGL, det_transpose]

theorem exponent_line : 2 * inductionExponent .line cohomologicalPoint =
    -2 * inductionExponent .plane cohomologicalPoint + 2 := by
  simp only [inductionExponent, cohomologicalPoint]; ring

theorem exponent_lineExp (n : ℕ) : lineExp n = planeExp n + (-1) := by
  simp only [lineExp, planeExp, inductionExponent, cohomologicalPoint]; ring

variable {n : ℕ}

/-- **Line weight versus plane weight.** -/
theorem lineWeight_eq (D : InducingData n) (s : Adelesˣ) {B : BinaryFiniteGL}
    (hB : B ∈ awayGroup placeThree) :
    lineWeight D s B = planeWeight D s (transposeGL B) *
      (normPower s 2 * normPower (GeneralLinearGroup.det (atFinite B)) (-1)) := by
  have hdet : GeneralLinearGroup.det (atFinite (transposeGL B)) =
      GeneralLinearGroup.det (atFinite B) := by
    rw [← transposeGL_atFinite, det_transposeGL]
  rw [lineWeight, planeWeight, omega_transpose D.cusp hB, hdet, exponent_line, exponent_lineExp,
    np_add, np_add]
  ring

end TernaryPeriodPolynomials.HeckeEigen.Satake
