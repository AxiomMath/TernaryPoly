module

public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Eigen.Satake.HeckeFormula
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Eigen.Satake.RationalCosets

@[expose] public section


/-!
# Away-from-three parts and the rational parabolic factorization of representatives

For a representative `r = n m γ` (rational Iwasawa decomposition, `γ ∈ GL₃(ℤ)`) of an
away-from-three correspondence, removing the three-adic component of `n m` gives a finite
parabolic factorization `r = p κ` with `p` trivial at three and `κ ∈ finiteLevel`, whose Levi part
is the away-from-three part of the rational Levi part. This turns `plane_hecke_formula` and
`line_hecke_formula` into formulas in terms of rational Levi data.

Original work (AxiomDeep, Claude Opus 5.5).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.RepresentationTheory
open TernaryPeriodPolynomials.HeckeEigen

namespace TernaryPeriodPolynomials.HeckeEigen.Satake

/-! ### Scalars -/

theorem finiteAdele_ext {x y : FiniteAdeles}
    (h : ∀ v : FinitePlace, finiteEvaluation v x = finiteEvaluation v y) : x = y := by
  apply IsDedekindDomain.FiniteAdeleRing.ext ℚ
  intro v
  exact h v

/-- The finite adele agreeing with `x` away from three and equal to `c` at three. -/
def adeleAway (x : FiniteAdeles) (c : placeThree.adicCompletion ℚ) : FiniteAdeles :=
  x - finiteAtPlaceScalar placeThree (finiteEvaluation placeThree x) +
    finiteAtPlaceScalar placeThree c

theorem adeleAway_three (x : FiniteAdeles) (c : placeThree.adicCompletion ℚ) :
    finiteEvaluation placeThree (adeleAway x c) = c := by
  simp only [adeleAway, map_add, map_sub, finiteAtPlaceScalar_same, sub_self, zero_add]

theorem adeleAway_away (x : FiniteAdeles) (c : placeThree.adicCompletion ℚ) {v : FinitePlace}
    (hv : v ≠ placeThree) : finiteEvaluation v (adeleAway x c) = finiteEvaluation v x := by
  simp only [adeleAway, map_add, map_sub, finiteAtPlaceScalar_away _ _ _ hv, sub_zero, add_zero]

/-- The finite idele agreeing with `s` away from three and equal to one at three. -/
def unitAway (s : FiniteAdelesˣ) : FiniteAdelesˣ where
  val := adeleAway s.val 1
  inv := adeleAway s⁻¹.val 1
  val_inv := by
    apply finiteAdele_ext; intro v
    rw [map_mul, map_one]
    by_cases hv : v = placeThree
    · subst hv; rw [adeleAway_three, adeleAway_three, one_mul]
    · rw [adeleAway_away _ _ hv, adeleAway_away _ _ hv, ← map_mul, Units.mul_inv, map_one]
  inv_val := by
    apply finiteAdele_ext; intro v
    rw [map_mul, map_one]
    by_cases hv : v = placeThree
    · subst hv; rw [adeleAway_three, adeleAway_three, one_mul]
    · rw [adeleAway_away _ _ hv, adeleAway_away _ _ hv, ← map_mul, Units.inv_mul, map_one]

theorem unitAway_three (s : FiniteAdelesˣ) :
    Units.map (finiteEvaluation placeThree : FiniteAdeles →* placeThree.adicCompletion ℚ)
      (unitAway s) = 1 :=
  Units.ext (adeleAway_three _ _)

theorem unitAway_away (s : FiniteAdelesˣ) {v : FinitePlace} (hv : v ≠ placeThree) :
    Units.map (finiteEvaluation v : FiniteAdeles →* v.adicCompletion ℚ) (unitAway s) =
      Units.map (finiteEvaluation v : FiniteAdeles →* v.adicCompletion ℚ) s :=
  Units.ext (adeleAway_away _ _ hv)

/-! ### `GL₂` -/

/-- The away-from-three part of a finite `GL₂` element. -/
def glAway2 (B : BinaryFiniteGL) : BinaryFiniteGL := (placePart (v := placeThree) B)⁻¹ * B

theorem glAway2_mem (B : BinaryFiniteGL) : glAway2 B ∈ awayGroup placeThree :=
  mul_placePart_inv_mem B

theorem glAway2_three (B : BinaryFiniteGL) :
    GeneralLinearGroup.map (finiteEvaluation placeThree) (glAway2 B) = 1 :=
  mem_awayGroup.mp (glAway2_mem B)

theorem glAway2_away (B : BinaryFiniteGL) {v : FinitePlace} (hv : v ≠ placeThree) :
    GeneralLinearGroup.map (finiteEvaluation v) (glAway2 B) =
      GeneralLinearGroup.map (finiteEvaluation v) B := by
  rw [glAway2, map_mul, map_inv, placePart, finiteAtPlaceGL_away _ _ _ _ hv, inv_one, one_mul]

theorem glAway2_mul (B C : BinaryFiniteGL) : glAway2 (B * C) = glAway2 B * glAway2 C := by
  apply finiteGeneralLinearGroup_ext
  intro v
  by_cases hv : v = placeThree
  · subst hv; rw [map_mul, glAway2_three, glAway2_three, glAway2_three, one_mul]
  · rw [map_mul, glAway2_away _ hv, glAway2_away _ hv, glAway2_away _ hv, map_mul]

theorem glAway2_transpose (B : BinaryFiniteGL) :
    glAway2 (transposeGL B) = transposeGL (glAway2 B) := by
  apply finiteGeneralLinearGroup_ext
  intro v
  rw [← transposeGL_map]
  by_cases hv : v = placeThree
  · subst hv
    rw [glAway2_three, glAway2_three]
    apply Units.ext; simp [transposeGL]
  · rw [glAway2_away _ hv, glAway2_away _ hv, transposeGL_map]

theorem glAway2_level {k : BinaryFiniteGL} (hk : k ∈ sphericalFinite) :
    glAway2 k ∈ awayLevel placeThree :=
  ⟨glAway2_mem k, Subgroup.mul_mem sphericalFinite
    (Subgroup.inv_mem sphericalFinite (placePart_spherical hk)) hk⟩

/-! ### `GL₃` -/

/-- The away-from-three part of a finite `GL₃` element. -/
def glAway3 (x : FiniteGL) : FiniteGL := x * (finiteAtThree (GeneralLinearGroup.map finiteThree x))⁻¹

theorem glAway3_three (x : FiniteGL) :
    GeneralLinearGroup.map (finiteEvaluation placeThree) (glAway3 x) = 1 := by
  apply (finiteThree_eq_one_iff _).mp
  rw [glAway3, map_mul, map_inv, finiteAtThree_three, mul_inv_cancel]

theorem glAway3_away (x : FiniteGL) {v : FinitePlace} (hv : v ≠ placeThree) :
    GeneralLinearGroup.map (finiteEvaluation v) (glAway3 x) =
      GeneralLinearGroup.map (finiteEvaluation v) x := by
  rw [glAway3, map_mul, map_inv, finiteAtThree_away _ _ hv, inv_one, mul_one]

variable {R S : Type*} [CommRing R] [CommRing S]

theorem planeUnipotent_map (φ : R →+* S) (a b : R) :
    GeneralLinearGroup.map φ (planeUnipotent a b) = planeUnipotent (φ a) (φ b) := by
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [planeUnipotent, GeneralLinearGroup.map_apply]

theorem lineUnipotent_map (φ : R →+* S) (a b : R) :
    GeneralLinearGroup.map φ (lineUnipotent a b) = lineUnipotent (φ a) (φ b) := by
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [lineUnipotent, upperUnipotent, GeneralLinearGroup.map_apply]

theorem planeUnipotent_zero' : planeUnipotent (0 : R) 0 = 1 := (planeUnipotentHom R).map_one

theorem lineUnipotent_zero' : lineUnipotent (0 : R) 0 = 1 := (lineUnipotentHom R).map_one

theorem planeLevi_one' : planeLevi (1 : GeneralLinearGroup (Fin 2) R) (1 : Rˣ) = 1 :=
  (planeLeviHom R).map_one

theorem lineLevi_one' : lineLevi (1 : Rˣ) (1 : GeneralLinearGroup (Fin 2) R) = 1 :=
  (lineLeviHom R).map_one

theorem planeLevi_split (B : GeneralLinearGroup (Fin 2) R) (s : Rˣ) :
    planeLevi 1 s * planeLevi B 1 = planeLevi B s := by
  have := ((planeLeviHom R).map_mul (1, s) (B, 1)).symm
  simp only [Prod.mk_mul_mk, one_mul, mul_one] at this
  exact this

theorem lineLevi_split (d : Rˣ) (A : GeneralLinearGroup (Fin 2) R) :
    lineLevi d 1 * lineLevi 1 A = lineLevi d A := by
  have := ((lineLeviHom R).map_mul (d, 1) (1, A)).symm
  simp only [Prod.mk_mul_mk, one_mul, mul_one] at this
  exact this

/-! ### The away part of a rational parabolic element -/

/-- Finite image of a rational unit. -/
abbrev unitF (s : ℚˣ) : FiniteAdelesˣ := Units.map (algebraMap ℚ FiniteAdeles : ℚ →* FiniteAdeles) s

/-- Finite image of a rational `GL₂` element. -/
abbrev glF (B : GeneralLinearGroup (Fin 2) ℚ) : BinaryFiniteGL :=
  GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) B

theorem glAway3_plane (v : ℚ × ℚ) (B : GeneralLinearGroup (Fin 2) ℚ) (s : ℚˣ) :
    glAway3 (rationalFinite (pU v * planeLevi B s)) =
      planeUnipotent (adeleAway (algebraMap ℚ FiniteAdeles v.1) 0)
          (adeleAway (algebraMap ℚ FiniteAdeles v.2) 0) *
        (planeLevi 1 (unitAway (unitF s)) * planeLevi (glAway2 (glF B)) 1) := by
  rw [planeLevi_split]
  apply finiteGeneralLinearGroup_ext
  intro w
  by_cases hw : w = placeThree
  · subst hw
    rw [glAway3_three, map_mul, planeUnipotent_map, planeLevi_map, adeleAway_three,
      adeleAway_three, glAway2_three, unitAway_three, planeUnipotent_zero', planeLevi_one', mul_one]
  · rw [glAway3_away _ hw]
    change GeneralLinearGroup.map (finiteEvaluation w)
      (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) (planeUnipotent v.1 v.2 * planeLevi B s)) = _
    simp only [map_mul, planeUnipotent_map, planeLevi_map]
    rw [adeleAway_away _ _ hw, adeleAway_away _ _ hw, glAway2_away _ hw, unitAway_away _ hw]

theorem glAway3_line (v : ℚ × ℚ) (d : ℚˣ) (A : GeneralLinearGroup (Fin 2) ℚ) :
    glAway3 (rationalFinite (lU v * lineLevi d A)) =
      lineUnipotent (adeleAway (algebraMap ℚ FiniteAdeles v.1) 0)
          (adeleAway (algebraMap ℚ FiniteAdeles v.2) 0) *
        (lineLevi (unitAway (unitF d)) 1 * lineLevi 1 (glAway2 (glF A))) := by
  rw [lineLevi_split]
  apply finiteGeneralLinearGroup_ext
  intro w
  by_cases hw : w = placeThree
  · subst hw
    rw [glAway3_three, map_mul, lineUnipotent_map, lineLevi_map, adeleAway_three,
      adeleAway_three, glAway2_three, unitAway_three, lineUnipotent_zero', lineLevi_one', mul_one]
  · rw [glAway3_away _ hw]
    change GeneralLinearGroup.map (finiteEvaluation w)
      (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) (lineUnipotent v.1 v.2 * lineLevi d A)) = _
    simp only [map_mul, lineUnipotent_map, lineLevi_map]
    rw [adeleAway_away _ _ hw, adeleAway_away _ _ hw, glAway2_away _ hw, unitAway_away _ hw]

/-! ### The level part -/

theorem rationalFinite_integral (γ₀ : IntegralGL) :
    rationalFinite (integralRational γ₀) ∈ finiteIntegralGLLevel 3 := by
  refine ⟨GeneralLinearGroup.map (Int.castRingHom IntegralAdeles) γ₀, ?_⟩
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  simp [rationalFinite, integralRational, GeneralLinearGroup.map_apply]

theorem three_integral_map (γ₀ : IntegralGL) :
    GeneralLinearGroup.map padicThreeEmbedding
        (GeneralLinearGroup.map (Int.castRingHom ℤ_[3]) γ₀) =
      GeneralLinearGroup.map finiteThree (rationalFinite (integralRational γ₀)) := by
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  simp [rationalFinite, integralRational, GeneralLinearGroup.map_apply, padicThreeEmbedding]

/-- **The rational factorization is a level factorization.** -/
theorem level_factor {t : HeckeCorrespondence} (ht : AwayThree t) {r : RationalGL3}
    (hr : r ∈ t.representatives) (P : RationalGL3) (γ₀ : IntegralGL)
    (h : r = P * integralRational γ₀) :
    ∃ κ : finiteLevel, rationalFinite r = glAway3 (rationalFinite P) * κ.val := by
  set C := finiteAtThree (GeneralLinearGroup.map finiteThree (rationalFinite P)) with hC
  have hloc := rep_local_level ht hr
  have hloc' := hloc
  obtain ⟨k, _, hk⟩ := hloc'
  have hP : rationalFinite P = rationalFinite r * (rationalFinite (integralRational γ₀))⁻¹ := by
    rw [h, map_mul, mul_inv_cancel_right]
  have hCint : C ∈ finiteIntegralGLLevel 3 := by
    have hlift : GeneralLinearGroup.map padicThreeEmbedding
        (k * (GeneralLinearGroup.map (Int.castRingHom ℤ_[3]) γ₀)⁻¹) =
        GeneralLinearGroup.map finiteThree (rationalFinite P) := by
      rw [map_mul, map_inv, three_integral_map, hP, map_mul, map_inv]
      congr 1
    rw [hC, ← hlift]
    exact finiteAtThree_integral _
  set κ := C * rationalFinite (integralRational γ₀)
  have hκint : κ ∈ finiteIntegralGLLevel 3 := mul_mem hCint (rationalFinite_integral γ₀)
  have hκ3 : GeneralLinearGroup.map finiteThree κ = GeneralLinearGroup.map finiteThree (rationalFinite r) := by
    simp only [κ, C, map_mul, map_inv, finiteAtThree_three, hP, inv_mul_cancel_right]
  refine ⟨⟨κ, finiteLevel_of_integral_of_three κ hκint (hκ3 ▸ hloc)⟩, ?_⟩
  change rationalFinite r = rationalFinite P * C⁻¹ * (C * rationalFinite (integralRational γ₀))
  rw [mul_assoc, inv_mul_cancel_left, h, map_mul]

end TernaryPeriodPolynomials.HeckeEigen.Satake
