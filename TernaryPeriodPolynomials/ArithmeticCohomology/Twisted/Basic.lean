module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Radical.Lattice

@[expose] public section


/-!
# The sign-twisted coefficient system

For a rank-one character `χ`, the coefficient representation `rationalCoefficientComponent n χ` of
`GL₃(ℚ)` is the trivial-character one, `rationalCoefficientComponent n trivialCharacter`,
multiplied by the scalar `detSign χ g = χ(sgn det g)`.  Since `χ` is trivial on the positive reals,
the scalar only depends on `e = χ(-1_∞)`, and for the odd quadratic character of conductor three
(`e = -1`) it is the sign of the rational determinant.  On every group element of positive
determinant (in particular on the radicals and on all elements of determinant `p > 0`) the two
representations agree.

This file only records the dictionary used to carry the level-one local computations of
`AxiomCodeSpectral` (stated for `trivialCharacter`) over to `e = -1`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace TernaryPeriodPolynomials.Twisted

/-- The value of a rank-one character at a real unit only depends on the sign. -/
theorem character_realUnit (χ : RankOneCharacter) (t : ℝˣ) :
    χ.toMonoidHom (realAdeleUnit t) =
      if 0 < t.val then 1 else χ.toMonoidHom (realAdeleUnit (-1)) := by
  split_ifs with h
  · exact χ.positiveReal t h
  · have hneg : t.val < 0 := lt_of_le_of_ne (not_lt.mp h) t.ne_zero
    have hpos : 0 < (-t).val := by
      rw [Units.val_neg]
      exact neg_pos.mpr hneg
    have hdec : t = (-1) * (-t) := by rw [neg_mul, one_mul, neg_neg]
    have hmul := map_mul realUnitHom (-1 : ℝˣ) (-t)
    rw [← hdec] at hmul
    have hmul' : realAdeleUnit t = realAdeleUnit (-1) * realAdeleUnit (-t) := hmul
    rw [hmul', map_mul, χ.positiveReal _ hpos, mul_one]

/-- The scalar by which `rationalCoefficientComponent n χ` differs from the trivial-character
representation: `χ` evaluated at the real determinant. -/
def detSign (χ : RankOneCharacter) : RationalGL3 →* ℂ :=
  (componentCharacter χ).comp (GeneralLinearGroup.map (algebraMap ℚ ℝ))

theorem detSign_apply (χ : RankOneCharacter) (g : RationalGL3) :
    detSign χ g = χ.toMonoidHom (realAdeleUnit
      (GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap ℚ ℝ) g))) := rfl

theorem detSign_eq_ite (χ : RankOneCharacter) (g : RationalGL3) :
    detSign χ g =
      if 0 < g.val.det then 1 else χ.toMonoidHom (realAdeleUnit (-1)) := by
  rw [detSign_apply, character_realUnit]
  have hdet : ((GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap ℚ ℝ) g) : ℝˣ) : ℝ) =
      algebraMap ℚ ℝ g.val.det := by
    rw [GeneralLinearGroup.val_det_apply]
    exact (RingHom.map_det (algebraMap ℚ ℝ) g.val).symm
  have hiff : (0 : ℝ) < ((GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap ℚ ℝ) g) : ℝˣ) : ℝ) ↔
      0 < g.val.det := by
    rw [hdet, eq_ratCast]
    exact Rat.cast_pos
  simp only [hiff]

/-- On elements of positive determinant the scalar is `1`, for every character. -/
theorem detSign_of_pos (χ : RankOneCharacter) {g : RationalGL3} (hg : 0 < g.val.det) :
    detSign χ g = 1 := by
  rw [detSign_eq_ite, ite_eq_left hg]

/-- For `χ(-1_∞) = -1` the scalar is the sign of the rational determinant. -/
theorem detSign_odd {χ : RankOneCharacter} (h : χ.toMonoidHom (realAdeleUnit (-1)) = -1)
    (g : RationalGL3) : detSign χ g = if 0 < g.val.det then 1 else -1 := by
  rw [detSign_eq_ite, h]

/-- **The sign twist.**  `rationalCoefficientComponent n χ g = detSign χ g • rationalCoefficientComponent
n trivialCharacter g`. -/
theorem rho_eq_detSign_smul (n : ℕ) (χ : RankOneCharacter) (g : RationalGL3) :
    rationalCoefficientComponent n χ g =
      detSign χ g • rationalCoefficientComponent n trivialCharacter g := by
  apply LinearMap.ext
  intro v
  change componentCharacter χ (GeneralLinearGroup.map (algebraMap ℚ ℝ) g) •
      realCoefficient n (GeneralLinearGroup.map (algebraMap ℚ ℝ) g) v =
    detSign χ g • ((1 : ℂ) • realCoefficient n (GeneralLinearGroup.map (algebraMap ℚ ℝ) g) v)
  rw [one_smul]
  rfl

theorem rho_apply_eq_detSign_smul (n : ℕ) (χ : RankOneCharacter) (g : RationalGL3)
    (v : HomogeneousPoly n) :
    rationalCoefficientComponent n χ g v =
      detSign χ g • rationalCoefficientComponent n trivialCharacter g v := by
  rw [rho_eq_detSign_smul]
  rfl

/-- On elements of positive determinant the two coefficient representations agree. -/
theorem rho_eq_of_pos (n : ℕ) (χ : RankOneCharacter) {g : RationalGL3} (hg : 0 < g.val.det) :
    rationalCoefficientComponent n χ g = rationalCoefficientComponent n trivialCharacter g := by
  rw [rho_eq_detSign_smul, detSign_of_pos χ hg, one_smul]

/-- The sign is multiplicative: the twisted representation is `ρ ⊗ detSign`. -/
theorem detSign_mul (χ : RankOneCharacter) (g h : RationalGL3) :
    detSign χ (g * h) = detSign χ g * detSign χ h := map_mul _ g h

theorem det_planeUnipotent (a b : ℚ) : (planeUnipotent a b).val.det = 1 := by
  simp [planeUnipotent, Matrix.det_fin_three]

theorem det_lowerPlaneUnipotent (a b : ℚ) : (lowerPlaneUnipotent a b).val.det = 1 := by
  simp [lowerPlaneUnipotent, Matrix.det_fin_three]

/-- The twisted and untwisted coefficient actions agree on the upper radical. -/
theorem rho_upperRadicalLattice (n : ℕ) (χ : RankOneCharacter) (element : RadicalLattice) :
    rationalCoefficientComponent n χ (upperRadicalLattice element) =
      rationalCoefficientComponent n trivialCharacter (upperRadicalLattice element) :=
  rho_eq_of_pos n χ (by
    change 0 < (planeUnipotent (element.toAdd.1 : ℚ) (element.toAdd.2 : ℚ)).val.det
    rw [det_planeUnipotent]
    exact one_pos)

/-- The twisted and untwisted coefficient actions agree on the lower radical. -/
theorem rho_lowerRadicalLattice (n : ℕ) (χ : RankOneCharacter) (element : RadicalLattice) :
    rationalCoefficientComponent n χ (lowerRadicalLattice element) =
      rationalCoefficientComponent n trivialCharacter (lowerRadicalLattice element) :=
  rho_eq_of_pos n χ (by
    change 0 < (lowerPlaneUnipotent (3 * (element.toAdd.1 : ℚ)) (3 * (element.toAdd.2 : ℚ))).val.det
    rw [det_lowerPlaneUnipotent]
    exact one_pos)

end TernaryPeriodPolynomials.Twisted
