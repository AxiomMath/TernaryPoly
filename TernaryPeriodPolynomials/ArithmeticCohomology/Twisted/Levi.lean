module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.Basic
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Arithmetic.LeviLattice

@[expose] public section


/-!
# The sign twist on the arithmetic Levi subgroup

For `m ∈ GL₂(ℤ)` the Levi element `arithmeticLevi m = diag(m, 1)` has determinant `det m = ±1`, so
for a character with `χ(-1_∞) = -1` the twisted Levi coefficient action is
`det m • arithmeticLeviCoefficient n m`.  Since `Binary.homogeneousAction d (τ + 1) A =
det A • Binary.homogeneousAction d τ A`, every `GL₂(ℤ)`-module `Sym^d ⊗ det^τ` that appears at a
level-one cusp for the trivial character appears for the twisted character with `τ` replaced by
`τ + 1`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace TernaryPeriodPolynomials.Twisted

/-- The rational determinant of an arithmetic Levi element. -/
theorem det_arithmeticLevi (m : GeneralLinearGroup (Fin 2) ℤ) :
    (arithmeticLevi m).val.det = ((m.val.det : ℤ) : ℚ) := by
  have h1 : (arithmeticLevi m).val.det = (Int.castRingHom ℚ) (planeLevi m 1).val.det :=
    (RingHom.map_det (Int.castRingHom ℚ) (planeLevi m 1).val).symm
  have h2 : (planeLevi m 1).val.det = m.val.det := by
    change (planeBlock m.val (1 : ℤˣ).val).det = _
    simp [planeBlock, Matrix.det_fin_three, Matrix.det_fin_two]
  rw [h1, h2]
  rfl

/-- For `χ(-1_∞) = -1` the determinant sign of a Levi element is its integral determinant. -/
theorem detSign_arithmeticLevi_odd {χ : RankOneCharacter}
    (h : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (m : GeneralLinearGroup (Fin 2) ℤ) :
    detSign χ (arithmeticLevi m) = (((GeneralLinearGroup.det m : ℤˣ) : ℤ) : ℂ) := by
  rw [detSign_odd h, det_arithmeticLevi]
  have hv : ((GeneralLinearGroup.det m : ℤˣ) : ℤ) = m.val.det := GeneralLinearGroup.val_det_apply m
  rw [← hv]
  rcases Int.units_eq_one_or (GeneralLinearGroup.det m) with hd | hd
  · rw [hd]
    simp
  · rw [hd]
    simp

/-- **The twisted Levi coefficient action.** -/
theorem rho_arithmeticLevi_odd (n : ℕ) {χ : RankOneCharacter}
    (h : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (m : GeneralLinearGroup (Fin 2) ℤ) :
    rationalCoefficientComponent n χ (arithmeticLevi m) =
      (((GeneralLinearGroup.det m : ℤˣ) : ℤ) : ℂ) • arithmeticLeviCoefficient n m := by
  rw [rho_eq_detSign_smul, detSign_arithmeticLevi_odd h]
  rfl

/-- Raising the determinant twist by one multiplies the binary action by the determinant. -/
theorem homogeneousAction_succ_twist (d : ℕ) (τ : ℤ) (A : Binary.GL2) :
    Binary.homogeneousAction d (τ + 1) A =
      (((GeneralLinearGroup.det A : ℂˣ) : ℂ)) • Binary.homogeneousAction d τ A := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  rw [Binary.homogeneousAction_coe, LinearMap.smul_apply, Submodule.coe_smul,
    Binary.homogeneousAction_coe, Binary.action_apply, Binary.action_apply, smul_smul]
  congr 1
  change ((GeneralLinearGroup.det A : ℂˣ) : ℂ) ^ (τ + 1) =
    ((GeneralLinearGroup.det A : ℂˣ) : ℂ) * ((GeneralLinearGroup.det A : ℂˣ) : ℂ) ^ τ
  rw [zpow_add_one₀ (Units.ne_zero _), mul_comm]

end TernaryPeriodPolynomials.Twisted
