module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.PlaneFaceTransfer
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Face.GoodPlane
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Face.BadPlane

@[expose] public section


/-!
# The two reference planes of the level group as `planeFlagAt h`

Paper: Lemma C.3 (`ar:lem:seed`).

The level group has two orbits of rational planes, represented by the bad plane `⟨e₁, e₂⟩`
(`Face.badPlaneFlag`) and the good plane `⟨e₃, e₂⟩` (`Face.goodPlaneFlag`).
`planeFlagAt_one`: `planeFlagAt 1 = Face.badPlaneFlag`;
`planeFlagAt_wGood`: `planeFlagAt wGood = Face.goodPlaneFlag` for the determinant-one signed permutation
matrix `wGood`.  So the plane-cusp descent and transfer of `PlaneFaceDescent`, `PlaneFaceTransfer`
apply to both reference planes.

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups
open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.Argument
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3S4c

/-- The determinant-one signed permutation matrix `e₁ ↦ e₃, e₂ ↦ -e₂, e₃ ↦ e₁`; it carries the good
plane `⟨e₃, e₂⟩` to the standard plane. -/
def wGood : SL(3, ℤ) :=
  ⟨!![0, 0, 1; 0, -1, 0; 1, 0, 0], by rw [Matrix.det_fin_three]; simp⟩

theorem planeFlagAt_one : planeFlagAt 1 = FacePairingFull.Face.badPlaneFlag := by
  change (QuotientGroup.mk (Matrix.SpecialLinearGroup.mapGL ℚ (1 : SL(3, ℤ))⁻¹) : Flags .plane) =
    QuotientGroup.mk 1
  simp

theorem wGood_inv : (wGood)⁻¹ = wGood := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_inv]
  rw [Matrix.adjugate_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wGood]

theorem planeFlagAt_wGood : planeFlagAt wGood = FacePairingFull.Face.goodPlaneFlag := by
  change (QuotientGroup.mk (Matrix.SpecialLinearGroup.mapGL ℚ wGood⁻¹) : Flags .plane) =
    dualFlag standardBadLine
  change _ = (QuotientGroup.mk (dualInvolution 1 * longWeyl) : Flags .plane)
  rw [map_one, one_mul, wGood_inv]
  apply QuotientGroup.eq.mpr
  rw [← map_inv, wGood_inv]
  refine ⟨?_, ?_⟩
  · simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]
    change ((wGood : Matrix (Fin 3) (Fin 3) ℤ) 2 0 : ℚ) * longWeylMatrix 0 0 +
      ((wGood : Matrix (Fin 3) (Fin 3) ℤ) 2 1 : ℚ) * longWeylMatrix 1 0 +
      ((wGood : Matrix (Fin 3) (Fin 3) ℤ) 2 2 : ℚ) * longWeylMatrix 2 0 = 0
    simp [wGood, longWeylMatrix]
  · simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]
    change ((wGood : Matrix (Fin 3) (Fin 3) ℤ) 2 0 : ℚ) * longWeylMatrix 0 1 +
      ((wGood : Matrix (Fin 3) (Fin 3) ℤ) 2 1 : ℚ) * longWeylMatrix 1 1 +
      ((wGood : Matrix (Fin 3) (Fin 3) ℤ) 2 2 : ℚ) * longWeylMatrix 2 1 = 0
    simp [wGood, longWeylMatrix]

end TernaryPeriodPolynomials.Argument.SeedC3S4c
