module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.PlaneDecomposition

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.ParabolicDecomposition

variable {R : Type} [CommRing R]

def planeBinaryBlock (element : GL3 R) : Matrix (Fin 2) (Fin 2) R :=
  !![element.val 0 0, element.val 0 1;
    element.val 1 0, element.val 1 1]

theorem planeBinaryBlock_mul_inv (element : GL3 R)
    (membership : element ∈ planeParabolic R) :
    planeBinaryBlock element * planeBinaryBlock element⁻¹ = 1 := by
  have inverseMembership := (planeParabolic R).inv_mem membership
  have inverseZeroFirst : (element.val)⁻¹ 2 0 = 0 := by
    simpa using inverseMembership.1
  have inverseZeroSecond : (element.val)⁻¹ 2 1 = 0 := by
    simpa using inverseMembership.2
  ext row column
  have equation := congrArg (fun matrix : Matrix (Fin 3) (Fin 3) R =>
    matrix row.castSucc column.castSucc) element.mul_inv
  fin_cases row <;> fin_cases column <;>
    simpa [planeBinaryBlock, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three,
      inverseZeroFirst, inverseZeroSecond] using equation

def planeBinaryUnit (element : GL3 R) (membership : element ∈ planeParabolic R) :
    GeneralLinearGroup (Fin 2) R where
  val := planeBinaryBlock element
  inv := planeBinaryBlock element⁻¹
  val_inv := planeBinaryBlock_mul_inv element membership
  inv_val := by
    simpa only [inv_inv] using
      planeBinaryBlock_mul_inv element⁻¹ ((planeParabolic R).inv_mem membership)

def planeRankOneUnit (element : GL3 R) (membership : element ∈ planeParabolic R) : Rˣ where
  val := element.val 2 2
  inv := element.inv 2 2
  val_inv := by
    simpa [Matrix.mul_apply, Fin.sum_univ_three, membership.1, membership.2] using
      congrArg (fun matrix : Matrix (Fin 3) (Fin 3) R => matrix 2 2) element.mul_inv
  inv_val := by
    simpa [Matrix.mul_apply, Fin.sum_univ_three, membership.1, membership.2, mul_comm] using
      congrArg (fun matrix : Matrix (Fin 3) (Fin 3) R => matrix 2 2) element.mul_inv

theorem plane_decomposition (element : GL3 R) (membership : element ∈ planeParabolic R) :
    element = planeUnipotent (element.val 0 2 * (planeRankOneUnit element membership).inv)
        (element.val 1 2 * (planeRankOneUnit element membership).inv) *
      planeLevi (planeBinaryUnit element membership) (planeRankOneUnit element membership) := by
  have corner := (planeRankOneUnit element membership).inv_val
  have cornerEquation : (element.val)⁻¹ 2 2 * element.val 2 2 = 1 := by
    simpa [planeRankOneUnit] using corner
  apply GeneralLinearGroup.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    simp [planeUnipotent, planeLevi, planeBlock, planeBinaryUnit, planeBinaryBlock,
      planeRankOneUnit, Matrix.mul_apply, Fin.sum_univ_three, membership.1,
      membership.2, mul_assoc, cornerEquation]

theorem plane_decomposition_exists (element : GL3 R)
    (membership : element ∈ planeParabolic R) :
    ∃ first second : R, ∃ binary : GeneralLinearGroup (Fin 2) R, ∃ unit : Rˣ,
      element = planeUnipotent first second * planeLevi binary unit :=
  ⟨_, _, _, _, plane_decomposition element membership⟩

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.ParabolicDecomposition
