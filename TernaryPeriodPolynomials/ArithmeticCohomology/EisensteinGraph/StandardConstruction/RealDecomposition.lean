module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.ParabolicDecomposition
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.RealDecomposition

abbrev RealVectors := EuclideanSpace ℝ (Fin 3)

def isometryMatrix (isometry : RealVectors ≃ₗᵢ[ℝ] RealVectors) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.toMatrix
    ((EuclideanSpace.basisFun (Fin 3) ℝ).map isometry)

theorem basis_repr (vector : RealVectors) (index : Fin 3) :
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.repr vector index = vector index := by
  rfl

theorem basis_repr_function (vector : RealVectors) :
    ⇑((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.repr vector) = vector.ofLp := by
  funext index
  exact basis_repr vector index

theorem isometryMatrix_orthogonal (isometry : RealVectors ≃ₗᵢ[ℝ] RealVectors) :
    isometryMatrix isometry ∈ Matrix.orthogonalGroup (Fin 3) ℝ :=
  OrthonormalBasis.toMatrix_orthonormalBasis_mem_orthogonal _ _

theorem isometryMatrix_eq_toMatrix (isometry : RealVectors ≃ₗᵢ[ℝ] RealVectors) :
    isometryMatrix isometry = LinearMap.toMatrix
      (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis isometry.toLinearEquiv.toLinearMap := by
  ext row column
  simp only [isometryMatrix, Module.Basis.toMatrix_apply, OrthonormalBasis.map_apply,
    LinearMap.toMatrix_apply]
  rfl

theorem isometryMatrix_mulVec (isometry : RealVectors ≃ₗᵢ[ℝ] RealVectors)
    (vector : RealVectors) :
    isometryMatrix isometry *ᵥ vector.ofLp = (isometry vector).ofLp := by
  rw [isometryMatrix_eq_toMatrix]
  simpa [basis_repr_function] using LinearMap.toMatrix_mulVec_repr
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis isometry.toLinearEquiv.toLinearMap vector

def isometryUnit (isometry : RealVectors ≃ₗᵢ[ℝ] RealVectors) : GL3 ℝ where
  val := isometryMatrix isometry
  inv := (isometryMatrix isometry).transpose
  val_inv := (Matrix.mem_orthogonalGroup_iff _ _).mp (isometryMatrix_orthogonal isometry)
  inv_val := (Matrix.mem_orthogonalGroup_iff' _ _).mp (isometryMatrix_orthogonal isometry)

theorem real_planeCompact (element : GL3 ℝ) :
    ∃ parabolic compact : GL3 ℝ, parabolic ∈ planeParabolic ℝ ∧
      compact.val.transpose * compact.val = 1 ∧ element = parabolic * compact := by
  let row : RealVectors := WithLp.toLp 2 (element.val 2)
  let target : RealVectors := EuclideanSpace.single 2 ‖row‖
  have equalNorm : ‖row‖ = ‖target‖ := by
    simp [target]
  let reflection : RealVectors ≃ₗᵢ[ℝ] RealVectors :=
    (Submodule.span ℝ {row - target})ᗮ.reflection
  have reflected : reflection row = target := Submodule.reflection_sub equalNorm
  let compact := isometryUnit reflection
  refine ⟨element * compact⁻¹, compact, ?_, ?_, ?_⟩
  · have transformed := isometryMatrix_mulVec reflection row
    rw [reflected] at transformed
    constructor
    · have coordinate := congrFun transformed 0
      change (element.val * (isometryMatrix reflection).transpose) 2 0 = 0
      simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, row, target, mul_comm] using coordinate
    · have coordinate := congrFun transformed 1
      change (element.val * (isometryMatrix reflection).transpose) 2 1 = 0
      simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, row, target, mul_comm] using coordinate
  · exact (Matrix.mem_orthogonalGroup_iff' _ _).mp (isometryMatrix_orthogonal reflection)
  · simp only [mul_assoc, inv_mul_cancel, mul_one]

theorem real_planeDecomposition (element : GL3 ℝ) :
    ∃ first second : ℝ, ∃ binary : GeneralLinearGroup (Fin 2) ℝ, ∃ unit : ℝˣ,
      ∃ compact : GL3 ℝ, compact.val.transpose * compact.val = 1 ∧
        element = planeUnipotent first second * planeLevi binary unit * compact := by
  obtain ⟨parabolic, compact, membership, orthogonal, decomposition⟩ :=
    real_planeCompact element
  obtain ⟨first, second, binary, unit, parabolicDecomposition⟩ :=
    ParabolicDecomposition.plane_decomposition_exists parabolic membership
  exact ⟨first, second, binary, unit, compact, orthogonal,
    decomposition.trans (congrArg (fun value => value * compact) parabolicDecomposition)⟩

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.RealDecomposition
