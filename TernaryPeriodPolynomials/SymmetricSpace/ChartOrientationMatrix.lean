module

public import TernaryPeriodPolynomials.SymmetricSpace.SymmetricSpaceChartOrientation
public import TernaryPeriodPolynomials.SymmetricSpace.ProjectiveChartOrientation

@[expose] public section

noncomputable section
namespace TernaryPoly.SymmetricSpaceChartOrientation
open Matrix
open SymmetricSpaceOrientation (Mat3 congruence)
open SymmetricSpaceCharts (Coordinates)

/-- Congruence transported through the literal five-entry-plus-trace coordinates. -/
def homogeneousLinear (g : Mat3) : HomogeneousCoordinates →ₗ[ℝ] HomogeneousCoordinates :=
  traceCoordinates.comp ((congruence g).comp fromTraceCoordinates)

/-- The actual matrix in the sum-type homogeneous coordinate basis. -/
def homogeneousMatrix (g : Mat3) : Matrix (Fin 5 ⊕ Unit) (Fin 5 ⊕ Unit) ℝ :=
  LinearMap.toMatrix' (homogeneousLinear g)

def chartA (g : Mat3) : Matrix (Fin 5) (Fin 5) ℝ :=
  fun i j => homogeneousMatrix g (.inl i) (.inl j)

def chartB (g : Mat3) : Coordinates := fun i => homogeneousMatrix g (.inl i) (.inr ())

def chartC (g : Mat3) : Coordinates := fun j => homogeneousMatrix g (.inr ()) (.inl j)

def chartD (g : Mat3) : ℝ := homogeneousMatrix g (.inr ()) (.inr ())

/-- The affine projective blocks are literal submatrices of the transported congruence. -/
theorem homogeneous_eq (g : Mat3) :
    ProjectiveChartOrientation.homogeneous (chartA g) (chartB g) (chartC g) (chartD g) =
      homogeneousMatrix g := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · rfl
  · cases j; rfl
  · cases i; rfl
  · cases i; cases j; rfl

/-- A change of the actual linear coordinates preserves the congruence determinant. -/
theorem homogeneousLinear_det (g : Mat3) : LinearMap.det (homogeneousLinear g)=g.det^4 := by
  calc
    _ = LinearMap.det (congruence g) := LinearMap.det_conj (congruence g) traceCoordinatesEquiv
    _ = g.det^4 := SymmetricSpaceOrientation.congruence_det g

/-- Exact homogeneous determinant, including singular real matrices. -/
theorem homogeneousMatrix_det (g : Mat3) : (homogeneousMatrix g).det=g.det^4 := by
  rw [homogeneousMatrix,LinearMap.det_toMatrix',homogeneousLinear_det]

theorem chart_homogeneous_det (g : Mat3) :
    (ProjectiveChartOrientation.homogeneous (chartA g) (chartB g) (chartC g) (chartD g)).det =
      g.det^4 := by rw [homogeneous_eq,homogeneousMatrix_det]

/-- The homogeneous matrix acts literally as congruence in the trace coordinates. -/
theorem homogeneousMatrix_mulVec (g : Mat3) (z : HomogeneousCoordinates) :
    homogeneousMatrix g *ᵥ z = traceCoordinates (congruence g (fromTraceCoordinates z)) :=
  LinearMap.toMatrix'_mulVec (homogeneousLinear g) z

/-- In the affine slice, the upper homogeneous coordinates are the affine numerator. -/
theorem homogeneousMatrix_affineLift_inl (g : Mat3) (x : Coordinates) (i : Fin 5) :
    (homogeneousMatrix g *ᵥ affineLift x) (.inl i) =
      ProjectiveChartOrientation.numerator (chartA g) (chartB g) x i := by
  simp [Matrix.mulVec,dotProduct,Fintype.sum_sum_type,affineLift,
    ProjectiveChartOrientation.numerator,chartA,chartB]

/-- In the affine slice, the trace homogeneous coordinate is the affine denominator. -/
theorem homogeneousMatrix_affineLift_inr (g : Mat3) (x : Coordinates) :
    (homogeneousMatrix g *ᵥ affineLift x) (.inr ()) =
      ProjectiveChartOrientation.denominator (chartC g) (chartD g) x := by
  simp [Matrix.mulVec,dotProduct,Fintype.sum_sum_type,affineLift,
    ProjectiveChartOrientation.denominator,chartC,chartD]

end TernaryPoly.SymmetricSpaceChartOrientation
