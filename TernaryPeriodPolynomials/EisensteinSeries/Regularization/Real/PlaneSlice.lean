module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Real.PlaneCoordinates

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

local notation "RealSL3" => SpecialLinearGroup (Fin 3) ℝ

def realPlaneNormalSet : Set RealSL3 :=
  {matrix | ∀ row : Fin 2, realPlaneCoordinate matrix row = 0}

theorem realPlaneNormalSet_closed : IsClosed realPlaneNormalSet := by
  change IsClosed {matrix | ∀ row : Fin 2, realPlaneCoordinate matrix row = 0}
  have sets : {matrix : RealSL3 | ∀ row : Fin 2, realPlaneCoordinate matrix row = 0} =
      ⋂ row : Fin 2, {matrix : RealSL3 | realPlaneCoordinate matrix row = 0} := by
    ext matrix
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
  rw [sets]
  exact isClosed_iInter (fun row : Fin 2 => isClosed_eq (realPlaneCoordinate_continuous row)
    (continuous_const : Continuous (fun _ : RealSL3 => (0 : ℝ))))

theorem realPlaneBase_mem_normalSet (matrix : RealSL3) : realPlaneBase matrix ∈ realPlaneNormalSet :=
  realPlaneCoordinate_base matrix

theorem realPlaneBase_of_mem_normalSet (matrix : RealSL3) (member : matrix ∈ realPlaneNormalSet) :
    realPlaneBase matrix = matrix := by
  rw [realPlaneBase, member 0, member 1, neg_zero, realSpecialPlane_zero, one_mul]

theorem realPlaneCoordinate_pair_plane_mul (coordinates : ℝ × ℝ) (matrix : RealSL3) :
    (realPlaneCoordinate (realSpecialPlane coordinates.1 coordinates.2 * matrix) 0,
      realPlaneCoordinate (realSpecialPlane coordinates.1 coordinates.2 * matrix) 1) =
      coordinates + (realPlaneCoordinate matrix 0, realPlaneCoordinate matrix 1) := by
  have first := realPlaneCoordinate_plane_mul ![coordinates.1, coordinates.2] matrix 0
  have second := realPlaneCoordinate_plane_mul ![coordinates.1, coordinates.2] matrix 1
  exact Prod.ext first second

noncomputable def realPlaneCoordinatesHomeomorph :
    RealSL3 ≃ₜ (ℝ × ℝ) × realPlaneNormalSet where
  toFun matrix := ((realPlaneCoordinate matrix 0, realPlaneCoordinate matrix 1),
    ⟨realPlaneBase matrix, realPlaneBase_mem_normalSet matrix⟩)
  invFun point := realSpecialPlane point.1.1 point.1.2 * point.2.val
  left_inv := realPlaneBase_factorization
  right_inv point := by
    apply Prod.ext
    · change (realPlaneCoordinate _ 0, realPlaneCoordinate _ 1) = point.1
      rw [realPlaneCoordinate_pair_plane_mul, point.2.property 0, point.2.property 1]
      exact add_zero point.1
    · apply Subtype.ext
      change realPlaneBase (realSpecialPlane point.1.1 point.1.2 * point.2.val) = point.2.val
      have base := realPlaneBase_plane_mul ![point.1.1, point.1.2] point.2.val
      exact base.trans (realPlaneBase_of_mem_normalSet point.2.val point.2.property)
  continuous_toFun :=
    ((realPlaneCoordinate_continuous 0).prodMk (realPlaneCoordinate_continuous 1)).prodMk
      (realPlaneBase_continuous.subtype_mk realPlaneBase_mem_normalSet)
  continuous_invFun := (realSpecialPlane_continuous.comp continuous_fst).mul
    (continuous_subtype_val.comp continuous_snd)

theorem realPlaneCoordinatesHomeomorph_plane_mul (coordinates : ℝ × ℝ) (matrix : RealSL3) :
    realPlaneCoordinatesHomeomorph (realSpecialPlane coordinates.1 coordinates.2 * matrix) =
      (coordinates + (realPlaneCoordinatesHomeomorph matrix).1,
        (realPlaneCoordinatesHomeomorph matrix).2) := by
  apply Prod.ext
  · exact realPlaneCoordinate_pair_plane_mul coordinates matrix
  · apply Subtype.ext
    exact realPlaneBase_plane_mul ![coordinates.1, coordinates.2] matrix

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
