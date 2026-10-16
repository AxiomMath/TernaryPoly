module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.Good.TetrahedronSymmetry
public import TernaryPeriodPolynomials.Building.BoundaryApartments.RefinementComplexity

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Matrix

def goodVectorCoordinates (frame : RationalGL3) (vertex : NormalizedGoodVector) : Fin 3 → ℚ :=
  frame.inv *ᵥ (fun row => (vertex.val row : ℚ))

theorem goodVectorCoordinates_combination (frame : RationalGL3) (vertex : NormalizedGoodVector) :
    frame.val *ᵥ goodVectorCoordinates frame vertex = (fun row => (vertex.val row : ℚ)) := by
  simp only [goodVectorCoordinates, Matrix.mulVec_mulVec, frame.val_inv, Matrix.one_mulVec]

theorem goodVectorCoordinates_of_combination (frame : RationalGL3) (vertex : NormalizedGoodVector)
    (weights : Fin 3 → ℚ) (combination : frame.val *ᵥ weights = (fun row => (vertex.val row : ℚ))) :
    goodVectorCoordinates frame vertex = weights := by
  rw [goodVectorCoordinates, ← combination, Matrix.mulVec_mulVec, frame.inv_val, Matrix.one_mulVec]

theorem goodTripleHeight_coordinates (frame : RationalGL3) (a b c : NormalizedGoodVector) :
    (goodTripleHeight (a, b, c) : ℚ) =
      |(vectorTripleMatrix (goodVectorCoordinates frame a, goodVectorCoordinates frame b,
        goodVectorCoordinates frame c)).det| * |frame.val.det| := by
  have matrix_equality : (goodTripleMatrix (a, b, c)).map (Int.castRingHom ℚ) =
      frame.val * vectorTripleMatrix (goodVectorCoordinates frame a, goodVectorCoordinates frame b,
        goodVectorCoordinates frame c) := by
    ext row column
    fin_cases column
    · simpa [goodTripleMatrix, vectorTripleMatrix, Matrix.mul_apply, Matrix.mulVec, dotProduct]
        using (congrFun (goodVectorCoordinates_combination frame a) row).symm
    · simpa [goodTripleMatrix, vectorTripleMatrix, Matrix.mul_apply, Matrix.mulVec, dotProduct]
        using (congrFun (goodVectorCoordinates_combination frame b) row).symm
    · simpa [goodTripleMatrix, vectorTripleMatrix, Matrix.mul_apply, Matrix.mulVec, dotProduct]
        using (congrFun (goodVectorCoordinates_combination frame c) row).symm
  rw [goodTripleHeight_cast, matrix_equality, Matrix.det_mul, abs_mul, mul_comm]

theorem goodVectorCoordinates_basis (frame : RationalGL3) (a b c : NormalizedGoodVector)
    (entries : frame.val = (goodTripleMatrix (a, b, c)).map (Int.castRingHom ℚ)) :
    goodVectorCoordinates frame a = Pi.single 0 1 ∧
      goodVectorCoordinates frame b = Pi.single 1 1 ∧
      goodVectorCoordinates frame c = Pi.single 2 1 := by
  refine ⟨goodVectorCoordinates_of_combination frame a _ ?_,
    goodVectorCoordinates_of_combination frame b _ ?_,
    goodVectorCoordinates_of_combination frame c _ ?_⟩ <;>
    rw [Matrix.mulVec_single_one, entries] <;> rfl

def comparisonTetrahedronHeights (weights other_weights : Fin 3 → ℚ) (pivot : Fin 3) :
    Fin 4 → ℚ :=
  ![|other_weights pivot|, |weights pivot|,
    comparisonFaceHeights weights other_weights pivot (if pivot = 0 then 1 else 0),
    comparisonFaceHeights weights other_weights pivot (if pivot = 2 then 1 else 2)]

theorem goodTetrahedron_coordinate_heights (frame : RationalGL3) (a b c d : NormalizedGoodVector)
    (entries : frame.val = (goodTripleMatrix (b, c, d)).map (Int.castRingHom ℚ))
    (other_weights : Fin 3 → ℚ) (other_coordinates : goodVectorCoordinates frame a = other_weights)
    (index : Fin 4) :
    (goodTripleHeight (tetrahedronFace (a, b, c, d) index) : ℚ) =
      ![1, |other_weights 0|, |other_weights 1|, |other_weights 2|] index * |frame.val.det| := by
  obtain ⟨b_coordinates, c_coordinates, d_coordinates⟩ := goodVectorCoordinates_basis frame b c d entries
  fin_cases index <;>
    simp [tetrahedronFace, goodTripleHeight_coordinates frame,
      other_coordinates, b_coordinates, c_coordinates, d_coordinates,
      vectorTripleMatrix, Matrix.det_fin_three]

theorem goodTetrahedron_cone_coordinate_heights (frame : RationalGL3)
    (a b c d vertex : NormalizedGoodVector)
    (entries : frame.val = (goodTripleMatrix (b, c, d)).map (Int.castRingHom ℚ))
    (weights other_weights : Fin 3 → ℚ)
    (coordinates : goodVectorCoordinates frame vertex = weights)
    (other_coordinates : goodVectorCoordinates frame a = other_weights)
    (pivot : Fin 3) (index : Fin 4) :
    (goodTripleHeight (tetrahedronFace (tetrahedronCone vertex (a, b, c, d) pivot.succ) index) : ℚ) =
      comparisonTetrahedronHeights weights other_weights pivot index * |frame.val.det| := by
  obtain ⟨b_coordinates, c_coordinates, d_coordinates⟩ := goodVectorCoordinates_basis frame b c d entries
  fin_cases pivot <;> fin_cases index <;>
    simp [tetrahedronFace, tetrahedronCone, prependVertex, goodTripleHeight_coordinates frame,
      coordinates, other_coordinates, b_coordinates, c_coordinates, d_coordinates,
      comparisonTetrahedronHeights, comparisonFaceHeights, vectorTripleMatrix, Matrix.det_fin_three,
      abs_sub_comm]
  all_goals
    left
    apply abs_eq_abs.mpr
    solve | left; ring | right; ring

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
