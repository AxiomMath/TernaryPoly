module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.Good.VectorReduction
public import TernaryPeriodPolynomials.Building.BoundaryApartments.UnimodularTetrahedra

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Matrix

def goodTripleInitial (triple : OrderedTriple NormalizedGoodVector) : ApartmentQuotient :=
  normalizedMatrixClass 1 (referenceFrame.inv * goodTripleMatrix triple)

theorem goodTripleMatrix_swap (first second third : NormalizedGoodVector) :
    goodTripleMatrix (second, first, third) =
      goodTripleMatrix (first, second, third) * integralSwapGenerator.val := by
  ext row column
  fin_cases column <;>
    simp [goodTripleMatrix, vectorTripleMatrix, integralSwapGenerator, Matrix.mul_apply,
      Fin.sum_univ_three]

theorem goodTripleMatrix_cyclic (first second third : NormalizedGoodVector) :
    goodTripleMatrix (second, third, first) =
      goodTripleMatrix (first, second, third) * integralCyclicGenerator.val := by
  ext row column
  fin_cases column <;>
    simp [goodTripleMatrix, vectorTripleMatrix, integralCyclicGenerator, Matrix.mul_apply,
      Fin.sum_univ_three]

theorem goodTripleInitial_swap (first second third : NormalizedGoodVector) :
    goodTripleInitial (second, first, third) = -goodTripleInitial (first, second, third) := by
  simp only [goodTripleInitial, goodTripleMatrix_swap first second third, ← Matrix.mul_assoc,
    normalizedMatrixClass_right_swap]

theorem goodTripleInitial_cyclic (first second third : NormalizedGoodVector) :
    goodTripleInitial (second, third, first) = goodTripleInitial (first, second, third) := by
  simp only [goodTripleInitial, goodTripleMatrix_cyclic first second third, ← Matrix.mul_assoc,
    normalizedMatrixClass_right_cyclic]

theorem goodTripleHeight_swap (first second third : NormalizedGoodVector) :
    goodTripleHeight (second, first, third) = goodTripleHeight (first, second, third) := by
  have equality : (goodTripleMatrix (second, first, third)).det =
      -(goodTripleMatrix (first, second, third)).det := by
    simp [goodTripleMatrix, vectorTripleMatrix, Matrix.det_fin_three]
    ring
  simp only [goodTripleHeight, equality, Int.natAbs_neg]

theorem goodTripleHeight_cyclic (first second third : NormalizedGoodVector) :
    goodTripleHeight (second, third, first) = goodTripleHeight (first, second, third) := by
  have equality : (goodTripleMatrix (second, third, first)).det =
      (goodTripleMatrix (first, second, third)).det := by
    simp [goodTripleMatrix, vectorTripleMatrix, Matrix.det_fin_three]
    ring
  simp only [goodTripleHeight, equality]

theorem goodTripleInitial_zero (triple : OrderedTriple NormalizedGoodVector)
    (zero : goodTripleHeight triple = 0) : goodTripleInitial triple = 0 := by
  apply normalizedMatrixClass_singular
  rw [Matrix.det_mul, show (goodTripleMatrix triple).det = 0 from Int.natAbs_eq_zero.mp zero, mul_zero]

theorem reference_inverse_sum (vector : Fin 3 → ℤ) :
    ∑ row, (referenceFrame.inv *ᵥ vector) row = vector 2 := by
  simp [referenceFrame, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

def goodTripleChange (triple : OrderedTriple NormalizedGoodVector)
    (unit : goodTripleHeight triple = 1) : normalizedFrameChanges := by
  have matrix_unit : IsUnit (goodTripleMatrix triple) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (Int.isUnit_iff_natAbs_eq.mpr unit)
  let frame : IntegralGL3 := matrix_unit.unit
  refine ⟨referenceFrame⁻¹ * frame, ?_⟩
  ext column
  change (∑ row, 1 * (((referenceFrame.inv * frame.val) row column : ℤ) : ZMod 3)) = 1
  simp only [one_mul, ← Int.cast_sum]
  have entry : (∑ row, (referenceFrame.inv * frame.val) row column) = frame.val 2 column :=
    reference_inverse_sum (frame.val.col column)
  rw [entry]
  change ((matrix_unit.unit.val 2 column : ℤ) : ZMod 3) = 1
  rw [matrix_unit.unit_spec]
  exact goodTripleMatrix_normalized triple column

theorem goodTripleChange_val (triple : OrderedTriple NormalizedGoodVector)
    (unit : goodTripleHeight triple = 1) :
    (goodTripleChange triple unit).val.val = referenceFrame.inv * goodTripleMatrix triple := by
  change referenceFrame.inv * _ = _
  rw [IsUnit.unit_spec]

theorem goodTripleInitial_subdivision (triple : OrderedTriple NormalizedGoodVector)
    (vertex : NormalizedGoodVector) (unit : goodTripleHeight triple = 1)
    (small : ∀ index, goodTripleHeight (tripleConeFaces vertex triple index) ≤ 1) :
    goodTripleInitial triple =
      goodTripleInitial (tripleConeFaces vertex triple 0) -
      goodTripleInitial (tripleConeFaces vertex triple 1) +
      goodTripleInitial (tripleConeFaces vertex triple 2) := by
  let frame := goodTripleChange triple unit
  let vector := referenceFrame.inv *ᵥ vertex.val
  have face_bounds (column : Fin 3) : |(frame.val.val.updateCol column vector).det| ≤ 1 := by
    have inverse_det : |referenceFrame.inv.det| = 1 := integralFrame_abs_det referenceFrame⁻¹
    rw [goodTripleChange_val, ← Matrix.mul_updateCol, Matrix.det_mul, abs_mul,
      inverse_det, one_mul]
    have bound := small column
    unfold goodTripleHeight at bound
    rw [goodTripleMatrix_cone_det] at bound
    have cast_bound : (((goodTripleMatrix triple).updateCol column vertex.val).det.natAbs : ℤ) ≤ 1 :=
      by exact_mod_cast bound
    simpa only [Int.natCast_natAbs] using cast_bound
  have subdivision := normalizedMatrixClass_unimodular_subdivision 1 frame vector
    (by rw [reference_inverse_sum]; exact vertex.property) face_bounds
  rw [goodTripleChange_val] at subdivision
  dsimp only [vector] at subdivision
  simp only [← Matrix.mul_updateCol] at subdivision
  rcases triple with ⟨first, second, third⟩
  have update_zero : (goodTripleMatrix (first, second, third)).updateCol 0 vertex.val =
      goodTripleMatrix (vertex, second, third) := by
    ext row column
    fin_cases column <;> rfl
  have update_one : (goodTripleMatrix (first, second, third)).updateCol 1 vertex.val =
      goodTripleMatrix (first, vertex, third) := by
    ext row column
    fin_cases column <;> rfl
  have update_two : (goodTripleMatrix (first, second, third)).updateCol 2 vertex.val =
      goodTripleMatrix (first, second, vertex) := by
    ext row column
    fin_cases column <;> rfl
  rw [update_zero, update_one, update_two] at subdivision
  change goodTripleInitial (first, second, third) =
    goodTripleInitial (vertex, second, third) + goodTripleInitial (first, vertex, third) +
      goodTripleInitial (first, second, vertex) at subdivision
  change goodTripleInitial (first, second, third) =
    goodTripleInitial (vertex, second, third) - goodTripleInitial (vertex, first, third) +
      goodTripleInitial (vertex, first, second)
  rw [goodTripleInitial_swap first vertex third, sub_neg_eq_add,
    goodTripleInitial_cyclic second vertex first, goodTripleInitial_cyclic first second vertex]
  exact subdivision

theorem goodTripleInitial_relation (tetrahedron : OrderedTetrahedron NormalizedGoodVector)
    (small : TetrahedronBound goodTripleHeight 1 tetrahedron) :
    tetrahedronValue goodTripleInitial tetrahedron = 0 := by
  by_cases unit_face : ∃ index, goodTripleHeight (tetrahedronFace tetrahedron index) = 1
  · obtain ⟨index, unit⟩ := unit_face
    rcases tetrahedron with ⟨a, b, c, d⟩
    have small_zero := small 0
    have small_one := small 1
    have small_two := small 2
    have small_three := small 3
    change goodTripleHeight (b, c, d) ≤ 1 at small_zero
    change goodTripleHeight (a, c, d) ≤ 1 at small_one
    change goodTripleHeight (a, b, d) ≤ 1 at small_two
    change goodTripleHeight (a, b, c) ≤ 1 at small_three
    change goodTripleInitial (b, c, d) - goodTripleInitial (a, c, d) +
      goodTripleInitial (a, b, d) - goodTripleInitial (a, b, c) = 0
    fin_cases index
    · have relation := goodTripleInitial_subdivision (b, c, d) a unit (by
        intro index
        fin_cases index
        · exact small_one
        · exact small_two
        · exact small_three)
      change goodTripleInitial (b, c, d) = goodTripleInitial (a, c, d) -
        goodTripleInitial (a, b, d) + goodTripleInitial (a, b, c) at relation
      rw [relation]
      abel
    · have relation := goodTripleInitial_subdivision (a, c, d) b unit (by
        intro index
        fin_cases index
        · exact small_zero
        · change goodTripleHeight (b, a, d) ≤ 1
          rw [goodTripleHeight_swap a b d]
          exact small_two
        · change goodTripleHeight (b, a, c) ≤ 1
          rw [goodTripleHeight_swap a b c]
          exact small_three)
      change goodTripleInitial (a, c, d) = goodTripleInitial (b, c, d) -
        goodTripleInitial (b, a, d) + goodTripleInitial (b, a, c) at relation
      rw [goodTripleInitial_swap a b d, goodTripleInitial_swap a b c] at relation
      rw [relation]
      abel
    · have relation := goodTripleInitial_subdivision (a, b, d) c unit (by
        intro index
        fin_cases index
        · change goodTripleHeight (c, b, d) ≤ 1
          rw [goodTripleHeight_swap b c d]
          exact small_zero
        · change goodTripleHeight (c, a, d) ≤ 1
          rw [goodTripleHeight_swap a c d]
          exact small_one
        · change goodTripleHeight (c, a, b) ≤ 1
          rw [goodTripleHeight_cyclic b c a, goodTripleHeight_cyclic a b c]
          exact small_three)
      change goodTripleInitial (a, b, d) = goodTripleInitial (c, b, d) -
        goodTripleInitial (c, a, d) + goodTripleInitial (c, a, b) at relation
      rw [goodTripleInitial_swap b c d, goodTripleInitial_swap a c d,
        goodTripleInitial_cyclic b c a, goodTripleInitial_cyclic a b c] at relation
      rw [relation]
      abel
    · have relation := goodTripleInitial_subdivision (a, b, c) d unit (by
        intro index
        fin_cases index
        · change goodTripleHeight (d, b, c) ≤ 1
          rw [goodTripleHeight_cyclic c d b, goodTripleHeight_cyclic b c d]
          exact small_zero
        · change goodTripleHeight (d, a, c) ≤ 1
          rw [goodTripleHeight_cyclic c d a, goodTripleHeight_cyclic a c d]
          exact small_one
        · change goodTripleHeight (d, a, b) ≤ 1
          rw [goodTripleHeight_cyclic b d a, goodTripleHeight_cyclic a b d]
          exact small_two)
      change goodTripleInitial (a, b, c) = goodTripleInitial (d, b, c) -
        goodTripleInitial (d, a, c) + goodTripleInitial (d, a, b) at relation
      rw [goodTripleInitial_cyclic c d b, goodTripleInitial_cyclic b c d,
        goodTripleInitial_cyclic c d a, goodTripleInitial_cyclic a c d,
        goodTripleInitial_cyclic b d a, goodTripleInitial_cyclic a b d] at relation
      rw [relation]
      abel
  · have zero (index : Fin 4) : goodTripleInitial (tetrahedronFace tetrahedron index) = 0 := by
      apply goodTripleInitial_zero
      have upper := small index
      have different : goodTripleHeight (tetrahedronFace tetrahedron index) ≠ 1 :=
        fun equality => unit_face ⟨index, equality⟩
      omega
    simp only [tetrahedronValue, zero, sub_zero, add_zero]

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
