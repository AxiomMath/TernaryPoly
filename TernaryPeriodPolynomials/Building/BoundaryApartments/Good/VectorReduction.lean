module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.RoundedGoodReduction
public import TernaryPeriodPolynomials.Building.BoundaryApartments.TetrahedronDescent
public import TernaryPeriodPolynomials.Building.BoundaryApartments.Apartment.IntegralNormalization
public import TernaryPeriodPolynomials.Building.BoundaryApartments.Apartment.DeterminantReduction

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Matrix

abbrev NormalizedGoodVector := {vector : Fin 3 → ℤ // (vector 2 : ZMod 3) = 1}

def vectorTripleMatrix {R : Type*} (triple : OrderedTriple (Fin 3 → R)) : Matrix (Fin 3) (Fin 3) R :=
  fun row => ![triple.1 row, triple.2.1 row, triple.2.2 row]

def goodTripleMatrix (triple : OrderedTriple NormalizedGoodVector) : Matrix (Fin 3) (Fin 3) ℤ :=
  vectorTripleMatrix (triple.1.val, triple.2.1.val, triple.2.2.val)

def goodTripleHeight (triple : OrderedTriple NormalizedGoodVector) : ℕ :=
  (goodTripleMatrix triple).det.natAbs

theorem goodTripleMatrix_normalized (triple : OrderedTriple NormalizedGoodVector) (column : Fin 3) :
    ((goodTripleMatrix triple) 2 column : ZMod 3) = 1 := by
  fin_cases column
  · exact triple.1.property
  · exact triple.2.1.property
  · exact triple.2.2.property

theorem integer_natAbs_cast (integer : ℤ) : (integer.natAbs : ℚ) = |(integer : ℚ)| := by
  rw [← Int.cast_abs, ← Int.natCast_natAbs]
  rfl

theorem goodTripleHeight_cast (triple : OrderedTriple NormalizedGoodVector) :
    (goodTripleHeight triple : ℚ) = |((goodTripleMatrix triple).map (Int.castRingHom ℚ)).det| := by
  rw [goodTripleHeight, integer_natAbs_cast, integer_matrix_det_cast]

theorem goodTripleMatrix_cone_det (triple : OrderedTriple NormalizedGoodVector)
    (vertex : NormalizedGoodVector) (index : Fin 3) :
    (goodTripleMatrix (tripleConeFaces vertex triple index)).det.natAbs =
      ((goodTripleMatrix triple).updateCol index vertex.val).det.natAbs := by
  rcases triple with ⟨first, second, third⟩
  fin_cases index
  · congr 2
    ext row column
    fin_cases column <;> rfl
  · have equality : (goodTripleMatrix (vertex, first, third)).det =
        -((goodTripleMatrix (first, second, third)).updateCol 1 vertex.val).det := by
      simp [goodTripleMatrix, vectorTripleMatrix, Matrix.det_fin_three]
      ring
    change (goodTripleMatrix (vertex, first, third)).det.natAbs = _
    rw [equality, Int.natAbs_neg]
    rfl
  · have equality : (goodTripleMatrix (vertex, first, second)).det =
        ((goodTripleMatrix (first, second, third)).updateCol 2 vertex.val).det := by
      simp [goodTripleMatrix, vectorTripleMatrix, Matrix.det_fin_three]
      ring
    change (goodTripleMatrix (vertex, first, second)).det.natAbs = _
    rw [equality]
    rfl

theorem normalized_good_vector_reduction (triple : OrderedTriple NormalizedGoodVector)
    (large : 1 < goodTripleHeight triple) :
    ∃ vertex : NormalizedGoodVector, ∃ weights : Fin 3 → ℚ,
      (goodTripleMatrix triple).map (Int.castRingHom ℚ) *ᵥ weights =
        (fun row => (vertex.val row : ℚ)) ∧
      (∀ index, |weights index| < 1) ∧
      (∀ first second, first ≠ second → |weights first| + |weights second| ≤ 1) := by
  let matrix := goodTripleMatrix triple
  have nonzero : matrix.det ≠ 0 := by
    intro zero
    simp only [goodTripleHeight, ← show matrix = goodTripleMatrix triple from rfl, zero,
      Int.natAbs_zero] at large
    omega
  have not_unit : ¬IsUnit matrix := by
    intro unit
    have one := Int.isUnit_iff_natAbs_eq.mp ((Matrix.isUnit_iff_isUnit_det matrix).mp unit)
    change 1 < matrix.det.natAbs at large
    omega
  have rational_nonzero : (matrix.map (Int.castRingHom ℚ)).det ≠ 0 := by
    rw [← integer_matrix_det_cast]
    exact_mod_cast nonzero
  let frame := GeneralLinearGroup.mkOfDetNeZero (matrix.map (Int.castRingHom ℚ)) rational_nonzero
  obtain ⟨vector, weights, combination, small, pairs, good⟩ :=
    small_good_integral_vector_pairwise matrix frame rfl not_unit
      (fun column => by rw [show matrix = goodTripleMatrix triple from rfl,
        goodTripleMatrix_normalized]; exact one_ne_zero)
  obtain ⟨sign, normalized⟩ := nonzero_modThree_sign (vector 2) good
  let vertex : NormalizedGoodVector := ⟨fun row => (sign : ℤ) * vector row, by
    simpa only [Int.cast_mul, mul_comm] using normalized⟩
  refine ⟨vertex, (fun index => ((sign : ℤ) : ℚ) * weights index), ?_, ?_, ?_⟩
  · change frame.val *ᵥ (((sign : ℤ) : ℚ) • weights) = _
    rw [Matrix.mulVec_smul, combination]
    ext row
    simp [vertex]
  · intro index
    rcases Int.units_eq_one_or sign with rfl | rfl <;> simpa using small index
  · intro first second different
    rcases Int.units_eq_one_or sign with rfl | rfl <;> simpa using pairs first second different

def goodTripleReducer (triple : OrderedTriple NormalizedGoodVector) : NormalizedGoodVector :=
  if large : 1 < goodTripleHeight triple then
    Classical.choose (normalized_good_vector_reduction triple large)
  else ⟨![0, 0, 1], by decide⟩

theorem goodTripleReducer_spec (triple : OrderedTriple NormalizedGoodVector)
    (large : 1 < goodTripleHeight triple) :
    ∃ weights : Fin 3 → ℚ,
      (goodTripleMatrix triple).map (Int.castRingHom ℚ) *ᵥ weights =
        (fun row => ((goodTripleReducer triple).val row : ℚ)) ∧
      (∀ index, |weights index| < 1) ∧
      (∀ first second, first ≠ second → |weights first| + |weights second| ≤ 1) := by
  rw [goodTripleReducer, dite_eq_left large]
  exact Classical.choose_spec (normalized_good_vector_reduction triple large)

theorem goodTripleReducer_decrease (triple : OrderedTriple NormalizedGoodVector)
    (large : 1 < goodTripleHeight triple) (index : Fin 3) :
    goodTripleHeight (tripleConeFaces (goodTripleReducer triple) triple index) <
      goodTripleHeight triple := by
  obtain ⟨weights, combination, small, _⟩ := goodTripleReducer_spec triple large
  have nonzero : (goodTripleMatrix triple).det ≠ 0 := by
    intro zero
    simp [goodTripleHeight, zero] at large
  have rational_nonzero : ((goodTripleMatrix triple).map (Int.castRingHom ℚ)).det ≠ 0 := by
    rw [← integer_matrix_det_cast]
    exact_mod_cast nonzero
  let frame := GeneralLinearGroup.mkOfDetNeZero
    ((goodTripleMatrix triple).map (Int.castRingHom ℚ)) rational_nonzero
  unfold goodTripleHeight
  rw [goodTripleMatrix_cone_det]
  exact integer_updateCol_det_decreases (goodTripleMatrix triple) frame rfl nonzero
    (goodTripleReducer triple).val weights combination small index

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
