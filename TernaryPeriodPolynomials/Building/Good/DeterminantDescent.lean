module

public import TernaryPeriodPolynomials.Building.NonunimodularFractionalPoint
public import TernaryPeriodPolynomials.Building.Good.LatticeReduction
public import TernaryPeriodPolynomials.Building.Good.IntegralNormalization
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section


/-! A good integral replacement vector strictly lowers every column determinant.
The replacement is normalized modulo three by its sign; no primitivity or
nonzero replacement determinant is assumed. -/

open scoped BigOperators
noncomputable section
namespace TernaryPoly.GoodDeterminantDescent

open ModThreeGoodAction GoodLatticeReduction Matrix

abbrev IntegralMatrix := Matrix (Fin 3) (Fin 3) ℤ

/-- A nonunimodular normalized integral frame has a residue-one lattice point
whose rational coefficients all have absolute value less than one. -/
theorem normalized_reduction_coefficients (M : IntegralMatrix)
    (hM : NormalizedColumns M) (hdet : M.det ≠ 0) (hlarge : 1 < M.det.natAbs) :
    ∃ (w : IntegralVector) (a : Fin 3 → ℚ),
      rationalVector w = (M.map (Int.castRingHom ℚ)).mulVec a ∧
      (∑ i, (w i : ZMod 3)) = 1 ∧ ∀ i, |a i| < 1 := by
  obtain ⟨w, a, hw, ha, hpos⟩ :=
    NonunimodularFractionalPoint.fractional_lattice_point M hdet hlarge
  obtain ⟨w, a, hw, hs, ha⟩ := good_reduction_coefficients M hM w a ha hpos hw
  rcases GoodIntegralNormalization.residue_one_or_neg_one _ hs with hs | hs
  · exact ⟨w, a, hw, hs, ha⟩
  · refine ⟨-w, -a, ?_, ?_, ?_⟩
    · rw [GoodIntegralNormalization.rationalVector_neg, hw, Matrix.mulVec_neg]
    · rwa [GoodIntegralNormalization.residue_neg]
    · intro i
      simpa only [Pi.neg_apply, abs_neg] using ha i

/-- The determinant of a column replacement is its corresponding coefficient
in the original frame times the original determinant. -/
theorem det_updateCol_mulVec (A : Matrix (Fin 3) (Fin 3) ℚ)
    (a : Fin 3 → ℚ) (j : Fin 3) :
    (A.updateCol j (A.mulVec a)).det = a j * A.det := by
  have h : A.mulVec a = fun k => ∑ i, a i • A k i := by
    ext k
    simp only [Matrix.mulVec, dotProduct, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  rw [h, Matrix.det_updateCol_sum, smul_eq_mul]

/-- The exact rational determinant identity for an integral replacement vector. -/
theorem det_updateCol_cast (M : IntegralMatrix) (w : IntegralVector)
    (a : Fin 3 → ℚ)
    (hw : rationalVector w = (M.map (Int.castRingHom ℚ)).mulVec a) (j : Fin 3) :
    ((M.updateCol j w).det : ℚ) = a j * (M.det : ℚ) := by
  have hcast : ((M.updateCol j w).det : ℚ) =
      ((M.map (Int.castRingHom ℚ)).updateCol j (rationalVector w)).det := by
    calc
      _ = ((M.updateCol j w).map (Int.castRingHom ℚ)).det :=
        (Int.castRingHom ℚ).map_det _
      _ = _ := by rw [Matrix.map_updateCol]; rfl
  rw [hcast, hw, det_updateCol_mulVec]
  exact congrArg (fun q : ℚ => a j * q) ((Int.castRingHom ℚ).map_det M).symm

/-- Strict determinant descent, including replacements whose determinant is zero. -/
theorem det_updateCol_natAbs_lt (M : IntegralMatrix) (hdet : M.det ≠ 0)
    (w : IntegralVector) (a : Fin 3 → ℚ)
    (hw : rationalVector w = (M.map (Int.castRingHom ℚ)).mulVec a)
    (ha : ∀ i, |a i| < 1) (j : Fin 3) :
    (M.updateCol j w).det.natAbs < M.det.natAbs := by
  have hd : 0 < |(M.det : ℚ)| := abs_pos.mpr (by exact_mod_cast hdet)
  have hlt : |((M.updateCol j w).det : ℚ)| < |(M.det : ℚ)| := by
    rw [det_updateCol_cast M w a hw j, abs_mul]
    exact (mul_lt_mul_of_pos_right (ha j) hd).trans_eq (one_mul _)
  have hn : ((M.updateCol j w).det.natAbs : ℚ) < (M.det.natAbs : ℚ) := by
    simpa only [Nat.cast_natAbs, Int.cast_abs] using hlt
  exact_mod_cast hn

/-- A residue-one replacement preserves the normalization of every column. -/
theorem normalizedColumns_updateCol (M : IntegralMatrix) (hM : NormalizedColumns M)
    (w : IntegralVector) (hw : ∑ i, (w i : ZMod 3) = 1) (j : Fin 3) :
    NormalizedColumns (M.updateCol j w) := by
  intro k
  by_cases hk : k = j
  · subst k
    simpa only [Matrix.updateCol_self] using hw
  · simpa only [Matrix.updateCol_ne hk] using hM k

/-- One normalized good integral vector strictly reduces all three absolute
column determinants, and every replacement frame remains normalized. -/
theorem exists_normalized_determinant_descent (M : IntegralMatrix)
    (hM : NormalizedColumns M) (hdet : M.det ≠ 0) (hlarge : 1 < M.det.natAbs) :
    ∃ w : IntegralVector, (∑ i, (w i : ZMod 3)) = 1 ∧
      ∀ j : Fin 3, (M.updateCol j w).det.natAbs < M.det.natAbs ∧
        NormalizedColumns (M.updateCol j w) := by
  obtain ⟨w, a, hw, hs, ha⟩ := normalized_reduction_coefficients M hM hdet hlarge
  refine ⟨w, hs, fun j => ?_⟩
  exact ⟨det_updateCol_natAbs_lt M hdet w a hw ha j,
    normalizedColumns_updateCol M hM w hs j⟩

end TernaryPoly.GoodDeterminantDescent
