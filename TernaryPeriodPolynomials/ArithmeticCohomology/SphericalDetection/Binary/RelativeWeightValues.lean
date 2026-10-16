module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.FiniteWeightValues

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem binaryRelativeLowering_mem (cusp : CuspidalRepresentation) (degree : ℕ)
    (level : Subgroup BinaryFiniteGL) (weight : ℤ)
    (vector : binarySmoothValues cusp (Fin (degree + 2)))
    (member : ∀ position, vector position ∈ cuspFiniteWeightValues cusp level (binaryUnitaryWeight degree weight position)) :
    ∀ position, binaryRelativeLowering cusp (binaryWeightBasis (degree + 1)) weight vector position ∈
      cuspFiniteWeightValues cusp level (binaryUnitaryWeight degree (weight - 2) position) := by
  intro position
  refine Fin.cases ?_ (fun position => ?_) position
  · rw [binaryRelativeLowering_zero]
    have identity : binaryUnitaryWeight degree (weight - 2) 0 = binaryUnitaryWeight degree weight 0 - 2 := by
      unfold binaryUnitaryWeight
      omega
    rw [identity]
    simpa only [binaryUnitaryWeight, Fin.val_zero, Nat.cast_zero, mul_zero, add_zero] using
      cuspFiniteWeightValues_lowering cusp level _ _ (member 0)
  · rw [binaryRelativeLowering_succ]
    apply Submodule.add_mem
    · have identity : binaryUnitaryWeight degree (weight - 2) position.succ = binaryUnitaryWeight degree weight position.castSucc := by
        simp only [binaryUnitaryWeight, Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
        omega
      rw [identity]
      exact Submodule.smul_mem _ _ (member position.castSucc)
    · have identity : binaryUnitaryWeight degree (weight - 2) position.succ = binaryUnitaryWeight degree weight position.succ - 2 := by
        unfold binaryUnitaryWeight
        omega
      rw [identity]
      exact cuspFiniteWeightValues_lowering cusp level _ _ (member position.succ)

theorem binaryRelativeRaising_mem (cusp : CuspidalRepresentation) (degree : ℕ)
    (level : Subgroup BinaryFiniteGL) (weight : ℤ)
    (vector : binarySmoothValues cusp (Fin (degree + 2)))
    (member : ∀ position, vector position ∈ cuspFiniteWeightValues cusp level (binaryUnitaryWeight degree weight position)) :
    ∀ position, binaryRelativeRaising cusp (binaryWeightBasis (degree + 1)) weight vector position ∈
      cuspFiniteWeightValues cusp level (binaryUnitaryWeight degree (weight + 2) position) := by
  intro position
  refine Fin.lastCases ?_ (fun position => ?_) position
  · rw [binaryRelativeRaising_last]
    have identity : binaryUnitaryWeight degree (weight + 2) (Fin.last (degree + 1)) =
        binaryUnitaryWeight degree weight (Fin.last (degree + 1)) + 2 := by
      unfold binaryUnitaryWeight
      omega
    have last_weight : weight + (degree + 1 : ℕ) = binaryUnitaryWeight degree weight (Fin.last (degree + 1)) := by
      simp only [binaryUnitaryWeight, Fin.val_last]
      omega
    rw [identity, last_weight]
    exact cuspFiniteWeightValues_raising cusp level _ _ (member (Fin.last (degree + 1)))
  · rw [binaryRelativeRaising_castSucc]
    apply Submodule.add_mem
    · have identity : binaryUnitaryWeight degree (weight + 2) position.castSucc = binaryUnitaryWeight degree weight position.succ := by
        simp only [binaryUnitaryWeight, Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
        omega
      rw [identity]
      exact Submodule.smul_mem _ _ (member position.succ)
    · have identity : binaryUnitaryWeight degree (weight + 2) position.castSucc = binaryUnitaryWeight degree weight position.castSucc + 2 := by
        unfold binaryUnitaryWeight
        omega
      rw [identity]
      exact cuspFiniteWeightValues_raising cusp level _ _ (member position.castSucc)

theorem binaryFiniteWeightValues_rotation (cusp : CuspidalRepresentation) (degree : ℕ)
    (level : Subgroup BinaryFiniteGL) (weight : ℤ)
    (vector : binarySmoothValues cusp (Fin (degree + 2)))
    (member : ∀ position, vector position ∈ cuspFiniteWeightValues cusp level (binaryUnitaryWeight degree weight position))
    (angle : Circle) :
    binaryHilbertOperator cusp (binaryWeightBasis (degree + 1)) (binaryRotations angle)
        (binarySmoothValues_val cusp vector) = (angle : ℂ) ^ weight • binarySmoothValues_val cusp vector :=
  binaryWeightBasis_eigenvector_of_coordinates cusp degree weight _ (fun position => (member position).2) angle

end TernaryPeriodPolynomials.SphericalDetection.Helpers
