module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.FiniteWeightValues
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Finite.Triangular

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem binaryRelativeLowering_lift_boundary (cusp : CuspidalRepresentation) (degree : ℕ)
    (level : Subgroup BinaryFiniteGL) (boundary : cuspAffineSmoothValues cusp)
    (boundary_mem : boundary ∈ cuspFiniteWeightValues cusp level (degree + 1 : ℕ)) :
    ∃ primitive : binarySmoothValues cusp (Fin (degree + 2)),
      primitive (Fin.last (degree + 1)) = boundary ∧
      (∀ position, primitive position ∈ cuspFiniteWeightValues cusp level (binaryUnitaryWeight degree 0 position)) ∧
      ∀ position : Fin (degree + 1),
        binaryRelativeLowering cusp (binaryWeightBasis (degree + 1)) 0 primitive position.succ = 0 := by
  have adjacent (position : Fin (degree + 1)) :
      binaryUnitaryWeight degree 0 position.succ - 2 = binaryUnitaryWeight degree 0 position.castSucc := by
    simp only [binaryUnitaryWeight, Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
    omega
  have last_weight : binaryUnitaryWeight degree 0 (Fin.last (degree + 1)) = (degree + 1 : ℕ) := by
    simp only [binaryUnitaryWeight, Fin.val_last]
    omega
  obtain ⟨primitive, last_value, primitive_mem, equations⟩ := finiteTriangular_solve_boundary
    (M := cuspAffineSmoothValues cusp) (degree + 1)
    (fun position => cuspFiniteWeightValues cusp level (binaryUnitaryWeight degree 0 position))
    (fun position => Complex.I * ((degree + 1 - position.val : ℕ) : ℂ))
    (fun position => cuspLoweringOperator cusp (binaryUnitaryWeight degree 0 position.succ))
    (fun _ => 0) boundary (by rw [last_weight]; exact boundary_mem)
    (by
      intro position
      apply mul_ne_zero Complex.I_ne_zero
      have positive : 0 < degree + 1 - position.val := by omega
      exact_mod_cast (ne_of_gt positive))
    (by
      intro position value member
      rw [← adjacent position]
      exact cuspFiniteWeightValues_lowering cusp level _ value member)
    (fun position => Submodule.zero_mem _)
  refine ⟨primitive, last_value, primitive_mem, ?_⟩
  intro position
  rw [binaryRelativeLowering_succ, equations position]

theorem binaryRelativeLowering_eliminate (cusp : CuspidalRepresentation) (degree : ℕ)
    (level : Subgroup BinaryFiniteGL) (lower : binarySmoothValues cusp (Fin (degree + 2)))
    (lower_mem : ∀ position, lower position ∈ cuspFiniteWeightValues cusp level (binaryUnitaryWeight degree (-2) position)) :
    ∃ primitive : binarySmoothValues cusp (Fin (degree + 2)),
      primitive (Fin.last (degree + 1)) = 0 ∧
      (∀ position, primitive position ∈ cuspFiniteWeightValues cusp level (binaryUnitaryWeight degree 0 position)) ∧
      ∀ position : Fin (degree + 1),
        (lower - binaryRelativeLowering cusp (binaryWeightBasis (degree + 1)) 0 primitive) position.succ = 0 := by
  have adjacent (position : Fin (degree + 1)) :
      binaryUnitaryWeight degree 0 position.succ - 2 = binaryUnitaryWeight degree 0 position.castSucc := by
    simp only [binaryUnitaryWeight, Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
    omega
  have target_weight (position : Fin (degree + 1)) :
      binaryUnitaryWeight degree (-2) position.succ = binaryUnitaryWeight degree 0 position.castSucc := by
    simp only [binaryUnitaryWeight, Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
    omega
  obtain ⟨primitive, last_zero, primitive_mem, equations⟩ := finiteTriangular_solve
    (M := cuspAffineSmoothValues cusp) (degree + 1)
    (fun position => cuspFiniteWeightValues cusp level (binaryUnitaryWeight degree 0 position))
    (fun position => Complex.I * ((degree + 1 - position.val : ℕ) : ℂ))
    (fun position => cuspLoweringOperator cusp (binaryUnitaryWeight degree 0 position.succ)) lower
    (by
      intro position
      apply mul_ne_zero Complex.I_ne_zero
      have positive : 0 < degree + 1 - position.val := by omega
      exact_mod_cast (ne_of_gt positive))
    (by
      intro position value member
      rw [← adjacent position]
      exact cuspFiniteWeightValues_lowering cusp level _ value member)
    (by
      intro position
      rw [← target_weight position]
      exact lower_mem position.succ)
  refine ⟨primitive, last_zero, primitive_mem, ?_⟩
  intro position
  change lower position.succ - binaryRelativeLowering cusp (binaryWeightBasis (degree + 1)) 0 primitive position.succ = 0
  rw [binaryRelativeLowering_succ, equations position, sub_self]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
