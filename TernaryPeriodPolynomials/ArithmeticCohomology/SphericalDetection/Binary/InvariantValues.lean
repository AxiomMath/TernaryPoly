module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.BoundedPolynomial
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.Representation

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem binaryValues_evaluation_bound {degree : ℕ} (cusp : CuspidalRepresentation)
    (values : BinaryAdelicGL → Binary.HomogeneousPoly (degree + 1))
    (cuspidal : BinaryValues cusp degree values) (coordinates : Fin 2 → ℂ) :
    ∃ bound : ℝ, ∀ argument, ‖eval coordinates (values argument).val‖ ≤ bound := by
  let functional : Binary.HomogeneousPoly (degree + 1) →ₗ[ℂ] ℂ :=
    (MvPolynomial.aeval coordinates).toLinearMap.comp (Binary.HomogeneousPoly (degree + 1)).subtype
  obtain ⟨vector, realizes⟩ := binaryValues_functional cusp values cuspidal functional
  obtain ⟨bound, bounded⟩ := cusp.bounded vector
  refine ⟨bound, ?_⟩
  intro argument
  change ‖functional (values argument)‖ ≤ bound
  exact (congrArg norm (congrFun realizes argument)).symm.trans_le (bounded argument)

theorem binary_eval_substitute (polynomial : Binary.Poly)
    (matrix : Matrix (Fin 2) (Fin 2) ℂ) (coordinates : Fin 2 → ℂ) :
    eval coordinates (Binary.substitute matrix polynomial) =
      eval (fun row => ∑ column, matrix row column * coordinates column) polynomial := by
  change eval coordinates (MvPolynomial.bind₁ (Binary.linearForm matrix) polynomial) = _
  rw [← aeval_eq_bind₁, aeval_eq_eval₂Hom, map_eval₂Hom]
  have constants : (eval coordinates).comp C = RingHom.id ℂ := eval₂Hom_comp_C _ _
  simp only [MvPolynomial.algebraMap_eq, constants, Binary.linearForm, map_sum, map_mul,
    eval_C, eval_X]
  rfl

theorem binaryValues_translate_of_fixed_det_one {degree : ℕ}
    (values : BinaryAdelicGL → Binary.HomogeneousPoly (degree + 1))
    (fixed : ∀ matrix argument, binaryCohomologicalAction degree matrix values argument = values argument)
    (matrix : BinaryRealGL) (determinant : matrix.val.det = 1) (argument : BinaryAdelicGL) :
    (values (argument * atInfinity matrix)).val =
      Binary.substitute (matrix.val.map Complex.ofReal) (values argument).val := by
  have equality := congrArg Subtype.val (fixed matrix⁻¹ (argument * atInfinity matrix))
  simp only [binaryCohomologicalAction, atInfinity_inv, mul_inv_cancel_right,
    Submodule.coe_smul, binaryCoefficient, Binary.homogeneousAction_coe,
    Binary.action_apply] at equality
  have normalization : normPower (GeneralLinearGroup.det (atInfinity matrix⁻¹))
      (((degree : ℂ) + 3) / 2) = 1 := by
    rw [binary_normalizingFactor_eq, GeneralLinearGroup.coe_inv, Matrix.det_nonsing_inv,
      Ring.inverse_eq_inv, determinant]
    simp
  simp only [atInfinity_inv, map_inv] at normalization
  have determinant_complex :
      (GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap ℝ ℂ) matrix)).val = 1 := by
    rw [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.val_map_apply]
    exact (Complex.ofRealHom.map_det matrix.val).symm.trans (by simp [determinant])
  simp only [normalization, one_smul, Binary.determinantCharacter,
    MonoidHom.coe_mk, OneHom.coe_mk, map_inv,
    determinant_complex, inv_one, one_zpow, inv_inv, GeneralLinearGroup.val_map_apply,
    Complex.coe_algebraMap] at equality
  exact equality.symm

def binaryLowerUnipotent (value : ℝ) : BinaryRealGL where
  val := !![1, 0; value, 1]
  inv := !![1, 0; -value, 1]
  val_inv := by
    ext row column
    fin_cases row <;> fin_cases column <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext row column
    fin_cases row <;> fin_cases column <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem binaryValues_invariant_eq_zero {degree : ℕ} (cusp : CuspidalRepresentation)
    (values : BinaryAdelicGL → Binary.HomogeneousPoly (degree + 1))
    (cuspidal : BinaryValues cusp degree values)
    (fixed : ∀ matrix argument, binaryCohomologicalAction degree matrix values argument = values argument) :
    values = 0 := by
  obtain ⟨first_bound, first_bounded⟩ := binaryValues_evaluation_bound cusp values cuspidal ![0, 1]
  obtain ⟨second_bound, second_bounded⟩ := binaryValues_evaluation_bound cusp values cuspidal ![1, 0]
  funext argument
  apply Subtype.ext
  apply homogeneous_binary_eq_zero_of_affine_bounds (Nat.succ_pos degree)
    (values argument).val (values argument).property first_bound second_bound
  · intro number
    have bound := first_bounded (argument * atInfinity (binaryUnipotent (number : ℝ)))
    rw [binaryValues_translate_of_fixed_det_one values fixed (binaryUnipotent (number : ℝ))
      (by simp [binaryUnipotent, Matrix.det_fin_two]), binary_eval_substitute] at bound
    have coordinates : (fun row => ∑ column,
        ((binaryUnipotent (number : ℝ)).val.map Complex.ofReal) row column * (![0, 1] column)) =
          ![(number : ℂ), 1] := by
      funext row
      fin_cases row <;> simp [binaryUnipotent, Fin.sum_univ_two]
    rw [coordinates] at bound
    exact bound
  · intro number
    have bound := second_bounded (argument * atInfinity (binaryLowerUnipotent (number : ℝ)))
    rw [binaryValues_translate_of_fixed_det_one values fixed (binaryLowerUnipotent (number : ℝ))
      (by simp [binaryLowerUnipotent, Matrix.det_fin_two]), binary_eval_substitute] at bound
    have coordinates : (fun row => ∑ column,
        ((binaryLowerUnipotent (number : ℝ)).val.map Complex.ofReal) row column * (![1, 0] column)) =
          ![1, (number : ℂ)] := by
      funext row
      fin_cases row <;> simp [binaryLowerUnipotent, Fin.sum_univ_two]
    rw [coordinates] at bound
    exact bound

end TernaryPeriodPolynomials.SphericalDetection.Helpers
