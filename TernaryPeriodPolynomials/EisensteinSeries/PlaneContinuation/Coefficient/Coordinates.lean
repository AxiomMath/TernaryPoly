module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Coefficient.Tensor

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspPolynomialLift TernaryPeriodPolynomials.PlaneEisensteinContinuation.CoefficientTensor

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.CoefficientCoordinates

noncomputable def lift (data : CuspidalRepresentation) (degree : ℕ)
    (linear : Module.End ℂ (Binary.HomogeneousPoly (degree + 1))) : Module.End ℂ (Vectors data degree) where
  toFun vectors index := ∑ other : Index (degree + 1),
    (linear (basisMonomial other)).val.coeff index.val • vectors other
  map_add' first second := by
    funext index
    simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib]
  map_smul' scalar vectors := by
    funext index
    simp only [Pi.smul_apply, Finset.smul_sum, RingHom.id_apply]
    exact Finset.sum_congr rfl (fun _ _ => smul_comm _ _ _)

theorem coefficients_apply (degree : ℕ) (linear : Module.End ℂ (Binary.HomogeneousPoly (degree + 1)))
    (polynomial : Binary.HomogeneousPoly (degree + 1)) (index : Index (degree + 1)) :
    ∑ other : Index (degree + 1), (linear (basisMonomial other)).val.coeff index.val *
        polynomial.val.coeff other.val = (linear polynomial).val.coeff index.val := by
  have equality := congrArg (fun value : Binary.HomogeneousPoly (degree + 1) =>
    (linear value).val.coeff index.val) (polynomial_reconstruct (degree + 1) polynomial)
  change (linear
    (∑ other : Index (degree + 1), polynomial.val.coeff other.val • basisMonomial other)).val.coeff index.val = _ at equality
  simpa only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul,
    MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, smul_eq_mul, mul_comm] using equality

theorem lift_tensor (data : CuspidalRepresentation) (degree : ℕ)
    (linear : Module.End ℂ (Binary.HomogeneousPoly (degree + 1)))
    (polynomial : Binary.HomogeneousPoly (degree + 1)) (vector : data.smooth) :
    lift data degree linear (tensor data degree polynomial.val vector) = tensor data degree (linear polynomial).val vector := by
  funext index
  change (∑ other : Index (degree + 1), (linear (basisMonomial other)).val.coeff index.val •
    (polynomial.val.coeff other.val • vector)) = _
  rw [show (∑ other : Index (degree + 1), (linear (basisMonomial other)).val.coeff index.val •
      (polynomial.val.coeff other.val • vector)) =
      (∑ other : Index (degree + 1), (linear (basisMonomial other)).val.coeff index.val *
        polynomial.val.coeff other.val) • vector by simp only [Finset.sum_smul, mul_smul]]
  rw [coefficients_apply]
  rfl

theorem tensor_basis_reconstruct (data : CuspidalRepresentation) (degree : ℕ) (vectors : Vectors data degree) :
    ∑ index : Index (degree + 1), tensor data degree (basisMonomial index).val (vectors index) = vectors := by
  classical
  funext index
  simp only [Finset.sum_apply, tensor, basisMonomial, MvPolynomial.coeff_monomial,
    Subtype.val_inj, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem tensor_ext (data : CuspidalRepresentation) (degree : ℕ)
    (first second : Module.End ℂ (Vectors data degree))
    (agreement : ∀ polynomial : Binary.HomogeneousPoly (degree + 1), ∀ vector : data.smooth,
      first (tensor data degree polynomial.val vector) = second (tensor data degree polynomial.val vector)) : first = second := by
  apply LinearMap.ext
  intro vectors
  rw [← tensor_basis_reconstruct data degree vectors]
  simp only [map_sum]
  exact Finset.sum_congr rfl (fun index _ => agreement (basisMonomial index) (vectors index))

theorem lift_one (data : CuspidalRepresentation) (degree : ℕ) : lift data degree 1 = 1 := by
  apply tensor_ext data degree
  intro polynomial vector
  rw [lift_tensor]
  rfl

theorem lift_mul (data : CuspidalRepresentation) (degree : ℕ)
    (first second : Module.End ℂ (Binary.HomogeneousPoly (degree + 1))) :
    lift data degree (first * second) = lift data degree first * lift data degree second := by
  apply tensor_ext data degree
  intro polynomial vector
  rw [Module.End.mul_apply, lift_tensor, lift_tensor, lift_tensor]
  rfl

noncomputable def changeMatrix : Matrix (Fin 2) (Fin 2) ℂ := !![1, Complex.I; 1, -Complex.I]

noncomputable def inverseMatrix : Matrix (Fin 2) (Fin 2) ℂ := !![1 / 2, 1 / 2; -Complex.I / 2, Complex.I / 2]

theorem change_inverse : changeMatrix * inverseMatrix = 1 := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [changeMatrix, inverseMatrix, Matrix.mul_apply, Fin.sum_univ_two, ← mul_div_assoc, div_mul_eq_mul_div]

theorem inverse_change : inverseMatrix * changeMatrix = 1 := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [changeMatrix, inverseMatrix, Matrix.mul_apply, Fin.sum_univ_two, ← mul_div_assoc, div_mul_eq_mul_div, neg_div]

noncomputable def substitute (degree : ℕ) (matrix : Matrix (Fin 2) (Fin 2) ℂ) :
    Module.End ℂ (Binary.HomogeneousPoly (degree + 1)) where
  toFun polynomial := ⟨Binary.substitute matrix polynomial.val, Binary.substitute_homogeneous matrix polynomial.property⟩
  map_add' first second := Subtype.ext (map_add (Binary.substitute matrix) first.val second.val)
  map_smul' scalar polynomial := Subtype.ext (map_smul (Binary.substitute matrix) scalar polynomial.val)

theorem substitute_mul (degree : ℕ) (first second : Matrix (Fin 2) (Fin 2) ℂ) :
    substitute degree first * substitute degree second = substitute degree (second * first) := by
  apply LinearMap.ext
  intro polynomial
  apply Subtype.ext
  exact congrArg (fun linear : Binary.Poly →ₐ[ℂ] Binary.Poly => linear polynomial.val) (Binary.substitute_comp first second)

theorem substitute_one (degree : ℕ) : substitute degree 1 = 1 := by
  apply LinearMap.ext
  intro polynomial
  apply Subtype.ext
  exact congrArg (fun linear : Binary.Poly →ₐ[ℂ] Binary.Poly => linear polynomial.val) Binary.substitute_one

noncomputable def toMonomials (data : CuspidalRepresentation) (degree : ℕ) : Module.End ℂ (Vectors data degree) :=
  lift data degree (substitute degree changeMatrix)

noncomputable def fromMonomials (data : CuspidalRepresentation) (degree : ℕ) : Module.End ℂ (Vectors data degree) :=
  lift data degree (substitute degree inverseMatrix)

theorem from_to (data : CuspidalRepresentation) (degree : ℕ) (vectors : Vectors data degree) :
    fromMonomials data degree (toMonomials data degree vectors) = vectors := by
  change (lift data degree (substitute degree inverseMatrix) * lift data degree (substitute degree changeMatrix)) vectors = _
  rw [← lift_mul, substitute_mul, change_inverse, substitute_one, lift_one, Module.End.one_apply]

theorem to_from (data : CuspidalRepresentation) (degree : ℕ) (vectors : Vectors data degree) :
    toMonomials data degree (fromMonomials data degree vectors) = vectors := by
  change (lift data degree (substitute degree changeMatrix) * lift data degree (substitute degree inverseMatrix)) vectors = _
  rw [← lift_mul, substitute_mul, inverse_change, substitute_one, lift_one, Module.End.one_apply]

theorem substitute_basis (degree : ℕ) (index : Index (degree + 1)) :
    (substitute degree changeMatrix (basisMonomial index)).val = PolynomialLadder.monomial (index.val 0) (index.val 1) := by
  change Binary.substitute changeMatrix (MvPolynomial.monomial index.val 1) = _
  rw [Binary.substitute, MvPolynomial.bind₁_monomial, map_one, one_mul]
  change (index.val.prod (fun position power => Binary.linearForm changeMatrix position ^ power)) = _
  rw [Finsupp.prod_pow, Fin.prod_univ_two]
  congr 1 <;> congr 1
  · simp [Binary.linearForm, changeMatrix, PolynomialLadder.plusVariable, Algebra.smul_def]
  · simp [Binary.linearForm, changeMatrix, PolynomialLadder.minusVariable, Algebra.smul_def, sub_eq_add_neg]

/-- Every supplied coefficient tuple has unique coordinates in the rotation monomials. -/
theorem rotation_reconstruct (data : CuspidalRepresentation) (degree : ℕ) (vectors : Vectors data degree) :
    ∑ index : Index (degree + 1),
      tensor data degree (PolynomialLadder.monomial (index.val 0) (index.val 1))
        (fromMonomials data degree vectors index) = vectors := by
  have equality := congrArg (toMonomials data degree)
    (tensor_basis_reconstruct data degree (fromMonomials data degree vectors))
  simp only [map_sum, toMonomials, lift_tensor, substitute_basis] at equality
  exact equality.trans (to_from data degree vectors)

theorem index_degree (degree : ℕ) (index : Index degree) : index.val 0 + index.val 1 = degree := by
  simpa only [Finsupp.degree_eq_sum, Fin.sum_univ_two] using index.property

theorem toMonomials_sum (data : CuspidalRepresentation) (degree : ℕ) (vectors : Vectors data degree) :
    toMonomials data degree vectors = ∑ index : Index (degree + 1),
      tensor data degree (PolynomialLadder.monomial (index.val 0) (index.val 1)) (vectors index) := by
  funext index
  change (∑ other : Index (degree + 1),
    (substitute degree changeMatrix (basisMonomial other)).val.coeff index.val • vectors other) = _
  simp only [substitute_basis, Finset.sum_apply, tensor]

theorem rotation_toMonomials (data : CuspidalRepresentation) (degree : ℕ) (vectors : Vectors data degree) :
    CoefficientInfinitesimal.operator data degree LieOperators.rotationMatrix (toMonomials data degree vectors) =
      toMonomials data degree (fun index => LieOperators.rotationOperator data (vectors index) +
        (Complex.I * ((index.val 1 : ℂ) - index.val 0)) • vectors index) := by
  rw [toMonomials_sum, map_sum, toMonomials_sum]
  apply Finset.sum_congr rfl
  intro index _
  rw [rotation_tensor data degree _ _ (index_degree (degree + 1) index), tensor_vector_add, tensor_vector_smul]

theorem fromMonomials_rotation (data : CuspidalRepresentation) (degree : ℕ) (vectors : Vectors data degree) :
    fromMonomials data degree (CoefficientInfinitesimal.operator data degree LieOperators.rotationMatrix vectors) =
      fun index => LieOperators.rotationOperator data (fromMonomials data degree vectors index) +
        (Complex.I * ((index.val 1 : ℂ) - index.val 0)) • fromMonomials data degree vectors index := by
  have equality := congrArg (fromMonomials data degree)
    (rotation_toMonomials data degree (fromMonomials data degree vectors))
  rw [to_from, from_to] at equality
  exact equality

theorem lift_fixed (data : CuspidalRepresentation) (degree : ℕ)
    (linear : Module.End ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL) (vectors : Vectors data degree)
    (fixed : ∀ index, (vectors index).val ∈ BinaryLevel.fixedSubspace data level) (index : Index (degree + 1)) :
    (lift data degree linear vectors index).val ∈ BinaryLevel.fixedSubspace data level := by
  change (∑ other : Index (degree + 1),
    (linear (basisMonomial other)).val.coeff index.val • vectors other).val ∈ _
  simp only [Submodule.coe_sum, Submodule.coe_smul]
  exact (BinaryLevel.fixedSubspace data level).sum_mem (fun other _ =>
    (BinaryLevel.fixedSubspace data level).smul_mem _ (fixed other))

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.CoefficientCoordinates
