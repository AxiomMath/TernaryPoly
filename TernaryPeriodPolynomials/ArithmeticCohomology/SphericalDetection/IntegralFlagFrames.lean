module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.IntegralLatticeBasis

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

/-- The kernel of a nonzero integral linear form has an integral basis that extends
by one vector to a basis of the ambient lattice. -/
theorem integerLinearForm_exists_basis {dimension : ℕ}
    (form : (Fin (dimension + 1) → ℤ) →ₗ[ℤ] ℤ) (nonzero : form ≠ 0) :
    ∃ basis : Module.Basis (Fin (dimension + 1)) ℤ (Fin (dimension + 1) → ℤ),
      ∀ index : Fin dimension, form (basis index.castSucc) = 0 := by
  let ideal : Ideal ℤ := LinearMap.range form
  let generator := Submodule.IsPrincipal.generator ideal
  have generator_nonzero : generator ≠ 0 := by
    intro zero
    apply nonzero
    apply LinearMap.ext
    intro vector
    obtain ⟨scalar, equality⟩ :=
      (Submodule.IsPrincipal.mem_iff_eq_smul_generator ideal).mp
        (show form vector ∈ ideal from ⟨vector, rfl⟩)
    change form vector = scalar • generator at equality
    change form vector = 0
    simpa only [zero, smul_zero] using equality
  obtain ⟨last, last_image⟩ :=
    (Submodule.IsPrincipal.generator_mem ideal : generator ∈ LinearMap.range form)
  obtain ⟨rank, ⟨kernel_basis⟩⟩ :=
    Submodule.nonempty_basis_of_pid (Pi.basisFun ℤ (Fin (dimension + 1))) (LinearMap.ker form)
  have independent (scalar : ℤ) (vector : Fin (dimension + 1) → ℤ)
      (in_kernel : vector ∈ LinearMap.ker form) (zero : scalar • last + vector = 0) : scalar = 0 := by
    have mapped := congrArg form zero
    rw [map_add, map_smul, last_image, LinearMap.mem_ker.mp in_kernel, add_zero, map_zero,
      smul_eq_mul] at mapped
    exact (mul_eq_zero.mp mapped).resolve_right generator_nonzero
  have spanning (vector : Fin (dimension + 1) → ℤ) :
      ∃ scalar : ℤ, vector + scalar • last ∈ LinearMap.ker form := by
    obtain ⟨scalar, equality⟩ :=
      (Submodule.IsPrincipal.mem_iff_eq_smul_generator ideal).mp
        (show form vector ∈ ideal from ⟨vector, rfl⟩)
    refine ⟨-scalar, ?_⟩
    rw [LinearMap.mem_ker, map_add, map_smul, last_image, equality, neg_smul, add_neg_cancel]
  let extended := kernel_basis.mkFinSnoc last independent spanning
  have rank_eq : rank = dimension := by
    have ranks := Module.finrank_eq_card_basis extended
    simpa using ranks.symm
  subst rank
  refine ⟨extended, fun index => ?_⟩
  change form ((kernel_basis.mkFinSnoc last independent spanning) index.castSucc) = 0
  rw [Module.Basis.coe_mkFinSnoc, Fin.snoc_castSucc]
  exact (kernel_basis index).property

/-- An integral basis gives an actual invertible integer matrix with those columns. -/
theorem integerBasis_exists_matrix {dimension : ℕ}
    (basis : Module.Basis (Fin dimension) ℤ (Fin dimension → ℤ)) :
    ∃ matrix : GeneralLinearGroup (Fin dimension) ℤ,
      ∀ column, (fun row => matrix.val row column) = basis column := by
  let matrix := GeneralLinearGroup.toLin.symm
    (LinearMap.GeneralLinearGroup.ofLinearEquiv basis.equivFun.symm)
  refine ⟨matrix, fun column => ?_⟩
  have action (vector : Fin dimension → ℤ) : matrix.val *ᵥ vector = basis.equivFun.symm vector := by
    change (matrix.val.mulVecLin) vector = _
    rw [← GeneralLinearGroup.coe_toLin]
    change ((GeneralLinearGroup.toLin (GeneralLinearGroup.toLin.symm
      (LinearMap.GeneralLinearGroup.ofLinearEquiv basis.equivFun.symm))).val) vector = _
    rw [MulEquiv.apply_symm_apply]
    rfl
  have equality := action (Pi.single column 1)
  funext row
  simpa [Pi.single_apply, Matrix.mulVec, dotProduct, ite_apply] using congrFun equality row

/-- A rational plane has a unimodular integral frame. -/
theorem rationalPlane_exists_integral_frame (matrix : RationalGL3) :
    ∃ frame : GeneralLinearGroup (Fin 3) ℤ,
      QuotientGroup.mk (integralRational frame) =
        (QuotientGroup.mk matrix : Flags .plane) := by
  let normal : Fin 3 → ℚ := fun column => (matrix⁻¹).val 2 column
  obtain ⟨denominator, integral⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors ℤ) normal
  choose row row_eq using integral
  have row_cast (index : Fin 3) : (row index : ℚ) = (denominator.val : ℚ) * normal index := by
    simpa only [Algebra.smul_def, eq_intCast] using row_eq index
  let form : (Fin 3 → ℤ) →ₗ[ℤ] ℤ :=
    { toFun := fun vector => row ⬝ᵥ vector
      map_add' := fun _ _ => dotProduct_add _ _ _
      map_smul' := fun _ _ => dotProduct_smul _ _ _ }
  have denominator_ne : (denominator.val : ℚ) ≠ 0 := by
    exact_mod_cast nonZeroDivisors.ne_zero denominator.property
  have form_cast (vector : Fin 3 → ℤ) : (form vector : ℚ) =
      (denominator.val : ℚ) * (normal ⬝ᵥ fun index => (vector index : ℚ)) := by
    simp only [form, LinearMap.coe_mk, AddHom.coe_mk, dotProduct, Int.cast_sum,
      Int.cast_mul, row_cast, Finset.mul_sum, mul_assoc]
  have form_ne : form ≠ 0 := by
    intro zero
    have normal_zero : normal = 0 := by
      funext index
      have equality := form_cast (Pi.single index 1)
      rw [zero] at equality
      have product_zero : (denominator.val : ℚ) * normal index = 0 := by
        simpa [Pi.single_apply, dotProduct] using equality.symm
      exact (mul_eq_zero.mp product_zero).resolve_left denominator_ne
    have diagonal := congrArg (fun value : RationalGL3 => value.val 2 2)
      (inv_mul_cancel matrix)
    change (∑ index, normal index * matrix.val index 2) = 1 at diagonal
    simp only [normal_zero, Pi.zero_apply, zero_mul, Finset.sum_const_zero] at diagonal
    exact zero_ne_one diagonal
  obtain ⟨basis, kernel⟩ := integerLinearForm_exists_basis (dimension := 2) form form_ne
  obtain ⟨frame, columns⟩ := integerBasis_exists_matrix basis
  refine ⟨frame, ?_⟩
  apply Eq.symm
  apply QuotientGroup.eq.mpr
  change ((matrix⁻¹ * integralRational frame).val 2 0 = 0) ∧
    ((matrix⁻¹ * integralRational frame).val 2 1 = 0)
  have vanishing (index : Fin 2) : (matrix⁻¹ * integralRational frame).val 2 index.castSucc = 0 := by
    have equality := form_cast (basis index.castSucc)
    rw [kernel, Int.cast_zero] at equality
    have zero : normal ⬝ᵥ (fun row => ((basis index.castSucc) row : ℚ)) = 0 :=
      (mul_eq_zero.mp equality.symm).resolve_left denominator_ne
    simpa only [GeneralLinearGroup.coe_mul, Matrix.mul_apply, integralRational,
      GeneralLinearGroup.map_apply, Int.coe_castRingHom, ← columns, normal, dotProduct] using zero
  exact ⟨vanishing 0, vanishing 1⟩

end TernaryPeriodPolynomials.SphericalDetection.Helpers
