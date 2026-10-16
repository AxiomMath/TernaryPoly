module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.IntegralFlagFrames

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem principalLinearForm_exists_basis {ring : Type*} [CommRing ring] [IsDomain ring]
    [IsPrincipalIdealRing ring] {dimension : ℕ}
    (form : (Fin (dimension + 1) → ring) →ₗ[ring] ring) (nonzero : form ≠ 0) :
    ∃ basis : Module.Basis (Fin (dimension + 1)) ring (Fin (dimension + 1) → ring),
      ∀ index : Fin dimension, form (basis index.castSucc) = 0 := by
  let ideal : Ideal ring := LinearMap.range form
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
    Submodule.nonempty_basis_of_pid (Pi.basisFun ring (Fin (dimension + 1))) (LinearMap.ker form)
  have independent (scalar : ring) (vector : Fin (dimension + 1) → ring)
      (in_kernel : vector ∈ LinearMap.ker form) (zero : scalar • last + vector = 0) : scalar = 0 := by
    have mapped := congrArg form zero
    rw [map_add, map_smul, last_image, LinearMap.mem_ker.mp in_kernel, add_zero, map_zero,
      smul_eq_mul] at mapped
    exact (mul_eq_zero.mp mapped).resolve_right generator_nonzero
  have spanning (vector : Fin (dimension + 1) → ring) :
      ∃ scalar : ring, vector + scalar • last ∈ LinearMap.ker form := by
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

theorem basis_exists_generalLinearGroup {ring : Type*} [CommRing ring] {dimension : ℕ}
    (basis : Module.Basis (Fin dimension) ring (Fin dimension → ring)) :
    ∃ matrix : GeneralLinearGroup (Fin dimension) ring,
      ∀ column, (fun row => matrix.val row column) = basis column := by
  let matrix := GeneralLinearGroup.toLin.symm
    (LinearMap.GeneralLinearGroup.ofLinearEquiv basis.equivFun.symm)
  refine ⟨matrix, fun column => ?_⟩
  have action (vector : Fin dimension → ring) : matrix.val *ᵥ vector = basis.equivFun.symm vector := by
    change (matrix.val.mulVecLin) vector = _
    rw [← GeneralLinearGroup.coe_toLin]
    change ((GeneralLinearGroup.toLin (GeneralLinearGroup.toLin.symm
      (LinearMap.GeneralLinearGroup.ofLinearEquiv basis.equivFun.symm))).val) vector = _
    rw [MulEquiv.apply_symm_apply]
    rfl
  have equality := action (Pi.single column 1)
  funext row
  simpa [Pi.single_apply, Matrix.mulVec, dotProduct, ite_apply] using congrFun equality row

/-- An invertible matrix over a fraction field can be made plane-parabolic by
an invertible integral change of columns. -/
theorem fractionGL_exists_parabolic_integral {ring field : Type*}
    [CommRing ring] [IsDomain ring] [IsPrincipalIdealRing ring]
    [Field field] [Algebra ring field] [IsFractionRing ring field]
    (matrix : GeneralLinearGroup (Fin 3) field) :
    ∃ frame : GeneralLinearGroup (Fin 3) ring,
      matrix * GeneralLinearGroup.map (algebraMap ring field) frame ∈ planeParabolic field := by
  let normal : Fin 3 → field := fun column => matrix.val 2 column
  obtain ⟨denominator, integral⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors ring) normal
  choose row row_eq using integral
  have row_map (index : Fin 3) : algebraMap ring field (row index) =
      algebraMap ring field denominator.val * normal index := by
    simpa only [Algebra.smul_def] using row_eq index
  let form : (Fin 3 → ring) →ₗ[ring] ring :=
    { toFun := fun vector => row ⬝ᵥ vector
      map_add' := fun _ _ => dotProduct_add _ _ _
      map_smul' := fun _ _ => dotProduct_smul _ _ _ }
  have denominator_ne : algebraMap ring field denominator.val ≠ 0 := by
    intro zero
    apply nonZeroDivisors.ne_zero denominator.property
    apply IsFractionRing.injective ring field
    simpa only [map_zero] using zero
  have form_map (vector : Fin 3 → ring) : algebraMap ring field (form vector) =
      algebraMap ring field denominator.val *
        (normal ⬝ᵥ fun index => algebraMap ring field (vector index)) := by
    simp only [form, LinearMap.coe_mk, AddHom.coe_mk, dotProduct, map_sum,
      map_mul, row_map, Finset.mul_sum, mul_assoc]
  have form_ne : form ≠ 0 := by
    intro zero
    have normal_zero : normal = 0 := by
      funext index
      have equality := form_map (Pi.single index 1)
      rw [zero] at equality
      have product_zero : algebraMap ring field denominator.val * normal index = 0 := by
        simpa [Pi.single_apply, dotProduct] using equality.symm
      exact (mul_eq_zero.mp product_zero).resolve_left denominator_ne
    have diagonal := congrArg (fun value : GeneralLinearGroup (Fin 3) field => value.val 2 2)
      (mul_inv_cancel matrix)
    change (∑ index, normal index * matrix⁻¹.val index 2) = 1 at diagonal
    simp only [normal_zero, Pi.zero_apply, zero_mul, Finset.sum_const_zero] at diagonal
    exact zero_ne_one diagonal
  obtain ⟨basis, kernel⟩ := principalLinearForm_exists_basis (dimension := 2) form form_ne
  obtain ⟨frame, columns⟩ := basis_exists_generalLinearGroup basis
  refine ⟨frame, ?_⟩
  change ((matrix * GeneralLinearGroup.map (algebraMap ring field) frame).val 2 0 = 0) ∧
    ((matrix * GeneralLinearGroup.map (algebraMap ring field) frame).val 2 1 = 0)
  have vanishing (index : Fin 2) :
      (matrix * GeneralLinearGroup.map (algebraMap ring field) frame).val 2 index.castSucc = 0 := by
    have equality := form_map (basis index.castSucc)
    rw [kernel, map_zero] at equality
    have zero : normal ⬝ᵥ (fun row => algebraMap ring field ((basis index.castSucc) row)) = 0 :=
      (mul_eq_zero.mp equality.symm).resolve_left denominator_ne
    simpa only [GeneralLinearGroup.coe_mul, Matrix.mul_apply, GeneralLinearGroup.map_apply,
      ← columns, normal, dotProduct] using zero
  exact ⟨vanishing 0, vanishing 1⟩

end TernaryPeriodPolynomials.SphericalDetection.Helpers
