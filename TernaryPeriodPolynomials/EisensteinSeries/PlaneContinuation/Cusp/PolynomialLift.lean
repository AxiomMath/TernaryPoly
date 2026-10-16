module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.ReflectionModes

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspPolynomialLift

abbrev Index (degree : ℕ) := {monomial : Fin 2 →₀ ℕ // monomial.degree = degree}

instance indexFinite (degree : ℕ) : Finite (Index degree) := by
  let encoding : Index degree → Fin 2 → Fin (degree + 1) := fun monomial position =>
    ⟨monomial.val position, by
      have bound := Finsupp.le_degree position monomial.val
      rw [monomial.property] at bound
      exact Nat.lt_succ_of_le bound⟩
  apply Finite.of_injective encoding
  intro first second equality
  apply Subtype.ext
  apply Finsupp.ext
  intro position
  exact congrArg Fin.val (congrFun equality position)

noncomputable instance indexFintype (degree : ℕ) : Fintype (Index degree) := Fintype.ofFinite _

noncomputable def basisMonomial {degree : ℕ} (index : Index degree) : Binary.HomogeneousPoly degree :=
  ⟨MvPolynomial.monomial index.val 1, MvPolynomial.isHomogeneous_monomial 1 index.property⟩

noncomputable def polynomial (degree : ℕ) : (Index degree → ℂ) →ₗ[ℂ] Binary.HomogeneousPoly degree where
  toFun coefficients := ∑ index, coefficients index • basisMonomial index
  map_add' first second := by simp [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' scalar coefficients := by simp [Pi.smul_apply, Finset.smul_sum, smul_smul]

theorem polynomial_coefficient (degree : ℕ) (coefficients : Index degree → ℂ) (index : Index degree) :
    (polynomial degree coefficients).val.coeff index.val = coefficients index := by
  classical
  change (∑ other : Index degree, coefficients other • basisMonomial other).val.coeff index.val = _
  simp only [Submodule.coe_sum, MvPolynomial.coeff_sum, Submodule.coe_smul,
    MvPolynomial.coeff_smul, basisMonomial, MvPolynomial.coeff_monomial, smul_eq_mul]
  have equality (other : Index degree) : other.val = index.val ↔ other = index := Subtype.val_inj
  simp only [equality, mul_ite, mul_one, mul_zero]
  simpa only [Finset.mem_univ, ite_true] using Finset.sum_ite_eq' Finset.univ index coefficients

theorem polynomial_reconstruct (degree : ℕ) (value : Binary.HomogeneousPoly degree) :
    polynomial degree (fun index => value.val.coeff index.val) = value := by
  apply Subtype.ext
  apply MvPolynomial.ext
  intro monomial
  by_cases homogeneous : monomial.degree = degree
  · exact polynomial_coefficient degree _ ⟨monomial, homogeneous⟩
  · rw [MvPolynomial.IsHomogeneous.coeff_eq_zero (polynomial degree _).property homogeneous,
      MvPolynomial.IsHomogeneous.coeff_eq_zero value.property homogeneous]

theorem polynomial_ext (degree : ℕ) (first second : Binary.HomogeneousPoly degree)
    (coefficients : ∀ index : Index degree,
      first.val.coeff index.val = second.val.coeff index.val) : first = second := by
  rw [← polynomial_reconstruct degree first, ← polynomial_reconstruct degree second]
  exact congrArg (polynomial degree) (funext coefficients)

abbrev Vectors (data : CuspidalRepresentation) (degree : ℕ) := Index (degree + 1) → data.smooth

noncomputable def realization (data : CuspidalRepresentation) (degree : ℕ) :
    Vectors data degree →ₗ[ℂ] (BinaryAdelicGL → Binary.HomogeneousPoly (degree + 1)) where
  toFun vectors point := polynomial (degree + 1) (fun index => data.realize (vectors index) point)
  map_add' first second := by
    funext point
    change polynomial _ (fun index => data.realize (first index + second index) point) = _
    simp only [map_add, Pi.add_apply]
    exact map_add (polynomial (degree + 1)) _ _
  map_smul' scalar vectors := by
    funext point
    change polynomial _ (fun index => data.realize (scalar • vectors index) point) = _
    simp only [map_smul, Pi.smul_apply]
    exact map_smul (polynomial (degree + 1)) scalar _

theorem realization_coefficient (data : CuspidalRepresentation) (degree : ℕ)
    (vectors : Vectors data degree) (index : Index (degree + 1)) (point : BinaryAdelicGL) :
    (realization data degree vectors point).val.coeff index.val = data.realize (vectors index) point :=
  polynomial_coefficient (degree + 1) _ index

theorem realization_injective (data : CuspidalRepresentation) (degree : ℕ) :
    Function.Injective (realization data degree) := by
  intro first second equality
  funext index
  apply data.injective
  funext point
  have coefficientEquality := congrArg (fun function : BinaryAdelicGL → Binary.HomogeneousPoly (degree + 1) =>
    (function point).val.coeff index.val) equality
  simpa only [realization_coefficient] using coefficientEquality

theorem realization_values (data : CuspidalRepresentation) (degree : ℕ) (vectors : Vectors data degree) :
    BinaryValues data degree (realization data degree vectors) := by
  intro monomial
  by_cases homogeneous : monomial.degree = degree + 1
  · refine ⟨vectors ⟨monomial, homogeneous⟩, ?_⟩
    funext point
    exact (realization_coefficient data degree vectors ⟨monomial, homogeneous⟩ point).symm
  · have equality : (fun point => (realization data degree vectors point).val.coeff monomial) = 0 := by
      funext point
      exact MvPolynomial.IsHomogeneous.coeff_eq_zero (realization data degree vectors point).property homogeneous
    rw [equality]
    exact (cuspFunctions data).zero_mem

noncomputable def lift (data : CuspidalRepresentation) (degree : ℕ)
    (function : BinaryAdelicGL → Binary.HomogeneousPoly (degree + 1))
    (values : BinaryValues data degree function) : Vectors data degree :=
  fun index => Classical.choose (values index.val)

theorem lift_coefficient (data : CuspidalRepresentation) (degree : ℕ)
    (function : BinaryAdelicGL → Binary.HomogeneousPoly (degree + 1))
    (values : BinaryValues data degree function) (index : Index (degree + 1)) (point : BinaryAdelicGL) :
    data.realize (lift data degree function values index) point = (function point).val.coeff index.val :=
  congrFun (Classical.choose_spec (values index.val)) point

theorem realization_lift (data : CuspidalRepresentation) (degree : ℕ)
    (function : BinaryAdelicGL → Binary.HomogeneousPoly (degree + 1))
    (values : BinaryValues data degree function) : realization data degree (lift data degree function values) = function := by
  funext point
  apply polynomial_ext (degree + 1)
  intro index
  rw [realization_coefficient, lift_coefficient]

theorem lift_realization (data : CuspidalRepresentation) (degree : ℕ) (vectors : Vectors data degree) :
    lift data degree (realization data degree vectors) (realization_values data degree vectors) = vectors := by
  apply realization_injective data degree
  exact realization_lift data degree _ _

theorem binaryValues_iff_exists (data : CuspidalRepresentation) (degree : ℕ)
    (function : BinaryAdelicGL → Binary.HomogeneousPoly (degree + 1)) :
    BinaryValues data degree function ↔ ∃ vectors : Vectors data degree, realization data degree vectors = function := by
  constructor
  · intro values
    exact ⟨lift data degree function values, realization_lift data degree function values⟩
  · rintro ⟨vectors, rfl⟩
    exact realization_values data degree vectors

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspPolynomialLift
