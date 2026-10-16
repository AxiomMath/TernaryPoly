module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Scalar.HeckeImage
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.CommonEigenvector
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Hecke.Multiplicativity
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.ScalarNonvanishing

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Manifold

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem cuspClassicalScalarImage_exists_form (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (negative : halfWeight < 0) (function : cuspClassicalScalarImage cusp halfWeight) :
    ∃ form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range (-2 * halfWeight),
      (form : UpperHalfPlane → ℂ) = function.val := by
  obtain ⟨vector, classical_vector, equality⟩ :=
    (cuspClassicalScalarImage_mem cusp halfWeight function.val).mp function.property
  exact ⟨⟨cuspLevelOneSlashInvariant cusp halfWeight vector classical_vector.1 classical_vector.2.1,
    classical_vector.2.2, cuspLevelOneSlashInvariant_zero_at_cusps cusp halfWeight negative vector
      classical_vector.1 classical_vector.2.1⟩, equality⟩

def cuspScalarImageForm (cusp : CuspidalRepresentation) (halfWeight : ℤ) (negative : halfWeight < 0)
    (function : cuspClassicalScalarImage cusp halfWeight) :
    CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range (-2 * halfWeight) :=
  (cuspClassicalScalarImage_exists_form cusp halfWeight negative function).choose

theorem cuspScalarImageForm_coe (cusp : CuspidalRepresentation) (halfWeight : ℤ) (negative : halfWeight < 0)
    (function : cuspClassicalScalarImage cusp halfWeight) :
    (cuspScalarImageForm cusp halfWeight negative function : UpperHalfPlane → ℂ) = function.val :=
  (cuspClassicalScalarImage_exists_form cusp halfWeight negative function).choose_spec

def cuspScalarImageToCuspForm (cusp : CuspidalRepresentation) (halfWeight : ℤ) (negative : halfWeight < 0) :
    cuspClassicalScalarImage cusp halfWeight →ₗ[ℂ]
      CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range (-2 * halfWeight) where
  toFun := cuspScalarImageForm cusp halfWeight negative
  map_add' first second := by
    apply DFunLike.ext
    intro point
    change cuspScalarImageForm cusp halfWeight negative (first + second) point =
      cuspScalarImageForm cusp halfWeight negative first point + cuspScalarImageForm cusp halfWeight negative second point
    simp only [cuspScalarImageForm_coe, Submodule.coe_add, Pi.add_apply]
  map_smul' scalar function := by
    apply DFunLike.ext
    intro point
    change cuspScalarImageForm cusp halfWeight negative (scalar • function) point =
      scalar • cuspScalarImageForm cusp halfWeight negative function point
    simp only [cuspScalarImageForm_coe, Submodule.coe_smul, Pi.smul_apply]

theorem cuspScalarImageToCuspForm_injective (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (negative : halfWeight < 0) : Function.Injective (cuspScalarImageToCuspForm cusp halfWeight negative) := by
  intro first second equal
  apply Subtype.ext
  have equal_functions := congrArg (fun form : CuspForm
    (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range (-2 * halfWeight) =>
      (form : UpperHalfPlane → ℂ)) equal
  simpa only [cuspScalarImageToCuspForm, LinearMap.coe_mk, AddHom.coe_mk,
    cuspScalarImageForm_coe] using equal_functions

theorem cuspClassicalScalarImage_finiteDimensional (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (negative : halfWeight < 0) : FiniteDimensional ℂ (cuspClassicalScalarImage cusp halfWeight) :=
  FiniteDimensional.of_injective
    (CuspForm.toModularFormₗ.comp (cuspScalarImageToCuspForm cusp halfWeight negative))
    (CuspForm.toModularFormₗ_injective.comp (cuspScalarImageToCuspForm_injective cusp halfWeight negative))

theorem scalarPrimeHecke_eigen_relations (halfWeight : ℤ) (function : UpperHalfPlane → ℂ)
    (eigenvalues : Nat.Primes → ℂ)
    (eigenvectors : ∀ prime, scalarPrimeHecke halfWeight prime function = eigenvalues prime • function) :
    HasPrimeHeckeRelations (-2 * halfWeight) function
      (fun prime => (prime.val : ℂ) ^ (-halfWeight - 1) * eigenvalues prime) := by
  intro prime point
  have equality := congrFun (eigenvectors prime).symm point
  change eigenvalues prime * function point =
    (prime.val : ℂ) ^ (-halfWeight) * function
      (GeneralLinearGroup.map (algebraMap ℚ ℝ) (binaryHeckeDilate prime.val prime.property.pos) • point) +
    (prime.val : ℂ) ^ halfWeight * ∑ index : Fin prime.val, function
      (GeneralLinearGroup.map (algebraMap ℚ ℝ) (binaryHeckeTranslate prime.val prime.property.pos index) • point) at equality
  have scaled := congrArg (fun value : ℂ => (prime.val : ℂ) ^ (-halfWeight - 1) * value) equality
  rw [mul_add, ← mul_assoc, ← mul_assoc, ← mul_assoc,
    ← zpow_add₀ (Nat.cast_ne_zero.mpr prime.property.ne_zero),
    ← zpow_add₀ (Nat.cast_ne_zero.mpr prime.property.ne_zero)] at scaled
  have first_exponent : -halfWeight - 1 + -halfWeight = -2 * halfWeight - 1 := by ring
  have second_exponent : -halfWeight - 1 + halfWeight = -1 := by ring
  rw [first_exponent, second_exponent, _root_.zpow_neg_one] at scaled
  exact scaled

/-- A nonzero actual classical scalar image contains a simultaneous Hecke eigenform. -/
theorem cuspClassicalScalarImage_exists_eigenform (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (negative : halfWeight < 0) (vector : cusp.smooth)
    (classical_vector : vector ∈ cuspClassicalVectors cusp halfWeight)
    (nonzero : cuspScalarWeightedLinear cusp halfWeight 1 vector ≠ 0) :
    ∃ (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range (-2 * halfWeight))
      (eigenvector : cusp.smooth) (eigenvalues : Nat.Primes → ℂ),
      form ≠ 0 ∧ eigenvector ∈ cuspClassicalVectors cusp halfWeight ∧
      (form : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear cusp halfWeight 1 eigenvector ∧
      HasPrimeHeckeRelations (-2 * halfWeight) form eigenvalues := by
  let : FiniteDimensional ℂ (cuspClassicalScalarImage cusp halfWeight) :=
    cuspClassicalScalarImage_finiteDimensional cusp halfWeight negative
  have image_nonzero : cuspClassicalScalarImage cusp halfWeight ≠ ⊥ := by
    intro zero
    have member := (cuspClassicalScalarImage_mem cusp halfWeight _).mpr ⟨vector, classical_vector, rfl⟩
    rw [zero, Submodule.mem_bot] at member
    exact nonzero member
  let : Nontrivial (cuspClassicalScalarImage cusp halfWeight) :=
    Submodule.nontrivial_iff_ne_bot.mpr image_nonzero
  obtain ⟨function, eigenvalues, function_nonzero, action⟩ :=
    commuting_family_exists_eigenvector (cuspScalarImageHecke cusp central_positive halfWeight)
      (cuspScalarImageHecke_commute cusp central_positive halfWeight)
  obtain ⟨eigenvector, eigenvector_classical, realization⟩ :=
    (cuspClassicalScalarImage_mem cusp halfWeight function.val).mp function.property
  refine ⟨cuspScalarImageForm cusp halfWeight negative function, eigenvector,
    fun prime => (prime.val : ℂ) ^ (-halfWeight - 1) * eigenvalues prime, ?_,
    eigenvector_classical, (cuspScalarImageForm_coe cusp halfWeight negative function).trans realization.symm, ?_⟩
  · intro zero
    apply function_nonzero
    apply Subtype.ext
    rw [← cuspScalarImageForm_coe cusp halfWeight negative function, zero]
    rfl
  · rw [cuspScalarImageForm_coe]
    exact scalarPrimeHecke_eigen_relations halfWeight function.val eigenvalues
      (fun prime => congrArg Subtype.val (action prime))

theorem cuspClassicalVectors_mem_of_holomorphic (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (vector : cusp.smooth) (spherical : vector.val ∈ cuspSphericalValues cusp)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector.val =
      (angle : ℂ) ^ (2 * halfWeight) • vector.val)
    (holomorphic : DifferentiableOn ℂ (cuspScalarWeightedRealization cusp halfWeight vector 1)
      UpperHalfPlane.upperHalfPlaneSet) : vector ∈ cuspClassicalVectors cusp halfWeight := by
  refine ⟨spherical, rotation, UpperHalfPlane.mdifferentiable_iff.mpr ?_⟩
  apply holomorphic.congr
  intro point positive
  rw [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos positive]
  rfl

/-- Only one nonzero holomorphic scalar realization is needed for extraction; the Hecke
eigenrelations and nonzero outer values follow inside its actual scalar image. -/
theorem cuspScalar_exists_eigenform_outerLValues (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (negative : halfWeight < 0) (vector : cusp.smooth)
    (spherical : vector.val ∈ cuspSphericalValues cusp)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector.val =
      (angle : ℂ) ^ (2 * halfWeight) • vector.val)
    (holomorphic : DifferentiableOn ℂ (cuspScalarWeightedRealization cusp halfWeight vector 1)
      UpperHalfPlane.upperHalfPlaneSet)
    (nonzero : vector ≠ 0)
    (modulus : ℕ) :
    ∃ (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range (-2 * halfWeight))
      (eigenvector : cusp.smooth) (eigenvalues : Nat.Primes → ℂ),
      form ≠ 0 ∧ eigenvector ∈ cuspClassicalVectors cusp halfWeight ∧
      (form : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear cusp halfWeight 1 eigenvector ∧
      HasPrimeHeckeRelations (-2 * halfWeight) form eigenvalues ∧
      LSeries (removeEulerCoefficients (fun index => (UpperHalfPlane.qExpansion 1 form).coeff index)
        modulus) (((-2 * halfWeight : ℤ) : ℂ) - 2) ≠ 0 ∧
      LSeries (removeEulerCoefficients (fun index => (UpperHalfPlane.qExpansion 1 form).coeff index)
        modulus) (((-2 * halfWeight : ℤ) : ℂ) - 1) ≠ 0 := by
  have function_nonzero : cuspScalarWeightedLinear cusp halfWeight 1 vector ≠ 0 := by
    obtain ⟨point, nonzero_value⟩ := cuspScalarWeightedRealization_identity_nonzero cusp central_positive
      halfWeight vector spherical rotation nonzero
    intro zero
    exact nonzero_value (congrFun zero point)
  obtain ⟨form, eigenvector, eigenvalues, form_nonzero, classical_vector, realization, relations⟩ :=
    cuspClassicalScalarImage_exists_eigenform cusp central_positive halfWeight negative vector
      (cuspClassicalVectors_mem_of_holomorphic cusp halfWeight vector spherical rotation holomorphic)
      function_nonzero
  refine ⟨form, eigenvector, eigenvalues, form_nonzero, classical_vector, realization, relations, ?_⟩
  simpa only [Complex.ofReal_sub, Complex.ofReal_intCast, Complex.ofReal_ofNat, Complex.ofReal_one] using
    levelOneCuspForm_hecke_outerLValues_ne_zero_of_nonzero form form_nonzero modulus eigenvalues relations

end TernaryPeriodPolynomials.SphericalDetection.Helpers
