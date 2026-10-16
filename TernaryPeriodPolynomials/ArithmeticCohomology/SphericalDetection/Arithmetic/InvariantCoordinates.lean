module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Arithmetic.EdgeExactness
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Radical.LatticeInvariants

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial CategoryTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def upperRadicalInvariantEmbedding (degree : ℕ) : ℂ →ₗ[ℂ] HomogeneousPoly degree :=
  LinearMap.toSpanSingleton ℂ _ ⟨X 2 ^ degree, isHomogeneous_X_pow 2 degree⟩

theorem upperRadicalInvariantEmbedding_apply (degree : ℕ) (scalar : ℂ) :
    (upperRadicalInvariantEmbedding degree scalar).val = scalar • (X 2 ^ degree : Poly) := rfl

def upperRadicalInvariantLine (degree : ℕ) : ℂ →ₗ[ℂ] (upperRadicalLatticeRep degree).ρ.invariants :=
  (upperRadicalInvariantEmbedding degree).codRestrict _ (by
    intro scalar
    apply (upperRadicalInvariant_scalar degree _).mpr
    exact ⟨scalar, Algebra.smul_def scalar _⟩)

theorem upperRadicalInvariantLine_apply (degree : ℕ) (scalar : ℂ) :
    (upperRadicalInvariantLine degree scalar).val.val = scalar • (X 2 ^ degree : Poly) := rfl

theorem upperRadicalInvariantLine_bijective (degree : ℕ) : Function.Bijective (upperRadicalInvariantLine degree) := by
  constructor
  · intro first second equality
    have values := congrArg
      (fun vector : (upperRadicalLatticeRep degree).ρ.invariants => vector.val.val.coeff (Finsupp.single 2 degree)) equality
    simpa [upperRadicalInvariantLine_apply, coeff_smul, coeff_X_pow] using values
  · intro polynomial
    obtain ⟨scalar, equality⟩ := (upperRadicalInvariant_scalar degree polynomial.val).mp polynomial.property
    refine ⟨scalar, Subtype.ext (Subtype.ext ?_)⟩
    exact (Algebra.smul_def scalar (X 2 ^ degree : Poly)).trans equality.symm

def upperRadicalInvariantEquiv (degree : ℕ) : ℂ ≃ₗ[ℂ] (upperRadicalLatticeRep degree).ρ.invariants :=
  LinearEquiv.ofBijective (upperRadicalInvariantLine degree) (upperRadicalInvariantLine_bijective degree)

def lowerRadicalInvariantLift (degree : ℕ) :
    Binary.HomogeneousPoly degree →ₗ[ℂ] (lowerRadicalLatticeRep degree).ρ.invariants :=
  (binaryHomogeneousLift degree).codRestrict _ (by
    intro binary
    exact (lowerRadicalInvariant_binary degree _).mpr ⟨binary, rfl⟩)

theorem lowerRadicalInvariantLift_apply (degree : ℕ) (binary : Binary.HomogeneousPoly degree) :
    (lowerRadicalInvariantLift degree binary).val = binaryHomogeneousLift degree binary := rfl

theorem lowerRadicalInvariantLift_bijective (degree : ℕ) : Function.Bijective (lowerRadicalInvariantLift degree) := by
  constructor
  · intro first second equality
    exact binaryHomogeneousLift_injective degree (congrArg Subtype.val equality)
  · intro polynomial
    obtain ⟨binary, equality⟩ := (lowerRadicalInvariant_binary degree polynomial.val).mp polynomial.property
    exact ⟨binary, Subtype.ext equality⟩

def lowerRadicalInvariantEquiv (degree : ℕ) :
    Binary.HomogeneousPoly degree ≃ₗ[ℂ] (lowerRadicalLatticeRep degree).ρ.invariants :=
  LinearEquiv.ofBijective (lowerRadicalInvariantLift degree) (lowerRadicalInvariantLift_bijective degree)

def arithmeticDeterminantCharacter : GeneralLinearGroup (Fin 2) ℤ →* ℂ :=
  (Binary.determinantCharacter (-1)).comp (GeneralLinearGroup.map (Int.castRingHom ℂ))

def arithmeticDeterminantRep : Rep ℂ (GeneralLinearGroup (Fin 2) ℤ) :=
  Rep.of ((algebraMap ℂ (Module.End ℂ ℂ)).toMonoidHom.comp arithmeticDeterminantCharacter)

theorem arithmeticDeterminantRep_apply (matrix : GeneralLinearGroup (Fin 2) ℤ) (scalar : ℂ) :
    arithmeticDeterminantRep.ρ matrix scalar = arithmeticDeterminantCharacter matrix * scalar := rfl

theorem action_planeLevi_third_power (exponent : ℤ) (matrix : Binary.GL2) (degree : ℕ) :
    action exponent (planeLevi matrix 1) (X 2 ^ degree) =
      Binary.determinantCharacter exponent matrix • (X 2 ^ degree : Poly) := by
  rw [action_apply, planeLevi_determinantCharacter]
  simp only [Units.val_one, one_zpow, mul_one, planeLevi_inverse, inv_one, planeLevi_value,
    map_pow, substitute_X, planeBlock_linearForm_third, C_1, one_mul]

theorem arithmeticLevi_upperInvariant (degree : ℕ) (matrix : GeneralLinearGroup (Fin 2) ℤ) (scalar : ℂ) :
    arithmeticLeviCoefficient degree matrix (upperRadicalInvariantEmbedding degree scalar) =
      upperRadicalInvariantEmbedding degree (arithmeticDeterminantCharacter matrix * scalar) := by
  rw [arithmeticLeviCoefficient_homogeneous]
  apply Subtype.ext
  change action (-1) (planeLevi (GeneralLinearGroup.map (Int.castRingHom ℂ) matrix) 1)
    (scalar • (X 2 ^ degree : Poly)) = (arithmeticDeterminantCharacter matrix * scalar) • (X 2 ^ degree : Poly)
  rw [map_smul, action_planeLevi_third_power, smul_smul, mul_comm]
  rfl

theorem arithmeticLevi_lowerInvariant (degree : ℕ) (matrix : GeneralLinearGroup (Fin 2) ℤ)
    (binary : Binary.HomogeneousPoly degree) :
    arithmeticLeviCoefficient degree matrix (binaryHomogeneousLift degree binary) =
      binaryHomogeneousLift degree ((arithmeticBinaryRep degree (-1)).ρ matrix binary) := by
  rw [arithmeticLeviCoefficient_homogeneous]
  apply Subtype.ext
  change action (-1) (planeLevi (GeneralLinearGroup.map (Int.castRingHom ℂ) matrix) 1)
    (binaryPolynomialLift binary.val) = binaryPolynomialLift
      (Binary.action (-1) (GeneralLinearGroup.map (Int.castRingHom ℂ) matrix) binary.val)
  rw [action_planeLevi_lift]
  simp only [Units.val_one, one_zpow, one_smul]

def identityPlaneInvariantIso (degree : ℕ) :
    arithmeticDeterminantRep ≅ splitInvariantRepresentation identityPlaneSplitting (identityPlaneCoefficientRep degree) :=
  Rep.mkIso (Representation.Equiv.mk (upperRadicalInvariantEquiv degree) (by
    intro matrix
    apply LinearMap.ext
    intro scalar
    apply Subtype.ext
    exact (arithmeticLevi_upperInvariant degree matrix scalar).symm))

def goodLineInvariantIso (degree : ℕ) :
    arithmeticBinaryRep degree (-1) ≅ splitInvariantRepresentation goodLineSplitting (goodLineCoefficientRep degree) :=
  Rep.mkIso (Representation.Equiv.mk (lowerRadicalInvariantEquiv degree) (by
    intro matrix
    apply LinearMap.ext
    intro binary
    apply Subtype.ext
    exact (arithmeticLevi_lowerInvariant degree matrix binary).symm))

def identityPlaneInvariantH2Iso (degree : ℕ) :
    groupCohomology.H2 arithmeticDeterminantRep ≅
      groupCohomology.H2 (splitInvariantRepresentation identityPlaneSplitting (identityPlaneCoefficientRep degree)) :=
  (groupCohomology.functor ℂ (GeneralLinearGroup (Fin 2) ℤ) 2).mapIso (identityPlaneInvariantIso degree)

def goodLineInvariantH2Iso (degree : ℕ) :
    groupCohomology.H2 (arithmeticBinaryRep degree (-1)) ≅
      groupCohomology.H2 (splitInvariantRepresentation goodLineSplitting (goodLineCoefficientRep degree)) :=
  (groupCohomology.functor ℂ (GeneralLinearGroup (Fin 2) ℤ) 2).mapIso (goodLineInvariantIso degree)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
