module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cuspidal.TensorValues
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineComplementCochain

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def ternaryPolynomialCoefficient (degree : ℕ) (monomial : Fin 3 →₀ ℕ) : HomogeneousPoly degree →ₗ[ℂ] ℂ :=
  (MvPolynomial.lcoeff ℂ monomial).comp (homogeneousSubmodule (Fin 3) ℂ degree).subtype

theorem ternaryPolynomialDual_mem_span_coefficients {degree : ℕ}
    (functional : HomogeneousPoly degree →ₗ[ℂ] ℂ) :
    functional ∈ Submodule.span ℂ (Set.range (ternaryPolynomialCoefficient degree)) := by
  let : FiniteDimensional ℂ (HomogeneousPoly degree) :=
    Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg (Fin 3) ℂ degree)
  apply FiniteDimensional.mem_span_of_iInf_ker_le_ker
  intro polynomial kernels
  have zero : polynomial = 0 := by
    apply Subtype.ext
    apply MvPolynomial.ext
    intro monomial
    have member := (iInf_le (fun monomial => (ternaryPolynomialCoefficient degree monomial).ker) monomial) kernels
    exact member
  rw [zero]
  exact Submodule.zero_mem _

theorem ternaryCuspidalTensorValues_iff (cusp : CuspidalRepresentation) (degree : ℕ)
    (values : BinaryAdelicGL → HomogeneousPoly degree) :
    values ∈ cuspidalTensorValues cusp (HomogeneousPoly degree) ↔
      ∀ monomial : Fin 3 →₀ ℕ, (fun argument => (values argument).val.coeff monomial) ∈ cuspFunctions cusp := by
  constructor
  · intro member monomial
    exact member (ternaryPolynomialCoefficient degree monomial)
  · intro coefficients functional
    let pullback : (HomogeneousPoly degree →ₗ[ℂ] ℂ) →ₗ[ℂ] (BinaryAdelicGL → ℂ) :=
      { toFun := fun functional argument => functional (values argument)
        map_add' := by intros; rfl
        map_smul' := by intros; rfl }
    have spanned : Submodule.span ℂ (Set.range (ternaryPolynomialCoefficient degree)) ≤
        (cuspFunctions cusp).comap pullback := by
      apply Submodule.span_le.mpr
      rintro _ ⟨monomial, rfl⟩
      exact coefficients monomial
    exact spanned (ternaryPolynomialDual_mem_span_coefficients functional)

theorem binaryInductionExponent_plane_endpoint (degree : ℕ) :
    binaryInductionExponent degree .plane cohomologicalPoint = ((degree : ℂ) + 3) / 2 := by
  unfold binaryInductionExponent inductionExponent cohomologicalPoint
  ring

/-- Evaluation along the entire binary adelic Levi retains the actual cusp constituent. -/
def sourcePlaneCuspidalValues {degree : ℕ} (data : InducingData degree) (source : SourceCochain degree)
    (cocycle : IsSourceCocycle data .plane source) (vertices : Fin 3 → RealGL3) (base : AdelicGL) :
    cuspidalTensorValues data.cusp (HomogeneousPoly degree) :=
  ⟨fun argument => normPower (GeneralLinearGroup.det argument) (-(((degree : ℂ) + 3) / 2)) •
    source vertices (planeLevi argument 1 * base), by
    apply (ternaryCuspidalTensorValues_iff data.cusp degree _).mpr
    intro monomial
    have member := (cocycle.1 vertices monomial).2.2.2.2.2 base
    have exponent : (((degree : ℂ) + 3) / 2 + inductionExponent .plane cohomologicalPoint) =
        ((degree : ℂ) + 3) / 2 := binaryInductionExponent_plane_endpoint degree
    simpa only [exponent, Submodule.coe_smul, coeff_smul, smul_eq_mul] using member⟩

theorem sourcePlaneCuspidalValues_apply {degree : ℕ} (data : InducingData degree) (source : SourceCochain degree)
    (cocycle : IsSourceCocycle data .plane source) (vertices : Fin 3 → RealGL3) (base : AdelicGL)
    (argument : BinaryAdelicGL) :
    (sourcePlaneCuspidalValues data source cocycle vertices base).val argument =
      normPower (GeneralLinearGroup.det argument) (-(((degree : ℂ) + 3) / 2)) •
        source vertices (planeLevi argument 1 * base) := rfl

theorem sourcePlaneCuspidalValues_identity {degree : ℕ} (data : InducingData degree) (source : SourceCochain degree)
    (cocycle : IsSourceCocycle data .plane source) (vertices : Fin 3 → RealGL3) (base : AdelicGL) :
    (sourcePlaneCuspidalValues data source cocycle vertices base).val 1 = source vertices base := by
  rw [sourcePlaneCuspidalValues_apply, map_one, normPower_one, one_smul,
    show planeLevi (1 : BinaryAdelicGL) 1 = 1 from (planeLeviHom Adeles).map_one, one_mul]

theorem sourcePlane_radical_invariant {degree : ℕ} (data : InducingData degree) (source : SourceCochain degree)
    (cocycle : IsSourceCocycle data .plane source) (vertices : Fin 3 → RealGL3)
    (first second : Adeles) (base : AdelicGL) :
    source vertices (planeUnipotent first second * base) = source vertices base := by
  apply Subtype.ext
  apply MvPolynomial.ext
  intro monomial
  exact (cocycle.1 vertices monomial).2.2.2.1 first second base

end TernaryPeriodPolynomials.SphericalDetection.Helpers
