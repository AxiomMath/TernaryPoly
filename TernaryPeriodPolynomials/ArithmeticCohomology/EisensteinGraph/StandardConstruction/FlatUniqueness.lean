module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Adelic.Decomposition
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.SectionSpace

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.FlatUniqueness

theorem normPower_ne_zero (unit : Adelesˣ) (parameter : ℂ) :
    normPower unit parameter ≠ 0 := Complex.exp_ne_zero _

theorem planeLevi_split (binary : BinaryAdelicGL) (unit : Adelesˣ) :
    planeLevi binary unit = planeLevi 1 unit * planeLevi binary 1 := by
  simpa only [Prod.mk_mul_mk, mul_one, one_mul, planeLeviHom,
    MonoidHom.coe_mk, OneHom.coe_mk] using
    (planeLeviHom Adeles).map_mul (1, unit) (binary, 1)

theorem flat_unique {degree : ℕ} (data : InducingData degree)
    (first second : ℂ → AdelicGL → ℂ)
    (firstFlat : IsFlatSection data first) (secondFlat : IsFlatSection data second)
    (sameEndpoint : first cohomologicalPoint = second cohomologicalPoint) : first = second := by
  funext parameter argument
  obtain ⟨a, b, binary, unit, compact, compactMembership, decomposition⟩ :=
    AdelicDecomposition.adelic_planeDecomposition argument
  have compactEquality : first parameter (planeLevi binary 1 * compact) =
      second parameter (planeLevi binary 1 * compact) := by
    apply mul_left_cancel₀ (normPower_ne_zero (GeneralLinearGroup.det binary)
      (-binaryInductionExponent degree .plane parameter))
    rw [firstFlat.2.2 parameter binary compact compactMembership,
      secondFlat.2.2 parameter binary compact compactMembership, sameEndpoint]
  rw [decomposition, mul_assoc, (firstFlat.1 parameter).2.2.2.1,
    (secondFlat.1 parameter).2.2.2.1, planeLevi_split, mul_assoc,
    (firstFlat.1 parameter).2.2.2.2.1, (secondFlat.1 parameter).2.2.2.2.1,
    compactEquality]

theorem flat_sub {degree : ℕ} (data : InducingData degree)
    (first second : ℂ → AdelicGL → ℂ)
    (firstFlat : IsFlatSection data first) (secondFlat : IsFlatSection data second) :
    IsFlatSection data (fun parameter argument =>
      first parameter argument - second parameter argument) := by
  simpa only [neg_one_mul, sub_eq_add_neg] using
    LinearFamilies.flat_add data first (fun parameter argument => -1 * second parameter argument)
      firstFlat (LinearFamilies.flat_smul data (-1) second secondFlat)

theorem flat_fourTerm {degree : ℕ} (data : InducingData degree)
    (extension : Fin 4 → ℂ → AdelicGL → ℂ)
    (flat : ∀ index, IsFlatSection data (extension index))
    (closed : ∀ argument,
      extension 0 cohomologicalPoint argument - extension 1 cohomologicalPoint argument +
        extension 2 cohomologicalPoint argument - extension 3 cohomologicalPoint argument = 0)
    (parameter : ℂ) (argument : AdelicGL) :
    extension 0 parameter argument - extension 1 parameter argument +
      extension 2 parameter argument - extension 3 parameter argument = 0 := by
  have combined := flat_sub data _ _
    (LinearFamilies.flat_add data _ _
      (flat_sub data _ _ (flat 0) (flat 1)) (flat 2)) (flat 3)
  have equality := flat_unique data _ (fun _ _ => 0) combined (FlatExtensions.flat_zero data)
    (by funext argument; exact closed argument)
  exact congrFun (congrFun equality parameter) argument

theorem endpointEvaluation_injective {degree : ℕ} (data : InducingData degree) :
    Function.Injective (SectionSpace.endpointEvaluation data) := by
  intro first second sameEndpoint
  apply Subtype.ext
  exact flat_unique data first.val second.val first.property second.property
    (congrArg Subtype.val sameEndpoint)

theorem endpointEvaluation_bijective {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data) :
    Function.Bijective (SectionSpace.endpointEvaluation data) :=
  ⟨endpointEvaluation_injective data,
    SectionSpace.endpointEvaluation_surjective data holomorphic⟩

def flatFamilyEquiv {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data) :
    EisensteinValue.flatFamilies data ≃ₗ[ℂ]
      SectionSpace.inducedSections data .plane cohomologicalPoint :=
  LinearEquiv.ofBijective (SectionSpace.endpointEvaluation data)
    (endpointEvaluation_bijective data holomorphic)

theorem linearFlatExtension_unique {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data)
    (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint)
    (extension : EisensteinValue.flatFamilies data)
    (endpoint : extension.val cohomologicalPoint = sectionValue.val) :
    SectionSpace.linearFlatExtension data holomorphic sectionValue = extension := by
  apply Subtype.ext
  exact flat_unique data _ _
    (SectionSpace.linearFlatExtension data holomorphic sectionValue).property
    extension.property
    ((SectionSpace.linearFlatExtension_endpoint data holomorphic sectionValue).trans endpoint.symm)

theorem sectionEisensteinValue_anyExtension {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data)
    (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint)
    (extension : EisensteinValue.flatFamilies data)
    (endpoint : extension.val cohomologicalPoint = sectionValue.val)
    (continuation : ℂ → AdelicGL → ℂ)
    (continues : IsEisensteinContinuation extension.val continuation)
    (regular : ∀ argument, AnalyticAt ℂ
      (fun parameter => continuation parameter argument) cohomologicalPoint) :
    (SectionSpace.sectionEisensteinValue data holomorphic sectionValue).val =
      continuation cohomologicalPoint := by
  change EisensteinValue.eisensteinValue data holomorphic
    (SectionSpace.linearFlatExtension data holomorphic sectionValue) = _
  rw [linearFlatExtension_unique data holomorphic sectionValue extension endpoint]
  exact EisensteinValue.eisensteinValue_realizes data holomorphic extension continuation
    continues regular

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.FlatUniqueness
