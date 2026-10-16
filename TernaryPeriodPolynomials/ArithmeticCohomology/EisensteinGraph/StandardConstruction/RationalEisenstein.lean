module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.SourceSpace

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.RationalEisenstein

theorem induced_planeRational_invariant {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ)
    (induced : IsInduced data .plane parameter function)
    (element : RationalGL3) (membership : element ∈ planeParabolic ℚ)
    (argument : AdelicGL) : function (rationalGroup element * argument) =
      function argument := by
  have adelicDecomposition : rationalGroup element =
      planeUnipotent (rationalAdele (element.val 0 2 / element.val 2 2))
        (rationalAdele (element.val 1 2 / element.val 2 2)) *
      planeLevi (GeneralLinearGroup.map rationalAdele
        (PlaneDecomposition.binaryLeviBlock element membership))
        (Units.map rationalAdele (PlaneDecomposition.rankOneBlock element membership)) := by
    conv_lhs => rw [PlaneDecomposition.plane_decomposition element membership]
    rw [map_mul]
    exact congrArg₂ (fun first second : AdelicGL => first * second)
      (PlaneDecomposition.map_planeUnipotent rationalAdele _ _)
      (PlaneDecomposition.map_planeLevi rationalAdele _ _)
  rw [adelicDecomposition, mul_assoc, induced.2.2.2.1]
  have leviSplit : planeLevi
      (GeneralLinearGroup.map rationalAdele
        (PlaneDecomposition.binaryLeviBlock element membership))
      (Units.map rationalAdele (PlaneDecomposition.rankOneBlock element membership)) =
      planeLevi (GeneralLinearGroup.map rationalAdele
        (PlaneDecomposition.binaryLeviBlock element membership)) 1 *
      planeLevi 1 (Units.map rationalAdele
        (PlaneDecomposition.rankOneBlock element membership)) := by
    simpa only [Prod.mk_mul_mk, mul_one, one_mul, planeLeviHom,
      MonoidHom.coe_mk, OneHom.coe_mk] using
      (planeLeviHom Adeles).map_mul
        (GeneralLinearGroup.map rationalAdele
          (PlaneDecomposition.binaryLeviBlock element membership), 1)
        (1, Units.map rationalAdele (PlaneDecomposition.rankOneBlock element membership))
  have binaryNorm : adeleNorm (GeneralLinearGroup.det
      (GeneralLinearGroup.map rationalAdele
        (PlaneDecomposition.binaryLeviBlock element membership))) = 1 := by
    rw [GeneralLinearGroup.map_det]
    exact RationalNorm.rational_norm _
  rw [leviSplit, mul_assoc]
  have binaryInvariant :=
    ParabolicInvariance.induced_binaryRational_norm_one data .plane parameter function
      induced (PlaneDecomposition.binaryLeviBlock element membership) binaryNorm
  simp only [binaryLevi] at binaryInvariant
  rw [binaryInvariant, induced.2.2.2.2.1, data.chi.rational]
  simp [normPower, RationalNorm.rational_norm]

theorem inverseRepresentative_eq {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ)
    (induced : IsInduced data .plane parameter function)
    (first second : RationalGL3) (related : first⁻¹ * second ∈ planeParabolic ℚ)
    (argument : AdelicGL) :
    function (rationalGroup first⁻¹ * argument) =
      function (rationalGroup second⁻¹ * argument) := by
  have inverseRelated : (first⁻¹ * second)⁻¹ ∈ planeParabolic ℚ :=
    (planeParabolic ℚ).inv_mem related
  have invariant := induced_planeRational_invariant data parameter function induced
    ((first⁻¹ * second)⁻¹) inverseRelated (rationalGroup first⁻¹ * argument)
  have argumentEquality :
      rationalGroup ((first⁻¹ * second)⁻¹) * (rationalGroup first⁻¹ * argument) =
      rationalGroup second⁻¹ * argument := by
    rw [← mul_assoc, ← map_mul, _root_.mul_inv_rev, inv_inv, mul_assoc,
      mul_inv_cancel, mul_one]
  rw [argumentEquality] at invariant
  exact invariant.symm

theorem eisensteinSummand_mk {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (parameter : ℂ)
    (induced : IsInduced data .plane parameter (extension parameter))
    (argument : AdelicGL) (representative : RationalGL3) :
    eisensteinSummand extension parameter argument (QuotientGroup.mk representative) =
      extension parameter (rationalGroup representative⁻¹ * argument) := by
  let flag : Flags .plane := QuotientGroup.mk representative
  have related : flag.out⁻¹ * representative ∈ planeParabolic ℚ := by
    apply QuotientGroup.eq.mp
    exact Quotient.out_eq flag
  exact inverseRepresentative_eq data parameter (extension parameter) induced
    flag.out representative related argument

theorem eisensteinSummand_rational {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (parameter : ℂ)
    (induced : IsInduced data .plane parameter (extension parameter))
    (element : RationalGL3) (argument : AdelicGL) (flag : Flags .plane) :
    eisensteinSummand extension parameter (rationalGroup element * argument) flag =
      eisensteinSummand extension parameter argument (element⁻¹ • flag) := by
  induction flag using Quotient.inductionOn with
  | h representative =>
    change eisensteinSummand extension parameter (rationalGroup element * argument)
        (QuotientGroup.mk representative) =
      eisensteinSummand extension parameter argument
        (QuotientGroup.mk (element⁻¹ * representative))
    rw [eisensteinSummand_mk data extension parameter induced,
      eisensteinSummand_mk data extension parameter induced,
      _root_.mul_inv_rev, inv_inv, map_mul, mul_assoc]

theorem continuation_rational {degree : ℕ} (data : InducingData degree)
    (extension continuation : ℂ → AdelicGL → ℂ)
    (flat : IsFlatSection data extension)
    (continues : IsEisensteinContinuation extension continuation)
    (point : ℂ)
    (regular : ∀ argument, AnalyticAt ℂ
      (fun parameter => continuation parameter argument) point)
    (element : RationalGL3) (argument : AdelicGL) :
    continuation point (rationalGroup element * argument) = continuation point argument := by
  obtain ⟨threshold, sums⟩ := continues.2
  apply ContinuationUniqueness.meromorphic_halfPlane_unique
    (fun parameter => continuation parameter (rationalGroup element * argument))
    (fun parameter => continuation parameter argument)
    (continues.1 (rationalGroup element * argument)) (continues.1 argument)
    threshold _ point (regular (rationalGroup element * argument)) (regular argument)
  intro parameter membership
  have reindexed : HasSum
      (fun flag : Flags .plane => eisensteinSummand extension parameter argument
        (element⁻¹ • flag)) (continuation parameter argument) := by
    simpa only [Function.comp_def, MulAction.toPerm_apply] using
      ((MulAction.toPerm element⁻¹).hasSum_iff.mpr (sums parameter membership argument))
  have shifted : HasSum
      (eisensteinSummand extension parameter (rationalGroup element * argument))
      (continuation parameter argument) := by
    exact reindexed.congr_fun (fun flag =>
      eisensteinSummand_rational data extension parameter (flat.1 parameter)
        element argument flag)
  exact (sums parameter membership (rationalGroup element * argument)).unique shifted

theorem eisensteinValue_rational {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data)
    (extension : EisensteinValue.flatFamilies data) (element : RationalGL3)
    (argument : AdelicGL) :
    EisensteinValue.eisensteinValue data holomorphic extension
        (rationalGroup element * argument) =
      EisensteinValue.eisensteinValue data holomorphic extension argument := by
  have continuationSpec := EisensteinValue.chosenContinuation_spec data holomorphic extension
  exact continuation_rational data extension.val
    (EisensteinValue.chosenContinuation data holomorphic extension) extension.property
    continuationSpec.1 cohomologicalPoint continuationSpec.2 element argument

theorem continuation_finite {degree : ℕ} (data : InducingData degree)
    (extension continuation : ℂ → AdelicGL → ℂ)
    (flat : IsFlatSection data extension)
    (continues : IsEisensteinContinuation extension continuation)
    (point : ℂ)
    (regular : ∀ argument, AnalyticAt ℂ
      (fun parameter => continuation parameter argument) point)
    (levelElement : finiteLevel) (argument : AdelicGL) :
    continuation point (argument * atFinite levelElement.val) =
      continuation point argument := by
  obtain ⟨threshold, sums⟩ := continues.2
  apply ContinuationUniqueness.meromorphic_halfPlane_unique
    (fun parameter => continuation parameter (argument * atFinite levelElement.val))
    (fun parameter => continuation parameter argument)
    (continues.1 (argument * atFinite levelElement.val)) (continues.1 argument)
    threshold _ point (regular (argument * atFinite levelElement.val)) (regular argument)
  intro parameter membership
  have shifted : HasSum
      (eisensteinSummand extension parameter (argument * atFinite levelElement.val))
      (continuation parameter argument) := by
    apply (sums parameter membership argument).congr_fun
    intro flag
    change extension parameter
        (rationalGroup flag.out⁻¹ * (argument * atFinite levelElement.val)) =
      extension parameter (rationalGroup flag.out⁻¹ * argument)
    rw [← mul_assoc, (flat.1 parameter).2.1 levelElement]
  exact (sums parameter membership (argument * atFinite levelElement.val)).unique shifted

theorem eisensteinValue_finite {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data)
    (extension : EisensteinValue.flatFamilies data) (levelElement : finiteLevel)
    (argument : AdelicGL) :
    EisensteinValue.eisensteinValue data holomorphic extension
        (argument * atFinite levelElement.val) =
      EisensteinValue.eisensteinValue data holomorphic extension argument := by
  have continuationSpec := EisensteinValue.chosenContinuation_spec data holomorphic extension
  exact continuation_finite data extension.val
    (EisensteinValue.chosenContinuation data holomorphic extension) extension.property
    continuationSpec.1 cohomologicalPoint continuationSpec.2 levelElement argument

def automorphicFunctions : Submodule ℂ (AdelicGL → ℂ) where
  carrier := {function |
    (∀ element : RationalGL3, ∀ argument,
      function (rationalGroup element * argument) = function argument) ∧
    (∀ levelElement : finiteLevel, ∀ argument,
      function (argument * atFinite levelElement.val) = function argument)}
  zero_mem' := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  add_mem' {first second} firstAutomorphic secondAutomorphic := by
    constructor
    · intro element argument
      change first _ + second _ = first _ + second _
      rw [firstAutomorphic.1, secondAutomorphic.1]
    · intro levelElement argument
      change first _ + second _ = first _ + second _
      rw [firstAutomorphic.2, secondAutomorphic.2]
  smul_mem' scalar function automorphic := by
    constructor
    · intro element argument
      change scalar • function _ = scalar • function _
      rw [automorphic.1]
    · intro levelElement argument
      change scalar • function _ = scalar • function _
      rw [automorphic.2]

def automorphicEisensteinValue {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data) :
    EisensteinValue.flatFamilies data →ₗ[ℂ] automorphicFunctions :=
  (EisensteinValue.eisensteinValue data holomorphic).codRestrict automorphicFunctions
    (fun extension => ⟨eisensteinValue_rational data holomorphic extension,
      eisensteinValue_finite data holomorphic extension⟩)

theorem source_automorphicContinuation {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data)
    (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (isSource : IsSourceCocycle data .plane source) :
    ∃ extension continuation :
        ℂ → (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree,
      (∀ vertices monomial, IsFlatSection data
        (fun parameter argument => (extension parameter vertices argument).val.coeff monomial)) ∧
      extension cohomologicalPoint = source ∧
      (∀ vertices monomial, IsEisensteinContinuation
        (fun parameter argument => (extension parameter vertices argument).val.coeff monomial)
        (fun parameter argument => (continuation parameter vertices argument).val.coeff monomial)) ∧
      (∀ vertices argument monomial, AnalyticAt ℂ
        (fun parameter => (continuation parameter vertices argument).val.coeff monomial) cohomologicalPoint) ∧
      (∀ vertices element argument,
        continuation cohomologicalPoint vertices (rationalGroup element * argument) =
          continuation cohomologicalPoint vertices argument) ∧
      (∀ vertices, ∀ levelElement : finiteLevel, ∀ argument,
        continuation cohomologicalPoint vertices (argument * atFinite levelElement.val) =
          continuation cohomologicalPoint vertices argument) := by
  obtain ⟨extension, continuation, flat, realizes, continues, regular⟩ :=
    FlatExtensions.source_eisensteinContinuation data holomorphic source isSource
  refine ⟨extension, continuation, flat, realizes, continues, regular, ?_, ?_⟩
  · intro vertices element argument
    apply Subtype.ext
    apply MvPolynomial.ext
    intro monomial
    exact continuation_rational data _ _ (flat vertices monomial)
      (continues vertices monomial) cohomologicalPoint
      (fun argument => regular vertices argument monomial) element argument
  · intro vertices levelElement argument
    apply Subtype.ext
    apply MvPolynomial.ext
    intro monomial
    exact continuation_finite data _ _ (flat vertices monomial)
      (continues vertices monomial) cohomologicalPoint
      (fun argument => regular vertices argument monomial) levelElement argument

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.RationalEisenstein
