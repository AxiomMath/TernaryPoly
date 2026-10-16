module

public import TernaryPeriodPolynomials.Building.GoodApartmentFunctional.Relations

@[expose] public section


open GeneralEisenstein
open Homogeneous Adelic Matrix
open TernaryPeriodPolynomials.GoodApartmentFunctional.Helpers

namespace TernaryPeriodPolynomials.GoodApartmentFunctional.Descent

noncomputable section

theorem rationalCoefficient_integral {degree : ℕ} (frame : IntegralGL3)
    (polynomial : HomogeneousPoly degree) :
    rationalCoefficientComponent degree trivialCharacter
        (GeneralLinearGroup.map (Int.castRingHom ℚ) frame) polynomial =
      homogeneousAction degree (-1)
        (GeneralLinearGroup.map (Int.castRingHom ℂ) frame) polynomial := by
  have castComposition :
      GeneralLinearGroup.map (algebraMap ℝ ℂ)
          (GeneralLinearGroup.map (algebraMap ℚ ℝ)
            (GeneralLinearGroup.map (Int.castRingHom ℚ) frame)) =
        GeneralLinearGroup.map (Int.castRingHom ℂ) frame := by
    apply Units.ext
    ext row column
    simp
  change componentCharacter trivialCharacter _ •
    homogeneousAction degree (-1) _ polynomial = _
  have character : ∀ realFrame : RealGL3,
      componentCharacter trivialCharacter realFrame = 1 := by
    intro realFrame
    rfl
  rw [character, one_smul, castComposition]

theorem extend_equivariant_functional {degree : ℕ} (polynomial : HomogeneousPoly degree)
    (functional : goodCycles →ₗ[ℂ] HomogeneousPoly degree)
    (equivariance : ∀ groupElement : rationalLevel, ∀ chain : goodCycles,
      functional (goodCycleAction groupElement chain) =
        rationalCoefficientComponent degree trivialCharacter groupElement.val (functional chain))
    (evaluation : ∀ frame : NormalizedFrames,
      functional (normalizedApartment frame) = normalizedFrameEvaluation polynomial frame) :
    ∃ extension : EdgeChains →ₗ[ℂ] HomogeneousPoly degree,
      IsPolynomialFunctional polynomial extension := by
  obtain ⟨extension, agreement⟩ := extend_goodCycles functional
  refine ⟨extension, ?_, ?_⟩
  · intro groupElement chain good
    let cycle : goodCycles := ⟨chain, (mem_goodCycles chain).mpr good⟩
    have translated : (goodCycleAction groupElement cycle).val =
        translateChain groupElement.val chain := rfl
    rw [← translated, agreement, equivariance, ← agreement]
  · intro frame normalized
    let normalizedFrame : NormalizedFrames := ⟨frame, normalized⟩
    have equality := agreement (normalizedApartment normalizedFrame)
    rw [evaluation] at equality
    exact congrArg Subtype.val equality |>.trans
      (normalizedFrameEvaluation_coe polynomial normalizedFrame)

def factorThroughSurjection {source target values : Type*}
    [AddCommGroup source] [Module ℂ source]
    [AddCommGroup target] [Module ℂ target]
    [AddCommGroup values] [Module ℂ values]
    (projection : source →ₗ[ℂ] target) (evaluation : source →ₗ[ℂ] values)
    (surjective : Function.Surjective projection)
    (relations : projection.ker ≤ evaluation.ker) : target →ₗ[ℂ] values :=
  (projection.ker.liftQ evaluation relations).comp
    (projection.quotKerEquivOfSurjective surjective).symm.toLinearMap

theorem factorThroughSurjection_apply {source target values : Type*}
    [AddCommGroup source] [Module ℂ source]
    [AddCommGroup target] [Module ℂ target]
    [AddCommGroup values] [Module ℂ values]
    (projection : source →ₗ[ℂ] target) (evaluation : source →ₗ[ℂ] values)
    (surjective : Function.Surjective projection)
    (relations : projection.ker ≤ evaluation.ker) (element : source) :
    factorThroughSurjection projection evaluation surjective relations
        (projection element) = evaluation element := by
  simp [factorThroughSurjection]

def descendedFrameEvaluation {degree : ℕ} (polynomial : HomogeneousPoly degree)
    (surjective : Function.Surjective apartmentPresentation)
    (relations : apartmentPresentation.ker ≤ (frameEvaluation polynomial).ker) :
    goodCycles →ₗ[ℂ] HomogeneousPoly degree :=
  factorThroughSurjection (source := NormalizedFrames →₀ ℂ) (target := goodCycles)
    (values := HomogeneousPoly degree) apartmentPresentation (frameEvaluation polynomial)
    surjective relations

theorem descendedFrameEvaluation_apply {degree : ℕ} (polynomial : HomogeneousPoly degree)
    (surjective : Function.Surjective apartmentPresentation)
    (relations : apartmentPresentation.ker ≤ (frameEvaluation polynomial).ker)
    (combination : NormalizedFrames →₀ ℂ) :
    descendedFrameEvaluation polynomial surjective relations
        (apartmentPresentation combination) = frameEvaluation polynomial combination := by
  simp only [descendedFrameEvaluation, factorThroughSurjection, LinearMap.comp_apply,
    LinearEquiv.coe_coe]
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply (R := ℂ)
    (M := NormalizedFrames →₀ ℂ) (M₂ := goodCycles)
    apartmentPresentation surjective combination]
  rfl

theorem descendedFrameEvaluation_frame {degree : ℕ} (polynomial : HomogeneousPoly degree)
    (surjective : Function.Surjective apartmentPresentation)
    (relations : apartmentPresentation.ker ≤ (frameEvaluation polynomial).ker)
    (frame : NormalizedFrames) :
    descendedFrameEvaluation polynomial surjective relations (normalizedApartment frame) =
      normalizedFrameEvaluation polynomial frame := by
  simpa [apartmentPresentation, frameEvaluation] using
    descendedFrameEvaluation_apply polynomial surjective relations (Finsupp.single frame 1)

def translateFrameCombinations (groupElement : arithmeticLevel) :
    (NormalizedFrames →₀ ℂ) →ₗ[ℂ] (NormalizedFrames →₀ ℂ) :=
  Finsupp.lmapDomain ℂ ℂ (translateNormalizedFrame groupElement)

theorem apartmentPresentation_translate (groupElement : arithmeticLevel)
    (combination : NormalizedFrames →₀ ℂ) :
    apartmentPresentation (translateFrameCombinations groupElement combination) =
      goodCycleAction ⟨rationalInclusion groupElement,
        MonoidHom.mem_range.mpr ⟨groupElement, rfl⟩⟩ (apartmentPresentation combination) := by
  have equality : apartmentPresentation.comp (translateFrameCombinations groupElement) =
      (goodCycleAction ⟨rationalInclusion groupElement,
        MonoidHom.mem_range.mpr ⟨groupElement, rfl⟩⟩).comp apartmentPresentation := by
    apply Finsupp.lhom_ext
    intro frame coefficient
    simp only [LinearMap.comp_apply, translateFrameCombinations, Finsupp.lmapDomain_apply,
      Finsupp.mapDomain_single, apartmentPresentation, Finsupp.linearCombination_single,
      map_smul]
    congr 1
    apply Subtype.ext
    exact normalizedApartment_translate groupElement frame
  exact LinearMap.congr_fun equality combination

theorem frameEvaluation_translate {degree : ℕ} (polynomial : HomogeneousPoly degree)
    (groupElement : arithmeticLevel) (combination : NormalizedFrames →₀ ℂ) :
    frameEvaluation polynomial (translateFrameCombinations groupElement combination) =
      rationalCoefficientComponent degree trivialCharacter (rationalInclusion groupElement)
        (frameEvaluation polynomial combination) := by
  have equality : (frameEvaluation polynomial).comp (translateFrameCombinations groupElement) =
      (rationalCoefficientComponent degree trivialCharacter (rationalInclusion groupElement)).comp
        (frameEvaluation polynomial) := by
    apply Finsupp.lhom_ext
    intro frame coefficient
    simp only [LinearMap.comp_apply, translateFrameCombinations, Finsupp.lmapDomain_apply,
      Finsupp.mapDomain_single, frameEvaluation, Finsupp.linearCombination_single, map_smul]
    congr 1
    rw [normalizedFrameEvaluation_translate]
    exact (rationalCoefficient_integral groupElement.val _).symm
  exact LinearMap.congr_fun equality combination

theorem functional_of_presentation {degree : ℕ} (polynomial : HomogeneousPoly degree)
    (surjective : Function.Surjective apartmentPresentation)
    (relations : apartmentPresentation.ker ≤ (frameEvaluation polynomial).ker) :
    ∃ extension : EdgeChains →ₗ[ℂ] HomogeneousPoly degree,
      IsPolynomialFunctional polynomial extension := by
  apply extend_equivariant_functional polynomial
    (descendedFrameEvaluation polynomial surjective relations)
  · intro groupElement chain
    obtain ⟨integral, equality⟩ := MonoidHom.mem_range.mp groupElement.property
    have groupEquality : groupElement =
        ⟨rationalInclusion integral, MonoidHom.mem_range.mpr ⟨integral, rfl⟩⟩ := by
      apply Subtype.ext
      exact equality.symm
    subst groupElement
    obtain ⟨combination, rfl⟩ := surjective chain
    rw [← apartmentPresentation_translate, descendedFrameEvaluation_apply,
      frameEvaluation_translate, descendedFrameEvaluation_apply]
  · exact descendedFrameEvaluation_frame polynomial surjective relations

theorem presentation_compatibility_of_functional {degree : ℕ}
    (polynomial : HomogeneousPoly degree)
    (extension : EdgeChains →ₗ[ℂ] HomogeneousPoly degree)
    (functional : IsPolynomialFunctional polynomial extension) :
    apartmentPresentation.ker ≤ (frameEvaluation polynomial).ker := by
  have equality : extension.comp (goodCycles.subtype.comp apartmentPresentation) =
      frameEvaluation polynomial := by
    apply Finsupp.lhom_ext
    intro frame coefficient
    simp only [LinearMap.comp_apply, apartmentPresentation, frameEvaluation,
      Finsupp.linearCombination_single, map_smul]
    congr 1
    apply Subtype.ext
    exact (functional.2 frame.val frame.property).trans
      (normalizedFrameEvaluation_coe polynomial frame).symm
  intro combination membership
  have zero : apartmentPresentation combination = 0 := membership
  change frameEvaluation polynomial combination = 0
  rw [← equality, LinearMap.comp_apply, LinearMap.comp_apply, zero, map_zero, map_zero]

theorem equivariantFunctional_on_goodCycles_iff {degree : ℕ}
    (polynomial : HomogeneousPoly degree) :
    (∃ extension : EdgeChains →ₗ[ℂ] HomogeneousPoly degree,
      IsPolynomialFunctional polynomial extension) ↔
    ∃ functional : goodCycles →ₗ[ℂ] HomogeneousPoly degree,
      (∀ groupElement : rationalLevel, ∀ chain : goodCycles,
        functional (goodCycleAction groupElement chain) =
          rationalCoefficientComponent degree trivialCharacter groupElement.val
            (functional chain)) ∧
      ∀ frame : NormalizedFrames,
        functional (normalizedApartment frame) = normalizedFrameEvaluation polynomial frame := by
  constructor
  · rintro ⟨extension, equivariance, evaluation⟩
    refine ⟨extension.comp goodCycles.subtype, ?_, ?_⟩
    · intro groupElement chain
      exact equivariance groupElement chain.val ((mem_goodCycles chain.val).mp chain.property)
    · intro frame
      apply Subtype.ext
      exact (evaluation frame.val frame.property).trans
        (normalizedFrameEvaluation_coe polynomial frame).symm
  · rintro ⟨functional, equivariance, evaluation⟩
    exact extend_equivariant_functional polynomial functional equivariance evaluation

end

end TernaryPeriodPolynomials.GoodApartmentFunctional.Descent
