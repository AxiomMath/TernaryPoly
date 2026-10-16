module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Source.NormalizedRadical
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.PlaneLevelRadicalPrimitive

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem realRadicalAxisCoordinates_contDiff_top (coordinate : Fin 2) :
    ContDiff ℝ ⊤ (fun parameter => (realRadicalAxis coordinate parameter).toAdd) := by
  classical
  change ContDiff ℝ ⊤ (fun parameter : ℝ => (Pi.single coordinate parameter : Fin 2 → ℝ))
  apply contDiff_pi.mpr
  intro position
  fin_cases coordinate <;> fin_cases position <;> simp <;> fun_prop

theorem sourcePlaneNormalizedGroupCocycle_axis_orbital_analyticAt {degree : ℕ} {index : Type} [Fintype index]
    (data : InducingData degree) (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source) (coordinate : Fin 2) (first : ℝ) :
    AnalyticAt ℝ (fun point : (BinaryRealMatrix × ℝ) × ℝ =>
      binaryHilbertTranslation data.cusp (atInfinity (invertibleMatrix point.1.1))
        (cuspidalTensorHilbertEmbedding data.cusp basis
          (sourcePlaneNormalizedGroupCocycle data source cocycle
            (SemidirectProduct.inl (realRadicalAxis coordinate point.1.2),
              SemidirectProduct.inl (realRadicalAxis coordinate point.2))).val)) ((1, first), 0) := by
  have axis_regular (point : ℝ) : AnalyticAt ℝ (fun parameter => (realRadicalAxis coordinate parameter).toAdd) point :=
    (realRadicalAxisCoordinates_contDiff_top coordinate).contDiffAt.analyticAt
  have input_regular : AnalyticAt ℝ
      (fun point : (BinaryRealMatrix × ℝ) × ℝ =>
        (point.1.1, ((realRadicalAxis coordinate point.1.2).toAdd, (realRadicalAxis coordinate point.2).toAdd))) ((1, first), 0) :=
    (analyticAt_fst.comp analyticAt_fst).prod
      (((axis_regular first).comp (x := ((1, first), 0)) (f := fun point : (BinaryRealMatrix × ℝ) × ℝ => point.1.2)
        (analyticAt_snd.comp analyticAt_fst)).prod
        ((axis_regular 0).comp (x := ((1, first), 0)) (f := fun point : (BinaryRealMatrix × ℝ) × ℝ => point.2) analyticAt_snd))
  have composed := (sourcePlaneNormalizedGroupCocycle_radical_orbital_analyticAt data basis source cocycle
    ((realRadicalAxis coordinate first).toAdd, (realRadicalAxis coordinate 0).toAdd)).comp
    (f := fun point : (BinaryRealMatrix × ℝ) × ℝ =>
      (point.1.1, ((realRadicalAxis coordinate point.1.2).toAdd, (realRadicalAxis coordinate point.2).toAdd))) input_regular
  convert composed using 1
  rfl

theorem sourcePlaneNormalizedGroupCocycle_exists_radical_primitive {degree : ℕ} {index : Type} [Fintype index]
    (positive : 0 < degree) (odd : Odd degree) (data : InducingData degree) (trivial : data.chi = trivialCharacter)
    (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source) :
    ∃ primitive : RealPlaneRadical → cuspidalTensorValues data.cusp (HomogeneousPoly degree),
      (∀ element, primitive element ∈ cuspidalTensorFiniteLevel data.cusp (HomogeneousPoly degree)) ∧
      ContDiff ℝ (↑(⊤ : ℕ∞)) (fun point : Fin 2 → ℝ =>
        cuspidalTensorHilbertEmbedding data.cusp basis (primitive (Multiplicative.ofAdd point))) ∧
      ∀ first second,
        cuspidalTensorMap (V := HomogeneousPoly degree) (W := HomogeneousPoly degree) data.cusp
          ((realUpperRadicalRep degree).ρ first) (primitive second) - primitive (first * second) + primitive first =
            (sourcePlaneNormalizedGroupCocycle data source cocycle (SemidirectProduct.inl first, SemidirectProduct.inl second)).val := by
  apply realPlaneLevelTwoCocycle_exists_radical_primitive_of_trivial degree positive odd data.cusp data.chi trivial basis
    (sourcePlaneNormalizedGroupCocycle data source cocycle) (sourcePlaneNormalizedGroupCocycle_unit data source cocycle)
  · exact (sourcePlaneNormalizedGroupCocycle_radical_hilbertContDiff data basis source cocycle).of_le le_top
  · exact sourcePlaneNormalizedGroupCocycle_axis_orbital_analyticAt data basis source cocycle

end TernaryPeriodPolynomials.SphericalDetection.Helpers
