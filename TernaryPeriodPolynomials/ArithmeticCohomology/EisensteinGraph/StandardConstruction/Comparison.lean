module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Helpers

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.Comparison

theorem integralFinite_integralMap (integralMatrix : IntegralGL3) :
    integralFinite integralMatrix =
      Matrix.GeneralLinearGroup.map integralEmbedding
        (Matrix.GeneralLinearGroup.map (Int.castRingHom IntegralAdeles) integralMatrix) := by
  apply Matrix.GeneralLinearGroup.ext
  intro row column
  change algebraMap ℚ FiniteAdeles ((integralMatrix.val row column : ℤ) : ℚ) =
    integralEmbedding ((integralMatrix.val row column : ℤ) : IntegralAdeles)
  simp

theorem rationalLevel_finiteLevel (element : rationalLevel) :
    rationalFinite element.val ∈ finiteLevel := by
  obtain ⟨integralMatrix, equality⟩ := element.property
  rw [← equality]
  change integralFinite integralMatrix.val ∈ finiteLevel
  rw [integralFinite_integralMap]
  apply Subgroup.mem_map.mpr
  refine ⟨Matrix.GeneralLinearGroup.map (Int.castRingHom IntegralAdeles)
    integralMatrix.val, ?_, rfl⟩
  change Matrix.GeneralLinearGroup.map integralReduction
    (Matrix.GeneralLinearGroup.map (Int.castRingHom IntegralAdeles) integralMatrix.val) ∈
      rowStabilizer
  have reductionEquality : Matrix.GeneralLinearGroup.map integralReduction
      (Matrix.GeneralLinearGroup.map (Int.castRingHom IntegralAdeles) integralMatrix.val) =
      reductionThree integralMatrix.val := by
    apply Matrix.GeneralLinearGroup.ext
    intro row column
    change integralReduction ((integralMatrix.val.val row column : ℤ) : IntegralAdeles) =
      ((integralMatrix.val.val row column : ℤ) : ZMod 3)
    simp
  rw [reductionEquality]
  exact integralMatrix.property

theorem rationalGroup_split (element : RationalGL3) :
    rationalGroup element =
      atInfinity (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) element) *
        atFinite (rationalFinite element) := by
  apply Matrix.GeneralLinearGroup.ext
  intro row column
  apply Prod.ext
  · change (element.val row column : ℝ) =
      ((pairMatrix (element.val.map (algebraMap ℚ ℝ)) 1 *
        pairMatrix 1 (rationalFinite element).val) row column).1
    simp [Matrix.mul_apply, pairMatrix, Matrix.one_apply, Prod.fst_sum]
  · change (rationalFinite element).val row column =
      ((pairMatrix (element.val.map (algebraMap ℚ ℝ)) 1 *
        pairMatrix 1 (rationalFinite element).val) row column).2
    simp [Matrix.mul_apply, pairMatrix, Matrix.one_apply, Prod.snd_sum]

theorem source_finiteInvariant {degree : ℕ} (data : InducingData degree) (side : Side)
    (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (isSource : IsSourceCocycle data side source) (finiteElement : finiteLevel)
    (vertices : Fin 3 → RealGL3) (argument : AdelicGL) :
    source vertices (argument * atFinite finiteElement.val) = source vertices argument := by
  apply Subtype.ext
  apply MvPolynomial.ext
  intro monomial
  exact (isSource.1 vertices monomial).2.1 finiteElement argument

def rationalEvaluation {degree : ℕ}
    (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (vertices : Fin 3 → RationalGL3) (representative : RationalGL3) : HomogeneousPoly degree :=
  source (fun index => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (vertices index))
    (rationalGroup representative⁻¹)

theorem rationalEvaluation_equivariant {degree : ℕ} (data : InducingData degree) (side : Side)
    (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (isSource : IsSourceCocycle data side source) (element : rationalLevel)
    (vertices : Fin 3 → RationalGL3) (representative : RationalGL3) :
    rationalEvaluation source (fun index => element.val * vertices index) representative =
      rationalCoefficientComponent degree data.chi element.val
        (rationalEvaluation source vertices (element.val⁻¹ * representative)) := by
  have verticesEquality :
      (fun index => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)
        (element.val * vertices index)) =
      (fun index => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) element.val *
        Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (vertices index)) := by
    funext index
    exact map_mul _ _ _
  unfold rationalEvaluation
  rw [verticesEquality, isSource.2.2.1]
  change realCoefficientComponent degree data.chi
    (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) element.val) _ =
    realCoefficientComponent degree data.chi
      (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) element.val) _
  congr 1
  rw [mul_inv_rev, inv_inv, map_mul, rationalGroup_split element.val, ← mul_assoc]
  symm
  exact source_finiteInvariant data side source isSource
    ⟨rationalFinite element.val, rationalLevel_finiteLevel element⟩ _ _

def FlagIndependent {degree : ℕ} (side : Side)
    (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree) : Prop :=
  ∀ vertices first second, first⁻¹ * second ∈ parabolic side →
    rationalEvaluation source vertices first = rationalEvaluation source vertices second

theorem evaluates_flagIndependent {degree : ℕ} (data : InducingData degree) (side : Side)
    (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (representative : cocycles rationalLevel
      (flagRepresentation (rationalCoefficientComponent degree data.chi) side))
    (evaluates : Evaluates data side source representative) : FlagIndependent side source := by
  intro vertices first second related
  have flagsEquality : (QuotientGroup.mk first : Flags side) = QuotientGroup.mk second :=
    QuotientGroup.eq.mpr related
  change rationalEvaluation source vertices first = rationalEvaluation source vertices second
  exact (evaluates vertices first).symm.trans
    ((congrArg (representative.val.val vertices) flagsEquality).trans
      (evaluates vertices second))

def evaluatedCochain {degree : ℕ} (data : InducingData degree) (side : Side)
    (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (isSource : IsSourceCocycle data side source) (independent : FlagIndependent side source) :
    cochains rationalLevel (flagRepresentation (rationalCoefficientComponent degree data.chi) side)
      2 :=
  ⟨fun vertices flag => Quotient.liftOn' flag (rationalEvaluation source vertices)
    (fun first second related => independent vertices first second
      (QuotientGroup.leftRel_apply.mp related)), by
    intro element vertices
    funext flag
    induction flag using Quotient.inductionOn with
    | h representative =>
      exact rationalEvaluation_equivariant data side source isSource element vertices representative⟩

def evaluatedCocycle {degree : ℕ} (data : InducingData degree) (side : Side)
    (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (isSource : IsSourceCocycle data side source) (independent : FlagIndependent side source) :
    cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent degree data.chi) side) :=
  ⟨evaluatedCochain data side source isSource independent, by
    funext vertices flag
    induction flag using Quotient.inductionOn with
    | h representative =>
      have tripleEquality : ∀ first second third,
          (fun index => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)
            ((![first, second, third] : Fin 3 → RationalGL3) index)) =
          ![Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) first,
            Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) second,
            Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) third] := by
        intro first second third
        funext index
        fin_cases index <;> rfl
      simpa only [differentialTwo, evaluatedCochain, Quotient.liftOn'_mk,
        rationalEvaluation, tripleEquality, LinearMap.coe_mk, AddHom.coe_mk,
        Pi.sub_apply, Pi.add_apply, Pi.zero_apply]
        using isSource.2.2.2
          (fun index => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (vertices index))
          (rationalGroup representative⁻¹)⟩

theorem evaluatedCocycle_realizes {degree : ℕ} (data : InducingData degree) (side : Side)
    (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (isSource : IsSourceCocycle data side source) (independent : FlagIndependent side source) :
    Evaluates data side source (evaluatedCocycle data side source isSource independent) := by
  intro vertices representative
  rfl

theorem sourceComparison_iff {degree : ℕ} (data : InducingData degree) :
    SourceComparisonExists data ↔
      ∀ side source, IsSourceCocycle data side source → FlagIndependent side source := by
  constructor
  · intro comparison side source isSource
    obtain ⟨representative, evaluates⟩ := comparison side source isSource
    exact evaluates_flagIndependent data side source representative evaluates
  · intro independent side source isSource
    exact ⟨evaluatedCocycle data side source isSource (independent side source isSource),
      evaluatedCocycle_realizes data side source isSource (independent side source isSource)⟩

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.Comparison
