module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Finite.ProfileResidues
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.ProfiniteCharacter
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealFrameChart TernaryPeriodPolynomials.PlaneEisensteinContinuation.FrameProfile TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteProfileResidues
open scoped Matrix.Norms.Elementwise Classical

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteProfileRegularity

theorem atFinite_continuous : Continuous (atFinite (m := 3)) := by
  apply Units.continuous_iff.mpr
  constructor
  · change Continuous (fun value : FiniteGL => fun row column => ((1 : Matrix (Fin 3) (Fin 3) ℝ) row column, value.val row column))
    exact continuous_pi (fun row => continuous_pi (fun column => continuous_const.prodMk
      ((continuous_apply column).comp ((continuous_apply row).comp (Units.continuous_val (M := Matrix (Fin 3) (Fin 3) FiniteAdeles))))))
  · change Continuous (fun value : FiniteGL => fun row column => ((1 : Matrix (Fin 3) (Fin 3) ℝ) row column, value⁻¹.val row column))
    exact continuous_pi (fun row => continuous_pi (fun column => continuous_const.prodMk
      ((continuous_apply column).comp ((continuous_apply row).comp
        ((Units.continuous_val (M := Matrix (Fin 3) (Fin 3) FiniteAdeles)).comp
          (continuous_inv : Continuous (fun value : FiniteGL => value⁻¹)))))))

def finiteCharacter {degree : ℕ} (data : InducingData degree) : IntegralFiniteGL →* ℂ where
  toFun := character data
  map_one' := by
    simp only [character, map_one, TernaryPeriodPolynomials.PlaneEisensteinContinuation.CompactAveraging.atFinite_one]
  map_mul' first second := by
    simp only [character, map_mul, atFinite_mul]

theorem character_continuous {degree : ℕ} (data : InducingData degree) : Continuous (character data) :=
  data.chi.continuous.comp (GeneralLinearGroup.continuous_det.comp
    (atFinite_continuous.comp TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel.integralMap_continuous))

instance finiteIntegersTotallyDisconnected (place : FinitePlace) :
    TotallyDisconnectedSpace (place.adicCompletionIntegers ℚ) := by
  let _ : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  let _ : Algebra ℤ (place.adicCompletionIntegers ℚ) := Ring.toIntAlgebra _
  exact (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv place).toHomeomorph.symm.totallyDisconnectedSpace

instance integralGroupTotallyDisconnected : TotallyDisconnectedSpace IntegralFiniteGL := by
  let _ : TotallyDisconnectedSpace (Matrix (Fin 3) (Fin 3) IntegralAdeles) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin 3 → Fin 3 → IntegralAdeles))
  let _ : TotallyDisconnectedSpace (Matrix (Fin 3) (Fin 3) IntegralAdeles)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.totallyDisconnectedSpace
  exact Units.isEmbedding_embedProduct.isTotallyDisconnected_range.mp
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)

theorem character_locallyConstant {degree : ℕ} (data : InducingData degree) : IsLocallyConstant (character data) := by
  let _ : CompactSpace (Matrix (Fin 3) (Fin 3) IntegralAdeles) :=
    inferInstanceAs (CompactSpace (Fin 3 → Fin 3 → IntegralAdeles))
  let _ : TotallyDisconnectedSpace (Matrix (Fin 3) (Fin 3) IntegralAdeles) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin 3 → Fin 3 → IntegralAdeles))
  exact ProfiniteCharacter.locallyConstant (finiteCharacter data) (character_continuous data)

theorem profile_locallyConstant {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {function : AdelicGL → ℂ} (induced : IsInduced data .plane parameter function)
    (frame : Rectangular ℝ) (fullRank : FullRank frame) :
    IsLocallyConstant (fun finitePoint : IntegralFiniteGL =>
      profile induced (adelicFrame (GeneralLinearGroup.map integralEmbedding finitePoint) frame)) := by
  have result := (character_locallyConstant data).inv.comp₂ (twisted_locallyConstant induced frame fullRank)
    (fun scalar vector => scalar • vector)
  simpa only [Pi.inv_apply, smul_smul, inv_mul_cancel₀ (character_nonzero data _), one_smul] using result

theorem profile_finite_range {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {function : AdelicGL → ℂ} (induced : IsInduced data .plane parameter function)
    (frame : Rectangular ℝ) (fullRank : FullRank frame) :
    (Set.range (fun finitePoint : IntegralFiniteGL =>
      profile induced (adelicFrame (GeneralLinearGroup.map integralEmbedding finitePoint) frame))).Finite := by
  let _ : CompactSpace (Matrix (Fin 3) (Fin 3) IntegralAdeles) :=
    inferInstanceAs (CompactSpace (Fin 3 → Fin 3 → IntegralAdeles))
  exact (profile_locallyConstant induced frame fullRank).range_finite

def index {degree : ℕ} (data : InducingData degree) (finitePoint : IntegralFiniteGL) :
    GeneralLinearGroup (Fin 3) (ZMod 3) × ℂ :=
  (GeneralLinearGroup.map integralReduction finitePoint, character data finitePoint)

theorem index_locallyConstant {degree : ℕ} (data : InducingData degree) : IsLocallyConstant (index data) := by
  let _ : TopologicalSpace (ZMod 3) := ⊥
  let _ : DiscreteTopology (ZMod 3) := ⟨rfl⟩
  have reduction : IsLocallyConstant (GeneralLinearGroup.map integralReduction (n := Fin 3)) :=
    (IsLocallyConstant.iff_continuous _).mpr TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel.reductionMap_continuous
  exact reduction.comp₂ (character_locallyConstant data) Prod.mk

def representativeOfIndex {degree : ℕ} (data : InducingData degree)
    (value : GeneralLinearGroup (Fin 3) (ZMod 3) × ℂ) : IntegralFiniteGL :=
  if membership : value ∈ Set.range (index data) then membership.choose else 1

def representative {degree : ℕ} (data : InducingData degree) (finitePoint : IntegralFiniteGL) : IntegralFiniteGL :=
  representativeOfIndex data (index data finitePoint)

theorem representative_index {degree : ℕ} (data : InducingData degree) (finitePoint : IntegralFiniteGL) :
    index data (representative data finitePoint) = index data finitePoint := by
  have membership : index data finitePoint ∈ Set.range (index data) := ⟨finitePoint, rfl⟩
  simp only [representative, representativeOfIndex, dite_eq_left membership]
  exact membership.choose_spec

theorem representative_locallyConstant {degree : ℕ} (data : InducingData degree) :
    IsLocallyConstant (representative data) :=
  (index_locallyConstant data).comp (representativeOfIndex data)

theorem representative_finite_range {degree : ℕ} (data : InducingData degree) :
    (Set.range (representative data)).Finite := by
  let _ : CompactSpace (Matrix (Fin 3) (Fin 3) IntegralAdeles) :=
    inferInstanceAs (CompactSpace (Fin 3 → Fin 3 → IntegralAdeles))
  exact (representative_locallyConstant data).range_finite

theorem profile_eq_representative {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {function : AdelicGL → ℂ} (induced : IsInduced data .plane parameter function)
    (finitePoint : IntegralFiniteGL) (frame : Rectangular ℝ) (fullRank : FullRank frame) :
    profile induced (adelicFrame (GeneralLinearGroup.map integralEmbedding finitePoint) frame) =
      profile induced (adelicFrame (GeneralLinearGroup.map integralEmbedding (representative data finitePoint)) frame) := by
  have equality := representative_index data finitePoint
  have reduction : GeneralLinearGroup.map integralReduction finitePoint =
      GeneralLinearGroup.map integralReduction (representative data finitePoint) := (congrArg Prod.fst equality).symm
  have characters : character data (representative data finitePoint) = character data finitePoint := congrArg Prod.snd equality
  rw [FiniteProfileResidues.profile_eq_of_reduction induced finitePoint (representative data finitePoint) reduction frame fullRank,
    characters, inv_mul_cancel₀ (character_nonzero data finitePoint), one_smul]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteProfileRegularity
