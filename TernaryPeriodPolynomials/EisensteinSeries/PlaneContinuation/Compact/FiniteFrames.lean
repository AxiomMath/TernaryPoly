module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Finite.ProfileRegularity
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.ProfiniteClopenExtension

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealFrameChart TernaryPeriodPolynomials.PlaneEisensteinContinuation.FrameProfile TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel
open scoped Matrix.Norms.Elementwise Classical

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.CompactFiniteFrames

abbrev IntegralSpace := Rectangular IntegralAdeles
abbrev RealFrame := {frame : Rectangular ℝ // FullRank frame}

def frame (point : IntegralFiniteGL) : IntegralSpace := columns point⁻¹.val

def embedding (value : IntegralSpace) : Rectangular FiniteAdeles := value.map integralEmbedding

theorem embedding_isOpenEmbedding : Topology.IsOpenEmbedding embedding :=
  Topology.IsOpenEmbedding.piMap (fun _ : Fin 3 =>
    Topology.IsOpenEmbedding.piMap (fun _ : Fin 2 => integralEmbedding_isOpenEmbedding))

theorem frame_continuous : Continuous frame := by
  apply continuous_pi
  intro row
  apply continuous_pi
  intro column
  exact (continuous_apply column.castSucc).comp ((continuous_apply row).comp
    ((Units.continuous_val (M := Matrix (Fin 3) (Fin 3) IntegralAdeles)).comp
      (continuous_inv : Continuous (fun point : IntegralFiniteGL => point⁻¹))))

theorem adelicFrame_apply (point : IntegralFiniteGL) (value : Rectangular ℝ) (row : Fin 3) (column : Fin 2) :
    adelicFrame (GeneralLinearGroup.map integralEmbedding point) value row column =
      (value row column, embedding (frame point) row column) := by
  unfold adelicFrame
  rw [RectangularKernel.standard, mul_standard]
  rfl

theorem adelicFrame_eq (first second : IntegralFiniteGL) (equality : frame first = frame second) (value : Rectangular ℝ) :
    adelicFrame (GeneralLinearGroup.map integralEmbedding first) value =
      adelicFrame (GeneralLinearGroup.map integralEmbedding second) value := by
  apply Matrix.ext
  intro row column
  rw [adelicFrame_apply, adelicFrame_apply, equality]

def profileKey {degree : ℕ} {data : InducingData degree} {sectionFunction : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection data sectionFunction) (point : IntegralFiniteGL) : ℂ → RealFrame → data.cusp.smooth :=
  fun parameter value => profile (flat.1 parameter) (adelicFrame (GeneralLinearGroup.map integralEmbedding point) value.val)

theorem key_compatible {degree : ℕ} {data : InducingData degree} {sectionFunction : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection data sectionFunction) (first second : IntegralFiniteGL) (equality : frame first = frame second) :
    profileKey flat first = profileKey flat second := by
  funext parameter value
  unfold profileKey
  rw [adelicFrame_eq first second equality]

theorem key_locallyConstant {degree : ℕ} {data : InducingData degree} {sectionFunction : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection data sectionFunction) : IsLocallyConstant (profileKey flat) := by
  have result := (FiniteProfileRegularity.representative_locallyConstant data).comp (profileKey flat)
  have equality : profileKey flat = profileKey flat ∘ FiniteProfileRegularity.representative data := by
    funext point parameter value
    exact FiniteProfileRegularity.profile_eq_representative (flat.1 parameter) point value.val value.property
  rw [← equality] at result
  exact result

theorem key_finite_range {degree : ℕ} {data : InducingData degree} {sectionFunction : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection data sectionFunction) : (Set.range (profileKey flat)).Finite := by
  let _ : CompactSpace (Matrix (Fin 3) (Fin 3) IntegralAdeles) :=
    inferInstanceAs (CompactSpace (Fin 3 → Fin 3 → IntegralAdeles))
  exact (key_locallyConstant flat).range_finite

theorem fiber_extension {degree : ℕ} {data : InducingData degree} {sectionFunction : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection data sectionFunction) (key : ℂ → RealFrame → data.cusp.smooth) :
    ∃ region : Set IntegralSpace, IsClopen region ∧ ∀ point : IntegralFiniteGL,
      frame point ∈ region ↔ profileKey flat point = key := by
  let _ : CompactSpace (Matrix (Fin 3) (Fin 3) IntegralAdeles) :=
    inferInstanceAs (CompactSpace (Fin 3 → Fin 3 → IntegralAdeles))
  let _ : CompactSpace IntegralSpace := inferInstanceAs (CompactSpace (Fin 3 → Fin 2 → IntegralAdeles))
  let _ : TotallyDisconnectedSpace IntegralSpace :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin 3 → Fin 2 → IntegralAdeles))
  exact ProfiniteClopenExtension.fiber_extension frame frame_continuous (profileKey flat)
    (key_locallyConstant flat) (key_compatible flat) key

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.CompactFiniteFrames
