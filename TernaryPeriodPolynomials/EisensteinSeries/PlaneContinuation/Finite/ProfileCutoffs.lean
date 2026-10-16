module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Compact.FiniteFrames
public import Mathlib.Topology.LocallyConstant.Algebra

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealFrameChart TernaryPeriodPolynomials.PlaneEisensteinContinuation.FrameProfile TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.CompactFiniteFrames
open scoped Matrix.Norms.Elementwise Classical

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteProfileCutoffs

theorem image_compact (region : Set IntegralSpace) (closed : IsClosed region) :
    IsCompact (embedding '' region) := by
  let _ : CompactSpace IntegralSpace := inferInstanceAs (CompactSpace (Fin 3 → Fin 2 → IntegralAdeles))
  exact closed.isCompact.image embedding_isOpenEmbedding.continuous

theorem image_clopen (region : Set IntegralSpace) (clopen : IsClopen region) :
    IsClopen (embedding '' region) :=
  ⟨(image_compact region clopen.isClosed).isClosed, embedding_isOpenEmbedding.isOpenMap region clopen.isOpen⟩

def indicator (region : Set IntegralSpace) (clopen : IsClopen region) : LocallyConstant (Rectangular FiniteAdeles) ℂ :=
  (LocallyConstant.const _ (1 : ℂ)).indicator (image_clopen region clopen)

theorem indicator_apply (region : Set IntegralSpace) (clopen : IsClopen region) (value : Rectangular FiniteAdeles) :
    indicator region clopen value = (embedding '' region).indicator (fun _ => (1 : ℂ)) value := rfl

theorem indicator_compactSupport (region : Set IntegralSpace) (clopen : IsClopen region) :
    HasCompactSupport (indicator region clopen : Rectangular FiniteAdeles → ℂ) := by
  apply HasCompactSupport.of_support_subset_isCompact (image_compact region clopen.isClosed)
  intro value nonzero
  by_contra outside
  exact nonzero (by rw [indicator_apply, Set.indicator_of_notMem outside])

theorem indicator_embedding (region : Set IntegralSpace) (clopen : IsClopen region) (value : IntegralSpace) :
    indicator region clopen (embedding value) = if value ∈ region then 1 else 0 := by
  have membership : embedding value ∈ embedding '' region ↔ value ∈ region := by
    constructor
    · rintro ⟨other, inside, equality⟩
      exact embedding_isOpenEmbedding.injective equality ▸ inside
    · intro inside
      exact ⟨value, inside, rfl⟩
  rw [indicator_apply]
  by_cases inside : value ∈ region
  · rw [Set.indicator_of_mem (membership.mpr inside), ite_eq_left inside]
  · rw [Set.indicator_of_notMem (fun h => inside (membership.mp h)), ite_eq_right inside]

theorem exists_cutoff {degree : ℕ} {data : InducingData degree} {sectionFunction : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection data sectionFunction) (key : ℂ → RealFrame → data.cusp.smooth) :
    ∃ cutoff : LocallyConstant (Rectangular FiniteAdeles) ℂ,
      HasCompactSupport (cutoff : Rectangular FiniteAdeles → ℂ) ∧
      ∀ point : IntegralFiniteGL, cutoff (embedding (frame point)) = if profileKey flat point = key then 1 else 0 := by
  obtain ⟨region, clopen, membership⟩ := CompactFiniteFrames.fiber_extension flat key
  refine ⟨indicator region clopen, indicator_compactSupport region clopen, fun point => ?_⟩
  rw [indicator_embedding, membership]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteProfileCutoffs
