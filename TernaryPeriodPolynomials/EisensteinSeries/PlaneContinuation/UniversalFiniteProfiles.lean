module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Flat.ProfilePackages

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealFrameChart TernaryPeriodPolynomials.PlaneEisensteinContinuation.FrameProfile
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.CompactFiniteFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.FlatProfilePackages
open scoped Matrix.Norms.Elementwise Classical

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.UniversalFiniteProfiles

abbrev ProfileType {degree : ℕ} (data : InducingData degree) :=
  (parameter : ℂ) → (function : AdelicGL → ℂ) →
    IsInduced data .plane parameter function → RealFrame → data.cusp.smooth

def profileKey {degree : ℕ} (data : InducingData degree) (point : IntegralFiniteGL) : ProfileType data :=
  fun _ _ induced value => profile induced
    (adelicFrame (GeneralLinearGroup.map integralEmbedding point) value.val)

theorem key_compatible {degree : ℕ} (data : InducingData degree)
    (first second : IntegralFiniteGL) (equality : CompactFiniteFrames.frame first = CompactFiniteFrames.frame second) :
    profileKey data first = profileKey data second := by
  funext parameter function induced value
  unfold profileKey
  rw [CompactFiniteFrames.adelicFrame_eq first second equality]

theorem key_locallyConstant {degree : ℕ} (data : InducingData degree) :
    IsLocallyConstant (profileKey data) := by
  have result := (FiniteProfileRegularity.representative_locallyConstant data).comp (profileKey data)
  have equality : profileKey data = profileKey data ∘ FiniteProfileRegularity.representative data := by
    funext point parameter function induced value
    exact FiniteProfileRegularity.profile_eq_representative induced point value.val value.property
  rw [← equality] at result
  exact result

theorem key_finite_range {degree : ℕ} (data : InducingData degree) :
    (Set.range (profileKey data)).Finite := by
  let _ : CompactSpace (Matrix (Fin 3) (Fin 3) IntegralAdeles) :=
    inferInstanceAs (CompactSpace (Fin 3 → Fin 3 → IntegralAdeles))
  exact (key_locallyConstant data).range_finite

abbrev Key {degree : ℕ} (data : InducingData degree) := Set.range (profileKey data)

instance keyFintype {degree : ℕ} (data : InducingData degree) : Fintype (Key data) :=
  (key_finite_range data).fintype

def representative {degree : ℕ} (data : InducingData degree) (key : Key data) : IntegralFiniteGL :=
  Classical.choose key.property

theorem representative_key {degree : ℕ} (data : InducingData degree) (key : Key data) :
    profileKey data (representative data key) = key.val :=
  Classical.choose_spec key.property

def selected {degree : ℕ} (data : InducingData degree) (point : IntegralFiniteGL) : Key data :=
  ⟨profileKey data point, ⟨point, rfl⟩⟩

theorem profile_eq_selected {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {function : AdelicGL → ℂ} (induced : IsInduced data .plane parameter function)
    (point : IntegralFiniteGL) (value : Rectangular ℝ) (fullRank : FullRank value) :
    profile induced (adelicFrame (GeneralLinearGroup.map integralEmbedding
      (representative data (selected data point))) value) =
        profile induced (adelicFrame (GeneralLinearGroup.map integralEmbedding point) value) :=
  congrFun (congrFun (congrFun (congrFun
    (representative_key data (selected data point)) parameter) function) induced) ⟨value, fullRank⟩

theorem fiber_extension {degree : ℕ} (data : InducingData degree) (key : ProfileType data) :
    ∃ region : Set IntegralSpace, IsClopen region ∧ ∀ point : IntegralFiniteGL,
      CompactFiniteFrames.frame point ∈ region ↔ profileKey data point = key := by
  let _ : CompactSpace (Matrix (Fin 3) (Fin 3) IntegralAdeles) :=
    inferInstanceAs (CompactSpace (Fin 3 → Fin 3 → IntegralAdeles))
  let _ : CompactSpace IntegralSpace := inferInstanceAs (CompactSpace (Fin 3 → Fin 2 → IntegralAdeles))
  let _ : TotallyDisconnectedSpace IntegralSpace :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin 3 → Fin 2 → IntegralAdeles))
  exact ProfiniteClopenExtension.fiber_extension CompactFiniteFrames.frame frame_continuous
    (profileKey data) (key_locallyConstant data) (key_compatible data) key

theorem exists_boxes {degree : ℕ} (data : InducingData degree) (key : Key data) :
    ∃ boxes : Boxes, ∀ point : IntegralFiniteGL,
      boxes.test (embedding (CompactFiniteFrames.frame point)) =
        if profileKey data point = key.val then 1 else 0 := by
  obtain ⟨region, clopen, membership⟩ := fiber_extension data key.val
  obtain ⟨scale, indices, equality⟩ := IntegralFiniteExpansion.indicator_expansion region clopen
  refine ⟨⟨scale, indices, fun coset =>
    FiniteProfileCutoffs.indicator region clopen (IntegralFiniteExpansion.coordinates.symm coset.out)⟩, ?_⟩
  intro point
  change (∑ coset ∈ indices, _ * _) = _
  rw [← equality, FiniteProfileCutoffs.indicator_embedding, membership]

theorem exists_supported_boxes {degree : ℕ} (data : InducingData degree) (key : Key data) :
    ∃ boxes : Boxes,
      (∀ point : IntegralFiniteGL, boxes.test (embedding (CompactFiniteFrames.frame point)) =
        if profileKey data point = key.val then 1 else 0) ∧
      (∀ value : Rectangular FiniteAdeles, value ∉ Set.range embedding → boxes.test value = 0) ∧
      ∀ value : Rectangular FiniteAdeles, boxes.test value = 0 ∨ boxes.test value = 1 := by
  obtain ⟨region, clopen, membership⟩ := fiber_extension data key.val
  obtain ⟨scale, indices, equality⟩ := IntegralFiniteExpansion.indicator_expansion region clopen
  let result : Boxes := ⟨scale, indices, fun coset =>
    FiniteProfileCutoffs.indicator region clopen (IntegralFiniteExpansion.coordinates.symm coset.out)⟩
  have resultEquality (value : Rectangular FiniteAdeles) :
      result.test value = FiniteProfileCutoffs.indicator region clopen value := (equality value).symm
  refine ⟨result, ?_, ?_, ?_⟩
  · intro point
    rw [resultEquality, FiniteProfileCutoffs.indicator_embedding, membership]
  · intro value outside
    rw [resultEquality, FiniteProfileCutoffs.indicator_apply, Set.indicator_of_notMem]
    rintro ⟨integral, _, equality⟩
    exact outside ⟨integral, equality⟩
  · intro value
    rw [resultEquality, FiniteProfileCutoffs.indicator_apply]
    by_cases inside : value ∈ embedding '' region
    · exact Or.inr (Set.indicator_of_mem inside _)
    · exact Or.inl (Set.indicator_of_notMem inside _)

def boxes {degree : ℕ} (data : InducingData degree) (key : Key data) : Boxes :=
  (exists_supported_boxes data key).choose

theorem boxes_frame {degree : ℕ} (data : InducingData degree) (key : Key data) (point : IntegralFiniteGL) :
    (boxes data key).test (embedding (CompactFiniteFrames.frame point)) =
      if profileKey data point = key.val then 1 else 0 :=
  (exists_supported_boxes data key).choose_spec.1 point

theorem boxes_supported {degree : ℕ} (data : InducingData degree) (key : Key data)
    (value : Rectangular FiniteAdeles) (outside : value ∉ Set.range embedding) :
    (boxes data key).test value = 0 :=
  (exists_supported_boxes data key).choose_spec.2.1 value outside

theorem boxes_values {degree : ℕ} (data : InducingData degree) (key : Key data)
    (value : Rectangular FiniteAdeles) : (boxes data key).test value = 0 ∨ (boxes data key).test value = 1 :=
  (exists_supported_boxes data key).choose_spec.2.2 value

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.UniversalFiniteProfiles
