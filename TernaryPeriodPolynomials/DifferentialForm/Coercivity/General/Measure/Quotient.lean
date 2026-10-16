module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Measure.FundamentalDomain

@[expose] public section


/-!
# General coercivity: the Riemannian volume of the orbit space

`quotientVolume Γ` is the pushforward of the Riemannian volume of `Space` restricted to a measurable
fundamental domain; it is characterised by Mathlib's `QuotientMeasureEqMeasurePreimage` and does not
depend on the domain.  Continuous functions of compact support on the orbit space are integrable.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open MeasureTheory Set Topology TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceCovering
open TernaryPoly.SymmetricSpaceCharts TernaryPoly.SymmetricSpaceRiemannian
open scoped ContDiff ENNReal

variable {Γ : Subgroup RealGL}

/-- Open sets of the orbit space are measurable for the quotient measurable structure. -/
instance instOpensMeasurableSpaceOrbitSpace (Γ : Subgroup RealGL) :
    OpensMeasurableSpace (OrbitSpace Γ) :=
  ⟨MeasurableSpace.generateFrom_le fun _ hU =>
    measurableSet_quotient.mpr (hU.preimage continuous_proj).measurableSet⟩

/-- The Riemannian volume of a compact subset of the positive coordinates is finite. -/
theorem coordinateVolume_lt_top {C : Set Coordinates} (hC : IsCompact C)
    (hsub : C ⊆ positiveCoordinates) : coordinateVolume C < ⊤ := by
  rw [coordinateVolume_apply]
  have hcont : ContinuousOn coordinateDensity C :=
    contDiffOn_coordinateDensity.continuousOn.mono hsub
  exact (hcont.integrableOn_compact hC).lintegral_lt_top

instance instIsFiniteMeasureOnCompactsSpaceVolume : IsFiniteMeasureOnCompacts spaceVolume :=
  ⟨fun _ hK => by
    rw [spaceVolume_apply]
    exact coordinateVolume_lt_top (hK.image coordinateEmbedding.continuous)
      (by rintro _ ⟨S, _, rfl⟩; exact extract_mem S)⟩

/-- Every compact subset of the orbit space of an admissible group is the image of a compact
subset of `Space`. -/
theorem Admissible.exists_compact_lift (h : Admissible Γ) {Q : Set (OrbitSpace Γ)}
    (hQ : IsCompact Q) : ∃ K : Set Space, IsCompact K ∧ Q ⊆ proj Γ '' K := by
  have hloc : ∀ q : OrbitSpace Γ, ∃ N : Set Space, IsCompact N ∧ proj Γ '' N ∈ 𝓝 q := by
    intro q
    obtain ⟨S, rfl⟩ := proj_surjective (Γ := Γ) q
    obtain ⟨N, hNc, hN⟩ := exists_compact_mem_nhds S
    exact ⟨N, hNc, h.isOpenMap_proj.image_mem_nhds hN⟩
  choose N hNc hNn using hloc
  obtain ⟨s, -, hs⟩ := hQ.elim_nhds_subcover (fun q => proj Γ '' N q) (fun q _ => hNn q)
  refine ⟨⋃ q ∈ s, N q, s.isCompact_biUnion fun q _ => hNc q, ?_⟩
  intro q hq
  obtain ⟨q', hq's, hqq'⟩ := Set.mem_iUnion₂.mp (hs hq)
  obtain ⟨S, hS, rfl⟩ := hqq'
  exact ⟨S, Set.mem_iUnion₂.mpr ⟨q', hq's, hS⟩, rfl⟩

open Classical in
/-- The Riemannian volume of the orbit space: the pushforward of the volume of `Space` restricted to
a measurable fundamental domain (any one; the result does not depend on the choice). -/
def quotientVolume (Γ : Subgroup RealGL) : Measure (OrbitSpace Γ) :=
  if h : ∃ t : Set Space, MeasurableSet t ∧ IsFundamentalDomain Γ t spaceVolume then
    (spaceVolume.restrict h.choose).map (proj Γ)
  else 0

/-- The orbit-space volume satisfies Mathlib's characterisation by every fundamental domain. -/
theorem Admissible.quotientMeasureEq (h : Admissible Γ) :
    QuotientMeasureEqMeasurePreimage spaceVolume (quotientVolume Γ) := by
  have : Countable Γ := h.countable
  have hex := h.exists_isFundamentalDomain
  unfold quotientVolume
  rw [dite_eq_left hex]
  exact hex.choose_spec.2.quotientMeasureEqMeasurePreimage_quotientMeasure

theorem Admissible.quotientVolume_eq (h : Admissible Γ) {t : Set Space}
    (ht : IsFundamentalDomain Γ t spaceVolume) :
    quotientVolume Γ = (spaceVolume.restrict t).map (proj Γ) := by
  have := h.quotientMeasureEq
  exact ht.projection_respects_measure (quotientVolume Γ)

/-- Integrals over the orbit space are integrals over any fundamental domain. -/
theorem Admissible.integral_quotientVolume (h : Admissible Γ) {t : Set Space}
    (ht : IsFundamentalDomain Γ t spaceVolume) {f : OrbitSpace Γ → ℝ} (hf : Measurable f) :
    ∫ q, f q ∂quotientVolume Γ = ∫ x in t, f (proj Γ x) ∂spaceVolume := by
  rw [h.quotientVolume_eq ht]
  exact integral_map (measurable_quotient_mk' (s := MulAction.orbitRel Γ Space)).aemeasurable
    hf.aestronglyMeasurable

/-- The orbit-space volume of a compact set is finite. -/
theorem Admissible.quotientVolume_lt_top (h : Admissible Γ) {Q : Set (OrbitSpace Γ)}
    (hQ : IsCompact Q) : quotientVolume Γ Q < ⊤ := by
  have : Countable Γ := h.countable
  have := h.quotientMeasureEq
  have := h.t2
  obtain ⟨K, hK, hQK⟩ := h.exists_compact_lift hQ
  obtain ⟨t, -, ht⟩ := h.exists_isFundamentalDomain
  have himg : IsCompact (proj Γ '' K) := hK.image continuous_proj
  have hmeas : MeasurableSet (proj Γ '' K) := himg.isClosed.measurableSet
  refine lt_of_le_of_lt (measure_mono hQK) ?_
  rw [ht.projection_respects_measure_apply (quotientVolume Γ) hmeas]
  have hpre : proj Γ ⁻¹' (proj Γ '' K) = ⋃ γ : Γ, (γ • ·) '' K := by
    ext S
    simp only [mem_preimage, mem_image, mem_iUnion]
    constructor
    · rintro ⟨T, hT, hTS⟩
      obtain ⟨γ, hγ⟩ := proj_eq_iff.mp hTS
      exact ⟨γ, T, hT, hγ⟩
    · rintro ⟨γ, T, hT, rfl⟩
      exact ⟨T, hT, (proj_smul γ T).symm⟩
  have hsum := ht.measure_eq_tsum K
  calc spaceVolume (proj Γ ⁻¹' (proj Γ '' K) ∩ t)
      = spaceVolume (⋃ γ : Γ, ((γ • ·) '' K ∩ t)) := by rw [hpre, iUnion_inter]
    _ ≤ ∑' γ : Γ, spaceVolume ((γ • ·) '' K ∩ t) := measure_iUnion_le _
    _ = spaceVolume K := by
        rw [hsum]
        exact tsum_congr fun γ => by rw [Set.image_smul]
    _ < ⊤ := hK.measure_lt_top

/-- Continuous functions of compact support on the orbit space are integrable. -/
theorem Admissible.integrable_of_continuous (h : Admissible Γ) {f : OrbitSpace Γ → ℝ}
    (hf : Continuous f) (hc : HasCompactSupport f) : Integrable f (quotientVolume Γ) := by
  have : IsFiniteMeasureOnCompacts (quotientVolume Γ) := ⟨fun _ hQ => h.quotientVolume_lt_top hQ⟩
  exact hf.integrable_of_hasCompactSupport hc

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
