module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Cover.Principal
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Measure.Quotient
public import TernaryPeriodPolynomials.SymmetricSpace.Riemannian.ChartIntegral
public import TernaryPeriodPolynomials.DifferentialForm.CoefficientMetric.Representation

@[expose] public section


/-!
# General coercivity: comparison with the orbit-space volume

The cover is `DeckGroup = principalSixInK`, acting on `Space` through `deckMatrix`; the same
group embedded in `GL₃(ℝ)` is `principalSixInKReal`.  The two groups have the same orbits, hence the
same quotient.  This file proves that the chart-glued Riemannian volume `orbitVolume` is the
pushforward of `spaceVolume` restricted to a measurable fundamental domain, which is how
`quotientVolume` is defined; so both volumes integrate every continuous function alike.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open MeasureTheory Set TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceCharts
open scoped TernaryPoly.SymmetricSpaceRiemannian Pointwise

/-- The deck group. -/
abbrev FDeck := TernaryPoly.SymmetricSpaceCovering.DeckGroup

/-- The orbit space. -/
abbrev FOrbit := TernaryPoly.SymmetricSpaceCovering.OrbitSpace

/-- The deck group as a subgroup of `GL₃(ℝ)`. -/
abbrev gamma0 : Subgroup RealGL := principalSixInKReal

/-- The deck element as an element of `gamma0`. -/
def toGamma (g : FDeck) : gamma0 :=
  ⟨TernaryPoly.PolynomialCoefficientMetric.deckMatrix g,
    ⟨(g : TernaryPoly.ModThreeGoodAction.K).val, ⟨g.1, g.2, rfl⟩, rfl⟩⟩

theorem toGamma_surjective : Function.Surjective toGamma := by
  rintro ⟨_, _, ⟨k, hk, rfl⟩, rfl⟩
  exact ⟨⟨k, hk⟩, rfl⟩

theorem toGamma_smul (g : FDeck) (S : Space) : toGamma g • S = g • S := rfl

theorem frozen_proj_eq_iff (S T : Space) :
    TernaryPoly.SymmetricSpaceCovering.quotientProjection S =
        TernaryPoly.SymmetricSpaceCovering.quotientProjection T ↔
      ∃ γ : gamma0, γ • T = S := by
  rw [TernaryPoly.SymmetricSpaceCovering.quotientProjection_quotientCovering.apply_eq_iff_mem_orbit]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨toGamma g, hg⟩
  · rintro ⟨γ, hγ⟩
    obtain ⟨g, rfl⟩ := toGamma_surjective γ
    exact ⟨g, hγ⟩

/-- The saturation of a measurable set meeting every orbit at most once has the volume of the set. -/
theorem volume_saturation {Γ : Subgroup RealGL} (h : Admissible Γ) {t : Set Space}
    (ht : MeasurableSet t) (hFD : IsFundamentalDomain Γ t spaceVolume) {A : Set Space}
    (hA : MeasurableSet A)
    (hinj : ∀ a ∈ A, ∀ a' ∈ A, ∀ γ : Γ, γ • a = a' → a = a') :
    spaceVolume ((⋃ γ : Γ, γ • A) ∩ t) = spaceVolume A := by
  have : Countable Γ := h.countable
  have hsum := hFD.measure_eq_tsum A
  rw [iUnion_inter, measure_iUnion, hsum]
  · intro g g' hne
    refine Set.disjoint_left.mpr ?_
    rintro x ⟨hx, -⟩ ⟨hx', -⟩
    obtain ⟨a, ha, rfl⟩ := mem_smul_set.mp hx
    obtain ⟨a', ha', haa⟩ := mem_smul_set.mp hx'
    have h1 : (g'⁻¹ * g) • a = a' := by
      rw [mul_smul, ← haa, smul_smul, inv_mul_cancel, one_smul]
    have h2 := hinj a ha a' ha' _ h1
    subst h2
    apply hne
    have := h.free' (g'⁻¹ * g) a h1
    exact (inv_mul_eq_one.mp this).symm
  · intro g
    exact (hA.const_smul g).inter ht

open TernaryPoly.SymmetricSpaceCovering in
theorem sat_eq {S : Space} {B : Set TernaryPoly.SymmetricSpaceCovering.OrbitSpace}
    (hB : B ⊆ (TernaryPoly.SymmetricSpaceCovering.localLift S).source) :
    TernaryPoly.SymmetricSpaceCovering.quotientProjection ⁻¹' B =
      ⋃ γ : gamma0, γ • (TernaryPoly.SymmetricSpaceCovering.localLift S '' B) := by
  ext x
  simp only [mem_preimage, mem_iUnion]
  constructor
  · intro hx
    have hs : TernaryPoly.SymmetricSpaceCovering.quotientProjection x ∈
        (TernaryPoly.SymmetricSpaceCovering.localLift S).source := hB hx
    have h1 := TernaryPoly.SymmetricSpaceQuotientManifold.projection_localLift S hs
    obtain ⟨γ, hγ⟩ := (frozen_proj_eq_iff _ _).mp h1.symm
    exact ⟨γ, mem_smul_set.mpr ⟨_, ⟨_, hx, rfl⟩, hγ⟩⟩
  · rintro ⟨γ, hγ⟩
    obtain ⟨_, ⟨b, hb, rfl⟩, rfl⟩ := mem_smul_set.mp hγ
    obtain ⟨g, rfl⟩ := toGamma_surjective γ
    have h1 := TernaryPoly.SymmetricSpaceQuotientManifold.projection_localLift S (hB hb)
    have h2 : TernaryPoly.SymmetricSpaceCovering.quotientProjection
        (toGamma g • TernaryPoly.SymmetricSpaceCovering.localLift S b) =
        TernaryPoly.SymmetricSpaceCovering.quotientProjection
          (TernaryPoly.SymmetricSpaceCovering.localLift S b) :=
      (frozen_proj_eq_iff _ _).mpr ⟨toGamma g, rfl⟩
    rw [h2, h1]
    exact hb

open TernaryPoly.SymmetricSpaceCovering TernaryPoly.SymmetricSpaceRiemannian in
/-- The chart-glued volume is the pushforward of the Riemannian volume of `Space` restricted
to a measurable fundamental domain. -/
theorem orbitVolume_eq_map {t : Set Space} (ht : MeasurableSet t)
    (hu : ∀ x : Space, ∃! γ : gamma0, γ • x ∈ t) :
    orbitVolume = (spaceVolume.restrict t).map quotientProjection := by
  have hA0 : Admissible gamma0 := admissible_principalSixInKReal
  have hFD : IsFundamentalDomain gamma0 t spaceVolume :=
    IsFundamentalDomain.mk' ht.nullMeasurableSet hu
  have hπ : Measurable quotientProjection := quotientProjection_covering.continuous.measurable
  refine TernaryPoly.CompatibleMeasureGluing.unique
    (fun i => (quotientChart (volumeAtlas i)).source) volumeAtlas_cover _ _ (fun i => ?_)
  set S := volumeAtlas i with hS
  have hU : MeasurableSet (quotientChart S).source := (quotientChart S).open_source.measurableSet
  ext A hA
  rw [orbitVolume_restrict_chart S, chartVolume, TernaryPoly.ChartLocalMeasure.localMeasure_apply,
    Measure.restrict_apply hA, Measure.map_apply hπ (hA.inter hU),
    Measure.restrict_apply (hπ (hA.inter hU))]
  set B := A ∩ (quotientChart S).source with hB
  have hBsub : B ⊆ (localLift S).source := by
    intro x hx
    simpa using hx.2
  have hBm : MeasurableSet B := hA.inter hU
  have hAm : MeasurableSet (localLift S '' B) :=
    TernaryPoly.ChartLocalMeasure.measurableSet_image (localLift S) hBm hBsub
  have hsat := sat_eq (S := S) hBsub
  have hinj : ∀ a ∈ localLift S '' B, ∀ a' ∈ localLift S '' B, ∀ γ : gamma0, γ • a = a' →
      a = a' := by
    rintro _ ⟨b, hb, rfl⟩ _ ⟨b', hb', rfl⟩ γ hγ
    have h1 : quotientProjection (localLift S b') = quotientProjection (localLift S b) :=
      (frozen_proj_eq_iff _ _).mpr ⟨γ, hγ⟩
    rw [TernaryPoly.SymmetricSpaceQuotientManifold.projection_localLift S (hBsub hb'),
      TernaryPoly.SymmetricSpaceQuotientManifold.projection_localLift S (hBsub hb)] at h1
    rw [h1]
  rw [hsat, volume_saturation hA0 ht hFD hAm hinj, spaceVolume_apply]
  congr 1
  rw [image_image]
  rfl

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
