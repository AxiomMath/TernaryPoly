module

public import TernaryPeriodPolynomials.Topology.Rational.Local.OrientationSupport
public import TernaryPeriodPolynomials.Topology.Rational.Local.OrientationHomeomorph

@[expose] public section


noncomputable section
namespace TernaryPoly.RationalChartCompactSupport
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open RationalRelativeSingular RationalRelativeExcision RationalLocalChartHomology RationalLocalOrientation

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- A chart sends a compact support in its source to an actual compact image support. -/
theorem image_isCompact (e : OpenPartialHomeomorph X Y) (K : Set X) (hK : IsCompact K)
    (hKs : K ⊆ e.source) : IsCompact (e '' K) :=
  hK.image_of_continuousOn (e.continuousOn.mono hKs)

/-- The literal chart image support is contained in the chart target. -/
theorem image_subset_target (e : OpenPartialHomeomorph X Y) (K : Set X)
    (hKs : K ⊆ e.source) : e '' K ⊆ e.target := by
  rintro _ ⟨x, hx, rfl⟩
  exact e.map_source (hKs hx)

/-- Injectivity on the chart source exactly identifies the two support preimages. -/
theorem image_mem_iff (e : OpenPartialHomeomorph X Y) (K : Set X)
    (hKs : K ⊆ e.source) (x : e.source) : e x.val ∈ e '' K ↔ x.val ∈ K := by
  constructor
  · rintro ⟨z, hz, he⟩
    have hzx : z = x.val := e.injOn (hKs hz) x.property he
    simpa only [hzx] using hz
  · intro hx
    exact ⟨x.val, hx, rfl⟩

/-- The actual source-target chart homeomorphism is an isomorphism of support pairs. -/
def chartSupportPairIso (e : OpenPartialHomeomorph X Y) (K : Set X) (hKs : K ⊆ e.source) :
    relativeChains ((Subtype.val : e.source → X) ⁻¹' K)ᶜ ≅
      relativeChains ((Subtype.val : e.target → Y) ⁻¹' (e '' K))ᶜ :=
  relativeHomeomorphIso e.toHomeomorphSourceTarget _ _ (fun x => by
    change (x.val ∉ K) ↔ e x.val ∉ e '' K
    exact not_congr (image_mem_iff e K hKs x).symm)

/-- The middle chart-pair isomorphism commutes with actual support-to-point maps. -/
theorem chartSupportPairIso_point (e : OpenPartialHomeomorph X Y) (K : Set X)
    (hKs : K ⊆ e.source) (x : X) (hx : x ∈ K) :
    (chartSupportPairIso e K hKs).hom ≫
        supportPointMap ((Subtype.val : e.target → Y) ⁻¹' (e '' K))
          (e.toHomeomorphSourceTarget ⟨x, hKs hx⟩) ⟨x, hx, rfl⟩ =
      supportPointMap ((Subtype.val : e.source → X) ⁻¹' K) ⟨x, hKs hx⟩ hx ≫
        (homeomorphLocalIso e.toHomeomorphSourceTarget ⟨x, hKs hx⟩).hom := by
  unfold chartSupportPairIso supportPointMap homeomorphLocalIso
  rw [relativeHomeomorphIso_hom, relativeHomeomorphIso_hom]
  erw [relativeMap_comp, relativeMap_comp]
  rfl

end TernaryPoly.RationalChartCompactSupport
