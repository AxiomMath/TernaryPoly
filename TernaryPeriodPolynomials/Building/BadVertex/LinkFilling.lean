module

public import TernaryPeriodPolynomials.Building.BadVertex.CoherentElimination
public import TernaryPeriodPolynomials.Building.BadVertex.MixedFilling
public import TernaryPeriodPolynomials.Building.BadVertex.Elimination
public import TernaryPeriodPolynomials.Topology.Rational.LineBasis

@[expose] public section

noncomputable section
namespace TernaryPoly.BadVertexLinkFilling
open ModThreeGoodAction AugmentedFrameComplex GoodLinkExtraction OrientedListChains

/-- Every actual two-cycle in a bad-vertex Good link bounds after inclusion in the Good
augmented-frame complex. Both infinite families reduce by finite exact face sums. -/
theorem frame_link_filling (g : IntegralGL) (hbad : ¬Good (augmentedLine g 0).val)
    {c : Chain RationalLine} (hc : c ∈ chains (augmentedGoodLink {augmentedLine g 0}) 3)
    (hd : boundary c = 0) :
    ∃ t : Chain RationalLine, t ∈ chains good 4 ∧ boundary t = c := by
  obtain ⟨t,r,ht,hr,him,hdr,he⟩ :=
    BadVertexCoherentElimination.eliminate_coherent g hbad hc hd
  obtain ⟨u,hu,hdu⟩ := BadVertexMixedFilling.mixed_cycle_filling g hbad hr him hdr
  exact ⟨t+u,(chains good 4).add_mem ht hu,by rw [map_add,hdu,← he]⟩

/-- The precise inclusion-boundary premise needed by finite bad-vertex elimination is proved. -/
theorem link_boundary_filling : BadVertexElimination.LinkBoundaryFilling := by
  intro a ha c hc hd
  obtain ⟨g,hg⟩ := RationalLineBasis.rationalLine_eq_augmentedLine a
  apply frame_link_filling g (by simpa only [hg,AugmentedFrameChains.isGood] using ha) (c := c) _ hd
  simpa only [hg] using hc

end TernaryPoly.BadVertexLinkFilling
