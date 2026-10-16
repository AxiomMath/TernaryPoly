module

public import TernaryPeriodPolynomials.Building.BadVertex.Elimination
public import TernaryPeriodPolynomials.Building.BadEdge.Elimination
public import TernaryPeriodPolynomials.Building.BadVertex.LinkFilling

@[expose] public section


noncomputable section
namespace TernaryPoly.GoodChainFilling
open AugmentedFrameComplex OrientedListChains
open BadVertexElimination BadEdgeElimination

/-- The exact ambient degree-two filling input, stated on actual finite oriented chains. -/
def AmbientTwoFilling : Prop :=
  ∀ c : Chain RationalLine, c ∈ chains ambient 3 → boundary c = 0 →
    ∃ t : Chain RationalLine, t ∈ chains ambient 4 ∧ boundary t = c

/-- The proved finite three-bad and two-bad elimination and last-stage chain chase reduce every
relative ambient filling to the exact bad-vertex inclusion-boundary obligation. -/
theorem good_replacement (hlink : LinkBoundaryFilling) {c : Chain RationalLine}
    (hc : c ∈ chains ambient 4) (hd : boundary c ∈ chains good 3) :
    ∃ t : Chain RationalLine, t ∈ chains good 4 ∧ boundary t = boundary c := by
  obtain ⟨d,hdAmbient,hdBoundary,hdThree,hdTwo⟩ := eliminate_three_and_two_bad hc hd
  obtain ⟨t,ht,hdt⟩ := eliminate_one_bad hlink hdAmbient (by rwa [hdBoundary]) hdTwo hdThree
  exact ⟨t,ht,hdt.trans hdBoundary⟩

/-- Actual Good H2 vanishing follows from exactly two explicit filling obligations.
Neither input is silently inferred from the finite cap identities. -/
theorem good_two_filling (hambient : AmbientTwoFilling) (hlink : LinkBoundaryFilling)
    {c : Chain RationalLine} (hc : c ∈ chains good 3) (hd : boundary c = 0) :
    ∃ t : Chain RationalLine, t ∈ chains good 4 ∧ boundary t = c := by
  obtain ⟨a,ha,hda⟩ := hambient c (chains_mono good_le_ambient 3 hc) hd
  obtain ⟨t,ht,hdt⟩ := good_replacement hlink ha (by rwa [hda])
  exact ⟨t,ht,hdt.trans hda⟩

/-- Every relative ambient tetrahedron filling with Good boundary admits an actual Good
replacement; all three bad strata are now removed unconditionally. -/
theorem good_replacement_unconditional {c : Chain RationalLine}
    (hc : c ∈ chains ambient 4) (hd : boundary c ∈ chains good 3) :
    ∃ t : Chain RationalLine, t ∈ chains good 4 ∧ boundary t = boundary c :=
  good_replacement BadVertexLinkFilling.link_boundary_filling hc hd

/-- The only filling input for actual Good H2 vanishing is ambient H2 filling. -/
theorem good_two_filling_of_ambient (hambient : AmbientTwoFilling)
    {c : Chain RationalLine} (hc : c ∈ chains good 3) (hd : boundary c = 0) :
    ∃ t : Chain RationalLine, t ∈ chains good 4 ∧ boundary t = c :=
  good_two_filling hambient BadVertexLinkFilling.link_boundary_filling hc hd

end TernaryPoly.GoodChainFilling
