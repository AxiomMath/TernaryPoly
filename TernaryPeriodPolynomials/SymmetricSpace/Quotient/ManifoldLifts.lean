module

public import TernaryPeriodPolynomials.SymmetricSpace.CoveringCharts
public import TernaryPeriodPolynomials.SymmetricSpace.ChartsAction

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceQuotientManifold
open SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering
open Topology Set Filter

/-- Local injectivity of a covering makes agreeing continuous lifts agree near the basepoint. -/
theorem covering_lifts_eventuallyEq {E B Y : Type*}
    [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace Y]
    {p : E → B} (hp : IsLocalHomeomorph p) {f h : Y → E} {y : Y}
    (hf : ContinuousAt f y) (hh : ContinuousAt h y) (heq : f y=h y)
    (hproj : (fun z => p (f z)) =ᶠ[𝓝 y] (fun z => p (h z))) :
    f =ᶠ[𝓝 y] h := by
  obtain ⟨e,he,hep⟩ := hp (f y)
  have hfU : ∀ᶠ z in 𝓝 y,f z∈e.source := hf.preimage_mem_nhds (e.open_source.mem_nhds he)
  have hhU : ∀ᶠ z in 𝓝 y,h z∈e.source :=
    hh.preimage_mem_nhds (e.open_source.mem_nhds (heq ▸ he))
  filter_upwards [hfU,hhU,hproj] with z hzf hzh hzp
  exact e.injOn hzf hzh (by simpa only [hep] using hzp)

/-- The inverse of each restricted actual local lift is the exact quotient projection. -/
theorem localLift_symm (S : Space) : (localLift S).symm=quotientProjection := by
  change (quotientProjection_covering.isLocalHomeomorph.localInverseAt S).symm=quotientProjection
  exact quotientProjection_covering.isLocalHomeomorph.localInverseAt_symm S

/-- A local covering lift really is a section on its source. -/
theorem projection_localLift (S : Space) {x : OrbitSpace} (hx : x∈(localLift S).source) :
    quotientProjection (localLift S x)=x := by
  rw [←localLift_symm S]
  exact (localLift S).left_inv hx

/-- The exact local deck transformation relating two overlapping covering sections. -/
theorem localLift_eventually_deck (S T : Space) (x : OrbitSpace)
    (hS : x∈(localLift S).source) (hT : x∈(localLift T).source) :
    ∃ g : DeckGroup, localLift T =ᶠ[𝓝 x] (fun y => g • localLift S y) := by
  have hq : quotientProjection (localLift T x)=quotientProjection (localLift S x) := by
    rw [projection_localLift T hT,projection_localLift S hS]
  obtain ⟨g,hg⟩ := quotientProjection_quotientCovering.apply_eq_iff_mem_orbit.mp hq
  refine ⟨g,covering_lifts_eventuallyEq quotientProjection_covering.isLocalHomeomorph
    ((localLift T).continuousAt hT)
    ((continuous_const_smul g).continuousAt.comp ((localLift S).continuousAt hS)) hg.symm ?_⟩
  filter_upwards [(localLift S).open_source.mem_nhds hS,
    (localLift T).open_source.mem_nhds hT] with y hyS hyT
  rw [quotientProjection_quotientCovering.map_smul,projection_localLift T hyT,
    projection_localLift S hyS]

/-- The literal coordinates intertwine the actual deck action with the proved coordinate action. -/
theorem coordinates_deck_smul (g : DeckGroup) (S : Space) :
    extract (g • S).val =
      coordinateAction (SymmetricSpaceArithmeticProper.realIntegral (deckInclusion g))
        (extract S.val) := by
  exact chartHomeomorph_act
    (SymmetricSpaceArithmeticProper.realIntegral (deckInclusion g)) S

/-- Every covering-chart transition is locally one actual arithmetic coordinate action. -/
theorem quotientChart_transition_eventually (S T : Space) (x : Coordinates)
    (hx : x∈((quotientChart S).symm.trans (quotientChart T)).source) :
    ∃ g : DeckGroup, ((quotientChart S).symm.trans (quotientChart T)) =ᶠ[𝓝 x]
      coordinateAction (SymmetricSpaceArithmeticProper.realIntegral (deckInclusion g)) := by
  have hxS : x∈(quotientChart S).target := hx.1
  have hyS : (quotientChart S).symm x∈(localLift S).source := by
    rw [←quotientChart_source]
    exact (quotientChart S).map_target hxS
  have hyT : (quotientChart S).symm x∈(localLift T).source := by
    rw [←quotientChart_source]
    exact hx.2
  obtain ⟨g,hg⟩ := localLift_eventually_deck S T ((quotientChart S).symm x) hyS hyT
  refine ⟨g,?_⟩
  have hg' := ((quotientChart S).symm.continuousAt hxS).eventually hg
  filter_upwards [hg',(quotientChart S).open_target.mem_nhds hxS] with y hgy hy
  change extract (localLift T ((quotientChart S).symm y)).val=_
  rw [hgy,coordinates_deck_smul]
  congr 1
  exact (quotientChart S).right_inv hy

end TernaryPoly.SymmetricSpaceQuotientManifold
