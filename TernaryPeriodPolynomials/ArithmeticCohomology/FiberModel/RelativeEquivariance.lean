module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Top.BoundaryComparisonOrdinaryIso
public import TernaryPeriodPolynomials.ArithmeticCohomology.FiberModel.BoundaryEdgeEquivariance
public import TernaryPeriodPolynomials.GroupCohomology.Homology.NormalActionEval
public import TernaryPeriodPolynomials.GroupCohomology.Homology.NormalActionQuotient

@[expose] public section


/-!
# `IntegralGL`-equivariance of the relative `Hom`-cohomology / ordinary-cycles identification (`S3`)

`gluedAct` and `relAct` equip the principal-six singular chains of the bordification and of the
bordification pair with the action of `IntegralGL` (`GActC`), the latter by descending along the
graded section of the relative projection.  The connecting map of the pair, the library's
identification `upstairsRelativeH2OrdinaryIso` of relative `H₂` with the ordinary cycles, and
therefore the library's isomorphism `relativeOrdinaryCohomologyIso` between relative
`Hom`-cohomology and `Γ(6)`-equivariant functionals on the Steinberg module, are equivariant:
`upstairsRelativeH2OrdinaryIso_cycAct`, `relativeOrdinaryCohomologyIso_hcohAct`.  The inputs are the
equivariance of the edge map (`BoundaryEdgeEquivariance`) and the generic layer
`GroupHomology.NormalAction`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FiberModel

open CategoryTheory Limits HomologicalComplex
open TernaryPoly TernaryPoly.IntegralGL3Congruence TernaryPoly.ModThreeGoodAction
  TernaryPoly.SingularBoundaryRestriction TernaryPoly.SymmetricSpaceRationalGluing
  TernaryPoly.EquivariantSingularResolution TernaryPoly.OrdinaryTopBoundaryComparison
  TernaryPoly.SymmetricSpaceBoundaryIncidenceHomology TernaryPoly.SymmetricSpaceBoundaryFull
  TernaryPoly.SymmetricSpaceBoundaryFullTransfer TernaryPoly.EquivariantSingularSmall
  TernaryPeriodPolynomials.Argument.GroupHomology

/-- The full `IntegralGL`-equivariant singular chains of the bordification. -/
abbrev fullGlued : ChainComplex (Rep.{0} ℚ IntegralGL) ℕ :=
  equivariantChains IntegralGL (TopCat.of Glued)

/-- The `IntegralGL`-action on the principal-six singular chains of the bordification. -/
def gluedAct : GActC (H := principalSix) (equivariantChains principalSix (TopCat.of Glued)) :=
  GActC.ofChain principalSix fullGlued

theorem boundaryInclusion_equivariantG (g : IntegralGL) (x : BoundaryCover) :
    boundaryInclusion (g • x) = g • boundaryInclusion x := rfl

theorem upstairsBoundaryChainMap_gmor : IsGMorC bdryAct gluedAct upstairsBoundaryChainMap :=
  fun n g x => Rep.hom_comm_apply
    ((SingularCoverNaturality.chainMap (G := IntegralGL) boundaryInclusion
      boundaryInclusion_equivariantG).f n) g x

/-- The `IntegralGL`-action on the relative chains of the bordification pair, descended along the
graded section of the relative projection. -/
def relAct : GActC (H := principalSix) upstairsRelativeChains :=
  GActC.quotient upstairsRelativeSequence_shortExact upstairsBoundaryChainMap_gmor
    (fun n => relativeProjectionSection boundaryInclusion boundaryInclusion_equivariant
      boundaryInclusion_injective n)
    (fun n => relativeProjectionSection_identity boundaryInclusion boundaryInclusion_equivariant
      boundaryInclusion_injective n)

theorem upstairsRelativeProjection_gmor : IsGMorC gluedAct relAct upstairsRelativeSequence.g :=
  GActC.isGMorC_quotient upstairsRelativeSequence_shortExact upstairsBoundaryChainMap_gmor _ _

/-- **Equivariance of the identification of relative `H₂` with the ordinary cycles.** -/
theorem upstairsRelativeH2OrdinaryIso_cycAct (g : IntegralGL) (z : Cyc upstairsRelativeChains 1) :
    upstairsRelativeH2OrdinaryIso.hom (relAct.cycAct g z).cls =
      TernaryPoly.OrdinaryFullAction.cycleAction (TernaryPoly.OrdinaryFullAction.integral g)
        (upstairsRelativeH2OrdinaryIso.hom z.cls) := by
  obtain ⟨z₁, h1, h2⟩ := delta_cycAct (k := 0) upstairsRelativeSequence_shortExact
    upstairsBoundaryChainMap_gmor upstairsRelativeProjection_gmor g z
  change boundaryH1OrdinaryCyclesIso.hom
    (upstairsRelativeSequence_shortExact.δ 2 1 rfl (relAct.cycAct g z).cls) =
    TernaryPoly.OrdinaryFullAction.cycleAction (TernaryPoly.OrdinaryFullAction.integral g)
      (boundaryH1OrdinaryCyclesIso.hom (upstairsRelativeSequence_shortExact.δ 2 1 rfl z.cls))
  have h1' : upstairsRelativeSequence_shortExact.δ 2 1 rfl z.cls = z₁.cls := h1
  have h2' : upstairsRelativeSequence_shortExact.δ 2 1 rfl (relAct.cycAct g z).cls =
      (bdryAct.cycAct g z₁).cls := h2
  rw [h1', h2']
  exact boundaryH1OrdinaryCyclesIso_cycAct g z₁

theorem relativeOrdinaryCohomologyIso_hcohAct_cocycle (W₀ : Rep.{0} ℚ IntegralGL) (g : IntegralGL)
    (xc : (homCochains upstairsRelativeChains (Rep.res principalSix.subtype W₀)).cycles 2)
    (σ : OrdinaryIncidenceChains.Cycles) :
    ((relativeOrdinaryCohomologyIso (Rep.res principalSix.subtype W₀)).hom
        (hcohAct relAct (GAct.ofRep principalSix W₀) g 2
          ((homCochains upstairsRelativeChains (Rep.res principalSix.subtype W₀)).homologyπ 2 xc))).hom
        σ =
      W₀.ρ g (((relativeOrdinaryCohomologyIso (Rep.res principalSix.subtype W₀)).hom
        ((homCochains upstairsRelativeChains (Rep.res principalSix.subtype W₀)).homologyπ 2 xc)).hom
        (TernaryPoly.OrdinaryFullAction.cycleAction
          (TernaryPoly.OrdinaryFullAction.integral g⁻¹) σ)) := by
  obtain ⟨z, hz⟩ := Cyc.exists_cls (D := upstairsRelativeChains) (k := 1)
    (upstairsRelativeH2OrdinaryIso.inv.hom σ)
  have hι : ∀ (y : (homCochains upstairsRelativeChains (Rep.res principalSix.subtype W₀)).homology 2)
      (τ : OrdinaryIncidenceChains.Cycles),
      ((relativeOrdinaryCohomologyIso (Rep.res principalSix.subtype W₀)).hom y).hom τ =
        (homologyEvaluation upstairsRelativeChains (Rep.res principalSix.subtype W₀) 2 y).hom
          (upstairsRelativeH2OrdinaryIso.inv.hom τ) := fun y τ => rfl
  rw [hι, hι]
  have hL := homologyEvaluation_hcohAct relAct (GAct.ofRep principalSix W₀) g 2 xc
    (cycMk upstairsRelativeChains 1 z.1 z.2)
  rw [iCycles_cycMk] at hL
  have hR : upstairsRelativeH2OrdinaryIso.inv.hom
      (TernaryPoly.OrdinaryFullAction.cycleAction (TernaryPoly.OrdinaryFullAction.integral g⁻¹) σ) =
        (relAct.cycAct g⁻¹ z).cls := by
    have h := upstairsRelativeH2OrdinaryIso_cycAct g⁻¹ z
    have h2 : upstairsRelativeH2OrdinaryIso.hom z.cls = σ := by
      rw [hz]
      exact congrArg (fun f => f.hom σ) upstairsRelativeH2OrdinaryIso.inv_hom_id
    rw [h2] at h
    rw [← h]
    exact congrArg (fun f => f.hom (relAct.cycAct g⁻¹ z).cls) upstairsRelativeH2OrdinaryIso.hom_inv_id
  have hE := homologyEvaluation_apply upstairsRelativeChains
    (Rep.res principalSix.subtype W₀) 2 xc
    (cycMk upstairsRelativeChains 1 (relAct.cycAct g⁻¹ z).1 (relAct.cycAct g⁻¹ z).2)
  rw [iCycles_cycMk] at hE
  rw [hR, ← hz]
  exact hL.trans (congrArg _ hE.symm)

/-- **Equivariance of the neat-level cohomology-to-functional identification (`S3`).**  For a
coefficient representation `W₀` of `IntegralGL` and `g ∈ IntegralGL`, the library's isomorphism
`relativeOrdinaryCohomologyIso` intertwines the conjugation action on relative `Hom`-cohomology
(`hcohAct`, i.e. `φ ↦ ρ_W(g) ∘ φ ∘ ρ(g)⁻¹`) with `Φ ↦ ρ_W(g) ∘ Φ ∘ ρ_St(g)⁻¹` on functionals
`St → W`. -/
theorem relativeOrdinaryCohomologyIso_hcohAct (W₀ : Rep.{0} ℚ IntegralGL) (g : IntegralGL)
    (x : (homCochains upstairsRelativeChains (Rep.res principalSix.subtype W₀)).homology 2)
    (σ : OrdinaryIncidenceChains.Cycles) :
    ((relativeOrdinaryCohomologyIso (Rep.res principalSix.subtype W₀)).hom
        (hcohAct relAct (GAct.ofRep principalSix W₀) g 2 x)).hom σ =
      W₀.ρ g (((relativeOrdinaryCohomologyIso (Rep.res principalSix.subtype W₀)).hom x).hom
        (TernaryPoly.OrdinaryFullAction.cycleAction
          (TernaryPoly.OrdinaryFullAction.integral g⁻¹) σ)) := by
  obtain ⟨xc, hxc⟩ := (ModuleCat.epi_iff_surjective
    ((homCochains upstairsRelativeChains (Rep.res principalSix.subtype W₀)).homologyπ 2)).mp
      inferInstance x
  rw [← hxc]
  exact relativeOrdinaryCohomologyIso_hcohAct_cocycle W₀ g xc σ

end TernaryPeriodPolynomials.Argument.FiberModel
