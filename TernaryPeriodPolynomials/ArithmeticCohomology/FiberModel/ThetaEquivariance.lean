module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FiberModel.LocalReindexFiber
public import TernaryPeriodPolynomials.Topology.DualityEquivariance.HomNaturality
public import TernaryPeriodPolynomials.Topology.SingularLocal.Homology
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Top.BoundaryComparisonCap
public import TernaryPeriodPolynomials.ArithmeticCohomology.FiberModel.RelativeEquivariance
public import TernaryPeriodPolynomials.GroupCohomology.Homology.NormalActionEval

@[expose] public section


/-!
# Equivariance of the neat-level duality `Θ` (assembly, conditional on the cap/coefficient reindexing)

With `S1 = bordifiedGroupLocalHomologyIso`, `S2 = relativeHomCapIso`, `S3 = relativeOrdinaryCohomologyIso`
and `Θ = groupOrdinaryIso = S1 ≫ S2⁻¹ ≫ S3`:

* `conj_S1`: `S1` carries Mathlib's conjugation action `c_k` to `H₃(epsLoc ≫ Lspace)` (E1 and
  `diag_eq_phi_eps`);
* `S2_hcohAct`: `S2 ∘ hcohAct_k = H₃(epsLoc ≫ Lspace) ∘ S2`, from the twisted naturality of the cap
  and the statement `CapEpsStatement` (the cap product commutes with the fibrewise coefficient
  reindexing `epsLoc`);
* `groupOrdinaryIso_equivariant`: with `S3`-equivariance (`RelativeEquivariance`) this gives
  `Θ (c_k x) = ρ(k) ∘ Θ(x) ∘ σ(k⁻¹)`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open scoped Classical

namespace TernaryPeriodPolynomials.Argument.FiberModel

open CategoryTheory AlgebraicTopology TernaryPoly TernaryPoly.FreeActionLinearization
  TernaryPoly.SingularLocalHomology TernaryPoly.EquivariantSingularResolution
  TernaryPoly.CoveringSingularOrbits TernaryPoly.SingularBoundaryRestriction
  TernaryPoly.IntegralGL3Congruence TernaryPoly.SymmetricSpaceRationalGluing
  TernaryPoly.SymmetricSpaceArithmeticProper TernaryPoly.SymmetricSpaceBordifiedPrincipalSix
  TernaryPoly.SymmetricSpaceBordifiedQuotient
  TernaryPeriodPolynomials.Argument.DualityEquivariance
  TernaryPeriodPolynomials.Argument.GroupHomology

variable (k : IntegralGL) (V₀ : Rep.{0} ℚ IntegralGL)

/-- The diagonal action of `k` on the coinvariant singular chains. -/
def diagCo : coinvariantChains principalSix (TopCat.of Glued) (Rep.res principalSix.subtype V₀) ⟶
    coinvariantChains principalSix (TopCat.of Glued) (Rep.res principalSix.subtype V₀) :=
  GY principalSix (Ygeo (TopCat.of Glued) V₀) k

theorem epsLoc_Lspace_eq :
    epsLoc k V₀ ≫ Lspace k (Rep.res principalSix.subtype V₀) =
      (chainIso wholeProjection wholeQuotientCovering (Rep.res principalSix.subtype V₀)).inv ≫
        diagCo k V₀ ≫
        (chainIso wholeProjection wholeQuotientCovering (Rep.res principalSix.subtype V₀)).hom := by
  have hd : epsChain k V₀ ≫ coinvariantSpaceMap (PhiW k) (PhiW_equivariant k)
      (Rep.res principalSix.subtype V₀) = diagCo k V₀ := diag_eq_phi_eps k V₀
  unfold epsLoc Lspace localSpaceMap
  rw [← hd]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- **`S1` intertwines the conjugation action with the reindexed geometric action.**  -/
theorem conj_S1 :
    groupHomology.map (conjN principalSix k) (conjRep principalSix V₀ k) 3 ≫
        (bordifiedGroupLocalHomologyIso (Rep.res principalSix.subtype V₀) 3).hom =
      (bordifiedGroupLocalHomologyIso (Rep.res principalSix.subtype V₀) 3).hom ≫
        HomologicalComplex.homologyMap (epsLoc k V₀ ≫ Lspace k (Rep.res principalSix.subtype V₀)) 3 := by
  have hE : groupHomology.map (conjN principalSix k) (conjRep principalSix V₀ k) 3 ≫
        (groupCoinvariantHomologyIso principalSix (TopCat.of Glued) (Rep.res principalSix.subtype V₀) 3).hom =
      (groupCoinvariantHomologyIso principalSix (TopCat.of Glued) (Rep.res principalSix.subtype V₀) 3).hom ≫
        HomologicalComplex.homologyMap (diagCo k V₀) 3 :=
    groupCoinvariantHomologyIso_conj (E := TopCat.of Glued) (N := principalSix) V₀ 3 k
  have hc := epsLoc_Lspace_eq k V₀
  have key : HomologicalComplex.homologyMap
        (chainIso wholeProjection wholeQuotientCovering (Rep.res principalSix.subtype V₀)).hom 3 ≫
      HomologicalComplex.homologyMap (epsLoc k V₀ ≫ Lspace k (Rep.res principalSix.subtype V₀)) 3 =
      HomologicalComplex.homologyMap (diagCo k V₀) 3 ≫
        HomologicalComplex.homologyMap
          (chainIso wholeProjection wholeQuotientCovering (Rep.res principalSix.subtype V₀)).hom 3 := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp, hc]
    simp
  change groupHomology.map (conjN principalSix k) (conjRep principalSix V₀ k) 3 ≫
      ((groupCoinvariantHomologyIso principalSix (TopCat.of Glued) (Rep.res principalSix.subtype V₀) 3).hom ≫
        HomologicalComplex.homologyMap
          (chainIso wholeProjection wholeQuotientCovering (Rep.res principalSix.subtype V₀)).hom 3) =
    ((groupCoinvariantHomologyIso principalSix (TopCat.of Glued) (Rep.res principalSix.subtype V₀) 3).hom ≫
        HomologicalComplex.homologyMap
          (chainIso wholeProjection wholeQuotientCovering (Rep.res principalSix.subtype V₀)).hom 3) ≫
      HomologicalComplex.homologyMap (epsLoc k V₀ ≫ Lspace k (Rep.res principalSix.subtype V₀)) 3
  rw [← Category.assoc, hE, Category.assoc, Category.assoc, key]

/-- The coefficient-reindexing compatibility of the cap isomorphism:
the cap product with the relative fundamental class commutes with the conjugation action on relative
`Hom`-cochains, up to the fibrewise reindexing `epsLoc` of local chains. -/
def CapEpsStatement : Prop :=
  HomologicalComplex.homologyMap (hcAct relAct (GAct.ofRep principalSix V₀) k ≫
      relHomPull k (Rep.res principalSix.subtype V₀)) 2 ≫
    relativeHomCapTw k (Rep.res principalSix.subtype V₀) =
  (OrdinaryTopBoundaryComparison.relativeHomCapIso (Rep.res principalSix.subtype V₀)).hom ≫
    HomologicalComplex.homologyMap (epsLoc k V₀) 3

/-- **`S2` is equivariant**, given the coefficient-reindexing compatibility. -/
theorem S2_hcohAct (h : CapEpsStatement k V₀) :
    hcohAct relAct (GAct.ofRep principalSix V₀) k 2 ≫
        (OrdinaryTopBoundaryComparison.relativeHomCapIso (Rep.res principalSix.subtype V₀)).hom =
      (OrdinaryTopBoundaryComparison.relativeHomCapIso (Rep.res principalSix.subtype V₀)).hom ≫
        HomologicalComplex.homologyMap (epsLoc k V₀ ≫ Lspace k (Rep.res principalSix.subtype V₀)) 3 := by
  have hA := relativeHomCap_twisted_natural k (Rep.res principalSix.subtype V₀)
  unfold CapEpsStatement at h
  unfold hcohAct
  rw [HomologicalComplex.homologyMap_comp (epsLoc k V₀) (Lspace k (Rep.res principalSix.subtype V₀)) 3]
  have h1 : (HomologicalComplex.homologyMap (hcAct relAct (GAct.ofRep principalSix V₀) k) 2 ≫
      HomologicalComplex.homologyMap (relHomPull k (Rep.res principalSix.subtype V₀)) 2) ≫
        relativeHomCapTw k (Rep.res principalSix.subtype V₀) =
      (OrdinaryTopBoundaryComparison.relativeHomCapIso (Rep.res principalSix.subtype V₀)).hom ≫
        HomologicalComplex.homologyMap (epsLoc k V₀) 3 := by
    rw [← HomologicalComplex.homologyMap_comp]
    exact h
  have step : HomologicalComplex.homologyMap (hcAct relAct (GAct.ofRep principalSix V₀) k) 2 ≫
      (OrdinaryTopBoundaryComparison.relativeHomCapIso (Rep.res principalSix.subtype V₀)).hom =
      HomologicalComplex.homologyMap (hcAct relAct (GAct.ofRep principalSix V₀) k) 2 ≫
        (HomologicalComplex.homologyMap (relHomPull k (Rep.res principalSix.subtype V₀)) 2 ≫
          relativeHomCapTw k (Rep.res principalSix.subtype V₀) ≫
            HomologicalComplex.homologyMap (Lspace k (Rep.res principalSix.subtype V₀)) 3) :=
    (congrArg (fun m => HomologicalComplex.homologyMap
      (hcAct relAct (GAct.ofRep principalSix V₀) k) 2 ≫ m) hA).symm
  rw [step, ← Category.assoc, ← Category.assoc, h1]
  exact Category.assoc _ _ _

/-- The identity morphism of a module category acts as the identity. -/
theorem moduleCat_hom_id_apply {A : ModuleCat.{0} ℚ} (z : A) : (𝟙 A : A ⟶ A).hom z = z := rfl

/-- Application of a composite morphism of module categories. -/
theorem moduleCat_hom_comp_apply {A B C : ModuleCat.{0} ℚ} (f : A ⟶ B) (g : B ⟶ C) (z : A) :
    (f ≫ g).hom z = g.hom (f.hom z) := rfl

/-- **The library's neat-level duality `Θ = S1 ≫ S2⁻¹ ≫ S3` is equivariant for the conjugation
action of `k ∈ GL₃(ℤ)`**, given the coefficient-reindexing compatibility of the cap product. -/
theorem groupOrdinaryIso_equivariant (h : CapEpsStatement k V₀)
    (x : groupHomology (Rep.res principalSix.subtype V₀) 3)
    (σ : OrdinaryIncidenceChains.Cycles) :
    ((OrdinaryTopBoundaryComparison.groupOrdinaryIso (Rep.res principalSix.subtype V₀)).hom
        ((groupHomology.map (conjN principalSix k) (conjRep principalSix V₀ k) 3).hom x)).hom σ =
      V₀.ρ k (((OrdinaryTopBoundaryComparison.groupOrdinaryIso
        (Rep.res principalSix.subtype V₀)).hom x).hom
        (TernaryPoly.OrdinaryFullAction.cycleAction
          (TernaryPoly.OrdinaryFullAction.integral k⁻¹) σ)) := by
  let V : Rep.{0} ℚ principalSix := Rep.res principalSix.subtype V₀
  let S1 := bordifiedGroupLocalHomologyIso V 3
  let S2 := OrdinaryTopBoundaryComparison.relativeHomCapIso V
  let T := HomologicalComplex.homologyMap (epsLoc k V₀ ≫ Lspace k V) 3
  obtain ⟨y, hy⟩ : ∃ y, S1.inv.hom (S2.hom.hom y) = x :=
    ⟨S2.inv.hom (S1.hom.hom x), by
      rw [show S2.hom.hom (S2.inv.hom (S1.hom.hom x)) = S1.hom.hom x from
        congrArg (fun f => f.hom (S1.hom.hom x)) S2.inv_hom_id]
      exact congrArg (fun f => f.hom x) S1.hom_inv_id⟩
  let Θ := OrdinaryTopBoundaryComparison.groupOrdinaryIso V
  let S3 := OrdinaryTopBoundaryComparison.relativeOrdinaryCohomologyIso V
  have hcap : ∀ y' : ((EquivariantSingularSmall.homCochains
      OrdinaryTopBoundaryComparison.upstairsRelativeChains V).homology 2),
      Θ.hom.hom (S1.inv.hom (S2.hom.hom y')) = S3.hom.hom y' := fun y' =>
    congrArg (fun f => f.hom y') (OrdinaryTopBoundaryComparison.cappedClass_groupOrdinary V)
  have hS1x : S1.hom.hom x = S2.hom.hom y := by
    rw [← hy]
    exact congrArg (fun f => f.hom (S2.hom.hom y)) S1.inv_hom_id
  have hconj := (moduleCat_hom_comp_apply _ _ ((groupHomology.map (conjN principalSix k)
      (conjRep principalSix V₀ k) 3).hom x)).symm.trans
    ((congrArg (fun f => f.hom x) (conj_S1 k V₀)).trans (moduleCat_hom_comp_apply _ _ x))
  have hS2 := (moduleCat_hom_comp_apply _ _ y).symm.trans
    ((congrArg (fun f => f.hom y) (S2_hcohAct k V₀ h)).trans (moduleCat_hom_comp_apply _ _ y))
  have hcx := (moduleCat_hom_id_apply ((groupHomology.map (conjN principalSix k)
      (conjRep principalSix V₀ k) 3).hom x)).symm.trans (((congrArg (fun f => f.hom
        ((groupHomology.map (conjN principalSix k)
      (conjRep principalSix V₀ k) 3).hom x)) S1.hom_inv_id).symm.trans
      (congrArg (fun w => S1.inv.hom w) hconj)).trans
      ((congrArg (fun w => S1.inv.hom (T.hom w)) hS1x).trans
        (congrArg (fun w => S1.inv.hom w) hS2.symm)))
  have hΘx : Θ.hom.hom x = S3.hom.hom y := by
    rw [← hy]
    exact hcap y
  rw [hcx, hcap, hΘx]
  exact relativeOrdinaryCohomologyIso_hcohAct V₀ k y σ

end TernaryPeriodPolynomials.Argument.FiberModel
