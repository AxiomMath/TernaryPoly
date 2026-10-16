module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Naturality.HLevel
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.LevelG.BoundaryCap
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Lemma33Diagram
public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.DualityG

@[expose] public section


/-!
# `j^H_*`, `PD_∂^H` and the Lemma 3.3 diagram at an intermediate level `H`, descended from the neat-level geometric maps

Formalized by Claude Sonnet 5.5.

For a `GL₃(ℤ)`-module `V₀` and `Γ(6) ≤ H`: `repBd`, `repHc` are the actions of `H` on neat-level boundary homology (`bAct`) and
cohomology (`hcohAct`); `Γ(6)` acts trivially.  `jQH : QbdH → H₃(H, Res_H V₀)` is the descent of `Cor_{Γ(6)}^H ∘ j_*`
(`jH0_bdL`: invariance under `bAct`, from `boundaryToGroup_equivariant`), `PDQH : QbdH → H¹` the descent of
`avg_{H/Γ(6)} ∘ PD_∂` (`PD_avgBdH`: `PD_∂ ∘ avgBdH = avg ∘ PD_∂`, from `PDboundary_equivariant`), with values in the `H`-invariants
(`PDQH_invariant`).  `levelH_diagram_geom`: `F^H_{j^H_* q}(ℓ) = ⟨PD_∂^H q, ∂a⟩` with no scalar, proved from `thetaH_corN`,
`apartmentEvaluation_cAct`, `boundaryToGroup_equivariant`, the neat-level diagram `diagram_apply` and `PDboundary_equivariant`.
-/

open CategoryTheory Limits HomologicalComplex TernaryPoly TernaryPoly.IntegralGL3Congruence
  TernaryPoly.OrdinaryBoundaryActualEvaluation
  TernaryPoly.SymmetricSpaceBoundaryFull TernaryPoly.SymmetricSpaceBoundaryFullTransfer
  TernaryPoly.EquivariantSingularSmall TernaryPoly.SymmetricSpaceBoundaryIncidenceHomology
  TernaryPoly.RationalCohomologyDescent
  TernaryPoly.SingularLocalHomology TernaryPoly.ModThreeGoodAction TernaryPoly.OrdinaryBoundaryCone
open TernaryPeriodPolynomials.Argument.GroupHomology
open TernaryPeriodPolynomials.Argument.FiberModel
open TernaryPeriodPolynomials.Argument.Lemma33.LevelG
open TernaryPeriodPolynomials.Argument.Statements.Lemma33Diagram (PDboundary flatBoundaryPairing)

noncomputable section
namespace TernaryPeriodPolynomials.Argument.Lemma33.Naturality

open Representation
attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- Descent of a linear map along a surjection whose kernel is killed. -/
def descendLin {B Q C : Type*} [AddCommGroup B] [Module ℚ B] [AddCommGroup Q] [Module ℚ Q]
    [AddCommGroup C] [Module ℚ C] (q : B →ₗ[ℚ] Q) (hq : Function.Surjective q) (f : B →ₗ[ℚ] C)
    (hf : ∀ b, q b = 0 → f b = 0) : Q →ₗ[ℚ] C :=
  (LinearMap.ker q).liftQ f (fun b hb => hf b hb) ∘ₗ (LinearMap.quotKerEquivOfSurjective q hq).symm.toLinearMap

theorem descendLin_apply {B Q C : Type*} [AddCommGroup B] [Module ℚ B] [AddCommGroup Q] [Module ℚ Q]
    [AddCommGroup C] [Module ℚ C] (q : B →ₗ[ℚ] Q) (hq : Function.Surjective q) (f : B →ₗ[ℚ] C)
    (hf : ∀ b, q b = 0 → f b = 0) (b : B) : descendLin q hq f hf (q b) = f b := by
  have : (LinearMap.quotKerEquivOfSurjective q hq).symm (q b) = Submodule.Quotient.mk b := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  simp only [descendLin, LinearMap.comp_apply, LinearEquiv.coe_coe, this]
  exact Submodule.liftQ_apply _ _ _

section Reps

variable (V₀ : Rep.{0} ℚ IntegralGL)

/-- Neat-level boundary homology `H₃(∂X̄_Γ(6); 𝓜)`. -/
abbrev Bd : ModuleCat ℚ := (boundaryLocalChains (Rep.res principalSix.subtype V₀)).homology 3

/-- Neat-level boundary cohomology `H¹(∂X̄_Γ(6); 𝓜)` (Hom-cochains of the cover). -/
abbrev Hc : ModuleCat ℚ := (homCochains boundaryChains (Rep.res principalSix.subtype V₀)).homology 1

/-- The geometric action of `g` on boundary cohomology, as a linear map. -/
def hcL (g : IntegralGL) : Hc V₀ →ₗ[ℚ] Hc V₀ :=
  (hcohAct bdryAct (GAct.ofRep principalSix V₀) g 1).hom

theorem hcAct_of_mem' (γ : IntegralGL) (hγ : γ ∈ principalSix) :
    hcAct bdryAct (GAct.ofRep principalSix V₀) γ = 𝟙 _ := by
  apply HomologicalComplex.hom_ext
  intro m
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply rep_hom_ext'
  intro x
  change (conjHom (bdryAct.act m) (GAct.ofRep principalSix V₀) γ φ).hom x = φ.hom x
  refine (conjHom_apply _ _ γ φ x).trans ?_
  have h := Rep.hom_comm_apply φ ⟨γ, hγ⟩ ((bdryAct.act m).ρ γ⁻¹ x)
  change V₀.ρ γ (φ.hom ((fullBoundaryChains.X m).ρ γ⁻¹ x)) = φ.hom x
  refine Eq.trans h.symm ?_
  change φ.hom ((fullBoundaryChains.X m).ρ γ ((fullBoundaryChains.X m).ρ γ⁻¹ x)) = φ.hom x
  congr 1
  exact LinearMap.congr_fun (show (fullBoundaryChains.X m).ρ γ * (fullBoundaryChains.X m).ρ γ⁻¹ = 1 by
    rw [← map_mul, mul_inv_cancel, map_one]) x

/-- The geometric action on neat-level boundary homology, as a linear map. -/
def bdL (g : IntegralGL) : Bd V₀ →ₗ[ℚ] Bd V₀ := (homologyMap (bAct V₀ g) 3).hom

variable (H : Subgroup IntegralGL)

/-- The action of `H` on neat-level boundary homology. -/
def repBd : Representation ℚ ↥H (Bd V₀) where
  toFun h := bdL V₀ h.1
  map_one' := by
    ext x
    change (homologyMap (bAct V₀ 1) 3).hom x = x
    rw [bAct_one, homologyMap_id]; rfl
  map_mul' g h := by
    ext x
    change (homologyMap (bAct V₀ (g.1 * h.1)) 3).hom x =
      (homologyMap (bAct V₀ g.1) 3).hom ((homologyMap (bAct V₀ h.1) 3).hom x)
    rw [bAct_mul, homologyMap_comp]; rfl

/-- The action of `H` on neat-level boundary cohomology. -/
def repHc : Representation ℚ ↥H (Hc V₀) where
  toFun h := hcL V₀ h.1
  map_one' := by
    ext x
    change (homologyMap (hcAct bdryAct (GAct.ofRep principalSix V₀) 1) 1).hom x = x
    rw [hcAct_one, homologyMap_id]; rfl
  map_mul' g h := by
    ext x
    change (homologyMap (hcAct bdryAct (GAct.ofRep principalSix V₀) (g.1 * h.1)) 1).hom x =
      (homologyMap (hcAct bdryAct (GAct.ofRep principalSix V₀) g.1) 1).hom
        ((homologyMap (hcAct bdryAct (GAct.ofRep principalSix V₀) h.1) 1).hom x)
    rw [hcAct_mul, homologyMap_comp]; rfl

theorem repBd_NH (n : NH H) : repBd V₀ H n = 1 := by
  ext x
  change (homologyMap (bAct V₀ n.1.1) 3).hom x = x
  rw [bAct_of_mem V₀ ⟨n.1.1, Subgroup.mem_subgroupOf.mp n.2⟩, homologyMap_id]; rfl

theorem repHc_NH (n : NH H) : repHc V₀ H n = 1 := by
  ext x
  change (homologyMap (hcAct bdryAct (GAct.ofRep principalSix V₀) n.1.1) 1).hom x = x
  rw [hcAct_of_mem' V₀ n.1.1 (Subgroup.mem_subgroupOf.mp n.2), homologyMap_id]; rfl

end Reps

section Maps

variable (H : Subgroup IntegralGL) (hH : principalSix ≤ H) (V₀ : Rep.{0} ℚ IntegralGL)

/-- The corestriction `H₃(Γ(6), Res V₀) → H₃(H, Res_H V₀)`. -/
def corNH : groupHomology (Rep.res principalSix.subtype V₀) 3 →ₗ[ℚ] groupHomology (MH H V₀) 3 :=
  corN (NH H) (MH H V₀) 3 ∘ₗ (liftN H hH V₀).inv.hom

/-- `Cor_{Γ(6)}^H ∘ j_*` on neat-level boundary homology. -/
def jH0 : Bd V₀ →ₗ[ℚ] groupHomology (MH H V₀) 3 :=
  corNH H hH V₀ ∘ₗ (SymmetricSpaceBoundaryDuality.boundaryToGroup (Rep.res principalSix.subtype V₀) 3).hom

theorem corNH_cAct (g : ↥H) (x : groupHomology (Rep.res principalSix.subtype V₀) 3) :
    corNH H hH V₀ (cAct principalSix V₀ 3 g.1 x) = corNH H hH V₀ x := by
  have h := liftN_cAct H hH V₀ g ((liftN H hH V₀).inv.hom x)
  have h2 : (liftN H hH V₀).hom.hom ((liftN H hH V₀).inv.hom x) = x := by
    change ((liftN H hH V₀).inv ≫ (liftN H hH V₀).hom).hom x = x
    rw [Iso.inv_hom_id]; rfl
  rw [h2] at h
  have h3 : (liftN H hH V₀).inv.hom (cAct principalSix V₀ 3 g.1 x) =
      cAct (NH H) (MH H V₀) 3 g ((liftN H hH V₀).inv.hom x) := by
    rw [← h]
    change ((liftN H hH V₀).hom ≫ (liftN H hH V₀).inv).hom _ = _
    rw [Iso.hom_inv_id]; rfl
  change corN (NH H) (MH H V₀) 3 ((liftN H hH V₀).inv.hom (cAct principalSix V₀ 3 g.1 x)) = _
  rw [h3, corN_cAct]
  rfl

theorem jH0_bdL (g : ↥H) (c : Bd V₀) : jH0 H hH V₀ (bdL V₀ g.1 c) = jH0 H hH V₀ c := by
  have h := ConcreteCategory.congr_hom (boundaryToGroup_equivariant V₀ g.1) c
  change (corNH H hH V₀) ((SymmetricSpaceBoundaryDuality.boundaryToGroup (Rep.res principalSix.subtype V₀) 3).hom
    ((homologyMap (bAct V₀ g.1) 3).hom c)) = _
  rw [show (SymmetricSpaceBoundaryDuality.boundaryToGroup (Rep.res principalSix.subtype V₀) 3).hom
    ((homologyMap (bAct V₀ g.1) 3).hom c) = cAct principalSix V₀ 3 g.1
      ((SymmetricSpaceBoundaryDuality.boundaryToGroup (Rep.res principalSix.subtype V₀) 3).hom c) from h]
  rw [corNH_cAct]
  rfl

theorem avgBdH_eq : avgBdH H V₀ = avgR (NH H) (repBd V₀ H) := rfl

theorem jH0_avg (c : Bd V₀) : jH0 H hH V₀ (avgBdH H V₀ c) = jH0 H hH V₀ c := by
  unfold avgBdH
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  have : ∀ x : ↥H ⧸ NH H, jH0 H hH V₀ ((homologyMap (bAct V₀ x.out.1) 3).hom c) = jH0 H hH V₀ c :=
    fun x => jH0_bdL H hH V₀ x.out c
  simp only [this, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ (card_ne_zero_NH H), one_smul]

/-- **`j^H_*`**: the map `H₃(∂X̄_H; 𝓜) → H₃(H, Res_H V₀)` descended from the neat-level `Cor_{Γ(6)}^H ∘ j_*`. -/
def jQH : QbdH H V₀ →ₗ[ℚ] groupHomology (MH H V₀) 3 :=
  descendLin (qBdH H hH V₀).hom (qBdH_surjective H hH V₀) (jH0 H hH V₀) (fun c hc => by
    rw [← jH0_avg H hH V₀ c, (qBdH_ker H hH V₀ c).mp hc, map_zero])

theorem jQH_qBdH (c : Bd V₀) : jQH H hH V₀ ((qBdH H hH V₀).hom c) = jH0 H hH V₀ c :=
  descendLin_apply _ _ _ _ c

/-- Neat-level Poincaré duality followed by the `H/Γ(6)`-average on cohomology. -/
def pd0 : Bd V₀ →ₗ[ℚ] Hc V₀ :=
  avgR (NH H) (repHc V₀ H) ∘ₗ (PDboundary (Rep.res principalSix.subtype V₀)).hom

theorem PD_avgBdH (c : Bd V₀) :
    (PDboundary (Rep.res principalSix.subtype V₀)).hom (avgBdH H V₀ c) = pd0 H V₀ c := by
  unfold avgBdH pd0
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum, LinearMap.comp_apply, avgR]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  exact BR.PDboundary_equivariant x.out.1 V₀ c

/-- **`PD_∂^H`**: boundary Poincaré duality `H₃(∂X̄_H; 𝓜) → H¹(∂X̄_H; 𝓜)` (values in the `H`-invariant classes),
descended from the actual neat-level cap map. -/
def PDQH : QbdH H V₀ →ₗ[ℚ] Hc V₀ :=
  descendLin (qBdH H hH V₀).hom (qBdH_surjective H hH V₀) (pd0 H V₀) (fun c hc => by
    rw [← PD_avgBdH, (qBdH_ker H hH V₀ c).mp hc, map_zero])

theorem PDQH_qBdH (c : Bd V₀) : PDQH H hH V₀ ((qBdH H hH V₀).hom c) = pd0 H V₀ c :=
  descendLin_apply _ _ _ _ c

theorem PDQH_invariant (q : QbdH H V₀) (h : ↥H) : repHc V₀ H h (PDQH H hH V₀ q) = PDQH H hH V₀ q := by
  obtain ⟨c, rfl⟩ := qBdH_surjective H hH V₀ q
  rw [PDQH_qBdH]
  exact avgR_invariant (fun n hn => repHc_NH V₀ H ⟨n, hn⟩) _ h

/-- The cap/coefficient reindexing compatibility for every `k` (`DualityEquivariance.capEps`). -/
abbrev capAll : ∀ k : IntegralGL, CapEpsStatement k V₀ :=
  fun k => TernaryPeriodPolynomials.Argument.DualityEquivariance.capEps k V₀

theorem avg_identity (Ψ : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] ↥(MH H V₀)) :
    avg (stH H) (MH H V₀).ρ (NH H) Ψ OrdinaryTopBoundaryComparison.identityApartment =
      ((Fintype.card (↥H ⧸ NH H) : ℚ)⁻¹) • ∑ x : ↥H ⧸ NH H,
        V₀.ρ x.out.1 (Ψ (OrdinaryApartmentPresentation.frameCycle x.out.1⁻¹)) := by
  change ((Fintype.card (↥H ⧸ NH H) : ℚ)⁻¹) • avgSum (stH H) (MH H V₀).ρ (NH H) Ψ _ = _
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  unfold GroupHomology.term
  change V₀.ρ x.out.1 (Ψ (OrdinaryFullAction.cycleAction (OrdinaryFullAction.integral x.out.1⁻¹)
    (OrdinaryApartmentPresentation.frameCycle 1))) = _
  rw [OrdinaryFullAction.frameCycle_equivariant, mul_one]

/-- **Lemma 3.3 at level `H`, with the actual geometric objects.**  For `q ∈ H₃(∂X̄_H; 𝓜)` (coinvariants of the neat-level
boundary chains under `H/Γ(6)`), the value `F_z(ℓ)` of the `H`-level Steinberg functional of `z = j^H_* q` on the identity apartment
is the flat pairing `⟨PD_∂^H q, ∂a⟩`.  No scalar: the average over `H/Γ(6)` appears on both sides. -/
theorem levelH_diagram_geom (q : QbdH H V₀) :
    ((thetaH H hH V₀ (capAll V₀) (jQH H hH V₀ q)).val : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] ↥(MH H V₀))
        OrdinaryTopBoundaryComparison.identityApartment =
      flatBoundaryPairing (Rep.res principalSix.subtype V₀) (PDQH H hH V₀ q) := by
  obtain ⟨c, rfl⟩ := qBdH_surjective H hH V₀ q
  rw [jQH_qBdH, PDQH_qBdH]
  set x := (SymmetricSpaceBoundaryDuality.boundaryToGroup (Rep.res principalSix.subtype V₀) 3).hom c with hx
  have hy : (liftN H hH V₀).hom.hom ((liftN H hH V₀).inv.hom x) = x := by
    change ((liftN H hH V₀).inv ≫ (liftN H hH V₀).hom).hom x = x
    rw [Iso.inv_hom_id]; rfl
  change ((thetaH H hH V₀ (capAll V₀) (corN (NH H) (MH H V₀) 3 ((liftN H hH V₀).inv.hom x))).val :
    OrdinaryIncidenceChains.Cycles →ₗ[ℚ] ↥(MH H V₀)) OrdinaryTopBoundaryComparison.identityApartment = _
  rw [thetaH_corN, psiGen_H H hH V₀, hy, avg_identity]
  have hterm : ∀ g : IntegralGL, V₀.ρ g
      ((psiGen principalSix (MulEquiv.refl principalSix) V₀ x) (OrdinaryApartmentPresentation.frameCycle g⁻¹)) =
      (flatBoundaryPairing (Rep.res principalSix.subtype V₀)).hom (hcL V₀ g (PDboundary (Rep.res principalSix.subtype V₀) c)) := by
    intro g
    have e1 := apartmentEvaluation_cAct V₀ g x
    have e2 : cAct principalSix V₀ 3 g x = (SymmetricSpaceBoundaryDuality.boundaryToGroup
        (Rep.res principalSix.subtype V₀) 3).hom ((homologyMap (bAct V₀ g) 3).hom c) :=
      (ConcreteCategory.congr_hom (boundaryToGroup_equivariant V₀ g) c).symm
    rw [psiGen_apply]
    have e3 := TernaryPeriodPolynomials.Argument.Statements.Lemma33Diagram.diagram_apply
      (Rep.res principalSix.subtype V₀) ((homologyMap (bAct V₀ g) 3).hom c)
    have e4 := BR.PDboundary_equivariant g V₀ c
    calc V₀.ρ g (((OrdinaryTopBoundaryComparison.groupOrdinaryIso (Rep.res principalSix.subtype V₀)).hom.hom x).hom
          (OrdinaryApartmentPresentation.frameCycle g⁻¹))
        = OrdinaryTopBoundaryComparison.groupApartmentEvaluation (Rep.res principalSix.subtype V₀)
            (cAct principalSix V₀ 3 g x) := e1.symm
      _ = OrdinaryTopBoundaryComparison.groupApartmentEvaluation (Rep.res principalSix.subtype V₀)
            ((SymmetricSpaceBoundaryDuality.boundaryToGroup (Rep.res principalSix.subtype V₀) 3).hom
              ((homologyMap (bAct V₀ g) 3).hom c)) := by rw [e2]
      _ = flatBoundaryPairing (Rep.res principalSix.subtype V₀)
            (PDboundary (Rep.res principalSix.subtype V₀) ((homologyMap (bAct V₀ g) 3).hom c)) := e3
      _ = _ := by rw [e4]; rfl
  unfold pd0 avgR
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun y _ => ?_
  exact hterm y.out.1

end Maps

end TernaryPeriodPolynomials.Argument.Lemma33.Naturality
