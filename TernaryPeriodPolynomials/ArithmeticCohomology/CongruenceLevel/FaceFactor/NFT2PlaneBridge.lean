module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.NFT2PlaneCore
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.Plane.Wiring
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.HSNormalFormPlane
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.M3Cut

@[expose] public section


/-!
# NFT-2 for planes: bridges between the rational model and the complex face-group data

Formalized by Claude Sonnet 5.5.

`qRep_comp_embP`, `qRepDual_comp_embP`: the rational model restricted along `planeEmb` is `planeRepAt ρ i` (resp. its literal contragredient); `cocycle_dd2P`, `cocycle_dd2_dualP`: `dd2` of the values of a complex two-cocycle; `pairOf_evalP`: `pairOf (evalC ≫ rHom r) v φ = r (φ v)`.
-/

open CategoryTheory Limits MonoidalCategory
open scoped MatrixGroups
open CongruenceSubgroup Matrix
open TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
open TernaryPoly.EquivariantSingularSmall TernaryPoly.BoundaryFaceResolutionComparison
open GeneralEisenstein
open TernaryPoly TernaryPoly.IntegralGL3Congruence
open TernaryPoly.OrdinaryIncidence (Line Plane)
open TernaryPoly.SymmetricSpaceBoundaryFull
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPeriodPolynomials.Argument.GammaNStokes
open TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open TernaryPeriodPolynomials.Argument.GammaNFacesFull TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.FlagH3
open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.HeckeDuality
  TernaryPoly.RankTwoAugmentedFrames TernaryPoly.BinaryModularSymbol

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

attribute [local instance] TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison.vertexAction

section BridgeP

variable {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V]
  (ρ : Representation ℂ (gammaN 6) V) (i : PlaneFaces 6)

example : Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ.dual) =
    dualRepG (planeRepAt ρ i) := rfl

theorem qRep_comp_embP (g : ↥(gammaNPAt 6 (planeFaceRepr i))) (v : V) :
    ((qRep (MonoidHom.id Γ6) (rep6 ρ)).ρ.comp (planeEmb (planeFaceRepr i))) g v = (planeRepAt ρ i).ρ g v := by
  show rep6 ρ (planeEmb (planeFaceRepr i) g) v = ρ (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp) g) v
  exact rep6_hρ ρ _ v

omit [Module ℚ V] [IsScalarTower ℚ ℂ V] in
theorem qRepDual_comp_embP (g : ↥(gammaNPAt 6 (planeFaceRepr i))) (φ : Module.Dual ℂ V) :
    ((qRep (MonoidHom.id Γ6) (rep6 ρ).dual).ρ.comp (planeEmb (planeFaceRepr i))) g φ = (dualRepG (planeRepAt ρ i)).ρ g φ := by
  show (rep6 ρ).dual (planeEmb (planeFaceRepr i) g) φ =
    (ρ.dual (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp) g)) φ
  exact rep6_dual_hρ ρ _ φ

theorem cocycle_dd2P (z : groupCohomology.cocycles₂ (planeRepAt ρ i)) :
    dd2 ((qRep (MonoidHom.id Γ6) (rep6 ρ)).ρ.comp (planeEmb (planeFaceRepr i))) (fun a c => z.1 (a, c)) = 0 := by
  funext g h j
  have := (groupCohomology.mem_cocycles₂_iff z.1).1 z.2 g h j
  simp only [dd2, Pi.zero_apply]
  rw [qRep_comp_embP]
  have e : ((planeRepAt ρ i).ρ g) (z.1 (h, j)) - z.1 (g * h, j) + z.1 (g, h * j) - z.1 (g, h) =
      ((planeRepAt ρ i).ρ g) (z.1 (h, j)) + z.1 (g, h * j) - (z.1 (g * h, j) + z.1 (g, h)) := by abel
  exact e.trans (sub_eq_zero.2 this.symm)

omit [Module ℚ V] [IsScalarTower ℚ ℂ V] in
theorem cocycle_dd2_dualP (z : groupCohomology.cocycles₂ (dualRepG (planeRepAt ρ i))) :
    dd2 ((qRep (MonoidHom.id Γ6) (rep6 ρ).dual).ρ.comp (planeEmb (planeFaceRepr i))) (fun a c => z.1 (a, c)) = 0 := by
  funext g h j
  have := (groupCohomology.mem_cocycles₂_iff z.1).1 z.2 g h j
  simp only [dd2, Pi.zero_apply]
  rw [qRepDual_comp_embP]
  have e : ((dualRepG (planeRepAt ρ i)).ρ g) (z.1 (h, j)) - z.1 (g * h, j) + z.1 (g, h * j) - z.1 (g, h) =
      ((dualRepG (planeRepAt ρ i)).ρ g) (z.1 (h, j)) + z.1 (g, h * j) - (z.1 (g * h, j) + z.1 (g, h)) := by abel
  exact e.trans (sub_eq_zero.2 this.symm)

theorem pairOf_evalP (r : ℂ →ₗ[ℚ] ℚ) (v : V) (φ : Module.Dual ℂ V) :
    pairOf (evalC (MonoidHom.id Γ6) (rep6 ρ) ≫ rHom r) v φ = r (φ v) := rfl

omit [Module ℚ V] [IsScalarTower ℚ ℂ V] in
theorem nft1_plane_dual' (y : groupCohomology.H2 (dualRepG (planeRepAt ρ i)))
    (e : PlaneDatum (qRep (MonoidHom.id Γ6) (rep6 ρ).dual))
    (hec : e.coord (planeFacesEquivOrbits i) =
      faceTauQ (fun i : PlaneFaces 6 => planeFacesEquivOrbits i) (fun i => planeOf (planeFaceRepr i)) planeOf_rep_mem
        (fun i => ↥(gammaNPAt 6 (planeFaceRepr i))) (fun i => planeEmb (planeFaceRepr i)) (fun i => planeEmb_injective (planeFaceRepr i))
        (fun i => planeEmb_range (planeFaceRepr i)) (rep6 ρ).dual i
        (cmpH2Dual ρ (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) y))
    (zy : groupCohomology.cocycles₂ (dualRepG (planeRepAt ρ i)))
    (hzy : groupCohomology.H2π _ zy = y) :
    ∃ κ' : gammaNPAt 6 (planeFaceRepr i) → Module.Dual ℂ V, ∀ a c, planeZbar (rep6 ρ).dual i e a c = zy.1 (a, c) +
      ((dualRepG (planeRepAt ρ i)).ρ a (κ' c) - κ' (a * c) + κ' a) :=
  nft1_plane_dual ρ i y e hec zy hzy

theorem planeZbar_eq_zbarP (i : PlaneFaces 6) (d : PlaneDatum (qRep (MonoidHom.id Γ6) (rep6 ρ))) (a c : ↥(gammaNPAt 6 (planeFaceRepr i))) :
    planeZbar (rep6 ρ) i d a c = zbarP i d a c := by
  unfold planeZbar zbarP
  congr 1
  funext j
  fin_cases j <;> rfl

omit [Module ℚ V] [IsScalarTower ℚ ℂ V] in
theorem planeZbar_eq_zbarP_dual (i : PlaneFaces 6) (d : PlaneDatum (qRep (MonoidHom.id Γ6) (rep6 ρ).dual)) (a c : ↥(gammaNPAt 6 (planeFaceRepr i))) :
    planeZbar (rep6 ρ).dual i d a c = zbarP i d a c := by
  unfold planeZbar zbarP
  congr 1
  funext j
  fin_cases j <;> rfl

/-- The values of a two-cocycle of the face group, as a cochain with values in the rational model. -/
def cocFn (z : groupCohomology.cocycles₂ (planeRepAt ρ i)) (a c : ↥(gammaNPAt 6 (planeFaceRepr i))) :
    (qRep (MonoidHom.id Γ6) (rep6 ρ)) := z.1 (a, c)

omit [Module ℚ V] [IsScalarTower ℚ ℂ V] in
/-- The same for the literal contragredient. -/
def cocFnDual (z : groupCohomology.cocycles₂ (dualRepG (planeRepAt ρ i))) (a c : ↥(gammaNPAt 6 (planeFaceRepr i))) :
    (qRep (MonoidHom.id Γ6) (rep6 ρ).dual) := z.1 (a, c)

/-- The nerve cochain of the datum `d` is the sum of a representing cocycle and a coboundary. -/
theorem zbarP_decomp (x : groupCohomology.H2 (planeRepAt ρ i)) (d : PlaneDatum (qRep (MonoidHom.id Γ6) (rep6 ρ)))
    (hdc : d.coord (planeFacesEquivOrbits i) =
        faceTauQ (fun i : PlaneFaces 6 => planeFacesEquivOrbits i) (fun i => planeOf (planeFaceRepr i)) planeOf_rep_mem
          (fun i => ↥(gammaNPAt 6 (planeFaceRepr i))) (fun i => planeEmb (planeFaceRepr i)) (fun i => planeEmb_injective (planeFaceRepr i))
          (fun i => planeEmb_range (planeFaceRepr i)) (rep6 ρ) i
          (cmpH2 ρ (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) x))
    (z : groupCohomology.cocycles₂ (planeRepAt ρ i)) (hz : groupCohomology.H2π (planeRepAt ρ i) z = x) :
    ∃ κ : ↥(gammaNPAt 6 (planeFaceRepr i)) → V, zbarP i d = cocFn ρ i z +
      dd1 ((qRep (MonoidHom.id Γ6) (rep6 ρ)).ρ.comp (planeEmb (planeFaceRepr i))) κ := by
  obtain ⟨κ, hκ⟩ := nft1_plane_rep6 ρ i x d hdc z hz
  refine ⟨κ, ?_⟩
  funext a c
  rw [← planeZbar_eq_zbarP, hκ a c]
  simp only [Pi.add_apply, dd1, qRep_comp_embP]
  rfl

omit [Module ℚ V] [IsScalarTower ℚ ℂ V] in
theorem zbarP_decomp_dual (y : groupCohomology.H2 (dualRepG (planeRepAt ρ i))) (e : PlaneDatum (qRep (MonoidHom.id Γ6) (rep6 ρ).dual))
    (hec : e.coord (planeFacesEquivOrbits i) =
      faceTauQ (fun i : PlaneFaces 6 => planeFacesEquivOrbits i) (fun i => planeOf (planeFaceRepr i)) planeOf_rep_mem
        (fun i => ↥(gammaNPAt 6 (planeFaceRepr i))) (fun i => planeEmb (planeFaceRepr i)) (fun i => planeEmb_injective (planeFaceRepr i))
        (fun i => planeEmb_range (planeFaceRepr i)) (rep6 ρ).dual i
        (cmpH2Dual ρ (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) y))
    (z : groupCohomology.cocycles₂ (dualRepG (planeRepAt ρ i))) (hz : groupCohomology.H2π _ z = y) :
    ∃ κ : ↥(gammaNPAt 6 (planeFaceRepr i)) → Module.Dual ℂ V, zbarP i e = cocFnDual ρ i z +
      dd1 ((qRep (MonoidHom.id Γ6) (rep6 ρ).dual).ρ.comp (planeEmb (planeFaceRepr i))) κ := by
  obtain ⟨κ, hκ⟩ := nft1_plane_dual' ρ i y e hec z hz
  refine ⟨κ, ?_⟩
  funext a c
  rw [← planeZbar_eq_zbarP_dual, hκ a c]
  simp only [Pi.add_apply, dd1, qRepDual_comp_embP]
  rfl

theorem pairing_convP (r : ℂ →ₗ[ℚ] ℚ)
    (ρ' : Representation ℚ ↥(gammaNPAt 6 (planeFaceRepr i)) (dualRepG (planeRepAt ρ i)))
    (hρ' : ∀ g x, ρ' g x = (dualRepG (planeRepAt ρ i)).ρ g x)
    (eQ : planeRepAt ρ i →ₗ[ℚ] dualRepG (planeRepAt ρ i) →ₗ[ℚ] ℚ)
    (he : ∀ x y, eQ x y = r (Module.Dual.eval ℂ (planeRepAt ρ i) x y))
    (v : V) (φ : Module.Dual ℂ V) (g : ↥(gammaNPAt 6 (planeFaceRepr i))) :
    pairOf (evalC (MonoidHom.id Γ6) (rep6 ρ) ≫ rHom r) v
      (((qRep (MonoidHom.id Γ6) (rep6 ρ).dual).ρ.comp (planeEmb (planeFaceRepr i))) g φ) = eQ v (ρ' g φ) := by
  rw [hρ' g φ, qRepDual_comp_embP, he]
  rfl

end BridgeP

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
