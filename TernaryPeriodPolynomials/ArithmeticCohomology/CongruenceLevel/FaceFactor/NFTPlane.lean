module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.NFTLine

@[expose] public section


open CategoryTheory Limits MonoidalCategory
open scoped MatrixGroups
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPeriodPolynomials.Argument.GammaNStokes
open TernaryPoly.BoundaryFaceResolutionComparison
open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
open TernaryPoly.EquivariantSingularSmall
open GeneralEisenstein
open TernaryPoly TernaryPoly.IntegralGL3Congruence
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open TernaryPoly.OrdinaryIncidence (Line Plane)
open TernaryPoly.SymmetricSpaceBoundaryFull

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

attribute [local instance] TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison.vertexAction


/-!
# NFT-1 for planes: the bar cochain of a plane datum at the plane `planeOf h` is cohomologous to any representing cocycle

Formalized by Claude Sonnet 5.5.

`nft1_plane`: for a plane face `i`, a mixed class `x` of the plane group `gammaNPAt 6 (planeFaceRepr i)` and a datum `d` whose Shapiro coordinate is the transport of `x`, the bar cochain of `d.z` at `planeOf (planeFaceRepr i)`, pulled back to the face group, differs from any representing cocycle by a coboundary.
-/

section Plane

open TernaryPeriodPolynomials.Argument.GammaNFacesFull TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.ConvergenceC4

variable {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V]
  (ρ₀ : Representation ℂ (gammaN 6) V) (ρ₆ : Representation ℂ Γ6 V)
  (hρ : ∀ (s : gammaN 6) (v : V), ρ₆ (gammaSixEquiv s) v = ρ₀ s v)

/-- The cochain `(a, c) ↦ z̄_d(σ a, σ c)` of the face group `Q = Γ(6) ∩ h⁻¹Qh` from the bar cochain of `d.z` at the plane `b = planeOf h`. -/
def planeZbar (i : PlaneFaces 6) (d : PlaneDatum (qRep (MonoidHom.id Γ6) ρ₆)) (a c : ↥(gammaNPAt 6 (planeFaceRepr i))) : V :=
  barCochain (MulAction.stabilizer Γ6 (planeOf (planeFaceRepr i))) (1 : RationalGL3) (planeOf (planeFaceRepr i)) d.z
    ![faceSigma (fun i : PlaneFaces 6 => planeOf (planeFaceRepr i)) (fun i => ↥(gammaNPAt 6 (planeFaceRepr i))) (fun i => planeEmb (planeFaceRepr i))
      (fun i => planeEmb_range (planeFaceRepr i)) i a,
      faceSigma (fun i : PlaneFaces 6 => planeOf (planeFaceRepr i)) (fun i => ↥(gammaNPAt 6 (planeFaceRepr i))) (fun i => planeEmb (planeFaceRepr i))
      (fun i => planeEmb_range (planeFaceRepr i)) i c]

theorem planeZbar_cocycle (i : PlaneFaces 6) (d : PlaneDatum (qRep (MonoidHom.id Γ6) ρ₆)) :
    (inhomogeneousCochains.d (Rep.res (MulAction.stabilizer Γ6 (planeOf (planeFaceRepr i))).subtype (qRepG ρ₆)) 2).hom
      (fun x => barCochain (MulAction.stabilizer Γ6 (planeOf (planeFaceRepr i))) (1 : RationalGL3) (planeOf (planeFaceRepr i)) d.z x) = 0 :=
  barCochain_cocycle (MulAction.stabilizer Γ6 (planeOf (planeFaceRepr i))) (qRepG ρ₆) (1 : RationalGL3) (planeOf (planeFaceRepr i))
    (fun g => g.2) d.z d.hz

/-- **NFT-1**: the bar cochain of `d.z` at the plane `b = planeOf h`, pulled back to the face group `Q`, is cohomologous to any cocycle `zx` representing `x`. -/
theorem nft1_plane (i : PlaneFaces 6)
    (x : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ₀)))
    (d : PlaneDatum (qRep (MonoidHom.id Γ6) ρ₆))
    (hdc : d.coord (planeFacesEquivOrbits i) =
      faceTauQ (fun i : PlaneFaces 6 => planeFacesEquivOrbits i) (fun i => planeOf (planeFaceRepr i)) planeOf_rep_mem
        (fun i => ↥(gammaNPAt 6 (planeFaceRepr i))) (fun i => planeEmb (planeFaceRepr i)) (fun i => planeEmb_injective (planeFaceRepr i))
        (fun i => planeEmb_range (planeFaceRepr i)) ρ₆ i
        (cmpGen ρ₀ ρ₆ hρ (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) x))
    (zx : groupCohomology.cocycles₂ (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ₀)))
    (hzx : groupCohomology.H2π _ zx = x) :
    ∃ κ : ↥(gammaNPAt 6 (planeFaceRepr i)) → V, ∀ a c : ↥(gammaNPAt 6 (planeFaceRepr i)),
      planeZbar ρ₆ i d a c = zx.1 (a, c) +
        (ρ₀ (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp) a) (κ c) - κ (a * c) + κ a) := by
  have key := coord_at_b (fun i : PlaneFaces 6 => planeFacesEquivOrbits i) (fun i => planeOf (planeFaceRepr i)) planeOf_rep_mem
    (fun i => ↥(gammaNPAt 6 (planeFaceRepr i))) (fun i => planeEmb (planeFaceRepr i)) (fun i => planeEmb_injective (planeFaceRepr i))
    (fun i => planeEmb_range (planeFaceRepr i)) ρ₆ i d.cls (cmpGen ρ₀ ρ₆ hρ (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) x) hdc
  have hc2 : (faceCoord (MulAction.stabilizer Γ6 (planeOf (planeFaceRepr i))) (qRepG ρ₆) (1 : RationalGL3) (planeOf (planeFaceRepr i))
      (fun g => g.2) 2).hom d.cls =
      (groupCohomology.π (Rep.res (MulAction.stabilizer Γ6 (planeOf (planeFaceRepr i))).subtype (qRepG ρ₆)) 2).hom
        (groupCohomology.cocyclesMk (fun x => barCochain (MulAction.stabilizer Γ6 (planeOf (planeFaceRepr i))) (1 : RationalGL3) (planeOf (planeFaceRepr i)) d.z x)
          (planeZbar_cocycle ρ₆ i d)) :=
    faceCoord_clsS_eq (MulAction.stabilizer Γ6 (planeOf (planeFaceRepr i))) (qRepG ρ₆) (1 : RationalGL3) (planeOf (planeFaceRepr i))
      (fun g => g.2) (m := 1) d.z d.hz
  rw [hc2] at key
  obtain ⟨hx0, hπ⟩ := pi_cocyclesMk_eq_H2π (Rep.res (MulAction.stabilizer Γ6 (planeOf (planeFaceRepr i))).subtype (qRepG ρ₆))
    (fun x => barCochain (MulAction.stabilizer Γ6 (planeOf (planeFaceRepr i))) (1 : RationalGL3) (planeOf (planeFaceRepr i)) d.z x) (planeZbar_cocycle ρ₆ i d)
  rw [hπ, ← hzx] at key
  have hcm : cmpGen ρ₀ ρ₆ hρ (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp))
      (groupCohomology.H2π (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ₀)) zx) =
      groupCohomology.H2π _ (groupCohomology.mapCocycles₂ (MonoidHom.id _) (EdgeNat.comparison (MonoidHom.id _)
        (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ₀))
        (Rep.res ((gammaSixEquiv : gammaN 6 →* Γ6).comp (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)))
          (Rep.of ρ₆)) LinearMap.id (fun s v => (hρ _ v).symm)) zx) :=
    EdgeNat.h2Map_π _ _ _ _ _ zx
  rw [hcm] at key
  have key2 : (groupCohomology.H2π (qRepG (ρ₆.comp (planeEmb (planeFaceRepr i))))).hom
      (groupCohomology.mapCocycles₂ (faceSigma (fun i : PlaneFaces 6 => planeOf (planeFaceRepr i)) (fun i => ↥(gammaNPAt 6 (planeFaceRepr i)))
        (fun i => planeEmb (planeFaceRepr i)) (fun i => planeEmb_range (planeFaceRepr i)) i)
        (faceQId (fun i : PlaneFaces 6 => planeOf (planeFaceRepr i)) (fun i => ↥(gammaNPAt 6 (planeFaceRepr i))) (fun i => planeEmb (planeFaceRepr i))
          (fun i => planeEmb_range (planeFaceRepr i)) ρ₆ i) ⟨_, hx0⟩) =
      (groupCohomology.H2π (qRepG (ρ₆.comp (planeEmb (planeFaceRepr i))))).hom
        (qCoc (ρ₆.comp (planeEmb (planeFaceRepr i))) (groupCohomology.mapCocycles₂ (MonoidHom.id _) (EdgeNat.comparison (MonoidHom.id _)
          (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ₀))
          (Rep.res ((gammaSixEquiv : gammaN 6 →* Γ6).comp (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)))
            (Rep.of ρ₆)) LinearMap.id (fun s v => (hρ _ v).symm)) zx)) := by
    refine Eq.trans ?_ (key.trans (qH2_π _ _))
    exact (groupCohomology.H2π_comp_map_apply _ _ _).symm
  obtain ⟨κ, hκ⟩ := coboundary_of_H2π_eq _ _ _ key2
  refine ⟨κ, fun a c => ?_⟩
  have h1 := hκ a c
  have e1 : (groupCohomology.mapCocycles₂ (faceSigma (fun i : PlaneFaces 6 => planeOf (planeFaceRepr i)) (fun i => ↥(gammaNPAt 6 (planeFaceRepr i)))
        (fun i => planeEmb (planeFaceRepr i)) (fun i => planeEmb_range (planeFaceRepr i)) i)
        (faceQId (fun i : PlaneFaces 6 => planeOf (planeFaceRepr i)) (fun i => ↥(gammaNPAt 6 (planeFaceRepr i))) (fun i => planeEmb (planeFaceRepr i))
          (fun i => planeEmb_range (planeFaceRepr i)) ρ₆ i) ⟨_, hx0⟩).1 (a, c) = planeZbar ρ₆ i d a c := rfl
  have e2 : (qCoc (ρ₆.comp (planeEmb (planeFaceRepr i))) (groupCohomology.mapCocycles₂ (MonoidHom.id _) (EdgeNat.comparison (MonoidHom.id _)
          (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ₀))
          (Rep.res ((gammaSixEquiv : gammaN 6 →* Γ6).comp (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)))
            (Rep.of ρ₆)) LinearMap.id (fun s v => (hρ _ v).symm)) zx)).1 (a, c) = zx.1 (a, c) := rfl
  have e3 : ((qRepG (ρ₆.comp (planeEmb (planeFaceRepr i)))).ρ a) (κ c) =
      ρ₀ (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp) a) (κ c) := by
    exact hρ _ _
  rw [e1, e2, e3] at h1
  exact h1

end Plane

section Instances

open TernaryPeriodPolynomials.Argument.GammaNFacesFull TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.ConvergenceC4

variable {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V]
  (ρ : Representation ℂ (gammaN 6) V)

omit [Module ℚ V] [IsScalarTower ℚ ℂ V] in
/-- **NFT-1 for the dual datum**: the same statement for the dual representation, in the form of `planeFace_exists_lifts`. -/
theorem nft1_plane_dual (i : PlaneFaces 6)
    (y : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ.dual)))
    (e : PlaneDatum (qRep (MonoidHom.id Γ6) (rep6 ρ).dual))
    (hec : e.coord (planeFacesEquivOrbits i) =
      faceTauQ (fun i : PlaneFaces 6 => planeFacesEquivOrbits i) (fun i => planeOf (planeFaceRepr i)) planeOf_rep_mem
        (fun i => ↥(gammaNPAt 6 (planeFaceRepr i))) (fun i => planeEmb (planeFaceRepr i)) (fun i => planeEmb_injective (planeFaceRepr i))
        (fun i => planeEmb_range (planeFaceRepr i)) (rep6 ρ).dual i
        (cmpH2Dual ρ (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) y))
    (zy : groupCohomology.cocycles₂ (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ.dual)))
    (hzy : groupCohomology.H2π _ zy = y) :
    ∃ κ : gammaNPAt 6 (planeFaceRepr i) → Module.Dual ℂ V, ∀ a c, planeZbar (rep6 ρ).dual i e a c = zy.1 (a, c) +
      (ρ.dual (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp) a) (κ c) - κ (a * c) + κ a) :=
  nft1_plane ρ.dual (rep6 ρ).dual (rep6_dual_hρ ρ) i y e hec zy hzy

/-- **NFT-1** for the transported representation `rep6 ρ`, in the form of `planeFace_exists_lifts`. -/
theorem nft1_plane_rep6 (i : PlaneFaces 6)
    (x : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ)))
    (d : PlaneDatum (qRep (MonoidHom.id Γ6) (rep6 ρ)))
    (hdc : d.coord (planeFacesEquivOrbits i) =
      faceTauQ (fun i : PlaneFaces 6 => planeFacesEquivOrbits i) (fun i => planeOf (planeFaceRepr i)) planeOf_rep_mem
        (fun i => ↥(gammaNPAt 6 (planeFaceRepr i))) (fun i => planeEmb (planeFaceRepr i)) (fun i => planeEmb_injective (planeFaceRepr i))
        (fun i => planeEmb_range (planeFaceRepr i)) (rep6 ρ) i
        (cmpH2 ρ (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) x))
    (zx : groupCohomology.cocycles₂ (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ)))
    (hzx : groupCohomology.H2π _ zx = x) :
    ∃ κ : gammaNPAt 6 (planeFaceRepr i) → V, ∀ a c, planeZbar (rep6 ρ) i d a c = zx.1 (a, c) +
      (ρ (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp) a) (κ c) - κ (a * c) + κ a) :=
  nft1_plane ρ (rep6 ρ) (rep6_hρ ρ) i x d hdc zx hzx

end Instances

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
