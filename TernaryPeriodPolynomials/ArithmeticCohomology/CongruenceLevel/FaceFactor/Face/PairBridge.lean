module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.ConeFunctionals
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Const.Phi
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Face.PairingLifts

@[expose] public section


/-!
# The face pairings of mixed classes, tested by a rational functional, are sums over the flag orbits of `flagPhi` on explicit flag classes

Formalized by Claude Sonnet 5.5.  Paper: `ar:eq:facepair`.

`conePairC_line_functional`, `conePairC_plane_functional`: for any line (plane) data `d`, `e` with a complex pairing `π` and a rational functional `r : ℂ →ₗ[ℚ] ℚ`, any primitive `γ` of `d.z ∪ e.z`
for the rational pairing `π ≫ rHom r`: `r (conePairC π Ω d.cone e.cone) = ∑_o flagPhi o (faceCoord_o [flag cochain])` with the `flagPhi` (the corner functional of the Stokes cycle).
`lineFacePairM_functional`, `planeFacePairM_functional`: the same for the face pairings `lineFacePairM`, `planeFacePairM` of lifts of mixed classes.  This is the exact left-hand side of the fibre-integration identity (M3).
-/

open CategoryTheory Limits MonoidalCategory
open scoped MatrixGroups
open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
open TernaryPeriodPolynomials.Argument.GammaNStokes
open TernaryPoly.EquivariantSingularSmall TernaryPoly.BoundaryFaceResolutionComparison
open GeneralEisenstein
open TernaryPoly TernaryPoly.IntegralGL3Congruence
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open TernaryPoly.OrdinaryIncidence (Line Plane)
open TernaryPoly.SymmetricSpaceBoundaryFull

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

attribute [local instance] TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison.vertexAction

variable {W W' : Rep.{0} ℚ Γ6}

theorem conePairC_line_functional (π : W ⊗ W' ⟶ Rep.trivial ℚ Γ6 ℂ) (r : ℂ →ₗ[ℚ] ℚ) (d : LineDatum W) (e : LineDatum W')
    (γ : (prodComplex Γ6 RationalGL3 Line).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6))
    (hγ : (prodComplex Γ6 RationalGL3 Line).d 4 3 ≫ γ =
      (nerveDiagSystem Γ6 RationalGL3 Line).Δ 2 2 4 rfl ≫ (d.z ⊗ₘ e.z) ≫ (π ≫ rHom r)) :
    r (conePairC π stokesCycle d.cone e.cone) =
      ∑ o, flagPhi o ((faceCoord (stabilizer Γ6 o.out) (𝟙_ (Rep.{0} ℚ Γ6)) (1 : RationalGL3) o.out
        (fun g => g.2) 3).hom (clsS (homCochains (prodComplex Γ6 RationalGL3 Flag) (𝟙_ (Rep.{0} ℚ Γ6)))
          (lineFlagCochain (π ≫ rHom r) d.w e.z γ) (lineFlagCochain_cocycle (π ≫ rHom r) d e γ hγ))) := by
  rw [rHom_conePairC, LineDatum.conePair_eq_corner (π ≫ rHom r) stokesCycle d e stokesCycle_isCoinvCycle γ hγ]
  exact flagPhi_spec _ (lineFlagCochain_cocycle (π ≫ rHom r) d e γ hγ)

theorem conePairC_plane_functional (π : W ⊗ W' ⟶ Rep.trivial ℚ Γ6 ℂ) (r : ℂ →ₗ[ℚ] ℚ) (d : PlaneDatum W) (e : PlaneDatum W')
    (γ : (prodComplex Γ6 RationalGL3 Plane).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6))
    (hγ : (prodComplex Γ6 RationalGL3 Plane).d 4 3 ≫ γ =
      (nerveDiagSystem Γ6 RationalGL3 Plane).Δ 2 2 4 rfl ≫ (d.z ⊗ₘ e.z) ≫ (π ≫ rHom r)) :
    r (conePairC π stokesCycle d.cone e.cone) =
      ∑ o, flagPhi o ((faceCoord (stabilizer Γ6 o.out) (𝟙_ (Rep.{0} ℚ Γ6)) (1 : RationalGL3) o.out
        (fun g => g.2) 3).hom (clsS (homCochains (prodComplex Γ6 RationalGL3 Flag) (𝟙_ (Rep.{0} ℚ Γ6)))
          (planeFlagCochain (π ≫ rHom r) d.z e.w γ) (planeFlagCochain_cocycle (π ≫ rHom r) d e γ hγ))) := by
  rw [rHom_conePairC, PlaneDatum.conePair_eq_corner (π ≫ rHom r) stokesCycle d e stokesCycle_isCoinvCycle γ hγ]
  exact flagPhi_spec _ (planeFlagCochain_cocycle (π ≫ rHom r) d e γ hγ)

section Faces

open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.ConvergenceC4

variable {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V]
  (ρ : Representation ℂ (gammaN 6) V)

/-- **The face pairing of lifts of mixed classes of a line face, tested by `r`, is a sum over the flag orbits of `flagPhi`.** -/
theorem lineFacePairM_functional (i : LineFaces 6)
    (x : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ)))
    (y : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ.dual)))
    (d : LineDatum (qRep (MonoidHom.id Γ6) (rep6 ρ))) (e : LineDatum (qRep (MonoidHom.id Γ6) (rep6 ρ).dual))
    (hd : d.IsOn (labelOrbit Γ6 Line (lineFacesEquivOrbits i)))
    (he : e.IsOn (labelOrbit Γ6 Line (lineFacesEquivOrbits i)))
    (hdc : d.coord (lineFacesEquivOrbits i) =
      faceTauQ (fun i : LineFaces 6 => lineFacesEquivOrbits i) (fun i => lineOf i.rep) lineOf_rep_mem
        (fun i => ↥(gammaNQAt 6 i.rep)) (fun i => lineEmb i.rep) (fun i => lineEmb_injective i.rep)
        (fun i => lineEmb_range i.rep) (rep6 ρ) i
        (cmpH2 ρ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) x))
    (hec : e.coord (lineFacesEquivOrbits i) =
      faceTauQ (fun i : LineFaces 6 => lineFacesEquivOrbits i) (fun i => lineOf i.rep) lineOf_rep_mem
        (fun i => ↥(gammaNQAt 6 i.rep)) (fun i => lineEmb i.rep) (fun i => lineEmb_injective i.rep)
        (fun i => lineEmb_range i.rep) (rep6 ρ).dual i
        (cmpH2Dual ρ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) y))
    (r : ℂ →ₗ[ℚ] ℚ) (γ : (prodComplex Γ6 RationalGL3 Line).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6))
    (hγ : (prodComplex Γ6 RationalGL3 Line).d 4 3 ≫ γ =
      (nerveDiagSystem Γ6 RationalGL3 Line).Δ 2 2 4 rfl ≫ (d.z ⊗ₘ e.z) ≫ (evalC (MonoidHom.id Γ6) (rep6 ρ) ≫ rHom r)) :
    r (lineFacePairM ρ i x y) =
      ∑ o, flagPhi o ((faceCoord (stabilizer Γ6 o.out) (𝟙_ (Rep.{0} ℚ Γ6)) (1 : RationalGL3) o.out
        (fun g => g.2) 3).hom (clsS (homCochains (prodComplex Γ6 RationalGL3 Flag) (𝟙_ (Rep.{0} ℚ Γ6)))
          (lineFlagCochain (evalC (MonoidHom.id Γ6) (rep6 ρ) ≫ rHom r) d.w e.z γ)
          (lineFlagCochain_cocycle (evalC (MonoidHom.id Γ6) (rep6 ρ) ≫ rHom r) d e γ hγ))) := by
  rw [lineFace_pair_eq_cone ρ i x y d e hd he hdc hec]
  exact conePairC_line_functional (evalC (MonoidHom.id Γ6) (rep6 ρ)) r d e γ hγ

/-- … for a plane face. -/
theorem planeFacePairM_functional (i : PlaneFaces 6)
    (x : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ)))
    (y : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ.dual)))
    (d : PlaneDatum (qRep (MonoidHom.id Γ6) (rep6 ρ))) (e : PlaneDatum (qRep (MonoidHom.id Γ6) (rep6 ρ).dual))
    (hd : d.IsOn (labelOrbit Γ6 Plane (planeFacesEquivOrbits i)))
    (he : e.IsOn (labelOrbit Γ6 Plane (planeFacesEquivOrbits i)))
    (hdc : d.coord (planeFacesEquivOrbits i) =
      faceTauQ (fun i : PlaneFaces 6 => planeFacesEquivOrbits i) (fun i => planeOf (planeFaceRepr i)) planeOf_rep_mem
        (fun i => ↥(gammaNPAt 6 (planeFaceRepr i))) (fun i => planeEmb (planeFaceRepr i)) (fun i => planeEmb_injective (planeFaceRepr i))
        (fun i => planeEmb_range (planeFaceRepr i)) (rep6 ρ) i
        (cmpH2 ρ (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) x))
    (hec : e.coord (planeFacesEquivOrbits i) =
      faceTauQ (fun i : PlaneFaces 6 => planeFacesEquivOrbits i) (fun i => planeOf (planeFaceRepr i)) planeOf_rep_mem
        (fun i => ↥(gammaNPAt 6 (planeFaceRepr i))) (fun i => planeEmb (planeFaceRepr i)) (fun i => planeEmb_injective (planeFaceRepr i))
        (fun i => planeEmb_range (planeFaceRepr i)) (rep6 ρ).dual i
        (cmpH2Dual ρ (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) y))
    (r : ℂ →ₗ[ℚ] ℚ) (γ : (prodComplex Γ6 RationalGL3 Plane).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6))
    (hγ : (prodComplex Γ6 RationalGL3 Plane).d 4 3 ≫ γ =
      (nerveDiagSystem Γ6 RationalGL3 Plane).Δ 2 2 4 rfl ≫ (d.z ⊗ₘ e.z) ≫ (evalC (MonoidHom.id Γ6) (rep6 ρ) ≫ rHom r)) :
    r (planeFacePairM ρ i x y) =
      ∑ o, flagPhi o ((faceCoord (stabilizer Γ6 o.out) (𝟙_ (Rep.{0} ℚ Γ6)) (1 : RationalGL3) o.out
        (fun g => g.2) 3).hom (clsS (homCochains (prodComplex Γ6 RationalGL3 Flag) (𝟙_ (Rep.{0} ℚ Γ6)))
          (planeFlagCochain (evalC (MonoidHom.id Γ6) (rep6 ρ) ≫ rHom r) d.z e.w γ)
          (planeFlagCochain_cocycle (evalC (MonoidHom.id Γ6) (rep6 ρ) ≫ rHom r) d e γ hγ))) := by
  rw [planeFace_pair_eq_cone ρ i x y d e hd he hdc hec]
  exact conePairC_plane_functional (evalC (MonoidHom.id Γ6) (rep6 ρ)) r d e γ hγ

end Faces

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
