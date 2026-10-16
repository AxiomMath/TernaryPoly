module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.NFT2PlaneMain

@[expose] public section


/-!
# The fibre-integration identity for planes: `M3PlaneAt flagEval 3`

Formalized by Claude Sonnet 5.5.

`m3Plane`: with `κ i = 3` for every plane face, `∑_o λ_o(flag class of the cut corner cocycle) = 3 · r (can6P ρ i x y)`.  Proof: `planeSum_general` reduces the sum over all flag orbits to the sum over the cusp representatives of
the flag groups `Stab (pflag h (wOf c))` (`Pc_orbit_inj`, `Pc_orbit_surj`), `nft2_plane` replaces the nerve data by normal-form data flagwise, and `planeSum_can` evaluates the sum.
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
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

attribute [local instance] TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison.vertexAction

open scoped Classical in
/-- **(M3), planes, for S3's evaluation data.** -/
theorem m3Plane : M3PlaneAt flagEval (fun _ => 3) := by
  intro V _ _ _ _ _ ρ i x y d e hd he hdc hec r γ hγ
  have hN : 3 ≤ 6 := by norm_num
  have hγ' := cutγ_plane_primitive (evalC (MonoidHom.id Γ6) (rep6 ρ) ≫ rHom r) d e γ hγ
    (labelOrbit Γ6 Plane (planeFacesEquivOrbits i)) (labelOrbit_invariant _) hd he
  rw [planeSum_general (evalC (MonoidHom.id Γ6) (rep6 ρ) ≫ rHom r) d e γ hγ
    (labelOrbit Γ6 Plane (planeFacesEquivOrbits i)) (labelOrbit_invariant _) hd he (planeOf (planeFaceRepr i)) (planeOf_rep_mem i)
    (fun c : ↥(cuspReps hN).R => pflag (planeFaceRepr i) (wOf (c : RationalLine2)))
    (fun c => flagPlaneOf_pflag _ _)
    (fun c c' hcc' => Subtype.ext (Pc_orbit_inj hN (planeFaceRepr i) c c' c.2 c'.2 hcc'))
    (fun o ho => by
      obtain ⟨c, hc, hco⟩ := Pc_orbit_surj hN (planeFaceRepr i) (planeFacesEquivOrbits i) (planeOf_rep_mem i) o ho
      exact ⟨⟨c, hc⟩, hco⟩)]
  obtain ⟨z, z', hzx, hzy, hU, hmix, hmix', gb, hrad, hd', w', hw', hΘ, hcls⟩ := nft2_plane hN ρ i x y d e hdc hec r
    (qReprG (dualRepG (planeRepAt ρ i)).ρ) (fun _ _ => rfl)
    (pairOf (evalC (MonoidHom.id Γ6) (rep6 ρ) ≫ rHom r)) (fun _ _ => rfl) _ hγ'
  rw [Finset.sum_congr rfl (fun c _ => hcls c)]
  exact planeSum_can hN (planeFaceRepr i) (planeRepAt ρ i) (qReprG (dualRepG (planeRepAt ρ i)).ρ) (fun _ _ => rfl)
    (pairOf (evalC (MonoidHom.id Γ6) (rep6 ρ) ≫ rHom r)) r (fun _ _ => rfl) x y z z' hzx hzy hU hmix hmix' gb hrad hd' w' hw' hΘ

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
