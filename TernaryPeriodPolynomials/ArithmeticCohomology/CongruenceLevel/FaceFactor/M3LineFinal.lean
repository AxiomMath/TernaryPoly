module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.NFTLine2
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.M3Cut
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.Flag.EvalInst
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.Flag.CuspOrbits

@[expose] public section


/-!
# The fibre-integration identity for lines (M3LineC)

Formalized by Claude Sonnet 5.5.

`m3Line : M3LineAt flagEval (fun _ => -3)`: for the cut primitive the sum over the flag orbits of the flag classes is `-3 · r (can6 ρ i x y)`.  The proof assembles `lineSum_general` (the sum over the flag orbits is the sum over the
cusp representatives of the classes of `lineTheta` at `flagAt h (cuspPrim c)`), `nft2_line` (the replacement of the nerve data by the normal form, flagwise) and `lineSum_can` (the sum of the normal-form flag terms).
-/

open CategoryTheory Limits MonoidalCategory
open scoped MatrixGroups
open CongruenceSubgroup Matrix
open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
open TernaryPeriodPolynomials.Argument.GammaNStokes
open TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open TernaryPoly.OrdinaryIncidence (Line Plane)
open TernaryPeriodPolynomials.Argument.GammaNFacesFull TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPoly.EquivariantSingularSmall TernaryPoly.BoundaryFaceResolutionComparison
open GeneralEisenstein
open TernaryPoly TernaryPoly.IntegralGL3Congruence
open TernaryPoly.SymmetricSpaceBoundaryFull
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.HeckeDuality
  TernaryPoly.RankTwoAugmentedFrames

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

attribute [local instance] TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison.vertexAction

/-- **(M3), lines, for the cut primitive and the evaluation data `flagEval`**, with the constants `κ i = -3`: `M3LineAt flagEval (fun _ => -3)`. -/
theorem m3Line : M3LineAt flagEval (fun _ => -3) := by
  intro V _ _ _ _ _ ρ i x y d e hd he hdc hec r γ hγ
  classical
  have hN : (3 : ℕ) ≤ 6 := by norm_num
  have hγ' := cutγ_line_primitive (evalC (MonoidHom.id Γ6) (rep6 ρ) ≫ rHom r) d e γ hγ
    (labelOrbit Γ6 Line (lineFacesEquivOrbits i)) (labelOrbit_invariant _) hd he
  have hbij := flagAt_cusp_bijOn' i.rep (lineFacesEquivOrbits i) (lineOf_rep_mem i)
  rw [lineSum_general _ d e γ hγ (labelOrbit Γ6 Line (lineFacesEquivOrbits i)) (labelOrbit_invariant _) hd he
    (lineOf i.rep) (lineOf_rep_mem i) (I := ↥(cuspReps hN).R) (fun c => flagAt i.rep (cuspPrim (c : RationalLine2)))
    (fun c => flagLineOf_flagAt i.rep _) (Set.injOn_univ.1 hbij.injOn)
    (fun o ho => by
      obtain ⟨c, -, hc⟩ := hbij.surjOn ho
      exact ⟨c, hc⟩)]
  let ρ' : Representation ℚ ↥(gammaNQAt 6 i.rep) (dualRepG (repAt ρ i)) := qReprG (dualRepG (repAt ρ i)).ρ
  let eQ : repAt ρ i →ₗ[ℚ] dualRepG (repAt ρ i) →ₗ[ℚ] ℚ := (evalBilinC (V := V)).compr₂ r
  obtain ⟨z, z', hzx, hzy, hU, hmix, hmix', gb, hgb, hdd, wB, hwB, hΘ, hcls⟩ :=
    nft2_line hN ρ i x y d e hdc hec r ρ' (fun _ _ => rfl) eQ (fun _ _ => rfl) _ hγ'
  rw [Finset.sum_congr rfl (fun c _ => hcls c)]
  have key := lineSum_can hN i.rep (repAt ρ i) ρ' (fun _ _ => rfl) eQ r (fun _ _ => rfl) x y z z' hzx hzy hU hmix hmix' gb hgb hdd
    wB hwB hΘ
  rw [key]
  rfl

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
