module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.NFT2PlaneBridge
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.HSMixedNormalForm
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.HSNormalFormPlane

@[expose] public section


/-!
# NFT-2 for planes: Step A

Formalized by Claude Sonnet 5.5.

`planeNormalForms`, `planeStepA`: normal-form representatives (`z(s a, s b) = 0`, `z(inl r, s l) = 0`) of two mixed classes of a plane face and the primitives `κ`, `κ'` of their differences with the nerve cochains `zbarP`.
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

section StepA

variable {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V]
  (ρ : Representation ℂ (gammaN 6) V) (i : PlaneFaces 6)

omit [Module ℚ V] [IsScalarTower ℚ ℂ V] in
/-- **Normal-form representatives of two mixed classes of a plane face.** -/
theorem planeNormalForms (i : PlaneFaces 6) (x : planeMixedSub ρ i) (y : planeMixedSub ρ.dual i) :
    ∃ (z : relativeTwoCocycles (faceExt 6 (planeFaceRepr i)).inl (planeRepAt ρ i))
      (z' : relativeTwoCocycles (faceExt 6 (planeFaceRepr i)).inl (dualRepG (planeRepAt ρ i))),
      relativeTwoCocycleClass (faceExt 6 (planeFaceRepr i)).inl (planeRepAt ρ i) z =
        ⟨x.1, res_radical_of_planeMixedAt (N := 6) (h := planeFaceRepr i) (W := planeRepAt ρ i) x⟩ ∧
      relativeTwoCocycleClass (faceExt 6 (planeFaceRepr i)).inl (dualRepG (planeRepAt ρ i)) z' =
        ⟨y.1, res_radical_of_planeMixedAt (N := 6) (h := planeFaceRepr i) (W := dualRepG (planeRepAt ρ i)) y⟩ ∧
      (∀ a b : Gamma 6, z.val (faceSplitting 6 (planeFaceRepr i) a, faceSplitting 6 (planeFaceRepr i) b) = 0) ∧
      (∀ (r : RadicalLattice) (l : Gamma 6), z.val ((faceExt 6 (planeFaceRepr i)).inl r, faceSplitting 6 (planeFaceRepr i) l) = 0) ∧
      (∀ (r : RadicalLattice) (l : Gamma 6), z'.val ((faceExt 6 (planeFaceRepr i)).inl r, faceSplitting 6 (planeFaceRepr i) l) = 0) := by
  have hvan : ∀ (A : Rep ℂ ↥(CongruenceSubgroup.Gamma 6)) (x : groupCohomology.H2 A), x = 0 :=
    fun A x => H2_vanish_level (CongruenceSubgroup.Gamma 6) A x
  obtain ⟨z, hzx, hU, hmix⟩ := exists_normal_form_mixed (faceSplitting 6 (planeFaceRepr i)) (planeRepAt ρ i) hvan
    ⟨x.1, res_radical_of_planeMixedAt (N := 6) (h := planeFaceRepr i) (W := planeRepAt ρ i) x⟩
  obtain ⟨z', hzy, -, hmix'⟩ := exists_normal_form_mixed (faceSplitting 6 (planeFaceRepr i)) (dualRepG (planeRepAt ρ i)) hvan
    ⟨y.1, res_radical_of_planeMixedAt (N := 6) (h := planeFaceRepr i) (W := dualRepG (planeRepAt ρ i)) y⟩
  exact ⟨z, z', hzx, hzy, hU, hmix, hmix'⟩

/-- **Step A of NFT-2 (planes)**: normal-form representatives together with the primitives `κ`, `κ'` of the differences with the nerve cochains. -/
theorem planeStepA (i : PlaneFaces 6) (x : planeMixedSub ρ i) (y : planeMixedSub ρ.dual i)
    (d : PlaneDatum (qRep (MonoidHom.id Γ6) (rep6 ρ))) (e : PlaneDatum (qRep (MonoidHom.id Γ6) (rep6 ρ).dual))
    (hdc : d.coord (planeFacesEquivOrbits i) =
        faceTauQ (fun i : PlaneFaces 6 => planeFacesEquivOrbits i) (fun i => planeOf (planeFaceRepr i)) planeOf_rep_mem
          (fun i => ↥(gammaNPAt 6 (planeFaceRepr i))) (fun i => planeEmb (planeFaceRepr i)) (fun i => planeEmb_injective (planeFaceRepr i))
          (fun i => planeEmb_range (planeFaceRepr i)) (rep6 ρ) i
          (cmpH2 ρ (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) x.1))
    (hec : e.coord (planeFacesEquivOrbits i) =
        faceTauQ (fun i : PlaneFaces 6 => planeFacesEquivOrbits i) (fun i => planeOf (planeFaceRepr i)) planeOf_rep_mem
          (fun i => ↥(gammaNPAt 6 (planeFaceRepr i))) (fun i => planeEmb (planeFaceRepr i)) (fun i => planeEmb_injective (planeFaceRepr i))
          (fun i => planeEmb_range (planeFaceRepr i)) (rep6 ρ).dual i
          (cmpH2Dual ρ (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) y.1)) :
    ∃ (z : relativeTwoCocycles (faceExt 6 (planeFaceRepr i)).inl (planeRepAt ρ i))
      (z' : relativeTwoCocycles (faceExt 6 (planeFaceRepr i)).inl (dualRepG (planeRepAt ρ i))),
      relativeTwoCocycleClass (faceExt 6 (planeFaceRepr i)).inl (planeRepAt ρ i) z =
        ⟨x.1, res_radical_of_planeMixedAt (N := 6) (h := planeFaceRepr i) (W := planeRepAt ρ i) x⟩ ∧
      relativeTwoCocycleClass (faceExt 6 (planeFaceRepr i)).inl (dualRepG (planeRepAt ρ i)) z' =
        ⟨y.1, res_radical_of_planeMixedAt (N := 6) (h := planeFaceRepr i) (W := dualRepG (planeRepAt ρ i)) y⟩ ∧
      (∀ a b : Gamma 6, z.val (faceSplitting 6 (planeFaceRepr i) a, faceSplitting 6 (planeFaceRepr i) b) = 0) ∧
      (∀ (r : RadicalLattice) (l : Gamma 6), z.val ((faceExt 6 (planeFaceRepr i)).inl r, faceSplitting 6 (planeFaceRepr i) l) = 0) ∧
      (∀ (r : RadicalLattice) (l : Gamma 6), z'.val ((faceExt 6 (planeFaceRepr i)).inl r, faceSplitting 6 (planeFaceRepr i) l) = 0) ∧
      ∃ (κ : ↥(gammaNPAt 6 (planeFaceRepr i)) → V) (κ' : ↥(gammaNPAt 6 (planeFaceRepr i)) → Module.Dual ℂ V),
        zbarP i d = cocFn ρ i z.val + dd1 ((qRep (MonoidHom.id Γ6) (rep6 ρ)).ρ.comp (planeEmb (planeFaceRepr i))) κ ∧
        zbarP i e = cocFnDual ρ i z'.val + dd1 ((qRep (MonoidHom.id Γ6) (rep6 ρ).dual).ρ.comp (planeEmb (planeFaceRepr i))) κ' := by
  obtain ⟨z, z', hzx, hzy, hU, hmix, hmix'⟩ := planeNormalForms ρ i x y
  obtain ⟨κ, h1⟩ := zbarP_decomp ρ i x.1 d hdc z.val (congrArg Subtype.val hzx)
  obtain ⟨κ', h2⟩ := zbarP_decomp_dual ρ i y.1 e hec z'.val (congrArg Subtype.val hzy)
  exact ⟨z, z', hzx, hzy, hU, hmix, hmix', κ, κ', h1, h2⟩


end StepA

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
