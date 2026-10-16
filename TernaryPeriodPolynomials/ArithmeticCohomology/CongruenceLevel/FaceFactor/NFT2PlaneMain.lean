module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.NFT2PlaneStepA

@[expose] public section


/-!
# NFT-2 for planes: the normal form of the nerve data and the flagwise replacement

Formalized by Claude Sonnet 5.5.

`nft2_plane`: for two mixed classes `x`, `y` of the plane face `i` with lifts `d`, `e` and any primitive `γ` of `d.z ∪ e.z`, there are normal-form relative cocycles `z`, `z'` representing `x`, `y`, a normalised primitive `gb` of `z ∪ z'` and primitives `w' c` of `z'` on the flag groups
`Stab (pflag h (wOf c))` such that the class `λ_{F_c}[planeTheta]` of the nerve data equals the class of the normal-form flag cocycle `planeFlagTheta` for every cusp `c`.
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

section MainP

variable {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V] [FiniteDimensional ℂ V]

omit [FiniteDimensional ℂ V] in
open scoped Classical in
/-- **NFT-2 (planes): the normal form of the nerve data and the flagwise replacement.** -/
theorem nft2_plane (hN : 3 ≤ 6) (ρ : Representation ℂ (gammaN 6) V) (i : PlaneFaces 6) (x : planeMixedSub ρ i)
    (y : planeMixedSub ρ.dual i)
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
          (cmpH2Dual ρ (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) y.1))
    (r : ℂ →ₗ[ℚ] ℚ)
    (ρ' : Representation ℚ ↥(gammaNPAt 6 (planeFaceRepr i)) (dualRepG (planeRepAt ρ i)))
    (hρ' : ∀ g x, ρ' g x = (dualRepG (planeRepAt ρ i)).ρ g x)
    (eQ : planeRepAt ρ i →ₗ[ℚ] dualRepG (planeRepAt ρ i) →ₗ[ℚ] ℚ)
    (he : ∀ x y, eQ x y = r (Module.Dual.eval ℂ (planeRepAt ρ i) x y))
    (γ : (prodComplex Γ6 RationalGL3 Plane).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6))
    (hγ : (prodComplex Γ6 RationalGL3 Plane).d 4 3 ≫ γ =
      (nerveDiagSystem Γ6 RationalGL3 Plane).Δ 2 2 4 rfl ≫ (d.z ⊗ₘ e.z) ≫ (evalC (MonoidHom.id Γ6) (rep6 ρ) ≫ rHom r)) :
    ∃ (z : relativeTwoCocycles (faceExt 6 (planeFaceRepr i)).inl (planeRepAt ρ i))
      (z' : relativeTwoCocycles (faceExt 6 (planeFaceRepr i)).inl (dualRepG (planeRepAt ρ i))),
      relativeTwoCocycleClass (faceExt 6 (planeFaceRepr i)).inl (planeRepAt ρ i) z =
        ⟨x.1, res_radical_of_planeMixedAt (N := 6) (h := planeFaceRepr i) (W := planeRepAt ρ i) x⟩ ∧
      relativeTwoCocycleClass (faceExt 6 (planeFaceRepr i)).inl (dualRepG (planeRepAt ρ i)) z' =
        ⟨y.1, res_radical_of_planeMixedAt (N := 6) (h := planeFaceRepr i) (W := dualRepG (planeRepAt ρ i)) y⟩ ∧
      (∀ a b : Gamma 6, z.val (faceSplitting 6 (planeFaceRepr i) a, faceSplitting 6 (planeFaceRepr i) b) = 0) ∧
      (∀ (r : RadicalLattice) (l : Gamma 6), z.val ((faceExt 6 (planeFaceRepr i)).inl r, faceSplitting 6 (planeFaceRepr i) l) = 0) ∧
      (∀ (r : RadicalLattice) (l : Gamma 6), z'.val ((faceExt 6 (planeFaceRepr i)).inl r, faceSplitting 6 (planeFaceRepr i) l) = 0) ∧
      ∃ (gb : ↥(gammaNPAt 6 (planeFaceRepr i)) → ↥(gammaNPAt 6 (planeFaceRepr i)) → ↥(gammaNPAt 6 (planeFaceRepr i)) → ℚ)
        (_ : ∀ a b c : RadicalLattice, gb ((faceExt 6 (planeFaceRepr i)).inl a) ((faceExt 6 (planeFaceRepr i)).inl b)
          ((faceExt 6 (planeFaceRepr i)).inl c) = 0)
        (_ : dd3T gb = cup22 ρ' eQ (fun a b => z.val (a, b)) (fun a b => z'.val (a, b)))
        (w' : ∀ c : ↥(cuspReps hN).R, ↥(MulAction.stabilizer Γ6 (pflag (planeFaceRepr i) (wOf (c : RationalLine2)))) →
          dualRepG (planeRepAt ρ i))
        (_ : ∀ (c : ↥(cuspReps hN).R) b₁ b₂, (dualRepG (planeRepAt ρ i)).ρ
          ((planeLift (planeFaceRepr i) (wOf (c : RationalLine2)) ((gammaEquiv hN).symm (cuspSigma (c : RationalLine2)))
            (sigmaCusp_val hN c)).ι b₁) (w' c b₂) - w' c (b₁ * b₂) + w' c b₁ =
          z'.val ((planeLift (planeFaceRepr i) (wOf (c : RationalLine2)) ((gammaEquiv hN).symm (cuspSigma (c : RationalLine2)))
            (sigmaCusp_val hN c)).ι b₁,
            (planeLift (planeFaceRepr i) (wOf (c : RationalLine2)) ((gammaEquiv hN).symm (cuspSigma (c : RationalLine2)))
              (sigmaCusp_val hN c)).ι b₂))
        (hΘ : ∀ c : ↥(cuspReps hN).R, dThree ((planeLift (planeFaceRepr i) (wOf (c : RationalLine2))
          ((gammaEquiv hN).symm (cuspSigma (c : RationalLine2))) (sigmaCusp_val hN c)).planeFlagTheta ρ' eQ
          (fun a b => z.val (a, b)) (w' c) gb) = 0),
        ∀ c : ↥(cuspReps hN).R,
          flagLam (pflag (planeFaceRepr i) (wOf (c : RationalLine2)))
            (clsRes (MulAction.stabilizer Γ6 (pflag (planeFaceRepr i) (wOf (c : RationalLine2))))
              (planeTheta (evalC (MonoidHom.id Γ6) (rep6 ρ) ≫ rHom r) d e γ (pflag (planeFaceRepr i) (wOf (c : RationalLine2))))
              (planeTheta_dThree _ d e γ hγ _)) =
          flagLam (pflag (planeFaceRepr i) (wOf (c : RationalLine2)))
            (clsRes (MulAction.stabilizer Γ6 (pflag (planeFaceRepr i) (wOf (c : RationalLine2)))) _ (hΘ c)) := by
  classical
  obtain ⟨z, z', hzx, hzy, hU, hmix, hmix', κ, κ', h1, h2⟩ := planeStepA ρ i x y d e hdc hec
  obtain ⟨gn, hgn, hrad, hF⟩ := nft2_plane_core (evalC (MonoidHom.id Γ6) (rep6 ρ) ≫ rHom r) i d e γ hγ
    (cocFn ρ i z.val) (cocFnDual ρ i z'.val) κ κ' (cocycle_dd2P ρ i z.val) (cocycle_dd2_dualP ρ i z'.val) h1 h2
    (faceExt 6 (planeFaceRepr i)).inl (faceExt 6 (planeFaceRepr i)).inl_injective (fun a b => z.2 a b)
  choose wn hwn hΘ hcls using fun c : ↥(cuspReps hN).R => hF (pflag (planeFaceRepr i) (wOf (c : RationalLine2)))
    (flagPlaneOf_pflag _ _)
  have hρst : ∀ (c : ↥(cuspReps hN).R) (g : ↥(MulAction.stabilizer Γ6 (pflag (planeFaceRepr i) (wOf (c : RationalLine2))))) (φ : Module.Dual ℂ V),
      (dualRepG (planeRepAt ρ i)).ρ (stabToE (planeFaceRepr i) (pflag (planeFaceRepr i) (wOf (c : RationalLine2)))
        (flagPlaneOf_pflag _ _) g) φ =
      ((qRep (MonoidHom.id Γ6) (rep6 ρ).dual).ρ.comp (MulAction.stabilizer Γ6 (pflag (planeFaceRepr i) (wOf (c : RationalLine2)))).subtype) g φ := by
    intro c g φ
    rw [← qRepDual_comp_embP]
    show (qRep (MonoidHom.id Γ6) (rep6 ρ).dual).ρ (planeEmb (planeFaceRepr i) _) φ = (qRep (MonoidHom.id Γ6) (rep6 ρ).dual).ρ (g : Γ6) φ
    rw [planeEmb_stabToE_gen]
  have hconv : ∀ (c : ↥(cuspReps hN).R)
      (g₀ g₁ : ↥(MulAction.stabilizer Γ6 (pflag (planeFaceRepr i) (wOf (c : RationalLine2))))) (v : V) (φ : Module.Dual ℂ V),
      eQ v (ρ' (stabToE (planeFaceRepr i) (pflag (planeFaceRepr i) (wOf (c : RationalLine2))) (flagPlaneOf_pflag _ _) g₀ *
        stabToE (planeFaceRepr i) (pflag (planeFaceRepr i) (wOf (c : RationalLine2))) (flagPlaneOf_pflag _ _) g₁) φ) =
      pairOf (evalC (MonoidHom.id Γ6) (rep6 ρ) ≫ rHom r) v
        (((qRep (MonoidHom.id Γ6) (rep6 ρ).dual).ρ.comp (MulAction.stabilizer Γ6 (pflag (planeFaceRepr i) (wOf (c : RationalLine2)))).subtype)
          (g₀ * g₁) φ) := by
    intro c g₀ g₁ v φ
    rw [hρ', ← map_mul, hρst]
    exact he v _
  have hfun : ∀ c : ↥(cuspReps hN).R, (planeLift (planeFaceRepr i) (wOf (c : RationalLine2))
      ((gammaEquiv hN).symm (cuspSigma (c : RationalLine2))) (sigmaCusp_val hN c)).planeFlagTheta ρ' eQ
      (fun a b => z.val (a, b)) (wn c) gn =
      fun g : Fin 3 → ↥(MulAction.stabilizer Γ6 (pflag (planeFaceRepr i) (wOf (c : RationalLine2)))) =>
        cup21 ((qRep (MonoidHom.id Γ6) (rep6 ρ).dual).ρ.comp (MulAction.stabilizer Γ6 (pflag (planeFaceRepr i) (wOf (c : RationalLine2)))).subtype)
          (pairOf (evalC (MonoidHom.id Γ6) (rep6 ρ) ≫ rHom r))
          (fun s t => cocFn ρ i z.val (stabToE (planeFaceRepr i) (pflag (planeFaceRepr i) (wOf (c : RationalLine2))) (flagPlaneOf_pflag _ _) s)
            (stabToE (planeFaceRepr i) (pflag (planeFaceRepr i) (wOf (c : RationalLine2))) (flagPlaneOf_pflag _ _) t))
          (-wn c) (g 0) (g 1) (g 2) +
        gn (stabToE (planeFaceRepr i) (pflag (planeFaceRepr i) (wOf (c : RationalLine2))) (flagPlaneOf_pflag _ _) (g 0))
          (stabToE (planeFaceRepr i) (pflag (planeFaceRepr i) (wOf (c : RationalLine2))) (flagPlaneOf_pflag _ _) (g 1))
          (stabToE (planeFaceRepr i) (pflag (planeFaceRepr i) (wOf (c : RationalLine2))) (flagPlaneOf_pflag _ _) (g 2)) := by
    intro c
    funext g
    simp only [LetterLift.planeFlagTheta, cup21]
    congr 1
    exact hconv c (g 0) (g 1) _ _
  refine ⟨z, z', hzx, hzy, hU, hmix, hmix', gn, hrad, ?_, wn, ?_, fun c => (hfun c) ▸ hΘ c, ?_⟩
  · rw [hgn]
    funext g1 g2 g3 g4
    exact pairing_convP ρ i r ρ' hρ' eQ he _ _ _
  · intro c b₁ b₂
    have h0 := congrFun (congrFun (hwn c) b₁) b₂
    simp only [dd1] at h0
    have h3 := hρst c b₁ (wn c b₂)
    exact (congrArg (fun t => t - wn c (b₁ * b₂) + wn c b₁) h3).trans h0
  · intro c
    exact congrArg (flagLam _) ((hcls c).trans (clsRes_congr _ (hfun c).symm _ _))

end MainP

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
