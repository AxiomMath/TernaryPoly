module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Terms
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Face.Bijection
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Cone.Bridge

@[expose] public section


/-!
# `FaceFactorisation6 → Step1 → Step2 → ConeFactorisation`

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups DirectSum
noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange

open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.FormClassK
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.EisensteinDual
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.ConvergenceC4
open MulAction
open TernaryPeriodPolynomials.Argument.EisensteinClass

section LineSum

variable {M n : ℕ} [NeZero M]

theorem lineSum_eq (h6 : 6 ∣ M) (hM : 3 ≤ M) (c : LineFaces 6 → ℂ)
    (hF : ∀ (i : LineFaces 6) (x : lineMixedSub (permRep (rhoEn n) (Δ6 M)) i) (y : lineMixedSub (permRep (rhoEn n) (Δ6 M)).dual i),
      lineFacePairM (permRep (rhoEn n) (Δ6 M)) i x.1 y.1 = c i * can6 (permRep (rhoEn n) (Δ6 M)) i x y)
    (S1 : FrameInvarianceLine M n hM) (S2 : OrbitIdentLine M n hM)
    (c₀ : groupCohomology.H2 (gammaNRepAll M n)) (hz : ZeroFlags M n c₀) (c₀' : groupCohomology.H2 (gammaNRepAllDual M n))
    (hz' : ZeroFlagsRep (gammaNRepAll M n).ρ.dual c₀')
    (cV : groupCohomology.H2 (Rep.of (permRep (rhoEn n) (Δ6 M))))
    (cVd : groupCohomology.H2 (Rep.of (permRep (rhoEn n).dual (Δ6 M))))
    (hcV : PhiH (rhoEn n) (Δ6 M) cV = transportΔ M (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl) c₀)
    (hcVd : PhiH (rhoEn n).dual (Δ6 M) cVd = transportΔ M (rhoEn n).dual (gammaNRepAll M n).ρ.dual
      (hρ_dual M (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl)) c₀') :
    ∑ i : LineFaces 6, ∑ o : orbitRel.Quotient ↥(lineSub i) (↥(gammaN 6) ⧸ Δ6 M),
      lineFacePairM (permRep (rhoEn n) (Δ6 M)) i (lineTermX c₀ hz cV hcV i o).1 (lineTermY c₀' hz' cVd hcVd i o).1 =
    ∑ i' : LineFaces M, c (LineFaces.mk (N := 6) i'.rep) * canAtClass M i'.rep n hM c₀ hz c₀' hz' := by
  have hT : ∀ (i : LineFaces 6) (o : orbitRel.Quotient ↥(lineSub i) (↥(gammaN 6) ⧸ Δ6 M)),
      lineFacePairM (permRep (rhoEn n) (Δ6 M)) i (lineTermX c₀ hz cV hcV i o).1 (lineTermY c₀' hz' cVd hcVd i o).1 =
        c i * canAtClass M (lineFaceOver M i o).rep n hM c₀ hz c₀' hz' := by
    intro i o
    have h1 := hF i (lineTermX c₀ hz cV hcV i o) (lineTermY c₀' hz' cVd hcVd i o)
    have h2 := S2 c₀ hz c₀' hz' cV cVd hcV hcVd i o
    rw [h1, h2]
    obtain ⟨q, hq, γ, hγ, hr⟩ := LineFaces.rel_rep (N := M) (i.rep * ((uOLine M i o : ↥(gammaN 6)) : SL(3, ℤ)))
    have hr' : (lineFaceOver M i o).rep = q * (i.rep * ((uOLine M i o : ↥(gammaN 6)) : SL(3, ℤ))) * γ := hr
    rw [hr', S1 c₀ hz c₀' hz' _ q γ hq hγ]
  simp_rw [hT]
  refine Eq.trans (Fintype.sum_sigma (fun x : (Σ i : LineFaces 6, orbitRel.Quotient ↥(lineSub i) (↥(gammaN 6) ⧸ Δ6 M)) =>
    c x.1 * canAtClass M (lineFaceOver M x.1 x.2).rep n hM c₀ hz c₀' hz')).symm ?_
  rw [← Equiv.sum_comp (lineFaceOverEquiv M h6)]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  have := mk6_lineFaceOver M h6 x.1 x.2
  change c x.1 * _ = c (LineFaces.mk (N := 6) (lineFaceOver M x.1 x.2).rep) * _
  rw [this]
  rfl

end LineSum
section PlaneSum

variable {M n : ℕ} [NeZero M]

theorem planeSum_eq (h6 : 6 ∣ M) (hM : 3 ≤ M) (c : PlaneFaces 6 → ℂ)
    (hF : ∀ (i : PlaneFaces 6) (x : planeMixedSub (permRep (rhoEn n) (Δ6 M)) i) (y : planeMixedSub (permRep (rhoEn n) (Δ6 M)).dual i),
      planeFacePairM (permRep (rhoEn n) (Δ6 M)) i x.1 y.1 = c i * can6P (permRep (rhoEn n) (Δ6 M)) i x y)
    (S1 : FrameInvariancePlane M n hM) (S2 : OrbitIdentPlane M n hM)
    (c₀ : groupCohomology.H2 (gammaNRepAll M n)) (hz : ZeroFlags M n c₀) (c₀' : groupCohomology.H2 (gammaNRepAllDual M n))
    (hz' : ZeroFlagsRep (gammaNRepAll M n).ρ.dual c₀')
    (cV : groupCohomology.H2 (Rep.of (permRep (rhoEn n) (Δ6 M))))
    (cVd : groupCohomology.H2 (Rep.of (permRep (rhoEn n).dual (Δ6 M))))
    (hcV : PhiH (rhoEn n) (Δ6 M) cV = transportΔ M (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl) c₀)
    (hcVd : PhiH (rhoEn n).dual (Δ6 M) cVd = transportΔ M (rhoEn n).dual (gammaNRepAll M n).ρ.dual
      (hρ_dual M (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl)) c₀') :
    ∑ i : PlaneFaces 6, ∑ o : orbitRel.Quotient ↥(planeSub i) (↥(gammaN 6) ⧸ Δ6 M),
      planeFacePairM (permRep (rhoEn n) (Δ6 M)) i (planeTermX c₀ hz cV hcV i o).1 (planeTermY c₀' hz' cVd hcVd i o).1 =
    ∑ i' : PlaneFaces M, c ((Quotient.mk (planeFaceSetoid 6) (planeFaceRepr i') : PlaneFaces 6)) * canAtClassP M (planeFaceRepr i') n hM c₀ hz c₀' hz' := by
  have hT : ∀ (i : PlaneFaces 6) (o : orbitRel.Quotient ↥(planeSub i) (↥(gammaN 6) ⧸ Δ6 M)),
      planeFacePairM (permRep (rhoEn n) (Δ6 M)) i (planeTermX c₀ hz cV hcV i o).1 (planeTermY c₀' hz' cVd hcVd i o).1 =
        c i * canAtClassP M (planeFaceRepr (planeFaceOver M i o)) n hM c₀ hz c₀' hz' := by
    intro i o
    have h1 := hF i (planeTermX c₀ hz cV hcV i o) (planeTermY c₀' hz' cVd hcVd i o)
    have h2 := S2 c₀ hz c₀' hz' cV cVd hcV hcVd i o
    rw [h1, h2]
    obtain ⟨q, hq, γ, hγ, hr⟩ := PlaneFaces_rel_rep M (planeFaceRepr i * ((uOPlane M i o : ↥(gammaN 6)) : SL(3, ℤ)))
    have hr' : planeFaceRepr (planeFaceOver M i o) = q * (planeFaceRepr i * ((uOPlane M i o : ↥(gammaN 6)) : SL(3, ℤ))) * γ := hr
    rw [hr', S1 c₀ hz c₀' hz' _ q γ hq hγ]
  simp_rw [hT]
  refine Eq.trans (Fintype.sum_sigma (fun x : (Σ i : PlaneFaces 6, orbitRel.Quotient ↥(planeSub i) (↥(gammaN 6) ⧸ Δ6 M)) =>
    c x.1 * canAtClassP M (planeFaceRepr (planeFaceOver M x.1 x.2)) n hM c₀ hz c₀' hz')).symm ?_
  rw [← Equiv.sum_comp (planeFaceOverEquiv M h6)]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  have := mk6_planeFaceOver M h6 x.1 x.2
  change c x.1 * _ = c ((Quotient.mk (planeFaceSetoid 6) (planeFaceRepr (planeFaceOver M x.1 x.2)) : PlaneFaces 6)) * _
  rw [this]
  rfl

end PlaneSum

section Main

variable {M n : ℕ} [NeZero M]

theorem canAtClass_rep_eq (hM : 3 ≤ M) (hn : 4 ≤ n) (c₀ : groupCohomology.H2 (gammaNRepAll M n)) (hz : ZeroFlags M n c₀)
    (ξQ : LineCuspSum M n) (hξQ : lineCuspSumEmbedding M n ξQ = lineBoundary M n c₀) (c' : Hd (N := M) (n := n) hn)
    (i : LineFaces M) :
    canAtClass M i.rep n hM c₀ hz (toLiteralG M n c'.1) (hdZero n hM hn c') =
      (qdiAlignmentInst (M := M) (n := n)).pairQ hM i (ξQ i) ((dualRQ hM hn c') i) := by
  unfold canAtClass canAt
  rw [mixedEdgeAt_lineClass n i.rep hM c₀ hz (ξQ i) (lineEmb_component n c₀ ξQ hξQ i),
    mixedEdgeAt_lineClassDual n hM hn c' i (hdZero n hM hn c')]
  rfl

theorem coneFactorisation_of (h6 : 6 ∣ M) (hM : 3 ≤ M) (hn : 4 ≤ n)
    (FF : FaceFactorisation6) (S1 : Step1 M n hM) (S2 : Step2 M n hM) : ConeFactorisation hM hn := by
  obtain ⟨c, d, hc, hd, hF⟩ := FF
  choose ψ hψ using fun j : PlaneFaces M => exists_planeDualMap n hM hn j
  refine ⟨fun i' => c (LineFaces.mk (N := 6) i'.rep), fun i' => hc _, ?_⟩
  let pP : ∀ j : PlaneFaces M, faceCuspidal M (planeFaceRepr j) n →ₗ[ℂ]
      groupCohomology.H2 (Rep.of ((dualRhoC M n).comp (Subgroup.inclusion (gammaNPAt_le M (planeFaceRepr j))))) →ₗ[ℂ] ℂ :=
    fun j => ((d (Quotient.mk (planeFaceSetoid 6) (planeFaceRepr j) : PlaneFaces 6)) • pairPfaceCan n hM (planeFaceRepr j)).compl₂ (ψ j)
  refine ⟨sumPairing _ _ pP, ?_⟩
  intro c₀ hz ξP ξQ hξP hξQ c' cV cVd hcV hcVd
  have hz' : ZeroFlagsRep (gammaNRepAll M n).ρ.dual (toLiteralG M n c'.1) := hdZero n hM hn c'
  have hL := lineSum_eq h6 hM c (fun i x y => (hF _ (permRep (rhoEn n) (Δ6 M))).1 i x y) S1.1 S2.1 c₀ hz
    (toLiteralG M n c'.1) hz' cV cVd hcV hcVd
  have hP := planeSum_eq h6 hM d (fun i x y => (hF _ (permRep (rhoEn n) (Δ6 M))).2 i x y) S1.2 S2.2 c₀ hz
    (toLiteralG M n c'.1) hz' cV cVd hcV hcVd
  have hstokes : stokesSum (rhoEn n) (Δ6 M) cV (h2Hom (dualRepHom (rhoEn n) (Δ6 M)) cVd) =
      (∑ i : LineFaces 6, ∑ o : orbitRel.Quotient ↥(lineSub i) (↥(gammaN 6) ⧸ Δ6 M),
        lineFacePairM (permRep (rhoEn n) (Δ6 M)) i (lineTermX c₀ hz cV hcV i o).1 (lineTermY (toLiteralG M n c'.1) hz' cVd hcVd i o).1) +
      (∑ i : PlaneFaces 6, ∑ o : orbitRel.Quotient ↥(planeSub i) (↥(gammaN 6) ⧸ Δ6 M),
        planeFacePairM (permRep (rhoEn n) (Δ6 M)) i (planeTermX c₀ hz cV hcV i o).1 (planeTermY (toLiteralG M n c'.1) hz' cVd hcVd i o).1) := rfl
  rw [hstokes, hL, hP, add_comm]
  congr 1
  · -- planes
    rw [sumPairing_apply]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have e : canAtClassP M (planeFaceRepr j) n hM c₀ hz (toLiteralG M n c'.1) hz' =
        pairPfaceCan n hM (planeFaceRepr j) (ξP j) (ψ j ((dualRP hn c') j)) := by
      unfold canAtClassP canAtP
      rw [planeEdge_planeClass n (planeFaceRepr j) hM c₀ hz (ξP j) (planeEmb_component n c₀ ξP hξP j), hψ j c']
      rfl
    simp only [pP, LinearMap.compl₂_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [e]
  · -- lines
    rw [sumPairing_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [QDiAlignment.pairQ_scale, ← canAtClass_rep_eq hM hn c₀ hz ξQ hξQ c' i]

end Main

end TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
