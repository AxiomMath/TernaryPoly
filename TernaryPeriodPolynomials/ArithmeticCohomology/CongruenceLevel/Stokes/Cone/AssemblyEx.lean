module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Plane.Pairing2
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Cone.Assembly

@[expose] public section


/-!
# Proposition C.5 from the factorisation (a′) alone

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
open TernaryPeriodPolynomials.Argument.SeedC3
open MulAction
open TernaryPeriodPolynomials.Argument.EisensteinClass

section Ex

variable {M n : ℕ} [NeZero M]

/-- **The cone-level factorisation, existence form**: there are a plane pairing and a family of left nondegenerate line pairings (for the faces of `Γ(M)`) such that the Stokes sum of the `Γ(6)` cone pairings
of the induced classes is the level-`M` Stokes expression.  This is what `GammaNC5FaceObligations` needs. -/
def ConeFactorisationEx (hM : 3 ≤ M) (hn : 4 ≤ n) : Prop :=
  ∃ (pairP : PlaneCuspSum M n →ₗ[ℂ] PDmod M n →ₗ[ℂ] ℂ) (pairQ : ∀ i : LineFaces M, lineFaceCuspidal M i.rep n →ₗ[ℂ] QDi M n i →ₗ[ℂ] ℂ),
    (∀ (i : LineFaces M) (a : lineFaceCuspidal M i.rep n), (∀ b, pairQ i a b = 0) → a = 0) ∧
    ∀ c₀ : groupCohomology.H2 (gammaNRepAll M n), ZeroFlags M n c₀ →
      ∀ (ξP : PlaneCuspSum M n) (ξQ : LineCuspSum M n),
        planeCuspSumEmbedding M n ξP = planeBoundary M n c₀ →
        lineCuspSumEmbedding M n ξQ = lineBoundary M n c₀ →
        ∀ c' : Hd (N := M) (n := n) hn,
          ∀ (cV : groupCohomology.H2 (Rep.of (permRep (rhoEn n) (Δ6 M))))
            (cVd : groupCohomology.H2 (Rep.of (permRep (rhoEn n).dual (Δ6 M)))),
            PhiH (rhoEn n) (Δ6 M) cV = transportΔ M (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl) c₀ →
            PhiH (rhoEn n).dual (Δ6 M) cVd = transportΔ M (rhoEn n).dual (gammaNRepAll M n).ρ.dual
              (hρ_dual M (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl))
              (toLiteralG M n c'.1 : groupCohomology.H2 (Rep.of (gammaNRepAll M n).ρ.dual)) →
            stokesSum (rhoEn n) (Δ6 M) cV (h2Hom (dualRepHom (rhoEn n) (Δ6 M)) cVd) =
              pairP ξP (dualRP hn c') + sumPairing _ _ pairQ ξQ (dualRQ hM hn c')

/-- **Stokes at level `Γ(M)` from the existence form**. -/
theorem stokes_of_coneFactorisationEx (hM : 3 ≤ M) (hn : 4 ≤ n) (F : ConeFactorisationEx hM hn) :
    ∃ (pairP : PlaneCuspSum M n →ₗ[ℂ] PDmod M n →ₗ[ℂ] ℂ) (pairQ : ∀ i : LineFaces M, lineFaceCuspidal M i.rep n →ₗ[ℂ] QDi M n i →ₗ[ℂ] ℂ),
      (∀ (i : LineFaces M) (a : lineFaceCuspidal M i.rep n), (∀ b, pairQ i a b = 0) → a = 0) ∧
      ∀ c₀ : groupCohomology.H2 (gammaNRepAll M n), ZeroFlags M n c₀ →
        ∀ (ξP : PlaneCuspSum M n) (ξQ : LineCuspSum M n),
          planeCuspSumEmbedding M n ξP = planeBoundary M n c₀ →
          lineCuspSumEmbedding M n ξQ = lineBoundary M n c₀ →
          ∀ c' : Hd (N := M) (n := n) hn,
            pairP ξP (dualRP hn c') + sumPairing _ _ pairQ ξQ (dualRQ hM hn c') = 0 := by
  obtain ⟨pairP, pairQ, hperf, hP⟩ := F
  refine ⟨pairP, pairQ, hperf, fun c₀ hz ξP ξQ hξP hξQ c' => ?_⟩
  obtain ⟨cV, hcV⟩ := (PhiH_bijective (rhoEn n) (Δ6 M)).2
    (transportΔ M (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl) c₀)
  obtain ⟨cVd, hcVd⟩ := (PhiH_bijective (rhoEn n).dual (Δ6 M)).2
    (transportΔ M (rhoEn n).dual (gammaNRepAll M n).ρ.dual (hρ_dual M (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl))
      (toLiteralG M n c'.1 : groupCohomology.H2 (Rep.of (gammaNRepAll M n).ρ.dual)))
  have hd : toLiteralG M n c'.1 ∈ HdLit hn := by
    obtain ⟨u, hu⟩ := c'.2
    exact ⟨u, congrArg (toLiteralG M n) hu⟩
  have h0 := gamma6_stokes_ind_M M (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl) c₀
    (toLiteralG M n c'.1 : groupCohomology.H2 (Rep.of (gammaNRepAll M n).ρ.dual))
    (fun g => hz g) (fun g => HdLit_zeroFlags hM hn _ hd g) cV hcV cVd hcVd
  rw [hP c₀ hz ξP ξQ hξP hξQ c' cV cVd hcV hcVd] at h0
  exact h0

section LineTerms

variable {M n : ℕ} [NeZero M] {i' : LineFaces M} (D : LineOver M i')

/-- The bilinear form `can6` on the mixed classes of the line face `i` of `Γ(6)`. -/
def can6Bil {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (gammaN 6) V) (i : LineFaces 6) :
    lineMixedSub ρ i →ₗ[ℂ] lineMixedSub ρ.dual i →ₗ[ℂ] ℂ :=
  (facePairingCan (by norm_num : 3 ≤ 6) (lineFaceSplitting 6 i.rep) (lineFaceRadicalInput_det 6 i.rep) (repAt ρ i)).compl₁₂
    (lineMixedToCusp ρ i) (lineMixedToCuspDual ρ i)

theorem can6Bil_apply {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (gammaN 6) V) (i : LineFaces 6) (x : lineMixedSub ρ i) (y : lineMixedSub ρ.dual i) :
    can6Bil ρ i x y = can6 ρ i x y := rfl

theorem toLitG_dualRQ (hM : 3 ≤ M) (hn : 4 ≤ n) (c' : Hd (N := M) (n := n) hn) (i : LineFaces M) :
    toLitG M n i.rep ((dualRQ hM hn c') i).1 =
      twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN M i.rep hp)) (gammaNRepAllDual M n) (toLiteralG M n c'.1) := by
  have h1 : ((dualRQ hM hn c') i).1 = resLine i c'.1 := dualRQ_apply_val hM hn c' i
  rw [h1]
  show toLiteral (gammaNQAt M i.rep) (gammaNQAt_le_N M i.rep) n (resLine i c'.1) = _
  exact toLiteralG_res M n (gammaNQAt M i.rep) (gammaNQAt_le_N M i.rep) c'.1

theorem LineOver.JE_eq_termX (c₀ : groupCohomology.H2 (gammaNRepAll M n)) (hz : ZeroFlags M n c₀) (ξ : lineFaceCuspidal M i'.rep n)
    (hξ : lineFaceCuspidalEmbedding M i'.rep n ξ = rLine M n i'.rep c₀)
    (cV : groupCohomology.H2 (Rep.of (permRep (rhoEn n) (Δ6 M))))
    (hcV : PhiH (rhoEn n) (Δ6 M) cV = transportΔ M (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl) c₀) :
    D.JE n ξ = lineTermX c₀ hz cV hcV D.i D.o := by
  apply Subtype.ext
  rw [D.termX_eq n c₀ hz cV hcV, ← hξ]
  rfl

theorem LineOver.JD_eq_termY (hM : 3 ≤ M) (hn : 4 ≤ n) (c' : Hd (N := M) (n := n) hn)
    (cVd : groupCohomology.H2 (Rep.of (permRep (rhoEn n).dual (Δ6 M))))
    (hcVd : PhiH (rhoEn n).dual (Δ6 M) cVd = transportΔ M (rhoEn n).dual (gammaNRepAll M n).ρ.dual
      (hρ_dual M (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl))
      (toLiteralG M n c'.1 : groupCohomology.H2 (Rep.of (gammaNRepAll M n).ρ.dual))) :
    D.JD n ((dualRQ hM hn c') i') = lineTermY (toLiteralG M n c'.1) (hdZero n hM hn c') cVd hcVd D.i D.o := by
  apply Subtype.ext
  rw [D.termY_eq n (toLiteralG M n c'.1) (hdZero n hM hn c') cVd hcVd]
  change toK D.i (Rep.of (permRep (rhoEn n) (Δ6 M)).dual) (dualPushG (rhoEn n) (Δ6 M) (lineSub D.i)
    (D.thetaGen (rhoEn n).dual (gammaNRepAll M n).ρ.dual (hρ_dual M (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl))
      (toLitG M n i'.rep ((dualRQ hM hn c') i').1))) = _
  rw [toLitG_dualRQ hM hn c' i']

end LineTerms

section PlaneTerms

variable {M n : ℕ} [NeZero M] {j' : PlaneFaces M} (D : PlaneOver M j')

omit [NeZero M] in
theorem toLitP_res (c' : groupCohomology.H2 (Rep.of (dualRhoC M n))) (j : PlaneFaces M) :
    toLitP n (planeFaceRepr j) (resToC M n (ρ := dualRhoC M n) (gammaNPAt M (planeFaceRepr j)) (gammaNPAt_le M (planeFaceRepr j)) c') =
      twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN M (planeFaceRepr j) hp)) (gammaNRepAllDual M n) (toLiteralG M n c') := by
  show toLiteral (gammaNPAt M (planeFaceRepr j)) (gammaNPAt_le M (planeFaceRepr j)) n
    (resToC M n (ρ := dualRhoC M n) (gammaNPAt M (planeFaceRepr j)) (gammaNPAt_le M (planeFaceRepr j)) c') = _
  exact toLiteralG_res M n (gammaNPAt M (planeFaceRepr j)) (gammaNPAt_le M (planeFaceRepr j)) c'

theorem PlaneOver.JEP_eq_termX (c₀ : groupCohomology.H2 (gammaNRepAll M n)) (hz : ZeroFlags M n c₀)
    (cV : groupCohomology.H2 (Rep.of (permRep (rhoEn n) (Δ6 M))))
    (hcV : PhiH (rhoEn n) (Δ6 M) cV = transportΔ M (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl) c₀) :
    D.JEP n (rPlane M n (planeFaceRepr j') c₀) = (planeTermX c₀ hz cV hcV D.i D.o).1 :=
  (D.termX_eq n c₀ hz cV hcV).symm

theorem PlaneOver.JDP_eq_termY (hM : 3 ≤ M) (hn : 4 ≤ n) (c' : Hd (N := M) (n := n) hn)
    (cVd : groupCohomology.H2 (Rep.of (permRep (rhoEn n).dual (Δ6 M))))
    (hcVd : PhiH (rhoEn n).dual (Δ6 M) cVd = transportΔ M (rhoEn n).dual (gammaNRepAll M n).ρ.dual
      (hρ_dual M (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl))
      (toLiteralG M n c'.1 : groupCohomology.H2 (Rep.of (gammaNRepAll M n).ρ.dual))) :
    D.JDP n ((dualRP hn c') j') = (planeTermY (toLiteralG M n c'.1) (hdZero n hM hn c') cVd hcVd D.i D.o).1 := by
  rw [D.termY_eq n (toLiteralG M n c'.1) (hdZero n hM hn c') cVd hcVd, dualRP_apply_val n hn c' j']
  change toKP D.i (Rep.of (permRep (rhoEn n) (Δ6 M)).dual) (dualPushG (rhoEn n) (Δ6 M) (planeSub D.i)
    (D.thetaGen (rhoEn n).dual (gammaNRepAll M n).ρ.dual (hρ_dual M (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl))
      (toLitP n (planeFaceRepr j') (resToC M n (ρ := dualRhoC M n) (gammaNPAt M (planeFaceRepr j')) (gammaNPAt_le M (planeFaceRepr j')) c'.1)))) = _
  rw [toLitP_res c'.1 j']

end PlaneTerms

section Sums

variable {M n : ℕ} [NeZero M]

/-- The chosen line data over each face of `Γ(M)`. -/
def lineOverOf (h6 : 6 ∣ M) (i' : LineFaces M) : LineOver M i' := Classical.choice (exists_lineOver M h6 i')

/-- The chosen plane data over each face of `Γ(M)`. -/
def planeOverOf (h6 : 6 ∣ M) (j' : PlaneFaces M) : PlaneOver M j' := Classical.choice (exists_planeOver M h6 j')

theorem line_term_ex (h6 : 6 ∣ M) (hM : 3 ≤ M) (hn : 4 ≤ n) (c : LineFaces 6 → ℂ)
    (c₀ : groupCohomology.H2 (gammaNRepAll M n)) (hz : ZeroFlags M n c₀) (ξQ : LineCuspSum M n)
    (hξQ : lineCuspSumEmbedding M n ξQ = lineBoundary M n c₀) (c' : Hd (N := M) (n := n) hn)
    (cV : groupCohomology.H2 (Rep.of (permRep (rhoEn n) (Δ6 M))))
    (cVd : groupCohomology.H2 (Rep.of (permRep (rhoEn n).dual (Δ6 M))))
    (hcV : PhiH (rhoEn n) (Δ6 M) cV = transportΔ M (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl) c₀)
    (hcVd : PhiH (rhoEn n).dual (Δ6 M) cVd = transportΔ M (rhoEn n).dual (gammaNRepAll M n).ρ.dual
      (hρ_dual M (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl))
      (toLiteralG M n c'.1 : groupCohomology.H2 (Rep.of (gammaNRepAll M n).ρ.dual))) (i' : LineFaces M) :
    c (lineOverOf h6 i').i * can6 (permRep (rhoEn n) (Δ6 M)) (lineOverOf h6 i').i
      (lineTermX c₀ hz cV hcV (lineOverOf h6 i').i (lineOverOf h6 i').o)
      (lineTermY (toLiteralG M n c'.1) (hdZero n hM hn c') cVd hcVd (lineOverOf h6 i').i (lineOverOf h6 i').o) =
    c (lineOverOf h6 i').i * can6Bil (permRep (rhoEn n) (Δ6 M)) (lineOverOf h6 i').i
      ((lineOverOf h6 i').JE n (ξQ i')) ((lineOverOf h6 i').JD n ((dualRQ hM hn c') i')) := by
  rw [(lineOverOf h6 i').JE_eq_termX c₀ hz (ξQ i') (lineEmb_component n c₀ ξQ hξQ i') cV hcV,
    (lineOverOf h6 i').JD_eq_termY hM hn c' cVd hcVd]
  rfl

theorem lineSum_ex (h6 : 6 ∣ M) (hM : 3 ≤ M) (hn : 4 ≤ n) (c : LineFaces 6 → ℂ)
    (hFl : ∀ (i : LineFaces 6) (x : lineMixedSub (permRep (rhoEn n) (Δ6 M)) i) (y : lineMixedSub (permRep (rhoEn n) (Δ6 M)).dual i),
      lineFacePairM (permRep (rhoEn n) (Δ6 M)) i x.1 y.1 = c i * can6 (permRep (rhoEn n) (Δ6 M)) i x y)
    (c₀ : groupCohomology.H2 (gammaNRepAll M n)) (hz : ZeroFlags M n c₀) (ξQ : LineCuspSum M n)
    (hξQ : lineCuspSumEmbedding M n ξQ = lineBoundary M n c₀) (c' : Hd (N := M) (n := n) hn)
    (cV : groupCohomology.H2 (Rep.of (permRep (rhoEn n) (Δ6 M))))
    (cVd : groupCohomology.H2 (Rep.of (permRep (rhoEn n).dual (Δ6 M))))
    (hcV : PhiH (rhoEn n) (Δ6 M) cV = transportΔ M (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl) c₀)
    (hcVd : PhiH (rhoEn n).dual (Δ6 M) cVd = transportΔ M (rhoEn n).dual (gammaNRepAll M n).ρ.dual
      (hρ_dual M (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl))
      (toLiteralG M n c'.1 : groupCohomology.H2 (Rep.of (gammaNRepAll M n).ρ.dual))) :
    ∑ i : LineFaces 6, ∑ o : orbitRel.Quotient ↥(lineSub i) (↥(gammaN 6) ⧸ Δ6 M),
      lineFacePairM (permRep (rhoEn n) (Δ6 M)) i (lineTermX c₀ hz cV hcV i o).1
        (lineTermY (toLiteralG M n c'.1) (hdZero n hM hn c') cVd hcVd i o).1 =
    ∑ i' : LineFaces M, c (lineOverOf h6 i').i * can6Bil (permRep (rhoEn n) (Δ6 M)) (lineOverOf h6 i').i
      ((lineOverOf h6 i').JE n (ξQ i')) ((lineOverOf h6 i').JD n ((dualRQ hM hn c') i')) := by
  have h1 : ∀ (i : LineFaces 6) (o : orbitRel.Quotient ↥(lineSub i) (↥(gammaN 6) ⧸ Δ6 M)),
      lineFacePairM (permRep (rhoEn n) (Δ6 M)) i (lineTermX c₀ hz cV hcV i o).1
        (lineTermY (toLiteralG M n c'.1) (hdZero n hM hn c') cVd hcVd i o).1 =
      c i * can6 (permRep (rhoEn n) (Δ6 M)) i (lineTermX c₀ hz cV hcV i o) (lineTermY (toLiteralG M n c'.1) (hdZero n hM hn c') cVd hcVd i o) :=
    fun i o => hFl i _ _
  simp_rw [h1]
  refine Eq.trans (Fintype.sum_sigma (fun x : (Σ i : LineFaces 6, orbitRel.Quotient ↥(lineSub i) (↥(gammaN 6) ⧸ Δ6 M)) =>
    c x.1 * can6 (permRep (rhoEn n) (Δ6 M)) x.1 (lineTermX c₀ hz cV hcV x.1 x.2)
      (lineTermY (toLiteralG M n c'.1) (hdZero n hM hn c') cVd hcVd x.1 x.2))).symm ?_
  rw [← Equiv.sum_comp (lineFaceOverEquiv M h6).symm]
  refine Finset.sum_congr rfl (fun i' _ => ?_)
  have hsymm : (lineFaceOverEquiv M h6).symm i' = ⟨(lineOverOf h6 i').i, (lineOverOf h6 i').o⟩ :=
    ((lineFaceOverEquiv M h6).symm_apply_eq).2 (lineOverOf h6 i').hface.symm
  rw [hsymm]
  exact line_term_ex h6 hM hn c c₀ hz ξQ hξQ c' cV cVd hcV hcVd i'

end Sums

section PlaneSums

variable {M n : ℕ} [NeZero M]

theorem plane_term_ex (h6 : 6 ∣ M) (hM : 3 ≤ M) (hn : 4 ≤ n) (d : PlaneFaces 6 → ℂ)
    (c₀ : groupCohomology.H2 (gammaNRepAll M n)) (hz : ZeroFlags M n c₀) (ξP : PlaneCuspSum M n)
    (hξP : planeCuspSumEmbedding M n ξP = planeBoundary M n c₀) (c' : Hd (N := M) (n := n) hn)
    (cV : groupCohomology.H2 (Rep.of (permRep (rhoEn n) (Δ6 M))))
    (cVd : groupCohomology.H2 (Rep.of (permRep (rhoEn n).dual (Δ6 M))))
    (hcV : PhiH (rhoEn n) (Δ6 M) cV = transportΔ M (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl) c₀)
    (hcVd : PhiH (rhoEn n).dual (Δ6 M) cVd = transportΔ M (rhoEn n).dual (gammaNRepAll M n).ρ.dual
      (hρ_dual M (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl))
      (toLiteralG M n c'.1 : groupCohomology.H2 (Rep.of (gammaNRepAll M n).ρ.dual))) (j' : PlaneFaces M) :
    d (planeOverOf h6 j').i * can6P (permRep (rhoEn n) (Δ6 M)) (planeOverOf h6 j').i
      (planeTermX c₀ hz cV hcV (planeOverOf h6 j').i (planeOverOf h6 j').o)
      (planeTermY (toLiteralG M n c'.1) (hdZero n hM hn c') cVd hcVd (planeOverOf h6 j').i (planeOverOf h6 j').o) =
    (d (planeOverOf h6 j').i • (planeOverOf h6 j').betaP n) (faceCuspidalEmbedding M n (planeFaceRepr j') (ξP j')) ((dualRP hn c') j') := by
  set D := planeOverOf h6 j' with hD
  have hemb : faceCuspidalEmbedding M n (planeFaceRepr j') (ξP j') = rPlane M n (planeFaceRepr j') c₀ := planeEmb_component n c₀ ξP hξP j'
  have hε : faceCuspidalEmbedding M n (planeFaceRepr j') (ξP j') ∈ D.UE n := by
    show D.JEP n _ ∈ planeMixedSub (permRep (rhoEn n) (Δ6 M)) D.i
    rw [hemb, D.JEP_eq_termX c₀ hz cV hcV]
    exact (planeTermX c₀ hz cV hcV D.i D.o).2
  have hε' : (dualRP hn c') j' ∈ D.UD n := by
    show D.JDP n _ ∈ planeMixedSub (permRep (rhoEn n) (Δ6 M)).dual D.i
    rw [D.JDP_eq_termY hM hn c' cVd hcVd]
    exact (planeTermY (toLiteralG M n c'.1) (hdZero n hM hn c') cVd hcVd D.i D.o).2
  rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, D.betaP_apply n _ hε _ hε']
  congr 2
  · apply Subtype.ext
    show (planeTermX c₀ hz cV hcV D.i D.o).1 = _
    exact (D.JEP_eq_termX c₀ hz cV hcV).symm.trans (congrArg (D.JEP n) hemb.symm)
  · apply Subtype.ext
    show (planeTermY (toLiteralG M n c'.1) (hdZero n hM hn c') cVd hcVd D.i D.o).1 = _
    exact (D.JDP_eq_termY hM hn c' cVd hcVd).symm

theorem planeSum_ex (h6 : 6 ∣ M) (hM : 3 ≤ M) (hn : 4 ≤ n) (d : PlaneFaces 6 → ℂ)
    (hFp : ∀ (i : PlaneFaces 6) (x : planeMixedSub (permRep (rhoEn n) (Δ6 M)) i) (y : planeMixedSub (permRep (rhoEn n) (Δ6 M)).dual i),
      planeFacePairM (permRep (rhoEn n) (Δ6 M)) i x.1 y.1 = d i * can6P (permRep (rhoEn n) (Δ6 M)) i x y)
    (c₀ : groupCohomology.H2 (gammaNRepAll M n)) (hz : ZeroFlags M n c₀) (ξP : PlaneCuspSum M n)
    (hξP : planeCuspSumEmbedding M n ξP = planeBoundary M n c₀) (c' : Hd (N := M) (n := n) hn)
    (cV : groupCohomology.H2 (Rep.of (permRep (rhoEn n) (Δ6 M))))
    (cVd : groupCohomology.H2 (Rep.of (permRep (rhoEn n).dual (Δ6 M))))
    (hcV : PhiH (rhoEn n) (Δ6 M) cV = transportΔ M (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl) c₀)
    (hcVd : PhiH (rhoEn n).dual (Δ6 M) cVd = transportΔ M (rhoEn n).dual (gammaNRepAll M n).ρ.dual
      (hρ_dual M (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl))
      (toLiteralG M n c'.1 : groupCohomology.H2 (Rep.of (gammaNRepAll M n).ρ.dual))) :
    ∑ i : PlaneFaces 6, ∑ o : orbitRel.Quotient ↥(planeSub i) (↥(gammaN 6) ⧸ Δ6 M),
      planeFacePairM (permRep (rhoEn n) (Δ6 M)) i (planeTermX c₀ hz cV hcV i o).1
        (planeTermY (toLiteralG M n c'.1) (hdZero n hM hn c') cVd hcVd i o).1 =
    ∑ j' : PlaneFaces M, (d (planeOverOf h6 j').i • (planeOverOf h6 j').betaP n)
      (faceCuspidalEmbedding M n (planeFaceRepr j') (ξP j')) ((dualRP hn c') j') := by
  have h1 : ∀ (i : PlaneFaces 6) (o : orbitRel.Quotient ↥(planeSub i) (↥(gammaN 6) ⧸ Δ6 M)),
      planeFacePairM (permRep (rhoEn n) (Δ6 M)) i (planeTermX c₀ hz cV hcV i o).1
        (planeTermY (toLiteralG M n c'.1) (hdZero n hM hn c') cVd hcVd i o).1 =
      d i * can6P (permRep (rhoEn n) (Δ6 M)) i (planeTermX c₀ hz cV hcV i o) (planeTermY (toLiteralG M n c'.1) (hdZero n hM hn c') cVd hcVd i o) :=
    fun i o => hFp i _ _
  simp_rw [h1]
  refine Eq.trans (Fintype.sum_sigma (fun x : (Σ i : PlaneFaces 6, orbitRel.Quotient ↥(planeSub i) (↥(gammaN 6) ⧸ Δ6 M)) =>
    d x.1 * can6P (permRep (rhoEn n) (Δ6 M)) x.1 (planeTermX c₀ hz cV hcV x.1 x.2)
      (planeTermY (toLiteralG M n c'.1) (hdZero n hM hn c') cVd hcVd x.1 x.2))).symm ?_
  rw [← Equiv.sum_comp (planeFaceOverEquiv M h6).symm]
  refine Finset.sum_congr rfl (fun j' _ => ?_)
  have hsymm : (planeFaceOverEquiv M h6).symm j' = ⟨(planeOverOf h6 j').i, (planeOverOf h6 j').o⟩ :=
    ((planeFaceOverEquiv M h6).symm_apply_eq).2 (planeOverOf h6 j').hface.symm
  rw [hsymm]
  exact plane_term_ex h6 hM hn d c₀ hz ξP hξP c' cV cVd hcV hcVd j'

end PlaneSums

section MainEx

variable {M n : ℕ} [NeZero M]

/-- **`FaceFactorisation6` implies the cone-level factorisation in existence form**: with the lines pairings `c_i · can6(J ·, J' ·)` transported from the induced module by the Mackey transports, and the plane pairing
extended from the mixed subspaces. -/
theorem coneFactorisationEx_of (h6 : 6 ∣ M) (hM : 3 ≤ M) (hn : 4 ≤ n) (FF : FaceFactorisation6) :
    ConeFactorisationEx hM hn := by
  obtain ⟨c, d, hc, hd, hF⟩ := FF
  have hFV := hF _ (permRep (rhoEn n) (Δ6 M))
  refine ⟨sumPairing _ _ (fun j' => (d (planeOverOf h6 j').i • (planeOverOf h6 j').betaP n).compl₁₂
      (faceCuspidalEmbedding M n (planeFaceRepr j')) LinearMap.id),
    fun i' => (c (lineOverOf h6 i').i • can6Bil (permRep (rhoEn n) (Δ6 M)) (lineOverOf h6 i').i).compl₁₂
      ((lineOverOf h6 i').JE n) ((lineOverOf h6 i').JD n), ?_, ?_⟩
  · intro i' a h
    exact (lineOverOf h6 i').pair_left_perfect n h6 (c _) (hc _) (hFV.1 _) a (fun η => h η)
  · intro c₀ hz ξP ξQ hξP hξQ c' cV cVd hcV hcVd
    have hstokes : stokesSum (rhoEn n) (Δ6 M) cV (h2Hom (dualRepHom (rhoEn n) (Δ6 M)) cVd) =
        (∑ i : LineFaces 6, ∑ o : orbitRel.Quotient ↥(lineSub i) (↥(gammaN 6) ⧸ Δ6 M),
          lineFacePairM (permRep (rhoEn n) (Δ6 M)) i (lineTermX c₀ hz cV hcV i o).1
            (lineTermY (toLiteralG M n c'.1) (hdZero n hM hn c') cVd hcVd i o).1) +
        (∑ i : PlaneFaces 6, ∑ o : orbitRel.Quotient ↥(planeSub i) (↥(gammaN 6) ⧸ Δ6 M),
          planeFacePairM (permRep (rhoEn n) (Δ6 M)) i (planeTermX c₀ hz cV hcV i o).1
            (planeTermY (toLiteralG M n c'.1) (hdZero n hM hn c') cVd hcVd i o).1) := rfl
    have hL := lineSum_ex h6 hM hn c (fun i x y => hFV.1 i x y) c₀ hz ξQ hξQ c' cV cVd hcV hcVd
    have hP := planeSum_ex h6 hM hn d (fun i x y => hFV.2 i x y) c₀ hz ξP hξP c' cV cVd hcV hcVd
    refine (hstokes.trans (congrArg₂ (· + ·) hL hP)).trans ?_
    rw [add_comm]
    refine congrArg₂ (· + ·) ?_ ?_
    · rw [sumPairing_apply]
      rfl
    · rw [sumPairing_apply]
      rfl

end MainEx

end Ex

/-- **Proposition C.5 for every `Γ(N)`, `N ≥ 3`, `n ≥ 4`, from the cone-level factorisation in existence form at the level `lcm(N, 6)`.** -/
theorem propC5_gammaN_of_coneFactorisationEx {N n : ℕ} [NeZero N] (hN : 3 ≤ N) (hn : 4 ≤ n)
    (F : ConeFactorisationEx (M := Nat.lcm N 6) (three_le_lcm hN) hn) : PropC5GammaN N n := by
  obtain ⟨pairP, pairQ, hperf, hS⟩ := stokes_of_coneFactorisationEx (three_le_lcm hN) hn F
  obtain ⟨T, hT⟩ := Classical.indefiniteDescription _ (eisensteinP_gammaN (N := Nat.lcm N 6) (n := n) (three_le_lcm hN) hn)
  obtain ⟨Td, hTd⟩ := Classical.indefiniteDescription _ (dualEisenstein_gammaN (N := Nat.lcm N 6) (n := n) (three_le_lcm hN) hn)
  exact propC5_of_face_obligations_at_level n (Nat.dvd_lcm_left N 6) (three_le_lcm hN)
    { T := T
      eisensteinP := hT
      Td := Td
      rPd := dualRP hn
      rQd := dualRQ (three_le_lcm hN) hn
      pairP := pairP
      pairQface := pairQ
      dualEisenstein := hTd
      stokes := hS
      perfectQface := hperf } (eisensteinP_gammaN (N := N) (n := n) hN hn)

/-- **Proposition C.5 for every `Γ(N)`, `N ≥ 3`, `n ≥ 4`, from the factorisation (a′) of the `Γ(6)` cone pairings through S2's canonical pairing alone.** -/
theorem propC5_gammaN_of_faceFactorisation {N n : ℕ} [NeZero N] (hN : 3 ≤ N) (hn : 4 ≤ n) (FF : FaceFactorisation6) :
    PropC5GammaN N n :=
  propC5_gammaN_of_coneFactorisationEx hN hn (coneFactorisationEx_of (Nat.dvd_lcm_right N 6) (three_le_lcm hN) hn FF)

end TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
