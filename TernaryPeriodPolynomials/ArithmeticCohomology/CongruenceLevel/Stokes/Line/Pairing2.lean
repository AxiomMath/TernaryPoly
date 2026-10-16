module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Line.Pairing1
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Line.ThetaConv

@[expose] public section


/-!
# The dual-side transport and the line pairings

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

section Part6

variable {M : ℕ} [NeZero M] (n : ℕ) {i' : LineFaces M} (D : LineOver M i')

/-- The raw dual-side transport `𝒞_Q(E^∨) → H²(K_i, Res V^*)`. -/
def LineOver.JDraw : QDi M n i' →ₗ[ℂ] groupCohomology.H2 (Rep.res (lineIncl D.i) (Rep.of (permRep (rhoEn n) (Δ6 M)).dual)) :=
  (toK D.i (Rep.of (permRep (rhoEn n) (Δ6 M)).dual)).comp
    ((dualPushG (rhoEn n) (Δ6 M) (lineSub D.i)).comp
      ((D.thetaGen (rhoEn n).dual (gammaNRepAll M n).ρ.dual (hρ_dual M (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl))).comp
        ((toLitG M n i'.rep).comp (dualCuspidalQ M n i'.rep).subtype)))

theorem LineOver.JDraw_mem (η : QDi M n i') : D.JDraw n η ∈ lineMixedSub (permRep (rhoEn n) (Δ6 M)).dual D.i := by
  have hε := toLitG_mem_lineMixedAt M n i'.rep η.1 η.2
  have hε' : ∀ F'' : GL (Fin 2) ℚ, twoCohomologyRestriction (lineFlagStab M i'.rep F'').subtype (lineW i' (gammaNRepAll M n).ρ.dual)
      (toLitG M n i'.rep η.1) = 0 := fun F'' => LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 hε F'')
  refine (Submodule.mem_iInf _).2 fun F₀ => LinearMap.mem_ker.2 ?_
  refine (toK_res_flag_iff D.i (Rep.of (permRep (rhoEn n) (Δ6 M)).dual) F₀ _).mpr ?_
  refine res_h2Hom_zero (lineFlagS D.i F₀).subtype ((Rep.resFunctor (lineSub D.i).subtype).map (dualRepHom (rhoEn n) (Δ6 M))) _ ?_
  exact (toK_res_flag_iff D.i (Rep.of (permRep (rhoEn n).dual (Δ6 M))) F₀ _).mp
    (D.thetaGen_flag_zero (rhoEn n).dual (gammaNRepAll M n).ρ.dual (hρ_dual M (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl)) _ hε' F₀)

/-- **The dual-side transport** `𝒞_Q(E^∨) → lineMixedSub V^* i`. -/
def LineOver.JD : QDi M n i' →ₗ[ℂ] lineMixedSub (permRep (rhoEn n) (Δ6 M)).dual D.i :=
  (D.JDraw n).codRestrict _ (D.JDraw_mem n)

end Part6

section Part7

variable {M : ℕ} [NeZero M] (n : ℕ) {i' : LineFaces M} (D : LineOver M i')

theorem LineOver.JD_exists (h6 : 6 ∣ M) (y : lineMixedSub (permRep (rhoEn n) (Δ6 M)).dual D.i)
    (hfix : h2E (Rep.res (lineIncl D.i) (Rep.of (permRep (rhoEn n) (Δ6 M)).dual)) (eO (Δ6 M) (lineSub D.i) D.o).dualMap
      (fun k v => eO_dual_equivariantK D (rhoEn n) k v) y.1 = y.1) :
    ∃ η : QDi M n i', D.JD n η = y := by
  obtain ⟨ε', hε'⟩ := D.dual_component_surj (rhoEn n) (gammaNRepAll M n).ρ.dual
    (hρ_dual M (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl)) h6 y.1 hfix
  have hmixy : ∀ F₀ : GL (Fin 2) ℚ, twoCohomologyRestriction (lineFlagStab 6 D.i.rep F₀).subtype
      (Rep.res (lineIncl D.i) (Rep.of (permRep (rhoEn n) (Δ6 M)).dual)) y.1 = 0 := fun F₀ =>
    LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 y.2 F₀)
  have hmix : ∀ F₀ : GL (Fin 2) ℚ, twoCohomologyRestriction (lineFlagStab 6 D.i.rep F₀).subtype
      (Rep.res (lineIncl D.i) (Rep.of (permRep (rhoEn n).dual (Δ6 M))))
      (toK D.i (Rep.of (permRep (rhoEn n).dual (Δ6 M)))
        (D.thetaGen (rhoEn n).dual (gammaNRepAll M n).ρ.dual (hρ_dual M (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl)) ε')) = 0 := by
    intro F₀
    refine (toK_res_flag_iff D.i (Rep.of (permRep (rhoEn n).dual (Δ6 M))) F₀ _).mpr ?_
    have h1 : twoCohomologyRestriction (lineFlagStab 6 D.i.rep F₀).subtype
        (Rep.res (lineIncl D.i) (Rep.of (permRep (rhoEn n) (Δ6 M)).dual))
        (toK D.i (Rep.of (permRep (rhoEn n) (Δ6 M)).dual) (dualPushG (rhoEn n) (Δ6 M) (lineSub D.i)
          (D.thetaGen (rhoEn n).dual (gammaNRepAll M n).ρ.dual (hρ_dual M (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl)) ε'))) = 0 := by
      rw [← hε']; exact hmixy F₀
    have h2 := (toK_res_flag_iff D.i (Rep.of (permRep (rhoEn n) (Δ6 M)).dual) F₀ _).mp h1
    rw [← dualPushG_inv (rhoEn n) (Δ6 M) (lineSub D.i)
      (D.thetaGen (rhoEn n).dual (gammaNRepAll M n).ρ.dual (hρ_dual M (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl)) ε')]
    exact res_h2Hom_zero (lineFlagS D.i F₀).subtype ((Rep.resFunctor (lineSub D.i).subtype).map (dualRepInv (rhoEn n) (Δ6 M))) _ h2
  have hflag := D.thetaGen_flag_converse (rhoEn n).dual (gammaNRepAll M n).ρ.dual
    (hρ_dual M (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl)) h6 ε' hmix
  let ε'' : groupCohomology.H2 (dualRepG (lineFaceRep M i'.rep n)) := ε'
  have hmem : ε'' ∈ lineMixedAt M i'.rep (dualRepG (lineFaceRep M i'.rep n)) :=
    (Submodule.mem_iInf _).2 fun F'' => LinearMap.mem_ker.2 (hflag F'')
  obtain ⟨η, hη, hηe⟩ := exists_dualCuspidal_of_mixed M n i'.rep ε'' hmem
  refine ⟨⟨η, hη⟩, ?_⟩
  apply Subtype.ext
  change D.JDraw n ⟨η, hη⟩ = y.1
  rw [hε']
  show toK D.i (Rep.of (permRep (rhoEn n) (Δ6 M)).dual) (dualPushG (rhoEn n) (Δ6 M) (lineSub D.i)
    (D.thetaGen (rhoEn n).dual (gammaNRepAll M n).ρ.dual (hρ_dual M (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl))
      (toLitG M n i'.rep η))) = _
  rw [hηe]

end Part7

section Part8

variable {M : ℕ} [NeZero M] (n : ℕ) {i' : LineFaces M} (D : LineOver M i')

/-- **Left perfectness of the transported pairing**: if `c ≠ 0` and `B = c · can6` on mixed classes of the induced module (the factorisation (a′) for it), then `ξ ↦ c · can6(J ξ, J' ·)` is left nondegenerate. -/
theorem LineOver.pair_left_perfect (h6 : 6 ∣ M) (c : ℂ) (hc : c ≠ 0)
    (hF : ∀ (x : lineMixedSub (permRep (rhoEn n) (Δ6 M)) D.i) (y : lineMixedSub (permRep (rhoEn n) (Δ6 M)).dual D.i),
      lineFacePairM (permRep (rhoEn n) (Δ6 M)) D.i x.1 y.1 = c * can6 (permRep (rhoEn n) (Δ6 M)) D.i x y)
    (ξ : lineFaceCuspidal M i'.rep n)
    (h : ∀ η : QDi M n i', c * can6 (permRep (rhoEn n) (Δ6 M)) D.i (D.JE n ξ) (D.JD n η) = 0) : ξ = 0 := by
  apply D.JE_injective n h6
  rw [map_zero]
  refine canAt_left_perfect 6 D.i.rep (repAt (permRep (rhoEn n) (Δ6 M)) D.i) (by norm_num) (D.JE n ξ) (fun y₁ => ?_)
  let y : lineMixedSub (permRep (rhoEn n) (Δ6 M)).dual D.i := y₁
  change can6 (permRep (rhoEn n) (Δ6 M)) D.i (D.JE n ξ) y = 0
  have hxfix : h2E (Rep.res (lineIncl D.i) (Rep.of (permRep (rhoEn n) (Δ6 M)))) (eO (Δ6 M) (lineSub D.i) D.o)
      (fun k v => eO_line_equivariant (rhoEn n) (Δ6 M) D.i D.o k v) (D.JE n ξ).1 = (D.JE n ξ).1 :=
    D.component_fixed (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl) _
  let y' : lineMixedSub (permRep (rhoEn n) (Δ6 M)).dual D.i :=
    ⟨h2E (Rep.res (lineIncl D.i) (Rep.of (permRep (rhoEn n) (Δ6 M)).dual)) (eO (Δ6 M) (lineSub D.i) D.o).dualMap
      (fun k v => eO_dual_equivariantK D (rhoEn n) k v) y.1,
      lineMixedSub_h2E_dual (permRep (rhoEn n) (Δ6 M)) D.i (eO (Δ6 M) (lineSub D.i) D.o)
        (fun k v => eO_line_equivariant (rhoEn n) (Δ6 M) D.i D.o k v) y.1 y.2⟩
  have key : c * can6 (permRep (rhoEn n) (Δ6 M)) D.i (D.JE n ξ) y = c * can6 (permRep (rhoEn n) (Δ6 M)) D.i (D.JE n ξ) y' := by
    rw [← hF, ← hF]
    exact lineFacePairM_component (permRep (rhoEn n) (Δ6 M)) D.i (eO (Δ6 M) (lineSub D.i) D.o)
      (fun k v => eO_line_equivariant (rhoEn n) (Δ6 M) D.i D.o k v) (fun v => eO_idem (Δ6 M) (lineSub D.i) D.o v)
      (D.JE n ξ).1 y.1 (D.JE n ξ).2 y.2 hxfix
  have hy'fix : h2E (Rep.res (lineIncl D.i) (Rep.of (permRep (rhoEn n) (Δ6 M)).dual)) (eO (Δ6 M) (lineSub D.i) D.o).dualMap
      (fun k v => eO_dual_equivariantK D (rhoEn n) k v) y'.1 = y'.1 :=
    h2E_idem _ _ _ (fun f => by
      apply LinearMap.ext; intro v
      change f (eO (Δ6 M) (lineSub D.i) D.o (eO (Δ6 M) (lineSub D.i) D.o v)) = f (eO (Δ6 M) (lineSub D.i) D.o v)
      rw [eO_idem]) _
  obtain ⟨η, hη⟩ := D.JD_exists n h6 y' hy'fix
  have h0 := h η
  rw [hη] at h0
  have : can6 (permRep (rhoEn n) (Δ6 M)) D.i (D.JE n ξ) y = 0 := by
    apply mul_left_cancel₀ hc
    rw [key, h0, mul_zero]
  exact this

end Part8

end TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
