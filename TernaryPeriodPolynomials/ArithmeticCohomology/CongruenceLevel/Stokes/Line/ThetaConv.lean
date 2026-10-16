module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Line.Theta

@[expose] public section


open scoped MatrixGroups DirectSum
noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange

open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.Argument.SeedC3
open MulAction

section Converse

variable {M : ℕ} [NeZero M] {i' : LineFaces M} (D : LineOver M i')

/-- The change of frame in `GL₂(ℚ)` attached to `q`. -/
def LineOver.cg1 : GL (Fin 2) ℚ :=
  castGL (botRight D.q⁻¹) (botRight D.q) (botRight_q_inv D.q D.hq).2 (botRight_q_inv D.q D.hq).1

/-- The group `S_i ∩ (flag group of frame `cg1 F''`) ∩ Stab`, i.e. `stabAt Stab (lineFlagS i (cg1 F'')) 1`. -/
def LineOver.K1 (F'' : GL (Fin 2) ℚ) : Subgroup ↥(lineSub D.i) :=
  stabAt (StabS (Δ6 M) (lineSub D.i) D.u) (lineFlagS D.i (D.cg1 * F'')) 1

/-- `κ` at the base point. -/
def LineOver.kap1 (F'' : GL (Fin 2) ℚ) : ↥(D.K1 F'') →* ↥(StabS (Δ6 M) (lineSub D.i) D.u) :=
  kappa (StabS (Δ6 M) (lineSub D.i) D.u) (D.K1 F'') 1 (stabAt_hu _ _ 1)

omit [NeZero M] in
theorem LineOver.mu_kap1_val (F'' : GL (Fin 2) ℚ) (k : ↥(D.K1 F'')) :
    ((D.mu (D.kap1 F'' k) : ↥(gammaNQAt M i'.rep)) : SL(3, ℤ)) = (D.u : SL(3, ℤ))⁻¹ * k.1.1.1 * (D.u : SL(3, ℤ)) := by
  have h1 : ((1 : ↥(lineSub D.i))⁻¹ * k.1 * 1 : ↥(lineSub D.i)) = k.1 := by
    simp only [inv_one, one_mul, mul_one]
  show (D.u : SL(3, ℤ))⁻¹ * ((((1 : ↥(lineSub D.i))⁻¹ * k.1 * 1 : ↥(lineSub D.i)) : ↥(lineSub D.i)).1.1 : SL(3, ℤ)) * (D.u : SL(3, ℤ)) = _
  rw [h1]

theorem LineOver.mu_kap1_mem_flag (F'' : GL (Fin 2) ℚ) (k : ↥(D.K1 F'')) :
    D.mu (D.kap1 F'' k) ∈ lineFlagStab M i'.rep F'' := by
  have hFk : (⟨k.1.1.1, k.1.2⟩ : ↥(gammaNQAt 6 D.i.rep)) ∈ lineFlagStab 6 D.i.rep (D.cg1 * F'') := k.2.1
  have hp' : (D.u : SL(3, ℤ))⁻¹ * k.1.1.1 * (D.u : SL(3, ℤ)) ∈ gammaNQAt M i'.rep := by
    have := (D.mu (D.kap1 F'' k)).2
    rw [D.mu_kap1_val] at this
    exact this
  have heq : D.mu (D.kap1 F'' k) = ⟨(D.u : SL(3, ℤ))⁻¹ * k.1.1.1 * (D.u : SL(3, ℤ)), hp'⟩ := Subtype.ext (D.mu_kap1_val F'' k)
  rw [heq]
  have gen : ∀ (a u : SL(3, ℤ)), a = u * (u⁻¹ * a * u) * u⁻¹ := fun a u => by group
  exact (lineFlagStab_iff_chain 6 M D.i.rep i'.rep D.q (D.u : SL(3, ℤ)) D.hq D.hrep ((D.u : SL(3, ℤ))⁻¹ * k.1.1.1 * (D.u : SL(3, ℤ)))
    hp' k.1.1.1 k.1.2 (gen _ _) F'').mpr hFk

/-- The homomorphism `K₁ → flag group of the face `i'`` induced by `μ ∘ κ₁`. -/
def LineOver.nu (F'' : GL (Fin 2) ℚ) : ↥(D.K1 F'') →* ↥(lineFlagStab M i'.rep F'') :=
  (D.mu.comp (D.kap1 F'')).codRestrict _ (D.mu_kap1_mem_flag F'')

theorem LineOver.nu_bijective (h6 : 6 ∣ M) (F'' : GL (Fin 2) ℚ) : Function.Bijective (D.nu F'') := by
  constructor
  · intro a b hab
    have h1 : D.mu (D.kap1 F'' a) = D.mu (D.kap1 F'' b) := congrArg Subtype.val hab
    have h3 : D.kap1 F'' a = D.kap1 F'' b := D.mu_injective h1
    apply Subtype.ext
    have h4 := congrArg (fun x : ↥(StabS (Δ6 M) (lineSub D.i) D.u) => ((x : ↥(lineSub D.i)))) h3
    change (1 : ↥(lineSub D.i))⁻¹ * a.1 * 1 = (1 : ↥(lineSub D.i))⁻¹ * b.1 * 1 at h4
    simp only [inv_one, one_mul, mul_one] at h4
    exact h4
  · intro p
    have hs : (D.u : SL(3, ℤ)) * ((p : ↥(gammaNQAt M i'.rep)) : SL(3, ℤ)) * (D.u : SL(3, ℤ))⁻¹ ∈ gammaNQAt 6 D.i.rep :=
      D.back_mem_Q h6 p.1
    have hF0 : (⟨(D.u : SL(3, ℤ)) * ((p : ↥(gammaNQAt M i'.rep)) : SL(3, ℤ)) * (D.u : SL(3, ℤ))⁻¹, hs⟩ : ↥(gammaNQAt 6 D.i.rep)) ∈
        lineFlagStab 6 D.i.rep (D.cg1 * F'') :=
      (lineFlagStab_iff_chain 6 M D.i.rep i'.rep D.q (D.u : SL(3, ℤ)) D.hq D.hrep ((p : ↥(gammaNQAt M i'.rep)) : SL(3, ℤ)) p.1.2
        ((D.u : SL(3, ℤ)) * ((p : ↥(gammaNQAt M i'.rep)) : SL(3, ℤ)) * (D.u : SL(3, ℤ))⁻¹) hs rfl F'').mp p.2
    have hmemK : (D.back h6 p.1).1 ∈ D.K1 F'' := by
      refine ⟨hF0, ?_⟩
      simp only [inv_one, one_mul, mul_one]
      exact (D.back h6 p.1).2
    refine ⟨⟨(D.back h6 p.1).1, hmemK⟩, ?_⟩
    apply Subtype.ext
    have h5 : D.mu (D.kap1 F'' ⟨(D.back h6 p.1).1, hmemK⟩) = D.mu (D.back h6 p.1) := by
      congr 1
      apply Subtype.ext
      simp [LineOver.kap1, kappa]
    exact h5.trans (D.mu_back h6 p.1)

end Converse

section ConverseGen

variable {M : ℕ} [NeZero M] {i' : LineFaces M} (D : LineOver M i') {E : Type} [AddCommGroup E] [Module ℂ E]
  (ρ : Representation ℂ ↥(gammaN 6) E) (ρM : Representation ℂ ↥(gammaN M) E) (hρ : ∀ x : ↥(Δ6 M), ρM (eΔ M x) = ρ x.1)

theorem rho_bijective {G : Type} [Group G] (ρ : Representation ℂ G E) (g : G) : Function.Bijective (ρ g) := by
  refine ⟨fun a b h => ?_, fun y => ⟨ρ g⁻¹ y, ?_⟩⟩
  · have := congrArg (ρ g⁻¹) h
    rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply, ← Module.End.mul_apply,
      ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at this
  · rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

/-- **Converse mixedness**: if `Θ(ε)` (transported to the line group of `Γ(6)`) vanishes on every flag group of `i`, then `ε` vanishes on every flag group of the face `i'` of `Γ(M)`. -/
theorem LineOver.thetaGen_flag_converse (h6 : 6 ∣ M) (ε : groupCohomology.H2 (lineW i' ρM))
    (hmix : ∀ F₀ : GL (Fin 2) ℚ, twoCohomologyRestriction (lineFlagStab 6 D.i.rep F₀).subtype
      (Rep.res (lineIncl D.i) (Rep.of (permRep ρ (Δ6 M)))) (toK D.i (Rep.of (permRep ρ (Δ6 M))) (D.thetaGen ρ ρM hρ ε)) = 0)
    (F'' : GL (Fin 2) ℚ) :
    twoCohomologyRestriction (lineFlagStab M i'.rep F'').subtype (lineW i' ρM) ε = 0 := by
  have h1 := (toK_res_flag_iff D.i (Rep.of (permRep ρ (Δ6 M))) (D.cg1 * F'') (D.thetaGen ρ ρM hρ ε)).mp (hmix (D.cg1 * F''))
  have h2 := Theta_res_zero_imp ρ (Δ6 M) (lineSub D.i) D.u (lineW i' ρM) D.mu (ρ (D.u : ↥(gammaN 6))) (D.hTgen ρ ρM hρ)
    (lineFlagS D.i (D.cg1 * F'')) ε h1
  set F' := lineFlagStab M i'.rep F'' with hF'
  have hcomm : D.mu.comp (D.kap1 F'') = F'.subtype.comp (D.nu F'') := by ext k; rfl
  have e1 := h2Map_comp D.mu (D.kap1 F'') (lineW i' ρM) (Rep.of (rhoStab ρ (Δ6 M) (lineSub D.i) D.u))
    (Rep.of ((ρ.comp (lineSub D.i).subtype).comp (D.K1 F'').subtype)) (ρ (D.u : ↥(gammaN 6))) (D.hTgen ρ ρM hρ)
    ((ρ.comp (lineSub D.i).subtype) 1)
    (kappa_hT (ρ.comp (lineSub D.i).subtype) (StabS (Δ6 M) (lineSub D.i) D.u) (D.K1 F'') 1 (stabAt_hu _ _ 1)) ε
  have hT₃ := compHT D.mu (D.kap1 F'') (lineW i' ρM) (Rep.of (rhoStab ρ (Δ6 M) (lineSub D.i) D.u))
    (Rep.of ((ρ.comp (lineSub D.i).subtype).comp (D.K1 F'').subtype)) (ρ (D.u : ↥(gammaN 6))) (D.hTgen ρ ρM hρ)
    ((ρ.comp (lineSub D.i).subtype) 1)
    (kappa_hT (ρ.comp (lineSub D.i).subtype) (StabS (Δ6 M) (lineSub D.i) D.u) (D.K1 F'') 1 (stabAt_hu _ _ 1))
  have hTb : Function.Bijective (((ρ.comp (lineSub D.i).subtype) 1).comp (ρ (D.u : ↥(gammaN 6)))) :=
    (rho_bijective (ρ.comp (lineSub D.i).subtype) 1).comp (rho_bijective ρ (D.u : ↥(gammaN 6)))
  have e2 := h2Map_comp F'.subtype (D.nu F'') (lineW i' ρM) (Rep.res F'.subtype (lineW i' ρM))
    (Rep.of ((ρ.comp (lineSub D.i).subtype).comp (D.K1 F'').subtype)) LinearMap.id (fun _ _ => rfl)
    (((ρ.comp (lineSub D.i).subtype) 1).comp (ρ (D.u : ↥(gammaN 6)))) (fun g v => hT₃ g v) ε
  rw [twoCohomologyRestriction_eq_h2Map]
  refine EdgeNat.h2Map_injective (D.nu F'') (Rep.res F'.subtype (lineW i' ρM))
    (Rep.of ((ρ.comp (lineSub D.i).subtype).comp (D.K1 F'').subtype))
    (((ρ.comp (lineSub D.i).subtype) 1).comp (ρ (D.u : ↥(gammaN 6)))) (fun g v => hT₃ g v) (D.nu_bijective h6 F'') hTb ?_
  rw [e2, map_zero]
  refine Eq.trans ?_ (e1.symm.trans h2)
  refine h2Map_congr hcomm.symm _ _ _ _ rfl ε

end ConverseGen

end TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
