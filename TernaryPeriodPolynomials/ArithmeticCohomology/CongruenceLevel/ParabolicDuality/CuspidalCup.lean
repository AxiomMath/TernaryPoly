module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.ParabolicDuality.CuspidalPairing

@[expose] public section


/-!
# The cup formula: the cuspidal pairing is skew

Formalized by Claude Sonnet 5.5.  Paper: `ar:eq:facepair`.

For twisted cusp functions `Φ` (of `A`) and `Φ'` (of `A'`) the Poincaré-Lefschetz pairing of `dΦ` with a cochain representing the class
of `Φ'` is the explicit sum over the three edges leaving each representative Farey triangle `y`:
`cupForm Φ Φ' = ∑_y ∑_{p ∈ nbF y} (⟨Φ(head p), Φ'(tail p)⟩ - ⟨Φ(tail p), Φ'(head p)⟩)`.
This is the cup/Petersson-type formula; it is visibly skew under exchanging `(A, Φ)` and `(A', Φ')` (`cupForm_flip`), so the pairing of
`cuspidal_pairing_exists` is skew-symmetric for a symmetric coupling.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNParabolicPD

open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.HeckeDuality
  TernaryPoly.RankTwoAugmentedFrames TernaryPoly.BinaryModularSymbol Module
open scoped Classical

section CupForm

variable {N : ℕ}

/-- **The cup form** of two cusp functions: the sum over the three edges leaving each representative triangle. -/
def cupForm (hN : 3 ≤ N) {E E' : Type} [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E']
    {ρ : Representation ℂ (gammaNGL N) E} {ρ' : Representation ℂ (gammaNGL N) E'} (C : Coupling ρ ρ')
    (Φ : RationalLine2 → E) (Φ' : RationalLine2 → E') : ℂ :=
  ∑ y ∈ (gammaNFareyData hN).RT.R, ∑ p ∈ nbF y,
    (C.e (Φ (head p)) (Φ' (tail p)) - C.e (Φ (tail p)) (Φ' (head p)))

/-- The cup form is skew under exchanging the two coefficient systems. -/
theorem cupForm_flip (hN : 3 ≤ N) {E E' : Type} [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E']
    {ρ : Representation ℂ (gammaNGL N) E} {ρ' : Representation ℂ (gammaNGL N) E'} (C : Coupling ρ ρ')
    (Φ : RationalLine2 → E) (Φ' : RationalLine2 → E') :
    cupForm hN C.flip Φ' Φ = - cupForm hN C Φ Φ' := by
  unfold cupForm
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Coupling.flip_e]
  simp only [LinearMap.flip_apply]
  ring

end CupForm


section Twisted

variable {N : ℕ} (A' : Rep ℂ (gammaNGL N))

/-- A twisted function on triangles with prescribed crossed homomorphism `g`, vanishing on the representatives. -/
def HhatFn (D : FareyData (gammaNGL N)) (g : gammaNGL N → A') : Tri → A' := fun t => g (dec D.RT t).2

theorem HhatFn_twisted (D : FareyData (gammaNGL N)) (g : gammaNGL N → A')
    (hg : ∀ a b, g (a * b) = A'.ρ a (g b) + g a) (γ : gammaNGL N) (x : Tri) :
    HhatFn A' D g ((γ : IntegralGL) • x) = A'.ρ γ (HhatFn A' D g x) + g γ := by
  have h : dec D.RT ((γ : IntegralGL) • x) = ((dec D.RT x).1, γ * (dec D.RT x).2) :=
    dec_eq D.RT D.freeT (by simp only [mul_smul, dec_spec]; rfl)
  unfold HhatFn
  rw [h]
  exact hg γ _

theorem HhatFn_rep (D : FareyData (gammaNGL N)) (g : gammaNGL N → A') (hg : ∀ a b, g (a * b) = A'.ρ a (g b) + g a)
    {r : Tri} (hr : r ∈ D.RT.R) : HhatFn A' D g r = 0 := by
  have h : dec D.RT r = (⟨r, hr⟩, 1) := dec_eq D.RT D.freeT (by simp)
  unfold HhatFn
  rw [h]
  have := hg 1 1
  simp only [mul_one, map_one, Module.End.one_apply] at this
  have h2 : g 1 + 0 = g 1 + g 1 := by rw [add_zero]; exact this.trans (add_comm _ _)
  exact (add_left_cancel h2).symm

/-- The coboundary of a twisted triangle function, as a cochain. -/
def deltaTw (Hh : Tri → A') (g : gammaNGL N → A') (hH : ∀ (γ : gammaNGL N) (x : Tri), Hh ((γ : IntegralGL) • x) = A'.ρ γ (Hh x) + g γ) :
    C1 A'.ρ :=
  ⟨fun q => Hh q.1.2 - Hh q.1.1, fun γ q => by
    change Hh ((γ : IntegralGL) • q.1.2) - Hh ((γ : IntegralGL) • q.1.1) = A'.ρ γ (Hh q.1.2 - Hh q.1.1)
    rw [hH, hH, map_sub]
    abel, fun q => by
    change Hh q.1.1 - Hh q.1.2 = -(Hh q.1.2 - Hh q.1.1)
    abel⟩

/-- The class of the coboundary of a twisted triangle function is the class of its cocycle. -/
theorem cohMap_deltaTw (Hh : Tri → A') (g : groupCohomology.cocycles₁ A')
    (hH : ∀ (γ : gammaNGL N) (x : Tri), Hh ((γ : IntegralGL) • x) = A'.ρ γ (Hh x) + (g : gammaNGL N → A') γ) :
    cohMap A' (deltaTw A' Hh (g : gammaNGL N → A') hH) = groupCohomology.H1π A' g := by
  rw [cohMap_apply, groupCohomology.H1π_eq_iff]
  refine ⟨Hh triPlus, ?_⟩
  funext γ
  simp only [groupCohomology.d₀₁_hom_apply]
  have hP : ∀ t, Hh t - Hh triPlus = pot A'.ρ (deltaTw A' Hh (g : gammaNGL N → A') hH) t := fun t =>
    pot_unique A'.ρ (deltaTw A' Hh (g : gammaNGL N → A') hH) (P := fun t => Hh t - Hh triPlus) (fun q => by
      change Hh q.1.2 - Hh triPlus - (Hh q.1.1 - Hh triPlus) = Hh q.1.2 - Hh q.1.1
      abel) (by simp) t
  have e1 : (cocycleMap A' (deltaTw A' Hh (g : gammaNGL N → A') hH) : gammaNGL N → A') γ =
      pot A'.ρ (deltaTw A' Hh (g : gammaNGL N → A') hH) ((γ : IntegralGL) • triPlus) := rfl
  have e2 := hP ((γ : IntegralGL) • triPlus)
  have e3 := hH γ triPlus
  change A'.ρ γ (Hh triPlus) - Hh triPlus = ((cocycleMap A' (deltaTw A' Hh (g : gammaNGL N → A') hH) : gammaNGL N → A') - (g : gammaNGL N → A')) γ
  rw [Pi.sub_apply, e1, ← e2, e3]
  abel

end Twisted


section Formula

variable {N : ℕ}

/-- The reversed-and-translated edge `σ⁻¹ • q.swap`, with `σ` the translation of the target triangle of `q` to its representative. -/
def tildeE (D : FareyData (gammaNGL N)) (q : OTE) : OTE :=
  ((((dec D.RT q.1.2).2)⁻¹ : gammaNGL N) : IntegralGL) • q.swap

theorem tildeE_eq (D : FareyData (gammaNGL N)) (q : OTE) (s : gammaNGL N) (hs : (dec D.RT q.1.2).2 = s) :
    tildeE D q = ((s⁻¹ : gammaNGL N) : IntegralGL) • q.swap := by
  unfold tildeE; rw [hs]

theorem tildeE_fst (D : FareyData (gammaNGL N)) (q : OTE) : (tildeE D q).1.1 = ((dec D.RT q.1.2).1 : Tri) := by
  obtain ⟨⟨r, s⟩, hdq⟩ : ∃ p : D.RT.R × gammaNGL N, dec D.RT q.1.2 = p := ⟨_, rfl⟩
  have hspec : s • (r : Tri) = q.1.2 := by
    have := dec_spec D.RT q.1.2
    rw [hdq] at this
    exact this
  rw [tildeE_eq D q s (by rw [hdq]), hdq]
  change (((s⁻¹ : gammaNGL N)) • q.1.2) = (r : Tri)
  rw [← hspec]
  exact inv_smul_smul _ _

theorem tildeE_tildeE (D : FareyData (gammaNGL N)) {q : OTE} (hq : q.1.1 ∈ D.RT.R) : tildeE D (tildeE D q) = q := by
  obtain ⟨⟨r, s⟩, hdq⟩ : ∃ p : D.RT.R × gammaNGL N, dec D.RT q.1.2 = p := ⟨_, rfl⟩
  have h1 : tildeE D q = ((s⁻¹ : gammaNGL N) : IntegralGL) • q.swap := tildeE_eq D q s (by rw [hdq])
  have h2 : dec D.RT (tildeE D q).1.2 = (⟨q.1.1, hq⟩, s⁻¹) := dec_eq D.RT D.freeT (by rw [h1]; rfl)
  have h3 : tildeE D (tildeE D q) = ((s⁻¹⁻¹ : gammaNGL N) : IntegralGL) • (tildeE D q).swap :=
    tildeE_eq D (tildeE D q) (s⁻¹) (by rw [h2])
  rw [h3, h1, OTE.swap_smul, OTE.swap_swap, inv_inv, ← mul_smul]
  simp


theorem step_C (hN : 3 ≤ N) {A A' : Rep ℂ (gammaNGL N)} (C : Coupling A.ρ A'.ρ) {Φ : RationalLine2 → A} (hΦ : Φ ∈ Tw A.ρ)
    {Φ' : RationalLine2 → A'} (hΦ' : Φ' ∈ Tw A'.ρ) (q : OTE) (σ : gammaNGL N) :
    C.e (dfun Φ q) (fTw A' Φ' σ) =
      C.e (dfun Φ q) (Φ' (head q)) +
        C.e (dfun Φ (((σ⁻¹ : gammaNGL N) : IntegralGL) • q.swap))
          (Φ' (tail (((σ⁻¹ : gammaNGL N) : IntegralGL) • q.swap))) := by
  have hsl : IsSL ((σ⁻¹ : gammaNGL N) : IntegralGL) := gammaN_isSL hN (σ⁻¹).2
  set y : RationalLine2 := ((σ⁻¹ : gammaNGL N) : IntegralGL) • head q with hy
  have h1 : Φ' (head q) = A'.ρ σ (Φ' y) + fTw A' Φ' σ := by
    have := fTw_twisted A' hΦ' σ y
    have hsy : (σ : IntegralGL) • y = head q := by
      rw [hy, ← mul_smul]
      have : (σ : IntegralGL) * ((σ⁻¹ : gammaNGL N) : IntegralGL) = 1 := by
        rw [← Subgroup.coe_mul]; simp
      rw [this, one_smul]
    rw [hsy] at this
    exact this
  have h2 : C.e (dfun Φ q) (A'.ρ σ (Φ' y)) =
      - C.e (dfun Φ (((σ⁻¹ : gammaNGL N) : IntegralGL) • q.swap)) (Φ' (tail (((σ⁻¹ : gammaNGL N) : IntegralGL) • q.swap))) := by
    have hI := C.inv (σ⁻¹) (dfun Φ q) (A'.ρ σ (Φ' y))
    have hinv : A'.ρ (σ⁻¹) (A'.ρ σ (Φ' y)) = Φ' y := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [hinv] at hI
    rw [← hI]
    have h3 : A.ρ (σ⁻¹) (dfun Φ q) = dfun Φ (((σ⁻¹ : gammaNGL N) : IntegralGL) • q) :=
      (dfun_equivariant A.ρ hN hΦ (σ⁻¹) q).symm
    have h4 : ((σ⁻¹ : gammaNGL N) : IntegralGL) • q = (((σ⁻¹ : gammaNGL N) : IntegralGL) • q.swap).swap := by
      rw [OTE.swap_smul, OTE.swap_swap]
    have h5 : y = tail (((σ⁻¹ : gammaNGL N) : IntegralGL) • q.swap) := by
      rw [hy, ← head_smul hsl, h4, head_swap]
    rw [h3, h4, dfun_swap, map_neg, LinearMap.neg_apply, h5]
  have h6 : fTw A' Φ' σ = Φ' (head q) - A'.ρ σ (Φ' y) := by rw [h1]; abel
  rw [h6, map_sub, h2]
  ring


theorem mem_RE_iff (D : FareyData (gammaNGL N)) (r : OTE) : r ∈ D.RE.R ↔ r.1.1 ∈ D.RT.R := by
  unfold FareyData.RE
  simp only [Finset.mem_biUnion, mem_nbF]
  constructor
  · rintro ⟨y, hy, rfl⟩; exact hy
  · intro h; exact ⟨_, h, rfl⟩

theorem tildeE_mem (D : FareyData (gammaNGL N)) (r : OTE) : tildeE D r ∈ D.RE.R := by
  rw [mem_RE_iff, tildeE_fst]
  exact (dec D.RT r.1.2).1.2

/-- **The cup formula**: the Poincaré-Lefschetz pairing of `dΦ` with the cochain of a twisted triangle function carrying the cocycle of `Φ'`. -/
theorem pV_bdry_deltaTw (hN : 3 ≤ N) {A A' : Rep ℂ (gammaNGL N)} (C : Coupling A.ρ A'.ρ) {Φ : RationalLine2 → A}
    (hΦ : Φ ∈ Tw A.ρ) {Φ' : RationalLine2 → A'} (hΦ' : Φ' ∈ Tw A'.ρ) :
    pV C (gammaNFareyData hN) (bdryTw A.ρ hN ⟨Φ, hΦ⟩)
        (deltaTw A' (HhatFn A' (gammaNFareyData hN) (fTw A' Φ')) (fTw A' Φ')
          (HhatFn_twisted A' (gammaNFareyData hN) (fTw A' Φ') (fTw_cocycle A' hΦ'))) =
      cupForm hN C Φ Φ' := by
  set D := gammaNFareyData hN with hD
  have hg := fTw_cocycle A' hΦ'
  rw [pV_apply]
  unfold pairR
  -- Step 1
  have step1 : ∀ r ∈ D.RE.R,
      C.e ((bdryTw A.ρ hN ⟨Φ, hΦ⟩).1 r) ((deltaTw A' (HhatFn A' D (fTw A' Φ')) (fTw A' Φ')
          (HhatFn_twisted A' D (fTw A' Φ') hg)).1 r) =
      C.e (dfun Φ r) (Φ' (head r)) + C.e (dfun Φ (tildeE D r)) (Φ' (tail (tildeE D r))) := by
    intro r hr
    have hr' : r.1.1 ∈ D.RT.R := (mem_RE_iff D r).mp hr
    have hG : (deltaTw A' (HhatFn A' D (fTw A' Φ')) (fTw A' Φ') (HhatFn_twisted A' D (fTw A' Φ') hg)).1 r =
        fTw A' Φ' (dec D.RT r.1.2).2 := by
      change HhatFn A' D (fTw A' Φ') r.1.2 - HhatFn A' D (fTw A' Φ') r.1.1 = _
      rw [HhatFn_rep A' D (fTw A' Φ') hg hr', sub_zero]
      rfl
    rw [hG]
    exact step_C hN C hΦ hΦ' r (dec D.RT r.1.2).2
  rw [Finset.sum_congr rfl step1, Finset.sum_add_distrib]
  -- Step 2
  have step2 : ∑ r ∈ D.RE.R, C.e (dfun Φ (tildeE D r)) (Φ' (tail (tildeE D r))) =
      ∑ r ∈ D.RE.R, C.e (dfun Φ r) (Φ' (tail r)) := by
    refine Finset.sum_bij' (fun r _ => tildeE D r) (fun r _ => tildeE D r) (fun r _ => tildeE_mem D r)
      (fun r _ => tildeE_mem D r) (fun r hr => tildeE_tildeE D ((mem_RE_iff D r).mp hr))
      (fun r hr => tildeE_tildeE D ((mem_RE_iff D r).mp hr)) (fun r _ => rfl)
  rw [step2, ← Finset.sum_add_distrib]
  -- Step 3
  rw [sum_RE]
  unfold cupForm
  refine Finset.sum_congr rfl fun y _ => ?_
  have hdiag : ∑ p ∈ nbF y, C.e (Φ (head p)) (Φ' (head p)) = ∑ p ∈ nbF y, C.e (Φ (tail p)) (Φ' (tail p)) :=
    (sum_head_nbF (fun x => C.e (Φ x) (Φ' x)) y).trans (sum_tail_nbF (fun x => C.e (Φ x) (Φ' x)) y).symm
  have hterm : ∀ p : OTE, C.e (dfun Φ p) (Φ' (head p)) + C.e (dfun Φ p) (Φ' (tail p)) =
      (C.e (Φ (head p)) (Φ' (head p)) - C.e (Φ (tail p)) (Φ' (tail p))) +
        (C.e (Φ (head p)) (Φ' (tail p)) - C.e (Φ (tail p)) (Φ' (head p))) := by
    intro p
    simp only [dfun, map_sub, LinearMap.sub_apply]
    ring
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hdiag, sub_self, zero_add]

end Formula


section Skew

variable {N : ℕ}

/-- **The cuspidal pairing is the cup form**: on classes of twisted cusp functions it is the explicit sum `cupForm`. -/
theorem cuspidal_pairing_cup (hN : 3 ≤ N) (A A' : Rep ℂ (gammaNGL N)) [FiniteDimensional ℂ A] [FiniteDimensional ℂ A']
    (C : Coupling A.ρ A'.ρ) :
    ∃ B : cuspidalSub A →ₗ[ℂ] cuspidalSub A' →ₗ[ℂ] ℂ,
      (∀ x, (∀ y, B x y = 0) → x = 0) ∧ (∀ y, (∀ x, B x y = 0) → y = 0) ∧
      ∀ (Φ : Tw A.ρ) (Φ' : Tw A'.ρ), Φ.1 cusp1 = 0 →
        B ⟨mTw A Φ, mTw_mem_cuspidal A Φ⟩ ⟨mTw A' Φ', mTw_mem_cuspidal A' Φ'⟩ = cupForm hN C Φ.1 Φ'.1 := by
  obtain ⟨B, hl, hr, hB⟩ := cuspidal_pairing_exists hN A A' C
  refine ⟨B, hl, hr, fun Φ Φ' h0 => ?_⟩
  set D := gammaNFareyData hN
  have hg := fTw_cocycle A' Φ'.2
  let gc : groupCohomology.cocycles₁ A' := ⟨fTw A' Φ'.1, fTwL_mem A' Φ'⟩
  let G := deltaTw A' (HhatFn A' D (fTw A' Φ'.1)) (fTw A' Φ'.1) (HhatFn_twisted A' D (fTw A' Φ'.1) hg)
  have hcoh : cohMap A' G = mTw A' Φ' := cohMap_deltaTw A' _ gc _
  have hG : cohMap A' G ∈ cuspidalSub A' := by rw [hcoh]; exact mTw_mem_cuspidal A' Φ'
  have := hB Φ G h0 hG
  have hsub : (⟨cohMap A' G, hG⟩ : cuspidalSub A') = ⟨mTw A' Φ', mTw_mem_cuspidal A' Φ'⟩ := Subtype.ext hcoh
  rw [hsub] at this
  rw [this]
  exact pV_bdry_deltaTw hN C Φ.2 Φ'.2

/-- **Skew-symmetry**: the cuspidal pairing of `(A, A')` and that of `(A', A)` (for the transposed coupling) are negatives of each other. -/
theorem cuspidal_pairing_skew (hN : 3 ≤ N) (A A' : Rep ℂ (gammaNGL N)) [FiniteDimensional ℂ A] [FiniteDimensional ℂ A']
    (C : Coupling A.ρ A'.ρ) :
    ∃ (B : cuspidalSub A →ₗ[ℂ] cuspidalSub A' →ₗ[ℂ] ℂ) (B' : cuspidalSub A' →ₗ[ℂ] cuspidalSub A →ₗ[ℂ] ℂ),
      (∀ x, (∀ y, B x y = 0) → x = 0) ∧ (∀ y, (∀ x, B x y = 0) → y = 0) ∧
      (∀ y, (∀ x, B' y x = 0) → y = 0) ∧ (∀ x, (∀ y, B' y x = 0) → x = 0) ∧
      ∀ x y, B x y = - B' y x := by
  obtain ⟨B, hl, hr, hB⟩ := cuspidal_pairing_cup hN A A' C
  obtain ⟨B', hl', hr', hB'⟩ := cuspidal_pairing_cup hN A' A C.flip
  refine ⟨B, B', hl, hr, hl', hr', ?_⟩
  rintro ⟨x, hx⟩ ⟨y, hy⟩
  obtain ⟨Φ, h0, rfl⟩ := exists_Tn_of_cuspidal hN A hx
  obtain ⟨Φ', h0', rfl⟩ := exists_Tn_of_cuspidal hN A' hy
  rw [hB Φ Φ' h0, hB' Φ' Φ h0', cupForm_flip]
  ring

end Skew

end TernaryPeriodPolynomials.Argument.GammaNParabolicPD
