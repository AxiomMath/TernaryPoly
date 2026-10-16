module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.ParabolicDuality.CuspRegroup
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.ParabolicDuality.TreeCohomology

@[expose] public section


/-!
# The Farey differential of a cusp function and the cusp formula for the duality pairing

Formalized by Claude Sonnet 5.5.  Context: `ar:eq:facepair`.

For a representation `ρ` of `Γ = Γ(N)` on `E`:
* `Tw ρ`: the functions `Φ : P¹(ℚ) → E` that are twisted equivariant, `Φ (γ x) = γ Φ(x) + f(γ)`, for a crossed homomorphism `f`
  (`EqFn ≤ Tw`: strictly equivariant functions);
* `bdryTw : Tw ρ → C¹(ρ)`, `Φ ↦ (q ↦ Φ(head q) - Φ(tail q))` (the compactly supported Farey cocycle `dΦ`) lands in `ker d_c`;
* `pV_bdry_eq` (**the cusp formula**): for strictly equivariant `Φ` and `G ∈ C¹(ρ')`,
  `⟨dΦ, G⟩ = 2 ∑_{c ∈ cusp orbits} e(Φ(c), G-cocycle(σ_c))`, `σ_c` the generator of the stabilizer of `c`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNParabolicPD

open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.HeckeDuality
  TernaryPoly.RankTwoAugmentedFrames TernaryPoly.BinaryModularSymbol
open scoped Classical

section Triangles

theorem Tk_neg_one_triPlus : Tk (-1) • triPlus = triMinus := by
  have hinv : (Tk (-1))⁻¹ = Tk 1 := by
    rw [inv_eq_iff_mul_eq_one, ← Tk_add]; simp [Tk_zero]
  have h1 : cusp1 ∈ (Tk (-1) • triPlus).1 := by
    rw [mem_tri_smul, hinv, Tk_cusp1]; simp [triPlus]
  have hc2 : Tk 1 • cusp2 = cusp3 :=
    smul_cusp2_eq isGen_cusp3 (Or.inl (by funext i; fin_cases i <;> simp [Tk_01, Tk_11, e1, e2]))
  have h2 : cusp2 ∈ (Tk (-1) • triPlus).1 := by
    rw [mem_tri_smul, hinv, hc2, mem_triPlus_cusps]; tauto
  rcases tri_over_standard_edge h1 h2 with h | h
  · exfalso
    have hz : IsGen (Tk (-1) • cusp2) (fun i => (Tk (-1)).val i 1) := by
      rw [smul_cusp2]; exact col_isGen (Tk (-1)) 1
    have hmem : Tk (-1) • cusp2 ∈ triPlus.1 := by
      have := smul_mem_tri_smul (g := Tk (-1)) (show cusp2 ∈ triPlus.1 by simp [triPlus])
      rwa [h] at this
    have := (mem_triPlus_gen hz).mp hmem
    rw [inV_iff] at this
    simp [Tk_01, Tk_11] at this
  · exact h

end Triangles

section Bdry

variable {N : ℕ} {E : Type} [AddCommGroup E] [Module ℂ E]

/-- The twisted equivariant functions on the cusps. -/
def Tw (ρ : Representation ℂ (gammaNGL N) E) : Submodule ℂ (RationalLine2 → E) where
  carrier := {Φ | ∃ f : gammaNGL N → E, (∀ g h, f (g * h) = ρ g (f h) + f g) ∧
    ∀ (γ : gammaNGL N) (x : RationalLine2), Φ (γ • x) = ρ γ (Φ x) + f γ}
  add_mem' := by
    rintro Φ Ψ ⟨f, hf, hΦ⟩ ⟨g, hg, hΨ⟩
    refine ⟨f + g, fun a b => ?_, fun γ x => ?_⟩
    · simp only [Pi.add_apply, hf, hg, map_add]; abel
    · simp only [Pi.add_apply, hΦ, hΨ, map_add]; abel
  zero_mem' := ⟨0, by simp, by simp⟩
  smul_mem' := by
    rintro c Φ ⟨f, hf, hΦ⟩
    refine ⟨c • f, fun a b => ?_, fun γ x => ?_⟩
    · simp only [Pi.smul_apply, hf, map_smul, smul_add]
    · simp only [Pi.smul_apply, hΦ, map_smul, smul_add]

variable (ρ : Representation ℂ (gammaNGL N) E)

theorem eqFn_le_Tw : EqFn (gammaNGL N) RationalLine2 ρ ≤ Tw ρ := by
  intro Φ hΦ
  exact ⟨0, by simp, fun γ x => by simp [hΦ γ x]⟩

theorem dfun_equivariant (hN : 3 ≤ N) {Φ : RationalLine2 → E} (hΦ : Φ ∈ Tw ρ) (γ : gammaNGL N) (q : OTE) :
    dfun Φ ((γ : IntegralGL) • q) = ρ γ (dfun Φ q) := by
  obtain ⟨f, -, hf⟩ := hΦ
  have hsl : IsSL (γ : IntegralGL) := gammaN_isSL hN γ.2
  unfold dfun
  rw [head_smul hsl, tail_smul hsl]
  have h1 := hf γ (head q)
  have h2 := hf γ (tail q)
  change Φ ((γ : IntegralGL) • head q) = _ at h1
  change Φ ((γ : IntegralGL) • tail q) = _ at h2
  rw [h1, h2, map_sub]
  abel

/-- The Farey differential `dΦ` of a twisted cusp function, as a compactly supported cochain. -/
def bdryTw (hN : 3 ≤ N) : Tw ρ →ₗ[ℂ] C1 ρ where
  toFun Φ := ⟨dfun Φ.1, fun γ q => dfun_equivariant ρ hN Φ.2 γ q, fun q => dfun_swap Φ.1 q⟩
  map_add' Φ Ψ := by
    apply Subtype.ext; funext q
    change dfun (Φ.1 + Ψ.1) q = dfun Φ.1 q + dfun Ψ.1 q
    unfold dfun; simp only [Pi.add_apply]; abel
  map_smul' c Φ := by
    apply Subtype.ext; funext q
    change dfun (c • Φ.1) q = c • dfun Φ.1 q
    unfold dfun; simp only [Pi.smul_apply, smul_sub]

theorem bdryTw_apply (hN : 3 ≤ N) (Φ : Tw ρ) (q : OTE) : (bdryTw ρ hN Φ).1 q = Φ.1 (head q) - Φ.1 (tail q) := rfl

theorem dc_bdryTw (hN : 3 ≤ N) (Φ : Tw ρ) : dc ρ (bdryTw ρ hN Φ) = 0 := by
  apply Subtype.ext; funext t
  change ∑ q ∈ nbF t, (bdryTw ρ hN Φ).1 q = 0
  exact sum_dfun_nbF Φ.1 t

end Bdry


section CuspFormula

variable {N : ℕ} {E E' : Type} [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E']
  {ρ : Representation ℂ (gammaNGL N) E} {ρ' : Representation ℂ (gammaNGL N) E'}

theorem Tk_N_mem : Tk (N : ℤ) ∈ gammaNGL N := by
  simpa using Tk_mem_gammaN (N := N) 1

/-- The generator `g_c T^N g_c⁻¹` of the stabilizer of the cusp `c` in `Γ(N)`. -/
def cuspSigma (c : RationalLine2) : gammaNGL N :=
  ⟨cuspElt c * Tk (N : ℤ) * (cuspElt c)⁻¹, gammaN_conj Tk_N_mem⟩

theorem cuspSigma_val (c : RationalLine2) :
    ((cuspSigma (N := N) c : gammaNGL N) : IntegralGL) = cuspElt c * Tk (N : ℤ) * (cuspElt c)⁻¹ := rfl

theorem cuspSigma_cusp (c : RationalLine2) : ((cuspSigma (N := N) c : gammaNGL N) : IntegralGL) • c = c := by
  have h : (cuspElt c)⁻¹ • c = cusp1 := inv_smul_eq_iff.mpr (cuspElt_cusp1 c).symm
  rw [cuspSigma_val, mul_smul, mul_smul, h, Tk_cusp1, cuspElt_cusp1]

theorem cuspSigma_triangle (c : RationalLine2) (m : ℤ) :
    ((cuspSigma (N := N) c : gammaNGL N) : IntegralGL) • ((cuspElt c * Tk m) • triPlus) =
      (cuspElt c * Tk ((N : ℤ) + m)) • triPlus := by
  rw [cuspSigma_val, ← mul_smul, Tk_add]
  congr 1
  group

/-- Sum of the cochain over one period of the fan at the cusp `c`. -/
theorem fan_sum (C : Coupling ρ ρ') {Φ : RationalLine2 → E} (hΦ : Φ ∈ EqFn (gammaNGL N) RationalLine2 ρ)
    (G : C1 ρ') (c : RationalLine2) :
    ∑ k ∈ Finset.range N, C.e (Φ c) (G.1 ((cuspElt c * Tk (k : ℤ)) • p0.swap)) =
      C.e (Φ c) (coc ρ' G (cuspSigma c)) := by
  let t : ℤ → Tri := fun m => (cuspElt c * Tk m) • triPlus
  have hq : ∀ k : ℕ, G.1 ((cuspElt c * Tk (k : ℤ)) • p0.swap) = pot ρ' G (t k) - pot ρ' G (t ((k : ℤ) - 1)) := by
    intro k
    rw [← pot_delta ρ' G ((cuspElt c * Tk (k : ℤ)) • p0.swap)]
    have h2 : ((cuspElt c * Tk (k : ℤ)) • p0.swap).1.2 = t k := rfl
    have h1 : ((cuspElt c * Tk (k : ℤ)) • p0.swap).1.1 = t ((k : ℤ) - 1) := by
      change (cuspElt c * Tk (k : ℤ)) • triMinus = _
      rw [← Tk_neg_one_triPlus, ← mul_smul]
      show _ = (cuspElt c * Tk ((k : ℤ) - 1)) • triPlus
      congr 1
      rw [mul_assoc, ← Tk_add]
      congr 2
    rw [h1, h2]
  have hsum : ∑ k ∈ Finset.range N, G.1 ((cuspElt c * Tk (k : ℤ)) • p0.swap) =
      pot ρ' G (t ((N : ℤ) + (-1))) - pot ρ' G (t (-1)) := by
    simp_rw [hq]
    have := Finset.sum_range_sub (fun k : ℕ => pot ρ' G (t ((k : ℤ) - 1))) N
    simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] at this
    rw [this]
    simp [sub_eq_add_neg]
  rw [← map_sum, hsum]
  have hσ : t ((N : ℤ) + (-1)) = ((cuspSigma (N := N) c : gammaNGL N) : IntegralGL) • t (-1) :=
    (cuspSigma_triangle c (-1)).symm
  have hpot := pot_smul ρ' G (cuspSigma (N := N) c) (t (-1))
  have hcoc : coc ρ' G (cuspSigma (N := N) c) = pot ρ' G (((cuspSigma (N := N) c : gammaNGL N) : IntegralGL) • triPlus) := rfl
  rw [hσ, hpot, ← hcoc]
  have hfix : ρ (cuspSigma (N := N) c) (Φ c) = Φ c := by
    have := hΦ (cuspSigma (N := N) c) c
    rw [← this]
    change Φ (((cuspSigma (N := N) c : gammaNGL N) : IntegralGL) • c) = Φ c
    rw [cuspSigma_cusp]
  have hI := C.inv (cuspSigma (N := N) c) (Φ c) (pot ρ' G (t (-1)))
  rw [hfix] at hI
  have e1 : (ρ' (cuspSigma (N := N) c)) (pot ρ' G (t (-1))) + coc ρ' G (cuspSigma (N := N) c) - pot ρ' G (t (-1)) =
      (ρ' (cuspSigma (N := N) c)) (pot ρ' G (t (-1))) - pot ρ' G (t (-1)) + coc ρ' G (cuspSigma (N := N) c) := by abel
  rw [e1, map_add, map_sub, hI]
  simp


/-- **The cusp formula for the duality pairing.**  For a strictly equivariant function `Φ` on the cusps and a cochain `G`, the pairing of the
compactly supported cocycle `dΦ` with `G` is `2 ∑_{cusp orbits} ⟨Φ(c), [G](σ_c)⟩`, where `σ_c` generates the stabilizer of `c` in `Γ(N)`. -/
theorem pV_bdry_eq (hN : 3 ≤ N) (C : Coupling ρ ρ') {Φ : RationalLine2 → E}
    (hΦ : Φ ∈ EqFn (gammaNGL N) RationalLine2 ρ) (G : C1 ρ') :
    pV C (gammaNFareyData hN) (bdryTw ρ hN ⟨Φ, eqFn_le_Tw ρ hΦ⟩) G =
      2 * ∑ c ∈ (cuspReps hN).R, C.e (Φ c) (coc ρ' G (cuspSigma c)) := by
  set D := gammaNFareyData hN with hD
  let h₁ : OTE → ℂ := fun q => C.e (Φ (head q)) (G.1 q)
  have hinv : ∀ (γ : gammaNGL N) (q : OTE), h₁ (γ • q) = h₁ q := by
    intro γ q
    have hsl : IsSL (γ : IntegralGL) := gammaN_isSL hN γ.2
    change C.e (Φ (head ((γ : IntegralGL) • q))) (G.1 ((γ : IntegralGL) • q)) = C.e (Φ (head q)) (G.1 q)
    rw [head_smul hsl]
    have h1 : Φ ((γ : IntegralGL) • head q) = ρ γ (Φ (head q)) := hΦ γ (head q)
    have h2 : G.1 ((γ : IntegralGL) • q) = ρ' γ (G.1 q) := G.2.1 γ q
    rw [h1, h2, C.inv]
  have h2eq : ∀ r : OTE, C.e (Φ (tail r)) (G.1 r) = - h₁ r.swap := by
    intro r
    change _ = -C.e (Φ (head r.swap)) (G.1 r.swap)
    rw [head_swap, G.2.2 r, map_neg, neg_neg]
  have hsum : pV C D (bdryTw ρ hN ⟨Φ, eqFn_le_Tw ρ hΦ⟩) G = ∑ r ∈ D.RE.R, (h₁ r + h₁ r.swap) := by
    rw [pV_apply]
    unfold pairR
    refine Finset.sum_congr rfl fun r _ => ?_
    change C.e (Φ (head r) - Φ (tail r)) (G.1 r) = h₁ r + h₁ r.swap
    rw [map_sub, LinearMap.sub_apply, h2eq]
    change h₁ r - -h₁ r.swap = _
    ring
  have hswap : ∑ r ∈ D.RE.R, h₁ r.swap = ∑ r ∈ D.RE.R, h₁ r := by
    have := sum_rep_indep D.freeO D.RE D.RE' h₁ hinv
    rw [this]
    unfold FareyData.RE'
    rw [Finset.sum_image (fun a _ b _ h => by simpa using congrArg OTE.swap h)]
  have hreps : ∑ r ∈ D.RE.R, h₁ r = ∑ r ∈ (edgeReps hN).R, h₁ r :=
    sum_rep_indep D.freeO D.RE (edgeReps hN) h₁ hinv
  rw [hsum, Finset.sum_add_distrib, hswap, ← two_mul, hreps, sum_edgeReps]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← fan_sum C hΦ G c]
  refine Finset.sum_congr rfl fun k _ => ?_
  change C.e (Φ (head ((cuspElt c * Tk (k : ℤ)) • p0.swap))) _ = _
  rw [edgeRep_head]

end CuspFormula

end TernaryPeriodPolynomials.Argument.GammaNParabolicPD
