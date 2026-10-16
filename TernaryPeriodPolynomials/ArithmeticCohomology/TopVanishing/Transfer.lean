module

public import TernaryPeriodPolynomials.ArithmeticCohomology.TopVanishing.Basic
public import Mathlib.GroupTheory.Index

@[expose] public section


/-!
# Transfer for top-degree vanishing

`H⁴` vanishing passes from a finite-index subgroup `Λ` to an ambient subgroup `Γ`: an invariant
primitive for a `Γ`-invariant cocycle is averaged over the cosets of `Λ` in `Γ`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.TopVanishing

open TernaryPeriodPolynomials.Duality

/-- The translate of a three-cochain by the inverse of `g`. -/
private def shiftInv {G : Type} [Group G] (θ : (Fin 4 → G) → ℂ) (g : G) (x : Fin 4 → G) : ℂ :=
  θ (fun i => g⁻¹ * x i)

private theorem differentialThreeRaw_shiftInv {G : Type} [Group G] (θ : (Fin 4 → G) → ℂ) (g : G)
    (x : Fin 5 → G) :
    differentialThreeRaw (shiftInv θ g) x = differentialThreeRaw θ (fun i => g⁻¹ * x i) := by
  have e : ∀ (a b c d : G),
      shiftInv θ g ![a, b, c, d] = θ ![g⁻¹ * a, g⁻¹ * b, g⁻¹ * c, g⁻¹ * d] := by
    intro a b c d
    unfold shiftInv
    refine congrArg θ (funext fun i => ?_)
    fin_cases i <;> rfl
  unfold differentialThreeRaw
  simp only [e]

private theorem differentialThreeRaw_avg {G : Type} {ι : Type} (s : Finset ι)
    (F : ι → (Fin 4 → G) → ℂ) (c : ℂ) (x : Fin 5 → G) :
    differentialThreeRaw (fun y => c * ∑ q ∈ s, F q y) x =
      c * ∑ q ∈ s, differentialThreeRaw (F q) x := by
  unfold differentialThreeRaw
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_add, mul_sub]

/-- `H⁴` vanishing passes from a finite-index subgroup to the ambient subgroup (transfer). -/
theorem IsTopVanishing.of_le_of_relIndex {G : Type} [Group G] {Λ Γ : Subgroup G} (hle : Λ ≤ Γ)
    (hindex : Λ.relIndex Γ ≠ 0) (h : IsTopVanishing Λ) : IsTopVanishing Γ := by
  intro f hinv hcoc
  obtain ⟨θ', hθ'inv, hθ'⟩ := h f
    (fun γ x => hinv ⟨γ.val, hle γ.property⟩ x) hcoc
  have : (Λ.subgroupOf Γ).FiniteIndex := ⟨hindex⟩
  have : Finite (Γ ⧸ Λ.subgroupOf Γ) := Subgroup.finite_quotient_of_finiteIndex
  have : Fintype (Γ ⧸ Λ.subgroupOf Γ) := Fintype.ofFinite _
  let s : Γ → (Fin 4 → G) → ℂ := fun g => shiftInv θ' (g : G)
  have s_congr : ∀ g₁ g₂ : Γ,
      (QuotientGroup.mk g₁ : Γ ⧸ Λ.subgroupOf Γ) = QuotientGroup.mk g₂ → s g₁ = s g₂ := by
    intro g₁ g₂ hg
    have hmem : g₁⁻¹ * g₂ ∈ Λ.subgroupOf Γ := QuotientGroup.eq.mp hg
    have hmem' : ((g₁⁻¹ * g₂ : Γ) : G) ∈ Λ := Subgroup.mem_subgroupOf.mp hmem
    funext x
    have := hθ'inv ⟨((g₁⁻¹ * g₂ : Γ) : G), hmem'⟩ (fun i => (g₂ : G)⁻¹ * x i)
    simp only [s, shiftInv]
    rw [← this]
    refine congrArg θ' (funext fun i => ?_)
    simp [mul_assoc]
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = Fintype.card (Γ ⧸ Λ.subgroupOf Γ) := ⟨_, rfl⟩
  have hm0 : (m : ℂ) ≠ 0 := by
    have : 0 < m := by
      rw [hm]
      exact Fintype.card_pos_iff.mpr ⟨QuotientGroup.mk 1⟩
    exact_mod_cast this.ne'
  refine ⟨fun x => (1 / (m : ℂ)) * ∑ q : Γ ⧸ Λ.subgroupOf Γ, s q.out x, ?_, ?_⟩
  · intro γ x
    have hshift : ∀ q : Γ ⧸ Λ.subgroupOf Γ, s q.out (fun i => (γ : G) * x i) =
        s (γ⁻¹ • q).out x := by
      intro q
      have h1 : s q.out (fun i => (γ : G) * x i) = s (γ⁻¹ * q.out) x := by
        simp only [s, shiftInv]
        refine congrArg θ' (funext fun i => ?_)
        simp [mul_assoc]
      rw [h1]
      have hq : (QuotientGroup.mk (γ⁻¹ * q.out) : Γ ⧸ Λ.subgroupOf Γ) =
          QuotientGroup.mk (γ⁻¹ • q).out := by
        calc (QuotientGroup.mk (γ⁻¹ * q.out) : Γ ⧸ Λ.subgroupOf Γ)
            = γ⁻¹ • QuotientGroup.mk q.out := rfl
          _ = γ⁻¹ • q := by rw [QuotientGroup.out_eq']
          _ = QuotientGroup.mk (γ⁻¹ • q).out := (QuotientGroup.out_eq' _).symm
      exact congr_fun (s_congr _ _ hq) x
    show (1 / (m : ℂ)) * ∑ q : Γ ⧸ Λ.subgroupOf Γ, s q.out (fun i => (γ : G) * x i) =
      (1 / (m : ℂ)) * ∑ q : Γ ⧸ Λ.subgroupOf Γ, s q.out x
    simp only [hshift]
    congr 1
    exact Equiv.sum_comp (MulAction.toPerm (γ⁻¹ : Γ))
      (fun q : Γ ⧸ Λ.subgroupOf Γ => s q.out x)
  · intro x
    have step : differentialThreeRaw
        (fun y => (1 / (m : ℂ)) * ∑ q : Γ ⧸ Λ.subgroupOf Γ, s q.out y) x =
        (1 / (m : ℂ)) * ∑ q : Γ ⧸ Λ.subgroupOf Γ, differentialThreeRaw (s q.out) x :=
      differentialThreeRaw_avg (Finset.univ : Finset (Γ ⧸ Λ.subgroupOf Γ)) (fun q => s q.out)
        (1 / (m : ℂ)) x
    rw [step]
    have hterm : ∀ q : Γ ⧸ Λ.subgroupOf Γ, differentialThreeRaw (s q.out) x = f x := by
      intro q
      rw [show s q.out = shiftInv θ' ((q.out : Γ) : G) from rfl,
        differentialThreeRaw_shiftInv, hθ']
      have := hinv (q.out : Γ)⁻¹ x
      simpa using this
    simp only [hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← hm, ← mul_assoc, one_div, inv_mul_cancel₀ hm0, one_mul]

end TernaryPeriodPolynomials.TopVanishing
