module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Hecke.RecursionAux
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Hecke.RecursionCount

@[expose] public section


/-!
# Hecke recursion: Serre's composition law for the lattice operator

Formalized by Claude Sonnet 5.5.

`latticeOp_comp`: for `z ↦ z + 1`-invariant `F`, `T_p T_{p^{r+1}} F = T_{p^{r+2}} F + p^{k-1} T_{p^r} F` with `T_n = latticeOp k n`.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.LatticeCounts.HeckeRecursion

open Finset Matrix TernaryPeriodPolynomials.Argument.LatticeCounts
open TernaryPeriodPolynomials.Argument.LatticeCounts.LatticeOperator

variable {p : ℕ}

/-! ### The composition law -/

theorem hnfWeight_mul (k : ℤ) {a₁ b₁ d₁ a₂ b₂ d₂ c : ℕ} (ha₁ : 0 < a₁) (hd₁ : 0 < d₁) (ha₂ : 0 < a₂) (hd₂ : 0 < d₂) :
    hnfWeight k (a₁, b₁, d₁) * hnfWeight k (a₂, b₂, d₂) = hnfWeight k (a₂ * a₁, c, d₂ * d₁) := by
  unfold hnfWeight
  simp only
  have h1 : (a₁ : ℂ) ≠ 0 := by exact_mod_cast ha₁.ne'
  have h2 : (a₂ : ℂ) ≠ 0 := by exact_mod_cast ha₂.ne'
  have h3 : (d₁ : ℂ) ≠ 0 := by exact_mod_cast hd₁.ne'
  have h4 : (d₂ : ℂ) ≠ 0 := by exact_mod_cast hd₂.ne'
  push_cast
  rw [show (a₂ : ℂ) * a₁ * (d₂ * d₁) = (a₁ * a₂) * (d₁ * d₂) by ring]
  simp only [mul_zpow]
  ring

theorem hnfWeight_scale {p : ℕ} (hp0 : 0 < p) (k : ℤ) {a b d : ℕ} (ha : 0 < a) (hd : 0 < d) :
    hnfWeight k (p * a, p * b, p * d) = (p : ℂ) ^ (k - 2) * hnfWeight k (a, b, d) := by
  unfold hnfWeight
  simp only
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast hp0.ne'
  have h1 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have h3 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  push_cast
  rw [show (p : ℂ) * a * (p * d) = (p * p) * (a * d) by ring, mul_zpow, mul_zpow, mul_zpow (p : ℂ) d]
  have hpp : (p : ℂ) ^ (k - 1) * (p : ℂ) ^ (k - 1) * (p : ℂ) ^ (-k) = (p : ℂ) ^ (k - 2) := by
    rw [← zpow_add₀ hp, ← zpow_add₀ hp]; congr 1; ring
  linear_combination (((a : ℂ) * d) ^ (k - 1) * (d : ℂ) ^ (-k)) * hpp

theorem hnfAct_scale {p : ℕ} (hp0 : 0 < p) {a b d : ℕ} (ha : 0 < a) (hd : 0 < d) (z : UpperHalfPlane) :
    hnfAct (p * a, p * b, p * d) z = hnfAct (a, b, d) z := by
  apply UpperHalfPlane.ext
  rw [coe_hnfAct (Nat.mul_pos hp0 ha) (Nat.mul_pos hp0 hd), coe_hnfAct ha hd]
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast hp0.ne'
  have h3 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  push_cast
  field_simp

/-- **Serre's composition law** `T_p T_{p^{r+1}} = T_{p^{r+2}} + p^{k-1} T_{p^r}` for the lattice operator, for functions invariant under
`z ↦ z + 1` (only this part of level-one automorphy is used: the product of two Hermite matrices is a Hermite matrix up to a
translation). -/
theorem latticeOp_comp (hp : p.Prime) (k : ℤ) {F : UpperHalfPlane → ℂ} (hF : PerInv F) (r : ℕ) (z : UpperHalfPlane) :
    latticeOp k (p ^ 1) (latticeOp k (p ^ (r + 1)) F) z =
      latticeOp k (p ^ (r + 2)) F z + (p : ℂ) ^ (k - 1) * latticeOp k (p ^ r) F z := by
  have hp0 : 0 < p := hp.pos
  have hr : 0 < p ^ (r + 1) := pow_pos hp0 _
  have hr0 : 0 < p ^ 1 := pow_pos hp0 _
  set g : ℕ × ℕ × ℕ → ℂ := fun T => hnfWeight k T * F (hnfAct T z) with hg
  have step : ∀ t ∈ hnfData (p ^ 1), ∀ s ∈ hnfData (p ^ (r + 1)),
      hnfWeight k t * (hnfWeight k s * F (hnfAct s (hnfAct t z))) = g (redP s t) := by
    intro t ht s hs
    rw [mem_hnfData hr0] at ht
    rw [mem_hnfData hr] at hs
    obtain ⟨ht1, ht2, ht3⟩ := ht
    obtain ⟨hs1, hs2, hs3⟩ := hs
    have htd : 0 < t.2.2 := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at ht2; exact hr0.ne' ht2.symm
    have hsd : 0 < s.2.2 := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hs2; exact hr.ne' hs2.symm
    have hcomp := hnfAct_comp hs1 hsd ht1 htd z
    have hred := perInv_reduce hF (Nat.mul_pos hs1 ht1) (Nat.mul_pos hsd htd)
      (s.1 * t.2.1 + s.2.1 * t.2.2) z
    have hw := hnfWeight_mul k (b₁ := t.2.1) (b₂ := s.2.1) (c := (s.1 * t.2.1 + s.2.1 * t.2.2) % (s.2.2 * t.2.2))
      ht1 htd hs1 hsd
    simp only [hg, redP]
    rw [hcomp, hred, ← mul_assoc, hw]
  unfold latticeOp
  have hlhs : ∑ t ∈ hnfData (p ^ 1), hnfWeight k t * ∑ s ∈ hnfData (p ^ (r + 1)), hnfWeight k s * F (hnfAct s (hnfAct t z)) =
      ∑ t ∈ hnfData (p ^ 1), ∑ s ∈ hnfData (p ^ (r + 1)), g (redP s t) := by
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun s hs => step t ht s hs
  rw [hlhs, pair_sum hp g]
  congr 1
  have hs : ∀ T ∈ hnfData (p ^ r), g (p * T.1, p * T.2.1, p * T.2.2) = (p : ℂ) ^ (k - 2) * g T := by
    intro T hT
    have hr' : 0 < p ^ r := pow_pos hp0 _
    rw [mem_hnfData hr'] at hT
    obtain ⟨h1, h2, h3⟩ := hT
    have hd : 0 < T.2.2 := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at h2; exact hr'.ne' h2.symm
    simp only [hg]
    rw [hnfWeight_scale hp0 k h1 hd, hnfAct_scale hp0 h1 hd]
    ring
  rw [Finset.sum_congr rfl hs, ← Finset.mul_sum, nsmul_eq_mul, ← mul_assoc]
  congr 1
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp0.ne'
  rw [show k - 1 = 1 + (k - 2) by ring, zpow_add₀ hp', zpow_one]

end TernaryPeriodPolynomials.Argument.LatticeCounts.HeckeRecursion
