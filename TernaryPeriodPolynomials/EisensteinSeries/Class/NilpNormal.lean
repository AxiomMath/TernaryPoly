module

public import Mathlib

@[expose] public section


/-!
# Normal form of a rank-one nilpotent integral `2 × 2` matrix

`rankOne_normalForm`: if `a, b ∈ ℤ²` are nonzero and orthogonal, then `a bᵀ = μ B⁻¹ E₁₂ B` with
`B ∈ SL₂(ℤ)` and `μ ≠ 0`.

Formalized by Claude Sonnet 5.5.
-/

open Matrix MatrixGroups
noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinClass

/-- A rank-one square-zero integral matrix `a bᵀ` is `μ B⁻¹ E₁₂ B` for some `B ∈ SL₂(ℤ)`, `μ ≠ 0`. -/
theorem rankOne_normalForm (a b : Fin 2 → ℤ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a 0 * b 0 + a 1 * b 1 = 0) :
    ∃ (B : SL(2, ℤ)) (μ : ℤ), μ ≠ 0 ∧
      Matrix.vecMulVec a b =
        μ • (((B⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * !![0, 1; 0, 0] *
          (B : Matrix (Fin 2) (Fin 2) ℤ)) := by
  set g : ℤ := (Int.gcd (a 0) (a 1) : ℤ) with hg
  have hg0 : g ≠ 0 := by
    intro h
    have : Int.gcd (a 0) (a 1) = 0 := Int.ofNat_eq_zero.mp h
    rw [Int.gcd_eq_zero_iff] at this
    apply ha
    funext i; fin_cases i <;> simp [this.1, this.2]
  obtain ⟨p0, hp0⟩ : g ∣ a 0 := Int.gcd_dvd_left (a 0) (a 1)
  obtain ⟨p1, hp1⟩ : g ∣ a 1 := Int.gcd_dvd_right (a 0) (a 1)
  have hcop : IsCoprime p0 p1 := by
    have h1 : Int.gcd (g * p0) (g * p1) = g.natAbs * Int.gcd p0 p1 := Int.gcd_mul_left g p0 p1
    rw [← hp0, ← hp1] at h1
    have h2 : (Int.gcd (a 0) (a 1) : ℕ) = g.natAbs := by simp [hg]
    rw [h2] at h1
    have hpos : 0 < g.natAbs := Int.natAbs_pos.mpr hg0
    have : Int.gcd p0 p1 = 1 := by
      have h3 : g.natAbs * Int.gcd p0 p1 = g.natAbs * 1 := by rw [mul_one]; exact h1.symm
      exact Nat.eq_of_mul_eq_mul_left hpos h3
    exact Int.isCoprime_iff_gcd_eq_one.mpr this
  obtain ⟨u, v, huv⟩ := hcop
  -- B⁻¹ = [[p0, -v], [p1, u]]
  let Binv : SL(2, ℤ) := ⟨!![p0, -v; p1, u], by
    rw [Matrix.det_fin_two_of]; linarith⟩
  have hs : p0 * b 0 + p1 * b 1 = 0 := by
    have : g * (p0 * b 0 + p1 * b 1) = 0 := by rw [hp0, hp1] at hab; linarith
    exact (mul_eq_zero.mp this).resolve_left hg0
  set c : ℤ := -v * b 0 + u * b 1 with hc
  have hb0 : b 0 = -p1 * c := by rw [hc]; linear_combination (u) * hs - (b 0) * huv
  have hb1 : b 1 = p0 * c := by rw [hc]; linear_combination (v) * hs - (b 1) * huv
  have hc0 : c ≠ 0 := by
    intro h0
    apply hb
    funext i; fin_cases i <;> simp [hb0, hb1, h0]
  refine ⟨Binv⁻¹, g * c, mul_ne_zero hg0 hc0, ?_⟩
  ext i j
  have hinv : (((Binv⁻¹)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![p0, -v; p1, u] := by
    rw [inv_inv]
  have hinv2 : ((Binv⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![u, v; -p1, p0] := by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    simp [Binv]
  rw [hinv, hinv2]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.vecMulVec, hp0, hp1, hb0, hb1] <;> ring

end TernaryPeriodPolynomials.Argument.EisensteinClass
