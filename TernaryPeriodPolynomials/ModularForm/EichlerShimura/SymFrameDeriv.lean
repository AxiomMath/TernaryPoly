module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.SymFrame
public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.Wirtinger

@[expose] public section


/-!
# The Wirtinger derivatives of the Hodge frame

Foundation file of the unconditional Eichler--Shimura route.  The frame `e_j(z) = (zt - 1)^j (z̄t - 1)^{m-j}` satisfies
`∂_z e_j = j (e_j - e_{j-1}) / (2iy)` and `∂_z̄ e_j = (m-j)(e_{j+1} - e_j) / (2iy)`
(`dz_frameE`, `dbar_frameE`); equivalently `∂_z E = E N₁`, `∂_z̄ E = E N₂` with the explicit
bidiagonal matrices `N1`, `N2` (`frameE_mul_N1`, `frameE_mul_N2`).

Formalized by Claude Sonnet 5.5.
-/

open Polynomial Complex
open TernaryPeriodPolynomials.Argument.ESFoundations.HodgePair

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ESFoundations.SymFrame

theorem sum_epol_coeff (m : ℕ) (z t : ℂ) {n : ℕ} (hn : n ≤ m) :
    ∑ i : Fin (m + 1), (epol m z n).coeff i * t ^ (i : ℕ) =
      (z * t - 1) ^ n * (starRingEnd ℂ z * t - 1) ^ (m - n) := by
  have hdeg : (epol m z n).natDegree < m + 1 := Nat.lt_succ_of_le (natDegree_epol_le m z hn)
  have h := eval_eq_sum_range' hdeg t
  have e : eval t (epol m z n) = (z * t - 1) ^ n * (starRingEnd ℂ z * t - 1) ^ (m - n) := by
    simp [epol]
  rw [← e, h, ← Fin.sum_univ_eq_sum_range (fun i => (epol m z n).coeff i * t ^ i)]

theorem differentiableAt_frameE (m : ℕ) (z : ℂ) (i j : Fin (m + 1)) :
    DifferentiableAt ℝ (fun w : ℂ => frameE m w i j) z :=
  ((contDiff_frameE m i j).differentiable (by simp)) z

/-- The generating function of the column derivatives. -/
theorem sum_dz_frameE (m : ℕ) (z t : ℂ) (j : Fin (m + 1)) :
    ∑ i : Fin (m + 1), dz (fun w => frameE m w i j) z * t ^ (i : ℕ) =
      (j : ℕ) * t * (z * t - 1) ^ ((j : ℕ) - 1) * (starRingEnd ℂ z * t - 1) ^ (m - j) := by
  rw [← dz_G m j t z]
  have hfun : (fun w : ℂ => (w * t - 1) ^ (j : ℕ) * (starRingEnd ℂ w * t - 1) ^ (m - j)) =
      fun w => ∑ i : Fin (m + 1), frameE m w i j * t ^ (i : ℕ) := by
    funext w
    exact (sum_frameE_pow m w t j).symm
  rw [hfun, dz_sum _ _ (fun i _ => (differentiableAt_frameE m z i j).mul_const _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dz_mul (differentiableAt_frameE m z i j) (differentiableAt_const _), dz_const]
  ring

theorem sum_dbar_frameE (m : ℕ) (z t : ℂ) (j : Fin (m + 1)) :
    ∑ i : Fin (m + 1), dbar (fun w => frameE m w i j) z * t ^ (i : ℕ) =
      (z * t - 1) ^ (j : ℕ) *
        (((m - j : ℕ) : ℂ) * t * (starRingEnd ℂ z * t - 1) ^ (m - j - 1)) := by
  rw [← dbar_G m j t z]
  have hfun : (fun w : ℂ => (w * t - 1) ^ (j : ℕ) * (starRingEnd ℂ w * t - 1) ^ (m - j)) =
      fun w => ∑ i : Fin (m + 1), frameE m w i j * t ^ (i : ℕ) := by
    funext w
    exact (sum_frameE_pow m w t j).symm
  rw [hfun, dbar_sum _ _ (fun i _ => (differentiableAt_frameE m z i j).mul_const _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dbar_mul (differentiableAt_frameE m z i j) (differentiableAt_const _), dbar_const]
  ring

theorem two_I_im_ne_zero {z : ℂ} (hz : 0 < z.im) : (2 * I * (z.im : ℂ)) ≠ 0 := by
  have : (z.im : ℂ) ≠ 0 := by exact_mod_cast hz.ne'
  simp [this]

/-- **The `∂_z` derivative of the frame**: `∂_z e_j = j (e_j - e_{j-1}) / (2iy)`. -/
theorem dz_frameE (m : ℕ) (z : ℂ) (hz : 0 < z.im) (i j : Fin (m + 1)) :
    dz (fun w => frameE m w i j) z = ((j : ℕ) : ℂ) / (2 * I * (z.im : ℂ)) *
      ((epol m z j).coeff i - (epol m z ((j : ℕ) - 1)).coeff i) := by
  have hne := two_I_im_ne_zero hz
  have hzz := sub_conj_eq z
  set v : Fin (m + 1) → ℂ := fun i => dz (fun w => frameE m w i j) z - ((j : ℕ) : ℂ) /
      (2 * I * (z.im : ℂ)) * ((epol m z j).coeff i - (epol m z ((j : ℕ) - 1)).coeff i) with hv
  have h0 : v = 0 := by
    apply vec_eq_zero_of_poly
    intro t
    have e1 := sum_dz_frameE m z t j
    have e2 := sum_epol_coeff m z t (n := (j : ℕ)) (by omega)
    have e3 := sum_epol_coeff m z t (n := (j : ℕ) - 1) (by omega)
    simp only [hv, sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
    rw [e1, e2, e3]
    rcases Nat.eq_zero_or_pos (j : ℕ) with h0 | hpos
    · simp [h0]
    · set u := z * t - 1 with hu
      set w := starRingEnd ℂ z * t - 1 with hw
      have hj : (j : ℕ) ≤ m := by omega
      have hu1 : u ^ (j : ℕ) = u ^ ((j : ℕ) - 1) * u := by
        rw [← pow_succ]; congr 1; omega
      have hw1 : w ^ (m - ((j : ℕ) - 1)) = w ^ (m - (j : ℕ)) * w := by
        rw [← pow_succ]; congr 1; omega
      have hdiff : u - w = 2 * I * (z.im : ℂ) * t := by
        rw [hu, hw, ← hzz]; ring
      rw [hu1, hw1]
      have hne' : (2 * (I * (z.im : ℂ))) ≠ 0 := by rwa [← mul_assoc]
      have hy : (z.im : ℂ) ≠ 0 := by exact_mod_cast hz.ne'
      have key : ((j : ℕ) : ℂ) / (2 * (I * (z.im : ℂ))) *
          (u ^ ((j : ℕ) - 1) * u * w ^ (m - (j : ℕ)) -
            u ^ ((j : ℕ) - 1) * (w ^ (m - (j : ℕ)) * w)) =
          ((j : ℕ) : ℂ) * t * u ^ ((j : ℕ) - 1) * w ^ (m - (j : ℕ)) := by
        have : u ^ ((j : ℕ) - 1) * u * w ^ (m - (j : ℕ)) -
            u ^ ((j : ℕ) - 1) * (w ^ (m - (j : ℕ)) * w) =
            u ^ ((j : ℕ) - 1) * w ^ (m - (j : ℕ)) * (u - w) := by ring
        rw [this, hdiff]
        field_simp
      linear_combination -key
  exact sub_eq_zero.mp (congrFun h0 i)

/-- **The `∂_z̄` derivative of the frame**: `∂_z̄ e_j = (m - j)(e_{j+1} - e_j) / (2iy)`. -/
theorem dbar_frameE (m : ℕ) (z : ℂ) (hz : 0 < z.im) (i j : Fin (m + 1)) :
    dbar (fun w => frameE m w i j) z = ((m - (j : ℕ) : ℕ) : ℂ) / (2 * I * (z.im : ℂ)) *
      ((epol m z ((j : ℕ) + 1)).coeff i - (epol m z j).coeff i) := by
  have hne := two_I_im_ne_zero hz
  have hzz := sub_conj_eq z
  set v : Fin (m + 1) → ℂ := fun i => dbar (fun w => frameE m w i j) z -
    ((m - (j : ℕ) : ℕ) : ℂ) / (2 * I * (z.im : ℂ)) *
      ((epol m z ((j : ℕ) + 1)).coeff i - (epol m z j).coeff i) with hv
  have h0 : v = 0 := by
    apply vec_eq_zero_of_poly
    intro t
    have e1 := sum_dbar_frameE m z t j
    have e2 := sum_epol_coeff m z t (n := (j : ℕ)) (by omega)
    simp only [hv, sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
    rw [e1, e2]
    rcases Nat.eq_or_lt_of_le (show (j : ℕ) ≤ m by omega) with hjm | hjm
    · simp [hjm]
    · have e3 := sum_epol_coeff m z t (n := (j : ℕ) + 1) (by omega)
      rw [e3]
      set u := z * t - 1 with hu
      set w := starRingEnd ℂ z * t - 1 with hw
      have hw1 : w ^ (m - (j : ℕ)) = w ^ (m - ((j : ℕ) + 1)) * w := by
        rw [← pow_succ]; congr 1; omega
      have hw2 : m - (j : ℕ) - 1 = m - ((j : ℕ) + 1) := by omega
      have hdiff : u - w = 2 * I * (z.im : ℂ) * t := by
        rw [hu, hw, ← hzz]; ring
      have hne' : (2 * (I * (z.im : ℂ))) ≠ 0 := by rwa [← mul_assoc]
      have hy : (z.im : ℂ) ≠ 0 := by exact_mod_cast hz.ne'
      rw [hw1, hw2, pow_succ]
      have key : ((m - (j : ℕ) : ℕ) : ℂ) / (2 * (I * (z.im : ℂ))) *
          (u ^ (j : ℕ) * u * w ^ (m - ((j : ℕ) + 1)) -
            u ^ (j : ℕ) * (w ^ (m - ((j : ℕ) + 1)) * w)) =
          u ^ (j : ℕ) * (((m - (j : ℕ) : ℕ) : ℂ) * t * w ^ (m - ((j : ℕ) + 1))) := by
        have : u ^ (j : ℕ) * u * w ^ (m - ((j : ℕ) + 1)) -
            u ^ (j : ℕ) * (w ^ (m - ((j : ℕ) + 1)) * w) =
            u ^ (j : ℕ) * w ^ (m - ((j : ℕ) + 1)) * (u - w) := by ring
        rw [this, hdiff]
        field_simp
      linear_combination -key
  exact sub_eq_zero.mp (congrFun h0 i)

/-- The matrix of `∂_z` on the frame: `∂_z E = E N₁`. -/
def N1 (m : ℕ) (z : ℂ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
  Matrix.of fun a b => if a = b then ((b : ℕ) : ℂ) / (2 * I * (z.im : ℂ))
    else if (a : ℕ) + 1 = b then -((b : ℕ) : ℂ) / (2 * I * (z.im : ℂ)) else 0

/-- The matrix of `∂_z̄` on the frame: `∂_z̄ E = E N₂`. -/
def N2 (m : ℕ) (z : ℂ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
  Matrix.of fun a b => if a = b then -((m - (b : ℕ) : ℕ) : ℂ) / (2 * I * (z.im : ℂ))
    else if (a : ℕ) = (b : ℕ) + 1 then ((m - (b : ℕ) : ℕ) : ℂ) / (2 * I * (z.im : ℂ)) else 0

theorem frameE_mul_N1 (m : ℕ) (z : ℂ) (i j : Fin (m + 1)) :
    (frameE m z * N1 m z) i j = ((j : ℕ) : ℂ) / (2 * I * (z.im : ℂ)) *
      ((epol m z j).coeff i - (epol m z ((j : ℕ) - 1)).coeff i) := by
  rw [Matrix.mul_apply]
  rcases j with ⟨_ | k, hk⟩
  · rw [Finset.sum_eq_single (⟨0, hk⟩ : Fin (m + 1))]
    · simp [N1, frameE]
    · intro b _ hb
      have : (b : ℕ) ≠ 0 := fun h => hb (Fin.ext h)
      simp [N1, this]
    · simp
  · have hk' : k < m + 1 := by omega
    rw [Finset.sum_eq_add (⟨k + 1, hk⟩ : Fin (m + 1)) (⟨k, hk'⟩ : Fin (m + 1))]
    · simp [N1, frameE]
      ring
    · simp [Fin.ext_iff]
    · intro b _ hb
      have h1 : (b : ℕ) ≠ k + 1 := fun h => hb.1 (Fin.ext h)
      have h2 : (b : ℕ) ≠ k := fun h => hb.2 (Fin.ext h)
      simp [N1, h1, h2, Fin.ext_iff]
    · simp
    · simp

theorem frameE_mul_N2 (m : ℕ) (z : ℂ) (i j : Fin (m + 1)) :
    (frameE m z * N2 m z) i j = ((m - (j : ℕ) : ℕ) : ℂ) / (2 * I * (z.im : ℂ)) *
      ((epol m z ((j : ℕ) + 1)).coeff i - (epol m z j).coeff i) := by
  rw [Matrix.mul_apply]
  by_cases hj : (j : ℕ) < m
  · have hk : (j : ℕ) + 1 < m + 1 := by omega
    rw [Finset.sum_eq_add j (⟨(j : ℕ) + 1, hk⟩ : Fin (m + 1))]
    · simp [N2, frameE, Fin.ext_iff]
      ring
    · simp [Fin.ext_iff]
    · intro b _ hb
      have h1 : (b : ℕ) ≠ j := fun h => hb.1 (Fin.ext h)
      have h2 : (b : ℕ) ≠ (j : ℕ) + 1 := fun h => hb.2 (Fin.ext h)
      simp [N2, h1, h2, Fin.ext_iff]
    · simp
    · simp
  · have hjm : (j : ℕ) = m := by omega
    simp [N2, hjm, frameE]

end TernaryPeriodPolynomials.Argument.ESFoundations.SymFrame
