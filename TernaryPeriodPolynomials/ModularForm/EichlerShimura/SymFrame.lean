module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.HodgePair

@[expose] public section


/-!
# The Hodge frame of `Sym^m` and its inverse, as explicit matrices

Foundation file of the unconditional Eichler--Shimura route.  Binary forms of degree `m` are coefficient vectors `v : Fin (m+1) → ℂ`, read as the
polynomial `Σ v_i t^i` (`t = Y/X`).  The Hodge frame at `z` in the upper half plane is
`e_j(z) = (zt - 1)^j (z̄t - 1)^{m-j}`; `frameE m z` is the matrix whose columns are these vectors
and `frameT m z` is its inverse, given by the explicit coefficients of
`q_i(U) = (c (z̄ U - z))^{m-i} (c (U - 1))^i`, `c = (2iy)⁻¹`.  Both are smooth on the upper half
plane (`contDiff_frameE`, `contDiffOn_frameT`) and `frameE * frameT = 1`
(`frameE_mul_frameT`).

Formalized by Claude Sonnet 5.5.
-/

open Polynomial Complex
open TernaryPeriodPolynomials.Argument.ESFoundations.HodgePair (U isOpen_U)

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ESFoundations.SymFrame

theorem coeff_lin_pow (z : ℂ) (j i : ℕ) :
    ((C z * X - 1) ^ j : ℂ[X]).coeff i = (-1) ^ (j - i) * (j.choose i : ℂ) * z ^ i := by
  have h : ((C z * X - 1) ^ j : ℂ[X]) = (((X + C (-1 : ℂ)) ^ j : ℂ[X])).comp (C z * X) := by
    simp [sub_eq_add_neg]
  rw [h, Polynomial.comp_C_mul_X_coeff, coeff_X_add_C_pow]

variable (m : ℕ)

/-- The Hodge frame vector `e_j(z) = (zt - 1)^j (z̄t - 1)^{m-j}`, dehomogenised at `X = 1`. -/
def epol (z : ℂ) (j : ℕ) : ℂ[X] :=
  (C z * X - 1) ^ j * (C (starRingEnd ℂ z) * X - 1) ^ (m - j)

/-- The frame matrix `E(z)`: column `j` is the coefficient vector of `e_j(z)`. -/
def frameE (z : ℂ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
  Matrix.of fun i j => (epol m z j).coeff i

theorem frameE_apply (z : ℂ) (i j : Fin (m + 1)) :
    frameE m z i j = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal (i : ℕ),
      ((-1) ^ ((j : ℕ) - p.1) * ((j : ℕ).choose p.1 : ℂ) * z ^ p.1) *
        ((-1) ^ (m - j - p.2) * ((m - j).choose p.2 : ℂ) * (starRingEnd ℂ z) ^ p.2) := by
  unfold frameE epol
  simp only [Matrix.of_apply, coeff_mul, coeff_lin_pow]

theorem contDiff_frameE (i j : Fin (m + 1)) :
    ContDiff ℝ ⊤ (fun z : ℂ => frameE m z i j) := by
  simp_rw [frameE_apply]
  refine ContDiff.sum fun p _ => ?_
  refine ContDiff.mul ?_ ?_
  · exact (contDiff_const.mul contDiff_const).mul (contDiff_id.pow _)
  · exact (contDiff_const.mul contDiff_const).mul (Complex.conjCLE.contDiff.pow _)

theorem natDegree_lin_le (a : ℂ) : (C a * X - 1 : ℂ[X]).natDegree ≤ 1 := by
  compute_degree

theorem natDegree_epol_le (z : ℂ) {j : ℕ} (hj : j ≤ m) : (epol m z j).natDegree ≤ m := by
  unfold epol
  refine (natDegree_mul_le).trans ?_
  have h1 : ((C z * X - 1) ^ j : ℂ[X]).natDegree ≤ j :=
    (natDegree_pow_le).trans (by simpa using Nat.mul_le_mul_left j (natDegree_lin_le z))
  have h2 : ((C (starRingEnd ℂ z) * X - 1) ^ (m - j) : ℂ[X]).natDegree ≤ m - j :=
    (natDegree_pow_le).trans
      (by simpa using Nat.mul_le_mul_left (m - j) (natDegree_lin_le (starRingEnd ℂ z)))
  omega

/-- Evaluation of the frame at `t`: `Σ_i E_{ij} t^i = (zt-1)^j (z̄t-1)^{m-j}`. -/
theorem sum_frameE_pow (z t : ℂ) (j : Fin (m + 1)) :
    ∑ i : Fin (m + 1), frameE m z i j * t ^ (i : ℕ) =
      (z * t - 1) ^ (j : ℕ) * (starRingEnd ℂ z * t - 1) ^ (m - j) := by
  have hdeg : (epol m z j).natDegree < m + 1 :=
    Nat.lt_succ_of_le (natDegree_epol_le m z (by omega))
  have h := eval_eq_sum_range' hdeg t
  have e : eval t (epol m z j) = (z * t - 1) ^ (j : ℕ) * (starRingEnd ℂ z * t - 1) ^ (m - j) := by
    simp [epol]
  rw [← e, h, ← Fin.sum_univ_eq_sum_range (fun i => (epol m z j).coeff i * t ^ i)]
  rfl

theorem vec_eq_zero_of_poly {v : Fin (m + 1) → ℂ}
    (h : ∀ t : ℂ, ∑ i : Fin (m + 1), v i * t ^ (i : ℕ) = 0) : v = 0 := by
  let P : ℂ[X] := ∑ i : Fin (m + 1), C (v i) * X ^ (i : ℕ)
  have hP : P = 0 := by
    apply Polynomial.funext
    intro t
    simp only [P, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, eval_zero]
    exact h t
  funext i
  have := congrArg (fun p => p.coeff (i : ℕ)) hP
  simp only [P, finsetSum_coeff, coeff_C_mul, coeff_X_pow, coeff_zero] at this
  rw [Finset.sum_eq_single i] at this
  · simpa using this
  · intro b _ hb
    have : (i : ℕ) ≠ b := fun h => hb (Fin.ext h).symm
    simp [this]
  · simp

/-- The inverse height factor. -/
def cinv (z : ℂ) : ℂ := (2 * I * (z.im : ℂ))⁻¹

/-- The coframe polynomial `q_i(U) = (c (z̄ U - z))^{m-i} (c (U - 1))^i`. -/
def qpol (z : ℂ) (i : ℕ) : ℂ[X] :=
  (C (cinv z * starRingEnd ℂ z) * X - C (cinv z * z)) ^ (m - i) *
    (C (cinv z) * X - C (cinv z)) ^ i

/-- The coframe matrix `T(z)`: column `i` is the coefficient vector of `q_i`. -/
def frameT (z : ℂ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
  Matrix.of fun j i => (qpol m z i).coeff j

theorem coeff_lin_pow' (α β : ℂ) (n k : ℕ) :
    ((C α * X - C β) ^ n : ℂ[X]).coeff k = (-β) ^ (n - k) * (n.choose k : ℂ) * α ^ k := by
  have h : ((C α * X - C β) ^ n : ℂ[X]) = (((X + C (-β : ℂ)) ^ n : ℂ[X])).comp (C α * X) := by
    simp [sub_eq_add_neg]
  rw [h, Polynomial.comp_C_mul_X_coeff, coeff_X_add_C_pow]

theorem frameT_apply (z : ℂ) (j i : Fin (m + 1)) :
    frameT m z j i = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal (j : ℕ),
      ((-(cinv z * z)) ^ (m - i - p.1) * ((m - i).choose p.1 : ℂ) *
          (cinv z * starRingEnd ℂ z) ^ p.1) *
        ((-cinv z) ^ ((i : ℕ) - p.2) * ((i : ℕ).choose p.2 : ℂ) * (cinv z) ^ p.2) := by
  unfold frameT qpol
  simp only [Matrix.of_apply, coeff_mul, coeff_lin_pow']

theorem natDegree_qpol_le (z : ℂ) {i : ℕ} (hi : i ≤ m) : (qpol m z i).natDegree ≤ m := by
  unfold qpol
  refine (natDegree_mul_le).trans ?_
  have l1 : (C (cinv z * starRingEnd ℂ z) * X - C (cinv z * z) : ℂ[X]).natDegree ≤ 1 := by
    compute_degree
  have l2 : (C (cinv z) * X - C (cinv z) : ℂ[X]).natDegree ≤ 1 := by compute_degree
  have h1 := (natDegree_pow_le (p := (C (cinv z * starRingEnd ℂ z) * X - C (cinv z * z) : ℂ[X]))
    (n := m - i)).trans (by simpa using Nat.mul_le_mul_left (m - i) l1)
  have h2 := (natDegree_pow_le (p := (C (cinv z) * X - C (cinv z) : ℂ[X]))
    (n := i)).trans (by simpa using Nat.mul_le_mul_left i l2)
  omega

theorem sum_frameT_pow (z w : ℂ) (i : Fin (m + 1)) :
    ∑ j : Fin (m + 1), frameT m z j i * w ^ (j : ℕ) = (qpol m z i).eval w := by
  have hdeg : (qpol m z i).natDegree < m + 1 :=
    Nat.lt_succ_of_le (natDegree_qpol_le m z (by omega))
  rw [eval_eq_sum_range' hdeg w,
    ← Fin.sum_univ_eq_sum_range (fun j => (qpol m z i).coeff j * w ^ j)]
  rfl

theorem cinv_mul (z : ℂ) (hz : 0 < z.im) : cinv z * (2 * I * (z.im : ℂ)) = 1 := by
  unfold cinv
  have : (2 * I * (z.im : ℂ)) ≠ 0 := by
    have : (z.im : ℂ) ≠ 0 := by exact_mod_cast hz.ne'
    simp [this]
  exact inv_mul_cancel₀ this

theorem sub_conj_eq (z : ℂ) : z - starRingEnd ℂ z = 2 * I * (z.im : ℂ) := by
  apply Complex.ext <;> simp
  ring

theorem frame_inverse_eval (z t : ℂ) (hz : 0 < z.im) (hw : starRingEnd ℂ z * t - 1 ≠ 0)
    (i : Fin (m + 1)) :
    ∑ j : Fin (m + 1), frameT m z j i * ((z * t - 1) ^ (j : ℕ) *
        (starRingEnd ℂ z * t - 1) ^ (m - j)) = t ^ (i : ℕ) := by
  set u := z * t - 1 with hu
  set w := starRingEnd ℂ z * t - 1 with hw'
  have h1 : ∀ j : Fin (m + 1), u ^ (j : ℕ) * w ^ (m - j) = w ^ m * (u / w) ^ (j : ℕ) := by
    intro j
    have hj : (j : ℕ) ≤ m := by omega
    have : w ^ m = w ^ (j : ℕ) * w ^ (m - j) := by
      rw [← pow_add]; congr 1; omega
    rw [this, div_pow]
    field_simp
  have h2 : ∑ j : Fin (m + 1), frameT m z j i * (u ^ (j : ℕ) * w ^ (m - j)) =
      w ^ m * (qpol m z i).eval (u / w) := by
    rw [← sum_frameT_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [h1]; ring
  rw [h2]
  have hzz : z - starRingEnd ℂ z = 2 * I * (z.im : ℂ) := sub_conj_eq z
  have hc := cinv_mul z hz
  have e1 : starRingEnd ℂ z * u - z * w = z - starRingEnd ℂ z := by
    rw [hu, hw']; ring
  have e2 : u - w = (z - starRingEnd ℂ z) * t := by
    rw [hu, hw']; ring
  simp only [qpol, eval_mul, eval_pow, eval_sub, eval_C, eval_X]
  have e3 : w ^ m = w ^ (m - (i : ℕ)) * w ^ (i : ℕ) := by
    rw [← pow_add]; congr 1; omega
  have f1 : w * (cinv z * starRingEnd ℂ z * (u / w) - cinv z * z) = 1 := by
    have : w * (cinv z * starRingEnd ℂ z * (u / w) - cinv z * z) =
        cinv z * (starRingEnd ℂ z * u - z * w) := by field_simp
    rw [this, e1, hzz, hc]
  have f2 : w * (cinv z * (u / w) - cinv z) = t := by
    have : w * (cinv z * (u / w) - cinv z) = cinv z * (u - w) := by field_simp
    rw [this, e2, hzz]
    linear_combination t * hc
  have e4 : w ^ (m - (i : ℕ)) * w ^ (i : ℕ) *
      ((cinv z * starRingEnd ℂ z * (u / w) - cinv z * z) ^ (m - (i : ℕ)) *
      (cinv z * (u / w) - cinv z) ^ (i : ℕ)) =
      (w * (cinv z * starRingEnd ℂ z * (u / w) - cinv z * z)) ^ (m - (i : ℕ)) *
      (w * (cinv z * (u / w) - cinv z)) ^ (i : ℕ) := by
    rw [mul_pow, mul_pow]; ring
  rw [e3, e4, f1, f2]
  simp

theorem eval_epol (z t : ℂ) (j : ℕ) :
    (epol m z j).eval t = (z * t - 1) ^ j * (starRingEnd ℂ z * t - 1) ^ (m - j) := by
  simp [epol]

theorem frameT_sum_epol (z : ℂ) (hz : 0 < z.im) (i : Fin (m + 1)) :
    ∑ j : Fin (m + 1), C (frameT m z j i) * epol m z j = (X : ℂ[X]) ^ (i : ℕ) := by
  apply Polynomial.eq_of_infinite_eval_eq
  have hz0 : starRingEnd ℂ z ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    exact hz.ne' this
  have hfin : {t : ℂ | starRingEnd ℂ z * t - 1 = 0}.Finite := by
    refine (Set.finite_singleton ((starRingEnd ℂ z)⁻¹)).subset ?_
    intro t ht
    simp only [Set.mem_ofPred_eq] at ht
    simp only [Set.mem_singleton_iff]
    field_simp
    linear_combination ht
  refine Set.Infinite.mono ?_ hfin.infinite_compl
  intro t ht
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at ht ⊢
  simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, eval_epol]
  exact frame_inverse_eval m z t hz ht i

theorem frameE_mul_frameT (z : ℂ) (hz : 0 < z.im) : frameE m z * frameT m z = 1 := by
  ext k i
  have h := congrArg (fun p : ℂ[X] => p.coeff (k : ℕ)) (frameT_sum_epol m z hz i)
  simp only [finsetSum_coeff, coeff_C_mul, coeff_X_pow] at h
  rw [Matrix.mul_apply]
  have : ∑ j : Fin (m + 1), frameE m z k j * frameT m z j i =
      ∑ j : Fin (m + 1), frameT m z j i * (epol m z j).coeff (k : ℕ) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]; rfl
  rw [this, h]
  by_cases hki : k = i
  · subst hki; simp
  · have : (k : ℕ) ≠ (i : ℕ) := fun h => hki (Fin.ext h)
    simp [this, Matrix.one_apply_ne hki]

theorem frameT_mul_frameE (z : ℂ) (hz : 0 < z.im) : frameT m z * frameE m z = 1 :=
  mul_eq_one_comm.mp (frameE_mul_frameT m z hz)

theorem contDiffOn_cinv : ContDiffOn ℝ ⊤ cinv U := by
  unfold cinv
  refine ContDiffOn.inv ?_ ?_
  · exact contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp Complex.imCLM.contDiff).contDiffOn
  · intro z hz
    have : (0 : ℝ) < z.im := hz
    simp [Complex.ext_iff]
    intro h
    exact absurd h (ne_of_gt this)

theorem contDiffOn_frameT (j i : Fin (m + 1)) :
    ContDiffOn ℝ ⊤ (fun z : ℂ => frameT m z j i) U := by
  simp_rw [frameT_apply]
  refine ContDiffOn.sum fun p _ => ?_
  have hc := contDiffOn_cinv
  refine ContDiffOn.mul ?_ ?_
  · refine ContDiffOn.mul (ContDiffOn.mul ?_ contDiffOn_const) ?_
    · exact ((hc.mul contDiffOn_id).neg).pow _
    · exact (hc.mul (Complex.conjCLE.contDiff.contDiffOn)).pow _
  · refine ContDiffOn.mul (ContDiffOn.mul ?_ contDiffOn_const) ?_
    · exact hc.neg.pow _
    · exact hc.pow _

end TernaryPeriodPolynomials.Argument.ESFoundations.SymFrame
