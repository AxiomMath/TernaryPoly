module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.SymFrameDeriv

@[expose] public section


/-!
# Closed and co-closed forms in the Hodge frame: the pair system

Foundation file of the unconditional Eichler--Shimura route.  Let `A, B : ℂ → ℂ^{m+1}` be the `dz` and `dz̄` components, in monomial coordinates, of a
`Sym^m`-valued one-form, `E = frameE`, `T = frameT = E⁻¹` and `a = T A`, `b = T B` its Hodge frame
components.  With the metric `H = Tᴴ D T`, `D = diag(y^m / C(m,j))` we prove: closedness
`∂_z̄ A = ∂_z B` reads `∂_z̄ a + N₂ a = ∂_z b + N₁ b` (`closed_frame`) and co-closedness
`∂_z̄ (H A) + ∂_z (H B) = 0` reads
`(∂_z̄ (D a) - N₁ᴴ D a) + (∂_z (D b) - N₂ᴴ D b) = 0` (`coclosed_frame`); the sum and the difference
of the two decouple the system (`pair_components`): for `0 ≤ k < m`,

  `2iy ∂_z̄ a_k = (m-k) a_k - (k+1) b_{k+1} = 2iy ∂_z b_{k+1}`  (`pair_system`),

and `∂_z̄ a_m = 0` (`top_holo`), `∂_z b_0 = 0` (`bottom_antiholo`).

Formalized by Claude Sonnet 5.5.
-/

open Polynomial Complex Matrix
open TernaryPeriodPolynomials.Argument.ESFoundations.HodgePair

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ESFoundations.SymFrame

variable {n : ℕ}

/-- Componentwise `∂_z̄` of a vector-valued function. -/
def dbarV (g : ℂ → Fin n → ℂ) (z : ℂ) : Fin n → ℂ := fun i => dbar (fun w => g w i) z

/-- Componentwise `∂_z` of a vector-valued function. -/
def dzV (g : ℂ → Fin n → ℂ) (z : ℂ) : Fin n → ℂ := fun i => dz (fun w => g w i) z

/-- Entrywise `∂_z̄` of a matrix-valued function. -/
def dbarM (M : ℂ → Matrix (Fin n) (Fin n) ℂ) (z : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => dbar (fun w => M w i j) z

/-- Entrywise `∂_z` of a matrix-valued function. -/
def dzM (M : ℂ → Matrix (Fin n) (Fin n) ℂ) (z : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => dz (fun w => M w i j) z

/-- Differentiability of a vector-valued function at a point. -/
def DiffV (g : ℂ → Fin n → ℂ) (z : ℂ) : Prop := ∀ i, DifferentiableAt ℝ (fun w => g w i) z

/-- Differentiability of a matrix-valued function at a point. -/
def DiffM (M : ℂ → Matrix (Fin n) (Fin n) ℂ) (z : ℂ) : Prop :=
  ∀ i j, DifferentiableAt ℝ (fun w => M w i j) z

theorem dbarV_mulVec {M : ℂ → Matrix (Fin n) (Fin n) ℂ} {g : ℂ → Fin n → ℂ} {z : ℂ}
    (hM : DiffM M z) (hg : DiffV g z) :
    dbarV (fun w => M w *ᵥ g w) z = dbarM M z *ᵥ g z + M z *ᵥ dbarV g z := by
  funext i
  simp only [dbarV, Matrix.mulVec, dotProduct, dbarM, Matrix.of_apply, Pi.add_apply]
  rw [dbar_sum Finset.univ (fun j w => M w i j * g w j)
    (fun j _ => (hM i j).mul (hg j))]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [dbar_mul (hM i j) (hg j)]

theorem dzV_mulVec {M : ℂ → Matrix (Fin n) (Fin n) ℂ} {g : ℂ → Fin n → ℂ} {z : ℂ}
    (hM : DiffM M z) (hg : DiffV g z) :
    dzV (fun w => M w *ᵥ g w) z = dzM M z *ᵥ g z + M z *ᵥ dzV g z := by
  funext i
  simp only [dzV, Matrix.mulVec, dotProduct, dzM, Matrix.of_apply, Pi.add_apply]
  rw [dz_sum Finset.univ (fun j w => M w i j * g w j)
    (fun j _ => (hM i j).mul (hg j))]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [dz_mul (hM i j) (hg j)]

theorem dbarM_conjTranspose {M : ℂ → Matrix (Fin n) (Fin n) ℂ} {z : ℂ} (hM : DiffM M z) :
    dbarM (fun w => (M w)ᴴ) z = (dzM M z)ᴴ := by
  ext i j
  simp only [dbarM, dzM, Matrix.conjTranspose_apply, Matrix.of_apply, star_def]
  exact dbar_conj (hM j i)

theorem dzM_conjTranspose {M : ℂ → Matrix (Fin n) (Fin n) ℂ} {z : ℂ} (hM : DiffM M z) :
    dzM (fun w => (M w)ᴴ) z = (dbarM M z)ᴴ := by
  ext i j
  simp only [dbarM, dzM, Matrix.conjTranspose_apply, Matrix.of_apply, star_def]
  exact dz_conj (hM j i)

theorem diffM_conjTranspose {M : ℂ → Matrix (Fin n) (Fin n) ℂ} {z : ℂ} (hM : DiffM M z) :
    DiffM (fun w => (M w)ᴴ) z := fun i j => by
  simp only [Matrix.conjTranspose_apply, star_def]
  exact (Complex.conjCLE.differentiableAt).comp z (hM j i)

theorem dbar_congr {f g : ℂ → ℂ} {z : ℂ} (h : f =ᶠ[nhds z] g) : dbar f z = dbar g z := by
  unfold dbar
  rw [h.fderiv_eq]

theorem dz_congr {f g : ℂ → ℂ} {z : ℂ} (h : f =ᶠ[nhds z] g) : dz f z = dz g z := by
  unfold dz
  rw [h.fderiv_eq]

theorem dbarV_congr {f g : ℂ → Fin n → ℂ} {z : ℂ} (h : f =ᶠ[nhds z] g) :
    dbarV f z = dbarV g z := by
  funext i
  exact dbar_congr (h.mono fun w hw => congrFun hw i)

theorem dzV_congr {f g : ℂ → Fin n → ℂ} {z : ℂ} (h : f =ᶠ[nhds z] g) :
    dzV f z = dzV g z := by
  funext i
  exact dz_congr (h.mono fun w hw => congrFun hw i)

theorem diffV_mulVec {M : ℂ → Matrix (Fin n) (Fin n) ℂ} {g : ℂ → Fin n → ℂ} {z : ℂ}
    (hM : DiffM M z) (hg : DiffV g z) : DiffV (fun w => M w *ᵥ g w) z := fun i => by
  simp only [Matrix.mulVec, dotProduct]
  exact DifferentiableAt.fun_sum fun j _ => (hM i j).mul (hg j)

section Frame

variable (m : ℕ)

theorem diffM_frameE (z : ℂ) : DiffM (frameE m) z := fun i j => differentiableAt_frameE m z i j

theorem diffM_frameT {z : ℂ} (hz : 0 < z.im) : DiffM (frameT m) z := fun i j =>
  ((contDiffOn_frameT m i j).differentiableOn (by simp) z hz).differentiableAt
    (isOpen_U.mem_nhds hz)

theorem dbarM_frameE {z : ℂ} (hz : 0 < z.im) :
    dbarM (frameE m) z = frameE m z * N2 m z := by
  ext i j
  simp only [dbarM, Matrix.of_apply]
  rw [dbar_frameE m z hz, frameE_mul_N2]

theorem dzM_frameE {z : ℂ} (hz : 0 < z.im) :
    dzM (frameE m) z = frameE m z * N1 m z := by
  ext i j
  simp only [dzM, Matrix.of_apply]
  rw [dz_frameE m z hz, frameE_mul_N1]

theorem eventually_mem_U {z : ℂ} (hz : 0 < z.im) : ∀ᶠ w in nhds z, 0 < w.im :=
  isOpen_U.mem_nhds hz

/-- **Closedness in the Hodge frame**: for `A = E a`, `B = E b`, the closedness `∂_z̄ A = ∂_z B`
reads `∂_z̄ a + N₂ a = ∂_z b + N₁ b`. -/
theorem closed_frame {A B : ℂ → Fin (m + 1) → ℂ} {z : ℂ} (hz : 0 < z.im)
    (hA : DiffV A z) (hB : DiffV B z) (hC : dbarV A z = dzV B z) :
    dbarV (fun w => frameT m w *ᵥ A w) z + N2 m z *ᵥ (frameT m z *ᵥ A z) =
      dzV (fun w => frameT m w *ᵥ B w) z + N1 m z *ᵥ (frameT m z *ᵥ B z) := by
  have hT := diffM_frameT m hz
  have haD := diffV_mulVec hT hA
  have hbD := diffV_mulVec hT hB
  have hEA : (fun w => A w) =ᶠ[nhds z] fun w => frameE m w *ᵥ (frameT m w *ᵥ A w) :=
    (eventually_mem_U hz).mono fun w hw => by
      show A w = frameE m w *ᵥ (frameT m w *ᵥ A w)
      rw [Matrix.mulVec_mulVec, frameE_mul_frameT m w hw, Matrix.one_mulVec]
  have hEB : (fun w => B w) =ᶠ[nhds z] fun w => frameE m w *ᵥ (frameT m w *ᵥ B w) :=
    (eventually_mem_U hz).mono fun w hw => by
      show B w = frameE m w *ᵥ (frameT m w *ᵥ B w)
      rw [Matrix.mulVec_mulVec, frameE_mul_frameT m w hw, Matrix.one_mulVec]
  have h1 : dbarV A z = frameE m z *ᵥ (dbarV (fun w => frameT m w *ᵥ A w) z +
      N2 m z *ᵥ (frameT m z *ᵥ A z)) := by
    rw [dbarV_congr hEA, dbarV_mulVec (diffM_frameE m z) haD, dbarM_frameE m hz,
      Matrix.mulVec_add, ← Matrix.mulVec_mulVec]
    exact add_comm _ _
  have h2 : dzV B z = frameE m z *ᵥ (dzV (fun w => frameT m w *ᵥ B w) z +
      N1 m z *ᵥ (frameT m z *ᵥ B z)) := by
    rw [dzV_congr hEB, dzV_mulVec (diffM_frameE m z) hbD, dzM_frameE m hz,
      Matrix.mulVec_add, ← Matrix.mulVec_mulVec]
    exact add_comm _ _
  have h3 := hC
  rw [h1, h2] at h3
  have inj : ∀ u v : Fin (m + 1) → ℂ, frameE m z *ᵥ u = frameE m z *ᵥ v → u = v := by
    intro u v h
    have h5 := congrArg (fun x => frameT m z *ᵥ x) h
    simpa only [Matrix.mulVec_mulVec, frameT_mul_frameE m z hz, Matrix.one_mulVec] using h5
  exact inj _ _ h3

/-- The Hodge weights `κ_j = 1 / C(m, j)`. -/
def kap (m j : ℕ) : ℝ := 1 / (m.choose j : ℝ)

/-- The diagonal Hodge metric in the frame, `y^m κ_j`. -/
def Dm (m : ℕ) (z : ℂ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
  Matrix.diagonal fun j => ((z.im ^ m * kap m j : ℝ) : ℂ)

/-- The Hodge metric `H = Tᴴ D T` in the monomial coordinates. -/
def Hmat (m : ℕ) (z : ℂ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
  (frameT m z)ᴴ * Dm m z * frameT m z

theorem diffM_mul {M N : ℂ → Matrix (Fin n) (Fin n) ℂ} {z : ℂ} (hM : DiffM M z) (hN : DiffM N z) :
    DiffM (fun w => M w * N w) z := fun i j => by
  simp only [Matrix.mul_apply]
  exact DifferentiableAt.fun_sum fun k _ => (hM i k).mul (hN k j)

theorem diffM_Dm (z : ℂ) : DiffM (Dm m) z := fun i j => by
  unfold Dm
  by_cases h : i = j
  · subst h
    simp only [Matrix.diagonal_apply_eq]
    exact (Complex.ofRealCLM.differentiableAt).comp z
      (((Complex.imCLM.differentiableAt).pow m).mul_const _)
  · simp only [Matrix.diagonal_apply_ne _ h]
    exact differentiableAt_const _

theorem diffM_Hmat {z : ℂ} (hz : 0 < z.im) : DiffM (Hmat m) z := by
  have hT := diffM_frameT m hz
  exact diffM_mul (diffM_mul (diffM_conjTranspose hT) (diffM_Dm m z)) hT

/-- **Co-closedness in the Hodge frame.** -/
theorem coclosed_frame {A B : ℂ → Fin (m + 1) → ℂ} {z : ℂ} (hz : 0 < z.im)
    (hA : DiffV A z) (hB : DiffV B z)
    (hCC : dbarV (fun w => Hmat m w *ᵥ A w) z + dzV (fun w => Hmat m w *ᵥ B w) z = 0) :
    (dbarV (fun w => Dm m w *ᵥ (frameT m w *ᵥ A w)) z -
        (N1 m z)ᴴ *ᵥ (Dm m z *ᵥ (frameT m z *ᵥ A z))) +
      (dzV (fun w => Dm m w *ᵥ (frameT m w *ᵥ B w)) z -
        (N2 m z)ᴴ *ᵥ (Dm m z *ᵥ (frameT m z *ᵥ B z))) = 0 := by
  have hT := diffM_frameT m hz
  have hE := diffM_frameE m z
  have hEh := diffM_conjTranspose hE
  have hH := diffM_Hmat m hz
  have hD := diffM_Dm m z
  have hXA := diffV_mulVec hH hA
  have hXB := diffV_mulVec hH hB
  have haD := diffV_mulVec hT hA
  have hbD := diffV_mulVec hT hB
  have key : ∀ C : ℂ → Fin (m + 1) → ℂ, ∀ w : ℂ, 0 < w.im →
      (frameE m w)ᴴ *ᵥ (Hmat m w *ᵥ C w) = Dm m w *ᵥ (frameT m w *ᵥ C w) := by
    intro C w hw
    have h1 : (frameE m w)ᴴ * (frameT m w)ᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, frameT_mul_frameE m w hw, Matrix.conjTranspose_one]
    unfold Hmat
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
    rw [h1, Matrix.one_mul]
  have evA : (fun w => (frameE m w)ᴴ *ᵥ (Hmat m w *ᵥ A w)) =ᶠ[nhds z]
      fun w => Dm m w *ᵥ (frameT m w *ᵥ A w) :=
    (eventually_mem_U hz).mono fun w hw => key A w hw
  have evB : (fun w => (frameE m w)ᴴ *ᵥ (Hmat m w *ᵥ B w)) =ᶠ[nhds z]
      fun w => Dm m w *ᵥ (frameT m w *ᵥ B w) :=
    (eventually_mem_U hz).mono fun w hw => key B w hw
  have dA := dbarV_congr evA
  have dB := dzV_congr evB
  rw [dbarV_mulVec hEh hXA, dbarM_conjTranspose hE, dzM_frameE m hz,
    Matrix.conjTranspose_mul] at dA
  rw [dzV_mulVec hEh hXB, dzM_conjTranspose hE, dbarM_frameE m hz,
    Matrix.conjTranspose_mul] at dB
  have kA := key A z hz
  have kB := key B z hz
  rw [← Matrix.mulVec_mulVec, kA] at dA
  rw [← Matrix.mulVec_mulVec, kB] at dB
  have hsum : (frameE m z)ᴴ *ᵥ (dbarV (fun w => Hmat m w *ᵥ A w) z +
      dzV (fun w => Hmat m w *ᵥ B w) z) = 0 := by rw [hCC, Matrix.mulVec_zero]
  rw [Matrix.mulVec_add] at hsum
  have e1 : (frameE m z)ᴴ *ᵥ dbarV (fun w => Hmat m w *ᵥ A w) z =
      dbarV (fun w => Dm m w *ᵥ (frameT m w *ᵥ A w)) z -
        (N1 m z)ᴴ *ᵥ (Dm m z *ᵥ (frameT m z *ᵥ A z)) := by
    exact eq_sub_of_add_eq' dA
  have e2 : (frameE m z)ᴴ *ᵥ dzV (fun w => Hmat m w *ᵥ B w) z =
      dzV (fun w => Dm m w *ᵥ (frameT m w *ᵥ B w)) z -
        (N2 m z)ᴴ *ᵥ (Dm m z *ᵥ (frameT m z *ᵥ B z)) := by
    exact eq_sub_of_add_eq' dB
  rw [e1, e2] at hsum
  exact hsum

/-- The next component (zero at the end). -/
def shl (x : Fin (m + 1) → ℂ) (j : Fin (m + 1)) : ℂ :=
  if h : (j : ℕ) + 1 < m + 1 then x ⟨(j : ℕ) + 1, h⟩ else 0

/-- The previous component (zero at the start). -/
def shr (x : Fin (m + 1) → ℂ) (j : Fin (m + 1)) : ℂ :=
  if h : 0 < (j : ℕ) then x ⟨(j : ℕ) - 1, by omega⟩ else 0

theorem N1_mulVec (z : ℂ) (x : Fin (m + 1) → ℂ) (j : Fin (m + 1)) :
    (N1 m z *ᵥ x) j = ((j : ℕ) : ℂ) / (2 * I * (z.im : ℂ)) * x j -
      ((j : ℕ) + 1 : ℂ) / (2 * I * (z.im : ℂ)) * shl m x j := by
  simp only [Matrix.mulVec, dotProduct]
  by_cases h : (j : ℕ) + 1 < m + 1
  · rw [Finset.sum_eq_add j (⟨(j : ℕ) + 1, h⟩ : Fin (m + 1))]
    · simp [N1, shl, h, Fin.ext_iff]
      ring
    · simp [Fin.ext_iff]
    · intro b _ hb
      have h1 : j ≠ b := fun e => hb.1 e.symm
      have h2 : b ≠ ⟨(j : ℕ) + 1, h⟩ := hb.2
      have h3 : ¬ ((j : ℕ) + 1 = b) := fun e => h2 (Fin.ext e.symm)
      simp [N1, h1, h3]
    · simp
    · simp
  · rw [Finset.sum_eq_single j]
    · simp [N1, shl, h]
    · intro b _ hb
      have h3 : ¬ ((j : ℕ) + 1 = b) := fun e => by have := b.2; omega
      have h1 : j ≠ b := fun e => hb e.symm
      simp [N1, h1, h3]
    · simp

theorem conj_two_I_im (z : ℂ) :
    starRingEnd ℂ (2 * I * (z.im : ℂ)) = -(2 * I * (z.im : ℂ)) := by
  rw [map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
  ring

theorem N2_mulVec (z : ℂ) (x : Fin (m + 1) → ℂ) (j : Fin (m + 1)) :
    (N2 m z *ᵥ x) j = -((m - (j : ℕ) : ℕ) : ℂ) / (2 * I * (z.im : ℂ)) * x j +
      ((m - ((j : ℕ) - 1) : ℕ) : ℂ) / (2 * I * (z.im : ℂ)) * shr m x j := by
  simp only [Matrix.mulVec, dotProduct]
  rcases j with ⟨_ | k, hk⟩
  · rw [Finset.sum_eq_single (⟨0, hk⟩ : Fin (m + 1))]
    · simp [N2, shr]
    · intro b _ hb
      have h1 : (0 : Fin (m + 1)) ≠ b := fun e => hb e.symm
      simp [N2, h1]
    · simp
  · have hk' : k < m + 1 := by omega
    rw [Finset.sum_eq_add (⟨k + 1, hk⟩ : Fin (m + 1)) (⟨k, hk'⟩ : Fin (m + 1))]
    · simp [N2, shr, Fin.ext_iff]
    · simp [Fin.ext_iff]
    · intro b _ hb
      have h1 : (⟨k + 1, hk⟩ : Fin (m + 1)) ≠ b := fun e => hb.1 e.symm
      have h3 : ¬ (k = (b : ℕ)) := fun e => hb.2 (Fin.ext (by simp only; omega))
      simp [N2, h1, h3]
    · simp
    · simp

theorem N1H_mulVec (z : ℂ) (x : Fin (m + 1) → ℂ) (j : Fin (m + 1)) :
    ((N1 m z)ᴴ *ᵥ x) j = -(((j : ℕ) : ℂ) / (2 * I * (z.im : ℂ))) * x j +
      ((j : ℕ) : ℂ) / (2 * I * (z.im : ℂ)) * shr m x j := by
  simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, star_def]
  rcases j with ⟨_ | k, hk⟩
  · rw [Finset.sum_eq_single (⟨0, hk⟩ : Fin (m + 1))]
    · simp [N1, shr]
    · intro b _ hb
      simp [N1]
    · simp
  · have hk' : k < m + 1 := by omega
    rw [Finset.sum_eq_add (⟨k + 1, hk⟩ : Fin (m + 1)) (⟨k, hk'⟩ : Fin (m + 1))]
    · simp [N1, shr, Fin.ext_iff, conj_two_I_im, div_neg, neg_mul]
      ring
    · simp [Fin.ext_iff]
    · intro b _ hb
      have h3 : ¬ ((b : ℕ) = k) := fun e => hb.2 (Fin.ext (by simp only; omega))
      simp [N1, hb.1, h3]
    · simp
    · simp

theorem N2H_mulVec (z : ℂ) (x : Fin (m + 1) → ℂ) (j : Fin (m + 1)) :
    ((N2 m z)ᴴ *ᵥ x) j = ((m - (j : ℕ) : ℕ) : ℂ) / (2 * I * (z.im : ℂ)) * x j -
      ((m - (j : ℕ) : ℕ) : ℂ) / (2 * I * (z.im : ℂ)) * shl m x j := by
  simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, star_def]
  by_cases h : (j : ℕ) + 1 < m + 1
  · rw [Finset.sum_eq_add j (⟨(j : ℕ) + 1, h⟩ : Fin (m + 1))]
    · simp [N2, shl, h, Fin.ext_iff, conj_two_I_im]
      ring
    · simp [Fin.ext_iff]
    · intro b _ hb
      have h1 : b ≠ j := hb.1
      have h3 : ¬ ((b : ℕ) = (j : ℕ) + 1) := fun e => hb.2 (Fin.ext e)
      simp [N2, h1, h3]
    · simp
    · simp
  · rw [Finset.sum_eq_single j]
    · have hjm : (j : ℕ) = m := by omega
      simp [N2, shl, hjm]
    · intro b _ hb
      have h3 : ¬ ((b : ℕ) = (j : ℕ) + 1) := fun e => by have := b.2; omega
      simp [N2, hb, h3]
    · simp

theorem dz_pow_ht (p : ℕ) (z : ℂ) :
    dz (fun w => ht w ^ p) z = (p : ℂ) * ht z ^ (p - 1) * (-I / 2) := by
  have h0 : HasFDerivAt ht ((Complex.ofRealCLM : ℝ →L[ℝ] ℂ).comp Complex.imCLM) z :=
    Complex.ofRealCLM.hasFDerivAt.comp z Complex.imCLM.hasFDerivAt
  have hd := h0.pow p
  unfold dz
  rw [hd.fderiv]
  simp [ht]
  ring

theorem cast_im_pow (m : ℕ) (c : ℝ) (w : ℂ) :
    (((w.im ^ m * c : ℝ)) : ℂ) = ht w ^ m * (c : ℂ) := by
  simp [ht]

theorem dbar_Dentry (m : ℕ) (c : ℝ) {z : ℂ} (hz : 0 < z.im) :
    dbar (fun w => (((w.im ^ m * c : ℝ)) : ℂ)) z =
      -((m : ℂ) / (2 * I * (z.im : ℂ))) * (((z.im ^ m * c : ℝ)) : ℂ) := by
  have hy : (z.im : ℂ) ≠ 0 := by exact_mod_cast hz.ne'
  simp_rw [cast_im_pow]
  have hd : DifferentiableAt ℝ (fun w : ℂ => ht w ^ m) z := (differentiable_ht z).pow m
  rw [dbar_mul hd (differentiableAt_const _), dbar_const, dbar_pow_ht]
  simp only [ht]
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · subst h0; simp
  · have : (z.im : ℂ) ^ m = (z.im : ℂ) ^ (m - 1) * z.im := by
      rw [← pow_succ]; congr 1; omega
    rw [this]
    field_simp
    ring_nf
    simp [Complex.I_sq]

theorem dz_Dentry (m : ℕ) (c : ℝ) {z : ℂ} (hz : 0 < z.im) :
    dz (fun w => (((w.im ^ m * c : ℝ)) : ℂ)) z =
      ((m : ℂ) / (2 * I * (z.im : ℂ))) * (((z.im ^ m * c : ℝ)) : ℂ) := by
  have hy : (z.im : ℂ) ≠ 0 := by exact_mod_cast hz.ne'
  simp_rw [cast_im_pow]
  have hd : DifferentiableAt ℝ (fun w : ℂ => ht w ^ m) z := (differentiable_ht z).pow m
  rw [dz_mul hd (differentiableAt_const _), dz_const, dz_pow_ht]
  simp only [ht]
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · subst h0; simp
  · have : (z.im : ℂ) ^ m = (z.im : ℂ) ^ (m - 1) * z.im := by
      rw [← pow_succ]; congr 1; omega
    rw [this]
    field_simp
    ring_nf
    simp [Complex.I_sq]

theorem Dm_mulVec (z : ℂ) (x : Fin (m + 1) → ℂ) (j : Fin (m + 1)) :
    (Dm m z *ᵥ x) j = (((z.im ^ m * kap m j : ℝ)) : ℂ) * x j := by
  simp [Dm, Matrix.mulVec_diagonal]

theorem kap_ne_zero {j : ℕ} (hj : j ≤ m) : kap m j ≠ 0 := by
  unfold kap
  have : (0 : ℝ) < (m.choose j : ℝ) := by exact_mod_cast Nat.choose_pos hj
  positivity

theorem kap_shift (k : ℕ) (hk : k + 1 ≤ m) :
    ((k + 1 : ℕ) : ℝ) * kap m k = ((m - k : ℕ) : ℝ) * kap m (k + 1) := by
  have id1 := Nat.choose_succ_right_eq m k
  have hc1 : (0 : ℝ) < (m.choose k : ℝ) := by exact_mod_cast Nat.choose_pos (by omega)
  have hc2 : (0 : ℝ) < (m.choose (k + 1) : ℝ) := by exact_mod_cast Nat.choose_pos hk
  have h2 : (k + 1) * m.choose (k + 1) = m.choose k * (m - k) := by rw [mul_comm]; exact id1
  unfold kap
  field_simp
  exact_mod_cast h2

theorem shr_Dm (z : ℂ) (x : Fin (m + 1) → ℂ) (j : Fin (m + 1)) :
    ((j : ℕ) : ℂ) * shr m (Dm m z *ᵥ x) j =
      ((((m - (j : ℕ) : ℕ) : ℂ) + 1) * (((z.im ^ m * kap m j : ℝ)) : ℂ)) * shr m x j := by
  by_cases h : 0 < (j : ℕ)
  · obtain ⟨k, hk⟩ : ∃ k, (j : ℕ) = k + 1 := ⟨(j : ℕ) - 1, by omega⟩
    have hkm : k + 1 ≤ m := by have := j.2; omega
    have e1 : (j : ℕ) - 1 = k := by omega
    have hmk : m - (j : ℕ) + 1 = m - k := by omega
    simp only [shr, h, dite_true, Dm_mulVec, e1]
    have keyR := kap_shift m k hkm
    have : ((j : ℕ) : ℂ) * (((z.im ^ m * kap m k : ℝ)) : ℂ) =
        ((((m - (j : ℕ) : ℕ) : ℂ) + 1) * (((z.im ^ m * kap m j : ℝ)) : ℂ)) := by
      have h1 : (((j : ℕ) : ℝ) * (z.im ^ m * kap m k)) =
          (((m - (j : ℕ) : ℕ) : ℝ) + 1) * (z.im ^ m * kap m j) := by
        rw [hk] at *
        have hh : ((m - (k + 1) : ℕ) : ℝ) + 1 = ((m - k : ℕ) : ℝ) := by
          exact_mod_cast hmk
        rw [hh]
        push_cast at keyR ⊢
        calc ((k : ℝ) + 1) * (z.im ^ m * kap m k) = z.im ^ m * (((k : ℝ) + 1) * kap m k) := by ring
          _ = z.im ^ m * (((m - k : ℕ) : ℝ) * kap m (k + 1)) := by rw [keyR]
          _ = _ := by ring
      exact_mod_cast h1
    rw [← mul_assoc, this]
  · have h0 : (j : ℕ) = 0 := by omega
    simp [shr, h0]

theorem shl_Dm (z : ℂ) (x : Fin (m + 1) → ℂ) (j : Fin (m + 1)) :
    ((m - (j : ℕ) : ℕ) : ℂ) * shl m (Dm m z *ᵥ x) j =
      ((((j : ℕ) : ℂ) + 1) * (((z.im ^ m * kap m j : ℝ)) : ℂ)) * shl m x j := by
  by_cases h : (j : ℕ) + 1 < m + 1
  · have hjm : (j : ℕ) + 1 ≤ m := by omega
    simp only [shl, h, dite_true, Dm_mulVec]
    have keyR := kap_shift m j hjm
    have : ((m - (j : ℕ) : ℕ) : ℂ) * (((z.im ^ m * kap m ((j : ℕ) + 1) : ℝ)) : ℂ) =
        ((((j : ℕ) : ℂ) + 1) * (((z.im ^ m * kap m j : ℝ)) : ℂ)) := by
      have h1 : (((m - (j : ℕ) : ℕ) : ℝ) * (z.im ^ m * kap m ((j : ℕ) + 1))) =
          (((j : ℕ) : ℝ) + 1) * (z.im ^ m * kap m j) := by
        push_cast at keyR
        calc ((m - (j : ℕ) : ℕ) : ℝ) * (z.im ^ m * kap m ((j : ℕ) + 1))
            = z.im ^ m * (((m - (j : ℕ) : ℕ) : ℝ) * kap m ((j : ℕ) + 1)) := by ring
          _ = z.im ^ m * (((j : ℝ) + 1) * kap m j) := by rw [← keyR]
          _ = _ := by ring
      exact_mod_cast h1
    rw [← mul_assoc, this]
  · have hjm : (j : ℕ) = m := by have := j.2; omega
    simp [shl, hjm]

theorem diff_Dentry (c : ℝ) (z : ℂ) :
    DifferentiableAt ℝ (fun w : ℂ => (((w.im ^ m * c : ℝ)) : ℂ)) z :=
  (Complex.ofRealCLM.differentiableAt).comp z
    (((Complex.imCLM.differentiableAt).pow m).mul_const _)

theorem shr_cast (x : Fin (m + 1) → ℂ) (j : Fin (m + 1)) :
    ((m - ((j : ℕ) - 1) : ℕ) : ℂ) * shr m x j = (((m - (j : ℕ) : ℕ) : ℂ) + 1) * shr m x j := by
  by_cases h : 0 < (j : ℕ)
  · have hj : (j : ℕ) ≤ m := by have := j.2; omega
    have : m - ((j : ℕ) - 1) = m - (j : ℕ) + 1 := by omega
    rw [this]; push_cast; ring
  · simp [shr, h]

/-- **The pair system in the Hodge frame.** -/
theorem pair_components {A B : ℂ → Fin (m + 1) → ℂ} {z : ℂ} (hz : 0 < z.im)
    (hA : DiffV A z) (hB : DiffV B z) (hC : dbarV A z = dzV B z)
    (hCC : dbarV (fun w => Hmat m w *ᵥ A w) z + dzV (fun w => Hmat m w *ᵥ B w) z = 0)
    (j : Fin (m + 1)) :
    (2 * I * (z.im : ℂ)) * dbar (fun w => (frameT m w *ᵥ A w) j) z =
        ((m - (j : ℕ) : ℕ) : ℂ) * (frameT m z *ᵥ A z) j -
          (((j : ℕ) : ℂ) + 1) * shl m (frameT m z *ᵥ B z) j ∧
    (2 * I * (z.im : ℂ)) * dz (fun w => (frameT m w *ᵥ B w) j) z =
        (((m - (j : ℕ) : ℕ) : ℂ) + 1) * shr m (frameT m z *ᵥ A z) j -
          ((j : ℕ) : ℂ) * (frameT m z *ᵥ B z) j := by
  have hne := two_I_im_ne_zero hz
  have hT := diffM_frameT m hz
  have haD := diffV_mulVec hT hA
  have hbD := diffV_mulVec hT hB
  have hC' := congrFun (closed_frame m hz hA hB hC) j
  have hCC' := congrFun (coclosed_frame m hz hA hB hCC) j
  simp only [Pi.add_apply, Pi.sub_apply, Pi.zero_apply] at hC' hCC'
  rw [N2_mulVec, N1_mulVec] at hC'
  rw [N1H_mulVec, N2H_mulVec] at hCC'
  have hY : (((z.im ^ m * kap m j : ℝ)) : ℂ) ≠ 0 := by
    have h1 : z.im ^ m * kap m j ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ hz.ne') (kap_ne_zero m (by have := j.2; omega))
    exact_mod_cast h1
  have e1 : dbarV (fun w => Dm m w *ᵥ (frameT m w *ᵥ A w)) z j =
      -((m : ℂ) / (2 * I * (z.im : ℂ))) * (((z.im ^ m * kap m j : ℝ)) : ℂ) *
          (frameT m z *ᵥ A z) j +
        (((z.im ^ m * kap m j : ℝ)) : ℂ) * dbar (fun w => (frameT m w *ᵥ A w) j) z := by
    show dbar (fun w => (Dm m w *ᵥ (frameT m w *ᵥ A w)) j) z = _
    simp_rw [Dm_mulVec]
    rw [dbar_mul (diff_Dentry m _ z) (haD j), dbar_Dentry m _ hz]
  have e2 : dzV (fun w => Dm m w *ᵥ (frameT m w *ᵥ B w)) z j =
      ((m : ℂ) / (2 * I * (z.im : ℂ))) * (((z.im ^ m * kap m j : ℝ)) : ℂ) *
          (frameT m z *ᵥ B z) j +
        (((z.im ^ m * kap m j : ℝ)) : ℂ) * dz (fun w => (frameT m w *ᵥ B w) j) z := by
    show dz (fun w => (Dm m w *ᵥ (frameT m w *ᵥ B w)) j) z = _
    simp_rw [Dm_mulVec]
    rw [dz_mul (diff_Dentry m _ z) (hbD j), dz_Dentry m _ hz]
  have s1 := shr_Dm m z (frameT m z *ᵥ A z) j
  have s2 := shl_Dm m z (frameT m z *ᵥ B z) j
  have s3 := shr_cast m (frameT m z *ᵥ A z) j
  rw [e1, e2] at hCC'
  rw [Dm_mulVec, Dm_mulVec] at hCC'
  have hM : (m : ℂ) = ((m - (j : ℕ) : ℕ) : ℂ) + ((j : ℕ) : ℂ) := by
    rw [← Nat.cast_add, Nat.sub_add_cancel (by have := j.2; omega)]
  set D' := 2 * I * (z.im : ℂ) with hD'
  set Y := (((z.im ^ m * kap m j : ℝ)) : ℂ) with hYdef
  set ac := dbar (fun w => (frameT m w *ᵥ A w) j) z
  set bz := dz (fun w => (frameT m w *ᵥ B w) j) z
  set aj := (frameT m z *ᵥ A z) j
  set bj := (frameT m z *ᵥ B z) j
  set sra := shr m (frameT m z *ᵥ A z) j
  set slb := shl m (frameT m z *ᵥ B z) j
  set Nj := ((m - (j : ℕ) : ℕ) : ℂ)
  set Jc := ((j : ℕ) : ℂ)
  have hCCn : ac - Nj / D' * aj - (Nj + 1) / D' * sra + bz + Jc / D' * bj +
      (Jc + 1) / D' * slb = 0 := by
    have h5 : Y * (ac - Nj / D' * aj - (Nj + 1) / D' * sra + bz + Jc / D' * bj +
        (Jc + 1) / D' * slb) = 0 := by
      linear_combination hCC' + (Y * (aj - bj) / D') * hM + (1 / D') * s1 - (1 / D') * s2
    exact (mul_eq_zero.mp h5).resolve_left hY
  have hCn : ac - Nj / D' * aj + (Nj + 1) / D' * sra - bz - Jc / D' * bj +
      (Jc + 1) / D' * slb = 0 := by
    have hC'' : ac + (-Nj / D' * aj + ((m - ((j : ℕ) - 1) : ℕ) : ℂ) / D' * sra) =
        bz + (Jc / D' * bj - (Jc + 1) / D' * slb) := hC'
    linear_combination hC'' - (1 / D') * s3
  constructor
  · field_simp at hCCn hCn ⊢
    linear_combination (1 / 2 : ℂ) * (hCCn + hCn)
  · field_simp at hCCn hCn ⊢
    linear_combination (1 / 2 : ℂ) * (hCCn - hCn)

/-- **The pair system for `0 ≤ k < m`**: the components `a_k` and `b_{k+1}` of `T A`, `T B` satisfy
`2iy ∂_z̄ a_k = (m-k) a_k - (k+1) b_{k+1} = 2iy ∂_z b_{k+1}`. -/
theorem pair_system {A B : ℂ → Fin (m + 1) → ℂ} {z : ℂ} (hz : 0 < z.im)
    (hA : DiffV A z) (hB : DiffV B z) (hC : dbarV A z = dzV B z)
    (hCC : dbarV (fun w => Hmat m w *ᵥ A w) z + dzV (fun w => Hmat m w *ᵥ B w) z = 0)
    {k : ℕ} (hk : k < m) :
    (2 * I * (z.im : ℂ)) * dbar (fun w => (frameT m w *ᵥ A w) ⟨k, by omega⟩) z =
        ((m : ℂ) - k) * (frameT m z *ᵥ A z) ⟨k, by omega⟩ -
          ((k : ℂ) + 1) * (frameT m z *ᵥ B z) ⟨k + 1, by omega⟩ ∧
    (2 * I * (z.im : ℂ)) * dz (fun w => (frameT m w *ᵥ B w) ⟨k + 1, by omega⟩) z =
        ((m : ℂ) - k) * (frameT m z *ᵥ A z) ⟨k, by omega⟩ -
          ((k : ℂ) + 1) * (frameT m z *ᵥ B z) ⟨k + 1, by omega⟩ := by
  have h1 := (pair_components m hz hA hB hC hCC ⟨k, by omega⟩).1
  have h2 := (pair_components m hz hA hB hC hCC ⟨k + 1, by omega⟩).2
  have e1 : shl m (frameT m z *ᵥ B z) ⟨k, by omega⟩ = (frameT m z *ᵥ B z) ⟨k + 1, by omega⟩ := by
    simp [shl, show k + 1 < m + 1 by omega]
  have e2 : shr m (frameT m z *ᵥ A z) ⟨k + 1, by omega⟩ = (frameT m z *ᵥ A z) ⟨k, by omega⟩ := by
    simp [shr]
  have c1 : (((m - k : ℕ)) : ℂ) = (m : ℂ) - k := by
    rw [Nat.cast_sub hk.le]
  have c2 : (((m - (k + 1) : ℕ) : ℂ)) + 1 = (m : ℂ) - k := by
    rw [Nat.cast_sub (by omega : k + 1 ≤ m)]; push_cast; ring
  refine ⟨?_, ?_⟩
  · simp only [] at h1
    rw [e1, c1] at h1
    exact h1
  · simp only [] at h2
    rw [e2, c2] at h2
    push_cast at h2 ⊢
    linear_combination h2

/-- The top component is holomorphic: `∂_z̄ a_m = 0`. -/
theorem top_holo {A B : ℂ → Fin (m + 1) → ℂ} {z : ℂ} (hz : 0 < z.im)
    (hA : DiffV A z) (hB : DiffV B z) (hC : dbarV A z = dzV B z)
    (hCC : dbarV (fun w => Hmat m w *ᵥ A w) z + dzV (fun w => Hmat m w *ᵥ B w) z = 0) :
    dbar (fun w => (frameT m w *ᵥ A w) (Fin.last m)) z = 0 := by
  have h1 := (pair_components m hz hA hB hC hCC (Fin.last m)).1
  have e : shl m (frameT m z *ᵥ B z) (Fin.last m) = 0 := by simp [shl]
  rw [e] at h1
  simp only [Fin.val_last, Nat.sub_self, Nat.cast_zero, zero_mul, mul_zero, sub_zero] at h1
  exact (mul_eq_zero.mp h1).resolve_left (two_I_im_ne_zero hz)

/-- The bottom component is antiholomorphic: `∂_z b_0 = 0`. -/
theorem bottom_antiholo {A B : ℂ → Fin (m + 1) → ℂ} {z : ℂ} (hz : 0 < z.im)
    (hA : DiffV A z) (hB : DiffV B z) (hC : dbarV A z = dzV B z)
    (hCC : dbarV (fun w => Hmat m w *ᵥ A w) z + dzV (fun w => Hmat m w *ᵥ B w) z = 0) :
    dz (fun w => (frameT m w *ᵥ B w) 0) z = 0 := by
  have h2 := (pair_components m hz hA hB hC hCC 0).2
  have e : shr m (frameT m z *ᵥ A z) 0 = 0 := by simp [shr]
  rw [e] at h2
  simp only [Fin.val_zero, Nat.cast_zero, mul_zero, zero_mul, sub_zero] at h2
  exact (mul_eq_zero.mp h2).resolve_left (two_I_im_ne_zero hz)

end Frame

end TernaryPeriodPolynomials.Argument.ESFoundations.SymFrame
