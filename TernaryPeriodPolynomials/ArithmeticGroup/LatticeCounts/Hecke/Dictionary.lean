module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Lattice.Operator
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Hecke.MatrixIdentity

@[expose] public section


/-!
# Normalization dictionary for `eq:lattice-hecke` at finite coordinate one (step (b))

Formalized by Claude Haiku 5.5.

`Fh k h g = (det g)^{k/2} (c i + d)^{-k} h(g i)` on `GL₂(ℝ)` with `det g > 0`.
Results (no hypothesis on `h` unless stated):

* `Fh_upper`: for a Hermite triple `U = [[a,b],[0,d]]`, `Fh (U g) = (a d)^{k/2} d^{-k} Nf g h(U g i)`.
* `sum_Fh_upper`: `∑_{t ∈ hnfData m} Fh (U_t g) = m^{1-k/2} Nf g · latticeOp k m h (g i)`.
* `Fh_smul_pos`: positive scalar matrices do not change `Fh`.
* `Fh_S_mul` (the only hypothesis on `h`): if `h (S z) = z^k h z` (weight-`k` invariance under
  `S = [[0,-1],[1,0]]`), then `Fh (S X) = Fh X`.
* `sum_Fh_lower`: paper form `∑_t Fh (L_t⁻¹ g)` with `L_t = [[a,0],[b,d]]`, equal to
  `m^{1-k/2} Nf (S⁻¹ g) · latticeOp k m h (S⁻¹ g i)`, using `Fh_S_mul` once.
-/

open Matrix UpperHalfPlane
open TernaryPeriodPolynomials.Argument.LatticeCounts.LatticeOperator

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.HeckeDictionary

/-- `(det g)^{k/2} (c i + d)^{-k}` on `GL₂(ℝ)`, the finite part of `F_h`. -/
def Nf (k : ℤ) (g : GL (Fin 2) ℝ) : ℂ :=
  (((Matrix.GeneralLinearGroup.det g).val : ℝ) : ℂ) ^ ((k : ℂ) / 2) *
    UpperHalfPlane.denom g Complex.I ^ (-k)

/-- `F_h(g) = (det g)^{k/2} (c i + d)^{-k} h(g i)`. -/
def Fh (k : ℤ) (h : UpperHalfPlane → ℂ) (g : GL (Fin 2) ℝ) : ℂ :=
  Nf k g * h (g • UpperHalfPlane.I)

/-- The upper Hermite matrix of a triple, as a `GL₂(ℝ)` element (triples in `hnfData` have
nonzero determinant). -/
theorem hnfMat_det_ne_zero {t : ℕ × ℕ × ℕ} (ht : 0 < t.1 ∧ 0 < t.2.2) :
    (hnfMat t).det ≠ 0 := by
  rw [hnfMat_det]
  have h1 : (0 : ℝ) < (t.1 : ℝ) := by exact_mod_cast ht.1
  have h2 : (0 : ℝ) < (t.2.2 : ℝ) := by exact_mod_cast ht.2
  exact (mul_pos h1 h2).ne'

theorem denom_mul_upper (t : ℕ × ℕ × ℕ) (hM : (hnfMat t).det ≠ 0) (g : GL (Fin 2) ℝ) (z : ℂ) :
    UpperHalfPlane.denom (GeneralLinearGroup.mkOfDetNeZero (hnfMat t) hM * g) z =
      (t.2.2 : ℂ) * UpperHalfPlane.denom g z := by
  simp [UpperHalfPlane.denom, hnfMat, Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem det_mul_upper (t : ℕ × ℕ × ℕ) (hM : (hnfMat t).det ≠ 0) (g : GL (Fin 2) ℝ) :
    (Matrix.GeneralLinearGroup.det (GeneralLinearGroup.mkOfDetNeZero (hnfMat t) hM * g)).val =
      ((t.1 : ℝ) * (t.2.2 : ℝ)) * (Matrix.GeneralLinearGroup.det g).val := by
  simp [hnfMat_det]

/-- The upper Hermite matrix `U_t` acts on `g`: `F_h(U_t g)` in terms of `h(U_t (g i))`. -/
theorem Fh_upper (k : ℤ) (h : UpperHalfPlane → ℂ) (t : ℕ × ℕ × ℕ) (ht : 0 < t.1 ∧ 0 < t.2.2)
    (g : GL (Fin 2) ℝ) (hg : 0 < (Matrix.GeneralLinearGroup.det g).val) :
    Fh k h (GeneralLinearGroup.mkOfDetNeZero (hnfMat t) (hnfMat_det_ne_zero ht) * g) =
      (((t.1 * t.2.2 : ℕ) : ℂ) ^ ((k : ℂ) / 2)) * ((t.2.2 : ℕ) : ℂ) ^ (-k) *
        Nf k g * h (hnfAct t (g • UpperHalfPlane.I)) := by
  have hM := hnfMat_det_ne_zero ht
  unfold Fh Nf
  rw [hnfAct_eq_of_det hM, mul_smul, det_mul_upper, denom_mul_upper]
  have hdet : (0 : ℝ) ≤ (t.1 : ℝ) * (t.2.2 : ℝ) := by positivity
  have hg' : (0 : ℝ) ≤ (Matrix.GeneralLinearGroup.det g).val := hg.le
  have e1 : ((((t.1 : ℝ) * (t.2.2 : ℝ)) * (Matrix.GeneralLinearGroup.det g).val : ℝ) : ℂ) ^
      ((k : ℂ) / 2) = ((((t.1 * t.2.2 : ℕ)) : ℂ)) ^ ((k : ℂ) / 2) *
        (((Matrix.GeneralLinearGroup.det g).val : ℝ) : ℂ) ^ ((k : ℂ) / 2) := by
    have := Complex.mul_cpow_ofReal_nonneg hdet hg' ((k : ℂ) / 2)
    push_cast at this ⊢
    exact this
  rw [e1, mul_zpow]
  push_cast
  ring

/-- `U_t g` as a `GL₂(ℝ)` element, with the convention `Uel t g = g` when `det U_t = 0`
(never used on `hnfData` triples). -/
def Uel (t : ℕ × ℕ × ℕ) (g : GL (Fin 2) ℝ) : GL (Fin 2) ℝ :=
  if hM : (hnfMat t).det ≠ 0 then GeneralLinearGroup.mkOfDetNeZero (hnfMat t) hM * g else g

theorem Uel_eq {t : ℕ × ℕ × ℕ} (ht : 0 < t.1 ∧ 0 < t.2.2) (g : GL (Fin 2) ℝ) :
    Uel t g = GeneralLinearGroup.mkOfDetNeZero (hnfMat t) (hnfMat_det_ne_zero ht) * g := by
  unfold Uel
  rw [dite_eq_left (hnfMat_det_ne_zero ht)]

/-- Splitting `m^{k/2} = m^{1-k/2} · m^{k-1}` for `m > 0`. -/
theorem cpow_half_split {m : ℕ} (hm : 0 < m) (k : ℤ) :
    (m : ℂ) ^ ((k : ℂ) / 2) = (m : ℂ) ^ (1 - (k : ℂ) / 2) * (m : ℂ) ^ (k - 1) := by
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [← Complex.cpow_intCast, ← Complex.cpow_add _ _ hm0]
  congr 1
  push_cast
  ring

/-- The per-term identity: `F_h(U_t g) = m^{1-k/2} · (weight_t · Nf g · h(U_t (g i)))`, `m = a d`. -/
theorem term_upper (k : ℤ) (h : UpperHalfPlane → ℂ) {m : ℕ} (hm : 0 < m) (t : ℕ × ℕ × ℕ)
    (ht : 0 < t.1 ∧ 0 < t.2.2) (hmt : t.1 * t.2.2 = m) (g : GL (Fin 2) ℝ)
    (hg : 0 < (Matrix.GeneralLinearGroup.det g).val) :
    Fh k h (Uel t g) =
      (m : ℂ) ^ (1 - (k : ℂ) / 2) * (Nf k g * (hnfWeight k t * h (hnfAct t (g • UpperHalfPlane.I)))) := by
  rw [Uel_eq ht, Fh_upper k h t ht g hg]
  unfold hnfWeight
  rw [hmt, cpow_half_split hm k]
  ring

/-- Finite coordinate one, upper form: `∑_{t ∈ hnfData m} F_h(U_t g) = m^{1-k/2} Nf g · T_m h (g i)`.
No hypothesis on `h`. -/
theorem sum_Fh_upper (k : ℤ) (h : UpperHalfPlane → ℂ) {m : ℕ} (hm : 0 < m)
    (g : GL (Fin 2) ℝ) (hg : 0 < (Matrix.GeneralLinearGroup.det g).val) :
    ∑ t ∈ hnfData m, Fh k h (Uel t g) =
      (m : ℂ) ^ (1 - (k : ℂ) / 2) * (Nf k g * latticeOp k m h (g • UpperHalfPlane.I)) := by
  unfold latticeOp
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [mem_hnfData hm] at ht
  obtain ⟨h1, h2, _⟩ := ht
  have hpos : 0 < t.2.2 := by
    rcases Nat.eq_zero_or_pos t.2.2 with h0 | h0
    · rw [h0, mul_zero] at h2
      exact absurd h2.symm hm.ne'
    · exact h0
  exact term_upper k h hm t ⟨h1, hpos⟩ h2 g hg

/-- Coercion of `Denom` at `i`: the denominator of `X` at `i` is nonzero. -/
theorem denom_I_ne (X : GL (Fin 2) ℝ) : UpperHalfPlane.denom X Complex.I ≠ 0 := by
  have := UpperHalfPlane.denom_ne_zero X UpperHalfPlane.I
  rwa [UpperHalfPlane.coe_I] at this

/-- The matrix `S = [[0,-1],[1,0]]` in `GL₂(ℝ)`. -/
def Sgl : GL (Fin 2) ℝ :=
  GeneralLinearGroup.mkOfDetNeZero !![(0 : ℝ), -1; 1, 0] (by norm_num [Matrix.det_fin_two])

theorem Sgl_coe : (Sgl : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; 1, 0] := rfl

theorem Sgl_det : (Matrix.GeneralLinearGroup.det Sgl).val = 1 := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, Sgl_coe, Matrix.det_fin_two_of]
  norm_num

/-- Left `S`-invariance of `F_h`, under the weight-`k` invariance hypothesis on `h`. -/
theorem Fh_S_mul (k : ℤ) (h : UpperHalfPlane → ℂ)
    (hS : ∀ z : UpperHalfPlane, h (Sgl • z) = (z : ℂ) ^ k * h z)
    (X : GL (Fin 2) ℝ) (hX : 0 < (Matrix.GeneralLinearGroup.det X).val) :
    Fh k h (Sgl * X) = Fh k h X := by
  unfold Fh Nf
  have hdet : (Matrix.GeneralLinearGroup.det (Sgl * X)).val =
      (Matrix.GeneralLinearGroup.det X).val := by
    rw [map_mul, Units.val_mul, Sgl_det, one_mul]
  have hden : UpperHalfPlane.denom (Sgl * X) Complex.I =
      ((X • UpperHalfPlane.I : UpperHalfPlane) : ℂ) * UpperHalfPlane.denom X Complex.I := by
    rw [UpperHalfPlane.coe_smul_of_det_pos hX UpperHalfPlane.I, UpperHalfPlane.coe_I,
      div_mul_cancel₀ _ (denom_I_ne X)]
    simp [UpperHalfPlane.denom, UpperHalfPlane.num, Sgl_coe, Units.val_mul, Matrix.mul_apply,
      Fin.sum_univ_two]
  have hS' := hS (X • UpperHalfPlane.I)
  rw [mul_smul, hS', hdet, hden, mul_zpow]
  have hw : ((X • UpperHalfPlane.I : UpperHalfPlane) : ℂ) ≠ 0 := UpperHalfPlane.ne_zero _
  have hw1 : ((X • UpperHalfPlane.I : UpperHalfPlane) : ℂ) ^ (-k) *
      ((X • UpperHalfPlane.I : UpperHalfPlane) : ℂ) ^ k = 1 := by
    rw [← zpow_add₀ hw]
    simp
  linear_combination (((Matrix.GeneralLinearGroup.det X).val : ℝ) : ℂ) ^ ((k : ℂ) / 2) *
    UpperHalfPlane.denom X Complex.I ^ (-k) * h (X • UpperHalfPlane.I) * hw1

/-- Positive scalar matrices do not change `F_h`. -/
theorem Fh_scalar_pos (k : ℤ) (h : UpperHalfPlane → ℂ) (u : ℝ) (hu : 0 < u)
    (X : GL (Fin 2) ℝ) (hX : 0 < (Matrix.GeneralLinearGroup.det X).val) :
    Fh k h (GeneralLinearGroup.scalar (Fin 2) (Units.mk0 u hu.ne') * X) = Fh k h X := by
  unfold Fh Nf
  have hu0 : (u : ℂ) ≠ 0 := by exact_mod_cast hu.ne'
  have hdet : (Matrix.GeneralLinearGroup.det
      (GeneralLinearGroup.scalar (Fin 2) (Units.mk0 u hu.ne') * X)).val =
      u ^ 2 * (Matrix.GeneralLinearGroup.det X).val := by
    simp [map_mul, Units.val_mul, Matrix.GeneralLinearGroup.det_scalar, sq]
  have hsm : (GeneralLinearGroup.scalar (Fin 2) (Units.mk0 u hu.ne') * X) • UpperHalfPlane.I =
      X • UpperHalfPlane.I := by
    rw [mul_smul, UpperHalfPlane.glScalar_smul]
  have hden : UpperHalfPlane.denom (GeneralLinearGroup.scalar (Fin 2) (Units.mk0 u hu.ne') * X)
      Complex.I = (u : ℂ) * UpperHalfPlane.denom X Complex.I := by
    simp [UpperHalfPlane.denom, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, Matrix.diagonal_mul]
    ring
  have key1 : (((u ^ 2 * (Matrix.GeneralLinearGroup.det X).val : ℝ)) : ℂ) ^ ((k : ℂ) / 2) =
      (u : ℂ) ^ k * (((Matrix.GeneralLinearGroup.det X).val : ℝ) : ℂ) ^ ((k : ℂ) / 2) := by
    rw [show ((u ^ 2 * (Matrix.GeneralLinearGroup.det X).val : ℝ) : ℂ) =
      (((u * u : ℝ)) : ℂ) * (((Matrix.GeneralLinearGroup.det X).val : ℝ) : ℂ) by push_cast; ring]
    rw [Complex.mul_cpow_ofReal_nonneg (mul_self_nonneg u) hX.le]
    rw [show ((u * u : ℝ) : ℂ) = (u : ℂ) * (u : ℂ) by push_cast; ring]
    rw [Complex.mul_cpow_ofReal_nonneg hu.le hu.le]
    rw [← Complex.cpow_add _ _ hu0, ← Complex.cpow_intCast,
      show (k : ℂ) / 2 + (k : ℂ) / 2 = (k : ℂ) by ring]
  have hu1 : (u : ℂ) ^ k * (u : ℂ) ^ (-k) = 1 := by
    rw [← zpow_add₀ hu0]
    simp
  rw [hsm, hden, hdet, key1, mul_zpow]
  linear_combination (((Matrix.GeneralLinearGroup.det X).val : ℝ) : ℂ) ^ ((k : ℂ) / 2) *
    UpperHalfPlane.denom X Complex.I ^ (-k) * h (X • UpperHalfPlane.I) * hu1

/-- The lower-triangular Hermite matrix `A_t = [[a,0],[b,d]] = (U_t)ᵀ`. -/
def lowMat (t : ℕ × ℕ × ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(t.1 : ℝ), 0; (t.2.1 : ℝ), (t.2.2 : ℝ)]

theorem lowMat_transpose (t : ℕ × ℕ × ℕ) : (lowMat t)ᵀ = hnfMat t := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lowMat, hnfMat]

theorem lowMat_det (t : ℕ × ℕ × ℕ) : (lowMat t).det = (t.1 : ℝ) * (t.2.2 : ℝ) := by
  simp [lowMat, Matrix.det_fin_two]

theorem lowMat_det_ne_zero {t : ℕ × ℕ × ℕ} (ht : 0 < t.1 ∧ 0 < t.2.2) :
    (lowMat t).det ≠ 0 := by
  rw [lowMat_det]
  exact (mul_pos (by exact_mod_cast ht.1) (by exact_mod_cast ht.2)).ne'

theorem m_ne_zero {t : ℕ × ℕ × ℕ} (ht : 0 < t.1 ∧ 0 < t.2.2) :
    (t.1 : ℝ) * (t.2.2 : ℝ) ≠ 0 := by
  rw [← lowMat_det]
  exact lowMat_det_ne_zero ht

/-- `m A⁻¹ = S Aᵀ S⁻¹` for `A = [[a,0],[b,d]]`, `m = a d` (the `HeckeMatrixIdentity`), in matrix form. -/
theorem lower_matrix_eq {t : ℕ × ℕ × ℕ} (ht : 0 < t.1 ∧ 0 < t.2.2)
    (G : Matrix (Fin 2) (Fin 2) ℝ) :
    (lowMat t)⁻¹ * G =
      Matrix.scalar (Fin 2) ((t.1 : ℝ) * (t.2.2 : ℝ))⁻¹ *
        (!![(0 : ℝ), -1; 1, 0] * (hnfMat t * (!![(0 : ℝ), -1; 1, 0]⁻¹ * G))) := by
  have ha : (t.1 : ℝ) ≠ 0 := by exact_mod_cast ht.1.ne'
  have hd : (t.2.2 : ℝ) ≠ 0 := by exact_mod_cast ht.2.ne'
  have hm0 : (t.1 : ℝ) * (t.2.2 : ℝ) ≠ 0 := mul_ne_zero ha hd
  have key : ((t.1 : ℝ) * (t.2.2 : ℝ)) • (lowMat t)⁻¹ =
      !![(0 : ℝ), -1; 1, 0] * hnfMat t * !![(0 : ℝ), -1; 1, 0]⁻¹ := by
    rw [← lowMat_transpose]
    exact TernaryPeriodPolynomials.Argument.LatticeCounts.HeckeMatrix.smul_inv_eq_conj_transpose
      (K := ℝ) _ _ _ ha hd
  have hinv : (lowMat t)⁻¹ = ((t.1 : ℝ) * (t.2.2 : ℝ))⁻¹ •
      (!![(0 : ℝ), -1; 1, 0] * hnfMat t * !![(0 : ℝ), -1; 1, 0]⁻¹) := by
    rw [← key, smul_smul, inv_mul_cancel₀ hm0, one_smul]
  rw [hinv, Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul]
  simp only [Matrix.mul_assoc]

/-- The lower-triangular Hermite matrix inverse as a `GL₂(ℝ)` element (paper `L_t⁻¹`). -/
def Gl (t : ℕ × ℕ × ℕ) (g : GL (Fin 2) ℝ) : GL (Fin 2) ℝ :=
  if hL : (lowMat t).det ≠ 0 then (GeneralLinearGroup.mkOfDetNeZero (lowMat t) hL)⁻¹ * g else g

theorem Gl_eq {t : ℕ × ℕ × ℕ} (ht : 0 < t.1 ∧ 0 < t.2.2) (g : GL (Fin 2) ℝ) :
    Gl t g = (GeneralLinearGroup.mkOfDetNeZero (lowMat t) (lowMat_det_ne_zero ht))⁻¹ * g := by
  unfold Gl
  rw [dite_eq_left (lowMat_det_ne_zero ht)]

/-- `L_t⁻¹ g = m⁻¹ · S (U_t (S⁻¹ g))` in `GL₂(ℝ)`, from `m A⁻¹ = S Aᵀ S⁻¹`. -/
theorem inv_lower_eq {t : ℕ × ℕ × ℕ} (ht : 0 < t.1 ∧ 0 < t.2.2) (g : GL (Fin 2) ℝ) :
    (GeneralLinearGroup.mkOfDetNeZero (lowMat t) (lowMat_det_ne_zero ht))⁻¹ * g =
      GeneralLinearGroup.scalar (Fin 2) (Units.mk0 ((t.1 : ℝ) * (t.2.2 : ℝ))⁻¹
          (inv_ne_zero (m_ne_zero ht))) *
        (Sgl * (GeneralLinearGroup.mkOfDetNeZero (hnfMat t) (hnfMat_det_ne_zero ht) *
          (Sgl⁻¹ * g))) := by
  apply Units.ext
  simp only [Units.val_mul, Matrix.coe_units_inv, Matrix.GeneralLinearGroup.coe_scalar,
    Units.val_mk0, Sgl_coe]
  exact lower_matrix_eq ht _

/-- Finite coordinate one, paper form: the lower-triangular sum
`∑_{t ∈ hnfData m} F_h(L_t⁻¹ g)` equals `m^{1-k/2} Nf(S⁻¹ g) T_m h(S⁻¹ g i)`.
The only hypothesis on `h` is the weight-`k` `S`-invariance `hS`, used once. -/
theorem sum_Fh_lower (k : ℤ) (h : UpperHalfPlane → ℂ)
    (hS : ∀ z : UpperHalfPlane, h (Sgl • z) = (z : ℂ) ^ k * h z)
    {m : ℕ} (hm : 0 < m) (g : GL (Fin 2) ℝ) (hg : 0 < (Matrix.GeneralLinearGroup.det g).val) :
    ∑ t ∈ hnfData m, Fh k h (Gl t g) =
      (m : ℂ) ^ (1 - (k : ℂ) / 2) *
        (Nf k (Sgl⁻¹ * g) * latticeOp k m h ((Sgl⁻¹ * g) • UpperHalfPlane.I)) := by
  have hSinv : (Matrix.GeneralLinearGroup.det (Sgl⁻¹)).val = 1 := by
    rw [map_inv, Units.val_inv_eq_inv_val, Sgl_det, inv_one]
  have hg' : 0 < (Matrix.GeneralLinearGroup.det (Sgl⁻¹ * g)).val := by
    rw [map_mul, Units.val_mul, hSinv, one_mul]
    exact hg
  unfold latticeOp
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [mem_hnfData hm] at ht
  obtain ⟨h1, h2, _⟩ := ht
  have hpos : 0 < t.2.2 := by
    rcases Nat.eq_zero_or_pos t.2.2 with h0 | h0
    · rw [h0, mul_zero] at h2
      exact absurd h2.symm hm.ne'
    · exact h0
  have hmpos : (0 : ℝ) < (t.1 : ℝ) * (t.2.2 : ℝ) :=
    mul_pos (by exact_mod_cast h1) (by exact_mod_cast hpos)
  have hU : 0 < (Matrix.GeneralLinearGroup.det (Uel t (Sgl⁻¹ * g))).val := by
    rw [Uel_eq ⟨h1, hpos⟩, det_mul_upper]
    exact mul_pos hmpos hg'
  have hX : 0 < (Matrix.GeneralLinearGroup.det (Sgl * Uel t (Sgl⁻¹ * g))).val := by
    rw [map_mul, Units.val_mul, Sgl_det, one_mul]
    exact hU
  rw [Gl_eq ⟨h1, hpos⟩ g, inv_lower_eq ⟨h1, hpos⟩ g, ← Uel_eq ⟨h1, hpos⟩,
    Fh_scalar_pos k h _ (inv_pos.mpr hmpos) _ hX, Fh_S_mul k h hS _ hU]
  exact term_upper k h hm t ⟨h1, hpos⟩ h2 (Sgl⁻¹ * g) hg'

end TernaryPeriodPolynomials.Argument.LatticeCounts.HeckeDictionary
