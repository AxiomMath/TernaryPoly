module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.HodgeReduce
public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.SymRepSL
public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.CutoffCalculus

@[expose] public section


/-!
# The unitary frame of the Hodge metric

Foundation file of the unconditional Eichler--Shimura route.  `frameS m z = diag (√(y^m / C(m,j))) · T(z)` is a frame of the `Sym^m`-induced Hodge
metric in monomial coordinates: `(frameS z)ᴴ (frameS z) = Hmat m z` (`frameS_gram`),
`‖S v‖² = Σ_j y^m κ_j |(T v)_j|²` (`sum_sq_norm_frameS`), and it is equivariant up to a unitary:
`frameS (γ z) · ρ(γ) = K · frameS z`, `K* K = 1` (`frameS_equiv`).

Formalized by Claude Sonnet 5.5.
-/

open Complex Matrix
open scoped MatrixGroups
open TernaryPeriodPolynomials.Argument.ESFoundations.HodgePair (U isOpen_U)
open TernaryPeriodPolynomials.Argument.ESFoundations.Partition (mob)

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ESFoundations.SymFrame

variable (m : ℕ)

theorem kap_nonneg (j : ℕ) : 0 ≤ kap m j := by
  unfold kap; positivity

/-- The unitary frame `S(z)` of the Hodge metric: `h_z(P, Q) = ⟪S Q, S P⟫`. -/
def frameS (z : ℂ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
  Matrix.diagonal (fun j : Fin (m + 1) => ((Real.sqrt (z.im ^ m * kap m j) : ℝ) : ℂ)) *
    frameT m z

theorem sqrtDiag_gram {z : ℂ} (hz : 0 < z.im) :
    (Matrix.diagonal (fun j : Fin (m + 1) => ((Real.sqrt (z.im ^ m * kap m j) : ℝ) : ℂ)))ᴴ *
      Matrix.diagonal (fun j : Fin (m + 1) => ((Real.sqrt (z.im ^ m * kap m j) : ℝ) : ℂ)) =
    Dm m z := by
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  unfold Dm
  congr 1
  funext j
  have : 0 ≤ z.im ^ m * kap m j := by
    have := kap_nonneg m j
    positivity
  simp [← Complex.ofReal_mul, Real.mul_self_sqrt this]

theorem frameS_gram {z : ℂ} (hz : 0 < z.im) : (frameS m z)ᴴ * frameS m z = Hmat m z := by
  unfold frameS Hmat
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc
    (Matrix.diagonal fun j : Fin (m + 1) => ((Real.sqrt (z.im ^ m * kap m j) : ℝ) : ℂ))ᴴ,
    sqrtDiag_gram m hz, ← Matrix.mul_assoc]

theorem sum_sq_norm_frameS {z : ℂ} (hz : 0 < z.im) (v : Fin (m + 1) → ℂ) :
    ∑ i, ‖(frameS m z *ᵥ v) i‖ ^ 2 =
      ∑ j : Fin (m + 1), z.im ^ m * kap m (j : ℕ) * ‖(frameT m z *ᵥ v) j‖ ^ 2 := by
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold frameS
  rw [← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal]
  have : 0 ≤ z.im ^ m * kap m j := by
    have := kap_nonneg m j
    positivity
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt this]

theorem frameS_equiv (γ : SL(2, ℤ)) {z : ℂ} (hz : z ∈ U) :
    ∃ K : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ, star K * K = 1 ∧
      frameS m (mob γ z) * symRep m γ = K * frameS m z := by
  set a : Fin (m + 1) → ℝ := fun j => Real.sqrt (z.im ^ m * kap m j) with ha
  set a' : Fin (m + 1) → ℝ := fun j => Real.sqrt ((mob γ z).im ^ m * kap m j) with ha'
  have hy : 0 < z.im := hz
  have hy' : 0 < (mob γ z).im := Partition.mob_mem γ z
  have hkap : ∀ j : Fin (m + 1), 0 < kap m (j : ℕ) := fun j => by
    unfold kap
    have : (0 : ℝ) < (m.choose j : ℝ) := by exact_mod_cast Nat.choose_pos (by omega)
    positivity
  have ha0 : ∀ j, 0 < a j := fun j => Real.sqrt_pos.mpr (mul_pos (pow_pos hy _) (hkap j))
  set dd : Fin (m + 1) → ℂ := fun j => ((a' j / a j : ℝ) : ℂ) *
    (Global.den γ z ^ (j : ℕ) * (starRingEnd ℂ (Global.den γ z)) ^ (m - (j : ℕ))) with hdd
  have hDen : Global.den γ z ≠ 0 := Partition.denom_ne_zero' γ hz
  have himr : (mob γ z).im = z.im / ‖Global.den γ z‖ ^ 2 := by
    have h := Global.ht_mob γ hz
    have h2 : starRingEnd ℂ (Global.den γ z) * Global.den γ z = (‖Global.den γ z‖ ^ 2 : ℝ) := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    unfold HodgePair.ht at h
    rw [mul_comm, h2] at h
    have hn : ((‖Global.den γ z‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
      have : ‖Global.den γ z‖ ≠ 0 := norm_ne_zero_iff.mpr hDen
      exact_mod_cast pow_ne_zero 2 this
    exact_mod_cast (by rw [h]; push_cast; ring : (((mob γ z).im : ℝ) : ℂ) =
      ((z.im / ‖Global.den γ z‖ ^ 2 : ℝ) : ℂ))
  refine ⟨Matrix.diagonal dd, ?_, ?_⟩
  · rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, Pi.star_apply]
      have hpos : 0 < a' i / a i :=
        div_pos (Real.sqrt_pos.mpr (mul_pos (pow_pos hy' _) (hkap i))) (ha0 i)
      have hnorm : ‖dd i‖ = a' i / a i * ‖Global.den γ z‖ ^ m := by
        simp only [hdd, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.norm_conj,
          ]
        rw [← pow_add]
        have : (i : ℕ) + (m - (i : ℕ)) = m := by have := i.2; omega
        rw [this, abs_of_pos hpos]
      have hratio : (a' i / a i) ^ 2 = (‖Global.den γ z‖ ^ 2)⁻¹ ^ m := by
        rw [div_pow, ha, ha', Real.sq_sqrt (mul_nonneg (pow_nonneg hy'.le _) (hkap i).le),
          Real.sq_sqrt (mul_nonneg (pow_nonneg hy.le _) (hkap i).le), himr]
        have hk := hkap i
        have hnn : ‖Global.den γ z‖ ≠ 0 := norm_ne_zero_iff.mpr hDen
        field_simp
        rw [div_eq_mul_one_div, mul_pow]
      have h1 : ‖dd i‖ ^ 2 = 1 := by
        rw [hnorm, mul_pow, hratio, ← pow_mul, ← inv_pow, ← pow_mul]
        have hnn : ‖Global.den γ z‖ ≠ 0 := norm_ne_zero_iff.mpr hDen
        have e : (‖Global.den γ z‖⁻¹) ^ (2 * m) * ‖Global.den γ z‖ ^ (m * 2) = 1 := by
          rw [mul_comm m 2, ← mul_pow, inv_mul_cancel₀ hnn, one_pow]
        convert e using 3
      rw [Complex.star_def, Complex.conj_mul']
      exact_mod_cast h1
    · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
  · unfold frameS
    rw [Matrix.mul_assoc, frameT_mul_symRep m γ hz, ← Matrix.mul_assoc, autoDiag,
      Matrix.diagonal_mul_diagonal, ← Matrix.mul_assoc (Matrix.diagonal dd),
      Matrix.diagonal_mul_diagonal]
    congr 2
    funext j
    have key : ((a' j / a j : ℝ) : ℂ) * (a j : ℂ) = (a' j : ℂ) := by
      rw [← Complex.ofReal_mul, div_mul_cancel₀ _ (ha0 j).ne']
    show (a' j : ℂ) * _ = _
    simp only [hdd, Global.conj_den]
    rw [← key]
    simp only [Global.den]
    ring

end TernaryPeriodPolynomials.Argument.ESFoundations.SymFrame
