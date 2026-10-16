module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.IntegralLift
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.SeedK0

@[expose] public section


/-!
# Group-level factorisation of `ι_v(L(s,t))` (part 3a)

For `z = (s,t) ∈ ℚ_p²` put `L(z) = Lst s t ∈ GL₃(ℚ_p)` with explicit inverse, and transport it to the
finite place `v` through `ψ_v = (finiteCompletionPadicEquiv v).symm`. If `max(‖s‖,‖t‖) = p^r`, the
k₀ lemma gives `k ∈ SL₃(ℤ_p)` with `P = L k` in the plane parabolic. Hence
`L = P · k⁻¹` and `ι_v(L) = ι_v(P) · ι_v(k⁻¹)`, and `ι_v(k⁻¹)` lifts to `GL₃(𝔸_f^∞)` by
`ιGL3_mem_integral_of_norm`.

Formalized by Claude Haiku 5.5.
-/

open PadicInt Matrix
open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalGL3
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellIntegralLift
open TernaryPeriodPolynomials.Argument.LatticeCounts.SeedK0
  (Lst toQ K0Spec exists_k0)
open TernaryPeriodPolynomials.SphericalDetection.Helpers (finiteCompletionPadicEquiv)

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitGL

section Group

variable {p : ℕ} [Fact p.Prime]

/-- Inverse of `Lst s t`: `[[-s,-t,1],[1,0,0],[0,1,0]]`. -/
def LstInv (s t : ℚ_[p]) : Matrix (Fin 3) (Fin 3) ℚ_[p] :=
  !![-s, -t, 1; 1, 0, 0; 0, 1, 0]

theorem Lst_mul_LstInv (s t : ℚ_[p]) : Lst s t * LstInv s t = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Lst, LstInv, Matrix.mul_apply, Fin.sum_univ_three]

theorem LstInv_mul_Lst (s t : ℚ_[p]) : LstInv s t * Lst s t = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Lst, LstInv, Matrix.mul_apply, Fin.sum_univ_three]

/-- `L(s,t)` as an element of `GL₃(ℚ_p)`. -/
def LstGL (s t : ℚ_[p]) : GeneralLinearGroup (Fin 3) ℚ_[p] :=
  ⟨Lst s t, LstInv s t, Lst_mul_LstInv s t, LstInv_mul_Lst s t⟩

theorem LstGL_val (s t : ℚ_[p]) : (LstGL s t).val = Lst s t := rfl

/-- Reduction of an integral matrix to `ℚ_p`. -/
theorem toQ_mul (A B : Matrix (Fin 3) (Fin 3) ℤ_[p]) : toQ (A * B) = toQ A * toQ B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toQ, Matrix.mul_apply, Fin.sum_univ_three]

theorem toQ_one : toQ (1 : Matrix (Fin 3) (Fin 3) ℤ_[p]) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toQ]

/-- For `k ∈ SL₃(ℤ_p)`, the rational matrix `toQ k` as an element of `GL₃(ℚ_p)`, with inverse
`toQ (adjugate k)`. -/
def kGL (k : Matrix (Fin 3) (Fin 3) ℤ_[p]) (hk : k.det = 1) : GeneralLinearGroup (Fin 3) ℚ_[p] :=
  ⟨toQ k, toQ k.adjugate, by
    rw [← toQ_mul, Matrix.mul_adjugate, hk, one_smul, toQ_one],
    by
    rw [← toQ_mul, Matrix.adjugate_mul, hk, one_smul, toQ_one]⟩

/-- The inverse of `kGL k hk`, as a group element: `toQ (adjugate k)`. -/
def kInvGL (k : Matrix (Fin 3) (Fin 3) ℤ_[p]) (hk : k.det = 1) :
    GeneralLinearGroup (Fin 3) ℚ_[p] :=
  ⟨toQ k.adjugate, toQ k, by
    rw [← toQ_mul, Matrix.adjugate_mul, hk, one_smul, toQ_one],
    by
    rw [← toQ_mul, Matrix.mul_adjugate, hk, one_smul, toQ_one]⟩

theorem kGL_inv_eq (k : Matrix (Fin 3) (Fin 3) ℤ_[p]) (hk : k.det = 1) :
    (kGL k hk)⁻¹ = kInvGL k hk := by
  apply inv_eq_of_mul_eq_one_right
  apply Units.ext
  show toQ k * toQ k.adjugate = 1
  rw [← toQ_mul, Matrix.mul_adjugate, hk, one_smul, toQ_one]

/-- The plane element `P = L(s,t) · k` over `ℚ_p`. -/
def PGL (s t : ℚ_[p]) (k : Matrix (Fin 3) (Fin 3) ℤ_[p]) (hk : k.det = 1) :
    GeneralLinearGroup (Fin 3) ℚ_[p] :=
  LstGL s t * kGL k hk

/-- **Factorisation over `ℚ_p`.** `L(s,t) = (L(s,t) · k) · k⁻¹`. -/
theorem LstGL_eq_PGL_mul_inv (s t : ℚ_[p]) (k : Matrix (Fin 3) (Fin 3) ℤ_[p]) (hk : k.det = 1) :
    LstGL s t = PGL s t k hk * kInvGL k hk := by
  rw [← kGL_inv_eq, PGL, mul_inv_cancel_right]

end Group

section Place

variable (v : FinitePlace) [Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime]

/-- The local isomorphism `ψ_v : ℚ_p → K_v` (inverse of `finiteCompletionPadicEquiv v`). -/
def psiV : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val] →+* v.adicCompletion ℚ :=
  (finiteCompletionPadicEquiv v).symm.toRingHom

theorem finiteCompletionPadicEquiv_psiV (x : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val]) :
    finiteCompletionPadicEquiv v (psiV v x) = x :=
  (finiteCompletionPadicEquiv v).apply_symm_apply x

/-- The element `L(z) ∈ GL₃(K_v)` for `z = (s,t)`. -/
def LstV (z : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val] × ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val]) :
    GeneralLinearGroup (Fin 3) (v.adicCompletion ℚ) :=
  GeneralLinearGroup.map (psiV v) (LstGL z.1 z.2)

/-- `P(z,k) = L(z) · k` in `GL₃(K_v)`. -/
def PV (z : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val] × ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val])
    (k : Matrix (Fin 3) (Fin 3) ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).val]) (hk : k.det = 1) :
    GeneralLinearGroup (Fin 3) (v.adicCompletion ℚ) :=
  GeneralLinearGroup.map (psiV v) (PGL z.1 z.2 k hk)

/-- The lift of `ι_v(k⁻¹)`: the inverse `kInvGL` transported to `K_v`, with its entries integral. -/
theorem kInv_lift (k : Matrix (Fin 3) (Fin 3) ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).val])
    (hk : k.det = 1) :
    ∃ kI : GeneralLinearGroup (Fin 3) IntegralAdeles,
      GeneralLinearGroup.map integralEmbedding kI =
        ιGL3 v (GeneralLinearGroup.map (psiV v) (kInvGL k hk)) := by
  have hinv : (GeneralLinearGroup.map (psiV v) (kInvGL k hk))⁻¹ =
      GeneralLinearGroup.map (psiV v) (kGL k hk) := by
    rw [← map_inv, ← kGL_inv_eq, inv_inv]
  apply ιGL3_mem_integral_of_norm
  · intro i j
    show ‖finiteCompletionPadicEquiv v (psiV v ((k.adjugate i j : ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).val]) : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val]))‖ ≤ 1
    rw [finiteCompletionPadicEquiv_psiV]
    exact PadicInt.norm_le_one _
  · intro i j
    rw [hinv]
    show ‖finiteCompletionPadicEquiv v (psiV v ((k i j : ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).val]) : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val]))‖ ≤ 1
    rw [finiteCompletionPadicEquiv_psiV]
    exact PadicInt.norm_le_one _

/-- **Factorisation at `v`.** For `z` with `max(‖s‖,‖t‖) = p^r`, there is `k ∈ SL₃(ℤ_p)` with
`ι_v(L(z)) = ι_v(P(z,k)) · ι_v(k⁻¹)`, and `ι_v(k⁻¹)` is the image of a `GL₃(𝔸_f^∞)` element. -/
theorem iotaLstV_factor {r : ℕ} (z : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val] ×
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val])
    (hz : max ‖z.1‖ ‖z.2‖ = ((Rat.HeightOneSpectrum.primesEquiv v).val : ℝ) ^ r) :
    ∃ k : Matrix (Fin 3) (Fin 3) ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).val],
      ∃ hk : k.det = 1,
      ∃ kI : GeneralLinearGroup (Fin 3) IntegralAdeles,
        ιGL3 v (LstV v z) = ιGL3 v (PV v z k hk) * GeneralLinearGroup.map integralEmbedding kI := by
  obtain ⟨k, A, hK⟩ := exists_k0 r hz
  have hk : k.det = 1 := hK.1
  obtain ⟨kI, hkI⟩ := kInv_lift v k hk
  refine ⟨k, hk, kI, ?_⟩
  rw [hkI, LstV, LstGL_eq_PGL_mul_inv z.1 z.2 k hk, map_mul, ιGL3_mul]
  rfl

end Place

end TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitGL

end
