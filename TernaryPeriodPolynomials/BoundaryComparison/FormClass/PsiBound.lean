module

public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.PsiExpansion

@[expose] public section


/-!
# The coefficient `(i, j, m)` of the summand at a general point `y ∈ Ω`: equivariance, expansion, bound

Formalized by Claude Sonnet 5.5.

`PsiCoefQ y i j m c w` is the `m`-th coefficient of the `(i, j)` component at `y` of the summand at `k γ_c qMat w` (the `E`-valued
form, not its pullback to the line face).  `PsiCoefQ_expansion`: through the cocycle law it is a finite sum of continuous weights times the
terms of the series at the translated point `planeAct (qMat w) y`; `PsiCoefQ_continuous_bound`: continuity in `w` and a locally summable
bound in the coset.
-/

open scoped MatrixGroups ContDiff
open MvPolynomial
open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument.EisensteinClass TernaryPeriodPolynomials.Argument.SeedC3S4c
  TernaryPeriodPolynomials.Argument.GammaNFaces TernaryPeriodPolynomials.Argument.Statements.ConvergenceC4
  TernaryPeriodPolynomials.Argument.Statements.EisensteinClass TernaryPeriodPolynomials.Argument.EisensteinDual
  TernaryPeriodPolynomials.Argument TernaryPoly.SmoothLocalDeRham TernaryPoly.SmoothCoveringDeRham
  TernaryPeriodPolynomials.Argument.SeedC3.Psi

noncomputable section
namespace TernaryPeriodPolynomials.Argument.FormClassK

variable (N : ℕ) [NeZero N] (k : SL(3, ℤ)) (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))

/-- The coefficient of the `(i, j)` component at `y` of the summand at `k γ_c qMat w`. -/
def PsiCoefQ (y : Fin 5 → ℝ) (i j : Fin 5) (m : Fin 3 →₀ ℕ) (c : Ck N k) (w : Fin 2 → ℝ) : ℂ :=
  (summandPoly n (hfun f) (realMat k * realMat (Quotient.out c).1 * qMat w) y i j).coeff m

omit [NeZero N] in
theorem PsiCoefQ_mk {y : Fin 5 → ℝ} (hy : y ∈ Omega) (i j : Fin 5) (m : Fin 3 →₀ ℕ) (a : ↥(gammaN N)) (w : Fin 2 → ℝ) :
    PsiCoefQ N k n f y i j m (Quotient.mk _ a) w =
      (summandPoly n (hfun f) (realMat k * realMat a.1 * qMat w) y i j).coeff m := by
  unfold PsiCoefQ
  have h : (Quotient.mk _ (Quotient.out (Quotient.mk (QuotientGroup.rightRel
      ((stabRow (CuspData.ofSL k).r).subgroupOf (gammaN N))) a)) : Ck N k) = Quotient.mk _ a :=
    Quotient.out_eq _
  rw [summandPoly_cusp_coset N k n f _ _ (Quotient.exact h) (det_qMat w) hy i j]

omit [NeZero N] in
/-- **Equivariance of `PsiCoefQ` for the line radical lattice.** -/
theorem PsiCoefQ_latQ {y : Fin 5 → ℝ} (hy : y ∈ Omega) (i j : Fin 5) (m : Fin 3 →₀ ℕ) (ℓ : Fin 2 → ℤ) (c : Ck N k)
    (w : Fin 2 → ℝ) :
    PsiCoefQ N k n f y i j m (cmulR N k (latQ N ℓ) c) w = PsiCoefQ N k n f y i j m c ((N : ℝ) • intVec ℓ + w) := by
  induction c using Quotient.inductionOn with | _ a => ?_
  rw [cmulR_mk, PsiCoefQ_mk N k n f hy i j m, PsiCoefQ_mk N k n f hy i j m]
  have : realMat k * realMat (a * latQ N ℓ).1 * qMat w =
      realMat k * realMat a.1 * qMat ((N : ℝ) • intVec ℓ + w) := by
    show realMat k * realMat (a.1 * (latQ N ℓ).1) * qMat w = _
    rw [realMat_mul, realMat_latQ, ← Matrix.mul_assoc, Matrix.mul_assoc _ (qMat _) (qMat w), qMat_mul]
  rw [this]

omit [NeZero N] in
/-- **Expansion of `PsiCoefQ` through the translated point.** -/
theorem PsiCoefQ_expansion {y : Fin 5 → ℝ} (hy : y ∈ Omega) (i j : Fin 5) (m : Fin 3 →₀ ℕ) (c : Ck N k) (w : Fin 2 → ℝ) :
    PsiCoefQ N k n f y i j m c w =
      ∑ t ∈ monSet n ×ˢ (Finset.univ : Finset (Fin 5)) ×ˢ (Finset.univ : Finset (Fin 5)),
        ((((fderiv ℝ (planeAct (qMat w)) y (Pi.single i 1) t.2.1 *
          fderiv ℝ (planeAct (qMat w)) y (Pi.single j 1) t.2.2 : ℝ) : ℂ)) * kapQ m t.1 w) *
          termFunK false (CuspData.ofSL k) (gammaN N) n f c t.2.1 t.2.2 t.1 (planeAct (qMat w) y) := by
  have hg : (realMat k * realMat (Quotient.out c).1).det = 1 := by
    rw [Matrix.det_mul, det_realMat, det_realMat]; norm_num
  unfold PsiCoefQ
  rw [summandPoly_mul_eq n (hfun f) hg (det_qMat w) hy i j, qMat_inv]
  have hhom : (formPullback (planeAct (qMat w)) (fun y a b => summandPoly n (hfun f)
      (realMat k * realMat (Quotient.out c).1) y a b) y i j).IsHomogeneous n := by
    unfold formPullback
    refine MvPolynomial.IsHomogeneous.sum _ _ _ fun a _ => ?_
    refine MvPolynomial.IsHomogeneous.sum _ _ _ fun b _ => ?_
    exact (summandPoly_isHomogeneous n (hfun f) hg _ a b).C_mul _
  rw [coeff_rho_expansion hhom _ m, Finset.sum_product]
  refine Finset.sum_congr rfl fun m' _ => ?_
  rw [Finset.sum_product]
  unfold formPullback kapQ
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [termFunK, summandK_false]
  rw [show (CuspData.ofSL k).a = realMat k from rfl]
  ring

theorem continuous_planeAct_qMat {y : Fin 5 → ℝ} (hy : y ∈ Omega) :
    Continuous fun w : Fin 2 → ℝ => planeAct (qMat w) y := by
  rw [continuous_iff_continuousAt]
  intro w
  have h := (contDiffAt_planeAct_pair (det_qMat w) hy).continuousAt
  exact h.comp (f := fun w' : Fin 2 → ℝ => (matToFun (qMat w'), y))
    ((continuous_matToFun_qMat.prodMk continuous_const).continuousAt)

theorem termFunK_qMat_bound (hn : 4 ≤ n) {y : Fin 5 → ℝ} (hy : y ∈ Omega) (a b : Fin 5) (m' : Fin 3 →₀ ℕ) (R : ℝ) :
    ∃ B : Ck N k → ℝ, Summable B ∧ ∀ c w, (∀ l, |w l| ≤ R) →
      ‖termFunK false (CuspData.ofSL k) (gammaN N) n f c a b m' (planeAct (qMat w) y)‖ ≤ B c := by
  set Kb : Set (Fin 2 → ℝ) := Metric.closedBall 0 |R| with hKb
  have hKbc : IsCompact Kb := isCompact_closedBall _ _
  set K : Set (Fin 5 → ℝ) := (fun w : Fin 2 → ℝ => planeAct (qMat w) y) '' Kb with hK
  have hKc : IsCompact K := hKbc.image (continuous_planeAct_qMat hy)
  have hKΩ : K ⊆ Omega := by
    rintro _ ⟨w, -, rfl⟩
    exact planeAct_mem (det_qMat w) hy
  obtain ⟨b', hbs, hbb⟩ := normal_convergence_at false (CuspData.ofSL k) (gammaN N) (leviGroup N) n f hn hKc hKΩ 0
  refine ⟨b', hbs, fun c w hw => ?_⟩
  have hwK : w ∈ Kb := by
    rw [hKb, mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (abs_nonneg R)]
    intro l
    simpa using (hw l).trans (le_abs_self R)
  have := hbb c _ ⟨w, hwK, rfl⟩ a b m'
  simpa using this

/-- **Continuity in `w` and a locally summable bound in the coset** for the coefficient at a general point `y ∈ Ω`. -/
theorem PsiCoefQ_continuous_bound (hn : 4 ≤ n) {y : Fin 5 → ℝ} (hy : y ∈ Omega) (i j : Fin 5) (m : Fin 3 →₀ ℕ) :
    (∀ c : Ck N k, Continuous (PsiCoefQ N k n f y i j m c)) ∧
    ∀ R : ℝ, ∃ B : Ck N k → ℝ, Summable B ∧ ∀ c w, (∀ l, |w l| ≤ R) → ‖PsiCoefQ N k n f y i j m c w‖ ≤ B c := by
  have key := sum_mul_bound (Cs := Ck N k)
    (monSet n ×ˢ (Finset.univ : Finset (Fin 5)) ×ˢ (Finset.univ : Finset (Fin 5)))
    (fun t w => ((((fderiv ℝ (planeAct (qMat w)) y (Pi.single i 1) t.2.1 *
          fderiv ℝ (planeAct (qMat w)) y (Pi.single j 1) t.2.2 : ℝ) : ℂ)) * kapQ m t.1 w))
    (fun t => by
      refine Continuous.mul ?_ (continuous_kapQ m t.1)
      exact Complex.continuous_ofReal.comp
        ((continuous_fderiv_planeAct_qMat hy i t.2.1).mul (continuous_fderiv_planeAct_qMat hy j t.2.2)))
    (fun t c w => termFunK false (CuspData.ofSL k) (gammaN N) n f c t.2.1 t.2.2 t.1 (planeAct (qMat w) y))
    (fun t c => (contDiffOn_termFunK false (CuspData.ofSL k) (gammaN N) (leviGroup N) n f c t.2.1 t.2.2 t.1
        |>.continuousOn.comp_continuous (continuous_planeAct_qMat hy) fun w => planeAct_mem (det_qMat w) hy))
    (fun t R => termFunK_qMat_bound N k n f hn hy t.2.1 t.2.2 t.1 R)
  have heq : ∀ c, PsiCoefQ N k n f y i j m c = fun w => ∑ t ∈ monSet n ×ˢ (Finset.univ : Finset (Fin 5)) ×ˢ
      (Finset.univ : Finset (Fin 5)),
      ((((fderiv ℝ (planeAct (qMat w)) y (Pi.single i 1) t.2.1 *
          fderiv ℝ (planeAct (qMat w)) y (Pi.single j 1) t.2.2 : ℝ) : ℂ)) * kapQ m t.1 w) *
        termFunK false (CuspData.ofSL k) (gammaN N) n f c t.2.1 t.2.2 t.1 (planeAct (qMat w) y) := by
    intro c; funext w; exact PsiCoefQ_expansion N k n f hy i j m c w
  refine ⟨fun c => ?_, fun R => ?_⟩
  · rw [heq]; exact key.1 c
  · obtain ⟨B, hBs, hBb⟩ := key.2 R
    refine ⟨B, hBs, fun c w hw => ?_⟩
    rw [PsiCoefQ_expansion N k n f hy i j m c w]
    exact hBb c w hw

end TernaryPeriodPolynomials.Argument.FormClassK
