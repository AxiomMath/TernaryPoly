module

public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.Smooth
public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.Decomp
public import Mathlib.Topology.Instances.Matrix

@[expose] public section


/-!
# Uniform bounds on compacta (Appendix C.3)

Uniform bounds, over a compact set `K ⊂ Ω` and over the compact group `SO(3)`, of the entries of
`P(q)⁻¹` and of the derivatives of `Φ_k` at the base point and `Φ_{P(q)⁻¹}` at `q`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergenceC4

open Matrix MvPolynomial

/-! ### Compactness: uniform bounds -/

/-- Special orthogonal matrices, as functions on `Fin 3 × Fin 3`. -/
def SOrth : Set (Fin 3 → Fin 3 → ℝ) :=
  {k | matOfFun k * (matOfFun k).transpose = 1 ∧ (matOfFun k).det = 1}

theorem abs_le_one_of_orth {k : Fin 3 → Fin 3 → ℝ} (hk : matOfFun k * (matOfFun k).transpose = 1)
    (i j : Fin 3) : |k i j| ≤ 1 := by
  have h := congrFun (congrFun hk i) i
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq, matOfFun_apply,
    Fin.sum_univ_three] at h
  have hsq : k i j * k i j ≤ 1 := by
    fin_cases j <;> simp <;> nlinarith [mul_self_nonneg (k i 0), mul_self_nonneg (k i 1),
      mul_self_nonneg (k i 2)]
  exact abs_le_one_iff_mul_self_le_one.2 hsq

theorem isCompact_SOrth : IsCompact SOrth := by
  have hc : Continuous (fun k : Fin 3 → Fin 3 → ℝ => matOfFun k) := continuous_id
  have hclosed : IsClosed SOrth := by
    have h1 : IsClosed {k : Fin 3 → Fin 3 → ℝ | matOfFun k * (matOfFun k).transpose = 1} :=
      isClosed_eq (hc.matrix_mul hc.matrix_transpose) continuous_const
    have h2 : IsClosed {k : Fin 3 → Fin 3 → ℝ | (matOfFun k).det = 1} :=
      isClosed_eq hc.matrix_det continuous_const
    exact h1.inter h2
  have hbox : IsCompact (Set.pi Set.univ fun _ : Fin 3 => Set.pi Set.univ fun _ : Fin 3 =>
      Set.Icc (-1 : ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  refine hbox.of_isClosed_subset hclosed ?_
  intro k hk i _ j _
  exact abs_le_one_iff_mul_self_le_one.1 (abs_le_one_of_orth hk.1 i j) |> fun h =>
    abs_le.1 (abs_le_one_of_orth hk.1 i j)

theorem norm_single_le_one (i : Fin 5) : ‖(Pi.single i (1 : ℝ) : Fin 5 → ℝ)‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
  by_cases h : j = i
  · subst h; simp
  · simp [h]

theorem abs_apply_le_norm (v : Fin 5 → ℝ) (c : Fin 5) : |v c| ≤ ‖v‖ := by
  simpa using norm_le_pi_norm v c

/-- Uniform bound of the derivative at the base point over all special orthogonal matrices. -/
theorem exists_bound_fderiv_SOrth : ∃ N : ℝ, ∀ k ∈ SOrth,
    ‖fderiv ℝ (planeAct (matOfFun k)) basePt‖ ≤ N := by
  refine isCompact_SOrth.exists_bound_of_continuousOn ?_
  intro k hk
  have hd : (matOfFun k).det = 1 := hk.2
  have h1 : ContDiffAt ℝ ⊤ (Function.uncurry fun (k : Fin 3 → Fin 3 → ℝ) (p : Fin 5 → ℝ) =>
      planeAct (matOfFun k) p) (k, (fun _ : Fin 3 → Fin 3 → ℝ => basePt) k) :=
    contDiffAt_planeAct_pair (g := matOfFun k) hd basePt_mem
  have h2 := h1.fderiv (g := fun _ : Fin 3 → Fin 3 → ℝ => basePt) (m := 0)
    contDiffAt_const (by simp)
  exact h2.continuousAt.continuousWithinAt

theorem exists_bound_planePinv {K : Set (Fin 5 → ℝ)} (hK : IsCompact K) (hKΩ : K ⊆ Omega) :
    ∃ Λ : ℝ, ∀ q ∈ K, ∀ l j, |planePinv q l j| ≤ Λ := by
  obtain ⟨Λ, hΛ⟩ := hK.exists_bound_of_continuousOn
    (f := fun q : Fin 5 → ℝ => matToFun (planePinv q))
    (fun q hq => (contDiffAt_matToFun_planePinv (hKΩ hq)).continuousAt.continuousWithinAt)
  refine ⟨Λ, fun q hq l j => ?_⟩
  have := hΛ q hq
  calc |planePinv q l j| = ‖matToFun (planePinv q) l j‖ := by
        simp [matToFun]
    _ ≤ ‖matToFun (planePinv q) l‖ := norm_le_pi_norm _ _
    _ ≤ ‖matToFun (planePinv q)‖ := norm_le_pi_norm _ _
    _ ≤ Λ := this

/-- Uniform bound of `D Φ_{P(q)⁻¹}` at `q` over a compact set. -/
theorem exists_bound_fderiv_pinv {K : Set (Fin 5 → ℝ)} (hK : IsCompact K) (hKΩ : K ⊆ Omega) :
    ∃ N : ℝ, ∀ q ∈ K, ‖fderiv ℝ (planeAct (planePinv q)) q‖ ≤ N := by
  refine hK.exists_bound_of_continuousOn ?_
  intro q hq
  have hqΩ := hKΩ hq
  have hd := det_planePinv hqΩ
  have hin : ContDiffAt ℝ ⊤ (fun z : (Fin 5 → ℝ) × (Fin 5 → ℝ) =>
      (matToFun (planePinv z.1), z.2)) (q, q) :=
    ((contDiffAt_matToFun_planePinv hqΩ).comp (q, q) contDiffAt_fst).prodMk contDiffAt_snd
  have h1 : ContDiffAt ℝ ⊤ (Function.uncurry fun (x : Fin 5 → ℝ) (p : Fin 5 → ℝ) =>
      planeAct (planePinv x) p) (q, (fun x : Fin 5 → ℝ => x) q) := by
    have := (contDiffAt_planeAct_pair (g := planePinv q) hd hqΩ).comp (q, q) hin
    exact this
  have h2 := h1.fderiv (g := fun x : Fin 5 → ℝ => x) (m := 0) contDiffAt_id (by simp)
  exact h2.continuousAt.continuousWithinAt

end TernaryPeriodPolynomials.Argument.ConvergenceC4
