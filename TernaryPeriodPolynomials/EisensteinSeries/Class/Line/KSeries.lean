module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.SeriesTransl
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Cusp.TransGen

@[expose] public section


/-!
# The series of both seed types at every cusp: conjugation and the cusp composition law

Paper: "the same letters
for the rational conjugates".

* `seriesFormK_cxP`: the series of type `b` at any cusp is `cxP b` (coefficientwise complex conjugation
  for `b = true`) of the holomorphic one.
* `seriesFormK_comp`: **cusp composition law**, for both seed types: pulling the series at the cusp `h'`
  back along `planeAct(h⁻¹)` gives the `ρ(h⁻¹)`-twist of the series at the cusp `h' h⁻¹`:

  `(planeAct h⁻¹)^* 𝓔^b_{h'} = ρ(h⁻¹) 𝓔^b_{h' h⁻¹}`  (on `Ω`).

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups
open MvPolynomial
noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument

section Conjugation

theorem cx_tsum (b : Bool) {ι : Type*} (g : ι → ℂ) : cx b (∑' i, g i) = ∑' i, cx b (g i) := by
  cases b
  · simp [cx]
  · simp only [cx]
    exact Complex.conj_tsum g

variable (D : CuspData) (Γ : Subgroup SL(3, ℤ)) (n : ℕ) (N : ℕ)
  (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))

theorem seriesCoeffK_cx (b : Bool) (i j : Fin 5) (m : Fin 3 →₀ ℕ) (x : Fin 5 → ℝ) :
    seriesCoeffK b D Γ n f i j m x = cx b (seriesCoeffK false D Γ n f i j m x) := by
  unfold seriesCoeffK
  rw [cx_tsum]
  refine tsum_congr fun c => ?_
  rw [termFunK_eq, termFunK_eq]
  simp only [cxL_apply]
  cases b <;> simp [cx]

theorem seriesFormK_cxP (b : Bool) (y : Fin 5 → ℝ) (i j : Fin 5) :
    seriesFormK b D Γ n f y i j = cxP b (seriesFormK false D Γ n f y i j) := by
  apply MvPolynomial.ext
  intro m
  rw [coeff_seriesFormK, coeff_cxP, coeff_seriesFormK, seriesCoeffK_cx]

end Conjugation

section Composition

variable (N : ℕ) [NeZero N] (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))

omit [NeZero N] in
theorem formPullback_rho (G : Matrix (Fin 3) (Fin 3) ℝ) (Φ : (Fin 5 → ℝ) → (Fin 5 → ℝ))
    (W : (Fin 5 → ℝ) → Fin 5 → Fin 5 → MvPolynomial (Fin 3) ℂ) (y : Fin 5 → ℝ) (i j : Fin 5) :
    formPullback Φ (fun y' a b => rho G (W y' a b)) y i j = rho G (formPullback Φ W y i j) := by
  unfold formPullback
  rw [rho_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [rho_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [rho_C_mul]

/-- **Cusp composition law, holomorphic seed**: `(planeAct h⁻¹)^* 𝓔_{h'} = ρ(h⁻¹) 𝓔_{h' h⁻¹}`. -/
theorem seriesFormK_false_comp (hn : 4 ≤ n) (h h' : SL(3, ℤ)) {y : Fin 5 → ℝ} (hy : y ∈ Omega) (a c : Fin 5) :
    formPullback (planeAct (realMat h⁻¹))
        (fun y' a' c' => seriesFormK false (CuspData.ofSL h') (gammaN N) n f y' a' c') y a c =
      rho (realMat h⁻¹) (seriesFormK false (CuspData.ofSL (h' * h⁻¹)) (gammaN N) n f y a c) := by
  set k : SL(3, ℤ) := h' * h⁻¹ with hk
  have hΩ : planeAct (realMat h⁻¹) y ∈ Omega := planeAct_mem (det_realMat _) hy
  have hd1 : DifferentiableAt ℝ (planeAct (realMat h⁻¹)) y := differentiableAt_planeAct (det_realMat _) hy
  have hd2 : DifferentiableAt ℝ (planeAct (realMat h')) (planeAct (realMat h⁻¹) y) :=
    differentiableAt_planeAct (det_realMat _) hΩ
  have e1 : formPullback (planeAct (realMat h⁻¹))
        (fun y' a' c' => seriesFormK false (CuspData.ofSL h') (gammaN N) n f y' a' c') y a c =
      formPullback (planeAct (realMat h⁻¹)) (fun y' a' c' =>
        rho (realMat h')⁻¹ (formPullback (planeAct (realMat h')) (seriesForm (gammaN N) n f) y' a' c'))
        y a c :=
    formPullback_congr_form y (fun a' c' => seriesFormK_false_eq N n f hn h' hΩ a' c') a c
  rw [e1, formPullback_rho]
  have hev : planeAct (realMat k) =ᶠ[nhds y] (planeAct (realMat h') ∘ planeAct (realMat h⁻¹)) :=
    Filter.eventuallyEq_of_mem (isOpen_Omega.mem_nhds hy) fun z hz => by
      rw [hk, realMat_mul]
      exact planeAct_mul (det_realMat _) hz
  have e2 := formPullback_comp (planeAct (realMat h⁻¹)) (planeAct (realMat h'))
    (seriesForm (gammaN N) n f) y hd1 hd2 a c
  rw [← e2, ← formPullback_congr _ hev, seriesFormK_false_eq N n f hn k hy]
  rw [rho_mul]
  have hmat : realMat h⁻¹ * (realMat k)⁻¹ = (realMat h')⁻¹ := by
    have hu : IsUnit (realMat h⁻¹).det := by rw [det_realMat]; exact isUnit_one
    rw [hk, realMat_mul, Matrix.mul_inv_rev, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu,
      Matrix.one_mul]
  rw [hmat]

/-- **Cusp composition law, both seed types**: `(planeAct h⁻¹)^* 𝓔^b_{h'} = ρ(h⁻¹) 𝓔^b_{h' h⁻¹}`
(on `Ω`). The series at the cusp `h'` pulled back to the cusp `h` is the `ρ(h⁻¹)`-twist of the series at
the cusp `h' h⁻¹`. -/
theorem seriesFormK_comp (hn : 4 ≤ n) (b : Bool) (h h' : SL(3, ℤ)) {y : Fin 5 → ℝ} (hy : y ∈ Omega) (a c : Fin 5) :
    formPullback (planeAct (realMat h⁻¹))
        (fun y' a' c' => seriesFormK b (CuspData.ofSL h') (gammaN N) n f y' a' c') y a c =
      rho (realMat h⁻¹) (seriesFormK b (CuspData.ofSL (h' * h⁻¹)) (gammaN N) n f y a c) := by
  have e : (fun y' a' c' => seriesFormK b (CuspData.ofSL h') (gammaN N) n f y' a' c') =
      fun y' a' c' => cxP b (seriesFormK false (CuspData.ofSL h') (gammaN N) n f y' a' c') := by
    funext y' a' c'
    exact seriesFormK_cxP _ _ n N f b y' a' c'
  rw [e, formPullback_cxP, seriesFormK_false_comp N n f hn h h' hy, seriesFormK_cxP _ _ n N f b,
    rho_cxP]

end Composition

end TernaryPeriodPolynomials.Argument.EisensteinClass
