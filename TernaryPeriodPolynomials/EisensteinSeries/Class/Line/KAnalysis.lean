module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Line.KCoef

@[expose] public section


/-!
# Analysis of the coefficient family `PhiQ0` at the cusp `k⁻¹ P k`

`PhiQ0 k c w` is continuous in `w`, locally summably bounded in the coset (normal convergence of the series
at the cusp `k⁻¹Pk`), and for the cosets with `r₀ = 0` (the first entry of the bottom row of `k γ_c`) its
integral along a closed period direction of the radical torus vanishes (`PhiQ0_closed`, cuspidality).

Formalized by Claude Sonnet 5.5.
-/

open MvPolynomial
open scoped MatrixGroups ContDiff Matrix
noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.SeedC3S4c
  TernaryPeriodPolynomials.Argument.FormClassK TernaryPeriodPolynomials.Argument.GammaNFaces
  TernaryPeriodPolynomials.Argument.Statements.EisensteinClass TernaryPeriodPolynomials.Argument.Statements.ConvergenceC4
  TernaryPeriodPolynomials.Argument.EisensteinDual
  TernaryPoly.SmoothLocalDeRham TernaryPoly.SmoothCoveringDeRham
  TernaryPeriodPolynomials.Argument.SeedC3.Psi

section Analysis

variable (N : ℕ) [NeZero N] (k : SL(3, ℤ)) (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))

omit [NeZero N] in
/-- **Expansion of `PhiQ0` through the translated face pullback of the terms of the series at `k⁻¹Pk`.** -/
theorem PhiQ0_expansion {x : Face} (hx : x ∈ faceSet) (p q : Fin 4) (m : Fin 3 →₀ ℕ)
    (c : Ck N k) (w : Fin 2 → ℝ) :
    PhiQ0 N k n f x p q m c w = ∑ m' ∈ monSet n, ∑ a : Fin 5, ∑ b : Fin 5,
      ((((fderiv ℝ jFace (x + shVec w) (Pi.single p 1) a *
        fderiv ℝ jFace (x + shVec w) (Pi.single q 1) b : ℝ) : ℂ)) * kapQ m m' w) *
        termFunK false (CuspData.ofSL k) (gammaN N) n f c a b m' (jFace (x + shVec w)) := by
  have hg : (realMat k * realMat (Quotient.out c).1).det = 1 := by
    rw [Matrix.det_mul, det_realMat, det_realMat]; norm_num
  unfold PhiQ0
  rw [← rho_fPull_shift n (hfun f) hg hx w p q]
  have hhom := fPull_isHomogeneous n jFace (fun y a b => summandPoly n (hfun f)
    (realMat k * realMat (Quotient.out c).1) y a b) (fun y a b => summandPoly_isHomogeneous n (hfun f)
    hg y a b) (x + shVec w) p q
  rw [coeff_rho_expansion hhom _ m]
  refine Finset.sum_congr rfl fun m' _ => ?_
  unfold fPull kapQ
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [termFunK, summandK_false]
  rw [show (CuspData.ofSL k).a = realMat k from rfl]
  ring

omit [NeZero N] in
theorem continuous_termFunK_jShift {x : Face} (hx : x ∈ faceSet) (c : Ck N k) (a b : Fin 5)
    (m' : Fin 3 →₀ ℕ) :
    Continuous fun w : Fin 2 → ℝ =>
      termFunK false (CuspData.ofSL k) (gammaN N) n f c a b m' (jFace (x + shVec w)) := by
  have h := (contDiffOn_termFunK false (CuspData.ofSL k) (gammaN N) (leviGroup N) n f c a b m').continuousOn
  exact h.comp_continuous (continuous_jShift hx) fun w => jPlane_mem (ptOf_mem (shVec_mem hx w))

/-- Uniform summable bound of the terms of the series at `k⁻¹Pk` along the translated face points. -/
theorem termFunK_jShift_bound (hn : 4 ≤ n) {x : Face} (hx : x ∈ faceSet) (a b : Fin 5)
    (m' : Fin 3 →₀ ℕ) (R : ℝ) :
    ∃ B : Ck N k → ℝ, Summable B ∧ ∀ c w, (∀ i, |w i| ≤ R) →
      ‖termFunK false (CuspData.ofSL k) (gammaN N) n f c a b m' (jFace (x + shVec w))‖ ≤ B c := by
  set Kb : Set (Fin 2 → ℝ) := Metric.closedBall 0 |R| with hKb
  have hKbc : IsCompact Kb := isCompact_closedBall _ _
  set K : Set (Fin 5 → ℝ) := (fun w : Fin 2 → ℝ => jFace (x + shVec w)) '' Kb with hK
  have hKc : IsCompact K := hKbc.image (continuous_jShift hx)
  have hKΩ : K ⊆ Omega := by
    rintro _ ⟨w, -, rfl⟩
    exact jPlane_mem (ptOf_mem (shVec_mem hx w))
  obtain ⟨b', hbs, hbb⟩ := normal_convergence_at false (CuspData.ofSL k) (gammaN N) (leviGroup N) n f
    hn hKc hKΩ 0
  refine ⟨b', hbs, fun c w hw => ?_⟩
  have hwK : w ∈ Kb := by
    rw [hKb, mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (abs_nonneg R)]
    intro i
    simpa using (hw i).trans (le_abs_self R)
  have := hbb c _ ⟨w, hwK, rfl⟩ a b m'
  simpa using this

omit [NeZero N] in
theorem PhiQ0_eq_sum_prod {x : Face} (hx : x ∈ faceSet) (p q : Fin 4) (m : Fin 3 →₀ ℕ)
    (c : Ck N k) (w : Fin 2 → ℝ) :
    PhiQ0 N k n f x p q m c w =
      ∑ i ∈ monSet n ×ˢ (Finset.univ : Finset (Fin 5)) ×ˢ (Finset.univ : Finset (Fin 5)),
        ((((fderiv ℝ jFace (x + shVec w) (Pi.single p 1) i.2.1 *
          fderiv ℝ jFace (x + shVec w) (Pi.single q 1) i.2.2 : ℝ) : ℂ)) * kapQ m i.1 w) *
          termFunK false (CuspData.ofSL k) (gammaN N) n f c i.2.1 i.2.2 i.1 (jFace (x + shVec w)) := by
  rw [PhiQ0_expansion N k n f hx p q m c w, Finset.sum_product]
  refine Finset.sum_congr rfl fun m' _ => ?_
  rw [Finset.sum_product]

theorem PhiQ0_continuous_bound (hn : 4 ≤ n) {x : Face} (hx : x ∈ faceSet) (p q : Fin 4)
    (m : Fin 3 →₀ ℕ) :
    (∀ c : Ck N k, Continuous (PhiQ0 N k n f x p q m c)) ∧
    ∀ R : ℝ, ∃ B : Ck N k → ℝ, Summable B ∧ ∀ c w, (∀ i, |w i| ≤ R) →
      ‖PhiQ0 N k n f x p q m c w‖ ≤ B c := by
  have key := sum_mul_bound (Cs := Ck N k)
    (monSet n ×ˢ (Finset.univ : Finset (Fin 5)) ×ˢ (Finset.univ : Finset (Fin 5)))
    (fun i w => ((((fderiv ℝ jFace (x + shVec w) (Pi.single p 1) i.2.1 *
          fderiv ℝ jFace (x + shVec w) (Pi.single q 1) i.2.2 : ℝ) : ℂ)) * kapQ m i.1 w))
    (fun i => by
      refine Continuous.mul ?_ (continuous_kapQ m i.1)
      exact Complex.continuous_ofReal.comp
        ((continuous_fderiv_jShift hx p i.2.1).mul (continuous_fderiv_jShift hx q i.2.2)))
    (fun i c w => termFunK false (CuspData.ofSL k) (gammaN N) n f c i.2.1 i.2.2 i.1
      (jFace (x + shVec w)))
    (fun i c => continuous_termFunK_jShift N k n f hx c i.2.1 i.2.2 i.1)
    (fun i R => termFunK_jShift_bound N k n f hn hx i.2.1 i.2.2 i.1 R)
  have heq : ∀ c, PhiQ0 N k n f x p q m c = fun w => ∑ i ∈ monSet n ×ˢ (Finset.univ : Finset (Fin 5)) ×ˢ
      (Finset.univ : Finset (Fin 5)),
      ((((fderiv ℝ jFace (x + shVec w) (Pi.single p 1) i.2.1 *
        fderiv ℝ jFace (x + shVec w) (Pi.single q 1) i.2.2 : ℝ) : ℂ)) * kapQ m i.1 w) *
        termFunK false (CuspData.ofSL k) (gammaN N) n f c i.2.1 i.2.2 i.1 (jFace (x + shVec w)) := by
    intro c; funext w; exact PhiQ0_eq_sum_prod N k n f hx p q m c w
  refine ⟨fun c => ?_, fun R => ?_⟩
  · rw [heq]; exact key.1 c
  · obtain ⟨B, hBs, hBb⟩ := key.2 R
    refine ⟨B, hBs, fun c w hw => ?_⟩
    rw [PhiQ0_eq_sum_prod N k n f hx p q m c w]
    exact hBb c w hw

omit [NeZero N] in
theorem PhiQ0_as_sum {x : Face} (p q : Fin 4) (m : Fin 3 →₀ ℕ) (c : Ck N k) (w : Fin 2 → ℝ) :
    PhiQ0 N k n f x p q m c w = ∑ a : Fin 5, ∑ b : Fin 5,
      ((((fderiv ℝ jFace x (Pi.single p 1) a * fderiv ℝ jFace x (Pi.single q 1) b : ℝ) : ℂ))) *
        (summandPoly n (hfun f) (realMat (k * (Quotient.out c).1) * qMat w) (jFace x) a b).coeff m := by
  unfold PhiQ0 fPull
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul, realMat_mul]

/-- **The closed-direction integral of `PhiQ0` vanishes on the cell `r₀ = 0`** (the line lies in the
plane `k γ`-conjugate of `P`): cuspidality of `f`. -/
theorem PhiQ0_closed {x : Face} (hx : x ∈ faceSet) (p q : Fin 4) (m : Fin 3 →₀ ℕ) (c : Ck N k)
    (h0 : cuspRow (gammaN N) (CuspData.ofSL k).r c 0 = 0) :
    ∃ i : Fin 2, ∀ w : Fin 2 → ℝ,
      ∫ s in (0 : ℝ)..1, PhiQ0 N k n f x p q m c (w + s • ((N : ℝ) • (Pi.single i 1 : Fin 2 → ℝ))) = 0 := by
  have hy : jFace x ∈ Omega := jPlane_mem (ptOf_mem hx)
  set γ : SL(3, ℤ) := k * (Quotient.out c).1 with hγ
  have hγ0 : (γ : Matrix (Fin 3) (Fin 3) ℤ) 2 0 = 0 := by
    rw [← cuspRow_out]; exact h0
  have hne : (γ : Matrix (Fin 3) (Fin 3) ℤ) 2 1 ≠ 0 ∨ (γ : Matrix (Fin 3) (Fin 3) ℤ) 2 2 ≠ 0 := by
    by_contra hcon
    rw [not_or, not_not, not_not] at hcon
    have hdet : (γ : Matrix (Fin 3) (Fin 3) ℤ).det = 1 := γ.2
    rw [Matrix.det_fin_three, hγ0, hcon.1, hcon.2] at hdet
    simp at hdet
  have mk : ∀ (i : Fin 2), (∀ w : Fin 2 → ℝ,
      ∫ s in (0 : ℝ)..1, ∑ a : Fin 5, ∑ b : Fin 5,
        ((((fderiv ℝ jFace x (Pi.single p 1) a * fderiv ℝ jFace x (Pi.single q 1) b : ℝ) : ℂ))) *
          (summandPoly n (hfun f) (realMat γ * qMat (w + s • ((N : ℝ) • (Pi.single i 1 : Fin 2 → ℝ))))
            (jFace x) a b).coeff m = 0) →
      ∀ w : Fin 2 → ℝ, ∫ s in (0 : ℝ)..1,
        PhiQ0 N k n f x p q m c (w + s • ((N : ℝ) • (Pi.single i 1 : Fin 2 → ℝ))) = 0 := by
    intro i hk w
    have := hk w
    simp_rw [PhiQ0_as_sum N k n f p q m c]
    exact this
  rcases hne with h1 | h2
  · refine ⟨0, mk 0 fun w => ?_⟩
    have := closed_direction_zero_Q N n f γ hγ0 (Pi.single 0 1) (by simpa [Pi.single_apply] using h1) w hy
      (fun i j => ((((fderiv ℝ jFace x (Pi.single p 1) i * fderiv ℝ jFace x (Pi.single q 1) j : ℝ) : ℂ))))
      m
    have e : intVec (Pi.single 0 1 : Fin 2 → ℤ) = (Pi.single 0 1 : Fin 2 → ℝ) := by
      funext i; fin_cases i <;> simp [intVec]
    rw [e] at this
    exact this
  · refine ⟨1, mk 1 fun w => ?_⟩
    have := closed_direction_zero_Q N n f γ hγ0 (Pi.single 1 1)
      (by simpa [Pi.single_apply] using h2) w hy
      (fun i j => ((((fderiv ℝ jFace x (Pi.single p 1) i * fderiv ℝ jFace x (Pi.single q 1) j : ℝ) : ℂ))))
      m
    have e : intVec (Pi.single 1 1 : Fin 2 → ℤ) = (Pi.single 1 1 : Fin 2 → ℝ) := by
      funext i; fin_cases i <;> simp [intVec]
    rw [e] at this
    exact this

end Analysis

end TernaryPeriodPolynomials.Argument.EisensteinClass
