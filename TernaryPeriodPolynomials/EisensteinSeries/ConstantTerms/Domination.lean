module

public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.Coset
public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.Compact
public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.Lattice

@[expose] public section


/-!
# Domination of a height-decaying family by a summable function on `Γ_P \ Γ` (Appendix C.3)

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergenceC4

open scoped ContDiff
open Matrix MvPolynomial

/-! ### Domination over the coset space by a summable function -/

theorem sqrt_pow_eq_rpow' (T : ℝ) (hT : 0 ≤ T) (N : ℕ) :
    (Real.sqrt T) ^ N = T ^ ((N : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hT]
  ring_nf

/-- A bound of the form `B(γ,q) ≤ C / (√ t(γ q))^{n+3}` on a compact set is dominated by a summable
function on `Γ_P \ Γ`, for `n ≥ 4`. -/
theorem exists_summable_dominating (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ)) (n : ℕ)
    (hn : 4 ≤ n) {K : Set (Fin 5 → ℝ)} (hK : IsCompact K) (hKΩ : K ⊆ Omega)
    (B : Γ → (Fin 5 → ℝ) → ℝ) (C₁ : ℝ)
    (hB : ∀ γ : Γ, ∀ q ∈ K, B γ q ≤ C₁ / (Real.sqrt (planeAct (realMat γ.1) q 4)) ^ (n + 3)) :
    ∃ b : PlaneCoset Γ → ℝ, Summable b ∧ ∀ (γ : Γ), ∀ q ∈ K, B γ q ≤ b (Quotient.mk _ γ) := by
  set s : ℝ := ((n : ℝ) + 3) / 2 with hs
  obtain ⟨Λ₀, hΛ₀⟩ := exists_bound_planePinv hK hKΩ
  set L : ℝ := max Λ₀ 1 with hL
  have hL1 : 1 ≤ L := le_max_right _ _
  have hL0 : 0 < 3 * L := by linarith
  set C₂ : ℝ := max C₁ 0 with hC₂
  refine ⟨fun c => C₂ * (3 * L) ^ s * ‖(fun j => (cosetRow Γ c j : ℝ))‖ ^ (-s), ?_, ?_⟩
  · have hr : -s < -3 := by
      rw [hs]; have : (4 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have h1 := summable_intVec_norm_rpow hr
    have h2 : Summable ((fun v : Fin 3 → ℤ => ‖(fun j => (v j : ℝ))‖ ^ (-s)) ∘ cosetRow Γ) :=
      h1.comp_injective (cosetRow_injective Γ)
    exact (h2.mul_left (C₂ * (3 * L) ^ s))
  · intro a q hq
    set g := realMat a.1 with hg
    have hdet : g.det = 1 := det_realMat a.1
    have hqΩ := hKΩ hq
    have hT := (planeAct_mem hdet hqΩ).2
    have hbound := hB a q hq
    have hrow : ‖fun j : Fin 3 => g 2 j‖ ≤ 3 * L * planeAct g q 4 :=
      norm_bottomRow_le hdet hqΩ L (fun l j' => (hΛ₀ q hq l j').trans (le_max_left _ _))
    have hvec : (fun j : Fin 3 => g 2 j) = fun j => ((cosetRow Γ (Quotient.mk _ a) j : ℤ) : ℝ) := by
      funext j
      simp [hg, realMat_apply, cosetRow, bottomRowZ]
    rw [hvec] at hrow
    set v : ℝ := ‖fun j => ((cosetRow Γ (Quotient.mk _ a) j : ℤ) : ℝ)‖ with hv
    have hvpos : 0 < v := by
      rw [hv, norm_pos_iff]
      intro h0
      apply bottomRowZ_ne_zero a.1
      funext j
      have := congrFun h0 j
      simpa [cosetRow, bottomRowZ] using this
    have hX : v / (3 * L) ≤ planeAct g q 4 := by
      rw [div_le_iff₀ hL0]; linarith
    have hpow : (v / (3 * L)) ^ s ≤ (Real.sqrt (planeAct g q 4)) ^ (n + 3) := by
      rw [sqrt_pow_eq_rpow' _ hT.le]
      have : ((n + 3 : ℕ) : ℝ) / 2 = s := by rw [hs]; push_cast; ring
      rw [this]
      exact Real.rpow_le_rpow (div_pos hvpos hL0).le hX (by rw [hs]; positivity)
    have hXs : 0 < (v / (3 * L)) ^ s := Real.rpow_pos_of_pos (div_pos hvpos hL0) _
    refine hbound.trans ?_
    calc C₁ / (Real.sqrt (planeAct g q 4)) ^ (n + 3)
        ≤ C₂ / (Real.sqrt (planeAct g q 4)) ^ (n + 3) :=
          div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ C₂ / (v / (3 * L)) ^ s :=
          div_le_div_of_nonneg_left (le_max_right _ _) hXs hpow
      _ = C₂ * (3 * L) ^ s * v ^ (-s) := by
          rw [Real.div_rpow hvpos.le hL0.le, Real.rpow_neg hvpos.le]
          field_simp

end TernaryPeriodPolynomials.Argument.ConvergenceC4
