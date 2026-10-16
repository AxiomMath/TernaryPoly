module

public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.Series
public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.ClosedTerms

@[expose] public section


/-!
# Closedness of the series `ar:eq:Eseries` (Appendix C.3, Proposition C.4)

The series of coefficient functions may be differentiated termwise once on `Ω` (`seriesCoeff_fderiv_apply`)
by the summable bound on first derivatives; every term is closed (`closedAt_summand_coeff`); hence the
sum is closed at every point of `Ω` (`seriesCoeff_closedAt`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergenceC4

open scoped ContDiff
open Matrix MvPolynomial

/-! ### Closedness of the series -/

section SeriesClosed

open UpperHalfPlane ModularForm
open scoped UpperHalfPlane

variable (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ))
  {F : Type*} [FunLike F ℍ ℂ] (Λ : Subgroup (GL (Fin 2) ℝ)) [Λ.HasDetOne] [Λ.IsArithmetic]
  (n : ℕ) [CuspFormClass F Λ ((n + 3 : ℕ) : ℤ)] (f : F)

include Λ

omit [Λ.HasDetOne] in
theorem summable_fderiv_termFun (hn : 4 ≤ n) {x : Fin 5 → ℝ} (hx : x ∈ Omega) (i j : Fin 5)
    (m : Fin 3 →₀ ℕ) (v : Fin 5 → ℝ) :
    Summable (fun c : PlaneCoset Γ => fderiv ℝ (termFun Γ n f c i j m) x v) := by
  obtain ⟨b, hb, hbd⟩ := exists_summable_jet_bound Γ Λ n f hn (isCompact_singleton (x := x))
    (Set.singleton_subset_iff.2 hx) 1 i j m
  refine Summable.of_norm_bounded (hb.mul_left ‖v‖) fun c => ?_
  have h1 := hbd c x rfl
  rw [norm_iteratedFDeriv_one] at h1
  calc ‖fderiv ℝ (termFun Γ n f c i j m) x v‖ ≤ ‖fderiv ℝ (termFun Γ n f c i j m) x‖ * ‖v‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ b c * ‖v‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ = ‖v‖ * b c := by ring

omit [Λ.HasDetOne] in
theorem seriesCoeff_fderiv_apply (hn : 4 ≤ n) (i j : Fin 5) (m : Fin 3 →₀ ℕ) {x : Fin 5 → ℝ}
    (hx : x ∈ Omega) (v : Fin 5 → ℝ) :
    fderiv ℝ (seriesCoeff Γ n f i j m) x v =
      ∑' c : PlaneCoset Γ, fderiv ℝ (termFun Γ n f c i j m) x v := by
  have h := (seriesCoeff_smooth Γ Λ n f hn i j m).2 1 x hx
  obtain ⟨b, hb, hbd⟩ := exists_summable_jet_bound Γ Λ n f hn (isCompact_singleton (x := x))
    (Set.singleton_subset_iff.2 hx) 1 i j m
  have hsum : Summable (fun c : PlaneCoset Γ => iteratedFDeriv ℝ 1 (termFun Γ n f c i j m) x) :=
    Summable.of_norm_bounded hb fun c => hbd c x rfl
  have := congrArg (fun L => L (fun _ => v)) h
  simp only [iteratedFDeriv_one_apply] at this
  rw [this]
  have hev := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 => Fin 5 → ℝ) ℂ
    (fun _ => v)).map_tsum hsum
  simpa using hev

omit [Λ.HasDetOne] in
theorem seriesCoeff_closedAt (hn : 4 ≤ n) {x : Fin 5 → ℝ} (hx : x ∈ Omega) (m : Fin 3 →₀ ℕ) :
    ClosedAt (fun a b y => seriesCoeff Γ n f a b m y) x := by
  intro i j k
  rw [seriesCoeff_fderiv_apply Γ Λ n f hn j k m hx, seriesCoeff_fderiv_apply Γ Λ n f hn i k m hx,
    seriesCoeff_fderiv_apply Γ Λ n f hn i j m hx]
  rw [← Summable.tsum_sub (summable_fderiv_termFun Γ Λ n f hn hx j k m _)
      (summable_fderiv_termFun Γ Λ n f hn hx i k m _),
    ← Summable.tsum_add ((summable_fderiv_termFun Γ Λ n f hn hx j k m _).sub
      (summable_fderiv_termFun Γ Λ n f hn hx i k m _))
      (summable_fderiv_termFun Γ Λ n f hn hx i j m _)]
  have hz : ∀ c : PlaneCoset Γ, fderiv ℝ (termFun Γ n f c j k m) x (Pi.single i 1) -
      fderiv ℝ (termFun Γ n f c i k m) x (Pi.single j 1) +
      fderiv ℝ (termFun Γ n f c i j m) x (Pi.single k 1) = 0 := fun c =>
    closedAt_summand_coeff n (hfun f) (hfun_differentiableOn Λ n f) (det_realMat _) hx m i j k
  exact (tsum_congr hz).trans tsum_zero

end SeriesClosed

end TernaryPeriodPolynomials.Argument.ConvergenceC4
