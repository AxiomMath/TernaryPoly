module

public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.Equivariance
public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.SeriesClosed

@[expose] public section


/-!
# Proposition C.4: packaging of the series

Normal convergence of every derivative with one summable majorant for all components and
coefficients (`exists_summable_jet_bound_all`), smoothness and closedness of the coefficient forms of
the sum in the coordinate form of the `seed_closed_equivariant` (`seriesForm_closed`,
`contDiffOn_seriesForm_coeff`), independence of the coset representatives
(`seriesCoeff_eq_tsum_section`), and the transformation law `δ^* E = ρ(δ) E`
(`seriesForm_pullback`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergenceC4

open scoped ContDiff
open Matrix MvPolynomial

section Packaging

open UpperHalfPlane ModularForm
open scoped UpperHalfPlane

variable (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ))
  {F : Type*} [FunLike F ℍ ℂ] (Λ : Subgroup (GL (Fin 2) ℝ)) [Λ.HasDetOne] [Λ.IsArithmetic]
  (n : ℕ) [CuspFormClass F Λ ((n + 3 : ℕ) : ℤ)] (f : F)

include Λ

omit [Λ.HasDetOne] in
/-- **Normal convergence of every derivative.** For every compact `K ⊂ Ω` and every order `k` one
summable function on `Γ_P\Γ` dominates, uniformly on `K`, the `k`-th derivative of every coefficient
of every component of every term of the series. -/
theorem exists_summable_jet_bound_all (hn : 4 ≤ n) {K : Set (Fin 5 → ℝ)} (hK : IsCompact K)
    (hKΩ : K ⊆ Omega) (k : ℕ) :
    ∃ b : PlaneCoset Γ → ℝ, Summable b ∧ ∀ (c : PlaneCoset Γ), ∀ x ∈ K, ∀ (i j : Fin 5)
      (m : Fin 3 →₀ ℕ), ‖iteratedFDeriv ℝ k (termFun Γ n f c i j m) x‖ ≤ b c := by
  have h : ∀ (i j : Fin 5) (m : Fin 3 →₀ ℕ), ∃ b : PlaneCoset Γ → ℝ, Summable b ∧ ∀ c, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ k (termFun Γ n f c i j m) x‖ ≤ b c :=
    fun i j m => exists_summable_jet_bound Γ Λ n f hn hK hKΩ k i j m
  choose b hb hbd using h
  refine ⟨fun c => ∑ i, ∑ j, ∑ m ∈ monSet n, |b i j m c|, ?_, ?_⟩
  · exact summable_sum fun i _ => summable_sum fun j _ => summable_sum fun m _ => (hb i j m).abs
  · intro c x hx i j m
    by_cases hm : m ∈ monSet n
    · calc ‖iteratedFDeriv ℝ k (termFun Γ n f c i j m) x‖ ≤ b i j m c := hbd i j m c x hx
        _ ≤ |b i j m c| := le_abs_self _
        _ ≤ ∑ m ∈ monSet n, |b i j m c| :=
          Finset.single_le_sum (f := fun m => |b i j m c|) (fun _ _ => abs_nonneg _) hm
        _ ≤ ∑ j, ∑ m ∈ monSet n, |b i j m c| :=
          Finset.single_le_sum (f := fun j => ∑ m ∈ monSet n, |b i j m c|)
            (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ j)
        _ ≤ ∑ i, ∑ j, ∑ m ∈ monSet n, |b i j m c| :=
          Finset.single_le_sum (f := fun i => ∑ j, ∑ m ∈ monSet n, |b i j m c|)
            (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
            (Finset.mem_univ i)
    · have h0 : termFun Γ n f c i j m = fun _ => 0 :=
        funext fun y => termFun_coeff_eq_zero Γ n f c y i j hm
      rw [h0]
      have : iteratedFDeriv ℝ k (fun _ : Fin 5 → ℝ => (0 : ℂ)) x = 0 := by
        simp
      rw [this, norm_zero]
      exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
        abs_nonneg _

omit [Λ.HasDetOne] in
/-- **The series is smooth and closed.** The coordinate form of `d E = 0` for the coefficient
forms of the sum, with the same coordinate partial derivatives as the closedness clause of
`seed_closed_equivariant`. -/
theorem seriesForm_closed (hn : 4 ≤ n) {x : Fin 5 → ℝ} (hx : x ∈ Omega) (m : Fin 3 →₀ ℕ)
    (i j k : Fin 5) :
    coordPartial (fun q => (seriesForm Γ n f q j k).coeff m) i x -
        coordPartial (fun q => (seriesForm Γ n f q i k).coeff m) j x +
        coordPartial (fun q => (seriesForm Γ n f q i j).coeff m) k x = 0 := by
  have hd : ∀ a b, DifferentiableAt ℝ (seriesCoeff Γ n f a b m) x := fun a b =>
    ((seriesCoeff_smooth Γ Λ n f hn a b m).1.contDiffAt (isOpen_Omega.mem_nhds hx)).differentiableAt
      (by simp)
  simp_rw [coeff_seriesForm]
  rw [coordPartial_eq_fderiv (hd j k) i, coordPartial_eq_fderiv (hd i k) j,
    coordPartial_eq_fderiv (hd i j) k]
  exact seriesCoeff_closedAt Γ Λ n f hn hx m i j k

omit [Λ.HasDetOne] in
/-- Each coefficient of each component of the sum is `C^∞` on `Ω`. -/
theorem contDiffOn_seriesForm_coeff (hn : 4 ≤ n) (i j : Fin 5) (m : Fin 3 →₀ ℕ) :
    ContDiffOn ℝ ∞ (fun y => (seriesForm Γ n f y i j).coeff m) Omega := by
  simp_rw [coeff_seriesForm]
  exact (seriesCoeff_smooth Γ Λ n f hn i j m).1

omit [Λ.IsArithmetic] in
/-- **Independence of the coset representatives.** The sum over `Γ_P\Γ` may be computed with
any section `r` of the quotient map. -/
theorem seriesCoeff_eq_tsum_section (hLevi : LeviIn Γ Λ) {x : Fin 5 → ℝ} (hx : x ∈ Omega)
    (i j : Fin 5) (m : Fin 3 →₀ ℕ) (r : PlaneCoset Γ → Γ)
    (hr : ∀ c, (Quotient.mk _ (r c) : PlaneCoset Γ) = c) :
    seriesCoeff Γ n f i j m x =
      ∑' c : PlaneCoset Γ, (summandPoly n (hfun f) (realMat (r c).1) x i j).coeff m := by
  unfold seriesCoeff
  refine tsum_congr fun c => ?_
  rw [termFun_eq_cosetTerm Γ Λ n f hLevi hx i j m c]
  conv_lhs => rw [← hr c]
  rfl

/-- **`δ^* E = ρ(δ) E`.** -/
theorem seriesForm_pullback (hn : 4 ≤ n) (hLevi : LeviIn Γ Λ) (δ : Γ) {x : Fin 5 → ℝ}
    (hx : x ∈ Omega) (i j : Fin 5) :
    formPullback (planeAct (realMat δ.1)) (seriesForm Γ n f) x i j =
      SeedC3.rho (realMat δ.1) (seriesForm Γ n f x i j) := by
  rw [← seriesForm_equivariant Γ Λ n f hn hLevi δ hx i j, rho_mul,
    Matrix.mul_nonsing_inv _ (by rw [det_realMat]; exact isUnit_one), rho_one]

end Packaging

end TernaryPeriodPolynomials.Argument.ConvergenceC4
