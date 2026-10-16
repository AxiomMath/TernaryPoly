module

public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.PsiBound

@[expose] public section


/-!
# The `E`-valued intertwiner at a general point `y ∈ Ω`: absolute convergence and the orbit sum

Formalized by Claude Sonnet 5.5.

`FzE b k y i j m (σ, w)` is the `m`-th coefficient of the `(i, j)` component at `y` of `cxP b` of the adelic section at
`(w₀⁻¹u(σ, w), ι(k⁻¹))`.  `FzE_integral`: for `3 ≤ N`, `4 ≤ n`, `y ∈ Ω` it is integrable over `𝔸_f² × ℝ²` with integral `cx b` of the orbit sum
`Σ_o ∫_{ℝ²} PsiCoefQ(c_o)(N v) dv`.
-/

open Matrix GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open scoped MatrixGroups
open MvPolynomial
open TernaryPeriodPolynomials.Argument.IntegralReduction
open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument.EisensteinClass TernaryPeriodPolynomials.Argument.SeedC3S4c
  TernaryPeriodPolynomials.Argument.EisensteinDual TernaryPeriodPolynomials.Argument.GammaNFaces

noncomputable section
namespace TernaryPeriodPolynomials.Argument.FormClassK

variable (N : ℕ) [NeZero N] (k : SL(3, ℤ)) (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))

/-- The coefficient of the `E`-valued integrand. -/
def FzE (b : Bool) (y : Fin 5 → ℝ) (i j : Fin 5) (m : Fin 3 →₀ ℕ) (z : (FiniteAdeles × FiniteAdeles) × (Fin 2 → ℝ)) : ℂ :=
  (cxP b (adelicSection N n (hfun f) (gReal z.2) (gFin z.1 * kInvFin k) y i j)).coeff m

theorem FzE_eq_zero_of_not (b : Bool) (y : Fin 5 → ℝ) (i j : Fin 5) (m : Fin 3 →₀ ℕ) (σ : FiniteAdeles × FiniteAdeles)
    (w : Fin 2 → ℝ) (hd : ¬∃ π κ, IsDecomp N (gFin σ * kInvFin k) π κ) : FzE N k n f b y i j m (σ, w) = 0 := by
  unfold FzE
  simp [adelicSection_of_not N n _ (gReal w) hd]

/-- **On the cell of the free orbit `o` the coefficient is `cx b (PsiCoefQ)`.** -/
theorem FzE_on_piece (hN : 3 ≤ N) (b : Bool) {y : Fin 5 → ℝ} (hy : y ∈ Omega) (i j : Fin 5) (m : Fin 3 →₀ ℕ)
    (o : FreeOrbK N k) {σ : FiniteAdeles × FiniteAdeles} (hσ : σ ∈ pieceFinK N k o) (w : Fin 2 → ℝ) :
    FzE N k n f b y i j m (σ, w) = cx b (PsiCoefQ N k n f y i j m (orbCosetK N k o) (shiftV (orbPtK N k o) w)) := by
  set c := orbCosetK N k o with hc
  set A : SL(3, ℤ) := k * (Quotient.out c).1 with hA
  have hr : orbPtK N k o = slRowPt A := ptCk_out N k c
  have hAN : A * k⁻¹ ∈ gammaN N := by
    have := conj_mem_gammaN N k _ (Quotient.out c).2
    simpa [hA] using this
  have hA0 : (A : Matrix (Fin 3) (Fin 3) ℤ) 2 0 ≠ 0 := (cuspRow_ne_zero_iffK N k c).1 (orbCosetK_r0 N k o)
  set a : FiniteAdeles × FiniteAdeles :=
    (algebraMap ℚ FiniteAdeles (slRowPt A).1, algebraMap ℚ FiniteAdeles (slRowPt A).2) with ha
  have h1 : σ.1 - a.1 ∈ latSet N := by
    have := (mem_latCoset N).1 hσ.1
    rwa [hr] at this
  have h2 : σ.2 - a.2 ∈ latSet N := by
    have := (mem_latCoset N).1 hσ.2
    rwa [hr] at this
  have hσe : σ = a + (σ - a) := by abel
  have e1 := adelicSection_gFin_add_latK N hN n f k w a (σ - a) h1 h2 hy i j
  rw [← hσe] at e1
  unfold FzE PsiCoefQ
  simp only
  rw [e1, adelicSection_gFin_rational_K N hN n f k A hAN hA0 w hy i j, coeff_cxP, hr, hA, realMat_mul]

/-- The summand of the orbit sum for a free orbit. -/
abbrev psiO (y : Fin 5 → ℝ) (i j : Fin 5) (m : Fin 3 →₀ ℕ) (o : FreeOrbK N k) : (Fin 2 → ℝ) → ℂ :=
  PsiCoefQ N k n f y i j m (orbCosetK N k o)

theorem psiO_data (hn : 4 ≤ n) {y : Fin 5 → ℝ} (hy : y ∈ Omega) (i j : Fin 5) (m : Fin 3 →₀ ℕ) :
    (∀ ℓ c v, PsiCoefQ N k n f y i j m ((qActK N k).act ℓ c) v = PsiCoefQ N k n f y i j m c ((N : ℝ) • intVec ℓ + v)) ∧
    (∀ c, Continuous (PsiCoefQ N k n f y i j m c)) ∧
    ∀ R : ℝ, ∃ B : Ck N k → ℝ, Summable B ∧ ∀ c v, (∀ l, |v l| ≤ R) → ‖PsiCoefQ N k n f y i j m c v‖ ≤ B c := by
  obtain ⟨hc, hb⟩ := PsiCoefQ_continuous_bound N k n f hn hy i j m
  exact ⟨fun ℓ c v => PsiCoefQ_latQ N k n f hy i j m ℓ c v, hc, hb⟩

theorem psiO_integrable (hn : 4 ≤ n) {y : Fin 5 → ℝ} (hy : y ∈ Omega) (i j : Fin 5) (m : Fin 3 →₀ ℕ) (o : FreeOrbK N k) :
    Integrable (psiO N k n f y i j m o) := by
  obtain ⟨h1, hc, hb⟩ := psiO_data N k n f hn hy i j m
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have h := QAct.orbit_integrable (qActK N k) (fun c w => PsiCoefQ N k n f y i j m c w) h1 hc hb o.1 o.2
  have := h.comp_smul (inv_ne_zero hN)
  have e : psiO N k n f y i j m o = fun v => PsiCoefQ N k n f y i j m (Quotient.out o.1) v := rfl
  rw [e]
  simpa [smul_smul, hN] using this

theorem psiO_norm_summable (hn : 4 ≤ n) {y : Fin 5 → ℝ} (hy : y ∈ Omega) (i j : Fin 5) (m : Fin 3 →₀ ℕ) :
    Summable fun o : FreeOrbK N k => ∫ v : Fin 2 → ℝ, ‖psiO N k n f y i j m o ((N : ℝ) • v)‖ := by
  obtain ⟨h1, hc, hb⟩ := psiO_data N k n f hn hy i j m
  have h := QAct.orbit_summable (qActK N k) (fun c w => ((‖PsiCoefQ N k n f y i j m c w‖ : ℝ) : ℂ))
    (fun ℓ c v => by simp only [h1 ℓ c v])
    (fun c => Complex.continuous_ofReal.comp (continuous_norm.comp (hc c)))
    (fun R => by
      obtain ⟨B, hBs, hBb⟩ := hb R
      exact ⟨B, hBs, fun c v hv => by simpa using hBb c v hv⟩)
  have e : ∀ o : FreeOrbK N k, ∫ v : Fin 2 → ℝ,
      (((‖PsiCoefQ N k n f y i j m (Quotient.out o.1) ((N : ℝ) • v)‖ : ℝ)) : ℂ) =
      ((∫ v : Fin 2 → ℝ, ‖psiO N k n f y i j m o ((N : ℝ) • v)‖ : ℝ) : ℂ) := fun o => integral_ofReal
  simp_rw [e] at h
  exact Complex.summable_ofReal.1 h

theorem integral_psiO (y : Fin 5 → ℝ) (i j : Fin 5) (m : Fin 3 →₀ ℕ) (o : FreeOrbK N k) :
    ∫ v : Fin 2 → ℝ, psiO N k n f y i j m o ((N : ℝ) • v) = ((N : ℂ) ^ 2)⁻¹ * ∫ v, psiO N k n f y i j m o v :=
  integral_comp_smul_N N _

theorem integral_norm_psiO (y : Fin 5 → ℝ) (i j : Fin 5) (m : Fin 3 →₀ ℕ) (o : FreeOrbK N k) :
    ∫ v : Fin 2 → ℝ, ‖psiO N k n f y i j m o ((N : ℝ) • v)‖ =
      ((N : ℝ) ^ 2)⁻¹ * ∫ v, ‖psiO N k n f y i j m o v‖ := by
  have := integral_comp_smul_N N (fun v => (((‖psiO N k n f y i j m o v‖ : ℝ)) : ℂ))
  simp_rw [integral_complex_ofReal] at this
  apply Complex.ofReal_injective
  simpa using this

end TernaryPeriodPolynomials.Argument.FormClassK
