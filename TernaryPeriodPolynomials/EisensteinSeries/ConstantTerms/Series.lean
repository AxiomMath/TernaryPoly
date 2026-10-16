module

public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.TermJets
public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.Domination
public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.LocalTsum
public import Mathlib.NumberTheory.ModularForms.Bounds

@[expose] public section


/-!
# The series `ar:eq:Eseries` of Appendix C.3 and normal convergence of every derivative

`seriesCoeff Γ n f i j m x` is the `m`-th coefficient of the `(i, j)` component at the point `x ∈ Ω`
of `∑_{γ ∈ Γ_P \ Γ} ρ(γ)⁻¹ γ^* ω_h` for the cusp form `f` of weight `n + 3` and `h = f ∘ ofComplex`.
`exists_summable_jet_bound`: for every compact `K ⊂ Ω` and every order `N`, the `N`-th iterated
derivatives of the terms are dominated, uniformly on `K`, by a summable function on `Γ_P \ Γ`.
`seriesCoeff_smooth`: the sum is `C^∞` on `Ω` and may be differentiated termwise.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergenceC4

open scoped ContDiff
open Matrix MvPolynomial

/-! ### The series: terms, smoothness, normal convergence of every derivative -/

theorem contDiffOn_term (n : ℕ) (h : ℂ → ℂ) (hd : DifferentiableOn ℂ h upperHalf)
    {g : Matrix (Fin 3) (Fin 3) ℝ} (hg : g.det = 1) (i j : Fin 5) (m : Fin 3 →₀ ℕ) :
    ContDiffOn ℝ ∞ (fun x => (summandPoly n h g x i j).coeff m) Omega := by
  intro q hq
  refine ContDiffAt.contDiffWithinAt ?_
  set z : Par := (matToFun (kFactor g q), q) with hzdef
  have hz1 : z.1 ∈ SOrth := kFactor_mem_SOrth hg hq
  have hz : GoodPar z := ⟨hz1.2, hq⟩
  have hq'' := planeAct_mem hg hq
  have hev : (fun x => (summandPoly n h g x i j).coeff m) =ᶠ[nhds q]
      (fun x => slashTwisted (n + 3) (planeA (planeAct g q)) h (uTau z x) * uTheta i j z x *
        uPoly n m z x) :=
    Filter.eventuallyEq_of_mem (isOpen_Omega.mem_nhds hq) fun x hx =>
      coeff_frozen_eq n h hg hq hx i j m
  refine ContDiffAt.congr_of_eventuallyEq ?_ hev
  have hmaps : Set.MapsTo (uTau z) Omega upperHalf := by
    intro x hx
    have := (Psi_mem hz1 hq hx).1
    show 0 < (seedTau (Psi z x)).im
    simpa [seedTau] using this
  have hτ : ContDiffAt ℝ ∞ (uTau z) q :=
    (contDiffOn_of_family hV_uTau hz).contDiffAt (isOpen_Omega.mem_nhds hq)
  have hA : ContDiffAt ℝ ∞ (slashTwisted (n + 3) (planeA (planeAct g q)) h) (uTau z q) :=
    (contDiffOn_hA n hd hq'').contDiffAt (isOpen_upperHalf.mem_nhds (hmaps hq))
  exact ((hA.comp q hτ).mul
    ((contDiffOn_of_family (hV_uTheta i j) hz).contDiffAt (isOpen_Omega.mem_nhds hq))).mul
    ((contDiffOn_of_family (hV_uPoly n m) hz).contDiffAt (isOpen_Omega.mem_nhds hq))

section SeriesDef

open UpperHalfPlane ModularForm
open scoped UpperHalfPlane

variable (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ))
  {F : Type*} [FunLike F ℍ ℂ] (Λ : Subgroup (GL (Fin 2) ℝ)) [Λ.HasDetOne] [Λ.IsArithmetic]
  (n : ℕ) [CuspFormClass F Λ ((n + 3 : ℕ) : ℤ)] (f : F)

/-- The extension `h = f ∘ ofComplex` of a cusp form to `ℂ`. -/
def hfun : ℂ → ℂ := fun z => f (ofComplex z)

include Λ n

omit [Λ.HasDetOne] [Λ.IsArithmetic] in
theorem hfun_differentiableOn : DifferentiableOn ℂ (hfun f) upperHalf := by
  have := UpperHalfPlane.mdifferentiable_iff.1 (CuspFormClass.holo (k := ((n + 3 : ℕ) : ℤ))
    (Γ := Λ) f)
  exact this

omit [Λ.HasDetOne] in
theorem hfun_bound : ∃ Ch : ℝ, ∀ τ : ℂ, 0 < τ.im →
    ‖hfun f τ‖ * τ.im ^ (((n : ℝ) + 3) / 2) ≤ Ch := by
  obtain ⟨Ch, hCh⟩ := CuspFormClass.exists_bound (k := ((n + 3 : ℕ) : ℤ)) f
  refine ⟨Ch, fun τ hτ => ?_⟩
  have h1 := hCh ⟨τ, hτ⟩
  have h2 : hfun f τ = f ⟨τ, hτ⟩ := by
    simp [hfun, ofComplex_apply_of_im_pos hτ]
  rw [h2]
  have hpos : 0 < (⟨τ, hτ⟩ : ℍ).im ^ ((((n + 3 : ℕ) : ℤ) : ℝ) / 2) :=
    Real.rpow_pos_of_pos (by simpa using hτ) _
  have h3 : ((((n + 3 : ℕ) : ℤ) : ℝ) / 2) = ((n : ℝ) + 3) / 2 := by push_cast; ring
  rw [h3] at h1 hpos
  have : ‖f ⟨τ, hτ⟩‖ * (⟨τ, hτ⟩ : ℍ).im ^ (((n : ℝ) + 3) / 2) ≤ Ch := by
    calc _ ≤ Ch / (⟨τ, hτ⟩ : ℍ).im ^ (((n : ℝ) + 3) / 2) *
          (⟨τ, hτ⟩ : ℍ).im ^ (((n : ℝ) + 3) / 2) := mul_le_mul_of_nonneg_right h1 hpos.le
      _ = Ch := div_mul_cancel₀ _ hpos.ne'
  simpa using this

/-- The term of the series attached to a coset (through a chosen representative):
the `m`-th coefficient of the `(i, j)` component of `ρ(γ)⁻¹ γ^* ω_h`. -/
def termFun (c : PlaneCoset Γ) (i j : Fin 5) (m : Fin 3 →₀ ℕ) : (Fin 5 → ℝ) → ℂ :=
  fun x => (summandPoly n (hfun f) (realMat (Quotient.out c).1) x i j).coeff m

/-- The coefficients of the series `ar:eq:Eseries`. -/
def seriesCoeff (i j : Fin 5) (m : Fin 3 →₀ ℕ) (x : Fin 5 → ℝ) : ℂ :=
  ∑' c : PlaneCoset Γ, termFun Γ n f c i j m x

omit [Λ.HasDetOne] [Λ.IsArithmetic] in
theorem contDiffOn_termFun (c : PlaneCoset Γ) (i j : Fin 5) (m : Fin 3 →₀ ℕ) :
    ContDiffOn ℝ ∞ (termFun Γ n f c i j m) Omega :=
  contDiffOn_term n (hfun f) (hfun_differentiableOn Λ n f) (det_realMat _) i j m

omit [Λ.HasDetOne] in
/-- **Normal convergence of every derivative.** -/
theorem exists_summable_jet_bound (hn : 4 ≤ n) {K : Set (Fin 5 → ℝ)} (hK : IsCompact K)
    (hKΩ : K ⊆ Omega) (N : ℕ) (i j : Fin 5) (m : Fin 3 →₀ ℕ) :
    ∃ b : PlaneCoset Γ → ℝ, Summable b ∧ ∀ (c : PlaneCoset Γ), ∀ x ∈ K,
      ‖iteratedFDeriv ℝ N (termFun Γ n f c i j m) x‖ ≤ b c := by
  obtain ⟨Ch, hCh⟩ := hfun_bound Λ n f
  obtain ⟨C, hC⟩ := term_jet_bound n (hfun f) Ch hCh (hfun_differentiableOn Λ n f) hK hKΩ N i j m
  obtain ⟨b, hbs, hb⟩ := exists_summable_dominating Γ n hn hK hKΩ
    (fun γ q => ‖iteratedFDeriv ℝ N (fun x =>
      (summandPoly n (hfun f) (realMat γ.1) x i j).coeff m) q‖) C
    (fun γ q hq => hC _ (det_realMat γ.1) q hq)
  refine ⟨b, hbs, fun c x hx => ?_⟩
  have := hb (Quotient.out c) x hx
  rwa [Quotient.out_eq] at this

omit [Λ.HasDetOne] in
/-- The series of coefficients is `C^∞` on `Ω` and may be differentiated termwise. -/
theorem seriesCoeff_smooth (hn : 4 ≤ n) (i j : Fin 5) (m : Fin 3 →₀ ℕ) :
    ContDiffOn ℝ ∞ (seriesCoeff Γ n f i j m) Omega ∧
      ∀ (k : ℕ), ∀ x ∈ Omega, iteratedFDeriv ℝ k (seriesCoeff Γ n f i j m) x =
        ∑' c : PlaneCoset Γ, iteratedFDeriv ℝ k (termFun Γ n f c i j m) x :=
  contDiffOn_tsum_local isOpen_Omega (fun c => termFun Γ n f c i j m)
    (fun c => contDiffOn_termFun Γ Λ n f c i j m)
    (fun _K hK hKΩ k => exists_summable_jet_bound Γ Λ n f hn hK hKΩ k i j m)

end SeriesDef

end TernaryPeriodPolynomials.Argument.ConvergenceC4
