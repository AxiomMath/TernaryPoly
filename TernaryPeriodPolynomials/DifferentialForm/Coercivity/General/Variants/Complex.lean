module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Main

@[expose] public section


/-!
# General coercivity: complex coefficients

A form with values in the complexification `Sym^n ℂ³ = Coefficients n ⊗ ℂ` of the real coefficient
bundle is a pair `(α, β)` of real forms, `ω = α + iβ`.  The flat connection and the exterior
derivative of the complexified bundle act componentwise, the Hermitian metric of `E ⊗ ℂ` is
`h(u + iv, u + iv) = |u|² + |v|²`, so the `L²` norm squares add, and the formal adjoint of the
complexified exterior derivative is the componentwise adjoint.  This pair model is the intermediate
step of `Variants/ComplexForms`, where forms valued in the genuine space of complex homogeneous
polynomials `ComplexCoefficients n` are identified with such pairs (`cxEquiv`, built on
`reImEquiv` of `Variants/ComplexCoefficients`, which is compatible with the substitution action and the
Hermitian Fischer norm).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open TernaryPoly.SymmetricSpacePositive

variable {Γ : Subgroup RealGL} {n k : ℕ}

/-- Complex-coefficient forms: the real and imaginary parts. -/
abbrev CFormC (Γ : Subgroup RealGL) (n k : ℕ) := CForm Γ n k × CForm Γ n k

/-- The Hermitian `L²` pairing of complex-coefficient forms,
`⟨α + iβ, α' + iβ'⟩ = ⟨α,α'⟩ + ⟨β,β'⟩` (real part of the Hermitian product). -/
def l2FormC (Γ : Subgroup RealGL) (n k : ℕ) : LinearMap.BilinForm ℝ (CFormC Γ n k) :=
  (l2Form Γ n k).compl₁₂ (LinearMap.fst ℝ _ _) (LinearMap.fst ℝ _ _) +
    (l2Form Γ n k).compl₁₂ (LinearMap.snd ℝ _ _) (LinearMap.snd ℝ _ _)

theorem l2FormC_apply (a b : CFormC Γ n k) :
    l2FormC Γ n k a b = l2Form Γ n k a.1 b.1 + l2Form Γ n k a.2 b.2 := rfl

/-- Squared `L²` norm of a complex-coefficient form. -/
def normSqC (a : CFormC Γ n k) : ℝ := l2FormC Γ n k a a

theorem normSqC_eq (a : CFormC Γ n k) : normSqC a = normSq a.1 + normSq a.2 := rfl

/-- The complexified exterior derivative. -/
def dC (Γ : Subgroup RealGL) (n k : ℕ) : CFormC Γ n k →ₗ[ℝ] CFormC Γ n (k + 1) :=
  LinearMap.prodMap (CForm.d Γ n k) (CForm.d Γ n k)

/-- The complexified local formal adjoint. -/
def deltaC (Γ : Subgroup RealGL) (n k : ℕ) : CFormC Γ n (k + 1) →ₗ[ℝ] CFormC Γ n k :=
  LinearMap.prodMap (CForm.delta Γ n k) (CForm.delta Γ n k)

/-- `e` is a formal adjoint of the complexified `d` at `b` for the Hermitian `L²` pairing. -/
def IsFormalAdjointC (Γ : Subgroup RealGL) (n k : ℕ) (b : CFormC Γ n (k + 1))
    (e : CFormC Γ n k) : Prop :=
  ∀ a : CFormC Γ n k, l2FormC Γ n (k + 1) (dC Γ n k a) b = l2FormC Γ n k a e

theorem l2FormC_d (a : CFormC Γ n k) (b : CFormC Γ n (k + 1)) :
    l2FormC Γ n (k + 1) (dC Γ n k a) b =
      l2Form Γ n (k + 1) (CForm.d Γ n k a.1) b.1 + l2Form Γ n (k + 1) (CForm.d Γ n k a.2) b.2 :=
  rfl

theorem l2FormC_delta (a : CFormC Γ n k) (e : CFormC Γ n k) :
    l2FormC Γ n k a e = l2Form Γ n k a.1 e.1 + l2Form Γ n k a.2 e.2 := rfl

theorem deltaC_fst (b : CFormC Γ n (k + 1)) : (deltaC Γ n k b).1 = CForm.delta Γ n k b.1 := rfl

theorem deltaC_snd (b : CFormC Γ n (k + 1)) : (deltaC Γ n k b).2 = CForm.delta Γ n k b.2 := rfl

theorem Admissible.deltaC_isFormalAdjoint (h : Admissible Γ) (b : CFormC Γ n (k + 1)) :
    IsFormalAdjointC Γ n k b (deltaC Γ n k b) := fun a =>
  (l2FormC_d a b).trans ((congrArg₂ (· + ·) (h.l2Form_d a.1 b.1) (h.l2Form_d a.2 b.2)).trans
    (l2FormC_delta a (deltaC Γ n k b)).symm)

theorem l2Form_zero_left' (a : CForm Γ n k) : l2Form Γ n k (0 : CForm Γ n k) a = 0 :=
  LinearMap.map_zero₂ _ _

/-- The formal adjoint of the complexified exterior derivative is unique, hence `deltaC`. -/
theorem Admissible.deltaC_unique (h : Admissible Γ) (b : CFormC Γ n (k + 1)) (e : CFormC Γ n k)
    (he : IsFormalAdjointC Γ n k b e) : e = deltaC Γ n k b := by
  have z1 : CForm.d Γ n k (0 : CForm Γ n k) = 0 := map_zero _
  have h1 : IsFormalAdjoint Γ n k b.1 e.1 := by
    intro a
    have h0 : l2Form Γ n (k + 1) (CForm.d Γ n k a) b.1 +
        l2Form Γ n (k + 1) (CForm.d Γ n k 0) b.2 = l2Form Γ n k a e.1 + l2Form Γ n k 0 e.2 :=
      (l2FormC_d (a, 0) b).symm.trans ((he (a, 0)).trans (l2FormC_delta (a, 0) e))
    have z2 : l2Form Γ n (k + 1) (CForm.d Γ n k 0) b.2 = 0 := by
      rw [z1]
      exact l2Form_zero_left' _
    have z3 : l2Form Γ n k (0 : CForm Γ n k) e.2 = 0 := l2Form_zero_left' _
    linarith
  have h2 : IsFormalAdjoint Γ n k b.2 e.2 := by
    intro a
    have h0 : l2Form Γ n (k + 1) (CForm.d Γ n k 0) b.1 +
        l2Form Γ n (k + 1) (CForm.d Γ n k a) b.2 = l2Form Γ n k 0 e.1 + l2Form Γ n k a e.2 :=
      (l2FormC_d (0, a) b).symm.trans ((he (0, a)).trans (l2FormC_delta (0, a) e))
    have z2 : l2Form Γ n (k + 1) (CForm.d Γ n k 0) b.1 = 0 := by
      rw [z1]
      exact l2Form_zero_left' _
    have z3 : l2Form Γ n k (0 : CForm Γ n k) e.1 = 0 := l2Form_zero_left' _
    linarith
  exact Prod.ext (h.delta_unique _ _ h1) (h.delta_unique _ _ h2)

/-- **Proposition C.1, complex coefficients.**  The same constant as for real coefficients works
for forms with values in `Sym^n ℂ³` for every admissible group. -/
theorem general_coercivity_complex (n : ℕ) (hn : 0 < n) :
    ∃ c : ℝ, 0 < c ∧ ∀ Γ : Subgroup RealGL, Admissible Γ →
      (∀ a : CFormC Γ n 0, c * normSqC a ≤ normSqC (dC Γ n 0 a)) ∧
        ∀ (k : ℕ) (a : CFormC Γ n (k + 1)),
          c * normSqC a ≤ normSqC (deltaC Γ n k a) + normSqC (dC Γ n (k + 1) a) := by
  obtain ⟨c, hc, h⟩ := general_coercivity n hn
  refine ⟨c, hc, fun Γ hΓ => ⟨fun a => ?_, fun k a => ?_⟩⟩
  · have h1 := (h Γ hΓ).1 a.1
    have h2 := (h Γ hΓ).1 a.2
    simp only [normSqC_eq, dC, LinearMap.prodMap_apply]
    linarith
  · have h1 := (h Γ hΓ).2 k a.1
    have h2 := (h Γ hΓ).2 k a.2
    simp only [normSqC_eq, dC, deltaC, LinearMap.prodMap_apply]
    linarith

/-- Complex version for the principal congruence groups of level divisible by three. -/
theorem coercivity_complex_principal (n : ℕ) (hn : 0 < n) :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, 3 ∣ N → ∀ H : Subgroup RealGL, H ≤ principalReal N →
      (∀ a : CFormC H n 0, c * normSqC a ≤ normSqC (dC H n 0 a)) ∧
        ∀ (k : ℕ) (a : CFormC H n (k + 1)),
          c * normSqC a ≤ normSqC (deltaC H n k a) + normSqC (dC H n (k + 1) a) := by
  obtain ⟨c, hc, h⟩ := general_coercivity_complex n hn
  exact ⟨c, hc, fun N h3 H hH => h H ((admissible_principalReal h3).mono hH)⟩

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
