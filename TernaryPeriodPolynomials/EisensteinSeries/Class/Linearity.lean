module

public import TernaryPeriodPolynomials.EisensteinSeries.EisensteinClass

@[expose] public section


/-!
# Linearity of the Eisenstein series `𝓔_P(ω_h)` and of its class in the cusp form

Paper: Proposition C.4
(`ar:prop:convergence`), the series `ar:eq:Eseries`, and the class of
`𝓔_P(ω_h)` in `H²(Γ, E_n)`.

The series is a sum over `Γ_P\Γ` of terms depending linearly on the cusp form `f` (through the seed
`h(τ)𝓑ⁿ β ∧ dτ` and `summandPoly`), and `ZigZag.deRhamClass` is linear. The statements below give
additivity and homogeneity of the series at points of the chart `Ω`, of the closed form
`planeEisensteinInv`, of its class `eisensteinClass` (real scalars), of the complexified class, and the
linear map `eisensteinClassLinear : CuspForm Λ k →ₗ[ℝ] H²(Γ, E_n)`; the Γ(N) versions are corollaries.

Formalized by Claude Haiku 5.5.
-/

open MvPolynomial UpperHalfPlane ModularForm
open scoped UpperHalfPlane MatrixGroups ContDiff

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.ConvergenceC4
  TernaryPeriodPolynomials.Argument.Statements.ConvergenceC4
  TernaryPeriodPolynomials.Argument.Statements.EisensteinClass
open TernaryPeriodPolynomials.Argument.SeedC3 TernaryPoly.SmoothLocalDeRham

/-! ### Linearity of the summands in the seed function -/

theorem seedForm_add (n : ℕ) (h₁ h₂ : ℂ → ℂ) (p : Fin 5 → ℝ) (a b : Fin 5) :
    seedForm n (fun z => h₁ z + h₂ z) p a b = seedForm n h₁ p a b + seedForm n h₂ p a b := by
  simp only [seedForm, add_mul, map_add]

theorem seedForm_smul (n : ℕ) (c : ℂ) (h : ℂ → ℂ) :
    seedForm n (fun z => c * h z) = fun p a b => MvPolynomial.C c * seedForm n h p a b := by
  funext p a b
  simp only [seedForm, map_mul]
  ring

theorem formPullback_add (Φ : (Fin 5 → ℝ) → (Fin 5 → ℝ))
    (W₁ W₂ : (Fin 5 → ℝ) → Fin 5 → Fin 5 → MvPolynomial (Fin 3) ℂ) (p : Fin 5 → ℝ) (i j : Fin 5) :
    formPullback Φ (fun y a b => W₁ y a b + W₂ y a b) p i j =
      formPullback Φ W₁ p i j + formPullback Φ W₂ p i j := by
  simp only [formPullback, mul_add, Finset.sum_add_distrib]

theorem formPullback_smul (Φ : (Fin 5 → ℝ) → (Fin 5 → ℝ)) (c : ℂ)
    (W : (Fin 5 → ℝ) → Fin 5 → Fin 5 → MvPolynomial (Fin 3) ℂ) (p : Fin 5 → ℝ) (i j : Fin 5) :
    formPullback Φ (fun y a b => MvPolynomial.C c * W y a b) p i j =
      MvPolynomial.C c * formPullback Φ W p i j := by
  unfold formPullback
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

theorem rho_add_poly' (g : Matrix (Fin 3) (Fin 3) ℝ) (p q : MvPolynomial (Fin 3) ℂ) :
    SeedC3.rho g (p + q) = SeedC3.rho g p + SeedC3.rho g q := by
  simp only [SeedC3.rho, map_add, mul_add]

theorem summandPoly_add (n : ℕ) (h₁ h₂ : ℂ → ℂ) (g : Matrix (Fin 3) (Fin 3) ℝ)
    (q : Fin 5 → ℝ) (i j : Fin 5) :
    summandPoly n (fun z => h₁ z + h₂ z) g q i j =
      summandPoly n h₁ g q i j + summandPoly n h₂ g q i j := by
  unfold summandPoly
  have hs : seedForm n (fun z => h₁ z + h₂ z) =
      fun p a b => seedForm n h₁ p a b + seedForm n h₂ p a b :=
    funext fun p => funext fun a => funext fun b => seedForm_add n h₁ h₂ p a b
  rw [hs, formPullback_add, rho_add_poly']

theorem summandPoly_smul (n : ℕ) (c : ℂ) (h : ℂ → ℂ) (g : Matrix (Fin 3) (Fin 3) ℝ)
    (q : Fin 5 → ℝ) (i j : Fin 5) :
    summandPoly n (fun z => c * h z) g q i j = MvPolynomial.C c * summandPoly n h g q i j := by
  unfold summandPoly
  rw [seedForm_smul, formPullback_smul, ConvergenceC4.rho_C_mul]

/-! ### Linearity of the terms and of the series in the cusp form -/

section Series

variable (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ)) (Λ : Subgroup (GL (Fin 2) ℝ))
  (n : ℕ)

theorem hfun_add (f g : CuspForm Λ ((n + 3 : ℕ) : ℤ)) :
    hfun (f + g) = fun z => hfun f z + hfun g z := by
  funext z
  simp [hfun]

theorem hfun_smul [Λ.HasDetOne] (c : ℂ) (f : CuspForm Λ ((n + 3 : ℕ) : ℤ)) :
    hfun (c • f) = fun z => c * hfun f z := by
  funext z
  simp [hfun]

theorem termFun_add (c : PlaneCoset Γ) (a b : Fin 5) (m : Fin 3 →₀ ℕ) (x : Fin 5 → ℝ)
    (f g : CuspForm Λ ((n + 3 : ℕ) : ℤ)) :
    termFun Γ n (f + g) c a b m x = termFun Γ n f c a b m x + termFun Γ n g c a b m x := by
  unfold termFun
  rw [hfun_add, summandPoly_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]

theorem termFun_smul [Λ.HasDetOne] (c : PlaneCoset Γ) (a b : Fin 5) (m : Fin 3 →₀ ℕ)
    (x : Fin 5 → ℝ) (s : ℂ) (f : CuspForm Λ ((n + 3 : ℕ) : ℤ)) :
    termFun Γ n (s • f) c a b m x = s * termFun Γ n f c a b m x := by
  unfold termFun
  rw [hfun_smul, summandPoly_smul, MvPolynomial.coeff_C_mul]

/-- Summability of the terms of `𝓔_P(ω_h)` at a point of the chart, from normal convergence. -/
theorem summable_termFun [Λ.HasDetOne] [Λ.IsArithmetic] (hn : 4 ≤ n) {y : Fin 5 → ℝ}
    (hy : y ∈ Omega) (f : CuspForm Λ ((n + 3 : ℕ) : ℤ)) (a b : Fin 5) (m : Fin 3 →₀ ℕ) :
    Summable fun c : PlaneCoset Γ => termFun Γ n f c a b m y := by
  obtain ⟨β, hβ, hb⟩ := normal_convergence Γ Λ n f hn isCompact_singleton
    (Set.singleton_subset_iff.2 hy) 0
  refine Summable.of_norm_bounded hβ fun c => ?_
  have h := hb c y (Set.mem_singleton y) a b m
  rwa [norm_iteratedFDeriv_zero] at h

/-- **Additivity of the Eisenstein series in the cusp form** (Proposition C.4). -/
theorem planeEisenstein_add [Λ.HasDetOne] [Λ.IsArithmetic] (hn : 4 ≤ n) {y : Fin 5 → ℝ}
    (hy : y ∈ Omega) (a b : Fin 5) (f g : CuspForm Λ ((n + 3 : ℕ) : ℤ)) :
    planeEisenstein Γ n (f + g) y a b = planeEisenstein Γ n f y a b + planeEisenstein Γ n g y a b := by
  apply Subtype.ext
  apply MvPolynomial.ext
  intro m
  rw [Submodule.coe_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_planeEisenstein, coeff_planeEisenstein,
    coeff_planeEisenstein, ← Summable.tsum_add (summable_termFun Γ Λ n hn hy f a b m)
      (summable_termFun Γ Λ n hn hy g a b m)]
  congr 1
  funext c
  exact termFun_add Γ Λ n c a b m y f g

/-- **Homogeneity of the Eisenstein series in the cusp form**: complex scalars pass
through the sum at every point (`tsum_mul_left`, no convergence needed). -/
theorem planeEisenstein_smul [Λ.HasDetOne] (s : ℂ) (y : Fin 5 → ℝ) (a b : Fin 5)
    (f : CuspForm Λ ((n + 3 : ℕ) : ℤ)) :
    planeEisenstein Γ n (s • f) y a b = s • planeEisenstein Γ n f y a b := by
  apply Subtype.ext
  apply MvPolynomial.ext
  intro m
  rw [Submodule.coe_smul, MvPolynomial.coeff_smul, coeff_planeEisenstein, coeff_planeEisenstein,
    smul_eq_mul, ← tsum_mul_left]
  congr 1
  funext c
  exact termFun_smul Γ Λ n c a b m y s f

end Series

/-! ### Linearity of the closed form `planeEisensteinInv` -/

section Form

variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ)} {n : ℕ}

/-- Additivity of the chart form of a family of components on `Ω`. -/
theorem InvComponents.toInv_add (W₁ W₂ W₃ : InvComponents Γ n)
    (h : ∀ y ∈ Omega, ∀ a b : Fin 5, W₃.comp y a b = W₁.comp y a b + W₂.comp y a b) :
    W₃.toInv = W₁.toInv + W₂.toInv := by
  apply Subtype.ext
  rw [Submodule.coe_add, InvComponents.toInv_val, InvComponents.toInv_val,
    InvComponents.toInv_val]
  apply Form.ext
  intro x hx
  rw [AddMemClass.coe_add, Pi.add_apply, W₃.form_apply hx, W₁.form_apply hx, W₂.form_apply hx]
  unfold InvComponents.raw
  rw [← map_add]
  congr 1
  funext a b
  exact h x hx a b

/-- Homogeneity of the chart form of a family of components on `Ω`. -/
theorem InvComponents.toInv_smul (r : ℝ) (W₁ W₂ : InvComponents Γ n)
    (h : ∀ y ∈ Omega, ∀ a b : Fin 5, W₂.comp y a b = r • W₁.comp y a b) :
    W₂.toInv = r • W₁.toInv := by
  apply Subtype.ext
  rw [Submodule.coe_smul, InvComponents.toInv_val, InvComponents.toInv_val]
  apply Form.ext
  intro x hx
  rw [SetLike.val_smul, Pi.smul_apply, W₂.form_apply hx, W₁.form_apply hx]
  unfold InvComponents.raw
  rw [← map_smul]
  congr 1
  funext a b
  exact h x hx a b

variable (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ)) (Λ : Subgroup (GL (Fin 2) ℝ))
  (n : ℕ)

/-- Additivity of the closed form `𝓔_P(ω_h)` (OB3) in the cusp form. -/
theorem planeEisensteinInv_add [Λ.HasDetOne] [Λ.IsArithmetic] (hn : 4 ≤ n)
    (hLevi : LeviIn Γ Λ) (f g : CuspForm Λ ((n + 3 : ℕ) : ℤ)) :
    planeEisensteinInv Γ Λ n (f + g) hn hLevi =
      planeEisensteinInv Γ Λ n f hn hLevi + planeEisensteinInv Γ Λ n g hn hLevi := by
  unfold planeEisensteinInv
  apply InvComponents.toInv_add
  intro y hy a b
  show Coef.mk (planeEisenstein Γ n (f + g) y a b) =
    Coef.mk (planeEisenstein Γ n f y a b) + Coef.mk (planeEisenstein Γ n g y a b)
  rw [planeEisenstein_add Γ Λ n hn hy a b f g]
  rfl

/-- Real homogeneity of the closed form `𝓔_P(ω_h)` (OB3) in the cusp form: `Coef n` is a real form of
`E_n`, so the real scalar `r` acts as the complex scalar `(r : ℂ)`. -/
theorem planeEisensteinInv_smul [Λ.HasDetOne] [Λ.IsArithmetic] (hn : 4 ≤ n)
    (hLevi : LeviIn Γ Λ) (r : ℝ) (f : CuspForm Λ ((n + 3 : ℕ) : ℤ)) :
    planeEisensteinInv Γ Λ n ((r : ℂ) • f) hn hLevi =
      r • planeEisensteinInv Γ Λ n f hn hLevi := by
  unfold planeEisensteinInv
  apply InvComponents.toInv_smul
  intro y hy a b
  show Coef.mk (planeEisenstein Γ n ((r : ℂ) • f) y a b) =
    r • Coef.mk (planeEisenstein Γ n f y a b)
  rw [planeEisenstein_smul Γ Λ n (r : ℂ) y a b f]
  rw [← Complex.coe_smul]
  rfl

end Form

/-! ### Linearity of the class `𝓔_P(ω_h) ∈ H²(Γ, E_n)` -/

section Class

variable (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ)) (Λ : Subgroup (GL (Fin 2) ℝ))
  (n : ℕ)

/-- The real scalar action on a cusp form is the action of `(r : ℂ)`. -/
theorem realSmul_eq_coe_smul [Λ.HasDetOne] (r : ℝ) (f : CuspForm Λ ((n + 3 : ℕ) : ℤ)) :
    r • f = (r : ℂ) • f := by
  apply CuspForm.ext
  intro z
  simp [Complex.real_smul]

/-- **Additivity of the class of `𝓔_P(ω_h)`** in the cusp form. -/
theorem eisensteinClass_add [Λ.HasDetOne] [Λ.IsArithmetic] (hn : 4 ≤ n) (hLevi : LeviIn Γ Λ)
    (f g : CuspForm Λ ((n + 3 : ℕ) : ℤ)) :
    eisensteinClass Γ Λ n (f + g) hn hLevi =
      eisensteinClass Γ Λ n f hn hLevi + eisensteinClass Γ Λ n g hn hLevi := by
  unfold eisensteinClass
  rw [planeEisensteinInv_add Γ Λ n hn hLevi f g, map_add]

/-- **Real homogeneity of the class of `𝓔_P(ω_h)`** in the cusp form. -/
theorem eisensteinClass_smul [Λ.HasDetOne] [Λ.IsArithmetic] (hn : 4 ≤ n) (hLevi : LeviIn Γ Λ)
    (r : ℝ) (f : CuspForm Λ ((n + 3 : ℕ) : ℤ)) :
    eisensteinClass Γ Λ n ((r : ℂ) • f) hn hLevi = r • eisensteinClass Γ Λ n f hn hLevi := by
  unfold eisensteinClass
  rw [planeEisensteinInv_smul Γ Λ n hn hLevi r f, map_smul]

/-- **The class of `𝓔_P(ω_h)` as a real-linear map of the cusp form**: the map
`f ↦ [𝓔_P(ω_h)] ∈ H²(Γ, E_n)` is `ℝ`-linear. -/
def eisensteinClassLinear [Λ.HasDetOne] [Λ.IsArithmetic] (hn : 4 ≤ n) (hLevi : LeviIn Γ Λ) :
    CuspForm Λ ((n + 3 : ℕ) : ℤ) →ₗ[ℝ] groupCohomology.H2 (Rep.of (gammaRho Γ n)) where
  toFun f := eisensteinClass Γ Λ n f hn hLevi
  map_add' f g := eisensteinClass_add Γ Λ n hn hLevi f g
  map_smul' r f := by
    rw [RingHom.id_apply, realSmul_eq_coe_smul Λ n r f, eisensteinClass_smul Γ Λ n hn hLevi r f]

/-- The complexified class of `𝓔_P(ω_h)` is additive in the cusp form. -/
theorem eisensteinClassC_add [Λ.HasDetOne] [Λ.IsArithmetic] (hn : 4 ≤ n) (hLevi : LeviIn Γ Λ)
    (f g : CuspForm Λ ((n + 3 : ℕ) : ℤ)) :
    eisensteinClassC Γ Λ n (f + g) hn hLevi =
      eisensteinClassC Γ Λ n f hn hLevi + eisensteinClassC Γ Λ n g hn hLevi := by
  unfold eisensteinClassC
  rw [eisensteinClass_add Γ Λ n hn hLevi f g, map_add]

/-- The complexified class of `𝓔_P(ω_h)` is real-homogeneous in the cusp form. -/
theorem eisensteinClassC_smul [Λ.HasDetOne] [Λ.IsArithmetic] (hn : 4 ≤ n) (hLevi : LeviIn Γ Λ)
    (r : ℝ) (f : CuspForm Λ ((n + 3 : ℕ) : ℤ)) :
    eisensteinClassC Γ Λ n ((r : ℂ) • f) hn hLevi = r • eisensteinClassC Γ Λ n f hn hLevi := by
  unfold eisensteinClassC
  rw [eisensteinClass_smul Γ Λ n hn hLevi r f, map_smul]

/-! ### The paper's group `Γ(N)` -/

variable (N : ℕ) [NeZero N]

/-- Additivity of the class of `𝓔_P(ω_h) ∈ H²(Γ(N), E_n)`. -/
theorem eisensteinClass_gammaN_add (hn : 4 ≤ n) (f g : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) :
    eisensteinClass_gammaN N n (f + g) hn =
      eisensteinClass_gammaN N n f hn + eisensteinClass_gammaN N n g hn :=
  eisensteinClass_add (gammaN N) (leviGroup N) n hn (leviIn_gammaN N) f g

/-- Real homogeneity of the class of `𝓔_P(ω_h) ∈ H²(Γ(N), E_n)`. -/
theorem eisensteinClass_gammaN_smul (hn : 4 ≤ n) (r : ℝ)
    (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) :
    eisensteinClass_gammaN N n ((r : ℂ) • f) hn = r • eisensteinClass_gammaN N n f hn :=
  eisensteinClass_smul (gammaN N) (leviGroup N) n hn (leviIn_gammaN N) r f

/-- The class of `𝓔_P(ω_h) ∈ H²(Γ(N), E_n)` as a real-linear map of the cusp form. -/
def eisensteinClassLinear_gammaN (hn : 4 ≤ n) :
    CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ) →ₗ[ℝ] groupCohomology.H2 (Rep.of (gammaRho (gammaN N) n)) :=
  eisensteinClassLinear (gammaN N) (leviGroup N) n hn (leviIn_gammaN N)

/-- Additivity of the complexified class of `𝓔_P(ω_h)` in `H²(Γ(N), E_n)_ℂ`. -/
theorem eisensteinClassC_gammaN_add (hn : 4 ≤ n) (f g : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) :
    eisensteinClassC_gammaN N n (f + g) hn =
      eisensteinClassC_gammaN N n f hn + eisensteinClassC_gammaN N n g hn :=
  eisensteinClassC_add (gammaN N) (leviGroup N) n hn (leviIn_gammaN N) f g

/-- Real homogeneity of the complexified class of `𝓔_P(ω_h)` in `H²(Γ(N), E_n)_ℂ`. -/
theorem eisensteinClassC_gammaN_smul (hn : 4 ≤ n) (r : ℝ)
    (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) :
    eisensteinClassC_gammaN N n ((r : ℂ) • f) hn = r • eisensteinClassC_gammaN N n f hn :=
  eisensteinClassC_smul (gammaN N) (leviGroup N) n hn (leviIn_gammaN N) r f

end Class

end TernaryPeriodPolynomials.Argument.EisensteinClass
