module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Linearity
public import TernaryPeriodPolynomials.EisensteinSeries.Class.CoefTwist
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Complexify

@[expose] public section


/-!
# Complex homogeneity and additivity of the class of the series in the cusp form

Paper: Proposition C.4,
the series and its class in `H²(Γ, E_n)`.

`Linearity.lean` proves additivity and REAL homogeneity at the standard cusp. Here the coefficient
intertwiner `cmulCLM c` (multiplication by an arbitrary complex `c`, a real-linear continuous
endomorphism of `E_n`, NOT an isometry, with no hypothesis on `c`) and `CoefTwist.deRhamClass_twist` give
complex homogeneity `[𝓔(c f)] = c [𝓔(f)]` of the complexified class (`eisensteinClassC_cmul`), and, at an
arbitrary cusp `D` with seed type `b`, `[𝓔_{D,b}(c f)] = cx b c · [𝓔_{D,b}(f)]`: complex-linear for the
holomorphic seed `b = false`, conjugate-linear for the antiholomorphic seed `b = true`
(`eisensteinAtClassC_cmul`); additivity at every cusp is `eisensteinAtClassC_add`.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory groupCohomology
open scoped ContDiff MatrixGroups
noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open ContinuousAlternatingMap TernaryPoly.SmoothCoveringDeRham
open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPoly.SmoothLocalDeRham TernaryPeriodPolynomials.Argument.Statements.EisensteinClass
  TernaryPeriodPolynomials.Argument.Statements.ConvergenceC4 TernaryPeriodPolynomials.Argument
  TernaryPeriodPolynomials.Argument.SeedC3.Psi

section Scalar

variable (n : ℕ)

/-- Multiplication by a complex scalar as a real-linear continuous endomorphism of `E_n`. -/
def cmulCLM (c : ℂ) : Coef n →L[ℝ] Coef n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun q => c • q
      map_add' := fun q r => smul_add c q r
      map_smul' := fun r q => by
        change c • ((r : ℝ) • q) = (r : ℝ) • (c • q)
        exact smul_comm c r q }

theorem cmulCLM_apply (c : ℂ) (q : Coef n) : cmulCLM n c q = c • q := rfl

theorem toPoly_cmulCLM (c : ℂ) (q : Coef n) :
    Coef.toPoly (cmulCLM n c q) = MvPolynomial.C c * Coef.toPoly q :=
  Coef.toPoly_smul c q

theorem intertwines_cmul_gammaRho (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ)) (c : ℂ) :
    Intertwines (cmulCLM n c) (gammaRho Γ n) (gammaRho Γ n) := by
  intro g v
  apply Coef.toPoly_injective
  rw [toPoly_gammaRho, toPoly_cmulCLM, toPoly_cmulCLM, toPoly_gammaRho, ConvergenceC4.rho_C_mul]

end Scalar

section Forms

variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ)} {n : ℕ}

/-- A coefficient endomorphism commutes with the packaging of components into an alternating form. -/
theorem coefficientFormMap_altRaw (T : Coef n →L[ℝ] Coef n) (c : Fin 5 → Fin 5 → Coef n)
    (hc : ∀ a b, c a b = -c b a) :
    coefficientFormMap T 2 (altRaw c) = altRaw (fun a b => T (c a b)) := by
  apply ext2
  intro i j
  rw [altRaw_basis_of_antisymm (fun a b => T (c a b))
    (fun a b => by rw [hc a b, map_neg]) i j]
  show T (altRaw c ![Pi.single i 1, Pi.single j 1]) = _
  rw [altRaw_basis_of_antisymm c hc i j]

/-- The chart form of a family of components that is a coefficient twist of another. -/
theorem InvComponents.toInv_twist (T : Coef n →L[ℝ] Coef n)
    (hT : Intertwines T (gammaRho Γ n) (gammaRho Γ n)) (W₁ W₂ : InvComponents Γ n)
    (h : ∀ y ∈ Omega, ∀ a b : Fin 5, W₂.comp y a b = T (W₁.comp y a b)) :
    W₂.toInv = twInv hT W₁.toInv := by
  apply Subtype.ext
  rw [twInv_coe, InvComponents.toInv_val, InvComponents.toInv_val]
  apply Form.ext
  intro x hx
  rw [ZigZag.twForm_apply, W₂.form_apply hx, W₁.form_apply hx]
  unfold InvComponents.raw
  rw [altCLM_apply, altCLM_apply, coefficientFormMap_altRaw T _ (W₁.anti x)]
  congr 1
  funext a b
  exact h x hx a b

end Forms

section ClassLevel

variable (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ)) (n : ℕ)

/-- **Complexification intertwines the twist by `c` with multiplication by `c`.** -/
theorem complexify_map_cmul (c : ℂ) (x : H2 (Rep.of (gammaRho Γ n))) :
    complexify Γ n ((groupCohomology.map (MonoidHom.id Γ)
      (twMor (intertwines_cmul_gammaRho n Γ c)) 2).hom x) = c • complexify Γ n x := by
  induction x using H2_induction_on with | _ c0 => ?_
  rw [groupCohomology.H2π_comp_map_apply, complexify_H2π, complexify_H2π, ← map_smul]
  congr 1

variable (Λ : Subgroup (GL (Fin 2) ℝ)) [Λ.HasDetOne] [Λ.IsArithmetic]

/-- **Complex homogeneity of the series as a closed form**: `𝓔_P(ω_{c f}) = c 𝓔_P(ω_f)` (twist by
multiplication by `c`). -/
theorem planeEisensteinInv_cmul (hn : 4 ≤ n) (hLevi : LeviIn Γ Λ) (c : ℂ)
    (f : CuspForm Λ ((n + 3 : ℕ) : ℤ)) :
    planeEisensteinInv Γ Λ n (c • f) hn hLevi =
      twInv (intertwines_cmul_gammaRho n Γ c) (planeEisensteinInv Γ Λ n f hn hLevi) := by
  unfold planeEisensteinInv
  apply InvComponents.toInv_twist
  intro y hy a b
  show Coef.mk (planeEisenstein Γ n (c • f) y a b) =
    cmulCLM n c (Coef.mk (planeEisenstein Γ n f y a b))
  rw [planeEisenstein_smul Γ Λ n c y a b f]
  rfl

/-- **Complex homogeneity of the complexified class of `𝓔_P(ω_f)` in the cusp form**. -/
theorem eisensteinClassC_cmul (hn : 4 ≤ n) (hLevi : LeviIn Γ Λ) (c : ℂ)
    (f : CuspForm Λ ((n + 3 : ℕ) : ℤ)) :
    eisensteinClassC Γ Λ n (c • f) hn hLevi = c • eisensteinClassC Γ Λ n f hn hLevi := by
  unfold eisensteinClassC eisensteinClass
  rw [planeEisensteinInv_cmul Γ n Λ hn hLevi c f,
    deRhamClass_twist convex_Omega Omega_nonempty (intertwines_cmul_gammaRho n Γ c)]
  exact complexify_map_cmul Γ n c _

/-- **Complex homogeneity for the paper's group `Γ(N)`.** -/
theorem eisensteinClassC_gammaN_cmul (N : ℕ) [NeZero N] (hn : 4 ≤ n) (c : ℂ)
    (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) :
    eisensteinClassC_gammaN N n (c • f) hn = c • eisensteinClassC_gammaN N n f hn :=
  eisensteinClassC_cmul (gammaN N) n (leviGroup N) hn (leviIn_gammaN N) c f

section Cusp

variable (b : Bool) (D : CuspData)

omit [Λ.IsArithmetic] in
theorem termFunK_smul (c : ℂ) (w : CuspCoset Γ D.r) (i j : Fin 5) (m : Fin 3 →₀ ℕ)
    (x : Fin 5 → ℝ) (f : CuspForm Λ ((n + 3 : ℕ) : ℤ)) :
    termFunK b D Γ n (c • f) w i j m x = cx b c * termFunK b D Γ n f w i j m x := by
  unfold termFunK
  rw [summandK_eq, summandK_eq, hfun_smul, summandPoly_smul]
  have : cxP b (MvPolynomial.C c * summandPoly n (hfun f) (D.a * realMat (Quotient.out w).1) x i j) =
      MvPolynomial.C (cx b c) * cxP b (summandPoly n (hfun f) (D.a * realMat (Quotient.out w).1)
        x i j) := by
    simp [cxP]
  rw [this, MvPolynomial.coeff_C_mul]

omit [Λ.IsArithmetic] in
/-- Complex (resp. conjugate-linear) homogeneity of the series at the cusp `D` in the cusp form. -/
theorem planeEisensteinAt_cmul (c : ℂ) (y : Fin 5 → ℝ) (a b' : Fin 5)
    (f : CuspForm Λ ((n + 3 : ℕ) : ℤ)) :
    planeEisensteinAt b D Γ n (c • f) y a b' = cx b c • planeEisensteinAt b D Γ n f y a b' := by
  apply Subtype.ext
  apply MvPolynomial.ext
  intro m
  rw [Submodule.coe_smul, MvPolynomial.coeff_smul, coeff_planeEisensteinAt,
    coeff_planeEisensteinAt, smul_eq_mul, ← tsum_mul_left]
  congr 1
  funext w
  exact termFunK_smul Γ n Λ b D c w a b' m y f

theorem planeEisensteinAtInv_cmul (hn : 4 ≤ n) (hLevi : LeviInCusp D Γ Λ) (c : ℂ)
    (f : CuspForm Λ ((n + 3 : ℕ) : ℤ)) :
    planeEisensteinAtInv b D Γ Λ n (c • f) hn hLevi =
      twInv (intertwines_cmul_gammaRho n Γ (cx b c)) (planeEisensteinAtInv b D Γ Λ n f hn hLevi) := by
  unfold planeEisensteinAtInv
  apply InvComponents.toInv_twist
  intro y hy a b'
  show Coef.mk (planeEisensteinAt b D Γ n (c • f) y a b') =
    cmulCLM n (cx b c) (Coef.mk (planeEisensteinAt b D Γ n f y a b'))
  rw [planeEisensteinAt_cmul Γ n Λ b D c y a b' f]
  rfl

/-- **The complexified class of the series at any cusp and seed type is `cx b`-linear in the cusp
form**: complex-linear for the holomorphic seed, conjugate-linear for the antiholomorphic seed. -/
theorem eisensteinAtClassC_cmul (hn : 4 ≤ n) (hLevi : LeviInCusp D Γ Λ) (c : ℂ)
    (f : CuspForm Λ ((n + 3 : ℕ) : ℤ)) :
    eisensteinAtClassC b D Γ Λ n (c • f) hn hLevi =
      cx b c • eisensteinAtClassC b D Γ Λ n f hn hLevi := by
  unfold eisensteinAtClassC eisensteinAtClass
  rw [planeEisensteinAtInv_cmul Γ n Λ b D hn hLevi c f,
    deRhamClass_twist convex_Omega Omega_nonempty (intertwines_cmul_gammaRho n Γ (cx b c))]
  exact complexify_map_cmul Γ n (cx b c) _

omit [Λ.HasDetOne] [Λ.IsArithmetic] in
/-- One term of the series at the cusp is additive in the cusp form. -/
theorem termFunK_add (w : CuspCoset Γ D.r) (i j : Fin 5) (m : Fin 3 →₀ ℕ)
    (x : Fin 5 → ℝ) (f g : CuspForm Λ ((n + 3 : ℕ) : ℤ)) :
    termFunK b D Γ n (f + g) w i j m x =
      termFunK b D Γ n f w i j m x + termFunK b D Γ n g w i j m x := by
  unfold termFunK
  rw [summandK_eq, summandK_eq, summandK_eq, hfun_add, summandPoly_add, map_add,
    AddMonoidAlgebra.coeff_add, Finsupp.add_apply]

omit [Λ.HasDetOne] in
/-- **Additivity of the series at the cusp `D` in the cusp form** (either seed type). -/
theorem planeEisensteinAt_add (hn : 4 ≤ n) {y : Fin 5 → ℝ} (hy : y ∈ Omega) (a b' : Fin 5)
    (f g : CuspForm Λ ((n + 3 : ℕ) : ℤ)) :
    planeEisensteinAt b D Γ n (f + g) y a b' =
      planeEisensteinAt b D Γ n f y a b' + planeEisensteinAt b D Γ n g y a b' := by
  apply Subtype.ext
  apply MvPolynomial.ext
  intro m
  rw [Submodule.coe_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_planeEisensteinAt,
    coeff_planeEisensteinAt, coeff_planeEisensteinAt,
    ← Summable.tsum_add (summable_termFunK_val b D Γ Λ n f hn hy a b' m)
      (summable_termFunK_val b D Γ Λ n g hn hy a b' m)]
  congr 1
  funext w
  exact termFunK_add Γ n Λ b D w a b' m y f g

/-- Additivity of the closed form of the series at the cusp `D`. -/
theorem planeEisensteinAtInv_add (hn : 4 ≤ n) (hLevi : LeviInCusp D Γ Λ)
    (f g : CuspForm Λ ((n + 3 : ℕ) : ℤ)) :
    planeEisensteinAtInv b D Γ Λ n (f + g) hn hLevi =
      planeEisensteinAtInv b D Γ Λ n f hn hLevi + planeEisensteinAtInv b D Γ Λ n g hn hLevi := by
  unfold planeEisensteinAtInv
  apply InvComponents.toInv_add
  intro y hy a b'
  show Coef.mk (planeEisensteinAt b D Γ n (f + g) y a b') =
    Coef.mk (planeEisensteinAt b D Γ n f y a b') + Coef.mk (planeEisensteinAt b D Γ n g y a b')
  rw [planeEisensteinAt_add Γ n Λ b D hn hy a b' f g]
  rfl

/-- **Additivity of the complexified class of the series at the cusp `D` in the cusp form.** -/
theorem eisensteinAtClassC_add (hn : 4 ≤ n) (hLevi : LeviInCusp D Γ Λ)
    (f g : CuspForm Λ ((n + 3 : ℕ) : ℤ)) :
    eisensteinAtClassC b D Γ Λ n (f + g) hn hLevi =
      eisensteinAtClassC b D Γ Λ n f hn hLevi + eisensteinAtClassC b D Γ Λ n g hn hLevi := by
  unfold eisensteinAtClassC eisensteinAtClass
  rw [planeEisensteinAtInv_add Γ n Λ b D hn hLevi f g, map_add, map_add]

end Cusp

end ClassLevel

end TernaryPeriodPolynomials.Argument.EisensteinClass
