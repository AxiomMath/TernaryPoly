module

public import TernaryPeriodPolynomials.BoundaryComparison.ClosedSeeds.LeviAlgebra
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.Analysis.Calculus.Deriv.Basic

@[expose] public section


/-! Clause (iii) of Lemma C.3 (`ar:lem:seed`): the Jacobian of `leviMap A t` at a point `p`,
component by component, needed to evaluate `formPullback`'s `fderiv ℝ (leviMap A t) p (Pi.single
i 1) a` for the handful of `(i,a)` pairs appearing in its reduced `8`-term sum. Components `0,1`
("affine block") depend only on `p 0, p 1`; components `2,3` ("Möbius block") depend only on `p 2,
p 3` via `seedTau`; component `4` depends only on `p 4`. Feeds
`TernaryPeriodPolynomials.seed_closed_equivariant`. -/


open MvPolynomial

namespace TernaryPeriodPolynomials.Argument

/-- Component `0` of `leviMap`: a linear function of `p 0, p 1` only. -/
theorem hasFDerivAt_levi0 (A : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) (p : Fin 5 → ℝ) :
    HasFDerivAt (fun q : Fin 5 → ℝ => (A 0 0 * q 0 + A 0 1 * q 1) / t)
      ((A 0 0 / t) • (ContinuousLinearMap.proj (0 : Fin 5) : (Fin 5 → ℝ) →L[ℝ] ℝ) +
        (A 0 1 / t) • (ContinuousLinearMap.proj (1 : Fin 5) : (Fin 5 → ℝ) →L[ℝ] ℝ)) p := by
  have h0 := (ContinuousLinearMap.proj (0 : Fin 5) : (Fin 5 → ℝ) →L[ℝ] ℝ).hasFDerivAt (x := p)
  have h1 := (ContinuousLinearMap.proj (1 : Fin 5) : (Fin 5 → ℝ) →L[ℝ] ℝ).hasFDerivAt (x := p)
  have hfun : (fun q : Fin 5 → ℝ => (A 0 0 * q 0 + A 0 1 * q 1) / t) =
      (fun q : Fin 5 → ℝ => (A 0 0 / t) • q 0 + (A 0 1 / t) • q 1) := by
    funext q; simp only [smul_eq_mul]; ring
  rw [hfun]
  exact (h0.const_smul (A 0 0 / t)).add (h1.const_smul (A 0 1 / t))

/-- Component `1` of `leviMap`: a linear function of `p 0, p 1` only. -/
theorem hasFDerivAt_levi1 (A : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) (p : Fin 5 → ℝ) :
    HasFDerivAt (fun q : Fin 5 → ℝ => (A 1 0 * q 0 + A 1 1 * q 1) / t)
      ((A 1 0 / t) • (ContinuousLinearMap.proj (0 : Fin 5) : (Fin 5 → ℝ) →L[ℝ] ℝ) +
        (A 1 1 / t) • (ContinuousLinearMap.proj (1 : Fin 5) : (Fin 5 → ℝ) →L[ℝ] ℝ)) p := by
  have h0 := (ContinuousLinearMap.proj (0 : Fin 5) : (Fin 5 → ℝ) →L[ℝ] ℝ).hasFDerivAt (x := p)
  have h1 := (ContinuousLinearMap.proj (1 : Fin 5) : (Fin 5 → ℝ) →L[ℝ] ℝ).hasFDerivAt (x := p)
  have hfun : (fun q : Fin 5 → ℝ => (A 1 0 * q 0 + A 1 1 * q 1) / t) =
      (fun q : Fin 5 → ℝ => (A 1 0 / t) • q 0 + (A 1 1 / t) • q 1) := by
    funext q; simp only [smul_eq_mul]; ring
  rw [hfun]
  exact (h0.const_smul (A 1 0 / t)).add (h1.const_smul (A 1 1 / t))

/-- Component `4` of `leviMap`: linear in `p 4` only. -/
theorem hasFDerivAt_levi4 (t : ℝ) (p : Fin 5 → ℝ) :
    HasFDerivAt (fun q : Fin 5 → ℝ => t * q 4)
      (t • (ContinuousLinearMap.proj (4 : Fin 5) : (Fin 5 → ℝ) →L[ℝ] ℝ)) p := by
  have h4 := (ContinuousLinearMap.proj (4 : Fin 5) : (Fin 5 → ℝ) →L[ℝ] ℝ).hasFDerivAt (x := p)
  have hfun : (fun q : Fin 5 → ℝ => t * q 4) = (fun q : Fin 5 → ℝ => t • q 4) := by
    funext q; simp only [smul_eq_mul]
  rw [hfun]
  exact h4.const_smul t

/-- The Fréchet derivative of `seedTau` as a function of all `5` real coordinates (depending only
on coordinates `2, 3`). -/
theorem hasFDerivAt_seedTau (p : Fin 5 → ℝ) :
    HasFDerivAt seedTau
      (Complex.ofRealCLM.comp (ContinuousLinearMap.proj (2 : Fin 5)) +
        Complex.I • (Complex.ofRealCLM.comp (ContinuousLinearMap.proj (3 : Fin 5)))) p := by
  unfold seedTau
  have h2 := (Complex.ofRealCLM.comp
    (ContinuousLinearMap.proj (2 : Fin 5) : (Fin 5 → ℝ) →L[ℝ] ℝ)).hasFDerivAt (x := p)
  have h3 := (Complex.ofRealCLM.comp
    (ContinuousLinearMap.proj (3 : Fin 5) : (Fin 5 → ℝ) →L[ℝ] ℝ)).hasFDerivAt (x := p)
  have hfun : (fun q : Fin 5 → ℝ => (q 2 : ℂ) + Complex.I * (q 3 : ℂ)) =
      (fun q : Fin 5 → ℝ =>
        Complex.ofRealCLM ((ContinuousLinearMap.proj (2 : Fin 5) : (Fin 5 → ℝ) →L[ℝ] ℝ) q) +
          Complex.I • Complex.ofRealCLM
            ((ContinuousLinearMap.proj (3 : Fin 5) : (Fin 5 → ℝ) →L[ℝ] ℝ) q)) := by
    funext q
    simp only [ContinuousLinearMap.proj_apply, Complex.ofRealCLM_apply, smul_eq_mul]
  rw [hfun]
  exact h2.add (h3.const_smul Complex.I)

/-- The Möbius map's derivative, lifted to a Fréchet derivative and restricted to `ℝ`-linearity. -/
theorem hasFDerivAt_leviMobiusC (A : Matrix (Fin 2) (Fin 2) ℝ) (τ : ℂ)
    (hden : (A 1 0 : ℂ) * τ + A 1 1 ≠ 0) :
    HasFDerivAt (fun z : ℂ => ((A 0 0 : ℂ) * z + A 0 1) / ((A 1 0 : ℂ) * z + A 1 1))
      ((ContinuousLinearMap.toSpanSingleton ℂ
          ((A.det : ℂ) / ((A 1 0 : ℂ) * τ + A 1 1) ^ 2)).restrictScalars ℝ) τ :=
  (hasDerivAt_leviMobius A τ hden).hasFDerivAt.restrictScalars ℝ

/-- The Fréchet derivative of `mobius ∘ seedTau` as a function of all `5` real coordinates. -/
theorem hasFDerivAt_mobius_comp_seedTau (A : Matrix (Fin 2) (Fin 2) ℝ) (p : Fin 5 → ℝ)
    (hden : (A 1 0 : ℂ) * seedTau p + A 1 1 ≠ 0) :
    HasFDerivAt (fun q : Fin 5 → ℝ =>
        ((A 0 0 : ℂ) * seedTau q + A 0 1) / ((A 1 0 : ℂ) * seedTau q + A 1 1))
      (((ContinuousLinearMap.toSpanSingleton ℂ
            ((A.det : ℂ) / ((A 1 0 : ℂ) * seedTau p + A 1 1) ^ 2)).restrictScalars ℝ).comp
        (Complex.ofRealCLM.comp (ContinuousLinearMap.proj (2 : Fin 5)) +
          Complex.I • (Complex.ofRealCLM.comp (ContinuousLinearMap.proj (3 : Fin 5))))) p := by
  exact HasFDerivAt.comp p (hasFDerivAt_leviMobiusC A (seedTau p) hden) (hasFDerivAt_seedTau p)

/-- Component `2` of `leviMap`: the real part of the Möbius-transformed `seedTau`. -/
theorem hasFDerivAt_levi2 (A : Matrix (Fin 2) (Fin 2) ℝ) (p : Fin 5 → ℝ)
    (hden : (A 1 0 : ℂ) * seedTau p + A 1 1 ≠ 0) :
    HasFDerivAt (fun q : Fin 5 → ℝ =>
        (((A 0 0 : ℂ) * seedTau q + A 0 1) / ((A 1 0 : ℂ) * seedTau q + A 1 1)).re)
      (Complex.reCLM.comp
        (((ContinuousLinearMap.toSpanSingleton ℂ
              ((A.det : ℂ) / ((A 1 0 : ℂ) * seedTau p + A 1 1) ^ 2)).restrictScalars ℝ).comp
          (Complex.ofRealCLM.comp (ContinuousLinearMap.proj (2 : Fin 5)) +
            Complex.I • (Complex.ofRealCLM.comp (ContinuousLinearMap.proj (3 : Fin 5)))))) p := by
  exact HasFDerivAt.comp p Complex.reCLM.hasFDerivAt (hasFDerivAt_mobius_comp_seedTau A p hden)

/-- Component `3` of `leviMap`: the imaginary part of the Möbius-transformed `seedTau`. -/
theorem hasFDerivAt_levi3 (A : Matrix (Fin 2) (Fin 2) ℝ) (p : Fin 5 → ℝ)
    (hden : (A 1 0 : ℂ) * seedTau p + A 1 1 ≠ 0) :
    HasFDerivAt (fun q : Fin 5 → ℝ =>
        (((A 0 0 : ℂ) * seedTau q + A 0 1) / ((A 1 0 : ℂ) * seedTau q + A 1 1)).im)
      (Complex.imCLM.comp
        (((ContinuousLinearMap.toSpanSingleton ℂ
              ((A.det : ℂ) / ((A 1 0 : ℂ) * seedTau p + A 1 1) ^ 2)).restrictScalars ℝ).comp
          (Complex.ofRealCLM.comp (ContinuousLinearMap.proj (2 : Fin 5)) +
            Complex.I • (Complex.ofRealCLM.comp (ContinuousLinearMap.proj (3 : Fin 5)))))) p := by
  exact HasFDerivAt.comp p Complex.imCLM.hasFDerivAt (hasFDerivAt_mobius_comp_seedTau A p hden)

end TernaryPeriodPolynomials.Argument
