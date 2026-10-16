module

public import TernaryPeriodPolynomials.BoundaryComparison.ClosedSeeds.LeviJacobian

@[expose] public section


/-! Clause (iii) of Lemma C.3 (`ar:lem:seed`): bundling the five component Jacobian facts from
`LeviJacobian.lean` into a single `HasFDerivAt (leviMap A t) _ p` fact, and extracting the numeric
Jacobian entries `fderiv ℝ (leviMap A t) p (Pi.single i 1) a` needed by `formPullback`. Feeds
`TernaryPeriodPolynomials.seed_closed_equivariant`. -/


open MvPolynomial

namespace TernaryPeriodPolynomials.Argument

/-- The bundled Fréchet derivative of `leviMap A t` at `p`, assembled from the five component
derivatives of `LeviJacobian.lean`. -/
theorem hasFDerivAt_leviMap (A : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) (p : Fin 5 → ℝ)
    (hden : (A 1 0 : ℂ) * seedTau p + A 1 1 ≠ 0) :
    HasFDerivAt (leviMap A t)
      (ContinuousLinearMap.pi
        (![(A 0 0 / t) • (ContinuousLinearMap.proj (0 : Fin 5) : (Fin 5 → ℝ) →L[ℝ] ℝ) +
              (A 0 1 / t) • (ContinuousLinearMap.proj (1 : Fin 5) : (Fin 5 → ℝ) →L[ℝ] ℝ),
            (A 1 0 / t) • (ContinuousLinearMap.proj (0 : Fin 5) : (Fin 5 → ℝ) →L[ℝ] ℝ) +
              (A 1 1 / t) • (ContinuousLinearMap.proj (1 : Fin 5) : (Fin 5 → ℝ) →L[ℝ] ℝ),
            Complex.reCLM.comp
              (((ContinuousLinearMap.toSpanSingleton ℂ
                    ((A.det : ℂ) / ((A 1 0 : ℂ) * seedTau p + A 1 1) ^ 2)).restrictScalars ℝ).comp
                (Complex.ofRealCLM.comp (ContinuousLinearMap.proj (2 : Fin 5)) +
                  Complex.I • (Complex.ofRealCLM.comp (ContinuousLinearMap.proj (3 : Fin 5))))),
            Complex.imCLM.comp
              (((ContinuousLinearMap.toSpanSingleton ℂ
                    ((A.det : ℂ) / ((A 1 0 : ℂ) * seedTau p + A 1 1) ^ 2)).restrictScalars ℝ).comp
                (Complex.ofRealCLM.comp (ContinuousLinearMap.proj (2 : Fin 5)) +
                  Complex.I • (Complex.ofRealCLM.comp (ContinuousLinearMap.proj (3 : Fin 5))))),
            t • (ContinuousLinearMap.proj (4 : Fin 5) : (Fin 5 → ℝ) →L[ℝ] ℝ)])) p := by
  show HasFDerivAt (fun (q : Fin 5 → ℝ) (i : Fin 5) => leviMap A t q i) _ p
  apply hasFDerivAt_pi.mpr
  intro a
  fin_cases a
  · exact hasFDerivAt_levi0 A t p
  · exact hasFDerivAt_levi1 A t p
  · exact hasFDerivAt_levi2 A p hden
  · exact hasFDerivAt_levi3 A p hden
  · exact hasFDerivAt_levi4 t p

end TernaryPeriodPolynomials.Argument
