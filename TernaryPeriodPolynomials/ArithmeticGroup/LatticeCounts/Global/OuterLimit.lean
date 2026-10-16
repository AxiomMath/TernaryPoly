module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.OuterRatioProduct

@[expose] public section


/-!
# The limit step of the global outer identity

Formalized by Claude Haiku 5.5, with Claude Opus 5.5.

If the finite-`S` adelic integrals satisfy `I_S = v_h · ∏_{p∈S} c_p` (the finite-`S` identity) and
converge along finite sets `S` of primes `p ≠ 3` to the global integral `J`, then `J = v_h · L^{(3)}`-ratio.
The product limit is `outer_ratio_product`. The two inputs `finite_identity` and `limit` are the
missing lemmas (2)-(3) and the dominated-convergence step, stated separately in the report.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument

open Filter Topology TernaryPeriodPolynomials.SphericalDetection.Helpers

/-- **Limit step.** Given a finite-`S` identity `I_S = v · ∏_{p∈S} c_p` and the convergence
`I_S → J` along finite sets of primes `p ≠ 3`, the limit `J` is `v` times the ratio of the
removed L-series at `k-2` and `k-1`. -/
theorem global_integral_eq_outer_ratio {k : ℤ} (hk : 6 < k) (h : CuspForm levelOne k)
    (hh : IsNormalizedEigenform h) (v J : ℂ)
    (finiteIntegral : Finset {p : Nat.Primes // p.val ≠ 3} → ℂ)
    (finite_identity : ∀ S : Finset {p : Nat.Primes // p.val ≠ 3},
      finiteIntegral S = v * ∏ p ∈ S, globalOuterLocalRatio k (fourierCoeff h p.val.val) p.val)
    (limit : Tendsto finiteIntegral atTop (𝓝 J)) :
    J = v * (LSeries (removeEulerCoefficients (fun m => fourierCoeff h m) 3) ((k : ℂ) - 2) /
      LSeries (removeEulerCoefficients (fun m => fourierCoeff h m) 3) ((k : ℂ) - 1)) := by
  have prod : HasProd (fun p : {p : Nat.Primes // p.val ≠ 3} =>
      globalOuterLocalRatio k (fourierCoeff h p.val.val) p.val)
      (LSeries (removeEulerCoefficients (fun m => fourierCoeff h m) 3) ((k : ℂ) - 2) /
        LSeries (removeEulerCoefficients (fun m => fourierCoeff h m) 3) ((k : ℂ) - 1)) :=
    (outer_ratio_product hk h hh).2
  have scaled : Tendsto (fun S : Finset {p : Nat.Primes // p.val ≠ 3} =>
      v * ∏ p ∈ S, globalOuterLocalRatio k (fourierCoeff h p.val.val) p.val) atTop
      (𝓝 (v * (LSeries (removeEulerCoefficients (fun m => fourierCoeff h m) 3) ((k : ℂ) - 2) /
        LSeries (removeEulerCoefficients (fun m => fourierCoeff h m) 3) ((k : ℂ) - 1)))) :=
    tendsto_const_nhds.mul prod
  have same : finiteIntegral = fun S : Finset {p : Nat.Primes // p.val ≠ 3} =>
      v * ∏ p ∈ S, globalOuterLocalRatio k (fourierCoeff h p.val.val) p.val :=
    funext finite_identity
  rw [same] at limit
  exact tendsto_nhds_unique limit scaled

end TernaryPeriodPolynomials.Argument
