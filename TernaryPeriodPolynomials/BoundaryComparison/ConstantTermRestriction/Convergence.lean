module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.RightHalfPlane
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Reindex

@[expose] public section



/-! Both halves are already proved, generically in `degree`, in the read-only
`Proofs/PlaneEisensteinContinuation` library:
* `RightHalfPlane.summable` gives absolute convergence of `eisensteinSummand` at any parameter
  with real part `> -degree/2`; at `cohomologicalPoint = -3/2` this needs exactly `degree > 3`,
  i.e. `4 ≤ degree`, matching the target's hypothesis `hn` exactly.
* `Reindex.literalSum_rational_left` is exactly the claimed `G(ℚ)`-left-invariance of
  `∑' q, eisensteinSummand F s g q` (definitionally `ScalarSeries.literalSum F s g`). -/

open GeneralEisenstein GeneralEisenstein.Adelic

namespace TernaryPeriodPolynomials.Argument.Classification

/-- The real part of the cohomological point, as a bare real-number fact. -/
theorem cohomologicalPoint_re : (cohomologicalPoint).re = -3/2 := by
  unfold cohomologicalPoint
  norm_num [Complex.div_re, Complex.normSq, Complex.ofReal_re, Complex.ofReal_im]

theorem plane_eisenstein_convergent_invariant (n : ℕ) (hn : 4 ≤ n) (D : InducingData n) (F : ℂ → AdelicGL → ℂ)
    (hF : IsFlatSection D F) :
    (∀ g, Summable (eisensteinSummand F cohomologicalPoint g)) ∧
    ∀ (γ : RationalGL3) (g : AdelicGL),
      ∑' q, eisensteinSummand F cohomologicalPoint (rationalGroup γ * g) q =
        ∑' q, eisensteinSummand F cohomologicalPoint g q := by
  have hbound : -(n : ℝ) / 2 < (cohomologicalPoint).re := by
    rw [cohomologicalPoint_re]
    have h4 : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  refine ⟨fun g =>
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.RightHalfPlane.summable
      hF g cohomologicalPoint hbound,
    fun γ g =>
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.Reindex.literalSum_rational_left
      (hF.1 cohomologicalPoint) γ g⟩

end TernaryPeriodPolynomials.Argument.Classification
