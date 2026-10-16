module

public import TernaryPeriodPolynomials.Building.PlaneFlatExtensions
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Compact.ScalarConvergence
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Endpoint.ConstantTerm
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Hilbert.Cohomological

@[expose] public section


/-!
# Continuation-free plane Eisenstein hypothesis in degrees `n ≥ 4`

The paper never continues the plane Eisenstein series: for `n ≥ 4` (so `k = n + 3 > 6`) the
series converges absolutely at the cohomological point `s₀ = -3/2`.  The library already has the
half-plane convergence results (`CompactScalarConvergence.eisenstein_summable`,
`EndpointConstantTerm.eisensteinSum_analyticAt`) and the flat extensions of induced sections
(`PlaneFlatExtensions.plane_flat_extensions`).  This file packages exactly these inputs as the
predicate `PlaneEisensteinConvergent D`, which replaces `PlaneEisensteinHolomorphic D`
(meromorphic continuation of the plane Eisenstein operators) in the convergent versions of the
constant-term construction in this directory.

Written by Claude Sonnet 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein

open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction

/-- **Convergent plane Eisenstein data (CF1).** The degree is at least four, so that the plane
Eisenstein series converges absolutely at the cohomological point, and every induced section at
the cohomological point has a flat extension.  No meromorphic continuation is involved. -/
structure PlaneEisensteinConvergent {n : ℕ} (D : InducingData n) : Prop where
  /-- Degrees `n ≥ 4`: the cohomological point lies in the half plane `-n/2 < Re s`. -/
  large : 4 ≤ n
  /-- Flat extensions of induced sections at the cohomological point. -/
  flat : ∀ f : AdelicGL → ℂ, IsInduced D .plane cohomologicalPoint f →
    ∃ F : ℂ → AdelicGL → ℂ, IsFlatSection D F ∧ F cohomologicalPoint = f

/-- `PlaneEisensteinConvergent D` holds for every inducing datum of degree at least four. -/
theorem planeEisensteinConvergent {n : ℕ} (hn : 4 ≤ n) (D : InducingData n) :
    PlaneEisensteinConvergent D :=
  ⟨hn, TernaryPeriodPolynomials.PlaneFlatExtensions.plane_flat_extensions n D⟩

/-- **Half-plane convergence predicate (CF2).** `E` is the sum of the plane Eisenstein series of
`F` on the half plane `-n/2 < Re s`. -/
def IsEisensteinHalfPlane (n : ℕ) (F E : ℂ → AdelicGL → ℂ) : Prop :=
  ∀ s : ℂ, -(n : ℝ) / 2 < s.re → ∀ g : AdelicGL, HasSum (eisensteinSummand F s g) (E s g)

/-- The Eisenstein sum of a flat family is its sum on the half plane (CF2). -/
theorem isEisensteinHalfPlane_eisensteinSum {n : ℕ} (D : InducingData n)
    (F : ℂ → AdelicGL → ℂ) (flat : IsFlatSection D F) :
    IsEisensteinHalfPlane n F (StandardJointContinuity.eisensteinSum F) := fun s hs g =>
  (CompactScalarConvergence.eisenstein_summable D F flat s hs g).hasSum

/-- The Eisenstein series of a flat family is analytic in the parameter on the half plane (CF2). -/
theorem eisensteinSum_analyticAt_of_halfPlane {n : ℕ} (D : InducingData n)
    (F : ℂ → AdelicGL → ℂ) (flat : IsFlatSection D F) (g : AdelicGL) (s : ℂ)
    (hs : -(n : ℝ) / 2 < s.re) :
    AnalyticAt ℂ (fun z => StandardJointContinuity.eisensteinSum F z g) s :=
  EndpointConstantTerm.eisensteinSum_analyticAt D F flat g s hs

/-- The Eisenstein series of a flat family is absolutely summable at the cohomological point. -/
theorem summable_cohomological {n : ℕ} {D : InducingData n} (hol : PlaneEisensteinConvergent D)
    (F : ℂ → AdelicGL → ℂ) (flat : IsFlatSection D F) (g : AdelicGL) :
    Summable (eisensteinSummand F cohomologicalPoint g) :=
  CompactScalarConvergence.eisenstein_summable D F flat cohomologicalPoint
    (HilbertCohomological.point_in_halfPlane n hol.large) g

/-- The Eisenstein series of a flat family is analytic in the parameter at the cohomological
point. -/
theorem eisensteinSum_analyticAt_cohomological {n : ℕ} {D : InducingData n}
    (hol : PlaneEisensteinConvergent D) (F : ℂ → AdelicGL → ℂ) (flat : IsFlatSection D F)
    (g : AdelicGL) :
    AnalyticAt ℂ (fun z => StandardJointContinuity.eisensteinSum F z g) cohomologicalPoint :=
  eisensteinSum_analyticAt_of_halfPlane D F flat g cohomologicalPoint
    (HilbertCohomological.point_in_halfPlane n hol.large)

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein
