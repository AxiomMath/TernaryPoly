module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Edge.LatticeComparisonDerivative
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Edge.LatticeComparisonLattice
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.CanonicalTransferGlue
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.LowerRadicalEdgeFormula

@[expose] public section


/-!
# The lattice cocycle of the corrected radical edge

Let `t` be a regular two-cocycle of the real good-line stabilizer with values in linear scalar
tests and let `a` be a family of linear tests, differentiable at `0`, whose coboundary is `t` on
the real radical. For `γ ∈ GL₂(ℤ)` and an adelic point `h`, the corrected radical edge
`g_γ(Y) = t(γ, e^{Y γ}) - t(e^Y, γ) - (γ • a(Y γ) - a(Y))`, read as a coefficient vector at `h`,
is a crossed homomorphism of the real lower radical. Restricted to the lattice `3 ℤ²` it is a
one-cocycle of the lower radical lattice, whose lower radical coordinate is `3` times the
derivative edge of `t` at `γ`, corrected by the Levi difference of the derivative of `a`. At the
identity adelic point, and when `a` is invariant under the integral Levi at infinity, that Levi
difference is a coboundary of `GL₂(ℤ)` acting on `Sym^{n+1}` without determinant twist.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EdgeControl

variable {n : ℕ}

/-! ### Linear tests -/

theorem LinearTests.sub {F G : LineValues n} (hF : LinearTests F) (hG : LinearTests G) :
    LinearTests (F - G) := by
  intro h functional
  change F (h, functional) - G (h, functional) = _
  rw [lineVector_sub, map_sub, hF, hG]

theorem radicalEdge_linear {t : LineGroup → LineGroup → LineValues n}
    (tLinear : ∀ q q', LinearTests (t q q')) (m : unimodularLevi) (Y : Fin 2 → ℝ) :
    LinearTests (radicalEdge t m Y) := by
  rw [radicalEdge_eq]
  exact (tLinear _ _).sub (tLinear _ _)

theorem leviCorrectedEdge_linear {t : LineGroup → LineGroup → LineValues n}
    (tLinear : ∀ q q', LinearTests (t q q')) {a : (Fin 2 → ℝ) → LineValues n}
    (linear : ∀ Y, LinearTests (a Y)) (m : unimodularLevi) (Y : Fin 2 → ℝ) :
    LinearTests (leviCorrectedEdge t a m Y) :=
  (radicalEdge_linear tLinear m Y).sub (((linear _).smul _).sub (linear Y))

theorem lineVector_lineRadical_smul (Y : Fin 2 → ℝ) {F : LineValues n} (hF : LinearTests F)
    (h : BinaryAdelicGL) :
    lineVector (lineRadicalElement Y • F) h = realCoefficientComponent n trivialCharacter
      (lineRadicalMatrix (Multiplicative.ofAdd Y)) (lineVector F h) := by
  have right : ((lineRadicalElement Y).right : BinaryRealGL) = 1 := rfl
  rw [lineVector_smul _ hF, lineMatrix_lineRadicalElement, right, pivotConjugate_one,
    atInfinity_one, mul_one]

/-! ### The corrected radical edge as a coefficient vector -/

/-- The corrected radical edge at `m`, read as a coefficient vector at the adelic point `h`. -/
def correctedEdgeVector (t : LineGroup → LineGroup → LineValues n)
    (a : (Fin 2 → ℝ) → LineValues n) (m : unimodularLevi) (h : BinaryAdelicGL)
    (Y : Fin 2 → ℝ) : HomogeneousPoly n :=
  lineVector (leviCorrectedEdge t a m Y) h

/-- **The corrected radical edge vector is a crossed homomorphism of the real lower radical.** -/
theorem correctedEdgeVector_add {t : LineGroup → LineGroup → LineValues n}
    (cocycle : IsTwoCocycle t) (tLinear : ∀ q q', LinearTests (t q q'))
    {a : (Fin 2 → ℝ) → LineValues n} (linear : ∀ Y, LinearTests (a Y))
    (trivial : ∀ Y Y', t (lineRadicalElement Y) (lineRadicalElement Y') =
      lineRadicalElement Y • a Y' - a (Y + Y') + a Y) (m : unimodularLevi)
    (h : BinaryAdelicGL) (Y Y' : Fin 2 → ℝ) :
    correctedEdgeVector t a m h (Y + Y') = correctedEdgeVector t a m h Y +
      realCoefficientComponent n trivialCharacter (lineRadicalMatrix (Multiplicative.ofAdd Y))
        (correctedEdgeVector t a m h Y') := by
  unfold correctedEdgeVector
  rw [leviCorrectedEdge_add cocycle trivial, lineVector_add,
    lineVector_lineRadical_smul Y (leviCorrectedEdge_linear tLinear linear m Y')]

theorem correctedEdgeVector_differentiable {t : LineGroup → LineGroup → LineValues n}
    (regular : EdgeRegular t) {a : (Fin 2 → ℝ) → LineValues n} (linear : ∀ Y, LinearTests (a Y))
    (differentiable : ∀ p, DifferentiableAt ℝ (fun Y => a Y p) 0) (m : unimodularLevi)
    (h : BinaryAdelicGL) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    DifferentiableAt ℝ (fun Y => functional (correctedEdgeVector t a m h Y)) 0 := by
  have tests (Y : Fin 2 → ℝ) : functional (correctedEdgeVector t a m h Y) =
      leviCorrectedEdge t a m Y (h, functional) :=
    (leviCorrectedEdge_linear regular.linear linear m Y h functional).symm
  simp_rw [tests]
  set φ : BinaryAdelicGL × (HomogeneousPoly n →ₗ[ℂ] ℂ) :=
    (h * atInfinity (pivotConjugate ((lineLeviElement m).right : BinaryRealGL)),
      functional ∘ₗ realCoefficientComponent n trivialCharacter (lineMatrix (lineLeviElement m)))
  have shifted : DifferentiableAt ℝ (fun Y => a (rowAction m Y) φ) 0 := by
    have outer := differentiable φ
    rw [show (0 : Fin 2 → ℝ) = rowAction m 0 from (map_zero _).symm] at outer
    exact outer.comp (0 : Fin 2 → ℝ) (rowAction m).differentiableAt
  exact (regular.edge_differentiable m (h, functional)).sub
    (shifted.sub (differentiable (h, functional)))

theorem radicalAxisTangent_correctedEdgeVector (t : LineGroup → LineGroup → LineValues n)
    (a : (Fin 2 → ℝ) → LineValues n) (m : unimodularLevi) (h : BinaryAdelicGL) (i : Fin 2) :
    radicalAxisTangent (correctedEdgeVector t a m h) i = lineVector
      (fun p => fderiv ℝ (fun Y => leviCorrectedEdge t a m Y p) 0 (Pi.single i 1)) h := by
  unfold radicalAxisTangent correctedEdgeVector
  simp_rw [coord_lineVector]
  rfl

/-- **The tangent coordinate of the corrected radical edge.** -/
theorem lowerRadicalCoordinate_correctedEdgeVector {t : LineGroup → LineGroup → LineValues n}
    (cocycle : IsTwoCocycle t) (regular : EdgeRegular t) {a : (Fin 2 → ℝ) → LineValues n}
    (linear : ∀ Y, LinearTests (a Y))
    (differentiable : ∀ p, DifferentiableAt ℝ (fun Y => a Y p) 0)
    (trivial : ∀ Y Y', t (lineRadicalElement Y) (lineRadicalElement Y') =
      lineRadicalElement Y • a Y' - a (Y + Y') + a Y) (m : unimodularLevi)
    (h : BinaryAdelicGL) :
    lowerRadicalCoordinate n (fun i => (lowerRadicalAverageEquiv n i).symm
        (correctedEdgeVector t a m h ((3 : ℝ) • Pi.single i 1))) =
      (3 : ℂ) • (derivativeEdge t m h -
        (edgeAction m (radicalDerivativeCoordinate a) h - radicalDerivativeCoordinate a h)) := by
  rw [lowerRadicalCoordinate_radicalAxis
    (correctedEdgeVector_add cocycle regular.linear linear trivial m h)
    (correctedEdgeVector_differentiable regular linear differentiable m h),
    ← leviCorrectedEdge_derivative regular linear differentiable m h]
  congr 2
  funext i
  exact radicalAxisTangent_correctedEdgeVector t a m h i

/-! ### The lattice cocycle -/

theorem latticeVector_mul (r r' : RadicalLattice) :
    latticeVector (r * r') = latticeVector r + latticeVector r' := by
  funext j
  fin_cases j <;> simp [latticeVector, mul_add]

theorem latticeVector_generator (i : Fin 2) :
    latticeVector (radicalLatticeGenerator i) = (3 : ℝ) • Pi.single i 1 := by
  funext j
  fin_cases i <;> fin_cases j <;>
    simp [latticeVector, radicalLatticeGenerator, radicalLatticeFirst, radicalLatticeSecond]

theorem lowerRadicalLatticeRep_rho_latticeVector (r : RadicalLattice) :
    (lowerRadicalLatticeRep n).ρ r = realCoefficientComponent n trivialCharacter
      (lineRadicalMatrix (Multiplicative.ofAdd (latticeVector r))) := by
  rw [lowerRadicalLatticeRep_rho, rationalCoefficient_lowerRadicalLattice]
  rfl

/-- **The lattice cocycle of the corrected radical edge** at the integral Levi element `γ` and
the adelic point `h`: `r ↦ g_γ(3 r)`, read as a coefficient vector at `h`. -/
def latticeEdgeCocycle {t : LineGroup → LineGroup → LineValues n} (cocycle : IsTwoCocycle t)
    (tLinear : ∀ q q', LinearTests (t q q')) {a : (Fin 2 → ℝ) → LineValues n}
    (linear : ∀ Y, LinearTests (a Y))
    (trivial : ∀ Y Y', t (lineRadicalElement Y) (lineRadicalElement Y') =
      lineRadicalElement Y • a Y' - a (Y + Y') + a Y) (γ : GeneralLinearGroup (Fin 2) ℤ)
    (h : BinaryAdelicGL) : groupCohomology.cocycles₁ (lowerRadicalLatticeRep n) :=
  ⟨fun r => correctedEdgeVector t a (integralLevi γ) h (latticeVector r), by
    apply (groupCohomology.mem_cocycles₁_iff _).mpr
    intro r r'
    have law := correctedEdgeVector_add cocycle tLinear linear trivial (integralLevi γ) h
      (latticeVector r) (latticeVector r')
    rw [← latticeVector_mul, ← lowerRadicalLatticeRep_rho_latticeVector] at law
    exact law.trans (add_comm _ _)⟩

theorem latticeEdgeCocycle_apply {t : LineGroup → LineGroup → LineValues n}
    (cocycle : IsTwoCocycle t) (tLinear : ∀ q q', LinearTests (t q q'))
    {a : (Fin 2 → ℝ) → LineValues n} (linear : ∀ Y, LinearTests (a Y))
    (trivial : ∀ Y Y', t (lineRadicalElement Y) (lineRadicalElement Y') =
      lineRadicalElement Y • a Y' - a (Y + Y') + a Y) (γ : GeneralLinearGroup (Fin 2) ℤ)
    (h : BinaryAdelicGL) (r : RadicalLattice) :
    latticeEdgeCocycle cocycle tLinear linear trivial γ h r =
      lineVector (leviCorrectedEdge t a (integralLevi γ) (latticeVector r)) h := rfl

/-- **The lower radical coordinate of the lattice cocycle of the corrected radical edge** is `3`
times the derivative edge, corrected by the Levi difference of the derivative of `a`. -/
theorem lowerRadicalCocycleCoordinate_latticeEdgeCocycle
    {t : LineGroup → LineGroup → LineValues n} (cocycle : IsTwoCocycle t)
    (regular : EdgeRegular t) {a : (Fin 2 → ℝ) → LineValues n} (linear : ∀ Y, LinearTests (a Y))
    (differentiable : ∀ p, DifferentiableAt ℝ (fun Y => a Y p) 0)
    (trivial : ∀ Y Y', t (lineRadicalElement Y) (lineRadicalElement Y') =
      lineRadicalElement Y • a Y' - a (Y + Y') + a Y) (γ : GeneralLinearGroup (Fin 2) ℤ)
    (h : BinaryAdelicGL) :
    lowerRadicalCocycleCoordinate n (latticeEdgeCocycle cocycle regular.linear linear trivial γ h) =
      (3 : ℂ) • (derivativeEdge t (integralLevi γ) h -
        (edgeAction (integralLevi γ) (radicalDerivativeCoordinate a) h -
          radicalDerivativeCoordinate a h)) := by
  rw [lowerRadicalCocycleCoordinate_value, ← lowerRadicalCoordinate_correctedEdgeVector cocycle
    regular linear differentiable trivial]
  congr 1
  funext i
  rw [← latticeVector_generator]
  rfl

end TernaryPeriodPolynomials.AnalyticClasses
