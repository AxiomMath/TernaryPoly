module

public import TernaryPeriodPolynomials.DifferentialForm.WeakTests
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Test.DualAlgebra

@[expose] public section


/-! Actual algebraic compact-test functionals and the faithful Hilbert embedding. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open PolynomialCoefficientMetric PolynomialFormCoordinates PolynomialFormHilbert
open SmoothCoveringDeRham

/-- Algebraic functionals on the actual compact smooth test space. No distribution continuity
or local exactness is included in this definition. -/
abbrev TestDual (n k : ℕ) := Module.Dual ℝ (Core n k)

/-- Every actual Hilbert element gives its genuine compact-test pairing. -/
def hilbertTest (n k : ℕ) : Hilbert n k →ₗ[ℝ] TestDual n k :=
  testEmbedding (inclusion n k)

@[simp] theorem hilbertTest_apply (n k : ℕ) (u : Hilbert n k) (b : Core n k) :
    hilbertTest n k u b = inner ℝ u (inclusion n k b) := rfl

/-- The compact tests separate all actual Hilbert completion elements. -/
theorem hilbertTest_injective (n k : ℕ) : Function.Injective (hilbertTest n k) :=
  testEmbedding_injective (inclusion n k) (inclusion_dense n k)

/-- The transpose of the actual compact formal adjoint, defined on every algebraic test functional. -/
def testDifferential (n k : ℕ) : TestDual n k →ₗ[ℝ] TestDual n (k + 1) :=
  (compactAdjoint n k).dualMap

@[simp] theorem testDifferential_apply (n k : ℕ) (T : TestDual n k) (b : Core n (k + 1)) :
    testDifferential n k T b = T (compactAdjoint n k b) := rfl

/-- The actual maximal graph identity is exactly this test-dual differential identity. -/
theorem maximal_graph_iff_testDifferential (n k : ℕ) (u : Hilbert n k)
    (z : Hilbert n (k + 1)) :
    (u, z) ∈ (maximalDifferential n k).graph ↔
      testDifferential n k (hilbertTest n k u) = hilbertTest n (k + 1) z :=
  (mem_maximalDifferential_graph_iff n k u z).trans
    (dualMap_testEmbedding_eq_iff (inclusion n k) (inclusion n (k + 1))
      (compactAdjoint n k) u z).symm

end TernaryPoly.PolynomialFormWeakSmooth
