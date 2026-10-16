module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.LocalUniqueness
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Odd.VanishPoly

@[expose] public section


/-!
# Degree-zero reconstruction, part A: the polynomial/cocycle coordinate layer

First half (Steps 1-6) of the degree-zero reconstruction of the good-line `phiL`/`edgeK`
injectivity chain; see `ZeroDegreeChainB.lean` for the remaining steps (7-12, the
representation/category-theory layer) and the overview docstring there.
-/

noncomputable section

open GeneralEisenstein Matrix
open GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open MvPolynomial
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Spectral.LocalUniqueness
open TernaryPeriodPolynomials.SourceConstruction (homogeneousPoly_zero_eq_C)

namespace TernaryPeriodPolynomials.Argument.FacePairing


/-- **Step 1.** `degree = 0` analogue of
`lowerRadicalContraction_eq_zero_iff`, not needing `0 < degree`: at degree zero both sides are
constants, so the contraction vanishing forces each constant to vanish directly (no antiderivative
construction needed), and the trivial potential `0` then witnesses the existential. -/
theorem lowerRadicalContractionEqZeroIffZero (alpha beta : HomogeneousPoly 0) :
    lowerRadicalContraction alpha.val beta.val = 0 ↔
      ∃ potential : HomogeneousPoly 0,
        alpha.val = X 0 * pderiv 2 potential.val ∧ beta.val = X 1 * pderiv 2 potential.val := by
  constructor
  · intro hzero
    have hzero' : X 1 * alpha.val - X 0 * beta.val = 0 := hzero
    rw [homogeneousPoly_zero_eq_C alpha, homogeneousPoly_zero_eq_C beta] at hzero'
    have ha0 : alpha.val.coeff 0 = 0 := by
      have h := congrArg (MvPolynomial.eval (![0, 1, 0] : Fin 3 → ℂ)) hzero'
      simpa using h
    have hb0 : beta.val.coeff 0 = 0 := by
      have h := congrArg (MvPolynomial.eval (![1, 0, 0] : Fin 3 → ℂ)) hzero'
      simpa using h
    refine ⟨0, ?_, ?_⟩
    · rw [homogeneousPoly_zero_eq_C alpha, ha0]; simp
    · rw [homogeneousPoly_zero_eq_C beta, hb0]; simp
  · rintro ⟨potential, heq1, heq2⟩
    show X 1 * alpha.val - X 0 * beta.val = 0
    rw [heq1, heq2]
    exact lowerRadicalContraction_boundary potential.val

/-- **Step 2.** `degree = 0` analogue of `lowerRadicalCycleCoordinate_kernel`, verbatim modulo
substituting `lowerRadicalContractionEqZeroIffZero` for the positivity-requiring original. -/
theorem lowerRadicalCycleCoordinateKernelZero (pair : lowerRadicalCycles 0) :
    lowerRadicalCycleCoordinate 0 pair = 0 ↔
      ∃ potential : HomogeneousPoly 0,
        (pair.val 0).val = X 0 * pderiv 2 potential.val ∧
        (pair.val 1).val = X 1 * pderiv 2 potential.val := by
  rw [← lowerRadicalContractionEqZeroIffZero (pair.val 0) (pair.val 1)]
  constructor
  · intro zero
    rw [← lowerRadicalCycleCoordinate_lift, zero, Submodule.coe_zero, map_zero]
  · intro zero
    apply Subtype.ext
    change binaryPolynomialRestrict (lowerRadicalContraction (pair.val 0).val (pair.val 1).val) = 0
    rw [zero, map_zero]

/-- **Step 3.** `degree = 0` analogue of `lowerRadicalCocycleCoordinate_zero_iff`. -/
theorem lowerRadicalCocycleCoordinateZeroIffZero
    (cycle : groupCohomology.cocycles₁ (lowerRadicalLatticeRep 0)) :
    lowerRadicalCocycleCoordinate 0 cycle = 0 ↔
      groupCohomology.H1π (lowerRadicalLatticeRep 0) cycle = 0 := by
  rw [lowerRadicalCocycle_H1_zero_iff_polynomial_boundary]
  exact lowerRadicalCycleCoordinateKernelZero (lowerRadicalCocycleToInfinitesimal 0 cycle)

/-- **Step 4.** `degree = 0` analogue of `lowerRadicalCocycleCoordinate_eq_iff`. -/
theorem lowerRadicalCocycleCoordinateEqIffZero
    (first second : groupCohomology.cocycles₁ (lowerRadicalLatticeRep 0)) :
    lowerRadicalCocycleCoordinate 0 first = lowerRadicalCocycleCoordinate 0 second ↔
      groupCohomology.H1π (lowerRadicalLatticeRep 0) first =
        groupCohomology.H1π (lowerRadicalLatticeRep 0) second := by
  rw [← sub_eq_zero, ← map_sub, lowerRadicalCocycleCoordinateZeroIffZero, map_sub, sub_eq_zero]

/-- **Step 5.** `degree = 0` analogue of `lowerRadicalH1Coordinate`. -/
def lowerRadicalH1CoordinateZero :
    groupCohomology.H1 (lowerRadicalLatticeRep 0) ≃ₗ[ℂ] Binary.HomogeneousPoly 1 :=
  surjectiveLinearCoordinateEquiv (groupCohomology.H1π (lowerRadicalLatticeRep 0)).hom
    (oneCocycle_H1_surjective _) (lowerRadicalCocycleCoordinate 0)
    (lowerRadicalCocycleCoordinate_surjective 0)
    (fun first second => (lowerRadicalCocycleCoordinateEqIffZero first second).symm)

theorem lowerRadicalH1CoordinateZero_apply
    (cycle : groupCohomology.cocycles₁ (lowerRadicalLatticeRep 0)) :
    lowerRadicalH1CoordinateZero (groupCohomology.H1π (lowerRadicalLatticeRep 0) cycle) =
      lowerRadicalCocycleCoordinate 0 cycle :=
  surjectiveLinearCoordinateEquiv_apply (groupCohomology.H1π (lowerRadicalLatticeRep 0)).hom
    (oneCocycle_H1_surjective _) (lowerRadicalCocycleCoordinate 0)
    (lowerRadicalCocycleCoordinate_surjective 0)
    (fun first second => (lowerRadicalCocycleCoordinateEqIffZero first second).symm) cycle

/-- **Step 6.** `degree = 0` analogue of `lowerRadicalH1Coordinate_equivariant`. -/
theorem lowerRadicalH1CoordinateZero_equivariant (matrix : GeneralLinearGroup (Fin 2) ℤ)
    (cohomology : groupCohomology.H1 (lowerRadicalLatticeRep 0)) :
    lowerRadicalH1CoordinateZero (lowerRadicalH1Levi 0 matrix cohomology) =
      Binary.homogeneousAction 1 0 (GeneralLinearGroup.map (Int.castRingHom ℂ) matrix)
        (lowerRadicalH1CoordinateZero cohomology) := by
  obtain ⟨cycle, rfl⟩ := oneCocycle_H1_surjective (lowerRadicalLatticeRep 0) cohomology
  rw [lowerRadicalH1Levi_apply, lowerRadicalH1CoordinateZero_apply, lowerRadicalH1CoordinateZero_apply,
    lowerRadicalCocycleCoordinate_equivariant]

end TernaryPeriodPolynomials.Argument.FacePairing
