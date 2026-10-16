module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.ParametricGodementContinuation
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Godement.Sums
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.ContinuationAlgebra

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms TernaryPeriodPolynomials.PlaneEisensteinContinuation.VectorMatrixOrbit TernaryPeriodPolynomials.PlaneEisensteinContinuation.ZeroConstantThetaDecay

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteGodementFamilies

variable {Index : Type} {Source : Index → Type}
variable [∀ index, NormedAddCommGroup (Source index)] [∀ index, NormedSpace ℂ (Source index)]
variable [∀ index, CompleteSpace (Source index)]
variable {degree : ℕ} (data : InducingData degree) (indices : Finset Index)
variable (families : ∀ index, Source index →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
variable (tests : ∀ index, ℂ → SchwartzMap RealSpace (Source index))
variable (scales : Index → FiniteAdelesˣ) (offsets : Index → FiniteRectangularFourier.Space) (coefficients : Index → ℂ)

def test (parameter : ℂ) (value : Rectangular Adeles) : data.cusp.smooth :=
  ∑ index ∈ indices, coefficients index • liftTest data (families index)
    (BanachAdelicTheta.tensorTest (tests index parameter) (RectangularAdelicPoisson.finiteTest (scales index) (offsets index))) value

def continuation (parameter : ℂ) (point : AdelicGL) : ℂ :=
  ∑ index ∈ indices, coefficients index * VectorGodementContinuation.continuation data (families index)
    (tests index parameter) (scales index) (offsets index) parameter point

theorem term_integrable (continuous : ∀ index, Continuous (fun vector => (families index vector).val.val))
    (index : Index) (parameter : ℂ) (point : AdelicGL) (halfPlane : (1 - (degree : ℝ)) / 2 < parameter.re) :
    Integrable (VectorGodement.integrand data
      (fun value => coefficients index • liftTest data (families index)
        (BanachAdelicTheta.tensorTest (tests index parameter) (RectangularAdelicPoisson.finiteTest (scales index) (offsets index))) value)
      parameter point) BinaryHaar.measure := by
  have integrable := (VectorUnfolding.raw_integrable_at data (families index) (continuous index) (tests index parameter) _
    (finiteTest_continuous (scales index) (offsets index)) (finiteTest_compactSupport (scales index) (offsets index))
    parameter point halfPlane).const_mul (coefficients index)
  apply integrable.congr
  filter_upwards [] with binary
  exact (GodementSums.integrand_smul data _ _ _ _ binary).symm

theorem test_integrable (continuous : ∀ index, Continuous (fun vector => (families index vector).val.val))
    (parameter : ℂ) (point : AdelicGL) (halfPlane : (1 - (degree : ℝ)) / 2 < parameter.re) :
    Integrable (VectorGodement.integrand data (test data indices families tests scales offsets coefficients parameter)
      parameter point) BinaryHaar.measure := by
  have integrable := integrable_finsetSum indices
    (fun index _ => term_integrable data families tests scales offsets coefficients continuous index parameter point halfPlane)
  apply integrable.congr
  filter_upwards [] with binary
  exact (GodementSums.integrand_sum data indices _ parameter point binary).symm

theorem section_sum (continuous : ∀ index, Continuous (fun vector => (families index vector).val.val))
    (parameter : ℂ) (point : AdelicGL) (halfPlane : (1 - (degree : ℝ)) / 2 < parameter.re) :
    VectorGodement.sectionFunction data (test data indices families tests scales offsets coefficients parameter) parameter point =
      ∑ index ∈ indices, coefficients index * VectorGodement.sectionFunction data
        (liftTest data (families index) (BanachAdelicTheta.tensorTest (tests index parameter)
          (RectangularAdelicPoisson.finiteTest (scales index) (offsets index)))) parameter point := by
  unfold test
  rw [GodementSums.section_sum data indices _ parameter point
    (fun index _ => term_integrable data families tests scales offsets coefficients continuous index parameter point halfPlane)]
  apply Finset.sum_congr rfl
  intro index _
  exact GodementSums.section_smul data _ _ _ _

theorem isEisensteinContinuation (continuous : ∀ index, Continuous (fun vector => (families index vector).val.val))
    (holomorphic : ∀ index vector, Differentiable ℂ (fun parameter => tests index parameter vector))
    (bounded : ∀ index, ∀ compact : Set ℂ, IsCompact compact → UniformSchwartzBounds.Bounded (tests index '' compact)) :
    IsEisensteinContinuation
      (fun parameter point => VectorGodement.sectionFunction data (test data indices families tests scales offsets coefficients parameter) parameter point)
      (continuation data indices families tests scales offsets coefficients) := by
  have summed := ContinuationAlgebra.finset_sum indices
    (fun index parameter point => coefficients index * VectorGodement.sectionFunction data
      (liftTest data (families index) (BanachAdelicTheta.tensorTest (tests index parameter)
        (RectangularAdelicPoisson.finiteTest (scales index) (offsets index)))) parameter point)
    (fun index parameter point => coefficients index * VectorGodementContinuation.continuation data (families index)
      (tests index parameter) (scales index) (offsets index) parameter point)
    (fun index _ => ContinuationAlgebra.multiply
      (ParametricGodementContinuation.isEisensteinContinuation data (families index) (continuous index) (tests index)
        (holomorphic index) (bounded index) (scales index) (offsets index))
      (fun _ => coefficients index) (fun parameter => MeromorphicAt.const _ parameter))
  exact ContinuationAlgebra.transfer summed ((1 - (degree : ℝ)) / 2)
    (fun parameter halfPlane point => (section_sum data indices families tests scales offsets coefficients continuous parameter point halfPlane).symm)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteGodementFamilies
