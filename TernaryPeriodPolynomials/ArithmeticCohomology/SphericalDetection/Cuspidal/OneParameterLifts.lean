module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cuspidal.TwoCocyclePrimitive
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cuspidal.NilpotentInterpolation
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Two.CocycleExtension

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

attribute [local instance] complexEndRationalAlgebra

variable {V G : Type} [AddCommGroup V] [Module ℂ V] [Group G] {index : Type} [Fintype index]

theorem cuspidalTwoCocycleRealLift_exists (cusp : CuspidalRepresentation) (basis : Module.Basis index ℂ V)
    (representation : Representation ℂ G (cuspidalTensorValues cusp V))
    (cycle : groupCohomology.cocycles₂ (Rep.of representation)) (unit_zero : cycle (1, 1) = 0)
    (input : Multiplicative ℝ →* G) (operator : Module.End ℂ V) (cutoff : ℕ)
    (nilpotent : operator ^ (cutoff + 1) = 0)
    (hilbertAction : ℝ → (index → cusp.H) →L[ℝ] (index → cusp.H))
    (intertwines : ∀ parameter vector,
      cuspidalTensorHilbertEmbedding cusp basis (representation (input (Multiplicative.ofAdd parameter)) vector) =
        hilbertAction parameter (cuspidalTensorHilbertEmbedding cusp basis vector))
    (exponential : ∀ parameter vector, hilbertAction parameter vector =
      IsNilpotent.exp ((parameter : ℂ) • basisHilbertCoefficientHom cusp basis operator) vector)
    (action_add : ∀ first second vector, hilbertAction (first + second) vector = hilbertAction first (hilbertAction second vector))
    (regular : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun point : ℝ × ℝ => cuspidalTensorHilbertEmbedding cusp basis
      (cycle (input (Multiplicative.ofAdd point.1), input (Multiplicative.ofAdd point.2)))))
    (fixed : ∀ first second : ℝ,
      cycle (input (Multiplicative.ofAdd first), input (Multiplicative.ofAdd second)) ∈ cuspidalTensorFiniteLevel cusp V)
    (analytic : ∀ first : ℝ, AnalyticAt ℝ
      (fun point : (BinaryRealMatrix × ℝ) × ℝ =>
        binaryHilbertTranslation cusp (atInfinity (invertibleMatrix point.1.1))
          (cuspidalTensorHilbertEmbedding cusp basis
            (cycle (input (Multiplicative.ofAdd point.1.2), input (Multiplicative.ofAdd point.2))))) ((1, first), 0))
    (coefficient : cuspidalTensorValues cusp V) (coefficient_fixed : coefficient ∈ cuspidalTensorFiniteLevel cusp V) :
    ∃ lift : Multiplicative ℝ →* TwoCocycleExtension (Rep.of representation) cycle unit_zero,
      (∀ element, (lift element).element = input element) ∧
      (lift (Multiplicative.ofAdd 1)).coefficient = coefficient ∧
      (∀ parameter, (lift (Multiplicative.ofAdd parameter)).coefficient ∈ cuspidalTensorFiniteLevel cusp V) ∧
      ContDiff ℝ (↑(⊤ : ℕ∞))
        (fun parameter => cuspidalTensorHilbertEmbedding cusp basis (lift (Multiplicative.ofAdd parameter)).coefficient) ∧
      (∀ center : ℝ, AnalyticAt ℝ
        (fun point : BinaryRealMatrix × ℝ => binaryHilbertTranslation cusp (atInfinity (invertibleMatrix point.1))
          (cuspidalTensorHilbertEmbedding cusp basis (lift (Multiplicative.ofAdd point.2)).coefficient)) (1, center)) := by
  let restricted (first second : ℝ) := cycle (input (Multiplicative.ofAdd first), input (Multiplicative.ofAdd second))
  let action (parameter : ℝ) := representation (input (Multiplicative.ofAdd parameter))
  have relation (first second third : ℝ) :
      restricted (first + second) third + restricted first second =
        action first (restricted second third) + restricted first (second + third) := by
    have equality := twoCocycle_relation (Rep.of representation) cycle
      (input (Multiplicative.ofAdd first)) (input (Multiplicative.ofAdd second)) (input (Multiplicative.ofAdd third))
    rw [← input.map_mul, ← input.map_mul] at equality
    exact equality
  have origin (first : ℝ) : restricted first 0 = 0 := by
    change cycle (input (Multiplicative.ofAdd first), input 1) = 0
    rw [map_one, twoCocycle_one_right, unit_zero, map_zero]
  obtain ⟨primitive, primitive_zero, primitive_fixed, primitive_smooth, primitive_analytic, primitive_boundary⟩ :=
    cuspidalTwoCocycle_exists_primitive cusp basis action hilbertAction intertwines restricted relation origin regular fixed analytic
  obtain ⟨correction, correction_zero, correction_one, correction_fixed, correction_smooth, correction_analytic, correction_cocycle⟩ :=
    cuspidalNilpotentCocycle_exists_of_one cusp basis operator cutoff nilpotent action hilbertAction intertwines
      exponential action_add (coefficient + primitive 1)
        ((cuspidalTensorFiniteLevel cusp V).add_mem coefficient_fixed (primitive_fixed 1))
  let coefficients (point : ℝ) := -primitive point + correction point
  have coefficients_zero : coefficients 0 = 0 := by simp [coefficients, primitive_zero, correction_zero]
  have coefficients_mul (first second : ℝ) : coefficients (first + second) = coefficients first +
      representation (input (Multiplicative.ofAdd first)) (coefficients second) + restricted first second := by
    have boundary := primitive_boundary first second
    have additive := correction_cocycle first second
    change restricted first second = representation (input (Multiplicative.ofAdd first)) (primitive second) -
      primitive (first + second) + primitive first at boundary
    change correction (first + second) = representation (input (Multiplicative.ofAdd first)) (correction second) + correction first at additive
    simp only [coefficients, map_add, map_neg]
    linear_combination (norm := abel) -boundary + additive
  let lift : Multiplicative ℝ →* TwoCocycleExtension (Rep.of representation) cycle unit_zero :=
    { toFun := fun element => ⟨coefficients element.toAdd, input element⟩
      map_one' := by
        apply TwoCocycleExtension.ext
        · exact coefficients_zero
        · exact input.map_one
      map_mul' := by
        intro first second
        apply TwoCocycleExtension.ext
        · exact coefficients_mul first.toAdd second.toAdd
        · exact input.map_mul first second }
  refine ⟨lift, fun _ => rfl, ?_, ?_, ?_, ?_⟩
  · change -primitive 1 + correction 1 = coefficient
    rw [correction_one]
    abel
  · intro parameter
    exact (cuspidalTensorFiniteLevel cusp V).add_mem
      ((cuspidalTensorFiniteLevel cusp V).neg_mem (primitive_fixed parameter)) (correction_fixed parameter)
  · change ContDiff ℝ (↑(⊤ : ℕ∞)) (fun parameter => cuspidalTensorHilbertEmbedding cusp basis (coefficients parameter))
    simpa only [coefficients, map_add, map_neg] using primitive_smooth.neg.add correction_smooth
  · intro center
    change AnalyticAt ℝ (fun point : BinaryRealMatrix × ℝ =>
      binaryHilbertTranslation cusp (atInfinity (invertibleMatrix point.1))
        (cuspidalTensorHilbertEmbedding cusp basis (coefficients point.2))) (1, center)
    convert (primitive_analytic center).neg.add (correction_analytic center) using 1
    funext point
    simp only [coefficients, map_add, map_neg, Pi.neg_apply, Pi.add_apply]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
