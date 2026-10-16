module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cuspidal.OneParameterLifts
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.LiftEmbeddingCommutation
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.RadicalTwoCocycleDetection
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cuspidal.RealRadicalH1

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

attribute [local instance] complexEndRationalAlgebra

variable {index : Type} [Fintype index]

theorem realUpperCuspidalTwoCocycle_exists_axisLifts (degree : ℕ) (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (cycle : groupCohomology.cocycles₂ (realUpperCuspidalRep degree cusp)) (unit_zero : cycle (1, 1) = 0)
    (regular : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun point : (Fin 2 → ℝ) × (Fin 2 → ℝ) =>
      cuspidalTensorHilbertEmbedding cusp basis (cycle (Multiplicative.ofAdd point.1, Multiplicative.ofAdd point.2))))
    (fixed : ∀ first second, cycle (first, second) ∈ cuspidalTensorFiniteLevel cusp (HomogeneousPoly degree))
    (analytic : ∀ coordinate first, AnalyticAt ℝ
      (fun point : (BinaryRealMatrix × ℝ) × ℝ =>
        binaryHilbertTranslation cusp (atInfinity (invertibleMatrix point.1.1))
          (cuspidalTensorHilbertEmbedding cusp basis
            (cycle (realRadicalAxis coordinate point.1.2, realRadicalAxis coordinate point.2)))) ((1, first), 0))
    (primitive : RadicalLattice → cuspidalTensorValues cusp (HomogeneousPoly degree))
    (primitive_fixed : ∀ coordinate, primitive (radicalLatticeGenerator coordinate) ∈ cuspidalTensorFiniteLevel cusp (HomogeneousPoly degree))
    (boundary : ∀ first second, cuspidalTensorMap (V := HomogeneousPoly degree) (W := HomogeneousPoly degree) cusp ((realUpperRadicalRep degree).ρ (radicalLatticeReal first)) (primitive second) -
      primitive (first * second) + primitive first = cycle (radicalLatticeReal first, radicalLatticeReal second)) :
    ∃ lifts : Fin 2 → Multiplicative ℝ →* TwoCocycleExtension (realUpperCuspidalRep degree cusp) cycle unit_zero,
      (∀ coordinate element, (lifts coordinate element).element = realRadicalAxisHom coordinate element) ∧
      (∀ coordinate, (lifts coordinate (Multiplicative.ofAdd 1)).coefficient = -primitive (radicalLatticeGenerator coordinate)) ∧
      (∀ coordinate parameter, (lifts coordinate (Multiplicative.ofAdd parameter)).coefficient ∈ cuspidalTensorFiniteLevel cusp (HomogeneousPoly degree)) ∧
      (∀ coordinate, ContDiff ℝ (↑(⊤ : ℕ∞)) (fun parameter =>
        cuspidalTensorHilbertEmbedding cusp basis (lifts coordinate (Multiplicative.ofAdd parameter)).coefficient)) ∧
      (∀ coordinate center, AnalyticAt ℝ
        (fun point : BinaryRealMatrix × ℝ => binaryHilbertTranslation cusp (atInfinity (invertibleMatrix point.1))
          (cuspidalTensorHilbertEmbedding cusp basis (lifts coordinate (Multiplicative.ofAdd point.2)).coefficient)) (1, center)) ∧
      ∀ first second, Commute (lifts 0 first) (lifts 1 second) := by
  let : AddCommGroup (cuspidalTensorValues cusp (HomogeneousPoly degree)) :=
    (cuspidalTensorValues cusp (HomogeneousPoly degree)).addCommGroup
  let action (coordinate : Fin 2) (parameter : ℝ) : (index → cusp.H) →L[ℝ] (index → cusp.H) :=
    (basisHilbertCoefficient cusp basis ((realUpperRadicalRep degree).ρ (realRadicalAxis coordinate parameter))).restrictScalars ℝ
  have action_eq (coordinate : Fin 2) (parameter : ℝ) (vector : index → cusp.H) : action coordinate parameter vector =
      (realUpperHilbertRep degree cusp basis).ρ (realRadicalAxisHom coordinate (Multiplicative.ofAdd parameter)) vector := rfl
  have action_exponential (coordinate : Fin 2) (parameter : ℝ) (vector : index → cusp.H) : action coordinate parameter vector =
      IsNilpotent.exp ((parameter : ℂ) • realUpperHilbertGenerator degree cusp basis coordinate) vector :=
    LinearMap.congr_fun (realUpperHilbertRep_axis degree cusp basis coordinate parameter) vector
  have action_add (coordinate : Fin 2) (first second : ℝ) (vector : index → cusp.H) :
      action coordinate (first + second) vector = action coordinate first (action coordinate second vector) := by
    simp only [action_eq]
    change (realUpperHilbertRep degree cusp basis).ρ
      (realRadicalAxisHom coordinate (Multiplicative.ofAdd first * Multiplicative.ofAdd second)) vector = _
    rw [map_mul, map_mul, Module.End.mul_apply]
  have axis_regular (coordinate : Fin 2) : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun point : ℝ × ℝ =>
      cuspidalTensorHilbertEmbedding cusp basis
        (cycle (realRadicalAxis coordinate point.1, realRadicalAxis coordinate point.2))) := by
    have input_regular : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun point : ℝ × ℝ =>
        ((realRadicalAxis coordinate point.1).toAdd, (realRadicalAxis coordinate point.2).toAdd)) :=
      ((realRadicalAxisCoordinates_contDiff coordinate).comp contDiff_fst).prodMk
        ((realRadicalAxisCoordinates_contDiff coordinate).comp contDiff_snd)
    convert regular.comp input_regular using 1
    rfl
  have negative_fixed (coordinate : Fin 2) :
      -primitive (radicalLatticeGenerator coordinate) ∈ cuspidalTensorFiniteLevel cusp (HomogeneousPoly degree) := by
    intro matrix argument
    change -(primitive (radicalLatticeGenerator coordinate)).val _ = -(primitive (radicalLatticeGenerator coordinate)).val _
    rw [primitive_fixed coordinate matrix argument]
  have exists_lift (coordinate : Fin 2) :
      ∃ lift : Multiplicative ℝ →* TwoCocycleExtension (realUpperCuspidalRep degree cusp) cycle unit_zero,
        (∀ element, (lift element).element = realRadicalAxisHom coordinate element) ∧
        (lift (Multiplicative.ofAdd 1)).coefficient = -primitive (radicalLatticeGenerator coordinate) ∧
        (∀ parameter, (lift (Multiplicative.ofAdd parameter)).coefficient ∈ cuspidalTensorFiniteLevel cusp (HomogeneousPoly degree)) ∧
        ContDiff ℝ (↑(⊤ : ℕ∞)) (fun parameter =>
          cuspidalTensorHilbertEmbedding cusp basis (lift (Multiplicative.ofAdd parameter)).coefficient) ∧
        (∀ center, AnalyticAt ℝ
          (fun point : BinaryRealMatrix × ℝ => binaryHilbertTranslation cusp (atInfinity (invertibleMatrix point.1))
            (cuspidalTensorHilbertEmbedding cusp basis (lift (Multiplicative.ofAdd point.2)).coefficient)) (1, center)) :=
    cuspidalTwoCocycleRealLift_exists cusp basis
    (realUpperCuspidalRep degree cusp).ρ cycle unit_zero (realRadicalAxisHom coordinate)
    (upperRadicalGenerator degree coordinate) degree (upperRadicalGenerator_power_zero degree coordinate)
    (action coordinate)
    (fun parameter vector => realUpperCuspidalHilbert_intertwines degree cusp basis (realRadicalAxis coordinate parameter) vector)
    (action_exponential coordinate) (action_add coordinate) (axis_regular coordinate)
    (fun first second => fixed (realRadicalAxis coordinate first) (realRadicalAxis coordinate second))
    (analytic coordinate) (-primitive (radicalLatticeGenerator coordinate))
    (negative_fixed coordinate)
  choose lifts projects units lift_fixed lift_smooth lift_analytic using exists_lift
  let values (first second : RealPlaneRadical) : cuspidalTensorValues cusp (HomogeneousPoly degree) := cycle (first, second)
  have boundary_value (first second : RadicalLattice) :
      cuspidalTensorMap (V := HomogeneousPoly degree) (W := HomogeneousPoly degree) cusp
        ((realUpperRadicalRep degree).ρ (radicalLatticeReal first)) (primitive second) -
          primitive (first * second) + primitive first = values (radicalLatticeReal first) (radicalLatticeReal second) :=
    boundary first second
  have unit_commute : Commute (lifts 0 (Multiplicative.ofAdd 1)) (lifts 1 (Multiplicative.ofAdd 1)) := by
    apply TwoCocycleExtension.ext
    · change (lifts 0 (Multiplicative.ofAdd 1)).coefficient +
          (realUpperCuspidalRep degree cusp).ρ (lifts 0 (Multiplicative.ofAdd 1)).element (lifts 1 (Multiplicative.ofAdd 1)).coefficient +
            cycle ((lifts 0 (Multiplicative.ofAdd 1)).element, (lifts 1 (Multiplicative.ofAdd 1)).element) =
        (lifts 1 (Multiplicative.ofAdd 1)).coefficient +
          (realUpperCuspidalRep degree cusp).ρ (lifts 1 (Multiplicative.ofAdd 1)).element (lifts 0 (Multiplicative.ofAdd 1)).coefficient +
            cycle ((lifts 1 (Multiplicative.ofAdd 1)).element, (lifts 0 (Multiplicative.ofAdd 1)).element)
      simp only [units, projects]
      change -primitive (radicalLatticeGenerator 0) +
          cuspidalTensorMap (V := HomogeneousPoly degree) (W := HomogeneousPoly degree) cusp ((realUpperRadicalRep degree).ρ (realRadicalAxis 0 1)) (-primitive (radicalLatticeGenerator 1)) +
            values (realRadicalAxis 0 1) (realRadicalAxis 1 1) =
        -primitive (radicalLatticeGenerator 1) +
          cuspidalTensorMap (V := HomogeneousPoly degree) (W := HomogeneousPoly degree) cusp ((realUpperRadicalRep degree).ρ (realRadicalAxis 1 1)) (-primitive (radicalLatticeGenerator 0)) +
            values (realRadicalAxis 1 1) (realRadicalAxis 0 1)
      rw [realRadicalAxis_one, realRadicalAxis_one, map_neg, map_neg, ← boundary_value, ← boundary_value,
        mul_comm (radicalLatticeGenerator 0) (radicalLatticeGenerator 1)]
      abel
    · exact mul_comm _ _
  have commutation (coordinate : Fin 2)
      (element : TwoCocycleExtension (realUpperCuspidalRep degree cusp) cycle unit_zero)
      (commutes : Commute element (lifts coordinate (Multiplicative.ofAdd 1))) :
      ∀ parameter, Commute element (lifts coordinate parameter) := by
    apply twoCocycleRealLift_commute_of_one_embedding (realUpperCuspidalRep degree cusp)
      (realUpperHilbertRep degree cusp basis).ρ (cuspidalTensorHilbertEmbedding cusp basis)
      (cuspidalTensorHilbertEmbedding_injective cusp basis) (realUpperCuspidalHilbert_intertwines degree cusp basis)
      cycle unit_zero (realRadicalAxisHom coordinate) (realUpperHilbertGenerator degree cusp basis coordinate) degree
      (realUpperHilbertGenerator_nilpotent degree cusp basis coordinate) (action coordinate) (action_eq coordinate)
      (action_exponential coordinate) (lifts coordinate) (projects coordinate)
      ((lift_smooth coordinate).differentiable (by simp) 0) element (fun _ => Commute.all _ _)
      (realUpperHilbertRep_continuous degree cusp basis element.element) _ _ commutes
    · exact (regular.comp (contDiff_const.prodMk (realRadicalAxisCoordinates_contDiff coordinate))).differentiable (by simp) 0
    · exact (regular.comp ((realRadicalAxisCoordinates_contDiff coordinate).prodMk contDiff_const)).differentiable (by simp) 0
  refine ⟨lifts, projects, units, lift_fixed, lift_smooth, lift_analytic, ?_⟩
  intro first second
  have first_commutes := commutation 0 (lifts 1 (Multiplicative.ofAdd 1)) unit_commute.symm first
  exact commutation 1 (lifts 0 first) first_commutes.symm second

end TernaryPeriodPolynomials.SphericalDetection.Helpers
