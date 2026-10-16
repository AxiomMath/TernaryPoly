module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.PlaneLevelRadicalCocycles
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cuspidal.UpperLatticePrimitive
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.UpperCuspidalPrimitive

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem realPlaneLevelTwoCocycle_exists_radical_primitive {index : Type} [Fintype index]
    (degree : ℕ) (positive : 0 < degree) (odd : Odd degree) (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (cycle : groupCohomology.cocycles₂ (realPlaneLevelCuspidalRep degree cusp trivialCharacter)) (unit_zero : cycle (1, 1) = 0)
    (regular : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun point : (Fin 2 → ℝ) × (Fin 2 → ℝ) =>
      cuspidalTensorHilbertEmbedding cusp basis
        (cycle (SemidirectProduct.inl (Multiplicative.ofAdd point.1), SemidirectProduct.inl (Multiplicative.ofAdd point.2))).val))
    (analytic : ∀ coordinate first, AnalyticAt ℝ
      (fun point : (BinaryRealMatrix × ℝ) × ℝ =>
        binaryHilbertTranslation cusp (atInfinity (invertibleMatrix point.1.1))
          (cuspidalTensorHilbertEmbedding cusp basis
            (cycle (SemidirectProduct.inl (realRadicalAxis coordinate point.1.2), SemidirectProduct.inl (realRadicalAxis coordinate point.2))).val))
      ((1, first), 0)) :
    ∃ primitive : RealPlaneRadical → cuspidalTensorValues cusp (HomogeneousPoly degree),
      (∀ element, primitive element ∈ cuspidalTensorFiniteLevel cusp (HomogeneousPoly degree)) ∧
      ContDiff ℝ (↑(⊤ : ℕ∞)) (fun point : Fin 2 → ℝ =>
        cuspidalTensorHilbertEmbedding cusp basis (primitive (Multiplicative.ofAdd point))) ∧
      ∀ first second,
        cuspidalTensorMap (V := HomogeneousPoly degree) (W := HomogeneousPoly degree) cusp
          ((realUpperRadicalRep degree).ρ first) (primitive second) - primitive (first * second) + primitive first =
            (cycle (SemidirectProduct.inl first, SemidirectProduct.inl second)).val := by
  let : AddCommGroup (cuspidalTensorValues cusp (HomogeneousPoly degree)) :=
    (cuspidalTensorValues cusp (HomogeneousPoly degree)).addCommGroup
  let radicalCycle := realPlaneLevelRadicalCycle degree cusp cycle
  let latticeCycle := realPlaneLevelLatticeCycle degree cusp cycle
  have radical_unit : radicalCycle (1, 1) = 0 := by
    change (cycle (SemidirectProduct.inl 1, SemidirectProduct.inl 1)).val = 0
    rw [map_one]
    exact congrArg Subtype.val unit_zero
  have lattice_unit : latticeCycle (1, 1) = 0 := by
    change (cycle (realPlaneLatticeRadical 1, realPlaneLatticeRadical 1)).val = 0
    rw [map_one]
    exact congrArg Subtype.val unit_zero
  have lattice_fixed (first second : RadicalLattice) :
      latticeCycle (first, second) ∈ cuspidalTensorFiniteLevel cusp (HomogeneousPoly degree) :=
    (cycle (realPlaneLatticeRadical first, realPlaneLatticeRadical second)).property
  have projected (argument : BinaryAdelicGL) : binaryHomogeneousRestrict degree
      ((latticeCycle (radicalLatticeFirst, radicalLatticeSecond)).val argument -
        (latticeCycle (radicalLatticeSecond, radicalLatticeFirst)).val argument) = 0 :=
    realPlaneLevelTwoCocycle_projected_alternation_zero degree odd cusp cycle radicalLatticeFirst radicalLatticeSecond argument
  obtain ⟨latticePrimitive, latticePrimitive_fixed, latticeBoundary⟩ :=
    cuspidalUpperLatticeTwoCocycle_exists_primitive degree positive cusp latticeCycle lattice_unit lattice_fixed projected
  let primitiveValues : RadicalLattice → cuspidalTensorValues cusp (HomogeneousPoly degree) := latticePrimitive
  have boundary (first second : RadicalLattice) :
      cuspidalTensorMap (V := HomogeneousPoly degree) (W := HomogeneousPoly degree) cusp
        ((realUpperRadicalRep degree).ρ (radicalLatticeReal first)) (primitiveValues second) -
          primitiveValues (first * second) + primitiveValues first =
            radicalCycle (radicalLatticeReal first, radicalLatticeReal second) := by
    rw [realUpperRadicalRep_lattice]
    exact latticeBoundary first second
  have radical_fixed (first second : RealPlaneRadical) :
      radicalCycle (first, second) ∈ cuspidalTensorFiniteLevel cusp (HomogeneousPoly degree) :=
    (cycle (SemidirectProduct.inl first, SemidirectProduct.inl second)).property
  obtain ⟨lifts, projects, _, lift_fixed, lift_smooth, _, commute⟩ :=
    realUpperCuspidalTwoCocycle_exists_axisLifts degree cusp basis radicalCycle radical_unit regular radical_fixed analytic
      primitiveValues latticePrimitive_fixed boundary
  exact realUpperCuspidalAxisLifts_primitive degree cusp basis radicalCycle radical_unit regular radical_fixed
    lifts projects lift_fixed lift_smooth commute

theorem realPlaneLevelTwoCocycle_exists_radical_primitive_of_trivial {index : Type} [Fintype index]
    (degree : ℕ) (positive : 0 < degree) (odd : Odd degree) (cusp : CuspidalRepresentation)
    (character : RankOneCharacter) (trivial : character = trivialCharacter)
    (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (cycle : groupCohomology.cocycles₂ (realPlaneLevelCuspidalRep degree cusp character)) (unit_zero : cycle (1, 1) = 0)
    (regular : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun point : (Fin 2 → ℝ) × (Fin 2 → ℝ) =>
      cuspidalTensorHilbertEmbedding cusp basis
        (cycle (SemidirectProduct.inl (Multiplicative.ofAdd point.1), SemidirectProduct.inl (Multiplicative.ofAdd point.2))).val))
    (analytic : ∀ coordinate first, AnalyticAt ℝ
      (fun point : (BinaryRealMatrix × ℝ) × ℝ =>
        binaryHilbertTranslation cusp (atInfinity (invertibleMatrix point.1.1))
          (cuspidalTensorHilbertEmbedding cusp basis
            (cycle (SemidirectProduct.inl (realRadicalAxis coordinate point.1.2), SemidirectProduct.inl (realRadicalAxis coordinate point.2))).val))
      ((1, first), 0)) :
    ∃ primitive : RealPlaneRadical → cuspidalTensorValues cusp (HomogeneousPoly degree),
      (∀ element, primitive element ∈ cuspidalTensorFiniteLevel cusp (HomogeneousPoly degree)) ∧
      ContDiff ℝ (↑(⊤ : ℕ∞)) (fun point : Fin 2 → ℝ =>
        cuspidalTensorHilbertEmbedding cusp basis (primitive (Multiplicative.ofAdd point))) ∧
      ∀ first second,
        cuspidalTensorMap (V := HomogeneousPoly degree) (W := HomogeneousPoly degree) cusp
          ((realUpperRadicalRep degree).ρ first) (primitive second) - primitive (first * second) + primitive first =
            (cycle (SemidirectProduct.inl first, SemidirectProduct.inl second)).val := by
  subst character
  exact realPlaneLevelTwoCocycle_exists_radical_primitive degree positive odd cusp basis cycle unit_zero regular analytic

end TernaryPeriodPolynomials.SphericalDetection.Helpers
