module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.UpperCuspidalAnalyticPrimitive

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem realPlaneLevelTwoCocycle_exists_analytic_radical_primitive {index : Type} [Fintype index]
    (degree : ℕ) (positive : 0 < degree) (odd : Odd degree) (cusp : CuspidalRepresentation)
    (character : RankOneCharacter) (trivial : character = trivialCharacter)
    (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (cycle : groupCohomology.cocycles₂ (realPlaneLevelCuspidalRep degree cusp character)) (unit_zero : cycle (1, 1) = 0)
    (analytic : ∀ center : (Fin 2 → ℝ) × (Fin 2 → ℝ), AnalyticAt ℝ
      (fun point : BinaryRealMatrix × ((Fin 2 → ℝ) × (Fin 2 → ℝ)) =>
        binaryHilbertTranslation cusp (atInfinity (invertibleMatrix point.1))
          (cuspidalTensorHilbertEmbedding cusp basis
            (cycle (SemidirectProduct.inl (Multiplicative.ofAdd point.2.1),
              SemidirectProduct.inl (Multiplicative.ofAdd point.2.2))).val)) (1, center)) :
    ∃ primitive : RealPlaneRadical → cuspidalTensorValues cusp (HomogeneousPoly degree),
      (∀ element, primitive element ∈ cuspidalTensorFiniteLevel cusp (HomogeneousPoly degree)) ∧
      (∀ center : Fin 2 → ℝ, AnalyticAt ℝ (fun point : BinaryRealMatrix × (Fin 2 → ℝ) =>
        binaryHilbertTranslation cusp (atInfinity (invertibleMatrix point.1))
          (cuspidalTensorHilbertEmbedding cusp basis (primitive (Multiplicative.ofAdd point.2)))) (1, center)) ∧
      ∀ first second,
        cuspidalTensorMap (V := HomogeneousPoly degree) (W := HomogeneousPoly degree) cusp
          ((realUpperRadicalRep degree).ρ first) (primitive second) - primitive (first * second) + primitive first =
            (cycle (SemidirectProduct.inl first, SemidirectProduct.inl second)).val := by
  subst character
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
  have regular := cuspidalTensorFamily_contDiff_of_orbital cusp basis
    (fun point : (Fin 2 → ℝ) × (Fin 2 → ℝ) => radicalCycle (Multiplicative.ofAdd point.1, Multiplicative.ofAdd point.2)) analytic
  have axis_analytic := realUpperCuspidalTwoCocycle_axis_orbital_analyticAt degree cusp basis radicalCycle analytic
  obtain ⟨lifts, projects, _, lift_fixed, _, lift_analytic, commute⟩ :=
    realUpperCuspidalTwoCocycle_exists_axisLifts degree cusp basis radicalCycle radical_unit (regular.of_le le_top)
      radical_fixed axis_analytic primitiveValues latticePrimitive_fixed boundary
  exact ⟨realUpperCuspidalAxisPrimitive degree cusp radicalCycle radical_unit lifts,
    realUpperCuspidalAxisPrimitive_finiteLevel degree cusp radicalCycle radical_unit lifts radical_fixed lift_fixed,
    realUpperCuspidalAxisPrimitive_orbital_analyticAt degree cusp basis radicalCycle radical_unit lifts analytic lift_analytic,
    realUpperCuspidalAxisPrimitive_boundary degree cusp radicalCycle radical_unit lifts projects commute⟩

end TernaryPeriodPolynomials.SphericalDetection.Helpers
