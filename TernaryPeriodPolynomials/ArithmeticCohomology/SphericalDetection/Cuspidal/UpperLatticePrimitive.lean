module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cuspidal.TensorFinitePreimage
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Lattice.TwoCocyclePrimitiveValues
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.UpperRadicalCoinvariants
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cuspidal.LatticeCocycles

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem cuspidalUpperLatticeTwoCocycle_exists_primitive (degree : ℕ) (positive : 0 < degree)
    (cusp : CuspidalRepresentation)
    (cycle : groupCohomology.cocycles₂ (cuspidalTensorPointwiseRep cusp (upperRadicalLatticeRep degree)))
    (unit_zero : cycle (1, 1) = 0)
    (fixed : ∀ first second, cycle (first, second) ∈ cuspidalTensorFiniteLevel cusp (HomogeneousPoly degree))
    (projected : ∀ argument, binaryHomogeneousRestrict degree
      ((cycle (radicalLatticeFirst, radicalLatticeSecond)).val argument -
        (cycle (radicalLatticeSecond, radicalLatticeFirst)).val argument) = 0) :
    ∃ primitive : RadicalLattice → cuspidalTensorPointwiseRep cusp (upperRadicalLatticeRep degree),
      (∀ coordinate, primitive (radicalLatticeGenerator coordinate) ∈ cuspidalTensorFiniteLevel cusp (HomogeneousPoly degree)) ∧
      ∀ first second, (cuspidalTensorPointwiseRep cusp (upperRadicalLatticeRep degree)).ρ first
        (primitive second) - primitive (first * second) + primitive first = cycle (first, second) := by
  let : AddCommGroup (cuspidalTensorValues cusp (HomogeneousPoly degree)) :=
    (cuspidalTensorValues cusp (HomogeneousPoly degree)).addCommGroup
  let values : cuspidalTensorValues cusp (HomogeneousPoly degree) :=
    cycle (radicalLatticeFirst, radicalLatticeSecond) - cycle (radicalLatticeSecond, radicalLatticeFirst)
  have values_fixed : values ∈ cuspidalTensorFiniteLevel cusp (HomogeneousPoly degree) := by
    intro matrix argument
    change (cycle (radicalLatticeFirst, radicalLatticeSecond)).val _ -
      (cycle (radicalLatticeSecond, radicalLatticeFirst)).val _ = _
    rw [fixed, fixed]
    rfl
  let first_action : Module.End ℂ (HomogeneousPoly degree) := (upperRadicalLatticeRep degree).ρ radicalLatticeFirst
  let difference : Module.End ℂ (HomogeneousPoly degree) := first_action - 1
  have member (argument : BinaryAdelicGL) : values.val argument ∈ difference.range := by
    rw [show difference.range = (binaryHomogeneousRestrict degree).ker from upperRadicalLattice_first_range degree positive]
    exact projected argument
  obtain ⟨beta, equality, beta_fixed⟩ := cuspidalTensorMap_exists_finiteLevel_preimage cusp difference values values_fixed member
  let beta_rep : cuspidalTensorPointwiseRep cusp (upperRadicalLatticeRep degree) := beta
  have alternation : latticeTwoCocycleAlternation (cuspidalTensorPointwiseRep cusp (upperRadicalLatticeRep degree)) cycle =
      ((cuspidalTensorPointwiseRep cusp (upperRadicalLatticeRep degree)).ρ radicalLatticeFirst - 1) beta_rep -
        ((cuspidalTensorPointwiseRep cusp (upperRadicalLatticeRep degree)).ρ radicalLatticeSecond - 1) 0 := by
    rw [map_zero, sub_zero]
    apply Subtype.ext
    funext argument
    exact (congrArg (fun vector : cuspidalTensorValues cusp (HomogeneousPoly degree) => vector.val argument) equality).symm
  obtain ⟨primitive, first_value, second_value, boundary⟩ := latticeTwoCocycle_exists_primitive_of_alternation
    (cuspidalTensorPointwiseRep cusp (upperRadicalLatticeRep degree)) cycle unit_zero 0 beta_rep alternation
  refine ⟨primitive, ?_, boundary⟩
  intro coordinate
  fin_cases coordinate
  · change primitive radicalLatticeFirst ∈ cuspidalTensorFiniteLevel cusp (HomogeneousPoly degree)
    rw [first_value]
    exact (cuspidalTensorFiniteLevel cusp (HomogeneousPoly degree)).zero_mem
  · change primitive radicalLatticeSecond ∈ cuspidalTensorFiniteLevel cusp (HomogeneousPoly degree)
    rw [second_value]
    exact beta_fixed

end TernaryPeriodPolynomials.SphericalDetection.Helpers
