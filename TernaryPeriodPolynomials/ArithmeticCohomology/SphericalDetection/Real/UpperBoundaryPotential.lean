module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.LinearRangeInverse
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.UpperBinaryNormalForm
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cuspidal.NilpotentPrimitive

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def upperLatticeBoundaryPair (degree : ℕ) :
    HomogeneousPoly degree →ₗ[ℂ] HomogeneousPoly degree × HomogeneousPoly degree := by
  let first : Module.End ℂ (HomogeneousPoly degree) := (upperRadicalLatticeRep degree).ρ radicalLatticeFirst
  let second : Module.End ℂ (HomogeneousPoly degree) := (upperRadicalLatticeRep degree).ρ radicalLatticeSecond
  exact (first - 1).prod (second - 1)

def upperLatticeBoundaryInverse (degree : ℕ) :
    (HomogeneousPoly degree × HomogeneousPoly degree) →ₗ[ℂ] HomogeneousPoly degree :=
  linearRangeInverse (upperLatticeBoundaryPair degree)

theorem upperLatticeBoundaryInverse_apply (degree : ℕ) (polynomial : HomogeneousPoly degree) :
    upperLatticeBoundaryPair degree (upperLatticeBoundaryInverse degree (upperLatticeBoundaryPair degree polynomial)) =
      upperLatticeBoundaryPair degree polynomial :=
  linearRangeInverse_apply (upperLatticeBoundaryPair degree) polynomial

def realUpperBoundaryPotential (degree : ℕ) (cusp : CuspidalRepresentation)
    (cycle : groupCohomology.cocycles₁ (realUpperCuspidalRep degree cusp)) :
    cuspidalTensorValues cusp (HomogeneousPoly degree) :=
  cuspidalTensorMap cusp ((upperLatticeBoundaryInverse degree).comp
      (LinearMap.inl ℂ (HomogeneousPoly degree) (HomogeneousPoly degree)))
      (cycle (radicalLatticeReal radicalLatticeFirst)) +
    cuspidalTensorMap cusp ((upperLatticeBoundaryInverse degree).comp
      (LinearMap.inr ℂ (HomogeneousPoly degree) (HomogeneousPoly degree)))
      (cycle (radicalLatticeReal radicalLatticeSecond))

theorem realUpperBoundaryPotential_apply (degree : ℕ) (cusp : CuspidalRepresentation)
    (cycle : groupCohomology.cocycles₁ (realUpperCuspidalRep degree cusp)) (argument : BinaryAdelicGL) :
    (realUpperBoundaryPotential degree cusp cycle).val argument =
      upperLatticeBoundaryInverse degree
        ((cycle (radicalLatticeReal radicalLatticeFirst)).val argument,
          (cycle (radicalLatticeReal radicalLatticeSecond)).val argument) := by
  change upperLatticeBoundaryInverse degree ((cycle (radicalLatticeReal radicalLatticeFirst)).val argument, 0) +
    upperLatticeBoundaryInverse degree (0, (cycle (radicalLatticeReal radicalLatticeSecond)).val argument) = _
  rw [← map_add]
  simp only [Prod.mk_add_mk, add_zero, zero_add]

theorem realUpperBoundaryPotential_boundary {index : Type} [Fintype index]
    (degree : ℕ) (cusp : CuspidalRepresentation) (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (potential : cuspidalTensorValues cusp (HomogeneousPoly degree)) :
    oneBoundaryCycle (realUpperCuspidalRep degree cusp)
        (realUpperBoundaryPotential degree cusp (oneBoundaryCycle (realUpperCuspidalRep degree cusp) potential)) =
      oneBoundaryCycle (realUpperCuspidalRep degree cusp) potential := by
  apply realUpperCuspidalCocycle_eq_of_generators degree cusp basis
  · intro coordinate
    exact (realUpperCuspidalBoundary_differentiable degree cusp basis _ coordinate) 0
  · intro coordinate
    exact (realUpperCuspidalBoundary_differentiable degree cusp basis potential coordinate) 0
  · intro coordinate
    apply Subtype.ext
    funext argument
    rw [realRadicalAxis_one]
    have value := upperLatticeBoundaryInverse_apply degree (potential.val argument)
    let latticeAction : RadicalLattice → Module.End ℂ (HomogeneousPoly degree) :=
      fun radical => (upperRadicalLatticeRep degree).ρ radical
    have boundary (radical : RadicalLattice) :
        (oneBoundaryCycle (realUpperCuspidalRep degree cusp) potential (radicalLatticeReal radical)).val argument =
          latticeAction radical (potential.val argument) - potential.val argument := by
      change ((realUpperCuspidalRep degree cusp).ρ (radicalLatticeReal radical) potential).val argument -
        potential.val argument = _
      rw [realUpperCuspidalRep_lattice]
      rfl
    change ((realUpperCuspidalRep degree cusp).ρ (radicalLatticeReal (radicalLatticeGenerator coordinate))
        (realUpperBoundaryPotential degree cusp (oneBoundaryCycle (realUpperCuspidalRep degree cusp) potential))).val argument -
      (realUpperBoundaryPotential degree cusp (oneBoundaryCycle (realUpperCuspidalRep degree cusp) potential)).val argument = _
    rw [realUpperCuspidalRep_lattice]
    change latticeAction (radicalLatticeGenerator coordinate)
        ((realUpperBoundaryPotential degree cusp (oneBoundaryCycle (realUpperCuspidalRep degree cusp) potential)).val argument) -
      (realUpperBoundaryPotential degree cusp (oneBoundaryCycle (realUpperCuspidalRep degree cusp) potential)).val argument = _
    rw [realUpperBoundaryPotential_apply, boundary radicalLatticeFirst, boundary radicalLatticeSecond,
      boundary (radicalLatticeGenerator coordinate)]
    fin_cases coordinate
    · exact congrArg Prod.fst value
    · exact congrArg Prod.snd value

theorem realUpperBoundaryPotential_of_H1_zero {index : Type} [Fintype index]
    (degree : ℕ) (cusp : CuspidalRepresentation) (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (cycle : groupCohomology.cocycles₁ (realUpperCuspidalRep degree cusp))
    (zero : groupCohomology.H1π (realUpperCuspidalRep degree cusp) cycle = 0) :
    oneBoundaryCycle (realUpperCuspidalRep degree cusp) (realUpperBoundaryPotential degree cusp cycle) = cycle := by
  obtain ⟨potential, boundary⟩ := (groupCohomology.H1π_eq_zero_iff cycle).mp zero
  have equality : oneBoundaryCycle (realUpperCuspidalRep degree cusp) potential = cycle := Subtype.ext boundary
  rw [← equality]
  exact realUpperBoundaryPotential_boundary degree cusp basis potential

theorem realUpperBoundaryPotential_finiteLevel
    (degree : ℕ) (cusp : CuspidalRepresentation)
    (cycle : groupCohomology.cocycles₁ (realUpperCuspidalRep degree cusp))
    (first : cycle (radicalLatticeReal radicalLatticeFirst) ∈ cuspidalTensorFiniteLevel cusp (HomogeneousPoly degree))
    (second : cycle (radicalLatticeReal radicalLatticeSecond) ∈ cuspidalTensorFiniteLevel cusp (HomogeneousPoly degree)) :
    realUpperBoundaryPotential degree cusp cycle ∈ cuspidalTensorFiniteLevel cusp (HomogeneousPoly degree) :=
  (cuspidalTensorFiniteLevel cusp (HomogeneousPoly degree)).add_mem
    (cuspidalTensorMap_finiteLevel cusp _ _ first) (cuspidalTensorMap_finiteLevel cusp _ _ second)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
