module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Finite.ParameterThetaDecay

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLatticeCosets
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLinearLattices (basisVector coordinate_expansion)

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteParameterLattices

theorem uniform_lattice_image {Index : Type*} [TopologicalSpace Index]
    (linears : Index → Space →ₗ[FiniteAdeles] Space)
    (continuous : ∀ first second, Continuous (fun parameter => linears parameter (basisVector first) second))
    (parameters : Set Index) (compact : IsCompact parameters) (scale : FiniteAdelesˣ) :
    ∃ rational : ℚˣ, ∀ parameter ∈ parameters,
      ∀ value ∈ latticeSubgroup (FiniteLatticeMeasure.rationalScale rational),
        linears parameter value ∈ latticeSubgroup scale := by
  let coefficient : Coordinate × Coordinate → Index → FiniteAdeles :=
    fun pair parameter => linears parameter (basisVector pair.1) pair.2 * scale.inv
  let coefficientSet := ⋃ pair : Coordinate × Coordinate, coefficient pair '' parameters
  have coefficientCompact : IsCompact coefficientSet :=
    isCompact_iUnion (fun pair => compact.image ((continuous pair.1 pair.2).mul continuous_const))
  obtain ⟨denominator, nonzero, integral⟩ := CompactDenominators.exists_common_denominator coefficientSet coefficientCompact
  let rational : ℚˣ := Units.mk0 (denominator : ℚ) (by exact_mod_cast nonzero)
  refine ⟨rational, fun parameter parameterMem value membership => ?_⟩
  let linear := linears parameter
  apply (latticeSubgroup_mem scale _).mpr
  intro coordinate
  apply (FiniteFourierInversion.lattice_mem scale _).mpr
  rw [coordinate_expansion, Finset.sum_mul]
  change (∑ other, value other * linear (basisVector other) coordinate * scale.inv) ∈ integralEmbedding.range
  apply Subring.sum_mem
  intro other _
  obtain ⟨integer, equality⟩ := ((latticeSubgroup_mem _ value).mp membership) other
  have valueEquality : value other = (denominator : FiniteAdeles) * integralEmbedding integer := by
    change algebraMap ℚ FiniteAdeles (denominator : ℚ) * integralEmbedding integer = value other at equality
    rw [map_natCast] at equality
    exact equality.symm
  have coefficientIntegral := integral (coefficient (other, coordinate) parameter)
    (Set.mem_iUnion.mpr ⟨(other, coordinate), parameter, parameterMem, rfl⟩)
  have productIntegral := FiniteCharacter.lattice_mul (integralEmbedding integer)
    ((denominator : FiniteAdeles) * coefficient (other, coordinate) parameter) ⟨integer, rfl⟩ coefficientIntegral
  have productEquality : value other * linear (basisVector other) coordinate * scale.inv =
      integralEmbedding integer * ((denominator : FiniteAdeles) * coefficient (other, coordinate) parameter) := by
    rw [valueEquality]
    dsimp only [coefficient, linear]
    ring
  rw [productEquality]
  exact productIntegral

theorem coefficient_continuous (first second : Coordinate) :
    Continuous (fun parameter : FiniteParameterThetaDecay.Parameter =>
      RectangularAdelicPoisson.finiteTransform parameter.1 parameter.2 (basisVector first) second) := by
  change Continuous (fun parameter : FiniteParameterThetaDecay.Parameter =>
    (parameter.1⁻¹.val * RectangularAdelicPoisson.coordinates.symm (basisVector first) * parameter.2.val) second.1 second.2)
  exact (continuous_apply second.2).comp ((continuous_apply second.1).comp
    (((Units.continuous_val.comp continuous_fst.inv).matrix_mul continuous_const).matrix_mul
      (Units.continuous_val.comp continuous_snd)))

theorem box_uniform_periodic (scale : FiniteAdelesˣ) (offset : Space)
    (parameters : Set FiniteParameterThetaDecay.Parameter) (compact : IsCompact parameters) :
    ∃ rational : ℚˣ, ∀ parameter ∈ parameters,
      ∀ shift ∈ latticeSubgroup (FiniteLatticeMeasure.rationalScale rational), ∀ value,
        FiniteRectangularFourier.boxTest (fun _ => scale) offset
          (RectangularAdelicPoisson.finiteTransform parameter.1 parameter.2 (shift + value)) =
        FiniteRectangularFourier.boxTest (fun _ => scale) offset
          (RectangularAdelicPoisson.finiteTransform parameter.1 parameter.2 value) := by
  obtain ⟨rational, mapsTo⟩ := uniform_lattice_image
    (fun parameter : FiniteParameterThetaDecay.Parameter => (RectangularAdelicPoisson.finiteTransform parameter.1 parameter.2).toLinearMap)
    coefficient_continuous parameters compact scale
  refine ⟨rational, fun parameter parameterMem shift membership value => ?_⟩
  rw [map_add]
  exact FiniteLinearLattices.boxTest_invariant scale offset _ _ (mapsTo parameter parameterMem shift membership)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteParameterLattices
