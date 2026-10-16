module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Finite.LatticeCosets

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLatticeCosets
open scoped Classical

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLinearLattices

abbrev Space := FiniteRectangularFourier.Space

def basisVector (coordinate : Coordinate) : Space := fun other => if coordinate = other then 1 else 0

theorem coordinate_expansion (linear : Space →ₗ[FiniteAdeles] Space) (value : Space) (coordinate : Coordinate) :
    linear value coordinate = ∑ other, value other * linear (basisVector other) coordinate := by
  have equality := congrFun (linear.pi_apply_eq_sum_univ value) coordinate
  change linear value coordinate = ∑ other, value other * linear (fun j => if other = j then 1 else 0) coordinate
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using equality

theorem linear_continuous (linear : Space →ₗ[FiniteAdeles] Space) : Continuous linear := by
  apply continuous_pi
  intro coordinate
  have equality : (fun value => linear value coordinate) =
      fun value => ∑ other, value other * linear (basisVector other) coordinate := funext (fun value => coordinate_expansion linear value coordinate)
  rw [equality]
  exact continuous_finsetSum _ (fun other _ => (continuous_apply other).mul continuous_const)

def homeomorph (linear : Space ≃ₗ[FiniteAdeles] Space) : Space ≃ₜ Space where
  toEquiv := linear.toEquiv
  continuous_toFun := linear_continuous linear.toLinearMap
  continuous_invFun := linear_continuous linear.symm.toLinearMap

theorem exists_lattice_image (linear : Space →ₗ[FiniteAdeles] Space) (scale : FiniteAdelesˣ) :
    ∃ rational : ℚˣ, ∀ value ∈ latticeSubgroup (FiniteLatticeMeasure.rationalScale rational),
      linear value ∈ latticeSubgroup scale := by
  let coefficient : Coordinate × Coordinate → FiniteAdeles :=
    fun pair => linear (basisVector pair.1) pair.2 * scale.inv
  obtain ⟨denominator, nonzero, integral⟩ := CompactDenominators.exists_common_denominator
    (Set.range coefficient) (Set.finite_range coefficient).isCompact
  let rational : ℚˣ := Units.mk0 (denominator : ℚ) (by exact_mod_cast nonzero)
  refine ⟨rational, fun value membership => ?_⟩
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
  have coefficientIntegral := integral (coefficient (other, coordinate)) (Set.mem_range_self _)
  have productIntegral := FiniteCharacter.lattice_mul (integralEmbedding integer)
    ((denominator : FiniteAdeles) * coefficient (other, coordinate)) ⟨integer, rfl⟩ coefficientIntegral
  have productEquality : value other * linear (basisVector other) coordinate * scale.inv =
      integralEmbedding integer * ((denominator : FiniteAdeles) * coefficient (other, coordinate)) := by
    rw [valueEquality]
    dsimp only [coefficient]
    ring
  rw [productEquality]
  exact productIntegral

theorem box_mem_subgroup (scale : FiniteAdelesˣ) (offset value : Space) :
    value ∈ FiniteRectangularFourier.box (fun _ => scale) offset ↔ value - offset ∈ latticeSubgroup scale := by
  simp only [FiniteRectangularFourier.box, Set.mem_univ_pi, FiniteFourierInversion.coset_mem,
    latticeSubgroup_mem, Pi.sub_apply]

theorem boxTest_invariant (scale : FiniteAdelesˣ) (offset shift value : Space)
    (membership : shift ∈ latticeSubgroup scale) :
    FiniteRectangularFourier.boxTest (fun _ => scale) offset (shift + value) =
      FiniteRectangularFourier.boxTest (fun _ => scale) offset value := by
  have equivalent : shift + value ∈ FiniteRectangularFourier.box (fun _ => scale) offset ↔
      value ∈ FiniteRectangularFourier.box (fun _ => scale) offset := by
    rw [box_mem_subgroup, box_mem_subgroup, add_sub_assoc]
    exact (latticeSubgroup scale).add_mem_cancel_left membership
  rw [FiniteRectangularFourier.boxTest_indicator]
  by_cases belongs : value ∈ FiniteRectangularFourier.box (fun _ => scale) offset
  · rw [Set.indicator_of_mem (equivalent.mpr belongs), Set.indicator_of_mem belongs]
  · rw [Set.indicator_of_notMem (fun h => belongs (equivalent.mp h)), Set.indicator_of_notMem belongs]

theorem pullback_periodic (linear : Space →ₗ[FiniteAdeles] Space) (scale : FiniteAdelesˣ) (offset : Space) :
    ∃ rational : ℚˣ, ∀ shift ∈ latticeSubgroup (FiniteLatticeMeasure.rationalScale rational), ∀ value,
      FiniteRectangularFourier.boxTest (fun _ => scale) offset (linear (shift + value)) =
        FiniteRectangularFourier.boxTest (fun _ => scale) offset (linear value) := by
  obtain ⟨rational, mapsTo⟩ := exists_lattice_image linear scale
  refine ⟨rational, fun shift membership value => ?_⟩
  rw [map_add]
  exact boxTest_invariant scale offset _ _ (mapsTo shift membership)

theorem pullback_poisson_hasSum (realTest : SchwartzMap RealSpace ℂ)
    (linear : Space ≃ₗ[FiniteAdeles] Space) (scale : FiniteAdelesˣ) (offset : Space) :
    HasSum (fun rational : Coordinate → ℚ =>
      AdelicRectangularFourier.transform (AdelicRectangularFourier.tensor realTest
        (fun value => FiniteRectangularFourier.boxTest (fun _ => scale) offset (linear value)))
        (UnitBoxPoisson.rationalPoint rational))
      (∑' rational : Coordinate → ℚ,
        AdelicRectangularFourier.tensor realTest
          (fun value => FiniteRectangularFourier.boxTest (fun _ => scale) offset (linear value))
          (UnitBoxPoisson.rationalPoint rational)) := by
  obtain ⟨rational, invariant⟩ := pullback_periodic linear.toLinearMap scale offset
  exact FiniteLatticeCosets.poisson_hasSum realTest rational _
    ((FiniteRectangularFourier.boxTest_compactSupport (fun _ => scale) offset).comp_homeomorph (homeomorph linear)) invariant

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLinearLattices
