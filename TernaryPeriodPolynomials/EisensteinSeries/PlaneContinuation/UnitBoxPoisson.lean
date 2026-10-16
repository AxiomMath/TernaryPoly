module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Adelic.RectangularFourier

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz
open scoped Classical

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.UnitBoxPoisson

open AdelicRectangularFourier

theorem unit_coset : FiniteFourier.coset 1 0 = Set.range integralEmbedding := by
  simp [FiniteFourier.coset, FiniteFourier.lattice]

def unitBox : FiniteRectangularFourier.Space → ℂ :=
  FiniteRectangularFourier.boxTest (fun _ => 1) 0

theorem unit_lattice_measure : finiteMeasure.real (FiniteFourier.lattice 1) = 1 := by
  rw [FiniteLatticeMeasure.lattice_real_measure, FiniteLatticeMeasure.finiteUnit_one, map_one, NNReal.coe_one]

theorem scalar_transform_unit (frequency : FiniteAdeles) :
    FiniteFourier.transform ((Set.range integralEmbedding).indicator (fun _ => (1 : ℂ))) frequency =
      (Set.range integralEmbedding).indicator (fun _ => (1 : ℂ)) frequency := by
  rw [← unit_coset, FiniteFourier.transform_coset]
  simp only [Units.val_one, mul_one, mul_zero, neg_zero, FiniteCharacter.phase_zero, one_mul,
    unit_lattice_measure, Complex.ofReal_one]
  by_cases membership : frequency ∈ Set.range integralEmbedding <;> simp [unit_coset, membership]

theorem transform_unitBox : FiniteRectangularFourier.transform unitBox = unitBox := by
  funext frequency
  rw [unitBox, FiniteRectangularFourier.boxTest, FiniteRectangularFourier.transform_tensor]
  unfold FiniteRectangularFourier.tensor
  apply Finset.prod_congr rfl
  intro coordinate _
  change FiniteFourier.transform ((FiniteFourier.coset 1 0).indicator (fun _ => (1 : ℂ))) (frequency coordinate) = _
  rw [unit_coset, scalar_transform_unit]
  simp only [Pi.zero_apply, unit_coset]

def rationalPoint (rational : Coordinate → ℚ) : Space :=
  (WithLp.toLp 2 (fun coordinate => (rational coordinate : ℝ)),
    fun coordinate => algebraMap ℚ FiniteAdeles (rational coordinate))

def integerMap (integer : Coordinate → ℤ) : Coordinate → ℚ := fun coordinate => integer coordinate

theorem integerMap_injective : Function.Injective integerMap := by
  intro first second equality
  funext coordinate
  exact Int.cast_injective (congrFun equality coordinate)

theorem rational_integral_iff (rational : Coordinate → ℚ) :
    (rationalPoint rational).2 ∈ FiniteRectangularFourier.box (fun _ => 1) 0 ↔
      rational ∈ Set.range integerMap := by
  constructor
  · intro membership
    have integers : ∀ coordinate, ∃ integer : ℤ, rational coordinate = integer := by
      intro coordinate
      apply (IntegralRationals.integral_iff_integer _).mp
      have valueMembership := membership coordinate (Set.mem_univ _)
      change algebraMap ℚ FiniteAdeles (rational coordinate) ∈ FiniteFourier.coset 1 0 at valueMembership
      rwa [unit_coset] at valueMembership
    choose integer equality using integers
    exact ⟨integer, funext (fun coordinate => (equality coordinate).symm)⟩
  · rintro ⟨integer, rfl⟩ coordinate _
    change algebraMap ℚ FiniteAdeles ((integer coordinate : ℤ) : ℚ) ∈ FiniteFourier.coset 1 0
    rw [unit_coset]
    exact (IntegralRationals.integral_iff_integer _).mpr ⟨integer coordinate, rfl⟩

theorem unitBox_rational (rational : Coordinate → ℚ) :
    unitBox (rationalPoint rational).2 =
      (Set.range integerMap).indicator (fun _ => (1 : ℂ)) rational := by
  rw [unitBox, FiniteRectangularFourier.boxTest_indicator]
  by_cases membership : rational ∈ Set.range integerMap
  · rw [Set.indicator_of_mem ((rational_integral_iff rational).mpr membership), Set.indicator_of_mem membership]
  · rw [Set.indicator_of_notMem (fun h => membership ((rational_integral_iff rational).mp h)),
      Set.indicator_of_notMem membership]

theorem rationalPoint_integer_real (integer : Coordinate → ℤ) :
    (rationalPoint (integerMap integer)).1 = SchwartzPeriodization.integerVector integer := by
  ext coordinate
  change ((integer coordinate : ℚ) : ℝ) = (integer coordinate : ℝ)
  exact Rat.cast_intCast _

theorem tensor_integer (realTest : SchwartzMap RealSpace ℂ) (integer : Coordinate → ℤ) :
    tensor realTest unitBox (rationalPoint (integerMap integer)) = realTest (SchwartzPeriodization.integerVector integer) := by
  rw [tensor, unitBox_rational, Set.indicator_of_mem (Set.mem_range_self _), mul_one, rationalPoint_integer_real]

theorem tensor_outside (realTest : SchwartzMap RealSpace ℂ) (rational : Coordinate → ℚ)
    (outside : rational ∉ Set.range integerMap) : tensor realTest unitBox (rationalPoint rational) = 0 := by
  rw [tensor, unitBox_rational, Set.indicator_of_notMem outside, mul_zero]

theorem rational_sum (realTest : SchwartzMap RealSpace ℂ) :
    (∑' rational : Coordinate → ℚ, tensor realTest unitBox (rationalPoint rational)) =
      ∑' integer : Coordinate → ℤ, realTest (SchwartzPeriodization.integerVector integer) := by
  have supported : Function.support (fun rational => tensor realTest unitBox (rationalPoint rational)) ⊆ Set.range integerMap := by
    intro rational nonzero
    by_contra outside
    exact nonzero (tensor_outside realTest rational outside)
  have equality := integerMap_injective.tsum_eq supported
  simpa only [tensor_integer] using equality.symm

theorem rational_hasSum (realTest : SchwartzMap RealSpace ℂ) :
    HasSum (fun rational : Coordinate → ℚ => tensor realTest unitBox (rationalPoint rational))
      (∑' integer : Coordinate → ℤ, realTest (SchwartzPeriodization.integerVector integer)) := by
  apply (integerMap_injective.hasSum_iff (tensor_outside realTest)).mp
  change HasSum (fun integer => tensor realTest unitBox (rationalPoint (integerMap integer))) _
  simp only [tensor_integer]
  have result := (SchwartzPeriodization.summable realTest 0).hasSum
  simpa only [zero_add] using result

theorem transform_tensor_unit (realTest : SchwartzMap RealSpace ℂ) :
    transform (tensor realTest unitBox) = tensor (FourierTransform.fourier realTest) unitBox := by
  funext frequency
  rw [transform_tensor, transform_unitBox]
  rfl

theorem poisson (realTest : SchwartzMap RealSpace ℂ) :
    (∑' rational : Coordinate → ℚ, tensor realTest unitBox (rationalPoint rational)) =
      ∑' rational : Coordinate → ℚ, transform (tensor realTest unitBox) (rationalPoint rational) := by
  rw [transform_tensor_unit, rational_sum, rational_sum]
  exact RectangularPoisson.poisson realTest

theorem poisson_hasSum (realTest : SchwartzMap RealSpace ℂ) :
    HasSum (fun rational : Coordinate → ℚ => transform (tensor realTest unitBox) (rationalPoint rational))
      (∑' rational : Coordinate → ℚ, tensor realTest unitBox (rationalPoint rational)) := by
  rw [transform_tensor_unit, rational_sum, RectangularPoisson.poisson]
  exact rational_hasSum (FourierTransform.fourier realTest)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.UnitBoxPoisson
