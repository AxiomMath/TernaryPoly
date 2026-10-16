module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Adelic.Periodicity
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.SectionConstantTerms
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Plane.LeviMultiplication

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem binaryUnipotent_add {R : Type*} [CommRing R] (first second : R) :
    binaryUnipotent (first + second) = binaryUnipotent first * binaryUnipotent second := by
  apply Units.ext
  apply Matrix.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    simp [binaryUnipotent, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem map_binaryUnipotent {R S : Type*} [CommRing R] [CommRing S]
    (ringMap : R →+* S) (coordinate : R) :
    GeneralLinearGroup.map ringMap (binaryUnipotent coordinate) =
      binaryUnipotent (ringMap coordinate) := by
  apply Units.ext
  apply Matrix.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    simp [GeneralLinearGroup.map, binaryUnipotent, Matrix.map]

theorem induced_binary_unipotent_periodic
    {degree : ℕ} {inducingData : InducingData degree}
    {parameter : ℂ} {sectionValue : AdelicGL → ℂ}
    (induced : IsInduced inducingData .plane parameter sectionValue)
    (groupElement : AdelicGL) (rational : ℚ) (coordinate : Adeles) :
    sectionValue (planeLevi (binaryUnipotent (rationalAdele rational + coordinate)) 1 * groupElement) =
      sectionValue (planeLevi (binaryUnipotent coordinate) 1 * groupElement) := by
  rw [binaryUnipotent_add, planeLevi_binary_mul, mul_assoc, ← map_binaryUnipotent rationalAdele]
  exact induced_binary_rational induced (binaryUnipotent rational) _

theorem induced_binary_unipotent_shift_integral
    {degree : ℕ} {inducingData : InducingData degree}
    {parameter : ℂ} {sectionValue : AdelicGL → ℂ}
    (induced : IsInduced inducingData .plane parameter sectionValue)
    (groupElement : AdelicGL) (shift : Adeles) :
    (∫ coordinate in additiveDomain,
      sectionValue (planeLevi (binaryUnipotent (coordinate - shift)) 1 * groupElement) ∂adeleMeasure) = 0 := by
  rw [rational_periodic_integral_sub_right
    (fun coordinate => sectionValue (planeLevi (binaryUnipotent coordinate) 1 * groupElement))
    (induced_binary_unipotent_periodic induced groupElement) shift]
  exact (induced_binary_unipotent_cuspidal induced groupElement).2

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
