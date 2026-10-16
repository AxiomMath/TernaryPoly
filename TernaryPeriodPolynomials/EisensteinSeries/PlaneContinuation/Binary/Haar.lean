module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Rectangular.Kernel
public import Mathlib.MeasureTheory.Measure.Haar.Unique

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryHaar

instance matrixLocallyCompact : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) Adeles) :=
  inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → Adeles))

instance matrixSecondCountable : SecondCountableTopology (Matrix (Fin 2) (Fin 2) Adeles) :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → Adeles))

instance groupLocallyCompact : LocallyCompactSpace BinaryAdelicGL :=
  inferInstanceAs (LocallyCompactSpace (Matrix (Fin 2) (Fin 2) Adeles)ˣ)

instance groupSecondCountable : SecondCountableTopology BinaryAdelicGL := by
  let _ : SecondCountableTopology (Matrix (Fin 2) (Fin 2) Adeles)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact (Units.isEmbedding_embedProduct (M := Matrix (Fin 2) (Fin 2) Adeles)).secondCountableTopology

noncomputable instance groupMeasurableSpace : MeasurableSpace BinaryAdelicGL := borel BinaryAdelicGL

instance groupBorelSpace : BorelSpace BinaryAdelicGL := ⟨rfl⟩

noncomputable def measure : Measure BinaryAdelicGL := Measure.haar

instance measure_isHaar : measure.IsHaarMeasure := inferInstanceAs (Measure.haar.IsHaarMeasure)

theorem integral_left (function : BinaryAdelicGL → ℂ) (matrix : BinaryAdelicGL) :
    ∫ point, function (matrix * point) ∂measure = ∫ point, function point ∂measure :=
  integral_mul_left_eq_self function matrix

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryHaar
