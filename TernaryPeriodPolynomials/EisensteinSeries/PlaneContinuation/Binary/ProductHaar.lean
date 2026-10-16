module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Real.BinaryRecovery
public import Mathlib.MeasureTheory.Measure.Haar.Unique

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryProductHaar

instance realMeasurableSpace : MeasurableSpace BinaryRealGL := borel BinaryRealGL
instance realBorelSpace : BorelSpace BinaryRealGL := ⟨rfl⟩
instance finiteMeasurableSpace : MeasurableSpace BinaryFiniteGL := borel BinaryFiniteGL
instance finiteBorelSpace : BorelSpace BinaryFiniteGL := ⟨rfl⟩

instance realMatrixLocallyCompact : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) ℝ) :=
  inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → ℝ))
instance finiteMatrixLocallyCompact : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) FiniteAdeles) :=
  inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → FiniteAdeles))
instance realLocallyCompact : LocallyCompactSpace BinaryRealGL :=
  inferInstanceAs (LocallyCompactSpace (Matrix (Fin 2) (Fin 2) ℝ)ˣ)
instance finiteLocallyCompact : LocallyCompactSpace BinaryFiniteGL :=
  inferInstanceAs (LocallyCompactSpace (Matrix (Fin 2) (Fin 2) FiniteAdeles)ˣ)

instance realSecondCountable : SecondCountableTopology BinaryRealGL := by
  let _ : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℝ))
  let _ : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℝ)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact (Units.isEmbedding_embedProduct (M := Matrix (Fin 2) (Fin 2) ℝ)).secondCountableTopology

instance finiteSecondCountable : SecondCountableTopology BinaryFiniteGL := by
  let _ : SecondCountableTopology (Matrix (Fin 2) (Fin 2) FiniteAdeles) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → FiniteAdeles))
  let _ : SecondCountableTopology (Matrix (Fin 2) (Fin 2) FiniteAdeles)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact (Units.isEmbedding_embedProduct (M := Matrix (Fin 2) (Fin 2) FiniteAdeles)).secondCountableTopology

def combineEquiv : BinaryRealGL × BinaryFiniteGL ≃* BinaryAdelicGL where
  toFun := fun pair => combineGL pair.1 pair.2
  invFun := fun binary => (GeneralLinearGroup.map (RingHom.fst ℝ FiniteAdeles) binary,
    GeneralLinearGroup.map (RingHom.snd ℝ FiniteAdeles) binary)
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_mul' := fun first second => FiniteDecomposition.combineGL_mul first.1 second.1 first.2 second.2

theorem combine_continuous : Continuous combineEquiv := by
  apply Units.continuous_iff.mpr
  constructor
  · change Continuous (fun pair : BinaryRealGL × BinaryFiniteGL => fun row column =>
      (pair.1.val row column, pair.2.val row column))
    exact continuous_pi (fun row => continuous_pi (fun column =>
      (((continuous_apply column).comp ((continuous_apply row).comp
        (Units.continuous_val (M := Matrix (Fin 2) (Fin 2) ℝ)))).comp continuous_fst).prodMk
      (((continuous_apply column).comp ((continuous_apply row).comp
        (Units.continuous_val (M := Matrix (Fin 2) (Fin 2) FiniteAdeles)))).comp continuous_snd)))
  · change Continuous (fun pair : BinaryRealGL × BinaryFiniteGL => fun row column =>
      (pair.1⁻¹.val row column, pair.2⁻¹.val row column))
    exact continuous_pi (fun row => continuous_pi (fun column =>
      (((continuous_apply column).comp ((continuous_apply row).comp
        (Units.continuous_val (M := Matrix (Fin 2) (Fin 2) ℝ)))).comp
        (continuous_inv.comp continuous_fst)).prodMk
      (((continuous_apply column).comp ((continuous_apply row).comp
        (Units.continuous_val (M := Matrix (Fin 2) (Fin 2) FiniteAdeles)))).comp
        (continuous_inv.comp continuous_snd))))

theorem split_continuous : Continuous combineEquiv.symm := by
  apply Continuous.prodMk
  · apply Units.continuous_map
    exact continuous_pi (fun row => continuous_pi (fun column =>
      continuous_fst.comp ((continuous_apply column).comp (continuous_apply row))))
  · apply Units.continuous_map
    exact continuous_pi (fun row => continuous_pi (fun column =>
      continuous_snd.comp ((continuous_apply column).comp (continuous_apply row))))

def combineHomeomorph : BinaryRealGL × BinaryFiniteGL ≃ₜ BinaryAdelicGL where
  toEquiv := combineEquiv.toEquiv
  continuous_toFun := combine_continuous
  continuous_invFun := split_continuous

theorem combine_eq (realBinary : BinaryRealGL) (finiteBinary : BinaryFiniteGL) :
    combineEquiv (realBinary, finiteBinary) = atFinite finiteBinary * atInfinity realBinary := by
  rw [atFinite, atInfinity, ← FiniteDecomposition.combineGL_mul, one_mul, mul_one]
  rfl

def realMeasure : Measure BinaryRealGL := Measure.haar
def finiteBase : Measure BinaryFiniteGL := Measure.haar

instance realMeasure_isHaar : realMeasure.IsHaarMeasure := inferInstanceAs (Measure.haar.IsHaarMeasure)
instance finiteBase_isHaar : finiteBase.IsHaarMeasure := inferInstanceAs (Measure.haar.IsHaarMeasure)

def pushed : Measure BinaryAdelicGL := (realMeasure.prod finiteBase).map combineEquiv

instance pushed_isHaar : pushed.IsHaarMeasure :=
  combineEquiv.isHaarMeasure_map (realMeasure.prod finiteBase) combine_continuous split_continuous

def factor : NNReal := BinaryHaar.measure.haarScalarFactor pushed

theorem factor_pos : 0 < factor := Measure.haarScalarFactor_pos_of_isHaarMeasure BinaryHaar.measure pushed

def finiteMeasure : Measure BinaryFiniteGL := factor • finiteBase

instance finiteMeasure_isHaar : finiteMeasure.IsHaarMeasure :=
  Measure.IsHaarMeasure.nnreal_smul finiteBase factor_pos.ne'

theorem map_product : (realMeasure.prod finiteMeasure).map combineEquiv = BinaryHaar.measure := by
  rw [finiteMeasure, Measure.prod_smul_right, Measure.map_smul _ combine_continuous.measurable.aemeasurable]
  exact (Measure.isMulLeftInvariant_eq_smul BinaryHaar.measure pushed).symm

theorem measurePreserving : MeasurePreserving combineHomeomorph.toMeasurableEquiv
    (realMeasure.prod finiteMeasure) BinaryHaar.measure :=
  ⟨combine_continuous.measurable, map_product⟩

theorem integrable_iff (function : BinaryAdelicGL → ℂ) :
    Integrable function BinaryHaar.measure ↔
      Integrable (fun pair : BinaryRealGL × BinaryFiniteGL =>
        function (atFinite pair.2 * atInfinity pair.1)) (realMeasure.prod finiteMeasure) := by
  rw [← map_product]
  exact (integrable_map_equiv combineHomeomorph.toMeasurableEquiv function).trans (by
    simp only [Function.comp_def, show ∀ pair : BinaryRealGL × BinaryFiniteGL,
      combineHomeomorph.toMeasurableEquiv pair = atFinite pair.2 * atInfinity pair.1 from
        fun pair => combine_eq pair.1 pair.2])

theorem integral_product (function : BinaryAdelicGL → ℂ) :
    (∫ binary, function binary ∂BinaryHaar.measure) =
      ∫ pair : BinaryRealGL × BinaryFiniteGL,
        function (atFinite pair.2 * atInfinity pair.1) ∂(realMeasure.prod finiteMeasure) := by
  rw [← map_product]
  exact (integral_map_equiv combineHomeomorph.toMeasurableEquiv function).trans (by
    congr 1
    funext pair
    exact congrArg function (combine_eq pair.1 pair.2))

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryProductHaar
