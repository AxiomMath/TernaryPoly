module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Finite.FourierInversion

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz
open scoped Classical

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteRectangularFourier

abbrev Space := Coordinate → FiniteAdeles

def measure : Measure Space := Measure.pi (fun _ => finiteMeasure)

instance measure_sigmaFinite : SigmaFinite measure :=
  inferInstanceAs (SigmaFinite (Measure.pi (fun _ : Coordinate => finiteMeasure)))

def pairing (frequency value : Space) : ℂ :=
  FiniteCharacter.phase (-(∑ coordinate, frequency coordinate * value coordinate))

theorem phase_sum (values : Coordinate → FiniteAdeles) :
    FiniteCharacter.phase (∑ coordinate, values coordinate) = ∏ coordinate, FiniteCharacter.phase (values coordinate) := by
  have identity (indices : Finset Coordinate) : FiniteCharacter.phase (∑ coordinate ∈ indices, values coordinate) =
      ∏ coordinate ∈ indices, FiniteCharacter.phase (values coordinate) := by
    induction indices using Finset.induction_on with
    | empty => simp only [Finset.sum_empty, Finset.prod_empty, FiniteCharacter.phase_zero]
    | @insert coordinate indices outside induction =>
      rw [Finset.sum_insert outside, Finset.prod_insert outside, FiniteCharacter.phase_add, induction]
  exact identity Finset.univ

theorem pairing_product (frequency value : Space) :
    pairing frequency value = ∏ coordinate, FiniteCharacter.phase (-(frequency coordinate * value coordinate)) := by
  rw [pairing, ← Finset.sum_neg_distrib, phase_sum]

theorem pairing_continuous (frequency : Space) : Continuous (pairing frequency) := by
  unfold pairing
  exact FiniteCharacter.phase_continuous.comp
    (continuous_finsetSum _ (fun coordinate _ => continuous_const.mul (continuous_apply coordinate))).neg

theorem pairing_norm (frequency value : Space) : ‖pairing frequency value‖ = 1 := FiniteCharacter.phase_norm _

def transform (function : Space → ℂ) (frequency : Space) : ℂ :=
  ∫ value, pairing frequency value * function value ∂measure

def tensor (functions : Coordinate → FiniteAdeles → ℂ) (value : Space) : ℂ :=
  ∏ coordinate, functions coordinate (value coordinate)

theorem transform_tensor (functions : Coordinate → FiniteAdeles → ℂ) (frequency : Space) :
    transform (tensor functions) frequency = ∏ coordinate, FiniteFourier.transform (functions coordinate) (frequency coordinate) := by
  unfold transform tensor
  simp only [pairing_product, ← Finset.prod_mul_distrib]
  exact integral_fintype_prod_eq_prod (μ := fun _ => finiteMeasure)
    (fun coordinate value => FiniteCharacter.phase (-(frequency coordinate * value)) * functions coordinate value)

def box (scales : Coordinate → FiniteAdelesˣ) (offset : Space) : Set Space :=
  Set.univ.pi (fun coordinate => FiniteFourier.coset (scales coordinate) (offset coordinate))

def boxTest (scales : Coordinate → FiniteAdelesˣ) (offset : Space) : Space → ℂ :=
  tensor (fun coordinate => (FiniteFourier.coset (scales coordinate) (offset coordinate)).indicator (fun _ => (1 : ℂ)))

theorem box_compact (scales : Coordinate → FiniteAdelesˣ) (offset : Space) : IsCompact (box scales offset) := by
  convert isCompact_pi_infinite (fun coordinate => FiniteFourier.coset_compact (scales coordinate) (offset coordinate)) using 1
  ext value
  simp [box]

theorem boxTest_continuous (scales : Coordinate → FiniteAdelesˣ) (offset : Space) : Continuous (boxTest scales offset) := by
  unfold boxTest tensor
  exact continuous_finsetProd _ (fun coordinate _ =>
    (FiniteFourierInversion.indicator_continuous (scales coordinate) (offset coordinate)).comp (continuous_apply coordinate))

theorem boxTest_indicator (scales : Coordinate → FiniteAdelesˣ) (offset : Space) :
    boxTest scales offset = (box scales offset).indicator (fun _ => (1 : ℂ)) := by
  funext value
  unfold boxTest tensor
  by_cases membership : value ∈ box scales offset
  · rw [Set.indicator_of_mem membership]
    apply Finset.prod_eq_one
    intro coordinate _
    exact Set.indicator_of_mem (membership coordinate (Set.mem_univ _)) _
  · rw [Set.indicator_of_notMem membership]
    have outside : ∃ coordinate, value coordinate ∉ FiniteFourier.coset (scales coordinate) (offset coordinate) := by
      simpa only [box, Set.mem_univ_pi, not_forall] using membership
    obtain ⟨coordinate, outside⟩ := outside
    exact Finset.prod_eq_zero (Finset.mem_univ coordinate) (Set.indicator_of_notMem outside _)

theorem boxTest_compactSupport (scales : Coordinate → FiniteAdelesˣ) (offset : Space) :
    HasCompactSupport (boxTest scales offset) := by
  rw [boxTest_indicator]
  exact HasCompactSupport.intro (box_compact scales offset) (fun _ outside => Set.indicator_of_notMem outside _)

theorem boxTest_integrable (scales : Coordinate → FiniteAdelesˣ) (offset : Space) :
    Integrable (boxTest scales offset) measure :=
  Integrable.fintype_prod (fun coordinate => FiniteFourierInversion.indicator_integrable (scales coordinate) (offset coordinate))

theorem transform_boxTest (scales : Coordinate → FiniteAdelesˣ) (offset frequency : Space) :
    transform (boxTest scales offset) frequency =
      ∏ coordinate, FiniteCharacter.phase (-(frequency coordinate * offset coordinate)) *
        if frequency coordinate * (scales coordinate).val ∈ Set.range integralEmbedding then
          (finiteMeasure.real (FiniteFourier.lattice (scales coordinate)) : ℂ) else 0 := by
  rw [boxTest, transform_tensor]
  exact Finset.prod_congr rfl (fun coordinate _ => FiniteFourier.transform_coset _ _ _)

theorem transform_boxTest_continuous (scales : Coordinate → FiniteAdelesˣ) (offset : Space) :
    Continuous (transform (boxTest scales offset)) := by
  change Continuous (fun frequency => transform (tensor _) frequency)
  simp only [transform_tensor]
  exact continuous_finsetProd _ (fun coordinate _ =>
    (FiniteFourierInversion.transform_continuous (scales coordinate) (offset coordinate)).comp (continuous_apply coordinate))

theorem transform_boxTest_integrable (scales : Coordinate → FiniteAdelesˣ) (offset : Space) :
    Integrable (transform (boxTest scales offset)) measure := by
  change Integrable (fun frequency => transform (tensor _) frequency) measure
  simp only [transform_tensor]
  exact Integrable.fintype_prod (fun coordinate =>
    FiniteFourierInversion.transform_integrable (scales coordinate) (offset coordinate))

theorem inversion_boxTest (scales : Coordinate → FiniteAdelesˣ) (offset frequency : Space) :
    transform (transform (boxTest scales offset)) frequency = boxTest scales offset (-frequency) := by
  have tensorEquality : transform (boxTest scales offset) =
      tensor (fun coordinate => FiniteFourier.transform
        ((FiniteFourier.coset (scales coordinate) (offset coordinate)).indicator (fun _ => (1 : ℂ)))) := by
    funext value
    exact transform_tensor _ _
  rw [tensorEquality, transform_tensor]
  unfold boxTest tensor
  apply Finset.prod_congr rfl
  intro coordinate _
  exact FiniteFourierInversion.inversion_coset _ _ _

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteRectangularFourier
