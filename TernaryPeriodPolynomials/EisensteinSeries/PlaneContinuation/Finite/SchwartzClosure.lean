module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Rational.ThetaDecay

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLatticeCosets (latticeSubgroup latticeSubgroup_mem)
open scoped Classical

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteSchwartzClosure

open FiniteRectangularFourier

instance measure_isAddHaar : measure.IsAddHaarMeasure :=
  inferInstanceAs ((Measure.pi (fun _ : Coordinate => finiteMeasure)).IsAddHaarMeasure)

theorem weighted_integrable (function : Space → ℂ) (integrable : Integrable function measure) (frequency : Space) :
    Integrable (fun value => pairing frequency value * function value) measure :=
  integrable.bdd_mul (pairing_continuous frequency).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun value => (pairing_norm frequency value).le))

theorem transform_sum {Index : Type*} (indices : Finset Index) (functions : Index → Space → ℂ)
    (integrable : ∀ index ∈ indices, Integrable (functions index) measure) (frequency : Space) :
    transform (fun value => ∑ index ∈ indices, functions index value) frequency =
      ∑ index ∈ indices, transform (functions index) frequency := by
  unfold transform
  simp only [Finset.mul_sum]
  exact integral_finsetSum indices (fun index membership => weighted_integrable _ (integrable index membership) frequency)

theorem transform_const_mul (scalar : ℂ) (function : Space → ℂ) (frequency : Space) :
    transform (fun value => scalar * function value) frequency = scalar * transform function frequency := by
  unfold transform
  have equality : (fun value => pairing frequency value * (scalar * function value)) =
      fun value => scalar * (pairing frequency value * function value) := by funext value; ring
  rw [equality, integral_const_mul]

theorem latticeSubgroup_compact (scale : FiniteAdelesˣ) : IsCompact (latticeSubgroup scale : Set Space) := by
  convert isCompact_pi_infinite (fun _ : Coordinate => FiniteFourier.lattice_compact scale) using 1
  ext value
  exact latticeSubgroup_mem scale value

theorem transform_box_outside (scale : FiniteAdelesˣ) (offset frequency : Space)
    (outside : frequency ∉ latticeSubgroup scale⁻¹) :
    transform (boxTest (fun _ => scale) offset) frequency = 0 := by
  have outsideCoordinate : ∃ coordinate, frequency coordinate ∉ FiniteFourier.lattice scale⁻¹ := by
    simpa only [latticeSubgroup_mem, not_forall] using outside
  obtain ⟨coordinate, notIn⟩ := outsideCoordinate
  have nonintegral : frequency coordinate * scale.val ∉ Set.range integralEmbedding :=
    fun h => notIn ((FiniteFourierInversion.dual_mem scale _).mp h)
  rw [transform_boxTest]
  apply Finset.prod_eq_zero (Finset.mem_univ coordinate)
  rw [ite_eq_right nonintegral, mul_zero]

theorem transform_box_compactSupport (scale : FiniteAdelesˣ) (offset : Space) :
    HasCompactSupport (transform (boxTest (fun _ => scale) offset)) :=
  HasCompactSupport.intro (latticeSubgroup_compact scale⁻¹) (fun _ outside => transform_box_outside scale offset _ outside)

theorem expansion_transform (scale : FiniteAdelesˣ) (function : Space → ℂ) (compactSupport : HasCompactSupport function)
    (invariant : ∀ shift ∈ latticeSubgroup scale, ∀ value, function (shift + value) = function value) :
    ∃ indices : Finset (Space ⧸ latticeSubgroup scale),
      function = (fun value => ∑ coset ∈ indices, function coset.out * boxTest (fun _ => scale) coset.out value) ∧
      transform function = (fun frequency => ∑ coset ∈ indices, function coset.out * transform (boxTest (fun _ => scale) coset.out) frequency) := by
  obtain ⟨indices, expansion⟩ := FiniteLatticeCosets.expansion scale function compactSupport invariant
  have equality : function = fun value => ∑ coset ∈ indices, function coset.out * boxTest (fun _ => scale) coset.out value :=
    funext expansion
  refine ⟨indices, equality, ?_⟩
  funext frequency
  conv_lhs => rw [equality]
  rw [transform_sum indices _ (fun coset _ => (boxTest_integrable (fun _ => scale) coset.out).const_mul _)]
  exact Finset.sum_congr rfl (fun coset _ => transform_const_mul _ _ _)

theorem continuous_of_periodic (scale : FiniteAdelesˣ) (function : Space → ℂ) (compactSupport : HasCompactSupport function)
    (invariant : ∀ shift ∈ latticeSubgroup scale, ∀ value, function (shift + value) = function value) :
    Continuous function := by
  obtain ⟨indices, equality, _⟩ := expansion_transform scale function compactSupport invariant
  rw [equality]
  exact continuous_finsetSum _ (fun coset _ => continuous_const.mul (boxTest_continuous (fun _ => scale) coset.out))

theorem transform_continuous (scale : FiniteAdelesˣ) (function : Space → ℂ) (compactSupport : HasCompactSupport function)
    (invariant : ∀ shift ∈ latticeSubgroup scale, ∀ value, function (shift + value) = function value) :
    Continuous (transform function) := by
  obtain ⟨indices, _, equality⟩ := expansion_transform scale function compactSupport invariant
  rw [equality]
  exact continuous_finsetSum _ (fun coset _ => continuous_const.mul (transform_boxTest_continuous (fun _ => scale) coset.out))

theorem transform_outside (scale : FiniteAdelesˣ) (function : Space → ℂ) (compactSupport : HasCompactSupport function)
    (invariant : ∀ shift ∈ latticeSubgroup scale, ∀ value, function (shift + value) = function value)
    (frequency : Space) (outside : frequency ∉ latticeSubgroup scale⁻¹) : transform function frequency = 0 := by
  obtain ⟨indices, _, equality⟩ := expansion_transform scale function compactSupport invariant
  rw [equality]
  apply Finset.sum_eq_zero
  intro coset _
  rw [transform_box_outside scale coset.out frequency outside, mul_zero]

theorem transform_compactSupport (scale : FiniteAdelesˣ) (function : Space → ℂ) (compactSupport : HasCompactSupport function)
    (invariant : ∀ shift ∈ latticeSubgroup scale, ∀ value, function (shift + value) = function value) :
    HasCompactSupport (transform function) :=
  HasCompactSupport.intro (latticeSubgroup_compact scale⁻¹)
    (fun _ outside => transform_outside scale function compactSupport invariant _ outside)

theorem transform_integrable (scale : FiniteAdelesˣ) (function : Space → ℂ) (compactSupport : HasCompactSupport function)
    (invariant : ∀ shift ∈ latticeSubgroup scale, ∀ value, function (shift + value) = function value) :
    Integrable (transform function) measure :=
  (transform_continuous scale function compactSupport invariant).integrable_of_hasCompactSupport
    (transform_compactSupport scale function compactSupport invariant)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteSchwartzClosure
