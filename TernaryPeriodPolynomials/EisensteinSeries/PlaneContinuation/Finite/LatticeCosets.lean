module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Compact.CosetExpansion

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz
open scoped Classical

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLatticeCosets

abbrev Space := FiniteRectangularFourier.Space

def latticeSubgroup (scale : FiniteAdelesˣ) : AddSubgroup Space where
  carrier := AdelicRationalScaling.finiteBox scale
  zero_mem' := by
    intro coordinate _
    exact ⟨0, by simp⟩
  add_mem' := by
    intro first second firstMembership secondMembership coordinate _
    obtain ⟨firstIntegral, firstEquality⟩ := firstMembership coordinate (Set.mem_univ _)
    obtain ⟨secondIntegral, secondEquality⟩ := secondMembership coordinate (Set.mem_univ _)
    dsimp only at firstEquality secondEquality
    refine ⟨firstIntegral + secondIntegral, ?_⟩
    change scale.val * integralEmbedding (firstIntegral + secondIntegral) = first coordinate + second coordinate
    rw [map_add, mul_add, firstEquality, secondEquality]
  neg_mem' := by
    intro value membership coordinate _
    obtain ⟨integral, equality⟩ := membership coordinate (Set.mem_univ _)
    dsimp only at equality
    refine ⟨-integral, ?_⟩
    change scale.val * integralEmbedding (-integral) = -(value coordinate)
    rw [map_neg, mul_neg, equality]

theorem latticeSubgroup_mem (scale : FiniteAdelesˣ) (value : Space) :
    value ∈ latticeSubgroup scale ↔ ∀ coordinate, value coordinate ∈ FiniteFourier.lattice scale := by
  change value ∈ Set.univ.pi (fun _ => FiniteFourier.lattice scale) ↔ _
  exact Set.mem_univ_pi

theorem latticeSubgroup_open (scale : FiniteAdelesˣ) : IsOpen (latticeSubgroup scale : Set Space) := by
  have equality : (latticeSubgroup scale : Set Space) =
      ⋂ coordinate : Coordinate, (fun value : Space => value coordinate) ⁻¹' FiniteFourier.lattice scale := by
    ext value
    simp only [Set.mem_iInter, Set.mem_preimage, latticeSubgroup_mem, SetLike.mem_coe]
  rw [equality]
  exact isOpen_iInter_of_finite (fun coordinate => (FiniteFourier.lattice_open scale).preimage (continuous_apply coordinate))

theorem class_mem_box (scale : FiniteAdelesˣ) (coset : Space ⧸ latticeSubgroup scale) (value : Space) :
    (QuotientAddGroup.mk value : Space ⧸ latticeSubgroup scale) = coset ↔
      value ∈ FiniteRectangularFourier.box (fun _ => scale) coset.out := by
  have outEquality : (QuotientAddGroup.mk coset.out : Space ⧸ latticeSubgroup scale) = coset := Quotient.out_eq' coset
  calc
    _ ↔ (QuotientAddGroup.mk value : Space ⧸ latticeSubgroup scale) = QuotientAddGroup.mk coset.out := by rw [outEquality]
    _ ↔ value - coset.out ∈ latticeSubgroup scale := QuotientAddGroup.eq_iff_sub_mem
    _ ↔ _ := by
      simp only [latticeSubgroup_mem, Pi.sub_apply, FiniteRectangularFourier.box,
        Set.mem_univ_pi, FiniteFourierInversion.coset_mem]

theorem expansion (scale : FiniteAdelesˣ) (function : Space → ℂ) (compactSupport : HasCompactSupport function)
    (invariant : ∀ shift ∈ latticeSubgroup scale, ∀ value, function (shift + value) = function value) :
    ∃ indices : Finset (Space ⧸ latticeSubgroup scale), ∀ value,
      function value = ∑ coset ∈ indices, function coset.out *
        FiniteRectangularFourier.boxTest (fun _ => scale) coset.out value := by
  obtain ⟨indices, expansion⟩ := CompactCosetExpansion.expansion (latticeSubgroup scale)
    (latticeSubgroup_open scale) function compactSupport invariant
  refine ⟨indices, fun value => ?_⟩
  rw [expansion value]
  apply Finset.sum_congr rfl
  intro coset _
  rw [FiniteRectangularFourier.boxTest_indicator]
  by_cases equality : (QuotientAddGroup.mk value : Space ⧸ latticeSubgroup scale) = coset
  · rw [ite_eq_left equality, Set.indicator_of_mem ((class_mem_box scale coset value).mp equality), mul_one]
  · rw [ite_eq_right equality, Set.indicator_of_notMem (fun h => equality ((class_mem_box scale coset value).mpr h)), mul_zero]

theorem tensor_expansion (realTest : SchwartzMap RealSpace ℂ) (scale : FiniteAdelesˣ)
    (function : Space → ℂ) (compactSupport : HasCompactSupport function)
    (invariant : ∀ shift ∈ latticeSubgroup scale, ∀ value, function (shift + value) = function value) :
    ∃ indices : Finset (Space ⧸ latticeSubgroup scale),
      AdelicRectangularFourier.tensor realTest function = fun value =>
        ∑ coset ∈ indices, AdelicRectangularFourier.tensor (function coset.out • realTest)
          (FiniteRectangularFourier.boxTest (fun _ => scale) coset.out) value := by
  obtain ⟨indices, expansion⟩ := expansion scale function compactSupport invariant
  refine ⟨indices, funext (fun value => ?_)⟩
  rw [AdelicRectangularFourier.tensor, expansion value.2, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro coset _
  simp only [AdelicRectangularFourier.tensor, smul_apply, smul_eq_mul]
  ring

theorem poisson_hasSum (realTest : SchwartzMap RealSpace ℂ) (scale : ℚˣ)
    (function : Space → ℂ) (compactSupport : HasCompactSupport function)
    (invariant : ∀ shift ∈ latticeSubgroup (FiniteLatticeMeasure.rationalScale scale),
      ∀ value, function (shift + value) = function value) :
    HasSum (fun rational : Coordinate → ℚ =>
      AdelicRectangularFourier.transform (AdelicRectangularFourier.tensor realTest function) (UnitBoxPoisson.rationalPoint rational))
      (∑' rational : Coordinate → ℚ,
        AdelicRectangularFourier.tensor realTest function (UnitBoxPoisson.rationalPoint rational)) := by
  obtain ⟨indices, equality⟩ := tensor_expansion realTest (FiniteLatticeMeasure.rationalScale scale) function compactSupport invariant
  rw [equality]
  exact FiniteSumPoisson.boxes_poisson_hasSum indices (fun coset => function coset.out • realTest) (fun _ => scale) (fun coset => coset.out)

theorem summable (realTest : SchwartzMap RealSpace ℂ) (scale : ℚˣ)
    (function : Space → ℂ) (compactSupport : HasCompactSupport function)
    (invariant : ∀ shift ∈ latticeSubgroup (FiniteLatticeMeasure.rationalScale scale),
      ∀ value, function (shift + value) = function value) :
    Summable (fun rational : Coordinate → ℚ =>
      AdelicRectangularFourier.tensor realTest function (UnitBoxPoisson.rationalPoint rational)) := by
  obtain ⟨indices, equality⟩ := tensor_expansion realTest (FiniteLatticeMeasure.rationalScale scale) function compactSupport invariant
  rw [equality]
  exact summable_sum (fun coset _ => RationalBoxPoisson.summable (function coset.out • realTest) scale coset.out)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLatticeCosets
