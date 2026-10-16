module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.PrimeLattice
public import Mathlib.MeasureTheory.Group.Measure

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open scoped ENNReal

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.PrimeMeasure

instance integralAdelesContinuousMul : ContinuousMul IntegralAdeles :=
  Topology.IsInducing.continuousMul integralEmbedding
    integralEmbedding_isOpenEmbedding.isEmbedding.isInducing

instance integralAdelesTopologicalAddGroup : IsTopologicalAddGroup IntegralAdeles :=
  Topology.IsInducing.isTopologicalAddGroup integralEmbedding
    integralEmbedding_isOpenEmbedding.isEmbedding.isInducing

instance integralAdelesMeasurableSpace : MeasurableSpace IntegralAdeles := borel IntegralAdeles

instance integralAdelesBorelSpace : BorelSpace IntegralAdeles := ⟨rfl⟩

theorem residue_kernel_index (prime : ℕ) (isPrime : prime.Prime) :
    (PrimeLattice.residue prime isPrime).toAddMonoidHom.ker.index = prime := by
  rw [AddSubgroup.index_ker,
    AddMonoidHom.range_eq_top_of_surjective _ (PrimeLattice.residue_surjective prime isPrime)]
  exact (Nat.card_congr AddSubgroup.topEquiv.toEquiv).trans (Nat.card_zmod prime)

theorem residue_kernel_set (prime : ℕ) (isPrime : prime.Prime) :
    ((PrimeLattice.residue prime isPrime).toAddMonoidHom.ker : Set IntegralAdeles) =
      Set.range (fun value : IntegralAdeles => (prime : IntegralAdeles) * value) := by
  ext value
  exact (PrimeLattice.residue_zero_iff prime isPrime value).trans (by
    constructor <;> rintro ⟨quotient, equality⟩ <;> exact ⟨quotient, equality⟩)

theorem residue_kernel_measurable (prime : ℕ) (isPrime : prime.Prime) :
    MeasurableSet
      ((PrimeLattice.residue prime isPrime).toAddMonoidHom.ker : Set IntegralAdeles) := by
  rw [residue_kernel_set prime isPrime]
  exact (isCompact_range (continuous_const.mul continuous_id)).isClosed.measurableSet

theorem prime_lattice_measure (prime : ℕ) (isPrime : prime.Prime) :
    (prime : ℝ≥0∞) * finiteMeasure
      (Set.range (fun value : IntegralAdeles =>
        integralEmbedding ((prime : IntegralAdeles) * value))) = 1 := by
  let integralMeasure : Measure IntegralAdeles := Measure.comap integralEmbedding finiteMeasure
  have embeddingMeasurable : MeasurableEmbedding integralEmbedding :=
    integralEmbedding_isOpenEmbedding.measurableEmbedding
  let : integralMeasure.IsAddLeftInvariant :=
    Measure.IsAddLeftInvariant.comap finiteMeasure
      (f := integralEmbedding.toAddMonoidHom) embeddingMeasurable
  let kernel := (PrimeLattice.residue prime isPrime).toAddMonoidHom.ker
  let : kernel.FiniteIndex := AddSubgroup.finiteIndex_iff.mpr (by
    rw [residue_kernel_index prime isPrime]
    exact isPrime.ne_zero)
  have indexMeasure := MeasureTheory.AddSubgroup.index_mul_measure kernel
    (residue_kernel_measurable prime isPrime) integralMeasure
  rw [residue_kernel_index prime isPrime] at indexMeasure
  change (prime : ℝ≥0∞) *
    (Measure.comap integralEmbedding finiteMeasure) (kernel : Set IntegralAdeles) =
      (Measure.comap integralEmbedding finiteMeasure) Set.univ at indexMeasure
  rw [embeddingMeasurable.comap_apply, embeddingMeasurable.comap_apply,
    Set.image_univ, finiteMeasure_integralLattice] at indexMeasure
  have imageEquality : integralEmbedding '' (kernel : Set IntegralAdeles) =
      Set.range (fun value : IntegralAdeles =>
        integralEmbedding ((prime : IntegralAdeles) * value)) := by
    rw [residue_kernel_set prime isPrime]
    ext value
    constructor
    · rintro ⟨integralValue, ⟨quotient, rfl⟩, rfl⟩
      exact ⟨quotient, rfl⟩
    · rintro ⟨quotient, rfl⟩
      exact ⟨(prime : IntegralAdeles) * quotient, ⟨quotient, rfl⟩, rfl⟩
  rw [imageEquality] at indexMeasure
  exact indexMeasure

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.PrimeMeasure
