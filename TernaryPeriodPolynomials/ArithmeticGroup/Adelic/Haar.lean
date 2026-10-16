module

public import TernaryPeriodPolynomials.ArithmeticGroup.Adelic.SecondCountable
public import TernaryPeriodPolynomials.ArithmeticGroup.Adelic.Integers
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.Algebra.Order.Monoid.Canonical.Basic
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Data.Nat.NthRoot.Defs
public import Mathlib.SetTheory.Cardinal.ENNReal
public import Mathlib.Topology.Order.AtTopBotIxx

@[expose] public section




/-! Actual adelic additive Haar measures, normalized by the compact open integral lattice. -/
noncomputable section
namespace GeneralEisenstein.Adelic
open IsDedekindDomain TopologicalSpace MeasureTheory
open scoped RestrictedProduct

/-- The actual integral finite adele embedding is an open topological embedding. -/
theorem integralEmbedding_isOpenEmbedding : Topology.IsOpenEmbedding integralEmbedding :=
  RestrictedProduct.isOpenEmbedding_structureMap
    (fun _ => Valued.isOpen_valuationSubring _)

/-- The actual integral finite adele lattice is compact. -/
theorem integralLattice_isCompact : IsCompact (Set.range integralEmbedding) :=
  isCompact_range integralEmbedding_isOpenEmbedding.continuous

/-- The actual integral finite adele lattice is open. -/
theorem integralLattice_isOpen : IsOpen (Set.range integralEmbedding) :=
  integralEmbedding_isOpenEmbedding.isOpen_range

/-- The actual integral finite adele lattice is a compact set with nonempty interior. -/
def finiteUnitCompact : PositiveCompacts FiniteAdeles where
  carrier := Set.range integralEmbedding
  isCompact' := integralLattice_isCompact
  interior_nonempty' := by
    rw [integralLattice_isOpen.interior_eq]
    exact ⟨0, 0, integralEmbedding.map_zero⟩

/-- The finite adele measurable sets are its actual Borel sets. -/
instance finiteAdelesMeasurableSpace : MeasurableSpace FiniteAdeles := borel FiniteAdeles

instance finiteAdelesBorelSpace : BorelSpace FiniteAdeles := ⟨rfl⟩

/-- The genuine finite additive Haar measure, normalized to give the integral lattice mass one. -/
def finiteMeasure : Measure FiniteAdeles := Measure.addHaarMeasure finiteUnitCompact

instance finiteMeasure_isAddHaar : finiteMeasure.IsAddHaarMeasure :=
  inferInstanceAs ((Measure.addHaarMeasure finiteUnitCompact).IsAddHaarMeasure)

instance finiteMeasure_sigmaFinite : SigmaFinite finiteMeasure :=
  inferInstanceAs (SigmaFinite (Measure.addHaarMeasure finiteUnitCompact))

/-- The normalization is an exact equality for the actual integral embedding range. -/
theorem finiteMeasure_integralLattice : finiteMeasure (Set.range integralEmbedding) = 1 :=
  Measure.addHaarMeasure_self

/-- Genuine full additive Haar measure: real Lebesgue measure times normalized finite Haar. -/
def adeleMeasure : Measure Adeles := (volume : Measure ℝ).prod finiteMeasure

instance adeleMeasure_isAddHaar : adeleMeasure.IsAddHaarMeasure :=
  inferInstanceAs (((volume : Measure ℝ).prod finiteMeasure).IsAddHaarMeasure)

instance adeleMeasure_sigmaFinite : SigmaFinite adeleMeasure :=
  inferInstanceAs (SigmaFinite ((volume : Measure ℝ).prod finiteMeasure))

/-- The genuine two-coordinate additive Haar measure used on both maximal unipotent radicals. -/
def radicalMeasure : Measure (Adeles × Adeles) := adeleMeasure.prod adeleMeasure

instance radicalMeasure_isAddHaar : radicalMeasure.IsAddHaarMeasure :=
  inferInstanceAs ((adeleMeasure.prod adeleMeasure).IsAddHaarMeasure)

instance radicalMeasure_sigmaFinite : SigmaFinite radicalMeasure :=
  inferInstanceAs (SigmaFinite (adeleMeasure.prod adeleMeasure))

/-- Actual translation invariance of the genuine radical integral. -/
theorem radicalIntegral_add_right {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Adeles × Adeles → E) (a : Adeles × Adeles) :
    (∫ x, f (x + a) ∂radicalMeasure) = ∫ x, f x ∂radicalMeasure :=
  integral_add_right_eq_self f a

end GeneralEisenstein.Adelic

end
