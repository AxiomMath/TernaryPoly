module

public import TernaryPeriodPolynomials.ArithmeticGroup.Adelic.Ring
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.Analysis.Normed.Field.ProperSpace
public import Mathlib.Analysis.Normed.MulAction

@[expose] public section




/-! Actual local compactness and Hausdorff topology of the rational finite and full adeles. -/
noncomputable section
namespace GeneralEisenstein.Adelic
open IsDedekindDomain
open scoped RestrictedProduct

/-- Each actual finite completion of the rationals is locally compact via its genuine p-adic
continuous algebra equivalence. -/
instance finiteCompletionLocallyCompact (v : FinitePlace) : LocallyCompactSpace (v.adicCompletion ℚ) := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).property⟩
  exact (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toHomeomorph.locallyCompactSpace_iff.mpr inferInstance

/-- The actual integral valuation subring at every finite rational place is compact. -/
instance finiteIntegersCompact (v : FinitePlace) : CompactSpace (v.adicCompletionIntegers ℚ) := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).property⟩
  let : Algebra ℤ (v.adicCompletionIntegers ℚ) := Ring.toIntAlgebra _
  exact (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toHomeomorph.symm.compactSpace

/-- The genuine restricted product of rational finite completions is Hausdorff. -/
instance finiteAdelesT2 : T2Space FiniteAdeles :=
  inferInstanceAs (T2Space (Πʳ v : FinitePlace, [v.adicCompletion ℚ, v.adicCompletionIntegers ℚ]))

/-- The genuine finite adele ring is locally compact with its actual restricted-product topology. -/
instance finiteAdelesLocallyCompact : LocallyCompactSpace FiniteAdeles := by
  let : Fact (∀ v : FinitePlace, IsOpen (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ))) :=
    ⟨fun _ => Valued.isOpen_valuationSubring _⟩
  exact inferInstanceAs (LocallyCompactSpace
    (Πʳ v : FinitePlace, [v.adicCompletion ℚ, v.adicCompletionIntegers ℚ]))

/-- The full rational adele ring is Hausdorff in the genuine product topology. -/
instance adelesT2 : T2Space Adeles := inferInstanceAs (T2Space (ℝ × FiniteAdeles))

/-- The full rational adele ring is locally compact in the genuine product topology. -/
instance adelesLocallyCompact : LocallyCompactSpace Adeles :=
  inferInstanceAs (LocallyCompactSpace (ℝ × FiniteAdeles))

end GeneralEisenstein.Adelic

end
