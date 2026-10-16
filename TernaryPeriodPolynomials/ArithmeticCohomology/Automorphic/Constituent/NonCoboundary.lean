module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Automorphic.Constituent.NonCoboundaryAux
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Source.GoodPlaneSourceData

@[expose] public section


/-!
# The Eichler cocycle of a representation with a weight gap is not a coboundary

For the level-three Levi cocycle datum `E` of a cuspidal representation `σ` with the weight gap
`WeightGap σ n`, a nonzero cocycle `E.α` (which vanishes on the orthogonal group) is not the
coboundary of a cuspidal polynomial-valued function.  This is the last clause of
`Cohomological σ n`.  The proof is `not_coboundary_of_weightGap_alpha`, which only uses
`E.α` and `E.orth`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.LevelThreeSource (LevelLeviCocycleData)

namespace TernaryPeriodPolynomials.Automorphic.Constituent

/-- **The Eichler cocycle is not a coboundary under the weight gap.** -/
theorem not_coboundary_of_weightGap {σ : CuspidalRepresentation} {n : ℕ}
    (E : LevelLeviCocycleData σ n) (gap : WeightGap σ n) (hne : ∃ g x, E.α g x ≠ 0) :
    ¬ ∃ v : BinaryAdelicGL → Binary.HomogeneousPoly (n + 1),
      BinaryValues σ n v ∧
        ∀ g x, E.α g x = binaryCohomologicalAction n g v x - v x :=
  not_coboundary_of_weightGap_alpha E.α E.orth gap hne

end TernaryPeriodPolynomials.Automorphic.Constituent
