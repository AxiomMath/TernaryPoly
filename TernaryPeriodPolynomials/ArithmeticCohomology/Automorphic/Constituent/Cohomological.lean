module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Automorphic.Constituent.DistinguishedVector
public import TernaryPeriodPolynomials.ArithmeticCohomology.Automorphic.Constituent.Stages
public import TernaryPeriodPolynomials.ArithmeticCohomology.Automorphic.Constituent.WeightGap
public import TernaryPeriodPolynomials.ArithmeticCohomology.Automorphic.Constituent.InputGeneric
public import TernaryPeriodPolynomials.ArithmeticCohomology.Automorphic.Constituent.LeviToCohomological
public import TernaryPeriodPolynomials.ArithmeticCohomology.Automorphic.Constituent.NonCoboundary
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.WtPlanePeriodVector
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Injective.Main

@[expose] public section


/-!
# The cuspidal constituents of the Bergman model are cohomological

For `n ≥ 3` and a constituent `c : Piece n`, the distinguished vector `Piece.vec` of
`c.cusp hn` has rotation weight `-(n + 3)`, is fixed by the level group and, by the weight gap,
is holomorphic: it is the input `Piece.input` of the weight-generic Eichler construction.
The Eichler cocycle `lteDataWt` of this input is not identically zero, for otherwise the Levi
period class vanishes and Eichler–Shimura injectivity (`levelPeriodMap_injective_goodPlane`)
forces the vector to vanish; and it is not a coboundary, by the weight gap
(`not_coboundary_of_weightGap`).  Hence `Piece.cohomological`, and the paper datum
`Piece.cuspData` of the constituent.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.AnalyticClasses
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.EvenLevelThree

namespace TernaryPeriodPolynomials.Automorphic.Constituent

/-- **The distinguished vector of a classical level-three input lies in the classical vectors**:
its scalar realization is holomorphic. -/
theorem l3_vector_mem_classicalWt {σ : CuspidalRepresentation} {n : ℕ} (I : L3InputWt σ n)
    (stages : AnalyticScalar.ContinuousStages σ) :
    I.vector ∈ levelThreeClassicalVectorsWt σ I.wt := by
  refine ⟨I.vector_level, I.rotation, UpperHalfPlane.mdifferentiable_iff.mpr ?_⟩
  apply (cuspScalarWeightedRealization_holomorphicWt σ stages I.wt I.vector I.fixedLevel
    I.holomorphic 1).congr
  intro point positive
  rw [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos positive]
  rfl

/-- **The weight gap of the cuspidal representation of a constituent**, from the weight gap of the
Bergman model. -/
theorem Piece.gap {n : ℕ} (hn : 3 ≤ n) (c : Piece n) : WeightGap (c.cusp hn) n := by
  unfold Piece.cusp
  exact weightGap_cyclicOfLE (bergmanModel n) _ _ _ _ c.simple.le_typeSubspace c.simple c.mem
    c.ne

/-- **The Eichler input of the distinguished vector of a constituent.** -/
def Piece.input {n : ℕ} (hn : 3 ≤ n) (c : Piece n) : L3InputWt (c.cusp hn) n :=
  L3InputWt.ofGap (Piece.gap hn c) (Piece.central_positive hn c)
    (Piece.cusp3 hn c) (-((n : ℤ) + 3)) rfl
    ⟨Piece.vec hn c, Piece.vec_smooth hn c⟩ (Piece.vec_level hn c)
    (Piece.vec_rotation hn c)

/-- **The distinguished vector of a constituent has a holomorphic scalar function**: it lies in
the classical level-three vectors of weight `-(n + 3)`. -/
theorem Piece.vec_classical {n : ℕ} (hn : 3 ≤ n) (c : Piece n) :
    (⟨Piece.vec hn c, Piece.vec_smooth hn c⟩ : (c.cusp hn).smooth) ∈
      levelThreeClassicalVectorsWt (c.cusp hn) (-((n : ℤ) + 3)) :=
  l3_vector_mem_classicalWt (Piece.input hn c) (Piece.stages hn c)

/-- **The cuspidal constituents of the Bergman model are cohomological.** -/
theorem Piece.cohomological {n : ℕ} (hn : 3 ≤ n) (c : Piece n) :
    Cohomological (c.cusp hn) n := by
  have hne : ∃ (g : BinaryRealGL) (x : BinaryAdelicGL),
      (lteDataWt (Piece.input hn c) (Piece.stages hn c)).α g x ≠ 0 := by
    by_contra h
    have hzero : ∀ (g : BinaryRealGL) (x : BinaryAdelicGL),
        (lteDataWt (Piece.input hn c) (Piece.stages hn c)).α g x = 0 :=
      fun g x => by_contra fun hx => h ⟨g, x, hx⟩
    have hv := l3PlanePeriod_vector_eq_zeroWt (Piece.input hn c) (Piece.stages hn c)
      (LevelThreeInjective.Main.levelPeriodMap_injective_goodPlane n)
      ⟨0, fun A => (hzero _ _).trans (by simp)⟩
    have hv' : Piece.vec hn c = 0 := congrArg Subtype.val hv
    exact c.ne (congrArg (c.toBergman hn) hv')
  exact cohomological_of_leviData _
    (not_coboundary_of_weightGap _ (Piece.gap hn c) hne)

/-- **The paper datum of a constituent**: its cuspidal representation with the cohomological
witness. -/
def Piece.cuspData {n : ℕ} (hn : 3 ≤ n) (c : Piece n) : CohomologicalCuspData n :=
  ⟨c.cusp hn, Piece.cohomological hn c⟩

end TernaryPeriodPolynomials.Automorphic.Constituent

end
