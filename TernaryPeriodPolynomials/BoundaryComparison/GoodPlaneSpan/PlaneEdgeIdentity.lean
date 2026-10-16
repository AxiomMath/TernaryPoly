module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Detect.GoodPlaneCup
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Detect.GoodPlaneGeneric
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Detect.GoodPlaneLevi
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Source.GoodPlaneSourceData
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Source.GoodPlaneDetect
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.PlanePeriodCore
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Period.Parity
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Period.Cocycle
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.ArithmeticGenerators

@[expose] public section


/-!
# The good-plane edge value of a cup-product class, exactly, in terms of the level-three period map

Good-plane analogue of the line-side exact-value identity used in
`Automorphic.DirectFinal` (`periodsRealized_of`, via
`Period.MemberRealized.memberRealized`), which identifies the bad-line edge of a cup-product source
class with (a sign of) the classical level-three period `levelPeriodMap (n+1) (-1) f`.

For a `PlaneLeviCocycle n` datum coming from a level-three Levi-cocycle datum `E`
(`A := E.toPlaneLeviCocycle`), with period formula `L3PlanePeriodFormula E f` for a classical
weight-`(n+1)` level-three cusp form `f`, and a two-cocycle `Z` of `ΛG` representing the cup
product of `gpCupOf A`'s potentials (`GoodPlaneCupData.Represents`), the good-plane edge value
`goodPlaneEdgeH2` of the class of `Z` is **exactly** `-(levelPeriodMap (n+1) (-1) f)`:

* `alpha_gpMu_mul_gpDelta`: the raw Levi-cocycle identity extracted from the proof of
  `notCoboundary_of_period` (`DetectGoodPlaneGeneric.lean`), isolated as a standalone lemma;
* `gpCupOf_leviDelta_eq`: rewrites `(gpCupOf A).leviDelta m` via that identity, exposing the
  crossed coboundary of the constant `A.α gpDelta 1`;
* `goodPlaneEdgeCocycle_apply_leviDelta`: the pointwise value of the edge cocycle of a `Kostant`
  relative lift is `c • D.leviDelta m` (linearity of `Phi n` applied to `edgeVal_eq`);
* `goodPlaneEdgeCocycle_cup_eq`: the resulting cocycle `goodPlaneEdgeCocycle (D.relative hZ)`
  equals `- levelPlus (n+1) (-1) (periodCocycle (n+1) (-1) f) -
    crossedBoundary (levelRep (n+1) (-1)) (E.α gpDelta 1)` exactly, as an equality of crossed
  cocycles;
* `goodPlaneEdgeH2_cup_period`: the final exact class-level value,
  `goodPlaneEdgeH2 hn (classOf ΛG (rationalCoefficientComponent n trivialCharacter) Z) =
    -(levelPeriodMap (n + 1) (-1) f)`.
-/

open Matrix GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.ArithmeticGenerators
open TernaryPeriodPolynomials.LevelThree.GoodPlaneFrame
open TernaryPeriodPolynomials.LevelThree.GoodPlaneModel
open TernaryPeriodPolynomials.LevelThree.GoodPlaneEdge2
open TernaryPeriodPolynomials.LevelThree.GoodPlaneEdge3
open TernaryPeriodPolynomials.LevelThree.GoodPlaneQuot (qcls qcls_eq_zero_iff qcls_add qcls_smul)
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds (levelRep)
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodParity (levelPlus levelPeriodMap levelPeriodMap_apply)
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodCocycle (S periodCocycle)
open TernaryPeriodPolynomials.Spectral.CuspReduction (cuspLevel cuspRes)
open TernaryPeriodPolynomials.Spectral.CuspOrbits (cuspFlag goodPlaneFrame)
open TernaryPeriodPolynomials.BoundaryFiniteness.IntegralFlags (rational)
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.LevelThreeSource
open TernaryPeriodPolynomials.EvenLevelThree

noncomputable section


namespace TernaryPeriodPolynomials.Argument.GoodPlaneSpan

variable {n : ℕ}

/-- `qcls` sends negation to negation, for the fixed representation `levelRep (n + 1) (-1)`
(definitional: both sides unfold through `Submodule.Quotient.mk`). -/
theorem qcls_neg_levelRep (z : crossedCocycles (levelRep (n + 1) (-1))) :
    qcls (levelRep (n + 1) (-1)) (-z) = - qcls (levelRep (n + 1) (-1)) z := rfl

/-- `qcls` sends subtraction to subtraction, for the fixed representation `levelRep (n + 1) (-1)`
(definitional: both sides unfold through `Submodule.Quotient.mk`). -/
theorem qcls_sub_levelRep (z z' : crossedCocycles (levelRep (n + 1) (-1))) :
    qcls (levelRep (n + 1) (-1)) (z - z') =
      qcls (levelRep (n + 1) (-1)) z - qcls (levelRep (n + 1) (-1)) z' := rfl

/-- **The raw Levi-cocycle identity**, extracted from the proof of `notCoboundary_of_period`
(`SourceConstruction.DetectGoodPlaneGeneric`): for any `PlaneLeviCocycle` datum `A` whose
Levi value at `gpDelta` does not see integral real translates (`hlev`), the value at
`gpMu m * gpDelta` splits as the value at `gpMu m` plus the `levelRep`-translate of the constant
`A.α gpDelta 1`. -/
theorem alpha_gpMu_mul_gpDelta (A : PlaneLeviCocycle n)
    (hlev : ∀ m : binaryArithmeticLevel, A.α gpDelta (atInfinity (gpMu m)) = A.α gpDelta 1)
    (m : binaryArithmeticLevel) :
    A.α (gpMu m * gpDelta) 1 =
      A.α (gpMu m) 1 + levelRep (n + 1) (-1) m (A.α gpDelta 1) := by
  have c2 := A.cocycle (gpMu m) gpDelta 1
  have e2 : binaryCohomologicalAction n (gpMu m) (A.α gpDelta) 1 =
      levelRep (n + 1) (-1) m (A.α gpDelta 1) := by
    unfold binaryCohomologicalAction
    rw [gp_normPower_int m.val, one_smul, one_mul, hlev m, binaryCoefficient_gpMu]
  rwa [e2] at c2

/-- **The Levi potential of the generic potentials**: `(gpCupOf A).leviDelta m` is
`A.α (gpMu m) 1` plus the crossed coboundary of the constant `A.α gpDelta 1`. -/
theorem gpCupOf_leviDelta_eq (A : PlaneLeviCocycle n)
    (hlev : ∀ m : binaryArithmeticLevel, A.α gpDelta (atInfinity (gpMu m)) = A.α gpDelta 1)
    (m : binaryArithmeticLevel) :
    (gpCupOf A).leviDelta m =
      A.α (gpMu m) 1 + (levelRep (n + 1) (-1) m (A.α gpDelta 1) - A.α gpDelta 1) := by
  rw [gpCupOf_leviDelta A m, alpha_gpMu_mul_gpDelta A hlev m]
  abel

/-- The pointwise value of the good-plane edge cocycle of a `Kostant`-scaled relative lift, in
terms of `GoodPlaneCupData.leviDelta`. -/
theorem goodPlaneEdgeCocycle_apply_leviDelta (D : GoodPlaneCupData n) (c : ℂ)
    (hK : KostantLaw n D.lam c)
    (Z : cocycles ΛG (rationalCoefficientComponent n trivialCharacter)) (hZ : D.Represents Z)
    (m : binaryArithmeticLevel) :
    (goodPlaneEdgeCocycle (D.relative hZ)).val m = c • D.leviDelta m := by
  rw [goodPlaneEdgeCocycle_apply, D.edgeVal_eq hZ hK m, map_smul]
  rfl

/-- **The good-plane edge cocycle of a cup-product class, exactly.** For `A := E.toPlaneLeviCocycle`
coming from a level-three datum `E` via a period formula for `f` (`L3PlanePeriodFormula`,
`l3pp_levelPlus_eq_alpha`), the good-plane edge cocycle of a two-cocycle `Z` representing the cup
product of `gpCupOf A` equals the negative of the extended period cocycle of `f` minus the
crossed coboundary of `E.α gpDelta 1`. -/
theorem goodPlaneEdgeCocycle_cup_eq {σ : CuspidalRepresentation} (E : LevelLeviCocycleData σ n)
    (f : S (n + 1)) (hα : L3PlanePeriodFormula E ⇑f)
    (Z : cocycles ΛG (rationalCoefficientComponent n trivialCharacter))
    (hZ : (gpCupOf E.toPlaneLeviCocycle).Represents Z) :
    goodPlaneEdgeCocycle ((gpCupOf E.toPlaneLeviCocycle).relative hZ) =
      - levelPlus (n + 1) (-1) (periodCocycle (n + 1) (-1) f) -
        crossedBoundary (levelRep (n + 1) (-1)) (E.α gpDelta 1) := by
  have hlev : ∀ m : binaryArithmeticLevel,
      E.α gpDelta (atInfinity (gpMu m)) = E.α gpDelta 1 := fun m =>
    alpha_atInfinity_level E gpDelta m.property
  apply Subtype.ext
  funext m
  have hcA : (goodPlaneEdgeCocycle ((gpCupOf E.toPlaneLeviCocycle).relative hZ)).val m =
      (-1 : ℂ) • (gpCupOf E.toPlaneLeviCocycle).leviDelta m :=
    goodPlaneEdgeCocycle_apply_leviDelta (gpCupOf E.toPlaneLeviCocycle) (-1)
      (gpCupOf_kostant E.toPlaneLeviCocycle) Z hZ m
  have hld : (gpCupOf E.toPlaneLeviCocycle).leviDelta m =
      E.α (gpMu m) 1 + (levelRep (n + 1) (-1) m (E.α gpDelta 1) - E.α gpDelta 1) :=
    gpCupOf_leviDelta_eq E.toPlaneLeviCocycle hlev m
  have hp : (levelPlus (n + 1) (-1) (periodCocycle (n + 1) (-1) f)).val m = E.α (gpMu m) 1 :=
    l3pp_levelPlus_eq_alpha E f hα m
  show (goodPlaneEdgeCocycle ((gpCupOf E.toPlaneLeviCocycle).relative hZ)).val m =
    - (levelPlus (n + 1) (-1) (periodCocycle (n + 1) (-1) f)).val m -
      (levelRep (n + 1) (-1) m (E.α gpDelta 1) - E.α gpDelta 1)
  rw [hcA, hld, hp]
  module

/-- **The good-plane edge value of a cup-product class, exactly.** Combines
`goodPlaneEdgeCocycle_cup_eq` with `GoodPlaneCupData.goodPlaneEdgeH2_cup`: the class of `Z` has
good-plane edge value exactly `-(levelPeriodMap (n + 1) (-1) f)`. -/
theorem goodPlaneEdgeH2_cup_period {σ : CuspidalRepresentation} (hn : 0 < n)
    (E : LevelLeviCocycleData σ n) (f : S (n + 1)) (hα : L3PlanePeriodFormula E ⇑f)
    (Z : cocycles ΛG (rationalCoefficientComponent n trivialCharacter))
    (hZ : (gpCupOf E.toPlaneLeviCocycle).Represents Z) :
    goodPlaneEdgeH2 hn (classOf ΛG (rationalCoefficientComponent n trivialCharacter) Z) =
      - (levelPeriodMap (n + 1) (-1) f) := by
  have hlpm : levelPeriodMap (n + 1) (-1) f =
      qcls (levelRep (n + 1) (-1)) (levelPlus (n + 1) (-1) (periodCocycle (n + 1) (-1) f)) := by
    rw [levelPeriodMap_apply, Submodule.mkQ_apply]
    rfl
  have hz0 : qcls (levelRep (n + 1) (-1))
      (crossedBoundary (levelRep (n + 1) (-1)) (E.α gpDelta 1)) = 0 := by
    rw [qcls_eq_zero_iff]
    exact ⟨E.α gpDelta 1, rfl⟩
  rw [(gpCupOf E.toPlaneLeviCocycle).goodPlaneEdgeH2_cup hn hZ,
    goodPlaneEdgeCocycle_cup_eq E f hα Z hZ, qcls_sub_levelRep, hz0, qcls_neg_levelRep, sub_zero,
    ← hlpm]

end TernaryPeriodPolynomials.Argument.GoodPlaneSpan
