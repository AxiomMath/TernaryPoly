module

public import TernaryPeriodPolynomials.BoundaryComparison.GoodPlaneSpan.PlaneEdgeIdentity
public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.Global
public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.SourceCoordinate
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Detect.GoodPlaneGeneric
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Source.GoodPlaneSourceCusp
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Source.GoodPlaneSourceInduced
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.SourceSpace
public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs.CuspidalBoundary

@[expose] public section


/-!
# The good-plane edge value of a concrete source cocycle, exactly, via `cuspRes`/`goodPlaneEdge`

Connects `PlaneEdgeIdentity.goodPlaneEdgeH2_cup_period` (an exact `goodPlaneEdgeH2`-level identity
for a cocycle `Z` of `ΛG` representing a cup product) to the `goodPlaneEdge`/`cuspRes` form used by
`Assembly.lean`'s `GoodPlanePeriodsRealized`, via `cuspRes_classOf` (`Separation.Global`)
and the definitional identification of `psiG (classOf (cuspLevel .plane true) ...)` with
`classOf ΛG ... (conjCycle ...)` (the same defeq step used implicitly by the existing
nonvanishing proof `cuspRes_plane_true_ne_zero` in `DetectGoodPlaneCup.lean`, where
`apply D.edge_ne_zero ...` unifies with a goal stated via `psiG` directly).
-/

open Matrix GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.ArithmeticGenerators
open TernaryPeriodPolynomials.LevelThree.GoodPlaneFrame
open TernaryPeriodPolynomials.LevelThree.GoodPlaneModel
open TernaryPeriodPolynomials.LevelThree.GoodPlaneEdge2
open TernaryPeriodPolynomials.LevelThree.GoodPlaneEdge3
open TernaryPeriodPolynomials.LevelThree.GoodPlaneConj
open TernaryPeriodPolynomials.LevelThree.GoodPlaneQuot (qcls qcls_eq_zero_iff qcls_add qcls_smul)
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds (levelRep)
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodParity (levelPlus levelPeriodMap levelPeriodMap_apply)
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodCocycle (S periodCocycle)
open TernaryPeriodPolynomials.Spectral.CuspReduction (cuspLevel cuspRes CuspH2)
open TernaryPeriodPolynomials.Spectral.CuspOrbits (cuspFlag goodPlaneFrame)
open TernaryPeriodPolynomials.BoundaryFiniteness.IntegralFlags (rational)
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.LevelThreeSource
open TernaryPeriodPolynomials.EvenLevelThree
open TernaryPeriodPolynomials.Separation
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.SourceSpace

noncomputable section


namespace TernaryPeriodPolynomials.Argument.GoodPlaneSpan

variable {n : ℕ}

/-- `goodPlaneEdge` unfolds to `goodPlaneEdgeH2 ∘ psiG` pointwise (both sides reduce through
`LinearMap.comp`/`LinearEquiv.coe_toLinearMap`, definitionally). -/
theorem goodPlaneEdge_apply (hn : 0 < n) (ξ : CuspH2 n trivialCharacter .plane true) :
    goodPlaneEdge hn ξ = goodPlaneEdgeH2 hn (psiG (n := n) ξ) := rfl

/-- **The exact good-plane edge value of a concrete source cocycle `z`.** For `z` a cocycle of
`rationalLevel` at the good plane whose value at the triple `(1, gF * g, gF * (g * h))` (for the
flag `cuspFlag .plane true`) matches the raw cup-product formula of `gpCupOf E.toPlaneLeviCocycle`,
the `goodPlaneEdge` of its good Shapiro coordinate is exactly `-(levelPeriodMap (n+1) (-1) f)`. -/
theorem goodPlaneEdge_cuspRes_eq_period {σ : CuspidalRepresentation}
    (hn : 0 < n) (E : LevelLeviCocycleData σ n) (f : S (n + 1)) (hα : L3PlanePeriodFormula E ⇑f)
    (z : cocycles rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane))
    (hz : ∀ y : Fin 3 → RationalGL3,
      z.val.val (fun i => gF * y i) (cuspFlag .plane true) =
        rationalCoefficientComponent n trivialCharacter gF
          (((gpCupOf E.toPlaneLeviCocycle).l (y 2) - (gpCupOf E.toPlaneLeviCocycle).l (y 1))
            ((gpCupOf E.toPlaneLeviCocycle).a (y 1) - (gpCupOf E.toPlaneLeviCocycle).a (y 0)))) :
    goodPlaneEdge hn
        (cuspRes n trivialCharacter .plane true
          (classOf rationalLevel
            (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) z)) =
      - (levelPeriodMap (n + 1) (-1) f) := by
  rw [cuspRes_classOf trivialCharacter .plane true z, goodPlaneEdge_apply]
  have hZc : (gpCupOf E.toPlaneLeviCocycle).Represents (conjCycle
      (rationalCoefficientComponent n trivialCharacter) gF (cuspLevel .plane true) ΛG hH_conj
      (fixedPointCycle rationalLevel (rationalCoefficientComponent n trivialCharacter)
        (cuspFlag .plane true) z)) := by
    intro g h
    have e1 := hz ![1, g.val, g.val * h.val]
    exact (congrArg (rationalCoefficientComponent n trivialCharacter gF⁻¹) e1).trans
      (rho_gF_inv_apply _)
  have h4 : psiG (n := n) (classOf (cuspLevel .plane true)
      (rationalCoefficientComponent n trivialCharacter)
      (fixedPointCycle rationalLevel (rationalCoefficientComponent n trivialCharacter)
        (cuspFlag .plane true) z)) =
      classOf ΛG (rationalCoefficientComponent n trivialCharacter)
        (conjCycle (rationalCoefficientComponent n trivialCharacter) gF
          (cuspLevel .plane true) ΛG hH_conj
          (fixedPointCycle rationalLevel (rationalCoefficientComponent n trivialCharacter)
            (cuspFlag .plane true) z)) := rfl
  rw [h4]
  exact goodPlaneEdgeH2_cup_period hn E f hα _ hZc

/-- **The exact good-plane edge value of the concrete level-three source.** For `M : CohomologicalCuspData n`
and a Levi-cocycle datum `E` of `M.cusp` realizing a period formula for `f`, the good-plane
coordinate of the concrete adelic source `goodPlaneSource M.inducingData E` has `goodPlaneEdge`
value exactly `-(levelPeriodMap (n+1) (-1) f)`. This instantiates `goodPlaneEdge_cuspRes_eq_period`
at the concrete source, discharging its `hz` hypothesis via `evaluatedSource_realizes`,
`goodPlaneSource_rational_cusp` and `identityCupOf_goodPlane` (`M.inducingData.chi = trivialCharacter`
holds by `rfl`, since `CohomologicalCuspData.inducingData` is built with `trivialCharacter` directly). -/
theorem goodPlaneEdge_sourceCoordinate_eq_period (hn : 0 < n) (M : CohomologicalCuspData n)
    (E : LevelLeviCocycleData M.cusp n) (f : S (n + 1)) (hα : L3PlanePeriodFormula E ⇑f) :
    goodPlaneEdge hn
        (sourceCoordinate M.inducingData .plane true
          ⟨goodPlaneSource M.inducingData E,
            goodPlaneSource_isSourceCocycle_of_trivial M.inducingData E rfl⟩) =
      - (levelPeriodMap (n + 1) (-1) f) := by
  show goodPlaneEdge hn (cuspRes n trivialCharacter .plane true
    (classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane)
      (evaluatedSource M.inducingData .plane
        ⟨goodPlaneSource M.inducingData E,
          goodPlaneSource_isSourceCocycle_of_trivial M.inducingData E rfl⟩))) =
    - (levelPeriodMap (n + 1) (-1) f)
  apply goodPlaneEdge_cuspRes_eq_period hn E f hα
  intro y
  have hz := evaluatedSource_realizes M.inducingData .plane
    ⟨goodPlaneSource M.inducingData E,
      goodPlaneSource_isSourceCocycle_of_trivial M.inducingData E rfl⟩
  exact (hz (fun i => gF * y i) (planeFrameQ true)).trans
    ((goodPlaneSource_rational_cusp M.inducingData E (fun u => rfl) (fun i => gF * y i)).trans
      (identityCupOf_goodPlane (M.inducingData).chi rfl E.toPlaneLeviCocycle y))

end TernaryPeriodPolynomials.Argument.GoodPlaneSpan
