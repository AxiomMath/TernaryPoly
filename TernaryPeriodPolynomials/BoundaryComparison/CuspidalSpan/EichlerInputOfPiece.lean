module

public import TernaryPeriodPolynomials.BoundaryComparison.CuspidalSpan.ReynoldsPreservation
public import TernaryPeriodPolynomials.BoundaryComparison.CuspidalSpan.SphericalSupply
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.L3EichlerMain
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.CentralAction
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.WtForm
public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs.CuspidalBoundary

@[expose] public section


/-!
# An `EichlerInput` from a `SumIdentity` piece

`SumIdentity.lean`'s `sumIdentity` writes a nonzero level-one cusp form `f` as a sum, over a list
of pieces `p : Σ D : CohomologicalCuspData n, levelThreeClassicalVectorsWt D.cusp (-((n : ℤ) + 3))`, of
classical realizations of `reynoldsAverage p.1.cusp p.2.1`, and guarantees some piece has
`reynoldsAverage p.1.cusp p.2.1 ≠ 0`. This file packages such a piece as a full
`EichlerInput p.1.cusp n` (`AxiomCodeSourceConstruction/EichlerEquivariance.lean`), the input of
`exists_eichlerCocycle` (`AxiomCodeSourceConstruction/EichlerCocycle.lean`), by combining:

* `vector_spherical`: `reynoldsAverage_spherical` (`ReynoldsPreservation.lean`) applied to
  `leviFixed_of_mem_levelThreeValues` (`SphericalSupply.lean`), using the piece's own
  `levelThreeValues` membership (`AxiomCodeEvenLevelThree/WtForm.lean`'s
  `levelThreeClassicalVectorsWt` carrier, first component).
* `rotation`: `reynoldsAverage_rotation` (`ReynoldsPreservation.lean`) applied to the piece's own
  rotation eigencondition (the carrier's second component), transported along the arithmetic
  identity `2 * halfWeight = -(n + 3)` from `n = 2 * m + 1`.
* `holomorphic`: the line side's own **generic, "no level hypothesis"** `l3_holomorphic`
  (`AxiomCodeSourceConstruction/L3EichlerMain.lean`) applied to the piece's rotation eigencondition
  *before* averaging, transported through averaging by `reynoldsAverage_holomorphicOrbit`
  (`ReynoldsPreservation.lean`). `l3_holomorphic` needs only `Cohomological D.cusp n`, `halfWeight`,
  and the rotation eigencondition on an arbitrary smooth vector — it does not need, and this file
  does not use, `levelThreeClassicalVectorsWt`'s own `MDifferentiable` carrier component.
* `central_positive`: `cohomological_centralCharacter_positive`
  (`SphericalDetection/BinaryCentralAction.lean`), a property of the representation `D.cusp` alone,
  independent of the vector.
-/

noncomputable section


namespace TernaryPeriodPolynomials.Argument.CuspidalSpan

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.SourceConstruction (EichlerInput l3_holomorphic)
open TernaryPeriodPolynomials.EvenLevelThree (levelThreeClassicalVectorsWt)

/-- The `EichlerInput D.cusp n` built from a `levelThreeClassicalVectorsWt` piece with nonzero
Reynolds average, for `n = 2 * m + 1`. The companion `SumIdentity.lean` piece supplies exactly
`D`, `v`, and (when its global cusp form is nonzero) the nonvanishing hypothesis `hne`. -/
def eichlerInputOfPiece {n m : ℕ} (hm : n = 2 * m + 1) (D : CohomologicalCuspData n)
    (v : levelThreeClassicalVectorsWt D.cusp (-((n : ℤ) + 3)))
    (hne : reynoldsAverage D.cusp v.1 ≠ 0) :
    EichlerInput D.cusp n := by
  have hw : 2 * (-((m : ℤ) + 2)) = -((n : ℤ) + 3) := by rw [hm]; push_cast; ring
  have hrot : ∀ angle : Circle, D.cusp.π (atInfinity (binaryRotations angle)) v.1.val =
      (angle : ℂ) ^ (2 * (-((m : ℤ) + 2))) • v.1.val := by
    rw [hw]; exact v.2.2.1
  refine
    { central_positive := cohomological_centralCharacter_positive D.cusp D.cohomological
      halfWeight := -((m : ℤ) + 2)
      weight := hw
      vector := reynoldsAverage D.cusp v.1
      vector_ne := hne
      vector_spherical :=
        reynoldsAverage_spherical D.cusp v.1 (leviFixed_of_mem_levelThreeValues D.cusp v.1 v.2.1)
      rotation := ?_
      holomorphic := reynoldsAverage_holomorphicOrbit D.cusp (-((m : ℤ) + 2)) v.1
        (l3_holomorphic D.cohomological (-((m : ℤ) + 2)) hw v.1 hrot) }
  rw [hw]
  exact reynoldsAverage_rotation D.cusp (-((n : ℤ) + 3)) v.1 v.2.2.1

end TernaryPeriodPolynomials.Argument.CuspidalSpan
