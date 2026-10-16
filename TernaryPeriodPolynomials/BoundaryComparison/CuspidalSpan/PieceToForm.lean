module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Eichler.Equivariance
public import TernaryPeriodPolynomials.ArithmeticCohomology.EdgeControl.PrimitiveControl
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Source.LevelThreeEichlerMain
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.WtFactor
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.WtOrbit
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.WtScalar
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.WtScalarHolomorphic
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.HolomorphicOrbit
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Scalar.ImageEigenform
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Scalar.HeckeImage
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Binary.Level
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Analytic.Scalar
public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs.Automorphic

@[expose] public section


/-!
# From an `EichlerInput` to a bundled classical cusp form

Closes the "classical form ⟹ automorphic cuspidal datum" gap not closed by
`ReynoldsPreservation.lean`'s docstring ("What this does not close"): every `EichlerInput`
(`AxiomCodeSourceConstruction/EichlerEquivariance.lean`) built from a `Cohomological` datum
(`Definitions/Automorphic.lean`) carries a genuine level-one holomorphic `CuspForm` realizing its
vector via `cuspScalarWeightedLinear` (`EichlerInput.exists_classicalForm`).

The proof chains together, at `wt := 2 * I.halfWeight`:

* `cuspWeightedAffineOrbitWt_two_mul` / `holomorphicOrbitWt_of_holomorphicOrbit`: the vector-orbit
  "Wt vs. plain" bridge, mirroring `AxiomCodeEvenLevelThree/WtScalar.lean`'s own scalar bridge
  `cuspScalarWeightedRealizationWt_two_mul`, both proved from `WtFactor.lean`'s `wtFactor_even`.
  * `AxiomCodeLevelThreeSource/LevelThreeEichlerMain.lean`'s `levelThreeStages`, which — despite its
  name — needs only `Cohomological σ n` (not any level-three-specific hypothesis), to supply
  `AnalyticScalar.ContinuousStages σ`.
* `AxiomCodeEdge/PrimitiveControl.lean`'s `spherical_fixed`, turning sphericity into
  `BinaryLevel.fixedSubspace`-membership.
* `AxiomCodeEvenLevelThree/WtScalarHolomorphic.lean`'s `cuspScalarWeightedRealization_holomorphicWt_one`,
  turning Wt-orbit holomorphy into Wt-scalar-realization holomorphy.
* `SphericalDetection/ScalarImageEigenform.lean`'s `cuspClassicalVectors_mem_of_holomorphic` and
  `cuspClassicalScalarImage_exists_form`, and `ScalarHeckeImage.lean`'s `cuspClassicalScalarImage_mem`,
  bundling the realization into an actual `CuspForm`.
-/

noncomputable section


namespace TernaryPeriodPolynomials.Argument.CuspidalSpan

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.SourceConstruction (EichlerInput)
open TernaryPeriodPolynomials.EdgeControl (spherical_fixed)
open TernaryPeriodPolynomials.LevelThreeSource (levelThreeStages)
open TernaryPeriodPolynomials.EvenLevelThree
open TernaryPeriodPolynomials.PlaneEisensteinContinuation

/-- The `Wt`-indexed vector orbit at `2 * halfWeight` is the plain orbit at `halfWeight`: the
vector analogue of `WtScalar.lean`'s `cuspScalarWeightedRealizationWt_two_mul`, proved the same
way via `wtFactor_even`. -/
theorem cuspWeightedAffineOrbitWt_two_mul (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (vector : cusp.H) {point : ℂ} (hpoint : 0 < point.im) :
    cuspWeightedAffineOrbitWt cusp (2 * halfWeight) vector point =
      cuspWeightedAffineOrbit cusp halfWeight vector point := by
  unfold cuspWeightedAffineOrbitWt cuspWeightedAffineOrbit
  rw [wtFactor_even halfWeight hpoint]

/-- Holomorphy of the plain weighted affine orbit transfers to the `Wt`-indexed orbit at
`2 * halfWeight`: the repackaging needed to feed
`cuspScalarWeightedRealization_holomorphicWt_one` from `EichlerInput.holomorphic`. -/
theorem holomorphicOrbitWt_of_holomorphicOrbit (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (vector : cusp.H)
    (h : DifferentiableOn ℂ (cuspWeightedAffineOrbit cusp halfWeight vector)
      UpperHalfPlane.upperHalfPlaneSet) :
    DifferentiableOn ℂ (cuspWeightedAffineOrbitWt cusp (2 * halfWeight) vector)
      UpperHalfPlane.upperHalfPlaneSet :=
  h.congr fun _point hpoint => cuspWeightedAffineOrbitWt_two_mul cusp halfWeight vector hpoint

variable {σ : CuspidalRepresentation} {n : ℕ}

/-- **The central "piece ⟹ bundled classical form" theorem.** Every `EichlerInput` built from a
`Cohomological` datum carries a genuine level-one holomorphic `CuspForm` realizing its vector. -/
theorem EichlerInput.exists_classicalForm (I : EichlerInput σ n) (coh : Cohomological σ n) :
    ∃ form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range (-2 * I.halfWeight),
      (form : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector := by
  have negative : I.halfWeight < 0 := by
    have hw := I.weight
    have hn : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
    linarith
  have fixed : I.vector.val ∈ BinaryLevel.fixedSubspace σ BinaryLevel.finiteCongruence :=
    spherical_fixed σ I.vector.val I.vector_spherical
  have stages : AnalyticScalar.ContinuousStages σ := levelThreeStages coh
  have holoWt : DifferentiableOn ℂ (cuspWeightedAffineOrbitWt σ (2 * I.halfWeight) I.vector.val)
      UpperHalfPlane.upperHalfPlaneSet :=
    holomorphicOrbitWt_of_holomorphicOrbit σ I.halfWeight I.vector.val I.holomorphic
  have holoScalarWt : DifferentiableOn ℂ
      (cuspScalarWeightedRealizationWt σ (2 * I.halfWeight) I.vector 1)
      UpperHalfPlane.upperHalfPlaneSet :=
    cuspScalarWeightedRealization_holomorphicWt_one σ stages (2 * I.halfWeight) I.vector fixed
      holoWt
  have holoScalar : DifferentiableOn ℂ (cuspScalarWeightedRealization σ I.halfWeight I.vector 1)
      UpperHalfPlane.upperHalfPlaneSet :=
    holoScalarWt.congr fun point hpoint =>
      (cuspScalarWeightedRealizationWt_two_mul σ I.halfWeight I.vector 1 point hpoint).symm
  have memVectors : I.vector ∈ cuspClassicalVectors σ I.halfWeight :=
    cuspClassicalVectors_mem_of_holomorphic σ I.halfWeight I.vector I.vector_spherical I.rotation
      holoScalar
  have memImage : cuspScalarWeightedLinear σ I.halfWeight 1 I.vector ∈
      cuspClassicalScalarImage σ I.halfWeight :=
    (cuspClassicalScalarImage_mem σ I.halfWeight _).mpr ⟨I.vector, memVectors, rfl⟩
  exact cuspClassicalScalarImage_exists_form σ I.halfWeight negative
    ⟨cuspScalarWeightedLinear σ I.halfWeight 1 I.vector, memImage⟩

end TernaryPeriodPolynomials.Argument.CuspidalSpan
