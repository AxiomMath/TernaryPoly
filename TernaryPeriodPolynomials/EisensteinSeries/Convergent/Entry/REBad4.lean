module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.REBase
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.REBad3

@[expose] public section


/-!
# R-e: The bad-plane base case

`integral_planeOpposite_bad`: `∫_{3ℤ₃-region} rz(φ(w⁻¹u(v)π))(y) dv = (∏_{p≠3} c_p)·(1/9)·φ(y)`.

Formalized by Claude Sonnet 5.5.
-/


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Filter
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.SourceConstruction
open scoped ENNReal NNReal

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

/-- **The bad-plane base case**: the finite entry integral of the spherical plane vector over the region where the
`3`-adic coordinates lie in `3ℤ₃` is `(1/9)` times the product of the local Euler factors away from `3`. -/
theorem integral_planeOpposite_bad (cusp : CuspidalRepresentation) (χ : RankOneCharacter) (b : ℂ)
    (hχ : ∀ u : IntegralAdelesˣ, χ.toMonoidHom (integralAdeleUnit u) = 1)
    (vec : cusp.smooth) (nonzero : vec ≠ 0) (spherical : vec.val ∈ sphericalSubspace cusp)
    (convergent : 3 < b.re) (eigenvalues : FinitePlace → ℂ)
    (eigen : ∀ place, place ≠ placeThree →
      cuspLocalPadicSphereOperator cusp place 1 vec = eigenvalues place • vec)
    (value : ℂ) (product : HasProd (fun place : {place : FinitePlace // place ≠ placeThree} =>
      cuspLocalPadicEulerFactor cusp place.val (eigenvalues place.val) b) value) (y : BinaryAdelicGL) :
    (∫ v in badRegion, entryRz cusp (finitePlaneVector cusp χ 0 b (planeOppositeStandardMatrix v.1 v.2) vec.val) y
        ∂(finiteMeasure.prod finiteMeasure)) =
      value * (1 / 9 : ℂ) * cusp.realize vec y := by
  have split := adelic_split y
  set r := realPart y with hr
  set m := finitePart y with hm
  let vec' : cusp.smooth := cuspSmoothAction cusp (atInfinity r) vec
  have nonzero' : vec' ≠ 0 := cuspSmoothAction_ne_zero cusp (atInfinity r) vec nonzero
  have spherical' : vec'.val ∈ cuspSphericalValues cusp :=
    cuspSmoothAction_real_spherical cusp vec spherical r
  have eigen' : ∀ place, place ≠ placeThree →
      cuspLocalPadicSphereOperator cusp place 1 vec' = eigenvalues place • vec' := by
    intro place same
    simp only [vec']
    rw [cuspLocalPadicSphereOperator_real_commute, eigen place same, map_smul]
  have integrable := entryIntegrand_integrable cusp vec' spherical' m b convergent
  have two : 2 < b.re := by linarith
  have full := entryIntegral_eulerProduct threeStable_badRegion cusp vec' nonzero' spherical' m b two
    eigenvalues eigen' integrable value product
  rw [entryBase_bad] at full
  have nonzeroN : normPower (GeneralLinearGroup.det (atFinite m)) b ≠ 0 := normPower_ne_zero' _ _
  have pointwise : ∀ v : FiniteAdeles × FiniteAdeles,
      entryRz cusp (finitePlaneVector cusp χ 0 b (planeOppositeStandardMatrix v.1 v.2) vec.val) y =
        (normPower (GeneralLinearGroup.det (atFinite m)) b)⁻¹ * entryIntegrand cusp vec' m b v := by
    intro v
    rw [entryRz_planeOpposite cusp χ b hχ vec.property spherical, entryRz_of_mem vec.property]
    have key : y * atFinite (entryBlock v) = atFinite (m * entryBlock v) * atInfinity r := by
      rw [split, mul_assoc, ← atFinite_mul, atFinite_mul_atInfinity_comm]
    have move : cusp.realize vec (y * atFinite (entryBlock v)) =
        cusp.realize vec' (atFinite (m * entryBlock v)) := by
      rw [key]
      exact (cuspSmoothAction_realize cusp (atInfinity r) vec (atFinite (m * entryBlock v))).symm
    rw [move]
    unfold entryIntegrand
    rw [normPower_det_atFinite_mul]
    field_simp
    exact mul_comm _ _
  have base : entryBaseValue cusp vec' m b = normPower (GeneralLinearGroup.det (atFinite m)) b *
      cusp.realize vec y := by
    unfold entryBaseValue
    congr 1
    have key : y = atFinite m * atInfinity r := by
      rw [split, atFinite_mul_atInfinity_comm]
    rw [key]
    exact cuspSmoothAction_realize cusp (atInfinity r) vec (atFinite m)
  simp_rw [pointwise]
  rw [integral_const_mul, full, base]
  field_simp

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
