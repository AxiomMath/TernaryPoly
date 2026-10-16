module

public import TernaryPeriodPolynomials.BoundaryComparison.CuspidalSpan.ReynoldsAverage
public import TernaryPeriodPolynomials.BoundaryComparison.CuspidalSpan.ClassicalBridge
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Period.Eigen
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.Representation
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.SphericalProjection

@[expose] public section


/-!
# `reynoldsAverage` preserves the three remaining `EichlerInput` properties

`ReynoldsAverage.lean` shows that `reynoldsAverage cusp v` is fixed by *all* of `GL₂(ℤ̂)`
whenever `v` is fixed only by `PlaneLeviLevel` (`reynoldsAverage_fixed`). Building an
`EichlerInput` (`AxiomCodeSourceConstruction/EichlerEquivariance.lean`) out of
`w := reynoldsAverage cusp v` additionally needs `w` to inherit, from `v`, each of:

* the archimedean rotation eigenvalue (`EichlerInput.rotation`);
* holomorphy of the weighted affine orbit (`EichlerInput.holomorphic`);
* full sphericity, i.e. `w.val ∈ cuspSphericalValues cusp` (`EichlerInput.vector_spherical`).

All three are proved here:

* `reynoldsAverage_rotation`: `cusp.π` is linear and commutes with every finite-adelic
  translation by `atInfinity_commute_atFinite` (`SphericalDetection/BinaryRepresentation.lean`),
  so the rotation eigenvalue passes through each `cuspAt cusp (γ i) v` term unchanged, exactly as
  in the existing `cuspFiniteOperator_real` (`SphericalDetection/BinaryFiniteWeightValues.lean`).
* `reynoldsAverage_holomorphicOrbit`: each `cuspAt cusp (γ i) v` is, via this file's own
  `cuspAt_eq_rationalSlash` (`ClassicalBridge.lean`), a `cuspFiniteRationalSlash` translate of `v`,
  so `holomorphicOrbit_slash` applies termwise and `holomorphicOrbit_sum`/`_smul`
  (`AxiomCodeSourceConstruction/PeriodEigen.lean`) close the finite average, exactly as in the
  existing `holomorphicClassicalSpace_stable`.
* `reynoldsAverage_spherical`: `cuspSphericalValues` (`BinarySphericalProjection.lean`) is
  *definitionally* "fixed by `atFinite` through every element of `GL₂(ℤ̂)`", which is exactly what
  `reynoldsAverage_fixed` already supplies (applied at `element⁻¹`); no new averaging argument is
  needed beyond unfolding.

## What this does **not** close

These three lemmas discharge the "averaging preserves an already-held property" step only. They
presuppose a starting vector `v : cusp.smooth` that is already `PlaneLeviLevel`-fixed and already
carries the correct rotation eigenvalue and holomorphy *before* averaging, for some
`cusp : CuspidalRepresentation` tied to the given classical cusp form `f`. Constructing that `v`
from `f` in the first place — and separately, showing `reynoldsAverage cusp v ≠ 0`
(`EichlerInput.vector_ne`, a genuinely representation-theoretic nonvanishing fact, not a
consequence of linearity) — is not addressed here and remains exactly the "classical form ⟹
automorphic cuspidal datum" gap named in `CuspidalSupply.lean`'s docstring. Likewise unaddressed:
the further chain from a completed `EichlerInput` through the Eichler cocycle to an exact
`StratumH2`/`automorphicPlaneSpan` element matching `per (k+1) (-1) f`.
-/

noncomputable section


namespace TernaryPeriodPolynomials.Argument.CuspidalSpan

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.SourceConstruction (HolomorphicOrbit
  holomorphicOrbit_slash holomorphicOrbit_sum holomorphicOrbit_smul)
open TernaryPeriodPolynomials.Separation (PlaneLeviLevel)

/-- **Reynolds-averaging preserves the archimedean rotation eigenvalue.** If `v.val` has rotation
weight `wt` under every `binaryRotations angle`, so does `(reynoldsAverage cusp v).val`. Feeds
`EichlerInput.rotation`. -/
theorem reynoldsAverage_rotation (cusp : CuspidalRepresentation) (wt : ℤ) (v : cusp.smooth)
    (hrot : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) v.val =
      (angle : ℂ) ^ wt • v.val) (angle : Circle) :
    cusp.π (atInfinity (binaryRotations angle)) (reynoldsAverage cusp v).val =
      (angle : ℂ) ^ wt • (reynoldsAverage cusp v).val := by
  have step : ∀ i : Fin 8, cusp.π (atInfinity (binaryRotations angle))
      (cuspAt cusp (γ i) v).val = (angle : ℂ) ^ wt • (cuspAt cusp (γ i) v).val := by
    intro i
    show cusp.π (atInfinity (binaryRotations angle))
      (cusp.π (atFinite (GeneralLinearGroup.map integralEmbedding (γ i)⁻¹)) v.val) =
      (angle : ℂ) ^ wt • cusp.π (atFinite (GeneralLinearGroup.map integralEmbedding (γ i)⁻¹)) v.val
    rw [← Module.End.mul_apply, ← map_mul,
      (atInfinity_commute_atFinite (binaryRotations angle)
        (GeneralLinearGroup.map integralEmbedding (γ i)⁻¹)).eq,
      map_mul, Module.End.mul_apply, hrot, map_smul]
  show cusp.π (atInfinity (binaryRotations angle))
      ((8⁻¹ : ℂ) • ∑ i : Fin 8, (cuspAt cusp (γ i) v).val) =
    (angle : ℂ) ^ wt • ((8⁻¹ : ℂ) • ∑ i : Fin 8, (cuspAt cusp (γ i) v).val)
  rw [map_smul, map_sum, Finset.sum_congr rfl (fun i _ => step i), ← Finset.smul_sum, smul_comm]

/-- **Reynolds-averaging preserves holomorphy of the weighted affine orbit.** Feeds
`EichlerInput.holomorphic`. -/
theorem reynoldsAverage_holomorphicOrbit (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (v : cusp.smooth) (hhol : HolomorphicOrbit cusp halfWeight v.val) :
    HolomorphicOrbit cusp halfWeight (reynoldsAverage cusp v).val := by
  have step : ∀ i : Fin 8, HolomorphicOrbit cusp halfWeight (cuspAt cusp (γ i) v).val := by
    intro i
    rw [cuspAt_eq_rationalSlash]
    exact holomorphicOrbit_slash cusp halfWeight (SpecialLinearGroup.mapGL ℚ (M i)) v hhol
  show HolomorphicOrbit cusp halfWeight ((8⁻¹ : ℂ) • ∑ i : Fin 8, (cuspAt cusp (γ i) v).val)
  exact holomorphicOrbit_smul cusp halfWeight _
    (holomorphicOrbit_sum cusp halfWeight Finset.univ _ (fun i _ => step i))

/-- **Reynolds-averaging a `PlaneLeviLevel`-fixed vector lands in `cuspSphericalValues`.** A
direct corollary of `reynoldsAverage_fixed`: `cuspSphericalValues` is definitionally "fixed by
`atFinite` through every element of `GL₂(ℤ̂)`", which is exactly what `reynoldsAverage_fixed`
supplies (applied at `element⁻¹`, using `(element⁻¹)⁻¹ = element`). Feeds
`EichlerInput.vector_spherical`. -/
theorem reynoldsAverage_spherical (cusp : CuspidalRepresentation) (v : cusp.smooth)
    (leviFixed : ∀ κ : GeneralLinearGroup (Fin 2) IntegralAdeles, PlaneLeviLevel κ →
      cuspAt cusp κ v = v) :
    (reynoldsAverage cusp v).val ∈ cuspSphericalValues cusp := by
  intro element
  show cusp.π (atFinite (GeneralLinearGroup.map integralEmbedding element))
    (reynoldsAverage cusp v).val = (reynoldsAverage cusp v).val
  have h := reynoldsAverage_fixed cusp v leviFixed element⁻¹
  have hval : cusp.π (atFinite (GeneralLinearGroup.map integralEmbedding (element⁻¹)⁻¹))
      (reynoldsAverage cusp v).val = (reynoldsAverage cusp v).val := congrArg Subtype.val h
  rwa [inv_inv] at hval

end TernaryPeriodPolynomials.Argument.CuspidalSpan
