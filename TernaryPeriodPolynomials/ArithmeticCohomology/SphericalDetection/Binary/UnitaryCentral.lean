module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.HolomorphicOrbit

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem cuspUnitary_central (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp)
    (unit : Adelesˣ) (vector : cusp.H) :
    cusp.π (GeneralLinearGroup.scalar (Fin 2) unit) vector = cusp.centralCharacter unit • vector := by
  have dense : DenseRange (fun value : cusp.smooth => value.val) :=
    denseRange_subtype_val.mpr (sphericalCusp_smooth_dense cusp spherical)
  have equality := dense.equalizer
    (cuspUnitaryOperator cusp (GeneralLinearGroup.scalar (Fin 2) unit)).continuous
    (continuous_const.smul continuous_id) (by
      funext smooth_vector
      have smooth_equality :
          (⟨cusp.π (GeneralLinearGroup.scalar (Fin 2) unit) smooth_vector.val,
            cusp.smooth_stable _ _ smooth_vector.property⟩ : cusp.smooth) =
          cusp.centralCharacter unit • smooth_vector := by
        apply cusp.injective
        funext argument
        rw [cusp.equivariant, map_smul]
        change cusp.realize smooth_vector (argument * GeneralLinearGroup.scalar (Fin 2) unit) =
          cusp.centralCharacter unit * cusp.realize smooth_vector argument
        rw [← GeneralLinearGroup.scalar_commute, cusp.central]
      exact congrArg Subtype.val smooth_equality)
  exact congrFun equality vector

theorem cuspUnitary_positive_scalar (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (unit : ℝˣ) (positive : 0 < unit.val) (vector : cusp.H) :
    cusp.π (atInfinity (GeneralLinearGroup.scalar (Fin 2) unit)) vector = vector := by
  rw [atInfinity_scalar, cuspUnitary_central cusp spherical, central_positive unit positive, one_smul]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
