module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.SphericalProjection
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Finite.IntegralLevel
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.Smooth

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem cuspSphericalProjection_smooth (cusp : CuspidalRepresentation)
    (vector : cusp.H) (smooth : vector ∈ cusp.smooth) :
    cuspSphericalProjection cusp vector ∈ cusp.smooth := by
  apply (cusp.smooth_exact _).mpr
  constructor
  · have regular := ((cusp.smooth_exact vector).mp smooth).1
    have projected : Smooth (fun point : Fin 1 → BinaryRealGL =>
        cuspSphericalProjection cusp (cusp.π (atInfinity (point 0)) vector)) :=
      (cuspSphericalProjection cusp).restrictScalars ℝ |>.contDiff.comp_contDiffOn regular
    have equality : (fun point : Fin 1 → BinaryRealGL =>
        cuspSphericalProjection cusp (cusp.π (atInfinity (point 0)) vector)) =
        (fun point : Fin 1 → BinaryRealGL => cusp.π (atInfinity (point 0))
          (cuspSphericalProjection cusp vector)) := by
      funext point
      exact cuspSphericalProjection_real cusp (point 0) vector
    rwa [equality] at projected
  · refine ⟨finiteIntegralGLLevel 2, finiteIntegralGLLevel_isOpen 2,
      finiteIntegralGLLevel_isCompact 2, ?_⟩
    intro element
    obtain ⟨original, equality⟩ := element.property
    rw [← equality]
    exact cuspSphericalProjection_mem cusp vector original

def cuspSphericalSmoothProjection (cusp : CuspidalRepresentation) :
    cusp.smooth →ₗ[ℂ] cusp.smooth where
  toFun vector := ⟨cuspSphericalProjection cusp vector.val,
    cuspSphericalProjection_smooth cusp vector.val vector.property⟩
  map_add' first second := Subtype.ext (map_add (cuspSphericalProjection cusp) first.val second.val)
  map_smul' scalar vector := Subtype.ext (map_smul (cuspSphericalProjection cusp) scalar vector.val)

theorem cusp_exists_spherical_smooth_translate (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp) (vector : cusp.smooth) (nonzero : vector ≠ 0) :
    ∃ finite : BinaryFiniteGL,
      cuspSphericalSmoothProjection cusp
        ⟨cusp.π (atFinite finite) vector.val,
          cusp.smooth_stable (atFinite finite) vector.val vector.property⟩ ≠ 0 := by
  have nonzero_value : vector.val ≠ 0 := fun zero => nonzero (Subtype.ext zero)
  obtain ⟨finite, projected_nonzero⟩ :=
    cuspSphericalProjection_finite_nonzero cusp spherical vector.val nonzero_value
  refine ⟨finite, ?_⟩
  intro zero
  exact projected_nonzero (congrArg Subtype.val zero)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
