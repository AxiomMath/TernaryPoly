module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.FiniteWeightValues
public import Mathlib.Analysis.InnerProductSpace.LinearPMap

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem cuspSmooth_le_affineSmooth (cusp : CuspidalRepresentation) : cusp.smooth ≤ cuspAffineSmoothValues cusp := by
  intro vector member
  have regular := smooth_one_contDiffOn (function := fun matrix => cusp.π (atInfinity matrix) vector)
    ((cusp.smooth_exact vector).mp member).1
  have affine_regular := regular.comp binaryUpperSectionMatrix_contDiffOn binaryUpperSectionMatrix_invertible
  exact affine_regular.of_le le_top

theorem cuspAffineSmoothValues_dense (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp) :
    Dense (cuspAffineSmoothValues cusp : Set cusp.H) :=
  (sphericalCusp_smooth_dense cusp spherical).mono (cuspSmooth_le_affineSmooth cusp)

def cuspRaisingPMap (cusp : CuspidalRepresentation) (weight : ℤ) : cusp.H →ₗ.[ℂ] cusp.H :=
  ⟨cuspAffineSmoothValues cusp, (cuspAffineSmoothValues cusp).subtype.comp (cuspRaisingOperator cusp weight)⟩

def cuspLoweringPMap (cusp : CuspidalRepresentation) (weight : ℤ) : cusp.H →ₗ.[ℂ] cusp.H :=
  ⟨cuspAffineSmoothValues cusp, (cuspAffineSmoothValues cusp).subtype.comp (cuspLoweringOperator cusp weight)⟩

theorem cuspRaisingPMap_formalAdjoint (cusp : CuspidalRepresentation) (weight : ℤ) :
    (cuspRaisingPMap cusp weight).IsFormalAdjoint (-cuspLoweringPMap cusp weight) := by
  intro first second
  change inner ℂ (cuspRaisingOperator cusp weight first).val second.val =
    inner ℂ first.val (-(cuspLoweringOperator cusp weight second).val)
  rw [inner_neg_right]
  exact eq_neg_of_add_eq_zero_left (cuspRaisingOperator_skew cusp weight first second)

theorem cuspLoweringPMap_formalAdjoint (cusp : CuspidalRepresentation) (weight : ℤ) :
    (cuspLoweringPMap cusp weight).IsFormalAdjoint (-cuspRaisingPMap cusp weight) := by
  intro first second
  change inner ℂ (cuspLoweringOperator cusp weight first).val second.val =
    inner ℂ first.val (-(cuspRaisingOperator cusp weight second).val)
  rw [inner_neg_right]
  exact eq_neg_of_add_eq_zero_left (cuspLoweringOperator_skew cusp weight first second)

theorem cuspRaisingPMap_isClosable (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp) (weight : ℤ) :
    (cuspRaisingPMap cusp weight).IsClosable := by
  have dense : Dense ((-cuspLoweringPMap cusp weight).domain : Set cusp.H) := cuspAffineSmoothValues_dense cusp spherical
  apply LinearPMap.isClosable_iff_exists_closed_extension.mpr
  exact ⟨(-cuspLoweringPMap cusp weight).adjoint, LinearPMap.adjoint_isClosed dense,
    (cuspRaisingPMap_formalAdjoint cusp weight).symm.le_adjoint dense⟩

theorem cuspLoweringPMap_isClosable (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp) (weight : ℤ) :
    (cuspLoweringPMap cusp weight).IsClosable := by
  have dense : Dense ((-cuspRaisingPMap cusp weight).domain : Set cusp.H) := cuspAffineSmoothValues_dense cusp spherical
  apply LinearPMap.isClosable_iff_exists_closed_extension.mpr
  exact ⟨(-cuspRaisingPMap cusp weight).adjoint, LinearPMap.adjoint_isClosed dense,
    (cuspLoweringPMap_formalAdjoint cusp weight).symm.le_adjoint dense⟩

end TernaryPeriodPolynomials.SphericalDetection.Helpers
