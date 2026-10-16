module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.FrameUnfolding

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularKernel

def standard {ring : Type*} [CommRing ring] : Rectangular ring :=
  columns (1 : Matrix (Fin 3) (Fin 3) ring)

theorem standard_map {source target : Type*} [CommRing source] [CommRing target]
    (hom : source →+* target) : (standard : Rectangular source).map hom = standard := by
  ext row column
  simp [standard, columns, Matrix.one_apply]

theorem columns_map {source target : Type*} [CommRing source] [CommRing target]
    (hom : source →+* target) (matrix : Matrix (Fin 3) (Fin 3) source) :
    (columns matrix).map hom = columns (matrix.map hom) := rfl

noncomputable def kernel (test : Rectangular Adeles → ℂ) (point : AdelicGL)
    (binary : BinaryAdelicGL) : ℂ := test (point⁻¹.val * standard * binary.val)

noncomputable def term (test : Rectangular Adeles → ℂ) (point : AdelicGL)
    (binary : BinaryAdelicGL) (frame : Frame) : ℂ :=
  test (point⁻¹.val * frame.val.map rationalAdele * binary.val)

theorem term_parameterize (test : Rectangular Adeles → ℂ) (point : AdelicGL)
    (binary : BinaryAdelicGL) (flag : Flags .plane) (rational : BinaryRationalGL) :
    term test point binary (FrameUnfolding.parameterize (flag, rational)) =
      kernel test (rationalGroup flag.out⁻¹ * point)
        (GeneralLinearGroup.map rationalAdele rational * binary) := by
  unfold term kernel
  rw [FrameUnfolding.parameterize_val, Matrix.map_mul, columns_map,
    _root_.mul_inv_rev, ← map_inv, inv_inv, Units.val_mul, Units.val_mul]
  change test (point⁻¹.val * (columns (rationalGroup flag.out).val *
      (GeneralLinearGroup.map rationalAdele rational).val) * binary.val) = _
  rw [← mul_standard (rationalGroup flag.out).val]
  simp only [standard, Matrix.mul_assoc]

noncomputable def theta (test : Rectangular Adeles → ℂ) (point : AdelicGL)
    (binary : BinaryAdelicGL) : ℂ := ∑' frame : Frame, term test point binary frame

theorem theta_unfold (test : Rectangular Adeles → ℂ) (point : AdelicGL) (binary : BinaryAdelicGL)
    (summable : Summable (term test point binary)) :
    theta test point binary = ∑' flag : Flags .plane, ∑' rational : BinaryRationalGL,
      kernel test (rationalGroup flag.out⁻¹ * point)
        (GeneralLinearGroup.map rationalAdele rational * binary) := by
  rw [theta, FrameUnfolding.tsum_unfold _ summable]
  simp only [term_parameterize]

theorem kernel_plane_unipotent (test : Rectangular Adeles → ℂ) (point : AdelicGL)
    (binary : BinaryAdelicGL) (first second : Adeles) :
    kernel test (planeUnipotent first second * point) binary = kernel test point binary := by
  have standardFixed : (planeUnipotent first second)⁻¹.val * standard = standard := by
    rw [standard, mul_standard]
    apply Matrix.ext
    intro row column
    fin_cases row <;> fin_cases column <;> simp [columns, planeUnipotent, Matrix.one_apply]
  unfold kernel
  rw [_root_.mul_inv_rev, Units.val_mul,
    Matrix.mul_assoc point⁻¹.val (planeUnipotent first second)⁻¹.val standard, standardFixed]

theorem kernel_plane_levi (test : Rectangular Adeles → ℂ) (point : AdelicGL)
    (binary left : BinaryAdelicGL) (scalar : Adelesˣ) :
    kernel test (planeLevi left scalar * point) binary = kernel test point (left⁻¹ * binary) := by
  have inverseStandard : (planeLevi left scalar)⁻¹.val * standard = standard * left⁻¹.val := by
    rw [standard, mul_standard]
    apply Matrix.ext
    intro row column
    fin_cases row <;> fin_cases column <;>
      simp [columns, planeLevi, planeBlock, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
  unfold kernel
  rw [_root_.mul_inv_rev, Units.val_mul,
    Matrix.mul_assoc point⁻¹.val (planeLevi left scalar)⁻¹.val standard, inverseStandard, Units.val_mul]
  simp only [Matrix.mul_assoc]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularKernel
