module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.REGeneral
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.ScalarRealization

@[expose] public section


/-!
# R-e: The plane and line coefficient functions

`planeCoeff`, `lineCoeff` (the products `c_F(f)·F(x b_F(f))(z)` of the paper), their realizations `z_i^{hw}·rz(...)` and the identity `planeCoeff_integral` for finite matrices.

Formalized by Claude Sonnet 5.5.
-/


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Filter
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.SourceConstruction

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

/-- The plane coefficient function `c_F(f) · F(x · b_F(f))(z)` of a finite matrix `f` (written with the chosen
finite plane Iwasawa decomposition). -/
def planeCoeff (cusp : CuspidalRepresentation) (χ : RankOneCharacter) (b : ℂ) (hw : ℤ) (vec : cusp.smooth)
    (x : BinaryAdelicGL) (f : FiniteGL) (z : ℂ) : ℂ :=
  finitePlaneFactor χ 0 b (finitePlaneParabolic f) (finitePlaneParabolic_mem f) *
    cuspScalarWeightedRealization cusp hw vec
      (x * atFinite (planeBlockGL (finitePlaneParabolic f) (finitePlaneParabolic_mem f))) z

/-- The line coefficient function `c_F^{line}(f) · F(x · b_F^{line}(f))(z)`. -/
def lineCoeff (cusp : CuspidalRepresentation) (χ : RankOneCharacter) (b : ℂ) (hw : ℤ) (vec : cusp.smooth)
    (x : BinaryAdelicGL) (f : FiniteGL) (z : ℂ) : ℂ :=
  finiteLineFactor χ 2 b (finiteLineParabolic f) (finiteLineParabolic_mem f) *
    cuspScalarWeightedRealization cusp hw vec
      (x * atFinite (lineBlockGL (finiteLineParabolic f) (finiteLineParabolic_mem f))) z

/-- The real matrix of the upper half plane section. -/
def sectionMatrix (z : ℂ) : BinaryRealGL := invertibleMatrix (binaryUpperSectionMatrix z)

theorem entryRz_finitePlaneVector' (σ : CuspidalRepresentation) (χ : RankOneCharacter) (a b : ℂ) (g : FiniteGL)
    {v : σ.H} (hv : v ∈ σ.smooth) (x : BinaryAdelicGL) :
    entryRz σ (finitePlaneVector σ χ a b g v) x =
      finitePlaneFactor χ a b (finitePlaneParabolic g) (finitePlaneParabolic_mem g) *
        entryRz σ v (x * atFinite (planeBlockGL (finitePlaneParabolic g) (finitePlaneParabolic_mem g))) := by
  unfold finitePlaneVector
  rw [entryRz_smul (σ.smooth_stable _ _ hv), entryRz_pi hv]

theorem entryRz_finiteLineVector' (σ : CuspidalRepresentation) (χ : RankOneCharacter) (a b : ℂ) (g : FiniteGL)
    {v : σ.H} (hv : v ∈ σ.smooth) (x : BinaryAdelicGL) :
    entryRz σ (finiteLineVector σ χ a b g v) x =
      finiteLineFactor χ a b (finiteLineParabolic g) (finiteLineParabolic_mem g) *
        entryRz σ v (x * atFinite (lineBlockGL (finiteLineParabolic g) (finiteLineParabolic_mem g))) := by
  unfold finiteLineVector
  rw [entryRz_smul (σ.smooth_stable _ _ hv), entryRz_pi hv]

theorem planeCoeff_eq (cusp : CuspidalRepresentation) (χ : RankOneCharacter) (b : ℂ) (hw : ℤ)
    (vec : cusp.smooth) (x : BinaryAdelicGL) (f : FiniteGL) (z : ℂ) :
    planeCoeff cusp χ b hw vec x f z =
      (z.im ^ hw : ℝ) * entryRz cusp (finitePlaneVector cusp χ 0 b f vec.val)
        (x * atInfinity (sectionMatrix z)) := by
  unfold planeCoeff cuspScalarWeightedRealization cuspScalarAffineRealization sectionMatrix
  rw [entryRz_finitePlaneVector' cusp χ 0 b f vec.property, entryRz_of_mem vec.property]
  have comm : x * atInfinity (invertibleMatrix (binaryUpperSectionMatrix z)) *
      atFinite (planeBlockGL (finitePlaneParabolic f) (finitePlaneParabolic_mem f)) =
      x * atFinite (planeBlockGL (finitePlaneParabolic f) (finitePlaneParabolic_mem f)) *
        atInfinity (invertibleMatrix (binaryUpperSectionMatrix z)) := by
    rw [mul_assoc, ← atFinite_mul_atInfinity_comm, ← mul_assoc]
  rw [comm, Complex.real_smul]
  ring

theorem lineCoeff_eq (cusp : CuspidalRepresentation) (χ : RankOneCharacter) (b : ℂ) (hw : ℤ)
    (vec : cusp.smooth) (x : BinaryAdelicGL) (f : FiniteGL) (z : ℂ) :
    lineCoeff cusp χ b hw vec x f z =
      (z.im ^ hw : ℝ) * entryRz cusp (finiteLineVector cusp χ 2 b f vec.val)
        (x * atInfinity (sectionMatrix z)) := by
  unfold lineCoeff cuspScalarWeightedRealization cuspScalarAffineRealization sectionMatrix
  rw [entryRz_finiteLineVector' cusp χ 2 b f vec.property, entryRz_of_mem vec.property]
  have comm : x * atInfinity (invertibleMatrix (binaryUpperSectionMatrix z)) *
      atFinite (lineBlockGL (finiteLineParabolic f) (finiteLineParabolic_mem f)) =
      x * atFinite (lineBlockGL (finiteLineParabolic f) (finiteLineParabolic_mem f)) *
        atInfinity (invertibleMatrix (binaryUpperSectionMatrix z)) := by
    rw [mul_assoc, ← atFinite_mul_atInfinity_comm, ← mul_assoc]
  rw [comm, Complex.real_smul]
  ring

/-- **The finite entry identity at the level of finite matrices.** -/
theorem planeCoeff_integral (cusp : CuspidalRepresentation) (χ : RankOneCharacter) (b : ℂ) (hw : ℤ)
    (hχ : ∀ u : IntegralAdelesˣ, χ.toMonoidHom (integralAdeleUnit u) = 1)
    (vec : cusp.smooth) (nonzero : vec ≠ 0) (spherical : vec.val ∈ sphericalSubspace cusp)
    (convergent : 3 < b.re) (eigenvalues : FinitePlace → ℂ)
    (eigen : ∀ place, cuspLocalPadicSphereOperator cusp place 1 vec = eigenvalues place • vec)
    (value : ℂ) (product : HasProd (fun place : {place : FinitePlace // place ≠ placeThree} =>
      cuspLocalPadicEulerFactor cusp place.val (eigenvalues place.val) b) value)
    (x : BinaryAdelicGL) (f : FiniteGL) (z : ℂ) :
    (∫ v : FiniteAdeles × FiniteAdeles, planeCoeff cusp χ b hw vec x (weyl⁻¹ * lineUnipotent v.1 v.2 * f) z
        ∂(finiteMeasure.prod finiteMeasure)) =
      value * cuspLocalPadicEulerFactor cusp placeThree (eigenvalues placeThree) b *
        lineCoeff cusp χ (b - 1) hw vec x f z := by
  simp_rw [planeCoeff_eq]
  rw [integral_const_mul, lineCoeff_eq]
  have := entryPlaneIntegral_general cusp χ b hχ vec nonzero spherical convergent eigenvalues eigen value product f
    (x * atInfinity (sectionMatrix z))
  unfold entryPlaneIntegral at this
  simp_rw [one_mul] at this
  rw [this]
  ring

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
