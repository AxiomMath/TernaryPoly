module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.KTypeSection
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.RealIwasawa
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.FiniteSpherical
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.AdelicSplit
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Obstructions
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.SmoothHelpers
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.CohomologicalHolomorphic
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Finite.GLStrongApproximation
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelOneParity.Helpers
public import TernaryPeriodPolynomials.EisensteinSeries.ArchimedeanConstant.RealShift
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

@[expose] public section


/-!
# Spherical line-induced sections nonzero at the good-line cusp

For `D` spherical and `χ` trivial on `Ẑ^×`, the vector-valued section
`Ψ(g) = Ψ_f(g_f)(Ψ_∞(g_∞))` — the archimedean K-type section of `KTypeSection` built on the
analytic Iwasawa decomposition of `RealIwasawa` from the holomorphic weight vector of `D`, followed
by the spherical finite part of `FiniteSpherical` — gives the scalar section `g ↦ realize(Ψ g)(1)`,
which is a normalized line-induced section (`lineFunction_isInduced`). A real right translate of it
is nonzero at the good-line frame, which proves the section input `LineSectionConstruction D true`
for such `χ` (`lineSectionConstruction_true_of_character`). By
`Obstructions.not_spherical_of_lineSectionConstruction_true` a character hypothesis is necessary.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.Separation
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm (finiteAdeleUnit)
open TernaryPeriodPolynomials.GoodApartmentFunctional.FrameOrbit (referenceIntegral)
open TernaryPeriodPolynomials.BoundaryFiniteness.IntegralFlags (rational)
open TernaryPeriodPolynomials.HeckeTranslate.HeckeInvariance
  (combineGL_mul atInfinity_mul atFinite_mul)

namespace TernaryPeriodPolynomials.SourceConstruction

/-! ## The real Iwasawa data of the line parabolic -/

/-- The Gram–Schmidt Iwasawa decomposition, as line-parabolic Iwasawa data. -/
def realLineIwasawa : LineIwasawaData where
  B := iwasawaB
  K := iwasawaK
  mul_eq := iwasawaB_mul_iwasawaK
  B_mem g := ⟨(iwasawaB_upper g).1, (iwasawaB_upper g).2.1⟩
  B_corner_pos g := (iwasawaB_upper g).2.2.2.1
  B_block_pos g := by
    obtain ⟨_, _, h21, _, h11, h22⟩ := iwasawaB_upper g
    rw [h21, mul_zero, sub_zero]
    exact mul_pos h11 h22
  K_orth := iwasawaK_orthogonal
  B_one := iwasawaB_one
  K_one := iwasawaK_one
  equivariant p hp g := iwasawa_lineParabolic hp g
  B_analytic := iwasawaB_contDiffOn
  K_analytic := iwasawaK_contDiffOn

theorem realLineIwasawa_orth {κ : RealGL3} (hκ : IsOrthogonalReal κ) :
    realLineIwasawa.B κ = 1 ∧ realLineIwasawa.K κ = κ := by
  have h := iwasawa_eq isUpperPositive_one hκ
  rw [one_mul] at h
  exact h

/-! ## Levi parts of the generators -/

section Generators

theorem lineUnipotent_mem {R : Type*} [CommRing R] (a b : R) :
    lineUnipotent a b ∈ lineParabolic R := by
  constructor <;> simp [lineUnipotent, upperUnipotent]

theorem lineCorner_lineUnipotent (a b : ℝ) : lineCorner (lineUnipotent a b) = 1 := by
  simp [lineCorner, lineUnipotent, upperUnipotent]

theorem lineBlock_lineUnipotent (a b : ℝ) : lineBlock (lineUnipotent a b) = 1 := by
  apply Units.ext
  rw [lineBlock_val (lineUnipotent_mem a b)]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lineBlockMatrix, lineUnipotent, upperUnipotent]

theorem leviFactor_lineUnipotent (e : ℕ) (α β : ℂ) (a b : ℝ) :
    leviFactor e α β (lineUnipotent a b) = 1 := by
  unfold leviFactor
  rw [lineCorner_lineUnipotent, lineBlock_lineUnipotent, cornerFactor_one, Units.val_one,
    Matrix.det_one, blockFactor_one, mul_one]

theorem lineCorner_lineLevi (d : ℝˣ) (A : BinaryRealGL) : lineCorner (lineLevi d A) = d.val := by
  unfold lineCorner
  rw [lineLevi_val]
  simp

theorem lineBlock_lineLevi (d : ℝˣ) (A : BinaryRealGL) : lineBlock (lineLevi d A) = A := by
  apply Units.ext
  rw [lineBlock_val (lineLevi_mem d A)]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lineBlockMatrix, lineLevi_val]

theorem leviFactor_lineLevi (e : ℕ) (α β : ℂ) (d : ℝˣ) (A : BinaryRealGL) :
    leviFactor e α β (lineLevi d A) = cornerFactor e α d.val * blockFactor β A.val.det := by
  unfold leviFactor
  rw [lineCorner_lineLevi, lineBlock_lineLevi]

theorem lineCornerUnit_lineLevi {R : Type*} [CommRing R] (d : Rˣ) (A : GeneralLinearGroup (Fin 2) R)
    (h : lineLevi d A ∈ lineParabolic R) : lineCornerUnit (lineLevi d A) h = d := by
  apply Units.ext
  change (lineLevi d A).val 0 0 = d.val
  rw [lineLevi_val]
  simp

theorem lineBlockGL_lineLevi {R : Type*} [CommRing R] (d : Rˣ) (A : GeneralLinearGroup (Fin 2) R)
    (h : lineLevi d A ∈ lineParabolic R) : lineBlockGL (lineLevi d A) h = A := by
  apply Units.ext
  change !![(lineLevi d A).val 1 1, (lineLevi d A).val 1 2; (lineLevi d A).val 2 1,
    (lineLevi d A).val 2 2] = A.val
  rw [lineLevi_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem lineCornerUnit_lineUnipotent {R : Type*} [CommRing R] (a b : R)
    (h : lineUnipotent a b ∈ lineParabolic R) : lineCornerUnit (lineUnipotent a b) h = 1 := by
  apply Units.ext
  change (lineUnipotent a b).val 0 0 = 1
  simp [lineUnipotent, upperUnipotent]

theorem lineBlockGL_lineUnipotent {R : Type*} [CommRing R] (a b : R)
    (h : lineUnipotent a b ∈ lineParabolic R) : lineBlockGL (lineUnipotent a b) h = 1 := by
  apply Units.ext
  change !![(lineUnipotent a b).val 1 1, (lineUnipotent a b).val 1 2;
    (lineUnipotent a b).val 2 1, (lineUnipotent a b).val 2 2] = (1 : Matrix (Fin 2) (Fin 2) R)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lineUnipotent, upperUnipotent]

theorem finiteAdeleUnit_one : finiteAdeleUnit (1 : FiniteAdelesˣ) = 1 := Units.ext rfl

theorem normPower_one' (z : ℂ) : normPower (1 : Adelesˣ) z = 1 := by
  simp [normPower]

theorem finiteLineFactor_lineUnipotent (χ : RankOneCharacter) (a b : ℂ) (s t : FiniteAdeles)
    (h : lineUnipotent s t ∈ lineParabolic FiniteAdeles) :
    finiteLineFactor χ a b (lineUnipotent s t) h = 1 := by
  unfold finiteLineFactor
  rw [lineCornerUnit_lineUnipotent, lineBlockGL_lineUnipotent, map_one GeneralLinearGroup.det,
    finiteAdeleUnit_one, map_one χ.toMonoidHom, normPower_one', normPower_one', mul_one, mul_one]

theorem finiteLineFactor_lineLevi (χ : RankOneCharacter) (a b : ℂ) (d : FiniteAdelesˣ)
    (A : GeneralLinearGroup (Fin 2) FiniteAdeles) (h : lineLevi d A ∈ lineParabolic FiniteAdeles) :
    finiteLineFactor χ a b (lineLevi d A) h =
      χ.toMonoidHom (finiteAdeleUnit d) * normPower (finiteAdeleUnit d) a *
        normPower (finiteAdeleUnit (GeneralLinearGroup.det A)) b := by
  unfold finiteLineFactor
  rw [lineCornerUnit_lineLevi, lineBlockGL_lineLevi]

theorem realUnitPart_det {m : ℕ} (A : GeneralLinearGroup (Fin m) Adeles) :
    realUnitPart (GeneralLinearGroup.det A) = GeneralLinearGroup.det (realPart A) := by
  apply Units.ext
  change (RingHom.fst ℝ FiniteAdeles) A.val.det = ((RingHom.fst ℝ FiniteAdeles).mapMatrix A.val).det
  exact RingHom.map_det _ _

theorem finiteUnitPart_det {m : ℕ} (A : GeneralLinearGroup (Fin m) Adeles) :
    finiteUnitPart (GeneralLinearGroup.det A) = GeneralLinearGroup.det (finitePart A) := by
  apply Units.ext
  change (RingHom.snd ℝ FiniteAdeles) A.val.det = ((RingHom.snd ℝ FiniteAdeles).mapMatrix A.val).det
  exact RingHom.map_det _ _

end Generators

/-! ## The adelic vector-valued section -/

section Section

variable {n : ℕ} (D : InducingData n) (m : ℕ) (w : D.cusp.H)

/-- The block exponent `(n+1)/2` of the line induction at the cohomological point. -/
def lineBeta (n : ℕ) : ℂ := ((n : ℂ) + 1) / 2

/-- The archimedean section. -/
def lineRealSection (g : RealGL3) : D.cusp.H :=
  lineSection D.cusp m 0 2 (lineBeta n) w realLineIwasawa g

/-- The adelic vector-valued section. -/
def lineVector (g : AdelicGL) : D.cusp.H :=
  finiteLineVector D.cusp D.chi 2 (lineBeta n) (finiteGroup g) (lineRealSection D m w (realGroup g))

variable {D m w}

theorem lineRealSection_mem (hw : w ∈ D.cusp.smooth) (g : RealGL3) :
    lineRealSection D m w g ∈ D.cusp.smooth := by
  rw [lineRealSection, ← lineSectionSmooth_val D.cusp m 0 2 (lineBeta n) w hw realLineIwasawa g]
  exact (lineSectionSmooth D.cusp m 0 2 (lineBeta n) w hw realLineIwasawa g).property

theorem lineVector_mem (hw : w ∈ D.cusp.smooth) (g : AdelicGL) : lineVector D m w g ∈ D.cusp.smooth :=
  finiteLineVector_smooth D.chi 2 (lineBeta n) _ (lineRealSection_mem hw _)

theorem lineRealSection_spherical (hsph : w ∈ sphericalSubspace D.cusp) (g : RealGL3) :
    lineRealSection D m w g ∈ sphericalSubspace D.cusp := by
  unfold lineRealSection lineSection kPart wPlus
  refine Submodule.smul_mem _ _ (sphericalSubspace_real ?_ _)
  refine Submodule.smul_mem _ _ (Submodule.add_mem _ (Submodule.smul_mem _ _ hsph)
    (Submodule.smul_mem _ _ (sphericalSubspace_real hsph _)))

variable (D m w)

/-- The smooth-vector version. -/
def lineVectorS (hw : w ∈ D.cusp.smooth) (g : AdelicGL) : D.cusp.smooth :=
  ⟨lineVector D m w g, lineVector_mem hw g⟩

/-- The scalar section. -/
def lineFunction (hw : w ∈ D.cusp.smooth) (g : AdelicGL) : ℂ :=
  D.cusp.realize (lineVectorS D m w hw g) 1

variable {D m w}

/-! ### Equivariance -/

theorem realGroup_lineUnipotent (a b : Adeles) :
    realGroup (lineUnipotent a b) =
      lineUnipotent ((RingHom.fst ℝ FiniteAdeles) a) ((RingHom.fst ℝ FiniteAdeles) b) :=
  map_lineUnipotent' _ a b

theorem finiteGroup_lineUnipotent (a b : Adeles) :
    finiteGroup (lineUnipotent a b) =
      lineUnipotent ((RingHom.snd ℝ FiniteAdeles) a) ((RingHom.snd ℝ FiniteAdeles) b) :=
  map_lineUnipotent' _ a b

theorem realGroup_lineLevi (t : Adelesˣ) (A : BinaryAdelicGL) :
    realGroup (lineLevi t A) = lineLevi (realUnitPart t) (realPart A) :=
  map_lineLevi _ t A

theorem finiteGroup_lineLevi (t : Adelesˣ) (A : BinaryAdelicGL) :
    finiteGroup (lineLevi t A) = lineLevi (finiteUnitPart t) (finitePart A) :=
  map_lineLevi _ t A

theorem realPart_one {k : ℕ} : realPart (1 : GeneralLinearGroup (Fin k) Adeles) = 1 := map_one _

theorem finitePart_one {k : ℕ} : finitePart (1 : GeneralLinearGroup (Fin k) Adeles) = 1 := map_one _

theorem realUnitPart_one : realUnitPart (1 : Adelesˣ) = 1 := map_one _

theorem finiteUnitPart_one : finiteUnitPart (1 : Adelesˣ) = 1 := map_one _

/-- **Unipotent invariance.** -/
theorem lineVector_lineUnipotent (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)
    (hrot : RotationWeight D.cusp m w) (hsph : w ∈ sphericalSubspace D.cusp) (a b : Adeles)
    (g : AdelicGL) : lineVector D m w (lineUnipotent a b * g) = lineVector D m w g := by
  unfold lineVector
  rw [map_mul, map_mul, realGroup_lineUnipotent, finiteGroup_lineUnipotent]
  have hreal : lineRealSection D m w (lineUnipotent ((RingHom.fst ℝ FiniteAdeles) a)
      ((RingHom.fst ℝ FiniteAdeles) b) * realGroup g) = lineRealSection D m w (realGroup g) := by
    unfold lineRealSection
    rw [lineSection_equivariant D.cusp m 0 2 (lineBeta n) w hrot realLineIwasawa
      (lineUnipotent_mem _ _), leviFactor_lineUnipotent, lineBlock_lineUnipotent,
      rep_atInfinity_one, one_smul]
  rw [hreal, finiteLineVector_mul D.chi 2 (lineBeta n) hχ (lineRealSection_spherical hsph _)
    (lineUnipotent_mem _ _), finiteLineFactor_lineUnipotent, lineBlockGL_lineUnipotent,
    TernaryPeriodPolynomials.SphericalDetection.Helpers.atFinite_one, map_one, one_smul,
    Module.End.one_apply]

theorem cornerFactor_zero_eq (α : ℂ) (t : ℝ) :
    cornerFactor 0 α t = Complex.exp (α * (Real.log |t| : ℝ)) := by
  simp [cornerFactor]

/-- **The rank-one Levi character.** -/
theorem lineVector_lineLevi_corner (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)
    (hrot : RotationWeight D.cusp m w) (hsph : w ∈ sphericalSubspace D.cusp) (t : Adelesˣ)
    (g : AdelicGL) :
    lineVector D m w (lineLevi t 1 * g) =
      (D.chi.toMonoidHom t * normPower t 2) • lineVector D m w g := by
  unfold lineVector
  rw [map_mul, map_mul, realGroup_lineLevi, finiteGroup_lineLevi, realPart_one, finitePart_one]
  have hreal : lineRealSection D m w (lineLevi (realUnitPart t) 1 * realGroup g) =
      cornerFactor 0 2 (realUnitPart t).val • lineRealSection D m w (realGroup g) := by
    unfold lineRealSection
    rw [lineSection_equivariant D.cusp m 0 2 (lineBeta n) w hrot realLineIwasawa
      (lineLevi_mem _ _), leviFactor_lineLevi, lineBlock_lineLevi, rep_atInfinity_one,
      Units.val_one, Matrix.det_one, blockFactor_one, mul_one]
  rw [hreal, finiteLineVector_mul D.chi 2 (lineBeta n) hχ
      (Submodule.smul_mem _ _ (lineRealSection_spherical hsph _)) (lineLevi_mem _ _),
    finiteLineFactor_lineLevi, lineBlockGL_lineLevi,
    TernaryPeriodPolynomials.SphericalDetection.Helpers.atFinite_one, map_one D.cusp.π,
    Module.End.one_apply, finiteLineVector_smul, smul_smul, map_one GeneralLinearGroup.det,
    finiteAdeleUnit_one, normPower_one', mul_one]
  congr 1
  rw [character_split D.chi t, normPower_split t 2, character_real_eq_one D.chi hχ,
    TernaryPeriodPolynomials.EisensteinRegularization.Helpers.normPower_realAdeleUnit,
    cornerFactor_zero_eq]
  ring

/-- **The `GL₂` Levi law.** -/
theorem lineVector_lineLevi_block (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)
    (hrot : RotationWeight D.cusp m w) (hsph : w ∈ sphericalSubspace D.cusp) (A : BinaryAdelicGL)
    (g : AdelicGL) :
    lineVector D m w (lineLevi 1 A * g) =
      normPower (GeneralLinearGroup.det A) (lineBeta n) • D.cusp.π A (lineVector D m w g) := by
  unfold lineVector
  rw [map_mul, map_mul, realGroup_lineLevi, finiteGroup_lineLevi, realUnitPart_one,
    finiteUnitPart_one]
  have hreal : lineRealSection D m w (lineLevi 1 (realPart A) * realGroup g) =
      blockFactor (lineBeta n) (realPart A).val.det •
        D.cusp.π (atInfinity (realPart A)) (lineRealSection D m w (realGroup g)) := by
    unfold lineRealSection
    rw [lineSection_equivariant D.cusp m 0 2 (lineBeta n) w hrot realLineIwasawa
      (lineLevi_mem _ _), leviFactor_lineLevi, lineBlock_lineLevi, Units.val_one,
      cornerFactor_one, one_mul]
  rw [hreal, finiteLineVector_mul D.chi 2 (lineBeta n) hχ
      (Submodule.smul_mem _ _ (sphericalSubspace_real (lineRealSection_spherical hsph _) _))
      (lineLevi_mem _ _),
    finiteLineFactor_lineLevi, lineBlockGL_lineLevi, finiteAdeleUnit_one, map_one D.chi.toMonoidHom,
    normPower_one', one_mul, one_mul, finiteLineVector_smul, finiteLineVector_real, map_smul,
    smul_smul]
  have hsplit : D.cusp.π A (finiteLineVector D.cusp D.chi 2 (lineBeta n) (finiteGroup g)
      (lineRealSection D m w (realGroup g))) =
      D.cusp.π (atFinite (finitePart A)) (D.cusp.π (atInfinity (realPart A))
        (finiteLineVector D.cusp D.chi 2 (lineBeta n) (finiteGroup g)
          (lineRealSection D m w (realGroup g)))) := by
    rw [← Module.End.mul_apply, ← map_mul, atFinite_mul_atInfinity_comm, ← adelic_split A]
  rw [hsplit]
  congr 1
  rw [normPower_split (GeneralLinearGroup.det A) (lineBeta n), realUnitPart_det, finiteUnitPart_det,
    TernaryPeriodPolynomials.EisensteinRegularization.Helpers.normPower_realAdeleUnit]
  unfold blockFactor
  rw [GeneralLinearGroup.val_det_apply]
  ring

/-- Right invariance under the finite level. -/
theorem lineVector_level (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)
    (hsph : w ∈ sphericalSubspace D.cusp) (g : AdelicGL) (k : finiteLevel) :
    lineVector D m w (g * atFinite k.val) = lineVector D m w g := by
  unfold lineVector
  rw [map_mul, map_mul, realGroup_eq_realPart (atFinite k.val), realPart_atFinite, mul_one,
    finiteGroup_eq_finitePart (atFinite k.val), finitePart_atFinite]
  exact finiteLineVector_mul_level D.chi 2 (lineBeta n) hχ (lineRealSection_spherical hsph _) _ k

end Section

/-! ## The scalar section is induced -/

section Induced

variable {n : ℕ} {D : InducingData n} {m : ℕ} {w : D.cusp.H}

theorem line_exponent_eq :
    ((n : ℂ) + 3) / 2 - inductionExponent .line cohomologicalPoint = lineBeta n := by
  unfold inductionExponent cohomologicalPoint lineBeta
  ring

theorem line_binaryExponent_eq :
    binaryInductionExponent n .line cohomologicalPoint = lineBeta n := by
  unfold binaryInductionExponent inductionExponent cohomologicalPoint lineBeta
  ring

theorem line_corner_exponent_eq : 2 * inductionExponent .line cohomologicalPoint = 2 := by
  unfold inductionExponent cohomologicalPoint
  ring

theorem normPower_neg_mul (t : Adelesˣ) (z : ℂ) : normPower t (-z) * normPower t z = 1 := by
  unfold normPower
  rw [← Complex.exp_add]
  simp

/-- The realization of the vector section at a `GL₂` Levi translate. -/
theorem lineFunction_levi (hw : w ∈ D.cusp.smooth)
    (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)
    (hrot : RotationWeight D.cusp m w) (hsph : w ∈ sphericalSubspace D.cusp)
    (A : BinaryAdelicGL) (g : AdelicGL) :
    normPower (GeneralLinearGroup.det A) (-(lineBeta n)) *
        lineFunction D m w hw (lineLevi 1 A * g) =
      D.cusp.realize (lineVectorS D m w hw g) A := by
  have hvec : lineVectorS D m w hw (lineLevi 1 A * g) =
      normPower (GeneralLinearGroup.det A) (lineBeta n) •
        (⟨D.cusp.π A (lineVectorS D m w hw g).val,
          D.cusp.smooth_stable _ _ (lineVectorS D m w hw g).property⟩ : D.cusp.smooth) := by
    apply Subtype.ext
    exact lineVector_lineLevi_block hχ hrot hsph A g
  unfold lineFunction
  rw [hvec, map_smul, Pi.smul_apply, smul_eq_mul, ← mul_assoc, normPower_neg_mul, one_mul,
    D.cusp.equivariant, one_mul]

/-- The scalar section at a real right translate. -/
theorem lineFunction_mul_real (hw : w ∈ D.cusp.smooth) (g : AdelicGL) (y : RealGL3) :
    lineFunction D m w hw (g * atInfinity y) =
      finiteLineFactor D.chi 2 (lineBeta n) (finiteLineParabolic (finiteGroup g))
          (finiteLineParabolic_mem _) *
        D.cusp.realize (lineSectionSmooth D.cusp m 0 2 (lineBeta n) w hw realLineIwasawa
          (realGroup g * y))
          (atFinite (lineBlockGL (finiteLineParabolic (finiteGroup g))
            (finiteLineParabolic_mem _))) := by
  have hf : finiteGroup (g * atInfinity y) = finiteGroup g := by
    rw [map_mul, finiteGroup_eq_finitePart (atInfinity y), finitePart_atInfinity, mul_one]
  have hr : realGroup (g * atInfinity y) = realGroup g * y := by
    rw [map_mul, realGroup_eq_realPart (atInfinity y), realPart_atInfinity]
  have hvec : lineVectorS D m w hw (g * atInfinity y) =
      finiteLineFactor D.chi 2 (lineBeta n) (finiteLineParabolic (finiteGroup g))
          (finiteLineParabolic_mem _) •
        (⟨D.cusp.π (atFinite (lineBlockGL (finiteLineParabolic (finiteGroup g))
            (finiteLineParabolic_mem _)))
          (lineSectionSmooth D.cusp m 0 2 (lineBeta n) w hw realLineIwasawa (realGroup g * y)).val,
          D.cusp.smooth_stable _ _ (lineSectionSmooth D.cusp m 0 2 (lineBeta n) w hw
            realLineIwasawa (realGroup g * y)).property⟩ : D.cusp.smooth) := by
    apply Subtype.ext
    change finiteLineVector D.cusp D.chi 2 (lineBeta n) (finiteGroup (g * atInfinity y))
        (lineRealSection D m w (realGroup (g * atInfinity y))) = _
    rw [hf, hr, lineRealSection, ← lineSectionSmooth_val D.cusp m 0 2 (lineBeta n) w hw]
    rfl
  unfold lineFunction
  rw [hvec, map_smul, Pi.smul_apply, smul_eq_mul, D.cusp.equivariant, one_mul]

/-- **The scalar section is a normalized line-induced section.** -/
theorem lineFunction_isInduced (hw : w ∈ D.cusp.smooth)
    (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)
    (hrot : RotationWeight D.cusp m w) (hsph : w ∈ sphericalSubspace D.cusp) :
    IsInduced D .line cohomologicalPoint (lineFunction D m w hw) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g
    have hS := lineSectionSmooth_realize_smooth D.cusp m 0 2 (lineBeta n) w hw realLineIwasawa
      (atFinite (lineBlockGL (finiteLineParabolic (finiteGroup g)) (finiteLineParabolic_mem _)))
    have hL := smooth_comp_mul_left _ hS (realGroup g)
    have hC := smooth_const_mul hL (finiteLineFactor D.chi 2 (lineBeta n)
      (finiteLineParabolic (finiteGroup g)) (finiteLineParabolic_mem _))
    exact TernaryPeriodPolynomials.HeckeTranslate.SmoothClosure.smooth_congr hC
      (fun x => lineFunction_mul_real hw g (x 0))
  · intro k g
    unfold lineFunction
    rw [show lineVectorS D m w hw (g * atFinite k.val) = lineVectorS D m w hw g from
      Subtype.ext (lineVector_level hχ hsph g k)]
  · intro a
    refine ⟨fun x => lineVectorS D m w hw (a * atInfinity (x (Fin.last 0))), ?_, ?_⟩
    · -- the Hilbert-valued lift is analytic
      have hS := lineSection_smooth D.cusp m 0 2 (lineBeta n) w hw realLineIwasawa
      have hL := smooth_comp_mul_left _ hS (realGroup a)
      have hT := smooth_clm_comp
        ((finiteLineFactor D.chi 2 (lineBeta n) (finiteLineParabolic (finiteGroup a))
            (finiteLineParabolic_mem _)) •
          piCLM D.cusp (atFinite (lineBlockGL (finiteLineParabolic (finiteGroup a))
            (finiteLineParabolic_mem _)))) hL
      refine TernaryPeriodPolynomials.HeckeTranslate.SmoothClosure.smooth_congr hT
        (fun x => ?_)
      have hf : finiteGroup (a * atInfinity (x (Fin.last 0))) = finiteGroup a := by
        rw [map_mul, finiteGroup_eq_finitePart (atInfinity _), finitePart_atInfinity, mul_one]
      have hr : realGroup (a * atInfinity (x (Fin.last 0))) = realGroup a * x 0 := by
        rw [map_mul, realGroup_eq_realPart (atInfinity _), realPart_atInfinity]
        rfl
      change finiteLineVector D.cusp D.chi 2 (lineBeta n) (finiteGroup (a * atInfinity (x (Fin.last 0))))
          (lineRealSection D m w (realGroup (a * atInfinity (x (Fin.last 0))))) = _
      rw [hf, hr]
      rfl
    · intro x A
      change D.cusp.realize (lineVectorS D m w hw (a * atInfinity (x (Fin.last 0)))) A =
        normPower (GeneralLinearGroup.det A) (-binaryInductionExponent n .line cohomologicalPoint) *
          lineFunction D m w hw (lineLevi 1 A * (a * atInfinity (x (Fin.last 0))))
      rw [line_binaryExponent_eq]
      exact (lineFunction_levi hw hχ hrot hsph A _).symm
  · refine ⟨?_, ?_, ?_⟩
    · intro a b g
      unfold lineFunction
      rw [show lineVectorS D m w hw (lineUnipotent a b * g) = lineVectorS D m w hw g from
        Subtype.ext (lineVector_lineUnipotent hχ hrot hsph a b g)]
    · intro t g
      have hvec : lineVectorS D m w hw (lineLevi t 1 * g) =
          (D.chi.toMonoidHom t * normPower t 2) • lineVectorS D m w hw g :=
        Subtype.ext (lineVector_lineLevi_corner hχ hrot hsph t g)
      unfold lineFunction
      rw [hvec, map_smul, Pi.smul_apply, smul_eq_mul, line_corner_exponent_eq]
    · intro g
      refine ⟨lineVectorS D m w hw g, ?_⟩
      funext A
      rw [line_exponent_eq]
      exact (lineFunction_levi hw hχ hrot hsph A g).symm

end Induced

/-! ## Nonvanishing at the good-line cusp -/

section Nonvanishing

theorem exists_circle_pow_ne_one (m : ℕ) (hm : 0 < m) : ∃ a : Circle, (a : ℂ) ^ (2 * m) ≠ 1 := by
  refine ⟨Circle.exp (Real.pi / (2 * m)), ?_⟩
  rw [Circle.coe_exp, ← Complex.exp_nat_mul]
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have harg : ((2 * m : ℕ) : ℂ) * (((Real.pi / (2 * m) : ℝ) : ℂ) * Complex.I) =
      (Real.pi : ℂ) * Complex.I := by
    push_cast
    field_simp
  rw [harg, Complex.exp_pi_mul_I]
  norm_num

theorem lineLevi_rotation_orth (a : Circle) :
    IsOrthogonalReal (lineLevi 1 (TernaryPeriodPolynomials.SphericalDetection.Helpers.binaryRotations a)) := by
  have hn := Circle.normSq_coe a
  rw [Complex.normSq_apply] at hn
  unfold IsOrthogonalReal
  rw [lineLevi_val, binaryRotations_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply] <;> nlinarith [hn]

variable {σ : CuspidalRepresentation} {m : ℕ} {w : σ.H}

theorem kPart_one_eq : kPart σ m 0 w 1 = w + wPlus σ w := by
  simp [kPart]

/-- Vectors of opposite nonzero weights are independent: `w + σ(ε) w ≠ 0`. -/
theorem add_wPlus_ne_zero (hm : 0 < m) (hw0 : w ≠ 0) (hrot : RotationWeight σ m w) :
    w + wPlus σ w ≠ 0 := by
  intro h
  obtain ⟨a, ha⟩ := exists_circle_pow_ne_one m hm
  have hplus : wPlus σ w = -w := eq_neg_of_add_eq_zero_right h
  have h2 := congrArg (σ.π (atInfinity (TernaryPeriodPolynomials.SphericalDetection.Helpers.binaryRotations a))) h
  rw [map_add, hrot a, rep_rotation_wPlus σ m w hrot a, hplus, map_zero, smul_neg,
    ← sub_eq_add_neg] at h2
  have h3 : ((a : ℂ) ^ (-(m : ℤ)) - (a : ℂ) ^ m) • w = 0 := by
    rw [sub_smul]
    exact h2
  rcases smul_eq_zero.mp h3 with h4 | h4
  · apply ha
    have heq : (a : ℂ) ^ (-(m : ℤ)) = (a : ℂ) ^ m := sub_eq_zero.mp h4
    have ha0 : (a : ℂ) ≠ 0 := Circle.coe_ne_zero a
    rw [_root_.zpow_neg, zpow_natCast] at heq
    calc (a : ℂ) ^ (2 * m) = (a : ℂ) ^ m * (a : ℂ) ^ m := by ring
      _ = (a : ℂ) ^ m * ((a : ℂ) ^ m)⁻¹ := by rw [heq]
      _ = 1 := mul_inv_cancel₀ (pow_ne_zero _ ha0)
  · exact hw0 h4

/-- The real parts of a rational matrix. -/
theorem realPart_rational {k : ℕ} (γ : GeneralLinearGroup (Fin k) ℚ) :
    realPart (GeneralLinearGroup.map rationalAdele γ) = GeneralLinearGroup.map (algebraMap ℚ ℝ) γ := by
  apply Units.ext
  refine Matrix.ext fun i j => rfl

theorem finitePart_rational {k : ℕ} (γ : GeneralLinearGroup (Fin k) ℚ) :
    finitePart (GeneralLinearGroup.map rationalAdele γ) =
      GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) γ := by
  apply Units.ext
  refine Matrix.ext fun i j => rfl

/-- A nonzero spherical smooth vector has a nonzero realization at a real point. -/
theorem exists_real_point (u : σ.smooth) (hu : u ≠ 0) (hsph : u.val ∈ sphericalSubspace σ) :
    ∃ B : BinaryRealGL, σ.realize u (atInfinity B) ≠ 0 := by
  have h1 : σ.realize u ≠ 0 := fun h => hu (σ.injective (h.trans (map_zero _).symm))
  obtain ⟨z, hz⟩ := Function.ne_iff.mp h1
  obtain ⟨γ, k, hfin⟩ :=
    TernaryPeriodPolynomials.SphericalDetection.Helpers.finiteGL_rational_integral_factorization
      (finitePart z)
  set γR : BinaryRealGL := GeneralLinearGroup.map (algebraMap ℚ ℝ) γ
  set γF : BinaryFiniteGL := GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) γ
  set K : BinaryFiniteGL := GeneralLinearGroup.map integralEmbedding k
  have hrat : GeneralLinearGroup.map rationalAdele γ = atInfinity γR * atFinite γF := by
    conv_lhs => rw [adelic_split (GeneralLinearGroup.map rationalAdele γ)]
    rw [realPart_rational, finitePart_rational]
  have hc : atFinite γF * atInfinity (γR⁻¹ * realPart z) =
      atInfinity (γR⁻¹ * realPart z) * atFinite γF := atFinite_mul_atInfinity_comm _ _
  have hzsplit : z = GeneralLinearGroup.map rationalAdele γ *
      (atInfinity (γR⁻¹ * realPart z) * atFinite K) := by
    rw [hrat]
    calc z = atInfinity (realPart z) * atFinite (finitePart z) := adelic_split z
      _ = atInfinity (γR * (γR⁻¹ * realPart z)) * atFinite (γF * K) := by
          rw [mul_inv_cancel_left, hfin]
      _ = atInfinity γR * atInfinity (γR⁻¹ * realPart z) * (atFinite γF * atFinite K) := by
          rw [atInfinity_mul, atFinite_mul]
      _ = atInfinity γR * (atFinite γF * atInfinity (γR⁻¹ * realPart z)) * atFinite K := by
          rw [hc]; group
      _ = atInfinity γR * atFinite γF * (atInfinity (γR⁻¹ * realPart z) * atFinite K) := by
          group
  refine ⟨γR⁻¹ * realPart z, ?_⟩
  rw [hzsplit, σ.leftRational, ← σ.equivariant] at hz
  have hfix : (⟨σ.π (atFinite K) u.val, σ.smooth_stable _ _ u.property⟩ : σ.smooth) = u :=
    Subtype.ext (hsph k)
  rwa [hfix] at hz

end Nonvanishing

/-! ## The section input at the good line -/

section Construction

variable {n : ℕ}

theorem realGroup_rationalGroup (q : RationalGL3) :
    realGroup (rationalGroup q) = GeneralLinearGroup.map (algebraMap ℚ ℝ) q := by
  apply Units.ext
  refine Matrix.ext fun i j => rfl

theorem rationalFinite_goodLine_inv :
    rationalFinite (rational referenceIntegral)⁻¹ =
      GeneralLinearGroup.map integralEmbedding (goodLineFrame IntegralAdeles)⁻¹ := by
  rw [map_inv, rationalFinite_goodLine, map_inv]

/-- **The section input `LineSectionConstruction D true`**, for `χ` trivial on `Ẑ^×` (hence on the
whole idele class group). -/
theorem lineSectionConstruction_true_of_character (D : InducingData n)
    (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1) :
    LineSectionConstruction D true := by
  intro hsph
  have hodd :=
    TernaryPeriodPolynomials.LevelOneCohomologicalParity.Helpers.cohomological_spherical_odd
      n D.cusp D.cohomological hsph
  obtain ⟨halfWeight, w, hweight, hw0, hwsph, hwrot, _, _⟩ :=
    TernaryPeriodPolynomials.SphericalDetection.Helpers.cohomological_exists_spherical_holomorphic
      D.cusp hsph hodd D.cohomological
  have hrot : RotationWeight D.cusp (n + 3) w.val := by
    intro a
    rw [hwrot a, hweight]
    congr 2
  have hsph' : w.val ∈ sphericalSubspace D.cusp := hwsph
  have hw0' : w.val ≠ 0 := fun h => hw0 (Subtype.ext h)
  have hu0 : kPart D.cusp (n + 3) 0 w.val 1 ≠ 0 := by
    rw [kPart_one_eq]
    exact add_wPlus_ne_zero (by omega) hw0' hrot
  have husph : kPart D.cusp (n + 3) 0 w.val 1 ∈ sphericalSubspace D.cusp := by
    rw [kPart_one_eq]
    exact Submodule.add_mem _ hsph' (sphericalSubspace_real hsph' _)
  obtain ⟨B₀, hB₀⟩ := exists_real_point
    ⟨kPart D.cusp (n + 3) 0 w.val 1, kPart_mem D.cusp (n + 3) 0 w.val w.property 1⟩
    (fun h => hu0 (congrArg Subtype.val h)) husph
  set rR : RealGL3 := GeneralLinearGroup.map (algebraMap ℚ ℝ) (rational referenceIntegral)
  set h : RealGL3 := rR * lineLevi 1 B₀
  refine ⟨fun g => lineFunction D (n + 3) w.val w.property (g * atInfinity h),
    TernaryPeriodPolynomials.ArchimedeanConstant.isInduced_right_real h
      (lineFunction_isInduced w.property hχ hrot hsph'), ?_⟩
  show lineFunction D (n + 3) w.val w.property
    (rationalGroup (rational referenceIntegral)⁻¹ * atInfinity h) ≠ 0
  have hf : finiteGroup (rationalGroup (rational referenceIntegral)⁻¹ * atInfinity h) =
      GeneralLinearGroup.map integralEmbedding (goodLineFrame IntegralAdeles)⁻¹ := by
    rw [map_mul, finiteGroup_eq_finitePart (atInfinity h), finitePart_atInfinity, mul_one,
      finiteGroup_rational, rationalFinite_goodLine_inv]
  have hr : realGroup (rationalGroup (rational referenceIntegral)⁻¹ * atInfinity h) =
      lineLevi 1 B₀ := by
    rw [map_mul, realGroup_eq_realPart (atInfinity h), realPart_atInfinity, map_inv, map_inv,
      realGroup_rationalGroup]
    show rR⁻¹ * (rR * lineLevi 1 B₀) = lineLevi 1 B₀
    rw [inv_mul_cancel_left]
  have hreal : lineRealSection D (n + 3) w.val (lineLevi 1 B₀) =
      blockFactor (lineBeta n) B₀.val.det •
        D.cusp.π (atInfinity B₀) (kPart D.cusp (n + 3) 0 w.val 1) := by
    unfold lineRealSection
    rw [← mul_one (lineLevi 1 B₀), lineSection_equivariant D.cusp (n + 3) 0 2 (lineBeta n) w.val hrot
      realLineIwasawa (lineLevi_mem _ _), leviFactor_lineLevi, lineBlock_lineLevi, Units.val_one,
      cornerFactor_one, one_mul]
    congr 2
    unfold lineSection
    rw [realLineIwasawa.B_one, realLineIwasawa.K_one, leviFactor_one, lineBlock_one,
      rep_atInfinity_one, one_smul]
  have hvec : lineVectorS D (n + 3) w.val w.property
      (rationalGroup (rational referenceIntegral)⁻¹ * atInfinity h) =
      blockFactor (lineBeta n) B₀.val.det •
        (⟨D.cusp.π (atInfinity B₀) (kPart D.cusp (n + 3) 0 w.val 1),
          D.cusp.smooth_stable _ _ (kPart_mem D.cusp (n + 3) 0 w.val w.property 1)⟩ :
            D.cusp.smooth) := by
    apply Subtype.ext
    change finiteLineVector D.cusp D.chi 2 (lineBeta n)
        (finiteGroup (rationalGroup (rational referenceIntegral)⁻¹ * atInfinity h))
        (lineRealSection D (n + 3) w.val
          (realGroup (rationalGroup (rational referenceIntegral)⁻¹ * atInfinity h))) = _
    rw [hf, hr, finiteLineVector_integral D.chi 2 (lineBeta n) hχ
      (lineRealSection_spherical hsph' _), hreal]
    rfl
  unfold lineFunction
  rw [hvec, map_smul, Pi.smul_apply, smul_eq_mul]
  refine mul_ne_zero (Complex.exp_ne_zero _) ?_
  have heq := D.cusp.equivariant (atInfinity B₀)
    ⟨kPart D.cusp (n + 3) 0 w.val 1, kPart_mem D.cusp (n + 3) 0 w.val w.property 1⟩ 1
  rw [one_mul] at heq
  rw [show D.cusp.realize (⟨D.cusp.π (atInfinity B₀) (kPart D.cusp (n + 3) 0 w.val 1),
      D.cusp.smooth_stable _ _ (kPart_mem D.cusp (n + 3) 0 w.val w.property 1)⟩ : D.cusp.smooth) 1 =
      D.cusp.realize ⟨kPart D.cusp (n + 3) 0 w.val 1, kPart_mem D.cusp (n + 3) 0 w.val w.property 1⟩
        (atInfinity B₀) from heq]
  exact hB₀

end Construction

end TernaryPeriodPolynomials.SourceConstruction
