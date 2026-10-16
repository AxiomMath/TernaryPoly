module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Finite.Fourier

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLatticeMeasure

theorem finiteUnit_mul (first second : FiniteAdelesˣ) :
    Norm.finiteAdeleUnit (first * second) = Norm.finiteAdeleUnit first * Norm.finiteAdeleUnit second := by
  apply Units.ext
  ext <;> simp [Norm.finiteAdeleUnit]

theorem finiteUnit_one : Norm.finiteAdeleUnit 1 = 1 := by
  apply Units.ext
  rfl

theorem finiteUnit_inv (scale : FiniteAdelesˣ) :
    Norm.finiteAdeleUnit scale⁻¹ = (Norm.finiteAdeleUnit scale)⁻¹ := by
  apply Units.ext
  rfl

theorem domain_image (scale : FiniteAdelesˣ) :
    (fun value : Adeles => (Norm.finiteAdeleUnit scale).val * value) '' additiveDomain =
      Set.Ico 0 1 ×ˢ FiniteFourier.lattice scale := by
  change (fun value : ℝ × FiniteAdeles => (1 * value.1, scale.val * value.2)) ''
    (Set.Ico 0 1 ×ˢ Set.range integralEmbedding) = _
  simp only [one_mul]
  rw [← Set.prod_image_image_eq (m₁ := fun value : ℝ => value)
    (m₂ := fun value : FiniteAdeles => scale.val * value), Set.image_id', ← Set.range_comp]
  rfl

theorem lattice_measure (scale : FiniteAdelesˣ) :
    finiteMeasure (FiniteFourier.lattice scale) = (adeleNorm (Norm.finiteAdeleUnit scale) : ℝ≥0∞) := by
  rw [ProductFormula.adeleNorm_eq_measure_image, domain_image, adeleMeasure, Measure.prod_prod,
    Real.volume_Ico]
  norm_num

theorem lattice_real_measure (scale : FiniteAdelesˣ) :
    finiteMeasure.real (FiniteFourier.lattice scale) = (adeleNorm (Norm.finiteAdeleUnit scale) : ℝ) := by
  rw [Measure.real, lattice_measure, ENNReal.coe_toReal]

theorem lattice_real_measure_pos (scale : FiniteAdelesˣ) :
    0 < finiteMeasure.real (FiniteFourier.lattice scale) := by
  rw [lattice_real_measure]
  exact adeleNorm_pos _

theorem lattice_real_measure_inv (scale : FiniteAdelesˣ) :
    finiteMeasure.real (FiniteFourier.lattice scale⁻¹) =
      (finiteMeasure.real (FiniteFourier.lattice scale))⁻¹ := by
  rw [lattice_real_measure, lattice_real_measure, finiteUnit_inv, map_inv, NNReal.coe_inv]

theorem lattice_real_measure_mul_inv (scale : FiniteAdelesˣ) :
    finiteMeasure.real (FiniteFourier.lattice scale) *
      finiteMeasure.real (FiniteFourier.lattice scale⁻¹) = 1 := by
  rw [lattice_real_measure_inv, mul_inv_cancel₀ (ne_of_gt (lattice_real_measure_pos scale))]

def rationalScale (rational : ℚˣ) : FiniteAdelesˣ :=
  Units.map (algebraMap ℚ FiniteAdeles).toMonoidHom rational

theorem rational_decomposition (rational : ℚˣ) :
    Units.map rationalAdele.toMonoidHom rational =
      realAdeleUnit (Units.map (algebraMap ℚ ℝ).toMonoidHom rational) *
        Norm.finiteAdeleUnit (rationalScale rational) := by
  apply Units.ext
  apply Prod.ext <;> simp [realAdeleUnit, Norm.finiteAdeleUnit, rationalScale, rationalAdele]

theorem rational_lattice_measure (rational : ℚˣ) :
    finiteMeasure.real (FiniteFourier.lattice (rationalScale rational)) = |(rational.val : ℝ)|⁻¹ := by
  have product := congrArg (fun value : ℝ≥0 => (value : ℝ)) (ProductFormula.adeleNorm_rational rational)
  rw [rational_decomposition, map_mul, NNReal.coe_mul, Norm.adeleNorm_real] at product
  rw [lattice_real_measure]
  have realNonzero : (rational.val : ℝ) ≠ 0 := by exact_mod_cast rational.ne_zero
  change |(rational.val : ℝ)| * (adeleNorm (Norm.finiteAdeleUnit (rationalScale rational)) : ℝ) = 1 at product
  apply mul_left_cancel₀ (abs_ne_zero.mpr realNonzero)
  change |(rational.val : ℝ)| * (adeleNorm (Norm.finiteAdeleUnit (rationalScale rational)) : ℝ) = _
  rw [product, mul_inv_cancel₀ (abs_ne_zero.mpr realNonzero)]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLatticeMeasure
