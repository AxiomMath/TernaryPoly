module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.REVector
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.REJacobian

@[expose] public section


/-!
# R-e: The scalar identity of the exponents

`scalar_identity`: `|d|²/|det A| · χ(d)|d|⁰|det A|^b = χ(d)|d|²|det A|^{b-1}`, i.e. the plane Jacobian constant turns the plane factor into the line factor of `lineBeta = (n+1)/2`.

Formalized by Claude Sonnet 5.5.
-/


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Filter
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open scoped ENNReal NNReal

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

/-- The norm of a finite idele, as a positive real number. -/
def finNorm (t : FiniteAdelesˣ) : ℝ := (adeleNorm (Norm.finiteAdeleUnit t) : ℝ)

theorem finNorm_pos (t : FiniteAdelesˣ) : 0 < finNorm t := by
  unfold finNorm
  exact_mod_cast adeleNorm_pos _

theorem finNorm_mul (s t : FiniteAdelesˣ) : finNorm (s * t) = finNorm s * finNorm t := by
  unfold finNorm
  rw [FiniteLatticeMeasure.finiteUnit_mul, map_mul, NNReal.coe_mul]

theorem finNorm_inv (t : FiniteAdelesˣ) : finNorm t⁻¹ = (finNorm t)⁻¹ := by
  unfold finNorm
  rw [FiniteLatticeMeasure.finiteUnit_inv, map_inv, NNReal.coe_inv]

theorem scaleConstant_toReal (α : FiniteAdelesˣ) : (scaleConstant α).toReal = (finNorm α)⁻¹ := by
  unfold scaleConstant
  rw [ENNReal.coe_toReal]
  exact finNorm_inv α

theorem normPower_succ (t : FiniteAdelesˣ) (s : ℂ) :
    normPower (Norm.finiteAdeleUnit t) (s + 1) = normPower (Norm.finiteAdeleUnit t) s * (finNorm t : ℂ) := by
  unfold normPower finNorm
  rw [add_mul, one_mul, Complex.exp_add]
  congr 1
  rw [← Complex.ofReal_exp, Real.exp_log (by exact_mod_cast adeleNorm_pos _)]

theorem normPower_two (t : FiniteAdelesˣ) :
    normPower (Norm.finiteAdeleUnit t) 2 = (finNorm t : ℂ) ^ 2 := by
  have one : normPower (Norm.finiteAdeleUnit t) 1 = (finNorm t : ℂ) := by
    have := normPower_succ t 0
    rw [zero_add, normPower_zero', one_mul] at this
    exact this
  have h := normPower_succ t 1
  rw [one] at h
  have two : (1 : ℂ) + 1 = 2 := by norm_num
  rw [two] at h
  rw [h]
  ring

theorem scalar_identity (χ : RankOneCharacter) (b : ℂ) (d u₀ u₁ : FiniteAdelesˣ) :
    (((scaleConstant (d⁻¹ * u₀) * scaleConstant (d⁻¹ * u₁)).toReal : ℝ) : ℂ) *
        (χ.toMonoidHom (Norm.finiteAdeleUnit d) * normPower (Norm.finiteAdeleUnit d) 0 *
          normPower (Norm.finiteAdeleUnit (u₀ * u₁)) b) =
      χ.toMonoidHom (Norm.finiteAdeleUnit d) * normPower (Norm.finiteAdeleUnit d) 2 *
        normPower (Norm.finiteAdeleUnit (u₀ * u₁)) (b - 1) := by
  rw [ENNReal.toReal_mul, scaleConstant_toReal, scaleConstant_toReal, normPower_zero', normPower_two]
  have eb : normPower (Norm.finiteAdeleUnit (u₀ * u₁)) b =
      normPower (Norm.finiteAdeleUnit (u₀ * u₁)) (b - 1) * (finNorm (u₀ * u₁) : ℂ) := by
    rw [← normPower_succ, sub_add_cancel]
  rw [eb]
  simp only [finNorm_mul, finNorm_inv]
  have p₀ := finNorm_pos u₀
  have p₁ := finNorm_pos u₁
  have pd := finNorm_pos d
  have q₀ : (finNorm u₀ : ℂ) ≠ 0 := by exact_mod_cast p₀.ne'
  have q₁ : (finNorm u₁ : ℂ) ≠ 0 := by exact_mod_cast p₁.ne'
  have qd : (finNorm d : ℂ) ≠ 0 := by exact_mod_cast pd.ne'
  push_cast
  field_simp

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
