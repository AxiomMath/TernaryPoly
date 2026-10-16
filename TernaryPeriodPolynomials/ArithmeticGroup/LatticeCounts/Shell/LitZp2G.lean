module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.LitFibreG
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.LitZp2
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.LitSet

@[expose] public section


/-!
# The literal integral over `ℤ_p²` at a general base point (`0 < det g∞`)

Formalized by Claude Haiku 5.5.

Generalises `ShellLitZp2` to a base point `g_f` with `gf.val.map (finiteEvaluation v) = gp.val`,
`IntGL v gp.val`. For integral `z ∈ ℤ_p²` the literal integrand at `g_f` is the constant
`normPower(det g_f) b · vhValueFull k h g∞ (g_f · ι_v(gp)⁻¹)`, and the integral over `ℤ_p²`
(product measure one) equals that constant.
-/

open MeasureTheory Matrix PadicInt
open TernaryPeriodPolynomials.Argument.LatticeCounts.RightTranslation (ιGL)
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalAdelic (IntGL)
open TernaryPeriodPolynomials.Argument.LatticeCounts.ModelComparisonNeg (vhValueFull)
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitZp2 (exists_k0_integral ιGL_one)
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitFibreG
  (shellIntegrandG shellIntegrandG_eq_block)
open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.SphericalDetection.Helpers
  (cuspScalarWeightedLinear finitePadicMeasure finitePadicMeasure_normalized finiteCompletionPadicEquiv)
open TernaryPeriodPolynomials.Spectral.LevelOneHecke (levelOne)
open TernaryPeriodPolynomials.PlaneEisensteinContinuation

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitZp2G

variable {σ : CuspidalRepresentation} {n : ℕ}

/-- On `ℤ_p²` the literal integrand at a general base point is the constant
`normPower(det g_f) b · vhValueFull k h g∞ (g_f · ι_v(gp)⁻¹)` (for `k = -2·halfWeight`). -/
theorem shellIntegrandG_zp2 (v : FinitePlace) [Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime]
    (I : EichlerInput σ n)
    (h : CuspForm levelOne (-2 * I.halfWeight))
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (gInf : BinaryRealGL) (gf : BinaryFiniteGL)
    (gp : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))
    (hgp : gf.val.map (finiteEvaluation v) = gp.val) (hgI : IntGL v gp.val)
    {z : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val] × ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val]}
    (hz : z ∈ Padic.Zp2 (Rat.HeightOneSpectrum.primesEquiv v).val) :
    shellIntegrandG v I gf gInf z =
      normPower (Norm.finiteAdeleUnit (GeneralLinearGroup.det gf))
          (((-2 * I.halfWeight : ℤ) : ℂ) / 2) *
        vhValueFull (-2 * I.halfWeight) h gInf (gf * ιGL v gp⁻¹) := by
  obtain ⟨k, hK⟩ := exists_k0_integral (s := z.1) (t := z.2) hz.1 hz.2
  have hA : ∀ i j, (1 : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)).val i j =
      (finiteCompletionPadicEquiv v).symm
        (((1 : Matrix (Fin 2) (Fin 2) ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).val]) i j :
          ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).val]) :
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val]) := by
    intro i j
    rw [Units.val_one]
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij]
  have key := shellIntegrandG_eq_block v I h hform gInf (r := 0) (z := z) hK 1 hA gf gp hgp hgI
  rw [key, ιGL_one, one_mul]
  simp

/-- The integral over `ℤ_p²` of the literal integrand at a general base point is the constant
`normPower(det g_f) b · vhValueFull k h g∞ (g_f · ι_v(gp)⁻¹)`: the set has product measure one. -/
theorem integral_zp2_literal_G (v : FinitePlace) [Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime]
    (I : EichlerInput σ n)
    (h : CuspForm levelOne (-2 * I.halfWeight))
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (gInf : BinaryRealGL) (gf : BinaryFiniteGL)
    (gp : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))
    (hgp : gf.val.map (finiteEvaluation v) = gp.val) (hgI : IntGL v gp.val) :
    ∫ z in Padic.Zp2 (Rat.HeightOneSpectrum.primesEquiv v).val,
        shellIntegrandG v I gf gInf z
      ∂((finitePadicMeasure v).prod (finitePadicMeasure v)) =
      normPower (Norm.finiteAdeleUnit (GeneralLinearGroup.det gf))
          (((-2 * I.halfWeight : ℤ) : ℂ) / 2) *
        vhValueFull (-2 * I.halfWeight) h gInf (gf * ιGL v gp⁻¹) := by
  have hset : Padic.Zp2 (Rat.HeightOneSpectrum.primesEquiv v).val =
      {value | ‖value‖ ≤ 1} ×ˢ {value | ‖value‖ ≤ 1} := rfl
  have hnorm := finitePadicMeasure_normalized v
  have hmeas : ((finitePadicMeasure v).prod (finitePadicMeasure v))
      (Padic.Zp2 (Rat.HeightOneSpectrum.primesEquiv v).val) = 1 := by
    rw [hset, Measure.prod_prod, hnorm, mul_one]
  have hreal : ((finitePadicMeasure v).prod (finitePadicMeasure v)).real
      (Padic.Zp2 (Rat.HeightOneSpectrum.primesEquiv v).val) = 1 := by
    simp [Measure.real, hmeas]
  have heq : Set.EqOn (fun z => shellIntegrandG v I gf gInf z)
      (fun _ => normPower (Norm.finiteAdeleUnit (GeneralLinearGroup.det gf))
          (((-2 * I.halfWeight : ℤ) : ℂ) / 2) *
        vhValueFull (-2 * I.halfWeight) h gInf (gf * ιGL v gp⁻¹))
      (Padic.Zp2 (Rat.HeightOneSpectrum.primesEquiv v).val) :=
    fun z hz => shellIntegrandG_zp2 v I h hform gInf gf gp hgp hgI hz
  have hms : MeasurableSet (Padic.Zp2 (Rat.HeightOneSpectrum.primesEquiv v).val) :=
    (ShellLitSet.isOpen_zp2 (p := (Rat.HeightOneSpectrum.primesEquiv v).val)).measurableSet
  rw [setIntegral_congr_fun hms heq, setIntegral_const, hreal, one_smul]

end TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitZp2G

end
