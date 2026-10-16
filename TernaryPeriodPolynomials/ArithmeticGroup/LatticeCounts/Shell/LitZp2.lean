module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.LitPlane
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.LitFibre
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.LitSet

@[expose] public section


/-!
# The literal integral over `ℤ_p²` (`0 < det g∞`)

Formalized by Claude Haiku 5.5.

For integral `z ∈ ℤ_p²` the literal integrand `shellIntegrand v I g∞ z` is the constant
`vhValue k h g∞ 1`: the `K0Spec 0` datum is `k = L(z)⁻¹ ∈ GL₃(ℤ_p)` with `A = 1`, so
`integrand_eq_vhValueFull` applies with `r = 0`. Since `μ(ℤ_p²) = 1` for the finite product
measure, the integral over `ℤ_p²` equals `vhValue k h g∞ 1`.
-/

open MeasureTheory Matrix PadicInt
open TernaryPeriodPolynomials.Argument.LatticeCounts.SeedK0 (K0Spec Lst toQ)
open TernaryPeriodPolynomials.Argument.LatticeCounts.AdelicValue (vhValue)
open TernaryPeriodPolynomials.Argument.LatticeCounts.RightTranslation (ιGL)
open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.SphericalDetection.Helpers
  (cuspScalarWeightedLinear finitePadicMeasure finitePadicMeasure_normalized finiteCompletionPadicEquiv)
open TernaryPeriodPolynomials.Spectral.LevelOneHecke (levelOne)
open TernaryPeriodPolynomials.Argument (IsNormalizedEigenform)

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitZp2

variable {σ : CuspidalRepresentation} {n : ℕ}

/-- The `k₀` datum for integral `s, t`, with `r = 0`: the matrix `L(s,t)⁻¹ ∈ GL₃(ℤ_p)` and
`A = 1`. -/
theorem exists_k0_integral {p : ℕ} [Fact p.Prime] {s t : ℚ_[p]} (hs : ‖s‖ ≤ 1) (ht : ‖t‖ ≤ 1) :
    ∃ k : Matrix (Fin 3) (Fin 3) ℤ_[p], K0Spec 0 s t k 1 := by
  obtain ⟨α, hα⟩ : ∃ α : ℤ_[p], (α : ℚ_[p]) = s := ⟨⟨s, hs⟩, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : ℤ_[p], (β : ℚ_[p]) = t := ⟨⟨t, ht⟩, rfl⟩
  refine ⟨!![-α, -β, 1; 1, 0, 0; 0, 1, 0], ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Matrix.det_fin_three]
  · simp
  · intro j
    fin_cases j <;> simp [Matrix.one_apply, hs, ht]
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [Lst, toQ, Matrix.mul_apply, Fin.sum_univ_three]
  · simp [Lst, toQ, Matrix.mul_apply, Fin.sum_univ_three, hα]
  · simp [Lst, toQ, Matrix.mul_apply, Fin.sum_univ_three, hβ]
  · simp [Lst, toQ, Matrix.mul_apply, Fin.sum_univ_three]

/-- `ι_v(1) = 1` in `GL₂(𝔸_f)`. -/
theorem ιGL_one (v : FinitePlace) : ιGL v 1 = 1 :=
  Units.ext (by simp [RightTranslation.ιGL_val, RightTranslation.ιMat_one])

/-- On `ℤ_p²` the literal integrand is the constant `vhValue k h g∞ 1` (for `0 < det g∞`). -/
theorem shellIntegrand_zp2 (v : FinitePlace) [Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime]
    (I : EichlerInput σ n)
    (h : CuspForm levelOne (-2 * I.halfWeight))
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (gInf : BinaryRealGL) (hgInf : 0 < (GeneralLinearGroup.det gInf).val)
    {z : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val] × ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val]}
    (hz : z ∈ Padic.Zp2 (Rat.HeightOneSpectrum.primesEquiv v).val) :
    ShellLitFibre.shellIntegrand v I gInf z = vhValue (-2 * I.halfWeight) h gInf 1 := by
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
  have key := ShellLitPlane.integrand_eq_vhValueFull v I h hform gInf (r := 0) (z := z) hK 1 hA
  unfold ShellLitFibre.shellIntegrand
  rw [key, ModelComparisonNeg.vhValueFull, ite_eq_left hgInf, ιGL_one]
  simp

/-- The integral over `ℤ_p²` of the literal integrand is `vhValue k h g∞ 1`: the set has
product measure one. -/
theorem integral_zp2_literal (v : FinitePlace) [Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime]
    (I : EichlerInput σ n)
    (h : CuspForm levelOne (-2 * I.halfWeight))
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (gInf : BinaryRealGL) (hgInf : 0 < (GeneralLinearGroup.det gInf).val) :
    ∫ z in Padic.Zp2 (Rat.HeightOneSpectrum.primesEquiv v).val,
        ShellLitFibre.shellIntegrand v I gInf z
      ∂((finitePadicMeasure v).prod (finitePadicMeasure v)) =
      vhValue (-2 * I.halfWeight) h gInf 1 := by
  have hset : Padic.Zp2 (Rat.HeightOneSpectrum.primesEquiv v).val =
      {value | ‖value‖ ≤ 1} ×ˢ {value | ‖value‖ ≤ 1} := rfl
  have hnorm := finitePadicMeasure_normalized v
  have hmeas : ((finitePadicMeasure v).prod (finitePadicMeasure v))
      (Padic.Zp2 (Rat.HeightOneSpectrum.primesEquiv v).val) = 1 := by
    rw [hset, Measure.prod_prod, hnorm, mul_one]
  have hreal : ((finitePadicMeasure v).prod (finitePadicMeasure v)).real
      (Padic.Zp2 (Rat.HeightOneSpectrum.primesEquiv v).val) = 1 := by
    simp [Measure.real, hmeas]
  have heq : Set.EqOn (fun z => ShellLitFibre.shellIntegrand v I gInf z)
      (fun _ => vhValue (-2 * I.halfWeight) h gInf 1)
      (Padic.Zp2 (Rat.HeightOneSpectrum.primesEquiv v).val) :=
    fun z hz => shellIntegrand_zp2 v I h hform gInf hgInf hz
  have hms : MeasurableSet (Padic.Zp2 (Rat.HeightOneSpectrum.primesEquiv v).val) :=
    (ShellLitSet.isOpen_zp2 (p := (Rat.HeightOneSpectrum.primesEquiv v).val)).measurableSet
  rw [setIntegral_congr_fun hms heq, setIntegral_const, hreal, one_smul]

end TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitZp2

end
