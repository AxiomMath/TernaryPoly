module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagExactness.LineFlagConstantTerm
public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagExactness.BorelTranslate

@[expose] public section


/-!
# Borel conjugation of line-Levi-unipotent translates

Line-side analogue of `BorelTranslate`. For a rational upper-triangular `β`, the
real line-Levi unipotent `n'(t) = 1 + t E₁₂` satisfies
`n'(t) β = β · u · n'((β₂₂/β₁₁) t)` with `u` in the line radical. Consequently the
translated flag evaluations `F_t(x) = c(x)(n'(t) · q⁻¹)` of a line source cocycle
are permuted by the flag stabilizer through `t ↦ (β₂₂/β₁₁) t`.

Original work (AxiomDeep, Claude Opus 5.5).
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.FlagExactness

theorem lineLevi_mul_borel (t : ℝ) (β : RationalGL3) (h00 : β.val 0 0 ≠ 0) (h11 : β.val 1 1 ≠ 0)
    (h10 : β.val 1 0 = 0) (h20 : β.val 2 0 = 0) (h21 : β.val 2 1 = 0) :
    lineLevi 1 (binaryUnipotent ((t, 0) : Adeles)) * rationalGroup β =
      rationalGroup β *
        (lineUnipotent 0 (((-(t * ((β.val 2 2 * β.val 0 1 / (β.val 0 0 * β.val 1 1) : ℚ) : ℝ))),
            0) : Adeles) *
          lineLevi 1 (binaryUnipotent (((t * ((β.val 2 2 / β.val 1 1 : ℚ) : ℝ)), 0) : Adeles))) := by
  have h00' : ((β.val 0 0 : ℚ) : ℝ) ≠ 0 := by exact_mod_cast h00
  have h11' : ((β.val 1 1 : ℚ) : ℝ) ≠ 0 := by exact_mod_cast h11
  apply adelic_ext
  · apply Units.ext
    change ((lineLevi 1 (binaryUnipotent ((t, 0) : Adeles)) * rationalGroup β).val).map Prod.fst =
      ((rationalGroup β * (lineUnipotent 0 (((-(t * ((β.val 2 2 * β.val 0 1 /
        (β.val 0 0 * β.val 1 1) : ℚ) : ℝ))), 0) : Adeles) *
          lineLevi 1 (binaryUnipotent (((t * ((β.val 2 2 / β.val 1 1 : ℚ) : ℝ)), 0) : Adeles)))).val).map
            Prod.fst
    simp only [GeneralLinearGroup.coe_mul]
    apply Matrix.ext
    intro i j
    simp only [Matrix.map_apply, Matrix.mul_apply, Fin.sum_univ_three, lineLevi_val]
    fin_cases i <;> fin_cases j <;>
      simp [binaryUnipotent, lineUnipotent, upperUnipotent, rationalGroup, h10, h20, h21] <;>
      (try field_simp) <;> (try ring)
  · apply Units.ext
    change ((lineLevi 1 (binaryUnipotent ((t, 0) : Adeles)) * rationalGroup β).val).map Prod.snd =
      ((rationalGroup β * (lineUnipotent 0 (((-(t * ((β.val 2 2 * β.val 0 1 /
        (β.val 0 0 * β.val 1 1) : ℚ) : ℝ))), 0) : Adeles) *
          lineLevi 1 (binaryUnipotent (((t * ((β.val 2 2 / β.val 1 1 : ℚ) : ℝ)), 0) : Adeles)))).val).map
            Prod.snd
    simp only [GeneralLinearGroup.coe_mul]
    apply Matrix.ext
    intro i j
    simp only [Matrix.map_apply, Matrix.mul_apply, Fin.sum_univ_three, lineLevi_val]
    fin_cases i <;> fin_cases j <;>
      simp [binaryUnipotent, lineUnipotent, upperUnipotent, rationalGroup, h10, h20, h21]

/-- Line source cocycles absorb an upper-triangular rational factor behind a line Levi
unipotent, rescaling the unipotent coordinate. -/
theorem source_line_borel_translate {degree : ℕ} (data : InducingData degree)
    (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (isSource : IsSourceCocycle data .line source) (t : ℝ) (β : RationalGL3)
    (h00 : β.val 0 0 ≠ 0) (h11 : β.val 1 1 ≠ 0) (h10 : β.val 1 0 = 0) (h20 : β.val 2 0 = 0)
    (h21 : β.val 2 1 = 0) (vertices : Fin 3 → RealGL3) (g : AdelicGL) :
    source vertices (lineLevi 1 (binaryUnipotent ((t, 0) : Adeles)) * rationalGroup β * g) =
      source vertices
        (lineLevi 1 (binaryUnipotent (((t * ((β.val 2 2 / β.val 1 1 : ℚ) : ℝ)), 0) : Adeles)) * g) := by
  rw [lineLevi_mul_borel t β h00 h11 h10 h20 h21, mul_assoc, mul_assoc]
  rw [TernaryPeriodPolynomials.GraphPieces.RationalComparison.source_parabolicInvariant data
    TernaryPeriodPolynomials.GraphPieces.RationalNorm.rational_norm .line source isSource β
    ⟨h10, h20⟩]
  apply Subtype.ext
  apply MvPolynomial.ext
  intro monomial
  exact (isSource.1 vertices monomial).2.2.2.1 _ _ _

/-- The translated line flag evaluations are permuted by the flag stabilizer. -/
theorem lineTranslatedEvaluation_stabilizer {degree : ℕ} (data : InducingData degree)
    (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (isSource : IsSourceCocycle data .line source) (q : RationalGL3) (γ : rationalLevel)
    (h00 : (q⁻¹ * γ.val * q).val 0 0 ≠ 0) (h11 : (q⁻¹ * γ.val * q).val 1 1 ≠ 0)
    (h10 : (q⁻¹ * γ.val * q).val 1 0 = 0)
    (h20 : (q⁻¹ * γ.val * q).val 2 0 = 0) (h21 : (q⁻¹ * γ.val * q).val 2 1 = 0)
    (t : ℝ) (vertices : Fin 3 → RealGL3) :
    source (fun index => GeneralLinearGroup.map (algebraMap ℚ ℝ) γ.val * vertices index)
        (lineLevi 1 (binaryUnipotent ((t, 0) : Adeles)) * rationalGroup q⁻¹) =
      realCoefficientComponent degree data.chi (GeneralLinearGroup.map (algebraMap ℚ ℝ) γ.val)
        (source vertices
          (lineLevi 1 (binaryUnipotent
            (((t * (((q⁻¹ * γ.val * q).val 2 2 / (q⁻¹ * γ.val * q).val 1 1 : ℚ) : ℝ)), 0) : Adeles)) *
            rationalGroup q⁻¹)) := by
  rw [isSource.2.2.1]
  congr 1
  have hsplit := TernaryPeriodPolynomials.GraphPieces.Comparison.rationalGroup_split γ.val
  have hinf : atInfinity (GeneralLinearGroup.map (algebraMap ℚ ℝ) γ.val) =
      rationalGroup γ.val * atFinite (rationalFinite γ.val)⁻¹ := by
    rw [hsplit, mul_assoc, ← atFinite_inv', mul_inv_cancel, mul_one]
  have hconj : rationalGroup q⁻¹ * rationalGroup γ.val =
      rationalGroup (q⁻¹ * γ.val * q) * rationalGroup q⁻¹ := by
    rw [← map_mul, ← map_mul]
    congr 1
    group
  rw [hinf, ← mul_assoc, mul_assoc (lineLevi 1 _), hconj, ← mul_assoc]
  have hlevel : (rationalFinite γ.val)⁻¹ ∈ finiteLevel :=
    finiteLevel.inv_mem (TernaryPeriodPolynomials.GraphPieces.Comparison.rationalLevel_finiteLevel γ)
  rw [TernaryPeriodPolynomials.GraphPieces.Comparison.source_finiteInvariant data .line source
    isSource ⟨_, hlevel⟩]
  exact source_line_borel_translate data source isSource t _ h00 h11 h10 h20 h21 vertices _

end TernaryPeriodPolynomials.FlagExactness
