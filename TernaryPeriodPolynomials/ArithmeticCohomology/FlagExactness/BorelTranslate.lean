module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagExactness.FlagConstantTerm
public import TernaryPeriodPolynomials.ArithmeticCohomology.GraphPieces.RationalNorm

@[expose] public section


/-!
# Borel conjugation of Levi-unipotent translates

For a rational upper-triangular `β`, the real Levi unipotent `n(t)` satisfies
`n(t) β = β · u · n((β₁₁/β₀₀) t)` with `u` in the plane radical. Consequently the
translated flag evaluations `F_t(x) = c(x)(n(t) · q⁻¹)` of a plane source cocycle
are permuted by the flag stabilizer through `t ↦ (β₁₁/β₀₀) t`. This is the
equivariance of the averaging family in the `FlagExact` argument.

Original work (AxiomDeep, Claude Opus 5.5).
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.FlagExactness

theorem planeLevi_mul_borel (t : ℝ) (β : RationalGL3) (h00 : β.val 0 0 ≠ 0)
    (h10 : β.val 1 0 = 0) (h20 : β.val 2 0 = 0) (h21 : β.val 2 1 = 0) :
    planeLevi (binaryUnipotent ((t, 0) : Adeles)) 1 * rationalGroup β =
      rationalGroup β *
        (planeUnipotent (((t * ((β.val 1 2 / β.val 0 0 : ℚ) : ℝ)), 0) : Adeles) 0 *
          planeLevi (binaryUnipotent (((t * ((β.val 1 1 / β.val 0 0 : ℚ) : ℝ)), 0) : Adeles)) 1) := by
  have h00' : ((β.val 0 0 : ℚ) : ℝ) ≠ 0 := by exact_mod_cast h00
  apply adelic_ext
  · apply Units.ext
    ext i j
    simp only [realGroup, GeneralLinearGroup.coe_mul, map_mul]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, planeLevi, planeBlock, binaryUnipotent,
        planeUnipotent, rationalGroup, h10, h20, h21] <;>
      field_simp <;> ring
  · apply Units.ext
    ext i j
    simp only [finiteGroup, GeneralLinearGroup.coe_mul, map_mul]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, planeLevi, planeBlock, binaryUnipotent,
        planeUnipotent, rationalGroup, h10, h20, h21]

/-- Plane source cocycles absorb an upper-triangular rational factor behind a Levi
unipotent, rescaling the unipotent coordinate. -/
theorem source_borel_translate {degree : ℕ} (data : InducingData degree)
    (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (isSource : IsSourceCocycle data .plane source) (t : ℝ) (β : RationalGL3)
    (h00 : β.val 0 0 ≠ 0) (h10 : β.val 1 0 = 0) (h20 : β.val 2 0 = 0) (h21 : β.val 2 1 = 0)
    (vertices : Fin 3 → RealGL3) (g : AdelicGL) :
    source vertices (planeLevi (binaryUnipotent ((t, 0) : Adeles)) 1 * rationalGroup β * g) =
      source vertices
        (planeLevi (binaryUnipotent (((t * ((β.val 1 1 / β.val 0 0 : ℚ) : ℝ)), 0) : Adeles)) 1 * g) := by
  rw [planeLevi_mul_borel t β h00 h10 h20 h21, mul_assoc, mul_assoc]
  rw [TernaryPeriodPolynomials.GraphPieces.RationalComparison.source_parabolicInvariant data
    TernaryPeriodPolynomials.GraphPieces.RationalNorm.rational_norm .plane source isSource β
    ⟨h20, h21⟩]
  apply Subtype.ext
  apply MvPolynomial.ext
  intro monomial
  exact (isSource.1 vertices monomial).2.2.2.1 _ _ _


theorem atFinite_inv' (k : FiniteGL) : (atFinite k)⁻¹ = atFinite k⁻¹ := by
  apply adelic_ext
  · rw [map_inv]
    apply Units.ext
    change ((realGroup (atFinite k))⁻¹).val = (realGroup (atFinite k⁻¹)).val
    have h1 : realGroup (atFinite k) = 1 := by apply Units.ext; rfl
    have h2 : realGroup (atFinite k⁻¹) = 1 := by apply Units.ext; rfl
    rw [h1, h2, inv_one]
  · rw [map_inv]
    have h1 : finiteGroup (atFinite k) = k := by apply Units.ext; rfl
    have h2 : finiteGroup (atFinite k⁻¹) = k⁻¹ := by apply Units.ext; rfl
    rw [h1, h2]

/-- The translated flag evaluations are permuted by the flag stabilizer. -/
theorem translatedEvaluation_stabilizer {degree : ℕ} (data : InducingData degree)
    (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (isSource : IsSourceCocycle data .plane source) (q : RationalGL3) (γ : rationalLevel)
    (h00 : (q⁻¹ * γ.val * q).val 0 0 ≠ 0) (h10 : (q⁻¹ * γ.val * q).val 1 0 = 0)
    (h20 : (q⁻¹ * γ.val * q).val 2 0 = 0) (h21 : (q⁻¹ * γ.val * q).val 2 1 = 0)
    (t : ℝ) (vertices : Fin 3 → RealGL3) :
    source (fun index => GeneralLinearGroup.map (algebraMap ℚ ℝ) γ.val * vertices index)
        (planeLevi (binaryUnipotent ((t, 0) : Adeles)) 1 * rationalGroup q⁻¹) =
      realCoefficientComponent degree data.chi (GeneralLinearGroup.map (algebraMap ℚ ℝ) γ.val)
        (source vertices
          (planeLevi (binaryUnipotent
            (((t * (((q⁻¹ * γ.val * q).val 1 1 / (q⁻¹ * γ.val * q).val 0 0 : ℚ) : ℝ)), 0) : Adeles)) 1 *
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
  rw [hinf, ← mul_assoc, mul_assoc (planeLevi _ 1), hconj, ← mul_assoc]
  have hlevel : (rationalFinite γ.val)⁻¹ ∈ finiteLevel :=
    finiteLevel.inv_mem (TernaryPeriodPolynomials.GraphPieces.Comparison.rationalLevel_finiteLevel γ)
  rw [TernaryPeriodPolynomials.GraphPieces.Comparison.source_finiteInvariant data .plane source
    isSource ⟨_, hlevel⟩]
  exact source_borel_translate data source isSource t _ h00 h10 h20 h21 vertices _

end TernaryPeriodPolynomials.FlagExactness
