module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagExactness.FlagStabilizer

@[expose] public section


/-!
# Uniform averaging data at a rational flag

For a source cocycle `c` and a rational flag `q`, one positive integer `M`, depending
only on `q`, serves for all vertices and coefficients:

* the translated evaluations `F_t(x) = c(x)(n(t) · q⁻¹)` are `M`-periodic in `t`;
* every coefficient of `F_{M t}(x)` has vanishing integral over `t ∈ [0,1)`.

Here `n` is the real Levi unipotent: the plane one for plane sources and the line one
for line sources. With `translatedEvaluation_flagStabilizer`, this is the complete
equivariant constant-term input of the averaging argument for `FlagExact`.

Original work (AxiomDeep, Claude Opus 5.5).
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.EisensteinRegularization.Helpers

noncomputable section

namespace TernaryPeriodPolynomials.FlagExactness

theorem adele_shift_split (t : ℝ) (M : ℕ) :
    (((t + M : ℝ), (0 : FiniteAdeles)) : Adeles) =
      rationalAdele (M : ℚ) + ((t, (M : FiniteAdeles) * integralEmbedding (-1)) : Adeles) := by
  apply Prod.ext
  · change t + (M : ℝ) = ((M : ℚ) : ℝ) + t
    push_cast
    ring
  · change (0 : FiniteAdeles) = algebraMap ℚ FiniteAdeles (M : ℚ) + (M : FiniteAdeles) * integralEmbedding (-1)
    rw [map_neg, map_one, map_natCast]
    ring

/-- Uniform averaging data for plane source cocycles at a rational flag. -/
theorem flag_averaging_data {degree : ℕ} (data : InducingData degree)
    (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (isSource : IsSourceCocycle data .plane source) (q : RationalGL3) :
    ∃ M : ℕ, 0 < M ∧
      (∀ (t : ℝ) (vertices : Fin 3 → RealGL3),
        source vertices (planeLevi (binaryUnipotent (((t + M : ℝ), 0) : Adeles)) 1 * rationalGroup q⁻¹) =
          source vertices (planeLevi (binaryUnipotent ((t, 0) : Adeles)) 1 * rationalGroup q⁻¹)) ∧
      ∀ (vertices : Fin 3 → RealGL3) (monomial : Fin 3 →₀ ℕ),
        (∫ t in Set.Ico (0 : ℝ) 1, (source vertices (planeLevi (binaryUnipotent ((((M : ℝ) * t), 0) : Adeles)) 1 *
            rationalGroup q⁻¹)).val.coeff monomial) = 0 := by
  obtain ⟨M, hM, hlevel⟩ := scaled_unipotent_mem_finiteLevel (flagNilpotent q) (flagNilpotent_sq q)
  have finv : ∀ (vertices : Fin 3 → RealGL3) (t : ℝ) (z : IntegralAdeles),
      source vertices (planeLevi (binaryUnipotent ((t, (M : FiniteAdeles) * integralEmbedding z) : Adeles)) 1 *
        rationalGroup q⁻¹) =
      source vertices (planeLevi (binaryUnipotent ((t, 0) : Adeles)) 1 * rationalGroup q⁻¹) := by
    intro vertices t z'
    have hsplit : (((t, (M : FiniteAdeles) * integralEmbedding z') : Adeles)) =
        ((t, 0) : Adeles) + (((0 : ℝ), (M : FiniteAdeles) * integralEmbedding z') : Adeles) := by
      ext <;> simp
    have hsq : (((M : FiniteAdeles) * integralEmbedding z') •
        (flagNilpotent q).map (algebraMap ℚ FiniteAdeles)) *
        (((M : FiniteAdeles) * integralEmbedding z') •
          (flagNilpotent q).map (algebraMap ℚ FiniteAdeles)) = 0 := by
      rw [smul_mul_smul_comm, ← Matrix.map_mul, flagNilpotent_sq, Matrix.map_zero _ (map_zero _),
        smul_zero]
    rw [hsplit, binaryUnipotent_add, planeLevi_binary_mul, mul_assoc,
      planeLevi_finite_mul_rationalGroup q _ hsq, ← mul_assoc]
    exact TernaryPeriodPolynomials.GraphPieces.Comparison.source_finiteInvariant data .plane
      source isSource ⟨_, hlevel z' hsq⟩ vertices _
  refine ⟨M, hM, ?_, ?_⟩
  · intro t vertices
    rw [adele_shift_split]
    apply Subtype.ext
    apply MvPolynomial.ext
    intro monomial
    rw [induced_binary_unipotent_periodic (isSource.1 vertices monomial) (rationalGroup q⁻¹) (M : ℚ)]
    exact congrArg (fun value : HomogeneousPoly degree => value.val.coeff monomial)
      (finv vertices t (-1))
  · intro vertices monomial
    have induced := isSource.1 vertices monomial
    apply induced_binary_real_constant_term induced (rationalGroup q⁻¹) M hM
    · intro t z hz
      obtain ⟨z', rfl⟩ := hz
      exact congrArg (fun value : HomogeneousPoly degree => value.val.coeff monomial)
        (finv vertices t z')
    · exact ((induced_continuous induced).comp ((planeLeviUnipotent_continuous.comp
        (continuous_id.prodMk continuous_const)).mul continuous_const)).measurable

/-- Uniform averaging data for line source cocycles at a rational flag. -/
theorem line_flag_averaging_data {degree : ℕ} (data : InducingData degree)
    (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (isSource : IsSourceCocycle data .line source) (q : RationalGL3) :
    ∃ M : ℕ, 0 < M ∧
      (∀ (t : ℝ) (vertices : Fin 3 → RealGL3),
        source vertices (lineLevi 1 (binaryUnipotent (((t + M : ℝ), 0) : Adeles)) * rationalGroup q⁻¹) =
          source vertices (lineLevi 1 (binaryUnipotent ((t, 0) : Adeles)) * rationalGroup q⁻¹)) ∧
      ∀ (vertices : Fin 3 → RealGL3) (monomial : Fin 3 →₀ ℕ),
        (∫ t in Set.Ico (0 : ℝ) 1, (source vertices (lineLevi 1 (binaryUnipotent ((((M : ℝ) * t), 0) : Adeles)) *
            rationalGroup q⁻¹)).val.coeff monomial) = 0 := by
  obtain ⟨M, hM, hlevel⟩ := scaled_unipotent_mem_finiteLevel (lineFlagNilpotent q)
    (lineFlagNilpotent_sq q)
  have finv : ∀ (vertices : Fin 3 → RealGL3) (t : ℝ) (z : IntegralAdeles),
      source vertices (lineLevi 1 (binaryUnipotent ((t, (M : FiniteAdeles) * integralEmbedding z) : Adeles)) *
        rationalGroup q⁻¹) =
      source vertices (lineLevi 1 (binaryUnipotent ((t, 0) : Adeles)) * rationalGroup q⁻¹) := by
    intro vertices t z'
    have hsplit : (((t, (M : FiniteAdeles) * integralEmbedding z') : Adeles)) =
        ((t, 0) : Adeles) + (((0 : ℝ), (M : FiniteAdeles) * integralEmbedding z') : Adeles) := by
      ext <;> simp
    have hsq : (((M : FiniteAdeles) * integralEmbedding z') •
        (lineFlagNilpotent q).map (algebraMap ℚ FiniteAdeles)) *
        (((M : FiniteAdeles) * integralEmbedding z') •
          (lineFlagNilpotent q).map (algebraMap ℚ FiniteAdeles)) = 0 := by
      rw [smul_mul_smul_comm, ← Matrix.map_mul, lineFlagNilpotent_sq, Matrix.map_zero _ (map_zero _),
        smul_zero]
    rw [hsplit, binaryUnipotent_add, lineLevi_binary_mul, mul_assoc,
      lineLevi_finite_mul_rationalGroup q _ hsq, ← mul_assoc]
    exact TernaryPeriodPolynomials.GraphPieces.Comparison.source_finiteInvariant data .line
      source isSource ⟨_, hlevel z' hsq⟩ vertices _
  refine ⟨M, hM, ?_, ?_⟩
  · intro t vertices
    rw [adele_shift_split]
    apply Subtype.ext
    apply MvPolynomial.ext
    intro monomial
    rw [induced_line_unipotent_periodic (isSource.1 vertices monomial) (rationalGroup q⁻¹) (M : ℚ)]
    exact congrArg (fun value : HomogeneousPoly degree => value.val.coeff monomial)
      (finv vertices t (-1))
  · intro vertices monomial
    have induced := isSource.1 vertices monomial
    apply induced_line_real_constant_term induced (rationalGroup q⁻¹) M hM
    · intro t z hz
      obtain ⟨z', rfl⟩ := hz
      exact congrArg (fun value : HomogeneousPoly degree => value.val.coeff monomial)
        (finv vertices t z')
    · exact ((induced_continuous induced).comp ((lineLeviUnipotent_continuous.comp
        (continuous_id.prodMk continuous_const)).mul continuous_const)).measurable

end TernaryPeriodPolynomials.FlagExactness
