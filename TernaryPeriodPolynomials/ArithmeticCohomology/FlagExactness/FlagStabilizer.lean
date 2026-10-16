module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagExactness.StabilizerBorel
public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagExactness.LineBorelTranslate

@[expose] public section


/-!
# The flag stabilizer acts on the averaging families by signs

For `γ` in the arithmetic level fixing the complete flag `q B`, the translated flag
evaluations `F_t(x) = c(x)(n(t) · q⁻¹)` of a plane source cocycle satisfy
`F_t(γ x) = ρ(γ) F_{ε t}(x)` with `ε = ±1`. The same holds for line source cocycles
and the line Levi unipotent. The only hypothesis is the stabilizer condition that
appears in `FlagExact`.

Original work (AxiomDeep, Claude Opus 5.5).
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.FlagExactness

theorem ratio_sign {a b : ℚ} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    b / a = 1 ∨ b / a = -1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> norm_num

theorem diag_ne_zero {a : ℚ} (ha : a = 1 ∨ a = -1) : a ≠ 0 := by
  rcases ha with rfl | rfl <;> norm_num

/-- Plane averaging family: the flag stabilizer acts through `t ↦ ±t`. -/
theorem translatedEvaluation_flagStabilizer {degree : ℕ} (data : InducingData degree)
    (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (isSource : IsSourceCocycle data .plane source) (q : RationalGL3) (γ : rationalLevel)
    (h : γ.val • (QuotientGroup.mk q : Edges) = QuotientGroup.mk q) :
    ∃ ε : ℚ, (ε = 1 ∨ ε = -1) ∧ ∀ (t : ℝ) (vertices : Fin 3 → RealGL3),
      source (fun index => GeneralLinearGroup.map (algebraMap ℚ ℝ) γ.val * vertices index)
          (planeLevi (binaryUnipotent ((t, 0) : Adeles)) 1 * rationalGroup q⁻¹) =
        realCoefficientComponent degree data.chi (GeneralLinearGroup.map (algebraMap ℚ ℝ) γ.val)
          (source vertices
            (planeLevi (binaryUnipotent (((t * (ε : ℝ)), 0) : Adeles)) 1 * rationalGroup q⁻¹)) := by
  obtain ⟨h10, h20, h21⟩ := borel_entries (stabilizer_mem_borel q γ.val h)
  have s0 := stabilizer_diag_sign q γ h 0
  have s1 := stabilizer_diag_sign q γ h 1
  refine ⟨_, ratio_sign s0 s1, fun t vertices => ?_⟩
  exact translatedEvaluation_stabilizer data source isSource q γ (diag_ne_zero s0) h10 h20 h21 t
    vertices

/-- Line averaging family: the flag stabilizer acts through `t ↦ ±t`. -/
theorem lineTranslatedEvaluation_flagStabilizer {degree : ℕ} (data : InducingData degree)
    (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (isSource : IsSourceCocycle data .line source) (q : RationalGL3) (γ : rationalLevel)
    (h : γ.val • (QuotientGroup.mk q : Edges) = QuotientGroup.mk q) :
    ∃ ε : ℚ, (ε = 1 ∨ ε = -1) ∧ ∀ (t : ℝ) (vertices : Fin 3 → RealGL3),
      source (fun index => GeneralLinearGroup.map (algebraMap ℚ ℝ) γ.val * vertices index)
          (lineLevi 1 (binaryUnipotent ((t, 0) : Adeles)) * rationalGroup q⁻¹) =
        realCoefficientComponent degree data.chi (GeneralLinearGroup.map (algebraMap ℚ ℝ) γ.val)
          (source vertices
            (lineLevi 1 (binaryUnipotent (((t * (ε : ℝ)), 0) : Adeles)) * rationalGroup q⁻¹)) := by
  obtain ⟨h10, h20, h21⟩ := borel_entries (stabilizer_mem_borel q γ.val h)
  have s0 := stabilizer_diag_sign q γ h 0
  have s1 := stabilizer_diag_sign q γ h 1
  have s2 := stabilizer_diag_sign q γ h 2
  refine ⟨_, ratio_sign s1 s2, fun t vertices => ?_⟩
  exact lineTranslatedEvaluation_stabilizer data source isSource q γ (diag_ne_zero s0)
    (diag_ne_zero s1) h10 h20 h21 t vertices

end TernaryPeriodPolynomials.FlagExactness
