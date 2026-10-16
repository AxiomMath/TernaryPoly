module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagExactness.PlaneTranslateInvariance
public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagExactness.LineUnipotentReduction
public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagExactness.LineFlagConstantTerm

@[expose] public section


/-!
# Stabilizer exactness for line source cocycles

The line-side analogue of `PlaneTranslateInvariance`, with the line Levi unipotent
`n'(r) = lineLevi 1 (binaryUnipotent r)`.

Original work (AxiomDeep, Claude Opus 5.5).
-/

open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.GraphPieces

noncomputable section

namespace TernaryPeriodPolynomials.FlagExactness

/-- The rational line Levi unipotent `n'(r)`. -/
def lineShift (r : ℚ) : RationalGL3 := lineLevi 1 (binaryUnipotent r)

theorem lineShift_unitri (r : ℚ) : IsUnitri (lineShift r) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [lineShift, lineLevi_val, binaryUnipotent]

theorem conj_lineShift_mem (q : RationalGL3) (r : ℚ) : q * lineShift r * q⁻¹ ∈ conjUnitri q := by
  rw [mem_conjUnitri]
  have : q⁻¹ * (q * lineShift r * q⁻¹) * q = lineShift r := by group
  rw [this]
  exact lineShift_unitri r

theorem map_lineShift (r : ℚ) :
    Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (lineShift r) =
      lineLevi 1 (binaryUnipotent (r : ℝ)) := by
  apply Units.ext
  ext i j
  rw [Matrix.GeneralLinearGroup.map_apply, lineShift, lineLevi_val, lineLevi_val]
  fin_cases i <;> fin_cases j <;> simp [binaryUnipotent]

theorem atInfinity_lineShift (s : ℝ) :
    atInfinity (lineLevi 1 (binaryUnipotent s)) =
      lineLevi 1 (binaryUnipotent ((s, (0 : FiniteAdeles)) : Adeles)) := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  change pairMatrix (lineLevi 1 (binaryUnipotent s)).val (1 : FiniteGL).val i j = _
  rw [lineLevi_val, lineLevi_val]
  apply Prod.ext <;> fin_cases i <;> fin_cases j <;> simp [pairMatrix, binaryUnipotent]

theorem lineLevi_translate_shift (q : RationalGL3) (r : ℚ) (t : ℝ) :
    lineLevi 1 (binaryUnipotent ((t, 0) : Adeles)) * rationalGroup q⁻¹ *
        atInfinity (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (q * lineShift r * q⁻¹)) =
      lineLevi 1 (binaryUnipotent (((t + r : ℝ), 0) : Adeles)) * rationalGroup q⁻¹ := by
  have e1 : rationalGroup q⁻¹ *
      atInfinity (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (q * lineShift r * q⁻¹)) =
      atInfinity (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (lineShift r)) * rationalGroup q⁻¹ := by
    rw [TernaryPeriodPolynomials.HeckeTranslate.HeckeInvariance.atInfinity_mul_rationalGroup]
    congr 2
    simp only [map_mul, map_inv, inv_inv]
  rw [mul_assoc, e1, ← mul_assoc, map_lineShift, atInfinity_lineShift, ← lineLevi_binary_mul,
    ← adelic_binaryUnipotent_add, Prod.mk_add_mk, add_zero]

/-- The real translate by `n'(r)` is absorbed into the vertices. -/
theorem lineTranslate_shift {degree : ℕ} (data : InducingData degree)
    (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (isSource : IsSourceCocycle data .line source) (q : RationalGL3) (r : ℚ) (t : ℝ)
    (x : Fin 3 → RationalGL3) :
    lineTranslate source q t (realVertices (fun i => (q * lineShift r * q⁻¹) * x i)) =
      rationalCoefficientComponent degree data.chi (q * lineShift r * q⁻¹)
        (lineTranslate source q (t + r) (realVertices x)) := by
  rw [lineTranslate, lineTranslate, realVertices_mul, isSource.2.2.1, lineLevi_translate_shift]
  rfl

theorem lineTranslate_periodic_int {degree : ℕ}
    (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree) (q : RationalGL3) (M : ℕ)
    (hper : ∀ (t : ℝ) (vertices : Fin 3 → RealGL3),
      source vertices (lineLevi 1 (binaryUnipotent (((t + M : ℝ), 0) : Adeles)) * rationalGroup q⁻¹) =
        source vertices (lineLevi 1 (binaryUnipotent ((t, 0) : Adeles)) * rationalGroup q⁻¹))
    (m : ℤ) (t : ℝ) (y : Fin 3 → RealGL3) :
    lineTranslate source q (t + m * M) y = lineTranslate source q t y := by
  have hper' : ∀ t : ℝ, lineTranslate source q (t + M) y = lineTranslate source q t y := fun t => hper t y
  induction m using Int.induction_on generalizing t with
  | zero => simp
  | succ m ih =>
    have e : t + ((((m : ℤ) + 1 : ℤ)) : ℝ) * M = (t + ((m : ℤ) : ℝ) * M) + M := by push_cast; ring
    rw [e, hper', ih]
  | pred m ih =>
    have e : t + (((-(m : ℤ) - 1 : ℤ)) : ℝ) * M + M = t + ((-(m : ℤ) : ℤ) : ℝ) * M := by
      push_cast; ring
    rw [← hper', e, ih]

/-- **Rational translate invariance on the unipotent stabilizer** (line sources). -/
theorem line_unipotentInvariance {degree : ℕ} (data : InducingData degree)
    (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (isSource : IsSourceCocycle data .line source) (q : RationalGL3) (r : ℚ) :
    ∃ primitive : cochains (unipotentStabilizer q) (rationalCoefficientComponent degree data.chi) 1,
      ∀ x, (differentialOne _ _ primitive).val x =
        (lineTranslateCochain data source isSource q r).val x -
          (lineTranslateCochain data source isSource q 0).val x := by
  obtain ⟨M, hM, hper, -⟩ := line_flag_averaging_data data source isSource q
  let C : ℤ → (Fin 3 → RationalGL3) → HomogeneousPoly degree :=
    fun k x => lineTranslate source q ((k : ℝ) * r) (realVertices x)
  have cocycle : ∀ k (x : Fin 4 → RationalGL3), C k ![x 1, x 2, x 3] - C k ![x 0, x 2, x 3] +
      C k ![x 0, x 1, x 3] - C k ![x 0, x 1, x 2] = 0 := by
    intro k x
    have hv : ∀ a b c : RationalGL3, realVertices ![a, b, c] =
        ![Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) a,
          Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) b,
          Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) c] := by
      intro a b c
      funext i
      fin_cases i <;> rfl
    simp only [C, lineTranslate, hv]
    exact isSource.2.2.2 (realVertices x) _
  have shift : ∀ k x, C k (fun i => (q * lineShift r * q⁻¹) * x i) =
      rationalCoefficientComponent degree data.chi (q * lineShift r * q⁻¹) (C (k + 1) x) := by
    intro k x
    simp only [C]
    rw [lineTranslate_shift data source isSource q r]
    congr 2
    push_cast
    ring
  have equiv : ∀ k, ∀ γ ∈ unipotentStabilizer q, ∀ x, C k (fun i => γ * x i) =
      rationalCoefficientComponent degree data.chi γ (C k x) := by
    intro k γ hγ x
    exact lineTranslate_unipotent_equivariant data source isSource q _ ⟨γ, hγ⟩ x
  have hK : 0 < r.den * M := Nat.mul_pos r.den_pos hM
  have period : ∀ x, C ((r.den * M : ℕ) : ℤ) x = C 0 x := by
    intro x
    simp only [C]
    have e : (((r.den * M : ℕ) : ℤ) : ℝ) * (r : ℝ) = 0 + (r.num : ℤ) * (M : ℝ) := by
      have hr : (r : ℝ) * (r.den : ℝ) = (r.num : ℝ) := by exact_mod_cast Rat.mul_den_eq_num r
      push_cast
      rw [zero_add, ← hr]
      ring
    rw [e, lineTranslate_periodic_int source q M hper]
    simp
  obtain ⟨P, hP⟩ := translation_family_primitive data.chi q (q * lineShift r * q⁻¹)
    (conj_lineShift_mem q r) (unipotentStabilizer q) (unipotentStabilizer_le_conjUnitri q) C
    cocycle shift equiv _ hK period
  refine ⟨P, fun x => ?_⟩
  rw [hP x]
  simp only [C, Int.cast_one, one_mul, Int.cast_zero, zero_mul]
  rfl

/-- **Stabilizer exactness for line source cocycles.** -/
theorem line_flagExact {degree : ℕ} (data : InducingData degree)
    (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (isSource : IsSourceCocycle data .line source) (q : RationalGL3) :
    EndpointReduction.FlagExact data source q :=
  line_flagExact_of_unipotentInvariance data source isSource q
    (line_unipotentInvariance data source isSource q)

end TernaryPeriodPolynomials.FlagExactness
