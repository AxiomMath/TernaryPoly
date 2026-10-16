module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagExactness.TranslationFamily
public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagExactness.UnipotentReduction
public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagExactness.AveragingData
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.CombineGL

@[expose] public section


/-!
# Stabilizer exactness for plane source cocycles

For a plane source cocycle and a complete flag `q`, the rationally translated flag
cochains `x ↦ c(x)(n(k r) q⁻¹)` (`k ∈ ℤ`) form a translation family for
`h = q n(r) q⁻¹`: the real translate by `n(r)` is absorbed into the vertices by the
equivariance of the source in its real variable. The family is periodic (level structure)
and equivariant for the unipotent stabilizer, so `TranslationFamily` shows that the
translate by `n(r)` does not change the stabilizer class. By
`flagExact_of_unipotentInvariance` this gives `FlagExact` at every complete flag.

Original work (AxiomDeep, Claude Opus 5.5).
-/

open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.GraphPieces

noncomputable section

namespace TernaryPeriodPolynomials.FlagExactness

/-- The rational plane Levi unipotent `n(r)`. -/
def planeShift (r : ℚ) : RationalGL3 := planeLevi (binaryUnipotent r) 1

theorem planeShift_unitri (r : ℚ) : IsUnitri (planeShift r) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [planeShift, planeLevi, planeBlock, binaryUnipotent]

theorem conj_planeShift_mem (q : RationalGL3) (r : ℚ) : q * planeShift r * q⁻¹ ∈ conjUnitri q := by
  rw [mem_conjUnitri]
  have : q⁻¹ * (q * planeShift r * q⁻¹) * q = planeShift r := by group
  rw [this]
  exact planeShift_unitri r

theorem unipotentStabilizer_le_conjUnitri (q : RationalGL3) : unipotentStabilizer q ≤ conjUnitri q := by
  intro γ hγ
  obtain ⟨hedge, hdiag⟩ := hγ
  obtain ⟨h10, h20, h21⟩ := borel_entries (edgeStabilizer_borel q hedge)
  exact ⟨hdiag 0, hdiag 1, hdiag 2, h10, h20, h21⟩

theorem adelic_binaryUnipotent_add (a b : Adeles) :
    binaryUnipotent (a + b) = binaryUnipotent a * binaryUnipotent b := by
  apply Units.ext
  apply Matrix.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    simp [binaryUnipotent, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem map_planeShift (r : ℚ) :
    Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (planeShift r) =
      planeLevi (binaryUnipotent (r : ℝ)) 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [planeShift, planeLevi, planeBlock, binaryUnipotent, Matrix.GeneralLinearGroup.map_apply]

theorem atInfinity_planeShift (s : ℝ) :
    atInfinity (planeLevi (binaryUnipotent s) 1) =
      planeLevi (binaryUnipotent ((s, (0 : FiniteAdeles)) : Adeles)) 1 := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  apply Prod.ext <;> fin_cases i <;> fin_cases j <;>
    simp [atInfinity, combineGL, pairMatrix, planeLevi, planeBlock, binaryUnipotent]

theorem planeLevi_translate_shift (q : RationalGL3) (r : ℚ) (t : ℝ) :
    planeLevi (binaryUnipotent ((t, 0) : Adeles)) 1 * rationalGroup q⁻¹ *
        atInfinity (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (q * planeShift r * q⁻¹)) =
      planeLevi (binaryUnipotent (((t + r : ℝ), 0) : Adeles)) 1 * rationalGroup q⁻¹ := by
  have e1 : rationalGroup q⁻¹ *
      atInfinity (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (q * planeShift r * q⁻¹)) =
      atInfinity (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (planeShift r)) * rationalGroup q⁻¹ := by
    rw [TernaryPeriodPolynomials.HeckeTranslate.HeckeInvariance.atInfinity_mul_rationalGroup]
    congr 2
    simp only [map_mul, map_inv, inv_inv]
  rw [mul_assoc, e1, ← mul_assoc, map_planeShift, atInfinity_planeShift]
  congr 1
  have e2 := (planeLeviHom Adeles).map_mul (binaryUnipotent ((t, 0) : Adeles), 1)
    (binaryUnipotent (((r : ℝ), 0) : Adeles), 1)
  change planeLevi _ 1 * planeLevi _ 1 = _
  change planeLevi (binaryUnipotent ((t, 0) : Adeles) * binaryUnipotent (((r : ℝ), 0) : Adeles)) (1 * 1) =
    planeLevi _ 1 * planeLevi _ 1 at e2
  rw [← e2, ← adelic_binaryUnipotent_add, mul_one, Prod.mk_add_mk, add_zero]

/-- The real translate by `n(r)` is absorbed into the vertices. -/
theorem planeTranslate_shift {degree : ℕ} (data : InducingData degree)
    (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (isSource : IsSourceCocycle data .plane source) (q : RationalGL3) (r : ℚ) (t : ℝ)
    (x : Fin 3 → RationalGL3) :
    planeTranslate source q t (realVertices (fun i => (q * planeShift r * q⁻¹) * x i)) =
      rationalCoefficientComponent degree data.chi (q * planeShift r * q⁻¹)
        (planeTranslate source q (t + r) (realVertices x)) := by
  rw [planeTranslate, planeTranslate, realVertices_mul, isSource.2.2.1, planeLevi_translate_shift]
  rfl

theorem planeTranslate_periodic_int {degree : ℕ}
    (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree) (q : RationalGL3) (M : ℕ)
    (hper : ∀ (t : ℝ) (vertices : Fin 3 → RealGL3),
      source vertices (planeLevi (binaryUnipotent (((t + M : ℝ), 0) : Adeles)) 1 * rationalGroup q⁻¹) =
        source vertices (planeLevi (binaryUnipotent ((t, 0) : Adeles)) 1 * rationalGroup q⁻¹))
    (m : ℤ) (t : ℝ) (y : Fin 3 → RealGL3) :
    planeTranslate source q (t + m * M) y = planeTranslate source q t y := by
  have hper' : ∀ t : ℝ, planeTranslate source q (t + M) y = planeTranslate source q t y := fun t => hper t y
  induction m using Int.induction_on generalizing t with
  | zero => simp
  | succ m ih =>
    have e : t + ((((m : ℤ) + 1 : ℤ)) : ℝ) * M = (t + ((m : ℤ) : ℝ) * M) + M := by push_cast; ring
    rw [e, hper', ih]
  | pred m ih =>
    have e : t + (((-(m : ℤ) - 1 : ℤ)) : ℝ) * M + M = t + ((-(m : ℤ) : ℤ) : ℝ) * M := by
      push_cast; ring
    rw [← hper', e, ih]

/-- **Rational translate invariance on the unipotent stabilizer** (plane sources). -/
theorem plane_unipotentInvariance {degree : ℕ} (data : InducingData degree)
    (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (isSource : IsSourceCocycle data .plane source) (q : RationalGL3) (r : ℚ) :
    ∃ primitive : cochains (unipotentStabilizer q) (rationalCoefficientComponent degree data.chi) 1,
      ∀ x, (differentialOne _ _ primitive).val x =
        (planeTranslateCochain data source isSource q r).val x -
          (planeTranslateCochain data source isSource q 0).val x := by
  obtain ⟨M, hM, hper, -⟩ := flag_averaging_data data source isSource q
  let C : ℤ → (Fin 3 → RationalGL3) → HomogeneousPoly degree :=
    fun k x => planeTranslate source q ((k : ℝ) * r) (realVertices x)
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
    simp only [C, planeTranslate, hv]
    exact isSource.2.2.2 (realVertices x) _
  have shift : ∀ k x, C k (fun i => (q * planeShift r * q⁻¹) * x i) =
      rationalCoefficientComponent degree data.chi (q * planeShift r * q⁻¹) (C (k + 1) x) := by
    intro k x
    simp only [C]
    rw [planeTranslate_shift data source isSource q r]
    congr 2
    push_cast
    ring
  have equiv : ∀ k, ∀ γ ∈ unipotentStabilizer q, ∀ x, C k (fun i => γ * x i) =
      rationalCoefficientComponent degree data.chi γ (C k x) := by
    intro k γ hγ x
    exact planeTranslate_unipotent_equivariant data source isSource q _ ⟨γ, hγ⟩ x
  have hK : 0 < r.den * M := Nat.mul_pos r.den_pos hM
  have period : ∀ x, C ((r.den * M : ℕ) : ℤ) x = C 0 x := by
    intro x
    simp only [C]
    have e : (((r.den * M : ℕ) : ℤ) : ℝ) * (r : ℝ) = 0 + (r.num : ℤ) * (M : ℝ) := by
      have hr : (r : ℝ) * (r.den : ℝ) = (r.num : ℝ) := by exact_mod_cast Rat.mul_den_eq_num r
      push_cast
      rw [zero_add, ← hr]
      ring
    rw [e, planeTranslate_periodic_int source q M hper]
    simp
  obtain ⟨P, hP⟩ := translation_family_primitive data.chi q (q * planeShift r * q⁻¹)
    (conj_planeShift_mem q r) (unipotentStabilizer q) (unipotentStabilizer_le_conjUnitri q) C
    cocycle shift equiv _ hK period
  refine ⟨P, fun x => ?_⟩
  rw [hP x]
  simp only [C, Int.cast_one, one_mul, Int.cast_zero, zero_mul]
  rfl

/-- **Stabilizer exactness for plane source cocycles.** -/
theorem plane_flagExact {degree : ℕ} (data : InducingData degree)
    (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (isSource : IsSourceCocycle data .plane source) (q : RationalGL3) :
    EndpointReduction.FlagExact data source q :=
  flagExact_of_unipotentInvariance data source isSource q
    (plane_unipotentInvariance data source isSource q)

end TernaryPeriodPolynomials.FlagExactness
