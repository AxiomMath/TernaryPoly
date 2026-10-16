module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagExactness.RadicalEquivariance
public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagExactness.BinaryRealConstantTerm
public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagExactness.UnipotentLevel
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.SectionContinuity

@[expose] public section


/-!
# Real constant terms of plane source cocycles at rational flags

Let `c` be a plane source cocycle and `q` a rational flag representative. For a
suitable `M > 0`, every coefficient of `c(x)(n(M t) · q⁻¹)` has vanishing integral
over `t ∈ [0,1)`. Here `n` is the unipotent of the `GL₂` Levi, with real coordinate
only. This is the constant-term input of the averaging argument for `FlagExact`.

Original work (AxiomDeep, Claude Opus 5.5).
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.FlagExactness

/-- The elementary matrix of the Levi unipotent. -/
def leviNilpotent (R : Type*) [CommRing R] : Matrix (Fin 3) (Fin 3) R := !![0, 1, 0; 0, 0, 0; 0, 0, 0]

theorem leviNilpotent_sq (R : Type*) [CommRing R] : leviNilpotent R * leviNilpotent R = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [leviNilpotent, Matrix.mul_apply, Fin.sum_univ_three]

theorem leviNilpotent_map :
    (leviNilpotent ℚ).map (algebraMap ℚ FiniteAdeles) = leviNilpotent FiniteAdeles := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [leviNilpotent]

theorem planeLevi_binaryUnipotent_val {R : Type*} [CommRing R] (w : R) :
    (planeLevi (binaryUnipotent w) 1).val = 1 + w • leviNilpotent R := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [planeLevi, planeBlock, binaryUnipotent, leviNilpotent]

/-- The conjugated nilpotent `q E q⁻¹`. -/
def flagNilpotent (q : RationalGL3) : Matrix (Fin 3) (Fin 3) ℚ :=
  q.val * leviNilpotent ℚ * (q⁻¹).val

theorem flagNilpotent_sq (q : RationalGL3) : flagNilpotent q * flagNilpotent q = 0 := by
  have hinv : (q⁻¹).val * q.val = 1 := by
    rw [← GeneralLinearGroup.coe_mul, inv_mul_cancel, GeneralLinearGroup.coe_one]
  unfold flagNilpotent
  calc q.val * leviNilpotent ℚ * (q⁻¹).val * (q.val * leviNilpotent ℚ * (q⁻¹).val)
      = q.val * leviNilpotent ℚ * ((q⁻¹).val * q.val) * leviNilpotent ℚ * (q⁻¹).val := by
        simp only [Matrix.mul_assoc]
    _ = 0 := by
        rw [hinv, Matrix.mul_one, Matrix.mul_assoc q.val, leviNilpotent_sq, Matrix.mul_zero,
          Matrix.zero_mul]

theorem planeLeviUnipotent_continuous :
    Continuous (fun a : Adeles => planeLevi (binaryUnipotent a) 1) := by
  apply Units.continuous_iff.mpr
  constructor <;> apply continuous_pi <;> intro row <;> apply continuous_pi <;> intro column <;>
    fin_cases row <;> fin_cases column <;>
    simp [planeLevi, planeBlock, binaryUnipotent] <;>
    first | fun_prop | exact ⟨by fun_prop, by fun_prop⟩

/-- The finite unipotent at a rational flag, conjugated to the right. -/
theorem planeLevi_finite_mul_rationalGroup (q : RationalGL3) (w : FiniteAdeles)
    (h : (w • (flagNilpotent q).map (algebraMap ℚ FiniteAdeles)) *
      (w • (flagNilpotent q).map (algebraMap ℚ FiniteAdeles)) = 0) :
    planeLevi (binaryUnipotent (((0 : ℝ), w) : Adeles)) 1 * rationalGroup q⁻¹ =
      rationalGroup q⁻¹ * atFinite (unipotentUnit _ h) := by
  apply adelic_ext
  · have hreal : realGroup (planeLevi (binaryUnipotent (((0 : ℝ), w) : Adeles)) 1) = 1 := by
      apply Units.ext
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [realGroup, planeLevi, planeBlock, binaryUnipotent, Matrix.GeneralLinearGroup.map_apply]
    have hfin : realGroup (atFinite (unipotentUnit _ h)) = 1 := by
      apply Units.ext
      rfl
    rw [realGroup.map_mul, realGroup.map_mul, hreal, hfin, one_mul, mul_one]
  · have hplane : finiteGroup (planeLevi (binaryUnipotent (((0 : ℝ), w) : Adeles)) 1) =
        planeLevi (binaryUnipotent w) 1 := by
      apply Units.ext
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [finiteGroup, planeLevi, planeBlock, binaryUnipotent, Matrix.GeneralLinearGroup.map_apply]
    have hfin : finiteGroup (atFinite (unipotentUnit _ h)) = unipotentUnit _ h := by
      apply Units.ext
      rfl
    rw [finiteGroup.map_mul, finiteGroup.map_mul, hplane, hfin, finiteGroup_rational]
    apply Units.ext
    rw [GeneralLinearGroup.coe_mul, GeneralLinearGroup.coe_mul, planeLevi_binaryUnipotent_val,
      unipotentUnit_val]
    have hqf : (rationalFinite q⁻¹).val * (rationalFinite q).val = 1 := by
      rw [← GeneralLinearGroup.coe_mul, ← map_mul, inv_mul_cancel, map_one,
        GeneralLinearGroup.coe_one]
    have hmap : (flagNilpotent q).map (algebraMap ℚ FiniteAdeles) =
        (rationalFinite q).val * leviNilpotent FiniteAdeles * (rationalFinite q⁻¹).val := by
      rw [flagNilpotent, Matrix.map_mul, Matrix.map_mul, leviNilpotent_map]
      rfl
    rw [hmap]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul]
    congr 1
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hqf, Matrix.one_mul]

/-- Vanishing of the real constant term of a plane source cocycle at a rational flag. -/
theorem flag_real_constant_term {degree : ℕ} (data : InducingData degree)
    (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (isSource : IsSourceCocycle data .plane source) (q : RationalGL3)
    (vertices : Fin 3 → RealGL3) (monomial : Fin 3 →₀ ℕ) :
    ∃ M : ℕ, 0 < M ∧
      (∫ t in Set.Ico (0 : ℝ) 1, (source vertices (planeLevi (binaryUnipotent ((((M : ℝ) * t), 0) : Adeles)) 1 *
          rationalGroup q⁻¹)).val.coeff monomial) = 0 := by
  obtain ⟨M, hM, hlevel⟩ := scaled_unipotent_mem_finiteLevel (flagNilpotent q) (flagNilpotent_sq q)
  refine ⟨M, hM, ?_⟩
  have induced := isSource.1 vertices monomial
  apply induced_binary_real_constant_term induced (rationalGroup q⁻¹) M hM
  · intro t z hz
    obtain ⟨z', rfl⟩ := hz
    have hsplit : (((t, (M : FiniteAdeles) * integralEmbedding z') : Adeles)) =
        ((t, 0) : Adeles) + (((0 : ℝ), (M : FiniteAdeles) * integralEmbedding z') : Adeles) := by
      ext <;> simp
    have hsq : (((M : FiniteAdeles) * integralEmbedding z') •
        (flagNilpotent q).map (algebraMap ℚ FiniteAdeles)) *
        (((M : FiniteAdeles) * integralEmbedding z') •
          (flagNilpotent q).map (algebraMap ℚ FiniteAdeles)) = 0 := by
      rw [smul_mul_smul_comm, ← Matrix.map_mul, flagNilpotent_sq, Matrix.map_zero _ (map_zero _),
        smul_zero]
    rw [hsplit, TernaryPeriodPolynomials.EisensteinRegularization.Helpers.binaryUnipotent_add,
      TernaryPeriodPolynomials.EisensteinRegularization.Helpers.planeLevi_binary_mul,
      mul_assoc, planeLevi_finite_mul_rationalGroup q _ hsq, ← mul_assoc]
    exact induced.2.1 ⟨_, hlevel z' hsq⟩ _
  · exact ((TernaryPeriodPolynomials.EisensteinRegularization.Helpers.induced_continuous
      induced).comp ((planeLeviUnipotent_continuous.comp
        (continuous_id.prodMk continuous_const)).mul continuous_const)).measurable

end TernaryPeriodPolynomials.FlagExactness
