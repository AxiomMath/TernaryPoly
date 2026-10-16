module

public import TernaryPeriodPolynomials.ArithmeticCohomology.MultiplicityOne.DictionaryInjective
public import TernaryPeriodPolynomials.ArithmeticCohomology.MultiplicityOne.DictionaryTraceAL
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Real.Cuspidality
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Compact.Averaging

@[expose] public section


/-!
# A spherical vector and its Atkin–Lehner translate are linearly independent

Let `v ≠ 0` be a smooth vector of a cuspidal representation `σ` fixed by `GL₂(ℤ̂)`, and let
`W = [[0,-1],[3,0]]`.  The translate `v' = cuspFiniteRationalSlash σ W v = π(W_f⁻¹) v` is the
adelic counterpart of the oldform `f(3τ)` attached to the level-one form `f` of `v`.  We show that
`v` and `v'` are linearly independent.

Suppose `v' = c v`.  Put `F(h) = realize v (h_∞)` for `h ∈ GL₂(ℝ)`.  Left rationality turns
`v' = c v` into `F(W h) = c F(h)`, and sphericity gives `F(γ h) = F(h)` for `γ ∈ SL₂(ℤ)`.
With `A = [[0,1],[-1,0]] W = diag(3,1)` this reads `F(A h) = c F(h)`, and
`A u(x) = u(3x) A` for the unipotent `u(x)`.  Hence (for `c ≠ 0`) every period `3x` of
`r ↦ F(u(r) h)` gives the period `x`; starting from the integer periods, every triadic rational
`m / 3^k` is a period, and by continuity and density every real number is.  Then the constant term
`∫₀³ F(u(r) h) dr = 3 F(h)` vanishes by cuspidality (`RealCuspidality.integral_period_zero`), so
`F = 0`, contradicting `levelThree_realization_exists_real_nonzero`.  For `c = 0`, `F(W h) = 0`
already gives `F = 0`.

* `linearIndependent_atkinLehner`: `LinearIndependent ℂ ![v, cuspFiniteRationalSlash σ W v]`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace TernaryPeriodPolynomials.Oldform

open TernaryPeriodPolynomials.MultiplicityOne (atkinLehnerQ levelThreeValues
  cuspSphericalValues_le_levelThreeValues levelThree_realization_exists_real_nonzero)

/-! ## Triadic rationals are dense -/

/-- The triadic rationals `m / 3^k` are dense in `ℝ`. -/
theorem dense_triadic : Dense {x : ℝ | ∃ k : ℕ, ∃ m : ℤ, x = (m : ℝ) / 3 ^ k} := by
  rw [Metric.dense_iff]
  intro x ε hε
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 3 : ℝ) < 1)
  have h3 : (0 : ℝ) < 3 ^ k := by positivity
  have hfl := Int.floor_le (x * 3 ^ k)
  have hlt := Int.lt_floor_add_one (x * 3 ^ k)
  have key1 : (⌊x * 3 ^ k⌋ : ℝ) / 3 ^ k ≤ x := by
    rw [div_le_iff₀ h3]
    exact hfl
  have key2 : x - 1 / 3 ^ k < (⌊x * 3 ^ k⌋ : ℝ) / 3 ^ k := by
    rw [lt_div_iff₀ h3, sub_mul, one_div, inv_mul_cancel₀ h3.ne']
    linarith
  have hk' : 1 / (3 : ℝ) ^ k < ε := by rwa [_root_.one_div_pow] at hk
  refine ⟨(⌊x * 3 ^ k⌋ : ℝ) / 3 ^ k, ?_, k, ⌊x * 3 ^ k⌋, rfl⟩
  rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff]
  constructor <;> linarith

/-! ## Periods of a function on `GL₂(ℝ)` -/

/-- **Triadic periods.**  If `F(A h) = c F(h)` with `c ≠ 0`, `A u(x) = u(3x) A`, and every
integer is a left period of `F` along `u`, then so is every triadic rational. -/
theorem triadic_periods (F : GeneralLinearGroup (Fin 2) ℝ → ℂ) (A : GeneralLinearGroup (Fin 2) ℝ)
    (c : ℂ) (hc : c ≠ 0)
    (hint : ∀ (m : ℤ) (h : GeneralLinearGroup (Fin 2) ℝ), F (binaryUnipotent (m : ℝ) * h) = F h)
    (hA : ∀ h, F (A * h) = c * F h)
    (hcomm : ∀ x : ℝ, A * binaryUnipotent x = binaryUnipotent (3 * x) * A) :
    ∀ (k : ℕ) (m : ℤ) (h : GeneralLinearGroup (Fin 2) ℝ),
      F (binaryUnipotent ((m : ℝ) / 3 ^ k) * h) = F h := by
  intro k
  induction k with
  | zero =>
    intro m h
    simpa using hint m h
  | succ k ih =>
    intro m h
    have step := hA (binaryUnipotent ((m : ℝ) / 3 ^ (k + 1)) * h)
    have triple : 3 * ((m : ℝ) / 3 ^ (k + 1)) = (m : ℝ) / 3 ^ k := by
      rw [pow_succ]
      field_simp
    rw [← mul_assoc, hcomm, triple, mul_assoc, ih m (A * h), hA h] at step
    exact (mul_left_cancel₀ hc step).symm

/-- **Real periods.**  A function on `GL₂(ℝ)`, continuous along every orbit `r ↦ u(r) h`, with
every triadic rational as a left period along `u`, has every real number as a left period. -/
theorem real_periods (F : GeneralLinearGroup (Fin 2) ℝ → ℂ)
    (hcont : ∀ h, Continuous fun r : ℝ => F (binaryUnipotent r * h))
    (htri : ∀ (k : ℕ) (m : ℤ) (h : GeneralLinearGroup (Fin 2) ℝ),
      F (binaryUnipotent ((m : ℝ) / 3 ^ k) * h) = F h)
    (r : ℝ) (h : GeneralLinearGroup (Fin 2) ℝ) : F (binaryUnipotent r * h) = F h := by
  have hext := Continuous.ext_on dense_triadic (hcont h) continuous_const
    (fun x hx => by
      obtain ⟨k, m, rfl⟩ := hx
      exact htri k m h)
  exact congrFun hext r

/-! ## The scalar function of a spherical vector on `GL₂(ℝ)` -/

section Spherical

variable (σ : CuspidalRepresentation) (v : σ.smooth)

/-- The finite image of an element of `SL₂(ℤ)` is integral. -/
theorem map_mapGL_rat_eq (δ : SpecialLinearGroup (Fin 2) ℤ) :
    GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) (SpecialLinearGroup.mapGL ℚ δ) =
      GeneralLinearGroup.map integralEmbedding (SpecialLinearGroup.mapGL IntegralAdeles δ) := by
  apply Units.ext
  funext row column
  simp only [GeneralLinearGroup.map_apply, SpecialLinearGroup.mapGL_coe_matrix,
    SpecialLinearGroup.map_apply_coe]
  change algebraMap ℚ FiniteAdeles (algebraMap ℤ ℚ (δ.val row column)) =
    integralEmbedding (algebraMap ℤ IntegralAdeles (δ.val row column))
  simp

/-- The finite rational slash by an element of `SL₂(ℤ)` fixes a spherical vector. -/
theorem slash_specialLinear_spherical (hsph : v.val ∈ cuspSphericalValues σ)
    (γ : SpecialLinearGroup (Fin 2) ℤ) :
    cuspFiniteRationalSlash σ (SpecialLinearGroup.mapGL ℚ γ) v = v := by
  apply Subtype.ext
  change σ.π (atFinite (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles)
    (SpecialLinearGroup.mapGL ℚ γ)⁻¹)) v.val = v.val
  rw [← map_inv (SpecialLinearGroup.mapGL ℚ) γ, map_mapGL_rat_eq]
  exact hsph _

/-- The scalar function of a spherical vector is left invariant under `SL₂(ℤ)`. -/
theorem realize_specialLinear (hsph : v.val ∈ cuspSphericalValues σ)
    (γ : SpecialLinearGroup (Fin 2) ℤ) (h : GeneralLinearGroup (Fin 2) ℝ) :
    σ.realize v (atInfinity (SpecialLinearGroup.mapGL ℝ γ * h)) = σ.realize v (atInfinity h) := by
  have key := cuspFiniteRationalSlash_realize σ (SpecialLinearGroup.mapGL ℚ γ) v h
  rw [slash_specialLinear_spherical σ v hsph γ, binaryIntegral_specialLinear_real] at key
  exact key.symm

/-- An eigenvalue relation for the Atkin–Lehner slash is a functional equation for the scalar
function. -/
theorem realize_atkinLehner (c : ℂ) (hc : cuspFiniteRationalSlash σ atkinLehnerQ v = c • v)
    (h : GeneralLinearGroup (Fin 2) ℝ) :
    σ.realize v (atInfinity (GeneralLinearGroup.map (algebraMap ℚ ℝ) atkinLehnerQ * h)) =
      c * σ.realize v (atInfinity h) := by
  have key := cuspFiniteRationalSlash_realize σ atkinLehnerQ v h
  rw [hc, map_smul, Pi.smul_apply, smul_eq_mul] at key
  exact key.symm

/-- The matrix `[[0,1],[-1,0]]` of `SL₂(ℤ)`. -/
def flipZ : SpecialLinearGroup (Fin 2) ℤ :=
  ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩

/-- `A = [[0,1],[-1,0]] · W = diag(3, 1)` satisfies `A u(x) = u(3x) A`. -/
theorem flip_atkinLehner_unipotent (x : ℝ) :
    SpecialLinearGroup.mapGL ℝ flipZ * GeneralLinearGroup.map (algebraMap ℚ ℝ) atkinLehnerQ *
        binaryUnipotent x =
      binaryUnipotent (3 * x) *
        (SpecialLinearGroup.mapGL ℝ flipZ * GeneralLinearGroup.map (algebraMap ℚ ℝ) atkinLehnerQ) := by
  have e : ∀ i j, ((SpecialLinearGroup.mapGL ℝ flipZ : GeneralLinearGroup (Fin 2) ℝ).val i j) =
      ((flipZ.val i j : ℤ) : ℝ) :=
    TernaryPeriodPolynomials.EisensteinRegularization.Helpers.binaryIntegral_mapGL_entry
      ℝ flipZ
  apply Units.ext
  ext row column
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, e]
  fin_cases row <;> fin_cases column <;>
    simp [flipZ, atkinLehnerQ, binaryUnipotent, GeneralLinearGroup.map_apply]

/-- The finite congruence level fixes a spherical vector. -/
theorem spherical_mem_fixedSubspace (hsph : v.val ∈ cuspSphericalValues σ) :
    v.val ∈ PlaneEisensteinContinuation.BinaryLevel.fixedSubspace σ
      PlaneEisensteinContinuation.BinaryLevel.finiteCongruence := by
  intro element
  obtain ⟨k, -, hk⟩ := Subgroup.mem_map.mp element.property
  rw [← hk]
  exact hsph k

/-- The real orbit function at the identity finite point. -/
theorem realFunction_one (h : GeneralLinearGroup (Fin 2) ℝ) (r : ℝ) :
    PlaneEisensteinContinuation.UnipotentPeriodicity.realFunction σ v 1 h r =
      σ.realize v (atInfinity (binaryUnipotent r * h)) := by
  unfold PlaneEisensteinContinuation.UnipotentPeriodicity.realFunction
  rw [map_one, PlaneEisensteinContinuation.CompactAveraging.atFinite_one, one_mul]

/-- **Cuspidality.**  If every real number is a left period of the scalar function of a spherical
vector along `u` at `h`, the scalar function vanishes at `h`. -/
theorem realize_eq_zero_of_periods (hsph : v.val ∈ cuspSphericalValues σ)
    (h : GeneralLinearGroup (Fin 2) ℝ)
    (hper : ∀ r : ℝ, σ.realize v (atInfinity (binaryUnipotent r * h)) =
      σ.realize v (atInfinity h)) :
    σ.realize v (atInfinity h) = 0 := by
  have hint := PlaneEisensteinContinuation.RealCuspidality.integral_period_zero σ v
    (spherical_mem_fixedSubspace σ v hsph) 1 h 0
  have hcongr : (∫ r in (0 : ℝ)..0 + 3, σ.realize v (atInfinity h)) =
      ∫ r in (0 : ℝ)..0 + 3,
        PlaneEisensteinContinuation.UnipotentPeriodicity.realFunction σ v 1 h r := by
    apply intervalIntegral.integral_congr
    intro r _
    show σ.realize v (atInfinity h) =
      PlaneEisensteinContinuation.UnipotentPeriodicity.realFunction σ v 1 h r
    rw [realFunction_one]
    exact (hper r).symm
  rw [hint, intervalIntegral.integral_const] at hcongr
  rcases smul_eq_zero.mp hcongr with h3 | hF
  · norm_num at h3
  · exact hF

/-- **No Atkin–Lehner eigenvector.**  A nonzero spherical vector is not an eigenvector of the
Atkin–Lehner slash. -/
theorem slash_atkinLehner_ne_smul (hv : v ≠ 0) (hsph : v.val ∈ cuspSphericalValues σ) (c : ℂ) :
    cuspFiniteRationalSlash σ atkinLehnerQ v ≠ c • v := by
  intro hc
  obtain ⟨real, hreal⟩ := levelThree_realization_exists_real_nonzero σ v
    (cuspSphericalValues_le_levelThreeValues σ hsph) hv
  apply hreal
  have hW := realize_atkinLehner σ v c hc
  by_cases hc0 : c = 0
  · have key := hW ((GeneralLinearGroup.map (algebraMap ℚ ℝ) atkinLehnerQ)⁻¹ * real)
    rw [← mul_assoc, mul_inv_cancel, one_mul, hc0, zero_mul] at key
    exact key
  · set F : GeneralLinearGroup (Fin 2) ℝ → ℂ := fun h => σ.realize v (atInfinity h)
    set A := SpecialLinearGroup.mapGL ℝ flipZ *
      GeneralLinearGroup.map (algebraMap ℚ ℝ) atkinLehnerQ with hAdef
    have hA : ∀ h, F (A * h) = c * F h := by
      intro h
      change σ.realize v (atInfinity (A * h)) = c * σ.realize v (atInfinity h)
      rw [hAdef, mul_assoc, realize_specialLinear σ v hsph flipZ, hW]
    have hint : ∀ (m : ℤ) (h : GeneralLinearGroup (Fin 2) ℝ),
        F (binaryUnipotent (m : ℝ) * h) = F h := by
      intro m h
      change σ.realize v (atInfinity (binaryUnipotent (m : ℝ) * h)) = σ.realize v (atInfinity h)
      rw [← PlaneEisensteinContinuation.UnipotentPeriodicity.integerUnipotent_map]
      exact realize_specialLinear σ v hsph _ h
    have hcont : ∀ h, Continuous fun r : ℝ => F (binaryUnipotent r * h) := by
      intro h
      have hc' := PlaneEisensteinContinuation.UnipotentPeriodicity.realFunction_continuous σ v 1 h
      have heq : PlaneEisensteinContinuation.UnipotentPeriodicity.realFunction σ v 1 h =
          fun r : ℝ => F (binaryUnipotent r * h) := by
        funext r
        exact realFunction_one σ v h r
      rw [heq] at hc'
      exact hc'
    have htri := triadic_periods F A c hc0 hint hA (flip_atkinLehner_unipotent)
    exact realize_eq_zero_of_periods σ v hsph real (fun r => real_periods F hcont htri r real)

/-- **The oldform pair is linearly independent.**  A nonzero spherical vector and its
Atkin–Lehner translate are linearly independent. -/
theorem linearIndependent_atkinLehner (hv : v ≠ 0) (hsph : v.val ∈ cuspSphericalValues σ) :
    LinearIndependent ℂ ![v, cuspFiniteRationalSlash σ atkinLehnerQ v] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  by_cases ht : t = 0
  · subst ht
    rw [zero_smul, add_zero] at hst
    exact ⟨(smul_eq_zero.mp hst).resolve_right hv, rfl⟩
  · exfalso
    apply slash_atkinLehner_ne_smul σ v hv hsph (-s / t)
    have hneg : t • cuspFiniteRationalSlash σ atkinLehnerQ v = -(s • v) := by
      rw [eq_neg_iff_add_eq_zero, add_comm]
      exact hst
    calc cuspFiniteRationalSlash σ atkinLehnerQ v
        = t⁻¹ • (t • cuspFiniteRationalSlash σ atkinLehnerQ v) := by
          rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
      _ = (-s / t) • v := by
          rw [hneg, smul_neg, smul_smul, ← neg_smul, div_eq_inv_mul, mul_neg]

end Spherical

end TernaryPeriodPolynomials.Oldform
