module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.REBad1
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Finite.PlaneLevelFactorization
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.REDecomp
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.AdelicSplit

@[expose] public section


/-!
# R-e: Factorization in the good-line class

`finite_goodLine_lowerTriangular`: a finite matrix with `3`-component in `L(ℚ₃) g₀ K₁` is `u(a,a') · lineLevi(d,B) · g₀ · k` with `B` lower triangular and `k` in the finite level.

Formalized by Claude Sonnet 5.5.
-/


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Filter
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.HeckeEigen
open TernaryPeriodPolynomials.SourceConstruction

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

/-- A finite adelic matrix with integral three-component has a line Iwasawa decomposition whose line factor is
trivial at three and whose compact factor has the given three-component. -/
theorem finiteGL_line_integral_factorization (matrix : FiniteGL) (integer : GeneralLinearGroup (Fin 3) ℤ_[3])
    (integer_eq : GeneralLinearGroup.map padicThreeEmbedding integer = GeneralLinearGroup.map finiteThree matrix) :
    ∃ (parabolic : FiniteGL) (compact : FiniteGL), parabolic ∈ lineParabolic FiniteAdeles ∧
      GeneralLinearGroup.map finiteThree parabolic = 1 ∧ compact ∈ finiteIntegralGLLevel 3 ∧
      GeneralLinearGroup.map finiteThree compact = GeneralLinearGroup.map finiteThree matrix ∧
      matrix = parabolic * compact := by
  obtain ⟨parabolic, hpar, compact, factors⟩ := finiteGL_line_compact_factorization matrix
  let local_lift := integer * (GeneralLinearGroup.map integralThree compact)⁻¹
  have local_lift_eq : GeneralLinearGroup.map padicThreeEmbedding local_lift =
      GeneralLinearGroup.map finiteThree parabolic := by
    dsimp only [local_lift]
    rw [map_mul, map_inv, finiteThree_integralMatrix, integer_eq, factors, map_mul,
      mul_inv_cancel_right]
  let correction := finiteAtThree (GeneralLinearGroup.map finiteThree parabolic)
  have correction_integral : correction ∈ finiteIntegralGLLevel 3 := by
    change finiteAtThree (GeneralLinearGroup.map finiteThree parabolic) ∈ _
    rw [← local_lift_eq]
    exact finiteAtThree_integral local_lift
  have correction_line : correction ∈ lineParabolic FiniteAdeles :=
    finiteAtThree_line (generalLinearGroup_map_line finiteThree hpar)
  let new_compact := correction * GeneralLinearGroup.map integralEmbedding compact
  have compact_integral : new_compact ∈ finiteIntegralGLLevel 3 :=
    (finiteIntegralGLLevel 3).mul_mem correction_integral ⟨compact, rfl⟩
  have compact_three : GeneralLinearGroup.map finiteThree new_compact =
      GeneralLinearGroup.map finiteThree matrix := by
    dsimp only [new_compact, correction]
    rw [map_mul, finiteAtThree_three, ← map_mul, ← factors]
  refine ⟨parabolic * correction⁻¹, new_compact,
    (lineParabolic FiniteAdeles).mul_mem hpar ((lineParabolic FiniteAdeles).inv_mem correction_line),
    ?_, compact_integral, compact_three, ?_⟩
  · rw [map_mul, map_inv]
    dsimp only [correction]
    rw [finiteAtThree_three, mul_inv_cancel]
  · change matrix = (parabolic * correction⁻¹) *
      (correction * GeneralLinearGroup.map integralEmbedding compact)
    rw [mul_assoc, inv_mul_cancel_left]
    exact factors

theorem permMatrix_map_hom {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) :
    GeneralLinearGroup.map φ (permMatrix R) = permMatrix S := by
  apply Units.ext
  ext i j; fin_cases i <;> fin_cases j <;> simp [permMatrix, GeneralLinearGroup.map_apply]

theorem permMatrix_local : permMatrix ℚ_[3] = localGoodLine := by
  apply Units.ext
  ext i j; fin_cases i <;> fin_cases j <;> rfl

/-- A finite matrix whose three-component lies in `L(ℚ₃) g₀ K₁` is `q · g₀ · k` with `q` in the finite line
parabolic and `k` in the finite level. -/
theorem finite_goodLine_decomposition (f : FiniteGL) (hf : goodLineSet (GeneralLinearGroup.map finiteThree f)) :
    ∃ (q : FiniteGL) (k : FiniteGL), q ∈ lineParabolic FiniteAdeles ∧ k ∈ finiteLevel ∧
      f = q * permMatrix FiniteAdeles * k := by
  obtain ⟨p, k₀, hk₀, h3⟩ := hf
  have hQ : finiteAtThree p.val ∈ lineParabolic FiniteAdeles := finiteAtThree_line p.property
  have hQ3 : GeneralLinearGroup.map finiteThree (finiteAtThree p.val) = p.val := finiteAtThree_three _
  have hX3 : GeneralLinearGroup.map finiteThree ((finiteAtThree p.val)⁻¹ * f) = localGoodLine * k₀ := by
    rw [map_mul, map_inv, hQ3, h3]
    group
  have hk₀' := hk₀
  obtain ⟨kint, _, kint_eq⟩ := hk₀
  have g0 : GeneralLinearGroup.map PadicInt.Coe.ringHom (permMatrix ℤ_[3]) = localGoodLine := by
    rw [permMatrix_map_hom, permMatrix_local]
  have integer_eq : GeneralLinearGroup.map padicThreeEmbedding (permMatrix ℤ_[3] * kint) =
      GeneralLinearGroup.map finiteThree ((finiteAtThree p.val)⁻¹ * f) := by
    rw [hX3, map_mul]
    change GeneralLinearGroup.map PadicInt.Coe.ringHom (permMatrix ℤ_[3]) *
      GeneralLinearGroup.map PadicInt.Coe.ringHom kint = _
    rw [g0, kint_eq]
  obtain ⟨par, comp, hpar, hpar3, hcomp, hcomp3, hdec⟩ :=
    finiteGL_line_integral_factorization ((finiteAtThree p.val)⁻¹ * f) (permMatrix ℤ_[3] * kint) integer_eq
  have hg0 : permMatrix FiniteAdeles ∈ finiteIntegralGLLevel 3 :=
    ⟨permMatrix IntegralAdeles, permMatrix_map⟩
  have hg0_three : GeneralLinearGroup.map finiteThree (permMatrix FiniteAdeles) = localGoodLine := by
    rw [← permMatrix_local]
    have := permMatrix_map_hom (finiteThree)
    exact this
  have hk_integral : permMatrix FiniteAdeles * comp ∈ finiteIntegralGLLevel 3 :=
    (finiteIntegralGLLevel 3).mul_mem hg0 hcomp
  have hk_three : GeneralLinearGroup.map finiteThree (permMatrix FiniteAdeles * comp) = k₀ := by
    rw [map_mul, hg0_three, hcomp3, hX3, ← mul_assoc]
    have : localGoodLine * localGoodLine = 1 := by
      rw [← permMatrix_local, permMatrix_mul_self]
    rw [this, one_mul]
  have hk_level : permMatrix FiniteAdeles * comp ∈ finiteLevel :=
    finiteLevel_of_integral_of_three _ hk_integral (by rw [hk_three]; exact hk₀')
  refine ⟨finiteAtThree p.val * par, permMatrix FiniteAdeles * comp,
    (lineParabolic FiniteAdeles).mul_mem hQ hpar, hk_level, ?_⟩
  have square : permMatrix FiniteAdeles * (permMatrix FiniteAdeles * comp) = comp := by
    rw [← mul_assoc, permMatrix_mul_self, one_mul]
  calc f = finiteAtThree p.val * ((finiteAtThree p.val)⁻¹ * f) := by rw [mul_inv_cancel_left]
    _ = finiteAtThree p.val * (par * comp) := by rw [← hdec]
    _ = finiteAtThree p.val * par * permMatrix FiniteAdeles * (permMatrix FiniteAdeles * comp) := by
        rw [mul_assoc (finiteAtThree p.val * par), square, mul_assoc]

theorem conj_lineLevi_mem_finiteLevel (K : GeneralLinearGroup (Fin 2) IntegralAdeles) :
    GeneralLinearGroup.map integralEmbedding (permMatrix IntegralAdeles * lineLevi 1 K * permMatrix IntegralAdeles) ∈
      finiteLevel := by
  refine ⟨permMatrix IntegralAdeles * lineLevi 1 K * permMatrix IntegralAdeles, ?_, rfl⟩
  change lastRow ᵥ* (GeneralLinearGroup.map integralReduction
    (permMatrix IntegralAdeles * lineLevi 1 K * permMatrix IntegralAdeles)).val = lastRow
  funext j
  fin_cases j <;>
    simp [lastRow, Matrix.vecMul, dotProduct, Fin.sum_univ_three, permMatrix,
      lineLevi_val, Matrix.mul_apply]

/-- A finite matrix in the good-line class is `u(a,a') · lineLevi d B · g₀ · k` with `B` lower triangular and `k`
in the finite level. -/
theorem finite_goodLine_lowerTriangular (f : FiniteGL)
    (hf : goodLineSet (GeneralLinearGroup.map finiteThree f)) :
    ∃ (a a' : FiniteAdeles) (d : FiniteAdelesˣ) (B : GeneralLinearGroup (Fin 2) FiniteAdeles) (k : FiniteGL),
      B.val 0 1 = 0 ∧ k ∈ finiteLevel ∧
      f = lineUnipotent a a' * lineLevi d B * permMatrix FiniteAdeles * k := by
  obtain ⟨q, k₀, hq, hk₀, hdec⟩ := finite_goodLine_decomposition f hf
  obtain ⟨a, a', d, B, hB⟩ := lineParabolic_exists_decomposition q hq
  obtain ⟨k', hk'⟩ := gl2_column_reduction B
  let K : GeneralLinearGroup (Fin 2) IntegralAdeles := Matrix.SpecialLinearGroup.toGL k'
  let K2 : GeneralLinearGroup (Fin 2) FiniteAdeles := GeneralLinearGroup.map integralEmbedding K
  refine ⟨a, a', d, B * K2, (permMatrix FiniteAdeles * lineLevi 1 K2⁻¹ * permMatrix FiniteAdeles) * k₀,
    ?_, ?_, ?_⟩
  · simpa [K2, K, GeneralLinearGroup.map_apply] using hk'
  · refine finiteLevel.mul_mem ?_ hk₀
    have h := conj_lineLevi_mem_finiteLevel K⁻¹
    have e : GeneralLinearGroup.map integralEmbedding
        (permMatrix IntegralAdeles * lineLevi 1 K⁻¹ * permMatrix IntegralAdeles) =
        permMatrix FiniteAdeles * lineLevi 1 K2⁻¹ * permMatrix FiniteAdeles := by
      rw [map_mul, map_mul, permMatrix_map, map_lineLevi, map_one, map_inv]
    rwa [e] at h
  · have h1 : lineLevi d B = lineLevi d (B * K2) * lineLevi 1 K2⁻¹ := by
      rw [← lineLevi_mul_right, mul_inv_cancel_right]
    have square : permMatrix FiniteAdeles * permMatrix FiniteAdeles = 1 := permMatrix_mul_self _
    rw [hdec, hB, lineLevi_one_mul d B, h1]
    simp only [mul_assoc]
    rw [← mul_assoc (permMatrix FiniteAdeles) (permMatrix FiniteAdeles), square, one_mul]

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
