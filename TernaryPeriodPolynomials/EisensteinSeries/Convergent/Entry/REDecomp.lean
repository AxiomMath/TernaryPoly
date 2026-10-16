module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.REVector
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.REGL2
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Eigen.LineVectors

@[expose] public section


/-!
# R-e: The line decomposition with a lower triangular block

`finite_line_decomposition`: every `f ∈ GL₃(𝔸_f)` is `u(a,a') · lineLevi(d,B) · κ` with `B` lower triangular and `κ ∈ GL₃(Ẑ)`.

Formalized by Claude Sonnet 5.5.
-/


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Filter
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.HeckeEigen

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

theorem lineLevi_mul_right {R : Type*} [CommRing R] (d : Rˣ) (X Y : GeneralLinearGroup (Fin 2) R) :
    lineLevi d (X * Y) = lineLevi d X * lineLevi 1 Y := by
  have h := map_mul (lineLeviHom R) (d, X) (1, Y)
  simpa [lineLeviHom] using h

theorem lineLevi_one_mul {R : Type*} [CommRing R] (d : Rˣ) (X : GeneralLinearGroup (Fin 2) R) :
    lineLevi d 1 * lineLevi 1 X = lineLevi d X := by
  have h := map_mul (lineLeviHom R) (d, 1) (1, X)
  simpa [lineLeviHom] using h.symm

/-- Every finite adelic matrix is `u(a,a') · lineLevi d B · κ` with a lower triangular block `B` and an integral
`κ`. -/
theorem finite_line_decomposition (f : FiniteGL) :
    ∃ (a a' : FiniteAdeles) (d : FiniteAdelesˣ) (B : GeneralLinearGroup (Fin 2) FiniteAdeles)
      (κ : GeneralLinearGroup (Fin 3) IntegralAdeles),
      B.val 0 1 = 0 ∧ f = lineUnipotent a a' * lineLevi d B * GeneralLinearGroup.map integralEmbedding κ := by
  obtain ⟨q, hq, k, hk⟩ := finiteLine_factorization f
  obtain ⟨a, a', d, B, hB⟩ := lineParabolic_exists_decomposition q hq
  obtain ⟨k', hk'⟩ := gl2_column_reduction B
  let K : GeneralLinearGroup (Fin 2) IntegralAdeles := Matrix.SpecialLinearGroup.toGL k'
  let K2 : GeneralLinearGroup (Fin 2) FiniteAdeles := GeneralLinearGroup.map integralEmbedding K
  refine ⟨a, a', d, B * K2, lineLevi 1 K⁻¹ * k, ?_, ?_⟩
  · simpa [K2, K, GeneralLinearGroup.map_apply] using hk'
  · have h1 : GeneralLinearGroup.map integralEmbedding (lineLevi 1 K⁻¹) = lineLevi 1 K2⁻¹ := by
      rw [map_lineLevi, map_one, map_inv]
    have h2 : lineLevi 1 K2 * lineLevi 1 K2⁻¹ = 1 := by
      rw [← lineLevi_mul_right, mul_inv_cancel]
      exact (lineLeviHom FiniteAdeles).map_one
    have h3 : ∀ X : FiniteGL, lineLevi 1 K2 * (lineLevi 1 K2⁻¹ * X) = X := fun X => by
      rw [← mul_assoc, h2, one_mul]
    rw [hk, hB, map_mul, h1, lineLevi_mul_right, ← lineLevi_one_mul d B]
    simp only [mul_assoc, h3]

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
