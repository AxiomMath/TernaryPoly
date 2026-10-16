module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.CupSeed
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.RadicalAnalytic
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Plane.SourceData
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Edge.DerivativeExplicitTransport

@[expose] public section


/-!
# The Iwasawa factor and the plane chart

For `y ∈ GL₃(ℝ)` with Iwasawa factor `b = iwasawaB y` (upper triangular with positive diagonal, `b bᵀ = y yᵀ`), the
plane coordinates of the Gram matrix `y yᵀ` are read off `b`: `u(y yᵀ) = (b₀₂/b₂₂, b₁₂/b₂₂)` and
`τ(y yᵀ) = (b₀₀ i + b₀₁)/b₁₁ = basePoint (iwA y)` (`gramPlaneU_iwasawa`, `basePoint_iwA`).  Hence the coefficients of
`planeRadical n χ (iwP y)` are `radicalCoeff` at `gramPlaneU (y yᵀ)` (`coeff_planeRadical_iwP`), and the Gram matrix
lies in the chart domain (`gram_mem_gramDomain`).

Formalized by Claude Sonnet 5.5.
-/

open scoped Matrix.Norms.Elementwise
open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.Statements.RealEntrySeed
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.AnalyticClasses TernaryPeriodPolynomials.AnalyticClasses.EdgeExplicit

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

local notation "Mat3" => Matrix (Fin 3) (Fin 3) ℝ

theorem iwasawaB_gram (y : RealGL3) :
    (iwasawaB y).val * (iwasawaB y).val.transpose = y.val * y.val.transpose := by
  have hy := det_ne_zero_realGL3 y
  rw [iwasawaB_val, iwasawaBMatrix_eq_mul_transpose _ hy, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.mul_assoc, ← Matrix.mul_assoc _ (iwasawaKMatrix y.val), iwasawaKMatrix_transpose_mul _ hy,
    Matrix.one_mul]

section Upper

variable (B : Mat3) (h10 : B 1 0 = 0) (h20 : B 2 0 = 0) (h21 : B 2 1 = 0)

include h10 h20 h21

theorem gram_upper_entries :
    (B * B.transpose) 2 2 = B 2 2 ^ 2 ∧ (B * B.transpose) 0 2 = B 0 2 * B 2 2 ∧
      (B * B.transpose) 1 2 = B 1 2 * B 2 2 ∧ (B * B.transpose) 0 0 = B 0 0 ^ 2 + B 0 1 ^ 2 + B 0 2 ^ 2 ∧
      (B * B.transpose) 0 1 = B 0 1 * B 1 1 + B 0 2 * B 1 2 ∧ (B * B.transpose) 1 1 = B 1 1 ^ 2 + B 1 2 ^ 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, h10, h20, h21, sq]

theorem gramPlaneU_upper (h22 : B 2 2 ≠ 0) :
    gramPlaneU (B * B.transpose) = (B 0 2 / B 2 2, B 1 2 / B 2 2) := by
  obtain ⟨e22, e02, e12, -, -, -⟩ := gram_upper_entries B h10 h20 h21
  simp only [gramPlaneU, e22, e02, e12]
  ext
  · simp only; field_simp
  · simp only; field_simp

theorem gramSchur_upper (h22 : B 2 2 ≠ 0) :
    gramSchur (B * B.transpose) = !![B 0 0 ^ 2 + B 0 1 ^ 2, B 0 1 * B 1 1; B 0 1 * B 1 1, B 1 1 ^ 2] := by
  have e10 : (B * B.transpose) 1 0 = B 0 1 * B 1 1 + B 0 2 * B 1 2 := by
    simp [Matrix.mul_apply, Fin.sum_univ_three, h10]; ring
  obtain ⟨e22, e02, e12, e00, e01, e11⟩ := gram_upper_entries B h10 h20 h21
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [gramSchur, Fin.zero_eta, Fin.mk_one, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val', e22, e02, e12, e00, e01, e11, e10] <;>
    field_simp <;> ring

theorem gramPlaneTau_upper (h22 : B 2 2 ≠ 0) (h00 : 0 < B 0 0) (h11 : 0 < B 1 1) :
    gramPlaneTau (B * B.transpose) =
      ((B 0 1 / B 1 1 : ℝ) : ℂ) + Complex.I * ((B 0 0 / B 1 1 : ℝ) : ℂ) := by
  have hS := gramSchur_upper B h10 h20 h21 h22
  have hdet : (gramSchur (B * B.transpose)).det = (B 0 0 * B 1 1) ^ 2 := by
    rw [hS, Matrix.det_fin_two]
    simp
    ring
  unfold gramPlaneTau
  rw [hdet, Real.sqrt_sq (by positivity), hS]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  have h11' : B 1 1 ≠ 0 := h11.ne'
  have e1 : B 0 1 * B 1 1 / B 1 1 ^ 2 = B 0 1 / B 1 1 := by field_simp
  have e2 : B 0 0 * B 1 1 / B 1 1 ^ 2 = B 0 0 / B 1 1 := by field_simp
  rw [e1, e2]

end Upper

theorem iwasawaB_zero_entries (y : RealGL3) :
    (iwasawaB y).val 1 0 = 0 ∧ (iwasawaB y).val 2 0 = 0 ∧ (iwasawaB y).val 2 1 = 0 :=
  ⟨(iwasawaB_upper y).1, (iwasawaB_upper y).2.1, (iwasawaB_upper y).2.2.1⟩

theorem gramPlaneU_iwasawa (y : RealGL3) :
    gramPlaneU (y.val * y.val.transpose) = ((iwasawaB y).val 0 2 / (iwasawaB y).val 2 2,
      (iwasawaB y).val 1 2 / (iwasawaB y).val 2 2) := by
  obtain ⟨h10, h20, h21⟩ := iwasawaB_zero_entries y
  rw [← iwasawaB_gram]
  exact gramPlaneU_upper _ h10 h20 h21 (iwasawaB_upper y).2.2.2.2.2.ne'

theorem basePoint_iwA (y : RealGL3) :
    basePoint (iwA y) = gramPlaneTau (y.val * y.val.transpose) := by
  obtain ⟨h10, h20, h21⟩ := iwasawaB_zero_entries y
  obtain ⟨-, -, -, p00, p11, p22⟩ := iwasawaB_upper y
  rw [← iwasawaB_gram, gramPlaneTau_upper _ h10 h20 h21 p22.ne' p00 p11]
  have hdet : 0 < (iwA y).val.det := by
    rw [Matrix.det_fin_two, iwA_val, iwA_val, iwA_val, iwA_val]
    simp only [Fin.castSucc_zero, Fin.castSucc_one]
    rw [h10]
    nlinarith
  unfold basePoint
  rw [coe_smul_I_of_upper hdet (by rw [iwA_val]; simpa using h10)]
  simp only [iwA_val, Fin.castSucc_zero, Fin.castSucc_one]
  push_cast
  ring

theorem gram_mem_gramDomain (g : Mat3) (hg : g.det ≠ 0) : g * g.transpose ∈ gramDomain :=
  ⟨gram_pos_22 g hg, gramSchur_pos_11 g hg, gramSchur_det_pos g hg⟩

theorem coeff_planeRadical_iwP (n : ℕ) (χ : RankOneCharacter) (y : RealGL3)
    (Q : Binary.HomogeneousPoly (n + 1)) (m : Fin 3 →₀ ℕ) :
    (planeRadical n χ (iwP y) Q : Poly).coeff m =
      radicalCoeff n Q m (gramPlaneU (y.val * y.val.transpose)) := by
  rw [coeff_planeRadical_eq, gramPlaneU_iwasawa]
  rfl

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
