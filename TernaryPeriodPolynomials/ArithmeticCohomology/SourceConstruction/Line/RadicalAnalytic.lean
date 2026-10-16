module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Line.RadicalCocycle
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.RadicalAnalytic

@[expose] public section


/-!
# Real analyticity of the line radical along the Iwasawa factor

* every coefficient of `lineRadical n χ p Q` is an `ℂ`-linear combination, with constant
  coefficients depending on `Q` and the monomial only, of the two radical coordinates
  `lrC0 p`, `lrC1 p` (`coeff_lineRadical`);
* the radical coordinates of the Iwasawa factor `iwasawaB (invertibleMatrix A)` are real analytic
  (indeed rational with nonvanishing denominator) functions of `A ∈ GL₃(ℝ)`
  (`lrC0_iwasawaB_contDiffOn`);
* hence `A ↦ coeff m (lineRadical n χ ⟨iwasawaB (invertibleMatrix A), _⟩ Q)` is real analytic on
  the invertible matrices (`lineRadical_iwasawaB_contDiffOn`).

The matrix coefficients of the coefficient representation along the Iwasawa decomposition are
`realCoefficientComponent_inv_contDiffOn` of `RadicalAnalytic.lean`, which does not depend on the
parabolic.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open MvPolynomial Matrix GeneralEisenstein
open GeneralEisenstein.Adelic (lineParabolic invertibleMatrix)
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.SourceConstruction

local notation "Mat3" => Matrix (Fin 3) (Fin 3) ℝ

/-! ## Coefficients of the radical -/

/-- The coefficient of `x^m` in the radical is `lrC0(p) K₀ + lrC1(p) K₁` for constants `K₀`, `K₁`
depending only on `Q` and `m`. -/
theorem coeff_lineRadical (n : ℕ) (χ : RankOneCharacter) (p : lineParabolic ℝ)
    (Q : Binary.HomogeneousPoly (n + 1)) (m : Fin 3 →₀ ℕ) :
    (lineRadical n χ p Q : Poly).coeff m =
      algebraMap ℝ ℂ (lrC0 p) *
          (rename (Fin.succ : Fin 2 → Fin 3) (pderiv (0 : Fin 2) (Q : Binary.Poly))).coeff m +
        algebraMap ℝ ℂ (lrC1 p) *
          (rename (Fin.succ : Fin 2 → Fin 3) (pderiv (1 : Fin 2) (Q : Binary.Poly))).coeff m := by
  rw [coe_lineRadical]
  simp only [lrVecDeriv, map_add, map_mul, rename_C, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_C_mul]

/-! ## Analyticity along the Iwasawa factor -/

theorem iwasawaB_mem_lineParabolic (g : RealGL3) : iwasawaB g ∈ lineParabolic ℝ :=
  ⟨(iwasawaB_upper g).1, (iwasawaB_upper g).2.1⟩

/-- The first radical coordinate of the Iwasawa factor is real analytic on the invertible
matrices. -/
theorem lrC0_iwasawaB_contDiffOn :
    ContDiffOn ℝ ⊤ (fun A : Mat3 =>
      lrC0 ⟨iwasawaB (invertibleMatrix A), iwasawaB_mem_lineParabolic _⟩) {A | A.det ≠ 0} := by
  have hB := iwasawaB_contDiffOn
  have hentry : ∀ i j, ContDiffOn ℝ ⊤
      (fun A : Mat3 => (iwasawaB (invertibleMatrix A)).val i j) {A | A.det ≠ 0} :=
    fun i j => contDiffOn_pi.mp (contDiffOn_pi.mp hB i) j
  have hden : ∀ A ∈ {A : Mat3 | A.det ≠ 0},
      (iwasawaB (invertibleMatrix A)).val 1 1 * (iwasawaB (invertibleMatrix A)).val 2 2 -
        (iwasawaB (invertibleMatrix A)).val 1 2 * (iwasawaB (invertibleMatrix A)).val 2 1 ≠ 0 :=
    fun A _ => lrDet_ne_zero ⟨iwasawaB (invertibleMatrix A), iwasawaB_mem_lineParabolic _⟩
  refine ((((hentry 1 1).mul (hentry 0 2)).sub ((hentry 1 2).mul (hentry 0 1))).div
    (((hentry 1 1).mul (hentry 2 2)).sub ((hentry 1 2).mul (hentry 2 1))) hden).congr
    fun A _ => ?_
  rfl

/-- The second radical coordinate of the Iwasawa factor is real analytic on the invertible
matrices. -/
theorem lrC1_iwasawaB_contDiffOn :
    ContDiffOn ℝ ⊤ (fun A : Mat3 =>
      lrC1 ⟨iwasawaB (invertibleMatrix A), iwasawaB_mem_lineParabolic _⟩) {A | A.det ≠ 0} := by
  have hB := iwasawaB_contDiffOn
  have hentry : ∀ i j, ContDiffOn ℝ ⊤
      (fun A : Mat3 => (iwasawaB (invertibleMatrix A)).val i j) {A | A.det ≠ 0} :=
    fun i j => contDiffOn_pi.mp (contDiffOn_pi.mp hB i) j
  have hden : ∀ A ∈ {A : Mat3 | A.det ≠ 0},
      (iwasawaB (invertibleMatrix A)).val 1 1 * (iwasawaB (invertibleMatrix A)).val 2 2 -
        (iwasawaB (invertibleMatrix A)).val 1 2 * (iwasawaB (invertibleMatrix A)).val 2 1 ≠ 0 :=
    fun A _ => lrDet_ne_zero ⟨iwasawaB (invertibleMatrix A), iwasawaB_mem_lineParabolic _⟩
  refine ((((hentry 2 1).mul (hentry 0 2)).sub ((hentry 2 2).mul (hentry 0 1))).div
    (((hentry 1 1).mul (hentry 2 2)).sub ((hentry 1 2).mul (hentry 2 1))) hden).congr
    fun A _ => ?_
  rfl

/-- **Analyticity of the line radical along the analytic Iwasawa factor.** -/
theorem lineRadical_iwasawaB_contDiffOn (n : ℕ) (χ : RankOneCharacter)
    (Q : Binary.HomogeneousPoly (n + 1)) (m : Fin 3 →₀ ℕ) :
    ContDiffOn ℝ ⊤ (fun A : Mat3 =>
      (lineRadical n χ ⟨iwasawaB (invertibleMatrix A), iwasawaB_mem_lineParabolic _⟩ Q).val.coeff
        m) {A | A.det ≠ 0} := by
  have h0 := contDiff_algebraMap_real.fun_comp_contDiffOn lrC0_iwasawaB_contDiffOn
  have h1 := contDiff_algebraMap_real.fun_comp_contDiffOn lrC1_iwasawaB_contDiffOn
  refine ((h0.mul (contDiffOn_const (c :=
      (rename (Fin.succ : Fin 2 → Fin 3) (pderiv (0 : Fin 2) (Q : Binary.Poly))).coeff m))).add
    (h1.mul (contDiffOn_const (c :=
      (rename (Fin.succ : Fin 2 → Fin 3) (pderiv (1 : Fin 2) (Q : Binary.Poly))).coeff m)))).congr
    fun A _ => ?_
  exact coeff_lineRadical n χ _ Q m

end TernaryPeriodPolynomials.SourceConstruction

end
