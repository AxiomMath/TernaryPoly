module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.CupSeed
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Form.Identity
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Line.SeedFrame
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Line.Cholesky
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.RhoContinuity

@[expose] public section


/-!
# The twisted pullback of the seed on a Gram point and its form identity

`twPull ω M P Q₁ Q₂ = ρ(M)⁻¹ ω_{M P Mᵀ}(M Q₁ Mᵀ, M Q₂ Mᵀ)`: the pullback of the pair of Gram tangents `(Q₁, Q₂)` at
`P` under the congruence by `M`, twisted by `ρ(M)⁻¹`.  For `P = q qᵀ` (`q` the Cholesky factor in the line parabolic)
it is `ρ(q) ω̃(M q)(V₁, V₂)` with `V_i = ½ q⁻¹ Q_i q⁻ᵀ` (`twPull_eq_frame`).  Hence the unconditional pointwise form
identity (`form_identity_coeff`) gives, for `M = L_{s,t}`, integrability in `(s,t)` and
`∫ coeff_κ twPull ω L_{s,t} P Q₁ Q₂ = c_∞ coeff_κ (linePairQ σ P Q₁ Q₂)` (`twPull_integral`), where `linePairQ` is the line
seed pair in the same frame.  Homogeneity of the frame coefficients (`isHomogeneous_frameCoefficient_seed`, …) is
what makes the coefficient mixing `ρ(q)` a finite sum over the degree-`n` monomials.

Formalized by Claude Sonnet 5.5.
-/

open scoped Matrix.Norms.Elementwise
open MeasureTheory MvPolynomial GeneralEisenstein Matrix
open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.Statements.RealEntrySeed
open TernaryPeriodPolynomials.Argument.Statements.RealEntryNormalization

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

local notation "Mat3" => Matrix (Fin 3) (Fin 3) ℝ

/-- The `ρ(M)⁻¹`-twisted pullback of a two-form pair under the congruence `G ↦ M G Mᵀ`. -/
def twPull (ω : (Fin 5 → ℝ) → Fin 5 → Fin 5 → MvPolynomial (Fin 3) ℂ) (M P Q₁ Q₂ : Mat3) :
    MvPolynomial (Fin 3) ℂ :=
  SeedC3.rho M⁻¹ (formPair ω (M * P * Mᵀ) (M * Q₁ * Mᵀ) (M * Q₂ * Mᵀ))

/-- `½ q⁻¹ Q q⁻ᵀ`: the direction in the frame `q` of the Gram tangent `Q`. -/
def halfConj (q Q : Mat3) : Mat3 := (1 / 2 : ℝ) • (q⁻¹ * Q * (q⁻¹)ᵀ)

theorem halfConj_spec (q Q : Mat3) (hq : q.det ≠ 0) (hQ : Qᵀ = Q) :
    q * (halfConj q Q + (halfConj q Q)ᵀ) * qᵀ = Q := by
  have hu : IsUnit q.det := isUnit_iff_ne_zero.mpr hq
  have h1 : q * q⁻¹ = 1 := Matrix.mul_nonsing_inv q hu
  have h2 : (q⁻¹)ᵀ * qᵀ = 1 := by
    rw [← Matrix.transpose_mul, h1, Matrix.transpose_one]
  set X : Mat3 := q⁻¹ * Q * (q⁻¹)ᵀ with hX
  have hXt : Xᵀ = X := by
    rw [hX, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hQ, Matrix.mul_assoc]
  have hqX : q * X * qᵀ = Q := by
    rw [hX]
    calc q * (q⁻¹ * Q * (q⁻¹)ᵀ) * qᵀ = (q * q⁻¹) * Q * ((q⁻¹)ᵀ * qᵀ) := by simp only [Matrix.mul_assoc]
      _ = Q := by rw [h1, h2]; simp
  have hs : halfConj q Q + (halfConj q Q)ᵀ = X := by
    unfold halfConj
    rw [← hX, Matrix.transpose_smul, hXt, ← add_smul]
    norm_num
  rw [hs, hqX]

/-- **The twisted pullback in a Cholesky-type frame.** For `P = q qᵀ` and symmetric `Q₁, Q₂` with frame
directions `V_i = ½ q⁻¹ Q_i q⁻ᵀ`: `twPull ω L P Q₁ Q₂ = ρ(q) ω̃(L q)(V₁, V₂)`. -/
theorem twPull_eq_frame (ω : (Fin 5 → ℝ) → Fin 5 → Fin 5 → MvPolynomial (Fin 3) ℂ)
    (L q Q₁ Q₂ : Mat3) (hL : L.det ≠ 0) (hq : q.det ≠ 0) (hQ₁ : Q₁ᵀ = Q₁) (hQ₂ : Q₂ᵀ = Q₂) :
    twPull ω L (q * qᵀ) Q₁ Q₂ =
      SeedC3.rho q (frameCoefficient ω (L * q) (halfConj q Q₁) (halfConj q Q₂)) := by
  have hLq : (L * q).det ≠ 0 := by rw [Matrix.det_mul]; exact mul_ne_zero hL hq
  have e0 : L * (q * qᵀ) * Lᵀ = (L * q) * (L * q)ᵀ := by
    rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
  have eQ : ∀ Q, Qᵀ = Q → L * Q * Lᵀ = (L * q) * (halfConj q Q + (halfConj q Q)ᵀ) * (L * q)ᵀ := by
    intro Q hQ
    have := halfConj_spec q Q hq hQ
    calc L * Q * Lᵀ = L * (q * (halfConj q Q + (halfConj q Q)ᵀ) * qᵀ) * Lᵀ := by rw [this]
      _ = (L * q) * (halfConj q Q + (halfConj q Q)ᵀ) * (L * q)ᵀ := by
        rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
  have hv : formPair ω (L * (q * qᵀ) * Lᵀ) (L * Q₁ * Lᵀ) (L * Q₂ * Lᵀ) =
      frameValue ω (L * q) (halfConj q Q₁) (halfConj q Q₂) := by
    rw [e0, eQ Q₁ hQ₁, eQ Q₂ hQ₂]
    unfold formPair frameValue
    simp only [chartTangent_eq _ _ hLq]
  unfold twPull frameCoefficient
  rw [hv]
  have hLinv : (L * q)⁻¹ = q⁻¹ * L⁻¹ := by
    rw [Matrix.mul_inv_rev]
  rw [hLinv, rho_mul, rho_rho_inv q hq]

theorem isHomogeneous_rho (g : Mat3) {Q : MvPolynomial (Fin 3) ℂ} {k : ℕ} (hQ : Q.IsHomogeneous k) :
    (SeedC3.rho g Q).IsHomogeneous k := by
  rw [rho_eq_C_mul_substitute]
  exact (substitute_homogeneous _ hQ).C_mul _

theorem isHomogeneous_seedLinear (p : Fin 5 → ℝ) : (seedLinear p).IsHomogeneous 1 := by
  unfold seedLinear
  refine IsHomogeneous.add (IsHomogeneous.sub ?_ ?_) ?_
  · exact isHomogeneous_C_mul_X _ _
  · exact isHomogeneous_X _ _
  · exact isHomogeneous_C_mul_X _ _

theorem isHomogeneous_frameCoefficient_seed (n : ℕ) (h : ℂ → ℂ) (g V W : Mat3) :
    (frameCoefficient (seedForm n h) g V W).IsHomogeneous n := by
  unfold frameCoefficient
  rw [frameValue_seedForm]
  refine isHomogeneous_rho _ ?_
  have := (isHomogeneous_seedLinear (gramChart (g * gᵀ))).pow n
  rw [one_mul] at this
  exact this.C_mul _

theorem isHomogeneous_formPair_seed (n : ℕ) (h : ℂ → ℂ) (G Q₁ Q₂ : Mat3) :
    (formPair (seedForm n h) G Q₁ Q₂).IsHomogeneous n := by
  rw [formPair_seedForm]
  have := (isHomogeneous_seedLinear (gramChart G)).pow n
  rw [one_mul] at this
  exact this.C_mul _

theorem coeff_eq_zero_of_sum_ne {Q : MvPolynomial (Fin 3) ℂ} {n : ℕ} (hQ : Q.IsHomogeneous n)
    (m' : Fin 3 →₀ ℕ) (hm' : m'.sum (fun _ k => k) ≠ n) : Q.coeff m' = 0 := by
  apply hQ.coeff_eq_zero
  intro hdeg
  exact hm' hdeg

theorem isHomogeneous_lineFrameCoefficient (n : ℕ) (h : ℂ → ℂ) (g V W : Mat3) :
    (lineFrameCoefficient (lineSeedForm n h) g V W).IsHomogeneous n := by
  rw [lineFrameCoefficient_lineSeedForm]
  refine isHomogeneous_rho _ ?_
  have hlin : (C (lineTau (lineChart (g * gᵀ))) * X 2 - X 1 : MvPolynomial (Fin 3) ℂ).IsHomogeneous 1 :=
    (isHomogeneous_C_mul_X _ _).sub (isHomogeneous_X _ _)
  have := hlin.pow n
  rw [one_mul] at this
  exact this.C_mul _

/-- The line-seed pair in the Cholesky frame of the Gram point `P`. -/
def linePairQ (σ : (Fin 5 → ℝ) → Fin 5 → Fin 5 → MvPolynomial (Fin 3) ℂ) (P Q₁ Q₂ : Mat3) :
    MvPolynomial (Fin 3) ℂ :=
  SeedC3.rho (cholLine P) (lineFrameCoefficient σ (cholLine P) (halfConj (cholLine P) Q₁)
    (halfConj (cholLine P) Q₂))

theorem det_cholLine (P : Mat3) : (cholLine P).det = cholA P * (cholC00 P * cholC11 P) := by
  simp [cholLine, Matrix.det_fin_three]
  ring

theorem cholLine_det_pos {P : Mat3} (hs : 0 < P 2 2) (hD : 0 < P 1 1 * P 2 2 - P 1 2 ^ 2)
    (hdet : 0 < P.det) : 0 < (cholLine P).det := by
  rw [det_cholLine]
  exact mul_pos (cholA_pos P hD hdet) (mul_pos (cholC00_pos P hs hD) (cholC11_pos P hs))

/-- **The form identity for the twisted pullback at a Gram point.** -/
theorem twPull_integral (n : ℕ) (hn : 3 ≤ n) (h : ℂ → ℂ) (hh : DifferentiableOn ℂ h {z : ℂ | 0 < z.im})
    (M : ℝ) (hM : ∀ z : ℂ, 0 < z.im → ‖h z‖ ^ 2 * z.im ^ (n + 3) ≤ M)
    (P Q₁ Q₂ : Mat3) (hP : Pᵀ = P) (hs : 0 < P 2 2) (hD : 0 < P 1 1 * P 2 2 - P 1 2 ^ 2)
    (hdet : 0 < P.det) (hQ₁ : Q₁ᵀ = Q₁) (hQ₂ : Q₂ᵀ = Q₂) (κ : Fin 3 →₀ ℕ) :
    Integrable (fun st : ℝ × ℝ =>
      (twPull (seedForm n h) (entryFrame st.1 st.2) P Q₁ Q₂).coeff κ) ∧
    ∫ st : ℝ × ℝ, (twPull (seedForm n h) (entryFrame st.1 st.2) P Q₁ Q₂).coeff κ =
      (-2 * Real.pi * Complex.I / ((n : ℂ) + 1)) *
        (linePairQ (lineSeedForm n h) P Q₁ Q₂).coeff κ := by
  set q := cholLine P with hqdef
  have hqP : q * qᵀ = P := cholLine_mul_transpose P hP hs hD hdet
  have hqpos : 0 < q.det := cholLine_det_pos hs hD hdet
  have hqne : q.det ≠ 0 := hqpos.ne'
  set V₁ := halfConj q Q₁ with hV₁
  set V₂ := halfConj q Q₂ with hV₂
  have e : ∀ st : ℝ × ℝ, twPull (seedForm n h) (entryFrame st.1 st.2) P Q₁ Q₂ =
      SeedC3.rho q (frameCoefficient (seedForm n h) (entryFrame st.1 st.2 * q) V₁ V₂) := by
    intro st
    have := twPull_eq_frame (seedForm n h) (entryFrame st.1 st.2) q Q₁ Q₂
      (by rw [entryFrame_det_eq]; exact one_ne_zero) hqne hQ₁ hQ₂
    rwa [hqP] at this
  have hpt : ∀ st : ℝ × ℝ, (twPull (seedForm n h) (entryFrame st.1 st.2) P Q₁ Q₂).coeff κ =
      ∑ ν ∈ degSet n, (frameCoefficient (seedForm n h) (entryFrame st.1 st.2 * q) V₁ V₂).coeff ν *
          (SeedC3.rho q (MvPolynomial.monomial ν 1)).coeff κ := by
    intro st
    rw [e]
    exact coeff_rho_eq_sum q n _ (fun m' hm' => coeff_eq_zero_of_sum_ne
      (isHomogeneous_frameCoefficient_seed n h _ V₁ V₂) m' hm') κ
  have hF : ∀ ν ∈ degSet n,
      Integrable (fun st : ℝ × ℝ => (frameCoefficient (seedForm n h) (entryFrame st.1 st.2 * q) V₁ V₂).coeff ν) ∧
      intFrameCoeff n h q V₁ V₂ ν = (-2 * Real.pi * Complex.I / ((n : ℂ) + 1)) *
        (lineFrameCoefficient (lineSeedForm n h) q V₁ V₂).coeff ν :=
    fun ν _ => form_identity_coeff n hn h hh M hM q hqpos V₁ V₂ ν
  simp_rw [hpt]
  refine ⟨integrable_finsetSum _ (fun ν hν => (hF ν hν).1.mul_const _), ?_⟩
  rw [integral_finsetSum _ (fun ν hν => (hF ν hν).1.mul_const _)]
  simp_rw [integral_mul_const]
  unfold linePairQ
  rw [← hqdef, ← hV₁, ← hV₂]
  rw [coeff_rho_eq_sum q n _ (fun m' hm' => coeff_eq_zero_of_sum_ne (isHomogeneous_lineFrameCoefficient n h q V₁ V₂) m' hm') κ,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun ν hν => ?_
  have := (hF ν hν).2
  unfold intFrameCoeff at this
  rw [this]
  ring

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
