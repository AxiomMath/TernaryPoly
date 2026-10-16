module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Plane.Fubini
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Line.CupSeed

@[expose] public section


/-!
# The line seed pair in the Cholesky frame is the frame-free line pair

`linePairQ_eq_lineFormPair`: the line-seed pair `ρ(q) σ̃(q)(V₁, V₂)` in the Cholesky frame `q` of a Gram point `P`
equals the frame-free pairing `lineFormPair σ P Q₁ Q₂` of the line seed with the Gram tangents `Q₁, Q₂`
(`lineTangent_eq_fderiv`).  Together with `plane_fubini` and `line_cup_bridge` this connects the real
intertwining integral of the plane cup/integral cochain with the line cup/integral cochain.

Formalized by Claude Sonnet 5.5.
-/

open scoped Matrix.Norms.Elementwise
open MeasureTheory MvPolynomial GeneralEisenstein Matrix
open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.Statements.RealEntrySeed
open TernaryPeriodPolynomials.Argument.Statements.RealEntryNormalization

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

local notation "Mat3" => Matrix (Fin 3) (Fin 3) ℝ

/-- The line seed pair in the Cholesky frame is the frame-free line pair of the Gram tangents. -/
theorem linePairQ_eq_lineFormPair (σ : (Fin 5 → ℝ) → Fin 5 → Fin 5 → MvPolynomial (Fin 3) ℂ)
    (P Q₁ Q₂ : Mat3) (hP : Pᵀ = P) (hPd : P ∈ cholDomain) (hQ₁ : Q₁ᵀ = Q₁) (hQ₂ : Q₂ᵀ = Q₂) :
    linePairQ σ P Q₁ Q₂ = lineFormPair σ P Q₁ Q₂ := by
  obtain ⟨hs, hD, hdet⟩ := hPd
  set q := cholLine P with hqdef
  have hqP : q * qᵀ = P := cholLine_mul_transpose P hP hs hD hdet
  have hqne : q.det ≠ 0 := (cholLine_det_pos hs hD hdet).ne'
  have hT : ∀ (Q : Mat3), Qᵀ = Q → ∀ a, lineTangent q (halfConj q Q) a = lineT P Q a := by
    intro Q hQ a
    rw [lineTangent_eq_fderiv q _ hqne a, halfConj_spec q Q hqne hQ, hqP]
    rfl
  unfold linePairQ lineFrameCoefficient lineFormPair
  have hchart : lineChart (q * qᵀ) = lineChart P := by rw [hqP]
  simp only [hT Q₁ hQ₁, hT Q₂ hQ₂, hchart, ← hqdef]
  rw [rho_rho_inv q hqne]

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
