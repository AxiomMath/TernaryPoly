module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Form.IdentityAssembly
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Line.SeedFrame

@[expose] public section


/-!
# The pointwise form identity (unconditional)

`form_identity_coeff`: for `n ≥ 3`, `h` holomorphic on the upper half-plane with the cusp decay
`‖h z‖² (Im z)^{n+3} ≤ M`, every `g` with `0 < det g`, all `V, W` and every polynomial coefficient `m`, the function
`(s,t) ↦ coeff_m ω̃_h(L_{s,t} g)(V,W)` is integrable over `ℝ²` and
`∫_{ℝ²} coeff_m ω̃_h(L_{s,t} g)(V,W) = c_∞ · coeff_m σ̃_h(g)(V,W)`, `c_∞ = -2πi/(n+1)`, where `ω_h` is the plane seed
and `σ_h` the line seed.  This is `form_identity_coeff_of_R3` with the line-seed covariance
`lineFrameCoefficient_lineParabolic` (R3, proved in `LineSeedFrame`) discharged.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

open MeasureTheory TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.Statements.RealEntrySeed
open TernaryPeriodPolynomials.Argument.Statements.RealEntryNormalization

/-- **The pointwise form identity, one coefficient.** -/
theorem form_identity_coeff (n : ℕ) (hn : 3 ≤ n) (h : ℂ → ℂ)
    (hh : DifferentiableOn ℂ h {z : ℂ | 0 < z.im}) (M : ℝ)
    (hM : ∀ z : ℂ, 0 < z.im → ‖h z‖ ^ 2 * z.im ^ (n + 3) ≤ M)
    (g : Matrix (Fin 3) (Fin 3) ℝ) (hg : 0 < g.det) (V W : Matrix (Fin 3) (Fin 3) ℝ)
    (m : Fin 3 →₀ ℕ) :
    Integrable (fun st : ℝ × ℝ =>
      (frameCoefficient (seedForm n h) (entryFrame st.1 st.2 * g) V W).coeff m) ∧
    intFrameCoeff n h g V W m =
      (-2 * Real.pi * Complex.I / ((n : ℂ) + 1)) *
        (lineFrameCoefficient (lineSeedForm n h) g V W).coeff m :=
  form_identity_coeff_of_R3 n hn h hh M hM
    (fun a b C ha hC g V W hg => lineFrameCoefficient_lineParabolic n h a b C ha hC g V W hg) g hg V W m

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
