module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Line.KBridgeB
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Form.Identity
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Plane.Twist
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Line.SeedFrame

@[expose] public section


/-!
# The bridge: the real intertwining integral at a face point is `c_∞` times the line seed

Paper: Appendix C.5 (`ar:eq:intertwiner`, `ar:eq:cinfty`).

`Tinf_eq_lineSeed`: for `3 ≤ n`, `h` holomorphic on the upper half plane with the cusp decay `‖h z‖² (Im z)^(n+3) ≤ M`,
every face point `x`, pair `(e_p, e_q)` and coefficient `m`:
`T_∞[h](x; e_p, e_q)_m = c_∞ · h(τ_x) · lineWedge x p q · coeff_m (τ_x Z - Y)ⁿ`, `τ_x = lineTau (lineChart (g_x g_xᵀ))`.
This combines `Tinf_eq` (`fPull_gx`, `integral_fin2_negswap`)/`form_identity_coeff` and the closed form of
the line seed frame coefficient.

Formalized by Claude Sonnet 5.5.
-/

open MeasureTheory MvPolynomial
open scoped MatrixGroups ContDiff Matrix
noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument.FormClassK TernaryPeriodPolynomials.Argument.EisensteinDual
open TernaryPeriodPolynomials.Argument.Statements.RealEntrySeed (gramChart gramCurve chartTangent)


section Integrate

open TernaryPeriodPolynomials.Argument.Statements.RealEntrySeed (frameCoefficient)
open TernaryPeriodPolynomials.Argument.Statements.RealEntryNormalization
  (lineFrameCoefficient lineSeedForm lineTangent lineChart lineTau)
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
  (form_identity_coeff intFrameCoeff coeff_rho_eq_sum isHomogeneous_frameCoefficient_seed
    isHomogeneous_lineFrameCoefficient coeff_eq_zero_of_sum_ne degSet lineFrameCoefficient_lineSeedForm)

/-- The line-seed wedge scalar `β(V) dτ(W) - β(W) dτ(V)` of the Maurer-Cartan directions at `x`. -/
def lineWedge (x : Face) (p q : Fin 4) : ℂ :=
  TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry.lineBeta
      (lineTau (lineChart (gx x * (gx x).transpose))) (lineTangent (gx x) (Vgx x (Pi.single p 1))) *
    TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry.lineDTauOf
      (lineTangent (gx x) (Vgx x (Pi.single q 1))) -
  TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry.lineBeta
      (lineTau (lineChart (gx x * (gx x).transpose))) (lineTangent (gx x) (Vgx x (Pi.single q 1))) *
    TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry.lineDTauOf
      (lineTangent (gx x) (Vgx x (Pi.single p 1)))

/-- **The bridge**: the real intertwining integral of the seed `h` at the face point `x` (pair `(e_p, e_q)`,
coefficient `m`) is `c_∞` times the line seed: `h(τ_x) · lineWedge · coeff_m (τ_x Z - Y)ⁿ`,
`τ_x = lineTau (lineChart (g_x g_xᵀ))`. -/
theorem Tinf_eq_lineSeed (n : ℕ) (hn : 3 ≤ n) (h : ℂ → ℂ)
    (hh : DifferentiableOn ℂ h {z : ℂ | 0 < z.im}) (M : ℝ)
    (hM : ∀ z : ℂ, 0 < z.im → ‖h z‖ ^ 2 * z.im ^ (n + 3) ≤ M) {x : Face} (hx : x ∈ faceSet)
    (p q : Fin 4) (m : Fin 3 →₀ ℕ) :
    Tinf n h x p q m = (-2 * Real.pi * Complex.I / ((n : ℂ) + 1)) *
      (h (lineTau (lineChart (gx x * (gx x).transpose))) * lineWedge x p q *
        ((C (lineTau (lineChart (gx x * (gx x).transpose))) * X 2 - X 1 : MvPolynomial (Fin 3) ℂ) ^ n).coeff m) := by
  set g := gx x with hgdef
  have hg : g.det = 1 := det_gx hx
  have hg0 : g.det ≠ 0 := by rw [hg]; exact one_ne_zero
  set Vp := Vgx x (Pi.single p 1) with hVp
  set Vq := Vgx x (Pi.single q 1) with hVq
  set F : ℝ × ℝ → ℂ := fun st => ((rho g (frameCoefficient (seedForm n h) (entryFrame st.1 st.2 * g) Vp Vq)) :
    MvPolynomial (Fin 3) ℂ).coeff m with hF
  have hpt : ∀ u : Fin 2 → ℝ, orbitIntegrand n h x p q m W0inv u = F (-(u 1), -(u 0)) := by
    intro u
    have hMdet : (W0inv * qMat u).det = 1 := by rw [Matrix.det_mul, det_W0inv, det_qMat]; norm_num
    unfold orbitIntegrand
    rw [fPull_gx n h hMdet hx p q, W0inv_qMat]
  have hT : Tinf n h x p q m = ∫ st : ℝ × ℝ, F st := by
    unfold Tinf
    simp_rw [hpt]
    exact integral_fin2_negswap F
  have hQ : ∀ st : ℝ × ℝ, ∀ m' : Fin 3 →₀ ℕ, m'.sum (fun _ k => k) ≠ n →
      (frameCoefficient (seedForm n h) (entryFrame st.1 st.2 * g) Vp Vq).coeff m' = 0 :=
    fun st m' hm' => coeff_eq_zero_of_sum_ne (isHomogeneous_frameCoefficient_seed n h _ _ _) m' hm'
  set κ : (Fin 3 →₀ ℕ) → ℂ := fun m' => (rho g (monomial m' 1)).coeff m with hκ
  have hFsum : ∀ st : ℝ × ℝ, F st = ∑ m' ∈ degSet n,
      (frameCoefficient (seedForm n h) (entryFrame st.1 st.2 * g) Vp Vq).coeff m' * κ m' :=
    fun st => coeff_rho_eq_sum g n _ (hQ st) m
  have hid := fun m' => form_identity_coeff n hn h hh M hM g (by rw [hg]; norm_num) Vp Vq m'
  rw [hT]
  simp_rw [hFsum]
  rw [MeasureTheory.integral_finsetSum _ (fun m' _ => (hid m').1.mul_const (κ m'))]
  have hint : ∀ m' ∈ degSet n, ∫ st : ℝ × ℝ,
      (frameCoefficient (seedForm n h) (entryFrame st.1 st.2 * g) Vp Vq).coeff m' * κ m' =
      (-2 * Real.pi * Complex.I / ((n : ℂ) + 1)) *
        ((lineFrameCoefficient (lineSeedForm n h) g Vp Vq).coeff m' * κ m') := by
    intro m' _
    rw [MeasureTheory.integral_mul_const]
    have := (hid m').2
    unfold intFrameCoeff at this
    rw [this]; ring
  rw [Finset.sum_congr rfl hint, ← Finset.mul_sum]
  congr 1
  rw [← coeff_rho_eq_sum g n _ (fun m' hm' => coeff_eq_zero_of_sum_ne
    (isHomogeneous_lineFrameCoefficient n h g Vp Vq) m' hm') m]
  rw [lineFrameCoefficient_lineSeedForm, TernaryPeriodPolynomials.Argument.Statements.RealEntrySeed.rho_rho_inv g hg0, MvPolynomial.coeff_C_mul]
  unfold lineWedge
  ring

end Integrate


end TernaryPeriodPolynomials.Argument.EisensteinClass
