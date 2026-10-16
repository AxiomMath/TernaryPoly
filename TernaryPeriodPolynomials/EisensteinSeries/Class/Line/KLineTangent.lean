module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Line.KGxExplicit
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Line.KBridgeA

@[expose] public section


/-!
# The line-chart tangents of the Maurer-Cartan directions

Paper: Appendix C.5.

`lineTangent g V` is defined by differentiating the line chart along the curve `g(1 + εV)(1 + εV)ᵀgᵀ`. For
`g = g_x` and `V = V_e(x) = g_x⁻¹ ∂_e g_x` this curve has the same value and velocity as `g_{x+εe} g_{x+εe}ᵀ`
(`lineTangent_gx_eq`), whose line chart is `(-u₂, -u₁, -ξ, η)` (`lineChart_gx_values`). Hence
`lineTangent g_x V_e = (-e₁, -e₀, -e₂, e₃, *)` in the first four coordinates (`lineTangent_gx_values`).

Formalized by Claude Sonnet 5.5.
-/

open MeasureTheory MvPolynomial
open scoped MatrixGroups ContDiff Matrix
noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.SeedC3S4c
  TernaryPeriodPolynomials.Argument.FormClassK TernaryPeriodPolynomials.Argument.GammaNFaces
  TernaryPeriodPolynomials.Argument.Statements.EisensteinClass TernaryPeriodPolynomials.Argument.Statements.ConvergenceC4
  TernaryPeriodPolynomials.Argument.EisensteinDual
  TernaryPoly.SmoothLocalDeRham TernaryPoly.SmoothCoveringDeRham
  TernaryPeriodPolynomials.Argument.SeedC3.Psi
open TernaryPeriodPolynomials.Argument.Statements.RealEntrySeed (gramCurve)
open TernaryPeriodPolynomials.Argument.Statements.RealEntryNormalization (lineChart lineTangent)

section Smooth

theorem diffAt_lineChart {G₀ : Matrix (Fin 3) (Fin 3) ℝ} (h22 : 0 < G₀ 2 2)
    (hD : 0 < G₀ 1 1 * G₀ 2 2 - G₀ 1 2 * G₀ 2 1) (a : Fin 5) (ha : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3) :
    DifferentiableAt ℝ (fun z : Fin 3 → Fin 3 → ℝ => lineChart (matOfFun z) a) (matToFun G₀) := by
  have hF : ∀ i j, ContDiffAt ℝ ⊤ (fun z : Fin 3 → Fin 3 → ℝ => matOfFun z i j) (matToFun G₀) := by
    intro i j
    exact ((contDiff_apply ℝ ℝ j).comp (contDiff_apply ℝ (Fin 3 → ℝ) i)).contDiffAt
  have hDD : ContDiffAt ℝ ⊤ (fun z : Fin 3 → Fin 3 → ℝ =>
      matOfFun z 1 1 * matOfFun z 2 2 - matOfFun z 1 2 * matOfFun z 2 1) (matToFun G₀) :=
    ((hF 1 1).mul (hF 2 2)).sub ((hF 1 2).mul (hF 2 1))
  rcases ha with rfl | rfl | rfl | rfl
  · have : (fun z : Fin 3 → Fin 3 → ℝ => lineChart (matOfFun z) 0) = fun z =>
        (matOfFun z 0 1 * matOfFun z 2 2 - matOfFun z 0 2 * matOfFun z 2 1) /
          (matOfFun z 1 1 * matOfFun z 2 2 - matOfFun z 1 2 * matOfFun z 2 1) :=
      funext fun z => lineChart_c0 _
    rw [this]
    exact ((((hF 0 1).mul (hF 2 2)).sub ((hF 0 2).mul (hF 2 1))).div hDD hD.ne').differentiableAt (by simp)
  · have : (fun z : Fin 3 → Fin 3 → ℝ => lineChart (matOfFun z) 1) = fun z =>
        (matOfFun z 0 2 * matOfFun z 1 1 - matOfFun z 0 1 * matOfFun z 1 2) /
          (matOfFun z 1 1 * matOfFun z 2 2 - matOfFun z 1 2 * matOfFun z 2 1) :=
      funext fun z => lineChart_c1 _
    rw [this]
    exact ((((hF 0 2).mul (hF 1 1)).sub ((hF 0 1).mul (hF 1 2))).div hDD hD.ne').differentiableAt (by simp)
  · have : (fun z : Fin 3 → Fin 3 → ℝ => lineChart (matOfFun z) 2) = fun z =>
        matOfFun z 1 2 / matOfFun z 2 2 := funext fun z => lineChart_c2 _
    rw [this]
    exact ((hF 1 2).div (hF 2 2) h22.ne').differentiableAt (by simp)
  · have : (fun z : Fin 3 → Fin 3 → ℝ => lineChart (matOfFun z) 3) = fun z =>
        Real.sqrt (matOfFun z 1 1 * matOfFun z 2 2 - matOfFun z 1 2 * matOfFun z 2 1) /
          matOfFun z 2 2 := funext fun z => lineChart_c3 _
    rw [this]
    exact ((hDD.sqrt hD.ne').div (hF 2 2) h22.ne').differentiableAt (by simp)

theorem deriv_eq_of_curves {Γ : Matrix (Fin 3) (Fin 3) ℝ → ℝ} {G₁ G₂ : ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    {S : Matrix (Fin 3) (Fin 3) ℝ}
    (hΓ : DifferentiableAt ℝ (fun z : Fin 3 → Fin 3 → ℝ => Γ (matOfFun z)) (matToFun (G₁ 0)))
    (h0 : G₂ 0 = G₁ 0) (h₁ : ∀ i j, HasDerivAt (fun ε => G₁ ε i j) (S i j) 0)
    (h₂ : ∀ i j, HasDerivAt (fun ε => G₂ ε i j) (S i j) 0) :
    deriv (fun ε => Γ (G₁ ε)) 0 = deriv (fun ε => Γ (G₂ ε)) 0 := by
  have hd := hΓ.hasFDerivAt
  have hc₁ : HasDerivAt (fun ε => matToFun (G₁ ε)) (matToFun S) 0 := by
    rw [hasDerivAt_pi]; intro i; rw [hasDerivAt_pi]; intro j; exact h₁ i j
  have hc₂ : HasDerivAt (fun ε => matToFun (G₂ ε)) (matToFun S) 0 := by
    rw [hasDerivAt_pi]; intro i; rw [hasDerivAt_pi]; intro j; exact h₂ i j
  have e1 := hd.comp_hasDerivAt (0 : ℝ) hc₁
  have hd' : HasFDerivAt (fun z : Fin 3 → Fin 3 → ℝ => Γ (matOfFun z))
      (fderiv ℝ (fun z : Fin 3 → Fin 3 → ℝ => Γ (matOfFun z)) (matToFun (G₁ 0))) (matToFun (G₂ 0)) := by
    rw [h0]; exact hd
  have e2 := hd'.comp_hasDerivAt (0 : ℝ) hc₂
  exact e1.deriv.trans e2.deriv.symm

end Smooth

section Curve

theorem hasDerivAt_gram_B {x : Face} (hx : x ∈ faceSet) (e : Face) (i j : Fin 3) :
    HasDerivAt (fun ε : ℝ => (gx (x + ε • e) * (gx (x + ε • e)).transpose) i j)
      ((dgx x e * (gx x).transpose + gx x * (dgx x e).transpose) i j) 0 := by
  have hB := hasDerivAt_gx_entry hx e
  have hBt : ∀ i j, HasDerivAt (fun ε : ℝ => (gx (x + ε • e)).transpose i j)
      ((dgx x e).transpose i j) 0 := fun i j => by simpa using hB j i
  have := hasDerivAt_mat_mul (A := fun ε => gx (x + ε • e))
    (B := fun ε => (gx (x + ε • e)).transpose) hB hBt i j
  simpa using this

theorem S_eq {x : Face} (hx : x ∈ faceSet) (e : Face) :
    gx x * (Vgx x e + (Vgx x e).transpose) * (gx x).transpose =
      dgx x e * (gx x).transpose + gx x * (dgx x e).transpose := by
  have hgV : gx x * Vgx x e = dgx x e := by
    unfold Vgx
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (unit_det_gx hx), Matrix.one_mul]
  have h2 : (Vgx x e).transpose * (gx x).transpose = (dgx x e).transpose := by
    rw [← Matrix.transpose_mul, hgV]
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc (gx x) (Vgx x e).transpose, h2, hgV]

theorem lineTangent_gx_eq {x : Face} (hx : x ∈ faceSet) (e : Face) (a : Fin 5)
    (ha : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3) :
    lineTangent (gx x) (Vgx x e) a =
      deriv (fun ε : ℝ => lineChart (gx (x + ε • e) * (gx (x + ε • e)).transpose) a) 0 := by
  have hy : (0 : ℝ) < x 3 := hx
  obtain ⟨-, -, -, -, h22⟩ := gx_gram_entries hx
  have hG22 : 0 < (gx x * (gx x).transpose) 2 2 := by rw [h22]; positivity
  have hDpos : 0 < (gx x * (gx x).transpose) 1 1 * (gx x * (gx x).transpose) 2 2 -
      (gx x * (gx x).transpose) 1 2 * (gx x * (gx x).transpose) 2 1 := by
    rw [lineChart_gx_det hx]; exact one_pos
  have hdiff := diffAt_lineChart hG22 hDpos a ha
  have e0 : gramCurve (gx x) (Vgx x e) 0 = gx x * (gx x).transpose := by simp [gramCurve]
  unfold lineTangent
  refine deriv_eq_of_curves (Γ := fun G => lineChart G a) (G₁ := gramCurve (gx x) (Vgx x e))
    (G₂ := fun ε => gx (x + ε • e) * (gx (x + ε • e)).transpose)
    (S := gx x * (Vgx x e + (Vgx x e).transpose) * (gx x).transpose) ?_ ?_
    (hasDerivAt_gram_V (gx x) (Vgx x e)) ?_
  · rw [e0]; exact hdiff
  · rw [e0]; simp
  · intro i j
    have := hasDerivAt_gram_B hx e i j
    rwa [← S_eq hx e] at this

end Curve

end TernaryPeriodPolynomials.Argument.EisensteinClass
