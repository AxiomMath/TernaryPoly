module

public import TernaryPeriodPolynomials.DifferentialForm.DeRham.Covering.Geometry
public import Mathlib.Analysis.Convex.Basic

@[expose] public section

noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Set

/-- A positive-denominator fractional affine map sends a convex domain to a convex set.
The barycentric preimage uses the actual reciprocal denominator weights. -/
theorem convex_image_fractional_affine
    {E H : Type} [AddCommGroup E] [Module ℝ E] [AddCommGroup H] [Module ℝ H]
    {S : Set E} (hS : Convex ℝ S) (f : E → H) (d : E → ℝ)
    (hd : ∀ x ∈ S, 0 < d x)
    (hf : ∀ x ∈ S, ∀ y ∈ S, ∀ a b : ℝ, a + b = 1 →
      f (a • x + b • y) = a • f x + b • f y)
    (hda : ∀ x ∈ S, ∀ y ∈ S, ∀ a b : ℝ, a + b = 1 →
      d (a • x + b • y) = a * d x + b * d y) :
    Convex ℝ ((fun x => (d x)⁻¹ • f x) '' S) := by
  intro u hu v hv a b ha hb hab
  obtain ⟨x,hx,rfl⟩ := hu
  obtain ⟨y,hy,rfl⟩ := hv
  have hxpos := hd x hx
  have hypos := hd y hy
  have hx0 := ne_of_gt hxpos
  have hy0 := ne_of_gt hypos
  let c := a / d x + b / d y
  have hc : 0 < c := by
    have h₁ : 0 ≤ a / d x := div_nonneg ha hxpos.le
    have h₂ : 0 ≤ b / d y := div_nonneg hb hypos.le
    by_contra hn
    have hz : a / d x + b / d y = 0 := le_antisymm (le_of_not_gt hn) (add_nonneg h₁ h₂)
    have ha0 : a / d x = 0 := by linarith
    have hb0 : b / d y = 0 := by linarith
    have : a = 0 := (div_eq_zero_iff).mp ha0 |>.resolve_right hx0
    have : b = 0 := (div_eq_zero_iff).mp hb0 |>.resolve_right hy0
    linarith
  have hc0 := ne_of_gt hc
  let A := (a / d x) / c
  let B := (b / d y) / c
  have hAB : A + B = 1 := by dsimp [A,B]; rw [← add_div]; exact div_self hc0
  have hz := hS hx hy (div_nonneg (div_nonneg ha hxpos.le) hc.le)
    (div_nonneg (div_nonneg hb hypos.le) hc.le) hAB
  refine ⟨A • x + B • y, hz, ?_⟩
  have hdv : d (A • x + B • y) = c⁻¹ := by
    rw [hda x hx y hy A B hAB]
    dsimp [A,B]
    field_simp
    nlinarith [hab]
  change (d (A • x + B • y))⁻¹ • f (A • x + B • y) =
    a • ((d x)⁻¹ • f x) + b • ((d y)⁻¹ • f y)
  rw [hdv, inv_inv, hf x hx y hy A B hAB, smul_add, smul_smul, smul_smul,
    smul_smul, smul_smul]
  have hA : c * A = a * (d x)⁻¹ := by dsimp [A]; field_simp
  have hB : c * B = b * (d y)⁻¹ := by dsimp [B]; field_simp
  rw [hA,hB]

end TernaryPoly.SmoothSingularGlobal
