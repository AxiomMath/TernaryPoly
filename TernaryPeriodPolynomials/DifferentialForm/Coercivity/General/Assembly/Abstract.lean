module

public import Mathlib

@[expose] public section


/-!
# Abstract Weitzenboeck assembly for the general coercivity estimate

Formalized by Claude Sonnet 5.5.

This file is pure algebra and contains no geometry.  It records the formal argument by which the
pointwise algebraic coercivity of the symmetric parts `S↑`, `S↓` of the exterior derivative and its
adjoint is promoted to coercivity of `d` and its formal adjoint `δ` on a space of forms, once the
four integrated identities (`H1`-`H4` below) are available.

Three vector spaces `A`, `M`, `U` (forms of degree `m - 1`, `m`, `m + 1`) carry symmetric bilinear
forms `BA`, `BM`, `BU` (the `L²` pairings); `d`, `δ` are the exterior derivative and its formal
adjoint, and `S↑`, `S↓` are the zero-order symmetric parts, so that `d - S↑` and `δ - S↓` are the
covariant exterior derivative and its adjoint.  The identities are

* `H1`  `⟪d a, ω⟫_M = ⟪a, δ ω⟫_A` (integration by parts);
* `H2`, `H3`  the pointwise adjointness of `S↑` and `S↓`, integrated;
* `H4`  `⟪ω, S↓ (d ω - S↑ ω) + (d - S↑) (S↓ ω)⟫_M = 0`, the integral of a divergence.

The conclusion is `‖S↑ ω‖² + ‖S↓ ω‖² ≤ ‖d ω‖² + ‖δ ω‖²`, with equality up to the nonnegative terms
`‖(d - S↑) ω‖² + ‖(δ - S↓) ω‖²`.
-/

namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity.Abstract

section

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Expansion of the square of a sum for a symmetric real bilinear form. -/
theorem bilin_add_self (B : LinearMap.BilinForm ℝ V) (hB : ∀ x y, B x y = B y x) (x y : V) :
    B (x + y) (x + y) = B x x + 2 * B x y + B y y := by
  simp only [map_add, LinearMap.add_apply]
  rw [hB y x]
  ring

/-- Splitting `B (x) (x)` along a decomposition `x = n + s`, solved for `B s s + 2 B s n`. -/
theorem bilin_sub_self (B : LinearMap.BilinForm ℝ V) (hB : ∀ x y, B x y = B y x) (x s : V) :
    B x x = B (x - s) (x - s) + 2 * B s (x - s) + B s s := by
  have h := bilin_add_self B hB (x - s) s
  rw [sub_add_cancel] at h
  rw [h, hB (x - s) s]

end

section

variable {A M U : Type*} [AddCommGroup A] [Module ℝ A] [AddCommGroup M] [Module ℝ M]
  [AddCommGroup U] [Module ℝ U]

/-- The abstract Weitzenboeck inequality.  Given the integrated identities `H1`-`H4`, the squared
norms of the symmetric parts are bounded by those of `d ω` and `δ ω`. -/
theorem symmetric_le_flat (BA : LinearMap.BilinForm ℝ A) (BM : LinearMap.BilinForm ℝ M)
    (BU : LinearMap.BilinForm ℝ U)
    (hA : ∀ x y, BA x y = BA y x) (hM : ∀ x y, BM x y = BM y x) (hU : ∀ x y, BU x y = BU y x)
    (hApos : ∀ x, 0 ≤ BA x x) (hUpos : ∀ x, 0 ≤ BU x x)
    (d : M → U) (dA : A → M) (δ : M → A) (sU : M → U) (sA : A → M) (sD : M → A) (sDU : U → M)
    (H1 : ∀ (a : A) (ω : M), BM (dA a) ω = BA a (δ ω))
    (H2 : ∀ (a : A) (ω : M), BM (sA a) ω = BA a (sD ω))
    (H3 : ∀ (ω : M) (u : U), BU (sU ω) u = BM ω (sDU u))
    (H4 : ∀ ω : M, BM ω (sDU (d ω - sU ω) + (dA (sD ω) - sA (sD ω))) = 0) (ω : M) :
    BU (sU ω) (sU ω) + BA (sD ω) (sD ω) ≤ BU (d ω) (d ω) + BA (δ ω) (δ ω) := by
  have eU := bilin_sub_self BU hU (d ω) (sU ω)
  have eA := bilin_sub_self BA hA (δ ω) (sD ω)
  have cU : BU (sU ω) (d ω - sU ω) = BM ω (sDU (d ω - sU ω)) := H3 ω _
  have cA : BA (sD ω) (δ ω - sD ω) = BM ω (dA (sD ω) - sA (sD ω)) := by
    have h1 := H1 (sD ω) ω
    have h2 := H2 (sD ω) ω
    simp only [map_sub]
    rw [hM ω (dA (sD ω)), hM ω (sA (sD ω)), h1, h2]
  have h4 := H4 ω
  rw [map_add] at h4
  have pU := hUpos (d ω - sU ω)
  have pA := hApos (δ ω - sD ω)
  linarith

/-- The one-sided version of `symmetric_le_flat` (lowest degree: there is no `A`-side). -/
theorem symmetric_le_flat_bot (BM : LinearMap.BilinForm ℝ M) (BU : LinearMap.BilinForm ℝ U)
    (hU : ∀ x y, BU x y = BU y x) (hUpos : ∀ x, 0 ≤ BU x x)
    (d : M → U) (sU : M → U) (sDU : U → M)
    (H3 : ∀ (ω : M) (u : U), BU (sU ω) u = BM ω (sDU u))
    (H4 : ∀ ω : M, BM ω (sDU (d ω - sU ω)) = 0) (ω : M) :
    BU (sU ω) (sU ω) ≤ BU (d ω) (d ω) := by
  have eU := bilin_sub_self BU hU (d ω) (sU ω)
  have cU : BU (sU ω) (d ω - sU ω) = BM ω (sDU (d ω - sU ω)) := H3 ω _
  have h4 := H4 ω
  have pU := hUpos (d ω - sU ω)
  linarith

/-- Coercivity of `d` and `δ` from coercivity of the symmetric parts. -/
theorem coercive_of_symmetric_coercive (BA : LinearMap.BilinForm ℝ A)
    (BM : LinearMap.BilinForm ℝ M) (BU : LinearMap.BilinForm ℝ U)
    (hA : ∀ x y, BA x y = BA y x) (hM : ∀ x y, BM x y = BM y x) (hU : ∀ x y, BU x y = BU y x)
    (hApos : ∀ x, 0 ≤ BA x x) (hUpos : ∀ x, 0 ≤ BU x x)
    (d : M → U) (dA : A → M) (δ : M → A) (sU : M → U) (sA : A → M) (sD : M → A) (sDU : U → M)
    (H1 : ∀ (a : A) (ω : M), BM (dA a) ω = BA a (δ ω))
    (H2 : ∀ (a : A) (ω : M), BM (sA a) ω = BA a (sD ω))
    (H3 : ∀ (ω : M) (u : U), BU (sU ω) u = BM ω (sDU u))
    (H4 : ∀ ω : M, BM ω (sDU (d ω - sU ω) + (dA (sD ω) - sA (sD ω))) = 0) (c : ℝ) (ω : M)
    (hc : c * BM ω ω ≤ BU (sU ω) (sU ω) + BA (sD ω) (sD ω)) :
    c * BM ω ω ≤ BU (d ω) (d ω) + BA (δ ω) (δ ω) :=
  hc.trans (symmetric_le_flat BA BM BU hA hM hU hApos hUpos d dA δ sU sA sD sDU H1 H2 H3 H4 ω)

/-- Coercivity of `d` in the lowest degree, from coercivity of `S↑`. -/
theorem coercive_bot_of_symmetric_coercive (BM : LinearMap.BilinForm ℝ M)
    (BU : LinearMap.BilinForm ℝ U)
    (hU : ∀ x y, BU x y = BU y x) (hUpos : ∀ x, 0 ≤ BU x x)
    (d : M → U) (sU : M → U) (sDU : U → M)
    (H3 : ∀ (ω : M) (u : U), BU (sU ω) u = BM ω (sDU u))
    (H4 : ∀ ω : M, BM ω (sDU (d ω - sU ω)) = 0) (c : ℝ) (ω : M)
    (hc : c * BM ω ω ≤ BU (sU ω) (sU ω)) :
    c * BM ω ω ≤ BU (d ω) (d ω) :=
  hc.trans (symmetric_le_flat_bot BM BU hU hUpos d sU sDU H3 H4 ω)

end

end TernaryPeriodPolynomials.Argument.GeneralCoercivity.Abstract
