module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Period.Primitive
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Period.Taylor
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.SymFixed

@[expose] public section


/-!
# Bol's identity for vector-valued Eichler integrals

Let `Q : ℂ → Sym^m` be a (holomorphic) primitive of `f(z) (X₀ - z X₁)^m`, i.e. `Q' = f u^m` with
`u = X₀ - z X₁`. Writing `Q(z) = ∑ a_i(z) u^i X₁^{m-i}` (the *Taylor coordinates*
`a_i(z) = ∑_p q_p(z) C(p,i) z^{p-i}` of `Q(z)(w, 1)` at `w = z`), one has `Q(z)(z, 1) = a_0(z)`,
the Bol recursion `a_i' = (i + 1) a_{i+1} + [i = m] f`, and, if `Q(z + c) = Q(z)(X₀ - cX₁, X₁)`,
all `a_i` are `c`-periodic (`aN_periodic`). In particular:

* `f = 0` as soon as `a_0 = Q(·)(·, 1)` vanishes identically (`f_eq_zero_of_aN_zero`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein Matrix MvPolynomial UpperHalfPlane Filter
open scoped Manifold ModularForm Topology
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodPrimitive
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodTaylor

namespace TernaryPeriodPolynomials.LevelThree.LevelThreePeriodBol

variable (m : ℕ)

/-- The `p`-th monomial coordinate of `v ∈ Sym^m` (zero for `p > m`). -/
def coordN (v : V m) (p : ℕ) : ℂ :=
  if h : p < m + 1 then (binaryStandardBasis m).coord ⟨p, h⟩ v else 0

theorem coordN_fin (v : V m) (p : Fin (m + 1)) :
    coordN m v p.val = (binaryStandardBasis m).coord p v := by
  simp [coordN, p.isLt]

/-- Evaluation at `(w, 1)` in terms of coordinates. -/
theorem eval_eq_sum (v : V m) (w : ℂ) :
    eval ![w, 1] v.val = ∑ p ∈ Finset.range (m + 1), coordN m v p * w ^ p := by
  have hv := (binaryStandardBasis m).sum_repr v
  conv_lhs => rw [← hv]
  rw [Submodule.coe_sum, map_sum,
    ← Fin.sum_univ_eq_sum_range (fun p => coordN m v p * w ^ p) (m + 1)]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Submodule.coe_smul, MvPolynomial.smul_eval, binaryStandardBasis_coe, coordN_fin]
  simp [Module.Basis.coord_apply]

theorem eval_polyOf (v : V m) (w : ℂ) :
    (polyOf m (coordN m v)).eval w = eval ![w, 1] v.val := by
  rw [eval_eq_sum]
  simp [polyOf, Polynomial.eval_finsetSum]

/-- The monomial coordinates of the function `Q`. -/
abbrev qN (Q : ℂ → V m) (p : ℕ) (w : ℂ) : ℂ := coordN m (Q w) p

/-- The Taylor coordinates of `Q`. -/
abbrev aN (Q : ℂ → V m) (i : ℕ) (w : ℂ) : ℂ := taylorCoeff m (qN m Q) i w

theorem aN_zero (Q : ℂ → V m) (w : ℂ) : aN m Q 0 w = eval ![w, 1] (Q w).val := by
  rw [eval_eq_sum]
  simp [aN, taylorCoeff, qN]

theorem aN_top (Q : ℂ → V m) (w : ℂ) : aN m Q (m + 1) w = 0 := by
  unfold aN taylorCoeff
  apply Finset.sum_eq_zero
  intro p hp
  have : p < m + 1 := Finset.mem_range.mp hp
  rw [Nat.choose_eq_zero_of_lt (show p < m + 1 by omega)]
  simp

/-- **The Bol recursion for vector-valued primitives.** -/
theorem hasDerivAt_aN {f : ℍ → ℂ} {Q : ℂ → V m} (hQ : IsPrimitive m f Q) (i : ℕ) (z : ℂ)
    (hz : 0 < z.im) :
    HasDerivAt (aN m Q i)
      (((i : ℂ) + 1) * aN m Q (i + 1) z + (if i = m then f (ofComplex z) else 0)) z := by
  have hq : ∀ p ≤ m, HasDerivAt (qN m Q p)
      (f (ofComplex z) * ((m.choose p : ℂ) * (-z) ^ (m - p))) z := by
    intro p hp
    have hlt : p < m + 1 := Nat.lt_succ_of_le hp
    have h := hQ ((binaryStandardBasis m).coord ⟨p, hlt⟩) z hz
    have hfun : qN m Q p = fun w => (binaryStandardBasis m).coord ⟨p, hlt⟩ (Q w) := by
      funext w
      simp [qN, coordN, hlt]
    rw [hfun]
    refine h.congr_deriv ?_
    rw [pointForm, map_smul, binaryPointPower_standardCoord, smul_eq_mul]
  have h := hasDerivAt_taylorCoeff m (qN m Q) (f (ofComplex z)) z i hq
  refine h.congr_deriv ?_
  by_cases hi : i = m
  · simp [hi]
  · simp [hi]

/-- **Periodicity of the Taylor coordinates.** If `Q(z + c)(w) = Q(z)(w - c)` for all `w`, then all
Taylor coordinates are `c`-periodic. -/
theorem aN_periodic (Q : ℂ → V m) (c : ℂ) (z : ℂ)
    (hshift : ∀ s : ℂ, eval ![s, 1] (Q (z + c)).val = eval ![s - c, 1] (Q z).val) (i : ℕ) :
    aN m Q i (z + c) = aN m Q i z := by
  have key : Polynomial.taylor (z + c) (polyOf m (fun p => qN m Q p (z + c))) =
      Polynomial.taylor z (polyOf m (fun p => qN m Q p z)) := by
    apply Polynomial.funext
    intro s
    rw [Polynomial.taylor_eval, Polynomial.taylor_eval, eval_polyOf, eval_polyOf, hshift,
      show s + (z + c) - c = s + z by ring]
  unfold aN
  rw [taylorCoeff_eq_coeff_taylor, taylorCoeff_eq_coeff_taylor, key]

/-- **Bol's vanishing.** If the zeroth Taylor coordinate `Q(z)(z, 1)` vanishes identically on the
upper half-plane, then `f` vanishes identically. -/
theorem f_eq_zero_of_aN_zero {f : ℍ → ℂ} {Q : ℂ → V m} (hQ : IsPrimitive m f Q)
    (h0 : ∀ z : ℂ, 0 < z.im → aN m Q 0 z = 0) (z : ℂ) (hz : 0 < z.im) :
    f (ofComplex z) = 0 := by
  have hnhds : ∀ w : ℂ, 0 < w.im → {u : ℂ | 0 < u.im} ∈ 𝓝 w := fun w hw =>
    UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hw
  -- a vanishing coordinate has vanishing derivative
  have step : ∀ i : ℕ, (∀ w : ℂ, 0 < w.im → aN m Q i w = 0) → ∀ w : ℂ, 0 < w.im →
      ((i : ℂ) + 1) * aN m Q (i + 1) w + (if i = m then f (ofComplex w) else 0) = 0 := by
    intro i hi w hw
    have hd := hasDerivAt_aN m hQ i w hw
    have hev : aN m Q i =ᶠ[𝓝 w] fun _ => (0 : ℂ) :=
      Filter.eventually_of_mem (hnhds w hw) (fun u hu => hi u hu)
    have hd0 : HasDerivAt (aN m Q i) 0 w := (hasDerivAt_const w (0 : ℂ)).congr_of_eventuallyEq hev
    exact hd.unique hd0
  have all : ∀ i : ℕ, i ≤ m → ∀ w : ℂ, 0 < w.im → aN m Q i w = 0 := by
    intro i
    induction i with
    | zero => intro _; exact h0
    | succ i ih =>
      intro hi w hw
      have hs := step i (ih (by omega)) w hw
      have him : i ≠ m := by omega
      rw [ite_eq_right him, add_zero] at hs
      have hne : ((i : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero i
      exact (mul_eq_zero.mp hs).resolve_left hne
  have hs := step m (all m le_rfl) z hz
  rw [ite_eq_left rfl, aN_top, mul_zero, zero_add] at hs
  exact hs

end TernaryPeriodPolynomials.LevelThree.LevelThreePeriodBol
