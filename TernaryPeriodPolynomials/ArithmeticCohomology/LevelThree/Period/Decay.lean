module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Algebra.Field.Periodic
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Algebra.Algebra.TransferInstance
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Card
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Monoid.Canonical.Basic
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Analysis.Calculus.Deriv.AffineMap
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Data.List.Enum
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Data.Nat.NthRoot.Defs
public import Mathlib.Data.String.Defs
public import Mathlib.GroupTheory.QuotientGroup.ModEq
public import Mathlib.Lean.Elab.InfoTree
public import Mathlib.Lean.Elab.Tactic.Basic
public import Mathlib.Lean.Elab.Tactic.Meta
public import Mathlib.Lean.Expr.ExtraRecognizers
public import Mathlib.Lean.Expr.Rat
public import Mathlib.Lean.GoalsLocation
public import Mathlib.Lean.MessageData.Trace
public import Mathlib.Lean.Meta
public import Mathlib.Lean.Meta.Basic
public import Mathlib.Lean.Meta.KAbstractPositions
public import Mathlib.Lean.Meta.Tactic.Rewrite
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.SetTheory.Cardinal.ENNReal
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Topology.Algebra.IsUniformGroup.Order
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.WithTopology

@[expose] public section


/-!
# Decay of the Taylor coordinates of a periodic Eichler integral

Let `a_0, a_1, …, a_m` be holomorphic functions on the upper half-plane, `c`-periodic,
satisfying the Bol recursion
`a_i' = (i + 1) a_{i+1} + [i = m] F` (with `a_{m+1} = 0`),
where `F` decays like `e^{-κ y}` as `y = Im z → ∞`. Then:

* `step_bound`: if `h' = n g` for a periodic `h` and `g' = d` is bounded by `B e^{-κ y}`, then
  `g` is bounded by `c B e^{-κ y}`. The point is that the horizontal mean of `g` over one period is
  `(h(x + c) - h(x))/n = 0`, while `g` varies over a period by at most `c ‖g'‖`;
* `vertical_bound`: a periodic holomorphic function whose derivative decays exponentially is bounded
  near `i∞` (compactness of one period at one height, plus the fencing theorem vertically);
* `bounded_zero`: consequently `a_0` is bounded near `i∞` (`a_i = O(e^{-κ y})` for `i ≥ 1`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open MeasureTheory Set Filter

namespace TernaryPeriodPolynomials.LevelThree.LevelThreePeriodDecay

theorem line_im (x y : ℝ) : ((x : ℂ) + y * Complex.I).im = y := by simp

theorem hasDerivAt_line {g d : ℂ → ℂ} (hd : ∀ z : ℂ, 0 < z.im → HasDerivAt g (d z) z)
    (y : ℝ) (hy : 0 < y) (x : ℝ) :
    HasDerivAt (fun t : ℝ => g ((t : ℂ) + y * Complex.I)) (d ((x : ℂ) + y * Complex.I)) x := by
  have hpos : 0 < ((x : ℂ) + y * Complex.I).im := by rw [line_im]; exact hy
  exact ((hd _ hpos).comp_add_const (x : ℂ) (y * Complex.I)).comp_ofReal

theorem hasDerivAt_vertical {g d : ℂ → ℂ} (hd : ∀ z : ℂ, 0 < z.im → HasDerivAt g (d z) z)
    (x : ℝ) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => g ((x : ℂ) + (s : ℂ) * Complex.I))
      (Complex.I * d ((x : ℂ) + (t : ℂ) * Complex.I)) t := by
  have hpos : 0 < ((x : ℂ) + (t : ℂ) * Complex.I).im := by rw [line_im]; exact ht
  have inner : HasDerivAt (fun s : ℝ => (x : ℂ) + (s : ℂ) * Complex.I) Complex.I t := by
    have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := (hasDerivAt_id (t : ℂ)).comp_ofReal
    simpa using (h1.mul_const Complex.I).const_add (x : ℂ)
  have outer := (hd _ hpos).hasFDerivAt.restrictScalars ℝ
  have comp := outer.comp_hasDerivAt t inner
  exact comp.congr_deriv (by simp)

/-- The fundamental theorem of calculus along a horizontal line. -/
theorem horizontal_ftc {h h' : ℂ → ℂ} (hd : ∀ z : ℂ, 0 < z.im → HasDerivAt h (h' z) z)
    (hc : ContinuousOn h' {z : ℂ | 0 < z.im}) (y : ℝ) (hy : 0 < y) (x₀ x₁ : ℝ) :
    ∫ x in x₀..x₁, h' ((x : ℂ) + y * Complex.I) =
      h ((x₁ : ℂ) + y * Complex.I) - h ((x₀ : ℂ) + y * Complex.I) := by
  have himg : ∀ x : ℝ, (x : ℂ) + y * Complex.I ∈ {z : ℂ | 0 < z.im} := fun x => by
    show 0 < ((x : ℂ) + y * Complex.I).im
    rw [line_im]; exact hy
  have path : Continuous (fun x : ℝ => (x : ℂ) + y * Complex.I) := by fun_prop
  have integrable : IntervalIntegrable (fun x : ℝ => h' ((x : ℂ) + y * Complex.I)) volume x₀ x₁ :=
    (hc.comp path.continuousOn (fun x _ => himg x)).intervalIntegrable
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_line hd y hy x) integrable

/-- Horizontal Lipschitz bound from a bound on the derivative along the line. -/
theorem horizontal_lipschitz {g d : ℂ → ℂ} (hd : ∀ z : ℂ, 0 < z.im → HasDerivAt g (d z) z)
    (y : ℝ) (hy : 0 < y) (B : ℝ) (hB : ∀ x : ℝ, ‖d ((x : ℂ) + y * Complex.I)‖ ≤ B) (x x' : ℝ) :
    ‖g ((x' : ℂ) + y * Complex.I) - g ((x : ℂ) + y * Complex.I)‖ ≤ B * ‖x' - x‖ := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun t : ℝ => g ((t : ℂ) + y * Complex.I))
    (f' := fun t : ℝ => d ((t : ℂ) + y * Complex.I)) (s := Set.univ) (C := B)
    (fun t _ => (hasDerivAt_line hd y hy t).hasDerivWithinAt) (fun t _ => hB t)
    convex_univ (Set.mem_univ x) (Set.mem_univ x')
  exact h

/-- **One step of the descending induction.** -/
theorem step_bound {g h d : ℂ → ℂ} {n : ℂ} (hn : n ≠ 0) {c κ B A : ℝ} (hc : 0 < c) (hA : 0 < A)
    (hh : ∀ z : ℂ, 0 < z.im → HasDerivAt h (n * g z) z)
    (hper : ∀ z : ℂ, 0 < z.im → h (z + c) = h z)
    (hg : ∀ z : ℂ, 0 < z.im → HasDerivAt g (d z) z)
    (hd : ∀ z : ℂ, A ≤ z.im → ‖d z‖ ≤ B * Real.exp (-κ * z.im)) :
    ∀ z : ℂ, A ≤ z.im → ‖g z‖ ≤ c * B * Real.exp (-κ * z.im) := by
  intro z hz
  have hy : 0 < z.im := lt_of_lt_of_le hA hz
  have hzeq : z = (z.re : ℂ) + z.im * Complex.I := by
    apply Complex.ext <;> simp
  set x₀ : ℝ := z.re with hx₀
  set y : ℝ := z.im with hy_def
  have hgcont : ContinuousOn g {w : ℂ | 0 < w.im} := fun w hw =>
    (hg w hw).continuousAt.continuousWithinAt
  have hcont : ContinuousOn (fun w => n * g w) {w : ℂ | 0 < w.im} :=
    continuousOn_const.mul hgcont
  have himg : ∀ x : ℝ, (x : ℂ) + y * Complex.I ∈ {w : ℂ | 0 < w.im} := fun x => by
    show 0 < ((x : ℂ) + y * Complex.I).im
    rw [line_im]; exact hy
  have path : Continuous (fun x : ℝ => (x : ℂ) + y * Complex.I) := by fun_prop
  have gint : IntervalIntegrable (fun x : ℝ => g ((x : ℂ) + y * Complex.I)) volume x₀ (x₀ + c) :=
    (hgcont.comp path.continuousOn (fun x _ => himg x)).intervalIntegrable
  -- the mean of `g` over one period vanishes
  have mean : ∫ x in x₀..(x₀ + c), g ((x : ℂ) + y * Complex.I) = 0 := by
    have ftc := horizontal_ftc hh hcont y hy x₀ (x₀ + c)
    have hshift : h (((x₀ + c : ℝ) : ℂ) + y * Complex.I) = h ((x₀ : ℂ) + y * Complex.I) := by
      have h1 := hper ((x₀ : ℂ) + y * Complex.I) (by rw [line_im]; exact hy)
      rw [← h1]
      congr 1
      push_cast
      ring
    rw [hshift, sub_self, intervalIntegral.integral_const_mul] at ftc
    exact (mul_eq_zero.mp ftc).resolve_left hn
  -- the bound on the derivative along the line
  have hBnn : 0 ≤ B * Real.exp (-κ * y) := (norm_nonneg _).trans (hd z hz)
  have hline : ∀ x : ℝ, ‖d ((x : ℂ) + y * Complex.I)‖ ≤ B * Real.exp (-κ * y) := by
    intro x
    have h1 := hd ((x : ℂ) + y * Complex.I) (by rw [line_im]; exact hz)
    rwa [line_im] at h1
  have hosc : ∀ x ∈ Set.uIoc x₀ (x₀ + c),
      ‖g ((x₀ : ℂ) + y * Complex.I) - g ((x : ℂ) + y * Complex.I)‖ ≤ B * Real.exp (-κ * y) * c := by
    intro x hx
    rw [Set.uIoc_of_le (by linarith)] at hx
    rw [norm_sub_rev]
    have h1 := horizontal_lipschitz hg y hy _ hline x₀ x
    refine h1.trans ?_
    have h2 : ‖x - x₀‖ ≤ c := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [hx.1])]
      linarith [hx.2]
    exact mul_le_mul_of_nonneg_left h2 hBnn
  have hdiff := intervalIntegral.norm_integral_le_of_norm_le_const hosc
  have hintegral : ∫ x in x₀..(x₀ + c), (g ((x₀ : ℂ) + y * Complex.I) -
      g ((x : ℂ) + y * Complex.I)) = (c : ℂ) * g ((x₀ : ℂ) + y * Complex.I) := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const gint,
      intervalIntegral.integral_const, mean, sub_zero]
    simp
  rw [hintegral] at hdiff
  have hnorm : ‖(c : ℂ) * g ((x₀ : ℂ) + y * Complex.I)‖ = c * ‖g ((x₀ : ℂ) + y * Complex.I)‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
  rw [hnorm, add_sub_cancel_left, abs_of_pos hc] at hdiff
  have hfinal : ‖g ((x₀ : ℂ) + y * Complex.I)‖ ≤ B * Real.exp (-κ * y) * c := by
    by_contra hcon
    push Not at hcon
    have := mul_lt_mul_of_pos_left hcon hc
    nlinarith
  rw [hzeq]
  calc ‖g ((x₀ : ℂ) + y * Complex.I)‖ ≤ B * Real.exp (-κ * y) * c := hfinal
    _ = c * B * Real.exp (-κ * y) := by ring

/-- A periodic holomorphic function with exponentially decaying derivative is bounded. -/
theorem vertical_bound {g d : ℂ → ℂ} {c κ B A : ℝ} (hc : 0 < c) (hκ : 0 < κ) (hA : 0 < A)
    (hg : ∀ z : ℂ, 0 < z.im → HasDerivAt g (d z) z)
    (hper : ∀ z : ℂ, 0 < z.im → g (z + c) = g z)
    (hd : ∀ z : ℂ, A ≤ z.im → ‖d z‖ ≤ B * Real.exp (-κ * z.im)) :
    ∃ M : ℝ, ∀ z : ℂ, A ≤ z.im → ‖g z‖ ≤ M := by
  -- bound at height `A`
  have hAimg : ∀ x : ℝ, (x : ℂ) + A * Complex.I ∈ {w : ℂ | 0 < w.im} := fun x => by
    show 0 < ((x : ℂ) + A * Complex.I).im
    rw [line_im]; exact hA
  have gcont : ContinuousOn g {w : ℂ | 0 < w.im} := fun w hw =>
    (hg w hw).continuousAt.continuousWithinAt
  have path : Continuous (fun x : ℝ => (x : ℂ) + A * Complex.I) := by fun_prop
  have hφcont : ContinuousOn (fun x : ℝ => g ((x : ℂ) + A * Complex.I)) (Set.Icc 0 c) :=
    gcont.comp path.continuousOn (fun x _ => hAimg x)
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := c)).exists_bound_of_continuousOn hφcont
  have hφper : Function.Periodic (fun x : ℝ => g ((x : ℂ) + A * Complex.I)) c := by
    intro x
    have h1 := hper ((x : ℂ) + A * Complex.I) (by rw [line_im]; exact hA)
    change g (((x + c : ℝ) : ℂ) + A * Complex.I) = g ((x : ℂ) + A * Complex.I)
    rw [← h1]
    congr 1
    push_cast
    ring
  have hbase : ∀ x : ℝ, ‖g ((x : ℂ) + A * Complex.I)‖ ≤ M₀ := by
    intro x
    obtain ⟨x', hx', hxx'⟩ := hφper.exists_mem_Ico₀ hc x
    rw [hxx']
    exact hM₀ x' ⟨hx'.1, hx'.2.le⟩
  refine ⟨M₀ + B / κ * Real.exp (-κ * A), ?_⟩
  intro z hz
  have hzeq : z = (z.re : ℂ) + (z.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  set x : ℝ := z.re with hx
  set y : ℝ := z.im with hy
  -- the fencing theorem along the vertical segment `[A, y]`
  let ψ : ℝ → ℂ := fun s => g ((x : ℂ) + (s : ℂ) * Complex.I)
  let Bf : ℝ → ℝ := fun s => ‖ψ A‖ + B / κ * (Real.exp (-κ * A) - Real.exp (-κ * s))
  have hψ : ∀ s : ℝ, 0 < s → HasDerivAt ψ (Complex.I * d ((x : ℂ) + (s : ℂ) * Complex.I)) s :=
    fun s hs => hasDerivAt_vertical hg x s hs
  have hBf : ∀ s : ℝ, HasDerivAt Bf (B * Real.exp (-κ * s)) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => Real.exp (-κ * s)) (Real.exp (-κ * s) * (-κ)) s := by
      have := ((hasDerivAt_id s).const_mul (-κ)).exp
      simpa using this
    have h2 := (h1.const_sub (Real.exp (-κ * A))).const_mul (B / κ)
    have h3 := h2.const_add ‖ψ A‖
    have hk : κ ≠ 0 := hκ.ne'
    refine h3.congr_deriv ?_
    calc B / κ * -(Real.exp (-κ * s) * -κ) = B * Real.exp (-κ * s) * (κ / κ) := by ring
      _ = B * Real.exp (-κ * s) := by rw [div_self hk, mul_one]
  have hcontψ : ContinuousOn ψ (Set.Icc A y) := by
    intro s hs
    exact (hψ s (lt_of_lt_of_le hA hs.1)).continuousAt.continuousWithinAt
  have hfence := image_norm_le_of_norm_deriv_right_le_deriv_boundary (a := A) (b := y)
    (f := ψ) (f' := fun s => Complex.I * d ((x : ℂ) + (s : ℂ) * Complex.I)) hcontψ
    (fun s hs => (hψ s (lt_of_lt_of_le hA hs.1)).hasDerivWithinAt)
    (B := Bf) (B' := fun s => B * Real.exp (-κ * s)) (by simp [Bf]) hBf
    (fun s hs => by
      rw [norm_mul, Complex.norm_I, one_mul]
      have h1 := hd ((x : ℂ) + (s : ℂ) * Complex.I) (by rw [line_im]; exact hs.1)
      rwa [line_im] at h1)
  have hψy : ‖ψ y‖ ≤ Bf y := hfence ⟨hz, le_refl _⟩
  have hψA : ‖ψ A‖ ≤ M₀ := hbase x
  rw [hzeq]
  have hexp : 0 ≤ Real.exp (-κ * y) := (Real.exp_pos _).le
  have hBκ : 0 ≤ B / κ := by
    have h0 := (norm_nonneg _).trans (hd z hz)
    have hB : 0 ≤ B := by
      by_contra hneg
      push Not at hneg
      have hp := Real.exp_pos (-κ * z.im)
      have := mul_neg_of_neg_of_pos hneg hp
      linarith
    positivity
  calc ‖g ((x : ℂ) + (y : ℂ) * Complex.I)‖ = ‖ψ y‖ := rfl
    _ ≤ Bf y := hψy
    _ ≤ M₀ + B / κ * Real.exp (-κ * A) := by
      simp only [Bf]
      nlinarith [mul_nonneg hBκ hexp]

/-- **Descending induction.** For `1 ≤ i ≤ m + 1` the Taylor coordinate `a_i` decays like
`e^{-κ y}`. -/
theorem decay_of_bol {m : ℕ} {a : ℕ → ℂ → ℂ} {F : ℂ → ℂ} {c κ C A : ℝ} (hc : 0 < c) (hA : 0 < A)
    (hderiv : ∀ (i : ℕ) (z : ℂ), 0 < z.im →
      HasDerivAt (a i) (((i : ℂ) + 1) * a (i + 1) z + (if i = m then F z else 0)) z)
    (htop : ∀ z : ℂ, a (m + 1) z = 0)
    (hper : ∀ (i : ℕ) (z : ℂ), 0 < z.im → a i (z + c) = a i z)
    (hF : ∀ z : ℂ, A ≤ z.im → ‖F z‖ ≤ C * Real.exp (-κ * z.im)) :
    ∀ n i : ℕ, i + n = m + 1 → 1 ≤ i →
      ∃ D : ℝ, ∀ z : ℂ, A ≤ z.im → ‖a i z‖ ≤ D * Real.exp (-κ * z.im) := by
  intro n
  induction n with
  | zero =>
    intro i hi _
    refine ⟨0, fun z _ => ?_⟩
    have : i = m + 1 := by omega
    subst this
    simp [htop z]
  | succ n ih =>
    intro i hi hi1
    obtain ⟨D, hD⟩ := ih (i + 1) (by omega) (by omega)
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    have hjm : j ≠ m := by omega
    have hh : ∀ z : ℂ, 0 < z.im → HasDerivAt (a j) (((j : ℂ) + 1) * a (j + 1) z) z := by
      intro z hz
      have h1 := hderiv j z hz
      rwa [ite_eq_right hjm, add_zero] at h1
    refine ⟨c * (((j : ℝ) + 1 + 1) * D + C), ?_⟩
    have hstep := step_bound (g := a (j + 1)) (h := a j) (n := (j : ℂ) + 1)
      (d := fun z => (((j + 1 : ℕ) : ℂ) + 1) * a (j + 1 + 1) z +
        (if j + 1 = m then F z else 0))
      (by exact_mod_cast Nat.succ_ne_zero j) (c := c) (κ := κ)
      (B := ((j : ℝ) + 1 + 1) * D + C) (A := A) hc hA hh (hper j)
      (fun z hz => hderiv (j + 1) z hz) (by
        intro z hz
        have hz1 := hD z hz
        have hFz : (0 : ℝ) ≤ C * Real.exp (-κ * z.im) := (norm_nonneg _).trans (hF z hz)
        have hFb : ‖(if j + 1 = m then F z else 0)‖ ≤ C * Real.exp (-κ * z.im) := by
          by_cases hm : j + 1 = m
          · rw [ite_eq_left hm]; exact hF z hz
          · rw [ite_eq_right hm, norm_zero]; exact hFz
        calc ‖(((j + 1 : ℕ) : ℂ) + 1) * a (j + 1 + 1) z + (if j + 1 = m then F z else 0)‖
            ≤ ‖(((j + 1 : ℕ) : ℂ) + 1) * a (j + 1 + 1) z‖ +
                ‖(if j + 1 = m then F z else 0)‖ := norm_add_le _ _
          _ ≤ ((j : ℝ) + 1 + 1) * (D * Real.exp (-κ * z.im)) + C * Real.exp (-κ * z.im) := by
              refine add_le_add ?_ hFb
              rw [norm_mul]
              have hnorm : ‖(((j + 1 : ℕ) : ℂ) + 1)‖ = (j : ℝ) + 1 + 1 := by
                have : (((j + 1 : ℕ) : ℂ) + 1) = (((j : ℝ) + 1 + 1 : ℝ) : ℂ) := by push_cast; ring
                rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
              rw [hnorm]
              exact mul_le_mul_of_nonneg_left hz1 (by positivity)
          _ = (((j : ℝ) + 1 + 1) * D + C) * Real.exp (-κ * z.im) := by ring)
    intro z hz
    refine (hstep z hz).trans (le_of_eq ?_)
    ring

/-- **Boundedness of the zeroth Taylor coordinate near `i∞`.** -/
theorem bounded_zero {m : ℕ} {a : ℕ → ℂ → ℂ} {F : ℂ → ℂ} {c κ C A : ℝ} (hc : 0 < c) (hκ : 0 < κ)
    (hA : 0 < A)
    (hderiv : ∀ (i : ℕ) (z : ℂ), 0 < z.im →
      HasDerivAt (a i) (((i : ℂ) + 1) * a (i + 1) z + (if i = m then F z else 0)) z)
    (htop : ∀ z : ℂ, a (m + 1) z = 0)
    (hper : ∀ (i : ℕ) (z : ℂ), 0 < z.im → a i (z + c) = a i z)
    (hF : ∀ z : ℂ, A ≤ z.im → ‖F z‖ ≤ C * Real.exp (-κ * z.im)) :
    ∃ M : ℝ, ∀ z : ℂ, A ≤ z.im → ‖a 0 z‖ ≤ M := by
  obtain ⟨D, hD⟩ := decay_of_bol hc hA hderiv htop hper hF m 1 (by omega) (le_refl 1)
  refine vertical_bound (g := a 0)
    (d := fun z => (((0 : ℕ) : ℂ) + 1) * a (0 + 1) z + (if 0 = m then F z else 0))
    (B := D + C) hc hκ hA (fun z hz => hderiv 0 z hz) (hper 0) ?_
  intro z hz
  have hz1 := hD z hz
  have hFz : (0 : ℝ) ≤ C * Real.exp (-κ * z.im) := (norm_nonneg _).trans (hF z hz)
  have hFb : ‖(if 0 = m then F z else 0)‖ ≤ C * Real.exp (-κ * z.im) := by
    by_cases hm : 0 = m
    · rw [ite_eq_left hm]; exact hF z hz
    · rw [ite_eq_right hm, norm_zero]; exact hFz
  calc ‖(((0 : ℕ) : ℂ) + 1) * a (0 + 1) z + (if 0 = m then F z else 0)‖
      ≤ ‖(((0 : ℕ) : ℂ) + 1) * a (0 + 1) z‖ + ‖(if 0 = m then F z else 0)‖ := norm_add_le _ _
    _ ≤ D * Real.exp (-κ * z.im) + C * Real.exp (-κ * z.im) := by
        refine add_le_add ?_ hFb
        simpa using hz1
    _ = (D + C) * Real.exp (-κ * z.im) := by ring

end TernaryPeriodPolynomials.LevelThree.LevelThreePeriodDecay
