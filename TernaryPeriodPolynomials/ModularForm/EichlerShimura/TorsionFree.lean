module

public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Data.List.Enum
public import Mathlib.Data.String.Defs
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
public import Mathlib.LinearAlgebra.Matrix.Integer
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup
public import Mathlib.Topology.WithTopology

@[expose] public section


/-!
# `Γ(N)`, `N ≥ 3`, acts freely on the upper half plane

`free_action`: a nontrivial element of the principal congruence subgroup `Γ(N)`, `N ≥ 3`, has no
fixed point in `ℍ`; `neg_one_not_mem_Gamma`: `-1 ∉ Γ(N)`. A fixed point forces either a
diagonal element `±1` or `(a + d)² < 4`, and the congruences `a ≡ d ≡ 1 (mod N)` exclude both.

Written by Claude Opus 5.5.
-/

open UpperHalfPlane ModularGroup CongruenceSubgroup
open scoped MatrixGroups

namespace TernaryPeriodPolynomials.Argument.ESFoundations

private theorem dvd_sub_one_of_cast_eq_one {N : ℕ} {a : ℤ} (h : (a : ZMod N) = 1) :
    (N : ℤ) ∣ a - 1 := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [h, sub_self]

private theorem trace_bound {a b c d N : ℤ} (hN : 3 ≤ N) (ha : N ∣ a - 1) (hb : N ∣ b)
    (hc : N ∣ c) (hd : N ∣ d - 1) (hdet : a * d - b * c = 1) (htr : (a + d) ^ 2 ≤ 3) : False := by
  obtain ⟨s, hs⟩ := ha
  obtain ⟨u, hu⟩ := hb
  obtain ⟨v, hv⟩ := hc
  obtain ⟨t, ht⟩ := hd
  have hsum : a + d - 2 = N * (s + t) := by rw [mul_add, ← hs, ← ht]; ring
  have h1 : -3 ≤ a + d - 2 ∧ a + d - 2 ≤ -1 := by
    constructor <;> nlinarith [sq_nonneg (a + d + 2), sq_nonneg (a + d - 2)]
  have hst : s + t = -1 := by
    rcases le_or_gt (s + t) (-2) with h | h
    · nlinarith
    · rcases le_or_gt 0 (s + t) with h' | h'
      · nlinarith
      · omega
  have hN3 : N = 3 := by nlinarith
  subst hN3
  have ha' : a = 1 + 3 * s := by linarith
  have hd' : d = 1 + 3 * t := by linarith
  rw [ha', hd', hu, hv] at hdet
  have : 3 * (s + t) + 9 * (s * t - u * v) = 0 := by linarith [hdet]
  omega

private theorem fixed_eqs (g : SL(2, ℤ)) (z : ℍ) (h : g • z = z) :
    ((g 0 0 : ℤ) : ℝ) * (z : ℂ).re + ((g 0 1 : ℤ) : ℝ) =
        (z : ℂ).re * (((g 1 0 : ℤ) : ℝ) * (z : ℂ).re + ((g 1 1 : ℤ) : ℝ)) -
          (z : ℂ).im * (((g 1 0 : ℤ) : ℝ) * (z : ℂ).im) ∧
      2 * ((g 1 0 : ℤ) : ℝ) * (z : ℂ).re + ((g 1 1 : ℤ) : ℝ) - ((g 0 0 : ℤ) : ℝ) = 0 := by
  have hz : ((g • z : ℍ) : ℂ) = z := by rw [h]
  rw [UpperHalfPlane.specialLinearGroup_apply] at hz
  simp only [algebraMap_int_eq, eq_intCast, Complex.ofReal_intCast] at hz
  have hne : ((g 1 0 : ℤ) : ℂ) * z + ((g 1 1 : ℤ) : ℂ) ≠ 0 := by
    have := UpperHalfPlane.denom_ne_zero g z
    rw [ModularGroup.denom_apply] at this
    exact_mod_cast this
  rw [div_eq_iff hne] at hz
  have hre := congrArg Complex.re hz
  have him := congrArg Complex.im hz
  simp only [Complex.add_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im, Complex.add_im,
    Complex.mul_im, zero_mul, sub_zero, add_zero] at hre him
  refine ⟨hre, ?_⟩
  have hy : (z : ℂ).im ≠ 0 := z.im_pos.ne'
  have : (2 * ((g 1 0 : ℤ) : ℝ) * (z : ℂ).re + ((g 1 1 : ℤ) : ℝ) - ((g 0 0 : ℤ) : ℝ)) *
      (z : ℂ).im = 0 := by linear_combination -him
  exact (mul_eq_zero.mp this).resolve_right hy

private theorem fixed_trace (g : SL(2, ℤ)) (z : ℍ) (h : g • z = z) (hc : g 1 0 ≠ 0) :
    (g 0 0 + g 1 1) ^ 2 ≤ 3 := by
  obtain ⟨hre, hx2⟩ := fixed_eqs g z h
  set a : ℝ := ((g 0 0 : ℤ) : ℝ)
  set b : ℝ := ((g 0 1 : ℤ) : ℝ)
  set c : ℝ := ((g 1 0 : ℤ) : ℝ)
  set d : ℝ := ((g 1 1 : ℤ) : ℝ)
  have hdet : a * d - b * c = 1 := by
    have := g.2
    rw [Matrix.det_fin_two] at this
    simp only [a, b, c, d]
    exact_mod_cast this
  have key : 4 * c ^ 2 * (z : ℂ).im ^ 2 = 4 - (a + d) ^ 2 := by
    linear_combination (4 * c) * hre + (2 * c * (z : ℂ).re - a + d) * hx2 + 4 * hdet
  have hc' : c ≠ 0 := by simp only [c]; exact_mod_cast hc
  have hpos : 0 < 4 * c ^ 2 * (z : ℂ).im ^ 2 := by
    have : 0 < (z : ℂ).im := z.im_pos
    positivity
  have h' : (((g 0 0 + g 1 1 : ℤ) : ℝ)) ^ 2 < 4 := by push_cast; linarith
  have h'' : (g 0 0 + g 1 1) ^ 2 < 4 := by exact_mod_cast h'
  omega

/-- `-1 ∉ Γ(N)` for `N ≥ 3`. -/
theorem neg_one_not_mem_Gamma {N : ℕ} (hN : 3 ≤ N) : (-1 : SL(2, ℤ)) ∉ Gamma N := by
  intro h
  rw [Gamma_mem] at h
  have h1 := dvd_sub_one_of_cast_eq_one h.1
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
    Matrix.neg_apply, Matrix.one_apply_eq] at h1
  have h2 : (N : ℤ) ≤ 2 := Int.le_of_dvd (by norm_num) (by simpa using h1)
  omega

/-- A nontrivial element of `Γ(N)`, `N ≥ 3`, has no fixed point in the upper half plane. -/
theorem free_action (N : ℕ) (hN : 3 ≤ N) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma N) (h1 : γ ≠ 1)
    (z : ℍ) : γ • z ≠ z := by
  intro hfix
  rw [Gamma_mem] at hγ
  obtain ⟨ha, hb, hc, hd⟩ := hγ
  have ha' := dvd_sub_one_of_cast_eq_one ha
  have hd' := dvd_sub_one_of_cast_eq_one hd
  have hb' : (N : ℤ) ∣ γ 0 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp hb
  have hc' : (N : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp hc
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.2
    rw [Matrix.det_fin_two] at this
    exact this
  have hN' : (3 : ℤ) ≤ N := by exact_mod_cast hN
  by_cases hc0 : γ 1 0 = 0
  · obtain ⟨hre, hx2⟩ := fixed_eqs γ z hfix
    rw [hc0] at hre hx2 hdet
    simp only [Int.cast_zero, zero_mul, mul_zero, zero_add, sub_zero, mul_zero] at hre hx2 hdet
    have had : γ 0 0 = γ 1 1 := by
      have : ((γ 1 1 : ℤ) : ℝ) = ((γ 0 0 : ℤ) : ℝ) := by linarith
      exact_mod_cast this.symm
    have hb0 : γ 0 1 = 0 := by
      have : ((γ 0 1 : ℤ) : ℝ) = 0 := by rw [had] at hre; linarith
      exact_mod_cast this
    rw [had] at hdet ha'
    have hsq : γ 1 1 * γ 1 1 = 1 := hdet
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hsq with ⟨h11, -⟩ | ⟨h11, -⟩
    · apply h1
      ext i j
      fin_cases i <;> fin_cases j <;> simp [had, hb0, hc0, h11]
    · rw [h11] at ha'
      have h2 : (N : ℤ) ≤ 2 := Int.le_of_dvd (by norm_num) (by simpa using ha')
      omega
  · exact trace_bound hN' ha' hb' hc' hd' hdet (fixed_trace γ z hfix hc0)

/-- `Γ(N)`, `N ≥ 3`, acts freely on `ℍ`. -/
theorem free_gamma (N : ℕ) (hN : 3 ≤ N) :
    ∀ γ ∈ Gamma N, γ ≠ 1 → ∀ z : ℍ, γ • z ≠ z :=
  fun _ hγ h1 z => free_action N hN hγ h1 z

end TernaryPeriodPolynomials.Argument.ESFoundations
