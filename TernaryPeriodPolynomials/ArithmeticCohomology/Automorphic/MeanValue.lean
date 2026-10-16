module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
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
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Analysis.Real.Cardinality
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
# Weight projection of translates of a lifted holomorphic function

For a real `2 × 2` matrix `g = !![a, b; c, d]` with positive determinant and `w` in the upper
half plane, write `j g w = c * w + d` and `g • w = (a * w + b) / (c * w + d)`. For a weight
`k : ℕ` and a function `F` holomorphic on the upper half plane, the lift
`Φ_F(x) = (det x)^(k/2) * j(x, i)^(-k) * F(x • i)` transforms under the rotation `r_θ` by
`Φ_F(x r_θ) = e^(-ikθ) Φ_F(x)`, and its `k`-th Fourier projection along the rotations satisfies

`(2π)⁻¹ ∫₀^{2π} e^(ikθ) Φ_F(x r_θ g) dθ = ψ_k(g) Φ_F(x)`,

with `ψ_k(g) = (det g)^(k/2) (2i)^k / (b - c + i(a + d))^k`. The proof passes to the disc by the
Cayley transform, on which the rotations act by `ζ ↦ e^(-2iθ) ζ`, and applies the mean value
property of holomorphic functions.
-/

open Complex MeasureTheory intervalIntegral Metric Real

namespace TernaryPeriodPolynomials.Automorphic.MeanValue

/-- The automorphy factor `j(g, w) = c w + d` of `g = !![a, b; c, d]`. -/
def j (g : Matrix (Fin 2) (Fin 2) ℝ) (w : ℂ) : ℂ := (g 1 0 : ℂ) * w + g 1 1

/-- The Möbius action `g • w = (a w + b) / (c w + d)` of `g = !![a, b; c, d]`. -/
noncomputable def mob (g : Matrix (Fin 2) (Fin 2) ℝ) (w : ℂ) : ℂ :=
  ((g 0 0 : ℂ) * w + g 0 1) / j g w

/-- The rotation matrix `r_θ = !![cos θ, -sin θ; sin θ, cos θ]`. -/
noncomputable def rot (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]

/-- The weight `k` lift `Φ_F(x) = (det x)^(k/2) j(x, i)^(-k) F(x • i)` of `F`. -/
noncomputable def Φ (k : ℕ) (F : ℂ → ℂ) (x : Matrix (Fin 2) (Fin 2) ℝ) : ℂ :=
  ((x.det ^ ((k : ℝ) / 2) : ℝ) : ℂ) * (j x I ^ k)⁻¹ * F (mob x I)

/-- The eigenvalue `ψ_k(g) = (det g)^(k/2) (2i)^k / (b - c + i(a + d))^k` of the weight `k`
projection of the translate by `g = !![a, b; c, d]`. -/
noncomputable def ψ (k : ℕ) (g : Matrix (Fin 2) (Fin 2) ℝ) : ℂ :=
  ((g.det ^ ((k : ℝ) / 2) : ℝ) : ℂ) * (2 * I) ^ k /
    (((g 0 1 : ℂ) - g 1 0) + I * ((g 0 0 : ℂ) + g 1 1)) ^ k

/-- The upper half plane as a subset of `ℂ`. -/
def H : Set ℂ := {z | 0 < z.im}

lemma det_fin_two' (g : Matrix (Fin 2) (Fin 2) ℝ) : g.det = g 0 0 * g 1 1 - g 0 1 * g 1 0 :=
  Matrix.det_fin_two g

lemma j_ne_zero {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : 0 < g.det) {w : ℂ} (hw : 0 < w.im) :
    j g w ≠ 0 := by
  intro h
  have him : g 1 0 * w.im = 0 := by simpa [j] using congrArg Complex.im h
  have hre : g 1 0 * w.re + g 1 1 = 0 := by simpa [j] using congrArg Complex.re h
  have h1 : g 1 0 = 0 := by
    rcases mul_eq_zero.1 him with h1 | h1
    · exact h1
    · linarith
  have h2 : g 1 1 = 0 := by simpa [h1] using hre
  rw [det_fin_two', h1, h2] at hg
  simp at hg

lemma im_mob {g : Matrix (Fin 2) (Fin 2) ℝ} (w : ℂ) (hj : j g w ≠ 0) :
    (mob g w).im = g.det * w.im / normSq (j g w) := by
  have hn : normSq (j g w) ≠ 0 := by simpa using hj
  rw [mob, Complex.div_im, det_fin_two']
  field_simp
  simp [j]
  ring

lemma mob_mem {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : 0 < g.det) {w : ℂ} (hw : 0 < w.im) :
    0 < (mob g w).im := by
  rw [im_mob w (j_ne_zero hg hw)]
  have := normSq_pos.2 (j_ne_zero hg hw)
  positivity

lemma j_mul (x h : Matrix (Fin 2) (Fin 2) ℝ) (w : ℂ) (hj : j h w ≠ 0) :
    j (x * h) w = j x (mob h w) * j h w := by
  rw [mob]
  simp only [j, Matrix.mul_apply, Fin.sum_univ_two] at hj ⊢
  push_cast
  field_simp
  ring

lemma mob_mul (x h : Matrix (Fin 2) (Fin 2) ℝ) (w : ℂ) (hj : j h w ≠ 0) : mob (x * h) w = mob x (mob h w) := by
  have hnum : ((x * h) 0 0 : ℂ) * w + (x * h) 0 1 = ((x 0 0 : ℂ) * mob h w + x 0 1) * j h w := by
    rw [mob]
    simp only [j, Matrix.mul_apply, Fin.sum_univ_two] at hj ⊢
    push_cast
    field_simp
    ring
  rw [mob, hnum, j_mul x h w hj, mul_div_mul_right _ _ hj]
  rfl

/-! ### Rotations -/

lemma det_rot (θ : ℝ) : (rot θ).det = 1 := by
  rw [rot, Matrix.det_fin_two_of]
  linear_combination Real.cos_sq_add_sin_sq θ

lemma j_rot (θ : ℝ) (w : ℂ) : j (rot θ) w = Complex.sin θ * w + Complex.cos θ := by
  simp [j, rot]

lemma num_rot (θ : ℝ) (w : ℂ) :
    ((rot θ 0 0 : ℂ) * w + rot θ 0 1) = Complex.cos θ * w - Complex.sin θ := by
  simp [rot, sub_eq_add_neg]

lemma j_rot_ne_zero (θ : ℝ) {w : ℂ} (hw : 0 < w.im) : j (rot θ) w ≠ 0 :=
  j_ne_zero (by rw [det_rot]; exact one_pos) hw

lemma j_rot_I (θ : ℝ) : j (rot θ) I = cexp (θ * I) := by
  rw [j_rot, Complex.exp_mul_I]
  ring

lemma mob_rot_I (θ : ℝ) : mob (rot θ) I = I := by
  have hj : j (rot θ) I ≠ 0 := by rw [j_rot_I]; exact Complex.exp_ne_zero _
  rw [mob, div_eq_iff hj, num_rot, j_rot]
  linear_combination (-Complex.sin θ) * I_sq

/-- `j(r_θ, w) (r_θ • w + i) = e^(iθ) (w + i)`. -/
lemma j_rot_mul_add_I (θ : ℝ) {w : ℂ} (hj : j (rot θ) w ≠ 0) :
    j (rot θ) w * (mob (rot θ) w + I) = cexp (θ * I) * (w + I) := by
  rw [mul_add, mob, mul_div_cancel₀ _ hj, num_rot, j_rot, Complex.exp_mul_I]
  linear_combination (-Complex.sin θ) * I_sq

/-- `e^(iθ) j(r_θ, w) (r_θ • w - i) = w - i`. -/
lemma exp_mul_j_rot_mul_sub_I (θ : ℝ) {w : ℂ} (hj : j (rot θ) w ≠ 0) :
    cexp (θ * I) * (j (rot θ) w * (mob (rot θ) w - I)) = w - I := by
  rw [mul_sub, mob, mul_div_cancel₀ _ hj, num_rot, j_rot, Complex.exp_mul_I]
  linear_combination (w - I) * Complex.cos_sq_add_sin_sq (θ : ℂ) +
    (-(Complex.sin θ ^ 2 * w + Complex.cos θ * Complex.sin θ)) * I_sq

/-- The lift `Φ_F` transforms by `e^(-ikθ)` under right translation by the rotation `r_θ`. -/
theorem Φ_mul_rot (k : ℕ) (F : ℂ → ℂ) (x : Matrix (Fin 2) (Fin 2) ℝ) (θ : ℝ) :
    Φ k F (x * rot θ) = cexp (-(k * θ * I)) * Φ k F x := by
  have hj : j (rot θ) I ≠ 0 := by rw [j_rot_I]; exact Complex.exp_ne_zero _
  rw [Φ, Φ, Matrix.det_mul, det_rot, mul_one, j_mul _ _ _ hj, mob_mul _ _ _ hj, mob_rot_I,
    j_rot_I, show -((k : ℂ) * θ * I) = -(k * (θ * I)) by ring, Complex.exp_neg,
    Complex.exp_nat_mul, mul_pow, mul_inv]
  ring

/-! ### The Cayley transform -/

/-- The Cayley transform `w ↦ (w - i) / (w + i)` from the upper half plane to the unit disc. -/
noncomputable def cay (w : ℂ) : ℂ := (w - I) / (w + I)

/-- The inverse Cayley transform `ζ ↦ i (1 + ζ) / (1 - ζ)` from the unit disc to the upper half
plane. -/
noncomputable def icay (ζ : ℂ) : ℂ := I * (1 + ζ) / (1 - ζ)

lemma add_I_ne_zero {w : ℂ} (hw : 0 < w.im) : w + I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  linarith

lemma icay_cay {w : ℂ} (hw : w + I ≠ 0) : icay (cay w) = w := by
  have h1 : 1 - cay w = 2 * I / (w + I) := by
    rw [cay, eq_div_iff hw]
    field_simp
    ring
  have h2 : 1 + cay w = 2 * w / (w + I) := by
    rw [cay, eq_div_iff hw]
    field_simp
    ring
  rw [icay, h1, h2]
  field_simp

lemma icay_zero : icay 0 = I := by simp [icay]

lemma norm_cay_lt_one {w : ℂ} (hw : 0 < w.im) : ‖cay w‖ < 1 := by
  rw [cay, norm_div, div_lt_one (norm_pos_iff.2 (add_I_ne_zero hw))]
  refine lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) ?_
  rw [Complex.sq_norm, Complex.sq_norm, normSq_apply, normSq_apply]
  simp
  nlinarith

lemma one_sub_ne_zero {ζ : ℂ} (hζ : ‖ζ‖ < 1) : 1 - ζ ≠ 0 := by
  intro h
  rw [← sub_eq_zero.1 h, norm_one] at hζ
  exact lt_irrefl _ hζ

lemma icay_mem {ζ : ℂ} (hζ : ‖ζ‖ < 1) : 0 < (icay ζ).im := by
  have hn : normSq (1 - ζ) ≠ 0 := by simpa using one_sub_ne_zero hζ
  have hpos : 0 < normSq (1 - ζ) := lt_of_le_of_ne (normSq_nonneg _) (Ne.symm hn)
  have h1 : ζ.re ^ 2 + ζ.im ^ 2 < 1 := by
    have := pow_lt_one₀ (norm_nonneg ζ) hζ (two_ne_zero)
    rwa [Complex.sq_norm, normSq_apply, ← sq, ← sq] at this
  have : (icay ζ).im = (1 - ζ.re ^ 2 - ζ.im ^ 2) / normSq (1 - ζ) := by
    rw [icay, Complex.div_im]
    field_simp
    simp
    ring
  rw [this]
  apply div_pos (by linarith) hpos

lemma differentiableOn_icay : DifferentiableOn ℂ icay (ball 0 1) := by
  refine ((differentiableOn_const _).mul ((differentiableOn_const _).add differentiableOn_id)).div
    ((differentiableOn_const _).sub differentiableOn_id) fun ζ hζ => ?_
  exact one_sub_ne_zero (by simpa using hζ)

/-- The rotation `r_θ` acts on the Cayley coordinate by `ζ ↦ e^(-2iθ) ζ`. -/
lemma cay_mob_rot (θ : ℝ) {w : ℂ} (hw : 0 < w.im) :
    cay (mob (rot θ) w) = (cexp (θ * I))⁻¹ ^ 2 * cay w := by
  have hj := j_rot_ne_zero θ hw
  have he := Complex.exp_ne_zero (θ * I)
  have hp : mob (rot θ) w + I = cexp (θ * I) * (w + I) / j (rot θ) w := by
    rw [eq_div_iff hj, mul_comm, j_rot_mul_add_I θ hj]
  have hm : mob (rot θ) w - I = (w - I) / (cexp (θ * I) * j (rot θ) w) := by
    rw [eq_div_iff (mul_ne_zero he hj), ← exp_mul_j_rot_mul_sub_I θ hj]
    ring
  rw [cay, hp, hm, cay]
  field_simp

/-! ### The holomorphic function attached to `x` -/

/-- The function `G_x(w) = (det x)^(k/2) j(x, w)^(-k) F(x • w)` on the upper half plane, so
that `Φ_F(x) = G_x(i)`. -/
noncomputable def G (k : ℕ) (F : ℂ → ℂ) (x : Matrix (Fin 2) (Fin 2) ℝ) (w : ℂ) : ℂ :=
  ((x.det ^ ((k : ℝ) / 2) : ℝ) : ℂ) * (j x w ^ k)⁻¹ * F (mob x w)

lemma Φ_eq_G (k : ℕ) (F : ℂ → ℂ) (x : Matrix (Fin 2) (Fin 2) ℝ) : Φ k F x = G k F x I := rfl

lemma Φ_mul (k : ℕ) (F : ℂ → ℂ) {x h : Matrix (Fin 2) (Fin 2) ℝ} (hx : 0 ≤ x.det)
    (hh : 0 ≤ h.det) (hj : j h I ≠ 0) :
    Φ k F (x * h) =
      ((h.det ^ ((k : ℝ) / 2) : ℝ) : ℂ) * (j h I ^ k)⁻¹ * G k F x (mob h I) := by
  rw [Φ, G, Matrix.det_mul, Real.mul_rpow hx hh, j_mul _ _ _ hj, mob_mul _ _ _ hj, mul_pow,
    mul_inv]
  push_cast
  ring

lemma differentiableOn_j (g : Matrix (Fin 2) (Fin 2) ℝ) (s : Set ℂ) :
    DifferentiableOn ℂ (j g) s :=
  ((differentiableOn_const _).mul differentiableOn_id).add (differentiableOn_const _)

lemma differentiableOn_mob {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : 0 < g.det) :
    DifferentiableOn ℂ (mob g) H :=
  (((differentiableOn_const _).mul differentiableOn_id).add (differentiableOn_const _)).div
    (differentiableOn_j g H) fun _ hw => j_ne_zero hg hw

lemma differentiableOn_G (k : ℕ) {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F H)
    {x : Matrix (Fin 2) (Fin 2) ℝ} (hx : 0 < x.det) : DifferentiableOn ℂ (G k F x) H :=
  ((differentiableOn_const _).mul (((differentiableOn_j x H).pow k).inv
    fun _ hw => pow_ne_zero _ (j_ne_zero hx hw))).mul
    (hF.comp (differentiableOn_mob hx) fun _ hw => mob_mem hx hw)

/-! ### The mean value property along the rotations -/

/-- A holomorphic function on the unit disc, averaged over the orbit `θ ↦ e^(-2iθ) ζ₀` of a
point `ζ₀` of the disc, gives its value at the centre. -/
theorem integral_exp_sq_mul_eq {v : ℂ → ℂ} (hv : DifferentiableOn ℂ v (ball 0 1)) {ζ₀ : ℂ}
    (hζ₀ : ‖ζ₀‖ < 1) :
    ∫ θ in (0 : ℝ)..2 * π, v ((cexp (θ * I))⁻¹ ^ 2 * ζ₀) = 2 * π * v 0 := by
  set f : ℂ → ℂ := fun z => v (z ^ 2 * ζ₀) with hf
  have hfd : DifferentiableOn ℂ f (closedBall 0 1) := by
    refine hv.comp ((differentiableOn_id.pow 2).mul (differentiableOn_const _)) fun z hz => ?_
    rw [mem_closedBall, dist_zero_right] at hz
    rw [mem_ball, dist_zero_right, norm_mul, norm_pow]
    calc ‖z‖ ^ 2 * ‖ζ₀‖ ≤ 1 * ‖ζ₀‖ := by
          gcongr
          exact pow_le_one₀ (norm_nonneg _) hz
      _ < 1 := by rwa [one_mul]
  have hC := hfd.circleIntegral_sub_inv_smul (mem_ball_self one_pos)
  have hint : (∮ z in C(0, 1), (z - 0)⁻¹ • f z) =
      I * ∫ θ in (0 : ℝ)..2 * π, f (cexp (θ * I)) := by
    rw [circleIntegral, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [deriv_circleMap, circleMap_zero, sub_zero, ofReal_one, one_mul, smul_eq_mul]
    field_simp [Complex.exp_ne_zero]
  have hmean : ∫ θ in (0 : ℝ)..2 * π, f (cexp (θ * I)) = 2 * π * f 0 := by
    rw [hint, smul_eq_mul] at hC
    have := I_ne_zero
    apply mul_left_cancel₀ this
    rw [hC]
    ring
  have hsub := intervalIntegral.integral_comp_sub_left
    (fun θ : ℝ => v ((cexp (θ * I))⁻¹ ^ 2 * ζ₀)) (a := 0) (b := 2 * π) (2 * π)
  simp only [sub_self, sub_zero] at hsub
  rw [← hsub]
  have hrw : ∀ θ : ℝ, (cexp (((2 * π - θ : ℝ) : ℂ) * I))⁻¹ = cexp (θ * I) := by
    intro θ
    rw [← Complex.exp_neg, show -(((2 * π - θ : ℝ) : ℂ) * I) = θ * I - 2 * π * I by
      push_cast; ring, Complex.exp_sub, Complex.exp_two_pi_mul_I, div_one]
  simp only [hrw]
  simpa [hf] using hmean

/-! ### The weight projection -/

lemma j_mul_mob_add_I {g : Matrix (Fin 2) (Fin 2) ℝ} (hj : j g I ≠ 0) :
    j g I * (mob g I + I) = ((g 0 1 : ℂ) - g 1 0) + I * ((g 0 0 : ℂ) + g 1 1) := by
  rw [mul_add, mob, mul_div_cancel₀ _ hj, j]
  linear_combination (g 1 0 : ℂ) * I_sq

/-- **Weight projection of translates.** For `x, g` of positive determinant and `F` holomorphic
on the upper half plane, the `k`-th Fourier coefficient along the rotations of the translate
`θ ↦ Φ_F(x r_θ g)` is `ψ_k(g) Φ_F(x)`. -/
theorem weight_projection (k : ℕ) {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F {z | 0 < z.im})
    {x g : Matrix (Fin 2) (Fin 2) ℝ} (hx : 0 < x.det) (hg : 0 < g.det) :
    (1 / (2 * π) : ℂ) * ∫ θ in (0 : ℝ)..2 * π, cexp (k * θ * I) * Φ k F (x * rot θ * g) =
      ψ k g * Φ k F x := by
  set w₀ := mob g I with hw₀def
  have hI : (0 : ℝ) < I.im := by simp
  have hw₀ : 0 < w₀.im := mob_mem hg hI
  have hjg : j g I ≠ 0 := j_ne_zero hg hI
  have hw₀I : w₀ + I ≠ 0 := add_I_ne_zero hw₀
  set u : ℂ → ℂ := fun w => G k F x w * (w + I) ^ k with hu
  set v : ℂ → ℂ := fun ζ => u (icay ζ) with hv
  have hvd : DifferentiableOn ℂ v (ball 0 1) := by
    refine (((differentiableOn_G k hF hx).mul ((differentiableOn_id.add
      (differentiableOn_const _)).pow k)).comp differentiableOn_icay fun ζ hζ => ?_)
    exact icay_mem (by simpa using hζ)
  set C : ℂ := ((g.det ^ ((k : ℝ) / 2) : ℝ) : ℂ) * (j g I ^ k)⁻¹ * ((w₀ + I) ^ k)⁻¹ with hC
  have hpt : ∀ θ : ℝ, cexp (k * θ * I) * Φ k F (x * rot θ * g) =
      C * v ((cexp (θ * I))⁻¹ ^ 2 * cay w₀) := by
    intro θ
    have hjr : j (rot θ) w₀ ≠ 0 := j_rot_ne_zero θ hw₀
    have hj1 : j (rot θ * g) I ≠ 0 := by
      rw [j_mul _ _ _ hjg]
      exact mul_ne_zero hjr hjg
    have hw₁ : 0 < (mob (rot θ) w₀).im := mob_mem (by rw [det_rot]; exact one_pos) hw₀
    have he := Complex.exp_ne_zero (θ * I)
    have hrel := j_rot_mul_add_I θ hjr
    have hvu : v ((cexp (θ * I))⁻¹ ^ 2 * cay w₀) =
        G k F x (mob (rot θ) w₀) * (mob (rot θ) w₀ + I) ^ k := by
      rw [← cay_mob_rot θ hw₀]
      simp only [hv, hu]
      rw [icay_cay (add_I_ne_zero hw₁)]
    have hw₁I : mob (rot θ) w₀ + I = cexp (θ * I) * (w₀ + I) / j (rot θ) w₀ := by
      rw [eq_div_iff hjr, mul_comm, hrel]
    rw [hvu, Matrix.mul_assoc, Φ_mul k F hx.le
      (by rw [Matrix.det_mul, det_rot, one_mul]; exact hg.le) hj1, Matrix.det_mul, det_rot,
      one_mul, j_mul _ _ _ hjg, mob_mul _ _ _ hjg, ← hw₀def, hC,
      show (k : ℂ) * θ * I = k * (θ * I) by ring, Complex.exp_nat_mul, hw₁I, div_pow, mul_pow,
      mul_pow]
    field_simp
  rw [intervalIntegral.integral_congr fun θ _ => hpt θ, intervalIntegral.integral_const_mul,
    integral_exp_sq_mul_eq hvd (norm_cay_lt_one hw₀)]
  have hv0 : v 0 = Φ k F x * (2 * I) ^ k := by
    rw [hv, hu]
    simp only
    rw [icay_zero, Φ_eq_G]
    ring
  rw [hv0, ψ, ← j_mul_mob_add_I hjg, ← hw₀def, hC]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  field_simp
  rw [mul_pow]
  ring

end TernaryPeriodPolynomials.Automorphic.MeanValue
