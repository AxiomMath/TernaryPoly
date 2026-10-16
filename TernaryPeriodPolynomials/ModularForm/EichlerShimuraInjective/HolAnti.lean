module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimuraInjective.Green

@[expose] public section


/-!
# Green's formula for sums `Σ uᵢ · conj wᵢ`

For holomorphic `uᵢ, wᵢ`, `H = Σ uᵢ conj wᵢ` with `H(z+1) = H(z)` and `H(-1/z) = conj(z)² H(z)`, `∬_{F_T} ∂_z H = -(i/2) ∫ H(x + iT) dx` (`stokes_holAnti`).

Eichler-Shimura theory is used for injectivity of the seed map at level `Γ(N)`.

Formalized by Claude Sonnet 5.5.
-/

open MeasureTheory Set intervalIntegral

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EichlerShimuraInj

open scoped ComplexConjugate


open Complex


section HolAnti

variable {ι : Type} [Fintype ι] (u w du dw : ι → ℂ → ℂ)

/-- The sum `Σ uᵢ · conj wᵢ` of products of a holomorphic and an antiholomorphic function. -/
def holAnti (z : ℂ) : ℂ := ∑ i, u i z * conj (w i z)

/-- Its Wirtinger derivative `∂_z`, `Σ uᵢ' · conj wᵢ`. -/
def holAntiD (z : ℂ) : ℂ := ∑ i, du i z * conj (w i z)

theorem hasDerivAt_real_dir (c : ℂ) (x : ℝ) : HasDerivAt (fun t : ℝ => (t : ℂ) + c) 1 x := by
  simpa using ((hasDerivAt_id x).ofReal_comp).add_const c

theorem hasDerivAt_imag_dir (a : ℝ) (y : ℝ) : HasDerivAt (fun t : ℝ => (a : ℂ) + (t : ℂ) * I) I y := by
  simpa using (((hasDerivAt_id y).ofReal_comp).mul_const I).const_add (a : ℂ)

variable {u w du dw}

omit [Fintype ι] in
theorem hasDerivAt_u_real (i : ι) {z : ℂ} (hu : HasDerivAt (u i) (du i z) z) (x y : ℝ) (hz : z = (x : ℂ) + (y : ℂ) * I) :
    HasDerivAt (fun t : ℝ => u i ((t : ℂ) + (y : ℂ) * I)) (du i z) x := by
  subst hz
  have h := hu.scomp x (hasDerivAt_real_dir ((y : ℂ) * I) x)
  rw [one_smul] at h
  exact h

omit [Fintype ι] in
theorem hasDerivAt_u_imag (i : ι) {z : ℂ} (hu : HasDerivAt (u i) (du i z) z) (x y : ℝ) (hz : z = (x : ℂ) + (y : ℂ) * I) :
    HasDerivAt (fun t : ℝ => u i ((x : ℂ) + (t : ℂ) * I)) (I * du i z) y := by
  subst hz
  have h := hu.scomp y (hasDerivAt_imag_dir x y)
  rw [smul_eq_mul] at h
  exact h

theorem hasDerivAt_conj_real (f : ℝ → ℂ) {f' : ℂ} {x : ℝ} (hf : HasDerivAt f f' x) :
    HasDerivAt (fun t => conj (f t)) (conj f') x := hf.star


variable (u w du dw)

/-- The real coordinates `(x, y) ↦ x + y I`. -/
def cxPt (p : ℝ × ℝ) : ℂ := (p.1 : ℂ) + (p.2 : ℂ) * I

theorem continuous_cxPt : Continuous cxPt := by unfold cxPt; fun_prop

theorem cxPt_im (p : ℝ × ℝ) : (cxPt p).im = p.2 := by simp [cxPt]

theorem cxPt_mem {p : ℝ × ℝ} (hp : 0 < p.2) : cxPt p ∈ {z : ℂ | 0 < z.im} := by
  show 0 < (cxPt p).im
  rw [cxPt_im]; exact hp

def Fre (x y : ℝ) : ℂ := holAnti u w ((x : ℂ) + (y : ℂ) * I)

def Fxre (x y : ℝ) : ℂ := ∑ i, (du i ((x : ℂ) + (y : ℂ) * I) * conj (w i ((x : ℂ) + (y : ℂ) * I)) +
  u i ((x : ℂ) + (y : ℂ) * I) * conj (dw i ((x : ℂ) + (y : ℂ) * I)))

def Fyre (x y : ℝ) : ℂ := ∑ i, (I * du i ((x : ℂ) + (y : ℂ) * I) * conj (w i ((x : ℂ) + (y : ℂ) * I)) -
  I * (u i ((x : ℂ) + (y : ℂ) * I) * conj (dw i ((x : ℂ) + (y : ℂ) * I))))

variable {u w du dw}

theorem Fxre_sub_Fyre (x y : ℝ) :
    Fxre u w du dw x y - I * Fyre u w du dw x y = 2 * holAntiD w du ((x : ℂ) + (y : ℂ) * I) := by
  unfold Fxre Fyre holAntiD
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have : I * (I * du i ((x : ℂ) + (y : ℂ) * I) * conj (w i ((x : ℂ) + (y : ℂ) * I)) -
      I * (u i ((x : ℂ) + (y : ℂ) * I) * conj (dw i ((x : ℂ) + (y : ℂ) * I)))) =
      -(du i ((x : ℂ) + (y : ℂ) * I) * conj (w i ((x : ℂ) + (y : ℂ) * I))) +
      u i ((x : ℂ) + (y : ℂ) * I) * conj (dw i ((x : ℂ) + (y : ℂ) * I)) := by
    ring_nf; simp [Complex.I_sq]
  rw [this]; ring

end HolAnti



section HolAntiStokes

variable {ι : Type} [Fintype ι] {u w du dw : ι → ℂ → ℂ}

theorem contOn_of_deriv {f f' : ℂ → ℂ} (h : ∀ z : ℂ, 0 < z.im → HasDerivAt f (f' z) z) :
    ContinuousOn f {z : ℂ | 0 < z.im} := fun z hz => (h z hz).continuousAt.continuousWithinAt

theorem stokesData_holAnti
    (hu : ∀ i z, 0 < z.im → HasDerivAt (u i) (du i z) z)
    (hw : ∀ i z, 0 < z.im → HasDerivAt (w i) (dw i z) z)
    (hcdu : ∀ i, ContinuousOn (du i) {z : ℂ | 0 < z.im})
    (hcdw : ∀ i, ContinuousOn (dw i) {z : ℂ | 0 < z.im})
    (hper : ∀ z : ℂ, 0 < z.im → holAnti u w (z + 1) = holAnti u w z) :
    StokesData (Fre u w) (Fxre u w du dw) (Fyre u w du dw) where
  dx x y hy := by
    have hz : 0 < ((x : ℂ) + (y : ℂ) * I).im := by simpa using hy
    unfold Fre Fxre holAnti
    refine HasDerivAt.fun_sum (fun i _ => ?_)
    have h1 := hasDerivAt_u_real i (hu i _ hz) x y rfl
    have h2 := hasDerivAt_conj_real _ (hasDerivAt_u_real i (hw i _ hz) x y rfl)
    exact h1.mul h2
  dy x y hy := by
    have hz : 0 < ((x : ℂ) + (y : ℂ) * I).im := by simpa using hy
    unfold Fre holAnti
    have hs := HasDerivAt.fun_sum (u := Finset.univ) (x := y)
      (A := fun i (t : ℝ) => u i ((x : ℂ) + (t : ℂ) * I) * conj (w i ((x : ℂ) + (t : ℂ) * I)))
      (A' := fun i => (I * du i ((x : ℂ) + (y : ℂ) * I)) * conj (w i ((x : ℂ) + (y : ℂ) * I)) +
        u i ((x : ℂ) + (y : ℂ) * I) * conj (I * dw i ((x : ℂ) + (y : ℂ) * I)))
      (fun i _ => (hasDerivAt_u_imag i (hu i _ hz) x y rfl).mul
        (hasDerivAt_conj_real _ (hasDerivAt_u_imag i (hw i _ hz) x y rfl)))
    refine hs.congr_deriv ?_
    unfold Fyre
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_mul, Complex.conj_I]
    ring
  cF := by
    have hcu : ∀ i, ContinuousOn (u i) {z : ℂ | 0 < z.im} := fun i => contOn_of_deriv (hu i)
    have hcw : ∀ i, ContinuousOn (w i) {z : ℂ | 0 < z.im} := fun i => contOn_of_deriv (hw i)
    have : ContinuousOn (holAnti u w) {z : ℂ | 0 < z.im} :=
      continuousOn_finsetSum _ (fun i _ => (hcu i).mul (Complex.continuous_conj.comp_continuousOn (hcw i)))
    exact this.comp continuous_cxPt.continuousOn (fun p hp => cxPt_mem hp)
  cFx := by
    have hcu : ∀ i, ContinuousOn (u i) {z : ℂ | 0 < z.im} := fun i => contOn_of_deriv (hu i)
    have hcw : ∀ i, ContinuousOn (w i) {z : ℂ | 0 < z.im} := fun i => contOn_of_deriv (hw i)
    have : ContinuousOn (fun z => ∑ i, (du i z * conj (w i z) + u i z * conj (dw i z))) {z : ℂ | 0 < z.im} :=
      continuousOn_finsetSum _ (fun i _ => ((hcdu i).mul (Complex.continuous_conj.comp_continuousOn (hcw i))).add
        ((hcu i).mul (Complex.continuous_conj.comp_continuousOn (hcdw i))))
    exact this.comp continuous_cxPt.continuousOn (fun p hp => cxPt_mem hp)
  cFy := by
    have hcu : ∀ i, ContinuousOn (u i) {z : ℂ | 0 < z.im} := fun i => contOn_of_deriv (hu i)
    have hcw : ∀ i, ContinuousOn (w i) {z : ℂ | 0 < z.im} := fun i => contOn_of_deriv (hw i)
    have : ContinuousOn (fun z => ∑ i, (I * du i z * conj (w i z) - I * (u i z * conj (dw i z)))) {z : ℂ | 0 < z.im} :=
      continuousOn_finsetSum _ (fun i _ => ((continuousOn_const.mul (hcdu i)).mul
        (Complex.continuous_conj.comp_continuousOn (hcw i))).sub
        (continuousOn_const.mul ((hcu i).mul (Complex.continuous_conj.comp_continuousOn (hcdw i)))))
    exact this.comp continuous_cxPt.continuousOn (fun p hp => cxPt_mem hp)
  per y hy := by
    unfold Fre
    have h1 : ((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I = (((-1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) + 1 := by
      push_cast; ring
    rw [h1]
    exact hper _ (by simpa using hy)

theorem gArc_odd (hS : ∀ z : ℂ, 0 < z.im → holAnti u w (-1 / z) = conj z ^ 2 * holAnti u w z)
    {x : ℝ} (hx : |x| ≤ 1 / 2) : gArc (Fre u w) (-x) = - gArc (Fre u w) x := by
  have ha := arcY_pos hx
  have hneg : arcY (-x) = arcY x := by unfold arcY; simp
  have hxa' : x ^ 2 + (arcY x) ^ 2 = 1 := by
    unfold arcY; rw [Real.sq_sqrt]; · ring
    · have := abs_le.mp hx; nlinarith
  unfold gArc
  rw [hneg]
  unfold Fre
  generalize arcY x = a at *
  have hxa : (x : ℂ) ^ 2 + (a : ℂ) ^ 2 = 1 := by exact_mod_cast hxa'
  have hz : 0 < (((x : ℂ) + (a : ℂ) * I)).im := by simpa using ha
  have hinv : -1 / ((x : ℂ) + (a : ℂ) * I) = ((-x : ℝ) : ℂ) + (a : ℂ) * I := by
    have hne : (x : ℂ) + (a : ℂ) * I ≠ 0 := fun h => by
      have := congrArg Complex.im h; simp at this; exact ha.ne' this
    rw [div_eq_iff hne]
    push_cast
    linear_combination hxa - (a : ℂ) ^ 2 * Complex.I_sq
  have hH := hS _ hz
  rw [hinv] at hH
  have hane : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  rw [hH]
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  have key : ((x : ℂ) + (a : ℂ) * -I) ^ 2 * (-(x : ℂ) - I * (a : ℂ)) = -((x : ℂ) - I * (a : ℂ)) := by
    linear_combination (-((x : ℂ) - (a : ℂ) * I)) * hxa + ((x : ℂ) - (a : ℂ) * I) * (a : ℂ) ^ 2 * Complex.I_sq
  field_simp
  linear_combination (holAnti u w ((x : ℂ) + (a : ℂ) * I)) * key

theorem stokes_holAnti
    (hu : ∀ i z, 0 < z.im → HasDerivAt (u i) (du i z) z)
    (hw : ∀ i z, 0 < z.im → HasDerivAt (w i) (dw i z) z)
    (hcdu : ∀ i, ContinuousOn (du i) {z : ℂ | 0 < z.im})
    (hcdw : ∀ i, ContinuousOn (dw i) {z : ℂ | 0 < z.im})
    (hper : ∀ z : ℂ, 0 < z.im → holAnti u w (z + 1) = holAnti u w z)
    (hS : ∀ z : ℂ, 0 < z.im → holAnti u w (-1 / z) = conj z ^ 2 * holAnti u w z)
    {T : ℝ} (hT : 1 ≤ T) :
    ∫ x in (-1 / 2 : ℝ)..(1 / 2), ∫ y in arcY x..T, holAntiD w du ((x : ℂ) + (y : ℂ) * I) =
      -(I / 2) * ∫ x in (-1 / 2 : ℝ)..(1 / 2), holAnti u w ((x : ℂ) + (T : ℂ) * I) := by
  have hd := stokesData_holAnti hu hw hcdu hcdw hper
  have hodd : ∀ x ∈ Icc (-1 / 2 : ℝ) (1 / 2), gArc (Fre u w) (-x) = - gArc (Fre u w) x :=
    fun x hx => gArc_odd hS (abs_le.mpr ⟨by linarith [hx.1], hx.2⟩)
  have h := hd.stokes_real hT hodd
  have e1 : ∀ x : ℝ, ∫ y in arcY x..T, (Fxre u w du dw x y - I * Fyre u w du dw x y) =
      2 * ∫ y in arcY x..T, holAntiD w du ((x : ℂ) + (y : ℂ) * I) := by
    intro x
    simp_rw [Fxre_sub_Fyre]
    exact intervalIntegral.integral_const_mul _ _
  simp_rw [e1] at h
  rw [intervalIntegral.integral_const_mul] at h
  unfold Fre at h
  have : (2 : ℂ) * (∫ x in (-1 / 2 : ℝ)..(1 / 2), ∫ y in arcY x..T, holAntiD w du ((x : ℂ) + (y : ℂ) * I)) =
      2 * (-(I / 2) * ∫ x in (-1 / 2 : ℝ)..(1 / 2), holAnti u w ((x : ℂ) + (T : ℂ) * I)) := by
    rw [h]; ring
  exact mul_left_cancel₀ two_ne_zero this

end HolAntiStokes

end TernaryPeriodPolynomials.Argument.EichlerShimuraInj
