module

public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.Scalar
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
public import Mathlib.Analysis.Calculus.Deriv.AffineMap
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft

@[expose] public section


/-!
# Closedness of two-forms is preserved by pullback (coordinate form)

A two-form on `ℝ⁵` given by antisymmetric complex component functions `om y a b` is closed at `y` if
its coordinate exterior derivative vanishes (`ClosedAt`). For a `C^∞` map `Φ`, the scalar pullback
`scalarPullback Φ om` is closed at `x` whenever `om` is closed at `Φ x` (`closed_scalarPullback`): the
second-derivative terms cancel by symmetry of the Hessian and antisymmetry of `om`, and the first
order terms by the cyclic identity (`closed_algebra`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergenceC4

open scoped ContDiff

/-! ### The algebra of the closedness of a pullback -/

/-- The trilinear sum `S x y z = ∑ P_{dab} x_d y_a z_b`. -/
def triS (P : Fin 5 → Fin 5 → Fin 5 → ℂ) (x y z : Fin 5 → ℂ) : ℂ :=
  ∑ a : Fin 5, ∑ b : Fin 5, ∑ d : Fin 5, P d a b * y a * z b * x d

theorem sum3_eq (F : Fin 5 → Fin 5 → Fin 5 → ℂ) :
    ∑ a : Fin 5, ∑ b : Fin 5, ∑ d : Fin 5, F a b d =
      ∑ p : Fin 5 × Fin 5 × Fin 5, F p.1 p.2.1 p.2.2 := by
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]

theorem triS_anti (P : Fin 5 → Fin 5 → Fin 5 → ℂ) (hP : ∀ d a b, P d a b = - P d b a)
    (x y z : Fin 5 → ℂ) : triS P x y z = - triS P x z y := by
  unfold triS
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [hP d a b]; ring

/-- Cyclic shift of the three summation indices. -/
def shiftEquiv : (Fin 5 × Fin 5 × Fin 5) ≃ (Fin 5 × Fin 5 × Fin 5) where
  toFun p := (p.2.2, p.1, p.2.1)
  invFun p := (p.2.1, p.2.2, p.1)
  left_inv _ := rfl
  right_inv _ := rfl

theorem triS_cyclic (P : Fin 5 → Fin 5 → Fin 5 → ℂ)
    (hcl : ∀ d a b, P d a b + P a b d + P b d a = 0) (x y z : Fin 5 → ℂ) :
    triS P x y z + triS P y z x + triS P z x y = 0 := by
  set G₁ : Fin 5 × Fin 5 × Fin 5 → ℂ := fun p => P p.2.2 p.1 p.2.1 * y p.1 * z p.2.1 * x p.2.2
    with hG₁
  set G₂ : Fin 5 × Fin 5 × Fin 5 → ℂ := fun p => P p.1 p.2.1 p.2.2 * y p.1 * z p.2.1 * x p.2.2
    with hG₂
  set G₃ : Fin 5 × Fin 5 × Fin 5 → ℂ := fun p => P p.2.1 p.2.2 p.1 * y p.1 * z p.2.1 * x p.2.2
    with hG₃
  have e1 : triS P x y z = ∑ p, G₁ p := by
    unfold triS; rw [sum3_eq (fun a b d => P d a b * y a * z b * x d)]
  have e2 : triS P y z x = ∑ p, G₂ p := by
    unfold triS; rw [sum3_eq (fun a b d => P d a b * z a * x b * y d)]
    rw [← Equiv.sum_comp shiftEquiv G₂]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [hG₂, shiftEquiv, Equiv.coe_fn_mk]; ring
  have e3 : triS P z x y = ∑ p, G₃ p := by
    unfold triS; rw [sum3_eq (fun a b d => P d a b * x a * y b * z d)]
    rw [← Equiv.sum_comp shiftEquiv.symm G₃]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [hG₃, shiftEquiv, Equiv.coe_fn_symm_mk]; ring
  rw [e1, e2, e3, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun p _ => ?_
  have := hcl p.2.2 p.1 p.2.1
  simp only [hG₁, hG₂, hG₃]
  linear_combination (y p.1 * z p.2.1 * x p.2.2) * this

theorem closed_algebra (u v t sij sik sjk : Fin 5 → ℂ) (w : Fin 5 → Fin 5 → ℂ)
    (P : Fin 5 → Fin 5 → Fin 5 → ℂ) (hw : ∀ a b, w a b = - w b a)
    (hP : ∀ d a b, P d a b = - P d b a) (hcl : ∀ d a b, P d a b + P a b d + P b d a = 0) :
    (∑ a : Fin 5, ∑ b : Fin 5, ((sij a * t b + v a * sik b) * w a b +
        v a * t b * (∑ d : Fin 5, u d * P d a b)))
      - (∑ a : Fin 5, ∑ b : Fin 5, ((sij a * t b + u a * sjk b) * w a b +
        u a * t b * (∑ d : Fin 5, v d * P d a b)))
      + (∑ a : Fin 5, ∑ b : Fin 5, ((sik a * v b + u a * sjk b) * w a b +
        u a * v b * (∑ d : Fin 5, t d * P d a b))) = 0 := by
  have H1 : ∑ a : Fin 5, ∑ b : Fin 5, (v a * sik b + sik a * v b) * w a b = 0 := by
    have : ∑ a : Fin 5, ∑ b : Fin 5, sik a * v b * w a b =
        - ∑ a : Fin 5, ∑ b : Fin 5, v a * sik b * w a b := by
      rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hw b a]; ring
    simp only [add_mul, Finset.sum_add_distrib]
    rw [this]; ring
  have H2 : triS P u v t - triS P v u t + triS P t u v = 0 := by
    have h1 := triS_anti P hP v u t
    have h2 := triS_cyclic P hcl u v t
    linear_combination h2 - h1
  have e2 : triS P u v t = ∑ a : Fin 5, ∑ b : Fin 5, v a * t b * (∑ d : Fin 5, u d * P d a b) := by
    unfold triS
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    ring
  have e3 : triS P v u t = ∑ a : Fin 5, ∑ b : Fin 5, u a * t b * (∑ d : Fin 5, v d * P d a b) := by
    unfold triS
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    ring
  have e4 : triS P t u v = ∑ a : Fin 5, ∑ b : Fin 5, u a * v b * (∑ d : Fin 5, t d * P d a b) := by
    unfold triS
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    ring
  rw [e2, e3, e4] at H2
  simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib] at H2 ⊢
  have hterm : ∀ (a b : Fin 5), ((sij a * t b + v a * sik b) * w a b +
      v a * t b * ∑ d, u d * P d a b) -
      ((sij a * t b + u a * sjk b) * w a b + u a * t b * ∑ d, v d * P d a b) +
      ((sik a * v b + u a * sjk b) * w a b + u a * v b * ∑ d, t d * P d a b) =
      (v a * sik b + sik a * v b) * w a b +
      (v a * t b * ∑ d, u d * P d a b - u a * t b * ∑ d, v d * P d a b +
        u a * v b * ∑ d, t d * P d a b) := fun a b => by ring
  have hsum : ∀ (f g : Fin 5 → Fin 5 → ℂ),
      ∑ a, ∑ b, (f a b + g a b) = ∑ a, ∑ b, f a b + ∑ a, ∑ b, g a b := by
    intro f g; simp only [Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hterm a b)),
    hsum (fun a b => (v a * sik b + sik a * v b) * w a b)
      (fun a b => v a * t b * ∑ d, u d * P d a b - u a * t b * ∑ d, v d * P d a b +
        u a * v b * ∑ d, t d * P d a b), H1, H2]
  ring

/-! ### Closedness is preserved by pullback -/

/-- Coordinate closedness of a two-form given by the complex component functions `c a b`. -/
def ClosedAt (c : Fin 5 → Fin 5 → (Fin 5 → ℝ) → ℂ) (x : Fin 5 → ℝ) : Prop :=
  ∀ i j k : Fin 5, fderiv ℝ (c j k) x (Pi.single i 1) - fderiv ℝ (c i k) x (Pi.single j 1) +
    fderiv ℝ (c i j) x (Pi.single k 1) = 0

/-- The `a`-th component of the image of the `p`-th basis vector under `D Φ_z`. -/
def Dv (Φ : (Fin 5 → ℝ) → (Fin 5 → ℝ)) (p a : Fin 5) (z : Fin 5 → ℝ) : ℝ :=
  fderiv ℝ Φ z (Pi.single p 1) a

theorem fderiv_apply_eq_sum_Dv (Φ : (Fin 5 → ℝ) → (Fin 5 → ℝ)) (z : Fin 5 → ℝ) (r : Fin 5)
    (L : (Fin 5 → ℝ) →L[ℝ] ℂ) :
    L (fderiv ℝ Φ z (Pi.single r 1)) = ∑ d : Fin 5, (Dv Φ r d z : ℂ) * L (Pi.single d 1) := by
  have e : fderiv ℝ Φ z (Pi.single r 1) = ∑ d : Fin 5, Dv Φ r d z • (Pi.single d (1 : ℝ) : Fin 5 → ℝ) := by
    funext a
    simp [Dv, Finset.sum_apply, Pi.single_apply]
  rw [e, map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [map_smul]; simp

theorem hasFDerivAt_Dv {Φ : (Fin 5 → ℝ) → (Fin 5 → ℝ)} {x : Fin 5 → ℝ}
    (hΦ : ContDiffAt ℝ ∞ Φ x) (p a : Fin 5) :
    HasFDerivAt (fun z => Dv Φ p a z)
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 5 => ℝ) a ∘L
        ContinuousLinearMap.apply ℝ (Fin 5 → ℝ) (Pi.single p (1 : ℝ))).comp
          (fderiv ℝ (fderiv ℝ Φ) x)) x := by
  have hΦ2 : ContDiffAt ℝ 2 Φ x := hΦ.of_le (WithTop.coe_le_coe.2 le_top)
  have h1 : DifferentiableAt ℝ (fderiv ℝ Φ) x :=
    (ContDiffAt.fderiv_right hΦ2 (m := 1) (by norm_num)).differentiableAt (by norm_num)
  exact (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.proj (R := ℝ)
    (φ := fun _ : Fin 5 => ℝ) a ∘L ContinuousLinearMap.apply ℝ (Fin 5 → ℝ) (Pi.single p (1 : ℝ)))).comp
      x h1.hasFDerivAt

theorem fderiv_Dv_apply {Φ : (Fin 5 → ℝ) → (Fin 5 → ℝ)} {x : Fin 5 → ℝ}
    (hΦ : ContDiffAt ℝ ∞ Φ x) (p a r : Fin 5) :
    fderiv ℝ (fun z => Dv Φ p a z) x (Pi.single r 1) =
      fderiv ℝ (fderiv ℝ Φ) x (Pi.single r 1) (Pi.single p 1) a := by
  rw [(hasFDerivAt_Dv hΦ p a).fderiv]
  rfl

theorem Dv_symm {Φ : (Fin 5 → ℝ) → (Fin 5 → ℝ)} {x : Fin 5 → ℝ}
    (hΦ : ContDiffAt ℝ ∞ Φ x) (p a r : Fin 5) :
    fderiv ℝ (fun z => Dv Φ p a z) x (Pi.single r 1) =
      fderiv ℝ (fun z => Dv Φ r a z) x (Pi.single p 1) := by
  rw [fderiv_Dv_apply hΦ, fderiv_Dv_apply hΦ]
  have hΦ2 : ContDiffAt ℝ 2 Φ x := hΦ.of_le (WithTop.coe_le_coe.2 le_top)
  have := ContDiffAt.isSymmSndFDerivAt hΦ2 (by simp [minSmoothness_of_isRCLikeNormedField])
  rw [this.eq (Pi.single r 1) (Pi.single p 1)]

theorem hasFDerivAt_scalarPullback {Φ : (Fin 5 → ℝ) → (Fin 5 → ℝ)} {x : Fin 5 → ℝ}
    (hΦ : ContDiffAt ℝ ∞ Φ x) (om : (Fin 5 → ℝ) → Fin 5 → Fin 5 → ℂ)
    (hωd : ∀ a b, DifferentiableAt ℝ (fun y => om y a b) (Φ x)) (p q : Fin 5) :
    HasFDerivAt (fun z => scalarPullback Φ om z p q) (∑ a : Fin 5, ∑ b : Fin 5,
      ((((Dv Φ p a x * Dv Φ q b x : ℝ) : ℂ)) •
          ((fderiv ℝ (fun y => om y a b) (Φ x)).comp (fderiv ℝ Φ x)) +
        (om (Φ x) a b) • (Complex.ofRealCLM.comp
          (Dv Φ p a x • fderiv ℝ (fun z => Dv Φ q b z) x +
            Dv Φ q b x • fderiv ℝ (fun z => Dv Φ p a z) x)))) x := by
  have hΦd : DifferentiableAt ℝ Φ x := hΦ.differentiableAt (by simp)
  have hD : ∀ p a, HasFDerivAt (fun z => Dv Φ p a z) (fderiv ℝ (fun z => Dv Φ p a z) x) x :=
    fun p a => (hasFDerivAt_Dv hΦ p a).differentiableAt.hasFDerivAt
  have hωΦ : ∀ a b, HasFDerivAt (fun z => om (Φ z) a b)
      ((fderiv ℝ (fun y => om y a b) (Φ x)).comp (fderiv ℝ Φ x)) x :=
    fun a b => ((hωd a b).hasFDerivAt).comp x hΦd.hasFDerivAt
  have hF : ∀ a b, HasFDerivAt (fun z => ((Dv Φ p a z * Dv Φ q b z : ℝ) : ℂ) * om (Φ z) a b)
      ((((Dv Φ p a x * Dv Φ q b x : ℝ) : ℂ)) •
          ((fderiv ℝ (fun y => om y a b) (Φ x)).comp (fderiv ℝ Φ x)) +
        (om (Φ x) a b) • (Complex.ofRealCLM.comp
          (Dv Φ p a x • fderiv ℝ (fun z => Dv Φ q b z) x +
            Dv Φ q b x • fderiv ℝ (fun z => Dv Φ p a z) x))) x := by
    intro a b
    have h1 := Complex.ofRealCLM.hasFDerivAt.comp x ((hD p a).mul (hD q b))
    exact h1.mul (hωΦ a b)
  unfold scalarPullback
  refine HasFDerivAt.fun_sum fun a _ => ?_
  exact HasFDerivAt.fun_sum fun b _ => hF a b

theorem differentiableAt_scalarPullback {Φ : (Fin 5 → ℝ) → (Fin 5 → ℝ)} {x : Fin 5 → ℝ}
    (hΦ : ContDiffAt ℝ ∞ Φ x) (om : (Fin 5 → ℝ) → Fin 5 → Fin 5 → ℂ)
    (hωd : ∀ a b, DifferentiableAt ℝ (fun y => om y a b) (Φ x)) (p q : Fin 5) :
    DifferentiableAt ℝ (fun z => scalarPullback Φ om z p q) x :=
  (hasFDerivAt_scalarPullback hΦ om hωd p q).differentiableAt

theorem fderiv_scalarPullback {Φ : (Fin 5 → ℝ) → (Fin 5 → ℝ)} {x : Fin 5 → ℝ}
    (hΦ : ContDiffAt ℝ ∞ Φ x) (om : (Fin 5 → ℝ) → Fin 5 → Fin 5 → ℂ)
    (hωd : ∀ a b, DifferentiableAt ℝ (fun y => om y a b) (Φ x)) (p q r : Fin 5) :
    fderiv ℝ (fun z => scalarPullback Φ om z p q) x (Pi.single r 1) =
      ∑ a : Fin 5, ∑ b : Fin 5,
        ((((fderiv ℝ (fun z => Dv Φ p a z) x (Pi.single r 1) : ℝ) : ℂ) * (Dv Φ q b x : ℂ) +
          (Dv Φ p a x : ℂ) * ((fderiv ℝ (fun z => Dv Φ q b z) x (Pi.single r 1) : ℝ) : ℂ)) *
            om (Φ x) a b +
          ((Dv Φ p a x * Dv Φ q b x : ℝ) : ℂ) * ∑ d : Fin 5, (Dv Φ r d x : ℂ) *
            fderiv ℝ (fun y => om y a b) (Φ x) (Pi.single d 1)) := by
  rw [(hasFDerivAt_scalarPullback hΦ om hωd p q).fderiv]
  simp only [sum_apply, add_apply, smul_apply, ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [fderiv_apply_eq_sum_Dv Φ x r (fderiv ℝ (fun y => om y a b) (Φ x))]
  push_cast
  ring

/-- **Closedness is preserved by pullback.** -/
theorem closed_scalarPullback {Φ : (Fin 5 → ℝ) → (Fin 5 → ℝ)} {x : Fin 5 → ℝ}
    (hΦ : ContDiffAt ℝ ∞ Φ x) (om : (Fin 5 → ℝ) → Fin 5 → Fin 5 → ℂ)
    (hωd : ∀ a b, DifferentiableAt ℝ (fun y => om y a b) (Φ x))
    (hanti : ∀ y a b, om y a b = - om y b a)
    (hcl : ClosedAt (fun a b y => om y a b) (Φ x)) :
    ClosedAt (fun i j z => scalarPullback Φ om z i j) x := by
  intro i j k
  rw [fderiv_scalarPullback hΦ om hωd, fderiv_scalarPullback hΦ om hωd,
    fderiv_scalarPullback hΦ om hωd]
  have hS : ∀ p r a, fderiv ℝ (fun z => Dv Φ p a z) x (Pi.single r 1) =
      fderiv ℝ (fun z => Dv Φ r a z) x (Pi.single p 1) := fun p r a => Dv_symm hΦ p a r
  have hP : ∀ d a b, fderiv ℝ (fun y => om y a b) (Φ x) (Pi.single d 1) =
      - fderiv ℝ (fun y => om y b a) (Φ x) (Pi.single d 1) := by
    intro d a b
    have : (fun y => om y a b) = fun y => - om y b a := funext fun y => hanti y a b
    rw [this, fderiv_fun_neg]; rfl
  have hcl' : ∀ d a b, fderiv ℝ (fun y => om y a b) (Φ x) (Pi.single d 1) +
      fderiv ℝ (fun y => om y b d) (Φ x) (Pi.single a 1) +
      fderiv ℝ (fun y => om y d a) (Φ x) (Pi.single b 1) = 0 := by
    intro d a b
    have h := hcl d a b
    -- h : P_d(a,b) - P_a(d,b) + P_b(d,a) = 0
    have e1 := hP a d b
    have e2 := hP b d a
    -- P_a(d,b) = -P_a(b,d)
    linear_combination h + e1
  have hα := closed_algebra (fun a => (Dv Φ i a x : ℂ)) (fun a => (Dv Φ j a x : ℂ))
    (fun a => (Dv Φ k a x : ℂ))
    (fun a => ((fderiv ℝ (fun z => Dv Φ j a z) x (Pi.single i 1) : ℝ) : ℂ))
    (fun a => ((fderiv ℝ (fun z => Dv Φ k a z) x (Pi.single i 1) : ℝ) : ℂ))
    (fun a => ((fderiv ℝ (fun z => Dv Φ k a z) x (Pi.single j 1) : ℝ) : ℂ))
    (fun a b => om (Φ x) a b)
    (fun d a b => fderiv ℝ (fun y => om y a b) (Φ x) (Pi.single d 1))
    (fun a b => hanti _ a b) hP hcl'
  simp only [hS j i, hS k i, hS k j] at *
  push_cast
  exact hα

end TernaryPeriodPolynomials.Argument.ConvergenceC4
