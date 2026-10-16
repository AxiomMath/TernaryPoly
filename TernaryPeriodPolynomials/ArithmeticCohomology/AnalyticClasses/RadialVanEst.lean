module

public import Mathlib

@[expose] public section


/-!
# The radial van Est lemma

Let `ρ` be a `C¹` representation of a finite-dimensional real vector space `E` (viewed as an
additive Lie group) on a complete real normed space `V`, and let `T : E × E → V` be a `C²`
two-cocycle with `T (a, 0) = 0`. Given a linear map `η : E →L[ℝ] V` whose Lie-algebra
coboundary equals the antisymmetrised mixed derivative of `T` at the origin, the explicit
radial primitive

`f v = ∫₀¹ ρ (s • v) (η v) ds - ∫₀¹ ∂₂T (s • v, 0) [v] ds`

satisfies `δf = T`, i.e. `ρ a (f b) - f (a + b) + f a = T (a, b)`.

The proof writes `T (a, b) = ∫₀¹ ∂₂T (a, s • b) [b] ds`, uses the derivative of the cocycle
identity to express `∂₂T (a, b)` through the one-form `φ r = ∂₂T (r, 0)`, and checks that the
twisted one-form `ω r = ρ r ∘ η - φ r` is closed. A radial Poincaré lemma then shows that `f`
is a primitive of `ω`, and the two expressions agree.

The main statements are `twoCocycle_eq_boundary_radialPrimitive` (on `Fin 2 → ℝ`, with the Lie
condition at the standard basis), the general `twoCocycle_eq_boundary_radialPrimitive_of_lie`,
and the one-dimensional case `twoCocycle_eq_boundary_radialPrimitive_collinear`, which needs no
Lie condition.

Original work by Claude Opus 5.5 (AxiomCode).
-/

namespace TernaryPeriodPolynomials.AnalyticClasses

open MeasureTheory Metric Set

section Preliminaries

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The radial primitive `f v = ∫₀¹ ρ (s • v) (η v) ds - ∫₀¹ ∂₂T (s • v, 0) [v] ds` attached to
a representation `ρ`, a two-cochain `T` and a linear map `η`. -/
noncomputable def radialPrimitive (ρ : E → V →L[ℝ] V) (T : E × E → V) (η : E →L[ℝ] V)
    (v : E) : V :=
  (∫ s in (0 : ℝ)..1, ρ (s • v) (η v)) - ∫ s in (0 : ℝ)..1, fderiv ℝ (fun b => T (s • v, b)) 0 v

/-- Translating the variable of a differentiable map. -/
theorem hasFDerivAt_comp_const_add {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {f' : E →L[ℝ] F} (a : E) (h : HasFDerivAt f f' a) :
    HasFDerivAt (fun t => f (a + t)) f' 0 := by
  have h' : HasFDerivAt f f' (a + 0) := by rwa [add_zero]
  exact (h'.comp (0 : E) ((hasFDerivAt_id (0 : E)).const_add a)).congr_fderiv (by simp)

/-- The partial derivative of a differentiable map `T : E × E → V` in the second variable. -/
theorem hasFDerivAt_partial_right {T : E × E → V} (hT : Differentiable ℝ T) (a c : E) :
    HasFDerivAt (fun c' => T (a, c')) ((fderiv ℝ T (a, c)).comp (ContinuousLinearMap.inr ℝ E E))
      c :=
  (hT (a, c)).hasFDerivAt.comp c (hasFDerivAt_prodMk_right a c)

/-- For a `C²` map `T`, the partial derivative `a ↦ ∂₂T (a, 0)` is `C¹`. -/
theorem contDiff_partial_right_zero {T : E × E → V} (hT : ContDiff ℝ 2 T) :
    ContDiff ℝ 1 (fun a => fderiv ℝ (fun b => T (a, b)) 0) := by
  have hT1 : ContDiff ℝ 1 (fderiv ℝ T) := hT.fderiv_right (by norm_num)
  have e : (fun a => fderiv ℝ (fun b => T (a, b)) 0) =
      fun a => (fderiv ℝ T (a, 0)).comp (ContinuousLinearMap.inr ℝ E E) := by
    funext a
    exact (hasFDerivAt_partial_right (hT.differentiable two_ne_zero) a 0).fderiv
  rw [e]
  exact (hT1.comp (contDiff_id.prodMk contDiff_const)).clm_comp contDiff_const

end Preliminaries

section General

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- **Radial Poincaré lemma.** If the `C¹` one-form `ω` is closed, then its radial integral
`y ↦ ∫₀¹ ω (s • y) y ds` is a primitive of `ω`. -/
theorem hasFDerivAt_radialIntegral (ω : E → E →L[ℝ] V) (hω : ContDiff ℝ 1 ω)
    (hsymm : ∀ x u w, fderiv ℝ ω x u w = fderiv ℝ ω x w u) (x : E) :
    HasFDerivAt (fun y => ∫ s in (0 : ℝ)..1, ω (s • y) y) (ω x) x := by
  have hωd : Differentiable ℝ ω := hω.differentiable one_ne_zero
  have hωc : Continuous ω := hω.continuous
  have hω'c : Continuous (fderiv ℝ ω) := hω.continuous_fderiv one_ne_zero
  let F' : E → ℝ → E →L[ℝ] V := fun y s =>
    ω (s • y) + s • ContinuousLinearMap.flipₗᵢ ℝ E E V (fderiv ℝ ω (s • y)) y
  have hderiv : ∀ y (s : ℝ), HasFDerivAt (fun y => ω (s • y) y) (F' y s) y := by
    intro y s
    have h1 : HasFDerivAt (fun y : E => s • y) (s • ContinuousLinearMap.id ℝ E) y :=
      (hasFDerivAt_id y).const_smul s
    refine (((hωd (s • y)).hasFDerivAt.comp y h1).clm_apply (hasFDerivAt_id y)).congr_fderiv ?_
    ext w
    simp [F']
  have hF'c : Continuous (fun p : E × ℝ => F' p.1 p.2) := by fun_prop
  have hFc : Continuous (fun p : E × ℝ => ω (p.2 • p.1) p.1) := by fun_prop
  have hF'x : Continuous (F' x) := hF'c.comp (Continuous.prodMk_right x)
  obtain ⟨C, hC⟩ := ((isCompact_closedBall x 1).prod
    (isCompact_Icc (a := (0 : ℝ)) (b := 1))).exists_bound_of_continuousOn hF'c.continuousOn
  have key := intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume)
    (a := 0) (b := 1) (F := fun y s => ω (s • y) y) (F' := F') (x₀ := x) (bound := fun _ => C)
    (ball_mem_nhds x one_pos)
    (Filter.Eventually.of_forall fun y =>
      (hFc.comp (Continuous.prodMk_right y)).aestronglyMeasurable)
    ((hFc.comp (Continuous.prodMk_right x)).intervalIntegrable _ _)
    hF'x.aestronglyMeasurable
    (Filter.Eventually.of_forall fun t ht y hy =>
      hC (y, t) ⟨ball_subset_closedBall hy, by simpa using Ioc_subset_Icc_self ht⟩)
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun t _ y _ => hderiv y t)
  convert key using 1
  ext w
  rw [ContinuousLinearMap.intervalIntegral_apply (hF'x.intervalIntegrable _ _)]
  have hd : ∀ s ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s : ℝ => s • ω (s • x) w) (F' x s w) s := by
    intro s _
    have h2 : HasDerivAt (fun s : ℝ => ω (s • x) w) (fderiv ℝ ω (s • x) x w) s := by
      have := (hωd (s • x)).hasFDerivAt.comp_hasDerivAt s ((hasDerivAt_id s).smul_const x)
      simpa using this.clm_apply (hasDerivAt_const s w)
    refine ((hasDerivAt_id s).smul h2).congr_deriv ?_
    simp [F', hsymm, add_comm]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((hF'x.clm_apply continuous_const).intervalIntegrable _ _)]
  simp

/-- **Radial van Est lemma, general form.** Let `ρ` be a `C¹` homomorphism from `E` to the
operators on `V`, let `T` be a `C²` two-cocycle with `T (a, 0) = 0`, and let `η` satisfy the
Lie condition: the Lie-algebra coboundary of `η` equals the antisymmetrised mixed derivative of
`T` at the origin. Then `T` is the coboundary of the radial primitive. -/
theorem twoCocycle_eq_boundary_radialPrimitive_of_lie (ρ : E → V →L[ℝ] V) (T : E × E → V)
    (η : E →L[ℝ] V) (hρ : ContDiff ℝ 1 ρ) (hρ_add : ∀ a b, ρ (a + b) = (ρ a).comp (ρ b))
    (hT : ContDiff ℝ 2 T)
    (hcocycle : ∀ a b c, ρ a (T (b, c)) - T (a + b, c) + T (a, b + c) - T (a, b) = 0)
    (hT0 : ∀ a, T (a, 0) = 0)
    (hLie : ∀ u w, fderiv ℝ ρ 0 u (η w) - fderiv ℝ ρ 0 w (η u) =
      fderiv ℝ (fun a => fderiv ℝ (fun b => T (a, b)) 0) 0 u w -
        fderiv ℝ (fun a => fderiv ℝ (fun b => T (a, b)) 0) 0 w u)
    (a b : E) :
    ρ a (radialPrimitive ρ T η b) - radialPrimitive ρ T η (a + b) + radialPrimitive ρ T η a =
      T (a, b) := by
  have hTd : Differentiable ℝ T := hT.differentiable two_ne_zero
  have hT1 : ContDiff ℝ 1 (fderiv ℝ T) := hT.fderiv_right (by norm_num)
  set D : E → E → E →L[ℝ] V :=
    fun a c => (fderiv ℝ T (a, c)).comp (ContinuousLinearMap.inr ℝ E E) with hD
  have hR : ∀ a c, HasFDerivAt (fun c' => T (a, c')) (D a c) c :=
    hasFDerivAt_partial_right hTd
  have hDc : Continuous (fun p : E × E => D p.1 p.2) :=
    (hT1.continuous.comp (continuous_fst.prodMk continuous_snd)).clm_comp continuous_const
  set D₀ : E → E →L[ℝ] V := fun x => D x 0 with hD₀def
  have hfd : (fun a => fderiv ℝ (fun b => T (a, b)) 0) = D₀ := by
    funext a
    exact (hR a 0).fderiv
  have hD₀ : ContDiff ℝ 1 D₀ := hfd ▸ contDiff_partial_right_zero hT
  have hD₀d : Differentiable ℝ D₀ := hD₀.differentiable one_ne_zero
  have hρd : Differentiable ℝ ρ := hρ.differentiable one_ne_zero
  have hρc : Continuous ρ := hρ.continuous
  rw [hfd] at hLie
  -- The derivative of the cocycle identity in the last variable.
  have hstar : ∀ a b, D a b = D₀ (a + b) - (ρ a).comp (D₀ b) := by
    intro a b
    have h1 : HasFDerivAt (fun c => T (a, b + c)) (D a b) 0 :=
      hasFDerivAt_comp_const_add b (hR a b)
    have h2 : HasFDerivAt (fun c => T (a, b + c)) (D₀ (a + b) - (ρ a).comp (D₀ b)) 0 := by
      have e : (fun c => T (a, b + c)) =
          fun c => T (a, b) + T (a + b, c) - ρ a (T (b, c)) := by
        funext c
        have := hcocycle a b c
        rw [← sub_eq_zero, ← this]
        abel
      rw [e]
      exact (((hasFDerivAt_const (T (a, b)) (0 : E)).add (hR (a + b) 0)).sub
        ((ρ a).hasFDerivAt.comp (0 : E) (hR b 0))).congr_fderiv (by simp [D₀])
    exact h1.unique h2
  -- The derivative of the representation.
  have hρ' : ∀ x, fderiv ℝ ρ x =
      (ContinuousLinearMap.compL ℝ V V V (ρ x)).comp (fderiv ℝ ρ 0) := by
    intro x
    have h1 : HasFDerivAt (fun t => ρ (x + t)) (fderiv ℝ ρ x) 0 :=
      hasFDerivAt_comp_const_add x (hρd x).hasFDerivAt
    have h2 : HasFDerivAt (fun t => ρ (x + t))
        ((ContinuousLinearMap.compL ℝ V V V (ρ x)).comp (fderiv ℝ ρ 0)) 0 := by
      have e : (fun t => ρ (x + t)) = fun t => ContinuousLinearMap.compL ℝ V V V (ρ x) (ρ t) := by
        funext t
        simp [hρ_add]
      rw [e]
      exact (ContinuousLinearMap.compL ℝ V V V (ρ x)).hasFDerivAt.comp 0 (hρd 0).hasFDerivAt
    exact h1.unique h2
  -- Equivariance of the curl of `D₀`, from the symmetry of second derivatives.
  have hsym2 : ∀ a u w, fderiv ℝ D₀ a u w - ρ a (fderiv ℝ D₀ 0 u w) =
      fderiv ℝ D₀ a w u - ρ a (fderiv ℝ D₀ 0 w u) := by
    intro a u w
    have hga : ContDiff ℝ 2 (fun c => T (a, c)) := hT.comp (contDiff_const.prodMk contDiff_id)
    have hsymm := (hga.contDiffAt (x := 0)).isSymmSndFDerivAt (by simp) u w
    have hfd' : fderiv ℝ (fun c => T (a, c)) = fun c => D₀ (a + c) - (ρ a).comp (D₀ c) := by
      funext c
      rw [(hR a c).fderiv, hstar]
    have hder : HasFDerivAt (fun c => D₀ (a + c) - (ρ a).comp (D₀ c))
        (fderiv ℝ D₀ a - (ContinuousLinearMap.compL ℝ E V V (ρ a)).comp (fderiv ℝ D₀ 0)) 0 := by
      have h1 : HasFDerivAt (fun c => D₀ (a + c)) (fderiv ℝ D₀ a) 0 :=
        hasFDerivAt_comp_const_add a (hD₀d a).hasFDerivAt
      exact h1.sub ((ContinuousLinearMap.compL ℝ E V V (ρ a)).hasFDerivAt.comp 0
        (hD₀d 0).hasFDerivAt)
    rw [hfd', hder.fderiv] at hsymm
    simpa using hsymm
  -- The twisted one-form and its closedness.
  set ω : E → E →L[ℝ] V := fun x => (ρ x).comp η - D₀ x with hωdef
  have hω : ContDiff ℝ 1 ω := (hρ.clm_comp contDiff_const).sub hD₀
  have hωc : Continuous ω := hω.continuous
  have hωsymm : ∀ x u w, fderiv ℝ ω x u w = fderiv ℝ ω x w u := by
    intro x u w
    have h : HasFDerivAt ω
        (((ContinuousLinearMap.compL ℝ E V V).flip η).comp (fderiv ℝ ρ x) - fderiv ℝ D₀ x) x :=
      (((ContinuousLinearMap.compL ℝ E V V).flip η).hasFDerivAt.comp x
        (hρd x).hasFDerivAt).sub (hD₀d x).hasFDerivAt
    have hL := congrArg (ρ x) (hLie u w)
    rw [map_sub, map_sub] at hL
    have hS := hsym2 x u w
    rw [h.fderiv, hρ' x]
    simp only [sub_apply, ContinuousLinearMap.coe_comp,
      Function.comp_apply, ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply]
    linear_combination (norm := module) hL - hS
  -- The radial primitive is the radial integral of `ω`.
  have hP := hasFDerivAt_radialIntegral ω hω hωsymm
  have hrp : ∀ v, radialPrimitive ρ T η v = ∫ s in (0 : ℝ)..1, ω (s • v) v := by
    intro v
    unfold radialPrimitive
    have e : ∀ s : ℝ, fderiv ℝ (fun b => T (s • v, b)) 0 = D₀ (s • v) := fun s =>
      congrFun hfd (s • v)
    simp_rw [e]
    have hD₀c := hD₀.continuous
    have c1 : Continuous fun s : ℝ => ρ (s • v) (η v) := by fun_prop
    have c2 : Continuous fun s : ℝ => D₀ (s • v) v := by fun_prop
    rw [← intervalIntegral.integral_sub (c1.intervalIntegrable _ _) (c2.intervalIntegrable _ _)]
    simp [ω]
  -- `T (a, b)` as a line integral.
  have hTb : T (a, b) = ∫ s in (0 : ℝ)..1, D a (s • b) b := by
    have hd : ∀ s ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s : ℝ => T (a, s • b)) (D a (s • b) b) s := by
      intro s _
      refine ((hR a (s • b)).comp_hasDerivAt s ((hasDerivAt_id s).smul_const b)).congr_deriv ?_
      simp
    have c : Continuous fun s : ℝ => D a (s • b) b :=
      (hDc.comp (continuous_const.prodMk (continuous_id.smul continuous_const) :
        Continuous fun s : ℝ => (a, s • b))).clm_apply continuous_const
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (c.intervalIntegrable _ _)]
    simp [hT0]
  -- `f (a + b) - f a` as a line integral.
  have hPab : (∫ s in (0 : ℝ)..1, ω (s • (a + b)) (a + b)) - ∫ s in (0 : ℝ)..1, ω (s • a) a =
      ∫ s in (0 : ℝ)..1, ω (a + s • b) b := by
    have hd : ∀ s ∈ uIcc (0 : ℝ) 1, HasDerivAt
        (fun s : ℝ => ∫ t in (0 : ℝ)..1, ω (t • (a + s • b)) (a + s • b)) (ω (a + s • b) b) s := by
      intro s _
      refine ((hP (a + s • b)).comp_hasDerivAt s
        (((hasDerivAt_id s).smul_const b).const_add a)).congr_deriv ?_
      simp
    have c : Continuous fun s : ℝ => ω (a + s • b) b := by fun_prop
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (c.intervalIntegrable _ _)]
    simp
  have hint : ∀ s : ℝ, D a (s • b) b = ρ a (ω (s • b) b) - ω (a + s • b) b := by
    intro s
    rw [hstar]
    simp only [hωdef, hρ_add, sub_apply, ContinuousLinearMap.coe_comp,
      Function.comp_apply, map_sub]
    abel
  rw [hrp, hrp, hrp, hTb]
  simp_rw [hint]
  have hc1 : Continuous fun s : ℝ => ω (s • b) b := by fun_prop
  have hc2 : Continuous fun s : ℝ => ω (a + s • b) b := by fun_prop
  have hc3 : Continuous fun s : ℝ => ρ a (ω (s • b) b) := by fun_prop
  rw [intervalIntegral.integral_sub (hc3.intervalIntegrable _ _)
    (hc2.intervalIntegrable _ _), ← hPab,
    ← ContinuousLinearMap.intervalIntegral_comp_comm _ (hc1.intervalIntegrable _ _)]
  abel

end General

section Collinear

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- **One-dimensional radial van Est lemma.** Without any Lie condition on `η`, the cocycle `T`
agrees with the coboundary of the radial primitive on every collinear pair `(s • v, s' • v)`. -/
theorem twoCocycle_eq_boundary_radialPrimitive_collinear (ρ : E → V →L[ℝ] V) (T : E × E → V)
    (η : E →L[ℝ] V) (hρ : ContDiff ℝ 1 ρ) (hρ_add : ∀ a b, ρ (a + b) = (ρ a).comp (ρ b))
    (hT : ContDiff ℝ 2 T)
    (hcocycle : ∀ a b c, ρ a (T (b, c)) - T (a + b, c) + T (a, b + c) - T (a, b) = 0)
    (hT0 : ∀ a, T (a, 0) = 0) (v : E) (s s' : ℝ) :
    ρ (s • v) (radialPrimitive ρ T η (s' • v)) - radialPrimitive ρ T η (s • v + s' • v) +
      radialPrimitive ρ T η (s • v) = T (s • v, s' • v) := by
  set L : ℝ →L[ℝ] E := ContinuousLinearMap.toSpanSingleton ℝ v with hLdef
  have hL : ∀ t : ℝ, L t = t • v := fun t => by simp [L]
  set ρ' : ℝ → V →L[ℝ] V := fun t => ρ (t • v) with hρ'def
  set T' : ℝ × ℝ → V := fun p => T (p.1 • v, p.2 • v) with hT'def
  set η' : ℝ →L[ℝ] V := η.comp L with hη'def
  have hTd : Differentiable ℝ T := hT.differentiable two_ne_zero
  have hrp : ∀ t : ℝ, radialPrimitive ρ' T' η' t = radialPrimitive ρ T η (t • v) := by
    intro t
    unfold radialPrimitive
    congr 1
    · congr 1
      funext σ
      simp [ρ', η', hL, smul_smul]
    · congr 1
      funext σ
      have e : (fun b : ℝ => T' (σ • t, b)) = (fun c => T (σ • t • v, c)) ∘ L := by
        funext b
        simp [T', hL, smul_smul]
      rw [e, fderiv_comp (0 : ℝ) ((hasFDerivAt_partial_right hTd _ _).differentiableAt)
        L.differentiableAt, ContinuousLinearMap.fderiv]
      simp [hL]
  have hρ' : ContDiff ℝ 1 ρ' := hρ.comp (contDiff_id.smul contDiff_const)
  have hT' : ContDiff ℝ 2 T' :=
    hT.comp ((contDiff_fst.smul contDiff_const).prodMk (contDiff_snd.smul contDiff_const))
  have key := twoCocycle_eq_boundary_radialPrimitive_of_lie ρ' T' η' hρ'
    (fun a b => by simp [ρ', add_smul, hρ_add])
    hT' (fun a b c => by simpa [ρ', T', add_smul] using hcocycle (a • v) (b • v) (c • v))
    (fun a => by simp [T', hT0])
    (fun u w => by
      have hu : u = u • (1 : ℝ) := by simp
      have hw : w = w • (1 : ℝ) := by simp
      rw [hu, hw]
      simp only [map_smul, smul_apply, smul_smul, mul_comm w u, sub_self])
    s s'
  rw [hrp, hrp, hrp] at key
  simpa [ρ', T', add_smul] using key

end Collinear

section Plane

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- **Radial van Est lemma.** Let `ρ` be a `C¹` homomorphism from `Fin 2 → ℝ` to the operators
on `V`, let `T` be a `C²` two-cocycle with `T (a, 0) = 0`, and let `η` satisfy the Lie condition
`X_{e₀} (η e₁) - X_{e₁} (η e₀) = m (e₀, e₁) - m (e₁, e₀)`, where `X_w` is the derivative of `ρ`
at `0` in direction `w` and `m (w', w)` is the mixed derivative of `T` at the origin. Then `T`
is the coboundary of the radial primitive. -/
theorem twoCocycle_eq_boundary_radialPrimitive (ρ : (Fin 2 → ℝ) → V →L[ℝ] V)
    (T : (Fin 2 → ℝ) × (Fin 2 → ℝ) → V) (η : (Fin 2 → ℝ) →L[ℝ] V) (hρ : ContDiff ℝ 1 ρ)
    (hρ_add : ∀ a b, ρ (a + b) = (ρ a).comp (ρ b)) (hT : ContDiff ℝ 2 T)
    (hcocycle : ∀ a b c, ρ a (T (b, c)) - T (a + b, c) + T (a, b + c) - T (a, b) = 0)
    (hT0 : ∀ a, T (a, 0) = 0)
    (hLie : fderiv ℝ ρ 0 (Pi.single 0 1) (η (Pi.single 1 1)) -
        fderiv ℝ ρ 0 (Pi.single 1 1) (η (Pi.single 0 1)) =
      fderiv ℝ (fun a => fderiv ℝ (fun b => T (a, b)) 0 (Pi.single 1 1)) 0 (Pi.single 0 1) -
        fderiv ℝ (fun a => fderiv ℝ (fun b => T (a, b)) 0 (Pi.single 0 1)) 0 (Pi.single 1 1))
    (a b : Fin 2 → ℝ) :
    ρ a (radialPrimitive ρ T η b) - radialPrimitive ρ T η (a + b) + radialPrimitive ρ T η a =
      T (a, b) := by
  refine twoCocycle_eq_boundary_radialPrimitive_of_lie ρ T η hρ hρ_add hT hcocycle hT0 ?_ a b
  have hG : DifferentiableAt ℝ (fun a => fderiv ℝ (fun b => T (a, b)) 0) 0 :=
    (contDiff_partial_right_zero hT).differentiable one_ne_zero 0
  have hm : ∀ w' w : Fin 2 → ℝ,
      fderiv ℝ (fun a => fderiv ℝ (fun b => T (a, b)) 0 w) 0 w' =
        fderiv ℝ (fun a => fderiv ℝ (fun b => T (a, b)) 0) 0 w' w := by
    intro w' w
    rw [fderiv_clm_apply hG (differentiableAt_const w)]
    simp
  rw [hm, hm] at hLie
  intro u w
  have hdec : ∀ x : Fin 2 → ℝ, x = x 0 • Pi.single 0 1 + x 1 • Pi.single 1 1 := by
    intro x
    ext i
    fin_cases i <;> simp
  rw [hdec u, hdec w]
  simp only [map_add, map_smul, add_apply, smul_apply]
  linear_combination (norm := module) (u 0 * w 1 - u 1 * w 0) • hLie

end Plane

end TernaryPeriodPolynomials.AnalyticClasses
