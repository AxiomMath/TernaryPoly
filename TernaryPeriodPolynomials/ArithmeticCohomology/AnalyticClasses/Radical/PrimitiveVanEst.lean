module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.RadialVanEst

@[expose] public section


/-!
# The radial van Est lemma under partial regularity

The radial van Est lemma holds as soon as the two-cocycle `T` is differentiable in its second
variable and the partial derivative `a ↦ ∂₂T (a, 0)` is `C¹`; no joint `C²` regularity of `T` is
needed. Indeed, the derivative of the cocycle identity expresses `∂₂T (a, c)` through
`a ↦ ∂₂T (a, 0)`, so each `c ↦ T (a, c)` has a differentiable derivative, and the symmetry of its
second derivative is all that the closedness of the twisted one-form uses. The radial primitive
is moreover differentiable, being the radial integral of a closed `C¹` one-form.

Original work by Claude Opus 5.5 (AxiomCode).
-/

namespace TernaryPeriodPolynomials.AnalyticClasses

open MeasureTheory Set

section General

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- **Radial van Est lemma under partial regularity.** Let `ρ` be a `C¹` homomorphism from `E`
to the operators on `V`, let `T` be a two-cocycle with `T (a, 0) = 0` that is differentiable in
its second variable, with `a ↦ ∂₂T (a, 0)` of class `C¹`, and let `η` satisfy the Lie condition.
Then `T` is the coboundary of the radial primitive, and the radial primitive is
differentiable. -/
theorem boundary_radialPrimitive_of_partial (ρ : E → V →L[ℝ] V) (T : E × E → V)
    (η : E →L[ℝ] V) (hρ : ContDiff ℝ 1 ρ) (hρ_add : ∀ a b, ρ (a + b) = (ρ a).comp (ρ b))
    (hTd : ∀ a, Differentiable ℝ (fun c => T (a, c)))
    (hD₀ : ContDiff ℝ 1 (fun a => fderiv ℝ (fun b => T (a, b)) 0))
    (hcocycle : ∀ a b c, ρ a (T (b, c)) - T (a + b, c) + T (a, b + c) - T (a, b) = 0)
    (hT0 : ∀ a, T (a, 0) = 0)
    (hLie : ∀ u w, fderiv ℝ ρ 0 u (η w) - fderiv ℝ ρ 0 w (η u) =
      fderiv ℝ (fun a => fderiv ℝ (fun b => T (a, b)) 0) 0 u w -
        fderiv ℝ (fun a => fderiv ℝ (fun b => T (a, b)) 0) 0 w u) :
    (∀ a b, ρ a (radialPrimitive ρ T η b) - radialPrimitive ρ T η (a + b) +
      radialPrimitive ρ T η a = T (a, b)) ∧ Differentiable ℝ (radialPrimitive ρ T η) := by
  set D : E → E → E →L[ℝ] V := fun a c => fderiv ℝ (fun c' => T (a, c')) c with hD
  have hR : ∀ a c, HasFDerivAt (fun c' => T (a, c')) (D a c) c := fun a c =>
    (hTd a c).hasFDerivAt
  set D₀ : E → E →L[ℝ] V := fun x => D x 0 with hD₀def
  have hD₀d : Differentiable ℝ D₀ := hD₀.differentiable one_ne_zero
  have hD₀c : Continuous D₀ := hD₀.continuous
  have hρd : Differentiable ℝ ρ := hρ.differentiable one_ne_zero
  have hρc : Continuous ρ := hρ.continuous
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
    have hder : HasFDerivAt (fun c => D₀ (a + c) - (ρ a).comp (D₀ c))
        (fderiv ℝ D₀ a - (ContinuousLinearMap.compL ℝ E V V (ρ a)).comp (fderiv ℝ D₀ 0)) 0 := by
      have h1 : HasFDerivAt (fun c => D₀ (a + c)) (fderiv ℝ D₀ a) 0 :=
        hasFDerivAt_comp_const_add a (hD₀d a).hasFDerivAt
      exact h1.sub ((ContinuousLinearMap.compL ℝ E V V (ρ a)).hasFDerivAt.comp 0
        (hD₀d 0).hasFDerivAt)
    have hfirst : ∀ c, HasFDerivAt (fun c' => T (a, c')) (D₀ (a + c) - (ρ a).comp (D₀ c)) c :=
      fun c => (hstar a c) ▸ hR a c
    have hsymm := second_derivative_symmetric hfirst hder u w
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
    have c1 : Continuous fun s : ℝ => ρ (s • v) (η v) := by fun_prop
    have c2 : Continuous fun s : ℝ => D₀ (s • v) v := by fun_prop
    rw [← intervalIntegral.integral_sub (c1.intervalIntegrable _ _) (c2.intervalIntegrable _ _)]
    simp [ω, D₀, D]
  refine ⟨fun a b => ?_, fun x => ?_⟩
  swap
  · rw [show radialPrimitive ρ T η = fun v => ∫ s in (0 : ℝ)..1, ω (s • v) v from funext hrp]
    exact (hP x).differentiableAt
  -- `T (a, b)` as a line integral.
  have hDc : Continuous fun s : ℝ => D a (s • b) b := by
    simp_rw [hstar]
    fun_prop
  have hTb : T (a, b) = ∫ s in (0 : ℝ)..1, D a (s • b) b := by
    have hd : ∀ s ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s : ℝ => T (a, s • b)) (D a (s • b) b) s := by
      intro s _
      refine ((hR a (s • b)).comp_hasDerivAt s ((hasDerivAt_id s).smul_const b)).congr_deriv ?_
      simp
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hDc.intervalIntegrable _ _)]
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

section Plane

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- **Radial van Est lemma on the plane under partial regularity**, with the Lie condition
`X_{e₀} (η e₁) - X_{e₁} (η e₀) = m (e₀, e₁) - m (e₁, e₀)` at the standard basis. -/
theorem boundary_radialPrimitive_of_partial_plane (ρ : (Fin 2 → ℝ) → V →L[ℝ] V)
    (T : (Fin 2 → ℝ) × (Fin 2 → ℝ) → V) (η : (Fin 2 → ℝ) →L[ℝ] V) (hρ : ContDiff ℝ 1 ρ)
    (hρ_add : ∀ a b, ρ (a + b) = (ρ a).comp (ρ b))
    (hTd : ∀ a, Differentiable ℝ (fun c => T (a, c)))
    (hD₀ : ContDiff ℝ 1 (fun a => fderiv ℝ (fun b => T (a, b)) 0))
    (hcocycle : ∀ a b c, ρ a (T (b, c)) - T (a + b, c) + T (a, b + c) - T (a, b) = 0)
    (hT0 : ∀ a, T (a, 0) = 0)
    (hLie : fderiv ℝ ρ 0 (Pi.single 0 1) (η (Pi.single 1 1)) -
        fderiv ℝ ρ 0 (Pi.single 1 1) (η (Pi.single 0 1)) =
      fderiv ℝ (fun a => fderiv ℝ (fun b => T (a, b)) 0 (Pi.single 1 1)) 0 (Pi.single 0 1) -
        fderiv ℝ (fun a => fderiv ℝ (fun b => T (a, b)) 0 (Pi.single 0 1)) 0 (Pi.single 1 1)) :
    (∀ a b, ρ a (radialPrimitive ρ T η b) - radialPrimitive ρ T η (a + b) +
      radialPrimitive ρ T η a = T (a, b)) ∧ Differentiable ℝ (radialPrimitive ρ T η) := by
  refine boundary_radialPrimitive_of_partial ρ T η hρ hρ_add hTd hD₀ hcocycle hT0 ?_
  have hG : DifferentiableAt ℝ (fun a => fderiv ℝ (fun b => T (a, b)) 0) 0 :=
    hD₀.differentiable one_ne_zero 0
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
