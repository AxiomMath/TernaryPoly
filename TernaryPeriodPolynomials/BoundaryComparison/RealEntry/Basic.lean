module

public import TernaryPeriodPolynomials.BoundaryComparison.Defs

@[expose] public section


/-! Generic algebraic helper lemmas for the Appendix C.5 real-entry proof. -/


namespace TernaryPeriodPolynomials.Argument

theorem one_sub_div_eq (a Q : ℝ) (hQ : Q ≠ 0) : 1 - a / Q = (Q - a) / Q := by
  field_simp

theorem div_div_eq_div (a Q A : ℝ) (hQ : Q ≠ 0) (hA : A ≠ 0) : a / Q / (A / Q) = a / A := by
  field_simp

theorem sqrt_div_lemma (Q A : ℝ) (hQ : 0 < Q) (hA : 0 < A) :
    Real.sqrt (1 / Q) / (A / Q) = Real.sqrt Q / A := by
  have hw : Real.sqrt Q * Real.sqrt Q = Q := Real.mul_self_sqrt hQ.le
  rw [one_div, Real.sqrt_inv]
  field_simp
  linear_combination -hw

/-! ### `HasDerivAt` combinators









-/

theorem base_const_mul (c y : ℝ) : HasDerivAt (fun x : ℝ => c * x) c y := by
  have hcoe : (⇑(c • ContinuousLinearMap.id ℝ ℝ) : ℝ → ℝ) = fun x => c * x := by
    ext x; simp [smul_eq_mul]
  have hL : HasFDerivAt (fun x : ℝ => c * x) (c • ContinuousLinearMap.id ℝ ℝ) y := by
    rw [← hcoe]; exact (c • ContinuousLinearMap.id ℝ ℝ).hasFDerivAt
  have hD := hasFDerivAt_iff_hasDerivAt.mp hL
  have hval : (c • ContinuousLinearMap.id ℝ ℝ) 1 = c := by simp [smul_eq_mul]
  rwa [hval] at hD

theorem base_ofReal (y : ℝ) : HasDerivAt (fun r : ℝ => (r : ℂ)) (1 : ℂ) y := by
  have hcoe : (⇑Complex.ofRealCLM : ℝ → ℂ) = fun r : ℝ => (r : ℂ) := by
    ext r; simp [Complex.ofRealCLM_apply]
  have hL : HasFDerivAt (fun r : ℝ => (r : ℂ)) Complex.ofRealCLM y := by
    rw [← hcoe]; exact Complex.ofRealCLM.hasFDerivAt
  have hD := hasFDerivAt_iff_hasDerivAt.mp hL
  have hval : Complex.ofRealCLM 1 = (1 : ℂ) := by simp [Complex.ofRealCLM_apply]
  rwa [hval] at hD

theorem hasDerivAt_ofReal_comp {f : ℝ → ℝ} {d x : ℝ} (hf : HasDerivAt f d x) :
    HasDerivAt (fun y => (f y : ℂ)) (d : ℂ) x := by
  have h := (base_ofReal (f x)).scomp x hf
  have hval : (d : ℝ) • (1 : ℂ) = (d : ℂ) := by apply Complex.ext <;> simp
  rwa [hval] at h

theorem hasDerivAt_const_mul_comp {f : ℝ → ℝ} {d x : ℝ} (c : ℝ) (hf : HasDerivAt f d x) :
    HasDerivAt (fun y => c * f y) (d * c) x := by
  have h := (base_const_mul c (f x)).scomp x hf
  have heq : ((fun r : ℝ => c * r) ∘ f) = (fun y => c * f y) := rfl
  have hv : d • c = d * c := by simp [smul_eq_mul]
  rw [heq, hv] at h
  exact h

theorem hasDerivAt_div_const_comp {f : ℝ → ℝ} {d x : ℝ} (c : ℝ) (hf : HasDerivAt f d x) :
    HasDerivAt (fun y => f y / c) (d / c) x := by
  have h := hasDerivAt_const_mul_comp c⁻¹ hf
  have heq : (fun y => c⁻¹ * f y) = (fun y => f y / c) := by funext y; ring
  have hv : d * c⁻¹ = d / c := by ring
  rw [heq, hv] at h
  exact h

theorem base_const_mul_C (c w : ℂ) : HasDerivAt (fun z : ℂ => c * z) c w := by
  have hcoe : (⇑(c • ContinuousLinearMap.id ℂ ℂ) : ℂ → ℂ) = fun z => c * z := by
    ext z; simp [smul_eq_mul]
  have hL : HasFDerivAt (fun z : ℂ => c * z) (c • ContinuousLinearMap.id ℂ ℂ) w := by
    rw [← hcoe]; exact (c • ContinuousLinearMap.id ℂ ℂ).hasFDerivAt
  have hD := hasFDerivAt_iff_hasDerivAt.mp hL
  have hval : (c • ContinuousLinearMap.id ℂ ℂ) 1 = c := by simp [smul_eq_mul]
  rwa [hval] at hD

theorem hasDerivAt_const_mul_C_comp {g : ℝ → ℂ} {dg : ℂ} {x : ℝ} (c : ℂ)
    (hg : HasDerivAt g dg x) : HasDerivAt (fun y => c * g y) (dg * c) x := by
  have h := (base_const_mul_C c (g x)).scomp x hg
  have heq : ((fun z : ℂ => c * z) ∘ g) = (fun y => c * g y) := rfl
  have hv : dg • c = dg * c := by simp [smul_eq_mul]
  rw [heq, hv] at h
  exact h

theorem hasDerivAt_add_C {f g : ℝ → ℂ} {df dg : ℂ} {x : ℝ} (hf : HasDerivAt f df x)
    (hg : HasDerivAt g dg x) : HasDerivAt (fun y => f y + g y) (df + dg) x := by
  have hF : HasFDerivAt f (ContinuousLinearMap.toSpanSingleton ℝ df) x :=
    hasFDerivAt_iff_hasDerivAt.mpr (by simpa using hf)
  have hG : HasFDerivAt g (ContinuousLinearMap.toSpanSingleton ℝ dg) x :=
    hasFDerivAt_iff_hasDerivAt.mpr (by simpa using hg)
  have hD := hasFDerivAt_iff_hasDerivAt.mp (hF.add hG)
  have heq : (f + g) = (fun y => f y + g y) := rfl
  have hv : (ContinuousLinearMap.toSpanSingleton ℝ df + ContinuousLinearMap.toSpanSingleton ℝ dg) 1
      = df + dg := by
    simp [ContinuousLinearMap.toSpanSingleton_apply]
  rw [heq, hv] at hD
  exact hD

end TernaryPeriodPolynomials.Argument
