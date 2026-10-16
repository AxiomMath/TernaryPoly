module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularity.Action

@[expose] public section


/-!
# The rotation action on the coefficients of a Bergman function

The rotation `rotGL θ` acts on the coefficient `coeffPlus F n` of the upper half plane part by
the character `exp ((k + 2 n) θ i)` and on `coeffMinus F n` by its inverse.  Consequently, if
`θ ↦ realRep (rotGL θ) F` has a derivative `D θ` for every `θ` which is itself differentiable at
`0` with derivative `V`, then `coeffPlus V n = -(k + 2 n)² • coeffPlus F n`, and likewise for
`coeffMinus`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Regularity

section Calculus

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [NormedAddCommGroup Y]
  [NormedSpace ℂ Y]

theorem hasDerivAt_ofReal_id (θ : ℝ) : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 θ :=
  (hasDerivAt_id' (x := θ)).ofReal_comp

theorem hasDerivAt_cexp_smul (κ : ℂ) (a : Y) (θ : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (κ * (t : ℂ)) • a)
      ((Complex.exp (κ * (θ : ℂ)) * κ) • a) θ := by
  have h1 : HasDerivAt (fun t : ℝ => κ * (t : ℂ)) (κ * 1) θ :=
    (hasDerivAt_ofReal_id θ).const_mul κ
  have h2 := (h1.cexp).smul_const a
  exact h2.congr_deriv (by rw [mul_one])

/-- If a differentiable curve `R` is carried by a continuous linear map `L` to the exponential
`t ↦ exp (κ t) • a`, and its derivative `D` is differentiable at `0`, then `L` carries the
derivative `V` of `D` at `0` to `κ ^ 2 • a`. -/
theorem second_derivative_of_exp {R D : ℝ → X} {V : X} (L : X →L[ℂ] Y) (κ : ℂ) (a : Y)
    (hR : ∀ θ, HasDerivAt R (D θ) θ) (hV : HasDerivAt D V 0)
    (hform : ∀ θ : ℝ, L (R θ) = Complex.exp (κ * (θ : ℂ)) • a) : L V = (κ ^ 2) • a := by
  have h1 : ∀ θ : ℝ, HasDerivAt (fun t => L (R t)) (L (D θ)) θ := fun θ =>
    (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt θ (hR θ)
  have hfun : (fun t => L (R t)) = fun t : ℝ => Complex.exp (κ * (t : ℂ)) • a := funext hform
  have h4 : ∀ θ : ℝ, L (D θ) = (Complex.exp (κ * (θ : ℂ)) * κ) • a := fun θ => by
    have h3 : HasDerivAt (fun t => L (R t)) ((Complex.exp (κ * (θ : ℂ)) * κ) • a) θ := by
      rw [hfun]
      exact hasDerivAt_cexp_smul κ a θ
    exact (h1 θ).unique h3
  have h5 : HasDerivAt (fun t => L (D t)) (L V) 0 :=
    (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hV
  have hfun2 : (fun t => L (D t)) = fun t : ℝ => (Complex.exp (κ * (t : ℂ)) * κ) • a :=
    funext h4
  have h6 : HasDerivAt (fun t => L (D t))
      (((Complex.exp (κ * ((0 : ℝ) : ℂ)) * κ) * κ) • a) 0 := by
    rw [hfun2]
    have h7 : HasDerivAt (fun t : ℝ => κ * (t : ℂ)) (κ * 1) 0 :=
      (hasDerivAt_ofReal_id 0).const_mul κ
    have h8 := (h7.cexp.mul_const κ).smul_const a
    exact h8.congr_deriv (by rw [mul_one])
  rw [h5.unique h6]
  simp [sq]

end Calculus

section Rotation

variable {k : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem autFactor_rotGL (k : ℕ) (θ : ℝ) (z : ℂ) :
    autFactor k (rotGL θ) z = (denom (rotGL (-θ)) z ^ k)⁻¹ := by
  rw [autFactor, det_rotGL, abs_one, Real.one_rpow, inv_one, Complex.ofReal_one, one_mul,
    rotGL_neg]

theorem realRep_rot_eq (θ : ℝ) (F : BergmanSpace k E) {z : ℂ} (hz : z.im ≠ 0) :
    realRep k E (rotGL θ) F z = (denom (rotGL (-θ)) z ^ k)⁻¹ • F (moeb (rotGL (-θ)) z) := by
  rw [realRep_apply _ F hz, autFactor_rotGL, rotGL_neg]

theorem lowerPart_realRep_rot (θ : ℝ) (F : BergmanSpace k E) {z : ℂ} (hz : z.im ≠ 0) :
    lowerPart (⇑(realRep k E (rotGL θ) F)) z =
      (denom (rotGL θ) z ^ k)⁻¹ • lowerPart (F : ℂ → E) (moeb (rotGL θ) z) := by
  have hz' : (-z).im ≠ 0 := by
    rw [Complex.neg_im]
    exact neg_ne_zero.2 hz
  have h := realRep_rot_eq θ F hz'
  rw [denom_rotGL_neg, moeb_rotGL_neg] at h
  exact h

variable [CompleteSpace E]

theorem coeffPlus_realRep_rot (θ : ℝ) (F : BergmanSpace k E) (n : ℕ) :
    coeffPlus (realRep k E (rotGL θ) F) n =
      Complex.exp ((((k : ℂ) + 2 * n) * θ) * Complex.I) • coeffPlus F n := by
  unfold coeffPlus
  rw [upperCoeff_congr (k := k) (G' := fun z => (denom (rotGL (-θ)) z ^ k)⁻¹ •
      (F : ℂ → E) (moeb (rotGL (-θ)) z))
    (fun z hz => realRep_rot_eq θ F (mem_upper_iff.1 hz).ne') n,
    upperCoeff_rot (-θ) F.differentiableOn_upper n]
  have h : -(((k : ℂ) + 2 * n) * ((-θ : ℝ) : ℂ)) * Complex.I =
      (((k : ℂ) + 2 * n) * θ) * Complex.I := by
    push_cast
    ring
  rw [h]

theorem coeffMinus_realRep_rot (θ : ℝ) (F : BergmanSpace k E) (n : ℕ) :
    coeffMinus (realRep k E (rotGL θ) F) n =
      Complex.exp (-(((k : ℂ) + 2 * n) * θ) * Complex.I) • coeffMinus F n := by
  unfold coeffMinus
  rw [upperCoeff_congr (k := k) (G' := fun z => (denom (rotGL θ) z ^ k)⁻¹ •
      lowerPart (F : ℂ → E) (moeb (rotGL θ) z))
    (fun z hz => lowerPart_realRep_rot θ F (mem_upper_iff.1 hz).ne') n,
    upperCoeff_rot θ F.differentiableOn_lowerPart n]

theorem coeffPlus_of_hasDerivAt_rot (hk : 2 ≤ k) {F V : BergmanSpace k E}
    {D : ℝ → BergmanSpace k E}
    (hD : ∀ θ, HasDerivAt (fun t => realRep k E (rotGL t) F) (D θ) θ)
    (hV : HasDerivAt D V 0) (n : ℕ) :
    coeffPlus V n = -(((k : ℂ) + 2 * n) ^ 2) • coeffPlus F n := by
  have hform : ∀ θ : ℝ, coeffPlusL hk n (realRep k E (rotGL θ) F) =
      Complex.exp ((((k : ℂ) + 2 * n) * Complex.I) * (θ : ℂ)) • coeffPlus F n := by
    intro θ
    rw [coeffPlusL_apply, coeffPlus_realRep_rot,
      show (((k : ℂ) + 2 * n) * (θ : ℂ)) * Complex.I =
        (((k : ℂ) + 2 * n) * Complex.I) * (θ : ℂ) by ring]
  have h := second_derivative_of_exp (coeffPlusL hk n) (((k : ℂ) + 2 * n) * Complex.I)
    (coeffPlus F n) hD hV hform
  rw [coeffPlusL_apply] at h
  rw [h]
  have hsq : (((k : ℂ) + 2 * n) * Complex.I) ^ 2 = -(((k : ℂ) + 2 * n) ^ 2) := by
    rw [mul_pow, Complex.I_sq]
    ring
  rw [hsq]

theorem coeffMinus_of_hasDerivAt_rot (hk : 2 ≤ k) {F V : BergmanSpace k E}
    {D : ℝ → BergmanSpace k E}
    (hD : ∀ θ, HasDerivAt (fun t => realRep k E (rotGL t) F) (D θ) θ)
    (hV : HasDerivAt D V 0) (n : ℕ) :
    coeffMinus V n = -(((k : ℂ) + 2 * n) ^ 2) • coeffMinus F n := by
  have hform : ∀ θ : ℝ, coeffMinusL hk n (realRep k E (rotGL θ) F) =
      Complex.exp ((-(((k : ℂ) + 2 * n) * Complex.I)) * (θ : ℂ)) • coeffMinus F n := by
    intro θ
    rw [coeffMinusL_apply, coeffMinus_realRep_rot,
      show -(((k : ℂ) + 2 * n) * (θ : ℂ)) * Complex.I =
        (-(((k : ℂ) + 2 * n) * Complex.I)) * (θ : ℂ) by ring]
  have h := second_derivative_of_exp (coeffMinusL hk n) (-(((k : ℂ) + 2 * n) * Complex.I))
    (coeffMinus F n) hD hV hform
  rw [coeffMinusL_apply] at h
  rw [h]
  have hsq : (-(((k : ℂ) + 2 * n) * Complex.I)) ^ 2 = -(((k : ℂ) + 2 * n) ^ 2) := by
    rw [neg_sq, mul_pow, Complex.I_sq]
    ring
  rw [hsq]

end Rotation

end TernaryPeriodPolynomials.Regularity

end
