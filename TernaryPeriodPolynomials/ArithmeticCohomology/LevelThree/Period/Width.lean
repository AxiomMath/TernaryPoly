module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Period.Primitive
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.SymFixed

@[expose] public section


/-!
# Periods of the Eichler integral over one width

Let `g` be holomorphic on the upper half-plane, periodic of period `w > 0`, and tending to zero at
`i∞`. Then the coefficient of `X₀^m` of its Eichler integral (`primitive m g`, the functional
`p ↦ p(1, 0)`) is itself periodic of period `w` (`coord_primitive_periodic`). Indeed
`F(z + w) - F(z)` has derivative `g(z + w) - g(z) = 0`, so it is a constant `c`; but for `z` of
large imaginary part `F(z + w) - F(z) = ∫₀^w g(z + t) dt` is small.

This is the analytic input for the parabolicity of the period cocycle at the cusp `∞`, and, after
conjugating by `S`, at the cusp `0`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein Matrix MvPolynomial UpperHalfPlane MeasureTheory
open scoped Manifold ModularForm
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodPrimitive

namespace TernaryPeriodPolynomials.LevelThree.LevelThreePeriodWidth

variable (m : ℕ)

/-- The functional `p ↦ p(1, 0)` on `Sym^m`. -/
def ell0 : V m →ₗ[ℂ] ℂ := SymFixed.evalAt ![1, 0]

/-- The functional `p ↦ p(0, 1)` on `Sym^m`. -/
def ell1 : V m →ₗ[ℂ] ℂ := SymFixed.evalAt ![0, 1]

theorem ell0_apply (p : V m) : ell0 m p = eval ![1, 0] p.val := rfl

theorem ell1_apply (p : V m) : ell1 m p = eval ![0, 1] p.val := rfl

theorem ell0_binaryPointPower (z : ℂ) : ell0 m (binaryPointPower m z) = 1 := by
  rw [ell0_apply]
  simp [binaryPointPower]

theorem ell0_pointForm (g : ℍ → ℂ) (z : ℂ) : ell0 m (pointForm m g z) = g (ofComplex z) := by
  rw [pointForm, map_smul, ell0_binaryPointPower, smul_eq_mul, mul_one]

/-- The `X₀^m`-coordinate of the Eichler integral is a primitive of `g`. -/
theorem ell0_hasDerivAt {g : ℍ → ℂ} (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) (z : ℂ)
    (hz : 0 < z.im) :
    HasDerivAt (fun w => ell0 m (primitive m g w)) (g (ofComplex z)) z := by
  have h := primitive_isPrimitive m hg (ell0 m) z hz
  rwa [ell0_pointForm] at h

/-- `F(z + w) - F(z)` is constant on the upper half-plane for `w`-periodic `g`. -/
theorem coord_difference_const {g : ℍ → ℂ} (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) (w : ℝ)
    (hper : Function.Periodic (g ∘ ofComplex) (w : ℂ)) (z : ℂ) (hz : 0 < z.im) :
    ell0 m (primitive m g (z + w)) - ell0 m (primitive m g z) =
      ell0 m (primitive m g (Complex.I + w)) - ell0 m (primitive m g Complex.I) := by
  have hF := ell0_hasDerivAt m hg
  have deriv : ∀ x : ℂ, 0 < x.im →
      HasDerivAt (fun x => ell0 m (primitive m g (x + w)) - ell0 m (primitive m g x)) 0 x := by
    intro x hx
    have hx' : 0 < (x + w).im := by simpa using hx
    have h1 : HasDerivAt (fun x => ell0 m (primitive m g (x + w))) (g (ofComplex (x + w))) x :=
      (hF (x + w) hx').comp_add_const x (w : ℂ)
    have h2 := h1.sub (hF x hx)
    have h3 : g (ofComplex (x + w)) - g (ofComplex x) = 0 := sub_eq_zero.mpr (hper x)
    rwa [h3] at h2
  apply (convex_halfSpace_im_gt 0).is_const_of_fderivWithin_eq_zero
    (f := fun x => ell0 m (primitive m g (x + w)) - ell0 m (primitive m g x))
    (fun x hx => (deriv x hx).differentiableAt.differentiableWithinAt)
    (fun x hx => ?_) hz (by simp)
  rw [fderivWithin_of_isOpen UpperHalfPlane.isOpen_upperHalfPlaneSet hx]
  simpa using (deriv x hx).hasFDerivAt.fderiv

/-- **Periodicity of the `X₀^m`-coordinate.** If `g` is holomorphic, `w`-periodic and tends to zero
at `i∞`, the `X₀^m`-coordinate of its Eichler integral is `w`-periodic. -/
theorem coord_primitive_periodic {g : ℍ → ℂ} (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) (w : ℝ)
    (hw : 0 < w) (hper : Function.Periodic (g ∘ ofComplex) (w : ℂ))
    (hzero : IsZeroAtImInfty g) (z : ℂ) (hz : 0 < z.im) :
    ell0 m (primitive m g (z + w)) = ell0 m (primitive m g z) := by
  rw [← sub_eq_zero]
  by_contra hc
  have hcpos : 0 < ‖ell0 m (primitive m g (z + w)) - ell0 m (primitive m g z)‖ :=
    norm_pos_iff.mpr hc
  set ε : ℝ := ‖ell0 m (primitive m g (z + w)) - ell0 m (primitive m g z)‖ / (2 * w) with hε
  have hεpos : 0 < ε := by positivity
  obtain ⟨A, hA⟩ : ∃ A : ℝ, ∀ x : ℍ, A ≤ x.im → ‖g x‖ ≤ ε := by
    have hz' : Filter.Tendsto g UpperHalfPlane.atImInfty (nhds (0 : ℂ)) := hzero
    have h := hz'.eventually (Metric.closedBall_mem_nhds (0 : ℂ) hεpos)
    obtain ⟨A, hA⟩ := (UpperHalfPlane.atImInfty_mem _).mp h
    exact ⟨A, fun x hx => by simpa using hA x hx⟩
  let z0 : ℂ := Complex.I * ((max A 1 : ℝ) : ℂ)
  have hz0 : 0 < z0.im := by
    simp only [z0, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im]
    simp
  have hconst := coord_difference_const m hg w hper z hz
  have hconst0 := coord_difference_const m hg w hper z0 hz0
  have hF := ell0_hasDerivAt m hg
  have hcont : ContinuousOn (g ∘ ofComplex) {z : ℂ | 0 < z.im} :=
    (UpperHalfPlane.mdifferentiable_iff.mp hg).continuousOn
  have path : Continuous (fun t : ℝ => z0 + (t : ℂ)) := by fun_prop
  have image : ∀ t : ℝ, z0 + (t : ℂ) ∈ {z : ℂ | 0 < z.im} := fun t => by simpa using hz0
  have integrable : IntervalIntegrable (fun t : ℝ => g (ofComplex (z0 + (t : ℂ)))) volume 0 w :=
    (hcont.comp path.continuousOn (fun t _ => image t)).intervalIntegrable
  have derivative : ∀ t ∈ Set.uIcc (0 : ℝ) w,
      HasDerivAt (fun t : ℝ => ell0 m (primitive m g (z0 + (t : ℂ))))
        (g (ofComplex (z0 + (t : ℂ)))) t := by
    intro t _
    exact ((hF (z0 + (t : ℂ)) (image t)).comp_const_add z0 (t : ℂ)).comp_ofReal
  have integral := intervalIntegral.integral_eq_sub_of_hasDerivAt derivative integrable
  have bound : ‖∫ t in (0 : ℝ)..w, g (ofComplex (z0 + (t : ℂ)))‖ ≤ ε * |w - 0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t _
    let pt : ℍ := ⟨z0 + (t : ℂ), image t⟩
    have hpt : ofComplex (z0 + (t : ℂ)) = pt := ofComplex_apply pt
    rw [hpt]
    apply hA
    show A ≤ (z0 + (t : ℂ)).im
    simp [z0]
  rw [integral] at bound
  simp only [Complex.ofReal_zero, add_zero] at bound
  have hsame : ell0 m (primitive m g (z0 + w)) - ell0 m (primitive m g z0) =
      ell0 m (primitive m g (z + w)) - ell0 m (primitive m g z) := hconst0.trans hconst.symm
  rw [hsame] at bound
  have hw0 : w ≠ 0 := hw.ne'
  have hhalf : ε * |w - 0| =
      ‖ell0 m (primitive m g (z + w)) - ell0 m (primitive m g z)‖ / 2 := by
    rw [sub_zero, abs_of_pos hw, hε]
    field_simp
  linarith

end TernaryPeriodPolynomials.LevelThree.LevelThreePeriodWidth
