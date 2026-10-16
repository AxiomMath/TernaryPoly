module

public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Line.Refl

@[expose] public section


/-!
# The line reflection on the seed: `r^* σ_h = (-1)ⁿ ρ(r) \overline{σ_{h^*}}` (LS10, part 2)

For `h, h^*` holomorphic on `ℍ` with `h^*(z) = \overline{h(-\bar z)}`, the reflection `r = diag(1; -1, 1)` of the line face
(`reflFCLM`, `τ ↦ -\bar τ`) satisfies, pointwise on the face, with `ρ(r) = lreflCoef`:

* `pullRaw_lrefl_dEta`: `r^* σ_h = (-1)ⁿ ρ(r) \overline{σ_{h^*}}`;
* `pullForm_lrefl_seed` (as closed forms) and `pullForm_lrefl_conjSeed`: `r^* \overline{σ_{h^*}} = (-1)ⁿ ρ(r) σ_h`.

(The sign is `(-1)ⁿ`, versus `(-1)^{n+1}` for the plane: the factor `-1` from `r^*dτ = -d\bar τ`, the factor `(-1)^{n+1}`
from `ρ(r) \overline{P_τ}ⁿ = (-1)^{n+1} P_{-\bar τ}ⁿ`, and `r^*(τ dw₁ + dw₂) = \overline{τ dw₁ + dw₂}`.)

Formalized by Claude Sonnet 5.5.
-/

open MvPolynomial ComplexConjugate
open TernaryPoly.SmoothLocalDeRham TernaryPoly.SmoothCoveringDeRham
open scoped ContDiff

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LineSeed

open TernaryPeriodPolynomials.Argument.SeedC3 TernaryPeriodPolynomials.Argument.SeedC3.Psi

theorem faceTau_refl (x : Face) : faceTau (reflFCLM x) = -conj (faceTau x) := by
  apply Complex.ext
  · simp [faceTau, reflFCLM_apply, reflFSign]
  · simp [faceTau, reflFCLM_apply, reflFSign]

theorem dtau_refl (v : Face) : dtau (reflFCLM v) = -conj (dtau v) := by
  apply Complex.ext
  · simp [dtau_apply, reflFCLM_apply, reflFSign]
  · simp [dtau_apply, reflFCLM_apply, reflFSign]

theorem reflFCLM_zero (v : Face) : reflFCLM v 0 = -v 0 := by simp [reflFCLM_apply, reflFSign]
theorem reflFCLM_one (v : Face) : reflFCLM v 1 = v 1 := by simp [reflFCLM_apply, reflFSign]

open TernaryPoly.SmoothLocalDeRham in
/-- The coefficient polynomial of `dη` on an arbitrary pair `(v, w)` of tangent vectors. -/
theorem toPoly_d_lineEtaForm_apply (h : ℂ → ℂ) (n : ℕ) (hh : DifferentiableOn ℂ h upperSet) {x : Face}
    (hx : x ∈ faceSet) (v w : Face) :
    Coef.toPoly ((d isOpen_faceSet 1 (lineEtaForm h n hh) : RawForm Face (Coef n) 2) x ![v, w]) =
      C (h (faceTau x) * ((faceTau x * (v 0 : ℂ) + (v 1 : ℂ)) * dtau w -
        (faceTau x * (w 0 : ℂ) + (w 1 : ℂ)) * dtau v)) * Ppoly (faceTau x) ^ n := by
  rw [d_apply isOpen_faceSet _ hx]
  have heq : (lineEtaForm h n hh : RawForm Face (Coef n) 1) =ᶠ[nhds x] lineEtaRaw h n := by
    filter_upwards [isOpen_faceSet.mem_nhds hx] with y hy using restrictForm_apply _ _ hy
  rw [heq.extDeriv_eq (𝕜 := ℝ), toPoly_extDeriv_lineEtaRaw h hh n hx]

theorem pullRaw_lrefl_apply {n : ℕ} (W : RawForm Face (Coef n) 2) (x v w : Face) :
    pullRaw reflFCLM W x ![v, w] = W (reflFCLM x) ![reflFCLM v, reflFCLM w] := by
  change W (reflFCLM x) (fun k => (fderiv ℝ (⇑reflFCLM) x) (![v, w] k)) = _
  rw [reflFCLM.fderiv]
  congr 1
  funext k
  fin_cases k <;> rfl

theorem pullRaw_lrefl_dEta (n : ℕ) (h hs : ℂ → ℂ) (hh : DifferentiableOn ℂ h upperSet)
    (hhs : DifferentiableOn ℂ hs upperSet)
    (hrel : ∀ z : ℂ, 0 < z.im → hs z = conj (h (-conj z))) {x : Face} (hx : x ∈ faceSet) :
    pullRaw reflFCLM (d isOpen_faceSet 1 (lineEtaForm h n hh) : RawForm Face (Coef n) 2) x =
      ((-1 : ℝ) ^ n) • coefficientFormMap ((lreflCoefCLM n).comp (conjCLM n)) 2
        ((d isOpen_faceSet 1 (lineEtaForm hs n hhs) : RawForm Face (Coef n) 2) x) := by
  apply ContinuousAlternatingMap.ext
  intro vv
  have hv : vv = ![vv 0, vv 1] := by
    funext k
    fin_cases k <;> rfl
  rw [hv]
  generalize vv 0 = v
  generalize vv 1 = w
  apply Coef.toPoly_injective
  have e2 : ∀ (c : ℝ) (y : Coef n), Coef.toPoly (c • y) = C (c : ℂ) * Coef.toPoly y := by
    intro c y
    have : c • y = ((c : ℂ) • y : Coef n) := (Complex.coe_smul c y).symm
    rw [this, Coef.toPoly_smul]
  have e3 : (((-1 : ℝ) ^ n) • coefficientFormMap ((lreflCoefCLM n).comp (conjCLM n)) 2
        ((d isOpen_faceSet 1 (lineEtaForm hs n hhs) : RawForm Face (Coef n) 2) x))
          ![v, w] =
        ((-1 : ℝ) ^ n) • lreflCoef n (Coef.conjCoef
          (((d isOpen_faceSet 1 (lineEtaForm hs n hhs) : RawForm Face (Coef n) 2) x) ![v, w])) := rfl
  rw [pullRaw_lrefl_apply, toPoly_d_lineEtaForm_apply h n hh (reflFCLM_mem hx), e3, e2,
    toPoly_lreflCoef, Coef.toPoly_conjCoef, toPoly_d_lineEtaForm_apply hs n hhs hx,
    faceTau_refl, dtau_refl, dtau_refl, reflFCLM_zero, reflFCLM_zero, reflFCLM_one, reflFCLM_one]
  have hτ := hrel (faceTau x) (faceTau_im hx)
  set t := faceTau x
  set S : ℂ := (t * (v 0 : ℂ) + (v 1 : ℂ)) * dtau w - (t * (w 0 : ℂ) + (w 1 : ℂ)) * dtau v with hS
  have hP := rho_lrefl_conjPpoly_pow t n
  have step : C (-1 : ℂ) * bind₁ (![X 0, -X 1, X 2] : Fin 3 → MvPolynomial (Fin 3) ℂ)
      (MvPolynomial.map (starRingEnd ℂ) (C (hs t * S) * Ppoly t ^ n)) =
      C (conj (hs t * S)) * (C ((-1 : ℂ) ^ (n + 1)) * Ppoly (-conj t) ^ n) := by
    rw [← hP, map_mul, MvPolynomial.map_C, map_mul, bind₁_C_right]
    ring
  rw [step, ← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul]
  congr 2
  rw [hτ, hS]
  simp only [map_sub, map_mul, map_add, Complex.conj_ofReal, Complex.conj_conj,
    Complex.ofReal_pow, Complex.ofReal_neg, Complex.ofReal_one]
  have hu : ((-1 : ℂ) ^ n) * ((-1 : ℂ) ^ n) = 1 := by rw [← mul_pow]; norm_num
  rw [pow_succ]
  linear_combination (h (-conj t) * ((conj t * (v 0 : ℂ) + (v 1 : ℂ)) * conj (dtau w) -
      (conj t * (w 0 : ℂ) + (w 1 : ℂ)) * conj (dtau v))) * hu

open ZigZag in
/-- **The line reflection on the seed, as closed forms:** `r^* σ_h = (-1)ⁿ ρ(r) \overline{σ_{h^*}}`. -/
theorem pullForm_lrefl_seed (n : ℕ) (h hs : ℂ → ℂ) (hh : DifferentiableOn ℂ h upperSet)
    (hhs : DifferentiableOn ℂ hs upperSet)
    (hrel : ∀ z : ℂ, 0 < z.im → hs z = conj (h (-conj z))) :
    pullForm isOpen_faceSet reflAction reflGen 2 (d isOpen_faceSet 1 (lineEtaForm h n hh)) =
      ((-1 : ℝ) ^ n) • twForm ((lreflCoefCLM n).comp (conjCLM n)) 2
        (d isOpen_faceSet 1 (lineEtaForm hs n hhs)) := by
  apply Form.ext
  intro x hx
  rw [pullForm_apply isOpen_faceSet reflAction reflGen _ hx]
  have h1 : reflAction.act reflGen = ⇑reflFCLM := funext reflAction_act_gen
  rw [h1]
  change _ = ((-1 : ℝ) ^ n) • (twForm ((lreflCoefCLM n).comp (conjCLM n)) 2
        (d isOpen_faceSet 1 (lineEtaForm hs n hhs)) : RawForm Face (Coef n) 2) x
  rw [twForm_apply]
  exact pullRaw_lrefl_dEta n h hs hh hhs hrel hx

open ZigZag in
/-- The same for the conjugate seed: `r^* \overline{σ_{h^*}} = (-1)ⁿ ρ(r) σ_h`. -/
theorem pullForm_lrefl_conjSeed (n : ℕ) (h hs : ℂ → ℂ) (hh : DifferentiableOn ℂ h upperSet)
    (hhs : DifferentiableOn ℂ hs upperSet)
    (hrel : ∀ z : ℂ, 0 < z.im → hs z = conj (h (-conj z))) :
    pullForm isOpen_faceSet reflAction reflGen 2
        (twForm (conjCLM n) 2 (d isOpen_faceSet 1 (lineEtaForm hs n hhs))) =
      ((-1 : ℝ) ^ n) • twForm (lreflCoefCLM n) 2 (d isOpen_faceSet 1 (lineEtaForm h n hh)) := by
  have hrel' : ∀ z : ℂ, 0 < z.im → h z = conj (hs (-conj z)) := by
    intro z hz
    have hz' : 0 < (-conj z).im := by simpa using hz
    rw [hrel _ hz']
    simp
  rw [pullForm_twForm, pullForm_lrefl_seed n hs h hhs hh hrel', map_smul, ← twForm_mul,
    ← ContinuousLinearMap.comp_assoc, conjCLM_comp_lreflCoefCLM, ContinuousLinearMap.comp_assoc,
    conjCLM_comp_conjCLM, ContinuousLinearMap.comp_id]

end TernaryPeriodPolynomials.Argument.LineSeed
