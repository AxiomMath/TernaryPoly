module

public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Line.Theta

@[expose] public section


/-!
# The primitives `θ_g` as chart zero-forms, and `dθ_g = g^*η - ρ(g)η` (LS6, part 2)

Formalized by Claude Sonnet 5.5.
-/

open MvPolynomial
open scoped ContDiff

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LineSeed

open TernaryPeriodPolynomials.Argument.SeedC3 TernaryPeriodPolynomials.Argument.SeedC3.Psi
open TernaryPeriodPolynomials.Argument.SeedC3.Calc

namespace LineData

variable {G : Type} [Group G] (D : LineData G) (h : ℂ → ℂ) (n : ℕ) (Gm : ℕ → ℂ → ℂ)

/-- **The defect of `Ψ` is the derivative of `θ_g`** (in `E_n`). -/
theorem defect_coef (g : G) {x : Face} (hx : x ∈ faceSet)
    (hmod : h (mob (D.lam g) (faceTau x)) = dnm (D.lam g) (faceTau x) ^ (n + 3) * h (faceTau x)) :
    ((dnm (D.lam g) (faceTau x))⁻¹ ^ 2) • linePsiVal h n (D.act g x) -
        D.rhoCoef n g (linePsiVal h n x) = D.thetaDeriv h n g (faceTau x) := by
  apply Coef.toPoly_injective
  rw [Coef.toPoly_sub, Coef.toPoly_smul, D.toPoly_rhoCoef, D.toPoly_thetaDeriv]
  exact D.defect_poly h n g hx hmod

theorem thetaFun_hasFDerivAt (g : G) (hG : ∀ j z, 0 < z.im → HasDerivAt (Gm j) (h z * z ^ j) z)
    {x : Face} (hx : x ∈ faceSet) :
    HasFDerivAt (D.thetaFun n Gm g)
      (∑ k ∈ Finset.range (n + 1),
        ((D.thetaScalar n g k (h (faceTau x) * faceTau x ^ (k + 1)) (h (faceTau x) * faceTau x ^ k)) • dtau).smulRight
          (D.thetaVec n g k)) x := by
  have hτ : HasFDerivAt faceTau dtau x := by
    have : faceTau = ⇑dtau := funext faceTau_eq
    rw [this]; exact dtau.hasFDerivAt
  unfold thetaFun
  refine HasFDerivAt.fun_sum (u := Finset.range (n + 1)) (x := x)
    (A := fun k y => D.thetaScalar n g k (Gm (k + 1) (faceTau y)) (Gm k (faceTau y)) • D.thetaVec n g k)
    (A' := fun k => ((D.thetaScalar n g k (h (faceTau x) * faceTau x ^ (k + 1)) (h (faceTau x) * faceTau x ^ k)) •
      dtau).smulRight (D.thetaVec n g k)) (fun k _ => ?_)
  have hA : HasFDerivAt (fun y => Gm (k + 1) (faceTau y)) ((h (faceTau x) * faceTau x ^ (k + 1)) • dtau) x :=
    (hG (k + 1) (faceTau x) (faceTau_im hx)).comp_hasFDerivAt x hτ
  have hB : HasFDerivAt (fun y => Gm k (faceTau y)) ((h (faceTau x) * faceTau x ^ k) • dtau) x :=
    (hG k (faceTau x) (faceTau_im hx)).comp_hasFDerivAt x hτ
  have hs := (((hA.const_mul (D.v g 0 : ℂ)).add (hB.const_mul (D.v g 1 : ℂ))).const_mul
    ((n.choose k : ℂ) * (-1) ^ (n - k)))
  have hs' : HasFDerivAt (fun y => D.thetaScalar n g k (Gm (k + 1) (faceTau y)) (Gm k (faceTau y)))
      ((D.thetaScalar n g k (h (faceTau x) * faceTau x ^ (k + 1)) (h (faceTau x) * faceTau x ^ k)) • dtau) x := by
    refine hs.congr_fderiv ?_
    ext v
    simp only [thetaScalar, smul_apply, add_apply, smul_eq_mul]
    ring
  exact hs'.smul_const (D.thetaVec n g k)

theorem thetaDeriv_eq_sum (g : G) (τ : ℂ) :
    D.thetaDeriv h n g τ = ∑ k ∈ Finset.range (n + 1),
      D.thetaScalar n g k (h τ * τ ^ (k + 1)) (h τ * τ ^ k) • D.thetaVec n g k := rfl

theorem thetaFun_fderiv_apply (g : G) (hG : ∀ j z, 0 < z.im → HasDerivAt (Gm j) (h z * z ^ j) z)
    {x : Face} (hx : x ∈ faceSet) (v : Face) :
    fderiv ℝ (D.thetaFun n Gm g) x v = dtau v • D.thetaDeriv h n g (faceTau x) := by
  rw [(D.thetaFun_hasFDerivAt h n Gm g hG hx).fderiv, thetaDeriv_eq_sum]
  simp only [sum_apply, ContinuousLinearMap.smulRight_apply, smul_apply,
    smul_eq_mul, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm]

theorem thetaFun_contDiffOn (g : G) (hG : ∀ j z, 0 < z.im → HasDerivAt (Gm j) (h z * z ^ j) z) :
    ContDiffOn ℝ ∞ (D.thetaFun n Gm g) faceSet := by
  unfold thetaFun
  refine ContDiffOn.sum fun k _ => ?_
  have hGm : ∀ j, ContDiffOn ℝ ∞ (fun y : Face => Gm j (faceTau y)) faceSet := fun j => by
    have hd : DifferentiableOn ℂ (Gm j) upperSet := fun z hz =>
      (hG j z hz).differentiableAt.differentiableWithinAt
    have h1 : ContDiffOn ℂ ∞ (Gm j) upperSet := hd.contDiffOn isOpen_upperSet
    exact (h1.restrict_scalars ℝ).comp contDiff_faceTau.contDiffOn fun x hx => faceTau_mem_upper hx
  have hs : ContDiffOn ℝ ∞ (fun y : Face => D.thetaScalar n g k (Gm (k + 1) (faceTau y)) (Gm k (faceTau y)))
      faceSet := by
    unfold thetaScalar
    exact contDiffOn_const.mul ((contDiffOn_const.mul (hGm (k + 1))).add (contDiffOn_const.mul (hGm k)))
  exact hs.smul_const _

/-- The real form of `ρ` acts as the complex one. -/
theorem repCLM_rhoR (g : G) (q : Coef n) : ZigZag.repCLM (D.rhoR n) g q = D.rhoCoef n g q := rfl

open TernaryPoly.SmoothLocalDeRham TernaryPoly.SmoothCoveringDeRham ZigZag in
/-- The primitive `θ_g` as a chart zero-form. -/
def thetaForm (g : G) (hG : ∀ j z, 0 < z.im → HasDerivAt (Gm j) (h z * z ^ j) z) :
    Form (F := Coef n) faceSet 0 :=
  ofFunction (D.thetaFun n Gm g) (D.thetaFun_contDiffOn h n Gm g hG)

open TernaryPoly.SmoothLocalDeRham TernaryPoly.SmoothCoveringDeRham ZigZag in
/-- **`dθ_g = g^*η - ρ(g)η`.** -/
theorem dTheta_eq (hh : DifferentiableOn ℂ h upperSet)
    (hG : ∀ j z, 0 < z.im → HasDerivAt (Gm j) (h z * z ^ j) z)
    (hmod : ∀ g : G, ∀ z : ℂ, 0 < z.im →
      h (mob (D.lam g) z) = dnm (D.lam g) z ^ (n + 3) * h z) (g : G) :
    d isOpen_faceSet 0 (D.thetaForm h n Gm g hG) =
      pullForm isOpen_faceSet D.action g 1 (lineEtaForm h n hh) -
        twForm (repCLM (D.rhoR n) g) 1 (lineEtaForm h n hh) := by
  apply Form.ext
  intro x hx
  have hax : D.act g x ∈ faceSet := D.act_mapsTo g hx
  rw [thetaForm, d_ofFunction isOpen_faceSet _ _ hx]
  have hsub : ((pullForm isOpen_faceSet D.action g 1 (lineEtaForm h n hh) -
      twForm (repCLM (D.rhoR n) g) 1 (lineEtaForm h n hh) : Form (F := Coef n) faceSet 1) :
        RawForm Face (Coef n) 1) x =
      (pullForm isOpen_faceSet D.action g 1 (lineEtaForm h n hh) : RawForm Face (Coef n) 1) x -
      (twForm (repCLM (D.rhoR n) g) 1 (lineEtaForm h n hh) : RawForm Face (Coef n) 1) x := rfl
  rw [hsub, pullForm_apply isOpen_faceSet D.action g _ hx, twForm_apply]
  ext u
  have e1 : (lineEtaForm h n hh : RawForm Face (Coef n) 1) (D.act g x) = lineEtaRaw h n (D.act g x) :=
    restrictForm_apply _ _ hax
  have e2 : (lineEtaForm h n hh : RawForm Face (Coef n) 1) x = lineEtaRaw h n x :=
    restrictForm_apply _ _ hx
  have hmod' := hmod g (faceTau x) (faceTau_im hx)
  have hdef := D.defect_coef h n g hx hmod'
  simp only [pullRaw, e2, ContinuousAlternatingMap.sub_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, coefficientFormMap_apply, lineEtaRaw]
  have e1' : (lineEtaForm h n hh : RawForm Face (Coef n) 1) (D.action.act g x) =
      lineEtaRaw h n (D.act g x) := e1
  rw [e1']
  simp [lineEtaRaw, etaCLM, etaLin, repCLM_rhoR]
  have hdt : dtau ((fderiv ℝ (D.action.act g) x) (u 0)) =
      ((dnm (D.lam g) (faceTau x))⁻¹) ^ 2 * dtau (u 0) := by
    rw [inv_pow]; exact D.dtau_fderiv_act g hx (u 0)
  rw [D.thetaFun_fderiv_apply h n Gm g hG hx, ← hdef, hdt, smul_sub, smul_smul]
  congr 1
  ring_nf

end LineData

end TernaryPeriodPolynomials.Argument.LineSeed
