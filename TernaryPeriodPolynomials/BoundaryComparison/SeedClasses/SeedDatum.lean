module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.SeedTheta
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.ZigZagMain
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.EichlerClass

@[expose] public section


/-!
# The zig-zag datum of the seed

Paper: Lemma C.3 (`ar:lem:seed`),
the class of the seed `ω_h` in `H²(Γ_P, E_n)` via the Čech--de Rham zig-zag.

Face model: `η = Ψ dτ` with `dη = ω_h` (`SeedPsi`), `θ_g = Θ_g(τ)` with
`dθ_g = g^*η - ρ(g)η` (`dTheta_eq`), packaged as a `ZigZag.Datum` (`seedDatum`).

Formalized by Claude Sonnet 5.5.
-/

open MvPolynomial
open scoped ContDiff

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3

open Calc Psi

namespace PlaneData

variable {G : Type} [Group G] (D : PlaneData G)

/-- `dτ` after the action of `g`: `dτ ∘ D(g) = (cτ+d)^{-2} dτ`. -/
theorem dtau_fderiv_act (g : G) {x : Face} (hx : x ∈ faceSet) (v : Face) :
    dtau (fderiv ℝ (D.act g) x v) = (dnm (D.lam g) (faceTau x) ^ 2)⁻¹ * dtau v := by
  have hdet := D.det_one g
  have hτ : HasFDerivAt faceTau dtau x := by
    have : faceTau = ⇑dtau := funext faceTau_eq
    rw [this]; exact dtau.hasFDerivAt
  have hact : DifferentiableAt ℝ (D.act g) x :=
    (((D.act_contDiffOn g) x hx).contDiffAt (isOpen_faceSet.mem_nhds hx)).differentiableAt (by simp)
  have h1 : HasFDerivAt (fun y => dtau (D.act g y)) (dtau.comp (fderiv ℝ (D.act g) x)) x :=
    dtau.hasFDerivAt.comp x hact.hasFDerivAt
  have h2 : HasFDerivAt (fun y => mob (D.lam g) (faceTau y))
      (((1 / dnm (D.lam g) (faceTau x) ^ 2) : ℂ) • dtau) x :=
    (mob_hasDerivAt (D.lam g) hdet (faceTau_im hx)).comp_hasFDerivAt x hτ
  have hfun : (fun y => dtau (D.act g y)) = fun y => mob (D.lam g) (faceTau y) := by
    funext y
    rw [← faceTau_eq, D.faceTau_act]
  rw [hfun] at h1
  have := h1.unique h2
  have := congrArg (fun L => L v) this
  simpa [one_div] using this

variable (h : ℂ → ℂ) (n : ℕ) (Gm : ℕ → ℂ → ℂ)

/-- `Θ_g(τ) = Σ_j G_j(τ) m_j(g)` as a function on the face. -/
def thetaFun (g : G) (x : Face) : Coef n :=
  ∑ j ∈ Finset.range (n + 2), Gm j (faceTau x) • D.thetaVec n g j

theorem thetaFun_hasFDerivAt (g : G) (hG : ∀ j z, 0 < z.im → HasDerivAt (Gm j) (h z * z ^ j) z)
    {x : Face} (hx : x ∈ faceSet) :
    HasFDerivAt (D.thetaFun n Gm g)
      (∑ j ∈ Finset.range (n + 2), ((h (faceTau x) * faceTau x ^ j) • dtau).smulRight
        (D.thetaVec n g j)) x := by
  have hτ : HasFDerivAt faceTau dtau x := by
    have : faceTau = ⇑dtau := funext faceTau_eq
    rw [this]; exact dtau.hasFDerivAt
  unfold thetaFun
  have := HasFDerivAt.fun_sum (u := Finset.range (n + 2)) (x := x)
    (A := fun j y => Gm j (faceTau y) • D.thetaVec n g j)
    (A' := fun j => ((h (faceTau x) * faceTau x ^ j) • dtau).smulRight (D.thetaVec n g j))
    (fun j _ => ((hG j (faceTau x) (faceTau_im hx)).comp_hasFDerivAt x hτ).smul_const
      (D.thetaVec n g j))
  simpa using this

theorem thetaFun_fderiv_apply (g : G) (hG : ∀ j z, 0 < z.im → HasDerivAt (Gm j) (h z * z ^ j) z)
    {x : Face} (hx : x ∈ faceSet) (v : Face) :
    fderiv ℝ (D.thetaFun n Gm g) x v = dtau v • D.thetaDeriv n h g (faceTau x) := by
  rw [(D.thetaFun_hasFDerivAt h n Gm g hG hx).fderiv]
  simp only [thetaDeriv, FunLike.coe_sum, Finset.sum_apply,
    ContinuousLinearMap.smulRight_apply, smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]

theorem thetaFun_contDiffOn (g : G)
    (hG : ∀ j z, 0 < z.im → HasDerivAt (Gm j) (h z * z ^ j) z) :
    ContDiffOn ℝ ∞ (D.thetaFun n Gm g) faceSet := by
  unfold thetaFun
  refine ContDiffOn.sum fun j _ => ?_
  have hd : DifferentiableOn ℂ (Gm j) upperSet := fun z hz =>
    (hG j z hz).differentiableAt.differentiableWithinAt
  have h1 : ContDiffOn ℂ ∞ (Gm j) upperSet := hd.contDiffOn isOpen_upperSet
  exact ((h1.restrict_scalars ℝ).comp contDiff_faceTau.contDiffOn
    fun x hx => faceTau_mem_upper hx).smul_const _

/-- The real form of the coefficient representation on `Coef n`. -/
def rhoR (n : ℕ) : Representation ℝ G (Coef n) where
  toFun g := (D.rhoCoef n g).restrictScalars ℝ
  map_one' := by
    ext q
    change D.rhoC n 1 q = q
    rw [map_one]; rfl
  map_mul' g k := by
    ext q
    change D.rhoC n (g * k) q = D.rhoC n g (D.rhoC n k q)
    rw [map_mul]; rfl

theorem rhoR_apply (n : ℕ) (g : G) (q : Coef n) : D.rhoR n g q = D.rhoCoef n g q := rfl

theorem repCLM_rhoR (n : ℕ) (g : G) (q : Coef n) :
    ZigZag.repCLM (D.rhoR n) g q = D.rhoCoef n g q := rfl

open TernaryPoly.SmoothLocalDeRham ZigZag in
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
      pullForm isOpen_faceSet D.action g 1 (etaForm h hh n) -
        twForm (repCLM (D.rhoR n) g) 1 (etaForm h hh n) := by
  apply Form.ext
  intro x hx
  have hax : D.act g x ∈ faceSet := D.act_mapsTo g hx
  rw [thetaForm, d_ofFunction isOpen_faceSet _ _ hx]
  have hsub : ((pullForm isOpen_faceSet D.action g 1 (etaForm h hh n) -
      twForm (repCLM (D.rhoR n) g) 1 (etaForm h hh n) : Form (F := Coef n) faceSet 1) :
        RawForm Face (Coef n) 1) x =
      (pullForm isOpen_faceSet D.action g 1 (etaForm h hh n) : RawForm Face (Coef n) 1) x -
      (twForm (repCLM (D.rhoR n) g) 1 (etaForm h hh n) : RawForm Face (Coef n) 1) x := rfl
  rw [hsub, pullForm_apply isOpen_faceSet D.action g _ hx, twForm_apply]
  ext u
  have e1 : (etaForm h hh n : RawForm Face (Coef n) 1) (D.act g x) = etaRaw h n (D.act g x) :=
    restrictForm_apply _ _ hax
  have e2 : (etaForm h hh n : RawForm Face (Coef n) 1) x = etaRaw h n x :=
    restrictForm_apply _ _ hx
  have hmod' := hmod g (faceTau x) (faceTau_im hx)
  have hdef := D.defect_coef h n g hx hmod'
  simp only [pullRaw, e2, ContinuousAlternatingMap.sub_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, coefficientFormMap_apply, etaRaw]
  have e1' : (etaForm h hh n : RawForm Face (Coef n) 1) (D.action.act g x) =
      etaRaw h n (D.act g x) := e1
  rw [e1']
  simp [etaRaw, etaCLM, etaLin, repCLM_rhoR]
  have hdt : dtau ((fderiv ℝ (D.action.act g) x) (u 0)) =
      ((dnm (D.lam g) (faceTau x))⁻¹) ^ 2 * dtau (u 0) := by
    rw [inv_pow]; exact D.dtau_fderiv_act g hx (u 0)
  rw [D.thetaFun_fderiv_apply h n Gm g hG hx, ← hdef, hdt, smul_sub, smul_smul]
  congr 1
  ring_nf

open TernaryPoly.SmoothLocalDeRham ZigZag in
/-- **The zig-zag datum of the seed.** `η = Ψ dτ`, `θ_g = Θ_g(τ)`; the form is `ω_h = dη`. -/
def seedDatum (hh : DifferentiableOn ℂ h upperSet)
    (hG : ∀ j z, 0 < z.im → HasDerivAt (Gm j) (h z * z ^ j) z)
    (hmod : ∀ g : G, ∀ z : ℂ, 0 < z.im →
      h (mob (D.lam g) z) = dnm (D.lam g) z ^ (n + 3) * h z) :
    Datum (d isOpen_faceSet 0 : Form (F := Coef n) faceSet 0 →ₗ[ℝ] Form (F := Coef n) faceSet 1)
      (d isOpen_faceSet 1) (fun g => pullForm isOpen_faceSet D.action g 1)
      (fun g => twForm (repCLM (D.rhoR n) g) 1) (d isOpen_faceSet 1 (etaForm h hh n)) where
  η := etaForm h hh n
  θ g := D.thetaForm h n Gm g hG
  dη := rfl
  dθ g := D.dTheta_eq h n Gm hh hG hmod g

end PlaneData

end TernaryPeriodPolynomials.Argument.SeedC3
