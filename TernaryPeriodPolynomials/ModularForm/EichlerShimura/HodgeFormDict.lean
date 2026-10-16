module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.HodgeDatumSym
public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.HodgeDecoupling
public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.L2.Slash

@[expose] public section


/-!
# From a smooth closed and co-closed form to the decoupling

Foundation file of the unconditional Eichler--Shimura route.  A real one-form `L = a dx + b dy` with values in `ℂ^{m+1}` (`a = L 1`, `b = L i`) has the
`dz` and `dz̄` coefficients `α = (a - i b) / 2` and `β = (a + i b) / 2` (`coefA`, `coefB`).  This
file translates, for the Hodge datum of `Sym^m` (`hodgeDatumSym`), the data produced by the `L²`
Hodge projection and Weyl's lemma into the hypotheses of `Decoupling.decoupling`:

* closedness `∂_x b = ∂_y a` is `∂_z̄ α = ∂_z β` (`closed_coeff`);
* co-closedness `∂_x (H a) + ∂_y (H b) = 0` is `∂_z̄ (Hmat α) + ∂_z (Hmat β) = 0`
  (`coclosed_coeff`, `H_sym_apply`);
* the energy density is `2 Σ_j y^m κ_j (|a_j|² + |b_j|²)` in the Hodge frame (`edens_sym`,
  `fullEnergy_eq`);
* invariance under the slash action gives the weights of `decoupling` (`eqv_coef`).

The result is `decoupling_of_form`.

Formalized by Claude Sonnet 5.5.
-/

open Complex Matrix MeasureTheory
open scoped MatrixGroups ContDiff InnerProductSpace
open TernaryPeriodPolynomials.Argument.ESFoundations.HodgePair (U isOpen_U dbar dz)
open TernaryPeriodPolynomials.Argument.ESFoundations.Partition (mob)

noncomputable section

open scoped Classical

namespace TernaryPeriodPolynomials.Argument.ESFoundations.SymFrame

open TernaryPeriodPolynomials.Argument.ESFoundations.L2 (Wd Form)
open TernaryPeriodPolynomials.Argument.ESFoundations.Decoupling (comp fullEnergy)
open TernaryPeriodPolynomials.Argument.ESFoundations.Partition (cutoff)
open TernaryPeriodPolynomials.Argument.ESFoundations.Global (den)
open TernaryPeriodPolynomials.Argument.ESFoundations.Weyl (dir)

/-- The `dz` coefficient of the real form `a dx + b dy`: `(a - i b) / 2`. -/
def coefA {d : ℕ} (a b : ℂ → Wd d) (w : ℂ) : Fin d → ℂ :=
  fun i => (1 / 2 : ℂ) * a w i + (-(Complex.I / 2)) * b w i

/-- The `dz̄` coefficient of the real form `a dx + b dy`: `(a + i b) / 2`. -/
def coefB {d : ℕ} (a b : ℂ → Wd d) (w : ℂ) : Fin d → ℂ :=
  fun i => (1 / 2 : ℂ) * a w i + (Complex.I / 2) * b w i

section Calculus

variable {d : ℕ}

theorem contDiffOn_proj {a : ℂ → Wd d} (ha : ContDiffOn ℝ ∞ a U) (i : Fin d) :
    ContDiffOn ℝ ∞ (fun w => a w i) U :=
  ((EuclideanSpace.proj (𝕜 := ℂ) i).restrictScalars ℝ).contDiff.comp_contDiffOn ha

theorem fderiv_proj {a : ℂ → Wd d} {z : ℂ} (ha : DifferentiableAt ℝ a z) (i : Fin d) (v : ℂ) :
    fderiv ℝ (fun w => a w i) z v = fderiv ℝ a z v i := by
  have h := ((EuclideanSpace.proj (𝕜 := ℂ) i).restrictScalars ℝ).hasFDerivAt.comp z
    ha.hasFDerivAt
  exact congrArg (fun T => T v) h.fderiv

theorem fderiv_comb {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) (s t v : ℂ) :
    fderiv ℝ (fun w => s * f w + t * g w) z v = s * fderiv ℝ f z v + t * fderiv ℝ g z v := by
  rw [fderiv_fun_add (hf.const_mul s) (hg.const_mul t), fderiv_const_mul hf, fderiv_const_mul hg]
  simp

theorem dbar_comb {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) (s t : ℂ) :
    dbar (fun w => s * f w + t * g w) z = s * dbar f z + t * dbar g z := by
  unfold dbar
  rw [fderiv_comb hf hg, fderiv_comb hf hg]
  ring

theorem dz_comb {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) (s t : ℂ) :
    dz (fun w => s * f w + t * g w) z = s * dz f z + t * dz g z := by
  unfold dz
  rw [fderiv_comb hf hg, fderiv_comb hf hg]
  ring

/-- Closedness of `a dx + b dy` (`∂_x b = ∂_y a`) is `∂_z̄ α = ∂_z β` for the coefficients of
`dz` and `dz̄`. -/
theorem closed_coeff {a b : ℂ → Wd d} (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U)
    (hcl : ∀ z ∈ U, fderiv ℝ b z 1 = fderiv ℝ a z Complex.I) {z : ℂ} (hz : z ∈ U) :
    dbarV (coefA a b) z = dzV (coefB a b) z := by
  funext i
  have hda : DifferentiableAt ℝ a z := (ha.differentiableOn (by simp) z hz).differentiableAt
      (isOpen_U.mem_nhds hz)
  have hdb : DifferentiableAt ℝ b z := (hb.differentiableOn (by simp) z hz).differentiableAt
      (isOpen_U.mem_nhds hz)
  have hfa : DifferentiableAt ℝ (fun w => a w i) z :=
    ((contDiffOn_proj ha i).differentiableOn (by simp) z hz).differentiableAt
      (isOpen_U.mem_nhds hz)
  have hfb : DifferentiableAt ℝ (fun w => b w i) z :=
    ((contDiffOn_proj hb i).differentiableOn (by simp) z hz).differentiableAt
      (isOpen_U.mem_nhds hz)
  have h := congrArg (fun x : Wd d => x i) (hcl z hz)
  simp only at h
  unfold dbarV dzV coefA coefB
  rw [dbar_comb hfa hfb, dz_comb hfa hfb]
  unfold dbar dz
  simp only [fderiv_proj hda, fderiv_proj hdb]
  rw [h]
  ring

/-- Co-closedness `∂_x (H a) + ∂_y (H b) = 0` (here `c = H a`, `e = H b`) is
`∂_z̄ (H α) + ∂_z (H β) = 0`. -/
theorem coclosed_coeff {M : ℂ → Matrix (Fin d) (Fin d) ℂ} {a b c e : ℂ → Wd d}
    (hc : ∀ w ∈ U, ∀ i, c w i = (M w *ᵥ fun j => a w j) i)
    (he : ∀ w ∈ U, ∀ i, e w i = (M w *ᵥ fun j => b w j) i)
    (hcd : ContDiffOn ℝ ∞ c U) (hed : ContDiffOn ℝ ∞ e U)
    (hco : ∀ z ∈ U, fderiv ℝ c z 1 + fderiv ℝ e z Complex.I = 0) {z : ℂ} (hz : z ∈ U) :
    dbarV (fun w => M w *ᵥ coefA a b w) z + dzV (fun w => M w *ᵥ coefB a b w) z = 0 := by
  funext i
  have hdc : DifferentiableAt ℝ c z := (hcd.differentiableOn (by simp) z hz).differentiableAt
      (isOpen_U.mem_nhds hz)
  have hde : DifferentiableAt ℝ e z := (hed.differentiableOn (by simp) z hz).differentiableAt
      (isOpen_U.mem_nhds hz)
  have hfc : DifferentiableAt ℝ (fun w => c w i) z :=
    ((contDiffOn_proj hcd i).differentiableOn (by simp) z hz).differentiableAt
      (isOpen_U.mem_nhds hz)
  have hfe : DifferentiableAt ℝ (fun w => e w i) z :=
    ((contDiffOn_proj hed i).differentiableOn (by simp) z hz).differentiableAt
      (isOpen_U.mem_nhds hz)
  have hA : (fun w => (M w *ᵥ coefA a b w) i) =ᶠ[nhds z]
      fun w => (1 / 2 : ℂ) * c w i + (-(Complex.I / 2)) * e w i := by
    filter_upwards [isOpen_U.mem_nhds hz] with w hw
    have : coefA a b w = (1 / 2 : ℂ) • (fun j => a w j) + (-(Complex.I / 2)) • (fun j => b w j) :=
      by funext j; simp [coefA]
    rw [this, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
    simp [hc w hw, he w hw]
  have hB : (fun w => (M w *ᵥ coefB a b w) i) =ᶠ[nhds z]
      fun w => (1 / 2 : ℂ) * c w i + (Complex.I / 2) * e w i := by
    filter_upwards [isOpen_U.mem_nhds hz] with w hw
    have : coefB a b w = (1 / 2 : ℂ) • (fun j => a w j) + (Complex.I / 2) • (fun j => b w j) :=
      by funext j; simp [coefB]
    rw [this, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
    simp [hc w hw, he w hw]
  have h := congrArg (fun x : Wd d => x i) (hco z hz)
  simp only [PiLp.add_apply, PiLp.zero_apply] at h
  simp only [Pi.add_apply, Pi.zero_apply, dbarV, dzV]
  have e1 : dbar (fun w => (M w *ᵥ coefA a b w) i) z =
      dbar (fun w => (1 / 2 : ℂ) * c w i + (-(Complex.I / 2)) * e w i) z := by
    unfold dbar; rw [hA.fderiv_eq]
  have e2 : dz (fun w => (M w *ᵥ coefB a b w) i) z =
      dz (fun w => (1 / 2 : ℂ) * c w i + (Complex.I / 2) * e w i) z := by
    unfold dz; rw [hB.fderiv_eq]
  rw [e1, e2, dbar_comb hfc hfe, dz_comb hfc hfe]
  unfold dbar dz
  simp only [fderiv_proj hdc, fderiv_proj hde]
  linear_combination (1 / 2 : ℂ) * h +
    (-(1 / 2 : ℂ) * (fderiv ℝ e z Complex.I) i) * Complex.I_sq

end Calculus


section Sym

variable (m : ℕ) (Γ : Subgroup SL(2, ℤ))

/-- The real operator `H` of the Hodge datum of `Sym^m` is the Hodge matrix `Hmat`. -/
theorem H_sym_apply {z : ℂ} (hz : z ∈ U) (x : Wd (m + 1)) :
    ((hodgeDatumSym m Γ).H z x).ofLp = Hmat m z *ᵥ x.ofLp := by
  have hy : 0 < z.im := hz
  have h1 : (hodgeDatumSym m Γ).H z x = ContinuousLinearMap.adjoint
      (Matrix.toEuclideanCLM (n := Fin (m + 1)) (𝕜 := ℂ) (frameS m z))
      (Matrix.toEuclideanCLM (n := Fin (m + 1)) (𝕜 := ℂ) (frameS m z) x) := rfl
  have h2 : ContinuousLinearMap.adjoint
      (Matrix.toEuclideanCLM (n := Fin (m + 1)) (𝕜 := ℂ) (frameS m z)) =
      Matrix.toEuclideanCLM (n := Fin (m + 1)) (𝕜 := ℂ) (star (frameS m z)) := by
    rw [← ContinuousLinearMap.star_eq_adjoint, map_star]
  rw [h1, h2, ofLp_toEuclideanCLM, ofLp_toEuclideanCLM, Matrix.mulVec_mulVec,
    Matrix.star_eq_conjTranspose, frameS_gram m hy]

theorem comp_coefA (a b : ℂ → Wd (m + 1)) (j : Fin (m + 1)) (w : ℂ) :
    comp m (coefA a b) j w = (1 / 2 : ℂ) * (frameT m w *ᵥ fun i => a w i) j +
      (-(Complex.I / 2)) * (frameT m w *ᵥ fun i => b w i) j := by
  have : coefA a b w = (1 / 2 : ℂ) • (fun i => a w i) + (-(Complex.I / 2)) • (fun i => b w i) := by
    funext i; simp [coefA]
  rw [Decoupling.comp, this]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

theorem comp_coefB (a b : ℂ → Wd (m + 1)) (j : Fin (m + 1)) (w : ℂ) :
    comp m (coefB a b) j w = (1 / 2 : ℂ) * (frameT m w *ᵥ fun i => a w i) j +
      (Complex.I / 2) * (frameT m w *ᵥ fun i => b w i) j := by
  have : coefB a b w = (1 / 2 : ℂ) • (fun i => a w i) + (Complex.I / 2) • (fun i => b w i) := by
    funext i; simp [coefB]
  rw [Decoupling.comp, this]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

theorem norm_sq_comb (x y : ℂ) :
    ‖(1 / 2 : ℂ) * x + (-(Complex.I / 2)) * y‖ ^ 2 + ‖(1 / 2 : ℂ) * x + (Complex.I / 2) * y‖ ^ 2 =
      (‖x‖ ^ 2 + ‖y‖ ^ 2) / 2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

/-- The energy density of the Hodge datum of `Sym^m` in the frame components. -/
theorem edens_sym {z : ℂ} (hz : z ∈ U) (L : Form (m + 1)) :
    (hodgeDatumSym m Γ).edens L z =
      2 * ∑ j : Fin (m + 1), z.im ^ m * kap m j *
        (‖comp m (coefA (fun w => L w 1) (fun w => L w Complex.I)) j z‖ ^ 2 +
          ‖comp m (coefB (fun w => L w 1) (fun w => L w Complex.I)) j z‖ ^ 2) := by
  have hy : 0 < z.im := hz
  have hS : ∀ x : Wd (m + 1), ‖(hodgeDatumSym m Γ).S z x‖ ^ 2 =
      ∑ j : Fin (m + 1), z.im ^ m * kap m j * ‖(frameT m z *ᵥ x.ofLp) j‖ ^ 2 := fun x => by
    rw [EuclideanSpace.norm_sq_eq]
    exact sum_sq_norm_frameS m hy x.ofLp
  unfold L2.HodgeDatum.edens
  rw [hS, hS, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [comp_coefA, comp_coefB, norm_sq_comb]
  ring



/-- The finite-energy density of the `Hodge` decoupling is half of the energy density of the form
`a dx + b dy`, weighted by the cutoff. -/
theorem fullEnergy_eq (R : Finset SL(2, ℤ)) (L : Form (m + 1)) (z : ℂ) :
    fullEnergy Γ R m (coefA (fun w => L w 1) (fun w => L w Complex.I))
        (coefB (fun w => L w 1) (fun w => L w Complex.I)) z =
      (1 / 2) * (if z ∈ U then cutoff Γ R z * (hodgeDatumSym m Γ).edens L z else 0) := by
  unfold fullEnergy
  by_cases hz : z ∈ U
  · simp only [hz, ite_true]
    rw [edens_sym m Γ hz L]
    ring
  · simp [hz]


theorem coefA_algebra {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (A B : Fin n → ℂ) (p q : ℝ) :
    (1 / 2 : ℂ) • (M *ᵥ ((p : ℂ) • A + (q : ℂ) • B)) +
        (-(Complex.I / 2)) • (M *ᵥ ((-(q : ℂ)) • A + (p : ℂ) • B)) =
      ((p : ℂ) + (q : ℂ) * Complex.I) •
        (M *ᵥ ((1 / 2 : ℂ) • A + (-(Complex.I / 2)) • B)) := by
  funext i
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination ((1 / 2 : ℂ) * (q : ℂ) * (M *ᵥ B) i) * Complex.I_sq

theorem coefB_algebra {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (A B : Fin n → ℂ) (p q : ℝ) :
    (1 / 2 : ℂ) • (M *ᵥ ((p : ℂ) • A + (q : ℂ) • B)) +
        (Complex.I / 2) • (M *ᵥ ((-(q : ℂ)) • A + (p : ℂ) • B)) =
      ((p : ℂ) - (q : ℂ) * Complex.I) •
        (M *ᵥ ((1 / 2 : ℂ) • A + (Complex.I / 2) • B)) := by
  funext i
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination ((1 / 2 : ℂ) * (q : ℂ) * (M *ᵥ B) i) * Complex.I_sq

/-- The coefficients of an equivariant form transform with the weights of the Hodge frame. -/
theorem eqv_coef (L : Form (m + 1)) (hE : (hodgeDatumSym m Γ).Eqv L) {γ : SL(2, ℤ)}
    (hγ : γ ∈ Γ) {w : ℂ} (hw : w ∈ U) :
    coefA (fun w => L w 1) (fun w => L w Complex.I) (mob γ w) =
        den γ w ^ 2 • (symRep m γ *ᵥ coefA (fun w => L w 1) (fun w => L w Complex.I) w) ∧
      coefB (fun w => L w 1) (fun w => L w Complex.I) (mob γ w) =
        starRingEnd ℂ (den γ w ^ 2) •
          (symRep m γ *ᵥ coefB (fun w => L w 1) (fun w => L w Complex.I) w) := by
  have hD : den γ w ≠ 0 := Partition.denom_ne_zero' γ hw
  have key : ∀ v : ℂ, (L (mob γ w) v).ofLp = symRep m γ *ᵥ (L w (den γ w ^ 2 * v)).ofLp := by
    intro v
    have h := congrArg (fun T : ℂ →L[ℝ] Wd (m + 1) => T (den γ w ^ 2 * v))
      (hE ⟨γ, hγ⟩ w hw)
    have h1 : (hodgeDatumSym m Γ).slash ⟨γ, hγ⟩ L w (den γ w ^ 2 * v) =
        (hodgeDatumSym m Γ).ρR (⟨γ, hγ⟩ : Γ)⁻¹ (L (mob γ w) v) := by
      have e : L2.mobDeriv γ w * (den γ w ^ 2 * v) = v := by
        unfold L2.mobDeriv L2.jfun
        change 1 / den γ w ^ 2 * (den γ w ^ 2 * v) = v
        field_simp
      simp [L2.HodgeDatum.slash, L2.fderiv_mob_apply _ hw, e]
    rw [h1] at h
    have h2 : (hodgeDatumSym m Γ).ρ ⟨γ, hγ⟩ ((hodgeDatumSym m Γ).ρR (⟨γ, hγ⟩ : Γ)⁻¹
        (L (mob γ w) v)) = L (mob γ w) v := by
      show (hodgeDatumSym m Γ).ρ ⟨γ, hγ⟩ ((hodgeDatumSym m Γ).ρ (⟨γ, hγ⟩ : Γ)⁻¹
        (L (mob γ w) v)) = _
      rw [← mul_apply_eq_comp, ← map_mul, mul_inv_cancel, map_one]
      rfl
    rw [← h2, h]
    rfl
  have dec : ∀ u : ℂ, (L w u).ofLp =
      (u.re : ℂ) • (L w 1).ofLp + (u.im : ℂ) • (L w Complex.I).ofLp := by
    intro u
    have : L w u = u.re • L w 1 + u.im • L w Complex.I := by
      rw [← map_smul, ← map_smul, ← map_add]
      congr 1
      apply Complex.ext <;> simp
    rw [this]
    funext i
    simp [Complex.coe_smul]
  have ha : (L (mob γ w) 1).ofLp = symRep m γ *ᵥ ((((den γ w ^ 2).re : ℝ) : ℂ) •
      (L w 1).ofLp + (((den γ w ^ 2).im : ℝ) : ℂ) • (L w Complex.I).ofLp) := by
    rw [key, mul_one, dec]
  have hb : (L (mob γ w) Complex.I).ofLp = symRep m γ *ᵥ ((-(((den γ w ^ 2).im : ℝ) : ℂ)) •
      (L w 1).ofLp + (((den γ w ^ 2).re : ℝ) : ℂ) • (L w Complex.I).ofLp) := by
    rw [key, dec]
    simp
  have hcoefA : coefA (fun w => L w 1) (fun w => L w Complex.I) w =
      (1 / 2 : ℂ) • (L w 1).ofLp + (-(Complex.I / 2)) • (L w Complex.I).ofLp := by
    funext j; simp [coefA]
  have hcoefB : coefB (fun w => L w 1) (fun w => L w Complex.I) w =
      (1 / 2 : ℂ) • (L w 1).ofLp + (Complex.I / 2) • (L w Complex.I).ofLp := by
    funext j; simp [coefB]
  constructor
  · funext i
    have h := congrFun (coefA_algebra (symRep m γ) (L w 1).ofLp (L w Complex.I).ofLp
      (den γ w ^ 2).re (den γ w ^ 2).im) i
    rw [Complex.re_add_im] at h
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h
    rw [hcoefA]
    simp only [coefA, Pi.smul_apply, smul_eq_mul]
    rw [ha, hb]
    exact h
  · funext i
    have h := congrFun (coefB_algebra (symRep m γ) (L w 1).ofLp (L w Complex.I).ofLp
      (den γ w ^ 2).re (den γ w ^ 2).im) i
    have hc : ((den γ w ^ 2).re : ℂ) - ((den γ w ^ 2).im : ℂ) * Complex.I =
        starRingEnd ℂ (den γ w ^ 2) := by
      generalize den γ w ^ 2 = u
      apply Complex.ext
      · rw [Complex.conj_re]; simp
      · rw [Complex.conj_im]; simp
    rw [hc] at h
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h
    rw [hcoefB]
    simp only [coefB, Pi.smul_apply, smul_eq_mul]
    rw [ha, hb]
    exact h


variable {m Γ}

/-- **The gap-free feed of the decoupling.**  A form `L` (given by its values `a = L 1`,
`b = L i`) which is smooth, closed (`∂_x b = ∂_y a`), co-closed for the Hodge metric of `Sym^m`
(`∂_x (H a) + ∂_y (H b) = 0`), equivariant, and of finite energy, is a sum
`f(z) (zY - X)^m dz + conj (g(z) (z̄Y - X)^m) dz̄` of a holomorphic and an antiholomorphic cusp form
datum `f, g`. -/
theorem decoupling_of_form {R : Finset SL(2, ℤ)} (hR : Partition.IsCover Γ R) (L : Form (m + 1))
    (ha : ContDiffOn ℝ ∞ (fun w => L w 1) U) (hb : ContDiffOn ℝ ∞ (fun w => L w Complex.I) U)
    (hcl : ∀ z ∈ U, fderiv ℝ (fun w => L w Complex.I) z 1 = fderiv ℝ (fun w => L w 1) z Complex.I)
    (hco : ∀ z ∈ U, fderiv ℝ (fun w => (hodgeDatumSym m Γ).H w (L w 1)) z 1 +
      fderiv ℝ (fun w => (hodgeDatumSym m Γ).H w (L w Complex.I)) z Complex.I = 0)
    (hE : (hodgeDatumSym m Γ).Eqv L)
    (hen : Integrable (fun z => if z ∈ U then cutoff Γ R z * (hodgeDatumSym m Γ).edens L z
      else 0)) :
    ∃ f g : ℂ → ℂ, DifferentiableOn ℂ f U ∧ DifferentiableOn ℂ g U ∧
      (∀ γ ∈ Γ, ∀ z ∈ U, f (mob γ z) = den γ z ^ (m + 2) * f z) ∧
      (∀ γ ∈ Γ, ∀ z ∈ U, g (mob γ z) = den γ z ^ (m + 2) * g z) ∧
      Integrable (fun z => if z ∈ U then cutoff Γ R z * (z.im ^ m * ‖f z‖ ^ 2) else 0) ∧
      Integrable (fun z => if z ∈ U then cutoff Γ R z * (z.im ^ m * ‖g z‖ ^ 2) else 0) ∧
      ∀ z ∈ U, (coefA (fun w => L w 1) (fun w => L w Complex.I) z =
          f z • (fun i => frameE m z i (Fin.last m))) ∧
        coefB (fun w => L w 1) (fun w => L w Complex.I) z =
          starRingEnd ℂ (g z) • (fun i => frameE m z i 0) := by
  classical
  set D := hodgeDatumSym m Γ with hD
  have hαs : ∀ i, ContDiffOn ℝ ∞
      (fun w => coefA (fun w => L w 1) (fun w => L w Complex.I) w i) U := fun i => by
    unfold coefA
    exact (contDiffOn_const.mul (contDiffOn_proj ha i)).add
      (contDiffOn_const.mul (contDiffOn_proj hb i))
  have hβs : ∀ i, ContDiffOn ℝ ∞
      (fun w => coefB (fun w => L w 1) (fun w => L w Complex.I) w i) U := fun i => by
    unfold coefB
    exact (contDiffOn_const.mul (contDiffOn_proj ha i)).add
      (contDiffOn_const.mul (contDiffOn_proj hb i))
  have hcd : ContDiffOn ℝ ∞ (fun w => D.H w (L w 1)) U := D.smooth_H.clm_apply ha
  have hed : ContDiffOn ℝ ∞ (fun w => D.H w (L w Complex.I)) U := D.smooth_H.clm_apply hb
  have hC := fun (z : ℂ) (hz : z ∈ U) => closed_coeff ha hb hcl hz
  have hCC := fun (z : ℂ) (hz : z ∈ U) => coclosed_coeff (M := Hmat m) (a := fun w => L w 1)
    (b := fun w => L w Complex.I) (c := fun w => D.H w (L w 1))
    (e := fun w => D.H w (L w Complex.I))
    (fun w hw i => congrFun (H_sym_apply m Γ hw (L w 1)) i)
    (fun w hw i => congrFun (H_sym_apply m Γ hw (L w Complex.I)) i) hcd hed hco hz
  have hen' : Integrable (fullEnergy Γ R m (coefA (fun w => L w 1) (fun w => L w Complex.I))
      (coefB (fun w => L w 1) (fun w => L w Complex.I))) := by
    have : fullEnergy Γ R m (coefA (fun w => L w 1) (fun w => L w Complex.I))
        (coefB (fun w => L w 1) (fun w => L w Complex.I)) = fun z =>
        (1 / 2 : ℝ) * (if z ∈ U then cutoff Γ R z * D.edens L z else 0) := by
      funext z; exact fullEnergy_eq m Γ R L z
    rw [this]
    exact hen.const_mul _
  exact Decoupling.decoupling hR hαs hβs hC hCC
    (fun γ hγ z hz => (eqv_coef m Γ L hE hγ hz).1)
    (fun γ hγ z hz => (eqv_coef m Γ L hE hγ hz).2) hen'


/-- The real one-form `a dx + b dy`. -/
def formOfPair {d : ℕ} (a b : ℂ → Wd d) : Form d := fun z =>
  (Complex.reCLM.smulRight (a z)) + (Complex.imCLM.smulRight (b z))

@[simp] theorem formOfPair_one {d : ℕ} (a b : ℂ → Wd d) (z : ℂ) : formOfPair a b z 1 = a z := by
  simp [formOfPair]

@[simp] theorem formOfPair_I {d : ℕ} (a b : ℂ → Wd d) (z : ℂ) :
    formOfPair a b z Complex.I = b z := by
  simp [formOfPair]

/-- The decoupling for the output of the `L²` Hodge projection and of Weyl's lemma
(`weyl_regularity_closed_coclosed`): smooth `a, b` with `∂₀ b = ∂₁ a` and
`∂₀ (H a) + ∂₁ (H b) = 0` for the Hodge field of `Sym^m`, such that the form `a dx + b dy` is
equivariant and has finite energy. -/
theorem decoupling_of_pair {R : Finset SL(2, ℤ)} (hR : Partition.IsCover Γ R)
    {a b : ℂ → Wd (m + 1)} (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U)
    (hcl : ∀ z ∈ U, fderiv ℝ b z (dir 0) = fderiv ℝ a z (dir 1))
    (hco : ∀ z ∈ U, fderiv ℝ (fun z => (hodgeDatumSym m Γ).H z (a z)) z (dir 0) +
      fderiv ℝ (fun z => (hodgeDatumSym m Γ).H z (b z)) z (dir 1) = 0)
    (hE : (hodgeDatumSym m Γ).Eqv (formOfPair a b))
    (hen : Integrable (fun z => if z ∈ U then
      cutoff Γ R z * (hodgeDatumSym m Γ).edens (formOfPair a b) z else 0)) :
    ∃ f g : ℂ → ℂ, DifferentiableOn ℂ f U ∧ DifferentiableOn ℂ g U ∧
      (∀ γ ∈ Γ, ∀ z ∈ U, f (mob γ z) = den γ z ^ (m + 2) * f z) ∧
      (∀ γ ∈ Γ, ∀ z ∈ U, g (mob γ z) = den γ z ^ (m + 2) * g z) ∧
      Integrable (fun z => if z ∈ U then cutoff Γ R z * (z.im ^ m * ‖f z‖ ^ 2) else 0) ∧
      Integrable (fun z => if z ∈ U then cutoff Γ R z * (z.im ^ m * ‖g z‖ ^ 2) else 0) ∧
      ∀ z ∈ U, (coefA a b z = f z • (fun i => frameE m z i (Fin.last m))) ∧
        coefB a b z = starRingEnd ℂ (g z) • (fun i => frameE m z i 0) := by
  have e1 : (fun w => formOfPair a b w 1) = a := funext fun w => formOfPair_one a b w
  have e2 : (fun w => formOfPair a b w Complex.I) = b := funext fun w => formOfPair_I a b w
  have h := decoupling_of_form hR (formOfPair a b) (by rw [e1]; exact ha) (by rw [e2]; exact hb)
    (by rw [e1, e2]; simpa [dir] using hcl)
    (by simpa [dir] using hco) hE hen
  rwa [e1, e2] at h

end Sym

end TernaryPeriodPolynomials.Argument.ESFoundations.SymFrame
