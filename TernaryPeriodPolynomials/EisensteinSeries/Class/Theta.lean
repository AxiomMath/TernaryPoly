module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.CartanForm
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Double2
public import TernaryPeriodPolynomials.EisensteinSeries.Class.AvInv

@[expose] public section


/-!
# The averaged Cartan primitive and `d Θ = Av W - P W`

For a closed form `W` of degree `k + 1` on the boundary model and a smooth family `σ` of coefficient
transports, `thetaForm σ c W = ∫₀¹∫₀¹ σ(-c t) B_{c t} W dt` (the translation-Cartan primitives, averaged) is a
chart form with `d Θ = Av W - P W` (`d_thetaForm`), where `Av W = avFormS σ c W` is the torus average
and `P = Pavg σ c = ∫₀¹∫₀¹ σ(-c t) dt` acts on the coefficients.

Formalized by Claude Sonnet 5.5.
-/

open ContinuousAlternatingMap Set MeasureTheory
open scoped ContDiff MatrixGroups
noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.SeedC3.Psi TernaryPoly.SmoothLocalDeRham
  TernaryPoly.SmoothCoveringDeRham

variable {n : ℕ} {k : ℕ}

theorem compAlt_isBoundedBilinear (n k : ℕ) :
    IsBoundedBilinearMap ℝ (fun q : (Coef n →L[ℝ] Coef n) × (Face [⋀^Fin k]→L[ℝ] Coef n) =>
      q.1.compContinuousAlternatingMap q.2) :=
  { add_left := fun L₁ L₂ w => by ext; simp
    smul_left := fun r L w => by ext; simp
    add_right := fun L w₁ w₂ => by ext; simp
    smul_right := fun r L w => by ext; simp
    bound := ⟨1, one_pos, fun L w => by simpa using L.norm_compContinuousAlternatingMap_le w⟩ }

/-- Evaluation of a coefficient endomorphism on a fixed alternating form, as a linear map in the
endomorphism. -/
def coefCLM (n k : ℕ) (w0 : Face [⋀^Fin k]→L[ℝ] Coef n) :
    (Coef n →L[ℝ] Coef n) →L[ℝ] (Face [⋀^Fin k]→L[ℝ] Coef n) :=
  LinearMap.mkContinuous
    { toFun := fun T => T.compContinuousAlternatingMap w0
      map_add' := fun T T' => by ext; simp
      map_smul' := fun r T => by ext; simp }
    ‖w0‖ (fun T => by
      have := T.norm_compContinuousAlternatingMap_le w0
      calc _ ≤ _ := this
        _ = _ := by ring)

theorem coefCLM_apply (T : Coef n →L[ℝ] Coef n) (w0 : Face [⋀^Fin k]→L[ℝ] Coef n) :
    coefCLM n k w0 T = T.compContinuousAlternatingMap w0 := rfl

variable {σ : (Fin 2 → ℝ) → (Coef n →L[ℝ] Coef n)}

/-- The integrand of the averaged Cartan primitive. -/
def thetaIntegrand (σ : (Fin 2 → ℝ) → (Coef n →L[ℝ] Coef n)) (c : ℝ)
    (W : Form (F := Coef n) faceSet (k + 1)) (p : (Face × ℝ) × ℝ) : Face [⋀^Fin k]→L[ℝ] Coef n :=
  (σ (-(c • ![p.1.2, p.2]))).compContinuousAlternatingMap
    (cartanRaw (tvec c p) (W : RawForm Face (Coef n) (k + 1)) p.1.1)

theorem contDiffOn_thetaIntegrand (hσ : ContDiff ℝ ∞ σ) (c : ℝ)
    (W : Form (F := Coef n) faceSet (k + 1)) :
    ContDiffOn ℝ ∞ (thetaIntegrand σ c W)
      ((faceSet ×ˢ (Set.univ : Set ℝ)) ×ˢ (Set.univ : Set ℝ)) := by
  have hL : ContDiff ℝ ∞ (fun p : (Face × ℝ) × ℝ => σ (-(c • ![p.1.2, p.2]))) := by
    refine hσ.comp ?_
    refine contDiff_pi.2 fun i => ?_
    fin_cases i <;> simp <;> fun_prop
  exact (compAlt_isBoundedBilinear n k).contDiff.comp_contDiffOn
    (hL.contDiffOn.prodMk (contDiffOn_cartanParam c W))

/-- The averaged Cartan primitive `Θ = ∫₀¹∫₀¹ σ(-c t) B_{c t} W dt` (raw form). -/
def thetaRaw (σ : (Fin 2 → ℝ) → (Coef n →L[ℝ] Coef n)) (c : ℝ)
    (W : Form (F := Coef n) faceSet (k + 1)) (x : Face) : Face [⋀^Fin k]→L[ℝ] Coef n :=
  ∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1, thetaIntegrand σ c W ((x, a), b)

theorem contDiffOn_thetaRaw (hσ : ContDiff ℝ ∞ σ) (c : ℝ) (W : Form (F := Coef n) faceSet (k + 1)) :
    ContDiffOn ℝ ∞ (thetaRaw σ c W) faceSet :=
  contDiffOn_iteratedIntegral isOpen_faceSet _ (contDiffOn_thetaIntegrand hσ c W)

/-- The averaged Cartan primitive as a chart form. -/
def thetaForm (hσ : ContDiff ℝ ∞ σ) (c : ℝ) (W : Form (F := Coef n) faceSet (k + 1)) :
    Form (F := Coef n) faceSet k :=
  restrictForm faceSet (thetaRaw σ c W) (contDiffOn_thetaRaw hσ c W)

theorem thetaForm_apply (hσ : ContDiff ℝ ∞ σ) (c : ℝ) (W : Form (F := Coef n) faceSet (k + 1))
    {x : Face} (hx : x ∈ faceSet) :
    ((thetaForm hσ c W : Form (F := Coef n) faceSet k) : RawForm Face (Coef n) k) x =
      thetaRaw σ c W x :=
  restrictForm_apply _ _ hx

theorem iterIntegral_sub' {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [CompleteSpace A]
    (g h : ℝ → ℝ → A) (hg : Continuous (Function.uncurry g)) (hh : Continuous (Function.uncurry h)) :
    (∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1, (g a b - h a b)) =
      (∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1, g a b) - ∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1, h a b := by
  have hin : ∀ (k : ℝ → ℝ → A), Continuous (Function.uncurry k) → ∀ a,
      IntervalIntegrable (fun b => k a b) volume 0 1 := fun k hk a =>
    (hk.comp (Continuous.prodMk_right a)).intervalIntegrable 0 1
  have hcont : ∀ (k : ℝ → ℝ → A), Continuous (Function.uncurry k) →
      Continuous fun a => ∫ b in (0:ℝ)..1, k a b := fun k hk =>
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hk 0 1
  have : (fun a : ℝ => ∫ b in (0:ℝ)..1, (g a b - h a b)) =
      fun a => (∫ b in (0:ℝ)..1, g a b) - ∫ b in (0:ℝ)..1, h a b := by
    funext a
    exact intervalIntegral.integral_sub (hin g hg a) (hin h hh a)
  rw [this]
  exact intervalIntegral.integral_sub ((hcont g hg).intervalIntegrable 0 1)
    ((hcont h hh).intervalIntegrable 0 1)

theorem extDeriv_cartanRaw (v : Fin 2 → ℝ) (W : Form (F := Coef n) faceSet (k + 1))
    (hW : d isOpen_faceSet (k + 1) W = 0) {x : Face} (hx : x ∈ faceSet) :
    extDeriv (cartanRaw (shVec v) (W : RawForm Face (Coef n) (k + 1))) x =
      (W : RawForm Face (Coef n) (k + 1)) (x + shVec v) - (W : RawForm Face (Coef n) (k + 1)) x := by
  have h := d_cartanForm_apply v W hW hx
  rw [d_apply isOpen_faceSet _ hx] at h
  have heq : (cartanForm v W : RawForm Face (Coef n) k) =ᶠ[nhds x]
      cartanRaw (shVec v) (W : RawForm Face (Coef n) (k + 1)) := by
    filter_upwards [isOpen_faceSet.mem_nhds hx] with y hy using cartanForm_apply v W hy
  rw [heq.extDeriv_eq (𝕜 := ℝ)] at h
  exact h

/-- The coefficient average `P = ∫₀¹∫₀¹ σ(-c (a,b)) da db`. -/
def Pavg (σ : (Fin 2 → ℝ) → (Coef n →L[ℝ] Coef n)) (c : ℝ) : Coef n →L[ℝ] Coef n :=
  ∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1, σ (-(c • ![a, b]))

theorem continuous_avIntegrandS_uncurry (hσ : ContDiff ℝ ∞ σ) (c : ℝ)
    (W : Form (F := Coef n) faceSet k) {x : Face} (hx : x ∈ faceSet) :
    Continuous (Function.uncurry fun a b : ℝ => avIntegrandS k σ c W ((x, a), b)) := by
  have h := (contDiffOn_avIntegrandS hσ c W).continuousOn
  rw [← continuousOn_univ]
  have hc : Continuous (fun p : ℝ × ℝ => (((x, p.1), p.2) : (Face × ℝ) × ℝ)) := by fun_prop
  exact h.comp hc.continuousOn fun p _ => ⟨⟨hx, trivial⟩, trivial⟩

theorem extDeriv_thetaRaw (hσ : ContDiff ℝ ∞ σ) (c : ℝ) (W : Form (F := Coef n) faceSet (k + 1))
    (hW : d isOpen_faceSet (k + 1) W = 0) {x : Face} (hx : x ∈ faceSet) :
    extDeriv (thetaRaw σ c W) x =
      avRawS (k := k + 1) σ c W x -
        coefCLM n (k + 1) ((W : RawForm Face (Coef n) (k + 1)) x) (Pavg σ c) := by
  unfold thetaRaw
  rw [extDeriv_iteratedIntegral isOpen_faceSet _ (contDiffOn_thetaIntegrand hσ c W) hx]
  -- the pointwise integrand
  have hpt : ∀ a b : ℝ, extDeriv (fun y => thetaIntegrand σ c W ((y, a), b)) x =
      avIntegrandS (k + 1) σ c W ((x, a), b) -
        (coefCLM n (k + 1) ((W : RawForm Face (Coef n) (k + 1)) x)) (σ (-(c • ![a, b]))) := by
    intro a b
    have hdiff : DifferentiableAt ℝ (cartanRaw (shVec (c • ![a, b]))
        (W : RawForm Face (Coef n) (k + 1))) x :=
      ((contDiffOn_cartanRaw (c • ![a, b]) W x hx).contDiffAt
        (isOpen_faceSet.mem_nhds hx)).differentiableAt (by simp)
    have e1 : (fun y => thetaIntegrand σ c W ((y, a), b)) =
        coefficientRaw (σ (-(c • ![a, b]))) (cartanRaw (shVec (c • ![a, b]))
          (W : RawForm Face (Coef n) (k + 1))) := rfl
    rw [e1, extDeriv_coefficientRaw _ hdiff, extDeriv_cartanRaw (c • ![a, b]) W hW hx]
    have hsub : ∀ (T : Coef n →L[ℝ] Coef n) (A B : Face [⋀^Fin (k + 1)]→L[ℝ] Coef n),
        T.compContinuousAlternatingMap (A - B) =
          T.compContinuousAlternatingMap A - T.compContinuousAlternatingMap B := by
      intro T A B; ext; simp
    rw [coefficientFormMap_apply, hsub]
    have hA : avIntegrandS (k + 1) σ c W ((x, a), b) = (σ (-(c • ![a, b]))).compContinuousAlternatingMap
        ((W : RawForm Face (Coef n) (k + 1)) (x + shVec (c • ![a, b]))) :=
      shiftS_apply (k + 1) σ _ W hx
    rw [hA, coefCLM_apply]
  have hσc : Continuous σ := hσ.continuous
  have hBc : Continuous (Function.uncurry fun a b : ℝ =>
      (coefCLM n (k + 1) ((W : RawForm Face (Coef n) (k + 1)) x)) (σ (-(c • ![a, b])))) := by
    refine (coefCLM n (k + 1) _).continuous.comp (hσc.comp ?_)
    fun_prop
  simp only [hpt]
  rw [iterIntegral_sub' _ _ (continuous_avIntegrandS_uncurry hσ c W hx) hBc]
  congr 1
  have := iterIntegral_clm_comm (coefCLM n (k + 1) ((W : RawForm Face (Coef n) (k + 1)) x))
    (fun a b => σ (-(c • ![a, b]))) (by
      refine hσc.comp ?_
      fun_prop)
  exact this.symm

/-- **`d Θ = Av W - P W`** for a closed form `W`. -/
theorem d_thetaForm (hσ : ContDiff ℝ ∞ σ) (c : ℝ) (W : Form (F := Coef n) faceSet (k + 1))
    (hW : d isOpen_faceSet (k + 1) W = 0) :
    d isOpen_faceSet k (thetaForm hσ c W) =
      avFormS hσ c W - ZigZag.twForm (Pavg σ c) (k + 1) W := by
  apply Form.ext
  intro x hx
  rw [d_apply isOpen_faceSet _ hx]
  have heq : (thetaForm hσ c W : RawForm Face (Coef n) k) =ᶠ[nhds x] thetaRaw σ c W := by
    filter_upwards [isOpen_faceSet.mem_nhds hx] with y hy using thetaForm_apply hσ c W hy
  rw [heq.extDeriv_eq (𝕜 := ℝ), extDeriv_thetaRaw hσ c W hW hx]
  change _ = ((avFormS hσ c W : Form (F := Coef n) faceSet (k + 1)) : RawForm Face (Coef n) (k + 1)) x -
    ((ZigZag.twForm (Pavg σ c) (k + 1) W : Form (F := Coef n) faceSet (k + 1)) :
      RawForm Face (Coef n) (k + 1)) x
  rw [avFormS_apply hσ c W hx, ZigZag.twForm_apply, coefficientFormMap_apply, coefCLM_apply]

end TernaryPeriodPolynomials.Argument.EisensteinClass
