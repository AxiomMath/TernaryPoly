module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Theta
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Unip

@[expose] public section


/-!
# Theorem K: the torus average differs from a closed equivariant form by an equivariant differential

(the nilmanifold
theorem with unipotent coefficients, abelian radical `Nℤ²`; "the averaging map ... induces the inverse
cohomology isomorphism").

`exists_equivariant_primitive`: for a unipotent representation `σ` of `ℝ²` (`UniRep σ`) and a closed
`σ`-equivariant form `W` of positive degree on the boundary model (`EqvS σ c W`: `W(x + u) = σ(u) W(x)` for
`u ∈ c ℤ²`), there is a `σ`-equivariant form `Ξ` with `d Ξ = Av W - W`, `Av` the torus average with
coefficient transport. Proof: `Av W = P W + d Θ` (Cartan homotopy for the translations, `d_thetaForm`) and
`P - 1 = T₁(σ(c e₀) - 1) + T₂(σ(c e₁) - 1)` (`Pavg_sub_one_mem`, unipotence), and `(σ(c eᵢ) - 1) W = d B_{c eᵢ} W`
by Cartan again, with lattice-equivariant `B`. No Fourier series is used.

Formalized by Claude Sonnet 5.5.
-/

open ContinuousAlternatingMap Set MeasureTheory
open scoped ContDiff MatrixGroups
noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.SeedC3.Psi TernaryPoly.SmoothLocalDeRham
  TernaryPoly.SmoothCoveringDeRham

theorem intervalIntegral_mem_closed {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [CompleteSpace A] {s : Set A} (hconv : Convex ℝ s) (hcl : IsClosed s) (f : ℝ → A)
    (hf : Continuous f) (hs : ∀ t, f t ∈ s) : ∫ t in (0:ℝ)..1, f t ∈ s := by
  rw [intervalIntegral.integral_of_le zero_le_one]
  have : IsProbabilityMeasure (volume.restrict (Ioc (0:ℝ) 1)) := ⟨by simp⟩
  exact hconv.integral_mem hcl (ae_of_all _ hs)
    ((hf.integrableOn_Icc (a := 0) (b := 1)).mono_set Ioc_subset_Icc_self)

theorem iterIntegral_mem_closed {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [CompleteSpace A] {s : Set A} (hconv : Convex ℝ s) (hcl : IsClosed s) (g : ℝ → ℝ → A)
    (hg : Continuous (Function.uncurry g)) (hs : ∀ a b, g a b ∈ s) :
    ∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1, g a b ∈ s := by
  refine intervalIntegral_mem_closed hconv hcl _ ?_ fun a => ?_
  · exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hg 0 1
  · exact intervalIntegral_mem_closed hconv hcl _ (hg.comp (Continuous.prodMk_right a)) (hs a)

variable {n k : ℕ} {σ : (Fin 2 → ℝ) → (Coef n →L[ℝ] Coef n)}

/-- **The coefficient average minus one lies in the lattice ideal.** -/
theorem Pavg_sub_one_mem (h : UniRep σ) {c : ℝ} (hc : c ≠ 0) : Pavg σ c - 1 ∈ idealA σ c := by
  have hcont : Continuous (Function.uncurry fun a b : ℝ => σ (-(c • ![a, b])) - 1) := by
    refine (h.cont.comp ?_).sub continuous_const
    fun_prop
  have hcont0 : Continuous (Function.uncurry fun a b : ℝ => σ (-(c • ![a, b]))) := by
    refine h.cont.comp ?_
    fun_prop
  have e : Pavg σ c - 1 = ∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1, (σ (-(c • ![a, b])) - 1) := by
    have hone : Continuous (Function.uncurry fun (_ _ : ℝ) => (1 : Coef n →L[ℝ] Coef n)) :=
      continuous_const
    have := iterIntegral_sub' (fun a b : ℝ => σ (-(c • ![a, b]))) (fun _ _ => 1) hcont0 hone
    rw [this]
    simp [Pavg]
  rw [e]
  exact iterIntegral_mem_closed (Submodule.convex _) (isClosed_idealA c) _ hcont
    fun a b => sub_one_mem_idealA h hc _

/-! ### Lattice equivariance -/

/-- Precomposition with a coefficient endomorphism, as a continuous linear map on `k`-forms. -/
def compAltCLM (T : Coef n →L[ℝ] Coef n) (k : ℕ) :
    (Face [⋀^Fin k]→L[ℝ] Coef n) →L[ℝ] (Face [⋀^Fin k]→L[ℝ] Coef n) :=
  LinearMap.mkContinuous
    { toFun := fun w => T.compContinuousAlternatingMap w
      map_add' := fun w w' => by ext; simp
      map_smul' := fun r w => by ext; simp }
    ‖T‖ (fun w => T.norm_compContinuousAlternatingMap_le w)

theorem compAltCLM_apply (T : Coef n →L[ℝ] Coef n) (w : Face [⋀^Fin k]→L[ℝ] Coef n) :
    compAltCLM T k w = T.compContinuousAlternatingMap w := rfl

/-- **Lattice equivariance** of a chart form: `W(x + u) = σ(u) ∘ W(x)` for `u ∈ c ℤ²`. -/
def EqvS (σ : (Fin 2 → ℝ) → (Coef n →L[ℝ] Coef n)) (c : ℝ) (W : Form (F := Coef n) faceSet k) :
    Prop :=
  ∀ m : Fin 2 → ℤ, ∀ x ∈ faceSet,
    (W : RawForm Face (Coef n) k) (x + shVec (c • intVec m)) =
      (σ (c • intVec m)).compContinuousAlternatingMap ((W : RawForm Face (Coef n) k) x)

theorem EqvS.add {c : ℝ} {W W' : Form (F := Coef n) faceSet k} (h : EqvS σ c W) (h' : EqvS σ c W') :
    EqvS σ c (W + W') := by
  intro m x hx
  change (W : RawForm Face (Coef n) k) _ + (W' : RawForm Face (Coef n) k) _ =
    (σ _).compContinuousAlternatingMap ((W : RawForm Face (Coef n) k) x +
      (W' : RawForm Face (Coef n) k) x)
  rw [h m x hx, h' m x hx]
  ext; simp

theorem EqvS.twForm {c : ℝ} {W : Form (F := Coef n) faceSet k} (h : EqvS σ c W)
    {T : Coef n →L[ℝ] Coef n} (hT : Comm σ T) : EqvS σ c (ZigZag.twForm T k W) := by
  intro m x hx
  rw [ZigZag.twForm_apply, ZigZag.twForm_apply, coefficientFormMap_apply, coefficientFormMap_apply,
    h m x hx]
  ext w
  exact congrArg (fun S : Coef n →L[ℝ] Coef n => S _) ((hT (c • intVec m)).eq)

theorem integrable_cartan_slice (W : Form (F := Coef n) faceSet (k + 1)) (v : Fin 2 → ℝ) {x : Face}
    (hx : x ∈ faceSet) :
    IntervalIntegrable (fun s : ℝ => ((W : RawForm Face (Coef n) (k + 1)) (x + s • shVec v)).curryLeft
      (shVec v)) volume 0 1 := by
  have h := (contDiffOn_cartan_integrand (U := faceSet) (shVec v) (Form.smooth W)).continuousOn
  have hc : Continuous (fun s : ℝ => ((x, s) : Face × ℝ)) := Continuous.prodMk_right x
  exact (h.comp_continuous hc fun s => shVec_smul_mem hx v s).intervalIntegrable 0 1

theorem EqvS.cartanForm {c : ℝ} {W : Form (F := Coef n) faceSet (k + 1)} (h : EqvS σ c W)
    (v : Fin 2 → ℝ) : EqvS σ c (cartanForm v W) := by
  intro m x hx
  have hxu : x + shVec (c • intVec m) ∈ faceSet := by
    have := shVec_smul_mem hx (c • intVec m) 1
    simpa using this
  rw [cartanForm_apply v W hxu, cartanForm_apply v W hx]
  have hint := integrable_cartan_slice W v hx
  have hcomm := (compAltCLM (σ (c • intVec m)) k).intervalIntegral_comp_comm hint
  change _ = compAltCLM (σ (c • intVec m)) k _
  rw [← hcomm]
  refine intervalIntegral.integral_congr fun s hs => ?_
  have hs' : s ∈ Icc (0:ℝ) 1 := by simpa using hs
  have hxs : x + s • shVec v ∈ faceSet := shVec_smul_mem hx v s
  have e : x + shVec (c • intVec m) + s • shVec v = (x + s • shVec v) + shVec (c • intVec m) := by
    abel
  show ((W : RawForm Face (Coef n) (k + 1)) (x + shVec (c • intVec m) + s • shVec v)).curryLeft
      (shVec v) = (σ (c • intVec m)).compContinuousAlternatingMap
        (((W : RawForm Face (Coef n) (k + 1)) (x + s • shVec v)).curryLeft (shVec v))
  rw [e, h m _ hxs]
  rfl

theorem continuous_thetaIntegrand_uncurry (hσ : ContDiff ℝ ∞ σ) (c : ℝ)
    (W : Form (F := Coef n) faceSet (k + 1)) {x : Face} (hx : x ∈ faceSet) :
    Continuous (Function.uncurry fun a b : ℝ => thetaIntegrand σ c W ((x, a), b)) := by
  have h := (contDiffOn_thetaIntegrand hσ c W).continuousOn
  rw [← continuousOn_univ]
  have hc : Continuous (fun p : ℝ × ℝ => (((x, p.1), p.2) : (Face × ℝ) × ℝ)) := by fun_prop
  exact h.comp hc.continuousOn fun p _ => ⟨⟨hx, trivial⟩, trivial⟩

theorem EqvS.thetaForm (h : UniRep σ) {c : ℝ} {W : Form (F := Coef n) faceSet (k + 1)}
    (hE : EqvS σ c W) : EqvS σ c (thetaForm h.smooth c W) := by
  intro m x hx
  have hxu : x + shVec (c • intVec m) ∈ faceSet := by
    have := shVec_smul_mem hx (c • intVec m) 1
    simpa using this
  rw [thetaForm_apply _ _ _ hxu, thetaForm_apply _ _ _ hx]
  unfold thetaRaw
  have hcomm := iterIntegral_clm_comm (compAltCLM (σ (c • intVec m)) k)
    (fun a b => thetaIntegrand σ c W ((x, a), b)) (continuous_thetaIntegrand_uncurry h.smooth c W hx)
  change _ = compAltCLM (σ (c • intVec m)) k _
  rw [hcomm]
  refine intervalIntegral.integral_congr fun a _ => ?_
  refine intervalIntegral.integral_congr fun b _ => ?_
  have hcart := (EqvS.cartanForm hE (c • ![a, b])) m x hx
  rw [cartanForm_apply _ W hxu, cartanForm_apply _ W hx] at hcart
  show (σ (-(c • ![a, b]))).compContinuousAlternatingMap
      (cartanRaw (shVec (c • ![a, b])) (W : RawForm Face (Coef n) (k + 1)) (x + shVec (c • intVec m))) =
    (σ (c • intVec m)).compContinuousAlternatingMap ((σ (-(c • ![a, b]))).compContinuousAlternatingMap
      (cartanRaw (shVec (c • ![a, b])) (W : RawForm Face (Coef n) (k + 1)) x))
  have hc2 : cartanRaw (shVec (c • ![a, b])) (W : RawForm Face (Coef n) (k + 1)) (x + shVec (c • intVec m)) =
      (σ (c • intVec m)).compContinuousAlternatingMap
        (cartanRaw (shVec (c • ![a, b])) (W : RawForm Face (Coef n) (k + 1)) x) := hcart
  rw [hc2]
  ext w
  exact congrArg (fun S : Coef n →L[ℝ] Coef n => S _) ((h.comm (-(c • ![a, b])) (c • intVec m)).eq)

theorem intVec_single (i : Fin 2) : intVec (Pi.single i 1 : Fin 2 → ℤ) = Pi.single i 1 := by
  funext j
  fin_cases i <;> fin_cases j <;> simp [intVec]

/-- **Theorem K (abelian Kasuya, existence form).** For a closed lattice-equivariant form `W` of
degree `k + 1 ≥ 1` on the boundary model, the torus average differs from `W` by the differential of a
lattice-equivariant form of degree `k`. -/
theorem exists_equivariant_primitive (h : UniRep σ) {c : ℝ} (hc : c ≠ 0)
    (W : Form (F := Coef n) faceSet (k + 1)) (hW : d isOpen_faceSet (k + 1) W = 0)
    (hE : EqvS σ c W) :
    ∃ Ξ : Form (F := Coef n) faceSet k, EqvS σ c Ξ ∧
      d isOpen_faceSet k Ξ = avFormS h.smooth c W - W := by
  obtain ⟨T₁, T₂, hT₁, hT₂, hP⟩ := Pavg_sub_one_mem h hc
  have hPy : ∀ y : Coef n, Pavg σ c y = y + T₁ ((σ (c • Pi.single 0 1) - 1) y) +
      T₂ ((σ (c • Pi.single 1 1) - 1) y) := by
    intro y
    have := congrArg (fun S : Coef n →L[ℝ] Coef n => S y) (sub_eq_iff_eq_add'.mp hP)
    simpa [add_assoc] using this
  refine ⟨thetaForm h.smooth c W + ZigZag.twForm T₁ k (cartanForm (c • Pi.single 0 1) W) +
    ZigZag.twForm T₂ k (cartanForm (c • Pi.single 1 1) W), ?_, ?_⟩
  · exact ((EqvS.thetaForm h hE).add ((EqvS.cartanForm hE _).twForm hT₁)).add
      ((EqvS.cartanForm hE _).twForm hT₂)
  · rw [map_add, map_add, ZigZag.d_twForm isOpen_faceSet, ZigZag.d_twForm isOpen_faceSet,
      d_thetaForm h.smooth c W hW]
    apply Form.ext
    intro x hx
    have hd0 := d_cartanForm_apply (c • Pi.single 0 1) W hW hx
    have hd1 := d_cartanForm_apply (c • Pi.single 1 1) W hW hx
    have hx0 : (W : RawForm Face (Coef n) (k + 1)) (x + shVec (c • Pi.single 0 1)) =
        (σ (c • Pi.single 0 1)).compContinuousAlternatingMap ((W : RawForm Face (Coef n) (k + 1)) x) := by
      have := hE (Pi.single 0 1) x hx
      rwa [intVec_single] at this
    have hx1 : (W : RawForm Face (Coef n) (k + 1)) (x + shVec (c • Pi.single 1 1)) =
        (σ (c • Pi.single 1 1)).compContinuousAlternatingMap ((W : RawForm Face (Coef n) (k + 1)) x) := by
      have := hE (Pi.single 1 1) x hx
      rwa [intVec_single] at this
    simp only [Submodule.coe_add, Submodule.coe_sub, Pi.add_apply, Pi.sub_apply,
      ZigZag.twForm_apply, coefficientFormMap_apply, hd0, hd1, hx0, hx1]
    ext v
    simp only [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.sub_apply]
    show (((avFormS h.smooth c W : Form (F := Coef n) faceSet (k + 1)) :
        RawForm Face (Coef n) (k + 1)) x) v - Pavg σ c (((W : RawForm Face (Coef n) (k + 1)) x) v) +
      T₁ ((σ (c • Pi.single 0 1)) (((W : RawForm Face (Coef n) (k + 1)) x) v) -
        (((W : RawForm Face (Coef n) (k + 1)) x) v)) +
      T₂ ((σ (c • Pi.single 1 1)) (((W : RawForm Face (Coef n) (k + 1)) x) v) -
        (((W : RawForm Face (Coef n) (k + 1)) x) v)) =
      (((avFormS h.smooth c W : Form (F := Coef n) faceSet (k + 1)) :
        RawForm Face (Coef n) (k + 1)) x) v - (((W : RawForm Face (Coef n) (k + 1)) x) v)
    rw [hPy]
    simp only [_root_.sub_apply, one_apply_eq_self, map_sub]
    abel

end TernaryPeriodPolynomials.Argument.EisensteinClass
