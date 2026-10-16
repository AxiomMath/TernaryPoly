module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.AvInv

@[expose] public section


/-!
# General-degree, general-representation torus average on the boundary model

`Average.lean` treats degree-two forms and the representation `ρ(t_v)`. Here the same construction is made
for forms of every degree `k` and for an arbitrary smooth family `σ : ℝ² → End(Coef n)` of coefficient
transports (later `σ = ρ∘M` for an integral matrix `M`, as needed for the Levi-twisted equivariance
conditions): `shiftS k σ v W = σ(-v) τ_v^* W`, its pointwise formula `shiftS_apply`, the average
`avFormS` (smooth, `contDiffOn_avIntegrandS`; closed when `W` is closed, `d_avFormS`).

Formalized by Claude Sonnet 5.5.
-/

open ContinuousAlternatingMap
open scoped ContDiff MatrixGroups
noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.SeedC3.Psi TernaryPoly.SmoothLocalDeRham
  TernaryPoly.SmoothCoveringDeRham

variable {n : ℕ} (k : ℕ) (σ : (Fin 2 → ℝ) → (Coef n →L[ℝ] Coef n))

/-- General-degree, general-representation translated form `W_v = σ(-v) τ_v^* W`. -/
def shiftS (v : Fin 2 → ℝ) : Form (F := Coef n) faceSet k →ₗ[ℝ] Form (F := Coef n) faceSet k :=
  (ZigZag.twForm (σ (-v)) k).comp
    (ZigZag.pullForm isOpen_faceSet trPD.action (Multiplicative.ofAdd v) k)

theorem shiftS_apply (v : Fin 2 → ℝ) (W : Form (F := Coef n) faceSet k) {x : Face}
    (hx : x ∈ faceSet) :
    ((shiftS k σ v W : Form (F := Coef n) faceSet k) : RawForm Face (Coef n) k) x =
      (σ (-v)).compContinuousAlternatingMap
        ((W : RawForm Face (Coef n) k) (x + shVec v)) := by
  unfold shiftS
  simp only [LinearMap.comp_apply]
  rw [ZigZag.twForm_apply]
  have hpull : ((ZigZag.pullForm isOpen_faceSet trPD.action (Multiplicative.ofAdd v) k W :
      Form (F := Coef n) faceSet k) : RawForm Face (Coef n) k) x =
      (W : RawForm Face (Coef n) k) (x + shVec v) := by
    rw [ZigZag.pullForm_apply isOpen_faceSet trPD.action _ _ hx]
    have hact : trPD.action.act (Multiplicative.ofAdd v) = fun y : Face => y + shVec v := by
      funext y; exact trPD_act (Multiplicative.ofAdd v) y
    simp only [pullRaw, hact, (hasFDerivAt_add_const_face (shVec v) x).fderiv]
    ext w
    simp
  rw [hpull]
  rfl

/-- The integrand of the average as a function of `((x, a), b)`. -/
def avIntegrandS (c : ℝ) (W : Form (F := Coef n) faceSet k) (p : (Face × ℝ) × ℝ) :
    Face [⋀^Fin k]→L[ℝ] Coef n :=
  ((shiftS k σ (c • ![p.1.2, p.2]) W : Form (F := Coef n) faceSet k) :
    RawForm Face (Coef n) k) p.1.1

variable {k σ}

theorem contDiffOn_avIntegrandS (hσ : ContDiff ℝ ∞ σ) (c : ℝ) (W : Form (F := Coef n) faceSet k) :
    ContDiffOn ℝ ∞ (avIntegrandS k σ c W)
      ((faceSet ×ˢ (Set.univ : Set ℝ)) ×ˢ (Set.univ : Set ℝ)) := by
  have hshift : ContDiff ℝ ∞ (fun p : (Face × ℝ) × ℝ => shVec (c • ![p.1.2, p.2])) := by
    refine contDiff_pi.2 fun i => ?_
    fin_cases i <;> simp [shVec] <;> fun_prop
  have hL : ContDiff ℝ ∞ (fun p : (Face × ℝ) × ℝ => σ (-(c • ![p.1.2, p.2]))) := by
    refine hσ.comp ?_
    refine contDiff_pi.2 fun i => ?_
    fin_cases i <;> simp <;> fun_prop
  have harg : ContDiff ℝ ∞ (fun p : (Face × ℝ) × ℝ => p.1.1 + shVec (c • ![p.1.2, p.2])) :=
    (contDiff_fst.comp contDiff_fst).add hshift
  have hw : ContDiffOn ℝ ∞ (fun p : (Face × ℝ) × ℝ =>
      (W : RawForm Face (Coef n) k) (p.1.1 + shVec (c • ![p.1.2, p.2])))
      ((faceSet ×ˢ (Set.univ : Set ℝ)) ×ˢ (Set.univ : Set ℝ)) :=
    (Form.smooth W).comp harg.contDiffOn fun p hp => shVec_mem hp.1.1 _
  have hb : IsBoundedBilinearMap ℝ (fun q : (Coef n →L[ℝ] Coef n) × (Face [⋀^Fin k]→L[ℝ] Coef n) =>
      q.1.compContinuousAlternatingMap q.2) :=
    { add_left := fun L₁ L₂ w => by ext; simp
      smul_left := fun r L w => by ext; simp
      add_right := fun L w₁ w₂ => by ext; simp
      smul_right := fun r L w => by ext; simp
      bound := ⟨1, one_pos, fun L w => by simpa using L.norm_compContinuousAlternatingMap_le w⟩ }
  have := hb.contDiff.comp_contDiffOn (hL.contDiffOn.prodMk hw)
  refine this.congr fun p hp => ?_
  exact shiftS_apply k σ _ W hp.1.1

/-! ### The average -/

/-- The torus average `∫₀¹∫₀¹ shiftS σ (c·(a,b)) W da db` as a raw form. -/
def avRawS (σ : (Fin 2 → ℝ) → (Coef n →L[ℝ] Coef n)) (c : ℝ) (W : Form (F := Coef n) faceSet k)
    (x : Face) : Face [⋀^Fin k]→L[ℝ] Coef n :=
  ∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1, avIntegrandS k σ c W ((x, a), b)

theorem contDiffOn_avRawS (hσ : ContDiff ℝ ∞ σ) (c : ℝ) (W : Form (F := Coef n) faceSet k) :
    ContDiffOn ℝ ∞ (avRawS (k := k) σ c W) faceSet :=
  contDiffOn_iteratedIntegral isOpen_faceSet _ (contDiffOn_avIntegrandS hσ c W)

/-- **The torus average** as a chart form. -/
def avFormS (hσ : ContDiff ℝ ∞ σ) (c : ℝ) (W : Form (F := Coef n) faceSet k) :
    Form (F := Coef n) faceSet k :=
  restrictForm faceSet (avRawS (k := k) σ c W) (contDiffOn_avRawS hσ c W)

theorem avFormS_apply (hσ : ContDiff ℝ ∞ σ) (c : ℝ) (W : Form (F := Coef n) faceSet k) {x : Face}
    (hx : x ∈ faceSet) :
    ((avFormS hσ c W : Form (F := Coef n) faceSet k) : RawForm Face (Coef n) k) x =
      avRawS (k := k) σ c W x :=
  restrictForm_apply _ _ hx

/-! ### Closedness -/

theorem d_shiftS (v : Fin 2 → ℝ) (W : Form (F := Coef n) faceSet k)
    (hW : d isOpen_faceSet k W = 0) : d isOpen_faceSet k (shiftS k σ v W) = 0 := by
  unfold shiftS
  simp only [LinearMap.comp_apply]
  rw [ZigZag.d_twForm isOpen_faceSet, ZigZag.d_pullForm isOpen_faceSet trPD.action, hW]
  simp

theorem extDeriv_avIntegrandS (c : ℝ) (W : Form (F := Coef n) faceSet k)
    (hW : d isOpen_faceSet k W = 0) {x : Face} (hx : x ∈ faceSet) (a b : ℝ) :
    extDeriv (fun y => avIntegrandS k σ c W ((y, a), b)) x = 0 := by
  have h := d_shiftS (σ := σ) (c • ![a, b]) W hW
  have hd := d_apply isOpen_faceSet (shiftS k σ (c • ![a, b]) W) hx
  rw [h] at hd
  exact hd.symm

theorem d_avFormS (hσ : ContDiff ℝ ∞ σ) (c : ℝ) (W : Form (F := Coef n) faceSet k)
    (hW : d isOpen_faceSet k W = 0) : d isOpen_faceSet k (avFormS hσ c W) = 0 := by
  apply Form.ext
  intro x hx
  rw [d_apply isOpen_faceSet _ hx]
  have heq : (avFormS hσ c W : RawForm Face (Coef n) k) =ᶠ[nhds x] avRawS (k := k) σ c W := by
    filter_upwards [isOpen_faceSet.mem_nhds hx] with y hy using avFormS_apply hσ c W hy
  rw [heq.extDeriv_eq (𝕜 := ℝ)]
  have hf := contDiffOn_avIntegrandS hσ c W
  have hD := hasFDerivAt_iteratedIntegral isOpen_faceSet (avIntegrandS k σ c W) hf hx
  unfold extDeriv
  have hav : avRawS (k := k) σ c W = fun y => ∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1,
      avIntegrandS k σ c W ((y, a), b) := rfl
  rw [hav, hD.fderiv]
  have hDset : IsOpen (((faceSet ×ˢ (Set.univ : Set ℝ)) ×ˢ (Set.univ : Set ℝ)) :
      Set ((Face × ℝ) × ℝ)) := (isOpen_faceSet.prod isOpen_univ).prod isOpen_univ
  have hM : ContDiffOn ℝ ∞ (fun p => (fderiv ℝ (avIntegrandS k σ c W) p).comp (inl2 Face))
      ((faceSet ×ˢ (Set.univ : Set ℝ)) ×ˢ (Set.univ : Set ℝ)) :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen hDset).mp hf).2.clm_comp contDiffOn_const
  have hcont : Continuous (Function.uncurry fun a b : ℝ =>
      (fderiv ℝ (avIntegrandS k σ c W) ((x, a), b)).comp (inl2 Face)) := by
    rw [← continuousOn_univ]
    refine hM.continuousOn.comp (continuous_const.prodMk continuous_fst |>.prodMk
      continuous_snd).continuousOn fun p _ => ⟨⟨hx, trivial⟩, trivial⟩
  have hcomm := iterIntegral_clm_comm
    (alternatizeUncurryFinCLM ℝ Face (Coef n))
    (fun a b => (fderiv ℝ (avIntegrandS k σ c W) ((x, a), b)).comp (inl2 Face)) hcont
  have e : ∀ a b : ℝ, alternatizeUncurryFinCLM ℝ Face (Coef n)
      ((fderiv ℝ (avIntegrandS k σ c W) ((x, a), b)).comp (inl2 Face)) = 0 := by
    intro a b
    have hdiff : DifferentiableAt ℝ (avIntegrandS k σ c W) ((x, a), b) :=
      ((hf _ ⟨⟨hx, trivial⟩, trivial⟩).contDiffAt
        (hDset.mem_nhds ⟨⟨hx, trivial⟩, trivial⟩)).differentiableAt (by simp)
    have hpath : HasFDerivAt (fun y : Face => ((y, a), b)) (inl2 Face) x := by
      refine (((hasFDerivAt_id x).prodMk (hasFDerivAt_const a x)).prodMk
        (hasFDerivAt_const b x)).congr_fderiv ?_
      ext v <;> simp [inl2]
    have hch := hdiff.hasFDerivAt.comp x hpath
    have h3 : fderiv ℝ (fun y : Face => avIntegrandS k σ c W ((y, a), b)) x =
        (fderiv ℝ (avIntegrandS k σ c W) ((x, a), b)).comp (inl2 Face) := hch.fderiv
    have := extDeriv_avIntegrandS (σ := σ) c W hW hx a b
    unfold extDeriv at this
    rw [h3] at this
    exact this
  change (alternatizeUncurryFinCLM ℝ Face (Coef n))
    (∫ (a : ℝ) (b : ℝ) in 0..1, fderiv ℝ (avIntegrandS k σ c W) ((x, a), b) ∘SL inl2 Face) = 0
  rw [hcomm]
  simp only [e]
  simp

end TernaryPeriodPolynomials.Argument.EisensteinClass
