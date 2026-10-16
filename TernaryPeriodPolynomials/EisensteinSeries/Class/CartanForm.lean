module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Cartan
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Gen

@[expose] public section


/-!
# The Cartan primitive of a closed form on the boundary model, as a chart form

`cartanForm v W = ∫₀¹ ι_v W(· + s v) ds` is a chart form (`contDiffOn_cartanRaw`) and, for a closed `W`,
`d (cartanForm v W) = W(· + v) - W` (`d_cartanForm_apply`, from `cartan_raw`). `contDiffOn_cartanParam`
is the joint smoothness in the point and in the translation parameters `v = c (a, b)`.

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

theorem shVec_smul_mem {x : Face} (hx : x ∈ faceSet) (v : Fin 2 → ℝ) (s : ℝ) :
    x + s • shVec v ∈ faceSet := by
  have : 0 < x 3 := hx
  show 0 < (x + s • shVec v) 3
  simpa [shVec] using this

theorem faceSet_stable (v : Fin 2 → ℝ) : ∀ x ∈ faceSet, ∀ s ∈ Icc (0:ℝ) 1, x + s • shVec v ∈ faceSet :=
  fun _ hx s _ => shVec_smul_mem hx v s

theorem contDiffOn_cartanRaw (v : Fin 2 → ℝ) (W : Form (F := Coef n) faceSet (k + 1)) :
    ContDiffOn ℝ ∞ (cartanRaw (shVec v) (W : RawForm Face (Coef n) (k + 1))) faceSet := by
  have hD := cartan_domain_open isOpen_faceSet (shVec v)
  have hf := contDiffOn_cartan_integrand (U := faceSet) (shVec v) (Form.smooth W)
  have := parameterIntegral_smooth hD hf
  refine this.mono ?_
  intro x hx s hs
  exact shVec_smul_mem hx v s

/-- The Cartan primitive `B_v W = ∫₀¹ ι_v W(· + s v) ds` as a chart form. -/
def cartanForm (v : Fin 2 → ℝ) (W : Form (F := Coef n) faceSet (k + 1)) :
    Form (F := Coef n) faceSet k :=
  restrictForm faceSet (cartanRaw (shVec v) (W : RawForm Face (Coef n) (k + 1)))
    (contDiffOn_cartanRaw v W)

theorem cartanForm_apply (v : Fin 2 → ℝ) (W : Form (F := Coef n) faceSet (k + 1)) {x : Face}
    (hx : x ∈ faceSet) :
    ((cartanForm v W : Form (F := Coef n) faceSet k) : RawForm Face (Coef n) k) x =
      ∫ s in (0:ℝ)..1, ((W : RawForm Face (Coef n) (k + 1)) (x + s • shVec v)).curryLeft (shVec v) :=
  restrictForm_apply _ _ hx

/-- **Cartan homotopy for the translation by `v`**: for a closed form,
`d B_v W = τ_v^* W - W` (pointwise: `W(x + v) - W(x)`). -/
theorem d_cartanForm_apply (v : Fin 2 → ℝ) (W : Form (F := Coef n) faceSet (k + 1))
    (hW : d isOpen_faceSet (k + 1) W = 0) {x : Face} (hx : x ∈ faceSet) :
    ((d isOpen_faceSet k (cartanForm v W) : Form (F := Coef n) faceSet (k + 1)) :
        RawForm Face (Coef n) (k + 1)) x =
      (W : RawForm Face (Coef n) (k + 1)) (x + shVec v) - (W : RawForm Face (Coef n) (k + 1)) x := by
  rw [d_apply isOpen_faceSet _ hx]
  have heq : (cartanForm v W : RawForm Face (Coef n) k) =ᶠ[nhds x]
      cartanRaw (shVec v) (W : RawForm Face (Coef n) (k + 1)) := by
    filter_upwards [isOpen_faceSet.mem_nhds hx] with y hy using cartanForm_apply v W hy
  rw [heq.extDeriv_eq (𝕜 := ℝ)]
  have h := cartan_raw isOpen_faceSet (shVec v) (faceSet_stable v) (Form.smooth W) hx
  have hz : cartanRaw (shVec v) (extDeriv (W : RawForm Face (Coef n) (k + 1))) x = 0 := by
    unfold cartanRaw
    have : ∀ s ∈ Icc (0:ℝ) 1, (extDeriv (W : RawForm Face (Coef n) (k + 1)) (x + s • shVec v)).curryLeft
        (shVec v) = 0 := by
      intro s hs
      have hd := d_apply isOpen_faceSet W (shVec_smul_mem hx v s)
      rw [hW] at hd
      have : extDeriv (W : RawForm Face (Coef n) (k + 1)) (x + s • shVec v) = 0 := hd.symm
      rw [this]
      ext w
      simp
    rw [intervalIntegral.integral_congr (g := fun _ => 0)
      (fun s hs => this s (by simpa using hs))]
    simp
  rw [hz, add_zero] at h
  exact h

/-! ### The averaged Cartan primitive `Θ` -/

/-- The vector `shVec (c·(a, b))` as a function of the parameter `((x, a), b)`. -/
def tvec (c : ℝ) (p : (Face × ℝ) × ℝ) : Face := shVec (c • ![p.1.2, p.2])

theorem contDiff_tvec (c : ℝ) : ContDiff ℝ ∞ (tvec c) := by
  refine contDiff_pi.2 fun i => ?_
  fin_cases i <;> simp [tvec, shVec] <;> fun_prop

/-- Joint smoothness of the Cartan primitive in the point and in the translation parameters. -/
theorem contDiffOn_cartanParam (c : ℝ) (W : Form (F := Coef n) faceSet (k + 1)) :
    ContDiffOn ℝ ∞ (fun p : (Face × ℝ) × ℝ =>
      cartanRaw (tvec c p) (W : RawForm Face (Coef n) (k + 1)) p.1.1)
      ((faceSet ×ˢ (Set.univ : Set ℝ)) ×ˢ (Set.univ : Set ℝ)) := by
  let D' : Set (((Face × ℝ) × ℝ) × ℝ) :=
    {q | q.1.1.1 + q.2 • tvec c q.1 ∈ faceSet}
  have hD' : IsOpen D' := isOpen_faceSet.preimage (by
    have := contDiff_tvec c
    fun_prop)
  have hmap : ContDiff ℝ ∞ (fun q : ((Face × ℝ) × ℝ) × ℝ => q.1.1.1 + q.2 • tvec c q.1) := by
    have := contDiff_tvec c
    exact ((contDiff_fst.comp (contDiff_fst.comp contDiff_fst)).add
      (contDiff_snd.smul (this.comp contDiff_fst)))
  have hW1 : ContDiffOn ℝ ∞ (fun q : ((Face × ℝ) × ℝ) × ℝ =>
      (W : RawForm Face (Coef n) (k + 1)) (q.1.1.1 + q.2 • tvec c q.1)) D' :=
    (Form.smooth W).comp hmap.contDiffOn (fun q hq => hq)
  let L : (Face [⋀^Fin (k + 1)]→L[ℝ] Coef n) →L[ℝ] (Face →L[ℝ] Face [⋀^Fin k]→L[ℝ] Coef n) :=
    (curryLeftLI (𝕜 := ℝ) (E := Face) (F := Coef n) (n := k)).toContinuousLinearMap
  have hL := ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
    (E := Face [⋀^Fin (k + 1)]→L[ℝ] Coef n) (F := Face →L[ℝ] Face [⋀^Fin k]→L[ℝ] Coef n) L
  have hcurry := hL.comp_contDiffOn hW1
  have hf : ContDiffOn ℝ ∞ (fun q : ((Face × ℝ) × ℝ) × ℝ =>
      (W : RawForm Face (Coef n) (k + 1)) (q.1.1.1 + q.2 • tvec c q.1) |>.curryLeft (tvec c q.1)) D' :=
    hcurry.clm_apply ((contDiff_tvec c).comp contDiff_fst).contDiffOn
  have := parameterIntegral_smooth hD' hf
  refine this.mono ?_
  intro p hp s hs
  exact shVec_smul_mem hp.1.1 _ s

end TernaryPeriodPolynomials.Argument.EisensteinClass
