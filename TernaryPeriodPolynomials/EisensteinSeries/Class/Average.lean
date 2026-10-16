module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Shift
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Double
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Periodic
public import TernaryPeriodPolynomials.EisensteinSeries.Class.IterComm

@[expose] public section


/-!
# The torus average of a form on the boundary model, and its invariance

Paper: "Restriction and
averaging on the fiber": average, with coefficient transport, over the compact fiber
`Nℤ² \\ ℝ²` with Haar volume one; "this average is a cochain map" and "both maps commute with the
lattice-preserving Levi action".

For a chart 2-form `F` on `e(P) = ℝ² × ℍ` and the lattice scale `c` (`= N`), `avForm n c F` is the form
`∫₀¹∫₀¹ F_{c·(a, b)} da db`, with `F_v = ρ(t_v)⁻¹ τ_v^* F` (`shiftForm`). It is smooth
(`contDiffOn_avRaw`, differentiation under the integral, `Double.lean`), closed when `F` is closed
(`d_avForm`), and, when `F` is invariant under a plane parabolic group `D` with `Γ_P = cℤ² ⋊ Λ`
(`LatticeData`: integral Levi blocks, the radical lattice `cℤ²` realized in the group),
`D`-invariant: `g^*(Av F) = ρ(g) Av F` (`pullForm_avForm`: the Levi block permutes the translations,
`pullForm_shiftForm`, the family is `cℤ²`-periodic, `shiftForm_add_lattice`, and the unit-square
integral of a periodic function is `SL₂(ℤ)`-invariant, `sqInt_zAct`).

This file does NOT prove that `Av F` has the same de Rham class as `F` (Kasuya's nilmanifold theorem in the
abelian case) nor any property of the sums of the Eisenstein series.

Formalized by Claude Sonnet 5.5.
-/

open ContinuousAlternatingMap
open scoped ContDiff MatrixGroups
noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.SeedC3.Psi TernaryPoly.SmoothLocalDeRham
  TernaryPoly.SmoothCoveringDeRham

variable (n : ℕ)

/-- The translation vector as a vector of the face coordinates. -/
def shVec (v : Fin 2 → ℝ) : Face := ![v 0, v 1, 0, 0]

theorem hasFDerivAt_add_const_face (c : Face) (x : Face) :
    HasFDerivAt (fun y : Face => y + c) (ContinuousLinearMap.id ℝ Face) x :=
  (hasFDerivAt_id x).add_const c

/-- **Pointwise formula for the translated form**:
`(F_v)(x) = ρ(t_v)⁻¹ ∘ F(x + v)`. -/
theorem shiftForm_apply (v : Fin 2 → ℝ) (F : Form (F := Coef n) faceSet 2) {x : Face}
    (hx : x ∈ faceSet) :
    ((shiftForm n v F : Form (F := Coef n) faceSet 2) : RawForm Face (Coef n) 2) x =
      (trL n (-v)).compContinuousAlternatingMap
        ((F : RawForm Face (Coef n) 2) (x + shVec v)) := by
  unfold shiftForm
  simp only [LinearMap.comp_apply]
  rw [ZigZag.twForm_apply]
  have hpull : ((ZigZag.pullForm isOpen_faceSet trPD.action (Multiplicative.ofAdd v) 2 F :
      Form (F := Coef n) faceSet 2) : RawForm Face (Coef n) 2) x =
      (F : RawForm Face (Coef n) 2) (x + shVec v) := by
    rw [ZigZag.pullForm_apply isOpen_faceSet trPD.action _ _ hx]
    have hact : trPD.action.act (Multiplicative.ofAdd v) = fun y : Face => y + shVec v := by
      funext y; exact trPD_act (Multiplicative.ofAdd v) y
    simp only [pullRaw, hact, (hasFDerivAt_add_const_face (shVec v) x).fderiv]
    ext w
    simp
  rw [hpull]
  rfl

/-- The integrand of the average as a function of `((x, a), b)`: `F_{c·(a, b)}(x)`. -/
def avIntegrand (c : ℝ) (F : Form (F := Coef n) faceSet 2) (p : (Face × ℝ) × ℝ) :
    Face [⋀^Fin 2]→L[ℝ] Coef n :=
  ((shiftForm n (c • ![p.1.2, p.2]) F : Form (F := Coef n) faceSet 2) :
    RawForm Face (Coef n) 2) p.1.1

theorem shVec_mem {x : Face} (hx : x ∈ faceSet) (v : Fin 2 → ℝ) : x + shVec v ∈ faceSet := by
  have : 0 < x 3 := hx
  show 0 < (x + shVec v) 3
  simpa [shVec] using this

theorem contDiffOn_avIntegrand (c : ℝ) (F : Form (F := Coef n) faceSet 2) :
    ContDiffOn ℝ ∞ (avIntegrand n c F) ((faceSet ×ˢ (Set.univ : Set ℝ)) ×ˢ (Set.univ : Set ℝ)) := by
  have hshift : ContDiff ℝ ∞ (fun p : (Face × ℝ) × ℝ => shVec (c • ![p.1.2, p.2])) := by
    refine contDiff_pi.2 fun i => ?_
    fin_cases i <;> simp [shVec] <;> fun_prop
  have hL : ContDiff ℝ ∞ (fun p : (Face × ℝ) × ℝ => trL n (-(c • ![p.1.2, p.2]))) := by
    refine (contDiff_trL n).comp ?_
    refine contDiff_pi.2 fun i => ?_
    fin_cases i <;> simp <;> fun_prop
  have harg : ContDiff ℝ ∞ (fun p : (Face × ℝ) × ℝ => p.1.1 + shVec (c • ![p.1.2, p.2])) :=
    (contDiff_fst.comp contDiff_fst).add hshift
  have hw : ContDiffOn ℝ ∞ (fun p : (Face × ℝ) × ℝ =>
      (F : RawForm Face (Coef n) 2) (p.1.1 + shVec (c • ![p.1.2, p.2])))
      ((faceSet ×ˢ (Set.univ : Set ℝ)) ×ˢ (Set.univ : Set ℝ)) :=
    (Form.smooth F).comp harg.contDiffOn fun p hp => shVec_mem hp.1.1 _
  have hb : IsBoundedBilinearMap ℝ (fun q : (Coef n →L[ℝ] Coef n) × (Face [⋀^Fin 2]→L[ℝ] Coef n) =>
      q.1.compContinuousAlternatingMap q.2) :=
    { add_left := fun L₁ L₂ w => by ext; simp
      smul_left := fun r L w => by ext; simp
      add_right := fun L w₁ w₂ => by ext; simp
      smul_right := fun r L w => by ext; simp
      bound := ⟨1, one_pos, fun L w => by simpa using L.norm_compContinuousAlternatingMap_le w⟩ }
  have := hb.contDiff.comp_contDiffOn (hL.contDiffOn.prodMk hw)
  refine this.congr fun p hp => ?_
  exact shiftForm_apply n _ F hp.1.1

/-! ### The average -/

/-- The average `∫_{[0,1]²} F_{c·(a,b)} da db` of the translated, transported forms (raw form). -/
def avRaw (c : ℝ) (F : Form (F := Coef n) faceSet 2) (x : Face) : Face [⋀^Fin 2]→L[ℝ] Coef n :=
  ∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1, avIntegrand n c F ((x, a), b)

theorem contDiffOn_avRaw (c : ℝ) (F : Form (F := Coef n) faceSet 2) :
    ContDiffOn ℝ ∞ (avRaw n c F) faceSet :=
  contDiffOn_iteratedIntegral isOpen_faceSet _ (contDiffOn_avIntegrand n c F)

/-- **The torus average of a form on the face**, as a chart form. -/
def avForm (c : ℝ) (F : Form (F := Coef n) faceSet 2) : Form (F := Coef n) faceSet 2 :=
  restrictForm faceSet (avRaw n c F) (contDiffOn_avRaw n c F)

theorem avForm_apply (c : ℝ) (F : Form (F := Coef n) faceSet 2) {x : Face} (hx : x ∈ faceSet) :
    ((avForm n c F : Form (F := Coef n) faceSet 2) : RawForm Face (Coef n) 2) x =
      avRaw n c F x :=
  restrictForm_apply _ _ hx

/-! ### Closedness -/

theorem d_shiftForm (v : Fin 2 → ℝ) (F : Form (F := Coef n) faceSet 2)
    (hF : d isOpen_faceSet 2 F = 0) : d isOpen_faceSet 2 (shiftForm n v F) = 0 := by
  unfold shiftForm
  simp only [LinearMap.comp_apply]
  rw [ZigZag.d_twForm isOpen_faceSet, ZigZag.d_pullForm isOpen_faceSet trPD.action, hF]
  simp

theorem extDeriv_avIntegrand (c : ℝ) (F : Form (F := Coef n) faceSet 2)
    (hF : d isOpen_faceSet 2 F = 0) {x : Face} (hx : x ∈ faceSet) (a b : ℝ) :
    extDeriv (fun y => avIntegrand n c F ((y, a), b)) x = 0 := by
  have h := d_shiftForm n (c • ![a, b]) F hF
  have hd := d_apply isOpen_faceSet (shiftForm n (c • ![a, b]) F) hx
  rw [h] at hd
  exact hd.symm

theorem d_avForm (c : ℝ) (F : Form (F := Coef n) faceSet 2) (hF : d isOpen_faceSet 2 F = 0) :
    d isOpen_faceSet 2 (avForm n c F) = 0 := by
  apply Form.ext
  intro x hx
  rw [d_apply isOpen_faceSet _ hx]
  have heq : (avForm n c F : RawForm Face (Coef n) 2) =ᶠ[nhds x] avRaw n c F := by
    filter_upwards [isOpen_faceSet.mem_nhds hx] with y hy using avForm_apply n c F hy
  rw [heq.extDeriv_eq (𝕜 := ℝ)]
  have hf := contDiffOn_avIntegrand n c F
  have hD := hasFDerivAt_iteratedIntegral isOpen_faceSet (avIntegrand n c F) hf hx
  unfold extDeriv
  have hav : avRaw n c F = fun y => ∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1, avIntegrand n c F ((y, a), b) :=
    rfl
  rw [hav, hD.fderiv]
  have hDset : IsOpen (((faceSet ×ˢ (Set.univ : Set ℝ)) ×ˢ (Set.univ : Set ℝ)) :
      Set ((Face × ℝ) × ℝ)) := (isOpen_faceSet.prod isOpen_univ).prod isOpen_univ
  have hM : ContDiffOn ℝ ∞ (fun p => (fderiv ℝ (avIntegrand n c F) p).comp (inl2 Face))
      ((faceSet ×ˢ (Set.univ : Set ℝ)) ×ˢ (Set.univ : Set ℝ)) :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen hDset).mp hf).2.clm_comp contDiffOn_const
  have hcont : Continuous (Function.uncurry fun a b : ℝ =>
      (fderiv ℝ (avIntegrand n c F) ((x, a), b)).comp (inl2 Face)) := by
    rw [← continuousOn_univ]
    refine hM.continuousOn.comp (continuous_const.prodMk continuous_fst |>.prodMk
      continuous_snd).continuousOn fun p _ => ⟨⟨hx, trivial⟩, trivial⟩
  have hcomm := iterIntegral_clm_comm
    (alternatizeUncurryFinCLM ℝ Face (Coef n))
    (fun a b => (fderiv ℝ (avIntegrand n c F) ((x, a), b)).comp (inl2 Face)) hcont
  have e : ∀ a b : ℝ, alternatizeUncurryFinCLM ℝ Face (Coef n)
      ((fderiv ℝ (avIntegrand n c F) ((x, a), b)).comp (inl2 Face)) = 0 := by
    intro a b
    have hdiff : DifferentiableAt ℝ (avIntegrand n c F) ((x, a), b) :=
      ((hf _ ⟨⟨hx, trivial⟩, trivial⟩).contDiffAt
        (hDset.mem_nhds ⟨⟨hx, trivial⟩, trivial⟩)).differentiableAt (by simp)
    have hpath : HasFDerivAt (fun y : Face => ((y, a), b)) (inl2 Face) x := by
      refine (((hasFDerivAt_id x).prodMk (hasFDerivAt_const a x)).prodMk
        (hasFDerivAt_const b x)).congr_fderiv ?_
      ext v <;> simp [inl2]
    have hch := hdiff.hasFDerivAt.comp x hpath
    have h3 : fderiv ℝ (fun y : Face => avIntegrand n c F ((y, a), b)) x =
        (fderiv ℝ (avIntegrand n c F) ((x, a), b)).comp (inl2 Face) := hch.fderiv
    have := extDeriv_avIntegrand n c F hF hx a b
    unfold extDeriv at this
    rw [h3] at this
    exact this
  change (alternatizeUncurryFinCLM ℝ Face (Coef n))
    (∫ (a : ℝ) (b : ℝ) in 0..1, fderiv ℝ (avIntegrand n c F) ((x, a), b) ∘SL inl2 Face) = 0
  rw [hcomm]
  simp only [e]
  simp

/-! ### Equivariance -/

/-- Precomposition of alternating 2-forms with a continuous linear map, as a continuous linear map. -/
def compCLM (M : Face →L[ℝ] Face) :
    (Face [⋀^Fin 2]→L[ℝ] Coef n) →L[ℝ] (Face [⋀^Fin 2]→L[ℝ] Coef n) :=
  LinearMap.mkContinuous
    { toFun := fun B => B.compContinuousLinearMap M
      map_add' := fun B B' => by ext; simp
      map_smul' := fun r B => by ext; simp }
    (‖M‖ ^ 2) (fun B => by
      have := B.norm_compContinuousLinearMap_le M
      simp only [Fintype.card_fin] at this
      calc _ ≤ _ := this
        _ = _ := by ring)

theorem compCLM_apply (M : Face →L[ℝ] Face) (B : Face [⋀^Fin 2]→L[ℝ] Coef n) :
    compCLM n M B = B.compContinuousLinearMap M := rfl

theorem avIntegrand_continuous (c : ℝ) (F : Form (F := Coef n) faceSet 2) {x : Face}
    (hx : x ∈ faceSet) :
    Continuous (fun t : Fin 2 → ℝ => avIntegrand n c F ((x, t 0), t 1)) := by
  have h := (contDiffOn_avIntegrand n c F).continuousOn
  rw [← continuousOn_univ]
  have hc : Continuous (fun t : Fin 2 → ℝ => (((x, t 0), t 1) : (Face × ℝ) × ℝ)) := by fun_prop
  exact h.comp hc.continuousOn fun t _ => ⟨⟨hx, trivial⟩, trivial⟩

section Equivariance

variable {G : Type} [Group G] (D : PlaneData G) (c : ℝ)

/-- The integrality hypotheses on the plane parabolic group: Levi blocks are `SL₂(ℤ)` matrices and
the radical lattice `c ℤ²` is realized by elements of the group. -/
structure LatticeData : Prop where
  levi : ∀ g : G, ∃ A : SL(2, ℤ), (D.lam g⁻¹ : Matrix (Fin 2) (Fin 2) ℝ) =
    (A : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ)
  lattice : ∀ k : Fin 2 → ℤ, ∃ ν : G, (D.lam ν : Matrix (Fin 2) (Fin 2) ℝ) = 1 ∧
    D.w ν = c • intVec k

variable {D c}

theorem avIntegrand_periodic (hL : LatticeData D c) (F : Form (F := Coef n) faceSet 2)
    (hF : ∀ g, ZigZag.pullForm isOpen_faceSet D.action g 2 F =
      ZigZag.twForm (ZigZag.repCLM (D.rhoR n) g) 2 F) (x : Face) :
    PerZ2 (fun t : Fin 2 → ℝ => avIntegrand n c F ((x, t 0), t 1)) := by
  intro t k
  obtain ⟨ν, hν1, hν2⟩ := hL.lattice k
  have := shiftForm_add_lattice D n ν hν1 (c • intVec k) (c • t) hν2 F (hF ν)
  have e : (c • ![(t + intVec k) 0, (t + intVec k) 1] : Fin 2 → ℝ) = c • intVec k + c • t := by
    funext i; fin_cases i <;> simp [intVec] <;> ring
  have e2 : (c • ![t 0, t 1] : Fin 2 → ℝ) = c • t := by
    funext i; fin_cases i <;> simp
  show ((shiftForm n (c • ![(t + intVec k) 0, (t + intVec k) 1]) F : Form (F := Coef n) faceSet 2) :
      RawForm Face (Coef n) 2) x = ((shiftForm n (c • ![t 0, t 1]) F : Form (F := Coef n)
        faceSet 2) : RawForm Face (Coef n) 2) x
  rw [e, e2, this]

/-- **The average is `Γ_P`-equivariant**: `g^*(Av F) = ρ(g) Av F`. -/
theorem pullForm_avForm (hL : LatticeData D c) (F : Form (F := Coef n) faceSet 2)
    (hF : ∀ g, ZigZag.pullForm isOpen_faceSet D.action g 2 F =
      ZigZag.twForm (ZigZag.repCLM (D.rhoR n) g) 2 F) (g : G) :
    ZigZag.pullForm isOpen_faceSet D.action g 2 (avForm n c F) =
      ZigZag.twForm (ZigZag.repCLM (D.rhoR n) g) 2 (avForm n c F) := by
  apply Form.ext
  intro x hx
  have hgx : D.act g x ∈ faceSet := D.act_mapsTo g hx
  rw [ZigZag.pullForm_apply isOpen_faceSet D.action g _ hx, ZigZag.twForm_apply,
    avForm_apply n c F hx]
  unfold pullRaw
  rw [show (D.action.act g) = D.act g from rfl, avForm_apply n c F hgx]
  obtain ⟨A, hA⟩ := hL.levi g
  let L := coefficientFormMap (ZigZag.repCLM (D.rhoR n) g) 2 (E := Face) (F := Coef n)
  let Ψ : (Fin 2 → ℝ) → Face [⋀^Fin 2]→L[ℝ] Coef n :=
    fun t => avIntegrand n c F ((x, t 0), t 1)
  have hΨc : Continuous Ψ := avIntegrand_continuous n c F hx
  have hΨp : PerZ2 Ψ := avIntegrand_periodic n hL F hF x
  have hcont1 : Continuous (Function.uncurry fun a b : ℝ =>
      avIntegrand n c F ((D.act g x, a), b)) := by
    have := avIntegrand_continuous n c F hgx
    have h2 := this.comp (show Continuous fun p : ℝ × ℝ => (![p.1, p.2] : Fin 2 → ℝ) by fun_prop)
    exact h2
  have hcont2 : Continuous (Function.uncurry fun a b : ℝ => Ψ ![a, b]) := by
    refine hΨc.comp ?_
    fun_prop
  have key : ∀ t : Fin 2 → ℝ,
      compCLM n (fderiv ℝ (D.act g) x) (avIntegrand n c F ((D.act g x, t 0), t 1)) =
        L (Ψ (zAct (A : Matrix (Fin 2) (Fin 2) ℤ) t)) := by
    intro t
    have ht : (![t 0, t 1] : Fin 2 → ℝ) = t := by funext i; fin_cases i <;> rfl
    have hvec : (D.lam g⁻¹ : Matrix (Fin 2) (Fin 2) ℝ).mulVec (c • ![t 0, t 1]) =
        c • ![(zAct (A : Matrix (Fin 2) (Fin 2) ℤ) t) 0, (zAct (A : Matrix (Fin 2) (Fin 2) ℤ) t) 1] := by
      have : (![(zAct (A : Matrix (Fin 2) (Fin 2) ℤ) t) 0,
          (zAct (A : Matrix (Fin 2) (Fin 2) ℤ) t) 1] : Fin 2 → ℝ) =
          zAct (A : Matrix (Fin 2) (Fin 2) ℤ) t := by funext i; fin_cases i <;> rfl
      rw [this, ht, hA, Matrix.mulVec_smul]
      rfl
    have h1 := pullForm_shiftForm D n g (c • ![t 0, t 1]) F (hF g)
    have h2 := congrFun (congrArg (fun w : Form (F := Coef n) faceSet 2 =>
      (w : RawForm Face (Coef n) 2)) h1) x
    rw [ZigZag.pullForm_apply isOpen_faceSet D.action g _ hx, ZigZag.twForm_apply, hvec] at h2
    exact h2
  have hL1 := iterIntegral_clm_comm (compCLM n (fderiv ℝ (D.act g) x))
    (fun a b => avIntegrand n c F ((D.act g x, a), b)) hcont1
  have hL2 := iterIntegral_clm_comm L (fun a b => Ψ ![a, b]) hcont2
  have hS := sqInt_zAct A (f := fun t => L (Ψ t)) (L.continuous.comp hΨc)
    (fun t k => by simp only [hΨp t k])
  have hlhs : (∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1,
      compCLM n (fderiv ℝ (D.act g) x) (avIntegrand n c F ((D.act g x, a), b))) =
        ∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1, L (Ψ (zAct (A : Matrix (Fin 2) (Fin 2) ℤ) ![a, b])) := by
    refine intervalIntegral.integral_congr fun a _ => ?_
    refine intervalIntegral.integral_congr fun b _ => ?_
    simpa using key ![a, b]
  show compCLM n (fderiv ℝ (D.act g) x) (avRaw n c F (D.act g x)) = L (avRaw n c F x)
  unfold avRaw
  rw [hL1, hlhs]
  exact hS.trans (hL2.symm)

end Equivariance

end TernaryPeriodPolynomials.Argument.EisensteinClass
