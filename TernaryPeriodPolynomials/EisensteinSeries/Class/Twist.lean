module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Avx
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Shift
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Average

@[expose] public section


/-!
# Levi twists, intertwiners, and the commutation of the average with `g^*` and `ρ(g)`

* `pullForm_comm_trPullK`, `pullTr_apply`, `eqvS_iff_pull`: degree-free versions of the commutation
  `g^* τ_v^* = τ_{λ_g⁻¹ v}^* g^*`, and lattice equivariance as an identity of chart forms.
* `eqvS_pullForm`, `eqvS_twForm_rho`, `eqvS_twForm_of_intertwine`, `eqvS_of_invariant`: `g^*` and `ρ(g)`
  carry `σ`-lattice-equivariant forms to forms equivariant for the Levi-twisted representation
  `sgm D n g v = ρ(t_{λ_g v})`; an invariant form is equivariant for `trL n`.
* `avFormS_twForm` (**C2**) and `avFormS_pullForm` (**C1**): the average commutes with intertwiners of
  the coefficient representations and with `g^*` for an `SL₂(ℤ)` Levi block (the unit-square integral
  of a periodic function is `SL₂(ℤ)`-invariant, `sqInt_zAct`).

Formalized by Claude Sonnet 5.5.
-/

open ContinuousAlternatingMap Set MeasureTheory
open scoped ContDiff MatrixGroups
noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.SeedC3.Psi TernaryPoly.SmoothLocalDeRham
  TernaryPoly.SmoothCoveringDeRham

variable {G : Type} [Group G] (D : PlaneData G) {n k : ℕ}

theorem pullBack_act_eqK (g : G) (w : Form (F := Coef n) faceSet k) :
    pullBack isOpen_faceSet (D.act_contDiffOn g) (D.act_mapsTo g) k w =
      ZigZag.pullForm isOpen_faceSet D.action g k w := by
  apply Form.ext
  intro x hx
  rw [pullBack_apply isOpen_faceSet _ _ _ hx, ZigZag.pullForm_apply isOpen_faceSet D.action g _ hx]
  rfl

/-- `g^* τ_v^* = τ_{λ_g⁻¹ v}^* g^*` in every degree. -/
theorem pullForm_comm_trPullK (g : G) (v : Fin 2 → ℝ) (w : Form (F := Coef n) faceSet k) :
    ZigZag.pullForm isOpen_faceSet D.action g k
        (ZigZag.pullForm isOpen_faceSet trPD.action (Multiplicative.ofAdd v) k w) =
      ZigZag.pullForm isOpen_faceSet trPD.action
        (Multiplicative.ofAdd ((D.lam g⁻¹ : Matrix (Fin 2) (Fin 2) ℝ).mulVec v)) k
        (ZigZag.pullForm isOpen_faceSet D.action g k w) := by
  have h := pullBack_pullForm isOpen_faceSet isOpen_faceSet trPD.action trPD.action (lamHom D g)
    (lamEquiv D g).smooth (lamEquiv D g).mapsTo (lamEquiv D g).equiv
    (Multiplicative.ofAdd ((D.lam g⁻¹ : Matrix (Fin 2) (Fin 2) ℝ).mulVec v)) w
  rw [lamHom_apply, lam_mulVec_inv] at h
  have e : pullBack (F := Coef n) isOpen_faceSet (lamEquiv D g).smooth (lamEquiv D g).mapsTo k =
      pullBack (F := Coef n) isOpen_faceSet (D.act_contDiffOn g) (D.act_mapsTo g) k := rfl
  rw [e] at h
  simpa only [pullBack_act_eqK] using h

/-- Pullback by a translation is evaluation at the translated point. -/
theorem pullTr_apply (v : Fin 2 → ℝ) (W : Form (F := Coef n) faceSet k) {x : Face}
    (hx : x ∈ faceSet) :
    ((ZigZag.pullForm isOpen_faceSet trPD.action (Multiplicative.ofAdd v) k W :
      Form (F := Coef n) faceSet k) : RawForm Face (Coef n) k) x =
      (W : RawForm Face (Coef n) k) (x + shVec v) := by
  rw [ZigZag.pullForm_apply isOpen_faceSet trPD.action _ _ hx]
  have hact : trPD.action.act (Multiplicative.ofAdd v) = fun y : Face => y + shVec v := by
    funext y; exact trPD_act (Multiplicative.ofAdd v) y
  simp only [pullRaw, hact, (hasFDerivAt_add_const_face (shVec v) x).fderiv]
  ext w
  simp

variable {σ : (Fin 2 → ℝ) → (Coef n →L[ℝ] Coef n)} {c : ℝ}

/-- Lattice equivariance as an identity of chart forms. -/
theorem eqvS_iff_pull {W : Form (F := Coef n) faceSet k} :
    EqvS σ c W ↔ ∀ m : Fin 2 → ℤ,
      ZigZag.pullForm isOpen_faceSet trPD.action (Multiplicative.ofAdd (c • intVec m)) k W =
        ZigZag.twForm (σ (c • intVec m)) k W := by
  constructor
  · intro h m
    apply Form.ext
    intro x hx
    rw [pullTr_apply _ _ hx, ZigZag.twForm_apply, coefficientFormMap_apply]
    exact h m x hx
  · intro h m x hx
    have := congrFun (congrArg (fun w : Form (F := Coef n) faceSet k =>
      (w : RawForm Face (Coef n) k)) (h m)) x
    rw [pullTr_apply _ _ hx, ZigZag.twForm_apply, coefficientFormMap_apply] at this
    exact this

theorem lam_mulVec_intVec {g : G} (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hA : (D.lam g : Matrix (Fin 2) (Fin 2) ℝ) = A.map (Int.castRingHom ℝ)) (m : Fin 2 → ℤ) :
    (D.lam g : Matrix (Fin 2) (Fin 2) ℝ).mulVec (c • intVec m) = c • intVec (A.mulVec m) := by
  rw [Matrix.mulVec_smul, hA]
  exact congrArg (c • ·) (zAct_intVec A m)

/-- **`g^*` preserves lattice equivariance, with the Levi-twisted representation.** -/
theorem eqvS_pullForm (g : G) (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hA : (D.lam g : Matrix (Fin 2) (Fin 2) ℝ) = A.map (Int.castRingHom ℝ))
    {W : Form (F := Coef n) faceSet k} (hE : EqvS σ c W) :
    EqvS (fun v => σ ((D.lam g : Matrix (Fin 2) (Fin 2) ℝ).mulVec v)) c
      (ZigZag.pullForm isOpen_faceSet D.action g k W) := by
  rw [eqvS_iff_pull] at hE ⊢
  intro m
  have h1 := pullForm_comm_trPullK D g ((D.lam g : Matrix (Fin 2) (Fin 2) ℝ).mulVec (c • intVec m))
    W
  rw [lam_mulVec_inv', lam_mulVec_intVec D A hA, hE (A.mulVec m),
    ZigZag.pullForm_twForm isOpen_faceSet D.action] at h1
  rw [← h1, lam_mulVec_intVec D A hA]

/-- The intertwining relation `σ(λ_g u) ρ(g) = ρ(g) σ(u)` for the translation representation. -/
theorem trL_intertwine (g : G) (u : Fin 2 → ℝ) :
    (trL n ((D.lam g : Matrix (Fin 2) (Fin 2) ℝ).mulVec u)).comp
        (ZigZag.repCLM (D.rhoR n) g) =
      (ZigZag.repCLM (D.rhoR n) g).comp (trL n u) := by
  have h := trL_comp_rho D n g (-((D.lam g : Matrix (Fin 2) (Fin 2) ℝ).mulVec u))
  rw [Matrix.mulVec_neg, lam_mulVec_inv', neg_neg, neg_neg] at h
  exact h

/-- **`ρ(g)` preserves lattice equivariance, with the Levi-twisted representation.** -/
theorem eqvS_twForm_rho (g : G) {W : Form (F := Coef n) faceSet k} (hE : EqvS (trL n) c W) :
    EqvS (fun v => trL n ((D.lam g : Matrix (Fin 2) (Fin 2) ℝ).mulVec v)) c
      (ZigZag.twForm (ZigZag.repCLM (D.rhoR n) g) k W) := by
  rw [eqvS_iff_pull] at hE ⊢
  intro m
  rw [ZigZag.pullForm_twForm isOpen_faceSet trPD.action, hE m, ← ZigZag.twForm_mul,
    ← ZigZag.twForm_mul, ← trL_intertwine D g]

/-! ### Commutation of the average with `ρ(g)` and `g^*` -/

theorem shiftS_twForm {σ' : (Fin 2 → ℝ) → (Coef n →L[ℝ] Coef n)} (T : Coef n →L[ℝ] Coef n)
    (hint : ∀ u, (σ' u).comp T = T.comp (σ u)) (v : Fin 2 → ℝ) (W : Form (F := Coef n) faceSet k) :
    shiftS k σ' v (ZigZag.twForm T k W) = ZigZag.twForm T k (shiftS k σ v W) := by
  unfold shiftS
  simp only [LinearMap.comp_apply]
  rw [ZigZag.pullForm_twForm isOpen_faceSet trPD.action, ← ZigZag.twForm_mul,
    ← ZigZag.twForm_mul, hint]

/-- **C2.** The average commutes with an intertwiner of the coefficient representations. -/
theorem avFormS_twForm {σ' : (Fin 2 → ℝ) → (Coef n →L[ℝ] Coef n)} (hσ : ContDiff ℝ ∞ σ)
    (hσ' : ContDiff ℝ ∞ σ') (T : Coef n →L[ℝ] Coef n)
    (hint : ∀ u, (σ' u).comp T = T.comp (σ u)) (W : Form (F := Coef n) faceSet k) :
    avFormS hσ' c (ZigZag.twForm T k W) = ZigZag.twForm T k (avFormS hσ c W) := by
  apply Form.ext
  intro x hx
  rw [avFormS_apply hσ' c _ hx, ZigZag.twForm_apply, avFormS_apply hσ c _ hx,
    coefficientFormMap_apply]
  have hcont := continuous_avIntegrandS_uncurry hσ c W hx
  have hL := iterIntegral_clm_comm (compAltCLM T k) (fun a b => avIntegrandS k σ c W ((x, a), b))
    hcont
  unfold avRawS
  change _ = compAltCLM T k _
  rw [hL]
  refine intervalIntegral.integral_congr fun a _ => ?_
  refine intervalIntegral.integral_congr fun b _ => ?_
  show ((shiftS k σ' (c • ![a, b]) (ZigZag.twForm T k W) : Form (F := Coef n) faceSet k) :
    RawForm Face (Coef n) k) x = compAltCLM T k (((shiftS k σ (c • ![a, b]) W :
      Form (F := Coef n) faceSet k) : RawForm Face (Coef n) k) x)
  rw [shiftS_twForm T hint, ZigZag.twForm_apply, coefficientFormMap_apply]
  rfl

/-- `g^*` followed by the translation transport. -/
theorem shiftS_pullForm {σ' : (Fin 2 → ℝ) → (Coef n →L[ℝ] Coef n)} (g : G)
    (hσ' : ∀ v, σ' v = σ ((D.lam g : Matrix (Fin 2) (Fin 2) ℝ).mulVec v)) (v : Fin 2 → ℝ)
    (W : Form (F := Coef n) faceSet k) :
    shiftS k σ' v (ZigZag.pullForm isOpen_faceSet D.action g k W) =
      ZigZag.pullForm isOpen_faceSet D.action g k
        (shiftS k σ ((D.lam g : Matrix (Fin 2) (Fin 2) ℝ).mulVec v) W) := by
  unfold shiftS
  simp only [LinearMap.comp_apply]
  rw [ZigZag.pullForm_twForm isOpen_faceSet D.action, pullForm_comm_trPullK D g, lam_mulVec_inv',
    hσ', Matrix.mulVec_neg]

/-- Precomposition of alternating `k`-forms with a continuous linear map of the face. -/
def pullCLM (n k : ℕ) (M : Face →L[ℝ] Face) :
    (Face [⋀^Fin k]→L[ℝ] Coef n) →L[ℝ] (Face [⋀^Fin k]→L[ℝ] Coef n) :=
  LinearMap.mkContinuous
    { toFun := fun B => B.compContinuousLinearMap M
      map_add' := fun B B' => by ext; simp
      map_smul' := fun r B => by ext; simp }
    (‖M‖ ^ k) (fun B => by
      have := B.norm_compContinuousLinearMap_le M
      simp only [Fintype.card_fin] at this
      calc _ ≤ _ := this
        _ = _ := by ring)

theorem pullCLM_apply (M : Face →L[ℝ] Face) (B : Face [⋀^Fin k]→L[ℝ] Coef n) :
    pullCLM n k M B = B.compContinuousLinearMap M := rfl

theorem avIntegrandS_continuous (hσ : ContDiff ℝ ∞ σ) (c : ℝ) (W : Form (F := Coef n) faceSet k)
    {x : Face} (hx : x ∈ faceSet) :
    Continuous (fun t : Fin 2 → ℝ => avIntegrandS k σ c W ((x, t 0), t 1)) := by
  have h := (contDiffOn_avIntegrandS hσ c W).continuousOn
  rw [← continuousOn_univ]
  have hc : Continuous (fun t : Fin 2 → ℝ => (((x, t 0), t 1) : (Face × ℝ) × ℝ)) := by fun_prop
  exact h.comp hc.continuousOn fun t _ => ⟨⟨hx, trivial⟩, trivial⟩

/-- **C1.** The average commutes with `g^*` when the Levi block `λ_g` is an `SL₂(ℤ)` matrix. -/
theorem avFormS_pullForm (h : UniRep σ) (g : G) (A : SL(2, ℤ))
    (hA : (D.lam g : Matrix (Fin 2) (Fin 2) ℝ) =
      (A : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ))
    {σ' : (Fin 2 → ℝ) → (Coef n →L[ℝ] Coef n)}
    (hσ' : ∀ v, σ' v = σ ((D.lam g : Matrix (Fin 2) (Fin 2) ℝ).mulVec v))
    (hσ'sm : ContDiff ℝ ∞ σ') {W : Form (F := Coef n) faceSet k} (hE : EqvS σ c W) :
    avFormS hσ'sm c (ZigZag.pullForm isOpen_faceSet D.action g k W) =
      ZigZag.pullForm isOpen_faceSet D.action g k (avFormS h.smooth c W) := by
  apply Form.ext
  intro x hx
  have hgx : D.act g x ∈ faceSet := D.act_mapsTo g hx
  rw [avFormS_apply hσ'sm c _ hx, ZigZag.pullForm_apply isOpen_faceSet D.action g _ hx]
  unfold pullRaw
  rw [show (D.action.act g) = D.act g from rfl, avFormS_apply h.smooth c _ hgx]
  let Φ : (Fin 2 → ℝ) → Face [⋀^Fin k]→L[ℝ] Coef n :=
    fun t => avIntegrandS k σ c W ((D.act g x, t 0), t 1)
  have hΦc : Continuous Φ := avIntegrandS_continuous h.smooth c W hgx
  have hΦp : PerZ2 Φ := avIntegrandS_periodic h hE (D.act g x)
  have hcont1 : Continuous (Function.uncurry fun a b : ℝ =>
      avIntegrandS k σ c W ((D.act g x, a), b)) := by
    have h2 := hΦc.comp (show Continuous fun p : ℝ × ℝ => (![p.1, p.2] : Fin 2 → ℝ) by fun_prop)
    exact h2
  have key : ∀ t : Fin 2 → ℝ,
      avIntegrandS k σ' c (ZigZag.pullForm isOpen_faceSet D.action g k W) ((x, t 0), t 1) =
        pullCLM n k (fderiv ℝ (D.act g) x) (Φ (zAct (A : Matrix (Fin 2) (Fin 2) ℤ) t)) := by
    intro t
    have ht : (![t 0, t 1] : Fin 2 → ℝ) = t := by funext i; fin_cases i <;> rfl
    have hvec : (D.lam g : Matrix (Fin 2) (Fin 2) ℝ).mulVec (c • ![t 0, t 1]) =
        c • ![(zAct (A : Matrix (Fin 2) (Fin 2) ℤ) t) 0,
          (zAct (A : Matrix (Fin 2) (Fin 2) ℤ) t) 1] := by
      have : (![(zAct (A : Matrix (Fin 2) (Fin 2) ℤ) t) 0,
          (zAct (A : Matrix (Fin 2) (Fin 2) ℤ) t) 1] : Fin 2 → ℝ) =
          zAct (A : Matrix (Fin 2) (Fin 2) ℤ) t := by funext i; fin_cases i <;> rfl
      rw [this, ht, hA, Matrix.mulVec_smul]
      rfl
    have h1 := shiftS_pullForm D (σ := σ) g hσ' (c • ![t 0, t 1]) W
    have h2 := congrFun (congrArg (fun w : Form (F := Coef n) faceSet k =>
      (w : RawForm Face (Coef n) k)) h1) x
    rw [ZigZag.pullForm_apply isOpen_faceSet D.action g _ hx, hvec] at h2
    exact h2
  have hL1 := iterIntegral_clm_comm (pullCLM n k (fderiv ℝ (D.act g) x))
    (fun a b => avIntegrandS k σ c W ((D.act g x, a), b)) hcont1
  have hS := sqInt_zAct A (f := fun t => pullCLM n k (fderiv ℝ (D.act g) x) (Φ t))
    ((pullCLM n k (fderiv ℝ (D.act g) x)).continuous.comp hΦc)
    (fun t m => by simp only [hΦp t m])
  have hlhs : (avRawS (k := k) σ' c (ZigZag.pullForm isOpen_faceSet D.action g k W) x) =
      ∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1,
        pullCLM n k (fderiv ℝ (D.act g) x) (Φ (zAct (A : Matrix (Fin 2) (Fin 2) ℤ) ![a, b])) := by
    unfold avRawS
    refine intervalIntegral.integral_congr fun a _ => ?_
    refine intervalIntegral.integral_congr fun b _ => ?_
    simpa using key ![a, b]
  show _ = pullCLM n k (fderiv ℝ (D.act g) x) (avRawS (k := k) σ c W (D.act g x))
  rw [hlhs]
  unfold avRawS
  rw [hL1]
  exact hS

/-- The Levi-twisted translation representation `v ↦ ρ(t_{λ_g v})`. -/
def sgm (D : PlaneData G) (n : ℕ) (g : G) : (Fin 2 → ℝ) → (Coef n →L[ℝ] Coef n) :=
  fun v => trL n ((D.lam g : Matrix (Fin 2) (Fin 2) ℝ).mulVec v)

theorem uniRep_sgm (g : G) : UniRep (sgm D n g) :=
  (uniRep_trL n).comp_mulVec _

theorem sgm_mul (g h : G) (v : Fin 2 → ℝ) :
    sgm D n (g * h) v = sgm D n g ((D.lam h : Matrix (Fin 2) (Fin 2) ℝ).mulVec v) := by
  unfold sgm
  rw [map_mul, Units.val_mul, Matrix.mulVec_mulVec]

theorem sgm_funext_mul (g h : G) :
    sgm D n (g * h) = fun v => sgm D n g ((D.lam h : Matrix (Fin 2) (Fin 2) ℝ).mulVec v) :=
  funext (sgm_mul D g h)

theorem sgm_one : sgm D n 1 = trL n := by
  funext v
  simp [sgm]

/-- Intertwiner version of `eqvS_twForm_rho`. -/
theorem eqvS_twForm_of_intertwine {σ₁ σ₂ : (Fin 2 → ℝ) → (Coef n →L[ℝ] Coef n)}
    {W : Form (F := Coef n) faceSet k} (hE : EqvS σ₁ c W) (T : Coef n →L[ℝ] Coef n)
    (hint : ∀ u, (σ₂ u).comp T = T.comp (σ₁ u)) : EqvS σ₂ c (ZigZag.twForm T k W) := by
  rw [eqvS_iff_pull] at hE ⊢
  intro m
  rw [ZigZag.pullForm_twForm isOpen_faceSet trPD.action, hE m, ← ZigZag.twForm_mul,
    ← ZigZag.twForm_mul, hint]

theorem rho_intertwine_sgm (g h : G) (u : Fin 2 → ℝ) :
    (sgm D n (g * h) u).comp (ZigZag.repCLM (D.rhoR n) g) =
      (ZigZag.repCLM (D.rhoR n) g).comp (sgm D n h u) := by
  rw [sgm_mul]
  exact trL_intertwine D g _

theorem pullForm_congr_actK {G' : Type} [Group G'] (A : ZigZag.Action G faceSet)
    (B : ZigZag.Action G' faceSet) (g : G) (g' : G') (h : ∀ x ∈ faceSet, A.act g x = B.act g' x)
    (w : Form (F := Coef n) faceSet k) :
    ZigZag.pullForm isOpen_faceSet A g k w = ZigZag.pullForm isOpen_faceSet B g' k w := by
  apply Form.ext
  intro x hx
  rw [ZigZag.pullForm_apply isOpen_faceSet A g _ hx, ZigZag.pullForm_apply isOpen_faceSet B g' _ hx]
  have : A.act g =ᶠ[nhds x] B.act g' := by
    filter_upwards [isOpen_faceSet.mem_nhds hx] with y hy using h y hy
  exact pullRaw_eventuallyEq _ this

/-- A lattice element of `Γ_P` acts on invariant forms as a translation with coefficient `ρ(t_u)`. -/
theorem pull_lattice (ν : G) (hν : (D.lam ν : Matrix (Fin 2) (Fin 2) ℝ) = 1) (u : Fin 2 → ℝ)
    (hu : D.w ν = u) (F : Form (F := Coef n) faceSet k)
    (hF : ZigZag.pullForm isOpen_faceSet D.action ν k F =
      ZigZag.twForm (ZigZag.repCLM (D.rhoR n) ν) k F) :
    ZigZag.pullForm isOpen_faceSet trPD.action (Multiplicative.ofAdd u) k F =
      ZigZag.twForm (trL n u) k F := by
  have hact : ∀ x ∈ faceSet, D.action.act ν x = trPD.action.act (Multiplicative.ofAdd u) x := by
    intro x hx
    change D.act ν x = trPD.act (Multiplicative.ofAdd u) x
    rw [trPD_act]
    funext i
    fin_cases i
    · simp [PlaneData.act, hν, hu, faceTau]
    · simp [PlaneData.act, hν, hu, faceTau]
    · simp [PlaneData.act, hν, faceTau, mob]
    · simp [PlaneData.act, hν, faceTau, mob]
  have hrho : ZigZag.repCLM (D.rhoR n) ν = trL n u := by
    ext q
    apply Coef.toPoly_injective
    change Coef.toPoly (D.rhoCoef n ν q) = _
    rw [D.toPoly_rhoCoef, toPoly_trL]
    unfold PlaneData.plm
    rw [hν, hu]
    congr 1
  rw [← pullForm_congr_actK D.action trPD.action ν (Multiplicative.ofAdd u) hact, hF, hrho]

/-- **An invariant form is lattice equivariant** for the translation representation. -/
theorem eqvS_of_invariant (hL : LatticeData D c) {F : Form (F := Coef n) faceSet k}
    (hF : ∀ g, ZigZag.pullForm isOpen_faceSet D.action g k F =
      ZigZag.twForm (ZigZag.repCLM (D.rhoR n) g) k F) : EqvS (trL n) c F := by
  rw [eqvS_iff_pull]
  intro m
  obtain ⟨ν, hν1, hν2⟩ := hL.lattice m
  exact pull_lattice D ν hν1 _ hν2 F (hF ν)

end TernaryPeriodPolynomials.Argument.EisensteinClass
