module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.KThm
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Double2

@[expose] public section


/-!
# Algebra of the torus average: linearity, translation invariance, idempotence

For a unipotent representation `σ` of `ℝ²` and a lattice-equivariant form `W` (`EqvS σ c W`):
`avFormS` is additive and homogeneous (`avFormS_add`, `avFormS_smul`, `avLin`), commutes with `d`
(`d_avFormS_comm`), `Av W` is invariant under all transports (`shiftS_avFormS`), hence equivariant
(`eqvS_avFormS`) and fixed by `Av` (`avFormS_idem`); the normalization `W - Av W` has average zero
(`avFormS_sub_avFormS`). The unit-square integral of a periodic function is translation invariant
(`sqInt_translate`).

Formalized by Claude Sonnet 5.5.
-/

open ContinuousAlternatingMap Set MeasureTheory
open scoped ContDiff MatrixGroups
noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.SeedC3.Psi TernaryPoly.SmoothLocalDeRham
  TernaryPoly.SmoothCoveringDeRham

variable {n k : ℕ} {σ : (Fin 2 → ℝ) → (Coef n →L[ℝ] Coef n)}

theorem d_shiftS_comm (v : Fin 2 → ℝ) (W : Form (F := Coef n) faceSet k) :
    d isOpen_faceSet k (shiftS k σ v W) = shiftS (k + 1) σ v (d isOpen_faceSet k W) := by
  unfold shiftS
  simp only [LinearMap.comp_apply]
  rw [ZigZag.d_twForm isOpen_faceSet, ZigZag.d_pullForm isOpen_faceSet trPD.action]

theorem d_avFormS_comm (hσ : ContDiff ℝ ∞ σ) (c : ℝ) (W : Form (F := Coef n) faceSet k) :
    d isOpen_faceSet k (avFormS hσ c W) = avFormS hσ c (d isOpen_faceSet k W) := by
  apply Form.ext
  intro x hx
  rw [d_apply isOpen_faceSet _ hx, avFormS_apply hσ c _ hx]
  have heq : (avFormS hσ c W : RawForm Face (Coef n) k) =ᶠ[nhds x] avRawS (k := k) σ c W := by
    filter_upwards [isOpen_faceSet.mem_nhds hx] with y hy using avFormS_apply hσ c W hy
  rw [heq.extDeriv_eq (𝕜 := ℝ)]
  unfold avRawS
  rw [extDeriv_iteratedIntegral isOpen_faceSet _ (contDiffOn_avIntegrandS hσ c W) hx]
  refine intervalIntegral.integral_congr fun a _ => ?_
  refine intervalIntegral.integral_congr fun b _ => ?_
  have h1 := d_apply isOpen_faceSet (shiftS k σ (c • ![a, b]) W) hx
  rw [d_shiftS_comm] at h1
  exact h1.symm

theorem avIntegrandS_add (c : ℝ) (W W' : Form (F := Coef n) faceSet k) (p : (Face × ℝ) × ℝ) :
    avIntegrandS k σ c (W + W') p = avIntegrandS k σ c W p + avIntegrandS k σ c W' p := by
  simp [avIntegrandS, map_add]

theorem avIntegrandS_smul (c r : ℝ) (W : Form (F := Coef n) faceSet k) (p : (Face × ℝ) × ℝ) :
    avIntegrandS k σ c (r • W) p = r • avIntegrandS k σ c W p := by
  simp [avIntegrandS, map_smul]

theorem avRawS_add (hσ : ContDiff ℝ ∞ σ) (c : ℝ) (W W' : Form (F := Coef n) faceSet k) {x : Face}
    (hx : x ∈ faceSet) :
    avRawS (k := k) σ c (W + W') x = avRawS (k := k) σ c W x + avRawS (k := k) σ c W' x := by
  unfold avRawS
  simp only [avIntegrandS_add]
  exact iterIntegral_add (fun a b => avIntegrandS k σ c W ((x, a), b))
    (fun a b => avIntegrandS k σ c W' ((x, a), b)) (continuous_avIntegrandS_uncurry hσ c W hx)
    (continuous_avIntegrandS_uncurry hσ c W' hx)

theorem avRawS_smul (c r : ℝ) (W : Form (F := Coef n) faceSet k) (x : Face) :
    avRawS (k := k) σ c (r • W) x = r • avRawS (k := k) σ c W x := by
  unfold avRawS
  simp only [avIntegrandS_smul, intervalIntegral.integral_smul]

theorem avFormS_add (hσ : ContDiff ℝ ∞ σ) (c : ℝ) (W W' : Form (F := Coef n) faceSet k) :
    avFormS hσ c (W + W') = avFormS hσ c W + avFormS hσ c W' := by
  apply Form.ext
  intro x hx
  rw [avFormS_apply hσ c _ hx]
  change _ = ((avFormS hσ c W : Form (F := Coef n) faceSet k) : RawForm Face (Coef n) k) x +
    ((avFormS hσ c W' : Form (F := Coef n) faceSet k) : RawForm Face (Coef n) k) x
  rw [avFormS_apply hσ c _ hx, avFormS_apply hσ c _ hx]
  exact avRawS_add hσ c W W' hx

theorem avFormS_smul (hσ : ContDiff ℝ ∞ σ) (c r : ℝ) (W : Form (F := Coef n) faceSet k) :
    avFormS hσ c (r • W) = r • avFormS hσ c W := by
  apply Form.ext
  intro x hx
  rw [avFormS_apply hσ c _ hx]
  change _ = r • ((avFormS hσ c W : Form (F := Coef n) faceSet k) : RawForm Face (Coef n) k) x
  rw [avFormS_apply hσ c _ hx]
  exact avRawS_smul c r W x

/-- The torus average as a linear map on chart forms. -/
def avLin (hσ : ContDiff ℝ ∞ σ) (c : ℝ) :
    Form (F := Coef n) faceSet k →ₗ[ℝ] Form (F := Coef n) faceSet k where
  toFun := avFormS hσ c
  map_add' := avFormS_add hσ c
  map_smul' := avFormS_smul hσ c

/-! ### Translation invariance and idempotence of the average -/

theorem shVec_add (v w : Fin 2 → ℝ) : shVec (v + w) = shVec v + shVec w := by
  funext i; fin_cases i <;> simp [shVec]

theorem shVec_neg (v : Fin 2 → ℝ) : shVec (-v) = -shVec v := by
  funext i; fin_cases i <;> simp [shVec]

theorem shVec_zero : shVec (0 : Fin 2 → ℝ) = 0 := by
  funext i; fin_cases i <;> simp [shVec]

theorem compAlt_mul (A B : Coef n →L[ℝ] Coef n) (w : Face [⋀^Fin k]→L[ℝ] Coef n) :
    (A * B).compContinuousAlternatingMap w =
      A.compContinuousAlternatingMap (B.compContinuousAlternatingMap w) := by
  ext; simp

theorem shiftS_shiftS (h : UniRep σ) (v w : Fin 2 → ℝ) (W : Form (F := Coef n) faceSet k) :
    shiftS k σ v (shiftS k σ w W) = shiftS k σ (v + w) W := by
  apply Form.ext
  intro x hx
  rw [shiftS_apply k σ v _ hx, shiftS_apply k σ w _ (shVec_mem hx v), shiftS_apply k σ _ _ hx,
    ← compAlt_mul, shVec_add, ← add_assoc, neg_add, h.add]

theorem shiftS_add_lattice (h : UniRep σ) {c : ℝ}
    {W : Form (F := Coef n) faceSet k} (hE : EqvS σ c W) (m : Fin 2 → ℤ) (v : Fin 2 → ℝ) :
    shiftS k σ (c • intVec m + v) W = shiftS k σ v W := by
  apply Form.ext
  intro x hx
  rw [shiftS_apply k σ _ _ hx, shiftS_apply k σ _ _ hx, shVec_add]
  have e : x + (shVec (c • intVec m) + shVec v) = (x + shVec v) + shVec (c • intVec m) := by abel
  have key : σ (-(c • intVec m + v)) * σ (c • intVec m) = σ (-v) := by
    rw [← h.add]; congr 1; abel
  rw [e, hE m _ (shVec_mem hx v), ← compAlt_mul, key]

theorem avIntegrandS_periodic (h : UniRep σ) {c : ℝ} {W : Form (F := Coef n) faceSet k}
    (hE : EqvS σ c W) (x : Face) :
    PerZ2 (fun t : Fin 2 → ℝ => avIntegrandS k σ c W ((x, t 0), t 1)) := by
  intro t m
  have e : (c • ![(t + intVec m) 0, (t + intVec m) 1] : Fin 2 → ℝ) = c • intVec m + c • t := by
    funext i; fin_cases i <;> simp [intVec] <;> ring
  have e2 : (c • ![t 0, t 1] : Fin 2 → ℝ) = c • t := by
    funext i; fin_cases i <;> simp
  show ((shiftS k σ (c • ![(t + intVec m) 0, (t + intVec m) 1]) W : Form (F := Coef n) faceSet k) :
      RawForm Face (Coef n) k) x = ((shiftS k σ (c • ![t 0, t 1]) W : Form (F := Coef n)
        faceSet k) : RawForm Face (Coef n) k) x
  rw [e, e2, shiftS_add_lattice h hE]

/-- Shifting the unit-square integration window of a periodic function does not change it. -/
theorem integral_unit_translate {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] (F : ℝ → G)
    (hF : Function.Periodic F 1) (s : ℝ) :
    ∫ x in (0:ℝ)..1, F (x + s) = ∫ x in (0:ℝ)..1, F x := by
  rw [intervalIntegral.integral_comp_add_right F s]
  have := hF.intervalIntegral_add_eq s 0
  rw [zero_add] at this
  rw [zero_add, add_comm 1 s]
  exact this

theorem sqInt_translate {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {f : (Fin 2 → ℝ) → G}
    (hp : PerZ2 f) (s : Fin 2 → ℝ) : sqInt (fun v => f (v + s)) = sqInt f := by
  unfold sqInt
  have hv : ∀ a b : ℝ, (![a, b] : Fin 2 → ℝ) + s = ![a + s 0, b + s 1] := by
    intro a b; funext i; fin_cases i <;> simp
  simp only [hv]
  have hper2 : ∀ a : ℝ, Function.Periodic (fun b : ℝ => f ![a, b]) 1 := by
    intro a b
    have := hp ![a, b] (fun i => if i = 0 then 0 else 1)
    convert this using 2
    funext i; fin_cases i <;> simp [intVec]
  have h1 : ∀ a : ℝ, ∫ b in (0:ℝ)..1, f ![a + s 0, b + s 1] = ∫ b in (0:ℝ)..1, f ![a + s 0, b] :=
    fun a => integral_unit_translate (fun b => f ![a + s 0, b]) (hper2 _) (s 1)
  simp only [h1]
  set g : ℝ → G := fun a => ∫ b in (0:ℝ)..1, f ![a, b] with hg
  have hper : Function.Periodic g 1 := by
    intro a
    refine intervalIntegral.integral_congr fun b _ => ?_
    have := hp ![a, b] (fun i => if i = 0 then 1 else 0)
    convert this using 2
    funext i; fin_cases i <;> simp [intVec]
  exact integral_unit_translate g hper (s 0)

/-- **The average is translation invariant**: `σ(-v) τ_v^* (Av W) = Av W` for a lattice-equivariant `W`. -/
theorem shiftS_avFormS (h : UniRep σ) {c : ℝ} (hc : c ≠ 0) {W : Form (F := Coef n) faceSet k}
    (hE : EqvS σ c W) (v : Fin 2 → ℝ) :
    shiftS k σ v (avFormS h.smooth c W) = avFormS h.smooth c W := by
  apply Form.ext
  intro x hx
  rw [shiftS_apply k σ v _ hx, avFormS_apply h.smooth c _ (shVec_mem hx v),
    avFormS_apply h.smooth c _ hx]
  unfold avRawS
  have hcont1 : Continuous (Function.uncurry fun a b : ℝ =>
      avIntegrandS k σ c W ((x + shVec v, a), b)) := by
    have := continuous_avIntegrandS_uncurry h.smooth c W (shVec_mem hx v)
    exact this
  have hL := iterIntegral_clm_comm (compAltCLM (σ (-v)) k)
    (fun a b => avIntegrandS k σ c W ((x + shVec v, a), b)) hcont1
  show compAltCLM (σ (-v)) k _ = _
  rw [hL]
  set f : (Fin 2 → ℝ) → Face [⋀^Fin k]→L[ℝ] Coef n := fun t => avIntegrandS k σ c W ((x, t 0), t 1)
    with hf
  have key : ∀ a b : ℝ, compAltCLM (σ (-v)) k (avIntegrandS k σ c W ((x + shVec v, a), b)) =
      f (![a, b] + c⁻¹ • v) := by
    intro a b
    have e1 : (c • ![(![a, b] + c⁻¹ • v) 0, (![a, b] + c⁻¹ • v) 1] : Fin 2 → ℝ) =
        v + c • ![a, b] := by
      funext i; fin_cases i <;> simp <;> field_simp <;> ring
    have e2 := shiftS_shiftS (k := k) h v (c • ![a, b]) W
    have e3 := congrFun (congrArg (fun w : Form (F := Coef n) faceSet k =>
      (w : RawForm Face (Coef n) k)) e2) x
    rw [shiftS_apply k σ v _ hx] at e3
    simp only [hf]
    show _ = ((shiftS k σ (c • ![(![a, b] + c⁻¹ • v) 0, (![a, b] + c⁻¹ • v) 1]) W :
      Form (F := Coef n) faceSet k) : RawForm Face (Coef n) k) x
    rw [e1, ← e3]
    rfl
  have e4 : (∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1,
      compAltCLM (σ (-v)) k (avIntegrandS k σ c W ((x + shVec v, a), b))) =
        sqInt (fun t => f (t + c⁻¹ • v)) := by
    unfold sqInt
    refine intervalIntegral.integral_congr fun a _ => ?_
    refine intervalIntegral.integral_congr fun b _ => ?_
    exact key a b
  rw [e4, sqInt_translate (avIntegrandS_periodic h hE x) _]
  rfl

/-- A form invariant under all the transports `W ↦ σ(-v) τ_v^* W` is lattice equivariant for every
lattice scale. -/
theorem eqvS_of_shiftS (h : UniRep σ) {W : Form (F := Coef n) faceSet k}
    (hW : ∀ v, shiftS k σ v W = W) (c : ℝ) : EqvS σ c W := by
  intro m x hx
  have h1 := congrFun (congrArg (fun w : Form (F := Coef n) faceSet k =>
    (w : RawForm Face (Coef n) k)) (hW (c • intVec m))) x
  rw [shiftS_apply k σ _ _ hx] at h1
  rw [← h1, ← compAlt_mul, ← h.add]
  simp only [add_neg_cancel, h.zero]
  ext; simp

theorem avIntegrandS_of_shiftS_inv {c : ℝ} {W : Form (F := Coef n) faceSet k}
    (hW : ∀ v, shiftS k σ v W = W) (p : (Face × ℝ) × ℝ) :
    avIntegrandS k σ c W p = ((W : Form (F := Coef n) faceSet k) : RawForm Face (Coef n) k) p.1.1 := by
  unfold avIntegrandS
  rw [hW]

/-- **The average of a translation-invariant form is itself.** -/
theorem avFormS_of_shiftS_inv (hσ : ContDiff ℝ ∞ σ) (c : ℝ) {W : Form (F := Coef n) faceSet k}
    (hW : ∀ v, shiftS k σ v W = W) : avFormS hσ c W = W := by
  apply Form.ext
  intro x hx
  rw [avFormS_apply hσ c _ hx]
  unfold avRawS
  have : ∀ a b : ℝ, avIntegrandS k σ c W ((x, a), b) =
      ((W : Form (F := Coef n) faceSet k) : RawForm Face (Coef n) k) x :=
    fun a b => avIntegrandS_of_shiftS_inv hW _
  simp [this]

/-- **Idempotence**: `Av (Av W) = Av W`. -/
theorem avFormS_idem (h : UniRep σ) {c : ℝ} (hc : c ≠ 0) {W : Form (F := Coef n) faceSet k}
    (hE : EqvS σ c W) :
    avFormS h.smooth c (avFormS h.smooth c W) = avFormS h.smooth c W :=
  avFormS_of_shiftS_inv h.smooth c (shiftS_avFormS h hc hE)

theorem eqvS_avFormS (h : UniRep σ) {c : ℝ} (hc : c ≠ 0) {W : Form (F := Coef n) faceSet k}
    (hE : EqvS σ c W) : EqvS σ c (avFormS h.smooth c W) :=
  eqvS_of_shiftS h (shiftS_avFormS h hc hE) c

theorem eqvS_sub {c : ℝ} {W W' : Form (F := Coef n) faceSet k} (h : EqvS σ c W)
    (h' : EqvS σ c W') : EqvS σ c (W - W') := by
  intro m x hx
  change (W : RawForm Face (Coef n) k) _ - (W' : RawForm Face (Coef n) k) _ =
    (σ _).compContinuousAlternatingMap ((W : RawForm Face (Coef n) k) x -
      (W' : RawForm Face (Coef n) k) x)
  rw [h m x hx, h' m x hx]
  ext; simp

/-- The normalized form `W - Av W` has average zero. -/
theorem avFormS_sub_avFormS (h : UniRep σ) {c : ℝ} (hc : c ≠ 0) {W : Form (F := Coef n) faceSet k}
    (hE : EqvS σ c W) :
    avFormS h.smooth c (W - avFormS h.smooth c W) = 0 := by
  have := (avLin (k := k) h.smooth c).map_sub W (avFormS h.smooth c W)
  change avFormS h.smooth c (W - avFormS h.smooth c W) = avFormS h.smooth c W -
    avFormS h.smooth c (avFormS h.smooth c W) at this
  rw [this, avFormS_idem h hc hE, sub_self]

end TernaryPeriodPolynomials.Argument.EisensteinClass
