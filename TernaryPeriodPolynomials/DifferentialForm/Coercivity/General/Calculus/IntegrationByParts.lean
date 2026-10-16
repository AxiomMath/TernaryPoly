module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Calculus.ChartIntegral
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Forms.Pairing
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Forms.Operators
public import TernaryPeriodPolynomials.DifferentialForm.LocalIntegrationTest

@[expose] public section


/-! # General coercivity: integration by parts on the orbit space (G1)

For an admissible group `Γ`, compactly supported equivariant forms `a` of degree `k` and `b` of degree
`k + 1` satisfy `⟪d a, b⟫ = ⟪a, δ b⟫` for the `L²` pairing of the orbit space (`l2Form_d`), and `δ b`
is the unique element of `CForm Γ n k` with this property (`delta_unique`).

Formalized by Claude Sonnet 5.5. -/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open MeasureTheory Set Filter Topology TernaryPoly.SymmetricSpacePositive
  TernaryPoly.SymmetricSpaceCharts TernaryPoly.SymmetricSpaceCovering
  TernaryPoly.SymmetricSpaceRiemannian TernaryPoly.PolynomialCoefficientMetric
  TernaryPoly.PolynomialFormMetric TernaryPoly.PolynomialFormCoordinates
  TernaryPoly.SmoothCoveringDeRham TernaryPoly.SmoothLocalDeRham
  TernaryPoly.PolynomialFormGeometricEnergy
open scoped ContDiff

variable {Γ : Subgroup RealGL} {n k : ℕ}

theorem scalarPairing_coordProj (h : Admissible Γ) (a b : CForm Γ n k) {x : Coordinates}
    (hx : x ∈ positiveCoordinates) :
    scalarPairing a b (coordProj Γ x) = formPairing n k x (CForm.fn a x) (CForm.fn b x) := by
  have hS : coordinateChart (coordinateChart.symm x) = x :=
    coordinateChart.right_inv (by simpa using hx)
  have := scalarPairing_proj h a b (coordinateChart.symm x)
  rw [hS] at this
  exact this

/-! ### The first-order error term of the cutoff -/

/-- The form `u a` for a scalar function `u`. -/
def cutForm (a : CForm Γ n k) (u : Coordinates → ℝ) : Coordinates → FormValue n k :=
  fun y => u y • CForm.fn a y

/-- The pointwise pairing `⟨d a (x), b (x)⟩`. -/
def dPair (a : CForm Γ n k) (b : CForm Γ n (k + 1)) (x : Coordinates) : ℝ :=
  formPairing n (k + 1) x (extDeriv (CForm.fn a) x) (CForm.fn b x)

/-- The pointwise pairing `⟨a (x), δ b (x)⟩` with the explicit local adjoint. -/
def aPair (a : CForm Γ n k) (b : CForm Γ n (k + 1)) (x : Coordinates) : ℝ :=
  formPairing n k x (CForm.fn a x) (localAdjoint n k (CForm.fn b) x)

/-- `T_u(x) = ⟨d(u a)(x), b(x)⟩ - u(x) ⟨d a(x), b(x)⟩`: the error of the Leibniz rule for a scalar
cutoff `u`. -/
def Tf (a : CForm Γ n k) (b : CForm Γ n (k + 1)) (u : Coordinates → ℝ) (x : Coordinates) : ℝ :=
  formPairing n (k + 1) x (extDeriv (cutForm a u) x) (CForm.fn b x) - u x * dPair a b x

theorem Tf_congr (a : CForm Γ n k) (b : CForm Γ n (k + 1)) {u u' : Coordinates → ℝ}
    {x : Coordinates} (hu : u =ᶠ[𝓝 x] u') : Tf a b u x = Tf a b u' x := by
  have he : cutForm a u =ᶠ[𝓝 x] cutForm a u' := by
    filter_upwards [hu] with y hy
    simp only [cutForm, hy]
  unfold Tf
  rw [he.extDeriv_eq, hu.eq_of_nhds]

theorem Tf_zero (a : CForm Γ n k) (b : CForm Γ n (k + 1)) (x : Coordinates) :
    Tf a b (fun _ => 0) x = 0 := by
  have h0 : cutForm a (fun _ => 0) = 0 := by
    funext y
    exact zero_smul ℝ (CForm.fn a y)
  unfold Tf
  rw [h0, extDeriv_eq_zero_of_notMem_tsupport n k 0 (by simp)]
  simp

theorem Tf_one (a : CForm Γ n k) (b : CForm Γ n (k + 1)) (x : Coordinates) :
    Tf a b (fun _ => 1) x = 0 := by
  have h1 : cutForm a (fun _ => 1) = CForm.fn a := by
    funext y
    exact one_smul ℝ (CForm.fn a y)
  unfold Tf dPair
  rw [h1]
  simp

theorem Tf_add (a : CForm Γ n k) (b : CForm Γ n (k + 1)) {u u' : Coordinates → ℝ}
    {x : Coordinates} (hx : x ∈ positiveCoordinates) (hu : DifferentiableAt ℝ u x)
    (hu' : DifferentiableAt ℝ u' x) :
    Tf a b (fun y => u y + u' y) x = Tf a b u x + Tf a b u' x := by
  let : IsBoundedSMul ℝ (FormValue n k) :=
    @NormedSpace.toIsBoundedSMul ℝ (FormValue n k) _ _ inferInstance
  have ha : DifferentiableAt ℝ (CForm.fn a) x :=
    ((CForm.smooth a x hx).contDiffAt (isOpen_positiveCoordinates.mem_nhds hx)).differentiableAt
      (by simp)
  have h1 : DifferentiableAt ℝ (cutForm a u) x := DifferentiableAt.smul (f := CForm.fn a) hu ha
  have h2 : DifferentiableAt ℝ (cutForm a u') x := DifferentiableAt.smul (f := CForm.fn a) hu' ha
  have hsplit : cutForm a (fun y => u y + u' y) = fun y => cutForm a u y + cutForm a u' y :=
    funext fun y => add_smul (u y) (u' y) (CForm.fn a y)
  unfold Tf
  rw [hsplit, extDeriv_fun_add h1 h2, formPairing_add_left]
  beta_reduce
  ring

theorem Tf_sum (a : CForm Γ n k) (b : CForm Γ n (k + 1)) {ι : Type*} [DecidableEq ι]
    (A : Finset ι) (u : ι → Coordinates → ℝ) {x : Coordinates} (hx : x ∈ positiveCoordinates)
    (hu : ∀ i ∈ A, DifferentiableAt ℝ (u i) x) :
    Tf a b (fun y => ∑ i ∈ A, u i y) x = ∑ i ∈ A, Tf a b (u i) x := by
  induction A using Finset.induction_on with
  | empty => simpa using Tf_zero a b x
  | insert j A hj ih =>
    have hA : ∀ i ∈ A, DifferentiableAt ℝ (u i) x := fun i hi => hu i (Finset.mem_insert_of_mem hi)
    have hsum : (fun y => ∑ i ∈ insert j A, u i y) = fun y => u j y + ∑ i ∈ A, u i y :=
      funext fun y => Finset.sum_insert hj
    rw [Finset.sum_insert hj, hsum,
      Tf_add a b hx (hu j (Finset.mem_insert_self j A)) (DifferentiableAt.fun_sum hA), ih hA]

theorem Tf_contDiffOn (a : CForm Γ n k) (b : CForm Γ n (k + 1)) {φ : Coordinates → ℝ}
    (hφ : ContDiff ℝ ∞ φ) : ContDiffOn ℝ ∞ (Tf a b φ) positiveCoordinates := by
  let : IsBoundedSMul ℝ (FormValue n k) :=
    @NormedSpace.toIsBoundedSMul ℝ (FormValue n k) _ _ inferInstance
  have hG : ContDiffOn ℝ ∞ (cutForm a φ) positiveCoordinates :=
    ContDiffOn.smul (𝕜 := ℝ) (𝕜' := ℝ) (E := Coordinates) (F := FormValue n k)
      hφ.contDiffOn (CForm.smooth a)
  have h1 := contDiffOn_formPairing_functions n (k + 1) (fun _ h => h)
    (smooth_extDeriv isOpen_positiveCoordinates hG) (CForm.smooth b)
  have h2 := contDiffOn_formPairing_functions n (k + 1) (fun _ h => h)
    (smooth_extDeriv isOpen_positiveCoordinates (CForm.smooth a)) (CForm.smooth b)
  exact h1.sub (hφ.contDiffOn.mul h2)

theorem tsupport_cutForm_subset (a : CForm Γ n k) (φ : Coordinates → ℝ) :
    tsupport (cutForm a φ) ⊆ tsupport φ := by
  unfold cutForm
  exact tsupport_smul_subset_left φ (CForm.fn a)

theorem support_cutForm_subset (a : CForm Γ n k) (φ : Coordinates → ℝ) :
    Function.support (cutForm a φ) ⊆ Function.support φ := by
  intro y hy
  rw [Function.mem_support] at hy ⊢
  intro hφy
  apply hy
  show φ y • CForm.fn a y = 0
  rw [hφy]
  exact zero_smul ℝ (CForm.fn a y)

theorem Tf_eq_zero (a : CForm Γ n k) (b : CForm Γ n (k + 1)) {φ : Coordinates → ℝ}
    {x : Coordinates} (hx : x ∉ tsupport φ) : Tf a b φ x = 0 := by
  have hG : x ∉ tsupport (cutForm a φ) := fun hh => hx (tsupport_cutForm_subset a φ hh)
  unfold Tf
  rw [extDeriv_eq_zero_of_notMem_tsupport n k _ hG, image_eq_zero_of_notMem_tsupport hx]
  simp

/-- The error term transforms by the substitution of the translated cutoff. -/
theorem Tf_action (h : Admissible Γ) (a : CForm Γ n k) (b : CForm Γ n (k + 1))
    {φ : Coordinates → ℝ} (hφ : ContDiff ℝ ∞ φ) (γ : Γ) {x : Coordinates}
    (hx : x ∈ positiveCoordinates) :
    Tf a b φ (coordinateAction (γ : RealGL) x) =
      Tf a b (fun y => φ (coordinateAction (γ : RealGL) y)) x := by
  have hdet : (γ : RealGL).val.det ^ 2 = 1 := h.det_sq γ
  have hxg : coordinateAction (γ : RealGL) x ∈ positiveCoordinates :=
    coordinateAction_mem (γ : RealGL) x hx
  let : IsBoundedSMul ℝ (FormValue n k) :=
    @NormedSpace.toIsBoundedSMul ℝ (FormValue n k) _ _ inferInstance
  have hG : ContDiffOn ℝ ∞ (cutForm a φ) positiveCoordinates :=
    ContDiffOn.smul (𝕜 := ℝ) (𝕜' := ℝ) (E := Coordinates) (F := FormValue n k)
      hφ.contDiffOn (CForm.smooth a)
  have key1 : actPull n k (γ : RealGL) (cutForm a φ) =ᶠ[𝓝 x]
      cutForm a (fun y => φ (coordinateAction (γ : RealGL) y)) := by
    filter_upwards [isOpen_positiveCoordinates.mem_nhds hx] with y hy
    rw [actPull_apply n k (γ : RealGL) _ hy]
    have hlin : realFormPullback n k (γ : RealGL) y (cutForm a φ (coordinateAction (γ : RealGL) y)) =
        φ (coordinateAction (γ : RealGL) y) •
          realFormPullback n k (γ : RealGL) y (CForm.fn a (coordinateAction (γ : RealGL) y)) := by
      ext v
      simp [realFormPullback, cutForm, coefficientFormMap]
    rw [hlin, ← actPull_apply n k (γ : RealGL) (CForm.fn a) hy,
      actPull_eq_of_equivariantAt n k (γ : RealGL) hy (CForm.equivariantAt a γ hy)]
    try rfl
  have hb : actPull n (k + 1) (γ : RealGL) (CForm.fn b) x = CForm.fn b x :=
    actPull_eq_of_equivariantAt n (k + 1) (γ : RealGL) hx (CForm.equivariantAt b γ hx)
  have key2 : formPairing n (k + 1) (coordinateAction (γ : RealGL) x)
      (extDeriv (cutForm a φ) (coordinateAction (γ : RealGL) x))
      (CForm.fn b (coordinateAction (γ : RealGL) x)) =
      formPairing n (k + 1) x
        (extDeriv (cutForm a (fun y => φ (coordinateAction (γ : RealGL) y))) x) (CForm.fn b x) := by
    rw [← key1.extDeriv_eq, extDeriv_actPull n k (γ : RealGL) hG hx]
    have := formPairing_actPull n (k + 1) (γ : RealGL) hdet (extDeriv (cutForm a φ))
      (CForm.fn b) hx
    rw [hb] at this
    exact this.symm
  have key3 : dPair a b (coordinateAction (γ : RealGL) x) = dPair a b x := by
    have := pairingFn_action h (CForm.d Γ n k a) b γ hx
    simpa only [pairingFn, dPair, CForm.d_apply a hx, CForm.d_apply a hxg] using this
  unfold Tf
  rw [key2, key3]

/-- The error terms of the translates of a cutoff sum to zero. -/
theorem Admissible.tsum_Tf (h : Admissible Γ) (a : CForm Γ n k) (b : CForm Γ n (k + 1))
    {Q : Set (OrbitSpace Γ)} {φ : Coordinates → ℝ} (hφ : CutoffData Γ Q φ)
    (hbQ : projSupport Γ (CForm.fn b) ⊆ Q) (S : Space) :
    ∑' γ : Γ, Tf a b φ (coordinateChart (γ • S)) = 0 := by
  classical
  have hx : coordinateChart S ∈ positiveCoordinates := extract_mem S
  have hterm : ∀ γ : Γ, Tf a b φ (coordinateChart (γ • S)) =
      Tf a b (fun y => φ (coordinateAction (γ : RealGL) y)) (coordinateChart S) := by
    intro γ
    have hc : coordinateChart (γ • S) = coordinateAction (γ : RealGL) (coordinateChart S) :=
      coordinateChart_act (γ : RealGL) S
    rw [hc]
    exact Tf_action h a b hφ.smooth γ hx
  simp only [hterm]
  by_cases hxb : coordProj Γ (coordinateChart S) ∈ projSupport Γ (CForm.fn b)
  · obtain ⟨N, hN, A, hNp, hzero, hsum⟩ := hφ.localPartition hx (hbQ hxb)
    have hout : ∀ γ : Γ, γ ∉ A →
        Tf a b (fun y => φ (coordinateAction (γ : RealGL) y)) (coordinateChart S) = 0 := by
      intro γ hγ
      have he : (fun y => φ (coordinateAction (γ : RealGL) y)) =ᶠ[𝓝 (coordinateChart S)]
          fun _ => (0 : ℝ) := by
        filter_upwards [hN] with y hy using hzero γ hγ y hy
      rw [Tf_congr a b he, Tf_zero]
    rw [tsum_eq_sum (s := A) hout]
    have hdiff : ∀ γ ∈ A, DifferentiableAt ℝ
        (fun y => φ (coordinateAction (γ : RealGL) y)) (coordinateChart S) := by
      intro γ _
      exact (hφ.smooth.differentiable (by simp) _).comp _
        (((contDiffOn_coordinateAction (γ : RealGL) _ hx).contDiffAt
          (isOpen_positiveCoordinates.mem_nhds hx)).differentiableAt (by simp))
    rw [← Tf_sum a b A _ hx hdiff]
    have he : (fun y => ∑ γ ∈ A, φ (coordinateAction (γ : RealGL) y)) =ᶠ[𝓝 (coordinateChart S)]
        fun _ => (1 : ℝ) := by
      filter_upwards [hN] with y hy using hsum y hy
    rw [Tf_congr a b he, Tf_one]
  · have hb0 : CForm.fn b (coordinateChart S) = 0 := by
      have := (eventuallyEq_zero_of_notMem_projSupport hx hxb).eq_of_nhds
      simpa using this
    have hz : ∀ γ : Γ,
        Tf a b (fun y => φ (coordinateAction (γ : RealGL) y)) (coordinateChart S) = 0 := by
      intro γ
      unfold Tf dPair
      rw [hb0]
      simp
    simp only [hz, tsum_zero]

/-! ### Integration by parts -/

/-- Integration by parts for the cut-off form `φ a` against `b`, in the chart integral. -/
theorem integral_extDeriv_cut_eq {Q : Set (OrbitSpace Γ)} {φ : Coordinates → ℝ}
    (hφ : CutoffData Γ Q φ) (a : CForm Γ n k) (b : CForm Γ n (k + 1)) :
    ∫ x in positiveCoordinates, coordinateDensity x *
        formPairing n (k + 1) x (extDeriv (cutForm a φ) x) (CForm.fn b x) =
      ∫ x in positiveCoordinates, coordinateDensity x *
        formPairing n k x (cutForm a φ x) (localAdjoint n k (CForm.fn b) x) := by
  let : IsBoundedSMul ℝ (FormValue n k) :=
    @NormedSpace.toIsBoundedSMul ℝ (FormValue n k) _ _ inferInstance
  have hGon : ContDiffOn ℝ ∞ (cutForm a φ) positiveCoordinates :=
    ContDiffOn.smul (𝕜 := ℝ) (𝕜' := ℝ) (E := Coordinates) (F := FormValue n k)
      hφ.smooth.contDiffOn (CForm.smooth a)
  have hGs : tsupport (cutForm a φ) ⊆ positiveCoordinates :=
    (tsupport_cutForm_subset a φ).trans hφ.tsupport_subset
  have hGc : HasCompactSupport (cutForm a φ) :=
    hφ.compactSupport.mono' ((support_cutForm_subset a φ).trans (subset_tsupport φ))
  have hibp := integral_extDeriv_localAdjoint_test n k (cutForm a φ) (CForm.fn b) hGon
    (CForm.smooth b) hGc hGs
  have hLout : ∀ x ∉ positiveCoordinates, coordinateDensity x *
      formPairing n (k + 1) x (extDeriv (cutForm a φ) x) (CForm.fn b x) = 0 := by
    intro x hx
    rw [extDeriv_eq_zero_of_notMem_tsupport n k (cutForm a φ) (fun hh => hx (hGs hh))]
    simp
  have hRout : ∀ x ∉ positiveCoordinates, coordinateDensity x *
      formPairing n k x (cutForm a φ x) (localAdjoint n k (CForm.fn b) x) = 0 := by
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (f := cutForm a φ) (fun hh => hx (hGs hh))]
    simp
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hLout,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero hRout] at hibp
  exact hibp

/-- The first integral of `integral_extDeriv_cut_eq` splits into the Leibniz error term and the
uncut pairing. -/
theorem integral_extDeriv_cut_split {Q : Set (OrbitSpace Γ)} {φ : Coordinates → ℝ}
    (hφ : CutoffData Γ Q φ) (a : CForm Γ n k) (b : CForm Γ n (k + 1)) :
    ∫ x in positiveCoordinates, coordinateDensity x *
        formPairing n (k + 1) x (extDeriv (cutForm a φ) x) (CForm.fn b x) =
      (∫ x in positiveCoordinates, coordinateDensity x * Tf a b φ x) +
        ∫ x in positiveCoordinates, coordinateDensity x * (φ x * dPair a b x) := by
  have hPc : ContinuousOn (dPair a b) positiveCoordinates :=
    (contDiffOn_formPairing_functions n (k + 1) (fun _ h => h)
      (smooth_extDeriv isOpen_positiveCoordinates (CForm.smooth a)) (CForm.smooth b)).continuousOn
  have hTc : ContinuousOn (Tf a b φ) positiveCoordinates :=
    (Tf_contDiffOn a b hφ.smooth).continuousOn
  have hi1 : IntegrableOn (fun x => coordinateDensity x * (φ x * dPair a b x)) positiveCoordinates :=
    integrableOn_positive (contDiffOn_coordinateDensity.continuousOn.mul
        (hφ.smooth.continuous.continuousOn.mul hPc)) hφ.compactSupport hφ.tsupport_subset
      (fun x hx => by simp [image_eq_zero_of_notMem_tsupport hx])
  have hi2 : IntegrableOn (fun x => coordinateDensity x * Tf a b φ x) positiveCoordinates :=
    integrableOn_positive (contDiffOn_coordinateDensity.continuousOn.mul hTc) hφ.compactSupport
      hφ.tsupport_subset (fun x hx => by simp [Tf_eq_zero a b hx])
  have hL : ∫ x in positiveCoordinates, coordinateDensity x *
      formPairing n (k + 1) x (extDeriv (cutForm a φ) x) (CForm.fn b x) =
      (∫ x in positiveCoordinates, coordinateDensity x * Tf a b φ x) +
        ∫ x in positiveCoordinates, coordinateDensity x * (φ x * dPair a b x) := by
    rw [← integral_add hi2 hi1]
    apply setIntegral_congr_fun isOpen_positiveCoordinates.measurableSet
    intro x _
    dsimp only
    unfold Tf
    ring
  exact hL

/-- The pairing of the cut-off form with the explicit local adjoint. -/
theorem integral_cut_adjoint_eq {φ : Coordinates → ℝ}
    (a : CForm Γ n k) (b : CForm Γ n (k + 1)) :
    ∫ x in positiveCoordinates, coordinateDensity x *
        formPairing n k x (cutForm a φ x) (localAdjoint n k (CForm.fn b) x) =
      ∫ x in positiveCoordinates, coordinateDensity x * (φ x * aPair a b x) := by
  apply setIntegral_congr_fun isOpen_positiveCoordinates.measurableSet
  intro x _
  dsimp only
  simp only [cutForm, formPairing_smul_left, aPair]

/-- The error terms of the Leibniz rule integrate to zero. -/
theorem Admissible.integral_Tf_eq_zero (h : Admissible Γ) (a : CForm Γ n k) (b : CForm Γ n (k + 1))
    {Q : Set (OrbitSpace Γ)} {φ : Coordinates → ℝ} (hφ : CutoffData Γ Q φ)
    (hbQ : projSupport Γ (CForm.fn b) ⊆ Q) :
    ∫ x in positiveCoordinates, coordinateDensity x * Tf a b φ x = 0 := by
  have hTc : ContinuousOn (Tf a b φ) positiveCoordinates :=
    (Tf_contDiffOn a b hφ.smooth).continuousOn
  rw [← integral_chart (Tf a b φ)]
  apply h.integral_eq_zero_of_tsum_eq_zero
  · exact (hTc.comp_continuous continuous_chart_coordinates (fun S => extract_mem S)).measurable
  · exact integrable_chart hTc hφ.compactSupport hφ.tsupport_subset
      (fun x hx => Tf_eq_zero a b hx)
  · intro S
    exact h.tsum_Tf a b hφ hbQ S

/-- The chart integral of the cut-off pairing `⟨d a, b⟩` over the orbit space. -/
theorem Admissible.integral_scalarPairing_d (h : Admissible Γ) (a : CForm Γ n k)
    (b : CForm Γ n (k + 1)) (φ : Coordinates → ℝ) :
    ∫ x in positiveCoordinates, coordinateDensity x *
        (φ x * scalarPairing (CForm.d Γ n k a) b (coordProj Γ x)) =
      ∫ x in positiveCoordinates, coordinateDensity x * (φ x * dPair a b x) := by
  apply setIntegral_congr_fun isOpen_positiveCoordinates.measurableSet
  intro x hx
  dsimp only
  rw [scalarPairing_coordProj h _ _ hx, CForm.d_apply a hx]
  try rfl

/-- The chart integral of the cut-off pairing `⟨a, δ b⟩` over the orbit space. -/
theorem Admissible.integral_scalarPairing_delta (h : Admissible Γ) (a : CForm Γ n k)
    (b : CForm Γ n (k + 1)) (φ : Coordinates → ℝ) :
    ∫ x in positiveCoordinates, coordinateDensity x *
        (φ x * scalarPairing a (CForm.delta Γ n k b) (coordProj Γ x)) =
      ∫ x in positiveCoordinates, coordinateDensity x * (φ x * aPair a b x) := by
  apply setIntegral_congr_fun isOpen_positiveCoordinates.measurableSet
  intro x hx
  dsimp only
  rw [scalarPairing_coordProj h _ _ hx, CForm.delta_apply h b hx]
  try rfl

/-- The `L²` pairing as a cutoff-weighted chart integral. -/
theorem Admissible.l2Form_eq_chart_integral (h : Admissible Γ) {l : ℕ} {Q : Set (OrbitSpace Γ)}
    {φ : Coordinates → ℝ} (hφ : CutoffData Γ Q φ) (a b : CForm Γ n l)
    (hF : Function.support (scalarPairing a b) ⊆ Q) :
    l2Form Γ n l a b = ∫ x in positiveCoordinates, coordinateDensity x *
      (φ x * scalarPairing a b (coordProj Γ x)) :=
  (l2Form_apply a b).trans (h.integral_quotient_eq hφ (continuous_scalarPairing h a b) hF)

theorem Admissible.l2Form_d (h : Admissible Γ) (a : CForm Γ n k) (b : CForm Γ n (k + 1)) :
    l2Form Γ n (k + 1) (CForm.d Γ n k a) b = l2Form Γ n k a (CForm.delta Γ n k b) := by
  have hQ : IsCompact (projSupport Γ (CForm.fn a) ∪ projSupport Γ (CForm.fn b)) :=
    (CForm.compact a).union (CForm.compact b)
  have hex := h.exists_cutoff hQ
  obtain ⟨φ, hφ⟩ := hex
  have hFL : Function.support (scalarPairing (CForm.d Γ n k a) b) ⊆
      projSupport Γ (CForm.fn a) ∪ projSupport Γ (CForm.fn b) := by
    rw [scalarPairing_comm]
    exact (support_scalarPairing_subset b _).trans (subset_closure.trans subset_union_right)
  have hFR : Function.support (scalarPairing a (CForm.delta Γ n k b)) ⊆
      projSupport Γ (CForm.fn a) ∪ projSupport Γ (CForm.fn b) :=
    (support_scalarPairing_subset a _).trans (subset_closure.trans subset_union_left)
  rw [h.l2Form_eq_chart_integral hφ _ _ hFL, h.l2Form_eq_chart_integral hφ _ _ hFR]
  rw [h.integral_scalarPairing_d a b φ, h.integral_scalarPairing_delta a b φ]
  have hibp := integral_extDeriv_cut_eq hφ a b
  rw [integral_extDeriv_cut_split hφ a b, integral_cut_adjoint_eq (φ := φ) a b,
    h.integral_Tf_eq_zero a b hφ (fun q hq => Or.inr hq), zero_add] at hibp
  exact hibp

/-! ### Nondegeneracy and uniqueness of the formal adjoint -/

/-- The `L²` pairing of an admissible group is definite. -/
theorem Admissible.eq_zero_of_normSq_eq_zero (h : Admissible Γ) (c : CForm Γ n k)
    (hc : normSq c = 0) : c = 0 := by
  obtain ⟨φ, hφ⟩ := h.exists_cutoff (CForm.compact c)
  have hsupp : Function.support (scalarPairing c c) ⊆ projSupport Γ (CForm.fn c) :=
    (support_scalarPairing_subset c c).trans subset_closure
  rw [normSq_eq, h.integral_quotient_eq hφ (continuous_scalarPairing h c c) hsupp] at hc
  have hgc : ContinuousOn (fun x => coordinateDensity x * (φ x * scalarPairing c c (coordProj Γ x)))
      positiveCoordinates :=
    contDiffOn_coordinateDensity.continuousOn.mul (hφ.smooth.continuous.continuousOn.mul
      ((continuous_scalarPairing h c c).comp_continuousOn continuousOn_coordProj))
  have hg0 : ∀ x ∈ positiveCoordinates,
      0 ≤ coordinateDensity x * (φ x * scalarPairing c c (coordProj Γ x)) := fun x hx =>
    mul_nonneg (coordinateDensity_pos x hx).le
      (mul_nonneg (hφ.nonneg x) (scalarPairing_self_nonneg c _))
  have hgi := integrableOn_positive hgc hφ.compactSupport hφ.tsupport_subset
    (fun x hx => by simp [image_eq_zero_of_notMem_tsupport hx])
  have hae := (setIntegral_eq_zero_iff_of_nonneg_ae
    (ae_restrict_of_forall_mem isOpen_positiveCoordinates.measurableSet hg0) hgi).mp hc
  have hEq := Measure.eqOn_open_of_ae_eq hae isOpen_positiveCoordinates hgc continuousOn_const
  apply CForm.ext
  intro x hx
  by_contra hne
  have hS : coordinateChart (coordinateChart.symm x) = x :=
    coordinateChart.right_inv (by simpa using hx)
  set S : Space := coordinateChart.symm x with hSdef
  have hpos : 0 < scalarPairing c c (proj Γ S) := by
    rw [scalarPairing_proj h, pairingFn, hS]
    exact formPairing_positive n k x hx _ hne
  have hQ : proj Γ S ∈ projSupport Γ (CForm.fn c) := hsupp (ne_of_gt hpos)
  have hsum := hφ.tsum_eq_one hQ
  obtain ⟨γ, hγ⟩ : ∃ γ : Γ, φ (coordinateChart (γ • S)) ≠ 0 := by
    by_contra hall
    have hall' : ∀ γ : Γ, φ (coordinateChart (γ • S)) = 0 := fun γ =>
      not_not.mp fun hne => hall ⟨γ, hne⟩
    rw [tsum_congr hall', tsum_zero] at hsum
    exact zero_ne_one hsum
  have hy : coordinateChart (γ • S) ∈ positiveCoordinates := extract_mem _
  have hgy := hEq hy
  have hφy : 0 < φ (coordinateChart (γ • S)) := lt_of_le_of_ne (hφ.nonneg _) (Ne.symm hγ)
  have hprojy : coordProj Γ (coordinateChart (γ • S)) = proj Γ S := by
    rw [coordProj_chart, proj_smul]
  simp only [Pi.zero_apply] at hgy
  rw [hprojy] at hgy
  exact (ne_of_gt (mul_pos (coordinateDensity_pos _ hy) (mul_pos hφy hpos))) hgy

/-- `e` is a formal adjoint of `d` at `b` for the `L²` pairing of the orbit space. -/
def IsFormalAdjoint (Γ : Subgroup RealGL) (n k : ℕ) (b : CForm Γ n (k + 1)) (e : CForm Γ n k) :
    Prop :=
  ∀ a : CForm Γ n k, l2Form Γ n (k + 1) (CForm.d Γ n k a) b = l2Form Γ n k a e

/-- The explicit local adjoint is a formal adjoint of the exterior derivative. -/
theorem Admissible.delta_isFormalAdjoint (h : Admissible Γ) (b : CForm Γ n (k + 1)) :
    IsFormalAdjoint Γ n k b (CForm.delta Γ n k b) := fun a => h.l2Form_d a b

/-- The formal adjoint of the exterior derivative is unique, hence equal to `δ`. -/
theorem Admissible.delta_unique (h : Admissible Γ) (b : CForm Γ n (k + 1)) (e : CForm Γ n k)
    (he : IsFormalAdjoint Γ n k b e) : e = CForm.delta Γ n k b := by
  have key : ∀ a : CForm Γ n k,
      l2Form Γ n k a e = l2Form Γ n k a (CForm.delta Γ n k b) :=
    fun a => (he a).symm.trans (h.l2Form_d a b)
  have h1 : normSq (e - CForm.delta Γ n k b) = 0 := by
    show l2Form Γ n k (e - CForm.delta Γ n k b) (e - CForm.delta Γ n k b) = 0
    rw [map_sub (l2Form Γ n k (e - CForm.delta Γ n k b)), key, sub_self]
  exact sub_eq_zero.mp (h.eq_zero_of_normSq_eq_zero (e - CForm.delta Γ n k b) h1)

theorem Admissible.isFormalAdjoint_iff (h : Admissible Γ) (b : CForm Γ n (k + 1))
    (e : CForm Γ n k) : IsFormalAdjoint Γ n k b e ↔ e = CForm.delta Γ n k b :=
  ⟨h.delta_unique b e, fun he => by subst he; exact h.delta_isFormalAdjoint b⟩

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
