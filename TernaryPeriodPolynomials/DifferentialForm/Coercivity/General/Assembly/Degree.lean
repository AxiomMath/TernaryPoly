module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Assembly.Abstract
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Assembly.Pointwise
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Calculus.Divergence
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Calculus.IntegrationByParts

@[expose] public section


/-!
# The coercivity estimate in a fixed degree, on the orbit space of an admissible group

Formalized by Claude Sonnet 5.5.

For an admissible group `Γ` and the space `CForm Γ n m` of smooth equivariant `m`-forms with
compact support in the orbit space, the abstract Weitzenboeck argument of `Assembly/Abstract.lean`
is instantiated with

* the `L²` pairings `l2Form Γ n m` of the orbit space;
* `d`, `δ` and the zero-order parts `S↑ = symExt`, `S↓ = symCon`;
* the integration by parts `l2Form (d a) b = l2Form a (δ b)` (`Admissible.l2Form_d`);
* the pointwise adjointness of `S↑` and `S↓`, integrated;
* the divergence theorem on the orbit space applied to the energy current of the form.

The group-free pointwise inputs (`SymmetricAdjoint`, `PositiveCoercive`, `PositiveDivergence`, and
their degree-zero analogues) are hypotheses here; `Assembly/Degrees.lean` supplies them in every
degree, so the statements below are uniform in the degree and in `Γ`.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open TernaryPoly TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceCharts
  TernaryPoly.SymmetricSpaceCovering TernaryPoly.SmoothCoveringDeRham
  TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
  TernaryPoly.PolynomialFormConnection TernaryPoly.PolynomialFormGeometricEnergy
  TernaryPoly.PolynomialFormCoordinates
open TernaryPoly.SmoothLocalDeRham
open MeasureTheory Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

variable {Γ : Subgroup RealGL} {n k : ℕ}


/-- The underlying function of a difference of compactly supported equivariant forms. -/
theorem CForm.fn_sub' {m : ℕ} (a b : CForm Γ n m) : CForm.fn (a - b) = CForm.fn a - CForm.fn b := by
  have h : CForm.fn (a - b + b) = CForm.fn a := congrArg CForm.fn (sub_add_cancel a b)
  rw [CForm.fn_add] at h
  exact eq_sub_of_add_eq h

/-- The covariant exterior derivative is the flat exterior derivative minus the symmetric part. -/
theorem covariantExterior_eq_sub (m : ℕ) (w : Coordinates → FormValue n m) (x : Coordinates) :
    covariantExterior n m w x = extDeriv w x - symmetricExterior n m x (w x) :=
  eq_sub_of_add_eq (flatExterior_eq_covariant_add_symmetric n m w x).symm

/-! ### The divergence theorem for the energy current of a form -/

/-- If the weighted divergence of the energy current of a form `w` is twice the pointwise pairing
of `w` with another form `η`, then `w` and `η` are `L²`-orthogonal on the orbit space. -/
theorem Admissible.l2Form_eq_zero_of_current (h : Admissible Γ) {m : ℕ} (w η : CForm Γ n m)
    (hη : ∀ x ∈ positiveCoordinates,
      weightedDivergence (energyCurrent n m (CForm.fn w)) x =
        2 * formPairing n m x (CForm.fn w x) (CForm.fn η x)) :
    l2Form Γ n m w η = 0 := by
  have hsupp : projSupport Γ (energyCurrent n m (CForm.fn w)) ⊆ projSupport Γ (CForm.fn w) := by
    unfold projSupport
    refine closure_mono (image_mono fun x hx => ?_)
    intro hz
    exact hx (energyCurrent_of_eq_zero n m _ x hz)
  have hint := h.integral_eq_zero_of_divergence (contDiffOn_energyCurrent n m (CForm.smooth w))
    (fun γ => energyCurrent_isActionVectorField n m (γ : RealGL) (h.det_sq γ)
      (fun x hx => CForm.equivariantAt w γ hx))
    ((CForm.compact w).of_isClosed_subset isClosed_closure hsupp)
    (D := fun q => 2 * scalarPairing w η q)
    (continuous_const.mul (continuous_scalarPairing h w η))
    (fun x hx => by
      have hs := scalarPairing_proj h w η (coordinateChart.symm x)
      rw [coordinateChart.right_inv (by simpa using hx)] at hs
      show 2 * scalarPairing w η (proj Γ (coordinateChart.symm x)) = _
      simp only [pairingFn] at hs
      rw [hs, hη x hx])
  rw [integral_const_mul] at hint
  rw [l2Form_apply]
  exact (mul_eq_zero.mp hint).resolve_left two_ne_zero

/-! ### Integrated pointwise inputs -/

/-- The pointwise adjointness of `S↑` and `S↓`, integrated over the orbit space. -/
theorem Admissible.l2Form_symExt (h : Admissible Γ) (hadj : SymmetricAdjoint n k)
    (a : CForm Γ n k) (b : CForm Γ n (k + 1)) :
    l2Form Γ n (k + 1) (CForm.symExt Γ n k a) b = l2Form Γ n k a (CForm.symCon Γ n k b) :=
  l2Form_congr _ _ _ _ fun x hx => by
    rw [CForm.symExt_apply h a hx, CForm.symCon_apply h b hx]
    exact hadj x hx _ _

/-- Monotonicity of the orbit-space integral from a pointwise inequality along the projection. -/
theorem integral_mono_proj {F G : OrbitSpace Γ → ℝ} (hF : Integrable F (quotientVolume Γ))
    (hG : Integrable G (quotientVolume Γ)) (hFG : ∀ S : Space, F (proj Γ S) ≤ G (proj Γ S)) :
    ∫ q, F q ∂quotientVolume Γ ≤ ∫ q, G q ∂quotientVolume Γ :=
  integral_mono hF hG fun q => by
    obtain ⟨S, rfl⟩ := proj_surjective (Γ := Γ) q
    exact hFG S

/-- The pointwise coercivity of the symmetric parts, evaluated at a point of the orbit space. -/
theorem Admissible.scalarPairing_symmetric_positive (h : Admissible Γ) {c : ℝ}
    (hc : PositiveCoercive n k c) (w : CForm Γ n (k + 1)) (S : Space) :
    c * scalarPairing w w (proj Γ S) ≤
      scalarPairing (CForm.symExt Γ n (k + 1) w) (CForm.symExt Γ n (k + 1) w) (proj Γ S) +
        scalarPairing (CForm.symCon Γ n k w) (CForm.symCon Γ n k w) (proj Γ S) := by
  have hx : coordinateChart S ∈ positiveCoordinates := extract_mem S
  simp only [scalarPairing_proj h, pairingFn]
  have hp := hc _ hx (CForm.fn w (coordinateChart S))
  rw [CForm.symExt_apply h w hx, CForm.symCon_apply h w hx]
  exact hp

/-- Integrated pointwise coercivity of the symmetric parts, in positive degree. -/
theorem Admissible.normSq_symmetric_positive (h : Admissible Γ) {c : ℝ}
    (hc : PositiveCoercive n k c) (w : CForm Γ n (k + 1)) :
    c * normSq w ≤ normSq (CForm.symExt Γ n (k + 1) w) + normSq (CForm.symCon Γ n k w) := by
  have hmono : ∫ q, c * scalarPairing w w q ∂quotientVolume Γ ≤
      ∫ q, (scalarPairing (CForm.symExt Γ n (k + 1) w) (CForm.symExt Γ n (k + 1) w) q +
        scalarPairing (CForm.symCon Γ n k w) (CForm.symCon Γ n k w) q) ∂quotientVolume Γ :=
    integral_mono_proj ((integrable_scalarPairing w w).const_mul c)
      ((integrable_scalarPairing _ _).add (integrable_scalarPairing _ _))
      (h.scalarPairing_symmetric_positive hc w)
  have e1 : ∫ q, c * scalarPairing w w q ∂quotientVolume Γ =
      c * ∫ q, scalarPairing w w q ∂quotientVolume Γ := integral_const_mul c _
  have e2 : ∫ q, (scalarPairing (CForm.symExt Γ n (k + 1) w) (CForm.symExt Γ n (k + 1) w) q +
        scalarPairing (CForm.symCon Γ n k w) (CForm.symCon Γ n k w) q) ∂quotientVolume Γ =
      (∫ q, scalarPairing (CForm.symExt Γ n (k + 1) w) (CForm.symExt Γ n (k + 1) w) q
        ∂quotientVolume Γ) +
        ∫ q, scalarPairing (CForm.symCon Γ n k w) (CForm.symCon Γ n k w) q ∂quotientVolume Γ :=
    integral_add (integrable_scalarPairing _ _) (integrable_scalarPairing _ _)
  exact e1.symm.le.trans (hmono.trans e2.le)

/-- The pointwise coercivity of `S↑` in degree zero, evaluated at a point of the orbit space. -/
theorem Admissible.scalarPairing_symmetric_bottom (h : Admissible Γ) {c : ℝ}
    (hc : BottomCoercive n c) (w : CForm Γ n 0) (S : Space) :
    c * scalarPairing w w (proj Γ S) ≤
      scalarPairing (CForm.symExt Γ n 0 w) (CForm.symExt Γ n 0 w) (proj Γ S) := by
  have hx : coordinateChart S ∈ positiveCoordinates := extract_mem S
  simp only [scalarPairing_proj h, pairingFn]
  have hp := hc _ hx (CForm.fn w (coordinateChart S))
  rw [CForm.symExt_apply h w hx]
  exact hp

/-- Integrated pointwise coercivity of `S↑`, in degree zero. -/
theorem Admissible.normSq_symmetric_bottom (h : Admissible Γ) {c : ℝ}
    (hc : BottomCoercive n c) (w : CForm Γ n 0) :
    c * normSq w ≤ normSq (CForm.symExt Γ n 0 w) := by
  have hmono : ∫ q, c * scalarPairing w w q ∂quotientVolume Γ ≤
      ∫ q, scalarPairing (CForm.symExt Γ n 0 w) (CForm.symExt Γ n 0 w) q ∂quotientVolume Γ :=
    integral_mono_proj ((integrable_scalarPairing w w).const_mul c)
      (integrable_scalarPairing _ _) (h.scalarPairing_symmetric_bottom hc w)
  have e1 : ∫ q, c * scalarPairing w w q ∂quotientVolume Γ =
      c * ∫ q, scalarPairing w w q ∂quotientVolume Γ := integral_const_mul c _
  exact e1.symm.le.trans hmono

/-! ### The cancellation: the mixed term vanishes -/

/-- The mixed second-order term `S↓(dw - S↑w) + (d - S↑)(S↓w)` is `L²`-orthogonal to `w`: this is
the divergence theorem applied to the energy current of `w`. -/
theorem Admissible.l2Form_mixed_positive (h : Admissible Γ) (hdiv : PositiveDivergence n k)
    (w : CForm Γ n (k + 1)) :
    l2Form Γ n (k + 1) w
      (CForm.symCon Γ n (k + 1) (CForm.d Γ n (k + 1) w - CForm.symExt Γ n (k + 1) w) +
        (CForm.d Γ n k (CForm.symCon Γ n k w) - CForm.symExt Γ n k (CForm.symCon Γ n k w))) =
      0 := by
  refine h.l2Form_eq_zero_of_current w _ fun x hx => ?_
  have hf : (fun y => symmetricContraction n k y (CForm.fn w y)) =
      CForm.fn (CForm.symCon Γ n k w) := by
    funext y
    by_cases hy : y ∈ positiveCoordinates
    · exact (CForm.symCon_apply h w hy).symm
    · rw [CForm.outside w hy, symmetricContraction_zero, CForm.outside _ hy]
  have e2 : CForm.fn (CForm.symCon Γ n (k + 1) (CForm.d Γ n (k + 1) w - CForm.symExt Γ n (k + 1) w) +
        (CForm.d Γ n k (CForm.symCon Γ n k w) - CForm.symExt Γ n k (CForm.symCon Γ n k w))) x =
      symmetricContraction n (k + 1) x (covariantExterior n (k + 1) (CForm.fn w) x) +
        covariantExterior n k (fun y => symmetricContraction n k y (CForm.fn w y)) x := by
    simp only [covariantExterior_eq_sub, hf, CForm.fn_add, CForm.fn_sub', Pi.add_apply, Pi.sub_apply,
      CForm.symCon_apply h _ hx, CForm.d_apply _ hx, CForm.symExt_apply h _ hx]
  exact (hdiv (CForm.smooth w) x hx).trans
    (congrArg (fun v => 2 * formPairing n (k + 1) x (CForm.fn w x) v) e2.symm)

/-- The mixed term in degree zero. -/
theorem Admissible.l2Form_mixed_bottom (h : Admissible Γ) (hdiv : BottomDivergence n)
    (w : CForm Γ n 0) :
    l2Form Γ n 0 w
      (CForm.symCon Γ n 0 (CForm.d Γ n 0 w - CForm.symExt Γ n 0 w)) = 0 := by
  refine h.l2Form_eq_zero_of_current w _ fun x hx => ?_
  have e2 : CForm.fn (CForm.symCon Γ n 0 (CForm.d Γ n 0 w - CForm.symExt Γ n 0 w)) x =
      symmetricContraction n 0 x (covariantExterior n 0 (CForm.fn w) x) := by
    simp only [covariantExterior_eq_sub, CForm.fn_sub', Pi.sub_apply, CForm.symCon_apply h _ hx,
      CForm.d_apply _ hx, CForm.symExt_apply h _ hx]
  exact (hdiv (CForm.smooth w) x hx).trans
    (congrArg (fun v => 2 * formPairing n 0 x (CForm.fn w x) v) e2.symm)

/-! ### Coercivity in a fixed degree -/

/-- Coercivity of `(d, δ)` on `(k + 1)`-forms of an admissible group, from the group-free
pointwise facts of degree `k + 1`. -/
theorem Admissible.coercive_positive (h : Admissible Γ) {c : ℝ}
    (hc : PositiveCoercive n k c) (hadj : SymmetricAdjoint n k)
    (hadj' : SymmetricAdjoint n (k + 1)) (hdiv : PositiveDivergence n k)
    (w : CForm Γ n (k + 1)) :
    c * normSq w ≤ normSq (CForm.delta Γ n k w) + normSq (CForm.d Γ n (k + 1) w) := by
  -- Shortcut instances: the generic `AddCommGroup` search on the submodule `CForm` is expensive.
  let _iA : AddCommGroup (CForm Γ n k) := Submodule.addCommGroup _
  let _iM : AddCommGroup (CForm Γ n (k + 1)) := Submodule.addCommGroup _
  let _iU : AddCommGroup (CForm Γ n (k + 1 + 1)) := Submodule.addCommGroup _
  have H1 : ∀ (a : CForm Γ n k) (b : CForm Γ n (k + 1)),
      l2Form Γ n (k + 1) (CForm.d Γ n k a) b = l2Form Γ n k a (CForm.delta Γ n k b) :=
    fun a b => h.l2Form_d a b
  have H2 : ∀ (a : CForm Γ n k) (b : CForm Γ n (k + 1)),
      l2Form Γ n (k + 1) (CForm.symExt Γ n k a) b = l2Form Γ n k a (CForm.symCon Γ n k b) :=
    fun a b => h.l2Form_symExt hadj a b
  have H3 : ∀ (a : CForm Γ n (k + 1)) (u : CForm Γ n (k + 1 + 1)),
      l2Form Γ n (k + 1 + 1) (CForm.symExt Γ n (k + 1) a) u =
        l2Form Γ n (k + 1) a (CForm.symCon Γ n (k + 1) u) :=
    fun a u => h.l2Form_symExt hadj' a u
  have H4 : ∀ a : CForm Γ n (k + 1), l2Form Γ n (k + 1) a
      (CForm.symCon Γ n (k + 1) (CForm.d Γ n (k + 1) a - CForm.symExt Γ n (k + 1) a) +
        (CForm.d Γ n k (CForm.symCon Γ n k a) - CForm.symExt Γ n k (CForm.symCon Γ n k a))) = 0 :=
    fun a => h.l2Form_mixed_positive hdiv a
  have hc' : c * l2Form Γ n (k + 1) w w ≤ l2Form Γ n (k + 1 + 1)
      (CForm.symExt Γ n (k + 1) w) (CForm.symExt Γ n (k + 1) w) +
        l2Form Γ n k (CForm.symCon Γ n k w) (CForm.symCon Γ n k w) :=
    h.normSq_symmetric_positive hc w
  have key := Abstract.coercive_of_symmetric_coercive (A := CForm Γ n k) (M := CForm Γ n (k + 1))
    (U := CForm Γ n (k + 1 + 1)) (l2Form Γ n k) (l2Form Γ n (k + 1)) (l2Form Γ n (k + 1 + 1)) l2Form_comm l2Form_comm l2Form_comm (fun a => normSq_nonneg a)
    (fun a => normSq_nonneg a) (CForm.d Γ n (k + 1)) (CForm.d Γ n k) (CForm.delta Γ n k)
    (CForm.symExt Γ n (k + 1)) (CForm.symExt Γ n k) (CForm.symCon Γ n k)
    (CForm.symCon Γ n (k + 1)) H1 H2 H3 H4 c w hc'
  unfold normSq
  linarith

/-- Coercivity of `d` on `0`-forms of an admissible group, from the group-free pointwise facts of
degree zero. -/
theorem Admissible.coercive_bottom (h : Admissible Γ) {c : ℝ}
    (hc : BottomCoercive n c) (hadj : SymmetricAdjoint n 0) (hdiv : BottomDivergence n)
    (w : CForm Γ n 0) :
    c * normSq w ≤ normSq (CForm.d Γ n 0 w) := by
  have H3 : ∀ (a : CForm Γ n 0) (u : CForm Γ n (0 + 1)),
      l2Form Γ n (0 + 1) (CForm.symExt Γ n 0 a) u = l2Form Γ n 0 a (CForm.symCon Γ n 0 u) :=
    fun a u => h.l2Form_symExt hadj a u
  have H4 : ∀ a : CForm Γ n 0, l2Form Γ n 0 a
      (CForm.symCon Γ n 0 (CForm.d Γ n 0 a - CForm.symExt Γ n 0 a)) = 0 :=
    fun a => h.l2Form_mixed_bottom hdiv a
  have hc' : c * l2Form Γ n 0 w w ≤ l2Form Γ n (0 + 1) (CForm.symExt Γ n 0 w)
      (CForm.symExt Γ n 0 w) := h.normSq_symmetric_bottom hc w
  exact Abstract.coercive_bot_of_symmetric_coercive (M := CForm Γ n 0) (U := CForm Γ n (0 + 1))
    (l2Form Γ n 0) (l2Form Γ n (0 + 1))
    l2Form_comm (fun a => normSq_nonneg a) (CForm.d Γ n 0) (CForm.symExt Γ n 0)
    (CForm.symCon Γ n 0) H3 H4 c w hc'

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
