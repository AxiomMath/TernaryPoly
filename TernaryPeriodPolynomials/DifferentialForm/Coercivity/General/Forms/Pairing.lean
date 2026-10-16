module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Forms.Operators
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Measure.Quotient

@[expose] public section


/-! # General coercivity: the `L²` pairing of compactly supported equivariant forms

The pointwise metric `formPairing` of two equivariant forms is `Γ`-invariant, hence descends to a
continuous function `scalarPairing a b` on the orbit space `OrbitSpace Γ`, of compact support.  The
`L²` pairing is its integral against the Riemannian volume `quotientVolume Γ` of the orbit space,
bundled as a symmetric bilinear form `l2Form Γ n k` on `CForm Γ n k`; `normSq a` is `l2Form a a`.
For a non-admissible `Γ` the descended function is defined to be zero.

Formalized by Claude Sonnet 5.5. -/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open TernaryPoly TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceCharts
  TernaryPoly.SymmetricSpaceCovering TernaryPoly.PolynomialCoefficientMetric
  TernaryPoly.PolynomialFormMetric TernaryPoly.SmoothLocalDeRham
open MeasureTheory Set Filter
open scoped ContDiff Topology

variable {Γ : Subgroup RealGL} {n k : ℕ}

/-- The pointwise metric of two forms in coordinates. -/
def pairingFn (a b : CForm Γ n k) (x : Coordinates) : ℝ :=
  formPairing n k x (CForm.fn a x) (CForm.fn b x)

theorem pairingFn_action (h : Admissible Γ) (a b : CForm Γ n k) (γ : Γ) {x : Coordinates}
    (hx : x ∈ positiveCoordinates) :
    pairingFn a b (coordinateAction (γ : RealGL) x) = pairingFn a b x :=
  formPairing_equivariantAt n k (γ : RealGL) (h.det_sq γ) hx (CForm.equivariantAt a γ hx)
    (CForm.equivariantAt b γ hx)

theorem continuousOn_pairingFn (a b : CForm Γ n k) :
    ContinuousOn (pairingFn a b) positiveCoordinates :=
  (contDiffOn_formPairing_functions n k (fun _ h => h) (CForm.smooth a) (CForm.smooth b)).continuousOn

open Classical in
/-- The `Γ`-invariant pointwise metric of two forms, as a function on the orbit space. -/
def scalarPairing (a b : CForm Γ n k) : OrbitSpace Γ → ℝ :=
  if h : Admissible Γ then
    Quotient.lift (s := MulAction.orbitRel Γ Space)
      (fun S : Space => pairingFn a b (coordinateChart S)) (by
        intro S T hST
        obtain ⟨γ, hγ⟩ := MulAction.orbitRel_apply.mp hST
        subst hγ
        have hc : coordinateChart (γ • T) = coordinateAction (γ : RealGL) (coordinateChart T) :=
          coordinateChart_act (γ : RealGL) T
        change pairingFn a b (coordinateChart (γ • T)) = pairingFn a b (coordinateChart T)
        rw [hc]
        exact pairingFn_action h a b γ (extract_mem T))
  else fun _ => 0

theorem scalarPairing_proj (h : Admissible Γ) (a b : CForm Γ n k) (S : Space) :
    scalarPairing a b (proj Γ S) = pairingFn a b (coordinateChart S) := by
  unfold scalarPairing
  rw [dite_eq_left h]
  rfl

theorem scalarPairing_of_not_admissible (h : ¬ Admissible Γ) (a b : CForm Γ n k) :
    scalarPairing a b = fun _ => 0 := by
  unfold scalarPairing
  rw [dite_eq_right h]

theorem scalarPairing_add_left (a a' b : CForm Γ n k) :
    scalarPairing (a + a') b = scalarPairing a b + scalarPairing a' b := by
  by_cases h : Admissible Γ
  · funext q
    obtain ⟨S, rfl⟩ := proj_surjective (Γ := Γ) q
    simp only [Pi.add_apply, scalarPairing_proj h, pairingFn, CForm.fn_add, formPairing_add_left]
  · funext q
    simp [scalarPairing_of_not_admissible h]

theorem scalarPairing_smul_left (c : ℝ) (a b : CForm Γ n k) :
    scalarPairing (c • a) b = c • scalarPairing a b := by
  by_cases h : Admissible Γ
  · funext q
    obtain ⟨S, rfl⟩ := proj_surjective (Γ := Γ) q
    simp only [Pi.smul_apply, scalarPairing_proj h, pairingFn, CForm.fn_smul, formPairing_smul_left,
      smul_eq_mul]
  · funext q
    simp [scalarPairing_of_not_admissible h]

theorem scalarPairing_comm (a b : CForm Γ n k) : scalarPairing a b = scalarPairing b a := by
  by_cases h : Admissible Γ
  · funext q
    obtain ⟨S, rfl⟩ := proj_surjective (Γ := Γ) q
    simp only [scalarPairing_proj h, pairingFn]
    exact formPairing_symm n k _ (extract_mem S) _ _
  · rw [scalarPairing_of_not_admissible h, scalarPairing_of_not_admissible h]

theorem scalarPairing_add_right (a b b' : CForm Γ n k) :
    scalarPairing a (b + b') = scalarPairing a b + scalarPairing a b' := by
  rw [scalarPairing_comm, scalarPairing_add_left, scalarPairing_comm b, scalarPairing_comm b']

theorem scalarPairing_smul_right (c : ℝ) (a b : CForm Γ n k) :
    scalarPairing a (c • b) = c • scalarPairing a b := by
  rw [scalarPairing_comm, scalarPairing_smul_left, scalarPairing_comm]

theorem scalarPairing_self_nonneg (a : CForm Γ n k) (q : OrbitSpace Γ) :
    0 ≤ scalarPairing a a q := by
  by_cases h : Admissible Γ
  · obtain ⟨S, rfl⟩ := proj_surjective (Γ := Γ) q
    rw [scalarPairing_proj h]
    exact formPairing_nonneg n k _ (extract_mem S) _
  · simp [scalarPairing_of_not_admissible h]

theorem continuous_scalarPairing (h : Admissible Γ) (a b : CForm Γ n k) :
    Continuous (scalarPairing a b) := by
  unfold scalarPairing
  rw [dite_eq_left h]
  refine Continuous.quotient_lift ?_ _
  exact (continuousOn_pairingFn a b).comp_continuous continuous_chart_coordinates
    (fun S => extract_mem S)

theorem support_scalarPairing_subset (a b : CForm Γ n k) :
    Function.support (scalarPairing a b) ⊆ coordProj Γ '' Function.support (CForm.fn a) := by
  intro q hq
  by_cases h : Admissible Γ
  · obtain ⟨S, rfl⟩ := proj_surjective (Γ := Γ) q
    rw [Function.mem_support, scalarPairing_proj h] at hq
    refine ⟨coordinateChart S, ?_, coordProj_chart S⟩
    intro ha
    apply hq
    unfold pairingFn
    rw [ha]
    exact formPairing_zero_left _ _ _ _
  · exfalso
    apply hq
    rw [scalarPairing_of_not_admissible h]

theorem hasCompactSupport_scalarPairing (a b : CForm Γ n k) :
    HasCompactSupport (scalarPairing a b) := by
  unfold HasCompactSupport tsupport
  exact (CForm.compact a).of_isClosed_subset isClosed_closure
    (closure_mono (support_scalarPairing_subset a b))

theorem integrable_scalarPairing (a b : CForm Γ n k) :
    Integrable (scalarPairing a b) (quotientVolume Γ) := by
  by_cases h : Admissible Γ
  · exact h.integrable_of_continuous (continuous_scalarPairing h a b)
      (hasCompactSupport_scalarPairing a b)
  · rw [scalarPairing_of_not_admissible h]
    exact integrable_zero _ _ _

/-- Forms with the same pointwise metric pairing on the positive coordinates have the same
descended pairing (the degrees may differ). -/
theorem scalarPairing_congr {l : ℕ} (a b : CForm Γ n k) (a' b' : CForm Γ n l)
    (hpt : ∀ x ∈ positiveCoordinates, formPairing n k x (CForm.fn a x) (CForm.fn b x) =
      formPairing n l x (CForm.fn a' x) (CForm.fn b' x)) :
    scalarPairing a b = scalarPairing a' b' := by
  by_cases h : Admissible Γ
  · funext q
    obtain ⟨S, rfl⟩ := proj_surjective (Γ := Γ) q
    rw [scalarPairing_proj h, scalarPairing_proj h]
    exact hpt _ (extract_mem S)
  · rw [scalarPairing_of_not_admissible h, scalarPairing_of_not_admissible h]

/-! ### The bilinear `L²` form -/

/-- The `L²` pairing of two compactly supported equivariant forms: the integral of the descended
pointwise metric against the Riemannian volume of the orbit space. -/
def l2Form (Γ : Subgroup RealGL) (n k : ℕ) : LinearMap.BilinForm ℝ (CForm Γ n k) :=
  LinearMap.mk₂ ℝ (fun a b => ∫ q, scalarPairing a b q ∂quotientVolume Γ)
    (fun a a' b => by
      rw [scalarPairing_add_left]
      exact integral_add (integrable_scalarPairing a b) (integrable_scalarPairing a' b))
    (fun c a b => by
      rw [scalarPairing_smul_left]
      exact integral_smul c _)
    (fun a b b' => by
      rw [scalarPairing_add_right]
      exact integral_add (integrable_scalarPairing a b) (integrable_scalarPairing a b'))
    (fun c a b => by
      rw [scalarPairing_smul_right]
      exact integral_smul c _)

theorem l2Form_apply (a b : CForm Γ n k) :
    l2Form Γ n k a b = ∫ q, scalarPairing a b q ∂quotientVolume Γ := rfl

theorem l2Form_comm (a b : CForm Γ n k) : l2Form Γ n k a b = l2Form Γ n k b a := by
  rw [l2Form_apply, l2Form_apply, scalarPairing_comm]

theorem l2Form_congr {l : ℕ} (a b : CForm Γ n k) (a' b' : CForm Γ n l)
    (hpt : ∀ x ∈ positiveCoordinates, formPairing n k x (CForm.fn a x) (CForm.fn b x) =
      formPairing n l x (CForm.fn a' x) (CForm.fn b' x)) :
    l2Form Γ n k a b = l2Form Γ n l a' b' := by
  rw [l2Form_apply, l2Form_apply, scalarPairing_congr a b a' b' hpt]

/-- The squared `L²` norm. -/
def normSq (a : CForm Γ n k) : ℝ := l2Form Γ n k a a

theorem normSq_eq (a : CForm Γ n k) :
    normSq a = ∫ q, scalarPairing a a q ∂quotientVolume Γ := rfl

theorem normSq_nonneg (a : CForm Γ n k) : 0 ≤ normSq a :=
  integral_nonneg (scalarPairing_self_nonneg a)

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
