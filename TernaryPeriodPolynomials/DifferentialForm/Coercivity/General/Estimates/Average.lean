module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Calculus.ChartIntegral
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Forms.Operators

@[expose] public section


/-! # General coercivity, Tier B: averaging compactly supported forms over the group

For a smooth compactly supported `Coefficients n`-valued `k`-form `g` on the positive coordinates the
locally finite sum `Π g = ∑_γ γ*(g)` of its normalized pullbacks is a smooth `Γ`-equivariant form
with compact support in the orbit space: this is the "push-forward" from the cover to the quotient.
The sum is the unique tool by which the quotient `L²` structure is transported to ordinary
compactly supported analysis on the positive coordinates.

Formalized by Claude Sonnet 5.5. -/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open TernaryPoly TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceCharts
  TernaryPoly.SymmetricSpaceCovering TernaryPoly.PolynomialCoefficientMetric
  TernaryPoly.PolynomialFormMetric TernaryPoly.SmoothCoveringDeRham TernaryPoly.SmoothLocalDeRham
  TernaryPoly.PolynomialFormConnection TernaryPoly.PolynomialFormGeometricEnergy
open MeasureTheory Set Filter Topology
open scoped ContDiff

variable {Γ : Subgroup RealGL} {n k : ℕ}

/-! ### Local finiteness of translates of a compact set -/

theorem Admissible.translates_finite (h : Admissible Γ) {K : Set Coordinates} (hK : IsCompact K)
    (hKp : K ⊆ positiveCoordinates) {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    {γ : Γ | coordinateAction (γ : RealGL) x ∈ K}.Finite := by
  have hD := isCompact_chart_preimage hK hKp
  have hS : coordinateChart (coordinateChart.symm x) = x :=
    coordinateChart.right_inv (by simpa using hx)
  refine (h.transporters {coordinateChart.symm x} _ isCompact_singleton hD).subset ?_
  intro γ hγ
  refine ⟨γ • coordinateChart.symm x, ⟨_, rfl, rfl⟩, ?_⟩
  show coordinateChart (γ • coordinateChart.symm x) ∈ K
  rw [show coordinateChart (γ • coordinateChart.symm x) =
    coordinateAction (γ : RealGL) (coordinateChart (coordinateChart.symm x)) from
      (coordinateChart_act (γ : RealGL) _), hS]
  exact hγ

theorem Admissible.translates_locallyFinite (h : Admissible Γ) {K : Set Coordinates}
    (hK : IsCompact K) (hKp : K ⊆ positiveCoordinates) :
    ∀ x ∈ positiveCoordinates, ∃ N ∈ 𝓝 x, N ⊆ positiveCoordinates ∧
      {γ : Γ | ∃ y ∈ N, coordinateAction (γ : RealGL) y ∈ K}.Finite := by
  intro x hx
  obtain ⟨N, hNc, hN⟩ := exists_compact_mem_nhds (coordinateChart.symm x)
  have hD := isCompact_chart_preimage hK hKp
  have hxs : x ∈ coordinateChart.target := by simpa using hx
  have hNn : coordinateChart '' N ∈ 𝓝 x := by
    have := coordinateChart.image_mem_nhds (x := coordinateChart.symm x) (by simp) hN
    rwa [coordinateChart.right_inv hxs] at this
  refine ⟨coordinateChart '' N, hNn, ?_, ?_⟩
  · rintro _ ⟨S, -, rfl⟩
    exact extract_mem S
  · refine (h.transporters N _ hNc hD).subset ?_
    rintro γ ⟨y, ⟨S, hS, rfl⟩, hne⟩
    have hmem : coordinateAction (γ : RealGL) (coordinateChart S) = coordinateChart (γ • S) :=
      (coordinateChart_act (γ : RealGL) S).symm
    rw [hmem] at hne
    exact ⟨γ • S, ⟨S, hS, rfl⟩, hne⟩

/-! ### Algebra of the normalized pullback -/

theorem realCoefficientMap_mul (n : ℕ) (a b : RealGL) (p : Coefficients n) :
    realCoefficientMap n (a * b) p = realCoefficientMap n a (realCoefficientMap n b p) := by
  rw [realCoefficientMap_eq_action, realCoefficientMap_eq_action, realCoefficientMap_eq_action]
  simp only [LinearMap.coe_toContinuousLinearMap', map_mul, Module.End.mul_apply]

theorem realFormPullback_zero (n k : ℕ) (g : RealGL) (x : Coordinates) :
    realFormPullback n k g x 0 = 0 := by
  apply ContinuousAlternatingMap.ext
  intro v
  simp [realFormPullback, coefficientFormMap]

theorem realFormPullback_add (n k : ℕ) (g : RealGL) (x : Coordinates) (a b : FormValue n k) :
    realFormPullback n k g x (a + b) =
      realFormPullback n k g x a + realFormPullback n k g x b := by
  apply ContinuousAlternatingMap.ext
  intro v
  simp [realFormPullback, coefficientFormMap]

theorem realFormPullback_smul (n k : ℕ) (g : RealGL) (x : Coordinates) (c : ℝ) (a : FormValue n k) :
    realFormPullback n k g x (c • a) = c • realFormPullback n k g x a := by
  apply ContinuousAlternatingMap.ext
  intro v
  simp [realFormPullback, coefficientFormMap]

theorem realFormPullback_sum (n k : ℕ) (g : RealGL) (x : Coordinates) {ι : Type*}
    (s : Finset ι) (f : ι → FormValue n k) :
    realFormPullback n k g x (∑ i ∈ s, f i) = ∑ i ∈ s, realFormPullback n k g x (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using realFormPullback_zero n k g x
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, realFormPullback_add, ih]

/-- Pulling back twice is pulling back by the product. -/
theorem actPull_mul (n k : ℕ) (g g' : RealGL) (w : Coordinates → FormValue n k) {x : Coordinates}
    (hx : x ∈ positiveCoordinates) :
    actPull n k g (actPull n k g' w) x = actPull n k (g' * g) w x := by
  have hgx : coordinateAction g x ∈ positiveCoordinates := coordinateAction_mem g x hx
  rw [actPull_apply n k g _ hx, actPull_apply n k g' w hgx, actPull_apply n k (g' * g) w hx]
  have hmul : coordinateAction (g' * g) x = coordinateAction g' (coordinateAction g x) :=
    coordinateAction_mul g' g hx
  have hD : fderiv ℝ (coordinateAction (g' * g)) x =
      (fderiv ℝ (coordinateAction g') (coordinateAction g x)).comp
        (fderiv ℝ (coordinateAction g) x) := by
    have he : coordinateAction (g' * g) =ᶠ[𝓝 x] coordinateAction g' ∘ coordinateAction g := by
      filter_upwards [isOpen_positiveCoordinates.mem_nhds hx] with y hy
      exact coordinateAction_mul g' g hy
    rw [he.fderiv_eq]
    exact fderiv_comp x
      (((contDiffOn_coordinateAction g' _ hgx).contDiffAt
        (isOpen_positiveCoordinates.mem_nhds hgx)).differentiableAt (by simp))
      (((contDiffOn_coordinateAction g x hx).contDiffAt
        (isOpen_positiveCoordinates.mem_nhds hx)).differentiableAt (by simp))
  apply ContinuousAlternatingMap.ext
  intro v
  change realCoefficientMap n g⁻¹ (realCoefficientMap n g'⁻¹ (w (coordinateAction g' (coordinateAction g x))
      (fun i => fderiv ℝ (coordinateAction g') (coordinateAction g x)
        (fderiv ℝ (coordinateAction g) x (v i))))) =
    realCoefficientMap n (g' * g)⁻¹ (w (coordinateAction (g' * g) x)
      (fun i => fderiv ℝ (coordinateAction (g' * g)) x (v i)))
  rw [hmul, hD, mul_inv_rev, realCoefficientMap_mul]
  rfl

theorem actPull_add (n k : ℕ) (g : RealGL) (w z : Coordinates → FormValue n k) {x : Coordinates}
    (hx : x ∈ positiveCoordinates) :
    actPull n k g (w + z) x = actPull n k g w x + actPull n k g z x := by
  rw [actPull_apply n k g _ hx, actPull_apply n k g _ hx, actPull_apply n k g _ hx]
  exact realFormPullback_add n k g x _ _

theorem actPull_smul (n k : ℕ) (g : RealGL) (c : ℝ) (w : Coordinates → FormValue n k)
    {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    actPull n k g (c • w) x = c • actPull n k g w x := by
  rw [actPull_apply n k g _ hx, actPull_apply n k g _ hx]
  exact realFormPullback_smul n k g x c _

theorem equivariantAt_of_actPull_eq (n k : ℕ) (g : RealGL) {w : Coordinates → FormValue n k}
    {x : Coordinates} (hx : x ∈ positiveCoordinates) (h : actPull n k g w x = w x) :
    EquivariantAt n k g w x := by
  have := actPull_equation n k g w hx
  rw [h] at this
  exact this.symm

/-! ### Compactly supported test forms and their averages -/

theorem contDiff_smul_form (c : ℝ) {g : Coordinates → FormValue n k} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (c • g) := by
  let : IsBoundedSMul ℝ (FormValue n k) :=
    @NormedSpace.toIsBoundedSMul ℝ (FormValue n k) _ _ inferInstance
  exact hg.const_smul c

variable (n k) in
/-- Smooth `Coefficients n`-valued `k`-forms with compact support in the positive coordinates. -/
def Cc : Submodule ℝ (Coordinates → FormValue n k) where
  carrier := {g | ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ tsupport g ⊆ positiveCoordinates}
  zero_mem' := ⟨contDiff_const, HasCompactSupport.zero, by simp⟩
  add_mem' := by
    rintro g g' ⟨h1, h2, h3⟩ ⟨h1', h2', h3'⟩
    exact ⟨h1.add h1', h2.add h2', (tsupport_add _ _).trans (union_subset h3 h3')⟩
  smul_mem' := by
    rintro c g ⟨h1, h2, h3⟩
    exact ⟨contDiff_smul_form c h1,
      h2.mono' ((Function.support_const_smul_subset c g).trans (subset_tsupport g)),
      (tsupport_smul_subset_right (fun _ : Coordinates => c) g).trans h3⟩

/-- The average `x ↦ ∑_γ γ*g (x)` of a form over the group. -/
def actSum (Γ : Subgroup RealGL) (n k : ℕ) (g : Coordinates → FormValue n k) (x : Coordinates) :
    FormValue n k :=
  ∑ᶠ γ : Γ, actPull n k (γ : RealGL) g x

theorem actPull_ne_zero_mem (g : Coordinates → FormValue n k) (γ : RealGL) {x : Coordinates}
    (hx : x ∈ positiveCoordinates) (hne : actPull n k γ g x ≠ 0) :
    coordinateAction γ x ∈ tsupport g := by
  apply subset_tsupport
  intro h0
  apply hne
  rw [actPull_apply n k γ g hx, h0]
  exact realFormPullback_zero n k γ x

theorem Admissible.actSum_support_finite (h : Admissible Γ) {g : Coordinates → FormValue n k}
    (hg : g ∈ Cc n k) {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    (Function.support fun γ : Γ => actPull n k (γ : RealGL) g x).Finite :=
  (h.translates_finite hg.2.1 hg.2.2 hx).subset fun γ hγ => actPull_ne_zero_mem g γ hx hγ

theorem actSum_of_notMem (g : Coordinates → FormValue n k) {x : Coordinates}
    (hx : x ∉ positiveCoordinates) : actSum Γ n k g x = 0 := by
  unfold actSum
  simp [actPull_of_notMem n k _ g hx]

theorem Admissible.contDiffOn_actSum (h : Admissible Γ) {g : Coordinates → FormValue n k}
    (hg : g ∈ Cc n k) : ContDiffOn ℝ ∞ (actSum Γ n k g) positiveCoordinates := by
  apply contDiffOn_of_locally_contDiffOn
  intro x hx
  obtain ⟨N, hN, hNp, hfin⟩ := h.translates_locallyFinite hg.2.1 hg.2.2 x hx
  refine ⟨interior N, isOpen_interior, mem_interior_iff_mem_nhds.mpr hN, ?_⟩
  have hsum : ContDiffOn ℝ ∞ (fun y => ∑ γ ∈ hfin.toFinset, actPull n k (γ : RealGL) g y)
      (positiveCoordinates ∩ interior N) :=
    ContDiffOn.sum fun γ _ => (contDiffOn_actPull n k (γ : RealGL) hg.1.contDiffOn).mono
      inter_subset_left
  refine hsum.congr fun y hy => ?_
  unfold actSum
  apply finsum_eq_sum_of_support_subset
  intro γ hγ
  exact hfin.mem_toFinset.mpr ⟨y, interior_subset hy.2, actPull_ne_zero_mem g γ hy.1 hγ⟩

theorem Admissible.actSum_eq_sum (h : Admissible Γ) {g : Coordinates → FormValue n k}
    (hg : g ∈ Cc n k) {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    actSum Γ n k g x = ∑ γ ∈ (h.actSum_support_finite hg hx).toFinset,
      actPull n k (γ : RealGL) g x := by
  unfold actSum
  exact finsum_eq_sum_of_support_subset _ (by simp)

theorem Admissible.actPull_actSum (h : Admissible Γ) {g : Coordinates → FormValue n k}
    (hg : g ∈ Cc n k) (γ' : Γ) {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    actPull n k (γ' : RealGL) (actSum Γ n k g) x = actSum Γ n k g x := by
  have hgx : coordinateAction (γ' : RealGL) x ∈ positiveCoordinates :=
    coordinateAction_mem (γ' : RealGL) x hx
  rw [actPull_apply n k _ _ hx, h.actSum_eq_sum hg hgx, realFormPullback_sum]
  have h1 : ∀ γ : Γ, realFormPullback n k (γ' : RealGL) x
      (actPull n k (γ : RealGL) g (coordinateAction (γ' : RealGL) x)) =
      actPull n k ((γ * γ' : Γ) : RealGL) g x := by
    intro γ
    rw [← actPull_apply n k (γ' : RealGL) (actPull n k (γ : RealGL) g) hx,
      actPull_mul n k (γ' : RealGL) (γ : RealGL) g hx]
    rfl
  simp only [h1]
  have h2 : ∑ γ ∈ (h.actSum_support_finite hg hgx).toFinset,
      actPull n k ((γ * γ' : Γ) : RealGL) g x =
      ∑ᶠ γ : Γ, actPull n k ((γ * γ' : Γ) : RealGL) g x := by
    symm
    apply finsum_eq_sum_of_support_subset
    intro γ hγ
    rw [Finset.mem_coe, Set.Finite.mem_toFinset, Function.mem_support]
    intro h0
    apply hγ
    show actPull n k ((γ * γ' : Γ) : RealGL) g x = 0
    rw [← h1, h0]
    exact realFormPullback_zero n k _ x
  rw [h2]
  exact finsum_comp_equiv (Equiv.mulRight γ') (f := fun γ : Γ => actPull n k (γ : RealGL) g x)

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
