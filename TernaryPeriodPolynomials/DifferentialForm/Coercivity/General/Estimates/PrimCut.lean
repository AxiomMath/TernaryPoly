module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Estimates.Weyl

@[expose] public section


/-! # General coercivity, Tier B (phase F): cutoffs, commutators and the group action on test forms

Linear maps on the space `Cc n k` of compactly supported smooth test forms: multiplication by a
smooth function `mulCc`, the coderivative `deltaCc`, the pullback `pullCc γ` by a group element,
and the commutator `commCc c = c δ - δ c` of the coderivative with a cutoff.  Its support is
contained in the support of the cutoff and of the form; it is natural for `pullCc`; and its
pairing with a zero-form is the pairing of the form against the forward symbol of the cutoff.

Formalized by Claude Sonnet 5.5. -/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open TernaryPoly TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceCharts
  TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
  TernaryPoly.PolynomialFormWeakSmooth TernaryPoly.PolynomialFormCoordinates
  TernaryPoly.SymmetricSpaceRiemannian TernaryPoly.CompactCoordinateIntegration
open Set MeasureTheory Filter Topology
open scoped ContDiff

variable {n k : ℕ}

/-- Multiplication of test forms by a smooth function. -/
def mulCc (ψ : Coordinates → ℝ) (hψ : ContDiff ℝ ∞ ψ) : Cc n k →ₗ[ℝ] Cc n k where
  toFun g := ⟨fun x => ψ x • g.1 x, by
      let : IsBoundedSMul ℝ (FormValue n k) :=
        @NormedSpace.toIsBoundedSMul ℝ (FormValue n k) _ _ inferInstance
      exact hψ.smul g.2.1,
    g.2.2.1.mono' ((Function.support_smul_subset_right ψ g.1).trans (subset_tsupport _)),
    (tsupport_smul_subset_right ψ g.1).trans g.2.2.2⟩
  map_add' g h := Subtype.ext (funext fun x => by
    change ψ x • (g.1 x + h.1 x) = ψ x • g.1 x + ψ x • h.1 x
    exact fv_smul_add _ _ _)
  map_smul' c g := Subtype.ext (funext fun x => by
    change ψ x • (c • g.1 x) = c • (ψ x • g.1 x)
    rw [fv_smul_smul, fv_smul_smul, mul_comm])

theorem mulCc_coe (ψ : Coordinates → ℝ) (hψ : ContDiff ℝ ∞ ψ) (g : Cc n k) (x : Coordinates) :
    (mulCc ψ hψ g).1 x = ψ x • g.1 x := rfl

/-- The coderivative on test forms. -/
def deltaCc (n k : ℕ) : Cc n (k + 1) →ₗ[ℝ] Cc n k where
  toFun g := ⟨localAdjoint n k g.1, localAdjoint_mem_Cc g.2⟩
  map_add' g h := Subtype.ext (funext_of_pos
    (fun x hx => localAdjoint_add n k g.2.1.contDiffOn h.2.1.contDiffOn hx)
    (fun x hx => Cc.zero_outside (localAdjoint_mem_Cc (add_mem g.2 h.2)) x hx)
    (fun x hx => by
      change localAdjoint n k g.1 x + localAdjoint n k h.1 x = 0
      rw [Cc.zero_outside (localAdjoint_mem_Cc g.2) x hx,
        Cc.zero_outside (localAdjoint_mem_Cc h.2) x hx, add_zero]))
  map_smul' c g := Subtype.ext (funext_of_pos
    (fun x hx => localAdjoint_smul n k c g.2.1.contDiffOn hx)
    (fun x hx => Cc.zero_outside (localAdjoint_mem_Cc ((Cc n (k + 1)).smul_mem c g.2)) x hx)
    (fun x hx => by
      change c • localAdjoint n k g.1 x = 0
      rw [Cc.zero_outside (localAdjoint_mem_Cc g.2) x hx]
      exact fv_smul_zero _))

theorem deltaCc_coe (g : Cc n (k + 1)) : (deltaCc n k g).1 = localAdjoint n k g.1 := rfl

theorem deltaIn_coe_eq (Ω : Set Coordinates) (g : CcIn n (k + 1) Ω) :
    ((deltaIn n k Ω g).1 : Cc n k) = deltaCc n k g.1 := rfl

/-- The commutator of the coderivative with multiplication by a cutoff. -/
def commCc (c : Coordinates → ℝ) (hc : ContDiff ℝ ∞ c) : Cc n (k + 1) →ₗ[ℝ] Cc n k :=
  (mulCc c hc).comp (deltaCc n k) - (deltaCc n k).comp (mulCc c hc)

theorem commCc_apply (c : Coordinates → ℝ) (hc : ContDiff ℝ ∞ c) (g : Cc n (k + 1)) (x : Coordinates) :
    (commCc c hc g).1 x = c x • localAdjoint n k g.1 x - localAdjoint n k (fun y => c y • g.1 y) x := rfl

theorem tsupport_commCc (c : Coordinates → ℝ) (hc : ContDiff ℝ ∞ c) (g : Cc n (k + 1)) :
    tsupport (commCc c hc g).1 ⊆ tsupport c ∩ tsupport g.1 := by
  have hz : ∀ x, x ∉ tsupport c ∩ tsupport g.1 → (commCc c hc g).1 x = 0 := by
    intro x hx
    rw [commCc_apply]
    have hcw : tsupport (fun y => c y • g.1 y) ⊆ tsupport c ∩ tsupport g.1 :=
      subset_inter (tsupport_smul_subset_left c g.1) (tsupport_smul_subset_right c g.1)
    have h2 : localAdjoint n k (fun y => c y • g.1 y) x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hx (hcw ((tsupport_localAdjoint n k _) h)))
    rw [h2, sub_zero]
    by_cases hxc : x ∈ tsupport c
    · have hxg : x ∉ tsupport g.1 := fun h => hx ⟨hxc, h⟩
      have h1 : localAdjoint n k g.1 x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hxg ((tsupport_localAdjoint n k _) h))
      rw [h1]
      exact fv_smul_zero _
    · have h0 : c x = 0 := image_eq_zero_of_notMem_tsupport hxc
      rw [h0]
      exact ContinuousAlternatingMap.ext fun w => by simp
  apply closure_minimal _ ((isClosed_tsupport c).inter (isClosed_tsupport g.1))
  intro x hx
  by_contra hn
  exact hx (hz x hn)

/-- The normalized pullback by a group element on test forms. -/
def pullCc (γ : RealGL) : Cc n k →ₗ[ℝ] Cc n k where
  toFun g := ⟨actPull n k γ g.1, actPull_mem_Cc n k γ g.2⟩
  map_add' g h := Subtype.ext (funext_of_pos
    (fun x hx => actPull_add n k γ g.1 h.1 hx)
    (fun _ hx => actPull_of_notMem n k γ _ hx)
    (fun x hx => by
      change actPull n k γ g.1 x + actPull n k γ h.1 x = 0
      rw [actPull_of_notMem n k γ _ hx, actPull_of_notMem n k γ _ hx, add_zero]))
  map_smul' c g := Subtype.ext (funext_of_pos
    (fun x hx => actPull_smul n k γ c g.1 hx)
    (fun _ hx => actPull_of_notMem n k γ _ hx)
    (fun x hx => by
      change c • actPull n k γ g.1 x = 0
      rw [actPull_of_notMem n k γ _ hx]
      exact fv_smul_zero _))

theorem pullCc_coe (γ : RealGL) (g : Cc n k) : (pullCc γ g).1 = actPull n k γ g.1 := rfl

theorem pullCc_mul (γ δ : RealGL) (g : Cc n k) : pullCc γ (pullCc δ g) = pullCc (δ * γ) g :=
  Subtype.ext (funext_of_pos (fun _ hx => actPull_mul n k γ δ g.1 hx)
    (fun _ hx => actPull_of_notMem n k γ _ hx) (fun _ hx => actPull_of_notMem n k _ _ hx))

open Classical in
/-- The cutoff `c ∘ γ` transported by a group element, extended by zero off the positive
coordinates. -/
def cutAct (γ : RealGL) (c : Coordinates → ℝ) : Coordinates → ℝ :=
  fun y => if y ∈ positiveCoordinates then c (coordinateAction γ y) else 0

open Classical in
theorem cutAct_apply (γ : RealGL) (c : Coordinates → ℝ) {y : Coordinates}
    (hy : y ∈ positiveCoordinates) : cutAct γ c y = c (coordinateAction γ y) := ite_eq_left hy

theorem tsupport_cutAct_subset (γ : RealGL) {c : Coordinates → ℝ} (hcs : HasCompactSupport c)
    (hcp : tsupport c ⊆ positiveCoordinates) :
    tsupport (cutAct γ c) ⊆ coordinateAction γ⁻¹ '' tsupport c := by
  have hK := hcs.image_of_continuousOn ((contDiffOn_coordinateAction γ⁻¹).continuousOn.mono hcp)
  apply closure_minimal _ hK.isClosed
  intro y hy
  have hyp : y ∈ positiveCoordinates := by
    by_contra hn
    exact hy (by classical exact ite_eq_right hn)
  rw [Function.mem_support, cutAct_apply γ c hyp] at hy
  exact ⟨coordinateAction γ y, subset_tsupport _ hy, coordinateAction_inv_apply γ hyp⟩

theorem contDiff_cutAct (γ : RealGL) {c : Coordinates → ℝ} (hc : ContDiff ℝ ∞ c)
    (hcs : HasCompactSupport c) (hcp : tsupport c ⊆ positiveCoordinates) :
    ContDiff ℝ ∞ (cutAct γ c) := by
  have hon : ContDiffOn ℝ ∞ (cutAct γ c) positiveCoordinates := by
    have : ContDiffOn ℝ ∞ (fun y => c (coordinateAction γ y)) positiveCoordinates :=
      hc.comp_contDiffOn (contDiffOn_coordinateAction γ)
    exact this.congr fun y hy => cutAct_apply γ c hy
  refine contDiff_of_tsupport_subset isOpen_positiveCoordinates hon ?_
  rintro y hy
  obtain ⟨z, hz, rfl⟩ := tsupport_cutAct_subset γ hcs hcp hy
  exact coordinateAction_mem γ⁻¹ _ (hcp hz)

theorem hasCompactSupport_cutAct (γ : RealGL) {c : Coordinates → ℝ}
    (hcs : HasCompactSupport c) (hcp : tsupport c ⊆ positiveCoordinates) :
    HasCompactSupport (cutAct γ c) :=
  (hcs.image_of_continuousOn ((contDiffOn_coordinateAction γ⁻¹).continuousOn.mono hcp)).of_isClosed_subset
    (isClosed_tsupport _) (tsupport_cutAct_subset γ hcs hcp)

theorem cutAct_inv_apply (γ : RealGL) (c : Coordinates → ℝ) {x : Coordinates}
    (hx : x ∈ positiveCoordinates) : cutAct γ⁻¹ c (coordinateAction γ x) = c x := by
  rw [cutAct_apply _ _ (coordinateAction_mem γ x hx), coordinateAction_inv_apply γ hx]

/-- `ρ · γ^* g = γ^*((ρ ∘ γ⁻¹) · g)`. -/
theorem mulCc_pullCc (γ : RealGL) {c : Coordinates → ℝ} (hc : ContDiff ℝ ∞ c)
    (hcs : HasCompactSupport c) (hcp : tsupport c ⊆ positiveCoordinates) (g : Cc n k) :
    mulCc c hc (pullCc γ g) = pullCc γ (mulCc (cutAct γ⁻¹ c) (contDiff_cutAct γ⁻¹ hc hcs hcp) g) := by
  apply Subtype.ext
  funext x
  by_cases hx : x ∈ positiveCoordinates
  · change c x • actPull n k γ g.1 x = actPull n k γ (fun y => cutAct γ⁻¹ c y • g.1 y) x
    rw [actPull_fun_smul n k γ _ _ hx, cutAct_inv_apply γ c hx]
  · have h0 : (pullCc γ (mulCc (cutAct γ⁻¹ c) (contDiff_cutAct γ⁻¹ hc hcs hcp) g)).1 x = 0 :=
      actPull_of_notMem n k γ _ hx
    rw [h0]
    change c x • actPull n k γ g.1 x = 0
    rw [actPull_of_notMem n k γ _ hx]
    exact fv_smul_zero _

/-- The coderivative commutes with the pullback by a unimodular element. -/
theorem deltaCc_pullCc (γ : RealGL) (hγ : γ.val.det ^ 2 = 1) (g : Cc n (k + 1)) :
    deltaCc n k (pullCc γ g) = pullCc γ (deltaCc n k g) := by
  apply Subtype.ext
  exact funext_of_pos (fun x hx => localAdjoint_actPull n k γ hγ g.2.1.contDiffOn hx)
    (fun x hx => Cc.zero_outside (deltaCc n k (pullCc γ g)).2 x hx)
    (fun x hx => Cc.zero_outside (pullCc γ (deltaCc n k g)).2 x hx)

theorem commCc_pullCc (γ : RealGL) (hγ : γ.val.det ^ 2 = 1) {c : Coordinates → ℝ}
    (hc : ContDiff ℝ ∞ c) (hcs : HasCompactSupport c) (hcp : tsupport c ⊆ positiveCoordinates)
    (g : Cc n (k + 1)) :
    commCc c hc (pullCc γ g) =
      pullCc γ (commCc (cutAct γ⁻¹ c) (contDiff_cutAct γ⁻¹ hc hcs hcp) g) := by
  simp only [commCc, LinearMap.sub_apply, LinearMap.comp_apply]
  rw [deltaCc_pullCc γ hγ, mulCc_pullCc γ hc hcs hcp, mulCc_pullCc γ hc hcs hcp,
    deltaCc_pullCc γ hγ, map_sub]

theorem commCc_eq_symbol (c : Coordinates → ℝ) (hc : ContDiff ℝ ∞ c) (g : Cc n (k + 1))
    {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    (commCc c hc g).1 x = localAdjointSymbol n k c g.1 x := by
  rw [commCc_apply, localAdjoint_cutoff n k c g.1 hx (hc.differentiable (by simp) x)
    ((g.2.1.differentiable (by simp)) x)]
  exact ContinuousAlternatingMap.ext fun w => by simp

/-- Pointwise adjointness of the commutator symbol: the pairing of a form against the commutator
of a test form is the pairing of the forward symbol against the test form. -/
theorem pair_commCc (c : Coordinates → ℝ) (hc : ContDiff ℝ ∞ c) (f : Coordinates → FormValue n k)
    (g : Cc n (k + 1)) {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    coordinateDensity x * formPairing n k x (f x) ((commCc c hc g).1 x) =
      coordinateDensity x * formPairing n (k + 1) x (localDifferentialSymbol n k c f x) (g.1 x) := by
  rw [commCc_eq_symbol c hc g hx, ← weightedGram_pairing, ← weightedGram_pairing]
  have hG : (weightedGram n k x).mulVec (coordinates n k (localAdjointSymbol n k c g.1 x)) =
      fun l => matrixSymbolTranspose (fun d : Fin 5 => Pi.single d 1) (differentialCoefficients n k) c
        (metricDual (weightedGram n (k + 1)) (components n (k + 1) g.1)) l x := by
    have hu := (Matrix.isUnit_iff_isUnit_det _).mp (weightedGram_isUnit n k x hx)
    simp only [localAdjointSymbol, ContinuousLinearEquiv.apply_symm_apply, weightedSymbolTranspose]
    change (weightedGram n k x).mulVec ((weightedGram n k x)⁻¹.mulVec _) = _
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
  rw [hG]
  simp only [localDifferentialSymbol, ContinuousLinearEquiv.apply_symm_apply, dotProduct,
    matrixSymbol, matrixSymbolTranspose, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun d _ => ?_
  simp only [metricDual, components]
  ring

theorem contDiffOn_localDifferentialSymbol (c : Coordinates → ℝ) (hc : ContDiff ℝ ∞ c)
    {V : Set Coordinates} {f : Coordinates → FormValue n k} (hf : ContDiffOn ℝ ∞ f V) :
    ContDiffOn ℝ ∞ (localDifferentialSymbol n k c f) V := by
  have hdc : ∀ d : Fin 5, ContDiff ℝ ∞ (fun x => fderiv ℝ c x (Pi.single d 1)) := fun d =>
    (hc.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  change ContDiffOn ℝ ∞ ((coordinates n (k + 1)).symm ∘ (fun x => fun j => matrixSymbol
    (fun d : Fin 5 => Pi.single d 1) (differentialCoefficients n k) c (components n k f) j x)) V
  apply ContDiff.comp_contDiffOn (𝕜 := ℝ) (E := Coordinates)
    (F := Index n (k + 1) → ℝ) (G := FormValue n (k + 1)) (coordinates n (k + 1)).symm.contDiff
  apply contDiffOn_pi.mpr
  intro j
  unfold matrixSymbol
  exact ContDiffOn.sum fun i _ => ContDiffOn.sum fun d _ =>
    ((contDiff_const.mul (hdc d)).contDiffOn).mul (contDiffOn_components n k hf i)

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
