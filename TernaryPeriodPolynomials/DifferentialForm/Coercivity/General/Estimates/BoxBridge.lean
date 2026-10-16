module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Estimates.RegBasic
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Estimates.Descent
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Metric.AdjointTest
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Form.Recognition
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.LocalPotential
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.HilbertRegularCurrent
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Metric.TestSynthesis

@[expose] public section



/-! # General coercivity, Tier B (phase F): from functionals on test forms to coordinate currents

A linear functional `T` on the compactly supported smooth `k`-forms of the positive coordinates
defines, on every open `Ω ⊆ positiveCoordinates`, a form-valued coordinate current
`bridge T : FormWeak n k Ω` by testing against the inverse-Gram test forms
`metricDualTestRaw` of the weak-regularity library.  The coordinate exterior derivative of
`bridge T` is `bridge (T ∘ δ)`, and `bridge` of the functional `g ↦ ∫ ρ ⟨a, g⟩` of a continuous form
`a` is the regular current of `a`.

Formalized by Claude Sonnet 5.5. -/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open TernaryPoly TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceCharts
  TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
  TernaryPoly.PolynomialFormWeakSmooth TernaryPoly.PolynomialFormCoordinates
  TernaryPoly.SymmetricSpaceRiemannian
open Set MeasureTheory TernaryPoly.CompactCoordinateIntegration
open scoped ContDiff Distributions

variable {n k : ℕ}

theorem fv_add_smul (a b : ℝ) (A : FormValue n k) : (a + b) • A = a • A + b • A :=
  ContinuousAlternatingMap.ext fun v => by simp [add_smul]

/-- Test forms supported in a given set of coordinates. -/
def CcIn (n k : ℕ) (Ω : Set Coordinates) : Submodule ℝ (Cc n k) where
  carrier := {g | tsupport g.1 ⊆ Ω}
  zero_mem' := by simp
  add_mem' := by
    intro g h hg hh
    exact (tsupport_add g.1 h.1).trans (union_subset hg hh)
  smul_mem' := by
    intro c g hg
    exact (tsupport_smul_subset_right (fun _ : Coordinates => c) g.1).trans hg

theorem mem_CcIn {Ω : Set Coordinates} {g : Cc n k} : g ∈ CcIn n k Ω ↔ tsupport g.1 ⊆ Ω := Iff.rfl

/-- Multiplying a scalar test function by the inverse-Gram vector is a linear map into `CcIn`. -/
def mdtLin (Ω : TopologicalSpace.Opens Coordinates) (hΩ : (Ω : Set Coordinates) ⊆ positiveCoordinates)
    (i : Index n k) : 𝓓(Ω, ℝ) →ₗ[ℝ] CcIn n k (Ω : Set Coordinates) where
  toFun φ := ⟨⟨metricDualTestRaw n k Ω i φ, metricDualTestRaw_smooth n k Ω hΩ i φ,
    metricDualTestRaw_hasCompactSupport n k Ω i φ,
    (metricDualTestRaw_tsupport n k Ω i φ).trans (φ.tsupport_subset.trans hΩ)⟩,
    (metricDualTestRaw_tsupport n k Ω i φ).trans φ.tsupport_subset⟩
  map_add' φ ψ := Subtype.ext (Subtype.ext (funext fun x => by
    change metricDualTestRaw n k Ω i (φ + ψ) x = metricDualTestRaw n k Ω i φ x + metricDualTestRaw n k Ω i ψ x
    exact fv_add_smul _ _ _))
  map_smul' c φ := Subtype.ext (Subtype.ext (funext fun x => by
    change metricDualTestRaw n k Ω i (c • φ) x = c • metricDualTestRaw n k Ω i φ x
    exact (fv_smul_smul _ _ _).symm))

theorem mdtLin_coe (Ω : TopologicalSpace.Opens Coordinates)
    (hΩ : (Ω : Set Coordinates) ⊆ positiveCoordinates) (i : Index n k) (φ : 𝓓(Ω, ℝ)) :
    ((mdtLin Ω hΩ i φ : CcIn n k (Ω : Set Coordinates)).1.1 : Coordinates → FormValue n k) =
      metricDualTestRaw n k Ω i φ := rfl

/-- The form-valued coordinate current defined by a functional on test forms. -/
def bridge (Ω : TopologicalSpace.Opens Coordinates)
    (hΩ : (Ω : Set Coordinates) ⊆ positiveCoordinates) (T : CcIn n k (Ω : Set Coordinates) →ₗ[ℝ] ℝ) :
    FormWeak n k Ω :=
  formWeakOfCoordinates n k Ω (fun i => T.comp (mdtLin Ω hΩ i))

theorem bridge_coordinates (Ω : TopologicalSpace.Opens Coordinates)
    (hΩ : (Ω : Set Coordinates) ⊆ positiveCoordinates) (T : CcIn n k (Ω : Set Coordinates) →ₗ[ℝ] ℝ)
    (φ : 𝓓(Ω, ℝ)) (i : Index n k) :
    coordinates n k (bridge Ω hΩ T φ) i = T (mdtLin Ω hΩ i φ) := by
  change coordinates n k ((coordinates n k).symm _) i = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  rfl

/-- The coderivative as a linear map of test forms supported in `Ω`. -/
def deltaIn (n k : ℕ) (Ω : Set Coordinates) : CcIn n (k + 1) Ω →ₗ[ℝ] CcIn n k Ω where
  toFun g := ⟨⟨localAdjoint n k g.1.1, localAdjoint_mem_Cc g.1.2⟩,
    (tsupport_localAdjoint n k g.1.1).trans g.2⟩
  map_add' g h := Subtype.ext (Subtype.ext (funext_of_pos
    (fun x hx => localAdjoint_add n k g.1.2.1.contDiffOn h.1.2.1.contDiffOn hx)
    (fun x hx => Cc.zero_outside (localAdjoint_mem_Cc (add_mem g.1.2 h.1.2)) x hx)
    (fun x hx => by
      change localAdjoint n k g.1.1 x + localAdjoint n k h.1.1 x = 0
      rw [Cc.zero_outside (localAdjoint_mem_Cc g.1.2) x hx,
        Cc.zero_outside (localAdjoint_mem_Cc h.1.2) x hx, add_zero])))
  map_smul' c g := Subtype.ext (Subtype.ext (funext_of_pos
    (fun x hx => localAdjoint_smul n k c g.1.2.1.contDiffOn hx)
    (fun x hx => Cc.zero_outside (localAdjoint_mem_Cc ((Cc n (k + 1)).smul_mem c g.1.2)) x hx)
    (fun x hx => by
      change c • localAdjoint n k g.1.1 x = 0
      rw [Cc.zero_outside (localAdjoint_mem_Cc g.1.2) x hx]
      exact fv_smul_zero _)))

@[simp] theorem deltaIn_coe {Ω : Set Coordinates} (g : CcIn n (k + 1) Ω) :
    ((deltaIn n k Ω g : CcIn n k Ω).1.1 : Coordinates → FormValue n k) = localAdjoint n k g.1.1 := rfl

theorem deltaIn_mdtLin (Ω : TopologicalSpace.Opens Coordinates)
    (hΩ : (Ω : Set Coordinates) ⊆ positiveCoordinates) (j : Index n (k + 1)) (φ : 𝓓(Ω, ℝ)) :
    deltaIn n k (Ω : Set Coordinates) (mdtLin Ω hΩ j φ) = ∑ i : Index n k, mdtLin Ω hΩ i
      (scalarMatrixTransposeTest Ω (fun d : Fin 5 => Pi.single d 1)
        (fun j i d => symbolMatrix n k d j i) j φ i) := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  have h1 : ((∑ i : Index n k, mdtLin Ω hΩ i
      (scalarMatrixTransposeTest Ω (fun d : Fin 5 => Pi.single d 1)
        (fun j i d => symbolMatrix n k d j i) j φ i) : CcIn n k (Ω : Set Coordinates)).1.1 :
        Coordinates → FormValue n k) x =
      ∑ i : Index n k, metricDualTestRaw n k Ω i
        (scalarMatrixTransposeTest Ω (fun d : Fin 5 => Pi.single d 1)
          (fun j i d => symbolMatrix n k d j i) j φ i) x := by
    rw [Submodule.coe_sum, Submodule.coe_sum, Finset.sum_apply]
    rfl
  rw [h1]
  exact congrFun (localAdjoint_metricDualTestRaw n k Ω hΩ j φ) x

theorem bridge_exterior_coordinates_right (Ω : TopologicalSpace.Opens Coordinates)
    (hΩ : (Ω : Set Coordinates) ⊆ positiveCoordinates) (T : CcIn n k (Ω : Set Coordinates) →ₗ[ℝ] ℝ)
    (φ : 𝓓(Ω, ℝ)) (j : Index n (k + 1)) :
    coordinates n (k + 1) (bridge Ω hΩ (T.comp (deltaIn n k (Ω : Set Coordinates))) φ) j =
    ∑ i : Index n k, ∑ d : Fin 5, -(symbolMatrix n k d j i) *
      T (mdtLin Ω hΩ i (TestFunction.lineDerivCLM ℝ (Pi.single d 1) φ)) := by
  rw [bridge_coordinates, LinearMap.comp_apply, deltaIn_mdtLin, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [scalarMatrixTransposeTest, map_sum, map_smul, smul_eq_mul]

theorem bridge_exterior_entry (Ω : TopologicalSpace.Opens Coordinates)
    (hΩ : (Ω : Set Coordinates) ⊆ positiveCoordinates) (T : CcIn n k (Ω : Set Coordinates) →ₗ[ℝ] ℝ)
    (d : Fin 5) (j : Index n (k + 1)) (i : Index n k) (ψ : 𝓓(Ω, ℝ)) :
    symbolMatrix n k d j i * coordinates n k (-bridge Ω hΩ T ψ) i =
      -symbolMatrix n k d j i * T (mdtLin Ω hΩ i ψ) := by
  rw [ContinuousLinearEquiv.map_neg, Pi.neg_apply, bridge_coordinates]
  ring

theorem bridge_exterior_term (Ω : TopologicalSpace.Opens Coordinates)
    (hΩ : (Ω : Set Coordinates) ⊆ positiveCoordinates) (T : CcIn n k (Ω : Set Coordinates) →ₗ[ℝ] ℝ)
    (d : Fin 5) (j : Index n (k + 1)) (ψ : 𝓓(Ω, ℝ)) :
    coordinates n (k + 1) (symbol n k d (-bridge Ω hΩ T ψ)) j =
      ∑ i : Index n k, -symbolMatrix n k d j i * T (mdtLin Ω hΩ i ψ) := by
  rw [← symbolMatrix_apply, Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl fun i _ => bridge_exterior_entry Ω hΩ T d j i ψ

theorem bridge_exterior_coordinates_left (Ω : TopologicalSpace.Opens Coordinates)
    (hΩ : (Ω : Set Coordinates) ⊆ positiveCoordinates) (T : CcIn n k (Ω : Set Coordinates) →ₗ[ℝ] ℝ)
    (φ : 𝓓(Ω, ℝ)) (j : Index n (k + 1)) :
    coordinates n (k + 1) (formWeakExterior n k Ω (bridge Ω hΩ T) φ) j =
    ∑ d : Fin 5, ∑ i : Index n k, -(symbolMatrix n k d j i) *
      T (mdtLin Ω hΩ i (TestFunction.lineDerivCLM ℝ (Pi.single d 1) φ)) := by
  rw [formWeakExterior_apply, TernaryPoly.PolynomialFormCoordinates.coordinates_sum, Finset.sum_apply]
  exact Finset.sum_congr rfl fun d _ => bridge_exterior_term Ω hΩ T d j _

theorem bridge_exterior (Ω : TopologicalSpace.Opens Coordinates)
    (hΩ : (Ω : Set Coordinates) ⊆ positiveCoordinates) (T : CcIn n k (Ω : Set Coordinates) →ₗ[ℝ] ℝ) :
    formWeakExterior n k Ω (bridge Ω hΩ T) = bridge Ω hΩ (T.comp (deltaIn n k (Ω : Set Coordinates))) := by
  apply LinearMap.ext
  intro φ
  apply (coordinates n (k + 1)).injective
  funext j
  rw [bridge_exterior_coordinates_right Ω hΩ T φ j, bridge_exterior_coordinates_left Ω hΩ T φ j,
    Finset.sum_comm]

theorem bridge_regular (Ω : TopologicalSpace.Opens Coordinates)
    (hΩ : (Ω : Set Coordinates) ⊆ positiveCoordinates) (T : CcIn n k (Ω : Set Coordinates) →ₗ[ℝ] ℝ)
    (a : Coordinates → FormValue n k) (ha : ContinuousOn a Ω)
    (hT : ∀ g : CcIn n k (Ω : Set Coordinates),
      T g = ∫ x, coordinateDensity x * formPairing n k x (a x) (g.1.1 x)) :
    bridge Ω hΩ T = valuedRegularCurrent volume Ω a ha := by
  have h2 : valuedRegularCurrent volume Ω a ha = formWeakOfCoordinates n k Ω
      (formWeakCoordinates n k Ω (valuedRegularCurrent volume Ω a ha)) :=
    (formWeakOfCoordinates_coordinates n k Ω _).symm
  refine Eq.trans (congrArg (formWeakOfCoordinates n k Ω) (funext fun i => ?_)) h2.symm
  rw [formWeakCoordinates_regular]
  apply LinearMap.ext
  intro φ
  rw [LinearMap.comp_apply, hT]
  change _ = ∫ x, coordinates n k (a x) i * φ x ∂volume
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  exact metricDualTestRaw_pairing_all n k Ω hΩ i φ (a x) x

/-! ### The inverse: from currents to functionals -/

/-- The scalar coefficient `(G ∘ g)_j` of a test form against the weighted Gram matrix. -/
def wcoeff (j : Index n k) (g : Coordinates → FormValue n k) (x : Coordinates) : ℝ :=
  ((weightedGram n k x).mulVec (coordinates n k (g x))) j

theorem wcoeff_eq_metricDual (j : Index n k) (g : Coordinates → FormValue n k) :
    wcoeff j g = metricDual (weightedGram n k) (components n k g) j := rfl

theorem tsupport_wcoeff_subset (j : Index n k) (g : Coordinates → FormValue n k) :
    tsupport (wcoeff j g) ⊆ tsupport g := by
  apply closure_mono
  intro x hx
  rw [Function.mem_support] at hx ⊢
  intro h0
  apply hx
  simp only [wcoeff, h0, ContinuousLinearEquiv.map_zero, Matrix.mulVec_zero, Pi.zero_apply]

theorem contDiff_wcoeff (j : Index n k) {g : Coordinates → FormValue n k}
    (hg : ContDiff ℝ ∞ g) (hs : tsupport g ⊆ positiveCoordinates) :
    ContDiff ℝ ∞ (wcoeff j g) := by
  have hon : ContDiffOn ℝ ∞ (wcoeff j g) positiveCoordinates := by
    have hG := contDiffOn_pi.mp (contDiffOn_weightedGram n k) j
    unfold wcoeff
    simp only [Matrix.mulVec, dotProduct]
    exact ContDiffOn.sum fun l _ => (contDiffOn_pi.mp hG l).mul
      (contDiffOn_components n k hg.contDiffOn l)
  exact contDiff_of_tsupport_subset isOpen_positiveCoordinates hon
    ((tsupport_wcoeff_subset j g).trans hs)

/-- The scalar test `(G ∘ g)_j`. -/
def wcoeffTest (Ω : TopologicalSpace.Opens Coordinates) (j : Index n k)
    (g : CcIn n k (Ω : Set Coordinates)) : 𝓓(Ω, ℝ) :=
  ⟨wcoeff j g.1.1, contDiff_wcoeff j g.1.2.1 (g.1.2.2.2),
    g.1.2.2.1.of_isClosed_subset (isClosed_tsupport _) (tsupport_wcoeff_subset j g.1.1),
    (tsupport_wcoeff_subset j g.1.1).trans g.2⟩

/-- The coefficient tests as a linear map. -/
def wcoeffLin (Ω : TopologicalSpace.Opens Coordinates) (j : Index n k) :
    CcIn n k (Ω : Set Coordinates) →ₗ[ℝ] 𝓓(Ω, ℝ) where
  toFun g := wcoeffTest Ω j g
  map_add' g h := TestFunction.ext fun x => by
    change wcoeff j (g.1.1 + h.1.1) x = wcoeff j g.1.1 x + wcoeff j h.1.1 x
    simp [wcoeff, Matrix.mulVec_add]
  map_smul' c g := TestFunction.ext fun x => by
    change wcoeff j (c • g.1.1) x = c * wcoeff j g.1.1 x
    simp [wcoeff, Matrix.mulVec_smul]

theorem wcoeffLin_apply (Ω : TopologicalSpace.Opens Coordinates) (j : Index n k)
    (g : CcIn n k (Ω : Set Coordinates)) (x : Coordinates) :
    wcoeffLin Ω j g x = wcoeff j g.1.1 x := rfl

theorem wcoeffLin_mdtLin (Ω : TopologicalSpace.Opens Coordinates)
    (hΩ : (Ω : Set Coordinates) ⊆ positiveCoordinates) (j i : Index n k) (ψ : 𝓓(Ω, ℝ)) :
    wcoeffLin Ω j (mdtLin Ω hΩ i ψ) = if j = i then ψ else 0 := by
  apply TestFunction.ext
  intro x
  have h := congrFun (congrFun (metricDualTestRaw_metricDual n k Ω hΩ i ψ) j) x
  rw [wcoeffLin_apply]
  change metricDual (weightedGram n k) (components n k (metricDualTestRaw n k Ω i ψ)) j x = _
  rw [h]
  by_cases hji : j = i
  · subst hji; simp
  · simp [hji]

theorem sum_mdtLin_wcoeffLin (Ω : TopologicalSpace.Opens Coordinates)
    (hΩ : (Ω : Set Coordinates) ⊆ positiveCoordinates) (g : CcIn n k (Ω : Set Coordinates)) :
    ∑ j : Index n k, mdtLin Ω hΩ j (wcoeffLin Ω j g) = g := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  have h1 : ((∑ j : Index n k, mdtLin Ω hΩ j (wcoeffLin Ω j g) : CcIn n k (Ω : Set Coordinates)).1.1 :
      Coordinates → FormValue n k) x =
      ∑ j : Index n k, metricDualTestRaw n k Ω j (wcoeffLin Ω j g) x := by
    rw [Submodule.coe_sum, Submodule.coe_sum, Finset.sum_apply]
    rfl
  rw [h1]
  by_cases hx : x ∈ positiveCoordinates
  · apply (coordinates n k).injective
    rw [metricDualTestRaw_sum_coordinates]
    have hG := (Matrix.isUnit_iff_isUnit_det _).mp (weightedGram_isUnit n k x hx)
    change (weightedGram n k x)⁻¹.mulVec ((weightedGram n k x).mulVec (coordinates n k (g.1.1 x))) = _
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hG, Matrix.one_mulVec]
  · rw [Cc.zero_outside g.1.2 x hx]
    apply Finset.sum_eq_zero
    intro j _
    have : wcoeffLin Ω j g x = 0 := by
      rw [wcoeffLin_apply]
      exact image_eq_zero_of_notMem_tsupport (fun ht => hx (g.1.2.2.2 (tsupport_wcoeff_subset j g.1.1 ht)))
    change (wcoeffLin Ω j g x) • metricDualTestVector n k j x = 0
    rw [this]
    exact ContinuousAlternatingMap.ext fun w => by simp

/-- The functional on test forms defined by a coordinate current. -/
def unbridge (Ω : TopologicalSpace.Opens Coordinates) (W : FormWeak n k Ω) :
    CcIn n k (Ω : Set Coordinates) →ₗ[ℝ] ℝ where
  toFun g := ∑ j : Index n k, coordinates n k (W (wcoeffLin Ω j g)) j
  map_add' g h := by
    simp only [map_add, Pi.add_apply, Finset.sum_add_distrib]
  map_smul' c g := by
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]

theorem unbridge_apply (Ω : TopologicalSpace.Opens Coordinates) (W : FormWeak n k Ω)
    (g : CcIn n k (Ω : Set Coordinates)) :
    unbridge Ω W g = ∑ j : Index n k, coordinates n k (W (wcoeffLin Ω j g)) j := rfl

theorem unbridge_mdtLin (Ω : TopologicalSpace.Opens Coordinates)
    (hΩ : (Ω : Set Coordinates) ⊆ positiveCoordinates) (W : FormWeak n k Ω) (i : Index n k)
    (ψ : 𝓓(Ω, ℝ)) : unbridge Ω W (mdtLin Ω hΩ i ψ) = coordinates n k (W ψ) i := by
  rw [unbridge_apply]
  simp only [wcoeffLin_mdtLin]
  rw [Finset.sum_eq_single i]
  · simp only [↓reduceIte]
  · intro j _ hji
    simp only [hji, ↓reduceIte, LinearMap.map_zero, ContinuousLinearEquiv.map_zero]
    rfl
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem unbridge_bridge (Ω : TopologicalSpace.Opens Coordinates)
    (hΩ : (Ω : Set Coordinates) ⊆ positiveCoordinates) (T : CcIn n k (Ω : Set Coordinates) →ₗ[ℝ] ℝ) :
    unbridge Ω (bridge Ω hΩ T) = T := by
  apply LinearMap.ext
  intro g
  rw [unbridge_apply]
  simp only [bridge_coordinates]
  rw [← map_sum, sum_mdtLin_wcoeffLin]

theorem bridge_unbridge (Ω : TopologicalSpace.Opens Coordinates)
    (hΩ : (Ω : Set Coordinates) ⊆ positiveCoordinates) (W : FormWeak n k Ω) :
    bridge Ω hΩ (unbridge Ω W) = W := by
  apply LinearMap.ext
  intro φ
  apply (coordinates n k).injective
  funext i
  rw [bridge_coordinates, unbridge_mdtLin]

theorem unbridge_exterior (Ω : TopologicalSpace.Opens Coordinates)
    (hΩ : (Ω : Set Coordinates) ⊆ positiveCoordinates) (W : FormWeak n k Ω) :
    unbridge Ω (formWeakExterior n k Ω W) =
      (unbridge Ω W).comp (deltaIn n k (Ω : Set Coordinates)) := by
  have h1 := bridge_exterior Ω hΩ (unbridge Ω W)
  rw [bridge_unbridge Ω hΩ W] at h1
  rw [h1, unbridge_bridge]

theorem unbridge_regular (Ω : TopologicalSpace.Opens Coordinates)
    (a : Coordinates → FormValue n k) (ha : ContinuousOn a Ω)
    (g : CcIn n k (Ω : Set Coordinates)) :
    unbridge Ω (valuedRegularCurrent volume Ω a ha) g =
      ∫ x, coordinateDensity x * formPairing n k x (a x) (g.1.1 x) := by
  have hcoord : ∀ j : Index n k, ContinuousOn (fun x => coordinates n k (a x) j) Ω := fun j =>
    (((ContinuousLinearMap.proj j).comp (coordinates n k).toContinuousLinearMap).continuous.comp_continuousOn ha)
  have hint : ∀ j : Index n k, Integrable (fun x => coordinates n k (a x) j * wcoeffLin Ω j g x) := by
    intro j
    have := valuedRegular_test_integrable volume Ω (fun x => coordinates n k (a x) j) (hcoord j)
      (wcoeffLin Ω j g)
    exact this.congr (Filter.Eventually.of_forall fun x => (smul_eq_mul _ _).trans (mul_comm _ _))
  have hj : ∀ j : Index n k, coordinates n k (valuedRegularCurrent volume Ω a ha (wcoeffLin Ω j g)) j =
      ∫ x, coordinates n k (a x) j * wcoeffLin Ω j g x := by
    intro j
    have := congrArg (fun T : ScalarWeak Ω => T (wcoeffLin Ω j g)) (formWeakCoordinates_regular n k Ω a ha j)
    exact this
  rw [unbridge_apply]
  simp only [hj]
  rw [← integral_finsetSum _ fun j _ => hint j]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  have h := weightedGram_pairing n k x (a x) (g.1.1 x)
  show ∑ i, coordinates n k (a x) i * wcoeff i g.1.1 x = coordinateDensity x * formPairing n k x (a x) (g.1.1 x)
  rw [← h, dotProduct]
  rfl

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
