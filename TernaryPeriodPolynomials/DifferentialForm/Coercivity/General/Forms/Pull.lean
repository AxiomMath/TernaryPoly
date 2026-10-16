module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Measure.SpaceVolume
public import TernaryPeriodPolynomials.DifferentialForm.AdjointDeckCovariance
public import TernaryPeriodPolynomials.DifferentialForm.GeometricEnergy.RealPullback
public import TernaryPeriodPolynomials.DifferentialForm.GeometricEnergy.Compact
public import TernaryPeriodPolynomials.DifferentialForm.Connection.Energy.CurrentDeck
public import TernaryPeriodPolynomials.SymmetricSpace.Riemannian.DeckIntegral

@[expose] public section


/-! Group-level ports of the deck-group covariance layer to an arbitrary `g : RealGL`.

Every lemma of the original library about `DeckGroup` that is used in the quotient calculus (inverse laws
and density change of variables, normalized pullback `deckPull`, covariance of the exterior
derivative, the local adjoint, the symmetric exterior and contraction operators and the energy
current) is restated for an arbitrary `g : RealGL`, with the hypothesis `g.val.det ^ 2 = 1` where
the coefficient metric is involved. Nothing here mentions a subgroup: the subgroup `Γ` enters only
in `Forms/Basic`, by instantiating `g := (γ : RealGL)`.

Formalized by Claude Sonnet 5.5. -/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open TernaryPoly TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceCharts
  TernaryPoly.SymmetricSpaceCovering TernaryPoly.SymmetricSpaceTraceMetric
  TernaryPoly.SymmetricSpaceRiemannian TernaryPoly.SmoothCoveringDeRham
  TernaryPoly.SmoothLocalDeRham TernaryPoly.PolynomialCoefficientMetric
  TernaryPoly.PolynomialFormMetric TernaryPoly.PolynomialFormConnection
  TernaryPoly.PolynomialFormGeometricEnergy TernaryPoly.PolynomialFormCoordinates
open TernaryPoly.CompactCoordinateIntegration
open Set Filter MeasureTheory
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

/-! ### Inverse laws of the coordinate action (group laws are in `Cover/Coordinates`) -/

theorem coordinateAction_inv_apply (g : RealGL) {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    coordinateAction g⁻¹ (coordinateAction g x) = x := by
  rw [← coordinateAction_mul g⁻¹ g hx, inv_mul_cancel, coordinateAction_one hx]

/-- The derivative of the coordinate action composed with that of its inverse is the identity. -/
theorem actionDerivative_inverse (g : RealGL) {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    (fderiv ℝ (coordinateAction g⁻¹) (coordinateAction g x)).comp (fderiv ℝ (coordinateAction g) x) =
      ContinuousLinearMap.id ℝ Coordinates := by
  have he : (coordinateAction g⁻¹ ∘ coordinateAction g) =ᶠ[𝓝 x] id := by
    filter_upwards [isOpen_positiveCoordinates.mem_nhds hx] with y hy
    exact coordinateAction_inv_apply g hy
  have hg := ((contDiffOn_coordinateAction g x hx).contDiffAt
    (isOpen_positiveCoordinates.mem_nhds hx)).differentiableAt (by simp)
  have hi := ((contDiffOn_coordinateAction g⁻¹ (coordinateAction g x)
    (coordinateAction_mem g x hx)).contDiffAt
    (isOpen_positiveCoordinates.mem_nhds (coordinateAction_mem g x hx))).differentiableAt (by simp)
  rw [← fderiv_comp x hi hg, he.fderiv_eq, fderiv_id]

/-! ### Change of variables -/

/-- The coordinate action of `g` as an open partial homeomorphism of the positive coordinates. -/
def actionCoordinates (g : RealGL) : OpenPartialHomeomorph Coordinates Coordinates where
  toFun := coordinateAction g
  invFun := coordinateAction g⁻¹
  source := positiveCoordinates
  target := positiveCoordinates
  map_source' := fun _ hx => coordinateAction_mem g _ hx
  map_target' := fun _ hx => coordinateAction_mem g⁻¹ _ hx
  left_inv' := fun _ hx => coordinateAction_inv_apply g hx
  right_inv' := by
    intro x hx
    have h := coordinateAction_inv_apply g⁻¹ hx
    rwa [inv_inv] at h
  open_source := isOpen_positiveCoordinates
  open_target := isOpen_positiveCoordinates
  continuousOn_toFun := (contDiffOn_coordinateAction g).continuousOn
  continuousOn_invFun := (contDiffOn_coordinateAction g⁻¹).continuousOn

/-- Density-weighted change of variables on the positive coordinates for any `g`. -/
theorem integral_coordinateDensity_action (g : RealGL) (f : Coordinates → ℝ) :
    ∫ x in positiveCoordinates, coordinateDensity x * f (coordinateAction g x) =
      ∫ x in positiveCoordinates, coordinateDensity x * f x := by
  have hd (x : Coordinates) (hx : x ∈ positiveCoordinates) :
      HasFDerivWithinAt (coordinateAction g) (fderiv ℝ (coordinateAction g) x)
        positiveCoordinates x :=
    (((contDiffOn_coordinateAction g x hx).contDiffAt
      (isOpen_positiveCoordinates.mem_nhds hx)).differentiableAt
      (by simp)).hasFDerivAt.hasFDerivWithinAt
  have he := integral_image_eq_integral_abs_det_fderiv_smul volume
    isOpen_positiveCoordinates.measurableSet hd (coordinateAction_injOn g)
    (fun x => coordinateDensity x * f x)
  have himage : coordinateAction g '' positiveCoordinates = positiveCoordinates :=
    (actionCoordinates g).image_source_eq_target
  rw [himage] at he
  refine (setIntegral_congr_fun isOpen_positiveCoordinates.measurableSet (fun x hx => ?_)).trans
    he.symm
  change coordinateDensity x * f (coordinateAction g x) =
    |(fderiv ℝ (coordinateAction g) x).det| *
      (coordinateDensity (coordinateAction g x) * f (coordinateAction g x))
  rw [coordinateDensity_action g x hx, mul_assoc]

/-! ### Normalized pullback -/

theorem realCoefficientMap_inverse' (n : ℕ) (g : RealGL) (p : Coefficients n) :
    realCoefficientMap n g⁻¹ (realCoefficientMap n g p) = p := by
  have h := realCoefficientMap_inverse n g⁻¹ p
  rwa [inv_inv] at h

theorem coefficientFormMap_comp {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L M : F →L[ℝ] F) (k : ℕ) (w : Coordinates [⋀^Fin k]→L[ℝ] F) :
    coefficientFormMap L k (coefficientFormMap M k w) = coefficientFormMap (L.comp M) k w := by
  ext v
  simp [coefficientFormMap]

/-- Pull back along the coordinate action of `g` and undo its coefficient action; zero outside the
positive coordinates. Group-level version of `TernaryPoly.PolynomialFormCoordinates.deckPull`. -/
def actPull (n k : ℕ) (g : RealGL) (w : Coordinates → FormValue n k) :
    Coordinates → FormValue n k :=
  positiveCoordinates.indicator
    (coefficientRaw (realCoefficientMap n g⁻¹) (pullRaw (coordinateAction g) w))

theorem actPull_apply (n k : ℕ) (g : RealGL) (w : Coordinates → FormValue n k)
    {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    actPull n k g w x = realFormPullback n k g x (w (coordinateAction g x)) :=
  indicator_of_mem hx _

theorem actPull_of_notMem (n k : ℕ) (g : RealGL) (w : Coordinates → FormValue n k)
    {x : Coordinates} (hx : x ∉ positiveCoordinates) : actPull n k g w x = 0 :=
  indicator_of_notMem hx _

theorem contDiffOn_actPull (n k : ℕ) (g : RealGL) {w : Coordinates → FormValue n k}
    (hw : ContDiffOn ℝ ∞ w positiveCoordinates) :
    ContDiffOn ℝ ∞ (actPull n k g w) positiveCoordinates := by
  have h := coefficientRaw_smooth (realCoefficientMap n g⁻¹)
    (pullRaw_smooth isOpen_positiveCoordinates (contDiffOn_coordinateAction g) hw
      (fun _ hx => coordinateAction_mem g _ hx))
  exact h.congr (fun x hx => actPull_apply n k g w hx)

theorem actPull_equation (n k : ℕ) (g : RealGL) (w : Coordinates → FormValue n k)
    {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    coefficientFormMap (realCoefficientMap n g) k (actPull n k g w x) =
      (w (coordinateAction g x)).compContinuousLinearMap (fderiv ℝ (coordinateAction g) x) := by
  rw [actPull_apply n k g w hx]
  exact (realFormPullback_spec n k g x _).symm

theorem formPairing_actPull (n k : ℕ) (g : RealGL) (hg : g.val.det ^ 2 = 1)
    (w z : Coordinates → FormValue n k) {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    formPairing n k x (actPull n k g w x) (actPull n k g z x) =
      formPairing n k (coordinateAction g x) (w (coordinateAction g x))
        (z (coordinateAction g x)) :=
  (formPairing_real n k g hg x hx _ _ _ _ (actPull_equation n k g w hx).symm
    (actPull_equation n k g z hx).symm).symm

/-- The support transports into the inverse image of the original compact support. -/
theorem tsupport_actPull (n k : ℕ) (g : RealGL) (w : Coordinates → FormValue n k)
    (hc : HasCompactSupport w) (hs : tsupport w ⊆ positiveCoordinates) :
    tsupport (actPull n k g w) ⊆ coordinateAction g⁻¹ '' tsupport w := by
  have hK := hc.image_of_continuousOn ((contDiffOn_coordinateAction g⁻¹).continuousOn.mono hs)
  apply closure_minimal _ hK.isClosed
  intro x hx
  have hxp : x ∈ positiveCoordinates := by
    by_contra hn
    exact hx (actPull_of_notMem n k g w hn)
  have hval : w (coordinateAction g x) ≠ 0 := by
    intro hzero
    apply hx
    rw [actPull_apply n k g w hxp, hzero]
    ext v
    simp [realFormPullback, coefficientFormMap]
  exact ⟨coordinateAction g x, subset_tsupport _ hval, coordinateAction_inv_apply g hxp⟩

theorem hasCompactSupport_actPull (n k : ℕ) (g : RealGL) (w : Coordinates → FormValue n k)
    (hc : HasCompactSupport w) (hs : tsupport w ⊆ positiveCoordinates) :
    HasCompactSupport (actPull n k g w) :=
  (hc.image_of_continuousOn ((contDiffOn_coordinateAction g⁻¹).continuousOn.mono hs)).of_isClosed_subset
    (isClosed_tsupport _) (tsupport_actPull n k g w hc hs)

theorem tsupport_actPull_positive (n k : ℕ) (g : RealGL) (w : Coordinates → FormValue n k)
    (hc : HasCompactSupport w) (hs : tsupport w ⊆ positiveCoordinates) :
    tsupport (actPull n k g w) ⊆ positiveCoordinates := by
  rintro x hx
  obtain ⟨y, hy, rfl⟩ := tsupport_actPull n k g w hc hs hx
  exact coordinateAction_mem g⁻¹ _ (hs hy)

theorem contDiff_actPull (n k : ℕ) (g : RealGL) {w : Coordinates → FormValue n k}
    (hw : ContDiffOn ℝ ∞ w positiveCoordinates) (hc : HasCompactSupport w)
    (hs : tsupport w ⊆ positiveCoordinates) : ContDiff ℝ ∞ (actPull n k g w) :=
  contDiff_of_tsupport_subset isOpen_positiveCoordinates (contDiffOn_actPull n k g hw)
    (tsupport_actPull_positive n k g w hc hs)

/-- Pulling back by `g` and then by `g⁻¹` recovers the form on the positive coordinates. -/
theorem actPull_inverse (n k : ℕ) (g : RealGL) (w : Coordinates → FormValue n k)
    {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    actPull n k g (actPull n k g⁻¹ w) x = w x := by
  rw [actPull_apply n k g _ hx, actPull_apply n k g⁻¹ w (coordinateAction_mem g _ hx)]
  apply ContinuousAlternatingMap.ext
  intro v
  change realCoefficientMap n g⁻¹ (realCoefficientMap n g⁻¹⁻¹
    (w (coordinateAction g⁻¹ (coordinateAction g x)) (fun i =>
      (fderiv ℝ (coordinateAction g⁻¹) (coordinateAction g x))
        ((fderiv ℝ (coordinateAction g) x) (v i))))) = w x v
  rw [inv_inv, realCoefficientMap_inverse' n g, coordinateAction_inv_apply g hx]
  apply congrArg (w x)
  funext i
  exact congrArg (fun L : Coordinates →L[ℝ] Coordinates => L (v i)) (actionDerivative_inverse g hx)

/-- The exterior differential commutes with the normalized pullback on the positive coordinates. -/
theorem extDeriv_actPull (n k : ℕ) (g : RealGL) {w : Coordinates → FormValue n k}
    (hw : ContDiffOn ℝ ∞ w positiveCoordinates) {x : Coordinates}
    (hx : x ∈ positiveCoordinates) :
    extDeriv (actPull n k g w) x = actPull n (k + 1) g (extDeriv w) x := by
  have he : actPull n k g w =ᶠ[𝓝 x]
      coefficientRaw (realCoefficientMap n g⁻¹) (pullRaw (coordinateAction g) w) := by
    filter_upwards [isOpen_positiveCoordinates.mem_nhds hx] with y hy
    exact indicator_of_mem hy _
  have hd := ((pullRaw_smooth isOpen_positiveCoordinates (contDiffOn_coordinateAction g) hw
    (fun _ hy => coordinateAction_mem g _ hy)) x hx).contDiffAt
    (isOpen_positiveCoordinates.mem_nhds hx)
  rw [he.extDeriv_eq, extDeriv_coefficientRaw _ (hd.differentiableAt (by simp)),
    extDeriv_pullRaw ((contDiffOn_coordinateAction g x hx).contDiffAt
      (isOpen_positiveCoordinates.mem_nhds hx))
      (((hw _ (coordinateAction_mem g _ hx)).contDiffAt
        (isOpen_positiveCoordinates.mem_nhds (coordinateAction_mem g _ hx))).differentiableAt
        (by simp)),
    actPull_apply n (k + 1) g (extDeriv w) hx]
  rfl

/-! ### Local integrals and the local adjoint -/

theorem localIntegral_actPull (n k : ℕ) (g : RealGL) (hg : g.val.det ^ 2 = 1)
    (f z : Coordinates → FormValue n k) (hf : ∀ x ∉ positiveCoordinates, f x = 0) :
    localIntegral n k (actPull n k g f) (actPull n k g z) = localIntegral n k f z := by
  rw [localIntegral_eq_setIntegral n k _ _ (fun x hx => actPull_of_notMem n k g f hx),
    localIntegral_eq_setIntegral n k f z hf]
  calc
    _ = ∫ x in positiveCoordinates, coordinateDensity x *
        formPairing n k (coordinateAction g x) (f (coordinateAction g x))
          (z (coordinateAction g x)) := by
      apply setIntegral_congr_fun isOpen_positiveCoordinates.measurableSet
      intro x hx
      dsimp only
      rw [formPairing_actPull n k g hg f z hx]
    _ = _ := integral_coordinateDensity_action g (fun x => formPairing n k x (f x) (z x))

theorem localIntegral_actPull_right (n k : ℕ) (g : RealGL) (hg : g.val.det ^ 2 = 1)
    (f z : Coordinates → FormValue n k) (hf : ∀ x ∉ positiveCoordinates, f x = 0) :
    localIntegral n k f (actPull n k g z) = localIntegral n k (actPull n k g⁻¹ f) z := by
  have he := localIntegral_congr n k (g := actPull n k g z)
    (fun _ hx => actPull_inverse n k g f hx) (fun _ _ => rfl)
    (fun _ hx => actPull_of_notMem n k g (actPull n k g⁻¹ f) hx) hf
  exact he.symm.trans (localIntegral_actPull n k g hg (actPull n k g⁻¹ f) z
    (fun _ hx => actPull_of_notMem n k g⁻¹ f hx))

/-- Exact naturality of the coordinate adjoint under the normalized pullback of `g`. -/
theorem localAdjoint_actPull (n k : ℕ) (g : RealGL) (hg : g.val.det ^ 2 = 1)
    {w : Coordinates → FormValue n (k + 1)} (hw : ContDiffOn ℝ ∞ w positiveCoordinates) :
    EqOn (localAdjoint n k (actPull n (k + 1) g w))
      (actPull n k g (localAdjoint n k w)) positiveCoordinates := by
  apply eqOn_of_form_test_integrals n k
    (contDiffOn_localAdjoint n k (contDiffOn_actPull n (k + 1) g hw))
    (contDiffOn_actPull n k g (contDiffOn_localAdjoint n k hw))
  intro f hf hc hs
  let t := actPull n k g⁻¹ f
  have ht : ContDiffOn ℝ ∞ t positiveCoordinates := contDiffOn_actPull n k g⁻¹ hf.contDiffOn
  have htc : HasCompactSupport t := hasCompactSupport_actPull n k g⁻¹ f hc hs
  have hts : tsupport t ⊆ positiveCoordinates := tsupport_actPull_positive n k g⁻¹ f hc hs
  have hf0 (x : Coordinates) (hx : x ∉ positiveCoordinates) : f x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hh => hx (hs hh))
  have hdf0 (x : Coordinates) (hx : x ∉ positiveCoordinates) : extDeriv f x = 0 :=
    extDeriv_eq_zero_of_notMem_tsupport n k f (fun hh => hx (hs hh))
  have hdt0 (x : Coordinates) (hx : x ∉ positiveCoordinates) : extDeriv t x = 0 :=
    extDeriv_eq_zero_of_notMem_tsupport n k t (fun hh => hx (hts hh))
  change localIntegral n k f (localAdjoint n k (actPull n (k + 1) g w)) =
    localIntegral n k f (actPull n k g (localAdjoint n k w))
  calc
    _ = localIntegral n (k + 1) (extDeriv f) (actPull n (k + 1) g w) :=
      (integral_extDeriv_localAdjoint_test n k f (actPull n (k + 1) g w)
        hf.contDiffOn (contDiffOn_actPull n (k + 1) g hw) hc hs).symm
    _ = localIntegral n (k + 1) (actPull n (k + 1) g⁻¹ (extDeriv f)) w :=
      localIntegral_actPull_right n (k + 1) g hg (extDeriv f) w hdf0
    _ = localIntegral n (k + 1) (extDeriv t) w := by
      apply localIntegral_congr n (k + 1)
      · intro x hx
        exact (extDeriv_actPull n k g⁻¹ hf.contDiffOn hx).symm
      · intro _ _; rfl
      · intro x hx
        exact actPull_of_notMem n (k + 1) g⁻¹ (extDeriv f) hx
      · exact hdt0
    _ = localIntegral n k t (localAdjoint n k w) :=
      integral_extDeriv_localAdjoint_test n k t w ht hw htc hts
    _ = _ := (localIntegral_actPull_right n k g hg f (localAdjoint n k w) hf0).symm

/-! ### Equivariance equations -/

/-- The equivariance equation of a raw form for `g` at the point `x`: the tangent pullback of
`w` along the coordinate action of `g` equals the coefficient action of `g` applied to `w x`. -/
def EquivariantAt (n k : ℕ) (g : RealGL) (w : Coordinates → FormValue n k) (x : Coordinates) :
    Prop :=
  (w (coordinateAction g x)).compContinuousLinearMap (fderiv ℝ (coordinateAction g) x) =
    coefficientFormMap (realCoefficientMap n g) k (w x)

theorem actPull_eq_of_equivariantAt (n k : ℕ) (g : RealGL) {w : Coordinates → FormValue n k}
    {x : Coordinates} (hx : x ∈ positiveCoordinates) (h : EquivariantAt n k g w x) :
    actPull n k g w x = w x := by
  rw [actPull_apply n k g w hx]
  change coefficientFormMap (realCoefficientMap n g⁻¹) k
    ((w (coordinateAction g x)).compContinuousLinearMap (fderiv ℝ (coordinateAction g) x)) = _
  have h' : (w (coordinateAction g x)).compContinuousLinearMap (fderiv ℝ (coordinateAction g) x) =
      coefficientFormMap (realCoefficientMap n g) k (w x) := h
  rw [h', coefficientFormMap_comp]
  have : (realCoefficientMap n g⁻¹).comp (realCoefficientMap n g) = ContinuousLinearMap.id ℝ _ :=
    ContinuousLinearMap.ext (realCoefficientMap_inverse' n g)
  rw [this]
  ext v
  simp [coefficientFormMap]

/-- The coordinate adjoint of a `g`-equivariant form is `g`-equivariant. -/
theorem localAdjoint_equivariantAt (n k : ℕ) (g : RealGL) (hg : g.val.det ^ 2 = 1)
    {w : Coordinates → FormValue n (k + 1)} (hw : ContDiffOn ℝ ∞ w positiveCoordinates)
    (hE : ∀ x ∈ positiveCoordinates, EquivariantAt n (k + 1) g w x)
    {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    EquivariantAt n k g (localAdjoint n k w) x := by
  have he : actPull n (k + 1) g w =ᶠ[𝓝 x] w := by
    filter_upwards [isOpen_positiveCoordinates.mem_nhds hx] with y hy
    exact actPull_eq_of_equivariantAt n (k + 1) g hy (hE y hy)
  have hcov := localAdjoint_actPull n k g hg hw hx
  rw [localAdjoint_congr n k he] at hcov
  have hp := actPull_equation n k g (localAdjoint n k w) hx
  rw [← hcov] at hp
  exact hp.symm

/-- The exterior derivative of a `g`-equivariant form is `g`-equivariant. -/
theorem extDeriv_equivariantAt (n k : ℕ) (g : RealGL) {w : Coordinates → FormValue n k}
    (hw : ContDiffOn ℝ ∞ w positiveCoordinates)
    (hE : ∀ x ∈ positiveCoordinates, EquivariantAt n k g w x)
    {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    EquivariantAt n (k + 1) g (extDeriv w) x := by
  have he : actPull n k g w =ᶠ[𝓝 x] w := by
    filter_upwards [isOpen_positiveCoordinates.mem_nhds hx] with y hy
    exact actPull_eq_of_equivariantAt n k g hy (hE y hy)
  have hcov := extDeriv_actPull n k g hw hx
  rw [he.extDeriv_eq] at hcov
  have hp := actPull_equation n (k + 1) g (extDeriv w) hx
  rw [← hcov] at hp
  exact hp.symm

/-- The form pairing of `g`-equivariant sections is invariant under the coordinate action. -/
theorem formPairing_equivariantAt (n k : ℕ) (g : RealGL) (hg : g.val.det ^ 2 = 1)
    {w z : Coordinates → FormValue n k} {x : Coordinates} (hx : x ∈ positiveCoordinates)
    (hw : EquivariantAt n k g w x) (hz : EquivariantAt n k g z x) :
    formPairing n k (coordinateAction g x) (w (coordinateAction g x)) (z (coordinateAction g x)) =
      formPairing n k x (w x) (z x) :=
  formPairing_real n k g hg x hx _ _ _ _ hw hz

/-! ### Symmetric exterior, contraction and energy current -/

/-- Literal covariance of a fiberwise operator under the coordinate action of `g`. -/
def IsActionOperator (n k l : ℕ) (g : RealGL)
    (A : Coordinates → FormValue n k →L[ℝ] FormValue n l) : Prop :=
  ∀ x ∈ positiveCoordinates, ∀ a b : FormValue n k,
    a.compContinuousLinearMap (fderiv ℝ (coordinateAction g) x) =
      coefficientFormMap (realCoefficientMap n g) k b →
    (A (coordinateAction g x) a).compContinuousLinearMap (fderiv ℝ (coordinateAction g) x) =
      coefficientFormMap (realCoefficientMap n g) l (A x b)

theorem IsActionOperator.equivariantAt {n k l : ℕ} {g : RealGL}
    {A : Coordinates → FormValue n k →L[ℝ] FormValue n l} (hA : IsActionOperator n k l g A)
    {w : Coordinates → FormValue n k} {x : Coordinates} (hx : x ∈ positiveCoordinates)
    (h : EquivariantAt n k g w x) : EquivariantAt n l g (fun y => A y (w y)) x :=
  hA x hx _ _ h

theorem symmetricExteriorCLM_isActionOperator (n k : ℕ) (g : RealGL) (hg : g.val.det ^ 2 = 1) :
    IsActionOperator n k (k + 1) g (symmetricExteriorCLM n k) := by
  intro x hx a b ha
  simp only [symmetricExteriorCLM_apply]
  exact symmetricExterior_real n k g hg x hx a b ha

theorem symmetricContractionCLM_isActionOperator (n k : ℕ) (g : RealGL)
    (hg : g.val.det ^ 2 = 1) : IsActionOperator n (k + 1) k g (symmetricContractionCLM n k) := by
  intro x hx a b ha
  simp only [symmetricContractionCLM_apply]
  exact symmetricContraction_real n k g hg x hx a b ha

/-- Literal tangent covariance of a vector field under the coordinate action of `g`. -/
def IsActionVectorField (g : RealGL) (V : Coordinates → Coordinates) : Prop :=
  ∀ x ∈ positiveCoordinates, V (coordinateAction g x) = fderiv ℝ (coordinateAction g) x (V x)

theorem symmetricPart_form_real (n k : ℕ) (g : RealGL) (hg : g.val.det ^ 2 = 1)
    (x : Coordinates) (hx : x ∈ positiveCoordinates) (v : Coordinates) (a b : FormValue n k)
    (ha : a.compContinuousLinearMap (fderiv ℝ (coordinateAction g) x) =
      coefficientFormMap (realCoefficientMap n g) k b) :
    (coefficientFormMap (symmetricPart n (coordinateAction g x)
      (fderiv ℝ (coordinateAction g) x v)) k a).compContinuousLinearMap
      (fderiv ℝ (coordinateAction g) x) =
      coefficientFormMap (realCoefficientMap n g) k
        (coefficientFormMap (symmetricPart n x v) k b) := by
  apply ContinuousAlternatingMap.ext
  intro z
  have he := congrArg (fun c : FormValue n k => c z) ha
  change a (fun i => fderiv ℝ (coordinateAction g) x (z i)) = realCoefficientMap n g (b z) at he
  change symmetricPart n (coordinateAction g x) (fderiv ℝ (coordinateAction g) x v)
      (a (fun i => fderiv ℝ (coordinateAction g) x (z i))) =
    realCoefficientMap n g (symmetricPart n x v (b z))
  rw [he]
  exact symmetricPart_real n g hg x hx v (b z)

theorem energyCovector_real (n k : ℕ) (g : RealGL) (hg : g.val.det ^ 2 = 1) (x : Coordinates)
    (hx : x ∈ positiveCoordinates) (v : Coordinates) (a b : FormValue n k)
    (ha : a.compContinuousLinearMap (fderiv ℝ (coordinateAction g) x) =
      coefficientFormMap (realCoefficientMap n g) k b) :
    energyCovector n k (coordinateAction g x) a (fderiv ℝ (coordinateAction g) x v) =
      energyCovector n k x b v :=
  formPairing_real n k g hg x hx _ _ _ _ ha (symmetricPart_form_real n k g hg x hx v a b ha)

/-- The energy current of a `g`-equivariant section is a `g`-covariant vector field. -/
theorem energyCurrent_isActionVectorField (n k : ℕ) (g : RealGL) (hg : g.val.det ^ 2 = 1)
    {w : Coordinates → FormValue n k} (hE : ∀ x ∈ positiveCoordinates, EquivariantAt n k g w x) :
    IsActionVectorField g (energyCurrent n k w) := by
  intro x hx
  let L := fderiv ℝ (coordinateAction g) x
  let M := LinearMap.toMatrix' L.toLinearMap
  let a := energyCovectorCoordinates n k w x
  let b := energyCovectorCoordinates n k w (coordinateAction g x)
  have hab : M.transpose *ᵥ b = a := by
    rw [show b = fun i => energyCovector n k (coordinateAction g x) (w (coordinateAction g x))
      (Pi.single i 1) from rfl]
    rw [covectorCoordinates_pullback]
    funext i
    exact energyCovector_real n k g hg x hx (Pi.single i 1) _ _ (hE x hx)
  change inverseGram (coordinateAction g x) *ᵥ b = L (inverseGram x *ᵥ a)
  rw [← inverseGram_real g x hx]
  change (M * inverseGram x * M.transpose) *ᵥ b = L (inverseGram x *ᵥ a)
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hab]
  exact LinearMap.toMatrix'_mulVec L.toLinearMap _

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
