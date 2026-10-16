module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Variants.ComplexForms

@[expose] public section


/-!
# General coercivity, complex dual coefficients

The dual coefficient system `(Sym^n((ℝ³)*))^* ⊗ ℂ` of the complexified bundle: smooth `Γ`-equivariant
forms with values in `Sym^n ℂ³` for the representation `complexRepresentation ∘ θ`, with the Hermitian
extension of the dual flat metric.  Real and imaginary parts identify them with pairs of dual forms
(`cxEquivD`), compatibly with `d` and the Hermitian `L²` pairing; the coercivity estimate for the
real dual coefficients (`general_coercivity_dual`) then gives the estimate with the same constant.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open TernaryPoly TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceCharts
  TernaryPoly.SymmetricSpaceCovering TernaryPoly.SmoothCoveringDeRham
  TernaryPoly.SmoothLocalDeRham TernaryPoly.PolynomialCoefficientMetric
  TernaryPoly.PolynomialFormMetric TernaryPoly.PolynomialFormConnection
open Set Filter MvPolynomial
open scoped ContDiff Topology

attribute [local instance 2000] TernaryPoly.PolynomialCoefficientMetric.coefficientTopologicalSpace

variable {Γ : Subgroup RealGL} {n k : ℕ}

/-- Equivariance of a `Sym^n ℂ³`-valued form for the dual (Cartan-twisted) substitution action. -/
def IsCxDualEquivariant (Γ : Subgroup RealGL) (n k : ℕ) (w : Coordinates → FormC n k) : Prop :=
  ∀ (γ : Γ) (x : Coordinates), x ∈ positiveCoordinates →
    pullRaw (coordinateAction (γ : RealGL)) w x =
      coefficientFormMap
        (complexRepresentation n (thetaHom (γ : RealGL))).toContinuousLinearMap k (w x)

theorem IsCxDualEquivariant.zero : IsCxDualEquivariant Γ n k 0 := by
  intro g x hx
  apply ContinuousAlternatingMap.ext
  intro v
  simp [pullRaw, coefficientFormMap]

theorem IsCxDualEquivariant.add {w z : Coordinates → FormC n k} (hw : IsCxDualEquivariant Γ n k w)
    (hz : IsCxDualEquivariant Γ n k z) : IsCxDualEquivariant Γ n k (w + z) := by
  intro g x hx
  apply ContinuousAlternatingMap.ext
  intro v
  simpa [pullRaw, coefficientFormMap] using
    congrArg (fun z : FormC n k => z v) (congrArg₂ (· + ·) (hw g x hx) (hz g x hx))

theorem IsCxDualEquivariant.smul (c : ℝ) {w : Coordinates → FormC n k}
    (hw : IsCxDualEquivariant Γ n k w) : IsCxDualEquivariant Γ n k (c • w) := by
  intro g x hx
  apply ContinuousAlternatingMap.ext
  intro v
  simpa [pullRaw, coefficientFormMap] using
    congrArg (fun z : FormC n k => z v) (congrArg (c • ·) (hw g x hx))

variable (Γ n k) in
/-- Smooth `Γ`-equivariant forms with values in the complexified dual coefficient space, with compact
closed projected support in the orbit space. -/
def CFormCxD : Submodule ℝ (Form (F := ComplexCoefficients n) positiveCoordinates k) where
  carrier := {w | IsCxDualEquivariant Γ n k (w : Coordinates → FormC n k) ∧
    IsCompact (projSupport Γ (w : Coordinates → FormC n k))}
  zero_mem' := ⟨IsCxDualEquivariant.zero, by simp [projSupport_zero']⟩
  add_mem' := by
    rintro w z ⟨hw, hwc⟩ ⟨hz, hzc⟩
    exact ⟨hw.add hz, (hwc.union hzc).of_isClosed_subset isClosed_closure (projSupport_add' _ _)⟩
  smul_mem' := by
    rintro c w ⟨hw, hwc⟩
    exact ⟨hw.smul c, hwc.of_isClosed_subset isClosed_closure (projSupport_smul' c _)⟩

/-- The underlying function of a complex dual form. -/
abbrev CFormCxD.fn (w : CFormCxD Γ n k) : Coordinates → FormC n k :=
  ((w : Form (F := ComplexCoefficients n) positiveCoordinates k) : Coordinates → FormC n k)

theorem CFormCxD.equivariant (w : CFormCxD Γ n k) : IsCxDualEquivariant Γ n k (CFormCxD.fn w) :=
  w.2.1

theorem CFormCxD.compact (w : CFormCxD Γ n k) : IsCompact (projSupport Γ (CFormCxD.fn w)) :=
  w.2.2

theorem CFormCxD.smooth (w : CFormCxD Γ n k) :
    ContDiffOn ℝ ∞ (CFormCxD.fn w) positiveCoordinates :=
  Form.smooth (w : Form (F := ComplexCoefficients n) positiveCoordinates k)

@[ext] theorem CFormCxD.ext {w z : CFormCxD Γ n k}
    (h : ∀ x ∈ positiveCoordinates, CFormCxD.fn w x = CFormCxD.fn z x) : w = z :=
  Subtype.ext (Form.ext h)

theorem isRepEquivariant_re (w : CFormCxD Γ n k) :
    IsRepEquivariant Γ n (dualRep Γ n) k
      (formMap (reL n) k (w : Form (F := ComplexCoefficients n) positiveCoordinates k)
        : Coordinates → FormValue n k) := by
  intro γ x hx
  change pullRaw (coordinateAction (γ : RealGL)) (coefficientRaw (reL n) (CFormCxD.fn w)) x =
    coefficientFormMap (dualRep Γ n γ).toContinuousLinearMap k
      (coefficientFormMap (reL n) k (CFormCxD.fn w x))
  rw [pullRaw_coefficientRaw, CFormCxD.equivariant w γ x hx, cFM_comp, cFM_comp,
    reL_comp_rep (thetaHom (γ : RealGL))]
  rfl

theorem isRepEquivariant_im (w : CFormCxD Γ n k) :
    IsRepEquivariant Γ n (dualRep Γ n) k
      (formMap (imL n) k (w : Form (F := ComplexCoefficients n) positiveCoordinates k)
        : Coordinates → FormValue n k) := by
  intro γ x hx
  change pullRaw (coordinateAction (γ : RealGL)) (coefficientRaw (imL n) (CFormCxD.fn w)) x =
    coefficientFormMap (dualRep Γ n γ).toContinuousLinearMap k
      (coefficientFormMap (imL n) k (CFormCxD.fn w x))
  rw [pullRaw_coefficientRaw, CFormCxD.equivariant w γ x hx, cFM_comp, cFM_comp,
    imL_comp_rep (thetaHom (γ : RealGL))]
  rfl

/-- The real and imaginary parts of a complex dual form. -/
def toPairsD (Γ : Subgroup RealGL) (n k : ℕ) : CFormCxD Γ n k →ₗ[ℝ] DForm Γ n k × DForm Γ n k where
  toFun w := (⟨formMap (reL n) k (w : Form (F := ComplexCoefficients n) positiveCoordinates k),
      isRepEquivariant_re w, (CFormCxD.compact w).of_isClosed_subset isClosed_closure
        (projSupport_map_subset (reL n) _)⟩,
    ⟨formMap (imL n) k (w : Form (F := ComplexCoefficients n) positiveCoordinates k),
      isRepEquivariant_im w, (CFormCxD.compact w).of_isClosed_subset isClosed_closure
        (projSupport_map_subset (imL n) _)⟩)
  map_add' _ _ := Prod.ext (Subtype.ext (map_add _ _ _)) (Subtype.ext (map_add _ _ _))
  map_smul' _ _ := Prod.ext (Subtype.ext (map_smul _ _ _)) (Subtype.ext (map_smul _ _ _))

theorem isCxDualEquivariant_ofPairs (a b : DForm Γ n k) :
    IsCxDualEquivariant Γ n k
      (formMap (embRe n) k (a : Form (F := Coefficients n) positiveCoordinates k) +
        formMap (embIm n) k (b : Form (F := Coefficients n) positiveCoordinates k) :
          Form (F := ComplexCoefficients n) positiveCoordinates k) := by
  intro γ x hx
  change pullRaw (coordinateAction (γ : RealGL))
      (coefficientRaw (embRe n) (DForm.fn a) + coefficientRaw (embIm n) (DForm.fn b)) x =
    coefficientFormMap (complexRepresentation n (thetaHom (γ : RealGL))).toContinuousLinearMap k
      (coefficientFormMap (embRe n) k (DForm.fn a x) + coefficientFormMap (embIm n) k (DForm.fn b x))
  rw [pullRaw_add', pullRaw_coefficientRaw, pullRaw_coefficientRaw, DForm.equivariant a γ x hx,
    DForm.equivariant b γ x hx, map_add, cFM_comp, cFM_comp, cFM_comp, cFM_comp]
  have e1 : (embRe n).comp (dualRep Γ n γ).toContinuousLinearMap =
      (complexRepresentation n (thetaHom (γ : RealGL))).toContinuousLinearMap.comp (embRe n) :=
    (rep_comp_embRe (thetaHom (γ : RealGL))).symm
  have e2 : (embIm n).comp (dualRep Γ n γ).toContinuousLinearMap =
      (complexRepresentation n (thetaHom (γ : RealGL))).toContinuousLinearMap.comp (embIm n) :=
    (rep_comp_embIm (thetaHom (γ : RealGL))).symm
  rw [e1, e2]

/-- A complex dual form from its real and imaginary parts. -/
def ofPairsD (Γ : Subgroup RealGL) (n k : ℕ) : DForm Γ n k × DForm Γ n k →ₗ[ℝ] CFormCxD Γ n k where
  toFun p := ⟨formMap (embRe n) k (p.1 : Form (F := Coefficients n) positiveCoordinates k) +
      formMap (embIm n) k (p.2 : Form (F := Coefficients n) positiveCoordinates k),
    isCxDualEquivariant_ofPairs p.1 p.2,
    ((DForm.compact p.1).of_isClosed_subset isClosed_closure
        (projSupport_map_subset (embRe n) _) |>.union
      ((DForm.compact p.2).of_isClosed_subset isClosed_closure
        (projSupport_map_subset (embIm n) _))).of_isClosed_subset isClosed_closure
      (projSupport_add' _ _)⟩
  map_add' p q := Subtype.ext (by
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, map_add]
    abel)
  map_smul' c p := Subtype.ext (by
    simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, map_smul, smul_add]
    rfl)

theorem ofPairsD_fn (p : DForm Γ n k × DForm Γ n k) (x : Coordinates) :
    CFormCxD.fn (ofPairsD Γ n k p) x =
      coefficientFormMap (embRe n) k (DForm.fn p.1 x) +
        coefficientFormMap (embIm n) k (DForm.fn p.2 x) := rfl

theorem toPairsD_comp_ofPairsD_fst_aux (p : DForm Γ n k × DForm Γ n k) :
    ((toPairsD Γ n k) ((ofPairsD Γ n k) p)).1 = p.1 :=
  DForm.ext fun x _ => by
    change coefficientFormMap (reL n) k (coefficientFormMap (embRe n) k (DForm.fn p.1 x) +
      coefficientFormMap (embIm n) k (DForm.fn p.2 x)) = DForm.fn p.1 x
    rw [TernaryPoly.PolynomialFormCoordinates.clm_map_add, cFM_comp, cFM_comp, reL_comp_embRe,
      reL_comp_embIm, cFM_id, cFM_zero, add_zero]

theorem toPairsD_comp_ofPairsD_snd_aux (p : DForm Γ n k × DForm Γ n k) :
    ((toPairsD Γ n k) ((ofPairsD Γ n k) p)).2 = p.2 :=
  DForm.ext fun x _ => by
    change coefficientFormMap (imL n) k (coefficientFormMap (embRe n) k (DForm.fn p.1 x) +
      coefficientFormMap (embIm n) k (DForm.fn p.2 x)) = DForm.fn p.2 x
    rw [TernaryPoly.PolynomialFormCoordinates.clm_map_add, cFM_comp, cFM_comp, imL_comp_embRe,
      imL_comp_embIm, cFM_id, cFM_zero, zero_add]

theorem ofPairsD_comp_toPairsD_aux (w : CFormCxD Γ n k) : (ofPairsD Γ n k) ((toPairsD Γ n k) w) = w :=
  CFormCxD.ext fun x _ => by
    change coefficientFormMap (embRe n) k (coefficientFormMap (reL n) k (CFormCxD.fn w x)) +
      coefficientFormMap (embIm n) k (coefficientFormMap (imL n) k (CFormCxD.fn w x)) =
        CFormCxD.fn w x
    rw [cFM_comp, cFM_comp, ← cFM_add, embRe_reL_add, cFM_id]

/-- **The real/imaginary bridge for complex dual forms.** -/
def cxEquivD (Γ : Subgroup RealGL) (n k : ℕ) : CFormCxD Γ n k ≃ₗ[ℝ] DForm Γ n k × DForm Γ n k :=
  LinearEquiv.ofLinearMap (toPairsD Γ n k) (ofPairsD Γ n k)
    (LinearMap.ext fun p => Prod.ext (toPairsD_comp_ofPairsD_fst_aux p) (toPairsD_comp_ofPairsD_snd_aux p))
    (LinearMap.ext fun w => ofPairsD_comp_toPairsD_aux w)

theorem toPairsD_fst_fn (w : CFormCxD Γ n k) :
    DForm.fn (toPairsD Γ n k w).1 = coefficientRaw (reL n) (CFormCxD.fn w) := rfl

theorem toPairsD_snd_fn (w : CFormCxD Γ n k) :
    DForm.fn (toPairsD Γ n k w).2 = coefficientRaw (imL n) (CFormCxD.fn w) := rfl

theorem toPairsD_ofPairsD (p : DForm Γ n k × DForm Γ n k) : toPairsD Γ n k (ofPairsD Γ n k p) = p :=
  (cxEquivD Γ n k).apply_symm_apply p

theorem ofPairsD_toPairsD (w : CFormCxD Γ n k) : ofPairsD Γ n k (toPairsD Γ n k w) = w :=
  (cxEquivD Γ n k).symm_apply_apply w

/-! ### The exterior derivative and the Hermitian metric -/

/-- The exterior derivative of complex dual forms. -/
def CFormCxD.d (h : Admissible Γ) (n k : ℕ) : CFormCxD Γ n k →ₗ[ℝ] CFormCxD Γ n (k + 1) :=
  (ofPairsD Γ n (k + 1)).comp ((LinearMap.prodMap (dualD h n k) (dualD h n k)).comp
    (toPairsD Γ n k))

theorem CFormCxD.d_apply (h : Admissible Γ) (w : CFormCxD Γ n k) {x : Coordinates}
    (hx : x ∈ positiveCoordinates) :
    CFormCxD.fn (CFormCxD.d h n k w) x = extDeriv (CFormCxD.fn w) x := by
  have hdiff : DifferentiableAt ℝ (CFormCxD.fn w) x :=
    ((CFormCxD.smooth w x hx).contDiffAt (isOpen_positiveCoordinates.mem_nhds hx)).differentiableAt
      (by simp)
  change CFormCxD.fn (ofPairsD Γ n (k + 1) (dualD h n k (toPairsD Γ n k w).1,
    dualD h n k (toPairsD Γ n k w).2)) x = _
  rw [ofPairsD_fn]
  simp only
  have e1 := dualD_apply h (toPairsD Γ n k w).1 hx
  have e2 := dualD_apply h (toPairsD Γ n k w).2 hx
  have e3 : DForm.fn (toPairsD Γ n k w).1 = coefficientRaw (reL n) (CFormCxD.fn w) :=
    toPairsD_fst_fn w
  have e4 : DForm.fn (toPairsD Γ n k w).2 = coefficientRaw (imL n) (CFormCxD.fn w) :=
    toPairsD_snd_fn w
  have e5 := extDeriv_coefficientRaw (reL n) hdiff
  have e6 := extDeriv_coefficientRaw (imL n) hdiff
  have e7 : coefficientFormMap (embRe n) (k + 1)
      (coefficientFormMap (reL n) (k + 1) (extDeriv (CFormCxD.fn w) x)) +
      coefficientFormMap (embIm n) (k + 1)
        (coefficientFormMap (imL n) (k + 1) (extDeriv (CFormCxD.fn w) x)) =
        extDeriv (CFormCxD.fn w) x := by
    rw [cFM_comp, cFM_comp, ← cFM_add, embRe_reL_add, cFM_id]
  refine (congrArg₂ (fun u v => coefficientFormMap (embRe n) (k + 1) u +
    coefficientFormMap (embIm n) (k + 1) v) e1 e2).trans ?_
  rw [e3, e4, e5, e6]
  exact e7

theorem toPairsD_d (h : Admissible Γ) (w : CFormCxD Γ n k) :
    toPairsD Γ n (k + 1) (CFormCxD.d h n k w) =
      (dualD h n k (toPairsD Γ n k w).1, dualD h n k (toPairsD Γ n k w).2) :=
  toPairsD_ofPairsD _

/-- The metric of the complexified dual bundle at `x`: the inverse trace Gram matrix tensored with the
Hermitian extension of the dual coefficient metric (the Fischer metric at the Cartan point `ι x`). -/
def formPairingCD (n k : ℕ) (x : Coordinates) (a b : FormC n k) : ℝ :=
  (k.factorial : ℝ)⁻¹ * matrixContraction (cplxBilin n (coordinateCoefficientBilin n (iotaC x)))
    (tensorMatrix k (inverseGram x)) (formCoordC a) (formCoordC b)

theorem formPairingCD_eq (x : Coordinates) (a b : FormC n k) :
    formPairingCD n k x a b =
      dualFormPairing n k x (coefficientFormMap (reL n) k a) (coefficientFormMap (reL n) k b) +
        dualFormPairing n k x (coefficientFormMap (imL n) k a) (coefficientFormMap (imL n) k b) := by
  unfold formPairingCD dualFormPairing matrixContraction
  simp only [cplxBilin, LinearMap.add_apply, LinearMap.compl₁₂_apply, mul_add, Finset.sum_add_distrib]
  ring_nf
  rfl

/-- The descended pointwise Hermitian dual metric. -/
def scalarPairingCxD (a b : CFormCxD Γ n k) : OrbitSpace Γ → ℝ :=
  dualScalar (toPairsD Γ n k a).1 (toPairsD Γ n k b).1 +
    dualScalar (toPairsD Γ n k a).2 (toPairsD Γ n k b).2

theorem scalarPairingCxD_proj (h : Admissible Γ) (a b : CFormCxD Γ n k) (S : Space) :
    scalarPairingCxD a b (proj Γ S) =
      formPairingCD n k (coordinateChart S) (CFormCxD.fn a (coordinateChart S))
        (CFormCxD.fn b (coordinateChart S)) := by
  unfold scalarPairingCxD
  exact (congrArg₂ (· + ·) (dualScalar_proj h _ _ S) (dualScalar_proj h _ _ S)).trans
    (formPairingCD_eq _ _ _).symm

theorem integrable_dualScalar (h : Admissible Γ) (a b : DForm Γ n k) :
    MeasureTheory.Integrable (dualScalar a b) (quotientVolume Γ) := by
  have hcongr : dualScalar a b =
      (scalarPairing (toStd h n k a) (toStd h n k b)) ∘ qIota Γ :=
    funext (dualScalar_eq_std h a b)
  have hmeas : Measurable (scalarPairing (toStd h n k a) (toStd h n k b)) :=
    (continuous_scalarPairing h.theta _ _).measurable
  rw [hcongr]
  refine (MeasureTheory.integrable_map_measure ?_ (measurable_qIota Γ).aemeasurable).mp ?_
  · rw [map_qIota_quotientVolume h]
    exact hmeas.aestronglyMeasurable
  · rw [map_qIota_quotientVolume h]
    exact integrable_scalarPairing _ _

/-- The Hermitian `L²` pairing of complex dual forms. -/
def l2CxD (a b : CFormCxD Γ n k) : ℝ := ∫ q, scalarPairingCxD a b q ∂quotientVolume Γ

/-- The squared `L²` norm of a complex dual form. -/
def normSqCxD (a : CFormCxD Γ n k) : ℝ := l2CxD a a

theorem l2CxD_eq_pairs (h : Admissible Γ) (a b : CFormCxD Γ n k) :
    l2CxD a b = dualL2 (toPairsD Γ n k a).1 (toPairsD Γ n k b).1 +
      dualL2 (toPairsD Γ n k a).2 (toPairsD Γ n k b).2 := by
  unfold l2CxD scalarPairingCxD dualL2
  exact MeasureTheory.integral_add (integrable_dualScalar h _ _) (integrable_dualScalar h _ _)

theorem dualL2_zero_left (h : Admissible Γ) (b : DForm Γ n k) :
    dualL2 (0 : DForm Γ n k) b = 0 := by
  have e := dualL2_eq h (0 : DForm Γ n k) b
  rw [map_zero] at e
  exact e.trans (l2Form_zero_left' _)

theorem dualL2_zero_right (h : Admissible Γ) (b : DForm Γ n k) :
    dualL2 b (0 : DForm Γ n k) = 0 := by
  have e := dualL2_eq h b (0 : DForm Γ n k)
  rw [map_zero] at e
  exact e.trans (map_zero _)

/-- `e` is a formal adjoint of the exterior derivative of complex dual forms at `b`. -/
def IsCxDualFormalAdjoint (h : Admissible Γ) (n k : ℕ) (b : CFormCxD Γ n (k + 1))
    (e : CFormCxD Γ n k) : Prop :=
  ∀ a : CFormCxD Γ n k, l2CxD (CFormCxD.d h n k a) b = l2CxD a e

/-- The defect of `α` against the pair `(b, e)` in the componentwise adjoint relation. -/
def defect (h : Admissible Γ) (b : DForm Γ n (k + 1)) (e : DForm Γ n k) (α : DForm Γ n k) : ℝ :=
  dualL2 (dualD h n k α) b - dualL2 α e

theorem defect_zero (h : Admissible Γ) {b : DForm Γ n (k + 1)} {e : DForm Γ n k} :
    defect h b e 0 = 0 := by
  unfold defect
  rw [map_zero, dualL2_zero_left h, dualL2_zero_left h, sub_zero]

theorem real_aux2 (x1 x2 u1 u2 v1 v2 : ℝ) (hg : v1 + v2 = u1 + u2) :
    (x1 + u1) + (x2 + u2) = (x1 + x2) + (v1 + v2) := by
  rw [hg]; ring

theorem real_aux (x1 x2 x1' x2' y1 y2 : ℝ) (h1 : x1 = x1') (h2 : x2 = x2') :
    x1 + x2 - (y1 + y2) = (x1' - y1) + (x2' - y2) := by
  subst h1 h2; ring

theorem isCxDualFormalAdjoint_iff (h : Admissible Γ) (b : CFormCxD Γ n (k + 1))
    (e : CFormCxD Γ n k) :
    IsCxDualFormalAdjoint h n k b e ↔
      IsDualFormalAdjoint h (toPairsD Γ n (k + 1) b).1 (toPairsD Γ n k e).1 ∧
        IsDualFormalAdjoint h (toPairsD Γ n (k + 1) b).2 (toPairsD Γ n k e).2 := by
  have key : ∀ a : CFormCxD Γ n k, l2CxD (CFormCxD.d h n k a) b - l2CxD a e =
      (dualL2 (dualD h n k (toPairsD Γ n k a).1) (toPairsD Γ n (k + 1) b).1 -
        dualL2 (toPairsD Γ n k a).1 (toPairsD Γ n k e).1) +
      (dualL2 (dualD h n k (toPairsD Γ n k a).2) (toPairsD Γ n (k + 1) b).2 -
        dualL2 (toPairsD Γ n k a).2 (toPairsD Γ n k e).2) := by
    intro a
    have e1 := l2CxD_eq_pairs h (CFormCxD.d h n k a) b
    have e2 := l2CxD_eq_pairs h a e
    have e3 : toPairsD Γ n (k + 1) (CFormCxD.d h n k a) =
        (dualD h n k (toPairsD Γ n k a).1, dualD h n k (toPairsD Γ n k a).2) := toPairsD_d h a
    have e4 : dualL2 (toPairsD Γ n (k + 1) (CFormCxD.d h n k a)).1 (toPairsD Γ n (k + 1) b).1 =
        dualL2 (dualD h n k (toPairsD Γ n k a).1) (toPairsD Γ n (k + 1) b).1 :=
      congrArg (fun x => dualL2 x (toPairsD Γ n (k + 1) b).1) (congrArg Prod.fst e3)
    have e5 : dualL2 (toPairsD Γ n (k + 1) (CFormCxD.d h n k a)).2 (toPairsD Γ n (k + 1) b).2 =
        dualL2 (dualD h n k (toPairsD Γ n k a).2) (toPairsD Γ n (k + 1) b).2 :=
      congrArg (fun x => dualL2 x (toPairsD Γ n (k + 1) b).2) (congrArg Prod.snd e3)
    exact (congrArg₂ (fun x y : ℝ => x - y) e1 e2).trans
      (real_aux _ _ _ _ _ _ e4 e5)
  have key2 : ∀ a : CFormCxD Γ n k, l2CxD (CFormCxD.d h n k a) b - l2CxD a e =
      defect h (toPairsD Γ n (k + 1) b).1 (toPairsD Γ n k e).1 (toPairsD Γ n k a).1 +
        defect h (toPairsD Γ n (k + 1) b).2 (toPairsD Γ n k e).2 (toPairsD Γ n k a).2 :=
    key
  have hpair : ∀ p : DForm Γ n k × DForm Γ n k, toPairsD Γ n k (ofPairsD Γ n k p) = p :=
    toPairsD_ofPairsD
  constructor
  · intro hd
    have hz : ∀ a : CFormCxD Γ n k,
        defect h (toPairsD Γ n (k + 1) b).1 (toPairsD Γ n k e).1 (toPairsD Γ n k a).1 +
          defect h (toPairsD Γ n (k + 1) b).2 (toPairsD Γ n k e).2 (toPairsD Γ n k a).2 = 0 :=
      fun a => (key2 a).symm.trans (sub_eq_zero.mpr (hd a))
    constructor
    · intro α
      have h1 := hz (ofPairsD Γ n k (α, 0))
      have e1 : (toPairsD Γ n k (ofPairsD Γ n k (α, 0))).1 = α :=
        congrArg Prod.fst (hpair (α, 0))
      have e2 : (toPairsD Γ n k (ofPairsD Γ n k (α, 0))).2 = 0 :=
        congrArg Prod.snd (hpair (α, 0))
      have d1 : defect h (toPairsD Γ n (k + 1) b).1 (toPairsD Γ n k e).1
          (toPairsD Γ n k (ofPairsD Γ n k (α, 0))).1 =
          defect h (toPairsD Γ n (k + 1) b).1 (toPairsD Γ n k e).1 α :=
        congrArg (defect h (toPairsD Γ n (k + 1) b).1 (toPairsD Γ n k e).1) e1
      have d2 : defect h (toPairsD Γ n (k + 1) b).2 (toPairsD Γ n k e).2
          (toPairsD Γ n k (ofPairsD Γ n k (α, 0))).2 = 0 :=
        (congrArg (defect h (toPairsD Γ n (k + 1) b).2 (toPairsD Γ n k e).2) e2).trans
          (defect_zero h)
      exact sub_eq_zero.mp (((add_zero _).symm.trans (congrArg₂ (· + ·) d1 d2).symm).trans h1)
    · intro α
      have h1 := hz (ofPairsD Γ n k (0, α))
      have e1 : (toPairsD Γ n k (ofPairsD Γ n k (0, α))).1 = 0 :=
        congrArg Prod.fst (hpair (0, α))
      have e2 : (toPairsD Γ n k (ofPairsD Γ n k (0, α))).2 = α :=
        congrArg Prod.snd (hpair (0, α))
      have d1 : defect h (toPairsD Γ n (k + 1) b).1 (toPairsD Γ n k e).1
          (toPairsD Γ n k (ofPairsD Γ n k (0, α))).1 = 0 :=
        (congrArg (defect h (toPairsD Γ n (k + 1) b).1 (toPairsD Γ n k e).1) e1).trans
          (defect_zero h)
      have d2 : defect h (toPairsD Γ n (k + 1) b).2 (toPairsD Γ n k e).2
          (toPairsD Γ n k (ofPairsD Γ n k (0, α))).2 =
          defect h (toPairsD Γ n (k + 1) b).2 (toPairsD Γ n k e).2 α :=
        congrArg (defect h (toPairsD Γ n (k + 1) b).2 (toPairsD Γ n k e).2) e2
      exact sub_eq_zero.mp (((zero_add _).symm.trans (congrArg₂ (· + ·) d1 d2).symm).trans h1)
  · rintro ⟨h1, h2⟩ a
    refine sub_eq_zero.mp ((key2 a).trans ?_)
    exact (congrArg₂ (· + ·) (sub_eq_zero.mpr (h1 (toPairsD Γ n k a).1))
      (sub_eq_zero.mpr (h2 (toPairsD Γ n k a).2))).trans (add_zero 0)

theorem normSqCxD_eq_pairs (h : Admissible Γ) (a : CFormCxD Γ n k) :
    normSqCxD a = dualNormSq (toPairsD Γ n k a).1 + dualNormSq (toPairsD Γ n k a).2 :=
  l2CxD_eq_pairs h a a

/-- **General coercivity for complex dual forms.**  There is `c_n > 0`, independent of the
admissible group `Γ`, such that for every compactly supported smooth `Γ`-equivariant form with
values in the dual of the complex homogeneous polynomials (the complexified dual
representation), `c ‖a‖² ≤ ‖d a‖²` in degree `0` and `c ‖a‖² ≤ ‖e‖² + ‖d a‖²` whenever `e` is a
formal adjoint of `d` at `a`, all norms being those of the Hermitian metric
`h(u + iv, u + iv) = |u|² + |v|²` integrated over the orbit space. -/
theorem general_coercivity_complex_dual (n : ℕ) (hn : 0 < n) :
    ∃ c : ℝ, 0 < c ∧ ∀ Γ : Subgroup RealGL, ∀ h : Admissible Γ,
      (∀ a : CFormCxD Γ n 0, c * normSqCxD a ≤ normSqCxD (CFormCxD.d h n 0 a)) ∧
        ∀ (k : ℕ) (a : CFormCxD Γ n (k + 1)) (e : CFormCxD Γ n k),
          IsCxDualFormalAdjoint h n k a e →
            c * normSqCxD a ≤ normSqCxD e + normSqCxD (CFormCxD.d h n (k + 1) a) := by
  obtain ⟨c, hc, H⟩ := general_coercivity_dual n hn
  refine ⟨c, hc, fun Γ h => ⟨fun a => ?_, fun k a e hae => ?_⟩⟩
  · have h1 := (H Γ h).1 (toPairsD Γ n 0 a).1
    have h2 := (H Γ h).1 (toPairsD Γ n 0 a).2
    have e1 := normSqCxD_eq_pairs h a
    have e2 := normSqCxD_eq_pairs h (CFormCxD.d h n 0 a)
    have e3 := toPairsD_d h a
    have f1 : dualNormSq (toPairsD Γ n (0 + 1) (CFormCxD.d h n 0 a)).1 =
        dualNormSq (dualD h n 0 (toPairsD Γ n 0 a).1) :=
      congrArg dualNormSq (congrArg Prod.fst e3)
    have f2 : dualNormSq (toPairsD Γ n (0 + 1) (CFormCxD.d h n 0 a)).2 =
        dualNormSq (dualD h n 0 (toPairsD Γ n 0 a).2) :=
      congrArg dualNormSq (congrArg Prod.snd e3)
    have g := congrArg₂ (· + ·) f1 f2
    have : c * normSqCxD a ≤ normSqCxD (CFormCxD.d h n 0 a) :=
      calc c * normSqCxD a = c * dualNormSq (toPairsD Γ n 0 a).1 +
            c * dualNormSq (toPairsD Γ n 0 a).2 := (congrArg (c * ·) e1).trans (mul_add _ _ _)
        _ ≤ _ := add_le_add h1 h2
        _ = _ := (g.symm.trans e2.symm)
    exact this
  · obtain ⟨hA, hB⟩ := (isCxDualFormalAdjoint_iff h a e).mp hae
    have h1 := (H Γ h).2 k _ _ hA
    have h2 := (H Γ h).2 k _ _ hB
    have e1 := normSqCxD_eq_pairs h a
    have e2 := normSqCxD_eq_pairs h e
    have e3 := normSqCxD_eq_pairs h (CFormCxD.d h n (k + 1) a)
    have e4 := toPairsD_d h a
    have f1 : dualNormSq (toPairsD Γ n (k + 1 + 1) (CFormCxD.d h n (k + 1) a)).1 =
        dualNormSq (dualD h n (k + 1) (toPairsD Γ n (k + 1) a).1) :=
      congrArg dualNormSq (congrArg Prod.fst e4)
    have f2 : dualNormSq (toPairsD Γ n (k + 1 + 1) (CFormCxD.d h n (k + 1) a)).2 =
        dualNormSq (dualD h n (k + 1) (toPairsD Γ n (k + 1) a).2) :=
      congrArg dualNormSq (congrArg Prod.snd e4)
    have g := congrArg₂ (· + ·) f1 f2
    calc c * normSqCxD a = c * dualNormSq (toPairsD Γ n (k + 1) a).1 +
          c * dualNormSq (toPairsD Γ n (k + 1) a).2 := (congrArg (c * ·) e1).trans (mul_add _ _ _)
      _ ≤ (dualNormSq (toPairsD Γ n k e).1 + dualNormSq (dualD h n (k + 1) (toPairsD Γ n (k + 1) a).1)) +
          (dualNormSq (toPairsD Γ n k e).2 + dualNormSq (dualD h n (k + 1) (toPairsD Γ n (k + 1) a).2)) :=
        add_le_add h1 h2
      _ = normSqCxD e + normSqCxD (CFormCxD.d h n (k + 1) a) :=
        (real_aux2 _ _ _ _ _ _ g).trans (congrArg₂ (· + ·) e2.symm e3.symm)

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
