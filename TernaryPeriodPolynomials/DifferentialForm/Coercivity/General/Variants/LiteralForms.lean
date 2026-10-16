module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Variants.ComplexLiteralDual
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Estimates.PrimCoeff

@[expose] public section



/-! # General coercivity: forms with values in the literal `ℂ`-linear dual of `Sym^n ℂ³`

`LitCoeff n = StrongDual ℂ (CHom n)` is the `ℂ`-linear dual of `Sym^n ℂ³` with its operator norm;
`GL₃(ℝ)` acts by the contragredient `litRep n g φ = φ ∘ ρ_ℂ(g)⁻¹`.  The Fischer–Riesz map
`litPhi n : ComplexCoefficients n ≃ₗ[ℝ] LitCoeff n` intertwines `ρ_ℂ ∘ θ` with `litRep`
(`litPhi_equivariant`).  Smooth `Γ`-equivariant compactly supported `LitCoeff`-valued forms `LitForm`
are therefore the same as the complex dual forms `CFormCxD` (`litForms`), compatibly with the
exterior derivative (`LitForm.d_apply`), the `L²` pairing and formal adjoint (defined by transport
of the Hermitian dual metric, which is `‖ρ*(g)⁻¹ φ‖` in the literal dual norm by
`dualNorm_metric_frame`), coercivity (`general_coercivity_lit`) and the vanishing of `H²_c → H²`
(`closed_compact_exact_lit`).

Formalized by Claude Sonnet 5.5. -/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open TernaryPoly TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceCharts
  TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
  TernaryPoly.SymmetricSpaceCovering TernaryPoly.SmoothCoveringDeRham TernaryPoly.SmoothLocalDeRham
  TernaryPoly.PolynomialFormConnection
open Set
open scoped ContDiff

variable {Γ : Subgroup RealGL} {n k : ℕ}

/-- The literal `ℂ`-linear dual of `Sym^n ℂ³`, with its operator norm.  It is a definition (not an
abbreviation) so that its normed-space structure is the single one declared below. -/
def LitCoeff (n : ℕ) : Type := StrongDual ℂ (CHom n)

instance litCoeffNormedAddCommGroup (n : ℕ) : NormedAddCommGroup (LitCoeff n) :=
  inferInstanceAs (NormedAddCommGroup (StrongDual ℂ (CHom n)))

instance litCoeffNormedSpaceC (n : ℕ) : NormedSpace ℂ (LitCoeff n) :=
  inferInstanceAs (NormedSpace ℂ (StrongDual ℂ (CHom n)))

instance litCoeffNormedSpaceR (n : ℕ) : NormedSpace ℝ (LitCoeff n) := NormedSpace.complexToReal

instance litCoeffFiniteDimensional (n : ℕ) : FiniteDimensional ℂ (LitCoeff n) :=
  inferInstanceAs (FiniteDimensional ℂ (StrongDual ℂ (CHom n)))

/-- A linear functional as an element of `LitCoeff n`. -/
def LitCoeff.mk (n : ℕ) (φ : StrongDual ℂ (CHom n)) : LitCoeff n := φ

/-- An element of `LitCoeff n` as a continuous `ℂ`-linear functional. -/
def LitCoeff.toStrong {n : ℕ} (φ : LitCoeff n) : StrongDual ℂ (CHom n) := φ

instance (n : ℕ) : CoeFun (LitCoeff n) (fun _ => CHom n → ℂ) := ⟨fun φ => φ.toStrong⟩

/-- The Fischer–Riesz isomorphism, `ℝ`-linear. -/
def litPhi (n : ℕ) : ComplexCoefficients n ≃ₗ[ℝ] LitCoeff n :=
  (chomEquiv n).symm.trans
    { toFun := fun p => LitCoeff.mk n (InnerProductSpace.toDual ℂ (CHom n) p)
      map_add' := fun p q => map_add (InnerProductSpace.toDual ℂ (CHom n)) p q
      map_smul' := fun r p => by
        change InnerProductSpace.toDual ℂ (CHom n) ((r : ℂ) • p) =
          (r : ℂ) • InnerProductSpace.toDual ℂ (CHom n) p
        rw [LinearIsometryEquiv.map_smulₛₗ]
        ext v
        simp [Complex.real_smul]
      invFun := fun φ => (InnerProductSpace.toDual ℂ (CHom n)).symm φ.toStrong
      left_inv := fun p => by simp [LitCoeff.mk, LitCoeff.toStrong]
      right_inv := fun φ => (InnerProductSpace.toDual ℂ (CHom n)).apply_symm_apply φ.toStrong }

/-- The contragredient action on the literal dual, `ℝ`-linear. -/
def litRepLin (n : ℕ) (g : RealGL) : LitCoeff n →ₗ[ℝ] LitCoeff n where
  toFun φ := LitCoeff.mk n (φ.toStrong.comp (rhoC n g⁻¹).toContinuousLinearMap)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The contragredient action on the literal dual, as a continuous `ℝ`-linear map. -/
def litRep (n : ℕ) (g : RealGL) : LitCoeff n →L[ℝ] LitCoeff n :=
  LinearMap.toContinuousLinearMap (litRepLin n g)

theorem litRep_apply (n : ℕ) (g : RealGL) (φ : LitCoeff n) (v : CHom n) :
    litRep n g φ v = φ (rhoC n g⁻¹ v) := rfl

/-- `ρ_ℂ(θ g)` corresponds to the contragredient action under the Fischer–Riesz map. -/
theorem litPhi_equivariant (n : ℕ) (g : RealGL) (p : ComplexCoefficients n) :
    litPhi n (complexRepresentation n (thetaHom g) p) = litRep n g (litPhi n p) := by
  have h := toDual_rhoC_theta n g ((chomEquiv n).symm p)
  have e : (chomEquiv n).symm (complexRepresentation n (thetaHom g) p) =
      rhoC n (thetaHom g) ((chomEquiv n).symm p) := by
    apply CHom.ext
    have := rhoC_val_eq_representation n (thetaHom g) ((chomEquiv n).symm p)
    rw [LinearEquiv.apply_symm_apply] at this
    exact this
  change LitCoeff.mk n (InnerProductSpace.toDual ℂ (CHom n) ((chomEquiv n).symm (complexRepresentation n (thetaHom g) p))) = _
  rw [e, h]
  rfl

/-- The Fischer–Riesz isomorphism as a continuous `ℝ`-linear map. -/
def litPhiCLM (n : ℕ) : ComplexCoefficients n →L[ℝ] LitCoeff n :=
  LinearMap.toContinuousLinearMap (litPhi n).toLinearMap

/-- Its inverse as a continuous `ℝ`-linear map. -/
def litPhiInvCLM (n : ℕ) : LitCoeff n →L[ℝ] ComplexCoefficients n :=
  LinearMap.toContinuousLinearMap (litPhi n).symm.toLinearMap

theorem litPhiCLM_apply (n : ℕ) (p : ComplexCoefficients n) : litPhiCLM n p = litPhi n p := rfl

theorem litPhiInvCLM_apply (n : ℕ) (φ : LitCoeff n) : litPhiInvCLM n φ = (litPhi n).symm φ := rfl

theorem litPhiInv_equivariant (n : ℕ) (g : RealGL) (φ : LitCoeff n) :
    (litPhi n).symm (litRep n g φ) = complexRepresentation n (thetaHom g) ((litPhi n).symm φ) := by
  apply (litPhi n).injective
  rw [LinearEquiv.apply_symm_apply, litPhi_equivariant, LinearEquiv.apply_symm_apply]

theorem litPhiCLM_comp_rep (n : ℕ) (g : RealGL) :
    (litPhiCLM n).comp (complexRepresentation n (thetaHom g)).toContinuousLinearMap =
      (litRep n g).comp (litPhiCLM n) :=
  ContinuousLinearMap.ext fun p => litPhi_equivariant n g p

theorem litPhiInvCLM_comp_rep (n : ℕ) (g : RealGL) :
    (litPhiInvCLM n).comp (litRep n g) =
      (complexRepresentation n (thetaHom g)).toContinuousLinearMap.comp (litPhiInvCLM n) :=
  ContinuousLinearMap.ext fun φ => litPhiInv_equivariant n g φ

/-! ### Literal dual-valued forms -/

/-- Values of `LitCoeff n`-valued `k`-forms. -/
abbrev FormL (n k : ℕ) := Coordinates [⋀^Fin k]→L[ℝ] LitCoeff n

/-- Equivariance of a `LitCoeff n`-valued form for the contragredient action of `Γ`. -/
def IsLitEquivariant (Γ : Subgroup RealGL) (n k : ℕ) (w : Coordinates → FormL n k) : Prop :=
  ∀ (γ : Γ) (x : Coordinates), x ∈ positiveCoordinates →
    pullRaw (coordinateAction (γ : RealGL)) w x =
      coefficientFormMap (E := Coordinates) (F := LitCoeff n) (G := LitCoeff n) (litRep n (γ : RealGL)) k (w x)

theorem projSupport_add_gen {M : Type*} [AddZeroClass M] (w z : Coordinates → M) :
    projSupport Γ (w + z) ⊆ projSupport Γ w ∪ projSupport Γ z := by
  unfold projSupport
  rw [← closure_union, ← image_union]
  exact closure_mono (image_mono (Function.support_add _ _))

theorem projSupport_smul_gen {M : Type*} [AddCommMonoid M] [Module ℝ M] (c : ℝ)
    (w : Coordinates → M) : projSupport Γ (c • w) ⊆ projSupport Γ w := by
  unfold projSupport
  exact closure_mono (image_mono (Function.support_const_smul_subset c w))

variable (Γ n k) in
/-- Smooth `Γ`-equivariant forms with values in the literal dual `StrongDual ℂ (Sym^n ℂ³)` for the
contragredient action, with compact closed projected support in the orbit space. -/
def LitForm : Submodule ℝ (Form (F := LitCoeff n) positiveCoordinates k) where
  carrier := {w | IsLitEquivariant Γ n k (w : Coordinates → FormL n k) ∧
    IsCompact (projSupport Γ (w : Coordinates → FormL n k))}
  zero_mem' := ⟨fun g x hx => by
      apply ContinuousAlternatingMap.ext
      intro v
      simp [pullRaw, coefficientFormMap], by simp [projSupport]⟩
  add_mem' := by
    rintro w z ⟨hw, hwc⟩ ⟨hz, hzc⟩
    refine ⟨fun g x hx => ?_, (hwc.union hzc).of_isClosed_subset isClosed_closure
      (projSupport_add_gen _ _)⟩
    apply ContinuousAlternatingMap.ext
    intro v
    simpa [pullRaw, coefficientFormMap] using
      congrArg (fun z : FormL n k => z v) (congrArg₂ (· + ·) (hw g x hx) (hz g x hx))
  smul_mem' := by
    rintro c w ⟨hw, hwc⟩
    refine ⟨fun g x hx => ?_, hwc.of_isClosed_subset isClosed_closure (projSupport_smul_gen c _)⟩
    apply ContinuousAlternatingMap.ext
    intro v
    simpa [pullRaw, coefficientFormMap] using
      congrArg (fun z : FormL n k => z v) (congrArg (c • ·) (hw g x hx))

/-- The underlying function of a literal dual form. -/
abbrev LitForm.fn (w : LitForm Γ n k) : Coordinates → FormL n k :=
  ((w : Form (F := LitCoeff n) positiveCoordinates k) : Coordinates → FormL n k)

theorem LitForm.equivariant (w : LitForm Γ n k) : IsLitEquivariant Γ n k (LitForm.fn w) := w.2.1

theorem LitForm.compact (w : LitForm Γ n k) : IsCompact (projSupport Γ (LitForm.fn w)) := w.2.2

theorem LitForm.smooth (w : LitForm Γ n k) : ContDiffOn ℝ ∞ (LitForm.fn w) positiveCoordinates :=
  Form.smooth (w : Form (F := LitCoeff n) positiveCoordinates k)

@[ext] theorem LitForm.ext {w z : LitForm Γ n k}
    (h : ∀ x ∈ positiveCoordinates, LitForm.fn w x = LitForm.fn z x) : w = z :=
  Subtype.ext (Form.ext h)

theorem litPhiInvCLM_comp_litPhiCLM (n : ℕ) : (litPhiInvCLM n).comp (litPhiCLM n) =
    ContinuousLinearMap.id ℝ _ :=
  ContinuousLinearMap.ext fun p => (litPhi n).symm_apply_apply p

theorem litPhiCLM_comp_litPhiInvCLM (n : ℕ) : (litPhiCLM n).comp (litPhiInvCLM n) =
    ContinuousLinearMap.id ℝ _ :=
  ContinuousLinearMap.ext fun p => (litPhi n).apply_symm_apply p

theorem isLitEquivariant_map (w : CFormCxD Γ n k) :
    IsLitEquivariant Γ n k
      (formMap (F := ComplexCoefficients n) (G := LitCoeff n) (litPhiCLM n) k (w : Form (F := ComplexCoefficients n) positiveCoordinates k)
        : Coordinates → FormL n k) := by
  intro γ x hx
  change pullRaw (coordinateAction (γ : RealGL)) (coefficientRaw (E := Coordinates) (F := ComplexCoefficients n) (G := LitCoeff n) (litPhiCLM n) (CFormCxD.fn w)) x =
    coefficientFormMap (E := Coordinates) (F := LitCoeff n) (G := LitCoeff n) (litRep n (γ : RealGL)) k (coefficientFormMap (E := Coordinates) (F := ComplexCoefficients n) (G := LitCoeff n) (litPhiCLM n) k (CFormCxD.fn w x))
  rw [pullRaw_coefficientRaw, CFormCxD.equivariant w γ x hx, cFM_comp, cFM_comp,
    litPhiCLM_comp_rep]

theorem isCxDualEquivariant_map (w : LitForm Γ n k) :
    IsCxDualEquivariant Γ n k
      (formMap (F := LitCoeff n) (G := ComplexCoefficients n) (litPhiInvCLM n) k (w : Form (F := LitCoeff n) positiveCoordinates k)
        : Coordinates → FormC n k) := by
  intro γ x hx
  change pullRaw (coordinateAction (γ : RealGL)) (coefficientRaw (E := Coordinates) (F := LitCoeff n) (G := ComplexCoefficients n) (litPhiInvCLM n) (LitForm.fn w)) x =
    coefficientFormMap (complexRepresentation n (thetaHom (γ : RealGL))).toContinuousLinearMap k
      (coefficientFormMap (E := Coordinates) (F := LitCoeff n) (G := ComplexCoefficients n) (litPhiInvCLM n) k (LitForm.fn w x))
  rw [pullRaw_coefficientRaw, LitForm.equivariant w γ x hx, cFM_comp, cFM_comp,
    litPhiInvCLM_comp_rep]

/-- Complex dual forms to literal dual forms. -/
def litTo (Γ : Subgroup RealGL) (n k : ℕ) : CFormCxD Γ n k →ₗ[ℝ] LitForm Γ n k where
  toFun w := ⟨formMap (F := ComplexCoefficients n) (G := LitCoeff n) (litPhiCLM n) k (w : Form (F := ComplexCoefficients n) positiveCoordinates k),
    isLitEquivariant_map w, (CFormCxD.compact w).of_isClosed_subset isClosed_closure
      (projSupport_map_subset (litPhiCLM n) _)⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

/-- Literal dual forms to complex dual forms. -/
def litFrom (Γ : Subgroup RealGL) (n k : ℕ) : LitForm Γ n k →ₗ[ℝ] CFormCxD Γ n k where
  toFun w := ⟨formMap (F := LitCoeff n) (G := ComplexCoefficients n) (litPhiInvCLM n) k (w : Form (F := LitCoeff n) positiveCoordinates k),
    isCxDualEquivariant_map w, (LitForm.compact w).of_isClosed_subset isClosed_closure
      (projSupport_map_subset (litPhiInvCLM n) _)⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

theorem litTo_fn (w : CFormCxD Γ n k) (x : Coordinates) :
    LitForm.fn (litTo Γ n k w) x = coefficientFormMap (E := Coordinates) (F := ComplexCoefficients n) (G := LitCoeff n) (litPhiCLM n) k (CFormCxD.fn w x) := rfl

theorem litFrom_fn (w : LitForm Γ n k) (x : Coordinates) :
    CFormCxD.fn (litFrom Γ n k w) x = coefficientFormMap (E := Coordinates) (F := LitCoeff n) (G := ComplexCoefficients n) (litPhiInvCLM n) k (LitForm.fn w x) := rfl

/-- **The identification of the literal dual-valued forms with the complex dual forms.** -/
def litForms (Γ : Subgroup RealGL) (n k : ℕ) : CFormCxD Γ n k ≃ₗ[ℝ] LitForm Γ n k :=
  LinearEquiv.ofLinearMap (litTo Γ n k) (litFrom Γ n k)
    (LinearMap.ext fun w => LitForm.ext fun x _ => by
      change coefficientFormMap (E := Coordinates) (F := ComplexCoefficients n) (G := LitCoeff n) (litPhiCLM n) k (coefficientFormMap (E := Coordinates) (F := LitCoeff n) (G := ComplexCoefficients n) (litPhiInvCLM n) k (LitForm.fn w x)) = _
      rw [cFM_comp, litPhiCLM_comp_litPhiInvCLM, cFM_id]; rfl)
    (LinearMap.ext fun w => CFormCxD.ext fun x _ => by
      change coefficientFormMap (E := Coordinates) (F := LitCoeff n) (G := ComplexCoefficients n) (litPhiInvCLM n) k (coefficientFormMap (E := Coordinates) (F := ComplexCoefficients n) (G := LitCoeff n) (litPhiCLM n) k (CFormCxD.fn w x)) = _
      rw [cFM_comp, litPhiInvCLM_comp_litPhiCLM, cFM_id]; rfl)

theorem litForms_fn (w : CFormCxD Γ n k) (x : Coordinates) :
    LitForm.fn (litForms Γ n k w) x = coefficientFormMap (E := Coordinates) (F := ComplexCoefficients n) (G := LitCoeff n) (litPhiCLM n) k (CFormCxD.fn w x) := rfl

theorem litForms_symm_fn (w : LitForm Γ n k) (x : Coordinates) :
    CFormCxD.fn ((litForms Γ n k).symm w) x = coefficientFormMap (E := Coordinates) (F := LitCoeff n) (G := ComplexCoefficients n) (litPhiInvCLM n) k (LitForm.fn w x) :=
  rfl

/-- The exterior derivative of literal dual forms. -/
def LitForm.d (h : Admissible Γ) (n k : ℕ) : LitForm Γ n k →ₗ[ℝ] LitForm Γ n (k + 1) :=
  ((litForms Γ n (k + 1)).toLinearMap.comp (CFormCxD.d h n k)).comp (litForms Γ n k).symm.toLinearMap

theorem LitForm.d_apply (h : Admissible Γ) (w : LitForm Γ n k) {x : Coordinates}
    (hx : x ∈ positiveCoordinates) :
    LitForm.fn (LitForm.d h n k w) x = extDeriv (LitForm.fn w) x := by
  have hdiff : DifferentiableAt ℝ (CFormCxD.fn ((litForms Γ n k).symm w)) x :=
    ((CFormCxD.smooth _ x hx).contDiffAt (isOpen_positiveCoordinates.mem_nhds hx)).differentiableAt
      (by simp)
  change coefficientFormMap (E := Coordinates) (F := ComplexCoefficients n) (G := LitCoeff n) (litPhiCLM n) (k + 1)
    (CFormCxD.fn (CFormCxD.d h n k ((litForms Γ n k).symm w)) x) = _
  rw [CFormCxD.d_apply h _ hx]
  have e : LitForm.fn w = coefficientRaw (E := Coordinates) (F := ComplexCoefficients n) (G := LitCoeff n) (litPhiCLM n) (CFormCxD.fn ((litForms Γ n k).symm w)) := by
    funext y
    change _ = coefficientFormMap (E := Coordinates) (F := ComplexCoefficients n) (G := LitCoeff n) (litPhiCLM n) k (coefficientFormMap (E := Coordinates) (F := LitCoeff n) (G := ComplexCoefficients n) (litPhiInvCLM n) k (LitForm.fn w y))
    rw [cFM_comp, litPhiCLM_comp_litPhiInvCLM, cFM_id]
  rw [e, extDeriv_coefficientRaw _ hdiff]

theorem litForms_d (h : Admissible Γ) (a : CFormCxD Γ n k) :
    LitForm.d h n k (litForms Γ n k a) = litForms Γ n (k + 1) (CFormCxD.d h n k a) := by
  change (litForms Γ n (k + 1)) (CFormCxD.d h n k ((litForms Γ n k).symm (litForms Γ n k a))) = _
  rw [LinearEquiv.symm_apply_apply]

/-! ### The `L²` structure, by transport of the Hermitian dual metric -/

/-- The Hermitian `L²` pairing of literal dual forms over the orbit space: the pointwise metric is the
dual flat metric of the coefficient system tensored with the metric of the exterior powers
(see `litCoeff_normSq_frame` for its coefficient part), transported along `litForms`. -/
def litL2 (a b : LitForm Γ n k) : ℝ := l2CxD ((litForms Γ n k).symm a) ((litForms Γ n k).symm b)

/-- The squared `L²` norm of a literal dual form. -/
def litNormSq (a : LitForm Γ n k) : ℝ := litL2 a a

theorem litL2_litForms (a b : CFormCxD Γ n k) :
    litL2 (litForms Γ n k a) (litForms Γ n k b) = l2CxD a b := by
  unfold litL2
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]

theorem litNormSq_litForms (a : CFormCxD Γ n k) :
    litNormSq (litForms Γ n k a) = normSqCxD a := litL2_litForms a a

/-- `e` is a formal adjoint of the exterior derivative of literal dual forms at `b`. -/
def IsLitFormalAdjoint (h : Admissible Γ) (n k : ℕ) (b : LitForm Γ n (k + 1)) (e : LitForm Γ n k) :
    Prop :=
  ∀ a : LitForm Γ n k, litL2 (LitForm.d h n k a) b = litL2 a e

theorem isLitFormalAdjoint_iff (h : Admissible Γ) (b : CFormCxD Γ n (k + 1)) (e : CFormCxD Γ n k) :
    IsLitFormalAdjoint h n k (litForms Γ n (k + 1) b) (litForms Γ n k e) ↔
      IsCxDualFormalAdjoint h n k b e := by
  have h1 : ∀ a : CFormCxD Γ n k, litL2 (LitForm.d h n k (litForms Γ n k a))
      (litForms Γ n (k + 1) b) = l2CxD (CFormCxD.d h n k a) b := fun a => by
    rw [litForms_d h a]
    exact litL2_litForms _ _
  constructor
  · intro H a
    exact (h1 a).symm.trans ((H (litForms Γ n k a)).trans (litL2_litForms a e))
  · intro H a
    obtain ⟨a', rfl⟩ := (litForms Γ n k).surjective a
    exact (h1 a').trans ((H a').trans (litL2_litForms a' e).symm)

/-- **General coercivity for forms with values in the literal complex dual.**  There is `c_n > 0`,
independent of the admissible group `Γ`, such that for every compactly supported smooth
`Γ`-equivariant form with values in `StrongDual ℂ (Sym^n ℂ³)` (contragredient action, dual operator
norm), `c ‖a‖² ≤ ‖d a‖²` in degree `0` and `c ‖a‖² ≤ ‖e‖² + ‖d a‖²` whenever `e` is a formal adjoint
of `d` at `a`. -/
theorem general_coercivity_lit (n : ℕ) (hn : 0 < n) :
    ∃ c : ℝ, 0 < c ∧ ∀ Γ : Subgroup RealGL, ∀ h : Admissible Γ,
      (∀ a : LitForm Γ n 0, c * litNormSq a ≤ litNormSq (LitForm.d h n 0 a)) ∧
        ∀ (k : ℕ) (a : LitForm Γ n (k + 1)) (e : LitForm Γ n k),
          IsLitFormalAdjoint h n k a e →
            c * litNormSq a ≤ litNormSq e + litNormSq (LitForm.d h n (k + 1) a) := by
  obtain ⟨c, hc, H⟩ := general_coercivity_complex_dual n hn
  refine ⟨c, hc, fun Γ h => ⟨fun a => ?_, fun k a e hae => ?_⟩⟩
  · obtain ⟨a', rfl⟩ := (litForms Γ n 0).surjective a
    have h1 : litNormSq (LitForm.d h n 0 (litForms Γ n 0 a')) = normSqCxD (CFormCxD.d h n 0 a') := by
      rw [litForms_d h a']
      exact litNormSq_litForms _
    calc c * litNormSq (litForms Γ n 0 a') = c * normSqCxD a' :=
          congrArg (c * ·) (litNormSq_litForms a')
      _ ≤ normSqCxD (CFormCxD.d h n 0 a') := (H Γ h).1 a'
      _ = _ := h1.symm
  · obtain ⟨a', rfl⟩ := (litForms Γ n (k + 1)).surjective a
    obtain ⟨e', rfl⟩ := (litForms Γ n k).surjective e
    have h1 : litNormSq (LitForm.d h n (k + 1) (litForms Γ n (k + 1) a')) =
        normSqCxD (CFormCxD.d h n (k + 1) a') := by
      rw [litForms_d h a']
      exact litNormSq_litForms _
    calc c * litNormSq (litForms Γ n (k + 1) a') = c * normSqCxD a' :=
          congrArg (c * ·) (litNormSq_litForms a')
      _ ≤ normSqCxD e' + normSqCxD (CFormCxD.d h n (k + 1) a') :=
          (H Γ h).2 k a' e' ((isLitFormalAdjoint_iff h a' e').mp hae)
      _ = _ := congrArg₂ (· + ·) (litNormSq_litForms e').symm h1.symm

/-- The coefficient part of the metric: at the point `x` with frame `g`, the literal dual norm of
`ρ*(g)⁻¹ φ` squared equals the Hermitian coefficient metric `cplxBilin` (the Fischer metric at the
Cartan point `ι x`) of the corresponding complex polynomial. -/
theorem litCoeff_normSq_frame {x : Coordinates} (hx : x ∈ positiveCoordinates) (g : RealGL)
    (hg : determinantNormalize (reconstruct x) =
      (g : Matrix (Fin 3) (Fin 3) ℝ) * (g : Matrix (Fin 3) (Fin 3) ℝ).transpose)
    (p : ComplexCoefficients n) :
    ‖litRep n g⁻¹ (litPhi n p)‖ ^ 2 =
      cplxBilin n (coordinateCoefficientBilin n (iotaC x)) p p := by
  have h := dualNorm_metric_frame hx g hg n (litPhi n p).toStrong
  have e : (InnerProductSpace.toDual ℂ (CHom n)).symm (litPhi n p).toStrong = (chomEquiv n).symm p :=
    (InnerProductSpace.toDual ℂ (CHom n)).symm_apply_apply ((chomEquiv n).symm p)
  rw [e, LinearEquiv.apply_symm_apply] at h
  have e2 : litRep n g⁻¹ (litPhi n p) =
      LitCoeff.mk n ((litPhi n p).toStrong.comp (rhoC n g).toContinuousLinearMap) := by
    change LitCoeff.mk n ((litPhi n p).toStrong.comp (rhoC n g⁻¹⁻¹).toContinuousLinearMap) = _
    rw [inv_inv]
  rw [e2]
  exact h

/-- **Tier B for literal dual forms.**  A closed literal dual two-form is exact with a smooth
equivariant primitive. -/
theorem Admissible.closed_compact_exact_lit (h : Admissible Γ) (hn : 0 < n)
    (ζ : LitForm Γ n 2) (hζ : LitForm.d h n 2 ζ = 0) :
    ∃ η : Coordinates → FormL n 1, ContDiffOn ℝ ∞ η positiveCoordinates ∧
      (∀ x ∉ positiveCoordinates, η x = 0) ∧ IsLitEquivariant Γ n 1 η ∧
      ∀ x ∈ positiveCoordinates, extDeriv η x = LitForm.fn ζ x := by
  obtain ⟨ζ', rfl⟩ := (litForms Γ n 2).surjective ζ
  rw [litForms_d] at hζ
  have hζ' : CFormCxD.d h n 2 ζ' = 0 := (litForms Γ n 3).injective (hζ.trans (litForms Γ n 3).map_zero.symm)
  obtain ⟨η, h1, h2, h3, h4⟩ := Admissible.closed_compact_exact_complex_dual h hn ζ' hζ'
  refine ⟨coefficientRaw (E := Coordinates) (F := ComplexCoefficients n) (G := LitCoeff n)
    (litPhiCLM n) η, coefficientRaw_smooth _ h1, fun x hx => ?_, fun γ x hx => ?_, fun x hx => ?_⟩
  · change coefficientFormMap (E := Coordinates) (F := ComplexCoefficients n) (G := LitCoeff n)
      (litPhiCLM n) 1 (η x) = 0
    rw [h2 x hx]
    exact TernaryPoly.PolynomialFormCoordinates.clm_map_zero _
  · change pullRaw (coordinateAction (γ : RealGL))
        (coefficientRaw (E := Coordinates) (F := ComplexCoefficients n) (G := LitCoeff n)
          (litPhiCLM n) η) x =
      coefficientFormMap (E := Coordinates) (F := LitCoeff n) (G := LitCoeff n) (litRep n (γ : RealGL)) 1
        (coefficientFormMap (E := Coordinates) (F := ComplexCoefficients n) (G := LitCoeff n)
          (litPhiCLM n) 1 (η x))
    rw [pullRaw_coefficientRaw, h3 γ x hx, cFM_comp, cFM_comp, litPhiCLM_comp_rep]
  · have hd : DifferentiableAt ℝ η x :=
      ((h1 x hx).contDiffAt (isOpen_positiveCoordinates.mem_nhds hx)).differentiableAt (by simp)
    rw [extDeriv_coefficientRaw _ hd, h4 x hx]
    rfl

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
