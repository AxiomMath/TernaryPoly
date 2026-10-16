module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Variants.ComplexCoefficients
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Variants.DualMain
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Variants.Complex

@[expose] public section


/-!
# General coercivity, complex coefficients: forms with values in `Sym^n ℂ³`

`CFormCx Γ n k` is the space of smooth `Γ`-equivariant `k`-forms on the positive coordinates with
values in the complexified polynomial space `ComplexCoefficients n = Sym^n ℂ³` (homogeneous complex
polynomials of degree `n`, acted on by `GL₃(ℝ)` through `complexRepresentation`), with compact closed
projected support in the orbit space.  Its elements are identified, by taking real and imaginary
parts of the coefficients (`cxEquiv`, built from `reImEquiv` of `Variants/ComplexCoefficients`), with
pairs of real forms; this identification commutes with the exterior derivative (`toPairs_d`), and
carries the Hermitian `L²` pairing `l2Cx`, whose pointwise integrand is the intrinsic metric
`formPairingC` of the complexified bundle (`scalarPairingCx_proj`), to the sum of the two real `L²`
pairings (`l2Cx_eq_pairs`).  Hence the coercivity estimate for real coefficients gives
`general_coercivity_complex_forms` with the same constant.

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

/-! ### Coefficient maps -/

section CoefficientMaps

variable (n : ℕ)

/-- Real part of a complex coefficient, as a continuous linear map. -/
def reL : ComplexCoefficients n →L[ℝ] Coefficients n :=
  (ContinuousLinearMap.fst ℝ (Coefficients n) (Coefficients n)).comp
    (reImCLE n).toContinuousLinearMap

/-- Imaginary part of a complex coefficient. -/
def imL : ComplexCoefficients n →L[ℝ] Coefficients n :=
  (ContinuousLinearMap.snd ℝ (Coefficients n) (Coefficients n)).comp
    (reImCLE n).toContinuousLinearMap

/-- The real coefficients inside the complex ones. -/
def embRe : Coefficients n →L[ℝ] ComplexCoefficients n :=
  (reImCLE n).symm.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ (Coefficients n) (Coefficients n))

/-- `i` times the real coefficients inside the complex ones. -/
def embIm : Coefficients n →L[ℝ] ComplexCoefficients n :=
  (reImCLE n).symm.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ (Coefficients n) (Coefficients n))

theorem reL_embRe (q : Coefficients n) : reL n (embRe n q) = q := by
  simp [reL, embRe]

theorem imL_embRe (q : Coefficients n) : imL n (embRe n q) = 0 := by
  simp [imL, embRe]

theorem reL_embIm (q : Coefficients n) : reL n (embIm n q) = 0 := by
  simp [reL, embIm]

theorem imL_embIm (q : Coefficients n) : imL n (embIm n q) = q := by
  simp [imL, embIm]

theorem embRe_add_embIm (p : ComplexCoefficients n) :
    embRe n (reL n p) + embIm n (imL n p) = p := by
  have : (reImCLE n).symm ((reImCLE n p).1, 0) + (reImCLE n).symm (0, (reImCLE n p).2) = p := by
    rw [← map_add]
    simp
  simpa [embRe, embIm, reL, imL] using this

theorem reL_complexRep (g : RealGL) (p : ComplexCoefficients n) :
    reL n (complexRepresentation n g p) = realHomogeneousAction n g (reL n p) := by
  have := congrArg Prod.fst (reImEquiv_complexRepresentation n g p)
  simpa [reL, reImCLE] using this

theorem imL_complexRep (g : RealGL) (p : ComplexCoefficients n) :
    imL n (complexRepresentation n g p) = realHomogeneousAction n g (imL n p) := by
  have := congrArg Prod.snd (reImEquiv_complexRepresentation n g p)
  simpa [imL, reImCLE] using this

end CoefficientMaps

/-! ### Form-level coefficient maps -/

section FormMaps

variable {F G H : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
  [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem cFM_comp (L : G →L[ℝ] H) (M : F →L[ℝ] G) (k : ℕ) (a : Coordinates [⋀^Fin k]→L[ℝ] F) :
    coefficientFormMap L k (coefficientFormMap M k a) = coefficientFormMap (L.comp M) k a := by
  ext v
  simp [coefficientFormMap]

theorem cFM_compCLM (L : F →L[ℝ] G) (k : ℕ) (a : Coordinates [⋀^Fin k]→L[ℝ] F)
    (M : Coordinates →L[ℝ] Coordinates) :
    (coefficientFormMap L k a).compContinuousLinearMap M =
      coefficientFormMap L k (a.compContinuousLinearMap M) := by
  ext v
  simp [coefficientFormMap]

theorem cFM_add (L M : F →L[ℝ] G) (k : ℕ) (a : Coordinates [⋀^Fin k]→L[ℝ] F) :
    coefficientFormMap (L + M) k a = coefficientFormMap L k a + coefficientFormMap M k a := by
  ext v
  simp [coefficientFormMap]

theorem cFM_id (k : ℕ) (a : Coordinates [⋀^Fin k]→L[ℝ] F) :
    coefficientFormMap (ContinuousLinearMap.id ℝ F) k a = a := by
  ext v
  simp [coefficientFormMap]

theorem pullRaw_coefficientRaw (L : F →L[ℝ] G) {k : ℕ}
    (f : Coordinates → Coordinates) (w : Coordinates → Coordinates [⋀^Fin k]→L[ℝ] F)
    (x : Coordinates) :
    pullRaw f (coefficientRaw L w) x = coefficientFormMap L k (pullRaw f w x) :=
  cFM_compCLM L k _ _

/-- A continuous linear map of coefficients, applied to smooth forms. -/
def formMap (L : F →L[ℝ] G) (k : ℕ) : Form (F := F) positiveCoordinates k →ₗ[ℝ]
    Form (F := G) positiveCoordinates k where
  toFun w := ⟨coefficientRaw L (w : Coordinates → Coordinates [⋀^Fin k]→L[ℝ] F),
    coefficientRaw_smooth L (Form.smooth w), fun x hx => by
      change coefficientFormMap L k ((w : Coordinates → Coordinates [⋀^Fin k]→L[ℝ] F) x) = 0
      rw [Form.outside w hx]
      exact map_zero _⟩
  map_add' w z := by
    apply Subtype.ext
    funext x
    exact map_add (coefficientFormMap L k) _ _
  map_smul' c w := by
    apply Subtype.ext
    funext x
    exact map_smul (coefficientFormMap L k) c _

theorem formMap_apply (L : F →L[ℝ] G) {k : ℕ} (w : Form (F := F) positiveCoordinates k)
    (x : Coordinates) :
    (formMap L k w : Coordinates → Coordinates [⋀^Fin k]→L[ℝ] G) x =
      coefficientFormMap L k ((w : Coordinates → Coordinates [⋀^Fin k]→L[ℝ] F) x) := rfl

end FormMaps

/-! ### The space of complex-coefficient forms -/

/-- Values of `ℂ`-polynomial-valued `k`-forms. -/
abbrev FormC (n k : ℕ) := Coordinates [⋀^Fin k]→L[ℝ] ComplexCoefficients n

/-- Equivariance of a `Sym^n ℂ³`-valued form for the substitution action of `Γ`. -/
def IsCxEquivariant (Γ : Subgroup RealGL) (n k : ℕ) (w : Coordinates → FormC n k) : Prop :=
  ∀ (γ : Γ) (x : Coordinates), x ∈ positiveCoordinates →
    pullRaw (coordinateAction (γ : RealGL)) w x =
      coefficientFormMap (complexRepresentation n (γ : RealGL)).toContinuousLinearMap k (w x)

variable {Γ : Subgroup RealGL} {n k : ℕ}

theorem IsCxEquivariant.zero : IsCxEquivariant Γ n k 0 := by
  intro g x hx
  apply ContinuousAlternatingMap.ext
  intro v
  simp [pullRaw, coefficientFormMap]

theorem IsCxEquivariant.add {w z : Coordinates → FormC n k} (hw : IsCxEquivariant Γ n k w)
    (hz : IsCxEquivariant Γ n k z) : IsCxEquivariant Γ n k (w + z) := by
  intro g x hx
  apply ContinuousAlternatingMap.ext
  intro v
  simpa [pullRaw, coefficientFormMap] using
    congrArg (fun z : FormC n k => z v) (congrArg₂ (· + ·) (hw g x hx) (hz g x hx))

theorem IsCxEquivariant.smul (c : ℝ) {w : Coordinates → FormC n k} (hw : IsCxEquivariant Γ n k w) :
    IsCxEquivariant Γ n k (c • w) := by
  intro g x hx
  apply ContinuousAlternatingMap.ext
  intro v
  simpa [pullRaw, coefficientFormMap] using
    congrArg (fun z : FormC n k => z v) (congrArg (c • ·) (hw g x hx))

theorem projSupport_zero' : projSupport Γ (0 : Coordinates → FormC n k) = ∅ := by
  simp [projSupport]

theorem projSupport_add' (w z : Coordinates → FormC n k) :
    projSupport Γ (w + z) ⊆ projSupport Γ w ∪ projSupport Γ z := by
  unfold projSupport
  rw [← closure_union, ← image_union]
  exact closure_mono (image_mono (Function.support_add _ _))

theorem projSupport_smul' (c : ℝ) (w : Coordinates → FormC n k) :
    projSupport Γ (c • w) ⊆ projSupport Γ w := by
  unfold projSupport
  exact closure_mono (image_mono (Function.support_const_smul_subset c w))

variable (Γ n k) in
/-- Smooth `Γ`-equivariant forms with values in the complexified polynomial space `Sym^n ℂ³`, whose
closed projected support in the orbit space is compact. -/
def CFormCx : Submodule ℝ (Form (F := ComplexCoefficients n) positiveCoordinates k) where
  carrier := {w | IsCxEquivariant Γ n k (w : Coordinates → FormC n k) ∧
    IsCompact (projSupport Γ (w : Coordinates → FormC n k))}
  zero_mem' := ⟨IsCxEquivariant.zero, by simp [projSupport_zero']⟩
  add_mem' := by
    rintro w z ⟨hw, hwc⟩ ⟨hz, hzc⟩
    exact ⟨hw.add hz, (hwc.union hzc).of_isClosed_subset isClosed_closure (projSupport_add' _ _)⟩
  smul_mem' := by
    rintro c w ⟨hw, hwc⟩
    exact ⟨hw.smul c, hwc.of_isClosed_subset isClosed_closure (projSupport_smul' c _)⟩

/-- The underlying function of a complex-coefficient form. -/
abbrev CFormCx.fn (w : CFormCx Γ n k) : Coordinates → FormC n k :=
  ((w : Form (F := ComplexCoefficients n) positiveCoordinates k) : Coordinates → FormC n k)

theorem CFormCx.equivariant (w : CFormCx Γ n k) : IsCxEquivariant Γ n k (CFormCx.fn w) := w.2.1

theorem CFormCx.compact (w : CFormCx Γ n k) : IsCompact (projSupport Γ (CFormCx.fn w)) := w.2.2

theorem CFormCx.smooth (w : CFormCx Γ n k) : ContDiffOn ℝ ∞ (CFormCx.fn w) positiveCoordinates :=
  Form.smooth (w : Form (F := ComplexCoefficients n) positiveCoordinates k)

theorem CFormCx.outside (w : CFormCx Γ n k) {x : Coordinates} (hx : x ∉ positiveCoordinates) :
    (CFormCx.fn w) x = 0 :=
  Form.outside (w : Form (F := ComplexCoefficients n) positiveCoordinates k) hx

@[ext] theorem CFormCx.ext {w z : CFormCx Γ n k}
    (h : ∀ x ∈ positiveCoordinates, (CFormCx.fn w) x = (CFormCx.fn z) x) : w = z :=
  Subtype.ext (Form.ext h)

/-! ### Compatibility of the coefficient maps with the actions -/

theorem reL_comp_rep (g : RealGL) :
    (reL n).comp (complexRepresentation n g).toContinuousLinearMap =
      (realHomogeneousAction n g).toContinuousLinearMap.comp (reL n) :=
  ContinuousLinearMap.ext (reL_complexRep n g)

theorem imL_comp_rep (g : RealGL) :
    (imL n).comp (complexRepresentation n g).toContinuousLinearMap =
      (realHomogeneousAction n g).toContinuousLinearMap.comp (imL n) :=
  ContinuousLinearMap.ext (imL_complexRep n g)

theorem rep_comp_embRe (g : RealGL) :
    (complexRepresentation n g).toContinuousLinearMap.comp (embRe n) =
      (embRe n).comp (realHomogeneousAction n g).toContinuousLinearMap := by
  ext1 q
  have h := embRe_add_embIm n (complexRepresentation n g (embRe n q))
  rw [reL_complexRep, imL_complexRep, reL_embRe, imL_embRe, map_zero, map_zero] at h
  simpa using h.symm

theorem rep_comp_embIm (g : RealGL) :
    (complexRepresentation n g).toContinuousLinearMap.comp (embIm n) =
      (embIm n).comp (realHomogeneousAction n g).toContinuousLinearMap := by
  ext1 q
  have h := embRe_add_embIm n (complexRepresentation n g (embIm n q))
  rw [reL_complexRep, imL_complexRep, reL_embIm, imL_embIm, map_zero, map_zero] at h
  simpa using h.symm

theorem reL_comp_embRe : (reL n).comp (embRe n) = ContinuousLinearMap.id ℝ _ :=
  ContinuousLinearMap.ext (reL_embRe n)

theorem reL_comp_embIm : (reL n).comp (embIm n) = 0 := ContinuousLinearMap.ext (reL_embIm n)

theorem imL_comp_embRe : (imL n).comp (embRe n) = 0 := ContinuousLinearMap.ext (imL_embRe n)

theorem imL_comp_embIm : (imL n).comp (embIm n) = ContinuousLinearMap.id ℝ _ :=
  ContinuousLinearMap.ext (imL_embIm n)

theorem embRe_reL_add : (embRe n).comp (reL n) + (embIm n).comp (imL n) =
    ContinuousLinearMap.id ℝ _ :=
  ContinuousLinearMap.ext (embRe_add_embIm n)

theorem cFM_zero {F G : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
    [NormedSpace ℝ G] (k : ℕ) (a : Coordinates [⋀^Fin k]→L[ℝ] F) :
    coefficientFormMap (0 : F →L[ℝ] G) k a = 0 := by
  ext v
  simp [coefficientFormMap]

theorem pullRaw_add' {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Coordinates → Coordinates) (a b : Coordinates → Coordinates [⋀^Fin k]→L[ℝ] F)
    (x : Coordinates) : pullRaw f (a + b) x = pullRaw f a x + pullRaw f b x := by
  ext v
  simp [pullRaw]

theorem projSupport_map_subset {F G : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : F →L[ℝ] G)
    (w : Coordinates → Coordinates [⋀^Fin k]→L[ℝ] F) :
    projSupport Γ (coefficientRaw L w) ⊆ projSupport Γ w := by
  unfold projSupport
  refine closure_mono (image_mono ?_)
  intro x hx hw
  apply hx
  change coefficientFormMap L k (w x) = 0
  rw [hw]
  exact map_zero _

theorem isEquivariant_re (w : CFormCx Γ n k) :
    IsEquivariant Γ n k (formMap (reL n) k (w : Form (F := ComplexCoefficients n) positiveCoordinates k)
      : Coordinates → FormValue n k) := by
  intro γ x hx
  change pullRaw (coordinateAction (γ : RealGL)) (coefficientRaw (reL n) (CFormCx.fn w)) x =
    coefficientFormMap (coefficientRep Γ n γ).toContinuousLinearMap k
      (coefficientFormMap (reL n) k (CFormCx.fn w x))
  rw [pullRaw_coefficientRaw, CFormCx.equivariant w γ x hx, cFM_comp, cFM_comp,
    reL_comp_rep (γ : RealGL)]
  rfl

theorem isEquivariant_im (w : CFormCx Γ n k) :
    IsEquivariant Γ n k (formMap (imL n) k (w : Form (F := ComplexCoefficients n) positiveCoordinates k)
      : Coordinates → FormValue n k) := by
  intro γ x hx
  change pullRaw (coordinateAction (γ : RealGL)) (coefficientRaw (imL n) (CFormCx.fn w)) x =
    coefficientFormMap (coefficientRep Γ n γ).toContinuousLinearMap k
      (coefficientFormMap (imL n) k (CFormCx.fn w x))
  rw [pullRaw_coefficientRaw, CFormCx.equivariant w γ x hx, cFM_comp, cFM_comp,
    imL_comp_rep (γ : RealGL)]
  rfl

/-- The real and imaginary parts of a complex-coefficient form. -/
def toPairs (Γ : Subgroup RealGL) (n k : ℕ) :
    CFormCx Γ n k →ₗ[ℝ] CForm Γ n k × CForm Γ n k where
  toFun w := (⟨formMap (reL n) k (w : Form (F := ComplexCoefficients n) positiveCoordinates k),
      isEquivariant_re w, (CFormCx.compact w).of_isClosed_subset isClosed_closure
        (projSupport_map_subset (reL n) _)⟩,
    ⟨formMap (imL n) k (w : Form (F := ComplexCoefficients n) positiveCoordinates k),
      isEquivariant_im w, (CFormCx.compact w).of_isClosed_subset isClosed_closure
        (projSupport_map_subset (imL n) _)⟩)
  map_add' _ _ := Prod.ext (Subtype.ext (map_add _ _ _)) (Subtype.ext (map_add _ _ _))
  map_smul' _ _ := Prod.ext (Subtype.ext (map_smul _ _ _)) (Subtype.ext (map_smul _ _ _))

theorem isCxEquivariant_ofPairs (a b : CForm Γ n k) :
    IsCxEquivariant Γ n k (formMap (embRe n) k (a : Form (F := Coefficients n) positiveCoordinates k) +
      formMap (embIm n) k (b : Form (F := Coefficients n) positiveCoordinates k) :
        Form (F := ComplexCoefficients n) positiveCoordinates k) := by
  intro γ x hx
  change pullRaw (coordinateAction (γ : RealGL))
      (coefficientRaw (embRe n) (CForm.fn a) + coefficientRaw (embIm n) (CForm.fn b)) x =
    coefficientFormMap (complexRepresentation n (γ : RealGL)).toContinuousLinearMap k
      (coefficientFormMap (embRe n) k (CForm.fn a x) + coefficientFormMap (embIm n) k (CForm.fn b x))
  rw [pullRaw_add', pullRaw_coefficientRaw, pullRaw_coefficientRaw, CForm.equivariant a γ x hx,
    CForm.equivariant b γ x hx, map_add, cFM_comp, cFM_comp, cFM_comp, cFM_comp]
  have e1 : (embRe n).comp (coefficientRep Γ n γ).toContinuousLinearMap =
      (complexRepresentation n (γ : RealGL)).toContinuousLinearMap.comp (embRe n) :=
    (rep_comp_embRe (γ : RealGL)).symm
  have e2 : (embIm n).comp (coefficientRep Γ n γ).toContinuousLinearMap =
      (complexRepresentation n (γ : RealGL)).toContinuousLinearMap.comp (embIm n) :=
    (rep_comp_embIm (γ : RealGL)).symm
  rw [e1, e2]

/-- A complex-coefficient form from its real and imaginary parts. -/
def ofPairs (Γ : Subgroup RealGL) (n k : ℕ) :
    CForm Γ n k × CForm Γ n k →ₗ[ℝ] CFormCx Γ n k where
  toFun p := ⟨formMap (embRe n) k (p.1 : Form (F := Coefficients n) positiveCoordinates k) +
      formMap (embIm n) k (p.2 : Form (F := Coefficients n) positiveCoordinates k),
    isCxEquivariant_ofPairs p.1 p.2,
    ((CForm.compact p.1).of_isClosed_subset isClosed_closure
        (projSupport_map_subset (embRe n) _) |>.union
      ((CForm.compact p.2).of_isClosed_subset isClosed_closure
        (projSupport_map_subset (embIm n) _))).of_isClosed_subset isClosed_closure
      (projSupport_add' _ _)⟩
  map_add' p q := Subtype.ext (by
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, map_add]
    abel)
  map_smul' c p := Subtype.ext (by
    simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, map_smul, smul_add]
    rfl)

theorem toPairs_fst_fn (w : CFormCx Γ n k) :
    CForm.fn (toPairs Γ n k w).1 = coefficientRaw (reL n) (CFormCx.fn w) := rfl

theorem toPairs_snd_fn (w : CFormCx Γ n k) :
    CForm.fn (toPairs Γ n k w).2 = coefficientRaw (imL n) (CFormCx.fn w) := rfl

theorem ofPairs_fn (p : CForm Γ n k × CForm Γ n k) (x : Coordinates) :
    CFormCx.fn (ofPairs Γ n k p) x =
      coefficientFormMap (embRe n) k (CForm.fn p.1 x) +
        coefficientFormMap (embIm n) k (CForm.fn p.2 x) := rfl

theorem toPairs_comp_ofPairs_fst_aux (p : CForm Γ n k × CForm Γ n k) :
    ((toPairs Γ n k) ((ofPairs Γ n k) p)).1 = p.1 :=
  CForm.ext fun x _ => by
    change coefficientFormMap (reL n) k (coefficientFormMap (embRe n) k (CForm.fn p.1 x) +
      coefficientFormMap (embIm n) k (CForm.fn p.2 x)) = CForm.fn p.1 x
    rw [TernaryPoly.PolynomialFormCoordinates.clm_map_add, cFM_comp, cFM_comp, reL_comp_embRe,
      reL_comp_embIm, cFM_id, cFM_zero, add_zero]

theorem toPairs_comp_ofPairs_snd_aux (p : CForm Γ n k × CForm Γ n k) :
    ((toPairs Γ n k) ((ofPairs Γ n k) p)).2 = p.2 :=
  CForm.ext fun x _ => by
    change coefficientFormMap (imL n) k (coefficientFormMap (embRe n) k (CForm.fn p.1 x) +
      coefficientFormMap (embIm n) k (CForm.fn p.2 x)) = CForm.fn p.2 x
    rw [TernaryPoly.PolynomialFormCoordinates.clm_map_add, cFM_comp, cFM_comp, imL_comp_embRe,
      imL_comp_embIm, cFM_id, cFM_zero, zero_add]

theorem ofPairs_comp_toPairs_aux (w : CFormCx Γ n k) : (ofPairs Γ n k) ((toPairs Γ n k) w) = w :=
  CFormCx.ext fun x _ => by
    change coefficientFormMap (embRe n) k (coefficientFormMap (reL n) k (CFormCx.fn w x)) +
      coefficientFormMap (embIm n) k (coefficientFormMap (imL n) k (CFormCx.fn w x)) =
        CFormCx.fn w x
    rw [cFM_comp, cFM_comp, ← cFM_add, embRe_reL_add, cFM_id]

/-- **The real/imaginary bridge for forms.**  Compactly supported smooth `Γ`-equivariant forms with
values in `Sym^n ℂ³` are the same as pairs of such forms with values in `Sym^n ℝ³`. -/
def cxEquiv (Γ : Subgroup RealGL) (n k : ℕ) : CFormCx Γ n k ≃ₗ[ℝ] CForm Γ n k × CForm Γ n k :=
  LinearEquiv.ofLinearMap (toPairs Γ n k) (ofPairs Γ n k)
    (LinearMap.ext fun p => Prod.ext (toPairs_comp_ofPairs_fst_aux p) (toPairs_comp_ofPairs_snd_aux p))
    (LinearMap.ext fun w => ofPairs_comp_toPairs_aux w)

/-! ### The exterior derivative -/

/-- The exterior derivative of complex-coefficient forms (componentwise on real and imaginary
parts, with the explicit pointwise formula `d_apply`). -/
def CFormCx.d (Γ : Subgroup RealGL) (n k : ℕ) : CFormCx Γ n k →ₗ[ℝ] CFormCx Γ n (k + 1) :=
  (ofPairs Γ n (k + 1)).comp ((LinearMap.prodMap (CForm.d Γ n k) (CForm.d Γ n k)).comp
    (toPairs Γ n k))

theorem CFormCx.d_apply (w : CFormCx Γ n k) {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    CFormCx.fn (CFormCx.d Γ n k w) x = extDeriv (CFormCx.fn w) x := by
  have hdiff : DifferentiableAt ℝ (CFormCx.fn w) x :=
    ((CFormCx.smooth w x hx).contDiffAt (isOpen_positiveCoordinates.mem_nhds hx)).differentiableAt
      (by simp)
  change CFormCx.fn (ofPairs Γ n (k + 1) (CForm.d Γ n k (toPairs Γ n k w).1,
    CForm.d Γ n k (toPairs Γ n k w).2)) x = _
  rw [ofPairs_fn]
  simp only
  have e1 := CForm.d_apply (toPairs Γ n k w).1 hx
  have e2 := CForm.d_apply (toPairs Γ n k w).2 hx
  have e3 : CForm.fn (toPairs Γ n k w).1 = coefficientRaw (reL n) (CFormCx.fn w) :=
    toPairs_fst_fn w
  have e4 : CForm.fn (toPairs Γ n k w).2 = coefficientRaw (imL n) (CFormCx.fn w) :=
    toPairs_snd_fn w
  have e5 := extDeriv_coefficientRaw (reL n) hdiff
  have e6 := extDeriv_coefficientRaw (imL n) hdiff
  have e7 : coefficientFormMap (embRe n) (k + 1) (coefficientFormMap (reL n) (k + 1) (extDeriv (CFormCx.fn w) x)) +
      coefficientFormMap (embIm n) (k + 1) (coefficientFormMap (imL n) (k + 1) (extDeriv (CFormCx.fn w) x)) =
        extDeriv (CFormCx.fn w) x := by
    rw [cFM_comp, cFM_comp, ← cFM_add, embRe_reL_add, cFM_id]
  refine (congrArg₂ (fun u v => coefficientFormMap (embRe n) (k + 1) u + coefficientFormMap (embIm n) (k + 1) v)
    e1 e2).trans ?_
  rw [e3, e4, e5, e6]
  exact e7

theorem toPairs_d (w : CFormCx Γ n k) :
    toPairs Γ n (k + 1) (CFormCx.d Γ n k w) =
      (CForm.d Γ n k (toPairs Γ n k w).1, CForm.d Γ n k (toPairs Γ n k w).2) :=
  (cxEquiv Γ n (k + 1)).apply_symm_apply _

/-! ### The Hermitian metric and the `L²` norm -/

/-- Values of a complex-coefficient form on the ordered tuples of the coordinate basis. -/
def formCoordC {n k : ℕ} (a : FormC n k) (I : Fin k → Fin 5) : ComplexCoefficients n :=
  a (fun r => Pi.single (I r) 1)

/-- The real part of the Hermitian extension of a real coefficient bilinear form to `Sym^n ℂ³`:
`B(a + ib, a' + ib') = B(a, a') + B(b, b')` (real part). -/
def cplxBilin (n : ℕ) (B : Coefficients n →ₗ[ℝ] Coefficients n →ₗ[ℝ] ℝ) :
    ComplexCoefficients n →ₗ[ℝ] ComplexCoefficients n →ₗ[ℝ] ℝ :=
  B.compl₁₂ (reL n).toLinearMap (reL n).toLinearMap +
    B.compl₁₂ (imL n).toLinearMap (imL n).toLinearMap

/-- The metric of the complexified bundle `Λ^k T* ⊗ E_ℂ` at `x`: the inverse trace Gram matrix tensored
with the Hermitian extension of the Fischer coefficient metric at `x`. -/
def formPairingC (n k : ℕ) (x : Coordinates) (a b : FormC n k) : ℝ :=
  (k.factorial : ℝ)⁻¹ * matrixContraction (cplxBilin n (coordinateCoefficientBilin n x))
    (tensorMatrix k (inverseGram x)) (formCoordC a) (formCoordC b)

theorem formPairingC_eq (x : Coordinates) (a b : FormC n k) :
    formPairingC n k x a b =
      formPairing n k x (coefficientFormMap (reL n) k a) (coefficientFormMap (reL n) k b) +
        formPairing n k x (coefficientFormMap (imL n) k a) (coefficientFormMap (imL n) k b) := by
  unfold formPairingC formPairing matrixContraction
  simp only [cplxBilin, LinearMap.add_apply, LinearMap.compl₁₂_apply, mul_add, Finset.sum_add_distrib]
  ring_nf
  rfl

/-- The descended pointwise Hermitian metric of two complex-coefficient forms. -/
def scalarPairingCx (a b : CFormCx Γ n k) : OrbitSpace Γ → ℝ :=
  scalarPairing (toPairs Γ n k a).1 (toPairs Γ n k b).1 +
    scalarPairing (toPairs Γ n k a).2 (toPairs Γ n k b).2

/-- The descended function is, at the class of a point, the intrinsic Hermitian metric of the values
of the two forms in the fibre of the complexified bundle. -/
theorem scalarPairingCx_proj (h : Admissible Γ) (a b : CFormCx Γ n k) (S : Space) :
    scalarPairingCx a b (proj Γ S) =
      formPairingC n k (coordinateChart S) (CFormCx.fn a (coordinateChart S))
        (CFormCx.fn b (coordinateChart S)) := by
  unfold scalarPairingCx
  exact (congrArg₂ (· + ·) (scalarPairing_proj h _ _ S) (scalarPairing_proj h _ _ S)).trans
    (formPairingC_eq _ _ _).symm

/-- The Hermitian `L²` pairing of complex-coefficient forms: the integral of the descended pointwise
metric against the Riemannian volume of the orbit space. -/
def l2Cx (a b : CFormCx Γ n k) : ℝ := ∫ q, scalarPairingCx a b q ∂quotientVolume Γ

/-- The squared `L²` norm of a complex-coefficient form. -/
def normSqCx (a : CFormCx Γ n k) : ℝ := l2Cx a a

theorem l2Cx_eq_pairs (a b : CFormCx Γ n k) :
    l2Cx a b = l2FormC Γ n k (toPairs Γ n k a) (toPairs Γ n k b) := by
  unfold l2Cx scalarPairingCx
  exact MeasureTheory.integral_add (integrable_scalarPairing _ _) (integrable_scalarPairing _ _)

/-! ### Coercivity for forms with values in `Sym^n ℂ³` -/

/-- `e` is a formal adjoint of the exterior derivative of complex-coefficient forms at `b`, for the
Hermitian `L²` pairing. -/
def IsCxFormalAdjoint (Γ : Subgroup RealGL) (n k : ℕ) (b : CFormCx Γ n (k + 1))
    (e : CFormCx Γ n k) : Prop :=
  ∀ a : CFormCx Γ n k, l2Cx (CFormCx.d Γ n k a) b = l2Cx a e

/-- The formal adjoint of the complexified exterior derivative, transported from the explicit local
adjoint of the real and imaginary parts. -/
def CFormCx.delta (Γ : Subgroup RealGL) (n k : ℕ) : CFormCx Γ n (k + 1) →ₗ[ℝ] CFormCx Γ n k :=
  (ofPairs Γ n k).comp ((LinearMap.prodMap (CForm.delta Γ n k) (CForm.delta Γ n k)).comp
    (toPairs Γ n (k + 1)))

theorem toPairs_ofPairs (p : CForm Γ n k × CForm Γ n k) : toPairs Γ n k (ofPairs Γ n k p) = p :=
  (cxEquiv Γ n k).apply_symm_apply p

theorem ofPairs_toPairs (w : CFormCx Γ n k) : ofPairs Γ n k (toPairs Γ n k w) = w :=
  (cxEquiv Γ n k).symm_apply_apply w

theorem toPairs_delta (w : CFormCx Γ n (k + 1)) :
    toPairs Γ n k (CFormCx.delta Γ n k w) = deltaC Γ n k (toPairs Γ n (k + 1) w) :=
  toPairs_ofPairs _

theorem toPairs_d' (w : CFormCx Γ n k) :
    toPairs Γ n (k + 1) (CFormCx.d Γ n k w) = dC Γ n k (toPairs Γ n k w) :=
  toPairs_d w

theorem l2Cx_d_eq (a : CFormCx Γ n k) (b : CFormCx Γ n (k + 1)) :
    l2Cx (CFormCx.d Γ n k a) b = l2FormC Γ n (k + 1) (dC Γ n k (toPairs Γ n k a))
      (toPairs Γ n (k + 1) b) := by
  have e := l2Cx_eq_pairs (CFormCx.d Γ n k a) b
  exact e.trans (congrArg (fun p => l2FormC Γ n (k + 1) p (toPairs Γ n (k + 1) b)) (toPairs_d' a))

theorem isCxFormalAdjoint_iff (b : CFormCx Γ n (k + 1)) (e : CFormCx Γ n k) :
    IsCxFormalAdjoint Γ n k b e ↔
      IsFormalAdjointC Γ n k (toPairs Γ n (k + 1) b) (toPairs Γ n k e) := by
  constructor
  · intro hd α
    have h1 := hd (ofPairs Γ n k α)
    have e1 := l2Cx_d_eq (ofPairs Γ n k α) b
    have e2 := l2Cx_eq_pairs (ofPairs Γ n k α) e
    have e1' : l2Cx (CFormCx.d Γ n k (ofPairs Γ n k α)) b =
        l2FormC Γ n (k + 1) (dC Γ n k α) (toPairs Γ n (k + 1) b) :=
      e1.trans (congrArg (fun p => l2FormC Γ n (k + 1) (dC Γ n k p) (toPairs Γ n (k + 1) b))
        (toPairs_ofPairs α))
    have e2' : l2Cx (ofPairs Γ n k α) e = l2FormC Γ n k α (toPairs Γ n k e) :=
      e2.trans (congrArg (fun p => l2FormC Γ n k p (toPairs Γ n k e)) (toPairs_ofPairs α))
    exact e1'.symm.trans (h1.trans e2')
  · intro hf a
    have e2 := l2Cx_eq_pairs a e
    exact (l2Cx_d_eq a b).trans ((hf (toPairs Γ n k a)).trans e2.symm)

theorem cx_adjoint_exists (h : Admissible Γ) (b : CFormCx Γ n (k + 1)) :
    IsCxFormalAdjoint Γ n k b (CFormCx.delta Γ n k b) := by
  rw [isCxFormalAdjoint_iff, toPairs_delta]
  exact h.deltaC_isFormalAdjoint _

theorem cx_adjoint_unique (h : Admissible Γ) (b : CFormCx Γ n (k + 1)) (e : CFormCx Γ n k)
    (he : IsCxFormalAdjoint Γ n k b e) : e = CFormCx.delta Γ n k b := by
  have h1 := h.deltaC_unique _ _ ((isCxFormalAdjoint_iff b e).mp he)
  exact (cxEquiv Γ n k).injective (h1.trans (toPairs_delta b).symm)

theorem normSqCx_eq_pairs (a : CFormCx Γ n k) : normSqCx a = normSqC (toPairs Γ n k a) :=
  l2Cx_eq_pairs a a

/-- **Proposition C.1 for forms with values in `Sym^n ℂ³`.**  For every `n > 0` there is one
constant `c > 0` such that for every admissible group `Γ`, every compactly supported smooth
`Γ`-equivariant `Sym^n ℂ³`-valued form `a` satisfies `c ‖a‖² ≤ ‖D a‖²` in degree zero and
`c ‖a‖² ≤ ‖e‖² + ‖D a‖²` in positive degree for every formal adjoint `e` of `D` at `a`; the norms
are the Hermitian `L²` norms of the complexified flat bundle. -/
theorem general_coercivity_complex_forms (n : ℕ) (hn : 0 < n) :
    ∃ c : ℝ, 0 < c ∧ ∀ Γ : Subgroup RealGL, Admissible Γ →
      (∀ a : CFormCx Γ n 0, c * normSqCx a ≤ normSqCx (CFormCx.d Γ n 0 a)) ∧
        ∀ (k : ℕ) (a : CFormCx Γ n (k + 1)) (e : CFormCx Γ n k), IsCxFormalAdjoint Γ n k a e →
          c * normSqCx a ≤ normSqCx e + normSqCx (CFormCx.d Γ n (k + 1) a) := by
  obtain ⟨c, hc, H⟩ := general_coercivity_complex n hn
  refine ⟨c, hc, fun Γ h => ⟨fun a => ?_, fun k a e hae => ?_⟩⟩
  · have h1 := (H Γ h).1 (toPairs Γ n 0 a)
    have e1 := normSqCx_eq_pairs a
    have e2 := (normSqCx_eq_pairs (CFormCx.d Γ n 0 a)).trans
      (congrArg normSqC (toPairs_d' a))
    exact (congrArg (c * ·) e1).trans_le (h1.trans_eq e2.symm)
  · have he : toPairs Γ n k e = deltaC Γ n k (toPairs Γ n (k + 1) a) :=
      h.deltaC_unique _ _ ((isCxFormalAdjoint_iff a e).mp hae)
    have h1 := (H Γ h).2 k (toPairs Γ n (k + 1) a)
    have e1 := normSqCx_eq_pairs a
    have e2 := (normSqCx_eq_pairs e).trans (congrArg normSqC he)
    have e3 := (normSqCx_eq_pairs (CFormCx.d Γ n (k + 1) a)).trans
      (congrArg normSqC (toPairs_d' a))
    exact (congrArg (c * ·) e1).trans_le (h1.trans_eq (congrArg₂ (· + ·) e2 e3).symm)

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
