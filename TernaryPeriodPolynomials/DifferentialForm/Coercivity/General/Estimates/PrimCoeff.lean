module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Estimates.PrimGlobal
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Variants.ComplexDual

@[expose] public section



/-! # General coercivity, Tier B for the dual and complex coefficient systems

The vanishing `H²_c → H²` (de Rham form) of `Admissible.closed_compact_exact` for `E = Sym^n`
transfers to the dual `E*` (through the Cartan involution, `θ(Γ)` being admissible), to the
complexification `E ⊗ ℂ` (componentwise on real and imaginary parts) and to the complexified dual.

Formalized by Claude Sonnet 5.5. -/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open TernaryPoly TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceCharts
  TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
  TernaryPoly.SymmetricSpaceCovering TernaryPoly.SmoothCoveringDeRham TernaryPoly.SmoothLocalDeRham
  TernaryPoly.PolynomialFormConnection
open Set
open scoped ContDiff

variable {n k : ℕ} {Γ : Subgroup RealGL}

/-- **Tier B for the dual coefficient system.**  Every closed compactly supported smooth dual form
of degree two is the exterior derivative of a smooth form equivariant for the dual
representation `ρ ∘ θ`. -/
theorem Admissible.closed_compact_exact_dual (h : Admissible Γ) (hn : 0 < n) (ζ : DForm Γ n 2)
    (hζ : dualD h n 2 ζ = 0) :
    ∃ η : Coordinates → FormValue n 1, ContDiffOn ℝ ∞ η positiveCoordinates ∧
      (∀ x ∉ positiveCoordinates, η x = 0) ∧ IsRepEquivariant Γ n (dualRep Γ n) 1 η ∧
      ∀ x ∈ positiveCoordinates, extDeriv η x = DForm.fn ζ x := by
  have hζ' : CForm.d (thetaImage Γ) n 2 (toStd h n 2 ζ) = 0 := by
    have := congrArg (toStd h n 3) hζ
    rw [map_zero] at this
    exact (toStd_ofStd h _).symm.trans this
  obtain ⟨η', h1, -, h3, h4⟩ := Admissible.closed_compact_exact h.theta hn (toStd h n 2 ζ) hζ'
  refine ⟨ioPull n 1 η', contDiffOn_ioPull n 1 h1, fun x hx => ioPull_of_notMem n 1 _ hx,
    isRepEquivariant_ioPull_dual h3, fun x hx => ?_⟩
  rw [extDeriv_ioPull n 1 h1 hx, ioPull_congr n 2 (fun y hy => h4 y hy) hx, toStd_fn,
    ioPull_ioPull n 2 _ hx]

/-- Real and imaginary parts, as raw functions, assemble to a complex-coefficient form. -/
def pairRaw (n k : ℕ) (a b : Coordinates → FormValue n k) : Coordinates → FormC n k :=
  coefficientRaw (embRe n) a + coefficientRaw (embIm n) b

theorem isCxEquivariant_pairRaw {a b : Coordinates → FormValue n k}
    (ha : IsEquivariant Γ n k a) (hb : IsEquivariant Γ n k b) :
    IsCxEquivariant Γ n k (pairRaw n k a b) := by
  intro γ x hx
  change pullRaw (coordinateAction (γ : RealGL)) (coefficientRaw (embRe n) a + coefficientRaw (embIm n) b) x =
    coefficientFormMap (complexRepresentation n (γ : RealGL)).toContinuousLinearMap k
      (coefficientFormMap (embRe n) k (a x) + coefficientFormMap (embIm n) k (b x))
  rw [pullRaw_add', pullRaw_coefficientRaw, pullRaw_coefficientRaw, ha γ x hx, hb γ x hx, map_add,
    cFM_comp, cFM_comp, cFM_comp, cFM_comp]
  have e1 : (embRe n).comp (coefficientRep Γ n γ).toContinuousLinearMap =
      (complexRepresentation n (γ : RealGL)).toContinuousLinearMap.comp (embRe n) :=
    (rep_comp_embRe (γ : RealGL)).symm
  have e2 : (embIm n).comp (coefficientRep Γ n γ).toContinuousLinearMap =
      (complexRepresentation n (γ : RealGL)).toContinuousLinearMap.comp (embIm n) :=
    (rep_comp_embIm (γ : RealGL)).symm
  rw [e1, e2]

theorem contDiffOn_pairRaw {a b : Coordinates → FormValue n k}
    (ha : ContDiffOn ℝ ∞ a positiveCoordinates) (hb : ContDiffOn ℝ ∞ b positiveCoordinates) :
    ContDiffOn ℝ ∞ (pairRaw n k a b) positiveCoordinates :=
  (coefficientRaw_smooth (embRe n) ha).add (coefficientRaw_smooth (embIm n) hb)

theorem pairRaw_zero_outside {a b : Coordinates → FormValue n k}
    (ha : ∀ x ∉ positiveCoordinates, a x = 0) (hb : ∀ x ∉ positiveCoordinates, b x = 0)
    {x : Coordinates} (hx : x ∉ positiveCoordinates) : pairRaw n k a b x = 0 := by
  change coefficientFormMap (embRe n) k (a x) + coefficientFormMap (embIm n) k (b x) = 0
  rw [ha x hx, hb x hx, TernaryPoly.PolynomialFormCoordinates.clm_map_zero,
    TernaryPoly.PolynomialFormCoordinates.clm_map_zero, add_zero]

theorem extDeriv_pairRaw {a b : Coordinates → FormValue n k}
    (ha : ContDiffOn ℝ ∞ a positiveCoordinates) (hb : ContDiffOn ℝ ∞ b positiveCoordinates)
    {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    extDeriv (pairRaw n k a b) x =
      coefficientFormMap (embRe n) (k + 1) (extDeriv a x) +
        coefficientFormMap (embIm n) (k + 1) (extDeriv b x) := by
  have hda : DifferentiableAt ℝ a x :=
    ((ha x hx).contDiffAt (isOpen_positiveCoordinates.mem_nhds hx)).differentiableAt (by simp)
  have hdb : DifferentiableAt ℝ b x :=
    ((hb x hx).contDiffAt (isOpen_positiveCoordinates.mem_nhds hx)).differentiableAt (by simp)
  have h1 : DifferentiableAt ℝ (coefficientRaw (embRe n) a) x :=
    (((coefficientRaw_smooth (embRe n) ha) x hx).contDiffAt
      (isOpen_positiveCoordinates.mem_nhds hx)).differentiableAt (by simp)
  have h2 : DifferentiableAt ℝ (coefficientRaw (embIm n) b) x :=
    (((coefficientRaw_smooth (embIm n) hb) x hx).contDiffAt
      (isOpen_positiveCoordinates.mem_nhds hx)).differentiableAt (by simp)
  unfold pairRaw
  rw [extDeriv_add h1 h2, extDeriv_coefficientRaw (embRe n) hda, extDeriv_coefficientRaw (embIm n) hdb]

/-- **Tier B for the complexified coefficient system.** -/
theorem Admissible.closed_compact_exact_complex (h : Admissible Γ) (hn : 0 < n)
    (ζ : CFormCx Γ n 2) (hζ : CFormCx.d Γ n 2 ζ = 0) :
    ∃ η : Coordinates → FormC n 1, ContDiffOn ℝ ∞ η positiveCoordinates ∧
      (∀ x ∉ positiveCoordinates, η x = 0) ∧ IsCxEquivariant Γ n 1 η ∧
      ∀ x ∈ positiveCoordinates, extDeriv η x = CFormCx.fn ζ x := by
  have hp : toPairs Γ n (2 + 1) (CFormCx.d Γ n 2 ζ) = toPairs Γ n (2 + 1) 0 :=
    congrArg (toPairs Γ n (2 + 1)) hζ
  have hz : toPairs Γ n (2 + 1) 0 = 0 := (toPairs Γ n (2 + 1)).map_zero
  have hp' : (CForm.d Γ n 2 (toPairs Γ n 2 ζ).1, CForm.d Γ n 2 (toPairs Γ n 2 ζ).2) =
      (0 : CForm Γ n 3 × CForm Γ n 3) :=
    (toPairs_d ζ).symm.trans (hp.trans hz)
  have hda : CForm.d Γ n 2 (toPairs Γ n 2 ζ).1 = 0 := congrArg Prod.fst hp'
  have hdb : CForm.d Γ n 2 (toPairs Γ n 2 ζ).2 = 0 := congrArg Prod.snd hp'
  obtain ⟨ηa, ha1, ha2, ha3, ha4⟩ := Admissible.closed_compact_exact h hn _ hda
  obtain ⟨ηb, hb1, hb2, hb3, hb4⟩ := Admissible.closed_compact_exact h hn _ hdb
  refine ⟨pairRaw n 1 ηa ηb, contDiffOn_pairRaw ha1 hb1, fun x hx => pairRaw_zero_outside ha2 hb2 hx,
    isCxEquivariant_pairRaw ha3 hb3, fun x hx => ?_⟩
  rw [extDeriv_pairRaw ha1 hb1 hx, ha4 x hx, hb4 x hx]
  have := congrArg (fun z : CFormCx Γ n 2 => CFormCx.fn z x) (ofPairs_toPairs ζ)
  simpa [ofPairs_fn] using this

theorem isCxDualEquivariant_pairRaw {a b : Coordinates → FormValue n k}
    (ha : IsRepEquivariant Γ n (dualRep Γ n) k a) (hb : IsRepEquivariant Γ n (dualRep Γ n) k b) :
    IsCxDualEquivariant Γ n k (pairRaw n k a b) := by
  intro γ x hx
  change pullRaw (coordinateAction (γ : RealGL)) (coefficientRaw (embRe n) a + coefficientRaw (embIm n) b) x =
    coefficientFormMap (complexRepresentation n (thetaHom (γ : RealGL))).toContinuousLinearMap k
      (coefficientFormMap (embRe n) k (a x) + coefficientFormMap (embIm n) k (b x))
  rw [pullRaw_add', pullRaw_coefficientRaw, pullRaw_coefficientRaw, ha γ x hx, hb γ x hx, map_add,
    cFM_comp, cFM_comp, cFM_comp, cFM_comp]
  have e1 : (embRe n).comp (dualRep Γ n γ).toContinuousLinearMap =
      (complexRepresentation n (thetaHom (γ : RealGL))).toContinuousLinearMap.comp (embRe n) :=
    (rep_comp_embRe (thetaHom (γ : RealGL))).symm
  have e2 : (embIm n).comp (dualRep Γ n γ).toContinuousLinearMap =
      (complexRepresentation n (thetaHom (γ : RealGL))).toContinuousLinearMap.comp (embIm n) :=
    (rep_comp_embIm (thetaHom (γ : RealGL))).symm
  rw [e1, e2]

/-- **Tier B for the complexified dual coefficient system.** -/
theorem Admissible.closed_compact_exact_complex_dual (h : Admissible Γ) (hn : 0 < n)
    (ζ : CFormCxD Γ n 2) (hζ : CFormCxD.d h n 2 ζ = 0) :
    ∃ η : Coordinates → FormC n 1, ContDiffOn ℝ ∞ η positiveCoordinates ∧
      (∀ x ∉ positiveCoordinates, η x = 0) ∧ IsCxDualEquivariant Γ n 1 η ∧
      ∀ x ∈ positiveCoordinates, extDeriv η x = CFormCxD.fn ζ x := by
  have hp : toPairsD Γ n (2 + 1) (CFormCxD.d h n 2 ζ) = toPairsD Γ n (2 + 1) 0 :=
    congrArg (toPairsD Γ n (2 + 1)) hζ
  have hz : toPairsD Γ n (2 + 1) 0 = 0 := (toPairsD Γ n (2 + 1)).map_zero
  have hp' : (dualD h n 2 (toPairsD Γ n 2 ζ).1, dualD h n 2 (toPairsD Γ n 2 ζ).2) =
      (0 : DForm Γ n 3 × DForm Γ n 3) :=
    (toPairsD_d h ζ).symm.trans (hp.trans hz)
  have hda : dualD h n 2 (toPairsD Γ n 2 ζ).1 = 0 := congrArg Prod.fst hp'
  have hdb : dualD h n 2 (toPairsD Γ n 2 ζ).2 = 0 := congrArg Prod.snd hp'
  obtain ⟨ηa, ha1, ha2, ha3, ha4⟩ := Admissible.closed_compact_exact_dual h hn _ hda
  obtain ⟨ηb, hb1, hb2, hb3, hb4⟩ := Admissible.closed_compact_exact_dual h hn _ hdb
  refine ⟨pairRaw n 1 ηa ηb, contDiffOn_pairRaw ha1 hb1, fun x hx => pairRaw_zero_outside ha2 hb2 hx,
    isCxDualEquivariant_pairRaw ha3 hb3, fun x hx => ?_⟩
  rw [extDeriv_pairRaw ha1 hb1 hx, ha4 x hx, hb4 x hx]
  have := congrArg (fun z : CFormCxD Γ n 2 => CFormCxD.fn z x) (ofPairsD_toPairsD ζ)
  simpa [ofPairsD_fn] using this

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
