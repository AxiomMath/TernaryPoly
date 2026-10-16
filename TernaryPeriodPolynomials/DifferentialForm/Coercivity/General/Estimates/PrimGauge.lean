module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Estimates.PrimCut
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Estimates.Boxes

@[expose] public section


/-! # General coercivity, Tier B (phase F): the equivariant gauge functional

Given local gauges `S_i` on the boxes of a `BoxData`, the functional
`S f = ∑_{(γ,i)} S_i(ρ_i · γ^* f)` on test zero-forms is a locally finite sum, `Γ`-invariant.

Formalized by Claude Sonnet 5.5. -/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open TernaryPoly TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceCharts
  TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
  TernaryPoly.PolynomialFormWeakSmooth TernaryPoly.PolynomialFormCoordinates
  TernaryPoly.SymmetricSpaceRiemannian TernaryPoly.CompactCoordinateIntegration
open Set MeasureTheory Filter Topology
open scoped ContDiff

variable {n k : ℕ} {Γ : Subgroup RealGL}

theorem deltaCc_deltaCc (w : Cc n (k + 2)) : deltaCc n k (deltaCc n (k + 1) w) = 0 := by
  apply Subtype.ext
  refine funext_of_pos (fun x hx => ?_) (fun x hx => Cc.zero_outside (deltaCc n k _).2 x hx)
    (fun x _ => rfl)
  change localAdjoint n k (localAdjoint n (k + 1) w.1) x = (0 : Coordinates → FormValue n k) x
  have hsm : ContDiffOn ℝ ∞ (localAdjoint n (k + 1) w.1) positiveCoordinates :=
    contDiffOn_localAdjoint n (k + 1) w.2.1.contDiffOn
  refine eqOn_of_form_test_integrals n k (contDiffOn_localAdjoint n k hsm) contDiffOn_const
    (fun f hf hc hs => ?_) hx
  have hfc : f ∈ Cc n k := ⟨hf, hc, hs⟩
  have hdf : extDeriv f ∈ Cc n (k + 1) := extDeriv_mem_Cc hfc
  have h1 := integral_extDeriv_localAdjoint_test n k f (localAdjoint n (k + 1) w.1)
    hf.contDiffOn hsm hc hs
  have h2 := integral_extDeriv_localAdjoint_test n (k + 1) (extDeriv f) w.1
    hdf.1.contDiffOn w.2.1.contDiffOn hdf.2.1 hdf.2.2
  have hdd : ∀ y, extDeriv (extDeriv f) y = 0 := fun y =>
    extDeriv_extDeriv_apply (r := ∞) hf.contDiffAt (by simp only [minSmoothness_of_isRCLikeNormedField]; norm_cast)
  have h3 : ∫ y, coordinateDensity y * formPairing n (k + 2) y (extDeriv (extDeriv f) y) (w.1 y) = 0 := by
    simp [hdd]
  rw [← h1, ← h2, h3]
  simp

/-! ### The boxes of a `BoxData` and finiteness of translates meeting a compact set -/

/-- The `i`-th box of a `BoxData`. -/
abbrev BoxData.box (D : BoxData Γ) (i : D.ι) : TopologicalSpace.Opens Coordinates :=
  coordinateTestBox (D.e i) (D.a i)

theorem BoxData.finite_meet (D : BoxData Γ) {K : Set Coordinates} (hK : IsCompact K)
    (hKp : K ⊆ positiveCoordinates) :
    {q : Γ × D.ι | ∃ z ∈ K, coordinateAction (q.1 : RealGL) z ∈ tsupport (D.ρ q.2)}.Finite := by
  choose! N hNn hNf using fun x (hx : x ∈ K) => D.locFin x (hKp hx)
  obtain ⟨t, htK, hcov⟩ := hK.elim_nhds_subcover N hNn
  refine (t.finite_toSet.biUnion fun x hx => hNf x (htK x hx)).subset ?_
  rintro q ⟨z, hzK, hzt⟩
  obtain ⟨x, hxt, hzx⟩ := mem_iUnion₂.mp (hcov hzK)
  exact mem_iUnion₂.mpr ⟨x, hxt, ⟨z, hzx, hzt⟩⟩

theorem BoxData.finite_pairs (D : BoxData Γ) {K : Set Coordinates} (hK : IsCompact K)
    (hKp : K ⊆ positiveCoordinates) :
    {p : Γ × D.ι | ∃ y ∈ tsupport (D.ρ p.2), coordinateAction (p.1 : RealGL) y ∈ K}.Finite := by
  have hfin := D.finite_meet hK hKp
  refine (hfin.image (fun q : Γ × D.ι => (q.1⁻¹, q.2))).subset ?_
  rintro ⟨γ, i⟩ ⟨y, hyt, hyK⟩
  refine ⟨(γ⁻¹, i), ⟨coordinateAction (γ : RealGL) y, hyK, ?_⟩, by simp⟩
  have hyp : y ∈ positiveCoordinates := D.box_pos i (D.tsupport_subset i hyt)
  show coordinateAction ((γ⁻¹ : Γ) : RealGL) (coordinateAction (γ : RealGL) y) ∈ _
  rw [coordinateAction_inv_action γ hyp]
  exact hyt

section Gauge

variable (D : BoxData Γ) (S : ∀ i : D.ι, CcIn n 0 (D.box i : Set Coordinates) →ₗ[ℝ] ℝ)

/-- The cut test form `ρ_i · γ^* f`, supported in the box `B_i`. -/
def cutLin (p : Γ × D.ι) : Cc n k →ₗ[ℝ] CcIn n k (D.box p.2 : Set Coordinates) :=
  LinearMap.codRestrict (CcIn n k (D.box p.2 : Set Coordinates))
    ((mulCc (D.ρ p.2) (D.smooth p.2)).comp (pullCc (p.1 : RealGL)))
    (fun f => (tsupport_smul_subset_left (D.ρ p.2) (actPull n k (p.1 : RealGL) f.1)).trans
      (D.tsupport_subset p.2))

theorem cutLin_coe (p : Γ × D.ι) (f : Cc n k) (x : Coordinates) :
    ((cutLin D p f : CcIn n k (D.box p.2 : Set Coordinates)).1.1 : Coordinates → FormValue n k) x =
      D.ρ p.2 x • actPull n k (p.1 : RealGL) f.1 x := rfl

theorem cutLin_eq_zero (p : Γ × D.ι) (f : Cc n k)
    (h : ∀ y ∈ tsupport (D.ρ p.2), coordinateAction (p.1 : RealGL) y ∉ tsupport f.1) :
    cutLin D p f = 0 := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  rw [cutLin_coe]
  show _ = (0 : FormValue n k)
  by_cases hx : x ∈ tsupport (D.ρ p.2)
  · have h0 : f.1 (coordinateAction (p.1 : RealGL) x) = 0 := image_eq_zero_of_notMem_tsupport (h x hx)
    have hxp : x ∈ positiveCoordinates := D.box_pos p.2 (D.tsupport_subset p.2 hx)
    rw [actPull_apply n k _ _ hxp, h0, realFormPullback_zero]
    exact fv_smul_zero _
  · rw [image_eq_zero_of_notMem_tsupport hx]
    exact ContinuousAlternatingMap.ext fun w => by simp

/-- One term of the gauge functional. -/
def gaugeTerm (p : Γ × D.ι) : Cc n 0 →ₗ[ℝ] ℝ := (S p.2).comp (cutLin D p)

theorem support_gaugeTerm_finite (f : Cc n 0) :
    (Function.support fun p : Γ × D.ι => gaugeTerm D S p f).Finite := by
  refine (D.finite_pairs f.2.2.1 f.2.2.2).subset ?_
  intro p hp
  rw [Function.mem_support] at hp
  by_contra hn
  apply hp
  have : cutLin D p f = 0 := cutLin_eq_zero D p f (fun y hy hyf => hn ⟨y, hy, hyf⟩)
  change S p.2 (cutLin D p f) = 0
  rw [this, map_zero]

/-- The gauge functional `f ↦ ∑_{(γ,i)} S_i(ρ_i · γ^* f)` on test zero-forms. -/
def gaugeLin : Cc n 0 →ₗ[ℝ] ℝ where
  toFun f := ∑ᶠ p : Γ × D.ι, gaugeTerm D S p f
  map_add' f f' := by
    simp only [map_add]
    exact finsum_add_distrib (support_gaugeTerm_finite D S f) (support_gaugeTerm_finite D S f')
  map_smul' c f := by
    simp only [map_smul, smul_eq_mul, RingHom.id_apply]
    exact (mul_finsum _ c).symm

theorem gaugeLin_apply (f : Cc n 0) : gaugeLin D S f = ∑ᶠ p : Γ × D.ι, gaugeTerm D S p f := rfl

theorem gaugeLin_eq_sum (f : Cc n 0) (P : Finset (Γ × D.ι))
    (hP : ∀ p, p ∉ P → gaugeTerm D S p f = 0) : gaugeLin D S f = ∑ p ∈ P, gaugeTerm D S p f := by
  rw [gaugeLin_apply]
  apply finsum_eq_sum_of_support_subset
  intro p hp
  by_contra hn
  exact (Function.mem_support.mp hp) (hP p hn)

theorem cutLin_pullCc (p : Γ × D.ι) (δ : Γ) (f : Cc n 0) :
    cutLin D p (pullCc (δ : RealGL) f) = cutLin D (δ * p.1, p.2) f := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  change D.ρ p.2 x • (pullCc (p.1 : RealGL) (pullCc (δ : RealGL) f)).1 x =
    D.ρ p.2 x • (pullCc ((δ * p.1 : Γ) : RealGL) f).1 x
  rw [pullCc_mul]
  rfl

theorem gaugeLin_pullCc (δ : Γ) (f : Cc n 0) :
    gaugeLin D S (pullCc (δ : RealGL) f) = gaugeLin D S f := by
  rw [gaugeLin_apply, gaugeLin_apply]
  have e1 : ∀ p : Γ × D.ι, gaugeTerm D S p (pullCc (δ : RealGL) f) =
      gaugeTerm D S (Equiv.prodCongr (Equiv.mulLeft δ) (Equiv.refl D.ι) p) f := fun p => by
    change S p.2 (cutLin D p (pullCc (δ : RealGL) f)) = S p.2 (cutLin D (δ * p.1, p.2) f)
    rw [cutLin_pullCc]
  simp only [e1]
  exact finsum_comp_equiv (Equiv.prodCongr (Equiv.mulLeft δ) (Equiv.refl D.ι))
    (f := fun q : Γ × D.ι => gaugeTerm D S q f)

/-- The gauge-corrected functional `E = T - S ∘ δ` on test one-forms. -/
def corrected (T : Cc n 1 →ₗ[ℝ] ℝ) : Cc n 1 →ₗ[ℝ] ℝ := T - (gaugeLin D S).comp (deltaCc n 0)

theorem corrected_apply (T : Cc n 1 →ₗ[ℝ] ℝ) (g : Cc n 1) :
    corrected D S T g = T g - gaugeLin D S (deltaCc n 0 g) := rfl

theorem corrected_pullCc (h : Admissible Γ) (T : Cc n 1 →ₗ[ℝ] ℝ)
    (hinv : ∀ (δ : Γ) (g : Cc n 1), T (pullCc (δ : RealGL) g) = T g) (δ : Γ) (g : Cc n 1) :
    corrected D S T (pullCc (δ : RealGL) g) = corrected D S T g := by
  rw [corrected_apply, corrected_apply, hinv, deltaCc_pullCc _ (h.det_sq δ), gaugeLin_pullCc]

theorem corrected_deltaCc (T : Cc n 1 →ₗ[ℝ] ℝ) (w : Cc n 2) :
    corrected D S T (deltaCc n 1 w) = T (deltaCc n 1 w) := by
  rw [corrected_apply, deltaCc_deltaCc, map_zero, sub_zero]

end Gauge

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
