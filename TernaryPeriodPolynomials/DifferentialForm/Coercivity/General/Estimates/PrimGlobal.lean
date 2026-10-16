module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Estimates.PrimAssemble
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Estimates.PrimitiveF
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Estimates.WeakPrimitive

@[expose] public section


/-! # General coercivity, Tier B (phase F): a weak primitive is a smooth equivariant primitive

If `T` is a `Γ`-invariant functional on compactly supported test one-forms whose weak coderivative
is a closed compactly supported smooth `Γ`-equivariant two-form `ζ`, then there is a smooth
`Γ`-equivariant one-form `η` with `dη = ζ`. The functional `T` itself need not be represented by a
smooth form: the proof constructs a corrected `Γ`-invariant functional `E = T - S ∘ δ` with the same
weak coderivative as `T` (`exists_smooth_rep`), and it is `E` that is represented by `η`.

Formalized by Claude Sonnet 5.5. -/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open TernaryPoly TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceCharts
  TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
  TernaryPoly.PolynomialFormWeakSmooth TernaryPoly.PolynomialFormCoordinates
  TernaryPoly.SymmetricSpaceRiemannian TernaryPoly.CompactCoordinateIntegration
  TernaryPoly.SmoothCoveringDeRham TernaryPoly.PolynomialFormGeometricEnergy
  TernaryPoly.PolynomialFormConnection TernaryPoly.SmoothLocalDeRham
open Set MeasureTheory Filter Topology
open scoped ContDiff

variable {n : ℕ} {Γ : Subgroup RealGL}

/-- Local primitive data exist on every coordinate box. -/
theorem nonempty_localPrim (T : Cc n 1 →ₗ[ℝ] ℝ) (ζ : CForm Γ n 2) (hζ : CForm.d Γ n 2 ζ = 0)
    (hweak : ∀ g : Cc n 2, T (deltaCc n 1 g) =
      ∫ x, coordinateDensity x * formPairing n 2 x (CForm.fn ζ x) (g.1 x))
    (b : WeakCubeFive ≃L[ℝ] Coordinates) (c : Coordinates)
    (hΩ : (coordinateTestBox b c : Set Coordinates) ⊆ positiveCoordinates) :
    Nonempty (LocalPrim (coordinateTestBox b c) T) := by
  have hclosed : ∀ x ∈ (coordinateTestBox b c : Set Coordinates), extDeriv (CForm.fn ζ) x = 0 := by
    intro x hx
    have hxp := hΩ hx
    have := congrArg (fun z : CForm Γ n 3 => CForm.fn z x) hζ
    simp only [CForm.d_apply _ hxp] at this
    exact this
  obtain ⟨v, hv, S, -, hprim⟩ := local_primitive b c hΩ T (CForm.fn ζ)
    ((CForm.smooth ζ).mono hΩ) hclosed (fun g => hweak g.1)
  exact ⟨⟨v, hv, S, hprim⟩⟩

/-- **Smooth representation.**  There is a `Γ`-invariant functional `E` on test one-forms with the
same weak coderivative as `T` which is represented by a smooth one-form. -/
theorem exists_smooth_rep (h : Admissible Γ) (T : Cc n 1 →ₗ[ℝ] ℝ)
    (hinv : ∀ (δ : Γ) (g : Cc n 1), T (pullCc (δ : RealGL) g) = T g)
    (ζ : CForm Γ n 2) (hζ : CForm.d Γ n 2 ζ = 0)
    (hweak : ∀ g : Cc n 2, T (deltaCc n 1 g) =
      ∫ x, coordinateDensity x * formPairing n 2 x (CForm.fn ζ x) (g.1 x)) :
    ∃ (E : Cc n 1 →ₗ[ℝ] ℝ), (∀ (δ : Γ) (g : Cc n 1), E (pullCc (δ : RealGL) g) = E g) ∧
      (∀ w : Cc n 2, E (deltaCc n 1 w) = T (deltaCc n 1 w)) ∧
      ∃ (η : Coordinates → FormValue n 1) (_ : ContDiffOn ℝ ∞ η positiveCoordinates),
        (∀ x ∉ positiveCoordinates, η x = 0) ∧
        ∀ g : Cc n 1, E g = ∫ x, coordinateDensity x * formPairing n 1 x (η x) (g.1 x) := by
  classical
  let D : BoxData Γ := h.nonempty_boxData.some
  let G : ∀ i : D.ι, LocalPrim (D.box i) T := fun i =>
    (nonempty_localPrim T ζ hζ hweak (D.e i) (D.a i) (D.box_pos i)).some
  let E : Cc n 1 →ₗ[ℝ] ℝ := corrected D (fun i => (G i).S) T
  refine ⟨E, fun δ g => corrected_pullCc D _ h T hinv δ g, fun w => corrected_deltaCc D _ T w, ?_⟩
  let Vo : TopologicalSpace.Opens Coordinates := ⟨positiveCoordinates, isOpen_positiveCoordinates⟩
  let A : CcIn n 1 (Vo : Set Coordinates) →ₗ[ℝ] ℝ := E.comp (CcIn n 1 (Vo : Set Coordinates)).subtype
  have key : ∀ x ∈ (Vo : Set Coordinates), ∃ (U : TopologicalSpace.Opens Coordinates)
      (hU : (U : Set Coordinates) ⊆ Vo) (_ : x ∈ (U : Set Coordinates))
      (f : Coordinates → FormValue n 1) (hf : ContDiffOn ℝ ∞ f U),
      ∀ g : CcIn n 1 (U : Set Coordinates), A (inclIn hU g) = pairIn U f hf.continuousOn g := by
    intro x hx
    obtain ⟨b, c, hxb, hcl⟩ := exists_coordinateTestBox_closure_subset
      (isOpen_positiveCoordinates.mem_nhds hx)
    have hBpos : (coordinateTestBox b c : Set Coordinates) ⊆ positiveCoordinates :=
      subset_closure.trans hcl
    let GB := (nonempty_localPrim T ζ hζ hweak b c hBpos).some
    obtain ⟨η, hη, hrep⟩ := corrected_local h D T hinv G (coordinateTestBox b c) hcl
      (coordinateTestBox_isCompact_closure b c) GB
    exact ⟨coordinateTestBox b c, hBpos, hxb, η, hη, fun g => hrep g⟩
  obtain ⟨η, hη, hrepV⟩ := exists_smooth_of_local Vo (subset_refl _) A key
  refine ⟨fun x => if x ∈ positiveCoordinates then η x else 0, ?_, ?_, ?_⟩
  · exact hη.congr (fun x hx => ite_eq_left hx)
  · intro x hx
    exact ite_eq_right hx
  · intro g
    have hg : g ∈ CcIn n 1 (Vo : Set Coordinates) := g.2.2.2
    have h1 := hrepV ⟨g, hg⟩
    refine h1.trans ?_
    rw [pairIn_apply]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro x
    by_cases hx : x ∈ positiveCoordinates
    · change coordinateDensity x * formPairing n 1 x (η x) (g.1 x) =
        coordinateDensity x * formPairing n 1 x (if x ∈ positiveCoordinates then η x else 0) (g.1 x)
      rw [ite_eq_left hx]
    · have h0 : g.1 x = 0 := Cc.zero_outside g.2 x hx
      change coordinateDensity x * formPairing n 1 x (η x) (g.1 x) =
        coordinateDensity x * formPairing n 1 x (if x ∈ positiveCoordinates then η x else 0) (g.1 x)
      rw [h0]
      simp

/-- **Phase F.**  If a `Γ`-invariant functional on test one-forms has as weak coderivative a closed
compactly supported smooth `Γ`-equivariant two-form `ζ`, then `ζ` has a smooth `Γ`-equivariant
primitive `η` (`dη = ζ`); in particular `ζ` is exact. (`η` represents the corrected functional of
`exists_smooth_rep`, not necessarily `T` itself.) -/
theorem exists_smooth_primitive (h : Admissible Γ) (T : Cc n 1 →ₗ[ℝ] ℝ)
    (hinv : ∀ (δ : Γ) (g : Cc n 1), T (pullCc (δ : RealGL) g) = T g)
    (ζ : CForm Γ n 2) (hζ : CForm.d Γ n 2 ζ = 0)
    (hweak : ∀ g : Cc n 2, T (deltaCc n 1 g) =
      ∫ x, coordinateDensity x * formPairing n 2 x (CForm.fn ζ x) (g.1 x)) :
    ∃ η : Coordinates → FormValue n 1, ContDiffOn ℝ ∞ η positiveCoordinates ∧
      (∀ x ∉ positiveCoordinates, η x = 0) ∧ IsEquivariant Γ n 1 η ∧
      ∀ x ∈ positiveCoordinates, extDeriv η x = CForm.fn ζ x := by
  classical
  obtain ⟨E, hE, hEδ, η, hη, hout, hrep⟩ := exists_smooth_rep h T hinv ζ hζ hweak
  let Vo : TopologicalSpace.Opens Coordinates := ⟨positiveCoordinates, isOpen_positiveCoordinates⟩
  have hVo : (Vo : Set Coordinates) ⊆ positiveCoordinates := subset_refl _
  have hrepV : ∀ g : CcIn n 1 (Vo : Set Coordinates), E g.1 = pairIn Vo η hη.continuousOn g :=
    fun g => hrep g.1
  refine ⟨η, hη, hout, ?_, ?_⟩
  · -- equivariance
    rw [isEquivariant_iff_actPull]
    intro δ hδ x hx
    let δΓ : Γ := ⟨δ, hδ⟩
    have hdet : δ.val.det ^ 2 = 1 := h.det_sq δΓ
    have hact : ContDiffOn ℝ ∞ (actPull n 1 δ η) positiveCoordinates := contDiffOn_actPull n 1 δ hη
    refine eqOn_of_pairIn_eq Vo hVo (actPull n 1 δ η) η hact.continuousOn hη.continuousOn
      (fun g => ?_) hx
    have hg_eq : g.1.1 = actPull n 1 δ (actPull n 1 δ⁻¹ g.1.1) := by
      funext y
      by_cases hy : y ∈ positiveCoordinates
      · exact (actPull_inverse n 1 δ g.1.1 hy).symm
      · rw [Cc.zero_outside g.1.2 y hy, actPull_of_notMem n 1 δ _ hy]
    have h1 : pairIn Vo (actPull n 1 δ η) hact.continuousOn g =
        localIntegral n 1 (actPull n 1 δ η) (actPull n 1 δ (actPull n 1 δ⁻¹ g.1.1)) := by
      rw [pairIn_apply]
      conv_rhs => rw [← hg_eq]
      rfl
    have h2 := localIntegral_actPull n 1 δ hdet η (actPull n 1 δ⁻¹ g.1.1) hout
    have h3 : localIntegral n 1 η (actPull n 1 δ⁻¹ g.1.1) = E (pullCc δ⁻¹ g.1) :=
      (hrep (pullCc δ⁻¹ g.1)).symm
    have h4 : E (pullCc (δΓ⁻¹ : Γ) g.1) = E g.1 := hE δΓ⁻¹ g.1
    have h5 : E (pullCc δ⁻¹ g.1) = E g.1 := by
      have : ((δΓ⁻¹ : Γ) : RealGL) = δ⁻¹ := rfl
      rw [← this]; exact h4
    rw [h1, h2, h3, h5, hrepV g]
  · intro x hx
    have hζc : ContinuousOn (CForm.fn ζ) (Vo : Set Coordinates) := (CForm.smooth ζ).continuousOn
    have hdη : ContDiffOn ℝ ∞ (extDeriv η) (Vo : Set Coordinates) :=
      smooth_extDeriv Vo.isOpen hη
    have c1 : bridge Vo hVo (pairIn Vo η hη.continuousOn) =
        valuedRegularCurrent volume Vo η hη.continuousOn :=
      bridge_regular Vo hVo _ η hη.continuousOn (fun g => rfl)
    have c2 := formWeakExterior_regular n 1 volume Vo η hη
    have c3 := bridge_exterior Vo hVo (pairIn Vo η hη.continuousOn)
    have c4 : bridge Vo hVo ((pairIn Vo η hη.continuousOn).comp (deltaIn n 1 (Vo : Set Coordinates))) =
        valuedRegularCurrent volume Vo (CForm.fn ζ) hζc := by
      refine bridge_regular Vo hVo _ (CForm.fn ζ) hζc (fun g => ?_)
      change pairIn Vo η hη.continuousOn (deltaIn n 1 (Vo : Set Coordinates) g) = _
      rw [pairIn_apply]
      have := hrep (deltaCc n 1 g.1)
      exact this.symm.trans ((hEδ g.1).trans (hweak g.1))
    have c5 : valuedRegularCurrent volume Vo (extDeriv η) hdη.continuousOn =
        valuedRegularCurrent volume Vo (CForm.fn ζ) hζc := by
      rw [← c2, ← c1, c3, c4]
    exact (valuedRegularCurrent_eq_iff volume (coordinates n 2) Vo _ _ hdη.continuousOn hζc).mp c5 hx

/-- **Tier B, the general theorem.**  For every admissible group `Γ` and every `n > 0`, each closed
compactly supported smooth `Γ`-equivariant two-form with values in `Sym^n` is the exterior
derivative of a smooth `Γ`-equivariant one-form (not compactly supported): the map
`H²_c(X_Γ, E) → H²(X_Γ, E)` vanishes in de Rham form. -/
theorem Admissible.closed_compact_exact (h : Admissible Γ) (hn : 0 < n) (ζ : CForm Γ n 2)
    (hζ : CForm.d Γ n 2 ζ = 0) :
    ∃ η : Coordinates → FormValue n 1, ContDiffOn ℝ ∞ η positiveCoordinates ∧
      (∀ x ∉ positiveCoordinates, η x = 0) ∧ IsEquivariant Γ n 1 η ∧
      ∀ x ∈ positiveCoordinates, extDeriv η x = CForm.fn ζ x := by
  have : Fact (Admissible Γ) := ⟨h⟩
  obtain ⟨u, hu⟩ := Admissible.closed_has_weak_primitive hn ζ hζ
  exact exists_smooth_primitive h (currentFun u) (fun δ g => currentFun_invariant u δ g) ζ hζ
    (fun g => currentFun_weak u ζ hu g)

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
