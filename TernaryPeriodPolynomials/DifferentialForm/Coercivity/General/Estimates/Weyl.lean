module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Estimates.BoxBridge
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.BoxNeighborhood
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.RegularSeparation

@[expose] public section


/-! # General coercivity, Tier B (phase F): local regularity of functionals on test forms

A functional `A` on the test ZERO-forms supported in an open set `V ⊆ positiveCoordinates` whose
coderivative `A ∘ δ` is represented by a smooth one-form is itself represented by a smooth zero-form
(`weyl_open`): locally this is the Weyl lemma on coordinate boxes (`weyl_box`), transported by
`bridge`/`unbridge`. The regularity statement is for zero-form functionals only. The degree-general
lemma `exists_smooth_of_local` is pure gluing: local smooth representatives agree
(`eqOn_of_pairIn_eq`) and the representation passes from compact supports in boxes to all test forms
by a smooth partition of unity (`pairIn_local_to_global`).

Formalized by Claude Sonnet 5.5. -/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open TernaryPoly TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceCharts
  TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
  TernaryPoly.PolynomialFormWeakSmooth TernaryPoly.PolynomialFormCoordinates
  TernaryPoly.SymmetricSpaceRiemannian TernaryPoly.CompactCoordinateIntegration
open Set MeasureTheory Filter Topology
open scoped ContDiff Distributions Manifold

variable {n k : ℕ}

theorem fv_sum_smul {ι : Type*} (s : Finset ι) (a : ι → ℝ) (A : FormValue n k) :
    (∑ i ∈ s, a i) • A = ∑ i ∈ s, a i • A :=
  ContinuousAlternatingMap.ext fun w => by simp [Finset.sum_smul]

/-! ### The pairing functional of a continuous form -/

theorem integrable_pairing (Ω : TopologicalSpace.Opens Coordinates)
    (f : Coordinates → FormValue n k) (hf : ContinuousOn f Ω)
    (g : CcIn n k (Ω : Set Coordinates)) :
    Integrable (fun x => coordinateDensity x * formPairing n k x (f x) (g.1.1 x)) := by
  have hcoord : ∀ j : Index n k, ContinuousOn (fun x => coordinates n k (f x) j) Ω := fun j =>
    (((ContinuousLinearMap.proj j).comp (coordinates n k).toContinuousLinearMap).continuous.comp_continuousOn hf)
  have hint : ∀ j : Index n k, Integrable (fun x => coordinates n k (f x) j * wcoeffLin Ω j g x) := by
    intro j
    have := valuedRegular_test_integrable volume Ω (fun x => coordinates n k (f x) j) (hcoord j)
      (wcoeffLin Ω j g)
    exact this.congr (Filter.Eventually.of_forall fun x => (smul_eq_mul _ _).trans (mul_comm _ _))
  have hpt : (fun x => coordinateDensity x * formPairing n k x (f x) (g.1.1 x)) =
      fun x => ∑ j : Index n k, coordinates n k (f x) j * wcoeffLin Ω j g x := by
    funext x
    rw [← weightedGram_pairing n k x (f x) (g.1.1 x), dotProduct]
    rfl
  rw [hpt]
  exact integrable_finsetSum _ fun j _ => hint j

/-- The functional `g ↦ ∫ ρ ⟨f, g⟩` on test forms supported in `Ω`. -/
def pairIn (Ω : TopologicalSpace.Opens Coordinates) (f : Coordinates → FormValue n k)
    (hf : ContinuousOn f Ω) : CcIn n k (Ω : Set Coordinates) →ₗ[ℝ] ℝ where
  toFun g := ∫ x, coordinateDensity x * formPairing n k x (f x) (g.1.1 x)
  map_add' g h := by
    have e : (fun x => coordinateDensity x * formPairing n k x (f x) ((g + h).1.1 x)) =
        fun x => coordinateDensity x * formPairing n k x (f x) (g.1.1 x) +
          coordinateDensity x * formPairing n k x (f x) (h.1.1 x) := by
      funext x
      change coordinateDensity x * formPairing n k x (f x) (g.1.1 x + h.1.1 x) = _
      rw [formPairing_add_right, mul_add]
    rw [e]
    exact integral_add (integrable_pairing Ω f hf g) (integrable_pairing Ω f hf h)
  map_smul' c g := by
    have e : (fun x => coordinateDensity x * formPairing n k x (f x) ((c • g).1.1 x)) =
        fun x => c * (coordinateDensity x * formPairing n k x (f x) (g.1.1 x)) := by
      funext x
      change coordinateDensity x * formPairing n k x (f x) (c • g.1.1 x) = _
      rw [formPairing_smul_right]
      ring
    rw [e]
    exact integral_const_mul c _

theorem pairIn_apply (Ω : TopologicalSpace.Opens Coordinates) (f : Coordinates → FormValue n k)
    (hf : ContinuousOn f Ω) (g : CcIn n k (Ω : Set Coordinates)) :
    pairIn Ω f hf g = ∫ x, coordinateDensity x * formPairing n k x (f x) (g.1.1 x) := rfl

theorem unbridge_regular_eq (Ω : TopologicalSpace.Opens Coordinates) (f : Coordinates → FormValue n k)
    (hf : ContinuousOn f Ω) : unbridge Ω (valuedRegularCurrent volume Ω f hf) = pairIn Ω f hf :=
  LinearMap.ext fun g => unbridge_regular Ω f hf g

theorem eqOn_of_pairIn_eq (Ω : TopologicalSpace.Opens Coordinates)
    (hΩ : (Ω : Set Coordinates) ⊆ positiveCoordinates) (f f' : Coordinates → FormValue n k)
    (hf : ContinuousOn f Ω) (hf' : ContinuousOn f' Ω)
    (h : ∀ g : CcIn n k (Ω : Set Coordinates), pairIn Ω f hf g = pairIn Ω f' hf' g) :
    EqOn f f' Ω := by
  have h1 := bridge_regular Ω hΩ (pairIn Ω f hf) f hf (fun g => rfl)
  have h2 := bridge_regular Ω hΩ (pairIn Ω f' hf') f' hf' (fun g => rfl)
  have hT : pairIn Ω f hf = pairIn Ω f' hf' := LinearMap.ext h
  rw [hT] at h1
  exact (valuedRegularCurrent_eq_iff volume (coordinates n k) Ω f f' hf hf').mp (h1.symm.trans h2)

/-! ### Multiplication by smooth functions -/

/-- Multiplication of test forms supported in `V` by a smooth function. -/
def mulIn (V : Set Coordinates) (ψ : Coordinates → ℝ) (hψ : ContDiff ℝ ∞ ψ) :
    CcIn n k V →ₗ[ℝ] CcIn n k V where
  toFun g := ⟨⟨fun x => ψ x • g.1.1 x, by
      let : IsBoundedSMul ℝ (FormValue n k) :=
        @NormedSpace.toIsBoundedSMul ℝ (FormValue n k) _ _ inferInstance
      exact hψ.smul g.1.2.1,
    g.1.2.2.1.mono' ((Function.support_smul_subset_right ψ g.1.1).trans (subset_tsupport _)),
    (tsupport_smul_subset_right ψ g.1.1).trans g.1.2.2.2⟩,
    (tsupport_smul_subset_right ψ g.1.1).trans g.2⟩
  map_add' g h := Subtype.ext (Subtype.ext (funext fun x => by
    change ψ x • (g.1.1 x + h.1.1 x) = ψ x • g.1.1 x + ψ x • h.1.1 x
    exact fv_smul_add _ _ _))
  map_smul' c g := Subtype.ext (Subtype.ext (funext fun x => by
    change ψ x • (c • g.1.1 x) = c • (ψ x • g.1.1 x)
    rw [fv_smul_smul, fv_smul_smul, mul_comm]))

theorem mulIn_coe (V : Set Coordinates) (ψ : Coordinates → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (g : CcIn n k V) (x : Coordinates) :
    (mulIn V ψ hψ g).1.1 x = ψ x • g.1.1 x := rfl

theorem pairIn_mulIn (Ω : TopologicalSpace.Opens Coordinates) (f : Coordinates → FormValue n k)
    (hf : ContinuousOn f Ω) (ψ : Coordinates → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (g : CcIn n k (Ω : Set Coordinates)) :
    pairIn Ω f hf (mulIn (Ω : Set Coordinates) ψ hψ g) =
      ∫ x, ψ x * (coordinateDensity x * formPairing n k x (f x) (g.1.1 x)) := by
  rw [pairIn_apply]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  change coordinateDensity x * formPairing n k x (f x) (ψ x • g.1.1 x) = _
  rw [formPairing_smul_right]
  ring

/-- Evaluation of a finite sum of test forms is the sum of the evaluations. -/
theorem CcIn_sum_apply {V : Set Coordinates} {ι : Type*} (s : Finset ι) (h : ι → CcIn n k V)
    (x : Coordinates) : (∑ i ∈ s, h i).1.1 x = ∑ i ∈ s, (h i).1.1 x := by
  let ev : CcIn n k V →ₗ[ℝ] FormValue n k :=
    { toFun := fun g => g.1.1 x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact map_sum ev h s

/-- A test form is the sum of its multiples by a family of smooth functions summing to one on its
support. -/
theorem eq_sum_mulIn {V : Set Coordinates} {ι : Type*} [Fintype ι] (ψ : ι → Coordinates → ℝ)
    (hψs : ∀ i, ContDiff ℝ ∞ (ψ i)) (g : CcIn n k V)
    (hs : ∀ x ∈ tsupport g.1.1, ∑ i, ψ i x = 1) :
    g = ∑ i, mulIn V (ψ i) (hψs i) g := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  have h1 : ((∑ i, mulIn V (ψ i) (hψs i) g : CcIn n k V).1.1 : Coordinates → FormValue n k) x =
      ∑ i, ψ i x • g.1.1 x :=
    CcIn_sum_apply Finset.univ (fun i => mulIn V (ψ i) (hψs i) g) x
  refine Eq.trans ?_ h1.symm
  by_cases hx : x ∈ tsupport g.1.1
  · have e1 : (∑ i, ψ i x) • g.1.1 x = ∑ i, ψ i x • g.1.1 x := fv_sum_smul _ _ _
    have e2 : (∑ i, ψ i x) • g.1.1 x = g.1.1 x :=
      (congrArg (fun r : ℝ => r • g.1.1 x) (hs x hx)).trans (fv_one_smul _)
    exact e2.symm.trans e1
  · have h0 : g.1.1 x = 0 := image_eq_zero_of_notMem_tsupport hx
    have h2 : ∑ i, ψ i x • g.1.1 x = 0 :=
      Finset.sum_eq_zero fun i _ =>
        (congrArg (fun v : FormValue n k => ψ i x • v) h0).trans (fv_smul_zero _)
    exact h0.trans h2.symm

/-- The representation of a functional by a smooth form is a local property. -/
theorem pairIn_local_to_global (V : TopologicalSpace.Opens Coordinates)
    (A : CcIn n k (V : Set Coordinates) →ₗ[ℝ] ℝ) (f : Coordinates → FormValue n k)
    (hf : ContinuousOn f V)
    (hloc : ∀ x ∈ (V : Set Coordinates), ∃ U : Set Coordinates, IsOpen U ∧ x ∈ U ∧
      ∀ g : CcIn n k (V : Set Coordinates), tsupport g.1.1 ⊆ U → A g = pairIn V f hf g) :
    A = pairIn V f hf := by
  classical
  apply LinearMap.ext
  intro g
  have hKc : IsCompact (tsupport g.1.1) := g.1.2.2.1
  have hKV : tsupport g.1.1 ⊆ V := g.2
  choose! U hUo hxU hUA using hloc
  obtain ⟨t, hcov⟩ := hKc.elim_nhds_subcover' (fun x hx => U x)
    (fun x hx => (hUo x (hKV hx)).mem_nhds (hxU x (hKV hx)))
  have hW : tsupport g.1.1 ⊆ ⋃ i : ↥t, U i.1.1 := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hcov hx)
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩
  obtain ⟨ψ, hψ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (𝓘(ℝ, Coordinates))
    hKc.isClosed (fun i : ↥t => U i.1.1) (fun i => hUo _ (hKV i.1.2)) hW
  have hψs : ∀ i : ↥t, ContDiff ℝ ∞ (ψ i) := fun i => contMDiff_iff_contDiff.mp (ψ i).contMDiff
  have hdecomp : g = ∑ i : ↥t, mulIn (V : Set Coordinates) (ψ i) (hψs i) g :=
    eq_sum_mulIn (fun i : ↥t => ψ i) hψs g (fun x hx => by
      have := ψ.sum_eq_one hx
      rwa [finsum_eq_sum_of_fintype] at this)
  have hA : A g = ∑ i : ↥t, A (mulIn (V : Set Coordinates) (ψ i) (hψs i) g) := by
    exact (congrArg A hdecomp).trans (map_sum A _ _)
  have hP : pairIn V f hf g = ∑ i : ↥t, pairIn V f hf (mulIn (V : Set Coordinates) (ψ i) (hψs i) g) := by
    exact (congrArg (pairIn V f hf) hdecomp).trans (map_sum (pairIn V f hf) _ _)
  refine hA.trans (Eq.trans ?_ hP.symm)
  apply Finset.sum_congr rfl
  intro i _
  apply hUA i.1.1 (hKV i.1.2)
  exact (tsupport_smul_subset_left (ψ i) g.1.1).trans (hψ i)

/-! ### Inclusions of supports -/

theorem CcIn_mono {U V : Set Coordinates} (h : U ⊆ V) : CcIn n k U ≤ CcIn n k V :=
  fun _ hg => hg.trans h

/-- Inclusion of test forms supported in a smaller set. -/
def inclIn {U V : Set Coordinates} (h : U ⊆ V) : CcIn n k U →ₗ[ℝ] CcIn n k V :=
  Submodule.inclusion (CcIn_mono h)

theorem inclIn_coe {U V : Set Coordinates} (h : U ⊆ V) (g : CcIn n k U) :
    (inclIn h g).1 = g.1 := rfl

theorem deltaIn_inclIn {U V : Set Coordinates} (h : U ⊆ V) (g : CcIn n (k + 1) U) :
    deltaIn n k V (inclIn h g) = inclIn h (deltaIn n k U g) := rfl

/-! ### The Weyl lemma on a box -/

theorem weyl_box (b : WeakCubeFive ≃L[ℝ] Coordinates) (c : Coordinates)
    (hΩ : (coordinateTestBox b c : Set Coordinates) ⊆ positiveCoordinates)
    (A : CcIn n 0 (coordinateTestBox b c : Set Coordinates) →ₗ[ℝ] ℝ)
    (θ : Coordinates → FormValue n 1) (hθ : ContDiffOn ℝ ∞ θ (coordinateTestBox b c))
    (hA : ∀ g : CcIn n 1 (coordinateTestBox b c : Set Coordinates),
      A (deltaIn n 0 (coordinateTestBox b c : Set Coordinates) g) =
        pairIn (coordinateTestBox b c) θ hθ.continuousOn g) :
    ∃ (f : Coordinates → FormValue n 0) (hf : ContDiffOn ℝ ∞ f (coordinateTestBox b c)),
      ∀ g : CcIn n 0 (coordinateTestBox b c : Set Coordinates),
        A g = pairIn (coordinateTestBox b c) f hf.continuousOn g := by
  have hW : formWeakExterior n 0 (coordinateTestBox b c) (bridge (coordinateTestBox b c) hΩ A) =
      valuedRegularCurrent volume (coordinateTestBox b c) θ hθ.continuousOn := by
    rw [bridge_exterior]
    exact bridge_regular (coordinateTestBox b c) hΩ _ θ hθ.continuousOn (fun g => hA g)
  obtain ⟨f, hf, hrep⟩ := coordinateTestBox_zeroForm_smooth_of_smooth_exterior n b c
    (bridge (coordinateTestBox b c) hΩ A) θ hθ hW
  refine ⟨f, hf, fun g => ?_⟩
  have h1 := unbridge_bridge (coordinateTestBox b c) hΩ A
  rw [hrep, unbridge_regular_eq] at h1
  exact (LinearMap.congr_fun h1 g).symm

theorem pairIn_congr_of_eqOn (Ω : TopologicalSpace.Opens Coordinates) {f f' : Coordinates → FormValue n k}
    (hf : ContinuousOn f Ω) (hf' : ContinuousOn f' Ω) (g : CcIn n k (Ω : Set Coordinates))
    (h : EqOn f f' (tsupport g.1.1)) : pairIn Ω f hf g = pairIn Ω f' hf' g := by
  rw [pairIn_apply, pairIn_apply]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  by_cases hx : x ∈ tsupport g.1.1
  · simp only [h hx]
  · have h0 : g.1.1 x = 0 := image_eq_zero_of_notMem_tsupport hx
    simp [h0]

/-- **Gluing of local smooth representatives.**  A functional on test forms supported in an open
set which is represented by a smooth form near every point is represented by one smooth form. -/
theorem exists_smooth_of_local (V : TopologicalSpace.Opens Coordinates)
    (hV : (V : Set Coordinates) ⊆ positiveCoordinates)
    (A : CcIn n k (V : Set Coordinates) →ₗ[ℝ] ℝ)
    (key : ∀ x ∈ (V : Set Coordinates), ∃ (U : TopologicalSpace.Opens Coordinates)
      (hU : (U : Set Coordinates) ⊆ V) (_ : x ∈ (U : Set Coordinates))
      (f : Coordinates → FormValue n k) (hf : ContDiffOn ℝ ∞ f U),
      ∀ g : CcIn n k (U : Set Coordinates), A (inclIn hU g) = pairIn U f hf.continuousOn g) :
    ∃ (f : Coordinates → FormValue n k) (hf : ContDiffOn ℝ ∞ f V),
      ∀ g : CcIn n k (V : Set Coordinates), A g = pairIn V f hf.continuousOn g := by
  classical
  choose U hU hxU f hf hrep using key
  let F : Coordinates → FormValue n k := fun y => if hy : y ∈ (V : Set Coordinates) then f y hy y else 0
  have hF : ∀ y (hy : y ∈ (V : Set Coordinates)), ∀ z ∈ (U y hy : Set Coordinates), F z = f y hy z := by
    intro y hy z hz
    have hzV : z ∈ (V : Set Coordinates) := hU y hy hz
    simp only [F, dite_eq_left hzV]
    have hzz : z ∈ (U z hzV : Set Coordinates) := hxU z hzV
    let Ω'' : TopologicalSpace.Opens Coordinates := U z hzV ⊓ U y hy
    have hΩ'' : (Ω'' : Set Coordinates) ⊆ positiveCoordinates :=
      (inter_subset_left.trans ((hU z hzV).trans hV))
    have hc1 : ContinuousOn (f z hzV) Ω'' := (hf z hzV).continuousOn.mono inter_subset_left
    have hc2 : ContinuousOn (f y hy) Ω'' := (hf y hy).continuousOn.mono inter_subset_right
    have heq := eqOn_of_pairIn_eq Ω'' hΩ'' (f z hzV) (f y hy) hc1 hc2 (fun g => by
      have g1 : (g.1 : Cc n k) ∈ CcIn n k (U z hzV : Set Coordinates) := g.2.trans inter_subset_left
      have g2 : (g.1 : Cc n k) ∈ CcIn n k (U y hy : Set Coordinates) := g.2.trans inter_subset_right
      have e1 := hrep z hzV ⟨g.1, g1⟩
      have e2 := hrep y hy ⟨g.1, g2⟩
      have e3 : A (inclIn (hU z hzV) ⟨g.1, g1⟩) = A (inclIn (hU y hy) ⟨g.1, g2⟩) := rfl
      have i1 : pairIn Ω'' (f z hzV) hc1 g =
          pairIn (U z hzV) (f z hzV) (hf z hzV).continuousOn ⟨g.1, g1⟩ := rfl
      have i2 : pairIn Ω'' (f y hy) hc2 g =
          pairIn (U y hy) (f y hy) (hf y hy).continuousOn ⟨g.1, g2⟩ := rfl
      exact i1.trans (e1.symm.trans (e3.trans (e2.trans i2.symm))))
    exact heq ⟨hzz, hz⟩
  have hFc : ContDiffOn ℝ ∞ F V := by
    apply contDiffOn_of_locally_contDiffOn
    intro y hy
    exact ⟨U y hy, (U y hy).isOpen, hxU y hy, ((hf y hy).congr (fun z hz => hF y hy z hz)).mono inter_subset_right⟩
  refine ⟨F, hFc, fun g => ?_⟩
  have hglob := pairIn_local_to_global V A F hFc.continuousOn (fun x hx =>
    ⟨U x hx, (U x hx).isOpen, hxU x hx, fun g hg => by
      have e1 := hrep x hx ⟨g.1, hg⟩
      refine e1.trans ?_
      rw [pairIn_apply, pairIn_apply]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro z
      by_cases hz : z ∈ tsupport g.1.1
      · change coordinateDensity z * formPairing n k z (f x hx z) (g.1.1 z) =
          coordinateDensity z * formPairing n k z (F z) (g.1.1 z)
        rw [hF x hx z (hg hz)]
      · have h0 : g.1.1 z = 0 := image_eq_zero_of_notMem_tsupport hz
        change coordinateDensity z * formPairing n k z (f x hx z) (g.1.1 z) =
          coordinateDensity z * formPairing n k z (F z) (g.1.1 z)
        rw [h0]
        simp⟩)
  exact LinearMap.congr_fun hglob g


theorem weyl_open (V : TopologicalSpace.Opens Coordinates)
    (hV : (V : Set Coordinates) ⊆ positiveCoordinates)
    (A : CcIn n 0 (V : Set Coordinates) →ₗ[ℝ] ℝ)
    (θ : Coordinates → FormValue n 1) (hθ : ContDiffOn ℝ ∞ θ V)
    (hA : ∀ g : CcIn n 1 (V : Set Coordinates),
      A (deltaIn n 0 (V : Set Coordinates) g) = pairIn V θ hθ.continuousOn g) :
    ∃ (f : Coordinates → FormValue n 0) (hf : ContDiffOn ℝ ∞ f V),
      ∀ g : CcIn n 0 (V : Set Coordinates), A g = pairIn V f hf.continuousOn g := by
  have key : ∀ x ∈ (V : Set Coordinates), ∃ (U : TopologicalSpace.Opens Coordinates)
      (hU : (U : Set Coordinates) ⊆ V) (_ : x ∈ (U : Set Coordinates))
      (f : Coordinates → FormValue n 0) (hf : ContDiffOn ℝ ∞ f U),
      ∀ g : CcIn n 0 (U : Set Coordinates), A (inclIn hU g) = pairIn U f hf.continuousOn g := by
    intro x hx
    obtain ⟨b, c, hxb, hbV, -⟩ := exists_coordinateTestBox_in_open V.isOpen hx
    have hA' : ∀ g : CcIn n 1 (coordinateTestBox b c : Set Coordinates),
        (A.comp (inclIn hbV)) (deltaIn n 0 (coordinateTestBox b c : Set Coordinates) g) =
          pairIn (coordinateTestBox b c) θ (hθ.mono hbV).continuousOn g := by
      intro g
      change A (inclIn hbV (deltaIn n 0 _ g)) = _
      rw [← deltaIn_inclIn]
      exact (hA (inclIn hbV g)).trans rfl
    obtain ⟨f, hf, hrep⟩ := weyl_box b c (hbV.trans hV) (A.comp (inclIn hbV)) θ (hθ.mono hbV) hA'
    exact ⟨coordinateTestBox b c, hbV, hxb, f, hf, fun g => hrep g⟩
  exact exists_smooth_of_local V hV A key

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
