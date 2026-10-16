module

public import TernaryPeriodPolynomials.DifferentialForm.CoefficientBundle.ZeroForms

@[expose] public section


/-! Exact local identification with the existing degree-zero covering de Rham sections. -/
noncomputable section
namespace TernaryPoly.PolynomialCoefficientBundle
open PolynomialCoefficientMetric SymmetricSpacePositive SymmetricSpaceCovering
  SymmetricSpaceQuotientManifold SymmetricSpaceCharts SmoothLocalDeRham SmoothCoveringDeRham
open Set Filter Topology Bundle Manifold ContinuousAlternatingMap
open scoped ContDiff Manifold

theorem coordinateChart_liftedDomain (U : Set OrbitSpace) (S : Space) :
    coordinateChart S ∈ liftedDomain U ↔ quotientProjection S ∈ U := by
  have h : coordinateChart.symm (coordinateChart S) = S := coordinateChart.left_inv (by simp)
  simp only [liftedDomain, mem_inter_iff, mem_preimage, coordinateProjection, h]
  exact and_iff_right (extract_mem S)

def zeroFormFunction (n : ℕ) {U : Set OrbitSpace} (w : EquivariantForm (deckRepresentation n) U 0)
    (S : Space) : Coefficients n := decodeZero n ((w.val.val : RawForm Coordinates (Coefficients n) 0) (coordinateChart S))

theorem zeroFormFunction_outside (n : ℕ) {U : Set OrbitSpace}
    (w : EquivariantForm (deckRepresentation n) U 0) (S : Space) (hS : quotientProjection S ∉ U) :
    zeroFormFunction n w S = 0 := by
  have hx : coordinateChart S ∉ liftedDomain U := (coordinateChart_liftedDomain U S).not.mpr hS
  unfold zeroFormFunction
  rw [show w.val.val (coordinateChart S) = 0 from Form.outside w.val hx]
  exact zeroEquiv.symm.map_zero

theorem zeroFormFunction_equivariant (n : ℕ) {U : Set OrbitSpace}
    (w : EquivariantForm (deckRepresentation n) U 0) : IsEquivariantFunction n (zeroFormFunction n w) := by
  intro g S
  by_cases hS : quotientProjection S ∈ U
  · have h := (zero_equivariant_iff n U _).mp w.property g (coordinateChart S)
      ((coordinateChart_liftedDomain U S).mpr hS)
    rw [deckMap_chart] at h
    exact h
  · rw [zeroFormFunction_outside n w S hS, _root_.map_zero,
      zeroFormFunction_outside n w (g • S) (by simpa only [quotientProjection_quotientCovering.map_smul] using hS)]

theorem smooth_zeroFormFunction (n : ℕ) {U : Set OrbitSpace}
    (w : EquivariantForm (deckRepresentation n) U 0) :
    ContMDiffOn 𝓘(ℝ, Coordinates) 𝓘(ℝ, Coefficients n) ∞ (zeroFormFunction n w) (quotientProjection ⁻¹' U) := by
  exact (smooth_toFunction w.val).contMDiffOn.comp coordinateChart_contMDiff.contMDiffOn
    (fun S hS => (coordinateChart_liftedDomain U S).mpr hS)

theorem zeroFormFunction_coveringZeroForm (n : ℕ) {U : Set OrbitSpace}
    (f : Space → Coefficients n) (he : IsEquivariantFunction n f)
    (hs : ContMDiffOn 𝓘(ℝ, Coordinates) 𝓘(ℝ, Coefficients n) ∞ f (quotientProjection ⁻¹' U))
    (hz : ∀ S, quotientProjection S ∉ U → f S = 0) :
    zeroFormFunction n (coveringZeroForm n f he hs) = f := by
  funext S
  by_cases hS : quotientProjection S ∈ U
  · change decodeZero n ((ofFunction (coordinateFunction n f) (smooth_coordinateFunction n f hs)).val (coordinateChart S)) = f S
    rw [ofFunction_apply _ _ ((coordinateChart_liftedDomain U S).mpr hS), decodeZero_encode]
    unfold coordinateFunction
    rw [coordinateChart.left_inv (by simp)]
  · rw [zeroFormFunction_outside n _ S hS, hz S hS]

theorem coveringZeroForm_zeroFormFunction (n : ℕ) {U : Set OrbitSpace}
    (w : EquivariantForm (deckRepresentation n) U 0) :
    coveringZeroForm n (zeroFormFunction n w) (zeroFormFunction_equivariant n w)
      (smooth_zeroFormFunction n w) = w := by
  apply Subtype.ext
  apply Form.ext
  intro x hx
  change (ofFunction (coordinateFunction n (zeroFormFunction n w))
    (smooth_coordinateFunction n _ (smooth_zeroFormFunction n w))).val x = _
  rw [ofFunction_apply _ _ hx]
  change zeroEquiv (decodeZero n ((w.val.val : RawForm Coordinates (Coefficients n) 0)
    (coordinateChart (coordinateChart.symm x)))) = _
  rw [coordinateChart.right_inv (by simpa only [coordinateChart_target] using hx.1)]
  exact zeroEquiv.apply_symm_apply _

def sectionToZeroForm (n : ℕ) {U : Set OrbitSpace} (hU : IsOpen U) (s : SmoothSectionOn n U) :
    EquivariantForm (deckRepresentation n) U 0 :=
  coveringZeroForm n (sectionFunction n s.val) (sectionFunction_equivariant n s.val)
    (smoothOn_sectionFunction n hU s.val s.property.1)

def zeroFormToSection (n : ℕ) {U : Set OrbitSpace} (hU : IsOpen U)
    (w : EquivariantForm (deckRepresentation n) U 0) : SmoothSectionOn n U :=
  ⟨functionSection n (zeroFormFunction n w),
    smoothOn_functionSection n hU _ (zeroFormFunction_equivariant n w) (smooth_zeroFormFunction n w),
    fun _b hb => functionSection_outside n _ (zeroFormFunction_outside n w) hb⟩

@[simp] theorem zeroFormToSection_sectionToZeroForm (n : ℕ) {U : Set OrbitSpace} (hU : IsOpen U)
    (s : SmoothSectionOn n U) : zeroFormToSection n hU (sectionToZeroForm n hU s) = s := by
  apply Subtype.ext
  dsimp only [zeroFormToSection, sectionToZeroForm]
  rw [zeroFormFunction_coveringZeroForm n _ _ _ (fun S hS => sectionFunction_outside n s.val s.property.2 hS),
    functionSection_sectionFunction]

@[simp] theorem sectionToZeroForm_zeroFormToSection (n : ℕ) {U : Set OrbitSpace} (hU : IsOpen U)
    (w : EquivariantForm (deckRepresentation n) U 0) : sectionToZeroForm n hU (zeroFormToSection n hU w) = w := by
  have he := sectionFunction_functionSection n (zeroFormFunction n w) (zeroFormFunction_equivariant n w)
  unfold sectionToZeroForm zeroFormToSection
  simp only [he]
  exact coveringZeroForm_zeroFormFunction n w

/-- Smooth sections on each genuine quotient open set are exactly the already constructed
covering de Rham zero-forms, with the same coefficient action and zero extension. -/
def sectionsZeroFormEquiv (n : ℕ) {U : Set OrbitSpace} (hU : IsOpen U) :
    SmoothSectionOn n U ≃ EquivariantForm (deckRepresentation n) U 0 where
  toFun := sectionToZeroForm n hU
  invFun := zeroFormToSection n hU
  left_inv := zeroFormToSection_sectionToZeroForm n hU
  right_inv := sectionToZeroForm_zeroFormToSection n hU

end TernaryPoly.PolynomialCoefficientBundle
