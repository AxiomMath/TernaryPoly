module

public import TernaryPeriodPolynomials.DifferentialForm.Metric.DescentSmooth

@[expose] public section


/-! Exact projected support and pointwise definiteness for the descended scalar metric. -/
noncomputable section
namespace TernaryPoly.PolynomialFormMetric
open SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering
open PolynomialCoefficientMetric PolynomialCoefficientBundle SmoothCoveringDeRham SmoothLocalDeRham
open Set
open scoped ContDiff Manifold Topology

theorem support_scalarPairing (n k : ℕ) {U : Set OrbitSpace}
    (a b : EquivariantForm (deckRepresentation n) U k) :
    Function.support (scalarPairing n k a b) ⊆
      (coordinateProjection '' Function.support a.val.val) ∩
        (coordinateProjection '' Function.support b.val.val) := by
  intro q hq
  let x := coordinateChart (chosenLift q)
  have hproj : coordinateProjection x = q := by
    simp only [x, coordinateProjection, coordinateChart.left_inv (by simp), chosenLift_projection]
  have ha : a.val.val x ≠ 0 := by
    intro ha
    apply hq
    change formPairing n k x (a.val.val x) (b.val.val x) = 0
    rw [ha, formPairing_zero_left]
  have hb : b.val.val x ≠ 0 := by
    intro hb
    apply hq
    change formPairing n k x (a.val.val x) (b.val.val x) = 0
    rw [hb, formPairing_zero_right]
  exact ⟨⟨x, ha, hproj⟩, ⟨x, hb, hproj⟩⟩

/-- Closed support is contained in the intersection of the actual closed projected supports. -/
theorem tsupport_scalarPairing (n k : ℕ) {U : Set OrbitSpace}
    (a b : EquivariantForm (deckRepresentation n) U k) :
    tsupport (scalarPairing n k a b) ⊆ quotientSupport a ∩ quotientSupport b := by
  apply closure_minimal _ (isClosed_closure.inter isClosed_closure)
  intro q hq
  have h := support_scalarPairing n k a b hq
  exact ⟨subset_closure h.1, subset_closure h.2⟩

theorem scalarPairing_outside (n k : ℕ) {U : Set OrbitSpace}
    (a b : EquivariantForm (deckRepresentation n) U k) {q : OrbitSpace} (hq : q ∉ U) :
    scalarPairing n k a b q = 0 := by
  have hx : coordinateChart (chosenLift q) ∉ liftedDomain U := by
    intro hx
    apply hq
    simpa only [Set.mem_preimage, coordinateProjection, coordinateChart.left_inv (by simp), chosenLift_projection] using hx.2
  change formPairing n k _ (a.val.val _) (b.val.val _) = 0
  rw [Form.outside a.val hx, formPairing_zero_left]

/-- Vanishing of the squared norm everywhere detects the actual covering form. -/
theorem scalarPairing_self_identically_zero (n k : ℕ) {U : Set OrbitSpace}
    (a : EquivariantForm (deckRepresentation n) U k) : scalarPairing n k a a = 0 ↔ a = 0 := by
  constructor
  · intro h
    apply Subtype.ext
    apply Subtype.ext
    funext x
    by_cases hx : x ∈ positiveCoordinates
    · apply (scalarPairing_self_eq_zero n k a x hx).mp
      exact congrFun h (coordinateProjection x)
    · exact Form.outside a.val (fun hd => hx hd.1)
  · rintro rfl
    funext q
    exact formPairing_zero_left n k _ _

/-- Compact projected support of either factor gives compact support of the scalar pairing. -/
theorem hasCompactSupport_scalarPairing (n k : ℕ) {U : Set OrbitSpace}
    (a b : EquivariantForm (deckRepresentation n) U k)
    (ha : IsCompact (quotientSupport a)) : HasCompactSupport (scalarPairing n k a b) :=
  ha.of_isClosed_subset (isClosed_tsupport _) (fun _ hq => (tsupport_scalarPairing n k a b hq).1)

theorem scalarPairing_add_left (n k : ℕ) {U : Set OrbitSpace}
    (a b c : EquivariantForm (deckRepresentation n) U k) :
    scalarPairing n k (a + b) c = scalarPairing n k a c + scalarPairing n k b c := by
  funext q
  exact formPairing_add_left n k _ _ _ _

theorem scalarPairing_smul_left (n k : ℕ) {U : Set OrbitSpace} (t : ℝ)
    (a b : EquivariantForm (deckRepresentation n) U k) :
    scalarPairing n k (t • a) b = t • scalarPairing n k a b := by
  funext q
  exact formPairing_smul_left n k _ t _ _

theorem scalarPairing_add_right (n k : ℕ) {U : Set OrbitSpace}
    (a b c : EquivariantForm (deckRepresentation n) U k) :
    scalarPairing n k a (b + c) = scalarPairing n k a b + scalarPairing n k a c := by
  funext q
  exact formPairing_add_right n k _ _ _ _

theorem scalarPairing_smul_right (n k : ℕ) {U : Set OrbitSpace} (t : ℝ)
    (a b : EquivariantForm (deckRepresentation n) U k) :
    scalarPairing n k a (t • b) = t • scalarPairing n k a b := by
  funext q
  exact formPairing_smul_right n k _ t _ _

end TernaryPoly.PolynomialFormMetric
