module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.Cutoff.Strong
public import TernaryPeriodPolynomials.DifferentialForm.WeakTests

@[expose] public section


/-! Compact support of Hilbert cutoff outputs is proved by actual compact-test annihilation. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Set PolynomialFormHilbert PolynomialCoefficientMetric PolynomialFormCoordinates
  SmoothLocalDeRham SmoothCoveringDeRham SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpaceRiemannian
open scoped ContDiff Manifold SymmetricSpaceRiemannian LinearPMap

/-- Support for an actual Hilbert form, expressed only through its genuine compact smooth tests. -/
def HasWeakSupportIn (n k : ℕ) (K : Set OrbitSpace) (u : Hilbert n k) : Prop :=
  ∀ a : Core n k, Disjoint (quotientSupport a.val) K → inner ℝ u (inclusion n k a) = 0

theorem coreScalarMultiply_eq_zero (n k : ℕ) (χ : OrbitSpace → ℝ)
    (hχ : ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ χ) (a : Core n k)
    (he : ∀ q ∈ quotientSupport a.val, χ q = 0) : coreScalarMultiply n k χ hχ a = 0 := by
  apply Subtype.ext
  apply Subtype.ext
  apply Form.ext
  intro x _hx
  change (coreScalarMultiply n k χ hχ a).val.val.val x = 0
  apply (coreScalarMultiply_apply n k χ hχ a x).trans
  by_cases ha : a.val.val.val x = 0
  · exact (congrArg (χ (coordinateProjection x) • ·) ha).trans (smul_zero _)
  · have hx : coordinateProjection x ∈ quotientSupport a.val :=
      subset_closure (mem_image_of_mem coordinateProjection ha)
    exact (congrArg (fun t : ℝ => t • a.val.val.val x) (he _ hx)).trans (zero_smul ℝ _)

theorem scalarMultiplier_weakSupport (n k : ℕ) (χ : OrbitSpace → ℝ)
    (hχ : ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ χ) (A : ℝ) (hA : 0 ≤ A)
    (hb : ∀ q, |χ q| ≤ A) (u : Hilbert n k) :
    HasWeakSupportIn n k (tsupport χ) (scalarMultiplier n k χ hχ A hA hb u) := by
  intro a ha
  have hz : coreScalarMultiply n k χ hχ a = 0 := coreScalarMultiply_eq_zero n k χ hχ a
    (fun q hq => image_eq_zero_of_notMem_tsupport (fun h => Set.disjoint_left.mp ha hq h))
  have hm : scalarMultiplier n k χ hχ A hA hb (inclusion n k a) = 0 :=
    (scalarMultiplier_inclusion n k χ hχ A hA hb a).trans
      ((congrArg (inclusion n k) hz).trans (map_zero _))
  exact (inner_scalarMultiplier n k χ hχ A hA hb u (inclusion n k a)).trans
    ((congrArg (inner ℝ u) hm).trans (inner_zero_right u))

/-- No pointwise representative or unproved regularity of the Hilbert input is used. -/
theorem cutoffMultiplier_weakSupport (n k : ℕ) (c : BoundedCutoffSequence) (j : ℕ) (u : Hilbert n k) :
    HasWeakSupportIn n k (tsupport (c.toFun j)) (cutoffMultiplier n k c j u) :=
  scalarMultiplier_weakSupport n k (c.toFun j) (c.smooth j) 1 zero_le_one
    (fun q => by rw [abs_of_nonneg (c.range j q).1]; exact (c.range j q).2) u

/-- The support set just proved for every Hilbert cutoff output is actually compact. -/
theorem cutoffMultiplier_compact_weakSupport (n k : ℕ) (c : BoundedCutoffSequence) (j : ℕ)
    (u : Hilbert n k) : ∃ K : Set OrbitSpace, IsCompact K ∧ HasWeakSupportIn n k K (cutoffMultiplier n k c j u) :=
  ⟨tsupport (c.toFun j), c.compact j, cutoffMultiplier_weakSupport n k c j u⟩

/-- Maximal exterior differentiation preserves support in the actual compact-test sense. -/
theorem HasWeakSupportIn.maximalDifferential {n k : ℕ} {K : Set OrbitSpace}
    {u : Hilbert n k} {du : Hilbert n (k + 1)} (h : HasWeakSupportIn n k K u)
    (hu : (u, du) ∈ (maximalDifferential n k).graph) : HasWeakSupportIn n (k + 1) K du := by
  intro b hb
  have hs : quotientSupport (compactAdjoint n k b).val ⊆ quotientSupport b.val :=
    quotientSupport_equivariantAdjoint n k b.val
  exact ((mem_maximalDifferential_graph_iff n k u du).mp hu b).trans
    (h (compactAdjoint n k b) (hb.mono_left hs))

/-- Maximal codifferentiation preserves support by the literal compact differential on tests. -/
theorem HasWeakSupportIn.maximalCodifferential {n k : ℕ} {K : Set OrbitSpace}
    {u : Hilbert n (k + 1)} {δu : Hilbert n k} (h : HasWeakSupportIn n (k + 1) K u)
    (hu : (u, δu) ∈ (maximalCodifferential n k).graph) : HasWeakSupportIn n k K δu := by
  intro a ha
  let d := compactDifferential (deckRepresentation n) isOpen_univ k
  have hs : quotientSupport (d a).val ⊆ quotientSupport a.val :=
    quotientSupport_differential isOpen_univ a.val
  exact ((mem_maximalCodifferential_graph_iff n k u δu).mp hu a).trans (h (d a) (ha.mono_left hs))

end TernaryPoly.PolynomialFormConnection
