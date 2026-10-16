module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Intrinsic.SmoothGluing

@[expose] public section

/-! Actual local smooth representability is local for genuine intrinsic currents. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set TopologicalSpace PolynomialCoefficientMetric SymmetricSpaceCovering SmoothCoveringDeRham

/-- A genuine intrinsic current locally equal to actual smooth currents has one global actual
smooth equivariant representative on its actual quotient open. -/
theorem intrinsicCurrent_smooth_of_locally_smooth (n k : ℕ) (U : Set OrbitSpace) (hU : IsOpen U)
    (T : IntrinsicCurrent n k U)
    (h : ∀ q : U, ∃ (V : Opens (TopCat.of OrbitSpace)) (hVU : (V : Set OrbitSpace) ⊆ U),
      q.val ∈ V ∧ ∃ a : EquivariantForm (deckRepresentation n) V k,
        intrinsicCurrentRestriction n k hVU T = intrinsicSmoothCurrent n k V V.isOpen a) :
    ∃ a : EquivariantForm (deckRepresentation n) U k, T = intrinsicSmoothCurrent n k U hU a := by
  classical
  let V (q : U) := (h q).choose
  let hVU (q : U) : (V q : Set OrbitSpace) ⊆ U := (h q).choose_spec.choose
  have hq (q : U) : q.val ∈ V q := (h q).choose_spec.choose_spec.1
  let a (q : U) : EquivariantForm (deckRepresentation n) (V q) k :=
    (h q).choose_spec.choose_spec.2.choose
  have ha (q : U) : intrinsicCurrentRestriction n k (hVU q) T =
      intrinsicSmoothCurrent n k (V q) (V q).isOpen (a q) :=
    (h q).choose_spec.choose_spec.2.choose_spec
  have hcover : U ⊆ ⋃ q : U, (V q : Set OrbitSpace) := by
    intro q hqU
    exact mem_iUnion.mpr ⟨⟨q, hqU⟩, hq ⟨q, hqU⟩⟩
  exact intrinsicSmoothCurrent_glue n k U hU T V hVU hcover a ha

end TernaryPoly.PolynomialFormWeakSmooth
