module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Intrinsic.SmoothGlobal
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Intrinsic.CoverSeparation
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.FormGluing

@[expose] public section

/-! Gluing actual smooth representatives of a genuine intrinsic current. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set TopologicalSpace PolynomialCoefficientMetric PolynomialFormCoordinates SymmetricSpaceCharts
  SymmetricSpacePositive SymmetricSpaceCovering SmoothCoveringDeRham SmoothLocalDeRham
  SmoothSingularGlobal

/-- Actual smooth representatives of one intrinsic current agree on every genuine overlap. -/
theorem intrinsicSmoothCurrent_representatives_agree (n k : ℕ) (U : Set OrbitSpace)
    (T : IntrinsicCurrent n k U) {V W : Set OrbitSpace} (hV : IsOpen V) (hW : IsOpen W)
    (hVU : V ⊆ U) (hWU : W ⊆ U)
    (a : EquivariantForm (deckRepresentation n) V k)
    (b : EquivariantForm (deckRepresentation n) W k)
    (ha : intrinsicCurrentRestriction n k hVU T = intrinsicSmoothCurrent n k V hV a)
    (hb : intrinsicCurrentRestriction n k hWU T = intrinsicSmoothCurrent n k W hW b) :
    restrictEquivariant (deckRepresentation n) (inter_subset_left : V ∩ W ⊆ V) k a =
      restrictEquivariant (deckRepresentation n) (inter_subset_right : V ∩ W ⊆ W) k b := by
  apply intrinsicSmoothCurrent_injective n k (V ∩ W) (hV.inter hW)
  apply (intrinsicSmoothCurrent_restriction n k hV (hV.inter hW) inter_subset_left a).symm.trans
  apply (congrArg (intrinsicCurrentRestriction n k (inter_subset_left : V ∩ W ⊆ V)) ha.symm).trans
  apply Eq.trans (show intrinsicCurrentRestriction n k inter_subset_left
    (intrinsicCurrentRestriction n k hVU T) = intrinsicCurrentRestriction n k inter_subset_right
      (intrinsicCurrentRestriction n k hWU T) from rfl)
  apply (congrArg (intrinsicCurrentRestriction n k (inter_subset_right : V ∩ W ⊆ W)) hb).trans
  exact intrinsicSmoothCurrent_restriction n k hW (hV.inter hW) inter_subset_right b

/-- A genuine intrinsic current locally represented by actual smooth forms on an arbitrary
actual open cover is globally represented by an actual smooth equivariant form. -/
theorem intrinsicSmoothCurrent_glue (n k : ℕ) (U : Set OrbitSpace) (hU : IsOpen U)
    (T : IntrinsicCurrent n k U) {ι : Type} (V : ι → Opens (TopCat.of OrbitSpace))
    (hVU : ∀ i, (V i : Set OrbitSpace) ⊆ U) (hcover : U ⊆ ⋃ i, (V i : Set OrbitSpace))
    (a : ∀ i, EquivariantForm (deckRepresentation n) (V i : Set OrbitSpace) k)
    (ha : ∀ i, intrinsicCurrentRestriction n k (hVU i) T =
      intrinsicSmoothCurrent n k (V i : Set OrbitSpace) (V i).isOpen (a i)) :
    ∃ b : EquivariantForm (deckRepresentation n) U k, T = intrinsicSmoothCurrent n k U hU b := by
  have hc : (formPresheaf (deckRepresentation n) k).IsCompatible V a := by
    intro i j
    exact intrinsicSmoothCurrent_representatives_agree n k U T (V i).isOpen (V j).isOpen
      (hVU i) (hVU j) (a i) (a j) (ha i) (ha j)
  have hUU : U ⊆ ((iSup V : Opens (TopCat.of OrbitSpace)) : Set OrbitSpace) := by
    intro q hq
    exact Opens.mem_iSup.mpr (mem_iUnion.mp (hcover hq))
  let b := restrictEquivariant (deckRepresentation n) hUU k
    (gluedForm (deckRepresentation n) V k a hc)
  have hb (i : ι) : restrictEquivariant (deckRepresentation n) (hVU i) k b = a i := by
    apply Subtype.ext
    apply Form.ext
    intro x hx
    apply (restrictEquivariant_apply (deckRepresentation n) (hVU i) b hx).trans
    apply (restrictEquivariant_apply (deckRepresentation n) hUU
      (gluedForm (deckRepresentation n) V k a hc) (liftedDomain_mono (hVU i) hx)).trans
    exact gluedRaw_apply (deckRepresentation n) V k a hc i hx
  refine ⟨b, ?_⟩
  apply intrinsicCurrent_ext_cover n k U (fun i => (V i : Set OrbitSpace))
    (fun i => (V i).isOpen) hVU hcover T
  intro i
  exact (ha i).trans ((congrArg (intrinsicSmoothCurrent n k (V i : Set OrbitSpace) (V i).isOpen)
    (hb i).symm).trans (intrinsicSmoothCurrent_restriction n k hU (V i).isOpen (hVU i) b).symm)

end TernaryPoly.PolynomialFormWeakSmooth
