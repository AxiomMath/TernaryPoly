module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.FrameFor

@[expose] public section


/-!
# Lemma 3.3, G3: every cellular chain lies in the span of the elementary chains of a finite set of cells

`cellSpan W 𝒞` is the span of the elementary coinvariant chains `[w ⊗ C]` of top cells `C ∈ 𝒞`;
`exists_cellSpan`: every element of `(cellCoinv W).X 3` lies in `cellSpan W 𝒞` for some finite `𝒞`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Classical Pointwise

namespace TernaryPeriodPolynomials.Argument.Lemma33.Locality

open CategoryTheory TernaryPoly TernaryPoly.IntegralGL3Congruence
  TernaryPeriodPolynomials.Argument.Lemma33.Retract

/-- The span of the elementary cellular chains on a finite set of top cells. -/
def cellSpan (W : Rep.{0} ℚ principalSix) (𝒞 : Finset (Graded 3)) : Submodule ℚ ((cellCoinv W).X 3) :=
  Submodule.span ℚ {x | ∃ C ∈ 𝒞, ∃ w : W,
    x = Rep.coinvariantsTensorMk W (cellRep 3) w (MonoidAlgebra.single C 1)}

theorem cellSpan_mono (W : Rep.{0} ℚ principalSix) {𝒞 𝒞' : Finset (Graded 3)} (h : 𝒞 ⊆ 𝒞') :
    cellSpan W 𝒞 ≤ cellSpan W 𝒞' :=
  Submodule.span_mono fun _ ⟨C, hC, w, hx⟩ => ⟨C, h hC, w, hx⟩

theorem exists_cellSpan_pure (W : Rep.{0} ℚ principalSix) (w : W) (x : cellRep 3) :
    ∃ 𝒞 : Finset (Graded 3), Rep.coinvariantsTensorMk W (cellRep 3) w x ∈ cellSpan W 𝒞 := by
  let L : (Graded 3 →₀ ℚ) →ₗ[ℚ] (cellCoinv W).X 3 :=
    (Rep.coinvariantsTensorMk W (cellRep 3) w) ∘ₗ (MonoidAlgebra.coeffLinearEquiv ℚ).symm.toLinearMap
  suffices H : ∀ x' : Graded 3 →₀ ℚ, ∃ 𝒞 : Finset (Graded 3), L x' ∈ cellSpan W 𝒞 by
    obtain ⟨𝒞, h𝒞⟩ := H ((MonoidAlgebra.coeffLinearEquiv ℚ) x)
    refine ⟨𝒞, ?_⟩
    have : L ((MonoidAlgebra.coeffLinearEquiv ℚ) x) = Rep.coinvariantsTensorMk W (cellRep 3) w x := by
      change Rep.coinvariantsTensorMk W (cellRep 3) w ((MonoidAlgebra.coeffLinearEquiv ℚ).symm
        ((MonoidAlgebra.coeffLinearEquiv ℚ) x)) = _
      rw [LinearEquiv.symm_apply_apply]
    rw [this] at h𝒞
    exact h𝒞
  intro x'
  induction x' using Finsupp.induction_linear with
  | zero => exact ⟨∅, by rw [map_zero]; exact Submodule.zero_mem _⟩
  | add x y hx hy =>
    obtain ⟨𝒞₁, h₁⟩ := hx
    obtain ⟨𝒞₂, h₂⟩ := hy
    refine ⟨𝒞₁ ∪ 𝒞₂, ?_⟩
    rw [map_add]
    exact Submodule.add_mem _ (cellSpan_mono W Finset.subset_union_left h₁)
      (cellSpan_mono W Finset.subset_union_right h₂)
  | single C a =>
    refine ⟨{C}, Submodule.subset_span ⟨C, Finset.mem_singleton_self C, a • w, ?_⟩⟩
    change Rep.coinvariantsTensorMk W (cellRep 3) w ((MonoidAlgebra.coeffLinearEquiv ℚ).symm
      (Finsupp.single C a)) = _
    have h1 : ((MonoidAlgebra.coeffLinearEquiv ℚ).symm (Finsupp.single C a) : cellRep 3) =
        a • (MonoidAlgebra.single C (1 : ℚ) : cellRep 3) := by
      rw [← Finsupp.smul_single_one C a, map_smul]
      rfl
    rw [h1, map_smul, LinearMap.map_smul₂]

theorem exists_cellSpan (W : Rep.{0} ℚ principalSix) (z : (cellCoinv W).X 3) :
    ∃ 𝒞 : Finset (Graded 3), z ∈ cellSpan W 𝒞 := by
  have hsurj : Function.Surjective
      (TensorProduct.lift (Rep.coinvariantsTensorMk W (cellRep 3)) :
        TensorProduct ℚ W (cellRep 3) →ₗ[ℚ] ((Rep.coinvariantsTensor ℚ principalSix).obj W).obj
          (cellRep 3)) := by
    intro z
    obtain ⟨t, ht⟩ := Representation.Coinvariants.mk_surjective (W.ρ.tprod (cellRep 3).ρ) z
    refine ⟨t, ?_⟩
    rw [← ht]
    have hlin : (TensorProduct.lift (Rep.coinvariantsTensorMk W (cellRep 3)) :
        TensorProduct ℚ W (cellRep 3) →ₗ[ℚ] ((Rep.coinvariantsTensor ℚ principalSix).obj W).obj
          (cellRep 3)) = Representation.Coinvariants.mk (W.ρ.tprod (cellRep 3).ρ) :=
      TensorProduct.ext' (fun a b => rfl)
    exact LinearMap.congr_fun hlin t
  obtain ⟨t, rfl⟩ := hsurj z
  induction t using TensorProduct.inductionOn with
  | tmul w x => exact exists_cellSpan_pure W w x
  | add t t' ht ht' =>
    obtain ⟨𝒞₁, h₁⟩ := ht
    obtain ⟨𝒞₂, h₂⟩ := ht'
    refine ⟨𝒞₁ ∪ 𝒞₂, ?_⟩
    rw [map_add]
    exact Submodule.add_mem _ (cellSpan_mono W Finset.subset_union_left h₁)
      (cellSpan_mono W Finset.subset_union_right h₂)

end TernaryPeriodPolynomials.Argument.Lemma33.Locality
