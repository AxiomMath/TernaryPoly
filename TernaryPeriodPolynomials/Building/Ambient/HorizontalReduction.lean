module

public import TernaryPeriodPolynomials.Building.Ambient.HorizontalElimination
public import TernaryPeriodPolynomials.Building.Ambient.HorizontalSubdivision

@[expose] public section


noncomputable section
namespace TernaryPoly.AmbientHorizontalReduction
open ModThreeGoodAction AugmentedFrameComplex PrimitiveLineHeight
open OrientedListChains OrientedChainProjection AmbientHeightFiltration
open AmbientHorizontalElimination AmbientHorizontalSubdivision

/-- Actual normalized differences discharge the local geometric input. -/
theorem pair_geometry (F : IntegralVector →ₗ[ℤ] ℤ) (N : ℕ) (hN : 0 < N) :
    PairGeometry F N := by
  intro U V hne hU hV hf
  exact horizontal_input F N hN U V hne hf hU hV

/-- Actual finite horizontal reduction of a bounded reduced two-cycle. -/
theorem eliminate_horizontal_actual (F : IntegralVector →ₗ[ℤ] ℤ) (N : ℕ) (hN : 0 < N)
    {c : Chain RationalLine} (hc : c ∈ reducedTriangles F N) (hd : boundary c = 0) :
    ∃ t r : Chain RationalLine, t ∈ chains (bounded F N) 4 ∧
      r ∈ reducedTriangles F N ∧ boundary r = 0 ∧ c = boundary t + r ∧
      ∀ k : ℕ, 2 ≤ k → badCountProjection (fun L => height F L < N) k r = 0 :=
  eliminate_horizontal F N (pair_geometry F N hN) hc hd

/-- Additive and horizontal surgeries together leave at most one high vertex per triangle. -/
theorem reduce_to_one_high (F : IntegralVector →ₗ[ℤ] ℤ) (N : ℕ) (hN : 0 < N)
    {c : Chain RationalLine} (hc : c ∈ chains (bounded F N) 3) (hd : boundary c = 0) :
    ∃ t r : Chain RationalLine, t ∈ chains (bounded F N) 4 ∧
      r ∈ reducedTriangles F N ∧ boundary r = 0 ∧ c = boundary t + r ∧
      ∀ k : ℕ, 2 ≤ k → badCountProjection (fun L => height F L < N) k r = 0 := by
  obtain ⟨t,d,ht,hdmem,he,hdb⟩ :=
    AmbientHighAdditiveElimination.eliminate_high_additive_preserves_boundary F N hN hc
  obtain ⟨t',r,ht',hr,hdr,he',hproj⟩ :=
    eliminate_horizontal_actual F N hN hdmem (hdb.trans hd)
  refine ⟨t+t',r,(chains (bounded F N) 4).add_mem ht ht',hr,hdr,?_,hproj⟩
  rw [he,he',map_add]
  abel

end TernaryPoly.AmbientHorizontalReduction
