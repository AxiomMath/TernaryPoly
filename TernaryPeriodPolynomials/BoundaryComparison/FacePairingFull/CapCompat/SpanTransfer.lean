module

public import TernaryPeriodPolynomials.Topology.TopHomology.FundamentalTie

@[expose] public section


/-!
# Transport of a spanning cycle along a homotopy equivalence

If `ω` spans the degree-four cycles of the coinvariants of `P` modulo boundaries and `e : P ≃ Q` is a chain homotopy
equivalence of complexes of representations, then `e.hom ω` spans the degree-four cycles of the coinvariants of `Q`
modulo boundaries.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat

open TernaryPeriodPolynomials.Argument.TopHomology

variable {Γ : Type} [Group Γ] {P Q : ChainComplex (Rep.{0} ℚ Γ) ℕ}

theorem span_transfer (e : HomotopyEquiv P Q) (ω : (P.X 4).ρ.Coinvariants)
    (hcyc : ∀ z : (P.X 4).ρ.Coinvariants, coinvD P 4 3 z = 0 →
      ∃ c : ℚ, z - c • ω ∈ LinearMap.range (coinvD P 5 4))
    (z' : (Q.X 4).ρ.Coinvariants) (hz' : coinvD Q 4 3 z' = 0) :
    ∃ c : ℚ, z' - c • coinvF e.hom 4 ω ∈ LinearMap.range (coinvD Q 5 4) := by
  have hz : coinvD P 4 3 (coinvF e.inv 4 z') = 0 := by
    have := LinearMap.congr_fun (coinvF_coinvD e.inv 4 3) z'
    simp only [LinearMap.comp_apply] at this
    rw [← this, hz', map_zero]
  obtain ⟨ν, hν⟩ := hcyc _ hz
  refine ⟨ν, ?_⟩
  have h1 : coinvF e.hom 4 (coinvF e.inv 4 z' - ν • ω) ∈ LinearMap.range (coinvD Q 5 4) := by
    obtain ⟨w, hw⟩ := hν
    refine ⟨coinvF e.hom 5 w, ?_⟩
    have := LinearMap.congr_fun (coinvF_coinvD e.hom 5 4) w
    simp only [LinearMap.comp_apply] at this
    rw [← this, hw]
  have h2 := homotopy_cycle e.homotopyInvHomId z' hz'
  rw [coinvF_comp, coinvF_id] at h2
  have h2' : coinvF e.hom 4 (coinvF e.inv 4 z') - z' ∈ LinearMap.range (coinvD Q 5 4) := h2
  rw [map_sub, map_smul] at h1
  have h3 := Submodule.add_mem _ h1 (Submodule.neg_mem _ h2')
  have h4 : coinvF e.hom 4 (coinvF e.inv 4 z') - ν • coinvF e.hom 4 ω +
      -(coinvF e.hom 4 (coinvF e.inv 4 z') - z') = z' - ν • coinvF e.hom 4 ω := by abel
  rw [h4] at h3
  exact h3

end TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
