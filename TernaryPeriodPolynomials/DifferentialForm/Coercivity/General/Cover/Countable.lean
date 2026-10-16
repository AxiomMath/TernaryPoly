module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Basic

@[expose] public section


/-!
# General coercivity: admissible groups are countable

Finite compact transporters force countability: `Γ` is the countable union, over a compact exhaustion
`K₀ ⊆ K₁ ⊆ …` of `Space`, of the finite sets of elements carrying a fixed base point into `Kₙ`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceCovering

variable {Γ : Subgroup RealGL}

/-- An admissible group is countable. -/
theorem Admissible.countable (h : Admissible Γ) : Countable Γ := by
  obtain ⟨S₀, hS₀⟩ := traceOnePositive_nonempty
  let S : Space := ⟨S₀, hS₀⟩
  have hcov : (Set.univ : Set Γ) ⊆
      ⋃ n : ℕ, {g : Γ | ((g • ·) '' ({S} : Set Space) ∩ compactCovering Space n).Nonempty} := by
    intro g _
    have hg : g • S ∈ ⋃ n, compactCovering Space n := by
      rw [iUnion_compactCovering]
      exact Set.mem_univ _
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hg
    exact Set.mem_iUnion.mpr ⟨n, ⟨g • S, ⟨S, rfl, rfl⟩, hn⟩⟩
  have hc : (Set.univ : Set Γ).Countable :=
    (Set.countable_iUnion fun n =>
      (h.transporters {S} (compactCovering Space n) isCompact_singleton
        (isCompact_compactCovering Space n)).countable).mono hcov
  exact Set.countable_univ_iff.mp hc

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
