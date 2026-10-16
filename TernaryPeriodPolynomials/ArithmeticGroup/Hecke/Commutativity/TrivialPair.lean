module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs

@[expose] public section


/-!
# Isotypical projections for a trivial associate pair

If the associate pair is `⊥`, the only isotypical projection is `0`. If it is `⊤`, the only one is
the identity. In both cases the projection exists, is unique, and lies in the away-three Hecke
algebra. These are the degenerate cases of `cuspidal_associate_projector` and
`associate_projector_away_three_algebra`, proved unconditionally.

Original work (AxiomDeep, Claude Opus 5.5).
-/

open GeneralEisenstein

namespace TernaryPeriodPolynomials.HeckeCommutativity

variable {n : ℕ} (D : InducingData n)
  (T : (side : Side) → HeckeCorrespondence → Module.End ℂ (StratumH2 n D.chi side))

theorem isotypical_eq_zero_of_bot (h : associatePair D = ⊥) {p} (hp : IsIsotypicalProjection D T p) :
    p = 0 := by
  apply LinearMap.ext
  intro x
  have hx : p x ∈ LinearMap.range p := LinearMap.mem_range_self p x
  rw [hp.1, h, Submodule.mem_bot] at hx
  simpa using hx

theorem isotypical_eq_one_of_top (h : associatePair D = ⊤) {p} (hp : IsIsotypicalProjection D T p) :
    p = 1 := by
  apply LinearMap.ext
  intro x
  exact hp.2.1 x (h ▸ Submodule.mem_top)

theorem zero_isotypical_of_bot (h : associatePair D = ⊥) : IsIsotypicalProjection D T 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [h, LinearMap.range_zero]
  · intro x hx
    rw [h, Submodule.mem_bot] at hx
    simp [hx]
  · intro t
    simp

theorem one_isotypical_of_top (h : associatePair D = ⊤) : IsIsotypicalProjection D T 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [h]
    exact LinearMap.range_id
  · intro x _
    rfl
  · intro t
    rfl

/-- **Degenerate case of `cuspidal_associate_projector`.** -/
theorem existsUnique_isotypical_of_trivial (h : associatePair D = ⊥ ∨ associatePair D = ⊤) :
    ∃ p, IsIsotypicalProjection D T p ∧ ∀ p', IsIsotypicalProjection D T p' → p' = p := by
  rcases h with h | h
  · exact ⟨0, zero_isotypical_of_bot D T h, fun p' hp' => isotypical_eq_zero_of_bot D T h hp'⟩
  · exact ⟨1, one_isotypical_of_top D T h, fun p' hp' => isotypical_eq_one_of_top D T h hp'⟩

/-- **Degenerate case of `associate_projector_away_three_algebra`.** -/
theorem isotypical_mem_awayThree_of_trivial (hecke : BoundaryHecke n D.chi)
    (h : associatePair D = ⊥ ∨ associatePair D = ⊤) {p}
    (hp : IsIsotypicalProjection D hecke p) : p ∈ awayThreeHeckeAlgebra D hecke := by
  rcases h with h | h
  · rw [isotypical_eq_zero_of_bot D hecke h hp]
    exact Subalgebra.zero_mem _
  · rw [isotypical_eq_one_of_top D hecke h hp]
    exact Subalgebra.one_mem _

end TernaryPeriodPolynomials.HeckeCommutativity
