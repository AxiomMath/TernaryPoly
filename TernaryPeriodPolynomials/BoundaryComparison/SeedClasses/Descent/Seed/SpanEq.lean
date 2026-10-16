module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.Level.Seed
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.ParabolicSeeds

@[expose] public section


/-!
# The spanning clause of Lemma C.3 as an equivalence

Paper: Lemma C.3
(`ar:lem:seed`), last sentence.

The seeds have parabolic edge (`seedKerSpan_le_comap`, from `ParabolicSeeds`), so under the
Eichler--Shimura hypothesis `ESSpan Λ n` the span of the seed classes is exactly the set of classes
with zero radical restriction and parabolic edge (`seedKerSpan_eq_comap`, `mem_seedSpan_iff`).

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups
open GeneralEisenstein Matrix MvPolynomial
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open CategoryTheory groupCohomology

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3S4c

variable {Λ : Subgroup SL(2, ℤ)} {n : ℕ}

/-- The seeds have parabolic edge (unconditional). -/
theorem seedKerSpan_le_comap :
    seedKerSpan Λ n ≤ Submodule.comap (levelEdge Λ n) (parabolicH1 Λ n) := by
  have hn : ((n : ℂ) + 1)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast Nat.succ_ne_zero n)
  rw [seedKerSpan, Submodule.span_le]
  rintro _ (⟨f, rfl⟩ | ⟨f, rfl⟩)
  · change levelEdge Λ n (seedKerClass f) ∈ parabolicH1 Λ n
    rw [seedKerClass, levelSeedEdge]
    exact Submodule.smul_mem _ _ ⟨holCocycle f, holCocycle_mem_parabolicCocycles f, rfl⟩
  · change levelEdge Λ n (seedConjKerClass f) ∈ parabolicH1 Λ n
    rw [seedConjKerClass, levelSeedConjEdge]
    exact Submodule.smul_mem _ _ ⟨antiholCocycle f, antiholCocycle_mem_parabolicCocycles f, rfl⟩

/-- **The mixed cuspidal group is spanned by the seeds, conditional on Eichler--Shimura**: under
`ESSpan Λ n`, the classes with zero radical restriction and parabolic edge are exactly the span of
the holomorphic and antiholomorphic seeds. -/
theorem seedKerSpan_eq_comap (hES : ESSpan Λ n) :
    seedKerSpan Λ n = Submodule.comap (levelEdge Λ n) (parabolicH1 Λ n) :=
  le_antisymm seedKerSpan_le_comap (fun x hx => seed_span_of_ESSpan Λ n hES x hx)


/-- `seedSpan` is the image of `seedKerSpan` in `H²`. -/
theorem seedSpan_le_map :
    seedSpan Λ n ≤ Submodule.map (LinearMap.ker (twoCohomologyRestriction (levelExt Λ).inl
      (levelRep Λ n))).subtype (seedKerSpan Λ n) := by
  rw [seedSpan, Submodule.span_le]
  rintro _ (⟨f, rfl⟩ | ⟨f, rfl⟩)
  · refine ⟨seedKerClass f, Submodule.subset_span (Or.inl ⟨f, rfl⟩), ?_⟩
    exact complexifyL_cuspSeedClass f |>.symm
  · refine ⟨seedConjKerClass f, Submodule.subset_span (Or.inr ⟨f, rfl⟩), ?_⟩
    exact complexifyL_cuspSeedConjClass f |>.symm

/-- **The spanning clause of Lemma C.3 as an equivalence, conditional on `ESSpan Λ n`.** A class of
`H²(ℤ² ⋊ Λ, E_n)` is in the span of the complexified de Rham classes of the seeds `ω_f`,
`\overline{ω_f}` if and only if it restricts to zero on the radical lattice and its
Hochschild--Serre edge is a parabolic class. -/
theorem mem_seedSpan_iff (hES : ESSpan Λ n) (y : H2 (levelRep Λ n)) :
    y ∈ seedSpan Λ n ↔ ∃ hy : twoCohomologyRestriction (levelExt Λ).inl (levelRep Λ n) y = 0,
      levelEdge Λ n ⟨y, hy⟩ ∈ parabolicH1 Λ n := by
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := seedSpan_le_map hy
    have hx' : x ∈ Submodule.comap (levelEdge Λ n) (parabolicH1 Λ n) := by
      rw [← seedKerSpan_eq_comap hES]
      exact hx
    exact ⟨x.2, hx'⟩
  · rintro ⟨hy, hpar⟩
    exact seed_span_conditional Λ n hES y hy hpar

end TernaryPeriodPolynomials.Argument.SeedC3S4c
