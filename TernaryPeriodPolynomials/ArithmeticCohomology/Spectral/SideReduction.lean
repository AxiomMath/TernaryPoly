module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Necessity
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Eigen.Satake.IsotypicalKernel
public import TernaryPeriodPolynomials.ArithmeticCohomology.GraphPieces.Reduction

@[expose] public section


/-!
# Separation of the associate pair, one stratum at a time

The pair Hecke operators act diagonally on `BoundaryCoordinates = H²_plane × H²_line`, so
`EigenSeparated (awayThreeHeckeAlgebra D hecke) (associatePair D)` follows from a statement on
each maximal stratum separately, and it suffices to test the *generating* correspondences.
`SideSeparated D hecke side` says: if `c` is the eigencharacter of a nonzero vector of the
associate pair, every class on that stratum that is a generalized `c(t)`-eigenvector of every
away-three correspondence `t` lies in the cuspidal constituent `boundarySummand D side`.

Separation is independent of the realization of the Hecke action, because every
`ActualBoundaryHecke` family is `canonicalStratumHecke`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein

namespace TernaryPeriodPolynomials.Spectral

open TernaryPeriodPolynomials.SpectralSeparation

variable {n : ℕ}

/-- Separation on one maximal stratum, tested on generators. -/
def SideSeparated (D : InducingData n) (hecke : BoundaryHecke n D.chi) (side : Side) : Prop :=
  ∀ c : HeckeCorrespondence → ℂ,
    (∃ a ∈ associatePair D, a ≠ 0 ∧ ∀ t, AwayThree t → pairHecke D hecke t a = c t • a) →
    ∀ w : StratumH2 n D.chi side,
      (∀ t, AwayThree t → ∃ k : ℕ, ((hecke side t - c t • 1) ^ k) w = 0) →
      w ∈ boundarySummand D side

section Generic

variable {P Q ι : Type*} [AddCommGroup P] [Module ℂ P] [AddCommGroup Q] [Module ℂ Q]

/-- Abstract form of the reduction to strata: for a family of product operators
`H₁ t × H₂ t`, separation on each factor, tested on generators, gives separation of the
product subspace for the algebra the generators span. -/
private theorem eigenSeparated_prod (good : ι → Prop) (H₁ : ι → Module.End ℂ P)
    (H₂ : ι → Module.End ℂ Q) (SP : Submodule ℂ P) (SQ : Submodule ℂ Q)
    (hsc : ∀ t, good t → ∃ c : ℂ, ∀ y ∈ SP.prod SQ, (H₁ t).prodMap (H₂ t) y = c • y)
    (hP : ∀ c : ι → ℂ,
      (∃ a ∈ SP.prod SQ, a ≠ 0 ∧ ∀ t, good t → (H₁ t).prodMap (H₂ t) a = c t • a) →
      ∀ w : P, (∀ t, good t → ∃ k : ℕ, ((H₁ t - c t • 1) ^ k) w = 0) → w ∈ SP)
    (hL : ∀ c : ι → ℂ,
      (∃ a ∈ SP.prod SQ, a ≠ 0 ∧ ∀ t, good t → (H₁ t).prodMap (H₂ t) a = c t • a) →
      ∀ w : Q, (∀ t, good t → ∃ k : ℕ, ((H₂ t - c t • 1) ^ k) w = 0) → w ∈ SQ) :
    EigenSeparated
      (Algebra.adjoin ℂ {A | ∃ t, good t ∧ A = (H₁ t).prodMap (H₂ t)}) (SP.prod SQ) := by
  intro a w ha ha0 hshare
  obtain ⟨c, hc⟩ : ∃ c : ι → ℂ,
      ∀ t, good t → ∀ y ∈ SP.prod SQ, (H₁ t).prodMap (H₂ t) y = c t • y := by
    classical
    refine ⟨fun t => if ht : good t then (hsc t ht).choose else 0, ?_⟩
    intro t ht y hy
    simp only [dite_eq_left ht]
    exact (hsc t ht).choose_spec y hy
  have hgen : ∀ t, good t → ∃ k : ℕ, (((H₁ t).prodMap (H₂ t) - c t • 1) ^ k) w = 0 := by
    intro t ht
    have hmem : (H₁ t).prodMap (H₂ t) ∈
        Algebra.adjoin ℂ {A | ∃ t, good t ∧ A = (H₁ t).prodMap (H₂ t)} :=
      Algebra.subset_adjoin ⟨t, ht, rfl⟩
    obtain ⟨μ, ⟨k, hk⟩, ⟨l, hl⟩⟩ := hshare _ hmem
    obtain rfl : μ = c t :=
      eq_of_genEigen_of_eigen _ a (c t) μ (hc t ht a ha) ha0 k hk
    exact ⟨l, hl⟩
  have hex : ∃ a ∈ SP.prod SQ, a ≠ 0 ∧ ∀ t, good t → (H₁ t).prodMap (H₂ t) a = c t • a :=
    ⟨a, ha, ha0, fun t ht => hc t ht a ha⟩
  have hside : ∀ t, good t →
      (∃ k : ℕ, ((H₁ t - c t • 1) ^ k) w.1 = 0) ∧ ∃ k : ℕ, ((H₂ t - c t • 1) ^ k) w.2 = 0 := by
    intro t ht
    obtain ⟨k, hk⟩ := hgen t ht
    have hk' := prodMap_sub_smul_pow_apply (H₁ t) (H₂ t) (c t) k w
    rw [hk] at hk'
    exact ⟨⟨k, (Prod.ext_iff.mp hk'.symm).1⟩, ⟨k, (Prod.ext_iff.mp hk'.symm).2⟩⟩
  exact ⟨hP c hex w.1 (fun t ht => (hside t ht).1), hL c hex w.2 (fun t ht => (hside t ht).2)⟩

end Generic

/-- **Reduction to strata.** Separation on both maximal strata gives separation of the associate
pair for the whole away-three algebra. -/
theorem eigenSeparated_of_sideSeparated (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (hP : SideSeparated D hecke .plane)
    (hL : SideSeparated D hecke .line) :
    EigenSeparated (awayThreeHeckeAlgebra D hecke) (associatePair D) :=
  eigenSeparated_prod (fun t => AwayThree t) (fun t => hecke .plane t) (fun t => hecke .line t)
    (boundarySummand D .plane) (boundarySummand D .line)
    (fun t ht => HeckeEigen.Satake.pair_scalar D hecke hhecke t ht) hP hL

/-- Separation does not depend on the realization of the Hecke action: every family satisfying
`ActualBoundaryHecke` is the canonical one. -/
theorem eigenSeparated_canonical_iff (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) :
    EigenSeparated (awayThreeHeckeAlgebra D hecke) (associatePair D) ↔
      EigenSeparated
        (awayThreeHeckeAlgebra D (GraphPieces.Reduction.canonicalStratumHecke n D.chi))
        (associatePair D) := by
  obtain rfl := GraphPieces.Reduction.stratumHecke_unique n D.chi hecke hhecke
  exact Iff.rfl

end TernaryPeriodPolynomials.Spectral
