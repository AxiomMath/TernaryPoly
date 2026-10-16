module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs

@[expose] public section


/-!
# Uniqueness of an isotypical projection lying in the away-three Hecke algebra

If one isotypical projection lies in `awayThreeHeckeAlgebra`, every isotypical
projection equals it: a second one commutes with all Hecke generators, hence
with the first, and two commuting idempotents with the same range on which both
are the identity coincide.  This is the elementary linear-algebra step relating
`associate_projector_away_three_algebra` to the uniqueness clause of
`cuspidal_associate_projector`; it does not supply existence.

Original work (AxiomDeep, Claude Opus 5.5).
-/

open GeneralEisenstein

namespace TernaryPeriodPolynomials.HeckeStability

theorem commute_of_mem_awayThreeHeckeAlgebra {n : ℕ} {D : InducingData n}
    {hecke : BoundaryHecke n D.chi} {p' : Module.End ℂ (BoundaryCoordinates n D.chi)}
    (hp' : IsIsotypicalProjection D hecke p')
    {q : Module.End ℂ (BoundaryCoordinates n D.chi)} (hq : q ∈ awayThreeHeckeAlgebra D hecke) :
    q * p' = p' * q := by
  have hle : awayThreeHeckeAlgebra D hecke ≤ Subalgebra.centralizer ℂ {p'} := by
    apply Algebra.adjoin_le
    rintro A ⟨t, -, rfl⟩
    rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    intro b hb
    rw [Set.mem_singleton_iff] at hb
    subst hb
    exact hp'.2.2 t
  have hmem := hle hq
  rw [Subalgebra.mem_centralizer_iff] at hmem
  exact (hmem p' (Set.mem_singleton p')).symm

theorem eq_of_commute_of_same_range {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A : Submodule ℂ V) {p p' : Module.End ℂ V}
    (hp : LinearMap.range p = A) (hp1 : ∀ x ∈ A, p x = x)
    (hp' : LinearMap.range p' = A) (hp'1 : ∀ x ∈ A, p' x = x)
    (hcomm : p * p' = p' * p) : p' = p := by
  apply LinearMap.ext
  intro x
  have h1 : p (p' x) = p' x := hp1 _ (hp' ▸ LinearMap.mem_range_self p' x)
  have h2 : p' (p x) = p x := hp'1 _ (hp ▸ LinearMap.mem_range_self p x)
  have h3 : p (p' x) = p' (p x) := by
    rw [← Module.End.mul_apply, hcomm, Module.End.mul_apply]
  rw [← h1, h3, h2]

theorem isotypicalProjection_unique_of_mem {n : ℕ} {D : InducingData n}
    {hecke : BoundaryHecke n D.chi} {p p' : Module.End ℂ (BoundaryCoordinates n D.chi)}
    (hp : IsIsotypicalProjection D hecke p) (hpa : p ∈ awayThreeHeckeAlgebra D hecke)
    (hp' : IsIsotypicalProjection D hecke p') : p' = p :=
  eq_of_commute_of_same_range (associatePair D) hp.1 hp.2.1 hp'.1 hp'.2.1
    (commute_of_mem_awayThreeHeckeAlgebra hp' hpa)

/-- The away-three algebra statement gives the uniqueness clause of the cuspidal
projector statement (existence remains a separate obligation). -/
theorem isotypicalProjection_unique_of_awayThree
    (algebra : ∀ n : ℕ, 0 < n → ∀ D : InducingData n,
      ∀ hecke : BoundaryHecke n D.chi, ActualBoundaryHecke n D.chi hecke →
      ∀ p : Module.End ℂ (BoundaryCoordinates n D.chi), IsIsotypicalProjection D hecke p →
      p ∈ awayThreeHeckeAlgebra D hecke)
    {n : ℕ} (hn : 0 < n) (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke)
    {p p' : Module.End ℂ (BoundaryCoordinates n D.chi)}
    (hp : IsIsotypicalProjection D hecke p) (hp' : IsIsotypicalProjection D hecke p') :
    p' = p :=
  isotypicalProjection_unique_of_mem hp (algebra n hn D hecke hhecke p hp) hp'

end TernaryPeriodPolynomials.HeckeStability
