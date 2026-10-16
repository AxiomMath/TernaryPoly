module

public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Stability.PermutationInvariance
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Stability.CosetDecomposition

@[expose] public section


/-!
# Hecke correspondences preserve the boundary summands

The single-coset decomposition `CosetDecomposition.cosetDecomposition_all` holds for every
representative of every Hecke correspondence. With it the Hecke translate has the
coset-permutation invariance. Consequently the actual Hecke operators preserve
`boundarySummand D side` and `associatePair D`. This is an
unconditional prerequisite for the spectral statements
`associate_projector_away_three_algebra`, `cuspidal_associate_projector` and
`cuspidal_finite_spectral_recovery`. It does not by itself prove any of them.

Original work (AxiomDeep, Claude Opus 5.5).
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.HeckeStability

/-- Every Hecke correspondence satisfies the single-coset decomposition. -/
theorem cosetDecomposition_all (t : HeckeCorrespondence) : CosetDecomposition t :=
  fun r _ k hk => CosetDecomposition.cosetDecomposition_all r k hk

theorem cosetPermutation_all (t : HeckeCorrespondence) : CosetPermutation t :=
  cosetPermutation_of_decomposition t (cosetDecomposition_all t)

/-- **Hecke stability of the boundary summands** (every double-coset correspondence). -/
theorem boundarySummand_hecke_stable {n : ℕ} {D : InducingData n} (t : HeckeCorrespondence)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke) (side : Side) :
    ∀ a ∈ boundarySummand D side, hecke side t a ∈ boundarySummand D side :=
  boundarySummand_hecke_stable_of_perm t (cosetPermutation_all t) hecke hhecke side

/-- **Hecke stability of the associate pair** (every double-coset correspondence). -/
theorem associatePair_hecke_stable {n : ℕ} {D : InducingData n} (t : HeckeCorrespondence)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke) :
    ∀ y ∈ associatePair D, pairHecke D hecke t y ∈ associatePair D :=
  associatePair_hecke_stable_of_perm t (cosetPermutation_all t) hecke hhecke

theorem boundarySummand_hecke_stable_of_awayThree {n : ℕ} {D : InducingData n}
    (t : HeckeCorrespondence) (_ht : AwayThree t)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke) (side : Side) :
    ∀ a ∈ boundarySummand D side, hecke side t a ∈ boundarySummand D side :=
  boundarySummand_hecke_stable t hecke hhecke side

theorem associatePair_hecke_stable_of_awayThree {n : ℕ} {D : InducingData n}
    (t : HeckeCorrespondence) (_ht : AwayThree t)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke) :
    ∀ y ∈ associatePair D, pairHecke D hecke t y ∈ associatePair D :=
  associatePair_hecke_stable t hecke hhecke

/-- The associate pair is stable under the whole away-three Hecke algebra. -/
theorem associatePair_stable_of_mem_awayThreeHeckeAlgebra {n : ℕ} {D : InducingData n}
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    {q : Module.End ℂ (BoundaryCoordinates n D.chi)} (hq : q ∈ awayThreeHeckeAlgebra D hecke) :
    ∀ y ∈ associatePair D, q y ∈ associatePair D := by
  let S : Subalgebra ℂ (Module.End ℂ (BoundaryCoordinates n D.chi)) :=
    { carrier := {q | ∀ y ∈ associatePair D, q y ∈ associatePair D}
      mul_mem' := fun ha hb y hy => ha _ (hb y hy)
      add_mem' := fun ha hb y hy => (associatePair D).add_mem (ha y hy) (hb y hy)
      algebraMap_mem' := fun c y hy => by
        rw [Module.algebraMap_end_apply]
        exact (associatePair D).smul_mem c hy }
  have hle : awayThreeHeckeAlgebra D hecke ≤ S := by
    apply Algebra.adjoin_le
    rintro A ⟨t, -, rfl⟩
    exact associatePair_hecke_stable t hecke hhecke
  exact hle hq

/-- **Exact remaining content of `cuspidal_associate_projector`.** Since the associate
pair is Hecke stable (proved above), the existence and uniqueness of the isotypical
projection is equivalent to the two genuinely spectral inputs: a Hecke-invariant
complement, and the vanishing of Hecke-equivariant maps killing the pair with range
in the pair. -/
theorem existsUnique_isotypicalProjection_iff {n : ℕ} (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke) :
    (∃ p : Module.End ℂ (BoundaryCoordinates n D.chi),
      IsIsotypicalProjection D hecke p ∧
      ∀ p', IsIsotypicalProjection D hecke p' → p' = p) ↔
    (∃ S' : Submodule ℂ (BoundaryCoordinates n D.chi),
      IsCompl (associatePair D) S' ∧ ∀ t, ∀ x ∈ S', pairHecke D hecke t x ∈ S') ∧
    (∀ q : Module.End ℂ (BoundaryCoordinates n D.chi),
      LinearMap.range q ≤ associatePair D →
      (∀ x ∈ associatePair D, q x = 0) →
      (∀ t, q.comp (pairHecke D hecke t) = (pairHecke D hecke t).comp q) → q = 0) := by
  constructor
  · intro h
    exact ((HeckeTranslate.TargetReduction.existsUnique_iff_split hecke hhecke).mp h).2
  · intro h
    exact (HeckeTranslate.TargetReduction.existsUnique_iff_split hecke hhecke).mpr
      ⟨fun t => associatePair_hecke_stable t hecke hhecke, h⟩

end TernaryPeriodPolynomials.HeckeStability
