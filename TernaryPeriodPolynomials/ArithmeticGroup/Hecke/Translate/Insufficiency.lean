/-
  Evidence that `cuspidal_associate_projector` is not
  derivable from the hypotheses of `IsIsotypicalProjection` alone.

  The file contains two results:

  1. `isotypical_difference` / `isotypical_add_intertwiner` show that, relative
     to any one solution `p`, the set of all solutions of
     `IsIsotypicalProjection D T ·` is an affine torsor over the space

        Q(D,T) = { q : End V | range q ≤ associatePair D,
                              q = 0 on associatePair D,
                              q · (pairHecke D T t) = (pairHecke D T t) · q  ∀ t }.

     Consequently uniqueness of the isotypical projection is *equivalent* to
     `Q(D,T) = 0`.  It is exactly the "no intertwiner between the complement and

     the associate pair" (multiplicity-one) input.

  2. `abstract_shape_not_unique` exhibits a concrete module (ℂ × ℂ) with a
     proper nonzero submodule `S` and the identity among the operators for
     which two distinct projections onto `S` fix `S` and commute with every
     operator.  Hence the *logical shape* of `IsIsotypicalProjection` does not
     by itself force uniqueness.

  Together these show the theorem cannot be closed from its stated
  hypotheses, and that the missing hypothesis is precisely `Q(D,T)=0`.
-/
module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs

@[expose] public section



open GeneralEisenstein
open Homogeneous Adelic

namespace TernaryPeriodPolynomials.HeckeTranslate

section Generic

variable {V ι : Type*} [AddCommGroup V] [Module ℂ V]

/-- `p` is a projection onto the subspace `A` (range `A`, identity on `A`) that commutes with
every operator `H t` of a family of endomorphisms. -/
def IsCommutingProjection (A : Submodule ℂ V) (H : ι → Module.End ℂ V)
    (p : Module.End ℂ V) : Prop :=
  LinearMap.range p = A ∧ (∀ x ∈ A, p x = x) ∧ ∀ t, p.comp (H t) = (H t).comp p

variable {A : Submodule ℂ V} {H : ι → Module.End ℂ V}

theorem IsCommutingProjection.mem_of_mem_range {p : Module.End ℂ V}
    (hp : IsCommutingProjection A H p) (x : V) : p x ∈ A :=
  hp.1 ▸ LinearMap.mem_range_self p x

theorem IsCommutingProjection.apply_apply {p : Module.End ℂ V}
    (hp : IsCommutingProjection A H p) (x : V) : p (p x) = p x :=
  hp.2.1 (p x) (hp.mem_of_mem_range x)

/-- The difference of two commuting projections onto `A` is a square-zero
intertwiner that factors through `A` and kills it. -/
theorem IsCommutingProjection.sub_properties {p p' : Module.End ℂ V}
    (hp : IsCommutingProjection A H p) (hp' : IsCommutingProjection A H p') :
    LinearMap.range (p - p') ≤ A ∧
    (∀ x ∈ A, (p - p') x = 0) ∧
    (p - p').comp (p - p') = 0 ∧
    (∀ t, (p - p').comp (H t) = (H t).comp (p - p')) := by
  have hrange : LinearMap.range (p - p') ≤ A := by
    rintro y ⟨x, rfl⟩
    exact sub_mem (hp.mem_of_mem_range x) (hp'.mem_of_mem_range x)
  have hkill : ∀ x ∈ A, (p - p') x = 0 := by
    intro x hx
    rw [LinearMap.sub_apply, hp.2.1 x hx, hp'.2.1 x hx, sub_self]
  refine ⟨hrange, hkill, ?_, ?_⟩
  · apply LinearMap.ext
    intro x
    exact hkill ((p - p') x) (hrange (LinearMap.mem_range_self (p - p') x))
  · intro t
    rw [LinearMap.sub_comp, LinearMap.comp_sub, hp.2.2 t, hp'.2.2 t]

/-- Adding an intertwiner with range in `A` that kills `A` to a commuting projection onto `A`
gives a commuting projection onto `A`. -/
theorem IsCommutingProjection.add_intertwiner {p : Module.End ℂ V}
    (hp : IsCommutingProjection A H p) {q : Module.End ℂ V}
    (hqr : LinearMap.range q ≤ A) (hqk : ∀ x ∈ A, q x = 0)
    (hqc : ∀ t, q.comp (H t) = (H t).comp q) :
    IsCommutingProjection A H (p + q) := by
  refine ⟨?_, ?_, ?_⟩
  · apply le_antisymm
    · rintro y ⟨x, rfl⟩
      rw [LinearMap.add_apply]
      exact add_mem (hp.mem_of_mem_range x) (hqr (LinearMap.mem_range_self q x))
    · intro s hs
      exact ⟨s, by rw [LinearMap.add_apply, hp.2.1 s hs, hqk s hs, add_zero]⟩
  · intro x hx
    rw [LinearMap.add_apply, hp.2.1 x hx, hqk x hx, add_zero]
  · intro t
    rw [LinearMap.add_comp, LinearMap.comp_add, hp.2.2 t, hqc t]

/-- Uniqueness of the commuting projection fails as soon as there is a nonzero intertwiner
with range in `A` killing `A`. -/
theorem IsCommutingProjection.not_unique_of_nonzero_intertwiner {p : Module.End ℂ V}
    (hp : IsCommutingProjection A H p) {q : Module.End ℂ V}
    (hqr : LinearMap.range q ≤ A) (hqk : ∀ x ∈ A, q x = 0)
    (hqc : ∀ t, q.comp (H t) = (H t).comp q) (hq0 : q ≠ 0) :
    ¬ (∀ p', IsCommutingProjection A H p' → p' = p) := by
  intro huniq
  have hp' : IsCommutingProjection A H (p + q) := hp.add_intertwiner hqr hqk hqc
  have hpq : p + q = p := huniq (p + q) hp'
  have h2 : p + q = p + 0 := by simpa using hpq
  exact hq0 (add_left_cancel h2)

/-- Uniqueness of the commuting projection onto `A` is equivalent to the vanishing of the
intertwiners with range in `A` that kill `A`, once a commuting projection exists. -/
theorem isCommutingProjection_unique_iff (hex : ∃ p : Module.End ℂ V, IsCommutingProjection A H p) :
    (∃ p : Module.End ℂ V, IsCommutingProjection A H p ∧
        ∀ p', IsCommutingProjection A H p' → p' = p) ↔
      (∀ q : Module.End ℂ V, LinearMap.range q ≤ A → (∀ x ∈ A, q x = 0) →
        (∀ t, q.comp (H t) = (H t).comp q) → q = 0) := by
  constructor
  · rintro ⟨p, hp, huniq⟩ q hqr hqk hqc
    have hpq : p + q = p := huniq (p + q) (hp.add_intertwiner hqr hqk hqc)
    have h2 : p + q = p + 0 := by simpa using hpq
    exact add_left_cancel h2
  · intro hQ
    obtain ⟨p, hp⟩ := hex
    refine ⟨p, hp, ?_⟩
    intro p' hp'
    have hd := hp'.sub_properties hp
    have hzero : p' - p = 0 := hQ (p' - p) hd.1 hd.2.1 hd.2.2.2
    exact sub_eq_zero.mp hzero

/-- A commuting projection onto `A` is idempotent. -/
theorem IsCommutingProjection.comp_self {p : Module.End ℂ V}
    (hp : IsCommutingProjection A H p) : p.comp p = p :=
  LinearMap.ext hp.apply_apply

/-- The kernel of a commuting projection onto `A` is a complement of `A`. -/
theorem IsCommutingProjection.isCompl_ker {p : Module.End ℂ V}
    (hp : IsCommutingProjection A H p) : IsCompl A (LinearMap.ker p) := by
  refine ⟨?_, ?_⟩
  · rw [disjoint_iff_inf_le]
    intro x hx
    rw [Submodule.mem_bot]
    rw [← hp.2.1 x hx.1, LinearMap.mem_ker.mp hx.2]
  · rw [codisjoint_iff_le_sup]
    intro x _
    have hker : x - p x ∈ LinearMap.ker p := by
      rw [LinearMap.mem_ker, map_sub, hp.apply_apply x, sub_self]
    have : p x + (x - p x) = x := by abel
    rw [← this]
    exact Submodule.add_mem_sup (hp.mem_of_mem_range x) hker

end Generic

variable {n : ℕ} {D : InducingData n}
variable {T : (side : Side) → HeckeCorrespondence → Module.End ℂ (StratumH2 n D.chi side)}

/-- The difference of two Hecke-isotypical projections is a square-zero
intertwiner that factors through the associate pair and kills it. -/
theorem isotypical_difference
    {p p' : Module.End ℂ (BoundaryCoordinates n D.chi)}
    (hp : IsIsotypicalProjection D T p) (hp' : IsIsotypicalProjection D T p') :
    LinearMap.range (p - p') ≤ associatePair D ∧
    (∀ x ∈ associatePair D, (p - p') x = 0) ∧
    (p - p').comp (p - p') = 0 ∧
    (∀ t, (p - p').comp (pairHecke D T t) = (pairHecke D T t).comp (p - p')) :=
  IsCommutingProjection.sub_properties (A := associatePair D) (H := pairHecke D T) hp hp'

/-- Adding any intertwiner in `Q(D,T)` to a solution again gives a solution. -/
theorem isotypical_add_intertwiner
    {p : Module.End ℂ (BoundaryCoordinates n D.chi)}
    (hp : IsIsotypicalProjection D T p)
    {q : Module.End ℂ (BoundaryCoordinates n D.chi)}
    (hqr : LinearMap.range q ≤ associatePair D)
    (hqk : ∀ x ∈ associatePair D, q x = 0)
    (hqc : ∀ t, q.comp (pairHecke D T t) = (pairHecke D T t).comp q) :
    IsIsotypicalProjection D T (p + q) :=
  IsCommutingProjection.add_intertwiner (A := associatePair D) (H := pairHecke D T) hp hqr hqk hqc

/-- If a solution exists and there is a nonzero intertwiner through the
associate pair, then the uniqueness conclusion of `cuspidal_associate_projector` fails. -/
theorem uniqueness_fails_of_nonzero_intertwiner
    {p : Module.End ℂ (BoundaryCoordinates n D.chi)}
    (hp : IsIsotypicalProjection D T p)
    {q : Module.End ℂ (BoundaryCoordinates n D.chi)}
    (hqr : LinearMap.range q ≤ associatePair D)
    (hqk : ∀ x ∈ associatePair D, q x = 0)
    (hqc : ∀ t, q.comp (pairHecke D T t) = (pairHecke D T t).comp q)
    (hq0 : q ≠ 0) :
    ¬ (∀ p', IsIsotypicalProjection D T p' → p' = p) :=
  IsCommutingProjection.not_unique_of_nonzero_intertwiner (A := associatePair D)
    (H := pairHecke D T) hp hqr hqk hqc hq0

/-- The uniqueness conclusion is *equivalent* to the vanishing of
the Hecke-equivariant intertwiners through the associate pair.
-/
theorem isotypical_unique_iff
    (hex : ∃ p : Module.End ℂ (BoundaryCoordinates n D.chi), IsIsotypicalProjection D T p) :
    (∃ p : Module.End ℂ (BoundaryCoordinates n D.chi),
        IsIsotypicalProjection D T p ∧
        ∀ p', IsIsotypicalProjection D T p' → p' = p) ↔
      (∀ q : Module.End ℂ (BoundaryCoordinates n D.chi),
        LinearMap.range q ≤ associatePair D →
        (∀ x ∈ associatePair D, q x = 0) →
        (∀ t, q.comp (pairHecke D T t) = (pairHecke D T t).comp q) → q = 0) :=
  isCommutingProjection_unique_iff (A := associatePair D) (H := pairHecke D T) hex

/-- The logical shape of `IsIsotypicalProjection` (range, identity on the
range, commutation with a family containing the identity) does not force
uniqueness. -/
theorem abstract_shape_not_unique :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (S : Submodule ℂ V)
      (A : V →ₗ[ℂ] V),
      A = 1 ∧
      ∃ p p' : V →ₗ[ℂ] V, p ≠ p' ∧
        LinearMap.range p = S ∧ (∀ x ∈ S, p x = x) ∧ p.comp A = A.comp p ∧
        LinearMap.range p' = S ∧ (∀ x ∈ S, p' x = x) ∧ p'.comp A = A.comp p' := by
  classical
  refine ⟨ℂ × ℂ, inferInstance, inferInstance,
    LinearMap.ker (LinearMap.snd ℂ ℂ ℂ), (LinearMap.id : ℂ × ℂ →ₗ[ℂ] ℂ × ℂ), rfl,
    (LinearMap.fst ℂ ℂ ℂ).prod 0,
    ((LinearMap.fst ℂ ℂ ℂ) + (LinearMap.snd ℂ ℂ ℂ)).prod 0,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- p ≠ p'
    intro h
    have h0 : (LinearMap.fst ℂ ℂ ℂ).prod (0 : ℂ × ℂ →ₗ[ℂ] ℂ) (0, 1) =
        (((LinearMap.fst ℂ ℂ ℂ) + (LinearMap.snd ℂ ℂ ℂ)).prod 0) (0, 1) := by rw [h]
    simp at h0
  · -- range p = S
    apply le_antisymm
    · rintro y ⟨x, rfl⟩
      simp [LinearMap.prod_apply]
    · intro y hy
      refine ⟨y, ?_⟩
      have hy2 : y.2 = 0 := LinearMap.mem_ker.mp hy
      ext <;> simp [LinearMap.prod_apply, hy2]
  · -- p fixes S
    intro x hx
    have hx2 : x.2 = 0 := LinearMap.mem_ker.mp hx
    ext <;> simp [LinearMap.prod_apply, hx2]
  · -- p commutes with A = id
    rw [LinearMap.comp_id, LinearMap.id_comp]
  · -- range p' = S
    apply le_antisymm
    · rintro y ⟨x, rfl⟩
      simp [LinearMap.prod_apply]
    · intro y hy
      refine ⟨(y.1, y.2), ?_⟩
      have hy2 : y.2 = 0 := LinearMap.mem_ker.mp hy
      ext <;> simp [LinearMap.prod_apply, hy2]
  · -- p' fixes S
    intro x hx
    have hx2 : x.2 = 0 := LinearMap.mem_ker.mp hx
    ext <;> simp [LinearMap.prod_apply, hx2]
  · -- p' commutes with A = id
    rw [LinearMap.comp_id, LinearMap.id_comp]

/-- An isotypical projection is idempotent: `p ∘ p = p`. -/
theorem isotypicalProjection_idempotent
    {p : Module.End ℂ (BoundaryCoordinates n D.chi)}
    (hp : IsIsotypicalProjection D T p) : p.comp p = p :=
  IsCommutingProjection.comp_self (A := associatePair D) (H := pairHecke D T) hp

/-- An isotypical projection has `associatePair D` as its range and
`LinearMap.ker p` as a complement. -/
theorem isotypicalProjection_ker_isCompl
    {p : Module.End ℂ (BoundaryCoordinates n D.chi)}
    (hp : IsIsotypicalProjection D T p) :
    IsCompl (associatePair D) (LinearMap.ker p) :=
  IsCommutingProjection.isCompl_ker (A := associatePair D) (H := pairHecke D T) hp

end TernaryPeriodPolynomials.HeckeTranslate
