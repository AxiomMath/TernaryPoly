module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.FiniteIndexDescent

@[expose] public section


/-!
# Tools for the cuspidal condition of an arbitrary family of cusp subgroups

* `mem_cuspidalFamily_iff_map`: finite-index descent along a homomorphism `φ : L' →* L` whose range
  has finite index (a class of `H¹(L, V)` is cuspidal iff its pullback to `L'` is cuspidal for the
  preimages `φ⁻¹(B i)` of the cusp subgroups); this is `mem_cuspidalFamily_iff_res` for a not
  necessarily injective or subgroup-valued `φ` (e.g. `SL₂(ℤ) → GL₂(ℤ)` presented through the
  subgroup `⊤`).
* `mem_cuspidalFamily_iso_iff`: the cuspidal condition is invariant under isomorphisms of
  `L`-modules.
* `map_mem_cuspidalFamily`: functoriality of the cuspidal condition along a homomorphism that maps
  cusp subgroups into cusp subgroups.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory
open scoped BigOperators MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3S4c

section CuspidalFamilyTools

variable {L : Type} [Group L] {ι : Type} (B : ι → Subgroup L)

/-- **Finite-index descent along a homomorphism.** For `φ : L' →* L` with range of finite index, a
class `x ∈ H¹(L, V)` vanishes on every `B i` iff its pullback to `L'` vanishes on every
`φ⁻¹(B i)`. -/
theorem mem_cuspidalFamily_iff_map {L' : Type} [Group L'] (φ : L' →* L) [φ.range.FiniteIndex]
    (V : Rep ℂ L) (x : groupCohomology.H1 V) :
    x ∈ cuspidalFamily B V ↔
      (groupCohomology.map φ (𝟙 (Rep.res φ V)) 1).hom x ∈
        cuspidalFamily (fun i => (B i).comap φ) (Rep.res φ V) := by
  induction x using groupCohomology.H1_induction_on with
  | h c =>
    rw [groupCohomology.H1π_comp_map_apply, mem_cuspidalFamily_π, mem_cuspidalFamily_π]
    refine forall_congr' fun i => ?_
    constructor
    · rintro ⟨u, hu⟩
      exact ⟨u, fun γ => hu ⟨φ (γ : L'), γ.2⟩⟩
    · rintro ⟨u, hu⟩
      have hfin : Finite (↥(B i) ⧸ φ.range.subgroupOf (B i)) := inferInstance
      obtain ⟨v, hv⟩ := coboundary_of_finiteIndex (H := ↥(B i)) (V := V)
        (V.ρ.comp (B i).subtype) (φ.range.subgroupOf (B i)) (fun h => c.1 (h : L))
        (fun x y => (groupCohomology.mem_cocycles₁_iff c.1).mp c.2 (x : L) (y : L)) u
        (fun k hk => by
          obtain ⟨γ, hγ⟩ := Subgroup.mem_subgroupOf.mp hk
          have := hu ⟨γ, by change φ γ ∈ B i; rw [hγ]; exact k.2⟩
          change c.1 (φ γ) = V.ρ (φ γ) u - u at this
          change c.1 (k : L) = V.ρ (k : L) u - u
          rw [← hγ]; exact this)
      exact ⟨v, fun γ => hv γ⟩

/-- Cuspidality transports along an isomorphism of `L`-modules. -/
theorem mem_cuspidalFamily_iso_iff {V W : Rep ℂ L} (e : V ≅ W) (x : groupCohomology.H1 V) :
    x ∈ cuspidalFamily B V ↔
      ModuleCat.Hom.hom ((groupCohomology.functor ℂ L 1).mapIso e).hom x ∈ cuspidalFamily B W := by
  induction x using groupCohomology.H1_induction_on with
  | h c =>
    have himg : ModuleCat.Hom.hom ((groupCohomology.functor ℂ L 1).mapIso e).hom
        (groupCohomology.H1π V c) = groupCohomology.H1π W
          (groupCohomology.mapCocycles₁ (MonoidHom.id L) e.hom c) :=
      groupCohomology.H1π_comp_map_apply (MonoidHom.id L) e.hom c
    refine (mem_cuspidalFamily_π B V c).trans (Iff.trans ?_
      (Iff.of_eq (congrArg (fun x : groupCohomology.H1 W => x ∈ cuspidalFamily B W) himg)).symm)
    refine Iff.trans ?_ (mem_cuspidalFamily_π B W
      (groupCohomology.mapCocycles₁ (MonoidHom.id L) e.hom c)).symm
    refine forall_congr' fun i => ?_
    constructor
    · rintro ⟨u, hu⟩
      refine ⟨e.hom.hom u, fun γ => ?_⟩
      have h1 := hu γ
      have h2 : ((groupCohomology.mapCocycles₁ (MonoidHom.id L) e.hom c).1 (γ : L)) =
          e.hom.hom (c.1 (γ : L)) := rfl
      rw [h2, h1, map_sub]
      congr 1
      exact Rep.hom_comm_apply e.hom (γ : L) u
    · rintro ⟨u, hu⟩
      refine ⟨e.inv.hom u, fun γ => ?_⟩
      have h1 := hu γ
      have h2 : ((groupCohomology.mapCocycles₁ (MonoidHom.id L) e.hom c).1 (γ : L)) =
          e.hom.hom (c.1 (γ : L)) := rfl
      rw [h2] at h1
      have h3 : ∀ v : V, e.inv.hom (e.hom.hom v) = v := fun v => by simp
      have h4 : c.1 (γ : L) = e.inv.hom (e.hom.hom (c.1 (γ : L))) := (h3 _).symm
      rw [h4, h1, map_sub]
      congr 1
      exact Rep.hom_comm_apply e.inv (γ : L) u

/-- Functoriality of the cuspidal condition along a homomorphism that maps each cusp subgroup of
the source into a cusp subgroup of the target. -/
theorem map_mem_cuspidalFamily {L₂ : Type} [Group L₂] {κ : Type} (B₂ : κ → Subgroup L₂)
    (σ : L₂ →* L) (hσ : ∀ j, ∃ i, (B₂ j).map σ ≤ B i) {V₁ : Rep ℂ L} {V₂ : Rep ℂ L₂}
    (φ : Rep.res σ V₁ ⟶ V₂) (x : groupCohomology.H1 V₁) (hx : x ∈ cuspidalFamily B V₁) :
    (groupCohomology.map σ φ 1).hom x ∈ cuspidalFamily B₂ V₂ := by
  induction x using groupCohomology.H1_induction_on with
  | h c =>
    rw [groupCohomology.H1π_comp_map_apply, mem_cuspidalFamily_π]
    rw [mem_cuspidalFamily_π] at hx
    intro j
    obtain ⟨i, hi⟩ := hσ j
    obtain ⟨u, hu⟩ := hx i
    refine ⟨φ.hom u, fun γ => ?_⟩
    have h1 := hu ⟨σ (γ : L₂), hi ⟨γ, γ.2, rfl⟩⟩
    change φ.hom (c.1 (σ (γ : L₂))) = V₂.ρ (γ : L₂) (φ.hom u) - φ.hom u
    change c.1 (σ (γ : L₂)) = V₁.ρ (σ (γ : L₂)) u - u at h1
    rw [h1, map_sub]
    congr 1
    exact Rep.hom_comm_apply φ (γ : L₂) u

end CuspidalFamilyTools

end TernaryPeriodPolynomials.Argument.SeedC3S4c
