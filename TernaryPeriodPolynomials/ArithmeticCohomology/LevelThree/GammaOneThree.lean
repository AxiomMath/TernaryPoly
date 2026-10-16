module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.TwoGenerator
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.LowDegreeParabolic

@[expose] public section


/-!
# `Γ₁(3)` inside the bad-line Levi `Γ₁'(3)`

`binaryArithmeticLevel = Γ₁'(3) = {A ∈ GL₂(ℤ) : second row ≡ (0, 1) mod 3}` is the binary Levi of
both level-three cusps (the bad line and the good plane). Its determinant-one part is
`Γ₁(3) = ⟨T, L⟩`, `T = [[1,1],[0,1]]`, `L = [[1,0],[3,1]]`, and `Γ₁'(3) = Γ₁(3) ⊔ Γ₁(3) ε`
with `ε = diag(-1, 1)` normalizing `Γ₁(3)` (`εTε = T⁻¹`, `εLε = L⁻¹`).

* `core`: the subgroup `⟨T, L⟩`; `core_closure`, `core_elliptic_cube` (the hypotheses of
  `TwoGenerator`);
* `mem_core_or`: every element of `Γ₁'(3)` lies in `core` or in `core · ε`;
* `pullback_injective`: for an index-two situation of this shape, restriction of `H¹` is injective
  as soon as the subgroup has no nonzero invariant vectors.

Generation of `Γ₁'(3)` by `T`, `L`, `ε` is Sol's `ArithmeticGenerators.generators_span`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.LevelThree.GammaOneThree

open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic
open Helpers ArithmeticGenerators LowDegreeParabolic TwoGenerator

section IndexTwo

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)

/-- **Restriction to an index-two subgroup is injective on `H¹`** when the subgroup has no
nonzero invariants: if `G = H ∪ H ε` and `ε⁻¹ H ε ⊆ H`. -/
theorem pullback_injective (H : Subgroup G) (ε : G) (cover : ∀ g : G, g ∈ H ∨ g * ε ∈ H)
    (normal : ∀ k ∈ H, ε⁻¹ * k * ε ∈ H)
    (noInvariants : ∀ v : V, (∀ h ∈ H, ρ h v = v) → v = 0) :
    Function.Injective (crossedPullbackH1 H.subtype ρ) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hx' := hx
  change (crossedBoundaries (ρ.comp H.subtype)).mkQ (crossedPullbackCocycles H.subtype ρ z) = 0 at hx'
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hx'
  obtain ⟨v, hv⟩ := hx'
  have onH : ∀ h ∈ H, z.val h = ρ h v - v := by
    intro h hh
    exact (congrFun (congrArg Subtype.val hv) ⟨h, hh⟩).symm
  let z' : crossedCocycles ρ := z - crossedBoundary ρ v
  have z'H : ∀ h ∈ H, z'.val h = 0 := by
    intro h hh
    change z.val h - (ρ h v - v) = 0
    rw [onH h hh, sub_self]
  have fixedA : ∀ k ∈ H, ρ k (z'.val ε) = z'.val ε := by
    intro k hk
    have hmem := normal k hk
    have e : k * ε = ε * (ε⁻¹ * k * ε) := by group
    have h1 := cocycle_mul z' k ε
    have h2 := cocycle_mul z' ε (ε⁻¹ * k * ε)
    rw [z'H k hk, zero_add] at h1
    rw [z'H _ hmem, map_zero, add_zero, ← e] at h2
    rw [← h1, h2]
  have a0 : z'.val ε = 0 := noInvariants _ fixedA
  have z'0 : z' = 0 := by
    apply Subtype.ext
    funext g
    rcases cover g with hg | hg
    · exact z'H g hg
    · have h := cocycle_mul z' g ε
      rw [z'H _ hg, a0, map_zero, add_zero] at h
      exact h.symm
  have equal : z = crossedBoundary ρ v := sub_eq_zero.mp z'0
  change (crossedBoundaries ρ).mkQ z = 0
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact ⟨v, equal.symm⟩

end IndexTwo

section Core

/-- `Γ₁(3) = ⟨T, L⟩` inside `Γ₁'(3)`. -/
def core : Subgroup binaryArithmeticLevel := Subgroup.closure {upper 1, lower 1}

/-- `T` as an element of `Γ₁(3)`. -/
def coreT : core := ⟨upper 1, Subgroup.subset_closure (by simp)⟩

/-- `L` as an element of `Γ₁(3)`. -/
def coreL : core := ⟨lower 1, Subgroup.subset_closure (by simp)⟩

theorem core_closure : Subgroup.closure ({coreT, coreL} : Set core) = ⊤ := by
  have h := Subgroup.closure_closure_coe_preimage (k := ({upper 1, lower 1} : Set binaryArithmeticLevel))
  have hs : ({coreT, coreL} : Set core) =
      ((↑) : core → binaryArithmeticLevel) ⁻¹' {upper 1, lower 1} := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_preimage]
    constructor
    · rintro (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (h | h)
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
  rw [hs]
  exact h

theorem lower_inv : (lower 1)⁻¹ = lower (-1) := by
  rw [lower_zpow (-1), zpow_neg_one]

theorem core_elliptic_cube : (coreT * coreL⁻¹) ^ 3 = 1 := by
  apply Subtype.ext
  change (upper 1 * (lower 1)⁻¹) ^ 3 = 1
  rw [lower_inv]
  exact elliptic_cube

theorem reflection_mul_self : reflection * reflection = 1 := by
  apply Subtype.ext
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [reflection, Matrix.mul_apply, Fin.sum_univ_two]

theorem reflection_inv : reflection⁻¹ = reflection :=
  inv_eq_of_mul_eq_one_right reflection_mul_self

theorem reflection_conj_upper : reflection * upper 1 * reflection = upper (-1) := by
  apply Subtype.ext
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [reflection, upper, Matrix.mul_apply, Fin.sum_univ_two]

theorem reflection_conj_lower : reflection * lower 1 * reflection = lower (-1) := by
  apply Subtype.ext
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [reflection, lower, Matrix.mul_apply, Fin.sum_univ_two]

theorem upper_neg_mem : upper (-1) ∈ core := by
  rw [upper_zpow]
  exact core.zpow_mem (Subgroup.subset_closure (by simp)) _

theorem lower_neg_mem : lower (-1) ∈ core := by
  rw [lower_zpow]
  exact core.zpow_mem (Subgroup.subset_closure (by simp)) _

/-- `ε` normalizes `Γ₁(3)`. -/
theorem conj_mem_core {k : binaryArithmeticLevel} (hk : k ∈ core) :
    reflection * k * reflection ∈ core := by
  induction hk using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · rw [reflection_conj_upper]; exact upper_neg_mem
    · rw [reflection_conj_lower]; exact lower_neg_mem
  | one => rw [mul_one, reflection_mul_self]; exact core.one_mem
  | mul x y _ _ hx hy =>
    have e : reflection * (x * y) * reflection =
        (reflection * x * reflection) * (reflection * y * reflection) := by
      simp only [mul_assoc, ← mul_assoc reflection reflection, reflection_mul_self, one_mul]
    rw [e]
    exact core.mul_mem hx hy
  | inv x _ hx =>
    have e : reflection * x⁻¹ * reflection = (reflection * x * reflection)⁻¹ := by
      simp only [mul_inv_rev, reflection_inv, mul_assoc]
    rw [e]
    exact core.inv_mem hx

theorem conj_inv_mem_core {k : binaryArithmeticLevel} (hk : k ∈ core) :
    reflection⁻¹ * k * reflection ∈ core := by
  rw [reflection_inv]
  exact conj_mem_core hk

/-- **`Γ₁'(3) = Γ₁(3) ⊔ Γ₁(3) ε`**. -/
theorem mem_core_or (g : binaryArithmeticLevel) : g ∈ core ∨ g * reflection ∈ core := by
  have hεε : ∀ x : binaryArithmeticLevel, reflection * (reflection * x) = x := by
    intro x
    rw [← mul_assoc, reflection_mul_self, one_mul]
  let K : Subgroup binaryArithmeticLevel :=
    { carrier := {g | g ∈ core ∨ g * reflection ∈ core}
      one_mem' := Or.inl core.one_mem
      mul_mem' := by
        intro g k hg hk
        rcases hg with hg | hg <;> rcases hk with hk | hk
        · exact Or.inl (core.mul_mem hg hk)
        · right
          rw [mul_assoc]
          exact core.mul_mem hg hk
        · right
          have e : g * k * reflection = (g * reflection) * (reflection * k * reflection) := by
            simp only [mul_assoc, hεε]
          rw [e]
          exact core.mul_mem hg (conj_mem_core hk)
        · left
          have e : g * k = (g * reflection) * (reflection * (k * reflection) * reflection) := by
            simp only [mul_assoc, hεε, reflection_mul_self, mul_one]
          rw [e]
          exact core.mul_mem hg (conj_mem_core hk)
      inv_mem' := by
        intro g hg
        rcases hg with hg | hg
        · exact Or.inl (core.inv_mem hg)
        · right
          have e : g⁻¹ * reflection = reflection * (g * reflection)⁻¹ * reflection := by
            simp only [mul_inv_rev, reflection_inv, hεε]
          rw [e]
          exact conj_mem_core (core.inv_mem hg) }
  have top : K = ⊤ := by
    apply top_unique
    rw [← generators_span]
    apply (Subgroup.closure_le K).mpr
    intro x hx
    rcases hx with rfl | rfl | rfl
    · exact Or.inl (Subgroup.subset_closure (by simp))
    · exact Or.inl (Subgroup.subset_closure (by simp))
    · right
      rw [reflection_mul_self]
      exact core.one_mem
  have member : g ∈ K := top ▸ Subgroup.mem_top g
  exact member

/-- Restriction from `Γ₁'(3)` to `Γ₁(3)` is injective on `H¹` when `Γ₁(3)` has no invariants. -/
theorem core_pullback_injective {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ binaryArithmeticLevel V)
    (noInvariants : ∀ v : V, (∀ h ∈ core, ρ h v = v) → v = 0) :
    Function.Injective (crossedPullbackH1 core.subtype ρ) :=
  pullback_injective ρ core reflection mem_core_or (fun _ hk => conj_inv_mem_core hk) noInvariants

end Core

end TernaryPeriodPolynomials.LevelThree.GammaOneThree
