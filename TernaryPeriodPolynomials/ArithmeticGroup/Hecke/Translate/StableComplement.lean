/-
  From complementary invariant subspaces to an invariant projection.

  This is the general linear-algebra step of the associate-pair construction:
  once (a) the associate pair is stable under the Hecke action and (b) it has
  a Hecke-stable complement, the projection along that complement exists, has
  the required range, fixes the associate pair, and commutes with every Hecke
  operator.  Stated abstractly so it applies to any Hecke module.
-/
module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.HeckeTranslate.StableComplement

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- **Invariant projection from an invariant complement.**  If `S` and `S'` are
complementary subspaces and a family `H` of endomorphisms preserves each of them,
then the projection onto `S` along `S'` exists, has range `S`, fixes `S`, and
commutes with every member of `H`. -/
theorem exists_invariant_projection (S S' : Submodule ℂ V) (h : IsCompl S S')
    (H : Set (Module.End ℂ V))
    (hS : ∀ A ∈ H, ∀ x ∈ S, A x ∈ S)
    (hS' : ∀ A ∈ H, ∀ x ∈ S', A x ∈ S') :
    ∃ p : Module.End ℂ V, LinearMap.range p = S ∧ (∀ x ∈ S, p x = x) ∧
      ∀ A ∈ H, p.comp A = A.comp p := by
  refine ⟨S.projection S' h, Submodule.range_projection h, ?_, ?_⟩
  · intro x hx
    exact Submodule.projection_apply_of_mem_left h hx
  · intro A hA
    apply LinearMap.ext
    intro x
    show (S.projection S' h) (A x) = A ((S.projection S' h) x)
    have hmem : x - (S.projection S' h) x ∈ S' := Submodule.sub_projection_mem h x
    have hAx : A x = A ((S.projection S' h) x) + A (x - (S.projection S' h) x) := by
      rw [← map_add]
      congr 1
      abel
    rw [hAx, map_add,
      Submodule.projection_apply_of_mem_left h
        (hS A hA _ (Submodule.projection_apply_mem h x)),
      Submodule.projection_apply_of_mem_right h (hS' A hA _ hmem), add_zero]

/-- **Conversely**, the kernel of an invariant idempotent with range `S` is an
`H`-stable complement of `S`.  Thus (invariant complement) and (invariant
projection with range `S`) are equivalent. -/
theorem exists_stable_complement_of_invariant_projection (S : Submodule ℂ V)
    (H : Set (Module.End ℂ V)) (p : Module.End ℂ V)
    (hrange : LinearMap.range p = S) (hfix : ∀ x ∈ S, p x = x)
    (hcomm : ∀ A ∈ H, p.comp A = A.comp p) :
    ∃ S' : Submodule ℂ V, IsCompl S S' ∧ ∀ A ∈ H, ∀ x ∈ S', A x ∈ S' := by
  have hpp : ∀ y, p (p y) = p y := fun y =>
    hfix (p y) (by rw [← hrange]; exact LinearMap.mem_range_self p y)
  refine ⟨LinearMap.ker p, ⟨?_, ?_⟩, ?_⟩
  · rw [disjoint_iff_inf_le]
    intro x hx
    rw [Submodule.mem_bot]
    have hxS : x ∈ S := hx.1
    have hxker : p x = 0 := LinearMap.mem_ker.mp hx.2
    rw [← hfix x hxS, hxker]
  · rw [codisjoint_iff_le_sup]
    intro x _
    have hpx : p x ∈ S := by rw [← hrange]; exact LinearMap.mem_range_self p x
    have hker : x - p x ∈ LinearMap.ker p := by
      rw [LinearMap.mem_ker, map_sub, hpp x, sub_self]
    have : p x + (x - p x) = x := by abel
    rw [← this]
    exact Submodule.add_mem_sup hpx hker
  · intro A hA x hx
    rw [LinearMap.mem_ker] at hx ⊢
    show p (A x) = 0
    rw [← LinearMap.comp_apply, hcomm A hA, LinearMap.comp_apply, hx, map_zero]

end TernaryPeriodPolynomials.HeckeTranslate.StableComplement

end
