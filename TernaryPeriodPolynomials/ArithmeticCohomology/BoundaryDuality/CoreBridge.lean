module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.CocycleBridge
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Existence

@[expose] public section


/-!
# The parabolic cup pairing on `H¹(Γ₁(3), ·)`

`Γ₁(3) = ⟨T, L⟩ ≅ ℤ * ℤ/3` (D's `FreeProduct.coreEquiv`), `E = T L⁻¹` of order three.  Take the
three special elements `a = T`, `g₂ = L⁻¹`, `a g₂ = E` of the triple model: two cusps (`T`, `L`) and
one cone point (`E`).  Every parabolic crossed homomorphism has a primitive triple, every constrained
triple is the primitive triple of a crossed homomorphism (D's `Existence.exists_cocycle`), and
crossed homomorphisms are determined by their values at `T` and `L⁻¹`.  Hence the cup pairing of
`CocycleBridge` on the parabolic classes of `Γ₁(3)` with coefficients in a perfectly paired
`(V, W)` has trivial left and right radical: **Poincaré duality for the parabolic cohomology of
`Γ₁(3)` with arbitrary invariant coefficients**.
-/

noncomputable section

namespace TernaryPeriodPolynomials.BoundaryDuality.CoreBridge

open TripleModel LinearDuality CocycleBridge
open TernaryPeriodPolynomials.LevelThree
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open GammaOneThree FreeProduct TwoGenerator

variable {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ core V)

/-- In characteristic zero the kernel of the norm of `E` (`E³ = 1`) is the image of `E - 1`. -/
theorem exists_sub_of_norm3 {b : V} (hb : norm3 ρ coreE b = 0) : ∃ s, ρ coreE s - s = b := by
  have h3 : ρ coreE (ρ coreE (ρ coreE b)) = b := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
      show coreE * coreE * coreE = coreE ^ 3 by rw [pow_succ, pow_two], coreE_cube, map_one,
      Module.End.one_apply]
  refine ⟨(3 : ℂ)⁻¹ • (ρ coreE b + (2 : ℂ) • ρ coreE (ρ coreE b)), ?_⟩
  rw [norm3_apply] at hb
  simp only [map_smul, map_add, h3]
  linear_combination (norm := module) (-(3 : ℂ)⁻¹) • hb

/-- Every parabolic crossed homomorphism of `Γ₁(3)` has a primitive triple. -/
theorem exists_primitive {z : crossedCocycles ρ} (hz : z ∈ parabolicCocycles ρ coreT coreL) :
    ∃ v : V × V × V, IsPrimitive ρ coreT coreL⁻¹ z.val v := by
  obtain ⟨v1, hv1⟩ := (mem_moved _).1 hz.1
  obtain ⟨w, hw⟩ := (mem_moved _).1 hz.2
  obtain ⟨s, hs⟩ := exists_sub_of_norm3 ρ (norm3_cocycle_eq_zero z coreE_cube)
  refine ⟨(v1, w, s), ?_, ?_, ?_⟩
  · show z.val coreT = (ρ coreT - 1) v1
    rw [LinearMap.sub_apply, Module.End.one_apply]
    exact hv1.symm
  · have h := cocycle_inv z coreL
    have e : ρ coreL⁻¹ (ρ coreL w) = w := rep_inv_apply ρ coreL w
    show z.val coreL⁻¹ = (ρ coreL⁻¹ - 1) w
    rw [LinearMap.sub_apply, Module.End.one_apply, h, ← hw, map_sub, e]
    abel
  · have h := cocycle_inv z coreE
    have e : ρ coreE⁻¹ (ρ coreE s) = s := rep_inv_apply ρ coreE s
    change z.val coreE⁻¹ = (ρ coreE⁻¹ - 1) s
    rw [LinearMap.sub_apply, Module.End.one_apply, h, ← hs, map_sub, e]
    abel

/-- A crossed homomorphism with a primitive triple is parabolic. -/
theorem parabolic_of_primitive {z : crossedCocycles ρ} {v : V × V × V}
    (hv : IsPrimitive ρ coreT coreL⁻¹ z.val v) : z ∈ parabolicCocycles ρ coreT coreL := by
  refine ⟨(mem_moved _).2 ⟨v.1, ?_⟩, (mem_moved _).2 ⟨v.2.1, ?_⟩⟩
  · have := hv.1
    rw [LinearMap.sub_apply, Module.End.one_apply] at this
    exact this.symm
  · have h := cocycle_inv z coreL⁻¹
    rw [inv_inv] at h
    have e : ρ coreL (ρ coreL⁻¹ v.2.1) = v.2.1 := by
      rw [← rep_mul_apply, mul_inv_cancel, map_one, Module.End.one_apply]
    have := hv.2.1
    rw [LinearMap.sub_apply, Module.End.one_apply] at this
    rw [h, this, map_sub, e]
    abel

/-- Crossed homomorphisms of `Γ₁(3)` are determined by their values at `T` and `L⁻¹`. -/
theorem generated (z z' : core → V) (hz : IsCocycle ρ z) (hz' : IsCocycle ρ z')
    (h1 : z coreT = z' coreT) (h2 : z coreL⁻¹ = z' coreL⁻¹) : z = z' := by
  have := cocycle_ext_of_closure (ρ := ρ) (S := ({coreT, coreE} : Set core)) Existence.closure_T_E
    (z := ⟨z, hz⟩) (z' := ⟨z', hz'⟩) (by
      rintro s (rfl | rfl)
      · exact h1
      · change z (coreT * coreL⁻¹) = z' (coreT * coreL⁻¹)
        rw [hz coreT coreL⁻¹, hz' coreT coreL⁻¹, h1, h2])
  exact congrArg Subtype.val this

/-- Every constrained triple is the primitive triple of a crossed homomorphism of `Γ₁(3)`. -/
theorem exists_cocycle_primitive {v : V × V × V} (hv : v ∈ tripleCycles ρ coreT coreL⁻¹) :
    ∃ z : core → V, IsCocycle ρ z ∧ IsPrimitive ρ coreT coreL⁻¹ z v := by
  have hc : constraint ρ coreT coreL⁻¹ v = 0 := LinearMap.mem_ker.1 hv
  rw [constraint_apply] at hc
  have hb : norm3 ρ coreE ((ρ coreE - 1) v.2.2) = 0 := by
    have := norm3_sub_eq_zero (ρ := ρ) coreE_cube v.2.2
    rw [LinearMap.sub_apply, Module.End.one_apply]
    exact this
  obtain ⟨z, hzT, hzE⟩ := Existence.exists_cocycle ρ ((ρ coreT - 1) v.1) ((ρ coreE - 1) v.2.2) hb
  refine ⟨z.val, z.property, ?_⟩
  refine ⟨hzT, ?_, ?_⟩
  · have hE : z.val coreE = z.val coreT + ρ coreT (z.val coreL⁻¹) := z.property coreT coreL⁻¹
    have m : ρ (coreT * coreL⁻¹) v.2.1 = ρ coreT (ρ coreL⁻¹ v.2.1) := rep_mul_apply ρ _ _ _
    have hzT' : z.val coreT = ρ coreT v.1 - v.1 := by
      rw [hzT, LinearMap.sub_apply, Module.End.one_apply]
    have hzE' : z.val coreE = ρ coreE v.2.2 - v.2.2 := by
      rw [hzE, LinearMap.sub_apply, Module.End.one_apply]
    have hc' := hc
    simp only [LinearMap.sub_apply, Module.End.one_apply] at hc'
    have key : ρ coreT (z.val coreL⁻¹) = ρ coreT ((ρ coreL⁻¹ - 1) v.2.1) := by
      rw [LinearMap.sub_apply, Module.End.one_apply, map_sub, ← m]
      linear_combination (norm := module) (-1 : ℂ) • hE + (1 : ℂ) • hzE' + (-1 : ℂ) • hzT' +
        (-1 : ℂ) • hc'
    have := congrArg (fun w => ρ coreT⁻¹ w) key
    simpa only [rep_inv_apply ρ] using this
  · have h := cocycle_inv z coreE
    have e : ρ coreE⁻¹ (ρ coreE v.2.2) = v.2.2 := rep_inv_apply ρ coreE v.2.2
    change z.val coreE⁻¹ = (ρ coreE⁻¹ - 1) v.2.2
    rw [LinearMap.sub_apply, Module.End.one_apply, h, hzE, LinearMap.sub_apply,
      Module.End.one_apply, map_sub, e]
    abel

variable {W : Type} [AddCommGroup W] [Module ℂ W] (ρ' : Representation ℂ core W)
  {B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ}

/-- **Left nondegeneracy of the parabolic cup pairing on `Γ₁(3)`**: a crossed homomorphism which has
a primitive triple `v` (equivalently, is parabolic) and whose cup pairing with every parabolic crossed
homomorphism vanishes is a coboundary. -/
theorem left_nondegenerate [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
    (hL : ∀ v, (∀ w, B v w = 0) → v = 0) (hR : ∀ w, (∀ v, B v w = 0) → w = 0)
    (hinv : ∀ g v w, B (ρ g v) (ρ' g w) = B v w)
    {z : crossedCocycles ρ} {v : V × V × V} (hv : IsPrimitive ρ coreT coreL⁻¹ z.val v)
    (zero : ∀ z' : crossedCocycles ρ', ∀ v' : W × W × W, IsPrimitive ρ' coreT coreL⁻¹ z'.val v' →
      cupFormula B ρ' coreT coreL⁻¹ z.val z'.val v = 0) :
    z ∈ crossedBoundaries ρ := by
  obtain ⟨u, hu⟩ := CocycleBridge.left_nondegenerate (z := z.val) hL hR hinv coreT coreL⁻¹
    (generated ρ) (fun v' hv' => exists_cocycle_primitive ρ' hv') z.property hv
    (fun z' v' hz' hp => by
      rw [← cupFormula_eq_tripleForm hinv (z := z.val) z.property hv hp]
      exact zero ⟨z', hz'⟩ v' hp)
  exact LinearMap.mem_range.2 ⟨u, Subtype.ext (funext fun g => (hu g).symm)⟩

/-- **Right nondegeneracy of the parabolic cup pairing on `Γ₁(3)`.** -/
theorem right_nondegenerate [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
    (hL : ∀ v, (∀ w, B v w = 0) → v = 0) (hR : ∀ w, (∀ v, B v w = 0) → w = 0)
    (hinv : ∀ g v w, B (ρ g v) (ρ' g w) = B v w)
    {z' : crossedCocycles ρ'} {v' : W × W × W} (hv' : IsPrimitive ρ' coreT coreL⁻¹ z'.val v')
    (zero : ∀ z : crossedCocycles ρ, ∀ v : V × V × V, IsPrimitive ρ coreT coreL⁻¹ z.val v →
      cupFormula B ρ' coreT coreL⁻¹ z.val z'.val v = 0) :
    z' ∈ crossedBoundaries ρ' := by
  obtain ⟨u, hu⟩ := CocycleBridge.right_nondegenerate (z' := z'.val) hL hR hinv coreT coreL⁻¹
    (generated ρ') (fun v hv => exists_cocycle_primitive ρ hv) z'.property hv'
    (fun z v hz hp => by
      rw [← cupFormula_eq_tripleForm hinv hz hp hv']
      exact zero ⟨z, hz⟩ v hp)
  exact LinearMap.mem_range.2 ⟨u, Subtype.ext (funext fun g => (hu g).symm)⟩

end TernaryPeriodPolynomials.BoundaryDuality.CoreBridge
