module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FullDescent

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryFullTransfer
open CategoryTheory RationalCohomologyDescent
variable {G : Type} [Group G] (H : Subgroup G) [H.FiniteIndex]
attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- Full equivariance is exactly invariance under the finite set of right-coset conjugations. -/
theorem finite_invariance_iff (A V : Rep.{0} ℚ G)
    (f : Rep.res H.subtype A ⟶ Rep.res H.subtype V) :
    (∀ q : RightCosets H, ∀ x : A,
      V.ρ q.out⁻¹ (f.hom (A.ρ q.out x)) = f.hom x) ↔
      ∀ g : G, ∀ x : A, f.hom (A.ρ g x) = V.ρ g (f.hom x) := by
  constructor
  · intro h
    apply (transfer_fixed_iff H A V f).mp
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    change (transferHom H A V f).hom x = f.hom x
    rw [transferHom_apply]
    simp only [h,Finset.sum_const,Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul ℚ,← Nat.card_eq_fintype_card,smul_smul,inv_mul_cancel₀,one_smul]
    exact_mod_cast (Nat.card_pos (α := RightCosets H)).ne'
  · intro h q x
    rw [h,← Module.End.mul_apply,← map_mul,inv_mul_cancel,map_one,Module.End.one_apply]

end TernaryPoly.SymmetricSpaceBoundaryFullTransfer

namespace TernaryPoly.SymmetricSpaceBoundaryFull
open CategoryTheory HomologicalComplex

/-- The actual full-level summand of finite-cover boundary cohomology, specified by the geometric projector. -/
def fullLevelComponent (n : ℕ) (e : ℤ) (j : ℕ) :
    Submodule ℚ ((coverBoundaryCochains n e).homology j) :=
  LinearMap.ker ((homologyMap (boundaryProjector n e) j).hom - LinearMap.id)

@[simp] theorem mem_fullLevelComponent (n : ℕ) (e : ℤ) (j : ℕ)
    (x : (coverBoundaryCochains n e).homology j) :
    x ∈ fullLevelComponent n e j ↔ homologyMap (boundaryProjector n e) j x = x := by
  simp only [fullLevelComponent,LinearMap.mem_ker,LinearMap.sub_apply,LinearMap.id_apply,sub_eq_zero]

/-- The geometric full-level image is exactly the projector-fixed component. -/
theorem fullLevelComponent_iff_image (n : ℕ) (e : ℤ) (j : ℕ)
    (x : (coverBoundaryCochains n e).homology j) :
    x ∈ fullLevelComponent n e j ↔
      ∃ y : (fullBoundaryCochains n e).homology j, homologyMap (boundaryRestriction n e) j y = x := by
  rw [mem_fullLevelComponent]
  have hs : homologyMap (boundaryRestriction n e) j ≫ homologyMap (boundaryTransfer n e) j = 𝟙 _ := by
    rw [← homologyMap_comp,boundaryRestriction_transfer,homologyMap_id]
  constructor
  · intro h
    refine ⟨homologyMap (boundaryTransfer n e) j x,?_⟩
    change (homologyMap (boundaryTransfer n e) j ≫ homologyMap (boundaryRestriction n e) j) x = x
    rw [← homologyMap_comp]
    exact h
  · rintro ⟨y,rfl⟩
    change homologyMap (boundaryTransfer n e ≫ boundaryRestriction n e) j _ = _
    rw [homologyMap_comp]
    have he := congrArg (fun f => f y) hs
    change homologyMap (boundaryRestriction n e) j
      (homologyMap (boundaryTransfer n e) j (homologyMap (boundaryRestriction n e) j y)) = _
    exact congrArg (fun z => homologyMap (boundaryRestriction n e) j z) he

/-- Genuine full-level cohomology is isomorphic precisely to its entire-boundary invariant summand. -/
def fullLevelComponentEquiv (n : ℕ) (e : ℤ) (j : ℕ) :
    (fullBoundaryCochains n e).homology j ≃ₗ[ℚ] fullLevelComponent n e j :=
  LinearEquiv.ofBijective
    ((homologyMap (boundaryRestriction n e) j).hom.codRestrict (fullLevelComponent n e j)
      (fun x => (fullLevelComponent_iff_image n e j _).mpr ⟨x,rfl⟩))
    ⟨fun x y h => boundaryRestriction_injective n e j (congrArg Subtype.val h),by
      intro x
      obtain ⟨y,hy⟩ := (fullLevelComponent_iff_image n e j x.val).mp x.property
      exact ⟨y,Subtype.ext hy⟩⟩

end TernaryPoly.SymmetricSpaceBoundaryFull
