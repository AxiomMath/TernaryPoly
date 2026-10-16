module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.InvariantTransfer
public import Mathlib.GroupTheory.GroupAction.ConjAct

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryHeckeTransfer
open CategoryTheory OrdinaryInvariantTransfer RationalCohomologyDescent
variable {G : Type} [Group G] (Γ : Subgroup G) (g : G)

/-- The actual intersection Γ∩gΓg⁻¹, viewed inside Γ. -/
def intersection : Subgroup Γ :=
  Γ.comap ((MulAut.conj g⁻¹).toMonoidHom.comp Γ.subtype)

@[simp] theorem mem_intersection (h : Γ) : h ∈ intersection Γ g ↔ g⁻¹*h.val*g ∈ Γ := by
  simp [intersection]

/-- Conjugation carries a Γ-fixed vector to a vector fixed by the actual intersection. -/
def translate (A : Rep ℚ G) : (Rep.res Γ.subtype A).ρ.invariants →ₗ[ℚ]
    (Rep.res (intersection Γ g).subtype (Rep.res Γ.subtype A)).ρ.invariants :=
  ((A.ρ g).comp (Rep.res Γ.subtype A).ρ.invariants.subtype).codRestrict _ (by
    intro v
    rw [Representation.mem_invariants]
    intro h
    have hh : g⁻¹*h.val.val*g ∈ Γ := (mem_intersection Γ g h.val).mp h.property
    have hv := (Representation.mem_invariants _ _).mp v.property ⟨_,hh⟩
    change A.ρ (g⁻¹*h.val.val*g) v.val=v.val at hv
    change A.ρ h.val.val (A.ρ g v.val)=A.ρ g v.val
    calc
      _ = A.ρ g (A.ρ (g⁻¹*h.val.val*g) v.val) := by
        simp only [←Module.End.mul_apply,←map_mul]
        congr 1
        group
      _ = _ := congrArg (A.ρ g) hv)

@[simp] theorem translate_val (A : Rep ℚ G) (v : (Rep.res Γ.subtype A).ρ.invariants) :
    (translate Γ g A v).val=A.ρ g v.val := rfl

variable [(intersection Γ g).FiniteIndex]
attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- The genuine unnormalized Hecke operator: conjugation followed by finite-index transfer. -/
def hecke (A : Rep ℚ G) : Module.End ℚ (Rep.res Γ.subtype A).ρ.invariants :=
  (transfer (intersection Γ g) (Rep.res Γ.subtype A)).comp (translate Γ g A)

/-- Exact double-coset sum, using inverse right-coset representatives. -/
theorem hecke_apply (A : Rep ℚ G) (v : (Rep.res Γ.subtype A).ρ.invariants) :
    (hecke Γ g A v).val=
      ∑ q : RightCosets (intersection Γ g),A.ρ (q.out.val⁻¹*g) v.val := by
  change (transfer (intersection Γ g) (Rep.res Γ.subtype A) (translate Γ g A v)).val=_
  rw [transfer_apply]
  apply Finset.sum_congr rfl
  intro q _
  change A.ρ q.out.val⁻¹ (A.ρ g v.val)=A.ρ (q.out.val⁻¹*g) v.val
  rw [map_mul,Module.End.mul_apply]

/-- Every actual ambient coefficient intertwiner commutes with this correspondence. -/
theorem hecke_natural {A B : Rep ℚ G} (f : A ⟶ B)
    (v : (Rep.res Γ.subtype A).ρ.invariants) (w : (Rep.res Γ.subtype B).ρ.invariants)
    (hw : w.val=f.hom v.val) : f.hom (hecke Γ g A v).val=(hecke Γ g B w).val := by
  rw [hecke_apply,hecke_apply,map_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [hw]
  exact LinearMap.congr_fun (f.hom.isIntertwining' (q.out.val⁻¹*g)) v.val

end TernaryPoly.OrdinaryHeckeTransfer
