module

public import TernaryPeriodPolynomials.Topology.Rational.Cohomology.Descent
public import Mathlib.RepresentationTheory.Invariants

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryInvariantTransfer
open CategoryTheory RationalCohomologyDescent
variable {G : Type} [Group G] (H : Subgroup G) (A : Rep ℚ G)

/-- A subgroup-fixed vector gives a genuine constant coinduced function. -/
def constant : (Rep.res H.subtype A).ρ.invariants →ₗ[ℚ]
    Rep.coind H.subtype (Rep.res H.subtype A) where
  toFun v := ⟨fun _ => v.val,fun h _ => ((Representation.mem_invariants _ _).mp v.property h).symm⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem constant_apply (v : (Rep.res H.subtype A).ρ.invariants) (g : G) :
    (constant H A v).val g=v.val := rfl

theorem constant_fixed (v : (Rep.res H.subtype A).ρ.invariants) (g : G) :
    (Rep.coind H.subtype (Rep.res H.subtype A)).ρ g (constant H A v)=constant H A v := rfl

variable [H.FiniteIndex]
attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- The unnormalized finite-index transfer on actual fixed vectors. -/
def transfer : (Rep.res H.subtype A).ρ.invariants →ₗ[ℚ] A.ρ.invariants :=
  ((coindTrace H A).hom.toLinearMap.comp (constant H A)).codRestrict A.ρ.invariants (by
    intro v
    rw [Representation.mem_invariants]
    intro g
    have he := (coindTrace H A).hom.isIntertwining' g
    have hev := LinearMap.congr_fun he (constant H A v)
    change (coindTrace H A).hom
      ((Rep.coind H.subtype (Rep.res H.subtype A)).ρ g (constant H A v))=
      A.ρ g ((coindTrace H A).hom (constant H A v)) at hev
    rw [constant_fixed] at hev
    exact hev.symm)

/-- Exact sum over right cosets, with the inverse action dictated by induction/coinduction. -/
theorem transfer_apply (v : (Rep.res H.subtype A).ρ.invariants) :
    (transfer H A v).val =
      ∑ q : RightCosets H,A.ρ q.out⁻¹ v.val := by
  classical
  change (indCounit H A).hom
    ((Rep.res H.subtype A).coindToInd (constant H A v)) = _
  rw [Rep.coindToInd_apply,map_sum]
  apply Finset.sum_congr rfl
  intro q _
  have hq : (Quotient.mk (QuotientGroup.rightRel H) q.out) = q := Quotient.out_eq q
  conv_lhs => rw [← hq]
  rw [Quotient.liftOn_mk,indCounit_mk,constant_apply]

/-- Restriction of a globally fixed vector followed by transfer multiplies by the actual index. -/
theorem transfer_of_fixed (v : A.ρ.invariants) :
    (transfer H A ⟨v.val,by
      rw [Representation.mem_invariants]
      intro h
      exact (Representation.mem_invariants _ _).mp v.property h.val⟩).val =
      (Nat.card (RightCosets H) : ℚ) • v.val := by
  rw [transfer_apply]
  have hv (q : RightCosets H) : A.ρ q.out⁻¹ v.val=v.val :=
    (Representation.mem_invariants _ _).mp v.property _
  simp only [hv,Finset.sum_const,Finset.card_univ,Nat.card_eq_fintype_card]
  exact (Nat.cast_smul_eq_nsmul ℚ _ _).symm

/-- Genuine representation morphisms commute with the unnormalized transfer. -/
theorem transfer_natural {B : Rep ℚ G} (f : A ⟶ B)
    (v : (Rep.res H.subtype A).ρ.invariants)
    (w : (Rep.res H.subtype B).ρ.invariants) (hw : w.val=f.hom v.val) :
    f.hom (transfer H A v).val=(transfer H B w).val := by
  rw [transfer_apply,transfer_apply,map_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [hw]
  exact LinearMap.congr_fun (f.hom.isIntertwining' q.out⁻¹) v.val

end TernaryPoly.OrdinaryInvariantTransfer
