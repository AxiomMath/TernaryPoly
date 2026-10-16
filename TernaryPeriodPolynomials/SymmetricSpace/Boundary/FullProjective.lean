module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FullTransferEvaluation

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryFullTransfer
open CategoryTheory RationalCohomologyDescent
variable {G : Type} [Group G] (H : Subgroup G) [H.FiniteIndex]
attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- Averaging also commutes with every genuine coefficient morphism. -/
theorem transferHom_postcomp {A V W : Rep.{0} ℚ G} (u : V ⟶ W)
    (f : Rep.res H.subtype A ⟶ Rep.res H.subtype V) :
    transferHom H A W (f ≫ (Rep.resFunctor H.subtype).map u) =
      transferHom H A V f ≫ u := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  change (transferHom H A W (f ≫ (Rep.resFunctor H.subtype).map u)).hom x =
    u.hom ((transferHom H A V f).hom x)
  rw [transferHom_apply,transferHom_apply,map_smul,map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  exact (LinearMap.congr_fun (u.hom.isIntertwining' q.out⁻¹) _).symm

/-- Rational projectivity descends along the actual finite-index subgroup restriction. -/
theorem projective_of_restriction (A : Rep.{0} ℚ G)
    [Projective (Rep.res H.subtype A)] : Projective A where
  factors {E X} f e _ := by
    let : Epi ((Rep.resFunctor H.subtype).map e) :=
      (Rep.epi_iff_surjective _).mpr ((Rep.epi_iff_surjective e).mp inferInstance)
    obtain ⟨l,hl⟩ := Projective.factors ((Rep.resFunctor H.subtype).map f)
      ((Rep.resFunctor H.subtype).map e)
    refine ⟨transferHom H A E l,?_⟩
    rw [← transferHom_postcomp,hl]
    exact restrict_transferHom H A X f

end TernaryPoly.SymmetricSpaceBoundaryFullTransfer
