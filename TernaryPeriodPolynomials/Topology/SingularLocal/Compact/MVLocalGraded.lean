module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.MVGraded
public import TernaryPeriodPolynomials.Topology.SingularLocal.Support.Cochains

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCompactMV
open CategoryTheory HomologicalComplex SingularLocalCoefficient EquivariantSingularResolution
open EquivariantSingularSmall EquivariantSingularMayerVietoris SingularLocalSupport

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G)

/-- Under the actual local-cochain comparison, vanishing on a subset means annihilating its actual subordinate chains. -/
theorem localRestriction_zero_iff (A : Set B) (n : ℕ)
    (c : (equivariantChains G E).X n ⟶ V) :
    (localRestriction p A V).f n ((cochainIso p hp.out V).hom.f n c) = 0 ↔
      (subordinateInclusion G E (p ⁻¹' A) (preimage_invariant p A)).f n ≫ c = 0 := by
  have h := congrArg (fun f => f c)
    (HomologicalComplex.congr_hom (subordinateLocalIso_restriction p A V) n)
  change (subordinateLocalIso p A V).hom.f n
    ((subordinateInclusion G E (p ⁻¹' A) (preimage_invariant p A)).f n ≫ c) =
      (localRestriction p A V).f n ((cochainIso p hp.out V).hom.f n c) at h
  rw [← h]
  exact (map_eq_zero_iff ((subordinateLocalIso p A V).hom.f n).hom
    ((ModuleCat.mono_iff_injective _).mp inferInstance))

/-- Every actual local cochain vanishing on A∩D has graded summands vanishing on A and D separately. -/
theorem local_cochain_decomposition (A D : Set B) (n : ℕ) (c : (localCochains p hp.out V).X n)
    (hc : (localRestriction p (A ∩ D) V).f n c = 0) :
    ∃ x y : (localCochains p hp.out V).X n,
      (localRestriction p A V).f n x = 0 ∧ (localRestriction p D V).f n y = 0 ∧ x+y=c := by
  obtain ⟨c,rfl⟩ := (ModuleCat.epi_iff_surjective ((cochainIso p hp.out V).hom.f n)).mp inferInstance c
  have hc' := (localRestriction_zero_iff p V (A ∩ D) n c).mp hc
  have hinter : (subordinateInclusion G E ((p ⁻¹' A) ∩ (p ⁻¹' D))
      (invariant_inter G E _ _ (preimage_invariant p A) (preimage_invariant p D))).f n ≫ c = 0 := hc'
  obtain ⟨x,y,hx,hy,hxy⟩ := graded_cochain_decomposition G E (p ⁻¹' A) (p ⁻¹' D)
    (preimage_invariant p A) (preimage_invariant p D) V n c hinter
  refine ⟨(cochainIso p hp.out V).hom.f n x,(cochainIso p hp.out V).hom.f n y,
    (localRestriction_zero_iff p V A n x).mpr hx,(localRestriction_zero_iff p V D n y).mpr hy,?_⟩
  erw [← map_add,hxy]

end TernaryPoly.SingularLocalCompactMV
