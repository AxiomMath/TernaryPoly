module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FullTransfer

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryFullTransfer
open CategoryTheory HomologicalComplex EquivariantSingularSmall RationalCohomologyDescent

variable {G : Type} [Group G] (H : Subgroup G) [H.FiniteIndex]
attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- The unnormalized trace is the exact sum over right cosets. -/
theorem trace_apply (V : Rep.{0} ℚ G) (z : Rep.coind H.subtype (Rep.res H.subtype V)) :
    (coindTrace H V).hom z = ∑ q : RightCosets H, V.ρ q.out⁻¹ (z.val q.out) := by
  classical
  change (indCounit H V).hom ((Rep.res H.subtype V).coindToInd z) = _
  rw [Rep.coindToInd_apply,map_sum]
  apply Finset.sum_congr rfl
  intro q _
  have hq : Quotient.mk (QuotientGroup.rightRel H) q.out = q := Quotient.out_eq q
  conv_lhs => rw [← hq]
  rw [Quotient.liftOn_mk,indCounit_mk]

/-- Exact normalized finite-cover descent, retaining inverse actions and the index. -/
theorem transferHom_apply (A V : Rep.{0} ℚ G)
    (f : Rep.res H.subtype A ⟶ Rep.res H.subtype V) (x : A) :
    (transferHom H A V f).hom x =
      (Nat.card (RightCosets H) : ℚ)⁻¹ •
        ∑ q : RightCosets H, V.ρ q.out⁻¹ (f.hom (A.ρ q.out x)) := by
  change (Nat.card (RightCosets H) : ℚ)⁻¹ • (coindTrace H V).hom
    ((Rep.resCoindToHom H.subtype A (Rep.res H.subtype V) f).hom x) = _
  rw [trace_apply]
  rfl

/-- Restriction and transfer split actual cohomology, in every degree. -/
theorem homology_restriction_transfer (C : ChainComplex (Rep ℚ G) ℕ)
    (V : Rep.{0} ℚ G) (n : ℕ) :
    homologyMap (restriction H C V) n ≫ homologyMap (transfer H C V) n = 𝟙 _ := by
  rw [← homologyMap_comp,restriction_transfer,homologyMap_id]

theorem homology_restriction_injective (C : ChainComplex (Rep ℚ G) ℕ)
    (V : Rep.{0} ℚ G) (n : ℕ) :
    Function.Injective (homologyMap (restriction H C V) n) := by
  intro x y h
  have he := congrArg (fun z => homologyMap (transfer H C V) n z) h
  have hx := congrArg (fun u => u x) (homology_restriction_transfer H C V n)
  have hy := congrArg (fun u => u y) (homology_restriction_transfer H C V n)
  exact hx.symm.trans (he.trans hy)

/-- This projector specifies the full-level summand of cover cochains. -/
def descentProjector (C : ChainComplex (Rep ℚ G) ℕ) (V : Rep.{0} ℚ G) :=
  transfer H C V ≫ restriction H C V

theorem descentProjector_idempotent (C : ChainComplex (Rep ℚ G) ℕ) (V : Rep.{0} ℚ G) :
    descentProjector H C V ≫ descentProjector H C V = descentProjector H C V := by
  unfold descentProjector
  rw [Category.assoc,← Category.assoc (restriction H C V),restriction_transfer,
    Category.id_comp]

omit [H.FiniteIndex] in
/-- Literal full-level cochains are exactly the image of actual restriction. -/
theorem restriction_range_iff (A V : Rep.{0} ℚ G)
    (f : Rep.res H.subtype A ⟶ Rep.res H.subtype V) :
    (∃ c : A ⟶ V, restrictHom H A V c = f) ↔
      ∀ g : G, ∀ x : A, f.hom (A.ρ g x) = V.ρ g (f.hom x) := by
  constructor
  · rintro ⟨c,rfl⟩ g x
    exact LinearMap.congr_fun (c.hom.isIntertwining' g) x
  · intro hf
    refine ⟨Rep.ofHom ⟨f.hom.toLinearMap,?_⟩,?_⟩
    · intro g
      exact LinearMap.ext (hf g)
    · rfl

/-- Finite-index averaging projects precisely onto full equivariance, not every cover cochain. -/
theorem transfer_fixed_iff (A V : Rep.{0} ℚ G)
    (f : Rep.res H.subtype A ⟶ Rep.res H.subtype V) :
    restrictHom H A V (transferHom H A V f) = f ↔
      ∀ g : G, ∀ x : A, f.hom (A.ρ g x) = V.ρ g (f.hom x) := by
  rw [← restriction_range_iff H A V f]
  constructor
  · exact fun h => ⟨transferHom H A V f,h⟩
  · rintro ⟨c,rfl⟩
    rw [restrict_transferHom]

omit [H.FiniteIndex] in
/-- Restriction commutes with actual geometric chain pullback. -/
theorem restriction_natural {C D : ChainComplex (Rep ℚ G) ℕ} (u : C ⟶ D)
    (V : Rep.{0} ℚ G) :
    homPullback u V ≫ restriction H C V = restriction H D V ≫
      homPullback (((Rep.resFunctor H.subtype).mapHomologicalComplex
        (ComplexShape.down ℕ)).map u) (Rep.res H.subtype V) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  rfl

/-- The genuine transfer also commutes with boundary and face restriction. -/
theorem transfer_natural {C D : ChainComplex (Rep ℚ G) ℕ} (u : C ⟶ D)
    (V : Rep.{0} ℚ G) :
    homPullback (((Rep.resFunctor H.subtype).mapHomologicalComplex
      (ComplexShape.down ℕ)).map u) (Rep.res H.subtype V) ≫ transfer H C V =
      transfer H D V ≫ homPullback u V := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  exact transferHom_precomp H (u.f n) f

end TernaryPoly.SymmetricSpaceBoundaryFullTransfer
