module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FullInducedBarMap
public import TernaryPeriodPolynomials.Topology.Singular.CoverNaturalityRestrictionAugmentation

@[expose] public section

noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryFull
open CategoryTheory HomologicalComplex Representation EquivariantSingularSmall SingularCoverRestriction

variable {G : Type} [Group G]

/-- The canonical identity-induction Shapiro isomorphism on the literal induced bar complex. -/
def inducedBarShapiro (S : Subgroup G) (W : Rep.{0} ℚ G) :
    homCochains (inducedBarComplex S) W ≅
      homCochains (Rep.barResolution ℚ S).complex (Rep.res S.subtype W) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun _ => (Rep.indResHomEquiv S.subtype _ W).toModuleIso) (fun _ _ _ => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      apply Rep.hom_ext
      apply IntertwiningMap.ext
      apply LinearMap.ext
      intro b
      rfl)

theorem inducedBarShapiro_apply (S : Subgroup G) (W : Rep.{0} ℚ G) (n : ℕ)
    (c : (inducedBarComplex S).X n ⟶ W) (b : (Rep.barResolution ℚ S).complex.X n) :
    ((inducedBarShapiro S W).hom.f n c).hom b =
      c.hom (IndV.mk S.subtype ((Rep.barResolution ℚ S).complex.X n).ρ 1 b) := rfl

/-- Canonical induced incidence becomes literal cochain restriction under identity evaluation. -/
theorem inducedBarShapiro_natural (S T : Subgroup G) (hST : S ≤ T) (W : Rep.{0} ℚ G) :
    homPullback (inducedBarMap S T hST) W ≫ (inducedBarShapiro S W).hom =
    (inducedBarShapiro T W).hom ≫ barHomMap (Subgroup.inclusion hST) (Rep.res T.subtype W) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  change (inducedBarShapiro S W).hom.f n ((inducedBarMap S T hST).f n ≫ c) =
    (barHomMap (Subgroup.inclusion hST) (Rep.res T.subtype W)).f n
      ((inducedBarShapiro T W).hom.f n c)
  refine Eq.trans ?_ (barHomMap_apply (Subgroup.inclusion hST) (Rep.res T.subtype W) n
    ((inducedBarShapiro T W).hom.f n c)).symm
  apply Rep.hom_ext
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro b
  change c.hom ((inducedBarDegree S T hST n).hom (IndV.mk _ _ 1 b)) =
    c.hom (IndV.mk _ _ 1 ((subgroupBarDegree S T hST n).hom b))
  rw [inducedBarDegree_mk]

/-- The literal subgroup bar map preserves its complete augmentation. -/
theorem subgroupBarDegree_augmentation (S T : Subgroup G) (hST : S ≤ T)
    (b : (Rep.barResolution ℚ S).complex.X 0) :
    ((Rep.barResolution ℚ T).π.f 0).hom ((subgroupBarDegree S T hST 0).hom b) =
      ((Rep.barResolution ℚ S).π.f 0).hom b :=
  congrArg (fun f => f.hom b) (barDegreeMap_augmentation (Subgroup.inclusion hST))

/-- The full label augmentation retains the ambient coset and scalar bar augmentation. -/
theorem fullParabolicAt_augmentation {X : Type} [MulAction G X] (a : X)
    (ha : ∀ x : X, ∃ g : G, g • a = x) (S : Subgroup G)
    (hs : MulAction.stabilizer G a = S) (g : G)
    (b : (Rep.barResolution ℚ S).complex.X 0) :
    ((fullParabolicResolutionAt G a ha S hs).π.f 0).hom
      (IndV.mk S.subtype ((Rep.barResolution ℚ S).complex.X 0).ρ g b) =
    MonoidAlgebra.single (g⁻¹ • a) ((barAugmentation (G := S)).hom b) := by
  change (fullInducedLabelIso G a ha S hs).hom.hom
    (((Rep.indFunctor ℚ S.subtype).mapProjectiveResolution (Rep.barResolution ℚ S)).π.f 0
      (IndV.mk S.subtype ((Rep.barResolution ℚ S).complex.X 0).ρ g b)) = _
  change (fullInducedLabelIso G a ha S hs).hom.hom
    ((Rep.indMap S.subtype ((Rep.barResolution ℚ S).π.f 0)).hom
      (IndV.mk S.subtype ((Rep.barResolution ℚ S).complex.X 0).ρ g b)) = _
  change (fullInducedLabelIso G a ha S hs).hom.hom
    (IndV.mk S.subtype (Representation.trivial ℚ S ℚ) g
      ((barAugmentation (G := S)).hom b)) = _
  cases hs
  change (fullOrbitLabelIso G a ha).hom.hom
    (BoundaryFaceResolutionComparison.inducedOrbitLinear G a
      (IndV.mk (MulAction.stabilizer G a).subtype (Representation.trivial ℚ _ ℚ) g
        ((barAugmentation (G := MulAction.stabilizer G a)).hom b))) = _
  rw [BoundaryFaceResolutionComparison.inducedOrbitLinear_mk]
  exact SingularComponentAugmentation.permutationMap_single (fullOrbitEquiv G a ha)
    (fun _ _ => rfl) (BoundaryFaceResolutionComparison.orbitPoint G a g⁻¹) _

end TernaryPoly.SymmetricSpaceBoundaryFull
