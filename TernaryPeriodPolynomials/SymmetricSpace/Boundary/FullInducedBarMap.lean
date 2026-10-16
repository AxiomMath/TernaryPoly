module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FullParabolicModels
public import TernaryPeriodPolynomials.Topology.Singular.CoverNaturalityRestrictionBar

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryFull
open CategoryTheory HomologicalComplex Representation SingularCoverRestriction

variable {G : Type} [Group G] (S T : Subgroup G) (hST : S ≤ T)

abbrev inducedBarComplex (S : Subgroup G) :=
  ((Rep.indFunctor ℚ S.subtype).mapHomologicalComplex (ComplexShape.down ℕ)).obj (Rep.barResolution ℚ S).complex

/-- The actual induction unit on each stabilizer bar module. -/
def barInductionUnit (S : Subgroup G) (n : ℕ) :
    (Rep.barResolution ℚ S).complex.X n ⟶
      Rep.res S.subtype ((inducedBarComplex S).X n) :=
  (Rep.indResHomEquiv S.subtype _ _).toFun (𝟙 _)

/-- Subgroup bar map in the exact projective-resolution coordinates. -/
def subgroupBarDegree (n : ℕ) : (Rep.barResolution ℚ S).complex.X n ⟶
    Rep.res (Subgroup.inclusion hST) ((Rep.barResolution ℚ T).complex.X n) :=
  (barMap (Subgroup.inclusion hST)).f n

theorem subgroupBarDegree_comm (i j : ℕ) :
    subgroupBarDegree S T hST i ≫ Rep.resMap (Subgroup.inclusion hST)
      ((Rep.barResolution ℚ T).complex.d i j) =
    (Rep.barResolution ℚ S).complex.d i j ≫ subgroupBarDegree S T hST j :=
  (barMap (Subgroup.inclusion hST)).comm i j

/-- Literal inclusion of one induced stabilizer bar module in another. -/
def inducedBarDegree (n : ℕ) : (inducedBarComplex S).X n ⟶ (inducedBarComplex T).X n :=
  (Rep.indResHomEquiv S.subtype _ _).symm
    (subgroupBarDegree S T hST n ≫
      Rep.resMap (Subgroup.inclusion hST) (barInductionUnit T n))

/-- The genuine subgroup map keeps the ambient induction coordinate exactly. -/
theorem inducedBarDegree_mk (n : ℕ) (g : G) (b : (Rep.barResolution ℚ S).complex.X n) :
    (inducedBarDegree S T hST n).hom
      (IndV.mk S.subtype ((Rep.barResolution ℚ S).complex.X n).ρ g b) =
    IndV.mk T.subtype ((Rep.barResolution ℚ T).complex.X n).ρ g
      ((subgroupBarDegree S T hST n).hom b) := by
  have h := (Rep.indResHomEquiv S.subtype _ _).apply_symm_apply
    (subgroupBarDegree S T hST n ≫
      Rep.resMap (Subgroup.inclusion hST) (barInductionUnit T n))
  have h₁ := congrArg (fun f => f.hom b) h
  change (inducedBarDegree S T hST n).hom (IndV.mk _ _ 1 b) =
    IndV.mk _ _ 1 ((subgroupBarDegree S T hST n).hom b) at h₁
  have h₂ := Rep.hom_comm_apply (inducedBarDegree S T hST n) g⁻¹ (IndV.mk _ _ 1 b)
  change (inducedBarDegree S T hST n).hom
    (Representation.ind _ _ g⁻¹ (IndV.mk _ _ 1 b)) =
    Representation.ind _ _ g⁻¹ ((inducedBarDegree S T hST n).hom (IndV.mk _ _ 1 b)) at h₂
  simpa only [h₁,Representation.ind_mk,inv_inv,one_mul] using h₂

/-- Induction acts on the bar differential without changing its induction coordinate. -/
theorem inducedBar_d_mk (S : Subgroup G) (i j : ℕ) (g : G)
    (b : (Rep.barResolution ℚ S).complex.X i) :
    ((inducedBarComplex S).d i j).hom
      (IndV.mk S.subtype ((Rep.barResolution ℚ S).complex.X i).ρ g b) =
    IndV.mk S.subtype ((Rep.barResolution ℚ S).complex.X j).ρ g
      (((Rep.barResolution ℚ S).complex.d i j).hom b) := rfl

/-- Canonical actual induced bar chain map for an inclusion of full parabolics. -/
def inducedBarMap : inducedBarComplex S ⟶ inducedBarComplex T where
  f := inducedBarDegree S T hST
  comm' i j _ := by
    apply Rep.hom_ext
    apply IntertwiningMap.ext
    apply IndV.hom_ext
    intro g
    apply LinearMap.ext
    intro b
    change ((inducedBarComplex T).d i j).hom ((inducedBarDegree S T hST i).hom (IndV.mk _ _ g b)) =
      (inducedBarDegree S T hST j).hom (((inducedBarComplex S).d i j).hom (IndV.mk _ _ g b))
    rw [inducedBarDegree_mk,inducedBar_d_mk,inducedBar_d_mk,inducedBarDegree_mk]
    exact congrArg (fun x => IndV.mk T.subtype ((Rep.barResolution ℚ T).complex.X j).ρ g x)
      (congrArg (fun m => m.hom b) (subgroupBarDegree_comm S T hST i j))

end TernaryPoly.SymmetricSpaceBoundaryFull
