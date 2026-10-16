module

public import TernaryPeriodPolynomials.Topology.Rational.Relative.ExcisionAlgebra
public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.MayerVietorisExact
public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.SmallHomotopy
public import TernaryPeriodPolynomials.Topology.SingularLocal.Homology.Coinvariants
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

@[expose] public section


universe u v u' v'
noncomputable section
namespace TernaryPoly.SingularLocalExcision
open CategoryTheory Limits HomologicalComplex

/-- Any additive coefficient functor preserves a genuinely degreewise split singular sequence. -/
theorem map_degreewise_split_shortExact {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
    [Abelian C] [Abelian D] (F : C ⥤ D) [F.Additive]
    (S : ShortComplex (ChainComplex C ℕ))
    (hS : ∀ n, (S.map (eval C (ComplexShape.down ℕ) n)).Splitting) :
    (S.map (F.mapHomologicalComplex (ComplexShape.down ℕ))).ShortExact := by
  apply shortExact_of_degreewise_shortExact
  intro n
  exact ((hS n).map F).shortExact

/-- Mapping a signed biproduct square through an additive functor preserves its precise shape. -/
def mapSquareIso {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.Additive] {I U V S : C}
    (a : I ⟶ U) (b : I ⟶ V) (u : U ⟶ S) (v : V ⟶ S) (h : b ≫ v = a ≫ u) :
    (ShortComplex.mk (biprod.lift a (-b)) (biprod.desc u v)
      (by simp [biprod.lift_desc,Preadditive.neg_comp,h])).map F ≅
    ShortComplex.mk (biprod.lift (F.map a) (-(F.map b))) (biprod.desc (F.map u) (F.map v))
      (by rw [biprod.lift_desc,Preadditive.neg_comp,← F.map_comp,← F.map_comp,h]; simp) :=
  letI : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_preservesBiproducts F
  ShortComplex.isoMk (Iso.refl _) (F.mapBiprod U V) (Iso.refl _)
    (by
      change 𝟙 (F.obj I) ≫ biprod.lift (F.map a) (-F.map b) =
        F.map (biprod.lift a (-b)) ≫ (F.mapBiprod U V).hom
      rw [Category.id_comp, biprod.map_lift_mapBiprod, F.map_neg])
    (by
      change (F.mapBiprod U V).hom ≫ biprod.desc (F.map u) (F.map v) =
        F.map (biprod.desc u v) ≫ 𝟙 (F.obj S)
      rw [Category.comp_id, biprod.mapBiprod_hom_desc])

variable (G : Type) [Group G] (E : TopCat.{0}) [MulAction G E] [ContinuousConstSMul G E]
  (W : Rep.{0} ℚ G)

/-- The actual tensor-coinvariant functor on representation-valued singular chain complexes. -/
abbrev coefficients := ((Rep.coinvariantsTensor ℚ G).obj W).mapHomologicalComplex (ComplexShape.down ℕ)

variable [IsCancelSMul G E]

/-- Arbitrary rational coefficients preserve the actual equivariant small-chain homotopy equivalence. -/
def smallCoefficientHomotopyEquiv (𝒰 : SphereOddDegree.OpenCoverData E)
    (h𝒰 : EquivariantSingularSmall.InvariantCover G E 𝒰) :
    _root_.HomotopyEquiv ((coefficients G W).obj (EquivariantSingularSmall.smallComplex G E 𝒰 h𝒰))
      (SingularLocalHomology.coinvariantChains G E W) :=
  ((Rep.coinvariantsTensor ℚ G).obj W).mapHomotopyEquiv
    (EquivariantSingularSmall.smallHomotopyEquiv G E 𝒰 h𝒰)

/-- The coefficient homotopy equivalence retains the genuine small-chain inclusion as its forward map. -/
theorem smallCoefficientHomotopyEquiv_hom (𝒰 : SphereOddDegree.OpenCoverData E)
    (h𝒰 : EquivariantSingularSmall.InvariantCover G E 𝒰) :
    (smallCoefficientHomotopyEquiv G E W 𝒰 h𝒰).hom =
      (coefficients G W).map (EquivariantSingularSmall.smallInclusion G E 𝒰 h𝒰) := by
  change (coefficients G W).map (EquivariantSingularSmall.smallHomotopyEquiv G E 𝒰 h𝒰).hom = _
  rw [EquivariantSingularSmall.smallHomotopyEquiv_hom]

/-- The actual small-chain inclusion is a quasi-isomorphism with arbitrary coefficient representation. -/
theorem smallCoefficientInclusion_quasiIso (𝒰 : SphereOddDegree.OpenCoverData E)
    (h𝒰 : EquivariantSingularSmall.InvariantCover G E 𝒰) :
    QuasiIso ((coefficients G W).map (EquivariantSingularSmall.smallInclusion G E 𝒰 h𝒰)) := by
  rw [← smallCoefficientHomotopyEquiv_hom]
  infer_instance

end TernaryPoly.SingularLocalExcision
