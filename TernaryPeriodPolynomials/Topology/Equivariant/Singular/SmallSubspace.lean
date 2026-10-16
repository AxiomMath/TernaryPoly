module

public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.SmallGeometry
public import TernaryPeriodPolynomials.Topology.SingularHomology.SubChainSubspaceBridge
public import TernaryPeriodPolynomials.Topology.Singular.CoverNaturalityChains

@[expose] public section


noncomputable section
namespace TernaryPoly.EquivariantSingularSmall
open CategoryTheory HomologicalComplex EquivariantSingularResolution SingularCoverNaturality
open SphereOddDegree SphereOddDegree.AffineBarycentricSubdivision

variable (G : Type) [Group G] (E : TopCat.{0}) [MulAction G E] [ContinuousConstSMul G E]
  (S : Set E)

/-- The canonical action on a genuinely invariant subspace. -/
instance invariantSubtypeAction [hS : Fact (InvariantSet G E S)] : MulAction G S where
  smul g x := ⟨g • x.val,hS.out g x.val x.property⟩
  one_smul x := Subtype.ext (one_smul G x.val)
  mul_smul g h x := Subtype.ext (mul_smul g h x.val)

/-- The canonical invariant-subspace action is continuous. -/
instance invariantSubtypeContinuous [Fact (InvariantSet G E S)] : ContinuousConstSMul G S where
  continuous_const_smul g :=
    ((continuous_const_smul g).comp continuous_subtype_val).subtype_mk _

/-- Freeness of the ambient action passes to the actual invariant subspace. -/
instance invariantSubtypeFree [Fact (InvariantSet G E S)] [IsCancelSMul G E] : IsCancelSMul G S where
  right_cancel' g h x he := (inferInstance : IsCancelSMul G E).right_cancel' g h x.val
    (congrArg Subtype.val he)

variable [MulAction G S] [ContinuousConstSMul G S]
  (hS : InvariantSet G E S) (hinc : ∀ (g : G) (x : S), (g • x).val = g • x.val)

/-- The scalar subspace corestriction is equivariant for the actual subspace inclusion. -/
def subspaceCorestrictDegree (n : ℕ) :
    (equivariantChains G (TopCat.of S)).X n ⟶ (subordinateComplex G E S hS).X n :=
  Rep.ofHom ⟨((subChainCorestrict ℚ E S).f n).hom, fun g => by
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    exact congrArg (fun m => (m.f n).hom c)
      (underlyingMap_equivariant (sInclusion S) hinc g)⟩

/-- Actual singular chains of the subspace map into its literal subordinate-chain complex. -/
def subspaceCorestrict : equivariantChains G (TopCat.of S) ⟶ subordinateComplex G E S hS where
  f := subspaceCorestrictDegree G E S hS hinc
  comm' i j hij := by
    obtain rfl : i = j+1 := hij.symm
    ext c
    apply Subtype.ext
    simp only [subordinateComplex, familyComplex, ChainComplex.of_d]
    have h := congrArg (fun m => (m.hom c).val) ((subChainCorestrict ℚ E S).comm (j+1) j)
    simp only [subChainComplex_d] at h
    exact h

/-- The actual equivariant subspace corestriction is an isomorphism in each degree. -/
instance subspaceCorestrictDegree_isIso (n : ℕ) : IsIso (subspaceCorestrictDegree G E S hS hinc n) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr (subChainCorestrict_bijective S n)

/-- The actual equivariant subspace corestriction is a chain isomorphism. -/
instance subspaceCorestrict_isIso : IsIso (subspaceCorestrict G E S hS hinc) := by
  have : ∀ n, IsIso ((subspaceCorestrict G E S hS hinc).f n) :=
    fun n => subspaceCorestrictDegree_isIso G E S hS hinc n
  exact HomologicalComplex.Hom.isIso_of_components _

/-- Actual subspace chains and actual subordinate chains are equivariantly isomorphic. -/
def subspaceIso : equivariantChains G (TopCat.of S) ≅ subordinateComplex G E S hS :=
  asIso (subspaceCorestrict G E S hS hinc)

/-- The subspace comparison commutes with the literal ambient inclusion, already on chains. -/
theorem subspaceCorestrict_inclusion :
    subspaceCorestrict G E S hS hinc ≫ subordinateInclusion G E S hS =
      chainMap (sInclusion S) hinc := by
  apply HomologicalComplex.hom_ext
  intro n
  ext c
  rfl

end TernaryPoly.EquivariantSingularSmall
