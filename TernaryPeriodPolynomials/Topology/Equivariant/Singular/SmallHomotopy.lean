module

public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.SmallGeometry
public import TernaryPeriodPolynomials.Topology.SingularHomology.SmallChainsQuasiIso
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective

@[expose] public section


noncomputable section
namespace TernaryPoly.EquivariantSingularSmall
open CategoryTheory HomologicalComplex FreeActionLinearization EquivariantSingularResolution
open SphereOddDegree

variable (G : Type) [Group G] (E : TopCat.{0}) [MulAction G E] [ContinuousConstSMul G E]
  (𝒰 : OpenCoverData E) (h𝒰 : InvariantCover G E 𝒰)

/-- The literal equivariant small-chain inclusion becomes a quasi-isomorphism after forgetting the action. -/
theorem forgetSmallInclusion_quasiIso :
    QuasiIso (((forget₂ (Rep ℚ G) (ModuleCat ℚ)).mapHomologicalComplex (ComplexShape.down ℕ)).map
      (smallInclusion G E 𝒰 h𝒰)) := by
  have h : QuasiIso ((forgetSmallIso G E 𝒰 h𝒰).hom ≫ smallChainsInclusion ℚ E 𝒰) := inferInstance
  rw [← forgetSmallInclusion G E 𝒰 h𝒰] at h
  exact quasiIso_of_comp_right (hφφ' := h)

/-- The scalar small-simplices theorem reflects to the actual representation-valued complexes. -/
instance smallInclusion_quasiIso : QuasiIso (smallInclusion G E 𝒰 h𝒰) := by
  apply (quasiIso_map_iff_of_preservesHomology (smallInclusion G E 𝒰 h𝒰)
    (forget₂ (Rep ℚ G) (ModuleCat ℚ))).mp
  exact forgetSmallInclusion_quasiIso G E 𝒰 h𝒰

variable [IsCancelSMul G E]

/-- Projectivity of actual small and full singular-chain degrees upgrades the actual inclusion
quasi-isomorphism to an equivariant homotopy equivalence, without contractibility of E. -/
theorem exists_smallInclusion_homotopyEquiv :
    ∃ e : _root_.HomotopyEquiv (smallComplex G E 𝒰 h𝒰) (equivariantChains G E),
      e.hom = smallInclusion G E 𝒰 h𝒰 := by
  have : ∀ n, Projective ((equivariantChains G E).X n) := fun n => chainRep_projective G E n
  have : ∀ n, Projective ((smallComplex G E 𝒰 h𝒰).X n) := fun n => smallComplex_projective G E 𝒰 h𝒰 n
  exact (ChainComplex.quasiIso_iff_of_projective (smallInclusion G E 𝒰 h𝒰)).mp inferInstance

/-- An actual equivariant small-chain homotopy equivalence whose forward map is the literal inclusion. -/
def smallHomotopyEquiv :
    _root_.HomotopyEquiv (smallComplex G E 𝒰 h𝒰) (equivariantChains G E) :=
  Classical.choose (exists_smallInclusion_homotopyEquiv G E 𝒰 h𝒰)

/-- The chosen homotopy equivalence retains exactly the genuine small-chain inclusion. -/
theorem smallHomotopyEquiv_hom :
    (smallHomotopyEquiv G E 𝒰 h𝒰).hom = smallInclusion G E 𝒰 h𝒰 :=
  Classical.choose_spec (exists_smallInclusion_homotopyEquiv G E 𝒰 h𝒰)

end TernaryPoly.EquivariantSingularSmall
