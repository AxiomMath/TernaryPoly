module

public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.ResolutionAugmentation
public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.ResolutionProjective
public import TernaryPeriodPolynomials.Topology.ContractibleSingularHomology
public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

@[expose] public section


noncomputable section
open CategoryTheory Limits AlgebraicTopology
namespace TernaryPoly.EquivariantSingularResolution

variable (G : Type) [Group G] (X : TopCat.{0}) [MulAction G X] [ContinuousConstSMul G X]

/-- The coefficient sum on the actual singular connected components. -/
def componentSum :
    (∐ fun _ : SSet.π₀ (TopCat.toSSet.obj X) => ModuleCat.of ℚ ℚ) ⟶ ModuleCat.of ℚ ℚ :=
  Sigma.desc (fun _ => 𝟙 _)

/-- Contractibility makes the actual sum over connected components an isomorphism. -/
instance componentSum_isIso [ContractibleSpace X] : IsIso (componentSum X) := by
  have h : IsIso (((TopCat.toSSet.obj X).homology₀Iso (ModuleCat.of ℚ ℚ)).hom ≫
      componentSum X) :=
    inferInstanceAs (IsIso (ContractibleSingularHomology.homologyZeroIso (X := X)).hom)
  exact IsIso.of_isIso_comp_left
    (((TopCat.toSSet.obj X).homology₀Iso (ModuleCat.of ℚ ℚ)).hom) (componentSum X)

/-- The literal coefficient-sum augmentation is the cokernel of the actual first boundary. -/
def augmentationIsCokernel [ContractibleSpace X] :
    IsColimit (CokernelCofork.ofπ (augmentationModule X) (d_augmentation X)) :=
  (SSet.isColimitCokernelCoforkChainComplexDOneZero
    (TopCat.toSSet.obj X) (ModuleCat.of ℚ ℚ)).ofIsoColimit
      (Cofork.ext (asIso (componentSum X)) (augmentationModule_eq_components X).symm)

/-- Exactness of the literal augmented underlying singular complex. -/
theorem underlying_augmented_exact [ContractibleSpace X] :
    (ShortComplex.mk _ _ (d_augmentation X)).Exact :=
  ShortComplex.exact_of_g_is_cokernel _ (augmentationIsCokernel X)

/-- Surjectivity of the literal coefficient-sum augmentation. -/
instance augmentationModule_epi [ContractibleSpace X] : Epi (augmentationModule X) :=
  epi_of_isColimit_cofork (augmentationIsCokernel X)

/-- Exactness of the actual augmented singular representation complex. -/
theorem augmented_exact [ContractibleSpace X] :
    (ShortComplex.mk _ _ (equivariantD_augmentation G X)).Exact := by
  apply (ShortComplex.exact_map_iff_of_faithful _
    (forget₂ (Rep ℚ G) (ModuleCat ℚ))).mp
  exact underlying_augmented_exact X

/-- The actual equivariant augmentation is an epimorphism. -/
instance augmentation_epi [ContractibleSpace X] : Epi (augmentation G X) :=
  (forget₂ (Rep ℚ G) (ModuleCat ℚ)).epi_of_epi_map (augmentationModule_epi X)

/-- The actual equivariant singular complex is exact in positive degree. -/
theorem equivariantChains_exactAt [ContractibleSpace X] (n : ℕ) (hn : n ≠ 0) :
    (equivariantChains G X).ExactAt n := by
  rw [HomologicalComplex.exactAt_iff]
  apply (ShortComplex.exact_map_iff_of_faithful _
    (forget₂ (Rep ℚ G) (ModuleCat ℚ))).mp
  exact (ContractibleSingularHomology.chains_exactAt (X := X) n hn)

/-- The literal augmentation is a quasi-isomorphism. -/
instance augmentationChain_quasiIso [ContractibleSpace X] :
    QuasiIso (augmentationChain G X) := by
  constructor
  intro n
  cases n with
  | zero =>
    rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
    · exact ⟨augmented_exact G X, augmentation_epi G X⟩
    all_goals rfl
  | succ n =>
    rw [quasiIsoAt_iff_exactAt']
    · exact equivariantChains_exactAt G X (n+1) (Nat.succ_ne_zero n)
    · exact ChainComplex.exactAt_succ_single_obj _ _

/-- The actual singular chains form a projective resolution of the trivial representation. -/
def projectiveResolution [ContractibleSpace X] [IsCancelSMul G X] :
    ProjectiveResolution (Rep.trivial ℚ G ℚ) where
  complex := equivariantChains G X
  projective n := chainRep_projective G X n
  π := augmentationChain G X
  quasiIso := augmentationChain_quasiIso G X

end TernaryPoly.EquivariantSingularResolution
