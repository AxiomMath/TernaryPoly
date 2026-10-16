module

public import TernaryPeriodPolynomials.Topology.Singular.ComponentAugmentationScalar
public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.ResolutionExactness
public import Mathlib.Algebra.Homology.SingleHomology

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularComponentAugmentation
open Topology CategoryTheory Limits AlgebraicTopology HomologicalComplex
open EquivariantSingularResolution FreeActionLinearization
open scoped MonoidAlgebra Simplicial

variable {ι : Type} (E : ι → Type) [∀ i,TopologicalSpace (E i)]
  [∀ i,ContractibleSpace (E i)] [TopologicalSpace ι] [DiscreteTopology ι]
variable (G : Type) [Group G] [MulAction G ι] [MulAction G (Total E)]
  [ContinuousConstSMul G (Total E)]
  (hlabel : ∀ (g : G) (x : Total E),(g • x).1=g • x.1)

include hlabel in
omit [∀ i,ContractibleSpace (E i)] [TopologicalSpace ι] [DiscreteTopology ι] in
theorem zeroSimplexLabel_smul (g : G) (simplex : SingularSimplex (TopCat.of (Total E)) 0) :
    (TopCat.toSSetObj₀Equiv (g • simplex)).1=g • (TopCat.toSSetObj₀Equiv simplex).1 := by
  have h := congrArg (fun f : C(Convexity.StdSimplex ℝ (Fin 1),Total E) => (f default).1)
    (singularEquiv_smul G (TopCat.of (Total E)) 0 g simplex)
  exact h.trans (hlabel g ((TopCat.toSSetObjEquiv _ _ simplex) default))

def labelActionMap (g : G) : ModuleCat.of ℚ ℚ[ι] ⟶ ModuleCat.of ℚ ℚ[ι] :=
  ModuleCat.ofHom (Representation.ofMulAction ℚ G ι g)

omit [TopologicalSpace ι] [DiscreteTopology ι] in
theorem single_labelActionMap (g : G) (i : ι) :
    ModuleCat.ofHom (MonoidAlgebra.lsingle i) ≫ labelActionMap (ι := ι) G g =
      ModuleCat.ofHom (MonoidAlgebra.lsingle (g • i)) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  exact Representation.ofMulAction_single g i r

include hlabel in
/-- The literal component augmentation commutes with the actual arithmetic action. -/
theorem scalarAction_augmentation (g : G) :
    (scalarChainMap G (TopCat.of (Total E)) g).f 0 ≫ scalarAugmentation E =
      scalarAugmentation E ≫ labelActionMap (ι := ι) G g := by
  apply (TopCat.toSSet.obj (TopCat.of (Total E))).chainComplex_hom_ext
  intro simplex
  have ha := (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ scalarAugmentation E)
      (generator_smul G (TopCat.of (Total E)) 0 simplex g)).trans
        (generator_scalarAugmentation E (g • simplex)))
  have hb := (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ labelActionMap (ι := ι) G g)
      (generator_scalarAugmentation E simplex)).trans (single_labelActionMap G g _))
  exact ha.trans ((congrArg (fun i : ι => ModuleCat.ofHom (MonoidAlgebra.lsingle (R := ℚ) (S := ℚ) i))
    (zeroSimplexLabel_smul E G hlabel g simplex)).trans hb.symm)

def augmentation : chainRep G (TopCat.of (Total E)) 0 ⟶ Rep.ofMulAction ℚ G ι :=
  Rep.ofHom ⟨(scalarAugmentation E).hom,fun g =>
    congrArg ModuleCat.Hom.hom (scalarAction_augmentation E G hlabel g)⟩

theorem augmentation_single (simplex : SingularSimplex (TopCat.of (Total E)) 0) (r : ℚ) :
    augmentation E G hlabel (degreeLinearEquiv (TopCat.of (Total E)) 0 (MonoidAlgebra.single simplex r))=
      MonoidAlgebra.single (TopCat.toSSetObj₀Equiv simplex).1 r :=
  scalarAugmentation_single E simplex r

theorem d_augmentation : equivariantD G (TopCat.of (Total E)) 1 0 ≫ augmentation E G hlabel=0 := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  exact congrArg ModuleCat.Hom.hom (d_scalarAugmentation E)

def augmentationChain : equivariantChains G (TopCat.of (Total E)) ⟶
    (ChainComplex.single₀ (Rep ℚ G)).obj (Rep.ofMulAction ℚ G ι) :=
  (ChainComplex.toSingle₀Equiv _ _).symm ⟨augmentation E G hlabel,d_augmentation E G hlabel⟩

@[simp] theorem augmentationChain_f_zero : (augmentationChain E G hlabel).f 0=augmentation E G hlabel :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

theorem augmented_exact : (ShortComplex.mk _ _ (d_augmentation E G hlabel)).Exact := by
  apply (ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep ℚ G) (ModuleCat ℚ))).mp
  exact scalar_augmented_exact E

instance augmentation_epi : Epi (augmentation E G hlabel) :=
  (forget₂ (Rep ℚ G) (ModuleCat ℚ)).epi_of_epi_map (scalarAugmentation_epi E)

omit [MulAction G ι] in
theorem equivariant_exactAt (n : ℕ) (hn : n≠0) :
    (equivariantChains G (TopCat.of (Total E))).ExactAt n := by
  rw [HomologicalComplex.exactAt_iff]
  apply (ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep ℚ G) (ModuleCat ℚ))).mp
  exact scalar_exactAt E n hn

instance augmentationChain_quasiIso : QuasiIso (augmentationChain E G hlabel) := by
  constructor
  intro n
  cases n with
  | zero =>
    rw [ChainComplex.quasiIsoAt₀_iff,ShortComplex.quasiIso_iff_of_zeros']
    · exact ⟨augmented_exact E G hlabel,augmentation_epi E G hlabel⟩
    all_goals rfl
  | succ n =>
    rw [quasiIsoAt_iff_exactAt']
    · exact equivariant_exactAt E G (n+1) (Nat.succ_ne_zero n)
    · exact ChainComplex.exactAt_succ_single_obj _ _

omit [MulAction G ι] in
theorem positive_equivariant_homology_isZero (n : ℕ) (hn : n≠0) :
    IsZero ((equivariantChains G (TopCat.of (Total E))).homology n) :=
  (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp (equivariant_exactAt E G n hn)

/-- H0 is the actual label permutation representation via the induced literal augmentation. -/
def homologyZeroIso : (equivariantChains G (TopCat.of (Total E))).homology 0 ≅ Rep.ofMulAction ℚ G ι :=
  asIso (homologyMap (augmentationChain E G hlabel) 0) ≪≫
    singleObjHomologySelfIso (ComplexShape.down ℕ) 0 (Rep.ofMulAction ℚ G ι)

/-- Free action on the total face space, not an equivariant contraction of its components,
gives an actual projective resolution of the component permutation module. -/
def projectiveResolution [IsCancelSMul G (Total E)] : ProjectiveResolution (Rep.ofMulAction ℚ G ι) where
  complex := equivariantChains G (TopCat.of (Total E))
  projective n := chainRep_projective G (TopCat.of (Total E)) n
  π := augmentationChain E G hlabel
  quasiIso := augmentationChain_quasiIso E G hlabel

end TernaryPoly.SingularComponentAugmentation
