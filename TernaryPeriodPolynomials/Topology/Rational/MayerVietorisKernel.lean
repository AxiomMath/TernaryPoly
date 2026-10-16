module

/-
The signed-MV kernel argument follows akopjan/HamSandwich (Apache-2.0),
SphereHomologyS1BaseMV.lean. Rewritten for explicit rational ModuleCat maps,
arbitrary two-open covers, and the actual point-induced augmentation.
-/
public import TernaryPeriodPolynomials.Topology.Rational.SubspaceAugmentation

@[expose] public section


noncomputable section
namespace TernaryPoly.RationalMayerVietoris
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open SphereOddDegree SphereOddDegree.AffineBarycentricSubdivision
open RationalSingularAugmentation ContractibleSingularHomology

/-- Homology classes of a direct sum are detected by the literal two projections. -/
theorem biprod_homology_zero_iff {A B : ChainComplex (ModuleCat.{0} ℚ) ℕ} (n : ℕ)
    (y : (A ⊞ B).homology n) :
    y = 0 ↔ (homologyMap (biprod.fst : A ⊞ B ⟶ A) n).hom y = 0 ∧
      (homologyMap (biprod.snd : A ⊞ B ⟶ B) n).hom y = 0 := by
  constructor
  · rintro rfl; simp
  · rintro ⟨h₁,h₂⟩
    have h := congrArg (fun f => homologyMap f n)
      (biprod.total (X := A) (Y := B))
    simp only [homologyMap_add, homologyMap_comp, homologyMap_id] at h
    have hy := congrArg (fun f => f.hom y) h
    change (homologyMap (biprod.inl : A ⟶ A ⊞ B) n).hom
        ((homologyMap (biprod.fst : A ⊞ B ⟶ A) n).hom y) +
      (homologyMap (biprod.inr : B ⟶ A ⊞ B) n).hom
        ((homologyMap (biprod.snd : A ⊞ B ⟶ B) n).hom y) = y at hy
    rw [h₁,h₂,map_zero,map_zero,add_zero] at hy
    exact hy.symm

variable {X : Type} [TopologicalSpace X] (U V : Opens X) (hUV : U ⊔ V = ⊤)

/-- The actual signed Mayer–Vietoris left homomorphism on H0, with explicit carriers. -/
abbrev leftMapZero (_hUV : U ⊔ V = ⊤) :
    (subChainComplex ℚ (TopCat.of X) ((U : Set X) ∩ (V : Set X))).homology 0 ⟶
      (subChainComplex ℚ (TopCat.of X) (U : Set X) ⊞
        subChainComplex ℚ (TopCat.of X) (V : Set X)).homology 0 :=
  homologyMap (biprod.lift (mvInclUV_U ℚ (X := TopCat.of X) U V)
    (-(mvInclUV_V ℚ (X := TopCat.of X) U V))) 0

/-- The first projection is the literal overlap-to-U map. -/
theorem left_comp_fst :
    leftMapZero U V hUV ≫ homologyMap biprod.fst 0 =
      homologyMap (mvInclUV_U ℚ (X := TopCat.of X) U V) 0 := by
  change homologyMap _ 0 ≫ _ = _
  rw [← homologyMap_comp]
  exact congrArg (fun f => homologyMap f 0) (biprod.lift_fst _ _)

/-- The second projection is minus the literal overlap-to-V map. -/
theorem left_comp_snd :
    leftMapZero U V hUV ≫ homologyMap biprod.snd 0 =
      -homologyMap (mvInclUV_V ℚ (X := TopCat.of X) U V) 0 := by
  change homologyMap _ 0 ≫ _ = _
  rw [← homologyMap_comp]
  exact (congrArg (fun f => homologyMap f 0) (biprod.lift_snd _ _)).trans
    (homologyMap_neg _ _)

/-- The actual MV H0 kernel is exactly the kernel of overlap augmentation. -/
theorem kernel_leftMapZero_eq [ContractibleSpace U] [ContractibleSpace V] :
    LinearMap.ker (leftMapZero U V hUV).hom =
      LinearMap.ker (supportedAugmentation X ((U : Set X) ∩ (V : Set X))).hom := by
  have hU := supportedAugmentation_naturality X ((U : Set X) ∩ (V : Set X)) U
    Set.inter_subset_left
  have hV := supportedAugmentation_naturality X ((U : Set X) ∩ (V : Set X)) V
    Set.inter_subset_right
  have hfst := left_comp_fst U V hUV
  have hsnd := left_comp_snd U V hUV
  have injU : Function.Injective (supportedAugmentation X (U : Set X)).hom :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  have injV : Function.Injective (supportedAugmentation X (V : Set X)).hom :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  ext x
  change (leftMapZero U V hUV).hom x = 0 ↔
    (supportedAugmentation X ((U : Set X) ∩ (V : Set X))).hom x = 0
  have eU := congrArg (fun f => f.hom x) hU
  have eV := congrArg (fun f => f.hom x) hV
  have eF := congrArg (fun f => f.hom x) hfst
  have eS := congrArg (fun f => f.hom x) hsnd
  change (supportedAugmentation X (U : Set X)).hom
    ((homologyMap (mvInclUV_U ℚ (X := TopCat.of X) U V) 0).hom x) = _ at eU
  change (supportedAugmentation X (V : Set X)).hom
    ((homologyMap (mvInclUV_V ℚ (X := TopCat.of X) U V) 0).hom x) = _ at eV
  change (homologyMap (biprod.fst :
    subChainComplex ℚ (TopCat.of X) (U : Set X) ⊞ subChainComplex ℚ (TopCat.of X) (V : Set X) ⟶ _) 0).hom ((leftMapZero U V hUV).hom x) =
    (homologyMap (mvInclUV_U ℚ (X := TopCat.of X) U V) 0).hom x at eF
  change (homologyMap (biprod.snd :
    subChainComplex ℚ (TopCat.of X) (U : Set X) ⊞ subChainComplex ℚ (TopCat.of X) (V : Set X) ⟶ _) 0).hom ((leftMapZero U V hUV).hom x) =
    -(homologyMap (mvInclUV_V ℚ (X := TopCat.of X) U V) 0).hom x at eS
  constructor
  · intro hx
    rw [← eU, ← eF, hx, map_zero, map_zero]
  · intro hx
    apply (biprod_homology_zero_iff 0 _).mpr
    constructor
    · rw [eF]
      apply injU
      rw [map_zero, eU, hx]
    · rw [eS, neg_eq_zero]
      apply injV
      rw [map_zero, eV, hx]

/-- The categorical kernels of the actual maps identify. -/
def kernel_leftMapZero_iso [ContractibleSpace U] [ContractibleSpace V] :
    kernel (leftMapZero U V hUV) ≅
      kernel (supportedAugmentation X ((U : Set X) ∩ (V : Set X))) :=
  ModuleCat.kernelIsoKer _ ≪≫
    eqToIso (congrArg (fun S : Submodule ℚ ((subChainComplex ℚ (TopCat.of X)
      ((U : Set X) ∩ (V : Set X))).homology 0) => ModuleCat.of ℚ S)
        (kernel_leftMapZero_eq U V hUV)) ≪≫
    (ModuleCat.kernelIsoKer _).symm

end TernaryPoly.RationalMayerVietoris
