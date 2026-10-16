module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapMVHomologyMaps
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.MVSmallEpi

@[expose] public section

noncomputable section
namespace TernaryPoly.SingularLocalCompactCapMV
open CategoryTheory Limits HomologicalComplex
open SingularLocalHomology SingularLocalExcision EquivariantSingularSmall EquivariantSingularMayerVietoris

/-- Any rational coefficient representation preserves the degreewise injection of genuine
small scalar chains, because the inclusion has an actual equivariant graded retraction. -/
instance coefficientSmallInclusion_mono (G : Type) [Group G] (E : TopCat.{0})
    [MulAction G E] [ContinuousConstSMul G E] (V : Rep.{0} ℚ G)
    (𝒰 : SphereOddDegree.OpenCoverData E) (h𝒰 : InvariantCover G E 𝒰) :
    Mono ((coefficients G V).map (smallInclusion G E 𝒰 h𝒰)) := by
  apply mono_of_mono_f
  intro n
  let F := (Rep.coinvariantsTensor ℚ G).obj V
  change Mono (F.map ((smallInclusion G E 𝒰 h𝒰).f n))
  apply mono_of_mono_fac (g := F.map ((smallInclusion G E 𝒰 h𝒰).f n))
    (f := F.map (SingularLocalCompactMV.smallGradedRetraction E G 𝒰 h𝒰 n)) (h := 𝟙 _)
  rw [← F.map_comp,SingularLocalCompactMV.smallInclusion_gradedRetraction,F.map_id]

/-- The actual small-to-geometric chain comparison is degreewise injective. -/
instance smallToLocal_mono {G : Type} [Group G] {E B : TopCat.{0}}
    [MulAction G E] [ContinuousConstSMul G E] (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)]
    (V : Rep.{0} ℚ G) (U D : TopologicalSpace.Opens B) (hUD : U ⊔ D = ⊤) [IsCancelSMul G E] :
    Mono (smallToLocal p V U D hUD) := by
  have h := coefficientSmallInclusion_mono G E V
    (SphereOddDegree.twoSetCover (preimageOpen p U) (preimageOpen p D) (preimageOpen_cover p U D hUD))
    (twoSetCover_invariant G E _ _ (preimage_invariant p U) (preimage_invariant p D)
      (preimageOpen_cover p U D hUD))
  unfold smallToLocal
  exact @mono_comp _ _ _ _ _ _ h _ inferInstance

end TernaryPoly.SingularLocalCompactCapMV
