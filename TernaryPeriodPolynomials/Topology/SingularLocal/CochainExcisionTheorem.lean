module

public import TernaryPeriodPolynomials.Topology.SingularLocal.CochainExcisionMaps
public import TernaryPeriodPolynomials.Topology.Singular.CochainExcisionAlgebra
public import TernaryPeriodPolynomials.Topology.Singular.CochainKernelComparison

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCochainExcision
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open EquivariantSingularSmall EquivariantSingularMayerVietoris SingularLocalCoefficient SingularLocalSupport

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G)
  (A D : Opens B) (hAD : A ⊔ D = ⊤)

/-- The genuine relative comparison from ambient cochains to small cochains. -/
def toSmallKernel : relativeCochains p V (A : Set B) ⟶ kernel (smallLeft p V A D hAD) :=
  kernel.map _ _ (localToSmall p A D hAD V) (𝟙 _) (by
    rw [Category.comp_id]
    exact (localToSmall_left p V A D hAD).symm)

/-- The actual relative small-cochain comparison is a quasi-isomorphism. -/
instance toSmallKernel_quasiIso : QuasiIso (toSmallKernel p V A D hAD) := by
  unfold toSmallKernel
  exact CochainExcisionAlgebra.kernel_map_quasiIso (localRestriction p A V)
    (smallLeft p V A D hAD) (localToSmall p A D hAD V) (𝟙 _) _

/-- Actual right restriction from the relative small-cochain kernel to the neighborhood pair. -/
def fromSmallKernel : kernel (smallLeft p V A D hAD) ⟶
    neighborhoodCochains p V (A : Set B) (D : Set B) :=
  kernel.map _ _ (smallRight p V A D hAD)
    (nestedLocalRestriction p ((A : Set B) ∩ (D : Set B)) A Set.inter_subset_left V)
    (small_square p V A D hAD).symm

/-- The genuine signed small-cochain sequence identifies the relative small and neighborhood kernels. -/
instance fromSmallKernel_isIso : IsIso (fromSmallKernel p V A D hAD) := by
  apply CochainExcisionAlgebra.kernel_map_isIso_of_shortExact
    (smallLeft p V A D hAD) (smallRight p V A D hAD) _ _ (small_square p V A D hAD)
  have hf : biprod.lift (smallLeft p V A D hAD) (smallRight p V A D hAD) =
      (localSmallSequence p A D hAD V).f := by
    apply biprod.hom_ext
    · erw [biprod.lift_fst]; rfl
    · erw [biprod.lift_snd]; rfl
  have hg := localSmallSequence_g p A D hAD V
  have hs := localSmallSequence_shortExact p A D hAD V
  convert hs using 1; first | (simp only [hf,← hg]; rfl)

/-- The two kernel maps compose to the literal geometric relative cochain restriction. -/
theorem cochainExcisionMap_factorization :
    cochainExcisionMap p V (A : Set B) (D : Set B) =
      toSmallKernel p V A D hAD ≫ fromSmallKernel p V A D hAD := by
  apply (cancel_mono (kernel.ι
    (nestedLocalRestriction p ((A : Set B) ∩ (D : Set B)) D Set.inter_subset_right V))).mp
  rw [cochainExcisionMap_inclusion,Category.assoc]
  change _ = toSmallKernel p V A D hAD ≫
    (kernel.lift _ _ _ ≫ kernel.ι _)
  rw [kernel.lift_ι,← Category.assoc]
  change _ = (kernel.lift _ _ _ ≫ kernel.ι _) ≫ smallRight p V A D hAD
  rw [kernel.lift_ι,Category.assoc,localToSmall_right]

include hAD in
/-- Genuine excision on relative local cochains for every open cover, with arbitrary rational coefficients. -/
theorem cochainExcisionMap_quasiIso : QuasiIso (cochainExcisionMap p V (A : Set B) (D : Set B)) := by
  rw [cochainExcisionMap_factorization p V A D hAD]
  infer_instance

/-- The actual cochain excision map induces an isomorphism in every cohomological degree. -/
def cochainExcisionIso (k : ℕ) :
    (relativeCochains p V (A : Set B)).homology k ≅
      (neighborhoodCochains p V (A : Set B) (D : Set B)).homology k := by
  have := cochainExcisionMap_quasiIso p V A D hAD
  exact asIso (homologyMap (cochainExcisionMap p V (A : Set B) (D : Set B)) k)

end TernaryPoly.SingularLocalCochainExcision
