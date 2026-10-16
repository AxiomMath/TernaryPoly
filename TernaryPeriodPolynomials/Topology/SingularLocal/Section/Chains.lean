module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Section.Fibers
public import TernaryPeriodPolynomials.Topology.SingularLocal.Constant.Comparison

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalSection
open CategoryTheory Limits CoveringSingularOrbits SingularLocalCoefficient SingularLocalHomology
open SingularLocalConstant FreeActionLinearization
open scoped Classical

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E]
    (p : E ⟶ B) (hp : IsQuotientCoveringMap p G) (s : B ⟶ E) (hs : s ≫ p = 𝟙 B)
    (V : Rep.{0} ℚ G)

/-- Section evaluation identifies actual finite local chains with values on the same simplices. -/
def chainValueEquiv (n : ℕ) : VertexChain p hp V n ≃ₗ[ℚ] (SingularSimplex B n →₀ V) :=
  DFinsupp.mapRange.linearEquiv (fun σ => sectionEvaluation p hp s hs V (atVertex σ)) ≪≫ₗ
    (finsuppLequivDFinsupp ℚ).symm

/-- A singleton retains its actual simplex and section-evaluated coefficient. -/
theorem chainValueEquiv_single (n : ℕ) (σ : SingularSimplex B n)
    (c : FiberCoefficient p hp V (atVertex σ)) :
    chainValueEquiv p hp s hs V n (DFinsupp.single σ c) =
      Finsupp.single σ (sectionEvaluation p hp s hs V (atVertex σ) c) := by
  change (DFinsupp.mapRange (fun τ => sectionEvaluation p hp s hs V (atVertex τ)) (fun τ => map_zero _)
    (DFinsupp.single σ c)).toFinsupp = _
  rw [DFinsupp.mapRange_single,DFinsupp.toFinsupp_single]

/-- Section evaluation identifies geometric local chains with actual ordinary singular chains. -/
def ordinaryDegreeEquiv (n : ℕ) : (VertexChain p hp V n) ≃ₗ[ℚ]
    (ordinaryChains B (ModuleCat.of ℚ V)).X n :=
  chainValueEquiv p hp s hs V n ≪≫ₗ (ordinaryFinsuppIso B (ModuleCat.of ℚ V) n).symm.toLinearEquiv

/-- The ordinary comparison preserves literal singular generators and section values. -/
theorem ordinaryDegreeEquiv_single (n : ℕ) (σ : SingularSimplex B n)
    (c : FiberCoefficient p hp V (atVertex σ)) :
    ordinaryDegreeEquiv p hp s hs V n (DFinsupp.single σ c) =
      ((TopCat.toSSet.obj B).ιChainComplex (R := ModuleCat.of ℚ V) σ)
        (sectionEvaluation p hp s hs V (atVertex σ) c) := by
  exact (congrArg (ordinaryFinsuppIso B (ModuleCat.of ℚ V) n).inv
    (chainValueEquiv_single p hp s hs V n σ c)).trans
      (ordinaryFinsuppIso_inv_single B (ModuleCat.of ℚ V) n σ _)

/-- Actual backwards-transported local boundary becomes the ordinary singular boundary. -/
theorem ordinaryDegreeEquiv_boundary_single (n : ℕ) (σ : SingularSimplex B (n+1))
    (c : FiberCoefficient p hp V (atVertex σ)) :
    ordinaryDegreeEquiv p hp s hs V n (boundary p hp V n (DFinsupp.single σ c)) =
      (ordinaryChains B (ModuleCat.of ℚ V)).d (n+1) n
        (ordinaryDegreeEquiv p hp s hs V (n+1) (DFinsupp.single σ c)) := by
  rw [ordinaryDegreeEquiv_single,ordinary_boundary_generator,boundary_single,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_zsmul,ordinaryDegreeEquiv_single,sectionEvaluation_transport]
  rfl

/-- The literal degreewise comparison intertwines both differentials. -/
theorem ordinaryDegreeEquiv_boundary (n : ℕ) :
    (ordinaryDegreeEquiv p hp s hs V n).toLinearMap.comp (boundary p hp V n) =
      ((ordinaryChains B (ModuleCat.of ℚ V)).d (n+1) n).hom.comp
        (ordinaryDegreeEquiv p hp s hs V (n+1)).toLinearMap := by
  apply DFinsupp.lhom_ext
  exact ordinaryDegreeEquiv_boundary_single p hp s hs V n

variable [ContinuousConstSMul G E] [IsCancelSMul G E]

/-- The section induces a genuine isomorphism to ordinary singular chains. -/
def ordinaryChainIso : localChains p hp V ≅ ordinaryChains B (ModuleCat.of ℚ V) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (ordinaryDegreeEquiv p hp s hs V n).toModuleIso) (fun i j hij => by
      obtain rfl : i = j+1 := hij.symm
      apply ModuleCat.hom_ext
      simp only [localChains,ChainComplex.of_d]
      exact (ordinaryDegreeEquiv_boundary p hp s hs V j).symm)

/-- The genuine local-chain comparison to identity-cover constant coefficients. -/
def chainIso : localChains p hp V ≅ SingularLocalConstant.chains B (ModuleCat.of ℚ V) :=
  ordinaryChainIso p hp s hs V ≪≫ (SingularLocalConstant.ordinaryChainIso B (ModuleCat.of ℚ V)).symm

/-- Under the actual ordinary-chain comparison, section trivialization has its literal degree map. -/
theorem chainIso_hom_ordinary_apply (n : ℕ) (c : (localChains p hp V).X n) :
    SingularLocalConstant.chainDegreeEquiv B (ModuleCat.of ℚ V) n ((chainIso p hp s hs V).hom.f n c) =
      ordinaryDegreeEquiv p hp s hs V n c := by
  exact (SingularLocalConstant.chainDegreeEquiv B (ModuleCat.of ℚ V) n).apply_symm_apply _

end TernaryPoly.SingularLocalSection
