module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Section.Fibers

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalSection
open CategoryTheory CoveringSingularOrbits SingularLocalCoefficient SingularLocalConstant

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E]
    (p : E ⟶ B) (hp : IsQuotientCoveringMap p G) (s : B ⟶ E) (hs : s ≫ p = 𝟙 B)
    (V : Rep.{0} ℚ G)

/-- Actual section evaluation identifies local cochains with constant cochains on the same simplices. -/
def cochainDegreeEquiv (n : ℕ) : VertexCochain p hp V n ≃ₗ[ℚ]
    VertexCochain (𝟙 B) (identityCover B) (constantRep (ModuleCat.of ℚ V)) n :=
  LinearEquiv.piCongrRight (fun σ => constantFiberEquiv p hp s hs V (atVertex σ))

/-- Section trivialization intertwines the genuine transported-face cochain differential. -/
theorem cochainDegreeEquiv_d (n : ℕ) (φ : VertexCochain p hp V n) :
    cochainDegreeEquiv p hp s hs V (n+1) (differential p hp V n φ) =
      differential (𝟙 B) (identityCover B) (constantRep (ModuleCat.of ℚ V)) n
        (cochainDegreeEquiv p hp s hs V n φ) := by
  funext σ
  change constantFiberEquiv p hp s hs V (atVertex σ) (differential p hp V n φ σ) = _
  erw [differential_apply,differential_apply,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_zsmul]
  exact congrArg (fun c => (-1 : ℤ)^i.val • c)
    (constantFiberEquiv_transport p hp s hs V (simplexPullPath (simplexCoface n i) σ) _)

variable [ContinuousConstSMul G E]

/-- The section gives a genuine isomorphism of geometric cochain complexes. -/
def cochainIso : localCochains p hp V ≅
    localCochains (𝟙 B) (identityCover B) (constantRep (ModuleCat.of ℚ V)) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (cochainDegreeEquiv p hp s hs V n).toModuleIso) (fun i j hij => by
      obtain rfl : j = i+1 := hij.symm
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro φ
      simp only [localCochains, CochainComplex.of_d]
      exact (cochainDegreeEquiv_d p hp s hs V i φ).symm)

/-- The actual cochain isomorphism retains the fiberwise evaluation formula. -/
theorem cochainIso_hom_f (n : ℕ) : (cochainIso p hp s hs V).hom.f n =
    (cochainDegreeEquiv p hp s hs V n).toModuleIso.hom := rfl

end TernaryPoly.SingularLocalSection
