module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Homology.Boundary

@[expose] public section

noncomputable section
namespace TernaryPoly.SingularLocalHomology
open CategoryTheory FreeActionLinearization CoveringSingularOrbits
open scoped Classical

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  [IsCancelSMul G E] (p : E ⟶ B) (hp : IsQuotientCoveringMap p G) (V : Rep.{0} ℚ G)

/-- The genuine transported-face geometric boundary squares to zero, because the proved
actual degreewise identification intertwines it with the singular chain differential. -/
theorem boundary_squared (n : ℕ) :
    (boundary p hp V n).comp (boundary p hp V (n+1)) = 0 := by
  apply LinearMap.ext
  intro c
  apply (degreeEquiv p hp V n).symm.injective
  change (degreeEquiv p hp V n).symm (boundary p hp V n (boundary p hp V (n+1) c)) =
    (degreeEquiv p hp V n).symm 0
  rw [map_zero]
  have h₁ := LinearMap.congr_fun (degreeEquiv_symm_boundary p hp V n)
    (boundary p hp V (n+1) c)
  have h₂ := LinearMap.congr_fun (degreeEquiv_symm_boundary p hp V (n+1)) c
  have hz : (coinvariantChains G E V).d (n+1) n
      ((coinvariantChains G E V).d (n+2) (n+1) ((degreeEquiv p hp V (n+2)).symm c)) = 0 :=
    congrArg (fun f => f ((degreeEquiv p hp V (n+2)).symm c))
      ((coinvariantChains G E V).d_comp_d (n+2) (n+1) n)
  exact h₁.trans ((congrArg ((coinvariantChains G E V).d (n+1) n) h₂).trans hz)

/-- The genuine geometric singular chain complex: actual dependent finite sums of vertex-fiber
coefficients, with the alternating backwards-transported actual face differential. -/
def localChains : ChainComplex (ModuleCat ℚ) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of ℚ (VertexChain p hp V n))
    (fun n => ModuleCat.ofHom (boundary p hp V n)) (fun n => by
      apply ModuleCat.hom_ext
      exact boundary_squared p hp V n)

/-- A genuine chain isomorphism identifies the actual tensor-coinvariant complex and the
independently defined geometric finite-sum, transported-face complex. -/
def chainIso : coinvariantChains G E V ≅ localChains p hp V :=
  (HomologicalComplex.Hom.isoOfComponents
    (fun n => (degreeEquiv p hp V n).symm.toModuleIso) (fun i j hij => by
      obtain rfl : i = j+1 := hij.symm
      apply ModuleCat.hom_ext
      simp only [localChains, ChainComplex.of_d]
      exact (degreeEquiv_symm_boundary p hp V j).symm)).symm

/-- The chain isomorphism's degree map is the actual coefficient-fiber degree equivalence. -/
theorem chainIso_hom_f (n : ℕ) : (chainIso p hp V).hom.f n =
    (degreeEquiv p hp V n).toModuleIso.hom := rfl

/-- The inverse chain map sends an elementary local chain to its actual arbitrary-lift tensor. -/
theorem chainIso_inv_single (n : ℕ) {σ : SingularSimplex B n} (τ : Lifts p σ)
    (c : FiberCoefficient p hp V (atVertex σ)) :
    (chainIso p hp V).inv.f n (DFinsupp.single σ c) =
      generator G E V n τ.val (c.val (liftVertexEquiv p hp σ τ)) :=
  degreeEquiv_symm_single_lift p hp V n τ c

/-- The actual group homology comparison to genuine geometric local-coefficient singular homology. -/
def groupLocalHomologyIso [ContractibleSpace E] (n : ℕ) :
    groupHomology V n ≅ (localChains p hp V).homology n :=
  groupCoinvariantHomologyIso G E V n ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) n).mapIso (chainIso p hp V)

end TernaryPoly.SingularLocalHomology
