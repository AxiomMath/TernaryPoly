module

public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.MayerVietorisCochains
public import Mathlib.Algebra.Homology.HomologySequence

@[expose] public section


noncomputable section
namespace TernaryPoly.EquivariantSingularMayerVietoris
open CategoryTheory HomologicalComplex EquivariantSingularSmall TopologicalSpace

variable (G : Type) [Group G] (E : TopCat.{0}) [MulAction G E] [ContinuousConstSMul G E]
  (U V : Opens E) (hU : InvariantSet G E (U : Set E)) (hV : InvariantSet G E (V : Set E))
  (hUV : U ⊔ V = ⊤) (W : Rep.{0} ℚ G)

/-- Actual connecting map from intersection cohomology to small cohomology. -/
def connecting (n : ℕ) :
    (homCochains (interChains G E U V hU hV) W).homology n ⟶
      (homCochains (coverChains G E U V hU hV hUV) W).homology (n+1) :=
  (cochainShortExact G E U V hU hV hUV W).δ n (n+1) rfl

/-- The genuine connecting map followed by restriction vanishes. -/
theorem connecting_comp (n : ℕ) :
    connecting G E U V hU hV hUV W n ≫
      homologyMap (homPullback (rightMap G E U V hU hV hUV) W) (n+1) = 0 :=
  (cochainShortExact G E U V hU hV hUV W).δ_comp n (n+1) rfl

/-- The genuine difference restriction followed by the connecting map vanishes. -/
theorem comp_connecting (n : ℕ) :
    homologyMap (homPullback (leftMap G E U V hU hV) W) n ≫
      connecting G E U V hU hV hUV W n = 0 :=
  (cochainShortExact G E U V hU hV hUV W).comp_δ n (n+1) rfl

/-- Mayer–Vietoris is exact at the actual small cohomology term. -/
theorem cohomology_exact_small (n : ℕ) :
    (ShortComplex.mk _ _ (connecting_comp G E U V hU hV hUV W n)).Exact :=
  (cochainShortExact G E U V hU hV hUV W).homology_exact₁ n (n+1) rfl

/-- Mayer–Vietoris is exact at the actual Hom cohomology of the two open pieces. -/
theorem cohomology_exact_sum (n : ℕ) :
    ((cochainShortComplex G E U V hU hV hUV W).map
      (homologyFunctor (ModuleCat ℚ) (ComplexShape.up ℕ) n)).Exact :=
  (cochainShortExact G E U V hU hV hUV W).homology_exact₂ n

/-- Mayer–Vietoris is exact at the actual intersection cohomology term. -/
theorem cohomology_exact_inter (n : ℕ) :
    (ShortComplex.mk _ _ (comp_connecting G E U V hU hV hUV W n)).Exact :=
  (cochainShortExact G E U V hU hV hUV W).homology_exact₃ n (n+1) rfl

/-- The actual small-chain comparison turns the connecting map into ambient singular cohomology. -/
def ambientConnecting [IsCancelSMul G E] (n : ℕ) :
    (homCochains (interChains G E U V hU hV) W).homology n ⟶
      (EquivariantSingularCohomology.cochains G E W).homology (n+1) :=
  connecting G E U V hU hV hUV W n ≫
    (smallCohomologyIso G E (SphereOddDegree.twoSetCover U V hUV)
      (twoSetCover_invariant G E U V hU hV hUV) W (n+1)).inv

end TernaryPoly.EquivariantSingularMayerVietoris
