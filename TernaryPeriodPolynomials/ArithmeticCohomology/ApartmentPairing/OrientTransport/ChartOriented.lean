module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.OrientTransport.ChartPair
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.OrientTransport.ThomScale

@[expose] public section


/-!
# The staircase constant `d₅` and oriented chains

`d5` is the class of the staircase product cell `stair` in `H₅(ℝ⁵, ℝ⁵ ∖ Nset)` read against the library's compact generator
`G = compactGenerator 3 Nset` (rank one: `compact_class_smul`).  A chain of `ℝ⁵` with boundary off `Nset` whose class at the
origin is the library local generator has class exactly `G` (`relCls_eq_G`).

Formalized by Claude Sonnet 5.5.
-/

open SphereOddDegree SphereOddDegree.AlexanderWhitney SphereOddDegree.AffineBarycentricSubdivision
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open TernaryPeriodPolynomials.Argument.Lemma33.Locality
open TernaryPeriodPolynomials.Argument.Lemma33.Orient
open TernaryPoly TernaryPoly.EuclideanLocalHomology TernaryPoly.ContractibleSingularHomology
  TernaryPoly.RationalRelativeSingular TernaryPoly.RationalManifoldCompact TernaryPoly.EuclideanCompactClasses
  TernaryPoly.RationalLocalOrientation TernaryPoly.EuclideanOrientationScalar
open TernaryPoly.SingularLocalCap.Descent TernaryPoly.SingularLocalCap

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport

local notation "X5" => TopCat.of (EuclideanSpace ℝ (Fin 5))

/-- The library compact generator of `H₅(ℝ⁵, ℝ⁵ ∖ Nset)`. -/
def Gen : (supportChains (Nset : Set (EuclideanSpace ℝ (Fin (3 + 2))))).homology (3 + 2) :=
  compactGenerator 3 Nset isCompact_Nset

/-- The class of the staircase product cell against the compact generator. -/
def d5 : ℚ :=
  Classical.choose (compact_class_smul 3 Nset isCompact_Nset convex_Nset ⟨0, zero_mem_Nset⟩
    (relCls stair (relCls_mem_of_sup stair_boundary_mem)))

theorem relCls_stair_eq :
    relCls stair (relCls_mem_of_sup stair_boundary_mem) = d5 • Gen :=
  Classical.choose_spec (compact_class_smul 3 Nset isCompact_Nset convex_Nset ⟨0, zero_mem_Nset⟩
    (relCls stair (relCls_mem_of_sup stair_boundary_mem)))

/-- **A chain whose class at the origin is the library local generator has class `Gen`.**  The group
`H₅(ℝ⁵, ℝ⁵ ∖ Nset)` has rank one, and the point restriction to the origin is injective on it. -/
theorem relCls_eq_Gen (c : singularChainGroup ℚ X5 (3 + 2))
    (h : (singularBoundary ℚ X5 (3 + 2 - 1)).hom c ∈ subChainSubmodule ℚ X5 (Nset : Set X5)ᶜ (3 + 2 - 1))
    (hpt : homologyMap (supportPointMap (Nset : Set (EuclideanSpace ℝ (Fin 5))) 0 zero_mem_Nset) (3 + 2)
      (relCls c h) = localGenerator 3 0) :
    relCls c h = Gen := by
  obtain ⟨q, hq⟩ := compact_class_smul 3 Nset isCompact_Nset convex_Nset ⟨0, zero_mem_Nset⟩ (relCls c h)
  have hG : homologyMap (supportPointMap (Nset : Set (EuclideanSpace ℝ (Fin 5))) 0 zero_mem_Nset) (3 + 2)
      (compactGenerator 3 Nset isCompact_Nset) = localGenerator 3 0 :=
    compactGenerator_at_point 3 Nset isCompact_Nset 0 zero_mem_Nset
  rw [hq, map_smul, hG] at hpt
  have h1 : q • localGenerator 3 0 = (1 : ℚ) • localGenerator 3 0 := by rw [one_smul]; exact hpt
  have hq1 : q = 1 := smul_left_injective ℚ (localGenerator_ne_zero 3 0) h1
  rw [hq, hq1, one_smul]
  rfl

variable {y₀ : (chains R3).X 3 →ₗ[ℚ] ℚ} {θ₀ : (chains R2).X 2 →ₗ[ℚ] ℚ}

/-- **The oriented chart-level value.**  If `F_# cc` has class the library generator at the origin, then
`d₅ · ⟨y₀ ∘ (π F)_#, θ₀ ∘ (ρ F)_#⟩(cc) = lamPos · lam2`. -/
theorem chart_pair_oriented (H : ThomPair y₀ θ₀) {X : TopCat.{0}} (F : X ⟶ X5)
    (cc : singularChainGroup ℚ X (3 + 2))
    (hcc : (singularBoundary ℚ X 4).hom cc ∈
      subChainSubmodule ℚ X (F.hom ⁻¹' UA) 4 ⊔ subChainSubmodule ℚ X (F.hom ⁻¹' UB) 4)
    (hpt : homologyMap (supportPointMap (Nset : Set (EuclideanSpace ℝ (Fin 5))) 0 zero_mem_Nset) (3 + 2)
      (relCls ((singularChainMap ℚ F (3 + 2)).hom cc)
        (relCls_mem_of_sup (push_boundary_mem F cc hcc))) = localGenerator 3 0) :
    d5 * capPairF X (ModuleCat.of ℚ ℚ) 2 3 ((yE y₀).comp (singularChainMap ℚ F 3).hom)
      ((thE θ₀).comp (singularChainMap ℚ F 2).hom) cc = lamPos * lam2 := by
  have hG := relCls_eq_Gen _ _ hpt
  have := chart_pair_value H F cc hcc d5 1 (by rw [hG, relCls_stair_eq, one_smul])
  rw [one_mul] at this
  exact this

end TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport
