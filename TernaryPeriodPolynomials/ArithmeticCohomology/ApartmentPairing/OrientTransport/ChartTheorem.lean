module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.OrientTransport.ChartClass

@[expose] public section


/-!
# The chart-level value of the Thom pairing

For a chain `c` of `ℝ⁵` whose boundary lies over `UA` and `UB`, the pairing of the two pulled-back Thom cochains is determined
by the class of `c` in `H₅(ℝ⁵, ℝ⁵ ∖ Nset)`: if `d₅ · [c] = q · [stair]` there, then
`d₅ · Pair c = q · (lamPos · lam2)`.

Formalized by Claude Sonnet 5.5.
-/

open SphereOddDegree SphereOddDegree.AlexanderWhitney SphereOddDegree.AffineBarycentricSubdivision
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open TernaryPeriodPolynomials.Argument.Lemma33.Locality
open TernaryPeriodPolynomials.Argument.Lemma33.Orient
open TernaryPoly TernaryPoly.EuclideanLocalHomology TernaryPoly.ContractibleSingularHomology
  TernaryPoly.RationalRelativeSingular TernaryPoly.RationalManifoldCompact
open TernaryPoly.SingularLocalCap.Descent

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport

local notation "X5" => TopCat.of (EuclideanSpace ℝ (Fin 5))

theorem sup_le_compl (n : ℕ) :
    subChainSubmodule ℚ X5 UA n ⊔ subChainSubmodule ℚ X5 UB n ≤ subChainSubmodule ℚ X5 (Nset : Set X5)ᶜ n := by
  rw [Nset_compl]
  exact sup_le (subChainSubmodule_mono Set.subset_union_left n) (subChainSubmodule_mono Set.subset_union_right n)

theorem relCls_mem_of_sup {c : singularChainGroup ℚ X5 (3 + 2)}
    (h : (singularBoundary ℚ X5 4).hom c ∈ subChainSubmodule ℚ X5 UA 4 ⊔ subChainSubmodule ℚ X5 UB 4) :
    (singularBoundary ℚ X5 (3 + 2 - 1)).hom c ∈ subChainSubmodule ℚ X5 (Nset : Set X5)ᶜ (3 + 2 - 1) :=
  sup_le_compl 4 h

variable {y₀ : (chains R3).X 3 →ₗ[ℚ] ℚ} {θ₀ : (chains R2).X 2 →ₗ[ℚ] ℚ}

/-- **The chart-level value of the Thom pairing.**  If `d₅ · [c] = q · [stair]` in `H₅(ℝ⁵, ℝ⁵ ∖ Nset)`, for chains with
boundary over `UA ∪ UB` split as a sum of a `UA`-chain and a `UB`-chain, then `d₅ · Pair c = q · lamPos · lam2`. -/
theorem chart_value (H : ThomPair y₀ θ₀) (c : singularChainGroup ℚ X5 (3 + 2))
    (hc : (singularBoundary ℚ X5 4).hom c ∈ subChainSubmodule ℚ X5 UA 4 ⊔ subChainSubmodule ℚ X5 UB 4)
    (d5 q : ℚ)
    (e : d5 • relCls c (relCls_mem_of_sup hc) = q • relCls stair (relCls_mem_of_sup stair_boundary_mem)) :
    d5 * Pair y₀ θ₀ c = q * (lamPos * lam2) := by
  have e' : relCls (d5 • c) (boundary_smul_mem d5 c (relCls_mem_of_sup hc)) =
      relCls (q • stair) (boundary_smul_mem q stair (relCls_mem_of_sup stair_boundary_mem)) := by
    rw [relCls_smul, relCls_smul]; exact e
  obtain ⟨w, hw, u, hu⟩ := exists_decomp_of_relCls_eq _ _ _ _ e'
  have hbw : (singularBoundary ℚ X5 4).hom w ∈
      subChainSubmodule ℚ X5 UA 4 ⊔ subChainSubmodule ℚ X5 UB 4 := by
    have h1 : (singularBoundary ℚ X5 4).hom (d5 • c) = (singularBoundary ℚ X5 4).hom (q • stair) +
        (singularBoundary ℚ X5 4).hom w + (singularBoundary ℚ X5 4).hom ((singularBoundary ℚ X5 (3 + 2)).hom u) := by
      rw [← map_add, ← map_add]
      exact congrArg _ hu
    rw [show (singularBoundary ℚ X5 4).hom ((singularBoundary ℚ X5 (3 + 2)).hom u) = 0 from
      singularBoundary_boundary_zero ℚ X5 4 u, add_zero] at h1
    have h2 : (singularBoundary ℚ X5 4).hom w =
        d5 • (singularBoundary ℚ X5 4).hom c - q • (singularBoundary ℚ X5 4).hom stair := by
      rw [← map_smul, ← map_smul, h1]; abel
    rw [h2]
    exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hc) (Submodule.smul_mem _ _ stair_boundary_mem)
  have hw' : w ∈ subChainSubmodule ℚ X5 ((UA : Set X5) ∪ (UB : Set X5)) (4 + 1) := by
    have := hw
    rw [Nset_compl] at this
    exact this
  obtain ⟨wU, hwU, wV, hwV, u', hu'⟩ := triad_decomp (X := X5) (UA : Set X5) (UB : Set X5) isOpen_UA isOpen_UB 4 w hw' hbw
  have hPw : Pair y₀ θ₀ w = 0 := by
    rw [hu', map_add, map_add]
    have h1 : Pair y₀ θ₀ wU = 0 := Pair_UA H hwU
    have h2 : Pair y₀ θ₀ wV = 0 := Pair_UB H hwV
    have h3 : Pair y₀ θ₀ ((singularBoundary ℚ X5 (2 + 3)).hom u') = 0 := Pair_boundary H u'
    rw [h1, h2, zero_add, zero_add]
    exact h3
  have h4 := congrArg (Pair y₀ θ₀) hu
  have h5 : Pair y₀ θ₀ ((singularBoundary ℚ X5 (3 + 2)).hom u) = 0 := Pair_boundary H u
  rw [map_add, map_add, hPw, h5, map_smul, map_smul, Pair_stair H] at h4
  simpa using h4

end TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport
