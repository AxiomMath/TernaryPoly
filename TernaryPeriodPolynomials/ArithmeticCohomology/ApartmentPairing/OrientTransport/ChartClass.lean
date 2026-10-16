module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.OrientTransport.Staircase
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.OrientTransport.TriadDecomp
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.PDRep
public import TernaryPeriodPolynomials.Topology.Euclidean.OrientationScalar

@[expose] public section


open SphereOddDegree SphereOddDegree.AlexanderWhitney SphereOddDegree.AffineBarycentricSubdivision
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open TernaryPeriodPolynomials.Argument.Lemma33.Locality
open TernaryPoly TernaryPoly.EuclideanLocalHomology TernaryPoly.ContractibleSingularHomology
  TernaryPoly.RationalRelativeSingular TernaryPoly.RationalManifoldCompact
open TernaryPoly.SingularLocalCap.Descent

/-!
# Relative classes of chains with boundary in the complement of the compact box

For a chain `c` of `ℝ⁵` whose boundary lies in the chains supported off the compact box `Nset`,
`relCls c` is its class in the support homology `H₅(ℝ⁵, ℝ⁵ ∖ Nset)`.  Equality of two such classes
yields a decomposition `c = c' + w + ∂u` with `w` supported off `Nset`, which is what the
triad decomposition needs to transfer the pairing value from one chain to another.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport

local notation "E5" => EuclideanSpace ℝ (Fin 5)
local notation "X5" => TopCat.of (EuclideanSpace ℝ (Fin 5))

theorem isCompact_Nset : IsCompact Nset := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · have h1 : IsClosed {x : E5 | ‖piE x‖ ≤ 1 / 4} := isClosed_le (continuous_norm.comp piE_cont) continuous_const
    have h2 : IsClosed {x : E5 | ‖rhoE x‖ ≤ 1 / 4} := isClosed_le (continuous_norm.comp rhoE_cont) continuous_const
    exact h1.inter h2
  · refine (Metric.isBounded_closedBall (x := (0 : E5)) (r := 1)).subset ?_
    intro x hx
    obtain ⟨h1, h2⟩ := hx
    have e1 : ‖piE x‖ ^ 2 ≤ (1 / 4) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    have e2 : ‖rhoE x‖ ^ 2 ≤ (1 / 4) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
    rw [norm_piE_sq] at e1
    rw [norm_rhoE_sq] at e2
    have : ‖x‖ ^ 2 ≤ 1 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp [Fin.sum_univ_five]
      nlinarith
    rw [Metric.mem_closedBall, dist_zero_right]
    nlinarith [norm_nonneg x]

theorem convex_Nset : Convex ℝ Nset := by
  have h1 : Convex ℝ {x : E5 | ‖piE x‖ ≤ 1 / 4} := by
    have := (convex_closedBall (0 : R3) (1 / 4)).linear_preimage piE
    simpa [Metric.closedBall, dist_zero_right] using this
  have h2 : Convex ℝ {x : E5 | ‖rhoE x‖ ≤ 1 / 4} := by
    have := (convex_closedBall (0 : R2) (1 / 4)).linear_preimage rhoE
    simpa [Metric.closedBall, dist_zero_right] using this
  exact h1.inter h2

theorem zero_mem_Nset : (0 : E5) ∈ Nset := by
  simp [Nset]

/-- A chain lies over `S` iff its image in the relative chains modulo `S` vanishes. -/
theorem proj_eq_zero_iff (S : Set X5) (n : ℕ) (x : singularChainGroup ℚ X5 n) :
    (cokernel.π (RationalRelativeSingular.inclusion S)).f n x = 0 ↔ x ∈ subChainSubmodule ℚ X5 S n := by
  constructor
  · intro h0
    obtain ⟨b, hb⟩ := (SingularLocalCap.RelativeAlgebra.projection_zero_iff
      (RationalRelativeSingular.inclusion S) n _).mp h0
    rw [← hb]
    exact singularChainMap_sInclusion_mem _ _ b
  · intro hx
    obtain ⟨y, hy⟩ := (subChainCorestrict_bijective (R := ℚ) S n).2 ⟨x, hx⟩
    exact (SingularLocalCap.RelativeAlgebra.projection_zero_iff
      (RationalRelativeSingular.inclusion S) n _).mpr ⟨y, congrArg Subtype.val hy⟩

theorem proj_cycle (c : singularChainGroup ℚ X5 (3 + 2))
    (h : (singularBoundary ℚ X5 (3 + 2 - 1)).hom c ∈ subChainSubmodule ℚ X5 Nsetᶜ (3 + 2 - 1)) :
    (supportChains Nset).d (3 + 2) (3 + 2 - 1)
      ((cokernel.π (RationalRelativeSingular.inclusion (Nset : Set X5)ᶜ)).f (3 + 2) c) = 0 := by
  have hd := ConcreteCategory.congr_hom
    ((cokernel.π (RationalRelativeSingular.inclusion (Nset : Set X5)ᶜ)).comm (3 + 2) (3 + 2 - 1)) c
  have h0 : (cokernel.π (RationalRelativeSingular.inclusion (Nset : Set X5)ᶜ)).f (3 + 2 - 1)
      ((singularBoundary ℚ X5 (3 + 2 - 1)).hom c) = 0 := (proj_eq_zero_iff _ _ _).mpr h
  exact hd.trans h0

/-- The class, in the top local homology of `ℝ⁵` along `Nset`, of a chain whose boundary lies over `Nsetᶜ`. -/
def relCls (c : singularChainGroup ℚ X5 (3 + 2))
    (h : (singularBoundary ℚ X5 (3 + 2 - 1)).hom c ∈ subChainSubmodule ℚ X5 Nsetᶜ (3 + 2 - 1)) :
    (supportChains Nset).homology (3 + 2) :=
  chainClass (supportChains Nset) (3 + 2)
    ⟨(cokernel.π (RationalRelativeSingular.inclusion (Nset : Set X5)ᶜ)).f (3 + 2) c, proj_cycle c h⟩

theorem exists_decomp_of_relCls_eq (c c' : singularChainGroup ℚ X5 (3 + 2))
    (h : (singularBoundary ℚ X5 (3 + 2 - 1)).hom c ∈ subChainSubmodule ℚ X5 Nsetᶜ (3 + 2 - 1))
    (h' : (singularBoundary ℚ X5 (3 + 2 - 1)).hom c' ∈ subChainSubmodule ℚ X5 Nsetᶜ (3 + 2 - 1))
    (e : relCls c h = relCls c' h') :
    ∃ w ∈ subChainSubmodule ℚ X5 Nsetᶜ (3 + 2), ∃ u : singularChainGroup ℚ X5 (3 + 2 + 1),
      c = c' + w + (singularBoundary ℚ X5 (3 + 2)).hom u := by
  obtain ⟨b, hb⟩ := exists_boundary_of_chainClass_eq (supportChains Nset) (3 + 2) _ _ e
  obtain ⟨b', hb'⟩ := SingularLocalCap.RelativeAlgebra.projection_surjective
    (RationalRelativeSingular.inclusion (Nset : Set X5)ᶜ) (3 + 2 + 1) b
  refine ⟨c - c' - (singularBoundary ℚ X5 (3 + 2)).hom b', ?_, b', by abel⟩
  rw [← proj_eq_zero_iff]
  have hd := ConcreteCategory.congr_hom
    ((cokernel.π (RationalRelativeSingular.inclusion (Nset : Set X5)ᶜ)).comm (3 + 2 + 1) (3 + 2)) b'
  have hbd : (cokernel.π (RationalRelativeSingular.inclusion (Nset : Set X5)ᶜ)).f (3 + 2)
      ((singularBoundary ℚ X5 (3 + 2)).hom b') =
      (cokernel.π (RationalRelativeSingular.inclusion (Nset : Set X5)ᶜ)).f (3 + 2) c -
        (cokernel.π (RationalRelativeSingular.inclusion (Nset : Set X5)ᶜ)).f (3 + 2) c' := by
    have h1 : (cokernel.π (RationalRelativeSingular.inclusion (Nset : Set X5)ᶜ)).f (3 + 2)
        ((singularBoundary ℚ X5 (3 + 2)).hom b') = (supportChains Nset).d (3 + 2 + 1) (3 + 2)
          ((cokernel.π (RationalRelativeSingular.inclusion (Nset : Set X5)ᶜ)).f (3 + 2 + 1) b') := hd.symm
    rw [h1, hb']
    exact hb
  rw [map_sub, map_sub, hbd]
  abel

theorem boundary_smul_mem (a : ℚ) (c : singularChainGroup ℚ X5 (3 + 2))
    (h : (singularBoundary ℚ X5 (3 + 2 - 1)).hom c ∈ subChainSubmodule ℚ X5 Nsetᶜ (3 + 2 - 1)) :
    (singularBoundary ℚ X5 (3 + 2 - 1)).hom (a • c) ∈ subChainSubmodule ℚ X5 Nsetᶜ (3 + 2 - 1) := by
  rw [map_smul]
  exact Submodule.smul_mem _ _ h

theorem relCls_smul (a : ℚ) (c : singularChainGroup ℚ X5 (3 + 2))
    (h : (singularBoundary ℚ X5 (3 + 2 - 1)).hom c ∈ subChainSubmodule ℚ X5 Nsetᶜ (3 + 2 - 1)) :
    relCls (a • c) (boundary_smul_mem a c h) = a • relCls c h := by
  unfold relCls chainClass
  have : (⟨(cokernel.π (RationalRelativeSingular.inclusion (Nset : Set X5)ᶜ)).f (3 + 2) (a • c),
      proj_cycle (a • c) (boundary_smul_mem a c h)⟩ :
        SingularLocalCap.Homology.Cycles ((supportChains Nset).sc' (3 + 2 + 1) (3 + 2) (3 + 2 - 1))) =
      a • ⟨(cokernel.π (RationalRelativeSingular.inclusion (Nset : Set X5)ᶜ)).f (3 + 2) c, proj_cycle c h⟩ := by
    apply Subtype.ext
    exact map_smul _ _ _
  rw [this, map_smul, map_smul]

end TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport
