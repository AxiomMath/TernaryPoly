module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.FiniteCofaces
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.FiniteFamilies
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.SingularCechBicomplex
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.SingularSubdomainSimplex

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Set Function CategoryTheory FreeActionLinearization SphereOddDegree
open SmoothCoveringDeRham SymmetricSpaceCovering SymmetricSpaceCharts
open scoped Simplicial

variable {F : Type} [AddCommGroup F] [Module ℝ F] (ρ : Representation ℝ DeckGroup F)

/-- A nonzero actual singular Hom cochain has a literal simplex on which its value is nonzero. -/
theorem coveringCochain_exists_ne_zero {U : Set OrbitSpace} {n : ℕ}
    (w : (coveringCochains ρ U).X n) (hw : w ≠ 0) :
    ∃ σ : SingularSimplex (TopCat.of (CoverOpen U)) n,
      cochainFunctionEquiv DeckGroup (TopCat.of (CoverOpen U)) (Rep.of ρ) n w σ ≠ 0 := by
  by_contra! h
  apply hw
  apply (cochainFunctionEquiv DeckGroup (TopCat.of (CoverOpen U)) (Rep.of ρ) n).injective
  apply Subtype.ext
  funext σ
  exact (h σ).trans (congrArg (fun v => v σ)
    (map_zero (cochainFunctionEquiv DeckGroup (TopCat.of (CoverOpen U)) (Rep.of ρ) n))).symm

/-- A nonzero actual singular cochain has a genuinely nonempty quotient domain. -/
theorem coveringCochain_domain_nonempty {U : Set OrbitSpace} {n : ℕ}
    (w : (coveringCochains ρ U).X n) (hw : w ≠ 0) : U.Nonempty := by
  obtain ⟨σ,_⟩ := coveringCochain_exists_ne_zero ρ w hw
  exact ⟨coordinateProjection (mvSimplexMap σ (Convexity.StdSimplex.single 0)).val,
    (mvSimplexMap σ (Convexity.StdSimplex.single 0)).property.2⟩

variable (C : CompactConvexCover)

/-- Actual singular face restrictions preserve finite tuple support on the actual compact
convex cover. -/
theorem singularCechSelect_finiteSupport (n k : ℕ) (a : Fin (k+2))
    (w : SingularCechTerms ρ (fun i => (C.sheet i).quotientDomain) n (k+1))
    (hw : (familySupport w).Finite) :
    (familySupport (singularCechSelect ρ (fun i => (C.sheet i).quotientDomain) a.succAbove n w)).Finite := by
  apply (C.finite_cofaces k hw).subset
  intro t ht
  refine ⟨coveringCochain_domain_nonempty ρ _ ht,a,?_⟩
  intro hz
  apply ht
  change (coveringCochainRestriction ρ (cechDomain_select_subset _ a.succAbove t)).f n
    (w (t ∘ a.succAbove)) = 0
  rw [hz,map_zero]

/-- The actual horizontal singular differential preserves finite tuple support. -/
theorem singularCechHorizontal_finiteSupport (n k : ℕ)
    (w : SingularCechTerms ρ (fun i => (C.sheet i).quotientDomain) n (k+1))
    (hw : (familySupport w).Finite) :
    (familySupport (horizontal (singularCechBicomplex ρ (fun i => (C.sheet i).quotientDomain)) k n w)).Finite := by
  have hd := congrArg (fun f : SingularCechTerms ρ (fun i => (C.sheet i).quotientDomain) n (k+1) →ₗ[ℝ]
    SingularCechTerms ρ (fun i => (C.sheet i).quotientDomain) n (k+2) => f w)
      (singularCechBicomplex_horizontal ρ (fun i => (C.sheet i).quotientDomain) k n)
  rw [LinearMap.sum_apply] at hd
  apply (congrArg (fun y : SingularCechTerms ρ (fun i => (C.sheet i).quotientDomain) n (k+2) =>
    (familySupport y).Finite) hd).mpr
  change (∑ a : Fin (k+2), ((-1 : ℤ)^a.val •
    singularCechSelect ρ (fun i => (C.sheet i).quotientDomain) a.succAbove n) w) ∈
    finiteFamilySubmodule (fun t : Fin (k+2) → C.Index =>
      (coveringCochains ρ (cechDomain (fun i => (C.sheet i).quotientDomain) t)).X n)
  apply Submodule.sum_mem
  intro a _
  rw [LinearMap.smul_apply]
  exact (finiteFamilySubmodule (fun t : Fin (k+2) → C.Index =>
    (coveringCochains ρ (cechDomain (fun i => (C.sheet i).quotientDomain) t)).X n)).toAddSubgroup.zsmul_mem
      (singularCechSelect_finiteSupport ρ C n k a w hw) _

/-- The actual singular coboundary preserves finite tuple support componentwise. -/
theorem singularCechVertical_finiteSupport (n k : ℕ)
    (w : SingularCechTerms ρ (fun i => (C.sheet i).quotientDomain) n k)
    (hw : (familySupport w).Finite) :
    (familySupport (singularCechColumnD ρ (fun i => (C.sheet i).quotientDomain) k n w)).Finite :=
  finiteFamily_map _ (fun t => ((coveringCochains ρ
    (cechDomain (fun i => (C.sheet i).quotientDomain) t)).d n (n+1)).hom) hw

end TernaryPoly.SmoothSingularGlobal
