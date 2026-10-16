module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.SmallSimplexCover
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.SingularNaturality

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory Set FreeActionLinearization SphereOddDegree
open SmoothCoveringDeRham SymmetricSpaceCovering SymmetricSpaceCharts
open scoped Simplicial

/-- An actual singular simplex in the genuine full coordinate covering. -/
abbrev GlobalCoverSimplex (n : ℕ) := SingularSimplex (TopCat.of (CoverOpen Set.univ)) n

/-- Push an actual local-cover simplex into the genuine full covering. -/
def globalizeSimplex (V : Set OrbitSpace) (n : ℕ)
    (σ : SingularSimplex (TopCat.of (CoverOpen V)) n) : GlobalCoverSimplex n :=
  (TopCat.toSSet.map (coverInclusion (Set.subset_univ V))).app (.op ⦋n⦌) σ

/-- Globalized actual simplices retain their literal coordinate values. -/
theorem globalizeSimplex_value (V : Set OrbitSpace) (n : ℕ)
    (σ : SingularSimplex (TopCat.of (CoverOpen V)) n) (t : Convexity.StdSimplex ℝ (Fin (n+1))) :
    (mvSimplexMap (globalizeSimplex V n σ) t).val = (mvSimplexMap σ t).val := rfl

/-- Containment of the actual projected simplex in a genuine quotient subset. -/
def SimplexInDomain (V : Set OrbitSpace) {n : ℕ} (σ : GlobalCoverSimplex n) : Prop :=
  ∀ t, coordinateProjection (mvSimplexMap σ t).val ∈ V

/-- A globalized local simplex is contained in its actual original quotient domain. -/
theorem globalizeSimplex_mem (V : Set OrbitSpace) (n : ℕ)
    (σ : SingularSimplex (TopCat.of (CoverOpen V)) n) :
    SimplexInDomain V (globalizeSimplex V n σ) := fun t => (mvSimplexMap σ t).property.2

/-- Literal codomain restriction reconstructs a simplex in a genuine covering subdomain. -/
def restrictGlobalSimplex (V : Set OrbitSpace) (n : ℕ) (σ : GlobalCoverSimplex n)
    (hσ : SimplexInDomain V σ) : SingularSimplex (TopCat.of (CoverOpen V)) n :=
  (TopCat.toSSetObjEquiv (TopCat.of (CoverOpen V)) (.op ⦋n⦌)).symm
    ⟨fun t => ⟨(mvSimplexMap σ t).val, (mvSimplexMap σ t).property.1, hσ t⟩,
      (continuous_subtype_val.comp (mvSimplexMap σ).continuous).subtype_mk _⟩

/-- Actual codomain restriction leaves every simplex coordinate unchanged. -/
theorem restrictGlobalSimplex_value (V : Set OrbitSpace) (n : ℕ) (σ : GlobalCoverSimplex n)
    (hσ : SimplexInDomain V σ) (t : Convexity.StdSimplex ℝ (Fin (n+1))) :
    (mvSimplexMap (restrictGlobalSimplex V n σ hσ) t).val = (mvSimplexMap σ t).val := by
  have h := (TopCat.toSSetObjEquiv (TopCat.of (CoverOpen V)) (.op ⦋n⦌)).apply_symm_apply
    (⟨fun t => ⟨(mvSimplexMap σ t).val, (mvSimplexMap σ t).property.1, hσ t⟩,
      (continuous_subtype_val.comp (mvSimplexMap σ).continuous).subtype_mk _⟩ :
        C(Convexity.StdSimplex ℝ (Fin (n+1)), CoverOpen V))
  exact congrArg (fun f => (f t).val) h

/-- Globalizing a restricted actual simplex recovers the original simplex exactly. -/
theorem globalize_restrictSimplex (V : Set OrbitSpace) (n : ℕ) (σ : GlobalCoverSimplex n)
    (hσ : SimplexInDomain V σ) : globalizeSimplex V n (restrictGlobalSimplex V n σ hσ) = σ := by
  apply (TopCat.toSSetObjEquiv (TopCat.of (CoverOpen Set.univ)) (.op ⦋n⦌)).injective
  apply ContinuousMap.ext
  intro t
  apply Subtype.ext
  exact restrictGlobalSimplex_value V n σ hσ t

/-- Restricting a globalized actual local simplex recovers that local simplex exactly. -/
theorem restrict_globalizeSimplex (V : Set OrbitSpace) (n : ℕ)
    (σ : SingularSimplex (TopCat.of (CoverOpen V)) n) :
    restrictGlobalSimplex V n (globalizeSimplex V n σ) (globalizeSimplex_mem V n σ) = σ := by
  apply (TopCat.toSSetObjEquiv (TopCat.of (CoverOpen V)) (.op ⦋n⦌)).injective
  apply ContinuousMap.ext
  intro t
  apply Subtype.ext
  exact restrictGlobalSimplex_value V n _ _ t

/-- Actual local-to-global simplex inclusion commutes with the genuine deck action. -/
theorem globalizeSimplex_smul (V : Set OrbitSpace) (n : ℕ) (g : DeckGroup)
    (σ : SingularSimplex (TopCat.of (CoverOpen V)) n) :
    globalizeSimplex V n (g • σ) = g • globalizeSimplex V n σ := by
  apply (TopCat.toSSetObjEquiv (TopCat.of (CoverOpen Set.univ)) (.op ⦋n⦌)).injective
  apply ContinuousMap.ext
  intro t
  apply Subtype.ext
  change (mvSimplexMap (globalizeSimplex V n (g • σ)) t).val = (mvSimplexMap (g • globalizeSimplex V n σ) t).val
  rw [globalizeSimplex_value,simplexMap_smul,simplexMap_smul]
  rfl

/-- Actual codomain restriction commutes with the genuine deck action. -/
theorem restrictGlobalSimplex_smul (V : Set OrbitSpace) (n : ℕ) (g : DeckGroup)
    (σ : GlobalCoverSimplex n) (hσ : SimplexInDomain V σ) (hgσ : SimplexInDomain V (g • σ)) :
    restrictGlobalSimplex V n (g • σ) hgσ = g • restrictGlobalSimplex V n σ hσ := by
  apply (TopCat.toSSetObjEquiv (TopCat.of (CoverOpen V)) (.op ⦋n⦌)).injective
  apply ContinuousMap.ext
  intro t
  apply Subtype.ext
  change (mvSimplexMap (restrictGlobalSimplex V n (g • σ) hgσ) t).val =
    (mvSimplexMap (g • restrictGlobalSimplex V n σ hσ) t).val
  rw [restrictGlobalSimplex_value,simplexMap_smul,simplexMap_smul]
  exact congrArg (SmoothCoveringDeRham.deckMap g) (restrictGlobalSimplex_value V n σ hσ t).symm

end TernaryPoly.SmoothSingularGlobal
