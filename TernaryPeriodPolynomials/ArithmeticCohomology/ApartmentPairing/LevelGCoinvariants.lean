module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.LevelG.Coinvariants
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.LevelG.MathlibShapiro
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.LevelG.Averages
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.LevelG.GeoCellular
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.LevelG.Natural
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Geometric.ChartCompare
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Lemma33LevelG

@[expose] public section


/-!
# Lemma 3.3 at level `G` on the honest coinvariant boundary homology (action, equivariance, descent)

Formalized by Claude Sonnet 5.5.

Paper: "compatible with induction of coefficients and with passage to a finite-index subgroup".

## What is proved here (beyond `Exports/Lemma33LevelG.lean`)

* `GL₃(ℤ)` acts on the singular boundary chains with twisted coefficients (`LevelG.bAct`, from the diagonal action on the
  `G`-complex `M ⊗ Sing(∂X̃)`), as a right action (`bAct_mul`, `bAct_one`) trivial on `Γ(6)` (`bAct_of_mem`).
* `boundaryToGroup` is equivariant for it and conjugation on group homology (`boundaryToGroup_equivariant`), and boundary
  Poincaré duality is equivariant for `bAct` and the conjugation action on `Hom` cohomology (`BR.PDboundary_equivariant`; trivial
  orientation character).
* `H3boundaryG` is exactly the space of `bAct`-invariants (`mem_H3boundaryG_iff`).
* The honest `H₃(∂X̄_G; 𝓜) = H₃((M ⊗ Sing ∂X̃)_G)` (`Qbd`): `qBd` is surjective with kernel the kernel of the average, `G` acts
  trivially, `qBd` restricts to an isomorphism `coinvIso` from `H3boundaryG`; `jQ`, `PDQ` and the diagram on `Qbd`.
* `levelG_cellular_geo` (GeoCellular.lean) and the pushed staircase cell and the chart comparison (`Geometric.stairClassSpace_at`, `stairClassTrans_at`).

## Compatibility with induction and finite-index passage

What is proved (`Statements.Lemma33LevelG`): (i) `lemma_3_3_levelK`: the `K`-level functional of `shapiroG(j^G_*ω)` at `ℓ` is `evaluation`
of `⟨ω, ∂a⟩`.  Since `shapiroG` is DEFINED through the duality and `frobenius` is evaluation at `ℓ`, this is definitional (R8 §3.2); it is not the paper's induction compatibility, which concerns the cellular coset-unfolding Shapiro map on the boundary groups.  For that
map the relation carries the index: `Naturality.ShapiroCor.mathlibShapiro_eq_index_smul` (Mathlib's Shapiro = `[G:K] • shapiroG`) and
`shapiroComparison_scaled`.  (ii) The cover passage `Γ(6) ⊂ G` (`lemma_3_3_levelG` part 3, `levelG_diagram_all`: `Cor` on homology is
`transfer` on cohomology, pairing unchanged).  Not covered: the paper's `K`-level (and intermediate-level) boundary objects as equivariant
quotients, their `j_*` / `PD_∂`, the boundary Shapiro map and the commuting squares with all scalars derived from the
actual cap/descent maps, and the literal finite-index assertion of the paper.

## What is NOT proved

* `ShapiroComparison n t` (`LevelG.MathlibShapiro`, the scalar-one equality of `shapiroG` with Mathlib's Shapiro isomorphism) is
  EQUIVALENT to `H₃(G, M_{n,t}) = 0` (`shapiroComparison_iff_trivial`); the true relation has the factor `[G:K]`
  (`mathlibShapiro_eq_index_smul`, `shapiroComparison_scaled`).  `Statements.Lemma33LevelG.lemma_3_3_levelK` is stated for `shapiroG`.
* The boundary homology of the non-neat subgroup `K` with coefficients `E_{n,t}` is not constructed; `K`-level statements are
  stated for the Steinberg functional (`H3_K_equiv`) and the pairing in `M`, through `Γ(6)`-descent.
-/

open CategoryTheory HomologicalComplex TernaryPoly TernaryPoly.IntegralGL3Congruence TernaryPoly.ModThreeGoodAction
  TernaryPoly.OrdinaryBoundaryActualEvaluation TernaryPoly.SymmetricSpaceBoundaryFull
  TernaryPoly.OrdinaryBoundaryCone TernaryPoly.SymmetricSpaceBoundaryFullTransfer
open TernaryPeriodPolynomials.Argument.GroupHomology
open TernaryPeriodPolynomials.Argument.FiberModel
open TernaryPeriodPolynomials.Argument.Lemma33.LevelG
open TernaryPeriodPolynomials.Argument.Statements.Lemma33Diagram (PDboundary)

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Statements.Lemma33LevelGHonest

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- **Equivariance and descent for the geometric action on the boundary** (every `G`-module `V₀`, every `g`). -/
theorem equivariance (V₀ : Rep.{0} ℚ IntegralGL) (g : IntegralGL)
    (c : (SingularLocalHomology.boundaryLocalChains (Rep.res principalSix.subtype V₀)).homology 3) :
    -- `j_*` is equivariant
    (TernaryPoly.SymmetricSpaceBoundaryDuality.boundaryToGroup (Rep.res principalSix.subtype V₀) 3).hom
        ((homologyMap (bAct V₀ g) 3).hom c) =
      (groupHomology.map (conjN principalSix g) (conjRep principalSix V₀ g) 3).hom
        ((TernaryPoly.SymmetricSpaceBoundaryDuality.boundaryToGroup (Rep.res principalSix.subtype V₀) 3).hom c) ∧
    -- `PD_∂` is equivariant
    PDboundary (Rep.res principalSix.subtype V₀) (homologyMap (bAct V₀ g) 3 c) =
      hcohAct bdryAct (GAct.ofRep principalSix V₀) g 1 (PDboundary (Rep.res principalSix.subtype V₀) c) :=
  ⟨ConcreteCategory.congr_hom (boundaryToGroup_equivariant V₀ g) c, BR.PDboundary_equivariant g V₀ c⟩

/-- **Lemma 3.3 at level `G`, honest form** for `M = actualCoefficients n e` (`= Ind_K^G E_{n,e}`). -/
theorem levelG_honest (n : ℕ) (e : ℤ) :
    -- `H₃(∂X̄_G; 𝓜)` inside the neat level is the space of invariants of the geometric action
    (∀ c : (SingularLocalHomology.boundaryLocalChains (restrictedCoefficients n e)).homology 3, c ∈ H3boundaryG n e ↔
      ∀ g : IntegralGL, homologyMap (bAct (actualCoefficients n e) g) 3 c = c) ∧
    -- the honest coinvariant homology: `qBd` is onto with kernel the kernel of the average, and `G` acts trivially
    Function.Surjective (qBd (actualCoefficients n e)).hom ∧
    (∀ c : (SingularLocalHomology.boundaryLocalChains (restrictedCoefficients n e)).homology 3, (qBd (actualCoefficients n e)).hom c = 0 ↔ avgBd (actualCoefficients n e) c = 0) ∧
    (∀ (g : IntegralGL) (c : (SingularLocalHomology.boundaryLocalChains (restrictedCoefficients n e)).homology 3), (qBd (actualCoefficients n e)).hom (homologyMap (bAct (actualCoefficients n e) g) 3 c) =
      (qBd (actualCoefficients n e)).hom c) ∧
    -- the iso `H3boundaryG ≃ Qbd` is `qBd`
    (∀ c : H3boundaryG n e, (coinvIso n e) c = (qBd (actualCoefficients n e)).hom c.1) ∧
    -- `j^G_*` on `Qbd` is `Cor ∘ j_*`, and the diagram commutes on `Qbd`
    (∀ c : (SingularLocalHomology.boundaryLocalChains (restrictedCoefficients n e)).homology 3, jQ n e ((qBd (actualCoefficients n e)).hom c) =
      (corG n e).hom ((TernaryPoly.SymmetricSpaceBoundaryDuality.boundaryToGroup (restrictedCoefficients n e) 3).hom c)) ∧
    (∀ y : Qbd (actualCoefficients n e),
      topEvaluationG (actualCoefficients n e) (jQ n e y) = fullBoundaryPairing n e (PDQ n e y)) := by
  refine ⟨mem_H3boundaryG_iff n e, qBd_surjective _, qBd_ker _, qBd_bAct _, ?_, jQ_qBd n e, levelG_diagram_Q n e⟩
  intro c
  exact coinvIso_apply n e c

end TernaryPeriodPolynomials.Argument.Statements.Lemma33LevelGHonest
