module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.LevelG.Shapiro

@[expose] public section


/-!
# Lemma 3.3 (`lem:apartment-boundary-pairing`) at level `G = GL₃(ℤ)` with `M = Ind_K^G E_{n,t}`

Formalized by Claude Sonnet 5.5.

## What is proved

* `lemma_3_3_levelG`: the diagram `eq:apartment-boundary-diagram` at level `G` for `H¹(∂X̄_G; M)` (the library's invariant
  cohomology `Hom_G(C_*(∂X̄), M)`) and for `H₃(∂X̄_G; 𝓜)` (realized as its Poincaré dual in neat-level boundary homology), with the
  bottom arrow `⟨ω, ∂a⟩ ∈ M`, the right arrow `z ↦ F_z(ℓ)` through `Θ^G`, the agreement with the neat-level `PDboundary` and
  `flatBoundaryPairing`, and the descent statements: for every neat-level class `c`, `Cor(j_* c) = Cor(j_* avG(c))` and its
  pairing is `⟨transfer(PD_∂ c), ∂a⟩` (rational averaging is exact and preserves the pairing).
* `lemma_3_3_levelK`: with `M = Ind_K^G E_{n,t}` (`t ∈ {0,1}`) and Shapiro's lemma realized through Borel--Serre duality
  (`H₃(G, M) ≃ H₃(K, E_{n,t})`, `shapiroG`), the identity-apartment value of Lemma 3.2's functional is the identity-coset
  component `evaluation n` of `⟨ω, ∂a⟩`, i.e. `λ(F_{j_*c}(ℓ)) = ⟨PD_∂ c, ∂a_{φ_λ}⟩` for `φ_λ = λ ∘ evaluation`; and with the paper's
  library normalization (`coeffAtT0Norm`, a scale artefact, not the geometric local intersection number `+1`; see
  `Exports/Lemma33LevelGHonest.lean` and `levelG_cellular_geo`) it is the coefficient of a cellular top cycle against the normalized generator.
* `evaluator_equivariant`: equivariance of the top evaluator for the conjugation action of `GL₃(ℤ)`; `pairing_coset_formula`: the
  coset-unfolded formula.

## What is not proved

This file states the diagram on `H3boundaryG` and its averaged (descent) form.  The geometric action `bAct` of `GL₃(ℤ)` on the
singular boundary chains, equivariance of `j_*` and `PD_∂` (trivial orientation character), the identification of `H3boundaryG`
with the invariants and with the honest coinvariant homology are proved in `Exports/Lemma33LevelGHonest.lean`.  The relation of `shapiroG` with Mathlib's group-homology Shapiro
isomorphism is PROVED with the factor `[G:K]` (`Naturality.ShapiroCor.mathlibShapiro_eq_index_smul`); the scalar-one version holds iff
`H₃ = 0`.  Not covered: the paper's `K`-level boundary objects and the boundary-level induction squares (see `Exports/Lemma33LevelGHonest.lean`);
`|d₅| = 1` is not provable and not needed.
-/

open CategoryTheory HomologicalComplex TernaryPoly TernaryPoly.IntegralGL3Congruence TernaryPoly.ModThreeGoodAction
  TernaryPoly.OrdinaryBoundaryActualEvaluation TernaryPoly.SymmetricSpaceBoundaryFull
  TernaryPoly.SymmetricSpaceBoundaryFullTransfer TernaryPoly.OrdinaryBoundaryCone
  TernaryPoly.OrdinaryBoundaryCommonRoot TernaryPoly.OrdinaryTopBoundaryComparison
  TernaryPoly.SymmetricSpaceBoundaryIncidenceHomology
open TernaryPeriodPolynomials.Argument.FiberModel
open TernaryPeriodPolynomials.Argument.GroupHomology
open TernaryPeriodPolynomials.Argument.Lemma33.LevelG
open TernaryPeriodPolynomials.Argument.Statements.Lemma33Diagram (PDboundary flatBoundaryPairing)
open TernaryPeriodPolynomials.Argument.Statements.FiberModel (H3_K_equiv)

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Statements.Lemma33LevelG

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- **Lemma 3.3 at level `G = GL₃(ℤ)`** for `M = Ind_K^G E` realized as the 26-covector system `actualCoefficients n e`.

1. the diagram `j^G_* ≫ (z ↦ F_z(ℓ)) = PD_∂⁻¹ ≫ (ω ↦ ⟨ω, ∂a⟩)` on `H¹(∂X̄_G; M)` (invariants);
2. the same with `H₃(∂X̄_G; 𝓜)` and `PD_∂` in the paper's direction, agreeing with the neat-level `PDboundary` and
   `flatBoundaryPairing`;
3. descent (coinvariants in homology, invariants in cohomology) preserves the pairing: for every neat-level boundary class
   `c`, `Cor(j_* c) = Cor(j_* avG(c))`, with pairing `⟨transfer(PD_∂ c), ∂a⟩`, and `avG` fixes `H₃(∂X̄_G; 𝓜)`;
4. the cellular reading with the paper's normalization: `F_{j^G_*ω}(ℓ)` is the coefficient of a top cycle against the
   normalized generator. -/
theorem lemma_3_3_levelG (n : ℕ) (e : ℤ) :
    (∀ ω : (fullBoundaryCochains n e).homology 1,
      topEvaluationG (actualCoefficients n e) (fullBoundaryClassToG n e ω) = fullBoundaryPairing n e ω) ∧
    (∀ c : H3boundaryG n e,
      topEvaluationG (actualCoefficients n e)
          (corG n e (SymmetricSpaceBoundaryDuality.boundaryToGroup (restrictedCoefficients n e) 3 c.1)) =
        fullBoundaryPairing n e (PDG n e c) ∧
      flatBoundaryPairing (restrictedCoefficients n e) (PDboundary (restrictedCoefficients n e) c.1) =
        fullBoundaryPairing n e (PDG n e c)) ∧
    (∀ c : (SingularLocalHomology.boundaryLocalChains (restrictedCoefficients n e)).homology 3,
      corG n e (SymmetricSpaceBoundaryDuality.boundaryToGroup (restrictedCoefficients n e) 3 c) =
          corG n e (SymmetricSpaceBoundaryDuality.boundaryToGroup (restrictedCoefficients n e) 3 (avG n e c).1) ∧
      topEvaluationG (actualCoefficients n e)
          (corG n e (SymmetricSpaceBoundaryDuality.boundaryToGroup (restrictedCoefficients n e) 3 c)) =
        fullBoundaryPairing n e
          (homologyMap (transfer principalSix fullBoundaryChains (actualCoefficients n e)) 1
            (PDboundary (restrictedCoefficients n e) c))) ∧
    (∀ c : H3boundaryG n e, avG n e c.1 = c) :=
  ⟨levelG_diagram n e, fun c => ⟨levelG_diagram_PD n e c, flatBoundaryPairing_PDG n e c⟩,
    fun c => ⟨corN_avG n e c, levelG_diagram_all n e c⟩, avG_fixed n e⟩

open TernaryPeriodPolynomials.Argument.Lemma33.Retract
open TernaryPeriodPolynomials.Argument.Lemma33.Normalized (coeffAtT0Norm)

/-- **Lemma 3.3 at level `G` with the coefficient system `M = Ind_K^G E_{n,t}` and `H₃(X̄_G; 𝓜) ≅ H₃(K, E_{n,t})`**
(`t ∈ {0,1}`, determinant exponent `e = -t`).  For `ω ∈ H¹(∂X̄_G; M)`, the Steinberg functional of the `K`-level class
`Sh(j^G_* PD_∂⁻¹ ω) ∈ H₃(K, E_{n,t})` (Lemma 3.2's `F`) has, on the identity apartment, the value
`F(ℓ) = evaluation(⟨ω, ∂a⟩)`: the identity-coset component of the boundary pairing, so that for `φ_λ = λ ∘ evaluation`
(`φ_λ(F) = λ(F(ℓ))`) one has `λ(F_{j_*c}(ℓ)) = ⟨PD_∂ c, ∂a_{φ_λ}⟩`.  With the library's normalization the same value is the
coefficient of a cellular top cycle against the library-normalized top-cell generator (`coeffAtT0Norm`, a scale artefact; the geometric
form is `levelG_cellular_geo`). -/
theorem lemma_3_3_levelK (n : ℕ) (t : Fin 2) :
    (∀ ω : (fullBoundaryCochains n (expT t)).homology 1,
      (H3_K_equiv n t (shapiroG n t (fullBoundaryClassToG n (expT t) ω))).1 identityApartment =
        evaluation n (fullBoundaryPairing n (expT t) ω) ∧
      ∃ (z : (cellCoinv (restrictedCoefficients n (expT t))).X 3)
        (hz : ((cellCoinv (restrictedCoefficients n (expT t))).d 3 2).hom z = 0),
        fullBoundaryClassToGroup n (expT t) ω =
            cellGroupHomologyMap (restrictedCoefficients n (expT t)) 3
              (cellClass (restrictedCoefficients n (expT t)) z hz) ∧
          (H3_K_equiv n t (shapiroG n t (fullBoundaryClassToG n (expT t) ω))).1 identityApartment =
            evaluation n ((coeffAtT0Norm (restrictedCoefficients n (expT t))).hom z)) ∧
    (∀ c : (SingularLocalHomology.boundaryLocalChains (restrictedCoefficients n (expT t))).homology 3,
      (H3_K_equiv n t (shapiroG n t
          (corG n (expT t) (SymmetricSpaceBoundaryDuality.boundaryToGroup (restrictedCoefficients n (expT t)) 3 c)))).1
          identityApartment =
        evaluation n (fullBoundaryPairing n (expT t)
          (homologyMap (transfer principalSix fullBoundaryChains (actualCoefficients n (expT t))) 1
            (PDboundary (restrictedCoefficients n (expT t)) c)))) := by
  refine ⟨fun ω => ⟨?_, ?_⟩, fun c => ?_⟩
  · rw [shapiroG_evaluation, levelG_diagram]
  · obtain ⟨z, hz, h1, h2, h3⟩ := levelG_cellular n (expT t) ω
    refine ⟨z, hz, h1, ?_⟩
    rw [shapiroG_evaluation, h2]
  · rw [shapiroG_evaluation, levelG_diagram_all]

/-- **Equivariance of the top evaluator** under the conjugation action of `GL₃(ℤ)` (O-G1, evaluator part), for every
`G`-representation `M`: `ev(c_g x) = ρ(g)(Θ(x)(apartment of frame g⁻¹))`.  (Equivariance of `j_*` and `PD_∂` is proved in
averaged form, `lemma_3_3_levelG`.) -/
theorem evaluator_equivariant (M : Rep.{0} ℚ IntegralGL) (g : IntegralGL)
    (x : groupHomology (Rep.res principalSix.subtype M) 3) :
    groupApartmentEvaluation (Rep.res principalSix.subtype M) (cAct principalSix M 3 g x) =
      M.ρ g (((groupOrdinaryIso (Rep.res principalSix.subtype M)).hom x).hom
        (OrdinaryApartmentPresentation.frameCycle g⁻¹)) :=
  apartmentEvaluation_cAct M g x

/-- **Coset unfolding, explicit**: the pairing at level `G` of an arbitrary neat-level cocycle is the normalized sum over
the cosets of `Γ(6)`, `[G:Γ(6)]⁻¹ ∑_q ρ(q⁻¹)⟨x, q·∂a⟩`, each summand the translated apartment evaluation. -/
theorem pairing_coset_formula (n : ℕ) (e : ℤ)
    (x₀ : (EquivariantSingularSmall.homCochains boundaryChains (restrictedCoefficients n e)).cycles 1) :
    topEvaluationG (actualCoefficients n e)
        (corG n e (boundaryImage n e
          ((EquivariantSingularSmall.homCochains boundaryChains (restrictedCoefficients n e)).homologyπ 1 x₀))) =
      (Nat.card (TernaryPoly.RationalCohomologyDescent.RightCosets principalSix) : ℚ)⁻¹ •
        ∑ q : TernaryPoly.RationalCohomologyDescent.RightCosets principalSix,
          (actualCoefficients n e).ρ q.out⁻¹
            ((cocycleValue boundaryChains (restrictedCoefficients n e) 1 x₀).hom
              ((fullBoundaryChains.X 1).ρ q.out apartmentChainFull)) :=
  levelG_diagram_formula n e x₀

end TernaryPeriodPolynomials.Argument.Statements.Lemma33LevelG
