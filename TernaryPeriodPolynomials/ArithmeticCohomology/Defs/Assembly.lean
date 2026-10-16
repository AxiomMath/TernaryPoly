module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs.Polynomial

@[expose] public section


/-!
# Composition of the six paper statements

This module imports definitions only. The assembly theorem
checks that their exact conclusions suffice for the paper's J_f=0 step.
-/

noncomputable section
namespace GeneralEisenstein
open Homogeneous

/-- Two actual descents of the same finite-coset formula give the same action. -/
theorem realizesHecke_unique {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ RationalGL3 V)
    (T T' : HeckeCorrespondence → Module.End ℂ (H2 rationalLevel ρ))
    (hT : RealizesHecke ρ T) (hT' : RealizesHecke ρ T') : T = T' := by
  funext t
  apply LinearMap.ext
  intro a
  refine Quotient.inductionOn a ?_
  intro c
  rcases hT t c with ⟨z, hz, ht⟩
  rcases hT' t c with ⟨z', hz', ht'⟩
  have heq : z = z' := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    rw [hz x, hz' x]
  change T t (classOf rationalLevel ρ c) = T' t (classOf rationalLevel ρ c)
  rw [ht, ht', heq]

/-- The mathematical statements of the six separate inputs.
This package is solely the interface of
the proved composition lemma below. -/
structure EisensteinInputs where
  bridge : ∀ n, 0 < n → ∀ f : HomogeneousPoly n,
    SymmetricSolution f → PolynomialBoundaryBridge f
  recognition : ∀ n, 0 < n → ∀ b : BoundaryCoordinates n trivialCharacter,
    GoodBoundaryVanishing n trivialCharacter b →
    InnerBoundary n trivialCharacter .line b.2 → CuspidalRecognition n b
  holomorphy : ∀ n, 0 < n → ∀ D : InducingData n,
    D.chi = trivialCharacter → PlaneEisensteinHolomorphic D
  graph : ∀ n, ∀ D : InducingData n, PlaneEisensteinHolomorphic D → GraphConclusion D
  projection : ∀ n, 0 < n → ∀ D : InducingData n,
    ∀ hecke : (side : Side) → HeckeCorrespondence → Module.End ℂ (StratumH2 n D.chi side),
    (∀ side, RealizesHecke
      (flagRepresentation (rationalCoefficientComponent n D.chi) side) (hecke side)) →
    ∀ p : Module.End ℂ (BoundaryCoordinates n D.chi), IsIsotypicalProjection D hecke p →
    ∀ b, GoodBoundaryVanishing n D.chi b → GoodBoundaryVanishing n D.chi (p b)
  detection : ∀ n, 0 < n → ∀ D : InducingData n, D.chi = trivialCharacter →
    PlaneEisensteinHolomorphic D →
    ∀ T : boundarySummand D .plane →ₗ[ℂ] boundarySummand D .line,
    RealizesStandard D T → ∀ ξ : boundarySummand D .plane,
    VanishesOnGood n D.chi .plane ξ.val →
    VanishesOnGood n D.chi .line (T ξ).val → ξ = 0

/-- The six statements imply the paper's
vanishing proposition with no further source-recognition or compatibility input. -/
theorem bernoulli_obstruction_vanishes_of_challenges
    (H : EisensteinInputs) (n : ℕ) (hn : 0 < n)
    (f : HomogeneousPoly n) (hf : SymmetricSolution f) : bernoulliObstruction f = 0 := by
  classical
  rcases H.bridge n hn f hf with
    ⟨F, τ, c, hF, hτ, hc, hpaths, hgood, hinner, hmixed, hA, hB, hR, hdetect⟩
  let b := globalCoordinates n trivialCharacter c
  rcases H.recognition n hn b hgood hinner with
    ⟨hecke, hhecke, m, D, p, hp, hrecover⟩
  have hzero : ∀ i, (p i b).2 = 0 := by
    intro i
    let d := (D i).inducingData
    have hhol : PlaneEisensteinHolomorphic d := H.holomorphy n hn d rfl
    rcases H.graph n d hhol with
      ⟨hsource, r, q, hecke', p', T, hr, hq, hpair, hhecke', hp', hunique, hT, hgraph⟩
    dsimp only [d, CohomologicalCuspData.inducingData] at *
    have heq : hecke' = hecke := by
      funext side
      exact realizesHecke_unique _ _ _ (hhecke' side) (hhecke side)
    have hpi : IsIsotypicalProjection d hecke' (p i) := by
      rw [heq]
      exact hp i
    have hpeq : p i = p' := hunique (p i) hpi
    have hmem : p' b ∈ LinearMap.range (p'.comp (q.comp r)) := by
      refine ⟨classOf rationalLevel (rationalCoefficientComponent n trivialCharacter) c, ?_⟩
      simp only [LinearMap.comp_apply]
      have h1 := hr c
      have h2 := hq (globalBoundaryCocycle n trivialCharacter c)
      exact congrArg p' ((congrArg q h1).trans h2)
    have hpoint : ∃ ξ : boundarySummand d .plane, p' b = (ξ.val, (T ξ).val) := by
      exact (Set.ext_iff.mp hgraph (p' b)).mp hmem
    rcases hpoint with ⟨ξ, hξ⟩
    have hg := H.projection n hn d hecke hhecke (p i) (hp i) b hgood
    rw [hpeq, hξ] at hg
    have hξzero := H.detection n hn d rfl hhol T hT ξ hg.1 hg.2
    rw [hpeq, hξ, hξzero]
    simp
  apply hdetect
  change b.2 = 0
  rw [← hrecover]
  exact Finset.sum_eq_zero (fun i _ => hzero i)

end GeneralEisenstein
end
