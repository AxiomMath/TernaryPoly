module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.SingularCechFlags

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory Set FreeActionLinearization SphereOddDegree
open SmoothCoveringDeRham SymmetricSpaceCovering SymmetricSpaceCharts
open scoped Simplicial

variable {F : Type} [AddCommGroup F] [Module ℝ F] (ρ : Representation ℝ DeckGroup F)
  {ι : Type} (U : ι → Set OrbitSpace) (hU : ∀ i, IsOpen (U i)) (hcover : Set.univ ⊆ ⋃ i, U i)

/-- Actual local singular Hom cochains evaluate on the actual simplices in a Čech flag. -/
def singularCechToFlags (n k : ℕ) : SingularCechTerms ρ U n (k+1) →ₗ[ℝ]
    (smallSimplexIndexCover U hU hcover n).flagCochains ρ (k+1) where
  toFun w := ⟨fun x => cochainFunctionEquiv DeckGroup (TopCat.of (CoverOpen (cechDomain U x.labels)))
    (Rep.of ρ) n (w x.labels) (flagSimplex U hU hcover n k x),fun g x => by
      exact (congrArg
        (cochainFunctionEquiv DeckGroup (TopCat.of (CoverOpen (cechDomain U x.labels)))
          (Rep.of ρ) n (w x.labels)) (flagSimplex_smul U hU hcover n k g x)).trans
            ((cochainFunctionEquiv DeckGroup (TopCat.of (CoverOpen (cechDomain U x.labels)))
              (Rep.of ρ) n (w x.labels)).property g _)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Evaluation of the actual flag-function map. -/
theorem singularCechToFlags_apply (n k : ℕ) (w : SingularCechTerms ρ U n (k+1))
    (x : SingularCoverFlag U hU hcover n (k+1)) :
    (singularCechToFlags ρ U hU hcover n k w).val x =
      cochainFunctionEquiv DeckGroup (TopCat.of (CoverOpen (cechDomain U x.labels)))
        (Rep.of ρ) n (w x.labels) (flagSimplex U hU hcover n k x) := rfl

/-- Actual flag functions restrict to equivariant functions on each genuine local simplex family. -/
def singularFlagsAtLocal (n k : ℕ) (t : Fin (k+1) → ι) :
    (smallSimplexIndexCover U hU hcover n).flagCochains ρ (k+1) →ₗ[ℝ]
      equivariantFunctions DeckGroup (TopCat.of (CoverOpen (cechDomain U t))) (Rep.of ρ) n where
  toFun w := ⟨fun σ => w.val (localSimplexFlag U hU hcover n k t σ),fun g σ =>
    (congrArg w.val (localSimplexFlag_smul U hU hcover n k t g σ)).trans (w.property g _)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Actual flag functions extend linearly to the actual equivariant singular Hom cochains
on each genuine Čech intersection. -/
def singularFlagsToCech (n k : ℕ) : (smallSimplexIndexCover U hU hcover n).flagCochains ρ (k+1) →ₗ[ℝ]
    SingularCechTerms ρ U n (k+1) :=
  LinearMap.pi (fun t => (cochainFunctionEquiv DeckGroup (TopCat.of (CoverOpen (cechDomain U t)))
    (Rep.of ρ) n).symm.toLinearMap.comp (singularFlagsAtLocal ρ U hU hcover n k t))

/-- Extension to actual singular Hom cochains retains literal generator evaluation. -/
theorem singularFlagsToCech_evaluate (n k : ℕ)
    (w : (smallSimplexIndexCover U hU hcover n).flagCochains ρ (k+1))
    (t : Fin (k+1) → ι) (σ : SingularSimplex (TopCat.of (CoverOpen (cechDomain U t))) n) :
    cochainFunctionEquiv DeckGroup (TopCat.of (CoverOpen (cechDomain U t))) (Rep.of ρ) n
      (singularFlagsToCech ρ U hU hcover n k w t) σ = w.val (localSimplexFlag U hU hcover n k t σ) :=
  congrArg (fun f => f σ) ((cochainFunctionEquiv DeckGroup
    (TopCat.of (CoverOpen (cechDomain U t))) (Rep.of ρ) n).apply_symm_apply _)

/-- The actual local-cochain-to-flag and flag-to-local-cochain maps are inverse. -/
theorem singularFlagsToCech_toFlags (n k : ℕ) (w : SingularCechTerms ρ U n (k+1)) :
    singularFlagsToCech ρ U hU hcover n k (singularCechToFlags ρ U hU hcover n k w) = w := by
  funext t
  apply (cochainFunctionEquiv DeckGroup (TopCat.of (CoverOpen (cechDomain U t))) (Rep.of ρ) n).injective
  apply Subtype.ext
  funext σ
  rw [singularFlagsToCech_evaluate,singularCechToFlags_apply]
  exact congrArg (cochainFunctionEquiv DeckGroup (TopCat.of (CoverOpen (cechDomain U t))) (Rep.of ρ) n (w t))
    (flagSimplex_local U hU hcover n k t σ)

/-- The inverse composite is the identity on actual equivariant small-simplex flag functions. -/
theorem singularCechToFlags_fromFlags (n k : ℕ)
    (w : (smallSimplexIndexCover U hU hcover n).flagCochains ρ (k+1)) :
    singularCechToFlags ρ U hU hcover n k (singularFlagsToCech ρ U hU hcover n k w) = w := by
  apply Subtype.ext
  funext x
  rw [singularCechToFlags_apply,singularFlagsToCech_evaluate]
  exact congrArg w.val (localSimplexFlag_flag U hU hcover n k x)

/-- The genuine local singular Čech terms are exactly the actual equivariant flag-function terms. -/
def singularCechFlagEquiv (n k : ℕ) : SingularCechTerms ρ U n (k+1) ≃ₗ[ℝ]
    (smallSimplexIndexCover U hU hcover n).flagCochains ρ (k+1) :=
  { singularCechToFlags ρ U hU hcover n k with
    invFun := singularFlagsToCech ρ U hU hcover n k
    left_inv := singularFlagsToCech_toFlags ρ U hU hcover n k
    right_inv := singularCechToFlags_fromFlags ρ U hU hcover n k }

end TernaryPoly.SmoothSingularGlobal
