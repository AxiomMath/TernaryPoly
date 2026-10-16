module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.FiniteSingularCech
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.SingularFlagNaturality

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Set Function CategoryTheory FreeActionLinearization SphereOddDegree
open SmoothCoveringDeRham SymmetricSpaceCovering SymmetricSpaceCharts
open scoped Simplicial

variable {F : Type} [AddCommGroup F] [Module ℝ F] (ρ : Representation ℝ DeckGroup F)
  {ι : Type} (U : ι → Set OrbitSpace) (hU : ∀ i, IsOpen (U i)) (hcover : Set.univ ⊆ ⋃ i, U i)

/-- The genuine singular Čech homotopy, transported through the actual flag identifications. -/
def singularCechH (n k : ℕ) : SingularCechTerms ρ U n (k+2) →ₗ[ℝ] SingularCechTerms ρ U n (k+1) :=
  (singularFlagsToCech ρ U hU hcover n k).comp
    (((smallSimplexIndexCover U hU hcover n).flagH ρ (k+1)).comp
      (singularCechToFlags ρ U hU hcover n (k+1)))

/-- Its output is an actual horizontal primitive of every actual closed singular Čech cochain. -/
theorem singularCechH_primitive (n k : ℕ) (w : SingularCechTerms ρ U n (k+2))
    (hw : horizontal (singularCechBicomplex ρ U) (k+1) n w = 0) :
    horizontal (singularCechBicomplex ρ U) k n (singularCechH ρ U hU hcover n k w) = w := by
  have hx : (smallSimplexIndexCover U hU hcover n).flagD ρ (k+2)
      (singularCechToFlags ρ U hU hcover n (k+1) w) = 0 :=
    (singularCechToFlags_d ρ U hU hcover n (k+1) w).symm.trans
      ((congrArg (singularCechToFlags ρ U hU hcover n (k+2)) hw).trans (map_zero _))
  apply (singularCechFlagEquiv ρ U hU hcover n (k+1)).injective
  change singularCechToFlags ρ U hU hcover n (k+1) _ = _
  rw [singularCechToFlags_d]
  change (smallSimplexIndexCover U hU hcover n).flagD ρ (k+1)
    (singularCechToFlags ρ U hU hcover n k (singularFlagsToCech ρ U hU hcover n k
      ((smallSimplexIndexCover U hU hcover n).flagH ρ (k+1)
        (singularCechToFlags ρ U hU hcover n (k+1) w)))) = _
  rw [singularCechToFlags_fromFlags]
  exact (smallSimplexIndexCover U hU hcover n).flag_primitive ρ (k+1) _ hx

/-- The actual singular Čech homotopy preserves finite tuple support, since it only deletes
an index from a tuple at which the input cochain was nonzero. -/
theorem singularCechH_finiteSupport (n k : ℕ) (w : SingularCechTerms ρ U n (k+2))
    (hw : (familySupport w).Finite) :
    (familySupport (singularCechH ρ U hU hcover n k w)).Finite := by
  apply (hw.image (fun t => fun j : Fin (k+1) => t j.succ)).subset
  intro t ht
  by_contra h
  have hz (i : ι) : w (Fin.cons i t) = 0 := by
    by_contra hn
    exact h ⟨Fin.cons i t,hn,by funext j; simp⟩
  apply ht
  apply (cochainFunctionEquiv DeckGroup (TopCat.of (CoverOpen (cechDomain U t))) (Rep.of ρ) n).injective
  apply Subtype.ext
  funext σ
  have hv := singularFlagsToCech_evaluate ρ U hU hcover n k
    ((smallSimplexIndexCover U hU hcover n).flagH ρ (k+1)
      (singularCechToFlags ρ U hU hcover n (k+1) w)) t σ
  apply hv.trans
  change (singularCechToFlags ρ U hU hcover n (k+1) w).val
    ((smallSimplexIndexCover U hU hcover n).prepend (localSimplexFlag U hU hcover n k t σ)) = _
  rw [singularCechToFlags_apply]
  let i := (smallSimplexIndexCover U hU hcover n).index
    (localSimplexFlag U hU hcover n k t σ).point
  change cochainFunctionEquiv DeckGroup (TopCat.of (CoverOpen (cechDomain U (Fin.cons i t))))
    (Rep.of ρ) n (w (Fin.cons i t)) _ = _
  have hs := congrArg (fun c : (coveringCochains ρ (cechDomain U (Fin.cons i t))).X n =>
    cochainFunctionEquiv DeckGroup (TopCat.of (CoverOpen (cechDomain U (Fin.cons i t))))
      (Rep.of ρ) n c (flagSimplex U hU hcover n (k+1)
        ((smallSimplexIndexCover U hU hcover n).prepend (localSimplexFlag U hU hcover n k t σ)))) (hz i)
  refine hs.trans ?_
  exact (congrArg (fun v => v (flagSimplex U hU hcover n (k+1)
    ((smallSimplexIndexCover U hU hcover n).prepend (localSimplexFlag U hU hcover n k t σ)))) (map_zero (cochainFunctionEquiv DeckGroup
    (TopCat.of (CoverOpen (cechDomain U (Fin.cons i t)))) (Rep.of ρ) n))).trans
      (congrArg (fun v => v σ) (map_zero (cochainFunctionEquiv DeckGroup
        (TopCat.of (CoverOpen (cechDomain U t))) (Rep.of ρ) n))).symm

end TernaryPoly.SmoothSingularGlobal
