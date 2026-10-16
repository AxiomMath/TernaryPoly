module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.SingularFlagCochains

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory Set FreeActionLinearization SphereOddDegree
open SmoothCoveringDeRham SymmetricSpaceCovering SymmetricSpaceCharts
open scoped Simplicial

variable {F : Type} [AddCommGroup F] [Module ℝ F] (ρ : Representation ℝ DeckGroup F)
  {ι : Type} (U : ι → Set OrbitSpace) (hU : ∀ i, IsOpen (U i)) (hcover : Set.univ ⊆ ⋃ i, U i)

/-- Actual local-to-flag evaluation intertwines genuine Čech restriction with literal flag selection. -/
theorem singularCechToFlags_select (n p q : ℕ) (f : Fin (p+1) → Fin (q+1))
    (w : SingularCechTerms ρ U n (p+1)) :
    singularCechToFlags ρ U hU hcover n q (singularCechSelect ρ U f n w) =
      (smallSimplexIndexCover U hU hcover n).flagSelect ρ f (singularCechToFlags ρ U hU hcover n p w) := by
  apply Subtype.ext
  funext x
  change cochainFunctionEquiv DeckGroup (TopCat.of (CoverOpen (cechDomain U x.labels))) (Rep.of ρ) n
    ((coveringCochainRestriction ρ (cechDomain_select_subset U f x.labels)).f n (w (x.labels ∘ f)))
    (flagSimplex U hU hcover n q x) =
      cochainFunctionEquiv DeckGroup (TopCat.of (CoverOpen (cechDomain U (x.labels ∘ f)))) (Rep.of ρ) n
        (w (x.labels ∘ f)) (flagSimplex U hU hcover n p ((smallSimplexIndexCover U hU hcover n).select f x))
  exact (cochainPullback_evaluate (coverInclusion (cechDomain_select_subset U f x.labels))
    (coverInclusion_equivariant (cechDomain_select_subset U f x.labels)) (Rep.of ρ) n
    (w (x.labels ∘ f)) (flagSimplex U hU hcover n q x)).trans
      (congrArg (cochainFunctionEquiv DeckGroup (TopCat.of (CoverOpen (cechDomain U (x.labels ∘ f))))
        (Rep.of ρ) n (w (x.labels ∘ f))) (flagSimplex_select U hU hcover n p q f x).symm)

/-- The actual local singular Čech differential is carried to the genuine alternating flag differential. -/
theorem singularCechToFlags_d (n p : ℕ) (w : SingularCechTerms ρ U n (p+1)) :
    singularCechToFlags ρ U hU hcover n (p+1) (horizontal (singularCechBicomplex ρ U) p n w) =
      (smallSimplexIndexCover U hU hcover n).flagD ρ (p+1) (singularCechToFlags ρ U hU hcover n p w) := by
  have hd := congrArg (fun f : SingularCechTerms ρ U n (p+1) →ₗ[ℝ]
      SingularCechTerms ρ U n (p+2) => singularCechToFlags ρ U hU hcover n (p+1) (f w))
    (singularCechBicomplex_horizontal ρ U p n)
  refine hd.trans ?_
  rw [LinearMap.sum_apply,map_sum]
  simp only [LinearMap.smul_apply,map_zsmul,singularCechToFlags_select]
  simp only [InvariantSetCover.flagD,LinearMap.sum_apply,LinearMap.smul_apply]

include hU hcover in
/-- Every horizontally closed actual singular Čech cochain in positive degree admits an actual
primitive, supplied by the genuine deck-invariant flag contraction. -/
theorem singularCech_horizontal_primitive (n p : ℕ)
    (w : SingularCechTerms ρ U n (p+2))
    (hw : horizontal (singularCechBicomplex ρ U) (p+1) n w = 0) :
    ∃ z : SingularCechTerms ρ U n (p+1), horizontal (singularCechBicomplex ρ U) p n z = w := by
  let x := singularCechToFlags ρ U hU hcover n (p+1) w
  have hx : (smallSimplexIndexCover U hU hcover n).flagD ρ (p+2) x = 0 := by
    exact (singularCechToFlags_d ρ U hU hcover n (p+1) w).symm.trans
      ((congrArg (singularCechToFlags ρ U hU hcover n (p+2)) hw).trans (map_zero _))
  let y := (smallSimplexIndexCover U hU hcover n).flagH ρ (p+1) x
  refine ⟨(singularCechFlagEquiv ρ U hU hcover n p).symm y, ?_⟩
  apply (singularCechFlagEquiv ρ U hU hcover n (p+1)).injective
  change singularCechToFlags ρ U hU hcover n (p+1) _ = x
  rw [singularCechToFlags_d]
  change (smallSimplexIndexCover U hU hcover n).flagD ρ (p+1)
    ((singularCechFlagEquiv ρ U hU hcover n p) ((singularCechFlagEquiv ρ U hU hcover n p).symm y)) = x
  rw [LinearEquiv.apply_symm_apply]
  exact (smallSimplexIndexCover U hU hcover n).flag_primitive ρ (p+1) x hx

end TernaryPoly.SmoothSingularGlobal
