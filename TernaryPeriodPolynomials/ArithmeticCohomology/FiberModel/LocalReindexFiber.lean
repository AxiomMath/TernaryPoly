module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FiberModel.LocalReindex

@[expose] public section


/-!
# Fibrewise reindexing of local chains between the gluing and its conjugation-twisted copy

`epsFib` is post-composition of fibre coefficients with `ρ_{V₀}(k)`, from the fibre coefficients of
`wholeProjection` to those of the twisted covering `pTw k` (the two coverings have the same
underlying map up to the homeomorphism `GluedTw.homeo k`, hence the same fibres; only the equivariance
condition changes).  `epsLoc` is the induced chain map on geometric local chains, obtained from the
coinvariant reindexing `epsChain` through the chain isomorphisms `chainIso`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open scoped Classical

namespace TernaryPeriodPolynomials.Argument.FiberModel

open CategoryTheory AlgebraicTopology TernaryPoly TernaryPoly.FreeActionLinearization
  TernaryPoly.SingularLocalHomology TernaryPoly.EquivariantSingularResolution
  TernaryPoly.CoveringSingularOrbits TernaryPoly.SingularBoundaryRestriction
  TernaryPoly.SingularLocalCoefficient
  TernaryPoly.IntegralGL3Congruence TernaryPoly.SymmetricSpaceRationalGluing
  TernaryPoly.SymmetricSpaceArithmeticProper TernaryPoly.SymmetricSpaceBordifiedPrincipalSix
  TernaryPoly.SymmetricSpaceBordifiedQuotient
  TernaryPeriodPolynomials.Argument.DualityEquivariance
  TernaryPeriodPolynomials.Argument.GroupHomology

variable (k : IntegralGL) (V₀ : Rep.{0} ℚ IntegralGL)

/-- The fibre of the twisted covering over `b` is the fibre of the gluing over `b`. -/
def fibUntw {b : BordifiedOrbit} (e : Fiber (pTw k) b) : Fiber wholeProjection b :=
  ⟨e.val.val, e.property⟩

/-- The coefficient reindexing on fibre coefficients: post-composition with `ρ_{V₀}(k)`. -/
def epsFib (b : BordifiedOrbit)
    (c : FiberCoefficient wholeProjection wholeQuotientCovering (Rep.res principalSix.subtype V₀) b) :
    FiberCoefficient (pTw k) (twisted_whole_covering k) (Rep.res principalSix.subtype V₀) b :=
  ⟨fun e => V₀.ρ k (c.val (fibUntw k e)), fun g e => by
    have h1 : fibUntw k (fiberSmul (pTw k) (twisted_whole_covering k) g e) =
        fiberSmul wholeProjection wholeQuotientCovering (cjk k g) (fibUntw k e) := rfl
    have h2 := c.property (cjk k g) (fibUntw k e)
    change V₀.ρ k (c.val (fibUntw k (fiberSmul (pTw k) (twisted_whole_covering k) g e))) =
      V₀.ρ g.1 (V₀.ρ k (c.val (fibUntw k e)))
    rw [h1, h2]
    change V₀.ρ k (V₀.ρ (cjk k g).1 (c.val (fibUntw k e))) = _
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, cjk_val]
    congr 2
    group⟩

/-- The coefficient reindexing on local chains, transported from coinvariant chains. -/
def epsLoc : localChains wholeProjection wholeQuotientCovering (Rep.res principalSix.subtype V₀) ⟶
    localChains (pTw k) (twisted_whole_covering k) (Rep.res principalSix.subtype V₀) :=
  (chainIso wholeProjection wholeQuotientCovering (Rep.res principalSix.subtype V₀)).inv ≫
    epsChain k V₀ ≫
    (chainIso (pTw k) (twisted_whole_covering k) (Rep.res principalSix.subtype V₀)).hom

theorem jInv_chainElement (n : ℕ) (τ : SingularSimplex (TopCat.of Glued) n) :
    (jInvChains k n).hom (chainElement principalSix (TopCat.of Glued) n τ) =
      chainElement principalSix (TopCat.of (GluedTw k)) n (projection (jInvMap k) n τ) := by
  have h := congrArg (fun m => m.hom (1 : ℚ)) (SingularCoverNaturality.generator_map (jInvMap k) n τ)
  exact h

/-- The lift of a simplex of the gluing to a simplex of the twisted gluing. -/
def jInvLift {n : ℕ} {σ : SingularSimplex (TopCat.of BordifiedOrbit) n} (τ : Lifts wholeProjection σ) :
    Lifts (pTw k) σ :=
  ⟨projection (jInvMap k) n τ.val, τ.property⟩

theorem epsChain_generator (n : ℕ) (τ : SingularSimplex (TopCat.of Glued) n)
    (v : Rep.res principalSix.subtype V₀) :
    ((epsChain k V₀).f n).hom (generator principalSix (TopCat.of Glued)
        (Rep.res principalSix.subtype V₀) n τ v) =
      generator principalSix (TopCat.of (GluedTw k)) (Rep.res principalSix.subtype V₀) n
        (projection (jInvMap k) n τ) (V₀.ρ k v) := by
  change ((epsHomAt k V₀ n).hom (Rep.coinvariantsTensorMk _ _ v
    (chainElement principalSix (TopCat.of Glued) n τ))) = _
  rw [epsHomAt_mk, jInv_chainElement]
  rfl

set_option maxRecDepth 4000 in
theorem epsLoc_single (n : ℕ) (σ : SingularSimplex (TopCat.of BordifiedOrbit) n)
    (c : FiberCoefficient wholeProjection wholeQuotientCovering
      (Rep.res principalSix.subtype V₀) (atVertex σ)) :
    ((epsLoc k V₀).f n).hom
        (DFinsupp.single (β := fun σ' : SingularSimplex (TopCat.of BordifiedOrbit) n =>
          FiberCoefficient wholeProjection wholeQuotientCovering
            (Rep.res principalSix.subtype V₀) (atVertex σ')) σ c) =
      DFinsupp.single (β := fun σ' : SingularSimplex (TopCat.of BordifiedOrbit) n =>
          FiberCoefficient (pTw k) (twisted_whole_covering k)
            (Rep.res principalSix.subtype V₀) (atVertex σ')) σ (epsFib k V₀ (atVertex σ) c) := by
  let V := Rep.res principalSix.subtype V₀
  apply (degreeEquiv (pTw k) (twisted_whole_covering k) V n).symm.injective
  let τ := chosenLift wholeProjection wholeQuotientCovering n σ
  have e : ∀ x, ((epsLoc k V₀).f n).hom x =
      (degreeEquiv (pTw k) (twisted_whole_covering k) V n)
        (((epsChain k V₀).f n).hom (((chainIso wholeProjection wholeQuotientCovering V).inv.f n).hom x)) :=
    fun x => rfl
  have hL : (degreeEquiv (pTw k) (twisted_whole_covering k) V n).symm
      (((epsLoc k V₀).f n).hom (DFinsupp.single (β := fun σ' : SingularSimplex
        (TopCat.of BordifiedOrbit) n => FiberCoefficient wholeProjection wholeQuotientCovering
          V (atVertex σ')) σ c)) =
      ((epsChain k V₀).f n).hom (((chainIso wholeProjection wholeQuotientCovering V).inv.f n).hom
        (DFinsupp.single (β := fun σ' : SingularSimplex (TopCat.of BordifiedOrbit) n =>
          FiberCoefficient wholeProjection wholeQuotientCovering V (atVertex σ')) σ c)) := by
    exact (congrArg (degreeEquiv (pTw k) (twisted_whole_covering k) V n).symm (e _)).trans
      (LinearEquiv.symm_apply_apply _ _)
  have h1 := chainIso_inv_single wholeProjection wholeQuotientCovering V n τ c
  have h2 := degreeEquiv_symm_single_lift (pTw k) (twisted_whole_covering k) V n (jInvLift k τ)
    (epsFib k V₀ (atVertex σ) c)
  refine hL.trans ((congrArg ((epsChain k V₀).f n).hom h1).trans ?_)
  refine (epsChain_generator k V₀ n τ.val _).trans ?_
  exact h2.symm


end TernaryPeriodPolynomials.Argument.FiberModel
