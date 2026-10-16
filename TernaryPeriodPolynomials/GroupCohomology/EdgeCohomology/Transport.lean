module

public import TernaryPeriodPolynomials.GroupCohomology.EdgeCohomology.TwistSubquotients

@[expose] public section


/-!
# Transport of first cohomology along an equivariant linear isomorphism of the coefficients

Formalized by Claude Sonnet 5.5.

`transportH1 e he : H¹(N, R) ≃ₗ H¹(N, R')` for an `N`-equivariant linear isomorphism `e : R ≃ₗ R'` (used to identify the radical
representation inside the edge group with the library's `planeRep n`, `lineRep n`, whose carriers agree and whose actions agree pointwise).
On cocycle classes it is the pointwise application of `e` (`transportH1_H1π`), and it commutes with the maps
`groupCohomology.map f T` of an endomorphism `f` of `N` whenever the coefficient maps correspond (`transportH1_map`).
-/

open TernaryPoly

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EdgeCohomology

open CategoryTheory groupCohomology TernaryPoly.LowDegreeHochschildSerre

section Transport

variable {N : Type} [Group N] {R R' : Rep.{0} ℚ N}

/-- Transport of the first cohomology along an equivariant linear isomorphism of the coefficients. -/
def transportH1 (e : R ≃ₗ[ℚ] R') (he : ∀ (g : N) (v : R), e (R.ρ g v) = R'.ρ g (e v)) :
    groupCohomology R 1 ≃ₗ[ℚ] groupCohomology R' 1 :=
  (groupCohomology.mapIso (MulEquiv.refl N) e (fun g => LinearMap.ext fun v => he g v) 1).toLinearEquiv

/-- The cocycle with transported values. -/
def transportC (e : R ≃ₗ[ℚ] R') (he : ∀ (g : N) (v : R), e (R.ρ g v) = R'.ρ g (e v))
    (c : cocycles₁ R) : cocycles₁ R' :=
  ⟨fun g => e (c.1 g), (mem_cocycles₁_iff _).mpr (fun g h => by
    have := (mem_cocycles₁_iff _).mp c.2 g h
    change e (c.1 (g * h)) = R'.ρ g (e (c.1 h)) + e (c.1 g)
    rw [this, map_add, he])⟩

theorem transportH1_H1π (e : R ≃ₗ[ℚ] R') (he : ∀ (g : N) (v : R), e (R.ρ g v) = R'.ρ g (e v))
    (c : cocycles₁ R) :
    transportH1 e he (H1π R c) = H1π R' (transportC e he c) := by
  unfold transportH1
  simp only [Iso.toLinearEquiv_apply, groupCohomology.mapIso_hom]
  rw [H1π_comp_map_apply]
  rfl

theorem transportH1_map (e : R ≃ₗ[ℚ] R') (he : ∀ (g : N) (v : R), e (R.ρ g v) = R'.ρ g (e v))
    (f : N →* N) (T : Rep.res f R ⟶ R) (T' : Rep.res f R' ⟶ R')
    (hT : ∀ v : R, e (T.hom v) = T'.hom (e v)) (x : groupCohomology R 1) :
    transportH1 e he (groupCohomology.map f T 1 x) = groupCohomology.map f T' 1 (transportH1 e he x) := by
  induction x using H1_induction_on with | h c => ?_
  rw [H1π_comp_map_apply, transportH1_H1π, transportH1_H1π, H1π_comp_map_apply]
  congr 1
  apply Subtype.ext
  funext g
  exact hT (c.1 (f g))

end Transport

end TernaryPeriodPolynomials.Argument.EdgeCohomology
