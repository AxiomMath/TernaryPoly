module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.BoundaryDescent.CoinvGroup
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.BoundaryDescent.CoinvBoundary

@[expose] public section


/-!
# Compatibility of the boundary descent with the boundary map `j_*`

Formalized by Claude Sonnet 5.5.  Proof of Proposition 3.4,
("The same finite-cover descent applies to boundary homology and commutes with its map to ordinary homology, so exact averaging preserves the
surjection at level `K`").

`jN` is the neat-level map `j_* : H₃(∂X̄_{Γ(6)}; 𝓜) → H₃(Γ(6), E)` (with `Γ(6)` realised as `Γ(6)`-in-`H`); it intertwines the geometric action
`repBd` with the conjugation action `repN` (`jN_equivariant`, from `boundaryToGroup_equivariant`).  `jCoinv` is the induced map of coinvariants.
`jQH_boundaryCoinvEquiv`: the square
`jQH ∘ boundaryCoinvEquiv = groupCoinvEquiv ∘ jCoinv`  (the descent isomorphisms are compatible with the boundary map).
`jCoinv_surjective`, `jQH_surjective`: surjectivity of the neat-level `j_*` is inherited by the coinvariants and by `j^H_*`.
-/

open CategoryTheory Limits HomologicalComplex TernaryPoly TernaryPoly.IntegralGL3Congruence Representation
  TernaryPoly.OrdinaryBoundaryActualEvaluation
  TernaryPoly.SymmetricSpaceBoundaryFull TernaryPoly.SymmetricSpaceBoundaryFullTransfer
  TernaryPoly.EquivariantSingularSmall TernaryPoly.SymmetricSpaceBoundaryIncidenceHomology
  TernaryPoly.RationalCohomologyDescent
  TernaryPoly.SingularLocalHomology TernaryPoly.ModThreeGoodAction TernaryPoly.OrdinaryBoundaryCone
open TernaryPeriodPolynomials.Argument.GroupHomology
open TernaryPeriodPolynomials.Argument.FiberModel
open TernaryPeriodPolynomials.Argument.Lemma33.LevelG
open TernaryPeriodPolynomials.Argument.Lemma33.Naturality

noncomputable section
namespace TernaryPeriodPolynomials.Argument.Lemma33.BoundaryDescent

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

section Compat

variable (H : Subgroup IntegralGL) (hH : principalSix ≤ H) (V₀ : Rep.{0} ℚ IntegralGL)

theorem liftN_inv_cAct (g : ↥H) (x : groupHomology (Rep.res principalSix.subtype V₀) 3) :
    (liftN H hH V₀).inv.hom (cAct principalSix V₀ 3 g.1 x) =
      cAct (NH H) (MH H V₀) 3 g ((liftN H hH V₀).inv.hom x) := by
  have h := liftN_cAct H hH V₀ g ((liftN H hH V₀).inv.hom x)
  have h2 : (liftN H hH V₀).hom.hom ((liftN H hH V₀).inv.hom x) = x := by
    change ((liftN H hH V₀).inv ≫ (liftN H hH V₀).hom).hom x = x
    rw [Iso.inv_hom_id]; rfl
  rw [h2] at h
  rw [← h]
  change ((liftN H hH V₀).hom ≫ (liftN H hH V₀).inv).hom _ = _
  rw [Iso.hom_inv_id]; rfl

/-- **The neat-level boundary map `j_*`**, valued in `H₃(Γ(6)-in-H, Res_H V₀)`. -/
def jN : Bd V₀ →ₗ[ℚ] groupHomology (Rep.res (NH H).subtype (MH H V₀)) 3 :=
  (liftN H hH V₀).inv.hom ∘ₗ (SymmetricSpaceBoundaryDuality.boundaryToGroup (Rep.res principalSix.subtype V₀) 3).hom

/-- `j_*` intertwines the geometric action of `H` on boundary homology with the conjugation action on `H₃(Γ(6), E)`. -/
theorem jN_equivariant (g : ↥H) (c : Bd V₀) : jN H hH V₀ (repBd V₀ H g c) = repN H V₀ g (jN H hH V₀ c) := by
  have h := ConcreteCategory.congr_hom (boundaryToGroup_equivariant V₀ g.1) c
  change (liftN H hH V₀).inv.hom ((SymmetricSpaceBoundaryDuality.boundaryToGroup (Rep.res principalSix.subtype V₀) 3).hom
    ((homologyMap (bAct V₀ g.1) 3).hom c)) = cAct (NH H) (MH H V₀) 3 g ((liftN H hH V₀).inv.hom
      ((SymmetricSpaceBoundaryDuality.boundaryToGroup (Rep.res principalSix.subtype V₀) 3).hom c))
  rw [show (SymmetricSpaceBoundaryDuality.boundaryToGroup (Rep.res principalSix.subtype V₀) 3).hom
    ((homologyMap (bAct V₀ g.1) 3).hom c) = cAct principalSix V₀ 3 g.1
      ((SymmetricSpaceBoundaryDuality.boundaryToGroup (Rep.res principalSix.subtype V₀) 3).hom c) from h]
  exact liftN_inv_cAct H hH V₀ g _

/-- The map `j_*` on `H`-coinvariants. -/
def jCoinv : Coinvariants (repBd V₀ H) →ₗ[ℚ] Coinvariants (repN H V₀) :=
  Coinvariants.lift (repBd V₀ H) (Coinvariants.mk (repN H V₀) ∘ₗ jN H hH V₀) (fun g => LinearMap.ext fun c => by
    simp only [LinearMap.comp_apply, jN_equivariant, Coinvariants.mk_self_apply])

@[simp]
theorem jCoinv_mk (c : Bd V₀) :
    jCoinv H hH V₀ (Coinvariants.mk (repBd V₀ H) c) = Coinvariants.mk (repN H V₀) (jN H hH V₀ c) := rfl

/-- **The descent isomorphisms are compatible with the boundary map**: `j^H_* ∘ (boundary descent) = (group descent) ∘ j_*`. -/
theorem jQH_boundaryCoinvEquiv (w : Coinvariants (repBd V₀ H)) :
    jQH H hH V₀ (boundaryCoinvEquiv H hH V₀ w) = groupCoinvEquiv H V₀ (jCoinv H hH V₀ w) := by
  induction w using Coinvariants.induction_on with
  | h c =>
    rw [boundaryCoinvEquiv_mk, jQH_qBdH, jCoinv_mk, groupCoinvEquiv_mk]
    rfl

/-- The map `j_*` on `Δ`-coinvariants, `Δ = H/Γ(6)`. -/
def jCoinvDelta : Coinvariants (repDeltaBd H V₀) →ₗ[ℚ] Coinvariants (repDeltaN H V₀) :=
  Coinvariants.lift (repDeltaBd H V₀) (Coinvariants.mk (repDeltaN H V₀) ∘ₗ jN H hH V₀) (fun q => by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    exact LinearMap.ext fun c => by
      change Coinvariants.mk (repDeltaN H V₀) (jN H hH V₀ (repBd V₀ H g c)) = Coinvariants.mk (repDeltaN H V₀) (jN H hH V₀ c)
      rw [jN_equivariant]
      exact Coinvariants.mk_self_apply (repDeltaN H V₀) (g : ↥H ⧸ NH H) _)

@[simp]
theorem jCoinvDelta_mk (c : Bd V₀) :
    jCoinvDelta H hH V₀ (Coinvariants.mk (repDeltaBd H V₀) c) = Coinvariants.mk (repDeltaN H V₀) (jN H hH V₀ c) := rfl

/-- **Compatibility with the boundary map, for the `Δ`-coinvariants.** -/
theorem jQH_boundaryCoinvDelta (w : Coinvariants (repDeltaBd H V₀)) :
    jQH H hH V₀ (boundaryCoinvDelta H hH V₀ w) = groupCoinvDelta H V₀ (jCoinvDelta H hH V₀ w) := by
  induction w using Coinvariants.induction_on with
  | h c =>
    rw [boundaryCoinvDelta_mk, jQH_qBdH, jCoinvDelta_mk, groupCoinvDelta_mk]
    rfl

theorem jN_surjective (h : Function.Surjective (SymmetricSpaceBoundaryDuality.boundaryToGroup
    (Rep.res principalSix.subtype V₀) 3).hom) : Function.Surjective (jN H hH V₀) := by
  intro y
  obtain ⟨x, hx⟩ := h ((liftN H hH V₀).hom.hom y)
  refine ⟨x, ?_⟩
  change (liftN H hH V₀).inv.hom ((SymmetricSpaceBoundaryDuality.boundaryToGroup (Rep.res principalSix.subtype V₀) 3).hom x) = y
  rw [hx]
  change ((liftN H hH V₀).hom ≫ (liftN H hH V₀).inv).hom y = y
  rw [Iso.hom_inv_id]; rfl

/-- **Exact averaging preserves the surjection onto ordinary homology**: if the neat-level boundary map is surjective,
so is the induced map of `H`-coinvariants. -/
theorem jCoinv_surjective (h : Function.Surjective (SymmetricSpaceBoundaryDuality.boundaryToGroup
    (Rep.res principalSix.subtype V₀) 3).hom) : Function.Surjective (jCoinv H hH V₀) := by
  intro w'
  obtain ⟨z, rfl⟩ := Coinvariants.mk_surjective (repN H V₀) w'
  obtain ⟨c, rfl⟩ := jN_surjective H hH V₀ h z
  exact ⟨Coinvariants.mk (repBd V₀ H) c, rfl⟩

theorem jCoinvDelta_surjective (h : Function.Surjective (SymmetricSpaceBoundaryDuality.boundaryToGroup
    (Rep.res principalSix.subtype V₀) 3).hom) : Function.Surjective (jCoinvDelta H hH V₀) := by
  intro w'
  obtain ⟨z, rfl⟩ := Coinvariants.mk_surjective (repDeltaN H V₀) w'
  obtain ⟨c, rfl⟩ := jN_surjective H hH V₀ h z
  exact ⟨Coinvariants.mk (repDeltaBd H V₀) c, rfl⟩

/-- **The `H`-level boundary map `j^H_* : H₃(∂X̄_H; 𝓜) → H₃(H, E)` is surjective** as soon as the neat-level one is. -/
theorem jQH_surjective (h : Function.Surjective (SymmetricSpaceBoundaryDuality.boundaryToGroup
    (Rep.res principalSix.subtype V₀) 3).hom) : Function.Surjective (jQH H hH V₀) := by
  intro y
  obtain ⟨w, hw⟩ := jCoinv_surjective H hH V₀ h ((groupCoinvEquiv H V₀).symm y)
  refine ⟨boundaryCoinvEquiv H hH V₀ w, ?_⟩
  rw [jQH_boundaryCoinvEquiv, hw, LinearEquiv.apply_symm_apply]

end Compat

end TernaryPeriodPolynomials.Argument.Lemma33.BoundaryDescent
