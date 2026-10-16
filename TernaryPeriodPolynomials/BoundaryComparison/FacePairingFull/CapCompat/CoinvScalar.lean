module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.KroneckerRep
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.PairingComparison
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.SingularCap
public import TernaryPeriodPolynomials.Topology.TopHomology.FundamentalTie

@[expose] public section


/-!
# Coinvariants of the equivariant singular chains of a quotient cover

For a quotient covering `p : E ⟶ B` with deck group `G`, pushing singular chains forward is `G`-invariant and induces
a bijection `coinvToScalar` from the coinvariants of the equivariant singular chains `chainRep G E n` onto the scalar
singular chains of the base.  It commutes with the coinvariant differential `coinvD` and the singular boundary, so
a chain is a coinvariant cycle (`IsCoinvCycle`, i.e. killed by all invariant functionals) exactly when its pushforward
is a cycle of the base; every base cycle is the pushforward of a coinvariant cycle, and a relation between coinvariant
classes modulo boundaries descends to a relation between pushforwards modulo base boundaries.

* `coinvToScalar`, `coinvToScalar_mk`, `coinvToScalar_bijective` (B1.1-2);
* `coinvToScalar_coinvD` (B1.3);
* `isCoinvCycle_iff_mk_d`, `isCoinvCycle_iff` (B1.4);
* `exists_coinvCycle_lift` (B1.5), `pushforward_sub_smul_boundary(_four)` (B1.6).

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits MonoidalCategory
open TernaryPoly TernaryPoly.EquivariantSingularResolution TernaryPoly.SingularLocalHomology
open TernaryPoly.FreeActionLinearization TernaryPoly.CoveringSingularOrbits TernaryPoly.SingularLocalCap
open SphereOddDegree SphereOddDegree.AffineBarycentricSubdivision
open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
open TernaryPeriodPolynomials.Argument.KroneckerRep

noncomputable section

namespace TernaryPeriodPolynomials.Argument.CoinvScalar

section Generic

variable {Γ : Type} [Group Γ] (C : ChainComplex (Rep.{0} ℚ Γ) ℕ)

/-- A coinvariant class vanishes exactly when every invariant functional kills a representative. -/
theorem mk_eq_zero_iff_forall_hom {X : Rep.{0} ℚ Γ} (x : X) :
    Representation.Coinvariants.mk X.ρ x = 0 ↔ ∀ φ : X ⟶ 𝟙_ (Rep.{0} ℚ Γ), φ.hom x = 0 := by
  constructor
  · intro h φ
    have h1 : coinvHom X ℚ (show X ⟶ Rep.trivial ℚ Γ ℚ from φ) (Representation.Coinvariants.mk X.ρ x) = 0 := by
      rw [h, map_zero]
    exact h1
  · intro h
    refine (Module.forall_dual_apply_eq_zero_iff ℚ _).1 (fun ψ => ?_)
    exact h ((coinvHom X ℚ).symm ψ : X ⟶ Rep.trivial ℚ Γ ℚ)

theorem isCoinvCycle_iff_mk_d {m : ℕ} (Ω : C.X (m+1)) :
    IsCoinvCycle Ω ↔ Representation.Coinvariants.mk (C.X m).ρ ((C.d (m+1) m).hom Ω) = 0 :=
  (mk_eq_zero_iff_forall_hom _).symm

end Generic

section Cover

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) (hp : IsQuotientCoveringMap p G)

theorem chainElement_eq (n : ℕ) (σ : SingularSimplex E n) :
    chainElement G E n σ = chainGenerator ℚ E n σ := rfl

theorem singularChainMap_chainElement (n : ℕ) (σ : SingularSimplex E n) :
    (singularChainMap ℚ p n).hom (chainElement G E n σ) = chainGenerator ℚ B n (projection p n σ) :=
  singularChainMap_generator ℚ p n σ

include hp in
theorem singularChainMap_invariant (n : ℕ) (g : G) :
    (singularChainMap ℚ p n).hom ∘ₗ (chainRep G E n).ρ g = (singularChainMap ℚ p n).hom := by
  apply chainRep_linear_ext
  intro σ
  change (singularChainMap ℚ p n).hom ((chainRep G E n).ρ g (chainElement G E n σ)) = _
  rw [chainElement_smul, singularChainMap_chainElement, singularChainMap_chainElement, projection_smul p hp]

/-- **(B1.1)** The map from the coinvariants of the equivariant singular chains of a quotient cover to the singular
chains of the base induced by pushing chains forward. -/
def coinvToScalar (n : ℕ) : (chainRep G E n).ρ.Coinvariants →ₗ[ℚ] (scalarChains B).X n :=
  Representation.Coinvariants.lift (chainRep G E n).ρ (singularChainMap ℚ p n).hom
    (singularChainMap_invariant p hp n)

theorem coinvToScalar_mk (n : ℕ) (x : chainRep G E n) :
    coinvToScalar p hp n (Representation.Coinvariants.mk (chainRep G E n).ρ x) =
      (singularChainMap ℚ p n).hom x :=
  Representation.Coinvariants.lift_mk _ _ _ _

open scoped Classical

/-- A linear section of the pushforward of singular chains, built from the chosen lifts of base simplices. -/
def chainSection (n : ℕ) : singularChainGroup ℚ B n ⟶ singularChainGroup ℚ E n :=
  Limits.Sigma.desc (fun σ : singularSimplices B n =>
    Sigma.ι (fun _ : singularSimplices E n => ModuleCat.of ℚ ℚ) (chosenLift p hp n σ).val)

theorem chainSection_generator (n : ℕ) (σ : SingularSimplex B n) :
    (chainSection p hp n).hom (chainGenerator ℚ B n σ) = chainGenerator ℚ E n (chosenLift p hp n σ).val :=
  congrArg (fun t : ModuleCat.of ℚ ℚ ⟶ singularChainGroup ℚ E n => t.hom (1 : ℚ))
    (Limits.Sigma.ι_comp_desc (fun τ : singularSimplices B n =>
      Sigma.ι (fun _ : singularSimplices E n => ModuleCat.of ℚ ℚ) (chosenLift p hp n τ).val) σ :
      Sigma.ι (fun _ : singularSimplices B n => ModuleCat.of ℚ ℚ) σ ≫ chainSection p hp n =
        Sigma.ι (fun _ : singularSimplices E n => ModuleCat.of ℚ ℚ) (chosenLift p hp n σ).val)

theorem mk_chainSection_pushforward (n : ℕ) (x : chainRep G E n) :
    Representation.Coinvariants.mk (chainRep G E n).ρ
        ((chainSection p hp n).hom ((singularChainMap ℚ p n).hom x)) =
      Representation.Coinvariants.mk (chainRep G E n).ρ x := by
  have h : (Representation.Coinvariants.mk (chainRep G E n).ρ ∘ₗ (chainSection p hp n).hom ∘ₗ
      (singularChainMap ℚ p n).hom) = Representation.Coinvariants.mk (chainRep G E n).ρ := by
    apply chainRep_linear_ext
    intro σ
    change Representation.Coinvariants.mk (chainRep G E n).ρ
        ((chainSection p hp n).hom ((singularChainMap ℚ p n).hom (chainElement G E n σ))) = _
    rw [singularChainMap_chainElement, chainSection_generator]
    obtain ⟨g, hg⟩ := (projection_eq_iff_orbit p hp n (chosenLift p hp n (projection p n σ)).val σ).1
      (chosenLift p hp n (projection p n σ)).property
    rw [chainElement_eq, ← hg, ← chainElement_eq, ← chainElement_smul]
    exact Representation.Coinvariants.mk_self_apply _ g _
  exact LinearMap.congr_fun h x

/-- **(B1.2)** The coinvariants of the equivariant singular chains of a quotient cover are the singular chains of
the base. -/
theorem coinvToScalar_bijective (n : ℕ) : Function.Bijective (coinvToScalar p hp n) := by
  constructor
  · intro a b hab
    have hL : ∀ c : (chainRep G E n).ρ.Coinvariants,
        Representation.Coinvariants.mk (chainRep G E n).ρ ((chainSection p hp n).hom (coinvToScalar p hp n c)) = c := by
      intro c
      induction c using Representation.Coinvariants.induction_on with
      | h x =>
        rw [coinvToScalar_mk]
        exact mk_chainSection_pushforward p hp n x
    rw [← hL a, ← hL b, hab]
  · intro y
    obtain ⟨x, hx⟩ := singularChainMap_surjective p hp n y
    exact ⟨Representation.Coinvariants.mk (chainRep G E n).ρ x, by rw [coinvToScalar_mk]; exact hx⟩

/-- **(B1.3)** Compatibility with the differentials. -/
theorem coinvToScalar_coinvD (n : ℕ) (z : ((equivariantChains G E).X (n+1)).ρ.Coinvariants) :
    coinvToScalar p hp n (coinvD (equivariantChains G E) (n+1) n z) =
      ((scalarChains B).d (n+1) n).hom (coinvToScalar p hp (n+1) z) := by
  induction z using Representation.Coinvariants.induction_on with
  | h x =>
    rw [coinvD_mk]
    erw [coinvToScalar_mk p hp n, coinvToScalar_mk p hp (n+1)]
    exact (congrArg (fun t => t.hom x) (singularChainMap_boundary ℚ p n)).symm

include hp in
/-- **(B1.4)** A chain of the equivariant singular complex is a coinvariant cycle exactly when its pushforward is a
cycle of the base. -/
theorem isCoinvCycle_iff (n : ℕ) (ω : (equivariantChains G E).X (n+1)) :
    IsCoinvCycle ω ↔ ((scalarChains B).d (n+1) n).hom ((singularChainMap ℚ p (n+1)).hom ω) = 0 := by
  rw [isCoinvCycle_iff_mk_d]
  have hinj := (coinvToScalar_bijective p hp n).1
  have key : coinvToScalar p hp n (Representation.Coinvariants.mk ((equivariantChains G E).X n).ρ
      (((equivariantChains G E).d (n+1) n).hom ω)) =
      ((scalarChains B).d (n+1) n).hom ((singularChainMap ℚ p (n+1)).hom ω) := by
    have h1 := coinvToScalar_coinvD p hp n (Representation.Coinvariants.mk _ ω)
    rw [coinvD_mk] at h1
    exact h1.trans (congrArg (fun t => ((scalarChains B).d (n+1) n).hom t) (coinvToScalar_mk p hp (n+1) ω))
  rw [← key, ← map_zero (coinvToScalar p hp n)]
  exact hinj.eq_iff.symm

include hp in
/-- **(B1.5)** Fundamental-class lift: every cycle of the base singular complex is the pushforward of a coinvariant
cycle of the equivariant singular complex. -/
theorem exists_coinvCycle_lift (n : ℕ) (c : (scalarChains B).X (n+1))
    (hc : ((scalarChains B).d (n+1) n).hom c = 0) :
    ∃ ω : (equivariantChains G E).X (n+1), IsCoinvCycle ω ∧ (singularChainMap ℚ p (n+1)).hom ω = c := by
  obtain ⟨ω, hω⟩ := singularChainMap_surjective p hp (n+1) c
  refine ⟨ω, (isCoinvCycle_iff p hp n ω).2 ?_, hω⟩
  rw [hω]
  exact hc

include hp in
/-- **(B1.6)** Homology relation: a relation between coinvariant classes modulo boundaries of the coinvariant complex
descends to a relation between the pushforwards modulo boundaries of the base singular complex. -/
theorem pushforward_sub_smul_boundary (n : ℕ) (ω₁ ω₂ : (equivariantChains G E).X (n+1)) (c : ℚ)
    (h : Representation.Coinvariants.mk ((equivariantChains G E).X (n+1)).ρ ω₁ -
        c • Representation.Coinvariants.mk ((equivariantChains G E).X (n+1)).ρ ω₂ ∈
      LinearMap.range (coinvD (equivariantChains G E) (n+2) (n+1))) :
    ∃ τ : (scalarChains B).X (n+2), ((scalarChains B).d (n+2) (n+1)).hom τ =
      (singularChainMap ℚ p (n+1)).hom ω₁ - c • (singularChainMap ℚ p (n+1)).hom ω₂ := by
  obtain ⟨z, hz⟩ := h
  refine ⟨coinvToScalar p hp (n+2) z, ?_⟩
  rw [← coinvToScalar_coinvD p hp (n+1) z, hz]
  refine ((map_sub (coinvToScalar p hp (n+1)) _ _).trans
    (congrArg₂ (· - ·) (coinvToScalar_mk p hp (n+1) ω₁) ?_))
  exact (map_smul (coinvToScalar p hp (n+1)) c _).trans (congrArg (c • ·) (coinvToScalar_mk p hp (n+1) ω₂))

include hp in
/-- **(B1.6)** in degree four. -/
theorem pushforward_sub_smul_boundary_four (ω₁ ω₂ : (equivariantChains G E).X 4) (c : ℚ)
    (h : Representation.Coinvariants.mk ((equivariantChains G E).X 4).ρ ω₁ -
        c • Representation.Coinvariants.mk ((equivariantChains G E).X 4).ρ ω₂ ∈
      LinearMap.range (coinvD (equivariantChains G E) 5 4)) :
    ∃ τ : (scalarChains B).X 5, ((scalarChains B).d 5 4).hom τ =
      (singularChainMap ℚ p 4).hom ω₁ - c • (singularChainMap ℚ p 4).hom ω₂ :=
  pushforward_sub_smul_boundary p hp 3 ω₁ ω₂ c h

end Cover

end TernaryPeriodPolynomials.Argument.CoinvScalar
