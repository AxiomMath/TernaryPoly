module

public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeHomology.SigmaH2

@[expose] public section


/-!
# The Hochschild-Serre isomorphism intertwines a `P`-level correspondence with the binary Hecke operator

Formalized by Claude Sonnet 5.5.
(the representatives
`C_c`, `C_∞` give `p T_2(p)`; "Transfer contributes `e_t`, ... Their product is `e_t λ²`").

`hsFarey_corr`: let `(S, f, c)` be a correspondence on `H₃(P, A)` such that

* `f` is injective, `f(S ∩ U) ⊆ U`, and on the radical `f|_{S ∩ U}` has a rational inverse `μ` of determinant `[U : S ∩ U]`;
* the image `Γ₀` of `S` in `P/U` is the preimage of the binary Hecke subgroup `{k | p ∣ k₀₁}` and `f` induces on it the binary
  Hecke map `k ↦ (k₀₀, k₀₁/p; p k₁₀, k₁₁)`;
* the coefficient map is `lin ∘ c = r · ρ_M(diag(1/p, 1)) ∘ lin`.

Then `hsFarey ∘ (tr_S ≫ H₃(f, c)) = r · T₂(p) ∘ hsFarey`, with `T₂(p) = heckeOp (binDatum p) M 1` the homology Hecke operator
of `diag(1/p, 1)` on `H₁(GL₂(ℤ), M)`.
-/

open CategoryTheory MonoidalCategory Representation Representation.Coinvariants CategoryTheory.Limits
open TernaryPeriodPolynomials.Argument.HochschildSerre TernaryPeriodPolynomials.Argument.GroupHomology
open TernaryPeriodPolynomials.Argument.GroupHomologyDescent (T2 U2)
open TernaryPeriodPolynomials.Argument.FareyTree TernaryPoly.RankTwoAugmentedFrames
open TernaryPoly.OrdinaryResidueParabolic

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HeckeHomology

section HS

open scoped Classical

variable {P : Type} [Group P] (U : Subgroup P) [U.Normal] (S : Subgroup P) [S.FiniteIndex] (f : S →* P)
  (hfU : ∀ s : S, (s : P) ∈ U → f s ∈ U) (hf : Function.Injective f) (A : Rep.{0} ℚ P)
  (c : Rep.res S.subtype A ⟶ Rep.res f A) [Module.Finite ℚ A.V] (eU : U2 ≃* U) (hA : ∀ u : U, A.ρ u = 1)

theorem homologyIsoRes_hom_gamma {Γ : Type} [Group Γ] (D : Rep.{0} ℚ Γ) (π : P ⧸ U →* Γ) (lin : A.V ≃ₗ[ℚ] D.V)
    (hcompat : ∀ (g : P) (a : A.V), lin (deltaG eU g • A.ρ g a) = D.ρ (π (QuotientGroup.mk g)) (lin a))
    (a : A.V) :
    (homologyIsoRes eU hA D π lin hcompat).hom.hom (gammaEquiv eU hA a) = lin a := by
  change lin ((gammaEquiv eU hA).symm (gammaEquiv eU hA a)) = lin a
  rw [LinearEquiv.symm_apply_apply]

variable (p : ℕ) [Fact p.Prime] (π : P ⧸ U →* IntegralGL) (hπ : Function.Surjective π)
  (hker : (π.ker : Set (P ⧸ U)).Finite) (hU3 : IsZero (groupHomology (Rep.res U.subtype A) 3))
  (M : Rep.{0} ℚ GL2) (lin : A.V ≃ₗ[ℚ] (Rep.res binIota M).V)
  (hcompat : ∀ (g : P) (a : A.V), lin (deltaG eU g • A.ρ g a) =
    (Rep.res binIota M).ρ (π (QuotientGroup.mk g)) (lin a))

include hf hA hπ hker in
/-- **The Hochschild-Serre isomorphism intertwines the `P`-level correspondence `(S, f, c)` with `r · T₂(p)`.** -/
theorem hsFarey_corr (μ : U →* U) (hμ : ∀ n : U1 U S, μ (nuU U S f hfU n) = (n : U))
    (hω : (omegaZ (muPsi eU μ HochschildSerre.e1) (muPsi eU μ HochschildSerre.e2) : ℚ) = (Fintype.card (RC (U1 U S)) : ℚ))
    (hne : (Fintype.card (RC (U1 U S)) : ℚ) ≠ 0)
    (hGamma : ∀ q, q ∈ G0 U S ↔ π q ∈ (binDatum p).S)
    (hchi : ∀ g : G0 U S, π (chi U S f hfU g) = (binDatum p).f ⟨π g, (hGamma g).mp g.2⟩)
    (r : ℚ) (hc : ∀ a, lin (c.hom a) = r • (M.ρ (C1 p)) (lin a)) (x : groupHomology A 3) :
    hsFarey U A π hπ hker hU3 (Rep.res binIota M) (homologyIsoRes eU hA (Rep.res binIota M) π lin hcompat)
        ((groupHomology.map f c 3).hom ((trR S A 3).hom x)) =
      r • (heckeOp (binDatum p) M 1).hom
        (hsFarey U A π hπ hker hU3 (Rep.res binIota M) (homologyIsoRes eU hA (Rep.res binIota M) π lin hcompat) x) := by
  have hz : ∀ w : (ZP U A).homology 2,
      (homologyIsoRes eU hA (Rep.res binIota M) π lin hcompat).hom.hom
          ((zetaH (G0 U S) (chi U S f hfU) (ZP U A) 2 (zetaC U S f hfU A c (liftBar S f hf))).hom w) =
        r • (M.ρ (C1 p)) ((homologyIsoRes eU hA (Rep.res binIota M) π lin hcompat).hom.hom w) := by
    intro w
    obtain ⟨a, rfl⟩ := (gammaEquiv eU hA).surjective w
    rw [zetaH_gammaEquiv U S f hfU A c eU hA hf μ hμ hω hne a,
      homologyIsoRes_hom_gamma U A eU hA (Rep.res binIota M) π lin hcompat,
      homologyIsoRes_hom_gamma U A eU hA (Rep.res binIota M) π lin hcompat]
    exact hc a
  have hcorr := congrArg (fun m => m.hom x) (corr_ZIso_hmuC U S f hfU A c hf 3)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hcorr
  have hE : (H1Iso (Rep.res binIota M)).toLinearEquiv
        (hsFarey U A π hπ hker hU3 (Rep.res binIota M)
          (homologyIsoRes eU hA (Rep.res binIota M) π lin hcompat)
          ((groupHomology.map f c 3).hom ((trR S A 3).hom x))) =
      r • (ResHeckeKer (binDatum p) M (binLift p)).hom ((H1Iso (Rep.res binIota M)).toLinearEquiv
        (hsFarey U A π hπ hker hU3 (Rep.res binIota M)
          (homologyIsoRes eU hA (Rep.res binIota M) π lin hcompat) x)) := by
    rw [hsFarey_eq_hsZ, hsFarey_eq_hsZ, hcorr]
    exact hsZ_hecke (ZP U A) p hπ hker (ZP_projective U A) (isZero_ZP_homology U A 3 hU3) M
      (homologyIsoRes eU hA (Rep.res binIota M) π lin hcompat) (G0 U S) hGamma (chi U S f hfU) hchi
      (zetaC U S f hfU A c (liftBar S f hf)) r hz _
  apply (H1Iso (Rep.res binIota M)).toLinearEquiv.injective
  have hH := congrArg (fun m => m.hom (hsFarey U A π hπ hker hU3 (Rep.res binIota M)
    (homologyIsoRes eU hA (Rep.res binIota M) π lin hcompat) x)) (binary_hecke_H1Iso p M)
  rw [map_smul]
  refine hE.trans (congrArg (fun z => r • z) ?_).symm
  exact hH

end HS

end TernaryPeriodPolynomials.Argument.HeckeHomology
