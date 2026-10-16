module

public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeHomology.ZetaAmbient
public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeHomology.RadicalTransfer
public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.HeckeFarey

@[expose] public section


/-!
# The quotient correspondence `ζ` on `H₂(Z) ≅ A`: the radical factor

Formalized by Claude Sonnet 5.5.
Paper: "Transfer contributes `e_t`, inverse
conjugation on the radical's top homology contributes `λ²/det C`".

For the quotient correspondence `(Γ₀, χ, ζ)` of `ZetaMap.lean` attached to `(S, f, c)` and a lift of `(S, f)` to the bar resolution,
the map `zetaH` induced by `ζ` on `H₂(ZP U A)`, in the coordinates `gammaEquiv : A ≅ H₂(ZP U A)`, is the coefficient map `c`
(`zetaH_gammaEquiv`), provided the radical data satisfy the hypotheses of `radical_corr`: a rational inverse `μ` of
`ν = f|_{S ∩ U}` with `μ ∘ ν = incl` whose determinant equals the index `[U : S ∩ U]`.
-/

open CategoryTheory MonoidalCategory Representation Representation.Coinvariants
open TernaryPeriodPolynomials.Argument.HochschildSerre TernaryPeriodPolynomials.Argument.GroupHomology
open TernaryPeriodPolynomials.Argument.GroupHomologyDescent (T2 U2)

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HeckeHomology

section H2

open scoped Classical

variable {P : Type} [Group P] (U : Subgroup P) [U.Normal] (S : Subgroup P) [S.FiniteIndex] (f : S →* P)
  (hfU : ∀ s : S, (s : P) ∈ U → f s ∈ U) (A : Rep.{0} ℚ P)
  (c : Rep.res S.subtype A ⟶ Rep.res f A)

omit [U.Normal] [S.FiniteIndex] in
theorem nuU_injective (hf : Function.Injective f) : Function.Injective (nuU U S f hfU) := by
  intro a b h
  have h1 : f (incl1 U S a) = f (incl1 U S b) := congrArg Subtype.val h
  have h2 := hf h1
  have h3 : ((incl1 U S a : S) : P) = ((incl1 U S b : S) : P) := congrArg Subtype.val h2
  exact Subtype.ext (Subtype.ext h3)

omit [U.Normal] [S.FiniteIndex] in
theorem lamU_overId (hf : Function.Injective f) :
    LiftGOverId (RU U) (U1 U S) (nuU U S f hfU) (lamU U S f hfU (liftBar S f hf)) := by
  have h := liftBar_overId S f hf
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  refine LinearMap.ext fun v => ?_
  have h' := congrArg (fun t => t.hom v) h
  exact h'

omit [U.Normal] [S.FiniteIndex] in
theorem nuU_hproj (hf : Function.Injective f) (q : ℕ) :
    Projective ((Rep.resFunctor (nuU U S f hfU)).obj ((RU U).complex.X q)) := by
  have : Projective ((RU U).complex.X q) := (RU U).projective q
  exact projective_res_of_injective (nuU U S f hfU) (nuU_injective U S f hfU hf) _

variable [Module.Finite ℚ A.V] (eU : U2 ≃* U) (hA : ∀ u : U, A.ρ u = 1)

omit [U.Normal] [S.FiniteIndex] [Module.Finite ℚ A.V] in
theorem cU_eq_cTriv :
    cU U S f hfU A c = cTriv hA (U1 U S).subtype (nuU U S f hfU) c.hom.toLinearMap :=
  Rep.hom_ext (Representation.IntertwiningMap.ext rfl)

omit [U.Normal] in
/-- **The correspondence on `H₂(U, A)`**: transfer to `S ∩ U` followed by `H₂(ν, c)` multiplies the fundamental class by
`[U : S ∩ U] / det μ`, for a rational inverse `μ` of `ν`. -/
theorem corr_H2_gamma (μ : U →* U) (hμ : ∀ n : U1 U S, μ (nuU U S f hfU n) = (n : U))
    (hω : (omegaZ (muPsi eU μ e1) (muPsi eU μ e2) : ℚ) = (Fintype.card (RC (U1 U S)) : ℚ))
    (hne : (Fintype.card (RC (U1 U S)) : ℚ) ≠ 0) (x : A.V) :
    (groupHomology.map (nuU U S f hfU) (cU U S f hfU A c) 2).hom
        ((trR (U1 U S) (Rep.res U.subtype A) 2).hom ((PsiIso eU hA).hom.hom (kappa0 A.V x))) =
      (PsiIso eU hA).hom.hom (kappa0 A.V (c.hom x)) := by
  have h := radical_corr eU hA (U1 U S) (nuU U S f hfU) μ hμ c.hom.toLinearMap x
  rw [hω, ← cU_eq_cTriv U S f hfU A c hA] at h
  have h2 := smul_right_injective (groupHomology (Rep.res U.subtype A) 2) hne h
  exact h2

/-- **`ζ` acts on `H₂(Z) ≅ A` as the coefficient map `c`** (the radical factor is `1`). -/
theorem zetaH_gammaEquiv (hf : Function.Injective f) (μ : U →* U) (hμ : ∀ n : U1 U S, μ (nuU U S f hfU n) = (n : U))
    (hω : (omegaZ (muPsi eU μ e1) (muPsi eU μ e2) : ℚ) = (Fintype.card (RC (U1 U S)) : ℚ))
    (hne : (Fintype.card (RC (U1 U S)) : ℚ) ≠ 0) (x : A.V) :
    (zetaH (G0 U S) (chi U S f hfU) (ZP U A) 2 (zetaC U S f hfU A c (liftBar S f hf))).hom
        (gammaEquiv eU hA x) = gammaEquiv eU hA (c.hom x) := by
  have hzz : zetaF (G0 U S) (chi U S f hfU) (zetaC U S f hfU A c (liftBar S f hf)) =
      zU U S f hfU A c (liftBar S f hf) := by
    refine HomologicalComplex.hom_ext _ _ fun j => ?_
    rfl
  have hcorr := corr_resolution_generic (Rep.res U.subtype A) (RU U) (U1 U S) (nuU U S f hfU)
    (cU U S f hfU A c) (lamU U S f hfU (liftBar S f hf)) (lamU_overId U S f hfU hf)
    (nuU_hproj U S f hfU hf) 2
  have key : ∀ z, (HomologicalComplex.homologyMap
      (zetaF (G0 U S) (chi U S f hfU) (zetaC U S f hfU A c (liftBar S f hf))) 2).hom
      ((eN U A 2).hom.hom z) =
      (eN U A 2).hom.hom ((groupHomology.map (nuU U S f hfU) (cU U S f hfU A c) 2).hom
        ((trR (U1 U S) (Rep.res U.subtype A) 2).hom z)) := by
    intro z
    rw [hzz]
    exact congrArg (fun m => m.hom z) hcorr
  refine (zetaH_forget (G0 U S) (chi U S f hfU) 2 (zetaC U S f hfU A c (liftBar S f hf)) _).trans ?_
  refine congrArg (((ZP U A).sc 2).mapHomologyIso (forget₂ (Rep.{0} ℚ (P ⧸ U)) (ModuleCat ℚ))).hom.hom ?_
  refine (key _).trans ?_
  exact congrArg (eN U A 2).hom.hom (corr_H2_gamma U S f hfU A c eU hA μ hμ hω hne x)

end H2

end TernaryPeriodPolynomials.Argument.HeckeHomology
