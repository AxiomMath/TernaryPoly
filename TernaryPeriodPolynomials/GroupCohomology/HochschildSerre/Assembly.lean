module

public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.Setup
public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.Inflation

@[expose] public section


/-!
# Hochschild-Serre in degree three over a quotient `GL₂(ℤ)` (abstract form)

Formalized by Claude Sonnet 5.5.

`hsFarey`: for `U ⊲ P`, `A : Rep ℚ P` with `H₃(U, A) = 0`, a surjection `π : P/U ↠ GL₂(ℤ)` with finite kernel, and an isomorphism
`H₂(Z) ≅ res π D` of `P/U`-representations between the second homology of the `U`-coinvariant complex `ZP U A` and the
inflation of a `GL₂(ℤ)`-representation `D`, we get `H₃(P, A) ≃ₗ[ℚ] H₁(GL₂(ℤ), D)`.  The proof combines
`thmAEquiv` (the `Q`-side step), `groupHomologyZIso`, the inflation lemmas and `H1Iso`
(`H₁(GL₂(ℤ), D)` as the kernel of the dual Farey boundary).
-/

open CategoryTheory MonoidalCategory Representation Limits

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HochschildSerre

open TernaryPeriodPolynomials.Argument.FareyTree TernaryPoly.RankTwoAugmentedFrames

variable {P : Type} [Group P] (U : Subgroup P) [U.Normal] (A : Rep.{0} ℚ P)

/-- **Hochschild-Serre in degree three for a split-off `GL₂(ℤ)` quotient with `H_3(U) = 0`.** -/
def hsFarey (π : P ⧸ U →* IntegralGL) (hπ : Function.Surjective π)
    (hker : (π.ker : Set (P ⧸ U)).Finite)
    (hU3 : IsZero (groupHomology (Rep.res U.subtype A) 3)) (D : Rep.{0} ℚ IntegralGL)
    (e : (ZP U A).homology 2 ≅ Rep.res π D) :
    groupHomology A 3 ≃ₗ[ℚ] groupHomology D 1 := by
  have h1 : Projective (Rep.res π P1) := projective_res_P1 π hker
  have h0 : Projective (Rep.res π P0) := projective_res_P0 π hker
  have hZ3 : IsZero ((ZP U A).homology 3) := isZero_ZP_homology U A 3 hU3
  let e1 : groupHomology A 3 ≃ₗ[ℚ] (CxF (ZP U A) (Rep.trivial ℚ (P ⧸ U) ℚ)).homology 3 :=
    (groupHomologyZIso U A 3).toLinearEquiv
  let e2 : (CxF (ZP U A) (Rep.trivial ℚ (P ⧸ U) ℚ)).homology 3 ≃ₗ[ℚ]
      LinearMap.ker ((FXmap (Rep.resMap π d1)).app ((ZP U A).homology 2)).hom :=
    thmAEquiv (ZP U A) (Rep.res π P1) (Rep.res π P0) (Rep.resMap π d1) (epsQ π) (resD1_epsQ π)
      (ZP_projective U A) (sesQ_shortExact π) hZ3
  let e3 : LinearMap.ker ((FXmap (Rep.resMap π d1)).app ((ZP U A).homology 2)).hom ≃ₗ[ℚ]
      LinearMap.ker ((FXmap (Rep.resMap π d1)).app (Rep.res π D)).hom :=
    kerNatEquiv (FXmap (Rep.resMap π d1)) e
  let e4 : LinearMap.ker ((FXmap (Rep.resMap π d1)).app (Rep.res π D)).hom ≃ₗ[ℚ]
      LinearMap.ker ((FXmap d1).app D).hom :=
    kerInflEquiv π hπ d1 D
  let e5 : groupHomology D 1 ≃ₗ[ℚ] LinearMap.ker ((FXmap d1).app D).hom :=
    (H1Iso D).toLinearEquiv
  exact e1.trans (e2.trans (e3.trans (e4.trans e5.symm)))

end TernaryPeriodPolynomials.Argument.HochschildSerre
