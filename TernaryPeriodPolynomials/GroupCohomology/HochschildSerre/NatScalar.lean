module

public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.Functorial
public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.Assembly

@[expose] public section


/-!
# Scalar naturality of the Hochschild-Serre isomorphism `H₃(P, A) ≅ H₁(GL₂(ℤ), D)`

Formalized by Claude Sonnet 5.5.

* `hsFarey_val`: the underlying element of `H₁(GL₂(ℤ), D) ⊂ (D ⊗ P1)_Γ` of `hsFarey y` is the ambient Hochschild-Serre map
  (`hsAmb`: connecting homomorphism followed by `phiH`) followed by `e` and the inflation isomorphism;
* `hsFarey_nat_scalar`: an endomorphism `(φ, a)` of `(P, A)` inducing the identity on `P/U` and acting as the scalar `c` on
  `H₂(ZP U A)` acts as `c` on `H₁(GL₂(ℤ), D)` (the radical factor of the Hecke correspondence of `diag(1/p,1,1)`).
-/

open CategoryTheory MonoidalCategory Representation Limits

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HochschildSerre

open TernaryPeriodPolynomials.Argument.FareyTree TernaryPoly.RankTwoAugmentedFrames
open TernaryPeriodPolynomials.Argument.GroupHomologyDescent (T2 U2)

variable {P : Type} [Group P] (U : Subgroup P) [U.Normal] (A : Rep.{0} ℚ P)

/-- The ambient Hochschild-Serre map (before identifying `H₂(Z)` with `D`). -/
theorem hsFarey_val (π : P ⧸ U →* IntegralGL) (hπ : Function.Surjective π)
    (hker : (π.ker : Set (P ⧸ U)).Finite)
    [Projective (Rep.res π P1)] [Projective (Rep.res π P0)]
    (hU3 : IsZero (groupHomology (Rep.res U.subtype A) 3)) (D : Rep.{0} ℚ IntegralGL)
    (e : (ZP U A).homology 2 ≅ Rep.res π D) (y : groupHomology A 3) :
    ((H1Iso D).toLinearEquiv (hsFarey U A π hπ hker hU3 D e y)).1 = 
      inflEquiv π hπ D P1 (((FX (Rep.res π P1)).map e.hom).hom
        ((hsAmb (Rep.res π P1) (Rep.res π P0) (Rep.resMap π d1) (epsQ π) (resD1_epsQ π)
          (sesQ_shortExact π) (ZP U A) (ZP_projective U A)) ((groupHomologyZIso U A 3).hom y))) := by
  unfold hsFarey
  simp only [LinearEquiv.trans_apply]
  erw [LinearEquiv.apply_symm_apply]
  rfl


omit [U.Normal] in
theorem FX_map_scalar {Q : Type} [Group Q] (X : Rep.{0} ℚ Q) {N : Rep.{0} ℚ Q} (f : N ⟶ N) (c : ℚ)
    (hf : ∀ n : N, f.hom n = c • n) (v : (FX X).obj N) :
    ((FX X).map f).hom v = c • v := by
  induction v using Coinvariants.induction_on with
  | h w =>
    induction w using TensorProduct.inductionOn with
    | tmul n x =>
      have h1 : ((FX X).map f).hom (Coinvariants.mk (N.ρ.tprod X.ρ) (n ⊗ₜ[ℚ] x)) =
          Coinvariants.mk (N.ρ.tprod X.ρ) ((f.hom n) ⊗ₜ[ℚ] x) := rfl
      refine h1.trans ?_
      rw [hf n]
      exact (congrArg (Coinvariants.mk (N.ρ.tprod X.ρ)) (TensorProduct.smul_tmul' c n x)).trans
        (map_smul (Coinvariants.mk (N.ρ.tprod X.ρ)) c (n ⊗ₜ[ℚ] x))
    | add u w hu hw =>
      rw [map_add, map_add, hu, hw, smul_add]


/-- **Scalar naturality of the Hochschild-Serre isomorphism.**  An endomorphism `(φ, a)` of `(P, A)` that induces the identity on
`P/U` and acts on `H₂(Z)` as the scalar `c` acts on `H₃(P, A) ≅ H₁(GL₂(ℤ), D)` as the scalar `c`. -/
theorem hsFarey_nat_scalar (π : P ⧸ U →* IntegralGL) (hπ : Function.Surjective π)
    (hker : (π.ker : Set (P ⧸ U)).Finite)
    [Projective (Rep.res π P1)] [Projective (Rep.res π P0)]
    (hU3 : IsZero (groupHomology (Rep.res U.subtype A) 3)) (D : Rep.{0} ℚ IntegralGL)
    (e : (ZP U A).homology 2 ≅ Rep.res π D)
    (φ : P →* P) (a : A ⟶ Rep.res φ A) (hφU : ∀ u : U, φ (u : P) ∈ U) (hφq : ∀ g : P, φ g * g⁻¹ ∈ U) (c : ℚ)
    (hc : ∀ w : (ZP U A).homology 2, (HomologicalComplex.homologyMap (zMap A φ a hφU hφq) 2).hom w = c • w)
    (y : groupHomology A 3) :
    hsFarey U A π hπ hker hU3 D e (groupHomology.map φ a 3 y) = c • hsFarey U A π hπ hker hU3 D e y := by
  apply (H1Iso D).toLinearEquiv.injective
  apply Subtype.ext
  rw [map_smul, Submodule.coe_smul, hsFarey_val, hsFarey_val]
  have h1 : ((groupHomologyZIso U A 3).hom).hom (groupHomology.map φ a 3 y) =
      (HomologicalComplex.homologyMap (muX (zMap A φ a hφU hφq) (𝟙_ (Rep.{0} ℚ (P ⧸ U)))) 3).hom
        (((groupHomologyZIso U A 3).hom).hom y) :=
    congrArg (fun m => m.hom y) (eZ_nat A φ a hφU hφq 3)
  have h2 := congrArg (fun m => m.hom (((groupHomologyZIso U A 3).hom).hom y))
    (hsAmb_nat (zMap A φ a hφU hφq) (Rep.res π P1) (Rep.res π P0) (Rep.resMap π d1) (epsQ π)
      (resD1_epsQ π) (ZP_projective U A) (ZP_projective U A) (sesQ_shortExact π))
  have h3 : ∀ u : (FX (Rep.res π P1)).obj ((ZP U A).homology 2),
      ((FX (Rep.res π P1)).map (HomologicalComplex.homologyMap (zMap A φ a hφU hφq) 2)).hom u = c • u :=
    fun u => FX_map_scalar (Rep.res π P1) _ c hc u
  have h4 : (hsAmb (Rep.res π P1) (Rep.res π P0) (Rep.resMap π d1) (epsQ π) (resD1_epsQ π)
      (sesQ_shortExact π) (ZP U A) (ZP_projective U A)).hom
        ((HomologicalComplex.homologyMap (muX (zMap A φ a hφU hφq) (𝟙_ (Rep.{0} ℚ (P ⧸ U)))) 3).hom
          (((groupHomologyZIso U A 3).hom).hom y)) =
      c • (hsAmb (Rep.res π P1) (Rep.res π P0) (Rep.resMap π d1) (epsQ π) (resD1_epsQ π)
        (sesQ_shortExact π) (ZP U A) (ZP_projective U A)).hom (((groupHomologyZIso U A 3).hom).hom y) :=
    h2.trans (h3 _)
  refine (congrArg (fun v => inflEquiv π hπ D P1 (((FX (Rep.res π P1)).map e.hom).hom
    ((hsAmb (Rep.res π P1) (Rep.res π P0) (Rep.resMap π d1) (epsQ π) (resD1_epsQ π)
      (sesQ_shortExact π) (ZP U A) (ZP_projective U A)).hom v))) h1).trans ?_
  rw [h4, map_smul, map_smul]


section IdCoeff

variable {U} (eU : TernaryPeriodPolynomials.Argument.GroupHomologyDescent.U2 ≃* U)

/-- The coefficient morphism `A ⟶ Res_φ A` given by the identity, when `U` acts trivially and `φ g g⁻¹ ∈ U`. -/
def idCoeff (hA : ∀ u : U, A.ρ u = 1) (φ : P →* P) (hφq : ∀ g : P, φ g * g⁻¹ ∈ U) :
    A ⟶ Rep.res φ A :=
  Rep.ofHom ⟨LinearMap.id, fun h => by
    refine LinearMap.ext fun a => ?_
    have h1 : A.ρ (φ h) = A.ρ h := by
      have : φ h = (φ h * h⁻¹) * h := by group
      rw [this, map_mul, hA ⟨φ h * h⁻¹, hφq h⟩]
      exact LinearMap.id_comp _
    exact (congrArg (fun m => m a) h1).symm⟩

/-- **The Hochschild-Serre isomorphism and an endomorphism acting by the identity on the fibre**: it acts as the determinant
`ω(μ e₁, μ e₂)` of `φ|_U` on the radical `U ≅ ℤ²`. -/
theorem hsFarey_idCoeff [Module.Finite ℚ A.V] (π : P ⧸ U →* IntegralGL) (hπ : Function.Surjective π)
    (hker : (π.ker : Set (P ⧸ U)).Finite)
    [Projective (Rep.res π P1)] [Projective (Rep.res π P0)]
    (hU3 : IsZero (groupHomology (Rep.res U.subtype A) 3)) (D : Rep.{0} ℚ IntegralGL)
    (e : (ZP U A).homology 2 ≅ Rep.res π D) (hA : ∀ u : U, A.ρ u = 1)
    (φ : P →* P) (hφU : ∀ u : U, φ (u : P) ∈ U) (hφq : ∀ g : P, φ g * g⁻¹ ∈ U)
    (y : groupHomology A 3) :
    hsFarey U A π hπ hker hU3 D e (groupHomology.map φ (idCoeff A hA φ hφq) 3 y) =
      (omegaZ (muPhi φ hφU eU TernaryPeriodPolynomials.Argument.HochschildSerre.e1)
        (muPhi φ hφU eU TernaryPeriodPolynomials.Argument.HochschildSerre.e2) : ℚ) •
        hsFarey U A π hπ hker hU3 D e y := by
  refine hsFarey_nat_scalar U A π hπ hker hU3 D e φ (idCoeff A hA φ hφq) hφU hφq _ ?_ y
  intro w
  obtain ⟨x, rfl⟩ := (gammaEquiv eU hA).surjective w
  exact H2_zMap A φ (idCoeff A hA φ hφq) hφU hφq eU hA x


/-- **Scalar naturality, general coefficient.**  If `a` acts on `H₂(Z)`, in the coordinates `gammaEquiv`, by the scalar `κ`, then
`(φ, a)` acts on `H₃(P, A) ≅ H₁(GL₂(ℤ), D)` as `ω(μ e₁, μ e₂) · κ`. -/
theorem hsFarey_scalarCoeff [Module.Finite ℚ A.V] (π : P ⧸ U →* IntegralGL) (hπ : Function.Surjective π)
    (hker : (π.ker : Set (P ⧸ U)).Finite)
    [Projective (Rep.res π P1)] [Projective (Rep.res π P0)]
    (hU3 : IsZero (groupHomology (Rep.res U.subtype A) 3)) (D : Rep.{0} ℚ IntegralGL)
    (e : (ZP U A).homology 2 ≅ Rep.res π D) (hA : ∀ u : U, A.ρ u = 1)
    (φ : P →* P) (a : A ⟶ Rep.res φ A) (hφU : ∀ u : U, φ (u : P) ∈ U) (hφq : ∀ g : P, φ g * g⁻¹ ∈ U)
    (κ : ℚ) (hax : ∀ x : A.V, gammaEquiv eU hA (a.hom x) = κ • gammaEquiv eU hA x)
    (y : groupHomology A 3) :
    hsFarey U A π hπ hker hU3 D e (groupHomology.map φ a 3 y) =
      ((omegaZ (muPhi φ hφU eU TernaryPeriodPolynomials.Argument.HochschildSerre.e1)
        (muPhi φ hφU eU TernaryPeriodPolynomials.Argument.HochschildSerre.e2) : ℚ) * κ) •
        hsFarey U A π hπ hker hU3 D e y := by
  refine hsFarey_nat_scalar U A π hπ hker hU3 D e φ a hφU hφq _ ?_ y
  intro w
  obtain ⟨x, rfl⟩ := (gammaEquiv eU hA).surjective w
  rw [H2_zMap A φ a hφU hφq eU hA x, hax x, smul_smul]

end IdCoeff

end TernaryPeriodPolynomials.Argument.HochschildSerre
