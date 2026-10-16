module

public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.HeckeNat
public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.Assembly
public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeHomology.BinaryHecke

@[expose] public section


/-!
# The Hochschild-Serre map and the binary Hecke operator on `H₁(GL₂(ℤ), -)`

Formalized by Claude Sonnet 5.5.

Everything is abstract in `Q` (the quotient `P/U` of `hsFarey`) and the complex `Z` (`ZP U A`).

* `hsZ`: `hsFarey` with the identification `groupHomologyZIso` removed: the composite
  `H₃((Z ⊗ 1)_Q) ≃ ker (FXmap d) ≃ ker dC ≃ H₁(GL₂(ℤ), D)` (`hsFarey_eq_hsZ` is `rfl`); `H1Iso_hsZ`: the underlying element of
  `(D ⊗ P1)_Γ` of `hsZ y` is `inflEquiv (FX.map e (hsAmb y))`.
* `inflLam`: inflation of the binary lift `binLift p` to `Γ₀ → χ`, with `inflLam_d`, `inflLam_eps` (the compatibilities
  `hd`, `hε` of `sesHecke`).
* `Tterm`, `sum_rc_infl`, `rcMap`: the coset terms of the binary operator, left `S`-invariance, and the bijection of right cosets
  `RC Γ₀ ≃ RC S` induced by `π`.
* `PhiLin_kappaExp`: the inflation `PhiLin` of `(H₂ Z ⊗ Res P1)_Q` to `(D ⊗ P1)_Γ` intertwines `kappaExp` with `r` times the
  Farey-model operator `(ResHecke (binDatum p) M farResolution (binLift p)).f 1`, when `e ∘ zetaH = r · ρ_M(C1 p) ∘ e` on `H₂`.
* **`hsZ_hecke`**: `H1Iso (hsZ (H₃(hmuC … lamTriv) y)) = r • ResHeckeKer (binDatum p) M (binLift p) (H1Iso (hsZ y))`.  The scalar
  `r` is the only place where a normalisation enters.
* `zetaH_forget`: `zetaH` is the map induced on homology by `ζ` viewed as a chain map `zetaF` of the underlying linear complexes,
  through the comparison `mapHomologyIso (forget₂ …)`.
-/

open CategoryTheory MonoidalCategory Representation Limits
open TernaryPeriodPolynomials.Argument.FareyTree TernaryPoly.RankTwoAugmentedFrames
open TernaryPeriodPolynomials.Argument.HeckeHomology TernaryPoly.OrdinaryResidueParabolic

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HochschildSerre

variable {Q : Type} [Group Q] (Z : ChainComplex (Rep.{0} ℚ Q) ℕ)

/-- The Hochschild-Serre map `H₃((Z ⊗ 1)_Q) → H₁(GL₂(ℤ), D)` of `hsFarey` with the identification
`groupHomologyZIso` removed. -/
def hsZ (π : Q →* IntegralGL) (hπ : Function.Surjective π) (hker : (π.ker : Set Q).Finite)
    (hZ : ∀ j, Projective (Z.X j)) (hZ3 : IsZero (Z.homology 3)) (D : Rep.{0} ℚ IntegralGL)
    (e : Z.homology 2 ≅ Rep.res π D) :
    (CxF Z (Rep.trivial ℚ Q ℚ)).homology 3 ≃ₗ[ℚ] groupHomology D 1 := by
  have h1 : Projective (Rep.res π P1) := projective_res_P1 π hker
  have h0 : Projective (Rep.res π P0) := projective_res_P0 π hker
  exact (thmAEquiv Z (Rep.res π P1) (Rep.res π P0) (Rep.resMap π d1) (epsQ π) (resD1_epsQ π) hZ
      (sesQ_shortExact π) hZ3).trans
    ((kerNatEquiv (FXmap (Rep.resMap π d1)) e).trans
      ((kerInflEquiv π hπ d1 D).trans (H1Iso D).toLinearEquiv.symm))

theorem hsFarey_eq_hsZ {P : Type} [Group P] (U : Subgroup P) [U.Normal] (A : Rep.{0} ℚ P)
    (π : P ⧸ U →* IntegralGL) (hπ : Function.Surjective π)
    (hker : (π.ker : Set (P ⧸ U)).Finite)
    (hU3 : IsZero (groupHomology (Rep.res U.subtype A) 3)) (D : Rep.{0} ℚ IntegralGL)
    (e : (ZP U A).homology 2 ≅ Rep.res π D) (x : groupHomology A 3) :
    hsFarey U A π hπ hker hU3 D e x =
      hsZ (ZP U A) π hπ hker (ZP_projective U A) (isZero_ZP_homology U A 3 hU3) D e
        ((groupHomologyZIso U A 3).hom.hom x) := rfl

theorem H1Iso_hsZ (π : Q →* IntegralGL) (hπ : Function.Surjective π) (hker : (π.ker : Set Q).Finite)
    (hZ : ∀ j, Projective (Z.X j)) (hZ3 : IsZero (Z.homology 3)) (D : Rep.{0} ℚ IntegralGL)
    (e : Z.homology 2 ≅ Rep.res π D) (y : (CxF Z (Rep.trivial ℚ Q ℚ)).homology 3) :
    Subtype.val ((H1Iso D).toLinearEquiv (hsZ Z π hπ hker hZ hZ3 D e y)) =
      inflEquiv π hπ D P1
        (((FX (Rep.res π P1)).map e.hom).hom
          (haveI : Projective (Rep.res π P1) := projective_res_P1 π hker
           haveI : Projective (Rep.res π P0) := projective_res_P0 π hker
           (hsAmb (Rep.res π P1) (Rep.res π P0) (Rep.resMap π d1) (epsQ π) (resD1_epsQ π)
            (sesQ_shortExact π) Z hZ).hom y)) := by
  have h1 : Projective (Rep.res π P1) := projective_res_P1 π hker
  have h0 : Projective (Rep.res π P0) := projective_res_P0 π hker
  have key : (H1Iso D).toLinearEquiv (hsZ Z π hπ hker hZ hZ3 D e y) =
      kerInflEquiv π hπ d1 D (kerNatEquiv (FXmap (Rep.resMap π d1)) e
        (thmAEquiv Z (Rep.res π P1) (Rep.res π P0) (Rep.resMap π d1) (epsQ π) (resD1_epsQ π) hZ
          (sesQ_shortExact π) hZ3 y)) :=
    (H1Iso D).toLinearEquiv.apply_symm_apply _
  rw [key]
  rfl

section Lam

variable (p : ℕ) [Fact p.Prime] {π : Q →* IntegralGL} (Γ₀ : Subgroup Q) (χ : Γ₀ →* Q)
  (hGamma : ∀ q, q ∈ Γ₀ ↔ π q ∈ (binDatum p).S)
  (hchi : ∀ g : Γ₀, π (χ g) = (binDatum p).f ⟨π g, (hGamma g).mp g.2⟩)

/-- Inflation of a binary lift `l : Res_S X ⟶ Res_f X` to `Γ₀ → χ`. -/
def inflLam (X : Rep.{0} ℚ IntegralGL) (l : Rep.res (binDatum p).S.subtype X ⟶ Rep.res (binDatum p).f X) :
    Rep.res Γ₀.subtype (Rep.res π X) ⟶ Rep.res χ (Rep.res π X) :=
  Rep.ofHom ⟨l.hom.toLinearMap, fun g => by
    refine LinearMap.ext fun v => ?_
    have h := Rep.hom_comm_apply l ⟨π g.1, (hGamma g.1).mp g.2⟩ v
    change l.hom (X.ρ (π g.1) v) = X.ρ (π (χ g)) (l.hom v)
    rw [hchi g]
    exact h⟩

theorem inflLam_hom (X : Rep.{0} ℚ IntegralGL)
    (l : Rep.res (binDatum p).S.subtype X ⟶ Rep.res (binDatum p).f X) (v : X) :
    (inflLam p Γ₀ χ hGamma hchi X l).hom v = l.hom v := rfl

end Lam

section Gen

variable (p : ℕ) [Fact p.Prime] (M : Rep.{0} ℚ GL2) (m : M) (v : P1)

/-- The coset-term of the binary Hecke operator on the generator `[m ⊗ v]`. -/
def Tterm (s : IntegralGL) : ((FX P1).obj (Rep.res binIota M)) :=
  Coinvariants.mk ((Rep.res binIota M).ρ.tprod P1.ρ)
    (M.ρ (C1 p) ((Rep.res binIota M).ρ s m) ⊗ₜ[ℚ] ((binLift p).f 1).hom (P1.ρ s v))

theorem Tterm_left_inv (s' : (binDatum p).S) (s : IntegralGL) :
    Tterm p M m v ((s' : IntegralGL) * s) = Tterm p M m v s := by
  have hf : binIota ((binDatum p).f s') * C1 p = C1 p * binIota s'.1 := by
    rw [(binDatum p).hf s']; group
  have h1 : M.ρ (C1 p) ((Rep.res binIota M).ρ ((s' : IntegralGL) * s) m) =
      (Rep.res binIota M).ρ ((binDatum p).f s') (M.ρ (C1 p) ((Rep.res binIota M).ρ s m)) := by
    change M.ρ (C1 p) (M.ρ (binIota ((s' : IntegralGL) * s)) m) =
      M.ρ (binIota ((binDatum p).f s')) (M.ρ (C1 p) (M.ρ (binIota s) m))
    have key : binIota ((binDatum p).f s') * (C1 p * binIota s) = C1 p * binIota ((s' : IntegralGL) * s) := by
      rw [map_mul binIota, ← mul_assoc, hf, mul_assoc]
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, ← Module.End.mul_apply, ← map_mul,
      mul_assoc, key]
  have h2 : ((binLift p).f 1).hom (P1.ρ ((s' : IntegralGL) * s) v) =
      P1.ρ ((binDatum p).f s') (((binLift p).f 1).hom (P1.ρ s v)) := by
    have := Rep.hom_comm_apply ((binLift p).f 1) s' (P1.ρ s v)
    change ((binLift p).f 1).hom (P1.ρ s'.1 (P1.ρ s v)) = _ at this
    rw [← Module.End.mul_apply, ← map_mul] at this
    exact this
  unfold Tterm
  rw [h1, h2]
  exact Coinvariants.mk_self_apply ((Rep.res binIota M).ρ.tprod P1.ρ) ((binDatum p).f s')
    (M.ρ (C1 p) ((Rep.res binIota M).ρ s m) ⊗ₜ[ℚ] ((binLift p).f 1).hom (P1.ρ s v))

end Gen

section Cosets

variable {π : Q →* IntegralGL} (hπ : Function.Surjective π) (Γ₀ : Subgroup Q) (S : Subgroup IntegralGL)
  (hΓ : ∀ q, q ∈ Γ₀ ↔ π q ∈ S)

/-- The map of right cosets induced by `π`. -/
def rcMap : RC Γ₀ → RC S :=
  Quotient.map' π (fun a b hab => by
    rw [QuotientGroup.rightRel_apply] at hab ⊢
    rw [← map_inv, ← map_mul]
    exact (hΓ _).mp hab)

theorem rcMap_mk (a : Q) : rcMap Γ₀ S hΓ (Quotient.mk _ a) = Quotient.mk _ (π a) := rfl

include hπ in
theorem rcMap_bijective : Function.Bijective (rcMap Γ₀ S hΓ) := by
  constructor
  · intro x y hxy
    induction x using Quotient.inductionOn' with
    | h a =>
      induction y using Quotient.inductionOn' with
      | h b =>
        change rcMap Γ₀ S hΓ (Quotient.mk _ a) = rcMap Γ₀ S hΓ (Quotient.mk _ b) at hxy
        rw [rcMap_mk, rcMap_mk, rc_eq_iff] at hxy
        apply Quotient.sound'
        rw [QuotientGroup.rightRel_apply]
        refine (hΓ _).mpr ?_
        rw [map_mul, map_inv]
        exact hxy
  · intro y
    induction y using Quotient.inductionOn' with
    | h b =>
      obtain ⟨a, rfl⟩ := hπ b
      exact ⟨Quotient.mk _ a, rfl⟩

include hπ hΓ in
/-- Reindexing of a coset sum along `π`, for a left `S`-invariant summand. -/
theorem sum_rc_infl [Γ₀.FiniteIndex] [S.FiniteIndex] {W : Type*} [AddCommMonoid W] (T : IntegralGL → W)
    (hT : ∀ (s' : S) (s : IntegralGL), T ((s' : IntegralGL) * s) = T s) :
    ∑ c : RC Γ₀, T (π c.out) = ∑ x : RC S, T x.out := by
  classical
  have h1 : ∀ c : RC Γ₀, T (π c.out) = T (rcMap Γ₀ S hΓ c).out := by
    intro c
    have hc : rcMap Γ₀ S hΓ c = Quotient.mk _ (π c.out) := by
      conv_lhs => rw [← Quotient.out_eq c]
      rfl
    have h2 : (Quotient.mk (QuotientGroup.rightRel S) (π c.out) : RC S) =
        Quotient.mk _ (rcMap Γ₀ S hΓ c).out := by
      rw [← hc, Quotient.out_eq]
    rw [rc_eq_iff] at h2
    have h3 : (rcMap Γ₀ S hΓ c).out = ((rcMap Γ₀ S hΓ c).out * (π c.out)⁻¹) * π c.out := by group
    rw [h3]
    exact (hT ⟨_, h2⟩ _).symm
  simp only [h1]
  exact Equiv.sum_comp (Equiv.ofBijective _ (rcMap_bijective hπ Γ₀ S hΓ)) (fun x : RC S => T x.out)

end Cosets

section Main

variable (p : ℕ) [Fact p.Prime] {π : Q →* IntegralGL} (hπ : Function.Surjective π) (M : Rep.{0} ℚ GL2)
  (e : Z.homology 2 ≅ Rep.res π (Rep.res binIota M))

/-- The inflation of a class `(H₂ Z ⊗ Res P1)_Q` to `(D ⊗ P1)_Γ` through `e`. -/
def PhiLin : (FX (Rep.res π P1)).obj (Z.homology 2) →ₗ[ℚ] (FX P1).obj (Rep.res binIota M) :=
  (inflEquiv π hπ (Rep.res binIota M) P1).toLinearMap ∘ₗ ((FX (Rep.res π P1)).map e.hom).hom

theorem PhiLin_mk (h : Z.homology 2) (x : P1) :
    PhiLin Z hπ M e (Coinvariants.mk ((Z.homology 2).ρ.tprod (Rep.res π P1).ρ) (h ⊗ₜ[ℚ] x)) =
      Coinvariants.mk ((Rep.res binIota M).ρ.tprod P1.ρ) (e.hom.hom h ⊗ₜ[ℚ] x) := rfl

variable (Γ₀ : Subgroup Q) [Γ₀.FiniteIndex] (hGamma : ∀ q, q ∈ Γ₀ ↔ π q ∈ (binDatum p).S)
  (χ : Γ₀ →* Q) (hchi : ∀ g : Γ₀, π (χ g) = (binDatum p).f ⟨π g, (hGamma g).mp g.2⟩)
  (ζ : ResC Γ₀.subtype Z ⟶ ResC χ Z) (r : ℚ)
  (hz : ∀ w : Z.homology 2, e.hom.hom ((zetaH Γ₀ χ Z 2 ζ).hom w) = r • (M.ρ (C1 p)) (e.hom.hom w))

include hGamma hchi hz in
theorem PhiLin_kappaExp_mk (h : Z.homology 2) (x : P1) :
    PhiLin Z hπ M e
        ((kappaExp Γ₀ χ Z 2 ζ (Rep.res π P1) (inflLam p Γ₀ χ hGamma hchi P1 ((binLift p).f 1))).hom
          (Coinvariants.mk ((Z.homology 2).ρ.tprod (Rep.res π P1).ρ) (h ⊗ₜ[ℚ] x))) =
      r • ((ResHecke (binDatum p) M farResolution (binLift p)).f 1).hom
        (PhiLin Z hπ M e (Coinvariants.mk ((Z.homology 2).ρ.tprod (Rep.res π P1).ρ) (h ⊗ₜ[ℚ] x))) := by
  have hterm : ∀ c : RC Γ₀, PhiLin Z hπ M e (Coinvariants.mk ((Z.homology 2).ρ.tprod (Rep.res π P1).ρ)
      ((zetaH Γ₀ χ Z 2 ζ).hom ((Z.homology 2).ρ c.out h) ⊗ₜ[ℚ]
        (inflLam p Γ₀ χ hGamma hchi P1 ((binLift p).f 1)).hom ((Rep.res π P1).ρ c.out x))) =
      r • Tterm p M (e.hom.hom h) x (π c.out) := by
    intro c
    have he : e.hom.hom ((Z.homology 2).ρ c.out h) = (Rep.res binIota M).ρ (π c.out) (e.hom.hom h) :=
      Rep.hom_comm_apply e.hom c.out h
    rw [PhiLin_mk, hz, he]
    unfold Tterm
    rw [← TensorProduct.smul_tmul', map_smul]
    rfl
  erw [kappaExp_mk, map_sum]
  simp only [hterm]
  rw [← Finset.smul_sum, sum_rc_infl hπ Γ₀ (binDatum p).S hGamma (Tterm p M (e.hom.hom h) x)
    (fun s' s => Tterm_left_inv p M (e.hom.hom h) x s' s)]
  rw [PhiLin_mk]
  erw [binary_resHecke_mk p M 1 (e.hom.hom h) x]
  rfl

include hGamma hchi hz in
theorem PhiLin_kappaExp (a : (FX (Rep.res π P1)).obj (Z.homology 2)) :
    PhiLin Z hπ M e
        ((kappaExp Γ₀ χ Z 2 ζ (Rep.res π P1) (inflLam p Γ₀ χ hGamma hchi P1 ((binLift p).f 1))).hom a) =
      r • ((ResHecke (binDatum p) M farResolution (binLift p)).f 1).hom (PhiLin Z hπ M e a) := by
  have key : (PhiLin Z hπ M e ∘ₗ
      (kappaExp Γ₀ χ Z 2 ζ (Rep.res π P1) (inflLam p Γ₀ χ hGamma hchi P1 ((binLift p).f 1))).hom) =
      r • (((ResHecke (binDatum p) M farResolution (binLift p)).f 1).hom ∘ₗ PhiLin Z hπ M e) := by
    refine Coinvariants.hom_ext (TensorProduct.ext' fun h x => ?_)
    exact PhiLin_kappaExp_mk Z p hπ M e Γ₀ hGamma χ hchi ζ r hz h x
  exact LinearMap.congr_fun key a

end Main

section Compat

variable (p : ℕ) [Fact p.Prime] {π : Q →* IntegralGL} (Γ₀ : Subgroup Q)
  (hGamma : ∀ q, q ∈ Γ₀ ↔ π q ∈ (binDatum p).S) (χ : Γ₀ →* Q)
  (hchi : ∀ g : Γ₀, π (χ g) = (binDatum p).f ⟨π g, (hGamma g).mp g.2⟩)

theorem inflLam_d :
    inflLam p Γ₀ χ hGamma hchi P1 ((binLift p).f 1) ≫ (Rep.resFunctor χ).map (Rep.resMap π d1) =
      (Rep.resFunctor Γ₀.subtype).map (Rep.resMap π d1) ≫ inflLam p Γ₀ χ hGamma hchi P0 ((binLift p).f 0) := by
  have hc := (binLift p).comm 1 0
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  refine LinearMap.ext fun v => ?_
  have h := congrArg (fun t => t.hom v) hc
  exact h

theorem inflLam_eps :
    inflLam p Γ₀ χ hGamma hchi P0 ((binLift p).f 0) ≫ (Rep.resFunctor χ).map (epsQ π) =
      (Rep.resFunctor Γ₀.subtype).map (epsQ π) := by
  have hc := binLift_overId p
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  refine LinearMap.ext fun v => ?_
  have h := congrArg (fun t => t.hom v) hc
  exact h

end Compat


section Final

variable (p : ℕ) [Fact p.Prime] {π : Q →* IntegralGL} (hπ : Function.Surjective π)
  (hker : (π.ker : Set Q).Finite) (hZ : ∀ j, Projective (Z.X j)) (hZ3 : IsZero (Z.homology 3))
  (M : Rep.{0} ℚ GL2) (e : Z.homology 2 ≅ Rep.res π (Rep.res binIota M))
  (Γ₀ : Subgroup Q) [Γ₀.FiniteIndex] (hGamma : ∀ q, q ∈ Γ₀ ↔ π q ∈ (binDatum p).S)
  (χ : Γ₀ →* Q) (hchi : ∀ g : Γ₀, π (χ g) = (binDatum p).f ⟨π g, (hGamma g).mp g.2⟩)
  (ζ : ResC Γ₀.subtype Z ⟶ ResC χ Z) (r : ℚ)
  (hz : ∀ w : Z.homology 2, e.hom.hom ((zetaH Γ₀ χ Z 2 ζ).hom w) = r • (M.ρ (C1 p)) (e.hom.hom w))

omit [Γ₀.FiniteIndex] in
theorem ker_comp_subtype_finite (hker : (π.ker : Set Q).Finite) :
    (((π.comp Γ₀.subtype).ker : Subgroup Γ₀) : Set Γ₀).Finite :=
  (hker.preimage (f := (Subtype.val : Γ₀ → Q)) Subtype.val_injective.injOn).subset fun _ hg => hg

omit [Γ₀.FiniteIndex] in
include hchi in
theorem ker_comp_chi_finite (hker : (π.ker : Set Q).Finite) :
    (((π.comp χ).ker : Subgroup Γ₀) : Set Γ₀).Finite := by
  refine (ker_comp_subtype_finite Γ₀ hker).subset fun g hg => ?_
  have h1 : π (χ g) = 1 := hg
  rw [hchi g] at h1
  have h2 : (⟨π g.1, (hGamma g).mp g.2⟩ : (binDatum p).S) = 1 := binDatum_f_injective p (by rw [h1, map_one])
  have h3 : π g.1 = 1 := congrArg Subtype.val h2
  exact h3

include hπ hker hGamma hchi hz in
/-- **Hecke-type compatibility of the Hochschild-Serre map with the binary Hecke operator.**  Let `Q` be a group with a
surjection `π : Q → GL₂(ℤ)` with finite kernel, `Z` a complex of projective `Q`-modules with `H₃(Z) = 0` and
`e : H₂(Z) ≅ Res_π (Res_ι M)` (`D = Res_ι M` for a `GL₂(ℚ)`-module `M`).  Let `Γ₀ = π⁻¹((binDatum p).S)`, `χ : Γ₀ → Q`
lifting the correspondence map `f` of the binary datum, and `ζ : Res_{Γ₀} Z ⟶ Res_χ Z` a chain map such that on `H₂`
`e ∘ zetaH(ζ) = r · ρ_M(diag(1/p,1)) ∘ e`.  Then the Hecke-type endomorphism `hmuC` of `H₃((Z ⊗ 1)_Q)` corresponds under the
Hochschild-Serre isomorphism `hsZ` and `H1Iso` to `r` times the Farey-model Hecke operator `ResHeckeKer (binDatum p) M (binLift p)`
on `ker dC ⊂ (D ⊗ P1)_Γ`.  The scalar `r` is the only place where a normalisation enters. -/
theorem hsZ_hecke (y : (CxF Z (Rep.trivial ℚ Q ℚ)).homology 3) :
    (H1Iso (Rep.res binIota M)).toLinearEquiv
        (hsZ Z π hπ hker hZ hZ3 (Rep.res binIota M) e
          ((HomologicalComplex.homologyMap (hmuC Γ₀ χ Z ζ (lamTriv Γ₀ χ)) 3).hom y)) =
      r • (ResHeckeKer (binDatum p) M (binLift p)).hom
        ((H1Iso (Rep.res binIota M)).toLinearEquiv (hsZ Z π hπ hker hZ hZ3 (Rep.res binIota M) e y)) := by
  have h1 : Projective (Rep.res π P1) := projective_res_P1 π hker
  have h0 : Projective (Rep.res π P0) := projective_res_P0 π hker
  have h2 : Projective (Rep.res Γ₀.subtype (Rep.res π P1)) :=
    projective_res_P1 (π.comp Γ₀.subtype) (ker_comp_subtype_finite Γ₀ hker)
  have h3 : Projective (Rep.res χ (Rep.res π P1)) :=
    projective_res_P1 (π.comp χ) (ker_comp_chi_finite p Γ₀ hGamma χ hchi hker)
  have hh := congrArg (fun t => t.hom y)
    (hsAmb_hecke Γ₀ χ (Rep.res π P1) (Rep.res π P0) (Rep.resMap π d1) (epsQ π) (resD1_epsQ π) Z ζ
      (inflLam p Γ₀ χ hGamma hchi P1 ((binLift p).f 1)) (inflLam p Γ₀ χ hGamma hchi P0 ((binLift p).f 0))
      (inflLam_d p Γ₀ hGamma χ hchi) (inflLam_eps p Γ₀ hGamma χ hchi) hZ (sesQ_shortExact π))
  have hΦ : ∀ y', Subtype.val ((H1Iso (Rep.res binIota M)).toLinearEquiv
      (hsZ Z π hπ hker hZ hZ3 (Rep.res binIota M) e y')) = PhiLin Z hπ M e
        ((hsAmb (Rep.res π P1) (Rep.res π P0) (Rep.resMap π d1) (epsQ π) (resD1_epsQ π)
          (sesQ_shortExact π) Z hZ).hom y') := fun y' => H1Iso_hsZ Z π hπ hker hZ hZ3 _ e y'
  apply Subtype.ext
  rw [hΦ]
  have hh' : (hsAmb (Rep.res π P1) (Rep.res π P0) (Rep.resMap π d1) (epsQ π) (resD1_epsQ π)
      (sesQ_shortExact π) Z hZ).hom ((HomologicalComplex.homologyMap (hmuC Γ₀ χ Z ζ (lamTriv Γ₀ χ)) 3).hom y) =
      (kappaExp Γ₀ χ Z 2 ζ (Rep.res π P1) (inflLam p Γ₀ χ hGamma hchi P1 ((binLift p).f 1))).hom
        ((hsAmb (Rep.res π P1) (Rep.res π P0) (Rep.resMap π d1) (epsQ π) (resD1_epsQ π)
          (sesQ_shortExact π) Z hZ).hom y) := hh
  rw [hh', PhiLin_kappaExp Z p hπ M e Γ₀ hGamma χ hchi ζ r hz]
  change _ = r • ((ResHecke (binDatum p) M farResolution (binLift p)).f 1).hom
    (Subtype.val ((H1Iso (Rep.res binIota M)).toLinearEquiv
      (hsZ Z π hπ hker hZ hZ3 (Rep.res binIota M) e y)))
  rw [hΦ]

end Final

section Forget

variable (Γ₀ : Subgroup Q) (χ : Γ₀ →* Q) {Z} (n : ℕ) (ζ : ResC Γ₀.subtype Z ⟶ ResC χ Z)

/-- `ζ` as a chain map of the underlying `ℚ`-linear complexes (the underlying complexes of `Res_{Γ₀} Z`, `Res_χ Z` and `Z`
coincide). -/
def zetaF : ((forget₂ (Rep.{0} ℚ Q) (ModuleCat.{0} ℚ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj Z ⟶
    ((forget₂ (Rep.{0} ℚ Q) (ModuleCat.{0} ℚ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj Z :=
  ((forget₂ (Rep.{0} ℚ Γ₀) (ModuleCat.{0} ℚ)).mapHomologicalComplex (ComplexShape.down ℕ)).map ζ

theorem zetaF_f (j : ℕ) (z : Z.X j) : ((zetaF Γ₀ χ ζ).f j).hom z = (ζ.f j).hom z := rfl

theorem zeta_chase {𝒞 : Type*} [Category 𝒞] {H F1 F2 F3 : 𝒞} (zF : H ⟶ H) (ΘY : H ⟶ F1)
    (ΘY' : H ⟶ F2) (ΘQ : H ⟶ F3) (a : F1 ⟶ F3) (ainv : F3 ⟶ F1) (Hz : F1 ⟶ F2)
    (b : F2 ⟶ F3) (zH : F3 ⟶ F3) (hzH : zH = ainv ≫ Hz ≫ b) (h1 : ΘQ = ΘY ≫ a) (h2 : ΘQ = ΘY' ≫ b)
    (hnat : zF ≫ ΘY' = ΘY ≫ Hz) (hinv : a ≫ ainv = 𝟙 F1) :
    zF ≫ ΘQ = ΘQ ≫ zH := by
  have L : zF ≫ ΘQ = ΘY ≫ Hz ≫ b := by
    rw [h2, ← Category.assoc, hnat, Category.assoc]
  have R : ΘQ ≫ zH = ΘY ≫ Hz ≫ b := by
    rw [hzH, h1]
    simp only [Category.assoc]
    rw [reassoc_of% hinv]
  exact L.trans R.symm

/-- **`zetaH` is the map induced by `ζ` on the homology of the underlying linear complexes.** -/
theorem zetaH_forget (c : ((forget₂ (Rep.{0} ℚ Q) (ModuleCat.{0} ℚ)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj Z |>.homology n) :
    (zetaH Γ₀ χ Z n ζ).hom (((Z.sc n).mapHomologyIso (forget₂ (Rep.{0} ℚ Q) (ModuleCat.{0} ℚ))).hom.hom c) =
      ((Z.sc n).mapHomologyIso (forget₂ (Rep.{0} ℚ Q) (ModuleCat.{0} ℚ))).hom.hom
        ((HomologicalComplex.homologyMap (zetaF Γ₀ χ ζ) n).hom c) := by
  have hF := zeta_chase
    (HomologicalComplex.homologyMap (zetaF Γ₀ χ ζ) n)
    (((ResC Γ₀.subtype Z).sc n).mapHomologyIso (forget₂ (Rep.{0} ℚ Γ₀) (ModuleCat.{0} ℚ))).hom
    (((ResC χ Z).sc n).mapHomologyIso (forget₂ (Rep.{0} ℚ Γ₀) (ModuleCat.{0} ℚ))).hom
    ((Z.sc n).mapHomologyIso (forget₂ (Rep.{0} ℚ Q) (ModuleCat.{0} ℚ))).hom
    ((forget₂ (Rep.{0} ℚ Γ₀) (ModuleCat.{0} ℚ)).map (resHomIso Z n Γ₀.subtype).hom)
    ((forget₂ (Rep.{0} ℚ Γ₀) (ModuleCat.{0} ℚ)).map (resHomIso Z n Γ₀.subtype).inv)
    ((forget₂ (Rep.{0} ℚ Γ₀) (ModuleCat.{0} ℚ)).map (HomologicalComplex.homologyMap ζ n))
    ((forget₂ (Rep.{0} ℚ Γ₀) (ModuleCat.{0} ℚ)).map (resHomIso Z n χ).hom)
    ((forget₂ (Rep.{0} ℚ Γ₀) (ModuleCat.{0} ℚ)).map (zetaH Γ₀ χ Z n ζ))
    (by
      unfold zetaH
      exact (Functor.map_comp _ _ _).trans (congrArg _ (Functor.map_comp _ _ _)))
    (congrArg Iso.hom (mapHomologyIso_comp (Rep.resFunctor Γ₀.subtype)
      (forget₂ (Rep.{0} ℚ Γ₀) (ModuleCat.{0} ℚ)) (Z.sc n)))
    (congrArg Iso.hom (mapHomologyIso_comp (Rep.resFunctor χ)
      (forget₂ (Rep.{0} ℚ Γ₀) (ModuleCat.{0} ℚ)) (Z.sc n)))
    (ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor _ (ComplexShape.down ℕ) n).map ζ)
      (forget₂ (Rep.{0} ℚ Γ₀) (ModuleCat.{0} ℚ)))
    (((CategoryTheory.Functor.map_comp _ _ _).symm.trans (congrArg _ (resHomIso Z n Γ₀.subtype).hom_inv_id)).trans
      (CategoryTheory.Functor.map_id _ _))
  exact (congrArg (fun t => t.hom c) hF).symm

end Forget

end TernaryPeriodPolynomials.Argument.HochschildSerre
