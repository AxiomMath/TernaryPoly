module

public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeHomology.Hecke

@[expose] public section


/-!
# Computing the Hecke operator in an arbitrary projective resolution

Formalized by Claude Sonnet 5.5.  Lemma B.1, "The Hecke transfer".

Abstract homological algebra, nothing arithmetic.  For `ι : Γ →* Ĝ`, a Hecke datum `D` (`S ≤ Γ`, `f : S →* Γ`), a
`Ĝ`-representation `M` and any projective resolution `R` of the trivial `Γ`-module, a *lift* `lam` of the
correspondence is a chain map `Res_S R ⟶ Res_f R` over the identity (`LiftRes`, `LiftOverId`).  `ResHecke D M R lam`
is the endomorphism of the complex `(M ⊗ R_•)_Γ` given in degree `q` by the transfer `(M ⊗ R_q)_Γ → (M ⊗ R_q)_S`
followed by `[m ⊗ r] ↦ [g m ⊗ lam r]` (`ResHecke_f_mk`).

* `PhiMap f φ ℓ`: for `f : H →* G`, `φ : A_H ⟶ Res_f A_G` and a chain map `ℓ : P ⟶ Res_f Z`, the chain map
  `(A_H ⊗ P)_H → (A_G ⊗ Z)_G`, `[a ⊗ p] ↦ [φ a ⊗ ℓ p]`; compatible with composition and with homotopies.
* `groupHomologyIso_PhiMap`: for *any* projective resolution `P` of `H`, `R` of `G` with `Res_f R` projective termwise and
  any chain map `ℓ` over the identity, `PhiMap f φ ℓ` computes `groupHomology.map f φ n` through Mathlib's
  `groupHomologyIso` (via the bar resolutions, the explicit chain map `barMap f` and the comparison theorem).
* `groupHomologyIso_TYR`: the coset-sum transfer `trR` is computed by the termwise transfer in any resolution.
* `heckeOp_resolution`: `groupHomologyIso ≫ H_n(ResHecke) = heckeOp ≫ groupHomologyIso`.
-/


open CategoryTheory Representation Representation.Coinvariants MonoidalCategory
open TernaryPeriodPolynomials.Argument.GroupHomology

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HeckeHomology

section General

variable {H G : Type} [Group H] [Group G] (f : H →* G) {AH : Rep.{0} ℚ H} {AG : Rep.{0} ℚ G}
  (φ : AH ⟶ Rep.res f AG)

/-- `a ⊗ z ↦ φ a ⊗ z` on coinvariants. -/
def WMap (Z : Rep.{0} ℚ G) :
    ((Rep.coinvariantsTensor ℚ H).obj AH).obj (Rep.res f Z) ⟶
      ((Rep.coinvariantsTensor ℚ G).obj AG).obj Z :=
  ModuleCat.ofHom (Coinvariants.lift (AH.ρ.tprod (Z.ρ.comp f))
    ((Coinvariants.mk (AG.ρ.tprod Z.ρ)) ∘ₗ TensorProduct.map φ.hom.toLinearMap LinearMap.id)
    (fun h => TensorProduct.ext' fun a z => by
      have h1 : φ.hom (AH.ρ h a) = AG.ρ (f h) (φ.hom a) := Rep.hom_comm_apply φ h a
      change Coinvariants.mk (AG.ρ.tprod Z.ρ) (φ.hom (AH.ρ h a) ⊗ₜ[ℚ] Z.ρ (f h) z) =
        Coinvariants.mk (AG.ρ.tprod Z.ρ) (φ.hom a ⊗ₜ[ℚ] z)
      rw [h1]
      exact Coinvariants.mk_self_apply (AG.ρ.tprod Z.ρ) (f h) (φ.hom a ⊗ₜ[ℚ] z)))

theorem WMap_mk (Z : Rep.{0} ℚ G) (a : AH) (z : Z) :
    (WMap f φ Z).hom (Coinvariants.mk _ (a ⊗ₜ[ℚ] z)) =
      Coinvariants.mk (AG.ρ.tprod Z.ρ) (φ.hom a ⊗ₜ[ℚ] z) := rfl

/-- The natural transformation `W`. -/
def WNat : Rep.resFunctor f ⋙ (Rep.coinvariantsTensor ℚ H).obj AH ⟶
    (Rep.coinvariantsTensor ℚ G).obj AG where
  app Z := WMap f φ Z
  naturality Z Z' u := by
    refine Rep.coinvariantsTensor_hom_ext (LinearMap.ext fun a => LinearMap.ext fun z => ?_)
    rfl

/-- Chain-level `W`. -/
def WChain (Z : ChainComplex (Rep.{0} ℚ G) ℕ) :
    (((Rep.coinvariantsTensor ℚ H).obj AH).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (((Rep.resFunctor f).mapHomologicalComplex (ComplexShape.down ℕ)).obj Z) ⟶
      (((Rep.coinvariantsTensor ℚ G).obj AG).mapHomologicalComplex (ComplexShape.down ℕ)).obj Z :=
  (NatTrans.mapHomologicalComplex (WNat f φ) (ComplexShape.down ℕ)).app Z

theorem WChain_natural {Z Z' : ChainComplex (Rep.{0} ℚ G) ℕ} (u : Z ⟶ Z') :
    (((Rep.coinvariantsTensor ℚ H).obj AH).mapHomologicalComplex (ComplexShape.down ℕ)).map
        (((Rep.resFunctor f).mapHomologicalComplex (ComplexShape.down ℕ)).map u) ≫ WChain f φ Z' =
      WChain f φ Z ≫
        (((Rep.coinvariantsTensor ℚ G).obj AG).mapHomologicalComplex (ComplexShape.down ℕ)).map u :=
  (NatTrans.mapHomologicalComplex (WNat f φ) (ComplexShape.down ℕ)).naturality u

/-- The chain map `(AH ⊗ P)_H → (AG ⊗ Z)_G` attached to a chain map `ℓ : P → Res_f Z`. -/
def PhiMap {P : ChainComplex (Rep.{0} ℚ H) ℕ} {Z : ChainComplex (Rep.{0} ℚ G) ℕ}
    (ℓ : P ⟶ ((Rep.resFunctor f).mapHomologicalComplex (ComplexShape.down ℕ)).obj Z) :
    (((Rep.coinvariantsTensor ℚ H).obj AH).mapHomologicalComplex (ComplexShape.down ℕ)).obj P ⟶
      (((Rep.coinvariantsTensor ℚ G).obj AG).mapHomologicalComplex (ComplexShape.down ℕ)).obj Z :=
  (((Rep.coinvariantsTensor ℚ H).obj AH).mapHomologicalComplex (ComplexShape.down ℕ)).map ℓ ≫
    WChain f φ Z

theorem PhiMap_f_mk {P : ChainComplex (Rep.{0} ℚ H) ℕ} {Z : ChainComplex (Rep.{0} ℚ G) ℕ}
    (ℓ : P ⟶ ((Rep.resFunctor f).mapHomologicalComplex (ComplexShape.down ℕ)).obj Z) (q : ℕ)
    (a : AH) (p : P.X q) :
    ((PhiMap f φ ℓ).f q).hom (Coinvariants.mk _ (a ⊗ₜ[ℚ] p)) =
      Coinvariants.mk (AG.ρ.tprod (Z.X q).ρ) (φ.hom a ⊗ₜ[ℚ] (ℓ.f q).hom p) := rfl

theorem PhiMap_comp_left {P P' : ChainComplex (Rep.{0} ℚ H) ℕ} {Z : ChainComplex (Rep.{0} ℚ G) ℕ}
    (a : P' ⟶ P)
    (ℓ : P ⟶ ((Rep.resFunctor f).mapHomologicalComplex (ComplexShape.down ℕ)).obj Z) :
    PhiMap f φ (a ≫ ℓ) =
      (((Rep.coinvariantsTensor ℚ H).obj AH).mapHomologicalComplex (ComplexShape.down ℕ)).map a ≫
        PhiMap f φ ℓ := by
  unfold PhiMap
  rw [Functor.map_comp, Category.assoc]

theorem PhiMap_comp_right {P : ChainComplex (Rep.{0} ℚ H) ℕ} {Z Z' : ChainComplex (Rep.{0} ℚ G) ℕ}
    (ℓ : P ⟶ ((Rep.resFunctor f).mapHomologicalComplex (ComplexShape.down ℕ)).obj Z)
    (u : Z ⟶ Z') :
    PhiMap f φ (ℓ ≫ ((Rep.resFunctor f).mapHomologicalComplex (ComplexShape.down ℕ)).map u) =
      PhiMap f φ ℓ ≫
        (((Rep.coinvariantsTensor ℚ G).obj AG).mapHomologicalComplex (ComplexShape.down ℕ)).map u := by
  unfold PhiMap
  rw [Functor.map_comp, Category.assoc, WChain_natural, Category.assoc]

theorem PhiMap_homologyMap_congr {P : ChainComplex (Rep.{0} ℚ H) ℕ} {Z : ChainComplex (Rep.{0} ℚ G) ℕ}
    {ℓ ℓ' : P ⟶ ((Rep.resFunctor f).mapHomologicalComplex (ComplexShape.down ℕ)).obj Z}
    (h : Homotopy ℓ ℓ') (n : ℕ) :
    HomologicalComplex.homologyMap (PhiMap f φ ℓ) n =
      HomologicalComplex.homologyMap (PhiMap f φ ℓ') n := by
  have := (((Rep.coinvariantsTensor ℚ H).obj AH).mapHomotopy (c := ComplexShape.down ℕ) h).homologyMap_eq n
  unfold PhiMap
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp, this]


section Bar

variable [DecidableEq H] [DecidableEq G]

theorem inhom_PhiMap_barMap :
    (groupHomology.inhomogeneousChainsIso AH).hom ≫ PhiMap f φ (barMap (k := ℚ) f) =
      groupHomology.chainsMap f φ ≫ (groupHomology.inhomogeneousChainsIso AG).hom := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  refine groupHomology.inhomogeneousChains.ext fun x => ?_
  refine ModuleCat.hom_ext (LinearMap.ext fun a => ?_)
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.hom_ofHom, Finsupp.lsingle_apply]
  have eL := groupHomology.chainsMap_f_single f φ n x a
  have e1 := inhomIso_hom_f_single AH n x a
  have e2 := inhomIso_hom_f_single AG n (f ∘ x) (φ.hom a)
  have e3 : ((barMap (k := ℚ) f).f n).hom
      (Finsupp.single x (MonoidAlgebra.single (1 : H) (1 : ℚ))) =
      Finsupp.single (f ∘ x) (MonoidAlgebra.single (1 : G) (1 : ℚ)) := by
    change (barTerm (k := ℚ) f n).hom _ = _
    rw [barTerm_single, map_one]
  rw [eL, e2]
  change ((PhiMap f φ (barMap (k := ℚ) f)).f n).hom
      (((groupHomology.inhomogeneousChainsIso AH).hom.f n).hom (Finsupp.single x a)) = _
  rw [e1]
  refine (PhiMap_f_mk f φ (barMap (k := ℚ) f) n a _).trans ?_
  rw [e3]

theorem groupHomologyIso_PhiMap_bar (n : ℕ) :
    (groupHomologyIso AH n (Rep.barResolution ℚ H)).hom ≫
        HomologicalComplex.homologyMap (PhiMap f φ (barMap (k := ℚ) f)) n =
      groupHomology.map f φ n ≫ (groupHomologyIso AG n (Rep.barResolution ℚ G)).hom := by
  rw [groupHomologyIso_bar_hom, groupHomologyIso_bar_hom]
  have h1 := congrArg (fun c => HomologicalComplex.homologyMap c n) (inhom_PhiMap_barMap f φ)
  have hA := HomologicalComplex.homologyMap_comp (groupHomology.inhomogeneousChainsIso AH).hom
    (PhiMap f φ (barMap (k := ℚ) f)) n
  have hB := HomologicalComplex.homologyMap_comp (groupHomology.chainsMap f φ)
    (groupHomology.inhomogeneousChainsIso AG).hom n
  exact hA.symm.trans (h1.trans hB)

end Bar

theorem barMap_pi_gen :
    (barMap (k := ℚ) f).f 0 ≫ (Rep.resFunctor f).map ((Rep.barResolution ℚ G).π.f 0) =
      (Rep.barResolution ℚ H).π.f 0 := by
  refine Rep.free_ext _ _ _ _ _ fun x => ?_
  have h2 := barPi_f_zero (k := ℚ) (G := H) x 1 1
  have h3 := barPi_f_zero (k := ℚ) (G := G) (f ∘ x) 1 1
  refine Eq.trans ?_ h2.symm
  have key : ((Rep.resFunctor f).map ((Rep.barResolution ℚ G).π.f 0)).hom
      ((barTerm (k := ℚ) f 0).hom (Finsupp.single x (MonoidAlgebra.single 1 1))) =
      ((Rep.barResolution ℚ G).π.f 0).hom (Finsupp.single (f ∘ x) (MonoidAlgebra.single 1 1)) := by
    rw [barTerm_single, map_one]
    rfl
  exact key.trans h3

/-- `barMap` typed on the complexes of the bar resolutions. -/
def barMapR : (Rep.barResolution ℚ H).complex ⟶
    ((Rep.resFunctor f).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (Rep.barResolution ℚ G).complex :=
  barMap (k := ℚ) f

theorem groupHomologyIso_PhiMap_barR [DecidableEq H] [DecidableEq G] (n : ℕ) :
    (groupHomologyIso AH n (Rep.barResolution ℚ H)).hom ≫
        HomologicalComplex.homologyMap (PhiMap f φ (barMapR f)) n =
      groupHomology.map f φ n ≫ (groupHomologyIso AG n (Rep.barResolution ℚ G)).hom :=
  groupHomologyIso_PhiMap_bar f φ n

theorem barMapR_pi :
    (barMapR f).f 0 ≫ (Rep.resFunctor f).map ((Rep.barResolution ℚ G).π.f 0) =
      (Rep.barResolution ℚ H).π.f 0 := barMap_pi_gen f

/-- `Res_f R` as a projective resolution of the trivial `H`-module, given that its terms are
projective. -/
def resfResolution (R : ProjectiveResolution (Rep.trivial ℚ G ℚ))
    (hproj : ∀ q, Projective ((Rep.resFunctor f).obj (R.complex.X q))) :
    ProjectiveResolution ((Rep.resFunctor f).obj (Rep.trivial ℚ G ℚ)) where
  complex := ((Rep.resFunctor f).mapHomologicalComplex (ComplexShape.down ℕ)).obj R.complex
  projective := hproj
  π := ((Rep.resFunctor f).mapHomologicalComplex (ComplexShape.down ℕ)).map R.π ≫
    (HomologicalComplex.singleMapHomologicalComplex _ _ _).hom.app _
  quasiIso := inferInstance


/-- **Resolution independence of `groupHomology.map`.** For a chain map `ℓ` from a projective
resolution `P` of the trivial `H`-module to `Res_f R`, over the identity (`hℓ`), where `R` is a
projective resolution of the trivial `G`-module whose restriction to `H` along `f` has projective
terms, the map `Hₙ(AH ⊗ P)_H → Hₙ(AG ⊗ R)_G` induced by `ℓ` and `φ` is `groupHomology.map f φ n`. -/
theorem groupHomologyIso_PhiMap [DecidableEq H] [DecidableEq G]
    (R : ProjectiveResolution (Rep.trivial ℚ G ℚ))
    (hproj : ∀ q, Projective ((Rep.resFunctor f).obj (R.complex.X q)))
    (P : ProjectiveResolution (Rep.trivial ℚ H ℚ))
    (ℓ : P.complex ⟶ ((Rep.resFunctor f).mapHomologicalComplex (ComplexShape.down ℕ)).obj R.complex)
    (hℓ : ℓ.f 0 ≫ (Rep.resFunctor f).map (R.π.f 0) = P.π.f 0) (n : ℕ) :
    (groupHomologyIso AH n P).hom ≫ HomologicalComplex.homologyMap (PhiMap f φ ℓ) n =
      groupHomology.map f φ n ≫ (groupHomologyIso AG n R).hom := by
  let a : (Rep.barResolution ℚ H).complex ⟶ P.complex :=
    ProjectiveResolution.lift (𝟙 _) (Rep.barResolution ℚ H) P
  let u : (Rep.barResolution ℚ G).complex ⟶ R.complex :=
    ProjectiveResolution.lift (𝟙 _) (Rep.barResolution ℚ G) R
  have ha : a.f 0 ≫ P.π.f 0 = (Rep.barResolution ℚ H).π.f 0 :=
    (ProjectiveResolution.lift_commutes_zero (𝟙 _) (Rep.barResolution ℚ H) P).trans
      (Category.comp_id _)
  have hu : u.f 0 ≫ R.π.f 0 = (Rep.barResolution ℚ G).π.f 0 :=
    (ProjectiveResolution.lift_commutes_zero (𝟙 _) (Rep.barResolution ℚ G) R).trans
      (Category.comp_id _)
  have hg1 : (a ≫ ℓ) ≫ (resfResolution f R hproj).π =
      (Rep.barResolution ℚ H).π ≫ (ChainComplex.single₀ _).map (𝟙 (Rep.trivial ℚ H ℚ)) := by
    refine toSingle₀_ext' _ _ ?_
    exact ((Category.assoc (a.f 0) (ℓ.f 0) ((Rep.resFunctor f).map (R.π.f 0))).trans
      ((congrArg (fun z => a.f 0 ≫ z) hℓ).trans ha)).trans (Category.comp_id _).symm
  have hg2 : (barMapR f ≫ ((Rep.resFunctor f).mapHomologicalComplex (ComplexShape.down ℕ)).map u) ≫
      (resfResolution f R hproj).π =
      (Rep.barResolution ℚ H).π ≫ (ChainComplex.single₀ _).map (𝟙 (Rep.trivial ℚ H ℚ)) := by
    refine toSingle₀_ext' _ _ ?_
    have h1 : (Rep.resFunctor f).map (u.f 0) ≫ (Rep.resFunctor f).map (R.π.f 0) =
        (Rep.resFunctor f).map ((Rep.barResolution ℚ G).π.f 0) := by
      rw [← Functor.map_comp, hu]
    exact ((Category.assoc ((barMapR f).f 0) ((Rep.resFunctor f).map (u.f 0))
      ((Rep.resFunctor f).map (R.π.f 0))).trans
      ((congrArg (fun z => (barMapR f).f 0 ≫ z) h1).trans (barMapR_pi f))).trans
      (Category.comp_id _).symm
  have hom : Homotopy (a ≫ ℓ) (barMapR f ≫
      ((Rep.resFunctor f).mapHomologicalComplex (ComplexShape.down ℕ)).map u) :=
    ProjectiveResolution.liftHomotopy (𝟙 _) (P := Rep.barResolution ℚ H)
      (Q := resfResolution f R hproj) _ _ hg1 hg2
  have i1 := groupHomologyIso_hom_comp AH n a ha
  have i2 := groupHomologyIso_hom_comp AG n u hu
  rw [← i1, Category.assoc, ← HomologicalComplex.homologyMap_comp, ← PhiMap_comp_left,
    PhiMap_homologyMap_congr f φ hom, PhiMap_comp_right, HomologicalComplex.homologyMap_comp,
    ← Category.assoc, groupHomologyIso_PhiMap_barR, Category.assoc, i2]

end General

section Transfer

open scoped Classical

variable {K : Type} [Group K] (N : Subgroup K) [N.FiniteIndex] (A : Rep.{0} ℚ K)
  (R : ProjectiveResolution (Rep.trivial ℚ K ℚ))

/-- `A ⊗ R_•`. -/
abbrev YR : ChainComplex (Rep.{0} ℚ K) ℕ :=
  ((tensorLeft A).mapHomologicalComplex (ComplexShape.down ℕ)).obj R.complex

theorem TYR_natural {P Q : ChainComplex (Rep.{0} ℚ K) ℕ} (u : P ⟶ Q) :
    ((cK (k := ℚ) (K := K)).mapHomologicalComplex (ComplexShape.down ℕ)).map u ≫ TYR N Q =
      TYR N P ≫ ((cN (k := ℚ) N).mapHomologicalComplex (ComplexShape.down ℕ)).map u :=
  (NatTrans.mapHomologicalComplex (tNatR N) (ComplexShape.down ℕ)).naturality u

/-- **The transfer computed in an arbitrary projective resolution.** -/
theorem groupHomologyIso_TYR (n : ℕ) :
    (groupHomologyIso A n R).hom ≫ HomologicalComplex.homologyMap (TYR N (YR A R)) n =
      trR N A n ≫ (groupHomologyIso (Rep.res N.subtype A) n
        ((Rep.resFunctor N.subtype).mapProjectiveResolution R)).hom := by
  let u : (Rep.barResolution ℚ K).complex ⟶ R.complex :=
    ProjectiveResolution.lift (𝟙 _) (Rep.barResolution ℚ K) R
  have hu : u.f 0 ≫ R.π.f 0 = (Rep.barResolution ℚ K).π.f 0 :=
    (ProjectiveResolution.lift_commutes_zero (𝟙 _) (Rep.barResolution ℚ K) R).trans
      (Category.comp_id _)
  let ures : ((Rep.resFunctor N.subtype).mapProjectiveResolution (Rep.barResolution ℚ K)).complex ⟶
      ((Rep.resFunctor N.subtype).mapProjectiveResolution R).complex :=
    ((Rep.resFunctor N.subtype).mapHomologicalComplex (ComplexShape.down ℕ)).map u
  have hures : ures.f 0 ≫ ((Rep.resFunctor N.subtype).mapProjectiveResolution R).π.f 0 =
      ((Rep.resFunctor N.subtype).mapProjectiveResolution (Rep.barResolution ℚ K)).π.f 0 := by
    change (Rep.resFunctor N.subtype).map (u.f 0) ≫ (Rep.resFunctor N.subtype).map (R.π.f 0) = _
    rw [← Functor.map_comp, hu]
    rfl
  have i1 := groupHomologyIso_hom_comp A n u hu
  have i2 := groupHomologyIso_hom_comp (Rep.res N.subtype A) n ures hures
  have hnat := TYR_natural N (((tensorLeft A).mapHomologicalComplex (ComplexShape.down ℕ)).map u)
  have heN : (eN N A n).hom = (groupHomologyIso (Rep.res N.subtype A) n
      ((Rep.resFunctor N.subtype).mapProjectiveResolution (Rep.barResolution ℚ K))).hom := rfl
  have hcn : HomologicalComplex.homologyMap
      ((((Rep.coinvariantsTensor ℚ N).obj (Rep.res N.subtype A)).mapHomologicalComplex
        (ComplexShape.down ℕ)).map ures) n =
      HomologicalComplex.homologyMap (((cN (k := ℚ) N).mapHomologicalComplex (ComplexShape.down ℕ)).map
        (((tensorLeft A).mapHomologicalComplex (ComplexShape.down ℕ)).map u)) n := rfl
  have hck : HomologicalComplex.homologyMap
      ((((Rep.coinvariantsTensor ℚ K).obj A).mapHomologicalComplex
        (ComplexShape.down ℕ)).map u) n =
      HomologicalComplex.homologyMap (((cK (k := ℚ) (K := K)).mapHomologicalComplex (ComplexShape.down ℕ)).map
        (((tensorLeft A).mapHomologicalComplex (ComplexShape.down ℕ)).map u)) n := rfl
  rw [← i1]
  erw [Category.assoc, hck, ← HomologicalComplex.homologyMap_comp, hnat,
    HomologicalComplex.homologyMap_comp, ← Category.assoc, ← i2, ← heN, hcn]
  have key : trR N A n ≫ (eN N A n).hom =
      (eK A n).hom ≫ HomologicalComplex.homologyMap (TYR N (YA A)) n := by
    unfold trR
    rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  erw [← Category.assoc, key]
  rfl

end Transfer

section Hecke

open scoped Classical

variable {Γ Ĝ : Type} [Group Γ] [Group Ĝ] {ι : Γ →* Ĝ} {g : Ĝ} (D : HeckeDatum ι g) (M : Rep.{0} ℚ Ĝ)
  (R : ProjectiveResolution (Rep.trivial ℚ Γ ℚ))

/-- The terms `Res_S R_q` and `Res_f R_q` as complexes of `S`-modules: a **lift** of the Hecke
correspondence to `R` is a chain map between them. -/
abbrev LiftRes :=
  ((Rep.resFunctor D.S.subtype).mapHomologicalComplex (ComplexShape.down ℕ)).obj R.complex ⟶
    ((Rep.resFunctor D.f).mapHomologicalComplex (ComplexShape.down ℕ)).obj R.complex

/-- A lift is over the identity of the trivial module. -/
def LiftOverId (lam : LiftRes D R) : Prop :=
  lam.f 0 ≫ (Rep.resFunctor D.f).map (R.π.f 0) = (Rep.resFunctor D.S.subtype).map (R.π.f 0)

/-- **The ambient Hecke operator in the resolution `R`**: in degree `q` the composite
`(M ⊗ R_q)_Γ → (M ⊗ R_q)_S → (M ⊗ R_q)_Γ`, transfer followed by `m ⊗ r ↦ g m ⊗ lam r`. -/
def ResHecke (lam : LiftRes D R) :
    R.complex.coinvariantsTensorObj (Rep.res ι M) ⟶ R.complex.coinvariantsTensorObj (Rep.res ι M) :=
  haveI := D.finiteIndex
  TYR D.S (YR (Rep.res ι M) R) ≫
    PhiMap (AH := Rep.res D.S.subtype (Rep.res ι M)) (AG := Rep.res ι M)
      (P := ((Rep.resFunctor D.S.subtype).mapHomologicalComplex (ComplexShape.down ℕ)).obj R.complex)
      (Z := R.complex) D.f (corrMap D M) lam

/-- **Lemma B.1, resolution model.** The Hecke operator of a Hecke datum is computed in any projective
resolution `R` of the trivial `Γ`-module, by the ambient operator `ResHecke D M R lam` attached to any
lift `lam` of the correspondence (a chain map `Res_S R → Res_f R` over the identity) when the terms of
`Res_f R` are projective. -/
theorem heckeOp_resolution (lam : LiftRes D R) (hlam : LiftOverId D R lam)
    (hproj : ∀ q, Projective ((Rep.resFunctor D.f).obj (R.complex.X q))) (n : ℕ) :
    (groupHomologyIso (Rep.res ι M) n R).hom ≫ HomologicalComplex.homologyMap (ResHecke D M R lam) n =
      heckeOp D M n ≫ (groupHomologyIso (Rep.res ι M) n R).hom := by
  have := D.finiteIndex
  have hT := groupHomologyIso_TYR D.S (Rep.res ι M) R n
  have hP := groupHomologyIso_PhiMap D.f (corrMap D M) R hproj
    ((Rep.resFunctor D.S.subtype).mapProjectiveResolution R) lam hlam n
  unfold ResHecke heckeOp
  erw [HomologicalComplex.homologyMap_comp, ← Category.assoc, hT, Category.assoc, hP, Category.assoc]

instance instFiniteIndexHeckeS : D.S.FiniteIndex := D.finiteIndex

/-- The ambient operator on generators: `[m ⊗ r] ↦ ∑_{S x ∈ S\\Γ} [g (x m) ⊗ lam (x r)]`. -/
theorem ResHecke_f_mk (lam : LiftRes D R) (q : ℕ) (m : Rep.res ι M) (r : R.complex.X q) :
    ((ResHecke D M R lam).f q).hom (Coinvariants.mk _ (m ⊗ₜ[ℚ] r)) =
      ∑ x : RC D.S, Coinvariants.mk ((Rep.res ι M).ρ.tprod (R.complex.X q).ρ)
        (M.ρ g ((Rep.res ι M).ρ x.out m) ⊗ₜ[ℚ] (lam.f q).hom ((R.complex.X q).ρ x.out r)) := by
  have h1 : ((TYR D.S (YR (Rep.res ι M) R)).f q).hom (Coinvariants.mk _ (m ⊗ₜ[ℚ] r)) =
      ∑ x : RC D.S, Coinvariants.mk (((Rep.res ι M).ρ.tprod (R.complex.X q).ρ).comp D.S.subtype)
        (((Rep.res ι M).ρ.tprod (R.complex.X q).ρ) x.out (m ⊗ₜ[ℚ] r)) := tSumR_apply _ _ _
  have h2 := fun (a : Rep.res D.S.subtype (Rep.res ι M)) (p : (Rep.resFunctor D.S.subtype).obj (R.complex.X q)) =>
    PhiMap_f_mk (AH := Rep.res D.S.subtype (Rep.res ι M)) (AG := Rep.res ι M)
      (P := ((Rep.resFunctor D.S.subtype).mapHomologicalComplex (ComplexShape.down ℕ)).obj R.complex)
      (Z := R.complex) D.f (corrMap D M) lam q a p
  refine (congrArg (fun z => (PhiMap (AH := Rep.res D.S.subtype (Rep.res ι M)) (AG := Rep.res ι M)
      (P := ((Rep.resFunctor D.S.subtype).mapHomologicalComplex (ComplexShape.down ℕ)).obj R.complex)
      (Z := R.complex) D.f (corrMap D M) lam |>.f q).hom z) h1).trans ?_
  exact (map_sum _ _ _).trans (Finset.sum_congr rfl fun x _ => h2 _ _)

end Hecke
end TernaryPeriodPolynomials.Argument.HeckeHomology
