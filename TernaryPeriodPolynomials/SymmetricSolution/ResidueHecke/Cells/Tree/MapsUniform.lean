module

public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Tree.MapsMain

@[expose] public section


/-!
# Lemma B.1: the Schur scalar of the Hochschild-Serre tree formula does not depend on the coefficient module

Formalized by Claude Sonnet 5.5.

For a `U`-trivial finite-dimensional `P`-module `A` and `a ∈ A`, the map `Ψ'_A(a ⊗ ℓ₀) = [Θ₂(a ⊗ ℓ₀ ⊗ s₀)] ∈ H₂(Z_R(A))` and the
fundamental-class isomorphism `Γ_A(a) = H₂(fZ) (gammaEquiv a)` are both natural along the linear map `τ_a : ℚ → A`, `1 ↦ a`, at the
level of the vector-space complexes of `U`-coinvariants (`nuNat`, `etaBar`, `etaR`; the chain-level squares `beta_nat`,
`etaR_square`; `eN_nat`, `psi_nat`, `gamma_nat`, `psiInst_nat`).  Hence `Ψ'_A(a ⊗ ℓ₀) = c₀ Γ_A(a)` with ONE scalar `c₀` fixed by the
case `A = ℚ` (`psiInst_universal`); `lam` in `Schur_scalar` is this `c₀` for every `A`.
-/

open CategoryTheory MonoidalCategory Representation Limits
open scoped TensorProduct

noncomputable section

namespace TernaryPeriodPolynomials.Argument.AppendixBResidue

open TernaryPeriodPolynomials.Argument.HochschildSerre
open TernaryPeriodPolynomials.Argument.GroupHomology
open TernaryPeriodPolynomials.Argument.GroupHomologyDescent (T2 U2)

section Nu

variable {P : Type} [Group P] (U : Subgroup P) {A : Rep.{0} ℚ P} (hA : ∀ u : U, A.ρ u = 1) (a : A.V)

/-- `c ⊗ x ↦ c a ⊗ x` on `U`-coinvariants of `ℚ ⊗ X → A ⊗ X`. -/
def nuLinMap (X : Rep.{0} ℚ P) :
    Coinvariants ((Rep.trivial ℚ P ℚ ⊗ X).ρ.comp U.subtype) →ₗ[ℚ]
      Coinvariants ((A ⊗ X).ρ.comp U.subtype) :=
  Coinvariants.lift _ ((Coinvariants.mk _) ∘ₗ
      (TensorProduct.map (LinearMap.toSpanSingleton ℚ A.V a) LinearMap.id))
    (fun u => by
      refine TensorProduct.ext' fun c x => ?_
      have h := Coinvariants.mk_self_apply ((A ⊗ X).ρ.comp U.subtype) u (c • a ⊗ₜ[ℚ] x)
      have hu := hA u
      simpa [Representation.tprod_apply, hu, ← TensorProduct.smul_tmul', map_smul] using h)

theorem nuLinMap_mk (X : Rep.{0} ℚ P) (c : ℚ) (x : X.V) :
    nuLinMap U hA a X (Coinvariants.mk _ (c ⊗ₜ[ℚ] x)) = Coinvariants.mk _ ((c • a) ⊗ₜ[ℚ] x) := rfl

/-- The natural transformation `c ⊗ x ↦ c a ⊗ x` on `U`-coinvariants of `A ⊗ X`. -/
def nuNat : (tensorLeft (Rep.trivial ℚ P ℚ)) ⋙ cN (k := ℚ) U ⟶ (tensorLeft A) ⋙ cN (k := ℚ) U where
  app X := ModuleCat.ofHom (nuLinMap U hA a X)
  naturality X Y f := by
    refine ModuleCat.hom_ext (Coinvariants.hom_ext (TensorProduct.ext' fun c x => ?_))
    rfl

end Nu


section Eta

variable {P : Type} [Group P] (U : Subgroup P) {A : Rep.{0} ℚ P} (hA : ∀ u : U, A.ρ u = 1) (a : A.V)

/-- The chain map `ℚ ⊗ bar → A ⊗ bar` on `U`-coinvariants. -/
def etaBar : CxN U (YA (Rep.trivial ℚ P ℚ)) ⟶ CxN U (YA A) :=
  (NatTrans.mapHomologicalComplex (nuNat U hA a) (ComplexShape.down ℕ)).app (Rep.barComplex ℚ P)

theorem etaBar_f_mk (j : ℕ) (c : ℚ) (x : ((Rep.barComplex ℚ P).X j).V) :
    ((etaBar U hA a).f j).hom (Coinvariants.mk _ (c ⊗ₜ[ℚ] x)) = Coinvariants.mk _ ((c • a) ⊗ₜ[ℚ] x) := rfl

/-- The morphism `ℚ → A`, `1 ↦ a`, of `U`-representations. -/
def tauU : Rep.res U.subtype (Rep.trivial ℚ P ℚ) ⟶ Rep.res U.subtype A :=
  Rep.ofHom ⟨LinearMap.toSpanSingleton ℚ A.V a, fun u => by
    refine LinearMap.ext fun c => ?_
    have := hA u
    simp [this]⟩

theorem beta_nat :
    groupHomology.chainsMap (MonoidHom.id U) (tauU U hA a) ≫ betaA U A =
      betaA U (Rep.trivial ℚ P ℚ) ≫ etaBar U hA a := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  refine groupHomology.inhomogeneousChains.ext fun x => ?_
  refine ModuleCat.hom_ext (LinearMap.ext fun c => ?_)
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    Finsupp.lsingle_apply]
  have e1 := groupHomology.chainsMap_f_single (A := Rep.res U.subtype (Rep.trivial ℚ P ℚ))
    (B := Rep.res U.subtype A) (MonoidHom.id U) (tauU U hA a) n x c
  erw [e1]
  erw [betaA_single U A n (fun i => (MonoidHom.id U) (x i)) (c • a)]
  have e2 := betaA_single U (Rep.trivial ℚ P ℚ) n x c
  have e3 := congrArg (fun z => ((etaBar U hA a).f n).hom z) e2
  refine Eq.trans ?_ e3.symm
  exact (etaBar_f_mk U hA a n c _).symm

theorem eN_nat [U.Normal] (n : ℕ) :
    groupHomology.map (MonoidHom.id U) (tauU U hA a) n ≫ (eN U A n).hom =
      (eN U (Rep.trivial ℚ P ℚ) n).hom ≫ HomologicalComplex.homologyMap (etaBar U hA a) n := by
  rw [eN_hom, eN_hom]
  have h := congrArg (fun φ => HomologicalComplex.homologyMap φ n) (beta_nat U hA a)
  have h1 := HomologicalComplex.homologyMap_comp (groupHomology.chainsMap (MonoidHom.id U) (tauU U hA a))
    (betaA U A) n
  have h2 := HomologicalComplex.homologyMap_comp (betaA U (Rep.trivial ℚ P ℚ)) (etaBar U hA a) n
  exact h1.symm.trans (h.trans h2)

variable (eU : U2 ≃* U)

theorem psi_nat (hA₀ : ∀ u : U, (Rep.trivial ℚ P ℚ).ρ u = 1) (x : groupHomology (TV (Rep.trivial ℚ P ℚ).V) 2) :
    groupHomology.map (MonoidHom.id U) (tauU U hA a) 2 ((PsiIso eU hA₀).hom.hom x) =
      (PsiIso eU hA).hom.hom
        (groupHomology.map (MonoidHom.id U2) (trivHom (LinearMap.toSpanSingleton ℚ A.V a)) 2 x) := by
  let φ0 : TV (Rep.trivial ℚ P ℚ).V ⟶ Rep.res eU.toMonoidHom (Rep.res U.subtype (Rep.trivial ℚ P ℚ)) :=
    Rep.ofHom ⟨(LinearEquiv.refl ℚ (Rep.trivial ℚ P ℚ).V).toLinearMap, fun g => by
      rfl⟩
  let φ1 : TV A.V ⟶ Rep.res eU.toMonoidHom (Rep.res U.subtype A) :=
    Rep.ofHom ⟨(LinearEquiv.refl ℚ A.V).toLinearMap, fun g => by
      ext a
      change a = (A.ρ (eU g).1) a
      have : A.ρ (eU g).1 = 1 := hA (eU g)
      rw [this]; rfl⟩
  have hL := groupHomology.map_comp (C := Rep.res U.subtype A) eU.toMonoidHom (MonoidHom.id U) φ0
    (tauU U hA a) 2
  have hR := groupHomology.map_comp (C := Rep.res U.subtype A) (MonoidHom.id U2) eU.toMonoidHom
    (trivHom (LinearMap.toSpanSingleton ℚ A.V a)) φ1 2
  have hfg : (MonoidHom.id U).comp eU.toMonoidHom = eU.toMonoidHom.comp (MonoidHom.id U2) := rfl
  have hc : groupHomology.map eU.toMonoidHom φ0 2 ≫ groupHomology.map (MonoidHom.id U) (tauU U hA a) 2 =
      groupHomology.map (MonoidHom.id U2) (trivHom (LinearMap.toSpanSingleton ℚ A.V a)) 2 ≫
        groupHomology.map eU.toMonoidHom φ1 2 :=
    hL.symm.trans ((groupHomology.map_congr hfg (by ext; rfl) 2).trans hR)
  have := congrArg (fun φ => φ.hom x) hc
  exact this

end Eta

section Gamma

variable {P : Type} [Group P] (U : Subgroup P) [U.Normal] (eU : U2 ≃* U)
  (R : ProjectiveResolution (Rep.trivial ℚ P ℚ)) {A : Rep.{0} ℚ P} (hA : ∀ u : U, A.ρ u = 1) (a : A.V)

/-- The chain map `ℚ ⊗ R → A ⊗ R` on `U`-coinvariants. -/
def etaR : CxN U (YAR R (Rep.trivial ℚ P ℚ)) ⟶ CxN U (YAR R A) :=
  (NatTrans.mapHomologicalComplex (nuNat U hA a) (ComplexShape.down ℕ)).app R.complex

omit [U.Normal] in
theorem etaR_square : etaBar U hA a ≫ CxNf U R A = CxNf U R (Rep.trivial ℚ P ℚ) ≫ etaR U R hA a :=
  ((NatTrans.mapHomologicalComplex (nuNat U hA a) (ComplexShape.down ℕ)).naturality (fR R)).symm

variable [Representation.IsTrivial (A.ρ.comp U.subtype)] [Module.Finite ℚ A.V]

/-- The transport of `etaR` to the Rep-level homology (vector spaces). -/
def nuH : ((ZR U R (Rep.trivial ℚ P ℚ)).homology 2).V →ₗ[ℚ] ((ZR U R A).homology 2).V :=
  LinearMap.comp (((ZR U R A).sc 2).mapHomologyIso (forget₂ (Rep.{0} ℚ (P ⧸ U)) (ModuleCat ℚ))).hom.hom
    (LinearMap.comp (HomologicalComplex.homologyMap (etaR U R hA a) 2).hom
      (((ZR U R (Rep.trivial ℚ P ℚ)).sc 2).mapHomologyIso (forget₂ (Rep.{0} ℚ (P ⧸ U)) (ModuleCat ℚ))).inv.hom)

omit [Representation.IsTrivial (A.ρ.comp U.subtype)] [Module.Finite ℚ A.V] in
theorem nuH_apply (z : ((ZR U R (Rep.trivial ℚ P ℚ)).homology 2).V) :
    nuH U R hA a z = (((ZR U R A).sc 2).mapHomologyIso (forget₂ (Rep.{0} ℚ (P ⧸ U)) (ModuleCat ℚ))).hom.hom
      ((HomologicalComplex.homologyMap (etaR U R hA a) 2).hom
        ((((ZR U R (Rep.trivial ℚ P ℚ)).sc 2).mapHomologyIso
          (forget₂ (Rep.{0} ℚ (P ⧸ U)) (ModuleCat ℚ))).inv.hom z)) := rfl

omit [Representation.IsTrivial (A.ρ.comp U.subtype)] [Module.Finite ℚ A.V] in
theorem nuH_hom (z : (((ZR U R (Rep.trivial ℚ P ℚ)).sc 2).map (forget₂ (Rep.{0} ℚ (P ⧸ U)) (ModuleCat ℚ))).homology) :
    nuH U R hA a ((((ZR U R (Rep.trivial ℚ P ℚ)).sc 2).mapHomologyIso
      (forget₂ (Rep.{0} ℚ (P ⧸ U)) (ModuleCat ℚ))).hom.hom z) =
      (((ZR U R A).sc 2).mapHomologyIso (forget₂ (Rep.{0} ℚ (P ⧸ U)) (ModuleCat ℚ))).hom.hom
        ((HomologicalComplex.homologyMap (etaR U R hA a) 2).hom z) := by
  refine (nuH_apply U R hA a _).trans ?_
  have := congrArg (fun m => m.hom z) ((((ZR U R (Rep.trivial ℚ P ℚ)).sc 2).mapHomologyIso
      (forget₂ (Rep.{0} ℚ (P ⧸ U)) (ModuleCat ℚ))).hom_inv_id)
  change _ = _
  rw [show ((((ZR U R (Rep.trivial ℚ P ℚ)).sc 2).mapHomologyIso
      (forget₂ (Rep.{0} ℚ (P ⧸ U)) (ModuleCat ℚ))).inv.hom
      (((((ZR U R (Rep.trivial ℚ P ℚ)).sc 2).mapHomologyIso
      (forget₂ (Rep.{0} ℚ (P ⧸ U)) (ModuleCat ℚ))).hom).hom z)) = z from this]

theorem gamma_nat (hA₀ : ∀ u : U, (Rep.trivial ℚ P ℚ).ρ u = 1) :
    (HomologicalComplex.homologyMap (fZ U R A) 2).hom (gammaEquiv eU hA a) =
      nuH U R hA a ((HomologicalComplex.homologyMap (fZ U R (Rep.trivial ℚ P ℚ)) 2).hom
        (gammaEquiv eU hA₀ 1)) := by
  have : Module.Finite ℚ (Rep.trivial ℚ P ℚ).V := inferInstanceAs (Module.Finite ℚ ℚ)
  -- the class `x_A(a)` in the vector-space homology of `CxN U (YA A)`
  have k := map_kappa (V := (Rep.trivial ℚ P ℚ).V) (LinearMap.toSpanSingleton ℚ A.V a) e1 e2 (1 : ℚ)
  have k1 : kappa0 A.V a = groupHomology.map (MonoidHom.id U2)
      (trivHom (LinearMap.toSpanSingleton ℚ A.V a)) 2 (kappa0 (Rep.trivial ℚ P ℚ).V 1) := by
    rw [kappa0, k]
    simp
  have k2 := psi_nat U hA a eU hA₀ (kappa0 (Rep.trivial ℚ P ℚ).V 1)
  have k3 := congrArg (fun φ => φ.hom ((PsiIso eU hA₀).hom.hom (kappa0 (Rep.trivial ℚ P ℚ).V 1)))
    (eN_nat U hA a 2)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at k3
  have key1 : (eN U A 2).hom.hom ((PsiIso eU hA).hom.hom (kappa0 A.V a)) =
      (HomologicalComplex.homologyMap (etaBar U hA a) 2).hom
        ((eN U (Rep.trivial ℚ P ℚ) 2).hom.hom ((PsiIso eU hA₀).hom.hom (kappa0 (Rep.trivial ℚ P ℚ).V 1))) := by
    rw [k1, ← k2]
    exact k3
  set xQ := (eN U (Rep.trivial ℚ P ℚ) 2).hom.hom
    ((PsiIso eU hA₀).hom.hom (kappa0 (Rep.trivial ℚ P ℚ).V 1)) with hxQ
  have hg : ∀ (B : Rep.{0} ℚ P) [Representation.IsTrivial (B.ρ.comp U.subtype)] [Module.Finite ℚ B.V]
      (hB : ∀ u : U, B.ρ u = 1) (y : B.V), gammaEquiv eU hB y =
        (((ZP U B).sc 2).mapHomologyIso (forget₂ (Rep.{0} ℚ (P ⧸ U)) (ModuleCat ℚ))).hom.hom
          ((eN U B 2).hom.hom ((PsiIso eU hB).hom.hom (kappa0 B.V y))) := fun _ _ _ _ _ => rfl
  have hN : ∀ (B : Rep.{0} ℚ P) (z : ((CxN U (YA B)).homology 2)),
      (HomologicalComplex.homologyMap (fZ U R B) 2).hom
        ((((ZP U B).sc 2).mapHomologyIso (forget₂ (Rep.{0} ℚ (P ⧸ U)) (ModuleCat ℚ))).hom.hom z) =
      (((ZR U R B).sc 2).mapHomologyIso (forget₂ (Rep.{0} ℚ (P ⧸ U)) (ModuleCat ℚ))).hom.hom
        ((HomologicalComplex.homologyMap (CxNf U R B) 2).hom z) := by
    intro B z
    have hN := ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor _ (ComplexShape.down ℕ) 2).map (fZ U R B))
      (forget₂ (Rep.{0} ℚ (P ⧸ U)) (ModuleCat ℚ))
    have h1 := congrArg (fun m => m.hom z) hN
    simp only [ModuleCat.hom_comp] at h1
    exact h1.symm
  have sqH : (HomologicalComplex.homologyMap (CxNf U R A) 2).hom
      ((HomologicalComplex.homologyMap (etaBar U hA a) 2).hom xQ) =
      (HomologicalComplex.homologyMap (etaR U R hA a) 2).hom
        ((HomologicalComplex.homologyMap (CxNf U R (Rep.trivial ℚ P ℚ)) 2).hom xQ) := by
    have h := congrArg (fun φ => HomologicalComplex.homologyMap φ 2) (etaR_square U R hA a)
    have h1 := HomologicalComplex.homologyMap_comp (etaBar U hA a) (CxNf U R A) 2
    have h2 := HomologicalComplex.homologyMap_comp (CxNf U R (Rep.trivial ℚ P ℚ)) (etaR U R hA a) 2
    have h3 := congrArg (fun m => m.hom xQ) (h1.symm.trans (h.trans h2))
    exact h3
  have hinv : ∀ z, ((((ZR U R (Rep.trivial ℚ P ℚ)).sc 2).mapHomologyIso
      (forget₂ (Rep.{0} ℚ (P ⧸ U)) (ModuleCat ℚ))).inv).hom
      (((((ZR U R (Rep.trivial ℚ P ℚ)).sc 2).mapHomologyIso
        (forget₂ (Rep.{0} ℚ (P ⧸ U)) (ModuleCat ℚ))).hom).hom z) = z := fun z => by
    have := congrArg (fun m => m.hom z) ((((ZR U R (Rep.trivial ℚ P ℚ)).sc 2).mapHomologyIso
      (forget₂ (Rep.{0} ℚ (P ⧸ U)) (ModuleCat ℚ))).hom_inv_id)
    exact this
  rw [hg A hA a, key1, hN A, hg (Rep.trivial ℚ P ℚ) hA₀ 1, hN (Rep.trivial ℚ P ℚ)]
  have fin : ∀ z, nuH U R hA a ((((ZR U R (Rep.trivial ℚ P ℚ)).sc 2).mapHomologyIso
      (forget₂ (Rep.{0} ℚ (P ⧸ U)) (ModuleCat ℚ))).hom.hom z) =
      (((ZR U R A).sc 2).mapHomologyIso (forget₂ (Rep.{0} ℚ (P ⧸ U)) (ModuleCat ℚ))).hom.hom
        ((HomologicalComplex.homologyMap (etaR U R hA a) 2).hom z) := fun z =>
    (nuH_apply U R hA a _).trans (by rw [hinv])
  rw [sqH]
  exact (fin _).symm

end Gamma

section Cls

variable {Q : Type} [Group Q]

open TernaryPeriodPolynomials.Argument.HochschildSerre in
/-- The vector-space class of the cycle `Θ n` of the complex `Z`. -/
def clsV (Z : ChainComplex (Rep.{0} ℚ Q) ℕ) {N : Rep.{0} ℚ Q} (Θ : N ⟶ Z.X 2) (hΘ : Θ ≫ Z.d 2 1 = 0)
    (n : N.V) : (((Z.sc 2).map (forget₂ (Rep.{0} ℚ Q) (ModuleCat ℚ))).homology) :=
  ((Z.sc 2).map (forget₂ (Rep.{0} ℚ Q) (ModuleCat ℚ))).homologyπ.hom
    (((Z.sc 2).mapCyclesIso (forget₂ (Rep.{0} ℚ Q) (ModuleCat ℚ))).inv.hom
      (((forget₂ (Rep.{0} ℚ Q) (ModuleCat ℚ)).map (Z.liftCycles Θ 1 next21 hΘ)).hom n))

open TernaryPeriodPolynomials.Argument.HochschildSerre in
theorem clsV_spec (Z : ChainComplex (Rep.{0} ℚ Q) ℕ) {N : Rep.{0} ℚ Q} (Θ : N ⟶ Z.X 2) (hΘ : Θ ≫ Z.d 2 1 = 0)
    (n : N.V) :
    ((Z.sc 2).mapHomologyIso (forget₂ (Rep.{0} ℚ Q) (ModuleCat ℚ))).hom.hom (clsV Z Θ hΘ n) =
      (Z.liftCycles Θ 1 next21 hΘ ≫ Z.homologyπ 2).hom n := by
  let F := forget₂ (Rep.{0} ℚ Q) (ModuleCat ℚ)
  let S := Z.sc 2
  have hpi := piF F S
  let k : (F.obj S.cycles) := (F.map (Z.liftCycles Θ 1 next21 hΘ)).hom n
  let z : (S.map F).cycles := (S.mapCyclesIso F).inv.hom k
  have h1 := congrArg (fun t => t.hom z) hpi
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1
  have e : (S.mapCyclesIso F).hom.hom z = k := by
    have := congrArg (fun t => t.hom k) (Iso.inv_hom_id (S.mapCyclesIso F))
    exact this
  rw [e] at h1
  refine h1.trans ?_
  have : (F.map (Z.liftCycles Θ 1 next21 hΘ ≫ Z.homologyπ 2)).hom n = (F.map S.homologyπ).hom k := by
    rw [F.map_comp]
    rfl
  exact this.symm

open TernaryPeriodPolynomials.Argument.HochschildSerre in
theorem clsV_iCycles (Z : ChainComplex (Rep.{0} ℚ Q) ℕ) {N : Rep.{0} ℚ Q} (Θ : N ⟶ Z.X 2)
    (hΘ : Θ ≫ Z.d 2 1 = 0) (n : N.V) :
    ((Z.sc 2).map (forget₂ (Rep.{0} ℚ Q) (ModuleCat ℚ))).iCycles.hom
      (((Z.sc 2).mapCyclesIso (forget₂ (Rep.{0} ℚ Q) (ModuleCat ℚ))).inv.hom
        (((forget₂ (Rep.{0} ℚ Q) (ModuleCat ℚ)).map (Z.liftCycles Θ 1 next21 hΘ)).hom n)) = Θ.hom n := by
  let F := forget₂ (Rep.{0} ℚ Q) (ModuleCat ℚ)
  let S := Z.sc 2
  let k : (F.obj S.cycles) := (F.map (Z.liftCycles Θ 1 next21 hΘ)).hom n
  let z : (S.map F).cycles := (S.mapCyclesIso F).inv.hom k
  have h5 := ShortComplex.mapCyclesIso_hom_iCycles (S := S) F
  have h6 := congrArg (fun t => t.hom z) h5
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h6
  have e : (S.mapCyclesIso F).hom.hom z = k := by
    have := congrArg (fun t => t.hom k) (Iso.inv_hom_id (S.mapCyclesIso F))
    exact this
  rw [e] at h6
  refine h6.symm.trans ?_
  have h7 : F.map (Z.liftCycles Θ 1 next21 hΘ) ≫ F.map (S.iCycles) = F.map Θ :=
    ((F.map_comp _ _).symm.trans (congrArg F.map (HomologicalComplex.liftCycles_i Z Θ 1 next21 hΘ)))
  exact congrArg (fun t => t.hom n) h7

theorem hom_cls {S S' : ShortComplex (ModuleCat.{0} ℚ)} (ψ : S ⟶ S') (z : S.cycles) (z' : S'.cycles)
    (h : S'.iCycles.hom z' = ψ.τ₂.hom (S.iCycles.hom z)) :
    (ShortComplex.homologyMap ψ).hom (S.homologyπ.hom z) = S'.homologyπ.hom z' := by
  have nat := congrArg (fun t => t.hom z) (ShortComplex.homologyπ_naturality ψ)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at nat
  refine nat.trans ?_
  congr 1
  have inj : Function.Injective S'.iCycles.hom := (ModuleCat.mono_iff_injective _).1 inferInstance
  apply inj
  have h2 := congrArg (fun t => t.hom z) (ShortComplex.cyclesMap_i ψ)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  exact h2.trans h.symm

end Cls


section Beta

variable {P : Type} [Group P] (U : Subgroup P) [U.Normal]
  (R : ProjectiveResolution (Rep.trivial ℚ P ℚ)) {A : Rep.{0} ℚ P} (hA : ∀ u : U, A.ρ u = 1) (a : A.V)
  [Representation.IsTrivial (A.ρ.comp U.subtype)]

/-- The element `1` of the trivial representation `ℚ`. -/
def oneT : (Rep.trivial ℚ P ℚ).V := (1 : ℚ)

theorem etaR_f_nu (j : ℕ) (w : ((Phi U).obj (R.complex.X j)).V) :
    ((etaR U R hA a).f j).hom ((nuRep U (Rep.trivial ℚ P ℚ) (R.complex.X j)).hom ((oneT (P := P)) ⊗ₜ[ℚ] w)) =
      (nuRep U A (R.complex.X j)).hom (a ⊗ₜ[ℚ] w) := by
  induction w using Coinvariants.induction_on with
  | h x =>
    change ((etaR U R hA a).f j).hom (Coinvariants.mk _ ((oneT (P := P)) ⊗ₜ[ℚ] x)) = Coinvariants.mk _ (a ⊗ₜ[ℚ] x)
    rw [show ((etaR U R hA a).f j).hom (Coinvariants.mk _ ((oneT (P := P)) ⊗ₜ[ℚ] x)) =
      Coinvariants.mk _ (((1 : ℚ) • a) ⊗ₜ[ℚ] x) from rfl, one_smul]

variable {L P1' P0' : Rep.{0} ℚ (P ⧸ U)} (d' : P1' ⟶ P0') (ε' : P0' ⟶ Rep.trivial ℚ (P ⧸ U) ℚ)
  (hdε : d' ≫ ε' = 0) (hS : (ShortComplex.mk d' ε' hdε).ShortExact)
  (t3 : L ⊗ P1' ⟶ (Phi U).obj (R.complex.X 3)) (t2 : L ⊗ P0' ⟶ (Phi U).obj (R.complex.X 2))
  (hi : t3 ≫ (Phi U).map (R.complex.d 3 2) = (L ◁ d') ≫ t2)
  (hii : t2 ≫ (Phi U).map (R.complex.d 2 1) = 0)

theorem psiInst_nat (ℓ : L.V) :
    (PsiInst U A R d' ε' hdε hS t3 t2 hi hii).hom (a ⊗ₜ[ℚ] ℓ) =
      nuH U R hA a ((PsiInst U (Rep.trivial ℚ P ℚ) R d' ε' hdε hS t3 t2 hi hii).hom
        ((oneT (P := P)) ⊗ₜ[ℚ] ℓ)) := by
  rw [PsiInst_tmul, PsiInst_tmul]
  have cA := clsV_spec (ZR U R A) (ThetaIn U A R t2) (ThetaIn_cyc U A R t2 hii)
    ((a ⊗ₜ[ℚ] ℓ) ⊗ₜ[ℚ] sZero P1' P0' d' ε' hdε hS)
  have cQ := clsV_spec (ZR U R (Rep.trivial ℚ P ℚ)) (ThetaIn U (Rep.trivial ℚ P ℚ) R t2)
    (ThetaIn_cyc U (Rep.trivial ℚ P ℚ) R t2 hii) (((oneT (P := P)) ⊗ₜ[ℚ] ℓ) ⊗ₜ[ℚ] sZero P1' P0' d' ε' hdε hS)
  rw [← cA, ← cQ, nuH_hom]
  congr 1
  refine (hom_cls (S := ((ZR U R (Rep.trivial ℚ P ℚ)).sc 2).map (forget₂ (Rep.{0} ℚ (P ⧸ U)) (ModuleCat ℚ)))
    (S' := ((ZR U R A).sc 2).map (forget₂ (Rep.{0} ℚ (P ⧸ U)) (ModuleCat ℚ)))
    ((HomologicalComplex.shortComplexFunctor _ (ComplexShape.down ℕ) 2).map (etaR U R hA a)) _ _ ?_).symm
  change _ = ((etaR U R hA a).f 2).hom (_)
  rw [clsV_iCycles, clsV_iCycles, Theta2_tmul, Theta2_tmul, etaR_f_nu]

end Beta

section Universal

variable {P : Type} [Group P] (U : Subgroup P) [U.Normal] (eU : U2 ≃* U)
  (R : ProjectiveResolution (Rep.trivial ℚ P ℚ))
  {L P1' P0' : Rep.{0} ℚ (P ⧸ U)} (d' : P1' ⟶ P0') (ε' : P0' ⟶ Rep.trivial ℚ (P ⧸ U) ℚ)
  (hdε : d' ≫ ε' = 0) (hS : (ShortComplex.mk d' ε' hdε).ShortExact)
  (t3 : L ⊗ P1' ⟶ (Phi U).obj (R.complex.X 3)) (t2 : L ⊗ P0' ⟶ (Phi U).obj (R.complex.X 2))
  (hi : t3 ≫ (Phi U).map (R.complex.d 3 2) = (L ◁ d') ≫ t2)
  (hii : t2 ≫ (Phi U).map (R.complex.d 2 1) = 0) (ℓ₀ : L.V)

/-- **Universality of the Schur scalar**: there is one scalar `c₀`, independent of the coefficient module `A`, with
`Ψ'_A(a ⊗ ℓ₀) = c₀ · Γ_A(a)` where `Γ_A = H₂(fZ) ∘ gammaEquiv`. -/
theorem psiInst_universal :
    ∃ c₀ : ℚ, ∀ (A : Rep.{0} ℚ P) [Representation.IsTrivial (A.ρ.comp U.subtype)] [Module.Finite ℚ A.V]
      (hA : ∀ u : U, A.ρ u = 1) (a : A.V),
      (PsiInst U A R d' ε' hdε hS t3 t2 hi hii).hom (a ⊗ₜ[ℚ] ℓ₀) =
        c₀ • (HomologicalComplex.homologyMap (fZ U R A) 2).hom (gammaEquiv eU hA a) := by
  have hA₀ : ∀ u : U, (Rep.trivial ℚ P ℚ).ρ u = 1 := fun _ => rfl
  have : Module.Finite ℚ (Rep.trivial ℚ P ℚ).V := inferInstanceAs (Module.Finite ℚ ℚ)
  have hbij : Function.Bijective (fun c : (Rep.trivial ℚ P ℚ).V =>
      (HomologicalComplex.homologyMap (fZ U R (Rep.trivial ℚ P ℚ)) 2).hom (gammaEquiv eU hA₀ c)) :=
    ((ConcreteCategory.bijective_of_isIso
      (HomologicalComplex.homologyMap (fZ U R (Rep.trivial ℚ P ℚ)) 2)).comp (gammaEquiv eU hA₀).bijective)
  obtain ⟨c₀, hc₀⟩ := hbij.2 ((PsiInst U (Rep.trivial ℚ P ℚ) R d' ε' hdε hS t3 t2 hi hii).hom
    ((oneT (P := P)) ⊗ₜ[ℚ] ℓ₀))
  refine ⟨(c₀ : ℚ), fun A _ _ hA a => ?_⟩
  rw [psiInst_nat U R hA a d' ε' hdε hS t3 t2 hi hii ℓ₀, ← hc₀]
  have h1 : gammaEquiv eU hA₀ c₀ = (c₀ : ℚ) • gammaEquiv eU hA₀ (oneT (P := P)) := by
    rw [← map_smul]
    congr 1
    change c₀ = c₀ * 1
    rw [mul_one]
  change nuH U R hA a ((HomologicalComplex.homologyMap (fZ U R (Rep.trivial ℚ P ℚ)) 2).hom
      (gammaEquiv eU hA₀ c₀)) = _
  rw [h1, map_smul, map_smul, gamma_nat U eU R hA a hA₀]
  rfl

end Universal

end TernaryPeriodPolynomials.Argument.AppendixBResidue
