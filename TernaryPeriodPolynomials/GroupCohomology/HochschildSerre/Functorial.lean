module

public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.Setup
public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.QNat
public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.HSIso

@[expose] public section


/-!
# Functoriality of the Hochschild-Serre set-up for endomorphisms inducing the identity on `P/U`

Formalized by Claude Sonnet 5.5.

For `U ⊲ P`, `A : Rep ℚ P`, an endomorphism `φ` of `P` with `φ(U) ⊆ U` and `φ(g) g⁻¹ ∈ U` (so that `φ` induces the identity on `P/U`)
and `a : A ⟶ Res_φ A`:

* `zMap`: the chain endomorphism of the complex `ZP U A` of `P/U`-modules, `[y] ↦ [(a ⊗ bar φ) y]`;
* `eZ_nat`: `H_n(φ, a) ≫ (groupHomologyZIso) = (groupHomologyZIso) ≫ H_n(zMap)` (naturality of `H_n(P, A) ≅ H_n((Z ⊗ 1)_{P/U})`);
* `H2_zMap`: in the coordinates `A ≅ H₂(Z)` (`gammaEquiv`), `H₂(zMap)` is `ω(μ e₁, μ e₂) · a`, where `μ` is `φ|_U` transported to
  `U ≅ ℤ²` (the determinant of `φ|_U` on the radical).
-/

open CategoryTheory MonoidalCategory Representation Limits

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HochschildSerre

open TernaryPeriodPolynomials.Argument.GroupHomology
open TernaryPeriodPolynomials.Argument.GroupHomologyDescent (T2 U2)

variable {P : Type} [Group P] (U : Subgroup P) [U.Normal] (A : Rep.{0} ℚ P)
  (φ : P →* P) (a : A ⟶ Rep.res φ A)

/-- The `φ`-semilinear map `A ⊗ bar_j(P) → A ⊗ bar_j(P)` induced by `(φ, a)`. -/
def xiLin (j : ℕ) : ((YA A).X j) →ₗ[ℚ] ((YA A).X j) :=
  TensorProduct.map a.hom.toLinearMap (barTerm (k := ℚ) φ j).hom.toLinearMap


theorem xiLin_rho (j : ℕ) (g : P) (y : (YA A).X j) :
    xiLin A φ a j (((YA A).X j).ρ g y) = ((YA A).X j).ρ (φ g) (xiLin A φ a j y) := by
  have key : ∀ y : TensorProduct ℚ A ((Rep.free ℚ P (Fin j → P))),
      TensorProduct.map a.hom.toLinearMap (barTerm (k := ℚ) φ j).hom.toLinearMap
        ((A.ρ.tprod (Rep.free ℚ P (Fin j → P)).ρ g) y) =
      (A.ρ.tprod (Rep.free ℚ P (Fin j → P)).ρ (φ g))
        (TensorProduct.map a.hom.toLinearMap (barTerm (k := ℚ) φ j).hom.toLinearMap y) := by
    intro y
    induction y using TensorProduct.inductionOn with
    | tmul u v =>
      simp only [Representation.tprod_apply, TensorProduct.map_tmul]
      have h1 : a.hom (A.ρ g u) = A.ρ (φ g) (a.hom u) := Rep.hom_comm_apply a g u
      have h2 : (barTerm (k := ℚ) φ j).hom ((Rep.free ℚ P (Fin j → P)).ρ g v) =
          (Rep.free ℚ P (Fin j → P)).ρ (φ g) ((barTerm (k := ℚ) φ j).hom v) :=
        Rep.hom_comm_apply (barTerm (k := ℚ) φ j) g v
      exact congrArg₂ (· ⊗ₜ[ℚ] ·) h1 h2
    | add u w hu hw =>
      simp only [map_add, hu, hw]
  exact key y


section ZMap

variable {U} (hφU : ∀ u : U, φ (u : P) ∈ U) (hφq : ∀ g : P, φ g * g⁻¹ ∈ U)

/-- The map on `U`-coinvariants induced by `xiLin`. -/
def zLin (j : ℕ) : ((Phi U).obj ((YA A).X j)).V →ₗ[ℚ] ((Phi U).obj ((YA A).X j)).V :=
  Coinvariants.lift (((YA A).X j).ρ.comp U.subtype)
    ((Coinvariants.mk (((YA A).X j).ρ.comp U.subtype)).comp (xiLin A φ a j)) (fun u => LinearMap.ext fun y => by
      change Coinvariants.mk (((YA A).X j).ρ.comp U.subtype) (xiLin A φ a j (((YA A).X j).ρ u.1 y)) =
        Coinvariants.mk (((YA A).X j).ρ.comp U.subtype) (xiLin A φ a j y)
      rw [xiLin_rho]
      exact Coinvariants.mk_self_apply (((YA A).X j).ρ.comp U.subtype) ⟨φ u.1, hφU u⟩ _)

theorem zLin_mk (j : ℕ) (y : (YA A).X j) :
    zLin A φ a hφU j (Coinvariants.mk (((YA A).X j).ρ.comp U.subtype) y) =
      Coinvariants.mk (((YA A).X j).ρ.comp U.subtype) (xiLin A φ a j y) := rfl

/-- The `Q`-linear degreewise map of the `U`-coinvariant complex. -/
def zRep (j : ℕ) : (ZP U A).X j ⟶ (ZP U A).X j :=
  Rep.ofHom ⟨zLin A φ a hφU j, fun q => by
    induction q using QuotientGroup.induction_on with
    | H g =>
      refine LinearMap.ext fun w => ?_
      induction w using Coinvariants.induction_on with
      | h y =>
        change zLin A φ a hφU j (Coinvariants.mk (((YA A).X j).ρ.comp U.subtype) (((YA A).X j).ρ g y)) =
          Coinvariants.mk (((YA A).X j).ρ.comp U.subtype) (((YA A).X j).ρ g (xiLin A φ a j y))
        rw [zLin_mk, xiLin_rho]
        have h : ((YA A).X j).ρ (φ g) (xiLin A φ a j y) =
            ((YA A).X j).ρ (φ g * g⁻¹) (((YA A).X j).ρ g (xiLin A φ a j y)) := by
          rw [← Module.End.mul_apply (((YA A).X j).ρ (φ g * g⁻¹)) (((YA A).X j).ρ g), ← map_mul,
            inv_mul_cancel_right]
        rw [h]
        exact Coinvariants.mk_self_apply (((YA A).X j).ρ.comp U.subtype) ⟨φ g * g⁻¹, hφq g⟩ _⟩

theorem xiLin_d (j : ℕ) (y : (YA A).X (j + 1)) :
    xiLin A φ a j ((YA A).d (j + 1) j y) = (YA A).d (j + 1) j (xiLin A φ a (j + 1) y) := by
  have key : ∀ y : TensorProduct ℚ A ((Rep.free ℚ P (Fin (j + 1) → P))),
      TensorProduct.map a.hom.toLinearMap (barTerm (k := ℚ) φ j).hom.toLinearMap
        (TensorProduct.map LinearMap.id (Rep.barComplex.d ℚ P j).hom.toLinearMap y) =
      TensorProduct.map LinearMap.id (Rep.barComplex.d ℚ P j).hom.toLinearMap
        (TensorProduct.map a.hom.toLinearMap (barTerm (k := ℚ) φ (j + 1)).hom.toLinearMap y) := by
    intro y
    induction y using TensorProduct.inductionOn with
    | tmul u v =>
      simp only [TensorProduct.map_tmul, LinearMap.id_apply]
      have h := congrArg (fun m => m.hom v) (barTerm_comm (k := ℚ) φ j)
      exact congrArg (fun w => a.hom u ⊗ₜ[ℚ] w) h.symm
    | add u w hu hw =>
      simp only [map_add, hu, hw]
  have hdb : (Rep.barComplex ℚ P).d (j + 1) j = Rep.barComplex.d ℚ P j := by
    simp only [Rep.barComplex, ChainComplex.of_d]
  have hY : (YA A).d (j + 1) j = A ◁ (Rep.barComplex ℚ P).d (j + 1) j := rfl
  rw [hY, hdb]
  exact key y

/-- The chain endomorphism of `ZP U A` induced by `(φ, a)`. -/
def zMap : ZP U A ⟶ ZP U A where
  f j := zRep A φ a hφU hφq j
  comm' := by
    rintro i j (rfl : j + 1 = i)
    refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun w => ?_))
    induction w using Coinvariants.induction_on with
    | h y =>
      change Coinvariants.mk (((YA A).X j).ρ.comp U.subtype) ((YA A).d (j + 1) j (xiLin A φ a (j + 1) y)) =
        zLin A φ a hφU j (Coinvariants.mk (((YA A).X j).ρ.comp U.subtype) ((YA A).d (j + 1) j y))
      rw [zLin_mk, xiLin_d]

end ZMap


section KMap

variable {U} (hφU : ∀ u : U, φ (u : P) ∈ U) (hφq : ∀ g : P, φ g * g⁻¹ ∈ U)

theorem FXunitIso_hom_mk {Q : Type} [Group Q] (N : Rep.{0} ℚ Q) (n : N) :
    ((FXunitIso.app N).hom).hom (Coinvariants.mk (N.ρ.tprod (Representation.trivial ℚ Q ℚ)) (n ⊗ₜ[ℚ] (1 : ℚ))) =
      Coinvariants.mk N.ρ n := by
  change Coinvariants.mk N.ρ ((ρ_ N).hom.hom (n ⊗ₜ[ℚ] (1 : ℚ))) = _
  rw [Rep.hom_hom_rightUnitor]
  simp

/-- `ZIso` on generators. -/
theorem ZIso_hom_mk (j : ℕ) (y : (YA A).X j) :
    ((ZIso U A).hom.f j).hom (Coinvariants.mk _ (Coinvariants.mk (((YA A).X j).ρ.comp U.subtype) y ⊗ₜ[ℚ]
      (1 : ℚ))) = Coinvariants.mk ((YA A).X j).ρ y := by
  have h := FXunitIso_hom_mk ((Phi U).obj ((YA A).X j))
    (Coinvariants.mk (((YA A).X j).ρ.comp U.subtype) y)
  exact (congrArg (fun w => ((coinvIterIso U).hom.app ((YA A).X j)).hom w) h).trans rfl

/-- The induced chain endomorphism of the complex of `P`-coinvariants `(A ⊗ bar P)_P`. -/
def KMap : CxK (YA A) ⟶ CxK (YA A) where
  f j := ModuleCat.ofHom (Coinvariants.lift ((YA A).X j).ρ
    ((Coinvariants.mk ((YA A).X j).ρ).comp (xiLin A φ a j)) (fun g => LinearMap.ext fun y => by
      change Coinvariants.mk ((YA A).X j).ρ (xiLin A φ a j (((YA A).X j).ρ g y)) =
        Coinvariants.mk ((YA A).X j).ρ (xiLin A φ a j y)
      rw [xiLin_rho]
      exact Coinvariants.mk_self_apply ((YA A).X j).ρ (φ g) _))
  comm' := by
    rintro i j (rfl : j + 1 = i)
    refine ModuleCat.hom_ext (Coinvariants.hom_ext (LinearMap.ext fun y => ?_))
    change Coinvariants.mk ((YA A).X j).ρ ((YA A).d (j + 1) j (xiLin A φ a (j + 1) y)) =
      Coinvariants.mk ((YA A).X j).ρ (xiLin A φ a j ((YA A).d (j + 1) j y))
    rw [xiLin_d]

theorem KMap_f_mk (j : ℕ) (y : (YA A).X j) :
    ((KMap A φ a).f j).hom (Coinvariants.mk ((YA A).X j).ρ y) =
      Coinvariants.mk ((YA A).X j).ρ (xiLin A φ a j y) := rfl

theorem ZIso_inv_mk (j : ℕ) (y : (YA A).X j) :
    ((ZIso U A).inv.f j).hom (Coinvariants.mk ((YA A).X j).ρ y) =
      Coinvariants.mk _ (Coinvariants.mk (((YA A).X j).ρ.comp U.subtype) y ⊗ₜ[ℚ] (1 : ℚ)) := by
  have h := congrArg (fun m => (m.f j).hom (Coinvariants.mk _ (Coinvariants.mk
    (((YA A).X j).ρ.comp U.subtype) y ⊗ₜ[ℚ] (1 : ℚ)))) (ZIso U A).hom_inv_id
  have h2 := ZIso_hom_mk (U := U) A j y
  refine Eq.trans ?_ h
  exact congrArg (fun w => ((ZIso U A).inv.f j).hom w) h2.symm

theorem ZIso_KMap :
    KMap A φ a ≫ (ZIso U A).inv =
      (ZIso U A).inv ≫ muX (zMap A φ a hφU hφq) (𝟙_ (Rep.{0} ℚ (P ⧸ U))) := by
  refine HomologicalComplex.hom_ext _ _ fun j => ?_
  refine ModuleCat.hom_ext (Coinvariants.hom_ext (LinearMap.ext fun y => ?_))
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp]
  change ((ZIso U A).inv.f j).hom (((KMap A φ a).f j).hom (Coinvariants.mk ((YA A).X j).ρ y)) =
    ((muX (zMap A φ a hφU hφq) (𝟙_ (Rep.{0} ℚ (P ⧸ U)))).f j).hom (((ZIso U A).inv.f j).hom
      (Coinvariants.mk ((YA A).X j).ρ y))
  rw [KMap_f_mk, ZIso_inv_mk, ZIso_inv_mk]
  rfl

open scoped Classical in
theorem chains_KMap :
    groupHomology.chainsMap φ a ≫ (groupHomology.inhomogeneousChainsIso A).hom =
      (groupHomology.inhomogeneousChainsIso A).hom ≫ KMap A φ a := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  refine groupHomology.inhomogeneousChains.ext fun x => ?_
  refine ModuleCat.hom_ext (LinearMap.ext fun b => ?_)
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.hom_ofHom, Finsupp.lsingle_apply]
  have eL := groupHomology.chainsMap_f_single φ a n x b
  have eL2 := inhomIso_hom_f_single A n (φ ∘ x) (a.hom b)
  have eR := inhomIso_hom_f_single A n x b
  rw [eL, eL2]
  change _ = ((KMap A φ a).f n).hom (((groupHomology.inhomogeneousChainsIso A).hom.f n).hom
    (Finsupp.single x b))
  rw [eR]
  refine Eq.trans ?_ (KMap_f_mk A φ a n _).symm
  change _ = Coinvariants.mk ((YA A).X n).ρ
    (TensorProduct.map a.hom.toLinearMap (barTerm (k := ℚ) φ n).hom.toLinearMap
      (b ⊗ₜ[ℚ] Finsupp.single x (MonoidAlgebra.single (1 : P) (1 : ℚ))))
  rw [TensorProduct.map_tmul]
  change _ = Coinvariants.mk ((YA A).X n).ρ
    (a.hom b ⊗ₜ[ℚ] (barTerm (k := ℚ) φ n).hom (Finsupp.single x (MonoidAlgebra.single (1 : P) (1 : ℚ))))
  rw [barTerm_single, map_one]
  rfl

open scoped Classical in
theorem eK_KMap (n : ℕ) :
    groupHomology.map φ a n ≫ (eK A n).hom =
      (eK A n).hom ≫ HomologicalComplex.homologyMap (KMap A φ a) n := by
  have e1 : groupHomology.map φ a n ≫ (eK A n).hom =
      HomologicalComplex.homologyMap (groupHomology.chainsMap φ a ≫
        (groupHomology.inhomogeneousChainsIso A).hom) n := by
    rw [groupHomologyIso_bar_hom]
    exact (HomologicalComplex.homologyMap_comp _ _ n).symm
  have e2 : (eK A n).hom ≫ HomologicalComplex.homologyMap (KMap A φ a) n =
      HomologicalComplex.homologyMap ((groupHomology.inhomogeneousChainsIso A).hom ≫ KMap A φ a) n := by
    rw [groupHomologyIso_bar_hom]
    exact (HomologicalComplex.homologyMap_comp _ _ n).symm
  rw [e1, e2]
  exact congrArg (fun m => HomologicalComplex.homologyMap m n) (chains_KMap A φ a)

/-- **Naturality of `H_n(P, A) ≅ H_n((Z ⊗ 1)_{P/U})` for a morphism `(φ, a)` inducing the identity on `P/U`.** -/
theorem eZ_nat (n : ℕ) :
    groupHomology.map φ a n ≫ (groupHomologyZIso U A n).hom =
      (groupHomologyZIso U A n).hom ≫
        HomologicalComplex.homologyMap (muX (zMap A φ a hφU hφq) (𝟙_ (Rep.{0} ℚ (P ⧸ U)))) n := by
  have h1 : (groupHomologyZIso U A n).hom = (eK A n).hom ≫ HomologicalComplex.homologyMap (ZIso U A).inv n :=
    rfl
  have h2 : HomologicalComplex.homologyMap (KMap A φ a) n ≫ HomologicalComplex.homologyMap (ZIso U A).inv n =
      HomologicalComplex.homologyMap (ZIso U A).inv n ≫
        HomologicalComplex.homologyMap (muX (zMap A φ a hφU hφq) (𝟙_ (Rep.{0} ℚ (P ⧸ U)))) n :=
    (HomologicalComplex.homologyMap_comp _ _ n).symm.trans
      ((congrArg (fun m => HomologicalComplex.homologyMap m n) (ZIso_KMap A φ a hφU hφq)).trans
        (HomologicalComplex.homologyMap_comp _ _ n))
  rw [h1]
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun w => w ≫ HomologicalComplex.homologyMap (ZIso U A).inv n) (eK_KMap A φ a n)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun w => (eK A n).hom ≫ w) h2).trans ?_
  exact (Category.assoc _ _ _).symm

end KMap


section Gamma

variable {U} (hφU : ∀ u : U, φ (u : P) ∈ U) (hφq : ∀ g : P, φ g * g⁻¹ ∈ U)

/-- `φ` restricted to the normal subgroup `U`. -/
def phiU : U →* U :=
  MonoidHom.codRestrict (φ.comp U.subtype) U hφU

/-- The coefficient morphism `Res_U A ⟶ Res_{φ|U} Res_U A` induced by `a`. -/
def aU : Rep.res U.subtype A ⟶ Rep.res (phiU φ hφU) (Rep.res U.subtype A) :=
  Rep.ofHom ⟨a.hom.toLinearMap, fun u => by
    refine LinearMap.ext fun b => ?_
    exact Rep.hom_comm_apply a u.1 b⟩

theorem chains_phiU :
    groupHomology.chainsMap (phiU φ hφU) (aU A φ a hφU) ≫ betaA U A =
      betaA U A ≫ ((forget₂ (Rep.{0} ℚ (P ⧸ U)) (ModuleCat ℚ)).mapHomologicalComplex _).map
        (zMap A φ a hφU hφq) := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  refine groupHomology.inhomogeneousChains.ext fun x => ?_
  refine ModuleCat.hom_ext (LinearMap.ext fun b => ?_)
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.hom_ofHom, Finsupp.lsingle_apply]
  have eL : ((groupHomology.chainsMap (phiU φ hφU) (aU A φ a hφU)).f n).hom (Finsupp.single x b) =
      Finsupp.single (phiU φ hφU ∘ x) (a.hom b) :=
    groupHomology.chainsMap_f_single (phiU φ hφU) (aU A φ a hφU) n x b
  rw [eL, betaA_single U A n (phiU φ hφU ∘ x) (a.hom b)]
  change _ = zLin A φ a hφU n (((betaA U A).f n).hom (Finsupp.single x b))
  rw [betaA_single U A n x b]
  refine Eq.trans ?_ (zLin_mk A φ a hφU n _).symm
  change _ = Coinvariants.mk (((YA A).X n).ρ.comp U.subtype)
    (TensorProduct.map a.hom.toLinearMap (barTerm (k := ℚ) φ n).hom.toLinearMap
      (b ⊗ₜ[ℚ] Finsupp.single (U.subtype ∘ x) (MonoidAlgebra.single (1 : P) (1 : ℚ))))
  rw [TensorProduct.map_tmul]
  change _ = Coinvariants.mk (((YA A).X n).ρ.comp U.subtype)
    (a.hom b ⊗ₜ[ℚ] (barTerm (k := ℚ) φ n).hom (Finsupp.single (U.subtype ∘ x) (MonoidAlgebra.single (1 : P) (1 : ℚ))))
  rw [barTerm_single, map_one]
  rfl


variable (eU : U2 ≃* U)

/-- `φ|_U` transported to `U2`. -/
def muPhi : U2 →* U2 := (eU.symm.toMonoidHom).comp ((phiU φ hφU).comp eU.toMonoidHom)

omit [U.Normal] in
theorem eU_muPhi (v : U2) : eU (muPhi φ hφU eU v) = phiU φ hφU (eU v) := by
  simp [muPhi]

omit [U.Normal] in
theorem phiU_Psi (hA : ∀ u : U, A.ρ u = 1) (x : groupHomology (TV A.V) 2) :
    groupHomology.map (phiU φ hφU) (aU A φ a hφU) 2 ((PsiIso eU hA).hom.hom x) =
      (PsiIso eU hA).hom.hom
        (groupHomology.map (muPhi φ hφU eU) (trivHomRes (muPhi φ hφU eU) a.hom.toLinearMap) 2 x) := by
  let φ0 : TV A.V ⟶ Rep.res eU.toMonoidHom (Rep.res U.subtype A) :=
    Rep.ofHom ⟨(LinearEquiv.refl ℚ A.V).toLinearMap, fun g => by
      ext a
      change a = (A.ρ (eU g).1) a
      have : A.ρ (eU g).1 = 1 := hA (eU g)
      rw [this]; rfl⟩
  have hL := groupHomology.map_comp eU.toMonoidHom (phiU φ hφU) φ0 (aU A φ a hφU) 2
  have hR := groupHomology.map_comp (muPhi φ hφU eU) eU.toMonoidHom
    (trivHomRes (muPhi φ hφU eU) a.hom.toLinearMap) φ0 2
  have hfg : (phiU φ hφU).comp eU.toMonoidHom = eU.toMonoidHom.comp (muPhi φ hφU eU) := by
    ext v
    exact congrArg Subtype.val (eU_muPhi φ hφU eU v).symm
  have hc : groupHomology.map eU.toMonoidHom φ0 2 ≫ groupHomology.map (phiU φ hφU) (aU A φ a hφU) 2 =
      groupHomology.map (muPhi φ hφU eU) (trivHomRes (muPhi φ hφU eU) a.hom.toLinearMap) 2 ≫
        groupHomology.map eU.toMonoidHom φ0 2 :=
    hL.symm.trans ((groupHomology.map_congr hfg (by ext a; rfl) 2).trans hR)
  have := congrArg (fun φ => φ.hom x) hc
  exact this


variable [Module.Finite ℚ A.V]

omit [Module.Finite ℚ A.V] in
theorem eN_phiU (n : ℕ) :
    groupHomology.map (phiU φ hφU) (aU A φ a hφU) n ≫ (eN U A n).hom =
      (eN U A n).hom ≫ HomologicalComplex.homologyMap
        (((forget₂ (Rep.{0} ℚ (P ⧸ U)) (ModuleCat ℚ)).mapHomologicalComplex _).map
          (zMap A φ a hφU hφq)) n := by
  have h1 := congrArg (fun m => HomologicalComplex.homologyMap m n) (chains_phiU A φ a hφU hφq)
  have hA := HomologicalComplex.homologyMap_comp (groupHomology.chainsMap (phiU φ hφU) (aU A φ a hφU))
    (betaA U A) n
  have hB := HomologicalComplex.homologyMap_comp (betaA U A)
    (((forget₂ (Rep.{0} ℚ (P ⧸ U)) (ModuleCat ℚ)).mapHomologicalComplex _).map (zMap A φ a hφU hφq)) n
  rw [eN_hom]
  exact hA.symm.trans (h1.trans hB)

/-- **The action of `(φ, a)` on `H₂(Z)` in the coordinates `A ≅ H₂(Z)`**: multiplication by the determinant
`ω(μ e₁, μ e₂)` of `φ|_U` on `U ≅ ℤ²` composed with `a`. -/
theorem H2_zMap (hA : ∀ u : U, A.ρ u = 1) (x : A.V) :
    (HomologicalComplex.homologyMap (zMap A φ a hφU hφq) 2).hom (gammaEquiv eU hA x) =
      (omegaZ (muPhi φ hφU eU e1) (muPhi φ hφU eU e2) : ℚ) • gammaEquiv eU hA (a.hom x) := by
  set Θ := ((ZP U A).sc 2).mapHomologyIso (forget₂ (Rep.{0} ℚ (P ⧸ U)) (ModuleCat ℚ)) with hΘ
  have hN := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ (ComplexShape.down ℕ) 2).map (zMap A φ a hφU hφq))
    (forget₂ (Rep.{0} ℚ (P ⧸ U)) (ModuleCat ℚ))
  have hg : ∀ y : A.V, gammaEquiv eU hA y = Θ.hom.hom ((eN U A 2).hom.hom ((PsiIso eU hA).hom.hom (kappa0 A.V y))) :=
    fun y => rfl
  rw [hg, hg]
  have h1 := congrArg (fun m => m.hom ((eN U A 2).hom.hom ((PsiIso eU hA).hom.hom (kappa0 A.V x)))) hN
  simp only [ModuleCat.hom_comp] at h1
  have h2 := congrArg (fun m => m.hom ((PsiIso eU hA).hom.hom (kappa0 A.V x))) (eN_phiU A φ a hφU hφq 2)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  have h3 := phiU_Psi A φ a hφU eU hA (kappa0 A.V x)
  have h4 := map_kappa0_gen (muPhi φ hφU eU) a.hom.toLinearMap x
  rw [h4, map_smul] at h3
  set ω : ℚ := (omegaZ (muPhi φ hφU eU e1) (muPhi φ hφU eU e2) : ℚ) with hω
  have hB : (HomologicalComplex.homologyMap
      (((forget₂ (Rep.{0} ℚ (P ⧸ U)) (ModuleCat ℚ)).mapHomologicalComplex _).map
        (zMap A φ a hφU hφq)) 2).hom
      ((eN U A 2).hom.hom ((PsiIso eU hA).hom.hom (kappa0 A.V x))) =
      ω • (eN U A 2).hom.hom ((PsiIso eU hA).hom.hom (kappa0 A.V (a.hom x))) := by
    refine h2.symm.trans ?_
    rw [h3, map_smul]
    rfl
  refine h1.symm.trans ?_
  change Θ.hom.hom ((HomologicalComplex.homologyMap
      (((forget₂ (Rep.{0} ℚ (P ⧸ U)) (ModuleCat ℚ)).mapHomologicalComplex _).map
        (zMap A φ a hφU hφq)) 2).hom
      ((eN U A 2).hom.hom ((PsiIso eU hA).hom.hom (kappa0 A.V x)))) = _
  rw [hB]
  exact map_smul Θ.hom.hom ω _

end Gamma

end TernaryPeriodPolynomials.Argument.HochschildSerre
