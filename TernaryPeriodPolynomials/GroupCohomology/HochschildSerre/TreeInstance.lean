module

public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.TreeTheorem
public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.ResolutionZ
public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.HSIso

@[expose] public section


/-!
# Tree maps into `Φ(R)` as the data of the tree theorem

Formalized by Claude Sonnet 5.5.

For `U ⊲ P`, `A : Rep ℚ P` with `U` acting trivially, `Ā` the induced `P/U`-representation and `Φ = Phi U`:

* `nuIso X : Ā ⊗ Φ(X) ≅ Φ(A ⊗ X)`, `[x] ↦ [a ⊗ x]` (inverse `[a ⊗ x] ↦ a ⊗ [x]`), natural in `X` (`nuRep_natural`);
* `ThetaIn`: from `t_j : L ⊗ P' ⟶ Φ(R_j)` the maps `Θ_j : (Ā ⊗ L) ⊗ P' ⟶ (ZR U R A).X j`, satisfying the two
  hypotheses of the tree theorem (`ThetaIn_comm`, `ThetaIn_cyc`);
* `boundary_of_homologyπ_eq_zero'`: a cycle of a complex of representations with zero homology class is a boundary;
* `kapLin`: the contraction `Φ(A ⊗ X) → Φ(X)` by a linear functional of `A`, natural in `X`;
* `PsiInst` is the map `Ψ'` of the tree theorem for this data; `PsiInst_injective` and `PsiInst_isIso` (the latter via
  a dimension count with `gammaEquiv` and `fZ_homology_iso`), under the nonvanishing hypothesis that
  `t2(ℓ₀ ⊗ s₀)` is not a boundary;
* `L_character`: for the trivial module, `P/U` acts on the line `L` through the determinant factor `deltaG`.
-/

open CategoryTheory MonoidalCategory Representation Limits
open scoped TensorProduct
open TernaryPeriodPolynomials.Argument.GroupHomologyDescent (T2 U2)

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HochschildSerre

variable {P : Type} [Group P] (U : Subgroup P) (A : Rep.{0} ℚ P)
  [Representation.IsTrivial (A.ρ.comp U.subtype)]

/-- `A` as a representation of `P/U`. -/
abbrev Abar [U.Normal] : Rep.{0} ℚ (P ⧸ U) := A.ofQuotient U

theorem A_triv (u : U) (a : A.V) : A.ρ (u : P) a = a :=
  Representation.isTrivial_apply (A.ρ.comp U.subtype) u a

/-- `a ↦ ([x] ↦ [a ⊗ x])`. -/
def nuFun (X : Rep.{0} ℚ P) (a : A.V) :
    Coinvariants (X.ρ.comp U.subtype) →ₗ[ℚ] Coinvariants ((A ⊗ X).ρ.comp U.subtype) :=
  Coinvariants.lift (X.ρ.comp U.subtype)
    ((Coinvariants.mk ((A ⊗ X).ρ.comp U.subtype)) ∘ₗ (TensorProduct.mk ℚ A.V X.V a))
    (fun u => by
      apply LinearMap.ext
      intro x
      have h := Coinvariants.mk_self_apply ((A ⊗ X).ρ.comp U.subtype) u (a ⊗ₜ[ℚ] x)
      simpa [Representation.tprod_apply, A_triv U A u a] using h)

theorem nuFun_mk (X : Rep.{0} ℚ P) (a : A.V) (x : X.V) :
    nuFun U A X a (Coinvariants.mk (X.ρ.comp U.subtype) x) =
      Coinvariants.mk ((A ⊗ X).ρ.comp U.subtype) (a ⊗ₜ[ℚ] x) := rfl

/-- `Ā ⊗ Φ(X) → Φ(A ⊗ X)` on underlying modules. -/
def nuLin (X : Rep.{0} ℚ P) :
    TensorProduct ℚ A.V (Coinvariants (X.ρ.comp U.subtype)) →ₗ[ℚ]
      Coinvariants ((A ⊗ X).ρ.comp U.subtype) :=
  TensorProduct.lift
    { toFun := nuFun U A X
      map_add' := fun a b => by
        apply LinearMap.ext
        intro ξ
        induction ξ using Coinvariants.induction_on with
        | h x =>
          change Coinvariants.mk ((A ⊗ X).ρ.comp U.subtype) ((a + b) ⊗ₜ[ℚ] x) =
            Coinvariants.mk ((A ⊗ X).ρ.comp U.subtype) (a ⊗ₜ[ℚ] x) +
              Coinvariants.mk ((A ⊗ X).ρ.comp U.subtype) (b ⊗ₜ[ℚ] x)
          rw [TensorProduct.add_tmul, map_add]
      map_smul' := fun r a => by
        apply LinearMap.ext
        intro ξ
        induction ξ using Coinvariants.induction_on with
        | h x =>
          change Coinvariants.mk ((A ⊗ X).ρ.comp U.subtype) ((r • a) ⊗ₜ[ℚ] x) =
            r • Coinvariants.mk ((A ⊗ X).ρ.comp U.subtype) (a ⊗ₜ[ℚ] x)
          rw [← TensorProduct.smul_tmul', map_smul] }

theorem nuLin_tmul_mk (X : Rep.{0} ℚ P) (a : A.V) (x : X.V) :
    nuLin U A X (a ⊗ₜ[ℚ] Coinvariants.mk (X.ρ.comp U.subtype) x) =
      Coinvariants.mk ((A ⊗ X).ρ.comp U.subtype) (a ⊗ₜ[ℚ] x) := rfl

/-- The inverse: `[a ⊗ x] ↦ a ⊗ [x]`. -/
def nuInv (X : Rep.{0} ℚ P) :
    Coinvariants ((A ⊗ X).ρ.comp U.subtype) →ₗ[ℚ]
      TensorProduct ℚ A.V (Coinvariants (X.ρ.comp U.subtype)) :=
  Coinvariants.lift _ (TensorProduct.map LinearMap.id (Coinvariants.mk (X.ρ.comp U.subtype)))
    (fun u => by
      refine TensorProduct.ext' fun a x => ?_
      change TensorProduct.map LinearMap.id (Coinvariants.mk (X.ρ.comp U.subtype))
        (A.ρ (u : P) a ⊗ₜ[ℚ] X.ρ (u : P) x) = _
      rw [A_triv U A u a, TensorProduct.map_tmul]
      have := Coinvariants.mk_self_apply (X.ρ.comp U.subtype) u x
      exact congrArg (fun z => a ⊗ₜ[ℚ] z) this)

theorem nuInv_mk (X : Rep.{0} ℚ P) (a : A.V) (x : X.V) :
    nuInv U A X (Coinvariants.mk ((A ⊗ X).ρ.comp U.subtype) (a ⊗ₜ[ℚ] x)) =
      a ⊗ₜ[ℚ] Coinvariants.mk (X.ρ.comp U.subtype) x := rfl

theorem nuLin_nuInv (X : Rep.{0} ℚ P) : (nuLin U A X).comp (nuInv U A X) = LinearMap.id := by
  refine Coinvariants.hom_ext (LinearMap.ext fun w => ?_)
  induction w using TensorProduct.inductionOn with
  | tmul a x => rfl
  | add x y hx hy =>
    simp only [LinearMap.comp_apply, map_add] at hx hy ⊢
    rw [hx, hy]

theorem nuInv_nuLin (X : Rep.{0} ℚ P) : (nuInv U A X).comp (nuLin U A X) = LinearMap.id := by
  refine TensorProduct.ext' fun a ξ => ?_
  induction ξ using Coinvariants.induction_on with
  | h x => rfl

section Iso

variable [U.Normal]

/-- `Ā ⊗ Φ(X) ≃ Φ(A ⊗ X)` as vector spaces. -/
def nuEquiv (X : Rep.{0} ℚ P) :
    TensorProduct ℚ A.V (Coinvariants (X.ρ.comp U.subtype)) ≃ₗ[ℚ]
      Coinvariants ((A ⊗ X).ρ.comp U.subtype) :=
  LinearEquiv.ofLinearMap (nuLin U A X) (nuInv U A X) (nuLin_nuInv U A X) (nuInv_nuLin U A X)

theorem nuLin_equivariant (X : Rep.{0} ℚ P) (q : P ⧸ U) :
    nuLin U A X ∘ₗ ((Abar U A ⊗ (Phi U).obj X).ρ q) = ((Phi U).obj (A ⊗ X)).ρ q ∘ₗ nuLin U A X := by
  induction q using QuotientGroup.induction_on with
  | H g =>
    refine TensorProduct.ext' fun a ξ => ?_
    induction ξ using Coinvariants.induction_on with
    | h x =>
      rfl

/-- **`ν : Ā ⊗ Φ(X) ≅ Φ(A ⊗ X)`**. -/
def nuIso (X : Rep.{0} ℚ P) : Abar U A ⊗ (Phi U).obj X ≅ (Phi U).obj (A ⊗ X) :=
  Rep.mkIso (Representation.Equiv.mk (nuEquiv U A X) (fun q => nuLin_equivariant U A X q))

/-- `ν` as a morphism. -/
def nuRep (X : Rep.{0} ℚ P) : Abar U A ⊗ (Phi U).obj X ⟶ (Phi U).obj (A ⊗ X) := (nuIso U A X).hom

theorem nuRep_hom_tmul_mk (X : Rep.{0} ℚ P) (a : A.V) (x : X.V) :
    (nuRep U A X).hom (a ⊗ₜ[ℚ] Coinvariants.mk (X.ρ.comp U.subtype) x) =
      Coinvariants.mk ((A ⊗ X).ρ.comp U.subtype) (a ⊗ₜ[ℚ] x) := rfl

theorem nuRep_natural {X Y : Rep.{0} ℚ P} (f : X ⟶ Y) :
    (Abar U A ◁ (Phi U).map f) ≫ nuRep U A Y = nuRep U A X ≫ (Phi U).map (A ◁ f) := by
  refine Rep.hom_ext (Representation.IntertwiningMap.ext (TensorProduct.ext' fun a ξ => ?_))
  induction ξ using Coinvariants.induction_on with
  | h x => rfl

end Iso

section Instance

variable [U.Normal] (R : ProjectiveResolution (Rep.trivial ℚ P ℚ)) {L P1' P0' : Rep.{0} ℚ (P ⧸ U)}
  (d' : P1' ⟶ P0')

/-- `Θ_j = (Ā ⊗ L) ⊗ P ≅ Ā ⊗ (L ⊗ P) → Ā ⊗ Φ(R_j) → Φ(A ⊗ R_j)`. -/
def ThetaIn {j : ℕ} {P' : Rep.{0} ℚ (P ⧸ U)} (t : L ⊗ P' ⟶ (Phi U).obj (R.complex.X j)) :
    (Abar U A ⊗ L) ⊗ P' ⟶ (ZR U R A).X j :=
  (α_ (Abar U A) L P').hom ≫ (Abar U A ◁ t) ≫ nuRep U A (R.complex.X j)

theorem ThetaIn_comm (t3 : L ⊗ P1' ⟶ (Phi U).obj (R.complex.X 3))
    (t2 : L ⊗ P0' ⟶ (Phi U).obj (R.complex.X 2))
    (hi : t3 ≫ (Phi U).map (R.complex.d 3 2) = (L ◁ d') ≫ t2) :
    ThetaIn U A R t3 ≫ (ZR U R A).d 3 2 = ((Abar U A ⊗ L) ◁ d') ≫ ThetaIn U A R t2 := by
  change (α_ (Abar U A) L P1').hom ≫ (Abar U A ◁ t3) ≫ nuRep U A (R.complex.X 3) ≫
      (Phi U).map (A ◁ R.complex.d 3 2) = _
  rw [← nuRep_natural, ← Category.assoc (Abar U A ◁ t3), ← MonoidalCategory.whiskerLeft_comp, hi]
  unfold ThetaIn
  rw [MonoidalCategory.whiskerLeft_comp, ← Category.assoc, ← Category.assoc,
    ← MonoidalCategory.associator_naturality_right]
  simp only [Category.assoc]

theorem ThetaIn_cyc (t2 : L ⊗ P0' ⟶ (Phi U).obj (R.complex.X 2))
    (hii : t2 ≫ (Phi U).map (R.complex.d 2 1) = 0) :
    ThetaIn U A R t2 ≫ (ZR U R A).d 2 1 = 0 := by
  change (α_ (Abar U A) L P0').hom ≫ (Abar U A ◁ t2) ≫ nuRep U A (R.complex.X 2) ≫
      (Phi U).map (A ◁ R.complex.d 2 1) = 0
  rw [← nuRep_natural, ← Category.assoc (Abar U A ◁ t2), ← MonoidalCategory.whiskerLeft_comp, hii]
  simp

end Instance



/-- In a short complex of modules, a cycle with zero homology class is a boundary. -/
theorem moduleCat_boundary_of_homologyπ_eq_zero (S : ShortComplex (ModuleCat.{0} ℚ)) (z : S.cycles)
    (h : S.homologyπ.hom z = 0) : ∃ x : S.X₁, S.toCycles.hom x = z := by
  have h1 := congrArg (fun t => t.hom (S.moduleCatCyclesIso.hom z)) (S.moduleCatCyclesIso_inv_π)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1
  have e : S.moduleCatCyclesIso.inv.hom (S.moduleCatCyclesIso.hom z) = z := by
    simp
  rw [e, h] at h1
  have h2 : S.moduleCatLeftHomologyData.π.hom (S.moduleCatCyclesIso.hom z) = 0 := by
    have := congrArg S.moduleCatHomologyIso.hom.hom h1
    have e2 : S.moduleCatHomologyIso.hom.hom (S.moduleCatHomologyIso.inv.hom
        (S.moduleCatLeftHomologyData.π.hom (S.moduleCatCyclesIso.hom z))) =
        S.moduleCatLeftHomologyData.π.hom (S.moduleCatCyclesIso.hom z) := by
      simp
    rw [e2, map_zero] at this
    exact this.symm
  have h3 : S.moduleCatCyclesIso.hom z ∈ LinearMap.range S.moduleCatToCycles :=
    (Submodule.Quotient.mk_eq_zero _).1 h2
  obtain ⟨x, hx⟩ := h3
  refine ⟨x, ?_⟩
  have h4 := congrArg (fun t => t.hom x) S.toCycles_moduleCatCyclesIso_hom
  have h5 : S.moduleCatCyclesIso.hom (S.toCycles.hom x) = S.moduleCatCyclesIso.hom z := by
    refine Eq.trans ?_ hx
    exact h4
  exact (ConcreteCategory.bijective_of_isIso S.moduleCatCyclesIso.hom).1 h5

theorem boundary_of_homologyπ_eq_zero {Q : Type} [Group Q] (Z : ChainComplex (Rep.{0} ℚ Q) ℕ)
    {N : Rep.{0} ℚ Q} (Θ : N ⟶ Z.X 2) (hΘ : Θ ≫ Z.d 2 1 = 0) (n : N.V)
    (h : (Z.liftCycles Θ 1 next21 hΘ ≫ Z.homologyπ 2).hom n = 0) :
    ∃ y : (Z.X ((ComplexShape.down ℕ).prev 2)).V, (Z.d ((ComplexShape.down ℕ).prev 2) 2).hom y = Θ.hom n := by
  let F := forget₂ (Rep.{0} ℚ Q) (ModuleCat ℚ)
  let S := Z.sc 2
  have hpi := piF F S
  let k : (F.obj S.cycles) := (F.map (Z.liftCycles Θ 1 next21 hΘ)).hom n
  let z : (S.map F).cycles := (S.mapCyclesIso F).inv.hom k
  have hz0 : (S.map F).homologyπ.hom z = 0 := by
    have h1 := congrArg (fun t => t.hom z) hpi
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1
    have e : (S.mapCyclesIso F).hom.hom z = k := by
      have := congrArg (fun t => t.hom k) (Iso.inv_hom_id (S.mapCyclesIso F))
      exact this
    rw [e] at h1
    have hk : (F.map S.homologyπ).hom k = 0 := by
      have : (F.map (Z.liftCycles Θ 1 next21 hΘ ≫ Z.homologyπ 2)).hom n = 0 := h
      exact this
    rw [hk] at h1
    exact (ConcreteCategory.bijective_of_isIso (S.mapHomologyIso F).hom).1 (h1.trans (map_zero _).symm)
  obtain ⟨x, hx⟩ := moduleCat_boundary_of_homologyπ_eq_zero (S.map F) z hz0
  refine ⟨x, ?_⟩
  have h2 := congrArg ((S.map F).iCycles.hom) hx
  have h3 : (S.map F).iCycles.hom ((S.map F).toCycles.hom x) = (S.map F).f.hom x := by
    have := congrArg (fun t => t.hom x) (S.map F).toCycles_i
    exact this
  have h4 : (S.map F).iCycles.hom z = Θ.hom n := by
    have h5 := ShortComplex.mapCyclesIso_hom_iCycles (S := S) F
    have h6 := congrArg (fun t => t.hom z) h5
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h6
    have e : (S.mapCyclesIso F).hom.hom z = k := by
      have := congrArg (fun t => t.hom k) (Iso.inv_hom_id (S.mapCyclesIso F))
      exact this
    rw [e] at h6
    refine h6.symm.trans ?_
    have h7 : F.map (Z.liftCycles Θ 1 next21 hΘ) ≫ F.map (S.iCycles) = F.map Θ := by
      exact ((F.map_comp _ _).symm.trans (congrArg F.map (HomologicalComplex.liftCycles_i Z Θ 1 next21 hΘ)))
    exact congrArg (fun t => t.hom n) h7
  rw [h4] at h2
  rw [← h2, h3]
  rfl

theorem boundary_of_homologyπ_eq_zero' {Q : Type} [Group Q] (Z : ChainComplex (Rep.{0} ℚ Q) ℕ)
    {N : Rep.{0} ℚ Q} (Θ : N ⟶ Z.X 2) (hΘ : Θ ≫ Z.d 2 1 = 0) (n : N.V)
    (h : (Z.liftCycles Θ 1 next21 hΘ ≫ Z.homologyπ 2).hom n = 0) :
    ∃ y : (Z.X 3).V, (Z.d 3 2).hom y = Θ.hom n := by
  obtain ⟨y, hy⟩ := boundary_of_homologyπ_eq_zero Z Θ hΘ n h
  have hp : (ComplexShape.down ℕ).prev 2 = 3 := ChainComplex.prev ℕ 2
  generalize hp' : (ComplexShape.down ℕ).prev 2 = p at y hy
  have : p = 3 := hp'.symm.trans hp
  subst this
  exact ⟨y, hy⟩

section Contraction

variable {P : Type} [Group P] (U : Subgroup P) (A : Rep.{0} ℚ P)
  [Representation.IsTrivial (A.ρ.comp U.subtype)] (f : A.V →ₗ[ℚ] ℚ)

/-- `[a ⊗ x] ↦ f(a) [x]`. -/
def kapLin (X : Rep.{0} ℚ P) :
    Coinvariants ((A ⊗ X).ρ.comp U.subtype) →ₗ[ℚ] Coinvariants (X.ρ.comp U.subtype) :=
  Coinvariants.lift _
    ((TensorProduct.lid ℚ (Coinvariants (X.ρ.comp U.subtype))).toLinearMap ∘ₗ
      TensorProduct.map f (Coinvariants.mk (X.ρ.comp U.subtype)))
    (fun u => by
      refine TensorProduct.ext' fun a x => ?_
      change (TensorProduct.lid ℚ (Coinvariants (X.ρ.comp U.subtype)))
        (TensorProduct.map f (Coinvariants.mk (X.ρ.comp U.subtype)) (A.ρ (u : P) a ⊗ₜ[ℚ] X.ρ (u : P) x)) =
        (TensorProduct.lid ℚ (Coinvariants (X.ρ.comp U.subtype)))
          (TensorProduct.map f (Coinvariants.mk (X.ρ.comp U.subtype)) (a ⊗ₜ[ℚ] x))
      rw [A_triv U A u a]
      simp only [TensorProduct.map_tmul, TensorProduct.lid_tmul]
      exact congrArg (fun z => f a • z) (Coinvariants.mk_self_apply (X.ρ.comp U.subtype) u x))

theorem kapLin_mk (X : Rep.{0} ℚ P) (a : A.V) (x : X.V) :
    kapLin U A f X (Coinvariants.mk ((A ⊗ X).ρ.comp U.subtype) (a ⊗ₜ[ℚ] x)) =
      f a • Coinvariants.mk (X.ρ.comp U.subtype) x := by
  change (TensorProduct.lid ℚ (Coinvariants (X.ρ.comp U.subtype)))
    (TensorProduct.map f (Coinvariants.mk (X.ρ.comp U.subtype)) (a ⊗ₜ[ℚ] x)) = _
  simp only [TensorProduct.map_tmul, TensorProduct.lid_tmul]

theorem kapLin_nuLin (X : Rep.{0} ℚ P) (a : A.V) (ξ : Coinvariants (X.ρ.comp U.subtype)) :
    kapLin U A f X (nuLin U A X (a ⊗ₜ[ℚ] ξ)) = f a • ξ := by
  induction ξ using Coinvariants.induction_on with
  | h x => exact kapLin_mk U A f X a x

variable [U.Normal]

theorem kapLin_natural {X Y : Rep.{0} ℚ P} (g : X ⟶ Y) :
    kapLin U A f Y ∘ₗ ((Phi U).map (A ◁ g)).hom.toLinearMap =
      ((Phi U).map g).hom.toLinearMap ∘ₗ kapLin U A f X := by
  refine Coinvariants.hom_ext (TensorProduct.ext' fun a x => ?_)
  change kapLin U A f Y (Coinvariants.mk _ (a ⊗ₜ[ℚ] g.hom x)) =
    ((Phi U).map g).hom (kapLin U A f X (Coinvariants.mk _ (a ⊗ₜ[ℚ] x)))
  rw [kapLin_mk, kapLin_mk]
  change f a • Coinvariants.mk (Y.ρ.comp U.subtype) (g.hom x) =
    ((Phi U).map g).hom.toLinearMap (f a • Coinvariants.mk (X.ρ.comp U.subtype) x)
  exact (((Phi U).map g).hom.toLinearMap.map_smul (f a) (Coinvariants.mk (X.ρ.comp U.subtype) x)).symm

end Contraction

section PsiInj

variable {P : Type} [Group P] (U : Subgroup P) [U.Normal] (A : Rep.{0} ℚ P)
  [Representation.IsTrivial (A.ρ.comp U.subtype)] (R : ProjectiveResolution (Rep.trivial ℚ P ℚ))
  {L P1' P0' : Rep.{0} ℚ (P ⧸ U)} (d' : P1' ⟶ P0') (ε' : P0' ⟶ Rep.trivial ℚ (P ⧸ U) ℚ)
  (hdε : d' ≫ ε' = 0) (hS : (ShortComplex.mk d' ε' hdε).ShortExact)
  (t3 : L ⊗ P1' ⟶ (Phi U).obj (R.complex.X 3)) (t2 : L ⊗ P0' ⟶ (Phi U).obj (R.complex.X 2))
  (hi : t3 ≫ (Phi U).map (R.complex.d 3 2) = (L ◁ d') ≫ t2)
  (hii : t2 ≫ (Phi U).map (R.complex.d 2 1) = 0)

/-- The map `Ψ'` of the tree theorem for the data `(Ā ⊗ L, Θ_j)`. -/
def PsiInst : Abar U A ⊗ L ⟶ (ZR U R A).homology 2 :=
  PsiPrime (ZR U R A) P1' P0' d' ε' hdε (Abar U A ⊗ L) hS (ThetaIn U A R t3) (ThetaIn U A R t2)
    (ThetaIn_comm U A R d' t3 t2 hi) (ThetaIn_cyc U A R t2 hii)

theorem PsiInst_tmul (a : A.V) (ℓ : L.V) :
    (PsiInst U A R d' ε' hdε hS t3 t2 hi hii).hom (a ⊗ₜ[ℚ] ℓ) =
      ((ZR U R A).liftCycles (ThetaIn U A R t2) 1 next21 (ThetaIn_cyc U A R t2 hii) ≫
        (ZR U R A).homologyπ 2).hom
        ((a ⊗ₜ[ℚ] ℓ) ⊗ₜ[ℚ] sZero P1' P0' d' ε' hdε hS) := rfl

theorem Theta2_tmul (a : A.V) (ℓ : L.V) (p : P0'.V) :
    (ThetaIn U A R t2).hom ((a ⊗ₜ[ℚ] ℓ) ⊗ₜ[ℚ] p) =
      (nuRep U A (R.complex.X 2)).hom (a ⊗ₜ[ℚ] t2.hom (ℓ ⊗ₜ[ℚ] p)) := rfl

theorem one_dim_tmul {M0 L0 : Type} [AddCommGroup M0] [Module ℚ M0] [AddCommGroup L0] [Module ℚ L0]
    (ℓ₀ : L0) (hℓ : ℓ₀ ≠ 0) (hL : Module.finrank ℚ L0 = 1) (m : M0 ⊗[ℚ] L0) :
    ∃ a : M0, m = a ⊗ₜ[ℚ] ℓ₀ := by
  have hc := (finrank_eq_one_iff_of_nonzero' ℓ₀ hℓ).1 hL
  induction m using TensorProduct.inductionOn with
  | tmul a ℓ =>
    obtain ⟨c, rfl⟩ := hc ℓ
    exact ⟨c • a, (TensorProduct.smul_tmul c a ℓ₀).symm⟩
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, by rw [TensorProduct.add_tmul]⟩

theorem PsiInst_injective (ℓ₀ : L.V) (hℓ : ℓ₀ ≠ 0) (hL : Module.finrank ℚ L.V = 1)
    (h3 : t2.hom (ℓ₀ ⊗ₜ[ℚ] sZero P1' P0' d' ε' hdε hS) ∉
      LinearMap.range ((Phi U).map (R.complex.d 3 2)).hom.toLinearMap) :
    Function.Injective (PsiInst U A R d' ε' hdε hS t3 t2 hi hii).hom := by
  show Function.Injective (PsiInst U A R d' ε' hdε hS t3 t2 hi hii).hom.toLinearMap
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro m hm
  obtain ⟨a, rfl⟩ := one_dim_tmul ℓ₀ hℓ hL m
  by_contra hne
  have ha : a ≠ 0 := by
    rintro rfl
    exact hne (by simp)
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℚ ha
  have h0 : ((ZR U R A).liftCycles (ThetaIn U A R t2) 1 next21 (ThetaIn_cyc U A R t2 hii) ≫
        (ZR U R A).homologyπ 2).hom ((a ⊗ₜ[ℚ] ℓ₀) ⊗ₜ[ℚ] sZero P1' P0' d' ε' hdε hS) = 0 := hm
  obtain ⟨y, hy⟩ := boundary_of_homologyπ_eq_zero' (ZR U R A) (ThetaIn U A R t2) (ThetaIn_cyc U A R t2 hii) _ h0
  rw [Theta2_tmul] at hy
  apply h3
  have h1 := congrArg (kapLin U A f (R.complex.X 2)) hy
  have h2 : kapLin U A f (R.complex.X 2) ((nuRep U A (R.complex.X 2)).hom
      (a ⊗ₜ[ℚ] t2.hom (ℓ₀ ⊗ₜ[ℚ] sZero P1' P0' d' ε' hdε hS))) =
      t2.hom (ℓ₀ ⊗ₜ[ℚ] sZero P1' P0' d' ε' hdε hS) := by
    exact (kapLin_nuLin U A f (R.complex.X 2) a _).trans (by rw [hf]; exact one_smul ℚ _)
  rw [h2] at h1
  refine ⟨kapLin U A f (R.complex.X 3) y, ?_⟩
  rw [← h1]
  have h4 := LinearMap.congr_fun (kapLin_natural U A f (R.complex.d 3 2)) y
  exact h4.symm

theorem PsiInst_isIso [Module.Finite ℚ A.V] (eU : U2 ≃* U) (hA : ∀ u : U, A.ρ u = 1)
    (ℓ₀ : L.V) (hℓ : ℓ₀ ≠ 0) (hL : Module.finrank ℚ L.V = 1)
    (h3 : t2.hom (ℓ₀ ⊗ₜ[ℚ] sZero P1' P0' d' ε' hdε hS) ∉
      LinearMap.range ((Phi U).map (R.complex.d 3 2)).hom.toLinearMap) :
    IsIso (PsiInst U A R d' ε' hdε hS t3 t2 hi hii) := by
  have hinj := PsiInst_injective U A R d' ε' hdε hS t3 t2 hi hii ℓ₀ hℓ hL h3
  have : Module.Finite ℚ L.V := Module.finite_of_finrank_pos (by omega)
  let e2 : (ZP U A).homology 2 ≅ (ZR U R A).homology 2 := asIso (HomologicalComplex.homologyMap (fZ U R A) 2)
  let e3 : ((ZP U A).homology 2).V ≃ₗ[ℚ] ((ZR U R A).homology 2).V :=
    ((forget₂ (Rep.{0} ℚ (P ⧸ U)) (ModuleCat ℚ)).mapIso e2).toLinearEquiv
  have hfr : Module.finrank ℚ ((ZR U R A).homology 2).V = Module.finrank ℚ A.V :=
    (LinearEquiv.finrank_eq ((gammaEquiv eU hA).trans e3)).symm
  have hfM : Module.finrank ℚ (Abar U A ⊗ L).V = Module.finrank ℚ A.V := by
    change Module.finrank ℚ (A.V ⊗[ℚ] L.V) = _
    rw [Module.finrank_tensorProduct, hL, mul_one]
  have : Module.Finite ℚ (Abar U A ⊗ L).V := inferInstanceAs (Module.Finite ℚ (A.V ⊗[ℚ] L.V))
  have : Module.Finite ℚ ((ZR U R A).homology 2).V :=
    Module.Finite.equiv ((gammaEquiv eU hA).trans e3)
  have hsurj : Function.Surjective (PsiInst U A R d' ε' hdε hS t3 t2 hi hii).hom :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (hfM.trans hfr.symm)).1 hinj
  have : IsIso ((forget₂ (Rep.{0} ℚ (P ⧸ U)) (ModuleCat ℚ)).map
      (PsiInst U A R d' ε' hdε hS t3 t2 hi hii)) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact ⟨hinj, hsurj⟩
  exact isIso_of_reflects_iso _ (forget₂ (Rep.{0} ℚ (P ⧸ U)) (ModuleCat ℚ))

end PsiInj

section Character

variable {P : Type} [Group P] (U : Subgroup P) [U.Normal]

instance trivialRep_isTrivial_comp : Representation.IsTrivial ((Rep.trivial ℚ P ℚ).ρ.comp U.subtype) :=
  ⟨fun _ => rfl⟩

omit [U.Normal] in
theorem trivialRep_hA : ∀ u : U, (Rep.trivial ℚ P ℚ).ρ u = 1 := fun _ => rfl

variable (R : ProjectiveResolution (Rep.trivial ℚ P ℚ))
  {L P1' P0' : Rep.{0} ℚ (P ⧸ U)} (d' : P1' ⟶ P0') (ε' : P0' ⟶ Rep.trivial ℚ (P ⧸ U) ℚ)
  (hdε : d' ≫ ε' = 0) (hS : (ShortComplex.mk d' ε' hdε).ShortExact)
  (t3 : L ⊗ P1' ⟶ (Phi U).obj (R.complex.X 3)) (t2 : L ⊗ P0' ⟶ (Phi U).obj (R.complex.X 2))
  (hi : t3 ≫ (Phi U).map (R.complex.d 3 2) = (L ◁ d') ≫ t2)
  (hii : t2 ≫ (Phi U).map (R.complex.d 2 1) = 0)

include hS t3 hi hii in
/-- **The character of `L`**: if the cell data give an isomorphism `Ā ⊗ L ≅ H₂(ZR U R A)` for the trivial module
`A = ℚ`, then `P/U` acts on `L` through the determinant factor `deltaG`. -/
theorem L_character (eU : U2 ≃* U) (ℓ₀ : L.V) (hℓ : ℓ₀ ≠ 0) (hL : Module.finrank ℚ L.V = 1)
    (h3 : t2.hom (ℓ₀ ⊗ₜ[ℚ] sZero P1' P0' d' ε' hdε hS) ∉
      LinearMap.range ((Phi U).map (R.complex.d 3 2)).hom.toLinearMap) (p : P) :
    L.ρ (QuotientGroup.mk p) = (deltaG eU p) • LinearMap.id := by
  let A : Rep.{0} ℚ P := Rep.trivial ℚ P ℚ
  have hinj := PsiInst_injective U A R d' ε' hdε hS t3 t2 hi hii ℓ₀ hℓ hL h3
  refine LinearMap.ext fun ℓ => ?_
  -- the action on `H₂(ZR)` is the scalar `deltaG`
  have hact : ∀ w : ((ZR U R A).homology 2).V,
      ((ZR U R A).homology 2).ρ (QuotientGroup.mk p) w = deltaG eU p • w := by
    intro w
    let e2 : (ZP U A).homology 2 ≅ (ZR U R A).homology 2 :=
      asIso (HomologicalComplex.homologyMap (fZ U R A) 2)
    obtain ⟨a, ha⟩ := (gammaEquiv eU (trivialRep_hA U)).surjective (e2.inv.hom w)
    have hw : w = e2.hom.hom (gammaEquiv eU (trivialRep_hA U) a) := by
      rw [ha]
      have := congrArg (fun t => t.hom w) e2.inv_hom_id
      exact this.symm
    rw [hw, ← Rep.hom_comm_apply e2.hom, gammaEquiv_equivariant eU (trivialRep_hA U) p a, map_smul]
    have : A.ρ p a = a := rfl
    rw [this]
    rfl
  set Ψ := PsiInst U A R d' ε' hdε hS t3 t2 hi hii with hΨ
  have h1 : Ψ.hom ((1 : ℚ) ⊗ₜ[ℚ] L.ρ (QuotientGroup.mk p) ℓ) =
      Ψ.hom ((deltaG eU p) • ((1 : ℚ) ⊗ₜ[ℚ] ℓ)) := by
    have e : ((1 : ℚ) ⊗ₜ[ℚ] L.ρ (QuotientGroup.mk p) ℓ : (Abar U A ⊗ L).V) =
        (Abar U A ⊗ L).ρ (QuotientGroup.mk p) ((1 : ℚ) ⊗ₜ[ℚ] ℓ) := rfl
    rw [e, Rep.hom_comm_apply Ψ, hact, map_smul]
  have h2 := hinj h1
  have h3' := congrArg (TensorProduct.lid ℚ L.V) h2
  rw [TensorProduct.lid_tmul, TensorProduct.smul_tmul', TensorProduct.lid_tmul] at h3'
  simpa using h3'

end Character


end TernaryPeriodPolynomials.Argument.HochschildSerre
