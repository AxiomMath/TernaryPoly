module

public import TernaryPeriodPolynomials.GroupCohomology.Homology.Descent
public import TernaryPeriodPolynomials.GroupCohomology.Homology.BarMaps

@[expose] public section


/-!
# Corestriction from a normal finite index subgroup, in Mathlib's `groupHomology`

For `N ⊲ K` of finite index with `[K : N]` invertible in the field `k` and `A : Rep k K`, let
`cor = groupHomology.map N.subtype (𝟙 _) : Hₙ(N, Res A) → Hₙ(K, A)` and let
`c_g = groupHomology.map (conj g) (ρ g) : Hₙ(N, Res A) → Hₙ(N, Res A)` for `g ∈ K` (`cAct`).
The main results are

* `corN_surjective`: `cor` is surjective;
* `corN_eq_zero_iff`: `cor z = 0 ↔ avg z = 0`, where `avg = [K:N]⁻¹ ∑_{x ∈ K/N} c_{x.out}` (`avgN`);
* `corN_cAct`: `cor ∘ c_g = cor`;
* `avgN_idem`: `avg` is idempotent.

The proof compares Mathlib's `groupHomologyIso` for the bar resolution `P` of `K` (giving
`Hₙ(K, A) ≅ Hₙ((P ⊗ A)_K)`) and for its restriction to `N` (giving `Hₙ(N, Res A) ≅
Hₙ((P ⊗ A)_N)`), via the naturality statements `cor_comparison` (`cor` is the map induced by the
quotient `(P ⊗ A)_N → (P ⊗ A)_K`) and `conj_comparison` (`c_g` is induced by the diagonal action of
`g`; this uses that the right translations of the bar resolution are homotopic to the identity),
and then applies the splitting of `Descent`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

universe u

namespace TernaryPeriodPolynomials.Argument.GroupHomology

open CategoryTheory Finsupp Rep MonoidalCategory
open scoped MonoidAlgebra Classical


section Rt

variable {k : Type u} [CommRing k] {K : Type u} [Group K]

/-- Conjugation `y ↦ a⁻¹ y a` as a monoid homomorphism. -/
def conjInv (a : K) : K →* K := (MulAut.conj a⁻¹).toMonoidHom

@[simp] theorem conjInv_apply (a y : K) : conjInv a y = a⁻¹ * y * a := by
  simp [conjInv]

/-- Right translation by `a` on the terms of the bar resolution. -/
def rtTerm (a : K) (n : ℕ) : free k K (Fin n → K) ⟶ free k K (Fin n → K) :=
  freeLift k K _ (fun x => single (conjInv a ∘ x) (MonoidAlgebra.single a (1 : k)))

theorem rtTerm_single (a : K) (n : ℕ) (x : Fin n → K) (h : K) (r : k) :
    (rtTerm (k := k) a n).hom (single x (MonoidAlgebra.single h r)) =
      single (conjInv a ∘ x) (MonoidAlgebra.single (h * a) r) := by
  simp [rtTerm, Representation.freeLift_single_single]

theorem rtTerm_comm (a : K) (n : ℕ) :
    rtTerm (k := k) a (n + 1) ≫ barComplex.d k K n = barComplex.d k K n ≫ rtTerm a n := by
  refine free_ext _ _ _ _ _ fun x => ?_
  have h1 := barComplex.d_single (k := k) (G := K) n x
  have h2 := barComplex.d_single (k := k) (G := K) n (conjInv a ∘ x)
  simp only [Rep.hom_comp, Representation.IntertwiningMap.comp_apply]
  have e1 : (rtTerm (k := k) a (n + 1)).hom (single x (MonoidAlgebra.single 1 1)) =
      (Representation.free k K (Fin (n + 1) → K)) a
        (single (conjInv a ∘ x) (MonoidAlgebra.single 1 1)) := by
    rw [rtTerm_single, Representation.free_single_single]
    simp
  rw [e1, Rep.hom_comm_apply (barComplex.d k K n) a, h2, h1]
  simp only [map_add, map_sum]
  congr 1
  · rw [Representation.free_single_single, rtTerm_single]
    simp [conjInv_apply, mul_assoc, Function.comp_def]
  · refine Finset.sum_congr rfl fun j _ => ?_
    have hc := Fin.comp_contractNth (· * ·) (· * ·) (f := conjInv a)
      (fun x y => map_mul (conjInv a) x y) j x
    rw [Representation.free_single_single, rtTerm_single, hc]
    simp

end Rt

section Cmp

variable {k : Type u} [Field k] {K : Type u} [Group K] (N : Subgroup K) [N.Normal] (A : Rep.{u} k K)

/-- `A ⊗ P_n` for the bar resolution `P` of `K`. -/
abbrev YA : ChainComplex (Rep.{u} k K) ℕ :=
  ((tensorLeft A).mapHomologicalComplex (ComplexShape.down ℕ)).obj (barComplex k K)

theorem inhomIso_hom_f_single {G : Type u} [Group G] [DecidableEq G] (B : Rep.{u} k G) (n : ℕ)
    (x : Fin n → G) (b : B) :
    ((groupHomology.inhomogeneousChainsIso B).hom.f n).hom (single x b) =
      Representation.Coinvariants.mk (B.ρ.tprod (Representation.free k G (Fin n → G)))
        (b ⊗ₜ[k] single x (MonoidAlgebra.single (1 : G) (1 : k))) := by
  simp only [groupHomology.inhomogeneousChainsIso]
  exact finsuppToCoinvariantsTensorFree_single x b

theorem coinvTensor_map_mk {G : Type u} [Group G] (B : Rep.{u} k G) {X Y : Rep.{u} k G} (φ : X ⟶ Y)
    (b : B) (x : X) :
    (((coinvariantsTensor k G).obj B).map φ).hom
        (Representation.Coinvariants.mk (B.ρ.tprod X.ρ) (b ⊗ₜ[k] x)) =
      Representation.Coinvariants.mk (B.ρ.tprod Y.ρ) (b ⊗ₜ[k] φ.hom x) := rfl

/-- the comparison `inhom(N, Res A) → C_N` -/
def betaA : groupHomology.inhomogeneousChains (Rep.res N.subtype A) ⟶
    ((resFunctor N.subtype).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (barComplex k K) |>.coinvariantsTensorObj (Rep.res N.subtype A) :=
  (groupHomology.inhomogeneousChainsIso (Rep.res N.subtype A)).hom ≫
    (((Rep.coinvariantsTensor k N).obj (Rep.res N.subtype A)).mapHomologicalComplex _).map
      (barMap (k := k) N.subtype)

omit [N.Normal] in
theorem chains_incl_comm :
    groupHomology.chainsMap N.subtype (𝟙 (Rep.res N.subtype A)) ≫
        (groupHomology.inhomogeneousChainsIso A).hom =
      betaA N A ≫ QY N (YA A) := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  refine groupHomology.inhomogeneousChains.ext fun x => ?_
  refine ModuleCat.hom_ext (LinearMap.ext fun a => ?_)
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.hom_ofHom, lsingle_apply]
  have eL : ((groupHomology.chainsMap N.subtype (𝟙 (Rep.res N.subtype A))).f n).hom (single x a) =
      single (N.subtype ∘ x) a := by
    have := groupHomology.chainsMap_f_single N.subtype (𝟙 (Rep.res N.subtype A)) n x a
    simpa using this
  have e1 := inhomIso_hom_f_single (Rep.res N.subtype A) n x a
  have e2 := coinvTensor_map_mk (Rep.res N.subtype A) ((barMap (k := k) N.subtype).f n) a
    (single x (MonoidAlgebra.single (1 : N) (1 : k)))
  have e3 : ((barMap (k := k) N.subtype).f n).hom (single x (MonoidAlgebra.single (1 : N) (1 : k))) =
      single (N.subtype ∘ x) (MonoidAlgebra.single (1 : K) (1 : k)) := by
    change (barTerm (k := k) N.subtype n).hom _ = _
    rw [barTerm_single, map_one]
  have e5 := inhomIso_hom_f_single A n (N.subtype ∘ x) a
  refine Eq.trans (congrArg (fun z => ((groupHomology.inhomogeneousChainsIso A).hom.f n).hom z) eL) ?_
  refine Eq.trans e5 ?_
  change _ = (qMap N (A ⊗ free k K (Fin n → K)).ρ)
    ((((coinvariantsTensor k N).obj (Rep.res N.subtype A)).map ((barMap (k := k) N.subtype).f n)).hom
      (((groupHomology.inhomogeneousChainsIso (Rep.res N.subtype A)).hom.f n).hom (single x a)))
  rw [e1, e2, e3]
  rfl


end Cmp

section RtMap

theorem toSingle₀_ext' {V : Type*} [Category V] [Abelian V] {C : ChainComplex V ℕ} {X : V}
    (φ ψ : C ⟶ (ChainComplex.single₀ V).obj X) (h : φ.f 0 = ψ.f 0) : φ = ψ :=
  (ChainComplex.toSingle₀Equiv C X).injective (Subtype.ext h)

variable {k : Type u} [Field k] {K : Type u} [Group K]

/-- Right translation as a chain map `bar(K) ⟶ bar(K)`. -/
def rtMap (a : K) : barComplex k K ⟶ barComplex k K where
  f n := rtTerm a n
  comm' := by
    rintro i j (rfl : j + 1 = i)
    simp only [barComplex, ChainComplex.of_d]
    exact rtTerm_comm (k := k) a j

theorem rtMap_pi (a : K) :
    (rtMap (k := k) a).f 0 ≫ (barResolution k K).π.f 0 = (barResolution k K).π.f 0 := by
  refine free_ext _ _ _ _ _ fun x => ?_
  have h2 := barPi_f_zero (k := k) (G := K) x 1 1
  have h3 := barPi_f_zero (k := k) (G := K) (conjInv a ∘ x) a 1
  refine Eq.trans ?_ h2.symm
  change ((barResolution k K).π.f 0).hom ((rtTerm (k := k) a 0).hom (single x (MonoidAlgebra.single 1 1))) = _
  rw [rtTerm_single]
  simpa using h3

/-- `rtMap a` is homotopic to the identity (any two lifts of the identity are). -/
def rtHomotopy (a : K) : Homotopy (rtMap (k := k) a) (𝟙 (barComplex k K)) :=
  ProjectiveResolution.liftHomotopy (𝟙 _) (P := barResolution k K) (Q := barResolution k K)
    (rtMap a) (𝟙 _)
    (by
      apply toSingle₀_ext'
      refine (HomologicalComplex.comp_f _ _ 0).trans ((rtMap_pi (k := k) a).trans ?_)
      simp
      rfl)
    (by
      apply toSingle₀_ext'
      simp
      rfl)

end RtMap

section Conj

variable {k : Type u} [Field k] {K : Type u} [Group K] (N : Subgroup K) [N.Normal] (A : Rep.{u} k K)

/-- Conjugation by `g ∈ K` on the normal subgroup `N`, as a monoid homomorphism. -/
def conjN (g : K) : N →* N := (MulAut.conjNormal g).toMonoidHom

theorem conjN_coe (g : K) (n : N) : ((conjN N g n : N) : K) = g * n * g⁻¹ := by
  simp [conjN]

/-- The action of `g` on `A`, as a morphism `Res_N A ⟶ Res_{conj g} Res_N A`. -/
def conjRep (g : K) : Rep.res N.subtype A ⟶ Rep.res (conjN N g) (Rep.res N.subtype A) :=
  Rep.ofHom ⟨A.ρ g, fun n => by
    ext a
    change A.ρ g (A.ρ n a) = A.ρ (((conjN N g n : N) : K)) (A.ρ g a)
    have h : A.ρ g⁻¹ (A.ρ g a) = a := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
      rfl
    rw [conjN_coe, map_mul, map_mul]
    change A.ρ g (A.ρ n a) = A.ρ g (A.ρ n (A.ρ g⁻¹ (A.ρ g a)))
    rw [h]⟩

end Conj


section C2

variable {k : Type u} [Field k] {K : Type u} [Group K] (N : Subgroup K) [N.Normal] (A : Rep.{u} k K)

/-- Right translation on `CxN`. -/
def FNrt (a : K) : CxN N (YA A) ⟶ CxN N (YA A) :=
  ((cN (k := k) N).mapHomologicalComplex _).map
    (((tensorLeft A).mapHomologicalComplex _).map (rtMap (k := k) a))

omit [N.Normal] in
theorem homologyMap_FNrt (a : K) (n : ℕ) :
    HomologicalComplex.homologyMap (FNrt N A a) n = 𝟙 _ := by
  have h := (cN (k := k) N).mapHomotopy (c := ComplexShape.down ℕ)
    ((tensorLeft A).mapHomotopy (c := ComplexShape.down ℕ) (rtHomotopy (k := k) a))
  have := h.homologyMap_eq n
  simpa [FNrt] using this

omit [N.Normal] in
theorem cN_tensorLeft_mk {X Y : Rep.{u} k K} (φ : X ⟶ Y) (a : A) (p : X) :
    (cN (k := k) N).map ((tensorLeft A).map φ)
        (Representation.Coinvariants.mk _ (a ⊗ₜ[k] p)) =
      Representation.Coinvariants.mk _ (a ⊗ₜ[k] φ.hom p) := rfl

theorem gamMap_tensor_mk {X : Rep.{u} k K} (g : K) (a : A) (p : X) :
    gamMap N (A ⊗ X).ρ g (Representation.Coinvariants.mk _ (a ⊗ₜ[k] p)) =
      Representation.Coinvariants.mk _ (A.ρ g a ⊗ₜ[k] X.ρ g p) := rfl


omit [N.Normal] in
theorem betaA_single (n : ℕ) (x : Fin n → N) (a : A) :
    ((betaA N A).f n).hom (single x a) =
      Representation.Coinvariants.mk ((A.ρ.tprod (Representation.free k K (Fin n → K))).comp N.subtype)
        (a ⊗ₜ[k] single (N.subtype ∘ x) (MonoidAlgebra.single (1 : K) (1 : k))) := by
  have e1 := inhomIso_hom_f_single (Rep.res N.subtype A) n x a
  have e2 := coinvTensor_map_mk (Rep.res N.subtype A) ((barMap (k := k) N.subtype).f n) a
    (single x (MonoidAlgebra.single (1 : N) (1 : k)))
  have e3 : ((barMap (k := k) N.subtype).f n).hom (single x (MonoidAlgebra.single (1 : N) (1 : k))) =
      single (N.subtype ∘ x) (MonoidAlgebra.single (1 : K) (1 : k)) := by
    change (barTerm (k := k) N.subtype n).hom _ = _
    rw [barTerm_single, map_one]
  change (((coinvariantsTensor k N).obj (Rep.res N.subtype A)).map ((barMap (k := k) N.subtype).f n)).hom
      (((groupHomology.inhomogeneousChainsIso (Rep.res N.subtype A)).hom.f n).hom (single x a)) = _
  rw [e1, e2, e3]
  rfl

theorem chains_conj_comm (g : K) :
    groupHomology.chainsMap (conjN N g) (conjRep N A g) ≫ betaA N A =
      betaA N A ≫ GY N (YA A) g ≫ FNrt N A g⁻¹ := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  refine groupHomology.inhomogeneousChains.ext fun x => ?_
  refine ModuleCat.hom_ext (LinearMap.ext fun a => ?_)
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.hom_ofHom, lsingle_apply]
  have eL : ((groupHomology.chainsMap (conjN N g) (conjRep N A g)).f n).hom (single x a) =
      single (conjN N g ∘ x) (A.ρ g a) := by
    have := groupHomology.chainsMap_f_single (conjN N g) (conjRep N A g) n x a
    exact this
  change ((betaA N A).f n).hom (((groupHomology.chainsMap (conjN N g) (conjRep N A g)).f n).hom
      (single x a)) = ((FNrt N A g⁻¹).f n).hom (((GY N (YA A) g).f n).hom
        (((betaA N A).f n).hom (single x a)))
  rw [eL, betaA_single, betaA_single]
  change _ = (cN (k := k) N).map ((tensorLeft A).map (rtTerm (k := k) g⁻¹ n))
    (gamMap N (A ⊗ free k K (Fin n → K)).ρ g
      (Representation.Coinvariants.mk _ (a ⊗ₜ[k] single (N.subtype ∘ x)
        (MonoidAlgebra.single (1 : K) (1 : k)))))
  have hG := gamMap_tensor_mk N A (X := free k K (Fin n → K)) g a
    (single (N.subtype ∘ x) (MonoidAlgebra.single (1 : K) (1 : k)))
  have hF := cN_tensorLeft_mk N A (rtTerm (k := k) g⁻¹ n) (A.ρ g a)
    ((free k K (Fin n → K)).ρ g (single (N.subtype ∘ x) (MonoidAlgebra.single (1 : K) (1 : k))))
  have e : (rtTerm (k := k) g⁻¹ n).hom ((free k K (Fin n → K)).ρ g
      (single (N.subtype ∘ x) (MonoidAlgebra.single (1 : K) (1 : k)))) =
      single (N.subtype ∘ conjN N g ∘ x) (MonoidAlgebra.single (1 : K) (1 : k)) := by
    change (rtTerm (k := k) g⁻¹ n).hom
      ((Representation.free k K (Fin n → K)) g (single (N.subtype ∘ x) (MonoidAlgebra.single 1 1))) = _
    rw [Representation.free_single_single, rtTerm_single]
    congr 1
    · funext i
      simp [conjN_coe, conjInv_apply, mul_assoc]
    · simp
  refine Eq.trans ?_ ((congrArg (fun z => (cN (k := k) N).map ((tensorLeft A).map
    (rtTerm (k := k) g⁻¹ n)) z) hG).trans hF).symm
  exact (congrArg (fun z => Representation.Coinvariants.mk _ ((A.ρ g a) ⊗ₜ[k] z)) e).symm

end C2

section Hom

variable {k : Type u} [Field k] {K : Type u} [Group K] (N : Subgroup K) [N.Normal] (A : Rep.{u} k K)

/-- `Hₙ` isomorphism `Hₙ(N, Res A) ≅ Hₙ((Res P ⊗ Res A)_N)` through the restricted bar resolution. -/
abbrev eN (n : ℕ) :
    groupHomology (Rep.res N.subtype A) n ≅
      (CxN N (YA A)).homology n :=
  groupHomologyIso (Rep.res N.subtype A) n
    ((resFunctor N.subtype).mapProjectiveResolution (barResolution k K))

/-- `Hₙ(K, A) ≅ Hₙ((P ⊗ A)_K)` through the bar resolution. -/
abbrev eK (n : ℕ) : groupHomology A n ≅ (CxK (YA A)).homology n :=
  groupHomologyIso A n (barResolution k K)

omit [N.Normal] in
theorem eN_hom (n : ℕ) :
    (eN N A n).hom = HomologicalComplex.homologyMap (betaA N A) n := by
  have h := groupHomologyIso_hom_comp (Rep.res N.subtype A) n (barMap (k := k) N.subtype)
    (P := barResolution k N)
    (Q := (resFunctor N.subtype).mapProjectiveResolution (barResolution k K))
    (barMap_pi (k := k) N)
  rw [groupHomologyIso_bar_hom] at h
  rw [← h]
  rw [betaA, HomologicalComplex.homologyMap_comp]
  rfl

omit [N.Normal] in
theorem cor_comparison (n : ℕ) :
    groupHomology.map N.subtype (𝟙 (Rep.res N.subtype A)) n ≫ (eK A n).hom =
      (eN N A n).hom ≫ HomologicalComplex.homologyMap (QY N (YA A)) n := by
  have h1 := congrArg (fun φ => HomologicalComplex.homologyMap φ n) (chains_incl_comm N A)
  have hA := HomologicalComplex.homologyMap_comp
    (groupHomology.chainsMap N.subtype (𝟙 (Rep.res N.subtype A)))
    (groupHomology.inhomogeneousChainsIso A).hom n
  have hB := HomologicalComplex.homologyMap_comp (betaA N A) (QY N (YA A)) n
  rw [eN_hom, groupHomologyIso_bar_hom]
  exact hA.symm.trans (h1.trans hB)

theorem conj_comparison (g : K) (n : ℕ) :
    groupHomology.map (conjN N g) (conjRep N A g) n ≫ (eN N A n).hom =
      (eN N A n).hom ≫ HomologicalComplex.homologyMap (GY N (YA A) g) n := by
  have h1 := congrArg (fun φ => HomologicalComplex.homologyMap φ n) (chains_conj_comm N A g)
  have hA := HomologicalComplex.homologyMap_comp
    (groupHomology.chainsMap (conjN N g) (conjRep N A g)) (betaA N A) n
  have hC : HomologicalComplex.homologyMap (betaA N A ≫ GY N (YA A) g ≫ FNrt N A g⁻¹) n =
      HomologicalComplex.homologyMap (betaA N A) n ≫ HomologicalComplex.homologyMap (GY N (YA A) g) n := by
    have c1 := HomologicalComplex.homologyMap_comp (betaA N A) (GY N (YA A) g ≫ FNrt N A g⁻¹) n
    have c2 := HomologicalComplex.homologyMap_comp (GY N (YA A) g) (FNrt N A g⁻¹) n
    have c3 := homologyMap_FNrt N A g⁻¹ n
    refine c1.trans (congrArg (fun z => HomologicalComplex.homologyMap (betaA N A) n ≫ z)
      (c2.trans ((congrArg (fun z => HomologicalComplex.homologyMap (GY N (YA A) g) n ≫ z) c3).trans
        (Category.comp_id _))))
  rw [eN_hom]
  exact hA.symm.trans (h1.trans hC)

end Hom

section Alg

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

variable {k : Type u} [Field k] {K : Type u} [Group K] (N : Subgroup K) [N.Normal] [N.FiniteIndex]
  (A : Rep.{u} k K) (n : ℕ)

/-- The corestriction `Hₙ(N, Res A) → Hₙ(K, A)` as a linear map. -/
abbrev corN : groupHomology (Rep.res N.subtype A) n →ₗ[k] groupHomology A n :=
  (groupHomology.map N.subtype (𝟙 (Rep.res N.subtype A)) n).hom

/-- The conjugation action of `g ∈ K` on `Hₙ(N, Res A)` (Mathlib's functoriality for the pair
`(c_g, ρ(g))`). -/
abbrev cAct (g : K) : groupHomology (Rep.res N.subtype A) n →ₗ[k] groupHomology (Rep.res N.subtype A) n :=
  (groupHomology.map (conjN N g) (conjRep N A g) n).hom

/-- The averaging operator over `K/N` on `Hₙ(N, Res A)`. -/
def avgN : groupHomology (Rep.res N.subtype A) n →ₗ[k] groupHomology (Rep.res N.subtype A) n :=
  ((Fintype.card (K ⧸ N) : k)⁻¹) • ∑ x : K ⧸ N, cAct N A n x.out

omit [N.FiniteIndex] in
theorem eN_cAct (g : K) (z : groupHomology (Rep.res N.subtype A) n) :
    (eN N A n).hom.hom (cAct N A n g z) =
      (HomologicalComplex.homologyMap (GY N (YA A) g) n).hom ((eN N A n).hom.hom z) :=
  LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp (conj_comparison N A g n)) z

omit [N.Normal] [N.FiniteIndex] in
theorem eK_corN (z : groupHomology (Rep.res N.subtype A) n) :
    (eK A n).hom.hom (corN N A n z) =
      (HomologicalComplex.homologyMap (QY N (YA A)) n).hom ((eN N A n).hom.hom z) :=
  LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp (cor_comparison N A n)) z

theorem eN_avgN (z : groupHomology (Rep.res N.subtype A) n) :
    (eN N A n).hom.hom (avgN N A n z) = avgH N (YA A) n ((eN N A n).hom.hom z) := by
  unfold avgN avgH
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum, eN_cAct]

variable {N A n}

omit [N.Normal] [N.FiniteIndex] in
theorem iso_hom_bijective {X Y : ModuleCat.{u} k} (e : X ≅ Y) : Function.Bijective e.hom.hom :=
  ConcreteCategory.bijective_of_isIso e.hom

theorem corN_surjective (hm : (Fintype.card (K ⧸ N) : k) ≠ 0) : Function.Surjective (corN N A n) := by
  intro w
  obtain ⟨u, hu⟩ := descent_surjective N (YA A) n hm ((eK A n).hom.hom w)
  obtain ⟨z, rfl⟩ := (iso_hom_bijective (eN N A n)).2 u
  refine ⟨z, (iso_hom_bijective (eK A n)).1 ?_⟩
  exact (eK_corN N A n z).trans hu

theorem corN_eq_zero_iff (hm : (Fintype.card (K ⧸ N) : k) ≠ 0)
    (z : groupHomology (Rep.res N.subtype A) n) : corN N A n z = 0 ↔ avgN N A n z = 0 := by
  have e1 : corN N A n z = 0 ↔ (eK A n).hom.hom (corN N A n z) = 0 := by
    constructor
    · intro h; rw [h, map_zero]
    · intro h; exact (iso_hom_bijective (eK A n)).1 (h.trans (map_zero _).symm)
  have e2 : avgN N A n z = 0 ↔ (eN N A n).hom.hom (avgN N A n z) = 0 := by
    constructor
    · intro h; rw [h, map_zero]
    · intro h; exact (iso_hom_bijective (eN N A n)).1 (h.trans (map_zero _).symm)
  rw [e1, e2, eK_corN N A n, eN_avgN N A n]
  exact descent_ker N (YA A) n hm _

omit [N.FiniteIndex] in
theorem corN_cAct (g : K) (z : groupHomology (Rep.res N.subtype A) n) :
    corN N A n (cAct N A n g z) = corN N A n z := by
  refine (iso_hom_bijective (eK A n)).1 ?_
  rw [eK_corN N A n, eK_corN N A n, eN_cAct N A n]
  exact descent_gam N (YA A) n g _

theorem avgN_idem (hm : (Fintype.card (K ⧸ N) : k) ≠ 0)
    (z : groupHomology (Rep.res N.subtype A) n) : avgN N A n (avgN N A n z) = avgN N A n z := by
  refine (iso_hom_bijective (eN N A n)).1 ?_
  rw [eN_avgN N A n, eN_avgN N A n]
  exact avgH_idem N (YA A) n hm _

end Alg

end TernaryPeriodPolynomials.Argument.GroupHomology
