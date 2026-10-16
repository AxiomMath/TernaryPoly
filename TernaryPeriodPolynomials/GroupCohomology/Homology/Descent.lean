module

public import Mathlib.RepresentationTheory.Homological.GroupHomology.Basic
public import Mathlib.RepresentationTheory.Homological.GroupHomology.Shapiro
public import Mathlib.GroupTheory.Index
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.Algebra.Homology.ShortComplex.Linear
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Units.Opposite
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import Mathlib.Data.List.Enum
public import Mathlib.Data.String.Defs
public import Mathlib.GroupTheory.Perm.Option
public import Mathlib.Lean.Elab.InfoTree
public import Mathlib.Lean.Elab.Tactic.Basic
public import Mathlib.Lean.Elab.Tactic.Meta
public import Mathlib.Lean.Expr.ExtraRecognizers
public import Mathlib.Lean.Expr.Rat
public import Mathlib.Lean.GoalsLocation
public import Mathlib.Lean.MessageData.Trace
public import Mathlib.Lean.Meta
public import Mathlib.Lean.Meta.Basic
public import Mathlib.Lean.Meta.KAbstractPositions
public import Mathlib.Lean.Meta.Tactic.Rewrite
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.Order.Fin.SuccAboveOrderIso
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr

@[expose] public section


/-!
# Coinvariants of a normal finite index subgroup: the descent splitting

For a normal subgroup `N ⊲ K` of finite index (with `[K : N]` invertible in the field `k`) and a
`k`-linear representation `V` of `K`, the quotient `q : V_N → V_K`, the action
`γ_g : V_N → V_N` of `g ∈ K` (Mathlib's `toCoinvariants`) and the transfer-like map
`t : V_K → V_N`, `⟦v⟧ ↦ [K:N]⁻¹ ∑_{x ∈ K/N} ⟦x v⟧`, are natural in `V` and satisfy
`t ≫ q = 𝟙`, `q ≫ t = [K:N]⁻¹ ∑_x γ_x`, `γ_g ≫ q = q`.  Applied to a chain complex `Y` of
representations of `K`, this gives on homology: `Hₙ(Y_N) → Hₙ(Y_K)` is surjective, its kernel is
the kernel of the averaging endomorphism `avgH`, `avgH` is idempotent, and `Hₙ(q) ∘ Hₙ(γ_g) = Hₙ(q)`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

universe u

namespace TernaryPeriodPolynomials.Argument.GroupHomology

open CategoryTheory Representation Representation.Coinvariants

variable {k K : Type*} [Field k] [Group K] (N : Subgroup K) [N.Normal]
  {V : Type*} [AddCommGroup V] [Module k V] (ρ : Representation k K V)

/-- The quotient `V_N → V_K`. -/
def qMap : Coinvariants (ρ.comp N.subtype) →ₗ[k] Coinvariants ρ :=
  Coinvariants.lift _ (Coinvariants.mk ρ) fun n => LinearMap.ext fun v =>
    (Coinvariants.mk_self_apply ρ n.1 v)

omit [N.Normal] in
@[simp] theorem qMap_mk (v : V) : qMap N ρ (Coinvariants.mk _ v) = Coinvariants.mk ρ v := rfl

/-- The action of `g ∈ K` on `V_N`. -/
def gamMap (g : K) : Coinvariants (ρ.comp N.subtype) →ₗ[k] Coinvariants (ρ.comp N.subtype) :=
  toCoinvariants ρ N g

@[simp] theorem gamMap_mk (g : K) (v : V) :
    gamMap N ρ g (Coinvariants.mk _ v) = Coinvariants.mk _ (ρ g v) := rfl

theorem gamMap_of_mem (n : N) : gamMap N ρ n.1 = LinearMap.id := by
  ext v
  exact (Coinvariants.mk_self_apply (ρ.comp N.subtype) n v)

theorem gamMap_mul (g h : K) : gamMap N ρ (g * h) = gamMap N ρ g ∘ₗ gamMap N ρ h := by
  ext v
  simp [gamMap]

theorem qMap_comp_gamMap (g : K) : qMap N ρ ∘ₗ gamMap N ρ g = qMap N ρ := by
  ext v
  simp


section Transfer

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

variable [N.FiniteIndex]

omit [N.FiniteIndex] in
theorem gamMap_out (g : K) : gamMap N ρ (g : K ⧸ N).out = gamMap N ρ g := by
  obtain ⟨n, hn⟩ := QuotientGroup.mk_out_eq_mul N g
  rw [hn, gamMap_mul, gamMap_of_mem]
  ext v
  rfl

/-- The sum over coset representatives, landing in `V_N`. -/
def tSum : V →ₗ[k] Coinvariants (ρ.comp N.subtype) :=
  ∑ x : K ⧸ N, gamMap N ρ x.out ∘ₗ Coinvariants.mk _

theorem tSum_apply (v : V) :
    tSum N ρ v = ∑ x : K ⧸ N, Coinvariants.mk _ (ρ x.out v) := by
  simp [tSum]

theorem tSum_invariant (h : K) (v : V) : tSum N ρ (ρ h v) = tSum N ρ v := by
  simp only [tSum, LinearMap.sum_apply, LinearMap.comp_apply]
  have key : ∀ x : K ⧸ N, gamMap N ρ x.out (Coinvariants.mk _ (ρ h v)) =
      gamMap N ρ (x * (h : K ⧸ N)).out (Coinvariants.mk _ v) := by
    intro x
    have e : (x * (h : K ⧸ N)) = ((x.out * h : K) : K ⧸ N) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.out_eq']
    rw [e, gamMap_out, gamMap_mul]
    simp [gamMap]
  simp only [key]
  exact Equiv.sum_comp (Equiv.mulRight (h : K ⧸ N)) (fun y => gamMap N ρ y.out (Coinvariants.mk _ v))


/-- The transfer-like map `V_K → V_N` (scaled by `c`). -/
def tMap (c : k) : Coinvariants ρ →ₗ[k] Coinvariants (ρ.comp N.subtype) :=
  Coinvariants.lift ρ (c • tSum N ρ) fun h => LinearMap.ext fun v => by
    simp [tSum_invariant]

theorem tMap_mk (c : k) (v : V) : tMap N ρ c (Coinvariants.mk ρ v) = c • tSum N ρ v := rfl

/-- The averaging idempotent on `V_N`, scaled by `c`. -/
def eMap (c : k) : Coinvariants (ρ.comp N.subtype) →ₗ[k] Coinvariants (ρ.comp N.subtype) :=
  c • ∑ x : K ⧸ N, gamMap N ρ x.out

theorem qMap_tMap (hm : (Fintype.card (K ⧸ N) : k) ≠ 0) :
    qMap N ρ ∘ₗ tMap N ρ ((Fintype.card (K ⧸ N) : k)⁻¹) = LinearMap.id := by
  ext v
  simp only [LinearMap.comp_apply, tMap_mk, tSum_apply, map_smul, map_sum, qMap_mk,
    Coinvariants.mk_self_apply, Finset.sum_const, Finset.card_univ, LinearMap.id_comp]
  rw [← Nat.cast_smul_eq_nsmul k, smul_smul, inv_mul_cancel₀ hm, one_smul]

theorem tMap_qMap (c : k) : tMap N ρ c ∘ₗ qMap N ρ = eMap N ρ c := by
  ext v
  simp [tMap_mk, tSum_apply, eMap]

end Transfer

section Functors

variable {k K : Type u} [Field k] [Group K] (N : Subgroup K) [N.Normal]

/-- `P ↦ (Res_N P)_N`. -/
def cN : Rep.{u} k K ⥤ ModuleCat.{u} k :=
  Rep.resFunctor N.subtype ⋙ Rep.coinvariantsFunctor k N

/-- `P ↦ P_K`. -/
def cK : Rep.{u} k K ⥤ ModuleCat.{u} k := Rep.coinvariantsFunctor k K

instance : (cN (k := k) N).Additive := by unfold cN; infer_instance

instance : (cK (k := k) (K := K)).Additive := by unfold cK; infer_instance

omit [N.Normal] in
theorem cN_map_mk {P Q : Rep.{u} k K} (f : P ⟶ Q) (v : P) :
    (cN N).map f (Coinvariants.mk _ v) = Coinvariants.mk _ (f.hom v) := rfl

theorem cK_map_mk {P Q : Rep.{u} k K} (f : P ⟶ Q) (v : P) :
    (cK (k := k) (K := K)).map f (Coinvariants.mk _ v) = Coinvariants.mk _ (f.hom v) := rfl

/-- The quotient natural transformation `cN ⟶ cK`. -/
def qNat : cN (k := k) N ⟶ cK where
  app P := ModuleCat.ofHom (qMap N P.ρ)
  naturality _ _ _ := ModuleCat.hom_ext (Coinvariants.hom_ext (LinearMap.ext fun _ => rfl))

/-- The action of `g` on `cN`. -/
def gamNat (g : K) : cN (k := k) N ⟶ cN N where
  app P := ModuleCat.ofHom (gamMap N P.ρ g)
  naturality P Q f := ModuleCat.hom_ext (Coinvariants.hom_ext (LinearMap.ext fun v => by
    have h : f.hom (P.ρ g (v : P.V)) = Q.ρ g (f.hom (v : P.V)) :=
      Rep.hom_comm_apply f g (v : P.V)
    exact congrArg (Coinvariants.mk (Q.ρ.comp N.subtype)) h.symm))

section FunctorsT

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

variable [N.FiniteIndex]

/-- The transfer-like natural transformation `cK ⟶ cN` (scaled by `c`). -/
def tNat (c : k) : cK (k := k) (K := K) ⟶ cN N where
  app P := ModuleCat.ofHom (tMap N P.ρ c)
  naturality P Q f := ModuleCat.hom_ext (Coinvariants.hom_ext (LinearMap.ext fun v => by
    change tMap N Q.ρ c (Coinvariants.mk _ (f.hom v)) = _
    rw [tMap_mk, tSum_apply]
    change _ = Coinvariants.map _ _ _ (tMap N P.ρ c (Coinvariants.mk _ v))
    rw [tMap_mk, tSum_apply]
    simp only [map_smul, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    exact congrArg (Coinvariants.mk (Q.ρ.comp N.subtype)) (Rep.hom_comm_apply f x.out v).symm))

theorem tNat_qNat (hm : (Fintype.card (K ⧸ N) : k) ≠ 0) (P : Rep.{u} k K) :
    (tNat N ((Fintype.card (K ⧸ N) : k)⁻¹)).app P ≫ (qNat N).app P = 𝟙 _ :=
  ModuleCat.hom_ext (qMap_tMap N P.ρ hm)

theorem qNat_tNat (c : k) (P : Rep.{u} k K) :
    (qNat N).app P ≫ (tNat N c).app P = ModuleCat.ofHom (eMap N P.ρ c) :=
  ModuleCat.hom_ext (tMap_qMap N P.ρ c)

end FunctorsT

end Functors


section HomologyLinear

variable {R' : Type*} [Semiring R'] {C : Type*} [Category* C] [Preadditive C] [Linear R' C]
  [CategoryWithHomology C] {ι : Type*} {c : ComplexShape ι} {K L : HomologicalComplex C c}

theorem homologyMap_smul' (r : R') (φ : K ⟶ L) (i : ι) :
    HomologicalComplex.homologyMap (r • φ) i = r • HomologicalComplex.homologyMap φ i := by
  have h : (HomologicalComplex.shortComplexFunctor C c i).map (r • φ) =
      r • (HomologicalComplex.shortComplexFunctor C c i).map φ := by
    ext <;> rfl
  unfold HomologicalComplex.homologyMap
  rw [h, ShortComplex.homologyMap_smul]
  rfl


theorem homologyMap_sum' {ι' : Type*} {K L : HomologicalComplex C c} (s : Finset ι') (f : ι' → (K ⟶ L))
    (i : ι) :
    HomologicalComplex.homologyMap (∑ x ∈ s, f x) i = ∑ x ∈ s, HomologicalComplex.homologyMap (f x) i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, HomologicalComplex.homologyMap_add, ih]

end HomologyLinear

open HomologicalComplex
section SplitHomology

variable {k : Type u} [Field k] {C D : ChainComplex (ModuleCat.{u} k) ℕ}
  (Q : C ⟶ D) (T : D ⟶ C) (h : T ≫ Q = 𝟙 D) (n : ℕ)

include h in
theorem homologyMap_split_apply (x : D.homology n) :
    (homologyMap Q n).hom ((homologyMap T n).hom x) = x := by
  have h1 : homologyMap T n ≫ homologyMap Q n = 𝟙 _ := by
    rw [← homologyMap_comp, h, homologyMap_id]
  exact LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp h1) x

include h in
theorem homologyMap_surjective_of_split : Function.Surjective (homologyMap Q n).hom :=
  fun x => ⟨_, homologyMap_split_apply Q T h n x⟩

include h in
theorem homologyMap_injective_of_split : Function.Injective (homologyMap T n).hom :=
  fun x y hxy => by
    rw [← homologyMap_split_apply Q T h n x, ← homologyMap_split_apply Q T h n y, hxy]

include h in
theorem homologyMap_ker_eq (z : C.homology n) :
    (homologyMap Q n).hom z = 0 ↔ (homologyMap T n).hom ((homologyMap Q n).hom z) = 0 := by
  constructor
  · intro hz; rw [hz, map_zero]
  · intro hz
    rw [← homologyMap_split_apply Q T h n ((homologyMap Q n).hom z), hz]
    exact map_zero _

end SplitHomology

section ComplexLevel

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

variable {k K : Type u} [Field k] [Group K] (N : Subgroup K) [N.Normal] [N.FiniteIndex]
  (Y : ChainComplex (Rep.{u} k K) ℕ)

omit [N.FiniteIndex] in
/-- The `N`-coinvariant complex. -/
abbrev CxN : ChainComplex (ModuleCat.{u} k) ℕ := ((cN (k := k) N).mapHomologicalComplex _).obj Y

omit [N.FiniteIndex] in
/-- The `K`-coinvariant complex. -/
abbrev CxK : ChainComplex (ModuleCat.{u} k) ℕ := ((cK (k := k) (K := K)).mapHomologicalComplex _).obj Y

omit [N.FiniteIndex] in
/-- The quotient chain map. -/
def QY : CxN N Y ⟶ CxK Y := (NatTrans.mapHomologicalComplex (qNat (k := k) N) _).app Y

/-- The transfer-like chain map. -/
def TY (c : k) : CxK Y ⟶ CxN N Y := (NatTrans.mapHomologicalComplex (tNat (k := k) N c) _).app Y

omit [N.FiniteIndex] in
/-- The action of `g` on the `N`-coinvariant complex. -/
def GY (g : K) : CxN N Y ⟶ CxN N Y := (NatTrans.mapHomologicalComplex (gamNat (k := k) N g) _).app Y

omit [N.Normal] [N.FiniteIndex] in
theorem sum_f {ι : Type*} (s : Finset ι) (f : ι → (CxN N Y ⟶ CxN N Y)) (i : ℕ) :
    (∑ x ∈ s, f x).f i = ∑ x ∈ s, (f x).f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih, HomologicalComplex.add_f_apply]

theorem TY_QY (hm : (Fintype.card (K ⧸ N) : k) ≠ 0) :
    TY N Y ((Fintype.card (K ⧸ N) : k)⁻¹) ≫ QY N Y = 𝟙 _ :=
  HomologicalComplex.hom_ext _ _ fun i => tNat_qNat N hm (Y.X i)

omit [N.FiniteIndex] in
theorem GY_QY (g : K) : GY N Y g ≫ QY N Y = QY N Y :=
  HomologicalComplex.hom_ext _ _ fun i => ModuleCat.hom_ext (qMap_comp_gamMap N (Y.X i).ρ g)

omit [N.Normal] [N.FiniteIndex] in
theorem hom_smul_sum_ofHom {A : Type u} [AddCommGroup A] [Module k A] {ι : Type*} (g : ι → A →ₗ[k] A)
    (s : Finset ι) (c : k) :
    (c • ∑ x ∈ s, ModuleCat.ofHom (g x) : ModuleCat.of k A ⟶ ModuleCat.of k A).hom =
      c • ∑ x ∈ s, g x := by
  rw [ModuleCat.hom_smul, ModuleCat.hom_sum]
  rfl

theorem QY_TY (c : k) :
    QY N Y ≫ TY N Y c = c • ∑ x : K ⧸ N, GY N Y x.out := by
  refine HomologicalComplex.hom_ext _ _ fun i => ?_
  rw [HomologicalComplex.smul_f_apply, sum_f]
  refine ModuleCat.hom_ext (Coinvariants.hom_ext (LinearMap.ext fun v => ?_))
  have key := hom_smul_sum_ofHom (k := k) (fun x : K ⧸ N => gamMap N (Y.X i).ρ x.out) Finset.univ c
  simp only [QY, TY, GY, gamNat, qNat, tNat, NatTrans.mapHomologicalComplex_app_f]
  refine Eq.trans ?_ (congrArg (fun F => (F ∘ₗ Coinvariants.mk (MonoidHom.comp (Y.X i).ρ N.subtype)) v)
    key).symm
  change tMap N (Y.X i).ρ c (qMap N (Y.X i).ρ (Coinvariants.mk _ v)) =
    (c • ∑ x : K ⧸ N, gamMap N (Y.X i).ρ x.out) (Coinvariants.mk _ v)
  simp [tMap_mk, tSum_apply, LinearMap.sum_apply]

section HomologyLevel

variable (n : ℕ)

/-- The averaging endomorphism of `Hₙ` of the `N`-coinvariant complex. -/
def avgH : (CxN N Y).homology n →ₗ[k] (CxN N Y).homology n :=
  ((Fintype.card (K ⧸ N) : k)⁻¹) • ∑ x : K ⧸ N, (homologyMap (GY N Y x.out) n).hom

theorem avgH_eq :
    avgH N Y n = (homologyMap (TY N Y ((Fintype.card (K ⧸ N) : k)⁻¹)) n).hom ∘ₗ
      (homologyMap (QY N Y) n).hom := by
  have h := congrArg (fun f => homologyMap f n) (QY_TY N Y ((Fintype.card (K ⧸ N) : k)⁻¹))
  simp only [homologyMap_comp, homologyMap_smul', homologyMap_sum'] at h
  have h2 := congrArg ModuleCat.Hom.hom h
  rw [ModuleCat.hom_smul, ModuleCat.hom_sum] at h2
  exact h2.symm

theorem descent_surjective (hm : (Fintype.card (K ⧸ N) : k) ≠ 0) :
    Function.Surjective (homologyMap (QY N Y) n).hom :=
  homologyMap_surjective_of_split _ _ (TY_QY N Y hm) n

theorem descent_ker (hm : (Fintype.card (K ⧸ N) : k) ≠ 0) (z : (CxN N Y).homology n) :
    (homologyMap (QY N Y) n).hom z = 0 ↔ avgH N Y n z = 0 := by
  rw [avgH_eq]
  constructor
  · intro h
    change (homologyMap (TY N Y _) n).hom ((homologyMap (QY N Y) n).hom z) = 0
    rw [h, map_zero]
  · intro h
    have hinj := homologyMap_injective_of_split _ _ (TY_QY N Y hm) n
    exact hinj (by rw [map_zero]; exact h)

omit [N.FiniteIndex] in
theorem descent_gam (g : K) (z : (CxN N Y).homology n) :
    (homologyMap (QY N Y) n).hom ((homologyMap (GY N Y g) n).hom z) =
      (homologyMap (QY N Y) n).hom z := by
  have h := congrArg (fun f => homologyMap f n) (GY_QY N Y g)
  simp only [homologyMap_comp] at h
  exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h) z

theorem avgH_idem (hm : (Fintype.card (K ⧸ N) : k) ≠ 0) (z : (CxN N Y).homology n) :
    avgH N Y n (avgH N Y n z) = avgH N Y n z := by
  rw [avgH_eq]
  change (homologyMap (TY N Y _) n).hom ((homologyMap (QY N Y) n).hom
    ((homologyMap (TY N Y _) n).hom ((homologyMap (QY N Y) n).hom z))) = _
  rw [homologyMap_split_apply _ _ (TY_QY N Y hm) n]
  rfl

end HomologyLevel

end ComplexLevel

end TernaryPeriodPolynomials.Argument.GroupHomology
