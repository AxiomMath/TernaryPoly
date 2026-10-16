module

public import Mathlib.RepresentationTheory.Homological.GroupHomology.Basic
public import Mathlib.Algebra.Homology.ConcreteCategory
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Abelian.Ext
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
# Semilinear actions of an ambient group on representations of a normal subgroup

For a normal subgroup `H` of `G`, an `H`-representation `X` may carry a compatible action of `G`
(`GAct`): this is the structure of the restriction `Rep.res H.subtype V` of a `G`-representation `V`,
and also of every `H`-complex obtained from a `G`-complex.  `conjHom` is the induced conjugation
action on `H`-equivariant homomorphisms, `hcAct` its action on the `Hom`-cochain complex
`Hom_H(D, W)` of a chain complex `D` of `H`-representations (a chain map, hence an action on
cohomology `hcohAct`).  On the chain side, `Cyc` packages cycles as elements, `Cyc.cls` is the
homology class, `Cyc.cls_eq_iff` the boundary criterion, `delta_cycAct` the equivariance of the
connecting homomorphism, and `GActC.transport` moves an action along an isomorphism of complexes.
This is the common twisted-chain layer used to prove that isomorphisms built from `Hom`-cochains
and connecting homomorphisms are equivariant for the finite quotient `G/H`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GroupHomology

open CategoryTheory


section Cycles

variable {Γ : Type} [Group Γ]

/-- A cycle of degree `k + 1` of a chain complex, as an element annihilated by the differential. -/
def Cyc (D : ChainComplex (Rep.{0} ℚ Γ) ℕ) (k : ℕ) : Type :=
  {x : D.X (k + 1) // D.d (k + 1) k x = 0}

/-- The image of a cycle under a chain map. -/
def Cyc.map {D D' : ChainComplex (Rep.{0} ℚ Γ) ℕ} (f : D ⟶ D') {k : ℕ} (z : Cyc D k) : Cyc D' k :=
  ⟨f.f (k + 1) z.1, by
    have h := congrArg (fun m => m z.1) (f.comm (k + 1) k)
    change D'.d (k + 1) k (f.f (k + 1) z.1) = f.f k (D.d (k + 1) k z.1) at h
    rw [h, z.2, map_zero]⟩

end Cycles

section Basic

variable {G : Type} [Group G] (H : Subgroup G) [H.Normal]

theorem conj_mem' (g : G) (h : ↥H) : g * h.1 * g⁻¹ ∈ H :=
  Subgroup.Normal.conj_mem inferInstance h.1 h.2 g

/-- The conjugate `g h g⁻¹ ∈ H` of an element `h ∈ H`. -/
def conjElt (g : G) (h : ↥H) : ↥H := ⟨g * h.1 * g⁻¹, conj_mem' H g h⟩

@[simp] theorem conjElt_val (g : G) (h : ↥H) : (conjElt H g h).1 = g * h.1 * g⁻¹ := rfl

/-- A `G`-semilinear action on an `H`-representation `X`: `g (h x) = (g h g⁻¹) (g x)`. -/
structure GAct (X : Rep.{0} ℚ ↥H) where
  /-- The action of `G` on the underlying module. -/
  ρ : Representation ℚ G X
  /-- Compatibility with the `H`-action. -/
  conj : ∀ (g : G) (h : ↥H) (x : X), ρ g (X.ρ h x) = X.ρ (conjElt H g h) (ρ g x)

/-- The restriction of a `G`-representation carries the tautological `G`-action. -/
def GAct.ofRep (V : Rep.{0} ℚ G) : GAct H (Rep.res H.subtype V) where
  ρ := V.ρ
  conj g h x := by
    change V.ρ g (V.ρ h.1 x) = V.ρ (g * h.1 * g⁻¹) (V.ρ g x)
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    simp [mul_assoc]

variable {H}

omit [H.Normal] in
theorem rep_hom_ext' {X Y : Rep.{0} ℚ ↥H} {φ ψ : X ⟶ Y} (h : ∀ x : X, φ.hom x = ψ.hom x) :
    φ = ψ := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  exact LinearMap.ext h

/-- Conjugation by `g ∈ G` on `H`-equivariant homomorphisms: `φ ↦ ρ_W(g) ∘ φ ∘ ρ_X(g)⁻¹`. -/
def conjHom {X W : Rep.{0} ℚ ↥H} (A : GAct H X) (B : GAct H W) (g : G) (φ : X ⟶ W) : X ⟶ W :=
  Rep.ofHom ⟨(B.ρ g).comp (φ.hom.toLinearMap.comp (A.ρ g⁻¹)), fun h => LinearMap.ext fun x => by
    have h1 := A.conj g⁻¹ h x
    have h2 := Rep.hom_comm_apply φ (conjElt H g⁻¹ h) (A.ρ g⁻¹ x)
    have h3 := B.conj g (conjElt H g⁻¹ h) (φ.hom (A.ρ g⁻¹ x))
    have h4 : conjElt H g (conjElt H g⁻¹ h) = h := Subtype.ext (by simp [mul_assoc])
    rw [h4] at h3
    change B.ρ g (φ.hom (A.ρ g⁻¹ (X.ρ h x))) = W.ρ h (B.ρ g (φ.hom (A.ρ g⁻¹ x)))
    rw [h1, h2, h3]⟩

@[simp] theorem conjHom_apply {X W : Rep.{0} ℚ ↥H} (A : GAct H X) (B : GAct H W) (g : G)
    (φ : X ⟶ W) (x : X) : (conjHom A B g φ).hom x = B.ρ g (φ.hom (A.ρ g⁻¹ x)) := rfl

theorem conjHom_one {X W : Rep.{0} ℚ ↥H} (A : GAct H X) (B : GAct H W) (φ : X ⟶ W) :
    conjHom A B 1 φ = φ := by
  apply rep_hom_ext'
  intro x
  simp [conjHom_apply]

theorem conjHom_mul {X W : Rep.{0} ℚ ↥H} (A : GAct H X) (B : GAct H W) (g h : G) (φ : X ⟶ W) :
    conjHom A B (g * h) φ = conjHom A B g (conjHom A B h φ) := by
  apply rep_hom_ext'
  intro x
  simp only [conjHom_apply]
  rw [map_mul, mul_inv_rev, map_mul]
  rfl

theorem conjHom_add {X W : Rep.{0} ℚ ↥H} (A : GAct H X) (B : GAct H W) (g : G) (φ ψ : X ⟶ W) :
    conjHom A B g (φ + ψ) = conjHom A B g φ + conjHom A B g ψ := by
  apply rep_hom_ext'
  intro x
  change B.ρ g (φ.hom (A.ρ g⁻¹ x) + ψ.hom (A.ρ g⁻¹ x)) = _
  rw [map_add]
  rfl

theorem conjHom_smul {X W : Rep.{0} ℚ ↥H} (A : GAct H X) (B : GAct H W) (g : G) (c : ℚ)
    (φ : X ⟶ W) : conjHom A B g (c • φ) = c • conjHom A B g φ := by
  apply rep_hom_ext'
  intro x
  change B.ρ g (c • φ.hom (A.ρ g⁻¹ x)) = _
  rw [map_smul]
  rfl

/-- A morphism of `H`-representations commuting with the `G`-actions. -/
def IsGMor {X Y : Rep.{0} ℚ ↥H} (A : GAct H X) (B : GAct H Y) (f : X ⟶ Y) : Prop :=
  ∀ (g : G) (x : X), f.hom (A.ρ g x) = B.ρ g (f.hom x)

theorem IsGMor.id {X : Rep.{0} ℚ ↥H} (A : GAct H X) : IsGMor A A (𝟙 X) := fun _ _ => rfl

theorem IsGMor.comp {X Y Z : Rep.{0} ℚ ↥H} {A : GAct H X} {B : GAct H Y} {C : GAct H Z}
    {f : X ⟶ Y} {f' : Y ⟶ Z} (hf : IsGMor A B f) (hf' : IsGMor B C f') : IsGMor A C (f ≫ f') :=
  fun g x => by
    change f'.hom (f.hom (A.ρ g x)) = C.ρ g (f'.hom (f.hom x))
    rw [hf g x, hf' g]

/-- Precomposing with a `G`-morphism commutes with conjugation. -/
theorem conjHom_comp_left {X' X W : Rep.{0} ℚ ↥H} {A' : GAct H X'} {A : GAct H X}
    (B : GAct H W) {f : X' ⟶ X} (hf : IsGMor A' A f) (g : G) (φ : X ⟶ W) :
    conjHom A' B g (f ≫ φ) = f ≫ conjHom A B g φ := by
  apply rep_hom_ext'
  intro x
  change B.ρ g (φ.hom (f.hom (A'.ρ g⁻¹ x))) = B.ρ g (φ.hom (A.ρ g⁻¹ (f.hom x)))
  rw [hf]

/-- Postcomposing with a `G`-morphism commutes with conjugation. -/
theorem conjHom_comp_right {X W W' : Rep.{0} ℚ ↥H} (A : GAct H X) {B : GAct H W} {B' : GAct H W'}
    {f : W ⟶ W'} (hf : IsGMor B B' f) (g : G) (φ : X ⟶ W) :
    conjHom A B' g (φ ≫ f) = conjHom A B g φ ≫ f := by
  apply rep_hom_ext'
  intro x
  change B'.ρ g (f.hom (φ.hom (A.ρ g⁻¹ x))) = f.hom (B.ρ g (φ.hom (A.ρ g⁻¹ x)))
  rw [hf]

/-- `conjHom` as a `ℚ`-linear endomorphism of `X ⟶ W`. -/
def conjHomL {X W : Rep.{0} ℚ ↥H} (A : GAct H X) (B : GAct H W) (g : G) :
    (X ⟶ W) →ₗ[ℚ] (X ⟶ W) where
  toFun := conjHom A B g
  map_add' := conjHom_add A B g
  map_smul' := conjHom_smul A B g

/-- A `G`-semilinear action on every term of a chain complex of `H`-representations, commuting
with the differentials. -/
structure GActC (D : ChainComplex (Rep.{0} ℚ ↥H) ℕ) where
  /-- The action on the degree `n` term. -/
  act : ∀ n, GAct H (D.X n)
  /-- The differentials are `G`-equivariant. -/
  comm : ∀ (g : G) (n m : ℕ) (x : D.X n),
    (D.d n m).hom ((act n).ρ g x) = (act m).ρ g ((D.d n m).hom x)

/-- The tautological action on the restriction of a complex of `G`-representations. -/
def GActC.ofChain (H : Subgroup G) [H.Normal] (C : ChainComplex (Rep.{0} ℚ G) ℕ) :
    GActC (((Rep.resFunctor H.subtype).mapHomologicalComplex (ComplexShape.down ℕ)).obj C) where
  act n := GAct.ofRep H (C.X n)
  comm g n m x := Rep.hom_comm_apply (C.d n m) g x

theorem GActC.isGMor_d {D : ChainComplex (Rep.{0} ℚ ↥H) ℕ} (A : GActC D) (n m : ℕ) :
    IsGMor (A.act n) (A.act m) (D.d n m) := fun g x => A.comm g n m x


/-- The action of `g` on cycles. -/
def GActC.cycAct {D : ChainComplex (Rep.{0} ℚ ↥H) ℕ} (A : GActC D) (g : G) {k : ℕ} (z : Cyc D k) :
    Cyc D k :=
  ⟨(A.act (k + 1)).ρ g z.1, by rw [A.comm, z.2, map_zero]⟩

/-- A chain map commuting with the `G`-actions. -/
def IsGMorC {D D' : ChainComplex (Rep.{0} ℚ ↥H) ℕ} (A : GActC D) (A' : GActC D')
    (f : D ⟶ D') : Prop :=
  ∀ n, IsGMor (A.act n) (A'.act n) (f.f n)

theorem IsGMorC.id {D : ChainComplex (Rep.{0} ℚ ↥H) ℕ} (A : GActC D) : IsGMorC A A (𝟙 D) :=
  fun n => IsGMor.id (A.act n)

theorem IsGMorC.comp {D D' D'' : ChainComplex (Rep.{0} ℚ ↥H) ℕ} {A : GActC D} {A' : GActC D'}
    {A'' : GActC D''} {f : D ⟶ D'} {f' : D' ⟶ D''} (hf : IsGMorC A A' f) (hf' : IsGMorC A' A'' f') :
    IsGMorC A A'' (f ≫ f') := fun n => (hf n).comp (hf' n)

theorem IsGMorC.map_cycAct {D D' : ChainComplex (Rep.{0} ℚ ↥H) ℕ} {A : GActC D} {A' : GActC D'}
    {f : D ⟶ D'} (hf : IsGMorC A A' f) (g : G) {k : ℕ} (z : Cyc D k) :
    Cyc.map f (A.cycAct g z) = A'.cycAct g (Cyc.map f z) :=
  Subtype.ext (hf (k + 1) g z.1)

/-- The restriction of a chain map of `G`-complexes is `G`-equivariant for the tautological actions. -/
theorem GActC.isGMorC_ofChain (H : Subgroup G) [H.Normal] {C C' : ChainComplex (Rep.{0} ℚ G) ℕ}
    (f : C ⟶ C') :
    IsGMorC (GActC.ofChain H C) (GActC.ofChain H C')
      (((Rep.resFunctor H.subtype).mapHomologicalComplex (ComplexShape.down ℕ)).map f) :=
  fun n g x => Rep.hom_comm_apply (f.f n) g x

/-- The conjugation action of `g ∈ G` on the `Hom`-cochain complex `Hom_H(D, W)` is a cochain map. -/
def hcAct {D : ChainComplex (Rep.{0} ℚ ↥H) ℕ} {W : Rep.{0} ℚ ↥H} (A : GActC D) (B : GAct H W)
    (g : G) : D.linearYonedaObj ℚ W ⟶ D.linearYonedaObj ℚ W where
  f n := ModuleCat.ofHom (conjHomL (A.act n) B g)
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    exact (conjHom_comp_left B (A.isGMor_d j i) g φ).symm

theorem hcAct_f_apply {D : ChainComplex (Rep.{0} ℚ ↥H) ℕ} {W : Rep.{0} ℚ ↥H} (A : GActC D)
    (B : GAct H W) (g : G) (n : ℕ) (φ : D.X n ⟶ W) :
    (hcAct A B g).f n φ = conjHom (A.act n) B g φ := rfl

theorem hcAct_one {D : ChainComplex (Rep.{0} ℚ ↥H) ℕ} {W : Rep.{0} ℚ ↥H} (A : GActC D)
    (B : GAct H W) : hcAct A B 1 = 𝟙 _ := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  exact conjHom_one (A.act n) B φ

theorem hcAct_mul {D : ChainComplex (Rep.{0} ℚ ↥H) ℕ} {W : Rep.{0} ℚ ↥H} (A : GActC D)
    (B : GAct H W) (g h : G) : hcAct A B (g * h) = hcAct A B h ≫ hcAct A B g := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  exact conjHom_mul (A.act n) B g h φ

/-- The action of `g ∈ G` on the `n`-th cohomology of `Hom_H(D, W)`. -/
def hcohAct {D : ChainComplex (Rep.{0} ℚ ↥H) ℕ} {W : Rep.{0} ℚ ↥H} (A : GActC D)
    (B : GAct H W) (g : G) (n : ℕ) :
    (D.linearYonedaObj ℚ W).homology n ⟶ (D.linearYonedaObj ℚ W).homology n :=
  HomologicalComplex.homologyMap (hcAct A B g) n

end Basic


section Concrete

variable {Γ : Type} [Group Γ]

local instance : HasForget₂ (Rep.{0} ℚ Γ) Ab.{0} :=
  HasForget₂.trans (Rep ℚ Γ) (ModuleCat ℚ) Ab
local instance : (forget₂ (Rep.{0} ℚ Γ) Ab.{0}).Additive :=
  inferInstanceAs ((forget₂ (Rep ℚ Γ) (ModuleCat ℚ) ⋙ forget₂ (ModuleCat ℚ) Ab).Additive)
local instance : (forget₂ (Rep.{0} ℚ Γ) Ab.{0}).PreservesHomology :=
  inferInstanceAs ((forget₂ (Rep ℚ Γ) (ModuleCat ℚ) ⋙ forget₂ (ModuleCat ℚ) Ab).PreservesHomology)

variable (D : ChainComplex (Rep.{0} ℚ Γ) ℕ)

/-- The cycle of `D` in degree `k + 1` given by an element annihilated by the differential. -/
def cycMk (k : ℕ) (x : D.X (k + 1)) (hx : D.d (k + 1) k x = 0) : D.cycles (k + 1) :=
  (D.sc (k + 1)).cyclesMk x (by
    change D.d (k + 1) ((ComplexShape.down ℕ).next (k + 1)) x = 0
    rw [(ComplexShape.down ℕ).next_eq' (show (ComplexShape.down ℕ).Rel (k + 1) k from rfl)]
    exact hx)

theorem iCycles_cycMk (k : ℕ) (x : D.X (k + 1)) (hx : D.d (k + 1) k x = 0) :
    (D.iCycles (k + 1)) (cycMk D k x hx) = x :=
  (D.sc (k + 1)).i_cyclesMk _ _

theorem d_iCycles_apply (k : ℕ) (c : D.cycles (k + 1)) :
    D.d (k + 1) k ((D.iCycles (k + 1)) c) = 0 := by
  have h := congrArg (fun f => f c) (D.iCycles_d (k + 1) k)
  exact h

theorem cycMk_iCycles (k : ℕ) (c : D.cycles (k + 1)) :
    cycMk D k ((D.iCycles (k + 1)) c) (d_iCycles_apply D k c) = c := by
  apply (Preadditive.mono_iff_injective' (D.iCycles (k + 1))).mp inferInstance
  exact iCycles_cycMk D k _ _

theorem homologyπ_surjective (n : ℕ) : Function.Surjective (D.homologyπ n) :=
  (Preadditive.epi_iff_surjective' (D.homologyπ n)).mp inferInstance

/-- The homology class of an element of `D.X (k+1)` annihilated by the differential. -/
def clsAt (k : ℕ) (x : D.X (k + 1)) (hx : D.d (k + 1) k x = 0) : D.homology (k + 1) :=
  D.homologyπ (k + 1) (cycMk D k x hx)

theorem exists_clsAt (k : ℕ) (h : D.homology (k + 1)) :
    ∃ (x : D.X (k + 1)) (hx : D.d (k + 1) k x = 0), clsAt D k x hx = h := by
  obtain ⟨c, rfl⟩ := homologyπ_surjective D (k + 1) h
  exact ⟨D.iCycles (k + 1) c, d_iCycles_apply D k c, by
    unfold clsAt; rw [cycMk_iCycles]⟩

/-- Two cycles have the same class iff they differ by a boundary. -/
theorem clsAt_eq_iff (k : ℕ) (x y : D.X (k + 1)) (hx : D.d (k + 1) k x = 0)
    (hy : D.d (k + 1) k y = 0) :
    clsAt D k x hx = clsAt D k y hy ↔ ∃ b : D.X (k + 2), D.d (k + 2) (k + 1) b = x - y := by
  have hprev : (ComplexShape.down ℕ).prev (k + 1) = k + 2 :=
    (ComplexShape.down ℕ).prev_eq' (show (ComplexShape.down ℕ).Rel (k + 2) (k + 1) from rfl)
  have hex : (ShortComplex.mk (D.toCycles (k + 2) (k + 1)) (D.homologyπ (k + 1))
      (D.toCycles_comp_homologyπ (k + 2) (k + 1))).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ (D.homologyIsCokernel (k + 2) (k + 1) hprev)
  have hi : ∀ b : D.X (k + 2), (D.iCycles (k + 1)) (D.toCycles (k + 2) (k + 1) b) =
      D.d (k + 2) (k + 1) b := fun b => by
    have h := congrArg (fun f => f b) (D.toCycles_i (k + 2) (k + 1))
    exact h
  constructor
  · intro h
    have h0 : D.homologyπ (k + 1) (cycMk D k x hx - cycMk D k y hy) = 0 := by
      rw [map_sub]
      exact sub_eq_zero.mpr h
    obtain ⟨b, hb⟩ := (ShortComplex.exact_iff_of_hasForget _).mp hex _ h0
    have hb' : D.toCycles (k + 2) (k + 1) b = cycMk D k x hx - cycMk D k y hy := hb
    refine ⟨b, ?_⟩
    rw [← hi b, hb', map_sub, iCycles_cycMk, iCycles_cycMk]
  · rintro ⟨b, hb⟩
    have h1 : cycMk D k x hx = cycMk D k y hy + D.toCycles (k + 2) (k + 1) b := by
      apply (Preadditive.mono_iff_injective' (D.iCycles (k + 1))).mp inferInstance
      rw [map_add, iCycles_cycMk, iCycles_cycMk, hi b, hb]
      abel
    unfold clsAt
    rw [h1, map_add]
    have h2 : D.homologyπ (k + 1) (D.toCycles (k + 2) (k + 1) b) = 0 := by
      have h := congrArg (fun f => f b) (D.toCycles_comp_homologyπ (k + 2) (k + 1))
      exact h
    rw [h2, add_zero]

theorem cyclesMap_cycMk {D D' : ChainComplex (Rep.{0} ℚ Γ) ℕ} (f : D ⟶ D') (k : ℕ)
    (x : D.X (k + 1)) (hx : D.d (k + 1) k x = 0) (hfx : D'.d (k + 1) k (f.f (k + 1) x) = 0) :
    HomologicalComplex.cyclesMap f (k + 1) (cycMk D k x hx) = cycMk D' k (f.f (k + 1) x) hfx := by
  apply (Preadditive.mono_iff_injective' (D'.iCycles (k + 1))).mp inferInstance
  have h := congrArg (fun m => m (cycMk D k x hx)) (HomologicalComplex.cyclesMap_i f (k + 1))
  change (D'.iCycles (k + 1)) (HomologicalComplex.cyclesMap f (k + 1) (cycMk D k x hx)) =
    (f.f (k + 1)) ((D.iCycles (k + 1)) (cycMk D k x hx)) at h
  rw [h, iCycles_cycMk, iCycles_cycMk]

/-- Homology classes of cycles are natural for chain maps. -/
theorem clsAt_map {D D' : ChainComplex (Rep.{0} ℚ Γ) ℕ} (f : D ⟶ D') (k : ℕ)
    (x : D.X (k + 1)) (hx : D.d (k + 1) k x = 0) (hfx : D'.d (k + 1) k (f.f (k + 1) x) = 0) :
    HomologicalComplex.homologyMap f (k + 1) (clsAt D k x hx) = clsAt D' k (f.f (k + 1) x) hfx := by
  have h := congrArg (fun m => m (cycMk D k x hx)) (HomologicalComplex.homologyπ_naturality f (k + 1))
  unfold clsAt
  change (HomologicalComplex.homologyMap f (k + 1)) (D.homologyπ (k + 1) (cycMk D k x hx)) =
    D'.homologyπ (k + 1) (cycMk D' k (f.f (k + 1) x) hfx)
  have h' : D'.homologyπ (k + 1) (HomologicalComplex.cyclesMap f (k + 1) (cycMk D k x hx)) =
      (HomologicalComplex.homologyMap f (k + 1)) (D.homologyπ (k + 1) (cycMk D k x hx)) := h.symm
  rw [← h', cyclesMap_cycMk f k x hx hfx]

theorem cycMk_add (k : ℕ) (x y : D.X (k + 1)) (hx : D.d (k + 1) k x = 0)
    (hy : D.d (k + 1) k y = 0) (hxy : D.d (k + 1) k (x + y) = 0) :
    cycMk D k (x + y) hxy = cycMk D k x hx + cycMk D k y hy := by
  apply (Preadditive.mono_iff_injective' (D.iCycles (k + 1))).mp inferInstance
  rw [map_add, iCycles_cycMk, iCycles_cycMk, iCycles_cycMk]

theorem clsAt_add (k : ℕ) (x y : D.X (k + 1)) (hx : D.d (k + 1) k x = 0)
    (hy : D.d (k + 1) k y = 0) (hxy : D.d (k + 1) k (x + y) = 0) :
    clsAt D k (x + y) hxy = clsAt D k x hx + clsAt D k y hy := by
  unfold clsAt
  rw [cycMk_add D k x y hx hy hxy, map_add]


/-- The homology class of a cycle. -/
def Cyc.cls {D : ChainComplex (Rep.{0} ℚ Γ) ℕ} {k : ℕ} (z : Cyc D k) : D.homology (k + 1) :=
  clsAt D k z.1 z.2

theorem Cyc.exists_cls {D : ChainComplex (Rep.{0} ℚ Γ) ℕ} {k : ℕ} (h : D.homology (k + 1)) :
    ∃ z : Cyc D k, z.cls = h := by
  obtain ⟨x, hx, rfl⟩ := exists_clsAt D k h
  exact ⟨⟨x, hx⟩, rfl⟩

theorem Cyc.cls_eq_iff {D : ChainComplex (Rep.{0} ℚ Γ) ℕ} {k : ℕ} (z z' : Cyc D k) :
    z.cls = z'.cls ↔ ∃ b : D.X (k + 2), D.d (k + 2) (k + 1) b = z.1 - z'.1 :=
  clsAt_eq_iff D k z.1 z'.1 z.2 z'.2

theorem Cyc.cls_map {D D' : ChainComplex (Rep.{0} ℚ Γ) ℕ} (f : D ⟶ D') {k : ℕ} (z : Cyc D k) :
    HomologicalComplex.homologyMap f (k + 1) z.cls = (Cyc.map f z).cls :=
  clsAt_map f k z.1 z.2 _


/-- Existence of the lifts computing the connecting homomorphism on a cycle. -/
theorem exists_delta_rep {S : ShortComplex (ChainComplex (Rep.{0} ℚ Γ) ℕ)} (hS : S.ShortExact)
    (k : ℕ) (z₃ : Cyc S.X₃ (k + 1)) :
    ∃ (x₂ : S.X₂.X (k + 2)) (z₁ : Cyc S.X₁ k), S.g.f (k + 2) x₂ = z₃.1 ∧
      S.f.f (k + 1) z₁.1 = S.X₂.d (k + 2) (k + 1) x₂ := by
  have hdeg := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS
  obtain ⟨x₂, hx₂⟩ := (ShortComplex.ShortExact.surjective_g (hdeg (k + 2))) z₃.1
  have hx₂' : S.g.f (k + 2) x₂ = z₃.1 := hx₂
  have hgd : S.g.f (k + 1) (S.X₂.d (k + 2) (k + 1) x₂) = 0 := by
    have h := congrArg (fun m => m x₂) (S.g.comm (k + 2) (k + 1))
    change S.X₃.d (k + 2) (k + 1) (S.g.f (k + 2) x₂) = S.g.f (k + 1) (S.X₂.d (k + 2) (k + 1) x₂) at h
    rw [← h, hx₂', z₃.2]
  obtain ⟨x₁, hx₁⟩ := (ShortComplex.exact_iff_of_hasForget _).mp (hdeg (k + 1)).exact
    (S.X₂.d (k + 2) (k + 1) x₂) hgd
  have hx₁' : S.f.f (k + 1) x₁ = S.X₂.d (k + 2) (k + 1) x₂ := hx₁
  refine ⟨x₂, ⟨x₁, ?_⟩, hx₂', hx₁'⟩
  apply (Preadditive.mono_iff_injective' (S.f.f k)).mp (hdeg k).mono_f
  have h := congrArg (fun m => m x₁) (S.f.comm (k + 1) k)
  change S.X₂.d (k + 1) k (S.f.f (k + 1) x₁) = S.f.f k (S.X₁.d (k + 1) k x₁) at h
  rw [← h, hx₁']
  have h2 := congrArg (fun m => m x₂) (S.X₂.d_comp_d (k + 2) (k + 1) k)
  change S.X₂.d (k + 1) k (S.X₂.d (k + 2) (k + 1) x₂) = 0 at h2
  rw [h2, map_zero]

/-- Elementwise connecting homomorphism: if `x₃ ∈ X₃,k+2` is a cycle, `x₂ ∈ X₂,k+2` lifts it and
`d x₂ = f x₁`, then `δ [x₃] = [x₁]`. -/
theorem delta_clsAt {S : ShortComplex (ChainComplex (Rep.{0} ℚ Γ) ℕ)} (hS : S.ShortExact) (k : ℕ)
    (x₃ : S.X₃.X (k + 2)) (hx₃ : S.X₃.d (k + 2) (k + 1) x₃ = 0)
    (x₂ : S.X₂.X (k + 2)) (hx₂ : S.g.f (k + 2) x₂ = x₃)
    (x₁ : S.X₁.X (k + 1)) (hx₁ : S.f.f (k + 1) x₁ = S.X₂.d (k + 2) (k + 1) x₂)
    (hx₁' : S.X₁.d (k + 1) k x₁ = 0) :
    hS.δ (k + 2) (k + 1) rfl (clsAt S.X₃ (k + 1) x₃ hx₃) = clsAt S.X₁ k x₁ hx₁' := by
  have h := hS.δ_apply (k + 2) (k + 1) rfl x₃ hx₃ x₂ hx₂ x₁ hx₁ k
    ((ComplexShape.down ℕ).next_eq' (show (ComplexShape.down ℕ).Rel (k + 1) k from rfl))
  exact h

end Concrete



section Transport

variable {G : Type} [Group G] {H : Subgroup G} [H.Normal]

theorem rep_hom_inv_apply {Γ : Type} [Group Γ] {X Y : Rep.{0} ℚ Γ} (e : X ≅ Y) (y : Y) :
    e.hom.hom (e.inv.hom y) = y :=
  congrArg (fun f => f.hom y) e.inv_hom_id

theorem rep_inv_hom_apply {Γ : Type} [Group Γ] {X Y : Rep.{0} ℚ Γ} (e : X ≅ Y) (x : X) :
    e.inv.hom (e.hom.hom x) = x :=
  congrArg (fun f => f.hom x) e.hom_inv_id

/-- Transport of a `G`-action along an isomorphism of `H`-representations. -/
def GAct.transport {X Y : Rep.{0} ℚ ↥H} (A : GAct H X) (e : X ≅ Y) : GAct H Y where
  ρ :=
    { toFun := fun g => e.hom.hom.toLinearMap ∘ₗ A.ρ g ∘ₗ e.inv.hom.toLinearMap
      map_one' := by
        apply LinearMap.ext
        intro y
        change e.hom.hom (A.ρ 1 (e.inv.hom y)) = y
        rw [map_one]
        exact rep_hom_inv_apply e y
      map_mul' := fun g h => by
        apply LinearMap.ext
        intro y
        change e.hom.hom (A.ρ (g * h) (e.inv.hom y)) =
          e.hom.hom (A.ρ g (e.inv.hom (e.hom.hom (A.ρ h (e.inv.hom y)))))
        rw [rep_inv_hom_apply e, map_mul]
        rfl }
  conj g h y := by
    change e.hom.hom (A.ρ g (e.inv.hom (Y.ρ h y))) =
      Y.ρ (conjElt H g h) (e.hom.hom (A.ρ g (e.inv.hom y)))
    rw [Rep.hom_comm_apply e.inv h y, A.conj, Rep.hom_comm_apply e.hom]

theorem GAct.transport_apply {X Y : Rep.{0} ℚ ↥H} (A : GAct H X) (e : X ≅ Y) (g : G) (y : Y) :
    (A.transport e).ρ g y = e.hom.hom (A.ρ g (e.inv.hom y)) := rfl

/-- Transport of a `G`-action on a chain complex along an isomorphism of complexes. -/
def GActC.transport {D D' : ChainComplex (Rep.{0} ℚ ↥H) ℕ} (A : GActC D) (e : D ≅ D') :
    GActC D' where
  act n := (A.act n).transport ((HomologicalComplex.eval _ _ n).mapIso e)
  comm g n m y := by
    have h1 : ∀ x, (D'.d n m).hom ((e.hom.f n).hom x) = (e.hom.f m).hom ((D.d n m).hom x) :=
      fun x => congrArg (fun f => f.hom x) (e.hom.comm n m)
    have h2 : ∀ y, (D.d n m).hom ((e.inv.f n).hom y) = (e.inv.f m).hom ((D'.d n m).hom y) :=
      fun y => congrArg (fun f => f.hom y) (e.inv.comm n m)
    change (D'.d n m).hom ((e.hom.f n).hom ((A.act n).ρ g ((e.inv.f n).hom y))) =
      (e.hom.f m).hom ((A.act m).ρ g ((e.inv.f m).hom ((D'.d n m).hom y)))
    rw [h1, ← h2 y, A.comm]

/-- The transported structure makes the isomorphism equivariant. -/
theorem GActC.isGMorC_transport_hom {D D' : ChainComplex (Rep.{0} ℚ ↥H) ℕ} (A : GActC D)
    (e : D ≅ D') : IsGMorC A (A.transport e) e.hom := fun n g x => by
  have h : (e.inv.f n).hom ((e.hom.f n).hom x) = x :=
    rep_inv_hom_apply ((HomologicalComplex.eval _ _ n).mapIso e) x
  change (e.hom.f n).hom ((A.act n).ρ g x) =
    (e.hom.f n).hom ((A.act n).ρ g ((e.inv.f n).hom ((e.hom.f n).hom x)))
  rw [h]

/-- The inverse isomorphism is equivariant for the transported structure. -/
theorem GActC.isGMorC_transport_inv {D D' : ChainComplex (Rep.{0} ℚ ↥H) ℕ} (A : GActC D)
    (e : D ≅ D') : IsGMorC (A.transport e) A e.inv := fun n g y => by
  have h : (e.inv.f n).hom ((e.hom.f n).hom ((A.act n).ρ g ((e.inv.f n).hom y))) =
      (A.act n).ρ g ((e.inv.f n).hom y) :=
    rep_inv_hom_apply ((HomologicalComplex.eval _ _ n).mapIso e) _
  exact h

end Transport

section Equivariance

variable {G : Type} [Group G] {H : Subgroup G} [H.Normal]

/-- **Equivariance of the connecting homomorphism on cycle classes.**  If the three terms of a
short exact sequence of complexes carry compatible `G`-actions, the connecting homomorphism
sends the class of `ρ(g) z₃` to the class of `ρ(g) z₁`, where `z₁` represents `δ [z₃]`. -/
theorem delta_cycAct {S : ShortComplex (ChainComplex (Rep.{0} ℚ ↥H) ℕ)} (hS : S.ShortExact)
    {A₁ : GActC S.X₁} {A₂ : GActC S.X₂} {A₃ : GActC S.X₃} (hf : IsGMorC A₁ A₂ S.f)
    (hg : IsGMorC A₂ A₃ S.g) (g : G) (k : ℕ) (z₃ : Cyc S.X₃ (k + 1)) :
    ∃ z₁ : Cyc S.X₁ k, hS.δ (k + 2) (k + 1) rfl z₃.cls = z₁.cls ∧
      hS.δ (k + 2) (k + 1) rfl (A₃.cycAct g z₃).cls = (A₁.cycAct g z₁).cls := by
  obtain ⟨x₂, z₁, hx₂, hz₁⟩ := exists_delta_rep hS k z₃
  refine ⟨z₁, delta_clsAt hS k z₃.1 z₃.2 x₂ hx₂ z₁.1 hz₁ z₁.2, ?_⟩
  have hx₂' : S.g.f (k + 2) ((A₂.act (k + 2)).ρ g x₂) = (A₃.cycAct g z₃).1 := by
    change _ = (A₃.act (k + 2)).ρ g z₃.1
    rw [hg (k + 2) g x₂, hx₂]
  have hz₁' : S.f.f (k + 1) (A₁.cycAct g z₁).1 =
      S.X₂.d (k + 2) (k + 1) ((A₂.act (k + 2)).ρ g x₂) := by
    change S.f.f (k + 1) ((A₁.act (k + 1)).ρ g z₁.1) = _
    rw [hf (k + 1) g z₁.1, hz₁, A₂.comm]
  exact delta_clsAt hS k _ (A₃.cycAct g z₃).2 _ hx₂' _ hz₁' (A₁.cycAct g z₁).2

end Equivariance

end TernaryPeriodPolynomials.Argument.GroupHomology
