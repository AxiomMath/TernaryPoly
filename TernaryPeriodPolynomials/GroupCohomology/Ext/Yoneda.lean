module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
public import Mathlib.Algebra.Module.Submodule.EqLocus
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions.ComposableArrows
public import Mathlib.Data.Fintype.Shrink
public import Mathlib.Data.List.Enum
public import Mathlib.Data.String.Defs
public import Mathlib.GroupTheory.QuotientGroup.Finite
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
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr

@[expose] public section


/-!
# `Ext¹` and extensions: what the paper uses

The paper defines `Ext¹_H(V, M)` as equivalence classes of extensions `0 → M → X → V → 0`.  Every use of the Ext language in the proof of
`prop:alternating-even` (announced at the paper: "the extension is not automatic", "signs ... kill the extension obstruction") is the following
argument.  Apply `Hom_{K†}(-, E)` to `0 → St† → St → Q₀ → 0`.  A functional `f : St† → E` extends to `St` exactly when the **obstruction**
`δf ∈ Ext¹(Q₀, E)` vanishes; `δf` is the class of the *pushout extension* `0 → E → (E ⊕ St)/St† → Q₀ → 0`; and a class of an extension is zero exactly when the extension
splits.  So the property of the Yoneda description that is used is:

1. **the class of an extension is zero iff the extension splits** (`extClass_eq_zero_iff_split`);
2. **the class of the pushout extension of `0 → X₁ → X₂ → X₃ → 0` along `f : X₁ → E` is `δf`, and `f` extends over `X₂` iff this class is zero iff the pushout extension splits**
   (`extends_iff_obstruction_eq_zero`, `extends_iff_split_of_morphism`);
3. (not used by the paper's argument, but part of the definition) the class depends only on the equivalence class of the extension (`Extension.cls_eq_of_equiv`); the converse and the
   surjectivity (the full Yoneda bijection, `extensionClassEquiv`) are in `ExtYonedaPushout`.

Here `Ext` is Mathlib's `Ext` of the abelian category (`HasExt`), `extClass` the class of a short exact sequence.  This file works in an arbitrary abelian category with `Ext`;
`ExtYonedaPushout` constructs the pushout extension in `Rep ℚ G` and proves the Yoneda bijection.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Identities.ExtYoneda

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- An extension `0 → X₁ → X₂ → X₃ → 0` *splits* when `X₂ → X₃` has a section. -/
def Splits (S : ShortComplex C) : Prop := ∃ s : S.X₃ ⟶ S.X₂, s ≫ S.g = 𝟙 S.X₃

/-- **The class of an extension is zero iff the extension splits.** -/
theorem extClass_eq_zero_iff_split {S : ShortComplex C} (hS : S.ShortExact) :
    hS.extClass = 0 ↔ Splits S := by
  constructor
  · intro h
    obtain ⟨x₂, hx₂⟩ := Ext.covariant_sequence_exact₃ S.X₃ hS (Ext.mk₀ (𝟙 S.X₃)) (n₁ := 1) rfl
      (by rw [Ext.mk₀_id_comp, h])
    obtain ⟨s, rfl⟩ := (Ext.mk₀_bijective S.X₃ S.X₂).surjective x₂
    refine ⟨s, ?_⟩
    apply (Ext.mk₀_bijective S.X₃ S.X₃).injective
    rw [← hx₂, Ext.mk₀_comp_mk₀]
  · rintro ⟨s, hs⟩
    calc hS.extClass = (Ext.mk₀ (𝟙 S.X₃)).comp hS.extClass (zero_add 1) := (Ext.mk₀_id_comp _).symm
      _ = (Ext.mk₀ (s ≫ S.g)).comp hS.extClass (zero_add 1) := by rw [hs]
      _ = 0 := by
        rw [← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero]
        simp

/-- An extension `0 → E → X → V → 0` of `V` by `E` (the paper's objects of `Ext¹(V, E)`). -/
structure Extension (V E : C) where
  X : C
  j : E ⟶ X
  q : X ⟶ V
  w : j ≫ q = 0
  exact : (ShortComplex.mk j q w).ShortExact

namespace Extension

variable {V E : C}

/-- The underlying short complex. -/
def sc (T : Extension V E) : ShortComplex C := ShortComplex.mk T.j T.q T.w

/-- The class of an extension in `Ext¹(V, E)`. -/
def cls (T : Extension V E) : Ext V E 1 := T.exact.extClass

/-- **Equivalence of extensions**: a morphism of the middle terms compatible with the inclusion of `E` and the projection to `V`
(it is automatically an isomorphism, by the five lemma: `Equiv.symm`). -/
def Equiv (T T' : Extension V E) : Prop := ∃ φ : T.X ⟶ T'.X, T.j ≫ φ = T'.j ∧ φ ≫ T'.q = T.q

omit [HasExt.{w} C] in
theorem Equiv.refl (T : Extension V E) : T.Equiv T := ⟨𝟙 _, by simp, by simp⟩

omit [HasExt.{w} C] in
theorem Equiv.symm {T T' : Extension V E} (h : T.Equiv T') : T'.Equiv T := by
  obtain ⟨φ, h1, h2⟩ := h
  let m : T.sc ⟶ T'.sc := ⟨𝟙 E, φ, 𝟙 V, by dsimp [sc]; simpa using h1.symm, by dsimp [sc]; simpa using h2⟩
  have h1' : IsIso m.τ₁ := inferInstanceAs (IsIso (𝟙 E))
  have h3' : IsIso m.τ₃ := inferInstanceAs (IsIso (𝟙 V))
  have : IsIso φ := ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ m T.exact T'.exact
  refine ⟨inv φ, ?_, ?_⟩
  · rw [IsIso.comp_inv_eq]; exact h1.symm
  · rw [IsIso.inv_comp_eq]; exact h2.symm

omit [HasExt.{w} C] in
theorem Equiv.trans {T T' T'' : Extension V E} (h : T.Equiv T') (h' : T'.Equiv T'') : T.Equiv T'' := by
  obtain ⟨φ, h1, h2⟩ := h
  obtain ⟨ψ, h1', h2'⟩ := h'
  exact ⟨φ ≫ ψ, by rw [← Category.assoc, h1, h1'], by rw [Category.assoc, h2', h2]⟩

/-- **The class of an extension depends only on its equivalence class.** -/
theorem cls_eq_of_equiv {T T' : Extension V E} (h : T.Equiv T') : T.cls = T'.cls := by
  obtain ⟨φ, h1, h2⟩ := h
  let m : T.sc ⟶ T'.sc := ⟨𝟙 E, φ, 𝟙 V, by dsimp [sc]; simpa using h1.symm, by dsimp [sc]; simpa using h2⟩
  have := ShortComplex.ShortExact.extClass_naturality T.exact T'.exact m
  simpa [cls, m] using this

/-- **The class of an extension is zero iff it splits**. -/
theorem cls_eq_zero_iff (T : Extension V E) : T.cls = 0 ↔ Splits T.sc := extClass_eq_zero_iff_split T.exact

end Extension

/-- **The obstruction** `δf = [S]·f ∈ Ext¹(X₃, E)` to extending `f : X₁ → E` over `S.f : X₁ → X₂`:
the connecting map of the long exact sequence for `Hom(-, E)`. -/
def obstruction {S : ShortComplex C} (hS : S.ShortExact) {E : C} (f : S.X₁ ⟶ E) : Ext S.X₃ E 1 :=
  hS.extClass.comp (Ext.mk₀ f) (add_zero 1)

/-- **A functional extends iff its obstruction vanishes** (the exactness of `Hom(X₂,E) → Hom(X₁,E) → Ext¹(X₃,E)`). -/
theorem extends_iff_obstruction_eq_zero {S : ShortComplex C} (hS : S.ShortExact) {E : C} (f : S.X₁ ⟶ E) :
    (∃ F : S.X₂ ⟶ E, S.f ≫ F = f) ↔ obstruction hS f = 0 := by
  constructor
  · rintro ⟨F, rfl⟩
    unfold obstruction
    rw [← Ext.mk₀_comp_mk₀]
    exact hS.extClass_comp_assoc (Ext.mk₀ F)
  · intro h
    obtain ⟨x₂, hx₂⟩ := Ext.contravariant_sequence_exact₁ hS E (Ext.mk₀ f) (n₁ := 1) (by rfl) h
    obtain ⟨F, rfl⟩ := (Ext.mk₀_bijective S.X₂ E).surjective x₂
    refine ⟨F, ?_⟩
    apply (Ext.mk₀_bijective S.X₁ E).injective
    rw [← hx₂, Ext.mk₀_comp_mk₀]

/-- **The obstruction is the class of any extension receiving a morphism from `S` that is `f` on the sub and the identity on the quotient**
(in particular of the pushout extension, `ExtYonedaPushout`). -/
theorem obstruction_eq_cls {S : ShortComplex C} (hS : S.ShortExact) {E : C} (T : Extension S.X₃ E)
    (φ : S ⟶ T.sc) (h3 : φ.τ₃ = 𝟙 S.X₃) : obstruction hS φ.τ₁ = T.cls := by
  have := ShortComplex.ShortExact.extClass_naturality hS T.exact φ
  rw [h3, Ext.mk₀_id_comp] at this
  exact this

/-- **The paper's sentence**: `f` extends over `X₂` iff the extension `0 → E → X → X₃ → 0` obtained from `S` by `f` splits, i.e. iff its class in `Ext¹(X₃, E)` vanishes. -/
theorem extends_iff_split_of_morphism {S : ShortComplex C} (hS : S.ShortExact) {E : C} (T : Extension S.X₃ E)
    (φ : S ⟶ T.sc) (h3 : φ.τ₃ = 𝟙 S.X₃) :
    (∃ F : S.X₂ ⟶ E, S.f ≫ F = φ.τ₁) ↔ Splits T.sc := by
  refine (extends_iff_obstruction_eq_zero hS φ.τ₁).trans ?_
  rw [obstruction_eq_cls hS T φ h3]
  exact T.cls_eq_zero_iff

end TernaryPeriodPolynomials.Argument.Identities.ExtYoneda
