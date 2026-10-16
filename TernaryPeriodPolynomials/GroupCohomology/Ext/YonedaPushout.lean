module

public import TernaryPeriodPolynomials.GroupCohomology.Ext.Yoneda
public import Mathlib.RepresentationTheory.Rep.Iso
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
public import Mathlib.Algebra.Group.Units.Opposite
public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import Mathlib.GroupTheory.Perm.Option
public import Mathlib.Order.Fin.SuccAboveOrderIso
public import Mathlib.RingTheory.Finiteness.Lattice

@[expose] public section


/-!
# The pushout extension in `Rep ℚ G`, and surjectivity of the class map

For a short exact sequence `S : 0 → X₁ → X₂ → X₃ → 0` of rational representations and `f : X₁ → E`, the **pushout extension** is
`0 → E → (E ⊕ X₂)/{(f x, -ι x)} → X₃ → 0` (`pushoutExtension`).  It receives a morphism from `S` which is `f` on the sub and the identity on the quotient (`pushoutHom`),
hence (`ExtYoneda.obstruction_eq_cls`) its class is the obstruction `δf ∈ Ext¹(X₃, E)`, and `f` extends over `X₂` iff the pushout extension splits (`extends_iff_pushout_splits`):
this is the sentence of the paper.  Since `Rep ℚ G` has enough projectives, every class of `Ext¹(V, E)` is the class of an extension (`exists_extension_with_class`), and extensions of the same class are equivalent
(`equiv_of_cls_eq`: lift a projective cover, correct the lifts by the difference of the two obstructions, compare with the pushout via its universal property `pushDesc`).  So the
**Yoneda bijection** `{extensions of V by E}/≃ ≃ Ext¹(V, E)` holds for Mathlib's `Ext` in `Rep ℚ G` (`extensionClassEquiv`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Identities.ExtYoneda

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

variable {G : Type} [Group G]

/-- Forgetting the action reflects exactness: kernel/range equality suffices. -/
theorem rep_exact_of_range_eq_ker (S : ShortComplex (Rep.{0} ℚ G))
    (h : S.f.hom.toLinearMap.range = S.g.hom.toLinearMap.ker) : S.Exact := by
  apply (forget₂ (Rep.{0} ℚ G) (ModuleCat ℚ)).reflects_exact_of_faithful S
  apply (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr
  exact h

section Pushout

variable (S : ShortComplex (Rep.{0} ℚ G)) {E : Rep.{0} ℚ G} (f : S.X₁ ⟶ E)

/-- The relation submodule `{(f x, -ι x)} ⊆ E × X₂`. -/
def pushSub : Submodule ℚ (E × S.X₂) :=
  LinearMap.range ((f.hom.toLinearMap).prod (-(S.f.hom.toLinearMap)))

theorem pushSub_invariant (g : G) :
    pushSub S f ≤ (pushSub S f).comap ((E.ρ.prod S.X₂.ρ) g) := by
  rintro _ ⟨x, rfl⟩
  refine ⟨S.X₁.ρ g x, ?_⟩
  have h1 := LinearMap.congr_fun (f.hom.isIntertwining' g) x
  have h2 := LinearMap.congr_fun (S.f.hom.isIntertwining' g) x
  change (f.hom.toLinearMap (S.X₁.ρ g x), -S.f.hom.toLinearMap (S.X₁.ρ g x)) =
    (E.ρ g (f.hom.toLinearMap x), S.X₂.ρ g (-S.f.hom.toLinearMap x))
  rw [map_neg]
  exact Prod.ext h1 (congrArg Neg.neg h2)

/-- The middle term `(E ⊕ X₂)/{(f x, -ι x)}` of the pushout extension. -/
def pushRep : Rep.{0} ℚ G :=
  Rep.of ((E.ρ.prod S.X₂.ρ).quotient (pushSub S f) (pushSub_invariant S f))

/-- The inclusion `E → (E ⊕ X₂)/~`. -/
def pushJ : E ⟶ pushRep S f :=
  Rep.ofHom ⟨(pushSub S f).mkQ ∘ₗ LinearMap.inl ℚ E S.X₂, fun g => by
    apply LinearMap.ext
    intro e
    change (pushSub S f).mkQ (E.ρ g e, 0) = (pushSub S f).mkQ ((E.ρ.prod S.X₂.ρ) g (e, 0))
    simp [Representation.prod]⟩

/-- The map `X₂ → (E ⊕ X₂)/~`. -/
def pushT : S.X₂ ⟶ pushRep S f :=
  Rep.ofHom ⟨(pushSub S f).mkQ ∘ₗ LinearMap.inr ℚ E S.X₂, fun g => by
    apply LinearMap.ext
    intro x
    change (pushSub S f).mkQ (0, S.X₂.ρ g x) = (pushSub S f).mkQ ((E.ρ.prod S.X₂.ρ) g (0, x))
    simp [Representation.prod]⟩

theorem range_eq_ker_of_shortExact (hS : S.ShortExact) :
    LinearMap.range S.f.hom.toLinearMap = LinearMap.ker S.g.hom.toLinearMap :=
  (hS.exact.map (forget₂ (Rep.{0} ℚ G) (ModuleCat ℚ))).moduleCat_range_eq_ker

/-- The projection `(E ⊕ X₂)/~ → X₃`, `[(e, x)] ↦ π x`. -/
def pushQ (hS : S.ShortExact) : pushRep S f ⟶ S.X₃ :=
  Rep.ofHom ⟨(pushSub S f).liftQ (S.g.hom.toLinearMap ∘ₗ LinearMap.snd ℚ E S.X₂) (by
      rintro _ ⟨x, rfl⟩
      have : S.f.hom.toLinearMap x ∈ LinearMap.ker S.g.hom.toLinearMap :=
        range_eq_ker_of_shortExact S hS ▸ ⟨x, rfl⟩
      simpa using this), fun g => by
    apply LinearMap.ext
    intro z
    obtain ⟨⟨e, x⟩, rfl⟩ := (pushSub S f).mkQ_surjective z
    change S.g.hom.toLinearMap (S.X₂.ρ g x) = S.X₃.ρ g (S.g.hom.toLinearMap x)
    exact LinearMap.congr_fun (S.g.hom.isIntertwining' g) x⟩

theorem pushQ_mk (hS : S.ShortExact) (e : E) (x : S.X₂) :
    (pushQ S f hS).hom.toLinearMap ((pushSub S f).mkQ (e, x)) = S.g.hom.toLinearMap x := rfl

theorem pushQ_pushJ (hS : S.ShortExact) (e : E) :
    (pushQ S f hS).hom.toLinearMap ((pushJ S f).hom.toLinearMap e) = 0 :=
  (pushQ_mk S f hS e 0).trans (map_zero _)

/-- **The pushout extension** `0 → E → (E ⊕ X₂)/{(f x, -ι x)} → X₃ → 0` of `S` along `f`. -/
def pushoutExtension (hS : S.ShortExact) : Extension S.X₃ E where
  X := pushRep S f
  j := pushJ S f
  q := pushQ S f hS
  w := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro e
    exact pushQ_pushJ S f hS e
  exact := by
    have hmono : Mono S.f := hS.mono_f
    have hepi : Epi S.g := hS.epi_g
    have hinj : Function.Injective S.f.hom.toLinearMap := (Rep.mono_iff_injective S.f).mp hmono
    have hsurj : Function.Surjective S.g.hom.toLinearMap := (Rep.epi_iff_surjective S.g).mp hepi
    have hrk := range_eq_ker_of_shortExact S hS
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · apply rep_exact_of_range_eq_ker
      ext z
      obtain ⟨⟨e, x⟩, rfl⟩ := (pushSub S f).mkQ_surjective z
      constructor
      · rintro ⟨e', he'⟩
        refine LinearMap.mem_ker.mpr ?_
        have he'' : (pushJ S f).hom.toLinearMap e' = (pushSub S f).mkQ (e, x) := he'
        rw [← he'']
        exact map_zero S.g.hom.toLinearMap
      · intro hz
        have hx : x ∈ LinearMap.ker S.g.hom.toLinearMap := hz
        rw [← hrk] at hx
        obtain ⟨y, hy⟩ := hx
        refine ⟨e + f.hom.toLinearMap y, ?_⟩
        change (pushSub S f).mkQ (e + f.hom.toLinearMap y, 0) = (pushSub S f).mkQ (e, x)
        rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
        refine ⟨y, ?_⟩
        change (f.hom.toLinearMap y, -S.f.hom.toLinearMap y) = (e + f.hom.toLinearMap y - e, 0 - x)
        rw [hy]
        exact Prod.ext (by simp) (by simp)
    · rw [Rep.mono_iff_injective]
      intro e₁ e₂ h
      change (pushSub S f).mkQ (e₁, 0) = (pushSub S f).mkQ (e₂, 0) at h
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at h
      obtain ⟨x, hx⟩ := h
      have h1 : f.hom.toLinearMap x = e₁ - e₂ := congrArg Prod.fst hx
      have h2 : -S.f.hom.toLinearMap x = (0 : S.X₂) - 0 := congrArg Prod.snd hx
      have h3 : S.f.hom.toLinearMap x = S.f.hom.toLinearMap 0 := by
        rw [map_zero]
        have : -S.f.hom.toLinearMap x = 0 := by rw [h2]; simp
        exact neg_eq_zero.mp this
      have h4 := hinj h3
      rw [h4, map_zero] at h1
      exact (sub_eq_zero.mp h1.symm)
    · rw [Rep.epi_iff_surjective]
      intro w
      obtain ⟨x, hx⟩ := hsurj w
      exact ⟨(pushSub S f).mkQ (0, x), (pushQ_mk S f hS 0 x).trans hx⟩

/-- **The morphism of extensions `S → pushout extension`**: `f` on the sub, the identity on the quotient. -/
def pushoutHom (hS : S.ShortExact) : S ⟶ (pushoutExtension S f hS).sc where
  τ₁ := f
  τ₂ := pushT S f
  τ₃ := 𝟙 S.X₃
  comm₁₂ := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    change (pushSub S f).mkQ (f.hom.toLinearMap x, 0) = (pushSub S f).mkQ (0, S.f.hom.toLinearMap x)
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    refine ⟨x, ?_⟩
    change (f.hom.toLinearMap x, -S.f.hom.toLinearMap x) = (f.hom.toLinearMap x - 0, 0 - S.f.hom.toLinearMap x)
    exact Prod.ext (by simp) (by simp)
  comm₂₃ := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    rfl

/-- **The obstruction `δf` is the class of the pushout extension.** -/
theorem obstruction_eq_pushout_cls [HasExt.{1} (Rep.{0} ℚ G)] (hS : S.ShortExact) :
    obstruction hS f = (pushoutExtension S f hS).cls :=
  obstruction_eq_cls hS (pushoutExtension S f hS) (pushoutHom S f hS) rfl

/-- **`f` extends over `X₂` iff the pushout extension splits**. -/
theorem extends_iff_pushout_splits [HasExt.{1} (Rep.{0} ℚ G)] (hS : S.ShortExact) :
    (∃ F : S.X₂ ⟶ E, S.f ≫ F = f) ↔ Splits (pushoutExtension S f hS).sc :=
  extends_iff_split_of_morphism hS (pushoutExtension S f hS) (pushoutHom S f hS) rfl

/-- **Universal property of the pushout extension.**  A target `X` with `j : E → X` and `lam : X₂ → X` such that `f ≫ j = ι ≫ lam` receives `[(e, x)] ↦ j e + lam x`. -/
def pushDesc (X : Rep.{0} ℚ G) (j : E ⟶ X) (lam : S.X₂ ⟶ X) (h : f ≫ j = S.f ≫ lam) : pushRep S f ⟶ X :=
  Rep.ofHom ⟨(pushSub S f).liftQ (j.hom.toLinearMap ∘ₗ LinearMap.fst ℚ E S.X₂ + lam.hom.toLinearMap ∘ₗ LinearMap.snd ℚ E S.X₂) (by
      rintro _ ⟨x, rfl⟩
      have hx : j.hom.toLinearMap (f.hom.toLinearMap x) = lam.hom.toLinearMap (S.f.hom.toLinearMap x) :=
        congrArg (fun m => m.hom.toLinearMap x) h
      change j.hom.toLinearMap (f.hom.toLinearMap x) + lam.hom.toLinearMap (-S.f.hom.toLinearMap x) = 0
      rw [map_neg, hx]
      exact add_neg_cancel _), fun g => by
    apply LinearMap.ext
    intro z
    obtain ⟨⟨e, x⟩, rfl⟩ := (pushSub S f).mkQ_surjective z
    change j.hom.toLinearMap (E.ρ g e) + lam.hom.toLinearMap (S.X₂.ρ g x) =
      X.ρ g (j.hom.toLinearMap e + lam.hom.toLinearMap x)
    rw [map_add (X.ρ g)]
    exact congrArg₂ (· + ·) (LinearMap.congr_fun (j.hom.isIntertwining' g) e)
      (LinearMap.congr_fun (lam.hom.isIntertwining' g) x)⟩

theorem pushDesc_mk (X : Rep.{0} ℚ G) (j : E ⟶ X) (lam : S.X₂ ⟶ X) (h : f ≫ j = S.f ≫ lam) (e : E) (x : S.X₂) :
    (pushDesc S f X j lam h).hom.toLinearMap ((pushSub S f).mkQ (e, x)) =
      j.hom.toLinearMap e + lam.hom.toLinearMap x := rfl

/-- **Any extension receiving a morphism from `S` (`f` on the sub, identity on the quotient) is equivalent to the pushout extension.** -/
theorem pushout_equiv (hS : S.ShortExact) (T : Extension S.X₃ E) (φ : S ⟶ T.sc) (h3 : φ.τ₃ = 𝟙 S.X₃) :
    (pushoutExtension S φ.τ₁ hS).Equiv T := by
  let lam : S.X₂ ⟶ T.X := φ.τ₂
  have hq : lam ≫ T.q = S.g := by
    have h' := φ.comm₂₃
    rw [h3] at h'
    exact h'.trans (Category.comp_id S.g)
  have hj : φ.τ₁ ≫ T.j = S.f ≫ lam := φ.comm₁₂
  refine ⟨pushDesc S φ.τ₁ T.X T.j lam hj, ?_, ?_⟩
  · apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro e
    change T.j.hom.toLinearMap e + lam.hom.toLinearMap 0 = T.j.hom.toLinearMap e
    rw [map_zero, add_zero]
  · apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro z
    obtain ⟨⟨e, x⟩, rfl⟩ := (pushSub S φ.τ₁).mkQ_surjective z
    have h1 : T.q.hom.toLinearMap (T.j.hom.toLinearMap e) = 0 :=
      congrArg (fun m => m.hom.toLinearMap e) T.w
    have h2 : T.q.hom.toLinearMap (lam.hom.toLinearMap x) = S.g.hom.toLinearMap x :=
      congrArg (fun m => m.hom.toLinearMap x) hq
    change T.q.hom.toLinearMap (T.j.hom.toLinearMap e + lam.hom.toLinearMap x) = S.g.hom.toLinearMap x
    rw [map_add, h1, h2, zero_add]

end Pushout

section Classes

variable [HasExt.{1} (Rep.{0} ℚ G)]

/-- **Every class of `Ext¹(V, E)` is the class of an extension** (surjectivity of the Yoneda map): by dimension shifting along a projective cover
`0 → K → P → V → 0` the class is `δf` for some `f : K → E`, and `δf` is the class of the pushout extension. -/
theorem exists_extension_with_class (V E : Rep.{0} ℚ G) (α : Ext V E 1) :
    ∃ T : Extension V E, T.cls = α := by
  let π := Projective.π V
  let S : ShortComplex (Rep.{0} ℚ G) := ShortComplex.mk (kernel.ι π) π (kernel.condition π)
  have hS : S.ShortExact := { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel S.g) }
  have hx : (Ext.mk₀ S.g).comp α (zero_add 1) = 0 := Ext.eq_zero_of_projective _
  obtain ⟨x₁, hx₁⟩ := Ext.contravariant_sequence_exact₃ hS E α hx (n₀ := 0) (by rfl)
  obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective S.X₁ E).surjective x₁
  refine ⟨pushoutExtension S f hS, ?_⟩
  rw [← obstruction_eq_pushout_cls]
  exact hx₁

/-- The class map from equivalence classes of extensions is onto `Ext¹`; it is well defined (`Extension.cls_eq_of_equiv`).  That it is also injective
(extensions of the same class are equivalent) is the remaining half of the Yoneda bijection and is not proved here. -/
theorem cls_surjective (V E : Rep.{0} ℚ G) : Function.Surjective (Extension.cls : Extension V E → Ext V E 1) :=
  fun α => exists_extension_with_class V E α

/-- **Extensions of the same class are equivalent**: the second half of the Yoneda bijection. -/
theorem equiv_of_cls_eq (V E : Rep.{0} ℚ G) (T T' : Extension V E) (h : T.cls = T'.cls) : T.Equiv T' := by
  let π := Projective.π V
  let S : ShortComplex (Rep.{0} ℚ G) := ShortComplex.mk (kernel.ι π) π (kernel.condition π)
  have hS : S.ShortExact := { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel S.g) }
  have lift : ∀ U : Extension V E, ∃ (f : S.X₁ ⟶ E) (lam : S.X₂ ⟶ U.X),
      f ≫ U.j = S.f ≫ lam ∧ lam ≫ U.q = S.g := by
    intro U
    have : Epi U.q := U.exact.epi_g
    have : Mono U.j := U.exact.mono_f
    let lam := Projective.factorThru S.g U.q
    have hl : lam ≫ U.q = S.g := Projective.factorThru_comp S.g U.q
    refine ⟨U.exact.exact.lift (S.f ≫ lam) (by rw [Category.assoc, hl]; exact S.zero), lam, ?_, hl⟩
    exact U.exact.exact.lift_f _ _
  obtain ⟨f, lam, h1, h2⟩ := lift T
  obtain ⟨f', lam', h1', h2'⟩ := lift T'
  let φ : S ⟶ T.sc := ⟨f, lam, 𝟙 S.X₃, h1, h2.trans (Category.comp_id S.g).symm⟩
  let φ' : S ⟶ T'.sc := ⟨f', lam', 𝟙 S.X₃, h1', h2'.trans (Category.comp_id S.g).symm⟩
  have e1 : obstruction hS f = T.cls := obstruction_eq_cls hS T φ rfl
  have e2 : obstruction hS f' = T'.cls := obstruction_eq_cls hS T' φ' rfl
  have hdiff : obstruction hS (f - f') = 0 := by
    unfold obstruction at e1 e2 ⊢
    rw [sub_eq_add_neg, Ext.mk₀_add, Ext.mk₀_neg, Ext.comp_add, Ext.comp_neg, e1, e2, h]
    exact add_neg_cancel _
  obtain ⟨hh, hhh⟩ := (extends_iff_obstruction_eq_zero hS (f - f')).mpr hdiff
  let lam'' : S.X₂ ⟶ T'.X := lam' + hh ≫ T'.j
  let φ'' : S ⟶ T'.sc := ⟨f, lam'', 𝟙 S.X₃, by
      change f ≫ T'.j = S.f ≫ (lam' + hh ≫ T'.j)
      rw [Preadditive.comp_add, ← h1', ← Category.assoc, hhh, Preadditive.sub_comp]
      abel, by
      change (lam' + hh ≫ T'.j) ≫ T'.q = S.g ≫ 𝟙 S.X₃
      rw [Preadditive.add_comp, h2', Category.assoc, T'.w, Limits.comp_zero, add_zero, Category.comp_id]⟩
  exact (pushout_equiv S hS T φ rfl).symm.trans (pushout_equiv S hS T' φ'' rfl)

/-- **The Yoneda bijection**: equivalence classes of extensions of `V` by `E` are in bijection with `Ext¹(V, E)`, via the class of the extension. -/
theorem cls_eq_iff_equiv (V E : Rep.{0} ℚ G) (T T' : Extension V E) : T.cls = T'.cls ↔ T.Equiv T' :=
  ⟨equiv_of_cls_eq V E T T', Extension.cls_eq_of_equiv⟩

/-- The setoid of equivalent extensions. -/
def Extension.setoid (V E : Rep.{0} ℚ G) : Setoid (Extension V E) where
  r := Extension.Equiv
  iseqv := ⟨Extension.Equiv.refl, Extension.Equiv.symm, Extension.Equiv.trans⟩

/-- **`Ext¹(V, E)` is the set of equivalence classes of extensions**: the class map is a bijection from `{extensions}/≃` onto Mathlib's `Ext¹`. -/
def extensionClassEquiv (V E : Rep.{0} ℚ G) : Quotient (Extension.setoid V E) ≃ Ext V E 1 :=
  Equiv.ofBijective (Quotient.lift Extension.cls (fun _ _ h => Extension.cls_eq_of_equiv h))
    ⟨by
      intro a b hab
      induction a using Quotient.inductionOn
      induction b using Quotient.inductionOn
      exact Quotient.sound ((cls_eq_iff_equiv V E _ _).mp hab),
     by
      intro α
      obtain ⟨T, hT⟩ := exists_extension_with_class V E α
      exact ⟨Quotient.mk _ T, hT⟩⟩

end Classes

end TernaryPeriodPolynomials.Argument.Identities.ExtYoneda
