module

public import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality
public import Mathlib.RepresentationTheory.Homological.GroupHomology.Shapiro
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import Mathlib.Data.List.Enum
public import Mathlib.Data.String.Defs
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
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.Order.Fin.SuccAboveOrderIso
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr

@[expose] public section


/-!
# Functoriality of the bar resolution and naturality of `groupHomologyIso`

* `barTerm`, `barMap`: for a group homomorphism `f : G₁ →* G₂` the chain map
  `bar(G₁) ⟶ Res_f bar(G₂)`, `(g₁, …, gₙ) ↦ (f g₁, …, f gₙ)`, over the identity of `k`; it is
  compatible with the augmentations for a subgroup inclusion (`barMap_pi`), via the explicit formula
  `barPi_f_zero` for the augmentation of the bar resolution.
* `groupHomologyIso_bar_hom`: Mathlib's `groupHomologyIso` for the bar resolution is the homology map
  of `inhomogeneousChainsIso`.
* `groupHomologyIso_hom_comp`: for a chain map `φ : P ⟶ Q` of projective resolutions of the trivial
  representation (compatible with the augmentations), `groupHomologyIso A n P ≫ H(φ ⊗ A)` is
  `groupHomologyIso A n Q`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

universe u

namespace TernaryPeriodPolynomials.Argument.GroupHomology

open CategoryTheory Finsupp Rep
open scoped MonoidAlgebra

section BarAug

variable {k : Type u} [CommRing k] {G : Type u} [Group G] {n : ℕ}

set_option backward.defeqAttrib.useBackward true in
unif_hint (X : Type*) where ⊢ Action.V (Action.trivial G X) ≟ X in
unif_hint where ⊢ (HomologicalComplex.X (standardComplex k G) n).V ≟ k[Fin (n + 1) → G] in
set_option backward.isDefEq.respectTransparency false in
lemma diagonalSuccIsoFree_inv_single_single (m : ℕ) (f : Fin m → G) (g : G) (r : k) :
    (diagonalSuccIsoFree k G m).inv.hom (single f (MonoidAlgebra.single g r)) =
      MonoidAlgebra.single (g • Fin.partialProd f) r := by
  simp only [diagonalSuccIsoFree, diagonalSuccIsoTensorTrivial, Iso.trans_inv, Rep.hom_comp,
    Representation.IntertwiningMap.comp_apply]
  have step1 : (Hom.hom (leftRegularTensorTrivialIsoFree k G (Fin m → G)).inv)
      (single f (.single g r)) = .single g 1 ⊗ₜ[k] .single f r :=
    Representation.leftRegularTensorTrivialIsoFree_symm_apply_single_single f g r
  rw [step1]
  simp only [mkIso_inv, Representation.linearizeOfMulActionIso, Representation.Equiv.mk_symm,
    LinearEquiv.refl_symm, ConcreteCategory.hom_ofHom, Action.tensorObj_V, Action.trivial_V,
    Functor.mapIso_inv, tensor_V, tensor_ρ, Iso.symm_inv, Functor.Monoidal.μIso_hom, μ_hom,
    MonoidalCategory.tensorIso_inv, Representation.linearizeTrivialIso, hom_tensorHom,
    Representation.IntertwiningMap.tensor_apply, Representation.Equiv.coe_toIntertwiningMap,
    Representation.Equiv.mk_apply, LinearEquiv.refl_apply]
  have key₁ := Representation.linearizeMap_single (k := k)
    (Action.diagonalSuccIsoTensorTrivial G m).inv (g, f) ((1 : k) * r)
  have key₂ := Representation.LinearizeMonoidal.μ_apply_single_single (k := k)
    (X := Action.leftRegular G) (Y := Action.trivial G (Fin m → G)) g f 1 r
  exact ((congrArg (fun z => (Representation.linearizeMap
    (Action.diagonalSuccIsoTensorTrivial G m).inv) z) key₂).trans key₁).trans (by simp)

lemma barPi_f_zero (i : Fin 0 → G) (g : G) (r : k) :
    ((barResolution k G).π.f 0).hom (single i (MonoidAlgebra.single g r)) = r := by
  change ((standardComplex.εToSingle₀ k G).f 0).hom
    ((diagonalSuccIsoFree k G 0).inv.hom (single i (MonoidAlgebra.single g r))) = r
  rw [diagonalSuccIsoFree_inv_single_single]
  erw [standardComplex.εToSingle₀, ChainComplex.toSingle₀Equiv_symm_apply_f_zero]
  change (linearCombination k fun _ => (1 : k)) ((MonoidAlgebra.coeffLinearEquiv k)
    (MonoidAlgebra.single (g • Fin.partialProd i) r)) = r
  simp

end BarAug

section Maps

variable {k : Type u} [CommRing k] {G₁ G₂ : Type u} [Group G₁] [Group G₂] (f : G₁ →* G₂)

/-- Functoriality of the terms of the bar resolution along `f : G₁ →* G₂`. -/
def barTerm (n : ℕ) : free k G₁ (Fin n → G₁) ⟶ res f (free k G₂ (Fin n → G₂)) :=
  freeLift k G₁ _ (fun x => single (f ∘ x) (MonoidAlgebra.single (1 : G₂) (1 : k)))

theorem barTerm_single (n : ℕ) (x : Fin n → G₁) (h : G₁) (r : k) :
    (barTerm (k := k) f n).hom (single x (MonoidAlgebra.single h r)) =
      single (f ∘ x) (MonoidAlgebra.single (f h) r) := by
  simp [barTerm, Representation.freeLift_single_single]

theorem barTerm_comm (n : ℕ) :
    barTerm (k := k) f (n + 1) ≫ (resFunctor f).map (barComplex.d k G₂ n) =
      barComplex.d k G₁ n ≫ barTerm f n := by
  refine free_ext _ _ _ _ _ fun x => ?_
  have h1 := barComplex.d_single (k := k) (G := G₁) n x
  have h2 := barComplex.d_single (k := k) (G := G₂) n (f ∘ x)
  simp only [Rep.hom_comp, Representation.IntertwiningMap.comp_apply]
  have e1 : (barTerm (k := k) f (n + 1)).hom (single x (MonoidAlgebra.single 1 1)) =
      single (f ∘ x) (MonoidAlgebra.single (1 : G₂) 1) := by
    rw [barTerm_single, map_one]
  rw [e1]
  change (barComplex.d k G₂ n).hom (single (f ∘ x) (MonoidAlgebra.single 1 1)) = _
  rw [h2, h1, map_add, map_sum]
  congr 1
  · rw [barTerm_single]
    rfl
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [barTerm_single, map_one]
    simp [Fin.comp_contractNth]

/-- The chain map `bar(G₁) ⟶ Res_f bar(G₂)`. -/
def barMap : barComplex k G₁ ⟶
    ((resFunctor f).mapHomologicalComplex (ComplexShape.down ℕ)).obj (barComplex k G₂) where
  f n := barTerm f n
  comm' := by
    rintro i j (rfl : j + 1 = i)
    simp only [barComplex, ChainComplex.of_d, Functor.mapHomologicalComplex_obj_d]
    exact barTerm_comm (k := k) f j

theorem barMap_pi (N : Subgroup G₂) :
    (barMap (k := k) N.subtype).f 0 ≫
      ((resFunctor N.subtype).mapProjectiveResolution (barResolution k G₂)).π.f 0 =
      (barResolution k N).π.f 0 := by
  refine free_ext _ _ _ _ _ fun x => ?_
  have h2 := barPi_f_zero (k := k) (G := N) x 1 1
  have h3 := barPi_f_zero (k := k) (G := G₂) (fun i => (x i : G₂)) 1 1
  refine Eq.trans ?_ h2.symm
  have key : (((resFunctor N.subtype).mapProjectiveResolution (barResolution k G₂)).π.f 0).hom
      ((barTerm (k := k) N.subtype 0).hom (single x (MonoidAlgebra.single 1 1))) =
      (((resFunctor N.subtype).mapProjectiveResolution (barResolution k G₂)).π.f 0).hom
        (single (fun i => (x i : G₂)) (MonoidAlgebra.single 1 1)) := by
    rw [barTerm_single, map_one]
    rfl
  exact key.trans h3

end Maps

section GIso

variable {k G : Type u} [CommRing k] [Group G] [DecidableEq G] (A : Rep.{u} k G) (n : ℕ)

theorem iso_cancel_aux {C : Type*} [Category C] {X Y Z : C} (e : X ≅ Y) (t : Z ≅ Y) :
    ((e ≪≫ t.symm) ≪≫ t).hom = e.hom := by
  simp

theorem iso_comp_aux {C : Type*} [Category C] {X Y W V : C} (t : X ≅ W) (i₁ : W ≅ Y) (i₂ : W ≅ V)
    (H : Y ⟶ V) (h : i₂.hom = i₁.hom ≫ H) : (t ≪≫ i₁).hom ≫ H = (t ≪≫ i₂).hom := by
  simp [h]

theorem groupHomologyIso_bar_hom :
    (groupHomologyIso A n (barResolution k G)).hom =
      HomologicalComplex.homologyMap (groupHomology.inhomogeneousChainsIso A).hom n :=
  iso_cancel_aux
    (isoOfQuasiIsoAt (HomotopyEquiv.ofIso (groupHomology.inhomogeneousChainsIso A)).hom n)
    (A.torIso (barResolution k G) n)

theorem groupHomologyIso_hom_comp {P Q : ProjectiveResolution (Rep.trivial k G k)}
    (φ : P.complex ⟶ Q.complex) (comm : φ.f 0 ≫ Q.π.f 0 = P.π.f 0) :
    (groupHomologyIso A n P).hom ≫ HomologicalComplex.homologyMap
        ((((coinvariantsTensor k G).obj A).mapHomologicalComplex _).map φ) n =
      (groupHomologyIso A n Q).hom := by
  have h := ProjectiveResolution.isoLeftDerivedObj_hom_naturality (𝟙 _) P Q φ
    (by erw [Category.comp_id]; exact comm) ((coinvariantsTensor k G).obj A) n
  have h' : (A.torIso Q n).hom = (A.torIso P n).hom ≫ HomologicalComplex.homologyMap
      ((((coinvariantsTensor k G).obj A).mapHomologicalComplex _).map φ) n := by
    have := h
    erw [CategoryTheory.Functor.map_id, Category.id_comp] at this
    exact this
  exact iso_comp_aux (groupHomologyIsoTor A n) (A.torIso P n) (A.torIso Q n) _ h'

end GIso

end TernaryPeriodPolynomials.Argument.GroupHomology
