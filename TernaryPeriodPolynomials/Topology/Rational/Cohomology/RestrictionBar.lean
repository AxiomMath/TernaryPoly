module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
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

noncomputable section

namespace TernaryPoly.RationalCohomologyRestriction
open CategoryTheory Rep Finsupp

variable {G : Type} [Group G] (H : Subgroup G)

/-- The literal inclusion of subgroup tuples in the bar resolution. -/
def barInclusionF (n : ℕ) :
    Rep.free ℚ H (Fin n → H) ⟶ Rep.res H.subtype (Rep.free ℚ G (Fin n → G)) :=
  Rep.freeLift ℚ H _ (fun x => Finsupp.single (H.subtype ∘ x) (.single 1 1))

@[simp] theorem barInclusionF_single (n : ℕ) (x : Fin n → H) (g : H) (r : ℚ) :
    (barInclusionF H n).hom (Finsupp.single x (.single g r)) =
      Finsupp.single (H.subtype ∘ x) (.single (g : G) r) := by
  simp [barInclusionF]

/-- The literal subgroup-bar inclusion is a chain map. -/
def barInclusion :
    (Rep.barResolution ℚ H).complex ⟶
      ((Rep.resFunctor H.subtype).mapProjectiveResolution (Rep.barResolution ℚ G)).complex where
  f n := barInclusionF H n
  comm' i j hij := by
    obtain rfl : j + 1 = i := hij
    dsimp only [Functor.mapProjectiveResolution, Rep.barResolution, Functor.mapHomologicalComplex]
    simp only [ChainComplex.of_d]
    change barInclusionF H (j+1) ≫ (Rep.resFunctor H.subtype).map (Rep.barComplex.d ℚ G j) =
      Rep.barComplex.d ℚ H j ≫ barInclusionF H j
    apply Rep.free_ext
    intro x
    change (Rep.barComplex.d ℚ G j).hom
        ((barInclusionF H (j+1)).hom (Finsupp.single x (.single (1 : H) 1))) =
      (barInclusionF H j).hom
        ((Rep.barComplex.d ℚ H j).hom (Finsupp.single x (.single (1 : H) 1)))
    rw [barInclusionF_single]
    change (Rep.barComplex.d ℚ G j).hom (Finsupp.single (H.subtype ∘ x) (.single 1 1)) = _
    rw [Rep.barComplex.d_single, Rep.barComplex.d_single]
    simp only [map_add, map_sum]
    congr 1
    · exact (barInclusionF_single H j (fun i => x i.succ) (x 0) 1).symm
    · apply Finset.sum_congr rfl
      intro t _
      calc
        _ = Finsupp.single (H.subtype ∘ t.contractNth (· * ·) x)
            (.single (1 : G) ((-1 : ℚ) ^ ((t : ℕ) + 1))) := by
          congr 1
          exact (Fin.comp_contractNth (· * ·) (· * ·)
            (fun _ _ => rfl : ∀ a b : H, H.subtype (a*b) = H.subtype a * H.subtype b) t x).symm
        _ = _ := (barInclusionF_single H j (t.contractNth (· * ·) x) 1
          ((-1 : ℚ) ^ ((t : ℕ) + 1))).symm

/-- The inverse bar/standard comparison on a literal generator. The proof follows
Mathlib's generator calculation in `barComplex.d_comp_diagonalSuccIsoFree_inv_eq`. -/
theorem diagonalFreeInv_single (n : ℕ) (x : Fin n → G) (g : G) (r : ℚ) :
    (Rep.diagonalSuccIsoFree ℚ G n).inv.hom (single x (MonoidAlgebra.single g r)) =
      MonoidAlgebra.single (g • Fin.partialProd x) r := by
  simp only [Rep.diagonalSuccIsoFree, Rep.diagonalSuccIsoTensorTrivial, Iso.trans_inv,
    Rep.hom_comp, Representation.IntertwiningMap.comp_apply]
  have step1 : (Rep.leftRegularTensorTrivialIsoFree ℚ G (Fin n → G)).inv.hom
      (single x (MonoidAlgebra.single g r)) =
      MonoidAlgebra.single g 1 ⊗ₜ[ℚ] MonoidAlgebra.single x r :=
    Representation.leftRegularTensorTrivialIsoFree_symm_apply_single_single x g r
  rw [step1]
  dsimp only [Rep.mkIso_inv, Representation.linearizeOfMulActionIso, Representation.Equiv.mk_symm,
    LinearEquiv.refl_symm, ConcreteCategory.hom_ofHom, Action.tensorObj_V, Action.trivial_V,
    CategoryTheory.Functor.mapIso_inv, Rep.tensor_V, Rep.tensor_ρ, Iso.symm_inv,
    Functor.Monoidal.μIso_hom, Rep.μ_hom, MonoidalCategory.tensorIso_inv,
    Representation.linearizeTrivialIso, Rep.hom_tensorHom,
    Representation.IntertwiningMap.tensor_apply, Representation.Equiv.coe_toIntertwiningMap,
    Representation.Equiv.mk_apply, LinearEquiv.refl_apply]
  have key₁ := Representation.linearizeMap_single (k := ℚ)
    (Action.diagonalSuccIsoTensorTrivial G n).inv (g, x) ((1 : ℚ) * r)
  have key₂ := Representation.LinearizeMonoidal.μ_apply_single_single (k := ℚ)
    (X := Action.leftRegular G) (Y := Action.trivial G (Fin n → G)) g x 1 r
  exact ((congrArg (fun z => (Representation.linearizeMap
    (Action.diagonalSuccIsoTensorTrivial G n).inv) z) key₂).trans key₁).trans (by
      simp only [one_mul]
      exact congrArg (fun z => MonoidAlgebra.single z r)
        (Action.diagonalSuccIsoTensorTrivial_inv_hom_apply g x))

/-- The actual bar augmentation sends each group-ring generator to its coefficient. -/
theorem barAugmentation_single (x : Fin 0 → G) (g : G) (r : ℚ) :
    ((Rep.barResolution ℚ G).π.f 0).hom (single x (MonoidAlgebra.single g r)) = r := by
  change (Rep.standardComplex.ε ℚ G).hom
    ((Rep.diagonalSuccIsoFree ℚ G 0).inv.hom (single x (MonoidAlgebra.single g r))) = r
  rw [diagonalFreeInv_single]
  simp [Rep.standardComplex.ε]

/-- The literal bar inclusion lifts the identity of the trivial representation. -/
theorem barInclusion_augmentation :
    (barInclusion H).f 0 ≫
      ((Rep.resFunctor H.subtype).mapProjectiveResolution (Rep.barResolution ℚ G)).π.f 0 =
      (Rep.barResolution ℚ H).π.f 0 := by
  apply Rep.free_ext
  intro x
  change ((Rep.barResolution ℚ G).π.f 0).hom
      ((barInclusionF H 0).hom (single x (MonoidAlgebra.single (1 : H) 1))) =
    ((Rep.barResolution ℚ H).π.f 0).hom (single x (MonoidAlgebra.single (1 : H) 1))
  rw [barInclusionF_single, barAugmentation_single, barAugmentation_single]

end TernaryPoly.RationalCohomologyRestriction
