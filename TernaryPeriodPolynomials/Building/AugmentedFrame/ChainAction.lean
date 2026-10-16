module

public import TernaryPeriodPolynomials.Building.AugmentedFrame.FrameComplex
public import TernaryPeriodPolynomials.Building.OrientedChain.ChainMap
public import Mathlib.RepresentationTheory.Basic

@[expose] public section

/-! The actual integral matrix action on rational line vertices, augmented faces,
and oriented chains. Good and proper-good preservation uses the literal K subgroup. -/

noncomputable section
namespace TernaryPoly.AugmentedChainAction

open ModThreeGoodAction AugmentedFrameComplex OrientedListChains

local instance : DecidableEq RationalLine := Classical.decEq _

/-- The actual rational matrix action as an order automorphism of rational subspaces. -/
def subspaceAction (g : IntegralGL) : RationalSubspace ≃o RationalSubspace :=
  Submodule.orderIsoMapComap (rationalRepresentation g)

@[simp] theorem subspaceAction_apply (g : IntegralGL) (L : RationalSubspace) :
    subspaceAction g L = L.map (rationalRepresentation g).toLinearMap := rfl

/-- Dimension is preserved by the genuine rational linear equivalence. -/
theorem subspaceAction_finrank (g : IntegralGL) (L : RationalSubspace) :
    Module.finrank ℚ (subspaceAction g L) = Module.finrank ℚ L :=
  ((rationalRepresentation g).submoduleMap L).finrank_eq.symm

/-- The actual rational subspace action restricts to a permutation of rational lines. -/
def lineAction (g : IntegralGL) : Equiv.Perm RationalLine :=
  (subspaceAction g).toEquiv.subtypeEquiv (by
    intro L
    change (Module.finrank ℚ L = 1) ↔ (Module.finrank ℚ (subspaceAction g L) = 1)
    rw [subspaceAction_finrank])

@[simp] theorem lineAction_val (g : IntegralGL) (L : RationalLine) :
    (lineAction g L).val = L.val.map (rationalRepresentation g).toLinearMap := rfl

/-- Identity matrices fix every actual rational line. -/
@[simp] theorem lineAction_one (L : RationalLine) : lineAction 1 L = L := by
  apply Subtype.ext
  simp only [lineAction_val, map_one]
  change L.val.map (LinearMap.id : Space →ₗ[ℚ] Space) = L.val
  simp only [Submodule.map_id]

/-- Multiplication of actual integral matrices gives composition on rational lines. -/
theorem lineAction_mul (g h : IntegralGL) (L : RationalLine) :
    lineAction (g * h) L = lineAction g (lineAction h L) := by
  apply Subtype.ext
  simpa only [lineAction_val, map_mul, LinearEquiv.coe_toLinearMap_mul, Module.End.mul_eq_comp]
    using Submodule.map_comp (rationalRepresentation h).toLinearMap
      (rationalRepresentation g).toLinearMap L.val

/-- The matrix action sends a displayed augmented frame to the frame of the product matrix. -/
theorem lineAction_augmentedLine (g h : IntegralGL) (i : Fin 4) :
    lineAction g (augmentedLine h i) = augmentedLine (g * h) i := by
  apply Subtype.ext
  change (Submodule.span ℚ {rationalRepresentation h (template i)}).map
      (rationalRepresentation g).toLinearMap =
    Submodule.span ℚ {rationalRepresentation (g * h) (template i)}
  rw [Submodule.map_span, Set.image_singleton, map_mul, LinearEquiv.mul_apply]
  rfl

/-- Membership in an actual augmented frame can be read without any equality-instance choice. -/
theorem mem_augmentedFrame_iff (h : IntegralGL) (L : RationalLine) :
    L ∈ augmentedFrame h ↔ ∃ i : Fin 4, augmentedLine h i = L := by
  simp only [augmentedFrame, Finset.mem_image, Finset.mem_univ, true_and]

/-- The finite image of an actual augmented frame is exactly the product frame. -/
theorem image_augmentedFrame (g h : IntegralGL) :
    (augmentedFrame h).image (lineAction g) = augmentedFrame (g * h) := by
  ext L
  simp only [Finset.mem_image, mem_augmentedFrame_iff]
  constructor
  · rintro ⟨M, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, (lineAction_augmentedLine g h i).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨augmentedLine h i, ⟨i, rfl⟩, lineAction_augmentedLine g h i⟩

/-- Every integral matrix action is an actual face map of the ambient augmented-frame complex. -/
theorem ambient_mapsFaces (g : IntegralGL) :
    OrientedChainMap.MapsFaces (lineAction g) ambient ambient := by
  classical
  intro s hs
  obtain ⟨hne, h, hsub⟩ := hs
  refine ⟨hne.image _, g * h, ?_⟩
  rw [← image_augmentedFrame]
  exact Finset.image_subset_image hsub

/-- On the actual K subgroup, line goodness is preserved and reflected. -/
theorem lineAction_good_iff (g : K) (L : RationalLine) :
    Good (lineAction g.val L).val ↔ Good L.val :=
  ModThreeGoodAction.good_act_iff g L.val

/-- The actual K action preserves the full subcomplex of lattice-good rational lines. -/
theorem good_mapsFaces (g : K) :
    OrientedChainMap.MapsFaces (lineAction g.val) good good := by
  classical
  intro s hs
  refine ⟨ambient_mapsFaces g.val s hs.1, ?_⟩
  intro L hL
  obtain ⟨M, hM, rfl⟩ := Finset.mem_image.mp hL
  exact (lineAction_good_iff g M).mpr (hs.2 M hM)

/-- Finite face spans commute with the actual rational linear action. -/
theorem faceSpan_image (g : IntegralGL) (s : Finset RationalLine) :
    faceSpan (s.image (lineAction g)) =
      (faceSpan s).map (rationalRepresentation g).toLinearMap := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [faceSpan]
  | @insert L s hL ih =>
    simp only [faceSpan, Finset.image_insert, Finset.sup_insert,
      lineAction_val, Submodule.map_sup] at ih ⊢
    rw [ih]

/-- The dimension of the finite face span is preserved by an actual integral matrix. -/
theorem faceSpan_image_finrank (g : IntegralGL) (s : Finset RationalLine) :
    Module.finrank ℚ (faceSpan (s.image (lineAction g))) = Module.finrank ℚ (faceSpan s) := by
  rw [faceSpan_image]
  exact ((rationalRepresentation g).submoduleMap (faceSpan s)).finrank_eq.symm

/-- The actual K action also preserves the proper-span good subcomplex. -/
theorem properGood_mapsFaces (g : K) :
    OrientedChainMap.MapsFaces (lineAction g.val) properGood properGood := by
  classical
  intro s hs
  refine ⟨good_mapsFaces g s hs.1, ?_⟩
  rw [faceSpan_image_finrank]
  exact hs.2

/-- The actual integral matrix action on all finite oriented rational-line chains. -/
def chainAction (g : IntegralGL) : Chain RationalLine ≃ₗ[ℚ] Chain RationalLine :=
  OrientedChainMap.mapEquiv (lineAction g)

@[simp] theorem chainAction_simplex (g : IntegralGL) (l : List RationalLine) :
    chainAction g (simplex l) = simplex (l.map (lineAction g)) :=
  OrientedChainMap.map_simplex (lineAction g) l

/-- Identity matrices act identically on actual oriented chains. -/
@[simp] theorem chainAction_one (c : Chain RationalLine) : chainAction 1 c = c := by
  change OrientedChainMap.map (lineAction 1) c = c
  have he : (lineAction (1 : IntegralGL) : RationalLine → RationalLine) = id :=
    funext lineAction_one
  rw [he, OrientedChainMap.map_id]
  rfl

/-- Actual multiplication gives the actual composition law on oriented chains. -/
theorem chainAction_mul (g h : IntegralGL) (c : Chain RationalLine) :
    chainAction (g * h) c = chainAction g (chainAction h c) := by
  change OrientedChainMap.map (lineAction (g * h)) c =
    OrientedChainMap.map (lineAction g) (OrientedChainMap.map (lineAction h) c)
  rw [OrientedChainMap.map_comp_apply]
  have he : (lineAction (g * h) : RationalLine → RationalLine) =
      (lineAction g) ∘ (lineAction h) := funext (lineAction_mul g h)
  rw [he]

/-- The matrix-induced linear maps form a genuine rational representation. -/
def chainRepresentation : Representation ℚ IntegralGL (Chain RationalLine) where
  toFun g := (chainAction g).toLinearMap
  map_one' := by
    apply LinearMap.ext
    exact chainAction_one
  map_mul' g h := by
    apply LinearMap.ext
    exact chainAction_mul g h

/-- The actual matrix action commutes with the actual oriented boundary. -/
theorem boundary_chainAction (g : IntegralGL) (c : Chain RationalLine) :
    boundary (chainAction g c) = chainAction g (boundary c) :=
  OrientedChainMap.boundary_map (lineAction g) c

/-- Every degree of the actual ambient simplex-chain module is invariant. -/
theorem chainAction_mem_ambient (g : IntegralGL) (n : ℕ) {c : Chain RationalLine}
    (hc : c ∈ chains ambient n) : chainAction g c ∈ chains ambient n :=
  OrientedChainMap.map_mem_chains (lineAction g) ambient ambient (ambient_mapsFaces g) n hc

/-- The actual K action preserves every degree of the good simplex-chain module. -/
theorem chainAction_mem_good (g : K) (n : ℕ) {c : Chain RationalLine}
    (hc : c ∈ chains good n) : chainAction g.val c ∈ chains good n :=
  OrientedChainMap.map_mem_chains (lineAction g.val) good good (good_mapsFaces g) n hc

/-- The actual K action preserves every degree of the proper-good simplex-chain module. -/
theorem chainAction_mem_properGood (g : K) (n : ℕ) {c : Chain RationalLine}
    (hc : c ∈ chains properGood n) : chainAction g.val c ∈ chains properGood n :=
  OrientedChainMap.map_mem_chains (lineAction g.val) properGood properGood
    (properGood_mapsFaces g) n hc

end TernaryPoly.AugmentedChainAction
