module

public import TernaryPeriodPolynomials.Building.AugmentedFrame.FrameComplex
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Tactic.Push
public import Lean.Elab.Tactic.Omega

@[expose] public section


noncomputable section
namespace TernaryPoly.AugmentedBadFaces
open ModThreeGoodAction AugmentedFrameComplex

/-- Coordinate-sum residues of the columns of an actual integral basis. -/
def columnResidue (g : IntegralGL) (j : Fin 3) : ZMod 3 := ∑ i, (g.val i j : ZMod 3)

/-- Invertibility prevents all three column residues from vanishing simultaneously. -/
theorem exists_columnResidue_ne_zero (g : IntegralGL) : ∃ j, columnResidue g j ≠ 0 := by
  by_contra h
  push Not at h
  have hz : Matrix.vecMul fixedRow (reduction g).val = 0 := by
    funext j
    change (∑ i, (1 : ZMod 3) * (g.val i j : ZMod 3)) = 0
    simpa only [columnResidue, one_mul] using h j
  have hi : (reduction g).val * (reduction g⁻¹).val = 1 := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have hc := congrArg (fun row => Matrix.vecMul row (reduction g⁻¹).val) hz
  rw [Matrix.vecMul_vecMul, hi, Matrix.vecMul_one, Matrix.zero_vecMul] at hc
  have hc0 := congrFun hc 0
  exact (one_ne_zero : (1 : ZMod 3) ≠ 0) hc0

/-- The rational image of a coordinate vector is the corresponding actual integer column. -/
theorem rationalRepresentation_basis (g : IntegralGL) (j : Fin 3) :
    rationalRepresentation g (Pi.single j 1) = rationalVector (fun i => g.val i j) := by
  rw [rationalRepresentation_apply, Matrix.mulVec_single_one]
  rfl

/-- Any nonzero column residue explicitly witnesses goodness of its rational column line. -/
theorem good_basis_line (g : IntegralGL) (j : Fin 3) (h : columnResidue g j ≠ 0) :
    Good (Submodule.span ℚ {rationalRepresentation g (Pi.single j 1)}) := by
  refine ⟨(fun i => g.val i j), ?_, h⟩
  rw [rationalRepresentation_basis]
  exact Submodule.mem_span_singleton_self _

/-- Every actual integral basis has a good rational column line. -/
theorem exists_good_basis_line (g : IntegralGL) :
    ∃ j : Fin 3, Good (Submodule.span ℚ {rationalRepresentation g (Pi.single j 1)}) := by
  obtain ⟨j,hj⟩ := exists_columnResidue_ne_zero g
  exact ⟨j,good_basis_line g j hj⟩

/-- The coordinate-basis columns occur among the first three augmented lines. -/
theorem augmentedLine_castSucc_val (g : IntegralGL) (j : Fin 3) :
    (augmentedLine g j.castSucc).val =
      Submodule.span ℚ {rationalRepresentation g (Pi.single j 1)} := by
  fin_cases j <;> rfl

/-- Every actual augmented frame contains at least one good vertex. -/
theorem exists_good_augmentedFrame (g : IntegralGL) :
    ∃ L ∈ augmentedFrame g, Good L.val := by
  obtain ⟨j,hj⟩ := exists_good_basis_line g
  refine ⟨augmentedLine g j.castSucc, Finset.mem_image.mpr ⟨j.castSucc, Finset.mem_univ _, rfl⟩, ?_⟩
  rwa [augmentedLine_castSucc_val]

private theorem template_eq_index (q : ℚ) (i j : Fin 4)
    (h : q • template j = template i) : i = j := by
  by_contra hne
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  fin_cases i <;> fin_cases j <;>
    simp_all [template, Pi.smul_apply, smul_eq_mul]

/-- All four actual augmented template lines remain distinct under every integral basis change. -/
theorem augmentedLine_injective (g : IntegralGL) : Function.Injective (augmentedLine g) := by
  intro i j h
  have hmem : rationalRepresentation g (template i) ∈
      Submodule.span ℚ {rationalRepresentation g (template j)} := by
    change rationalRepresentation g (template i) ∈ (augmentedLine g j).val
    rw [← h]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨q,hq⟩ := Submodule.mem_span_singleton.mp hmem
  apply template_eq_index q i j
  apply (rationalRepresentation g).injective
  rw [map_smul]
  exact hq

@[simp] theorem augmentedFrame_card (g : IntegralGL) : (augmentedFrame g).card = 4 := by
  rw [augmentedFrame, Finset.card_image_of_injective _ (augmentedLine_injective g)]
  rfl

/-- Every ambient face has at most four actual rational line vertices. -/
theorem ambient_card_le_four {s : Finset RationalLine} (hs : s ∈ ambient) : s.card ≤ 4 := by
  obtain ⟨_,g,hg⟩ := hs
  exact (Finset.card_le_card hg).trans_eq (augmentedFrame_card g)

/-- An all-bad face omits a good vertex of each witnessing augmented frame. -/
theorem all_bad_card_le_three {s : Finset RationalLine} (hs : s ∈ ambient)
    (hbad : ∀ L ∈ s, ¬ Good L.val) : s.card ≤ 3 := by
  obtain ⟨_,g,hg⟩ := hs
  obtain ⟨L,hL,hgood⟩ := exists_good_augmentedFrame g
  have hne : s ≠ augmentedFrame g := by
    intro he
    exact hbad L (he ▸ hL) hgood
  have hc := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hg,hne⟩)
  rw [augmentedFrame_card] at hc
  omega

/-- The fourth template vector has the sum of the first two column residues. -/
def templateResidue (g : IntegralGL) : Fin 4 → ZMod 3 :=
  ![columnResidue g 0,columnResidue g 1,columnResidue g 2,
    columnResidue g 0 + columnResidue g 1]

private theorem good_augmentedLine_three (g : IntegralGL)
    (h : columnResidue g 0 + columnResidue g 1 ≠ 0) : Good (augmentedLine g 3).val := by
  refine ⟨(fun i => g.val i 0 + g.val i 1), ?_, ?_⟩
  · have he : rationalVector (fun i => g.val i 0 + g.val i 1) =
        rationalRepresentation g (template 3) := by
      change _ = rationalRepresentation g (Pi.single 0 1 + Pi.single 1 1)
      rw [map_add, rationalRepresentation_basis, rationalRepresentation_basis]
      funext i
      simp only [rationalVector, Int.cast_add, Pi.add_apply]
    change rationalVector (fun i => g.val i 0 + g.val i 1) ∈
      Submodule.span ℚ {rationalRepresentation g (template 3)}
    rw [he]
    exact Submodule.mem_span_singleton_self _
  · simpa only [Int.cast_add, Finset.sum_add_distrib, columnResidue] using h

/-- A nonzero actual template residue is an explicit lattice witness for goodness. -/
theorem good_augmentedLine_of_residue (g : IntegralGL) (i : Fin 4)
    (h : templateResidue g i ≠ 0) : Good (augmentedLine g i).val := by
  fin_cases i
  · exact good_basis_line g 0 h
  · exact good_basis_line g 1 h
  · exact good_basis_line g 2 h
  · exact good_augmentedLine_three g h

/-- Every bad actual augmented line has zero template residue. -/
theorem bad_augmentedLine_residue (g : IntegralGL) (i : Fin 4)
    (h : ¬ Good (augmentedLine g i).val) : templateResidue g i = 0 := by
  by_contra hn
  exact h (good_augmentedLine_of_residue g i hn)

/-- Exact exhaustive residue classification over the four-element template. -/
private theorem zero_residue_triple :
    ∀ r : Fin 3 → ZMod 3, (∃ j, r j ≠ 0) →
    ∀ t : Finset (Fin 4), t.card = 3 →
      (∀ i ∈ t, (![r 0,r 1,r 2,r 0+r 1] : Fin 4 → ZMod 3) i = 0) →
      t = {0,1,3} := by
  decide +kernel

/-- The actual augmented rank-two core consists of the first, second, and sum lines. -/
def augmentedCore (g : IntegralGL) : Finset RationalLine :=
  {augmentedLine g 0,augmentedLine g 1,augmentedLine g 3}

/-- Every all-bad three-vertex subface is precisely the rank-two core of its witnessing frame. -/
theorem all_bad_card_three_eq_core (g : IntegralGL) {s : Finset RationalLine}
    (hsub : s ⊆ augmentedFrame g) (hcard : s.card = 3)
    (hbad : ∀ L ∈ s, ¬ Good L.val) : s = augmentedCore g := by
  classical
  let t : Finset (Fin 4) := Finset.univ.filter (fun i => augmentedLine g i ∈ s)
  have htimage : t.image (augmentedLine g) = s := by
    ext L
    constructor
    · intro hL
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hL
      exact (Finset.mem_filter.mp hi).2
    · intro hL
      obtain ⟨i,_,hi⟩ := Finset.mem_image.mp (hsub hL)
      exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,by simpa only [hi] using hL⟩,hi⟩
  have htcard : t.card = 3 := by
    rw [← Finset.card_image_of_injective t (augmentedLine_injective g), htimage, hcard]
  have htbad : ∀ i ∈ t, templateResidue g i = 0 := by
    intro i hi
    exact bad_augmentedLine_residue g i (hbad _ (Finset.mem_filter.mp hi).2)
  have hcore := zero_residue_triple (columnResidue g) (exists_columnResidue_ne_zero g)
    t htcard htbad
  rw [← htimage, hcore]
  simp only [augmentedCore, Finset.image_insert, Finset.image_singleton]

/-- Exhaustive classification retains the actual integral matrix witnessing an ambient face. -/
theorem all_bad_card_three_exists_core {s : Finset RationalLine} (hs : s ∈ ambient)
    (hcard : s.card = 3) (hbad : ∀ L ∈ s, ¬ Good L.val) :
    ∃ g : IntegralGL, s = augmentedCore g := by
  obtain ⟨_,g,hg⟩ := hs
  exact ⟨g,all_bad_card_three_eq_core g hg hcard hbad⟩

end TernaryPoly.AugmentedBadFaces
