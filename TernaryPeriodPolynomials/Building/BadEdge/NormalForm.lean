module

public import TernaryPeriodPolynomials.Building.AugmentedFrame.BadFaces

@[expose] public section

noncomputable section
namespace TernaryPoly.BadEdgeNormalForm
open ModThreeGoodAction AugmentedFrameComplex AugmentedBadFaces

abbrev Mat := Matrix (Fin 3) (Fin 3) ℤ

/-- The six increasing pairs of augmented template indices. -/
def pairIndex : Fin 6 → Fin 2 → Fin 4 :=
  ![![0,1],![0,2],![0,3],![1,2],![1,3],![2,3]]

/-- Integral basis completions for the six pairs, in the displayed endpoint order. -/
def pairMatrix : Fin 6 → Mat :=
  ![!![1,0,0;0,1,0;0,0,1],
    !![1,0,0;0,0,1;0,1,0],
    !![1,1,0;0,1,0;0,0,1],
    !![0,0,1;1,0,0;0,1,0],
    !![0,1,0;1,1,0;0,0,1],
    !![0,1,1;0,1,0;1,0,0]]

/-- Actual inverse matrices for the finite completion table. -/
def pairInverse : Fin 6 → Mat :=
  ![!![1,0,0;0,1,0;0,0,1],
    !![1,0,0;0,0,1;0,1,0],
    !![1,-1,0;0,1,0;0,0,1],
    !![0,1,0;0,0,1;1,0,0],
    !![-1,1,0;1,0,0;0,0,1],
    !![0,0,1;0,1,0;1,-1,0]]

theorem pairMatrix_mul_inverse : ∀ k, pairMatrix k * pairInverse k = 1 := by decide +kernel
theorem pairInverse_mul_matrix : ∀ k, pairInverse k * pairMatrix k = 1 := by decide +kernel

/-- Six genuine integer matrix units completing every pair. -/
def pairChange (k : Fin 6) : IntegralGL :=
  ⟨pairMatrix k,pairInverse k,pairMatrix_mul_inverse k,pairInverse_mul_matrix k⟩

private def integerTemplate : Fin 4 → IntegralVector :=
  ![![1,0,0],![0,1,0],![0,0,1],![1,1,0]]

private theorem rationalVector_integerTemplate : ∀ j, rationalVector (integerTemplate j) = template j := by
  decide +kernel

private theorem pairMatrix_template : ∀ (k : Fin 6) (j : Fin 2),
    (pairMatrix k).mulVec (integerTemplate j.castSucc.castSucc) = integerTemplate (pairIndex k j) := by
  decide +kernel

/-- The first two template vectors map to the selected ordered pair exactly, without sign changes. -/
theorem pairChange_template (k : Fin 6) (j : Fin 2) :
    rationalRepresentation (pairChange k) (template j.castSucc.castSucc) = template (pairIndex k j) := by
  rw [← rationalVector_integerTemplate,← rationalVector_integerTemplate,← rationalVector_mulVec]
  exact congrArg rationalVector (pairMatrix_template k j)

/-- A literal template-vector identity gives the corresponding line identity after any basis change. -/
theorem augmentedLine_mul_of_template (g h : IntegralGL) (i j : Fin 4)
    (hij : rationalRepresentation h (template i) = template j) :
    augmentedLine (g*h) i = augmentedLine g j := by
  apply Subtype.ext
  change Submodule.span ℚ {rationalRepresentation (g*h) (template i)} =
    Submodule.span ℚ {rationalRepresentation g (template j)}
  rw [map_mul]
  change Submodule.span ℚ {rationalRepresentation g (rationalRepresentation h (template i))} = _
  rw [hij]

theorem augmentedLine_pairChange (g : IntegralGL) (k : Fin 6) (j : Fin 2) :
    augmentedLine (g * pairChange k) j.castSucc.castSucc = augmentedLine g (pairIndex k j) :=
  augmentedLine_mul_of_template g (pairChange k) _ _ (pairChange_template k j)

def swapMatrix : Mat := !![0,1,0;1,0,0;0,0,1]
theorem swapMatrix_sq : swapMatrix * swapMatrix = 1 := by decide +kernel

/-- Swap the first two integral columns, retaining the complementary column. -/
def swapFirstTwo : IntegralGL := ⟨swapMatrix,swapMatrix,swapMatrix_sq,swapMatrix_sq⟩

private theorem swapFirstTwo_template_zero : rationalRepresentation swapFirstTwo (template 0) = template 1 := by
  rw [← rationalVector_integerTemplate,← rationalVector_integerTemplate,← rationalVector_mulVec]
  exact congrArg rationalVector (show swapMatrix.mulVec (integerTemplate 0) = integerTemplate 1 by decide +kernel)

private theorem swapFirstTwo_template_one : rationalRepresentation swapFirstTwo (template 1) = template 0 := by
  rw [← rationalVector_integerTemplate,← rationalVector_integerTemplate,← rationalVector_mulVec]
  exact congrArg rationalVector (show swapMatrix.mulVec (integerTemplate 1) = integerTemplate 0 by decide +kernel)

theorem augmentedLine_swapFirstTwo_zero (g : IntegralGL) :
    augmentedLine (g*swapFirstTwo) 0 = augmentedLine g 1 :=
  augmentedLine_mul_of_template g swapFirstTwo 0 1 swapFirstTwo_template_zero

theorem augmentedLine_swapFirstTwo_one (g : IntegralGL) :
    augmentedLine (g*swapFirstTwo) 1 = augmentedLine g 0 :=
  augmentedLine_mul_of_template g swapFirstTwo 1 0 swapFirstTwo_template_one

/-- The finite table, together with reversal, exhausts all ordered pairs of distinct template indices. -/
theorem pairIndex_exhaustive : ∀ i j : Fin 4, i ≠ j → ∃ k : Fin 6,
    (pairIndex k 0 = i ∧ pairIndex k 1 = j) ∨ (pairIndex k 1 = i ∧ pairIndex k 0 = j) := by
  decide +kernel

/-- Every ordered pair of distinct actual augmented-template lines is the initial pair of an integral basis. -/
theorem ordered_template_pair (g : IntegralGL) (i j : Fin 4) (hij : i ≠ j) :
    ∃ h : IntegralGL, augmentedLine h 0 = augmentedLine g i ∧
      augmentedLine h 1 = augmentedLine g j := by
  obtain ⟨k,hk | hk⟩ := pairIndex_exhaustive i j hij
  · refine ⟨g * pairChange k,?_,?_⟩
    · exact (augmentedLine_pairChange g k 0).trans (congrArg (augmentedLine g) hk.1)
    · exact (augmentedLine_pairChange g k 1).trans (congrArg (augmentedLine g) hk.2)
  · refine ⟨(g * pairChange k) * swapFirstTwo,?_,?_⟩
    · rw [augmentedLine_swapFirstTwo_zero]
      exact (augmentedLine_pairChange g k 1).trans (congrArg (augmentedLine g) hk.1)
    · rw [augmentedLine_swapFirstTwo_one]
      exact (augmentedLine_pairChange g k 0).trans (congrArg (augmentedLine g) hk.2)

/-- Every actual ordered ambient edge has a genuine integral-basis completion. -/
theorem ordered_ambient_edge (L M : RationalLine) (hLM : L ≠ M)
    (hface : {L,M} ∈ ambient) :
    ∃ g : IntegralGL, augmentedLine g 0 = L ∧ augmentedLine g 1 = M := by
  classical
  obtain ⟨_,g,hg⟩ := hface
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp (hg (by simp : L ∈ ({L,M} : Finset RationalLine)))
  obtain ⟨j,_,hj⟩ := Finset.mem_image.mp (hg (by simp : M ∈ ({L,M} : Finset RationalLine)))
  have hij : i ≠ j := by
    intro he
    apply hLM
    rw [← hi,← hj,he]
  obtain ⟨h,hh0,hh1⟩ := ordered_template_pair g i j hij
  exact ⟨h,hh0.trans hi,hh1.trans hj⟩

/-- The exact residue pattern for an integral basis with two bad initial column lines. -/
theorem bad_initial_residues (g : IntegralGL)
    (h0 : ¬Good (augmentedLine g 0).val) (h1 : ¬Good (augmentedLine g 1).val) :
    columnResidue g 0 = 0 ∧ columnResidue g 1 = 0 ∧ columnResidue g 2 ≠ 0 := by
  have hr0 : columnResidue g 0 = 0 := bad_augmentedLine_residue g 0 h0
  have hr1 : columnResidue g 1 = 0 := bad_augmentedLine_residue g 1 h1
  refine ⟨hr0,hr1,?_⟩
  obtain ⟨j,hj⟩ := exists_columnResidue_ne_zero g
  fin_cases j
  · exact False.elim (hj hr0)
  · exact False.elim (hj hr1)
  · exact hj

/-- Ordered all-bad edge normal form, with literal endpoints and the full required residue pattern. -/
theorem ordered_bad_edge (L M : RationalLine) (hLM : L ≠ M)
    (hface : {L,M} ∈ ambient) (hL : ¬Good L.val) (hM : ¬Good M.val) :
    ∃ g : IntegralGL, augmentedLine g 0 = L ∧ augmentedLine g 1 = M ∧
      columnResidue g 0 = 0 ∧ columnResidue g 1 = 0 ∧ columnResidue g 2 ≠ 0 := by
  obtain ⟨g,hg0,hg1⟩ := ordered_ambient_edge L M hLM hface
  obtain ⟨hr0,hr1,hr2⟩ := bad_initial_residues g (hg0 ▸ hL) (hg1 ▸ hM)
  exact ⟨g,hg0,hg1,hr0,hr1,hr2⟩

/-- Every two-element all-bad ambient face has the exact initial-column set normal form. -/
theorem all_bad_card_two (s : Finset RationalLine) (hface : s ∈ ambient) (hs : s.card = 2)
    (hbad : ∀ L ∈ s, ¬Good L.val) :
    ∃ g : IntegralGL, s = {augmentedLine g 0,augmentedLine g 1} ∧
      columnResidue g 0 = 0 ∧ columnResidue g 1 = 0 ∧ columnResidue g 2 ≠ 0 := by
  classical
  obtain ⟨L,M,hLM,rfl⟩ := Finset.card_eq_two.mp hs
  obtain ⟨g,hg0,hg1,hr0,hr1,hr2⟩ := ordered_bad_edge L M hLM hface
    (hbad L (by simp)) (hbad M (by simp))
  exact ⟨g,by rw [hg0,hg1],hr0,hr1,hr2⟩

end TernaryPoly.BadEdgeNormalForm
