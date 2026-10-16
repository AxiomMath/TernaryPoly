module

public import TernaryPeriodPolynomials.Building.BadVertex.Fibers
public import Mathlib.Data.List.Permutation

@[expose] public section


noncomputable section
namespace TernaryPoly.CoherentFramePermutations

open ModThreeGoodAction AugmentedFrameComplex CoherentPrismReduction
open BadVertexProjection BadVertexFibers

/-- All six ordered permutations of the coherent quotient triangle. -/
def permIndex : Fin 6 → Fin 3 → Fin 3 :=
  ![![0,1,2],![1,0,2],![0,2,1],![2,0,1],![1,2,0],![2,1,0]]

/-- Six literal integral basis changes, fixing b and changing the two quotient columns. -/
def changeMatrix : Fin 6 → Matrix (Fin 3) (Fin 3) ℤ :=
  ![!![1,0,0;0,1,0;0,0,1],
    !![1,0,0;0,0,1;0,1,0],
    !![1,0,0;0,-1,1;0,0,1],
    !![1,0,0;0,1,-1;0,1,0],
    !![1,0,0;0,0,1;0,-1,1],
    !![1,0,0;0,1,0;0,1,-1]]

theorem changeMatrix_det : ∀ r : Fin 6,
    (changeMatrix r).det = 1 ∨ (changeMatrix r).det = -1 := by decide +kernel

def basisChange (r : Fin 6) : IntegralGL :=
  Matrix.nonsingInvUnit (changeMatrix r) (by
    rcases changeMatrix_det r with h | h <;> rw [h] <;> norm_num)

/-- Only the chosen vector signs change; these signs disappear at the rational-line level. -/
def lineSign : Fin 6 → Fin 3 → ℤ :=
  ![![1,1,1],![1,1,1],![-1,1,1],![1,-1,1],![-1,1,1],![1,-1,1]]

theorem lineSign_ne_zero : ∀ r i, lineSign r i ≠ 0 := by decide +kernel

theorem changeMatrix_first : ∀ r : Fin 6,
    (changeMatrix r).mulVec (GoodAugmentedNormalForm.integralTemplate 0) =
      GoodAugmentedNormalForm.integralTemplate 0 := by decide +kernel

/-- Exact integer identities certify the claimed ordered permutations, including their signs. -/
theorem changeMatrix_coherent : ∀ (r : Fin 6) (i : Fin 3),
    (changeMatrix r).mulVec (fiberCoefficient i 0) =
      lineSign r i • fiberCoefficient (permIndex r i) 0 := by decide +kernel

theorem basisChange_first (g : IntegralGL) (r : Fin 6) :
    augmentedLine (g * basisChange r) 0 = augmentedLine g 0 := by
  apply BadEdgeNormalForm.augmentedLine_mul_of_template
  rw [← GoodAugmentedNormalForm.rationalVector_integralTemplate,← rationalVector_mulVec]
  change rationalVector ((changeMatrix r).mulVec
    (GoodAugmentedNormalForm.integralTemplate 0)) = _
  rw [changeMatrix_first,GoodAugmentedNormalForm.rationalVector_integralTemplate]

/-- Each new coherent vertex is exactly the stipulated original rational line. -/
theorem basisChange_fiber (g : IntegralGL) (r : Fin 6) (i : Fin 3) :
    fiberLine (g * basisChange r) i 0 = fiberLine g (permIndex r i) 0 := by
  apply Subtype.ext
  change Submodule.span ℚ {(rationalRepresentation (g * basisChange r)
    (rationalVector (fiberCoefficient i 0)))} = _
  rw [map_mul,LinearEquiv.mul_apply,← rationalVector_mulVec]
  change Submodule.span ℚ {(rationalRepresentation g
    (rationalVector ((changeMatrix r).mulVec (fiberCoefficient i 0))))} = _
  rw [changeMatrix_coherent]
  have hc : rationalVector (lineSign r i • fiberCoefficient (permIndex r i) 0) =
      (lineSign r i : ℚ) • rationalVector (fiberCoefficient (permIndex r i) 0) := by
    funext j
    simp [rationalVector,Pi.smul_apply,smul_eq_mul]
  rw [hc,map_smul,Submodule.span_singleton_smul_eq
    (isUnit_iff_ne_zero.mpr (by exact_mod_cast lineSign_ne_zero r i))]
  rfl

/-- Each finite index order is genuinely a list permutation, independently of any vertex labels. -/
theorem permIndex_perm : ∀ r : Fin 6,
    ([permIndex r 0,permIndex r 1,permIndex r 2] : List (Fin 3)).Perm [0,1,2] := by
  decide +kernel

theorem permIndex_labels {V : Type*} (v : Fin 3 → V) (r : Fin 6) :
    ([v (permIndex r 0),v (permIndex r 1),v (permIndex r 2)] : List V).Perm
      [v 0,v 1,v 2] := by
  simpa only [List.map_cons,List.map_nil] using (permIndex_perm r).map v

/-- Every ordered permutation of three labels occurs in the literal six-entry table. -/
theorem exists_permIndex {V : Type*} (v : Fin 3 → V) (l : List V)
    (hl : l.Perm [v 0,v 1,v 2]) :
    ∃ r : Fin 6, l = [v (permIndex r 0),v (permIndex r 1),v (permIndex r 2)] := by
  have hm := List.mem_permutations'.mpr hl
  simp [List.permutations',List.permutations'Aux] at hm
  simp [Fin.exists_fin_succ,permIndex]
  tauto

/-- Every actual list permutation is exactly a coherent list in an actual adapted integral basis. -/
theorem exists_basis_of_perm (g : IntegralGL) (l : List RationalLine)
    (hl : l.Perm [xFiber g 0,yFiber g 0,zFiber g 0]) :
    ∃ h : IntegralGL, augmentedLine h 0 = augmentedLine g 0 ∧
      l = [xFiber h 0,yFiber h 0,zFiber h 0] := by
  obtain ⟨r,hr⟩ := exists_permIndex (fun i => fiberLine g i 0) l hl
  refine ⟨g * basisChange r,basisChange_first g r,?_⟩
  simpa only [xFiber,yFiber,zFiber,basisChange_fiber] using hr

/-- A permutation of the projected ordered triangle is realized by the same actual six bases. -/
theorem exists_basis_of_projected_perm (g₀ g : IntegralGL)
    (l : List RankTwoAugmentedFrames.RationalLine2)
    (hl : l.Perm [vertex g₀ (xFiber g 0),vertex g₀ (yFiber g 0),vertex g₀ (zFiber g 0)]) :
    ∃ h : IntegralGL, augmentedLine h 0 = augmentedLine g 0 ∧
      l = [vertex g₀ (xFiber h 0),vertex g₀ (yFiber h 0),vertex g₀ (zFiber h 0)] ∧
      [xFiber h 0,yFiber h 0,zFiber h 0].Perm [xFiber g 0,yFiber g 0,zFiber g 0] := by
  obtain ⟨r,hr⟩ := exists_permIndex (fun i => vertex g₀ (fiberLine g i 0)) l hl
  refine ⟨g * basisChange r,basisChange_first g r,?_,?_⟩
  · simpa only [xFiber,yFiber,zFiber,basisChange_fiber] using hr
  · simpa only [xFiber,yFiber,zFiber,basisChange_fiber] using
      permIndex_labels (fun i => fiberLine g i 0) r

/-- Actual Good coherent vertices force the exact residue hypotheses used by prism reduction. -/
theorem good_residues (g : IntegralGL) (hbad : ¬Good (augmentedLine g 0).val)
    (hg : ∀ i : Fin 3, Good (fiberLine g i 0).val) :
    AugmentedPrismCaps.columnResidue g 0 = 0 ∧
    AugmentedPrismCaps.columnResidue g 1 ≠ 0 ∧
    AugmentedPrismCaps.columnResidue g 2 ≠ 0 ∧
    AugmentedPrismCaps.columnResidue g 1 + AugmentedPrismCaps.columnResidue g 2 ≠ 0 := by
  have hx (i : Fin 3) := (chart_good_iff g hbad
    (RankTwoAugmentedFrames.integralTemplate i) (template_pair_primitive i) 0).mp
      (by rw [← prism_fiber_eq_chart]; exact hg i)
  refine ⟨AugmentedBadFaces.bad_augmentedLine_residue g 0 hbad,?_,?_,?_⟩
  · simpa [RankTwoAugmentedFrames.integralTemplate,AugmentedPrismCaps.columnResidue,
      AugmentedBadFaces.columnResidue] using hx 0
  · simpa [RankTwoAugmentedFrames.integralTemplate,AugmentedPrismCaps.columnResidue,
      AugmentedBadFaces.columnResidue] using hx 1
  · simpa [RankTwoAugmentedFrames.integralTemplate,AugmentedPrismCaps.columnResidue,
      AugmentedBadFaces.columnResidue] using hx 2

/-- Exact ordered normalization preserves all Good residue assumptions required downstream. -/
theorem exists_good_basis_of_perm (g : IntegralGL) (hbad : ¬Good (augmentedLine g 0).val)
    (hg : ∀ i : Fin 3, Good (fiberLine g i 0).val)
    (l : List RationalLine) (hl : l.Perm [xFiber g 0,yFiber g 0,zFiber g 0]) :
    ∃ h : IntegralGL, augmentedLine h 0 = augmentedLine g 0 ∧
      l = [xFiber h 0,yFiber h 0,zFiber h 0] ∧
      AugmentedPrismCaps.columnResidue h 0 = 0 ∧
      AugmentedPrismCaps.columnResidue h 1 ≠ 0 ∧
      AugmentedPrismCaps.columnResidue h 2 ≠ 0 ∧
      AugmentedPrismCaps.columnResidue h 1 + AugmentedPrismCaps.columnResidue h 2 ≠ 0 := by
  obtain ⟨h,hh,he⟩ := exists_basis_of_perm g l hl
  have hgood (i : Fin 3) : Good (fiberLine h i 0).val := by
    have hm : fiberLine h i 0 ∈ [xFiber h 0,yFiber h 0,zFiber h 0] := by
      fin_cases i <;> simp
    rw [← he] at hm
    have hgmem := hl.mem_iff.mp hm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hgmem
    rcases hgmem with h | h | h <;> rw [h]
    · exact hg 0
    · exact hg 1
    · exact hg 2
  exact ⟨h,hh,he,good_residues h (by rwa [hh]) hgood⟩

/-- The existing affine basis retains the distinguished first rational line exactly. -/
theorem affineBasis_first (g : IntegralGL) (p : ℤ × ℤ) :
    augmentedLine (affineBasis g p) 0 = augmentedLine g 0 := by
  apply Subtype.ext
  change Submodule.span ℚ {rationalRepresentation (affineBasis g p) (Pi.single (0 : Fin 3) 1)} =
    Submodule.span ℚ {rationalRepresentation g (Pi.single (0 : Fin 3) 1)}
  rw [AugmentedBadFaces.rationalRepresentation_basis,AugmentedBadFaces.rationalRepresentation_basis]
  apply congrArg (fun v : IntegralVector => Submodule.span ℚ {rationalVector v})
  funext i
  exact affineBasis_column_zero g p i

/-- Zero-height vertices in the affine basis are the actual coherent vertices with offsets p. -/
theorem affineBasis_fiber_zero (g : IntegralGL) (p : ℤ × ℤ) (i : Fin 3) :
    fiberLine (affineBasis g p) i 0 =
      fiberLine g i ((![p.1,p.2,p.1+p.2] : Fin 3 → ℤ) i) := by
  have hc : (shearGL p).val.mulVec (fiberCoefficient i 0) =
      fiberCoefficient i ((![p.1,p.2,p.1+p.2] : Fin 3 → ℤ) i) := by
    change (shearMatrix p).mulVec (fiberCoefficient i 0) = _
    fin_cases i <;> funext j <;> fin_cases j <;>
      simp [shearMatrix,fiberCoefficient,Matrix.mulVec,dotProduct,Fin.sum_univ_three]
  apply Subtype.ext
  change Submodule.span ℚ {(rationalRepresentation (g * shearGL p)
    (rationalVector (fiberCoefficient i 0)))} = _
  rw [map_mul,LinearEquiv.mul_apply,← rationalVector_mulVec,hc]
  rfl

/-- Every permutation of any coherent affine triangle has an exact zero-height basis presentation. -/
theorem exists_basis_of_affine_perm (g : IntegralGL) (p : ℤ × ℤ) (l : List RationalLine)
    (hl : l.Perm [xFiber g p.1,yFiber g p.2,zFiber g (p.1+p.2)]) :
    ∃ h : IntegralGL, augmentedLine h 0 = augmentedLine g 0 ∧
      l = [xFiber h 0,yFiber h 0,zFiber h 0] := by
  have hp : l.Perm [xFiber (affineBasis g p) 0,yFiber (affineBasis g p) 0,
      zFiber (affineBasis g p) 0] := by
    simpa only [xFiber,yFiber,zFiber,affineBasis_fiber_zero,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using hl
  obtain ⟨h,hh,he⟩ := exists_basis_of_perm (affineBasis g p) l hp
  exact ⟨h,hh.trans (affineBasis_first g p),he⟩

end TernaryPoly.CoherentFramePermutations
