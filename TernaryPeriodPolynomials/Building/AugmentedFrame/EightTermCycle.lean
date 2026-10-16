module

public import TernaryPeriodPolynomials.Building.Good.AugmentedNormalForm
public import TernaryPeriodPolynomials.Building.AugmentedFrame.SquareCaps
public import TernaryPeriodPolynomials.Building.OrientedChain.ChainProjection

@[expose] public section


noncomputable section
namespace TernaryPoly.AugmentedEightTermCycle
open ModThreeGoodAction AugmentedFrameComplex AugmentedBadFaces
open GoodIntegralNormalization GoodAugmentedNormalForm OrientedListChains

abbrev Mat := Matrix (Fin 3) (Fin 3) ℤ

/-- Integer coordinates of u,v,w,s=u+v,w2=w+u,q=v-w. -/
def cycleVector : Fin 6 → IntegralVector :=
  ![![1,0,0],![0,1,0],![0,0,1],![1,1,0],![1,0,1],![0,1,-1]]

private theorem cycleVector_primitive : ∀ i, Primitive (cycleVector i) := by
  unfold Primitive content
  decide +kernel

theorem cycleVector_ne_zero : ∀ i, rationalVector (cycleVector i) ≠ 0 := by decide +kernel

/-- The six actual rational lines of the universal eight-term construction. -/
def cycleLine (g : IntegralGL) (i : Fin 6) : RationalLine :=
  vectorLine (rationalRepresentation g (rationalVector (cycleVector i)))
    (fun h => cycleVector_ne_zero i ((rationalRepresentation g).injective
      (h.trans (map_zero (rationalRepresentation g)).symm)))

abbrev u (g : IntegralGL) := cycleLine g 0
abbrev v (g : IntegralGL) := cycleLine g 1
abbrev w (g : IntegralGL) := cycleLine g 2
abbrev s (g : IntegralGL) := cycleLine g 3
abbrev w2 (g : IntegralGL) := cycleLine g 4
abbrev q (g : IntegralGL) := cycleLine g 5

/-- Primitivity gives the exact lattice goodness criterion for all six actual lines. -/
theorem cycleLine_good_iff_residue (g : IntegralGL) (i : Fin 6) :
    Good (cycleLine g i).val ↔ ∑ j, (g.val.mulVec (cycleVector i) j : ZMod 3) ≠ 0 := by
  have h := good_span_iff_residue (primitive_mulVec g (cycleVector_primitive i))
  rw [rationalVector_mulVec] at h
  exact h

/-- Under the bad-core hypotheses, precisely w,w2,q are good and u,v,s are bad. -/
theorem cycleLine_good_iff (g : IntegralGL)
    (hu : columnResidue g 0 = 0) (hv : columnResidue g 1 = 0)
    (hw : columnResidue g 2 ≠ 0) (i : Fin 6) :
    Good (cycleLine g i).val ↔ i = 2 ∨ i = 4 ∨ i = 5 := by
  rw [cycleLine_good_iff_residue, AugmentedSquareCaps.residue_mulVec,
    Fin.sum_univ_three,hu,hv,zero_mul,zero_mul,zero_add,zero_add]
  have hf : ∀ r : ZMod 3, r ≠ 0 → ∀ j : Fin 6,
      (r * (cycleVector j 2 : ZMod 3) ≠ 0 ↔ j = 2 ∨ j = 4 ∨ j = 5) := by decide +kernel
  exact hf _ hw i

/-- The six actual line vertices are distinct for every integral basis. -/
theorem cycleLine_injective (g : IntegralGL) : Function.Injective (cycleLine g) := by
  intro i j h
  have hm : rationalRepresentation g (rationalVector (cycleVector i)) ∈
      Submodule.span ℚ {rationalRepresentation g (rationalVector (cycleVector j))} := by
    change rationalRepresentation g (rationalVector (cycleVector i)) ∈ (cycleLine g j).val
    rw [← h]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨r,hr⟩ := Submodule.mem_span_singleton.mp hm
  have hb : r • rationalVector (cycleVector j) = rationalVector (cycleVector i) := by
    apply (rationalRepresentation g).injective
    rw [map_smul]
    exact hr
  have hs := PrimitiveLineUniqueness.primitive_eq_or_neg_of_mem_span
    (cycleVector_primitive j) (cycleVector_primitive i) (Submodule.mem_span_singleton.mpr ⟨r,hb⟩)
  have hc : ∀ a b : Fin 6, (cycleVector a = cycleVector b ∨ cycleVector a = -cycleVector b) → a = b := by
    decide +kernel
  exact hc i j hs

@[simp] theorem cycleLine_inj (g : IntegralGL) (i j : Fin 6) :
    cycleLine g i = cycleLine g j ↔ i = j := (cycleLine_injective g).eq_iff

def basisMatrix : Fin 8 → Mat :=
  ![![![0,0,1],![0,1,1],![1,-1,0]],
    ![![1,0,0],![0,1,0],![0,0,1]],
    ![![0,1,1],![0,0,1],![1,0,0]],
    ![![0,0,1],![0,1,0],![1,-1,1]],
    ![![0,1,0],![1,0,0],![-1,1,1]],
    ![![0,1,0],![0,0,1],![1,0,0]],
    ![![0,1,0],![1,0,1],![-1,1,0]],
    ![![1,0,1],![0,1,0],![0,0,1]]]

def inverseMatrix : Fin 8 → Mat :=
  ![![![-1,1,1],![-1,1,0],![1,0,0]],
    ![![1,0,0],![0,1,0],![0,0,1]],
    ![![0,0,1],![1,-1,0],![0,1,0]],
    ![![-1,1,1],![0,1,0],![1,0,0]],
    ![![0,1,0],![1,0,0],![-1,1,1]],
    ![![0,0,1],![1,0,0],![0,1,0]],
    ![![1,0,-1],![1,0,0],![-1,1,1]],
    ![![1,0,-1],![0,1,0],![0,0,1]]]

def frameIndex : Fin 8 → Fin 4 → Fin 6 :=
  ![![2,5,3,1],![0,1,2,3],![2,0,3,4],![2,5,4,1],![5,4,2,3],![2,0,1,4],![5,4,1,3],![0,1,4,3]]

def determinantSigns : Fin 8 → ℤ := ![-1,1,1,-1,-1,1,-1,1]

theorem basisMatrix_mul_inverse : ∀ i, basisMatrix i * inverseMatrix i = 1 := by decide +kernel
theorem inverseMatrix_mul_basis : ∀ i, inverseMatrix i * basisMatrix i = 1 := by decide +kernel

/-- Eight explicit integral matrix units, one for each displayed tetrahedron. -/
def basisChange (i : Fin 8) : IntegralGL :=
  ⟨basisMatrix i,inverseMatrix i,basisMatrix_mul_inverse i,inverseMatrix_mul_basis i⟩

/-- The displayed basis changes have exact determinant signs ±1. -/
theorem basisMatrix_det : ∀ i, (basisMatrix i).det = determinantSigns i := by decide +kernel

private theorem basisMatrix_template : ∀ i j,
    (basisMatrix i).mulVec (GoodAugmentedNormalForm.integralTemplate j) =
      cycleVector (frameIndex i j) := by decide +kernel

/-- The literal augmented template maps to the four appropriate cycle vertices. -/
theorem basisChange_template (i : Fin 8) (j : Fin 4) :
    rationalRepresentation (basisChange i) (template j) =
      rationalVector (cycleVector (frameIndex i j)) := by
  rw [← rationalVector_integralTemplate, ← rationalVector_mulVec]
  exact congrArg rationalVector (basisMatrix_template i j)

/-- These are actual line equalities for every integral basis, not assumed face labels. -/
theorem augmentedLine_basisChange (g : IntegralGL) (i : Fin 8) (j : Fin 4) :
    augmentedLine (g * basisChange i) j = cycleLine g (frameIndex i j) := by
  apply Subtype.ext
  change Submodule.span ℚ {rationalRepresentation (g * basisChange i) (template j)} =
    Submodule.span ℚ {rationalRepresentation g (rationalVector (cycleVector (frameIndex i j)))}
  rw [map_mul]
  change Submodule.span ℚ {rationalRepresentation g (rationalRepresentation (basisChange i) (template j))} = _
  rw [basisChange_template]

/-- Exact ordered vertex lists of the eight tetrahedra. -/
def termList (g : IntegralGL) : Fin 8 → List RationalLine :=
  ![[w g,q g,v g,s g],[w g,v g,u g,s g],[w g,u g,w2 g,s g],
    [w g,q g,v g,w2 g],[w g,q g,w2 g,s g],[w g,v g,u g,w2 g],
    [q g,v g,w2 g,s g],[v g,u g,w2 g,s g]]

private theorem fin4_univ : (Finset.univ : Finset (Fin 4)) = {0,1,2,3} := by decide +kernel

/-- Each tetrahedron's vertices are precisely an explicit actual augmented frame. -/
theorem termList_toFinset (g : IntegralGL) (i : Fin 8) :
    (termList g i).toFinset = augmentedFrame (g * basisChange i) := by
  change (termList g i).toFinset = Finset.univ.image (augmentedLine (g * basisChange i))
  rw [show augmentedLine (g * basisChange i) = (fun j => cycleLine g (frameIndex i j)) from
    funext (augmentedLine_basisChange g i),fin4_univ]
  fin_cases i <;> ext L <;>
    simp [termList,frameIndex,u,v,w,s,w2,q,or_comm,or_left_comm,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.head_cons,Matrix.tail_cons]

/-- Every one of the eight displayed tetrahedra is an actual ambient augmented face. -/
theorem termList_ambient (g : IntegralGL) (i : Fin 8) : (termList g i).toFinset ∈ ambient := by
  rw [termList_toFinset]
  exact augmentedFrame_mem _

/-- Each displayed tetrahedron gives an actual ambient oriented four-vertex chain. -/
theorem term_simplex_mem (g : IntegralGL) (i : Fin 8) :
    simplex (termList g i) ∈ chains ambient 4 := by
  have hallowed : Allowed ambient (termList g i) := by
    apply Or.inr
    convert termList_ambient g i using 1
    ext L
    simp only [List.mem_toFinset]
  have hlen : (termList g i).length = 4 := by fin_cases i <;> rfl
  simpa only [hlen] using simplex_mem_chains ambient (termList g i) hallowed

/-- The actual eight-term absolute chain from the bad-triangle construction. -/
def Z (g : IntegralGL) : Chain RationalLine :=
  -simplex (termList g 0) - simplex (termList g 1) - simplex (termList g 2) +
    simplex (termList g 3) + simplex (termList g 4) + simplex (termList g 5) +
    simplex (termList g 6) + simplex (termList g 7)

/-- All eight terms have actual ambient support. -/
theorem Z_mem_chains (g : IntegralGL) : Z g ∈ chains ambient 4 := by
  unfold Z
  apply Submodule.add_mem
  · apply Submodule.add_mem
    · apply Submodule.add_mem
      · apply Submodule.add_mem
        · apply Submodule.add_mem
          · apply Submodule.sub_mem
            · exact (chains ambient 4).sub_mem
                ((chains ambient 4).neg_mem (term_simplex_mem g 0)) (term_simplex_mem g 1)
            · exact term_simplex_mem g 2
          · exact term_simplex_mem g 3
        · exact term_simplex_mem g 4
      · exact term_simplex_mem g 5
    · exact term_simplex_mem g 6
  · exact term_simplex_mem g 7

/-- Exact alternating-deletion cancellation proves the universal absolute cycle identity. -/
theorem boundary_Z (g : IntegralGL) : boundary (Z g) = 0 := by
  change boundary (-simplex [w g,q g,v g,s g] - simplex [w g,v g,u g,s g] -
    simplex [w g,u g,w2 g,s g] + simplex [w g,q g,v g,w2 g] +
    simplex [w g,q g,w2 g,s g] + simplex [w g,v g,u g,w2 g] +
    simplex [q g,v g,w2 g,s g] + simplex [v g,u g,w2 g,s g]) = 0
  simp only [map_neg,map_sub,map_add,boundary_cons,boundary_nil,map_zero,cons_simplex]
  abel

/-- The exact number of distinct bad vertices of each displayed tetrahedron. -/
theorem termList_badCount (g : IntegralGL)
    (hu : columnResidue g 0 = 0) (hv : columnResidue g 1 = 0)
    (hw : columnResidue g 2 ≠ 0) (i : Fin 8) :
    OrientedChainProjection.badCount (fun L : RationalLine => Good L.val) (termList g i) =
      (![2,3,2,1,1,2,2,3] : Fin 8 → ℕ) i := by
  classical
  fin_cases i <;>
    simp [OrientedChainProjection.badCount,OrientedChainProjection.badVertices,
      termList,u,v,w,s,w2,q,Finset.filter_insert,Finset.filter_singleton,
      cycleLine_good_iff g hu hv hw,cycleLine_inj,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.head_cons,Matrix.tail_cons]

/-- The exact three-bad-vertex component consists only of the two adjacent complement terms. -/
theorem leading_badCount_three (g : IntegralGL)
    (hu : columnResidue g 0 = 0) (hv : columnResidue g 1 = 0)
    (hw : columnResidue g 2 ≠ 0) :
    OrientedChainProjection.badCountProjection (fun L : RationalLine => Good L.val) 3 (Z g) =
      -simplex [w g,v g,u g,s g] + simplex [v g,u g,w2 g,s g] := by
  change OrientedChainProjection.badCountProjection (fun L : RationalLine => Good L.val) 3 (Z g) =
    -simplex (termList g 1) + simplex (termList g 7)
  simp only [Z,map_neg,map_sub,map_add,OrientedChainProjection.badCountProjection_simplex,
    termList_badCount g hu hv hw]
  have hcount : ∀ i : Fin 8, ((![2,3,2,1,1,2,2,3] : Fin 8 → ℕ) i = 3) ↔
      i = 1 ∨ i = 7 := by decide +kernel
  simp only [hcount]
  norm_num [Fin.ext_iff]

end TernaryPoly.AugmentedEightTermCycle
