module

public import TernaryPeriodPolynomials.Building.AugmentedFrame.BadFaces
public import TernaryPeriodPolynomials.Building.OrientedChain.ListChains
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.Field.ZMod

@[expose] public section


noncomputable section
namespace TernaryPoly.AugmentedSquareCaps
open ModThreeGoodAction AugmentedFrameComplex AugmentedBadFaces
open OrientedListChains

abbrev Mat := Matrix (Fin 3) (Fin 3) ℤ

/-- Integer coordinates of A=w, B=w+b, C=w+c, D=w+b+c, W=2w+b+c. -/
def capVector : Fin 5 → IntegralVector :=
  ![![0,0,1],![1,0,1],![0,1,1],![1,1,1],![1,1,2]]

theorem capVector_ne_zero (i : Fin 5) : rationalVector (capVector i) ≠ 0 := by
  intro h
  have hn : ∀ j : Fin 5, rationalVector (capVector j) 2 ≠ 0 := by decide +kernel
  exact hn i (congrFun h 2)

/-- The five actual rational lines after applying the displayed integral basis. -/
def capLine (g : IntegralGL) (i : Fin 5) : RationalLine :=
  vectorLine (rationalRepresentation g (rationalVector (capVector i)))
    (fun h => capVector_ne_zero i ((rationalRepresentation g).injective
      (h.trans (map_zero (rationalRepresentation g)).symm)))

abbrev A (g : IntegralGL) := capLine g 0
abbrev B (g : IntegralGL) := capLine g 1
abbrev C (g : IntegralGL) := capLine g 2
abbrev D (g : IntegralGL) := capLine g 3
abbrev W (g : IntegralGL) := capLine g 4

/-- The actual integral coordinate-sum residue is the column-residue pairing. -/
theorem residue_mulVec (g : IntegralGL) (v : IntegralVector) :
    (∑ i, (g.val.mulVec v i : ZMod 3)) =
      ∑ j, columnResidue g j * (v j : ZMod 3) := by
  simp only [Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul]
  rw [Finset.sum_comm]
  simp only [columnResidue, Finset.sum_mul]

/-- With two bad basis columns, every cap vertex has nonzero residue. -/
theorem capVector_residue_ne_zero (g : IntegralGL)
    (hb : columnResidue g 0 = 0) (hc : columnResidue g 1 = 0)
    (hw : columnResidue g 2 ≠ 0) (i : Fin 5) :
    (∑ j, (g.val.mulVec (capVector i) j : ZMod 3)) ≠ 0 := by
  rw [residue_mulVec, Fin.sum_univ_three, hb, hc, zero_mul, zero_mul, zero_add, zero_add]
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  apply mul_ne_zero hw
  fin_cases i <;> decide +kernel

/-- All five displayed lines are good, witnessed in the actual integral lattice. -/
theorem capLine_good (g : IntegralGL)
    (hb : columnResidue g 0 = 0) (hc : columnResidue g 1 = 0)
    (hw : columnResidue g 2 ≠ 0) (i : Fin 5) : Good (capLine g i).val := by
  refine ⟨g.val.mulVec (capVector i), ?_, capVector_residue_ne_zero g hb hc hw i⟩
  change rationalVector (g.val.mulVec (capVector i)) ∈
    Submodule.span ℚ {rationalRepresentation g (rationalVector (capVector i))}
  rw [rationalVector_mulVec]
  exact Submodule.mem_span_singleton_self _

/-- Explicit bases (B,C,D), (A,D,C), (A,D,B), and (B,C,A). -/
def capMatrix : Fin 4 → Mat :=
  ![![![1,0,1],![0,1,1],![1,1,1]],
    ![![0,1,0],![0,1,1],![1,1,1]],
    ![![0,1,1],![0,1,0],![1,1,1]],
    ![![1,0,0],![0,1,0],![1,1,1]]]

/-- Explicit integer inverses certify the four basis changes. -/
def capInverse : Fin 4 → Mat :=
  ![![![0,-1,1],![-1,0,1],![1,1,-1]],
    ![![0,-1,1],![1,0,0],![-1,1,0]],
    ![![-1,0,1],![0,1,0],![1,-1,0]],
    ![![1,0,0],![0,1,0],![-1,-1,1]]]

theorem capMatrix_mul_inverse : ∀ i, capMatrix i * capInverse i = 1 := by decide +kernel
theorem capInverse_mul_matrix : ∀ i, capInverse i * capMatrix i = 1 := by decide +kernel

/-- The four concrete unit matrices, including their actual integer inverses. -/
def capGL (i : Fin 4) : IntegralGL :=
  ⟨capMatrix i,capInverse i,capMatrix_mul_inverse i,capInverse_mul_matrix i⟩

/-- Their determinants are explicitly minus one, one, minus one, and one. -/
theorem capMatrix_det (i : Fin 4) : (capMatrix i).det = (![-1,1,-1,1] : Fin 4 → ℤ) i := by
  have h : ∀ j : Fin 4, (capMatrix j).det = (![-1,1,-1,1] : Fin 4 → ℤ) j := by
    decide +kernel
  exact h i

private def integralTemplate : Fin 4 → IntegralVector :=
  ![![1,0,0],![0,1,0],![0,0,1],![1,1,0]]

private theorem rationalVector_integralTemplate (i : Fin 4) :
    rationalVector (integralTemplate i) = template i := by
  have h : ∀ j : Fin 4, rationalVector (integralTemplate j) = template j := by decide +kernel
  exact h i

/-- Template indices for each displayed augmented frame; the final entry is its sum line W. -/
def capIndex : Fin 4 → Fin 4 → Fin 5 :=
  ![![1,2,3,4],![0,3,2,4],![0,3,1,4],![1,2,0,4]]

private theorem capMatrix_template :
    ∀ i j, (capMatrix i).mulVec (integralTemplate j) = capVector (capIndex i j) := by
  decide +kernel

/-- Each concrete basis change maps the augmented template to exactly the displayed cap vertices. -/
theorem capGL_template (i j : Fin 4) :
    rationalRepresentation (capGL i) (template j) = rationalVector (capVector (capIndex i j)) := by
  rw [← rationalVector_integralTemplate, ← rationalVector_mulVec]
  exact congrArg rationalVector (capMatrix_template i j)

/-- After any integral basis change, the cap vertices are still the exact augmented frame lines. -/
theorem augmentedLine_capGL (g : IntegralGL) (i j : Fin 4) :
    augmentedLine (g * capGL i) j = capLine g (capIndex i j) := by
  apply Subtype.ext
  change Submodule.span ℚ {rationalRepresentation (g * capGL i) (template j)} =
    Submodule.span ℚ {rationalRepresentation g (rationalVector (capVector (capIndex i j)))}
  rw [map_mul]
  change Submodule.span ℚ {rationalRepresentation g (rationalRepresentation (capGL i) (template j))} = _
  rw [capGL_template]

/-- The actual cap frame is precisely the image of the four displayed cap indices. -/
theorem augmentedFrame_capGL (g : IntegralGL) (i : Fin 4) :
    augmentedFrame (g * capGL i) = Finset.univ.image (fun j => capLine g (capIndex i j)) := by
  apply Finset.image_congr
  intro j _
  exact augmentedLine_capGL g i j

/-- Every displayed cap frame is a face of the actual good augmented complex. -/
theorem capFrame_good (g : IntegralGL)
    (hb : columnResidue g 0 = 0) (hc : columnResidue g 1 = 0)
    (hw : columnResidue g 2 ≠ 0) (i : Fin 4) :
    augmentedFrame (g * capGL i) ∈ AugmentedFrameComplex.good := by
  refine ⟨augmentedFrame_mem _, ?_⟩
  intro L hL
  rw [augmentedFrame_capGL] at hL
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hL
  exact capLine_good g hb hc hw _

/-- The four tetrahedron vertex sets, in the same order as the square-cap chain. -/
def capFace (g : IntegralGL) : Fin 4 → Finset RationalLine :=
  ![{W g,B g,C g,D g},{W g,A g,C g,D g},{W g,A g,B g,D g},{W g,A g,B g,C g}]

private theorem fin4_univ : (Finset.univ : Finset (Fin 4)) = {0,1,2,3} := by decide +kernel

/-- Each of the four displayed tetrahedra is literally the augmented frame of its explicit matrix. -/
theorem augmentedFrame_capGL_eq_face (g : IntegralGL) (i : Fin 4) :
    augmentedFrame (g * capGL i) = capFace g i := by
  rw [augmentedFrame_capGL, fin4_univ]
  fin_cases i <;> ext L <;>
    simp [capFace,capIndex,A,B,C,D,W,or_comm,or_left_comm,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.head_cons,Matrix.tail_cons]

/-- The four explicitly displayed tetrahedra are genuine good faces. -/
theorem capFace_good (g : IntegralGL)
    (hb : columnResidue g 0 = 0) (hc : columnResidue g 1 = 0)
    (hw : columnResidue g 2 ≠ 0) (i : Fin 4) : capFace g i ∈ AugmentedFrameComplex.good := by
  rw [← augmentedFrame_capGL_eq_face]
  exact capFrame_good g hb hc hw i

/-- The literal finite cap chain from the four actual augmented tetrahedra. -/
def squareCap (g : IntegralGL) : Chain RationalLine :=
  simplex [W g,B g,C g,D g] - simplex [W g,A g,C g,D g] +
    simplex [W g,A g,B g,D g] - simplex [W g,A g,B g,C g]

private theorem simplex_four_mem {a b c d : RationalLine}
    (h : {a,b,c,d} ∈ AugmentedFrameComplex.good) :
    simplex [a,b,c,d] ∈ chains AugmentedFrameComplex.good 4 := by
  refine simplex_mem_chains AugmentedFrameComplex.good [a,b,c,d] (Or.inr ?_)
  convert h using 1
  ext x
  simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false,Finset.mem_insert,Finset.mem_singleton]

/-- The square cap is supported on actual good tetrahedra. -/
theorem squareCap_mem_chains (g : IntegralGL)
    (hb : columnResidue g 0 = 0) (hc : columnResidue g 1 = 0)
    (hw : columnResidue g 2 ≠ 0) : squareCap g ∈ chains AugmentedFrameComplex.good 4 := by
  unfold squareCap
  exact (chains AugmentedFrameComplex.good 4).sub_mem
    ((chains AugmentedFrameComplex.good 4).add_mem
      ((chains AugmentedFrameComplex.good 4).sub_mem
        (simplex_four_mem (capFace_good g hb hc hw 0))
        (simplex_four_mem (capFace_good g hb hc hw 1)))
      (simplex_four_mem (capFace_good g hb hc hw 2)))
    (simplex_four_mem (capFace_good g hb hc hw 3))

/-- The alternating five-vertex deletion identity holds without any face or distinctness hypothesis. -/
theorem five_vertex_boundary {V : Type*} (w a b c d : V) :
    boundary (simplex [w,b,c,d] - simplex [w,a,c,d] +
      simplex [w,a,b,d] - simplex [w,a,b,c]) = boundary (simplex [a,b,c,d]) := by
  simp only [map_sub,map_add,boundary_cons,boundary_nil,map_zero,cons_simplex]
  abel

/-- The cap fills the square sphere; the omitted tetrahedron itself need not be a face. -/
theorem squareCap_boundary (g : IntegralGL) :
    boundary (squareCap g) = boundary (simplex [A g,B g,C g,D g]) :=
  five_vertex_boundary (W g) (A g) (B g) (C g) (D g)

/-- The square sphere is an actual good two-chain, as the boundary of its good cap. -/
theorem square_boundary_mem_chains (g : IntegralGL)
    (hb : columnResidue g 0 = 0) (hc : columnResidue g 1 = 0)
    (hw : columnResidue g 2 ≠ 0) :
    boundary (simplex [A g,B g,C g,D g]) ∈ chains AugmentedFrameComplex.good 3 := by
  rw [← squareCap_boundary]
  exact boundary_mem_chains AugmentedFrameComplex.good 3 (squareCap_mem_chains g hb hc hw)

end TernaryPoly.AugmentedSquareCaps
