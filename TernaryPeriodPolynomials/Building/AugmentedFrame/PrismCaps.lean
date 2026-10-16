module

public import TernaryPeriodPolynomials.Building.AugmentedFrame.FrameComplex
public import TernaryPeriodPolynomials.Building.OrientedChain.ListChains
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section

/-! A universal all-good prism cap built from an actual integral basis (b,X,Y).
The construction uses two explicitly invertible integral augmented frames and
the actual alternating-list boundary. It asserts no infinite-link generation. -/

noncomputable section
namespace TernaryPoly.AugmentedPrismCaps

open ModThreeGoodAction AugmentedFrameComplex OrientedListChains

abbrev Mat := Matrix (Fin 3) (Fin 3) ℤ

local instance : DecidableEq RationalLine := Classical.decEq _

/-- Coefficients of X,Y,X+Y,X+b,X+Y+b relative to the actual basis (b,X,Y). -/
def integralCoefficient : Fin 5 → IntegralVector :=
  ![![0,1,0], ![0,0,1], ![0,1,1], ![1,1,0], ![1,1,1]]

def coefficient (i : Fin 5) : Space := rationalVector (integralCoefficient i)

theorem coefficient_ne_zero (i : Fin 5) : coefficient i ≠ 0 := by
  fin_cases i <;> decide +kernel

/-- Actual integral vectors of the five prism vertices. -/
def integralVector (g : IntegralGL) (i : Fin 5) : IntegralVector :=
  g.val.mulVec (integralCoefficient i)

/-- Each actual vector is the promised sum of original basis columns. -/
theorem integralVector_eq_columns (g : IntegralGL) (i : Fin 5) :
    integralVector g i =
      ![(fun k => g.val k 1), (fun k => g.val k 2),
        (fun k => g.val k 1 + g.val k 2),
        (fun k => g.val k 0 + g.val k 1),
        (fun k => g.val k 0 + g.val k 1 + g.val k 2)] i := by
  fin_cases i <;> funext k <;>
    simp [integralVector, integralCoefficient, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- Actual rational lines; nonzero follows from the genuine integral basis action. -/
def prismLine (g : IntegralGL) (i : Fin 5) : RationalLine :=
  vectorLine (rationalRepresentation g (coefficient i))
    (fun h => coefficient_ne_zero i ((rationalRepresentation g).injective
      (h.trans (map_zero (rationalRepresentation g)).symm)))

abbrev xLine (g : IntegralGL) := prismLine g 0
abbrev yLine (g : IntegralGL) := prismLine g 1
abbrev zLine (g : IntegralGL) := prismLine g 2
abbrev xShiftLine (g : IntegralGL) := prismLine g 3
abbrev zShiftLine (g : IntegralGL) := prismLine g 4

/-- The displayed rational lines are literally the spans of the corresponding integral vectors. -/
theorem prismLine_val (g : IntegralGL) (i : Fin 5) :
    (prismLine g i).val = Submodule.span ℚ {rationalVector (integralVector g i)} := by
  change Submodule.span ℚ {rationalRepresentation g (rationalVector (integralCoefficient i))} = _
  rw [← rationalVector_mulVec]
  rfl

/-- Coordinate-sum residue of one of the original basis columns. -/
def columnResidue (g : IntegralGL) (j : Fin 3) : ZMod 3 := ∑ k, (g.val k j : ZMod 3)

/-- Linearity of the coordinate-sum residue in the integer coefficient vector. -/
theorem integralVector_residue_sum (g : IntegralGL) (i : Fin 5) :
    (∑ k, (integralVector g i k : ZMod 3)) =
      ∑ j, (integralCoefficient i j : ZMod 3) * columnResidue g j := by
  simp only [integralVector, Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul,
    columnResidue, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  exact mul_comm _ _

/-- The five residues are exactly those of X,Y,X+Y,X+b,X+Y+b. -/
theorem integralVector_residue (g : IntegralGL) (i : Fin 5) :
    (∑ k, (integralVector g i k : ZMod 3)) =
      ![columnResidue g 1, columnResidue g 2,
        columnResidue g 1 + columnResidue g 2,
        columnResidue g 0 + columnResidue g 1,
        columnResidue g 0 + columnResidue g 1 + columnResidue g 2] i := by
  rw [integralVector_residue_sum]
  fin_cases i <;> simp [integralCoefficient, Fin.sum_univ_three]

/-- Nonzero coordinate-sum residue proves the literal lattice-goodness predicate. -/
theorem prismLine_good_of_residue (g : IntegralGL) (i : Fin 5)
    (hi : (∑ k, (integralVector g i k : ZMod 3)) ≠ 0) : Good (prismLine g i).val := by
  refine ⟨integralVector g i, ?_, hi⟩
  rw [prismLine_val]
  exact Submodule.subset_span (Set.mem_singleton _)

/-- A bad first column and the three stipulated good residues make all five actual lines good. -/
theorem all_good (g : IntegralGL) (hb : columnResidue g 0 = 0)
    (hX : columnResidue g 1 ≠ 0) (hY : columnResidue g 2 ≠ 0)
    (hZ : columnResidue g 1 + columnResidue g 2 ≠ 0) (i : Fin 5) :
    Good (prismLine g i).val := by
  apply prismLine_good_of_residue
  rw [integralVector_residue]
  fin_cases i
  · exact hX
  · exact hY
  · exact hZ
  · change columnResidue g 0 + columnResidue g 1 ≠ 0
    simpa only [hb, zero_add] using hX
  · change columnResidue g 0 + columnResidue g 1 + columnResidue g 2 ≠ 0
    simpa only [hb, zero_add] using hZ

/-- The first augmented basis has columns X,Y,X+b. -/
def firstMatrix : Mat := ![![0,0,1], ![1,0,1], ![0,1,0]]
def firstInverse : Mat := ![![-1,1,0], ![0,0,1], ![1,0,0]]
def firstChange : IntegralGL :=
  ⟨firstMatrix, firstInverse, by decide +kernel, by decide +kernel⟩

/-- The second augmented basis has columns Y,X+b,X+Y. -/
def secondMatrix : Mat := ![![0,1,0], ![0,1,1], ![1,0,1]]
def secondInverse : Mat := ![![1,-1,1], ![1,0,0], ![-1,1,0]]
def secondChange : IntegralGL :=
  ⟨secondMatrix, secondInverse, by decide +kernel, by decide +kernel⟩

theorem firstMatrix_det : firstMatrix.det = 1 := by decide +kernel
theorem secondMatrix_det : secondMatrix.det = 1 := by decide +kernel

def firstOrder : Fin 4 → Fin 5 := ![0,1,3,2]
def secondOrder : Fin 4 → Fin 5 := ![1,3,2,4]

theorem firstChange_template (i : Fin 4) :
    rationalRepresentation firstChange (template i) = coefficient (firstOrder i) := by
  rw [rationalRepresentation_apply]
  fin_cases i <;> decide +kernel

theorem secondChange_template (i : Fin 4) :
    rationalRepresentation secondChange (template i) = coefficient (secondOrder i) := by
  rw [rationalRepresentation_apply]
  fin_cases i <;> decide +kernel

/-- The four first-frame vertices are exactly the stated prism vertices. -/
theorem augmentedLine_first (g : IntegralGL) (i : Fin 4) :
    augmentedLine (g * firstChange) i = prismLine g (firstOrder i) := by
  apply Subtype.ext
  change Submodule.span ℚ {rationalRepresentation (g * firstChange) (template i)} =
    Submodule.span ℚ {rationalRepresentation g (coefficient (firstOrder i))}
  rw [map_mul, LinearEquiv.mul_apply, firstChange_template]

/-- The four second-frame vertices are exactly the other stated prism vertices. -/
theorem augmentedLine_second (g : IntegralGL) (i : Fin 4) :
    augmentedLine (g * secondChange) i = prismLine g (secondOrder i) := by
  apply Subtype.ext
  change Submodule.span ℚ {rationalRepresentation (g * secondChange) (template i)} =
    Submodule.span ℚ {rationalRepresentation g (coefficient (secondOrder i))}
  rw [map_mul, LinearEquiv.mul_apply, secondChange_template]

def firstVertices (g : IntegralGL) : List RationalLine :=
  [xLine g, yLine g, zLine g, xShiftLine g]
def secondVertices (g : IntegralGL) : List RationalLine :=
  [yLine g, zLine g, xShiftLine g, zShiftLine g]

/-- The first displayed tetrahedron lies in the actual integral augmented-frame complex. -/
theorem firstVertices_ambient (g : IntegralGL) : (firstVertices g).toFinset ∈ ambient := by
  classical
  refine ⟨by simp [firstVertices], g * firstChange, ?_⟩
  have hm (i : Fin 4) : prismLine g (firstOrder i) ∈ augmentedFrame (g * firstChange) := by
    let : DecidableEq RationalLine := fun a b => Subtype.instDecidableEq a b
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, augmentedLine_first g i⟩
  intro L hL
  simp only [firstVertices, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hL
  rcases hL with rfl | rfl | rfl | rfl
  · exact hm 0
  · exact hm 1
  · exact hm 3
  · exact hm 2

/-- The second displayed tetrahedron lies in the actual integral augmented-frame complex. -/
theorem secondVertices_ambient (g : IntegralGL) : (secondVertices g).toFinset ∈ ambient := by
  classical
  refine ⟨by simp [secondVertices], g * secondChange, ?_⟩
  have hm (i : Fin 4) : prismLine g (secondOrder i) ∈ augmentedFrame (g * secondChange) := by
    let : DecidableEq RationalLine := fun a b => Subtype.instDecidableEq a b
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, augmentedLine_second g i⟩
  intro L hL
  simp only [secondVertices, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hL
  rcases hL with rfl | rfl | rfl | rfl
  · exact hm 0
  · exact hm 2
  · exact hm 1
  · exact hm 3

/-- The first tetrahedron belongs to the actual all-good subcomplex. -/
theorem firstVertices_good (g : IntegralGL) (hb : columnResidue g 0 = 0)
    (hX : columnResidue g 1 ≠ 0) (hY : columnResidue g 2 ≠ 0)
    (hZ : columnResidue g 1 + columnResidue g 2 ≠ 0) :
    (firstVertices g).toFinset ∈ good := by
  classical
  refine ⟨firstVertices_ambient g, ?_⟩
  intro L hL
  simp only [firstVertices, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hL
  rcases hL with rfl | rfl | rfl | rfl
  · exact all_good g hb hX hY hZ 0
  · exact all_good g hb hX hY hZ 1
  · exact all_good g hb hX hY hZ 2
  · exact all_good g hb hX hY hZ 3

/-- The second tetrahedron belongs to the actual all-good subcomplex. -/
theorem secondVertices_good (g : IntegralGL) (hb : columnResidue g 0 = 0)
    (hX : columnResidue g 1 ≠ 0) (hY : columnResidue g 2 ≠ 0)
    (hZ : columnResidue g 1 + columnResidue g 2 ≠ 0) :
    (secondVertices g).toFinset ∈ good := by
  classical
  refine ⟨secondVertices_ambient g, ?_⟩
  intro L hL
  simp only [secondVertices, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hL
  rcases hL with rfl | rfl | rfl | rfl
  · exact all_good g hb hX hY hZ 1
  · exact all_good g hb hX hY hZ 2
  · exact all_good g hb hX hY hZ 3
  · exact all_good g hb hX hY hZ 4

/-- The two oriented actual tetrahedra in the universal prism cap. -/
def prismCap (g : IntegralGL) : Chain RationalLine :=
  simplex (firstVertices g) + simplex (secondVertices g)

/-- The explicit six oriented triangles of the prism sphere. -/
def prismSphere (g : IntegralGL) : Chain RationalLine :=
  -simplex [xLine g, zLine g, xShiftLine g] +
    simplex [xLine g, yLine g, xShiftLine g] -
    simplex [xLine g, yLine g, zLine g] +
    simplex [zLine g, xShiftLine g, zShiftLine g] -
    simplex [yLine g, xShiftLine g, zShiftLine g] +
    simplex [yLine g, zLine g, zShiftLine g]

/-- Both summands of the prism cap are genuine all-good four-vertex simplex chains. -/
theorem prismCap_mem_chains (g : IntegralGL) (hb : columnResidue g 0 = 0)
    (hX : columnResidue g 1 ≠ 0) (hY : columnResidue g 2 ≠ 0)
    (hZ : columnResidue g 1 + columnResidue g 2 ≠ 0) : prismCap g ∈ chains good 4 := by
  apply (chains good 4).add_mem
  · exact simplex_mem_chains good (firstVertices g)
      (Or.inr (firstVertices_good g hb hX hY hZ))
  · exact simplex_mem_chains good (secondVertices g)
      (Or.inr (secondVertices_good g hb hX hY hZ))

/-- The common face cancels in the actual oriented-chain boundary. -/
theorem boundary_prismCap (g : IntegralGL) : boundary (prismCap g) = prismSphere g := by
  simp only [prismCap, firstVertices, secondVertices, map_add, boundary_cons,
    boundary_nil, map_sub, map_zero, cons_simplex, sub_zero]
  unfold prismSphere
  abel

/-- The explicit six-face sphere belongs to the genuine good three-vertex chain module. -/
theorem prismSphere_mem_chains (g : IntegralGL) (hb : columnResidue g 0 = 0)
    (hX : columnResidue g 1 ≠ 0) (hY : columnResidue g 2 ≠ 0)
    (hZ : columnResidue g 1 + columnResidue g 2 ≠ 0) : prismSphere g ∈ chains good 3 := by
  rw [← boundary_prismCap]
  exact boundary_mem_chains good 3 (prismCap_mem_chains g hb hX hY hZ)

/-- The prism sphere is an actual cycle, as the displayed cap proves directly. -/
theorem boundary_prismSphere (g : IntegralGL) : boundary (prismSphere g) = 0 := by
  rw [← boundary_prismCap]
  exact boundary_squared (prismCap g)

end TernaryPoly.AugmentedPrismCaps
