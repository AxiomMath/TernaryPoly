module

public import TernaryPeriodPolynomials.Building.AugmentedFrame.PrismCaps
public import TernaryPeriodPolynomials.Building.Integer.Exactness
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Tauto

@[expose] public section


noncomputable section
namespace TernaryPoly.CoherentPrismReduction
open ModThreeGoodAction AugmentedFrameComplex OrientedListChains
open AugmentedPrismCaps

local instance : DecidableEq RationalLine := Classical.decEq _

/-- The three actual affine integer fibers over the quotient augmented triangle. -/
def fiberCoefficient (i : Fin 3) (k : ℤ) : IntegralVector :=
  ![![k,1,0],![k,0,1],![k,1,1]] i

theorem fiberCoefficient_ne_zero (i : Fin 3) (k : ℤ) :
    rationalVector (fiberCoefficient i k) ≠ 0 := by
  intro h
  fin_cases i
  · have he := congrFun h 1
    change (1 : ℚ) = 0 at he
    exact one_ne_zero he
  · have he := congrFun h 2
    change (1 : ℚ) = 0 at he
    exact one_ne_zero he
  · have he := congrFun h 1
    change (1 : ℚ) = 0 at he
    exact one_ne_zero he

def fiberLine (g : IntegralGL) (i : Fin 3) (k : ℤ) : RationalLine :=
  vectorLine (rationalRepresentation g (rationalVector (fiberCoefficient i k)))
    (fun h => fiberCoefficient_ne_zero i k ((rationalRepresentation g).injective
      (h.trans (map_zero (rationalRepresentation g)).symm)))

abbrev xFiber (g : IntegralGL) := fiberLine g 0
abbrev yFiber (g : IntegralGL) := fiberLine g 1
abbrev zFiber (g : IntegralGL) := fiberLine g 2

theorem fiberLine_val (g : IntegralGL) (i : Fin 3) (k : ℤ) :
    (fiberLine g i k).val =
      Submodule.span ℚ {rationalVector (g.val.mulVec (fiberCoefficient i k))} := by
  change Submodule.span ℚ {(rationalRepresentation g
    (rationalVector (fiberCoefficient i k)))} = _
  rw [← rationalVector_mulVec]

def shearMatrix (p : ℤ × ℤ) : Mat := !![1,p.1,p.2;0,1,0;0,0,1]

theorem shearMatrix_det (p : ℤ × ℤ) : (shearMatrix p).det = 1 := by
  simp [shearMatrix,Matrix.det_fin_three]

def shearGL (p : ℤ × ℤ) : IntegralGL :=
  Matrix.nonsingInvUnit (shearMatrix p) (by rw [shearMatrix_det]; exact isUnit_one)

def affineBasis (g : IntegralGL) (p : ℤ × ℤ) : IntegralGL := g * shearGL p

/-- Swap only the two good columns, preserving the bad first column. -/
def swapMatrix : Mat := !![1,0,0;0,0,1;0,1,0]
def swapGL : IntegralGL := ⟨swapMatrix,swapMatrix,by decide +kernel,by decide +kernel⟩

theorem affineBasis_column_zero (g : IntegralGL) (p : ℤ × ℤ) (r : Fin 3) :
    (affineBasis g p).val r 0 = g.val r 0 := by
  change (g.val * shearMatrix p) r 0 = _
  simp [Matrix.mul_apply,Fin.sum_univ_three,shearMatrix]

theorem affineBasis_column_one (g : IntegralGL) (p : ℤ × ℤ) (r : Fin 3) :
    (affineBasis g p).val r 1 = g.val r 0 * p.1 + g.val r 1 := by
  change (g.val * shearMatrix p) r 1 = _
  simp [Matrix.mul_apply,Fin.sum_univ_three,shearMatrix]

theorem affineBasis_column_two (g : IntegralGL) (p : ℤ × ℤ) (r : Fin 3) :
    (affineBasis g p).val r 2 = g.val r 0 * p.2 + g.val r 2 := by
  change (g.val * shearMatrix p) r 2 = _
  simp [Matrix.mul_apply,Fin.sum_univ_three,shearMatrix]

theorem affineBasis_residue_zero (g : IntegralGL) (p : ℤ × ℤ) :
    columnResidue (affineBasis g p) 0 = columnResidue g 0 := by
  simp only [columnResidue,affineBasis_column_zero]

theorem affineBasis_residue_one (g : IntegralGL) (p : ℤ × ℤ) :
    columnResidue (affineBasis g p) 1 =
      columnResidue g 0 * (p.1 : ZMod 3) + columnResidue g 1 := by
  simp only [columnResidue,affineBasis_column_one,Int.cast_add,Int.cast_mul,
    Finset.sum_add_distrib,Finset.sum_mul]

theorem affineBasis_residue_two (g : IntegralGL) (p : ℤ × ℤ) :
    columnResidue (affineBasis g p) 2 =
      columnResidue g 0 * (p.2 : ZMod 3) + columnResidue g 2 := by
  simp only [columnResidue,affineBasis_column_two,Int.cast_add,Int.cast_mul,
    Finset.sum_add_distrib,Finset.sum_mul]

theorem swapGL_residue (g : IntegralGL) (j : Fin 3) :
    columnResidue (g * swapGL) j =
      columnResidue g ((![0,2,1] : Fin 3 → Fin 3) j) := by
  unfold columnResidue
  congr 1
  funext r
  congr 1
  change (g.val * swapMatrix) r j = _
  fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_three,swapMatrix]

/-- The five prism vertices in their literal affine fiber coordinates. -/
def prismFiber (i : Fin 5) : Fin 3 := ![0,1,2,0,2] i
def prismIndex (p : ℤ × ℤ) (i : Fin 5) : ℤ :=
  ![p.1,p.2,p.1+p.2,p.1+1,p.1+p.2+1] i

theorem shear_prismCoefficient (p : ℤ × ℤ) (i : Fin 5) :
    (shearGL p).val.mulVec (integralCoefficient i) =
      fiberCoefficient (prismFiber i) (prismIndex p i) := by
  change (shearMatrix p).mulVec (integralCoefficient i) = _
  fin_cases i <;> funext r <;> fin_cases r <;>
    simp [shearMatrix,integralCoefficient,fiberCoefficient,prismFiber,prismIndex,
      Matrix.mulVec,dotProduct,Fin.sum_univ_three] <;> ring

theorem prismLine_affineBasis (g : IntegralGL) (p : ℤ × ℤ) (i : Fin 5) :
    prismLine (affineBasis g p) i =
      fiberLine g (prismFiber i) (prismIndex p i) := by
  apply Subtype.ext
  change Submodule.span ℚ {(rationalRepresentation (g * shearGL p)
    (rationalVector (integralCoefficient i)))} = _
  rw [map_mul,LinearEquiv.mul_apply,← rationalVector_mulVec,shear_prismCoefficient]
  rfl

theorem swap_fiberCoefficient (i : Fin 3) (k : ℤ) :
    swapGL.val.mulVec (fiberCoefficient i k) =
      fiberCoefficient ((![1,0,2] : Fin 3 → Fin 3) i) k := by
  change swapMatrix.mulVec (fiberCoefficient i k) = _
  fin_cases i <;> funext r <;> fin_cases r <;>
    simp [swapMatrix,fiberCoefficient,Matrix.mulVec,dotProduct,Fin.sum_univ_three]

theorem fiberLine_swap (g : IntegralGL) (i : Fin 3) (k : ℤ) :
    fiberLine (g * swapGL) i k =
      fiberLine g ((![1,0,2] : Fin 3 → Fin 3) i) k := by
  apply Subtype.ext
  change Submodule.span ℚ {(rationalRepresentation (g * swapGL)
    (rationalVector (fiberCoefficient i k)))} = _
  rw [map_mul,LinearEquiv.mul_apply,← rationalVector_mulVec,swap_fiberCoefficient]
  rfl

/-- One actual coherent lift of the quotient augmented triangle. -/
def coherent (g : IntegralGL) (p : ℤ × ℤ) : Chain RationalLine :=
  simplex [xFiber g p.1,yFiber g p.2,zFiber g (p.1+p.2)]

/-- All orderings of a literal adjacent-fiber triangle are generators. -/
def MixedGenerator (g : IntegralGL) (c : Chain RationalLine) : Prop :=
  ∃ (i j : Fin 3) (k l : ℤ), i ≠ j ∧
    (c = simplex [fiberLine g i k,fiberLine g i (k+1),fiberLine g j l] ∨
     c = simplex [fiberLine g i k,fiberLine g j l,fiberLine g i (k+1)] ∨
     c = simplex [fiberLine g i (k+1),fiberLine g i k,fiberLine g j l] ∨
     c = simplex [fiberLine g i (k+1),fiberLine g j l,fiberLine g i k] ∨
     c = simplex [fiberLine g j l,fiberLine g i k,fiberLine g i (k+1)] ∨
     c = simplex [fiberLine g j l,fiberLine g i (k+1),fiberLine g i k])

/-- This span is defined by actual adjacent-fiber triangles, independently of prism residuals. -/
def MixedSpan (g : IntegralGL) : Submodule ℚ (Chain RationalLine) :=
  Submodule.span ℚ {c | MixedGenerator g c}

def horizontalCap (g : IntegralGL) (p : ℤ × ℤ) : Chain RationalLine :=
  prismCap (affineBasis g p)

def verticalCap (g : IntegralGL) (p : ℤ × ℤ) : Chain RationalLine :=
  -prismCap (affineBasis (g * swapGL) (p.2,p.1))

/-- The four side faces with signs moved to the residual side of the horizontal identity. -/
def horizontalResidual (g : IntegralGL) (p : ℤ × ℤ) : Chain RationalLine :=
  simplex [xFiber g p.1,zFiber g (p.1+p.2),xFiber g (p.1+1)] -
  simplex [xFiber g p.1,yFiber g p.2,xFiber g (p.1+1)] -
  simplex [zFiber g (p.1+p.2),xFiber g (p.1+1),zFiber g (p.1+p.2+1)] -
  simplex [yFiber g p.2,zFiber g (p.1+p.2),zFiber g (p.1+p.2+1)]

/-- The vertical residual includes the required global minus sign after swapping X and Y. -/
def verticalResidual (g : IntegralGL) (p : ℤ × ℤ) : Chain RationalLine :=
  -horizontalResidual (g * swapGL) (p.2,p.1)

theorem horizontal_identity (g : IntegralGL) (p : ℤ × ℤ) :
    coherent g (p.1+1,p.2) - coherent g p =
      boundary (horizontalCap g p) + horizontalResidual g p := by
  rw [horizontalCap,boundary_prismCap]
  simp only [prismSphere,xLine,yLine,zLine,xShiftLine,zShiftLine,prismLine_affineBasis]
  change simplex [xFiber g (p.1+1),yFiber g p.2,zFiber g ((p.1+1)+p.2)] -
    simplex [xFiber g p.1,yFiber g p.2,zFiber g (p.1+p.2)] =
    -simplex [xFiber g p.1,zFiber g (p.1+p.2),xFiber g (p.1+1)] +
    simplex [xFiber g p.1,yFiber g p.2,xFiber g (p.1+1)] -
    simplex [xFiber g p.1,yFiber g p.2,zFiber g (p.1+p.2)] +
    simplex [zFiber g (p.1+p.2),xFiber g (p.1+1),zFiber g (p.1+p.2+1)] -
    simplex [yFiber g p.2,xFiber g (p.1+1),zFiber g (p.1+p.2+1)] +
    simplex [yFiber g p.2,zFiber g (p.1+p.2),zFiber g (p.1+p.2+1)] + horizontalResidual g p
  rw [show (p.1+1)+p.2 = p.1+p.2+1 by ring,
    simplex_swap_eq_neg (yFiber g p.2) (xFiber g (p.1+1))]
  unfold horizontalResidual
  abel

theorem coherent_swap (g : IntegralGL) (p : ℤ × ℤ) :
    coherent (g * swapGL) (p.2,p.1) = -coherent g p := by
  simp only [coherent,xFiber,yFiber,zFiber,fiberLine_swap]
  change simplex [yFiber g p.2,xFiber g p.1,zFiber g (p.2+p.1)] = _
  rw [add_comm p.2 p.1]
  exact simplex_swap_eq_neg _ _ _

theorem vertical_identity (g : IntegralGL) (p : ℤ × ℤ) :
    coherent g (p.1,p.2+1) - coherent g p =
      boundary (verticalCap g p) + verticalResidual g p := by
  have h := horizontal_identity (g * swapGL) (p.2,p.1)
  have h1 := coherent_swap g (p.1,p.2+1)
  have h0 := coherent_swap g p
  change coherent (g * swapGL) (p.2+1,p.1) = _ at h1
  rw [h1,h0] at h
  simp only [verticalCap,verticalResidual,map_neg,horizontalCap] at *
  convert congrArg Neg.neg h using 1 <;> abel

theorem horizontalResidual_mem (g : IntegralGL) (p : ℤ × ℤ) :
    horizontalResidual g p ∈ MixedSpan g := by
  have h1 : simplex [xFiber g p.1,zFiber g (p.1+p.2),xFiber g (p.1+1)] ∈ MixedSpan g := by
    apply Submodule.subset_span
    exact ⟨0,2,p.1,p.1+p.2,by decide,Or.inr (Or.inl rfl)⟩
  have h2 : simplex [xFiber g p.1,yFiber g p.2,xFiber g (p.1+1)] ∈ MixedSpan g := by
    apply Submodule.subset_span
    exact ⟨0,1,p.1,p.2,by decide,Or.inr (Or.inl rfl)⟩
  have h3 : simplex [zFiber g (p.1+p.2),xFiber g (p.1+1),zFiber g (p.1+p.2+1)] ∈ MixedSpan g := by
    apply Submodule.subset_span
    exact ⟨2,0,p.1+p.2,p.1+1,by decide,Or.inr (Or.inl rfl)⟩
  have h4 : simplex [yFiber g p.2,zFiber g (p.1+p.2),zFiber g (p.1+p.2+1)] ∈ MixedSpan g := by
    apply Submodule.subset_span
    exact ⟨2,1,p.1+p.2,p.2,by decide,Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩
  exact (MixedSpan g).sub_mem ((MixedSpan g).sub_mem ((MixedSpan g).sub_mem h1 h2) h3) h4

theorem MixedSpan_swap_le (g : IntegralGL) : MixedSpan (g * swapGL) ≤ MixedSpan g := by
  apply Submodule.span_le.mpr
  rintro c ⟨i,j,k,l,hij,hc⟩
  apply Submodule.subset_span
  have hinj : Function.Injective (![1,0,2] : Fin 3 → Fin 3) := by decide +kernel
  refine ⟨(![1,0,2] : Fin 3 → Fin 3) i,(![1,0,2] : Fin 3 → Fin 3) j,k,l,
    fun h => hij (hinj h),?_⟩
  simpa only [fiberLine_swap] using hc

theorem verticalResidual_mem (g : IntegralGL) (p : ℤ × ℤ) :
    verticalResidual g p ∈ MixedSpan g :=
  (MixedSpan g).neg_mem (MixedSpan_swap_le g (horizontalResidual_mem (g * swapGL) (p.2,p.1)))

theorem horizontalCap_mem (g : IntegralGL) (hb : columnResidue g 0 = 0)
    (hX : columnResidue g 1 ≠ 0) (hY : columnResidue g 2 ≠ 0)
    (hZ : columnResidue g 1 + columnResidue g 2 ≠ 0) (p : ℤ × ℤ) :
    horizontalCap g p ∈ chains good 4 := by
  apply prismCap_mem_chains
  · rwa [affineBasis_residue_zero]
  · simpa only [affineBasis_residue_one,hb,zero_mul,zero_add] using hX
  · simpa only [affineBasis_residue_two,hb,zero_mul,zero_add] using hY
  · simpa only [affineBasis_residue_one,affineBasis_residue_two,hb,zero_mul,zero_add] using hZ

theorem verticalCap_mem (g : IntegralGL) (hb : columnResidue g 0 = 0)
    (hX : columnResidue g 1 ≠ 0) (hY : columnResidue g 2 ≠ 0)
    (hZ : columnResidue g 1 + columnResidue g 2 ≠ 0) (p : ℤ × ℤ) :
    verticalCap g p ∈ chains good 4 := by
  apply (chains good 4).neg_mem
  apply horizontalCap_mem (g * swapGL)
  · rw [swapGL_residue]; exact hb
  · rw [swapGL_residue]; exact hY
  · rw [swapGL_residue]; exact hX
  · rw [swapGL_residue,swapGL_residue]
    change columnResidue g 2 + columnResidue g 1 ≠ 0
    rwa [add_comm]

/-- Coherent triangles extended to arbitrary finitely supported rational coefficients. -/
def coherentLinear (g : IntegralGL) : IntegerGridExactness.C₀ →ₗ[ℚ] Chain RationalLine :=
  Finsupp.linearCombination ℚ (coherent g)

@[simp] theorem coherentLinear_vertex (g : IntegralGL) (p : IntegerGridExactness.Vertex) :
    coherentLinear g (IntegerGridExactness.vertex p) = coherent g p := by
  simp [coherentLinear,IntegerGridExactness.vertex]

/-- The actual Good cap attached to a positive parameter-grid edge. -/
def neighborCap (g : IntegralGL) (e : IntegerGridExactness.Edge) : Chain RationalLine :=
  if e.2 = 0 then horizontalCap g e.1 else verticalCap g e.1

def neighborResidual (g : IntegralGL) (e : IntegerGridExactness.Edge) : Chain RationalLine :=
  if e.2 = 0 then horizontalResidual g e.1 else verticalResidual g e.1

def capLinear (g : IntegralGL) : IntegerGridExactness.C₁ →ₗ[ℚ] Chain RationalLine :=
  Finsupp.linearCombination ℚ (neighborCap g)

def residualLinear (g : IntegralGL) : IntegerGridExactness.C₁ →ₗ[ℚ] Chain RationalLine :=
  Finsupp.linearCombination ℚ (neighborResidual g)

theorem neighbor_identity (g : IntegralGL) (e : IntegerGridExactness.Edge) :
    coherent g (IntegerGridExactness.edgeHead e) - coherent g e.1 =
      boundary (neighborCap g e) + neighborResidual g e := by
  rcases e with ⟨p,d⟩
  fin_cases d
  · exact horizontal_identity g p
  · exact vertical_identity g p

theorem capLinear_mem (g : IntegralGL) (hb : columnResidue g 0 = 0)
    (hX : columnResidue g 1 ≠ 0) (hY : columnResidue g 2 ≠ 0)
    (hZ : columnResidue g 1 + columnResidue g 2 ≠ 0) (a : IntegerGridExactness.C₁) :
    capLinear g a ∈ chains good 4 := by
  induction a using Finsupp.induction_linear with
  | zero => simpa only [map_zero] using (chains good 4).zero_mem
  | add a b ha hb' => simpa only [map_add] using (chains good 4).add_mem ha hb'
  | single e q =>
    rw [capLinear,Finsupp.linearCombination_single]
    apply (chains good 4).smul_mem
    unfold neighborCap
    split
    · exact horizontalCap_mem g hb hX hY hZ e.1
    · exact verticalCap_mem g hb hX hY hZ e.1

theorem residualLinear_mem (g : IntegralGL) (a : IntegerGridExactness.C₁) :
    residualLinear g a ∈ MixedSpan g := by
  induction a using Finsupp.induction_linear with
  | zero => simpa only [map_zero] using (MixedSpan g).zero_mem
  | add a b ha hb => simpa only [map_add] using (MixedSpan g).add_mem ha hb
  | single e q =>
    rw [residualLinear,Finsupp.linearCombination_single]
    apply (MixedSpan g).smul_mem
    unfold neighborResidual
    split
    · exact horizontalResidual_mem g e.1
    · exact verticalResidual_mem g e.1

/-- The actual prism-boundary equation is compatible with the grid incidence map. -/
theorem linear_neighbor_identity (g : IntegralGL) (a : IntegerGridExactness.C₁) :
    coherentLinear g (IntegerGridExactness.boundary₁ a) =
      boundary (capLinear g a) + residualLinear g a := by
  induction a using Finsupp.induction_linear with
  | zero => simp only [map_zero,add_zero]
  | add a b ha hb => simp only [map_add,ha,hb]; abel
  | single e q =>
    rw [IntegerGridExactness.boundary₁_single,map_smul,map_sub,
      coherentLinear_vertex,coherentLinear_vertex,neighbor_identity]
    simp only [capLinear,residualLinear,Finsupp.linearCombination_single,map_smul,smul_add]

/-- A completely explicit finite reduction, including the augmentation term at the origin. -/
theorem coherent_reduction (g : IntegralGL) (a : IntegerGridExactness.C₀) :
    coherentLinear g a - IntegerGridExactness.augmentation a • coherent g (0,0) =
      boundary (capLinear g (IntegerGridExactness.pathLinear a)) +
        residualLinear g (IntegerGridExactness.pathLinear a) := by
  have h := linear_neighbor_identity g (IntegerGridExactness.pathLinear a)
  rwa [IntegerGridExactness.boundary₁_pathLinear,map_sub,map_smul,coherentLinear_vertex] at h

/-- Every finite augmentation-zero coherent combination reduces to actual Good boundaries and
literal adjacent-fiber mixed triangles. No global chart or projection hypothesis is assumed. -/
theorem coherent_augmentation_zero (g : IntegralGL) (hb : columnResidue g 0 = 0)
    (hX : columnResidue g 1 ≠ 0) (hY : columnResidue g 2 ≠ 0)
    (hZ : columnResidue g 1 + columnResidue g 2 ≠ 0) (a : IntegerGridExactness.C₀)
    (ha : IntegerGridExactness.augmentation a = 0) :
    ∃ t r : Chain RationalLine, t ∈ chains good 4 ∧ r ∈ MixedSpan g ∧
      coherentLinear g a = boundary t + r := by
  refine ⟨capLinear g (IntegerGridExactness.pathLinear a),
    residualLinear g (IntegerGridExactness.pathLinear a),
    capLinear_mem g hb hX hY hZ _,residualLinear_mem g _,?_⟩
  simpa only [ha,zero_smul,sub_zero] using coherent_reduction g a

/-- The affine fiber vectors are literally integer sums of the basis columns. -/
theorem fiberVector_columns (g : IntegralGL) (i : Fin 3) (k : ℤ) :
    g.val.mulVec (fiberCoefficient i k) =
      ![(fun r => g.val r 0 * k + g.val r 1),
        (fun r => g.val r 0 * k + g.val r 2),
        (fun r => g.val r 0 * k + g.val r 1 + g.val r 2)] i := by
  fin_cases i <;> funext r <;>
    simp [fiberCoefficient,Matrix.mulVec,dotProduct,Fin.sum_univ_three]

theorem fiberVector_residue (g : IntegralGL) (i : Fin 3) (k : ℤ) :
    (∑ r, (g.val.mulVec (fiberCoefficient i k) r : ZMod 3)) =
      columnResidue g 0 * (k : ZMod 3) +
        (![columnResidue g 1,columnResidue g 2,columnResidue g 1 + columnResidue g 2] i) := by
  rw [fiberVector_columns]
  fin_cases i <;>
    simp [columnResidue,Int.cast_add,Int.cast_mul,Finset.sum_add_distrib,Finset.sum_mul,add_assoc]

theorem fiberLine_good (g : IntegralGL) (hb : columnResidue g 0 = 0)
    (hX : columnResidue g 1 ≠ 0) (hY : columnResidue g 2 ≠ 0)
    (hZ : columnResidue g 1 + columnResidue g 2 ≠ 0) (i : Fin 3) (k : ℤ) :
    Good (fiberLine g i k).val := by
  refine ⟨g.val.mulVec (fiberCoefficient i k),?_,?_⟩
  · rw [fiberLine_val]
    exact Submodule.mem_span_singleton_self _
  · rw [fiberVector_residue,hb,zero_mul,zero_add]
    fin_cases i
    · exact hX
    · exact hY
    · exact hZ

/-- The actual basis with columns b, the selected fiber point, and a different-fiber point. -/
def mixedMatrix (i j : Fin 3) (k l : ℤ) : Mat :=
  !![1,k,l;0,fiberCoefficient i k 1,fiberCoefficient j l 1;
    0,fiberCoefficient i k 2,fiberCoefficient j l 2]

theorem mixedMatrix_unit (i j : Fin 3) (hij : i ≠ j) (k l : ℤ) :
    IsUnit (mixedMatrix i j k l).det := by
  rw [Matrix.det_fin_three]
  change IsUnit (1 * fiberCoefficient i k 1 * fiberCoefficient j l 2 -
    1 * fiberCoefficient j l 1 * fiberCoefficient i k 2 -
    k * 0 * fiberCoefficient j l 2 + k * fiberCoefficient j l 1 * 0 +
    l * 0 * fiberCoefficient i k 2 - l * fiberCoefficient i k 1 * 0)
  simp only [one_mul,mul_zero,zero_mul,sub_zero,add_zero]
  fin_cases i <;> fin_cases j <;>
    first | exact (hij rfl).elim | exact isUnit_one | exact isUnit_neg_one

def mixedGL (i j : Fin 3) (hij : i ≠ j) (k l : ℤ) : IntegralGL :=
  Matrix.nonsingInvUnit (mixedMatrix i j k l) (mixedMatrix_unit i j hij k l)

private def intTemplate : Fin 4 → IntegralVector :=
  ![![1,0,0],![0,1,0],![0,0,1],![1,1,0]]

private theorem template_eq_intTemplate (u : Fin 4) :
    template u = rationalVector (intTemplate u) := by
  fin_cases u <;> decide +kernel

private theorem mixedGL_mulVec (i j : Fin 3) (hij : i ≠ j) (k l : ℤ) (u : Fin 4) :
    (mixedGL i j hij k l).val.mulVec (intTemplate u) =
      (![Pi.single 0 1,fiberCoefficient i k,fiberCoefficient j l,fiberCoefficient i (k+1)] :
        Fin 4 → IntegralVector) u := by
  change (mixedMatrix i j k l).mulVec (intTemplate u) = _
  fin_cases u <;> funext r <;> fin_cases r <;>
    simp [mixedMatrix,intTemplate,Matrix.mulVec,dotProduct,Fin.sum_univ_three]
  all_goals fin_cases i <;> fin_cases j <;> simp [fiberCoefficient,add_comm]

theorem mixedGL_line_one (g : IntegralGL) (i j : Fin 3) (hij : i ≠ j) (k l : ℤ) :
    augmentedLine (g * mixedGL i j hij k l) 1 = fiberLine g i k := by
  apply Subtype.ext
  change Submodule.span ℚ {rationalRepresentation (g * mixedGL i j hij k l) (template 1)} = _
  rw [map_mul,LinearEquiv.mul_apply,template_eq_intTemplate,← rationalVector_mulVec,mixedGL_mulVec]
  rfl

theorem mixedGL_line_two (g : IntegralGL) (i j : Fin 3) (hij : i ≠ j) (k l : ℤ) :
    augmentedLine (g * mixedGL i j hij k l) 2 = fiberLine g j l := by
  apply Subtype.ext
  change Submodule.span ℚ {rationalRepresentation (g * mixedGL i j hij k l) (template 2)} = _
  rw [map_mul,LinearEquiv.mul_apply,template_eq_intTemplate,← rationalVector_mulVec,mixedGL_mulVec]
  rfl

theorem mixedGL_line_three (g : IntegralGL) (i j : Fin 3) (hij : i ≠ j) (k l : ℤ) :
    augmentedLine (g * mixedGL i j hij k l) 3 = fiberLine g i (k+1) := by
  apply Subtype.ext
  change Submodule.span ℚ {rationalRepresentation (g * mixedGL i j hij k l) (template 3)} = _
  rw [map_mul,LinearEquiv.mul_apply,template_eq_intTemplate,← rationalVector_mulVec,mixedGL_mulVec]
  rfl

/-- Every literal mixed triangle is a genuine face of an integral augmented frame. -/
theorem mixed_face_ambient (g : IntegralGL) (i j : Fin 3) (hij : i ≠ j) (k l : ℤ) :
    {fiberLine g i k,fiberLine g i (k+1),fiberLine g j l} ∈ ambient := by
  apply subset_augmentedFrame_mem (g * mixedGL i j hij k l) (by simp)
  have hmem (u : Fin 4) : augmentedLine (g * mixedGL i j hij k l) u ∈
      augmentedFrame (g * mixedGL i j hij k l) := by
    let : DecidableEq RationalLine := fun a b => Subtype.instDecidableEq a b
    exact Finset.mem_image.mpr ⟨u,Finset.mem_univ _,rfl⟩
  intro L hL
  simp only [Finset.mem_insert,Finset.mem_singleton] at hL
  rcases hL with rfl | rfl | rfl
  · rw [← mixedGL_line_one g i j hij k l]; exact hmem 1
  · rw [← mixedGL_line_three g i j hij k l]; exact hmem 3
  · rw [← mixedGL_line_two g i j hij k l]; exact hmem 2

theorem mixed_face_good (g : IntegralGL) (hb : columnResidue g 0 = 0)
    (hX : columnResidue g 1 ≠ 0) (hY : columnResidue g 2 ≠ 0)
    (hZ : columnResidue g 1 + columnResidue g 2 ≠ 0)
    (i j : Fin 3) (hij : i ≠ j) (k l : ℤ) :
    {fiberLine g i k,fiberLine g i (k+1),fiberLine g j l} ∈ good := by
  refine ⟨mixed_face_ambient g i j hij k l,?_⟩
  intro L hL
  simp only [Finset.mem_insert,Finset.mem_singleton] at hL
  rcases hL with rfl | rfl | rfl <;> exact fiberLine_good g hb hX hY hZ _ _

/-- All six orientations of every mixed generator have actual Good support. -/
theorem mixedGenerator_mem_chains (g : IntegralGL) (hb : columnResidue g 0 = 0)
    (hX : columnResidue g 1 ≠ 0) (hY : columnResidue g 2 ≠ 0)
    (hZ : columnResidue g 1 + columnResidue g 2 ≠ 0)
    {c : Chain RationalLine} (hc : MixedGenerator g c) : c ∈ chains good 3 := by
  obtain ⟨i,j,k,l,hij,hc⟩ := hc
  have hm := mixed_face_good g hb hX hY hZ i j hij k l
  have help (xs : List RationalLine) (hlen : xs.length = 3)
      (he : xs.toFinset = {fiberLine g i k,fiberLine g i (k+1),fiberLine g j l}) :
      simplex xs ∈ chains good 3 := by
    have hf : xs.toFinset ∈ good := he.symm ▸ hm
    have hh := simplex_mem_chains good xs (Or.inr hf)
    rw [hlen] at hh
    exact hh
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    apply help _ rfl
    ext L
    simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false,
      Finset.mem_insert,Finset.mem_singleton]
    all_goals tauto

/-- The independently defined mixed span consists entirely of genuine Good triangles. -/
theorem MixedSpan_le_chains (g : IntegralGL) (hb : columnResidue g 0 = 0)
    (hX : columnResidue g 1 ≠ 0) (hY : columnResidue g 2 ≠ 0)
    (hZ : columnResidue g 1 + columnResidue g 2 ≠ 0) : MixedSpan g ≤ chains good 3 := by
  apply Submodule.span_le.mpr
  exact fun _ hc => mixedGenerator_mem_chains g hb hX hY hZ hc

end TernaryPoly.CoherentPrismReduction
