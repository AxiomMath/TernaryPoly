module

public import TernaryPeriodPolynomials.Building.Good.RelativePresentationFrames

@[expose] public section


open Matrix
noncomputable section
namespace TernaryPoly.OrdinaryApartmentFrames
open ModThreeGoodAction GoodIntegralNormalization PrimitiveLineUniqueness
open AugmentedFrameComplex GoodAugmentedNormalForm GoodRelativeChains IntegralFrameHeightReduction

/-- Each subset records the columns whose primitive representative is negated. -/
def signEntry (s : Finset (Fin 3)) (j : Fin 3) : ℤ := if j∈s then -1 else 1

theorem signEntry_mul_self (s : Finset (Fin 3)) (j : Fin 3) :
    signEntry s j * signEntry s j = 1 := by
  unfold signEntry
  split <;> norm_num

/-- All independent primitive-column signs, as actual integral invertible matrices. -/
def signFrame (s : Finset (Fin 3)) : IntegralGL where
  val := Matrix.diagonal (signEntry s)
  inv := Matrix.diagonal (signEntry s)
  val_inv := by simp [Matrix.diagonal_mul_diagonal,signEntry_mul_self]
  inv_val := by simp [Matrix.diagonal_mul_diagonal,signEntry_mul_self]

@[simp] theorem signFrame_inv (s : Finset (Fin 3)) : (signFrame s)⁻¹=signFrame s := rfl

theorem mul_signFrame_entry (g : IntegralGL) (s : Finset (Fin 3)) (i j : Fin 3) :
    (g*signFrame s).val i j=g.val i j*signEntry s j :=
  Matrix.mul_diagonal _ _ _ _

/-- Ordered rational column lines determine the frame up to its three independent signs. -/
theorem eq_mul_signFrame_of_column_lines (g h : IntegralGL)
    (he : ∀ j : Fin 3, augmentedLine g j.castSucc=augmentedLine h j.castSucc) :
    ∃ s : Finset (Fin 3), h=g*signFrame s := by
  classical
  have hc (j : Fin 3) : h.val.col j=g.val.col j ∨ h.val.col j= -g.val.col j := by
    apply primitive_eq_or_neg_of_span_eq (column_primitive h j) (column_primitive g j)
    rw [←columnLine_span,←columnLine_span,he j]
  refine ⟨Finset.univ.filter (fun j => h.val.col j= -g.val.col j),?_⟩
  apply Units.ext
  ext i j
  rw [mul_signFrame_entry]
  by_cases hj : h.val.col j= -g.val.col j
  · simp only [signEntry,Finset.mem_filter,Finset.mem_univ,true_and,hj,ite_true,mul_neg_one]
    exact congrFun hj i
  · simp only [signEntry,Finset.mem_filter,Finset.mem_univ,true_and,hj,ite_false,mul_one]
    exact congrFun ((hc j).resolve_right hj) i

/-- The unrestricted cyclic matrix literally rotates the integral columns. -/
theorem mul_c_column (g : IntegralGL) (j : Fin 3) :
    (g*ReferenceCoefficientMatrices.c).val.col j=g.val.col ((![1,2,0] : Fin 3 → Fin 3) j) := by
  ext i
  change (∑ k : Fin 3,g.val i k*ReferenceCoefficientMatrices.cMatrix k j)=_
  fin_cases j <;> simp [ReferenceCoefficientMatrices.cMatrix,Fin.sum_univ_three]

theorem mul_s_column (g : IntegralGL) (j : Fin 3) :
    (g*ReferenceCoefficientMatrices.s).val.col j=g.val.col ((![1,0,2] : Fin 3 → Fin 3) j) := by
  ext i
  change (∑ k : Fin 3,g.val i k*ReferenceCoefficientMatrices.sMatrix k j)=_
  fin_cases j <;> simp [ReferenceCoefficientMatrices.sMatrix,Fin.sum_univ_three]

theorem mul_c_line (g : IntegralGL) (j : Fin 3) :
    augmentedLine (g*ReferenceCoefficientMatrices.c) j.castSucc=
      augmentedLine g ((![1,2,0] : Fin 3 → Fin 3) j).castSucc := by
  apply Subtype.ext
  rw [columnLine_span,columnLine_span,mul_c_column]

theorem mul_s_line (g : IntegralGL) (j : Fin 3) :
    augmentedLine (g*ReferenceCoefficientMatrices.s) j.castSucc=
      augmentedLine g ((![1,0,2] : Fin 3 → Fin 3) j).castSucc := by
  apply Subtype.ext
  rw [columnLine_span,columnLine_span,mul_s_column]

theorem triangleList_mul_c (g : IntegralGL) : triangleList (g*ReferenceCoefficientMatrices.c)=
    [augmentedLine g 1,augmentedLine g 2,augmentedLine g 0] :=
  congrArg (fun v : Fin 3 → RationalLine => [v 0,v 1,v 2]) (funext (mul_c_line g))

theorem triangleList_mul_s (g : IntegralGL) : triangleList (g*ReferenceCoefficientMatrices.s)=
    [augmentedLine g 1,augmentedLine g 0,augmentedLine g 2] :=
  congrArg (fun v : Fin 3 → RationalLine => [v 0,v 1,v 2]) (funext (mul_s_line g))

theorem triangleList_cycle_of_eq (g : IntegralGL) (L M N : RationalLine)
    (hg : triangleList g=[L,M,N]) : triangleList (g*ReferenceCoefficientMatrices.c)=[M,N,L] := by
  have he : augmentedLine g 0=L ∧ augmentedLine g 1=M ∧ augmentedLine g 2=N := by
    simpa only [triangleList,List.cons.injEq,and_true] using hg
  rw [triangleList_mul_c,he.1,he.2.1,he.2.2]

theorem triangleList_swap_of_eq (g : IntegralGL) (L M N : RationalLine)
    (hg : triangleList g=[L,M,N]) : triangleList (g*ReferenceCoefficientMatrices.s)=[M,L,N] := by
  have he : augmentedLine g 0=L ∧ augmentedLine g 1=M ∧ augmentedLine g 2=N := by
    simpa only [triangleList,List.cons.injEq,and_true] using hg
  rw [triangleList_mul_s,he.1,he.2.1,he.2.2]

end TernaryPoly.OrdinaryApartmentFrames
