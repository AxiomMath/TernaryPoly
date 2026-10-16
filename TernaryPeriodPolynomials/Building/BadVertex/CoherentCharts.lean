module

public import TernaryPeriodPolynomials.Building.BadVertex.Fibers

@[expose] public section


noncomputable section
namespace TernaryPoly.BadVertexCoherentCharts

open ModThreeGoodAction AugmentedFrameComplex BadVertexProjection BadVertexFibers
open CoherentPrismReduction

/-- Every affine fiber has the same quotient coordinates in any adapted comparison basis. -/
theorem fiber_projection (g h : IntegralGL)
    (hh : augmentedLine h 0 = augmentedLine g 0) (i : Fin 3) (k : ℤ) :
    vertex g (fiberLine h i k) =
      RankTwoAugmentedFrames.augmentedLine
        (lowerGL (g⁻¹ * h) (first_column_lower_zero g h hh)) i := by
  have hne : fiberLine h i k ≠ augmentedLine g 0 := by
    rw [← hh,prism_fiber_eq_chart]
    exact chart_ne_base _ _ _ _
  apply Subtype.ext
  rw [vertex_span g _ hne
    (v := rationalRepresentation h (rationalVector (fiberCoefficient i k))) rfl,
    projection_representation g h hh]
  have hc : dropFirst (rationalVector (fiberCoefficient i k)) =
      RankTwoAugmentedFrames.template i := by
    funext j
    fin_cases i <;> fin_cases j <;> rfl
  rw [hc]
  rfl

/-- The integral vector underlying a rank-two template image. -/
theorem rankTwo_template_vector (q : RankTwoAugmentedFrames.IntegralGL) (i : Fin 3) :
    RankTwoAugmentedFrames.rationalRepresentation q (RankTwoAugmentedFrames.template i) =
      RankTwoAugmentedFrames.rationalVector
        (q.val.mulVec (RankTwoAugmentedFrames.integralTemplate i)) := by
  rw [RankTwoAugmentedFrames.rationalVector_mulVec,
    RankTwoAugmentedFrames.rationalVector_integralTemplate]

/-- A primitive first column fixing the first quotient line is exactly its signed standard vector. -/
theorem rankTwo_first_signed (q : RankTwoAugmentedFrames.IntegralGL)
    (h0 : RankTwoAugmentedFrames.augmentedLine q 0 =
      RankTwoAugmentedFrames.augmentedLine 1 0) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ q.val 0 0 = s ∧ q.val 1 0 = 0 := by
  have hc : q.val.mulVec (RankTwoAugmentedFrames.integralTemplate 0) = q.val.col 0 := by
    funext i
    simp [RankTwoAugmentedFrames.integralTemplate,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
  have hs : Submodule.span ℚ {RankTwoAugmentedFrames.rationalVector (q.val.col 0)} =
      Submodule.span ℚ {(RankTwoAugmentedFrames.rationalVector
        (RankTwoAugmentedFrames.integralTemplate 0))} := by
    have he := congrArg Subtype.val h0
    change Submodule.span ℚ {(RankTwoAugmentedFrames.rationalRepresentation q
      (RankTwoAugmentedFrames.template 0))} =
      Submodule.span ℚ {(RankTwoAugmentedFrames.rationalRepresentation 1
        (RankTwoAugmentedFrames.template 0))} at he
    rw [rankTwo_template_vector,hc,map_one,LinearEquiv.coe_one,id_eq] at he
    simpa only [RankTwoAugmentedFrames.rationalVector_integralTemplate] using he
  rcases RankTwoAugmentedFrames.primitive_eq_or_neg_of_span_eq
    (rankTwo_column_primitive q 0) (template_pair_primitive 0) hs with hpos | hneg
  · exact ⟨1,Or.inl rfl,congrFun hpos 0,congrFun hpos 1⟩
  · refine ⟨-1,Or.inr rfl,congrFun hneg 0,?_⟩
    simpa [RankTwoAugmentedFrames.integralTemplate] using congrFun hneg 1

/-- Fixing all three projective template lines forces one common integral sign. -/
theorem rankTwo_scalar_of_fixes (q : RankTwoAugmentedFrames.IntegralGL)
    (hq : ∀ i : Fin 3, RankTwoAugmentedFrames.augmentedLine q i =
      RankTwoAugmentedFrames.augmentedLine 1 i) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ q.val = !![s,0;0,s] := by
  obtain ⟨s,hs,h00,h10⟩ := rankTwo_first_signed q (hq 0)
  have hm (i : Fin 3) : RankTwoAugmentedFrames.rationalRepresentation q
      (RankTwoAugmentedFrames.template i) ∈
      Submodule.span ℚ {RankTwoAugmentedFrames.template i} := by
    have he := congrArg Subtype.val (hq i)
    change Submodule.span ℚ {(RankTwoAugmentedFrames.rationalRepresentation q
      (RankTwoAugmentedFrames.template i))} =
      Submodule.span ℚ {(RankTwoAugmentedFrames.rationalRepresentation 1
        (RankTwoAugmentedFrames.template i))} at he
    rw [map_one,LinearEquiv.coe_one,id_eq] at he
    rw [← he]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp (hm 1)
  obtain ⟨b,hb⟩ := Submodule.mem_span_singleton.mp (hm 2)
  rw [rankTwo_template_vector] at ha hb
  have h01 : q.val 0 1 = 0 := by
    have he := congrFun ha 0
    have he' : (q.val 0 1 : ℚ) = 0 := by
      simpa [RankTwoAugmentedFrames.rationalVector,RankTwoAugmentedFrames.template,
        RankTwoAugmentedFrames.integralTemplate,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
        using he.symm
    exact_mod_cast he'
  have h11 : q.val 1 1 = s := by
    have he0 := congrFun hb 0
    have he1 := congrFun hb 1
    have hb0 : b = (s : ℚ) := by
      simpa [RankTwoAugmentedFrames.rationalVector,RankTwoAugmentedFrames.template,
        RankTwoAugmentedFrames.integralTemplate,Matrix.mulVec,dotProduct,Fin.sum_univ_two,
        h00,h01] using he0
    have hb1 : b = (q.val 1 1 : ℚ) := by
      simpa [RankTwoAugmentedFrames.rationalVector,RankTwoAugmentedFrames.template,
        RankTwoAugmentedFrames.integralTemplate,Matrix.mulVec,dotProduct,Fin.sum_univ_two,
        h10] using he1
    exact_mod_cast hb1.symm.trans hb0
  refine ⟨s,hs,?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00,h01,h10,h11]

/-- Actual adapted bases with identical ordered quotient triangles differ by this literal matrix. -/
theorem comparison_matrix (g h : IntegralGL)
    (hh : augmentedLine h 0 = augmentedLine g 0)
    (hq : ∀ i : Fin 3, vertex g (fiberLine h i 0) = vertex g (fiberLine g i 0)) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧
      (g⁻¹ * h).val = !![(g⁻¹ * h).val 0 0,(g⁻¹ * h).val 0 1,(g⁻¹ * h).val 0 2;
        0,s,0;0,0,s] := by
  let q := lowerGL (g⁻¹ * h) (first_column_lower_zero g h hh)
  have hfix : ∀ i : Fin 3, RankTwoAugmentedFrames.augmentedLine q i =
      RankTwoAugmentedFrames.augmentedLine 1 i := by
    intro i
    have he := hq i
    rw [fiber_projection g h hh,prism_fiber_vertex] at he
    exact he
  obtain ⟨s,hs,hqs⟩ := rankTwo_scalar_of_fixes q hfix
  refine ⟨s,hs,?_⟩
  have hlow (i j : Fin 2) : (g⁻¹ * h).val i.succ j.succ = !![s,0;0,s] i j := by
    exact congrFun (congrFun hqs i) j
  have hz := first_column_lower_zero g h hh
  ext i j
  fin_cases i <;> fin_cases j
  · rfl
  · rfl
  · rfl
  · exact hz 0
  · exact hlow 0 0
  · exact hlow 0 1
  · exact hz 1
  · exact hlow 1 0
  · exact hlow 1 1

/-- The finite affine coefficient identity keeps the two offsets and their sum aligned. -/
theorem triangular_coefficients (t a b s : ℤ) (hs : s*s = 1) (p : ℤ × ℤ) (i : Fin 3) :
    (!![t,a,b;0,s,0;0,0,s] : Matrix (Fin 3) (Fin 3) ℤ).mulVec
      (fiberCoefficient i ((![p.1,p.2,p.1+p.2] : Fin 3 → ℤ) i)) =
      s • fiberCoefficient i ((![s*(t*p.1+a),s*(t*p.2+b),
        s*(t*p.1+a)+s*(t*p.2+b)] : Fin 3 → ℤ) i) := by
  funext j
  fin_cases i <;> fin_cases j <;>
    simp [fiberCoefficient,Matrix.mulVec,dotProduct,Fin.sum_univ_three,
      mul_add,← mul_assoc,hs]
  all_goals ring

/-- A common nonzero sign in actual integral vectors does not alter their rational lines. -/
theorem fiberLine_of_coordinate_identity (g h : IntegralGL) (i : Fin 3) (a b s : ℤ)
    (hs : s ≠ 0)
    (hc : (g⁻¹ * h).val.mulVec (fiberCoefficient i a) = s • fiberCoefficient i b) :
    fiberLine h i a = fiberLine g i b := by
  apply Subtype.ext
  change Submodule.span ℚ {rationalRepresentation h (rationalVector (fiberCoefficient i a))} = _
  have he : rationalRepresentation h (rationalVector (fiberCoefficient i a)) =
      rationalRepresentation g (rationalRepresentation (g⁻¹ * h)
        (rationalVector (fiberCoefficient i a))) := by
    rw [map_mul,LinearEquiv.mul_apply,representation_inverse']
  rw [he,← rationalVector_mulVec,hc]
  have hcast : rationalVector (s • fiberCoefficient i b) =
      (s : ℚ) • rationalVector (fiberCoefficient i b) := by
    funext j
    simp [rationalVector,Pi.smul_apply,smul_eq_mul]
  rw [hcast,map_smul,Submodule.span_singleton_smul_eq
    (isUnit_iff_ne_zero.mpr (by exact_mod_cast hs))]
  rfl

/-- All coherent affine lifts above one ordered quotient triangle use one literal integer grid. -/
theorem coherent_chart_coordinates (g h : IntegralGL)
    (hh : augmentedLine h 0 = augmentedLine g 0)
    (hq : ∀ i : Fin 3, vertex g (fiberLine h i 0) = vertex g (fiberLine g i 0)) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ ∀ p : ℤ × ℤ,
      let k := s*((g⁻¹*h).val 0 0*p.1+(g⁻¹*h).val 0 1)
      let l := s*((g⁻¹*h).val 0 0*p.2+(g⁻¹*h).val 0 2)
      xFiber h p.1 = xFiber g k ∧ yFiber h p.2 = yFiber g l ∧
        zFiber h (p.1+p.2) = zFiber g (k+l) := by
  obtain ⟨s,hs,hm⟩ := comparison_matrix g h hh hq
  have hss : s*s = 1 := by rcases hs with rfl | rfl <;> norm_num
  have hsn : s ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
  refine ⟨s,hs,?_⟩
  intro p
  dsimp only
  have hc (i : Fin 3) : (g⁻¹ * h).val.mulVec
      (fiberCoefficient i ((![p.1,p.2,p.1+p.2] : Fin 3 → ℤ) i)) =
      s • fiberCoefficient i ((![s*((g⁻¹*h).val 0 0*p.1+(g⁻¹*h).val 0 1),
        s*((g⁻¹*h).val 0 0*p.2+(g⁻¹*h).val 0 2),
        s*((g⁻¹*h).val 0 0*p.1+(g⁻¹*h).val 0 1)+
        s*((g⁻¹*h).val 0 0*p.2+(g⁻¹*h).val 0 2)] : Fin 3 → ℤ) i) := by
    nth_rw 1 [hm]
    exact triangular_coefficients _ _ _ s hss p i
  exact ⟨fiberLine_of_coordinate_identity g h 0 _ _ s hsn (hc 0),
    fiberLine_of_coordinate_identity g h 1 _ _ s hsn (hc 1),
    fiberLine_of_coordinate_identity g h 2 _ _ s hsn (hc 2)⟩

/-- The coordinate comparison gives a literal equality of the existing coherent simplex chains. -/
theorem coherent_chain_reindex (g h : IntegralGL)
    (hh : augmentedLine h 0 = augmentedLine g 0)
    (hq : ∀ i : Fin 3, vertex g (fiberLine h i 0) = vertex g (fiberLine g i 0)) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ ∀ p : ℤ × ℤ,
      coherent h p = coherent g
        (s*((g⁻¹*h).val 0 0*p.1+(g⁻¹*h).val 0 1),
         s*((g⁻¹*h).val 0 0*p.2+(g⁻¹*h).val 0 2)) := by
  obtain ⟨s,hs,hc⟩ := coherent_chart_coordinates g h hh hq
  refine ⟨s,hs,?_⟩
  intro p
  obtain ⟨hx,hy,hz⟩ := hc p
  simp only [coherent,hx,hy,hz]

/-- The requested zero-height comparison exposes exactly the additive integer offsets. -/
theorem coherent_chart_zero (g h : IntegralGL)
    (hh : augmentedLine h 0 = augmentedLine g 0)
    (hx : vertex g (xFiber h 0) = vertex g (xFiber g 0))
    (hy : vertex g (yFiber h 0) = vertex g (yFiber g 0))
    (hz : vertex g (zFiber h 0) = vertex g (zFiber g 0)) :
    ∃ k l : ℤ, xFiber h 0 = xFiber g k ∧ yFiber h 0 = yFiber g l ∧
      zFiber h 0 = zFiber g (k+l) := by
  have hq (i : Fin 3) : vertex g (fiberLine h i 0) = vertex g (fiberLine g i 0) := by
    fin_cases i
    · exact hx
    · exact hy
    · exact hz
  obtain ⟨s,_,hs⟩ := coherent_chart_coordinates g h hh hq
  refine ⟨s*(g⁻¹*h).val 0 1,s*(g⁻¹*h).val 0 2,?_⟩
  simpa using hs (0,0)

end TernaryPoly.BadVertexCoherentCharts
