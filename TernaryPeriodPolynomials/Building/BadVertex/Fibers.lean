module

public import TernaryPeriodPolynomials.Building.BadVertex.Projection
public import TernaryPeriodPolynomials.Building.Coherent.PrismReduction

@[expose] public section


noncomputable section
namespace TernaryPoly.BadVertexFibers

open ModThreeGoodAction AugmentedFrameComplex BadVertexProjection
open GoodIntegralNormalization GoodAugmentedNormalForm

abbrev Pair := RankTwoAugmentedFrames.IntegralVector
abbrev PairPrimitive := RankTwoAugmentedFrames.Primitive

/-- Literal affine quotient coordinates with prescribed primitive lower pair. -/
def coordinateVector (p : Pair) (k : ℤ) : IntegralVector := ![k,p 0,p 1]

theorem pair_ne_zero (p : Pair) (hp : PairPrimitive p) :
    RankTwoAugmentedFrames.rationalVector p ≠ 0 := by
  obtain ⟨a,b,hab⟩ := RankTwoAugmentedFrames.primitive_bezout hp
  intro hz
  have h0 : p 0 = 0 := by
    have hi := congrFun hz 0
    change (p 0 : ℚ) = 0 at hi
    exact_mod_cast hi
  have h1 : p 1 = 0 := by
    have hi := congrFun hz 1
    change (p 1 : ℚ) = 0 at hi
    exact_mod_cast hi
  simp only [h0,h1,zero_mul,zero_add] at hab
  exact zero_ne_one hab

theorem coordinateVector_primitive (p : Pair) (hp : PairPrimitive p) (k : ℤ) :
    Primitive (coordinateVector p k) := by
  obtain ⟨a,b,hab⟩ := RankTwoAugmentedFrames.primitive_bezout hp
  apply primitive_of_bezout (b := ![0,a,b])
  simpa [Fin.sum_univ_three,coordinateVector,mul_comm] using hab

theorem coordinateVector_ne_zero (p : Pair) (hp : PairPrimitive p) (k : ℤ) :
    rationalVector (coordinateVector p k) ≠ 0 := by
  intro hz
  apply pair_ne_zero p hp
  funext i
  fin_cases i
  · exact congrFun hz 1
  · exact congrFun hz 2

/-- The chosen primitive pair determines the actual target quotient line. -/
def quotientLine (p : Pair) (hp : PairPrimitive p) : RankTwoAugmentedFrames.RationalLine2 :=
  RankTwoAugmentedFrames.vectorLine (RankTwoAugmentedFrames.rationalVector p) (pair_ne_zero p hp)

/-- The actual affine integer chart, with lift g·(0,p) and direction the first column of g. -/
def chart (g : IntegralGL) (p : Pair) (hp : PairPrimitive p) (k : ℤ) : RationalLine :=
  vectorLine (rationalRepresentation g (rationalVector (coordinateVector p k)))
    (fun hz => coordinateVector_ne_zero p hp k ((rationalRepresentation g).injective
      (hz.trans (map_zero (rationalRepresentation g)).symm)))

theorem chart_val (g : IntegralGL) (p : Pair) (hp : PairPrimitive p) (k : ℤ) :
    (chart g p hp k).val =
      Submodule.span ℚ {rationalVector (g.val.mulVec (coordinateVector p k))} := by
  change Submodule.span ℚ {rationalRepresentation g (rationalVector (coordinateVector p k))} = _
  rw [← rationalVector_mulVec]

/-- The chart is literally U+kB in the original integral lattice. -/
theorem chart_vector_affine (g : IntegralGL) (p : Pair) (k : ℤ) :
    g.val.mulVec (coordinateVector p k) =
      g.val.mulVec (coordinateVector p 0) + k • g.val.col 0 := by
  funext i
  simp [coordinateVector,Matrix.mulVec,dotProduct,Fin.sum_univ_three]
  ring

theorem projection_chart_vector (g : IntegralGL) (p : Pair) (k : ℤ) :
    projection g (rationalRepresentation g (rationalVector (coordinateVector p k))) =
      RankTwoAugmentedFrames.rationalVector p := by
  change dropFirst (rationalRepresentation g⁻¹
    (rationalRepresentation g (rationalVector (coordinateVector p k)))) = _
  rw [representation_inverse]
  funext i
  fin_cases i <;> rfl

theorem chart_ne_base (g : IntegralGL) (p : Pair) (hp : PairPrimitive p) (k : ℤ) :
    chart g p hp k ≠ augmentedLine g 0 := by
  intro he
  have hm : rationalRepresentation g (rationalVector (coordinateVector p k)) ∈
      (augmentedLine g 0).val := by
    rw [← he]
    exact Submodule.mem_span_singleton_self _
  have hz := (projection_eq_zero_iff g _).mpr hm
  rw [projection_chart_vector] at hz
  exact pair_ne_zero p hp hz

/-- Every chart coordinate has exactly the prescribed quotient vertex. -/
theorem vertex_chart (g : IntegralGL) (p : Pair) (hp : PairPrimitive p) (k : ℤ) :
    vertex g (chart g p hp k) = quotientLine p hp := by
  apply Subtype.ext
  rw [vertex_span g _ (chart_ne_base g p hp k)
    (v := rationalRepresentation g (rationalVector (coordinateVector p k))) rfl,
    projection_chart_vector]
  rfl

/-- Fixing the projected primitive generator removes every rational scaling ambiguity. -/
theorem chart_injective (g : IntegralGL) (p : Pair) (hp : PairPrimitive p) :
    Function.Injective (chart g p hp) := by
  intro k l he
  have hm : rationalRepresentation g (rationalVector (coordinateVector p k)) ∈
      Submodule.span ℚ {rationalRepresentation g (rationalVector (coordinateVector p l))} := by
    change _ ∈ (chart g p hp l).val
    rw [← he]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨q,hq⟩ := Submodule.mem_span_singleton.mp hm
  have ha : q • rationalVector (coordinateVector p l) = rationalVector (coordinateVector p k) := by
    apply (rationalRepresentation g).injective
    rw [map_smul]
    exact hq
  have hpq : q • RankTwoAugmentedFrames.rationalVector p =
      RankTwoAugmentedFrames.rationalVector p := by
    funext i
    fin_cases i
    · exact congrFun ha 1
    · exact congrFun ha 2
  have hq1 : q = 1 := smul_left_injective ℚ (pair_ne_zero p hp)
    (hpq.trans (one_smul ℚ _).symm)
  have hk := congrFun ha 0
  change q * (l : ℚ) = (k : ℚ) at hk
  rw [hq1,one_mul] at hk
  exact_mod_cast hk.symm

/-- Literal integral completion of the chart vector while keeping the first basis vector fixed. -/
def completionMatrix (p : Pair) (hp : PairPrimitive p) (k : ℤ) :
    Matrix (Fin 3) (Fin 3) ℤ :=
  let h := RankTwoAugmentedFrames.primitiveCompletion p hp
  !![1,k,0;0,h.val 0 0,h.val 0 1;0,h.val 1 0,h.val 1 1]

theorem completionMatrix_det (p : Pair) (hp : PairPrimitive p) (k : ℤ) :
    (completionMatrix p hp k).det = 1 := by
  have hd := RankTwoAugmentedFrames.primitiveCompletion_det p hp
  rw [Matrix.det_fin_two] at hd
  simpa [completionMatrix,Matrix.det_fin_three] using hd

def completion (p : Pair) (hp : PairPrimitive p) (k : ℤ) : IntegralGL :=
  Matrix.nonsingInvUnit (completionMatrix p hp k)
    (by rw [completionMatrix_det]; exact isUnit_one)

theorem completion_template_zero (p : Pair) (hp : PairPrimitive p) (k : ℤ) :
    rationalRepresentation (completion p hp k) (template 0) = template 0 := by
  have he : (completion p hp k).val.mulVec (integralTemplate 0) = integralTemplate 0 := by
    change (completionMatrix p hp k).mulVec (integralTemplate 0) = _
    funext i
    fin_cases i <;> simp [completionMatrix,integralTemplate,Matrix.mulVec,dotProduct,
      Fin.sum_univ_three]
  rw [← rationalVector_integralTemplate,← rationalVector_mulVec,he,rationalVector_integralTemplate]

theorem completion_template_one (p : Pair) (hp : PairPrimitive p) (k : ℤ) :
    rationalRepresentation (completion p hp k) (template 1) =
      rationalVector (coordinateVector p k) := by
  have hc := RankTwoAugmentedFrames.primitiveCompletion_first_column p hp
  have h0 := congrFun hc 0
  have h1 := congrFun hc 1
  have he : (completion p hp k).val.mulVec (integralTemplate 1) = coordinateVector p k := by
    change (completionMatrix p hp k).mulVec (integralTemplate 1) = _
    funext i
    fin_cases i <;> simp [completionMatrix,integralTemplate,coordinateVector,
      Matrix.mulVec,dotProduct,Fin.sum_univ_three,h0,h1]
  rw [← rationalVector_integralTemplate,← rationalVector_mulVec,he]

theorem completion_line_zero (g : IntegralGL) (p : Pair) (hp : PairPrimitive p) (k : ℤ) :
    augmentedLine (g * completion p hp k) 0 = augmentedLine g 0 :=
  BadEdgeNormalForm.augmentedLine_mul_of_template g _ _ _ (completion_template_zero p hp k)

theorem completion_line_one (g : IntegralGL) (p : Pair) (hp : PairPrimitive p) (k : ℤ) :
    augmentedLine (g * completion p hp k) 1 = chart g p hp k := by
  apply Subtype.ext
  change Submodule.span ℚ {rationalRepresentation (g * completion p hp k) (template 1)} = _
  rw [map_mul,LinearEquiv.mul_apply,completion_template_one]
  rfl

/-- Every integer chart point is an actual ambient neighbor, with a displayed integral basis. -/
theorem chart_ambient_edge (g : IntegralGL) (p : Pair) (hp : PairPrimitive p) (k : ℤ) :
    {augmentedLine g 0,chart g p hp k} ∈ ambient := by
  classical
  apply subset_augmentedFrame_mem (g * completion p hp k) (by simp)
  intro L hL
  simp only [Finset.mem_insert,Finset.mem_singleton] at hL
  rcases hL with rfl | rfl
  · exact Finset.mem_image.mpr ⟨0,Finset.mem_univ _,completion_line_zero g p hp k⟩
  · exact Finset.mem_image.mpr ⟨1,Finset.mem_univ _,completion_line_one g p hp k⟩

/-- Exhaustiveness of the actual fiber follows from primitive quotient uniqueness up to sign. -/
theorem exists_chart (g : IntegralGL) (p : Pair) (hp : PairPrimitive p) (L : RationalLine)
    (hL : L ≠ augmentedLine g 0) (he : {augmentedLine g 0,L} ∈ ambient)
    (hq : vertex g L = quotientLine p hp) : ∃ k : ℤ, chart g p hp k = L := by
  obtain ⟨v,hv,_,hs⟩ := RationalLineBasis.rationalLine_primitive_generator L
  have hvp := ambient_neighbor_primitive g L hL he hv hs
  have hspan : Submodule.span ℚ
      {RankTwoAugmentedFrames.rationalVector (integralProjection g v)} =
      Submodule.span ℚ {RankTwoAugmentedFrames.rationalVector p} := by
    have hh := congrArg Subtype.val hq
    rw [vertex_span g L hL hs,projection_rationalVector] at hh
    exact hh
  let a := g⁻¹.val.mulVec v
  have ha : g.val.mulVec a = v := by
    dsimp [a]
    rw [Matrix.mulVec_mulVec,← Units.val_mul,mul_inv_cancel,Units.val_one,Matrix.one_mulVec]
  rcases RankTwoAugmentedFrames.primitive_eq_or_neg_of_span_eq hvp hp hspan with hpos | hneg
  · refine ⟨a 0,?_⟩
    have hc : coordinateVector p (a 0) = a := by
      funext i
      fin_cases i
      · rfl
      · exact (congrFun hpos 0).symm
      · exact (congrFun hpos 1).symm
    apply Subtype.ext
    rw [chart_val,hc,ha,hs]
  · refine ⟨-a 0,?_⟩
    have hc : coordinateVector p (-a 0) = -a := by
      funext i
      fin_cases i
      · rfl
      · have hh := congrFun hneg 0
        change a 1 = -p 0 at hh
        change p 0 = -a 1
        rw [hh,neg_neg]
      · have hh := congrFun hneg 1
        change a 2 = -p 1 at hh
        change p 1 = -a 2
        rw [hh,neg_neg]
    apply Subtype.ext
    rw [chart_val,hc,Matrix.mulVec_neg,ha,GoodIntegralNormalization.rationalVector_neg,
      ← neg_one_smul ℚ (rationalVector v),
      Submodule.span_singleton_smul_eq (by norm_num : IsUnit (-1 : ℚ)),hs]

/-- The actual fiber over a chosen primitive quotient line is precisely one integer chart. -/
theorem fiber_iff_existsUnique (g : IntegralGL) (p : Pair) (hp : PairPrimitive p)
    (L : RationalLine) :
    (L ≠ augmentedLine g 0 ∧ {augmentedLine g 0,L} ∈ ambient ∧
      vertex g L = quotientLine p hp) ↔ ∃! k : ℤ, chart g p hp k = L := by
  constructor
  · rintro ⟨hL,he,hq⟩
    obtain ⟨k,hk⟩ := exists_chart g p hp L hL he hq
    exact ⟨k,hk,fun l hl => chart_injective g p hp (hl.trans hk.symm)⟩
  · rintro ⟨k,rfl,_⟩
    exact ⟨chart_ne_base g p hp k,chart_ambient_edge g p hp k,vertex_chart g p hp k⟩

/-- The residue calculation keeps the chosen quotient generator's sign explicit. -/
theorem chart_vector_residue (g : IntegralGL) (p : Pair) (k : ℤ) :
    (∑ i, (g.val.mulVec (coordinateVector p k) i : ZMod 3)) =
      (k : ZMod 3) * AugmentedBadFaces.columnResidue g 0 +
      (p 0 : ZMod 3) * AugmentedBadFaces.columnResidue g 1 +
      (p 1 : ZMod 3) * AugmentedBadFaces.columnResidue g 2 := by
  simp [coordinateVector,Matrix.mulVec,dotProduct,Fin.sum_univ_three,
    AugmentedBadFaces.columnResidue]
  ring

/-- Over a bad first line, goodness depends only on the chosen quotient pair. -/
theorem chart_good_iff (g : IntegralGL) (hbad : ¬Good (augmentedLine g 0).val)
    (p : Pair) (hp : PairPrimitive p) (k : ℤ) :
    Good (chart g p hp k).val ↔
      (p 0 : ZMod 3) * AugmentedBadFaces.columnResidue g 1 +
        (p 1 : ZMod 3) * AugmentedBadFaces.columnResidue g 2 ≠ 0 := by
  have hb : AugmentedBadFaces.columnResidue g 0 = 0 :=
    AugmentedBadFaces.bad_augmentedLine_residue g 0 hbad
  rw [chart_val,good_span_iff_residue (primitive_mulVec g (coordinateVector_primitive p hp k)),
    chart_vector_residue,hb,mul_zero,zero_add]

/-- Translation by the bad first column preserves actual lattice goodness. -/
theorem chart_good_translation (g : IntegralGL) (hbad : ¬Good (augmentedLine g 0).val)
    (p : Pair) (hp : PairPrimitive p) (k l : ℤ) :
    Good (chart g p hp k).val ↔ Good (chart g p hp l).val := by
  rw [chart_good_iff g hbad,chart_good_iff g hbad]

/-- An arbitrary literal integral lift changes only the integer origin of the same chart. -/
theorem chart_val_eq_lift_span (g : IntegralGL) (p : Pair) (hp : PairPrimitive p)
    (U : IntegralVector) (hU : integralProjection g U = p) (k : ℤ) :
    (chart g p hp (g⁻¹.val.mulVec U 0 + k)).val =
      Submodule.span ℚ {rationalVector (U + k • g.val.col 0)} := by
  let a := g⁻¹.val.mulVec U
  have hc : coordinateVector p (a 0) = a := by
    funext i
    fin_cases i
    · rfl
    · exact (congrFun hU 0).symm
    · exact (congrFun hU 1).symm
  have hga : g.val.mulVec (coordinateVector p (a 0)) = U := by
    rw [hc]
    dsimp [a]
    rw [Matrix.mulVec_mulVec,← Units.val_mul,mul_inv_cancel,Units.val_one,Matrix.one_mulVec]
  have hv : g.val.mulVec (coordinateVector p (a 0 + k)) = U + k • g.val.col 0 := by
    rw [chart_vector_affine,add_smul,← add_assoc,← chart_vector_affine,hga]
  rw [chart_val]
  change Submodule.span ℚ {rationalVector (g.val.mulVec (coordinateVector p (a 0 + k)))} = _
  rw [hv]

/-- The three literal quotient template pairs are primitive. -/
theorem template_pair_primitive : ∀ i : Fin 3,
    PairPrimitive (RankTwoAugmentedFrames.integralTemplate i) := by
  unfold PairPrimitive RankTwoAugmentedFrames.Primitive RankTwoAugmentedFrames.content
  decide +kernel

theorem template_quotientLine (i : Fin 3) :
    quotientLine (RankTwoAugmentedFrames.integralTemplate i) (template_pair_primitive i) =
      RankTwoAugmentedFrames.augmentedLine 1 i := by
  apply Subtype.ext
  change Submodule.span ℚ {(RankTwoAugmentedFrames.rationalVector
      (RankTwoAugmentedFrames.integralTemplate i))} =
    Submodule.span ℚ {(RankTwoAugmentedFrames.rationalRepresentation 1
      (RankTwoAugmentedFrames.template i))}
  rw [RankTwoAugmentedFrames.rationalVector_integralTemplate,map_one]
  rfl

/-- The existing prism fibers are exactly the corresponding literal quotient charts. -/
theorem prism_fiber_eq_chart (g : IntegralGL) (i : Fin 3) (k : ℤ) :
    CoherentPrismReduction.fiberLine g i k =
      chart g (RankTwoAugmentedFrames.integralTemplate i) (template_pair_primitive i) k := by
  apply Subtype.ext
  fin_cases i <;> rfl

/-- Exact quotient identity for the existing x/y/z fibers. -/
theorem prism_fiber_vertex (g : IntegralGL) (i : Fin 3) (k : ℤ) :
    vertex g (CoherentPrismReduction.fiberLine g i k) =
      RankTwoAugmentedFrames.augmentedLine 1 i := by
  rw [prism_fiber_eq_chart,vertex_chart,template_quotientLine]

/-- Each existing prism fiber is an injective actual integer chart. -/
theorem prism_fiber_injective (g : IntegralGL) (i : Fin 3) :
    Function.Injective (CoherentPrismReduction.fiberLine g i) := by
  intro k l he
  rw [prism_fiber_eq_chart,prism_fiber_eq_chart] at he
  exact chart_injective _ _ _ he

/-- Different quotient lines give disjoint actual integer charts. -/
theorem chart_ne_of_quotient_ne (g : IntegralGL) (p q : Pair)
    (hp : PairPrimitive p) (hq : PairPrimitive q)
    (hne : quotientLine p hp ≠ quotientLine q hq) (k l : ℤ) :
    chart g p hp k ≠ chart g q hq l := by
  intro he
  apply hne
  have hh := congrArg (vertex g) he
  simpa only [vertex_chart] using hh

/-- Different existing prism fibers are disjoint because their actual quotient lines differ. -/
theorem prism_fibers_disjoint (g : IntegralGL) (i j : Fin 3) (hij : i ≠ j) (k l : ℤ) :
    CoherentPrismReduction.fiberLine g i k ≠ CoherentPrismReduction.fiberLine g j l := by
  intro he
  have hh := congrArg (vertex g) he
  rw [prism_fiber_vertex,prism_fiber_vertex] at hh
  exact hij (RankTwoAugmentedFrames.augmentedLine_injective 1 hh)

/-- The two-fiber relabeling used for integer-path joins is genuinely injective. -/
theorem prism_fiber_sum_injective (g : IntegralGL) (i j : Fin 3) (hij : i ≠ j) :
    Function.Injective (Sum.elim (CoherentPrismReduction.fiberLine g i)
      (CoherentPrismReduction.fiberLine g j)) :=
  Sum.elim_injective.mpr ⟨prism_fiber_injective g i,prism_fiber_injective g j,
    prism_fibers_disjoint g i j hij⟩

theorem xyFiber_sum_injective (g : IntegralGL) :
    Function.Injective (Sum.elim (CoherentPrismReduction.xFiber g)
      (CoherentPrismReduction.yFiber g)) :=
  prism_fiber_sum_injective g 0 1 (by decide)

/-- Exhaustive unique-coordinate classification for each existing prism fiber. -/
theorem prism_fiber_existsUnique (g : IntegralGL) (i : Fin 3) (L : RationalLine)
    (hL : L ≠ augmentedLine g 0) (he : {augmentedLine g 0,L} ∈ ambient)
    (hq : vertex g L = RankTwoAugmentedFrames.augmentedLine 1 i) :
    ∃! k : ℤ, CoherentPrismReduction.fiberLine g i k = L := by
  have hq' : vertex g L = quotientLine (RankTwoAugmentedFrames.integralTemplate i)
      (template_pair_primitive i) := by rwa [template_quotientLine]
  have hh := (fiber_iff_existsUnique g (RankTwoAugmentedFrames.integralTemplate i)
    (template_pair_primitive i) L).mp ⟨hL,he,hq'⟩
  simpa only [prism_fiber_eq_chart] using hh

/-- An arbitrary rational quotient line admits one exhaustive primitive integer chart. -/
theorem quotientLine_exists_chart (Q : RankTwoAugmentedFrames.RationalLine2) :
    ∃ p : Pair, ∃ hp : PairPrimitive p, quotientLine p hp = Q := by
  obtain ⟨p,hp,_,hs⟩ := RankTwoAugmentedFrames.rationalLine_primitive_generator Q
  exact ⟨p,hp,Subtype.ext hs⟩

end TernaryPoly.BadVertexFibers
