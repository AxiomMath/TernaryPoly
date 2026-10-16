module

public import TernaryPeriodPolynomials.Building.BadVertex.Fibers
public import TernaryPeriodPolynomials.Building.BadVertex.SquareCaps

@[expose] public section

noncomputable section
namespace TernaryPoly.BadVertexMixedCharts
open ModThreeGoodAction AugmentedFrameComplex GoodIntegralNormalization
open BadVertexProjection BadVertexFibers CoherentPrismReduction OrientedListChains

/-- The only possible slopes of a primitive integer fiber coordinate. -/
def Sign (ε : ℤ) : Prop := ε = 1 ∨ ε = -1

theorem sign_mul {ε δ : ℤ} (hε : Sign ε) (hδ : Sign δ) : Sign (ε * δ) := by
  rcases hε with rfl | rfl <;> rcases hδ with rfl | rfl <;> norm_num [Sign]

theorem primitive_span_sign {v w : IntegralVector} (hv : Primitive v) (hw : Primitive w)
    (hs : Submodule.span ℚ {rationalVector v} = Submodule.span ℚ {rationalVector w}) :
    ∃ ε : ℤ, Sign ε ∧ v = ε • w := by
  rcases PrimitiveLineUniqueness.primitive_eq_or_neg_of_span_eq hv hw hs with he | he
  · exact ⟨1,Or.inl rfl,by simpa only [one_smul] using he⟩
  · exact ⟨-1,Or.inr rfl,by simpa only [neg_one_smul] using he⟩

/-- The primitive directions of two bases with the same first line differ by a sign. -/
theorem first_column_sign (g h : IntegralGL)
    (hb : augmentedLine h 0 = augmentedLine g 0) :
    ∃ ε : ℤ, Sign ε ∧ h.val.col 0 = ε • g.val.col 0 := by
  apply primitive_span_sign (column_primitive h 0) (column_primitive g 0)
  rw [← column_span h 0,← column_span g 0]
  exact congrArg Subtype.val hb

theorem coefficient_eq_coordinateVector (i : Fin 3) (k : ℤ) :
    fiberCoefficient i k = coordinateVector (RankTwoAugmentedFrames.integralTemplate i) k := by
  fin_cases i <;> rfl

theorem fiberVector_primitive (g : IntegralGL) (i : Fin 3) (k : ℤ) :
    Primitive (g.val.mulVec (fiberCoefficient i k)) := by
  rw [coefficient_eq_coordinateVector]
  exact GoodAugmentedNormalForm.primitive_mulVec g
    (coordinateVector_primitive _ (template_pair_primitive i) k)

theorem fiberVector_affine (g : IntegralGL) (i : Fin 3) (k : ℤ) :
    g.val.mulVec (fiberCoefficient i k) =
      g.val.mulVec (fiberCoefficient i 0) + k • g.val.col 0 := by
  simp only [coefficient_eq_coordinateVector]
  exact chart_vector_affine g _ k

/-- One fixed quotient vertex gives an actual integer coordinate for the second chart origin. -/
theorem fiber_origin (g h : IntegralGL) (hb : augmentedLine h 0 = augmentedLine g 0)
    (i : Fin 3) (hq : vertex g (fiberLine h i 0) = RankTwoAugmentedFrames.augmentedLine 1 i) :
    ∃ a : ℤ, fiberLine g i a = fiberLine h i 0 := by
  have hn : fiberLine h i 0 ≠ augmentedLine g 0 := by
    rw [← hb,prism_fiber_eq_chart]
    exact chart_ne_base _ _ _ _
  have he : {augmentedLine g 0,fiberLine h i 0} ∈ ambient := by
    rw [← hb,prism_fiber_eq_chart]
    exact chart_ambient_edge _ _ _ _
  obtain ⟨a,ha,_⟩ := prism_fiber_existsUnique g i (fiberLine h i 0) hn he hq
  exact ⟨a,ha⟩

/-- The origin vectors agree up to a sign after fixing the actual integer fiber coordinate. -/
theorem fiber_origin_sign (g h : IntegralGL)
    (hb : augmentedLine h 0 = augmentedLine g 0) (i : Fin 3)
    (hq : vertex g (fiberLine h i 0) = RankTwoAugmentedFrames.augmentedLine 1 i) :
    ∃ a ε : ℤ, Sign ε ∧
      h.val.mulVec (fiberCoefficient i 0) = ε • g.val.mulVec (fiberCoefficient i a) := by
  obtain ⟨a,ha⟩ := fiber_origin g h hb i hq
  have hs : Submodule.span ℚ {rationalVector (h.val.mulVec (fiberCoefficient i 0))} =
      Submodule.span ℚ {rationalVector (g.val.mulVec (fiberCoefficient i a))} := by
    rw [← fiberLine_val,← fiberLine_val]
    exact congrArg Subtype.val ha.symm
  obtain ⟨ε,hε,he⟩ := primitive_span_sign (fiberVector_primitive h i 0)
    (fiberVector_primitive g i a) hs
  exact ⟨a,ε,hε,he⟩

/-- Actual changes of integral basis act on each fixed quotient fiber by k ↦ a ± k. -/
theorem fiber_affine_transition (g h : IntegralGL)
    (hb : augmentedLine h 0 = augmentedLine g 0) (i : Fin 3)
    (hq : vertex g (fiberLine h i 0) = RankTwoAugmentedFrames.augmentedLine 1 i) :
    ∃ a δ : ℤ, Sign δ ∧ ∀ k : ℤ, fiberLine h i k = fiberLine g i (a + δ*k) := by
  obtain ⟨ε,hε,hcol⟩ := first_column_sign g h hb
  obtain ⟨a,η,hη,horg⟩ := fiber_origin_sign g h hb i hq
  refine ⟨a,η*ε,sign_mul hη hε,?_⟩
  intro k
  have hv : h.val.mulVec (fiberCoefficient i k) =
      η • g.val.mulVec (fiberCoefficient i (a + (η*ε)*k)) := by
    rw [fiberVector_affine h i k,horg,hcol,fiberVector_affine g i a,
      fiberVector_affine g i (a + (η*ε)*k)]
    rcases hε with rfl | rfl <;> rcases hη with rfl | rfl <;>
      funext r <;> simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul] <;> ring
  apply Subtype.ext
  rw [fiberLine_val,fiberLine_val,hv]
  have hc : rationalVector (η • g.val.mulVec (fiberCoefficient i (a+(η*ε)*k))) =
      (η : ℚ) • rationalVector (g.val.mulVec (fiberCoefficient i (a+(η*ε)*k))) := by
    funext r
    simp [rationalVector,Pi.smul_apply,smul_eq_mul]
  rw [hc,Submodule.span_singleton_smul_eq]
  rcases hη with rfl | rfl <;> norm_num

/-- The actual oriented mixed generator attached to a parameter-grid edge. -/
def mappedTriangle (g : IntegralGL) (e : IntegerGridExactness.Edge) : Chain RationalLine :=
  OrientedChainMap.map (BadVertexSquareCaps.fiberMap g) (IntegerPathJoinCycles.triangle e)

theorem mappedTriangle_horizontal (g : IntegralGL) (k l : ℤ) :
    mappedTriangle g ((k,l),0) = simplex [xFiber g k,xFiber g (k+1),yFiber g l] := by
  simp [mappedTriangle,IntegerPathJoinCycles.triangle,OrientedChainMap.map_simplex,
    BadVertexSquareCaps.fiberMap,IntegerPathJoinCycles.left,IntegerPathJoinCycles.right]

theorem mappedTriangle_vertical (g : IntegralGL) (k l : ℤ) :
    mappedTriangle g ((k,l),1) = -simplex [xFiber g k,yFiber g l,yFiber g (l+1)] := by
  simp [mappedTriangle,IntegerPathJoinCycles.triangle,OrientedChainMap.map_simplex,
    BadVertexSquareCaps.fiberMap,IntegerPathJoinCycles.left,IntegerPathJoinCycles.right]

theorem mappedTriangle_mem_range (g : IntegralGL) (e : IntegerGridExactness.Edge) :
    mappedTriangle g e ∈ LinearMap.range (BadVertexSquareCaps.mixed g) := by
  refine ⟨Finsupp.single e 1,?_⟩
  simp [BadVertexSquareCaps.mixed,IntegerPathJoinCycles.mixed,mappedTriangle]

/-- Permuting an actual oriented simplex changes at most its sign. -/
theorem simplex_perm_eq_or_neg {V : Type*} {l m : List V} (hp : l.Perm m) :
    simplex l = simplex m ∨ simplex l = -simplex m := by
  induction hp with
  | nil => exact Or.inl rfl
  | cons a hp ih =>
    rcases ih with he | he
    · exact Or.inl (by rw [← cons_simplex,← cons_simplex,he])
    · exact Or.inr (by rw [← cons_simplex,← cons_simplex,he,map_neg])
  | swap a b l => exact Or.inr (simplex_swap_eq_neg _ _ _)
  | trans hp hq ihp ihq =>
    rcases ihp with hp | hp <;> rcases ihq with hq | hq
    · exact Or.inl (hp.trans hq)
    · exact Or.inr (hp.trans hq)
    · exact Or.inr (by rw [hp,hq])
    · exact Or.inl (by rw [hp,hq,neg_neg])

theorem simplex_mem_of_perm {V : Type*} (S : Submodule ℚ (Chain V))
    {l m : List V} (hp : l.Perm m) (hm : simplex m ∈ S) : simplex l ∈ S := by
  rcases simplex_perm_eq_or_neg hp with he | he
  · exact he ▸ hm
  · rw [he]
    exact S.neg_mem hm

/-- Reversing the adjacent pair is the only orientation change for a horizontal triangle. -/
theorem horizontal_signed (g h : IntegralGL) (a b δ η : ℤ) (hδ : Sign δ)
    (hx : ∀ k, xFiber h k = xFiber g (a+δ*k))
    (hy : ∀ l, yFiber h l = yFiber g (b+η*l)) (k l : ℤ) :
    ∃ e : IntegerGridExactness.Edge,
      simplex [xFiber h k,xFiber h (k+1),yFiber h l] = mappedTriangle g e ∨
      simplex [xFiber h k,xFiber h (k+1),yFiber h l] = -mappedTriangle g e := by
  rw [hx,hx,hy]
  rcases hδ with rfl | rfl
  · refine ⟨((a+k,b+η*l),0),Or.inl ?_⟩
    rw [mappedTriangle_horizontal]
    simp only [one_mul,← add_assoc]
  · refine ⟨((a-k-1,b+η*l),0),Or.inr ?_⟩
    rw [mappedTriangle_horizontal]
    have hk : a + -1 * k = a-k-1+1 := by ring
    have hk1 : a + -1 * (k+1) = a-k-1 := by ring
    rw [hk,hk1]
    exact simplex_swap_eq_neg _ _ _

theorem simplex_swap_last {V : Type*} (a b c : V) :
    simplex [a,b,c] = -simplex [a,c,b] := by
  calc
    simplex [a,b,c] = cons a (simplex [b,c]) := (cons_simplex a _).symm
    _ = cons a (-simplex [c,b]) := congrArg (cons a) (simplex_swap_eq_neg b c [])
    _ = -simplex [a,c,b] := by rw [map_neg,cons_simplex]

/-- Vertical adjacent pairs have the corresponding actual signed parameter-grid generator. -/
theorem vertical_signed (g h : IntegralGL) (a b δ η : ℤ) (hη : Sign η)
    (hx : ∀ k, xFiber h k = xFiber g (a+δ*k))
    (hy : ∀ l, yFiber h l = yFiber g (b+η*l)) (k l : ℤ) :
    ∃ e : IntegerGridExactness.Edge,
      simplex [xFiber h k,yFiber h l,yFiber h (l+1)] = mappedTriangle g e ∨
      simplex [xFiber h k,yFiber h l,yFiber h (l+1)] = -mappedTriangle g e := by
  rw [hx,hy,hy]
  rcases hη with rfl | rfl
  · refine ⟨((a+δ*k,b+l),1),Or.inr ?_⟩
    rw [mappedTriangle_vertical,neg_neg]
    simp only [one_mul,← add_assoc]
  · refine ⟨((a+δ*k,b-l-1),1),Or.inl ?_⟩
    rw [mappedTriangle_vertical]
    have hl : b + -1 * l = b-l-1+1 := by ring
    have hl1 : b + -1 * (l+1) = b-l-1 := by ring
    rw [hl,hl1]
    exact simplex_swap_last _ _ _

/-- The two actual quotient columns agree with the fixed projected base edge. -/
def Compatible (g h : IntegralGL) : Prop :=
  augmentedLine h 0 = augmentedLine g 0 ∧
  vertex g (xFiber h 0) = vertex g (xFiber g 0) ∧
  vertex g (yFiber h 0) = vertex g (yFiber g 0)

theorem compatible_affine (g h : IntegralGL) (hc : Compatible g h) :
    ∃ a b δ η : ℤ, Sign δ ∧ Sign η ∧
      (∀ k, xFiber h k = xFiber g (a+δ*k)) ∧
      (∀ l, yFiber h l = yFiber g (b+η*l)) := by
  obtain ⟨a,δ,hδ,hx⟩ := fiber_affine_transition g h hc.1 0
    (hc.2.1.trans (prism_fiber_vertex g 0 0))
  obtain ⟨b,η,hη,hy⟩ := fiber_affine_transition g h hc.1 1
    (hc.2.2.trans (prism_fiber_vertex g 1 0))
  exact ⟨a,b,δ,η,hδ,hη,hx,hy⟩

theorem horizontal_mem_range (g h : IntegralGL) (hc : Compatible g h) (k l : ℤ) :
    simplex [xFiber h k,xFiber h (k+1),yFiber h l] ∈
      LinearMap.range (BadVertexSquareCaps.mixed g) := by
  obtain ⟨a,b,δ,η,hδ,_,hx,hy⟩ := compatible_affine g h hc
  obtain ⟨e,he⟩ := horizontal_signed g h a b δ η hδ hx hy k l
  rcases he with he | he
  · rw [he]; exact mappedTriangle_mem_range g e
  · rw [he]; exact (LinearMap.range (BadVertexSquareCaps.mixed g)).neg_mem (mappedTriangle_mem_range g e)

theorem vertical_mem_range (g h : IntegralGL) (hc : Compatible g h) (k l : ℤ) :
    simplex [xFiber h k,yFiber h l,yFiber h (l+1)] ∈
      LinearMap.range (BadVertexSquareCaps.mixed g) := by
  obtain ⟨a,b,δ,η,_,hη,hx,hy⟩ := compatible_affine g h hc
  obtain ⟨e,he⟩ := vertical_signed g h a b δ η hη hx hy k l
  rcases he with he | he
  · rw [he]; exact mappedTriangle_mem_range g e
  · rw [he]; exact (LinearMap.range (BadVertexSquareCaps.mixed g)).neg_mem (mappedTriangle_mem_range g e)

/-- All orderings of actual adjacent triangles over the fixed pair of quotient fibers. -/
def TwoFiberGenerator (g : IntegralGL) (c : Chain RationalLine) : Prop :=
  ∃ (k l : ℤ) (m : List RationalLine), c = simplex m ∧
    (m.Perm [xFiber g k,xFiber g (k+1),yFiber g l] ∨
      m.Perm [xFiber g k,yFiber g l,yFiber g (l+1)])

def TwoFiberSpan (g : IntegralGL) : Submodule ℚ (Chain RationalLine) :=
  Submodule.span ℚ {c | TwoFiberGenerator g c}

/-- Exhaustive chart comparison for every ordering of a local two-fiber mixed triangle. -/
theorem twoFiberGenerator_mem_range (g h : IntegralGL) (hc : Compatible g h)
    {c : Chain RationalLine} (hgen : TwoFiberGenerator h c) :
    c ∈ LinearMap.range (BadVertexSquareCaps.mixed g) := by
  obtain ⟨k,l,m,rfl,hperm⟩ := hgen
  rcases hperm with hp | hp
  · exact simplex_mem_of_perm _ hp (horizontal_mem_range g h hc k l)
  · exact simplex_mem_of_perm _ hp (vertical_mem_range g h hc k l)

/-- The entire actual mixed span of any compatible chart lies in one fixed mapped mixed range. -/
theorem twoFiberSpan_le_range (g h : IntegralGL) (hc : Compatible g h) :
    TwoFiberSpan h ≤ LinearMap.range (BadVertexSquareCaps.mixed g) := by
  apply Submodule.span_le.mpr
  intro c hc'
  exact twoFiberGenerator_mem_range g h hc hc'

/-- A parameter-grid edge generator remains in the fixed mapped mixed range. -/
theorem mappedTriangle_mem_range_of_compatible (g h : IntegralGL) (hc : Compatible g h)
    (e : IntegerGridExactness.Edge) :
    mappedTriangle h e ∈ LinearMap.range (BadVertexSquareCaps.mixed g) := by
  rcases e with ⟨⟨k,l⟩,i⟩
  fin_cases i
  · change mappedTriangle h ((k,l),0) ∈ _
    rw [mappedTriangle_horizontal]
    exact horizontal_mem_range g h hc k l
  · change mappedTriangle h ((k,l),1) ∈ _
    rw [mappedTriangle_vertical]
    exact (LinearMap.range (BadVertexSquareCaps.mixed g)).neg_mem
      (vertical_mem_range g h hc k l)

/-- Every finite actual two-fiber mixed combination can be grouped in the one fixed chart. -/
theorem mixed_range_le (g h : IntegralGL) (hc : Compatible g h) :
    LinearMap.range (BadVertexSquareCaps.mixed h) ≤
      LinearMap.range (BadVertexSquareCaps.mixed g) := by
  rintro c ⟨z,rfl⟩
  induction z using Finsupp.induction_linear with
  | zero => simpa only [map_zero] using (LinearMap.range (BadVertexSquareCaps.mixed g)).zero_mem
  | add z w hz hw =>
    simpa only [map_add] using (LinearMap.range (BadVertexSquareCaps.mixed g)).add_mem hz hw
  | single e q =>
    have he : BadVertexSquareCaps.mixed h (Finsupp.single e q) = q • mappedTriangle h e := by
      simp [BadVertexSquareCaps.mixed,IntegerPathJoinCycles.mixed,mappedTriangle]
    rw [he]
    exact (LinearMap.range (BadVertexSquareCaps.mixed g)).smul_mem q
      (mappedTriangle_mem_range_of_compatible g h hc e)

/-- Swapping the two quotient columns preserves the bad first column line. -/
theorem swap_base (h : IntegralGL) : augmentedLine (h * swapGL) 0 = augmentedLine h 0 := by
  apply BadEdgeNormalForm.augmentedLine_mul_of_template
  have hv : swapGL.val.mulVec (GoodAugmentedNormalForm.integralTemplate 0) =
      GoodAugmentedNormalForm.integralTemplate 0 := by decide +kernel
  rw [← GoodAugmentedNormalForm.rationalVector_integralTemplate,← rationalVector_mulVec,hv,
    GoodAugmentedNormalForm.rationalVector_integralTemplate]

theorem swap_xFiber (h : IntegralGL) (k : ℤ) : xFiber (h * swapGL) k = yFiber h k :=
  fiberLine_swap h 0 k

theorem swap_yFiber (h : IntegralGL) (k : ℤ) : yFiber (h * swapGL) k = xFiber h k :=
  fiberLine_swap h 1 k

/-- Compatibility with the fixed base edge in the opposite endpoint order. -/
def SwappedCompatible (g h : IntegralGL) : Prop :=
  augmentedLine h 0 = augmentedLine g 0 ∧
  vertex g (xFiber h 0) = vertex g (yFiber g 0) ∧
  vertex g (yFiber h 0) = vertex g (xFiber g 0)

theorem swapped_compatible (g h : IntegralGL) (hc : SwappedCompatible g h) :
    Compatible g (h * swapGL) := by
  refine ⟨(swap_base h).trans hc.1,?_,?_⟩
  · rw [swap_xFiber]
    exact hc.2.2
  · rw [swap_yFiber]
    exact hc.2.1

theorem simplex_rotate {V : Type*} (a b c : V) :
    simplex [a,b,c] = simplex [c,a,b] := by
  rw [simplex_swap_last a b c,simplex_swap_eq_neg a c [b],neg_neg]

/-- A horizontal mixed triangle over the opposite endpoint order still lies in the fixed range. -/
theorem horizontal_mem_range_swapped (g h : IntegralGL) (hc : SwappedCompatible g h)
    (k l : ℤ) : simplex [xFiber h k,xFiber h (k+1),yFiber h l] ∈
      LinearMap.range (BadVertexSquareCaps.mixed g) := by
  have hv := vertical_mem_range g (h * swapGL) (swapped_compatible g h hc) l k
  rw [swap_xFiber,swap_yFiber,swap_yFiber] at hv
  rw [simplex_rotate (xFiber h k) (xFiber h (k+1)) (yFiber h l)]
  exact hv

/-- The same endpoint reversal handles every vertical mixed triangle. -/
theorem vertical_mem_range_swapped (g h : IntegralGL) (hc : SwappedCompatible g h)
    (k l : ℤ) : simplex [xFiber h k,yFiber h l,yFiber h (l+1)] ∈
      LinearMap.range (BadVertexSquareCaps.mixed g) := by
  have hh := horizontal_mem_range g (h * swapGL) (swapped_compatible g h hc) l k
  rw [swap_xFiber,swap_xFiber,swap_yFiber] at hh
  rwa [simplex_rotate (yFiber h l) (yFiber h (l+1)) (xFiber h k)] at hh

/-- All orientations over an oppositely ordered local chart lie in the fixed mapped range. -/
theorem twoFiberSpan_le_range_swapped (g h : IntegralGL) (hc : SwappedCompatible g h) :
    TwoFiberSpan h ≤ LinearMap.range (BadVertexSquareCaps.mixed g) := by
  apply Submodule.span_le.mpr
  rintro c ⟨k,l,m,rfl,hperm⟩
  rcases hperm with hp | hp
  · exact simplex_mem_of_perm _ hp (horizontal_mem_range_swapped g h hc k l)
  · exact simplex_mem_of_perm _ hp (vertical_mem_range_swapped g h hc k l)

end TernaryPoly.BadVertexMixedCharts
