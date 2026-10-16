module

public import TernaryPeriodPolynomials.Building.RankTwo.AugmentedFrames
public import TernaryPeriodPolynomials.Building.BadEdge.NormalForm
public import TernaryPeriodPolynomials.Topology.Rational.LineBasis
public import TernaryPeriodPolynomials.Building.Good.AugmentedNormalForm
public import TernaryPeriodPolynomials.Building.OrientedChain.ChainMap
public import TernaryPeriodPolynomials.Building.Good.LinkExtraction

@[expose] public section


noncomputable section
namespace TernaryPoly.BadVertexProjection

open ModThreeGoodAction AugmentedFrameComplex

/-- Discard the first coordinate in the actual rational lattice space. -/
def dropFirst : Space →ₗ[ℚ] RankTwoAugmentedFrames.Space where
  toFun v := fun i => v i.succ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Quotient coordinates with respect to the fixed integral frame. -/
def projection (g : IntegralGL) : Space →ₗ[ℚ] RankTwoAugmentedFrames.Space :=
  dropFirst.comp (rationalRepresentation g⁻¹).toLinearMap

@[simp] theorem projection_apply (g : IntegralGL) (v : Space) (i : Fin 2) :
    projection g v i = rationalRepresentation g⁻¹ v i.succ := rfl

theorem representation_inverse (g : IntegralGL) (v : Space) :
    rationalRepresentation g⁻¹ (rationalRepresentation g v) = v := by
  rw [← LinearEquiv.mul_apply,← map_mul,inv_mul_cancel,map_one]
  rfl

theorem representation_inverse' (g : IntegralGL) (v : Space) :
    rationalRepresentation g (rationalRepresentation g⁻¹ v) = v := by
  rw [← LinearEquiv.mul_apply,← map_mul,mul_inv_cancel,map_one]
  rfl

theorem dropFirst_eq_zero_iff (v : Space) :
    dropFirst v = 0 ↔ v ∈ Submodule.span ℚ {Pi.single (0 : Fin 3) 1} := by
  constructor
  · intro hv
    apply Submodule.mem_span_singleton.mpr
    refine ⟨v 0,?_⟩
    funext i
    fin_cases i
    · simp
    · have h := congrFun hv 0
      change v 1 = 0 at h
      simpa using h.symm
    · have h := congrFun hv 1
      change v 2 = 0 at h
      simpa using h.symm
  · intro hv
    obtain ⟨q,rfl⟩ := Submodule.mem_span_singleton.mp hv
    funext i
    fin_cases i <;> simp [dropFirst]

/-- The quotient kernel is exactly the fixed first rational line. -/
theorem projection_eq_zero_iff (g : IntegralGL) (v : Space) :
    projection g v = 0 ↔ v ∈ (augmentedLine g 0).val := by
  change dropFirst (rationalRepresentation g⁻¹ v) = 0 ↔
    v ∈ Submodule.span ℚ {rationalRepresentation g (Pi.single (0 : Fin 3) 1)}
  rw [dropFirst_eq_zero_iff]
  constructor
  · intro hv
    obtain ⟨q,hq⟩ := Submodule.mem_span_singleton.mp hv
    apply Submodule.mem_span_singleton.mpr
    refine ⟨q,?_⟩
    have he := congrArg (rationalRepresentation g) hq
    simpa only [map_smul,representation_inverse'] using he
  · intro hv
    obtain ⟨q,rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [map_smul,representation_inverse]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

theorem projection_ker (g : IntegralGL) :
    LinearMap.ker (projection g) = (augmentedLine g 0).val := by
  ext v
  exact projection_eq_zero_iff g v

/-- Every nonzero generator of a different line survives the quotient. -/
theorem projection_ne_zero (g : IntegralGL) (L : RationalLine)
    (hL : L ≠ augmentedLine g 0) {v : Space} (_hv : v ≠ 0)
    (hs : Submodule.span ℚ {v} = L.val) : projection g v ≠ 0 := by
  intro hz
  apply hL
  apply Subtype.ext
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [← hs]
    exact Submodule.span_le.mpr (by
      intro x hx
      rcases hx with rfl
      exact (projection_eq_zero_iff g x).mp hz)
  · exact L.property.trans (augmentedLine g 0).property.symm

/-- A non-kernel rational line has an actual one-dimensional linear image. -/
theorem image_finrank (g : IntegralGL) (L : RationalLine)
    (hL : L ≠ augmentedLine g 0) :
    Module.finrank ℚ (L.val.map (projection g)) = 1 := by
  obtain ⟨v,_,hv,hs⟩ := RationalLineBasis.rationalLine_primitive_generator L
  rw [← hs,Submodule.map_span,Set.image_singleton]
  exact finrank_span_singleton (projection_ne_zero g L hL hv hs)

/-- The total vertex projection uses a fixed fallback only on the kernel line. -/
def vertex (g : IntegralGL) (L : RationalLine) : RankTwoAugmentedFrames.RationalLine2 :=
  if hL : L = augmentedLine g 0 then RankTwoAugmentedFrames.augmentedLine 1 0
  else ⟨L.val.map (projection g),image_finrank g L hL⟩

theorem vertex_val (g : IntegralGL) (L : RationalLine)
    (hL : L ≠ augmentedLine g 0) :
    (vertex g L).val = L.val.map (projection g) := by
  simp only [vertex,dite_eq_right hL]

theorem vertex_span (g : IntegralGL) (L : RationalLine)
    (hL : L ≠ augmentedLine g 0) {v : Space}
    (hs : Submodule.span ℚ {v} = L.val) :
    (vertex g L).val = Submodule.span ℚ {projection g v} := by
  rw [vertex_val g L hL,← hs,Submodule.map_span,Set.image_singleton]

/-- The integral quotient coordinates are literal lower entries of the inverse-frame vector. -/
def integralProjection (g : IntegralGL) (v : IntegralVector) : RankTwoAugmentedFrames.IntegralVector :=
  fun i => g⁻¹.val.mulVec v i.succ

theorem projection_rationalVector (g : IntegralGL) (v : IntegralVector) :
    projection g (rationalVector v) = RankTwoAugmentedFrames.rationalVector (integralProjection g v) := by
  funext i
  change rationalRepresentation g⁻¹ (rationalVector v) i.succ = _
  rw [← rationalVector_mulVec]
  rfl

/-- The lower square block of a literal integral change-of-basis matrix. -/
def lowerBlock (h : IntegralGL) : Matrix (Fin 2) (Fin 2) ℤ :=
  fun i j => h.val i.succ j.succ

theorem lowerBlock_isUnit (h : IntegralGL)
    (hz : ∀ i : Fin 2, h.val i.succ 0 = 0) : IsUnit (lowerBlock h).det := by
  have hd : h.val.det = h.val 0 0 * (lowerBlock h).det := by
    rw [Matrix.det_fin_three,Matrix.det_fin_two]
    have h1 := hz 0
    have h2 := hz 1
    change h.val 1 0 = 0 at h1
    change h.val 2 0 = 0 at h2
    simp only [h1,h2,mul_zero,zero_mul,sub_zero,add_zero,lowerBlock]
    change h.val 0 0 * h.val 1 1 * h.val 2 2 - h.val 0 0 * h.val 1 2 * h.val 2 1 =
      h.val 0 0 * (h.val 1 1 * h.val 2 2 - h.val 1 2 * h.val 2 1)
    ring
  apply isUnit_of_mul_isUnit_right (x := h.val 0 0)
  rw [← hd]
  exact (Matrix.isUnit_iff_isUnit_det h.val).mp h.isUnit

/-- The quotient basis is an actual integer matrix unit, not abstract quotient data. -/
def lowerGL (h : IntegralGL) (hz : ∀ i : Fin 2, h.val i.succ 0 = 0) :
    RankTwoAugmentedFrames.IntegralGL :=
  Matrix.nonsingInvUnit (lowerBlock h) (lowerBlock_isUnit h hz)

theorem integralProjection_col (g h : IntegralGL) (j : Fin 3) :
    integralProjection g (h.val.col j) = fun i => (g⁻¹ * h).val i.succ j := by
  rfl

/-- Equal first rational lines force literal zero lower coordinates. -/
theorem first_column_lower_zero (g h : IntegralGL)
    (hh : augmentedLine h 0 = augmentedLine g 0) :
    ∀ i : Fin 2, (g⁻¹ * h).val i.succ 0 = 0 := by
  have hm : rationalVector (h.val.col 0) ∈ (augmentedLine g 0).val := by
    rw [← hh]
    change rationalVector (h.val.col 0) ∈
      Submodule.span ℚ {rationalRepresentation h (Pi.single (0 : Fin 3) 1)}
    rw [AugmentedBadFaces.rationalRepresentation_basis]
    exact Submodule.mem_span_singleton_self _
  have he := (projection_eq_zero_iff g _).mpr hm
  rw [projection_rationalVector,integralProjection_col] at he
  intro i
  have hi := congrFun he i
  change ((g⁻¹ * h).val i.succ 0 : ℚ) = 0 at hi
  exact_mod_cast hi

/-- The two projected remaining columns are exactly the literal quotient basis columns. -/
theorem quotient_columns (g h : IntegralGL)
    (hh : augmentedLine h 0 = augmentedLine g 0) (j : Fin 2) :
    integralProjection g (h.val.col j.succ) =
      (lowerGL (g⁻¹ * h) (first_column_lower_zero g h hh)).val.col j := rfl

/-- Columns of a rank-two integer matrix unit have coordinate gcd one. -/
theorem rankTwo_column_primitive (h : RankTwoAugmentedFrames.IntegralGL) (j : Fin 2) :
    RankTwoAugmentedFrames.Primitive (h.val.col j) := by
  have he : h⁻¹.val j 0 * h.val 0 j + h⁻¹.val j 1 * h.val 1 j = 1 := by
    have hu : h⁻¹.val * h.val = 1 := by
      rw [← Units.val_mul,inv_mul_cancel,Units.val_one]
    have hm := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M j j) hu
    simpa only [Matrix.mul_apply,Fin.sum_univ_two,Matrix.one_apply_eq] using hm
  have hd : (RankTwoAugmentedFrames.content (h.val.col j) : ℤ) ∣ 1 := by
    rw [← he]
    apply dvd_add
    · exact dvd_mul_of_dvd_right (RankTwoAugmentedFrames.content_dvd _ 0) _
    · exact dvd_mul_of_dvd_right (RankTwoAugmentedFrames.content_dvd _ 1) _
  exact Nat.dvd_one.mp (Int.ofNat_dvd.mp hd)

/-- Every projected non-first column of a basis with the fixed first line is primitive. -/
theorem quotient_column_primitive (g h : IntegralGL)
    (hh : augmentedLine h 0 = augmentedLine g 0) (j : Fin 2) :
    RankTwoAugmentedFrames.Primitive (integralProjection g (h.val.col j.succ)) := by
  rw [quotient_columns g h hh]
  exact rankTwo_column_primitive _ j

theorem column_primitive (h : IntegralGL) (j : Fin 3) :
    GoodIntegralNormalization.Primitive (h.val.col j) := by
  have he := GoodAugmentedNormalForm.primitive_mulVec h
    (GoodAugmentedNormalForm.integralTemplate_primitive j.castSucc)
  fin_cases j <;> simpa [GoodAugmentedNormalForm.integralTemplate] using he

theorem column_span (h : IntegralGL) (j : Fin 3) :
    (augmentedLine h j.castSucc).val = Submodule.span ℚ {rationalVector (h.val.col j)} := by
  rw [AugmentedBadFaces.augmentedLine_castSucc_val,
    AugmentedBadFaces.rationalRepresentation_basis]
  rfl

/-- Negation preserves primitivity of the literal quotient pair. -/
theorem rankTwo_primitive_neg {v : RankTwoAugmentedFrames.IntegralVector}
    (hv : RankTwoAugmentedFrames.Primitive v) : RankTwoAugmentedFrames.Primitive (-v) := by
  simpa only [RankTwoAugmentedFrames.Primitive,RankTwoAugmentedFrames.content,
    Pi.neg_apply,Int.gcd_def,Int.natAbs_neg] using hv

/-- Any primitive generator of an actual ambient neighbor projects to a primitive pair. -/
theorem ambient_neighbor_primitive (g : IntegralGL) (L : RationalLine)
    (hL : L ≠ augmentedLine g 0) (he : {augmentedLine g 0,L} ∈ ambient)
    {v : IntegralVector} (hv : GoodIntegralNormalization.Primitive v)
    (hs : Submodule.span ℚ {rationalVector v} = L.val) :
    RankTwoAugmentedFrames.Primitive (integralProjection g v) := by
  obtain ⟨h,hh0,hh1⟩ := BadEdgeNormalForm.ordered_ambient_edge _ L hL.symm he
  have hspan : Submodule.span ℚ {rationalVector v} =
      Submodule.span ℚ {rationalVector (h.val.col 1)} := by
    rw [hs,← hh1]
    exact column_span h 1
  rcases PrimitiveLineUniqueness.primitive_eq_or_neg_of_span_eq hv
      (column_primitive h 1) hspan with hpos | hneg
  · rw [hpos]
    exact quotient_column_primitive g h hh0 0
  · rw [hneg]
    have hn : integralProjection g (-h.val.col 1) = -integralProjection g (h.val.col 1) := by
      funext i
      exact congrFun (Matrix.mulVec_neg (h.val.col 1) g⁻¹.val) i.succ
    rw [hn]
    exact rankTwo_primitive_neg (quotient_column_primitive g h hh0 0)

/-- Four explicit basis changes place each possible distinguished template vector first. -/
def templateChangeMatrix : Fin 4 → Matrix (Fin 3) (Fin 3) ℤ :=
  ![!![1,0,0;0,1,0;0,0,1],
    !![0,1,0;1,0,0;0,0,1],
    !![0,1,0;0,0,1;1,0,0],
    !![1,1,0;1,0,0;0,0,1]]

def templateChangeInverse : Fin 4 → Matrix (Fin 3) (Fin 3) ℤ :=
  ![!![1,0,0;0,1,0;0,0,1],
    !![0,1,0;1,0,0;0,0,1],
    !![0,0,1;1,0,0;0,1,0],
    !![0,1,0;1,-1,0;0,0,1]]

theorem templateChange_mul_inverse : ∀ i,
    templateChangeMatrix i * templateChangeInverse i = 1 := by decide +kernel

theorem templateChange_inverse_mul : ∀ i,
    templateChangeInverse i * templateChangeMatrix i = 1 := by decide +kernel

def templateChange (i : Fin 4) : IntegralGL :=
  ⟨templateChangeMatrix i,templateChangeInverse i,
    templateChange_mul_inverse i,templateChange_inverse_mul i⟩

theorem templateChange_first : ∀ i,
    (templateChange i).val.mulVec (GoodAugmentedNormalForm.integralTemplate 0) =
      GoodAugmentedNormalForm.integralTemplate i := by decide +kernel

theorem templateChange_line (h : IntegralGL) (i : Fin 4) :
    augmentedLine (h * templateChange i) 0 = augmentedLine h i := by
  apply BadEdgeNormalForm.augmentedLine_mul_of_template
  rw [← GoodAugmentedNormalForm.rationalVector_integralTemplate,
    ← GoodAugmentedNormalForm.rationalVector_integralTemplate,← rationalVector_mulVec,
    templateChange_first]

/-- Each projected template has the displayed rank-two index; collisions are intentional. -/
def projectedIndex : Fin 4 → Fin 4 → Fin 3 :=
  ![![0,0,1,0],![0,0,1,0],![0,1,0,2],![0,0,1,0]]

def projectedSign (i j : Fin 4) : ℤ := if i = 3 ∧ j = 1 then -1 else 1

theorem projectedSign_ne_zero (i j : Fin 4) : projectedSign i j ≠ 0 := by
  unfold projectedSign
  split <;> norm_num

/-- This exact finite coordinate identity includes the negative and repeated projected vertices. -/
theorem template_quotient_coordinates : ∀ i j : Fin 4, i ≠ j →
    (fun r : Fin 2 => (templateChange i)⁻¹.val.mulVec
      (GoodAugmentedNormalForm.integralTemplate j) r.succ) =
    projectedSign i j • RankTwoAugmentedFrames.integralTemplate (projectedIndex i j) := by
  decide +kernel

/-- The lower block is the induced linear action after deleting the first coordinate. -/
theorem dropFirst_representation (h : IntegralGL)
    (hz : ∀ i : Fin 2, h.val i.succ 0 = 0) (v : Space) :
    dropFirst (rationalRepresentation h v) =
      RankTwoAugmentedFrames.rationalRepresentation (lowerGL h hz) (dropFirst v) := by
  rw [rationalRepresentation_apply,RankTwoAugmentedFrames.rationalRepresentation_apply]
  funext i
  change (∑ j : Fin 3, (h.val i.succ j : ℚ) * v j) =
    ∑ j : Fin 2, (h.val i.succ j.succ : ℚ) * v j.succ
  rw [Fin.sum_univ_three,Fin.sum_univ_two,hz i,Int.cast_zero,zero_mul,zero_add]
  rfl

/-- Quotient coordinates of any vector transformed by an adapted frame use its actual GL₂ block. -/
theorem projection_representation (g h : IntegralGL)
    (hh : augmentedLine h 0 = augmentedLine g 0) (v : Space) :
    projection g (rationalRepresentation h v) =
      RankTwoAugmentedFrames.rationalRepresentation
        (lowerGL (g⁻¹ * h) (first_column_lower_zero g h hh)) (dropFirst v) := by
  change dropFirst (rationalRepresentation g⁻¹ (rationalRepresentation h v)) = _
  rw [← LinearEquiv.mul_apply,← map_mul]
  exact dropFirst_representation _ _ v

/-- Every other line in an actual augmented frame projects into one genuine rank-two frame. -/
theorem vertex_template (g h : IntegralGL) (i j : Fin 4)
    (hi : augmentedLine h i = augmentedLine g 0) (hij : i ≠ j) :
    vertex g (augmentedLine h j) =
      RankTwoAugmentedFrames.augmentedLine
        (lowerGL (g⁻¹ * (h * templateChange i))
          (first_column_lower_zero g (h * templateChange i)
            ((templateChange_line h i).trans hi))) (projectedIndex i j) := by
  let h' := h * templateChange i
  have hh' : augmentedLine h' 0 = augmentedLine g 0 := (templateChange_line h i).trans hi
  have hL : augmentedLine h j ≠ augmentedLine g 0 := by
    intro he
    exact hij ((AugmentedBadFaces.augmentedLine_injective h) (hi.trans he.symm))
  apply Subtype.ext
  rw [vertex_span g (augmentedLine h j) hL (v := rationalRepresentation h (template j)) rfl]
  have he : rationalRepresentation h (template j) =
      rationalRepresentation h' (rationalRepresentation (templateChange i)⁻¹ (template j)) := by
    change _ = rationalRepresentation (h * templateChange i) _
    rw [map_mul,LinearEquiv.mul_apply,representation_inverse']
  rw [he,projection_representation g h' hh']
  have hc : dropFirst (rationalRepresentation (templateChange i)⁻¹ (template j)) =
      (projectedSign i j : ℚ) •
        RankTwoAugmentedFrames.template (projectedIndex i j) := by
    rw [← GoodAugmentedNormalForm.rationalVector_integralTemplate,← rationalVector_mulVec]
    have hz := template_quotient_coordinates i j hij
    have hcast := congrArg RankTwoAugmentedFrames.rationalVector hz
    convert hcast using 1
    · rfl
    · rw [← RankTwoAugmentedFrames.rationalVector_integralTemplate (projectedIndex i j)]
      funext r
      simp [RankTwoAugmentedFrames.rationalVector,Pi.smul_apply,smul_eq_mul]
  rw [hc,map_smul]
  change Submodule.span ℚ {(projectedSign i j : ℚ) •
      RankTwoAugmentedFrames.rationalRepresentation _ _} = _
  rw [Submodule.span_singleton_smul_eq
    (isUnit_iff_ne_zero.mpr (by exact_mod_cast projectedSign_ne_zero i j))]
  rfl

/-- The actual link face image is a subset of one literal rank-two augmented frame. -/
theorem mapsFaces (g : IntegralGL) (hbad : ¬Good (augmentedLine g 0).val) :
    OrientedChainMap.MapsFaces (vertex g)
      (GoodLinkExtraction.augmentedGoodLink {augmentedLine g 0})
      RankTwoAugmentedFrames.ambient := by
  classical
  intro s hs
  have hs' : s.Nonempty ∧ {augmentedLine g 0} ∪ s ∈ ambient ∧
      ∀ L ∈ s, Good L.val := by
    convert (GoodLinkExtraction.mem_goodLink ambient _ _ s).mp hs using 1
    apply and_congr
    · apply iff_of_eq
      apply congrArg (fun t : Finset RationalLine => t ∈ ambient)
      ext L
      simp only [Finset.mem_union]
    · rfl
  obtain ⟨_,h,hh⟩ := hs'.2.1
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp (hh (by simp :
    augmentedLine g 0 ∈ {augmentedLine g 0} ∪ s))
  let q := lowerGL (g⁻¹ * (h * templateChange i))
    (first_column_lower_zero g (h * templateChange i) ((templateChange_line h i).trans hi))
  have hf : s.image (vertex g) ∈ RankTwoAugmentedFrames.ambient := by
    apply RankTwoAugmentedFrames.subset_augmentedFrame_mem q (hs'.1.image (vertex g))
    intro L hL
    obtain ⟨M,hM,rfl⟩ := Finset.mem_image.mp hL
    obtain ⟨j,_,hj⟩ := Finset.mem_image.mp (hh (Finset.mem_union_right _ hM))
    have hij : i ≠ j := by
      intro he
      apply hbad
      have hMgood := hs'.2.2 M hM
      rwa [← hj,← he,hi] at hMgood
    apply Finset.mem_image.mpr
    refine ⟨projectedIndex i j,Finset.mem_univ _,?_⟩
    rw [← hj]
    exact (vertex_template g h i j hi hij).symm
  convert hf using 1
  ext L
  simp only [Finset.mem_image]

/-- The quotient map preserves the actual chain support even when projected vertices repeat. -/
theorem transport_mem_chains (g : IntegralGL) (hbad : ¬Good (augmentedLine g 0).val)
    (n : ℕ) {c : OrientedListChains.Chain RationalLine}
    (hc : c ∈ OrientedListChains.chains
      (GoodLinkExtraction.augmentedGoodLink {augmentedLine g 0}) n) :
    OrientedChainMap.map (vertex g) c ∈
      OrientedListChains.chains RankTwoAugmentedFrames.ambient n :=
  OrientedChainMap.map_mem_chains _ _ _ (mapsFaces g hbad) n hc

/-- The arbitrary total vertex map already transports the alternating boundary exactly. -/
theorem boundary_transport (g : IntegralGL) (c : OrientedListChains.Chain RationalLine) :
    OrientedListChains.boundary (OrientedChainMap.map (vertex g) c) =
      OrientedChainMap.map (vertex g) (OrientedListChains.boundary c) :=
  OrientedChainMap.boundary_map (vertex g) c

end TernaryPoly.BadVertexProjection
