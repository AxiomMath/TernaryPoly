module

public import TernaryPeriodPolynomials.Building.BadVertex.Projection
public import TernaryPeriodPolynomials.Building.OrientedChain.ImageFaceBoundary

@[expose] public section


noncomputable section
namespace TernaryPoly.BadVertexProjectionChange
open ModThreeGoodAction AugmentedFrameComplex BadVertexProjection GoodLinkExtraction
open OrientedListChains OrientedImageFaceProjection OrientedImageFaceBoundary

abbrev QuotientLine := RankTwoAugmentedFrames.RationalLine2
abbrev QuotientSpace := RankTwoAugmentedFrames.Space

local instance : DecidableEq QuotientLine := Classical.decEq _
local instance : Nonempty QuotientLine := ⟨RankTwoAugmentedFrames.augmentedLine 1 0⟩
local instance : DecidableEq RationalLine := Classical.decEq _

/-- The actual image of a rational quotient line under an invertible rational linear map. -/
def lineMap (e : QuotientSpace ≃ₗ[ℚ] QuotientSpace) (L : QuotientLine) : QuotientLine :=
  ⟨L.val.map e.toLinearMap,(e.submoduleMap L.val).finrank_eq.symm.trans L.property⟩

theorem lineMap_inverse (e : QuotientSpace ≃ₗ[ℚ] QuotientSpace) (L : QuotientLine) :
    lineMap e.symm (lineMap e L) = L := by
  apply Subtype.ext
  exact (Submodule.map_symm_eq_iff e).mpr rfl

/-- An actual quotient linear equivalence induces a bijection of rational quotient lines. -/
def lineEquiv (e : QuotientSpace ≃ₗ[ℚ] QuotientSpace) : QuotientLine ≃ QuotientLine where
  toFun := lineMap e
  invFun := lineMap e.symm
  left_inv := lineMap_inverse e
  right_inv := lineMap_inverse e.symm

/-- The literal quotient-coordinate change from h-coordinates to g-coordinates. -/
def quotientChange (g h : IntegralGL) (hb : augmentedLine h 0 = augmentedLine g 0) :
    QuotientLine ≃ QuotientLine :=
  lineEquiv (RankTwoAugmentedFrames.rationalRepresentation
    (lowerGL (g⁻¹ * h) (first_column_lower_zero g h hb)))

theorem quotientChange_val (g h : IntegralGL) (hb : augmentedLine h 0 = augmentedLine g 0)
    (L : QuotientLine) :
    (quotientChange g h hb L).val = L.val.map
      (RankTwoAugmentedFrames.rationalRepresentation
        (lowerGL (g⁻¹ * h) (first_column_lower_zero g h hb))).toLinearMap := rfl

/-- The actual linear quotient projections change by the lower block on every vector. -/
theorem projection_change (g h : IntegralGL) (hb : augmentedLine h 0 = augmentedLine g 0)
    (v : Space) :
    projection g v = RankTwoAugmentedFrames.rationalRepresentation
      (lowerGL (g⁻¹ * h) (first_column_lower_zero g h hb)) (projection h v) := by
  have he := projection_representation g h hb (rationalRepresentation h⁻¹ v)
  rw [representation_inverse'] at he
  exact he

/-- The line-level identity excludes the common kernel line, where total projections use fallback. -/
theorem vertex_change (g h : IntegralGL) (hb : augmentedLine h 0 = augmentedLine g 0)
    (L : RationalLine) (hL : L ≠ augmentedLine g 0) :
    vertex g L = quotientChange g h hb (vertex h L) := by
  have hL' : L ≠ augmentedLine h 0 := by rwa [hb]
  apply Subtype.ext
  rw [vertex_val g L hL,quotientChange_val,vertex_val h L hL',← Submodule.map_comp]
  apply congrArg (fun f : Space →ₗ[ℚ] QuotientSpace => L.val.map f)
  apply LinearMap.ext
  intro v
  exact projection_change g h hb v

/-- Good vertices avoid the common bad first line. -/
theorem good_ne_base (g : IntegralGL) (hbad : ¬Good (augmentedLine g 0).val)
    (L : RationalLine) (hgood : Good L.val) : L ≠ augmentedLine g 0 := by
  intro he
  exact hbad (he ▸ hgood)

/-- Every allowed Good-link simplex avoids the kernel, including the empty augmented simplex. -/
theorem allowed_avoids_base (g : IntegralGL) (hbad : ¬Good (augmentedLine g 0).val)
    (l : List RationalLine) (hl : Allowed (augmentedGoodLink {augmentedLine g 0}) l) :
    ∀ L ∈ l, L ≠ augmentedLine g 0 := by
  rcases hl with rfl | hl
  · simp
  · intro L hL
    exact good_ne_base g hbad L (hl.2 L (List.mem_toFinset.mpr hL))

/-- Literal list maps agree after the quotient-coordinate change when the list avoids the kernel. -/
theorem list_map_change (g h : IntegralGL) (hb : augmentedLine h 0 = augmentedLine g 0)
    (l : List RationalLine) (hl : ∀ L ∈ l, L ≠ augmentedLine g 0) :
    (l.map (vertex h)).map (quotientChange g h hb) = l.map (vertex g) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro L hL
  exact (vertex_change g h hb L (hl L hL)).symm

/-- Finite image faces undergo the actual injective quotient-coordinate relabeling. -/
theorem imageFace_change (g h : IntegralGL) (hb : augmentedLine h 0 = augmentedLine g 0)
    (l : List RationalLine) (hl : ∀ L ∈ l, L ≠ augmentedLine g 0) :
    imageFace (vertex g) l = (imageFace (vertex h) l).image (quotientChange g h hb) := by
  rw [imageFace,imageFace,← list_map_change g h hb l hl]
  ext Q
  simp only [List.mem_toFinset,List.mem_map,Finset.mem_image]

/-- The number of quotient vertices does not depend on the adapted basis. -/
theorem imageFace_card_change (g h : IntegralGL) (hb : augmentedLine h 0 = augmentedLine g 0)
    (l : List RationalLine) (hl : ∀ L ∈ l, L ≠ augmentedLine g 0) :
    (imageFace (vertex g) l).card = (imageFace (vertex h) l).card := by
  rw [imageFace_change g h hb l hl,Finset.card_image_of_injective _ (quotientChange g h hb).injective]

/-- Exact image-face equality is preserved and reflected by the actual quotient bijection. -/
theorem imageFace_eq_change (g h : IntegralGL) (hb : augmentedLine h 0 = augmentedLine g 0)
    (l : List RationalLine) (hl : ∀ L ∈ l, L ≠ augmentedLine g 0) (s : Finset QuotientLine) :
    imageFace (vertex g) l = s.image (quotientChange g h hb) ↔ imageFace (vertex h) l = s := by
  rw [imageFace_change g h hb l hl]
  exact Finset.image_inj (quotientChange g h hb).injective

/-- Actual supported link chain maps commute with quotient-coordinate change. -/
theorem map_change (g h : IntegralGL) (hb : augmentedLine h 0 = augmentedLine g 0)
    (hbad : ¬Good (augmentedLine g 0).val) (n : ℕ) {c : Chain RationalLine}
    (hc : c ∈ chains (augmentedGoodLink {augmentedLine g 0}) n) :
    OrientedChainMap.map (quotientChange g h hb) (OrientedChainMap.map (vertex h) c) =
      OrientedChainMap.map (vertex g) c := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨l,_,hl,rfl⟩ := hc
    simp only [OrientedChainMap.map_simplex]
    rw [list_map_change g h hb l (allowed_avoids_base g hbad l hl)]
  | zero => simp only [map_zero]
  | add c d hc hd ihc ihd => simp only [map_add,ihc,ihd]
  | smul q c hc ih => simp only [map_smul,ih]

/-- Exact projected-face components of actual link chains are independent of the adapted chart. -/
theorem project_change (g h : IntegralGL) (hb : augmentedLine h 0 = augmentedLine g 0)
    (hbad : ¬Good (augmentedLine g 0).val) (s : Finset QuotientLine) (n : ℕ)
    {c : Chain RationalLine} (hc : c ∈ chains (augmentedGoodLink {augmentedLine g 0}) n) :
    project (vertex g) (s.image (quotientChange g h hb)) c = project (vertex h) s c := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨l,_,hl,rfl⟩ := hc
    rw [project_simplex,project_simplex]
    have he := imageFace_eq_change g h hb l (allowed_avoids_base g hbad l hl) s
    simp only [he]
  | zero => simp only [map_zero]
  | add c d hc hd ihc ihd => simp only [map_add,ihc,ihd]
  | smul q c hc ih => simp only [map_smul,ih]

/-- Remove precisely the simplices touching the kernel line. This is an actual linear filter. -/
def away (a : RationalLine) : Chain RationalLine →ₗ[ℚ] Chain RationalLine :=
  OrientedChainProjection.filter (fun l => a ∉ l) (fun hp => by dsimp only; rw [hp.mem_iff])

@[simp] theorem away_simplex (a : RationalLine) (l : List RationalLine) :
    away a (simplex l) = if a ∉ l then simplex l else 0 := by
  classical
  have he := OrientedChainProjection.filter_simplex (fun l => a ∉ l)
    (fun hp => by dsimp only; rw [hp.mem_iff]) l
  convert he using 1
  · rfl
  · split_ifs <;> rfl

/-- The kernel-avoidance filter is the identity on actual Good link chains. -/
theorem away_eq_self (g : IntegralGL) (hbad : ¬Good (augmentedLine g 0).val) (n : ℕ)
    {c : Chain RationalLine} (hc : c ∈ chains (augmentedGoodLink {augmentedLine g 0}) n) :
    away (augmentedLine g 0) c = c := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨l,_,hl,rfl⟩ := hc
    have hn : augmentedLine g 0 ∉ l := fun ha =>
      allowed_avoids_base g hbad l hl _ ha rfl
    rw [away_simplex,ite_eq_left hn]
  | zero => simp only [map_zero]
  | add c d hc hd ihc ihd => simp only [map_add,ihc,ihd]
  | smul q c hc ih => simp only [map_smul,ih]

/-- Filtering off the common kernel transports every projected-cardinality bound. -/
theorem away_mem_imageBounded (g h : IntegralGL)
    (hb : augmentedLine h 0 = augmentedLine g 0) (m : ℕ) {c : Chain RationalLine}
    (hc : c ∈ imageBounded (vertex g) m) :
    away (augmentedLine g 0) c ∈ imageBounded (vertex h) m := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨l,hcard,rfl⟩ := hc
    by_cases hn : augmentedLine g 0 ∉ l
    · rw [away_simplex,ite_eq_left hn]
      apply simplex_mem_imageBounded
      have hav : ∀ L ∈ l, L ≠ augmentedLine g 0 := by
        intro L hL he
        exact hn (he ▸ hL)
      rwa [← imageFace_card_change g h hb l hav]
    · rw [away_simplex,ite_eq_right hn]
      exact (imageBounded (vertex h) m).zero_mem
  | zero => simpa only [map_zero] using (imageBounded (vertex h) m).zero_mem
  | add c d hc hd ihc ihd =>
    simpa only [map_add] using (imageBounded (vertex h) m).add_mem ihc ihd
  | smul q c hc ih =>
    simpa only [map_smul] using (imageBounded (vertex h) m).smul_mem q ih

/-- Projected-dimension bounds for supported link chains do not depend on the chosen chart. -/
theorem imageBounded_change (g h : IntegralGL)
    (hb : augmentedLine h 0 = augmentedLine g 0)
    (hbad : ¬Good (augmentedLine g 0).val) (n m : ℕ) {c : Chain RationalLine}
    (hc : c ∈ chains (augmentedGoodLink {augmentedLine g 0}) n)
    (him : c ∈ imageBounded (vertex g) m) : c ∈ imageBounded (vertex h) m := by
  have he := away_mem_imageBounded g h hb m him
  rwa [away_eq_self g hbad n hc] at he

theorem imageBounded_change_iff (g h : IntegralGL)
    (hb : augmentedLine h 0 = augmentedLine g 0)
    (hbad : ¬Good (augmentedLine g 0).val) (n m : ℕ) {c : Chain RationalLine}
    (hc : c ∈ chains (augmentedGoodLink {augmentedLine g 0}) n) :
    c ∈ imageBounded (vertex g) m ↔ c ∈ imageBounded (vertex h) m := by
  constructor
  · exact imageBounded_change g h hb hbad n m hc
  · apply imageBounded_change h g hb.symm (by rwa [hb]) n m
    rwa [hb]

/-- Vanishing of the actual projected chain is independent of an adapted quotient chart. -/
theorem map_eq_zero_change (g h : IntegralGL)
    (hb : augmentedLine h 0 = augmentedLine g 0)
    (hbad : ¬Good (augmentedLine g 0).val) (n : ℕ) {c : Chain RationalLine}
    (hc : c ∈ chains (augmentedGoodLink {augmentedLine g 0}) n) :
    OrientedChainMap.map (vertex g) c = 0 ↔ OrientedChainMap.map (vertex h) c = 0 := by
  rw [← map_change g h hb hbad n hc]
  exact OrientedChainMap.map_eq_zero_iff _ (quotientChange g h hb).injective _

/-- Every finite quotient face retains its cardinality under the actual coordinate change. -/
theorem quotientChange_card (g h : IntegralGL) (hb : augmentedLine h 0 = augmentedLine g 0)
    (s : Finset QuotientLine) : (s.image (quotientChange g h hb)).card = s.card :=
  Finset.card_image_of_injective _ (quotientChange g h hb).injective

/-- The standard quotient augmented lines transform to the literal lower-block frame lines. -/
theorem quotientChange_template (g h : IntegralGL)
    (hb : augmentedLine h 0 = augmentedLine g 0) (i : Fin 3) :
    quotientChange g h hb (RankTwoAugmentedFrames.augmentedLine 1 i) =
      RankTwoAugmentedFrames.augmentedLine
        (lowerGL (g⁻¹ * h) (first_column_lower_zero g h hb)) i := by
  apply Subtype.ext
  rw [quotientChange_val]
  change (Submodule.span ℚ {(RankTwoAugmentedFrames.rationalRepresentation 1
    (RankTwoAugmentedFrames.template i))}).map _ = _
  rw [map_one]
  change (Submodule.span ℚ {RankTwoAugmentedFrames.template i}).map _ = _
  rw [Submodule.map_span,Set.image_singleton]
  rfl

/-- Reexpressing an arbitrary fixed projected face uses the inverse actual quotient bijection. -/
theorem project_change_inverse (g h : IntegralGL)
    (hb : augmentedLine h 0 = augmentedLine g 0)
    (hbad : ¬Good (augmentedLine g 0).val) (s : Finset QuotientLine) (n : ℕ)
    {c : Chain RationalLine} (hc : c ∈ chains (augmentedGoodLink {augmentedLine g 0}) n) :
    project (vertex g) s c =
      project (vertex h) (s.image (quotientChange g h hb).symm) c := by
  have he := project_change g h hb hbad (s.image (quotientChange g h hb).symm) n hc
  have hs : (s.image (quotientChange g h hb).symm).image (quotientChange g h hb) = s := by
    rw [Finset.image_image]
    simp only [Function.comp_def,Equiv.apply_symm_apply,Finset.image_id']
  rwa [hs] at he

end TernaryPoly.BadVertexProjectionChange
