module

public import TernaryPeriodPolynomials.Building.BadVertex.Projection
public import TernaryPeriodPolynomials.Building.Coherent.PrismReduction
public import Mathlib.Data.List.OfFn

@[expose] public section


noncomputable section
namespace TernaryPoly.BadVertexSimplexNormalForm
open ModThreeGoodAction AugmentedFrameComplex GoodLinkExtraction GoodIntegralNormalization
open CoherentPrismReduction BadVertexProjection

local instance : DecidableEq RationalLine := Classical.decEq _

/-- The ordered three-element complement of each possible bad template index. -/
def remainingIndex : Fin 4 → Fin 3 → Fin 4 :=
  ![![1,3,2], ![0,3,2], ![0,1,3], ![1,0,2]]

theorem remainingIndex_injective : ∀ i, Function.Injective (remainingIndex i) := by
  decide +kernel

theorem remainingIndex_range : ∀ i j, (∃ k, remainingIndex i k = j) ↔ j ≠ i := by
  decide +kernel

/-- The only coherent template case has the bad vertex outside the additive core. -/
def normalFiber : Fin 4 → Fin 3 → Fin 3 :=
  ![![0,0,1], ![0,0,1], ![0,1,2], ![0,0,1]]

def normalHeight : Fin 4 → Fin 3 → ℤ :=
  ![![0,1,0], ![0,1,0], ![0,0,0], ![-1,0,0]]

def normalSign (i : Fin 4) (j : Fin 3) : ℤ := if i = 3 ∧ j = 0 then -1 else 1

theorem normalSign_ne_zero (i : Fin 4) (j : Fin 3) : normalSign i j ≠ 0 := by
  unfold normalSign
  split <;> norm_num

/-- Exact integral identities, including the sign on the original second column. -/
theorem normal_coordinates : ∀ i j,
    (templateChange i).val.mulVec (fiberCoefficient (normalFiber i j) (normalHeight i j)) =
      normalSign i j • GoodAugmentedNormalForm.integralTemplate (remainingIndex i j) := by
  decide +kernel

theorem normal_line (h : IntegralGL) (i : Fin 4) (j : Fin 3) :
    fiberLine (h * templateChange i) (normalFiber i j) (normalHeight i j) =
      augmentedLine h (remainingIndex i j) := by
  apply Subtype.ext
  change Submodule.span ℚ {(rationalRepresentation (h * templateChange i)
    (rationalVector (fiberCoefficient (normalFiber i j) (normalHeight i j))))} = _
  rw [map_mul,LinearEquiv.mul_apply,← rationalVector_mulVec,normal_coordinates]
  have hc : rationalVector (normalSign i j •
      GoodAugmentedNormalForm.integralTemplate (remainingIndex i j)) =
      (normalSign i j : ℚ) • template (remainingIndex i j) := by
    rw [← GoodAugmentedNormalForm.rationalVector_integralTemplate]
    funext r
    simp [rationalVector,Pi.smul_apply,smul_eq_mul]
  rw [hc,map_smul,Submodule.span_singleton_smul_eq
    (isUnit_iff_ne_zero.mpr (by exact_mod_cast normalSign_ne_zero i j))]
  rfl

/-- Canonical order of the three remaining actual frame vertices. -/
def remainingLines (h : IntegralGL) (i : Fin 4) : List RationalLine :=
  List.ofFn (fun j => augmentedLine h (remainingIndex i j))

theorem remainingLines_nodup (h : IntegralGL) (i : Fin 4) :
    (remainingLines h i).Nodup :=
  List.nodup_ofFn.mpr ((AugmentedBadFaces.augmentedLine_injective h).comp
    (remainingIndex_injective i))

theorem mem_remainingLines (h : IntegralGL) (i : Fin 4) (L : RationalLine) :
    L ∈ remainingLines h i ↔ L ∈ augmentedFrame h ∧ L ≠ augmentedLine h i := by
  let : DecidableEq RationalLine := fun a b => Subtype.instDecidableEq a b
  rw [remainingLines,List.mem_ofFn]
  constructor
  · rintro ⟨j,rfl⟩
    refine ⟨Finset.mem_image.mpr ⟨remainingIndex i j,Finset.mem_univ _,rfl⟩,?_⟩
    intro he
    exact (remainingIndex_range i (remainingIndex i j)).mp ⟨j,rfl⟩
      (AugmentedBadFaces.augmentedLine_injective h he)
  · rintro ⟨hL,hne⟩
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hL
    have hji : j ≠ i := fun he => hne (congrArg (augmentedLine h) he)
    obtain ⟨k,hk⟩ := (remainingIndex_range i j).mpr hji
    exact ⟨k,congrArg (augmentedLine h) hk⟩

theorem remainingLines_normal (h : IntegralGL) (i : Fin 4) :
    remainingLines h i = List.ofFn (fun j =>
      fiberLine (h * templateChange i) (normalFiber i j) (normalHeight i j)) := by
  unfold remainingLines
  apply congrArg List.ofFn
  funext j
  exact (normal_line h i j).symm

/-- A three-vertex Good link face fills the complement of its bad vertex in an actual frame. -/
theorem exists_template_chart (a : RationalLine) (ha : ¬Good a.val)
    (l : List RationalLine) (hlen : l.length = 3) (hn : l.Nodup)
    (hl : l.toFinset ∈ augmentedGoodLink {a}) :
    ∃ h : IntegralGL, ∃ i : Fin 4, augmentedLine h i = a ∧
      l.Perm (remainingLines h i) ∧
      ∀ j : Fin 3, Good (augmentedLine h (remainingIndex i j)).val := by
  have hgood : ∀ L ∈ l.toFinset, Good L.val := hl.2
  have haL : a ∉ l.toFinset := fun hm => ha (hgood a hm)
  obtain ⟨_,h,hsub⟩ := hl.1.2
  have hcard : ({a} ∪ l.toFinset).card = 4 := by
    rw [Finset.singleton_union,Finset.card_insert_of_notMem haL,
      List.toFinset_card_of_nodup hn,hlen]
  have heq : {a} ∪ l.toFinset = augmentedFrame h :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcard,AugmentedBadFaces.augmentedFrame_card])
  have ham : a ∈ augmentedFrame h := hsub (Finset.mem_union_left _ (Finset.mem_singleton_self a))
  have hex : ∃ i, augmentedLine h i = a := by
    let : DecidableEq RationalLine := fun a b => Subtype.instDecidableEq a b
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp ham
    exact ⟨i,hi⟩
  obtain ⟨i,hi⟩ := hex
  have hm (L : RationalLine) : L ∈ l ↔ L ∈ remainingLines h i := by
    rw [mem_remainingLines,hi,← heq]
    simp only [Finset.mem_union,Finset.mem_singleton,List.mem_toFinset]
    constructor
    · intro hL
      exact ⟨Or.inr hL,fun he => haL (List.mem_toFinset.mpr (he ▸ hL))⟩
    · rintro ⟨hL,hne⟩
      exact hL.resolve_left hne
  refine ⟨h,i,hi,(List.perm_ext_iff_of_nodup hn (remainingLines_nodup h i)).mpr hm,?_⟩
  intro j
  apply hgood
  apply List.mem_toFinset.mpr
  apply (hm _).mpr
  exact List.mem_ofFn.mpr ⟨j,rfl⟩

/-- Every displayed affine fiber vector is primitive. -/
theorem fiberCoefficient_primitive (i : Fin 3) (k : ℤ) :
    Primitive (fiberCoefficient i k) := by
  fin_cases i
  · apply GoodAugmentedNormalForm.primitive_of_bezout (b := ![0,1,0])
    simp [fiberCoefficient,Fin.sum_univ_three]
  · apply GoodAugmentedNormalForm.primitive_of_bezout (b := ![0,0,1])
    simp [fiberCoefficient,Fin.sum_univ_three]
  · apply GoodAugmentedNormalForm.primitive_of_bezout (b := ![0,1,0])
    simp [fiberCoefficient,Fin.sum_univ_three]

/-- Goodness is exactly the nonvanishing projected residue, independently of fiber height. -/
theorem fiberLine_good_iff (g : IntegralGL)
    (hb : AugmentedPrismCaps.columnResidue g 0 = 0) (i : Fin 3) (k : ℤ) :
    Good (fiberLine g i k).val ↔
      (![AugmentedPrismCaps.columnResidue g 1,AugmentedPrismCaps.columnResidue g 2,
        AugmentedPrismCaps.columnResidue g 1 + AugmentedPrismCaps.columnResidue g 2] i) ≠ 0 := by
  rw [fiberLine_val,GoodAugmentedNormalForm.good_span_iff_residue
    (GoodAugmentedNormalForm.primitive_mulVec g (fiberCoefficient_primitive i k)),
    fiberVector_residue,hb,zero_mul,zero_add]

/-- The local chart is coherent exactly when the bad vertex is outside the additive core. -/
theorem template_chart_classification (h : IntegralGL) (i : Fin 4)
    (hbad : ¬Good (augmentedLine h i).val)
    (hgood : ∀ j : Fin 3, Good (augmentedLine h (remainingIndex i j)).val) :
    let g := h * templateChange i
    AugmentedPrismCaps.columnResidue g 0 = 0 ∧
    AugmentedPrismCaps.columnResidue g 1 ≠ 0 ∧
    AugmentedPrismCaps.columnResidue g 2 ≠ 0 ∧
    ((AugmentedPrismCaps.columnResidue g 1 + AugmentedPrismCaps.columnResidue g 2 ≠ 0 ∧
      remainingLines h i = [xFiber g 0,yFiber g 0,zFiber g 0]) ∨
      ∃ k : ℤ, (k = 0 ∨ k = -1) ∧
        remainingLines h i = [xFiber g k,xFiber g (k+1),yFiber g 0]) := by
  dsimp only
  have hb : AugmentedPrismCaps.columnResidue (h * templateChange i) 0 = 0 := by
    have hbad' : ¬Good (augmentedLine (h * templateChange i) 0).val := by
      rwa [templateChange_line]
    exact AugmentedBadFaces.bad_augmentedLine_residue (h * templateChange i) 0 hbad'
  have hg (j : Fin 3) := (fiberLine_good_iff (h * templateChange i) hb
    (normalFiber i j) (normalHeight i j)).mp
      (by rw [normal_line]; exact hgood j)
  refine ⟨hb,?_⟩
  have h0 := hg 0
  have h1 := hg 1
  have h2 := hg 2
  rw [remainingLines_normal]
  fin_cases i
  · refine ⟨h0,h2,Or.inr ⟨0,Or.inl rfl,?_⟩⟩
    simp [normalFiber,normalHeight,List.ofFn_succ]
  · refine ⟨h0,h2,Or.inr ⟨0,Or.inl rfl,?_⟩⟩
    simp [normalFiber,normalHeight,List.ofFn_succ]
  · refine ⟨h0,h1,Or.inl ⟨h2,?_⟩⟩
    simp [normalFiber,normalHeight,List.ofFn_succ]
  · refine ⟨h0,h2,Or.inr ⟨-1,Or.inr rfl,?_⟩⟩
    simp [normalFiber,normalHeight,List.ofFn_succ]

/-- Exhaustive normal form for every actual nodup Good bad-vertex-link triangle. -/
theorem triangle_normal_form (a : RationalLine) (ha : ¬Good a.val)
    (l : List RationalLine) (hlen : l.length = 3) (hn : l.Nodup)
    (hl : l.toFinset ∈ augmentedGoodLink {a}) :
    ∃ g : IntegralGL, augmentedLine g 0 = a ∧
      AugmentedPrismCaps.columnResidue g 0 = 0 ∧
      AugmentedPrismCaps.columnResidue g 1 ≠ 0 ∧
      AugmentedPrismCaps.columnResidue g 2 ≠ 0 ∧
      ((AugmentedPrismCaps.columnResidue g 1 + AugmentedPrismCaps.columnResidue g 2 ≠ 0 ∧
        l.Perm [xFiber g 0,yFiber g 0,zFiber g 0]) ∨
        ∃ k : ℤ, (k = 0 ∨ k = -1) ∧ l.Perm [xFiber g k,xFiber g (k+1),yFiber g 0]) := by
  obtain ⟨h,i,hi,hperm,hgood⟩ := exists_template_chart a ha l hlen hn hl
  obtain ⟨hb,hX,hY,hcases⟩ := template_chart_classification h i (hi ▸ ha) hgood
  refine ⟨h * templateChange i,(templateChange_line h i).trans hi,hb,hX,hY,?_⟩
  rcases hcases with ⟨hZ,he⟩ | ⟨k,hk,he⟩
  · exact Or.inl ⟨hZ,he ▸ hperm⟩
  · exact Or.inr ⟨k,hk,he ▸ hperm⟩

/-- The quotient template slots agree with the three local fiber types. -/
theorem normal_projected_index : ∀ i j,
    projectedIndex i (remainingIndex i j) = normalFiber i j := by
  decide +kernel

/-- Compatibility of the actual normal chart with any fixed quotient projection. -/
theorem remainingLines_projection (g h : IntegralGL) (i : Fin 4)
    (hi : augmentedLine h i = augmentedLine g 0) :
    (remainingLines h i).map (vertex g) =
      List.ofFn (fun j => RankTwoAugmentedFrames.augmentedLine
        (lowerGL (g⁻¹ * (h * templateChange i))
          (first_column_lower_zero g (h * templateChange i) ((templateChange_line h i).trans hi)))
        (normalFiber i j)) := by
  rw [remainingLines,List.map_ofFn]
  apply congrArg List.ofFn
  funext j
  dsimp only [Function.comp_apply]
  rw [vertex_template g h i (remainingIndex i j) hi
    (Ne.symm ((remainingIndex_range i (remainingIndex i j)).mp ⟨j,rfl⟩)),normal_projected_index]

/-- A Good link triangle admits a local chart whose ordered quotient is literally its base face. -/
theorem triangle_projected_chart (g : IntegralGL)
    (hbad : ¬Good (augmentedLine g 0).val) (l : List RationalLine)
    (hlen : l.length = 3) (hn : l.Nodup)
    (hl : l.toFinset ∈ augmentedGoodLink {augmentedLine g 0}) :
    ∃ h : IntegralGL, ∃ i : Fin 4, ∃ hi : augmentedLine h i = augmentedLine g 0,
      l.Perm (remainingLines h i) ∧
      (l.map (vertex g)).Perm
        (List.ofFn (fun j => RankTwoAugmentedFrames.augmentedLine
          (lowerGL (g⁻¹ * (h * templateChange i))
            (first_column_lower_zero g (h * templateChange i) ((templateChange_line h i).trans hi)))
          (normalFiber i j))) ∧
      ∀ j : Fin 3, Good (augmentedLine h (remainingIndex i j)).val := by
  obtain ⟨h,i,hi,hperm,hgood⟩ := exists_template_chart _ hbad l hlen hn hl
  refine ⟨h,i,hi,hperm,?_,hgood⟩
  rw [← remainingLines_projection g h i hi]
  exact hperm.map (vertex g)

end TernaryPoly.BadVertexSimplexNormalForm
