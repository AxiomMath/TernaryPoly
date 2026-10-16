module

public import TernaryPeriodPolynomials.Building.IntegralFrameHeightReduction
public import TernaryPeriodPolynomials.Building.BadEdge.NormalForm
public import TernaryPeriodPolynomials.Building.Ambient.DependentTriangles
public import TernaryPeriodPolynomials.Building.Good.LinkExtraction
public import TernaryPeriodPolynomials.Building.OrientedChain.ChainMap

@[expose] public section


noncomputable section
namespace TernaryPoly.AmbientEdgeRetraction
open ModThreeGoodAction GoodIntegralNormalization PrimitiveLineUniqueness
open GoodAugmentedNormalForm AugmentedFrameComplex AugmentedBadFaces
open PrimitiveLineHeight IntegralFrameHeightReduction

/-- The unrestricted actual vertex link, with the fixed vertex excluded. -/
def link (w : RationalLine) : PreAbstractSimplicialComplex RationalLine :=
  GoodLinkExtraction.goodLink ambient (fun L => L ≠ w) {w}

/-- The full subcomplex of the actual link below the specified primitive height. -/
def lowLink (F : IntegralVector →ₗ[ℤ] ℤ) (W : IntegralVector) (w : RationalLine) :
    PreAbstractSimplicialComplex RationalLine :=
  GoodLinkExtraction.goodLink ambient
    (fun L => L ≠ w ∧ (height F L : ℤ) < F W) {w}

@[simp] theorem singleton_mem_link (w L : RationalLine) :
    {L} ∈ link w ↔ {w,L} ∈ ambient ∧ L ≠ w := by
  let : DecidableEq RationalLine := fun a b => Subtype.instDecidableEq a b
  simp [link,GoodLinkExtraction.mem_goodLink]
  intro _
  constructor <;> intro h <;> convert h using 1 <;> ext x <;> simp

/-- Independent signs on the columns are genuine integral changes of basis. -/
def columnSigns (s : Fin 3 → ℤ) (hs : ∀ j, s j * s j = 1) : IntegralGL where
  val := Matrix.diagonal s
  inv := Matrix.diagonal s
  val_inv := by simp [Matrix.diagonal_mul_diagonal,hs]
  inv_val := by simp [Matrix.diagonal_mul_diagonal,hs]

theorem mul_columnSigns_col (g : IntegralGL) (s : Fin 3 → ℤ)
    (hs : ∀ j, s j * s j = 1) (j : Fin 3) :
    (g * columnSigns s hs).val.col j = s j • g.val.col j := by
  ext i
  change (g.val * Matrix.diagonal s) i j = s j * g.val i j
  rw [Matrix.mul_diagonal,mul_comm]

/-- Any specified primitive generators on the column lines can be installed exactly. -/
theorem exists_basis_columns (g : IntegralGL) (v : Fin 3 → IntegralVector)
    (hp : ∀ j, Primitive (v j))
    (hspan : ∀ j, Submodule.span ℚ {rationalVector (v j)} =
      (augmentedLine g j.castSucc).val) :
    ∃ h : IntegralGL, ∀ j, h.val.col j = v j := by
  have he (j : Fin 3) : ∃ s : ℤ, s*s=1 ∧ v j = s • g.val.col j := by
    rcases primitive_eq_or_neg_of_span_eq (hp j) (column_primitive g j)
      ((hspan j).trans (columnLine_span g j)) with h | h
    · exact ⟨1,by norm_num,by simpa using h⟩
    · exact ⟨-1,by norm_num,by simpa using h⟩
  choose s hs hv using he
  exact ⟨g * columnSigns s hs,fun j => (mul_columnSigns_col g s hs j).trans (hv j).symm⟩

/-- An actual link vertex admits an integral basis with the chosen primitive directions. -/
theorem link_vertex_basis (F : IntegralVector →ₗ[ℤ] ℤ) (W : IntegralVector)
    (w L : RationalLine) (hW : Primitive W)
    (hspan : Submodule.span ℚ {rationalVector W} = w.val) (hL : {L} ∈ link w) :
    ∃ g : IntegralGL, g.val.col 0 = W ∧
      g.val.col 1 = nonnegativeRepresentative F L := by
  obtain ⟨hface,hne⟩ := (singleton_mem_link w L).mp hL
  obtain ⟨g,hg0,hg1⟩ := BadEdgeNormalForm.ordered_ambient_edge w L hne.symm hface
  let v : Fin 3 → IntegralVector := ![W,nonnegativeRepresentative F L,g.val.col 2]
  have hp : ∀ j, Primitive (v j) := by
    intro j
    fin_cases j
    · exact hW
    · exact nonnegativeRepresentative_primitive F L
    · exact column_primitive g 2
  have hs : ∀ j, Submodule.span ℚ {rationalVector (v j)} =
      (augmentedLine g j.castSucc).val := by
    intro j
    fin_cases j
    · exact hspan.trans (congrArg Subtype.val hg0).symm
    · exact (nonnegativeRepresentative_span F L).trans (congrArg Subtype.val hg1).symm
    · exact (columnLine_span g 2).symm
  obtain ⟨h,hh⟩ := exists_basis_columns g v hp hs
  exact ⟨h,hh 0,hh 1⟩

/-- The literal quotient/remainder vector for the chosen nonnegative primitive generator. -/
def reducedVector (F : IntegralVector →ₗ[ℤ] ℤ) (W : IntegralVector)
    (L : RationalLine) : IntegralVector :=
  remainderVector F W (nonnegativeRepresentative F L)

/-- Total line map; the fallback is irrelevant on actual link vertices. -/
def retract (F : IntegralVector →ₗ[ℤ] ℤ) (W : IntegralVector)
    (L : RationalLine) : RationalLine :=
  if h : rationalVector (reducedVector F W L) ≠ 0 then
    vectorLine (rationalVector (reducedVector F W L)) h else L

/-- A basis realizing the two chosen directions realizes the remainder as its reduced second column. -/
theorem reducedVector_eq_column (F : IntegralVector →ₗ[ℤ] ℤ)
    (W : IntegralVector) (L : RationalLine) (g : IntegralGL)
    (hg0 : g.val.col 0 = W) (hg1 : g.val.col 1 = nonnegativeRepresentative F L) :
    reducedVector F W L = (reducedBasis F g).val.col 1 := by
  trans remainderVector F (g.val.col 0) (normalized F (g.val.col 1))
  · change remainderVector F W (nonnegativeRepresentative F L) = _
    rw [hg0,hg1,normalized_eq_self F _ (nonnegativeRepresentative_nonneg F L)]
  · exact (reducedBasis_col_remainder F g (0 : Fin 2)).symm

theorem reducedVector_primitive (F : IntegralVector →ₗ[ℤ] ℤ) (W : IntegralVector)
    (w L : RationalLine) (hW : Primitive W)
    (hspan : Submodule.span ℚ {rationalVector W} = w.val) (hL : {L} ∈ link w) :
    Primitive (reducedVector F W L) := by
  obtain ⟨g,hg0,hg1⟩ := link_vertex_basis F W w L hW hspan hL
  rw [reducedVector_eq_column F W L g hg0 hg1]
  exact column_primitive _ _

theorem reducedVector_ne_zero (F : IntegralVector →ₗ[ℤ] ℤ) (W : IntegralVector)
    (w L : RationalLine) (hW : Primitive W)
    (hspan : Submodule.span ℚ {rationalVector W} = w.val) (hL : {L} ∈ link w) :
    rationalVector (reducedVector F W L) ≠ 0 :=
  AmbientIndependentTriple.rationalVector_ne_zero_of_primitive
    (reducedVector_primitive F W w L hW hspan hL)

theorem retract_span (F : IntegralVector →ₗ[ℤ] ℤ) (W : IntegralVector)
    (w L : RationalLine) (hW : Primitive W)
    (hspan : Submodule.span ℚ {rationalVector W} = w.val) (hL : {L} ∈ link w) :
    (retract F W L).val = Submodule.span ℚ {rationalVector (reducedVector F W L)} := by
  simp only [retract,dite_eq_left (reducedVector_ne_zero F W w L hW hspan hL)]
  rfl

/-- All already-low vertices are fixed, even outside the actual link. -/
theorem retract_eq_self (F : IntegralVector →ₗ[ℤ] ℤ) (W : IntegralVector)
    (L : RationalLine) (hL : (height F L : ℤ) < F W) : retract F W L = L := by
  have hv : reducedVector F W L = nonnegativeRepresentative F L :=
    remainderVector_nonnegativeRepresentative F W L hL
  simp only [retract,hv,dite_eq_left (nonnegativeRepresentative_ne_zero F L)]
  exact nonnegativeRepresentative_line F L

/-- The reduced vertex is the literal second column line of the reduced integral basis. -/
theorem retract_eq_columnLine (F : IntegralVector →ₗ[ℤ] ℤ)
    (W : IntegralVector) (L : RationalLine) (g : IntegralGL)
    (hg0 : g.val.col 0 = W) (hg1 : g.val.col 1 = nonnegativeRepresentative F L) :
    retract F W L = augmentedLine (reducedBasis F g) 1 := by
  have hp : Primitive (reducedVector F W L) := by
    rw [reducedVector_eq_column F W L g hg0 hg1]
    exact column_primitive _ _
  have hn := AmbientIndependentTriple.rationalVector_ne_zero_of_primitive hp
  apply Subtype.ext
  simp only [retract,dite_eq_left hn]
  change Submodule.span ℚ {rationalVector (reducedVector F W L)} = _
  rw [reducedVector_eq_column F W L g hg0 hg1]
  exact (columnLine_span _ 1).symm

/-- Primitive height strictly drops at every vertex of the actual unrestricted link. -/
theorem retract_height_lt (F : IntegralVector →ₗ[ℤ] ℤ) (W : IntegralVector)
    (w L : RationalLine) (hW : Primitive W)
    (hspan : Submodule.span ℚ {rationalVector W} = w.val) (hN : 0 < F W)
    (hL : {L} ∈ link w) : (height F (retract F W L) : ℤ) < F W := by
  obtain ⟨g,hg0,hg1⟩ := link_vertex_basis F W w L hW hspan hL
  rw [retract_eq_columnLine F W L g hg0 hg1,← hg0]
  exact reducedBasis_height_lt F g (hg0 ▸ hN) 0

/-- The reduced vertex remains in the actual unrestricted link. -/
theorem retract_mem_link (F : IntegralVector →ₗ[ℤ] ℤ) (W : IntegralVector)
    (w L : RationalLine) (hW : Primitive W)
    (hspan : Submodule.span ℚ {rationalVector W} = w.val) (hL : {L} ∈ link w) :
    {retract F W L} ∈ link w := by
  classical
  obtain ⟨g,hg0,hg1⟩ := link_vertex_basis F W w L hW hspan hL
  have he0 : augmentedLine (reducedBasis F g) 0 = w := by
    apply Subtype.ext
    rw [show (0 : Fin 4) = (0 : Fin 3).castSucc from rfl,
      columnLine_span,reducedBasis_col_zero,hg0]
    exact hspan
  rw [retract_eq_columnLine F W L g hg0 hg1,← he0,singleton_mem_link]
  constructor
  · apply subset_augmentedFrame_mem (reducedBasis F g) (by simp)
    intro K hK
    simp only [Finset.mem_insert,Finset.mem_singleton] at hK
    rcases hK with rfl | rfl
    · exact Finset.mem_image.mpr ⟨0,Finset.mem_univ _,rfl⟩
    · exact Finset.mem_image.mpr ⟨1,Finset.mem_univ _,rfl⟩
  · exact fun h => (by decide : (1 : Fin 4) ≠ 0) (augmentedLine_injective _ h)

/-- Translation by an integral multiple of the reduction direction preserves the remainder vector. -/
theorem remainderVector_add_smul (F : IntegralVector →ₗ[ℤ] ℤ)
    (W v : IntegralVector) (k : ℤ) (hN : F W ≠ 0) :
    remainderVector F W (v + k • W) = remainderVector F W v := by
  unfold remainderVector
  rw [map_add,map_smul,smul_eq_mul,Int.add_mul_ediv_right _ _ hN,add_smul]
  abel

/-- In the sum case, nonnegative primitive heights either are both low or give opposite remainders. -/
theorem remainder_sum_cases (F : IntegralVector →ₗ[ℤ] ℤ) (W v u : IntegralVector)
    (hN : 0 < F W) (hv : 0 ≤ F v) (hu : 0 ≤ F u) (he : W = v + u) :
    (F v < F W ∧ F u < F W) ∨ remainderVector F W v = -remainderVector F W u := by
  have hval : F W = F v + F u := by rw [he,map_add]
  by_cases hv' : F v < F W
  · by_cases hu' : F u < F W
    · exact Or.inl ⟨hv',hu'⟩
    · right
      have hv0 : F v = 0 := by omega
      have huN : F u = F W := by omega
      rw [remainderVector_eq_self F W v hv hv']
      simp only [remainderVector,huN,Int.ediv_self (ne_of_gt hN),one_smul]
      rw [he]
      abel
  · right
    have hvN : F v = F W := by omega
    have hu0 : F u = 0 := by omega
    rw [remainderVector_eq_self F W u hu (by omega)]
    simp only [remainderVector,hvN,Int.ediv_self (ne_of_gt hN),one_smul]
    rw [he]
    abel

/-- Every signed additive relation gives fixed low vertices or equal actual remainder lines. -/
theorem signed_remainder_cases (F : IntegralVector →ₗ[ℤ] ℤ) (W v u : IntegralVector)
    (hN : 0 < F W) (hv : 0 ≤ F v) (hu : 0 ≤ F u)
    (s t : ℤ) (hs : s*s=1) (ht : t*t=1) (he : W = s • v + t • u) :
    (F v < F W ∧ F u < F W) ∨
      Submodule.span ℚ {rationalVector (remainderVector F W v)} =
        Submodule.span ℚ {rationalVector (remainderVector F W u)} := by
  have hs' : s = 1 ∨ s = -1 := Int.isUnit_eq_one_or (IsUnit.of_mul_eq_one s hs)
  have ht' : t = 1 ∨ t = -1 := Int.isUnit_eq_one_or (IsUnit.of_mul_eq_one t ht)
  rcases hs' with rfl | rfl <;> rcases ht' with rfl | rfl
  · simp only [one_smul] at he
    rcases remainder_sum_cases F W v u hN hv hu he with hl | hr
    · exact Or.inl hl
    · right
      rw [hr,span_neg]
  · simp only [one_smul,neg_one_smul] at he
    right
    have hv' : v = u + (1 : ℤ) • W := by rw [he,one_smul]; abel
    rw [hv',remainderVector_add_smul F W u 1 (ne_of_gt hN)]
  · simp only [one_smul,neg_one_smul] at he
    right
    have hu' : u = v + (1 : ℤ) • W := by rw [he,one_smul]; abel
    rw [hu',remainderVector_add_smul F W v 1 (ne_of_gt hN)]
  · simp only [neg_one_smul] at he
    have hval : F W = -F v + -F u := by rw [he,map_add,map_neg,map_neg]
    omega

/-- Equality of primitive remainder spans is equality of the actual line map on link vertices. -/
theorem retract_eq_of_remainder_span (F : IntegralVector →ₗ[ℤ] ℤ) (W : IntegralVector)
    (w L M : RationalLine) (hW : Primitive W)
    (hspan : Submodule.span ℚ {rationalVector W} = w.val)
    (hL : {L} ∈ link w) (hM : {M} ∈ link w)
    (he : Submodule.span ℚ {rationalVector (reducedVector F W L)} =
      Submodule.span ℚ {rationalVector (reducedVector F W M)}) :
    retract F W L = retract F W M := by
  apply Subtype.ext
  rw [retract_span F W w L hW hspan hL,retract_span F W w M hW hspan hM]
  exact he

/-- The two possible signs used in the finite additive-core certificate. -/
def signChoice : Fin 2 → ℤ := ![1,-1]

theorem signChoice_sq (i : Fin 2) : signChoice i * signChoice i = 1 := by
  fin_cases i <;> decide

/-- Each ordered additive template generator is a signed sum of the other two. -/
theorem core_template_relation : ∀ i j k : Fin 3, ([i,j,k] : List (Fin 3)).Nodup →
    ∃ a b : Fin 2,
      integralTemplate (AmbientDependentTriangles.coreIndex i) =
        signChoice a • integralTemplate (AmbientDependentTriangles.coreIndex j) +
        signChoice b • integralTemplate (AmbientDependentTriangles.coreIndex k) := by
  decide +kernel

/-- A primitive generator of an actual template line has an exact integral sign. -/
theorem primitive_template_sign (g : IntegralGL) (i : Fin 4) (v : IntegralVector)
    (hp : Primitive v) (hs : Submodule.span ℚ {rationalVector v} = (augmentedLine g i).val) :
    ∃ a : ℤ, a*a=1 ∧ v = a • g.val.mulVec (integralTemplate i) := by
  obtain ⟨a,ha⟩ := AmbientIndependentTriple.primitive_eq_unit_template g i hp hs
  refine ⟨a,?_,ha⟩
  rcases Int.units_eq_one_or a with rfl | rfl <;> norm_num

/-- Signed additive coefficients persist under independent choices of primitive signs. -/
theorem relation_change_signs (x y z W v u : IntegralVector) (a b c s t : ℤ)
    (ha : a*a=1) (hb : b*b=1) (hc : c*c=1) (hs : s*s=1) (ht : t*t=1)
    (hW : W = a • x) (hv : v = b • y) (hu : u = c • z) (he : x = s • y + t • z) :
    ∃ p q : ℤ, p*p=1 ∧ q*q=1 ∧ W = p • v + q • u := by
  refine ⟨a*s*b,a*t*c,?_,?_,?_⟩
  · calc
      (a*s*b)*(a*s*b) = (a*a)*(s*s)*(b*b) := by ring
      _ = 1 := by rw [ha,hs,hb]; norm_num
  · calc
      (a*t*c)*(a*t*c) = (a*a)*(t*t)*(c*c) := by ring
      _ = 1 := by rw [ha,ht,hc]; norm_num
  · rw [hW,hv,hu,he]
    ext i
    change a * (s * y i + t * z i) = (a*s*b)*(b*y i) + (a*t*c)*(c*z i)
    calc
      _ = (a*s)*(b*b)*y i + (a*t)*(c*c)*z i := by rw [hb,hc]; ring
      _ = _ := by ring

/-- The actual additive-core permutation has the signed relation among any primitive generators. -/
theorem primitive_core_relation (g : IntegralGL) (w L M : RationalLine)
    (hperm : [w,L,M].Perm (AmbientDependentTriangles.coreList g))
    (hn : [w,L,M].Nodup) (W v u : IntegralVector)
    (hW : Primitive W) (hv : Primitive v) (hu : Primitive u)
    (hsW : Submodule.span ℚ {rationalVector W} = w.val)
    (hsv : Submodule.span ℚ {rationalVector v} = L.val)
    (hsu : Submodule.span ℚ {rationalVector u} = M.val) :
    ∃ s t : ℤ, s*s=1 ∧ t*t=1 ∧ W = s • v + t • u := by
  have hmem (K : RationalLine) (hK : K ∈ [w,L,M]) :
      ∃ i : Fin 3, augmentedLine g (AmbientDependentTriangles.coreIndex i) = K := by
    have hm := hperm.mem_iff.mp hK
    simp only [AmbientDependentTriangles.coreList,List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩
  obtain ⟨i,hi⟩ := hmem w (by simp)
  obtain ⟨j,hj⟩ := hmem L (by simp)
  obtain ⟨k,hk⟩ := hmem M (by simp)
  have hidx : ([i,j,k] : List (Fin 3)).Nodup := by
    apply List.Nodup.of_map (f := fun a => augmentedLine g (AmbientDependentTriangles.coreIndex a))
    simpa only [List.map_cons,List.map_nil,hi,hj,hk] using hn
  obtain ⟨s,t,hst⟩ := core_template_relation i j k hidx
  obtain ⟨a,ha,hWa⟩ := primitive_template_sign g _ W hW (hsW.trans (congrArg Subtype.val hi).symm)
  obtain ⟨b,hb,hvb⟩ := primitive_template_sign g _ v hv (hsv.trans (congrArg Subtype.val hj).symm)
  obtain ⟨c,hc,huc⟩ := primitive_template_sign g _ u hu (hsu.trans (congrArg Subtype.val hk).symm)
  apply relation_change_signs _ _ _ W v u a b c (signChoice s) (signChoice t)
    ha hb hc (signChoice_sq s) (signChoice_sq t) hWa hvb huc
  rw [hst,Matrix.mulVec_add,Matrix.mulVec_smul,Matrix.mulVec_smul]

/-- The line map agrees with either complementary column of an aligned reduced basis. -/
theorem retract_eq_complementaryLine (F : IntegralVector →ₗ[ℤ] ℤ)
    (W : IntegralVector) (L : RationalLine) (g : IntegralGL) (j : Fin 2)
    (hg0 : g.val.col 0 = W)
    (hgj : g.val.col j.succ = nonnegativeRepresentative F L) :
    retract F W L = augmentedLine (reducedBasis F g) j.succ.castSucc := by
  have he : reducedVector F W L = (reducedBasis F g).val.col j.succ := by
    trans remainderVector F (g.val.col 0) (normalized F (g.val.col j.succ))
    · change remainderVector F W (nonnegativeRepresentative F L) = _
      rw [hg0,hgj,normalized_eq_self F _ (nonnegativeRepresentative_nonneg F L)]
    · exact (reducedBasis_col_remainder F g j).symm
  have hp : Primitive (reducedVector F W L) := by rw [he]; exact column_primitive _ _
  have hn := AmbientIndependentTriple.rationalVector_ne_zero_of_primitive hp
  apply Subtype.ext
  simp only [retract,dite_eq_left hn]
  change Submodule.span ℚ {rationalVector (reducedVector F W L)} = _
  rw [he]
  exact (columnLine_span _ j.succ).symm

/-- A standard actual link edge remains a standard edge after simultaneous quotient reduction. -/
theorem retract_basis_triangle (F : IntegralVector →ₗ[ℤ] ℤ) (W : IntegralVector)
    (w L M : RationalLine) (hW : Primitive W)
    (hspan : Submodule.span ℚ {rationalVector W} = w.val) (g : IntegralGL)
    (hg0 : augmentedLine g 0 = w) (hg1 : augmentedLine g 1 = L)
    (hg2 : augmentedLine g 2 = M) :
    {w,retract F W L,retract F W M} ∈ ambient := by
  let v : Fin 3 → IntegralVector :=
    ![W,nonnegativeRepresentative F L,nonnegativeRepresentative F M]
  have hp : ∀ j, Primitive (v j) := by
    intro j
    fin_cases j
    · exact hW
    · exact nonnegativeRepresentative_primitive F L
    · exact nonnegativeRepresentative_primitive F M
  have hs : ∀ j, Submodule.span ℚ {rationalVector (v j)} =
      (augmentedLine g j.castSucc).val := by
    intro j
    fin_cases j
    · exact hspan.trans (congrArg Subtype.val hg0).symm
    · exact (nonnegativeRepresentative_span F L).trans (congrArg Subtype.val hg1).symm
    · exact (nonnegativeRepresentative_span F M).trans (congrArg Subtype.val hg2).symm
  obtain ⟨h,hh⟩ := exists_basis_columns g v hp hs
  have h0 : augmentedLine (reducedBasis F h) 0 = w := by
    apply Subtype.ext
    change (augmentedLine (reducedBasis F h) (0 : Fin 3).castSucc).val = _
    rw [columnLine_span,reducedBasis_col_zero,hh 0]
    exact hspan
  have h1 : retract F W L = augmentedLine (reducedBasis F h) 1 :=
    retract_eq_complementaryLine F W L h 0 (hh 0) (hh 1)
  have h2 : retract F W M = augmentedLine (reducedBasis F h) 2 :=
    retract_eq_complementaryLine F W M h 1 (hh 0) (hh 2)
  rw [← h0,h1,h2]
  exact reducedBasis_triangle_ambient F h

/-- Actual link edges reduce either to the original low edge or to one line in the additive case. -/
theorem retract_additive_edge (F : IntegralVector →ₗ[ℤ] ℤ) (W : IntegralVector)
    (w L M : RationalLine) (hW : Primitive W)
    (hspan : Submodule.span ℚ {rationalVector W} = w.val) (hN : 0 < F W)
    (hL : {L} ∈ link w) (hM : {M} ∈ link w) (hn : [w,L,M].Nodup)
    (g : IntegralGL) (hp : [w,L,M].Perm (AmbientDependentTriangles.coreList g)) :
    ((height F L : ℤ) < F W ∧ (height F M : ℤ) < F W) ∨
      retract F W L = retract F W M := by
  obtain ⟨s,t,hs,ht,he⟩ := primitive_core_relation g w L M hp hn W
    (nonnegativeRepresentative F L) (nonnegativeRepresentative F M) hW
    (nonnegativeRepresentative_primitive F L) (nonnegativeRepresentative_primitive F M)
    hspan (nonnegativeRepresentative_span F L) (nonnegativeRepresentative_span F M)
  rcases signed_remainder_cases F W _ _ hN
    (nonnegativeRepresentative_nonneg F L) (nonnegativeRepresentative_nonneg F M)
    s t hs ht he with hl | he
  · left
    simpa only [nonnegativeRepresentative_value] using hl
  · right
    exact retract_eq_of_remainder_span F W w L M hW hspan hL hM he

/-- Adjoining the fixed vertex to the image of every actual link edge gives an actual ambient face. -/
theorem retract_edge_ambient (F : IntegralVector →ₗ[ℤ] ℤ) (W : IntegralVector)
    (w L M : RationalLine) (hW : Primitive W)
    (hspan : Submodule.span ℚ {rationalVector W} = w.val) (hN : 0 < F W)
    (hf : {L,M} ∈ link w) : {w,retract F W L,retract F W M} ∈ ambient := by
  classical
  have hL : {L} ∈ link w :=
    ((link w).isRelLowerSet_faces hf).2 (by simp) (by simp)
  have hM : {M} ∈ link w :=
    ((link w).isRelLowerSet_faces hf).2 (by simp) (by simp)
  by_cases he : L = M
  · subst M
    simpa using ((singleton_mem_link w _).mp (retract_mem_link F W w L hW hspan hL)).1
  have hwL := ((singleton_mem_link w L).mp hL).2
  have hwM := ((singleton_mem_link w M).mp hM).2
  have hn : [w,L,M].Nodup := by simp [hwL.symm,hwM.symm,he]
  have ht : [w,L,M].toFinset ∈ ambient := by
    convert hf.1.2 using 1
    ext x
    simp
  rcases AmbientDependentTriangles.ambient_triangle_dichotomy [w,L,M] rfl hn ht with
    ⟨g,hg⟩ | ⟨g,hg⟩
  · rcases retract_additive_edge F W w L M hW hspan hN hL hM hn g hg with hl | he
    · rw [retract_eq_self F W L hl.1,retract_eq_self F W M hl.2]
      simpa using ht
    · rw [he]
      simpa using ((singleton_mem_link w _).mp (retract_mem_link F W w M hW hspan hM)).1
  · have hg' : w = augmentedLine g 0 ∧ L = augmentedLine g 1 ∧ M = augmentedLine g 2 := by
      simpa only [List.cons.injEq,and_true] using hg
    exact retract_basis_triangle F W w L M hW hspan g hg'.1.symm hg'.2.1.symm hg'.2.2.symm

/-- Any nonnegative primitive generator yields the same remainder line.
At height zero the quotient vanishes for both possible signs. -/
theorem remainder_span_independent (F : IntegralVector →ₗ[ℤ] ℤ) (W : IntegralVector)
    (L : RationalLine) (v : IntegralVector) (hp : Primitive v)
    (hs : Submodule.span ℚ {rationalVector v} = L.val) (hv : 0 ≤ F v) :
    Submodule.span ℚ {rationalVector (reducedVector F W L)} =
      Submodule.span ℚ {rationalVector (remainderVector F W v)} := by
  by_cases hpos : 0 < height F L
  · rw [reducedVector,nonnegativeRepresentative_eq F L hp hs hv hpos]
  · have hz : height F L = 0 := by omega
    have hv0 := (height_eq_zero_iff F L hp hs).mp hz
    have hr0 : F (nonnegativeRepresentative F L) = 0 := by
      rw [nonnegativeRepresentative_value,hz,Int.natCast_zero]
    simp only [reducedVector,remainderVector,hv0,hr0,Int.zero_ediv,zero_smul,sub_zero]
    exact (nonnegativeRepresentative_span F L).trans hs.symm

/-- Low link membership is precisely link membership with the vertex height bounds. -/
theorem mem_lowLink_iff (F : IntegralVector →ₗ[ℤ] ℤ) (W : IntegralVector)
    (w : RationalLine) (s : Finset RationalLine) :
    s ∈ lowLink F W w ↔ s ∈ link w ∧ ∀ L ∈ s, (height F L : ℤ) < F W := by
  constructor
  · intro h
    exact ⟨⟨h.1,fun L hL => (h.2 L hL).1⟩,fun L hL => (h.2 L hL).2⟩
  · rintro ⟨h,hh⟩
    exact ⟨h.1,fun L hL => ⟨h.2 L hL,hh L hL⟩⟩

theorem lowLink_le_link (F : IntegralVector →ₗ[ℤ] ℤ) (W : IntegralVector) (w : RationalLine) :
    lowLink F W w ≤ link w := fun s hs => ((mem_lowLink_iff F W w s).mp hs).1

/-- Every actual link vertex maps into the low actual link. -/
theorem retract_vertex_mem_lowLink (F : IntegralVector →ₗ[ℤ] ℤ) (W : IntegralVector)
    (w L : RationalLine) (hW : Primitive W)
    (hspan : Submodule.span ℚ {rationalVector W} = w.val) (hN : 0 < F W)
    (hL : {L} ∈ link w) : {retract F W L} ∈ lowLink F W w := by
  rw [mem_lowLink_iff]
  refine ⟨retract_mem_link F W w L hW hspan hL,?_⟩
  intro K hK
  have he : K = retract F W L := Finset.mem_singleton.mp hK
  subst K
  exact retract_height_lt F W w L hW hspan hN hL

/-- Every actual link edge maps to a low actual link face, possibly a singleton. -/
theorem retract_edge_mem_lowLink (F : IntegralVector →ₗ[ℤ] ℤ) (W : IntegralVector)
    (w L M : RationalLine) (hW : Primitive W)
    (hspan : Submodule.span ℚ {rationalVector W} = w.val) (hN : 0 < F W)
    (hf : {L,M} ∈ link w) : {retract F W L,retract F W M} ∈ lowLink F W w := by
  classical
  have hL : {L} ∈ link w := ((link w).isRelLowerSet_faces hf).2 (by simp) (by simp)
  have hM : {M} ∈ link w := ((link w).isRelLowerSet_faces hf).2 (by simp) (by simp)
  refine ⟨⟨by simp,?_⟩,?_⟩
  · convert retract_edge_ambient F W w L M hW hspan hN hf using 1
    ext x
    simp
  · intro K hK
    simp only [Finset.mem_insert,Finset.mem_singleton] at hK
    rcases hK with rfl | rfl
    · exact ⟨((singleton_mem_link w _).mp (retract_mem_link F W w L hW hspan hL)).2,
        retract_height_lt F W w L hW hspan hN hL⟩
    · exact ⟨((singleton_mem_link w _).mp (retract_mem_link F W w M hW hspan hM)).2,
        retract_height_lt F W w M hW hspan hN hM⟩

open OrientedListChains

/-- Allowed vertex and edge lists map to allowed low-link lists; no triangle assertion is involved. -/
theorem allowed_retract_le_two (F : IntegralVector →ₗ[ℤ] ℤ) (W : IntegralVector)
    (w : RationalLine) (hW : Primitive W)
    (hspan : Submodule.span ℚ {rationalVector W} = w.val) (hN : 0 < F W)
    (l : List RationalLine) (hlen : l.length ≤ 2) (hl : Allowed (link w) l) :
    Allowed (lowLink F W w) (l.map (retract F W)) := by
  classical
  cases l with
  | nil => exact Or.inl rfl
  | cons L l =>
    cases l with
    | nil =>
      have hf : {L} ∈ link w := by simpa [Allowed] using hl
      exact Or.inr (by simpa using retract_vertex_mem_lowLink F W w L hW hspan hN hf)
    | cons M l =>
      have he : l = [] := by
        have hz : l.length = 0 := by simp only [List.length_cons] at hlen; omega
        exact List.length_eq_zero_iff.mp hz
      subst l
      have hf : {L,M} ∈ link w := by
        rcases hl with he | hl
        · simp at he
        · convert hl using 1
          ext x
          simp
      apply Or.inr
      convert retract_edge_mem_lowLink F W w L M hW hspan hN hf using 1
      ext x
      simp

/-- Actual quotient/remainder transport of finite supported chains in vertex indices zero, one and two. -/
theorem retract_mem_chains (F : IntegralVector →ₗ[ℤ] ℤ) (W : IntegralVector)
    (w : RationalLine) (hW : Primitive W)
    (hspan : Submodule.span ℚ {rationalVector W} = w.val) (hN : 0 < F W)
    (n : ℕ) (hn : n ≤ 2) {c : Chain RationalLine} (hc : c ∈ chains (link w) n) :
    OrientedChainMap.map (retract F W) c ∈ chains (lowLink F W w) n := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨l,hlen,hl,rfl⟩ := hc
    rw [OrientedChainMap.map_simplex]
    simpa only [List.length_map,hlen] using
      simplex_mem_chains (lowLink F W w) (l.map (retract F W))
        (allowed_retract_le_two F W w hW hspan hN l (hlen ▸ hn) hl)
  | zero => simpa only [map_zero] using (chains (lowLink F W w) n).zero_mem
  | add c d hc hd ihc ihd =>
    simpa only [map_add] using (chains (lowLink F W w) n).add_mem ihc ihd
  | smul q c hc ih =>
    simpa only [map_smul] using (chains (lowLink F W w) n).smul_mem q ih

/-- The low-link retraction is a genuine linear chain map in the stated supported degrees. -/
def chainRetraction (F : IntegralVector →ₗ[ℤ] ℤ) (W : IntegralVector)
    (w : RationalLine) (hW : Primitive W)
    (hspan : Submodule.span ℚ {rationalVector W} = w.val) (hN : 0 < F W)
    (n : ℕ) (hn : n ≤ 2) : chains (link w) n →ₗ[ℚ] chains (lowLink F W w) n :=
  ((OrientedChainMap.map (retract F W)).comp (chains (link w) n).subtype).codRestrict _
    (fun c => retract_mem_chains F W w hW hspan hN n hn c.property)

/-- Exact boundary compatibility of the restricted edge-to-vertex transport. -/
theorem chainRetraction_differential (F : IntegralVector →ₗ[ℤ] ℤ) (W : IntegralVector)
    (w : RationalLine) (hW : Primitive W)
    (hspan : Submodule.span ℚ {rationalVector W} = w.val) (hN : 0 < F W)
    (n : ℕ) (hn : n + 1 ≤ 2) (c : chains (link w) (n+1)) :
    differential (lowLink F W w) n (chainRetraction F W w hW hspan hN (n+1) hn c) =
      chainRetraction F W w hW hspan hN n (by omega) (differential (link w) n c) := by
  apply Subtype.ext
  exact OrientedChainMap.boundary_map (retract F W) c.val

/-- Every chain supported entirely on low vertices is fixed by the actual relabeling map. -/
theorem retract_eq_self_on_low_chains (F : IntegralVector →ₗ[ℤ] ℤ) (W : IntegralVector)
    (w : RationalLine) (n : ℕ) {c : Chain RationalLine}
    (hc : c ∈ chains (lowLink F W w) n) : OrientedChainMap.map (retract F W) c = c := by
  let : DecidableEq RationalLine := Classical.decEq RationalLine
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨l,_,hl,rfl⟩ := hc
    rw [OrientedChainMap.map_simplex]
    have he : l.map (retract F W) = l := by
      trans l.map id
      · apply List.map_congr_left
        intro L hL
        rcases hl with rfl | hl
        · simp at hL
        · exact retract_eq_self F W L (hl.2 L (List.mem_toFinset.mpr hL)).2
      · exact List.map_id l
    rw [he]
  | zero => exact map_zero _
  | add c d hc hd ihc ihd => simp only [map_add,ihc,ihd]
  | smul q c hc ih => simp only [map_smul,ih]

end TernaryPoly.AmbientEdgeRetraction
