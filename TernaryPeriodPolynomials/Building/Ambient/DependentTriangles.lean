module

public import TernaryPeriodPolynomials.Building.Ambient.IndependentTriple
public import TernaryPeriodPolynomials.Building.IntegralFrameHeightReduction
public import Mathlib.Data.List.OfFn

@[expose] public section


noncomputable section
namespace TernaryPoly.AmbientDependentTriangles

open ModThreeGoodAction AugmentedFrameComplex AugmentedBadFaces
open GoodIntegralNormalization GoodAugmentedNormalForm AmbientIndependentTriple
open PrimitiveLineHeight IntegralFrameHeightReduction

/-- The three literal indices of the augmented frame's additive core. -/
def coreIndex : Fin 3 → Fin 4 := ![0,1,3]

def coreList (g : IntegralGL) : List RationalLine :=
  [augmentedLine g 0,augmentedLine g 1,augmentedLine g 3]

/-- A distinct ordered template triple containing the complementary index is unimodular. -/
theorem templateTriple_unit : ∀ idx : Fin 3 → Fin 4,
    Function.Injective idx → (∃ j,idx j = 2) → (templateMatrix idx).det.natAbs = 1 := by
  decide +kernel

/-- Distinct triples avoiding the complementary index are exactly the ordered additive core. -/
theorem templateTriple_core : ∀ i j k : Fin 4,
    ([i,j,k] : List (Fin 4)).Nodup → i ≠ 2 → j ≠ 2 → k ≠ 2 →
      ([i,j,k] : List (Fin 4)).Perm [0,1,3] := by decide +kernel

/-- An actual independent three-subface is exactly the first three lines of an integral basis. -/
theorem ordered_template_basis (g : IntegralGL) (idx : Fin 3 → Fin 4)
    (hinj : Function.Injective idx) (h2 : ∃ j,idx j = 2) :
    ∃ h : IntegralGL, ∀ j : Fin 3, augmentedLine h j.castSucc = augmentedLine g (idx j) := by
  let a : IntegralGL := Matrix.nonsingInvUnit (templateMatrix idx)
    (Int.isUnit_iff_natAbs_eq.mpr (templateTriple_unit idx hinj h2))
  refine ⟨g*a,fun j => ?_⟩
  apply Subtype.ext
  rw [augmentedLine_castSucc_val,map_mul,LinearEquiv.mul_apply,rationalRepresentation_basis]
  change Submodule.span ℚ {(rationalRepresentation g
    (rationalVector ((templateMatrix idx).col j)))} = _
  change Submodule.span ℚ {rationalRepresentation g (rationalVector (integralTemplate (idx j)))} = _
  rw [rationalVector_integralTemplate]
  rfl

/-- Ordered nondegenerate ambient triangles are either additive cores or actual basis triples. -/
theorem ambient_triangle_dichotomy (l : List RationalLine) (hlen : l.length = 3)
    (hn : l.Nodup) (hf : l.toFinset ∈ ambient) :
    (∃ g : IntegralGL, l.Perm (coreList g)) ∨
      ∃ g : IntegralGL, l = [augmentedLine g 0,augmentedLine g 1,augmentedLine g 2] := by
  classical
  obtain ⟨L,M,N,rfl⟩ := List.length_eq_three.mp hlen
  obtain ⟨_,g,hg⟩ := hf
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp (hg (by simp : L ∈ [L,M,N].toFinset))
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp (hg (by simp : M ∈ [augmentedLine g i,M,N].toFinset))
  obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp
    (hg (by simp : N ∈ [augmentedLine g i,augmentedLine g j,N].toFinset))
  have hidx : ([i,j,k] : List (Fin 4)).Nodup := by
    apply List.Nodup.of_map (f := augmentedLine g)
    simpa only [List.map_cons,List.map_nil] using hn
  by_cases h2 : ∃ t : Fin 3, (![i,j,k] : Fin 3 → Fin 4) t = 2
  · right
    have hi : Function.Injective (![i,j,k] : Fin 3 → Fin 4) := by
      have hn' := hidx
      simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,
        not_false_eq_true,and_true,not_or] at hn'
      intro a b he
      fin_cases a <;> fin_cases b <;> simp_all
    obtain ⟨h,hh⟩ := ordered_template_basis g ![i,j,k] hi h2
    refine ⟨h,?_⟩
    simpa using congrArg (fun v : Fin 3 → RationalLine => [v 0,v 1,v 2]) (funext hh).symm
  · left
    have hcore := templateTriple_core i j k hidx
      (fun hi => h2 ⟨0,hi⟩) (fun hj => h2 ⟨1,hj⟩) (fun hk => h2 ⟨2,hk⟩)
    refine ⟨g,?_⟩
    simpa only [List.map_cons,List.map_nil,coreList] using hcore.map (augmentedLine g)

/-- Every actual basis triple has full rational span, expressed as the useful lower bound. -/
theorem basis_face_finrank_ge (g : IntegralGL) :
    3 ≤ Module.finrank ℚ (faceSpan
      [augmentedLine g 0,augmentedLine g 1,augmentedLine g 2].toFinset) := by
  classical
  let L : Fin 3 → RationalLine := fun j => augmentedLine g j.castSucc
  have hL (j : Fin 3) : Submodule.span ℚ {rationalVector (g.val.col j)} = (L j).val :=
    (columnLine_span g j).symm
  have hi : LinearIndependent ℚ (g.val.map (Int.castRingHom ℚ)).col := by
    apply Matrix.linearIndependent_cols_iff_isUnit.mpr
    exact (Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) g).isUnit
  have hd := linearIndependent_iff_card_le_finrank_span.mp hi
  change 3 ≤ Module.finrank ℚ (Submodule.span ℚ (Set.range (g.val.map (Int.castRingHom ℚ)).col)) at hd
  rw [column_span_eq_faceSpan g.val L hL] at hd
  have he : Finset.univ.image L =
      [augmentedLine g 0,augmentedLine g 1,augmentedLine g 2].toFinset := by
    ext x
    simp [L,Fin.exists_fin_succ,eq_comm]
  rwa [he] at hd

/-- A nondegenerate dependent ambient triangle is precisely an actual additive core. -/
theorem dependent_triangle_core (l : List RationalLine) (hlen : l.length = 3)
    (hn : l.Nodup) (hf : l.toFinset ∈ ambient)
    (hd : Module.finrank ℚ (faceSpan l.toFinset) ≤ 2) :
    ∃ g : IntegralGL, l.Perm [augmentedLine g 0,augmentedLine g 1,augmentedLine g 3] := by
  rcases ambient_triangle_dichotomy l hlen hn hf with h | ⟨g,rfl⟩
  · exact h
  · have hg := basis_face_finrank_ge g
    omega

/-- A literal shear of only the complementary column, fixing both core generators. -/
def lastShearMatrix (s a b : ℤ) : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1,0,-a;0,1,-b;0,0,s]

def lastShear (s a b : ℤ) (hs : s*s=1) : IntegralGL :=
  Matrix.nonsingInvUnit (lastShearMatrix s a b) (by
    have hd : (lastShearMatrix s a b).det = s := by simp [lastShearMatrix,Matrix.det_fin_three]
    rw [hd]
    exact IsUnit.of_mul_eq_one s hs)

theorem lastShear_col_zero (g : IntegralGL) (s a b : ℤ) (hs : s*s=1) :
    (g * lastShear s a b hs).val.col 0 = g.val.col 0 := by
  funext i
  change (g.val * lastShearMatrix s a b) i 0 = _
  simp [Matrix.mul_apply,Fin.sum_univ_three,lastShearMatrix]

theorem lastShear_col_one (g : IntegralGL) (s a b : ℤ) (hs : s*s=1) :
    (g * lastShear s a b hs).val.col 1 = g.val.col 1 := by
  funext i
  change (g.val * lastShearMatrix s a b) i 1 = _
  simp [Matrix.mul_apply,Fin.sum_univ_three,lastShearMatrix]

theorem lastShear_col_two (g : IntegralGL) (s a b : ℤ) (hs : s*s=1) :
    (g * lastShear s a b hs).val.col 2 =
      s • g.val.col 2 - a • g.val.col 0 - b • g.val.col 1 := by
  funext i
  change (g.val * lastShearMatrix s a b) i 2 = _
  simp [Matrix.mul_apply,Fin.sum_univ_three,lastShearMatrix]
  ring

/-- Each actual core generator is an exact sum of the first two integer columns. -/
theorem core_vector_columns (g : IntegralGL) (i : Fin 3) :
    g.val.mulVec (integralTemplate (coreIndex i)) =
      (![g.val.col 0,g.val.col 1,g.val.col 0 + g.val.col 1] : Fin 3 → IntegralVector) i := by
  fin_cases i <;> funext r <;>
    simp [coreIndex,integralTemplate,Matrix.mulVec,dotProduct,Fin.sum_univ_three]

/-- Fixing the first two columns fixes every actual core line, including their sum. -/
theorem core_lines_eq_of_columns (g h : IntegralGL)
    (h0 : h.val.col 0 = g.val.col 0) (h1 : h.val.col 1 = g.val.col 1) (i : Fin 3) :
    augmentedLine h (coreIndex i) = augmentedLine g (coreIndex i) := by
  apply Subtype.ext
  change Submodule.span ℚ {rationalRepresentation h (template (coreIndex i))} =
    Submodule.span ℚ {rationalRepresentation g (template (coreIndex i))}
  rw [← rationalVector_integralTemplate,← rationalVector_mulVec,← rationalVector_mulVec,
    core_vector_columns,core_vector_columns,h0,h1]

/-- A primitive generator of any core vertex has zero complementary inverse coordinate. -/
theorem core_inverse_last_zero (g : IntegralGL) (i : Fin 3) (w : IntegralVector)
    (hw : Primitive w) (hs : Submodule.span ℚ {rationalVector w} =
      (augmentedLine g (coreIndex i)).val) :
    g⁻¹.val.mulVec w 2 = 0 := by
  obtain ⟨u,hu⟩ := primitive_eq_unit_template g (coreIndex i) hw hs
  rw [hu,Matrix.mulVec_smul,Matrix.mulVec_mulVec,← Units.val_mul,inv_mul_cancel,
    Units.val_one,Matrix.one_mulVec]
  fin_cases i <;> simp [coreIndex,integralTemplate]

/-- The original vector is exactly its two core-coordinate column combination. -/
theorem vector_core_coordinates (g : IntegralGL) (w : IntegralVector)
    (hz : g⁻¹.val.mulVec w 2 = 0) :
    w = (g⁻¹.val.mulVec w 0) • g.val.col 0 + (g⁻¹.val.mulVec w 1) • g.val.col 1 := by
  have he : g.val.mulVec (g⁻¹.val.mulVec w) = w := by
    rw [Matrix.mulVec_mulVec,← Units.val_mul,mul_inv_cancel,Units.val_one,Matrix.one_mulVec]
  calc
    w = g.val.mulVec (g⁻¹.val.mulVec w) := he.symm
    _ = _ := by
      funext i
      change (∑ j : Fin 3, g.val i j * g⁻¹.val.mulVec w j) =
        g⁻¹.val.mulVec w 0 * g.val i 0 + g⁻¹.val.mulVec w 1 * g.val i 1
      rw [Fin.sum_univ_three,hz,mul_zero,add_zero]
      ring

/-- Actual complement reduction by an arbitrary integral core-plane vector. -/
def reducedComplement (F : IntegralVector →ₗ[ℤ] ℤ) (g : IntegralGL) (w : IntegralVector) : IntegralGL :=
  let q := F (normalized F (g.val.col 2)) / F w
  g * lastShear (positiveSign (F (g.val.col 2)))
    (q * g⁻¹.val.mulVec w 0) (q * g⁻¹.val.mulVec w 1) (positiveSign_mul_self _)

theorem reducedComplement_col_zero (F : IntegralVector →ₗ[ℤ] ℤ) (g : IntegralGL)
    (w : IntegralVector) : (reducedComplement F g w).val.col 0 = g.val.col 0 :=
  lastShear_col_zero _ _ _ _ _

theorem reducedComplement_col_one (F : IntegralVector →ₗ[ℤ] ℤ) (g : IntegralGL)
    (w : IntegralVector) : (reducedComplement F g w).val.col 1 = g.val.col 1 :=
  lastShear_col_one _ _ _ _ _

/-- The new primitive complementary vector is literally the Euclidean remainder vector. -/
theorem reducedComplement_col_two (F : IntegralVector →ₗ[ℤ] ℤ) (g : IntegralGL)
    (w : IntegralVector) (hz : g⁻¹.val.mulVec w 2 = 0) :
    (reducedComplement F g w).val.col 2 =
      remainderVector F w (normalized F (g.val.col 2)) := by
  let q := F (normalized F (g.val.col 2)) / F w
  rw [reducedComplement,lastShear_col_two]
  unfold remainderVector
  have hqw : q • w = (q * g⁻¹.val.mulVec w 0) • g.val.col 0 +
      (q * g⁻¹.val.mulVec w 1) • g.val.col 1 := by
    conv_lhs => rw [vector_core_coordinates g w hz]
    rw [smul_add,smul_smul,smul_smul]
  change positiveSign (F (g.val.col 2)) • g.val.col 2 -
      (q * g⁻¹.val.mulVec w 0) • g.val.col 0 -
      (q * g⁻¹.val.mulVec w 1) • g.val.col 1 =
    positiveSign (F (g.val.col 2)) • g.val.col 2 - q • w
  rw [hqw]
  abel

/-- The additive core is fixed pointwise throughout complement reduction. -/
theorem reducedComplement_core (F : IntegralVector →ₗ[ℤ] ℤ) (g : IntegralGL)
    (w : IntegralVector) (i : Fin 3) :
    augmentedLine (reducedComplement F g w) (coreIndex i) = augmentedLine g (coreIndex i) :=
  core_lines_eq_of_columns g _ (reducedComplement_col_zero F g w)
    (reducedComplement_col_one F g w) i

/-- The complementary primitive line is strictly lower than the positive reduction vector. -/
theorem reducedComplement_height_lt (F : IntegralVector →ₗ[ℤ] ℤ) (g : IntegralGL)
    (w : IntegralVector) (hz : g⁻¹.val.mulVec w 2 = 0) (hw : 0 < F w) :
    (height F (augmentedLine (reducedComplement F g w) 2) : ℤ) < F w := by
  change (height F (augmentedLine (reducedComplement F g w) (2 : Fin 3).castSucc) : ℤ) < F w
  rw [columnLine_height,reducedComplement_col_two F g w hz,remainderVector_value,
    normalized_value,Int.natCast_natAbs]
  obtain ⟨h0,hlt⟩ := AugmentedHeightArithmetic.remainder_bounds (F w) |F (g.val.col 2)| hw
  rwa [abs_of_nonneg h0]

/-- The fixed original core plus the reduced complement remains an actual augmented tetrahedron. -/
theorem reducedComplement_tetrahedron (F : IntegralVector →ₗ[ℤ] ℤ) (g : IntegralGL)
    (w : IntegralVector) :
    {augmentedLine g 0,augmentedLine g 1,augmentedLine g 3,
      augmentedLine (reducedComplement F g w) 2} ∈ ambient := by
  classical
  apply subset_augmentedFrame_mem (reducedComplement F g w) (by simp)
  intro L hL
  simp only [Finset.mem_insert,Finset.mem_singleton] at hL
  rcases hL with rfl | rfl | rfl | rfl
  · exact Finset.mem_image.mpr ⟨0,Finset.mem_univ _,reducedComplement_core F g w 0⟩
  · exact Finset.mem_image.mpr ⟨1,Finset.mem_univ _,reducedComplement_core F g w 1⟩
  · exact Finset.mem_image.mpr ⟨3,Finset.mem_univ _,reducedComplement_core F g w 2⟩
  · exact Finset.mem_image.mpr ⟨2,Finset.mem_univ _,rfl⟩

/-- Any positive-height core vertex gives a strictly lower actual complementary vertex.
In particular this applies to a vertex of positive maximal core height. -/
theorem exists_low_complement (F : IntegralVector →ₗ[ℤ] ℤ) (g : IntegralGL) (i : Fin 3)
    (hN : 0 < height F (augmentedLine g (coreIndex i))) :
    ∃ h : IntegralGL,
      (∀ j : Fin 3, augmentedLine h (coreIndex j) = augmentedLine g (coreIndex j)) ∧
      height F (augmentedLine h 2) < height F (augmentedLine g (coreIndex i)) ∧
      {augmentedLine g 0,augmentedLine g 1,augmentedLine g 3,augmentedLine h 2} ∈ ambient := by
  let L := augmentedLine g (coreIndex i)
  let w := nonnegativeRepresentative F L
  have hz : g⁻¹.val.mulVec w 2 = 0 := core_inverse_last_zero g i w
    (nonnegativeRepresentative_primitive F L) (nonnegativeRepresentative_span F L)
  have hw : 0 < F w := by
    rw [show F w = (height F L : ℤ) from nonnegativeRepresentative_value F L]
    exact_mod_cast hN
  refine ⟨reducedComplement F g w,reducedComplement_core F g w,?_,
    reducedComplement_tetrahedron F g w⟩
  have ht := reducedComplement_height_lt F g w hz hw
  rw [show F w = (height F L : ℤ) from nonnegativeRepresentative_value F L] at ht
  exact_mod_cast ht

/-- Each of the three other tetrahedron faces is an exact ordered integral basis triple. -/
theorem core_pair_complement_basis (g : IntegralGL) (i j : Fin 3) (hij : i ≠ j) :
    ∃ h : IntegralGL, augmentedLine h 0 = augmentedLine g (coreIndex i) ∧
      augmentedLine h 1 = augmentedLine g (coreIndex j) ∧
      augmentedLine h 2 = augmentedLine g 2 := by
  have hinj : Function.Injective (![coreIndex i,coreIndex j,2] : Fin 3 → Fin 4) :=
    (by decide +kernel : ∀ i j : Fin 3, i ≠ j →
      Function.Injective (![coreIndex i,coreIndex j,2] : Fin 3 → Fin 4)) i j hij
  obtain ⟨h,hh⟩ := ordered_template_basis g ![coreIndex i,coreIndex j,2] hinj ⟨2,rfl⟩
  exact ⟨h,hh 0,hh 1,hh 2⟩

end TernaryPoly.AmbientDependentTriangles
