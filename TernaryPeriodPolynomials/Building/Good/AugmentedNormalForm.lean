module

public import TernaryPeriodPolynomials.Building.AugmentedFrame.BadFaces
public import TernaryPeriodPolynomials.Building.Primitive.LineUniqueness

@[expose] public section


open scoped BigOperators
noncomputable section
namespace TernaryPoly.GoodAugmentedNormalForm
open ModThreeGoodAction GoodIntegralNormalization PrimitiveLineUniqueness
open AugmentedFrameComplex AugmentedBadFaces

/-- An integral linear functional taking a vector to one proves its primitivity. -/
theorem primitive_of_bezout {v b : IntegralVector}
    (hb : ∑ i, b i * v i = 1) : Primitive v := by
  have hd : (content v : ℤ) ∣ 1 := by
    rw [← hb]
    exact Finset.dvd_sum (fun i _ => dvd_mul_of_dvd_right (content_dvd v i) _)
  exact Nat.dvd_one.mp (Int.ofNat_dvd.mp hd)

/-- Actual invertible integer matrices preserve primitive vectors. -/
theorem primitive_mulVec (g : IntegralGL) {v : IntegralVector} (hv : Primitive v) :
    Primitive (g.val.mulVec v) := by
  obtain ⟨b,hb⟩ := primitive_bezout hv
  apply primitive_of_bezout (b := Matrix.vecMul b g⁻¹.val)
  change dotProduct (Matrix.vecMul b g⁻¹.val) (g.val.mulVec v) = 1
  rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  exact hb

/-- For a primitive generator, goodness of its rational line is exactly its nonzero residue. -/
theorem good_span_iff_residue {v : IntegralVector} (hv : Primitive v) :
    Good (Submodule.span ℚ {rationalVector v}) ↔ ∑ i, (v i : ZMod 3) ≠ 0 := by
  constructor
  · rintro ⟨w,hw,hr⟩ hz
    obtain ⟨n,rfl⟩ := integer_multiple_of_mem_span hv hw
    apply hr
    simp only [Int.cast_mul, ← Finset.mul_sum, hz, mul_zero]
  · intro hr
    exact ⟨v,Submodule.mem_span_singleton_self _,hr⟩

/-- The integral augmented template underlies the rational one. -/
def integralTemplate : Fin 4 → IntegralVector :=
  ![Pi.single 0 1,Pi.single 1 1,Pi.single 2 1,Pi.single 0 1 + Pi.single 1 1]

theorem integralTemplate_primitive (i : Fin 4) : Primitive (integralTemplate i) := by
  fin_cases i <;> unfold Primitive content integralTemplate <;> decide

theorem rationalVector_integralTemplate (i : Fin 4) :
    rationalVector (integralTemplate i) = template i := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [rationalVector,integralTemplate,template]

theorem templateResidue_eq_sum (g : IntegralGL) (i : Fin 4) :
    templateResidue g i = ∑ j, (g.val.mulVec (integralTemplate i) j : ZMod 3) := by
  fin_cases i <;>
    simp [templateResidue,integralTemplate,Matrix.mulVec_add,columnResidue,
      Finset.sum_add_distrib]

/-- Every actual augmented line has the exact primitive-vector residue criterion. -/
theorem good_augmentedLine_iff_residue (g : IntegralGL) (i : Fin 4) :
    Good (augmentedLine g i).val ↔ templateResidue g i ≠ 0 := by
  rw [templateResidue_eq_sum]
  have h := good_span_iff_residue (primitive_mulVec g (integralTemplate_primitive i))
  rw [rationalVector_mulVec,rationalVector_integralTemplate] at h
  exact h

/-- Choose the integer sign making a nonzero residue equal to one. -/
def normalizingSign (r : ZMod 3) : ℤ := if r = 1 then 1 else -1

theorem normalizingSign_mul_self (r : ZMod 3) : normalizingSign r * normalizingSign r = 1 := by
  unfold normalizingSign
  split <;> norm_num

theorem normalizingSign_ne_zero (r : ZMod 3) : normalizingSign r ≠ 0 := by
  unfold normalizingSign
  split <;> norm_num

theorem normalizingSign_mul_residue (r : ZMod 3) (hr : r ≠ 0) :
    (normalizingSign r : ZMod 3) * r = 1 := by
  exact (by decide : ∀ r : ZMod 3, r ≠ 0 →
    ((if r = 1 then 1 else -1 : ℤ) : ZMod 3) * r = 1) r hr

theorem nonzero_sum_forces_equal :
    ∀ a b : ZMod 3, a ≠ 0 → b ≠ 0 → a+b ≠ 0 → a = b := by decide

/-- The diagonal normalization is a genuine integer matrix unit, with itself as inverse. -/
def signDiagonal (g : IntegralGL) : IntegralGL where
  val := Matrix.diagonal (fun j => normalizingSign (columnResidue g j))
  inv := Matrix.diagonal (fun j => normalizingSign (columnResidue g j))
  val_inv := by simp [Matrix.diagonal_mul_diagonal,normalizingSign_mul_self]
  inv_val := by simp [Matrix.diagonal_mul_diagonal,normalizingSign_mul_self]

/-- Normalize each actual basis column by its residue sign. -/
def normalize (g : IntegralGL) : IntegralGL := g * signDiagonal g

theorem normalize_entry (g : IntegralGL) (i j : Fin 3) :
    (normalize g).val i j = g.val i j * normalizingSign (columnResidue g j) := by
  exact Matrix.mul_diagonal _ _ _ _

theorem normalize_mem_K (g : IntegralGL) (hg : ∀ j, columnResidue g j ≠ 0) :
    normalize g ∈ K := by
  rw [mem_K]
  funext j
  change (∑ i, (1 : ZMod 3) * ((normalize g).val i j : ZMod 3)) = 1
  simp only [one_mul,normalize_entry,Int.cast_mul,← Finset.sum_mul]
  exact (mul_comm _ _).trans (normalizingSign_mul_residue _ (hg j))

/-- Column normalization scales each rational basis vector by its integer sign. -/
theorem normalize_basis (g : IntegralGL) (j : Fin 3) :
    rationalRepresentation (normalize g) (Pi.single j 1) =
      (normalizingSign (columnResidue g j) : ℚ) •
        rationalRepresentation g (Pi.single j 1) := by
  rw [rationalRepresentation_basis,rationalRepresentation_basis]
  ext i
  simp only [rationalVector,normalize_entry,Int.cast_mul,Pi.smul_apply,smul_eq_mul]
  exact mul_comm _ _

/-- The signs of the four template vectors; the sum vector uses the first sign. -/
def templateSign (g : IntegralGL) : Fin 4 → ℤ :=
  ![normalizingSign (columnResidue g 0),normalizingSign (columnResidue g 1),
    normalizingSign (columnResidue g 2),normalizingSign (columnResidue g 0)]

theorem templateSign_ne_zero (g : IntegralGL) (i : Fin 4) : templateSign g i ≠ 0 := by
  fin_cases i <;> exact normalizingSign_ne_zero _

/-- Matching signs on the first two columns preserve the augmented sum line as well. -/
theorem normalize_template (g : IntegralGL)
    (hs : normalizingSign (columnResidue g 0) = normalizingSign (columnResidue g 1))
    (i : Fin 4) : rationalRepresentation (normalize g) (template i) =
      (templateSign g i : ℚ) • rationalRepresentation g (template i) := by
  fin_cases i
  · exact normalize_basis g 0
  · exact normalize_basis g 1
  · exact normalize_basis g 2
  · change rationalRepresentation (normalize g) (Pi.single 0 1 + Pi.single 1 1) =
      (normalizingSign (columnResidue g 0) : ℚ) •
        rationalRepresentation g (Pi.single 0 1 + Pi.single 1 1)
    rw [map_add,map_add,normalize_basis,normalize_basis,← hs,smul_add]

theorem normalize_augmentedLine (g : IntegralGL)
    (hs : normalizingSign (columnResidue g 0) = normalizingSign (columnResidue g 1))
    (i : Fin 4) : augmentedLine (normalize g) i = augmentedLine g i := by
  apply Subtype.ext
  change Submodule.span ℚ {rationalRepresentation (normalize g) (template i)} =
    Submodule.span ℚ {rationalRepresentation g (template i)}
  rw [normalize_template g hs]
  apply Submodule.span_singleton_smul_eq
  apply isUnit_iff_ne_zero.mpr
  exact_mod_cast templateSign_ne_zero g i

/-- Every all-good actual augmented frame admits a pointwise-identical representative in K. -/
theorem exists_K_augmentedLines (g : IntegralGL)
    (hg : ∀ i : Fin 4, Good (augmentedLine g i).val) :
    ∃ k : K, ∀ i : Fin 4, augmentedLine g i = augmentedLine k.val i := by
  have hr (i : Fin 4) : templateResidue g i ≠ 0 :=
    (good_augmentedLine_iff_residue g i).mp (hg i)
  have hc (j : Fin 3) : columnResidue g j ≠ 0 := by
    fin_cases j
    · exact hr 0
    · exact hr 1
    · exact hr 2
  have he : columnResidue g 0 = columnResidue g 1 :=
    nonzero_sum_forces_equal _ _ (hc 0) (hc 1) (hr 3)
  refine ⟨⟨normalize g,normalize_mem_K g hc⟩,fun i => ?_⟩
  exact (normalize_augmentedLine g (congrArg normalizingSign he) i).symm

/-- The full all-good tetrahedron orbit is represented by the genuine congruence subgroup. -/
theorem exists_K_augmentedFrame (g : IntegralGL)
    (hg : ∀ L ∈ augmentedFrame g, Good L.val) :
    ∃ k : K, augmentedFrame g = augmentedFrame k.val := by
  obtain ⟨k,hk⟩ := exists_K_augmentedLines g (fun i =>
    hg _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩))
  refine ⟨k,?_⟩
  unfold augmentedFrame
  rw [show augmentedLine g = augmentedLine k.val from funext hk]

end TernaryPoly.GoodAugmentedNormalForm
