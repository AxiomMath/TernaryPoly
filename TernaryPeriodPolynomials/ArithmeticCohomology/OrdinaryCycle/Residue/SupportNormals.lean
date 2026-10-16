module

public import TernaryPeriodPolynomials.Building.Primitive.LineHeight
public import TernaryPeriodPolynomials.Building.Good.AugmentedNormalForm

@[expose] public section

open scoped BigOperators
open Matrix
noncomputable section
namespace TernaryPoly.OrdinaryResidueSupport
open ModThreeGoodAction GoodIntegralNormalization PrimitiveLineUniqueness
open AugmentedFrameComplex PrimitiveLineHeight GoodAugmentedNormalForm

/-- A rational hyperplane is indexed by its actual one-dimensional rational normal space. -/
abbrev Normal := RationalLine

/-- Primitive integral rows cannot define the zero rational functional. -/
lemma primitive_rational_ne_zero {v : IntegralVector} (hv : Primitive v) :
    rationalVector v ≠ 0 := by
  obtain ⟨b,hb⟩ := primitive_bezout hv
  intro hz
  have hi (i : Fin 3) : v i=0 := by
    have h : (v i : ℚ)=0 := congrFun hz i
    exact_mod_cast h
  simp [hi] at hb

/-- The actual rational normal line of a primitive integral row. -/
def normalOfRow (v : IntegralVector) (hv : Primitive v) : Normal :=
  vectorLine (rationalVector v) (primitive_rational_ne_zero hv)

@[simp] lemma normalOfRow_val (v : IntegralVector) (hv : Primitive v) :
    (normalOfRow v hv).val=Submodule.span ℚ {rationalVector v} := rfl

lemma normalOfRow_neg (v : IntegralVector) (hv : Primitive v) :
    normalOfRow (-v) hv.neg=normalOfRow v hv :=
  Subtype.ext (span_neg v)

lemma normalOfRow_eq_iff {v w : IntegralVector} (hv : Primitive v) (hw : Primitive w) :
    normalOfRow v hv=normalOfRow w hw ↔ v=w ∨ v= -w := by
  constructor
  · intro h
    exact primitive_eq_or_neg_of_span_eq hv hw (congrArg Subtype.val h)
  · rintro (h | h)
    · subst v; rfl
    · subst v; exact normalOfRow_neg w hw

@[simp] lemma normalOfRow_generator (L : Normal) :
    normalOfRow (primitiveGenerator L) (primitiveGenerator_primitive L)=L :=
  Subtype.ext (primitiveGenerator_span L)

/-- Every normal is represented by a genuine primitive integral row, unique up to sign. -/
lemma exists_primitive_row (L : Normal) : ∃ v hv, normalOfRow v hv=L :=
  ⟨primitiveGenerator L,primitiveGenerator_primitive L,normalOfRow_generator L⟩

/-- Coordinate-sum height of the primitive normal; no choice of row sign matters. -/
def height (L : Normal) : ℕ := ∑ i, (primitiveGenerator L i).natAbs

lemma height_normalOfRow (v : IntegralVector) (hv : Primitive v) :
    height (normalOfRow v hv)=∑ i, (v i).natAbs := by
  rcases primitive_eq_or_neg_of_span_eq
    (primitiveGenerator_primitive (normalOfRow v hv)) hv
    (primitiveGenerator_span (normalOfRow v hv)) with he | he
  · simp only [height,he]
  · simp only [height,he,Pi.neg_apply,Int.natAbs_neg]

/-- Integral invertible right row multiplication preserves primitivity. -/
lemma primitive_vecMul (g : IntegralGL) {v : IntegralVector} (hv : Primitive v) :
    Primitive (Matrix.vecMul v g.val) := by
  obtain ⟨b,hb⟩ := primitive_bezout hv
  apply primitive_of_bezout (b := g⁻¹.val.mulVec b)
  change dotProduct (g⁻¹.val.mulVec b) (Matrix.vecMul v g.val)=1
  rw [dotProduct_comm,← Matrix.dotProduct_mulVec,Matrix.mulVec_mulVec,
    ← Units.val_mul,mul_inv_cancel,Units.val_one,Matrix.one_mulVec,dotProduct_comm]
  exact hb

/-- Right multiplication of an actual normal row by an actual integral matrix. -/
def rowAction (g : IntegralGL) (L : Normal) : Normal :=
  normalOfRow (Matrix.vecMul (primitiveGenerator L) g.val)
    (primitive_vecMul g (primitiveGenerator_primitive L))

lemma rowAction_normalOfRow (g : IntegralGL) (v : IntegralVector) (hv : Primitive v) :
    rowAction g (normalOfRow v hv)=normalOfRow (Matrix.vecMul v g.val) (primitive_vecMul g hv) := by
  apply (normalOfRow_eq_iff _ _).mpr
  rcases primitive_eq_or_neg_of_span_eq
    (primitiveGenerator_primitive (normalOfRow v hv)) hv
    (primitiveGenerator_span (normalOfRow v hv)) with he | he
  · exact Or.inl (congrArg (fun u => Matrix.vecMul u g.val) he)
  · exact Or.inr (by rw [he,Matrix.neg_vecMul])

@[simp] lemma rowAction_one (L : Normal) : rowAction 1 L=L := by
  obtain ⟨v,hv,rfl⟩ := exists_primitive_row L
  rw [rowAction_normalOfRow]
  simp

lemma rowAction_mul (g h : IntegralGL) (L : Normal) :
    rowAction (g*h) L=rowAction h (rowAction g L) := by
  obtain ⟨v,hv,rfl⟩ := exists_primitive_row L
  simp only [rowAction_normalOfRow,Units.val_mul,Matrix.vecMul_vecMul]

/-- The row action is a genuine equivalence; inverse substitution reverses this transport. -/
def rowEquiv (g : IntegralGL) : Normal ≃ Normal where
  toFun := rowAction g
  invFun := rowAction g⁻¹
  left_inv L := by rw [← rowAction_mul,mul_inv_cancel,rowAction_one]
  right_inv L := by rw [← rowAction_mul,inv_mul_cancel,rowAction_one]

/-- The rational linear functional defining the hyperplane. -/
def normalFunctional (L : Normal) : Space →ₗ[ℚ] ℚ where
  toFun x := dotProduct (rationalVector (primitiveGenerator L)) x
  map_add' _ _ := dotProduct_add _ _ _
  map_smul' _ _ := by simp [dotProduct_smul]

/-- The actual rational hyperplane attached to its primitive normal line. -/
def hyperplane (L : Normal) : RationalSubspace := (normalFunctional L).ker

lemma mem_hyperplane_iff (L : Normal) (x : Space) :
    x ∈ hyperplane L ↔ dotProduct (rationalVector (primitiveGenerator L)) x=0 := Iff.rfl

lemma mem_hyperplane_normalOfRow (v : IntegralVector) (hv : Primitive v) (x : Space) :
    x ∈ hyperplane (normalOfRow v hv) ↔ dotProduct (rationalVector v) x=0 := by
  rw [mem_hyperplane_iff]
  rcases primitive_eq_or_neg_of_span_eq
    (primitiveGenerator_primitive (normalOfRow v hv)) hv
    (primitiveGenerator_span (normalOfRow v hv)) with he | he
  · rw [he]
  · rw [he,rationalVector_neg,neg_dotProduct,neg_eq_zero]

lemma axis_primitive (i : Fin 3) : Primitive (Pi.single i (1 : ℤ)) := by
  fin_cases i <;> unfold Primitive content <;> decide +kernel

/-- The three coordinate hyperplanes have the three coordinate normal lines. -/
def axis (i : Fin 3) : Normal := normalOfRow (Pi.single i 1) (axis_primitive i)

def Coordinate (L : Normal) : Prop := ∃ i, L=axis i

lemma coordinate_normalOfRow_iff (v : IntegralVector) (hv : Primitive v) :
    Coordinate (normalOfRow v hv) ↔ ∃ i : Fin 3, ∀ j, j≠i → v j=0 := by
  constructor
  · rintro ⟨i,hi⟩
    rcases (normalOfRow_eq_iff hv (axis_primitive i)).mp hi with he | he
    · exact ⟨i,fun j hj => by simp [he,Pi.single_eq_of_ne hj]⟩
    · exact ⟨i,fun j hj => by simp [he,Pi.single_eq_of_ne hj]⟩
  · rintro ⟨i,hi⟩
    have he : v=Pi.single i (v i) := by
      funext j
      by_cases hj : j=i
      · subst j; simp
      · simp [Pi.single_eq_of_ne hj,hi j hj]
    have hu : IsUnit (v i) := by
      apply Int.isUnit_iff_natAbs_eq.mpr
      have hp := hv
      rw [he] at hp
      fin_cases i <;> simpa [Primitive,content] using hp
    refine ⟨i,(normalOfRow_eq_iff hv (axis_primitive i)).mpr ?_⟩
    rcases Int.isUnit_iff.mp hu with hh | hh
    · left; rw [he,hh]
    · right
      rw [he,hh]
      ext j
      by_cases hj : j=i <;> simp [hj,Pi.single_eq_of_ne]

lemma mem_hyperplane_axis (i : Fin 3) (x : Space) : x ∈ hyperplane (axis i) ↔ x i=0 := by
  rw [axis,mem_hyperplane_normalOfRow]
  have he : rationalVector (Pi.single i (1 : ℤ))=Pi.single i (1 : ℚ) := by
    ext j
    by_cases hj : j=i <;> simp [rationalVector,hj,Pi.single_eq_of_ne]
  rw [he,single_dotProduct,one_mul]

end TernaryPoly.OrdinaryResidueSupport
