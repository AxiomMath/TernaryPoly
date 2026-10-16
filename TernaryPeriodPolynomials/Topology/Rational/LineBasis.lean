module

public import TernaryPeriodPolynomials.Building.AugmentedFrame.FrameComplex
public import TernaryPeriodPolynomials.Building.Primitive.BasisExtension
public import Mathlib.RingTheory.Localization.Integer
public import Mathlib.RingTheory.Localization.FractionRing

@[expose] public section


noncomputable section
namespace TernaryPoly.RationalLineBasis

open ModThreeGoodAction GoodIntegralNormalization PrimitiveBasisExtension
open AugmentedFrameComplex

/-- A finite rational vector has a common positive integral denominator. -/
theorem clear_vector_denominators (x : Space) :
    ∃ (d : ℤ) (v : IntegralVector), 0 < d ∧ rationalVector v = (d : ℚ) • x := by
  classical
  obtain ⟨d,hd⟩ := IsLocalization.exist_integer_multiples_of_finite (Submonoid.pos ℤ) x
  let v : IntegralVector := fun i => (hd i).choose
  refine ⟨d.val,v,d.property,?_⟩
  funext i
  change (v i : ℚ) = (d.val : ℚ) * x i
  simpa only [Algebra.smul_def,algebraMap_int_eq,Int.coe_castRingHom,v] using (hd i).choose_spec

/-- A nonzero integer vector has nonzero coordinate content, without a residue hypothesis. -/
theorem content_ne_zero_of_ne_zero {v : IntegralVector} (hv : v ≠ 0) : content v ≠ 0 := by
  intro hd
  apply hv
  funext i
  have hi := content_dvd v i
  rw [hd,Nat.cast_zero,zero_dvd_iff] at hi
  exact hi

/-- Any nonzero rational vector has a primitive integral generator of the same rational span. -/
theorem exists_primitive_same_span (x : Space) (hx : x ≠ 0) :
    ∃ v : IntegralVector, Primitive v ∧ rationalVector v ≠ 0 ∧
      Submodule.span ℚ {rationalVector v} = Submodule.span ℚ {x} := by
  obtain ⟨d,v,hd,hv⟩ := clear_vector_denominators x
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have hvr : rationalVector v ≠ 0 := by
    rw [hv]
    exact smul_ne_zero hdq hx
  have hvz : v ≠ 0 := by
    intro h
    apply hvr
    funext i
    change (v i : ℚ) = 0
    rw [h]
    rfl
  have hc := content_ne_zero_of_ne_zero hvz
  have hcq : (content v : ℚ) ≠ 0 := by exact_mod_cast hc
  have hp : rationalVector (primitivePart v) ≠ 0 := by
    intro h
    have he := rationalVector_primitivePart v
    rw [h,smul_zero] at he
    exact hvr he.symm
  refine ⟨primitivePart v,primitivePart_primitive hc,hp,?_⟩
  calc
    Submodule.span ℚ {rationalVector (primitivePart v)} =
        Submodule.span ℚ {rationalVector v} := by
      rw [← rationalVector_primitivePart v,
        Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hcq)]
    _ = Submodule.span ℚ {x} := by
      rw [hv,Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hdq)]

/-- Every rational line, good or bad, has a primitive integral generator. -/
theorem rationalLine_primitive_generator (L : RationalLine) :
    ∃ v : IntegralVector, Primitive v ∧ rationalVector v ≠ 0 ∧
      Submodule.span ℚ {rationalVector v} = L.val := by
  have hL : L.val ≠ ⊥ := by
    intro h
    have hd := L.property
    rw [h,finrank_bot] at hd
    exact Nat.zero_ne_one hd
  obtain ⟨x,hx,hxz⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hL
  obtain ⟨v,hp,hv,hs⟩ := exists_primitive_same_span x hxz
  refine ⟨v,hp,hv,hs.trans ?_⟩
  apply Submodule.eq_of_le_of_finrank_eq
  · exact Submodule.span_le.mpr (by intro y hy; rcases hy with rfl; exact hx)
  · rw [finrank_span_singleton hxz,L.property]

/-- Primitive basis completion sends the first standard vector to its integral first column. -/
theorem primitiveCompletion_template_zero (v : IntegralVector) (hv : Primitive v) :
    rationalRepresentation (primitiveCompletion v hv) (template 0) = rationalVector v := by
  rw [rationalRepresentation_apply]
  change (Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) (primitiveCompletion v hv)).val.mulVec
    (Pi.single 0 1) = rationalVector v
  rw [Matrix.mulVec_single_one]
  funext i
  change ((primitiveCompletion v hv).val i 0 : ℚ) = (v i : ℚ)
  exact congrArg (fun z : ℤ => (z : ℚ)) (congrFun (primitiveCompletion_first_column v hv) i)

/-- Every rational line occurs as the first line of a genuine integral augmented frame. -/
theorem rationalLine_eq_augmentedLine (L : RationalLine) :
    ∃ g : IntegralGL, augmentedLine g 0 = L := by
  obtain ⟨v,hp,_,hs⟩ := rationalLine_primitive_generator L
  refine ⟨primitiveCompletion v hp,?_⟩
  apply Subtype.ext
  change Submodule.span ℚ {rationalRepresentation (primitiveCompletion v hp) (template 0)} = L.val
  rw [primitiveCompletion_template_zero]
  exact hs

/-- Singleton fullness follows from actual integral basis extension for every rational line. -/
theorem singleton_mem_ambient (L : RationalLine) : {L} ∈ ambient := by
  classical
  obtain ⟨g,hg⟩ := rationalLine_eq_augmentedLine L
  apply subset_augmentedFrame_mem g (Finset.singleton_nonempty L)
  apply Finset.singleton_subset_iff.mpr
  exact Finset.mem_image.mpr ⟨0,Finset.mem_univ _,hg⟩

/-- The existing genuine augmented-frame precomplex is an abstract simplicial complex. -/
def ambientComplex : AbstractSimplicialComplex RationalLine where
  toPreAbstractSimplicialComplex := ambient
  singleton_mem := singleton_mem_ambient

@[simp] theorem ambientComplex_toPreAbstractSimplicialComplex :
    ambientComplex.toPreAbstractSimplicialComplex = ambient := rfl

end TernaryPoly.RationalLineBasis
