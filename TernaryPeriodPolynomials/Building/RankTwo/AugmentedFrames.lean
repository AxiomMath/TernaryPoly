module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
public import Mathlib.RingTheory.Localization.Integer
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Data.Int.GCD
public import Mathlib.Algebra.Group.Int.Units
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Data.Fintype.Order
public import Mathlib.Data.List.Enum
public import Mathlib.Data.String.Defs
public import Mathlib.Lean.Elab.InfoTree
public import Mathlib.Lean.Elab.Tactic.Basic
public import Mathlib.Lean.Elab.Tactic.Meta
public import Mathlib.Lean.Expr.ExtraRecognizers
public import Mathlib.Lean.Expr.Rat
public import Mathlib.Lean.GoalsLocation
public import Mathlib.Lean.MessageData.Trace
public import Mathlib.Lean.Meta
public import Mathlib.Lean.Meta.Basic
public import Mathlib.Lean.Meta.KAbstractPositions
public import Mathlib.Lean.Meta.Tactic.Rewrite
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr

@[expose] public section


open scoped BigOperators
noncomputable section
namespace TernaryPoly.RankTwoAugmentedFrames

abbrev IntegralVector := Fin 2 → ℤ
abbrev Space := Fin 2 → ℚ
abbrev IntegralGL := Matrix.GeneralLinearGroup (Fin 2) ℤ
abbrev RationalLine2 := {L : Submodule ℚ Space // Module.finrank ℚ L = 1}

/-- The actual positive coordinate gcd of an integral pair. -/
def content (v : IntegralVector) : ℕ := Int.gcd (v 0) (v 1)
def Primitive (v : IntegralVector) : Prop := content v = 1
def rationalVector (v : IntegralVector) : Space := fun i => (v i : ℚ)
def primitivePart (v : IntegralVector) : IntegralVector := fun i => v i / (content v : ℤ)

theorem content_dvd (v : IntegralVector) (i : Fin 2) : (content v : ℤ) ∣ v i := by
  fin_cases i
  · exact Int.gcd_dvd_left _ _
  · exact Int.gcd_dvd_right _ _

theorem content_ne_zero {v : IntegralVector} (hv : v ≠ 0) : content v ≠ 0 := by
  intro hd
  apply hv
  funext i
  have hi := content_dvd v i
  rw [hd,Nat.cast_zero,zero_dvd_iff] at hi
  exact hi

theorem mul_primitivePart (v : IntegralVector) (i : Fin 2) :
    (content v : ℤ) * primitivePart v i = v i := Int.mul_ediv_cancel' (content_dvd v i)

theorem content_int_mul (n : ℤ) (v : IntegralVector) :
    content (fun i => n * v i) = n.natAbs * content v := by
  simp only [content,Int.gcd_def,Int.natAbs_mul,Nat.gcd_mul_left]

theorem primitivePart_primitive {v : IntegralVector} (hv : content v ≠ 0) :
    Primitive (primitivePart v) := by
  have he : (fun i => (content v : ℤ) * primitivePart v i) = v :=
    funext (mul_primitivePart v)
  have h := content_int_mul (content v) (primitivePart v)
  rw [he,Int.natAbs_natCast] at h
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hv)
    (by simpa only [mul_one] using h.symm)

theorem rationalVector_primitivePart (v : IntegralVector) :
    (content v : ℚ) • rationalVector (primitivePart v) = rationalVector v := by
  funext i
  change (content v : ℚ) * (primitivePart v i : ℚ) = (v i : ℚ)
  exact_mod_cast mul_primitivePart v i

theorem primitive_bezout {v : IntegralVector} (hv : Primitive v) :
    ∃ a b : ℤ, v 0 * a + v 1 * b = 1 := by
  refine ⟨Int.gcdA (v 0) (v 1),Int.gcdB (v 0) (v 1),?_⟩
  rw [← Int.gcd_eq_gcd_ab]
  change (content v : ℤ) = 1
  rw [hv,Nat.cast_one]

/-- Bézout gives a genuine determinant-one integer matrix with the specified first column. -/
theorem exists_primitive_completion (v : IntegralVector) (hv : Primitive v) :
    ∃ g : IntegralGL, (fun i => g.val i 0) = v ∧ g.val.det = 1 := by
  obtain ⟨a,b,hab⟩ := primitive_bezout hv
  let M : Matrix (Fin 2) (Fin 2) ℤ := !![v 0,-b;v 1,a]
  have hd : M.det = 1 := by
    rw [Matrix.det_fin_two]
    change v 0 * a - (-b) * v 1 = 1
    nlinarith [hab]
  refine ⟨Matrix.nonsingInvUnit M (by rw [hd]; exact isUnit_one),?_,hd⟩
  funext i
  fin_cases i <;> rfl

def primitiveCompletion (v : IntegralVector) (hv : Primitive v) : IntegralGL :=
  (exists_primitive_completion v hv).choose

theorem primitiveCompletion_first_column (v : IntegralVector) (hv : Primitive v) :
    (fun i => (primitiveCompletion v hv).val i 0) = v :=
  (exists_primitive_completion v hv).choose_spec.1

theorem primitiveCompletion_det (v : IntegralVector) (hv : Primitive v) :
    (primitiveCompletion v hv).val.det = 1 :=
  (exists_primitive_completion v hv).choose_spec.2

/-- Common denominators and coordinate gcd normalization are carried out in the actual lattice. -/
theorem clear_vector_denominators (x : Space) :
    ∃ (d : ℤ) (v : IntegralVector), 0 < d ∧ rationalVector v = (d : ℚ) • x := by
  classical
  obtain ⟨d,hd⟩ := IsLocalization.exist_integer_multiples_of_finite (Submonoid.pos ℤ) x
  let v : IntegralVector := fun i => (hd i).choose
  refine ⟨d.val,v,d.property,?_⟩
  funext i
  change (v i : ℚ) = (d.val : ℚ) * x i
  simpa only [Algebra.smul_def,algebraMap_int_eq,Int.coe_castRingHom,v] using (hd i).choose_spec

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
  have hc := content_ne_zero hvz
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

theorem rationalLine_primitive_generator (L : RationalLine2) :
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

theorem scalar_integral_of_primitive {v w : IntegralVector} (hv : Primitive v) {q : ℚ}
    (hq : rationalVector w = q • rationalVector v) : ∃ n : ℤ, (n : ℚ) = q := by
  obtain ⟨a,b,hab⟩ := primitive_bezout hv
  have he (i : Fin 2) : (w i : ℚ) = q * (v i : ℚ) := congrFun hq i
  have habq : (v 0 : ℚ) * (a : ℚ) + (v 1 : ℚ) * (b : ℚ) = 1 := by exact_mod_cast hab
  refine ⟨w 0 * a + w 1 * b,?_⟩
  push_cast
  rw [he,he]
  calc
    q * (v 0 : ℚ) * a + q * (v 1 : ℚ) * b =
        q * ((v 0 : ℚ) * a + (v 1 : ℚ) * b) := by ring
    _ = q := by rw [habq,mul_one]

theorem integer_multiple_of_mem_span {v w : IntegralVector} (hv : Primitive v)
    (hw : rationalVector w ∈ Submodule.span ℚ {rationalVector v}) :
    ∃ n : ℤ, w = fun i => n * v i := by
  obtain ⟨q,hq⟩ := Submodule.mem_span_singleton.mp hw
  obtain ⟨n,hn⟩ := scalar_integral_of_primitive hv hq.symm
  refine ⟨n,?_⟩
  funext i
  have hi : q * (v i : ℚ) = (w i : ℚ) := congrFun hq i
  rw [← hn] at hi
  exact_mod_cast hi.symm

theorem primitive_eq_or_neg_of_mem_span {v w : IntegralVector} (hv : Primitive v)
    (hw : Primitive w) (hmem : rationalVector w ∈ Submodule.span ℚ {rationalVector v}) :
    w = v ∨ w = -v := by
  obtain ⟨n,hn⟩ := integer_multiple_of_mem_span hv hmem
  have habs : n.natAbs = 1 := by
    have h := content_int_mul n v
    rw [← hn,hv,hw,mul_one] at h
    exact h.symm
  rcases Int.isUnit_iff.mp (Int.isUnit_iff_natAbs_eq.mpr habs) with h | h
  · left
    simpa only [h,one_mul] using hn
  · right
    funext i
    simpa only [h,neg_one_mul,Pi.neg_apply] using congrFun hn i

theorem primitive_eq_or_neg_of_span_eq {v w : IntegralVector} (hv : Primitive v)
    (hw : Primitive w)
    (hspan : Submodule.span ℚ {rationalVector v} = Submodule.span ℚ {rationalVector w}) :
    v = w ∨ v = -w := by
  apply primitive_eq_or_neg_of_mem_span hw hv
  rw [← hspan]
  exact Submodule.mem_span_singleton_self _

/-- Coefficient extension of the genuine integer matrix action. -/
def rationalRepresentation : IntegralGL →* (Space ≃ₗ[ℚ] Space) :=
  ((LinearMap.GeneralLinearGroup.generalLinearEquiv ℚ Space).toMonoidHom.comp
    Matrix.GeneralLinearGroup.toLin.toMonoidHom).comp
      (Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ))

theorem rationalRepresentation_apply (g : IntegralGL) (v : Space) :
    rationalRepresentation g v =
      (Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) g).val.mulVec v := by
  change (Matrix.GeneralLinearGroup.toLin
    (Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) g)).toLinearEquiv v = _
  rw [LinearMap.GeneralLinearGroup.coe_toLinearEquiv,Matrix.GeneralLinearGroup.toLin_apply]
  rfl

theorem rationalVector_mulVec (g : IntegralGL) (v : IntegralVector) :
    rationalVector (g.val.mulVec v) = rationalRepresentation g (rationalVector v) := by
  rw [rationalRepresentation_apply]
  funext i
  simp [rationalVector,Matrix.mulVec,dotProduct,Matrix.GeneralLinearGroup.map_apply]

def vectorLine (v : Space) (hv : v ≠ 0) : RationalLine2 :=
  ⟨Submodule.span ℚ {v},finrank_span_singleton hv⟩

/-- The three literal vectors in a rank-two augmented frame. -/
def template : Fin 3 → Space := ![![1,0],![0,1],![1,1]]
def integralTemplate : Fin 3 → IntegralVector := ![![1,0],![0,1],![1,1]]

theorem rationalVector_integralTemplate (i : Fin 3) :
    rationalVector (integralTemplate i) = template i := by
  funext j
  fin_cases i <;> fin_cases j <;> rfl

theorem template_ne_zero (i : Fin 3) : template i ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  fin_cases i <;> norm_num [template] at *

def augmentedLine (g : IntegralGL) (i : Fin 3) : RationalLine2 :=
  vectorLine (rationalRepresentation g (template i))
    (fun h => template_ne_zero i ((rationalRepresentation g).injective
      (h.trans (map_zero (rationalRepresentation g)).symm)))

def augmentedFrame (g : IntegralGL) : Finset RationalLine2 :=
  Finset.univ.image (augmentedLine g)

def IsFace (s : Finset RationalLine2) : Prop :=
  s.Nonempty ∧ ∃ g : IntegralGL, s ⊆ augmentedFrame g

/-- Faces are nonempty subsets of actual integral augmented frames. -/
def ambient : PreAbstractSimplicialComplex RationalLine2 where
  faces := {s | IsFace s}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨hs.1,?_⟩
    intro t hts ht
    exact ⟨ht,hs.2.imp (fun _ hg => hts.trans hg)⟩

theorem augmentedFrame_mem (g : IntegralGL) : augmentedFrame g ∈ ambient := by
  refine ⟨?_,g,Finset.Subset.refl _⟩
  exact Finset.image_nonempty.mpr Finset.univ_nonempty

theorem subset_augmentedFrame_mem (g : IntegralGL) {s : Finset RationalLine2}
    (hs : s.Nonempty) (hsub : s ⊆ augmentedFrame g) : s ∈ ambient := ⟨hs,g,hsub⟩

theorem primitiveCompletion_template_zero (v : IntegralVector) (hv : Primitive v) :
    rationalRepresentation (primitiveCompletion v hv) (template 0) = rationalVector v := by
  rw [rationalRepresentation_apply]
  change (Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) (primitiveCompletion v hv)).val.mulVec
    (Pi.single 0 1) = rationalVector v
  rw [Matrix.mulVec_single_one]
  funext i
  change ((primitiveCompletion v hv).val i 0 : ℚ) = (v i : ℚ)
  exact congrArg (fun z : ℤ => (z : ℚ)) (congrFun (primitiveCompletion_first_column v hv) i)

theorem rationalLine_eq_augmentedLine (L : RationalLine2) :
    ∃ g : IntegralGL, augmentedLine g 0 = L := by
  obtain ⟨v,hp,_,hs⟩ := rationalLine_primitive_generator L
  refine ⟨primitiveCompletion v hp,?_⟩
  apply Subtype.ext
  change Submodule.span ℚ {rationalRepresentation (primitiveCompletion v hp) (template 0)} = L.val
  rw [primitiveCompletion_template_zero]
  exact hs

theorem singleton_mem_ambient (L : RationalLine2) : {L} ∈ ambient := by
  classical
  obtain ⟨g,hg⟩ := rationalLine_eq_augmentedLine L
  apply subset_augmentedFrame_mem g (Finset.singleton_nonempty L)
  apply Finset.singleton_subset_iff.mpr
  exact Finset.mem_image.mpr ⟨0,Finset.mem_univ _,hg⟩

def ambientComplex : AbstractSimplicialComplex RationalLine2 where
  toPreAbstractSimplicialComplex := ambient
  singleton_mem := singleton_mem_ambient

/-- The three displayed lines are always distinct. -/
theorem augmentedLine_injective (g : IntegralGL) : Function.Injective (augmentedLine g) := by
  intro i j h
  have hs : Submodule.span ℚ {rationalRepresentation g (template i)} =
      Submodule.span ℚ {rationalRepresentation g (template j)} := congrArg Subtype.val h
  have hm : rationalRepresentation g (template i) ∈
      Submodule.span ℚ {rationalRepresentation g (template j)} := by
    rw [← hs]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨q,hq⟩ := Submodule.mem_span_singleton.mp hm
  have he : q • template j = template i := (rationalRepresentation g).injective
    ((map_smul (rationalRepresentation g) q (template j)).trans hq)
  have h0 := congrFun he 0
  have h1 := congrFun he 1
  fin_cases i <;> fin_cases j <;> first | rfl | (norm_num [template] at *; all_goals linarith)

theorem augmentedFrame_card (g : IntegralGL) : (augmentedFrame g).card = 3 := by
  rw [augmentedFrame,Finset.card_image_of_injective _ (augmentedLine_injective g)]
  rfl

/-- Cardinal-three faces are exactly the actual augmented frames. -/
theorem triangle_iff_frame (s : Finset RationalLine2) :
    s ∈ ambient ∧ s.card = 3 ↔ ∃ g : IntegralGL, s = augmentedFrame g := by
  constructor
  · rintro ⟨⟨_,g,hg⟩,hc⟩
    refine ⟨g,Finset.eq_of_subset_of_card_le hg ?_⟩
    rw [augmentedFrame_card,hc]
  · rintro ⟨g,rfl⟩
    exact ⟨augmentedFrame_mem g,augmentedFrame_card g⟩

/-- The matrix with two specified template vectors as its columns. -/
def pairMatrix (i j : Fin 3) : Matrix (Fin 2) (Fin 2) ℤ :=
  fun r c => if c = 0 then integralTemplate i r else integralTemplate j r

theorem pairMatrix_unit (i j : Fin 3) (h : i ≠ j) : IsUnit (pairMatrix i j).det := by
  fin_cases i <;> fin_cases j <;>
    first | exact (h rfl).elim | norm_num [pairMatrix,integralTemplate,Matrix.det_fin_two]

def pairGL (i j : Fin 3) (h : i ≠ j) : IntegralGL :=
  Matrix.nonsingInvUnit (pairMatrix i j) (pairMatrix_unit i j h)

theorem pairGL_template_zero (i j : Fin 3) (h : i ≠ j) :
    rationalRepresentation (pairGL i j h) (template 0) = template i := by
  have ht : (pairGL i j h).val.mulVec (integralTemplate 0) = integralTemplate i := by
    change (pairMatrix i j).mulVec (integralTemplate 0) = integralTemplate i
    funext r
    simp [Matrix.mulVec,dotProduct,Fin.sum_univ_two,pairMatrix,integralTemplate]
  rw [← rationalVector_integralTemplate 0,← rationalVector_mulVec,ht,
    rationalVector_integralTemplate]

theorem pairGL_template_one (i j : Fin 3) (h : i ≠ j) :
    rationalRepresentation (pairGL i j h) (template 1) = template j := by
  have ht : (pairGL i j h).val.mulVec (integralTemplate 1) = integralTemplate j := by
    change (pairMatrix i j).mulVec (integralTemplate 1) = integralTemplate j
    funext r
    simp [Matrix.mulVec,dotProduct,Fin.sum_univ_two,pairMatrix,integralTemplate]
  rw [← rationalVector_integralTemplate 1,← rationalVector_mulVec,ht,
    rationalVector_integralTemplate]

theorem augmentedLine_pair_zero (g : IntegralGL) (i j : Fin 3) (h : i ≠ j) :
    augmentedLine (g * pairGL i j h) 0 = augmentedLine g i := by
  apply Subtype.ext
  change Submodule.span ℚ {rationalRepresentation (g * pairGL i j h) (template 0)} = _
  rw [map_mul,LinearEquiv.mul_apply,pairGL_template_zero]
  rfl

theorem augmentedLine_pair_one (g : IntegralGL) (i j : Fin 3) (h : i ≠ j) :
    augmentedLine (g * pairGL i j h) 1 = augmentedLine g j := by
  apply Subtype.ext
  change Submodule.span ℚ {rationalRepresentation (g * pairGL i j h) (template 1)} = _
  rw [map_mul,LinearEquiv.mul_apply,pairGL_template_one]
  rfl

/-- Every ordered distinct actual edge is the pair of column lines of an integer basis. -/
theorem edge_basis (L M : RationalLine2) (hne : L ≠ M) (he : {L,M} ∈ ambient) :
    ∃ g : IntegralGL, augmentedLine g 0 = L ∧ augmentedLine g 1 = M := by
  obtain ⟨_,g,hg⟩ := he
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp (hg (Finset.mem_insert_self L {M}))
  obtain ⟨j,_,hj⟩ := Finset.mem_image.mp (hg (Finset.mem_insert_of_mem (Finset.mem_singleton_self M)))
  have hij : i ≠ j := by
    intro h
    apply hne
    rw [← hi,← hj,h]
  exact ⟨g * pairGL i j hij,(augmentedLine_pair_zero g i j hij).trans hi,
    (augmentedLine_pair_one g i j hij).trans hj⟩

end TernaryPoly.RankTwoAugmentedFrames
