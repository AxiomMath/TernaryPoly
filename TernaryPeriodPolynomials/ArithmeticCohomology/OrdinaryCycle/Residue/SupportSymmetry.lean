module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Residue.SupportNormals
public import Lean.Elab.Tactic.Omega

@[expose] public section


open scoped BigOperators
noncomputable section
namespace TernaryPoly.OrdinaryResidueSupport
open ModThreeGoodAction GoodIntegralNormalization PrimitiveLineUniqueness
open PrimitiveLineHeight GoodAugmentedNormalForm

/-- Independent signs on the three integral row coordinates. -/
def signRow (s : Fin 3 → Bool) (v : IntegralVector) : IntegralVector :=
  fun i => if s i then -v i else v i

/-- Permutation of the three integral row coordinates. -/
def permuteRow (π : Equiv.Perm (Fin 3)) (v : IntegralVector) : IntegralVector :=
  fun i => v (π i)

lemma signRow_natAbs (s : Fin 3 → Bool) (v : IntegralVector) (i : Fin 3) :
    (signRow s v i).natAbs=(v i).natAbs := by
  simp only [signRow]
  split <;> simp

lemma primitive_signRow (s : Fin 3 → Bool) {v : IntegralVector} (hv : Primitive v) :
    Primitive (signRow s v) := by
  simpa only [Primitive,content,signRow_natAbs] using hv

lemma primitive_permuteRow (π : Equiv.Perm (Fin 3)) {v : IntegralVector} (hv : Primitive v) :
    Primitive (permuteRow π v) := by
  obtain ⟨b,hb⟩ := primitive_bezout hv
  apply primitive_of_bezout (b := permuteRow π b)
  exact (Equiv.sum_comp π (fun i => b i*v i)).trans hb

lemma signRow_neg (s : Fin 3 → Bool) (v : IntegralVector) : signRow s (-v)= -signRow s v := by
  funext i
  simp only [signRow,Pi.neg_apply]
  split <;> simp

lemma permuteRow_neg (π : Equiv.Perm (Fin 3)) (v : IntegralVector) :
    permuteRow π (-v)= -permuteRow π v := rfl

def signNormal (s : Fin 3 → Bool) (L : Normal) : Normal :=
  normalOfRow (signRow s (primitiveGenerator L))
    (primitive_signRow s (primitiveGenerator_primitive L))

def permuteNormal (π : Equiv.Perm (Fin 3)) (L : Normal) : Normal :=
  normalOfRow (permuteRow π (primitiveGenerator L))
    (primitive_permuteRow π (primitiveGenerator_primitive L))

lemma signNormal_normalOfRow (s : Fin 3 → Bool) (v : IntegralVector) (hv : Primitive v) :
    signNormal s (normalOfRow v hv)=normalOfRow (signRow s v) (primitive_signRow s hv) := by
  apply (normalOfRow_eq_iff _ _).mpr
  rcases primitive_eq_or_neg_of_span_eq
    (primitiveGenerator_primitive (normalOfRow v hv)) hv
    (primitiveGenerator_span (normalOfRow v hv)) with he | he
  · exact Or.inl (congrArg (signRow s) he)
  · exact Or.inr (by rw [he,signRow_neg])

lemma permuteNormal_normalOfRow (π : Equiv.Perm (Fin 3)) (v : IntegralVector) (hv : Primitive v) :
    permuteNormal π (normalOfRow v hv)=normalOfRow (permuteRow π v) (primitive_permuteRow π hv) := by
  apply (normalOfRow_eq_iff _ _).mpr
  rcases primitive_eq_or_neg_of_span_eq
    (primitiveGenerator_primitive (normalOfRow v hv)) hv
    (primitiveGenerator_span (normalOfRow v hv)) with he | he
  · exact Or.inl (congrArg (permuteRow π) he)
  · exact Or.inr (by rw [he,permuteRow_neg])

@[simp] lemma height_signNormal (s : Fin 3 → Bool) (L : Normal) :
    height (signNormal s L)=height L := by
  unfold signNormal
  rw [height_normalOfRow]
  simp only [signRow_natAbs,height]

@[simp] lemma height_permuteNormal (π : Equiv.Perm (Fin 3)) (L : Normal) :
    height (permuteNormal π L)=height L := by
  unfold permuteNormal
  rw [height_normalOfRow]
  exact Equiv.sum_comp π (fun i => (primitiveGenerator L i).natAbs)

/-- Any row with two nonzero coordinates can place them first using an actual permutation. -/
lemma exists_permutation_nonzero (v : IntegralVector)
    (hn : ¬∃ i : Fin 3, ∀ j, j≠i → v j=0) :
    ∃ π : Equiv.Perm (Fin 3), v (π 0)≠0 ∧ v (π 1)≠0 := by
  by_cases h0 : v 0=0
  · have h1 : v 1≠0 := by
      intro h1
      apply hn
      refine ⟨2,?_⟩
      intro j hj
      fin_cases j <;> simp_all
    have h2 : v 2≠0 := by
      intro h2
      apply hn
      refine ⟨1,?_⟩
      intro j hj
      fin_cases j <;> simp_all
    exact ⟨Equiv.swap 0 2,by simpa [Equiv.swap_apply_def] using h2,by simpa [Equiv.swap_apply_def] using h1⟩
  · by_cases h1 : v 1=0
    · have h2 : v 2≠0 := by
        intro h2
        apply hn
        refine ⟨0,?_⟩
        intro j hj
        fin_cases j <;> simp_all
      exact ⟨Equiv.swap 1 2,by simpa [Equiv.swap_apply_def] using h0,by simpa [Equiv.swap_apply_def] using h2⟩
    · exact ⟨Equiv.refl _,h0,h1⟩

/-- Every noncoordinate normal has a signed-permuted primitive row with positive first pair. -/
theorem positive_representative (L : Normal) (hn : ¬Coordinate L) :
    ∃ (s : Fin 3 → Bool) (π : Equiv.Perm (Fin 3)) (v : IntegralVector) (hv : Primitive v),
      normalOfRow v hv=signNormal s (permuteNormal π L) ∧
      0<v 0 ∧ 0<v 1 ∧ 0≤v 2 := by
  obtain ⟨w,hw,rfl⟩ := exists_primitive_row L
  obtain ⟨π,h0,h1⟩ := exists_permutation_nonzero w
    (fun h => hn ((coordinate_normalOfRow_iff w hw).mpr h))
  let s : Fin 3 → Bool := fun i => decide (w (π i)<0)
  let v := signRow s (permuteRow π w)
  have he (i : Fin 3) : v i=|w (π i)| := by
    by_cases h : w (π i)<0
    · simp [v,signRow,s,permuteRow,h,abs_of_neg h]
    · simp [v,signRow,s,permuteRow,h,abs_of_nonneg (le_of_not_gt h)]
  refine ⟨s,π,v,primitive_signRow s (primitive_permuteRow π hw),?_,?_,?_,?_⟩
  · rw [permuteNormal_normalOfRow,signNormal_normalOfRow]
  · rw [he]; exact abs_pos.mpr h0
  · rw [he]; exact abs_pos.mpr h1
  · rw [he]; exact abs_nonneg _

end TernaryPoly.OrdinaryResidueSupport
