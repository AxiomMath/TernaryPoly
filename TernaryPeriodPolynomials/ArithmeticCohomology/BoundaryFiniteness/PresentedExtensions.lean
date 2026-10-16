module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryFiniteness.PresentedSemidirect

@[expose] public section


namespace TernaryPeriodPolynomials.BoundaryFiniteness.PresentedExtensions

noncomputable section

variable {E Q F : Type} [Group E] [Group Q] [Group F]

def conjugation (projection : E →* Q) (lift : F →* E) : F →* MulAut projection.ker :=
  MulAut.conjNormal.comp lift

def cover (projection : E →* Q) (lift : F →* E) :
    projection.ker ⋊[conjugation projection lift] F →* E :=
  SemidirectProduct.lift projection.ker.subtype lift (by
    intro word
    ext normal
    exact MulAut.conjNormal_apply (lift word) normal)

theorem cover_apply (projection : E →* Q) (lift : F →* E)
    (element : projection.ker ⋊[conjugation projection lift] F) :
    cover projection lift element = element.left.val * lift element.right := rfl

theorem cover_surjective (projection : E →* Q) (lift : F →* E)
    (surjective : Function.Surjective (projection.comp lift)) :
    Function.Surjective (cover projection lift) := by
  intro element
  obtain ⟨word, equation⟩ := surjective (projection element)
  refine ⟨⟨⟨element * (lift word)⁻¹, ?_⟩, word⟩, ?_⟩
  · change projection (element * (lift word)⁻¹) = 1
    change projection (lift word) = projection element at equation
    rw [map_mul, map_inv, equation, mul_inv_cancel]
  · simp [cover_apply]

theorem cover_right_injective (projection : E →* Q) (lift : F →* E)
    {x y : projection.ker ⋊[conjugation projection lift] F}
    (same_image : cover projection lift x = cover projection lift y)
    (same_right : x.right = y.right) : x = y := by
  apply SemidirectProduct.ext
  · apply Subtype.ext
    apply mul_right_cancel (b := lift x.right)
    simpa only [cover_apply, same_right] using same_image
  · exact same_right

def liftedRelation (projection : E →* Q) (lift : F →* E)
    (relation : (projection.comp lift).ker) : projection.ker ⋊[conjugation projection lift] F :=
  ⟨⟨(lift relation.val)⁻¹, by
    change projection ((lift relation.val)⁻¹) = 1
    rw [map_inv, show projection (lift relation.val) = 1 from relation.property, inv_one]⟩, relation.val⟩

theorem liftedRelation_mem (projection : E →* Q) (lift : F →* E)
    (relation : (projection.comp lift).ker) :
    liftedRelation projection lift relation ∈ (cover projection lift).ker := by
  change (lift relation.val)⁻¹ * lift relation.val = 1
  exact inv_mul_cancel _

theorem cover_kernel_finitelyNormallyGenerated (projection : E →* Q) (lift : F →* E)
    (presented : (projection.comp lift).ker.IsFinitelyNormallyGenerated) :
    (cover projection lift).ker.IsFinitelyNormallyGenerated := by
  classical
  obtain ⟨relations, finite, generated⟩ := presented
  let relator : F → projection.ker ⋊[conjugation projection lift] F := fun word =>
    if membership : word ∈ (projection.comp lift).ker then
      liftedRelation projection lift ⟨word, membership⟩ else 1
  have relator_mem (word : F) : relator word ∈ (cover projection lift).ker := by
    dsimp only [relator]
    split
    · exact liftedRelation_mem projection lift _
    · exact (cover projection lift).ker.one_mem
  have relations_mem (word : F) (membership : word ∈ relations) :
      word ∈ (projection.comp lift).ker := generated ▸ Subgroup.subset_normalClosure membership
  have right_relator (word : F) (membership : word ∈ relations) :
      (relator word).right = word := by
    simp only [relator, dite_eq_left (relations_mem word membership), liftedRelation]
  let normal := Subgroup.normalClosure (relator '' relations)
  have included : normal ≤ (cover projection lift).ker := by
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨word, _, rfl⟩
    exact relator_mem word
  have right_surjective : Function.Surjective
      (SemidirectProduct.rightHom : projection.ker ⋊[conjugation projection lift] F →* F) :=
    fun word => ⟨SemidirectProduct.inr word, rfl⟩
  have image_relations :
      SemidirectProduct.rightHom '' (relator '' relations) = relations := by
    ext word
    constructor
    · rintro ⟨_, ⟨original, membership, rfl⟩, rfl⟩
      change (relator original).right ∈ relations
      rwa [right_relator original membership]
    · intro membership
      exact ⟨relator word, ⟨word, membership, rfl⟩, right_relator word membership⟩
  have image_normal : normal.map SemidirectProduct.rightHom = (projection.comp lift).ker := by
    rw [Subgroup.map_normalClosure _ _ right_surjective, image_relations, generated]
  refine ⟨relator '' relations, finite.image _, le_antisymm included ?_⟩
  intro element membership
  have right_mem : element.right ∈ (projection.comp lift).ker := by
    have equation := congrArg projection (show cover projection lift element = 1 from membership)
    have left_image : projection element.left.val = 1 := element.left.property
    change projection (lift element.right) = 1
    simpa only [cover_apply, map_mul, left_image, one_mul, map_one] using equation
  rw [← image_normal] at right_mem
  obtain ⟨representative, representative_mem, same_right⟩ := right_mem
  have same_image : cover projection lift representative = cover projection lift element :=
    (show cover projection lift representative = 1 from included representative_mem).trans membership.symm
  have same := cover_right_injective projection lift same_image same_right
  exact same ▸ representative_mem

theorem finitelyPresented (projection : E →* Q) (surjective : Function.Surjective projection)
    [Group.IsFinitelyPresented projection.ker] [Group.IsFinitelyPresented Q] :
    Group.IsFinitelyPresented E := by
  classical
  obtain ⟨n, presentation, presentation_surjective, presentation_kernel⟩ :=
    Group.IsFinitelyPresented.out (G := Q)
  let lift : FreeGroup (Fin n) →* E :=
    FreeGroup.lift fun i => (surjective (presentation (FreeGroup.of i))).choose
  have factorization : projection.comp lift = presentation := by
    apply FreeGroup.ext_hom
    intro i
    simpa [lift] using (surjective (presentation (FreeGroup.of i))).choose_spec
  let := PresentedSemidirect.finitelyPresented (conjugation projection lift)
  apply Group.IsFinitelyPresented.of_surjective (cover projection lift)
    (cover_surjective projection lift (by rwa [factorization]))
  apply cover_kernel_finitelyNormallyGenerated
  rwa [factorization]

end

end TernaryPeriodPolynomials.BoundaryFiniteness.PresentedExtensions
