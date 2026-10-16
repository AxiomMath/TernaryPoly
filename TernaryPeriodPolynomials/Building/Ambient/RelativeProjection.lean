module

public import TernaryPeriodPolynomials.Building.BadVertex.Fibers

@[expose] public section

noncomputable section
namespace TernaryPoly.AmbientRelativeProjection
open ModThreeGoodAction AugmentedFrameComplex BadVertexProjection BadVertexFibers

/-- The actual unrestricted link of a rational vertex. -/
def link (w : RationalLine) : PreAbstractSimplicialComplex RationalLine :=
  GoodLinkExtraction.goodLink ambient (fun L => L ≠ w) {w}

@[simp] theorem mem_link (w : RationalLine) (s : Finset RationalLine) :
    s ∈ link w ↔ s.Nonempty ∧ {w} ∪ s ∈ ambient ∧ ∀ L ∈ s, L ≠ w := by
  rw [link,GoodLinkExtraction.mem_goodLink]
  constructor <;> rintro ⟨hn,hf,ha⟩ <;> refine ⟨hn,?_,ha⟩
  all_goals
    convert hf using 1
    ext L
    simp only [Finset.mem_union]

/-- The quotient preserves actual unrestricted faces, including collapsed fibers. -/
theorem projection_mapsFaces (g : IntegralGL) :
    OrientedChainMap.MapsFaces (vertex g) (link (augmentedLine g 0))
      RankTwoAugmentedFrames.ambient := by
  intro s hs
  obtain ⟨hne,hface,havoid⟩ := (mem_link _ _).mp hs
  obtain ⟨_,h,hh⟩ := hface
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp
    (hh (Finset.mem_union_left s (Finset.mem_singleton_self _)))
  let q := lowerGL (g⁻¹ * (h * templateChange i))
    (first_column_lower_zero g (h * templateChange i) ((templateChange_line h i).trans hi))
  have hf : s.image (vertex g) ∈ RankTwoAugmentedFrames.ambient := by
    apply RankTwoAugmentedFrames.subset_augmentedFrame_mem q (hne.image (vertex g))
    intro L hL
    obtain ⟨M,hM,rfl⟩ := Finset.mem_image.mp hL
    obtain ⟨j,_,hj⟩ := Finset.mem_image.mp (hh (Finset.mem_union_right _ hM))
    have hij : i ≠ j := by
      intro he
      exact havoid M hM (hj.symm.trans ((congrArg (augmentedLine h) he.symm).trans hi))
    exact Finset.mem_image.mpr ⟨projectedIndex i j,Finset.mem_univ _,
      hj ▸ (vertex_template g h i j hi hij).symm⟩
  convert hf using 1
  ext L
  simp only [Finset.mem_image]

/-- Insert a zero first coordinate, then return to the chosen integral frame. -/
def lift (g : IntegralGL) : RankTwoAugmentedFrames.Space →ₗ[ℚ] Space :=
  (rationalRepresentation g).toLinearMap.comp
    ({
      toFun := fun v => ![0,v 0,v 1]
      map_add' := by intros; funext i; fin_cases i <;> simp
      map_smul' := by intros; funext i; fin_cases i <;> simp
    } : RankTwoAugmentedFrames.Space →ₗ[ℚ] Space)

theorem projection_lift (g : IntegralGL) (v : RankTwoAugmentedFrames.Space) :
    projection g (lift g v) = v := by
  change dropFirst (rationalRepresentation g⁻¹ (rationalRepresentation g ![0,v 0,v 1])) = v
  rw [representation_inverse]
  funext i
  fin_cases i <;> rfl

theorem lift_injective (g : IntegralGL) : Function.Injective (lift g) :=
  (show Function.LeftInverse (projection g) (lift g) from projection_lift g).injective

theorem lift_finrank (g : IntegralGL) (Q : RankTwoAugmentedFrames.RationalLine2) :
    Module.finrank ℚ (Q.val.map (lift g)) = 1 := by
  obtain ⟨p,_,hp,hs⟩ := RankTwoAugmentedFrames.rationalLine_primitive_generator Q
  rw [← hs,Submodule.map_span,Set.image_singleton]
  exact finrank_span_singleton (fun hz => hp ((lift_injective g)
    (hz.trans (map_zero (lift g)).symm)))

/-- Literal zero-coordinate section of quotient rational lines. -/
def sectionVertex (g : IntegralGL) (Q : RankTwoAugmentedFrames.RationalLine2) : RationalLine :=
  ⟨Q.val.map (lift g),lift_finrank g Q⟩

theorem section_span (g : IntegralGL) (Q : RankTwoAugmentedFrames.RationalLine2)
    {v : RankTwoAugmentedFrames.Space} (hv : Submodule.span ℚ {v} = Q.val) :
    (sectionVertex g Q).val = Submodule.span ℚ {lift g v} := by
  change Q.val.map (lift g) = _
  rw [← hv,Submodule.map_span,Set.image_singleton]

theorem section_quotientLine (g : IntegralGL) (p : Pair) (hp : PairPrimitive p) :
    sectionVertex g (quotientLine p hp) = chart g p hp 0 := by
  apply Subtype.ext
  rw [section_span g _ (v := RankTwoAugmentedFrames.rationalVector p) rfl]
  rfl

theorem section_ne_base (g : IntegralGL) (Q : RankTwoAugmentedFrames.RationalLine2) :
    sectionVertex g Q ≠ augmentedLine g 0 := by
  obtain ⟨p,hp,rfl⟩ := quotientLine_exists_chart Q
  rw [section_quotientLine]
  exact chart_ne_base g p hp 0

@[simp] theorem vertex_section (g : IntegralGL) (Q : RankTwoAugmentedFrames.RationalLine2) :
    vertex g (sectionVertex g Q) = Q := by
  obtain ⟨p,hp,rfl⟩ := quotientLine_exists_chart Q
  rw [section_quotientLine,vertex_chart]

/-- Suspend an actual quotient basis, placing the distinguished vertex last. -/
def suspensionMatrix (q : RankTwoAugmentedFrames.IntegralGL) :
    Matrix (Fin 3) (Fin 3) ℤ := !![0,0,1;q.val 0 0,q.val 0 1,0;q.val 1 0,q.val 1 1,0]

theorem suspensionMatrix_det (q : RankTwoAugmentedFrames.IntegralGL) :
    (suspensionMatrix q).det = q.val.det := by
  simp [suspensionMatrix,Matrix.det_fin_three,Matrix.det_fin_two]

def suspensionGL (q : RankTwoAugmentedFrames.IntegralGL) : IntegralGL :=
  Matrix.nonsingInvUnit (suspensionMatrix q)
    (by rw [suspensionMatrix_det]; exact (Matrix.isUnit_iff_isUnit_det q.val).mp q.isUnit)

def suspensionIndex (i : Fin 3) : Fin 4 := ![0,1,3] i

theorem suspension_template (q : RankTwoAugmentedFrames.IntegralGL) (i : Fin 3) :
    rationalRepresentation (suspensionGL q) (template (suspensionIndex i)) =
      ![0,RankTwoAugmentedFrames.rationalRepresentation q (RankTwoAugmentedFrames.template i) 0,
        RankTwoAugmentedFrames.rationalRepresentation q (RankTwoAugmentedFrames.template i) 1] := by
  rw [rationalRepresentation_apply,RankTwoAugmentedFrames.rationalRepresentation_apply]
  change ((suspensionMatrix q).map (Int.castRingHom ℚ)).mulVec _ = _
  fin_cases i <;> funext r <;> fin_cases r <;>
    simp [suspensionMatrix,suspensionIndex,template,RankTwoAugmentedFrames.template,
      Matrix.mulVec,dotProduct,Fin.sum_univ_three,Fin.sum_univ_two]

theorem section_template (g : IntegralGL) (q : RankTwoAugmentedFrames.IntegralGL) (i : Fin 3) :
    sectionVertex g (RankTwoAugmentedFrames.augmentedLine q i) =
      augmentedLine (g * suspensionGL q) (suspensionIndex i) := by
  apply Subtype.ext
  rw [section_span g _ (v := RankTwoAugmentedFrames.rationalRepresentation q
    (RankTwoAugmentedFrames.template i)) rfl]
  change _ = Submodule.span ℚ {rationalRepresentation (g * suspensionGL q) _}
  rw [map_mul,LinearEquiv.mul_apply,suspension_template]
  rfl

theorem suspension_base (g : IntegralGL) (q : RankTwoAugmentedFrames.IntegralGL) :
    augmentedLine (g * suspensionGL q) 2 = augmentedLine g 0 := by
  apply BadEdgeNormalForm.augmentedLine_mul_of_template
  rw [rationalRepresentation_apply]
  change ((suspensionMatrix q).map (Int.castRingHom ℚ)).mulVec _ = _
  funext r
  fin_cases r <;> simp [suspensionMatrix,template,Matrix.mulVec,dotProduct,Fin.sum_univ_three]

/-- Every quotient face lifts, together with the fixed vertex, to one actual augmented frame. -/
theorem section_mapsFaces (g : IntegralGL) :
    OrientedChainMap.MapsFaces (sectionVertex g) RankTwoAugmentedFrames.ambient
      (link (augmentedLine g 0)) := by
  intro s hs
  obtain ⟨hne,q,hq⟩ := hs
  have hf : s.image (sectionVertex g) ∈ link (augmentedLine g 0) := by
    apply (mem_link _ _).mpr
    refine ⟨hne.image _,?_,?_⟩
    · apply subset_augmentedFrame_mem (g * suspensionGL q)
        (Finset.singleton_nonempty _ |>.mono Finset.subset_union_left)
      intro L hL
      rcases Finset.mem_union.mp hL with hL | hL
      · have he : L = augmentedLine g 0 := Finset.mem_singleton.mp hL
        exact Finset.mem_image.mpr ⟨2,Finset.mem_univ _,(suspension_base g q).trans he.symm⟩
      · obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp hL
        obtain ⟨i,_,hi⟩ := Finset.mem_image.mp (hq hQ)
        exact Finset.mem_image.mpr ⟨suspensionIndex i,Finset.mem_univ _,
          (section_template g q i).symm.trans (congrArg (sectionVertex g) hi)⟩
    · intro L hL
      obtain ⟨Q,_,rfl⟩ := Finset.mem_image.mp hL
      exact section_ne_base g Q
  convert hf using 1
  ext L
  simp only [Finset.mem_image]

end TernaryPoly.AmbientRelativeProjection
