module

public import TernaryPeriodPolynomials.Building.Ambient.RelativeFibers
public import TernaryPeriodPolynomials.Building.BadVertex.SimplexNormalForm
public import TernaryPeriodPolynomials.Building.BadVertex.MixedCharts

@[expose] public section


noncomputable section
namespace TernaryPoly.AmbientRelativeNormalForm
open ModThreeGoodAction AugmentedFrameComplex BadVertexProjection BadVertexFibers
open AmbientRelativeProjection AmbientRelativeFibers CoherentPrismReduction
open BadVertexSimplexNormalForm BadVertexMixedCharts

/-- A fixed quotient fiber remains fixed under every change of adapted integral frame. -/
theorem projected_fiber_constant (g h : IntegralGL)
    (hh : augmentedLine h 0 = augmentedLine g 0) (i : Fin 3) (k l : ℤ) :
    vertex g (fiberLine h i k) = vertex g (fiberLine h i l) := by
  have hn (n : ℤ) : fiberLine h i n ≠ augmentedLine g 0 := by
    rw [← hh,prism_fiber_eq_chart]
    exact chart_ne_base _ _ _ _
  apply Subtype.ext
  rw [vertex_span g _ (hn k) (v := rationalRepresentation h
      (rationalVector (fiberCoefficient i k))) rfl,
    vertex_span g _ (hn l) (v := rationalRepresentation h
      (rationalVector (fiberCoefficient i l))) rfl,
    projection_representation g h hh,projection_representation g h hh]
  congr 2
  funext r
  fin_cases i <;> fin_cases r <;> rfl

/-- Changes of actual adapted charts act by an integral translation and a sign. -/
theorem fiber_chart_transition (g h : IntegralGL)
    (hh : augmentedLine h 0 = augmentedLine g 0) (i : Fin 3)
    (p : Pair) (hp : PairPrimitive p)
    (hq : vertex g (fiberLine h i 0) = quotientLine p hp) :
    ∃ a δ : ℤ, Sign δ ∧ ∀ k, fiberLine h i k = chart g p hp (a+δ*k) := by
  have hn : fiberLine h i 0 ≠ augmentedLine g 0 := by
    rw [← hh,prism_fiber_eq_chart]
    exact chart_ne_base _ _ _ _
  have he : {augmentedLine g 0,fiberLine h i 0} ∈ ambient := by
    rw [← hh,prism_fiber_eq_chart]
    exact chart_ambient_edge _ _ _ _
  obtain ⟨a,ha⟩ := exists_chart g p hp _ hn he hq
  obtain ⟨ε,hε,hcol⟩ := first_column_sign g h hh
  have hs : Submodule.span ℚ {rationalVector (h.val.mulVec (fiberCoefficient i 0))} =
      Submodule.span ℚ {rationalVector (g.val.mulVec (coordinateVector p a))} := by
    rw [← fiberLine_val,← chart_val g p hp a]
    exact congrArg Subtype.val ha.symm
  obtain ⟨η,hη,horg⟩ := primitive_span_sign (fiberVector_primitive h i 0)
    (GoodAugmentedNormalForm.primitive_mulVec g (coordinateVector_primitive p hp a)) hs
  refine ⟨a,η*ε,sign_mul hη hε,?_⟩
  intro k
  have hv : h.val.mulVec (fiberCoefficient i k) =
      η • g.val.mulVec (coordinateVector p (a+(η*ε)*k)) := by
    rw [fiberVector_affine,horg,hcol,chart_vector_affine g p a,
      chart_vector_affine g p (a+(η*ε)*k)]
    rcases hε with rfl | rfl <;> rcases hη with rfl | rfl <;>
      funext r <;> simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul] <;> ring
  apply Subtype.ext
  rw [fiberLine_val,chart_val,hv]
  have hc (v : IntegralVector) : rationalVector (η • v) = (η : ℚ) • rationalVector v := by
    funext r
    simp [rationalVector,Pi.smul_apply,smul_eq_mul]
  rw [hc,Submodule.span_singleton_smul_eq]
  rcases hη with rfl | rfl <;> norm_num

/-- Equal projected template slots lie at equal or neighboring fiber coordinates. -/
theorem normal_heights_close : ∀ i j k,
    normalFiber i j = normalFiber i k →
      (normalHeight i j-normalHeight i k).natAbs ≤ 1 := by
  decide +kernel

/-- Every actual link edge has an adapted literal template chart. -/
theorem edge_template (g : IntegralGL) (L M : RationalLine)
    (he : {L,M} ∈ link (augmentedLine g 0)) :
    ∃ h : IntegralGL, ∃ i : Fin 4, ∃ j k : Fin 3,
      augmentedLine h i = augmentedLine g 0 ∧
      L = augmentedLine h (remainingIndex i j) ∧
      M = augmentedLine h (remainingIndex i k) := by
  obtain ⟨_,hf,ha⟩ := (mem_link _ _).mp he
  obtain ⟨_,h,hh⟩ := hf
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp
    (hh (Finset.mem_union_left _ (Finset.mem_singleton_self _)))
  obtain ⟨a,_,haL⟩ := Finset.mem_image.mp (hh (show L ∈ {augmentedLine g 0} ∪ {L,M} by simp))
  obtain ⟨b,_,hbM⟩ := Finset.mem_image.mp (hh (show M ∈ {augmentedLine g 0} ∪ {L,M} by simp))
  have hai : a ≠ i := by
    intro hei
    exact ha L (by simp) (haL.symm.trans ((congrArg (augmentedLine h) hei).trans hi))
  have hbi : b ≠ i := by
    intro hei
    exact ha M (by simp) (hbM.symm.trans ((congrArg (augmentedLine h) hei).trans hi))
  obtain ⟨j,hj⟩ := (remainingIndex_range i a).mpr hai
  obtain ⟨k,hk⟩ := (remainingIndex_range i b).mpr hbi
  exact ⟨h,i,j,k,hi,by rw [hj,haL],by rw [hk,hbM]⟩

/-- An actual link edge in one quotient fiber is an actual consecutive integer-path edge. -/
theorem same_fiber_adjacent (g : IntegralGL) (p : Pair) (hp : PairPrimitive p) (a b : ℤ)
    (he : {chart g p hp a,chart g p hp b} ∈ link (augmentedLine g 0)) :
    (a-b).natAbs ≤ 1 := by
  obtain ⟨h,i,j,k,hi,hL,hM⟩ := edge_template g _ _ he
  have hij : i ≠ remainingIndex i j :=
    Ne.symm ((remainingIndex_range i _).mp ⟨j,rfl⟩)
  have hik : i ≠ remainingIndex i k :=
    Ne.symm ((remainingIndex_range i _).mp ⟨k,rfl⟩)
  have hfjk : normalFiber i j = normalFiber i k := by
    have hproj : vertex g (augmentedLine h (remainingIndex i j)) =
        vertex g (augmentedLine h (remainingIndex i k)) := by
      rw [← hL,← hM,vertex_chart,vertex_chart]
    rw [vertex_template g h i _ hi hij,vertex_template g h i _ hi hik,
      normal_projected_index,normal_projected_index] at hproj
    exact RankTwoAugmentedFrames.augmentedLine_injective _ hproj
  let h' := h * templateChange i
  have hh' : augmentedLine h' 0 = augmentedLine g 0 := (templateChange_line h i).trans hi
  have hq : vertex g (fiberLine h' (normalFiber i j) 0) = quotientLine p hp := by
    rw [projected_fiber_constant g h' hh' _ 0 (normalHeight i j),normal_line,← hL,vertex_chart]
  obtain ⟨c,δ,hδ,htrans⟩ := fiber_chart_transition g h' hh' (normalFiber i j) p hp hq
  have ha : a = c+δ*normalHeight i j := by
    apply chart_injective g p hp
    rw [← htrans,normal_line,← hL]
  have hb : b = c+δ*normalHeight i k := by
    apply chart_injective g p hp
    rw [← htrans,hfjk,normal_line,← hM]
  have hc := normal_heights_close i j k hfjk
  rw [ha,hb]
  rcases hδ with rfl | rfl
  · simpa using hc
  · have hz : c + -1 * normalHeight i j - (c + -1 * normalHeight i k) =
        -(normalHeight i j-normalHeight i k) := by ring
    simpa only [hz,Int.natAbs_neg] using hc

end TernaryPoly.AmbientRelativeNormalForm
