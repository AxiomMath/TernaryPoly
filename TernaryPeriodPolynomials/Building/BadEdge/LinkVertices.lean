module

public import TernaryPeriodPolynomials.Building.Ambient.IndependentTriple

@[expose] public section


open scoped BigOperators
noncomputable section
namespace TernaryPoly.BadEdgeLinkVertices
open ModThreeGoodAction GoodIntegralNormalization PrimitiveLineUniqueness
open GoodAugmentedNormalForm AugmentedFrameComplex AugmentedBadFaces
open AmbientIndependentTriple

/-- Integer affine coordinates for vertices above a fixed rank-two direct summand. -/
def affineVector (p : ℤ × ℤ) : IntegralVector := ![p.1,p.2,1]

theorem affineVector_primitive (p : ℤ × ℤ) : Primitive (affineVector p) := by
  simp [Primitive,content,affineVector]

/-- The rational line of the actual vector g(m,n,1). -/
def coordinateLine (g : IntegralGL) (p : ℤ × ℤ) : RationalLine :=
  vectorLine (rationalVector (g.val.mulVec (affineVector p)))
    (rationalVector_ne_zero_of_primitive (primitive_mulVec g (affineVector_primitive p)))

/-- A genuine Good vertex in the ambient link of the first two column lines. -/
abbrev GoodLinkVertex (g : IntegralGL) :=
  {L : RationalLine // Good L.val ∧ {augmentedLine g 0,augmentedLine g 1,L} ∈ ambient}

/-- Coordinate-sum residue in an arbitrary integral basis. -/
theorem residue_mulVec (g : IntegralGL) (a : IntegralVector) :
    (∑ i, (g.val.mulVec a i : ZMod 3)) =
      ∑ j, columnResidue g j * (a j : ZMod 3) := by
  have h := Matrix.dotProduct_mulVec fixedRow (reduction g).val (residueVector a)
  rw [← residueVector_mulVec] at h
  simpa [dotProduct,fixedRow,residueVector,columnResidue,Matrix.vecMul,
    reduction,Matrix.GeneralLinearGroup.map_apply] using h

/-- For a bad coordinate edge, only the final coordinate contributes to goodness. -/
theorem residue_mulVec_bad_edge (g : IntegralGL)
    (h0 : columnResidue g 0 = 0) (h1 : columnResidue g 1 = 0)
    (a : IntegralVector) :
    (∑ i, (g.val.mulVec a i : ZMod 3)) = columnResidue g 2 * (a 2 : ZMod 3) := by
  rw [residue_mulVec,Fin.sum_univ_three,h0,h1]
  simp

/-- Each integer affine coordinate gives an explicit Good lattice witness. -/
theorem coordinateLine_good (g : IntegralGL)
    (h0 : columnResidue g 0 = 0) (h1 : columnResidue g 1 = 0)
    (h2 : columnResidue g 2 ≠ 0) (p : ℤ × ℤ) : Good (coordinateLine g p).val := by
  refine ⟨g.val.mulVec (affineVector p),Submodule.mem_span_singleton_self _,?_⟩
  simpa [residue_mulVec_bad_edge g h0 h1,affineVector] using h2

/-- Replace the last column of the coordinate identity by an arbitrary integral vector. -/
def coordinateMatrix (a : IntegralVector) : IntegralMatrix :=
  !![1,0,a 0;0,1,a 1;0,0,a 2]

/-- The actual three-column matrix formed from g's first two columns and ga. -/
def completionMatrix (g : IntegralGL) (a : IntegralVector) : IntegralMatrix :=
  g.val * coordinateMatrix a

theorem coordinateMatrix_det (a : IntegralVector) : (coordinateMatrix a).det = a 2 := by
  simp [coordinateMatrix,Matrix.det_fin_three]

theorem completionMatrix_det (g : IntegralGL) (a : IntegralVector) :
    (completionMatrix g a).det = g.val.det * a 2 := by
  rw [completionMatrix,Matrix.det_mul,coordinateMatrix_det]

theorem completionMatrix_col_zero (g : IntegralGL) (a : IntegralVector) :
    (completionMatrix g a).col 0 = g.val.col 0 := by
  ext i
  simp [completionMatrix,coordinateMatrix,Matrix.col,Matrix.mul_apply,Fin.sum_univ_three]

theorem completionMatrix_col_one (g : IntegralGL) (a : IntegralVector) :
    (completionMatrix g a).col 1 = g.val.col 1 := by
  ext i
  simp [completionMatrix,coordinateMatrix,Matrix.col,Matrix.mul_apply,Fin.sum_univ_three]

theorem completionMatrix_col_two (g : IntegralGL) (a : IntegralVector) :
    (completionMatrix g a).col 2 = g.val.mulVec a := by
  ext i
  simp [completionMatrix,coordinateMatrix,Matrix.col,Matrix.mul_apply,Matrix.mulVec,
    dotProduct,Fin.sum_univ_three]

/-- Integral affine points produce genuine invertible integer completion matrices. -/
def affineCompletion (g : IntegralGL) (p : ℤ × ℤ) : IntegralGL :=
  Matrix.nonsingInvUnit (completionMatrix g (affineVector p)) (by
    rw [completionMatrix_det]
    simp only [affineVector,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,mul_one]
    exact (Matrix.isUnit_iff_isUnit_det g.val).mp g.isUnit)

theorem affineCompletion_line_zero (g : IntegralGL) (p : ℤ × ℤ) :
    augmentedLine (affineCompletion g p) 0 = augmentedLine g 0 := by
  apply Subtype.ext
  change Submodule.span ℚ {rationalRepresentation (affineCompletion g p) (Pi.single 0 1)} =
    Submodule.span ℚ {rationalRepresentation g (Pi.single 0 1)}
  rw [rationalRepresentation_basis,rationalRepresentation_basis]
  exact congrArg (fun v => Submodule.span ℚ {rationalVector v})
    (completionMatrix_col_zero g (affineVector p))

theorem affineCompletion_line_one (g : IntegralGL) (p : ℤ × ℤ) :
    augmentedLine (affineCompletion g p) 1 = augmentedLine g 1 := by
  apply Subtype.ext
  change Submodule.span ℚ {rationalRepresentation (affineCompletion g p) (Pi.single 1 1)} =
    Submodule.span ℚ {rationalRepresentation g (Pi.single 1 1)}
  rw [rationalRepresentation_basis,rationalRepresentation_basis]
  exact congrArg (fun v => Submodule.span ℚ {rationalVector v})
    (completionMatrix_col_one g (affineVector p))

theorem affineCompletion_line_two (g : IntegralGL) (p : ℤ × ℤ) :
    augmentedLine (affineCompletion g p) 2 = coordinateLine g p := by
  apply Subtype.ext
  change Submodule.span ℚ {rationalRepresentation (affineCompletion g p) (Pi.single 2 1)} = _
  rw [rationalRepresentation_basis]
  exact congrArg (fun v => Submodule.span ℚ {rationalVector v})
    (completionMatrix_col_two g (affineVector p))

/-- Every affine coordinate makes an actual basis triangle in the ambient complex. -/
theorem coordinateLine_face (g : IntegralGL) (p : ℤ × ℤ) :
    {augmentedLine g 0,augmentedLine g 1,coordinateLine g p} ∈ ambient := by
  classical
  apply subset_augmentedFrame_mem (affineCompletion g p) (by simp)
  intro L hL
  simp only [Finset.mem_insert,Finset.mem_singleton] at hL
  rcases hL with rfl | rfl | rfl
  · exact Finset.mem_image.mpr ⟨0,Finset.mem_univ _,affineCompletion_line_zero g p⟩
  · exact Finset.mem_image.mpr ⟨1,Finset.mem_univ _,affineCompletion_line_one g p⟩
  · exact Finset.mem_image.mpr ⟨2,Finset.mem_univ _,affineCompletion_line_two g p⟩

/-- The columns of a genuine integral basis are primitive, whether Good or bad. -/
theorem basis_column_primitive (g : IntegralGL) (j : Fin 3) : Primitive (g.val.col j) := by
  have h := primitive_mulVec g (integralTemplate_primitive j.castSucc)
  fin_cases j <;> simpa [integralTemplate] using h

/-- The finite image of an ordered triple is its literal three-vertex set. -/
theorem image_three (a b c : RationalLine) :
    Finset.univ.image (![a,b,c] : Fin 3 → RationalLine) = {a,b,c} := by
  classical
  rw [show (Finset.univ : Finset (Fin 3)) = {0,1,2} by decide]
  simp

/-- A primitive generator of a Good link vertex has unit last inverse coordinate. -/
theorem inverse_third_isUnit (g : IntegralGL)
    (h0 : columnResidue g 0 = 0) (h1 : columnResidue g 1 = 0)
    (L : RationalLine) (hgood : Good L.val)
    (hface : {augmentedLine g 0,augmentedLine g 1,L} ∈ ambient)
    (v : IntegralVector) (hp : Primitive v)
    (hs : Submodule.span ℚ {rationalVector v} = L.val) :
    IsUnit ((g⁻¹.val.mulVec v) 2) := by
  let a : IntegralVector := g⁻¹.val.mulVec v
  have hga : g.val.mulVec a = v := by
    dsimp [a]
    rw [Matrix.mulVec_mulVec,← Units.val_mul,mul_inv_cancel,Units.val_one,Matrix.one_mulVec]
  have hres : (∑ i, (v i : ZMod 3)) ≠ 0 := by
    apply (good_span_iff_residue hp).mp
    rwa [hs]
  have ha2 : a 2 ≠ 0 := by
    intro hz
    apply hres
    rw [← hga,residue_mulVec_bad_edge g h0 h1,hz,Int.cast_zero,mul_zero]
  have hprim (j : Fin 3) : Primitive ((completionMatrix g a).col j) := by
    fin_cases j
    · change Primitive ((completionMatrix g a).col 0)
      rw [completionMatrix_col_zero g a]
      exact basis_column_primitive g 0
    · change Primitive ((completionMatrix g a).col 1)
      rw [completionMatrix_col_one g a]
      exact basis_column_primitive g 1
    · change Primitive ((completionMatrix g a).col 2)
      rw [completionMatrix_col_two g a,hga]
      exact hp
  have hlines (j : Fin 3) :
      Submodule.span ℚ {rationalVector ((completionMatrix g a).col j)} =
        ((![augmentedLine g 0,augmentedLine g 1,L] : Fin 3 → RationalLine) j).val := by
    fin_cases j
    · change Submodule.span ℚ {rationalVector ((completionMatrix g a).col 0)} =
        Submodule.span ℚ {rationalRepresentation g (Pi.single 0 1)}
      rw [completionMatrix_col_zero g a]
      rw [rationalRepresentation_basis]
      rfl
    · change Submodule.span ℚ {rationalVector ((completionMatrix g a).col 1)} =
        Submodule.span ℚ {rationalRepresentation g (Pi.single 1 1)}
      rw [completionMatrix_col_one g a]
      rw [rationalRepresentation_basis]
      rfl
    · change Submodule.span ℚ {rationalVector ((completionMatrix g a).col 2)} = L.val
      rw [completionMatrix_col_two g a,hga]
      exact hs
  have hd : (completionMatrix g a).det.natAbs = 1 :=
    det_natAbs_eq_one_of_ambient (completionMatrix g a) hprim
      (by rw [completionMatrix_det]; exact mul_ne_zero g.det_ne_zero ha2)
      ![augmentedLine g 0,augmentedLine g 1,L] hlines (by rwa [image_three])
  have hgdet : g.val.det.natAbs = 1 := Int.isUnit_iff_natAbs_eq.mp
    ((Matrix.isUnit_iff_isUnit_det g.val).mp g.isUnit)
  rw [completionMatrix_det,Int.natAbs_mul,hgdet,one_mul] at hd
  exact Int.isUnit_iff_natAbs_eq.mpr hd

/-- Every actual Good vertex in the bad-edge link has integral affine coordinates. -/
theorem exists_coordinates (g : IntegralGL)
    (h0 : columnResidue g 0 = 0) (h1 : columnResidue g 1 = 0)
    (L : RationalLine) (hgood : Good L.val)
    (hface : {augmentedLine g 0,augmentedLine g 1,L} ∈ ambient) :
    ∃ p : ℤ × ℤ, coordinateLine g p = L := by
  obtain ⟨v,hp,_,hs⟩ := RationalLineBasis.rationalLine_primitive_generator L
  let a : IntegralVector := g⁻¹.val.mulVec v
  have hga : g.val.mulVec a = v := by
    dsimp [a]
    rw [Matrix.mulVec_mulVec,← Units.val_mul,mul_inv_cancel,Units.val_one,Matrix.one_mulVec]
  have hu : IsUnit (a 2) := inverse_third_isUnit g h0 h1 L hgood hface v hp hs
  rcases Int.isUnit_iff.mp hu with ha | ha
  · refine ⟨(a 0,a 1),?_⟩
    apply Subtype.ext
    change Submodule.span ℚ {rationalVector (g.val.mulVec (affineVector (a 0,a 1)))} = L.val
    have he : affineVector (a 0,a 1) = a := by
      ext i
      fin_cases i <;> simp [affineVector,ha]
    rw [he,hga,hs]
  · refine ⟨(-a 0,-a 1),?_⟩
    apply Subtype.ext
    change Submodule.span ℚ {rationalVector (g.val.mulVec (affineVector (-a 0,-a 1)))} = L.val
    have he : affineVector (-a 0,-a 1) = -a := by
      ext i
      fin_cases i <;> simp [affineVector,ha]
    rw [he,Matrix.mulVec_neg,hga,rationalVector_neg]
    rw [show -rationalVector v = (-1 : ℚ) • rationalVector v by simp,
      Submodule.span_singleton_smul_eq (by norm_num : IsUnit (-1 : ℚ)),hs]

/-- The last affine coordinate one makes rational line coordinates unique. -/
theorem coordinateLine_injective (g : IntegralGL) : Function.Injective (coordinateLine g) := by
  intro p q he
  have hm : rationalVector (g.val.mulVec (affineVector p)) ∈
      Submodule.span ℚ {rationalVector (g.val.mulVec (affineVector q))} := by
    change rationalVector (g.val.mulVec (affineVector p)) ∈ (coordinateLine g q).val
    rw [← he]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨t,ht⟩ := Submodule.mem_span_singleton.mp hm
  rw [rationalVector_mulVec,rationalVector_mulVec] at ht
  have ha : t • rationalVector (affineVector q) = rationalVector (affineVector p) := by
    apply (rationalRepresentation g).injective
    rw [map_smul]
    exact ht
  have ht1 : t = 1 := by
    have h := congrFun ha 2
    simpa [rationalVector,affineVector] using h
  rw [ht1,one_smul] at ha
  apply Prod.ext
  · have h := congrFun ha 0
    change (q.1 : ℚ) = (p.1 : ℚ) at h
    exact_mod_cast h.symm
  · have h := congrFun ha 1
    change (q.2 : ℚ) = (p.2 : ℚ) at h
    exact_mod_cast h.symm

/-- Exhaustive unique-coordinate classification of the actual Good vertex set. -/
theorem existsUnique_coordinates (g : IntegralGL)
    (h0 : columnResidue g 0 = 0) (h1 : columnResidue g 1 = 0)
    (L : RationalLine) (hgood : Good L.val)
    (hface : {augmentedLine g 0,augmentedLine g 1,L} ∈ ambient) :
    ∃! p : ℤ × ℤ, coordinateLine g p = L := by
  obtain ⟨p,hp⟩ := exists_coordinates g h0 h1 L hgood hface
  exact ⟨p,hp,fun q hq => coordinateLine_injective g (hq.trans hp.symm)⟩

/-- The actual coordinate map into Good link vertices. -/
def coordinateVertex (g : IntegralGL)
    (h0 : columnResidue g 0 = 0) (h1 : columnResidue g 1 = 0)
    (h2 : columnResidue g 2 ≠ 0) (p : ℤ × ℤ) : GoodLinkVertex g :=
  ⟨coordinateLine g p,coordinateLine_good g h0 h1 h2 p,coordinateLine_face g p⟩

/-- Integer pairs classify all actual Good vertices in the bad-edge link. -/
def goodLinkVertexEquiv (g : IntegralGL)
    (h0 : columnResidue g 0 = 0) (h1 : columnResidue g 1 = 0)
    (h2 : columnResidue g 2 ≠ 0) : (ℤ × ℤ) ≃ GoodLinkVertex g :=
  Equiv.ofBijective (coordinateVertex g h0 h1 h2) ⟨
    fun _ _ he => coordinateLine_injective g (congrArg Subtype.val he),
    fun L => by
      obtain ⟨p,hp⟩ := exists_coordinates g h0 h1 L.val L.property.1 L.property.2
      exact ⟨p,Subtype.ext hp⟩⟩

@[simp] theorem goodLinkVertexEquiv_apply_val (g : IntegralGL)
    (h0 : columnResidue g 0 = 0) (h1 : columnResidue g 1 = 0)
    (h2 : columnResidue g 2 ≠ 0) (p : ℤ × ℤ) :
    (goodLinkVertexEquiv g h0 h1 h2 p).val = coordinateLine g p := rfl

end TernaryPoly.BadEdgeLinkVertices
