module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Retract.Cell0Geometry
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Retract.CellChains
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Retract.CellSpace
public import TernaryPeriodPolynomials.SymmetricSpace.Flag.CoordinatesCorner
public import TernaryPeriodPolynomials.Topology.Euclidean.Local.Homology
public import TernaryPeriodPolynomials.Topology.Rational.SingularAugmentation
public import TernaryPeriodPolynomials.Topology.Singular.CoverNaturalityChains
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.FlatAffine

@[expose] public section


/-!
# Local degree along the unipotent projection

The flat `{diag(a,b,(ab)⁻¹)}` is the zero locus of the unipotent coordinates `unip : Space → ℝ³`
of the Borel corner chart of the identity frame. A 3-chain of the symmetric space whose boundary
avoids the flat has a **local degree** `degπ c ∈ ℚ`: the class of `π_* c` in the local homology
`H₃(ℝ³, ℝ³ ∖ 0) ≅ ℚ`. (This is not a class in the zero group `H₃(Glued, Glued ∖ pt)`: it is the
normal-projection degree, the 3-dimensional local intersection number with the flat.)

* `unip_eq_zero_iff`: `unip S = 0` iff the form `S` is diagonal.
* `locRel`, `degπ`, `degπ_add`, `degπ_eq_of_sub` (homotopy/boundary invariance), `locRel_sing_zero`
  (simplices off the flat are null in the relative chains).
* `realizeVia`, `d_realizeVia`: realization of formal affine chains of positive definite forms through
  any continuous map (used for `Space` and for the projection).
* `locRel_cellAtSpace_zero`: every cell chain `cellAtSpace n D` with `D ≠ T₀` is invisible to the
  projection (its reach contains no diagonal form, `flat_reach`); `cycle_T0` the boundary of the
  standard top cell chain is invisible too, so `dT0 := degπ (cellAtSpace 3 T₀)` is defined.

Formalized by Claude Sonnet 5.5.
-/

open TernaryPoly TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceFlagCoordinates
  TernaryPoly.SymmetricSpaceParabolicCoordinates
open CategoryTheory Limits HomologicalComplex TernaryPoly.ContractibleSingularHomology
  TernaryPoly.RationalRelativeSingular TernaryPoly.EuclideanLocalHomology TernaryPoly.RationalSphere
  TernaryPoly.FreeActionLinearization

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Lemma33.Retract.LocalDegree

/-- The unipotent coordinates `(x, y, z)` of a point of the symmetric space in the Borel corner
chart of the identity frame. -/
def unip (S : Space) : Fin 3 → ℝ := (ldlHomeomorph S).1

theorem continuous_unip : Continuous unip :=
  (continuous_fst.comp ldlHomeomorph.continuous)

/-- The diagonal flat is the zero locus of the unipotent coordinates. -/
theorem unip_eq_zero_iff (S : Space) : unip S = 0 ↔ ∀ i j, i ≠ j → S.val i j = 0 := by
  constructor
  · intro h i j hij
    have hS : S = ldlHomeomorph.symm (ldlHomeomorph S) := (ldlHomeomorph.symm_apply_apply S).symm
    have hv := congrArg Subtype.val hS
    rw [ldlHomeomorph_symm] at hv
    have h0 : (ldlHomeomorph S).1 = 0 := h
    rw [hv]
    simp only [h0, Pi.zero_apply]
    change ((_ : ℝ)⁻¹ • flagMatrix 0 0 0 _ _) i j = 0
    have : upper 0 0 0 = 1 := by
      ext a b
      fin_cases a <;> fin_cases b <;> simp [upper]
    simp [flagMatrix, this, SymmetricSpaceFlagCoordinates.diagonal, hij]
  · intro h
    have e : ∀ i : Fin 2, unipotent S.val i = 0 := by
      intro i
      fin_cases i <;> simp [unipotent, topIndex, h]
    funext i
    unfold unip
    rw [ldlHomeomorph_unipotent]
    fin_cases i <;> simp [binaryX, schur, topIndex, e, h]

/-- The unipotent coordinates as a map into three-dimensional Euclidean space. -/
def piR3 : C(Space, EuclideanSpace ℝ (Fin 3)) :=
  ⟨fun S => (EuclideanSpace.equiv (Fin 3) ℝ).symm (unip S),
    (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous.comp continuous_unip⟩

/-- Singular chains of the symmetric space, projected to local chains of `ℝ³` at the origin. -/
def locRel : chains Space ⟶ localChains 3 :=
  TernaryPoly.RationalSingularAugmentation.chainMap piR3 ≫ cokernel.π (inclusion (Punctured 3))

/-- The **local degree** along the unipotent projection of a singular 3-chain of the symmetric
space whose boundary misses the flat `{unip = 0}`: the class of `π_* c` in the local homology
`H₃(ℝ³, ℝ³ ∖ 0) ≅ ℚ`. -/
def degπ (c : (chains Space).X 3)
    (h : ((localChains 3).d 3 2).hom ((locRel.f 3).hom c) = 0) : ℚ :=
  (localTopIso 1).hom.hom ((localChains 3).homologyπ 3 ((localChains 3).cyclesMk _ 2
      ((ComplexShape.down ℕ).next_eq' (show (ComplexShape.down ℕ).Rel 3 2 from rfl)) h))

open TernaryPeriodPolynomials.Argument.Lemma33 in
theorem locRel_sing_zero {n : ℕ} (σ : SingularSimplex (TopCat.of Space) n)
    (h : ∀ t, unip ((TopCat.of Space).toSSetObjEquiv _ σ t) ≠ 0) :
    (locRel.f n).hom (sing (TopCat.of Space) σ) = 0 := by
  let σ'' : SingularSimplex (TopCat.of (Punctured 3)) n :=
    ((TopCat.of (Punctured 3)).toSSetObjEquiv _).symm
      ⟨fun t => ⟨piR3 ((TopCat.of Space).toSSetObjEquiv _ σ t), by
        intro h0
        apply h t
        have : (EuclideanSpace.equiv (Fin 3) ℝ).symm (unip ((TopCat.of Space).toSSetObjEquiv _ σ t)) = 0 := h0
        simpa using this⟩,
        by
          refine Continuous.subtype_mk ?_ _
          exact piR3.continuous.comp ((TopCat.of Space).toSSetObjEquiv _ σ).continuous⟩
  have h1 : (TernaryPoly.RationalSingularAugmentation.chainMap piR3).f n =
      (TernaryPoly.SingularCoverNaturality.underlyingMap (TopCat.ofHom piR3)).f n := rfl
  have h2 : (inclusion (Punctured 3)).f n =
      (TernaryPoly.SingularCoverNaturality.underlyingMap
        (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of (Punctured 3) ⟶
          TopCat.of (EuclideanSpace ℝ (Fin 3)))).f n := rfl
  have hg1 := congrArg (fun m => m.hom (1 : ℚ))
    (TernaryPoly.SingularCoverNaturality.generator_map (TopCat.ofHom piR3) n σ)
  have hg2 := congrArg (fun m => m.hom (1 : ℚ))
    (TernaryPoly.SingularCoverNaturality.generator_map
      (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of (Punctured 3) ⟶
        TopCat.of (EuclideanSpace ℝ (Fin 3))) n σ'')
  have hs : (TopCat.toSSet.map (TopCat.ofHom piR3)).app _ σ =
      (TopCat.toSSet.map (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
        TopCat.of (Punctured 3) ⟶ TopCat.of (EuclideanSpace ℝ (Fin 3)))).app _ σ'' := by
    apply ((TopCat.of (EuclideanSpace ℝ (Fin 3))).toSSetObjEquiv _).injective
    exact ContinuousMap.ext (fun t => rfl)
  rw [hs] at hg1
  change (cokernel.π (inclusion (Punctured 3))).f n (((TernaryPoly.RationalSingularAugmentation.chainMap piR3).f n).hom
    (sing (TopCat.of Space) σ)) = 0
  have e1 : ((TernaryPoly.RationalSingularAugmentation.chainMap piR3).f n).hom (sing (TopCat.of Space) σ) =
      ((inclusion (Punctured 3)).f n).hom (sing (TopCat.of (Punctured 3)) σ'') := hg1.trans hg2.symm
  rw [e1]
  have := congrArg (fun m => m.hom (sing (TopCat.of (Punctured 3)) σ'')) (congrArg (fun m => m.f n) (cokernel.condition (inclusion (Punctured 3))))
  exact this

open TernaryPeriodPolynomials.Argument.Lemma33 TernaryPeriodPolynomials.Argument.Lemma33.Retract
  TernaryPeriodPolynomials.Argument.Lemma33.Retract.Cell0Geometry Finsupp
  TernaryPeriodPolynomials.FreeResolution

/-! ### Realization of formal affine chains through an arbitrary continuous map -/

/-- The singular simplex `f ∘ (affine simplex of forms)`. -/
def affVia {Y : Type} [TopologicalSpace Y] (f : C(PDMat, Y)) {n : ℕ} (y : AffSimp PDMat n) :
    SingularSimplex (TopCat.of Y) n :=
  ((TopCat.of Y).toSSetObjEquiv _).symm (f.comp (affMap n y))

theorem affVia_face {Y : Type} [TopologicalSpace Y] (f : C(PDMat, Y)) {n : ℕ}
    (y : AffSimp PDMat (n + 1)) (j : Fin (n + 2)) :
    (TopCat.toSSet.obj (TopCat.of Y)).δ j (affVia f y) = affVia f (AffSimp.face j y) := by
  apply ((TopCat.of Y).toSSetObjEquiv _).injective
  refine ContinuousMap.ext (fun z => ?_)
  rw [TopCat.toSSetObjEquiv_δ_apply]
  simp only [affVia, Equiv.apply_symm_apply]
  change f (affMap (n + 1) y (Convexity.StdSimplex.map j.succAbove z)) = f (affMap n (AffSimp.face j y) z)
  congr 1
  apply Subtype.ext
  rw [affMap_val, affMap_val]
  exact sum_stdSimplex_map_mat j.succAbove z (fun i => (y i).1)

/-- Realization of formal affine chains through `f`. -/
def realizeVia {Y : Type} [TopologicalSpace Y] (f : C(PDMat, Y)) (n : ℕ) :
    AffChain PDMat n →ₗ[ℚ] (chains Y).X n :=
  linearCombination ℚ (fun y => sing (TopCat.of Y) (affVia f y))

theorem realizeVia_single {Y : Type} [TopologicalSpace Y] (f : C(PDMat, Y)) {n : ℕ}
    (y : AffSimp PDMat n) (a : ℚ) :
    realizeVia f n (single y a) = a • sing (TopCat.of Y) (affVia f y) := by
  simp [realizeVia]

theorem d_realizeVia {Y : Type} [TopologicalSpace Y] (f : C(PDMat, Y)) (n : ℕ)
    (c : AffChain PDMat (n + 1)) :
    ((chains Y).d (n + 1) n).hom (realizeVia f (n + 1) c) = realizeVia f n (dAff PDMat n c) := by
  have h : ((chains Y).d (n + 1) n).hom ∘ₗ realizeVia f (n + 1) =
      realizeVia f n ∘ₗ dAff PDMat n := by
    apply Finsupp.lhom_ext
    intro y a
    have e : single y a = a • single y (1 : ℚ) := by simp
    rw [e]
    simp only [LinearMap.comp_apply, map_smul]
    congr 1
    rw [realizeVia_single, one_smul, d_sing, dAff_single, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, realizeVia_single, one_smul, affVia_face, ← Int.cast_smul_eq_zsmul ℚ]
    simp
  exact LinearMap.congr_fun h c

theorem realizeS_eq_via (n : ℕ) : realizeS n = realizeVia nuSp n := by
  apply Finsupp.lhom_ext
  intro y a
  rfl

theorem affVia_apply {Y : Type} [TopologicalSpace Y] (f : C(PDMat, Y)) {n : ℕ} (y : AffSimp PDMat n)
    (t : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    (TopCat.of Y).toSSetObjEquiv _ (affVia f y) t = f (affMap n y t) := by
  simp [affVia]

theorem isDiagMat_of_unip_nuSpace (M : PDMat) (h : unip (nuSpace M) = 0) : IsDiagMat M.1 := by
  have hoff := (unip_eq_zero_iff (nuSpace M)).mp h
  have hdet : IsUnit M.1.det := (Matrix.isUnit_iff_isUnit_det _).mp M.2.isUnit
  have htr : (M.1⁻¹).trace ≠ 0 := M.2.inv.trace_pos.ne'
  have hinv : IsDiagMat M.1⁻¹ := by
    intro i j hij
    have := hoff i j hij
    change ((M.1⁻¹).trace⁻¹ • M.1⁻¹) i j = 0 at this
    simpa [htr] using this
  have hd : M.1⁻¹ = Matrix.diagonal (fun i => M.1⁻¹ i i) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, hinv i j hij]
  have : M.1 = (M.1⁻¹)⁻¹ := (Matrix.nonsing_inv_nonsing_inv _ hdet).symm
  intro i j hij
  rw [this, hd, Matrix.inv_diagonal]
  simp [hij]

theorem unip_ne_of_reach (D : Cell) (hD : D ≠ T0) {M : PDMat} (hM : M ∈ reach D) :
    unip (nuSpace M) ≠ 0 := fun h => hD (flat_reach D hM (isDiagMat_of_unip_nuSpace M h)).1

theorem locRel_cellAtSpace_zero (D : Cell) (hD : D ≠ T0) (n : ℕ) :
    (locRel.f n).hom (cellAtSpace n D) = 0 := by
  unfold cellAtSpace
  rw [realizeS_eq_via]
  unfold realizeVia
  rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
  refine Finset.sum_eq_zero fun y hy => ?_
  rw [map_smul]
  have : (locRel.f n).hom (sing (TopCat.of Space) (affVia nuSp y)) = 0 := by
    apply locRel_sing_zero
    intro t
    rw [affVia_apply]
    exact unip_ne_of_reach D hD (affMap_mem_reach D y (cellAt_support n D y hy) t)
  rw [this, smul_zero]

theorem T0_grade : T0.grade = 3 := by
  have h : T0.val.card = 3 := by
    simp [T0, T0set, Finset.card_insert_of_notMem, Line.mk_eq_mk, e0, e1, e2, funext_iff,
      Fin.forall_fin_succ]
  unfold Cell.grade
  rw [h]

theorem realizeVia_Phi (n : ℕ) (z : Cell →₀ ℚ) :
    realizeVia nuSp n (coneData.Phi n z) = z.sum fun D a => a • cellAtSpace n D := by
  have h : realizeVia nuSp n ∘ₗ coneData.Phi n =
      Finsupp.linearCombination ℚ (cellAtSpace n) := by
    apply Finsupp.lhom_ext
    intro D a
    simp only [LinearMap.comp_apply, ConeData.Phi_single, map_smul, Finsupp.linearCombination_single]
    rw [← realizeS_eq_via]
    rfl
  have := LinearMap.congr_fun h z
  simpa [Finsupp.linearCombination_apply] using this

/-- The boundary of the standard top cell chain is a relative cycle for the unipotent projection. -/
theorem cycle_T0 :
    ((localChains 3).d 3 2).hom ((locRel.f 3).hom (cellAtSpace 3 T0)) = 0 := by
  have hcomm := congrArg (fun m => m.hom (cellAtSpace 3 T0)) (locRel.comm 3 2)
  change ((localChains 3).d 3 2).hom ((locRel.f 3).hom (cellAtSpace 3 T0)) =
    (locRel.f 2).hom (((chains Space).d 3 2).hom (cellAtSpace 3 T0)) at hcomm
  have hd : ((chains Space).d 3 2).hom (cellAtSpace 3 T0) =
      (incQ T0).sum fun D a => a • cellAtSpace 2 D := by
    unfold cellAtSpace
    rw [realizeS_eq_via, d_realizeVia, coneData.phi_boundary 2 T0 T0_grade,
      realizeVia_Phi]
    rfl
  rw [hcomm, hd, Finsupp.sum, map_sum]
  refine Finset.sum_eq_zero fun D hD => ?_
  rw [map_smul]
  have hne : D ≠ T0 := by
    intro h
    have := incQ_grade T0 D (Finsupp.mem_support_iff.mp hD)
    rw [h] at this
    omega
  rw [locRel_cellAtSpace_zero D hne 2, smul_zero]

/-- The local degree of the standard top cell chain along the unipotent projection. -/
def dT0 : ℚ := degπ (cellAtSpace 3 T0) cycle_T0

section DegreeAlgebra

variable (K : ChainComplex (ModuleCat.{0} ℚ) ℕ)

theorem cyclesMk_inj {i : ℕ} (x y : (forget₂ (ModuleCat.{0} ℚ) Ab).obj (K.X i)) (j : ℕ)
    (hj : (ComplexShape.down ℕ).next i = j) (hx hy) (h : x = y) :
    K.cyclesMk x j hj hx = K.cyclesMk y j hj hy := by
  subst h
  rfl

theorem homologyπ_cyclesMk_eq {i j : ℕ}
    (x y : (forget₂ (ModuleCat.{0} ℚ) Ab).obj (K.X j)) (z : (forget₂ (ModuleCat.{0} ℚ) Ab).obj (K.X i))
    (hj : (ComplexShape.down ℕ).next j = j - 1) (hx hy)
    (h : x = y + (forget₂ (ModuleCat.{0} ℚ) Ab).map (K.d i j) z) :
    (forget₂ (ModuleCat.{0} ℚ) Ab).map (K.homologyπ j) (K.cyclesMk x (j - 1) hj hx) =
      (forget₂ (ModuleCat.{0} ℚ) Ab).map (K.homologyπ j) (K.cyclesMk y (j - 1) hj hy) := by
  have inj : Function.Injective ((forget₂ (ModuleCat.{0} ℚ) Ab).map (K.iCycles j)) :=
    (Preadditive.mono_iff_injective (K.iCycles j)).1 inferInstance
  have e : K.cyclesMk x (j - 1) hj hx = K.cyclesMk y (j - 1) hj hy +
      (forget₂ (ModuleCat.{0} ℚ) Ab).map (K.toCycles i j) z := by
    apply inj
    rw [map_add, HomologicalComplex.i_cyclesMk, HomologicalComplex.i_cyclesMk,
      ← ConcreteCategory.forget₂_comp_apply, HomologicalComplex.toCycles_i, h]
  rw [e, map_add]
  have : (forget₂ (ModuleCat.{0} ℚ) Ab).map (K.homologyπ j)
      ((forget₂ (ModuleCat.{0} ℚ) Ab).map (K.toCycles i j) z) = 0 := by
    rw [← ConcreteCategory.forget₂_comp_apply, HomologicalComplex.toCycles_comp_homologyπ]
    simp
  rw [this, add_zero]

theorem cyclesMk_add {j : ℕ} (x y : (forget₂ (ModuleCat.{0} ℚ) Ab).obj (K.X j))
    (hj : (ComplexShape.down ℕ).next j = j - 1) (hx hy hxy) :
    K.cyclesMk (x + y) (j - 1) hj hxy = K.cyclesMk x (j - 1) hj hx + K.cyclesMk y (j - 1) hj hy := by
  have inj : Function.Injective ((forget₂ (ModuleCat.{0} ℚ) Ab).map (K.iCycles j)) :=
    (Preadditive.mono_iff_injective (K.iCycles j)).1 inferInstance
  apply inj
  rw [map_add, HomologicalComplex.i_cyclesMk, HomologicalComplex.i_cyclesMk,
    HomologicalComplex.i_cyclesMk]

end DegreeAlgebra

theorem degπ_add (c c' : (chains Space).X 3)
    (h : ((localChains 3).d 3 2).hom ((locRel.f 3).hom c) = 0)
    (h' : ((localChains 3).d 3 2).hom ((locRel.f 3).hom c') = 0)
    (h'' : ((localChains 3).d 3 2).hom ((locRel.f 3).hom (c + c')) = 0) :
    degπ (c + c') h'' = degπ c h + degπ c' h' := by
  have hnext : (ComplexShape.down ℕ).next 3 = 2 :=
    (ComplexShape.down ℕ).next_eq' (show (ComplexShape.down ℕ).Rel 3 2 from rfl)
  have hl : (locRel.f 3).hom (c + c') = (locRel.f 3).hom c + (locRel.f 3).hom c' := map_add _ _ _
  have hxy : (forget₂ (ModuleCat.{0} ℚ) Ab).map ((localChains 3).d 3 2)
      ((locRel.f 3).hom c + (locRel.f 3).hom c') = 0 := by
    change ((localChains 3).d 3 2).hom ((locRel.f 3).hom c + (locRel.f 3).hom c') = 0
    rw [map_add, h, h', add_zero]
  have e := cyclesMk_add (localChains 3) ((locRel.f 3).hom c) ((locRel.f 3).hom c') hnext h h' hxy
  have e2 : (localChains 3).cyclesMk ((locRel.f 3).hom (c + c')) 2 hnext h'' =
      (localChains 3).cyclesMk ((locRel.f 3).hom c + (locRel.f 3).hom c') 2 hnext hxy :=
    cyclesMk_inj (localChains 3) _ _ 2 hnext h'' hxy hl
  unfold degπ
  rw [e2, e, map_add, map_add]

theorem degπ_eq_of_sub (c c' : (chains Space).X 3)
    (h : ((localChains 3).d 3 2).hom ((locRel.f 3).hom c) = 0)
    (h' : ((localChains 3).d 3 2).hom ((locRel.f 3).hom c') = 0)
    (x : (localChains 3).X 4)
    (hx : (locRel.f 3).hom c = (locRel.f 3).hom c' + ((localChains 3).d 4 3).hom x) :
    degπ c h = degπ c' h' := by
  unfold degπ
  congr 1
  exact homologyπ_cyclesMk_eq (localChains 3) _ _ x _ _ _ hx

end TernaryPeriodPolynomials.Argument.Lemma33.Retract.LocalDegree
