module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.Geometry
public import TernaryPeriodPolynomials.SymmetricSpace.CoordinateIsotopy
public import TernaryPeriodPolynomials.SymmetricSpace.LocalOrientationPositive
public import TernaryPeriodPolynomials.SymmetricSpace.MatrixIsotopy.Positive
public import TernaryPeriodPolynomials.Topology.Rational.Relative.MapComposition

@[expose] public section


/-!
# Orientation transport, step (2): the library orientation is the product-chart orientation

The library orients the symmetric space `Space` of trace-one positive forms through the global Euclidean chart
`spaceHomeomorph` (`SymmetricSpaceLocalOrientation.localGenerator`: the chart's chosen local generator
`EuclideanLocalHomology.localGenerator 3`, pulled back to `Space`; `interiorOrientation` is its pushforward to the
arithmetic quotient and restriction to the interior).  The box coordinates of the locality argument
(`Locality.Geometry.coordHomeo`) are the unipotent coordinates followed by the log-pivots `(log a, log b)`, whereas
`spaceHomeomorph` has the same three unipotent coordinates and the log simple-root coordinates
`(½(log b - log a), -½ log b)`.  The two charts therefore differ by a LINEAR map of `ℝ⁵`, namely `Lmat` (identity on
the unipotent block and `[[-1/2, 1/2], [0, -1/2]]` on the pivots), of determinant `1/4 > 0`
(`det_Lmat`, `spaceHomeomorph_eq`).

* `linE_generator`: a positive-determinant linear map of `ℝ⁵` carries the local generator at `x` to the local generator
  at its image (isotopy to the identity along `RealMatrixIsotopy.positiveGLPath`, the library's
  `pointLocalMap_generator`).
* `chartGenerator_eq`: hence two charts of `Space` differing by a positive linear map define the same generator.
* `localGenerator_eq_psiGenerator`: **the orientation of `Space` used by the library (and so the fundamental class of
  `interiorOrientation`) is, at every point, the local generator of the product chart `psi = prodE ∘ coordHomeo`**
  (unipotent coordinates `∈ ℝ³`, log-pivots `∈ ℝ²`).  No sign and no scalar intervenes: the product orientation
  `ℝ³ × ℝ²` of the box IS the library orientation.

Formalized by Claude Sonnet 5.5.
-/

open TernaryPeriodPolynomials.Argument.Lemma33.Locality
open TernaryPoly TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceFlagCoordinates TernaryPoly.SymmetricSpaceEuclideanCoordinates
  TernaryPoly.EuclideanLocalHomology TernaryPoly.SymmetricSpaceLocalOrientation
  CategoryTheory HomologicalComplex TernaryPoly.RationalRelativeSingular

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport

abbrev E5 := EuclideanSpace ℝ (Fin 5)

/-- The linear self-map of `ℝ⁵` of an invertible matrix. -/
def linE (A : Matrix.GeneralLinearGroup (Fin 5) ℝ) : C(E5, E5) where
  toFun v := WithLp.toLp 2 (A.val.mulVec (WithLp.ofLp v))
  continuous_toFun := by
    refine (PiLp.continuous_toLp 2 (fun _ : Fin 5 => ℝ)).comp ?_
    exact (Continuous.matrix_mulVec continuous_const (PiLp.continuous_ofLp 2 (fun _ : Fin 5 => ℝ)))

theorem linE_injective (A : Matrix.GeneralLinearGroup (Fin 5) ℝ) : Function.Injective (linE A) := by
  intro v w h
  have h' : A.val.mulVec (WithLp.ofLp v) = A.val.mulVec (WithLp.ofLp w) := by
    simpa [linE] using congrArg WithLp.ofLp h
  have := congrArg (fun u => (A⁻¹ : Matrix.GeneralLinearGroup (Fin 5) ℝ).val.mulVec u) h'
  simp only [Matrix.mulVec_mulVec] at this
  exact (WithLp.ofLp_injective 2) (by simpa using this)

/-- The isotopy from the identity to `linE A` along a path of invertible matrices. -/
def linHomotopy {A : Matrix.GeneralLinearGroup (Fin 5) ℝ} (p : Path 1 A) :
    ContinuousMap.Homotopy (ContinuousMap.id E5) (linE A) where
  toFun z := linE (p z.1) z.2
  continuous_toFun := by
    refine (PiLp.continuous_toLp 2 (fun _ : Fin 5 => ℝ)).comp ?_
    refine Continuous.matrix_mulVec ?_ ((PiLp.continuous_ofLp 2 (fun _ : Fin 5 => ℝ)).comp continuous_snd)
    exact (Units.continuous_val.comp p.continuous).comp continuous_fst
  map_zero_left z := by
    simp [linE]
  map_one_left z := by
    simp [linE]

theorem linHomotopy_injective {A : Matrix.GeneralLinearGroup (Fin 5) ℝ} (p : Path 1 A)
    (t : unitInterval) : Function.Injective (fun z => linHomotopy p (t, z)) :=
  linE_injective (p t)

/-- A positive-determinant linear map of `ℝ⁵` preserves the local generator at every point. -/
theorem linE_generator {A : Matrix.GeneralLinearGroup (Fin 5) ℝ}
    (hA : 0 < (Matrix.GeneralLinearGroup.det A : ℝ)) (x : E5) :
    homologyMap (pointLocalMap (linE A) (linE_injective A) x) 5 (localGenerator 3 x) =
      localGenerator 3 (linE A x) :=
  pointLocalMap_generator 3 (linE A) (linE_injective A)
    (linHomotopy (RealMatrixIsotopy.positiveGLPath A hA)) (linHomotopy_injective _) x

/-- The comparison of local chains of `Space` at `S` with those of `ℝ⁵` at `ψ S` through a chart `ψ`. -/
def chartIso (ψ : Space ≃ₜ E5) (S : Space) :
    (localChainsAt S).homology 5 ≅ (EuclideanLocalHomology.localChainsAt 5 (ψ S)).homology 5 :=
  (homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) 5).mapIso
    (relativeHomeomorphIso ψ {S}ᶜ {ψ S}ᶜ (by
      intro T
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff, ψ.injective.eq_iff]))

/-- The orientation generator of `Space` at `S` read in the chart `ψ`. -/
def chartGenerator (ψ : Space ≃ₜ E5) (S : Space) : (localChainsAt S).homology 5 :=
  (chartIso ψ S).inv (localGenerator 3 (ψ S))

theorem chartIso_spaceHomeomorph (S : Space) :
    chartIso spaceHomeomorph S = coordinateLocalHomologyIso S := rfl

theorem localGenerator_eq_chartGenerator (S : Space) :
    SymmetricSpaceLocalOrientation.localGenerator S = chartGenerator spaceHomeomorph S := rfl

theorem linE_generator' {A : Matrix.GeneralLinearGroup (Fin 5) ℝ}
    (hA : 0 < (Matrix.GeneralLinearGroup.det A : ℝ)) (x y : E5) (h : linE A x = y)
    (hm : Set.MapsTo (linE A) ({x}ᶜ : Set E5) ({y}ᶜ : Set E5)) :
    homologyMap (relativeMap (linE A) ({x}ᶜ : Set E5) ({y}ᶜ : Set E5) hm) 5 (localGenerator 3 x) =
      localGenerator 3 y := by
  subst h
  exact linE_generator hA x

/-- **Chart change.**  If two charts of the symmetric space differ by a linear map of positive determinant,
`spaceHomeomorph = linE A ∘ ψ`, they define the same orientation generator at every point. -/
theorem chartGenerator_eq {A : Matrix.GeneralLinearGroup (Fin 5) ℝ}
    (hA : 0 < (Matrix.GeneralLinearGroup.det A : ℝ)) (ψ : Space ≃ₜ E5)
    (hψ : ∀ S, spaceHomeomorph S = linE A (ψ S)) (S : Space) :
    chartGenerator spaceHomeomorph S = chartGenerator ψ S := by
  have hfun : (spaceHomeomorph.toHomotopyEquiv.toFun : C(Space, E5)) =
      (linE A).comp ψ.toHomotopyEquiv.toFun := by
    exact ContinuousMap.ext fun z => hψ z
  have hmaps : Set.MapsTo (linE A) ({ψ S}ᶜ : Set E5) ({spaceHomeomorph S}ᶜ : Set E5) := by
    intro z hz hzs
    apply hz
    apply linE_injective A
    rw [← hψ S]
    exact hzs
  have hrel : ∀ (f g : C(Space, E5)) (hfg : f = g) (B : Set E5) (hf : Set.MapsTo f ({S}ᶜ : Set Space) B)
      (hg : Set.MapsTo g ({S}ᶜ : Set Space) B), relativeMap f _ B hf = relativeMap g _ B hg := by
    intro f g hfg B hf hg
    subst hfg
    rfl
  have key : (chartIso spaceHomeomorph S).hom =
      (chartIso ψ S).hom ≫ homologyMap (relativeMap (linE A) ({ψ S}ᶜ : Set E5)
        ({spaceHomeomorph S}ᶜ : Set E5) hmaps) 5 := by
    unfold chartIso
    simp only [Functor.mapIso_hom, relativeHomeomorphIso_hom]
    change _ = (homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) 5).map _ ≫
      (homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) 5).map _
    rw [← Functor.map_comp]
    refine congrArg (homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) 5).map ?_
    have hψm : Set.MapsTo ψ.toHomotopyEquiv.toFun ({S}ᶜ : Set Space) ({ψ S}ᶜ : Set E5) := by
      intro x hx hxs
      exact hx (ψ.injective hxs)
    exact (hrel _ ((linE A).comp ψ.toHomotopyEquiv.toFun) hfun _ _
      (fun x hx => hmaps (hψm hx))).trans (relativeMap_comp _ _ _ _ _ hψm hmaps).symm
  have hgen := linE_generator' hA (ψ S) (spaceHomeomorph S) (hψ S).symm hmaps
  unfold chartGenerator
  have e1 : (chartIso spaceHomeomorph S).hom ((chartIso spaceHomeomorph S).inv
      (localGenerator 3 (spaceHomeomorph S))) = localGenerator 3 (spaceHomeomorph S) :=
    Iso.inv_hom_id_apply _ _
  have e2 : (chartIso spaceHomeomorph S).hom ((chartIso ψ S).inv (localGenerator 3 (ψ S))) =
      localGenerator 3 (spaceHomeomorph S) := by
    rw [key]
    change homologyMap (relativeMap (linE A) ({ψ S}ᶜ : Set E5) ({spaceHomeomorph S}ᶜ : Set E5) hmaps) 5
      ((chartIso ψ S).hom ((chartIso ψ S).inv (localGenerator 3 (ψ S)))) = _
    rw [Iso.inv_hom_id_apply]
    exact hgen
  exact (ModuleCat.mono_iff_injective (chartIso spaceHomeomorph S).hom).mp inferInstance (e1.trans e2.symm)

/-- The product-coordinate chart `Space ≃ₜ ℝ⁵`: the unipotent coordinates followed by the log-pivots. -/
def prodE : R3 × R2 ≃ₜ EuclideanSpace ℝ (Fin 5) where
  toFun p := WithLp.toLp 2 ![p.1 0, p.1 1, p.1 2, p.2 0, p.2 1]
  invFun v := (WithLp.toLp 2 ![v 0, v 1, v 2], WithLp.toLp 2 ![v 3, v 4])
  left_inv p := by
    apply Prod.ext
    · apply PiLp.ext; intro i; fin_cases i <;> rfl
    · apply PiLp.ext; intro i; fin_cases i <;> rfl
  right_inv v := by
    apply PiLp.ext
    intro i
    fin_cases i <;> rfl
  continuous_toFun := by
    refine (PiLp.continuous_toLp 2 (fun _ : Fin 5 => ℝ)).comp ?_
    refine continuous_pi fun i => ?_
    fin_cases i
    · exact (PiLp.continuous_apply 2 _ 0).comp continuous_fst
    · exact (PiLp.continuous_apply 2 _ 1).comp continuous_fst
    · exact (PiLp.continuous_apply 2 _ 2).comp continuous_fst
    · exact (PiLp.continuous_apply 2 _ 0).comp continuous_snd
    · exact (PiLp.continuous_apply 2 _ 1).comp continuous_snd
  continuous_invFun := by
    refine Continuous.prodMk ?_ ?_
    · refine (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp ?_
      refine continuous_pi fun i => ?_
      fin_cases i
      · exact PiLp.continuous_apply 2 _ 0
      · exact PiLp.continuous_apply 2 _ 1
      · exact PiLp.continuous_apply 2 _ 2
    · refine (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp ?_
      refine continuous_pi fun i => ?_
      fin_cases i
      · exact PiLp.continuous_apply 2 _ 3
      · exact PiLp.continuous_apply 2 _ 4

/-- The product chart of the symmetric space. -/
def psi : Space ≃ₜ EuclideanSpace ℝ (Fin 5) := coordHomeo.trans prodE

/-- The linear change from the product chart to the global Euclidean chart of the library: identity on
the unipotent coordinates and `(u, v) ↦ ((v - u)/2, -v/2)` on the log-pivots. -/
def Lmat : Matrix (Fin 5) (Fin 5) ℝ :=
  !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, -1/2, 1/2; 0, 0, 0, 0, -1/2]

theorem det_Lmat : Lmat.det = 1 / 4 := by
  have h : Lmat.BlockTriangular id := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [Lmat]
  rw [Matrix.det_of_isUpperTriangular h]
  simp [Lmat, Fin.prod_univ_succ]
  norm_num


/-- The matrix `Lmat` as an element of the general linear group. -/
def Lgl : Matrix.GeneralLinearGroup (Fin 5) ℝ :=
  Matrix.GeneralLinearGroup.mk'' Lmat (by
    rw [det_Lmat]
    exact isUnit_iff_ne_zero.mpr (by norm_num))

theorem Lgl_apply (i j : Fin 5) : ((Lgl : Matrix.GeneralLinearGroup (Fin 5) ℝ) : Matrix (Fin 5) (Fin 5) ℝ) i j = Lmat i j := rfl

theorem Lgl_val : (Lgl : Matrix (Fin 5) (Fin 5) ℝ) = Lmat := rfl

theorem Lgl_det_pos : 0 < (Matrix.GeneralLinearGroup.det Lgl : ℝ) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, Lgl_val, det_Lmat]
  norm_num

theorem symm_eq_log (x : Set.Ioi (0 : ℝ)) : Real.expOrderIso.symm x = Real.log x := by
  apply Real.exp_injective
  rw [← Real.coe_expOrderIso_apply, OrderIso.apply_symm_apply, Real.exp_log x.2]

theorem spaceHomeomorph_eq (S : Space) : spaceHomeomorph S = linE Lgl (psi S) := by
  apply PiLp.ext
  intro i
  fin_cases i
  all_goals simp [linE, Lgl_apply, Lmat, symm_eq_log, psi, prodE, coordHomeo, spaceHomeomorph, vectorFiveHomeomorph, rootHomeomorph, uHomeo, tHomeo, positiveRootHomeomorph, positiveScaleHomeomorph, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · have ha : 0 < binaryA (SymmetricSpaceParabolicCoordinates.schur S.val) :=
      (ldlHomeomorph_a S) ▸ (ldlHomeomorph S).2.1.property
    have hb : 0 < binaryB (SymmetricSpaceParabolicCoordinates.schur S.val) :=
      (ldlHomeomorph_b S) ▸ (ldlHomeomorph S).2.2.property
    rw [Real.log_sqrt (div_nonneg hb.le ha.le), Real.log_div hb.ne' ha.ne']
    ring
  · have hb : 0 < binaryB (SymmetricSpaceParabolicCoordinates.schur S.val) :=
      (ldlHomeomorph_b S) ▸ (ldlHomeomorph S).2.2.property
    rw [Real.log_sqrt hb.le]
    ring

/-- **The library orientation of the symmetric space is the product-chart orientation.** -/
theorem localGenerator_eq_psiGenerator (S : Space) :
    SymmetricSpaceLocalOrientation.localGenerator S = chartGenerator psi S :=
  (localGenerator_eq_chartGenerator S).trans (chartGenerator_eq Lgl_det_pos psi spaceHomeomorph_eq S)

end TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport
