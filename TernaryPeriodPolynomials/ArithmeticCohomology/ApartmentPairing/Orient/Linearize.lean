module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Orient.RelClass

@[expose] public section


/-!
# Linearization of the unipotent projection on the standard top cell (Lemma 3.3, G3 local half)

The diagonal flat of the symmetric space is the zero locus of the unipotent coordinates
`unip : Space → ℝ³` of the Borel corner chart.  On the slice of unit-diagonal forms
`Q(p,q,r) = [[1,p,q],[p,1,r],[q,r,1]]` (the affine hull of the sixteen vertices of the standard top
cell `T₀` of the well-rounded retract) we prove the explicit formula
`unip (ν Q) = (-p, (pq - r)/(1 - p²), (pr - q)/(1 - p²))` (`unip_nuSpace_Qmat`), whose only zero is
`Q = 1` and whose linear part is `(p,q,r) ↦ (-p, -r, -q)` (a permutation matrix times `-1`, of
determinant `+1`).

* `Hmap s`: a rational homotopy on all positive definite forms, `s ∈ [0,1]`, vanishing exactly at
  the diagonal forms (`Hmap_eq_zero_iff`); on the slice `Hmap 1 = unip ∘ ν` (`Hf1_eq_Pc`) and
  `Hmap 0 = Lc`, the linear map `Q ↦ (-Q₁₂, -Q₂₃, -Q₁₃)` (`Hf0_eq_Lc`).
* `dT0_eq_degRel_lin`: the local degree `dT0 = degπ (cellAtSpace 3 T₀)` of the standard top cell
  equals the local degree `degRel` of the affine chain `realizeVia Lc 3 Phi3` (the cone chain of the
  cell pushed forward by the linear map `Lc`); `Phi3` is the formal cone chain of `T₀`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Classical
open TernaryPoly TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceFlagCoordinates
  CategoryTheory Limits HomologicalComplex TernaryPoly.RationalSingularAugmentation
  TernaryPoly.RationalRelativeSingular TernaryPoly.ContractibleSingularHomology
  TernaryPoly.FreeActionLinearization TernaryPoly.EuclideanLocalHomology TernaryPoly.RationalSphere
  TernaryPeriodPolynomials.Argument.Lemma33.Retract
  TernaryPeriodPolynomials.Argument.Lemma33.Retract.LocalDegree
  TernaryPeriodPolynomials.Argument.Lemma33.Retract.Cell0Geometry

namespace TernaryPeriodPolynomials.Argument.Lemma33.Orient

/-- The unit-diagonal slice of the form space, in the off-diagonal coordinates `(p,q,r)`. -/
def Qmat (p q r : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![1, p, q; p, 1, r; q, r, 1]

theorem Qmat_det (p q r : ℝ) : (Qmat p q r).det = 1 + 2 * p * q * r - p ^ 2 - q ^ 2 - r ^ 2 := by
  simp [Qmat, Matrix.det_fin_three]; ring

theorem Qmat_p_sq_lt (p q r : ℝ) (h : (Qmat p q r).PosDef) : p ^ 2 < 1 := by
  have h2 := h.dotProduct_mulVec_pos (x := ![1, -p, 0]) (by
    intro h0
    have := congrFun h0 0
    simp at this)
  simp [Qmat, dotProduct, Matrix.mulVec, Fin.sum_univ_succ] at h2
  nlinarith

theorem Qmat_det_pos (p q r : ℝ) (h : (Qmat p q r).PosDef) :
    0 < 1 + 2 * p * q * r - p ^ 2 - q ^ 2 - r ^ 2 := by
  rw [← Qmat_det]; exact h.det_pos

theorem flagMatrix_eq (x y z a b : ℝ) :
    flagMatrix x y z a b =
      !![a + x ^ 2 * b + z ^ 2, x * b + z * y, z; x * b + z * y, b + y ^ 2, y; z, y, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [flagMatrix, upper, SymmetricSpaceFlagCoordinates.diagonal, Matrix.mul_apply,
      Matrix.vecMul_diagonal, Fin.sum_univ_succ, Matrix.transpose_apply] <;> ring

theorem Qmat_mul_flag_aux (p q r D : ℝ) (hD : D = 1 + 2 * p * q * r - p ^ 2 - q ^ 2 - r ^ 2)
    (h1' : (1 - p ^ 2) ≠ 0) (hd' : D ≠ 0) :
    Qmat p q r * ((1 - p ^ 2) / D) •
      flagMatrix (-p) ((p * q - r) / (1 - p ^ 2)) ((p * r - q) / (1 - p ^ 2)) (D / (1 - p ^ 2))
        (D / (1 - p ^ 2) ^ 2) = 1 := by
  rw [flagMatrix_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Qmat, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    field_simp <;> rw [hD] <;> ring

/-- **The unipotent coordinates of the inverse of a unit-diagonal form**:
`unip (ν Q) = (-p, (pq - r)/(1 - p²), (pr - q)/(1 - p²))`. -/
theorem unip_nuSpace_Qmat (p q r : ℝ) (hQ : (Qmat p q r).PosDef) :
    unip (nuSpace ⟨Qmat p q r, hQ⟩) =
      ![-p, (p * q - r) / (1 - p ^ 2), (p * r - q) / (1 - p ^ 2)] := by
  have h1 : 0 < 1 - p ^ 2 := by linarith [Qmat_p_sq_lt p q r hQ]
  have hd := Qmat_det_pos p q r hQ
  set D := 1 + 2 * p * q * r - p ^ 2 - q ^ 2 - r ^ 2 with hD
  have ha : 0 < D / (1 - p ^ 2) := div_pos hd h1
  have hb : 0 < D / (1 - p ^ 2) ^ 2 := div_pos hd (pow_pos h1 2)
  let p0 : LDLParameters := (![-p, (p * q - r) / (1 - p ^ 2), (p * r - q) / (1 - p ^ 2)],
    (⟨D / (1 - p ^ 2), ha⟩, ⟨D / (1 - p ^ 2) ^ 2, hb⟩))
  have key := Qmat_mul_flag_aux p q r D hD h1.ne' hd.ne'
  have hinv : (Qmat p q r)⁻¹ = ((1 - p ^ 2) / D) • flagMatrix (-p) ((p * q - r) / (1 - p ^ 2))
      ((p * r - q) / (1 - p ^ 2)) (D / (1 - p ^ 2)) (D / (1 - p ^ 2) ^ 2) :=
    Matrix.inv_eq_right_inv key
  have hF : flagMatrix (-p) ((p * q - r) / (1 - p ^ 2)) ((p * r - q) / (1 - p ^ 2)) (D / (1 - p ^ 2))
      (D / (1 - p ^ 2) ^ 2) = (D / (1 - p ^ 2)) • (Qmat p q r)⁻¹ := by
    rw [hinv, smul_smul, div_mul_div_comm, mul_comm D (1 - p ^ 2),
      div_self (mul_ne_zero h1.ne' hd.ne'), one_smul]
  have hp0 : normalize (flagMatrix (p0.1 0) (p0.1 1) (p0.1 2) p0.2.1.val p0.2.2.val) =
      (nuSpace ⟨Qmat p q r, hQ⟩).val := by
    change normalize (flagMatrix (-p) ((p * q - r) / (1 - p ^ 2)) ((p * r - q) / (1 - p ^ 2))
      (D / (1 - p ^ 2)) (D / (1 - p ^ 2) ^ 2)) = normalize (Qmat p q r)⁻¹
    rw [hF]
    exact normalize_smul _ (div_pos hd h1).ne' _
  have hS := (ldlHomeomorph_symm (ldlHomeomorph (nuSpace ⟨Qmat p q r, hQ⟩))).symm.trans
    (congrArg Subtype.val (ldlHomeomorph.symm_apply_apply (nuSpace ⟨Qmat p q r, hQ⟩)))
  obtain ⟨w, _, huniq⟩ := normalizedFlag_exists_unique (nuSpace ⟨Qmat p q r, hQ⟩)
  have e : ldlHomeomorph (nuSpace ⟨Qmat p q r, hQ⟩) = p0 :=
    (huniq _ hS).trans (huniq p0 hp0).symm
  unfold unip
  rw [e]

/-! ### Positive definite forms: elementary inequalities -/

theorem pd_symm (M : PDMat) (i j : Fin 3) : M.1 j i = M.1 i j := by
  have := M.2.isHermitian
  have h := congrFun (congrFun this.eq i) j
  simpa [Matrix.conjTranspose_apply] using h

theorem pd_diag_pos (M : PDMat) (i : Fin 3) : 0 < M.1 i i := M.2.diag_pos

theorem pd_sq_lt (M : PDMat) : (M.1 0 1) ^ 2 < M.1 0 0 * M.1 1 1 := by
  have h2 := M.2.dotProduct_mulVec_pos (x := ![M.1 1 1, -M.1 0 1, 0]) (by
    intro h0
    have := congrFun h0 0
    have h11 := pd_diag_pos M 1
    simp at this
    linarith)
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_succ, pd_symm M 1 0] at h2
  have h11 := pd_diag_pos M 1
  have h3 : 0 < M.1 1 1 * (M.1 0 0 * M.1 1 1 - M.1 1 0 ^ 2) := by nlinarith [h2]
  have h4 := (mul_pos_iff_of_pos_left h11).mp h3
  rw [pd_symm M 1 0]
  linarith


/-! ### The homotopy from the linear map to the unipotent projection on the slice -/

/-- The common denominator of the homotopy. -/
def hden (s : ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ) : ℝ := M 1 1 - s * M 0 1 ^ 2 / M 0 0

/-- The homotopy `H_s`: rational in the entries of a positive definite form; `H_1` is the unipotent
projection `unip ∘ ν` on the slice of unit diagonal and `H_0` is its linearization
`Q ↦ (-q₁₂, -q₂₃, -q₁₃)` there. -/
def hfun (s : ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ) : Fin 3 → ℝ :=
  ![-(M 0 1) / M 0 0, (s * M 0 1 * M 0 2 / M 0 0 - M 1 2) / hden s M,
    (s * M 0 1 * M 1 2 / M 0 0 - M 0 2 * M 1 1 / M 0 0) / hden s M]

/-- The homotopy with values in Euclidean space. -/
def Hmap (s : ℝ) (M : PDMat) : E3 := (EuclideanSpace.equiv (Fin 3) ℝ).symm (hfun s M.1)

theorem hden_pos {s : ℝ} (hs1 : s ≤ 1) (M : PDMat) : 0 < hden s M.1 := by
  have h00 := pd_diag_pos M 0
  have h := pd_sq_lt M
  unfold hden
  have : M.1 1 1 - s * M.1 0 1 ^ 2 / M.1 0 0 = (M.1 0 0 * M.1 1 1 - s * M.1 0 1 ^ 2) / M.1 0 0 := by
    field_simp
  rw [this]
  apply div_pos _ h00
  nlinarith [sq_nonneg (M.1 0 1)]

theorem hfun_eq_zero_iff {s : ℝ} (hs1 : s ≤ 1) (M : PDMat) :
    hfun s M.1 = 0 ↔ IsDiagMat M.1 := by
  have h00 := pd_diag_pos M 0
  have h11 := pd_diag_pos M 1
  have hd := hden_pos hs1 M
  constructor
  · intro h
    have c0 := congrFun h 0
    have c1 := congrFun h 1
    have c2 := congrFun h 2
    simp only [hfun, Pi.zero_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val] at c0 c1 c2
    have a01 : M.1 0 1 = 0 := by
      have := c0
      rw [div_eq_zero_iff] at this
      rcases this with h | h
      · linarith
      · exact absurd h h00.ne'
    have a12 : M.1 1 2 = 0 := by
      rw [div_eq_zero_iff] at c1
      rcases c1 with h | h
      · rw [a01] at h; simpa using h
      · exact absurd h hd.ne'
    have a02 : M.1 0 2 = 0 := by
      rw [div_eq_zero_iff] at c2
      rcases c2 with h | h
      · rw [a01] at h
        have : M.1 0 2 * M.1 1 1 / M.1 0 0 = 0 := by simpa using h
        rw [div_eq_zero_iff, mul_eq_zero] at this
        rcases this with (h | h) | h
        · exact h
        · exact absurd h h11.ne'
        · exact absurd h h00.ne'
      · exact absurd h hd.ne'
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
    · exact a01
    · exact a02
    · rw [pd_symm M 0 1]; exact a01
    · exact a12
    · rw [pd_symm M 0 2]; exact a02
    · rw [pd_symm M 1 2]; exact a12
  · intro h
    have a01 := h 0 1 (by decide)
    have a02 := h 0 2 (by decide)
    have a12 := h 1 2 (by decide)
    funext i
    fin_cases i <;> simp [hfun, a01, a02, a12]

theorem Hmap_eq_zero_iff {s : ℝ} (hs1 : s ≤ 1) (M : PDMat) :
    Hmap s M = 0 ↔ IsDiagMat M.1 := by
  rw [← hfun_eq_zero_iff hs1 M]
  unfold Hmap
  constructor
  · intro h
    simpa using h
  · intro h
    rw [h]
    rfl

theorem continuous_Hmap : Continuous fun p : unitInterval × PDMat => Hmap p.1 p.2 := by
  unfold Hmap
  refine (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous.comp ?_
  have e : ∀ i j, Continuous fun p : unitInterval × PDMat => p.2.1 i j := fun i j =>
    (continuous_subtype_val.comp continuous_snd).matrix_elem i j
  have hs : Continuous fun p : unitInterval × PDMat => (p.1 : ℝ) := continuous_subtype_val.comp continuous_fst
  have h00 : ∀ p : unitInterval × PDMat, p.2.1 0 0 ≠ 0 := fun p => (pd_diag_pos p.2 0).ne'
  have hd : ∀ p : unitInterval × PDMat, hden p.1 p.2.1 ≠ 0 := fun p =>
    (hden_pos p.1.2.2 p.2).ne'
  have hden_c : Continuous fun p : unitInterval × PDMat => hden p.1 p.2.1 := by
    unfold hden
    exact (e 1 1).sub ((hs.mul ((e 0 1).pow 2)).div (e 0 0) h00)
  refine continuous_pi fun i => ?_
  fin_cases i
  · simp only [hfun, Fin.zero_eta, Matrix.cons_val_zero]
    exact (e 0 1).neg.div (e 0 0) h00
  · simp only [hfun, Fin.mk_one, Matrix.cons_val_one]
    exact (((hs.mul (e 0 1)).mul (e 0 2)).div (e 0 0) h00 |>.sub (e 1 2)).div hden_c hd
  · simp only [hfun, Fin.reduceFinMk, Matrix.cons_val]
    exact ((((hs.mul (e 0 1)).mul (e 1 2)).div (e 0 0) h00).sub (((e 0 2).mul (e 1 1)).div (e 0 0) h00)).div hden_c hd


/-! ### Endpoints on the unit-diagonal slice -/

/-- The unit-diagonal slice. -/
def IsUnitDiag (M : PDMat) : Prop := ∀ i, M.1 i i = 1

theorem slice_eq (M : PDMat) (h : IsUnitDiag M) : M.1 = Qmat (M.1 0 1) (M.1 0 2) (M.1 1 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Qmat, h 0, h 1, h 2, pd_symm M 0 1, pd_symm M 0 2, pd_symm M 1 2]


/-- The linearization `Q ↦ (-q₁₂, -q₂₃, -q₁₃)`. -/
def Lraw (M : Matrix (Fin 3) (Fin 3) ℝ) : E3 :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm ![-(M 0 1), -(M 1 2), -(M 0 2)]

/-- The linearization as a continuous map on positive definite forms. -/
def Lc : C(PDMat, E3) where
  toFun M := Lraw M.1
  continuous_toFun := by
    unfold Lraw
    refine (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous.comp ?_
    refine continuous_pi fun i => ?_
    have e : ∀ i j, Continuous fun M : PDMat => M.1 i j := fun i j =>
      continuous_subtype_val.matrix_elem i j
    fin_cases i
    · exact (e 0 1).neg
    · exact (e 1 2).neg
    · exact (e 0 2).neg

/-- The unipotent projection `unip ∘ ν` on positive definite forms. -/
def Pc : C(PDMat, E3) := piR3.comp nuSp

/-- The homotopy at time `0`. -/
def Hf0 : C(PDMat, E3) :=
  ⟨Hmap 0, continuous_Hmap.comp (Continuous.prodMk (continuous_const (y := (0 : unitInterval)))
    continuous_id)⟩

/-- The homotopy at time `1`. -/
def Hf1 : C(PDMat, E3) :=
  ⟨Hmap 1, continuous_Hmap.comp (Continuous.prodMk (continuous_const (y := (1 : unitInterval)))
    continuous_id)⟩

/-- The homotopy of continuous maps from the linearization to the (rational lift of the)
unipotent projection. -/
def Hhom : ContinuousMap.Homotopy Hf0 Hf1 where
  toFun p := Hmap p.1 p.2
  continuous_toFun := continuous_Hmap
  map_zero_left _ := rfl
  map_one_left _ := rfl

theorem Hf0_eq_Lc (M : PDMat) (h : IsUnitDiag M) : Hf0 M = Lc M := by
  have h00 := h 0
  have h11 := h 1
  change (EuclideanSpace.equiv (Fin 3) ℝ).symm (hfun 0 M.1) = (EuclideanSpace.equiv (Fin 3) ℝ).symm _
  congr 1
  funext i
  fin_cases i <;> simp [hfun, hden, h00, h11]

theorem Hf1_eq_Pc (M : PDMat) (h : IsUnitDiag M) : Hf1 M = Pc M := by
  have key := unip_nuSpace_Qmat (M.1 0 1) (M.1 0 2) (M.1 1 2) (by rw [← slice_eq M h]; exact M.2)
  have hM : (⟨Qmat (M.1 0 1) (M.1 0 2) (M.1 1 2), by rw [← slice_eq M h]; exact M.2⟩ : PDMat) = M :=
    Subtype.ext (slice_eq M h).symm
  rw [hM] at key
  have h00 := h 0
  have h11 := h 1
  change (EuclideanSpace.equiv (Fin 3) ℝ).symm (hfun 1 M.1) = (EuclideanSpace.equiv (Fin 3) ℝ).symm (unip (nuSpace M))
  congr 1
  rw [key]
  funext i
  fin_cases i <;> simp [hfun, hden, h00, h11]

theorem Hf0_ne_zero (M : PDMat) (hM : ¬ IsDiagMat M.1) : Hf0 M ≠ 0 := fun h =>
  hM ((Hmap_eq_zero_iff (s := 0) zero_le_one M).mp h)


/-! ### Chains: realization through maps, supports and relative cycles -/

section Chains

open TernaryPeriodPolynomials.Argument.Lemma33 Finsupp

variable {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z]

theorem map_affVia (g : C(Y, Z)) (f : C(PDMat, Y)) {n : ℕ} (y : AffSimp PDMat n) :
    (TopCat.toSSet.map (TopCat.ofHom g)).app (Opposite.op (SimplexCategory.mk n)) (affVia f y) =
      affVia (g.comp f) y := by
  apply ((TopCat.of Z).toSSetObjEquiv _).injective
  exact ContinuousMap.ext (fun t => rfl)

theorem chainMap_realizeVia (g : C(Y, Z)) (f : C(PDMat, Y)) (n : ℕ) (z : AffChain PDMat n) :
    ((chainMap g).f n).hom (realizeVia f n z) = realizeVia (g.comp f) n z := by
  have h : ((chainMap g).f n).hom ∘ₗ realizeVia f n = realizeVia (g.comp f) n := by
    apply Finsupp.lhom_ext
    intro y a
    have e : single y a = a • single y (1 : ℚ) := by simp
    rw [e]
    simp only [LinearMap.comp_apply, map_smul]
    rw [realizeVia_single, realizeVia_single, one_smul, one_smul, chainMap_sing, map_affVia]
  exact LinearMap.congr_fun h z

theorem affVia_congr (f g : C(PDMat, Y)) {n : ℕ} (y : AffSimp PDMat n)
    (h : ∀ t, f (affMap n y t) = g (affMap n y t)) : affVia f y = affVia g y := by
  apply ((TopCat.of Y).toSSetObjEquiv _).injective
  refine ContinuousMap.ext (fun t => ?_)
  exact (affVia_apply f y t).trans ((h t).trans (affVia_apply g y t).symm)

theorem realizeVia_congr (f g : C(PDMat, Y)) (n : ℕ) (z : AffChain PDMat n)
    (h : ∀ y ∈ z.support, ∀ t, f (affMap n y t) = g (affMap n y t)) :
    realizeVia f n z = realizeVia g n z := by
  rw [realizeVia, realizeVia, Finsupp.linearCombination_apply, Finsupp.linearCombination_apply]
  refine Finsupp.sum_congr (fun y hy => ?_)
  rw [affVia_congr f g y (h y hy)]

theorem realizeVia_mem_range (f : C(PDMat, Y)) (S : Set Y) (n : ℕ) (z : AffChain PDMat n)
    (h : ∀ y ∈ z.support, ∀ t, f (affMap n y t) ∈ S) :
    realizeVia f n z ∈ LinearMap.range ((RationalRelativeSingular.inclusion S).f n).hom := by
  rw [realizeVia, Finsupp.linearCombination_apply, Finsupp.sum]
  refine Submodule.sum_mem _ (fun y hy => Submodule.smul_mem _ _ ?_)
  apply sing_mem_range
  intro t
  rw [affVia_apply]
  exact h y hy t

end Chains


/-! ### The standard top cell -/

section T0

open Finsupp TernaryPeriodPolynomials.FreeResolution

/-- The formal affine 3-chain of the standard top cell (the cone recursion of the retract). -/
def Phi3 : AffChain PDMat 3 := coneData.phi 3 T0

theorem qfR_eV (M : Matrix (Fin 3) (Fin 3) ℝ) (k : Fin 3) : qfR M (eV k) = M k k := by
  fin_cases k <;> simp [qfR, eV, e0, e1, e2, Fin.sum_univ_three]

theorem Phi3_vertex_diag {y : AffSimp PDMat 3} (hy : y ∈ Phi3.support) (i : Fin 4) (k : Fin 3) :
    (y i).1 k k = 1 := by
  have hv := cellAt_support 3 T0 y hy i
  have hk : Line.mk (eV k) ∈ T0.val := by fin_cases k <;> simp [eV, T0, T0set]
  have := reach_eq_one T0 hv hk
  rwa [qfR_eV] at this

theorem Phi3_unitDiag {y : AffSimp PDMat 3} (hy : y ∈ Phi3.support) (t : Convexity.StdSimplex ℝ (Fin 4)) :
    IsUnitDiag (affMap 3 y t) := by
  intro k
  rw [affMap_val]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Phi3_vertex_diag hy, mul_one]
  exact t.total_of_fintype

theorem Phi3_boundary_nondiag {y : AffSimp PDMat 2} (hy : y ∈ (dAff PDMat 2 Phi3).support)
    (t : Convexity.StdSimplex ℝ (Fin 3)) : ¬ IsDiagMat (affMap 2 y t).1 := by
  intro hd
  have hb : dAff PDMat 2 Phi3 = coneData.Phi 2 (incQ T0) := coneData.phi_boundary 2 T0 T0_grade
  rw [hb] at hy
  obtain ⟨D, hD, hyD⟩ : ∃ D ∈ (incQ T0).support, y ∈ (coneData.phi 2 D).support := by
    have := coneData.support_Phi_subset 2 (incQ T0) hy
    simpa only [Finset.mem_biUnion] using this
  have hne : D ≠ T0 := by
    intro h
    have := incQ_grade T0 D (Finsupp.mem_support_iff.mp hD)
    rw [h] at this
    omega
  exact hne (flat_reach D (affMap_mem_reach D y (cellAt_support 2 D y hyD) t) hd).1

/-- The formal 3-chain of the standard top cell, as a singular chain of the cone of forms. -/
def cX : (chains PDMat).X 3 := realizeVia (ContinuousMap.id PDMat) 3 Phi3

/-- The non-diagonal forms. -/
def Snd : Set PDMat := {M | ¬ IsDiagMat M.1}

theorem cX_relCycle : RelCycle Snd cX := by
  apply relCycle_of_mem_range
  have h : ((chains PDMat).d 3 2).hom cX = realizeVia (ContinuousMap.id PDMat) 2 (dAff PDMat 2 Phi3) :=
    d_realizeVia (ContinuousMap.id PDMat) 2 Phi3
  rw [h]
  apply realizeVia_mem_range
  intro y hy t
  exact Phi3_boundary_nondiag hy t

theorem Hhom_maps (t : unitInterval) (M : PDMat) (hM : M ∈ Snd) : Hhom (t, M) ∈ Punctured 3 := by
  intro h0
  have h1 : Hmap (t : ℝ) M = 0 := h0
  exact hM ((Hmap_eq_zero_iff t.2.2 M).mp h1)

theorem Hf0_maps : Set.MapsTo Hf0 Snd (Punctured 3) := fun M hM => Hhom_maps 0 M hM

theorem Hf1_maps : Set.MapsTo Hf1 Snd (Punctured 3) := fun M hM => Hhom_maps 1 M hM

theorem chain_Hf0_eq_Lc :
    AbF.map ((chainMap Hf0).f 3) cX = realizeVia Lc 3 Phi3 := by
  change ((chainMap Hf0).f 3).hom (realizeVia (ContinuousMap.id PDMat) 3 Phi3) = _
  rw [chainMap_realizeVia]
  apply realizeVia_congr
  intro y hy t
  exact Hf0_eq_Lc _ (Phi3_unitDiag hy t)

theorem chain_Hf1_eq_Pc :
    AbF.map ((chainMap Hf1).f 3) cX = realizeVia Pc 3 Phi3 := by
  change ((chainMap Hf1).f 3).hom (realizeVia (ContinuousMap.id PDMat) 3 Phi3) = _
  rw [chainMap_realizeVia]
  apply realizeVia_congr
  intro y hy t
  exact Hf1_eq_Pc _ (Phi3_unitDiag hy t)

theorem lin_relCycle : RelCycle (Punctured 3) (realizeVia Lc 3 Phi3) := by
  rw [← chain_Hf0_eq_Lc]
  exact RelCycle.map Hf0 Snd (Punctured 3) Hf0_maps cX cX_relCycle

theorem proj_relCycle : RelCycle (Punctured 3) (realizeVia Pc 3 Phi3) := by
  rw [← chain_Hf1_eq_Pc]
  exact RelCycle.map Hf1 Snd (Punctured 3) Hf1_maps cX cX_relCycle

theorem cellAtSpace_T0_proj :
    AbF.map ((chainMap piR3).f 3) (cellAtSpace 3 T0) = realizeVia Pc 3 Phi3 := by
  change ((chainMap piR3).f 3).hom (realizeS 3 (coneData.phi 3 T0)) = _
  rw [realizeS_eq_via, chainMap_realizeVia]
  rfl

/-- **The local degree of the standard top cell is the local degree of its linearization**:
`dT0` is the class in `H₃(ℝ³, ℝ³ ∖ 0) ≅ ℚ` of the affine chain obtained by applying the linear map
`Q ↦ (-q₁₂, -q₂₃, -q₁₃)` (which has determinant `+1` in the coordinates `(q₁₂, q₁₃, q₂₃)`) to
the cone chain of the cell. -/
theorem dT0_eq_degRel_lin : dT0 = degRel (realizeVia Lc 3 Phi3) lin_relCycle := by
  have e1 : degπ (cellAtSpace 3 T0) cycle_T0 = degRel (realizeVia Pc 3 Phi3) proj_relCycle := by
    rw [degπ_eq_degRel]
    exact degRel_congr _ _ _ _ cellAtSpace_T0_proj
  unfold dT0
  rw [e1]
  unfold degRel
  congr 1
  have hh := relCls_homotopy Hf0 Hf1 Snd (Punctured 3) Hf0_maps Hf1_maps Hhom
    (fun t x hx => Hhom_maps t x hx) cX cX_relCycle
    (RelCycle.map Hf0 Snd _ Hf0_maps cX cX_relCycle) (RelCycle.map Hf1 Snd _ Hf1_maps cX cX_relCycle)
  calc relCls (Punctured 3) (realizeVia Pc 3 Phi3) proj_relCycle
      = relCls (Punctured 3) (AbF.map ((chainMap Hf1).f 3) cX)
          (RelCycle.map Hf1 Snd _ Hf1_maps cX cX_relCycle) :=
        relCls_congr _ _ _ _ _ chain_Hf1_eq_Pc.symm
    _ = relCls (Punctured 3) (AbF.map ((chainMap Hf0).f 3) cX)
          (RelCycle.map Hf0 Snd _ Hf0_maps cX cX_relCycle) := hh.symm
    _ = relCls (Punctured 3) (realizeVia Lc 3 Phi3) lin_relCycle :=
        relCls_congr _ _ _ _ _ chain_Hf0_eq_Lc

end T0

end TernaryPeriodPolynomials.Argument.Lemma33.Orient
