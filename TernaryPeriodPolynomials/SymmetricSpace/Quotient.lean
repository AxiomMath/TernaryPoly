module

public import TernaryPeriodPolynomials.SymmetricSpace.Model
public import TernaryPeriodPolynomials.SymmetricSpace.Positive
public import TernaryPeriodPolynomials.SymmetricSpace.Orientation

@[expose] public section


/-!
# The space `𝒳` of positive definite ternary forms modulo positive scaling, and the library's `SymmetricSpacePositive.Space`

Formalized by Claude Sonnet 5.5.

* `Forms`: the quotient of `{Q : Q positive definite}` (`PD`) by `Q ∼ c Q`, `c > 0`: the paper's `𝒳`.
* `normalizeEquiv : Pos1 ≃ Forms`: determinant-one representatives (`Q ↦ [Q]`, inverse `[Q] ↦ (det Q)^{-1/3} Q`).  Hence with `SymmetricSpaceModel.quotEquiv` the chain
  `SL₃(ℝ)/SO(3) ≃ {Q > 0, det Q = 1} ≃ 𝒳` of the paper, `g SO(3) ↦ [(g gᵗ)⁻¹]`, which is equivariant (`normalizeEquiv_smul`) for `g · [Q] = [g^{-t} Q g⁻¹]` (`formAct`, a
  `MulAction` of `GL₃(ℝ)` on `Forms`, restricted to `SL₃(ℝ)` through `toGL`).
* `congAct`: the congruence action `g · [P] = [g P gᵗ]` on Gram classes; `invForms`: `[Q] ↦ [Q⁻¹]`, an involution with `invForms (formAct g x) = congAct g (invForms x)`.
* `spaceEquiv : Space ≃ Forms` (compatibility with `TernaryPoly.SymmetricSpacePositive.Space`, the trace-one positive definite matrices): `S ↦ [S]`, inverse `[S] ↦ S/tr S`
  (`normalize`).  It is equivariant for the library's congruence `S ↦ g S gᵗ` (`TernaryPoly.SymmetricSpaceOrientation.congruence`) followed by the trace normalization: `spaceEquiv_act`.
  Through `invForms` the same bijection `Space ≃ 𝒳` takes this action to the paper's `g·Q = g^{-t} Q g⁻¹` (`spaceEquivQ_act`): `Q = S⁻¹` for a Gram representative `S`.
-/

open Matrix

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Identities.SymmetricSpace

abbrev GL3 : Type := Matrix.GeneralLinearGroup (Fin 3) ℝ

/-- Positive definite real ternary matrices. -/
def PD : Type := {Q : Mat // Q.PosDef}

@[ext] theorem PD.ext {Q R : PD} (h : Q.1 = R.1) : Q = R := Subtype.ext h

/-- Positive scaling. -/
def scaleSetoid : Setoid PD where
  r Q R := ∃ c : ℝ, 0 < c ∧ R.1 = c • Q.1
  iseqv := ⟨fun Q => ⟨1, one_pos, by simp⟩, fun {Q R} ⟨c, hc, h⟩ =>
      ⟨c⁻¹, inv_pos.mpr hc, by rw [h, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]⟩,
    fun {Q R S} ⟨c, hc, h⟩ ⟨d, hd, h'⟩ => ⟨d * c, mul_pos hd hc, by rw [h', h, smul_smul]⟩⟩

/-- The paper's `𝒳`: positive definite ternary forms modulo positive scaling. -/
def Forms : Type := Quotient scaleSetoid

def Forms.mk (Q : PD) : Forms := Quotient.mk scaleSetoid Q

theorem Forms.mk_eq_mk {Q R : PD} : Forms.mk Q = Forms.mk R ↔ ∃ c : ℝ, 0 < c ∧ R.1 = c • Q.1 :=
  Quotient.eq (r := scaleSetoid)

theorem Forms.ind {p : Forms → Prop} (h : ∀ Q : PD, p (Forms.mk Q)) : ∀ x, p x :=
  fun x => Quotient.inductionOn x h

theorem pd_smul (c : ℝ) (hc : 0 < c) (Q : PD) : (c • Q.1).PosDef := Q.2.smul hc

/-- Determinant-one representatives. -/
def Pos1.toPD (Q : Pos1) : PD := ⟨Q.1, Q.2.1⟩

theorem det_smul3 (c : ℝ) (Q : Mat) : (c • Q).det = c ^ 3 * Q.det := by
  rw [det_smul]; simp

theorem normalizeEquiv_inj {Q R : Pos1} (h : Forms.mk Q.toPD = Forms.mk R.toPD) : Q = R := by
  obtain ⟨c, hc, h⟩ := Forms.mk_eq_mk.mp h
  change R.1 = c • Q.1 at h
  have hdet := congrArg Matrix.det h
  rw [det_smul3, Q.2.2, R.2.2, mul_one] at hdet
  have hc1 : c = 1 := by
    have : c ^ 3 = 1 := hdet.symm
    exact (pow_eq_one_iff_of_nonneg hc.le (by norm_num)).mp this
  apply Pos1.ext
  rw [hc1, one_smul] at h
  exact h.symm

theorem exists_normalize (Q : PD) : ∃ R : Pos1, Forms.mk Q = Forms.mk R.toPD := by
  have hpos : 0 < Q.1.det := Q.2.det_pos
  set c : ℝ := Q.1.det ^ (-(1 / 3 : ℝ)) with hc
  have hcpos : 0 < c := Real.rpow_pos_of_pos hpos _
  have hc3 : c ^ 3 = Q.1.det⁻¹ := by
    rw [hc, ← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
    norm_num
    exact Real.rpow_neg_one _
  refine ⟨⟨c • Q.1, Q.2.smul hcpos, ?_⟩, ?_⟩
  · rw [det_smul3, hc3, inv_mul_cancel₀ hpos.ne']
  · apply Forms.mk_eq_mk.mpr
    exact ⟨c, hcpos, rfl⟩

/-- **`Pos1 ≃ 𝒳`:** determinant-one representatives of positive definite forms modulo scaling. -/
def normalizeEquiv : Pos1 ≃ Forms :=
  Equiv.ofBijective (fun Q => Forms.mk Q.toPD) ⟨fun _ _ h => normalizeEquiv_inj h, by
    intro x
    induction x using Forms.ind with
    | h Q =>
      obtain ⟨R, hR⟩ := exists_normalize Q
      exact ⟨R, hR.symm⟩⟩


/-- The inverse matrix of `g ∈ GL₃(ℝ)`. -/
def invU (g : GL3) : Mat := ((g⁻¹ : GL3) : Mat)

theorem isUnit_invU (g : GL3) : IsUnit (invU g) := Units.isUnit (g⁻¹)

/-- The left action `g · Q = g^{-t} Q g⁻¹` on positive definite forms. -/
def formActPD (g : GL3) (Q : PD) : PD :=
  ⟨(invU g)ᵀ * Q.1 * invU g, by
    have h := (Matrix.IsUnit.posDef_star_left_conjugate_iff (x := Q.1) (isUnit_invU g)).mpr Q.2
    simpa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using h⟩

theorem formActPD_compat (g : GL3) {Q R : PD} (h : scaleSetoid.r Q R) :
    scaleSetoid.r (formActPD g Q) (formActPD g R) := by
  obtain ⟨c, hc, h⟩ := h
  refine ⟨c, hc, ?_⟩
  change (invU g)ᵀ * R.1 * invU g = c • ((invU g)ᵀ * Q.1 * invU g)
  rw [h, Matrix.mul_smul, Matrix.smul_mul]

/-- The left action on `𝒳`. -/
def formAct (g : GL3) : Forms → Forms :=
  Quotient.map (sa := scaleSetoid) (sb := scaleSetoid) (formActPD g) (fun _ _ h => formActPD_compat g h)

theorem formAct_mk (g : GL3) (Q : PD) : formAct g (Forms.mk Q) = Forms.mk (formActPD g Q) := rfl

theorem invU_mul (g h : GL3) : invU (g * h) = invU h * invU g := by
  unfold invU
  rw [_root_.mul_inv_rev, Units.val_mul]

instance : MulAction GL3 Forms where
  smul := formAct
  one_smul x := by
    induction x using Forms.ind with
    | h Q =>
    show formAct 1 (Forms.mk Q) = Forms.mk Q
    rw [formAct_mk]
    congr 1
    apply PD.ext
    change (invU 1)ᵀ * Q.1 * invU 1 = Q.1
    have : invU 1 = 1 := by unfold invU; simp
    rw [this, transpose_one, Matrix.one_mul, Matrix.mul_one]
  mul_smul g h x := by
    induction x using Forms.ind with
    | h Q =>
    show formAct (g * h) (Forms.mk Q) = formAct g (formAct h (Forms.mk Q))
    rw [formAct_mk, formAct_mk, formAct_mk]
    congr 1
    apply PD.ext
    change (invU (g * h))ᵀ * Q.1 * invU (g * h) =
      (invU g)ᵀ * ((invU h)ᵀ * Q.1 * invU h) * invU g
    rw [invU_mul, transpose_mul]
    simp only [Matrix.mul_assoc]

/-- The congruence action `g · P = g P gᵗ` on Gram classes. -/
def congActPD (g : GL3) (P : PD) : PD :=
  ⟨(g : Mat) * P.1 * (g : Mat)ᵀ, by
    have h := (Matrix.IsUnit.posDef_star_right_conjugate_iff (x := P.1) (Units.isUnit g)).mpr P.2
    simpa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using h⟩

def congAct (g : GL3) : Forms → Forms :=
  Quotient.map (sa := scaleSetoid) (sb := scaleSetoid) (congActPD g) (fun _ _ ⟨c, hc, h⟩ =>
    ⟨c, hc, by
      change (g : Mat) * _ * (g : Mat)ᵀ = c • ((g : Mat) * _ * (g : Mat)ᵀ)
      rw [h, Matrix.mul_smul, Matrix.smul_mul]⟩)

theorem congAct_mk (g : GL3) (P : PD) : congAct g (Forms.mk P) = Forms.mk (congActPD g P) := rfl

theorem congAct_mul (g h : GL3) (x : Forms) : congAct (g * h) x = congAct g (congAct h x) := by
  induction x using Forms.ind with
  | h P =>
  rw [congAct_mk, congAct_mk, congAct_mk]
  congr 1
  apply PD.ext
  change ((g * h : GL3) : Mat) * P.1 * ((g * h : GL3) : Mat)ᵀ =
    (g : Mat) * ((h : Mat) * P.1 * (h : Mat)ᵀ) * (g : Mat)ᵀ
  rw [Units.val_mul, transpose_mul]
  simp only [Matrix.mul_assoc]

/-- Inversion of Gram classes and forms. -/
def invPD (Q : PD) : PD := ⟨Q.1⁻¹, Q.2.inv⟩

theorem inv_smul_mat (c : ℝ) (hc : c ≠ 0) (Q : PD) : (c • Q.1)⁻¹ = c⁻¹ • Q.1⁻¹ := by
  apply Matrix.inv_eq_right_inv
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hc, one_smul]
  exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp Q.2.isUnit)

def invForms : Forms → Forms :=
  Quotient.map (sa := scaleSetoid) (sb := scaleSetoid) invPD (fun Q R ⟨c, hc, h⟩ =>
    ⟨c⁻¹, inv_pos.mpr hc, by
      change R.1⁻¹ = c⁻¹ • Q.1⁻¹
      rw [h, inv_smul_mat c hc.ne' Q]⟩)

theorem invForms_mk (Q : PD) : invForms (Forms.mk Q) = Forms.mk (invPD Q) := rfl

theorem invForms_invForms (x : Forms) : invForms (invForms x) = x := by
  induction x using Forms.ind with
  | h Q =>
  rw [invForms_mk, invForms_mk]
  congr 1
  apply PD.ext
  exact Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp Q.2.isUnit)

/-- Inversion intertwines the left action on forms with congruence on Gram classes. -/
theorem invForms_formAct (g : GL3) (x : Forms) : invForms (formAct g x) = congAct g (invForms x) := by
  induction x using Forms.ind with
  | h Q =>
  rw [formAct_mk, invForms_mk, invForms_mk, congAct_mk]
  congr 1
  apply PD.ext
  change ((invU g)ᵀ * Q.1 * invU g)⁻¹ = (g : Mat) * Q.1⁻¹ * (g : Mat)ᵀ
  have hg : IsUnit (g : Mat).det := (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit g)
  have hgT : IsUnit ((g : Mat)ᵀ).det := by rw [det_transpose]; exact hg
  have hinv : invU g = (g : Mat)⁻¹ := Matrix.coe_units_inv g
  rw [hinv, Matrix.transpose_nonsing_inv, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
    Matrix.nonsing_inv_nonsing_inv _ hg, Matrix.nonsing_inv_nonsing_inv _ hgT]
  simp only [Matrix.mul_assoc]

theorem congAct_invForms (g : GL3) (x : Forms) : invForms (congAct g x) = formAct g (invForms x) := by
  have h := invForms_formAct g (invForms x)
  rw [invForms_invForms] at h
  rw [← invForms_invForms (formAct g (invForms x)), h]

/-- Inversion as an equivalence of `𝒳`. -/
def invEquiv : Forms ≃ Forms where
  toFun := invForms
  invFun := invForms
  left_inv := invForms_invForms
  right_inv := invForms_invForms

/-- **`𝒳 ≅ SL₃(ℝ)/SO(3)` of the paper:** `g SO(3) ↦ [(g gᵗ)⁻¹]`. -/
def cosetEquiv : SL3 ⧸ SO3 ≃ Forms := quotEquiv.trans normalizeEquiv

theorem normalizeEquiv_smul (h : SL3) (Q : Pos1) :
    normalizeEquiv (h • Q) = (Matrix.SpecialLinearGroup.toGL h) • normalizeEquiv Q := by
  change Forms.mk (h • Q).toPD = formAct (Matrix.SpecialLinearGroup.toGL h) (Forms.mk Q.toPD)
  rw [formAct_mk]
  congr 1

/-- **Equivariance of `𝒳 ≅ SL₃(ℝ)/SO(3)`:** left multiplication on cosets is `g · [Q] = [g^{-t} Q g⁻¹]`. -/
theorem cosetEquiv_smul (h : SL3) (x : SL3 ⧸ SO3) :
    cosetEquiv (h • x) = (Matrix.SpecialLinearGroup.toGL h) • cosetEquiv x := by
  change normalizeEquiv (quotEquiv (h • x)) = (Matrix.SpecialLinearGroup.toGL h) • normalizeEquiv (quotEquiv x)
  rw [quotEquiv_smul, normalizeEquiv_smul]

/-! ### Compatibility with `TernaryPoly.SymmetricSpacePositive.Space` -/

open TernaryPoly.SymmetricSpacePositive in
/-- The library's trace-one positive definite matrices, as classes of `𝒳`. -/
def spacePD (S : Space) : PD := ⟨S.1, S.2.1⟩

open TernaryPoly.SymmetricSpacePositive in
def spaceToForms (S : Space) : Forms := Forms.mk (spacePD S)

open TernaryPoly.SymmetricSpacePositive in
theorem spaceToForms_inj {S T : Space} (h : spaceToForms S = spaceToForms T) : S = T := by
  obtain ⟨c, hc, h⟩ := Forms.mk_eq_mk.mp h
  change T.1 = c • S.1 at h
  have htr := congrArg Matrix.trace h
  rw [trace_smul, S.2.2, T.2.2, smul_eq_mul, mul_one] at htr
  apply Subtype.ext
  rw [h, ← htr, one_smul]

open TernaryPoly.SymmetricSpacePositive in
theorem spaceToForms_surj (x : Forms) : ∃ S : Space, spaceToForms S = x := by
  induction x using Forms.ind with
  | h Q =>
  refine ⟨⟨normalize Q.1, normalize_mem Q.1 Q.2⟩, ?_⟩
  apply Forms.mk_eq_mk.mpr
  refine ⟨Q.1.trace, Q.2.trace_pos, ?_⟩
  change Q.1 = Q.1.trace • (Q.1.trace⁻¹ • Q.1)
  rw [smul_smul, mul_inv_cancel₀ Q.2.trace_pos.ne', one_smul]

open TernaryPoly.SymmetricSpacePositive in
/-- **(c):** the trace-one positive definite matrices of the library are `𝒳`: `S ↦ [S]`, inverse `[S] ↦ S/tr S`. -/
def spaceEquiv : Space ≃ Forms :=
  Equiv.ofBijective spaceToForms ⟨fun _ _ h => spaceToForms_inj h, fun x => spaceToForms_surj x⟩

open TernaryPoly.SymmetricSpacePositive in
/-- The congruence action `S ↦ g S gᵗ` of the library (`TernaryPoly.SymmetricSpaceOrientation.congruence`), followed by the trace normalization, on `Space`. -/
def spaceAct (g : GL3) (S : Space) : Space :=
  ⟨normalize ((g : Mat) * S.1 * (g : Mat)ᵀ), normalize_mem _ (congActPD g (spacePD S)).2⟩

open TernaryPoly.SymmetricSpacePositive in
theorem spaceAct_val (g : GL3) (S : Space) :
    (spaceAct g S).1 = normalize ((g : Mat) * S.1 * (g : Mat)ᵀ) := rfl

open TernaryPoly.SymmetricSpacePositive in
/-- `spaceAct` is the library's `congruence` followed by `normalize`: the symmetric matrix `S` is a point of `TernaryPoly.SymmetricSpaceOrientation.Symmetric`. -/
theorem spaceAct_eq_congruence (g : GL3) (S : Space) (hS : S.1.IsSymm) :
    (spaceAct g S).1 = normalize (TernaryPoly.SymmetricSpaceOrientation.congruence (g : Mat) ⟨S.1, hS⟩).val :=
  rfl

open TernaryPoly.SymmetricSpacePositive in
/-- **(c), equivariance:** under `S ↦ [S]` the library's congruence action on `Space` is the congruence action on Gram classes. -/
theorem spaceEquiv_act (g : GL3) (S : Space) : spaceEquiv (spaceAct g S) = congAct g (spaceEquiv S) := by
  change spaceToForms (spaceAct g S) = congAct g (Forms.mk (spacePD S))
  rw [congAct_mk]
  apply Forms.mk_eq_mk.mpr
  have hpos : 0 < ((g : Mat) * S.1 * (g : Mat)ᵀ).trace := (congActPD g (spacePD S)).2.trace_pos
  refine ⟨((g : Mat) * S.1 * (g : Mat)ᵀ).trace, hpos, ?_⟩
  change (g : Mat) * S.1 * (g : Mat)ᵀ =
    ((g : Mat) * S.1 * (g : Mat)ᵀ).trace •
      (TernaryPoly.SymmetricSpacePositive.normalize ((g : Mat) * S.1 * (g : Mat)ᵀ))
  rw [TernaryPoly.SymmetricSpacePositive.normalize, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]

open TernaryPoly.SymmetricSpacePositive in
/-- **(c), the paper's action:** through `Q = S⁻¹` the same bijection `Space ≃ 𝒳` carries the congruence action to `g·Q = g^{-t} Q g⁻¹`. -/
def spaceEquivQ : Space ≃ Forms := spaceEquiv.trans invEquiv

open TernaryPoly.SymmetricSpacePositive in
theorem spaceEquivQ_act (g : GL3) (S : Space) :
    spaceEquivQ (spaceAct g S) = formAct g (spaceEquivQ S) := by
  change invForms (spaceEquiv (spaceAct g S)) = formAct g (invForms (spaceEquiv S))
  rw [spaceEquiv_act, congAct_invForms]

end TernaryPeriodPolynomials.Argument.Identities.SymmetricSpace
