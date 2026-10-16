module

public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.Line.Face
public import TernaryPeriodPolynomials.EisensteinSeries.Class.RestAverage
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Unfold.K

@[expose] public section


/-!
# The line face: the translated face pullback of a summand is the face pullback of the summand at
`γ qMat w`

The face model of the line cusp `Q` is `jFace x = jPlane (ptOf x)` (the `LineFace`). A translation of the
face by `w` is the action of the radical element `qMat w` on `Ω` (`jFace_shift`); hence for a summand
`S(γ) = ρ(γ)⁻¹ γ^* ω` the radical-twisted translate of its face pullback is the face pullback of the
summand at `γ qMat w` (`rho_fPull_shift`):

  `ρ(qMat (-w)) (jFace^* S(γ)) (x + w) = jFace^* S(γ qMat w) (x)`.

Formalized by Claude Sonnet 5.5.
-/

open MvPolynomial
open scoped MatrixGroups ContDiff
noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.SeedC3S4c
  TernaryPeriodPolynomials.Argument.SeedC3.Psi TernaryPoly.SmoothLocalDeRham
  TernaryPeriodPolynomials.Argument.FormClassK TernaryPeriodPolynomials.Argument.EisensteinDual
  TernaryPeriodPolynomials.Argument.GammaNFaces

/-! ### Real equivariance of the plane involution -/

theorem jPlane_equivariant_real {g : Matrix (Fin 3) (Fin 3) ℝ} (hg : g.det = 1)
    {p : Fin 5 → ℝ} (hp : p ∈ Omega) :
    jPlane (planeAct g p) = planeAct (rt g⁻¹) (jPlane p) := by
  have hgu : IsUnit g.det := by rw [hg]; exact isUnit_one
  have hG := planeGram_isGram hp
  have hGu : IsUnit (planeGram p).det := by rw [hG.2]; exact isUnit_one
  unfold jPlane
  rw [planeGram_planeAct hg hp]
  unfold planeAct
  rw [planeGram_planePoint (isGram_jGram hG), rt_transpose]
  congr 1
  unfold jGram
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, ← Matrix.transpose_nonsing_inv]
  rw [← rt_mul, ← rt_mul]

/-- **A translation of the face is the action of `qMat w` on the line-face model.** -/
theorem jFace_shift {x : Face} (hx : x ∈ faceSet) (w : Fin 2 → ℝ) :
    jFace (x + shVec w) = planeAct (qMat w) (jFace x) := by
  have hp : ptOf x ∈ Omega := ptOf_mem hx
  have e1 : ptOf (x + shVec w) = planeAct (transMat (w 0) (w 1)) (ptOf x) := by
    rw [ptOf_shVec, planeAct_transMat _ _ hp]
  have hdet : (transMat (w 0) (w 1)).det = 1 := det_transMat _ _
  unfold jFace
  rw [e1, jPlane_equivariant_real hdet hp, transMat_inv, ← qMat_eq_rt]

/-! ### Pullbacks of component families along maps of the face -/

/-- The pullback of a polynomial-valued two-form (given by components on `Ω`) along a map from the
face: `(Φ^*W)(e_i, e_j) = Σ_{a,b} ∂_iΦ_a ∂_jΦ_b W_{ab}(Φ x)`. -/
def fPull (Φ : Face → Fin 5 → ℝ)
    (W : (Fin 5 → ℝ) → Fin 5 → Fin 5 → MvPolynomial (Fin 3) ℂ) (x : Face) (i j : Fin 4) :
    MvPolynomial (Fin 3) ℂ :=
  ∑ a : Fin 5, ∑ b : Fin 5,
    C (((fderiv ℝ Φ x (Pi.single i 1) a * fderiv ℝ Φ x (Pi.single j 1) b : ℝ) : ℂ)) * W (Φ x) a b

/-- **Chain rule for `fPull`.** -/
theorem fPull_comp (Φ₁ : Face → Fin 5 → ℝ) (Φ₂ : (Fin 5 → ℝ) → (Fin 5 → ℝ))
    (W : (Fin 5 → ℝ) → Fin 5 → Fin 5 → MvPolynomial (Fin 3) ℂ) (x : Face)
    (h₁ : DifferentiableAt ℝ Φ₁ x) (h₂ : DifferentiableAt ℝ Φ₂ (Φ₁ x)) (i j : Fin 4) :
    fPull (Φ₂ ∘ Φ₁) W x i j = fPull Φ₁ (formPullback Φ₂ W) x i j := by
  have hD : ∀ (i : Fin 4) (c : Fin 5), fderiv ℝ (Φ₂ ∘ Φ₁) x (Pi.single i 1) c =
      ∑ a : Fin 5, fderiv ℝ Φ₁ x (Pi.single i 1) a * fderiv ℝ Φ₂ (Φ₁ x) (Pi.single a 1) c := by
    intro i c
    rw [fderiv_comp x h₂ h₁, ContinuousLinearMap.comp_apply]
    exact linear_apply_eq_sum (fderiv ℝ Φ₂ (Φ₁ x)) _ c
  unfold fPull
  simp only [hD, Function.comp_apply]
  exact comp_alg (fun a => fderiv ℝ Φ₁ x (Pi.single i 1) a) (fun b => fderiv ℝ Φ₁ x (Pi.single j 1) b)
    (fun a c => fderiv ℝ Φ₂ (Φ₁ x) (Pi.single a 1) c)
    (fun c d => W (Φ₂ (Φ₁ x)) c d)

theorem differentiableAt_jFace {x : Face} (hx : x ∈ faceSet) : DifferentiableAt ℝ jFace x :=
  diffAt_of_contDiffOn isOpen_faceSet contDiffOn_jFace hx

/-- **Key identity**: the `ρ(qMat(-w))`-twisted translate of the face pullback of a summand is the face
pullback of the summand at `γ qMat w`. -/
theorem rho_fPull_shift (n : ℕ) (h : ℂ → ℂ) {g : Matrix (Fin 3) (Fin 3) ℝ} (hg : g.det = 1)
    {x : Face} (hx : x ∈ faceSet) (w : Fin 2 → ℝ) (i j : Fin 4) :
    rho (qMat (-w)) (fPull jFace (fun y a b => summandPoly n h g y a b) (x + shVec w) i j) =
      fPull jFace (fun y a b => summandPoly n h (g * qMat w) y a b) x i j := by
  have hxw : x + shVec w ∈ faceSet := shVec_mem hx w
  have hy₀ : jFace x ∈ Omega := jPlane_mem (ptOf_mem hx)
  have hQ : (qMat w).det = 1 := det_qMat w
  have hev : (jFace ∘ fun z => z + shVec w) =ᶠ[nhds x] planeAct (qMat w) ∘ jFace :=
    Filter.eventuallyEq_of_mem (isOpen_faceSet.mem_nhds hx) fun z hz => by
      simp only [Function.comp]
      exact jFace_shift hz w
  have hD : fderiv ℝ jFace (x + shVec w) = fderiv ℝ (planeAct (qMat w) ∘ jFace) x := by
    rw [← hev.fderiv_eq]
    have := fderiv_comp_add_right (𝕜 := ℝ) (shVec w) (f := jFace) (x := x)
    simpa [Function.comp_def] using this.symm
  have hpt : jFace (x + shVec w) = (planeAct (qMat w) ∘ jFace) x := jFace_shift hx w
  have hdiff : DifferentiableAt ℝ (planeAct (qMat w)) (jFace x) := differentiableAt_planeAct hQ hy₀
  have e1 : fPull jFace (fun y a b => summandPoly n h g y a b) (x + shVec w) i j =
      fPull (planeAct (qMat w) ∘ jFace) (fun y a b => summandPoly n h g y a b) x i j := by
    unfold fPull
    rw [hD, hpt]
  rw [e1, fPull_comp jFace (planeAct (qMat w)) _ x (differentiableAt_jFace hx) hdiff]
  unfold fPull
  rw [rho_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [rho_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  beta_reduce
  rw [rho_C_mul, summandPoly_mul_eq n h hg hQ hy₀ a b, qMat_inv]

/-! ### Coordinates of the face pullback and of the series -/

section Coordinates

variable (N : ℕ) [NeZero N] (n : ℕ)

omit [NeZero N] in
/-- Coordinates of the pullback to the line-face model of a closed equivariant form given by components. -/
theorem toPoly_lineFaceForm_basis (W : InvComponents (gammaN N) n) {x : Face} (hx : x ∈ faceSet)
    (i j : Fin 4) :
    Coef.toPoly ((((lineFaceForm N n W.toInv : ZigZag.invClosed isOpen_faceSet
        (gammaNPlaneData N).action (rhoQ N n)) : Form (F := Coef n) faceSet 2) :
          RawForm Face (Coef n) 2) x ![Pi.single i 1, Pi.single j 1]) =
      fPull jFace (fun y a b => Coef.toPoly (W.comp y a b)) x i j := by
  have hΩ : jFace x ∈ Omega := jPlane_mem (ptOf_mem hx)
  change Coef.toPoly ((pullBack isOpen_faceSet (lineFaceMap N).smooth (lineFaceMap N).mapsTo 2
    W.form : RawForm Face (Coef n) 2) x _) = _
  rw [pullBack_apply isOpen_faceSet _ _ _ hx]
  change Coef.toPoly (((W.form : RawForm (Fin 5 → ℝ) (Coef n) 2) (jFace x)).compContinuousLinearMap
    (fderiv ℝ jFace x) ![Pi.single i 1, Pi.single j 1]) = _
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply, W.form_apply hΩ]
  have : (⇑(fderiv ℝ jFace x) ∘ ![Pi.single i 1, Pi.single j 1]) =
      ![fderiv ℝ jFace x (Pi.single i 1), fderiv ℝ jFace x (Pi.single j 1)] := by
    funext k; fin_cases k <;> rfl
  rw [this, InvComponents.raw, altCLM_apply, altRaw_apply_of_antisymm _ (W.anti _),
    toPoly_finsetSum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [toPoly_finsetSum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Complex.coe_smul, Coef.toPoly_smul]
  simp

omit [NeZero N] in
/-- Coefficientwise tsum interchange for exchanging a rotation `ρ(G)` with a coefficientwise sum. -/
theorem coeff_rho_tsum {ι : Type*} (G : Matrix (Fin 3) (Fin 3) ℝ) {n : ℕ}
    (Q : MvPolynomial (Fin 3) ℂ) (P : ι → MvPolynomial (Fin 3) ℂ) (hQ : Q.IsHomogeneous n)
    (hP : ∀ c, (P c).IsHomogeneous n) (hsum : ∀ m' : Fin 3 →₀ ℕ, Summable fun c => (P c).coeff m')
    (hQc : ∀ m', Q.coeff m' = ∑' c, (P c).coeff m') (m : Fin 3 →₀ ℕ) :
    (rho G Q).coeff m = ∑' c, (rho G (P c)).coeff m := by
  rw [coeff_rho_expansion hQ G m]
  simp_rw [coeff_rho_expansion (hP _) G m]
  simp_rw [hQc]
  rw [Summable.tsum_finsetSum (fun m' _ => (hsum m').mul_right _)]
  refine Finset.sum_congr rfl fun m' _ => ?_
  rw [tsum_mul_right]

end Coordinates

section SeriesCoordinates

variable (N : ℕ) [NeZero N] (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))

omit [NeZero N] in
theorem fPull_isHomogeneous (Φ : Face → Fin 5 → ℝ)
    (W : (Fin 5 → ℝ) → Fin 5 → Fin 5 → MvPolynomial (Fin 3) ℂ)
    (hW : ∀ y a b, (W y a b).IsHomogeneous n) (x : Face) (i j : Fin 4) :
    (fPull Φ W x i j).IsHomogeneous n := by
  unfold fPull
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun a _ => ?_
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun b _ => ?_
  exact (hW _ a b).C_mul _

/-- The coefficient of the face pullback of the summand of a coset, as a function of the coset. -/
theorem summable_coeff_fPull (hn : 4 ≤ n) (Φ : Face → Fin 5 → ℝ) {x : Face} (hΦ : Φ x ∈ Omega) (i j : Fin 4)
    (m' : Fin 3 →₀ ℕ) :
    Summable fun c : PlaneCoset (gammaN N) =>
      (fPull Φ (fun y a b => summandPoly n (hfun f) (realMat (Quotient.out c).1) y a b) x i j).coeff m' := by
  have : ∀ c : PlaneCoset (gammaN N),
      (fPull Φ (fun y a b => summandPoly n (hfun f) (realMat (Quotient.out c).1) y a b) x i j).coeff m' =
        ∑ a : Fin 5, ∑ b : Fin 5, (((fderiv ℝ Φ x (Pi.single i 1) a * fderiv ℝ Φ x (Pi.single j 1) b : ℝ) : ℂ)) *
          termFun (gammaN N) n f c a b m' (Φ x) := by
    intro c
    unfold fPull
    simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul]
    rfl
  simp_rw [this]
  exact summable_sum fun a _ => summable_sum fun b _ =>
    (summable_termFun_val (gammaN N) (leviGroup N) n f hn hΦ a b m').mul_left _

/-- The face pullback of the series is the sum of the face pullbacks of the summands. -/
theorem coeff_fPull_series (hn : 4 ≤ n) (Φ : Face → Fin 5 → ℝ) {x : Face} (hΦ : Φ x ∈ Omega) (i j : Fin 4)
    (m' : Fin 3 →₀ ℕ) :
    (fPull Φ (fun y a b => seriesForm (gammaN N) n f y a b) x i j).coeff m' =
      ∑' c : PlaneCoset (gammaN N),
        (fPull Φ (fun y a b => summandPoly n (hfun f) (realMat (Quotient.out c).1) y a b) x i j).coeff m' := by
  have hc : ∀ c : PlaneCoset (gammaN N),
      (fPull Φ (fun y a b => summandPoly n (hfun f) (realMat (Quotient.out c).1) y a b) x i j).coeff m' =
        ∑ a : Fin 5, ∑ b : Fin 5, (((fderiv ℝ Φ x (Pi.single i 1) a * fderiv ℝ Φ x (Pi.single j 1) b : ℝ) : ℂ)) *
          termFun (gammaN N) n f c a b m' (Φ x) := by
    intro c
    unfold fPull
    simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul]
    rfl
  simp_rw [hc]
  rw [Summable.tsum_finsetSum (fun a _ => summable_sum fun b _ =>
    (summable_termFun_val (gammaN N) (leviGroup N) n f hn hΦ a b m').mul_left _)]
  unfold fPull
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Summable.tsum_finsetSum (fun b _ =>
    (summable_termFun_val (gammaN N) (leviGroup N) n f hn hΦ a b m').mul_left _)]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [tsum_mul_left, coeff_seriesForm]
  rfl

end SeriesCoordinates

section Integrand

open TernaryPeriodPolynomials.Argument.Statements.EisensteinClass TernaryPeriodPolynomials.Argument.Statements.ConvergenceC4

variable (N : ℕ) [NeZero N] (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))

/-- **The coefficient of the face pullback, along `jFace`, of the summand of the coset `c` at
`γ_c · qMat w`.** -/
def PhiQ (x : Face) (p q : Fin 4) (m : Fin 3 →₀ ℕ) (c : PlaneCoset (gammaN N)) (w : Fin 2 → ℝ) : ℂ :=
  (fPull jFace (fun y a b => summandPoly n (hfun f) (realMat (Quotient.out c).1 * qMat w) y a b)
    x p q).coeff m

/-- **The averaged integrand is the sum over the cosets of `PhiQ`**: the `m`-th coefficient of
`ρ(qMat (-w)) (jFace^* 𝓔)(x + w)(e_p, e_q)` is `Σ'_c PhiQ c w`. -/
theorem coeff_avIntegrand (hn : 4 ≤ n) {x : Face} (hx : x ∈ faceSet) (w : Fin 2 → ℝ) (p q : Fin 4)
    (m : Fin 3 →₀ ℕ) :
    polyCoefCLM n m (sQ n (-w)
      ((((lineFaceForm N n (planeEisensteinInv (gammaN N) (leviGroup N) n f hn (leviIn_gammaN N)) :
        ZigZag.invClosed isOpen_faceSet (gammaNPlaneData N).action (rhoQ N n)) :
          Form (F := Coef n) faceSet 2) : RawForm Face (Coef n) 2) (x + shVec w)
            ![Pi.single p 1, Pi.single q 1])) =
      ∑' c : PlaneCoset (gammaN N), PhiQ N n f x p q m c w := by
  have hxw : x + shVec w ∈ faceSet := shVec_mem hx w
  have hy₁ : jFace (x + shVec w) ∈ Omega := jPlane_mem (ptOf_mem hxw)
  rw [polyCoefCLM_apply, toPoly_sQ]
  unfold planeEisensteinInv
  rw [toPoly_lineFaceForm_basis N n _ hxw p q]
  have hQ : (fPull jFace (fun y a b => Coef.toPoly
      ((planeEisensteinComponents (gammaN N) (leviGroup N) n f hn (leviIn_gammaN N)).comp y a b))
      (x + shVec w) p q).IsHomogeneous n :=
    fPull_isHomogeneous n jFace _ (fun y a b => seriesForm_isHomogeneous (gammaN N) n f y a b) _ _ _
  have hP : ∀ c : PlaneCoset (gammaN N), (fPull jFace (fun y a b => summandPoly n (hfun f)
      (realMat (Quotient.out c).1) y a b) (x + shVec w) p q).IsHomogeneous n := fun c =>
    fPull_isHomogeneous n jFace _ (fun y a b => summandPoly_isHomogeneous n (hfun f) (det_realMat _) y a b) _ _ _
  rw [coeff_rho_tsum (qMat (-w)) _ _ hQ hP
    (fun m' => summable_coeff_fPull N n f hn jFace hy₁ p q m')
    (fun m' => coeff_fPull_series N n f hn jFace hy₁ p q m') m]
  refine tsum_congr fun c => ?_
  unfold PhiQ
  rw [← rho_fPull_shift n (hfun f) (det_realMat (Quotient.out c).1) hx w p q]

end Integrand

end TernaryPeriodPolynomials.Argument.EisensteinClass




