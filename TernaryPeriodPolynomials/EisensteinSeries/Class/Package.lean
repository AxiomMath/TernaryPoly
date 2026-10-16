module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Setup
public import TernaryPeriodPolynomials.EisensteinSeries.Class.AltForm
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.PolyCalcCoef
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.SeedTheta
public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.ClosedTerms

@[expose] public section


/-!
# Packaging a closed equivariant component family as an element of `ZigZag.invClosed`

Paper: Proposition C.4: the series `ℰ_P(ω_h)` "defines a smooth closed global two-form with values in `E`, which
is `Γ`-equivariant", and.

An `InvComponents Γ n` is a family of components `W y a b ∈ E_n` (`Coef n`), antisymmetric in
`(a, b)`, with smooth coefficients on `Ω`, closed in the coordinate sense of the `seed_closed_equivariant`
(`coordPartial`), and satisfying the transformation law `δ^* W = ρ(δ) W` of Proposition C.4 for
`δ ∈ Γ` (in the coordinate form `formPullback`). `InvComponents.toInv` assembles the chart form
`Σ Wₐᵦ dyₐ ∧ dy_b` and proves that it is closed (`dω = 0` in Mathlib's exterior derivative) and
`ρ`-equivariant (`δ^*ω = ρ(δ)ω` in the zig-zag's pullback and twist), i.e. an element of
`ZigZag.invClosed isOpen_Omega (gammaAct Γ) (gammaRho Γ n)` whose coordinates are the `W y a b`
(`toInv_basis`).

Formalized by Claude Sonnet 5.5.
-/

open MvPolynomial
open scoped ContDiff

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPoly.SmoothLocalDeRham TernaryPoly.SmoothCoveringDeRham

theorem toPoly_finsetSum {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Coef n) :
    Coef.toPoly (∑ i ∈ s, f i) = ∑ i ∈ s, Coef.toPoly (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Coef.toPoly_add, ih]

/-- A family of `E_n`-valued components on `Ω`: antisymmetric, coefficientwise smooth, closed, and
equivariant under `Γ` (Proposition C.4 in coordinates). -/
structure InvComponents (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ)) (n : ℕ) where
  /-- The components `W(∂ₐ, ∂_b)` at the point `y`. -/
  comp : (Fin 5 → ℝ) → Fin 5 → Fin 5 → Coef n
  anti : ∀ y a b, comp y a b = - comp y b a
  smooth : ∀ (i j : Fin 5) (m : Fin 3 →₀ ℕ),
    ContDiffOn ℝ ∞ (fun y => (Coef.toPoly (comp y i j)).coeff m) Omega
  closed : ∀ x ∈ Omega, ∀ (m : Fin 3 →₀ ℕ) (i j k : Fin 5),
    coordPartial (fun q => (Coef.toPoly (comp q j k)).coeff m) i x -
      coordPartial (fun q => (Coef.toPoly (comp q i k)).coeff m) j x +
      coordPartial (fun q => (Coef.toPoly (comp q i j)).coeff m) k x = 0
  equiv : ∀ δ : Γ, ∀ x ∈ Omega, ∀ i j : Fin 5,
    formPullback (planeAct (realMat δ.1)) (fun y a b => Coef.toPoly (comp y a b)) x i j =
      rho (realMat δ.1) (Coef.toPoly (comp x i j))

variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ)} {n : ℕ}

namespace InvComponents

variable (W : InvComponents Γ n)

theorem contDiffOn_comp (i j : Fin 5) : ContDiffOn ℝ ∞ (fun y => W.comp y i j) Omega := by
  refine Calc.contDiffOn_of_vec n ?_
  rw [contDiffOn_pi]
  intro e
  exact W.smooth i j (Finsupp.equivFunOnFinite.symm (fun k => (e k : ℕ)))

/-- The ambient representative of the two-form: the alternating map with components `W y`. -/
def raw (y : Fin 5 → ℝ) : (Fin 5 → ℝ) [⋀^Fin 2]→L[ℝ] Coef n := altCLM (fun a b => W.comp y a b)

theorem contDiffOn_raw : ContDiffOn ℝ ∞ W.raw Omega := by
  have h : ContDiffOn ℝ ∞ (fun y => fun a b => W.comp y a b) Omega :=
    contDiffOn_pi.2 fun a => contDiffOn_pi.2 fun b => W.contDiffOn_comp a b
  exact altCLM.contDiff.comp_contDiffOn h

/-- The chart two-form with components `W`. -/
def form : Form (F := Coef n) Omega 2 := restrictForm Omega W.raw W.contDiffOn_raw

theorem form_apply {x : Fin 5 → ℝ} (hx : x ∈ Omega) :
    (W.form : RawForm (Fin 5 → ℝ) (Coef n) 2) x = W.raw x :=
  restrictForm_apply W.raw W.contDiffOn_raw hx

theorem raw_basis (y : Fin 5 → ℝ) (i j : Fin 5) :
    W.raw y ![Pi.single i 1, Pi.single j 1] = W.comp y i j :=
  altRaw_basis_of_antisymm _ (W.anti y) i j

theorem differentiableAt_comp {x : Fin 5 → ℝ} (hx : x ∈ Omega) (i j : Fin 5) :
    DifferentiableAt ℝ (fun y => W.comp y i j) x :=
  ((W.contDiffOn_comp i j x hx).contDiffAt (isOpen_Omega.mem_nhds hx)).differentiableAt (by simp)

theorem differentiableAt_coeff {x : Fin 5 → ℝ} (hx : x ∈ Omega) (i j : Fin 5)
    (m : Fin 3 →₀ ℕ) :
    DifferentiableAt ℝ (fun y => (Coef.toPoly (W.comp y i j)).coeff m) x :=
  ((W.smooth i j m x hx).contDiffAt (isOpen_Omega.mem_nhds hx)).differentiableAt (by simp)

/-! ### Closedness -/

theorem vec_fderiv {f : (Fin 5 → ℝ) → Coef n} {x : Fin 5 → ℝ} (hf : DifferentiableAt ℝ f x)
    (v : Fin 5 → ℝ) (e : Fin 3 → Fin (n + 1)) :
    Coef.vec n (fderiv ℝ f x v) e = fderiv ℝ (fun y => Coef.vec n (f y) e) x v := by
  let L : Coef n →L[ℝ] ℂ := (ContinuousLinearMap.proj e).comp (Calc.vecCLM n)
  have h := (L.hasFDerivAt (x := f x)).comp x hf.hasFDerivAt
  exact (congrArg (fun T => T v) h.fderiv).symm

/-- Closedness in `E_n`: `∂ₐW_{bc} - ∂_bW_{ac} + ∂_cW_{ab} = 0`. -/
theorem closed_fderiv {x : Fin 5 → ℝ} (hx : x ∈ Omega) (a b c : Fin 5) :
    fderiv ℝ (fun y => W.comp y b c) x (Pi.single a 1) -
      fderiv ℝ (fun y => W.comp y a c) x (Pi.single b 1) +
      fderiv ℝ (fun y => W.comp y a b) x (Pi.single c 1) = 0 := by
  apply Coef.vec_injective
  ext e
  have hcl := W.closed x hx (Finsupp.equivFunOnFinite.symm (fun k => (e k : ℕ))) a b c
  rw [coordPartial_eq_fderiv (W.differentiableAt_coeff hx b c _),
    coordPartial_eq_fderiv (W.differentiableAt_coeff hx a c _),
    coordPartial_eq_fderiv (W.differentiableAt_coeff hx a b _)] at hcl
  simp only [map_add, map_sub, Pi.add_apply, Pi.sub_apply, map_zero, Pi.zero_apply]
  rw [vec_fderiv (W.differentiableAt_comp hx b c), vec_fderiv (W.differentiableAt_comp hx a c),
    vec_fderiv (W.differentiableAt_comp hx a b)]
  exact hcl

theorem differentiableAt_raw {x : Fin 5 → ℝ} (hx : x ∈ Omega) : DifferentiableAt ℝ W.raw x :=
  ((W.contDiffOn_raw x hx).contDiffAt (isOpen_Omega.mem_nhds hx)).differentiableAt (by simp)

theorem extDeriv_raw_eq_zero {x : Fin 5 → ℝ} (hx : x ∈ Omega) : extDeriv W.raw x = 0 := by
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  refine (Pi.basisFun ℝ (Fin 5)).ext_alternating ?_
  intro vv _
  have hd := W.differentiableAt_raw hx
  set v : Fin 3 → (Fin 5 → ℝ) := fun i => Pi.single (vv i) 1 with hv
  have h0 : (fun y => W.raw y (Fin.removeNth 0 v)) = fun y => W.comp y (vv 1) (vv 2) := by
    funext y
    have : Fin.removeNth 0 v = ![Pi.single (vv 1) 1, Pi.single (vv 2) 1] := by
      funext j; fin_cases j <;> rfl
    rw [this, W.raw_basis]
  have h1 : (fun y => W.raw y (Fin.removeNth 1 v)) = fun y => W.comp y (vv 0) (vv 2) := by
    funext y
    have : Fin.removeNth 1 v = ![Pi.single (vv 0) 1, Pi.single (vv 2) 1] := by
      funext j; fin_cases j <;> rfl
    rw [this, W.raw_basis]
  have h2 : (fun y => W.raw y (Fin.removeNth 2 v)) = fun y => W.comp y (vv 0) (vv 1) := by
    funext y
    have : Fin.removeNth 2 v = ![Pi.single (vv 0) 1, Pi.single (vv 1) 1] := by
      funext j; fin_cases j <;> rfl
    rw [this, W.raw_basis]
  simp only [Pi.basisFun_apply]
  change extDeriv W.raw x v = (0 : Coef n)
  rw [extDeriv_apply hd, Fin.sum_univ_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, h0, h1, h2, pow_zero, one_smul, pow_one,
    neg_smul, even_two.neg_one_pow]
  have := W.closed_fderiv hx (vv 0) (vv 1) (vv 2)
  rw [← this]
  simp only [hv]
  abel

theorem d_form : d isOpen_Omega 2 W.form = 0 := by
  apply Form.ext
  intro x hx
  rw [d_apply isOpen_Omega _ hx]
  have heq : (W.form : RawForm (Fin 5 → ℝ) (Coef n) 2) =ᶠ[nhds x] W.raw := by
    filter_upwards [isOpen_Omega.mem_nhds hx] with y hy using W.form_apply hy
  rw [heq.extDeriv_eq (𝕜 := ℝ), W.extDeriv_raw_eq_zero hx]
  rfl

/-! ### Equivariance -/

theorem toPoly_raw_pullback (δ : Γ) (x : Fin 5 → ℝ) (i j : Fin 5) :
    Coef.toPoly (W.raw (planeAct (realMat δ.1) x)
        ![fderiv ℝ (planeAct (realMat δ.1)) x (Pi.single i 1),
          fderiv ℝ (planeAct (realMat δ.1)) x (Pi.single j 1)]) =
      formPullback (planeAct (realMat δ.1)) (fun y a b => Coef.toPoly (W.comp y a b)) x i j := by
  rw [InvComponents.raw, altCLM_apply, altRaw_apply_of_antisymm _ (W.anti _), toPoly_finsetSum]
  unfold formPullback
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [toPoly_finsetSum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Complex.coe_smul, Coef.toPoly_smul]
  simp

theorem pullForm_form (δ : Γ) :
    ZigZag.pullForm isOpen_Omega (gammaAct Γ) δ 2 W.form =
      ZigZag.twForm (ZigZag.repCLM (gammaRho Γ n) δ) 2 W.form := by
  apply Form.ext
  intro x hx
  have hΦ : planeAct (realMat δ.1) x ∈ Omega := planeAct_mem (det_realMat δ.1) hx
  rw [ZigZag.pullForm_apply isOpen_Omega (gammaAct Γ) δ _ hx, ZigZag.twForm_apply,
    W.form_apply hx]
  apply ext2
  intro i j
  apply Coef.toPoly_injective
  have hL : pullRaw ((gammaAct Γ).act δ) (W.form : RawForm (Fin 5 → ℝ) (Coef n) 2) x
      ![Pi.single i 1, Pi.single j 1] =
      W.raw (planeAct (realMat δ.1) x)
        ![fderiv ℝ (planeAct (realMat δ.1)) x (Pi.single i 1),
          fderiv ℝ (planeAct (realMat δ.1)) x (Pi.single j 1)] := by
    show ((W.form : RawForm (Fin 5 → ℝ) (Coef n) 2) (planeAct (realMat δ.1) x)).compContinuousLinearMap
      (fderiv ℝ (planeAct (realMat δ.1)) x) ![Pi.single i 1, Pi.single j 1] = _
    rw [ContinuousAlternatingMap.compContinuousLinearMap_apply, W.form_apply hΦ]
    congr 1
    funext k; fin_cases k <;> rfl
  rw [hL, W.toPoly_raw_pullback δ x i j, W.equiv δ x hx i j]
  show _ = Coef.toPoly ((ZigZag.repCLM (gammaRho Γ n) δ) (W.raw x ![Pi.single i 1, Pi.single j 1]))
  rw [W.raw_basis]
  exact (toPoly_gammaRho Γ n δ _).symm

/-- **The component family defines an element of `ZigZag.invClosed`**: a closed `Γ`-equivariant
`E_n`-valued two-form on `Ω ≅ 𝒳`. -/
def toInv : ZigZag.invClosed isOpen_Omega (gammaAct Γ) (gammaRho Γ n) :=
  ⟨W.form, W.d_form, W.pullForm_form⟩

theorem toInv_val : (W.toInv : Form (F := Coef n) Omega 2) = W.form := rfl

/-- The coordinates of the chart form `W.toInv` on the coordinate vectors are the components. -/
theorem toInv_basis {y : Fin 5 → ℝ} (hy : y ∈ Omega) (i j : Fin 5) :
    ((W.toInv : Form (F := Coef n) Omega 2) : RawForm (Fin 5 → ℝ) (Coef n) 2) y
      ![Pi.single i 1, Pi.single j 1] = W.comp y i j := by
  rw [toInv_val, W.form_apply hy, W.raw_basis]

/-! ### Restriction to a subgroup -/

variable {H : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ)}

/-- The same components, regarded as a family for a subgroup `H ≤ Γ`. -/
def restrict (hH : H ≤ Γ) : InvComponents H n where
  comp := W.comp
  anti := W.anti
  smooth := W.smooth
  closed := W.closed
  equiv δ x hx i j := W.equiv (Subgroup.inclusion hH δ) x hx i j

end InvComponents

end TernaryPeriodPolynomials.Argument.EisensteinClass
