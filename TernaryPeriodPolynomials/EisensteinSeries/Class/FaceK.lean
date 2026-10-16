module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Unfold.K
public import TernaryPeriodPolynomials.EisensteinSeries.Class.ConstantTerm
public import TernaryPeriodPolynomials.EisensteinSeries.Class.AveragePreserves

@[expose] public section


/-!
# The class of the face form of the series at the cusp `k⁻¹ P k`, up to the cell

`faceSeriesK` is the pullback `ι^* E_{k⁻¹Pk}` to the boundary model `e(P)` of the series at the cusp
`CuspData.ofSL k`, a closed form invariant under `Γ_P`. Its coordinates are the sums of the
coefficients over the cosets `Γ_{k⁻¹Pk}\Γ(N)`; the **cell** is the set of cosets whose bottom row
`r_k γ` has vanishing first two entries (at most one coset for `N ≥ 3`: `k γ ∈ P(ℤ)`).
`classK_eq`: if `C` is any `Γ_P`-invariant closed form whose coordinates are the cell sum, then
`ι^*E` and `C` have the same de Rham class (the torus average of `ι^*E − C` vanishes
(`totalK_zero`), and averaging does not change the class (`deRhamClass_avInv`)).

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups ContDiff
open MeasureTheory Set MvPolynomial
noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPoly.SmoothLocalDeRham TernaryPoly.SmoothCoveringDeRham
open TernaryPeriodPolynomials.Argument.SeedC3.Psi TernaryPeriodPolynomials.Argument.Statements.EisensteinClass
open TernaryPeriodPolynomials.Argument.Statements.ConvergenceC4

section FaceK

variable (N : ℕ) [NeZero N] (k : SL(3, ℤ)) (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))
  (hn : 4 ≤ n)

/-- **The face form of the series at the cusp `k⁻¹ P k`**: the pullback `ι^* E` of the holomorphic
series at `CuspData.ofSL k` to the plane boundary model `e(P)`. -/
def faceSeriesK : ZigZag.invClosed isOpen_faceSet (gammaNPlaneData N).action
    ((gammaNPlaneData N).rhoR n) :=
  faceForm (gammaNPlaneData N) (inclP N) (fun g => gammaNPlaneData_plm N g)
    (planeEisensteinAtComponents false (CuspData.ofSL k) (gammaN N) (leviGroup N) n f hn
      (leviInCusp_gammaN N k))

/-- The cell: the cosets whose bottom row has vanishing first two entries. -/
def IsCellK (c : Ck N k) : Prop :=
  cuspRow (gammaN N) (CuspData.ofSL k).r c 0 = 0 ∧ cuspRow (gammaN N) (CuspData.ofSL k).r c 1 = 0

open Classical in
/-- The sum of the coefficients over the cell. -/
def cellCoeffK (y : Fin 5 → ℝ) (i j : Fin 5) (m : Fin 3 →₀ ℕ) : ℂ :=
  ∑' c : Ck N k, if IsCellK N k c then
    termFunK false (CuspData.ofSL k) (gammaN N) n f c i j m y else 0

open Classical in
/-- The sum of the coefficients over the non-cell cosets. -/
def restCoeffK (y : Fin 5 → ℝ) (i j : Fin 5) (m : Fin 3 →₀ ℕ) : ℂ :=
  ∑' c : Ck N k, if IsCellK N k c then 0 else
    termFunK false (CuspData.ofSL k) (gammaN N) n f c i j m y

theorem faceSeriesK_basis {x : Face} (hx : x ∈ faceSet) (i j : Fin 4) (m : Fin 3 →₀ ℕ) :
    (Coef.toPoly (((faceSeriesK N k n f hn : Form (F := Coef n) faceSet 2) :
        RawForm Face (Coef n) 2) x ![Pi.single i 1, Pi.single j 1])).coeff m =
      seriesCoeffK false (CuspData.ofSL k) (gammaN N) n f i.castSucc j.castSucc m (ptOf x) := by
  have h1 := faceForm_basis (gammaNPlaneData N) (inclP N) (fun g => gammaNPlaneData_plm N g)
    (planeEisensteinAtComponents false (CuspData.ofSL k) (gammaN N) (leviGroup N) n f hn
      (leviInCusp_gammaN N k)) hx i j
  rw [show (((faceSeriesK N k n f hn : Form (F := Coef n) faceSet 2) :
      RawForm Face (Coef n) 2) x ![Pi.single i 1, Pi.single j 1]) =
        Coef.mk (planeEisensteinAt false (CuspData.ofSL k) (gammaN N) n f (ptOf x) i.castSucc
          j.castSucc) from h1]
  exact coeff_planeEisensteinAt false (CuspData.ofSL k) (gammaN N) n f (ptOf x) i.castSucc
    j.castSucc m

theorem seriesCoeffK_split (hn : 4 ≤ n) {y : Fin 5 → ℝ} (hy : y ∈ Omega) (i j : Fin 5)
    (m : Fin 3 →₀ ℕ) :
    seriesCoeffK false (CuspData.ofSL k) (gammaN N) n f i j m y =
      cellCoeffK N k n f y i j m + restCoeffK N k n f y i j m := by
  classical
  have hs := summable_termFunK_val false (CuspData.ofSL k) (gammaN N)
    (leviGroup N) n f hn hy i j m
  have hs1 : Summable fun c : Ck N k => if IsCellK N k c then
      termFunK false (CuspData.ofSL k) (gammaN N) n f c i j m y else 0 := by
    exact (hs.indicator {c : Ck N k | IsCellK N k c}).congr (fun c => by
      by_cases hc : IsCellK N k c <;> simp [hc])
  have hs2 : Summable fun c : Ck N k => if IsCellK N k c then 0 else
      termFunK false (CuspData.ofSL k) (gammaN N) n f c i j m y := by
    exact (hs.indicator {c : Ck N k | ¬ IsCellK N k c}).congr (fun c => by
      by_cases hc : IsCellK N k c <;> simp [hc])
  unfold seriesCoeffK cellCoeffK restCoeffK
  rw [← Summable.tsum_add hs1 hs2]
  refine tsum_congr fun c => ?_
  by_cases hc : IsCellK N k c <;> simp [hc]

/-- **The averaged integrand is the sum over the non-cell cosets**: if `R` is a form whose
coordinates are the non-cell sums, the `m`-th coefficient of `ρ(t_{-v}) R(x + v)(e_p, e_q)` is
`Σ'_{c ∉ cell} S(k γ_c n(v))`. -/
theorem coeff_trL_restK (hn : 4 ≤ n)
    (R : ZigZag.invClosed isOpen_faceSet (gammaNPlaneData N).action ((gammaNPlaneData N).rhoR n))
    (hR : ∀ y ∈ faceSet, ∀ (i j : Fin 4) (m : Fin 3 →₀ ℕ),
      (Coef.toPoly (((R : Form (F := Coef n) faceSet 2) : RawForm Face (Coef n) 2) y
        ![Pi.single i 1, Pi.single j 1])).coeff m =
        restCoeffK N k n f (ptOf y) i.castSucc j.castSucc m)
    {x : Face} (hx : x ∈ faceSet) (v : Fin 2 → ℝ) (p q : Fin 4) (m : Fin 3 →₀ ℕ) :
    polyCoefCLM n m (trL n (-v)
      (((R : Form (F := Coef n) faceSet 2) : RawForm Face (Coef n) 2)
        (x + shVec v) ![Pi.single p 1, Pi.single q 1])) =
      ∑' c : Ck N k, FcK N k n f (ptOf x) p.castSucc q.castSucc m c v := by
  classical
  have hy : x + shVec v ∈ faceSet := shVec_mem hx v
  have hΩ := ptOf_mem hx
  set w := (((R : Form (F := Coef n) faceSet 2) : RawForm Face (Coef n) 2)
        (x + shVec v) ![Pi.single p 1, Pi.single q 1]) with hw
  have hcoef : ∀ m', (Coef.toPoly w).coeff m' =
      restCoeffK N k n f (ptOf (x + shVec v)) p.castSucc q.castSucc m' :=
    fun m' => hR _ hy p q m'
  rw [polyCoefCLM_apply, toPoly_trL]
  have hneg : transMat ((-v) 0) ((-v) 1) = nmat (-v) := rfl
  rw [hneg, coeff_rho_expansion (Coef.toPoly_isHomogeneous w) _ m]
  simp only [hcoef, ptOf_shVec]
  have hRHS : ∀ c : Ck N k,
      FcK N k n f (ptOf x) p.castSucc q.castSucc m c v = ∑ m' ∈ monSet n,
        (if IsCellK N k c then 0 else
          termFunK false (CuspData.ofSL k) (gammaN N) n f c p.castSucc q.castSucc m'
            (ptOf x + ![v 0, v 1, 0, 0, 0])) *
          (rho (nmat (-v)) (monomial m' 1)).coeff m := by
    intro c
    unfold FcK
    by_cases hc : IsCellK N k c
    · have hc' : cuspRow (gammaN N) (CuspData.ofSL k).r c 0 = 0 ∧
          cuspRow (gammaN N) (CuspData.ofSL k).r c 1 = 0 := hc
      simp [hc, hc']
    · have hc' : ¬ (cuspRow (gammaN N) (CuspData.ofSL k).r c 0 = 0 ∧
          cuspRow (gammaN N) (CuspData.ofSL k).r c 1 = 0) := hc
      simp only [ite_eq_right hc, ite_eq_right hc']
      exact PhiK_expansion N k n f hΩ _ _ m c v
  simp_rw [hRHS]
  have hΩ' : ptOf x + ![v 0, v 1, 0, 0, 0] ∈ Omega := shift_mem_Omega hΩ v
  have hsum : ∀ m' : Fin 3 →₀ ℕ, Summable fun c : Ck N k =>
      (if IsCellK N k c then 0 else
        termFunK false (CuspData.ofSL k) (gammaN N) n f c p.castSucc q.castSucc m'
          (ptOf x + ![v 0, v 1, 0, 0, 0])) * (rho (nmat (-v)) (monomial m' 1)).coeff m := by
    intro m'
    have h0 := summable_termFunK_val false (CuspData.ofSL k) (gammaN N) (leviGroup N) n f hn hΩ'
      p.castSucc q.castSucc m'
    have h1 : Summable fun c : Ck N k => if IsCellK N k c then 0 else
        termFunK false (CuspData.ofSL k) (gammaN N) n f c p.castSucc q.castSucc m'
          (ptOf x + ![v 0, v 1, 0, 0, 0]) :=
      (h0.indicator {c : Ck N k | ¬ IsCellK N k c}).congr (fun c => by
        by_cases hc : IsCellK N k c <;> simp [hc])
    exact h1.mul_right _
  rw [Summable.tsum_finsetSum (fun m' _ => hsum m')]
  refine Finset.sum_congr rfl fun m' _ => ?_
  unfold restCoeffK
  rw [tsum_mul_right]

/-- **The torus average of a form with non-cell coordinates vanishes.** -/
theorem avInv_zero_of_restK (hn : 4 ≤ n)
    (R : ZigZag.invClosed isOpen_faceSet (gammaNPlaneData N).action ((gammaNPlaneData N).rhoR n))
    (hR : ∀ y ∈ faceSet, ∀ (i j : Fin 4) (m : Fin 3 →₀ ℕ),
      (Coef.toPoly (((R : Form (F := Coef n) faceSet 2) : RawForm Face (Coef n) 2) y
        ![Pi.single i 1, Pi.single j 1])).coeff m =
        restCoeffK N k n f (ptOf y) i.castSucc j.castSucc m) :
    avInv n (latticeData_gammaN N) R = 0 := by
  apply Subtype.ext
  rw [avInv_val]
  show avForm n (N : ℝ) R.1 = 0
  apply Form.ext
  intro x hx
  rw [avForm_apply n _ _ hx]
  show avRaw n (N : ℝ) R.1 x = 0
  unfold avRaw
  have hcont := continuous_avIntegrand_uncurry n (N : ℝ) R.1 hx
  apply ext2Face
  intro p q
  apply Coef.toPoly_injective
  apply MvPolynomial.ext
  intro m
  let Λ : (Face [⋀^Fin 2]→L[ℝ] Coef n) →L[ℝ] ℂ :=
    (polyCoefCLM n m).comp (evalPairCLM n (Pi.single p 1) (Pi.single q 1))
  have h1 := iterIntegral_clm_comm Λ (fun a b => avIntegrand n (N : ℝ) R.1 ((x, a), b)) hcont
  have h2 : Λ (∫ a in (0 : ℝ)..1, ∫ b in (0 : ℝ)..1, avIntegrand n (N : ℝ) R.1 ((x, a), b)) =
      (Coef.toPoly ((∫ a in (0 : ℝ)..1, ∫ b in (0 : ℝ)..1,
        avIntegrand n (N : ℝ) R.1 ((x, a), b)) ![Pi.single p 1, Pi.single q 1])).coeff m := rfl
  have h3 : ∀ a b : ℝ, Λ (avIntegrand n (N : ℝ) R.1 ((x, a), b)) =
      ∑' c : Ck N k, FcK N k n f (ptOf x) p.castSucc q.castSucc m c ((N : ℝ) • ![a, b]) := by
    intro a b
    rw [← coeff_trL_restK N k n f hn R hR hx ((N : ℝ) • ![a, b]) p q m]
    show polyCoefCLM n m
      (evalPairCLM n (Pi.single p 1) (Pi.single q 1) (((shiftForm n ((N : ℝ) • ![a, b])
        R.1 : Form (F := Coef n) faceSet 2) : RawForm Face (Coef n) 2) x)) = _
    rw [shiftForm_apply n _ _ hx]
    rfl
  have h4 : (Coef.toPoly ((∫ a in (0 : ℝ)..1, ∫ b in (0 : ℝ)..1,
        avIntegrand n (N : ℝ) R.1 ((x, a), b)) ![Pi.single p 1, Pi.single q 1])).coeff m = 0 := by
    rw [← h2, h1]
    simp only [h3]
    exact totalK_zero N k n f hn (ptOf_mem hx) _ _ m
  simpa using h4

/-- **The torus average of `ι^*E − C` vanishes** for any invariant closed form `C` whose
coordinates are the cell sum. -/
theorem avInv_sub_zero_of_cell (hn : 4 ≤ n)
    (C : ZigZag.invClosed isOpen_faceSet (gammaNPlaneData N).action ((gammaNPlaneData N).rhoR n))
    (hC : ∀ y ∈ faceSet, ∀ (i j : Fin 4) (m : Fin 3 →₀ ℕ),
      (Coef.toPoly (((C : Form (F := Coef n) faceSet 2) : RawForm Face (Coef n) 2) y
        ![Pi.single i 1, Pi.single j 1])).coeff m =
        cellCoeffK N k n f (ptOf y) i.castSucc j.castSucc m) :
    avInv n (latticeData_gammaN N) (faceSeriesK N k n f hn - C) = 0 := by
  have hR : ∀ y ∈ faceSet, ∀ (i j : Fin 4) (m : Fin 3 →₀ ℕ),
      (Coef.toPoly ((((faceSeriesK N k n f hn - C : ZigZag.invClosed isOpen_faceSet
        (gammaNPlaneData N).action ((gammaNPlaneData N).rhoR n)) :
          Form (F := Coef n) faceSet 2) : RawForm Face (Coef n) 2) y
            ![Pi.single i 1, Pi.single j 1])).coeff m =
        restCoeffK N k n f (ptOf y) i.castSucc j.castSucc m := by
    intro y hy i j m
    have e : ((((faceSeriesK N k n f hn - C : ZigZag.invClosed isOpen_faceSet
        (gammaNPlaneData N).action ((gammaNPlaneData N).rhoR n)) :
          Form (F := Coef n) faceSet 2) : RawForm Face (Coef n) 2) y
            ![Pi.single i 1, Pi.single j 1]) =
        (((faceSeriesK N k n f hn : Form (F := Coef n) faceSet 2) : RawForm Face (Coef n) 2) y
          ![Pi.single i 1, Pi.single j 1]) -
        (((C : Form (F := Coef n) faceSet 2) : RawForm Face (Coef n) 2) y
          ![Pi.single i 1, Pi.single j 1]) := rfl
    rw [e, Coef.toPoly_sub, coeff_sub, faceSeriesK_basis N k n f hn hy, hC y hy,
      seriesCoeffK_split N k n f hn (ptOf_mem hy), add_sub_cancel_left]
  exact avInv_zero_of_restK N k n f hn _ hR

/-- **The class of the face form of the series at the cusp `k⁻¹Pk` is the class of any invariant
closed form whose coordinates are the cell sum.** -/
theorem classK_eq (hn : 4 ≤ n)
    (C : ZigZag.invClosed isOpen_faceSet (gammaNPlaneData N).action ((gammaNPlaneData N).rhoR n))
    (hC : ∀ y ∈ faceSet, ∀ (i j : Fin 4) (m : Fin 3 →₀ ℕ),
      (Coef.toPoly (((C : Form (F := Coef n) faceSet 2) : RawForm Face (Coef n) 2) y
        ![Pi.single i 1, Pi.single j 1])).coeff m =
        cellCoeffK N k n f (ptOf y) i.castSucc j.castSucc m) :
    ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty (gammaNPlaneData N).action
        ((gammaNPlaneData N).rhoR n) (faceSeriesK N k n f hn) =
      ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty (gammaNPlaneData N).action
        ((gammaNPlaneData N).rhoR n) C := by
  have h0 := avInv_sub_zero_of_cell N k n f hn C hC
  have h1 := deRhamClass_avInv (latticeData_gammaN N)
    (Nat.cast_ne_zero.mpr (NeZero.ne N)) (faceSeriesK N k n f hn - C)
  rw [h0, map_zero] at h1
  have h3 := (ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty
    (gammaNPlaneData N).action ((gammaNPlaneData N).rhoR n)).map_sub (faceSeriesK N k n f hn) C
  exact sub_eq_zero.1 (h3.symm.trans h1.symm)

end FaceK

end TernaryPeriodPolynomials.Argument.EisensteinClass
