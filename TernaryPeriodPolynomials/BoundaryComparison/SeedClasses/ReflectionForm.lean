module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.ReflectionSeed

@[expose] public section


/-!
# The finite reflection on the face: `r^* ω_h = (-1)^{n+1} ρ(r) \overline{ω_{h^*}}`

Paper: Lemma C.3 (`ar:lem:seed`),
"the finite reflection projection supplies the corresponding full-level statement".

The reflection `r = diag(-1, 1, 1)` of `GL₃(ℤ)` (determinant `-1`) acts on the face by
`(u₁, u₂, x, y) ↦ (-u₁, u₂, -x, y)` (`reflFCLM`), i.e. `τ ↦ -\bar τ`, and on the coefficients by
`ρ(r) q(X, Y, Z) = -q(-X, Y, Z)` (`reflCoef`, `toPoly_reflCoef`). On the Čech--de Rham forms of the
face (`pullForm`), for `h^*(z) = \overline{h(-\bar z)}` on `ℍ`:

* `pullForm_refl_seed`: `r^* ω_h = (-1)^{n+1} ρ(r) \overline{ω_{h^*}}`;
* `pullForm_refl_conjSeed`: `r^* \overline{ω_{h^*}} = (-1)^{n+1} ρ(r) ω_h`.

Hence on `ω_h + ε (-1)^{n+1} \overline{ω_{h^*}}` the reflection acts by `ε ρ(r)`: this is the
`ε`-isotypic projection of the seed.

Formalized by Claude Sonnet 5.5.
-/

open MvPolynomial GeneralEisenstein ComplexConjugate
open TernaryPoly.SmoothLocalDeRham TernaryPoly.SmoothCoveringDeRham
open scoped ContDiff

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3

theorem realCoefficient_coe (n : ℕ) (g : GL (Fin 3) ℝ) (q : HomogeneousPoly n) :
    ((realCoefficient n g q : HomogeneousPoly n) : MvPolynomial (Fin 3) ℂ) =
      rho (g : Matrix (Fin 3) (Fin 3) ℝ) (q : MvPolynomial (Fin 3) ℂ) := by
  change ((GeneralEisenstein.action (-1)
    (Matrix.GeneralLinearGroup.map (algebraMap ℝ ℂ) g)) (q : MvPolynomial (Fin 3) ℂ)) = _
  rw [GeneralEisenstein.action_apply]
  unfold rho GeneralEisenstein.substitute GeneralEisenstein.linearForm
  simp [GeneralEisenstein.determinantCharacter, Matrix.GeneralLinearGroup.map]
  have hd : ((g : Matrix (Fin 3) (Fin 3) ℝ).map Complex.ofReal).det =
      (((g : Matrix (Fin 3) (Fin 3) ℝ).det : ℝ) : ℂ) := by
    have := RingHom.map_det Complex.ofRealHom (g : Matrix (Fin 3) (Fin 3) ℝ)
    exact this.symm
  rw [hd, smul_eq_C_mul]

/-- The matrix `diag(-1, 1, 1)` of the reflection. -/
def rMat : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal ![-1, 1, 1]

theorem rMat_mul_self : rMat * rMat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem det_rMat : rMat.det = -1 := by
  simp [rMat, Matrix.det_diagonal, Fin.prod_univ_three]

theorem rMat_inv : rMat⁻¹ = rMat := Matrix.inv_eq_right_inv rMat_mul_self

/-- The reflection `diag(-1, 1, 1)` as an element of `GL₃(ℝ)`. -/
def rGL : GL (Fin 3) ℝ := Matrix.GeneralLinearGroup.mkOfDetNeZero rMat (by rw [det_rMat]; norm_num)

/-- `ρ(r)` on `E_n`. -/
def reflCoef (n : ℕ) : Coef n →ₗ[ℂ] Coef n := realCoefficient n rGL

theorem toPoly_reflCoef (n : ℕ) (q : Coef n) :
    Coef.toPoly (reflCoef n q) =
      C (-1 : ℂ) * bind₁ (![-X 0, X 1, X 2] : Fin 3 → MvPolynomial (Fin 3) ℂ) (Coef.toPoly q) := by
  refine (realCoefficient_coe n rGL q).trans ?_
  unfold rho
  have h1 : ((rGL : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) = rMat := rfl
  rw [h1, det_rMat, rMat_inv]
  congr 2
  · simp
  · congr 2
    funext i
    fin_cases i <;> simp [rMat, Fin.sum_univ_three]

/-- `ρ(r)` on `E_n` as a continuous real-linear map. -/
def reflCoefCLM (n : ℕ) : Coef n →L[ℝ] Coef n :=
  LinearMap.toContinuousLinearMap ((reflCoef n).restrictScalars ℝ)

/-- The signs `(-1, 1, -1, 1)` of the reflection of the face. -/
def reflFSign : Fin 4 → ℝ := ![-1, 1, -1, 1]

/-- The reflection `(u₁, u₂, x, y) ↦ (-u₁, u₂, -x, y)` of the face. -/
def reflFCLM : Face →L[ℝ] Face :=
  ContinuousLinearMap.pi fun a => reflFSign a • ContinuousLinearMap.proj a

theorem reflFCLM_apply (x : Face) (a : Fin 4) : reflFCLM x a = reflFSign a * x a := by
  simp [reflFCLM]

theorem reflFSign_eq (i : Fin 4) : reflFSign i = reflSign i.castSucc := by
  fin_cases i <;> simp [reflFSign, reflSign]

theorem reflFCLM_mem {x : Face} (hx : x ∈ faceSet) : reflFCLM x ∈ faceSet := by
  have : 0 < x 3 := hx
  change 0 < reflFCLM x 3
  rw [reflFCLM_apply]
  simpa [reflFSign] using this

theorem ptOf_reflFCLM (x : Face) : Psi.ptOf (reflFCLM x) = reflMap5 (Psi.ptOf x) := by
  funext a
  fin_cases a <;> simp [Psi.ptOf, reflMap5, reflFCLM_apply, reflFSign]

/-- Two continuous alternating 2-forms on the face agree if they agree on pairs of basis vectors. -/
theorem altEq_of_basis {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g : Face [⋀^Fin 2]→L[ℝ] F}
    (h : ∀ i j : Fin 4, f ![Pi.single i 1, Pi.single j 1] = g ![Pi.single i 1, Pi.single j 1]) :
    f = g := by
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  refine Module.Basis.ext_alternating (Pi.basisFun ℝ (Fin 4)) fun v _ => ?_
  have e : (fun k => (Pi.basisFun ℝ (Fin 4)) (v k)) = ![Pi.single (v 0) 1, Pi.single (v 1) 1] := by
    funext k
    fin_cases k <;> simp
  change f (fun k => (Pi.basisFun ℝ (Fin 4)) (v k)) = g (fun k => (Pi.basisFun ℝ (Fin 4)) (v k))
  rw [e]
  exact h _ _

theorem reflFCLM_single (i : Fin 4) :
    reflFCLM (Pi.single i 1) = reflFSign i • Pi.single i 1 := by
  funext a
  rw [reflFCLM_apply]
  by_cases h : a = i
  · subst h; simp
  · simp [h]

/-- **The reflection acts on the seed by the conjugate seed, on the face.** For `r = diag(-1,1,1)`
(acting on the face by `reflFCLM`), `r^*(dη_h) = (-1)^{n+1} ρ(r) \overline{dη_{h^*}}` pointwise on
the face, where `dη_h = ω_h` is the seed and `h^*(z) = \overline{h(-\bar z)}` on `ℍ`. -/
theorem pullRaw_refl_dEta (n : ℕ) (h hs : ℂ → ℂ) (hh : DifferentiableOn ℂ h Psi.upperSet)
    (hhs : DifferentiableOn ℂ hs Psi.upperSet)
    (hrel : ∀ z : ℂ, 0 < z.im → hs z = conj (h (-conj z))) {x : Face} (hx : x ∈ faceSet) :
    pullRaw reflFCLM (d isOpen_faceSet 1 (Psi.etaForm h hh n) : RawForm Face (Coef n) 2) x =
      ((-1 : ℝ) ^ (n + 1)) • coefficientFormMap ((reflCoefCLM n).comp (conjCLM n)) 2
        ((d isOpen_faceSet 1 (Psi.etaForm hs hhs n) : RawForm Face (Coef n) 2) x) := by
  apply altEq_of_basis
  intro i j
  apply Coef.toPoly_injective
  have hrx : reflFCLM x ∈ faceSet := reflFCLM_mem hx
  -- left side
  have hL : Coef.toPoly ((pullRaw reflFCLM
      (d isOpen_faceSet 1 (Psi.etaForm h hh n) : RawForm Face (Coef n) 2) x)
        ![Pi.single i 1, Pi.single j 1]) =
      formPullback reflMap5 (seedForm n h) (Psi.ptOf x) i.castSucc j.castSucc := by
    rw [formPullback_reflMap5]
    have e1 : (fun k : Fin 2 => (fderiv ℝ (⇑reflFCLM) x) (![Pi.single i 1, Pi.single j 1] k)) =
        fun k : Fin 2 => ![reflFSign i, reflFSign j] k • (![Pi.single i 1, Pi.single j 1] k) := by
      funext k
      rw [reflFCLM.fderiv]
      fin_cases k
      · simpa using reflFCLM_single i
      · simpa using reflFCLM_single j
    change Coef.toPoly (((d isOpen_faceSet 1 (Psi.etaForm h hh n) : RawForm Face (Coef n) 2)
      (reflFCLM x)) (fun k : Fin 2 => (fderiv ℝ (⇑reflFCLM) x) (![Pi.single i 1, Pi.single j 1] k)))
      = _
    rw [e1, ContinuousAlternatingMap.map_smul_univ]
    have e2 : ∀ (c : ℝ) (y : Coef n), Coef.toPoly (c • y) = C (c : ℂ) * Coef.toPoly y := by
      intro c y
      have : c • y = ((c : ℂ) • y : Coef n) := (Complex.coe_smul c y).symm
      rw [this, Coef.toPoly_smul]
    rw [e2, Fin.prod_univ_two, PlaneData.toPoly_d_etaForm h n hh hrx i j, ptOf_reflFCLM,
      reflFSign_eq,
      reflFSign_eq]
    simp
  -- right side
  have hR : Coef.toPoly ((((-1 : ℝ) ^ (n + 1)) • coefficientFormMap
      ((reflCoefCLM n).comp (conjCLM n)) 2
        ((d isOpen_faceSet 1 (Psi.etaForm hs hhs n) : RawForm Face (Coef n) 2) x))
          ![Pi.single i 1, Pi.single j 1]) =
      C ((-1 : ℂ) ^ (n + 1)) * (C (-1 : ℂ) * bind₁
        (![-X 0, X 1, X 2] : Fin 3 → MvPolynomial (Fin 3) ℂ)
          (MvPolynomial.map (starRingEnd ℂ)
            (seedForm n hs (Psi.ptOf x) i.castSucc j.castSucc))) := by
    have e2 : ∀ (c : ℝ) (y : Coef n), Coef.toPoly (c • y) = C (c : ℂ) * Coef.toPoly y := by
      intro c y
      have : c • y = ((c : ℂ) • y : Coef n) := (Complex.coe_smul c y).symm
      rw [this, Coef.toPoly_smul]
    have hv := PlaneData.toPoly_d_etaForm hs n hhs hx i j
    have e3 : (((-1 : ℝ) ^ (n + 1)) • coefficientFormMap ((reflCoefCLM n).comp (conjCLM n)) 2
        ((d isOpen_faceSet 1 (Psi.etaForm hs hhs n) : RawForm Face (Coef n) 2) x))
          ![Pi.single i 1, Pi.single j 1] =
        ((-1 : ℝ) ^ (n + 1)) • reflCoef n (Coef.conjCoef
          (((d isOpen_faceSet 1 (Psi.etaForm hs hhs n) : RawForm Face (Coef n) 2) x)
            ![Pi.single i 1, Pi.single j 1])) := rfl
    rw [e3, e2, toPoly_reflCoef, Coef.toPoly_conjCoef, hv]
    push_cast
    rfl
  rw [hL, hR]
  have hp := refl_pullback n h hs (Psi.ptOf x)
    (by rw [Psi.seedTau_ptOf]; exact hrel _ (faceTau_im hx)) i.castSucc j.castSucc
  rw [hp, ← mul_assoc, ← map_mul]
  congr 2
  rw [pow_succ]
  simp

/-- The group `ℤ/2` acting on the face by the reflection. -/
def reflAct (g : Multiplicative (ZMod 2)) (x : Face) : Face := if g = 1 then x else reflFCLM x

theorem reflFCLM_involutive (x : Face) : reflFCLM (reflFCLM x) = x := by
  funext a
  rw [reflFCLM_apply, reflFCLM_apply]
  fin_cases a <;> simp [reflFSign]

theorem mul_self_of_ne_one {g : Multiplicative (ZMod 2)} (hg : g ≠ 1) : g * g = 1 := by
  revert g; decide

theorem mul_eq_one_iff_of_ne_one {g h : Multiplicative (ZMod 2)} (hg : g ≠ 1) (hh : h ≠ 1) :
    g * h = 1 := by
  revert g h; decide

theorem mul_ne_one_of {g h : Multiplicative (ZMod 2)} (hg : g = 1) (hh : h ≠ 1) : g * h ≠ 1 := by
  subst hg; simpa using hh

/-- The reflection action of `ℤ/2` on the face, as a `ZigZag.Action`. -/
def reflAction : ZigZag.Action (Multiplicative (ZMod 2)) faceSet where
  act := reflAct
  smooth g := by
    unfold reflAct
    by_cases hg : g = 1
    · simp only [hg, ite_true]; exact contDiffOn_id
    · simp only [hg, ite_false]; exact reflFCLM.contDiff.contDiffOn
  mapsTo g x hx := by
    unfold reflAct
    by_cases hg : g = 1
    · simpa [hg] using hx
    · simpa [hg] using reflFCLM_mem hx
  mul g h x _ := by
    unfold reflAct
    by_cases hg : g = 1
    · simp [hg]
    · by_cases hh : h = 1
      · simp [hh]
      · have : g * h = 1 := mul_eq_one_iff_of_ne_one hg hh
        simp [this, hg, hh, reflFCLM_involutive]

/-- The generator of `ℤ/2`. -/
def reflGen : Multiplicative (ZMod 2) := Multiplicative.ofAdd 1

theorem reflGen_ne_one : reflGen ≠ 1 := by decide

theorem reflAction_act_gen (x : Face) : reflAction.act reflGen x = reflFCLM x := by
  change reflAct reflGen x = _
  simp [reflAct, reflGen_ne_one]

/-- **Lemma C.3, the finite reflection, as an identity of closed forms on the face.**
For `h, h^*` holomorphic on `ℍ` with `h^*(z) = \overline{h(-\bar z)}`:
`r^* ω_h = (-1)^{n+1} ρ(r) \overline{ω_{h^*}}`. -/
theorem pullForm_refl_seed (n : ℕ) (h hs : ℂ → ℂ) (hh : DifferentiableOn ℂ h Psi.upperSet)
    (hhs : DifferentiableOn ℂ hs Psi.upperSet)
    (hrel : ∀ z : ℂ, 0 < z.im → hs z = conj (h (-conj z))) :
    ZigZag.pullForm isOpen_faceSet reflAction reflGen 2
        (d isOpen_faceSet 1 (Psi.etaForm h hh n)) =
      ((-1 : ℝ) ^ (n + 1)) • ZigZag.twForm ((reflCoefCLM n).comp (conjCLM n)) 2
        (d isOpen_faceSet 1 (Psi.etaForm hs hhs n)) := by
  apply Form.ext
  intro x hx
  rw [ZigZag.pullForm_apply isOpen_faceSet reflAction reflGen _ hx]
  have h1 : reflAction.act reflGen = ⇑reflFCLM := funext reflAction_act_gen
  rw [h1]
  change _ = ((-1 : ℝ) ^ (n + 1)) • (ZigZag.twForm ((reflCoefCLM n).comp (conjCLM n)) 2
        (d isOpen_faceSet 1 (Psi.etaForm hs hhs n)) : RawForm Face (Coef n) 2) x
  rw [ZigZag.twForm_apply]
  exact pullRaw_refl_dEta n h hs hh hhs hrel hx

theorem conjCoef_conjCoef {n : ℕ} (q : Coef n) : Coef.conjCoef (Coef.conjCoef q) = q := by
  apply Coef.toPoly_injective
  simp only [Coef.toPoly_conjCoef]
  rw [MvPolynomial.map_map]
  have : (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ := by
    ext z; simp
  rw [this, MvPolynomial.map_id]

theorem conjCLM_comp_conjCLM (n : ℕ) :
    (conjCLM n).comp (conjCLM n) = ContinuousLinearMap.id ℝ _ := by
  ext q
  exact conjCoef_conjCoef q

theorem conjCLM_comp_reflCoefCLM (n : ℕ) :
    (conjCLM n).comp (reflCoefCLM n) = (reflCoefCLM n).comp (conjCLM n) := by
  ext q
  apply Coef.toPoly_injective
  change Coef.toPoly (Coef.conjCoef (reflCoef n q)) = Coef.toPoly (reflCoef n (Coef.conjCoef q))
  rw [Coef.toPoly_conjCoef, toPoly_reflCoef, toPoly_reflCoef, Coef.toPoly_conjCoef, map_mul,
    MvPolynomial.map_C, MvPolynomial.map_bind₁]
  have e : (fun i => MvPolynomial.map (starRingEnd ℂ)
      ((![-X 0, X 1, X 2] : Fin 3 → MvPolynomial (Fin 3) ℂ) i)) =
      (![-X 0, X 1, X 2] : Fin 3 → MvPolynomial (Fin 3) ℂ) := by
    funext i
    fin_cases i <;> simp
  rw [e]
  simp

/-- The same, for the conjugate seed: `r^* \overline{ω_{h^*}} = (-1)^{n+1} ρ(r) ω_h`. -/
theorem pullForm_refl_conjSeed (n : ℕ) (h hs : ℂ → ℂ) (hh : DifferentiableOn ℂ h Psi.upperSet)
    (hhs : DifferentiableOn ℂ hs Psi.upperSet)
    (hrel : ∀ z : ℂ, 0 < z.im → hs z = conj (h (-conj z))) :
    ZigZag.pullForm isOpen_faceSet reflAction reflGen 2
        (ZigZag.twForm (conjCLM n) 2 (d isOpen_faceSet 1 (Psi.etaForm hs hhs n))) =
      ((-1 : ℝ) ^ (n + 1)) • ZigZag.twForm (reflCoefCLM n) 2
        (d isOpen_faceSet 1 (Psi.etaForm h hh n)) := by
  have hrel' : ∀ z : ℂ, 0 < z.im → h z = conj (hs (-conj z)) := by
    intro z hz
    have hz' : 0 < (-conj z).im := by simpa using hz
    rw [hrel _ hz']
    simp
  rw [ZigZag.pullForm_twForm, pullForm_refl_seed n hs h hhs hh hrel', map_smul, ← ZigZag.twForm_mul,
    ← ContinuousLinearMap.comp_assoc, conjCLM_comp_reflCoefCLM, ContinuousLinearMap.comp_assoc,
    conjCLM_comp_conjCLM, ContinuousLinearMap.comp_id]

end TernaryPeriodPolynomials.Argument.SeedC3
