module

public import TernaryPeriodPolynomials.EisensteinSeries.EisensteinClass
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.SeedCusp
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.GammaNSeed

@[expose] public section


/-!
# Constant term of the Eisenstein class at the plane face: the reduction (Appendix C.4)

Paper: "the identity
constant term represents exactly `ξ`"
(`r_P 𝓔_P(ξ) = ξ`).

The restriction to the plane stabilizer `Γ_P = Γ(N) ∩ P(ℤ)` of the class of the series
`𝓔_P(ω_h) = ∑_{Γ_P\Γ} ρ(γ)⁻¹ γ^* ω_h` is the de Rham class of its pullback to the boundary model
`e(P)` (`Statements.EisensteinClass.eisensteinClass_gammaN_face`). Unfolding over `Γ_P \ Γ`, the identity
coset contributes exactly the seed `ω_h` (`termFun_idCoset`, `seriesCoeff_eq_seed_add_rest`), so

  `r_P [𝓔_P(ω_h)] = [seed of f] + [restFaceForm]`   (`resP_eisensteinClass_eq`),

where `restFaceForm` is the invariant closed form on `e(P)` whose coordinates are the sums over the
non-identity cosets (`restFaceForm_basis`). The scalar of the identity term is `1`.
`resP_eisensteinClass_iff` shows that the constant-term identity `r_P [𝓔_P] = [seed]` holds exactly
when `ConstantTermVanishing` does, the statement that the non-identity part has zero class (the
vanishing of the zero modes of the `s₂₃` coset terms by cuspidality). That statement is
the analytic core and is recorded as a definition `ConstantTermVanishing : Prop`, not proved.

Formalized by Claude Sonnet 5.5.
-/

open MvPolynomial UpperHalfPlane ModularForm
open scoped UpperHalfPlane MatrixGroups ContDiff

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3

theorem summandPoly_one (n : ℕ) (h : ℂ → ℂ) {q : Fin 5 → ℝ} (hq : q ∈ Omega) (i j : Fin 5) :
    summandPoly n h (realMat 1) q i j = seedForm n h q i j := by
  have hev : planeAct (1 : Matrix (Fin 3) (Fin 3) ℝ) =ᶠ[nhds q] id :=
    Filter.eventuallyEq_of_mem (isOpen_Omega.mem_nhds hq) fun y hy => planeAct_one hy
  unfold summandPoly
  rw [realMat_one, inv_one, rho_one, formPullback_congr _ hev]
  unfold formPullback
  simp [Pi.single_apply, apply_ite (fun r : ℝ => (C (r : ℂ) : MvPolynomial (Fin 3) ℂ)), ite_mul]

/-- The identity coset `Γ_P · 1`. -/
def idCoset (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ)) : PlaneCoset Γ :=
  Quotient.mk _ (1 : Γ)

section Identity

variable (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ))
  {F : Type*} [FunLike F ℍ ℂ] (Λ : Subgroup (GL (Fin 2) ℝ)) [Λ.HasDetOne] [Λ.IsArithmetic]
  (n : ℕ) [CuspFormClass F Λ ((n + 3 : ℕ) : ℤ)] (f : F)

omit [Λ.IsArithmetic] in
/-- **The identity coset contributes the seed**: `ρ(1)⁻¹ 1^* ω_h = ω_h`. -/
theorem termFun_idCoset (hLevi : LeviIn Γ Λ) {y : Fin 5 → ℝ} (hy : y ∈ Omega) (i j : Fin 5)
    (m : Fin 3 →₀ ℕ) :
    termFun Γ n f (idCoset Γ) i j m y = (seedForm n (hfun f) y i j).coeff m := by
  rw [termFun_eq_cosetTerm Γ Λ n f hLevi hy i j m]
  change (summandPoly n (fun z => f (ofComplex z)) (realMat (1 : Γ).1) y i j).coeff m = _
  rw [show (1 : Γ).1 = 1 from rfl, summandPoly_one n _ hy]
  rfl

open Classical in
/-- The part of the series over the non-identity cosets. -/
def restCoeff (i j : Fin 5) (m : Fin 3 →₀ ℕ) (y : Fin 5 → ℝ) : ℂ :=
  ∑' c : PlaneCoset Γ, if c = idCoset Γ then 0 else termFun Γ n f c i j m y

/-- **Unfolding over `Γ_P \ Γ`, first step**: the series is the seed (identity coset) plus the sum
over the non-identity cosets. -/
theorem seriesCoeff_eq_seed_add_rest (hn : 4 ≤ n) (hLevi : LeviIn Γ Λ) {y : Fin 5 → ℝ}
    (hy : y ∈ Omega) (i j : Fin 5) (m : Fin 3 →₀ ℕ) :
    seriesCoeff Γ n f i j m y = (seedForm n (hfun f) y i j).coeff m + restCoeff Γ n f i j m y := by
  unfold seriesCoeff restCoeff
  classical
  rw [(summable_termFun_val Γ Λ n f hn hy i j m).tsum_eq_add_tsum_ite (idCoset Γ),
    termFun_idCoset Γ Λ n f hLevi hy]

end Identity

/-- **The non-identity cosets are exactly the cosets whose bottom row has a nonzero entry among the
first two** (for `N ≥ 3`): a coset of `Γ(N)` with bottom row `(0, 0, c)` is the identity coset. -/
theorem eq_idCoset_iff {N : ℕ} (hN : 3 ≤ N) (c : PlaneCoset (gammaN N)) :
    c = idCoset (gammaN N) ↔ cosetRow (gammaN N) c 0 = 0 ∧ cosetRow (gammaN N) c 1 = 0 := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · intro h
    induction c using Quotient.inductionOn with
    | _ a =>
      obtain ⟨h0, h1⟩ := h
      have hs : a.1 ∈ planeStab := mem_planeStab_of_gammaN hN a.2 h0 h1
      apply Quotient.sound
      refine QuotientGroup.rightRel_apply.2 (Subgroup.mem_subgroupOf.2 ?_)
      simpa using planeStab.inv_mem hs

section GammaN

open TernaryPoly.SmoothLocalDeRham TernaryPeriodPolynomials.Argument.Statements.ConvergenceC4
open TernaryPeriodPolynomials.Argument.Statements.EisensteinClass TernaryPeriodPolynomials.Argument.SeedC3.Psi

variable (N : ℕ) [NeZero N] (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (hn : 4 ≤ n)

/-- The inclusion `Γ_P = Γ(N) ∩ P(ℤ) ↪ Γ(N)`. -/
abbrev inclP : gammaNP N →* gammaN N := Subgroup.inclusion (inf_le_left : gammaNP N ≤ gammaN N)

/-- **The face form of the series**: the pullback `i^*𝓔_P(ω_h)` of the Eisenstein form to the plane
boundary model `e(P)`. -/
def eisensteinFace : ZigZag.invClosed isOpen_faceSet (gammaNPlaneData N).action
    ((gammaNPlaneData N).rhoR n) :=
  faceForm (gammaNPlaneData N) (inclP N) (fun g => gammaNPlaneData_plm N g)
    (planeEisensteinComponents (gammaN N) (leviGroup N) n f hn (leviIn_gammaN N))

/-- **The non-identity part of the face form**: `i^*𝓔_P(ω_h) - ω_h`, an invariant closed form on
`e(P)` whose coordinates are the sums over the non-identity cosets of `Γ_P \ Γ`
(`restFaceForm_basis`). -/
def restFaceForm : ZigZag.invClosed isOpen_faceSet (gammaNPlaneData N).action
    ((gammaNPlaneData N).rhoR n) :=
  eisensteinFace N n f hn - cuspSeedInv (gammaNPlaneData N) (gammaNPlaneData_lam_mem N) (f := f)

/-- The coordinates of the non-identity part: the sum over the cosets `Γ_P γ ≠ Γ_P` of the
coefficients of `ρ(γ)⁻¹ γ^* ω_h` at the point `(u, τ, 1)`. -/
theorem restFaceForm_basis {x : Face} (hx : x ∈ faceSet) (i j : Fin 4) (m : Fin 3 →₀ ℕ) :
    (Coef.toPoly (((restFaceForm N n f hn : Form (F := Coef n) faceSet 2) :
        RawForm Face (Coef n) 2) x ![Pi.single i 1, Pi.single j 1])).coeff m =
      restCoeff (gammaN N) n f i.castSucc j.castSucc m (ptOf x) := by
  have hΩ := ptOf_mem hx
  have h1 := eisensteinFaceForm_gammaN_basis N n f hn hx i j
  have h2 := PlaneData.toPoly_d_etaForm (cuspH (leviGroup N) n f) n (cuspH_holo (leviGroup N) n f) hx i j
  have h3 := seriesCoeff_eq_seed_add_rest (gammaN N) (leviGroup N) n f hn (leviIn_gammaN N) hΩ
    i.castSucc j.castSucc m
  change (Coef.toPoly (((eisensteinFace N n f hn : Form (F := Coef n) faceSet 2) :
      RawForm Face (Coef n) 2) x ![Pi.single i 1, Pi.single j 1] -
    ((cuspSeedInv (gammaNPlaneData N) (gammaNPlaneData_lam_mem N) (f := f) :
      Form (F := Coef n) faceSet 2) : RawForm Face (Coef n) 2) x
        ![Pi.single i 1, Pi.single j 1])).coeff m = _
  rw [Coef.toPoly_sub, coeff_sub]
  have e1 : ((((eisensteinFace N n f hn : Form (F := Coef n) faceSet 2) :
      RawForm Face (Coef n) 2) x ![Pi.single i 1, Pi.single j 1]).toPoly).coeff m =
      seriesCoeff (gammaN N) n f i.castSucc j.castSucc m (ptOf x) := by
    rw [show (((eisensteinFace N n f hn : Form (F := Coef n) faceSet 2) :
      RawForm Face (Coef n) 2) x ![Pi.single i 1, Pi.single j 1]) =
        Coef.mk (planeEisenstein (gammaN N) n f (ptOf x) i.castSucc j.castSucc) from h1]
    exact coeff_planeEisenstein (gammaN N) n f (ptOf x) i.castSucc j.castSucc m
  have e2 : ((((cuspSeedInv (gammaNPlaneData N) (gammaNPlaneData_lam_mem N) (f := f) :
      Form (F := Coef n) faceSet 2) : RawForm Face (Coef n) 2) x
        ![Pi.single i 1, Pi.single j 1]).toPoly).coeff m =
      (seedForm n (hfun f) (ptOf x) i.castSucc j.castSucc).coeff m := by
    have := congrArg (·.coeff m) h2
    exact this
  rw [e1, e2, h3, add_sub_cancel_left]

/-- The group restriction `H²(Γ(N), E_n) → H²(Γ_P, E_n)` (along the identity of the coefficients). -/
def resP : groupCohomology.H2 (Rep.of (gammaRho (gammaN N) n)) →ₗ[ℝ]
    groupCohomology.H2 (Rep.of ((gammaNPlaneData N).rhoR n)) :=
  (groupCohomology.map (inclP N)
    (resMor (inclP N) ((gammaNPlaneData N).rhoR n) (gammaRho (gammaN N) n)
      (rhoR_eq_gammaRho (gammaNPlaneData N) (inclP N) (fun g => gammaNPlaneData_plm N g))) 2).hom

/-- **Constant term, reduction.** The restriction to `Γ_P` of the class of `𝓔_P(ω_h)` is the class
of the seed (the identity coset of `Γ_P \ Γ`, scalar `1`) plus the class of the non-identity part
`restFaceForm`. -/
theorem resP_eisensteinClass_eq :
    resP N n (eisensteinClass_gammaN N n f hn) =
      cuspSeedClass (gammaNPlaneData N) (gammaNPlaneData_lam_mem N) (f := f) +
        ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty
          (gammaNPlaneData N).action ((gammaNPlaneData N).rhoR n) (restFaceForm N n f hn) := by
  have h := eisensteinClass_gammaN_face N n f hn
  change ZigZag.deRhamClass _ _ _ _ _ (eisensteinFace N n f hn) = resP N n _ at h
  rw [← h, ← deRhamClass_cuspSeed (gammaNPlaneData N) (gammaNPlaneData_lam_mem N) (f := f),
    ← map_add]
  congr 1
  unfold restFaceForm
  abel

/-- **The constant-term statement `r_P 𝓔_P(ξ) = ξ`** at the plane face
for the identity cusp: the non-identity part of the series has zero class in `H²(Γ_P, E_n)`. This
is the analytic core (unfolding over the nontrivial double coset `P s₂₃ P`, vanishing of the
zero modes by cuspidality, and Kasuya's comparison); it is NOT proved here. -/
def ConstantTermVanishing : Prop :=
  ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty (gammaNPlaneData N).action
    ((gammaNPlaneData N).rhoR n) (restFaceForm N n f hn) = 0

/-- **The constant term of the literal class is the seed class, exactly when the non-identity part
is cohomologically trivial.** -/
theorem resP_eisensteinClass_iff :
    resP N n (eisensteinClass_gammaN N n f hn) =
      cuspSeedClass (gammaNPlaneData N) (gammaNPlaneData_lam_mem N) (f := f) ↔
    ConstantTermVanishing N n f hn := by
  rw [resP_eisensteinClass_eq, ConstantTermVanishing]
  exact ⟨fun h => by simpa using h, fun h => by rw [h, add_zero]⟩

end GammaN

end TernaryPeriodPolynomials.Argument.EisensteinClass
