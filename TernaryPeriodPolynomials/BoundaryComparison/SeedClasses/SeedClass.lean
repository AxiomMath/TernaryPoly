module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.SeedDatum

@[expose] public section


/-!
# The class of the seed in `H²(Γ_P, E_n)` and its closed-form cocycle

Paper: Lemma C.3 (`ar:lem:seed`),
the seed `ω_h`, its class on the face `e(P) = ℝ² × ℍ` and the Hochschild--Serre `(1,1)` component.

Conventions (all fixed here).

* Coefficients: `E_n = Sym^n((ℂ³)*) ⊗ det⁻¹` as the polynomials in `X, Y, Z` homogeneous of degree
  `n`, regarded as a REAL representation (`PlaneData.rhoR`) of the group `G = Γ_P` through
  `ρ(g) q (𝐗) = det(g)⁻¹ q(g⁻¹ 𝐗)` (`RhoAction.rho`), `g = [[λ_g, w_g], [0, 1]]`.
* Action on the face: `D.act g` (`PlaneAction.lean`), `act (gh) = act g ∘ act h`; pullback of
  forms `P1 g = g^*`; the group cohomology is Mathlib's `groupCohomology.H2 (Rep.of ρ)` with
  inhomogeneous cocycles `c(gh, j) + c(g, h) = g • c(h, j) + c(g, hj)` (`IsCocycle₂`).
* The cochain is `c(g, k) = k^*θ_g + ρ(g) θ_k - θ_{gk}` (a constant), where `dη = ω_h` and
  `dθ_g = g^*η - ρ(g) η` (`seedDatum`, `dTheta_eq`, `toPoly_d_etaForm`).
* Closed form (`toPoly_cochain`): for the moment primitives `G_j` normalized by `G_j(i) = 0`,
  `c(g, k) = (n+1)⁻¹ · (ρ(g) - ρ(g₀)) ε_{λ_k} / Z`, with `g₀ = [[λ_g, 0], [0, 1]]`.

Formalized by Claude Sonnet 5.5.
-/

open MvPolynomial
open scoped ContDiff

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3

open Calc Psi

theorem ddiv_zero : ddiv 0 = 0 := by
  apply MvPolynomial.ext; intro d; simp [ddiv]

theorem ddiv_sum {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial (Fin 3) ℂ) :
    ddiv (∑ i ∈ s, f i) = ∑ i ∈ s, ddiv (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ddiv_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ddiv_add, ih]

theorem rename_eichlerPoly (n : ℕ) (Gm : ℕ → ℂ → ℂ) (w : ℂ) :
    rename Fin.castSucc (eichlerPoly n Gm w) =
      ∑ j ∈ Finset.range (n + 2), C (Gm j w * coefB n j) * monoY n j := by
  simp only [eichlerPoly, map_sum, map_mul, rename_C, map_pow, rename_X]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [coefB, monoY]
  have h1 : (Fin.castSucc (1 : Fin 2) : Fin 3) = 1 := rfl
  have h0 : (Fin.castSucc (0 : Fin 2) : Fin 3) = 0 := rfl
  rw [h1, h0]
  simp only [map_mul, map_pow, map_neg, map_one, map_natCast]
  ring

namespace PlaneData

variable {G : Type} [Group G] (D : PlaneData G) (h : ℂ → ℂ) (n : ℕ) (Gm : ℕ → ℂ → ℂ)

omit h in
/-- The binary Eichler primitive viewed as a polynomial in `(X, Y, Z)` (no `Z`). -/
def eichler3 (w : ℂ) : MvPolynomial (Fin 3) ℂ := rename Fin.castSucc (eichlerPoly n Gm w)

omit h in
theorem toPoly_thetaFun (g : G) (x : Face) :
    Coef.toPoly (D.thetaFun n Gm g x) = C (((n : ℂ) + 1)⁻¹) *
      ddiv (rho (D.plm g) (eichler3 n Gm (faceTau x)) -
        rho (parabolicMatrix (D.lamM g) 0) (eichler3 n Gm (faceTau x))) := by
  have hA := D.lamM_det g
  unfold thetaFun
  rw [toPoly_sum]
  simp only [Coef.toPoly_smul]
  rw [eichler3, rename_eichlerPoly, D.plm_eq, rho_sum_poly _ _ hA, rho_sum_poly _ _ hA,
    ← Finset.sum_sub_distrib, ddiv_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ n + 1 := by simpa [Nat.lt_succ_iff] using hj
  rw [D.toPoly_thetaVec n g hj', rho_C_mul_poly _ _ hA, rho_C_mul_poly _ _ hA, ← mul_sub,
    ddiv_C_mul, thetaR]
  simp only [map_mul]
  ring

open TernaryPoly.SmoothLocalDeRham TernaryPoly.SmoothSingularComparison ZigZag in
/-- **The zig-zag cochain, pointwise**: `c(g,k) = Θ_g(k x) + ρ(g)Θ_k(x) - Θ_{gk}(x)`. -/
theorem cochain_eval (hh : DifferentiableOn ℂ h upperSet)
    (hG : ∀ j z, 0 < z.im → HasDerivAt (Gm j) (h z * z ^ j) z)
    (hmod : ∀ g : G, ∀ z : ℂ, 0 < z.im →
      h (mob (D.lam g) z) = dnm (D.lam g) z ^ (n + 3) * h z) (g k : G) {x : Face}
    (hx : x ∈ faceSet) :
    cochain (laws isOpen_faceSet convex_faceSet faceSet_nonempty D.action (D.rhoR n))
        (D.seedDatum h n Gm hh hG hmod) g k =
      D.thetaFun n Gm g (D.act k x) + D.rhoCoef n g (D.thetaFun n Gm k x) -
        D.thetaFun n Gm (g * k) x := by
  have e := c_cochain (laws isOpen_faceSet convex_faceSet faceSet_nonempty D.action (D.rhoR n))
    (D.seedDatum h n Gm hh hG hmod) g k
  have hax : D.act k x ∈ faceSet := D.act_mapsTo k hx
  have e2 := congrArg (fun w : Form (F := Coef n) faceSet 0 => (w : RawForm Face (Coef n) 0) x) e
  apply (zeroEquiv (E := Face) (F := Coef n)).injective
  simp only [deRhamConstant, constant, LinearMap.coe_mk, AddHom.coe_mk,
    ofFunction_apply _ _ hx] at e2
  have hsum : ∀ A B C : Form (F := Coef n) faceSet 0,
      ((A + B - C : Form (F := Coef n) faceSet 0) : RawForm Face (Coef n) 0) x =
        (A : RawForm Face (Coef n) 0) x + (B : RawForm Face (Coef n) 0) x -
          (C : RawForm Face (Coef n) 0) x := fun _ _ _ => rfl
  refine e2.trans ?_
  rw [hsum, pullForm_apply isOpen_faceSet D.action k _ hx, pullRaw_zero, twForm_apply]
  have t1 : ((D.seedDatum h n Gm hh hG hmod).θ g : RawForm Face (Coef n) 0) (D.action.act k x) =
      zeroEquiv (D.thetaFun n Gm g (D.act k x)) :=
    ofFunction_apply (D.thetaFun n Gm g) (D.thetaFun_contDiffOn h n Gm g hG) hax
  have t2 : ((D.seedDatum h n Gm hh hG hmod).θ k : RawForm Face (Coef n) 0) x =
      zeroEquiv (D.thetaFun n Gm k x) :=
    ofFunction_apply (D.thetaFun n Gm k) (D.thetaFun_contDiffOn h n Gm k hG) hx
  have t3 : ((D.seedDatum h n Gm hh hG hmod).θ (g * k) : RawForm Face (Coef n) 0) x =
      zeroEquiv (D.thetaFun n Gm (g * k) x) :=
    ofFunction_apply (D.thetaFun n Gm (g * k)) (D.thetaFun_contDiffOn h n Gm (g * k) hG) hx
  rw [t1, t2, t3]
  simp only [map_add, map_sub]
  congr 2

/-- The base point `x₀ = (0, 0, 0, 1)` of the face, with `τ(x₀) = i`. -/
def basePt : Face := ![0, 0, 0, 1]

theorem basePt_mem : basePt ∈ faceSet := by simp [basePt, faceSet]

theorem faceTau_basePt : faceTau basePt = Complex.I := by simp [basePt, faceTau]

omit h n Gm in
theorem faceTau_act_basePt (k : G) : faceTau (D.act k basePt) = mob (D.lam k) Complex.I := by
  rw [D.faceTau_act, faceTau_basePt]

omit h in
theorem thetaFun_basePt (hG0 : ∀ j, Gm j Complex.I = 0) (g : G) :
    D.thetaFun n Gm g basePt = 0 := by
  simp [thetaFun, faceTau_basePt, hG0]

omit h in
/-- **The closed-form cocycle of the seed** (polynomial in `X, Y, Z`):
`c(g, k) = (n+1)⁻¹ · (ρ([[λ_g, w_g], [0, 1]]) - ρ([[λ_g, 0], [0, 1]])) ε_{λ_k} / Z`,
`ε_γ` the Eichler cocycle of the moment primitives `Gm` (`eichlerCocycle`), viewed as a binary
form `ε_γ(X, Y)` inside `ℂ[X, Y, Z]`. -/
def seedCocycleFormula (g k : G) : MvPolynomial (Fin 3) ℂ :=
  C (((n : ℂ) + 1)⁻¹) *
    ddiv (rho (D.plm g) (rename Fin.castSucc (eichlerCocycle n Gm (D.lam k))) -
      rho (parabolicMatrix (D.lamM g) 0) (rename Fin.castSucc (eichlerCocycle n Gm (D.lam k))))

open TernaryPoly.SmoothLocalDeRham TernaryPoly.SmoothSingularComparison ZigZag in
/-- **The zig-zag cochain of the seed is the closed form** `seedCocycleFormula` (as polynomials in
`E_n`), when the moment primitives are normalized by `G_j(i) = 0`. -/
theorem toPoly_cochain (hh : DifferentiableOn ℂ h upperSet)
    (hG : ∀ j z, 0 < z.im → HasDerivAt (Gm j) (h z * z ^ j) z) (hG0 : ∀ j, Gm j Complex.I = 0)
    (hmod : ∀ g : G, ∀ z : ℂ, 0 < z.im →
      h (mob (D.lam g) z) = dnm (D.lam g) z ^ (n + 3) * h z) (g k : G) :
    Coef.toPoly (cochain (laws isOpen_faceSet convex_faceSet faceSet_nonempty D.action
        (D.rhoR n)) (D.seedDatum h n Gm hh hG hmod) g k) = D.seedCocycleFormula n Gm g k := by
  rw [D.cochain_eval h n Gm hh hG hmod g k basePt_mem, Coef.toPoly_sub, Coef.toPoly_add,
    D.thetaFun_basePt n Gm hG0 k, D.thetaFun_basePt n Gm hG0 (g * k), map_zero, Coef.toPoly_zero,
    add_zero, sub_zero, D.toPoly_thetaFun n Gm, faceTau_act_basePt]
  rfl

open TernaryPoly.SmoothLocalDeRham TernaryPoly.SmoothSingularComparison ZigZag in
/-- The seed `ω_h = dη` as a closed `ρ`-equivariant 2-form on the face. -/
def seedInv (hh : DifferentiableOn ℂ h upperSet)
    (hG : ∀ j z, 0 < z.im → HasDerivAt (Gm j) (h z * z ^ j) z)
    (hmod : ∀ g : G, ∀ z : ℂ, 0 < z.im →
      h (mob (D.lam g) z) = dnm (D.lam g) z ^ (n + 3) * h z) :
    invClosed isOpen_faceSet D.action (D.rhoR n) :=
  ⟨d isOpen_faceSet 1 (etaForm h hh n), d_squared isOpen_faceSet 1 _, fun g => by
    have e := D.dTheta_eq h n Gm hh hG hmod g
    have e' : pullForm isOpen_faceSet D.action g 1 (etaForm h hh n) =
        d isOpen_faceSet 0 (D.thetaForm h n Gm g hG) +
          twForm (repCLM (D.rhoR n) g) 1 (etaForm h hh n) := by rw [e]; abel
    rw [← d_pullForm, e', map_add, d_squared, zero_add, d_twForm]⟩

open CategoryTheory TernaryPoly.SmoothLocalDeRham TernaryPoly.SmoothSingularComparison ZigZag in
/-- **The class of the seed** in `H²(G, E_n)` (`E_n` as a real representation): the class of the
zig-zag datum `(η, θ_g)`. -/
def seedClass (hh : DifferentiableOn ℂ h upperSet)
    (hG : ∀ j z, 0 < z.im → HasDerivAt (Gm j) (h z * z ^ j) z)
    (hmod : ∀ g : G, ∀ z : ℂ, 0 < z.im →
      h (mob (D.lam g) z) = dnm (D.lam g) z ^ (n + 3) * h z) :
    groupCohomology.H2 (Rep.of (D.rhoR n)) :=
  zigzagClass (laws isOpen_faceSet convex_faceSet faceSet_nonempty D.action (D.rhoR n))
    (D.seedDatum h n Gm hh hG hmod)

open TernaryPoly.SmoothLocalDeRham TernaryPoly.SmoothSingularComparison ZigZag in
/-- The de Rham class map of the face sends the seed to `seedClass`. -/
theorem deRhamClass_seedInv (hh : DifferentiableOn ℂ h upperSet)
    (hG : ∀ j z, 0 < z.im → HasDerivAt (Gm j) (h z * z ^ j) z)
    (hmod : ∀ g : G, ∀ z : ℂ, 0 < z.im →
      h (mob (D.lam g) z) = dnm (D.lam g) z ^ (n + 3) * h z) :
    deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty D.action (D.rhoR n)
      (D.seedInv h n Gm hh hG hmod) = D.seedClass h n Gm hh hG hmod :=
  deRhamClass_eq isOpen_faceSet convex_faceSet faceSet_nonempty D.action (D.rhoR n)
    (D.seedInv h n Gm hh hG hmod) (D.seedDatum h n Gm hh hG hmod)

open TernaryPoly.SmoothLocalDeRham in
/-- **`dη = ω_h`**: the coefficients of `dη` on the coordinate basis are the `seedForm`. -/
theorem toPoly_d_etaForm (hh : DifferentiableOn ℂ h upperSet) {x : Face} (hx : x ∈ faceSet)
    (i j : Fin 4) :
    Coef.toPoly ((d isOpen_faceSet 1 (etaForm h hh n) : RawForm Face (Coef n) 2) x
        ![Pi.single i 1, Pi.single j 1]) =
      seedForm n h (ptOf x) i.castSucc j.castSucc := by
  rw [d_apply isOpen_faceSet _ hx]
  have heq : (etaForm h hh n : RawForm Face (Coef n) 1) =ᶠ[nhds x] etaRaw h n := by
    filter_upwards [isOpen_faceSet.mem_nhds hx] with y hy using restrictForm_apply _ _ hy
  rw [heq.extDeriv_eq (𝕜 := ℝ)]
  exact toPoly_dEta_basis h hh n hx i j

end PlaneData

end TernaryPeriodPolynomials.Argument.SeedC3
