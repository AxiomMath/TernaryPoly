module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.SeedClass

@[expose] public section


/-!
# The antiholomorphic seed: complex conjugation of the coefficients

Paper: Lemma C.3 (`ar:lem:seed`)
and the sentence after Proposition `ar:prop:convergence` (holomorphic and antiholomorphic seeds).

The antiholomorphic seed is the coefficientwise complex conjugate `ω̄_h = conj ω_h`
(`Coef.conjCoef`, `conjCLM`); since `ρ` has real coefficients (`map_conj_rho`) conjugation commutes
with the coefficient action, so it carries zig-zag data to zig-zag data (`ZigZag.Datum.twist`) and
the cocycle to its conjugate (`cochain_seedConj`, `toPoly_cochain_conj`).

Formalized by Claude Sonnet 5.5.
-/

open MvPolynomial
open scoped ContDiff

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3

open Calc Psi

/-- `rho` has real coefficients: it commutes with coefficientwise complex conjugation. -/
theorem map_conj_rho (g : Matrix (Fin 3) (Fin 3) ℝ) (q : MvPolynomial (Fin 3) ℂ) :
    MvPolynomial.map (starRingEnd ℂ) (rho g q) = rho g (MvPolynomial.map (starRingEnd ℂ) q) := by
  unfold rho
  rw [map_mul, MvPolynomial.map_C, MvPolynomial.map_bind₁]
  congr 1
  · simp
  · congr 2
    funext i
    simp [map_sum, MvPolynomial.map_C, MvPolynomial.map_X]

namespace Coef

variable {n : ℕ}

/-- Coefficientwise complex conjugation on `E_n`. -/
def conjCoef (q : Coef n) : Coef n :=
  ⟨MvPolynomial.map (starRingEnd ℂ) (toPoly q),
    (MvPolynomial.mem_homogeneousSubmodule n _).mpr ((toPoly_isHomogeneous q).map _)⟩

@[simp] theorem toPoly_conjCoef (q : Coef n) :
    toPoly (conjCoef q) = MvPolynomial.map (starRingEnd ℂ) (toPoly q) := rfl

/-- Complex conjugation of coefficients as a real-linear map. -/
def conjLin (n : ℕ) : Coef n →ₗ[ℝ] Coef n where
  toFun := conjCoef
  map_add' q r := by
    apply toPoly_injective
    simp
  map_smul' c q := by
    apply toPoly_injective
    have e1 : c • q = ((c : ℂ) • q : Coef n) := (Complex.coe_smul c q).symm
    have e2 : c • conjCoef q = ((c : ℂ) • conjCoef q : Coef n) := (Complex.coe_smul c _).symm
    simp only [RingHom.id_apply]
    rw [e1, e2]
    simp only [toPoly_conjCoef, toPoly_smul, map_mul, MvPolynomial.map_C, Complex.conj_ofReal]

end Coef

/-- Complex conjugation of the coefficients, as a continuous real-linear map. -/
def conjCLM (n : ℕ) : Coef n →L[ℝ] Coef n := LinearMap.toContinuousLinearMap (Coef.conjLin n)

theorem conjCLM_apply {n : ℕ} (q : Coef n) : conjCLM n q = Coef.conjCoef q := rfl


namespace ZigZag

open TernaryPoly.SmoothLocalDeRham TernaryPoly.SmoothSingularComparison

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [CompleteSpace F]
  {s : Set E} {G : Type} [Group G]

/-- A continuous real-linear endomorphism `L` of the coefficients commuting with `ρ` carries
zig-zag data for `ω` to zig-zag data for `L ω`. -/
def Datum.twist (hs : IsOpen s) (A : Action G s) (ρ : Representation ℝ G F) (L : F →L[ℝ] F)
    (hL : ∀ g, L.comp (repCLM ρ g) = (repCLM ρ g).comp L) {om : Form (F := F) s 2}
    (D : Datum (d hs 0) (d hs 1) (fun g => pullForm hs A g 1)
      (fun g => twForm (repCLM ρ g) 1) om) :
    Datum (d hs 0) (d hs 1) (fun g => pullForm hs A g 1)
      (fun g => twForm (repCLM ρ g) 1) (twForm L 2 om) where
  η := twForm L 1 D.η
  θ g := twForm L 0 (D.θ g)
  dη := by rw [d_twForm, D.dη]
  dθ g := by
    rw [d_twForm, D.dθ, map_sub, pullForm_twForm, ← twForm_mul, ← twForm_mul, hL]

theorem twist_cochain (hs : IsOpen s) (hc : Convex ℝ s) (hne : s.Nonempty) (A : Action G s)
    (ρ : Representation ℝ G F) (L : F →L[ℝ] F)
    (hL : ∀ g, L.comp (repCLM ρ g) = (repCLM ρ g).comp L) {om : Form (F := F) s 2}
    (D : Datum (d hs 0) (d hs 1) (fun g => pullForm hs A g 1)
      (fun g => twForm (repCLM ρ g) 1) om) (g k : G) :
    cochain (laws hs hc hne A ρ) (D.twist hs A ρ L hL) g k =
      L (cochain (laws hs hc hne A ρ) D g k) := by
  apply (laws hs hc hne A ρ).c_injective
  have e1 := c_cochain (laws hs hc hne A ρ) (D.twist hs A ρ L hL) g k
  have e2 := c_cochain (laws hs hc hne A ρ) D g k
  have hc' : deRhamConstant s (L (cochain (laws hs hc hne A ρ) D g k)) =
      twForm L 0 (deRhamConstant s (cochain (laws hs hc hne A ρ) D g k)) :=
    (twForm_constant L _).symm
  rw [hc']
  refine e1.trans ?_
  rw [e2]
  simp only [Datum.twist, map_add, map_sub]
  rw [pullForm_twForm, ← twForm_mul, ← twForm_mul, hL]

end ZigZag


namespace PlaneData

variable {G : Type} [Group G] (D : PlaneData G) (h : ℂ → ℂ) (n : ℕ) (Gm : ℕ → ℂ → ℂ)

omit h Gm in
theorem rhoCoef_conjCoef (g : G) (q : Coef n) :
    D.rhoCoef n g (Coef.conjCoef q) = Coef.conjCoef (D.rhoCoef n g q) := by
  apply Coef.toPoly_injective
  rw [D.toPoly_rhoCoef, Coef.toPoly_conjCoef, Coef.toPoly_conjCoef, D.toPoly_rhoCoef,
    map_conj_rho]

omit h Gm in
theorem conjCLM_comm (g : G) :
    (conjCLM n).comp (ZigZag.repCLM (D.rhoR n) g) =
      (ZigZag.repCLM (D.rhoR n) g).comp (conjCLM n) := by
  ext q
  simp only [ContinuousLinearMap.comp_apply, repCLM_rhoR]
  exact (D.rhoCoef_conjCoef n g q).symm

open TernaryPoly.SmoothLocalDeRham ZigZag in
/-- **The zig-zag datum of the antiholomorphic seed** `ω̄_h = conj ω_h`: `(conj η, conj θ_g)`. -/
def seedConjDatum (hh : DifferentiableOn ℂ h upperSet)
    (hG : ∀ j z, 0 < z.im → HasDerivAt (Gm j) (h z * z ^ j) z)
    (hmod : ∀ g : G, ∀ z : ℂ, 0 < z.im →
      h (mob (D.lam g) z) = dnm (D.lam g) z ^ (n + 3) * h z) :=
  (D.seedDatum h n Gm hh hG hmod).twist isOpen_faceSet D.action (D.rhoR n) (conjCLM n)
    (fun g => D.conjCLM_comm n g)


open TernaryPoly.SmoothLocalDeRham TernaryPoly.SmoothSingularComparison ZigZag in
/-- The antiholomorphic seed `ω̄_h` as a closed `ρ`-equivariant 2-form on the face. -/
def seedConjInv (hh : DifferentiableOn ℂ h upperSet)
    (hG : ∀ j z, 0 < z.im → HasDerivAt (Gm j) (h z * z ^ j) z)
    (hmod : ∀ g : G, ∀ z : ℂ, 0 < z.im →
      h (mob (D.lam g) z) = dnm (D.lam g) z ^ (n + 3) * h z) :
    invClosed isOpen_faceSet D.action (D.rhoR n) :=
  ⟨twForm (conjCLM n) 2 (d isOpen_faceSet 1 (etaForm h hh n)), by
    rw [d_twForm, d_squared, map_zero], fun g => by
    have e : pullForm isOpen_faceSet D.action g 2 (d isOpen_faceSet 1 (etaForm h hh n)) =
        twForm (repCLM (D.rhoR n) g) 2 (d isOpen_faceSet 1 (etaForm h hh n)) :=
      (D.seedInv h n Gm hh hG hmod).2.2 g
    rw [pullForm_twForm, e, ← twForm_mul, ← twForm_mul, D.conjCLM_comm n g]⟩


open CategoryTheory TernaryPoly.SmoothLocalDeRham TernaryPoly.SmoothSingularComparison ZigZag in
/-- **The class of the antiholomorphic seed** in `H²(G, E_n)`. -/
def seedConjClass (hh : DifferentiableOn ℂ h upperSet)
    (hG : ∀ j z, 0 < z.im → HasDerivAt (Gm j) (h z * z ^ j) z)
    (hmod : ∀ g : G, ∀ z : ℂ, 0 < z.im →
      h (mob (D.lam g) z) = dnm (D.lam g) z ^ (n + 3) * h z) :
    groupCohomology.H2 (Rep.of (D.rhoR n)) :=
  zigzagClass (laws isOpen_faceSet convex_faceSet faceSet_nonempty D.action (D.rhoR n))
    (D.seedConjDatum h n Gm hh hG hmod)

open CategoryTheory TernaryPoly.SmoothLocalDeRham TernaryPoly.SmoothSingularComparison ZigZag in
/-- The de Rham class map of the face sends the antiholomorphic seed to `seedConjClass`. -/
theorem deRhamClass_seedConjInv (hh : DifferentiableOn ℂ h upperSet)
    (hG : ∀ j z, 0 < z.im → HasDerivAt (Gm j) (h z * z ^ j) z)
    (hmod : ∀ g : G, ∀ z : ℂ, 0 < z.im →
      h (mob (D.lam g) z) = dnm (D.lam g) z ^ (n + 3) * h z) :
    deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty D.action (D.rhoR n)
      (D.seedConjInv h n Gm hh hG hmod) = D.seedConjClass h n Gm hh hG hmod :=
  deRhamClass_eq isOpen_faceSet convex_faceSet faceSet_nonempty D.action (D.rhoR n)
    (D.seedConjInv h n Gm hh hG hmod) (D.seedConjDatum h n Gm hh hG hmod)

open TernaryPoly.SmoothLocalDeRham TernaryPoly.SmoothSingularComparison ZigZag in
/-- The cochain of the antiholomorphic seed is the complex conjugate of the holomorphic one. -/
theorem cochain_seedConj (hh : DifferentiableOn ℂ h upperSet)
    (hG : ∀ j z, 0 < z.im → HasDerivAt (Gm j) (h z * z ^ j) z)
    (hmod : ∀ g : G, ∀ z : ℂ, 0 < z.im →
      h (mob (D.lam g) z) = dnm (D.lam g) z ^ (n + 3) * h z) (g k : G) :
    cochain (laws isOpen_faceSet convex_faceSet faceSet_nonempty D.action (D.rhoR n))
        (D.seedConjDatum h n Gm hh hG hmod) g k =
      Coef.conjCoef (cochain (laws isOpen_faceSet convex_faceSet faceSet_nonempty D.action
        (D.rhoR n)) (D.seedDatum h n Gm hh hG hmod) g k) :=
  twist_cochain isOpen_faceSet convex_faceSet faceSet_nonempty D.action (D.rhoR n) (conjCLM n)
    (fun g => D.conjCLM_comm n g) (D.seedDatum h n Gm hh hG hmod) g k

open TernaryPoly.SmoothLocalDeRham TernaryPoly.SmoothSingularComparison ZigZag in
/-- **Closed form of the antiholomorphic cocycle**: the coefficientwise conjugate of
`seedCocycleFormula`. -/
theorem toPoly_cochain_conj (hh : DifferentiableOn ℂ h upperSet)
    (hG : ∀ j z, 0 < z.im → HasDerivAt (Gm j) (h z * z ^ j) z) (hG0 : ∀ j, Gm j Complex.I = 0)
    (hmod : ∀ g : G, ∀ z : ℂ, 0 < z.im →
      h (mob (D.lam g) z) = dnm (D.lam g) z ^ (n + 3) * h z) (g k : G) :
    Coef.toPoly (cochain (laws isOpen_faceSet convex_faceSet faceSet_nonempty D.action
        (D.rhoR n)) (D.seedConjDatum h n Gm hh hG hmod) g k) =
      MvPolynomial.map (starRingEnd ℂ) (D.seedCocycleFormula n Gm g k) := by
  rw [D.cochain_seedConj h n Gm hh hG hmod, Coef.toPoly_conjCoef,
    D.toPoly_cochain h n Gm hh hG hG0 hmod]

open TernaryPoly.SmoothLocalDeRham ZigZag in
/-- The coefficients of the antiholomorphic seed `conj ω_h` are the conjugates of `seedForm`. -/
theorem toPoly_twForm_conj_d_etaForm (hh : DifferentiableOn ℂ h upperSet) {x : Face}
    (hx : x ∈ faceSet) (i j : Fin 4) :
    Coef.toPoly ((twForm (conjCLM n) 2 (d isOpen_faceSet 1 (etaForm h hh n)) :
        RawForm Face (Coef n) 2) x ![Pi.single i 1, Pi.single j 1]) =
      MvPolynomial.map (starRingEnd ℂ) (seedForm n h (ptOf x) i.castSucc j.castSucc) := by
  rw [← toPoly_d_etaForm h n hh hx i j]
  rfl

end PlaneData

end TernaryPeriodPolynomials.Argument.SeedC3
