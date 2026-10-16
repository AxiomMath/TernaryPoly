module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedForms.LevelOneFree
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Cell.KNeg
public import TernaryPeriodPolynomials.EisensteinSeries.Class.CoefTwist
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.ReflectionLevel

@[expose] public section


/-!
# R1c remainder: the reflected half of `g5_levelOne` is the antiholomorphic seed of `h^*`

Formalized by Claude Sonnet 5.5.
Paper: Lemma C.3 and the finite reflection projection.

`eps_seedClass`: `(epsHom, epsRep)_* complexifyG [seed h] = (-1)^(n+1) • complexifyG [seedConj h^*]`, where `h^* z = conj (h (-conj z))`.
The sign is `(-1)^(n+1)` (the reflection pullback `r^* omega_h = (-1)^(n+1) rho(r) conj omega_{h^*}`), not `(-1)^n`.
-/

open scoped MatrixGroups ContDiff
open Matrix GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPoly.SmoothLocalDeRham TernaryPoly.SmoothCoveringDeRham ComplexConjugate

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FormSeedBridge

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument.SeedC3.Psi TernaryPeriodPolynomials.Argument.EisensteinClass
  TernaryPeriodPolynomials.Argument.SeedC3S4c TernaryPeriodPolynomials.Argument
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

theorem rPrime_eq_diag : (rPrime : Matrix (Fin 3) (Fin 3) ℤ) = Matrix.diagonal ![1, -1, -1] := by
  rw [rPrime_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem epsConj_eq_rPrime (γ : SL(3, ℤ)) : epsConj γ = rPrime * γ * rPrime := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, rPrime_eq_diag]
  ext i j
  rw [epsConj_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j <;> simp

theorem reflMap5_planeAct (g : SL(3, ℤ)) {p : Fin 5 → ℝ} (hp : p ∈ Omega) :
    reflMap5 (planeAct (realMat g) p) = planeAct (realMat (epsConj g)) (reflMap5 p) := by
  have hg : (realMat g).det = 1 := det_realMat g
  have hr : (realMat rPrime).det = 1 := det_realMat rPrime
  have hgp : planeAct (realMat g) p ∈ Omega := planeAct_mem hg hp
  rw [← planeAct_rPrime hgp, ← planeAct_rPrime hp, epsConj_eq_rPrime, realMat_mul, realMat_mul,
    ← planeAct_mul hr hp, ← planeAct_mul hg hp]
  congr 1
  have : realMat rPrime * realMat rPrime = 1 := by rw [← realMat_mul, rPrime_mul_self, realMat_one]
  rw [Matrix.mul_assoc, this, Matrix.mul_one]

theorem ptOf_injective {x y : Face} (h : ptOf x = ptOf y) : x = y := by
  funext a
  have := congrFun h a.castSucc
  fin_cases a <;> simpa [ptOf] using this

variable (N : ℕ)

theorem reflFCLM_act (g : ↥(gammaNP N)) {x : Face} (hx : x ∈ faceSet) :
    reflFCLM ((gammaNPlaneData N).act g x) = (gammaNPlaneData N).act (epsHom N g) (reflFCLM x) := by
  apply ptOf_injective
  have e1 := planeAct_plm_ptOf (gammaNPlaneData N) g hx
  have e2 := planeAct_plm_ptOf (gammaNPlaneData N) (epsHom N g) (reflFCLM_mem hx)
  rw [gammaNPlaneData_plm] at e1 e2
  rw [ptOf_reflFCLM, ← e1, ← e2, ptOf_reflFCLM]
  exact reflMap5_planeAct g.1 (ptOf_mem hx)

/-- **The reflection of the face is equivariant along the conjugation `ε`.** -/
def reflEquivMap : EquivMap isOpen_faceSet isOpen_faceSet (gammaNPlaneData N).action (gammaNPlaneData N).action
    (epsHom N) where
  φ := reflFCLM
  smooth := reflFCLM.contDiff.contDiffOn
  mapsTo _ hx := reflFCLM_mem hx
  equiv g _ hx := reflFCLM_act N g hx

theorem rGL_eq_epsJ : rGL = epsJ := by
  apply Units.ext
  rw [epsJ_val]
  rfl

variable [NeZero N] (n : ℕ)

theorem reflCoefCLM_eq (v : Coef n) : reflCoefCLM n v = GeneralEisenstein.realCoefficient n epsJ v := by
  change reflCoef n v = _
  unfold reflCoef
  rw [rGL_eq_epsJ]
  rfl

omit [NeZero N] in
/-- `ρ(ε)` intertwines the `ε`-conjugated and the original coefficient representation of `Γ_P`. -/
theorem reflCoef_intertwines :
    Intertwines (reflCoefCLM n) (((gammaNPlaneData N).rhoR n).comp (epsHom N)) ((gammaNPlaneData N).rhoR n) := by
  intro g v
  change (gammaNPlaneData N).rhoR n g (reflCoefCLM n v) = reflCoefCLM n ((gammaNPlaneData N).rhoR n (epsHom N g) v)
  rw [reflCoefCLM_eq, reflCoefCLM_eq]
  have h1 : (gammaNPlaneData N).rhoR n g (GeneralEisenstein.realCoefficient n epsJ v) =
      GeneralEisenstein.realCoefficient n (Matrix.SpecialLinearGroup.mapGL ℝ g.1)
        (GeneralEisenstein.realCoefficient n epsJ v) :=
    rho_gammaNRep N n g _
  have h2 : (gammaNPlaneData N).rhoR n (epsHom N g) v =
      GeneralEisenstein.realCoefficient n (Matrix.SpecialLinearGroup.mapGL ℝ (epsHom N g).1) v :=
    rho_gammaNRep N n (epsHom N g) v
  rw [h1, h2]
  exact (eps_intertwine N n g v).symm

omit [NeZero N] in
theorem reflCoefCLM_comp_self : (reflCoefCLM n).comp (reflCoefCLM n) = ContinuousLinearMap.id ℝ (Coef n) := by
  ext q
  change reflCoefCLM n (reflCoefCLM n q) = q
  have key : ∀ v : HomogeneousPoly n, GeneralEisenstein.realCoefficient n epsJ
      (GeneralEisenstein.realCoefficient n epsJ v) = v := fun v => by
    rw [← Module.End.mul_apply, ← map_mul, epsJ_mul_self, map_one]
    rfl
  rw [reflCoefCLM_eq, reflCoefCLM_eq]
  exact key q

section Main

variable (h hs : ℂ → ℂ) (Gm Gms : ℕ → ℂ → ℂ)
  (hh : DifferentiableOn ℂ h upperSet)
  (hG : ∀ j z, 0 < z.im → HasDerivAt (Gm j) (h z * z ^ j) z)
  (hmod : ∀ g : ↥(gammaNP N), ∀ z : ℂ, 0 < z.im →
    h (mob ((gammaNPlaneData N).lam g) z) = dnm ((gammaNPlaneData N).lam g) z ^ (n + 3) * h z)
  (hhs : DifferentiableOn ℂ hs upperSet)
  (hGs : ∀ j z, 0 < z.im → HasDerivAt (Gms j) (hs z * z ^ j) z)
  (hmods : ∀ g : ↥(gammaNP N), ∀ z : ℂ, 0 < z.im →
    hs (mob ((gammaNPlaneData N).lam g) z) = dnm ((gammaNPlaneData N).lam g) z ^ (n + 3) * hs z)
  (hrel : ∀ z : ℂ, 0 < z.im → hs z = conj (h (-conj z)))

omit [NeZero N] in
include hrel in
/-- The reflected seed form: the coefficient twist of the pullback of the seed along the reflection of the face is `(-1)^{n+1}` times the antiholomorphic seed of `h^*`. -/
theorem reflected_form_eq :
    (twInv (reflCoef_intertwines N n)
      (pullInv (reflEquivMap N) (fun _ => rfl) ((gammaNPlaneData N).seedInv h n Gm hh hG hmod)) :
        ZigZag.invClosed isOpen_faceSet (gammaNPlaneData N).action ((gammaNPlaneData N).rhoR n)) =
      ((-1 : ℝ) ^ (n + 1)) • (gammaNPlaneData N).seedConjInv hs n Gms hhs hGs hmods := by
  apply Subtype.ext
  have hpb : (pullInv (reflEquivMap N) (fun _ => rfl) ((gammaNPlaneData N).seedInv h n Gm hh hG hmod) :
      ZigZag.invClosed isOpen_faceSet (gammaNPlaneData N).action (((gammaNPlaneData N).rhoR n).comp (epsHom N))).1 =
      ZigZag.pullForm isOpen_faceSet reflAction reflGen 2 (d isOpen_faceSet 1 (etaForm h hh n)) := by
    apply Form.ext
    intro x hx
    change (pullBack isOpen_faceSet (reflEquivMap N).smooth (reflEquivMap N).mapsTo 2
      (d isOpen_faceSet 1 (etaForm h hh n)) : RawForm Face (Coef n) 2) x = _
    rw [pullBack_apply isOpen_faceSet _ _ _ hx, ZigZag.pullForm_apply isOpen_faceSet reflAction reflGen _ hx]
    have h1 : reflAction.act reflGen = ⇑reflFCLM := funext reflAction_act_gen
    rw [h1]
    rfl
  change ZigZag.twForm (reflCoefCLM n) 2
      (pullInv (reflEquivMap N) (fun _ => rfl) ((gammaNPlaneData N).seedInv h n Gm hh hG hmod)).1 = _
  rw [hpb, pullForm_refl_seed n h hs hh hhs hrel, _root_.map_smul, ← ZigZag.twForm_mul]
  have hcc : (reflCoefCLM n).comp ((reflCoefCLM n).comp (conjCLM n)) = conjCLM n := by
    rw [← ContinuousLinearMap.comp_assoc, reflCoefCLM_comp_self, ContinuousLinearMap.id_comp]
  rw [hcc]
  rfl

theorem complexifyG_eps_map (x : groupCohomology.H2 (Rep.of ((gammaNPlaneData N).rhoR n))) :
    complexifyG N n ((groupCohomology.map (MonoidHom.id (gammaNP N)) (twMor (reflCoef_intertwines N n)) 2).hom
      ((groupCohomology.map (epsHom N) (resMor (epsHom N) (((gammaNPlaneData N).rhoR n).comp (epsHom N))
        ((gammaNPlaneData N).rhoR n) (fun _ => rfl)) 2).hom x)) =
      (groupCohomology.map (epsHom N) (epsRep N n) 2).hom (complexifyG N n x) := by
  induction x using groupCohomology.H2_induction_on with
  | h c =>
    rw [groupCohomology.H2π_comp_map_apply, groupCohomology.H2π_comp_map_apply, complexifyG_H2π,
      complexifyG_H2π, groupCohomology.H2π_comp_map_apply]
    refine congrArg (CategoryTheory.ConcreteCategory.hom (groupCohomology.H2π (gammaNRep N n))) ?_
    apply Subtype.ext
    funext p
    exact reflCoefCLM_eq n (c.1 (epsHom N p.1, epsHom N p.2))

include hrel in
/-- **The reflected half of `g5_levelOne`, identified (R1c remainder).**  For `h`, `h^* = \overline{h(-\bar·)}` satisfying the hypotheses of the seed class of `Γ_P = Γ(N) ∩ P(ℤ)`,
the conjugation by `ε = diag(-1,1,1)` (with the coefficient map `ρ(ε)`) carries the (complexified) seed class of `h` to `(-1)^{n+1}` times the (complexified) antiholomorphic seed class
of `h^*`.  (Hence the reflected summand of the model's identity-plane class is the antiholomorphic seed of `H'^*`, with the sign `(-1)^{n+1}` of the reflection pullback `r^*ω_h = (-1)^{n+1}ρ(r)\overline{ω_{h^*}}`.) -/
theorem eps_seedClass :
    (groupCohomology.map (epsHom N) (epsRep N n) 2).hom
        (complexifyG N n ((gammaNPlaneData N).seedClass h n Gm hh hG hmod)) =
      ((-1 : ℂ) ^ (n + 1)) • complexifyG N n ((gammaNPlaneData N).seedConjClass hs n Gms hhs hGs hmods) := by
  have e1 := deRhamClass_natural (reflEquivMap N) convex_faceSet faceSet_nonempty convex_faceSet
    faceSet_nonempty (ρ := ((gammaNPlaneData N).rhoR n).comp (epsHom N)) (ρ' := (gammaNPlaneData N).rhoR n)
    (fun _ => rfl) ((gammaNPlaneData N).seedInv h n Gm hh hG hmod)
  have e2 := deRhamClass_twist convex_faceSet faceSet_nonempty (reflCoef_intertwines N n)
    (pullInv (reflEquivMap N) (fun _ => rfl) ((gammaNPlaneData N).seedInv h n Gm hh hG hmod))
  rw [e1, (gammaNPlaneData N).deRhamClass_seedInv h n Gm hh hG hmod] at e2
  have e3 := reflected_form_eq N n h hs Gm Gms hh hG hmod hhs hGs hmods hrel
  rw [e3, _root_.map_smul, (gammaNPlaneData N).deRhamClass_seedConjInv hs n Gms hhs hGs hmods] at e2
  rw [← complexifyG_eps_map N n, ← e2, _root_.map_smul]
  rw [← Complex.coe_smul]
  push_cast
  rfl

end Main

end TernaryPeriodPolynomials.Argument.FormSeedBridge
