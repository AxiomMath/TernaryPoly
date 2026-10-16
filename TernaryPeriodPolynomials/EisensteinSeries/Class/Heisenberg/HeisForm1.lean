module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Heisenberg.HeisFrame
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.ZigZagMain

@[expose] public section



/-!
# Equivariant `1`-forms with gauge-trivialized coefficients, lattice actions, and the vanishing of exact classes

Formalized by Claude Sonnet 5.5.

* `psi1 ρt a`, `psiForm`: the `E`-valued `1`-form `ψ(v) = ρ(q) Σ_k θ^k(v) a_k(q)` with gauge-trivialized frame coefficients `a`; `gauge1` of it is `a` (`gauge1_psi1`).
* `deRhamClass_exact`: the zig-zag class (`ZigZag.deRhamClass`) of the exterior derivative of an equivariant `1`-form is zero (zig-zag with all `θ_g = 0`).
* `LatticeAction G`: a group acting on the chart by left translation through a homomorphism `nOf` into the Heisenberg group; `latAct`, `latRho` are the `ZigZag.Action` and the
  coefficient representation `g ↦ ρt (nOf g)`.
* `A2_equivariant`: for a closed equivariant `2`-form, `ω(X_b, X_c)(n x) = ρ(n) ω(X_b, X_c)(x)`; `psiForm_equivariant`: `ψ` is equivariant when its coefficients are periodic.
-/

open scoped ContDiff
open TernaryPoly.SmoothCoveringDeRham TernaryPoly.SmoothLocalDeRham
noncomputable section

namespace TernaryPeriodPolynomials.Argument.EisensteinClass.Heisenberg

section Psi

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The coframe `θ^k` at `q` as a continuous linear form. -/
def thetaL (k : Fin 3) (q : Pt) : Pt →L[ℝ] ℝ :=
  match k with
  | 0 => ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)
  | 1 => (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))
  | 2 => (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)) -
      q.1 • (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))

theorem thetaL_apply (k : Fin 3) (q v : Pt) : thetaL k q v = theta k q v := by
  fin_cases k <;> simp [thetaL, theta]

theorem thetaL_contDiff (k : Fin 3) : ContDiff ℝ ∞ (thetaL k) := by
  fin_cases k
  · exact contDiff_const
  · exact contDiff_const
  · exact contDiff_const.sub (contDiff_fst.smul contDiff_const)

/-- **The `1`-form with gauge-trivialized frame coefficients `a`**: `ψ(v) = ρ(q) Σ_k θ^k(v) a_k(q)`. -/
def psi1 (ρt : Pt → E →L[ℝ] E) (a : Pt → Fin 3 → E) (q : Pt) : Pt [⋀^Fin 1]→L[ℝ] E :=
  ContinuousAlternatingMap.ofSubsingleton ℝ Pt E (0 : Fin 1)
    ((ρt q).comp (∑ k, (thetaL k q).smulRight (a q k)))

theorem psi1_apply (ρt : Pt → E →L[ℝ] E) (a : Pt → Fin 3 → E) (q : Pt) (v : Fin 1 → Pt) :
    psi1 ρt a q v = ρt q (∑ k, theta k q (v 0) • a q k) := by
  show ((ρt q).comp (∑ k, (thetaL k q).smulRight (a q k))) (v 0) = _
  simp [thetaL_apply]

theorem psi1_contDiff {ρt : Pt → E →L[ℝ] E} (hρ : ContDiff ℝ ∞ ρt) {a : Pt → Fin 3 → E}
    (ha : ∀ k, ContDiff ℝ ∞ (fun q => a q k)) : ContDiff ℝ ∞ (psi1 ρt a) := by
  unfold psi1
  refine (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := Pt) (F := E) (0 : Fin 1)).toContinuousLinearEquiv.toContinuousLinearMap.contDiff.comp ?_
  refine hρ.clm_comp ?_
  refine ContDiff.sum fun k _ => ?_
  exact (((ContinuousLinearMap.smulRightL ℝ Pt E).contDiff.comp (thetaL_contDiff k)).clm_apply (ha k))

end Psi

section Exact

open TernaryPeriodPolynomials.Argument.SeedC3.ZigZag

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [CompleteSpace F]
  {s : Set E} {G : Type} [Group G]

/-- **The class of the exterior derivative of an equivariant `1`-form is zero** (zig-zag with all `θ_g = 0`). -/
theorem deRhamClass_exact (hs : IsOpen s) (hc : Convex ℝ s) (hne : s.Nonempty) (A : Action G s)
    (ρ : Representation ℝ G F) (om : invClosed hs A ρ) (ψ : Form (F := F) s 1)
    (hψ : ∀ g, pullForm hs A g 1 ψ = twForm (repCLM ρ g) 1 ψ)
    (hom : (om : Form (F := F) s 2) = d hs 1 ψ) : deRhamClass hs hc hne A ρ om = 0 := by
  let D : Datum (d hs 0) (d hs 1) (fun g => pullForm hs A g 1) (fun g => twForm (repCLM ρ g) 1)
      (om : Form (F := F) s 2) :=
    { η := ψ
      θ := fun _ => 0
      dη := hom.symm
      dθ := fun g => by simp [hψ g] }
  rw [deRhamClass_eq hs hc hne A ρ om D]
  have hL := laws hs hc hne A ρ
  have hcoc : cochainCocycle hL D = 0 := by
    apply Subtype.ext
    funext p
    have := c_cochain hL D p.1 p.2
    have h1 : cochain hL D p.1 p.2 = 0 := by
      apply hL.c_injective
      rw [this, map_zero]
      simp [D]
    exact h1
  unfold zigzagClass
  rw [hcoc, map_zero]

end Exact

section Lattice

open TernaryPeriodPolynomials.Argument.SeedC3.ZigZag

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {ρt : Pt → E →L[ℝ] E}
  {G : Type} [Group G]

/-- **A group acting on the Heisenberg chart by left translation through a homomorphism `nOf` into the Heisenberg group.** -/
structure LatticeAction (G : Type) [Group G] where
  nOf : G → Pt
  nOf_mul : ∀ g h, nOf (g * h) = mulH (nOf g) (nOf h)

theorem mulH_self_eq (p : Pt) (h : mulH p p = p) : p = 0 := by
  simp only [mulH] at h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg (fun q : Pt => q.2.1) h
  have h3 := congrArg (fun q : Pt => q.2.2) h
  simp at h1 h2 h3
  ext <;> simp <;> nlinarith

theorem LatticeAction.nOf_one (Λ : LatticeAction G) : Λ.nOf 1 = 0 := by
  have h := Λ.nOf_mul 1 1
  rw [one_mul] at h
  exact mulH_self_eq _ h.symm

/-- The action of `G` on the chart `Pt` by left translations. -/
def latAct (Λ : LatticeAction G) : Action G (Set.univ : Set Pt) where
  act g p := mulH (Λ.nOf g) p
  smooth g := by
    have : ContDiff ℝ ∞ (mulH (Λ.nOf g)) := by
      unfold mulH
      fun_prop
    exact this.contDiffOn
  mapsTo _ _ _ := Set.mem_univ _
  mul g h x _ := by
    show mulH (Λ.nOf (g * h)) x = mulH (Λ.nOf g) (mulH (Λ.nOf h) x)
    rw [Λ.nOf_mul, mulH_assoc]

/-- The coefficient representation of `G` through `ρt`. -/
def latRho (R : HeisRep ρt) (Λ : LatticeAction G) : Representation ℝ G E where
  toFun g := (ρt (Λ.nOf g)).toLinearMap
  map_one' := by
    ext v
    simp [Λ.nOf_one, R.one]
  map_mul' g h := by
    ext v
    simp [Λ.nOf_mul, R.mul]

theorem repCLM_latRho [FiniteDimensional ℝ E] (R : HeisRep ρt) (Λ : LatticeAction G) (g : G) :
    repCLM (latRho R Λ) g = ρt (Λ.nOf g) := by
  ext v
  rfl

end Lattice

section Equivariance

open TernaryPeriodPolynomials.Argument.SeedC3.ZigZag

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {ρt : Pt → E →L[ℝ] E} {G : Type} [Group G]

theorem Xf_fst (k : Fin 3) {p q : Pt} (h : p.1 = q.1) : Xf k p = Xf k q := by
  fin_cases k <;> simp [Xf, h]

theorem Mx_Xf' (n q : Pt) (k : Fin 3) : Mx n.1 (Xf k q) = Xf k (mulH n q) := by
  rw [Mx_Xf]
  exact Xf_fst k (by simp [mulH])

theorem fderiv_mulH (n x : Pt) : fderiv ℝ (mulH n) x = Mx n.1 := (hasFDerivAt_mulH n x).fderiv

omit [CompleteSpace E] in
/-- **Equivariance of a closed `2`-form in the frame**: `ω(X_b, X_c)(n x) = ρ(n) ω(X_b, X_c)(x)`. -/
theorem A2_equivariant (R : HeisRep ρt) (Λ : LatticeAction G)
    (om : invClosed (isOpen_univ : IsOpen (Set.univ : Set Pt)) (latAct Λ) (latRho R Λ)) (b c : Fin 3) (g : G)
    (x : Pt) :
    A2 om.1.1 b c (mulH (Λ.nOf g) x) = ρt (Λ.nOf g) (A2 om.1.1 b c x) := by
  have h := om.2.2 g
  have hx := congrArg (fun f : Form (F := E) Set.univ 2 => (f : RawForm Pt E 2) x) h
  simp only [pullForm_apply _ _ g _ (Set.mem_univ x), twForm_apply] at hx
  have hv := congrArg (fun φ : Pt [⋀^Fin 2]→L[ℝ] E => φ ![Xf b x, Xf c x]) hx
  simp only [pullRaw, coefficientFormMap_apply] at hv
  have hd : fderiv ℝ ((latAct Λ).act g) x = Mx (Λ.nOf g).1 := fderiv_mulH _ _
  rw [hd] at hv
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousLinearMap.compContinuousAlternatingMap_coe, repCLM_latRho] at hv
  have hvec : (Mx (Λ.nOf g).1 ∘ ![Xf b x, Xf c x]) =
      ![Xf b (mulH (Λ.nOf g) x), Xf c (mulH (Λ.nOf g) x)] := by
    funext i; fin_cases i <;> simp [Mx_Xf']
  rw [hvec] at hv
  exact hv

omit [CompleteSpace E] in
/-- The `1`-form `psi1` as a chart form on `Pt`. -/
def psiForm (R : HeisRep ρt) {a : Pt → Fin 3 → E} (ha : ∀ k, ContDiff ℝ ∞ (fun q => a q k)) :
    Form (F := E) (Set.univ : Set Pt) 1 :=
  ⟨psi1 ρt a, (psi1_contDiff R.smooth ha).contDiffOn, fun x hx => absurd (Set.mem_univ x) hx⟩

omit [CompleteSpace E] in
/-- **Equivariance of the `1`-form `ψ` with periodic gauge-trivialized coefficients.** -/
theorem psiForm_equivariant (R : HeisRep ρt) (Λ : LatticeAction G) {a : Pt → Fin 3 → E}
    (ha : ∀ k, ContDiff ℝ ∞ (fun q => a q k)) (hper : ∀ g x, a (mulH (Λ.nOf g) x) = a x) (g : G) :
    pullForm (isOpen_univ : IsOpen (Set.univ : Set Pt)) (latAct Λ) g 1 (psiForm R ha) =
      twForm (repCLM (latRho R Λ) g) 1 (psiForm R ha) := by
  apply Form.ext
  intro x _
  rw [pullForm_apply _ _ g _ (Set.mem_univ x), twForm_apply]
  ext v
  have hd : fderiv ℝ ((latAct Λ).act g) x = Mx (Λ.nOf g).1 := fderiv_mulH _ _
  simp only [pullRaw, hd, coefficientFormMap_apply, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousLinearMap.compContinuousAlternatingMap_coe, repCLM_latRho, Function.comp]
  show psi1 ρt a (mulH (Λ.nOf g) x) (fun i => Mx (Λ.nOf g).1 (v i)) = ρt (Λ.nOf g) (psi1 ρt a x v)
  rw [psi1_apply, psi1_apply, hper g x]
  simp only [theta_Mx]
  rw [R.mul]
  rfl

end Equivariance

section GaugePsi

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {ρt : Pt → E →L[ℝ] E}

theorem A1_psi1 (a : Pt → Fin 3 → E) (j : Fin 3) (q : Pt) :
    A1 (psi1 ρt a) j q = ρt q (a q j) := by
  unfold A1
  rw [psi1_apply]
  congr 1
  simp [theta_Xf]

theorem gauge1_psi1 (R : HeisRep ρt) (a : Pt → Fin 3 → E) (j : Fin 3) (q : Pt) :
    gauge1 ρt (psi1 ρt a) j q = a q j := by
  unfold gauge1
  rw [A1_psi1, R.cancel']

end GaugePsi

end TernaryPeriodPolynomials.Argument.EisensteinClass.Heisenberg
