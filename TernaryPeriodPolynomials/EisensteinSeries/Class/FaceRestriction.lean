module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Restrict
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.SeedPsi
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.PlaneAction
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.SeedDatum

@[expose] public section


/-!
# The boundary model `e(P)` and the restriction of the class of an equivariant form

Paper: ("`i_{R,t}`
realizes group restriction": the restriction `r_P` to the plane boundary model `e(P) = ℝ² × ℍ` is
the group restriction to `Γ_P`), and the seed on the face (Lemma C.3).

A plane parabolic group `D : PlaneData G` realized inside `Γ ⊂ SL₃(ℤ)` by `ψ : G → Γ`
(`D.plm g = realMat (ψ g)`, e.g. `Γ_P = Γ(N) ∩ P(ℤ)`) acts on the face `Face = ℝ² × ℍ` (`D.action`);
the inclusion `i : (u, τ) ↦ (u, τ, t = 1)` of the face into `Ω` is `ψ`-equivariant
(`faceEquivMap`, from `planeAct_plm_ptOf`: `planeAct [[λ, w], [0, 1]] ∘ i = i ∘ (λ, w)`). Hence, by the
naturality of the de Rham class (`deRhamClass_natural`), the class of the pullback `i^*W` of a closed
equivariant form `W` on `Ω` is the group restriction of `[W]` along `ψ` (`faceForm_class`); its
coordinates are `(i^*W)(∂ᵢ, ∂ⱼ)(u, τ) = W_{ij}(u, τ, 1)` (`faceForm_basis`), to be compared with the
seed `seedForm n h (ptOf x) i j` of Lemma C.3.

Formalized by Claude Sonnet 5.5.
-/

open TernaryPoly.SmoothLocalDeRham TernaryPoly.SmoothCoveringDeRham
open scoped ContDiff
noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.SeedC3.Psi

theorem ptOf_mem {x : Face} (hx : x ∈ faceSet) : ptOf x ∈ Omega := by
  have : 0 < x 3 := hx
  exact ⟨by simpa [ptOf] using this, by simp [ptOf]⟩

theorem parabolicMatrix_eq_mul (A : Matrix (Fin 2) (Fin 2) ℝ) (w : Fin 2 → ℝ) :
    parabolicMatrix A w = transMat (w 0) (w 1) * diagMat A 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [parabolicMatrix, transMat, diagMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem planeAct_plm_ptOf {G : Type} [Group G] (D : PlaneData G) (g : G) {x : Face}
    (hx : x ∈ faceSet) : planeAct (D.plm g) (ptOf x) = ptOf (D.act g x) := by
  have hdet : (D.lam g : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    have := D.det_one g
    simpa [Matrix.GeneralLinearGroup.det] using congrArg Units.val this
  have hp := ptOf_mem hx
  have hd1 : (diagMat (D.lam g : Matrix (Fin 2) (Fin 2) ℝ) 1).det = 1 := by
    rw [det_diagMat, hdet]; norm_num
  have hlev := planeAct_diag (D.lam g : Matrix (Fin 2) (Fin 2) ℝ) 1
    (by rw [hdet]; exact one_pos) one_pos (by rw [hdet]; norm_num) hp
  have hL : leviMap (D.lam g : Matrix (Fin 2) (Fin 2) ℝ) 1 (ptOf x) ∈ Omega := by
    rw [← hlev]; exact planeAct_mem hd1 hp
  rw [PlaneData.plm, parabolicMatrix_eq_mul, planeAct_mul hd1 hp, hlev,
    planeAct_transMat _ _ hL]
  funext i
  fin_cases i
  · simp [leviMap, ptOf, PlaneData.act]
  · simp [leviMap, ptOf, PlaneData.act]
  · simp [leviMap, ptOf, PlaneData.act, mob]
    rw [show seedTau ![x 0, x 1, x 2, x 3, 1] = faceTau x from seedTau_ptOf x]
  · simp [leviMap, ptOf, PlaneData.act, mob]
    rw [show seedTau ![x 0, x 1, x 2, x 3, 1] = faceTau x from seedTau_ptOf x]
  · simp [leviMap, ptOf, PlaneData.act]

/-- The inclusion `e(P) → 𝒳`, `(u, τ) ↦ (u, τ, t = 1)`, is the sum of a continuous linear map and a
constant. -/
def ptCLM : Face →L[ℝ] (Fin 5 → ℝ) :=
  ContinuousLinearMap.pi ![ContinuousLinearMap.proj 0, ContinuousLinearMap.proj 1,
    ContinuousLinearMap.proj 2, ContinuousLinearMap.proj 3, 0]

theorem ptOf_eq : ptOf = fun x => ptCLM x + Pi.single 4 1 := by
  funext x k
  fin_cases k <;> simp [ptOf, ptCLM]

theorem hasFDerivAt_ptOf (x : Face) : HasFDerivAt ptOf ptCLM x := by
  rw [ptOf_eq]
  exact ptCLM.hasFDerivAt.add_const _

theorem ptCLM_single (i : Fin 4) : ptCLM (Pi.single i 1) = Pi.single i.castSucc 1 := by
  funext k
  fin_cases i <;> fin_cases k <;> simp [ptCLM]

theorem contDiffOn_ptOf : ContDiffOn ℝ ∞ ptOf faceSet := by
  rw [ptOf_eq]
  exact (ptCLM.contDiff.add contDiff_const).contDiffOn

section FaceMap

variable {G : Type} [Group G] (D : PlaneData G) {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ)}
  (ψ : G →* Γ) (hψ : ∀ g, D.plm g = realMat (ψ g).1) {n : ℕ}

/-- **The boundary model of a plane parabolic group maps equivariantly into `𝒳`**: for
`D` a plane parabolic group with a homomorphism `ψ : G → Γ` realizing its matrices
(`D.plm g = realMat (ψ g)`), the map `i : e(P) → Ω`, `(u, τ) ↦ (u, τ, 1)` is equivariant along `ψ`. -/
def faceEquivMap : EquivMap isOpen_faceSet isOpen_Omega D.action (gammaAct Γ) ψ where
  φ := ptOf
  smooth := contDiffOn_ptOf
  mapsTo _ hx := ptOf_mem hx
  equiv g x hx := by
    change ptOf (D.act g x) = planeAct (realMat (ψ g).1) (ptOf x)
    rw [← hψ g, planeAct_plm_ptOf D g hx]

include hψ in
theorem rhoR_eq_gammaRho (g : G) : D.rhoR n g = gammaRho Γ n (ψ g) := by
  apply LinearMap.ext
  intro q
  apply Coef.toPoly_injective
  rw [toPoly_gammaRho]
  change Coef.toPoly (D.rhoCoef n g q) = _
  rw [D.toPoly_rhoCoef, hψ g]

/-- **The pullback of a closed equivariant form to the face** `e(P)`. -/
def faceForm (W : InvComponents Γ n) :
    ZigZag.invClosed isOpen_faceSet D.action (D.rhoR n) :=
  pullInv (faceEquivMap D ψ hψ) (rhoR_eq_gammaRho D ψ hψ) W.toInv

/-- The coordinates of the pullback to the face: `(ι^*W)(∂ᵢ, ∂ⱼ) = W_{ij}(u, τ, 1)`. -/
theorem faceForm_basis (W : InvComponents Γ n) {x : Face} (hx : x ∈ faceSet) (i j : Fin 4) :
    ((faceForm D ψ hψ W : Form (F := Coef n) faceSet 2) : RawForm Face (Coef n) 2) x
        ![Pi.single i 1, Pi.single j 1] = W.comp (ptOf x) i.castSucc j.castSucc := by
  change (pullBack isOpen_faceSet (faceEquivMap D ψ hψ).smooth (faceEquivMap D ψ hψ).mapsTo 2
    W.form : RawForm Face (Coef n) 2) x _ = _
  rw [pullBack_apply isOpen_faceSet _ _ _ hx]
  change ((W.form : RawForm (Fin 5 → ℝ) (Coef n) 2) (ptOf x)).compContinuousLinearMap
    (fderiv ℝ ptOf x) ![Pi.single i 1, Pi.single j 1] = _
  rw [(hasFDerivAt_ptOf x).fderiv, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    W.form_apply (ptOf_mem hx)]
  have : (⇑ptCLM ∘ ![Pi.single i 1, Pi.single j 1]) =
      ![Pi.single i.castSucc 1, Pi.single j.castSucc 1] := by
    funext k; fin_cases k <;> simp [ptCLM_single]
  rw [this, W.raw_basis]

/-- **The class of the pullback to the face is the restriction of the class**: the
restriction of `[W] ∈ H²(Γ, E_n)` along `ψ : G → Γ` is the de Rham class of the face form. -/
theorem faceForm_class (W : InvComponents Γ n) :
    ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty D.action (D.rhoR n)
        (faceForm D ψ hψ W) =
      (groupCohomology.map ψ (resMor ψ (D.rhoR n) (gammaRho Γ n) (rhoR_eq_gammaRho D ψ hψ)) 2).hom
        (ZigZag.deRhamClass isOpen_Omega convex_Omega Omega_nonempty (gammaAct Γ) (gammaRho Γ n)
          W.toInv) :=
  deRhamClass_natural (faceEquivMap D ψ hψ) convex_faceSet faceSet_nonempty convex_Omega
    Omega_nonempty (rhoR_eq_gammaRho D ψ hψ) W.toInv

end FaceMap

end TernaryPeriodPolynomials.Argument.EisensteinClass
