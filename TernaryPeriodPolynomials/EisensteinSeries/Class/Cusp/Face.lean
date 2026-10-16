module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.ConstantTerm
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.PlaneCusps

@[expose] public section


/-!
# Restriction of an equivariant form to the face of an arbitrary plane cusp

Paper: ("the same
letters for the rational conjugates" of the plane `P`), 3753.

For `h ∈ SL₃(ℤ)` the plane cusp `h⁻¹ P h` has the stabilizer `Γ_{h⁻¹Ph} = gammaNPAt N h` in `SL₃(ℤ)`
(`h p h⁻¹ ∈ Γ(N) ∩ P(ℤ)`), contained in `Γ(N)`. It acts on the boundary model `e(P) = ℝ² × ℍ` through
the conjugation `conjP N h` to `Γ_P` (`cuspFaceAction`), and the map
`i_h = planeAct(h⁻¹) ∘ (u, τ ↦ (u, τ, 1)) : e(P) → Ω` is equivariant along `Γ_{h⁻¹Ph} ↪ Γ(N)`
(`cuspFaceMap`; `planeAct_plm_ptOf` and the group law). By the naturality of the de Rham class the
class of the pullback `i_h^* W` of any closed equivariant form `W` of `Γ(N)` is the group restriction
of `[W]` to `Γ_{h⁻¹Ph}` (`cuspFaceForm_class`), with the coefficient representation
`ρ|_{Γ_{h⁻¹Ph}}` (the representation `faceRep N h n` of `GammaNSeed`).

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory groupCohomology
open TernaryPoly.SmoothLocalDeRham TernaryPoly.SmoothCoveringDeRham
open scoped ContDiff MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument.SeedC3.Psi TernaryPeriodPolynomials.Argument.SeedC3S4c

/-- Pull back a smooth action along a group homomorphism. -/
def actionComap {G G' : Type} [Group G] [Group G'] {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {s : Set E} (A : ZigZag.Action G s) (β : G' →* G) : ZigZag.Action G' s where
  act g := A.act (β g)
  smooth g := A.smooth (β g)
  mapsTo g := A.mapsTo (β g)
  mul g k x hx := by
    rw [map_mul]
    exact A.mul _ _ x hx

variable (N : ℕ) [NeZero N] (h : SL(3, ℤ))

omit [NeZero N] in
/-- The plane stabilizer of the cusp `h⁻¹ P h` lies in `Γ(N)` (normality of `Γ(N)`). -/
theorem gammaNPAt_le : gammaNPAt N h ≤ gammaN N := by
  intro p hp
  have h1 : h * p * h⁻¹ ∈ gammaN N := hp.1
  have := (gammaN_normal N).conj_mem _ h1 h⁻¹
  simpa [mul_assoc] using this

/-- The inclusion `Γ_{h⁻¹Ph} ↪ Γ(N)`. -/
abbrev inclAt : gammaNPAt N h →* gammaN N := Subgroup.inclusion (gammaNPAt_le N h)

/-- The action of `Γ_{h⁻¹Ph}` on the boundary model `e(P)` through `conjP N h : Γ_{h⁻¹Ph} ≃ Γ_P`. -/
def cuspFaceAction : ZigZag.Action (gammaNPAt N h) faceSet :=
  actionComap (gammaNPlaneData N).action (conjP N h).toMonoidHom

/-- The inclusion of the boundary model at the cusp `h⁻¹ P h`:
`i_h(u, τ) = h⁻¹ · (u, τ, 1)`. -/
def cuspPt (x : Face) : Fin 5 → ℝ := planeAct (realMat h⁻¹) (ptOf x)

theorem contDiffOn_cuspPt : ContDiffOn ℝ ∞ (cuspPt h) faceSet :=
  (contDiffOn_planeAct _ (det_realMat h⁻¹)).comp contDiffOn_ptOf fun _ hx => ptOf_mem hx

/-- **The boundary model of the cusp `h⁻¹ P h` maps equivariantly into `𝒳`** along
`Γ_{h⁻¹Ph} ↪ Γ(N)`. -/
def cuspFaceMap : EquivMap isOpen_faceSet isOpen_Omega (cuspFaceAction N h)
    (gammaAct (gammaN N)) (inclAt N h) where
  φ := cuspPt h
  smooth := contDiffOn_cuspPt h
  mapsTo _ hx := planeAct_mem (det_realMat h⁻¹) (ptOf_mem hx)
  equiv p x hx := by
    have hy : ptOf x ∈ Omega := ptOf_mem hx
    have hq : (realMat (conjP N h p).1).det = 1 := det_realMat _
    have e1 : ptOf ((gammaNPlaneData N).act (conjP N h p) x) =
        planeAct (realMat (conjP N h p).1) (ptOf x) := by
      rw [← planeAct_plm_ptOf (gammaNPlaneData N) (conjP N h p) hx, gammaNPlaneData_plm]
    change planeAct (realMat h⁻¹) (ptOf ((gammaNPlaneData N).act (conjP N h p) x)) =
      planeAct (realMat p.1) (planeAct (realMat h⁻¹) (ptOf x))
    rw [e1, ← planeAct_mul hq hy, ← planeAct_mul (det_realMat h⁻¹) hy, ← realMat_mul,
      ← realMat_mul]
    congr 2
    change h⁻¹ * (h * p.1 * h⁻¹) = p.1 * h⁻¹
    group

variable {n : ℕ}

/-- The coefficient representation `E_n` restricted to `Γ_{h⁻¹Ph}` (cf. `faceRep N h n`). -/
def rhoAt (n : ℕ) : Representation ℝ (gammaNPAt N h) (Coef n) :=
  (gammaRho (gammaN N) n).comp (inclAt N h)

/-- **The pullback of a closed `Γ(N)`-equivariant form to the face of the cusp `h⁻¹ P h`.** -/
def cuspFaceForm (W : InvComponents (gammaN N) n) :
    ZigZag.invClosed isOpen_faceSet (cuspFaceAction N h) (rhoAt N h n) :=
  pullInv (cuspFaceMap N h) (fun _ => rfl) W.toInv

omit [NeZero N] in
/-- **The class of the pullback to the face of any plane cusp is the group restriction of the
class**. -/
theorem cuspFaceForm_class (W : InvComponents (gammaN N) n) :
    ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty (cuspFaceAction N h)
        (rhoAt N h n) (cuspFaceForm N h W) =
      (groupCohomology.map (inclAt N h)
          (resMor (inclAt N h) (rhoAt N h n) (gammaRho (gammaN N) n) (fun _ => rfl)) 2).hom
        (ZigZag.deRhamClass isOpen_Omega convex_Omega Omega_nonempty (gammaAct (gammaN N))
          (gammaRho (gammaN N) n) W.toInv) :=
  deRhamClass_natural (cuspFaceMap N h) convex_faceSet faceSet_nonempty convex_Omega
    Omega_nonempty (fun _ => rfl) W.toInv

omit [NeZero N] in
/-- Coordinates of the pullback to the face of the cusp `h⁻¹ P h`: the chain-rule expansion
`(i_h^*W)(∂ᵢ, ∂ⱼ)(x) = ∑ₐ∑_b ∂ᵢ(i_h)ₐ ∂ⱼ(i_h)_b W_{ab}(i_h x)`. -/
theorem toPoly_cuspFaceForm_basis (W : InvComponents (gammaN N) n) {x : Face} (hx : x ∈ faceSet)
    (i j : Fin 4) :
    Coef.toPoly (((cuspFaceForm N h W : Form (F := Coef n) faceSet 2) :
        RawForm Face (Coef n) 2) x ![Pi.single i 1, Pi.single j 1]) =
      ∑ a : Fin 5, ∑ b : Fin 5,
        MvPolynomial.C (((fderiv ℝ (cuspPt h) x (Pi.single i 1) a *
          fderiv ℝ (cuspPt h) x (Pi.single j 1) b : ℝ)) : ℂ) *
          Coef.toPoly (W.comp (cuspPt h x) a b) := by
  have hΩ : cuspPt h x ∈ Omega := planeAct_mem (det_realMat h⁻¹) (ptOf_mem hx)
  change Coef.toPoly ((pullBack isOpen_faceSet (cuspFaceMap N h).smooth (cuspFaceMap N h).mapsTo 2
    W.form : RawForm Face (Coef n) 2) x _) = _
  rw [pullBack_apply isOpen_faceSet _ _ _ hx]
  change Coef.toPoly (((W.form : RawForm (Fin 5 → ℝ) (Coef n) 2) (cuspPt h x)).compContinuousLinearMap
    (fderiv ℝ (cuspPt h) x) ![Pi.single i 1, Pi.single j 1]) = _
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply, W.form_apply hΩ]
  have : (⇑(fderiv ℝ (cuspPt h) x) ∘ ![Pi.single i 1, Pi.single j 1]) =
      ![fderiv ℝ (cuspPt h) x (Pi.single i 1), fderiv ℝ (cuspPt h) x (Pi.single j 1)] := by
    funext k; fin_cases k <;> rfl
  rw [this, InvComponents.raw, altCLM_apply, altRaw_apply_of_antisymm _ (W.anti _),
    toPoly_finsetSum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [toPoly_finsetSum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Complex.coe_smul, Coef.toPoly_smul]
  simp

end TernaryPeriodPolynomials.Argument.EisensteinClass
