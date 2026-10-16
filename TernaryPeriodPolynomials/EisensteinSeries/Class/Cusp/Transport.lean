module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.CoefTwist
public import TernaryPeriodPolynomials.EisensteinSeries.Class.RestAverage
public import TernaryPeriodPolynomials.EisensteinSeries.Class.AveragePreserves
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Cusp.Face

@[expose] public section


/-!
# Transport of the averaging argument to the plane group of the cusp `h⁻¹ P h`

Paper: "the same letters
for the rational conjugates".

The plane group `Γ_{h⁻¹Ph}` acts on `e(P)` through the conjugation `conjP N h : Γ_{h⁻¹Ph} ≃* Γ_P`
(`cuspFaceAction`), with the coefficient representation `rhoAt N h n = ρ|_{Γ_{h⁻¹Ph}}`, which is NOT of the
form `(D.action, D.rhoR n)` of a `PlaneData` for `Γ_{h⁻¹Ph}`. We pull the plane data back along `conjP`
(`planeDataComap`, with `latticeData_comap`) and compare coefficients by the intertwiner `ρ(h⁻¹)`
(`intertwines_rhoAt`; `CoefTwist.deRhamClass_twist`). `deRhamClass_comapInv_eq_zero`: a closed form
invariant under `Γ_P` whose torus average vanishes has zero class as a form invariant under the pulled-back
group (this is `deRhamClass_avInv`, with the average unchanged).

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory groupCohomology
open TernaryPoly.SmoothLocalDeRham TernaryPoly.SmoothCoveringDeRham
open scoped ContDiff MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument.SeedC3.Psi TernaryPeriodPolynomials.Argument.SeedC3S4c

/-- The plane parabolic group data pulled back along a homomorphism. -/
def planeDataComap {G G' : Type} [Group G] [Group G'] (D : PlaneData G) (β : G' →* G) :
    PlaneData G' where
  lam := D.lam.comp β
  w g := D.w (β g)
  det_one g := D.det_one (β g)
  w_mul g k := by
    simp only [map_mul]
    exact D.w_mul _ _

theorem planeDataComap_action {G G' : Type} [Group G] [Group G'] (D : PlaneData G) (β : G' →* G) :
    (planeDataComap D β).action = actionComap D.action β := rfl

theorem planeDataComap_plm {G G' : Type} [Group G] [Group G'] (D : PlaneData G) (β : G' →* G)
    (g : G') : (planeDataComap D β).plm g = D.plm (β g) := rfl

theorem toPoly_rhoR {G : Type} [Group G] (D : PlaneData G) (n : ℕ) (g : G) (v : Coef n) :
    Coef.toPoly (D.rhoR n g v) = rho (D.plm g) (Coef.toPoly v) :=
  D.toPoly_rhoCoef n g v

theorem planeDataComap_rhoR {G G' : Type} [Group G] [Group G'] (D : PlaneData G) (β : G' →* G)
    (n : ℕ) : (planeDataComap D β).rhoR n = (D.rhoR n).comp β := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro v
  apply Coef.toPoly_injective
  show Coef.toPoly ((planeDataComap D β).rhoCoef n g v) = Coef.toPoly (D.rhoCoef n (β g) v)
  rw [PlaneData.toPoly_rhoCoef, PlaneData.toPoly_rhoCoef]
  rfl

theorem latticeData_comap {G G' : Type} [Group G] [Group G'] {D : PlaneData G} {c : ℝ}
    (hL : LatticeData D c) (β : G' →* G) (hβ : Function.Surjective β) :
    LatticeData (planeDataComap D β) c := by
  refine ⟨fun g => ?_, fun k => ?_⟩
  · obtain ⟨A, hA⟩ := hL.levi (β g)
    exact ⟨A, by simpa [planeDataComap] using hA⟩
  · obtain ⟨ν, hν1, hν2⟩ := hL.lattice k
    obtain ⟨ν', rfl⟩ := hβ ν
    exact ⟨ν', hν1, hν2⟩

section Comap

variable {G G' : Type} [Group G] [Group G'] (D : PlaneData G) (β : G' →* G) (n : ℕ)

/-- An invariant closed form of `D` is an invariant closed form of the pulled-back data. -/
def comapInv (F : ZigZag.invClosed isOpen_faceSet D.action (D.rhoR n)) :
    ZigZag.invClosed isOpen_faceSet (planeDataComap D β).action ((planeDataComap D β).rhoR n) :=
  ⟨F.1, F.2.1, fun g => by
    have h := F.2.2 (β g)
    rw [planeDataComap_rhoR]
    exact h⟩

theorem comapInv_coe (F : ZigZag.invClosed isOpen_faceSet D.action (D.rhoR n)) :
    ((comapInv D β n F : ZigZag.invClosed isOpen_faceSet (planeDataComap D β).action
      ((planeDataComap D β).rhoR n)) : Form (F := Coef n) faceSet 2) = F.1 := rfl

theorem deRhamClass_comapInv_eq_zero {c : ℝ} (hL : LatticeData D c) (hc : c ≠ 0)
    (hβ : Function.Surjective β)
    (F : ZigZag.invClosed isOpen_faceSet D.action (D.rhoR n)) (hF : avInv n hL F = 0) :
    ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty (planeDataComap D β).action
      ((planeDataComap D β).rhoR n) (comapInv D β n F) = 0 := by
  have hL' := latticeData_comap hL β hβ
  have h1 := deRhamClass_avInv (D := planeDataComap D β) (n := n) hL' hc (comapInv D β n F)
  have h2 : avInv n hL' (comapInv D β n F) = 0 := by
    apply Subtype.ext
    rw [avInv_val]
    have := congrArg (fun G : ZigZag.invClosed isOpen_faceSet D.action (D.rhoR n) =>
      (G : Form (F := Coef n) faceSet 2)) hF
    rw [avInv_val] at this
    exact this
  rw [h2, map_zero] at h1
  exact h1.symm

end Comap

section Twist

variable (N : ℕ) [NeZero N] (n : ℕ)

/-- The coefficient action `ρ(g)` of any `g ∈ SL₃(ℤ)` as a continuous linear map of `E_n`. -/
def rhoOfSL (g : SL(3, ℤ)) : Coef n →L[ℝ] Coef n :=
  ZigZag.repCLM (gammaRho (⊤ : Subgroup SL(3, ℤ)) n) ⟨g, Subgroup.mem_top g⟩

theorem toPoly_rhoOfSL (g : SL(3, ℤ)) (q : Coef n) :
    Coef.toPoly (rhoOfSL n g q) = rho (realMat g) (Coef.toPoly q) :=
  toPoly_gammaRho (⊤ : Subgroup SL(3, ℤ)) n ⟨g, Subgroup.mem_top g⟩ q

theorem rhoOfSL_mul (g k : SL(3, ℤ)) (q : Coef n) :
    rhoOfSL n (g * k) q = rhoOfSL n g (rhoOfSL n k q) := by
  apply Coef.toPoly_injective
  rw [toPoly_rhoOfSL, toPoly_rhoOfSL, toPoly_rhoOfSL, realMat_mul, rho_mul]

omit [NeZero N] in
/-- **`ρ(h⁻¹)` intertwines** the coefficient representation of `Γ_P` transported along the
conjugation `conjP N h` with the restricted representation `rhoAt N h n` of `Γ_{h⁻¹Ph}`. -/
theorem intertwines_rhoAt (h : SL(3, ℤ)) :
    Intertwines (rhoOfSL n h⁻¹) ((planeDataComap (gammaNPlaneData N) (conjP N h).toMonoidHom).rhoR n)
      (rhoAt N h n) := by
  intro p v
  apply Coef.toPoly_injective
  have e1 : Coef.toPoly ((rhoAt N h n p) (rhoOfSL n h⁻¹ v)) =
      rho (realMat p.1) (rho (realMat h⁻¹) (Coef.toPoly v)) := by
    change Coef.toPoly (gammaRho (gammaN N) n (inclAt N h p) (rhoOfSL n h⁻¹ v)) = _
    rw [toPoly_gammaRho, toPoly_rhoOfSL]
    rfl
  have e2 : Coef.toPoly (rhoOfSL n h⁻¹
      (((planeDataComap (gammaNPlaneData N) (conjP N h).toMonoidHom).rhoR n) p v)) =
      rho (realMat h⁻¹) (rho (realMat (h * p.1 * h⁻¹)) (Coef.toPoly v)) := by
    rw [toPoly_rhoOfSL, toPoly_rhoR, planeDataComap_plm, gammaNPlaneData_plm]
    rfl
  rw [e1, e2, rho_mul, rho_mul, ← realMat_mul, ← realMat_mul]
  congr 2
  group

end Twist

end TernaryPeriodPolynomials.Argument.EisensteinClass
