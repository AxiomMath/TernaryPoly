module

public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Line.ReflForm
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.FStar

@[expose] public section


/-!
# The `ε`-isotypic line seed `½(σ_f + ε (-1)ⁿ \overline{σ_{f^*}})` (LS10, part 3)

Line mirror of `SeedC3S4c.ReflectionDescent` (`reflSeedInv`, `pullForm_refl_reflSeed`, `deRhamClass_reflSeedInv`).

**The exact sign.**  For the line reflection `r = diag(1; -1, 1)` (`reflFCLM` on the face, `ρ(r) = lreflCoef` on `E_n`),
`r^* σ_h = c ρ(r) \overline{σ_{h^*}}` and `r^* \overline{σ_{h^*}} = c ρ(r) σ_h` with
**`c = (-1)ⁿ`** (`pullForm_lrefl_seed`, `pullForm_lrefl_conjSeed`); the plane has `(-1)^{n+1}`.  Hence on
`σ_f + ε c \overline{σ_{f^*}}` (`ε = ±1`) the reflection acts by `ε ρ(r)` (`pullForm_lrefl_reflSeed`), and the class is
`deRhamClass_reflSeedInv : [reflSeedInv f ε] = [σ_f] + ε (-1)ⁿ [\overline{σ_{f^*}}]`.  We omit the factor `½`: the combination
`reflSeedInv f ε` is `σ_f + (ε (-1)ⁿ) \overline{σ_{f^*}}`, i.e. `2 P_ε σ_f` for the projection `P_ε = ½(1 + ε r^*ρ(r)⁻¹)`.

Formalized by Claude Sonnet 5.5.
-/

open UpperHalfPlane ModularForm ComplexConjugate
open TernaryPoly.SmoothLocalDeRham CategoryTheory
open TernaryPeriodPolynomials.SphericalDetection.Helpers

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LineSeed

open TernaryPeriodPolynomials.Argument.SeedC3 TernaryPeriodPolynomials.Argument.SeedC3.Psi
open TernaryPeriodPolynomials.Argument.SeedC3S4c (fStar fStar_cuspH Lvl1)

section

variable {G : Type} [Group G] (D : LineData G) (hΛ : ∀ g, (D.lam g : GL (Fin 2) ℝ) ∈ Lvl1)
  {n : ℕ} (f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ))

/-- The `ε`-twisted combination `σ_f + ε (-1)ⁿ \overline{σ_{f^*}}` of the line seed of `f` and the antiholomorphic line seed
of `f^*`, a closed `ρ`-equivariant two-form for the line group. -/
def reflSeedInv (ε : ℝ) : ZigZag.invClosed isOpen_faceSet D.action (D.rhoR n) :=
  cuspSeedInv D hΛ (f := f) + (ε * (-1 : ℝ) ^ n) • cuspSeedConjInv D hΛ (f := fStar f)

/-- The line reflection acts on `σ_f + ε (-1)ⁿ \overline{σ_{f^*}}` by `ε ρ(r)` (`ε = ±1`). -/
theorem pullForm_lrefl_reflSeed {ε : ℝ} (hε : ε * ε = 1) :
    ZigZag.pullForm isOpen_faceSet reflAction reflGen 2
        ((reflSeedInv D hΛ f ε : ZigZag.invClosed isOpen_faceSet D.action (D.rhoR n)) :
          Form (F := Coef n) faceSet 2) =
      ε • ZigZag.twForm (lreflCoefCLM n) 2
        ((reflSeedInv D hΛ f ε : ZigZag.invClosed isOpen_faceSet D.action (D.rhoR n)) :
          Form (F := Coef n) faceSet 2) := by
  have hrel : ∀ z : ℂ, 0 < z.im → cuspH Lvl1 n (fStar f) z = conj (cuspH Lvl1 n f (-conj z)) :=
    fun z hz => fStar_cuspH f hz
  have h1 := pullForm_lrefl_seed n (cuspH Lvl1 n f) (cuspH Lvl1 n (fStar f))
    (cuspH_holo Lvl1 n f) (cuspH_holo Lvl1 n (fStar f)) hrel
  have h2 := pullForm_lrefl_conjSeed n (cuspH Lvl1 n f) (cuspH Lvl1 n (fStar f))
    (cuspH_holo Lvl1 n f) (cuspH_holo Lvl1 n (fStar f)) hrel
  have hcc : ((-1 : ℝ) ^ n) * ((-1 : ℝ) ^ n) = 1 := by
    rw [← mul_pow]; norm_num
  have hR : ((reflSeedInv D hΛ f ε : ZigZag.invClosed isOpen_faceSet D.action (D.rhoR n)) :
      Form (F := Coef n) faceSet 2) =
      d isOpen_faceSet 1 (lineEtaForm (cuspH Lvl1 n f) n (cuspH_holo Lvl1 n f)) +
        (ε * (-1 : ℝ) ^ n) • ZigZag.twForm (conjCLM n) 2
          (d isOpen_faceSet 1 (lineEtaForm (cuspH Lvl1 n (fStar f)) n
            (cuspH_holo Lvl1 n (fStar f)))) := rfl
  rw [hR, map_add, map_smul, h1, h2, ZigZag.twForm_mul]
  simp only [map_add, map_smul, smul_add, smul_smul]
  have e1 : ε * (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = ε := by rw [mul_assoc, hcc, mul_one]
  have e2 : ε * (ε * (-1 : ℝ) ^ n) = (-1 : ℝ) ^ n := by
    rw [← mul_assoc, hε, one_mul]
  rw [e1, e2, add_comm]

/-- The de Rham class of the `ε`-combination is the corresponding combination of the classes. -/
theorem deRhamClass_reflSeedInv (ε : ℝ) :
    ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty D.action (D.rhoR n)
        (reflSeedInv D hΛ f ε) =
      cuspSeedClass D hΛ (f := f) +
        (ε * (-1 : ℝ) ^ n) • cuspSeedConjClass D hΛ (f := fStar f) := by
  rw [reflSeedInv, map_add, map_smul, deRhamClass_cuspSeed, deRhamClass_cuspSeedConj]

end

end TernaryPeriodPolynomials.Argument.LineSeed
