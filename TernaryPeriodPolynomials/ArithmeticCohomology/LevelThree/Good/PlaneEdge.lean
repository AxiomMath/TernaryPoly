module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Good.PlaneRestriction
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.HeckeH1

@[expose] public section


/-!
# The binary coordinate of the good-plane edge and its Levi equivariance

For a relative two-cocycle `c` of the good-plane stabilizer `Λ` (vanishing on pairs of radical
elements) and `ℓ = (m, d)` in the Levi group `Γ₁'(3) × ℤˣ`, Sol's edge cycle
`splitEdgeCycle goodPlaneSplitting (coefRep n) ℓ c` is a one-cocycle of the radical lattice `ℤ²`
with values in `Sym^n`; its binary coordinate (`upperRadicalCocycleCoordinate`) lies in `Sym^{n+1}`
(`edgeVal`). The Levi group acts on cocycles by `splitRadicalCocycleAction`, and on binary
coordinates through `κ`: `coord_levi` says
`coordinate (ℓ · ξ) = Sym^{n+1} ⊗ det⁻¹ (κ(m)) (coordinate ξ)`, the factor `ℤˣ` acting trivially.
Consequently `edgeVal c` is a one-cocycle of `Γ₁'(3) × ℤˣ` with values in `Sym^{n+1} ⊗ det⁻¹`
through `κ` (`edgeVal_mul`), trivial on `ℤˣ` (`edgeVal_unit`), and after the coefficient transport
`Φ = Sym^{n+1}(δ)` it is a crossed one-cocycle of `Γ₁'(3)` for `ParabolicBounds.levelRep (n+1) (-1)`
(`goodPlaneEdgeCocycle`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix MvPolynomial GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

namespace TernaryPeriodPolynomials.LevelThree.GoodPlaneEdge

open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.LevelThree.GoodPlaneFrame
open TernaryPeriodPolynomials.LevelThree.GoodPlaneModel
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds (levelRep)
open TernaryPeriodPolynomials.Spectral.PlaneCoordinates (bmul)
open TernaryPeriodPolynomials.Spectral.LevelOneCosets (integralEmbed)
open TernaryPeriodPolynomials.Spectral.IdentityPlaneCosets
  (icast icast_smul_int bmul_integralEmbed)

variable (n : ℕ)

/-! ### The coordinate of a radical cocycle -/

theorem jc_val (ξ : groupCohomology.cocycles₁ (upperRadicalLatticeRep n)) :
    (upperRadicalCocycleCoordinate n ξ).val = (n + 1 : ℂ)⁻¹ •
      (X 0 * (IdentityPlaneCoordinate.genRes n ξ 0).val +
        X 1 * (IdentityPlaneCoordinate.genRes n ξ 1).val) := by
  rw [upperRadicalCocycleCoordinate_value]
  rfl

theorem gen_toAdd (k : Fin 2) :
    (radicalLatticeGenerator k).toAdd = if k = 0 then (1, 0) else (0, 1) := by
  unfold radicalLatticeGenerator radicalLatticeFirst radicalLatticeSecond
  split_ifs <;> rfl

theorem splitRadicalInput_apply (m : binaryArithmeticLevel) (d : ℤˣ) (b : RadicalLattice) :
    splitRadicalInput goodPlaneSplitting (m, d) b = Multiplicative.ofAdd (act m⁻¹ d b.toAdd) := by
  have hd : d⁻¹ = d := inv_eq_of_mul_eq_one_right (Int.units_mul_self d)
  have h := conjAct_apply (m, d)⁻¹ b
  change goodPlaneSplitting.conjAct (m, d)⁻¹ b = _
  rw [h]
  simp only [Prod.fst_inv, Prod.snd_inv, hd]

theorem icast_act (m : binaryArithmeticLevel) (d : ℤˣ) (b : ℤ × ℤ) :
    icast (act m d b) = ((d : ℤ) : ℚ) • bmul (integralEmbed (kap m)).val (icast b) := by
  rw [act, ← icast_smul_int, bmul_integralEmbed]

/-- **Generator values of the Levi translate of a radical cocycle.** -/
theorem genRes_levi (ξ : groupCohomology.cocycles₁ (upperRadicalLatticeRep n))
    (m : binaryArithmeticLevel) (d : ℤˣ) (k : Fin 2) :
    IdentityPlaneCoordinate.genRes n
        (splitRadicalCocycleAction goodPlaneSplitting (coefRep n) (m, d) ξ) k =
      IdentityPlaneCoordinate.Abin n (integralEmbed (kap m))
        (((((integralEmbed (kap m))⁻¹ : GL (Fin 2) ℚ).val 0 k : ℚ) : ℂ) •
            IdentityPlaneCoordinate.genRes n ξ 0 +
          ((((integralEmbed (kap m))⁻¹ : GL (Fin 2) ℚ).val 1 k : ℚ) : ℂ) •
            IdentityPlaneCoordinate.genRes n ξ 1) := by
  have hd : (((d : ℤ) : ℚ) : ℂ) ≠ 0 := by exact_mod_cast d.ne_zero
  have h1 : IdentityPlaneCoordinate.genRes n
      (splitRadicalCocycleAction goodPlaneSplitting (coefRep n) (m, d) ξ) k =
      IdentityPlaneCoordinate.res n (IdentityPlaneCoordinate.ρn n (Pg 0 m d)
        (ξ (Multiplicative.ofAdd (act m⁻¹ d (radicalLatticeGenerator k).toAdd)))) := by
    rw [← splitRadicalInput_apply]
    rfl
  have h2 := IdentityPlaneCoordinate.restrict_P n (icast 0) (integralEmbed (kap m)) (uq d)
    (ξ (Multiplicative.ofAdd (act m⁻¹ d (radicalLatticeGenerator k).toAdd)))
  rw [h1]
  refine h2.trans ?_
  rw [IdentityPlaneCoordinate.res_cocycle, icast_act, IdentityPlaneCoordinate.Lam_smul]
  simp only [map_inv]
  rw [gen_toAdd, IdentityPlaneCoordinate.Lam_bmul_e, map_smul, smul_smul]
  have hu : ((uq d : ℚˣ) : ℚ) = ((d : ℤ) : ℚ) := rfl
  rw [hu, inv_mul_cancel₀ hd, one_smul]

/-- **Levi equivariance of the binary coordinate.** The group `ℤˣ` acts trivially and `Γ₁'(3)`
through `κ`. -/
theorem coord_levi (ξ : groupCohomology.cocycles₁ (upperRadicalLatticeRep n))
    (m : binaryArithmeticLevel) (d : ℤˣ) :
    upperRadicalCocycleCoordinate n
        (splitRadicalCocycleAction goodPlaneSplitting (coefRep n) (m, d) ξ) =
      Binary.homogeneousAction (n + 1) (-1) (binaryIntegralComplex (kap m))
        (upperRadicalCocycleCoordinate n ξ) := by
  apply Subtype.ext
  rw [jc_val n (splitRadicalCocycleAction goodPlaneSplitting (coefRep n) (m, d) ξ),
    Binary.homogeneousAction_coe, jc_val n ξ, genRes_levi n ξ m d 0, genRes_levi n ξ m d 1]
  have key := IdentityPlaneCoordinate.action_coord n (integralEmbed (kap m))
    (IdentityPlaneCoordinate.genRes n ξ)
  have hcx : IdentityPlaneCoordinate.cx2 (integralEmbed (kap m)) = binaryIntegralComplex (kap m) :=
    LevelThreeHeckeH1.map_integralEmbed (kap m)
  rw [hcx] at key
  exact key

end TernaryPeriodPolynomials.LevelThree.GoodPlaneEdge
