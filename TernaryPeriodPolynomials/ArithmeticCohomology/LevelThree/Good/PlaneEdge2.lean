module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Good.PlaneEdge

@[expose] public section


/-!
# The edge cocycle of a relative two-cocycle of the good-plane stabilizer

`edgeVal n c ℓ` is the binary coordinate of Sol's edge cycle of the relative two-cocycle `c` at the
Levi element `ℓ = (m, d)`. By the Levi equivariance `GoodPlaneEdge.coord_levi` it is a one-cocycle
of `Γ₁'(3) × ℤˣ` with values in `Sym^{n+1} ⊗ det⁻¹` (through `κ`), vanishing on `ℤˣ`
(`edgeVal_unit`). After the coefficient transport `Φ = Sym^{n+1}(δ)` (`levelRep_Phi`:
`levelRep m ∘ Φ = Φ ∘ Mk m`) its restriction to `Γ₁'(3)` is a crossed one-cocycle of
`levelRep (n+1) (-1)`: `goodPlaneEdgeCocycle c : crossedCocycles (levelRep (n + 1) (-1))`, linear
in `c` (`goodPlaneEdgeCocycleLin`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix MvPolynomial GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

namespace TernaryPeriodPolynomials.LevelThree.GoodPlaneEdge2

open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.LevelOneCosets (integralEmbed)
open TernaryPeriodPolynomials.LevelThree.GoodPlaneFrame
open TernaryPeriodPolynomials.LevelThree.GoodPlaneModel
open TernaryPeriodPolynomials.LevelThree.GoodPlaneEdge
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds (levelRep)

variable (n : ℕ)

/-- `Sym^{n+1} ⊗ det⁻¹` evaluated at `κ(m)`. -/
def Mk (m : binaryArithmeticLevel) : Module.End ℂ (Binary.HomogeneousPoly (n + 1)) :=
  Binary.homogeneousAction (n + 1) (-1) (binaryIntegralComplex (kap m))

/-- The coordinate transport `Sym^{n+1} ⊗ det⁻¹` of `δ = diag(1, 3)`. -/
def Phi : Module.End ℂ (Binary.HomogeneousPoly (n + 1)) :=
  Binary.homogeneousAction (n + 1) (-1) (GeneralLinearGroup.map (algebraMap ℚ ℂ) del)

theorem Mk_one : Mk n 1 = 1 := by
  simp [Mk]

theorem Mk_mul (m m' : binaryArithmeticLevel) : Mk n (m * m') = Mk n m * Mk n m' := by
  simp [Mk]

theorem gl_relation (m : binaryArithmeticLevel) :
    binaryIntegralComplex m.val * GeneralLinearGroup.map (algebraMap ℚ ℂ) del =
      GeneralLinearGroup.map (algebraMap ℚ ℂ) del * binaryIntegralComplex (kap m) := by
  have h : GeneralLinearGroup.map (algebraMap ℚ ℂ) (integralEmbed (kap m)) =
      GeneralLinearGroup.map (algebraMap ℚ ℂ) (del⁻¹ * integralEmbed m.val * del) := by
    rw [integralEmbed_kap m]
  rw [map_mul, map_mul, map_inv, LevelThreeHeckeH1.map_integralEmbed,
    LevelThreeHeckeH1.map_integralEmbed] at h
  rw [h]
  group

/-- **`levelRep ∘ Φ = Φ ∘ Mk`**: the transport by `δ` converts `κ`-twisted coefficients into
`levelRep`. -/
theorem levelRep_Phi (m : binaryArithmeticLevel) (w : Binary.HomogeneousPoly (n + 1)) :
    levelRep (n + 1) (-1) m (Phi n w) = Phi n (Mk n m w) := by
  change Binary.homogeneousAction (n + 1) (-1) (binaryIntegralComplex m.val)
      (Binary.homogeneousAction (n + 1) (-1) (GeneralLinearGroup.map (algebraMap ℚ ℂ) del) w) =
    Binary.homogeneousAction (n + 1) (-1) (GeneralLinearGroup.map (algebraMap ℚ ℂ) del)
      (Binary.homogeneousAction (n + 1) (-1) (binaryIntegralComplex (kap m)) w)
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, gl_relation]

/-- The inverse coordinate transport. -/
def PhiInv : Module.End ℂ (Binary.HomogeneousPoly (n + 1)) :=
  Binary.homogeneousAction (n + 1) (-1) (GeneralLinearGroup.map (algebraMap ℚ ℂ) del⁻¹)

theorem Phi_PhiInv (x : Binary.HomogeneousPoly (n + 1)) : Phi n (PhiInv n x) = x := by
  change Binary.homogeneousAction (n + 1) (-1) (GeneralLinearGroup.map (algebraMap ℚ ℂ) del)
    (Binary.homogeneousAction (n + 1) (-1) (GeneralLinearGroup.map (algebraMap ℚ ℂ) del⁻¹) x) = x
  rw [← Module.End.mul_apply, ← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one,
    Module.End.one_apply]

theorem PhiInv_Phi (x : Binary.HomogeneousPoly (n + 1)) : PhiInv n (Phi n x) = x := by
  change Binary.homogeneousAction (n + 1) (-1) (GeneralLinearGroup.map (algebraMap ℚ ℂ) del⁻¹)
    (Binary.homogeneousAction (n + 1) (-1) (GeneralLinearGroup.map (algebraMap ℚ ℂ) del) x) = x
  rw [← Module.End.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one,
    Module.End.one_apply]

theorem Phi_injective : Function.Injective (Phi n) := by
  intro w w' h
  exact (PhiInv_Phi n w).symm.trans ((congrArg (fun x => PhiInv n x) h).trans (PhiInv_Phi n w'))

/-! ### The edge values -/

/-- The edge value, linear in the relative cocycle. -/
def edgeValLin (ℓ : Levi) :
    relativeTwoCocycles goodPlaneExtension.inl (coefRep n) →ₗ[ℂ] Binary.HomogeneousPoly (n + 1) :=
  (upperRadicalCocycleCoordinate n).comp (splitEdgeCycle goodPlaneSplitting (coefRep n) ℓ)

variable {n}

/-- The binary coordinate of the edge cycle of `c` at `ℓ`. -/
abbrev edgeVal (c : relativeTwoCocycles goodPlaneExtension.inl (coefRep n)) (ℓ : Levi) :
    Binary.HomogeneousPoly (n + 1) :=
  edgeValLin n ℓ c

theorem coord_boundary (v : Rep.res goodPlaneExtension.inl (coefRep n)) :
    upperRadicalCocycleCoordinate n
        (oneBoundaryCycle (Rep.res goodPlaneExtension.inl (coefRep n)) v) = 0 :=
  (upperRadicalCocycleCoordinate_zero_iff (degree := n) _).mpr (oneBoundaryCycle_H1_zero _ _)

/-- Additivity of the coordinate on the cocycles of the restricted representation (stated at the
type produced by `splitEdgeCycle_mul`, so that `rw` finds it). -/
theorem coord_add (a b : groupCohomology.cocycles₁ (Rep.res goodPlaneExtension.inl (coefRep n))) :
    upperRadicalCocycleCoordinate n (a + b) =
      upperRadicalCocycleCoordinate n a + upperRadicalCocycleCoordinate n b :=
  map_add (upperRadicalCocycleCoordinate n) a b

theorem edgeVal_mul (c : relativeTwoCocycles goodPlaneExtension.inl (coefRep n))
    (m : binaryArithmeticLevel) (d : ℤˣ) (ℓ' : Levi) :
    edgeVal c ((m, d) * ℓ') = Mk n m (edgeVal c ℓ') + edgeVal c (m, d) := by
  have h1 := coord_levi n (splitEdgeCycle goodPlaneSplitting (coefRep n) ℓ' c) m d
  change upperRadicalCocycleCoordinate n
      (splitEdgeCycle goodPlaneSplitting (coefRep n) ((m, d) * ℓ') c) =
    Binary.homogeneousAction (n + 1) (-1) (binaryIntegralComplex (kap m))
        (upperRadicalCocycleCoordinate n (splitEdgeCycle goodPlaneSplitting (coefRep n) ℓ' c)) +
      upperRadicalCocycleCoordinate n (splitEdgeCycle goodPlaneSplitting (coefRep n) (m, d) c)
  rw [splitEdgeCycle_mul, coord_add, coord_add, h1, coord_boundary, add_zero]

theorem edgeVal_one (c : relativeTwoCocycles goodPlaneExtension.inl (coefRep n)) :
    edgeVal c 1 = 0 := by
  have h := edgeVal_mul c 1 1 1
  rw [mul_one, show ((1 : binaryArithmeticLevel), (1 : ℤˣ)) = 1 from rfl, Mk_one,
    Module.End.one_apply] at h
  exact add_eq_left.mp h.symm

theorem edgeVal_unit (c : relativeTwoCocycles goodPlaneExtension.inl (coefRep n)) (d : ℤˣ) :
    edgeVal c (1, d) = 0 := by
  have h := edgeVal_mul c 1 d (1, d)
  have e : ((1 : binaryArithmeticLevel), d) * ((1 : binaryArithmeticLevel), d) = 1 :=
    Prod.ext (mul_one (1 : binaryArithmeticLevel)) (Int.units_mul_self d)
  rw [e, edgeVal_one, Mk_one, Module.End.one_apply] at h
  have two : (2 : ℂ) • edgeVal c (1, d) = 0 := by
    rw [two_smul]
    exact h.symm
  exact (smul_eq_zero.mp two).resolve_left (by norm_num)

theorem edgeVal_unit_mul (c : relativeTwoCocycles goodPlaneExtension.inl (coefRep n))
    (m : binaryArithmeticLevel) (d : ℤˣ) : edgeVal c (m, d) = edgeVal c (m, 1) := by
  have h := edgeVal_mul c m 1 (1, d)
  have e : ((m : binaryArithmeticLevel), (1 : ℤˣ)) * ((1 : binaryArithmeticLevel), d) = (m, d) :=
    Prod.ext (mul_one m) (one_mul d)
  rw [e, edgeVal_unit, map_zero, zero_add] at h
  exact h

theorem edgeVal_mul_one (c : relativeTwoCocycles goodPlaneExtension.inl (coefRep n))
    (m m' : binaryArithmeticLevel) :
    edgeVal c (m * m', 1) = Mk n m (edgeVal c (m', 1)) + edgeVal c (m, 1) := by
  have h := edgeVal_mul c m 1 (m', 1)
  have e : ((m : binaryArithmeticLevel), (1 : ℤˣ)) * (m', (1 : ℤˣ)) = (m * m', 1) :=
    Prod.ext rfl (mul_one (1 : ℤˣ))
  rw [e] at h
  exact h

/-! ### The crossed cocycle for `levelRep (n+1) (-1)` -/

/-- **The edge cocycle**, transported by `Φ = Sym^{n+1}(δ)`: a crossed one-cocycle of
`Γ₁'(3)` for `Sym^{n+1} ⊗ det⁻¹`. -/
def goodPlaneEdgeCocycle (c : relativeTwoCocycles goodPlaneExtension.inl (coefRep n)) :
    crossedCocycles (levelRep (n + 1) (-1)) :=
  ⟨fun m => Phi n (edgeVal c (m, 1)), by
    intro m m'
    change Phi n (edgeVal c (m * m', 1)) =
      Phi n (edgeVal c (m, 1)) + levelRep (n + 1) (-1) m (Phi n (edgeVal c (m', 1)))
    rw [edgeVal_mul_one, map_add, levelRep_Phi]
    exact add_comm _ _⟩

theorem goodPlaneEdgeCocycle_apply (c : relativeTwoCocycles goodPlaneExtension.inl (coefRep n))
    (m : binaryArithmeticLevel) :
    (goodPlaneEdgeCocycle c).val m = Phi n (edgeVal c (m, 1)) := rfl

/-- The edge cocycle is linear in the relative cocycle. -/
def goodPlaneEdgeCocycleLin :
    relativeTwoCocycles goodPlaneExtension.inl (coefRep n) →ₗ[ℂ]
      crossedCocycles (levelRep (n + 1) (-1)) where
  toFun c := goodPlaneEdgeCocycle c
  map_add' c c' := by
    apply Subtype.ext
    funext m
    change Phi n (edgeValLin n (m, 1) (c + c')) =
      Phi n (edgeValLin n (m, 1) c) + Phi n (edgeValLin n (m, 1) c')
    rw [map_add, map_add]
  map_smul' a c := by
    apply Subtype.ext
    funext m
    change Phi n (edgeValLin n (m, 1) (a • c)) = a • Phi n (edgeValLin n (m, 1) c)
    rw [map_smul, map_smul]

end TernaryPeriodPolynomials.LevelThree.GoodPlaneEdge2
