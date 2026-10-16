module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Hecke.AdjointMembershipFiber
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.CuspDualL2
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.L2Assembly
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Good.PlaneRestriction

@[expose] public section


/-!
# The `U`-primitive of the dual plane cocycle at the good plane

The dual plane of the bad line `L₀` is the plane `longWeyl ⟨e₁, e₂⟩ = ⟨e₃, e₂⟩`, which lies in the
orbit of the reference good plane `cuspFlag .plane true = g P` (`g = gF` the rational frame) under
the level element `s = swap(e₁, e₂)`: `longWeyl P = s g P`. Put `w = s g`. Then
`w Λ w⁻¹` is the stabilizer of the dual plane in the level (`Λ` the block-coordinate stabilizer
`ΛG`), and the conjugate cocycle `c' v = ρ(w)⁻¹ c (w v)` of the cocycle `c = y(·)(F)` at the dual
plane `F` is an ambient two-cocycle for `Λ`. Its radical restriction vanishes for every class
(`GoodPlaneRestriction.goodPlaneH2_restriction_zero`, `n > 0`), hence its restriction to the radical
lattice is exact, and the dual involution carries the lattice of `L₀`,
`I + x E₀₁ + y E₀₂`, to `w · upperRadicalLattice(-x, -y) · w⁻¹`. Pulling the primitive back along
`x ↦ w⁻¹ φ(x)` (`HeckeAdjointMembershipEngine.classOf_twistedPullback_eq_zero`) gives the
primitive `θ_U` of the dual plane cocycle restricted to the lattice of `L₀`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous

namespace TernaryPeriodPolynomials.BoundaryDuality.HeckeAdjointMembershipPlane

open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.BoundaryDuality.TraceChains
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.BoundaryDuality.FiberExact
open TernaryPeriodPolynomials.BoundaryDuality.FiberL1 (dualRep)
open TernaryPeriodPolynomials.BoundaryDuality.L2Matrices
  (L₀ uL0 zuL0_val embedZ_apply)
open TernaryPeriodPolynomials.BoundaryDuality.L2Assembly (latL0 latL0_le)
open TernaryPeriodPolynomials.BoundaryDuality.CuspDualL2 (dualFlag_L₀)
open TernaryPeriodPolynomials.BoundaryDuality.HeckeAdjointMembershipEngine
open TernaryPeriodPolynomials.BoundaryDuality.HeckeAdjointMembershipFiber
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.LevelThree.GoodPlaneFrame (gF ΛG gF_val mem_ΛG)
open TernaryPeriodPolynomials.LevelThree.GoodPlaneModel
  (goodPlaneExtension coefRep)
open TernaryPeriodPolynomials.LevelThree.GoodPlaneConj (conjCycle)
open TernaryPeriodPolynomials.LevelThree.GoodPlaneRestriction
  (goodPlaneH2_restriction_zero)

variable {n : ℕ}

/-! ### The level element `s` and the frame `w = s g` -/

/-- The permutation matrix exchanging `e₁` and `e₂`. -/
def swap01 : RationalGL3 :=
  ⟨!![0, 1, 0; 1, 0, 0; 0, 0, 1], !![0, 1, 0; 1, 0, 0; 0, 0, 1], by
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three], by
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

theorem swap01_val : (swap01 : Matrix (Fin 3) (Fin 3) ℚ) = !![0, 1, 0; 1, 0, 0; 0, 0, 1] := rfl

/-- The exchange of `e₁` and `e₂` lies in the level. -/
theorem swap01_mem_level : swap01 ∈ rationalLevel := by
  refine HeckeCommutativity.mem_rationalLevel_of_int swap01
    (!![0, 1, 0; 1, 0, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) ℤ) ?_ ?_ ?_
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [swap01]
  · have h : (!![0, 1, 0; 1, 0, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) ℤ).det = -1 := by
      simp [Matrix.det_fin_three]
    rw [h]
    exact isUnit_one.neg
  · intro j
    fin_cases j <;> simp

/-- The frame `w = s g`. -/
def wG : RationalGL3 := swap01 * gF

theorem wG_val : (wG : Matrix (Fin 3) (Fin 3) ℚ) = !![0, 0, 1; 1, 0, 0; 0, 3, 0] := by
  rw [wG, Units.val_mul, swap01_val, gF_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

/-- The dual plane of `L₀` is the translate of the reference good plane by `s`. -/
theorem dualPlane_eq : (QuotientGroup.mk longWeyl : Flags .plane) =
    swap01 • CuspOrbits.cuspFlag .plane true := by
  rw [LevelThree.GoodPlaneFrame.cuspFlag_eq]
  change (QuotientGroup.mk longWeyl : Flags .plane) = QuotientGroup.mk (swap01 * gF)
  rw [QuotientGroup.eq]
  change InPlaneParabolic (longWeyl⁻¹ * (swap01 * gF))
  have hmul : ((longWeyl⁻¹ * (swap01 * gF) : RationalGL3) : Matrix (Fin 3) (Fin 3) ℚ) =
      longWeylMatrix * (!![0, 1, 0; 1, 0, 0; 0, 0, 1] * !![1, 0, 0; 0, 0, 1; 0, 3, 0]) := by
    rw [Units.val_mul, Units.val_mul, swap01_val, gF_val]
    rfl
  constructor <;> rw [hmul] <;>
    simp [longWeylMatrix, Matrix.mul_apply, Fin.sum_univ_three]

/-- Conjugation by `w` carries `Λ` into the stabilizer in the level of the dual plane. -/
theorem conj_mem_levelStabilizer : ∀ h ∈ ΛG,
    wG * h * wG⁻¹ ∈ levelStabilizer (QuotientGroup.mk longWeyl : Flags .plane) := by
  intro h hh
  have hk := Subgroup.mem_inf.mp ((mem_ΛG h).mp hh)
  have e : wG * h * wG⁻¹ = swap01 * (gF * h * gF⁻¹) * swap01⁻¹ := by
    rw [wG]
    group
  rw [e]
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · exact mul_mem (mul_mem swap01_mem_level hk.1) (inv_mem swap01_mem_level)
  · rw [MulAction.mem_stabilizer_iff, dualPlane_eq, mul_smul, mul_smul, inv_smul_smul,
      MulAction.mem_stabilizer_iff.mp hk.2]

/-! ### The lattice of `L₀` and the upper radical lattice -/

/-- The inverse of a lattice element of `L₀`. -/
theorem uL0_inv (x y : ℤ) : (uL0 x y)⁻¹ = uL0 (-x) (-y) := by
  apply inv_eq_of_mul_eq_one_right
  have h : uL0 x y * uL0 (-x) (-y) = uL0 (x + -x) (y + -y) := latL0.u_mul x y (-x) (-y)
  have h0 : uL0 0 0 = 1 := latL0.u_zero
  have h1 : x + -x = 0 := by omega
  have h2 : y + -y = 0 := by omega
  rw [h1, h2, h0] at h
  exact h

/-- The matrix of the dual involution of a lattice element of `L₀`:
`I - x E₁₀ - 3y E₂₀`. -/
theorem dualInvolution_uL0_val (x y : ℤ) :
    (dualInvolution (uL0 x y)).val =
      !![1, 0, 0; -(x : ℚ), 1, 0; -3 * (y : ℚ), 0, 1] := by
  ext i j
  rw [dualInvolution_val_apply, uL0_inv]
  fin_cases i <;> fin_cases j <;> simp [uL0, embedZ_apply, zuL0_val]

/-- **The dual involution of the lattice of `L₀`, in the frame `w`.** -/
theorem dualInvolution_uL0_mul (x y : ℤ) :
    dualInvolution (uL0 x y) * wG =
      wG * upperRadicalLattice (Multiplicative.ofAdd (-x, -y)) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, dualInvolution_uL0_val, wG_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperRadicalLattice, planeUnipotent, Matrix.mul_apply, Fin.sum_univ_three]

/-- The radical lattice of `Λ` as a subgroup of `GL₃(ℚ)`. -/
abbrev radicalGroup : Subgroup RationalGL3 :=
  (ΛG.subtype.comp goodPlaneExtension.inl).range

theorem radicalGroup_le : radicalGroup ≤ ΛG := by
  rintro _ ⟨a, rfl⟩
  exact (goodPlaneExtension.inl a).property

/-- **The conjugate of the dual involution of the lattice of `L₀` lies in the radical lattice.** -/
theorem latL0_dual_mem : ∀ u ∈ latL0.sub, wG⁻¹ * dualInvolution u * wG ∈ radicalGroup := by
  rintro _ ⟨p, rfl⟩
  refine ⟨Multiplicative.ofAdd (-(Multiplicative.toAdd p).1, -(Multiplicative.toAdd p).2), ?_⟩
  show upperRadicalLattice
      (Multiplicative.ofAdd (-(Multiplicative.toAdd p).1, -(Multiplicative.toAdd p).2)) =
    wG⁻¹ * dualInvolution (uL0 (Multiplicative.toAdd p).1 (Multiplicative.toAdd p).2) * wG
  rw [mul_assoc, dualInvolution_uL0_mul, ← mul_assoc, inv_mul_cancel, one_mul]

/-! ### The primitive -/

/-- **The dual plane `U`-restriction at `L₀` is exact** (`n > 0`, trivial character), for every
plane cocycle. -/
theorem classOf_planeRestriction_L₀_eq_zero (hn : 0 < n)
    (y : MaximalCycles n trivialCharacter .plane) :
    classOf latL0.sub (dualRep (dualityData n trivialCharacter))
      (planeRestriction (dualityData n trivialCharacter) y L₀ latL0.sub latL0_le) = 0 := by
  have hF : (dualityData n trivialCharacter).dualFlag L₀ =
      (QuotientGroup.mk longWeyl : Flags .plane) := dualFlag_L₀
  -- the cocycle at the dual plane and its conjugate to `Λ`
  let cF := fixedPointCycle rationalLevel (rationalCoefficientComponent n trivialCharacter)
    (QuotientGroup.mk longWeyl : Flags .plane) y
  let c' := conjCycle (rationalCoefficientComponent n trivialCharacter) wG
    (levelStabilizer (QuotientGroup.mk longWeyl : Flags .plane)) ΛG conj_mem_levelStabilizer cF
  -- exactness of `c'` on the radical lattice
  have hzero := goodPlaneH2_restriction_zero n hn
    (groupCohomology.H2π (coefRep n)
      (ambientCocycleToGroup ΛG (rationalCoefficientComponent n trivialCharacter) c'))
  have hex : classOf radicalGroup (rationalCoefficientComponent n trivialCharacter)
      (HeckeAdjointMembershipEngine.restrictCocycle
        (rationalCoefficientComponent n trivialCharacter) ΛG radicalGroup radicalGroup_le c') =
        0 :=
    classOf_pullback_eq_zero_of_restriction_zero (rationalCoefficientComponent n trivialCharacter)
      (rationalCoefficientComponent n trivialCharacter) (MonoidHom.id RationalGL3) (fun _ => rfl)
      ΛG radicalGroup c'
      (HeckeAdjointMembershipEngine.restrictCocycle
        (rationalCoefficientComponent n trivialCharacter) ΛG radicalGroup radicalGroup_le c')
      (fun _ => rfl) goodPlaneExtension.inl goodPlaneExtension.inl_injective hzero
      (fun u hu => by
        obtain ⟨a, rfl⟩ := hu
        exact ⟨a, rfl⟩)
  obtain ⟨prim, hprim⟩ := (classOf_eq_zero_iff radicalGroup
    (rationalCoefficientComponent n trivialCharacter) _).mp hex
  exact classOf_twistedPullback_eq_zero (rationalCoefficientComponent n trivialCharacter)
    (dualRep (dualityData n trivialCharacter)) (dualityData n trivialCharacter).φ wG
    (fun _ => rfl)
    (levelStabilizer (QuotientGroup.mk longWeyl : Flags .plane)) radicalGroup latL0.sub
    latL0_dual_mem cF c'.val.val (fun _ => rfl)
    (planeRestriction (dualityData n trivialCharacter) y L₀ latL0.sub latL0_le)
    (planeRestriction_val (dualityData n trivialCharacter) y L₀ _ hF latL0.sub latL0_le)
    prim (fun v => congrFun (congrArg Subtype.val hprim) v)

end TernaryPeriodPolynomials.BoundaryDuality.HeckeAdjointMembershipPlane
