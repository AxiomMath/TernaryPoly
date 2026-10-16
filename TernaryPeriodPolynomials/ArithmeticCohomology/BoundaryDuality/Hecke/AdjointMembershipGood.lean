module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Hecke.AdjointMembership
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Hecke.AdjointMembershipFiber
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.CuspDualL2
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.L2Assembly
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.IdentityPlaneRestriction
public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.LineRestriction
public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.PlaneEdge
public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.PlaneEven

@[expose] public section


/-!
# The `U`-primitives at the good line `L₁`

The good line `L₁ = ⟨e₃⟩` of the boundary trace is the line flag `rationalGoodLine`, and the lattice
`U = {I + 3x E₂₀ + 3y E₂₁}` of its stabilizer is the image of the lower radical lattice
`lowerRadicalLattice`. Its dual plane is the identity plane `P₀ = ⟨e₁, e₂⟩`, and the dual involution
carries `I + 3x E₂₀ + 3y E₂₁` to `I - x E₀₂ - y E₁₂`, a value of the upper radical lattice
`upperRadicalLattice`. Hence the restrictions to `U` of the line cocycle at `L₁` and of the dual
plane cocycle at `P₀` are exact as soon as the radical restrictions of the corresponding local
classes vanish:

* line, trivial character: the Shapiro coordinate of a line summand class at `L₁` lies in `KL`
  (`HeckeAdjointMembership.cuspRes_line_true_mem_ML`), i.e. has vanishing radical restriction;
* line, odd character: every class of the local cohomology has vanishing radical restriction
  (`Twisted.goodLineH2_restriction_zeroT`);
* plane, odd degree (trivial character) or any degree (odd character): every class of the local
  cohomology at the identity plane has vanishing radical restriction
  (`identityPlaneH2_restriction_zero`, `Twisted.H2_restriction_zeroT`);
* plane, trivial character and even degree: the local joint generalized eigenspace at the identity
  plane is zero, so the coordinate of a plane summand class there vanishes.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic

namespace TernaryPeriodPolynomials.BoundaryDuality.HeckeAdjointMembershipGood

open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.BoundaryDuality.TraceChains
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.BoundaryDuality.FiberExact
open TernaryPeriodPolynomials.BoundaryDuality.FiberL1 (dualRep)
open TernaryPeriodPolynomials.BoundaryDuality.L2Matrices
  (L₁ g₂ uL1 zuL1_val embedZ_apply)
open TernaryPeriodPolynomials.BoundaryDuality.L2Assembly (latL1 latL1_le)
open TernaryPeriodPolynomials.BoundaryDuality.CuspDualL2 (g₂_inv_val dualFlag_L₁)
open TernaryPeriodPolynomials.BoundaryDuality.HeckeAdjointMembership
open TernaryPeriodPolynomials.BoundaryDuality.HeckeAdjointMembershipFiber
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspReduction

variable {n : ℕ}

/-! ### The line `L₁` and its lattice -/

/-- The line `L₁ = ⟨e₃⟩` is the good-line flag `rationalGoodLine`. -/
theorem L₁_eq_goodLine : L₁ = (QuotientGroup.mk rationalGoodLine : Flags .line) := by
  change (QuotientGroup.mk g₂ : Flags .line) = QuotientGroup.mk rationalGoodLine
  rw [QuotientGroup.eq]
  refine ⟨?_, ?_⟩ <;> rw [Units.val_mul, g₂_inv_val] <;>
    simp [rationalGoodLine, Matrix.mul_apply, Fin.sum_univ_three]

/-- The parametrization of the lattice of `L₁` is the lower radical lattice. -/
theorem latL1_hom_eq (p : Multiplicative (ℤ × ℤ)) : latL1.hom p = lowerRadicalLattice p := by
  show uL1 (Multiplicative.toAdd p).1 (Multiplicative.toAdd p).2 = lowerRadicalLattice p
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uL1, embedZ_apply, zuL1_val, lowerRadicalLattice, lowerPlaneUnipotent]

/-- Every element of the lattice of `L₁` is a value of the lower radical lattice. -/
theorem latL1_mem_rad : ∀ u ∈ latL1.sub, ∃ a : RadicalLattice, lowerRadicalLattice a = u := by
  rintro _ ⟨p, rfl⟩
  exact ⟨p, (latL1_hom_eq p).symm⟩

/-- The inverse of a lattice element. -/
theorem uL1_inv (x y : ℤ) : (uL1 x y)⁻¹ = uL1 (-x) (-y) := by
  apply inv_eq_of_mul_eq_one_right
  have h : uL1 x y * uL1 (-x) (-y) = uL1 (x + -x) (y + -y) := latL1.u_mul x y (-x) (-y)
  have h0 : uL1 0 0 = 1 := latL1.u_zero
  have h1 : x + -x = 0 := by omega
  have h2 : y + -y = 0 := by omega
  rw [h1, h2, h0] at h
  exact h

/-- **The dual involution carries the lattice of `L₁` to the upper radical lattice**:
`I + 3x E₂₀ + 3y E₂₁ ↦ I - x E₀₂ - y E₁₂`. -/
theorem dualInvolution_uL1 (x y : ℤ) :
    dualInvolution (uL1 x y) = upperRadicalLattice (Multiplicative.ofAdd (-x, -y)) := by
  apply Units.ext
  ext i j
  rw [dualInvolution_val_apply, uL1_inv]
  fin_cases i <;> fin_cases j <;>
    simp [uL1, embedZ_apply, zuL1_val, upperRadicalLattice, planeUnipotent] <;> ring

/-- The dual involution of an element of the lattice of `L₁` is a value of the upper radical
lattice, in the stabilizer of the identity plane. -/
theorem latL1_dual_mem_rad : ∀ u ∈ latL1.sub,
    ∃ a : RadicalLattice, (identityPlaneRadicalInclusion a).val = dualInvolution u := by
  rintro _ ⟨p, rfl⟩
  refine ⟨Multiplicative.ofAdd (-(Multiplicative.toAdd p).1, -(Multiplicative.toAdd p).2), ?_⟩
  exact (dualInvolution_uL1 (Multiplicative.toAdd p).1 (Multiplicative.toAdd p).2).symm

/-! ### The line cocycle at `L₁` -/

/-- **Good-line restriction for a class in `ML`.** The reference coordinate of the line class at
the good-line cusp lies in `ML`, the pull-back of `KL` along the transport `psiL` to the stabilizer
of `mk rationalGoodLine`. -/
theorem classOf_lineRestriction_goodLine_eq_zero (z : MaximalCycles n trivialCharacter .line)
    (Lf : Flags .line) (hLf : Lf = (QuotientGroup.mk rationalGoodLine : Flags .line))
    (U : Subgroup RationalGL3) (hU : U ≤ levelStabilizer Lf)
    (hrad : ∀ u ∈ U, ∃ a : RadicalLattice, lowerRadicalLattice a = u)
    (hML : cuspRes n trivialCharacter .line true
      (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter)
        .line) z) ∈ LocalUniqueness.ML n) :
    classOf U (rationalCoefficientComponent n trivialCharacter) (lineRestriction z Lf U hU) = 0 := by
  subst hLf
  have hKL : fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter)
      (QuotientGroup.mk rationalGoodLine)
      (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter)
        .line) z) ∈ GoodLineHecke.KL n := by
    rw [fixedPointH2_eq_transport trivialCharacter .line true
      (QuotientGroup.mk rationalGoodLine) GoodLineLocalOp.gammaL GoodLineLocalOp.gammaL_smul]
    exact (Submodule.mem_comap (f := GoodLineLocalOp.psiL n) (p := GoodLineHecke.KL n)).mp hML
  refine classOf_lineRestriction_eq_zero z _ U hU goodLineRadicalInclusion ?_ ?_ ?_
  · intro a b h
    exact lowerRadicalLattice_injective (congrArg Subtype.val h)
  · exact LinearMap.mem_ker.mp (Submodule.mem_comap.mp hKL)
  · intro u hu
    obtain ⟨a, ha⟩ := hrad u hu
    exact ⟨a, ha⟩

/-- **The line `U`-restriction at `L₁` is exact for a line summand class** (trivial character,
`3 ≤ n`, nonzero associate pair). -/
theorem classOf_lineRestriction_L₁_eq_zero (cusp : CuspidalRepresentation)
    (coh : Cohomological cusp n) (hecke : BoundaryHecke n trivialCharacter)
    (hhecke : ActualBoundaryHecke n trivialCharacter hecke) (hn : 3 ≤ n)
    (hne : associatePair (trivialData cusp coh) ≠ ⊥) (z : MaximalCycles n trivialCharacter .line)
    (hz : classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z ∈
        boundarySummand (trivialData cusp coh) .line) :
    classOf latL1.sub (rationalCoefficientComponent n trivialCharacter)
      (lineRestriction z L₁ latL1.sub latL1_le) = 0 := by
  exact classOf_lineRestriction_goodLine_eq_zero z L₁ L₁_eq_goodLine latL1.sub latL1_le
    latL1_mem_rad (cuspRes_line_true_mem_ML cusp coh hecke hhecke hn hne hz)

/-- **The line `U`-restriction at `L₁` is exact for every class, for an odd character.** -/
theorem classOf_lineRestriction_L₁_eq_zero_twisted (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (z : MaximalCycles n χ .line) :
    classOf latL1.sub (rationalCoefficientComponent n χ)
      (lineRestriction z L₁ latL1.sub latL1_le) = 0 := by
  have key : ∀ (Lf : Flags .line) (hLf : Lf = (QuotientGroup.mk rationalGoodLine : Flags .line))
      (hU : latL1.sub ≤ levelStabilizer Lf),
      classOf latL1.sub (rationalCoefficientComponent n χ) (lineRestriction z Lf latL1.sub hU) =
        0 := by
    intro Lf hLf hU
    subst hLf
    refine classOf_lineRestriction_eq_zero z _ latL1.sub hU goodLineRadicalInclusion ?_ ?_ ?_
    · intro a b h
      exact lowerRadicalLattice_injective (congrArg Subtype.val h)
    · exact Twisted.goodLineH2_restriction_zeroT n χ hχ _
    · intro u hu
      obtain ⟨a, ha⟩ := latL1_mem_rad u hu
      exact ⟨a, ha⟩
  exact key L₁ L₁_eq_goodLine latL1_le

/-! ### The dual plane cocycle at the identity plane -/

/-- **The dual plane `U`-restriction at `L₁` is exact in odd degree** (trivial character). -/
theorem classOf_planeRestriction_L₁_eq_zero_odd (hn : 0 < n) (hodd : Odd n)
    (y : MaximalCycles n trivialCharacter .plane) :
    classOf latL1.sub (dualRep (dualityData n trivialCharacter))
      (planeRestriction (dualityData n trivialCharacter) y L₁ latL1.sub latL1_le) = 0 :=
  classOf_planeRestriction_eq_zero (dualityData n trivialCharacter) y L₁
    (QuotientGroup.mk (1 : RationalGL3)) dualFlag_L₁ latL1.sub latL1_le
    identityPlaneRadicalInclusion
    (fun _ _ h => upperRadicalLattice_injective (congrArg Subtype.val h))
    (identityPlaneH2_restriction_zero n hn hodd _) latL1_dual_mem_rad

/-- **The dual plane `U`-restriction at `L₁` is exact for an odd character** (`n > 0`, any
parity, every plane cocycle). -/
theorem classOf_planeRestriction_L₁_eq_zero_twisted (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (hn : 0 < n)
    (y : MaximalCycles n χ .plane) :
    classOf latL1.sub (dualRep (dualityData n χ))
      (planeRestriction (dualityData n χ) y L₁ latL1.sub latL1_le) = 0 :=
  classOf_planeRestriction_eq_zero (dualityData n χ) y L₁ (QuotientGroup.mk (1 : RationalGL3))
    dualFlag_L₁ latL1.sub latL1_le identityPlaneRadicalInclusion
    (fun _ _ h => upperRadicalLattice_injective (congrArg Subtype.val h))
    (Twisted.H2_restriction_zeroT n χ hχ hn _) latL1_dual_mem_rad

/-- **The dual plane `U`-restriction at `L₁` is exact if the plane class vanishes at the identity
plane** (this is the case for a plane summand class when the trivial character has even degree). -/
theorem classOf_planeRestriction_L₁_eq_zero_of_coordinate (χ : RankOneCharacter)
    (y : MaximalCycles n χ .plane)
    (h : fixedPointH2 rationalLevel (rationalCoefficientComponent n χ)
      (QuotientGroup.mk (1 : RationalGL3))
      (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .plane) y) =
        0) :
    classOf latL1.sub (dualRep (dualityData n χ))
      (planeRestriction (dualityData n χ) y L₁ latL1.sub latL1_le) = 0 :=
  classOf_planeRestriction_eq_zero_of_classOf (dualityData n χ) y L₁
    (QuotientGroup.mk (1 : RationalGL3)) dualFlag_L₁ latL1.sub latL1_le
    (fun u hu => by
      obtain ⟨a, ha⟩ := latL1_dual_mem_rad u hu
      change dualInvolution u ∈ levelStabilizer (QuotientGroup.mk (1 : RationalGL3))
      rw [← ha]
      exact (identityPlaneRadicalInclusion a).property)
    h

/-- **The dual plane `U`-restriction at `L₁` for a plane summand class, trivial character, even
degree**: the local joint generalized eigenspace at the identity plane vanishes. -/
theorem classOf_planeRestriction_L₁_eq_zero_even (cusp : CuspidalRepresentation)
    (coh : Cohomological cusp n) (hecke : BoundaryHecke n trivialCharacter)
    (hhecke : ActualBoundaryHecke n trivialCharacter hecke) (hn : 0 < n) (heven : Even n)
    (y : MaximalCycles n trivialCharacter .plane)
    (hy : classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y ∈
        boundarySummand (trivialData cusp coh) .plane) :
    classOf latL1.sub (dualRep (dualityData n trivialCharacter))
      (planeRestriction (dualityData n trivialCharacter) y L₁ latL1.sub latL1_le) = 0 := by
  refine classOf_planeRestriction_L₁_eq_zero_of_coordinate trivialCharacter y ?_
  have hbot := Separation.localJoint_plane_false_eq_bot_of_even (trivialData cusp coh)
    rfl hecke hhecke hn heven
  have hmem := Separation.cuspRes_mem_localJoint_of_mem (trivialData cusp coh) hecke
    hhecke .plane false hy
  rw [hbot, Submodule.mem_bot] at hmem
  exact hmem

end TernaryPeriodPolynomials.BoundaryDuality.HeckeAdjointMembershipGood
