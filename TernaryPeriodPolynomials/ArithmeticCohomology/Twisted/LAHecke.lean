module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.LACoordinate
public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.LineRestriction
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Good.LineHecke

@[expose] public section


/-!
# The local `T_p` at the twisted good line on the binary edge

For the sign-twisted coefficients the local Hecke operator of the explicit correspondence
`goodLineCosets p` acts on the good-line binary edge by
`E(T y) = sgnP p • E y + (p^{n+2})⁻¹ • T_p E y`, with `T_p` the Hecke operator of
`GL₂(ℤ) diag(p,1) GL₂(ℤ)` on `H¹(GL₂(ℤ), Sym^{n+1} ⊗ det^{-1})`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace TernaryPeriodPolynomials.Twisted

open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.PlaneCoordinates
open TernaryPeriodPolynomials.Spectral.LevelOneCosets
open TernaryPeriodPolynomials.Spectral.IdentityPlaneCosets
open TernaryPeriodPolynomials.Spectral.LineCoordinates
open TernaryPeriodPolynomials.Spectral.GoodLineCosets
open TernaryPeriodPolynomials.Spectral.GoodLineEdge
open TernaryPeriodPolynomials.Spectral.GoodLineCoordinate
open TernaryPeriodPolynomials.Spectral.GoodLineHecke
open TernaryPeriodPolynomials.Spectral.IdentityPlaneCoordinate
open TernaryPeriodPolynomials.Spectral.LevelOneHeckeH1
open TernaryPeriodPolynomials.Spectral.HeckeH1
open TernaryPeriodPolynomials.Spectral.AmbientHecke
open TernaryPeriodPolynomials.Spectral.LocalHecke

namespace LH

/-! ### The determinant twist of the binary action -/

/-- The binary action with determinant twist `e` is `det ^ e` times the twist-zero action. -/
theorem homogeneousAction_twist (d : ℕ) (e : ℤ) (A : Binary.GL2) :
    Binary.homogeneousAction d e A =
      (((GeneralLinearGroup.det A : ℂˣ) : ℂ) ^ e) • Binary.homogeneousAction d 0 A := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  rw [Binary.homogeneousAction_coe, LinearMap.smul_apply, Submodule.coe_smul,
    Binary.homogeneousAction_coe, Binary.action_apply, Binary.action_apply, smul_smul]
  congr 1
  change ((GeneralLinearGroup.det A : ℂˣ) : ℂ) ^ e =
    ((GeneralLinearGroup.det A : ℂˣ) : ℂ) ^ e * ((GeneralLinearGroup.det A : ℂˣ) : ℂ) ^ (0 : ℤ)
  rw [zpow_zero, mul_one]

/-- The complex determinant of the Hecke representative `α_j` is `p`. -/
theorem det_cx_rep (p : Nat.Primes) (j : Option (Fin p.val)) :
    ((GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap ℚ ℂ)
      (binaryHeckeRepresentative p j)) : ℂˣ) : ℂ) = (p.val : ℂ) := by
  have h : (GeneralLinearGroup.map (algebraMap ℚ ℂ) (binaryHeckeRepresentative p j)).val =
      (M p j).map (Int.castRingHom ℂ) := by
    ext a b
    have e := congrFun (congrFun (rep_val p j) a) b
    have e' : (binaryHeckeRepresentative p j).val a b = ((M p j a b : ℤ) : ℚ) := by simpa using e
    change algebraMap ℚ ℂ ((binaryHeckeRepresentative p j).val a b) = _
    rw [e']
    simp
  rw [GeneralLinearGroup.val_det_apply, h, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
    modularHeckeMatrix_det]
  simp

/-- `ρ_τ(α_j⁻¹) = p^{n+1} (p⁻¹)^τ ρ_0(B_j)` on `Sym^{n+1} ⊗ det^τ`. -/
theorem rho_rep_invT (n : ℕ) (τ : ℤ) (p : Nat.Primes) (j : Option (Fin p.val))
    (v : Binary.HomogeneousPoly (n + 1)) :
    Binary.homogeneousAction (n + 1) τ
        (GeneralLinearGroup.map (algebraMap ℚ ℂ) (binaryHeckeRepresentative p j)⁻¹) v =
      (((p.val : ℂ) ^ (n + 1)) * ((p.val : ℂ)⁻¹) ^ τ) •
        Binary.homogeneousAction (n + 1) 0 (GeneralLinearGroup.map (algebraMap ℚ ℂ) (BGL p j)) v := by
  have h0 := rho_rep_inv0 n p j v
  change Binary.homogeneousAction (n + 1) 0
    (GeneralLinearGroup.map (algebraMap ℚ ℂ) (binaryHeckeRepresentative p j)⁻¹) v =
      ((p.val : ℂ) ^ (n + 1)) • Binary.homogeneousAction (n + 1) 0
        (GeneralLinearGroup.map (algebraMap ℚ ℂ) (BGL p j)) v at h0
  rw [homogeneousAction_twist (n + 1) τ, LinearMap.smul_apply, h0, smul_smul, map_inv, map_inv,
    Units.val_inv_eq_inv_val, det_cx_rep, mul_comm]

/-- At twist `-1`: `ρ_{-1}(α_j⁻¹) = p^{n+2} ρ_0(B_j)`. -/
theorem rho_rep_inv_neg_one (n : ℕ) (p : Nat.Primes) (j : Option (Fin p.val))
    (v : Binary.HomogeneousPoly (n + 1)) :
    Binary.homogeneousAction (n + 1) (-1)
        (GeneralLinearGroup.map (algebraMap ℚ ℂ) (binaryHeckeRepresentative p j)⁻¹) v =
      ((p.val : ℂ) ^ (n + 2)) •
        Binary.homogeneousAction (n + 1) 0 (GeneralLinearGroup.map (algebraMap ℚ ℂ) (BGL p j)) v := by
  rw [rho_rep_invT, _root_.zpow_neg_one, inv_inv]
  congr 1

/-- The scalar bookkeeping at twist `-1`. -/
theorem cast_p2 (n : ℕ) (p : Nat.Primes) :
    (((p.val : ℂ) ^ (n + 2))⁻¹) * (p.val : ℂ) ^ (n + 2) = 1 := by
  have hp : (p.val : ℂ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  exact inv_mul_cancel₀ (pow_ne_zero _ hp)

end LH

/-! ### Relative cocycles and the Hecke image -/

/-- The relative two-cocycles of the twisted good-line stabilizer. -/
abbrev RelLT (n : ℕ) (χ : RankOneCharacter) :=
  relativeTwoCocycles goodLineRadicalInclusion (goodLineCoefficientRepT n χ)

theorem rel1_UT (n : ℕ) (χ : RankOneCharacter) (c : RelLT n χ) (a b : ℤ × ℤ) :
    c.val (U1 a, U1 b) = 0 := by
  have h := c.2 (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)
  rwa [inl1_eq, inl1_eq] at h

/-- The Hecke image as a relative cocycle. -/
def heckeRelLT (n : ℕ) (χ : RankOneCharacter) (p : Nat.Primes) (c : RelLT n χ) : RelLT n χ :=
  ⟨heckeTwoL p (rationalCoefficientComponent n χ) c.val, by
    intro u v
    rw [inl1_eq, inl1_eq]
    exact heckeTwoL_relative p (rationalCoefficientComponent n χ) c.val (rel1_UT n χ c) _ _⟩

/-! ### The comparison of ambient cohomology with group cohomology of `Λ₁` -/

/-- The comparison of ambient cohomology with group cohomology of `Λ₁`, twisted. -/
def toH2LT (n : ℕ) (χ : RankOneCharacter) :
    H2 Λ₁ (rationalCoefficientComponent n χ) →ₗ[ℂ] groupCohomology.H2 (goodLineCoefficientRepT n χ) :=
  (LinearMap.range (boundaryMap Λ₁ (rationalCoefficientComponent n χ))).liftQ
    ((groupCohomology.H2π (goodLineCoefficientRepT n χ)).hom ∘ₗ
      ambientCocycleToGroup Λ₁ (rationalCoefficientComponent n χ)) (by
      rintro _ ⟨P, rfl⟩
      exact LinearMap.mem_ker.mpr
        ((ambientCocycle_H2_zero_iff Λ₁ (rationalCoefficientComponent n χ) _).mpr ⟨P, rfl⟩))

theorem toH2LT_classOf (n : ℕ) (χ : RankOneCharacter)
    (C : cocycles Λ₁ (rationalCoefficientComponent n χ)) :
    toH2LT n χ (classOf Λ₁ (rationalCoefficientComponent n χ) C) =
      groupCohomology.H2π (goodLineCoefficientRepT n χ)
        (ambientCocycleToGroup Λ₁ (rationalCoefficientComponent n χ) C) := rfl

theorem toH2LT_injective (n : ℕ) (χ : RankOneCharacter) : Function.Injective (toH2LT n χ) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  induction x using Submodule.Quotient.induction_on with
  | _ C =>
  change toH2LT n χ (classOf Λ₁ (rationalCoefficientComponent n χ) C) = 0 at hx
  rw [toH2LT_classOf] at hx
  exact (classOf_eq_zero_iff Λ₁ (rationalCoefficientComponent n χ) C).mpr
    ((ambientCocycle_H2_zero_iff Λ₁ (rationalCoefficientComponent n χ) C).mp hx)

/-- The Hecke image of a class, computed from a relative representative of its image. -/
theorem toH2LT_hecke (n : ℕ) (χ : RankOneCharacter) (p : Nat.Primes)
    (x : H2 Λ₁ (rationalCoefficientComponent n χ)) (c : RelLT n χ)
    (hc : toH2LT n χ x = groupCohomology.H2π (goodLineCoefficientRepT n χ) c.val) :
    toH2LT n χ (cohomologyAction (rationalCoefficientComponent n χ) (goodLineCosets p) x) =
      groupCohomology.H2π (goodLineCoefficientRepT n χ) (heckeRelLT n χ p c).val := by
  induction x using Submodule.Quotient.induction_on with
  | _ C =>
  change toH2LT n χ (cohomologyAction (rationalCoefficientComponent n χ) (goodLineCosets p)
    (classOf Λ₁ (rationalCoefficientComponent n χ) C)) = _
  rw [cohomologyAction_classOf, toH2LT_classOf]
  change toH2LT n χ (classOf Λ₁ (rationalCoefficientComponent n χ) C) = _ at hc
  rw [toH2LT_classOf] at hc
  exact ambientHecke_congr (goodLineCosets p) (rationalCoefficientComponent n χ) C
    (liftCocycle (goodLineCosets p) (rationalCoefficientComponent n χ) c.val)
    (hc.trans (congrArg (groupCohomology.H2π (goodLineCoefficientRepT n χ))
      (ambientCocycleToGroup_lift (goodLineCosets p) (rationalCoefficientComponent n χ) c.val).symm))


/-! ### The Hecke image on the edge cocycle -/

section Edge

variable (n : ℕ) (χ : RankOneCharacter) (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1)

theorem edgeL_eqT (c : RelLT n χ) (μ : GL (Fin 2) ℤ) (y : ℤ × ℤ) :
    edgeL (rationalCoefficientComponent n χ) c.val μ y =
      goodLineRadicalEdgeCycleT n χ c μ (Multiplicative.ofAdd y) := by
  rw [goodLineSplitEdgeCycle_applyT, inl1_eq, inl1_eq, splitting1_eq]
  rfl

/-- The pair of the edge cocycle at `μ`. -/
abbrev pairET (c : RelLT n χ) (μ : GL (Fin 2) ℤ) : Fin 2 → HomogeneousPoly n :=
  lowerRadicalCocyclePair n (goodLineRadicalEdgeCycleT n χ c μ)

theorem edgeL_expT (c : RelLT n χ) (μ : GL (Fin 2) ℤ) (y : ℤ × ℤ) :
    @id (HomogeneousPoly n) (edgeL (rationalCoefficientComponent n χ) c.val μ y) =
      Exp n (pairET n χ c μ) y := by
  rw [edgeL_eqT, cocycle_exp]
  rfl

theorem closed_pairET (c : RelLT n χ) (μ : GL (Fin 2) ℤ) : ClosedL n (pairET n χ c μ) :=
  lowerRadicalCocyclePair_generator_closed _

/-- The binary edge cocycle value, as a binary polynomial. -/
def bET (hn : 0 < n) (c : RelLT n χ) (μ : GL (Fin 2) ℤ) : Binary.HomogeneousPoly (n + 1) :=
  @id (Binary.HomogeneousPoly (n + 1)) (goodLineBinaryEdgeCycleT n χ hχ hn c μ)

theorem bET_eq (hn : 0 < n) (c : RelLT n χ) (μ : GL (Fin 2) ℤ) :
    bET n χ hχ hn c μ = lowerRadicalCoordinate n (pairET n χ c μ) := by
  change (goodLineBinaryEdgeCycleT n χ hχ hn c μ : Binary.HomogeneousPoly (n + 1)) = _
  rw [goodLineBinaryEdgeCycle_applyT]
  rfl

theorem bET_coordF (hn : 0 < n) (c : RelLT n χ) (μ : GL (Fin 2) ℤ) :
    bET n χ hχ hn c μ = coordF n (fun y => @id (HomogeneousPoly n)
      (edgeL (rationalCoefficientComponent n χ) c.val μ y)) := by
  rw [bET_eq]
  have h : (fun y => @id (HomogeneousPoly n)
      (edgeL (rationalCoefficientComponent n χ) c.val μ y)) = Exp n (pairET n χ c μ) :=
    funext (edgeL_expT n χ c μ)
  rw [h, coordF_exp]


/-- The Hecke cocycle of `GL₂(ℤ) diag(p, 1) GL₂(ℤ)` on `Sym^{n+1} ⊗ det⁻¹`. -/
abbrev heckeZLT (n : ℕ) (p : Nat.Primes) :
    groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) (-1)) →ₗ[ℂ]
      groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) (-1)) :=
  heckeCocycle (arithmeticCosets p) (arithmeticBinaryRep (n + 1) (-1)) (rationalRho (n + 1) (-1))
    (arithmetic_compat (n + 1) (-1)) integralEmbed_injective

variable (p : Nat.Primes)

/-- **Cocycle-level identity**: `E(Tc) = sgnP p • E(c) + (p^{n+2})⁻¹ • T_p E(c)`. -/
theorem edgeCycleLT_hecke (hn : 0 < n) (c : RelLT n χ) :
    goodLineBinaryEdgeCycleT n χ hχ hn (heckeRelLT n χ p c) =
      ((IdentityPlaneLocalOp.sgnP p : ℤ) : ℂ) • goodLineBinaryEdgeCycleT n χ hχ hn c +
        ((p.val : ℂ) ^ (n + 2))⁻¹ • heckeZLT n p (goodLineBinaryEdgeCycleT n χ hχ hn c) := by
  apply groupCohomology.cocycles₁_ext
  intro m
  have h := LH.coordF_edge_heckeT n χ hχ p c.val (rel1_UT n χ c) (pairET n χ c)
    (closed_pairET n χ c) (edgeL_expT n χ c) m
  have e1 : bET n χ hχ hn (heckeRelLT n χ p c) m =
      ((IdentityPlaneLocalOp.sgnP p : ℤ) : ℂ) • bET n χ hχ hn c m +
        ∑ j : Option (Fin p.val), Binary.homogeneousAction (n + 1) 0 (cx2 (BGL p j))
          (bET n χ hχ hn c (arithmeticDelta p m j)) := by
    rw [bET_coordF n χ hχ hn (heckeRelLT n χ p c) m]
    refine h.trans ?_
    simp only [bET_eq]
  have hz : heckeZLT n p (goodLineBinaryEdgeCycleT n χ hχ hn c) m =
      ∑ j, rationalRho (n + 1) (-1) (binaryHeckeRepresentative p j)⁻¹
        (goodLineBinaryEdgeCycleT n χ hχ hn c (arithmeticDelta p m j)) :=
    heckeCocycle_apply _ _ _ _ _ _ _
  have hp : ((p.val : ℂ) ^ (n + 2)) ≠ 0 := pow_ne_zero _ (by exact_mod_cast p.property.ne_zero)
  have hsum : ∑ j : Option (Fin p.val), Binary.homogeneousAction (n + 1) 0 (cx2 (BGL p j))
        (bET n χ hχ hn c (arithmeticDelta p m j)) =
      ((p.val : ℂ) ^ (n + 2))⁻¹ • heckeZLT n p (goodLineBinaryEdgeCycleT n χ hχ hn c) m := by
    rw [hz, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hj := LH.rho_rep_inv_neg_one n p j
      (goodLineBinaryEdgeCycleT n χ hχ hn c (arithmeticDelta p m j))
    change Binary.homogeneousAction (n + 1) 0 (cx2 (BGL p j))
        (goodLineBinaryEdgeCycleT n χ hχ hn c (arithmeticDelta p m j)) =
      ((p.val : ℂ) ^ (n + 2))⁻¹ • Binary.homogeneousAction (n + 1) (-1)
        (GeneralLinearGroup.map (algebraMap ℚ ℂ) (binaryHeckeRepresentative p j)⁻¹)
        (goodLineBinaryEdgeCycleT n χ hχ hn c (arithmeticDelta p m j))
    rw [hj, smul_smul, inv_mul_cancel₀ hp, one_smul]
  exact e1.trans (by rw [hsum]; rfl)

/-- **Class-level identity for relative cocycles.** -/
theorem fullEdge_heckeRelLT (hn : 0 < n) (c : RelLT n χ) :
    goodLineFullBinaryEdgeT n χ hχ hn
        (groupCohomology.H2π (goodLineCoefficientRepT n χ) (heckeRelLT n χ p c).val) =
      ((IdentityPlaneLocalOp.sgnP p : ℤ) : ℂ) •
          goodLineFullBinaryEdgeT n χ hχ hn
            (groupCohomology.H2π (goodLineCoefficientRepT n χ) c.val) +
        ((p.val : ℂ) ^ (n + 2))⁻¹ • arithmeticHecke (n + 1) (-1) p
          (goodLineFullBinaryEdgeT n χ hχ hn
            (groupCohomology.H2π (goodLineCoefficientRepT n χ) c.val)) := by
  rw [goodLineFullBinaryEdgeT_relative, goodLineFullBinaryEdgeT_relative,
    edgeCycleLT_hecke n χ hχ p hn c]
  simp only [map_add, map_smul]
  rw [arithmeticHecke, heckeH1_H1π]

/-! ### The edge on the whole ambient cohomology -/

include hχ in
/-- A class of `H²(Λ₁, V_χ)` is represented by a relative cocycle of the twisted stabilizer. -/
theorem exists_relLT (x : H2 Λ₁ (rationalCoefficientComponent n χ)) :
    ∃ c : RelLT n χ,
      toH2LT n χ x = groupCohomology.H2π (goodLineCoefficientRepT n χ) c.val := by
  obtain ⟨c, hc⟩ := relativeTwoCocycleClass_surjective goodLineRadicalInclusion
    goodLineRadicalInclusion_injective (goodLineCoefficientRepT n χ)
    ⟨toH2LT n χ x, goodLineH2_restriction_zeroT n χ hχ _⟩
  exact ⟨c, (congrArg Subtype.val hc).symm⟩

/-- **The binary edge of the sign-twisted good line on all of `H²(Λ₁, V_χ)`.** -/
def edgeH2LT (hn : 0 < n) :
    H2 Λ₁ (rationalCoefficientComponent n χ) →ₗ[ℂ]
      groupCohomology.H1 (arithmeticBinaryRep (n + 1) (-1)) :=
  (goodLineFullBinaryEdgeT n χ hχ hn).comp (toH2LT n χ)

theorem edgeH2LT_injective (hn : 0 < n) : Function.Injective (edgeH2LT n χ hχ hn) :=
  (goodLineFullBinaryEdgeT_injective n χ hχ hn).comp (toH2LT_injective n χ)

/-- **The local Hecke operator of the explicit good-line correspondence, identified on the binary
edge.** -/
theorem edgeH2LT_hecke (hn : 0 < n) (x : H2 Λ₁ (rationalCoefficientComponent n χ)) :
    edgeH2LT n χ hχ hn (cohomologyAction (rationalCoefficientComponent n χ) (goodLineCosets p) x) =
      ((IdentityPlaneLocalOp.sgnP p : ℤ) : ℂ) • edgeH2LT n χ hχ hn x +
        ((p.val : ℂ) ^ (n + 2))⁻¹ • arithmeticHecke (n + 1) (-1) p (edgeH2LT n χ hχ hn x) := by
  obtain ⟨c, hc⟩ := exists_relLT n χ hχ x
  change goodLineFullBinaryEdgeT n χ hχ hn
      (toH2LT n χ (cohomologyAction (rationalCoefficientComponent n χ) (goodLineCosets p) x)) =
    ((IdentityPlaneLocalOp.sgnP p : ℤ) : ℂ) • goodLineFullBinaryEdgeT n χ hχ hn (toH2LT n χ x) +
      ((p.val : ℂ) ^ (n + 2))⁻¹ • arithmeticHecke (n + 1) (-1) p
        (goodLineFullBinaryEdgeT n χ hχ hn (toH2LT n χ x))
  rw [toH2LT_hecke n χ p x c hc, hc]
  exact fullEdge_heckeRelLT n χ hχ p hn c

end Edge

end TernaryPeriodPolynomials.Twisted
