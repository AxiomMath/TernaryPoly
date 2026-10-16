module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Bad.LineRadical

@[expose] public section


/-!
# The edge of the Hecke image in pair coordinates

Combining `edge_heckeTwo'` (the cocycle-level formula) with the pair calculus of `BadLinePairs` and
the radical computation of `BadLineRadical`: if for every Levi element `A` the mixed cochain
`edge c A` of a relative cocycle `c` of `ΛB` is a linear cocycle `LP (P A)` plus a radical
coboundary, then so is the mixed cochain of `T c`, with pair

`P(T c, A) = P(c, A) + ∑_j B_j · P(c, δ_j(A))`

(`edge_heckeTwo_pair`), where `B_j · P` is Sol's `binaryMatrixPairAction` for the Levi blocks
`B_j = p α_j⁻¹` of the level-three Hecke cosets.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.LevelThree.BadLineHecke

open Matrix GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Spectral
open LineCoordinates IdentityPlaneCosets LevelOneCosets LevelThreeCosets BadLineCoordinates
open BadLineCosets BadLineTransitions BadLineVectors BadLineEdge BadLinePairs BadLineRadical
open IdentityPlaneCoordinate

variable (n : ℕ)

/-- The linear cochain `LP`, valued in the coefficient module of `ΛB`. -/
def LPA (P : Binary.HomogeneousPoly n × Binary.HomogeneousPoly n) (v : ℤ × ℤ) :
    Aρ (ρn n) := LP n P v

/-- `LPA` as an additive homomorphism. -/
def LPhA (P : Binary.HomogeneousPoly n × Binary.HomogeneousPoly n) :
    (ℤ × ℤ) →+ Aρ (ρn n) :=
  AddMonoidHom.mk' (LPA n P) (LP_add n P)

theorem LPA_add (P Q : Binary.HomogeneousPoly n × Binary.HomogeneousPoly n) (v : ℤ × ℤ) :
    LPA n (P + Q) v = LPA n P v + LPA n Q v := LP_pair_add n P Q v

theorem LPA_sum {ι : Type*} (s : Finset ι)
    (P : ι → Binary.HomogeneousPoly n × Binary.HomogeneousPoly n) (v : ℤ × ℤ) :
    LPA n (∑ i ∈ s, P i) v = ∑ i ∈ s, LPA n (P i) v := LP_pair_sum n s P v

theorem LPA_scalar (p : Nat.Primes) (P : Binary.HomogeneousPoly n × Binary.HomogeneousPoly n)
    (w : ℚ × ℚ) (v : ℤ × ℤ) :
    R1 (ρn n) (R w (epsU p) 1) (LPA n P v) = ((epsP p : ℂ))⁻¹ • LPA n P v := by
  change ρn n (R w (epsU p) 1) (LP n P v) = ((epsP p : ℂ))⁻¹ • LP n P v
  simp only [LP, map_add, map_smul, rho_R_one_emb, epsU_val, map_intCast]
  module

theorem LevUx (p : Nat.Primes) (hp3 : p.val ≠ 3) (r : ℤ × ℤ) (j : Option (Fin p.val)) :
    sLev p j * ((Ux (ivmul r (Bl p j)) : ΛB) : RationalGL3) =
      ((Ux r : ΛB) : RationalGL3) * sLev p j := by
  have h := levi_mul p hp3 r 1 1 j
  rw [levelDelta_one, levelNext_one] at h
  exact h

/-- **The Levi term of the edge of the Hecke image in pair form.** -/
theorem levi_term_pair (p : Nat.Primes) (hp3 : p.val ≠ 3)
    (c : groupCohomology.cocycles₂ (Aρ (ρn n))) (B : binaryArithmeticLevel)
    (j : Option (Fin p.val)) (P : Binary.HomogeneousPoly n × Binary.HomogeneousPoly n)
    (S : Aρ (ρn n))
    (h : ∀ v : ℤ × ℤ, edgeB (ρn n) c B v = LPA n P v + (R1 (ρn n) (Ux v) S - S))
    (r : ℤ × ℤ) :
    R1 (ρn n) (sLev p j) (edgeB (ρn n) c B (ivmul r (Bl p j))) =
      LPA n (binaryMatrixPairAction n (cx2 (BQ p j)) P) r +
        (R1 (ρn n) (Ux r) (R1 (ρn n) (sLev p j) S) - R1 (ρn n) (sLev p j) S) := by
  have e1 : R1 (ρn n) (sLev p j) (LPA n P (ivmul r (Bl p j))) =
      LPA n (binaryMatrixPairAction n (cx2 (BQ p j)) P) r := levi_LP n p j P r
  have e2 : R1 (ρn n) (sLev p j) (R1 (ρn n) (Ux (ivmul r (Bl p j))) S) =
      R1 (ρn n) (Ux r) (R1 (ρn n) (sLev p j) S) :=
    (R1_mul (ρn n) _ _ _).trans ((congrArg (fun g => R1 (ρn n) g S) (LevUx p hp3 r j)).trans
      (R1_mul (ρn n) _ _ _).symm)
  rw [h, map_add, map_sub, e1, e2]

/-- **The edge of `T c` is again a linear cocycle plus a coboundary.** -/
theorem edge_heckeTwo_pair (p : Nat.Primes) (hp3 : p.val ≠ 3)
    (c : groupCohomology.cocycles₂ (Aρ (ρn n))) (hrel : ∀ a b, c (Ux a, Ux b) = 0)
    (pairOf : binaryArithmeticLevel → Binary.HomogeneousPoly n × Binary.HomogeneousPoly n)
    (SOf : binaryArithmeticLevel → Aρ (ρn n))
    (hpair : ∀ (B : binaryArithmeticLevel) (v : ℤ × ℤ),
      edgeB (ρn n) c B v = LPA n (pairOf B) v + (R1 (ρn n) (Ux v) (SOf B) - SOf B))
    (A : binaryArithmeticLevel) :
    ∃ S : Aρ (ρn n), ∀ r : ℤ × ℤ,
      edgeB (ρn n) (heckeTwo p hp3 (ρn n) c) A r =
        LPA n (pairOf A + ∑ j : Option (Fin p.val),
          binaryMatrixPairAction n (cx2 (BQ p j)) (pairOf (levelDelta p hp3 A j))) r +
        (R1 (ρn n) (Ux r) S - S) := by
  obtain ⟨S'', hS''⟩ := rad_pair p A (ρn n) c (LPhA n (pairOf A))
    (fun w v => LPA_scalar n p (pairOf A) w v) (SOf A) (hpair A)
  refine ⟨S'' + SOf A + ∑ j : Option (Fin p.val),
    R1 (ρn n) (sLev p j) (SOf (levelDelta p hp3 A j)), fun r => ?_⟩
  rw [edge_heckeTwo' p hp3 (ρn n) c hrel A r, hS'', hpair A r,
    Finset.sum_congr rfl (fun j _ => levi_term_pair n p hp3 c (levelDelta p hp3 A j) j
      (pairOf (levelDelta p hp3 A j)) (SOf (levelDelta p hp3 A j)) (hpair _) r),
    LPA_add, LPA_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [map_add, map_sum]
  abel

end TernaryPeriodPolynomials.LevelThree.BadLineHecke
