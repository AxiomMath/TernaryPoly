module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Bad.LineModel
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Bad.LineLevel
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Bad.LineLocalOp

@[expose] public section


/-!
# The local `T_p` at the bad-line cusp on the Levi coefficient module

The local Hecke operator `localOp (T_p)` of the bad-line cusp `cuspFlag .line false` preserves the
subspace `badLineLocalRadicalKernel n` of classes with zero radical restriction, and, with
`badLineLeviMap : badLineRadicalKernel n ↪ H¹(Γ₁'(3), Sym^{n+1})`,

`badLineLeviMap (localOp y) = badLineLeviMap y + p^{-(n+1)} · T_p (badLineLeviMap y)`

where `T_p = badLevelHecke p hp3 n` is the Hecke operator of `Γ₁'(3) diag(1, p) Γ₁'(3)` on
`H¹(Γ₁'(3), Sym^{n+1})` (`LevelThreeHeckeH1.levelHecke`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.LevelThree.BadLineFinal

open Matrix GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Spectral
open LineCoordinates IdentityPlaneCosets LevelOneCosets LevelThreeCosets BadLineCoordinates
open BadLineCosets BadLineTransitions BadLineEdge BadLinePairs BadLineHecke BadLineLocal
open BadLineModel BadLineLevel BadLineLocalOp LevelThreeHeckeH1 IdentityPlaneCoordinate
open CuspReduction LocalHecke AmbientHecke ParabolicBounds

variable (n : ℕ)

theorem ker_of_mem (y : H2 ΛB (ρn n)) (hy : y ∈ badLineLocalRadicalKernel n) :
    radicalRestrictionH2 integralBadLineSplitting.conjAct
      (standardBadLineRepresentation n) (standardBadLineInhomogeneousH2Equiv n y) = 0 :=
  LinearMap.mem_ker.mp (Submodule.mem_comap.mp hy)

theorem rep_of_ker (y : H2 ΛB (ρn n)) (hy1 : radicalRestrictionH2 integralBadLineSplitting.conjAct
      (standardBadLineRepresentation n) (standardBadLineInhomogeneousH2Equiv n y) = 0) :
    ∃ z : RZ n, (inhomogeneousBoundaries (standardBadLineRepresentation n)).mkQ z.val =
      standardBadLineInhomogeneousH2Equiv n y :=
  radicalRestrictionH2_ker_representative integralBadLineSplitting.conjAct
    (standardBadLineRepresentation n) (standardBadLineInhomogeneousH2Equiv n y)
    (LinearMap.mem_ker.mpr hy1)

/-- A class of the radical kernel is represented by a relative two-cocycle of `ΛB`. -/
theorem exists_rel_rep (y : H2 ΛB (ρn n)) (hy : y ∈ badLineLocalRadicalKernel n) :
    ∃ (c : groupCohomology.cocycles₂ (Aρ (ρn n))) (hrel : ∀ a b, c (Ux a, Ux b) = 0),
      standardBadLineInhomogeneousH2Equiv n y =
        (inhomogeneousBoundaries (standardBadLineRepresentation n)).mkQ (wc n c hrel).val := by
  have hy1 : radicalRestrictionH2 integralBadLineSplitting.conjAct
      (standardBadLineRepresentation n) (standardBadLineInhomogeneousH2Equiv n y) = 0 :=
    ker_of_mem n y hy
  obtain ⟨z, hz⟩ := rep_of_ker n y hy1
  obtain ⟨c, hc⟩ : ∃ c : groupCohomology.cocycles₂ (Aρ (ρn n)), modelCycle n c = z.val :=
    ⟨cocycleOfModel n z.val, modelCycle_cocycleOfModel n z.val⟩
  have hrel : ∀ a b, c (Ux a, Ux b) = 0 := by
    intro a b
    have h := z.property (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)
    rw [← hc] at h
    exact h
  have hmodz : wc n c hrel = z := Subtype.ext hc
  refine ⟨c, hrel, ?_⟩
  rw [hmodz]
  exact hz.symm

/-- **The Levi cocycle of the Hecke image** (pointwise, at the level of cocycles). -/
theorem eAz_heckeTwo (hn : 0 < n) (p : Nat.Primes) (hp3 : p.val ≠ 3)
    (c : groupCohomology.cocycles₂ (Aρ (ρn n))) (hrel : ∀ a b, c (Ux a, Ux b) = 0)
    (A : binaryArithmeticLevel) :
    (eAz n hn (wc n (heckeTwo p hp3 (ρn n) c) (heckeTwo_relative p hp3 (ρn n) c hrel))).val A =
      (eAz n hn (wc n c hrel)).val A + ((p.val : ℂ) ^ (n + 1))⁻¹ •
        (crossedHeckeCocycles (levelCosets p hp3) (rationalRho (n + 1) 0) (levelRep (n + 1) 0)
          (level_compat (n + 1) 0) levelEmbed_injective (eAz n hn (wc n c hrel))).val A := by
  have hne : ((p.val : ℂ) ^ (n + 1)) ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast p.property.ne_zero)
  rw [levelHeckeCocycle_apply p n hp3 (eAz n hn (wc n c hrel)) A, smul_smul,
    inv_mul_cancel₀ hne, one_smul]
  choose pairOf SOf hpair using fun B => exists_pair n hn c hrel B
  have hwE : ∀ B, (eAz n hn (wc n c hrel)).val B = binaryPairWedge n (pairOf B) := by
    intro B
    rw [eAz_val]
    exact wedge_of_pair n hn c hrel B (pairOf B) (SOf B) (hpair B)
  obtain ⟨S, hS⟩ := edge_heckeTwo_pair n p hp3 c hrel pairOf SOf hpair A
  have hwT : (eAz n hn (wc n (heckeTwo p hp3 (ρn n) c)
        (heckeTwo_relative p hp3 (ρn n) c hrel))).val A =
      binaryPairWedge n (pairOf A + ∑ j : Option (Fin p.val),
        binaryMatrixPairAction n (cx2 (BQ p j)) (pairOf (levelDelta p hp3 A j))) := by
    rw [eAz_val]
    exact wedge_of_pair n hn (heckeTwo p hp3 (ρn n) c) (heckeTwo_relative p hp3 (ρn n) c hrel)
      A _ S hS
  have hj : ∀ j : Option (Fin p.val),
      rationalRho (n + 1) 0 (BQ p j) ((eAz n hn (wc n c hrel)).val (levelDelta p hp3 A j)) =
        binaryPairWedge n (binaryMatrixPairAction n (cx2 (BQ p j))
          (pairOf (levelDelta p hp3 A j))) := by
    intro j
    rw [hwE, binaryPairWedge_matrixAction]
    try rfl
  rw [hwT, hwE A, Finset.sum_congr rfl (fun j _ => hj j)]
  have hadd := map_add (wedgeH n) (pairOf A) (∑ j : Option (Fin p.val),
    binaryMatrixPairAction n (cx2 (BQ p j)) (pairOf (levelDelta p hp3 A j)))
  rw [map_sum] at hadd
  exact hadd

/-- The Hecke image of a relative cocycle lies in the radical kernel. -/
theorem hecke_mem_kernel (p : Nat.Primes) (hp3 : p.val ≠ 3)
    (c : groupCohomology.cocycles₂ (Aρ (ρn n))) (hrel : ∀ a b, c (Ux a, Ux b) = 0)
    (y : H2 ΛB (ρn n))
    (hz : standardBadLineInhomogeneousH2Equiv n y =
      (inhomogeneousBoundaries (standardBadLineRepresentation n)).mkQ (wc n c hrel).val) :
    standardBadLineInhomogeneousH2Equiv n
        (cohomologyAction (ρn n) (badLineCosets p hp3) y) =
      (inhomogeneousBoundaries (standardBadLineRepresentation n)).mkQ
        (wc n (heckeTwo p hp3 (ρn n) c) (heckeTwo_relative p hp3 (ρn n) c hrel)).val := by
  have hy_eq : y = classOf ΛB (ρn n) (liftCocycle (badLineCosets p hp3) (ρn n) c) := by
    apply (standardBadLineInhomogeneousH2Equiv n).injective
    rw [equiv_classOf_lift n p hp3 c]
    exact hz
  rw [hy_eq]
  exact equiv_cohomologyAction n p hp3 c

/-- **The bad-line edge map**: classes of the local cohomology with zero radical restriction map to
`H¹(Γ₁'(3), Sym^{n+1})`. -/
def badLineEdge (hn : 0 < n) :
    badLineLocalRadicalKernel n →ₗ[ℂ] CrossedH1 (binaryArithmeticRepresentation n) :=
  (badLineLeviMap n hn).comp (localToModel n)

theorem badLineEdge_injective (hn : 0 < n) : Function.Injective (badLineEdge n hn) :=
  (badLineLeviMap_injective n hn).comp (localToModel_injective n)

theorem badLineEdge_apply (hn : 0 < n) (x : badLineLocalRadicalKernel n) :
    badLineEdge n hn x = badLineLeviMap n hn (localToModel n x) := rfl

/-- The Hecke image of a class of the radical kernel stays in the radical kernel. -/
theorem cohAct_mem (p : Nat.Primes) (hp3 : p.val ≠ 3)
    (y : H2 ΛB (ρn n)) (hy : y ∈ badLineLocalRadicalKernel n) :
    cohomologyAction (ρn n) (badLineCosets p hp3) y ∈ badLineLocalRadicalKernel n := by
  obtain ⟨c, hrel, hz⟩ := exists_rel_rep n y hy
  have hT := hecke_mem_kernel n p hp3 c hrel y hz
  have hmem : standardBadLineInhomogeneousH2Equiv n
      (cohomologyAction (ρn n) (badLineCosets p hp3) y) ∈
      LinearMap.ker (radicalRestrictionH2 integralBadLineSplitting.conjAct
        (standardBadLineRepresentation n)) := by
    rw [hT]
    exact radicalZeroH2ToFull_mem_ker integralBadLineSplitting.conjAct
      (standardBadLineRepresentation n)
      ((radicalZeroBoundaries integralBadLineSplitting.conjAct
        (standardBadLineRepresentation n)).mkQ
        (wc n (heckeTwo p hp3 (ρn n) c) (heckeTwo_relative p hp3 (ρn n) c hrel)))
  exact hmem

theorem levi_orig (hn : 0 < n) (c : groupCohomology.cocycles₂ (Aρ (ρn n)))
    (hrel : ∀ a b, c (Ux a, Ux b) = 0) (y : H2 ΛB (ρn n))
    (hy : y ∈ badLineLocalRadicalKernel n)
    (hz : standardBadLineInhomogeneousH2Equiv n y =
      (inhomogeneousBoundaries (standardBadLineRepresentation n)).mkQ (wc n c hrel).val) :
    badLineEdge n hn ⟨y, hy⟩ =
      (crossedBoundaries (binaryArithmeticRepresentation n)).mkQ (eAz n hn (wc n c hrel)) := by
  rw [badLineEdge_apply, localToModel_eq n (wc n c hrel) y hy hz]
  exact leviMap_repr n hn (wc n c hrel)

theorem levi_hecke (hn : 0 < n) (p : Nat.Primes) (hp3 : p.val ≠ 3)
    (c : groupCohomology.cocycles₂ (Aρ (ρn n))) (hrel : ∀ a b, c (Ux a, Ux b) = 0)
    (y : H2 ΛB (ρn n))
    (hz : standardBadLineInhomogeneousH2Equiv n y =
      (inhomogeneousBoundaries (standardBadLineRepresentation n)).mkQ (wc n c hrel).val)
    (hy' : cohomologyAction (ρn n) (badLineCosets p hp3) y ∈ badLineLocalRadicalKernel n) :
    badLineEdge n hn ⟨cohomologyAction (ρn n) (badLineCosets p hp3) y, hy'⟩ =
      (crossedBoundaries (binaryArithmeticRepresentation n)).mkQ
        (eAz n hn (wc n (heckeTwo p hp3 (ρn n) c) (heckeTwo_relative p hp3 (ρn n) c hrel))) := by
  rw [badLineEdge_apply, localToModel_eq n
    (wc n (heckeTwo p hp3 (ρn n) c) (heckeTwo_relative p hp3 (ρn n) c hrel))
    (cohomologyAction (ρn n) (badLineCosets p hp3) y) hy' (hecke_mem_kernel n p hp3 c hrel y hz)]
  exact leviMap_repr n hn _

theorem badLevelHecke_mk (p : Nat.Primes) (hp3 : p.val ≠ 3)
    (z : crossedCocycles (binaryArithmeticRepresentation n)) :
    badLevelHecke p hp3 n (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (crossedHeckeCocycles (levelCosets p hp3) (rationalRho (n + 1) 0)
        (levelRep (n + 1) 0) (level_compat (n + 1) 0) levelEmbed_injective z) :=
  levelHecke_mk (n + 1) 0 p hp3 z

/-- The class of a cocycle, with declared codomain. -/
def clsB (E : crossedCocycles (binaryArithmeticRepresentation n)) :
    CrossedH1 (binaryArithmeticRepresentation n) :=
  Submodule.Quotient.mk E

/-- The Hecke relation at the level of classes, from the pointwise cocycle relation. -/
theorem glue (p : Nat.Primes) (hp3 : p.val ≠ 3)
    (E E' : crossedCocycles (binaryArithmeticRepresentation n))
    (h : ∀ A, E'.val A = E.val A + ((p.val : ℂ) ^ (n + 1))⁻¹ •
      (crossedHeckeCocycles (levelCosets p hp3) (rationalRho (n + 1) 0) (levelRep (n + 1) 0)
        (level_compat (n + 1) 0) levelEmbed_injective E).val A) :
    clsB n E' = clsB n E + ((p.val : ℂ) ^ (n + 1))⁻¹ • badLevelHecke p hp3 n (clsB n E) := by
  have hH := badLevelHecke_mk n p hp3 E
  let T : crossedCocycles (binaryArithmeticRepresentation n) :=
    crossedHeckeCocycles (levelCosets p hp3) (rationalRho (n + 1) 0) (levelRep (n + 1) 0)
      (level_compat (n + 1) 0) levelEmbed_injective E
  have hE : E' = E + ((p.val : ℂ) ^ (n + 1))⁻¹ • T := Subtype.ext (funext h)
  show (Submodule.Quotient.mk E' : CrossedH1 (binaryArithmeticRepresentation n)) =
    Submodule.Quotient.mk E + ((p.val : ℂ) ^ (n + 1))⁻¹ •
      badLevelHecke p hp3 n (Submodule.Quotient.mk E)
  rw [hH, hE]
  exact (Submodule.Quotient.mk_add _).trans
    (congrArg (fun t => Submodule.Quotient.mk E + t) (Submodule.Quotient.mk_smul _ _ T))

/-- **The local Hecke operator of the bad line on the radical kernel, in Levi coordinates.** -/
theorem cohAct_eq (hn : 0 < n) (p : Nat.Primes) (hp3 : p.val ≠ 3)
    (y : H2 ΛB (ρn n)) (hy : y ∈ badLineLocalRadicalKernel n)
    (hy' : cohomologyAction (ρn n) (badLineCosets p hp3) y ∈ badLineLocalRadicalKernel n) :
    badLineEdge n hn ⟨cohomologyAction (ρn n) (badLineCosets p hp3) y, hy'⟩ =
      badLineEdge n hn ⟨y, hy⟩ + ((p.val : ℂ) ^ (n + 1))⁻¹ •
        badLevelHecke p hp3 n (badLineEdge n hn ⟨y, hy⟩) := by
  obtain ⟨c, hrel, hz⟩ := exists_rel_rep n y hy
  rw [levi_hecke n hn p hp3 c hrel y hz hy', levi_orig n hn c hrel y hy hz]
  show clsB n _ = clsB n _ + _ • badLevelHecke p hp3 n (clsB n _)
  exact glue n p hp3 _ _ (eAz_heckeTwo n hn p hp3 c hrel)

theorem edge_congr (hn : 0 < n) (z z' : CuspH2 n trivialCharacter .line false)
    (hz : z ∈ badLineLocalRadicalKernel n) (hz' : z' ∈ badLineLocalRadicalKernel n)
    (h : z = z') : badLineEdge n hn ⟨z, hz⟩ = badLineEdge n hn ⟨z', hz'⟩ := by
  subst h
  rfl

theorem localOp_eq_cohAct (p : Nat.Primes) (hp3 : p.val ≠ 3)
    (y : CuspH2 n trivialCharacter .line false) :
    localOp n trivialCharacter (TpExistence.tp p) (TpExistence.tp_awayThree p hp3) .line false y =
      cohomologyAction (ρn n) (badLineCosets p hp3) y :=
  LinearMap.congr_fun (localOp_badLine_tp p n hp3) y

/-- The radical kernel is stable under `localOp (T_p)`. -/
theorem badLine_localOp_mem_kernel (p : Nat.Primes) (hp3 : p.val ≠ 3)
    (y : CuspH2 n trivialCharacter .line false) (hy : y ∈ badLineLocalRadicalKernel n) :
    localOp n trivialCharacter (TpExistence.tp p) (TpExistence.tp_awayThree p hp3) .line false y ∈
      badLineLocalRadicalKernel n := by
  rw [localOp_eq_cohAct]
  exact cohAct_mem n p hp3 y hy

/-- **`localOp` of `T_p` at the bad-line cusp acts on the Levi coordinates of the radical kernel
through `1 + p^{-(n+1)} T_p`.** -/
theorem badLine_localOp_eq (hn : 0 < n) (p : Nat.Primes) (hp3 : p.val ≠ 3)
    (y : CuspH2 n trivialCharacter .line false) (hy : y ∈ badLineLocalRadicalKernel n)
    (hy'' : localOp n trivialCharacter (TpExistence.tp p) (TpExistence.tp_awayThree p hp3)
      .line false y ∈ badLineLocalRadicalKernel n) :
    badLineEdge n hn ⟨localOp n trivialCharacter (TpExistence.tp p)
        (TpExistence.tp_awayThree p hp3) .line false y, hy''⟩ =
      badLineEdge n hn ⟨y, hy⟩ + ((p.val : ℂ) ^ (n + 1))⁻¹ •
        badLevelHecke p hp3 n (badLineEdge n hn ⟨y, hy⟩) := by
  have hy' := cohAct_mem n p hp3 y hy
  rw [edge_congr n hn _ _ hy'' hy' (localOp_eq_cohAct n p hp3 y)]
  exact cohAct_eq n hn p hp3 y hy hy'

end TernaryPeriodPolynomials.LevelThree.BadLineFinal
