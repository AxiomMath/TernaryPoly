module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Hecke.GeneratorsBounds
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Hecke.GenEqBasic
public import TernaryPeriodPolynomials.ArithmeticCohomology.RankTwo.Main
public import TernaryPeriodPolynomials.ArithmeticCohomology.RankTwo.GoodPlane
public import TernaryPeriodPolynomials.ArithmeticCohomology.Oldform.Complete
public import TernaryPeriodPolynomials.ArithmeticCohomology.PeriodLink.Final
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.GoodPlaneSummandWt
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Injective.Main

@[expose] public section


/-!
# The prime eigenspace equals the local joint eigenspace at the good plane

At the good plane (the dual plane of the bad line `L₀`), trivial character, the joint generalized
eigenspace `J` of the prime operators `T_p` embeds through the edge map into the classical joint
generalized eigenspace of `T_p` on `S_{n+3}(Γ₁(3))`, which has dimension at most two
(`HeckeGeneratorsBounds`). We show `J = L = coordinate image`:

* the coordinate image is nonzero for a nonzero pair of any parity: a nonzero level-three weight
  vector of `D.cusp` gives a good-plane source cocycle with nonzero coordinate
  (`coordinateImage_plane_true_ne_bot_of_trivial`);
* if `dim J = 2`, the classical space has dimension two, hence contains an oldform, so `D.cusp` is
  spherical (the argument of `AxiomCodeRankTwo`, for `J` instead of the full local joint eigenspace
  `L`), and the spherical oldform pair gives two independent coordinates;
* otherwise `dim J ≤ 1` and one nonzero coordinate fills `J`.

No condition on a line class is needed: only the nonzero associate pair.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous

namespace TernaryPeriodPolynomials.BoundaryDuality.HeckeGenEq

open TernaryPeriodPolynomials.BoundaryDuality.HeckeGenerators
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Separation
open TernaryPeriodPolynomials.LevelThree
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodParity (levelPeriodMap)
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.SourceSpace
open TernaryPeriodPolynomials.LevelThreeSource
  (levelThreeWeightVectors sourceWeight)

variable {n : ℕ}

/-! ### A nonzero good-plane coordinate -/

/-- **A nonzero pair, trivial character, has a nonzero good-plane coordinate image**, in every
degree `3 ≤ n`. -/
theorem coordinateImage_plane_true_ne_bot_of_trivial (hn : 3 ≤ n) (D : InducingData n)
    (hχ : D.chi = trivialCharacter) (hne : associatePair D ≠ ⊥) :
    coordinateImage D .plane true ≠ ⊥ := by
  have hW : levelThreeWeightVectors D.cusp (-((n : ℤ) + 3)) ≠ ⊥ := by
    rcases MultiplicityOne.spherical_or_levelThree D hne with ⟨v, hv, hfix⟩ | h
    · exact EvenLevelThree.levelThreeWeightVectors_ne_bot_of_levelVectorWt D
        ⟨v, hv, fun k _ => hfix k⟩
    · exact EvenLevelThree.levelThreeWeightVectors_ne_bot_of_levelVectorWt D h
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  have hw : (⟨x, hx⟩ : levelThreeWeightVectors D.cusp (sourceWeight n)) ≠ 0 :=
    fun h => hx0 (congrArg Subtype.val h)
  obtain ⟨c, hc⟩ := EvenLevelThree.goodPlane_sourceCoordinate_ne_zero_of_weightVectorWt D
    hχ (by omega) (LevelThreeInjective.Main.levelPeriodMap_injective_goodPlane n)
    ⟨x, hx⟩ hw
  exact (coordinateImage_ne_bot_iff D .plane true).mpr ⟨c, hc⟩

/-! ### Dimension of the prime eigenspace inside the classical eigenspace -/

/-- **The prime eigenspace at the good plane inside the classical joint generalized eigenspace**:
the edge map is injective and maps `J` into `levelJoint`, which has dimension at most that of the
classical joint generalized eigenspace with eigenvalues `p^{n+1} (c(T_p) - 1)`. -/
theorem finrank_localJointGen_goodPlane_le (hn : 1 ≤ n) (c : HeckeCorrespondence → ℂ)
    (hc : ‖c (TpExistence.tp LevelThreeBoundaryEisenstein.two) - 1‖ ≤ 3 / 4)
    (hinj : Function.Injective (levelPeriodMap (n + 1) (-1))) :
    Module.finrank ℂ (localJointGen n trivialCharacter c .plane true) ≤
      Module.finrank ℂ (LevelThreeJointGen.jointGenEigenspace (((n + 1 : ℕ) : ℤ) + 2)
        (fun q => (c (TpExistence.tp q) - 1) / ((q.val : ℂ) ^ (n + 2))⁻¹ /
          ((q.val : ℂ) ^ (-(-1 : ℤ))))) := by
  have hn0 : 0 < n := by omega
  have : FiniteDimensional ℂ (CuspH2 n trivialCharacter .plane true) :=
    GoodPlaneEdge3.goodPlane_finiteDimensional hn0
  have : FiniteDimensional ℂ (CrossedH1 (ParabolicBounds.levelRep (n + 1) (-1))) :=
    ParabolicBounds.level_H1_finiteDimensional (-1) (Nat.succ_pos n)
  have heq := LinearEquiv.finrank_eq
    (Submodule.equivMapOfInjective (GoodPlaneEdge3.goodPlaneEdge hn0)
      (GoodPlaneEdge3.goodPlaneEdge_injective hn0)
      (localJointGen n trivialCharacter c .plane true))
  rw [heq]
  exact (Submodule.finrank_mono (map_localJointGen_le hn0 c)).trans
    (RankTwo.finrank_levelJoint_le_jointGen n hn c hc hinj)

/-- **Rank two of the prime eigenspace at the good plane forces sphericity** (trivial character,
`3 ≤ n`, nonzero pair): the argument of `RankTwo.sphericalCusp_of_rankTwo_goodPlane` with
the joint generalized eigenspace of the prime operators in place of the full local joint
eigenspace. -/
theorem sphericalCusp_of_rankTwo_localJointGen_goodPlane (hn : 3 ≤ n) (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hχ : D.chi = trivialCharacter) (hne : associatePair D ≠ ⊥)
    (h2 : Module.finrank ℂ
      (localJointGen n D.chi (pairCharacter D hecke hhecke) .plane true) = 2) :
    SphericalCusp D.cusp := by
  have hc := MultiplicityOne.pairChar_two_bound D hχ hecke hhecke hn hne
  rw [hχ] at h2
  have hle := finrank_localJointGen_goodPlane_le (n := n) (by omega) (pairCharacter D hecke hhecke)
    hc (LevelThreeInjective.Main.levelPeriodMap_injective_goodPlane n)
  have hpos : (0 : ℤ) < ((n + 1 : ℕ) : ℤ) + 2 := by omega
  have hup := LevelThreeJointGen.finrank_jointGenEigenspace_le_two hpos
    (LevelThreePeterssonSemisimple.levelThree_semisimple (((n + 1 : ℕ) : ℤ) + 2))
    (fun q => (pairCharacter D hecke hhecke (TpExistence.tp q) - 1) /
      ((q.val : ℂ) ^ (n + 2))⁻¹ / ((q.val : ℂ) ^ (-(-1 : ℤ))))
  have h2' := le_antisymm hup (h2.symm.le.trans hle)
  refine RankTwo.sphericalCusp_of_finrank_jointGen_two D hχ hecke hhecke hne _
    (fun p _ => ?_) h2'
  exact RankTwo.goodPlane_eigenvalue n _ _ (by exact_mod_cast p.property.ne_zero)

/-- **Prime eigenspace at the good plane, non-spherical case: dimension at most one.** -/
theorem localUpperBoundGen_goodPlane_pair_one (hn : 3 ≤ n) (D : InducingData n)
    (hχ : D.chi = trivialCharacter) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (hne : associatePair D ≠ ⊥)
    (hns : ¬ SphericalCusp D.cusp) :
    LocalUpperBoundGen n D.chi (pairCharacter D hecke hhecke) .plane true 1 := by
  obtain ⟨hfin, hle⟩ := localUpperBoundGen_goodPlane_pair hn D hχ hecke hhecke hne
  refine ⟨hfin, ?_⟩
  by_contra hlt
  exact hns (sphericalCusp_of_rankTwo_localJointGen_goodPlane hn D hecke hhecke hχ hne
    (by omega))

/-! ### The equality -/

/-- **Good plane, trivial character: the prime eigenspace is the coordinate image and the local
joint eigenspace** (`3 ≤ n`, nonzero pair). -/
theorem localJointGen_eq_coordinateImage_goodPlane_trivial (hn : 3 ≤ n) (D : InducingData n)
    (hχ : D.chi = trivialCharacter) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (hne : associatePair D ≠ ⊥) :
    localJointGen n D.chi (pairCharacter D hecke hhecke) .plane true =
        coordinateImage D .plane true ∧
      localJoint n D.chi (pairCharacter D hecke hhecke) .plane true =
        coordinateImage D .plane true := by
  by_cases hsph : SphericalCusp D.cusp
  · exact localJointGen_eq_coordinateImage_of_lowerBound D hecke hhecke .plane true
      (localUpperBoundGen_goodPlane_pair hn D hχ hecke hhecke hne)
      (Oldform.coordinateLowerBound_goodPlane_two_of_spherical D hχ hsph
        (PeriodLink.levelThreePeriodNonvanishing n))
  · exact localJointGen_eq_coordinateImage_of_ne_bot D hecke hhecke .plane true
      (localUpperBoundGen_goodPlane_pair_one hn D hχ hecke hhecke hne hsph)
      (coordinateImage_plane_true_ne_bot_of_trivial hn D hχ hne)

/-- **Good plane, trivial character: the prime eigenspace is the local joint eigenspace**
(`3 ≤ n`, nonzero pair; no condition on the line class). -/
theorem localJointGen_eq_localJoint_goodPlane_trivial (hn : 3 ≤ n) (D : InducingData n)
    (hχ : D.chi = trivialCharacter) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (hne : associatePair D ≠ ⊥) :
    localJointGen n D.chi (pairCharacter D hecke hhecke) .plane true =
      localJoint n D.chi (pairCharacter D hecke hhecke) .plane true :=
  localJointGen_eq_localJoint_of_coordinate
    (localJointGen_eq_coordinateImage_goodPlane_trivial hn D hχ hecke hhecke hne)

end TernaryPeriodPolynomials.BoundaryDuality.HeckeGenEq
