module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Source.Rank
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Source.Vectors
public import TernaryPeriodPolynomials.ArithmeticCohomology.MultiplicityOne.Assembly

@[expose] public section


/-!
# The level-three source construction: the named inputs

At a level-three cusp (`(.plane, true)` good plane, `(.line, false)` bad line) the rank lower bound
`CoordinateRankLowerBound` is split through the space `W = levelThreeWeightVectors D.cusp (-(n+3))`
of level-three vectors of `D.cusp` of the cohomological rotation weight (the abstract counterpart
of the classical cusp forms of weight `n + 3` on `Γ₁(3)` lying in `D.cusp`):

* **(U) `LevelThreeLocalMatching`** — the local joint eigenspace has at most as many dimensions as
  `W` has linearly independent vectors.  This is the D-to-classical matching: the edge map
  embeds `localJoint` into the joint eigenspace of `H¹_par(Γ₁'(3), Sym^{n+1} ⊗ det^e)`, the period
  map identifies it with the classical eigenforms of weight `n + 3` on `Γ₁(3)` with the eigenvalues
  of the pair character, and strong multiplicity one puts these forms into `D.cusp`.
* **(L) `LevelThreeSourceConstruction`** — a linear map `W → sourceCocycles D side` whose Shapiro
  coordinate at the cusp is injective.  This is the cohomological induction of a level-three
  vector through the cell `P(𝔸_f) q⁻¹ K₁` of the cusp frame `q`, followed by the cup product with
  the Kostant class; injectivity is the injectivity of the level-three period map.

(U) and (L) are only asked for the trivial character.  For every other character the Shapiro
coordinate images at both level-three cusps vanish, and the rank lower bound is equivalent to the
vanishing `LevelThreeVanishing` (`Spectral.LevelOneNontrivial`); that
vanishing is the third input of `Main.lean`.

Finer forms proved here: (U) in rank at most one follows from the `LevelThreeBridge` (odd `n`),
and in general from a local bound `2` plus the oldform pair input
`LevelThreeOldformPair` (two independent vectors of `W` when the eigenspace is two-dimensional).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SpectralSeparation
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.SourceSpace
open TernaryPeriodPolynomials.Separation
open TernaryPeriodPolynomials.MultiplicityOne

namespace TernaryPeriodPolynomials.LevelThreeSource

variable {n : ℕ}

/-- The rotation weight of the level-three source vectors in degree `n`. -/
abbrev sourceWeight (n : ℕ) : ℤ := -((n : ℤ) + 3)

/-- **(U) Local matching at a level-three cusp.**  For the trivial character and a nonzero pair
with a finite-dimensional local joint eigenspace, `D.cusp` has as many linearly independent
level-three vectors of the cohomological weight as the dimension of that eigenspace. -/
def LevelThreeLocalMatching (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (side : Side) (good : Bool) : Prop :=
  D.chi = trivialCharacter → associatePair D ≠ ⊥ →
    FiniteDimensional ℂ (localJoint n D.chi (pairCharacter D hecke hhecke) side good) →
      ∃ v : Fin (Module.finrank ℂ (localJoint n D.chi (pairCharacter D hecke hhecke) side good)) →
        levelThreeWeightVectors D.cusp (sourceWeight n), LinearIndependent ℂ v

/-- **(L) Source construction at a level-three cusp.**  For the trivial character and a nonzero
pair, a linear map from the level-three weight vectors into the source cocycles of the side whose
Shapiro coordinate at the cusp is injective. -/
def LevelThreeSourceConstruction (D : InducingData n) (side : Side) (good : Bool) : Prop :=
  D.chi = trivialCharacter → associatePair D ≠ ⊥ →
    ∃ Φ : levelThreeWeightVectors D.cusp (sourceWeight n) →ₗ[ℂ] sourceCocycles D side,
      Function.Injective (sourceCoordinate D side good ∘ₗ Φ)

/-- **The oldform pair.**  For the trivial character and a nonzero pair whose local joint
eigenspace at the cusp is two-dimensional, `D.cusp` has two linearly independent level-three
vectors of the cohomological weight.  (A two-dimensional eigenspace only arises from a level-one
eigenform `f`, through `f(τ)` and `f(3τ)`; the two vectors are a spherical vector and its
translate by `diag(1, 3)` at the place three.) -/
def LevelThreeOldformPair (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (side : Side) (good : Bool) : Prop :=
  D.chi = trivialCharacter → associatePair D ≠ ⊥ →
    FiniteDimensional ℂ (localJoint n D.chi (pairCharacter D hecke hhecke) side good) →
      Module.finrank ℂ (localJoint n D.chi (pairCharacter D hecke hhecke) side good) = 2 →
        ∃ v : Fin 2 → levelThreeWeightVectors D.cusp (sourceWeight n), LinearIndependent ℂ v

/-- A nonzero pair of odd degree gives a nonzero level-three weight vector, from M1's bridge. -/
theorem exists_levelThreeWeightVector (hodd : Odd n) (hbridge : LevelThreeBridge)
    (D : InducingData n) (hne : associatePair D ≠ ⊥) :
    ∃ w : D.cusp.smooth, w ≠ 0 ∧ w ∈ levelThreeWeightVectors D.cusp (sourceWeight n) := by
  have hlev : ∃ v : D.cusp.smooth, v ≠ 0 ∧ v.val ∈ levelThreeValues D.cusp := by
    rcases spherical_or_levelThree D hne with hsph | h
    · obtain ⟨v, hv, hfix⟩ := hsph
      exact ⟨v, hv, fun k _ => hfix k⟩
    · exact h
  obtain ⟨halfWeight, hhalf, w, hw, hw0⟩ := hbridge D.cusp n hodd D.cohomological hlev
  exact ⟨w, hw0,
    levelThreeClassicalVectors_le_levelThreeWeightVectors D.cusp halfWeight _ hhalf hw⟩

/-- **(U) in rank at most one** from M1's `LevelThreeBridge` (odd degree). -/
theorem levelThreeLocalMatching_of_finrank_le_one (hodd : Odd n) (hbridge : LevelThreeBridge)
    (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (side : Side) (good : Bool)
    (hle : associatePair D ≠ ⊥ →
      FiniteDimensional ℂ (localJoint n D.chi (pairCharacter D hecke hhecke) side good) →
        Module.finrank ℂ (localJoint n D.chi (pairCharacter D hecke hhecke) side good) ≤ 1) :
    LevelThreeLocalMatching D hecke hhecke side good := by
  intro _ hne hfin
  obtain ⟨w, hw0, hw⟩ := exists_levelThreeWeightVector hodd hbridge D hne
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hle hne hfin) with h0 | h1
  · rw [h0]
    exact ⟨Fin.elim0, linearIndependent_empty_type⟩
  · rw [h1]
    refine ⟨fun _ => ⟨w, hw⟩, linearIndependent_unique_iff.mpr fun h => hw0 ?_⟩
    exact congrArg Subtype.val h

/-- **(U) from the local bound `2`**, M1's bridge (odd degree) and the oldform pair. -/
theorem levelThreeLocalMatching_of_bound (hodd : Odd n) (hbridge : LevelThreeBridge)
    (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (side : Side) (good : Bool)
    (hbound : associatePair D ≠ ⊥ →
      LocalUpperBound n D.chi (pairCharacter D hecke hhecke) side good 2)
    (hpair : LevelThreeOldformPair D hecke hhecke side good) :
    LevelThreeLocalMatching D hecke hhecke side good := by
  intro hχ hne hfin
  have hle := (hbound hne).2
  rcases Nat.lt_or_ge
    (Module.finrank ℂ (localJoint n D.chi (pairCharacter D hecke hhecke) side good)) 2 with
      hlt | hge
  · exact levelThreeLocalMatching_of_finrank_le_one hodd hbridge D hecke hhecke side good
      (fun _ _ => by omega) hχ hne hfin
  · have h2 : Module.finrank ℂ (localJoint n D.chi (pairCharacter D hecke hhecke) side good) =
        2 := le_antisymm hle hge
    rw [h2]
    exact hpair hχ hne hfin h2

end TernaryPeriodPolynomials.LevelThreeSource
