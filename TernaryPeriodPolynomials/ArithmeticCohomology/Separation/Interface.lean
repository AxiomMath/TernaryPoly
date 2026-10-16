module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.CuspReduction

@[expose] public section


/-!
# The separation interface: local upper bounds and global lower bounds at the four cusps

Eigencharacter separation of the associate pair (the single input of the three
projector/recovery targets) reduces, by `CuspReduction.eigenSeparated_of_cusps`, to one statement
per cusp `(side, good)`:

  every class of `localJoint n D.chi c side good` (the local joint generalized eigenspace of the
  pair character `c`) is the Shapiro coordinate of a class of `boundarySummand D side` vanishing at
  the other cusp of `side`.

Equivalently (`cuspStatement_iff`), `localJoint ≤ supportedImage D side good`, where
`supportedImage` is the image under the Shapiro coordinate of the summand classes supported at the
cusp. This file splits each such inclusion into two halves with a shared multiplicity `m`:

* `LocalUpperBound n χ c side good m` (purely local, about `H²(Γ_F, V)` and its local Hecke
  operators): the local joint generalized eigenspace is finite-dimensional of dimension `≤ m`;
* `GlobalLowerBound D side good m` (global, about the inducing datum `D`): there are `m` linearly
  independent local coordinates of summand classes supported at the cusp.

Since summand classes are Hecke eigenvectors with the pair character
(`supportedImage_le_localJoint`), the two halves force equality, and
`eigenSeparated_of_localStatements` proves separation.
`eigenSeparated_of_multiplicityOne` is the special case `m ≤ 1` phrased without dimensions.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SpectralSeparation
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspReduction

namespace TernaryPeriodPolynomials.Separation

variable {n : ℕ}

/-! ## The interface predicates -/

/-- **Local half.** At the cusp `(side, good)` the joint generalized
eigenspace of the local away-three Hecke operators for the character `c` is finite-dimensional of
dimension at most `m`. -/
def LocalUpperBound (n : ℕ) (χ : RankOneCharacter) (c : HeckeCorrespondence → ℂ) (side : Side)
    (good : Bool) (m : ℕ) : Prop :=
  FiniteDimensional ℂ (localJoint n χ c side good) ∧
    Module.finrank ℂ (localJoint n χ c side good) ≤ m

/-- Local multiplicity one at a cusp: any two local joint generalized eigenclasses are
proportional to a nonzero one. -/
def LocalMultiplicityOne (n : ℕ) (χ : RankOneCharacter) (c : HeckeCorrespondence → ℂ)
    (side : Side) (good : Bool) : Prop :=
  ∀ y ∈ localJoint n χ c side good, ∀ y' ∈ localJoint n χ c side good, y ≠ 0 →
    ∃ z : ℂ, y' = z • y

/-- The Shapiro coordinates at the cusp `(side, good)` of the summand classes vanishing at the
other cusp of `side`. -/
def supportedImage (D : InducingData n) (side : Side) (good : Bool) :
    Submodule ℂ (CuspH2 n D.chi side good) :=
  (boundarySummand D side ⊓ LinearMap.ker (cuspRes n D.chi side (!good))).map
    (cuspRes n D.chi side good)

/-- **Global half.** There are `m` summand classes supported at the cusp
`(side, good)` whose Shapiro coordinates there are linearly independent. -/
def GlobalLowerBound (D : InducingData n) (side : Side) (good : Bool) (m : ℕ) : Prop :=
  ∃ s : Fin m → CuspH2 n D.chi side good,
    (∀ i, s i ∈ supportedImage D side good) ∧ LinearIndependent ℂ s

/-- Global nonvanishing at a cusp: if the local joint generalized eigenspace of the pair character
is nonzero, some summand class supported at the cusp has nonzero coordinate there. -/
def GlobalNonvanishing (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (side : Side) (good : Bool) : Prop :=
  localJoint n D.chi (pairCharacter D hecke hhecke) side good ≠ ⊥ →
    supportedImage D side good ≠ ⊥

/-- The cusp statement consumed by `CuspReduction.eigenSeparated_of_cusps`. -/
def CuspStatement (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (side : Side) (good : Bool) : Prop :=
  ∀ y ∈ localJoint n D.chi (pairCharacter D hecke hhecke) side good,
    ∃ a ∈ boundarySummand D side,
      cuspRes n D.chi side good a = y ∧ cuspRes n D.chi side (!good) a = 0

/-! ## Summand classes are local eigenclasses of the pair character -/

theorem hecke_eq_pairCharacter_smul (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (t : HeckeCorrespondence) (ht : AwayThree t)
    (side : Side) {a : StratumH2 n D.chi side} (ha : a ∈ boundarySummand D side) :
    hecke side t a = pairCharacter D hecke hhecke t • a := by
  cases side
  · have hmem : ((a, 0) : BoundaryCoordinates n D.chi) ∈ associatePair D :=
      ⟨ha, Submodule.zero_mem _⟩
    have h := congrArg Prod.fst (pairCharacter_spec D hecke hhecke t ht _ hmem)
    simpa [pairHecke] using h
  · have hmem : ((0, a) : BoundaryCoordinates n D.chi) ∈ associatePair D :=
      ⟨Submodule.zero_mem _, ha⟩
    have h := congrArg Prod.snd (pairCharacter_spec D hecke hhecke t ht _ hmem)
    simpa [pairHecke] using h

theorem cuspRes_mem_localJoint_of_mem (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (side : Side) (good : Bool)
    {a : StratumH2 n D.chi side} (ha : a ∈ boundarySummand D side) :
    cuspRes n D.chi side good a ∈ localJoint n D.chi (pairCharacter D hecke hhecke) side good := by
  simp only [localJoint, Submodule.mem_iInf, Subtype.forall]
  intro t ht
  apply Module.End.eigenspace_le_maxGenEigenspace
  rw [Module.End.mem_eigenspace_iff, ← cuspRes_hecke hecke hhecke t ht side good a,
    hecke_eq_pairCharacter_smul D hecke hhecke t ht side ha, map_smul]

theorem supportedImage_le_localJoint (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (side : Side) (good : Bool) :
    supportedImage D side good ≤ localJoint n D.chi (pairCharacter D hecke hhecke) side good := by
  rintro _ ⟨a, ⟨ha, _⟩, rfl⟩
  exact cuspRes_mem_localJoint_of_mem D hecke hhecke side good ha

theorem cuspStatement_iff (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (side : Side) (good : Bool) :
    CuspStatement D hecke hhecke side good ↔
      localJoint n D.chi (pairCharacter D hecke hhecke) side good ≤ supportedImage D side good := by
  constructor
  · intro h y hy
    obtain ⟨a, ha, hy', ha'⟩ := h y hy
    exact ⟨a, ⟨ha, ha'⟩, hy'⟩
  · intro h y hy
    obtain ⟨a, ⟨ha, ha'⟩, hy'⟩ := h hy
    exact ⟨a, ha, hy', ha'⟩

/-- The cusp statement forces equality with the supported image. -/
theorem localJoint_eq_supportedImage (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (side : Side) (good : Bool)
    (h : CuspStatement D hecke hhecke side good) :
    localJoint n D.chi (pairCharacter D hecke hhecke) side good = supportedImage D side good :=
  le_antisymm ((cuspStatement_iff D hecke hhecke side good).mp h)
    (supportedImage_le_localJoint D hecke hhecke side good)

/-! ## Combining the halves -/

theorem cuspStatement_of_bounds (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (side : Side) (good : Bool) (m : ℕ)
    (hloc : LocalUpperBound n D.chi (pairCharacter D hecke hhecke) side good m)
    (hglob : GlobalLowerBound D side good m) : CuspStatement D hecke hhecke side good := by
  obtain ⟨hfin, hdim⟩ := hloc
  obtain ⟨s, hs, hind⟩ := hglob
  rw [cuspStatement_iff]
  set L := localJoint n D.chi (pairCharacter D hecke hhecke) side good
  have hspan : Submodule.span ℂ (Set.range s) ≤ L :=
    (Submodule.span_le.mpr (Set.range_subset_iff.mpr hs)).trans
      (supportedImage_le_localJoint D hecke hhecke side good)
  have hrank : Module.finrank ℂ (Submodule.span ℂ (Set.range s)) = m := by
    rw [finrank_span_eq_card hind, Fintype.card_fin]
  have heq : Submodule.span ℂ (Set.range s) = L :=
    Submodule.eq_of_le_of_finrank_le hspan (by rw [hrank]; exact hdim)
  rw [← heq]
  exact Submodule.span_le.mpr (Set.range_subset_iff.mpr hs)

theorem cuspStatement_of_multiplicityOne (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (side : Side) (good : Bool)
    (hloc : LocalMultiplicityOne n D.chi (pairCharacter D hecke hhecke) side good)
    (hglob : GlobalNonvanishing D hecke hhecke side good) :
    CuspStatement D hecke hhecke side good := by
  rw [cuspStatement_iff]
  intro y hy
  by_cases hbot : localJoint n D.chi (pairCharacter D hecke hhecke) side good = ⊥
  · rw [hbot, Submodule.mem_bot] at hy
    rw [hy]
    exact Submodule.zero_mem _
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hglob hbot)
  obtain ⟨z, rfl⟩ := hloc x (supportedImage_le_localJoint D hecke hhecke side good hx) y hy hx0
  exact Submodule.smul_mem _ z hx

/-- **Separation from the local statements.** If at each of the four cusps the local upper bound
 and the global lower bound hold with a common multiplicity,
the associate pair is eigencharacter separated. -/
theorem eigenSeparated_of_localStatements (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (m : Side → Bool → ℕ)
    (hloc : ∀ side good,
      LocalUpperBound n D.chi (pairCharacter D hecke hhecke) side good (m side good))
    (hglob : ∀ side good, GlobalLowerBound D side good (m side good)) :
    EigenSeparated (awayThreeHeckeAlgebra D hecke) (associatePair D) :=
  eigenSeparated_of_cusps D hecke hhecke fun side good =>
    cuspStatement_of_bounds D hecke hhecke side good (m side good) (hloc side good)
      (hglob side good)

/-- **Separation from local multiplicity one and global nonvanishing** at each cusp. -/
theorem eigenSeparated_of_multiplicityOne (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hloc : ∀ side good, LocalMultiplicityOne n D.chi (pairCharacter D hecke hhecke) side good)
    (hglob : ∀ side good, GlobalNonvanishing D hecke hhecke side good) :
    EigenSeparated (awayThreeHeckeAlgebra D hecke) (associatePair D) :=
  eigenSeparated_of_cusps D hecke hhecke fun side good =>
    cuspStatement_of_multiplicityOne D hecke hhecke side good (hloc side good) (hglob side good)

/-- Mixed form: each cusp is handled by either of the two splittings. -/
theorem eigenSeparated_of_cuspStatements (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke)
    (h : ∀ side good, CuspStatement D hecke hhecke side good) :
    EigenSeparated (awayThreeHeckeAlgebra D hecke) (associatePair D) :=
  eigenSeparated_of_cusps D hecke hhecke h

end TernaryPeriodPolynomials.Separation
