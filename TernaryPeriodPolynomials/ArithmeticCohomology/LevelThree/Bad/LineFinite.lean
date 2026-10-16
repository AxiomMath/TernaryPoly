module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.LocalInterface
public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.Assembly

@[expose] public section


/-!
# Local finiteness at the bad line of level three

`Separation.LocalJointFinite D hecke hhecke .line false` asks, for a nonzero associate
pair, for some bound `m` on the local joint generalized eigenspace of the pair character at the
bad-line cusp. The local cohomology `H²(Γ_F, V)` at any cusp is finite-dimensional
(`LocalInterface.cuspH2_finiteDimensional`: it is a retract of the finite-dimensional boundary
stratum), and the local joint generalized eigenspace is a subspace of it, so
`m = dim (localJoint …)` works. No Hecke computation is needed for finiteness itself.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SpectralSeparation
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspReduction

namespace TernaryPeriodPolynomials.LevelThree.BadLineFinite

open TernaryPeriodPolynomials.Separation

variable {n : ℕ}

/-- **Local finiteness at every cusp**: the local joint generalized eigenspace is a subspace of the
finite-dimensional local cohomology, so it is bounded by its own dimension. -/
theorem localJointFinite_of_cuspH2 (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (side : Side) (good : Bool) :
    LocalJointFinite D hecke hhecke side good := by
  intro _
  have hfin : FiniteDimensional ℂ (CuspH2 n D.chi side good) :=
    LocalInterface.cuspH2_finiteDimensional D.chi side good
  refine ⟨Module.finrank ℂ (localJoint n D.chi (pairCharacter D hecke hhecke) side good), ?_⟩
  unfold LocalUpperBound
  exact ⟨Module.Finite.of_injective (Submodule.subtype _) (Submodule.injective_subtype _),
    le_rfl⟩

/-- **Local finiteness at the bad line** (any character, any degree). -/
theorem localJointFinite_badLine (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) : LocalJointFinite D hecke hhecke .line false :=
  localJointFinite_of_cuspH2 D hecke hhecke .line false

/-- **Local finiteness at the bad line for the trivial character** (`3 ≤ n`): the exact
`LocalJointFinite` input of `eigenSeparated_of_openInputs`. -/
theorem localJointFinite_badLine_of_trivial (_hn : 3 ≤ n) (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (_hχ : D.chi = trivialCharacter) : LocalJointFinite D hecke hhecke .line false :=
  localJointFinite_badLine D hecke hhecke

end TernaryPeriodPolynomials.LevelThree.BadLineFinite
