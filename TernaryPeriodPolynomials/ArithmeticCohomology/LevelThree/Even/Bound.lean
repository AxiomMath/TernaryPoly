module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Good.PlaneBoundExport
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Bad.LineUpper
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.MultiplicityFinal
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.JointGen
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Source.Cases

@[expose] public section


/-!
# The local upper bound `1` at the level-three cusps for even `n`

For even `n` the weight `k = n + 3` of the cusp forms of level `Γ₁(3)` carrying the Eichler–Shimura
image is odd. There are no level-one oldforms in odd weight (`S_k(SL₂ℤ) = 0`), so the joint
eigenspace of the Hecke operators `T_p` (`p ≠ 3`) on `S_k(Γ₁(3))` has dimension at most one
(`LevelThreeMultiplicity.finrank_eigenspaceAwayThree_le_one_of_odd`) instead of two.

This file repeats the bound chain of the good plane (`GoodPlaneBoundTwo`, `GoodPlaneBoundExport`)
and of the bad line (`BadLineBound`, `BadLineUpper`) with the final multiplicity bound `2`
replaced by `1`, for the trivial character, given injectivity of the parity-projected period maps
`levelPeriodMap (n + 1) (-1)` and `levelPeriodMap (n + 1) 0`. It then packages the bound `1` as the
oldform-classes statement `LevelThreeOldformClasses` (a local joint eigenspace of dimension `2` is
impossible) and as the local bound `2` consumed by the rank split.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.EvenLevelThree

/-! ### Odd weight: multiplicity at most one -/

section Multiplicity

open TernaryPeriodPolynomials.LevelThree

/-- For even `n`, the weight `(n + 1) + 2` of the level-three period map is odd. -/
theorem odd_weight_of_even (n : ℕ) (heven : Even n) : Odd (((n + 1 : ℕ) : ℤ) + 2) := by
  obtain ⟨m, hm⟩ := heven
  exact ⟨(m : ℤ) + 1, by omega⟩

/-- **Multiplicity at most one for the joint generalized eigenspace in odd weight**, given
semisimplicity of the Hecke operators. -/
theorem finrank_jointGenEigenspace_le_one_of_odd {k : ℤ} (hk : Odd k)
    (hss : LevelThreeJointGen.Semisimple k) (eigenvalues : Nat.Primes → ℂ) :
    Module.finrank ℂ (LevelThreeJointGen.jointGenEigenspace k eigenvalues) ≤ 1 := by
  rw [LevelThreeJointGen.jointGen_eq_eigenspaceAwayThree hss]
  exact LevelThreeMultiplicity.finrank_eigenspaceAwayThree_le_one_of_odd hk eigenvalues

end Multiplicity

/-! ### The good plane -/

section GoodPlane

open GeneralEisenstein

open TernaryPeriodPolynomials.LevelThree
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.LevelThree.GoodPlaneJoint (levelJoint)
open TernaryPeriodPolynomials.LevelThree.LevelThreeBoundaryEisenstein (two)
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodCocycle (S)
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodParity (levelPeriodMap)
open TernaryPeriodPolynomials.LevelThree.LevelThreeHeckeH1 (levelHecke)
open TernaryPeriodPolynomials.LevelThree.LevelThreeHecke (levelThreeHecke)

/-- **`dim levelJoint ≤ 1` for even `n`**, given injectivity of the parity-projected period map. -/
theorem finrank_levelJoint_le_one_of_even (n : ℕ) (hn : 1 ≤ n) (heven : Even n)
    (c : HeckeCorrespondence → ℂ)
    (hc : ‖c (TpExistence.tp two) - 1‖ ≤ 3 / 4)
    (hinj : Function.Injective (levelPeriodMap (n + 1) (-1))) :
    Module.finrank ℂ (levelJoint n c) ≤ 1 := by
  have hm : 0 < n + 1 := Nat.succ_pos n
  have hrange := LevelThreePeriodDimension.levelPeriodMap_range_eq_parabolic_of_injective
    (m := n + 1) (e := -1) hm hinj
  have hJR : levelJoint n c ≤ LinearMap.range (levelPeriodMap (n + 1) (-1)) := by
    rw [hrange]
    exact GoodPlaneBound.levelJoint_le_parabolic n hn c hc
  have : Module.Finite ℂ (S (n + 1)) :=
    SturmBound.cuspForm_finiteDimensional (((n + 1 : ℕ) : ℤ) + 2)
  let μ : {p : Nat.Primes // p.val ≠ 3} → ℂ := fun p =>
    (c (TpExistence.tp p.1) - 1) / ((p.1.val : ℂ) ^ (n + 2))⁻¹
  have h1 := GoodPlaneBound.finrank_le_of_injective_equivariant (levelPeriodMap (n + 1) (-1)) hinj
    (fun p : {p : Nat.Primes // p.val ≠ 3} =>
      (((p.1.val : ℂ) ^ (-(-1 : ℤ))) • levelThreeHecke (((n + 1 : ℕ) : ℤ) + 2) p.1 p.2 :
        Module.End ℂ (S (n + 1))))
    (fun p => levelHecke (n + 1) (-1) p.1 p.2)
    (fun p f => (LevelThreePeriodParityHecke.levelHecke_levelPeriodMap (-1) p.1 p.2 hm f).symm)
    μ (levelJoint n c) le_rfl hJR
  refine h1.trans ?_
  have h2 : (⨅ p : {p : Nat.Primes // p.val ≠ 3},
      Module.End.maxGenEigenspace
        (((p.1.val : ℂ) ^ (-(-1 : ℤ))) • levelThreeHecke (((n + 1 : ℕ) : ℤ) + 2) p.1 p.2 :
          Module.End ℂ (S (n + 1))) (μ p) : Submodule ℂ (S (n + 1))) ≤
      LevelThreeJointGen.jointGenEigenspace (((n + 1 : ℕ) : ℤ) + 2)
        (fun q => (c (TpExistence.tp q) - 1) / ((q.val : ℂ) ^ (n + 2))⁻¹ /
          ((q.val : ℂ) ^ (-(-1 : ℤ)))) := by
    refine iInf_mono (fun p => ?_)
    have hp : ((p.1.val : ℂ) ^ (-(-1 : ℤ))) ≠ 0 := by
      rw [neg_neg, zpow_one]
      exact_mod_cast p.1.property.ne_zero
    exact fun f hf => GoodPlaneBound.mem_maxGen_of_smul _ _ _ hp hf
  have h3 := finrank_jointGenEigenspace_le_one_of_odd (odd_weight_of_even n heven)
    (LevelThreePeterssonSemisimple.levelThree_semisimple (((n + 1 : ℕ) : ℤ) + 2))
    (fun q => (c (TpExistence.tp q) - 1) / ((q.val : ℂ) ^ (n + 2))⁻¹ /
      ((q.val : ℂ) ^ (-(-1 : ℤ))))
  exact (Submodule.finrank_mono h2).trans h3

/-- **The local upper bound `1` at the good plane for even `n`** (trivial character), given
injectivity of the parity-projected period map. -/
theorem localUpperBound_one_of_even (n : ℕ) (hn : 1 ≤ n) (heven : Even n)
    (c : HeckeCorrespondence → ℂ)
    (hc : ‖c (TpExistence.tp two) - 1‖ ≤ 3 / 4)
    (hinj : Function.Injective (levelPeriodMap (n + 1) (-1))) :
    Separation.LocalUpperBound n trivialCharacter c .plane true 1 :=
  GoodPlaneJoint.localUpperBound_of_levelJoint n (by omega) c 1
    (finrank_levelJoint_le_one_of_even n hn heven c hc hinj)

end GoodPlane

/-! ### The good plane for the pair character -/

section GoodPlaneExport

open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SpectralSeparation
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspReduction

open TernaryPeriodPolynomials.Separation
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodParity (levelPeriodMap)

/-- **Local upper bound `1` at the good plane for the pair character** (`D.chi` trivial, `3 ≤ n`
even, nonzero pair), given injectivity of the parity-projected period map. -/
theorem localUpperBound_goodPlane_one_of_even_trivial {n : ℕ} (hn : 3 ≤ n) (heven : Even n)
    (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hχ : D.chi = trivialCharacter) (hne : associatePair D ≠ ⊥)
    (hinj : Function.Injective (levelPeriodMap (n + 1) (-1))) :
    LocalUpperBound n D.chi (pairCharacter D hecke hhecke) .plane true 1 := by
  have hc := pairCharacter_two_sub_one_norm_le_of_trivial D hχ hecke hhecke hn hne
  have key := localUpperBound_one_of_even n (by omega) heven
    (pairCharacter D hecke hhecke) hc hinj
  rw [← hχ] at key
  exact key

end GoodPlaneExport

/-! ### The bad line -/

section BadLine

open Module
open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SpectralSeparation
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic
open Helpers ArithmeticGenerators

open TernaryPeriodPolynomials.Separation
open TernaryPeriodPolynomials.LevelThree
open BadLineLocal LevelThreeHeckeH1 LevelThreeCosets IdentityPlaneCosets
open TernaryPeriodPolynomials.LevelThree.BadLineBound

variable {n : ℕ}

/-- **The local upper bound `1` at the bad line, from the period data.** The twin of
`BadLineBound.localUpperBound_badLine_two_of_period` for joint generalized eigenspaces of
dimension at most one. -/
theorem localUpperBound_badLine_one_of_period (hn : 3 ≤ n) (c : HeckeCorrespondence → ℂ)
    (hc : ‖c (TpExistence.tp LocalUniqueness.two) - 1‖ ≤ 3 / 4)
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (U : Away → Module.End ℂ V) (Φ : V →ₗ[ℂ] CrossedH1 (binaryArithmeticRepresentation n))
    (hΦ : Function.Injective Φ)
    (hint : ∀ (p : Away) (v : V), badLevelHecke p.1 p.2 n (Φ v) = Φ (U p v))
    (hrange : LinearMap.range Φ =
      TwoGenerator.parabolicH1 (ParabolicBounds.levelRep (n + 1) 0) (upper 1) (lower 1))
    (hbound : ∀ eig : Nat.Primes → ℂ,
      finrank ℂ (⨅ p : Away, (U p).maxGenEigenspace (eig p.1) : Submodule ℂ V) ≤ 1) :
    Separation.LocalUpperBound n trivialCharacter c .line false 1 := by
  have hn0 : 0 < n := by omega
  have h2 : LocalUniqueness.two.val ≠ 3 := by decide
  have hH : FiniteDimensional ℂ (CrossedH1 (binaryArithmeticRepresentation n)) :=
    ParabolicBounds.level_H1_finiteDimensional 0 (Nat.succ_pos n)
  have hβ : ∀ p : Away, ((p.1.val : ℂ) ^ (n + 1))⁻¹ ≠ 0 := fun p =>
    inv_ne_zero (pow_ne_zero _ (by exact_mod_cast p.1.property.ne_zero))
  have hne' := ne_qInf_qZero_two (n := n) (by omega) (c (TpExistence.tp LocalUniqueness.two)) hc
  exact LocalChain.local_bound (fun p : Away => tpOp n p) (badLineLocalRadicalKernel n)
    (fun p : Away => badLevelHecke p.1 p.2 n) U (BadLineFinal.badLineEdge n hn0) Φ
    (fun _ => (1 : ℂ)) (fun p => ((p.1.val : ℂ) ^ (n + 1))⁻¹) (fun _ => (1 : ℂ))
    (fun p => BadLineRestriction.lamB n p.1)
    (fun p => LevelThreeBoundaryHecke.qInf (n + 1) 0 p.1)
    (fun p => c (TpExistence.tp p.1))
    (fun p y hy => BadLineFinal.badLine_localOp_mem_kernel n p.1 p.2 y hy)
    (fun p y => by
      have h := badLineEdge_localOp n hn0 p.1 p.2 y
      rw [one_smul]
      exact h)
    hβ (BadLineFinal.badLineEdge_injective n hn0) ⟨LocalUniqueness.two, h2⟩
    (fun y => BadLineRestriction.badLine_localOp_sub_mem_kernel n hn0 LocalUniqueness.two h2 y)
    (ne_lamB_of_norm_le n LocalUniqueness.two _ hc) (fun _ => one_ne_zero) hΦ
    (fun p v => by rw [one_smul]; exact hint p v) ⟨LocalUniqueness.two, h2⟩
    (fun y => by
      rw [hrange]
      exact LevelThreeBoundaryEisenstein.badLevelHecke_sub_mem_parabolic n LocalUniqueness.two
        h2 y)
    hne'.1 1
    (hbound (fun q => (c (TpExistence.tp q) - 1) / ((q.val : ℂ) ^ (n + 1))⁻¹ / 1))
    (localJoint n trivialCharacter c .line false)
    (localJoint_le_iInf n c)

end BadLine

section BadLineEven

open GeneralEisenstein

open TernaryPeriodPolynomials.LevelThree
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodCocycle (S)
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodParity (levelPeriodMap)
open TernaryPeriodPolynomials.LevelThree.LevelThreeHecke (levelThreeHecke)

/-- **The local upper bound `1` at the bad line for even `n`** (trivial character, `3 ≤ n`), given
injectivity of the parity-projected period map `levelPeriodMap (n + 1) 0`. -/
theorem localUpperBound_badLine_one_of_even (n : ℕ) (hn : 3 ≤ n) (heven : Even n)
    (c : HeckeCorrespondence → ℂ)
    (hc : ‖c (TpExistence.tp LocalUniqueness.two) - 1‖ ≤ 3 / 4)
    (hinj : Function.Injective (levelPeriodMap (n + 1) 0)) :
    Separation.LocalUpperBound n trivialCharacter c .line false 1 := by
  have hm : 0 < n + 1 := Nat.succ_pos n
  have : FiniteDimensional ℂ (S (n + 1)) :=
    SturmBound.cuspForm_finiteDimensional (((n + 1 : ℕ) : ℤ) + 2)
  have hrange := LevelThreePeriodDimension.levelPeriodMap_range_eq_parabolic_of_injective
    (m := n + 1) (e := 0) hm hinj
  exact localUpperBound_badLine_one_of_period hn c hc
    (fun p : BadLineBound.Away => levelThreeHecke (((n + 1 : ℕ) : ℤ) + 2) p.1 p.2)
    (levelPeriodMap (n + 1) 0) hinj
    (fun p v => by
      have h := LevelThreePeriodParityHecke.levelHecke_levelPeriodMap (m := n + 1) 0 p.1 p.2 hm v
      rw [neg_zero, zpow_zero, one_smul] at h
      exact h)
    hrange
    (fun eig => finrank_jointGenEigenspace_le_one_of_odd (odd_weight_of_even n heven)
      (LevelThreePeterssonSemisimple.levelThree_semisimple (((n + 1 : ℕ) : ℤ) + 2)) eig)

end BadLineEven

/-! ### The bad line for the pair character -/

section BadLineExport

open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SpectralSeparation
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspReduction

open TernaryPeriodPolynomials.Separation
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodParity (levelPeriodMap)

/-- **Local upper bound `1` at the bad line for the pair character** (`D.chi` trivial, `3 ≤ n`
even, nonzero pair), given injectivity of the parity-projected period map
`levelPeriodMap (n + 1) 0`. -/
theorem localUpperBound_badLine_one_of_even_trivial {n : ℕ} (hn : 3 ≤ n) (heven : Even n)
    (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hχ : D.chi = trivialCharacter) (hne : associatePair D ≠ ⊥)
    (hinj : Function.Injective (levelPeriodMap (n + 1) 0)) :
    LocalUpperBound n D.chi (pairCharacter D hecke hhecke) .line false 1 := by
  have hc := pairCharacter_two_sub_one_norm_le_of_trivial D hχ hecke hhecke hn hne
  have key := localUpperBound_badLine_one_of_even n hn heven
    (pairCharacter D hecke hhecke) hc hinj
  rw [← hχ] at key
  exact key

end BadLineExport

/-! ### The oldform classes and the bound `2` for even `n` -/

section Oldform

open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SpectralSeparation
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.SourceSpace
open TernaryPeriodPolynomials.Separation
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodParity (levelPeriodMap)

variable {n : ℕ}

/-- The local upper bound `1` implies the local upper bound `2`. -/
theorem localUpperBound_two_of_one {χ : RankOneCharacter} {c : HeckeCorrespondence → ℂ}
    {side : Side} {good : Bool} (h : LocalUpperBound n χ c side good 1) :
    LocalUpperBound n χ c side good 2 :=
  ⟨h.1, h.2.trans (by norm_num)⟩

/-- **The oldform classes from the local bound `1`**: a local joint eigenspace of dimension at most
one cannot have dimension two, so the statement about two classes is vacuous. -/
theorem levelThreeOldformClasses_of_localUpperBound_one (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke) (side : Side)
    (good : Bool)
    (hbound1 : associatePair D ≠ ⊥ →
      LocalUpperBound n D.chi (pairCharacter D hecke hhecke) side good 1) :
    TernaryPeriodPolynomials.LevelThreeSource.LevelThreeOldformClasses
      D hecke hhecke side good := by
  intro hne _ h2
  have h1 := (hbound1 hne).2
  exact absurd h2 (by omega)

/-- **The oldform classes at the good plane for even `n`** (trivial character). -/
theorem levelThreeOldformClasses_goodPlane_of_even (hn : 3 ≤ n) (heven : Even n)
    (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (hχ : D.chi = trivialCharacter)
    (hinj : Function.Injective (levelPeriodMap (n + 1) (-1))) :
    TernaryPeriodPolynomials.LevelThreeSource.LevelThreeOldformClasses
      D hecke hhecke .plane true :=
  levelThreeOldformClasses_of_localUpperBound_one D hecke hhecke .plane true fun hne =>
    localUpperBound_goodPlane_one_of_even_trivial hn heven D hecke hhecke hχ hne hinj

/-- **The oldform classes at the bad line for even `n`** (trivial character). -/
theorem levelThreeOldformClasses_badLine_of_even (hn : 3 ≤ n) (heven : Even n)
    (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (hχ : D.chi = trivialCharacter)
    (hinj : Function.Injective (levelPeriodMap (n + 1) 0)) :
    TernaryPeriodPolynomials.LevelThreeSource.LevelThreeOldformClasses
      D hecke hhecke .line false :=
  levelThreeOldformClasses_of_localUpperBound_one D hecke hhecke .line false fun hne =>
    localUpperBound_badLine_one_of_even_trivial hn heven D hecke hhecke hχ hne hinj

/-- **The local upper bound `2` at the good plane for even `n`** (trivial character), in the form
consumed by the rank split. -/
theorem levelThreeLocalUpperBound_two_of_even_goodPlane (hn : 3 ≤ n) (heven : Even n)
    (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (hχ : D.chi = trivialCharacter)
    (hinj : Function.Injective (levelPeriodMap (n + 1) (-1))) :
    associatePair D ≠ ⊥ →
      LocalUpperBound n D.chi (pairCharacter D hecke hhecke) .plane true 2 :=
  fun hne => localUpperBound_two_of_one
    (localUpperBound_goodPlane_one_of_even_trivial hn heven D hecke hhecke hχ hne hinj)

/-- **The local upper bound `2` at the bad line for even `n`** (trivial character), in the form
consumed by the rank split. -/
theorem levelThreeLocalUpperBound_two_of_even_badLine (hn : 3 ≤ n) (heven : Even n)
    (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (hχ : D.chi = trivialCharacter)
    (hinj : Function.Injective (levelPeriodMap (n + 1) 0)) :
    associatePair D ≠ ⊥ →
      LocalUpperBound n D.chi (pairCharacter D hecke hhecke) .line false 2 :=
  fun hne => localUpperBound_two_of_one
    (localUpperBound_badLine_one_of_even_trivial hn heven D hecke hhecke hχ hne hinj)

end Oldform

end TernaryPeriodPolynomials.EvenLevelThree
