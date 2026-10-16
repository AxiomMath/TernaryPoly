module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.MultiplicityFinal
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.JointEigen
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.SturmBound

@[expose] public section


/-!
# Joint generalized eigenspaces of the Hecke operators on `S_k(Γ₁(3))`

`jointGenEigenspace k c` is the joint *generalized* eigenspace of the Hecke operators `T_p`
(`p ≠ 3` prime) for the system of eigenvalues `c`. `Semisimple k` says that each `T_p` is
semisimple (generalized eigenspaces are eigenspaces); this is the output of the Petersson
self-adjointness of `T_p` at level three. Given it:

* the joint generalized eigenspace equals the joint eigenspace of `LevelThreeMultiplicity`,
  hence has dimension at most two (`finrank_jointGenEigenspace_le_two`);
* `S_k(Γ₁(3))` is spanned by joint eigenforms (`iSup_jointEigenspace_eq_top`), and a nonzero space
  of cusp forms has a joint eigenform (`exists_jointEigenform`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open scoped ModularForm

namespace TernaryPeriodPolynomials.LevelThree.LevelThreeJointGen

open TernaryPeriodPolynomials
open LevelThreeHeckeSum LevelThreeHecke LevelThreeMultiplicity

variable {k : ℤ}

/-- The joint generalized eigenspace of the Hecke operators `T_p`, `p ≠ 3`, on `S_k(Γ₁(3))`. -/
def jointGenEigenspace (k : ℤ) (eigenvalues : Nat.Primes → ℂ) :
    Submodule ℂ (CuspForm levelThree k) :=
  ⨅ p : {p : Nat.Primes // p.val ≠ 3},
    Module.End.maxGenEigenspace (levelThreeHecke k p.1 p.2) (eigenvalues p.1)

/-- Each Hecke operator `T_p` (`p ≠ 3`) on `S_k(Γ₁(3))` is semisimple: its generalized
eigenspaces are eigenspaces. -/
abbrev Semisimple (k : ℤ) : Prop :=
  ∀ (p : Nat.Primes) (hp : p.val ≠ 3) (μ : ℂ),
    Module.End.maxGenEigenspace (levelThreeHecke k p hp) μ ≤
      Module.End.eigenspace (levelThreeHecke k p hp) μ

theorem eigenspaceAwayThree_le_jointGen (eigenvalues : Nat.Primes → ℂ) :
    eigenspaceAwayThree k eigenvalues ≤ jointGenEigenspace k eigenvalues :=
  iInf_mono fun _ => Module.End.eigenspace_le_maxGenEigenspace

theorem jointGen_le_eigenspaceAwayThree (hss : Semisimple k) (eigenvalues : Nat.Primes → ℂ) :
    jointGenEigenspace k eigenvalues ≤ eigenspaceAwayThree k eigenvalues :=
  iInf_mono fun p => hss p.1 p.2 _

theorem jointGen_eq_eigenspaceAwayThree (hss : Semisimple k) (eigenvalues : Nat.Primes → ℂ) :
    jointGenEigenspace k eigenvalues = eigenspaceAwayThree k eigenvalues :=
  le_antisymm (jointGen_le_eigenspaceAwayThree hss eigenvalues)
    (eigenspaceAwayThree_le_jointGen eigenvalues)

/-- **Multiplicity at most two for the joint generalized eigenspace** (weight `k > 0`), given
semisimplicity of the Hecke operators. -/
theorem finrank_jointGenEigenspace_le_two (hk : 0 < k) (hss : Semisimple k)
    (eigenvalues : Nat.Primes → ℂ) :
    Module.finrank ℂ (jointGenEigenspace k eigenvalues) ≤ 2 := by
  rw [jointGen_eq_eigenspaceAwayThree hss]
  exact LevelThreeMultiplicityFinal.finrank_eigenspaceAwayThree_le_two_of_pos hk eigenvalues

/-- The Hecke operators `T_p`, `p ≠ 3`, commute (as elements of the endomorphism ring). -/
theorem heckeFamily_commute :
    Pairwise fun (i j : {p : Nat.Primes // p.val ≠ 3}) =>
      Commute (levelThreeHecke k i.1 i.2) (levelThreeHecke k j.1 j.2) := by
  intro i j _
  apply LinearMap.ext
  intro f
  exact levelThreeHecke_comm i.1 j.1 i.2 j.2 f

/-- **`S_k(Γ₁(3))` is the sum of the joint eigenspaces of the Hecke operators `T_p`**,
`p ≠ 3` (given semisimplicity). -/
theorem iSup_jointEigenspace_eq_top (hss : Semisimple k) :
    ⨆ χ : {p : Nat.Primes // p.val ≠ 3} → ℂ,
      ⨅ i : {p : Nat.Primes // p.val ≠ 3},
        Module.End.eigenspace (levelThreeHecke k i.1 i.2) (χ i) = ⊤ := by
  have := SturmBound.cuspForm_finiteDimensional k
  exact JointEigen.iSup_iInf_eigenspace_eq_top _ heckeFamily_commute fun i μ => hss i.1 i.2 μ

/-- **Existence of a joint eigenform**: if `S_k(Γ₁(3)) ≠ 0` there is a nonzero cusp form which is
an eigenvector of every `T_p`, `p ≠ 3`. -/
theorem exists_jointEigenform (hss : Semisimple k) [Nontrivial (CuspForm levelThree k)] :
    ∃ (χ : {p : Nat.Primes // p.val ≠ 3} → ℂ) (f : CuspForm levelThree k), f ≠ 0 ∧
      ∀ i : {p : Nat.Primes // p.val ≠ 3}, levelThreeHecke k i.1 i.2 f = χ i • f := by
  have := SturmBound.cuspForm_finiteDimensional k
  exact JointEigen.exists_joint_eigenvector _ heckeFamily_commute fun i μ => hss i.1 i.2 μ

end TernaryPeriodPolynomials.LevelThree.LevelThreeJointGen
