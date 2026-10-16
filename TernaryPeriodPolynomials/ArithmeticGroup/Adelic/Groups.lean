module

public import TernaryPeriodPolynomials.ArithmeticGroup.Adelic.Levi
public import TernaryPeriodPolynomials.ArithmeticGroup.Adelic.Three
public import TernaryPeriodPolynomials.ArithmeticGroup.Adelic.Norm
public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs.Arithmetic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM

@[expose] public section


noncomputable section
namespace GeneralEisenstein.Adelic
open Matrix
open scoped Matrix.Norms.Elementwise

def pairMatrix {m : ℕ} (r : Matrix (Fin m) (Fin m) ℝ) (f : Matrix (Fin m) (Fin m) FiniteAdeles) :
    Matrix (Fin m) (Fin m) Adeles := fun i j => (r i j, f i j)

def combineGL {m : ℕ} (r : GeneralLinearGroup (Fin m) ℝ) (f : GeneralLinearGroup (Fin m) FiniteAdeles) : GeneralLinearGroup (Fin m) Adeles where
  val := pairMatrix r.val f.val
  inv := pairMatrix r⁻¹.val f⁻¹.val
  val_inv := by
    apply Matrix.ext
    intro i j
    apply Prod.ext
    · simpa only [Matrix.mul_apply, pairMatrix, Matrix.one_apply, apply_ite, Prod.fst_sum, Prod.fst_mul, Prod.fst_one, Prod.fst_zero] using congrArg (fun A : Matrix (Fin m) (Fin m) ℝ => A i j) r.mul_inv
    · simpa only [Matrix.mul_apply, pairMatrix, Matrix.one_apply, apply_ite, Prod.snd_sum, Prod.snd_mul, Prod.snd_one, Prod.snd_zero] using congrArg (fun A : Matrix (Fin m) (Fin m) FiniteAdeles => A i j) f.mul_inv
  inv_val := by
    apply Matrix.ext
    intro i j
    apply Prod.ext
    · simpa only [Matrix.mul_apply, pairMatrix, Matrix.one_apply, apply_ite, Prod.fst_sum, Prod.fst_mul, Prod.fst_one, Prod.fst_zero] using congrArg (fun A : Matrix (Fin m) (Fin m) ℝ => A i j) r.inv_mul
    · simpa only [Matrix.mul_apply, pairMatrix, Matrix.one_apply, apply_ite, Prod.snd_sum, Prod.snd_mul, Prod.snd_one, Prod.snd_zero] using congrArg (fun A : Matrix (Fin m) (Fin m) FiniteAdeles => A i j) f.inv_mul


/-- Real and finite inclusions have identity in the other factor. -/
def atInfinity {m : ℕ} (g : GeneralLinearGroup (Fin m) ℝ) := combineGL g 1

def atFinite {m : ℕ} (g : GeneralLinearGroup (Fin m) FiniteAdeles) := combineGL 1 g

/-- The actual finite compact subgroup, maximal away from three. -/
def finiteLevel : Subgroup (GeneralLinearGroup (Fin 3) FiniteAdeles) :=
  ((GeneralEisenstein.rowStabilizer).comap (GeneralLinearGroup.map integralReduction)).map
    (GeneralLinearGroup.map integralEmbedding)

/-- Maximal compact in the full adelic group. -/
def inMaximalCompact (g : AdelicGL) : Prop :=
  (realGroup g).val.transpose * (realGroup g).val = 1 ∧
  finiteGroup g ∈ Set.range (GeneralLinearGroup.map integralEmbedding)

/-- Total extension used only on the open set of invertible real matrices. -/
def invertibleMatrix {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) :
    GeneralLinearGroup (Fin m) ℝ :=
  if h : A.det ≠ 0 then GeneralLinearGroup.mkOfDetNeZero A h else 1

/-- Ordinary C-infinity on the open matrix manifold GL_m(R)^k. -/
def Smooth {m k : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : (Fin k → GeneralLinearGroup (Fin m) ℝ) → E) : Prop :=
  ContDiffOn ℝ ⊤ (fun A : Fin k → Matrix (Fin m) (Fin m) ℝ => f (fun i => invertibleMatrix (A i)))
    {A | ∀ i, (A i).det ≠ 0}

/-- The standard additive unipotent of GL_2. -/
def binaryUnipotent {R : Type*} [CommRing R] (a : R) : GeneralLinearGroup (Fin 2) R :=
  ⟨!![1,a;0,1],!![1,-a;0,1], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_two], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_two]⟩

/-- A fixed fundamental domain for A/Q, of additive volume one. -/
def additiveDomain : Set Adeles := Set.Ico 0 1 ×ˢ Set.range integralEmbedding

end GeneralEisenstein.Adelic

end
