module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Hecke.Arithmetic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Index

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryHeckeArithmetic
open Matrix PolynomialGLAction ModThreeGoodAction

/-- Entrywise extension of scalars as an actual ring homomorphism. -/
def matrixCast : Matrix (Fin 3) (Fin 3) ℤ →+* Matrix (Fin 3) (Fin 3) ℚ :=
  (Int.castRingHom ℚ).mapMatrix

@[simp] theorem matrixCast_apply (M : Matrix (Fin 3) (Fin 3) ℤ) (i j : Fin 3) :
    matrixCast M i j=(M i j : ℚ) := rfl

theorem integralEntries_iff_matrix (M : Matrix (Fin 3) (Fin 3) ℚ) :
    IntegralEntries M ↔ ∃ A, matrixCast A=M := by
  constructor
  · intro h
    choose a ha using h
    exact ⟨a,by ext i j; exact ha i j⟩
  · rintro ⟨A,rfl⟩
    exact fun i j => ⟨A i j,rfl⟩

/-- A finite family of rational numbers has an explicit nonzero common denominator. -/
theorem finite_denominator {ι : Type} [Fintype ι] (f : ι → ℚ) :
    ∃ d : ℕ, d ≠ 0 ∧ ∀ i, ∃ z : ℤ, (z : ℚ)=(d : ℚ)*f i := by
  classical
  let d := ∏ i, (f i).den
  refine ⟨d,Finset.prod_ne_zero_iff.mpr (fun i _ => (f i).den_ne_zero),?_⟩
  intro i
  obtain ⟨k,hk⟩ := Finset.dvd_prod_of_mem (fun i => (f i).den) (Finset.mem_univ i)
  refine ⟨(k : ℤ)*(f i).num,?_⟩
  change _=(∏ i, (f i).den : ℕ)*f i
  rw [hk,Nat.cast_mul,Int.cast_mul,Int.cast_natCast]
  rw [mul_right_comm, Rat.den_mul_eq_num,mul_comm]

/-- A rational matrix can be cleared by one nonzero natural denominator. -/
theorem matrix_denominator (M : Matrix (Fin 3) (Fin 3) ℚ) :
    ∃ d : ℕ, d ≠ 0 ∧ ∃ A : Matrix (Fin 3) (Fin 3) ℤ, matrixCast A=(d : ℚ) • M := by
  obtain ⟨d,hd,h⟩ := finite_denominator (fun ij : Fin 3 × Fin 3 => M ij.1 ij.2)
  choose a ha using h
  exact ⟨d,hd,(fun i j => a (i,j)),by ext i j; exact ha (i,j)⟩

/-- The actual finite congruence quotient of integral GL3. -/
def congruenceMap (m : ℕ) : IntegralGL →* GeneralLinearGroup (Fin 3) (ZMod m) :=
  GeneralLinearGroup.map (Int.castRingHom (ZMod m))

/-- Congruence to identity gives a literal integer-matrix multiple of the modulus. -/
theorem congruence_matrix (m : ℕ) (k : IntegralGL) (hk : congruenceMap m k=1) :
    ∃ Z : Matrix (Fin 3) (Fin 3) ℤ, k.val=1+(m : ℤ) • Z := by
  have hentry (i j : Fin 3) : (m : ℤ) ∣ (k.val-1) i j := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).mp
    have he := congrArg (fun x : GeneralLinearGroup (Fin 3) (ZMod m) => x.val i j) hk
    change (k.val i j : ZMod m)=(1 : Matrix (Fin 3) (Fin 3) (ZMod m)) i j at he
    change ((k.val i j-(1 : Matrix (Fin 3) (Fin 3) ℤ) i j : ℤ) : ZMod m)=0
    rw [Int.cast_sub,he]
    simp [Matrix.one_apply]
  choose z hz using hentry
  refine ⟨z,?_⟩
  ext i j
  have he := hz i j
  change k.val i j-(1 : Matrix (Fin 3) (Fin 3) ℤ) i j=m*z i j at he
  change k.val i j=(1 : Matrix (Fin 3) (Fin 3) ℤ) i j+m*z i j
  omega

end TernaryPoly.OrdinaryHeckeArithmetic
