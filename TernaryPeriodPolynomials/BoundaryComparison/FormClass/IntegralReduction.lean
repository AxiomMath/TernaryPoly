module

public import TernaryPeriodPolynomials.ArithmeticGroup.Adelic.Three
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

@[expose] public section


/-!
# Reduction modulo `N` on the integral adeles `Ẑ` and on `GL_n(Ẑ)`, and the level subgroup `K(N)`

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.IntegralReduction

open GeneralEisenstein.Adelic

/-- The reduction `Ẑ → ℤ_p → ℤ/p^e` at the prime `p`. -/
def primeReduction (p : Nat.Primes) (e : ℕ) : IntegralAdeles →+* ZMod (p ^ e) :=
  haveI : Fact (Nat.Prime (p : ℕ)) := ⟨p.2⟩
  (PadicInt.toZModPow e).comp
    ((@AlgEquiv.toRingEquiv _ _ _ _ _ _ _ (Ring.toIntAlgebra _)
      (@ContinuousAlgEquiv.toAlgEquiv _ _ _ _ _ _ _ _ _ (Ring.toIntAlgebra _)
        (PadicInt.adicCompletionIntegersEquiv ℤ p))).symm.toRingHom.comp
      (Pi.evalRingHom _ (Rat.HeightOneSpectrum.primesEquiv.symm p)))


/-- **Reduction modulo `N` on `Ẑ = ∏_v O_v`**: the Chinese remainder theorem over the primes dividing `N`, `Ẑ → ∏_{p ∣ N} ℤ/p^{v_p(N)} ≅ ℤ/N`. -/
def integralReductionN (N : ℕ) [NeZero N] : IntegralAdeles →+* ZMod N :=
  (ZMod.equivPi (n := N) (NeZero.ne N)).symm.toRingHom.comp
    (RingHom.pi fun p : N.primeFactors => primeReduction ⟨p.1, Nat.prime_of_mem_primeFactors p.2⟩ (N.factorization p.1))

variable (N : ℕ) [NeZero N]

@[simp] theorem integralReductionN_int (z : ℤ) : integralReductionN N (z : IntegralAdeles) = z :=
  map_intCast (integralReductionN N) z

@[simp] theorem integralReductionN_nat (m : ℕ) : integralReductionN N (m : IntegralAdeles) = m :=
  map_natCast (integralReductionN N) m

theorem integralReductionN_comp_intCast :
    (integralReductionN N).comp (Int.castRingHom IntegralAdeles) = Int.castRingHom (ZMod N) :=
  RingHom.ext_int _ _

theorem integralReductionN_surjective : Function.Surjective (integralReductionN N) := fun a => by
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective a
  exact ⟨(z : IntegralAdeles), integralReductionN_int N z⟩

/-- Reduction modulo `N` of `GL_n(Ẑ)`. -/
abbrev reductionGL (n : ℕ) : Matrix.GeneralLinearGroup (Fin n) IntegralAdeles →* Matrix.GeneralLinearGroup (Fin n) (ZMod N) :=
  Matrix.GeneralLinearGroup.map (integralReductionN N)

/-- **The principal congruence subgroup `K(N) ≤ GL_n(Ẑ)`**: the kernel of the reduction modulo `N`. -/
def levelKernel (n : ℕ) : Subgroup (Matrix.GeneralLinearGroup (Fin n) IntegralAdeles) :=
  (reductionGL N n).ker

instance levelKernel_normal (n : ℕ) : (levelKernel N n).Normal := MonoidHom.normal_ker _

theorem mem_levelKernel_iff {n : ℕ} (g : Matrix.GeneralLinearGroup (Fin n) IntegralAdeles) :
    g ∈ levelKernel N n ↔ ∀ i j, integralReductionN N ((g : Matrix (Fin n) (Fin n) IntegralAdeles) i j) =
      (1 : Matrix (Fin n) (Fin n) (ZMod N)) i j := by
  constructor
  · intro h i j
    have := congrArg (fun x : Matrix.GeneralLinearGroup (Fin n) (ZMod N) => (x : Matrix (Fin n) (Fin n) (ZMod N)) i j)
      (MonoidHom.mem_ker.mp h)
    exact this
  · intro h
    refine MonoidHom.mem_ker.mpr (Units.ext ?_)
    ext i j
    exact h i j

/-- The reduction of the image of an integer matrix is the integer matrix modulo `N`. -/
theorem reductionGL_map_intCast {n : ℕ} (γ : Matrix.GeneralLinearGroup (Fin n) ℤ) :
    reductionGL N n (Matrix.GeneralLinearGroup.map (Int.castRingHom IntegralAdeles) γ) =
      Matrix.GeneralLinearGroup.map (Int.castRingHom (ZMod N)) γ := by
  rw [← MonoidHom.comp_apply, ← Matrix.GeneralLinearGroup.map_comp, integralReductionN_comp_intCast]

theorem reductionGL_mapGL {n : ℕ} (γ : Matrix.SpecialLinearGroup (Fin n) ℤ) :
    reductionGL N n (Matrix.SpecialLinearGroup.mapGL IntegralAdeles γ) =
      Matrix.SpecialLinearGroup.mapGL (ZMod N) γ := by
  apply Units.ext
  ext i j
  simp [reductionGL, Matrix.GeneralLinearGroup.map_apply, Matrix.SpecialLinearGroup.mapGL_coe_matrix]

theorem mapGL_mem_levelKernel_iff {n : ℕ} (γ : Matrix.SpecialLinearGroup (Fin n) ℤ) :
    Matrix.SpecialLinearGroup.mapGL IntegralAdeles γ ∈ levelKernel N n ↔
      Matrix.SpecialLinearGroup.mapGL (ZMod N) γ = 1 := by
  unfold levelKernel
  rw [MonoidHom.mem_ker, reductionGL_mapGL]

end TernaryPeriodPolynomials.Argument.IntegralReduction
