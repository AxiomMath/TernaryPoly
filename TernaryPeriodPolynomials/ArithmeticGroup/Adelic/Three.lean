module

public import TernaryPeriodPolynomials.ArithmeticGroup.Adelic.Integers
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Analysis.Normed.MulAction
public import Mathlib.Tactic.Bound

@[expose] public section




/-! The genuine finite place at three and reduction of its integral completion. -/
noncomputable section
namespace GeneralEisenstein.Adelic

/-- The canonical rational finite place associated with the prime three. -/
def primeThree : Nat.Primes := ⟨3, by decide⟩

def placeThree : FinitePlace := Rat.HeightOneSpectrum.primesEquiv.symm primeThree

/-- Actual completion equivalence with the literal field used in the local calculation. -/
def threeCompletionEquiv : placeThree.adicCompletion ℚ ≃A[ℚ] ℚ_[3] :=
  (Padic.adicCompletionEquiv ℤ primeThree).symm

/-- Actual integer-completion equivalence, retaining the canonical integer embedding. -/
def threeIntegralEquiv : placeThree.adicCompletionIntegers ℚ ≃+* ℤ_[3] :=
  (@AlgEquiv.toRingEquiv _ _ _ _ _ _ _ (Ring.toIntAlgebra _)
    (@ContinuousAlgEquiv.toAlgEquiv _ _ _ _ _ _ _ _ _ (Ring.toIntAlgebra _)
      (PadicInt.adicCompletionIntegersEquiv ℤ primeThree))).symm

def integralThree : IntegralAdeles →+* ℤ_[3] :=
  threeIntegralEquiv.toRingHom.comp (Pi.evalRingHom _ placeThree)

def integralReduction : IntegralAdeles →+* ZMod 3 := PadicInt.toZMod.comp integralThree

@[simp] theorem integralReduction_int (z : ℤ) : integralReduction (z : IntegralAdeles) = z :=
  map_intCast integralReduction z

@[simp] theorem threeCompletion_rational (q : ℚ) :
    threeCompletionEquiv (algebraMap ℚ (placeThree.adicCompletion ℚ) q) = algebraMap ℚ ℚ_[3] q :=
  threeCompletionEquiv.commutes q

theorem threeIntegral_coe (x : placeThree.adicCompletionIntegers ℚ) :
    (threeIntegralEquiv x : ℚ_[3]) = threeCompletionEquiv x :=
  PadicInt.coe_adicCompletionIntegersEquiv_symm_apply ℤ primeThree x

end GeneralEisenstein.Adelic

end
