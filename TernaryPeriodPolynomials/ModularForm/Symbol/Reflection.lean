module

public import TernaryPeriodPolynomials.ModularForm.Symbol.Mobius
public import TernaryPeriodPolynomials.ModularForm.HeckeEndomorphism.AlternativeSymbols

@[expose] public section

noncomputable section
namespace TernaryPoly.BinaryCuspSymbol
open BinaryModularSymbol RankTwoAugmentedFrames BinaryRationalHeckePrime
open BinaryCuspHeckeEndomorphism

/-- The integral reflection in the first coordinate. -/
def reflectionIntegral : IntegralGL :=
  ⟨!![-1,0;0,1],!![-1,0;0,1],by decide +kernel,by decide +kernel⟩

def reflection : GL2 := integral reflectionIntegral

@[simp] theorem reflectionIntegral_det : reflectionIntegral.val.det = -1 := by
  norm_num [reflectionIntegral,Matrix.det_fin_two]

@[simp] theorem reflection_matrix : reflection.val=!![-1,0;0,1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

@[simp] theorem reflection_sq : reflection*reflection=1 := by
  apply Units.ext
  change reflection.val*reflection.val=1
  rw [reflection_matrix]
  decide +kernel

/-- Integral translation, used for the finite representative reindexing. -/
def slTranslation (a : ℤ) : SL2 := ⟨!![1,a;0,1],by simp [Matrix.det_fin_two]⟩

@[simp] theorem slTranslation_matrix (a : ℤ) :
    (slRational (slTranslation a)).val=!![1,(a : ℚ);0,1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The mod-p negative representative differs by an integral translation. -/
theorem reflection_adjugate_finite (p : ℕ) [Fact p.Prime] (b : ZMod p) :
    reflection*adjugateRepresentative p (.inl b)=
      adjugateRepresentative p (.inl (-b))*reflection*
        slRational (slTranslation (if b.val=0 then 0 else -1)) := by
  have hp : 0<p := (Fact.out : p.Prime).pos
  let : NeZero p := ⟨hp.ne'⟩
  have hv : b.val+(-b).val=if b.val=0 then 0 else p := by
    by_cases hb : b=0
    · simp [hb]
    · let : NeZero b := ⟨hb⟩
      have hbval : b.val≠0 := by simpa using hb
      rw [ZMod.val_neg_of_ne_zero,ite_eq_right hbval]
      have ht := ZMod.val_lt b
      omega
  apply Units.ext
  change reflection.val*(adjugateRepresentative p (.inl b)).val=
    (adjugateRepresentative p (.inl (-b))).val*reflection.val*
      (slRational (slTranslation (if b.val=0 then 0 else -1))).val
  rw [reflection_matrix,adjugateRepresentative_matrix,adjugateRepresentative_matrix,slTranslation_matrix]
  have hq : (b.val : ℚ)+((-b).val : ℚ)=if b.val=0 then 0 else (p : ℚ) := by
    exact_mod_cast hv
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply,Fin.sum_univ_two]
  split_ifs at * <;> norm_num at * <;> first | contradiction | linarith

/-- The exceptional diagonal representative commutes with reflection. -/
theorem reflection_adjugate_infinity (p : ℕ) [Fact p.Prime] (u : Unit) :
    reflection*adjugateRepresentative p (.inr u)=
      adjugateRepresentative p (.inr u)*reflection := by
  apply Units.ext
  change reflection.val*(adjugateRepresentative p (.inr u)).val=
    (adjugateRepresentative p (.inr u)).val*reflection.val
  rw [reflection_matrix,adjugateRepresentative_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_two]

/-- For an actual rational representation, the prime adjugate sum commutes with reflection
on every vector fixed by the integral special-linear group. -/
theorem adjugate_sum_reflection {V : Type*} [AddCommGroup V] [Module ℚ V]
    (ρ : Representation ℚ GL2 V) (p : ℕ) [Fact p.Prime] (v : V)
    (hv : ∀ γ : SL2,ρ (slRational γ) v=v) :
    ρ reflection (∑ i : PrimeIndex p,ρ (adjugateRepresentative p i) v)=
      ∑ i : PrimeIndex p,ρ (adjugateRepresentative p i) (ρ reflection v) := by
  classical
  rw [map_sum]
  have hf (b : ZMod p) : ρ reflection (ρ (adjugateRepresentative p (.inl b)) v)=
      ρ (adjugateRepresentative p (.inl (-b))) (ρ reflection v) := by
    rw [←Module.End.mul_apply,←map_mul,reflection_adjugate_finite,map_mul,Module.End.mul_apply,hv,
      map_mul,Module.End.mul_apply]
  have hi (u : Unit) : ρ reflection (ρ (adjugateRepresentative p (.inr u)) v)=
      ρ (adjugateRepresentative p (.inr u)) (ρ reflection v) := by
    rw [←Module.End.mul_apply,←map_mul,reflection_adjugate_infinity,map_mul,Module.End.mul_apply]
  rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
  congr 1
  · simp_rw [hf]
    exact Equiv.sum_comp (Equiv.neg (ZMod p)) (fun b => ρ (adjugateRepresentative p (.inl b)) (ρ reflection v))
  · exact Finset.sum_congr rfl (fun u _ => hi u)

end TernaryPoly.BinaryCuspSymbol
