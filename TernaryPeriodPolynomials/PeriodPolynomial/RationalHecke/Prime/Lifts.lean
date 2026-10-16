module

public import TernaryPeriodPolynomials.PeriodPolynomial.RationalHecke.Prime.Diagonal

@[expose] public section


noncomputable section
namespace TernaryPoly.BinaryRationalHeckePrime
open BinaryModularSymbol (GL2)
open Matrix RankTwoAugmentedFrames BinaryRationalHeckeArithmetic OrdinaryHeckeTransfer

def chartMatrix {p : ℕ} : PrimeIndex p → Matrix (Fin 2) (Fin 2) ℤ
  | .inl a => !![-(a.val : ℤ),1;1,0]
  | .inr _ => 1

def chartInverse {p : ℕ} : PrimeIndex p → Matrix (Fin 2) (Fin 2) ℤ
  | .inl a => !![0,1;1,(a.val : ℤ)]
  | .inr _ => 1

def chartLift {p : ℕ} (i : PrimeIndex p) : IntegralGL :=
  ⟨chartMatrix i,chartInverse i,by
    rcases i with a|u <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [chartMatrix,chartInverse,Matrix.mul_apply,Fin.sum_univ_two],by
    rcases i with a|u <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [chartMatrix,chartInverse,Matrix.mul_apply,Fin.sum_univ_two]⟩

def firstRow (p : ℕ) (k : IntegralGL) : Fin 2 → ZMod p := fun j => (k.val 0 j : ZMod p)

theorem firstRow_chart {p : ℕ} [Fact p.Prime] (i : PrimeIndex p) :
    firstRow p (chartLift i)=normalCovector i := by
  rcases i with a|u <;> funext j <;> fin_cases j <;>
    simp [firstRow,chartLift,chartMatrix,normalCovector]

theorem firstRow_ne_zero (p : ℕ) [Fact p.Prime] (k : IntegralGL) : firstRow p k ≠ 0 := by
  intro hz
  have hrow (j : Fin 2) : (congruenceMap p k).val 0 j=0 := congrFun hz j
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) (ZMod p) => M 0 0)
    (congruenceMap p k).val_inv
  rw [Matrix.mul_apply] at he
  simp [hrow] at he

def chartConditions {p : ℕ} (v : Fin 2 → ZMod p) : PrimeIndex p → Prop
  | .inl a => v 0+a*v 1=0
  | .inr _ => v 1=0

theorem chart_membership_iff (p : ℕ) [Fact p.Prime] (k : IntegralGL) (i : PrimeIndex p) :
    integralEquiv (k*(chartLift i)⁻¹) ∈ intersection Gamma (primeDiagonal p) ↔
      chartConditions (firstRow p k) i := by
  rw [mem_primeIntersection_iff_mod]
  rcases i with a|u <;>
    simp [chartConditions,firstRow,chartLift,chartInverse,Matrix.mul_apply,Fin.sum_univ_two,mul_comm]

theorem chartConditions_iff {p : ℕ} [Fact p.Prime] (v : Fin 2 → ZMod p) (hv : v ≠ 0)
    (i : PrimeIndex p) : chartConditions v i ↔ ∃ s : ZMod p, s ≠ 0 ∧ v=s • normalCovector i := by
  constructor
  · intro hi
    rcases i with a|u
    · have h0 : v 0+a*v 1=0 := hi
      have h1 : v 1 ≠ 0 := by
        intro h1
        apply hv
        funext j
        fin_cases j <;> simp_all
      refine ⟨v 1,h1,?_⟩
      funext j
      fin_cases j <;> dsimp [normalCovector]
      · linear_combination h0
      · simp
    · have h1 : v 1=0 := hi
      have h0 : v 0 ≠ 0 := by
        intro h0
        apply hv
        funext j
        fin_cases j <;> assumption
      refine ⟨v 0,h0,?_⟩
      funext j
      fin_cases j <;> simp [normalCovector,h1]
  · rintro ⟨s,_,rfl⟩
    rcases i with a|u <;> dsimp [chartConditions,normalCovector] <;> ring

end TernaryPoly.BinaryRationalHeckePrime
