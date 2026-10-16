module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Hecke.CosetsDiagonal

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryHeckeCosets
open Matrix PolynomialGLAction ModThreeGoodAction OrdinaryHeckeArithmetic OrdinaryHeckeTransfer

/-- Explicit unimodular integral lifts of the normalized projective covectors. -/
def chartMatrix {p : ℕ} : PrimeIndex p → Matrix (Fin 3) (Fin 3) ℤ
  | .inl (b,c) => !![-(b.val : ℤ),-(c.val : ℤ),1;1,0,0;0,1,0]
  | .inr (.inl a) => !![-(a.val : ℤ),1,0;1,0,0;0,0,1]
  | .inr (.inr _) => 1

def chartInverse {p : ℕ} : PrimeIndex p → Matrix (Fin 3) (Fin 3) ℤ
  | .inl (b,c) => !![0,1,0;0,0,1;1,(b.val : ℤ),(c.val : ℤ)]
  | .inr (.inl a) => !![0,1,0;1,(a.val : ℤ),0;0,0,1]
  | .inr (.inr _) => 1

def chartLift {p : ℕ} (i : PrimeIndex p) : IntegralGL :=
  ⟨chartMatrix i,chartInverse i,by
    rcases i with ⟨b,c⟩|a|u <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [chartMatrix,chartInverse,Matrix.mul_apply,Fin.sum_univ_three],by
    rcases i with ⟨b,c⟩|a|u <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [chartMatrix,chartInverse,Matrix.mul_apply,Fin.sum_univ_three]⟩

/-- The first row in the actual congruence quotient. -/
def firstRow (p : ℕ) (k : IntegralGL) : Fin 3 → ZMod p := fun j => (k.val 0 j : ZMod p)

theorem firstRow_chart {p : ℕ} [Fact p.Prime] (i : PrimeIndex p) :
    firstRow p (chartLift i)=normalCovector i := by
  rcases i with ⟨b,c⟩|a|u <;> funext j <;> fin_cases j <;>
    simp [firstRow,chartLift,chartMatrix,normalCovector]

/-- An invertible congruence matrix has a nonzero first row. -/
theorem firstRow_ne_zero (p : ℕ) [Fact p.Prime] (k : IntegralGL) : firstRow p k ≠ 0 := by
  intro hz
  have hrow (j : Fin 3) : (congruenceMap p k).val 0 j=0 := congrFun hz j
  have he := congrArg (fun M : Matrix (Fin 3) (Fin 3) (ZMod p) => M 0 0)
    (congruenceMap p k).val_inv
  rw [Matrix.mul_apply] at he
  simp [hrow] at he

/-- The two congruence equations obtained from the explicit inverse chart lift. -/
def chartConditions {p : ℕ} (v : Fin 3 → ZMod p) : PrimeIndex p → Prop
  | .inl (b,c) => v 0+b*v 2=0 ∧ v 1+c*v 2=0
  | .inr (.inl a) => v 0+a*v 1=0 ∧ v 2=0
  | .inr (.inr _) => v 1=0 ∧ v 2=0

/-- Exact subgroup membership after right multiplication by a chart lift inverse. -/
theorem chart_membership_iff (p : ℕ) [Fact p.Prime] (k : IntegralGL) (i : PrimeIndex p) :
    integralEquiv (k*(chartLift i)⁻¹) ∈ intersection Gamma (primeDiagonal p) ↔
      chartConditions (firstRow p k) i := by
  rw [mem_primeIntersection_iff_mod]
  rcases i with ⟨b,c⟩|a|u <;>
    simp [chartConditions,firstRow,chartLift,chartInverse,Matrix.mul_apply,
      Fin.sum_univ_three,mul_comm]

/-- The chart equations are equivalent to proportionality with the normalized covector. -/
theorem chartConditions_iff {p : ℕ} [Fact p.Prime] (v : Fin 3 → ZMod p) (hv : v ≠ 0)
    (i : PrimeIndex p) : chartConditions v i ↔ ∃ s : ZMod p, s ≠ 0 ∧ v=s • normalCovector i := by
  constructor
  · intro hi
    rcases i with ⟨b,c⟩|a|u
    · obtain ⟨h0,h1⟩ := hi
      have h2 : v 2 ≠ 0 := by
        intro h2
        apply hv
        funext j
        fin_cases j <;> simp_all
      refine ⟨v 2,h2,?_⟩
      funext j
      fin_cases j <;> dsimp [normalCovector]
      · linear_combination h0
      · linear_combination h1
      · simp
    · obtain ⟨h0,h2⟩ := hi
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
      · simpa using h2
    · obtain ⟨h1,h2⟩ := hi
      have h0 : v 0 ≠ 0 := by
        intro h0
        apply hv
        funext j
        fin_cases j <;> assumption
      refine ⟨v 0,h0,?_⟩
      funext j
      fin_cases j <;> simp [normalCovector,h1,h2]
  · rintro ⟨s,_,rfl⟩
    rcases i with ⟨b,c⟩|a|u <;> dsimp [chartConditions,normalCovector] <;> constructor <;> ring

end TernaryPoly.OrdinaryHeckeCosets
