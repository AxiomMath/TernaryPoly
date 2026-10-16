module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.SeedEquivariance

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.OrdinaryFiberPermutations
open OrdinaryCovectors OrdinarySeedEquivariance

def swapPerm : Equiv.Perm (Fin 3) :=
  ⟨![1,0,2],![1,0,2],by decide +kernel,by decide +kernel⟩
def cyclePerm : Equiv.Perm (Fin 3) :=
  ⟨![2,0,1],![1,2,0],by decide +kernel,by decide +kernel⟩

/-- Exhaustive certificate in S3, with no assumed generation theorem. -/
theorem permutation_decomposition : ∀ π : Equiv.Perm (Fin 3),
    ∃ a : Fin 3,∃ b : Fin 2,π=cyclePerm^a.val*swapPerm^b.val := by
  decide +kernel

def permuteRow (π : Equiv.Perm (Fin 3)) (r : Covector) : Covector := fun i => r (π i)
def permutePoly (π : Equiv.Perm (Fin 3)) : TernaryPolynomial →ₐ[ℚ] TernaryPolynomial :=
  bind₁ (fun i => X (π.symm i))

theorem permuteRow_mul (π σ : Equiv.Perm (Fin 3)) (r : Covector) :
    permuteRow (π*σ) r=permuteRow σ (permuteRow π r) := rfl

theorem permutePoly_mul (π σ : Equiv.Perm (Fin 3)) :
    (permutePoly σ).comp (permutePoly π)=permutePoly (π*σ) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [permutePoly,AlgHom.comp_apply]
  rfl

theorem permutePoly_one : permutePoly 1=AlgHom.id ℚ TernaryPolynomial := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [permutePoly]
  rfl

theorem permuteRow_swap (r : Covector) : permuteRow swapPerm r=swapRow r := by
  funext i
  fin_cases i <;> rfl

theorem permuteRow_cycle (r : Covector) : permuteRow cyclePerm r=cycleRow r := by
  funext i
  fin_cases i <;> rfl

theorem permutePoly_swap : permutePoly swapPerm=S := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [permutePoly,swapPerm,S]

theorem permutePoly_cycle : permutePoly cyclePerm=C := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [permutePoly,cyclePerm,C]

/-- The two actual generator equations imply every permutation coefficient equation. -/
theorem permutation_equivariance (F : Covector → TernaryPolynomial)
    (hs : ∀ r,F (swapRow r)=S (F r))
    (hc : ∀ r,F (cycleRow r)=C (F r)) :
    ∀ π r,F (permuteRow π r)=permutePoly π (F r) := by
  let Good (π : Equiv.Perm (Fin 3)) : Prop := ∀ r,F (permuteRow π r)=permutePoly π (F r)
  have h1 : Good 1 := by
    intro r
    rw [permutePoly_one]
    rfl
  have hm {π σ : Equiv.Perm (Fin 3)} (hπ : Good π) (hσ : Good σ) : Good (π*σ) := by
    intro r
    rw [permuteRow_mul,hσ,hπ]
    exact DFunLike.congr_fun (permutePoly_mul π σ) (F r)
  have hp {π : Equiv.Perm (Fin 3)} (hπ : Good π) (n : ℕ) : Good (π^n) := by
    induction n with
    | zero => simpa using h1
    | succ n ih => rw [pow_succ]; exact hm ih hπ
  have hswap : Good swapPerm := by
    intro r
    rw [permuteRow_swap,permutePoly_swap]
    exact hs r
  have hcycle : Good cyclePerm := by
    intro r
    rw [permuteRow_cycle,permutePoly_cycle]
    exact hc r
  intro π r
  obtain ⟨a,b,rfl⟩ := permutation_decomposition π
  exact hm (hp hcycle a.val) (hp hswap b.val) r

/-- The explicit polynomial seed table obeys all six coordinate permutations. -/
theorem seedValue_permutation {f P Q : TernaryPolynomial} (h : SymmetricSeedData f P Q)
    (hc : C f=f) (hs : S f=f) (π : Equiv.Perm (Fin 3)) (r : Covector) :
    OrdinarySeedFibers.seedValue f P Q (permuteRow π r)=
      permutePoly π (OrdinarySeedFibers.seedValue f P Q r) :=
  permutation_equivariance _ (seedValue_swap h hs) (seedValue_cycle h hc hs) π r

end TernaryPoly.OrdinaryFiberPermutations
