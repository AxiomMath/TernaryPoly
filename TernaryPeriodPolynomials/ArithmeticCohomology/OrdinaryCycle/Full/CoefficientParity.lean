module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Full.CoefficientSymmetry

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryFullCoefficient
open ModThreeGoodAction OrdinaryFullAction OrdinaryApartmentFrames SinglePoleSupport PolynomialGLAction

/-- Coordinate permutations as an actual integral matrix homomorphism. -/
def permutationHom : Equiv.Perm (Fin 3) →* IntegralGL where
  toFun := permutationMatrix
  map_one' := by apply Units.ext; simp [permutationMatrix]
  map_mul' π σ := by
    apply Units.ext
    change ((π*σ)⁻¹).permMatrix ℤ=(π⁻¹).permMatrix ℤ*(σ⁻¹).permMatrix ℤ
    rw [mul_inv_rev,Matrix.permMatrix_mul]

private theorem permutation_cases : ∀ π : Equiv.Perm (Fin 3),
    ∃ a : Fin 3, ∃ b : Fin 2, π=cyclePermutation^a.val*(Equiv.swap 0 1)^b.val := by
  decide +kernel

/-- The exact two permutation apartment relations imply the full determinant-minus-one symmetry. -/
theorem symmetry_of_relations {E : Type*} [AddCommGroup E] [Module ℚ E]
    (ρ : Representation ℚ OrdinaryFullAction.GL3 E) (v : E) (h : Relations ρ v) :
    ∀ π,ρ (integral (permutationMatrix π)) v=
      determinantCharacter (-1) (integral (permutationMatrix π)) • v := by
  let Good (π : Equiv.Perm (Fin 3)) : Prop :=
    ρ (integral (permutationHom π)) v=determinantCharacter (-1) (integral (permutationHom π)) • v
  have h1 : Good 1 := by simp only [Good,map_one,Module.End.one_apply,one_smul]
  have hm {π σ : Equiv.Perm (Fin 3)} (hπ : Good π) (hσ : Good σ) : Good (π*σ) := by
    dsimp only [Good] at hπ hσ ⊢
    rw [map_mul,map_mul,map_mul,Module.End.mul_apply,hσ,map_smul,hπ,map_mul,smul_smul]
    rw [mul_comm]
  have hp {π : Equiv.Perm (Fin 3)} (hπ : Good π) (k : ℕ) : Good (π^k) := by
    induction k with
    | zero => simpa only [pow_zero] using h1
    | succ k ih => simpa only [pow_succ] using hm ih hπ
  have hc : Good cyclePermutation := by
    change ρ (integral (permutationMatrix cyclePermutation)) v=
      determinantCharacter (-1) (integral (permutationMatrix cyclePermutation)) • v
    rw [permutationMatrix_cycle,determinantCharacter_cycle,one_smul]
    exact h.cyclic
  have hs : Good (Equiv.swap 0 1) := by
    change ρ (integral (permutationMatrix (Equiv.swap 0 1))) v=
      determinantCharacter (-1) (integral (permutationMatrix (Equiv.swap 0 1))) • v
    rw [permutationMatrix_swap,determinantCharacter_swap,neg_one_smul]
    exact h.swap
  intro π
  obtain ⟨a,b,rfl⟩ := permutation_cases π
  exact hm (hp hc a.val) (hp hs b.val)

/-- The apartment sign equations are exactly invariance under every literal boolean sign matrix. -/
theorem sign_invariant_of_relations {E : Type*} [AddCommGroup E] [Module ℚ E]
    (ρ : Representation ℚ OrdinaryFullAction.GL3 E) (v : E) (h : Relations ρ v) (s : Fin 3 → Bool) :
    ρ (integral (signMatrix s)) v=v := by
  classical
  have he : (fun i => decide (i∈Finset.univ.filter (fun i => s i=true)))=s := by
    funext i
    cases hi : s i <;> simp [hi]
  have hs := h.signs (Finset.univ.filter (fun i => s i=true))
  rw [signFrame_eq_signMatrix,he] at hs
  exact hs

end TernaryPoly.OrdinaryFullCoefficient
