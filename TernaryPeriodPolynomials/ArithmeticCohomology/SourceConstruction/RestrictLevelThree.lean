module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.RestrictCore
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Arithmetic.StabilizerEdge

@[expose] public section


/-!
# Level-three congruence subgroups of `GL₂(ℤ)` and restriction in `H¹`

The reduction `GL₂(ℤ) → GL₂(𝔽₃)` has finite image, so the preimage of any subgroup `K` of
`GL₂(𝔽₃)` has finite index (`levelThreeSubgroup K`).  We name the two instances used downstream:

* `secondRowSubgroup`, the matrices whose second row reduces to `(0, 1)` modulo `3`;
* `firstColumnSubgroup`, the matrices whose first column reduces to `(1, 0)ᵀ` modulo `3`.

By `RestrictCore`, a one-cocycle of `GL₂(ℤ)` that is a coboundary on such a subgroup is a
coboundary, in particular for `arithmeticBinaryRep d t`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.SourceConstruction

open TernaryPeriodPolynomials.SphericalDetection.Helpers

/-- Reduction modulo `3` of `GL₂(ℤ)`. -/
def reductionMod3 :
    Matrix.GeneralLinearGroup (Fin 2) ℤ →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) :=
  Matrix.GeneralLinearGroup.map (Int.castRingHom (ZMod 3))

theorem finite_generalLinearGroup_zmod_three :
    Finite (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :=
  Finite.of_injective
    (fun g : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) =>
      (fun i j => g.val i j : Fin 2 → Fin 2 → ZMod 3))
    (fun _ _ e => Units.ext (Matrix.ext fun i j => congrFun (congrFun e i) j))

/-- The preimage in `GL₂(ℤ)` of a subgroup of `GL₂(𝔽₃)` under reduction modulo `3`. -/
def levelThreeSubgroup (K : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))) :
    Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℤ) :=
  K.comap reductionMod3

theorem mem_levelThreeSubgroup {K : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))}
    {m : Matrix.GeneralLinearGroup (Fin 2) ℤ} :
    m ∈ levelThreeSubgroup K ↔ reductionMod3 m ∈ K :=
  Iff.rfl

/-- **The preimage of any subgroup of `GL₂(𝔽₃)` has finite index in `GL₂(ℤ)`.** -/
instance levelThreeSubgroup_finiteIndex
    (K : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))) :
    (levelThreeSubgroup K).FiniteIndex := by
  have : Finite (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :=
    finite_generalLinearGroup_zmod_three
  have : reductionMod3.ker.FiniteIndex := Subgroup.finiteIndex_ker reductionMod3
  refine Subgroup.finiteIndex_of_le (show reductionMod3.ker ≤ levelThreeSubgroup K from ?_)
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  rw [mem_levelThreeSubgroup, hg]
  exact K.one_mem

/-- The elements of `GL₂(𝔽₃)` fixing the row vector `v` under right multiplication. -/
def rowFixingSubgroup (v : Fin 2 → ZMod 3) :
    Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) where
  carrier := {g | Matrix.vecMul v g.val = v}
  one_mem' := by
    change Matrix.vecMul v (1 : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)).val = v
    rw [Units.val_one, Matrix.vecMul_one]
  mul_mem' := by
    intro a b ha hb
    have ha' : Matrix.vecMul v a.val = v := ha
    have hb' : Matrix.vecMul v b.val = v := hb
    change Matrix.vecMul v (a * b).val = v
    rw [Units.val_mul, ← Matrix.vecMul_vecMul, ha', hb']
  inv_mem' := by
    intro a ha
    have ha' : Matrix.vecMul v a.val = v := ha
    change Matrix.vecMul v (a⁻¹).val = v
    calc Matrix.vecMul v (a⁻¹).val = Matrix.vecMul (Matrix.vecMul v a.val) (a⁻¹).val := by
          rw [ha']
      _ = Matrix.vecMul v (a.val * (a⁻¹).val) := by rw [Matrix.vecMul_vecMul]
      _ = v := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]

/-- The elements of `GL₂(𝔽₃)` fixing the column vector `v` under left multiplication. -/
def columnFixingSubgroup (v : Fin 2 → ZMod 3) :
    Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) where
  carrier := {g | Matrix.mulVec g.val v = v}
  one_mem' := by
    change Matrix.mulVec (1 : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)).val v = v
    rw [Units.val_one, Matrix.one_mulVec]
  mul_mem' := by
    intro a b ha hb
    have ha' : Matrix.mulVec a.val v = v := ha
    have hb' : Matrix.mulVec b.val v = v := hb
    change Matrix.mulVec (a * b).val v = v
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hb', ha']
  inv_mem' := by
    intro a ha
    have ha' : Matrix.mulVec a.val v = v := ha
    change Matrix.mulVec (a⁻¹).val v = v
    calc Matrix.mulVec (a⁻¹).val v = Matrix.mulVec (a⁻¹).val (Matrix.mulVec a.val v) := by
          rw [ha']
      _ = Matrix.mulVec ((a⁻¹).val * a.val) v := by rw [Matrix.mulVec_mulVec]
      _ = v := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

/-- The matrices of `GL₂(ℤ)` whose second row reduces to `(0, 1)` modulo `3`. -/
def secondRowSubgroup : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℤ) :=
  levelThreeSubgroup (rowFixingSubgroup ![0, 1])

/-- The matrices of `GL₂(ℤ)` whose first column reduces to `(1, 0)ᵀ` modulo `3`. -/
def firstColumnSubgroup : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℤ) :=
  levelThreeSubgroup (columnFixingSubgroup ![1, 0])

instance secondRowSubgroup_finiteIndex : secondRowSubgroup.FiniteIndex :=
  levelThreeSubgroup_finiteIndex _

instance firstColumnSubgroup_finiteIndex : firstColumnSubgroup.FiniteIndex :=
  levelThreeSubgroup_finiteIndex _

theorem reductionMod3_apply (m : Matrix.GeneralLinearGroup (Fin 2) ℤ) (i j : Fin 2) :
    (reductionMod3 m).val i j = ((m.val i j : ℤ) : ZMod 3) := by
  rfl

theorem vecMul_zero_one_iff (M : Matrix (Fin 2) (Fin 2) (ZMod 3)) :
    Matrix.vecMul ![0, 1] M = ![0, 1] ↔ M 1 0 = 0 ∧ M 1 1 = 1 := by
  have hrow : ∀ j, Matrix.vecMul ![0, 1] M j = M 1 j := by
    intro j
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    rw [hrow] at h0 h1
    exact ⟨by simpa using h0, by simpa using h1⟩
  · rintro ⟨h0, h1⟩
    funext j
    rw [hrow]
    fin_cases j
    · simpa using h0
    · simpa using h1

theorem mulVec_one_zero_iff (M : Matrix (Fin 2) (Fin 2) (ZMod 3)) :
    Matrix.mulVec M ![1, 0] = ![1, 0] ↔ M 0 0 = 1 ∧ M 1 0 = 0 := by
  have hcol : ∀ i, Matrix.mulVec M ![1, 0] i = M i 0 := by
    intro i
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    rw [hcol] at h0 h1
    exact ⟨by simpa using h0, by simpa using h1⟩
  · rintro ⟨h0, h1⟩
    funext i
    rw [hcol]
    fin_cases i
    · simpa using h0
    · simpa using h1

theorem mem_secondRowSubgroup {m : Matrix.GeneralLinearGroup (Fin 2) ℤ} :
    m ∈ secondRowSubgroup ↔
      ((m.val 1 0 : ℤ) : ZMod 3) = 0 ∧ ((m.val 1 1 : ℤ) : ZMod 3) = 1 := by
  change Matrix.vecMul (![0, 1] : Fin 2 → ZMod 3) (reductionMod3 m).val = ![0, 1] ↔ _
  rw [vecMul_zero_one_iff, reductionMod3_apply, reductionMod3_apply]

theorem mem_firstColumnSubgroup {m : Matrix.GeneralLinearGroup (Fin 2) ℤ} :
    m ∈ firstColumnSubgroup ↔
      ((m.val 0 0 : ℤ) : ZMod 3) = 1 ∧ ((m.val 1 0 : ℤ) : ZMod 3) = 0 := by
  change Matrix.mulVec (reductionMod3 m).val (![1, 0] : Fin 2 → ZMod 3) = ![1, 0] ↔ _
  rw [mulVec_one_zero_iff, reductionMod3_apply, reductionMod3_apply]

/-- **Restriction to a level-three congruence subgroup is injective on `H¹(GL₂(ℤ), A)`** for every
complex representation `A`: a cocycle which is the coboundary of `v` on the preimage of `K` has
zero class. -/
theorem H1π_eq_zero_of_restrict_levelThree
    (K : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)))
    (A : Rep ℂ (Matrix.GeneralLinearGroup (Fin 2) ℤ))
    (φ : groupCohomology.cocycles₁ A) (v : A)
    (hv : ∀ m ∈ levelThreeSubgroup K, φ m = A.ρ m v - v) :
    groupCohomology.H1π A φ = 0 :=
  H1π_eq_zero_of_restrict A (levelThreeSubgroup K) φ v hv

/-- Restriction to the subgroup of matrices with second row `≡ (0, 1) (mod 3)` is injective on
`H¹(GL₂(ℤ), A)`. -/
theorem H1π_eq_zero_of_restrict_secondRow
    (A : Rep ℂ (Matrix.GeneralLinearGroup (Fin 2) ℤ))
    (φ : groupCohomology.cocycles₁ A) (v : A)
    (hv : ∀ m : Matrix.GeneralLinearGroup (Fin 2) ℤ,
      ((m.val 1 0 : ℤ) : ZMod 3) = 0 → ((m.val 1 1 : ℤ) : ZMod 3) = 1 →
        φ m = A.ρ m v - v) :
    groupCohomology.H1π A φ = 0 :=
  H1π_eq_zero_of_restrict A secondRowSubgroup φ v
    (fun m hm => hv m (mem_secondRowSubgroup.mp hm).1 (mem_secondRowSubgroup.mp hm).2)

/-- Restriction to the subgroup of matrices with first column `≡ (1, 0)ᵀ (mod 3)` is injective on
`H¹(GL₂(ℤ), A)`. -/
theorem H1π_eq_zero_of_restrict_firstColumn
    (A : Rep ℂ (Matrix.GeneralLinearGroup (Fin 2) ℤ))
    (φ : groupCohomology.cocycles₁ A) (v : A)
    (hv : ∀ m : Matrix.GeneralLinearGroup (Fin 2) ℤ,
      ((m.val 0 0 : ℤ) : ZMod 3) = 1 → ((m.val 1 0 : ℤ) : ZMod 3) = 0 →
        φ m = A.ρ m v - v) :
    groupCohomology.H1π A φ = 0 :=
  H1π_eq_zero_of_restrict A firstColumnSubgroup φ v
    (fun m hm => hv m (mem_firstColumnSubgroup.mp hm).1 (mem_firstColumnSubgroup.mp hm).2)

/-- The instance used downstream: a cocycle of `GL₂(ℤ)` in `arithmeticBinaryRep (n + 1) t` that is
a coboundary on the matrices with second row `≡ (0, 1) (mod 3)` has zero class. -/
theorem arithmeticBinaryRep_H1π_eq_zero_of_secondRow (n : ℕ) (t : ℤ)
    (φ : groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) t))
    (v : arithmeticBinaryRep (n + 1) t)
    (hv : ∀ m : Matrix.GeneralLinearGroup (Fin 2) ℤ,
      ((m.val 1 0 : ℤ) : ZMod 3) = 0 → ((m.val 1 1 : ℤ) : ZMod 3) = 1 →
        φ m = (arithmeticBinaryRep (n + 1) t).ρ m v - v) :
    groupCohomology.H1π (arithmeticBinaryRep (n + 1) t) φ = 0 :=
  H1π_eq_zero_of_restrict_secondRow _ φ v hv

/-- The instance used downstream: a cocycle of `GL₂(ℤ)` in `arithmeticBinaryRep (n + 1) t` that is
a coboundary on the matrices with first column `≡ (1, 0)ᵀ (mod 3)` has zero class. -/
theorem arithmeticBinaryRep_H1π_eq_zero_of_firstColumn (n : ℕ) (t : ℤ)
    (φ : groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) t))
    (v : arithmeticBinaryRep (n + 1) t)
    (hv : ∀ m : Matrix.GeneralLinearGroup (Fin 2) ℤ,
      ((m.val 0 0 : ℤ) : ZMod 3) = 1 → ((m.val 1 0 : ℤ) : ZMod 3) = 0 →
        φ m = (arithmeticBinaryRep (n + 1) t).ρ m v - v) :
    groupCohomology.H1π (arithmeticBinaryRep (n + 1) t) φ = 0 :=
  H1π_eq_zero_of_restrict_firstColumn _ φ v hv

end TernaryPeriodPolynomials.SourceConstruction
