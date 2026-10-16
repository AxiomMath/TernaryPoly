module

public import TernaryPeriodPolynomials.ArithmeticCohomology.MultiplicityOne.DictionaryHeckeFixed
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Eigen.Satake.PrimeWeight
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Eigen.Satake.CentralCharacter

@[expose] public section


/-!
# The Hecke sum on level-three vectors is the Satake scalar

Level-three vectors are fixed by `K3 = GL₂(ℤ̂^{(3)})` (`levelThreeValues_le_fixedVectors`). The
representatives `x_i = (binaryHeckeLocalized p i)⁻¹`, `i ∈ ℙ¹(𝔽_p)`, are trivial at three and
permuted by `K3` up to `K3`, so `∑ᵢ π(x_i) v` is again `K3`-fixed and
`fixed_combination_omega` shows that it equals `(∑ᵢ ω(x_i)) v`. Each `ω(x_i)` equals
`ω(diag(p,1)⁻¹)` because the Hecke representatives lie in the double coset
`GL₂(ℤ) diag(p,1) GL₂(ℤ)`. Hence, for every prime `p ≠ 3`,

  `cuspPrimeHeckeSum σ p v = (p + 1) · ω(diag(p,1)⁻¹) • v`.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Separation (PlaneLeviLevel)
open TernaryPeriodPolynomials.RepresentationTheory
open TernaryPeriodPolynomials.HeckeEigen.Satake

namespace TernaryPeriodPolynomials.MultiplicityOne

/-! ## Elements of `GL₂(ℤ̂)` trivial at three are of the level -/

theorem planeLeviLevel_of_eval_one {κ : GeneralLinearGroup (Fin 2) IntegralAdeles}
    (h : GeneralLinearGroup.map (finiteEvaluation placeThree)
      (GeneralLinearGroup.map integralEmbedding κ) = 1) : PlaneLeviLevel κ := by
  have entry (i j : Fin 2) :
      (((κ.val i j) placeThree : placeThree.adicCompletionIntegers ℚ) :
        placeThree.adicCompletion ℚ) =
      (1 : Matrix (Fin 2) (Fin 2) (placeThree.adicCompletion ℚ)) i j := by
    have equal := congrArg
      (fun M : GeneralLinearGroup (Fin 2) (placeThree.adicCompletion ℚ) => M.val i j) h
    simpa [GeneralLinearGroup.map_apply] using equal
  have zero : κ.val 1 0 placeThree = 0 := by
    apply Subtype.ext
    simpa using entry 1 0
  have one : κ.val 1 1 placeThree = 1 := by
    apply Subtype.ext
    simpa using entry 1 1
  refine And.intro ?_ ?_
  · change integralReduction (κ.val 1 0) = 0
    rw [integralReduction_apply, zero, map_zero, map_zero]
  · change integralReduction (κ.val 1 1) = 1
    rw [integralReduction_apply, one, map_one, map_one]

/-- Level-three vectors are fixed by `K3 = GL₂(ℤ̂^{(3)})`. -/
theorem levelThreeValues_le_fixedVectors (σ : CuspidalRepresentation) :
    levelThreeValues σ ≤ fixedVectors σ K3 := by
  intro v hv g
  obtain ⟨k, hk, hgk⟩ := g.property
  obtain ⟨κ, rfl⟩ := hk.2
  have hg : (g : BinaryAdelicGL) = atFinite (GeneralLinearGroup.map integralEmbedding κ) :=
    hgk.symm
  rw [hg]
  exact hv κ (planeLeviLevel_of_eval_one (mem_awayGroup.mp hk.1))

/-! ## The localized representatives -/

theorem xloc_mem_awayGroup (prime : Nat.Primes) (h3 : prime.val ≠ 3)
    (index : Option (Fin prime.val)) :
    (binaryHeckeLocalized prime index)⁻¹ ∈ awayGroup placeThree := by
  rw [mem_awayGroup, map_inv, binaryHeckeLocalized_away prime index placeThree
    (placeThree_ne_integralPrimePlace prime h3), inv_one]

theorem heckeLocalized_eq_mul (prime : Nat.Primes) (index : Option (Fin prime.val)) :
    GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) (binaryHeckeRepresentative prime index) =
      GeneralLinearGroup.map integralEmbedding (binaryHeckeOutsideCompact prime index) *
        binaryHeckeLocalized prime index := by
  rw [binaryHeckeLocalized, mul_inv_cancel_left]

/-- Right translation by `K3` permutes the localized representatives up to `K3`. -/
theorem xloc_transition (prime : Nat.Primes) (h3 : prime.val ≠ 3) (k : BinaryFiniteGL)
    (hk : k ∈ awayLevel placeThree) :
    ∃ π : Equiv.Perm (Option (Fin prime.val)), ∀ index, ∃ o ∈ awayLevel placeThree,
      k * (binaryHeckeLocalized prime index)⁻¹ =
        (binaryHeckeLocalized prime (π index))⁻¹ * o := by
  obtain ⟨compact, hcompact⟩ := hk.2
  refine ⟨binaryHeckePermutation prime compact, fun index => ?_⟩
  have transition := binaryHeckePermutation_transition_integral prime compact index
  have hT : GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles)
        (binaryHeckeRepresentative prime (binaryHeckePermutation prime compact index)) *
      GeneralLinearGroup.map integralEmbedding compact *
      (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles)
        (binaryHeckeRepresentative prime index))⁻¹ ∈ sphericalFinite := transition
  rw [hcompact] at hT
  rw [heckeLocalized_eq_mul prime index,
    heckeLocalized_eq_mul prime (binaryHeckePermutation prime compact index)] at hT
  have hKi : GeneralLinearGroup.map integralEmbedding (binaryHeckeOutsideCompact prime index) ∈
      sphericalFinite := ⟨binaryHeckeOutsideCompact prime index, rfl⟩
  have hKj : GeneralLinearGroup.map integralEmbedding
      (binaryHeckeOutsideCompact prime (binaryHeckePermutation prime compact index)) ∈
      sphericalFinite := ⟨binaryHeckeOutsideCompact prime (binaryHeckePermutation prime compact
        index), rfl⟩
  have away : binaryHeckeLocalized prime (binaryHeckePermutation prime compact index) * k *
      (binaryHeckeLocalized prime index)⁻¹ ∈ awayGroup placeThree := by
    rw [mem_awayGroup, map_mul, map_mul, map_inv,
      binaryHeckeLocalized_away prime index placeThree
        (placeThree_ne_integralPrimePlace prime h3),
      binaryHeckeLocalized_away prime (binaryHeckePermutation prime compact index) placeThree
        (placeThree_ne_integralPrimePlace prime h3), mem_awayGroup.mp hk.1]
    all_goals simp
  have spherical : binaryHeckeLocalized prime (binaryHeckePermutation prime compact index) * k *
      (binaryHeckeLocalized prime index)⁻¹ ∈ sphericalFinite := by
    have equal : binaryHeckeLocalized prime (binaryHeckePermutation prime compact index) * k *
        (binaryHeckeLocalized prime index)⁻¹ =
        (GeneralLinearGroup.map integralEmbedding
          (binaryHeckeOutsideCompact prime (binaryHeckePermutation prime compact index)))⁻¹ *
          (GeneralLinearGroup.map integralEmbedding
            (binaryHeckeOutsideCompact prime (binaryHeckePermutation prime compact index)) *
            binaryHeckeLocalized prime (binaryHeckePermutation prime compact index) * k *
            (GeneralLinearGroup.map integralEmbedding (binaryHeckeOutsideCompact prime index) *
              binaryHeckeLocalized prime index)⁻¹) *
          GeneralLinearGroup.map integralEmbedding (binaryHeckeOutsideCompact prime index) := by
      group
    rw [equal]
    exact sphericalFinite.mul_mem (sphericalFinite.mul_mem (sphericalFinite.inv_mem hKj) hT) hKi
  exact ⟨binaryHeckeLocalized prime (binaryHeckePermutation prime compact index) * k *
    (binaryHeckeLocalized prime index)⁻¹, ⟨away, spherical⟩, by group⟩

/-- The sum over the localized representatives of a `K3`-fixed vector is `K3`-fixed. -/
theorem xloc_sum_fixed (σ : CuspidalRepresentation) (prime : Nat.Primes) (h3 : prime.val ≠ 3)
    (w : σ.H) (hw : w ∈ fixedVectors σ K3) :
    (∑ index : Option (Fin prime.val),
      σ.π (atFinite (binaryHeckeLocalized prime index)⁻¹) w) ∈ fixedVectors σ K3 := by
  intro g
  obtain ⟨k, hk, hgk⟩ := g.property
  have hg : (g : BinaryAdelicGL) = atFinite k := hgk.symm
  obtain ⟨π, hπ⟩ := xloc_transition prime h3 k hk
  have step : ∀ index, σ.π (g : BinaryAdelicGL)
      (σ.π (atFinite (binaryHeckeLocalized prime index)⁻¹) w) =
      σ.π (atFinite (binaryHeckeLocalized prime (π index))⁻¹) w := by
    intro index
    obtain ⟨o, ho, hko⟩ := hπ index
    have hfix : σ.π (atFinite o) w = w := hw ⟨atFinite o, atFinite_mem_K3 ho⟩
    rw [hg, ← Module.End.mul_apply, ← map_mul, ← atFinite_mul, hko, atFinite_mul, map_mul,
      Module.End.mul_apply, hfix]
  rw [map_sum]
  calc ∑ index, σ.π (g : BinaryAdelicGL)
        (σ.π (atFinite (binaryHeckeLocalized prime index)⁻¹) w)
      = ∑ index, σ.π (atFinite (binaryHeckeLocalized prime (π index))⁻¹) w :=
        Finset.sum_congr rfl (fun index _ => step index)
    _ = ∑ index, σ.π (atFinite (binaryHeckeLocalized prime index)⁻¹) w :=
        Equiv.sum_comp π (fun index => σ.π (atFinite (binaryHeckeLocalized prime index)⁻¹) w)

/-! ## The scalars `ω(x_i)` -/

theorem Bo_inv (B : GeneralLinearGroup (Fin 2) ℚ) : Bo B⁻¹ = (Bo B)⁻¹ :=
  eq_inv_of_mul_eq_one_right (by rw [← Bo_mul, mul_inv_cancel, Bo_one])

theorem glAway2_of_mem {x : BinaryFiniteGL} (hx : x ∈ awayGroup placeThree) : glAway2 x = x := by
  rw [glAway2, placePart, mem_awayGroup.mp hx, map_one, inv_one, one_mul]

theorem xloc_omega (σ : CuspidalRepresentation) (prime : Nat.Primes) (h3 : prime.val ≠ 3)
    (index : Option (Fin prime.val)) :
    omega σ (binaryHeckeLocalized prime index)⁻¹ =
      omega σ (Bo (binaryHeckeRepresentative prime index)⁻¹) := by
  have hK : (GeneralLinearGroup.map integralEmbedding
      (binaryHeckeOutsideCompact prime index))⁻¹ ∈ sphericalFinite :=
    sphericalFinite.inv_mem ⟨binaryHeckeOutsideCompact prime index, rfl⟩
  have hBo : Bo (binaryHeckeRepresentative prime index)⁻¹ =
      (binaryHeckeLocalized prime index)⁻¹ *
        glAway2 (GeneralLinearGroup.map integralEmbedding
          (binaryHeckeOutsideCompact prime index))⁻¹ := by
    rw [Bo, glF, map_inv, heckeLocalized_eq_mul prime index, _root_.mul_inv_rev, glAway2_mul,
      glAway2_of_mem (xloc_mem_awayGroup prime h3 index)]
  have level := omega_level σ (binaryHeckeLocalized prime index)⁻¹ (a := 1)
    (b := glAway2 (GeneralLinearGroup.map integralEmbedding
      (binaryHeckeOutsideCompact prime index))⁻¹) (Subgroup.one_mem _) (glAway2_level hK)
  rw [one_mul] at level
  rw [hBo]
  exact level.symm

/-- The swap matrix `[[0,1],[1,0]]` in `GL₂(ℤ)`. -/
def swapZ : GeneralLinearGroup (Fin 2) ℤ :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0], by
    ext row column
    fin_cases row <;> fin_cases column <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two], by
    ext row column
    fin_cases row <;> fin_cases column <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]⟩

theorem heckeRep_double_coset (prime : Nat.Primes) (index : Option (Fin prime.val)) :
    ∃ a ∈ Γ2, ∃ b ∈ Γ2, binaryHeckeRepresentative prime index = a * dP prime.property * b := by
  cases index with
  | none =>
    refine ⟨1, Γ2.one_mem, 1, Γ2.one_mem, ?_⟩
    rw [mul_one, one_mul]
    apply Units.ext
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [binaryHeckeRepresentative, binaryHeckeDilate, dP]
  | some j =>
    have hswap : GeneralLinearGroup.map (Int.castRingHom ℚ) swapZ ∈ Γ2 := ⟨swapZ, rfl⟩
    have hunip : GeneralLinearGroup.map (Int.castRingHom ℚ) (binaryUnipotent (j.val : ℤ)) ∈ Γ2 :=
      ⟨binaryUnipotent (j.val : ℤ), rfl⟩
    refine ⟨GeneralLinearGroup.map (Int.castRingHom ℚ) swapZ, hswap,
      GeneralLinearGroup.map (Int.castRingHom ℚ) swapZ *
        GeneralLinearGroup.map (Int.castRingHom ℚ) (binaryUnipotent (j.val : ℤ)),
      Γ2.mul_mem hswap hunip, ?_⟩
    apply Units.ext
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [binaryHeckeRepresentative, binaryHeckeTranslate, dP, swapZ, binaryUnipotent,
        Matrix.mul_apply, Fin.sum_univ_two]

theorem omega_Bo_heckeRep_inv (σ : CuspidalRepresentation) (prime : Nat.Primes)
    (index : Option (Fin prime.val)) :
    omega σ (Bo (binaryHeckeRepresentative prime index)⁻¹) =
      omega σ (Bo (dP prime.property)⁻¹) := by
  obtain ⟨a, ha, b, hb, hrep⟩ := heckeRep_double_coset prime index
  have level := omega_level σ (Bo (dP prime.property)⁻¹) (a := Bo b⁻¹) (b := Bo a⁻¹)
    (Bo_Γ2 (Γ2.inv_mem hb)) (Bo_Γ2 (Γ2.inv_mem ha))
  rw [hrep, _root_.mul_inv_rev, _root_.mul_inv_rev, Bo_mul, Bo_mul, ← mul_assoc]
  exact level

/-- **The Hecke sum on a level-three vector is the Satake scalar.** For a prime `p ≠ 3` and a
smooth vector `v` fixed by the level `{k₁₀ ≡ 0, k₁₁ ≡ 1 (mod 3)}` of even rotation weight,
`cuspPrimeHeckeSum σ p v = (p + 1) · ω(diag(p,1)⁻¹) • v`. -/
theorem cuspPrimeHeckeSum_levelThree (σ : CuspidalRepresentation) (halfWeight : ℤ)
    (prime : Nat.Primes) (h3 : prime.val ≠ 3) (v : σ.smooth) (hv : v.val ∈ levelThreeValues σ)
    (rotation : ∀ angle : Circle, σ.π (atInfinity (binaryRotations angle)) v.val =
      (angle : ℂ) ^ (2 * halfWeight) • v.val) :
    cuspPrimeHeckeSum σ prime v =
      (((prime.val : ℂ) + 1) * omega σ (Bo (dP prime.property)⁻¹)) • v := by
  apply Subtype.ext
  rw [cuspPrimeHeckeSum_levelThree_eq_sum σ halfWeight prime h3 v hv rotation]
  have hw : v.val ∈ fixedVectors σ K3 := levelThreeValues_le_fixedVectors σ hv
  have hsum := xloc_sum_fixed σ prime h3 v.val hw
  have key := fixed_combination_omega σ Finset.univ (fun _ => (1 : ℂ))
    (fun index => (binaryHeckeLocalized prime index)⁻¹)
    (fun index _ => xloc_mem_awayGroup prime h3 index) v.val hw
    (by simpa only [one_smul] using hsum)
  simp only [one_smul, one_mul] at key
  rw [key]
  have omegas : ∀ index : Option (Fin prime.val),
      omega σ (binaryHeckeLocalized prime index)⁻¹ = omega σ (Bo (dP prime.property)⁻¹) :=
    fun index => (xloc_omega σ prime h3 index).trans (omega_Bo_heckeRep_inv σ prime index)
  simp only [omegas, Finset.sum_const, Finset.card_univ, Fintype.card_option, Fintype.card_fin,
    nsmul_eq_mul]
  push_cast
  all_goals rfl

end TernaryPeriodPolynomials.MultiplicityOne
