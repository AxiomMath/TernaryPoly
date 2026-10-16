module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularity.Injective
public import TernaryPeriodPolynomials.ArithmeticCohomology.Automorphic.TypeData
public import TernaryPeriodPolynomials.ArithmeticCohomology.Automorphic.AbstractIrreducibility
public import TernaryPeriodPolynomials.ArithmeticCohomology.Automorphic.Weight

@[expose] public section


/-!
# The weight `-k` type subspace of the Bergman representation

For a finite-adelic model `M` and an open compact subgroup `K` of `GL₂(𝔸_f)`, the type subspace
of `bergmanRep M` for the group `typeGroup K` (archimedean part in `SO(2)`, finite part in `K`) and
the weight `-k` character `Weight.typeCharacterInv k K` consists of the lowest weight vectors
`lowestMinus hk e` with `e` fixed by `K` (`typeSubspace_eq_map`).  It is therefore finite
dimensional (`finiteDimensional_typeSubspace`) and compression stable
(`compressionStable_typeSubspace`).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.Automorphic
open TernaryPeriodPolynomials.Automorphic.SmoothVectors

namespace TernaryPeriodPolynomials.Regularity

/-! ### The group `SO(2)` -/

theorem rotUnit_eq_rotGL (θ : ℝ) : Weight.rotUnit θ = rotGL θ :=
  Units.ext (by rw [rotGL_val]; rfl)

theorem rotGL_mem_so2 (θ : ℝ) : rotGL θ ∈ TypeData.so2 := by
  rw [← rotUnit_eq_rotGL]
  exact Weight.rotUnit_mem_so2 θ

/-- Every element of `SO(2)` is a rotation `rotGL θ`. -/
theorem exists_eq_rotGL_of_mem_so2 {g : BinaryRealGL} (hg : g ∈ TypeData.so2) :
    ∃ θ : ℝ, g = rotGL θ := by
  obtain ⟨θ, hθ⟩ := Weight.exists_rotUnit_of_mem_so2 hg
  exact ⟨θ, hθ.trans (rotUnit_eq_rotGL θ)⟩

/-! ### Components of `atInfinity` and `atFinite` -/

private theorem realPart_combineGL_eq (r : BinaryRealGL) (f : BinaryFiniteGL) :
    realPart (combineGL r f) = r := by
  apply Units.ext
  ext i j
  rfl

private theorem finitePart_combineGL_eq (r : BinaryRealGL) (f : BinaryFiniteGL) :
    finitePart (combineGL r f) = f := by
  apply Units.ext
  ext i j
  rfl

private theorem realPart_atInfinity_eq (g : BinaryRealGL) : realPart (atInfinity g) = g :=
  realPart_combineGL_eq g 1

private theorem finitePart_atInfinity_eq (g : BinaryRealGL) : finitePart (atInfinity g) = 1 :=
  finitePart_combineGL_eq g 1

private theorem realPart_atFinite_eq (u : BinaryFiniteGL) : realPart (atFinite u) = 1 :=
  realPart_combineGL_eq 1 u

private theorem finitePart_atFinite_eq (u : BinaryFiniteGL) : finitePart (atFinite u) = u :=
  finitePart_combineGL_eq 1 u

/-! ### The weight `-k` character -/

theorem typeCharacterInv_apply (k : ℕ) (K : Subgroup BinaryFiniteGL) (c : TypeData.typeGroup K) :
    Weight.typeCharacterInv k K c = (TypeData.typeCharacter k K c)⁻¹ :=
  rfl

/-- The weight `k` character of an element of the type group with rotation `rotGL θ` at infinity
is `e^{i k θ}`. -/
theorem typeCharacter_rotGL {k : ℕ} {K : Subgroup BinaryFiniteGL} {θ : ℝ}
    (c : TypeData.typeGroup K) (h : realPart (c : BinaryAdelicGL) = rotGL θ) :
    TypeData.typeCharacter k K c = Complex.exp (((k : ℂ) * θ) * Complex.I) :=
  Weight.typeCharacter_of_realPart_eq k K c θ (h.trans (rotUnit_eq_rotGL θ).symm)

theorem typeCharacter_one {k : ℕ} {K : Subgroup BinaryFiniteGL} (c : TypeData.typeGroup K)
    (h : realPart (c : BinaryAdelicGL) = 1) : TypeData.typeCharacter k K c = 1 := by
  rw [typeCharacter_rotGL (θ := 0) c (by rw [h, rotGL_zero])]
  simp

/-! ### Lowest weight vectors -/

section Lowest

variable {k : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The map `e ↦ lowestMinus hk e` as a linear map. -/
def lowestMinusL (hk : 2 ≤ k) : E →ₗ[ℂ] BergmanSpace k E where
  toFun := lowestMinus hk
  map_add' e f := by
    refine eq_of_coeff hk (fun n => ?_) (fun n => ?_)
    · rw [coeffPlus_lowestMinus, coeffPlus_add, coeffPlus_lowestMinus, coeffPlus_lowestMinus,
        add_zero]
    · rw [coeffMinus_lowestMinus, coeffMinus_add, coeffMinus_lowestMinus,
        coeffMinus_lowestMinus]
      split_ifs
      · exact smul_add _ _ _
      · exact (add_zero 0).symm
  map_smul' c e := by
    show lowestMinus hk (c • e) = c • lowestMinus hk e
    refine eq_of_coeff hk (fun n => ?_) (fun n => ?_)
    · rw [coeffPlus_lowestMinus, coeffPlus_smul, coeffPlus_lowestMinus,
        smul_zero]
    · rw [coeffMinus_lowestMinus, coeffMinus_smul, coeffMinus_lowestMinus]
      split_ifs
      · exact smul_comm _ _ _
      · exact (smul_zero c).symm

theorem lowestMinusL_apply (hk : 2 ≤ k) (e : E) : lowestMinusL hk e = lowestMinus hk e :=
  rfl

end Lowest

variable {k : ℕ} (M : FiniteModel k)

/-- The finite-adelic action commutes with forming the lowest weight vector. -/
theorem finRep_lowestMinus (hk : 2 ≤ k) (u : BinaryFiniteGL) (e : M.E) :
    finRep k M.σ M.unitary u (lowestMinus hk e) = lowestMinus hk (M.σ u e) := by
  refine eq_of_coeff hk (fun n => ?_) (fun n => ?_)
  · rw [coeffPlus_finRep, coeffPlus_lowestMinus, coeffPlus_lowestMinus, map_zero]
  · rw [coeffMinus_finRep, coeffMinus_lowestMinus, coeffMinus_lowestMinus]
    split_ifs
    · rw [map_smul]
    · rw [map_zero]

/-- `lowestMinus hk e` lies in the type subspace as soon as `e` is fixed by `K`. -/
theorem lowestMinus_mem_typeSubspace (hk : 2 ≤ k) {K : Subgroup BinaryFiniteGL} {e : M.E}
    (he : e ∈ fixedSubmodule M.σ K) :
    lowestMinus hk e ∈ AbstractIrreducibility.typeSubspace (bergmanRep M)
      (TypeData.typeGroup K) (Weight.typeCharacterInv k K) := by
  rw [AbstractIrreducibility.mem_typeSubspace]
  intro c
  obtain ⟨hr, hf⟩ := TypeData.mem_typeGroup.1 c.property
  obtain ⟨θ, hθ⟩ := exists_eq_rotGL_of_mem_so2 hr
  have hfix : M.σ (finitePart c.val) e = e := he ⟨finitePart c.val, hf⟩
  rw [bergmanRep_apply, finRep_lowestMinus M hk, hfix, hθ, realRep_rot_lowestMinus hk,
    typeCharacterInv_apply, typeCharacter_rotGL c hθ, ← Complex.exp_neg, neg_mul]

/-! ### The converse -/

theorem realRep_rot_eq_of_mem_typeSubspace {K : Subgroup BinaryFiniteGL}
    {F : BergmanSpace k M.E}
    (hF : F ∈ AbstractIrreducibility.typeSubspace (bergmanRep M) (TypeData.typeGroup K)
      (Weight.typeCharacterInv k K)) (θ : ℝ) :
    realRep k M.E (rotGL θ) F = Complex.exp (-((k : ℂ) * θ) * Complex.I) • F := by
  have hmem : atInfinity (rotGL θ) ∈ TypeData.typeGroup K := by
    rw [TypeData.mem_typeGroup, realPart_atInfinity_eq, finitePart_atInfinity_eq]
    exact ⟨rotGL_mem_so2 θ, K.one_mem⟩
  have h : bergmanRep M (atInfinity (rotGL θ)) F =
      Weight.typeCharacterInv k K ⟨atInfinity (rotGL θ), hmem⟩ • F :=
    (AbstractIrreducibility.mem_typeSubspace _ _ _).1 hF ⟨atInfinity (rotGL θ), hmem⟩
  have hchar : Weight.typeCharacterInv k K ⟨atInfinity (rotGL θ), hmem⟩ =
      Complex.exp (-((k : ℂ) * θ) * Complex.I) := by
    rw [typeCharacterInv_apply, typeCharacter_rotGL (θ := θ) ⟨atInfinity (rotGL θ), hmem⟩
      (realPart_atInfinity_eq _), ← Complex.exp_neg, neg_mul]
  rw [bergmanRep_atInfinity] at h
  rw [h, hchar]

theorem finRep_eq_of_mem_typeSubspace {K : Subgroup BinaryFiniteGL}
    {F : BergmanSpace k M.E}
    (hF : F ∈ AbstractIrreducibility.typeSubspace (bergmanRep M) (TypeData.typeGroup K)
      (Weight.typeCharacterInv k K)) {u : BinaryFiniteGL} (hu : u ∈ K) :
    finRep k M.σ M.unitary u F = F := by
  have hmem : atFinite u ∈ TypeData.typeGroup K := by
    rw [TypeData.mem_typeGroup, realPart_atFinite_eq, finitePart_atFinite_eq]
    exact ⟨TypeData.so2.one_mem, hu⟩
  have h : bergmanRep M (atFinite u) F = Weight.typeCharacterInv k K ⟨atFinite u, hmem⟩ • F :=
    (AbstractIrreducibility.mem_typeSubspace _ _ _).1 hF ⟨atFinite u, hmem⟩
  have hchar : Weight.typeCharacterInv k K ⟨atFinite u, hmem⟩ = 1 := by
    rw [typeCharacterInv_apply, typeCharacter_one ⟨atFinite u, hmem⟩
      (realPart_atFinite_eq _), inv_one]
  rw [bergmanRep_atFinite] at h
  rw [h, hchar, one_smul]

theorem eq_zero_of_exp_eq_neg {E : Type*} [AddCommGroup E] [Module ℂ E] {A B : ℂ}
    (hAB : Complex.exp A = -Complex.exp B) {a : E}
    (h : Complex.exp A • a = Complex.exp B • a) : a = 0 := by
  rw [hAB, neg_smul] at h
  have h2 : (2 : ℂ) • (Complex.exp B • a) = 0 := by
    rw [two_smul]
    calc Complex.exp B • a + Complex.exp B • a
        = -(Complex.exp B • a) + Complex.exp B • a := by rw [h]
      _ = 0 := neg_add_cancel _
  have hx : Complex.exp B • a = 0 := (smul_eq_zero.mp h2).resolve_left two_ne_zero
  exact (smul_eq_zero.mp hx).resolve_left (Complex.exp_ne_zero B)

theorem coeffPlus_eq_zero_of_mem_typeSubspace (hk : 2 ≤ k) {K : Subgroup BinaryFiniteGL}
    {F : BergmanSpace k M.E}
    (hF : F ∈ AbstractIrreducibility.typeSubspace (bergmanRep M) (TypeData.typeGroup K)
      (Weight.typeCharacterInv k K)) (n : ℕ) : coeffPlus F n = 0 := by
  have hkn : (k : ℂ) + n ≠ 0 := by exact_mod_cast (show k + n ≠ 0 by omega)
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, (2 * ((k : ℂ) + n)) * (θ : ℂ) = (Real.pi : ℂ) :=
    ⟨Real.pi / (2 * ((k : ℝ) + n)), by push_cast; field_simp⟩
  have h : Complex.exp ((((k : ℂ) + 2 * n) * θ) * Complex.I) • coeffPlus F n =
      Complex.exp (-((k : ℂ) * θ) * Complex.I) • coeffPlus F n := by
    have h := congrArg (fun G => coeffPlus G n) (realRep_rot_eq_of_mem_typeSubspace M hF θ)
    simpa only [coeffPlus_realRep_rot, coeffPlus_smul] using h
  refine eq_zero_of_exp_eq_neg ?_ h
  have hsplit : (((k : ℂ) + 2 * n) * θ) * Complex.I =
      -((k : ℂ) * θ) * Complex.I + Real.pi * Complex.I := by
    linear_combination Complex.I * hθ
  rw [hsplit, Complex.exp_add, Complex.exp_pi_mul_I, mul_neg_one]

theorem coeffMinus_eq_zero_of_mem_typeSubspace {K : Subgroup BinaryFiniteGL}
    {F : BergmanSpace k M.E}
    (hF : F ∈ AbstractIrreducibility.typeSubspace (bergmanRep M) (TypeData.typeGroup K)
      (Weight.typeCharacterInv k K)) {n : ℕ} (hn : n ≠ 0) : coeffMinus F n = 0 := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, (2 * (n : ℂ)) * (θ : ℂ) = -(Real.pi : ℂ) :=
    ⟨-Real.pi / (2 * (n : ℝ)), by push_cast; field_simp⟩
  have h : Complex.exp (-(((k : ℂ) + 2 * n) * θ) * Complex.I) • coeffMinus F n =
      Complex.exp (-((k : ℂ) * θ) * Complex.I) • coeffMinus F n := by
    have h := congrArg (fun G => coeffMinus G n) (realRep_rot_eq_of_mem_typeSubspace M hF θ)
    simpa only [coeffMinus_realRep_rot, coeffMinus_smul] using h
  refine eq_zero_of_exp_eq_neg ?_ h
  have hsplit : -(((k : ℂ) + 2 * n) * θ) * Complex.I =
      -((k : ℂ) * θ) * Complex.I + Real.pi * Complex.I := by
    linear_combination (-Complex.I) * hθ
  rw [hsplit, Complex.exp_add, Complex.exp_pi_mul_I, mul_neg_one]

/-- An element of the type subspace is the lowest weight vector of its `0`-th lower coefficient,
which is fixed by `K`. -/
theorem eq_lowestMinus_of_mem_typeSubspace (hk : 2 ≤ k) {K : Subgroup BinaryFiniteGL}
    {F : BergmanSpace k M.E}
    (hF : F ∈ AbstractIrreducibility.typeSubspace (bergmanRep M) (TypeData.typeGroup K)
      (Weight.typeCharacterInv k K)) :
    coeffMinus F 0 ∈ fixedSubmodule M.σ K ∧
      F = lowestMinus hk (((-1 : ℂ) ^ k) • coeffMinus F 0) := by
  refine ⟨?_, ?_⟩
  · intro u
    rw [← coeffMinus_finRep M.σ M.unitary u.val F 0, finRep_eq_of_mem_typeSubspace M hF u.property]
  · refine eq_of_coeff hk (fun n => ?_) (fun n => ?_)
    · rw [coeffPlus_eq_zero_of_mem_typeSubspace M hk hF n, coeffPlus_lowestMinus]
    · by_cases hn : n = 0
      · subst hn
        have hneg : ((-1 : ℂ) ^ k) * ((-1 : ℂ) ^ k) = 1 := by
          rw [← mul_pow]
          norm_num
        rw [coeffMinus_lowestMinus, ite_eq_left rfl, smul_smul, hneg, one_smul]
      · rw [coeffMinus_eq_zero_of_mem_typeSubspace M hF hn, coeffMinus_lowestMinus, ite_eq_right hn]

/-! ### The type subspace -/

/-- The type subspace is the image of the `K`-fixed vectors under `e ↦ lowestMinus hk e`. -/
theorem typeSubspace_eq_map (hk : 2 ≤ k) (K : Subgroup BinaryFiniteGL) :
    AbstractIrreducibility.typeSubspace (bergmanRep M) (TypeData.typeGroup K)
      (Weight.typeCharacterInv k K) = (fixedSubmodule M.σ K).map (lowestMinusL hk) := by
  ext F
  rw [Submodule.mem_map]
  constructor
  · intro hF
    obtain ⟨hfix, hFeq⟩ := eq_lowestMinus_of_mem_typeSubspace M hk hF
    exact ⟨((-1 : ℂ) ^ k) • coeffMinus F 0, Submodule.smul_mem _ _ hfix, hFeq.symm⟩
  · rintro ⟨e, he, rfl⟩
    exact lowestMinus_mem_typeSubspace M hk he

/-- The type subspace of `bergmanRep M` for `typeGroup K` and weight `-k` is finite
dimensional. -/
theorem finiteDimensional_typeSubspace (hk : 2 ≤ k) {K : Subgroup BinaryFiniteGL}
    (hK : IsOpenCompact K) :
    FiniteDimensional ℂ (AbstractIrreducibility.typeSubspace (bergmanRep M)
      (TypeData.typeGroup K) (Weight.typeCharacterInv k K)) := by
  have := M.finiteDimensional K hK
  rw [typeSubspace_eq_map M hk K]
  infer_instance

/-- The type subspace is compression stable: the compression lands in the type subspace. -/
theorem compressionStable_typeSubspace [Fact (2 ≤ k)] (K : Subgroup BinaryFiniteGL) :
    AbstractIrreducibility.CompressionStable (bergmanRep M) (TypeData.typeGroup K)
      (Weight.typeCharacterInv k K)
      (AbstractIrreducibility.typeSubspace (bergmanRep M) (TypeData.typeGroup K)
        (Weight.typeCharacterInv k K)) :=
  fun _ _ _ => Submodule.starProjection_apply_mem _ _

end TernaryPeriodPolynomials.Regularity

end
