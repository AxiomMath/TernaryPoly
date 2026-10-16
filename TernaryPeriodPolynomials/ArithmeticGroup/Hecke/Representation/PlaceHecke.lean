module

public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Representation.LocalHecke
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Representation.SphericalHecke
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Finite.PlaceIntegralEmbedding
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Finite.IntegralLevel

@[expose] public section


/-!
# Hecke operators at one place, at arbitrary level elsewhere

For a finite place `v`, embed `GL₂(ℚ_v)` and `GL₂(𝒪_v)` into `GL₂(𝔸)`. For every subgroup `K'`
supported away from `v` and every `x ∈ GL₂(ℚ_v)`, the Hecke operator of the local double coset
`GL₂(𝒪_v) x GL₂(𝒪_v)` acts by a scalar on the vectors of a `CuspidalRepresentation` fixed by
`GL₂(𝒪_v) ⊔ K'`.

The local Cartan property and the finiteness of local double cosets are derived from the global
ones (`transpose_cartan`, `sphericalFinite_finiteQuotient`) by evaluating components.

Original work (AxiomDeep, Claude Opus 5.5).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace TernaryPeriodPolynomials.RepresentationTheory

variable (v : FinitePlace)

/-- `GL₂(𝒪_v) → GL₂(ℚ_v)`. -/
def localIntegral : GeneralLinearGroup (Fin 2) (v.adicCompletionIntegers ℚ) →*
    GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ) :=
  GeneralLinearGroup.map (v.adicCompletionIntegers ℚ).toSubring.subtype

/-- `GL₂(ℚ_v)` inside `GL₂(𝔸_f)`. -/
def placeGroup : Subgroup BinaryFiniteGL := (finiteAtPlaceGL 2 v).range

/-- `GL₂(𝒪_v)` inside `GL₂(𝔸_f)`. -/
def placeLevel : Subgroup BinaryFiniteGL := ((finiteAtPlaceGL 2 v).comp (localIntegral v)).range

theorem placeLevel_le_placeGroup : placeLevel v ≤ placeGroup v := by
  rintro _ ⟨k, rfl⟩; exact ⟨_, rfl⟩

theorem placeLevel_le_spherical : placeLevel v ≤ sphericalFinite := by
  rintro _ ⟨k, rfl⟩
  exact finiteAtPlaceGL_integral 2 v k

variable {v}

/-- Components of `GL₂(Ẑ)` at `v` are integral. -/
theorem eval_mem_localIntegral {k : BinaryFiniteGL} (hk : k ∈ sphericalFinite) :
    GeneralLinearGroup.map (finiteEvaluation v) k ∈ (localIntegral v).range := by
  obtain ⟨k', rfl⟩ := hk
  refine ⟨GeneralLinearGroup.map (Pi.evalRingHom _ v) k', ?_⟩
  apply Units.ext
  funext i j
  rfl

/-- Elements of `GL₂(Ẑ)` supported at `v` lie in `GL₂(𝒪_v)`. -/
theorem mem_placeLevel_of_support {k : BinaryFiniteGL} (hk : k ∈ sphericalFinite)
    (hsupp : ∀ w, w ≠ v → GeneralLinearGroup.map (finiteEvaluation w) k = 1) :
    k ∈ placeLevel v := by
  obtain ⟨k₀, hk₀⟩ := eval_mem_localIntegral (v := v) hk
  refine ⟨k₀, ?_⟩
  apply finiteGeneralLinearGroup_ext
  intro w
  by_cases hw : w = v
  · subst hw
    rw [MonoidHom.comp_apply, finiteAtPlaceGL_same, hk₀]
  · rw [MonoidHom.comp_apply, finiteAtPlaceGL_away 2 v _ w hw, hsupp w hw]

theorem eval_away_placeGroup {x : BinaryFiniteGL} (hx : x ∈ placeGroup v) (w : FinitePlace)
    (hw : w ≠ v) : GeneralLinearGroup.map (finiteEvaluation w) x = 1 := by
  obtain ⟨y, rfl⟩ := hx
  exact finiteAtPlaceGL_away 2 v y w hw

theorem transposeGL_finiteAtPlace (y : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) :
    transposeGL (finiteAtPlaceGL 2 v y) = finiteAtPlaceGL 2 v (transposeGL y) := by
  apply finiteGeneralLinearGroup_ext
  intro w
  rw [← transposeGL_map]
  by_cases hw : w = v
  · subst hw; rw [finiteAtPlaceGL_same, finiteAtPlaceGL_same]
  · rw [finiteAtPlaceGL_away 2 v _ w hw, finiteAtPlaceGL_away 2 v _ w hw]
    apply Units.ext; simp

theorem transposeGL_placeLevel {k : BinaryFiniteGL} (hk : k ∈ placeLevel v) :
    transposeGL k ∈ placeLevel v := by
  obtain ⟨k', rfl⟩ := hk
  refine ⟨transposeGL k', ?_⟩
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, transposeGL_finiteAtPlace, localIntegral,
    transposeGL_map]

/-- **Local Cartan property** at `v`. -/
theorem local_transpose_cartan (y : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) :
    ∃ a b : placeLevel v,
      transposeGL (finiteAtPlaceGL 2 v y) = a.val * finiteAtPlaceGL 2 v y * b.val := by
  obtain ⟨a, b, hab⟩ := transpose_cartan (finiteAtPlaceGL 2 v y)
  obtain ⟨a₀, ha₀⟩ := eval_mem_localIntegral (v := v) a.property
  obtain ⟨b₀, hb₀⟩ := eval_mem_localIntegral (v := v) b.property
  refine ⟨⟨_, ⟨a₀, rfl⟩⟩, ⟨_, ⟨b₀, rfl⟩⟩, ?_⟩
  apply finiteGeneralLinearGroup_ext
  intro w
  by_cases hw : w = v
  · subst hw
    have := congrArg (GeneralLinearGroup.map (finiteEvaluation w)) hab
    simp only [map_mul] at this ⊢
    rw [this, MonoidHom.comp_apply, MonoidHom.comp_apply, finiteAtPlaceGL_same, finiteAtPlaceGL_same,
      ha₀, hb₀, finiteAtPlaceGL_same]
  · simp only [map_mul, MonoidHom.comp_apply]
    rw [← transposeGL_map, finiteAtPlaceGL_away 2 v _ w hw, finiteAtPlaceGL_away 2 v _ w hw,
      finiteAtPlaceGL_away 2 v _ w hw]
    apply Units.ext; simp

/-- **Finiteness of local double cosets.** -/
theorem placeLevel_finiteQuotient (x : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) :
    Finite (placeLevel v ⧸ conjIntersection (placeLevel v) (finiteAtPlaceGL 2 v x)) := by
  set γ := finiteAtPlaceGL 2 v x
  have hγ : γ ∈ placeGroup v := ⟨x, rfl⟩
  let F : placeLevel v ⧸ conjIntersection (placeLevel v) γ →
      sphericalFinite ⧸ conjIntersection sphericalFinite γ :=
    Quotient.map' (Subgroup.inclusion (placeLevel_le_spherical v)) (by
      intro a b hab
      rw [QuotientGroup.leftRel_apply] at hab ⊢
      have h := mem_conjIntersection.mp hab
      apply mem_conjIntersection.mpr
      exact placeLevel_le_spherical v h)
  apply Finite.of_injective F
  intro c d hcd
  induction c using Quotient.inductionOn' with | h a => ?_
  induction d using Quotient.inductionOn' with | h b => ?_
  apply Quotient.sound'
  have hcd' : (QuotientGroup.mk (Subgroup.inclusion (placeLevel_le_spherical v) a) :
      sphericalFinite ⧸ conjIntersection sphericalFinite γ) =
      QuotientGroup.mk (Subgroup.inclusion (placeLevel_le_spherical v) b) := hcd
  have hmem := mem_conjIntersection.mp (QuotientGroup.eq.mp hcd')
  rw [QuotientGroup.leftRel_apply]
  apply mem_conjIntersection.mpr
  apply mem_placeLevel_of_support hmem
  intro w hw
  have haw := eval_away_placeGroup (placeLevel_le_placeGroup v a.property) w hw
  have hbw := eval_away_placeGroup (placeLevel_le_placeGroup v b.property) w hw
  have hγw := eval_away_placeGroup hγ w hw
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion, map_mul, map_inv,
    haw, hbw, hγw, inv_one, mul_one]

/-- `GL₂(ℚ_v)` and `GL₂(𝒪_v)` inside `GL₂(𝔸)`. -/
def placeGroupA (v : FinitePlace) : Subgroup BinaryAdelicGL := (placeGroup v).map atFiniteHom
def placeLevelA (v : FinitePlace) : Subgroup BinaryAdelicGL := (placeLevel v).map atFiniteHom

/-- The local double coset of `x ∈ GL₂(ℚ_v)` inside `GL₂(𝔸)`. -/
def placeDoubleCoset (x : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) :
    DoubleCoset (placeLevelA v) :=
  haveI := placeLevel_finiteQuotient x
  (DoubleCoset.ofFinite (placeLevel v) (finiteAtPlaceGL 2 v x)).map atFiniteHom atFiniteHom_injective

theorem placeDoubleCoset_g (x : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) :
    (placeDoubleCoset x).g = atFinite (finiteAtPlaceGL 2 v x) := rfl

/-- The transpose is a Gelfand involution for `GL₂(𝒪_v)`, Cartan on `GL₂(ℚ_v)`. -/
def placeGelfand (v : FinitePlace) : GelfandInvolution (placeLevelA v) where
  ι := transposeGL
  map_mul := transposeGL_mul
  invol := transposeGL_transposeGL
  mem := by
    rintro _ ⟨k, hk, rfl⟩
    exact ⟨transposeGL k, transposeGL_placeLevel hk, (transposeGL_atFinite k).symm⟩
  F := placeGroupA v
  le := Subgroup.map_mono (placeLevel_le_placeGroup v)
  memF := by
    rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
    exact ⟨_, ⟨transposeGL y, rfl⟩, by
      change atFinite (finiteAtPlaceGL 2 v (transposeGL y)) = transposeGL (atFinite (finiteAtPlaceGL 2 v y))
      rw [transposeGL_atFinite, transposeGL_finiteAtPlace]⟩
  cartan := by
    rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
    obtain ⟨a, b, hab⟩ := local_transpose_cartan y
    refine ⟨⟨atFinite a.val, ⟨a.val, a.property, rfl⟩⟩, ⟨atFinite b.val, ⟨b.val, b.property, rfl⟩⟩, ?_⟩
    change transposeGL (atFinite (finiteAtPlaceGL 2 v y)) =
      atFinite a.val * atFinite (finiteAtPlaceGL 2 v y) * atFinite b.val
    rw [transposeGL_atFinite, hab, HeckeTranslate.HeckeInvariance.atFinite_mul,
      HeckeTranslate.HeckeInvariance.atFinite_mul]

/-- Finite elements trivial at `v` commute with `GL₂(ℚ_v)`. -/
theorem atFinite_away_commute {w : BinaryFiniteGL}
    (hw : GeneralLinearGroup.map (finiteEvaluation v) w = 1) {y : BinaryAdelicGL}
    (hy : y ∈ placeGroupA v) : atFinite w * y = y * atFinite w := by
  obtain ⟨_, ⟨z, rfl⟩, rfl⟩ := hy
  change atFinite w * atFinite (finiteAtPlaceGL 2 v z) = atFinite (finiteAtPlaceGL 2 v z) * atFinite w
  rw [HeckeTranslate.HeckeInvariance.atFinite_mul, HeckeTranslate.HeckeInvariance.atFinite_mul]
  congr 1
  apply finiteGeneralLinearGroup_ext
  intro w'
  rw [map_mul, map_mul]
  by_cases h : w' = v
  · subst h; rw [hw, finiteAtPlaceGL_same, one_mul, mul_one]
  · rw [finiteAtPlaceGL_away 2 v z w' h, one_mul, mul_one]

/-- Every element of `GL₂(𝔸)` is a product of a factor commuting with `GL₂(ℚ_v)` and an element of
`GL₂(ℚ_v)`. -/
theorem place_decomp (h : BinaryAdelicGL) : ∃ u x : BinaryAdelicGL,
    h = u * x ∧ x ∈ placeGroupA v ∧ ∀ y ∈ placeGroupA v, u * y = y * u := by
  set r := GeneralLinearGroup.map (RingHom.fst ℝ FiniteAdeles) h
  set f := GeneralLinearGroup.map (RingHom.snd ℝ FiniteAdeles) h
  set fv := finiteAtPlaceGL 2 v (GeneralLinearGroup.map (finiteEvaluation v) f)
  refine ⟨atInfinity r * atFinite (f * fv⁻¹), atFinite fv, ?_, ⟨fv, ⟨_, rfl⟩, rfl⟩, ?_⟩
  · rw [mul_assoc, HeckeTranslate.HeckeInvariance.atFinite_mul, inv_mul_cancel_right]
    exact binary_real_finite h
  · intro y hy
    have hw : GeneralLinearGroup.map (finiteEvaluation v) (f * fv⁻¹) = 1 := by
      rw [map_mul, map_inv, finiteAtPlaceGL_same, mul_inv_cancel]
    obtain ⟨_, ⟨z, rfl⟩, rfl⟩ := hy
    rw [mul_assoc, atFinite_away_commute hw ⟨_, ⟨z, rfl⟩, rfl⟩, ← mul_assoc, ← mul_assoc]
    congr 1
    exact (HeckeTranslate.HeckeInvariance.atFinite_comm_atInfinity _ r).symm

/-- **Local Hecke operators at `v` act by scalars** on the vectors of any `CuspidalRepresentation`
fixed by `GL₂(𝒪_v) ⊔ K'`, for every level `K'` commuting with `GL₂(ℚ_v)` (i.e. supported away
from `v`). -/
theorem placeHecke_scalar (σ : CuspidalRepresentation) (K' : Subgroup BinaryAdelicGL)
    (hK' : ∀ k ∈ K', ∀ x ∈ placeGroupA v, k * x = x * k)
    (x : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) :
    ∃ z : ℂ, ∀ vec ∈ fixedVectors σ (placeLevelA v ⊔ K'),
      heckeOperator σ (placeDoubleCoset x) vec = z • vec := by
  apply localHecke_scalar (placeLevelA v) K' (placeGroupA v)
    (Subgroup.map_mono (placeLevel_le_placeGroup v)) hK' place_decomp (placeGelfand v) le_rfl
  · rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
    exact ⟨placeDoubleCoset y, rfl⟩
  · exact ⟨_, ⟨x, rfl⟩, rfl⟩

/-- **The compressed local Hecke algebra at `v` acts by scalars**: every finite combination of
compressions of elements of `GL₂(ℚ_v)` is a scalar on `σ.H^(GL₂(𝒪_v) ⊔ K')`. -/
theorem placeCombination_scalar (σ : CuspidalRepresentation) (K' : Subgroup BinaryAdelicGL)
    (hK' : ∀ k ∈ K', ∀ x ∈ placeGroupA v, k * x = x * k)
    {ι : Type*} (S : Finset ι) (c : ι → ℂ) (x : ι → GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) :
    ∃ z : ℂ, ∀ w, (∑ i ∈ S, c i • compression σ (placeLevelA v ⊔ K')
      (atFinite (finiteAtPlaceGL 2 v (x i)))) w = z • w :=
  localCombination_scalar (placeLevelA v) K' (placeGroupA v)
    (Subgroup.map_mono (placeLevel_le_placeGroup v)) hK' place_decomp (placeGelfand v) le_rfl
    (by rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩; exact ⟨placeDoubleCoset y, rfl⟩) S c _
    (fun i _ => ⟨_, ⟨x i, rfl⟩, rfl⟩)

end TernaryPeriodPolynomials.RepresentationTheory
