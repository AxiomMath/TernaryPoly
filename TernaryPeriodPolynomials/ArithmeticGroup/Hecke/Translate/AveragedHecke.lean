/-
  The FULL finite-coset average on source cochains and its right-`finiteLevel`
  behaviour.

  `conj_atFinite_rationalGroup` shows that conjugating `atFinite k` by
  `rationalGroup r` exposes the finite correction
  `(rationalFinite r)⁻¹ * k * rationalFinite r`.  Accordingly the whole average
  `translateSource` is right-`finiteLevel`-invariant *provided* every
  representative's finite part *normalizes* the level
  (`translateSource_level_normalizer`); this is a sufficient condition and no
  converse is proved here.  The stronger hypothesis `rationalFinite r ∈
  finiteLevel` (`translateSource_level`) is the special case
  `finiteLevel ⊆ N(finiteLevel)`.  No failure of the average when `hnorm` fails
  is claimed.
-/
module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.HeckeInvariance
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.CombineGL

@[expose] public section



open GeneralEisenstein
open Homogeneous Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.HeckeTranslate.AveragedHecke

variable {n : ℕ} {D : InducingData n} {side : Side}

/-- Equal on all coefficients implies equal homogeneous polynomials. -/
theorem poly_ext {p q : HomogeneousPoly n}
    (h : ∀ m : Fin 3 →₀ ℕ,
      p.val.coeff m = q.val.coeff m) : p = q :=
  Subtype.ext (MvPolynomial.ext _ _ h)

/-- Clause (a) of `IsSourceCocycle` gives full `finiteLevel` right-invariance of
an entire source cochain. -/
theorem source_level_invariance {c : SourceCochain n}
    (hc : IsSourceCocycle D side c) :
    ∀ (x : Fin 3 → RealGL3) (k : finiteLevel) (g : AdelicGL),
      c x (g * atFinite k.val) = c x g := by
  intro x k g
  apply poly_ext
  intro m
  exact (hc.1 x m).2.1 k g

/-- Splitting `rationalGroup r` into its archimedean and finite factors. -/
theorem rationalGroup_atInfinity_atFinite (r : RationalGL3) :
    rationalGroup r = atInfinity (GeneralLinearGroup.map (algebraMap ℚ ℝ) r) *
      atFinite (rationalFinite r) := by
  rw [HeckeInvariance.rationalGroup_eq r]
  show combineGL (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)
      (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) r) =
    combineGL (GeneralLinearGroup.map (algebraMap ℚ ℝ) r) 1 *
      combineGL 1 (rationalFinite r)
  rw [HeckeInvariance.combineGL_mul, mul_one, one_mul]
  rfl

/-- Moving `atFinite k` to the right of `rationalGroup r` exposes the finite
correction `k.val * rationalFinite r`. -/
theorem atFinite_mul_rationalGroup_shift (k : finiteLevel) (r : RationalGL3) :
    atFinite k.val * rationalGroup r =
      atInfinity (GeneralLinearGroup.map (algebraMap ℚ ℝ) r) *
        atFinite (k.val * rationalFinite r) := by
  rw [rationalGroup_atInfinity_atFinite r]
  show combineGL 1 k.val *
      (combineGL (GeneralLinearGroup.map (algebraMap ℚ ℝ) r) 1 *
        combineGL 1 (rationalFinite r)) =
    combineGL (GeneralLinearGroup.map (algebraMap ℚ ℝ) r) 1 *
      combineGL 1 (k.val * rationalFinite r)
  rw [← mul_assoc, HeckeInvariance.combineGL_mul, HeckeInvariance.combineGL_mul,
    mul_one, one_mul, mul_one]
  rw [HeckeInvariance.combineGL_mul, mul_one, one_mul]

/-- Moving `atFinite k` to the left of `rationalGroup r` exposes the same finite
correction `rationalFinite r * k.val`. -/
theorem atFinite_mul_rationalGroup_shift' (k : finiteLevel) (r : RationalGL3) :
    rationalGroup r * atFinite k.val =
      atInfinity (GeneralLinearGroup.map (algebraMap ℚ ℝ) r) *
        atFinite (rationalFinite r * k.val) := by
  rw [rationalGroup_atInfinity_atFinite r]
  show (combineGL (GeneralLinearGroup.map (algebraMap ℚ ℝ) r) 1 *
        combineGL 1 (rationalFinite r)) * combineGL 1 k.val =
    combineGL (GeneralLinearGroup.map (algebraMap ℚ ℝ) r) 1 *
      combineGL 1 (rationalFinite r * k.val)
  rw [mul_assoc, HeckeInvariance.combineGL_mul, HeckeInvariance.combineGL_mul,
    mul_one, one_mul, mul_one]
  rw [HeckeInvariance.combineGL_mul, mul_one, one_mul]

/-- Conjugating `atFinite k` by `rationalGroup r` produces `atFinite` of the
finite correction `(rationalFinite r)⁻¹ * k * rationalFinite r`. -/
theorem conj_atFinite_rationalGroup (k : finiteLevel) (r : RationalGL3) :
    (rationalGroup r)⁻¹ * atFinite k.val * rationalGroup r =
      atFinite ((rationalFinite r)⁻¹ * k.val * rationalFinite r) := by
  rw [mul_assoc, HeckeInvariance.atFinite_mul_rationalGroup]
  group

/-- **Averaged covariance, sufficient form.**  If every representative's finite
part normalizes the fixed congruence level,
`(rationalFinite r)⁻¹ k (rationalFinite r) ∈ finiteLevel` for all
`k : finiteLevel`, then the whole finite-coset average `translateSource` is
right-`finiteLevel`-invariant.  This is a *sufficient* condition proved term
by term; no converse (necessity of normalizing the whole average) is claimed,
and no failure of the average when this hypothesis is dropped is asserted. -/
theorem translateSource_level_normalizer (t : HeckeCorrespondence) {c : SourceCochain n}
    (hc : IsSourceCocycle D side c)
    (hnorm : ∀ r ∈ t.representatives, ∀ k : finiteLevel,
      (rationalFinite r)⁻¹ * k.val * rationalFinite r ∈ finiteLevel)
    (x : Fin 3 → RealGL3) (k : finiteLevel) (g : AdelicGL) :
    HeckeInvariance.translateSource D t c x (g * atFinite k.val) =
      HeckeInvariance.translateSource D t c x g := by
  simp only [HeckeInvariance.translateSource]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hκ : (rationalFinite r)⁻¹ * k.val * rationalFinite r ∈ finiteLevel := hnorm r hr k
  have harg :
      c (fun i => (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x i)
          (g * atFinite k.val * rationalGroup r) =
        c (fun i => (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x i)
          (g * rationalGroup r) := by
    have h1 : g * atFinite k.val * rationalGroup r =
        (g * rationalGroup r) *
          atFinite ((rationalFinite r)⁻¹ * k.val * rationalFinite r) := by
      rw [← conj_atFinite_rationalGroup]
      group
    rw [h1, source_level_invariance hc _ ⟨_, hκ⟩ _]
  rw [harg]

/-- The exact `finiteLevel` condition that makes a single transported term invariant. -/
theorem rationalFinite_mem_iff (r : RationalGL3) :
    rationalFinite r ∈ finiteLevel ↔
      ∃ k : finiteLevel, rationalFinite r = k.val :=
  ⟨fun h => ⟨⟨rationalFinite r, h⟩, rfl⟩, fun ⟨k, hk⟩ => hk ▸ k.property⟩

/-- **Checked averaged covariance.**  If every representative's rational finite
part lies in the fixed congruence level, the whole finite-coset average
`translateSource` is right-`finiteLevel`-invariant. -/
theorem translateSource_level (t : HeckeCorrespondence) {c : SourceCochain n}
    (hc : IsSourceCocycle D side c)
    (hmem : ∀ r ∈ t.representatives, rationalFinite r ∈ finiteLevel)
    (x : Fin 3 → RealGL3) (k : finiteLevel) (g : AdelicGL) :
    HeckeInvariance.translateSource D t c x (g * atFinite k.val) =
      HeckeInvariance.translateSource D t c x g := by
  simp only [HeckeInvariance.translateSource]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hk : (k.val * rationalFinite r) ∈ finiteLevel :=
    finiteLevel.mul_mem k.property (hmem r hr)
  have hrf : rationalFinite r ∈ finiteLevel := hmem r hr
  have harg :
      c (fun i => (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x i)
          (g * atFinite k.val * rationalGroup r) =
        c (fun i => (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x i)
          (g * rationalGroup r) := by
    have h1 : g * atFinite k.val * rationalGroup r =
        (g * atInfinity (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)) *
          atFinite (k.val * rationalFinite r) := by
      rw [mul_assoc, atFinite_mul_rationalGroup_shift, ← mul_assoc]
    have h2 : g * rationalGroup r =
        (g * atInfinity (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)) *
          atFinite (rationalFinite r) := by
      rw [mul_assoc, rationalGroup_atInfinity_atFinite, ← mul_assoc]
    rw [h1, h2,
      source_level_invariance hc _ ⟨_, hk⟩ _,
      source_level_invariance hc _ ⟨_, hrf⟩ _]
  rw [harg]

/-- **Exact evaluation comparison.**  If a rational cycle `z` evaluates a source
cocycle `c`, then the canonical finite-coset Hecke translate
`Helpers.cocycleAction ... t z` evaluates the adelic finite-coset translate
`HeckeInvariance.translateSource D t c`.  This matches the literal arithmetic
Hecke formula on the `H²` side with the source side term by term; because the
source translation and the rational Hecke translation are the same finite sum,
no coboundary correction is required. -/
theorem evaluates_cocycleAction (D : InducingData n) (side : Side)
    (t : HeckeCorrespondence) {c : SourceCochain n}
    {z : MaximalCycles n D.chi side} (heval : Evaluates D side c z) :
    Evaluates D side (HeckeInvariance.translateSource D t c)
      (Helpers.cocycleAction
        (flagRepresentation (rationalCoefficientComponent n D.chi) side) t z) := by
  refine HeckeInvariance.evaluates_translate D side t heval ?_
  intro x
  unfold heckeCochain
  rfl

end TernaryPeriodPolynomials.HeckeTranslate.AveragedHecke

end

namespace TernaryPeriodPolynomials.HeckeTranslate.AveragedHecke

/-- A representative in `rationalLevel` has its rational finite part in the fixed
congruence level.  This is the positive half of the exact relationship between
`rationalLevel` and `finiteLevel`. -/
theorem rationalFinite_mem_of_rationalLevel {r : RationalGL3} (hr : r ∈ rationalLevel) :
    rationalFinite r ∈ finiteLevel := by
  rw [rationalLevel] at hr
  rcases MonoidHom.mem_range.mp hr with ⟨a, ha⟩
  subst ha
  have hhom : (algebraMap ℚ FiniteAdeles).comp (Int.castRingHom ℚ) =
      integralEmbedding.comp (Int.castRingHom IntegralAdeles) := by
    ext z
    simp
  have hred : integralReduction.comp (Int.castRingHom IntegralAdeles) =
      Int.castRingHom (ZMod 3) := by
    ext z
    simp
  have hval2 : rationalFinite (rationalInclusion a) =
      GeneralLinearGroup.map integralEmbedding
        (GeneralLinearGroup.map (Int.castRingHom IntegralAdeles) a.val) := by
    apply GeneralLinearGroup.ext
    intro i j
    simp only [rationalFinite, rationalInclusion, MonoidHom.comp_apply,
      Subgroup.coe_subtype, GeneralLinearGroup.map_apply]
    exact RingHom.congr_fun hhom (a.val.val i j)
  have hkey : GeneralLinearGroup.map integralReduction
        (GeneralLinearGroup.map (Int.castRingHom IntegralAdeles) a.val) =
      reductionThree a.val := by
    rw [reductionThree]
    apply GeneralLinearGroup.ext
    intro i j
    simp only [GeneralLinearGroup.map_apply]
    exact RingHom.congr_fun hred (a.val.val i j)
  rw [hval2, finiteLevel]
  refine Subgroup.mem_map.mpr
    ⟨GeneralLinearGroup.map (Int.castRingHom IntegralAdeles) a.val, ?_, rfl⟩
  rw [Subgroup.mem_comap, hkey]
  exact a.property


/-- **A concrete criterion for the level-normalizer hypothesis.**  If the base
element's finite part already lies in the fixed level (`rationalFinite t.g ∈
finiteLevel`), then so does every representative's: `r = a · g · b` with
`a, b ∈ rationalLevel`, and `rationalFinite` is multiplicative with
`rationalFinite (rationalLevel) ⊆ finiteLevel`. -/
theorem rationalFinite_mem_finiteLevel_of_representative (t : HeckeCorrespondence)
    (hg : rationalFinite t.g ∈ finiteLevel) :
    ∀ r ∈ t.representatives, rationalFinite r ∈ finiteLevel := by
  intro r hr
  obtain ⟨a, b, rfl⟩ := t.inDoubleCoset r hr
  rw [map_mul, map_mul]
  exact finiteLevel.mul_mem
    (finiteLevel.mul_mem (rationalFinite_mem_of_rationalLevel a.property) hg)
    (rationalFinite_mem_of_rationalLevel b.property)

/-- **Finite-level invariance of the Hecke translate, with the normalizer
hypothesis discharged.**  If the base element's finite part lies in the level,
then (by `rationalFinite_mem_finiteLevel_of_representative`) the whole translated
cochain is right-`finiteLevel`-invariant. -/
theorem translateSource_level_of_base_mem {n : ℕ} {D : InducingData n} {side : Side}
    (t : HeckeCorrespondence) {c : SourceCochain n} (hc : IsSourceCocycle D side c)
    (hg : rationalFinite t.g ∈ finiteLevel)
    (x : Fin 3 → RealGL3) (k : finiteLevel) (g : AdelicGL) :
    HeckeInvariance.translateSource D t c x (g * atFinite k.val) =
      HeckeInvariance.translateSource D t c x g :=
  translateSource_level t hc (rationalFinite_mem_finiteLevel_of_representative t hg) x k g
end TernaryPeriodPolynomials.HeckeTranslate.AveragedHecke
