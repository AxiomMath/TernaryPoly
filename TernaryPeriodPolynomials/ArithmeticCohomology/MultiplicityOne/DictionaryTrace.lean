module

public import TernaryPeriodPolynomials.ArithmeticCohomology.MultiplicityOne.DictionaryHeckeFixed
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Petersson.Domain

@[expose] public section


/-!
# The trace of a level-three vector to level one

Let `rep i`, `i ∈ {∞, 0, 1, 2}`, be the representatives `1, S, ST, ST²` of `Γ₀(3)\SL₂(ℤ)`.  For a
classical level-three vector `v` put `traceVector σ v = ∑ᵢ cuspFiniteRationalSlash σ (rep i) v`.

* Its scalar function is `∑ᵢ f ∣[k] rep i`, the classical trace of `f = cuspScalarWeightedLinear σ
  halfWeight 1 v` (`traceVector_scalar`).
* It is `GL₂(ℤ̂)`-fixed (`traceVector_spherical`): the vector `v` is fixed by the preimage
  `borelThree` of the upper triangular matrices modulo three (the sign of the diagonal is the
  scalar `-1`, which fixes `v`), the cosets `rep i⁻¹ · borelThree` are exactly `GL₂(ℤ̂)/borelThree`
  (`traceEquiv`), and left multiplication permutes them.
* Consequently the trace vanishes when `σ` is not spherical
  (`traceVector_eq_zero_of_not_spherical`).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.LevelThree
open TernaryPeriodPolynomials.LevelThree.LevelThreePeterssonDomain (rep)

namespace TernaryPeriodPolynomials.MultiplicityOne

/-! ## Reductions modulo three of integral matrices -/

theorem reduction_mapGL_entry (γ : SpecialLinearGroup (Fin 2) ℤ) (i j : Fin 2) :
    (GeneralLinearGroup.map integralReduction
      (SpecialLinearGroup.mapGL IntegralAdeles γ)).val i j = ((γ.val i j : ℤ) : ZMod 3) := by
  simp only [GeneralLinearGroup.map_apply, SpecialLinearGroup.mapGL_coe_matrix,
    SpecialLinearGroup.map_apply_coe]
  change integralReduction (algebraMap ℤ IntegralAdeles (γ.val i j)) = _
  simp

theorem reduction_rep_mul_lowerLeft (j : Option (Fin 3))
    (X : GeneralLinearGroup (Fin 2) IntegralAdeles) :
    (GeneralLinearGroup.map integralReduction
      (SpecialLinearGroup.mapGL IntegralAdeles (rep j) * X)).val 1 0 =
      LevelThreePeterssonDomain.cond j ((GeneralLinearGroup.map integralReduction X).val 0 0)
        ((GeneralLinearGroup.map integralReduction X).val 1 0) := by
  rw [map_mul, GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
    reduction_mapGL_entry, reduction_mapGL_entry]
  cases j with
  | none => simp [LevelThreePeterssonDomain.rep, LevelThreePeterssonDomain.cond]
  | some j =>
    simp [LevelThreePeterssonDomain.rep, LevelThreePeterssonDomain.cond,
      LevelThreePeterssonDomain.shearS]

/-! ## The preimage of the Borel subgroup modulo three -/

/-- The elements of `GL₂(ℤ̂)` which are upper triangular modulo three. -/
def borelThree : Subgroup (GeneralLinearGroup (Fin 2) IntegralAdeles) where
  carrier := {b | (GeneralLinearGroup.map integralReduction b).val 1 0 = 0}
  mul_mem' := by
    intro a b ha hb
    change (GeneralLinearGroup.map integralReduction a).val 1 0 = 0 at ha
    change (GeneralLinearGroup.map integralReduction b).val 1 0 = 0 at hb
    change (GeneralLinearGroup.map integralReduction (a * b)).val 1 0 = 0
    rw [map_mul, GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, ha, hb]
    simp
  one_mem' := by
    change (GeneralLinearGroup.map integralReduction 1).val 1 0 = 0
    rw [map_one]
    simp
  inv_mem' := by
    intro a ha
    change (GeneralLinearGroup.map integralReduction a).val 1 0 = 0 at ha
    change (GeneralLinearGroup.map integralReduction a⁻¹).val 1 0 = 0
    rw [map_inv]
    generalize GeneralLinearGroup.map integralReduction a = g at ha ⊢
    have det_ne := GeneralLinearGroup.det_ne_zero g
    have h11 : g.val 1 1 ≠ 0 := by
      intro h
      apply det_ne
      rw [Matrix.det_fin_two, ha, h]
      ring
    have identity : (g * g⁻¹).val 1 0 = (1 : GeneralLinearGroup (Fin 2) (ZMod 3)).val 1 0 := by
      rw [mul_inv_cancel]
    rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, ha, zero_mul, zero_add] at identity
    have one_eq : (1 : GeneralLinearGroup (Fin 2) (ZMod 3)).val 1 0 = 0 := by simp
    rw [one_eq] at identity
    exact (mul_eq_zero.mp identity).resolve_left h11

theorem mem_borelThree {b : GeneralLinearGroup (Fin 2) IntegralAdeles} :
    b ∈ borelThree ↔ (GeneralLinearGroup.map integralReduction b).val 1 0 = 0 := Iff.rfl

/-! ## Level-three vectors are fixed by `borelThree` -/

theorem levelThree_fixed_of_borel (σ : CuspidalRepresentation) (halfWeight : ℤ) (v : σ.smooth)
    (hv : v.val ∈ levelThreeValues σ)
    (rotation : ∀ angle : Circle, σ.π (atInfinity (binaryRotations angle)) v.val =
      (angle : ℂ) ^ (2 * halfWeight) • v.val)
    (b : GeneralLinearGroup (Fin 2) IntegralAdeles) (hb : b ∈ borelThree) :
    σ.π (atFinite (GeneralLinearGroup.map integralEmbedding b)) v.val = v.val := by
  have e10 : (GeneralLinearGroup.map integralReduction b).val 1 0 = 0 := hb
  have det_ne := GeneralLinearGroup.det_ne_zero (GeneralLinearGroup.map integralReduction b)
  have e11_ne : (GeneralLinearGroup.map integralReduction b).val 1 1 ≠ 0 := by
    intro h
    apply det_ne
    rw [Matrix.det_fin_two, e10, h]
    ring
  have cases_three : ∀ x : ZMod 3, x ≠ 0 → x = 1 ∨ x = -1 := by decide
  rcases cases_three _ e11_ne with e | e
  · exact hv b (And.intro e10 e)
  · have level := planeLeviLevel_mul_negOne e10 e
    have fixed := hv _ level
    rw [map_mul, atFinite_mul, map_mul, Module.End.mul_apply,
      levelThree_negOne_fixed σ halfWeight v rotation] at fixed
    exact fixed

/-! ## The cosets `rep i⁻¹ · borelThree` -/

/-- The integral matrix of `(rep i)⁻¹`. -/
def rinv (i : Option (Fin 3)) : GeneralLinearGroup (Fin 2) IntegralAdeles :=
  SpecialLinearGroup.mapGL IntegralAdeles (rep i)⁻¹

/-- The coset of `(rep i)⁻¹` in `GL₂(ℤ̂)/borelThree`. -/
def traceCoset (i : Option (Fin 3)) : GeneralLinearGroup (Fin 2) IntegralAdeles ⧸ borelThree :=
  QuotientGroup.mk (rinv i)

theorem traceCoset_injective : Function.Injective traceCoset := by
  intro i i' h
  unfold traceCoset at h
  have member := QuotientGroup.eq.mp h
  have equal : (rinv i)⁻¹ * rinv i' =
      SpecialLinearGroup.mapGL IntegralAdeles (rep i * (rep i')⁻¹) := by
    simp only [rinv, map_mul, map_inv, inv_inv]
  rw [equal] at member
  have h10 : (((rep i * (rep i')⁻¹) 1 0 : ℤ) : ZMod 3) = 0 := by
    have reduced : (GeneralLinearGroup.map integralReduction
      (SpecialLinearGroup.mapGL IntegralAdeles (rep i * (rep i')⁻¹))).val 1 0 = 0 := member
    rwa [reduction_mapGL_entry] at reduced
  have h10' : (((rep i' * (rep i')⁻¹) 1 0 : ℤ) : ZMod 3) = 0 := by simp
  exact LevelThreePeterssonDomain.rep_unique _ i i' h10 h10'

theorem traceCoset_surjective : Function.Surjective traceCoset := by
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  have not_zero : ¬((GeneralLinearGroup.map integralReduction g).val 0 0 = 0 ∧
      (GeneralLinearGroup.map integralReduction g).val 1 0 = 0) := by
    rintro ⟨h0, h1⟩
    apply GeneralLinearGroup.det_ne_zero (GeneralLinearGroup.map integralReduction g)
    rw [Matrix.det_fin_two, h0, h1]
    ring
  obtain ⟨i, hi⟩ := LevelThreePeterssonDomain.cond_exists _ _ not_zero
  refine ⟨i, ?_⟩
  unfold traceCoset
  rw [QuotientGroup.eq]
  have equal : (rinv i)⁻¹ * g = SpecialLinearGroup.mapGL IntegralAdeles (rep i) * g := by
    simp [rinv]
  rw [equal]
  change (GeneralLinearGroup.map integralReduction
    (SpecialLinearGroup.mapGL IntegralAdeles (rep i) * g)).val 1 0 = 0
  rw [reduction_rep_mul_lowerLeft]
  exact hi

/-- The four cosets `rep i⁻¹ · borelThree` are all of `GL₂(ℤ̂)/borelThree`. -/
def traceEquiv : Option (Fin 3) ≃ (GeneralLinearGroup (Fin 2) IntegralAdeles ⧸ borelThree) :=
  Equiv.ofBijective traceCoset ⟨traceCoset_injective, traceCoset_surjective⟩

/-- The permutation of the four cosets induced by left multiplication by `k`. -/
def tracePerm (k : GeneralLinearGroup (Fin 2) IntegralAdeles) : Equiv.Perm (Option (Fin 3)) :=
  (traceEquiv.trans (MulAction.toPerm k)).trans traceEquiv.symm

theorem tracePerm_spec (k : GeneralLinearGroup (Fin 2) IntegralAdeles) (i : Option (Fin 3)) :
    ∃ b ∈ borelThree, k * rinv i = rinv (tracePerm k i) * b := by
  have h : traceEquiv (tracePerm k i) = k • traceEquiv i := by
    simp [tracePerm, Equiv.trans_apply]
  have h' : (QuotientGroup.mk (rinv (tracePerm k i)) :
      GeneralLinearGroup (Fin 2) IntegralAdeles ⧸ borelThree) = QuotientGroup.mk (k * rinv i) := by
    exact h
  have member := QuotientGroup.eq.mp h'
  refine ⟨(rinv (tracePerm k i))⁻¹ * (k * rinv i), member, ?_⟩
  rw [mul_inv_cancel_left]

/-! ## The sum over the four cosets -/

theorem pi_atFinite_map_mul (σ : CuspidalRepresentation)
    (k x : GeneralLinearGroup (Fin 2) IntegralAdeles) :
    σ.π (atFinite (GeneralLinearGroup.map integralEmbedding (k * x))) =
      σ.π (atFinite (GeneralLinearGroup.map integralEmbedding k)) *
        σ.π (atFinite (GeneralLinearGroup.map integralEmbedding x)) := by
  rw [map_mul, atFinite_mul, map_mul]

/-- The sum over the four cosets of a `borelThree`-fixed vector is `GL₂(ℤ̂)`-fixed. -/
theorem traceSum_fixed (σ : CuspidalRepresentation) (w : σ.H)
    (hw : ∀ b ∈ borelThree, σ.π (atFinite (GeneralLinearGroup.map integralEmbedding b)) w = w)
    (k : GeneralLinearGroup (Fin 2) IntegralAdeles) :
    σ.π (atFinite (GeneralLinearGroup.map integralEmbedding k))
        (∑ i : Option (Fin 3),
          σ.π (atFinite (GeneralLinearGroup.map integralEmbedding (rinv i))) w) =
      ∑ i : Option (Fin 3),
        σ.π (atFinite (GeneralLinearGroup.map integralEmbedding (rinv i))) w := by
  rw [map_sum]
  have step : ∀ i, σ.π (atFinite (GeneralLinearGroup.map integralEmbedding k))
      (σ.π (atFinite (GeneralLinearGroup.map integralEmbedding (rinv i))) w) =
      σ.π (atFinite (GeneralLinearGroup.map integralEmbedding (rinv (tracePerm k i)))) w := by
    intro i
    obtain ⟨b, hb, hkb⟩ := tracePerm_spec k i
    rw [← Module.End.mul_apply, ← pi_atFinite_map_mul, hkb, pi_atFinite_map_mul,
      Module.End.mul_apply, hw b hb]
  calc _ = ∑ i : Option (Fin 3),
        σ.π (atFinite (GeneralLinearGroup.map integralEmbedding (rinv (tracePerm k i)))) w :=
        Finset.sum_congr rfl (fun i _ => step i)
    _ = _ := Equiv.sum_comp (tracePerm k)
        (fun i => σ.π (atFinite (GeneralLinearGroup.map integralEmbedding (rinv i))) w)

/-! ## The trace vector -/

/-- The trace of a vector to level one: `∑ᵢ cuspFiniteRationalSlash σ (rep i) v`. -/
def traceVector (σ : CuspidalRepresentation) (v : σ.smooth) : σ.smooth :=
  ∑ i : Option (Fin 3), cuspFiniteRationalSlash σ (SpecialLinearGroup.mapGL ℚ (rep i)) v

theorem ratf_mapGL (γ : SpecialLinearGroup (Fin 2) ℤ) :
    GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) (SpecialLinearGroup.mapGL ℚ γ) =
      GeneralLinearGroup.map integralEmbedding (SpecialLinearGroup.mapGL IntegralAdeles γ) := by
  apply Units.ext
  funext row column
  simp only [GeneralLinearGroup.map_apply, SpecialLinearGroup.mapGL_coe_matrix,
    SpecialLinearGroup.map_apply_coe]
  change algebraMap ℚ FiniteAdeles (algebraMap ℤ ℚ (γ.val row column)) =
    integralEmbedding (algebraMap ℤ IntegralAdeles (γ.val row column))
  simp

theorem cuspFiniteRationalSlash_rep_val (σ : CuspidalRepresentation)
    (γ : SpecialLinearGroup (Fin 2) ℤ) (w : σ.smooth) :
    (cuspFiniteRationalSlash σ (SpecialLinearGroup.mapGL ℚ γ) w).val =
      σ.π (atFinite (GeneralLinearGroup.map integralEmbedding
        (SpecialLinearGroup.mapGL IntegralAdeles γ⁻¹))) w.val := by
  change σ.π (atFinite (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles)
    (SpecialLinearGroup.mapGL ℚ γ)⁻¹)) w.val = _
  rw [← map_inv, ratf_mapGL]

theorem traceVector_val (σ : CuspidalRepresentation) (v : σ.smooth) :
    (traceVector σ v).val = ∑ i : Option (Fin 3),
      σ.π (atFinite (GeneralLinearGroup.map integralEmbedding (rinv i))) v.val := by
  simp only [traceVector, Submodule.coe_sum, cuspFiniteRationalSlash_rep_val, rinv]

/-- **The trace of a level-three vector is spherical.** -/
theorem traceVector_spherical (σ : CuspidalRepresentation) (halfWeight : ℤ) (v : σ.smooth)
    (hv : v.val ∈ levelThreeValues σ)
    (rotation : ∀ angle : Circle, σ.π (atInfinity (binaryRotations angle)) v.val =
      (angle : ℂ) ^ (2 * halfWeight) • v.val) :
    (traceVector σ v).val ∈ cuspSphericalValues σ := by
  intro k
  rw [traceVector_val]
  exact traceSum_fixed σ v.val
    (fun b hb => levelThree_fixed_of_borel σ halfWeight v hv rotation b hb) k

/-- **The scalar function of the trace vector is the classical trace.** -/
theorem traceVector_scalar (σ : CuspidalRepresentation) (halfWeight : ℤ) (v : σ.smooth)
    (rotation : ∀ angle : Circle, σ.π (atInfinity (binaryRotations angle)) v.val =
      (angle : ℂ) ^ (2 * halfWeight) • v.val) :
    cuspScalarWeightedLinear σ halfWeight 1 (traceVector σ v) =
      ∑ i : Option (Fin 3), SlashAction.map (-2 * halfWeight) (rep i)
        (cuspScalarWeightedLinear σ halfWeight 1 v) := by
  simp only [traceVector, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact levelThree_slash_eq σ halfWeight v rotation (rep i)

/-- A non-spherical representation has zero trace. -/
theorem traceVector_eq_zero_of_not_spherical (σ : CuspidalRepresentation) (halfWeight : ℤ)
    (v : σ.smooth) (hv : v.val ∈ levelThreeValues σ)
    (rotation : ∀ angle : Circle, σ.π (atInfinity (binaryRotations angle)) v.val =
      (angle : ℂ) ^ (2 * halfWeight) • v.val) (not_spherical : ¬SphericalCusp σ) :
    traceVector σ v = 0 := by
  by_contra nonzero
  exact not_spherical ⟨traceVector σ v, nonzero, traceVector_spherical σ halfWeight v hv rotation⟩

/-- The classical trace of the cusp form of a level-three vector vanishes when `σ` is not
spherical. -/
theorem trace_sum_slash_eq_zero_of_not_spherical (σ : CuspidalRepresentation) (halfWeight : ℤ)
    (v : σ.smooth) (hv : v.val ∈ levelThreeValues σ)
    (rotation : ∀ angle : Circle, σ.π (atInfinity (binaryRotations angle)) v.val =
      (angle : ℂ) ^ (2 * halfWeight) • v.val) (not_spherical : ¬SphericalCusp σ) :
    ∑ i : Option (Fin 3), SlashAction.map (-2 * halfWeight) (rep i)
      (cuspScalarWeightedLinear σ halfWeight 1 v) = 0 := by
  rw [← traceVector_scalar σ halfWeight v rotation,
    traceVector_eq_zero_of_not_spherical σ halfWeight v hv rotation not_spherical, map_zero]

end TernaryPeriodPolynomials.MultiplicityOne
