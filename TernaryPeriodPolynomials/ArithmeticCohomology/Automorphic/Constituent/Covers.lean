module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Automorphic.Constituent.Cohomological
public import TernaryPeriodPolynomials.EisensteinSeries.Regularity.Final
public import TernaryPeriodPolynomials.EisensteinSeries.Regularity.Assembly
public import TernaryPeriodPolynomials.EisensteinSeries.Regularity.TypeSpace
public import TernaryPeriodPolynomials.ArithmeticCohomology.Automorphic.ModelFamily
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.WtForm
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Period.Cocycle
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.IwasawaPhase

@[expose] public section


/-!
# The cuspidal constituents of the Bergman model cover all cusp forms

Let `f` be a cusp form of weight `n + 3` for `Γ₁(3)` (`n ≥ 3`).  Its adelic lift is the function of
a `K'`-fixed vector `e` of the finite-adelic model, and `lowestMinus e` lies in the type space
(`typeSubspace_eq_map`).  Splitting it into vectors of compression-simple subspaces
(`exists_sum_compressionSimple`) writes `e` as a sum of `K'`-fixed vectors `e_N`, and the
distinguished vector of the constituent of `N` realizes to `reproConst • ε e_N`
(`realization_lowestMinus`).  Along the symmetric section the weighted scalar function of the
rescaled distinguished vector is `wtFactor * ε e_N`, and `wtFactor` cancels the normalisation of
the classical lift (`wtFactor_mul_adelicLift_section`).  Summing gives `modelCoversForms`: every
cusp form of weight `n + 3` is a finite sum of cusp forms of classical level-three vectors of
cohomological cuspidal data.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.Automorphic
open TernaryPeriodPolynomials.Automorphic.SmoothVectors
open TernaryPeriodPolynomials.Automorphic.AbstractIrreducibility
open TernaryPeriodPolynomials.Regularity
open TernaryPeriodPolynomials.CuspIntegral (adelicLift adelicLift_infGL
  adelicLift_mul_levelGroup infGL_apply liftReal)
open TernaryPeriodPolynomials.EvenLevelThree
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodCocycle (S)
open TernaryPeriodPolynomials.EisensteinRegularization.Helpers
  (binaryRealGammaOneThree)

namespace TernaryPeriodPolynomials.Automorphic.Constituent

/-! ### Elementary facts -/

/-- `e ↦ lowestMinus hk e` is injective. -/
theorem lowestMinusL_injective {k : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (hk : 2 ≤ k) : Function.Injective (lowestMinusL (E := E) hk) := by
  intro e e' h
  have h0 : coeffMinus (lowestMinusL hk e) 0 = coeffMinus (lowestMinusL hk e') 0 := by rw [h]
  rw [lowestMinusL_apply, lowestMinusL_apply, coeffMinus_lowestMinus, coeffMinus_lowestMinus,
    ite_eq_left rfl, ite_eq_left rfl] at h0
  have hc : ((-1 : ℂ) ^ k) ≠ 0 := pow_ne_zero k (neg_ne_zero.mpr one_ne_zero)
  have h1 : ((-1 : ℂ) ^ k) • (e - e') = 0 := by rw [smul_sub, h0, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp h1).resolve_left hc)

/-- A cusp form of weight `k` is a cusp form of any equal weight `k'`, with the same function. -/
theorem exists_cuspForm_cast {k k' : ℤ} (h : k = k') (g : CuspForm binaryRealGammaOneThree k) :
    ∃ f : CuspForm binaryRealGammaOneThree k', (⇑f : UpperHalfPlane → ℂ) = ⇑g := by
  subst h
  exact ⟨g, rfl⟩

/-- The weight factor cancels the normalisation of the adelic lift along the symmetric section:
`wtFactor (-k) (Im z) * adelicLift f (section z) = f z`. -/
theorem wtFactor_mul_adelicLift_section {k : ℕ} {wt : ℤ} (hwt : wt = -(k : ℤ))
    (f : CuspForm binaryRealGammaOneThree (k : ℤ)) (z : UpperHalfPlane) :
    ((wtFactor wt z.im : ℝ) : ℂ) * adelicLift f (atInfinity (binarySymmetricSection z)) = f z := by
  subst hwt
  have hdet : 0 < (GeneralLinearGroup.det (binarySymmetricSection z) : ℝˣ).val := by
    rw [binarySymmetricSection_det]
    exact one_pos
  have hs : ((Real.sqrt z.im : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 z.im_pos).ne'
  have key : ((Real.sqrt z.im : ℝ) : ℂ) ^ (-(k : ℤ)) *
      (1 / ((Real.sqrt z.im : ℝ) : ℂ)) ^ (-(k : ℤ)) = 1 := by
    rw [← mul_zpow, mul_one_div_cancel hs, _root_.one_zpow]
  rw [← infGL_apply, adelicLift_infGL f _ hdet, liftReal, binarySymmetricSection_det,
    binarySymmetricSection_smul, binarySymmetricSection_denom,
    wtFactor_eq_sqrt_zpow _ z.im_pos, abs_one, Real.sqrt_one, Complex.ofReal_one, _root_.one_zpow,
    one_mul, Complex.ofReal_zpow, ← mul_assoc, key, one_mul]

/-! ### The fixed vectors of the model -/

/-- The realization of the vectors of the model fixed by the level group `K'`. -/
def evalK (n : ℕ) : fixedSubmodule (bergmanModel n).σ bergmanK →ₗ[ℂ] (BinaryAdelicGL → ℂ) :=
  (bergmanModel n).ε ∘ₗ
    Submodule.inclusion (fixed_le_finiteSmooth (bergmanModel n) levelGroup_isOpenCompact)

variable {n : ℕ}

/-- The vector of the model realizing the adelic lift of a cusp form is fixed by `K'`. -/
theorem fixed_of_lift (f : CuspForm binaryRealGammaOneThree (((n + 3 : ℕ)) : ℤ))
    (e : finiteSmooth (bergmanModel n).σ) (he : (bergmanModel n).ε e = adelicLift f) :
    (e : (bergmanModel n).E) ∈ fixedSubmodule (bergmanModel n).σ bergmanK := by
  intro u
  have h : (bergmanModel n).ε ⟨(bergmanModel n).σ u.1 e,
      finiteSmooth_stable _ u.1 e.2⟩ = (bergmanModel n).ε e := by
    funext x
    rw [(bergmanModel n).equivariant u.1 e x, he]
    exact adelicLift_mul_levelGroup f x u.2
  exact congrArg Subtype.val ((bergmanModel n).injective h)

/-! ### The distinguished vector of a constituent -/

/-- The realization of the distinguished vector of `c.cusp hn` is the realization of the Bergman
space vector `c.v`. -/
theorem realize_vec (hn : 3 ≤ n) (c : Piece n) (x : BinaryAdelicGL) :
    (c.cusp hn).realize ⟨c.vec hn, c.vec_smooth hn⟩ x =
      (realization (bergmanModel n) (by omega : 6 ≤ n + 3)).realize
        ⟨c.v, c.isSmoothVector_v⟩ x := rfl

/-- **The scalar function of the distinguished vector** of a constituent whose vector is the lowest
weight vector of the `K'`-fixed vector `E0`, along the symmetric section. -/
theorem scalar_vec_eq (hn : 3 ≤ n) (c : Piece n)
    (E0 : fixedSubmodule (bergmanModel n).σ bergmanK)
    (hE : lowestMinus (by omega : 2 ≤ n + 3) (E0 : (bergmanModel n).E) = c.v)
    (z : UpperHalfPlane) :
    cuspScalarWeightedLinearWt (c.cusp hn) (-((n : ℤ) + 3)) 1 ⟨c.vec hn, c.vec_smooth hn⟩ z =
      reproConst (n + 3) * (((wtFactor (-((n : ℤ) + 3)) z.im : ℝ) : ℂ) *
        evalK n E0 (atInfinity (binarySymmetricSection z))) := by
  have hsm := isSmoothVector_lowestMinus (bergmanModel n) (by omega : 2 ≤ n + 3)
    levelGroup_isOpenCompact E0.2
  have hreal := realization_lowestMinus (bergmanModel n) (by omega : 6 ≤ n + 3)
    levelGroup_isOpenCompact E0.2 hsm
  have hv : (⟨c.v, c.isSmoothVector_v⟩ : smoothSubmodule (bergmanRep (bergmanModel n))) =
      ⟨lowestMinus (by omega : 2 ≤ n + 3) (E0 : (bergmanModel n).E), hsm⟩ :=
    Subtype.ext hE.symm
  have hsec : invertibleMatrix (binaryUpperSectionMatrix (z : ℂ)) = binarySymmetricSection z := by
    rw [binaryUpperSectionMatrix_coe, invertibleMatrix_coe]
  change wtFactor (-((n : ℤ) + 3)) (z : ℂ).im • (c.cusp hn).realize
    ⟨c.vec hn, c.vec_smooth hn⟩
    (1 * atInfinity (invertibleMatrix (binaryUpperSectionMatrix (z : ℂ)))) = _
  rw [one_mul, hsec, realize_vec hn c, hv, hreal, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
  exact mul_left_comm _ _ _

/-- The term `wtFactor * ε e` along the symmetric section. -/
def coverTerm (n : ℕ) (e : fixedSubmodule (bergmanModel n).σ bergmanK) (z : UpperHalfPlane) : ℂ :=
  ((wtFactor (-((n : ℤ) + 3)) z.im : ℝ) : ℂ) *
    evalK n e (atInfinity (binarySymmetricSection z))

/-! ### Covering by constituents -/

/-- A finite sum of the terms `coverTerm n (E N)` over compression-simple subspaces `N`, with
`lowestMinus (E N) = μ N`, is a finite sum of scalar functions of classical level-three vectors of
cohomological cuspidal data. -/
theorem sum_cover (hn : 3 ≤ n)
    (s : Finset (Submodule ℂ (BergmanSpace (n + 3) (bergmanModel n).E)))
    (hs : ∀ N ∈ s, CompressionSimple (bergmanRep (bergmanModel n))
      (TypeData.typeGroup bergmanK) (Weight.typeCharacterInv (n + 3) bergmanK) N)
    (μ : (N : Submodule ℂ (BergmanSpace (n + 3) (bergmanModel n).E)) → N)
    (E : Submodule ℂ (BergmanSpace (n + 3) (bergmanModel n).E) →
      fixedSubmodule (bergmanModel n).σ bergmanK)
    (hE : ∀ N ∈ s, lowestMinus (by omega : 2 ≤ n + 3) (E N : (bergmanModel n).E) =
      (μ N : BergmanSpace (n + 3) (bergmanModel n).E)) :
    ∃ l : List (Σ D : CohomologicalCuspData n,
        levelThreeClassicalVectorsWt D.cusp (-((n : ℤ) + 3))),
      (fun z : UpperHalfPlane => ∑ N ∈ s, coverTerm n (E N) z) =
        (l.map fun p => cuspScalarWeightedLinearWt p.1.cusp (-((n : ℤ) + 3)) 1 p.2.1).sum := by
  classical
  revert hs hE
  refine Finset.induction_on s ?_ ?_
  · intro _ _
    exact ⟨[], by funext z; simp⟩
  · intro a s ha ih hs hE
    obtain ⟨l, hl⟩ := ih (fun N hN => hs N (Finset.mem_insert_of_mem hN))
      (fun N hN => hE N (Finset.mem_insert_of_mem hN))
    have hEa := hE a (Finset.mem_insert_self a s)
    have h1 : (fun z : UpperHalfPlane => ∑ N ∈ insert a s, coverTerm n (E N) z) =
        coverTerm n (E a) + fun z : UpperHalfPlane => ∑ N ∈ s, coverTerm n (E N) z := by
      funext z
      simp only [Finset.sum_insert ha, Pi.add_apply]
    by_cases h0 : (μ a : BergmanSpace (n + 3) (bergmanModel n).E) = 0
    · refine ⟨l, ?_⟩
      have hz : (E a : (bergmanModel n).E) = 0 := by
        apply lowestMinusL_injective (by omega : 2 ≤ n + 3)
        rw [map_zero]
        exact hEa.trans h0
      have hEz : E a = 0 := Subtype.ext hz
      have h0' : coverTerm n (E a) = 0 := by
        funext z
        simp [coverTerm, hEz]
      rw [h1, h0', zero_add, hl]
    · have hsa := hs a (Finset.mem_insert_self a s)
      obtain ⟨c, hcv⟩ : ∃ c : Piece n,
          c.v = (μ a : BergmanSpace (n + 3) (bergmanModel n).E) :=
        ⟨⟨a, hsa, μ a, (μ a).2, h0⟩, rfl⟩
      have hEc : lowestMinus (by omega : 2 ≤ n + 3) (E a : (bergmanModel n).E) = c.v :=
        hEa.trans hcv.symm
      have hcl : (reproConst (n + 3))⁻¹ • (⟨c.vec hn, c.vec_smooth hn⟩ : (c.cusp hn).smooth) ∈
          levelThreeClassicalVectorsWt (c.cusp hn) (-((n : ℤ) + 3)) :=
        Submodule.smul_mem _ _ (c.vec_classical hn)
      have hr : reproConst (n + 3) ≠ 0 := reproConst_ne_zero (by omega)
      have hp : ∀ z : UpperHalfPlane, cuspScalarWeightedLinearWt (c.cusp hn) (-((n : ℤ) + 3)) 1
          ((reproConst (n + 3))⁻¹ • (⟨c.vec hn, c.vec_smooth hn⟩ : (c.cusp hn).smooth)) z =
          ((wtFactor (-((n : ℤ) + 3)) z.im : ℝ) : ℂ) *
            evalK n (E a) (atInfinity (binarySymmetricSection z)) := by
        intro z
        rw [map_smul, Pi.smul_apply, smul_eq_mul, scalar_vec_eq hn c (E a) hEc z,
          inv_mul_cancel_left₀ hr]
      have h2 : coverTerm n (E a) = cuspScalarWeightedLinearWt (c.cuspData hn).cusp
          (-((n : ℤ) + 3)) 1
          ((reproConst (n + 3))⁻¹ • (⟨c.vec hn, c.vec_smooth hn⟩ : (c.cusp hn).smooth)) :=
        funext fun z => (hp z).symm
      refine ⟨⟨c.cuspData hn, ⟨(reproConst (n + 3))⁻¹ •
        (⟨c.vec hn, c.vec_smooth hn⟩ : (c.cusp hn).smooth), hcl⟩⟩ :: l, ?_⟩
      rw [h1, h2, hl]
      simp only [List.map_cons, List.sum_cons]

/-- **The cuspidal constituents of the Bergman model cover all cusp forms.**  For `n ≥ 3`, every
cusp form of weight `n + 3` for `Γ₁(3)` is a finite sum of the cusp forms of classical
level-three vectors of rotation weight `-(n + 3)` of cohomological cuspidal data.  This is
`Contracts.ModelCoversForms n`. -/
theorem modelCoversForms (n : ℕ) (hn : 3 ≤ n) :
    ∀ f : S (n + 1),
      ∃ l : List (Σ D : CohomologicalCuspData n,
          levelThreeClassicalVectorsWt D.cusp (-((n : ℤ) + 3))),
        (⇑f : UpperHalfPlane → ℂ) =
          (l.map fun p => cuspScalarWeightedLinearWt p.1.cusp (-((n : ℤ) + 3)) 1 p.2.1).sum := by
  intro g
  have hk2 : 2 ≤ n + 3 := by omega
  obtain ⟨f, hf⟩ := exists_cuspForm_cast (k' := ((n + 3 : ℕ) : ℤ))
    (by show ((n + 1 : ℕ) : ℤ) + 2 = ((n + 3 : ℕ) : ℤ); omega) g
  obtain ⟨e, he⟩ : ∃ e, (bergmanModel n).ε e = adelicLift f :=
    lifts_ε_lift Set.univ (Set.mem_univ f)
  obtain ⟨E0, hE0⟩ : ∃ E0 : fixedSubmodule (bergmanModel n).σ bergmanK,
      (E0 : (bergmanModel n).E) = e.1 := ⟨⟨e.1, fixed_of_lift f e he⟩, rfl⟩
  have hev : evalK n E0 = adelicLift f := by
    rw [← he]
    exact congrArg (bergmanModel n).ε (Subtype.ext hE0 :
      (Submodule.inclusion (fixed_le_finiteSmooth (bergmanModel n) levelGroup_isOpenCompact)
        E0 : finiteSmooth (bergmanModel n).σ) = e)
  have htype : typeSpace n =
      (fixedSubmodule (bergmanModel n).σ bergmanK).map (lowestMinusL hk2) :=
    typeSubspace_eq_map (bergmanModel n) hk2 bergmanK
  have hw : lowestMinusL hk2 (E0 : (bergmanModel n).E) ∈ typeSpace n := by
    rw [htype]
    exact Submodule.mem_map_of_mem E0.2
  obtain ⟨s, hs, μ, hsum⟩ := CyclicRepresentation.exists_sum_compressionSimple
    (π := bergmanRep (bergmanModel n)) (TypeData.typeGroup bergmanK)
    (Weight.typeCharacterInv (n + 3) bergmanK) (S := typeSpace n) le_rfl
    (ModelFamily.compressionStable_typeSubspace _ _ _) hw
  have hex : ∀ N ∈ s, ∃ eN : fixedSubmodule (bergmanModel n).σ bergmanK,
      lowestMinus hk2 (eN : (bergmanModel n).E) =
        (μ N : BergmanSpace (n + 3) (bergmanModel n).E) := by
    intro N hN
    have hmem : (μ N : BergmanSpace (n + 3) (bergmanModel n).E) ∈ typeSpace n :=
      (hs N hN).1 (μ N).2
    rw [htype] at hmem
    obtain ⟨e', he', hee⟩ := Submodule.mem_map.mp hmem
    exact ⟨⟨e', he'⟩, hee⟩
  choose! E hE using hex
  have hsumE : ∑ N ∈ s, E N = E0 := by
    apply Subtype.ext
    apply lowestMinusL_injective hk2
    rw [Submodule.coe_sum, map_sum, ← hsum]
    exact Finset.sum_congr rfl fun N hN => hE N hN
  obtain ⟨l, hl⟩ := sum_cover hn s (fun N hN => (hs N hN).2) μ E hE
  refine ⟨l, ?_⟩
  rw [← hl]
  funext z
  calc g z = f z := (congrFun hf z).symm
    _ = ((wtFactor (-((n : ℤ) + 3)) z.im : ℝ) : ℂ) *
          adelicLift f (atInfinity (binarySymmetricSection z)) :=
        (wtFactor_mul_adelicLift_section (k := n + 3) (by omega) f z).symm
    _ = ((wtFactor (-((n : ℤ) + 3)) z.im : ℝ) : ℂ) *
          evalK n E0 (atInfinity (binarySymmetricSection z)) := by rw [← hev]
    _ = ∑ N ∈ s, coverTerm n (E N) z := by
        simp only [coverTerm]
        rw [← hsumE, map_sum, Finset.sum_apply, Finset.mul_sum]

end TernaryPeriodPolynomials.Automorphic.Constituent

end
