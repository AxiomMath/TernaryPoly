module

public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.LowDegree.Cross

@[expose] public section


open CategoryTheory CategoryTheory.Limits groupCohomology
noncomputable section
namespace TernaryPoly.LowDegreeHochschildSerre

variable {N Q : Type} [Group N] [Group Q] (φ : Q →* MulAut N)
variable (A : Rep ℚ (G φ))

/-- Extend an N one-cocycle along the literal normal form nq. -/
def extendOne (z : cocycles₁ (radicalRep φ A)) : G φ → A := fun g => z g.left

theorem extendOne_first (z : cocycles₁ (radicalRep φ A)) :
    FirstNormalized φ A (cob₂ φ A (extendOne φ A z)) := by
  intro n g
  change A.ρ (nIn φ n) (z g.left) - z (n * φ 1 g.left) + z n = 0
  simp only [map_one, MulAut.one_apply]
  have he := (mem_cocycles₁_iff z).mp z.property n g.left
  change z (n*g.left) = A.ρ (nIn φ n) (z g.left) + z n at he
  rw [he]
  abel

theorem extendOne_cross (z : cocycles₁ (radicalRep φ A)) (q : Q) (n : N) :
    cob₂ φ A (extendOne φ A z) (qIn φ q,nIn φ (φ q⁻¹ n)) =
      cocyclesOneAction φ A q z n - z n := by
  change A.ρ (qIn φ q) (z (φ q⁻¹ n)) - z (1 * φ q (φ q⁻¹ n)) + z 1 = _
  simp only [one_mul, ← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one,
    MulAut.one_apply, cocycles₁_map_one, add_zero, cocyclesOneAction_apply]

/-- H¹(Q,H¹(N,A)) vanishing makes every cross class principal in an actual N cocycle. -/
theorem crossClass_primitive
    (hH1 : IsZero (groupCohomology (cohomologyRep φ A 1) 1))
    (c : cocycles₂ A) (hc : FirstNormalized φ A c) :
    ∃ z : cocycles₁ (radicalRep φ A), ∀ q,
      H1π (radicalRep φ A) (crossCocycle φ A c hc q) =
        H1π (radicalRep φ A) (cocyclesOneAction φ A q z - z) := by
  have := ModuleCat.isZero_iff_subsingleton.mp hH1
  have hz : H1π (cohomologyRep φ A 1) (crossClass φ A c hc) = 0 := Subsingleton.elim _ _
  obtain ⟨t, ht⟩ := (H1π_eq_zero_iff _).mp hz
  have ht' : ∀ q, (cohomologyRep φ A 1).ρ q t - t = crossClass φ A c hc q :=
    fun q => congrFun ht q
  obtain ⟨z, rfl⟩ : ∃ z : cocycles₁ (radicalRep φ A), H1π (radicalRep φ A) z = t := by
    induction t using H1_induction_on with | h z => exact ⟨z,rfl⟩
  refine ⟨z, fun q => ?_⟩
  rw [map_sub, ← H1π_action]
  exact (ht' q).symm

/-- Kill all cross classes while retaining the first normalization and the original H² class. -/
theorem normalize_cross_classes
    (hH1 : IsZero (groupCohomology (cohomologyRep φ A 1) 1))
    (c : cocycles₂ A) (hc : FirstNormalized φ A c) :
    ∃ c₂ : cocycles₂ A, H2π A c₂ = H2π A c ∧
      ∃ hc₂ : FirstNormalized φ A c₂, ∀ q,
        H1π (radicalRep φ A) (crossCocycle φ A c₂ hc₂ q) = 0 := by
  obtain ⟨z,hz⟩ := crossClass_primitive φ A hH1 c hc
  let c₂ := c - cob₂ φ A (extendOne φ A z)
  have hc₂ : FirstNormalized φ A c₂ := by
    intro n g
    change c (nIn φ n,g) - cob₂ φ A (extendOne φ A z) (nIn φ n,g) = 0
    rw [hc, extendOne_first φ A z, sub_self]
  refine ⟨c₂, ?_, hc₂, fun q => ?_⟩
  · change H2π A (c - cob₂ φ A (extendOne φ A z)) = H2π A c
    rw [map_sub]
    exact (congrArg (fun x => H2π A c - x) (H2π_cob₂ φ A _)).trans (sub_zero _)
  have he : crossCocycle φ A c₂ hc₂ q =
      crossCocycle φ A c hc q - (cocyclesOneAction φ A q z - z) := by
    apply Subtype.ext
    funext n
    change c (qIn φ q,nIn φ (φ q⁻¹ n)) -
      cob₂ φ A (extendOne φ A z) (qIn φ q,nIn φ (φ q⁻¹ n)) = _
    rw [extendOne_cross]
    rfl
  rw [he, map_sub, hz, sub_self]

/-- Both mixed vanishing conditions needed for actual inflation. -/
abbrev MixedNormalized (c : cocycles₂ A) : Prop :=
  FirstNormalized φ A c ∧ ∀ q n, c (qIn φ q,nIn φ n) = 0

/-- The remaining principal cross cocycles can be killed by an explicit one-cochain. -/
theorem normalize_cross_principal (c : cocycles₂ A) (hc : FirstNormalized φ A c)
    (hz : ∀ q, H1π (radicalRep φ A) (crossCocycle φ A c hc q) = 0) :
    ∃ c₃ : cocycles₂ A, H2π A c₃ = H2π A c ∧ MixedNormalized φ A c₃ := by
  classical
  have hw : ∀ q, ∃ w : A, ∀ n,
      A.ρ (nIn φ n) w - w = crossCocycle φ A c hc q n := by
    intro q
    obtain ⟨w,hw⟩ := (H1π_eq_zero_iff _).mp (hz q)
    exact ⟨w,fun n => congrFun hw n⟩
  choose w hw using hw
  let w' : Q → A := fun q => if q = 1 then 0 else w q
  have hw1 : w' 1 = 0 := by simp [w']
  have hw' (q : Q) (n : N) : A.ρ (nIn φ n) (w' q) - w' q =
      crossCocycle φ A c hc q n := by
    by_cases hq : q = 1
    · subst q
      simp only [hw1, map_zero, sub_self, crossCocycle_apply, map_one]
      exact (firstNormalized_one_left φ A hc _).symm
    · simpa only [w', ite_eq_right hq] using hw q n
  let L : G φ → A := fun g => A.ρ (nIn φ g.left) (w' g.right)
  have hL : FirstNormalized φ A (cob₂ φ A L) := by
    intro n g
    change A.ρ (nIn φ n) (A.ρ (nIn φ g.left) (w' g.right)) -
      A.ρ (nIn φ (n * φ 1 g.left)) (w' (1*g.right)) + A.ρ (nIn φ n) (w' 1) = 0
    simp only [map_one, MulAut.one_apply, one_mul, hw1, map_zero, map_mul,
      Module.End.mul_apply, sub_self, add_zero]
  have hLcross (q : Q) (n : N) :
      cob₂ φ A L (qIn φ q,nIn φ (φ q⁻¹ n)) = -crossCocycle φ A c hc q n := by
    change A.ρ (qIn φ q) (A.ρ (nIn φ (φ q⁻¹ n)) (w' 1)) -
      A.ρ (nIn φ (1 * φ q (φ q⁻¹ n))) (w' (q*1)) + A.ρ (nIn φ 1) (w' q) = _
    simp only [hw1, map_zero, one_mul, mul_one, ← MulAut.mul_apply, ← map_mul,
      mul_inv_cancel, map_one, MulAut.one_apply, Module.End.one_apply, zero_sub]
    rw [← hw']
    abel
  refine ⟨c + cob₂ φ A L, ?_, ?_, ?_⟩
  · rw [map_add]
    exact (congrArg (fun x => H2π A c + x) (H2π_cob₂ φ A L)).trans (add_zero _)
  · intro n g
    change c (nIn φ n,g) + cob₂ φ A L (nIn φ n,g) = 0
    rw [hc, hL, add_zero]
  · intro q n
    have hn : φ q⁻¹ (φ q n) = n := by
      rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
    have he := hLcross q (φ q n)
    rw [hn] at he
    change c (qIn φ q,nIn φ n) + cob₂ φ A L (qIn φ q,nIn φ n) = 0
    rw [he]
    simp only [crossCocycle_apply, hn, add_neg_cancel]

end TernaryPoly.LowDegreeHochschildSerre
