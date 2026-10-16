module

public import TernaryPeriodPolynomials.GroupCohomology.Relative.Edge.CohomologyActions
public import TernaryPeriodPolynomials.GroupCohomology.Relative.Edge.CohomologyNormalization

@[expose] public section

open MvPolynomial
noncomputable section
namespace TernaryPoly.RelativeEdgeCohomologyBB
open CategoryTheory CategoryTheory.Limits groupCohomology
open RelativeStabilizerConsumer RelativeEdgeCohomologyMatrices RelativeEdgeCohomologyActions
open RelativeEdgeCohomologyPolynomials RelativeEdgeCohomologyCocycles
open RadicalCoinvariantAlgebra


lemma bb_normalize (n : ℕ) (f : cocycles₁ (bbRep n)) (I : Set (Fin 3))
    (hI : ∀ k ∈ I, f (bbRoot k 1)=0) :
    ∃ f' : cocycles₁ (bbRep n), f' bbFirst=0 ∧ f' bbSecond=0 ∧
      (∀ k ∈ I, f' (bbRoot k 1)=0) ∧ H1π (bbRep n) f'=H1π (bbRep n) f := by
  obtain ⟨f',hs,ht,hr,hf⟩ := normalize_two_preserving (bbRep n) f bbFirst bbSecond
    bb_signs_involutions.1 bb_signs_involutions.2.1 bb_signs_involutions.2.2
    ((fun k => bbRoot k 1) '' I) (by rintro g ⟨k,hk,rfl⟩; exact hI k hk)
    (by
      rintro g ⟨k,_,rfl⟩
      fin_cases k
      · right; simpa using bbFirst_root 0 1
      · right; simpa using bbFirst_root 1 1
      · left; simpa using bbFirst_root 2 1)
    (by
      rintro g ⟨k,_,rfl⟩
      fin_cases k
      · right; simpa using bbSecond_root 0 1
      · left; simpa using bbSecond_root 1 1
      · right; simpa using bbSecond_root 2 1)
  exact ⟨f',hs,ht,fun k hk => hr _ ⟨k,hk,rfl⟩,hf⟩

lemma bb_first_erase (n : ℕ) (f : cocycles₁ (bbRep n)) (ht : f bbSecond=0) :
    erase 1 (f (bbRoot 0 1) : Poly)=0 := by
  have h := inverted_quotient (bbRep n) (eraseCoeff n 1) f bbSecond (bbRoot 0 1) ht
    (by rw [bbSecond_root]; simp) (fun p => by
      change erase 1 ((bbRep n).ρ (bbRoot 0 1) p : Poly)=erase 1 p
      rw [bb_action_coe]
      exact erase_shear 0 1 (by decide) p)
  change erase 1 ((bbRep n).ρ bbSecond (f (bbRoot 0 1)) : Poly) =
    -erase 1 (f (bbRoot 0 1) : Poly) at h
  rw [bb_second_coe, erase_flip, flip_erase_self] at h
  exact zero_of_neg_eq_self _ h

lemma bb_central_zero (n : ℕ) (f : cocycles₁ (bbRep n))
    (hs : f bbFirst=0) (ha : f (bbRoot 0 1)=0) : f (bbRoot 1 1)=0 := by
  have hp := commuting_fixed (bbRep n) f (bbRoot 0 1) (bbRoot 1 1) ha (bb_first_central 1 1)
  have hp' := congrArg (fun p : bbRep n => (p : Poly)) hp
  rw [bb_action_coe] at hp'
  have h0 := shear_fixed_erase 0 (f (bbRoot 1 1) : Poly) hp'
  apply inverted_root_zero (bbRep n) f bbFirst (bbRoot 1 1) hs
    (by rw [bbFirst_root]; simp)
  · apply Subtype.ext
    rw [bb_action_coe]
    change shear 0 2 (f (bbRoot 1 1) : Poly)=(f (bbRoot 1 1) : Poly)
    simpa only [shearStep_one] using first_shearStep_fixed 2 1 _ h0
  · apply Subtype.ext
    rw [bb_first_coe]
    exact flip_fixed_of_erase 0 _ h0

lemma bb_last_independent (n : ℕ) (f : cocycles₁ (bbRep n))
    (ha : f (bbRoot 0 1)=0) (hc : f (bbRoot 1 1)=0) :
    erase 0 (f (bbRoot 2 1) : Poly)=(f (bbRoot 2 1) : Poly) := by
  have hp := commutator_fixed (bbRep n) f (bbRoot 0 1) (bbRoot 2 1) (bbRoot 1 1)
    ha hc (by simpa using bb_commutator 1 1)
  have hp' := congrArg (fun p : bbRep n => (p : Poly)) hp
  rw [bb_action_coe] at hp'
  exact shear_fixed_erase 0 _ hp'

lemma bb_last_erase (n : ℕ) (hn : Even n) (f : cocycles₁ (bbRep n))
    (ht : f bbSecond=0) (h0 : erase 0 (f (bbRoot 2 1) : Poly)=(f (bbRoot 2 1) : Poly)) :
    erase 2 (f (bbRoot 2 1) : Poly)=0 := by
  have h := inverted_quotient (bbRep n) (eraseCoeff n 2) f bbSecond (bbRoot 2 1) ht
    (by rw [bbSecond_root]; simp) (fun p => by
      change erase 2 ((bbRep n).ρ (bbRoot 2 1) p : Poly)=erase 2 p
      rw [bb_action_coe]
      exact erase_shear 1 2 (by decide) p)
  change erase 2 ((bbRep n).ρ bbSecond (f (bbRoot 2 1)) : Poly) =
    -erase 2 (f (bbRoot 2 1) : Poly) at h
  rw [bb_second_coe, erase_flip,
    even_erase2_independent_flip1 _ (f (bbRoot 2 1)).property hn h0] at h
  exact zero_of_neg_eq_self _ h

lemma bb_kill_first (n : ℕ) (f : cocycles₁ (bbRep n)) (ht : f bbSecond=0) :
    ∃ f' : cocycles₁ (bbRep n), f' bbFirst=0 ∧ f' bbSecond=0 ∧
      f' (bbRoot 0 1)=0 ∧ H1π (bbRep n) f'=H1π (bbRep n) f := by
  obtain ⟨q,hqn,hq⟩ := (exists_homogeneous_shear_sub_iff 0 (f (bbRoot 0 1) : Poly)
    (f (bbRoot 0 1)).property).mpr (bb_first_erase n f ht)
  let v : bbRep n := ⟨q,hqn⟩
  have hv : coboundary (bbRep n) v (bbRoot 0 1)=f (bbRoot 0 1) := by
    apply Subtype.ext
    change ((bbRep n).ρ (bbRoot 0 1) v : Poly)-q=(f (bbRoot 0 1) : Poly)
    rw [bb_action_coe]
    exact hq
  let g := f-coboundary (bbRep n) v
  have hg : g (bbRoot 0 1)=0 := by
    change f (bbRoot 0 1)-coboundary (bbRep n) v (bbRoot 0 1)=0
    rw [hv,sub_self]
  obtain ⟨f',hs',ht',hr,he⟩ := bb_normalize n g {0} (by
    intro k hk; have hk' : k=0 := hk; subst k; exact hg)
  refine ⟨f',hs',ht',hr 0 rfl, ?_⟩
  exact he.trans (H1_sub_coboundary (bbRep n) f v)

/-- Direct elimination of the three root values proves the genuine BB H1 vanishing. -/
theorem bb_H1_zero (n : ℕ) (hn : Even n) : IsZero (groupCohomology (bbRep n) 1) := by
  apply isZero_H1_of_classes
  intro f
  obtain ⟨f₀,_,ht₀,he₀⟩ := normalize_two (bbRep n) f bbFirst bbSecond
    bb_signs_involutions.1 bb_signs_involutions.2.1 bb_signs_involutions.2.2
  obtain ⟨f₁,hs₁,ht₁,ha₁,he₁⟩ := bb_kill_first n f₀ ht₀
  have hc₁ := bb_central_zero n f₁ hs₁ ha₁
  have h0 := bb_last_independent n f₁ ha₁ hc₁
  have h2 := bb_last_erase n hn f₁ ht₁ h0
  obtain ⟨q,hqn,hq0,hq⟩ := exists_independent_shearStep 1 2 (by decide)
    (by decide) (by decide) 1 (by norm_num) (f₁ (bbRoot 2 1) : Poly)
    (f₁ (bbRoot 2 1)).property h2 h0
  let v : bbRep n := ⟨q,hqn⟩
  have hv0 : coboundary (bbRep n) v (bbRoot 0 1)=0 := by
    apply Subtype.ext
    change ((bbRep n).ρ (bbRoot 0 1) v : Poly)-q=0
    rw [bb_action_coe]
    change shear 0 1 q-q=0
    have h := first_shearStep_fixed 1 1 q hq0
    simpa only [shearStep_one, sub_eq_zero] using h
  have hv1 : coboundary (bbRep n) v (bbRoot 1 1)=0 := by
    apply Subtype.ext
    change ((bbRep n).ρ (bbRoot 1 1) v : Poly)-q=0
    rw [bb_action_coe]
    change shear 0 2 q-q=0
    have h := first_shearStep_fixed 2 1 q hq0
    simpa only [shearStep_one, sub_eq_zero] using h
  have hv2 : coboundary (bbRep n) v (bbRoot 2 1)=f₁ (bbRoot 2 1) := by
    apply Subtype.ext
    change ((bbRep n).ρ (bbRoot 2 1) v : Poly)-q=(f₁ (bbRoot 2 1) : Poly)
    rw [bb_action_coe]
    change shear 1 2 q-q=(f₁ (bbRoot 2 1) : Poly)
    simpa only [shearStep_one] using hq
  let f₂ := f₁-coboundary (bbRep n) v
  have hr (k : Fin 3) : f₂ (bbRoot k 1)=0 := by
    change f₁ (bbRoot k 1)-coboundary (bbRep n) v (bbRoot k 1)=0
    fin_cases k
    · change f₁ (bbRoot 0 1)-coboundary (bbRep n) v (bbRoot 0 1)=0
      rw [ha₁,hv0,sub_self]
    · change f₁ (bbRoot 1 1)-coboundary (bbRep n) v (bbRoot 1 1)=0
      rw [hc₁,hv1,sub_self]
    · change f₁ (bbRoot 2 1)-coboundary (bbRep n) v (bbRoot 2 1)=0
      rw [hv2,sub_self]
  obtain ⟨f₃,hs₃,ht₃,hr₃,he₃⟩ := bb_normalize n f₂ Set.univ (fun k _ => hr k)
  have hz : f₃=0 := RelativeEdgeCohomologyGenerators.bb_eq_zero (bbRep n) f₃ hs₃ ht₃
    (fun k => hr₃ k trivial)
  have he₂ := H1_sub_coboundary (bbRep n) f₁ v
  have he : H1π (bbRep n) f₃=H1π (bbRep n) f := he₃.trans (he₂.trans (he₁.trans he₀))
  rw [← he,hz,map_zero]

end TernaryPoly.RelativeEdgeCohomologyBB
