module

public import TernaryPeriodPolynomials.GroupCohomology.Relative.Edge.CohomologyActions
public import TernaryPeriodPolynomials.GroupCohomology.Relative.Edge.CohomologyNormalization

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.RelativeEdgeCohomologyBG
open CategoryTheory CategoryTheory.Limits groupCohomology
open RelativeStabilizerConsumer RelativeEdgeCohomologyMatrices RelativeEdgeCohomologyActions
open RelativeEdgeCohomologyPolynomials RelativeEdgeCohomologyCocycles
open RadicalCoinvariantAlgebra

lemma bg_normalize (n : ℕ) (f : cocycles₁ (bgRep n)) (I : Set (Fin 3))
    (hI : ∀ k ∈ I, f (bgRoot k 1)=0) :
    ∃ f' : cocycles₁ (bgRep n), f' bgFirst=0 ∧ f' bgSecond=0 ∧
      (∀ k ∈ I, f' (bgRoot k 1)=0) ∧ H1π (bgRep n) f'=H1π (bgRep n) f := by
  obtain ⟨f',hs,ht,hr,hf⟩ := normalize_two_preserving (bgRep n) f bgFirst bgSecond
    bg_signs_involutions.1 bg_signs_involutions.2.1 bg_signs_involutions.2.2
    ((fun k => bgRoot k 1) '' I) (by rintro g ⟨k,hk,rfl⟩; exact hI k hk)
    (by
      rintro g ⟨k,_,rfl⟩
      fin_cases k
      · right; simpa using bgFirst_root 0 1
      · left; simpa using bgFirst_root 1 1
      · right; simpa using bgFirst_root 2 1)
    (by
      rintro g ⟨k,_,rfl⟩
      fin_cases k
      · left; simpa using bgSecond_root 0 1
      · right; simpa using bgSecond_root 1 1
      · right; simpa using bgSecond_root 2 1)
  exact ⟨f',hs,ht,fun k hk => hr _ ⟨k,hk,rfl⟩,hf⟩

lemma bg_first_erase (n : ℕ) (hn : Even n) (f : cocycles₁ (bgRep n))
    (hs : f bgFirst=0) (ht : f bgSecond=0) : erase 2 (f (bgRoot 0 1) : Poly)=0 := by
  have h := inverted_quotient (bgRep n) (eraseCoeff n 2) f bgFirst (bgRoot 0 1) hs
    (by rw [bgFirst_root]; simp) (fun p => by
      change erase 2 ((bgRep n).ρ (bgRoot 0 1) p : Poly)=erase 2 p
      rw [bg_action_coe]
      exact erase_shearStep 0 2 (by decide) 1 p)
  change erase 2 ((bgRep n).ρ bgFirst (f (bgRoot 0 1)) : Poly) =
    -erase 2 (f (bgRoot 0 1) : Poly) at h
  rw [bg_first_coe, erase_flip,
    even_erase2_flip0_eq_flip1 _ (f (bgRoot 0 1)).property hn] at h
  have htfix := commuting_fixed (bgRep n) f bgSecond (bgRoot 0 1) ht
    (by simpa using bgSecond_root 0 1)
  have htfix' := congrArg (fun p : bgRep n => erase 2 (p : Poly)) htfix
  rw [bg_second_coe, erase_flip] at htfix'
  rw [htfix'] at h
  exact zero_of_neg_eq_self _ h

lemma bg_central_zero (n : ℕ) (f : cocycles₁ (bgRep n))
    (hs : f bgFirst=0) (ha : f (bgRoot 0 1)=0) : f (bgRoot 2 1)=0 := by
  have hp := commuting_fixed (bgRep n) f (bgRoot 0 1) (bgRoot 2 1) ha (bg_first_central 1 1)
  have hp' := congrArg (fun p : bgRep n => (p : Poly)) hp
  rw [bg_action_coe] at hp'
  have hp'' : shear 0 2 (f (bgRoot 2 1) : Poly)=(f (bgRoot 2 1) : Poly) := by
    simpa only [Matrix.cons_val_zero, shearStep_one] using hp'
  have h0 := shear_fixed_erase 1 (f (bgRoot 2 1) : Poly) hp''
  apply inverted_root_zero (bgRep n) f bgFirst (bgRoot 2 1) hs
    (by rw [bgFirst_root]; simp)
  · apply Subtype.ext
    rw [bg_action_coe]
    exact first_shearStep_fixed 1 1 _ h0
  · apply Subtype.ext
    rw [bg_first_coe]
    exact flip_fixed_of_erase 0 _ h0

lemma bg_last_independent (n : ℕ) (f : cocycles₁ (bgRep n))
    (ha : f (bgRoot 0 1)=0) (hc : f (bgRoot 2 1)=0) :
    erase 0 (f (bgRoot 1 1) : Poly)=(f (bgRoot 1 1) : Poly) := by
  have hc3 : f (bgRoot 2 3)=0 := by
    rw [bgRoot_zpow]
    exact (zeroSubgroup (bgRep n) f).zpow_mem hc 3
  have hp := commutator_fixed (bgRep n) f (bgRoot 0 1) (bgRoot 1 1) (bgRoot 2 3)
    ha hc3 (by simpa using bg_commutator 1 1)
  have hp' := congrArg (fun p : bgRep n => (p : Poly)) hp
  rw [bg_action_coe] at hp'
  apply shear_fixed_erase 1
  change shear 0 2 (f (bgRoot 1 1) : Poly)=(f (bgRoot 1 1) : Poly)
  simpa only [Matrix.cons_val_zero, shearStep_one] using hp'

lemma bg_last_erase (n : ℕ) (f : cocycles₁ (bgRep n)) (ht : f bgSecond=0) :
    erase 1 (f (bgRoot 1 1) : Poly)=0 := by
  have h := inverted_quotient (bgRep n) (eraseCoeff n 1) f bgSecond (bgRoot 1 1) ht
    (by rw [bgSecond_root]; simp) (fun p => by
      change erase 1 ((bgRep n).ρ (bgRoot 1 1) p : Poly)=erase 1 p
      rw [bg_action_coe]
      exact erase_shearStep 2 1 (by decide) 3 p)
  change erase 1 ((bgRep n).ρ bgSecond (f (bgRoot 1 1)) : Poly) =
    -erase 1 (f (bgRoot 1 1) : Poly) at h
  rw [bg_second_coe, erase_flip, flip_erase_self] at h
  exact zero_of_neg_eq_self _ h

lemma bg_kill_first (n : ℕ) (hn : Even n) (f : cocycles₁ (bgRep n))
    (hs : f bgFirst=0) (ht : f bgSecond=0) :
    ∃ f' : cocycles₁ (bgRep n), f' bgFirst=0 ∧ f' bgSecond=0 ∧
      f' (bgRoot 0 1)=0 ∧ H1π (bgRep n) f'=H1π (bgRep n) f := by
  obtain ⟨q,hqn,hq⟩ := (exists_homogeneous_shear_sub_iff 1 (f (bgRoot 0 1) : Poly)
    (f (bgRoot 0 1)).property).mpr (bg_first_erase n hn f hs ht)
  let v : bgRep n := ⟨q,hqn⟩
  have hv : coboundary (bgRep n) v (bgRoot 0 1)=f (bgRoot 0 1) := by
    apply Subtype.ext
    change ((bgRep n).ρ (bgRoot 0 1) v : Poly)-q=(f (bgRoot 0 1) : Poly)
    rw [bg_action_coe]
    change shearStep 0 2 1 q-q=(f (bgRoot 0 1) : Poly)
    rw [shearStep_one]
    exact hq
  let g := f-coboundary (bgRep n) v
  have hg : g (bgRoot 0 1)=0 := by
    change f (bgRoot 0 1)-coboundary (bgRep n) v (bgRoot 0 1)=0
    rw [hv,sub_self]
  obtain ⟨f',hs',ht',hr,he⟩ := bg_normalize n g {0} (by
    intro k hk; have hk' : k=0 := hk; subst k; exact hg)
  refine ⟨f',hs',ht',hr 0 rfl, ?_⟩
  exact he.trans (H1_sub_coboundary (bgRep n) f v)

/-- Direct cocycle elimination with the exact level-three root proves BG H1 vanishing. -/
theorem bg_H1_zero (n : ℕ) (hn : Even n) : IsZero (groupCohomology (bgRep n) 1) := by
  apply isZero_H1_of_classes
  intro f
  obtain ⟨f₀,hs₀,ht₀,he₀⟩ := normalize_two (bgRep n) f bgFirst bgSecond
    bg_signs_involutions.1 bg_signs_involutions.2.1 bg_signs_involutions.2.2
  obtain ⟨f₁,hs₁,ht₁,ha₁,he₁⟩ := bg_kill_first n hn f₀ hs₀ ht₀
  have hc₁ := bg_central_zero n f₁ hs₁ ha₁
  have h0 := bg_last_independent n f₁ ha₁ hc₁
  have h1 := bg_last_erase n f₁ ht₁
  obtain ⟨q,hqn,hq0,hq⟩ := exists_independent_shearStep 2 1 (by decide)
    (by decide) (by decide) 3 (by norm_num) (f₁ (bgRoot 1 1) : Poly)
    (f₁ (bgRoot 1 1)).property h1 h0
  let v : bgRep n := ⟨q,hqn⟩
  have hv0 : coboundary (bgRep n) v (bgRoot 0 1)=0 := by
    apply Subtype.ext
    change ((bgRep n).ρ (bgRoot 0 1) v : Poly)-q=0
    rw [bg_action_coe, sub_eq_zero]
    exact first_shearStep_fixed 2 1 q hq0
  have hv2 : coboundary (bgRep n) v (bgRoot 2 1)=0 := by
    apply Subtype.ext
    change ((bgRep n).ρ (bgRoot 2 1) v : Poly)-q=0
    rw [bg_action_coe, sub_eq_zero]
    exact first_shearStep_fixed 1 1 q hq0
  have hv1 : coboundary (bgRep n) v (bgRoot 1 1)=f₁ (bgRoot 1 1) := by
    apply Subtype.ext
    change ((bgRep n).ρ (bgRoot 1 1) v : Poly)-q=(f₁ (bgRoot 1 1) : Poly)
    rw [bg_action_coe]
    exact hq
  let f₂ := f₁-coboundary (bgRep n) v
  have hr (k : Fin 3) : f₂ (bgRoot k 1)=0 := by
    change f₁ (bgRoot k 1)-coboundary (bgRep n) v (bgRoot k 1)=0
    fin_cases k
    · change f₁ (bgRoot 0 1)-coboundary (bgRep n) v (bgRoot 0 1)=0
      rw [ha₁,hv0,sub_self]
    · change f₁ (bgRoot 1 1)-coboundary (bgRep n) v (bgRoot 1 1)=0
      rw [hv1,sub_self]
    · change f₁ (bgRoot 2 1)-coboundary (bgRep n) v (bgRoot 2 1) = 0
      rw [hc₁,hv2,sub_self]
  obtain ⟨f₃,hs₃,ht₃,hr₃,he₃⟩ := bg_normalize n f₂ Set.univ (fun k _ => hr k)
  have hz : f₃=0 := RelativeEdgeCohomologyGenerators.bg_eq_zero (bgRep n) f₃ hs₃ ht₃
    (fun k => hr₃ k trivial)
  have he₂ := H1_sub_coboundary (bgRep n) f₁ v
  have he : H1π (bgRep n) f₃=H1π (bgRep n) f := he₃.trans (he₂.trans (he₁.trans he₀))
  rw [← he,hz,map_zero]

end TernaryPoly.RelativeEdgeCohomologyBG
