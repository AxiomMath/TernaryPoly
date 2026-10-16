module

public import TernaryPeriodPolynomials.Building.OrientedChain.ChainProjection

@[expose] public section


noncomputable section
namespace TernaryPoly.OrientedProjectionCalculus
open OrientedListChains OrientedChainProjection OrientedChainJoin
variable {V : Type*}

/-- All ordering-independent coordinate projections commute on the actual quotient. -/
theorem filter_commute (P Q : List V → Prop) (hP : PermInvariant P) (hQ : PermInvariant Q)
    (c : Chain V) : filter P hP (filter Q hQ c) = filter Q hQ (filter P hP c) := by
  have he : (filter P hP).comp (filter Q hQ) = (filter Q hQ).comp (filter P hP) := by
    apply chain_ext
    intro l
    classical
    by_cases hp : P l <;> by_cases hq : Q l <;> simp [hp,hq]
  exact LinearMap.congr_fun he c

/-- Applying a cardinality projection before an exact-face projection keeps just matching sizes. -/
theorem badFace_badCount (G : V → Prop) (s : Finset V) (n : ℕ) (c : Chain V) :
    badFaceProjection G s (badCountProjection G n c) =
      if s.card = n then badFaceProjection G s c else 0 := by
  classical
  have he : (badFaceProjection G s).comp (badCountProjection G n) =
      if s.card = n then badFaceProjection G s else 0 := by
    apply chain_ext
    intro l
    by_cases hs : badVertices G l = s
    · by_cases hn : s.card = n <;> simp [hs,hn,badCount]
    · by_cases hn : badCount G l = n <;> by_cases hsn : s.card = n <;> simp [hs,hn,hsn]
  have h := LinearMap.congr_fun he c
  split_ifs at h ⊢ <;> exact h

/-- Vanishing of one cardinality stratum forces all its exact components to vanish. -/
theorem badFace_eq_zero_of_badCount_eq_zero (G : V → Prop) (s : Finset V) (n : ℕ)
    (hs : s.card = n) (c : Chain V) (hc : badCountProjection G n c = 0) :
    badFaceProjection G s c = 0 := by
  have h := badFace_badCount G s n c
  rw [hc,map_zero,ite_eq_left hs] at h
  exact h.symm

/-- The zero-bad stratum and empty exact-face projection are literally the same map. -/
theorem badCount_zero_eq_badFace_empty (G : V → Prop) :
    badCountProjection G 0 = badFaceProjection G ∅ := by
  apply chain_ext
  intro l
  classical
  rw [badCountProjection_simplex,badFaceProjection_simplex]
  have he : badCount G l = 0 ↔ badVertices G l = ∅ := Finset.card_eq_zero
  by_cases h : badVertices G l = ∅
  · rw [ite_eq_left h,ite_eq_left (he.mpr h)]
  · rw [ite_eq_right h,ite_eq_right (fun hc => h (he.mp hc))]

/-- Taking the same cardinality component twice has no further effect. -/
theorem badCount_idempotent (G : V → Prop) (n : ℕ) (c : Chain V) :
    badCountProjection G n (badCountProjection G n c) = badCountProjection G n c :=
  filter_idempotent _ (fun h => by dsimp only [badCount]; rw [badVertices_perm G h]) c

end TernaryPoly.OrientedProjectionCalculus
