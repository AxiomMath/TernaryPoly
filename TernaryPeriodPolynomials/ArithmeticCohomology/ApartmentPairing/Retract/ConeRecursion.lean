module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.List.Enum
public import Mathlib.Data.String.Defs
public import Mathlib.Lean.Elab.InfoTree
public import Mathlib.Lean.Elab.Tactic.Basic
public import Mathlib.Lean.Elab.Tactic.Meta
public import Mathlib.Lean.Expr.Basic
public import Mathlib.Lean.Expr.ExtraRecognizers
public import Mathlib.Lean.Expr.Rat
public import Mathlib.Lean.GoalsLocation
public import Mathlib.Lean.MessageData.Trace
public import Mathlib.Lean.Meta
public import Mathlib.Lean.Meta.Basic
public import Mathlib.Lean.Meta.KAbstractPositions
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.Tactic.Basify.Attr

@[expose] public section



/-!
# The cone recursion for chains on affine simplices

Formal chains on ordered affine simplices with vertices in a type `P` (`AffChain`), the simplicial
boundary `dAff`, the straight-line cone `coneAff` (prepending a vertex), its boundary identities
(`dAff_cone_succ`, `dAff_cone_zero`), and the acyclic-model recursion
`φ_{n+1}(C) = bpt(C) * Σ_D inc(C,D) φ_n(D)`, `φ_0(C) = ε(C) [bpt C]` attached to a graded augmented
complex with `δ² = 0` and `ε δ = 0` (`ConeData`): `phi_boundary` says that `φ` is a chain map for the
boundary `inc`, `phi_smul` that it is equivariant when the data are, and `phi_support` that all
simplices of `φ(C)` have their vertices in a prescribed set `reach C`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.Lemma33.Retract

open Finsupp

variable {P Q : Type*}

/-- An ordered affine simplex with vertices in `P`. -/
abbrev AffSimp (P : Type*) (n : ℕ) := Fin (n + 1) → P

/-- Formal rational chains on ordered affine simplices. -/
abbrev AffChain (P : Type*) (n : ℕ) := AffSimp P n →₀ ℚ

/-- The `i`-th face. -/
def AffSimp.face {n : ℕ} (i : Fin (n + 2)) (y : AffSimp P (n + 1)) : AffSimp P n :=
  y ∘ i.succAbove

/-- The cone vertex prepended. -/
def AffSimp.cone {n : ℕ} (b : P) (y : AffSimp P n) : AffSimp P (n + 1) := Fin.cons b y

/-- The simplicial boundary. -/
def dAff (P : Type*) (n : ℕ) : AffChain P (n + 1) →ₗ[ℚ] AffChain P n :=
  linearCombination ℚ (fun y : AffSimp P (n + 1) =>
    ∑ i : Fin (n + 2), (-1 : ℚ) ^ (i : ℕ) • single (AffSimp.face i y) (1 : ℚ))

/-- The straight-line cone operator. -/
def coneAff (b : P) (n : ℕ) : AffChain P n →ₗ[ℚ] AffChain P (n + 1) :=
  lmapDomain ℚ ℚ (AffSimp.cone b)

/-- The augmentation of a chain of points. -/
def augAff (P : Type*) : AffChain P 0 →ₗ[ℚ] ℚ :=
  linearCombination ℚ (fun _ : AffSimp P 0 => (1 : ℚ))

/-- The chain of a point. -/
def ptAff (b : P) : AffChain P 0 := single (fun _ => b) (1 : ℚ)

/-- Push forward along a map of vertex sets. -/
def mapAff (f : P → Q) (n : ℕ) : AffChain P n →ₗ[ℚ] AffChain Q n :=
  lmapDomain ℚ ℚ (fun y : AffSimp P n => f ∘ y)

theorem dAff_single {n : ℕ} (y : AffSimp P (n + 1)) :
    dAff P n (single y 1) = ∑ i : Fin (n + 2), (-1 : ℚ) ^ (i : ℕ) • single (AffSimp.face i y) (1 : ℚ) := by
  simp [dAff]

theorem coneAff_single (b : P) {n : ℕ} (y : AffSimp P n) :
    coneAff b n (single y 1) = single (AffSimp.cone b y) (1 : ℚ) := by
  simp [coneAff, lmapDomain_apply, mapDomain_single]

theorem face_zero_cone (b : P) {n : ℕ} (y : AffSimp P (n + 1)) :
    AffSimp.face 0 (AffSimp.cone b y) = y := by
  funext k
  simp [AffSimp.face, AffSimp.cone]

theorem face_succ_cone (b : P) {n : ℕ} (y : AffSimp P (n + 1)) (j : Fin (n + 2)) :
    AffSimp.face j.succ (AffSimp.cone b y) = AffSimp.cone b (AffSimp.face j y) := by
  funext k
  refine Fin.cases ?_ (fun k' => ?_) k
  · simp [AffSimp.face, AffSimp.cone]
  · simp [AffSimp.face, AffSimp.cone, Fin.succ_succAbove_succ]

theorem dAff_cone_single_succ (b : P) {n : ℕ} (y : AffSimp P (n + 1)) :
    dAff P (n + 1) (coneAff b (n + 1) (single y 1)) =
      single y 1 - coneAff b n (dAff P n (single y 1)) := by
  rw [coneAff_single, dAff_single, dAff_single, Fin.sum_univ_succ, map_sum, face_zero_cone]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ, pow_succ, face_succ_cone, map_smul,
    coneAff_single]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [mul_neg_one, neg_smul]

theorem dAff_cone_single_zero (b : P) (y : AffSimp P 0) :
    dAff P 0 (coneAff b 0 (single y 1)) = single y 1 - augAff P (single y 1) • ptAff b := by
  rw [coneAff_single, dAff_single]
  simp [Fin.sum_univ_succ, ptAff, augAff, AffSimp.face, AffSimp.cone]
  have : (Fin.cons b (Fin.tail y) : Fin 1 → P) = fun _ => b := by
    funext k
    obtain rfl : k = 0 := Fin.fin_one_eq_zero k
    rfl
  rw [this, sub_eq_add_neg]

theorem dAff_cone_succ (b : P) {n : ℕ} (c : AffChain P (n + 1)) :
    dAff P (n + 1) (coneAff b (n + 1) c) = c - coneAff b n (dAff P n c) := by
  have h : dAff P (n + 1) ∘ₗ coneAff b (n + 1) = LinearMap.id - coneAff b n ∘ₗ dAff P n := by
    apply Finsupp.lhom_ext
    intro y a
    have e : single y a = a • single y (1 : ℚ) := by simp
    rw [e]
    simp only [LinearMap.comp_apply, map_smul, LinearMap.sub_apply, LinearMap.id_apply,
      dAff_cone_single_succ, smul_sub]
  exact LinearMap.congr_fun h c

theorem dAff_cone_zero (b : P) (c : AffChain P 0) :
    dAff P 0 (coneAff b 0 c) = c - augAff P c • ptAff b := by
  have h : dAff P 0 ∘ₗ coneAff b 0 = LinearMap.id - (augAff P).smulRight (ptAff b) := by
    apply Finsupp.lhom_ext
    intro y a
    have e : single y a = a • single y (1 : ℚ) := by simp
    rw [e]
    simp only [LinearMap.comp_apply, map_smul, LinearMap.sub_apply, LinearMap.id_apply,
      dAff_cone_single_zero, smul_sub, LinearMap.smulRight_apply]
  exact LinearMap.congr_fun h c

theorem mapAff_single (f : P → Q) {n : ℕ} (y : AffSimp P n) (a : ℚ) :
    mapAff f n (single y a) = single (f ∘ y) a := by
  simp [mapAff]

theorem mapAff_coneAff (f : P → Q) (b : P) {n : ℕ} (c : AffChain P n) :
    mapAff f (n + 1) (coneAff b n c) = coneAff (f b) n (mapAff f n c) := by
  have h : mapAff f (n + 1) ∘ₗ coneAff b n = coneAff (f b) n ∘ₗ mapAff f n := by
    apply Finsupp.lhom_ext
    intro y a
    have e : single y a = a • single y (1 : ℚ) := by simp
    rw [e]
    simp only [LinearMap.comp_apply, map_smul]
    rw [coneAff_single, mapAff_single, mapAff_single, coneAff_single]
    congr 2
    funext k
    refine Fin.cases ?_ (fun k' => ?_) k <;> simp [AffSimp.cone]
  exact LinearMap.congr_fun h c

theorem mapAff_ptAff (f : P → Q) (b : P) : mapAff f 0 (ptAff b) = ptAff (f b) := by
  rw [ptAff, mapAff_single]
  rfl


/-! ### The cone recursion -/

section Recursion

variable {ι P : Type*}

/-- Data for the cone recursion: a graded complex `(ι →₀ ℚ, δ, ε)` and base points. -/
structure ConeData (ι P : Type*) where
  grade : ι → ℕ
  inc : ι → ι →₀ ℚ
  eps : ι → ℚ
  bpt : ι → P
  inc_grade : ∀ C D, inc C D ≠ 0 → grade D + 1 = grade C
  eps_grade : ∀ C, grade C ≠ 0 → eps C = 0
  inc_inc : linearCombination ℚ inc ∘ₗ linearCombination ℚ inc = 0
  eps_inc : linearCombination ℚ eps ∘ₗ linearCombination ℚ inc = 0

namespace ConeData

variable (D : ConeData ι P)

/-- The cone recursion `φ_{n+1}(C) = bpt(C) * Σ_D inc(C,D) φ_n(D)`, `φ_0(C) = ε(C) [bpt C]`. -/
def phi : (n : ℕ) → ι → AffChain P n
  | 0, C => D.eps C • ptAff (D.bpt C)
  | n + 1, C => coneAff (D.bpt C) n (linearCombination ℚ (phi n) (D.inc C))

/-- Extension of `phi` to all chains of cells. -/
def Phi (n : ℕ) : (ι →₀ ℚ) →ₗ[ℚ] AffChain P n := linearCombination ℚ (D.phi n)

theorem Phi_single (n : ℕ) (C : ι) (a : ℚ) : D.Phi n (single C a) = a • D.phi n C := by
  simp [Phi]

theorem phi_succ (n : ℕ) (C : ι) :
    D.phi (n + 1) C = coneAff (D.bpt C) n (D.Phi n (D.inc C)) := rfl

theorem aug_Phi_zero (z : ι →₀ ℚ) : augAff P (D.Phi 0 z) = linearCombination ℚ D.eps z := by
  have h : augAff P ∘ₗ D.Phi 0 = linearCombination ℚ D.eps := by
    apply Finsupp.lhom_ext
    intro C a
    simp [Phi, phi, augAff, ptAff]
  exact LinearMap.congr_fun h z

theorem dAff_Phi_of_boundary (n : ℕ)
    (ih : ∀ C, D.grade C = n + 1 → dAff P n (D.phi (n + 1) C) = D.Phi n (D.inc C))
    (z : ι →₀ ℚ) (hz : ∀ C ∈ z.support, D.grade C = n + 1) :
    dAff P n (D.Phi (n + 1) z) = D.Phi n (linearCombination ℚ D.inc z) := by
  induction z using Finsupp.induction with
  | zero => simp
  | single_add C a f hCf ha ihf =>
    have hC : D.grade C = n + 1 := hz C (by
      rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_eq_same,
        Finsupp.notMem_support_iff.mp hCf, add_zero]
      exact ha)
    have hf : ∀ C' ∈ f.support, D.grade C' = n + 1 := fun C' h' =>
      hz C' (by
        rw [Finsupp.mem_support_iff] at h' ⊢
        by_cases hCC : C' = C
        · subst hCC; exact absurd (by simpa using hCf) h'
        · simpa [Finsupp.single_apply, Ne.symm hCC] using h')
    rw [map_add, map_add, map_add, ihf hf, Phi_single, linearCombination_single, map_smul,
      ih C hC, map_add, map_smul]

theorem phi_boundary : ∀ (n : ℕ) (C : ι), D.grade C = n + 1 →
    dAff P n (D.phi (n + 1) C) = D.Phi n (D.inc C)
  | 0, C, hC => by
    rw [phi_succ, dAff_cone_zero, aug_Phi_zero]
    have : linearCombination ℚ D.eps (D.inc C) = 0 := by
      have := LinearMap.congr_fun D.eps_inc (single C 1)
      simpa using this
    rw [this, zero_smul, sub_zero]
  | n + 1, C, hC => by
    rw [phi_succ, dAff_cone_succ]
    have hsupp : ∀ C' ∈ (D.inc C).support, D.grade C' = n + 1 + 1 - 1 := by
      intro C' h'
      have := D.inc_grade C C' (Finsupp.mem_support_iff.mp h')
      omega
    have h2 := dAff_Phi_of_boundary D (n) (fun C' hC' => phi_boundary n C' hC') (D.inc C) (by
      intro C' h'
      have := D.inc_grade C C' (Finsupp.mem_support_iff.mp h')
      omega)
    have h3 : linearCombination ℚ D.inc (D.inc C) = 0 := by
      have := LinearMap.congr_fun D.inc_inc (single C 1)
      simpa using this
    rw [h2, h3, map_zero, map_zero, sub_zero]

theorem support_coneAff_subset (b : P) {n : ℕ} (c : AffChain P n) :
    (coneAff b n c).support ⊆ c.support.image (AffSimp.cone b) := by
  classical
  rw [coneAff, lmapDomain_apply]
  exact Finsupp.mapDomain_support

theorem support_Phi_subset (n : ℕ) (z : ι →₀ ℚ) :
    (D.Phi n z).support ⊆ z.support.biUnion fun C => (D.phi n C).support := by
  classical
  intro y hy
  have e : D.Phi n z = ∑ C ∈ z.support, z C • D.phi n C := by
    rw [Phi, linearCombination_apply, Finsupp.sum]
  rw [e] at hy
  obtain ⟨C, hC, hyC⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hy)
  exact Finset.mem_biUnion.mpr ⟨C, hC, Finsupp.support_smul hyC⟩

/-- Every simplex of `phi n C` has its vertices in `reach C`. -/
theorem phi_support (reach : ι → Set P) (hb : ∀ C, D.bpt C ∈ reach C)
    (hr : ∀ C C', D.inc C C' ≠ 0 → reach C' ⊆ reach C) :
    ∀ (n : ℕ) (C : ι), ∀ y ∈ (D.phi n C).support, ∀ i, y i ∈ reach C
  | 0, C, y, hy, i => by
    classical
    unfold phi at hy
    have h1 := Finsupp.support_smul hy
    rw [ptAff] at h1
    have h2 := Finsupp.support_single_subset h1
    rw [Finset.mem_singleton] at h2
    rw [h2]
    exact hb C
  | n + 1, C, y, hy, i => by
    classical
    rw [phi_succ] at hy
    obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp (support_coneAff_subset _ _ hy)
    obtain ⟨C', hC', hy''⟩ := Finset.mem_biUnion.mp (support_Phi_subset D n _ hy')
    refine Fin.cases ?_ (fun k => ?_) i
    · exact hb C
    · exact hr C C' (Finsupp.mem_support_iff.mp hC') (phi_support reach hb hr n C' y' hy'' k)

section Equivariance

variable {G : Type*} [Group G] [MulAction G ι] [MulAction G P]

theorem phi_smul (hb : ∀ (g : G) C, D.bpt (g • C) = g • D.bpt C) (he : ∀ (g : G) C, D.eps (g • C) = D.eps C)
    (hinc : ∀ (g : G) C, D.inc (g • C) = mapDomain (g • ·) (D.inc C)) :
    ∀ (n : ℕ) (g : G) (C : ι), D.phi n (g • C) = mapAff (g • ·) n (D.phi n C)
  | 0, g, C => by
    rw [phi, phi, he, hb, map_smul, mapAff_ptAff]
  | n + 1, g, C => by
    rw [phi_succ, phi_succ, hb, mapAff_coneAff, hinc]
    congr 1
    have : D.Phi n ∘ₗ lmapDomain ℚ ℚ (g • ·) = mapAff (g • ·) n ∘ₗ D.Phi n := by
      apply Finsupp.lhom_ext
      intro C' a
      simp only [LinearMap.comp_apply, lmapDomain_apply, mapDomain_single, Phi_single, map_smul]
      rw [phi_smul hb he hinc n g C']
    exact LinearMap.congr_fun this (D.inc C)

end Equivariance

end ConeData

end Recursion

end TernaryPeriodPolynomials.Argument.Lemma33.Retract
