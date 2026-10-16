module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.FlatChain
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.Cell.Support

@[expose] public section


/-!
# Lemma 3.3, G3: the interior points of the compactified flat lie in the flat

A point of the image of a chamber map `chamber (permGL σ)` that lies in the interior (the image of the
symmetric space under `embedding`) has strictly positive simple-root parameters and is therefore the image of a
permutation conjugate of a diagonal form, hence of a diagonal form: it lies in the diagonal flat
(`chamber_perm_interior_flat`, `fk_interior_flat`).

Formalized by Claude Sonnet 5.5.
-/

open TernaryPoly TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceRationalAction
  TernaryPoly.SymmetricSpaceRationalGluing TernaryPoly.SymmetricSpaceFlagCoordinates
  TernaryPeriodPolynomials.Argument.Lemma33
  TernaryPeriodPolynomials.Argument.Lemma33.Retract.LocalDegree

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Lemma33.Locality

theorem conj_perm_diag (σ : Equiv.Perm (Fin 3)) (d : Fin 3 → ℝ) (i j : Fin 3) (hij : i ≠ j) :
    (conjugate (realRational (permGL σ)) (Matrix.diagonal d)) i j = 0 := by
  unfold conjugate
  simp only [permGL, realRational]
  simp [Matrix.mul_apply, PEquiv.toMatrix_apply, Matrix.diagonal_apply, Matrix.star_apply]
  intro h
  exact absurd h hij

theorem act_perm_diagSpace_offdiag (σ : Equiv.Perm (Fin 3)) (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (i j : Fin 3) (hij : i ≠ j) :
    (act (realRational (permGL σ)) (diagSpace s t hs ht)).val i j = 0 := by
  change (SymmetricSpacePositive.normalize
    (conjugate (realRational (permGL σ)) (diagSpace s t hs ht).val)) i j = 0
  rw [diagSpace_val]
  unfold SymmetricSpacePositive.normalize
  rw [conjugate_smul]
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [conj_perm_diag σ _ i j hij]
  simp

theorem chamber_perm_interior_flat (σ : Equiv.Perm (Fin 3)) (q : ℝ × ℝ) (S : Space)
    (h : embedding S = chamber (permGL σ) q) : S ∈ flat := by
  have hmem : chart (permGL σ) ((0 : Vec3), (clampH q.1, clampH q.2)) ∈ Set.range embedding :=
    ⟨S, h⟩
  have hci := (chart_preimage_embedding (permGL σ)).subset hmem
  obtain ⟨hs, ht⟩ := hci
  change embedding S = chamberH (permGL σ) (clampH q.1, clampH q.2) at h
  rw [chamberH_pos (permGL σ) _ hs ht] at h
  have hS := embedding_injective h
  rw [mem_flat_iff_unip, unip_eq_zero_iff]
  intro i j hij
  rw [hS]
  exact act_perm_diagSpace_offdiag σ _ _ hs ht i j hij

theorem fk_interior_flat (k : ℕ) (q : ℝ × ℝ) (S : Space) (h : embedding S = fk k q) : S ∈ flat :=
  chamber_perm_interior_flat (hexPerm k) q S h

end TernaryPeriodPolynomials.Argument.Lemma33.Locality
