module

public import TernaryPeriodPolynomials.GroupCohomology.Relative.Edge.CohomologyPolynomials

@[expose] public section

open MvPolynomial
noncomputable section
namespace TernaryPoly.RelativeEdgeCohomologyPolynomials
open RadicalCoinvariantAlgebra

/-- Literal negation of a single coordinate. -/
def flip (i : Fin 3) : Poly →ₐ[ℚ] Poly :=
  bind₁ fun k => if k=i then -X k else X k

@[simp] lemma flip_X (i k : Fin 3) : flip i (X k) = if k=i then -X k else X k := by
  simp [flip]

lemma flip_flip (i : Fin 3) (p : Poly) : flip i (flip i p) = p := by
  have h : (flip i).comp (flip i) = AlgHom.id ℚ Poly := by
    ext k
    by_cases hk : k=i <;> simp [hk]
  exact DFunLike.congr_fun h p

lemma flip_erase_self (i : Fin 3) (p : Poly) : flip i (erase i p) = erase i p := by
  have h : (flip i).comp (erase i) = erase i := by
    ext k
    by_cases hk : k=i <;> simp [hk]
  exact DFunLike.congr_fun h p

lemma erase_flip (i j : Fin 3) (p : Poly) : erase j (flip i p) = flip i (erase j p) := by
  have h : (erase j).comp (flip i) = (flip i).comp (erase j) := by
    apply MvPolynomial.algHom_ext
    intro k
    fin_cases i <;> fin_cases j <;> fin_cases k <;> simp
  exact DFunLike.congr_fun h p

lemma flip_fixed_of_erase (i : Fin 3) (p : Poly) (h : erase i p = p) : flip i p = p := by
  rw [← h]
  exact flip_erase_self i p

lemma flip_all (p : Poly) : flip 0 (flip 1 (flip 2 p)) = bind₁ ![-X 0,-X 1,-X 2] p := by
  have h : (flip 0).comp ((flip 1).comp (flip 2)) = bind₁ ![-X 0,-X 1,-X 2] := by
    ext k
    fin_cases k <;> simp
  exact DFunLike.congr_fun h p

lemma even_erase2_flip0_eq_flip1 {n : ℕ} (p : Poly) (hp : p.IsHomogeneous n)
    (hn : Even n) : flip 0 (erase 2 p) = flip 1 (erase 2 p) := by
  have h := homogeneous_bind_neg_even (erase_homogeneous 2 hp) hn
  rw [← flip_all, flip_erase_self] at h
  have h' := congrArg (flip 0) h
  rw [flip_flip] at h'
  exact h'.symm

lemma even_axis_flip1 {n : ℕ} (p : Poly) (hp : p.IsHomogeneous n)
    (hn : Even n) (h0 : erase 0 p=p) (h2 : erase 2 p=p) : flip 1 p=p := by
  have h := even_erase2_flip0_eq_flip1 p hp hn
  rw [h2, flip_fixed_of_erase 0 p h0] at h
  exact h.symm

lemma erase_erase (i j : Fin 3) (p : Poly) : erase i (erase j p)=erase j (erase i p) := by
  have h : (erase i).comp (erase j)=(erase j).comp (erase i) := by
    apply MvPolynomial.algHom_ext
    intro k
    fin_cases i <;> fin_cases j <;> fin_cases k <;> simp
  exact DFunLike.congr_fun h p

lemma even_erase2_independent_flip1 {n : ℕ} (p : Poly) (hp : p.IsHomogeneous n)
    (hn : Even n) (h0 : erase 0 p=p) : flip 1 (erase 2 p)=erase 2 p := by
  apply even_axis_flip1 _ (erase_homogeneous 2 hp) hn
  · rw [erase_erase, h0]
  · exact erase_idempotent 2 p

end TernaryPoly.RelativeEdgeCohomologyPolynomials
