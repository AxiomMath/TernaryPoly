module

public import TernaryPeriodPolynomials.GroupCohomology.Relative.Stabilizer.Parameters
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.Index

@[expose] public section


open Matrix
noncomputable section
namespace TernaryPoly.IntegralGL2Free
open RelativeStabilizerParameters

def rootMatrix (i : Fin 2) (t : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  ![![![1,2*t],![0,1]], ![![1,0],![2*t,1]]] i

/-- The two actual even integral root subgroups. -/
def root (i : Fin 2) (t : ℤ) : GL2 where
  val := rootMatrix i t
  inv := rootMatrix i (-t)
  val_inv := by
    ext r c
    rw [Matrix.mul_apply]
    fin_cases i <;> fin_cases r <;> fin_cases c <;>
      simp [rootMatrix,Fin.sum_univ_two]
  inv_val := by
    ext r c
    rw [Matrix.mul_apply]
    fin_cases i <;> fin_cases r <;> fin_cases c <;>
      simp [rootMatrix,Fin.sum_univ_two]

@[simp] lemma root_zero (i : Fin 2) : root i 0=1 := by
  apply Units.ext
  fin_cases i <;> ext r c <;> fin_cases r <;> fin_cases c <;> simp [root,rootMatrix]

lemma root_mul (i : Fin 2) (s t : ℤ) : root i s*root i t=root i (s+t) := by
  apply Units.ext
  change _*_=_
  fin_cases i <;> ext r c <;> rw [Matrix.mul_apply] <;>
    fin_cases r <;> fin_cases c <;> simp [root,rootMatrix,Fin.sum_univ_two] <;> ring

@[simp] lemma root_inv (i : Fin 2) (t : ℤ) : (root i t)⁻¹=root i (-t) := by
  apply inv_eq_of_mul_eq_one_right
  rw [root_mul,add_neg_cancel,root_zero]

lemma root_det (i : Fin 2) (t : ℤ) : (root i t).val.det=1 := by
  rw [Matrix.det_fin_two]
  fin_cases i <;> simp [root,rootMatrix]

def rootHom (i : Fin 2) : Multiplicative ℤ →* GL2 where
  toFun t := root i t.toAdd
  map_one' := root_zero i
  map_mul' s t := (root_mul i s.toAdd t.toAdd).symm

lemma root_zpow (i : Fin 2) (t : ℤ) : root i t=(root i 1)^t := by
  simpa [rootHom] using map_zpow (rootHom i) (Multiplicative.ofAdd 1) t

/-- The literal two-generator subgroup. -/
def generated : Subgroup GL2 := (FreeGroup.lift (fun i : Fin 2 => root i 1)).range

lemma root_mem_generated (i : Fin 2) (t : ℤ) : root i t ∈ generated := by
  rw [root_zpow]
  apply generated.zpow_mem
  exact ⟨FreeGroup.of i, by simp⟩

/-- Congruence shape stable under the two even elementary row operations. -/
def Good (g : GL2) : Prop :=
  g.val.det=1 ∧ g.val 0 0 % 4=1 ∧ g.val 1 1 % 4=1 ∧
    g.val 0 1 % 2=0 ∧ g.val 1 0 % 2=0

lemma upper_mul_entries (g : GL2) (t : ℤ) :
    (root 0 t*g).val =
      ![![g.val 0 0+2*t*g.val 1 0,g.val 0 1+2*t*g.val 1 1],![g.val 1 0,g.val 1 1]] := by
  change _*_=_
  ext r c
  rw [Matrix.mul_apply]
  fin_cases r <;> fin_cases c <;> simp [root,rootMatrix,Fin.sum_univ_two]

lemma lower_mul_entries (g : GL2) (t : ℤ) :
    (root 1 t*g).val =
      ![![g.val 0 0,g.val 0 1],![g.val 1 0+2*t*g.val 0 0,g.val 1 1+2*t*g.val 0 1]] := by
  change _*_=_
  ext r c
  rw [Matrix.mul_apply]
  fin_cases r <;> fin_cases c <;> simp [root,rootMatrix,Fin.sum_univ_two,add_comm]

lemma even_row_mod_four (a b t : ℤ) (hb : b%2=0) : (a+2*t*b)%4=a%4 := by
  obtain ⟨b',hb'⟩ := Int.dvd_of_emod_eq_zero hb
  rw [hb']
  have he : a+2*t*(2*b')=a+4*(t*b') := by ring
  rw [he]
  omega

lemma even_row_mod_two (a b t : ℤ) : (a+2*t*b)%2=a%2 := by
  rw [mul_assoc]
  omega

lemma Good.upper {g : GL2} (hg : Good g) (t : ℤ) : Good (root 0 t*g) := by
  rcases hg with ⟨hd,ha,he,hb,hc⟩
  refine ⟨by rw [Units.val_mul,Matrix.det_mul,root_det,hd,one_mul],?_,?_,?_,?_⟩ <;>
    rw [upper_mul_entries] <;> simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
  · rw [even_row_mod_four _ _ _ hc,ha]
  · exact he
  · rw [even_row_mod_two,hb]
  · exact hc

lemma Good.lower {g : GL2} (hg : Good g) (t : ℤ) : Good (root 1 t*g) := by
  rcases hg with ⟨hd,ha,he,hb,hc⟩
  refine ⟨by rw [Units.val_mul,Matrix.det_mul,root_det,hd,one_mul],?_,?_,?_,?_⟩ <;>
    rw [lower_mul_entries] <;> simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
  · exact ha
  · rw [even_row_mod_four _ _ _ hb,he]
  · exact hb
  · rw [even_row_mod_two,hc]

end TernaryPoly.IntegralGL2Free
