module

public import TernaryPeriodPolynomials.GroupCohomology.Relative.Edge.CohomologyPolynomials

@[expose] public section

open MvPolynomial
noncomputable section
namespace TernaryPoly.OrdinaryFaceRadical
open RadicalCoinvariantAlgebra RelativeEdgeCohomologyPolynomials

/-- A nonzero rational first-root step forces literal independence of its first coordinate. -/
theorem first_shearStep_fixed_erase (j : Fin 2) (t : ℚ) (ht : t≠0) (p : Poly)
    (hp : shearStep 0 j.succ t p=p) : erase 0 p=p := by
  have hh := congrArg (finSuccEquiv ℚ 2) hp
  rw [finSuccEquiv_shearStep] at hh
  have hc := polynomial_eq_constant_of_translation (finSuccEquiv ℚ 2 p)
    (-(C t*X j)) (neg_ne_zero.mpr (mul_ne_zero (C_ne_zero.mpr ht) (X_ne_zero j))) hh
  have he (q : MvPolynomial (Fin 2) ℚ) :
      finSuccEquiv ℚ 2 (rename Fin.succ q)=Polynomial.C q := by
    induction q using MvPolynomial.induction_on with
    | C r => simp [finSuccEquiv_apply]
    | add p q hp hq => simp only [map_add,hp,hq]
    | mul_X p i hp => simp only [map_mul,rename_X,finSuccEquiv_X_succ,hp]
  have hshape : p=rename Fin.succ ((finSuccEquiv ℚ 2 p).coeff 0) :=
    (finSuccEquiv ℚ 2).injective (hc.trans (he _).symm)
  rw [hshape]
  have hz (q : MvPolynomial (Fin 2) ℚ) : erase 0 (rename Fin.succ q)=rename Fin.succ q := by
    induction q using MvPolynomial.induction_on with
    | C r => simp [erase]
    | add p q hp hq => simp only [map_add,hp,hq]
    | mul_X p i hp => simp [hp]
  exact hz _

/-- The two actual plane-root substitutions commute at every rational lattice step. -/
theorem plane_shearStep_commute (t : ℚ) (p : Poly) :
    shearStep 0 2 t (shearStep 1 2 t p)=shearStep 1 2 t (shearStep 0 2 t p) := by
  have he : (shearStep 0 2 t).comp (shearStep 1 2 t)=
      (shearStep 1 2 t).comp (shearStep 0 2 t) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [AlgHom.comp_apply,shearStep]
  exact DFunLike.congr_fun he p

/-- A closed homogeneous plane-lattice pair with zero normal-coordinate restrictions is a
common difference. This holds at every nonzero rational step, including the actual step three. -/
theorem plane_pair_exact_of_erase_zero {n : ℕ} (t : ℚ) (ht : t≠0) (a b : Poly)
    (ha : a.IsHomogeneous n) (hb : b.IsHomogeneous n)
    (hclosed : shearStep 0 2 t b-b=shearStep 1 2 t a-a)
    (ha0 : erase 2 a=0) (hb0 : erase 2 b=0) :
    ∃ v : Poly,v.IsHomogeneous n ∧
      shearStep 0 2 t v-v=a ∧ shearStep 1 2 t v-v=b := by
  obtain ⟨v,hv,hva⟩ := exists_homogeneous_shearStep 0 2 (by decide) t ht a ha ha0
  let r := b-(shearStep 1 2 t v-v)
  have hrn : r.IsHomogeneous n := hb.sub ((isHomogeneous_bind₁_linear hv _
    (fun i => shearStep_linear 1 2 i t)).sub hv)
  have hr0 : erase 2 r=0 := by
    dsimp [r]
    rw [map_sub,map_sub,erase_shearStep 1 2 (by decide),hb0,sub_self,sub_self]
  have hrfix : shearStep 0 2 t r=r := by
    have hstep := congrArg (shearStep 1 2 t) hva
    rw [map_sub,←plane_shearStep_commute] at hstep
    dsimp [r]
    simp only [map_sub]
    linear_combination hclosed-hstep+hva
  have hrx : erase 0 r=r := first_shearStep_fixed_erase 1 t ht r hrfix
  obtain ⟨w,hw,hwx,hwstep⟩ := exists_independent_shearStep 1 2 (by decide)
    (by decide) (by decide) t ht r hrn hr0 hrx
  refine ⟨v+w,hv.add hw,?_,?_⟩
  · rw [map_add,first_shearStep_fixed 2 t w hwx]
    linear_combination hva
  · rw [map_add]
    dsimp [r] at hwstep
    linear_combination hwstep

end TernaryPoly.OrdinaryFaceRadical
