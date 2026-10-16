module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryFiniteness.ModularPingPong
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryFiniteness.PresentedExtensions
public import Mathlib.Analysis.Complex.UpperHalfPlane.FixedPoints
public import Mathlib.Algebra.QuadraticDiscriminant

@[expose] public section


namespace TernaryPeriodPolynomials.BoundaryFiniteness.ModularPresentation

noncomputable section

open Matrix ModularGroup
open TernaryPeriodPolynomials.BoundaryFiniteness.ModularPingPong

def realMap : Modular →* GeneralLinearGroup (Fin 2) ℝ :=
  SpecialLinearGroup.toGL.comp (SpecialLinearGroup.map (Int.castRingHom ℝ))

theorem realMap_injective : Function.Injective realMap := by
  intro left right equation
  apply Subtype.ext
  ext i j
  apply Int.cast_injective (α := ℝ)
  exact congrArg (fun g : GeneralLinearGroup (Fin 2) ℝ => g.val i j) equation

theorem kernel_commute (g : action.ker) (h : Modular) : g.val * h = h * g.val := by
  have fixed (z : UpperHalfPlane) : realMap g.val • z = z := by
    change SpecialLinearGroup.toGL ((SpecialLinearGroup.map (Int.castRingHom ℝ)) g.val) • z = z
    rw [← ModularGroup.sl_moeb]
    exact congrArg (fun permutation : Equiv.Perm UpperHalfPlane => permutation z) g.property
  have central := UpperHalfPlane.forall_smul_eq_self_iff_mem_center.mp fixed
  apply realMap_injective
  simpa only [map_mul] using (Subgroup.mem_center_iff.mp central (realMap h)).symm

theorem kernel_entries (g : action.ker) :
    g.val.val 0 1 = 0 ∧ g.val.val 1 0 = 0 ∧ g.val.val 0 0 = g.val.val 1 1 := by
  have s := kernel_commute g S
  have t := kernel_commute g T
  have s00 := congrArg (fun matrix : Modular => matrix.val 0 0) s
  have t00 := congrArg (fun matrix : Modular => matrix.val 0 0) t
  have t01 := congrArg (fun matrix : Modular => matrix.val 0 1) t
  change (g.val.val * S.val) 0 0 = (S.val * g.val.val) 0 0 at s00
  change (g.val.val * T.val) 0 0 = (T.val * g.val.val) 0 0 at t00
  change (g.val.val * T.val) 0 1 = (T.val * g.val.val) 0 1 at t01
  norm_num [coe_S, coe_T, Matrix.mul_apply, Fin.sum_univ_two] at s00 t00 t01
  omega

theorem kernel_cases (g : action.ker) : g.val = 1 ∨ g.val = -1 := by
  obtain ⟨upper, lower, diagonal⟩ := kernel_entries g
  have determinant := g.val.property
  rw [Matrix.det_fin_two, upper, lower, ← diagonal] at determinant
  have sign : g.val.val 0 0 = 1 ∨ g.val.val 0 0 = -1 := by
    apply (sq_eq_one_iff).mp
    nlinarith
  rcases sign with positive | negative
  · left
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [upper, lower, ← diagonal, positive]
  · right
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [upper, lower, ← diagonal, negative]

instance kernel_finite : Finite action.ker := by
  apply Set.Finite.to_subtype
  apply Set.Finite.subset (Set.toFinite ({1, -1} : Set Modular))
  intro g membership
  exact kernel_cases ⟨g, membership⟩

theorem finitelyPresented : Group.IsFinitelyPresented Modular := by
  let := projective_finitelyPresented
  have kernel_equality : action.rangeRestrict.ker = action.ker := by
    ext g
    simp only [MonoidHom.mem_ker]
    exact Subtype.ext_iff
  let : Finite action.rangeRestrict.ker := kernel_equality ▸ kernel_finite
  exact PresentedExtensions.finitelyPresented action.rangeRestrict action.rangeRestrict_surjective

end

end TernaryPeriodPolynomials.BoundaryFiniteness.ModularPresentation

