module

public import TernaryPeriodPolynomials.GroupCohomology.Radical.FirstCohomologyPlaneTodd
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCohomology.FirstCohomologyCocycles
public import TernaryPeriodPolynomials.GroupCohomology.Radical.TopCohomologyPlane

@[expose] public section


open CategoryTheory MvPolynomial Matrix
noncomputable section
namespace TernaryPoly.RadicalFirstCohomology
open LatticeTopCohomology RadicalFirstCohomologyLattice RadicalCoinvariantAlgebra
open RadicalTopCohomology RadicalFirstCohomologyTodd groupCohomology
open RadicalFirstCohomologyAlgebra (planeFlip plane_sign_exact)
open RelativeStabilizerParameters RelativeStabilizerMatrices

/-- The actual plane Levi acts on the genuine first cohomology of its integral radical. -/
def planeH1Action (n : ℕ) (M : GL2) :
    groupCohomology (planeRep n) 1 ⟶ groupCohomology (planeRep n) 1 :=
  groupCohomology.map (matrixLattice M⁻¹).toMonoidHom (planeCoefficientHom n M) 1

theorem plane_sign_matrix : planeElement (-1) 0=diagonalHom (-1,-1) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [planeElement_val,planeMatrix,diagonalHom,bbMatrix]

theorem plane_sign_lattice (g : Lattice) : matrixLattice ((-1 : GL2)⁻¹) g=g⁻¹ := by
  change (matrixLattice ((-1 : GL2)⁻¹) g).toAdd=(-g.toAdd.1,-g.toAdd.2)
  rw [matrixLattice_coordinates]
  simp [Matrix.neg_mulVec,Matrix.one_mulVec]

theorem plane_sign_coefficient (n : ℕ) (v : H n) :
    ((planeCoefficientHom n (-1) v : H n) : Poly)=planeFlip v := by
  change (PolynomialGLAction.integralAction n 0 (planeElement (-1) 0) v : Poly)=_
  rw [plane_sign_matrix,integralAction_diagonal]
  simp [diagonalSubst,unitScalar,planeFlip]

theorem plane_cocycle_closed (n : ℕ) (c : cocycles₁ (planeRep n)) :
    shear 0 2 ((c second : H n) : Poly)-((c second : H n) : Poly)=
      shear 1 2 ((c first : H n) : Poly)-((c first : H n) : Poly) := by
  have h₀ := (mem_cocycles₁_iff c).mp c.property first second
  have h₁ := (mem_cocycles₁_iff c).mp c.property second first
  rw [mul_comm first second] at h₀
  rw [h₁,planeRep_first,planeRep_second] at h₀
  have h := congrArg (fun v : H n => (v : Poly)) h₀
  change shear 1 2 ((c first : H n) : Poly)+((c second : H n) : Poly)=
    shear 0 2 ((c second : H n) : Poly)+((c first : H n) : Poly) at h
  linear_combination -h

theorem plane_cocycle_sign_todd_first (n : ℕ) (c : cocycles₁ (planeRep n)) :
    ternaryTodd (X (1 : Fin 2))
      (((mapCocycles₁ (matrixLattice ((-1 : GL2)⁻¹)).toMonoidHom (planeCoefficientHom n (-1)) c) first : H n) : Poly)=
      -planeFlip (ternaryTodd (X (1 : Fin 2)) ((c first : H n) : Poly)) := by
  change ternaryTodd (X (1 : Fin 2))
    ((planeCoefficientHom n (-1) (c (matrixLattice ((-1 : GL2)⁻¹) first)) : H n) : Poly)=_
  rw [plane_sign_coefficient,plane_sign_lattice,firstTodd_planeFlip_shear]
  have hi := cocycles₁_map_inv c first
  rw [planeRep_first] at hi
  have hp := congrArg (fun v : H n => (v : Poly)) hi
  change shear 0 2 ((c first⁻¹ : H n) : Poly)= -((c first : H n) : Poly) at hp
  rw [hp,firstTodd_neg 1,map_neg]

theorem plane_cocycle_sign_todd_second (n : ℕ) (c : cocycles₁ (planeRep n)) :
    secondTodd
      (((mapCocycles₁ (matrixLattice ((-1 : GL2)⁻¹)).toMonoidHom (planeCoefficientHom n (-1)) c) second : H n) : Poly)=
      -planeFlip (secondTodd ((c second : H n) : Poly)) := by
  change secondTodd
    ((planeCoefficientHom n (-1) (c (matrixLattice ((-1 : GL2)⁻¹) second)) : H n) : Poly)=_
  rw [plane_sign_coefficient,plane_sign_lattice,secondTodd_planeFlip_shear]
  have hi := cocycles₁_map_inv c second
  rw [planeRep_second] at hi
  have hp := congrArg (fun v : H n => (v : Poly)) hi
  change shear 1 2 ((c second⁻¹ : H n) : Poly)= -((c second : H n) : Poly) at hp
  rw [hp,secondTodd_neg,map_neg]

/-- For even homogeneous degree the actual central plane sign is minus identity on genuine H¹. -/
theorem planeH1_sign (n : ℕ) (hn : Even n) :
    planeH1Action n (-1)= -𝟙 (groupCohomology (planeRep n) 1) := by
  apply LatticeFirstCohomology.map_H1_eq_neg_id
  intro c
  let a : Poly := ternaryTodd (X (1 : Fin 2)) ((c first : H n) : Poly)
  let b : Poly := secondTodd ((c second : H n) : Poly)
  have ha : a.IsHomogeneous n := ternaryTodd_homogeneous (show H n from c first).property (isHomogeneous_X ℚ 1)
  have hb : b.IsHomogeneous n := secondTodd_homogeneous (show H n from c second).property
  have hc : (-X 2)*pderiv 0 b-(-X 2)*pderiv 1 a=0 := planeTodd_closed _ _ (plane_cocycle_closed n c)
  obtain ⟨v,hv,hv₀,hv₁⟩ := plane_sign_exact hn ha hb hc
  refine ⟨⟨v,hv⟩,?_,?_⟩
  · rw [planeRep_first]
    apply Subtype.ext
    apply ternaryTodd_injective (X (1 : Fin 2))
    change ternaryTodd (X (1 : Fin 2))
      ((((mapCocycles₁ (matrixLattice ((-1 : GL2)⁻¹)).toMonoidHom (planeCoefficientHom n (-1)) c) first : H n) : Poly)+
        ((c first : H n) : Poly)) = _
    rw [firstTodd_add,plane_cocycle_sign_todd_first]
    change -planeFlip a+a=ternaryTodd (X (1 : Fin 2)) (shear 0 2 v-v)
    have hd := firstTodd_difference_poly 1 v
    simp only [Fin.succ_one_eq_two] at hd
    rw [hd]
    exact hv₀.symm
  · rw [planeRep_second]
    apply Subtype.ext
    apply secondTodd_injective
    change secondTodd
      ((((mapCocycles₁ (matrixLattice ((-1 : GL2)⁻¹)).toMonoidHom (planeCoefficientHom n (-1)) c) second : H n) : Poly)+
        ((c second : H n) : Poly)) = _
    rw [secondTodd_add,plane_cocycle_sign_todd_second]
    change -planeFlip b+b=secondTodd (shear 1 2 v-v)
    rw [secondTodd_difference]
    exact hv₁.symm

theorem planeH1_sign_fixed_zero (n : ℕ) (hn : Even n) (v : groupCohomology (planeRep n) 1)
    (hv : planeH1Action n (-1) v=v) : v=0 := by
  rw [planeH1_sign n hn] at hv
  change -v=v at hv
  have htwo : (2 : ℚ) • v=0 := by
    rw [two_smul]
    exact neg_eq_iff_add_eq_zero.mp hv
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

end TernaryPoly.RadicalFirstCohomology
