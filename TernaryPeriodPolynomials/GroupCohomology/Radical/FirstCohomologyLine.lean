module

public import TernaryPeriodPolynomials.GroupCohomology.Radical.FirstCohomologyLineTodd
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCohomology.FirstCohomologyCocycles
public import TernaryPeriodPolynomials.GroupCohomology.Radical.TopCohomologyLine

@[expose] public section


open CategoryTheory MvPolynomial
noncomputable section
namespace TernaryPoly.RadicalFirstCohomology
open LatticeTopCohomology RadicalFirstCohomologyLattice RadicalCoinvariantAlgebra
open RadicalTopCohomology RadicalFirstCohomologyTodd groupCohomology
open RadicalFirstCohomologyAlgebra (lineFlip line_sign_exact)

/-- The literal line diagonal sign acts on actual first group cohomology. -/
def lineH1Action (n : ℕ) (ε : ℤˣ × ℤˣ) :
    groupCohomology (lineRep n) 1 ⟶ groupCohomology (lineRep n) 1 :=
  groupCohomology.map (lineLattice ε).toMonoidHom (lineCoefficientHom n ε) 1

theorem line_sign_lattice (g : Lattice) : lineLattice (-1,1) g=g⁻¹ := by
  change Multiplicative.ofAdd (rootScale (-1,1) 0*g.toAdd.1,rootScale (-1,1) 1*g.toAdd.2)=g⁻¹
  change (rootScale (-1,1) 0*g.toAdd.1,rootScale (-1,1) 1*g.toAdd.2)=(-g.toAdd.1,-g.toAdd.2)
  simp [rootScale]

theorem line_sign_coefficient (n : ℕ) (v : H n) :
    ((lineCoefficientHom n (-1,1) v : H n) : Poly)=lineFlip v := by
  change (PolynomialGLAction.integralAction n 0
    (RelativeStabilizerParameters.diagonalHom (-1,1)) v : Poly)=_
  rw [integralAction_diagonal]
  simp [diagonalSubst,unitScalar,lineFlip]

/-- Generator evaluation of a genuine cocycle satisfies the literal line-radical closedness equation. -/
theorem line_cocycle_closed (n : ℕ) (c : cocycles₁ (lineRep n)) :
    shear 0 1 ((c second : H n) : Poly)-((c second : H n) : Poly)=
      shear 0 2 ((c first : H n) : Poly)-((c first : H n) : Poly) := by
  have h₀ := (mem_cocycles₁_iff c).mp c.property first second
  have h₁ := (mem_cocycles₁_iff c).mp c.property second first
  rw [mul_comm first second] at h₀
  rw [h₁,lineRep_first,lineRep_second] at h₀
  have h := congrArg (fun v : H n => (v : Poly)) h₀
  change shear 0 2 ((c first : H n) : Poly)+((c second : H n) : Poly)=
    shear 0 1 ((c second : H n) : Poly)+((c first : H n) : Poly) at h
  linear_combination -h

/-- At either actual line generator, the transformed Todd coordinate is minus its reflected coordinate. -/
theorem line_cocycle_sign_todd (n : ℕ) (c : cocycles₁ (lineRep n)) (g : Lattice) (j : Fin 2)
    (hg : (lineRep n).ρ g=homogeneousShear n 0 j.succ) :
    ternaryTodd (X j)
      (((mapCocycles₁ (lineLattice (-1,1)).toMonoidHom (lineCoefficientHom n (-1,1)) c) g : H n) : Poly)=
      -lineFlip (ternaryTodd (X j) ((c g : H n) : Poly)) := by
  change ternaryTodd (X j) ((lineCoefficientHom n (-1,1) (c (lineLattice (-1,1) g)) : H n) : Poly)=_
  rw [line_sign_coefficient,line_sign_lattice,firstTodd_lineFlip_shear]
  have hi := cocycles₁_map_inv c g
  rw [hg] at hi
  have hp := congrArg (fun v : H n => (v : Poly)) hi
  change shear 0 j.succ ((c g⁻¹ : H n) : Poly)= -((c g : H n) : Poly) at hp
  rw [hp,firstTodd_neg,map_neg]

/-- The independent line sign is minus identity on genuine H¹, in every homogeneous degree. -/
theorem lineH1_sign (n : ℕ) : lineH1Action n (-1,1)= -𝟙 (groupCohomology (lineRep n) 1) := by
  apply LatticeFirstCohomology.map_H1_eq_neg_id
  intro c
  let a : Poly := ternaryTodd (X (0 : Fin 2)) ((c first : H n) : Poly)
  let b : Poly := ternaryTodd (X (1 : Fin 2)) ((c second : H n) : Poly)
  have ha : a.IsHomogeneous n := ternaryTodd_homogeneous (show H n from c first).property (isHomogeneous_X ℚ 0)
  have hc : (-X 1)*pderiv 0 b-(-X 2)*pderiv 0 a=0 := lineTodd_closed _ _ (line_cocycle_closed n c)
  obtain ⟨v,hv,hv₀,hv₁⟩ := line_sign_exact ha hc
  refine ⟨⟨v,hv⟩,?_,?_⟩
  · rw [lineRep_first]
    apply Subtype.ext
    apply ternaryTodd_injective (X (0 : Fin 2))
    change ternaryTodd (X (0 : Fin 2))
      ((((mapCocycles₁ (lineLattice (-1,1)).toMonoidHom (lineCoefficientHom n (-1,1)) c) first : H n) : Poly)+
        ((c first : H n) : Poly)) = _
    rw [firstTodd_add,line_cocycle_sign_todd n c first 0 (by simpa only [Fin.succ_zero_eq_one] using lineRep_first n)]
    change -lineFlip a+a=ternaryTodd (X (0 : Fin 2)) (shear 0 1 v-v)
    have hd := firstTodd_difference_poly 0 v
    simp only [Fin.succ_zero_eq_one] at hd
    rw [hd]
    exact hv₀.symm
  · rw [lineRep_second]
    apply Subtype.ext
    apply ternaryTodd_injective (X (1 : Fin 2))
    change ternaryTodd (X (1 : Fin 2))
      ((((mapCocycles₁ (lineLattice (-1,1)).toMonoidHom (lineCoefficientHom n (-1,1)) c) second : H n) : Poly)+
        ((c second : H n) : Poly)) = _
    rw [firstTodd_add,line_cocycle_sign_todd n c second 1 (by simpa only [Fin.succ_one_eq_two] using lineRep_second n)]
    change -lineFlip b+b=ternaryTodd (X (1 : Fin 2)) (shear 0 2 v-v)
    have hd := firstTodd_difference_poly 1 v
    simp only [Fin.succ_one_eq_two] at hd
    rw [hd]
    exact hv₁.symm

/-- Consequently the actual line H¹ has no vectors fixed by its independent diagonal sign. -/
theorem lineH1_sign_fixed_zero (n : ℕ) (v : groupCohomology (lineRep n) 1)
    (hv : lineH1Action n (-1,1) v=v) : v=0 := by
  rw [lineH1_sign] at hv
  change -v=v at hv
  have htwo : (2 : ℚ) • v=0 := by
    rw [two_smul]
    exact neg_eq_iff_add_eq_zero.mp hv
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

end TernaryPoly.RadicalFirstCohomology
