module

public import TernaryPeriodPolynomials.Polynomial.MultivariateIntegral
public import TernaryPeriodPolynomials.GroupCohomology.Radical.CoinvariantAlgebra
public import TernaryPeriodPolynomials.Topology.HomogeneousQuotient
public import TernaryPeriodPolynomials.Polynomial.Parity
public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.Tactic.LinearCombination

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.RadicalFirstCohomologyAlgebra
open MultivariateIntegral
abbrev Poly := MvPolynomial (Fin 3) ℚ

def planeFlip : Poly →ₐ[ℚ] Poly := bind₁ ![-X 0,-X 1,X 2]
def lineFlip : Poly →ₐ[ℚ] Poly := bind₁ ![-X 0,X 1,X 2]

/-- Closed pairs for the actual dual plane root derivatives have homogeneous potentials. -/
theorem plane_closed_potential {a b : Poly} {n : ℕ}
    (ha : a.IsHomogeneous n) (hb : b.IsHomogeneous n)
    (h : (-X 2)*pderiv 0 b-(-X 2)*pderiv 1 a=0) :
    ∃ F : Poly,F.IsHomogeneous (n+1) ∧ pderiv 0 F=a ∧ pderiv 1 F=b := by
  have hz : (X (2 : Fin 3) : Poly)≠0 := X_ne_zero 2
  have he : X 2*(pderiv 1 a-pderiv 0 b)=0 := by linear_combination h
  have hc : pderiv 1 a=pderiv 0 b := sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hz)
  exact exists_homogeneous_potential (by decide : (0 : Fin 3)≠1) ha hb hc

/-- A potential with zero binary restriction gives a genuine homogeneous exact pair. -/
theorem plane_potential_exact {F : Poly} {n : ℕ} (hF : F.IsHomogeneous (n+1))
    (he : RadicalCoinvariantAlgebra.erase 2 F=0) :
    ∃ g : Poly,g.IsHomogeneous n ∧
      (-X 2)*pderiv 0 g=pderiv 0 F ∧ (-X 2)*pderiv 1 g=pderiv 1 F := by
  obtain ⟨g,hg⟩ := (RadicalCoinvariantAlgebra.erase_eq_zero_iff 2 F).mp he
  have hgh : g.IsHomogeneous n := isHomogeneous_quotient_add
    (isHomogeneous_X ℚ 2) (X_ne_zero 2) (by simpa only [hg,Nat.add_comm] using hF)
  refine ⟨-g,hgh.neg,?_,?_⟩ <;> rw [hg] <;> simp

theorem pderiv_planeFlip_zero (F : Poly) :
    pderiv 0 (planeFlip F)= -planeFlip (pderiv 0 F) := by
  induction F using MvPolynomial.induction_on with
  | C r => simp [planeFlip]
  | add p q hp hq => simp only [map_add,hp,hq,neg_add]
  | mul_X p i hp =>
    simp only [planeFlip] at hp
    fin_cases i <;> simp [planeFlip,map_mul,map_add,hp]

theorem pderiv_planeFlip_one (F : Poly) :
    pderiv 1 (planeFlip F)= -planeFlip (pderiv 1 F) := by
  induction F using MvPolynomial.induction_on with
  | C r => simp [planeFlip]
  | add p q hp hq => simp only [map_add,hp,hq,neg_add]
  | mul_X p i hp =>
    simp only [planeFlip] at hp
    fin_cases i <;> simp [planeFlip,map_mul,map_add,hp]

theorem planeFlip_homogeneous {F : Poly} {n : ℕ} (hF : F.IsHomogeneous n) :
    (planeFlip F).IsHomogeneous n := by
  apply isHomogeneous_bind₁_linear hF
  intro i
  fin_cases i
  · exact (isHomogeneous_X ℚ 0).neg
  · exact (isHomogeneous_X ℚ 1).neg
  · exact isHomogeneous_X ℚ 2

/-- On odd homogeneous potentials the plane involution plus identity is divisible by X2. -/
theorem erase_planeFlip_add {F : Poly} {n : ℕ} (hF : F.IsHomogeneous n) (hn : Odd n) :
    RadicalCoinvariantAlgebra.erase 2 (planeFlip F+F)=0 := by
  have he := congrArg (RadicalCoinvariantAlgebra.erase 2) (homogeneous_bind_neg_odd hF hn)
  have hh : (RadicalCoinvariantAlgebra.erase 2).comp (bind₁ ![-X 0,-X 1,-X 2]) =
      (RadicalCoinvariantAlgebra.erase 2).comp planeFlip := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [planeFlip,AlgHom.comp_apply]
  change ((RadicalCoinvariantAlgebra.erase 2).comp (bind₁ ![-X 0,-X 1,-X 2])) F = _ at he
  rw [hh] at he
  simpa only [AlgHom.comp_apply,map_neg,map_add,add_eq_zero_iff_eq_neg] using he

/-- The true plane central sign acts by minus identity modulo exact derivative pairs. -/
theorem plane_sign_exact {a b : Poly} {n : ℕ} (hn : Even n)
    (ha : a.IsHomogeneous n) (hb : b.IsHomogeneous n)
    (h : (-X 2)*pderiv 0 b-(-X 2)*pderiv 1 a=0) :
    ∃ g : Poly,g.IsHomogeneous n ∧
      (-X 2)*pderiv 0 g= -planeFlip a+a ∧
      (-X 2)*pderiv 1 g= -planeFlip b+b := by
  obtain ⟨F,hF,haF,hbF⟩ := plane_closed_potential ha hb h
  obtain ⟨g,hg,hg0,hg1⟩ := plane_potential_exact
    ((planeFlip_homogeneous hF).add hF) (erase_planeFlip_add hF (hn.add_odd (by decide)))
  refine ⟨g,hg,?_,?_⟩
  · simpa only [map_add,pderiv_planeFlip_zero,haF] using hg0
  · simpa only [map_add,pderiv_planeFlip_one,hbF] using hg1

theorem finSuccEquiv_lineFlip (F : Poly) :
    finSuccEquiv ℚ 2 (lineFlip F)=(finSuccEquiv ℚ 2 F).comp (-Polynomial.X) := by
  induction F using MvPolynomial.induction_on with
  | C r => simp [lineFlip,finSuccEquiv_apply]
  | add p q hp hq => simp only [map_add,hp,hq,Polynomial.add_comp]
  | mul_X p i hp =>
    simp only [map_mul,hp,Polynomial.mul_comp]
    fin_cases i <;> simp [lineFlip,finSuccEquiv_X_zero,
      finSuccEquiv_ternary_X_one,finSuccEquiv_ternary_X_two]

/-- A polynomial killed by the first root derivative is fixed by its coordinate reflection. -/
theorem lineFlip_of_pderiv_zero {F : Poly} (h : pderiv 0 F=0) : lineFlip F=F := by
  apply (finSuccEquiv ℚ 2).injective
  rw [finSuccEquiv_lineFlip]
  have hd := congrArg (finSuccEquiv ℚ 2) h
  rw [finSuccEquiv_pderiv_zero,map_zero] at hd
  rw [Polynomial.eq_C_of_derivative_eq_zero hd,Polynomial.C_comp]

/-- The literal determinant coordinate of a line-root closed pair is independent of X0. -/
theorem line_coordinate_closed {a b : Poly}
    (h : (-X 1)*pderiv 0 b-(-X 2)*pderiv 0 a=0) :
    pderiv 0 (X 2*a-X 1*b)=0 := by
  simp only [map_sub,pderiv_mul,pderiv_X_of_ne (by decide : (2 : Fin 3)≠0),
    pderiv_X_of_ne (by decide : (1 : Fin 3)≠0),zero_mul,zero_add]
  linear_combination h

/-- The kernel of the literal determinant coordinate consists exactly of proportional pairs. -/
theorem line_coordinate_kernel {a b : Poly} (h : X 2*a-X 1*b=0) :
    ∃ t : Poly,a=X 1*t ∧ b=X 2*t := by
  have he : X 2*a=X 1*b := sub_eq_zero.mp h
  have hd : (X (1 : Fin 3) : Poly) ∣ X 2*a := ⟨b,he⟩
  have hx : ¬(X (1 : Fin 3) : Poly) ∣ X 2 := by rw [X_dvd_X]; decide
  obtain ⟨t,ht⟩ := (X_dvd_mul_iff.mp hd).resolve_left hx
  refine ⟨t,ht,?_⟩
  apply mul_left_cancel₀ (X_ne_zero (1 : Fin 3))
  rw [←he,ht]
  ring

/-- Every homogeneous pair in that kernel is an exact pair for the actual negative root maps. -/
theorem line_coordinate_exact {a b : Poly} {n : ℕ} (ha : a.IsHomogeneous n)
    (h : X 2*a-X 1*b=0) :
    ∃ g : Poly,g.IsHomogeneous n ∧ (-X 1)*pderiv 0 g=a ∧ (-X 2)*pderiv 0 g=b := by
  obtain ⟨t,hat,hbt⟩ := line_coordinate_kernel h
  by_cases ht : t=0
  · refine ⟨0,isHomogeneous_zero _ _ _,?_,?_⟩ <;> simp [hat,hbt,ht]
  have hn : 1≤n := by
    have ha0 : a≠0 := by rw [hat]; exact mul_ne_zero (X_ne_zero 1) ht
    have he := ha.totalDegree ha0
    rw [hat,totalDegree_mul_of_isDomain (X_ne_zero 1) ht,totalDegree_X] at he
    omega
  have hth : t.IsHomogeneous (n-1) := isHomogeneous_quotient
    (isHomogeneous_X ℚ 1) (X_ne_zero 1) (by rwa [←hat])
  refine ⟨integral 0 (-t),?_,?_,?_⟩
  · simpa only [Nat.sub_add_cancel hn] using integral_homogeneous 0 hth.neg
  · rw [pderiv_integral,hat]; ring
  · rw [pderiv_integral,hbt]; ring

theorem lineFlip_homogeneous {F : Poly} {n : ℕ} (hF : F.IsHomogeneous n) :
    (lineFlip F).IsHomogeneous n := by
  apply isHomogeneous_bind₁_linear hF
  intro i
  fin_cases i
  · exact (isHomogeneous_X ℚ 0).neg
  · exact isHomogeneous_X ℚ 1
  · exact isHomogeneous_X ℚ 2

/-- The independent line sign acts by minus identity modulo exact derivative pairs in every degree. -/
theorem line_sign_exact {a b : Poly} {n : ℕ}
    (ha : a.IsHomogeneous n)
    (h : (-X 1)*pderiv 0 b-(-X 2)*pderiv 0 a=0) :
    ∃ g : Poly,g.IsHomogeneous n ∧
      (-X 1)*pderiv 0 g= -lineFlip a+a ∧
      (-X 2)*pderiv 0 g= -lineFlip b+b := by
  have he := lineFlip_of_pderiv_zero (line_coordinate_closed h)
  have hz : X 2*(a-lineFlip a)-X 1*(b-lineFlip b)=0 := by
    have hh : lineFlip (X 2*a-X 1*b)=X 2*lineFlip a-X 1*lineFlip b := by
      simp [lineFlip]
    rw [hh] at he
    linear_combination -he
  obtain ⟨g,hg,hga,hgb⟩ := line_coordinate_exact (ha.sub (lineFlip_homogeneous ha)) hz
  exact ⟨g,hg,by simpa only [sub_eq_add_neg,add_comm] using hga,
    by simpa only [sub_eq_add_neg,add_comm] using hgb⟩

end TernaryPoly.RadicalFirstCohomologyAlgebra
