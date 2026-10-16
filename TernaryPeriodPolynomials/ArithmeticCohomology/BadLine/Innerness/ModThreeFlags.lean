module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BadLine.Innerness.IntegralFlags

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Homogeneous Matrix

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers

theorem zmodThree_unit_sign (b : ZMod 3) (nonzero : b ≠ 0) :
    ∃ e : ℤ, e*e = 1 ∧ b*(e : ZMod 3) = 1 := by
  have sign : b = 1 ∨ b = -1 := by
    fin_cases b
    · exact (nonzero rfl).elim
    · exact Or.inl rfl
    · right
      change (2 : ZMod 3) = -1
      decide
  rcases sign with one | minus
  · exact ⟨1,by norm_num,by simp [one]⟩
  · exact ⟨-1,by norm_num,by simp [minus]⟩

def integralPlaneNormalize (r u e : ℤ) (unit : e*e = 1) : IntegralGL3 :=
  ⟨!![1,0,0;r,e,u;0,0,1],!![1,0,0;-e*r,e,-e*u;0,0,1],by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply,Fin.sum_univ_three,← mul_assoc,unit],by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply,Fin.sum_univ_three,unit]⟩

def integralLastSign (e : ℤ) (unit : e*e = 1) : IntegralGL3 :=
  ⟨!![1,0,0;0,1,0;0,0,e],!![1,0,0;0,1,0;0,0,e],by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply,Fin.sum_univ_three,unit],by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply,Fin.sum_univ_three,unit]⟩

def integralSwap23 : IntegralGL3 :=
  ⟨!![1,0,0;0,0,1;0,1,0],!![1,0,0;0,0,1;0,1,0],by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply,Fin.sum_univ_three],by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply,Fin.sum_univ_three]⟩

theorem integralSwap23_map : GeneralLinearGroup.map (Int.castRingHom ℚ) integralSwap23 = swapLastTwo := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [integralSwap23,swapLastTwo,GeneralLinearGroup.map_apply]

theorem swapLastTwo_square : swapLastTwo*swapLastTwo = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapLastTwo,Matrix.mul_apply,Fin.sum_univ_three]

theorem integral_plane_orbit_of_second_nonzero (V : IntegralGL3)
    (nonzero : (V.val 2 1 : ZMod 3) ≠ 0) :
    ∃ transport : rationalLevel,
      (QuotientGroup.mk (GeneralLinearGroup.map (Int.castRingHom ℚ) V) : Flags .plane) =
        transport.val • QuotientGroup.mk swapLastTwo := by
  let a : ZMod 3 := V.val 2 0
  let b : ZMod 3 := V.val 2 1
  let c : ZMod 3 := V.val 2 2
  obtain ⟨e,unit,sign⟩ := zmodThree_unit_sign b nonzero
  obtain ⟨r,hr⟩ := ZMod.intCast_surjective (-a/b)
  obtain ⟨u,hu⟩ := ZMod.intCast_surjective (-c/b)
  have bn : b ≠ 0 := nonzero
  have first_zero : a+b*(r : ZMod 3) = 0 := by rw [hr]; field_simp [bn]; ring
  have third_zero : c+b*(u : ZMod 3) = 0 := by rw [hu]; field_simp [bn]; ring
  let N := integralPlaneNormalize r u e unit
  let W := V*N*integralSwap23
  have level : W ∈ arithmeticLevel := by
    rw [arithmeticLevel_mem_iff]
    intro j
    fin_cases j
    · simpa [W,N,integralPlaneNormalize,integralSwap23,GeneralLinearGroup.coe_mul,
        Matrix.mul_apply,Fin.sum_univ_three,Int.cast_add,Int.cast_mul,add_comm,a,b,c] using first_zero
    · simpa [W,N,integralPlaneNormalize,integralSwap23,GeneralLinearGroup.coe_mul,
        Matrix.mul_apply,Fin.sum_univ_three,Int.cast_add,Int.cast_mul,add_comm,a,b,c] using third_zero
    · simpa [W,N,integralPlaneNormalize,integralSwap23,GeneralLinearGroup.coe_mul,
        Matrix.mul_apply,Fin.sum_univ_three,Int.cast_add,Int.cast_mul,add_comm,a,b,c] using sign
  let transport : rationalLevel :=
    ⟨GeneralLinearGroup.map (Int.castRingHom ℚ) W,rationalLevel_mem_of_integral W level⟩
  have plane_mem : GeneralLinearGroup.map (Int.castRingHom ℚ) N ∈ parabolic .plane := by
    exact ⟨rfl,rfl⟩
  refine ⟨transport,?_⟩
  have product : transport.val*swapLastTwo =
      GeneralLinearGroup.map (Int.castRingHom ℚ) V * GeneralLinearGroup.map (Int.castRingHom ℚ) N := by
    change GeneralLinearGroup.map (Int.castRingHom ℚ) (V*N*integralSwap23)*swapLastTwo = _
    rw [map_mul,map_mul,integralSwap23_map,mul_assoc,swapLastTwo_square,mul_one]
  change QuotientGroup.mk _ = QuotientGroup.mk (transport.val*swapLastTwo)
  rw [product,QuotientGroup.mk_mul_of_mem _ plane_mem]

theorem integral_last_nonzero (V : IntegralGL3)
    (first : (V.val 2 0 : ZMod 3) = 0) (second : (V.val 2 1 : ZMod 3) = 0) :
    (V.val 2 2 : ZMod 3) ≠ 0 := by
  intro third
  let reduced := GeneralLinearGroup.map (Int.castRingHom (ZMod 3)) V
  have invertible := congrArg (fun m : Matrix (Fin 3) (Fin 3) (ZMod 3) => m 2 2) reduced.mul_inv
  change ∑ k, (V.val 2 k : ZMod 3)*(reduced⁻¹).val k 2 = 1 at invertible
  simp only [Fin.sum_univ_three,first,second,third,zero_mul,add_zero] at invertible
  exact zero_ne_one invertible

theorem integral_standard_orbit_of_first_two_zero (V : IntegralGL3)
    (first : (V.val 2 0 : ZMod 3) = 0) (second : (V.val 2 1 : ZMod 3) = 0) :
    ∃ transport : rationalLevel,
      (QuotientGroup.mk (GeneralLinearGroup.map (Int.castRingHom ℚ) V) : Edges) =
        transport.val • QuotientGroup.mk 1 := by
  obtain ⟨e,unit,sign⟩ := zmodThree_unit_sign (V.val 2 2 : ZMod 3) (integral_last_nonzero V first second)
  let D := integralLastSign e unit
  let W := V*D
  have level : W ∈ arithmeticLevel := by
    rw [arithmeticLevel_mem_iff]
    intro j
    fin_cases j
    · simp [W,D,integralLastSign,Matrix.mul_apply,Fin.sum_univ_three,first]
    · simp [W,D,integralLastSign,Matrix.mul_apply,Fin.sum_univ_three,second]
    · simpa [W,D,integralLastSign,Matrix.mul_apply,Fin.sum_univ_three] using sign
  let transport : rationalLevel :=
    ⟨GeneralLinearGroup.map (Int.castRingHom ℚ) W,rationalLevel_mem_of_integral W level⟩
  have borel_mem : GeneralLinearGroup.map (Int.castRingHom ℚ) D ∈ parabolic .plane ⊓ parabolic .line :=
    ⟨⟨rfl,rfl⟩,⟨rfl,rfl⟩⟩
  refine ⟨transport,?_⟩
  change QuotientGroup.mk _ = QuotientGroup.mk (transport.val*1)
  rw [mul_one]
  change QuotientGroup.mk _ = QuotientGroup.mk (GeneralLinearGroup.map (Int.castRingHom ℚ) (V*D))
  rw [map_mul,QuotientGroup.mk_mul_of_mem _ borel_mem]

theorem integral_flag_orbit_cases (V : IntegralGL3) :
    (∃ transport : rationalLevel,
      (QuotientGroup.mk (GeneralLinearGroup.map (Int.castRingHom ℚ) V) : Edges) =
        transport.val • QuotientGroup.mk 1) ∨
    (∃ transport : rationalLevel,
      (QuotientGroup.mk (GeneralLinearGroup.map (Int.castRingHom ℚ) V) : Flags .plane) =
        transport.val • QuotientGroup.mk swapLastTwo) := by
  by_cases second : (V.val 2 1 : ZMod 3) = 0
  · by_cases first : (V.val 2 0 : ZMod 3) = 0
    · exact Or.inl (integral_standard_orbit_of_first_two_zero V first second)
    · right
      let K := integralPair01 0 1 (-1) 0 (by norm_num)
      have nonzero : ((V*K).val 2 1 : ZMod 3) ≠ 0 := by
        simpa [K,integralPair01,Matrix.mul_apply,Fin.sum_univ_three] using first
      obtain ⟨transport,equal⟩ := integral_plane_orbit_of_second_nonzero (V*K) nonzero
      have plane_mem : GeneralLinearGroup.map (Int.castRingHom ℚ) K ∈ parabolic .plane := ⟨rfl,rfl⟩
      rw [map_mul,QuotientGroup.mk_mul_of_mem _ plane_mem] at equal
      exact ⟨transport,equal⟩
  · exact Or.inr (integral_plane_orbit_of_second_nonzero V second)

theorem rational_flag_orbit_cases (edge : Edges) :
    (∃ transport : rationalLevel, edge = transport.val • QuotientGroup.mk 1) ∨
    (∃ transport : rationalLevel,
      endpoint .plane edge = transport.val • QuotientGroup.mk swapLastTwo) := by
  induction edge using Quotient.inductionOn with
  | h g =>
    obtain ⟨V,equal⟩ := rational_flag_integral_representative g
    change (∃ transport : rationalLevel, (QuotientGroup.mk g : Edges) = transport.val • QuotientGroup.mk 1) ∨
      (∃ transport : rationalLevel, endpoint .plane (QuotientGroup.mk g) = transport.val • QuotientGroup.mk swapLastTwo)
    rw [← equal]
    exact integral_flag_orbit_cases V

end TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers
