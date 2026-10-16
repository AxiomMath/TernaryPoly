module

public import TernaryPeriodPolynomials.Polynomial.CharTwo.HigherMultiplicity
public import TernaryPeriodPolynomials.Topology.HomogeneousQuotient

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.CharTwoNorm
open CharTwoProjector (sub Symmetric)

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

private theorem sub_mul (f g x y z : Poly) :
    sub (f*g) x y z = sub f x y z * sub g x y z := map_mul (bind₁ ![x,y,z]) f g

theorem symmetric_mul {f g : Poly} (hf : Symmetric f) (hg : Symmetric g) :
    Symmetric (f*g) := by
  constructor
  · simp only [sub_mul, hf.cyclic, hg.cyclic]
  · simp only [sub_mul, hf.swap, hg.swap]

private theorem symmetric_pow {f : Poly} (hf : Symmetric f) (n : ℕ) :
    Symmetric (f^n) := by
  constructor
  · simpa only [sub, map_pow] using congrArg (fun p => p^n) hf.cyclic
  · simpa only [sub, map_pow] using congrArg (fun p => p^n) hf.swap

private theorem symmetric_quotient {f g : Poly} (hf : Symmetric f) (hf0 : f ≠ 0)
    (hfg : Symmetric (f*g)) : Symmetric g := by
  constructor
  · apply mul_left_cancel₀ hf0
    simpa only [sub_mul, hf.cyclic] using hfg.cyclic
  · apply mul_left_cancel₀ hf0
    simpa only [sub_mul, hf.swap] using hfg.swap

theorem a_symmetric : Symmetric a := by
  apply CharTwoProjector.symmetric_of_isSymmetric
  intro σ
  exact (rename_elementary σ).1

private theorem c_symmetric : Symmetric c := by
  apply CharTwoProjector.symmetric_of_isSymmetric
  intro σ
  exact (rename_elementary σ).2.2

theorem cplus_symmetric : Symmetric cplus := by
  apply CharTwoProjector.symmetric_of_isSymmetric
  intro σ
  obtain ⟨ha,hb,hc⟩ := rename_elementary σ
  simp [cplus, ha, hb, hc]

theorem a_homogeneous : a.IsHomogeneous 1 :=
  ((isHomogeneous_X (ZMod 2) 0).add (isHomogeneous_X (ZMod 2) 1)).add
    (isHomogeneous_X (ZMod 2) 2)

private theorem c_homogeneous : c.IsHomogeneous 3 :=
  ((isHomogeneous_X (ZMod 2) 0).mul (isHomogeneous_X (ZMod 2) 1)).mul
    (isHomogeneous_X (ZMod 2) 2)

theorem cplus_homogeneous : cplus.IsHomogeneous 3 := by
  rw [cplus_eq_product]
  have h0 := isHomogeneous_X (ZMod 2) (0 : Fin 3)
  have h1 := isHomogeneous_X (ZMod 2) (1 : Fin 3)
  have h2 := isHomogeneous_X (ZMod 2) (2 : Fin 3)
  exact ((h0.add h1).mul (h0.add h2)).mul (h1.add h2)

private theorem d7_homogeneous : d7.IsHomogeneous 7 :=
  (a_homogeneous.mul c_homogeneous).mul cplus_homogeneous

theorem a_ne_zero : a ≠ 0 := by
  intro h
  have he := congrArg (eval (![1,0,0] : Fin 3 → ZMod 2)) h
  norm_num [a, Matrix.cons_val_two] at he

private theorem c_ne_zero : c ≠ 0 :=
  mul_ne_zero (mul_ne_zero (X_ne_zero (0 : Fin 3)) (X_ne_zero (1 : Fin 3)))
    (X_ne_zero (2 : Fin 3))

private theorem form02_ne_zero : (X 0+X 2 : Poly) ≠ 0 := by
  intro h
  have he := congrArg (eval (![1,0,0] : Fin 3 → ZMod 2)) h
  norm_num [Matrix.cons_val_two] at he

private theorem cplus_boundary_ne_zero : sub cplus (X 0) 0 (X 2) ≠ 0 := by
  simpa [cplus, a, b, c, sub] using
    mul_ne_zero form02_ne_zero (mul_ne_zero (X_ne_zero (0 : Fin 3)) (X_ne_zero (2 : Fin 3)))

theorem cplus_ne_zero : cplus ≠ 0 := by
  intro h
  apply cplus_boundary_ne_zero
  simp [h, sub]

private theorem d7_ne_zero : d7 ≠ 0 :=
  mul_ne_zero (mul_ne_zero a_ne_zero c_ne_zero) cplus_ne_zero

/-- The seventh Dickson invariant cancels from the actual norm-zero equation. -/
theorem norm_d7_mul_zero_iff (f : Poly) : norm (d7*f) = 0 ↔ norm f = 0 := by
  have h1 : sub₁ d7 = d7 := by simpa [invariant] using sub₁_invariant (2 : Fin 3)
  have h2 : sub₂ d7 = d7 := by simpa [invariant] using sub₂_invariant (2 : Fin 3)
  rw [norm_mul_of_fixed _ _ h1 h2, mul_eq_zero]
  simp only [d7_ne_zero, false_or]

/-- Multiplication by the source factor preserves symmetry. -/
theorem multiplier_source_symmetric {H : Poly} (hH : Symmetric H) :
    Symmetric ((a^3*cplus^2)*H) :=
  symmetric_mul (symmetric_mul (symmetric_pow a_symmetric 3)
    (symmetric_pow cplus_symmetric 2)) hH

/-- The source factor has degree nine. -/
theorem multiplier_source_homogeneous {H : Poly} {n : ℕ} (hH : H.IsHomogeneous n) :
    ((a^3*cplus^2)*H).IsHomogeneous (9+n) := by
  exact ((a_homogeneous.pow 3).mul (cplus_homogeneous.pow 2)).mul hH

/-- The odd multiplicity theorem forces the three coordinate factors in every even source. -/
theorem c_dvd_of_even_multiplier_norm_zero {H : Poly} {n : ℕ}
    (hH : H.IsHomogeneous n) (heven : Even n) (hs : Symmetric H)
    (hn : norm ((a^3*cplus^2)*H) = 0) : c ∣ H := by
  have hodd : Odd (9+n) := (by decide : Odd (9 : ℕ)).add_even heven
  have hc := c_dvd_of_odd_cplus_square (multiplier_source_homogeneous hH) hodd
    (multiplier_source_symmetric hs) hn
    (by exact ⟨a^3*H, by ring⟩)
  obtain ⟨g,hg⟩ := hc
  have h := congrArg (fun p => sub p (X 0) 0 (X 2)) hg
  rw [sub_mul (a^3*cplus^2) H, sub_mul c g] at h
  have hc0 : sub c (X 0) 0 (X 2) = 0 := by simp [c, sub]
  rw [hc0, zero_mul] at h
  have hm : sub (a^3*cplus^2) (X 0) 0 (X 2) ≠ 0 := by
    rw [sub_mul]
    simpa only [sub, map_pow] using
      mul_ne_zero (pow_ne_zero 3 (show sub a (X 0) 0 (X 2) ≠ 0 by
        simpa [a, sub] using form02_ne_zero)) (pow_ne_zero 2 cplus_boundary_ne_zero)
  exact c_dvd_of_middleBoundary_zero hs ((mul_eq_zero.mp h).resolve_left hm)

/-- After the coordinate factors are removed, the invariant quotient has zero norm. -/
theorem norm_after_coordinate_factor {H J : Poly}
    (hn : norm ((a^3*cplus^2)*H) = 0) (hJ : H = c*J) :
    norm ((a^2*cplus)*J) = 0 := by
  apply (norm_d7_mul_zero_iff _).mp
  convert hn using 1
  rw [hJ, d7]
  congr 1
  ring

private theorem homogeneous_after_coordinate_factor {H J : Poly} {n : ℕ}
    (hH : H.IsHomogeneous n) (hJ : H = c*J) :
    ((a^2*cplus)*J).IsHomogeneous (n+2) := by
  have he : d7*((a^2*cplus)*J) = (a^3*cplus^2)*H := by
    rw [hJ, d7]
    ring
  have hp : (d7*((a^2*cplus)*J)).IsHomogeneous (9+n) := by
    rw [he]
    exact multiplier_source_homogeneous hH
  have h := isHomogeneous_quotient d7_homogeneous d7_ne_zero hp
  convert h using 1
  omega

private theorem cplus_dvd_of_square_dvd {J : Poly} (hs : Symmetric J)
    (hd : cplus^2 ∣ (a^2*cplus)*J) : cplus ∣ J := by
  obtain ⟨r,hr⟩ := hd
  have he : a^2*J = cplus*r := by
    apply mul_left_cancel₀ cplus_ne_zero
    calc
      cplus*(a^2*J) = (a^2*cplus)*J := by ring
      _ = cplus^2*r := hr
      _ = cplus*(cplus*r) := by ring
  have h := congrArg (fun p => sub p (X 0) (X 0) (X 2)) he
  rw [sub_mul, sub_mul] at h
  have hc0 : sub cplus (X 0) (X 0) (X 2) = 0 := by
    simp [cplus_eq_product, sub, CharTwo.add_self_eq_zero]
  have ha : sub (a^2) (X 0) (X 0) (X 2) = (X 2)^2 := by
    simp [a, sub, CharTwo.add_self_eq_zero]
  rw [hc0, ha, zero_mul] at h
  exact cplus_dvd_of_symmetric_diagonal_zero hs
    ((mul_eq_zero.mp h).resolve_left (pow_ne_zero 2 (X_ne_zero (2 : Fin 3))))

/-- Removing precisely the invariant `d7` gives the reduced norm equation, in both directions. -/
theorem multiplier_factored_norm_zero_iff (K : Poly) :
    norm ((a^3*cplus^2)*(c*cplus*K)) = 0 ↔ norm ((a*cplus)^2*K) = 0 := by
  have he : (a^3*cplus^2)*(c*cplus*K) = d7*((a*cplus)^2*K) := by
    rw [d7]
    ring
  rw [he, norm_d7_mul_zero_iff]

/-- Every even homogeneous symmetric source in the multiplier norm kernel factors by `c*cplus`. -/
theorem exists_factored_even_multiplier {H : Poly} {n : ℕ}
    (hH : H.IsHomogeneous n) (heven : Even n) (hs : Symmetric H)
    (hn : norm ((a^3*cplus^2)*H) = 0) :
    ∃ K : Poly, H = c*cplus*K ∧ K.IsHomogeneous (n-6) ∧ Symmetric K ∧
      norm ((a*cplus)^2*K) = 0 := by
  obtain ⟨J,hJ⟩ := c_dvd_of_even_multiplier_norm_zero hH heven hs hn
  have hJs : Symmetric J := symmetric_quotient c_symmetric c_ne_zero (hJ ▸ hs)
  have hQn := norm_after_coordinate_factor hn hJ
  have hQh := homogeneous_after_coordinate_factor hH hJ
  have hQeven : Even (n+2) := heven.add (by decide : Even (2 : ℕ))
  have hQs := symmetric_mul (symmetric_mul (symmetric_pow a_symmetric 2) cplus_symmetric) hJs
  have hQa : a^2 ∣ (a^2*cplus)*J := ⟨cplus*J, by ring⟩
  have hC := cplus_square_dvd_of_even_a_square hQh hQeven hQs hQn hQa
  obtain ⟨K,hK⟩ := cplus_dvd_of_square_dvd hJs hC
  have hHK : H = c*cplus*K := by rw [hJ,hK,mul_assoc]
  refine ⟨K,hHK,?_,?_,?_⟩
  · exact isHomogeneous_quotient (c_homogeneous.mul cplus_homogeneous)
      (mul_ne_zero c_ne_zero cplus_ne_zero) (hHK ▸ hH)
  · exact symmetric_quotient cplus_symmetric cplus_ne_zero (hK ▸ hJs)
  · exact (multiplier_factored_norm_zero_iff K).mp (by simpa only [hHK] using hn)

end TernaryPoly.CharTwoNorm
