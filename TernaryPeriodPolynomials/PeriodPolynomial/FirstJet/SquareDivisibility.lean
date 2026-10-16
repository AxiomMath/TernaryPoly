module

public import TernaryPeriodPolynomials.PeriodPolynomial.FirstJet.Basic
public import TernaryPeriodPolynomials.Polynomial.Divisibility
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity

@[expose] public section


open MvPolynomial

noncomputable section

namespace TernaryPoly

local notation "BP" => MvPolynomial (Fin 2) ℚ

/-- Specialization to the coordinate-sum plane. -/
def coordinateSumPlane : TernaryPolynomial →ₐ[ℚ] TernaryPolynomial :=
  bind₁ ![X 0, X 1, -X 0-X 1]

private theorem coordinateSumPlane_sum :
    coordinateSumPlane (X 0+X 1+X 2) = 0 := by
  simp [coordinateSumPlane]

private theorem binaryBoundary_sum :
    binaryBoundary (X 0+X 1+X 2) = 0 := by
  simp [binaryBoundary]

/-- The binary boundary chart covers the whole coordinate-sum plane. -/
theorem coordinateSumPlane_zero_of_binaryBoundary_zero {g : TernaryPolynomial}
    (hg : binaryBoundary g = 0) : coordinateSumPlane g = 0 := by
  have h := congrArg (bind₁ (![X 1,-X 0] : Fin 2 → TernaryPolynomial)) hg
  have he : bind₁ (![X 1,-X 0] : Fin 2 → TernaryPolynomial) (binaryBoundary g) =
      coordinateSumPlane g := by
    simp only [binaryBoundary, coordinateSumPlane, bind₁_bind₁]
    congr 2
    funext i
    fin_cases i <;> simp
  rw [he, map_zero] at h
  exact h

/-- Vanishing on the coordinate-sum plane supplies its defining factor. -/
theorem coordinateSum_dvd_of_plane_zero {g : TernaryPolynomial}
    (hg : coordinateSumPlane g = 0) : (X 0+X 1+X 2) ∣ g := by
  have hv : Function.update (X : Fin 3 → TernaryPolynomial) 2 (-X 0-X 1) =
      ![X 0,X 1,-X 0-X 1] := by
    funext i
    fin_cases i <;> simp
  have h := linear_factor_dvd_of_substitution_zero g 2 (-X 0-X 1)
    (by simpa only [hv, coordinateSumPlane] using hg)
  convert h using 1
  ring

/-- Vanishing of a polynomial and a transverse first derivative gives a square factor. -/
theorem coordinateSum_sq_dvd_of_plane_zero {g : TernaryPolynomial}
    (hg : coordinateSumPlane g = 0) (hd : coordinateSumPlane (pderiv 2 g) = 0) :
    (X 0+X 1+X 2)^2 ∣ g := by
  obtain ⟨r, hr⟩ := coordinateSum_dvd_of_plane_zero hg
  have hrzero : coordinateSumPlane r = 0 := by
    rw [hr] at hd
    rw [pderiv_mul] at hd
    have hw : pderiv 2 (X 0+X 1+X 2 : TernaryPolynomial) = 1 := by simp
    rw [hw, map_add, map_mul, map_mul, map_one, coordinateSumPlane_sum,
      one_mul, zero_mul, add_zero] at hd
    exact hd
  obtain ⟨s, hs⟩ := coordinateSum_dvd_of_plane_zero hrzero
  refine ⟨s, ?_⟩
  rw [hr, hs, pow_two, mul_assoc]

private theorem binaryBoundary_C (g : TernaryPolynomial) :
    binaryBoundary (C g) =
      bind₁ (![X 1-X 0,-X 0] : Fin 2 → BP) (binaryBoundary g) := by
  simp only [binaryBoundary, C, bind₁_bind₁]
  congr 2
  funext i
  fin_cases i <;> simp
  ring

private theorem cyclic_partial0 (f : TernaryPolynomial) :
    pderiv 1 (C f) = C (pderiv 0 f) := by
  apply pderiv_bind₁_coordinate _ 1 0 _ f
  intro k
  fin_cases k <;> simp

private theorem cyclic_partial1 (f : TernaryPolynomial) :
    pderiv 2 (C f) = C (pderiv 1 f) := by
  apply pderiv_bind₁_coordinate _ 2 1 _ f
  intro k
  fin_cases k <;> simp

private theorem cyclic_partial2 (f : TernaryPolynomial) :
    pderiv 0 (C f) = C (pderiv 2 f) := by
  apply pderiv_bind₁_coordinate _ 0 2 _ f
  intro k
  fin_cases k <;> simp

private theorem cyclic_partials {f : TernaryPolynomial} (hc : C f = f) :
    C (pderiv 0 f) = pderiv 1 f ∧
      C (pderiv 1 f) = pderiv 2 f ∧ C (pderiv 2 f) = pderiv 0 f := by
  have h0 := cyclic_partial0 f
  have h1 := cyclic_partial1 f
  have h2 := cyclic_partial2 f
  rw [hc] at h0 h1 h2
  exact ⟨h0.symm,h1.symm,h2.symm⟩

private theorem zero_of_pair_sums (a b c : BP)
    (hab : a+b=0) (hbc : b+c=0) (hca : c+a=0) : a=0 ∧ b=0 ∧ c=0 := by
  have ha : a=0 := by
    apply add_self_eq_zero.mp
    calc
      a+a = (a+b)+(c+a)-(b+c) := by abel
      _ = 0 := by rw [hab,hbc,hca]; simp
  have hb : b=0 := by simpa only [ha,zero_add] using hab
  exact ⟨ha,hb,by simpa only [hb,zero_add] using hbc⟩

private theorem binaryBoundary_pair_zero_of_primitive_zero {f : TernaryPolynomial}
    (hp : binaryFirstJetPrimitive f = 0) :
    binaryBoundary (pderiv 0 f+pderiv 1 f) = 0 := by
  have h := congrArg (pderiv (0 : Fin 2)) hp
  simpa only [binaryFirstJetPrimitive, map_neg, pderiv_zero_binaryIntegral,
    map_zero, neg_eq_zero] using h

private theorem binaryBoundary_add (g h : TernaryPolynomial) :
    binaryBoundary (g+h) = binaryBoundary g+binaryBoundary h := map_add _ _ _

private theorem binaryBoundary_pair_rotate (g h g' h' : TernaryPolynomial)
    (hg : C g=g') (hh : C h=h') (hz : binaryBoundary (g+h)=0) :
    binaryBoundary (g'+h')=0 := by
  have h := binaryBoundary_C (g+h)
  rw [map_add, hg, hh, hz, map_zero] at h
  exact h

/-- A zero normalized primitive kills every boundary partial of a cyclic polynomial. -/
theorem binaryBoundary_partials_zero_of_primitive_zero {f : TernaryPolynomial}
    (hc : C f = f) (hp : binaryFirstJetPrimitive f = 0) :
    ∀ i : Fin 3, binaryBoundary (pderiv i f) = 0 := by
  have h01 := binaryBoundary_pair_zero_of_primitive_zero hp
  obtain ⟨hc0,hc1,hc2⟩ := cyclic_partials hc
  have h12 := binaryBoundary_pair_rotate _ _ _ _ hc0 hc1 h01
  have h20 := binaryBoundary_pair_rotate _ _ _ _ hc1 hc2 h12
  simp only [binaryBoundary_add] at h01 h12 h20
  obtain ⟨hz0,hz1,hz2⟩ := zero_of_pair_sums _ _ _ h01 h12 h20
  exact Fin.cases hz0 (Fin.cases hz1 (Fin.cases hz2 (fun i => Fin.elim0 i)))

/-- Positive homogeneity and cyclicity turn a zero first-jet primitive into a double plane factor. -/
theorem coordinateSum_sq_dvd_of_binaryFirstJetPrimitive_eq_zero
    {f : TernaryPolynomial} {n : ℕ} (hf : f.IsHomogeneous n) (hn : 0 < n)
    (hc : C f = f) (hp : binaryFirstJetPrimitive f = 0) :
    (X 0+X 1+X 2)^2 ∣ f := by
  have hpartials := binaryBoundary_partials_zero_of_primitive_zero hc hp
  have hboundary : binaryBoundary f = 0 := by
    apply (nsmul_eq_zero_iff_right (Nat.ne_of_gt hn)).mp
    have he := congrArg (bind₁ (![-X 1,X 0,X 1-X 0] : Fin 3 → BP))
      hf.sum_X_mul_pderiv
    have h0 : bind₁ ![-X 1,X 0,X 1-X 0] (pderiv 0 f) = (0 : BP) := hpartials 0
    have h1 : bind₁ ![-X 1,X 0,X 1-X 0] (pderiv 1 f) = (0 : BP) := hpartials 1
    have h2 : bind₁ ![-X 1,X 0,X 1-X 0] (pderiv 2 f) = (0 : BP) := hpartials 2
    simpa only [binaryBoundary, Fin.sum_univ_three, Nat.cast_smul_eq_nsmul, map_add, map_mul, map_nsmul,
      h0,h1,h2,mul_zero,zero_add] using he.symm
  exact coordinateSum_sq_dvd_of_plane_zero
    (coordinateSumPlane_zero_of_binaryBoundary_zero hboundary)
    (coordinateSumPlane_zero_of_binaryBoundary_zero (hpartials 2))

/-- A double coordinate-sum factor annihilates every first derivative on the boundary. -/
theorem binaryBoundary_partials_zero_of_coordinateSum_sq_dvd
    {f : TernaryPolynomial} (hf : (X 0+X 1+X 2)^2 ∣ f) :
    ∀ i : Fin 3, binaryBoundary (pderiv i f) = 0 := by
  obtain ⟨g,hg⟩ := hf
  intro i
  rw [hg, pow_two]
  change bind₁ (![-X 1,X 0,X 1-X 0] : Fin 3 → BP)
    (pderiv i (((X 0+X 1+X 2) * (X 0+X 1+X 2)) * g)) = 0
  have hw : bind₁ (![-X 1,X 0,X 1-X 0] : Fin 3 → BP) (X 0+X 1+X 2) = 0 :=
    binaryBoundary_sum
  simp only [pderiv_mul, map_add, map_mul] at hw ⊢
  simp only [hw, mul_zero, zero_mul, add_zero]

/-- A double coordinate-sum factor has zero normalized first-jet primitive, without symmetry assumptions. -/
theorem binaryFirstJetPrimitive_eq_zero_of_coordinateSum_sq_dvd
    {f : TernaryPolynomial} (hf : (X 0+X 1+X 2)^2 ∣ f) :
    binaryFirstJetPrimitive f = 0 := by
  have h := binaryBoundary_partials_zero_of_coordinateSum_sq_dvd hf
  have hb : binaryBoundary (pderiv 0 f+pderiv 1 f) = 0 := by
    change bind₁ (![-X 1,X 0,X 1-X 0] : Fin 3 → BP) (pderiv 0 f+pderiv 1 f) = 0
    rw [map_add, show bind₁ ![-X 1,X 0,X 1-X 0] (pderiv 0 f) = (0 : BP) from h 0,
      show bind₁ ![-X 1,X 0,X 1-X 0] (pderiv 1 f) = (0 : BP) from h 1, add_zero]
  simp only [binaryFirstJetPrimitive, hb, map_zero, neg_zero]

/-- The first-jet primitive detects exactly the double coordinate-sum factor in positive cyclic degree. -/
theorem binaryFirstJetPrimitive_eq_zero_iff_coordinateSum_sq_dvd
    {f : TernaryPolynomial} {n : ℕ} (hf : f.IsHomogeneous n) (hn : 0 < n)
    (hc : C f = f) :
    binaryFirstJetPrimitive f = 0 ↔ (X 0+X 1+X 2)^2 ∣ f :=
  ⟨coordinateSum_sq_dvd_of_binaryFirstJetPrimitive_eq_zero hf hn hc,
    binaryFirstJetPrimitive_eq_zero_of_coordinateSum_sq_dvd⟩

end TernaryPoly
