module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Kostant.BridgeCochain

@[expose] public section


/-!
# The Kostant identity of the level-one bridge at the good line

For `U`-equivariant homogeneous one-cocycles `f` (coefficients `ρ_χ`) and `g` (coefficients
`ρ_χ ∘ φ`) the fiber-integration pairing `κ(f, g) = ⟨f ⌣ g, σ⟩` is computed in the coordinates
`PhiTotal`, `PsiTotal` (`kostant_eq_binaryPairing`):

  `κ(f, g) = −(n+1)! · binaryPairing (n+1) (Φ f) (Ψ g)`.

The proof compares the cup-product value with the adjoint Kostant form `kostantValue` of
`KostantGoodLine` for the inversion `w = g(1, u(·)⁻¹)` of the dual cocycle: both are bilinear in the
class of the line cocycle, they agree on the cocycles with values in the invariants (where the
adjointness of `dualPairing` for the good-line and the identity-plane radicals turns one into the
negative of the other) and both vanish on coboundaries.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial
open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.SphericalDetection.Helpers

attribute [local instance] TernaryPeriodPolynomials.SphericalDetection.Helpers.complexEndRationalAlgebra

namespace TernaryPeriodPolynomials.BoundaryDuality.Kostant

open TernaryPeriodPolynomials.BoundaryDuality.L2Assembly (latL1)
open TernaryPeriodPolynomials.BoundaryDuality.FiberKostant (UCocycle)
open TernaryPeriodPolynomials.BoundaryDuality.FiberFormula (kostant)
open TernaryPeriodPolynomials.BoundaryDuality.FiberL1 (dualRep)
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives (dualityData)

/-! ### Vectors fixed by the good-line radical -/

theorem lowerRho_first_fixed (n : ℕ) (P : HomogeneousPoly n) (hP : pderiv 2 P.val = 0) :
    rhoLow n radicalLatticeFirst P = P := by
  have h := (nilpotent_difference_kernel (lowerRadicalGenerator n 0) n
    (lowerRadicalGenerator_power_zero n 0) P).mpr
    (lowerRadicalGenerator_of_pderiv_third_zero n 0 P hP)
  have e : rhoLow n radicalLatticeFirst = IsNilpotent.exp (lowerRadicalGenerator n 0) :=
    lowerRadicalLatticeRep_first n
  have h' : (IsNilpotent.exp (lowerRadicalGenerator n 0)) P - P = 0 := by
    let _ : Algebra ℚ (Module.End ℂ (HomogeneousPoly n)) := complexEndRationalAlgebra
    rw [exp_inst_irrel _ Algebra.toModule]
    exact h
  rw [e]
  exact sub_eq_zero.mp h'

theorem lowerRho_second_fixed (n : ℕ) (P : HomogeneousPoly n) (hP : pderiv 2 P.val = 0) :
    rhoLow n radicalLatticeSecond P = P := by
  have h := (nilpotent_difference_kernel (lowerRadicalGenerator n 1) n
    (lowerRadicalGenerator_power_zero n 1) P).mpr
    (lowerRadicalGenerator_of_pderiv_third_zero n 1 P hP)
  have e : rhoLow n radicalLatticeSecond = IsNilpotent.exp (lowerRadicalGenerator n 1) :=
    lowerRadicalLatticeRep_second n
  have h' : (IsNilpotent.exp (lowerRadicalGenerator n 1)) P - P = 0 := by
    let _ : Algebra ℚ (Module.End ℂ (HomogeneousPoly n)) := complexEndRationalAlgebra
    rw [exp_inst_irrel _ Algebra.toModule]
    exact h
  rw [e]
  exact sub_eq_zero.mp h'

/-- **Decomposition of a good-line cocycle** into a cocycle with values in the invariants and a
coboundary, on the two generators. -/
theorem lower_decomp (n : ℕ) (positive : 0 < n)
    (z : groupCohomology.cocycles₁ (lowerRadicalLatticeRep n)) :
    ∃ (P Q : HomogeneousPoly n), pderiv 2 P.val = 0 ∧ pderiv 2 Q.val = 0 ∧
      ∃ v : HomogeneousPoly n,
        (z radicalLatticeFirst : HomogeneousPoly n) = P + (rhoLow n radicalLatticeFirst v - v) ∧
          (z radicalLatticeSecond : HomogeneousPoly n) =
            Q + (rhoLow n radicalLatticeSecond v - v) := by
  obtain ⟨P, Q, hP, hQ, hPQ⟩ := exists_invariant_pair (lowerRadicalCocycleCoordinate n z)
  have hcoord : lowerRadicalCocycleCoordinate n (specialCocycle n P Q hP hQ) =
      lowerRadicalCocycleCoordinate n z := by
    apply Subtype.ext
    apply binaryPolynomialLift_injective
    rw [lift_lowerCoordinate_special n P Q hP hQ, hPQ]
    rfl
  obtain ⟨s, hs1, hs2, hsc⟩ : ∃ s : groupCohomology.cocycles₁ (lowerRadicalLatticeRep n),
      s radicalLatticeFirst = P ∧ s radicalLatticeSecond = Q ∧
        lowerRadicalCocycleCoordinate n s = lowerRadicalCocycleCoordinate n z :=
    ⟨specialCocycle n P Q hP hQ, specialCocycle_first n P Q hP hQ,
      specialCocycle_second n P Q hP hQ, hcoord⟩
  have hzero : lowerRadicalCocycleCoordinate n (z - s) = 0 := by
    rw [map_sub, hsc, sub_self]
  have hH1 := (lowerRadicalCocycleCoordinate_zero_iff positive (z - s)).mp hzero
  obtain ⟨potential, hfirst, hsecond⟩ :=
    (oneCocycle_H1_zero_iff_generator_boundaries (lowerRadicalLatticeRep n) (z - s)
      radicalLatticeFirst radicalLatticeSecond radicalLattice_generated).mp hH1
  have h1 : z radicalLatticeFirst = s radicalLatticeFirst +
      (((lowerRadicalLatticeRep n).ρ radicalLatticeFirst) potential - potential) := by
    have h := hfirst
    change z radicalLatticeFirst - s radicalLatticeFirst = _ at h
    exact sub_eq_iff_eq_add'.mp h
  have h2 : z radicalLatticeSecond = s radicalLatticeSecond +
      (((lowerRadicalLatticeRep n).ρ radicalLatticeSecond) potential - potential) := by
    have h := hsecond
    change z radicalLatticeSecond - s radicalLatticeSecond = _ at h
    exact sub_eq_iff_eq_add'.mp h
  refine ⟨s radicalLatticeFirst, s radicalLatticeSecond, ?_, ?_, potential, h1, h2⟩
  · exact (congrArg (fun x : HomogeneousPoly n => (pderiv 2) x.val) hs1).trans hP
  · exact (congrArg (fun x : HomogeneousPoly n => (pderiv 2) x.val) hs2).trans hQ

/-- **The adjoint Kostant form only depends on the invariant part of the line cocycle.** -/
theorem kostantValue_decomp (n : ℕ)
    (z : groupCohomology.cocycles₁ (lowerRadicalLatticeRep n))
    (w : groupCohomology.cocycles₁ (upperRadicalLatticeRep n)) (P Q v : HomogeneousPoly n)
    (hz1 : (z radicalLatticeFirst : HomogeneousPoly n) =
      P + (rhoLow n radicalLatticeFirst v - v))
    (hz2 : (z radicalLatticeSecond : HomogeneousPoly n) =
      Q + (rhoLow n radicalLatticeSecond v - v)) :
    kostantValue (dualPairing n) (z radicalLatticeFirst) (z radicalLatticeSecond)
        (w radicalLatticeFirst) (w radicalLatticeSecond) =
      kostantValue (dualPairing n) P Q (w radicalLatticeFirst) (w radicalLatticeSecond) := by
  have hw := oneCocycle_generator_closed (upperRadicalLatticeRep n) w radicalLatticeFirst
    radicalLatticeSecond (Commute.all _ _)
  have hwc : rhoUp n radicalLatticeFirst (wv n w radicalLatticeSecond) -
      wv n w radicalLatticeSecond =
      rhoUp n radicalLatticeSecond (wv n w radicalLatticeFirst) - wv n w radicalLatticeFirst := hw
  have hbd : kostantValue (dualPairing n)
      (rhoLow n radicalLatticeFirst v - v) (rhoLow n radicalLatticeSecond v - v)
      (w radicalLatticeFirst) (w radicalLatticeSecond) = 0 :=
    kostantValue_boundary_left (lowerRadicalLatticeRep n).ρ (upperRadicalLatticeRep n).ρ
      (dualPairing n) radicalLatticeFirst radicalLatticeSecond
      (isAdjointAt_lower_upper n radicalLatticeFirst)
      (isAdjointAt_lower_upper n radicalLatticeSecond) v _ _ hwc
  have h2 := congrArg₂ (fun x y => kostantValue (dualPairing n) x y (w radicalLatticeFirst)
    (w radicalLatticeSecond)) hz1 hz2
  have h1 := kostantValue_add_left (dualPairing n) P Q (rhoLow n radicalLatticeFirst v - v)
    (rhoLow n radicalLatticeSecond v - v) (w radicalLatticeFirst) (w radicalLatticeSecond)
  exact h2.trans (h1.trans ((congrArg (fun t => kostantValue (dualPairing n) P Q
    (w radicalLatticeFirst) (w radicalLatticeSecond) + t) hbd).trans (add_zero _)))

/-! ### The core algebra -/

/-- The invariance of `dualPairing` in the lattice form: the good-line radical element `p` is
paired with the inverse of the identity-plane radical element `p`. -/
theorem dual_inv_lattice (n : ℕ) (p : RadicalLattice) (v w : HomogeneousPoly n) :
    dualPairing n (rhoLow n p v) (rhoUp n p⁻¹ w) = dualPairing n v w := by
  have h := dualPairing_invariant n trivialCharacter (lowerRadicalLattice p) v w
  rw [rho_dual_lower_eq n trivialCharacter p] at h
  exact h

/-- **The algebra comparing the cup-product value with the adjoint Kostant form.** -/
theorem kappa_algebra (n : ℕ) (p1 p2 : RadicalLattice) (P Q v Wa Wb w1 w2 : HomogeneousPoly n)
    (hP1 : rhoLow n p1 P = P) (hP2 : rhoLow n p2 P = P)
    (hQ1 : rhoLow n p1 Q = Q) (hQ2 : rhoLow n p2 Q = Q)
    (hWa : Wa = -(rhoUp n p1⁻¹ w1))
    (hWb : Wb = -(rhoUp n p2⁻¹ w2))
    (hcl : rhoUp n p1⁻¹ Wb - Wb = rhoUp n p2⁻¹ Wa - Wa) :
    dualPairing n (P + (rhoLow n p1 v - v)) (rhoUp n p1⁻¹ Wb) -
        dualPairing n (Q + (rhoLow n p2 v - v)) (rhoUp n p2⁻¹ Wa) =
      -(dualPairing n P w2 - dualPairing n Q w1) := by
  have i1 := dual_inv_lattice n p1 v Wb
  have i2 := dual_inv_lattice n p2 v Wa
  have e1 := dual_inv_lattice n p1 P Wb
  rw [hP1] at e1
  have e2 := dual_inv_lattice n p2 Q Wa
  rw [hQ2] at e2
  have hp := dual_inv_lattice n p2 P w2
  rw [hP2] at hp
  have hq := dual_inv_lattice n p1 Q w1
  rw [hQ1] at hq
  have hP' : dualPairing n P Wb = -dualPairing n P w2 := by
    rw [hWb, map_neg, hp]
  have hQ' : dualPairing n Q Wa = -dualPairing n Q w1 := by
    rw [hWa, map_neg, hq]
  have hcl' : dualPairing n v (rhoUp n p1⁻¹ Wb) - dualPairing n v Wb =
      dualPairing n v (rhoUp n p2⁻¹ Wa) - dualPairing n v Wa := by
    have h := congrArg (dualPairing n v) hcl
    simpa only [map_sub] using h
  simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]
  linear_combination e1 + i1 - e2 - i2 + hP' - hQ' - hcl'

/-- The value of the dual cocycle on a radical element in terms of its inversion. -/
theorem g_value_eq_neg (n : ℕ) (χ : RankOneCharacter)
    {g : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hg : UCocycle (dualRep (dualityData n χ)) latL1.sub g) (p : RadicalLattice) :
    g ![1, lowerRadicalLattice p] = -(rhoUp n p⁻¹ (wCoc n χ hg p)) := by
  have h := uCocycle_law hg p p⁻¹
  rw [mul_inv_cancel, map_one, uCocycle_one hg] at h
  have e : dualRep (dualityData n χ) (lowerRadicalLattice p) = rhoUp n p⁻¹ :=
    rho_dual_lower_eq n χ p
  rw [e] at h
  exact eq_neg_of_add_eq_zero_right h.symm

/-- The closedness of the dual cocycle on two radical elements. -/
theorem g_closed (n : ℕ) (χ : RankOneCharacter)
    {g : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hg : UCocycle (dualRep (dualityData n χ)) latL1.sub g) (p q : RadicalLattice) :
    rhoUp n p⁻¹ (g ![1, lowerRadicalLattice q]) - g ![1, lowerRadicalLattice q] =
      rhoUp n q⁻¹ (g ![1, lowerRadicalLattice p]) - g ![1, lowerRadicalLattice p] := by
  have h1 := uCocycle_law hg p q
  have h2 := uCocycle_law hg q p
  rw [mul_comm q p] at h2
  have ep : dualRep (dualityData n χ) (lowerRadicalLattice p) = rhoUp n p⁻¹ :=
    rho_dual_lower_eq n χ p
  have eq' : dualRep (dualityData n χ) (lowerRadicalLattice q) = rhoUp n q⁻¹ :=
    rho_dual_lower_eq n χ q
  rw [ep] at h1
  rw [eq'] at h2
  exact sub_eq_sub_iff_add_eq_add.mpr (h1.symm.trans h2)

/-! ### The Kostant pairing in coordinates -/

/-- **The fiber-integration pairing is minus the adjoint Kostant form of the inverted dual
cocycle.** -/
theorem kostant_eq_neg_kostantValue (n : ℕ) (χ : RankOneCharacter) (positive : 0 < n)
    {f g : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hf : UCocycle (rationalCoefficientComponent n χ) latL1.sub f)
    (hg : UCocycle (dualRep (dualityData n χ)) latL1.sub g) :
    kostant (dualPairing n) latL1.σ f g =
      -kostantValue (dualPairing n) (zCoc n χ hf radicalLatticeFirst)
        (zCoc n χ hf radicalLatticeSecond) (wCoc n χ hg radicalLatticeFirst)
        (wCoc n χ hg radicalLatticeSecond) := by
  obtain ⟨P, Q, hP, hQ, v, hz1, hz2⟩ := lower_decomp n positive (zCoc n χ hf)
  have hz1' : f ![1, lowerRadicalLattice radicalLatticeFirst] =
      P + (rhoLow n radicalLatticeFirst v - v) := hz1
  have hz2' : f ![1, lowerRadicalLattice radicalLatticeSecond] =
      Q + (rhoLow n radicalLatticeSecond v - v) := hz2
  have key := kappa_algebra n radicalLatticeFirst radicalLatticeSecond P Q v
    (g ![1, lowerRadicalLattice radicalLatticeFirst])
    (g ![1, lowerRadicalLattice radicalLatticeSecond])
    (wCoc n χ hg radicalLatticeFirst) (wCoc n χ hg radicalLatticeSecond)
    (lowerRho_first_fixed n P hP) (lowerRho_second_fixed n P hP)
    (lowerRho_first_fixed n Q hQ) (lowerRho_second_fixed n Q hQ)
    (g_value_eq_neg n χ hg radicalLatticeFirst) (g_value_eq_neg n χ hg radicalLatticeSecond)
    (g_closed n χ hg radicalLatticeFirst radicalLatticeSecond)
  have hdec := kostantValue_decomp n (zCoc n χ hf) (wCoc n χ hg) P Q v hz1 hz2
  have hrw := congrArg₂ (fun x y => dualPairing n x (rhoUp n radicalLatticeFirst⁻¹
    (g ![1, lowerRadicalLattice radicalLatticeSecond])) -
      dualPairing n y (rhoUp n radicalLatticeSecond⁻¹
        (g ![1, lowerRadicalLattice radicalLatticeFirst]))) hz1' hz2'
  refine (kostant_generators n χ hf hg).trans (hrw.trans (key.trans ?_))
  exact congrArg Neg.neg ((rfl : dualPairing n P (wCoc n χ hg radicalLatticeSecond) -
    dualPairing n Q (wCoc n χ hg radicalLatticeFirst) =
      kostantValue (dualPairing n) P Q (wCoc n χ hg radicalLatticeFirst)
        (wCoc n χ hg radicalLatticeSecond)).trans hdec.symm)

/-- **The fiber-integration pairing is minus the apolar pairing of the coordinates.** -/
theorem kostant_eq_neg_binApolar (n : ℕ) (χ : RankOneCharacter) (positive : 0 < n)
    {f g : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hf : UCocycle (rationalCoefficientComponent n χ) latL1.sub f)
    (hg : UCocycle (dualRep (dualityData n χ)) latL1.sub g) :
    kostant (dualPairing n) latL1.σ f g = -binApolar (n + 1) (PhiTotal n f) (upperTotal n g) := by
  rw [kostant_eq_neg_kostantValue n χ positive hf hg,
    kostantValue_eq n positive (zCoc n χ hf) (wCoc n χ hg), PhiTotal_eq n χ hf,
    upperTotal_eq n χ hg]

/-- **The Kostant identity of the level-one bridge**:
`κ(f, g) = −(n+1)! · binaryPairing (n+1) (Φ f) (Ψ g)`. -/
theorem kostant_eq_binaryPairing (n : ℕ) (χ : RankOneCharacter) (positive : 0 < n)
    {f g : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hf : UCocycle (rationalCoefficientComponent n χ) latL1.sub f)
    (hg : UCocycle (dualRep (dualityData n χ)) latL1.sub g) :
    kostant (dualPairing n) latL1.σ f g =
      (-((n + 1).factorial : ℂ)) * BinaryPairing.binaryPairing (n + 1) (PhiTotal n f)
        (PsiTotal n g) := by
  rw [kostant_eq_neg_binApolar n χ positive hf hg, binApolar_eq_binaryPairing]
  change -(((n + 1).factorial : ℂ) * BinaryPairing.binaryPairing (n + 1) (PhiTotal n f)
    (PsiTotal n g)) = _
  ring

end TernaryPeriodPolynomials.BoundaryDuality.Kostant

end
