module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.LAEdge
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Good.LineCoordinate

@[expose] public section


/-!
# The binary coordinate of the twisted good-line edge under the local Hecke operator

The exponential form of lower-radical cocycles, the Levi and `σ`-equivariance of the exponentials
and the corestriction formula `cor_exp` of `GoodLineCoordinate` only involve the lower-radical
lattice (on which the twisted and untwisted coefficient systems agree).  For the sign-twisted
coefficients the three kinds of terms of `edgeL_heckeTwoL` become: the Levi terms `ℓ_j` (positive
determinant) are unchanged, the corestriction term is multiplied by `sgnP p` (the sign of
`τ_c`; the two Levi conjugations by `m` and `m⁻¹` contribute `det m * det m⁻¹ = 1`), and the
coboundary term is unchanged.  Consequently, if the edge cocycles are exponentials of closed pairs
`b μ`, the binary coordinate of the edge of the Hecke image at `m` is
`sgnP p • coord (b m) + ∑_j A(B_j) coord (b μ_j)` (`coordF_edge_heckeT`), with `A(B_j)` the twist-zero
action of `B_j`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open Matrix MvPolynomial GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace TernaryPeriodPolynomials.Twisted

open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.PlaneCoordinates
open TernaryPeriodPolynomials.Spectral.LevelOneCosets
open TernaryPeriodPolynomials.Spectral.IdentityPlaneCosets
open TernaryPeriodPolynomials.Spectral.LineCoordinates
open TernaryPeriodPolynomials.Spectral.GoodLineCosets
open TernaryPeriodPolynomials.Spectral.GoodLineEdge
open TernaryPeriodPolynomials.Spectral.IdentityPlaneCoordinate
open TernaryPeriodPolynomials.Spectral.GoodLineCoordinate

namespace LH

/-- The determinant of an arithmetic Levi element, as a complex number. -/
abbrev detC (m : GL (Fin 2) ℤ) : ℂ := (((GeneralLinearGroup.det m : ℤˣ) : ℤ) : ℂ)

theorem smul_cancel_aux {V : Type*} [AddCommGroup V] [Module ℂ V] (a b s : ℂ) (hab : a * b = 1)
    (w : V) : a • (s • (b • w)) = s • w := by
  rw [smul_comm a s, smul_smul a b w, hab, one_smul]

variable (n : ℕ) (χ : RankOneCharacter)

/-! ### The three kinds of terms -/

/-- The Levi terms are unchanged by the sign twist. -/
theorem leviT_term (p : Nat.Primes) (b : Fin 2 → HomogeneousPoly n) (j : Option (Fin p.val))
    (u : ℤ × ℤ) :
    rationalCoefficientComponent n χ (rExpl p (.inl j)) (Exp n b (ivmul u (Bint p j))) =
      Exp n (leviP n (cx2 (BGL p j)) b) u := by
  rw [rho_rExpl_inl]
  exact (rho_leviQ n (BGL p j) (Exp n b (ivmul u (Bint p j)))).trans
    (levi_exp n (cx2 (BGL p j)) (Bint p j) (cx2_BGL p j) b u)

/-- The Levi translate of an exponential, with the determinant of the translating element. -/
theorem conjT_exp (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (ν : GL (Fin 2) ℤ)
    (ξ : ℤ × ℤ → Aρ1 (rationalCoefficientComponent n χ)) (b : Fin 2 → HomogeneousPoly n)
    (hξ : ∀ y, @id (HomogeneousPoly n) (ξ y) = Exp n b y) (y : ℤ × ℤ) :
    @id (HomogeneousPoly n) (conjL (rationalCoefficientComponent n χ) ν ξ y) =
      detC ν • Exp n (leviP n (cx2 (integralEmbed ν)) b) y := by
  change rationalCoefficientComponent n χ (Qint 0 ν) (@id (HomogeneousPoly n) (ξ (ivmul y ν.val))) = _
  rw [hξ, rho_Qint_zero n χ hχ ν, LinearMap.smul_apply, Qint_zero ν, rho_leviQ,
    levi_exp n (cx2 (integralEmbed ν)) ν.val (cx2_integral ν)]

/-- **The radical term.**  The corestriction of the Levi translate of an exponential is `sgnP p` times
the untwisted expression. -/
theorem radT_term (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (p : Nat.Primes)
    (ξ : ℤ × ℤ → Aρ1 (rationalCoefficientComponent n χ)) (b : Fin 2 → HomogeneousPoly n)
    (hb : ClosedL n b) (hξ : ∀ y, @id (HomogeneousPoly n) (ξ y) = Exp n b y) (m : GL (Fin 2) ℤ) :
    ∃ T : HomogeneousPoly n, ∀ u : ℤ × ℤ,
      @id (HomogeneousPoly n) (R1 (rationalCoefficientComponent n χ) (Qint 0 m)
        (CorL p (rationalCoefficientComponent n χ)
          (conjL (rationalCoefficientComponent n χ) m⁻¹ ξ) (ivmul u m.val))) =
        ((IdentityPlaneLocalOp.sgnP p : ℤ) : ℂ) •
          (((p.val : ℂ) ^ 2) • Exp n (leviP n (cx2 (integralEmbed m))
              (sigmaP n (epsC p) (leviP n (cx2 (integralEmbed m⁻¹)) b))) u +
            (ρn n (lowerRadicalLattice (Multiplicative.ofAdd u)) T - T)) := by
  set b' := leviP n (cx2 (integralEmbed m⁻¹)) b
  have hb'c : ClosedL n b' := closedL_leviP n _ _ hb
  obtain ⟨S, hS⟩ := cor_exp n p b' hb'c
  refine ⟨ρn n (Qint 0 m) S, fun u => ?_⟩
  have hterm : ∀ (y : ℤ × ℤ) (c : Fin p.val × Fin p.val),
      rationalCoefficientComponent n χ (rExpl p (.inr c))
          (@id (HomogeneousPoly n) (conjL (rationalCoefficientComponent n χ) m⁻¹ ξ y)) =
        ((IdentityPlaneLocalOp.sgnP p : ℤ) : ℂ) •
          (detC m⁻¹ • ρn n (rExpl p (.inr c)) (Exp n b' y)) := by
    intro y c
    rw [conjT_exp n χ hχ m⁻¹ ξ b hξ y, map_smul, rho_rExpl_inr n χ hχ p c, LinearMap.smul_apply,
      smul_comm]
  have hcor : @id (HomogeneousPoly n) (CorL p (rationalCoefficientComponent n χ)
        (conjL (rationalCoefficientComponent n χ) m⁻¹ ξ) (ivmul u m.val)) =
      ((IdentityPlaneLocalOp.sgnP p : ℤ) : ℂ) • (detC m⁻¹ •
        @id (HomogeneousPoly n) (CorL p (ρn n) (Exp n b') (ivmul u m.val))) := by
    change ∑ c : Fin p.val × Fin p.val, rationalCoefficientComponent n χ (rExpl p (.inr c))
        (@id (HomogeneousPoly n) (conjL (rationalCoefficientComponent n χ) m⁻¹ ξ
          (-cq p (cvec p c - ivmul u m.val)))) =
      ((IdentityPlaneLocalOp.sgnP p : ℤ) : ℂ) • (detC m⁻¹ • ∑ c : Fin p.val × Fin p.val,
        ρn n (rExpl p (.inr c)) (Exp n b' (-cq p (cvec p c - ivmul u m.val))))
    rw [Finset.sum_congr rfl (fun c _ => hterm (-cq p (cvec p c - ivmul u m.val)) c), Finset.smul_sum,
      Finset.smul_sum]
  have hW : ρn n (Qint 0 m) (@id (HomogeneousPoly n) (CorL p (ρn n) (Exp n b') (ivmul u m.val))) =
      ((p.val : ℂ) ^ 2) • Exp n (leviP n (cx2 (integralEmbed m)) (sigmaP n (epsC p) b')) u +
        (ρn n (lowerRadicalLattice (Multiplicative.ofAdd u)) (ρn n (Qint 0 m) S) -
          ρn n (Qint 0 m) S) := by
    refine (congrArg (ρn n (Qint 0 m)) (hS (ivmul u m.val))).trans ?_
    rw [map_add, map_smul, map_sub, hcomm, Qint_zero, rho_leviQ,
      levi_exp n (cx2 (integralEmbed m)) m.val (cx2_integral m)]
  change rationalCoefficientComponent n χ (Qint 0 m) (@id (HomogeneousPoly n)
    (CorL p (rationalCoefficientComponent n χ)
      (conjL (rationalCoefficientComponent n χ) m⁻¹ ξ) (ivmul u m.val))) = _
  rw [rho_Qint_zero n χ hχ m, LinearMap.smul_apply, hcor, map_smul, map_smul, hW]
  exact smul_cancel_aux (V := HomogeneousPoly n) (detC m) (detC m⁻¹)
    ((IdentityPlaneLocalOp.sgnP p : ℤ) : ℂ) (det_mul_det_inv m) _

/-- The coboundary term is unchanged by the sign twist. -/
theorem cobT_term (Φ : Aρ1 (rationalCoefficientComponent n χ)) (u : ℤ × ℤ) :
    @id (HomogeneousPoly n) (R1 (rationalCoefficientComponent n χ) (Qint u 1) Φ - Φ) =
      ρn n (lowerRadicalLattice (Multiplicative.ofAdd u)) (@id (HomogeneousPoly n) Φ) -
        @id (HomogeneousPoly n) Φ := by
  change rationalCoefficientComponent n χ (Qint u 1) (@id (HomogeneousPoly n) Φ) -
    @id (HomogeneousPoly n) Φ = _
  rw [rho_Qint_one n χ u, rho_U]

/-! ### The coordinate of the Hecke image -/

/-- **Cocycle-level Hecke formula for the twisted good-line binary edge.**  If the edge cocycles of the
relative two-cocycle `c` are the exponentials of closed pairs `b μ`, then the binary coordinate of
the edge of `T c` at `m` is `sgnP p • coord (b m) + ∑_j A(B_j) coord (b μ_j)`. -/
theorem coordF_edge_heckeT (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (p : Nat.Primes)
    (c : groupCohomology.cocycles₂ (Aρ1 (rationalCoefficientComponent n χ)))
    (hrel : ∀ a b, c (U1 a, U1 b) = 0) (b : GL (Fin 2) ℤ → Fin 2 → HomogeneousPoly n)
    (hb : ∀ μ, ClosedL n (b μ))
    (hexp : ∀ μ y, @id (HomogeneousPoly n) (edgeL (rationalCoefficientComponent n χ) c μ y) =
      Exp n (b μ) y) (m : GL (Fin 2) ℤ) :
    coordF n (fun u => @id (HomogeneousPoly n)
        (edgeL (rationalCoefficientComponent n χ) (heckeTwoL p (rationalCoefficientComponent n χ) c) m u)) =
      ((IdentityPlaneLocalOp.sgnP p : ℤ) : ℂ) • lowerRadicalCoordinate n (b m) +
        ∑ j : Option (Fin p.val), Binary.homogeneousAction (n + 1) 0 (cx2 (BGL p j))
          (lowerRadicalCoordinate n (b (arithmeticDelta p m j))) := by
  obtain ⟨T, hT⟩ := radT_term n χ hχ p (edgeL (rationalCoefficientComponent n χ) c m) (b m) (hb m)
    (hexp m) m
  set Φ : Aρ1 (rationalCoefficientComponent n χ) :=
    ∑ d : Fin p.val × Fin p.val, phiL p (rationalCoefficientComponent n χ) c m d
  have hlev : ∀ (j : Option (Fin p.val)) (u : ℤ × ℤ),
      @id (HomogeneousPoly n) (R1 (rationalCoefficientComponent n χ) (rExpl p (.inl j))
        (edgeL (rationalCoefficientComponent n χ) c (arithmeticDelta p m j) (ivmul u (Bint p j)))) =
      Exp n (leviP n (cx2 (BGL p j)) (b (arithmeticDelta p m j))) u := by
    intro j u
    change rationalCoefficientComponent n χ (rExpl p (.inl j)) (@id (HomogeneousPoly n)
      (edgeL (rationalCoefficientComponent n χ) c (arithmeticDelta p m j) (ivmul u (Bint p j)))) = _
    rw [hexp (arithmeticDelta p m j) (ivmul u (Bint p j))]
    exact leviT_term n χ p (b (arithmeticDelta p m j)) j u
  have hfun : (fun u => @id (HomogeneousPoly n)
        (edgeL (rationalCoefficientComponent n χ) (heckeTwoL p (rationalCoefficientComponent n χ) c) m u)) =
      (∑ j : Option (Fin p.val), Exp n (leviP n (cx2 (BGL p j)) (b (arithmeticDelta p m j)))) +
        (((IdentityPlaneLocalOp.sgnP p : ℤ) : ℂ) •
          (((p.val : ℂ) ^ 2) • Exp n (leviP n (cx2 (integralEmbed m))
              (sigmaP n (epsC p) (leviP n (cx2 (integralEmbed m⁻¹)) (b m)))) +
            fun u => ρn n (lowerRadicalLattice (Multiplicative.ofAdd u)) T - T)) +
        fun u => ρn n (lowerRadicalLattice (Multiplicative.ofAdd u)) (@id (HomogeneousPoly n) Φ) -
          @id (HomogeneousPoly n) Φ := by
    funext u
    refine (congrArg (@id (HomogeneousPoly n))
      (edgeL_heckeTwoL p (rationalCoefficientComponent n χ) c hrel m u)).trans ?_
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply]
    have hsplit : @id (HomogeneousPoly n)
        ((∑ j : Option (Fin p.val), R1 (rationalCoefficientComponent n χ) (rExpl p (.inl j))
            (edgeL (rationalCoefficientComponent n χ) c (arithmeticDelta p m j) (ivmul u (Bint p j)))) +
          R1 (rationalCoefficientComponent n χ) (Qint 0 m)
            (CorL p (rationalCoefficientComponent n χ)
              (conjL (rationalCoefficientComponent n χ) m⁻¹ (edgeL (rationalCoefficientComponent n χ) c m))
              (ivmul u m.val)) +
          (R1 (rationalCoefficientComponent n χ) (Qint u 1) Φ - Φ)) =
        (∑ j : Option (Fin p.val), @id (HomogeneousPoly n)
            (R1 (rationalCoefficientComponent n χ) (rExpl p (.inl j))
              (edgeL (rationalCoefficientComponent n χ) c (arithmeticDelta p m j) (ivmul u (Bint p j))))) +
          @id (HomogeneousPoly n) (R1 (rationalCoefficientComponent n χ) (Qint 0 m)
            (CorL p (rationalCoefficientComponent n χ)
              (conjL (rationalCoefficientComponent n χ) m⁻¹ (edgeL (rationalCoefficientComponent n χ) c m))
              (ivmul u m.val))) +
          @id (HomogeneousPoly n) (R1 (rationalCoefficientComponent n χ) (Qint u 1) Φ - Φ) := rfl
    refine hsplit.trans ?_
    exact congrArg₂ (· + ·) (congrArg₂ (· + ·) (Finset.sum_congr rfl (fun j _ => hlev j u)) (hT u))
      (cobT_term n χ Φ u)
  have hL : ∀ j : Option (Fin p.val),
      coordF n (Exp n (leviP n (cx2 (BGL p j)) (b (arithmeticDelta p m j)))) =
        Binary.homogeneousAction (n + 1) 0 (cx2 (BGL p j))
          (lowerRadicalCoordinate n (b (arithmeticDelta p m j))) := by
    intro j
    rw [coordF_exp, coord_leviP]
  have hR : ((p.val : ℂ) ^ 2) • coordF n (Exp n (leviP n (cx2 (integralEmbed m))
      (sigmaP n (epsC p) (leviP n (cx2 (integralEmbed m⁻¹)) (b m))))) = lowerRadicalCoordinate n (b m) := by
    rw [coordF_exp, coord_leviP, coord_sigmaP, coord_leviP, map_smul, smul_smul, p_sq_eps p,
      one_smul, AL_mul, ← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one, map_one,
      Module.End.one_apply]
  have key : coordF n
      ((∑ j : Option (Fin p.val), Exp n (leviP n (cx2 (BGL p j)) (b (arithmeticDelta p m j)))) +
        (((IdentityPlaneLocalOp.sgnP p : ℤ) : ℂ) •
          (((p.val : ℂ) ^ 2) • Exp n (leviP n (cx2 (integralEmbed m))
              (sigmaP n (epsC p) (leviP n (cx2 (integralEmbed m⁻¹)) (b m)))) +
            fun u => ρn n (lowerRadicalLattice (Multiplicative.ofAdd u)) T - T)) +
        fun u => ρn n (lowerRadicalLattice (Multiplicative.ofAdd u)) (@id (HomogeneousPoly n) Φ) -
          @id (HomogeneousPoly n) Φ) =
      (∑ j : Option (Fin p.val), Binary.homogeneousAction (n + 1) 0 (cx2 (BGL p j))
        (lowerRadicalCoordinate n (b (arithmeticDelta p m j)))) +
        ((IdentityPlaneLocalOp.sgnP p : ℤ) : ℂ) • lowerRadicalCoordinate n (b m) := by
    generalize ((p.val : ℂ) ^ 2) = k at hR ⊢
    simp only [map_add, map_sum, map_smul, hR, coordF_cob, add_zero]
    exact congrArg (· + ((IdentityPlaneLocalOp.sgnP p : ℤ) : ℂ) • lowerRadicalCoordinate n (b m))
      (Finset.sum_congr rfl (fun j _ => hL j))
  calc coordF n (fun u => @id (HomogeneousPoly n)
        (edgeL (rationalCoefficientComponent n χ) (heckeTwoL p (rationalCoefficientComponent n χ) c) m u))
      = _ := congrArg (coordF n) hfun
    _ = _ := key
    _ = _ := add_comm _ _

end LH

end TernaryPeriodPolynomials.Twisted
