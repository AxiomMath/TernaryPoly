module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.DimensionCriterion
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.TpExistence
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Eigen.Satake.DistinctData
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Eigen.Satake.HeckeFormula

@[expose] public section


/-!
# The `T_p` value of the pair character

For a prime `p ≠ 3`, the away-three eigencharacter of a nonzero associate pair takes the value
`χ(sAd p) + (p² + p) p^{-(n+3)/2} ω(diag(p,1))` at `T_p`. When the cuspidal representation has a
nonzero away-from-three fixed vector this is the Satake computation of the `T_p` eigenvalue. When
it has none, every induced section at the cohomological point vanishes: the Hecke formula for the
trivial correspondence `Γ · 1 · Γ` multiplies every such section by `ω(1) = 0`. So the boundary
summands are acted on by any scalar, in particular by the Satake value. Since `|ω| ≤ 1`, the
character value differs from `χ(sAd p)` by at most `(p² + p) p^{-(n+3)/2}`, and for `n ≥ 1` its
modulus is at most `5/2`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.RepresentationTheory
open TernaryPeriodPolynomials.HeckeEigen
open TernaryPeriodPolynomials.HeckeEigen.Satake
open TernaryPeriodPolynomials.SphericalDetection

namespace TernaryPeriodPolynomials.Spectral.PairCharacterBound

variable {n : ℕ}

/-- The trivial correspondence `Γ · 1 · Γ = Γ`, with the single representative `1`. -/
def identityCorrespondence : HeckeCorrespondence where
  g := 1
  representatives := {1}
  inDoubleCoset := by
    intro r hr
    rw [Finset.mem_singleton.mp hr]
    exact ⟨1, 1, by simp⟩
  complete := by
    intro a b
    refine ⟨1, Finset.mem_singleton_self 1, ?_⟩
    simpa using rationalLevel.mul_mem a.2 b.2
  disjoint := by
    intro r hr t ht _
    rw [Finset.mem_singleton.mp hr, Finset.mem_singleton.mp ht]

/-- Without nonzero away-from-three fixed vectors every Hecke scalar `ω(B)` is zero. -/
theorem omega_eq_zero_of_subsingleton (σ : CuspidalRepresentation)
    [Subsingleton (fixedVectors σ K3)] (B : BinaryFiniteGL) : omega σ B = 0 := by
  unfold omega scalarOf
  rw [dite_eq_right]
  rintro ⟨h1, -⟩
  exact not_nontrivial (fixedVectors σ K3) h1

/-- Without nonzero away-from-three fixed vectors every induced section at the cohomological
point vanishes. -/
theorem isInduced_eq_zero_of_subsingleton (D : InducingData n)
    [Subsingleton (fixedVectors D.cusp K3)] (side : Side) {f : AdelicGL → ℂ}
    (hf : IsInduced D side cohomologicalPoint f) (g : AdelicGL) : f g = 0 := by
  have hmem : ∀ r ∈ identityCorrespondence.representatives, r = 1 :=
    fun r hr => Finset.mem_singleton.mp hr
  cases side
  · have h := plane_hecke_formula D identityCorrespondence (fun _ => 1) (fun _ => 1)
      (fun _ => 0) (fun _ => 0) (fun _ => 1) (fun _ => 1) (fun _ _ => map_one _)
      (fun r hr => by rw [hmem r hr]; simp)
      (fun _ _ => by simp [Helpers.atFinite_one, planeUnipotent_zero, planeLevi_one_one])
      (fun _ _ => one_mem _) f hf g
    simpa [identityCorrespondence, planeWeight, omega_eq_zero_of_subsingleton,
      Helpers.atFinite_one] using h
  · have h := line_hecke_formula D identityCorrespondence (fun _ => 1) (fun _ => 1)
      (fun _ => 0) (fun _ => 0) (fun _ => 1) (fun _ => 1) (fun _ _ => map_one _)
      (fun r hr => by rw [hmem r hr]; simp)
      (fun _ _ => by simp [Helpers.atFinite_one, lineUnipotent_zero, lineLevi_one_one])
      (fun _ _ => one_mem _) f hf g
    simpa [identityCorrespondence, lineWeight, omega_eq_zero_of_subsingleton,
      Helpers.atFinite_one] using h

/-- **`T_p` acts on every boundary summand by `cuspPlaneEigenvalue`**, with no hypothesis on the
away-from-three fixed vectors. -/
theorem summand_Tp_scalar_all (D : InducingData n) {p : ℕ} (hp : p.Prime) (h3 : p ≠ 3)
    (t : HeckeCorrespondence) (ht : AwayThree t) (hg : t.g = gP hp)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke) (side : Side) :
    ∀ a ∈ boundarySummand D side, hecke side t a = cuspPlaneEigenvalue D hp • a := by
  rcases subsingleton_or_nontrivial (fixedVectors D.cusp K3) with hs | hn
  · apply summand_scalar_of_source D side t hecke hhecke
    apply source_scalar_of_function t
    intro f hf g
    rw [isInduced_eq_zero_of_subsingleton D side hf g, mul_zero]
    exact Finset.sum_eq_zero fun r _ => isInduced_eq_zero_of_subsingleton D side hf _
  · exact summand_Tp_scalar D hp h3 t ht hg hecke hhecke side

/-- A scalar acting on both boundary summands is the pair character, if the pair is nonzero. -/
theorem pairCharacter_eq_of_summand_scalar (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (t : HeckeCorrespondence) (ht : AwayThree t)
    (μ : ℂ) (hP : ∀ a ∈ boundarySummand D .plane, hecke .plane t a = μ • a)
    (hL : ∀ b ∈ boundarySummand D .line, hecke .line t b = μ • b)
    (hne : associatePair D ≠ ⊥) : pairCharacter D hecke hhecke t = μ := by
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have h1 := pairCharacter_spec D hecke hhecke t ht y hy
  have hy' := hy
  rw [associatePair, Submodule.mem_prod] at hy'
  have h2 : pairHecke D hecke t y = μ • y := by
    change ((hecke .plane t).prodMap (hecke .line t)) y = μ • y
    rw [LinearMap.prodMap_apply, hP _ hy'.1, hL _ hy'.2]
    rfl
  rw [h1] at h2
  have h0 : (pairCharacter D hecke hhecke t - μ) • y = 0 := by rw [sub_smul, h2, sub_self]
  by_contra hc
  apply hy0
  rw [← one_smul ℂ y, ← inv_mul_cancel₀ (sub_ne_zero.mpr hc), mul_smul, h0, smul_zero]

/-- **The `T_p` value of the pair character** is the cohomological plane eigenvalue. -/
theorem pairCharacter_tp_eq (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (hne : associatePair D ≠ ⊥) (p : Nat.Primes)
    (hp3 : p.val ≠ 3) :
    pairCharacter D hecke hhecke (TpExistence.tp p) = cuspPlaneEigenvalue D p.property :=
  pairCharacter_eq_of_summand_scalar D hecke hhecke _ (TpExistence.tp_awayThree p hp3) _
    (summand_Tp_scalar_all D p.property hp3 _ (TpExistence.tp_awayThree p hp3) rfl hecke hhecke
      .plane)
    (summand_Tp_scalar_all D p.property hp3 _ (TpExistence.tp_awayThree p hp3) rfl hecke hhecke
      .line)
    hne

/-- **Distance of the `T_p` value from the character term.** -/
theorem pairCharacter_tp_sub_norm_le (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (hne : associatePair D ≠ ⊥) (p : Nat.Primes)
    (hp3 : p.val ≠ 3) :
    ‖pairCharacter D hecke hhecke (TpExistence.tp p) -
        D.chi.toMonoidHom (sAd (pUnit p.property))‖ ≤
      ((p : ℝ) ^ 2 + p) * Real.exp (-(((n : ℝ) + 3) / 2 * Real.log p)) := by
  rw [pairCharacter_tp_eq D hecke hhecke hne p hp3, cuspPlaneEigenvalue, add_sub_cancel_left]
  exact prime_plane_cusp_part_bound_real D p.property

/-- **Distance of the `T_p` value from `1`** for the trivial character. -/
theorem pairCharacter_tp_sub_one_norm_le (D : InducingData n) (hχ : D.chi = trivialCharacter)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hne : associatePair D ≠ ⊥) (p : Nat.Primes) (hp3 : p.val ≠ 3) :
    ‖pairCharacter D hecke hhecke (TpExistence.tp p) - 1‖ ≤
      ((p : ℝ) ^ 2 + p) * Real.exp (-(((n : ℝ) + 3) / 2 * Real.log p)) := by
  have hone : D.chi.toMonoidHom (sAd (pUnit p.property)) = 1 := by
    rw [hχ]
    rfl
  have h := pairCharacter_tp_sub_norm_le D hecke hhecke hne p hp3
  rwa [hone] at h

/-- **The `T_p` value of the pair character has modulus at most `5/2`** for `n ≥ 1`. -/
theorem pairCharacter_tp_norm_le_five_halves (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (hn : 1 ≤ n) (hne : associatePair D ≠ ⊥)
    (p : Nat.Primes) (hp3 : p.val ≠ 3) :
    ‖pairCharacter D hecke hhecke (TpExistence.tp p)‖ ≤ 5 / 2 := by
  rw [pairCharacter_tp_eq D hecke hhecke hne p hp3]
  exact cuspPlaneEigenvalue_norm_le_five_halves D p.property hn

end TernaryPeriodPolynomials.Spectral.PairCharacterBound
