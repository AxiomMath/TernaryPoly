module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Edge.LatticeCocycleLevi
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Edge.LatticeAssembly
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Edge.NormalCocycle

@[expose] public section


/-!
# The algebra of the real-side comparison

Let `t` be a regular two-cocycle of the real good-line stabilizer whose restriction to the radical
is the coboundary of a differentiable family `a` of linear tests, and let `T = t + δH` for a
one-cochain `H` of scalar tests linear in the test at the real translates `h₀ g` of an adelic
point `h₀`. Suppose that the coboundary of a one-cochain `β` of the
arithmetic good-line stabilizer is `T` read at `h₀` on radical lattice pairs, and
that its mixed coordinate is the lattice coordinate of the radical edge of `T` at `h₀`. If `a` and
`H` are invariant at `h₀` under the integral Levi at infinity, then
`ψ(r) = (a(3 r) + H(e^{3 r}))(h₀)` satisfies the hypotheses of the lattice edge comparison, and
`3` times the derivative edge of `t` at `h₀` is a one-coboundary of `GL₂(ℤ)` acting on `Sym^{n+1}`
without determinant twist. The swap of the binary variables intertwines this action with its
conjugate by the pivot swap.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {n : ℕ}

/-! ### Coboundaries of one-cochains of the real stabilizer -/

/-- The coboundary `δH (a, b) = a • H b - H (a b) + H a` of a one-cochain of `LineGroup`. -/
def lineCoboundary (H : LineGroup → LineValues n) (a b : LineGroup) : LineValues n :=
  a • H b - H (a * b) + H a

theorem radicalEdge_add (t s : LineGroup → LineGroup → LineValues n) (m : unimodularLevi)
    (Y : Fin 2 → ℝ) :
    radicalEdge (fun a b => t a b + s a b) m Y = radicalEdge t m Y + radicalEdge s m Y := by
  simp only [radicalEdge_eq]
  abel

theorem lineLevi_mul_radical (m : unimodularLevi) (Y : Fin 2 → ℝ) :
    lineLeviElement m * lineRadicalElement (rowAction m Y) =
      lineRadicalElement Y * lineLeviElement m := by
  rw [rowAction_apply, ← lineLevi_conj_radical]
  group

/-- The radical edge of a coboundary. -/
theorem radicalEdge_lineCoboundary (H : LineGroup → LineValues n) (m : unimodularLevi)
    (Y : Fin 2 → ℝ) :
    radicalEdge (lineCoboundary H) m Y =
      (lineLeviElement m • H (lineRadicalElement (rowAction m Y)) - H (lineRadicalElement Y)) +
        (H (lineLeviElement m) - lineRadicalElement Y • H (lineLeviElement m)) := by
  rw [radicalEdge_eq, ← rowAction_apply]
  unfold lineCoboundary
  rw [lineLevi_mul_radical]
  abel

/-- On radical pairs, `t + δH` is the coboundary of `Y ↦ a Y + H (e^Y)`. -/
theorem add_lineCoboundary_radical {t : LineGroup → LineGroup → LineValues n}
    {a : (Fin 2 → ℝ) → LineValues n}
    (trivial : ∀ Y Y', t (lineRadicalElement Y) (lineRadicalElement Y') =
      lineRadicalElement Y • a Y' - a (Y + Y') + a Y) (H : LineGroup → LineValues n)
    (Y Y' : Fin 2 → ℝ) :
    t (lineRadicalElement Y) (lineRadicalElement Y') +
        lineCoboundary H (lineRadicalElement Y) (lineRadicalElement Y') =
      lineRadicalElement Y • (a Y' + H (lineRadicalElement Y')) -
        (a (Y + Y') + H (lineRadicalElement (Y + Y'))) + (a Y + H (lineRadicalElement Y)) := by
  rw [trivial, lineCoboundary, ← lineRadicalElement_add, smul_add]
  abel

/-- The radical edge of `t + δH` is the corrected radical edge of `t`, plus the Levi difference
of `Y ↦ a Y + H (e^Y)`, plus a radical coboundary. -/
theorem radicalEdge_add_lineCoboundary (t : LineGroup → LineGroup → LineValues n)
    (a : (Fin 2 → ℝ) → LineValues n) (H : LineGroup → LineValues n) (m : unimodularLevi)
    (Y : Fin 2 → ℝ) :
    radicalEdge (fun p q => t p q + lineCoboundary H p q) m Y =
      leviCorrectedEdge t a m Y +
        (lineLeviElement m • (a (rowAction m Y) + H (lineRadicalElement (rowAction m Y))) -
          (a Y + H (lineRadicalElement Y))) +
        (H (lineLeviElement m) - lineRadicalElement Y • H (lineLeviElement m)) := by
  rw [radicalEdge_add, radicalEdge_lineCoboundary, leviCorrectedEdge, smul_add]
  abel

/-! ### Vectors of linear tests -/

theorem LinearTests.add {F G : LineValues n} (hF : LinearTests F) (hG : LinearTests G) :
    LinearTests (F + G) := by
  intro h functional
  change F (h, functional) + G (h, functional) = _
  rw [lineVector_add, map_add, hF, hG]

theorem lineVector_eq_of_tests {F : LineValues n} {h h' : BinaryAdelicGL}
    (same : ∀ ℓ, F (h, ℓ) = F (h', ℓ)) : lineVector F h = lineVector F h' := by
  unfold lineVector
  simp_rw [same]

/-- The coefficient vector of a translate of scalar tests that are linear in the test at the
moved point. -/
theorem lineVector_smul_of_linear (q : LineGroup) {F : LineValues n} {h : BinaryAdelicGL}
    (hF : ∀ ℓ, F (h * atInfinity (pivotConjugate (q.right : BinaryRealGL)), ℓ) =
      ℓ (lineVector F (h * atInfinity (pivotConjugate (q.right : BinaryRealGL))))) :
    lineVector (q • F) h = realCoefficientComponent n trivialCharacter (lineMatrix q)
      (lineVector F (h * atInfinity (pivotConjugate (q.right : BinaryRealGL)))) := by
  unfold lineVector
  simp only [lineValues_smul_apply]
  simp_rw [hF (((EdgeControl.homogeneousBasis n).coord _).comp _), LinearMap.comp_apply,
    Module.Basis.coord_apply]
  exact (EdgeControl.homogeneousBasis n).sum_repr _

/-- The coefficient vector of a radical translate of scalar tests that are linear in the test at
the point. -/
theorem lineVector_lineRadical_smul_of_linear (Y : Fin 2 → ℝ) {F : LineValues n}
    {h : BinaryAdelicGL} (hF : ∀ ℓ, F (h, ℓ) = ℓ (lineVector F h)) :
    lineVector (lineRadicalElement Y • F) h = realCoefficientComponent n trivialCharacter
      (lineRadicalMatrix (Multiplicative.ofAdd Y)) (lineVector F h) := by
  have right : ((lineRadicalElement Y).right : BinaryRealGL) = 1 := rfl
  have moved : h * atInfinity (pivotConjugate ((lineRadicalElement Y).right : BinaryRealGL)) =
      h := by
    rw [right, pivotConjugate_one, atInfinity_one, mul_one]
  rw [lineVector_smul_of_linear _ (by rw [moved]; exact hF), lineMatrix_lineRadicalElement, moved]

/-- Scalar tests linear in the test at a point, plus linear tests, are linear at that point. -/
theorem linear_add_of_linear {F G : LineValues n} {h : BinaryAdelicGL} (hF : LinearTests F)
    (hG : ∀ ℓ, G (h, ℓ) = ℓ (lineVector G h)) (ℓ : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    (F + G) (h, ℓ) = ℓ (lineVector (F + G) h) := by
  change F (h, ℓ) + G (h, ℓ) = _
  rw [lineVector_add, map_add, hF, hG]

/-! ### Integral matrices and the pivot swap -/

theorem map_binaryPivotSwap :
    GeneralLinearGroup.map (Int.castRingHom ℝ)
      (binaryPivotSwap : GeneralLinearGroup (Fin 2) ℤ) = binaryPivotSwap := by
  apply Units.ext
  funext i j
  fin_cases i <;> fin_cases j <;> simp [binaryPivotSwap, GeneralLinearGroup.map_apply]

/-- Conjugation of an integral matrix by the pivot swap. -/
def integralPivot (γ : GeneralLinearGroup (Fin 2) ℤ) : GeneralLinearGroup (Fin 2) ℤ :=
  binaryPivotSwap * γ * binaryPivotSwap

theorem map_integralPivot (γ : GeneralLinearGroup (Fin 2) ℤ) :
    GeneralLinearGroup.map (Int.castRingHom ℝ) (integralPivot γ) =
      pivotConjugate (GeneralLinearGroup.map (Int.castRingHom ℝ) γ) := by
  rw [integralPivot, map_mul, map_mul, map_binaryPivotSwap]
  rfl

theorem pivotConjugate_pivotConjugate (m : BinaryRealGL) :
    pivotConjugate (pivotConjugate m) = m := by
  unfold pivotConjugate
  calc binaryPivotSwap * (binaryPivotSwap * m * binaryPivotSwap) * binaryPivotSwap =
      (binaryPivotSwap * binaryPivotSwap) * m * (binaryPivotSwap * binaryPivotSwap) := by group
    _ = m := by rw [binaryPivotSwap_mul_self, one_mul, mul_one]

/-- The untwisted action of an integral matrix through its real image. -/
theorem det_smul_binaryCoefficient_map (γ : GeneralLinearGroup (Fin 2) ℤ)
    (P : Binary.HomogeneousPoly (n + 1)) :
    (((GeneralLinearGroup.map (Int.castRingHom ℝ) γ : BinaryRealGL).val.det : ℝ) : ℂ) •
        binaryCoefficient n (GeneralLinearGroup.map (Int.castRingHom ℝ) γ) P =
      Binary.homogeneousAction (n + 1) 0 (GeneralLinearGroup.map (Int.castRingHom ℂ) γ) P := by
  rw [det_smul_binaryCoefficient, ← map_integralLevi γ]
  rfl

theorem binarySwap_binarySwap (P : Binary.HomogeneousPoly (n + 1)) :
    binarySwap n (binarySwap n P) = P := by
  apply Subtype.ext
  change MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1)
    (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) P.val) = P.val
  have involution : (⇑(Equiv.swap (0 : Fin 2) 1) ∘ ⇑(Equiv.swap (0 : Fin 2) 1)) = id :=
    funext fun i => Equiv.swap_apply_self _ _ _
  rw [MvPolynomial.rename_rename, involution, MvPolynomial.rename_id_apply]

/-- **The swap intertwines the untwisted actions of `σ γ σ` and `γ`.** -/
theorem binarySwap_homogeneousAction (γ : GeneralLinearGroup (Fin 2) ℤ)
    (P : Binary.HomogeneousPoly (n + 1)) :
    binarySwap n (Binary.homogeneousAction (n + 1) 0
        (GeneralLinearGroup.map (Int.castRingHom ℂ) (integralPivot γ)) P) =
      Binary.homogeneousAction (n + 1) 0 (GeneralLinearGroup.map (Int.castRingHom ℂ) γ)
        (binarySwap n P) := by
  rw [← det_smul_binaryCoefficient_map, ← det_smul_binaryCoefficient_map, map_integralPivot,
    map_smul, binarySwap_binaryCoefficient, det_pivotConjugate]

/-! ### The lattice data of `t + δH` -/

theorem rowAction_latticeVector (γ : GeneralLinearGroup (Fin 2) ℤ) (r : RadicalLattice) :
    rowAction (integralLevi γ) (latticeVector r) =
      latticeVector (lowerLeviLatticeInput γ r) := by
  funext j
  rw [rowAction_apply]
  fin_cases j <;>
    simp [latticeVector, lowerLeviLatticeInput, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
      integralLevi, GeneralLinearGroup.map_apply] <;> ring

theorem goodLineCoefficientRep_radical_apply (r : RadicalLattice) (v : HomogeneousPoly n) :
    (goodLineCoefficientRep n).ρ (goodLineRadicalInclusion r) v =
      realCoefficientComponent n trivialCharacter
        (lineRadicalMatrix (Multiplicative.ofAdd (latticeVector r))) v := by
  rw [← lowerRadicalLatticeRep_rho_latticeVector]
  rfl

/-- **The radical condition** for `ψ(r) = (a(3 r) + H(e^{3 r}))(h)`. -/
theorem lineVector_add_lineCoboundary_lattice {t : LineGroup → LineGroup → LineValues n}
    {a : (Fin 2 → ℝ) → LineValues n} (linear : ∀ Y, LinearTests (a Y))
    (trivial : ∀ Y Y', t (lineRadicalElement Y) (lineRadicalElement Y') =
      lineRadicalElement Y • a Y' - a (Y + Y') + a Y) {H : LineGroup → LineValues n}
    (h : BinaryAdelicGL) (Hlinear : ∀ q ℓ, H q (h, ℓ) = ℓ (lineVector (H q) h))
    (r₁ r₂ : RadicalLattice) :
    lineVector (t (lineRadicalElement (latticeVector r₁)) (lineRadicalElement (latticeVector r₂)) +
        lineCoboundary H (lineRadicalElement (latticeVector r₁))
          (lineRadicalElement (latticeVector r₂))) h =
      realCoefficientComponent n trivialCharacter
          (lineRadicalMatrix (Multiplicative.ofAdd (latticeVector r₁)))
          (lineVector (a (latticeVector r₂) + H (lineRadicalElement (latticeVector r₂))) h) -
        lineVector (a (latticeVector (r₁ * r₂)) +
          H (lineRadicalElement (latticeVector (r₁ * r₂)))) h +
        lineVector (a (latticeVector r₁) + H (lineRadicalElement (latticeVector r₁))) h := by
  rw [add_lineCoboundary_radical trivial, lineVector_add, lineVector_sub,
    lineVector_lineRadical_smul_of_linear _ (linear_add_of_linear (linear _) (Hlinear _)),
    latticeVector_mul]

/-- **The mixed condition**: the lattice coordinate of the radical edge of `t + δH` is the lattice
coordinate of the corrected radical edge of `t` plus the Levi difference of `ψ`. -/
theorem latticeCoordinate_radicalEdge_add_lineCoboundary (t : LineGroup → LineGroup → LineValues n)
    {a : (Fin 2 → ℝ) → LineValues n} (linear : ∀ Y, LinearTests (a Y))
    {H : LineGroup → LineValues n} (h : BinaryAdelicGL)
    (Hlinear : ∀ q (g : BinaryRealGL) ℓ,
      H q (h * atInfinity g, ℓ) = ℓ (lineVector (H q) (h * atInfinity g)))
    (γ : GeneralLinearGroup (Fin 2) ℤ)
    (invariant : ∀ Y ℓ, (a Y + H (lineRadicalElement Y))
      (h * atInfinity (pivotConjugate (GeneralLinearGroup.map (Int.castRingHom ℝ) γ)), ℓ) =
        (a Y + H (lineRadicalElement Y)) (h, ℓ)) :
    latticeCoordinate n (fun r => lineVector (radicalEdge (fun p q => t p q + lineCoboundary H p q)
        (integralLevi γ) (latticeVector r)) h) =
      latticeCoordinate n
          (fun r => lineVector (leviCorrectedEdge t a (integralLevi γ) (latticeVector r)) h) +
        leviDifferenceCoordinate
          (fun r => lineVector (a (latticeVector r) + H (lineRadicalElement (latticeVector r))) h)
          γ := by
  have atPoint (q : LineGroup) (ℓ : HomogeneousPoly n →ₗ[ℂ] ℂ) :
      H q (h, ℓ) = ℓ (lineVector (H q) h) := by
    simpa only [atInfinity_one, mul_one] using Hlinear q 1 ℓ
  set w : HomogeneousPoly n := lineVector (H (lineLeviElement (integralLevi γ))) h
  set ψ : RadicalLattice → goodLineCoefficientRep n :=
    fun r => lineVector (a (latticeVector r) + H (lineRadicalElement (latticeVector r))) h
  have killed : latticeCoordinate n (fun r =>
      w - rationalCoefficientComponent n trivialCharacter (lowerRadicalLattice r) w) = 0 :=
    lowerRadicalCoordinate_lattice_coboundary w
  have pointwise : (fun r => lineVector (radicalEdge (fun p q => t p q + lineCoboundary H p q)
        (integralLevi γ) (latticeVector r)) h) =
      (fun r => lineVector (leviCorrectedEdge t a (integralLevi γ) (latticeVector r)) h) +
        (fun r => goodLineCoefficientPolynomial n
          ((goodLineCoefficientRep n).ρ (goodLineLeviSection γ) (ψ (lowerLeviLatticeInput γ r)) -
            ψ r)) +
        (fun r =>
          w - rationalCoefficientComponent n trivialCharacter (lowerRadicalLattice r) w) := by
    funext r
    simp only [Pi.add_apply]
    rw [radicalEdge_add_lineCoboundary, lineVector_add, lineVector_add, lineVector_sub,
      lineVector_sub, lineVector_smul_of_linear _ (linear_add_of_linear (linear _) (Hlinear _ _)),
      lineVector_lineRadical_smul_of_linear _ (atPoint _), rowAction_latticeVector,
      lineVector_eq_of_tests (h := h * atInfinity (pivotConjugate
        ((lineLeviElement (integralLevi γ)).right : BinaryRealGL))) (invariant _),
      lineMatrix_integralLevi,
      ← goodLineCoefficientRep_radical_apply]
    rfl
  rw [pointwise, map_add, map_add, killed, add_zero]
  rfl

/-! ### The derivative edge is a coboundary -/

/-- The lower radical coordinate of the derivative of an invariant family of tests is invariant
at any adelic point. -/
theorem radicalDerivativeCoordinate_eq_of_tests {a : (Fin 2 → ℝ) → LineValues n}
    {h h' : BinaryAdelicGL} (same : ∀ Y ℓ, a Y (h, ℓ) = a Y (h', ℓ)) :
    radicalDerivativeCoordinate a h = radicalDerivativeCoordinate a h' := by
  unfold radicalDerivativeCoordinate lineVector
  simp_rw [same]

/-- **The arithmetic comparison makes the derivative edge a coboundary.** Let `t` be a regular
two-cocycle of the real good-line stabilizer whose restriction to the radical is the coboundary of
a differentiable family `a` of linear tests, let `H` be a one-cochain of scalar tests linear in the
test at the real translates of `h`, and let `β` be a one-cochain of the arithmetic good-line
stabilizer whose coboundary is `t + δH` at `h` on radical lattice pairs and whose mixed coordinate
is the lattice coordinate of the radical edge of `t + δH` at `h`. If `a` and `H` are invariant at `h` under the integral Levi at infinity, then
`3` times the derivative edge of `t` at `h` is a one-coboundary of `GL₂(ℤ)` acting on `Sym^{n+1}`
without determinant twist. -/
theorem exists_derivativeEdge_coboundary (positive : 0 < n)
    {t : LineGroup → LineGroup → LineValues n} (cocycle : IsTwoCocycle t)
    (regular : EdgeRegular t) {a : (Fin 2 → ℝ) → LineValues n} (linear : ∀ Y, LinearTests (a Y))
    (differentiable : ∀ p, DifferentiableAt ℝ (fun Y => a Y p) 0)
    (trivial : ∀ Y Y', t (lineRadicalElement Y) (lineRadicalElement Y') =
      lineRadicalElement Y • a Y' - a (Y + Y') + a Y) {H : LineGroup → LineValues n}
    (h : BinaryAdelicGL)
    (Hlinear : ∀ q (g : BinaryRealGL) ℓ,
      H q (h * atInfinity g, ℓ) = ℓ (lineVector (H q) (h * atInfinity g)))
    (aInvariant : ∀ (γ : GeneralLinearGroup (Fin 2) ℤ) Y ℓ,
      a Y (h * atInfinity (pivotConjugate (GeneralLinearGroup.map (Int.castRingHom ℝ) γ)), ℓ) =
        a Y (h, ℓ))
    (HInvariant : ∀ (γ : GeneralLinearGroup (Fin 2) ℤ) q ℓ,
      H q (h * atInfinity (pivotConjugate (GeneralLinearGroup.map (Int.castRingHom ℝ) γ)), ℓ) =
        H q (h, ℓ))
    (β : flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine) →
      goodLineCoefficientRep n)
    (radical : ∀ r₁ r₂, twoBoundaryCycle (goodLineCoefficientRep n) β
      (goodLineRadicalInclusion r₁, goodLineRadicalInclusion r₂) =
        lineVector (t (lineRadicalElement (latticeVector r₁))
            (lineRadicalElement (latticeVector r₂)) +
          lineCoboundary H (lineRadicalElement (latticeVector r₁))
            (lineRadicalElement (latticeVector r₂))) h)
    (mixed : ∀ γ, goodLineMixedCoordinate n γ
      (fun pair => twoBoundaryCycle (goodLineCoefficientRep n) β pair) =
        latticeCoordinate n (fun r => lineVector (radicalEdge
          (fun p q => t p q + lineCoboundary H p q) (integralLevi γ) (latticeVector r)) h)) :
    ∃ P : Binary.HomogeneousPoly (n + 1), ∀ γ : GeneralLinearGroup (Fin 2) ℤ,
      (3 : ℂ) • derivativeEdge t (integralLevi γ) h =
        Binary.homogeneousAction (n + 1) 0 (GeneralLinearGroup.map (Int.castRingHom ℂ) γ) P -
          P := by
  set ψ : RadicalLattice → goodLineCoefficientRep n :=
    fun r => lineVector (a (latticeVector r) + H (lineRadicalElement (latticeVector r))) h
  set G := fun γ => latticeEdgeCocycle cocycle regular.linear linear trivial γ h
  have radical' (r₁ r₂ : RadicalLattice) : twoBoundaryCycle (goodLineCoefficientRep n) β
      (goodLineRadicalInclusion r₁, goodLineRadicalInclusion r₂) =
        (goodLineCoefficientRep n).ρ (goodLineRadicalInclusion r₁) (ψ r₂) - ψ (r₁ * r₂) +
          ψ r₁ := by
    rw [radical, lineVector_add_lineCoboundary_lattice linear trivial h
      (fun q ℓ => by simpa only [atInfinity_one, mul_one] using Hlinear q 1 ℓ),
      ← goodLineCoefficientRep_radical_apply]
    rfl
  have mixed' (γ : GeneralLinearGroup (Fin 2) ℤ) : goodLineMixedCoordinate n γ
      (fun pair => twoBoundaryCycle (goodLineCoefficientRep n) β pair) =
        lowerRadicalCocycleCoordinate n (G γ) + leviDifferenceCoordinate ψ γ := by
    rw [mixed, latticeCoordinate_radicalEdge_add_lineCoboundary t linear h Hlinear γ
      (fun Y ℓ => by
        change a Y _ + H _ _ = a Y _ + H _ _
        rw [aInvariant, HInvariant])]
    rfl
  obtain ⟨Q, hQ⟩ := latticeEdge_coboundary positive β ψ G radical' mixed'
  refine ⟨Q + (3 : ℂ) • radicalDerivativeCoordinate a h, fun γ => ?_⟩
  have value := hQ γ
  rw [lowerRadicalCocycleCoordinate_latticeEdgeCocycle cocycle regular linear differentiable
    trivial] at value
  have levi : edgeAction (integralLevi γ) (radicalDerivativeCoordinate a) h =
      Binary.homogeneousAction (n + 1) 0 (GeneralLinearGroup.map (Int.castRingHom ℂ) γ)
        (radicalDerivativeCoordinate a h) := by
    unfold edgeAction
    rw [radicalDerivativeCoordinate_eq_of_tests (h := h * atInfinity (pivotConjugate
      ((integralLevi γ : unimodularLevi) : BinaryRealGL))) (h' := h) (aInvariant γ)]
    exact det_smul_binaryCoefficient_map γ _
  rw [levi, smul_sub, smul_sub, sub_eq_iff_eq_add] at value
  rw [value, map_add, map_smul]
  abel

end TernaryPeriodPolynomials.AnalyticClasses
