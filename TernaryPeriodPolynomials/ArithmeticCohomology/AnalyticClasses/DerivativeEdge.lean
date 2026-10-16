module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Real.LineTransferCocycle
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.LowerRadicalDerivative

@[expose] public section


/-!
# The derivative edge of a two-cocycle of the real good-line stabilizer

For an inhomogeneous two-cocycle `t` of `LineGroup = ℝ² ⋊ SL₂^±(ℝ)` with values in scalar tests
that are linear in the test, the mixed edge function along the radical,
`Y ↦ t(m, m⁻¹ e^Y m) - t(e^Y, m)`, is differentiable at `Y = 0` as soon as `t` is differentiable
in each argument along the radical at the identity. Its derivative, read through the lower radical
coordinate, is the **derivative edge** `Ẽ(m)`, a function on `GL₂(𝔸)` with values in `Sym^{n+1}`.
By the cocycle law of the mixed edge function, the real Levi equivariance of the lower radical
coordinate and the vanishing of the coordinate on infinitesimal coboundaries, `Ẽ` is a one-cocycle
of the real Levi: `Ẽ(m₁ m₂) = Ẽ(m₁) + m₁ ⋆ Ẽ(m₂)` with
`(m ⋆ F)(h) = det m · binaryCoefficient m (F(h · σ m σ))`. No relativity of `t` on the radical is
needed.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EdgeControl

variable {n : ℕ}

/-! ### Elements of the real stabilizer -/

/-- Radical elements of the real good-line stabilizer. -/
def lineRadicalElement (Y : Fin 2 → ℝ) : LineGroup := SemidirectProduct.inl (Multiplicative.ofAdd Y)

/-- Levi elements of the real good-line stabilizer. -/
def lineLeviElement (m : unimodularLevi) : LineGroup := SemidirectProduct.inr m

theorem lineLeviElement_mul (a b : unimodularLevi) :
    lineLeviElement (a * b) = lineLeviElement a * lineLeviElement b :=
  map_mul SemidirectProduct.inr a b

theorem lineLevi_conj_radical (m : unimodularLevi) (Y : Fin 2 → ℝ) :
    (lineLeviElement m)⁻¹ * lineRadicalElement Y * lineLeviElement m =
      lineRadicalElement (Matrix.vecMul Y (m : BinaryRealGL).val) := by
  unfold lineLeviElement lineRadicalElement
  apply SemidirectProduct.ext
  · simp only [SemidirectProduct.mul_left, SemidirectProduct.inv_left, SemidirectProduct.left_inl,
      SemidirectProduct.left_inr, SemidirectProduct.inv_right, SemidirectProduct.right_inr,
      SemidirectProduct.mul_right, SemidirectProduct.right_inl]
    simp only [map_one, inv_one, one_mul, mul_one, map_inv]
    rw [← map_inv]
    apply Multiplicative.toAdd.injective
    rw [lineRadicalAction_apply, Subgroup.coe_inv, inv_inv]
    rfl
  · simp

/-! ### Vectors of linear scalar tests -/

/-- The coefficient vector read off from the tests on the dual basis. -/
def lineVector (F : LineValues n) (h : BinaryAdelicGL) : HomogeneousPoly n :=
  ∑ j, F (h, (homogeneousBasis n).coord j) • homogeneousBasis n j

/-- Scalar tests that are linear in the test. -/
def LinearTests (F : LineValues n) : Prop :=
  ∀ h (functional : HomogeneousPoly n →ₗ[ℂ] ℂ), F (h, functional) = functional (lineVector F h)

theorem functional_eq_basis_sum (functional : HomogeneousPoly n →ₗ[ℂ] ℂ)
    (v : HomogeneousPoly n) :
    functional v = ∑ j, (homogeneousBasis n).coord j v * functional (homogeneousBasis n j) := by
  conv_lhs => rw [← (homogeneousBasis n).sum_repr v]
  simp only [map_sum, map_smul, smul_eq_mul, Module.Basis.coord_apply]

theorem lineVector_vector (v : BinaryAdelicGL → HomogeneousPoly n) (h : BinaryAdelicGL) :
    lineVector (fun p => p.2 (v p.1)) h = v h := by
  unfold lineVector
  simp only [Module.Basis.coord_apply]
  exact (homogeneousBasis n).sum_repr (v h)

theorem lineVector_add (F G : LineValues n) (h : BinaryAdelicGL) :
    lineVector (F + G) h = lineVector F h + lineVector G h := by
  unfold lineVector
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [← add_smul]
  rfl

theorem lineVector_sub (F G : LineValues n) (h : BinaryAdelicGL) :
    lineVector (F - G) h = lineVector F h - lineVector G h := by
  unfold lineVector
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  change (F (h, (homogeneousBasis n).coord j) - G (h, (homogeneousBasis n).coord j)) •
    homogeneousBasis n j = _
  exact sub_smul (R := ℂ) (M := HomogeneousPoly n) _ _ _

theorem coord_lineVector (F : LineValues n) (h : BinaryAdelicGL) (j) :
    (homogeneousBasis n).coord j (lineVector F h) = F (h, (homogeneousBasis n).coord j) := by
  rw [Module.Basis.coord_apply, lineVector, Module.Basis.repr_sum_self]

theorem functional_lineVector (F : LineValues n) (h : BinaryAdelicGL)
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    functional (lineVector F h) =
      ∑ j, F (h, (homogeneousBasis n).coord j) * functional (homogeneousBasis n j) := by
  rw [functional_eq_basis_sum]
  simp only [coord_lineVector]

theorem lineVector_smul (q : LineGroup) {F : LineValues n} (hF : LinearTests F)
    (h : BinaryAdelicGL) :
    lineVector (q • F) h = realCoefficientComponent n trivialCharacter (lineMatrix q)
      (lineVector F (h * atInfinity (pivotConjugate (q.right : BinaryRealGL)))) := by
  unfold lineVector
  simp only [lineValues_smul_apply]
  simp_rw [hF _ (((homogeneousBasis n).coord _).comp _), LinearMap.comp_apply,
    Module.Basis.coord_apply]
  exact (homogeneousBasis n).sum_repr _

theorem LinearTests.smul {F : LineValues n} (hF : LinearTests F) (q : LineGroup) :
    LinearTests (q • F) := by
  intro h functional
  rw [lineVector_smul q hF, lineValues_smul_apply, hF, LinearMap.comp_apply]

/-- Derivatives of families of linear tests are linear tests. -/
theorem linearTests_fderiv {Φ : (Fin 2 → ℝ) → LineValues n} (linear : ∀ Y, LinearTests (Φ Y))
    (differentiable : ∀ p, DifferentiableAt ℝ (fun Y => Φ Y p) 0) (v : Fin 2 → ℝ) :
    LinearTests (fun p => fderiv ℝ (fun Y => Φ Y p) 0 v) := by
  intro h functional
  have expand : (fun Y => Φ Y (h, functional)) = fun Y =>
      ∑ j, functional (homogeneousBasis n j) * Φ Y (h, (homogeneousBasis n).coord j) := by
    funext Y
    rw [linear Y h functional, functional_lineVector]
    exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  have sum : HasFDerivAt (fun Y => ∑ j, functional (homogeneousBasis n j) *
      Φ Y (h, (homogeneousBasis n).coord j))
      (∑ j, functional (homogeneousBasis n j) •
        fderiv ℝ (fun Y => Φ Y (h, (homogeneousBasis n).coord j)) 0) 0 :=
    HasFDerivAt.fun_sum (fun j _ =>
      ((differentiable _).hasFDerivAt.const_mul (functional (homogeneousBasis n j))))
  change fderiv ℝ (fun Y => Φ Y (h, functional)) 0 v = _
  rw [expand, sum.fderiv, functional_lineVector (fun p => fderiv ℝ (fun Y => Φ Y p) 0 v),
    _root_.sum_apply]
  exact Finset.sum_congr rfl (fun j _ => by rw [_root_.smul_apply, smul_eq_mul, mul_comm])

/-! ### The derivative edge -/

/-- The mixed edge function of `t` along the real radical. -/
def radicalEdge (t : LineGroup → LineGroup → LineValues n) (m : unimodularLevi)
    (Y : Fin 2 → ℝ) : LineValues n :=
  mixedEdgeFunction t (lineLeviElement m) (lineRadicalElement Y)

theorem radicalEdge_eq (t : LineGroup → LineGroup → LineValues n) (m : unimodularLevi)
    (Y : Fin 2 → ℝ) :
    radicalEdge t m Y = t (lineLeviElement m) (lineRadicalElement (Matrix.vecMul Y
      (m : BinaryRealGL).val)) - t (lineRadicalElement Y) (lineLeviElement m) := by
  unfold radicalEdge mixedEdgeFunction
  rw [lineLevi_conj_radical]

/-- Regularity of a two-cochain along the real radical at the identity. -/
structure EdgeRegular (t : LineGroup → LineGroup → LineValues n) : Prop where
  linear : ∀ a b, LinearTests (t a b)
  second : ∀ (a : LineGroup) p, DifferentiableAt ℝ (fun Y => t a (lineRadicalElement Y) p) 0
  first : ∀ (b : LineGroup) p, DifferentiableAt ℝ (fun Y => t (lineRadicalElement Y) b p) 0

/-- The linear map `Y ↦ Y m` on row vectors. -/
def rowAction (m : unimodularLevi) : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.vecMulLinear (m : BinaryRealGL).val)

theorem rowAction_apply (m : unimodularLevi) (Y : Fin 2 → ℝ) :
    rowAction m Y = Matrix.vecMul Y (m : BinaryRealGL).val := rfl

theorem EdgeRegular.edge_differentiable {t : LineGroup → LineGroup → LineValues n}
    (regular : EdgeRegular t) (m : unimodularLevi) (p) :
    DifferentiableAt ℝ (fun Y => radicalEdge t m Y p) 0 := by
  simp_rw [radicalEdge_eq]
  have second : DifferentiableAt ℝ (fun Y => t (lineLeviElement m)
      (lineRadicalElement (rowAction m Y)) p) 0 := by
    have outer := regular.second (lineLeviElement m) p
    rw [show (0 : Fin 2 → ℝ) = rowAction m 0 from (map_zero _).symm] at outer
    exact outer.comp (0 : Fin 2 → ℝ) (rowAction m).differentiableAt
  exact second.sub (regular.first (lineLeviElement m) p)

theorem EdgeRegular.edge_linear {t : LineGroup → LineGroup → LineValues n}
    (regular : EdgeRegular t) (m : unimodularLevi) (Y : Fin 2 → ℝ) :
    LinearTests (radicalEdge t m Y) := by
  intro h functional
  rw [radicalEdge_eq]
  change t _ _ (h, functional) - t _ _ (h, functional) = _
  rw [lineVector_sub, map_sub, ← regular.linear, ← regular.linear]

/-- The derivative of the radical edge function at the identity. -/
def radicalEdgeDerivative (t : LineGroup → LineGroup → LineValues n) (m : unimodularLevi)
    (p : BinaryAdelicGL × (HomogeneousPoly n →ₗ[ℂ] ℂ)) : (Fin 2 → ℝ) →L[ℝ] ℂ :=
  fderiv ℝ (fun Y => radicalEdge t m Y p) 0

/-- One axis component of the derivative of the radical edge function. -/
def edgeComponent (t : LineGroup → LineGroup → LineValues n) (m : unimodularLevi) (i : Fin 2) :
    LineValues n :=
  fun p => radicalEdgeDerivative t m p (Pi.single i 1)

/-- **The derivative edge.** -/
def derivativeEdge (t : LineGroup → LineGroup → LineValues n) (m : unimodularLevi) :
    BinaryAdelicGL → Binary.HomogeneousPoly (n + 1) :=
  fun h => lowerRadicalCoordinate n (fun i => lineVector (edgeComponent t m i) h)

/-- The action of the real Levi on functions `GL₂(𝔸) → Sym^{n+1}`. -/
def edgeAction (m : unimodularLevi) (F : BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)) :
    BinaryAdelicGL → Binary.HomogeneousPoly (n + 1) :=
  fun h => (((m : BinaryRealGL).val.det : ℝ) : ℂ) •
    binaryCoefficient n m (F (h * atInfinity (pivotConjugate (m : BinaryRealGL))))

/-! ### The cocycle law -/

theorem radicalEdge_mul {t : LineGroup → LineGroup → LineValues n} (cocycle : IsTwoCocycle t)
    (a b : unimodularLevi) (Y : Fin 2 → ℝ) :
    radicalEdge t (a * b) Y = radicalEdge t a Y +
      lineLeviElement a • radicalEdge t b (rowAction a Y) +
      (lineRadicalElement Y • t (lineLeviElement a) (lineLeviElement b) -
        t (lineLeviElement a) (lineLeviElement b)) := by
  unfold radicalEdge
  rw [lineLeviElement_mul, mixedEdgeFunction_mul cocycle, lineLevi_conj_radical, rowAction_apply]

theorem lineMatrix_lineLeviElement (m : unimodularLevi) :
    lineMatrix (lineLeviElement m) = planeLevi (m : BinaryRealGL) 1 := by
  rw [lineMatrix_apply]
  change lineRadicalMatrix 1 * _ = _
  rw [map_one, one_mul]
  rfl

theorem lineMatrix_lineRadicalElement (Y : Fin 2 → ℝ) :
    lineMatrix (lineRadicalElement Y) = lineRadicalMatrix (Multiplicative.ofAdd Y) := by
  rw [lineMatrix_apply]
  change _ * planeLevi ((1 : unimodularLevi) : BinaryRealGL) 1 = _
  rw [OneMemClass.coe_one, show planeLevi (1 : BinaryRealGL) 1 = 1 from (planeLeviHom ℝ).map_one,
    mul_one]
  rfl

theorem lineRadical_smul_apply (Y : Fin 2 → ℝ) (F : LineValues n) (h : BinaryAdelicGL)
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    (lineRadicalElement Y • F) (h, functional) = F (h, functional ∘ₗ
      realCoefficientComponent n trivialCharacter
        (lineRadicalMatrix (Multiplicative.ofAdd Y))) := by
  rw [lineValues_smul_apply]
  change F (h * atInfinity (pivotConjugate ((1 : unimodularLevi) : BinaryRealGL)), _) = _
  rw [OneMemClass.coe_one, pivotConjugate_one, atInfinity_one, mul_one,
    lineMatrix_lineRadicalElement]

/-- The derivative of the remainder term of the cocycle law along an axis. -/
theorem hasDerivAt_radical_remainder {w : LineValues n} (linear : LinearTests w) (i : Fin 2)
    (h : BinaryAdelicGL) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    HasDerivAt (fun s : ℝ => (lineRadicalElement (s • Pi.single i 1) • w - w) (h, functional))
      (functional (lowerShear n i (lineVector w h))) 0 := by
  have equality :
      (fun s : ℝ => (lineRadicalElement (s • Pi.single i 1) • w - w) (h, functional)) =
      fun s : ℝ => functional (realCoefficientComponent n trivialCharacter
        (lineRadicalMatrix (Multiplicative.ofAdd (s • Pi.single i 1))) (lineVector w h)) -
          functional (lineVector w h) := by
    funext s
    change (lineRadicalElement (s • Pi.single i 1) • w) (h, functional) - w (h, functional) = _
    rw [lineRadical_smul_apply, linear, linear, LinearMap.comp_apply]
  rw [equality]
  simpa using (hasDerivAt_coefficient_lowerAxis functional (lineVector w h) i).sub_const
    (functional (lineVector w h))

theorem rowAction_single (m : unimodularLevi) (i : Fin 2) :
    rowAction m (Pi.single i 1) = ∑ k, (m : BinaryRealGL).val i k • Pi.single k 1 := by
  funext j
  rw [rowAction_apply, Finset.sum_apply]
  simp [Matrix.vecMul, dotProduct, Pi.single_apply]

/-- The derivative components of the radical edge function satisfy the cocycle law. -/
theorem edgeComponent_mul {t : LineGroup → LineGroup → LineValues n} (cocycle : IsTwoCocycle t)
    (regular : EdgeRegular t) (a b : unimodularLevi) (i : Fin 2)
    (p : BinaryAdelicGL × (HomogeneousPoly n →ₗ[ℂ] ℂ)) :
    edgeComponent t (a * b) i p = edgeComponent t a i p +
      ∑ k, (((a : BinaryRealGL).val i k : ℝ) : ℂ) *
        (lineLeviElement a • edgeComponent t b k) p +
      p.2 (lowerShear n i (lineVector (t (lineLeviElement a) (lineLeviElement b)) p.1)) := by
  set w := t (lineLeviElement a) (lineLeviElement b)
  set φ : BinaryAdelicGL × (HomogeneousPoly n →ₗ[ℂ] ℂ) →
      BinaryAdelicGL × (HomogeneousPoly n →ₗ[ℂ] ℂ) :=
    fun q => (q.1 * atInfinity (pivotConjugate ((lineLeviElement a).right : BinaryRealGL)),
      q.2 ∘ₗ realCoefficientComponent n trivialCharacter (lineMatrix (lineLeviElement a)))
  have moved (F : LineValues n) : (lineLeviElement a • F) p = F (φ p) := rfl
  have whole : HasFDerivAt (fun Y => radicalEdge t (a * b) Y p)
      (radicalEdgeDerivative t (a * b) p) 0 :=
    (regular.edge_differentiable (a * b) p).hasFDerivAt
  have first : HasFDerivAt (fun Y => radicalEdge t a Y p) (radicalEdgeDerivative t a p) 0 :=
    (regular.edge_differentiable a p).hasFDerivAt
  have second : HasFDerivAt (fun Y => radicalEdge t b (rowAction a Y) (φ p))
      ((radicalEdgeDerivative t b (φ p)).comp (rowAction a)) 0 := by
    have outer : HasFDerivAt (fun Y => radicalEdge t b Y (φ p))
        (radicalEdgeDerivative t b (φ p)) (rowAction a 0) := by
      rw [map_zero]
      exact (regular.edge_differentiable b (φ p)).hasFDerivAt
    exact outer.comp (0 : Fin 2 → ℝ) (rowAction a).hasFDerivAt
  have remainder : HasFDerivAt (fun Y => (lineRadicalElement Y • w - w) p)
      (radicalEdgeDerivative t (a * b) p - radicalEdgeDerivative t a p -
        (radicalEdgeDerivative t b (φ p)).comp (rowAction a)) 0 := by
    have equality : (fun Y => (lineRadicalElement Y • w - w) p) = fun Y =>
        radicalEdge t (a * b) Y p - radicalEdge t a Y p -
          radicalEdge t b (rowAction a Y) (φ p) := by
      funext Y
      rw [radicalEdge_mul cocycle]
      change _ = (radicalEdge t a Y p + (lineLeviElement a • radicalEdge t b (rowAction a Y)) p +
        (lineRadicalElement Y • w - w) p) - radicalEdge t a Y p -
          radicalEdge t b (rowAction a Y) (φ p)
      rw [moved]
      ring
    rw [equality]
    exact (whole.sub first).sub second
  have line : HasDerivAt (fun s : ℝ => s • (Pi.single i 1 : Fin 2 → ℝ)) (Pi.single i 1) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const (Pi.single i 1 : Fin 2 → ℝ)
  have directional := remainder.comp_hasDerivAt_of_eq (0 : ℝ) line (by simp)
  have explicit := hasDerivAt_radical_remainder (regular.linear (lineLeviElement a)
    (lineLeviElement b)) i p.1 p.2
  have unique := directional.unique explicit
  simp only [_root_.sub_apply, ContinuousLinearMap.comp_apply] at unique
  unfold edgeComponent
  change radicalEdgeDerivative t (a * b) p (Pi.single i 1) = radicalEdgeDerivative t a p
    (Pi.single i 1) + ∑ k, (((a : BinaryRealGL).val i k : ℝ) : ℂ) *
      radicalEdgeDerivative t b (φ p) (Pi.single k 1) + _
  rw [← unique, rowAction_single, map_sum]
  simp only [map_smul, Complex.real_smul]
  ring

theorem lineLeviElement_smul_apply (m : unimodularLevi) {F : LineValues n} (hF : LinearTests F)
    (h : BinaryAdelicGL) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    (lineLeviElement m • F) (h, functional) = functional (realCoefficientComponent n
      trivialCharacter (planeLevi (m : BinaryRealGL) 1)
        (lineVector F (h * atInfinity (pivotConjugate (m : BinaryRealGL))))) := by
  rw [lineValues_smul_apply, hF, LinearMap.comp_apply, lineMatrix_lineLeviElement]
  rfl

/-- **The derivative edge is a one-cocycle of the real Levi.** -/
theorem derivativeEdge_mul {t : LineGroup → LineGroup → LineValues n} (cocycle : IsTwoCocycle t)
    (regular : EdgeRegular t) (a b : unimodularLevi) :
    derivativeEdge t (a * b) = derivativeEdge t a + edgeAction a (derivativeEdge t b) := by
  funext h
  set w := t (lineLeviElement a) (lineLeviElement b)
  set h' := h * atInfinity (pivotConjugate (a : BinaryRealGL))
  set C := realCoefficientComponent n trivialCharacter (planeLevi (a : BinaryRealGL) 1)
  have componentLinear (k : Fin 2) : LinearTests (edgeComponent t b k) :=
    linearTests_fderiv (regular.edge_linear b) (regular.edge_differentiable b) (Pi.single k 1)
  have vector (i : Fin 2) : lineVector (edgeComponent t (a * b) i) h =
      lineVector (edgeComponent t a i) h +
        ∑ k, (((a : BinaryRealGL).val i k : ℝ) : ℂ) • C (lineVector (edgeComponent t b k) h') +
        lowerShear n i (lineVector w h) := by
    apply (homogeneousBasis n).ext_elem
    intro j
    rw [← Module.Basis.coord_apply, ← Module.Basis.coord_apply, coord_lineVector,
      edgeComponent_mul cocycle regular a b i, map_add, map_add, map_sum, coord_lineVector]
    simp_rw [lineLeviElement_smul_apply a (componentLinear _), map_smul, smul_eq_mul]
    rfl
  change lowerRadicalCoordinate n _ = lowerRadicalCoordinate n _ + edgeAction a _ h
  have pairs : (fun i => lineVector (edgeComponent t (a * b) i) h) =
      (fun i => lineVector (edgeComponent t a i) h) +
        (fun i => ∑ k, (((a : BinaryRealGL).val i k : ℝ) : ℂ) •
          C (lineVector (edgeComponent t b k) h')) +
        (fun i => lowerShear n i (lineVector w h)) := by
    funext i
    rw [vector]
    rfl
  rw [pairs, map_add, map_add, lowerRadicalCoordinate_lowerShear, add_zero,
    lowerRadicalCoordinate_levi]
  rfl

end TernaryPeriodPolynomials.AnalyticClasses
