module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Plane.Core
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.TraceBilinear
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.FacePairingForm

@[expose] public section


/-!
# The plane face pairing `⟨ , ⟩_P` as a bilinear form on inner classes

Mirror (exchange of the line and plane sides) of `TraceDetects` (representative independence),
`TraceBilinear` and `FacePairingForm`: `traceValueP z w y = Σ_v planeValueP … v z w y` for a plane
cocycle `z` with edge primitive `w` and a line cocycle `y`, the bilinear form
`facePairingP n : innerClasses n .plane →ₗ innerClasses n .line →ₗ ℂ`, and its independence of all
choices of representatives and primitives (`pairingValue_eqP`). Nondegeneracy is not part of this
file.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.BoundaryDuality.TraceChains
open TernaryPeriodPolynomials.BoundaryDuality.L2Trace
  (traceDataL2 isBoundaryTrace_traceDataL2)

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Plane

/-- The value of the face pairing `⟨ , ⟩_Q` at a plane cocycle `z` with edge primitive `w` and a
line cocycle `y`: the sum over the two plane cusps of the local values. -/
def traceValueP {n : ℕ} (z : MaximalCycles n trivialCharacter .plane)
    (w : EdgeCochains n trivialCharacter 1) (y : MaximalCycles n trivialCharacter .line) : ℂ :=
  ∑ v : Fin 2, planeValueP traceDataL2 (dualityDataP n trivialCharacter) v z w y

/-- The trace of the boundary cup product is `traceValueP`, for any vertex primitive. -/
theorem trace_boundaryValue_eq_traceValueP {n : ℕ} {z : MaximalCycles n trivialCharacter .plane}
    {w : EdgeCochains n trivialCharacter 1} {y : MaximalCycles n trivialCharacter .line}
    {γ : (Fin 4 → RationalGL3) → Flags .plane → ℂ}
    (hγ : VertexPrimitiveP (dualityDataP n trivialCharacter) z y γ) :
    traceDataL2.trace (boundaryValueP (dualityDataP n trivialCharacter) w y γ) =
      traceValueP z w y := by
  rw [trace_eq_chainValueP traceDataL2 (dualityDataP n trivialCharacter) hγ]
  exact chainValue_eq_sumP traceDataL2 (dualityDataP n trivialCharacter) z w y

/-- **Representative independence of the face pairing.** If `z, z₀` are cohomologous, `y, y₀` are
cohomologous with `y₀` edge-exact, and `w, w₀` are edge primitives, the values agree. -/
theorem traceValue_eq_of_classesP {n : ℕ}
    {z z₀ : MaximalCycles n trivialCharacter .plane} {w w₀ : EdgeCochains n trivialCharacter 1}
    {y y₀ : MaximalCycles n trivialCharacter .line}
    (hw : EdgePrimitiveP z w) (hw₀ : EdgePrimitiveP z₀ w₀)
    (hz : classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) z =
      classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) z₀)
    (hy : classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) y =
      classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) y₀)
    (flat₀ : LineEdgeExactP y₀) :
    traceValueP z w y = traceValueP z₀ w₀ y₀ := by
  obtain ⟨γ, hγ⟩ := planeCupExact_unconditionalP (dualityDataP n trivialCharacter) z y
  obtain ⟨γ₀, hγ₀⟩ := planeCupExact_unconditionalP (dualityDataP n trivialCharacter) z₀ y₀
  rw [← trace_boundaryValue_eq_traceValueP hγ, ← trace_boundaryValue_eq_traceValueP hγ₀]
  exact trace_eqP (dualityDataP n trivialCharacter) isBoundaryTrace_traceDataL2 hw hγ hw₀ hγ₀
    hz hy flat₀


variable {n : ℕ}

theorem planeValue_add_leftP (v : Fin 2) (z z' : MaximalCycles n trivialCharacter .plane)
    (w w' : EdgeCochains n trivialCharacter 1) (y : MaximalCycles n trivialCharacter .line) :
    planeValueP traceDataL2 (dualityDataP n trivialCharacter) v (z + z') (w + w') y =
      planeValueP traceDataL2 (dualityDataP n trivialCharacter) v z w y +
        planeValueP traceDataL2 (dualityDataP n trivialCharacter) v z' w' y := by
  unfold planeValueP
  simp only [Submodule.coe_add, Pi.add_apply, map_add, LinearMap.add_apply,
    linearCombination_fun_add, Finset.sum_add_distrib]
  abel

theorem planeValue_smul_leftP (v : Fin 2) (a : ℂ) (z : MaximalCycles n trivialCharacter .plane)
    (w : EdgeCochains n trivialCharacter 1) (y : MaximalCycles n trivialCharacter .line) :
    planeValueP traceDataL2 (dualityDataP n trivialCharacter) v (a • z) (a • w) y =
      a * planeValueP traceDataL2 (dualityDataP n trivialCharacter) v z w y := by
  unfold planeValueP
  simp only [Submodule.coe_smul, Pi.smul_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
    linearCombination_fun_smul, ← Finset.mul_sum, mul_sub]

theorem planeValue_add_rightP (v : Fin 2) (z : MaximalCycles n trivialCharacter .plane)
    (w : EdgeCochains n trivialCharacter 1) (y y' : MaximalCycles n trivialCharacter .line) :
    planeValueP traceDataL2 (dualityDataP n trivialCharacter) v z w (y + y') =
      planeValueP traceDataL2 (dualityDataP n trivialCharacter) v z w y +
        planeValueP traceDataL2 (dualityDataP n trivialCharacter) v z w y' := by
  unfold planeValueP
  simp only [Submodule.coe_add, Pi.add_apply, map_add, linearCombination_fun_add,
    Finset.sum_add_distrib]
  abel

theorem planeValue_smul_rightP (v : Fin 2) (a : ℂ) (z : MaximalCycles n trivialCharacter .plane)
    (w : EdgeCochains n trivialCharacter 1) (y : MaximalCycles n trivialCharacter .line) :
    planeValueP traceDataL2 (dualityDataP n trivialCharacter) v z w (a • y) =
      a * planeValueP traceDataL2 (dualityDataP n trivialCharacter) v z w y := by
  unfold planeValueP
  simp only [Submodule.coe_smul, Pi.smul_apply, map_smul, smul_eq_mul,
    linearCombination_fun_smul, ← Finset.mul_sum, mul_sub]

theorem traceValue_add_leftP (z z' : MaximalCycles n trivialCharacter .plane)
    (w w' : EdgeCochains n trivialCharacter 1) (y : MaximalCycles n trivialCharacter .line) :
    traceValueP (z + z') (w + w') y = traceValueP z w y + traceValueP z' w' y := by
  unfold traceValueP
  simp only [planeValue_add_leftP, Finset.sum_add_distrib]

theorem traceValue_smul_leftP (a : ℂ) (z : MaximalCycles n trivialCharacter .plane)
    (w : EdgeCochains n trivialCharacter 1) (y : MaximalCycles n trivialCharacter .line) :
    traceValueP (a • z) (a • w) y = a * traceValueP z w y := by
  unfold traceValueP
  simp only [planeValue_smul_leftP, Finset.mul_sum]

theorem traceValue_add_rightP (z : MaximalCycles n trivialCharacter .plane)
    (w : EdgeCochains n trivialCharacter 1) (y y' : MaximalCycles n trivialCharacter .line) :
    traceValueP z w (y + y') = traceValueP z w y + traceValueP z w y' := by
  unfold traceValueP
  simp only [planeValue_add_rightP, Finset.sum_add_distrib]

theorem traceValue_smul_rightP (a : ℂ) (z : MaximalCycles n trivialCharacter .plane)
    (w : EdgeCochains n trivialCharacter 1) (y : MaximalCycles n trivialCharacter .line) :
    traceValueP z w (a • y) = a * traceValueP z w y := by
  unfold traceValueP
  simp only [planeValue_smul_rightP, Finset.mul_sum]


theorem edgePrimitive_addP {z z' : MaximalCycles n trivialCharacter .plane}
    {w w' : EdgeCochains n trivialCharacter 1} (hw : EdgePrimitiveP z w)
    (hw' : EdgePrimitiveP z' w') : EdgePrimitiveP (z + z') (w + w') := by
  intro x e
  have e1 : (z + z').val.val x (endpoint .plane e) =
      z.val.val x (endpoint .plane e) + z'.val.val x (endpoint .plane e) := rfl
  have e2 : differentialOneRaw (w + w').val x e =
      differentialOneRaw w.val x e + differentialOneRaw w'.val x e := by
    change (w.val ![x 1, x 2] e + w'.val ![x 1, x 2] e) -
        (w.val ![x 0, x 2] e + w'.val ![x 0, x 2] e) +
        (w.val ![x 0, x 1] e + w'.val ![x 0, x 1] e) =
      (w.val ![x 1, x 2] e - w.val ![x 0, x 2] e + w.val ![x 0, x 1] e) +
        (w'.val ![x 1, x 2] e - w'.val ![x 0, x 2] e + w'.val ![x 0, x 1] e)
    abel
  rw [e1, e2, hw x e, hw' x e]

theorem edgePrimitive_smulP (c : ℂ) {z : MaximalCycles n trivialCharacter .plane}
    {w : EdgeCochains n trivialCharacter 1} (hw : EdgePrimitiveP z w) :
    EdgePrimitiveP (c • z) (c • w) := by
  intro x e
  have e1 : (c • z).val.val x (endpoint .plane e) = c • z.val.val x (endpoint .plane e) := rfl
  have e2 : differentialOneRaw (c • w).val x e = c • differentialOneRaw w.val x e := by
    change c • w.val ![x 1, x 2] e - c • w.val ![x 0, x 2] e + c • w.val ![x 0, x 1] e =
      c • (w.val ![x 1, x 2] e - w.val ![x 0, x 2] e + w.val ![x 0, x 1] e)
    rw [smul_add, smul_sub]
  rw [e1, e2, hw x e]

open scoped Classical in
/-- The raw value of the face pairing: the trace pairing at canonical representatives of inner
classes, and `0` otherwise. -/
def pairingValueP (n : ℕ) (b : StratumH2 n trivialCharacter .plane)
    (ξ : StratumH2 n trivialCharacter .line) : ℂ :=
  if h : InnerBoundary n trivialCharacter .plane b ∧ InnerBoundary n trivialCharacter .line ξ then
    traceValueP (Classical.choose h.1) (Classical.choose (Classical.choose_spec h.1).2)
      (Classical.choose h.2)
  else 0

/-- **The face pairing is independent of all choices.** -/
theorem pairingValue_eqP {b : StratumH2 n trivialCharacter .plane}
    {ξ : StratumH2 n trivialCharacter .line} (hb : InnerBoundary n trivialCharacter .plane b)
    (hξ : InnerBoundary n trivialCharacter .line ξ)
    {z : MaximalCycles n trivialCharacter .plane} {w : EdgeCochains n trivialCharacter 1}
    {y : MaximalCycles n trivialCharacter .line}
    (hz : classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) z = b)
    (hw : EdgePrimitiveP z w)
    (hy : classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) y = ξ) :
    pairingValueP n b ξ = traceValueP z w y := by
  have h : InnerBoundary n trivialCharacter .plane b ∧ InnerBoundary n trivialCharacter .line ξ :=
    ⟨hb, hξ⟩
  unfold pairingValueP
  rw [dite_eq_left h]
  have spec1 := Classical.choose_spec h.1
  have spec2 := Classical.choose_spec h.2
  have spec3 := Classical.choose_spec spec1.2
  exact (traceValue_eq_of_classesP hw (fun x e => spec3 x e)
    (hz.trans spec1.1.symm) (hy.trans spec2.1.symm) spec2.2).symm

/-- The face pairing, as a bilinear form on inner classes. -/
def facePairingP (n : ℕ) :
    innerClasses n .plane →ₗ[ℂ] innerClasses n .line →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun b ξ => pairingValueP n b.val ξ.val)
    (by
      rintro ⟨b₁, ⟨z₁, hz₁, u₁, hu₁⟩⟩ ⟨b₂, ⟨z₂, hz₂, u₂, hu₂⟩⟩ ⟨ξ, hξ⟩
      have hξ' : InnerBoundary n trivialCharacter .line ξ := hξ
      obtain ⟨y, hy, _⟩ := hξ'
      have hw₁ : EdgePrimitiveP z₁ u₁ := fun x e => hu₁ x e
      have hw₂ : EdgePrimitiveP z₂ u₂ := fun x e => hu₂ x e
      have hb₁ : InnerBoundary n trivialCharacter .plane b₁ := ⟨z₁, hz₁, u₁, hu₁⟩
      have hb₂ : InnerBoundary n trivialCharacter .plane b₂ := ⟨z₂, hz₂, u₂, hu₂⟩
      have hξ' : InnerBoundary n trivialCharacter .line ξ := hξ
      change pairingValueP n (b₁ + b₂) ξ = pairingValueP n b₁ ξ + pairingValueP n b₂ ξ
      rw [pairingValue_eqP (b := b₁ + b₂) ((innerClasses n .plane).add_mem hb₁ hb₂) hξ'
        (z := z₁ + z₂) (w := u₁ + u₂) (y := y) (by rw [map_add, hz₁, hz₂])
        (edgePrimitive_addP hw₁ hw₂) hy,
        pairingValue_eqP hb₁ hξ' hz₁ hw₁ hy, pairingValue_eqP hb₂ hξ' hz₂ hw₂ hy,
        traceValue_add_leftP])
    (by
      rintro c ⟨b, ⟨z, hz, u, hu⟩⟩ ⟨ξ, hξ⟩
      have hw : EdgePrimitiveP z u := fun x e => hu x e
      have hb : InnerBoundary n trivialCharacter .plane b := ⟨z, hz, u, hu⟩
      have hξ' : InnerBoundary n trivialCharacter .line ξ := hξ
      obtain ⟨y, hy, _⟩ := hξ'
      change pairingValueP n (c • b) ξ = c * pairingValueP n b ξ
      rw [pairingValue_eqP (b := c • b) ((innerClasses n .plane).smul_mem c hb) hξ
        (z := c • z) (w := c • u) (y := y) (by rw [map_smul, hz]) (edgePrimitive_smulP c hw) hy,
        pairingValue_eqP hb hξ hz hw hy, traceValue_smul_leftP])
    (by
      rintro ⟨b, ⟨z, hz, u, hu⟩⟩ ⟨ξ₁, ⟨y₁, hy₁, s₁, hs₁⟩⟩ ⟨ξ₂, ⟨y₂, hy₂, s₂, hs₂⟩⟩
      have hw : EdgePrimitiveP z u := fun x e => hu x e
      have hb : InnerBoundary n trivialCharacter .plane b := ⟨z, hz, u, hu⟩
      have hξ₁ : InnerBoundary n trivialCharacter .line ξ₁ := ⟨y₁, hy₁, s₁, hs₁⟩
      have hξ₂ : InnerBoundary n trivialCharacter .line ξ₂ := ⟨y₂, hy₂, s₂, hs₂⟩
      change pairingValueP n b (ξ₁ + ξ₂) = pairingValueP n b ξ₁ + pairingValueP n b ξ₂
      rw [pairingValue_eqP hb ((innerClasses n .line).add_mem hξ₁ hξ₂) hz hw
        (y := y₁ + y₂) (by rw [map_add, hy₁, hy₂]),
        pairingValue_eqP hb hξ₁ hz hw hy₁, pairingValue_eqP hb hξ₂ hz hw hy₂,
        traceValue_add_rightP])
    (by
      rintro c ⟨b, ⟨z, hz, u, hu⟩⟩ ⟨ξ, ⟨y, hy, s, hs⟩⟩
      have hw : EdgePrimitiveP z u := fun x e => hu x e
      have hb : InnerBoundary n trivialCharacter .plane b := ⟨z, hz, u, hu⟩
      have hξ : InnerBoundary n trivialCharacter .line ξ := ⟨y, hy, s, hs⟩
      change pairingValueP n b (c • ξ) = c * pairingValueP n b ξ
      rw [pairingValue_eqP hb ((innerClasses n .line).smul_mem c hξ) hz hw
        (y := c • y) (by rw [map_smul, hy]),
        pairingValue_eqP hb hξ hz hw hy, traceValue_smul_rightP])

/-- The face pairing at canonical data is the trace of any choice of representatives. -/
theorem facePairing_apply_eqP {b : innerClasses n .plane} {ξ : innerClasses n .line}
    {z : MaximalCycles n trivialCharacter .plane} {w : EdgeCochains n trivialCharacter 1}
    {y : MaximalCycles n trivialCharacter .line}
    (hz : classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) z = b.val)
    (hw : EdgePrimitiveP z w)
    (hy : classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) y = ξ.val) :
    facePairingP n b ξ = traceValueP z w y :=
  pairingValue_eqP b.property ξ.property hz hw hy


end TernaryPeriodPolynomials.Argument.FacePairingFull.Plane
