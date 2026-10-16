module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.TraceBilinear
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.LineClassesVanishZero

@[expose] public section


/-!
# The face pairing `⟨ , ⟩_Q` as a bilinear form on inner classes, and its zero left kernel

`innerClasses n side` is the subspace `𝒞(E)` of classes of `StratumH2 n trivialCharacter side` with
zero restriction to every complete flag (`InnerBoundary`; mixed cuspidal classes, see
`InnerBoundaryCusps`). `facePairing n : innerClasses n .line →ₗ innerClasses n .plane →ₗ ℂ` is the
trace of the boundary cup product, which is independent of every choice of representatives and
primitives (`pairingValue_eq`) and bilinear. Its left kernel is zero for every `n`
(`facePairing_left_nondegenerate`): the target `face_pairing_perfect` is the (formally weaker)
statement that for `b ≠ 0` some partner has a non-exact boundary cup product.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.Spectral.CuspReduction (cuspRes eq_zero_iff_cuspRes)
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.Argument.FacePairing

namespace TernaryPeriodPolynomials.Argument.FacePairingFull

variable {n : ℕ}

/-- The subspace of inner (mixed cuspidal) classes of a side. -/
def innerClasses (n : ℕ) (side : Side) : Submodule ℂ (StratumH2 n trivialCharacter side) where
  carrier := {a | InnerBoundary n trivialCharacter side a}
  zero_mem' := ⟨0, map_zero _, 0, fun x e => by
    rw [map_zero]
    rfl⟩
  add_mem' := by
    rintro a b ⟨z, hz, u, hu⟩ ⟨z', hz', u', hu'⟩
    refine ⟨z + z', by rw [map_add, hz, hz'], u + u', fun x e => ?_⟩
    have e1 : (z + z').val.val x (endpoint side e) =
        z.val.val x (endpoint side e) + z'.val.val x (endpoint side e) := rfl
    have e2 : (differentialOne rationalLevel
        (functionRepresentation (rationalCoefficientComponent n trivialCharacter) Edges)
          (u + u')).val x e =
        (differentialOne rationalLevel
          (functionRepresentation (rationalCoefficientComponent n trivialCharacter) Edges)
            u).val x e +
        (differentialOne rationalLevel
          (functionRepresentation (rationalCoefficientComponent n trivialCharacter) Edges)
            u').val x e := by
      rw [map_add]
      rfl
    rw [e1, e2, hu x e, hu' x e]
  smul_mem' := by
    rintro c a ⟨z, hz, u, hu⟩
    refine ⟨c • z, by rw [map_smul, hz], c • u, fun x e => ?_⟩
    have e1 : (c • z).val.val x (endpoint side e) = c • z.val.val x (endpoint side e) := rfl
    have e2 : (differentialOne rationalLevel
        (functionRepresentation (rationalCoefficientComponent n trivialCharacter) Edges)
          (c • u)).val x e =
        c • (differentialOne rationalLevel
          (functionRepresentation (rationalCoefficientComponent n trivialCharacter) Edges)
            u).val x e := by
      rw [map_smul]
      rfl
    rw [e1, e2, hu x e]

theorem edgePrimitive_add {z z' : MaximalCycles n trivialCharacter .line}
    {w w' : EdgeCochains n trivialCharacter 1} (hw : EdgePrimitive z w)
    (hw' : EdgePrimitive z' w') : EdgePrimitive (z + z') (w + w') := by
  intro x e
  have e1 : (z + z').val.val x (endpoint .line e) =
      z.val.val x (endpoint .line e) + z'.val.val x (endpoint .line e) := rfl
  have e2 : differentialOneRaw (w + w').val x e =
      differentialOneRaw w.val x e + differentialOneRaw w'.val x e := by
    change (w.val ![x 1, x 2] e + w'.val ![x 1, x 2] e) -
        (w.val ![x 0, x 2] e + w'.val ![x 0, x 2] e) +
        (w.val ![x 0, x 1] e + w'.val ![x 0, x 1] e) =
      (w.val ![x 1, x 2] e - w.val ![x 0, x 2] e + w.val ![x 0, x 1] e) +
        (w'.val ![x 1, x 2] e - w'.val ![x 0, x 2] e + w'.val ![x 0, x 1] e)
    abel
  rw [e1, e2, hw x e, hw' x e]

theorem edgePrimitive_smul (c : ℂ) {z : MaximalCycles n trivialCharacter .line}
    {w : EdgeCochains n trivialCharacter 1} (hw : EdgePrimitive z w) :
    EdgePrimitive (c • z) (c • w) := by
  intro x e
  have e1 : (c • z).val.val x (endpoint .line e) = c • z.val.val x (endpoint .line e) := rfl
  have e2 : differentialOneRaw (c • w).val x e = c • differentialOneRaw w.val x e := by
    change c • w.val ![x 1, x 2] e - c • w.val ![x 0, x 2] e + c • w.val ![x 0, x 1] e =
      c • (w.val ![x 1, x 2] e - w.val ![x 0, x 2] e + w.val ![x 0, x 1] e)
    rw [smul_add, smul_sub]
  rw [e1, e2, hw x e]

open scoped Classical in
/-- The raw value of the face pairing: the trace pairing at canonical representatives of inner
classes, and `0` otherwise. -/
def pairingValue (n : ℕ) (b : StratumH2 n trivialCharacter .line)
    (ξ : StratumH2 n trivialCharacter .plane) : ℂ :=
  if h : InnerBoundary n trivialCharacter .line b ∧ InnerBoundary n trivialCharacter .plane ξ then
    traceValue (Classical.choose h.1) (Classical.choose (Classical.choose_spec h.1).2)
      (Classical.choose h.2)
  else 0

/-- **The face pairing is independent of all choices.** -/
theorem pairingValue_eq {b : StratumH2 n trivialCharacter .line}
    {ξ : StratumH2 n trivialCharacter .plane} (hb : InnerBoundary n trivialCharacter .line b)
    (hξ : InnerBoundary n trivialCharacter .plane ξ)
    {z : MaximalCycles n trivialCharacter .line} {w : EdgeCochains n trivialCharacter 1}
    {y : MaximalCycles n trivialCharacter .plane}
    (hz : classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z = b)
    (hw : EdgePrimitive z w)
    (hy : classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y = ξ) :
    pairingValue n b ξ = traceValue z w y := by
  have h : InnerBoundary n trivialCharacter .line b ∧ InnerBoundary n trivialCharacter .plane ξ :=
    ⟨hb, hξ⟩
  unfold pairingValue
  rw [dite_eq_left h]
  have spec1 := Classical.choose_spec h.1
  have spec2 := Classical.choose_spec h.2
  have spec3 := Classical.choose_spec spec1.2
  exact (traceValue_eq_of_classes hw (fun x e => spec3 x e)
    (hz.trans spec1.1.symm) (hy.trans spec2.1.symm) spec2.2).symm

/-- The face pairing, as a bilinear form on inner classes. -/
def facePairing (n : ℕ) :
    innerClasses n .line →ₗ[ℂ] innerClasses n .plane →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun b ξ => pairingValue n b.val ξ.val)
    (by
      rintro ⟨b₁, ⟨z₁, hz₁, u₁, hu₁⟩⟩ ⟨b₂, ⟨z₂, hz₂, u₂, hu₂⟩⟩ ⟨ξ, hξ⟩
      have hξ' : InnerBoundary n trivialCharacter .plane ξ := hξ
      obtain ⟨y, hy, _⟩ := hξ'
      have hw₁ : EdgePrimitive z₁ u₁ := fun x e => hu₁ x e
      have hw₂ : EdgePrimitive z₂ u₂ := fun x e => hu₂ x e
      have hb₁ : InnerBoundary n trivialCharacter .line b₁ := ⟨z₁, hz₁, u₁, hu₁⟩
      have hb₂ : InnerBoundary n trivialCharacter .line b₂ := ⟨z₂, hz₂, u₂, hu₂⟩
      have hξ' : InnerBoundary n trivialCharacter .plane ξ := hξ
      change pairingValue n (b₁ + b₂) ξ = pairingValue n b₁ ξ + pairingValue n b₂ ξ
      rw [pairingValue_eq (b := b₁ + b₂) ((innerClasses n .line).add_mem hb₁ hb₂) hξ'
        (z := z₁ + z₂) (w := u₁ + u₂) (y := y) (by rw [map_add, hz₁, hz₂])
        (edgePrimitive_add hw₁ hw₂) hy,
        pairingValue_eq hb₁ hξ' hz₁ hw₁ hy, pairingValue_eq hb₂ hξ' hz₂ hw₂ hy,
        traceValue_add_left])
    (by
      rintro c ⟨b, ⟨z, hz, u, hu⟩⟩ ⟨ξ, hξ⟩
      have hw : EdgePrimitive z u := fun x e => hu x e
      have hb : InnerBoundary n trivialCharacter .line b := ⟨z, hz, u, hu⟩
      have hξ' : InnerBoundary n trivialCharacter .plane ξ := hξ
      obtain ⟨y, hy, _⟩ := hξ'
      change pairingValue n (c • b) ξ = c * pairingValue n b ξ
      rw [pairingValue_eq (b := c • b) ((innerClasses n .line).smul_mem c hb) hξ
        (z := c • z) (w := c • u) (y := y) (by rw [map_smul, hz]) (edgePrimitive_smul c hw) hy,
        pairingValue_eq hb hξ hz hw hy, traceValue_smul_left])
    (by
      rintro ⟨b, ⟨z, hz, u, hu⟩⟩ ⟨ξ₁, ⟨y₁, hy₁, s₁, hs₁⟩⟩ ⟨ξ₂, ⟨y₂, hy₂, s₂, hs₂⟩⟩
      have hw : EdgePrimitive z u := fun x e => hu x e
      have hb : InnerBoundary n trivialCharacter .line b := ⟨z, hz, u, hu⟩
      have hξ₁ : InnerBoundary n trivialCharacter .plane ξ₁ := ⟨y₁, hy₁, s₁, hs₁⟩
      have hξ₂ : InnerBoundary n trivialCharacter .plane ξ₂ := ⟨y₂, hy₂, s₂, hs₂⟩
      change pairingValue n b (ξ₁ + ξ₂) = pairingValue n b ξ₁ + pairingValue n b ξ₂
      rw [pairingValue_eq hb ((innerClasses n .plane).add_mem hξ₁ hξ₂) hz hw
        (y := y₁ + y₂) (by rw [map_add, hy₁, hy₂]),
        pairingValue_eq hb hξ₁ hz hw hy₁, pairingValue_eq hb hξ₂ hz hw hy₂,
        traceValue_add_right])
    (by
      rintro c ⟨b, ⟨z, hz, u, hu⟩⟩ ⟨ξ, ⟨y, hy, s, hs⟩⟩
      have hw : EdgePrimitive z u := fun x e => hu x e
      have hb : InnerBoundary n trivialCharacter .line b := ⟨z, hz, u, hu⟩
      have hξ : InnerBoundary n trivialCharacter .plane ξ := ⟨y, hy, s, hs⟩
      change pairingValue n b (c • ξ) = c * pairingValue n b ξ
      rw [pairingValue_eq hb ((innerClasses n .plane).smul_mem c hξ) hz hw
        (y := c • y) (by rw [map_smul, hy]),
        pairingValue_eq hb hξ hz hw hy, traceValue_smul_right])

/-- The face pairing at canonical data is the trace of any choice of representatives. -/
theorem facePairing_apply_eq {b : innerClasses n .line} {ξ : innerClasses n .plane}
    {z : MaximalCycles n trivialCharacter .line} {w : EdgeCochains n trivialCharacter 1}
    {y : MaximalCycles n trivialCharacter .plane}
    (hz : classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z = b.val)
    (hw : EdgePrimitive z w)
    (hy : classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y = ξ.val) :
    facePairing n b ξ = traceValue z w y :=
  pairingValue_eq b.property ξ.property hz hw hy

end TernaryPeriodPolynomials.Argument.FacePairingFull
