module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs.CuspidalBoundary
public import TernaryPeriodPolynomials.GroupCohomology.Relative.Stabilizer.Coordinates
public import TernaryPeriodPolynomials.Building.ModThreeGoodAction
public import TernaryPeriodPolynomials.Building.Good.Building

@[expose] public section


/-!
# `K† = B₃ K B₃⁻¹`, `e₃* B₃ = ℓ`, `T† = B₃ T↑`

Formalized by Claude Sonnet 5.5.

With the paper's `R₃ = [[1,0,0],[0,1,0],[-1,-1,1]]`, `B₃ = R₃⁻¹` and `ℓ = (1,1,1)`:

* `R3_mul_B3`, `B3_eq_inv_R3`; `lastRow_vecMul_B3`: `e₃* B₃ = ℓ` (over `ℤ`, and modulo three).
* `mem_arithmeticLevel_iff`: `g ∈ K†` (the Lean `GeneralEisenstein.arithmeticLevel`, defined directly by `e₃* g ≡ e₃* mod 3`) iff `B₃⁻¹ g B₃ ∈ K` (`K` = `TernaryPoly.ModThreeGoodAction.K`, defined by `ℓ k ≡ ℓ mod 3`); `arithmeticLevel_eq_conj`: `arithmeticLevel = B₃ K B₃⁻¹` as subgroups of `GL₃(ℤ)`; `conj_fixes_lastRow`: the paper's derivation, `e₃* (B₃ k B₃⁻¹) ≡ e₃*`.
* `rationalLevel_eq_conj`: the rational image `rationalLevel` is the `B₃`-conjugate of the rational image of `K`.
* `K3_eq_arithmeticLevel`: the Section-5 group `RelativeStabilizerCoordinates.K3` equals `arithmeticLevel`.
* `good3_map_B3_iff`, `graphIso_B3`: `T† = B₃ T↑`: a rational subspace `B₃ L` has an integral vector with last coordinate `≢ 0 (mod 3)` iff `L` has one with coordinate sum `≢ 0`, and `B₃` induces an isomorphism of incidence graphs `T↑ ≅ T†` (`T†` the graph of `Good3` vertices).
-/

open Matrix

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Identities

open GeneralEisenstein

/-- The paper's `R₃ = [[1,0,0],[0,1,0],[-1,-1,1]]`. -/
def R3 : IntegralGL3 :=
  Matrix.GeneralLinearGroup.mk'' !![1, 0, 0; 0, 1, 0; -1, -1, 1] (by
    rw [Matrix.det_fin_three]; simp)

/-- The paper's `B₃ = R₃⁻¹ = [[1,0,0],[0,1,0],[1,1,1]]`. -/
def B3 : IntegralGL3 :=
  Matrix.GeneralLinearGroup.mk'' !![1, 0, 0; 0, 1, 0; 1, 1, 1] (by
    rw [Matrix.det_fin_three]; simp)

theorem R3_val : (R3 : Matrix (Fin 3) (Fin 3) ℤ) = !![1, 0, 0; 0, 1, 0; -1, -1, 1] :=
  Matrix.GeneralLinearGroup.val_mk'' _ _

theorem B3_val : (B3 : Matrix (Fin 3) (Fin 3) ℤ) = !![1, 0, 0; 0, 1, 0; 1, 1, 1] :=
  Matrix.GeneralLinearGroup.val_mk'' _ _

theorem R3_mul_B3 : R3 * B3 = 1 := by
  apply Units.ext
  rw [Units.val_mul, R3_val, B3_val, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem B3_eq_inv_R3 : B3 = R3⁻¹ := eq_inv_of_mul_eq_one_right R3_mul_B3

theorem lastRow_vecMul_B3_int : (Pi.single 2 1 : Fin 3 → ℤ) ᵥ* (B3 : Matrix (Fin 3) (Fin 3) ℤ) = fun _ => 1 := by
  rw [B3_val]
  funext j
  fin_cases j <;> simp [Matrix.vecMul, dotProduct, Pi.single_apply]

/-- **`e₃* B₃ = ℓ`** modulo three: the covector `e₃* = (0,0,1)` times `B₃` is `ℓ = (1,1,1)`. -/
theorem lastRow_vecMul_B3 :
    lastRow ᵥ* (reductionThree B3 : Matrix (Fin 3) (Fin 3) (ZMod 3)) = TernaryPoly.ModThreeGoodAction.fixedRow := by
  funext j
  fin_cases j <;> simp [lastRow, reductionThree, TernaryPoly.ModThreeGoodAction.fixedRow, Matrix.vecMul, dotProduct,
    Pi.single_apply, Matrix.GeneralLinearGroup.map_apply, B3_val]

theorem vecMul_unit_cancel (u : GeneralLinearGroup (Fin 3) (ZMod 3)) (x y : Fin 3 → ZMod 3) :
    x ᵥ* (u : Matrix (Fin 3) (Fin 3) (ZMod 3)) = y ᵥ* (u : Matrix (Fin 3) (Fin 3) (ZMod 3)) ↔ x = y := by
  constructor
  · intro h
    have := congrArg (fun z => z ᵥ* ((u⁻¹ : GeneralLinearGroup (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3))) h
    have h1 : (u : Matrix (Fin 3) (Fin 3) (ZMod 3)) *
        ((u⁻¹ : GeneralLinearGroup (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, h1, Matrix.vecMul_one, Matrix.vecMul_one] at this
    exact this
  · rintro rfl; rfl

/-- **`K† = B₃ K B₃⁻¹`, elementwise:** `g` fixes `e₃*` modulo three iff `B₃⁻¹ g B₃` fixes `ℓ = (1,1,1)` modulo three. -/
theorem mem_arithmeticLevel_iff (g : IntegralGL3) :
    g ∈ arithmeticLevel ↔ B3⁻¹ * g * B3 ∈ TernaryPoly.ModThreeGoodAction.K := by
  rw [TernaryPoly.ModThreeGoodAction.mem_K]
  change lastRow ᵥ* ((reductionThree g : GeneralLinearGroup (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) = lastRow ↔ _
  have hb := lastRow_vecMul_B3
  have e : (TernaryPoly.ModThreeGoodAction.reduction (B3⁻¹ * g * B3) : GeneralLinearGroup (Fin 3) (ZMod 3)) =
      (reductionThree B3)⁻¹ * reductionThree g * reductionThree B3 := by
    simp [TernaryPoly.ModThreeGoodAction.reduction, reductionThree]
  rw [e, Units.val_mul, Units.val_mul, ← hb]
  set b := reductionThree B3 with hbdef
  set G := reductionThree g with hGdef
  have h1 : (b : Matrix (Fin 3) (Fin 3) (ZMod 3)) *
      ((b⁻¹ : GeneralLinearGroup (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have key : lastRow ᵥ* (b : Matrix (Fin 3) (Fin 3) (ZMod 3)) ᵥ*
      ((b⁻¹ : GeneralLinearGroup (Fin 3) (ZMod 3)) * G * b : Matrix (Fin 3) (Fin 3) (ZMod 3)) =
      (lastRow ᵥ* (G : Matrix (Fin 3) (Fin 3) (ZMod 3))) ᵥ* (b : Matrix (Fin 3) (Fin 3) (ZMod 3)) := by
    rw [Matrix.vecMul_vecMul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.vecMul_vecMul]
  rw [key]
  exact (vecMul_unit_cancel b _ _).symm

/-- **`K† = B₃ K B₃⁻¹`** as subgroups of `GL₃(ℤ)`: the Lean `arithmeticLevel` (defined by `e₃* g ≡ e₃* mod 3`) is the `B₃`-conjugate of `K`. -/
theorem arithmeticLevel_eq_conj :
    arithmeticLevel = TernaryPoly.ModThreeGoodAction.K.map (MulAut.conj B3).toMonoidHom := by
  ext g
  rw [mem_arithmeticLevel_iff, Subgroup.mem_map]
  constructor
  · intro h
    refine ⟨B3⁻¹ * g * B3, h, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]
  · rintro ⟨k, hk, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hk

/-- **The paper's derivation**: `K†` fixes `e₃*` modulo three, since `e₃* (B₃ k B₃⁻¹) = ℓ k B₃⁻¹ = ℓ B₃⁻¹ = e₃*` for `k ∈ K`. -/
theorem conj_fixes_lastRow (k : IntegralGL3) (hk : k ∈ TernaryPoly.ModThreeGoodAction.K) :
    lastRow ᵥ* ((reductionThree (B3 * k * B3⁻¹) : GeneralLinearGroup (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) =
      lastRow := by
  have h : B3 * k * B3⁻¹ ∈ arithmeticLevel := by
    rw [arithmeticLevel_eq_conj]
    exact ⟨k, hk, by simp [MulAut.conj_apply]⟩
  exact h

/-- `K†` fixes `e₃*` modulo three (the definition of the Lean group, matching the paper's conjugate). -/
theorem arithmeticLevel_fixes_lastRow (g : IntegralGL3) (hg : g ∈ arithmeticLevel) :
    lastRow ᵥ* ((reductionThree g : GeneralLinearGroup (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) = lastRow := hg

/-- The Section-5 group `K3` of the stabilizer computations is the Lean `K†`. -/
theorem K3_eq_arithmeticLevel : TernaryPoly.RelativeStabilizerCoordinates.K3 = arithmeticLevel := by
  ext g
  have hv : (![0, 0, 1] : Fin 3 → ZMod 3) = lastRow := by
    funext i; fin_cases i <;> simp [lastRow]
  change Matrix.vecMul (![0,0,1] : Fin 3 → ZMod 3) (TernaryPoly.ModThreeGoodAction.reduction g).val = ![0,0,1] ↔
    lastRow ᵥ* (reductionThree g).val = lastRow
  rw [hv]
  rfl

/-- **The rational image**: `rationalLevel` (the image of `K†` in `GL₃(ℚ)`) is the `B₃`-conjugate of the rational image of `K`. -/
theorem rationalLevel_eq_conj :
    rationalLevel = (TernaryPoly.ModThreeGoodAction.K.map (GeneralLinearGroup.map (Int.castRingHom ℚ))).map
      (MulAut.conj (GeneralLinearGroup.map (Int.castRingHom ℚ) B3)).toMonoidHom := by
  unfold rationalLevel rationalInclusion
  rw [MonoidHom.range_comp, Subgroup.range_subtype, arithmeticLevel_eq_conj, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext k
  simp [MulAut.conj_apply]

section Building

open TernaryPoly TernaryPoly.ModThreeGoodAction TernaryPoly.GoodIncidenceConnected
open TernaryPoly.RelativeStabilizerCoordinates (Good3)

theorem rep_rationalVector (g : IntegralGL) (v : IntegralVector) :
    rationalRepresentation g (rationalVector v) = rationalVector ((g : Matrix (Fin 3) (Fin 3) ℤ).mulVec v) := by
  funext i
  simp [rationalRepresentation, rationalVector, Matrix.mulVec, dotProduct]

theorem B3_mulVec_two (v : IntegralVector) :
    ((B3 : Matrix (Fin 3) (Fin 3) ℤ).mulVec v) 2 = v 0 + v 1 + v 2 := by
  simp [B3_val, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem R3_mulVec_sum (w : IntegralVector) :
    ∑ i, ((R3 : Matrix (Fin 3) (Fin 3) ℤ).mulVec w) i = w 2 := by
  simp [R3_val, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

/-- **`T† = B₃ T↑`, vertexwise**: a rational subspace `B₃ L` contains an integral vector with last coordinate `≢ 0 (mod 3)`
(good for `T†`) iff `L` contains an integral vector with coordinate sum `≢ 0 (mod 3)` (good for `T↑`). -/
theorem good3_map_B3_iff (L : Submodule ℚ (Fin 3 → ℚ)) :
    Good3 (L.map (rationalRepresentation B3).toLinearMap) ↔ Good L := by
  constructor
  · rintro ⟨w, hw, hw2⟩
    obtain ⟨x, hx, hxw⟩ := Submodule.mem_map.mp hw
    refine ⟨(R3 : Matrix (Fin 3) (Fin 3) ℤ).mulVec w, ?_, ?_⟩
    · rw [← rep_rationalVector]
      have : rationalRepresentation R3 (rationalVector w) = x := by
        rw [← hxw]
        change rationalRepresentation R3 (rationalRepresentation B3 x) = x
        rw [← LinearEquiv.mul_apply, ← map_mul, R3_mul_B3, map_one]
        rfl
      rw [this]; exact hx
    · have h' : ∑ i, ((((R3 : Matrix (Fin 3) (Fin 3) ℤ).mulVec w) i : ℤ) : ZMod 3) = (w 2 : ZMod 3) := by
        rw [← Int.cast_sum, R3_mulVec_sum]
      rw [h']
      exact hw2
  · rintro ⟨v, hv, hs⟩
    refine ⟨(B3 : Matrix (Fin 3) (Fin 3) ℤ).mulVec v, ?_, ?_⟩
    · rw [← rep_rationalVector]
      exact Submodule.mem_map.mpr ⟨_, hv, rfl⟩
    · rw [B3_mulVec_two]
      simpa [Fin.sum_univ_three] using hs

section GraphIso

variable (G G' : Submodule ℚ (Fin 3 → ℚ) → Prop) (e : Submodule ℚ (Fin 3 → ℚ) ≃o Submodule ℚ (Fin 3 → ℚ))
  (hdim : ∀ L, Module.finrank ℚ (e L) = Module.finrank ℚ L) (hgood : ∀ L, G' (e L) ↔ G L)
include hdim hgood

/-- An order automorphism preserving dimension and carrying `G` to `G'` bijects the `G`-lines onto the `G'`-lines. -/
def lineEquiv2 : Line G ≃ Line G' :=
  e.toEquiv.subtypeEquiv (by
    intro L
    change (Module.finrank ℚ L = 1 ∧ G L) ↔ (Module.finrank ℚ (e L) = 1 ∧ G' (e L))
    rw [hdim, hgood])

/-- ... and the `G`-planes onto the `G'`-planes. -/
def planeEquiv2 : Plane G ≃ Plane G' :=
  e.toEquiv.subtypeEquiv (by
    intro P
    change (Module.finrank ℚ P = 2 ∧ ∃ L : Line G, L.val ≤ P) ↔
      (Module.finrank ℚ (e P) = 2 ∧ ∃ L : Line G', L.val ≤ e P)
    rw [hdim]
    constructor
    · rintro ⟨hP, L, hL⟩
      exact ⟨hP, lineEquiv2 G G' e hdim hgood L, e.monotone hL⟩
    · rintro ⟨hP, M, hM⟩
      obtain ⟨L, rfl⟩ := (lineEquiv2 G G' e hdim hgood).surjective M
      exact ⟨hP, L, e.le_iff_le.mp hM⟩)

/-- The induced isomorphism of the two incidence graphs. -/
def graphIso2 : (GoodIncidenceConnected.graph G) ≃g (GoodIncidenceConnected.graph G') where
  toEquiv := Equiv.sumCongr (lineEquiv2 G G' e hdim hgood) (planeEquiv2 G G' e hdim hgood)
  map_rel_iff' := by
    intro u v
    cases u <;> cases v
    · exact Iff.rfl
    · exact e.lt_iff_lt
    · exact e.lt_iff_lt
    · exact Iff.rfl

end GraphIso

/-- **`T† = B₃ T↑`**: `B₃` induces an isomorphism from the restricted incidence graph `T↑` (good = integral vector with coordinate sum
`≢ 0 (mod 3)`) onto `T†` (good = integral vector with last coordinate `≢ 0 (mod 3)`), carrying lines to lines, planes to planes and preserving incidence. -/
def graphIso_B3 : (GoodIncidenceConnected.graph TernaryPoly.ModThreeGoodAction.Good) ≃g
    (GoodIncidenceConnected.graph TernaryPoly.RelativeStabilizerCoordinates.Good3) :=
  graphIso2 TernaryPoly.ModThreeGoodAction.Good TernaryPoly.RelativeStabilizerCoordinates.Good3
    (Submodule.orderIsoMapComap (TernaryPoly.ModThreeGoodAction.rationalRepresentation B3))
    (fun L => LinearEquiv.finrank_map_eq _ L) (fun L => good3_map_B3_iff L)

end Building

section Flags

open GeneralEisenstein.Adelic

/-- The rational subspace of a flag representative: the first two columns of `g` for a plane flag, the first column for a line flag. -/
def flagSubspace : Side → RationalGL3 → Submodule ℚ (Fin 3 → ℚ)
  | .plane, g => (LinearMap.ker (LinearMap.proj 2 : (Fin 3 → ℚ) →ₗ[ℚ] ℚ)).map (Matrix.mulVecLin g.val)
  | .line, g => (LinearMap.ker (LinearMap.proj 1 : (Fin 3 → ℚ) →ₗ[ℚ] ℚ) ⊓
      LinearMap.ker (LinearMap.proj 2 : (Fin 3 → ℚ) →ₗ[ℚ] ℚ)).map (Matrix.mulVecLin g.val)

theorem mem_flagSubspace (side : Side) (g : RationalGL3) (x : Fin 3 → ℚ) :
    x ∈ flagSubspace side g ↔ ∃ w : Fin 3 → ℚ,
      (match side with
       | .plane => w 2 = 0
       | .line => w 1 = 0 ∧ w 2 = 0) ∧ g.val *ᵥ w = x := by
  cases side <;> simp [flagSubspace, Submodule.mem_map, Submodule.mem_inf, LinearMap.mem_ker]

/-- Integral vectors "in a flag" (as in `GeneralEisenstein.IntegralVectorInFlag`) are the integral vectors of the flag's rational subspace; the
definition does not depend on the representative of the coset. -/
theorem integralVectorInFlag_iff (side : Side) (g : RationalGL3) (v : Fin 3 → ℤ) :
    IntegralVectorInFlag side (QuotientGroup.mk g) v ↔
      TernaryPoly.ModThreeGoodAction.rationalVector v ∈ flagSubspace side g := by
  rw [mem_flagSubspace]
  constructor
  · rintro ⟨g', hg', w, hw, hgw⟩
    obtain ⟨p, hp, rfl⟩ : ∃ p ∈ parabolic side, g' = g * p :=
      ⟨g⁻¹ * g', QuotientGroup.eq.mp hg'.symm, by group⟩
    refine ⟨p.val *ᵥ w, ?_, ?_⟩
    · cases side
      · have hp' : p.val 2 0 = 0 ∧ p.val 2 1 = 0 := hp
        have hw' : w 2 = 0 := hw
        simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, hp'.1, hp'.2, hw', mul_zero, add_zero, zero_mul]
      · have hp' : p.val 1 0 = 0 ∧ p.val 2 0 = 0 := hp
        have hw' : w 1 = 0 ∧ w 2 = 0 := hw
        simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, hp'.1, hp'.2, hw'.1, hw'.2, mul_zero, add_zero,
          zero_mul, and_self]
    · rw [Matrix.mulVec_mulVec, ← Units.val_mul]
      exact hgw
  · rintro ⟨w, hw, hgw⟩
    cases side <;> exact ⟨g, rfl, w, hw, hgw⟩

/-- **`GoodFlag` is goodness of the flag's subspace**: last coordinate `≢ 0 (mod 3)`, i.e. `Good3`. -/
theorem goodFlag_iff_good3 (side : Side) (g : RationalGL3) :
    GoodFlag side (QuotientGroup.mk g) ↔ TernaryPoly.RelativeStabilizerCoordinates.Good3 (flagSubspace side g) := by
  unfold GoodFlag TernaryPoly.RelativeStabilizerCoordinates.Good3
  simp only [integralVectorInFlag_iff]

theorem rationalRepresentation_apply (g : IntegralGL3) (y : Fin 3 → ℚ) :
    TernaryPoly.ModThreeGoodAction.rationalRepresentation g y =
      (GeneralLinearGroup.map (Int.castRingHom ℚ) g).val *ᵥ y := by
  funext i
  simp [TernaryPoly.ModThreeGoodAction.rationalRepresentation, Matrix.mulVec, dotProduct]

theorem flagSubspace_B3 (side : Side) (g : RationalGL3) :
    flagSubspace side (GeneralLinearGroup.map (Int.castRingHom ℚ) B3 * g) =
      (flagSubspace side g).map (TernaryPoly.ModThreeGoodAction.rationalRepresentation B3).toLinearMap := by
  ext x
  rw [mem_flagSubspace, Submodule.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨g.val *ᵥ w, (mem_flagSubspace side g _).mpr ⟨w, hw, rfl⟩, ?_⟩
    rw [LinearEquiv.coe_coe, rationalRepresentation_apply, Units.val_mul, Matrix.mulVec_mulVec]
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨w, hw, rfl⟩ := (mem_flagSubspace side g y).mp hy
    refine ⟨w, hw, ?_⟩
    rw [LinearEquiv.coe_coe, rationalRepresentation_apply, Units.val_mul, Matrix.mulVec_mulVec]

/-- **`T† = B₃ T↑` on flags**: the flag `B₃ g` is good for `T†` (an integral vector with last coordinate `≢ 0 (mod 3)`) iff the flag `g` is
good for `T↑` (an integral vector with coordinate sum `≢ 0 (mod 3)`). -/
theorem goodFlag_B3_iff (side : Side) (g : RationalGL3) :
    GoodFlag side (QuotientGroup.mk (GeneralLinearGroup.map (Int.castRingHom ℚ) B3 * g)) ↔
      TernaryPoly.ModThreeGoodAction.Good (flagSubspace side g) := by
  rw [goodFlag_iff_good3, flagSubspace_B3]
  exact good3_map_B3_iff _

end Flags

end TernaryPeriodPolynomials.Argument.Identities
