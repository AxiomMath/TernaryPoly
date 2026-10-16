module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs

@[expose] public section


/-!
# Homogeneous primitives from inhomogeneous ones

Let `Γ ≤ G` act on `G` by left multiplication. A `Γ`-equivariant homogeneous 2-cocycle on
all `G`-tuples whose inhomogeneous restriction to `Γ` is a coboundary is itself the
differential of a `Γ`-equivariant homogeneous 1-cochain. The proof uses an equivariant
retraction `π : G → Γ` (choose a representative of every orbit) and the prism homotopy
between `π` and the identity.

Original work (AxiomDeep, Claude Opus 5.5).
-/

open GeneralEisenstein.Homogeneous

noncomputable section

namespace TernaryPeriodPolynomials.FlagExactness

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

/-- A chosen representative of the `Γ`-orbit of `x`. -/
def orbitRep (Γ : Subgroup G) (x : G) : G :=
  Quotient.out (Quotient.mk (QuotientGroup.rightRel Γ) x)

theorem orbitRep_mem (Γ : Subgroup G) (x : G) : x * (orbitRep Γ x)⁻¹ ∈ Γ := by
  have h : QuotientGroup.rightRel Γ (orbitRep Γ x) x := Quotient.mk_out (s := QuotientGroup.rightRel Γ) x
  exact QuotientGroup.rightRel_apply.mp h

theorem orbitRep_mul (Γ : Subgroup G) (γ : Γ) (x : G) : orbitRep Γ (γ.val * x) = orbitRep Γ x := by
  unfold orbitRep
  congr 1
  apply Quotient.sound
  change QuotientGroup.rightRel Γ (γ.val * x) x
  rw [QuotientGroup.rightRel_apply]
  simp

/-- The equivariant retraction onto `Γ`. -/
def orbitRetract (Γ : Subgroup G) (x : G) : Γ := ⟨x * (orbitRep Γ x)⁻¹, orbitRep_mem Γ x⟩

theorem orbitRetract_mul (Γ : Subgroup G) (γ : Γ) (x : G) :
    orbitRetract Γ (γ.val * x) = γ * orbitRetract Γ x := by
  apply Subtype.ext
  simp [orbitRetract, orbitRep_mul, mul_assoc]

/-- **Homogeneous primitive from an inhomogeneous one.** -/
theorem exists_primitive_of_inhomogeneous (Γ : Subgroup G) (ρ : Representation ℂ G V)
    (K : cochains Γ ρ 2)
    (cocycle : ∀ x : Fin 4 → G, K.val ![x 1, x 2, x 3] - K.val ![x 0, x 2, x 3] +
      K.val ![x 0, x 1, x 3] - K.val ![x 0, x 1, x 2] = 0)
    (τ : Γ → V) (hτ : ∀ a b : Γ, K.val ![1, a.val, a.val * b.val] =
      ρ a.val (τ b) - τ (a * b) + τ a) :
    ∃ P : cochains Γ ρ 1, ∀ x, (differentialOne Γ ρ P).val x = K.val x := by
  have coc : ∀ a b c d : G, K.val ![b, c, d] - K.val ![a, c, d] + K.val ![a, b, d] -
      K.val ![a, b, c] = 0 := fun a b c d => cocycle ![a, b, c, d]
  set π := orbitRetract Γ
  have hπ : ∀ (γ : Γ) (x : G), π (γ.val * x) = γ * π x := orbitRetract_mul Γ
  let B : Γ → Γ → V := fun g₀ g₁ => ρ g₀.val (τ (g₀⁻¹ * g₁))
  let value : (Fin 2 → G) → V := fun y =>
    B (π (y 0)) (π (y 1)) - (K.val ![y 0, (π (y 0)).val, (π (y 1)).val] -
      K.val ![y 0, y 1, (π (y 1)).val])
  have hK : ∀ (γ : Γ) (a b c : G), K.val ![γ.val * a, γ.val * b, γ.val * c] =
      ρ γ.val (K.val ![a, b, c]) := by
    intro γ a b c
    have h := K.property γ ![a, b, c]
    have ht : (fun i => γ.val * (![a, b, c] : Fin 3 → G) i) = ![γ.val * a, γ.val * b, γ.val * c] := by
      funext i; fin_cases i <;> rfl
    rw [ht] at h
    exact h
  have hequiv : ∀ (γ : Γ) x, value (fun i => γ.val * x i) = ρ γ.val (value x) := by
    intro γ x
    simp only [value, B]
    rw [hπ, hπ]
    simp only [Subgroup.coe_mul]
    rw [hK, hK, map_sub, map_sub, ← Module.End.mul_apply, ← map_mul]
    congr 3
    group
  refine ⟨⟨value, hequiv⟩, fun x => ?_⟩
  change value ![x 1, x 2] - value ![x 0, x 2] + value ![x 0, x 1] = K.val x
  simp only [value, B, Matrix.cons_val_zero, Matrix.cons_val_one]
  set p0 := π (x 0)
  set p1 := π (x 1)
  set p2 := π (x 2)
  -- the inhomogeneous part gives `K (π x)`
  have hB : ρ p1.val (τ (p1⁻¹ * p2)) - ρ p0.val (τ (p0⁻¹ * p2)) + ρ p0.val (τ (p0⁻¹ * p1)) =
      K.val ![p0.val, p1.val, p2.val] := by
    have h := hτ (p0⁻¹ * p1) (p1⁻¹ * p2)
    have e1 : (p0⁻¹ * p1) * (p1⁻¹ * p2) = p0⁻¹ * p2 := by group
    rw [e1] at h
    have e2 : (![1, (p0⁻¹ * p1).val, (p0⁻¹ * p1).val * (p1⁻¹ * p2).val] : Fin 3 → G) =
        ![(p0⁻¹).val * p0.val, (p0⁻¹).val * p1.val, (p0⁻¹).val * p2.val] := by
      funext i
      fin_cases i <;> simp [mul_assoc]
    rw [e2, hK] at h
    have h' := congrArg (ρ p0.val) h
    rw [← Module.End.mul_apply, ← map_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one,
      map_one, Module.End.one_apply] at h'
    rw [h', map_add, map_sub, ← Module.End.mul_apply, ← map_mul, ← Subgroup.coe_mul]
    have e3 : p0 * (p0⁻¹ * p1) = p1 := by group
    rw [e3]
  have c1 := coc (x 0) p0.val p1.val p2.val
  have c2 := coc (x 0) (x 1) p1.val p2.val
  have c3 := coc (x 0) (x 1) (x 2) p2.val
  have hx : K.val x = K.val ![x 0, x 1, x 2] :=
    congrArg K.val (by funext i; fin_cases i <;> rfl)
  rw [hx]
  linear_combination (norm := abel) hB - c2 + c1 + c3

end TernaryPeriodPolynomials.FlagExactness
