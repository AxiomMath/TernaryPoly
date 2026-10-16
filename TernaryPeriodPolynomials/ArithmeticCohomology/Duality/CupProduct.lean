module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs.HomogeneousCohomology

@[expose] public section


/-!
# Higher homogeneous differentials and twisted cup products

The alternating homogeneous differentials in degrees three and four, and the Alexander–Whitney
cup product of two homogeneous cochains paired by a bilinear form, where the vertices of the
second factor are first moved by a map `ψ`. The Leibniz rule holds for any `ψ`; only the
equivariance of the product uses that `ψ` is a homomorphism preserving the level.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Duality

variable {G V W M : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup M] [Module ℂ M]

/-- The alternating homogeneous differential of a function of four vertices. -/
def differentialThreeRaw (f : (Fin 4 → G) → M) (x : Fin 5 → G) : M :=
  f ![x 1, x 2, x 3, x 4] - f ![x 0, x 2, x 3, x 4] + f ![x 0, x 1, x 3, x 4] -
    f ![x 0, x 1, x 2, x 4] + f ![x 0, x 1, x 2, x 3]

/-- The alternating homogeneous differential of a function of five vertices. -/
def differentialFourRaw (f : (Fin 5 → G) → M) (x : Fin 6 → G) : M :=
  f ![x 1, x 2, x 3, x 4, x 5] - f ![x 0, x 2, x 3, x 4, x 5] + f ![x 0, x 1, x 3, x 4, x 5] -
    f ![x 0, x 1, x 2, x 4, x 5] + f ![x 0, x 1, x 2, x 3, x 5] - f ![x 0, x 1, x 2, x 3, x 4]

/-- The homogeneous one-cochain differential of a function of two vertices. -/
def differentialOneRaw (f : (Fin 2 → G) → M) (x : Fin 3 → G) : M :=
  f ![x 1, x 2] - f ![x 0, x 2] + f ![x 0, x 1]

/-- A function of three vertices is a homogeneous cocycle. -/
def IsCocycleTwo (f : (Fin 3 → G) → M) : Prop :=
  ∀ x : Fin 4 → G, f ![x 1, x 2, x 3] - f ![x 0, x 2, x 3] + f ![x 0, x 1, x 3] -
    f ![x 0, x 1, x 2] = 0

/-- The cup product of a two-cochain with a two-cochain whose vertices are moved by `ψ`. -/
def cupTwoTwo (B : V →ₗ[ℂ] W →ₗ[ℂ] M) (ψ : G → G) (f : (Fin 3 → G) → V)
    (g : (Fin 3 → G) → W) (x : Fin 5 → G) : M :=
  B (f ![x 0, x 1, x 2]) (g ![ψ (x 2), ψ (x 3), ψ (x 4)])

/-- The cup product of a one-cochain with a two-cochain whose vertices are moved by `ψ`. -/
def cupOneTwo (B : V →ₗ[ℂ] W →ₗ[ℂ] M) (ψ : G → G) (u : (Fin 2 → G) → V)
    (g : (Fin 3 → G) → W) (x : Fin 4 → G) : M :=
  B (u ![x 0, x 1]) (g ![ψ (x 1), ψ (x 2), ψ (x 3)])

/-- The cup product of two cocycles is a cocycle. -/
theorem differentialFourRaw_cupTwoTwo (B : V →ₗ[ℂ] W →ₗ[ℂ] M) (ψ : G → G)
    {f : (Fin 3 → G) → V} {g : (Fin 3 → G) → W} (hf : IsCocycleTwo f) (hg : IsCocycleTwo g)
    (x : Fin 6 → G) : differentialFourRaw (cupTwoTwo B ψ f g) x = 0 := by
  have first : f ![x 1, x 2, x 3] - f ![x 0, x 2, x 3] + f ![x 0, x 1, x 3] -
      f ![x 0, x 1, x 2] = 0 := hf ![x 0, x 1, x 2, x 3]
  have second : g ![ψ (x 3), ψ (x 4), ψ (x 5)] - g ![ψ (x 2), ψ (x 4), ψ (x 5)] +
      g ![ψ (x 2), ψ (x 3), ψ (x 5)] - g ![ψ (x 2), ψ (x 3), ψ (x 4)] = 0 :=
    hg ![ψ (x 2), ψ (x 3), ψ (x 4), ψ (x 5)]
  have first' : f ![x 1, x 2, x 3] = f ![x 0, x 2, x 3] - f ![x 0, x 1, x 3] +
      f ![x 0, x 1, x 2] := by
    rw [← sub_eq_zero, ← first]; abel
  have second' : g ![ψ (x 2), ψ (x 3), ψ (x 4)] = g ![ψ (x 3), ψ (x 4), ψ (x 5)] -
      g ![ψ (x 2), ψ (x 4), ψ (x 5)] + g ![ψ (x 2), ψ (x 3), ψ (x 5)] := by
    rw [← sub_eq_zero, ← neg_eq_zero, ← second]; abel
  change B (f ![x 1, x 2, x 3]) (g ![ψ (x 3), ψ (x 4), ψ (x 5)]) -
      B (f ![x 0, x 2, x 3]) (g ![ψ (x 3), ψ (x 4), ψ (x 5)]) +
      B (f ![x 0, x 1, x 3]) (g ![ψ (x 3), ψ (x 4), ψ (x 5)]) -
      B (f ![x 0, x 1, x 2]) (g ![ψ (x 2), ψ (x 4), ψ (x 5)]) +
      B (f ![x 0, x 1, x 2]) (g ![ψ (x 2), ψ (x 3), ψ (x 5)]) -
      B (f ![x 0, x 1, x 2]) (g ![ψ (x 2), ψ (x 3), ψ (x 4)]) = 0
  rw [first', second', map_add, map_sub, map_add, map_sub, LinearMap.add_apply,
    LinearMap.sub_apply]
  abel

/-- Leibniz rule: the differential of `u ⌣ g` for a cocycle `g` is `du ⌣ g`. -/
theorem differentialThreeRaw_cupOneTwo (B : V →ₗ[ℂ] W →ₗ[ℂ] M) (ψ : G → G)
    (u : (Fin 2 → G) → V) {g : (Fin 3 → G) → W} (hg : IsCocycleTwo g) (x : Fin 5 → G) :
    differentialThreeRaw (cupOneTwo B ψ u g) x =
      cupTwoTwo B ψ (differentialOneRaw u) g x := by
  have second : g ![ψ (x 2), ψ (x 3), ψ (x 4)] - g ![ψ (x 1), ψ (x 3), ψ (x 4)] +
      g ![ψ (x 1), ψ (x 2), ψ (x 4)] - g ![ψ (x 1), ψ (x 2), ψ (x 3)] = 0 :=
    hg ![ψ (x 1), ψ (x 2), ψ (x 3), ψ (x 4)]
  have second' : g ![ψ (x 1), ψ (x 2), ψ (x 3)] = g ![ψ (x 2), ψ (x 3), ψ (x 4)] -
      g ![ψ (x 1), ψ (x 3), ψ (x 4)] + g ![ψ (x 1), ψ (x 2), ψ (x 4)] := by
    rw [← sub_eq_zero, ← neg_eq_zero, ← second]; abel
  change B (u ![x 1, x 2]) (g ![ψ (x 2), ψ (x 3), ψ (x 4)]) -
      B (u ![x 0, x 2]) (g ![ψ (x 2), ψ (x 3), ψ (x 4)]) +
      B (u ![x 0, x 1]) (g ![ψ (x 1), ψ (x 3), ψ (x 4)]) -
      B (u ![x 0, x 1]) (g ![ψ (x 1), ψ (x 2), ψ (x 4)]) +
      B (u ![x 0, x 1]) (g ![ψ (x 1), ψ (x 2), ψ (x 3)]) =
    B (u ![x 1, x 2] - u ![x 0, x 2] + u ![x 0, x 1]) (g ![ψ (x 2), ψ (x 3), ψ (x 4)])
  rw [second', map_add, map_sub, map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]
  abel

end TernaryPeriodPolynomials.Duality
