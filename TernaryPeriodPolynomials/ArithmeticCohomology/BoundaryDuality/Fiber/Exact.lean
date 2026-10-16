module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Fiber.L1

@[expose] public section


/-!
# The `U`-primitives of the fiber integration from exactness on the lattice

The fiber integration at a line cusp `Lf` uses primitives `ω_U`, `θ_U` of the restrictions of the
line cocycle `z(·)(Lf)` and of the dual plane cocycle `y(φ ·)(F)` (`F` the dual plane of `Lf`) to
a lattice `U` in the stabilizer of `Lf`. These restrictions are homogeneous two-cocycles of `U`
(`lineRestriction`, `planeRestriction`), and their primitives exist exactly when their classes in
`H²(U, ·)` vanish (`exists_omegaU`, `exists_thetaU`), in the shape of the hypotheses of
`FiberL1.lineValue_goodLine` and `FiberL0.lineValue_badLine`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous

namespace TernaryPeriodPolynomials.BoundaryDuality.FiberExact

open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.BoundaryDuality.TraceChains
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.BoundaryDuality.FiberL1 (dualRep)

section Generic

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

/-- **A primitive of an exact homogeneous two-cocycle**, with equivariance at displayed vertices. -/
theorem exists_primitive_of_classOf_eq_zero {Γ : Subgroup G} {ρ : Representation ℂ G V}
    (c : cocycles Γ ρ) (hc : classOf Γ ρ c = 0) :
    ∃ u : (Fin 2 → G) → V, (∀ γ ∈ Γ, ∀ a b, u ![γ * a, γ * b] = ρ γ (u ![a, b])) ∧
      ∀ a b d, differentialOneRaw u ![a, b, d] = c.val.val ![a, b, d] := by
  obtain ⟨p, hp⟩ := LinearMap.mem_range.mp ((Submodule.Quotient.mk_eq_zero _).mp hc)
  refine ⟨p.val, fun γ hγ a b => ?_, fun a b d => ?_⟩
  · have e : (fun i => γ * (![a, b] : Fin 2 → G) i) = ![γ * a, γ * b] := by
      funext i
      fin_cases i <;> rfl
    exact (congrArg p.val e).symm.trans (p.property ⟨γ, hγ⟩ ![a, b])
  · exact congrFun (congrArg (fun c => c.val.val) hp) ![a, b, d]

end Generic

variable {n : ℕ} {χ : RankOneCharacter}

/-- The restriction of a line two-cocycle at the line `Lf` to a subgroup of its stabilizer. -/
def lineRestriction (z : MaximalCycles n χ .line) (Lf : Flags .line) (U : Subgroup RationalGL3)
    (hU : U ≤ levelStabilizer Lf) : cocycles U (rationalCoefficientComponent n χ) :=
  ⟨⟨fun x => z.val.val x Lf, by
      intro γ x
      have hγ := hU γ.property
      have level : γ.val ∈ rationalLevel := (Subgroup.mem_inf.mp hγ).1
      have fixed : γ.val • Lf = Lf := MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp hγ).2
      have h := congrFun (z.val.property ⟨γ.val, level⟩ x) Lf
      change z.val.val (fun i => γ.val * x i) Lf =
        rationalCoefficientComponent n χ γ.val (z.val.val x (γ.val⁻¹ • Lf)) at h
      rw [inv_smul_eq_iff.mpr fixed.symm] at h
      exact h⟩, by
    apply LinearMap.mem_ker.mpr
    funext x
    exact congrFun (isCocycleTwo_of_mem z x) Lf⟩

/-- The restriction of a plane two-cocycle at the dual plane of `Lf`, with vertices moved by `φ`,
to a subgroup of the stabilizer of `Lf`. -/
def planeRestriction (Td : DualityData n χ) (y : MaximalCycles n χ .plane) (Lf : Flags .line)
    (U : Subgroup RationalGL3) (hU : U ≤ levelStabilizer Lf) : cocycles U (dualRep Td) :=
  ⟨⟨fun x => y.val.val ![Td.φ (x 0), Td.φ (x 1), Td.φ (x 2)] (Td.dualFlag Lf), by
      intro γ x
      have hγ := hU γ.property
      have level : γ.val ∈ rationalLevel := (Subgroup.mem_inf.mp hγ).1
      have fixed : γ.val • Lf = Lf := MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp hγ).2
      have dual : Td.φ γ.val ∈ rationalLevel := Td.level γ.val level
      have fixedF : (Td.φ γ.val)⁻¹ • Td.dualFlag Lf = Td.dualFlag Lf := by
        rw [inv_smul_eq_iff, ← Td.dualFlag_smul, fixed]
      have h := congrFun (cochain_triple y.val ⟨Td.φ γ.val, dual⟩ (Td.φ (x 0)) (Td.φ (x 1))
        (Td.φ (x 2))) (Td.dualFlag Lf)
      change y.val.val ![Td.φ γ.val * Td.φ (x 0), Td.φ γ.val * Td.φ (x 1),
          Td.φ γ.val * Td.φ (x 2)] (Td.dualFlag Lf) =
        rationalCoefficientComponent n χ (Td.φ γ.val)
          (y.val.val ![Td.φ (x 0), Td.φ (x 1), Td.φ (x 2)]
            ((Td.φ γ.val)⁻¹ • Td.dualFlag Lf)) at h
      rw [fixedF] at h
      change y.val.val ![Td.φ (γ.val * x 0), Td.φ (γ.val * x 1), Td.φ (γ.val * x 2)]
          (Td.dualFlag Lf) =
        rationalCoefficientComponent n χ (Td.φ γ.val)
          (y.val.val ![Td.φ (x 0), Td.φ (x 1), Td.φ (x 2)] (Td.dualFlag Lf))
      rw [map_mul, map_mul, map_mul]
      exact h⟩, by
    apply LinearMap.mem_ker.mpr
    funext x
    exact congrFun (isCocycleTwo_of_mem y ![Td.φ (x 0), Td.φ (x 1), Td.φ (x 2), Td.φ (x 3)])
      (Td.dualFlag Lf)⟩

/-- **The line `U`-primitive** from the vanishing of the class of the restriction to `U`. -/
theorem exists_omegaU (z : MaximalCycles n χ .line) (Lf : Flags .line) (U : Subgroup RationalGL3)
    (hU : U ≤ levelStabilizer Lf)
    (h : classOf U (rationalCoefficientComponent n χ) (lineRestriction z Lf U hU) = 0) :
    ∃ ωU : (Fin 2 → RationalGL3) → HomogeneousPoly n,
      (∀ γ ∈ U, ∀ a b,
        ωU ![γ * a, γ * b] = rationalCoefficientComponent n χ γ (ωU ![a, b])) ∧
      ∀ a b c, differentialOneRaw ωU ![a, b, c] = z.val.val ![a, b, c] Lf :=
  exists_primitive_of_classOf_eq_zero _ h

/-- **The dual plane `U`-primitive** from the vanishing of the class of the restriction to `U`. -/
theorem exists_thetaU (Td : DualityData n χ) (y : MaximalCycles n χ .plane) (Lf : Flags .line)
    (U : Subgroup RationalGL3) (hU : U ≤ levelStabilizer Lf)
    (h : classOf U (dualRep Td) (planeRestriction Td y Lf U hU) = 0) :
    ∃ θU : (Fin 2 → RationalGL3) → HomogeneousPoly n,
      (∀ γ ∈ U, ∀ a b,
        θU ![γ * a, γ * b] = rationalCoefficientComponent n χ (Td.φ γ) (θU ![a, b])) ∧
      ∀ a b c, differentialOneRaw θU ![a, b, c] =
        y.val.val ![Td.φ a, Td.φ b, Td.φ c] (Td.dualFlag Lf) :=
  exists_primitive_of_classOf_eq_zero _ h

end TernaryPeriodPolynomials.BoundaryDuality.FiberExact
