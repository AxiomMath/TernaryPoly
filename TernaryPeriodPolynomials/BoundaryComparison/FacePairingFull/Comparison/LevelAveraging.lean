module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelTransfer.Transfer
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.TraceQuotient
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.LevelSix

@[expose] public section


/-!
# S3: boundary exactness descends from `Γ(6)` to the level

If a level-invariant closed edge three-cochain is boundary exact for the subgroup `N6` (the image of
`Γ(6)`), it is boundary exact for the level `rationalLevel`: averaging over the finite quotient
`rationalLevel / N6` is the identity on level-invariant cochains,
produces level-invariant cochains, and commutes with the homogeneous differentials in degrees two and
three and with pullback along the equivariant maps `endpoint .plane`, `endpoint .line`
(`boundaryExactAt_of_N6`).  This is the injectivity of `Q_level → Q_{Γ(6)}`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.Argument.LevelTransfer

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison

section Degree3

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)

/-- Raw degree-three differential as a linear map. -/
def rd3 : FunSpace G V 3 →ₗ[ℂ] FunSpace G V 4 where
  toFun f x := differentialThreeRaw f x
  map_add' f g := by funext x; simp only [differentialThreeRaw, Pi.add_apply]; abel
  map_smul' a f := by
    funext x
    simp only [differentialThreeRaw, Pi.smul_apply, RingHom.id_apply, smul_add, smul_sub]

omit [Group G] in
theorem rd3_apply (f : FunSpace G V 3) (x : Fin 5 → G) : rd3 f x = differentialThreeRaw f x := rfl

theorem actFun_rd3 (s : G) (f : FunSpace G V 3) : actFun ρ s (rd3 f) = rd3 (actFun ρ s f) := by
  funext x
  have h : ∀ (a b c d : Fin 5), (fun i : Fin 4 => s⁻¹ * (![x a, x b, x c, x d] : Fin 4 → G) i) =
      ![s⁻¹ * x a, s⁻¹ * x b, s⁻¹ * x c, s⁻¹ * x d] := by
    intro a b c d; funext i; fin_cases i <;> rfl
  simp only [actFun_apply, rd3_apply, differentialThreeRaw, map_add, map_sub, h]

variable (N S : Subgroup G) [Fintype (S ⧸ N.subgroupOf S)]

theorem avg_rd3 (f : FunSpace G V 3) : avg ρ N S (rd3 f) = rd3 (avg ρ N S f) := by
  simp only [avg_apply, map_smul, map_sum, actFun_rd3]

end Degree3

section Pullback

variable {X : Type} [MulAction RationalGL3 X] (π : Edges → X) (hπ : ∀ (g : RationalGL3) (e : Edges),
  π (g • e) = g • π e)

/-- Pullback of a function of vertices and `X` to complete flags along an equivariant map. -/
def pullEdges {k : ℕ} : FunSpace RationalGL3 (X → ℂ) k →ₗ[ℂ] FunSpace RationalGL3 (Edges → ℂ) k where
  toFun p x e := p x (π e)
  map_add' p q := by funext x e; rfl
  map_smul' a p := by funext x e; rfl

include hπ in
theorem actFun_pullEdges {k : ℕ} (s : RationalGL3) (p : FunSpace RationalGL3 (X → ℂ) k) :
    actFun (functionRepresentation scalarTrivial Edges) s (pullEdges π p) =
      pullEdges π (actFun (functionRepresentation scalarTrivial X) s p) := by
  funext x e
  change scalarTrivial s (p (fun i => s⁻¹ * x i) (π (s⁻¹ • e))) =
    scalarTrivial s (p (fun i => s⁻¹ * x i) (s⁻¹ • π e))
  rw [hπ]

end Pullback

variable (N S : Subgroup RationalGL3) [Fintype (S ⧸ N.subgroupOf S)]

include N S in
theorem avg_pullEdges {X : Type} [MulAction RationalGL3 X] (π : Edges → X)
    (hπ : ∀ (g : RationalGL3) (e : Edges), π (g • e) = g • π e) {k : ℕ}
    (p : FunSpace RationalGL3 (X → ℂ) k) :
    avg (functionRepresentation scalarTrivial Edges) N S (pullEdges π p) =
      pullEdges π (avg (functionRepresentation scalarTrivial X) N S p) := by
  simp only [avg_apply, map_smul, map_sum, actFun_pullEdges π hπ]

/-- **Boundary exactness descends from `Γ(6)` to the level.** -/
theorem boundaryExactAt_of_N6
    {f : (Fin 4 → RationalGL3) → Edges → ℂ} (hf : f ∈ closedEdgeCochains rationalLevel)
    (h : BoundaryExactAt N6 f) : BoundaryExactAt rationalLevel f := by
  obtain ⟨edge, plane, line, hplane, hline, pc, lc, eq⟩ := h
  have hle := N6_le_rationalLevel
  have hnorm := N6_normalized
  have hfeq : f = rd2 edge.val + pullEdges (endpoint .plane) plane - pullEdges (endpoint .line) line := by
    funext x e
    have := eq x e
    rw [differentialTwo_eq] at this
    exact this
  have hfavg : avg (functionRepresentation scalarTrivial Edges) N6 rationalLevel f = f :=
    avg_of_isEq_S _ ((mem_cochains_iff _ rationalLevel 3 f).mp hf.1)
  have hplane' : avg (functionRepresentation scalarTrivial (Flags .plane)) N6 rationalLevel plane ∈
      cochains rationalLevel (functionRepresentation scalarTrivial (Flags .plane)) 3 :=
    avg_mem_cochains _ hle hnorm ⟨plane, hplane⟩
  have hline' : avg (functionRepresentation scalarTrivial (Flags .line)) N6 rationalLevel line ∈
      cochains rationalLevel (functionRepresentation scalarTrivial (Flags .line)) 3 :=
    avg_mem_cochains _ hle hnorm ⟨line, hline⟩
  have hedge' : avg (functionRepresentation scalarTrivial Edges) N6 rationalLevel edge.val ∈
      cochains rationalLevel (functionRepresentation scalarTrivial Edges) 2 :=
    avg_mem_cochains _ hle hnorm edge
  have hpz : rd3 plane = 0 := by funext x; exact pc x
  have hlz : rd3 line = 0 := by funext x; exact lc x
  refine ⟨⟨_, hedge'⟩, avg (functionRepresentation scalarTrivial (Flags .plane)) N6 rationalLevel plane,
    avg (functionRepresentation scalarTrivial (Flags .line)) N6 rationalLevel line,
    hplane', hline', ?_, ?_, ?_⟩
  · intro x
    have : rd3 (avg (functionRepresentation scalarTrivial (Flags .plane)) N6 rationalLevel plane) = 0 := by
      rw [← avg_rd3, hpz, map_zero]
    exact congrFun this x
  · intro x
    have : rd3 (avg (functionRepresentation scalarTrivial (Flags .line)) N6 rationalLevel line) = 0 := by
      rw [← avg_rd3, hlz, map_zero]
    exact congrFun this x
  · intro x e
    have key := congrArg (avg (functionRepresentation scalarTrivial Edges) N6 rationalLevel) hfeq
    rw [hfavg, map_sub, map_add, avg_rd2, avg_pullEdges N6 rationalLevel (endpoint .plane)
      (endpoint_smul .plane), avg_pullEdges N6 rationalLevel (endpoint .line) (endpoint_smul .line)] at key
    have := congrFun (congrFun key x) e
    rw [differentialTwo_eq]
    exact this

end TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
