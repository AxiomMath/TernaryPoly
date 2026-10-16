module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.TwoCocycleEdgeAlgebra

@[expose] public section


/-!
# The corrected mixed edge function of a relatively trivial two-cocycle

Let a group `G` act on an additive group `V`, let `t` be an inhomogeneous two-cocycle and let
`a : G → V` trivialize `t` on a subgroup `N`: `t (r, r') = r • a r' - a (r r') + a r` for
`r, r' ∈ N`. For `m` normalizing `N` (in the sense `m⁻¹ N m ⊆ N`), the mixed edge function
`f_m r = t (m, m⁻¹ r m) - t (r, m)` fails to be a crossed homomorphism on `N` by the coboundary of
`a^m - a`, where `a^m r = m • a (m⁻¹ r m)`. Hence the corrected edge function
`g_m = f_m - (a^m - a)` is a crossed homomorphism on `N`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

namespace TernaryPeriodPolynomials.AnalyticClasses

variable {G V : Type*} [Group G] [AddCommGroup V] [DistribMulAction G V]

/-- The mixed edge function of `t` at `m`, corrected by the conjugation defect `a^m - a` of `a`. -/
def correctedEdgeFunction (t : G → G → V) (a : G → V) (m r : G) : V :=
  mixedEdgeFunction t m r - (m • a (m⁻¹ * r * m) - a r)

/-- **Defect of the mixed edge function.** For a two-cocycle, the mixed edge function fails to be
a crossed homomorphism by `t (r, r') - m • t (m⁻¹ r m, m⁻¹ r' m)`. -/
theorem mixedEdgeFunction_mul_right {t : G → G → V} (ht : IsTwoCocycle t) (m r r' : G) :
    mixedEdgeFunction t m (r * r') = mixedEdgeFunction t m r + r • mixedEdgeFunction t m r' +
      (t r r' - m • t (m⁻¹ * r * m) (m⁻¹ * r' * m)) := by
  unfold mixedEdgeFunction
  set s := m⁻¹ * r * m
  set s' := m⁻¹ * r' * m
  have product : m⁻¹ * (r * r') * m = s * s' := by simp [s, s', mul_assoc]
  have hs : m * s = r * m := by simp [s, mul_assoc]
  have hs' : m * s' = r' * m := by simp [s', mul_assoc]
  have e1 := ht m s s'
  have e2 := ht r r' m
  have e3 := ht r m s'
  rw [hs] at e1
  rw [hs'] at e3
  rw [product, smul_sub]
  linear_combination (norm := abel) e1 + e2 - e3

/-- **The corrected edge function is a crossed homomorphism** at a pair `r, r'` on which `t` is
the coboundary of `a`, and whose conjugates by `m` have the same property. -/
theorem correctedEdgeFunction_mul_of_pairs {t : G → G → V} (ht : IsTwoCocycle t) (a : G → V)
    (m r r' : G) (pair : t r r' = r • a r' - a (r * r') + a r)
    (conjugatePair : t (m⁻¹ * r * m) (m⁻¹ * r' * m) =
      (m⁻¹ * r * m) • a (m⁻¹ * r' * m) - a (m⁻¹ * r * m * (m⁻¹ * r' * m)) + a (m⁻¹ * r * m)) :
    correctedEdgeFunction t a m (r * r') =
      correctedEdgeFunction t a m r + r • correctedEdgeFunction t a m r' := by
  unfold correctedEdgeFunction
  rw [mixedEdgeFunction_mul_right ht, pair, conjugatePair]
  have product : m⁻¹ * (r * r') * m = m⁻¹ * r * m * (m⁻¹ * r' * m) := by
    simp [mul_assoc]
  have moved : m • ((m⁻¹ * r * m) • a (m⁻¹ * r' * m)) = r • m • a (m⁻¹ * r' * m) := by
    rw [smul_smul, smul_smul]
    congr 1
    group
  rw [product, smul_add, smul_sub, moved]
  simp only [smul_sub]
  abel

/-- **The corrected edge function is a crossed homomorphism on the subgroup.** -/
theorem correctedEdgeFunction_mul {t : G → G → V} (ht : IsTwoCocycle t) (N : Subgroup G)
    (a : G → V) (trivial : ∀ r ∈ N, ∀ r' ∈ N, t r r' = r • a r' - a (r * r') + a r)
    {m : G} (normalizes : ∀ r ∈ N, m⁻¹ * r * m ∈ N) {r r' : G} (hr : r ∈ N) (hr' : r' ∈ N) :
    correctedEdgeFunction t a m (r * r') =
      correctedEdgeFunction t a m r + r • correctedEdgeFunction t a m r' :=
  correctedEdgeFunction_mul_of_pairs ht a m r r' (trivial r hr r' hr')
    (trivial _ (normalizes r hr) _ (normalizes r' hr'))

end TernaryPeriodPolynomials.AnalyticClasses
