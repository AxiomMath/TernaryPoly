module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.AdjointLevelOneParabolic
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Hecke.AdjointLevi

@[expose] public section


/-!
# Hecke adjointness of the parabolic cup pairing of `GL₂(ℤ)` and its consequences

The parabolic cup pairing `parabolicPairing` of `H¹(GL₂(ℤ), Sym^m ⊗ det^e)` with
`H¹(GL₂(ℤ), Sym^m ⊗ det^{e'})` is *Hecke adjoint with scalar* `κ_p = p^{e' - e}`:

  `π (T_p x, y) = p^{e' - e} · π (x, T_p y)`

for the Hecke operators `T_p` of `Γ diag(p, 1) Γ` on the parabolic classes.  The scalar comes from
the transposition of the double coset: it is mapped to itself by `g ↦ p g⁻¹`, and the two twists
`det^e`, `det^{e'}` and the degree contribute `p^{-(e + e' - m)} · p^{2 e' - m}`
(`AdjointLevelOneKappa.binaryPairing_hecke_conj`).  The proof of this adjointness is the
compatibility of the fundamental chain of `SL₂(ℤ)\ℍ` with the Hecke correspondence; it is stated
here as the hypothesis `ParabolicHeckeAdjoint` and consumed in the form needed at the edges of the
boundary of the Borel–Serre compactification.

Combined with the edge formulas `E(T_p y) = a E(y) + s T_p E(y)` of the line cusp (coefficient
`s_line`) and of the dual plane cusp (coefficient `s_plane`), the relation
`s_plane = s_line · κ_p` (`p^{-(n+2)} = p^{-(n+1)} · p^{-1}` for the untwisted pair
`(e, e') = (0, -1)`, `p^{-(n+1)} = p^{-(n+2)} · p` for the pair `(-1, 0)` of the odd
character of conductor three) makes the dual eigenvalue equal to the eigenvalue itself: if `x` is an
eigen-edge of the line cusp with eigenvalue `c`, the functional `π x (·)` is an eigenfunctional with
eigenvalue `c` of the local Hecke operator at the plane cusp.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.BoundaryDuality.AdjointLevelOne

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.BoundaryDuality.HeckeAdjointLevi
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelOne

/-- **The adjoint scalar `κ_p = p^{e' - e}`** of the Hecke operators of `Γ diag(p, 1) Γ` for the
twists `e`, `e'`. -/
def heckeScalar (e e' : ℤ) (p : Nat.Primes) : ℂ := ((p.val : ℕ) : ℂ) ^ (e' - e)

/-- The adjoint scalar is nonzero. -/
theorem heckeScalar_ne_zero (e e' : ℤ) (p : Nat.Primes) : heckeScalar e e' p ≠ 0 :=
  zpow_ne_zero _ (Nat.cast_ne_zero.mpr p.property.ne_zero)

/-- The scalar for the untwisted line against the identity plane is `p⁻¹`. -/
theorem heckeScalar_zero_neg_one (p : Nat.Primes) :
    heckeScalar 0 (-1) p = (((p.val : ℕ) : ℂ))⁻¹ := by
  simp [heckeScalar]

/-- The scalar for the odd-twisted line against the odd-twisted plane is `p`. -/
theorem heckeScalar_neg_one_zero (p : Nat.Primes) :
    heckeScalar (-1) 0 p = ((p.val : ℕ) : ℂ) := by
  simp [heckeScalar]

/-- **Hecke adjointness on the parabolic classes.**  The pairing `π` of the parabolic classes of
`H¹(GL₂(ℤ), Sym^d ⊗ det^τ)` and `H¹(GL₂(ℤ), Sym^d ⊗ det^{τ'})` satisfies
`π (T_p x, y) = κ_p π (x, T_p y)` for the parabolic Hecke operators. -/
def ParabolicHeckeAdjoint (d : ℕ) (τ τ' : ℤ)
    (π : parabolicH1 (arithmeticBinaryRep d τ) →ₗ[ℂ] parabolicH1 (arithmeticBinaryRep d τ') →ₗ[ℂ] ℂ)
    (κ : Nat.Primes → ℂ) : Prop :=
  ∀ p : Nat.Primes, IsHeckeAdjoint π (parabolicHecke d τ p) (parabolicHecke d τ' p) (κ p)

/-- **Hecke adjointness of the parabolic cup pairing** with the scalar `p^{e' - e}`: the
statement whose proof is the compatibility of the fundamental chain with the Hecke correspondence. -/
def ParabolicPairingHeckeAdjoint (m : ℕ) (e e' : ℤ) (hm : Even m)
    (hodd : Odd (e + e' - (m : ℤ))) : Prop :=
  ParabolicHeckeAdjoint m e e' (parabolicPairing (twistedPairing_arithmeticBinaryRep m e e' hm hodd))
    (heckeScalar e e')

/-- Adjointness for a pairing of the full cohomology groups restricts to the parabolic classes. -/
theorem parabolicHeckeAdjoint_of_levelOne (d : ℕ) (τ τ' : ℤ)
    (π : groupCohomology.H1 (arithmeticBinaryRep d τ) →ₗ[ℂ]
      groupCohomology.H1 (arithmeticBinaryRep d τ') →ₗ[ℂ] ℂ) (κ : Nat.Primes → ℂ)
    (h : ∀ p : Nat.Primes, IsHeckeAdjoint π (LevelOneHeckeH1.arithmeticHecke d τ p)
      (LevelOneHeckeH1.arithmeticHecke d τ' p) (κ p)) :
    ParabolicHeckeAdjoint d τ τ'
      (π.compl₁₂ (parabolicH1 (arithmeticBinaryRep d τ)).subtype
        (parabolicH1 (arithmeticBinaryRep d τ')).subtype) κ :=
  fun p x y => h p x.1 y.1

/-- **The pairing functional of an eigen-edge.**  Let `S'` be a `κ`-adjoint of `S` for `π`, let `x`
satisfy the edge relation `a x + s S x = c x`, and let `y'` be the image of `y` under the dual
edge formula `y' = a y + s' S' y`.  If `s' = s κ`, then `π x y' = c · π x y`. -/
theorem pairing_eigen_pointwise {X Y : Type*} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y]
    [Module ℂ Y] (π : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ) (S : Module.End ℂ X) (S' : Module.End ℂ Y) (κ : ℂ)
    (hadj : IsHeckeAdjoint π S S' κ) (a s s' c : ℂ) (hss : s' = s * κ) {x : X}
    (hx : a • x + s • S x = c • x) {y y' : Y} (hy : y' = a • y + s' • S' y) :
    π x y' = c * π x y := by
  have h1 : a * π x y + s * π (S x) y = c * π x y := by
    have h := congrArg (fun z => π z y) hx
    simpa using h
  have h2 : π (S x) y = κ * π x (S' y) := hadj x y
  rw [hy, hss]
  simp only [map_add, map_smul, smul_eq_mul]
  linear_combination h1 - s * h2

/-- `(q^{k+2})⁻¹ = (q^{k+1})⁻¹ q⁻¹`. -/
theorem inv_pow_add_two (q : ℂ) (k : ℕ) : (q ^ (k + 2))⁻¹ = (q ^ (k + 1))⁻¹ * q⁻¹ := by
  have h : q ^ (k + 2) = q ^ (k + 1) * q := pow_succ q (k + 1)
  rw [h, mul_inv]

/-- **The untwisted good line against the identity plane.**  Let `π` be the parabolic cup pairing
of `Sym^{n+1}` with `Sym^{n+1} ⊗ det⁻¹` (`n` odd), and assume it is Hecke adjoint with the scalar
`p^{-1}`.  If `x` is an eigen-edge of the good line (`x + p^{-(n+1)} T_p x = c x`) and `y'` is the
image `y' = y + p^{-(n+2)} T_p y` of the identity-plane edge, then `π x y' = c π x y`. -/
theorem goodLine_identityPlane_pairing_eigen (n : ℕ) (hodd : Odd n) (p : Nat.Primes)
    (hadj : ParabolicHeckeAdjoint (n + 1) 0 (-1)
      (parabolicPairing (twistedPairing_goodLine_trivial hodd)) (heckeScalar 0 (-1)))
    {x : parabolicH1 (arithmeticBinaryRep (n + 1) 0)} (c : ℂ)
    (hx : x + ((((p.val : ℕ) : ℂ)) ^ (n + 1))⁻¹ • parabolicHecke (n + 1) 0 p x = c • x)
    {y y' : parabolicH1 (arithmeticBinaryRep (n + 1) (-1))}
    (hy : y' = y + ((((p.val : ℕ) : ℂ)) ^ (n + 2))⁻¹ • parabolicHecke (n + 1) (-1) p y) :
    parabolicPairing (twistedPairing_goodLine_trivial hodd) x y' =
      c * parabolicPairing (twistedPairing_goodLine_trivial hodd) x y := by
  refine pairing_eigen_pointwise _ (parabolicHecke (n + 1) 0 p) (parabolicHecke (n + 1) (-1) p)
    (heckeScalar 0 (-1) p) (hadj p) 1 ((((p.val : ℕ) : ℂ) ^ (n + 1))⁻¹)
    ((((p.val : ℕ) : ℂ) ^ (n + 2))⁻¹) c ?_ (by rw [one_smul]; exact hx)
    (by rw [one_smul]; exact hy)
  rw [heckeScalar_zero_neg_one]
  exact inv_pow_add_two _ n

/-- **The odd-twisted good line against the odd-twisted identity plane.**  Let `π` be the
parabolic cup pairing of `Sym^{n+1} ⊗ det⁻¹` with `Sym^{n+1}` (`n` odd), Hecke adjoint with the
scalar `p`.  If `x` is an eigen-edge of the good line (`a x + p^{-(n+2)} T_p x = c x`, with `a` the
sign) and `y' = a y + p^{-(n+1)} T_p y`, then `π x y' = c π x y`. -/
theorem goodLine_identityPlane_odd_pairing_eigen (n : ℕ) (hodd : Odd n) (p : Nat.Primes)
    (hadj : ParabolicHeckeAdjoint (n + 1) (-1) 0
      (parabolicPairing (twistedPairing_goodLine_odd hodd)) (heckeScalar (-1) 0))
    (a : ℂ) {x : parabolicH1 (arithmeticBinaryRep (n + 1) (-1))} (c : ℂ)
    (hx : a • x + ((((p.val : ℕ) : ℂ)) ^ (n + 2))⁻¹ • parabolicHecke (n + 1) (-1) p x = c • x)
    {y y' : parabolicH1 (arithmeticBinaryRep (n + 1) 0)}
    (hy : y' = a • y + ((((p.val : ℕ) : ℂ)) ^ (n + 1))⁻¹ • parabolicHecke (n + 1) 0 p y) :
    parabolicPairing (twistedPairing_goodLine_odd hodd) x y' =
      c * parabolicPairing (twistedPairing_goodLine_odd hodd) x y := by
  refine pairing_eigen_pointwise _ (parabolicHecke (n + 1) (-1) p) (parabolicHecke (n + 1) 0 p)
    (heckeScalar (-1) 0 p) (hadj p) a ((((p.val : ℕ) : ℂ) ^ (n + 2))⁻¹)
    ((((p.val : ℕ) : ℂ) ^ (n + 1))⁻¹) c ?_ hx hy
  have hp : ((p.val : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr p.property.ne_zero
  rw [heckeScalar_neg_one_zero, inv_pow_add_two, mul_assoc, inv_mul_cancel₀ hp, mul_one]

end TernaryPeriodPolynomials.BoundaryDuality.AdjointLevelOne
