module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FiberModel.Abstract

@[expose] public section


/-!
# Literal definitions for Lemma 3.2 (`prop:26-model`)

Transcription of the objects of the paper's fiber model: the set `𝒮` of nonzero
row covectors in `𝔽₃³`, the space `V_n = ℚ[x,y,z]_n`, direct substitution `f ∣ h`, the signed
permutation matrices `h = D π`, the characters `χ₀(h) = sgn π` and `χ₁(h) = ∏ Dᵢᵢ`, the matrix `A`,
and the left action of `GL₃(ℤ)` on `E_{n,t} = Sym^n ⊗ det^{-t}`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FiberModel

open TernaryPoly TernaryPoly.ModThreeGoodAction TernaryPoly.OrdinaryCovectors

/-- The set `𝒮 = 𝔽₃³ ∖ {0}` of nonzero row covectors. -/
abbrev Covectors : Type := {r : Fin 3 → ZMod 3 // r ≠ 0}

/-- The coefficient space `V_n = ℚ[x,y,z]_n` of homogeneous polynomials of degree `n`. -/
abbrev V (n : ℕ) : Type := PolynomialGLAction.HomogeneousPoly n

/-- Reduction of an integral matrix modulo three. -/
def mod3 (h : Matrix (Fin 3) (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) (ZMod 3) :=
  h.map (Int.castRingHom (ZMod 3))

/-- Direct substitution `(f ∣ h)(x) = f(h x)`, without determinant twist. -/
def bar (h : Matrix (Fin 3) (Fin 3) ℤ) :
    MvPolynomial (Fin 3) ℚ →ₐ[ℚ] MvPolynomial (Fin 3) ℚ :=
  MvPolynomial.bind₁ fun i => ∑ j, MvPolynomial.C ((h i j : ℤ) : ℚ) * MvPolynomial.X j

/-- The matrix `A` of the paper. -/
def Amat : Matrix (Fin 3) (Fin 3) ℤ := !![0, -1, 0; 1, -1, 0; 0, 0, 1]

/-- The signed permutation matrix `h = D π`, with `D` diagonal with entries `±1`. -/
def signedPermMatrix (D : Fin 3 → ℤˣ) (π : Equiv.Perm (Fin 3)) : Matrix (Fin 3) (Fin 3) ℤ :=
  Matrix.diagonal (fun i => ((D i : ℤˣ) : ℤ)) * π.permMatrix ℤ

/-- The characters `χ₀(Dπ) = sgn π` and `χ₁(Dπ) = ∏ᵢ Dᵢᵢ` of the signed permutation matrices. -/
def chi (t : Fin 2) (D : Fin 3 → ℤˣ) (π : Equiv.Perm (Fin 3)) : ℤ :=
  if t = 0 then ((Equiv.Perm.sign π : ℤˣ) : ℤ) else ∏ i, ((D i : ℤˣ) : ℤ)

theorem act_val (r : NonzeroCovector) (g : IntegralGL) :
    (act r g).1 = Matrix.vecMul r.1 (mod3 g.val) := rfl

/-- The left action of `GL₃(ℤ)` on `E_{n,t} = Sym^n((ℚ³)^*) ⊗ det^{-t}`, i.e.
`g · f (x) = det(g)^{-t} f(g⁻¹ x)`, on the space `V_n`. -/
def coeff (n : ℕ) (t : Fin 2) : Representation ℚ IntegralGL (V n) :=
  PolynomialGLAction.integralAction n (-((t : ℕ) : ℤ))

/-- The functions `F : 𝒮 → V_n` of Lemma 3.2: `F(rh) = χ_t(h) F(r) ∣ h` for every signed
permutation matrix `h = D π` (equation `eq:fiber-signed`), and
`F(r) + F(rA²) ∣ A + F(rA) ∣ A² = 0` (equation `eq:fiber-norm`); covectors are multiplied modulo
three. -/
structure IsFiberFunction (t : Fin 2) (n : ℕ) (F : Covectors → V n) : Prop where
  signed : ∀ (D : Fin 3 → ℤˣ) (π : Equiv.Perm (Fin 3)) (r r' : Covectors),
    r'.1 = Matrix.vecMul r.1 (mod3 (signedPermMatrix D π)) →
      ((F r' : V n) : MvPolynomial (Fin 3) ℚ) =
        (chi t D π : ℚ) • bar (signedPermMatrix D π) (F r)
  norm : ∀ r r₁ r₂ : Covectors,
    r₁.1 = Matrix.vecMul r.1 (mod3 (Amat * Amat)) → r₂.1 = Matrix.vecMul r.1 (mod3 Amat) →
      ((F r : V n) : MvPolynomial (Fin 3) ℚ) + bar Amat (F r₁) + bar (Amat * Amat) (F r₂) = 0

end TernaryPeriodPolynomials.Argument.FiberModel
