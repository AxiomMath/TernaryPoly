module

public import TernaryPeriodPolynomials.ModularForm.PeriodDetection.Intertwining

@[expose] public section


noncomputable section
namespace TernaryPoly.BinaryCuspPeriodDetection
open BinaryCuspPeriod BinaryCuspPeriodInjective

/-- Nonzero exact forward scalars give the reverse formula with the literal inverse scalar. -/
theorem reverse_of_intertwines (d : ℕ) (hd : Even d)
    (U : Nat.Primes → Module.End ℂ (BinaryComplexPeriod.space ℂ d))
    (c : Nat.Primes → ℂ) (hc : ∀ p,c p≠0) (h : Intertwines d hd U c)
    (p : Nat.Primes) (f : Forms d) :
    U p (periodMap d hd f)=(c p)⁻¹ • periodMap d hd (primeHecke d p f) := by
  rw [h p f,smul_smul,inv_mul_cancel₀ (hc p),one_smul]

/-- Surjectivity of the actual period map transfers genuine cusp-Hecke commutativity, with
all exact nonzero intertwining scalars retained. -/
theorem commute_of_intertwines (d : ℕ) (hd : Even d)
    (hsurj : Function.Surjective (periodMap d hd))
    (U : Nat.Primes → Module.End ℂ (BinaryComplexPeriod.space ℂ d))
    (c : Nat.Primes → ℂ) (hc : ∀ p,c p≠0) (h : Intertwines d hd U c)
    (p q : Nat.Primes) : Commute (U p) (U q) := by
  apply LinearMap.ext
  intro v
  obtain ⟨f,rfl⟩ := hsurj v
  change U p (U q (periodMap d hd f))=U q (U p (periodMap d hd f))
  rw [reverse_of_intertwines d hd U c hc h q f,map_smul,
    reverse_of_intertwines d hd U c hc h p (primeHecke d q f),
    reverse_of_intertwines d hd U c hc h p f,map_smul,
    reverse_of_intertwines d hd U c hc h q (primeHecke d p f)]
  have hcomm : primeHecke d p (primeHecke d q f)=primeHecke d q (primeHecke d p f) :=
    LinearMap.congr_fun (primeHecke_commute d p q).eq f
  rw [hcomm,smul_comm]

end TernaryPoly.BinaryCuspPeriodDetection
