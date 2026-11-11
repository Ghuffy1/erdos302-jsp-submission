import Erdos302.ResidueCounts
import Erdos302.CrtResidues
import Mathlib.Data.Nat.GCD.Prime

namespace Erdos302

noncomputable def residueDensity (U : ∀ p : ℕ, Finset (ZMod p × ZMod p)) : ArithmeticFunction ℝ :=
  ArithmeticFunction.prodPrimeFactors (fun p => (U p).card / (p : ℝ) ^ 2)

theorem residueDensity_prime (U : ∀ p : ℕ, Finset (ZMod p × ZMod p)) {p : ℕ} (hp : p.Prime) :
    residueDensity U p = (U p).card / (p : ℝ) ^ 2 := by
  simp only [residueDensity, ArithmeticFunction.prodPrimeFactors_apply hp.ne_zero,
    hp.primeFactors, Finset.prod_singleton]

theorem residueDensity_crt (U : ∀ p : ℕ, Finset (ZMod p × ZMod p))
    (q : ℕ) (hq : Squarefree q) :
    residueDensity U q = (crtResiduePairs q hq U).card / (q : ℝ) ^ 2 := by
  rw [card_crtResiduePairs]
  simp only [residueDensity, ArithmeticFunction.prodPrimeFactors_apply hq.ne_zero,
    Nat.cast_prod, Finset.prod_div_distrib, Finset.prod_pow]
  have hprod : (∏ p ∈ q.primeFactors, (p : ℝ)) = (q : ℝ) := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hq]
  rw [hprod]

def residueEvent (U : ∀ p : ℕ, Finset (ZMod p × ZMod p)) (d : ℕ) (t : ℕ × ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ d → ((t.1 : ZMod p), (t.2 : ZMod p)) ∈ U p

noncomputable def residueIndicator (U : ∀ p : ℕ, Finset (ZMod p × ZMod p))
    (d : ℕ) (t : ℕ × ℕ) : ℝ := by
  classical
  exact if residueEvent U d t then 1 else 0

theorem residueEvent_one (U : ∀ p : ℕ, Finset (ZMod p × ZMod p)) (t : ℕ × ℕ) :
    residueEvent U 1 t := by
  intro p hp hp1
  exact (hp.not_dvd_one hp1).elim

theorem residueEvent_lcm (U : ∀ p : ℕ, Finset (ZMod p × ZMod p)) (d e : ℕ) (t : ℕ × ℕ) :
    residueEvent U (d.lcm e) t ↔ residueEvent U d t ∧ residueEvent U e t := by
  constructor
  · intro h
    exact ⟨fun p hp hd => h p hp (hd.trans (Nat.dvd_lcm_left d e)),
      fun p hp he => h p hp (he.trans (Nat.dvd_lcm_right d e))⟩
  · rintro ⟨hd, he⟩ p hp hpe
    rcases hp.dvd_lcm.mp hpe with hpd | hpe
    · exact hd p hp hpd
    · exact he p hp hpe

theorem residueIndicator_lcm (U : ∀ p : ℕ, Finset (ZMod p × ZMod p)) (d e : ℕ) (t : ℕ × ℕ) :
    residueIndicator U d t * residueIndicator U e t = residueIndicator U (d.lcm e) t := by
  classical
  by_cases hd : residueEvent U d t <;> by_cases he : residueEvent U e t <;>
    simp [residueIndicator, residueEvent_lcm, hd, he]

theorem residueEvent_iff_crt (U : ∀ p : ℕ, Finset (ZMod p × ZMod p))
    (q : ℕ) (hq : Squarefree q) (t : ℕ × ℕ) :
    residueEvent U q t ↔ ((t.1 : ZMod q), (t.2 : ZMod q)) ∈ crtResiduePairs q hq U := by
  rw [natCast_mem_crtResiduePairs]
  constructor
  · intro h p hp
    exact h p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)
  · intro h p hp hpq
    exact h p (Nat.mem_primeFactors.mpr ⟨hp, hpq, hq.ne_zero⟩)

theorem sum_residueIndicator (U : ∀ p : ℕ, Finset (ZMod p × ZMod p))
    (q : ℕ) (hq : Squarefree q) (M : ℕ) :
    (∑ t ∈ integerBox M, residueIndicator U q t) = residueBoxCount q M (crtResiduePairs q hq U) := by
  classical
  have hset : (integerBox M).filter (residueEvent U q) =
      (integerBox M).filter (fun t : ℕ × ℕ => ((t.1 : ZMod q), (t.2 : ZMod q)) ∈ crtResiduePairs q hq U) := by
    ext t
    simp only [Finset.mem_filter]
    rw [residueEvent_iff_crt U q hq t]
  simp only [residueIndicator, ← Finset.sum_filter, Finset.sum_const,
    nsmul_eq_mul, mul_one, residueBoxCount]
  rw [hset]

theorem residueIndicator_error (U : ∀ p : ℕ, Finset (ZMod p × ZMod p))
    (q : ℕ) (hq : Squarefree q) (M : ℕ) :
    |(∑ t ∈ integerBox M, residueIndicator U q t) - (M : ℝ) ^ 2 * residueDensity U q| ≤
      2 * M * q + (q : ℝ) ^ 2 := by
  rw [sum_residueIndicator U q hq M, residueDensity_crt U q hq]
  exact residueBoxCount_error (Nat.pos_of_ne_zero hq.ne_zero) M _

noncomputable def avoidingResiduePairs (q M : ℕ) (U : ∀ p : ℕ, Finset (ZMod p × ZMod p)) :
    Finset (ℕ × ℕ) := by
  classical
  exact (integerBox M).filter (fun t =>
    ∀ p ∈ q.primeFactors, ((t.1 : ZMod p), (t.2 : ZMod p)) ∉ U p)

theorem residueIndicator_one (U : ∀ p : ℕ, Finset (ZMod p × ZMod p)) (t : ℕ × ℕ) :
    residueIndicator U 1 t = 1 := by
  simp only [residueIndicator, residueEvent_one, ite_true]

theorem residueIndicator_zero_of_avoiding (U : ∀ p : ℕ, Finset (ZMod p × ZMod p))
    {q M d : ℕ} (hq : q ≠ 0) (hd : d ∣ q) (hd1 : d ≠ 1)
    {t : ℕ × ℕ} (ht : t ∈ avoidingResiduePairs q M U) : residueIndicator U d t = 0 := by
  classical
  obtain ⟨htbox, htavoid⟩ := Finset.mem_filter.mp ht
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hd1
  have hpq := hpd.trans hd
  have hnot : ¬ residueEvent U d t := by
    intro h
    exact htavoid p (Nat.mem_primeFactors.mpr ⟨hp, hpq, hq⟩) (h p hp hpd)
  simp only [residueIndicator, ite_eq_right hnot]

end Erdos302
