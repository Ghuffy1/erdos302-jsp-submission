import Erdos302.FiniteApproximation
import Erdos302.Parameters
import Erdos302.LimitBridge

/-!
Exact statements of the density and quantitative approximation results.

`DensityLimitStatement`, `RemovalEstimateStatement`, and
`EffectiveApproximationStatement` below define the propositions proved in
`Erdos302.Solution`. The fixed-prime limit is proved in `Erdos302.DensitySeries`.
-/

namespace Erdos302

open Filter
open scoped Topology

def primeSet (V : ℕ) : Finset ℕ := (Finset.range (2 * V + 1)).filter Nat.Prime

theorem primeSet_mono {V W : ℕ} (hVW : V ≤ W) : primeSet V ⊆ primeSet W := by
  intro p hp
  simp only [primeSet, Finset.mem_filter, Finset.mem_range] at hp ⊢
  exact ⟨by omega, hp.2⟩

def RetainedTriple (V a b c : ℕ) : Prop :=
  ∃ g u v : ℕ, 0 < g ∧ 0 < u ∧ u < v ∧ Nat.Coprime u v ∧
    u ∈ Nat.factoredNumbers (primeSet V) ∧
    v ∈ Nat.factoredNumbers (primeSet V) ∧
    u + v ∈ Nat.factoredNumbers (primeSet V) ∧
    a = g * u * v ∧ b = g * u * (u + v) ∧ c = g * v * (u + v)

def RelaxedFree (V : ℕ) (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ¬ RetainedTriple V a b c

theorem relaxedFree_empty (V : ℕ) : RelaxedFree V ∅ := by
  simp [RelaxedFree]

theorem noTriple_implies_relaxedFree {V : ℕ} {A : Finset ℕ}
    (hA : NoUnitFractionTriple A) : RelaxedFree V A := by
  intro a ha b hb c hc ht
  obtain ⟨g, u, v, hg, hu, huv, _, _, _, _, rfl, rfl, rfl⟩ := ht
  obtain ⟨heq, hab, hbc⟩ := parametric_triple hg hu huv
  exact hA _ ha _ hb _ hc hab.ne (lt_trans hab hbc).ne hbc.ne heq

theorem relaxedFree_mono {V : ℕ} {A B : Finset ℕ}
    (hAB : A ⊆ B) (hB : RelaxedFree V B) : RelaxedFree V A := by
  intro a ha b hb c hc
  exact hB a (hAB ha) b (hAB hb) c (hAB hc)

theorem retainedTriple_mono {V W a b c : ℕ} (hVW : V ≤ W)
    (ht : RetainedTriple V a b c) : RetainedTriple W a b c := by
  obtain ⟨g, u, v, hg, hu, huv, hcop, hsU, hsV, hsW, ha, hb, hc⟩ := ht
  have move {n : ℕ} (hn : n ∈ Nat.factoredNumbers (primeSet V)) :
      n ∈ Nat.factoredNumbers (primeSet W) := by
    rw [Nat.mem_factoredNumbers_iff_primeFactors_subset] at hn ⊢
    exact ⟨hn.1, hn.2.trans (primeSet_mono hVW)⟩
  exact ⟨g, u, v, hg, hu, huv, hcop, move hsU, move hsV, move hsW, ha, hb, hc⟩

noncomputable def relaxedExtremal (V N : ℕ) : ℕ :=
  maximumCard (RelaxedFree V) (Finset.Icc 1 N)

theorem extremal_le_relaxed (V N : ℕ) : extremal N ≤ relaxedExtremal V N := by
  obtain ⟨A, hA, hfree, hcard⟩ := exists_extremizer N
  rw [← hcard]
  exact card_le_maximumCard hA (noTriple_implies_relaxedFree hfree)

theorem relaxedExtremal_antitone (N : ℕ) : Antitone (fun V => relaxedExtremal V N) := by
  intro V W hVW
  obtain ⟨A, hA, hfree, hcard⟩ := exists_maximumCard (relaxedFree_empty W) (Finset.Icc 1 N)
  change maximumCard (RelaxedFree W) (Finset.Icc 1 N) ≤
    maximumCard (RelaxedFree V) (Finset.Icc 1 N)
  rw [← hcard]
  apply card_le_maximumCard hA
  intro a ha b hb c hc ht
  exact hfree a ha b hb c hc (retainedTriple_mono hVW ht)

noncomputable def U (V : ℕ) : ℝ := smoothUpperValue (primeSet V)

/-- The proposed constant, over exactly the cutoffs V >= 4. -/
noncomputable def claimedConstant : ℝ := sInf (Set.range (fun V : ℕ => U (V + 4)))

/-- The density-limit statement, matching the arbitrary-extremizer
function formulation of the original problem. -/
def DensityLimitStatement : Prop :=
  ∀ f : ℕ → ℕ, (∀ N, IsMaxNoTripleCard N (f N)) →
    Tendsto (fun N : ℕ => (f N : ℝ) / N) atTop (𝓝 claimedConstant)

/-- The quantitative deletion statement from the private refinement. -/
def RemovalEstimateStatement : Prop :=
  ∀ N V K : ℕ, 4 ≤ N → 4 ≤ V →
    0 ≤ (relaxedExtremal V N : ℝ) - extremal N ∧
    (relaxedExtremal V N : ℝ) - extremal N ≤
      (N : ℝ) * (500000 * Parameters.z ^ (-(K : ℤ)) +
        10 ^ 23 * Parameters.q ^ (3 * K) *
        (Real.rpow (Real.log V) (-(7 / 80 : ℝ)) +
          Real.rpow (Real.log N) (-(7 / 80 : ℝ))))

/-- The approximation-rate statement for the same U and C. -/
def EffectiveApproximationStatement : Prop :=
  ∀ V : ℕ, 4 ≤ V →
    0 ≤ U V - claimedConstant ∧
    U V - claimedConstant ≤ ((10 : ℝ) ^ 23 + 561000) *
      Real.rpow (Real.log V) (-(1 / 140 : ℝ))

/-- Finite-prime asymptotic target, proved by `Erdos302.fixedPrimeLimit`. -/
def FixedPrimeLimitStatement : Prop :=
  ∀ V : ℕ, 4 ≤ V →
    Tendsto (fun N : ℕ => (relaxedExtremal V N : ℝ) / N) atTop (𝓝 (U V))

end Erdos302
