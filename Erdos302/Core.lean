import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic

/-!
Private formalization of the finite arithmetic in Erdős problem 302.
The definition of `NoUnitFractionTriple` matches the original distinct-triple
problem. This module alone does not prove the density-limit theorem.
The finite problem definitions follow the Formal Conjectures Authors' 2026
ErdosProblems/302.lean (Apache-2.0), preserved in the parent source archive.
-/

namespace Erdos302

open Finset

/-- The original reciprocal equation, with the three distinctness conditions
kept in the admissibility definition below. -/
def ReciprocalEquation (a b c : ℕ) : Prop :=
  (1 : ℚ) / a = (1 : ℚ) / b + (1 : ℚ) / c

def NoUnitFractionTriple (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a ≠ b → a ≠ c → b ≠ c →
    ¬ ReciprocalEquation a b c

def IsMaxNoTripleCard (N m : ℕ) : Prop :=
  IsGreatest {k | ∃ A ⊆ Finset.Icc 1 N,
    NoUnitFractionTriple A ∧ A.card = k} m

theorem reciprocalEquation_iff {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ReciprocalEquation a b c ↔ b * c = a * (b + c) := by
  have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
  have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  have hc' : (c : ℚ) ≠ 0 := by exact_mod_cast hc.ne'
  unfold ReciprocalEquation
  constructor
  · intro h
    field_simp at h
    have h' : b * c = a * (c + b) := by exact_mod_cast h
    simpa only [add_comm] using h'
  · intro h
    have h' : (b : ℚ) * c = a * (b + c) := by exact_mod_cast h
    field_simp
    nlinarith

theorem noUnitFractionTriple_mono {A B : Finset ℕ}
    (hAB : A ⊆ B) (hB : NoUnitFractionTriple B) :
    NoUnitFractionTriple A := by
  intro a ha b hb c hc hab hac hbc
  exact hB a (hAB ha) b (hAB hb) c (hAB hc) hab hac hbc

theorem noUnitFractionTriple_empty : NoUnitFractionTriple ∅ := by
  simp [NoUnitFractionTriple]

noncomputable def admissibleSubsets (N : ℕ) : Finset (Finset ℕ) := by
  classical
  exact (Finset.Icc 1 N).powerset.filter NoUnitFractionTriple

noncomputable def extremal (N : ℕ) : ℕ :=
  (admissibleSubsets N).sup Finset.card

theorem mem_admissibleSubsets {N : ℕ} {A : Finset ℕ} :
    A ∈ admissibleSubsets N ↔ A ⊆ Finset.Icc 1 N ∧ NoUnitFractionTriple A := by
  classical
  simp [admissibleSubsets]

theorem admissibleSubsets_nonempty (N : ℕ) : (admissibleSubsets N).Nonempty := by
  exact ⟨∅, mem_admissibleSubsets.mpr ⟨empty_subset _, noUnitFractionTriple_empty⟩⟩

theorem card_le_extremal {N : ℕ} {A : Finset ℕ}
    (hA : A ⊆ Finset.Icc 1 N) (hfree : NoUnitFractionTriple A) :
    A.card ≤ extremal N := by
  exact Finset.le_sup (f := Finset.card) (mem_admissibleSubsets.mpr ⟨hA, hfree⟩)

theorem exists_extremizer (N : ℕ) :
    ∃ A ⊆ Finset.Icc 1 N, NoUnitFractionTriple A ∧ A.card = extremal N := by
  obtain ⟨A, hA, hcard⟩ :=
    Finset.exists_mem_eq_sup (admissibleSubsets N) (admissibleSubsets_nonempty N) Finset.card
  exact ⟨A, (mem_admissibleSubsets.mp hA).1, (mem_admissibleSubsets.mp hA).2, hcard.symm⟩

theorem extremal_isMax (N : ℕ) : IsMaxNoTripleCard N (extremal N) := by
  refine ⟨exists_extremizer N, ?_⟩
  rintro m ⟨A, hA, hfree, rfl⟩
  exact card_le_extremal hA hfree

theorem isMax_iff_eq_extremal {N m : ℕ} :
    IsMaxNoTripleCard N m ↔ m = extremal N := by
  constructor
  · intro hm
    exact le_antisymm ((extremal_isMax N).2 hm.1) (hm.2 (extremal_isMax N).1)
  · rintro rfl
    exact extremal_isMax N

theorem extremal_le (N : ℕ) : extremal N ≤ N := by
  obtain ⟨A, hA, _, hcard⟩ := exists_extremizer N
  have h := Finset.card_le_card hA
  rw [hcard] at h
  simpa using h

theorem extremal_mono : Monotone extremal := by
  intro N M hNM
  obtain ⟨A, hA, hfree, hcard⟩ := exists_extremizer N
  rw [← hcard]
  exact card_le_extremal (hA.trans (Finset.Icc_subset_Icc_right hNM)) hfree

theorem reciprocalEquation_symm {a b c : ℕ} :
    ReciprocalEquation a b c ↔ ReciprocalEquation a c b := by
  simp [ReciprocalEquation, add_comm]

theorem reciprocalEquation_first_lt {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : ReciprocalEquation a b c) : a < b ∧ a < c := by
  have hEq := (reciprocalEquation_iff ha hb hc).mp h
  constructor <;> nlinarith

/-- Every positive primitive-parameter tuple gives a valid ordered triple. -/
theorem parametric_triple {g u v : ℕ}
    (hg : 0 < g) (hu : 0 < u) (huv : u < v) :
    ReciprocalEquation (g * u * v) (g * u * (u + v)) (g * v * (u + v)) ∧
    g * u * v < g * u * (u + v) ∧
    g * u * (u + v) < g * v * (u + v) := by
  have hv : 0 < v := lt_trans hu huv
  have hw : 0 < u + v := by omega
  refine ⟨?_, ?_, ?_⟩
  · apply (reciprocalEquation_iff (by positivity) (by positivity) (by positivity)).mpr
    ring
  · nlinarith [Nat.mul_pos hg hu]
  · exact Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_left huv hg) hw

/-- Every positive ordered solution has the coprime parametrization used in
the manuscripts. No number-theoretic estimate is assumed here. -/
theorem exists_parametrization {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hbc : b < c)
    (h : ReciprocalEquation a b c) :
    ∃ g u v : ℕ, 0 < g ∧ 0 < u ∧ u < v ∧ Nat.Coprime u v ∧
      a = g * u * v ∧ b = g * u * (u + v) ∧ c = g * v * (u + v) := by
  have hc : 0 < c := lt_trans hb hbc
  obtain ⟨d, u, v, hd, hcop, hbu, hcv⟩ :=
    Nat.exists_coprime' (Nat.gcd_pos_of_pos_left c hb)
  have hu : 0 < u := by
    by_contra hnot
    have : u = 0 := by omega
    simp [this] at hbu
    omega
  have hv : 0 < v := by
    by_contra hnot
    have : v = 0 := by omega
    simp [this] at hcv
    omega
  have huv : u < v := (Nat.mul_lt_mul_right hd).mp (by
    simpa only [← hbu, ← hcv] using hbc)
  have hw : 0 < u + v := by omega
  have hEq := (reciprocalEquation_iff ha hb hc).mp h
  rw [hbu, hcv] at hEq
  have heq : d * u * v = a * (u + v) := by
    apply Nat.eq_of_mul_eq_mul_left hd
    nlinarith [hEq]
  have hcop' : Nat.Coprime (u + v) (u * v) := by
    apply Nat.Coprime.mul_right
    · simpa using hcop.symm
    · simpa using hcop
  have hdiv : u + v ∣ d := by
    apply hcop'.dvd_of_dvd_mul_right
    exact ⟨a, by nlinarith [heq]⟩
  obtain ⟨g, hgd⟩ := hdiv
  have hg : 0 < g := by nlinarith [hgd]
  refine ⟨g, u, v, hg, hu, huv, hcop, ?_, ?_, ?_⟩
  · apply Nat.eq_of_mul_eq_mul_left hw
    rw [hgd] at heq
    nlinarith [heq]
  · rw [hbu, hgd]
    ring
  · rw [hcv, hgd]
    ring

theorem primitive_gcd {u v : ℕ} (h : Nat.Coprime u v) :
    Nat.gcd (u * v) (Nat.gcd (u * (u + v)) (v * (u + v))) = 1 := by
  have h1 : Nat.Coprime u (u + v) := by simpa using h
  have h2 : Nat.Coprime v (u + v) := by simpa [add_comm] using h.symm
  have h3 : Nat.Coprime (u * v) (u + v) := h1.mul_left h2
  rw [Nat.gcd_mul_right, h.gcd_eq_one, one_mul]
  exact h3.gcd_eq_one

theorem parametric_gcd {g u v : ℕ} (h : Nat.Coprime u v) :
    Nat.gcd (g * u * v)
      (Nat.gcd (g * u * (u + v)) (g * v * (u + v))) = g := by
  simp only [Nat.mul_assoc, Nat.gcd_mul_left]
  rw [primitive_gcd h, mul_one]

/-- Uniqueness is essential: the scale and primitive parameters are genuinely
determined by the ordered triple, rather than merely giving a surjection. -/
theorem parametrization_unique {g u v g' u' v' : ℕ}
    (hg : 0 < g) (hu : 0 < u)
    (hcop : Nat.Coprime u v) (hcop' : Nat.Coprime u' v')
    (ha : g * u * v = g' * u' * v')
    (hb : g * u * (u + v) = g' * u' * (u' + v'))
    (hc : g * v * (u + v) = g' * v' * (u' + v')) :
    g = g' ∧ u = u' ∧ v = v' := by
  have hgEq : g = g' := by
    calc
      g = Nat.gcd (g * u * v)
          (Nat.gcd (g * u * (u + v)) (g * v * (u + v))) :=
        (parametric_gcd (g := g) hcop).symm
      _ = Nat.gcd (g' * u' * v')
          (Nat.gcd (g' * u' * (u' + v')) (g' * v' * (u' + v'))) := by rw [ha, hb, hc]
      _ = g' := parametric_gcd hcop'
  subst g'
  have huvEq : u * v = u' * v' := by
    apply Nat.eq_of_mul_eq_mul_left hg
    simpa only [Nat.mul_assoc] using ha
  have huwEq : u * (u + v) = u' * (u' + v') := by
    apply Nat.eq_of_mul_eq_mul_left hg
    simpa only [Nat.mul_assoc] using hb
  have huEq : u = u' := by nlinarith [huvEq, huwEq]
  subst u'
  have hvEq : v = v' := Nat.eq_of_mul_eq_mul_left hu huvEq
  exact ⟨rfl, rfl, hvEq⟩

end Erdos302
