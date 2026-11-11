import Erdos302.FiniteApproximation

namespace Erdos302

def smoothFactor (P : Finset ℕ) (n : ℕ) : ℕ :=
  (n.primeFactorsList.filter (· ∈ P)).prod

def roughFactor (P : Finset ℕ) (n : ℕ) : ℕ :=
  (n.primeFactorsList.filter (· ∉ P)).prod

def IsRough (P : Finset ℕ) (q : ℕ) : Prop :=
  q ≠ 0 ∧ ∀ p ∈ P, p.Prime → ¬ p ∣ q

theorem smoothFactor_mem (P : Finset ℕ) (n : ℕ) :
    smoothFactor P n ∈ Nat.factoredNumbers P :=
  Nat.prod_mem_factoredNumbers P n

theorem smoothFactor_ne_zero (P : Finset ℕ) (n : ℕ) : smoothFactor P n ≠ 0 :=
  (smoothFactor_mem P n).1

theorem roughFactor_ne_zero (P : Finset ℕ) (n : ℕ) : roughFactor P n ≠ 0 := by
  apply List.prod_ne_zero
  intro h
  have hp := List.mem_of_mem_filter h
  exact (Nat.pos_of_mem_primeFactorsList hp).ne' rfl

theorem roughFactor_isRough (P : Finset ℕ) (n : ℕ) : IsRough P (roughFactor P n) := by
  refine ⟨roughFactor_ne_zero P n, ?_⟩
  intro p hp hprime hdiv
  have hmem := mem_list_primes_of_dvd_prod hprime.prime
    (fun _ h => (Nat.prime_of_mem_primeFactorsList (List.mem_of_mem_filter h)).prime) hdiv
  have hnot : p ∉ P := by simpa using (List.mem_filter.mp hmem).2
  exact hnot hp

theorem smoothFactor_mul_roughFactor {P : Finset ℕ} {n : ℕ} (hn : n ≠ 0) :
    smoothFactor P n * roughFactor P n = n := by
  calc
    smoothFactor P n * roughFactor P n =
        ((n.primeFactorsList.filter (· ∈ P)) ++
          n.primeFactorsList.filter (· ∉ P)).prod := by simp [smoothFactor, roughFactor]
    _ = n.primeFactorsList.prod := by
      simpa only [decide_not] using (List.filter_append_perm (· ∈ P) n.primeFactorsList).prod_eq
    _ = n := Nat.prod_primeFactorsList hn

theorem roughFactor_mul_smoothFactor {P : Finset ℕ} {n : ℕ} (hn : n ≠ 0) :
    roughFactor P n * smoothFactor P n = n := by
  simpa only [mul_comm] using smoothFactor_mul_roughFactor (P := P) hn

theorem roughFactor_dvd (P : Finset ℕ) {n : ℕ} (hn : n ≠ 0) : roughFactor P n ∣ n :=
  ⟨smoothFactor P n, (roughFactor_mul_smoothFactor hn).symm⟩

theorem smoothFactor_mul (P : Finset ℕ) {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    smoothFactor P (a * b) = smoothFactor P a * smoothFactor P b := by
  calc
    smoothFactor P (a * b) =
        ((a.primeFactorsList ++ b.primeFactorsList).filter (· ∈ P)).prod :=
      (List.Perm.filter _ (Nat.perm_primeFactorsList_mul ha hb)).prod_eq
    _ = smoothFactor P a * smoothFactor P b := by simp [smoothFactor]

theorem roughFactor_mul (P : Finset ℕ) {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    roughFactor P (a * b) = roughFactor P a * roughFactor P b := by
  calc
    roughFactor P (a * b) =
        ((a.primeFactorsList ++ b.primeFactorsList).filter (· ∉ P)).prod :=
      (List.Perm.filter _ (Nat.perm_primeFactorsList_mul ha hb)).prod_eq
    _ = roughFactor P a * roughFactor P b := by simp [roughFactor]

theorem roughFactor_of_smooth {P : Finset ℕ} {n : ℕ}
    (hn : n ∈ Nat.factoredNumbers P) : roughFactor P n = 1 := by
  have hnil : n.primeFactorsList.filter (fun p => !decide (p ∈ P)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro p hp
    simpa using hn.2 p hp
  simp [roughFactor, hnil]

theorem smoothFactor_of_smooth {P : Finset ℕ} {n : ℕ}
    (hn : n ∈ Nat.factoredNumbers P) : smoothFactor P n = n := by
  have h := smoothFactor_mul_roughFactor (P := P) hn.1
  simpa only [roughFactor_of_smooth hn, mul_one] using h

theorem smoothFactor_of_rough {P : Finset ℕ} {q : ℕ} (hq : IsRough P q) :
    smoothFactor P q = 1 := by
  have hnil : q.primeFactorsList.filter (· ∈ P) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactorsList hp
    have hdiv := (Nat.mem_primeFactorsList hq.1).mp hp
    simpa using fun hpP => hq.2 p hpP hprime hdiv.2
  simp [smoothFactor, hnil]

theorem roughFactor_of_rough {P : Finset ℕ} {q : ℕ} (hq : IsRough P q) :
    roughFactor P q = q := by
  have h := smoothFactor_mul_roughFactor (P := P) hq.1
  simpa only [smoothFactor_of_rough hq, one_mul] using h

theorem roughFactor_mul_smooth {P : Finset ℕ} {q s : ℕ}
    (hq : q ≠ 0) (hs : s ∈ Nat.factoredNumbers P) :
    roughFactor P (q * s) = roughFactor P q := by
  rw [roughFactor_mul P hq hs.1, roughFactor_of_smooth hs, mul_one]

theorem factorization_unique {P : Finset ℕ} {n q s : ℕ}
    (hq : IsRough P q) (hs : s ∈ Nat.factoredNumbers P) (hn : n = q * s) :
    q = roughFactor P n ∧ s = smoothFactor P n := by
  rw [hn, roughFactor_mul_smooth hq.1 hs, roughFactor_of_rough hq,
    smoothFactor_mul P hq.1 hs.1, smoothFactor_of_rough hq,
    smoothFactor_of_smooth hs, one_mul]
  exact ⟨rfl, rfl⟩

theorem smooth_of_factor_and_rough_dvd {P : Finset ℕ} {n g t : ℕ}
    (hn : n ≠ 0) (hfactor : n = g * t) (hdiv : roughFactor P n ∣ g) :
    t ∈ Nat.factoredNumbers P := by
  obtain ⟨k, hk⟩ := hdiv
  have hs : smoothFactor P n = k * t := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (roughFactor_ne_zero P n))
    calc
      roughFactor P n * smoothFactor P n = n := roughFactor_mul_smoothFactor hn
      _ = g * t := hfactor
      _ = roughFactor P n * (k * t) := by rw [hk]; ring
  apply Nat.mem_factoredNumbers_of_dvd (smoothFactor_mem P n)
  exact ⟨k, by simpa only [mul_comm] using hs⟩

end Erdos302
