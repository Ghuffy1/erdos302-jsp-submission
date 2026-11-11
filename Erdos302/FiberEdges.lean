import Erdos302.Specification
import Erdos302.RoughPart

namespace Erdos302

theorem retainedTriple_same_rough {V a b c : ℕ} (ht : RetainedTriple V a b c) :
    roughFactor (primeSet V) a = roughFactor (primeSet V) b ∧
      roughFactor (primeSet V) a = roughFactor (primeSet V) c := by
  obtain ⟨g, u, v, hg, hu, huv, hcop, hsU, hsV, hsW, rfl, rfl, rfl⟩ := ht
  have hUV := Nat.mul_mem_factoredNumbers hsU hsV
  have hUW := Nat.mul_mem_factoredNumbers hsU hsW
  have hVW := Nat.mul_mem_factoredNumbers hsV hsW
  simp only [Nat.mul_assoc]
  rw [roughFactor_mul_smooth hg.ne' hUV, roughFactor_mul_smooth hg.ne' hUW,
    roughFactor_mul_smooth hg.ne' hVW]
  exact ⟨rfl, rfl⟩

theorem retainedTriple_of_same_rough {V a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hbc : b < c) (heq : ReciprocalEquation a b c)
    (hab : roughFactor (primeSet V) a = roughFactor (primeSet V) b)
    (hac : roughFactor (primeSet V) a = roughFactor (primeSet V) c) :
    RetainedTriple V a b c := by
  have hc : 0 < c := lt_trans hb hbc
  obtain ⟨g, u, v, hg, hu, huv, hcop, haEq, hbEq, hcEq⟩ :=
    exists_parametrization ha hb hbc heq
  have hqa : roughFactor (primeSet V) a ∣ a := roughFactor_dvd _ ha.ne'
  have hqb : roughFactor (primeSet V) a ∣ b := hab ▸ roughFactor_dvd _ hb.ne'
  have hqc : roughFactor (primeSet V) a ∣ c := hac ▸ roughFactor_dvd _ hc.ne'
  have hqg : roughFactor (primeSet V) a ∣ g := by
    have h := Nat.dvd_gcd hqa (Nat.dvd_gcd hqb hqc)
    have hGCD : Nat.gcd a (Nat.gcd b c) = g := by
      rw [haEq, hbEq, hcEq, parametric_gcd hcop]
    rwa [hGCD] at h
  have hUV : u * v ∈ Nat.factoredNumbers (primeSet V) :=
    smooth_of_factor_and_rough_dvd ha.ne' (by simpa [mul_assoc] using haEq) hqg
  have hUW : u * (u + v) ∈ Nat.factoredNumbers (primeSet V) :=
    smooth_of_factor_and_rough_dvd hb.ne' (by simpa [mul_assoc] using hbEq) (hab ▸ hqg)
  have hsU : u ∈ Nat.factoredNumbers (primeSet V) :=
    Nat.mem_factoredNumbers_of_dvd hUV ⟨v, rfl⟩
  have hsV : v ∈ Nat.factoredNumbers (primeSet V) :=
    Nat.mem_factoredNumbers_of_dvd hUV ⟨u, by ring⟩
  have hsW : u + v ∈ Nat.factoredNumbers (primeSet V) :=
    Nat.mem_factoredNumbers_of_dvd hUW ⟨u, by ring⟩
  exact ⟨g, u, v, hg, hu, huv, hcop, hsU, hsV, hsW, haEq, hbEq, hcEq⟩

theorem retainedTriple_iff {V a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hbc : b < c) :
    RetainedTriple V a b c ↔ ReciprocalEquation a b c ∧
      roughFactor (primeSet V) a = roughFactor (primeSet V) b ∧
      roughFactor (primeSet V) a = roughFactor (primeSet V) c := by
  constructor
  · intro ht
    have hr := retainedTriple_same_rough ht
    obtain ⟨g, u, v, hg, hu, huv, _, _, _, _, rfl, rfl, rfl⟩ := ht
    exact ⟨(parametric_triple hg hu huv).1, hr⟩
  · rintro ⟨heq, hab, hac⟩
    exact retainedTriple_of_same_rough ha hb hbc heq hab hac

theorem noTriple_of_relaxed_of_one_fiber {V : ℕ} {A : Finset ℕ}
    (hpos : ∀ a ∈ A, 0 < a) (hfree : RelaxedFree V A)
    (q : ℕ) (hq : ∀ a ∈ A, roughFactor (primeSet V) a = q) :
    NoUnitFractionTriple A := by
  intro a ha b hb c hc _ _ hbc heq
  have hab : roughFactor (primeSet V) a = roughFactor (primeSet V) b := by rw [hq a ha, hq b hb]
  have hac : roughFactor (primeSet V) a = roughFactor (primeSet V) c := by rw [hq a ha, hq c hc]
  rcases lt_or_gt_of_ne hbc with hlt | hgt
  · exact hfree a ha b hb c hc (retainedTriple_of_same_rough
      (hpos a ha) (hpos b hb) hlt heq hab hac)
  · exact hfree a ha c hc b hb (retainedTriple_of_same_rough
      (hpos a ha) (hpos c hc) hgt (reciprocalEquation_symm.mp heq) hac hab)

theorem relaxedFree_iff_fibers {V : ℕ} {A : Finset ℕ} (hpos : ∀ a ∈ A, 0 < a) :
    RelaxedFree V A ↔ ∀ q : ℕ,
      NoUnitFractionTriple (A.filter (fun n => roughFactor (primeSet V) n = q)) := by
  classical
  constructor
  · intro h q
    apply noTriple_of_relaxed_of_one_fiber
    · intro a ha
      exact hpos a (Finset.mem_filter.mp ha).1
    · exact relaxedFree_mono (Finset.filter_subset _ _) h
    · intro a ha
      exact (Finset.mem_filter.mp ha).2
  · intro h a ha b hb c hc ht
    have hr := retainedTriple_same_rough ht
    have ha' : a ∈ A.filter (fun n => roughFactor (primeSet V) n = roughFactor (primeSet V) a) :=
      Finset.mem_filter.mpr ⟨ha, rfl⟩
    have hb' : b ∈ A.filter (fun n => roughFactor (primeSet V) n = roughFactor (primeSet V) a) :=
      Finset.mem_filter.mpr ⟨hb, hr.1.symm⟩
    have hc' : c ∈ A.filter (fun n => roughFactor (primeSet V) n = roughFactor (primeSet V) a) :=
      Finset.mem_filter.mpr ⟨hc, hr.2.symm⟩
    obtain ⟨g, u, v, hg, hu, huv, _, _, _, _, haEq, hbEq, hcEq⟩ := ht
    obtain ⟨heq, hab, hbc⟩ := parametric_triple hg hu huv
    simp only [← haEq, ← hbEq, ← hcEq] at heq hab hbc
    exact h _ a ha' b hb' c hc' hab.ne (lt_trans hab hbc).ne hbc.ne heq

end Erdos302
