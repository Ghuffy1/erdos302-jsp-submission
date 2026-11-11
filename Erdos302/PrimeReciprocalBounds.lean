import Erdos302.ElementaryZeta
import Erdos302.WeightedPrimeLog
import Erdos302.ReciprocalPrimeSums
import Mathlib.NumberTheory.Harmonic.Bounds

namespace Erdos302

theorem reciprocal_le_power_add_log {s p : ℝ} (hp : 0 < p) :
    p⁻¹ ≤ p ^ (-s) + (s - 1) * (Real.log p / p) := by
  have he := Real.add_one_le_exp (-((s - 1) * Real.log p))
  have heq : p ^ (-s) = p⁻¹ * Real.exp (-((s - 1) * Real.log p)) := by
    rw [Real.rpow_def_of_pos hp]
    calc
      Real.exp (Real.log p * -s) =
          Real.exp (-Real.log p + -((s - 1) * Real.log p)) := by congr 1; ring
      _ = p⁻¹ * Real.exp (-((s - 1) * Real.log p)) := by
        rw [Real.exp_add, Real.exp_neg, Real.exp_log hp]
  rw [heq]
  have hm := mul_le_mul_of_nonneg_left he (inv_nonneg.mpr hp.le)
  simp only [div_eq_mul_inv]
  nlinarith

theorem prime_power_sum_le_log_product {s : ℝ} (hs : 0 < s)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    (∑ p ∈ P, (p : ℝ) ^ (-s)) ≤
      Real.log (∏ p ∈ P, (1 - (p : ℝ) ^ (-s))⁻¹) := by
  have hlt (p : ℕ) (hp : p ∈ P) : (p : ℝ) ^ (-s) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast (hP p hp).one_lt) (by linarith)
  have hpos (p : ℕ) (hp : p ∈ P) : 0 < (1 - (p : ℝ) ^ (-s))⁻¹ :=
    inv_pos.mpr (by linarith [hlt p hp])
  rw [Real.log_prod (fun p hp => (hpos p hp).ne')]
  apply Finset.sum_le_sum
  intro p hp
  rw [Real.log_inv]
  have h := Real.log_le_sub_one_of_pos (by linarith [hlt p hp] : 0 < 1 - (p : ℝ) ^ (-s))
  linarith

theorem prime_reciprocal_sum_upper (N : ℕ) (hN : 2 ≤ N) :
    (∑ p ∈ Nat.primesLE N, (p : ℝ)⁻¹) ≤ Real.log (Real.log N) + 11 := by
  let L := Real.log N
  have hLlower : (1 / 2 : ℝ) ≤ L :=
    log_two_lower.trans (Real.log_le_log (by norm_num) (by exact_mod_cast hN))
  have hLpos : 0 < L := by linarith
  let s := 1 + 1 / L
  have hsdiff : s - 1 = 1 / L := by dsimp [s]; ring
  have hs : 1 < s := by
    have h := one_div_pos.mpr hLpos
    dsimp [s]
    linarith
  have hprimes : ∀ p ∈ Nat.primesLE N, p.Prime := fun _ hp => Nat.prime_of_mem_primesLE hp
  let E := ∏ p ∈ Nat.primesLE N, (1 - (p : ℝ) ^ (-s))⁻¹
  have hEpos : 0 < E := by
    apply Finset.prod_pos
    intro p hp
    apply inv_pos.mpr
    have h := Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast (hprimes p hp).one_lt : (1 : ℝ) < p) (by linarith : -s < 0)
    linarith
  have hEbound : E ≤ 4 * L := by
    calc
      E ≤ 1 + 2 / (s - 1) := finite_euler_power_bound hs _ hprimes
      _ = 1 + 2 * L := by rw [hsdiff]; field_simp
      _ ≤ 4 * L := by linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlog4 : Real.log 4 ≤ 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
    linarith
  have hlogE : Real.log E ≤ Real.log L + 2 := by
    calc
      Real.log E ≤ Real.log (4 * L) := Real.log_le_log hEpos hEbound
      _ = Real.log L + Real.log 4 := by rw [Real.log_mul (by norm_num) hLpos.ne']; ring
      _ ≤ Real.log L + 2 := add_le_add le_rfl hlog4
  have herror : (s - 1) * (L + 4) ≤ 9 := by
    calc
      (s - 1) * (L + 4) = 1 + 4 / L := by rw [hsdiff]; field_simp
      _ ≤ 9 := by
        have h : 4 / L ≤ 8 := (div_le_iff₀ hLpos).mpr (by nlinarith)
        linarith
  calc
    (∑ p ∈ Nat.primesLE N, (p : ℝ)⁻¹) ≤
        ∑ p ∈ Nat.primesLE N, ((p : ℝ) ^ (-s) + (s - 1) * (Real.log p / p)) := by
      apply Finset.sum_le_sum
      intro p hp
      exact reciprocal_le_power_add_log (by exact_mod_cast (hprimes p hp).pos)
    _ = (∑ p ∈ Nat.primesLE N, (p : ℝ) ^ (-s)) +
        (s - 1) * (∑ p ∈ Nat.primesLE N, Real.log p / p) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ Real.log E + (s - 1) * (L + 4) :=
      add_le_add (prime_power_sum_le_log_product (by linarith : 0 < s) _ hprimes)
        (mul_le_mul_of_nonneg_left (weighted_prime_log_le N (by omega)) (by linarith))
    _ ≤ Real.log L + 2 + 9 := add_le_add hlogE herror
    _ = Real.log (Real.log N) + 11 := by dsimp [L]; ring

theorem harmonic_le_prime_euler_product (N : ℕ) :
    (harmonic N : ℝ) ≤ ∏ p ∈ Nat.primesLE N, (1 - (p : ℝ)⁻¹)⁻¹ := by
  classical
  let S := Finset.Icc 1 N
  let P := Nat.primesLE N
  have hmem (n : S) : (n : ℕ) ∈ Nat.factoredNumbers P := by
    obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp n.property
    apply Nat.mem_factoredNumbers_iff_forall_le.mpr
    refine ⟨by omega, ?_⟩
    intro p hpn hp hpdvd
    exact Nat.mem_primesLE.mpr ⟨hpn.trans hnN, hp⟩
  let e : S → Nat.factoredNumbers P := fun n => ⟨n, hmem n⟩
  have he : Function.Injective e := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun n : Nat.factoredNumbers P => (n : ℕ)) hab
  have h := Summable.tsum_le_tsum_of_inj e he
    (fun n _ => inv_nonneg.mpr (Nat.cast_nonneg (n : ℕ)))
    (fun n => (le_refl (((n : ℕ) : ℝ)⁻¹)))
    (hasSum_fintype (fun n : S => ((n : ℕ) : ℝ)⁻¹)).summable (smooth_reciprocal_summable P)
  rw [tsum_fintype] at h
  change (∑ n : S, ((n : ℕ) : ℝ)⁻¹) ≤
    ∑' n : Nat.factoredNumbers P, ((n : ℕ) : ℝ)⁻¹ at h
  rw [S.sum_coe_sort (fun n : ℕ => (n : ℝ)⁻¹)] at h
  have hfilter : P.filter Nat.Prime = P :=
    Finset.filter_eq_self.mpr (fun p hp => Nat.prime_of_mem_primesLE hp)
  rw [(smooth_reciprocal_hasSum P).tsum_eq, hfilter] at h
  simpa only [S, P, harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] using h

theorem reciprocal_euler_log_upper (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    Real.log (∏ p ∈ P, (1 - (p : ℝ)⁻¹)⁻¹) ≤ (∑ p ∈ P, (p : ℝ)⁻¹) + 1 := by
  have hpos (p : ℕ) (hp : p ∈ P) : 0 < (1 - (p : ℝ)⁻¹)⁻¹ := by
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (hP p hp).one_lt
    exact inv_pos.mpr (by linarith [inv_lt_one_of_one_lt₀ hp1])
  rw [Real.log_prod (fun p hp => (hpos p hp).ne')]
  calc
    (∑ p ∈ P, Real.log ((1 - (p : ℝ)⁻¹)⁻¹)) ≤ ∑ p ∈ P, ((p : ℝ) - 1)⁻¹ := by
      apply Finset.sum_le_sum
      intro p hp
      have hp1 : (1 : ℝ) < p := by exact_mod_cast (hP p hp).one_lt
      have h := Real.log_le_sub_one_of_pos (hpos p hp)
      have heq : (1 - (p : ℝ)⁻¹)⁻¹ - 1 = ((p : ℝ) - 1)⁻¹ := by
        have hp0 : (p : ℝ) ≠ 0 := by linarith
        have hpm : (p : ℝ) - 1 ≠ 0 := by linarith
        field_simp [hp0, hpm]
        <;> ring
      rwa [heq] at h
    _ = (∑ p ∈ P, (p : ℝ)⁻¹) + ∑ p ∈ P, (((p : ℝ) - 1)⁻¹ - (p : ℝ)⁻¹) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ ≤ (∑ p ∈ P, (p : ℝ)⁻¹) + 1 :=
      add_le_add le_rfl (prime_inverse_difference_sum_le_one P hP)

theorem prime_reciprocal_sum_lower (N : ℕ) (hN : 2 ≤ N) :
    Real.log (Real.log N) - 1 ≤ ∑ p ∈ Nat.primesLE N, (p : ℝ)⁻¹ := by
  have hlog : 0 < Real.log N :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hlogH : Real.log N ≤ (harmonic N : ℝ) := by
    have h := log_le_harmonic_floor (N : ℝ) (Nat.cast_nonneg N)
    simpa using h
  have hE := hlogH.trans (harmonic_le_prime_euler_product N)
  have hlogE := Real.log_le_log hlog hE
  have hupper := reciprocal_euler_log_upper (Nat.primesLE N)
    (fun p hp => Nat.prime_of_mem_primesLE hp)
  linarith

end Erdos302
