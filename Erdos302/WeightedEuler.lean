import Erdos302.PrimeReciprocalBounds

namespace Erdos302

theorem finite_prefix_euler_bound (f : ℕ →* ℝ) (hf : ∀ n, 0 ≤ f n)
    (hp : ∀ p : ℕ, p.Prime → ‖f p‖ < 1) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, f n) ≤ ∏ p ∈ Nat.primesLE N, (1 - f p)⁻¹ := by
  classical
  let S := Finset.Icc 1 N
  let P := Nat.primesLE N
  have hmem (n : S) : (n : ℕ) ∈ Nat.factoredNumbers P := by
    obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp n.property
    refine Nat.mem_factoredNumbers_iff_forall_le.mpr ⟨by omega, ?_⟩
    intro p hpn hprime hdvd
    exact Nat.mem_primesLE.mpr ⟨hpn.trans hnN, hprime⟩
  let e : S → Nat.factoredNumbers P := fun n => ⟨n, hmem n⟩
  have he : Function.Injective e := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun n : Nat.factoredNumbers P => (n : ℕ)) hab
  have hsum := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := f) (fun hprime => hp _ hprime) P
  have h := Summable.tsum_le_tsum_of_inj e he (fun n _ => hf n)
    (fun n => le_refl (f n)) (hasSum_fintype (fun n : S => f n)).summable hsum.2.summable
  rw [tsum_fintype] at h
  change (∑ n : S, f n) ≤ ∑' n : Nat.factoredNumbers P, f n at h
  rw [S.sum_coe_sort f, hsum.2.tsum_eq,
    Finset.filter_eq_self.mpr (fun p hpP => Nat.prime_of_mem_primesLE hpP)] at h
  exact h

theorem smallOmega_prime {p : ℕ} (hp : p.Prime) (X : ℕ) :
    smallOmega p X = if p ≤ X then 1 else 0 := by
  classical
  simp [smallOmega, hp.factorization, Finsupp.single_apply]

noncomputable def weightedReciprocalHom (t : ℝ) (X : ℕ) : ℕ →* ℝ where
  toFun n := t ^ smallOmega n X / n
  map_one' := by simp [smallOmega]
  map_mul' a b := by
    by_cases ha : a = 0
    · simp [ha]
    by_cases hb : b = 0
    · simp [hb]
    rw [smallOmega_mul ha hb, pow_add, Nat.cast_mul]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring

theorem weightedReciprocalHom_prime {t : ℝ} {p X : ℕ} (hp : p.Prime) :
    weightedReciprocalHom t X p = (if p ≤ X then t else 1) / (p : ℝ) := by
  change t ^ smallOmega p X / p = _
  rw [smallOmega_prime hp]
  split_ifs <;> simp

theorem weighted_reciprocal_euler_bound {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (N X : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, t ^ smallOmega n X / n) ≤
      ∏ p ∈ Nat.primesLE N, (1 - (if p ≤ X then t else 1) / (p : ℝ))⁻¹ := by
  have hf (n : ℕ) : 0 ≤ weightedReciprocalHom t X n := by
    exact div_nonneg (pow_nonneg ht0 _) (Nat.cast_nonneg n)
  have hp (p : ℕ) (hprime : p.Prime) : ‖weightedReciprocalHom t X p‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hf p), weightedReciprocalHom_prime hprime]
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hprime.one_lt
    have hp0 : (0 : ℝ) < p := by linarith
    apply (div_lt_one hp0).mpr
    split_ifs <;> linarith
  have h := finite_prefix_euler_bound (weightedReciprocalHom t X) hf hp N
  convert h using 1
  · rfl
  · apply Finset.prod_congr rfl
    intro p hpP
    rw [weightedReciprocalHom_prime (Nat.prime_of_mem_primesLE hpP)]

theorem weighted_reciprocal_factor_log {a p : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hp : 2 ≤ p) :
    Real.log (1 - a / p)⁻¹ ≤ a / p + ((p - 1)⁻¹ - p⁻¹) := by
  have hp0 : 0 < p := by linarith
  have hpa : 0 < p - a := by linarith
  have hp1 : 0 < p - 1 := by linarith
  have hfrac : a / p < 1 := (div_lt_one hp0).mpr (by linarith)
  have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr (by linarith : 0 < 1 - a / p))
  have hsq : a ^ 2 ≤ 1 := by nlinarith
  have herr : a ^ 2 / (p * (p - a)) ≤ 1 / (p * (p - 1)) := by
    calc
      a ^ 2 / (p * (p - a)) ≤ 1 / (p * (p - a)) :=
        div_le_div_of_nonneg_right hsq (by positivity)
      _ ≤ 1 / (p * (p - 1)) :=
        one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have hdiff : (1 - a / p)⁻¹ - 1 = a / p + a ^ 2 / (p * (p - a)) := by
    field_simp
    <;> ring
  have hdiff2 : 1 / (p * (p - 1)) = (p - 1)⁻¹ - p⁻¹ := by field_simp; ring
  rw [hdiff] at hlog
  rw [← hdiff2]
  exact hlog.trans (add_le_add le_rfl herr)

theorem weighted_prime_reciprocal_sum (t : ℝ) (N X : ℕ) :
    (∑ p ∈ Nat.primesLE N, (if p ≤ X then t else 1) / (p : ℝ)) =
      (∑ p ∈ Nat.primesLE N, (p : ℝ)⁻¹) +
        (t - 1) * (∑ p ∈ Nat.primesLE (min N X), (p : ℝ)⁻¹) := by
  have hfilter : (Nat.primesLE N).filter (fun p => p ≤ X) = Nat.primesLE (min N X) := by
    ext p
    simp only [Finset.mem_filter, Nat.mem_primesLE, le_min_iff]
    tauto
  rw [← hfilter, Finset.sum_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  split_ifs <;> ring

theorem weighted_euler_log_bound {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (N X : ℕ) (hN : 2 ≤ N) (hX : 2 ≤ X) :
    Real.log (∏ p ∈ Nat.primesLE N, (1 - (if p ≤ X then t else 1) / (p : ℝ))⁻¹) ≤
      Real.log (Real.log N) + (t - 1) * Real.log (Real.log (min N X)) + 13 := by
  have ha0 (p : ℕ) : 0 ≤ (if p ≤ X then t else 1) := by split_ifs <;> linarith
  have ha1 (p : ℕ) : (if p ≤ X then t else 1) ≤ 1 := by split_ifs <;> linarith
  have hp2 (p : ℕ) (hp : p ∈ Nat.primesLE N) : (2 : ℝ) ≤ p :=
    by exact_mod_cast Nat.two_le_of_mem_primesLE hp
  have hf (p : ℕ) (hp : p ∈ Nat.primesLE N) :
      (1 - (if p ≤ X then t else 1) / (p : ℝ))⁻¹ ≠ 0 := by
    have hpos : (0 : ℝ) < p := by linarith [hp2 p hp]
    have hlt : (if p ≤ X then t else 1) / (p : ℝ) < 1 :=
      (div_lt_one hpos).mpr (by linarith [ha1 p, hp2 p hp])
    exact (inv_pos.mpr (by linarith : 0 < 1 - (if p ≤ X then t else 1) / (p : ℝ))).ne'
  rw [Real.log_prod hf]
  calc
    (∑ p ∈ Nat.primesLE N,
        Real.log (1 - (if p ≤ X then t else 1) / (p : ℝ))⁻¹) ≤
      (∑ p ∈ Nat.primesLE N, (if p ≤ X then t else 1) / (p : ℝ)) + 1 := by
      calc
        (∑ p ∈ Nat.primesLE N,
            Real.log (1 - (if p ≤ X then t else 1) / (p : ℝ))⁻¹) ≤
          ∑ p ∈ Nat.primesLE N, ((if p ≤ X then t else 1) / (p : ℝ) +
            (((p : ℝ) - 1)⁻¹ - (p : ℝ)⁻¹)) :=
          Finset.sum_le_sum (fun p hp => weighted_reciprocal_factor_log (ha0 p) (ha1 p) (hp2 p hp))
        _ = (∑ p ∈ Nat.primesLE N, (if p ≤ X then t else 1) / (p : ℝ)) +
            ∑ p ∈ Nat.primesLE N, (((p : ℝ) - 1)⁻¹ - (p : ℝ)⁻¹) := Finset.sum_add_distrib
        _ ≤ (∑ p ∈ Nat.primesLE N, (if p ≤ X then t else 1) / (p : ℝ)) + 1 :=
          add_le_add le_rfl (prime_inverse_difference_sum_le_one _
            (fun p hp => Nat.prime_of_mem_primesLE hp))
    _ = (∑ p ∈ Nat.primesLE N, (p : ℝ)⁻¹) +
        (t - 1) * (∑ p ∈ Nat.primesLE (min N X), (p : ℝ)⁻¹) + 1 := by
      rw [weighted_prime_reciprocal_sum]
    _ ≤ Real.log (Real.log N) + 11 +
        (t - 1) * (Real.log (Real.log (min N X)) - 1) + 1 := by
      apply add_le_add _ le_rfl
      apply add_le_add (prime_reciprocal_sum_upper N hN)
      simpa only [Nat.cast_min] using
        mul_le_mul_of_nonpos_left (prime_reciprocal_sum_lower _ (le_min hN hX))
          (by linarith : t - 1 ≤ 0)
    _ ≤ Real.log (Real.log N) + (t - 1) * Real.log (Real.log (min N X)) + 13 := by
      nlinarith

theorem weighted_harmonic_sum_bound {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (N X : ℕ) (hN : 2 ≤ N) (hX : 2 ≤ X) :
    (∑ n ∈ Finset.Icc 1 N, t ^ smallOmega n X / n) ≤
      Real.exp 13 * Real.log N * (Real.log (min N X)) ^ (t - 1) := by
  have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hlogM : 0 < Real.log (min N X) :=
    Real.log_pos (by exact_mod_cast (show 1 < min N X by omega))
  calc
    (∑ n ∈ Finset.Icc 1 N, t ^ smallOmega n X / n) ≤
        ∏ p ∈ Nat.primesLE N, (1 - (if p ≤ X then t else 1) / (p : ℝ))⁻¹ :=
      weighted_reciprocal_euler_bound ht0 ht1 N X
    _ ≤ Real.exp (Real.log (Real.log N) +
        (t - 1) * Real.log (Real.log (min N X)) + 13) :=
      Real.le_exp_of_log_le (weighted_euler_log_bound ht0 ht1 N X hN hX)
    _ = Real.exp 13 * Real.log N * (Real.log (min N X)) ^ (t - 1) := by
      rw [Real.exp_add, Real.exp_add, Real.exp_log hlogN, Real.rpow_def_of_pos hlogM]
      rw [mul_comm (t - 1), mul_assoc]
      ring

end Erdos302
