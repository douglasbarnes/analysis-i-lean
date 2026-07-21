import Mathlib

/-! # Numbers and Sets: elementary number theory -/

namespace NumbersAndSets

abbrev Divides (a b : ℤ) := a ∣ b
abbrev Coprime (a b : ℕ) := Nat.Coprime a b
abbrev Prime (p : ℕ) := Nat.Prime p
abbrev Congruent (m a b : ℕ) := Nat.ModEq m a b
abbrev Totient := Nat.totient

theorem division_algorithm (a : ℤ) {b : ℤ} (hb : b ≠ 0) :
    ∃! qr : ℤ × ℤ, a = qr.1 * b + qr.2 ∧ 0 ≤ qr.2 ∧ qr.2 < |b| := by
  let q := a.ediv |b|
  let r := a.emod |b|
  have habs : |b| ≠ 0 := abs_ne_zero.mpr hb
  have hpos : 0 < |b| := abs_pos.mpr hb
  have hdecomp : a = q * |b| + r := by
    simpa [q, r] using (Int.ediv_add_emod a |b|).symm
  let q' := if 0 < b then q else -q
  have hqb : q' * b = q * |b| := by
    by_cases hp : 0 < b
    · simp [q', hp, abs_of_pos hp]
    · have hn : b < 0 := lt_of_le_of_ne (le_of_not_gt hp) (Ne.symm hb)
      simp [q', hp, abs_of_neg hn]
  refine ⟨(q', r), ⟨?_, Int.emod_nonneg _ habs, Int.emod_lt_of_pos _ hpos⟩, ?_⟩
  · simpa [hqb] using hdecomp
  · rintro ⟨q₂, r₂⟩ ⟨ha, hr0, hrb⟩
    apply Prod.ext
    · have : q₂ = q' := by
        apply (mul_left_cancel₀ hb)
        linarith [hdecomp, hqb]
      exact this
    · dsimp
      linarith [hdecomp, hqb]

theorem divisor_of_linear_combination {a b c u v : ℤ}
    (ha : c ∣ a) (hb : c ∣ b) : c ∣ u * a + v * b := by
  exact dvd_add (dvd_mul_of_dvd_right ha u) (dvd_mul_of_dvd_right hb v)

theorem bezout_identity (a b : ℕ) :
    ∃ u v : ℤ, (Nat.gcd a b : ℤ) = u * a + v * b := by
  simpa [mul_comm] using Int.gcd_eq_gcd_ab a b

theorem gcd_dvd_linear_combination_iff (a b : ℕ) (c : ℤ) :
    (Nat.gcd a b : ℤ) ∣ c ↔ ∃ u v : ℤ, c = u * a + v * b := by
  constructor
  · rintro ⟨k, rfl⟩
    obtain ⟨u, v, h⟩ := bezout_identity a b
    exact ⟨k * u, k * v, by rw [h]; ring⟩
  · rintro ⟨u, v, rfl⟩
    exact divisor_of_linear_combination (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left a b))
      (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right a b))

theorem exists_prime_factor {n : ℕ} (hn : n ≠ 1) : n = 0 ∨ ∃ p, p.Prime ∧ p ∣ n := by
  by_cases h0 : n = 0
  · exact Or.inl h0
  · exact Or.inr (Nat.exists_prime_and_dvd (Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨h0, hn⟩))

theorem infinitely_many_primes : Set.Infinite {p : ℕ | p.Prime} := by
  exact Nat.infinite_setOf_prime

theorem euclid_lemma {p a b : ℕ} (hp : p.Prime) (h : p ∣ a * b) : p ∣ a ∨ p ∣ b :=
  hp.dvd_mul.mp h

theorem prime_dvd_finset_product {ι : Type*} {s : Finset ι} {f : ι → ℕ} {p : ℕ}
    (hp : p.Prime) (h : p ∣ ∏ i ∈ s, f i) : ∃ i ∈ s, p ∣ f i := by
  simpa only [Finset.prod_eq_multiset_prod] using hp.dvd_finset_prod.mp h

theorem gcd_mul_lcm (a b : ℕ) : Nat.gcd a b * Nat.lcm a b = a * b :=
  Nat.gcd_mul_lcm a b

theorem modEq_of_modEq_of_dvd {a b m d : ℕ} (h : Nat.ModEq m a b) (hd : d ∣ m) :
    Nat.ModEq d a b := h.of_dvd hd

theorem modEq_add_mul {a b u v m : ℕ} (hab : Nat.ModEq m a b) (huv : Nat.ModEq m u v) :
    Nat.ModEq m (a + u) (b + v) ∧ Nat.ModEq m (a * u) (b * v) :=
  ⟨hab.add huv, hab.mul huv⟩

theorem unit_mod_iff_coprime (u m : ℕ) : IsUnit (u : ZMod m) ↔ Nat.Coprime u m := by
  simpa [Nat.coprime_comm] using ZMod.isUnit_iff_coprime u m

theorem fermat_little {p a : ℕ} (hp : p.Prime) : Nat.ModEq p (a ^ p) a :=
  Nat.ModEq.pow_card_sub_one_eq_one hp a

theorem euler_fermat {a m : ℕ} (h : Nat.Coprime a m) :
    Nat.ModEq m (a ^ Nat.totient m) 1 := Nat.ModEq.pow_totient h

theorem totient_prime {p : ℕ} (hp : p.Prime) : Nat.totient p = p - 1 := hp.totient

theorem totient_mul {m n : ℕ} (h : Nat.Coprime m n) :
    Nat.totient (m * n) = Nat.totient m * Nat.totient n := Nat.totient_mul h

theorem wilson {p : ℕ} (hp : p.Prime) : (p - 1)! % p = p - 1 := by
  exact Nat.Prime.factorial_mod_eq_sub_one hp

end NumbersAndSets
