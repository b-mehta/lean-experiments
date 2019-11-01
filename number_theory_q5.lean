import data.nat.basic
import data.nat.prime

open nat

lemma division_lemma { a n : ℕ } ( ha : a ≥ 1 ) : a - 1 ∣ a ^ n - 1 :=
begin
  apply dvd_of_mod_eq_zero,
  induction n with n, simp,
  suffices: (a^n * (a - 1 + 1) - 1) % (a - 1) = 0,
    by rwa nat.sub_add_cancel ha at this,
  rw [mul_add, mul_one, nat.add_sub_assoc (pow_pos ha _)], simpa
end

lemma division_lemma' { a p q : ℕ } ( ha : a ≥ 1 ) : a ^ p - 1 ∣ a ^ (p * q) - 1 :=
begin
  cases p, simp,
  rw nat.pow_mul,
  apply division_lemma (pow_pos ‹a ≥ 1› _),
end

lemma eq_add_of_sub_eq'' { a m n : ℕ } ( ha : a ≥ m ) : a - m = n → a = n + m := 
  (nat.sub_eq_iff_eq_add ha).1

lemma pow_monotonic { a m n : ℕ } ( ha : a ≥ 2 ) ( k : a^m ≥ a^n ) : m ≥ n :=
  le_of_not_gt (λ r, not_le_of_lt (pow_lt_pow_of_lt_right ha r) k)

lemma pow_inj { a m n : ℕ } ( ha : a ≥ 2 ) ( k : a^m = a^n ) : m = n :=
  by apply le_antisymm; apply pow_monotonic ha; apply le_of_eq; rw k

theorem question5 { a n : ℕ } { ha : a ≥ 2 } { hn : n ≥ 2 } : prime (a^n - 1) → a = 2 ∧ prime n := 
begin
  have: a ≥ 1, from le_of_succ_le ‹a ≥ 2›,
  have: n ≥ 1, from le_of_succ_le ‹n ≥ 2›,
  have: a^n > 0, from pow_pos ‹a > 0› n,
  intro b, split,
    cases b.right _ (division_lemma ‹a ≥ 1›),
      apply eq_add_of_sub_eq'' ‹a ≥ 1› ‹a - 1 = 1›, 
    have: a^n = a^1,
      rw nat.pow_one, from nat.sub_cancel ‹a^n ≥ 1› ‹a ≥ 1› ‹a - 1 = a^n - 1›.symm,
    exfalso,
    have: a^n > a^1 := pow_lt_pow_of_lt_right ‹a > 1› ‹n > 1›,
    apply ne_of_gt ‹a^n > a^1› ‹a^n = a^1›,
  
  refine ⟨‹n ≥ 2›, _⟩,
  intros m _,
  have: a^m ≥ 1, from pow_pos ‹a ≥ 1› m,
  have: a^m - 1 ∣ a^_ - 1 := division_lemma' ‹a ≥ 1›,
  rw nat.mul_div_cancel_left' ‹m ∣ n› at this,
  cases b.right (a^m - 1) this,
    left,
    have: a^m ≤ a, 
    by calc a^m ≤ 2 : le_of_eq $ eq_add_of_sub_eq'' ‹a^m ≥ 1› ‹a^m - 1 = 1›
            ... ≤ a : ‹a ≥ 2›,
    have: m ≤ 1, apply pow_monotonic ‹a ≥ 2›, rwa nat.pow_one, 
    have: m > 0 := pos_of_dvd_of_pos ‹m ∣ n› ‹n > 0›,
    apply le_antisymm ‹m ≤ 1› ‹m > 0›,
  right,
  have: a^m = a^n, from nat.sub_cancel ‹a^m ≥ 1› ‹a^n ≥ 1› ‹a^m - 1 = a^n - 1›, 
  exact pow_inj ‹a ≥ 2› this,
end