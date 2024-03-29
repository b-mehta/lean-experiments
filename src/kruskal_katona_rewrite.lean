import algebra.geom_sum
import data.finset
import data.fintype
import data.list
import tactic

open fintype
open finset

variables {n : ℕ}
local notation `X` := fin n
variables {𝒜 : finset (finset X)}

lemma union_singleton_eq_insert {α : Type*} [decidable_eq α] (a : α) (s : finset α) : finset.singleton a ∪ s = insert a s := begin ext, rw [mem_insert, mem_union, mem_singleton] end

lemma mem_powerset_len_iff_card {r : ℕ} : ∀ (x : finset X), x ∈ powerset_len r (elems X) ↔ card x = r :=
by intro x; rw mem_powerset_len; exact and_iff_right (subset_univ _)

def example1 : finset (finset (fin 5)) :=
{ {0,1,2}, {0,1,3}, {0,2,3}, {0,2,4} } 

section layers
  variables {r : ℕ}

  def is_layer (𝒜 : finset (finset X)) (r : ℕ) : Prop := ∀ A ∈ 𝒜, card A = r

  lemma union_layer {A B : finset (finset X)} : is_layer A r ∧ is_layer B r ↔ is_layer (A ∪ B) r :=
  begin
    split; intros p, 
      rw is_layer,
      intros,
      rw mem_union at H,
      cases H,
        exact (p.1 _ H),
        exact (p.2 _ H),
    split,
    all_goals {rw is_layer, intros, apply p, rw mem_union, tauto}, 
  end

  lemma powerset_len_iff_is_layer : is_layer 𝒜 r ↔ 𝒜 ⊆ powerset_len r (elems X) :=
  begin
    split; intros p A h,
      rw mem_powerset_len_iff_card,
      exact (p _ h),
    rw ← mem_powerset_len_iff_card, 
    exact p h
  end

  lemma size_in_layer (h : is_layer 𝒜 r) : card 𝒜 ≤ nat.choose (card X) r :=
  begin
    rw [fintype.card, ← card_powerset_len],
    apply card_le_of_subset,
    rwa [univ, ← powerset_len_iff_is_layer]
  end
end layers

lemma bind_sub_bind_of_sub_left {α β : Type*} [decidable_eq β] {s₁ s₂ : finset α} {t : α → finset β} (h : s₁ ⊆ s₂) : s₁.bind t ⊆ s₂.bind t :=
by intro x; simp; intros y hy hty; refine ⟨y, h hy, hty⟩

section shadow
  def all_removals (A : finset X) : finset (finset X) := A.image (erase A)

  lemma all_removals_size {A : finset X} {r : ℕ} (h : A.card = r) : is_layer (all_removals A) (r-1) := 
  begin
    intros B H,
    rw [all_removals, mem_image] at H,
    rcases H with ⟨i, ih, Bh⟩,
    rw [← Bh, card_erase_of_mem ih, h], refl
  end

  def mem_all_removals {A : finset X} {B : finset X} : B ∈ all_removals A ↔ ∃ i ∈ A, erase A i = B :=
  by simp only [all_removals, mem_image]

  lemma card_all_removals {A : finset X} {r : ℕ} (H : card A = r) : (all_removals A).card = r :=
  begin
    rwa [all_removals, card_image_of_inj_on],
    intros i ih j _ k,
    have q: i ∉ erase A j := k ▸ not_mem_erase i A,
    rw [mem_erase, not_and] at q,
    by_contra a, apply q a ih
  end

  def shadow (𝒜 : finset (finset X)) : finset (finset X) := 𝒜.bind all_removals

  reserve prefix `∂`:90
  notation ∂𝒜 := shadow 𝒜

  def mem_shadow (B : finset X) : B ∈ shadow 𝒜 ↔ ∃ A ∈ 𝒜, ∃ i ∈ A, erase A i = B := 
  by simp only [shadow, all_removals, mem_bind, mem_image]

  def mem_shadow' {B : finset X} : B ∈ shadow 𝒜 ↔ ∃ j ∉ B, insert j B ∈ 𝒜 :=
  begin
    rw mem_shadow,
    split,
      rintro ⟨A, HA, i, Hi, k⟩,
      rw ← k,
      refine ⟨i, not_mem_erase i A, _⟩,
      rwa insert_erase Hi,
    rintro ⟨i, Hi, k⟩,
      refine ⟨insert i B, k, i, mem_insert_self _ _, _⟩,
      rw erase_insert Hi
  end

  lemma shadow_layer {r : ℕ} : is_layer 𝒜 r → is_layer (∂𝒜) (r-1) :=
  begin
    intros a A H,
    rw [shadow, mem_bind] at H,
    rcases H with ⟨B, _, _⟩,
    exact all_removals_size (a _ ‹_›) _ ‹A ∈ all_removals B›,
  end

  def sub_of_shadow {B : finset X} : B ∈ ∂𝒜 → ∃ A ∈ 𝒜, B ⊆ A :=
  begin
    intro k,
    rw mem_shadow at k,
    rcases k with ⟨A, H, _, _, k⟩,
    rw ← k,
    exact ⟨A, H, erase_subset _ _⟩
  end

  def sub_iff_shadow_one {B : finset X} : B ∈ shadow 𝒜 ↔ ∃ A ∈ 𝒜, B ⊆ A ∧ card (A \ B) = 1 :=
  begin
    rw mem_shadow', split, 
      rintro ⟨i, ih, inA⟩,
      refine ⟨insert i B, inA, subset_insert _ _, _⟩, rw card_sdiff (subset_insert _ _), rw card_insert_of_not_mem ih, simp,
    rintro ⟨A, hA, _⟩,
    rw card_eq_one at a_h_h, rcases a_h_h with ⟨subs, j, eq⟩, 
    use j, refine ⟨_, _⟩, 
    intro, have: j ∈ finset.singleton j, rw mem_singleton, rw ← eq at this, rw mem_sdiff at this, exact this.2 a, 
    rw ← union_singleton_eq_insert, rw ← eq, rwa sdiff_union_of_subset subs, 
  end

  def sub_iff_shadow_iter {B : finset X} (k : ℕ) : B ∈ nat.iterate shadow k 𝒜 ↔ ∃ A ∈ 𝒜, B ⊆ A ∧ card (A \ B) = k :=
  begin
    revert 𝒜 B,
    induction k with k ih,
      simp, intros 𝒜 B, 
      split,
        intro p, refine ⟨B, p, subset.refl _, _⟩, apply eq_empty_of_forall_not_mem, intro x, rw mem_sdiff, tauto,
      rintro ⟨A, _, _⟩, rw sdiff_eq_empty_iff_subset at a_h_right, have: A = B := subset.antisymm a_h_right.2 a_h_right.1,
      rwa ← this,
    simp, intros 𝒜 B, have := @ih (∂𝒜) B,
    rw this, clear this ih,
    split, 
      rintro ⟨A, hA, BsubA, card_AdiffB_is_k⟩, rw sub_iff_shadow_one at hA, rcases hA with ⟨C, CinA, AsubC, card_CdiffA_is_1⟩,
      refine ⟨C, CinA, trans BsubA AsubC, _⟩,
      rw card_sdiff (trans BsubA AsubC), rw card_sdiff BsubA at card_AdiffB_is_k, rw card_sdiff AsubC at card_CdiffA_is_1,
      by calc card C - card B = (card C - card A + card A) - card B : begin rw nat.sub_add_cancel, apply card_le_of_subset AsubC end 
      ... = (card C - card A) + (card A - card B) : begin rw nat.add_sub_assoc, apply card_le_of_subset BsubA end
      ... = k + 1 : begin rw [card_CdiffA_is_1, card_AdiffB_is_k, add_comm] end,
    rintro ⟨A, hA, _, _⟩, 
    have z: A \ B ≠ ∅, rw ← card_pos, rw a_h_right_right, exact nat.succ_pos _,
    rw [ne, ← exists_mem_iff_ne_empty] at z, 
    rcases z with ⟨i, hi⟩,
    have: i ∈ A, rw mem_sdiff at hi, exact hi.1,
    have: B ⊆ erase A i, { intros t th, apply mem_erase_of_ne_of_mem _ (a_h_right_left th), intro, rw mem_sdiff at hi, rw a at th, exact hi.2 th },
    refine ⟨erase A i, _, ‹_›, _⟩,
    { rw mem_shadow, refine ⟨A, hA, i, ‹_›, rfl⟩ }, 
    rw card_sdiff ‹B ⊆ erase A i›, rw card_erase_of_mem ‹i ∈ A›, rw nat.pred_sub, rw ← card_sdiff a_h_right_left, rw a_h_right_right, simp,
  end
end shadow

#eval shadow example1

section local_lym
  lemma multiply_out {A B n r : ℕ} (hr1 : 1 ≤ r) (hr2 : r ≤ n)
    (h : A * r ≤ B * (n - r + 1)) : (A : ℚ) / (nat.choose n r) ≤ B / nat.choose n (r-1) :=
  begin
    rw div_le_div_iff; norm_cast,
    apply le_of_mul_le_mul_right _ ‹0 < r›,
    cases r,
      simp,
    rw nat.succ_eq_add_one at *,
    rw [← nat.sub_add_comm hr2, nat.add_sub_add_right] at h,
    rw [nat.add_sub_cancel, mul_assoc B, nat.choose_succ_right_eq, mul_right_comm, ← mul_assoc, mul_right_comm B], 
    exact nat.mul_le_mul_right _ h,
    apply nat.choose_pos hr2,
    apply nat.choose_pos (le_trans (nat.pred_le _) hr2)
  end

  def the_pairs (𝒜 : finset (finset X)) : finset (finset X × finset X) :=
  𝒜.bind (λ A, (all_removals A).image (prod.mk A))

  lemma card_the_pairs {r : ℕ} (𝒜 : finset (finset X)) : is_layer 𝒜 r → (the_pairs 𝒜).card = 𝒜.card * r :=
  begin
    intro, rw [the_pairs, card_bind],
    { convert (sum_congr rfl _),
      { rw [← nat.smul_eq_mul, ← sum_const] }, 
      intros,
      rw [card_image_of_inj_on, card_all_removals (a _ H)],
      exact (λ _ _ _ _ k, (prod.mk.inj k).2) },
    simp only [disjoint_left, mem_image],
    rintros _ _ _ _ k a ⟨_, _, a₁⟩ ⟨_, _, a₂⟩,
    exact k (prod.mk.inj (a₁.trans a₂.symm)).1,
  end

  def from_below (𝒜 : finset (finset X)) : finset (finset X × finset X) :=
  (∂𝒜).bind (λ B, (univ \ B).image (λ x, (insert x B, B)))

  lemma mem_the_pairs (A B : finset X) : (A,B) ∈ the_pairs 𝒜 ↔ A ∈ 𝒜 ∧ B ∈ all_removals A :=
  begin
    simp only [the_pairs, mem_bind, mem_image],
    split, 
    { rintro ⟨a, Ha, b, Hb, h⟩, 
      rw [(prod.mk.inj h).1, (prod.mk.inj h).2] at *,
      exact ⟨Ha, Hb⟩ },
    { intro h, exact ⟨A, h.1, B, h.2, rfl⟩}
  end

  lemma mem_from_below (A B : finset X) : A ∈ 𝒜 ∧ (∃ (i ∉ B), insert i B = A) → (A,B) ∈ from_below 𝒜 :=
  begin
    rw [from_below, mem_bind],
    rintro ⟨Ah, i, ih, a⟩,
    refine ⟨B, _, _⟩,
      rw mem_shadow',
      refine ⟨i, ih, a.symm ▸ Ah⟩,
    rw mem_image,
    refine ⟨i, mem_sdiff.2 ⟨complete _, ih⟩, by rw a⟩,
  end

  lemma above_sub_below (𝒜 : finset (finset X)) : the_pairs 𝒜 ⊆ from_below 𝒜 :=
  begin
    rintros ⟨A,B⟩ h,
    rw [mem_the_pairs, mem_all_removals] at h,
    apply mem_from_below,
    rcases h with ⟨Ah, i, ih, AeB⟩,
    refine ⟨Ah, i, _, _⟩; rw ← AeB,
      apply not_mem_erase,
    apply insert_erase ih
  end

  lemma card_from_below (r : ℕ) : is_layer 𝒜 r → (from_below 𝒜).card ≤ (∂𝒜).card * (n - (r - 1)) :=
  begin
    intro,
    rw [from_below],
    convert card_bind_le,
    rw [← nat.smul_eq_mul, ← sum_const],
    apply sum_congr rfl,
    intros, 
    rw [card_image_of_inj_on, card_sdiff (subset_univ _), card_univ, card_fin, shadow_layer a _ H],
    intros x1 x1h _ _ h,
    have q := mem_insert_self x1 x, 
    rw [(prod.mk.inj h).1, mem_insert] at q,
    apply or.resolve_right q ((mem_sdiff.1 x1h).2),
  end

  theorem local_lym {r : ℕ} (hr1 : r ≥ 1) (hr2 : r ≤ n) (H : is_layer 𝒜 r):
    (𝒜.card : ℚ) / nat.choose n r ≤ (∂𝒜).card / nat.choose n (r-1) :=
  begin
    apply multiply_out hr1 hr2,
    rw ← card_the_pairs _ H,
    transitivity,
      apply card_le_of_subset (above_sub_below _),
    rw ← nat.sub_sub_assoc hr2 hr1,
    apply card_from_below _ H
  end
end local_lym

section slice
  def slice (𝒜 : finset (finset X)) (r : ℕ) : finset (finset X) := 𝒜.filter (λ i, card i = r)

  reserve infix `#`:100
  notation 𝒜#r := slice 𝒜 r

  lemma mem_slice {r : ℕ} {A : finset X} : A ∈ 𝒜#r ↔ A ∈ 𝒜 ∧ A.card = r :=
  by rw [slice, mem_filter]

  lemma layered_slice {𝒜 : finset (finset X)} {r : ℕ} : is_layer (𝒜#r) r := λ _ h, (mem_slice.1 h).2

  lemma ne_of_diff_slice {r₁ r₂ : ℕ} {A₁ A₂ : finset X} (h₁ : A₁ ∈ 𝒜#r₁) (h₂ : A₂ ∈ 𝒜#r₂) : r₁ ≠ r₂ → A₁ ≠ A₂ :=
  mt (λ h, (layered_slice A₁ h₁).symm.trans ((congr_arg card h).trans (layered_slice A₂ h₂)))

end slice

section lym
  def antichain (𝒜 : finset (finset X)) : Prop := ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, A ≠ B → ¬(A ⊆ B)

  def decompose' (𝒜 : finset (finset X)) : Π (k : ℕ), finset (finset X)
    | 0 := 𝒜#n
    | (k+1) := 𝒜#(n - (k+1)) ∪ shadow (decompose' k)

  def decompose'_layer (𝒜 : finset (finset X)) (k : ℕ) : is_layer (decompose' 𝒜 k) (n-k) :=
  begin
    induction k with k ih;
      rw decompose',
      apply layered_slice,
    rw ← union_layer,
    split,
      apply layered_slice,
    apply shadow_layer ih,
  end

  theorem antichain_prop {r k : ℕ} (hk : k ≤ n) (hr : r < k) (H : antichain 𝒜) :
  ∀ A ∈ 𝒜#(n - k), ∀ B ∈ ∂decompose' 𝒜 r, ¬(A ⊆ B) :=
  begin
    intros A HA B HB k,
    rcases sub_of_shadow HB with ⟨C, HC, _⟩,
    replace k := trans k ‹B ⊆ C›, clear HB h_h B,
    induction r with r ih generalizing A C;
    rw decompose' at HC,
    any_goals { rw mem_union at HC, cases HC },
    any_goals { refine H A (mem_slice.1 HA).1 C (mem_slice.1 HC).1 _ ‹A ⊆ C›,
                apply ne_of_diff_slice HA HC _,
                apply ne_of_lt },
    { apply nat.sub_lt_of_pos_le _ _ hr hk },
    { mono },
    obtain ⟨_, HB', HB''⟩ := sub_of_shadow HC,
    refine ih (nat.lt_of_succ_lt hr) _ _ HA HB' (trans k_1 HB'')
  end

  lemma disjoint_of_antichain {k : ℕ} (hk : k + 1 ≤ n) (H : antichain 𝒜) : disjoint (𝒜#(n - (k + 1))) (∂decompose' 𝒜 k) := 
  disjoint_left.2 $ λ A HA HB, antichain_prop hk (lt_add_one k) H A HA A HB (subset.refl _)

  lemma card_decompose'_other {k : ℕ} (hk : k ≤ n) (H : antichain 𝒜) : 
    sum (range (k+1)) (λ r, ((𝒜#(n-r)).card : ℚ) / nat.choose n (n-r)) ≤ ((decompose' 𝒜 k).card : ℚ) / nat.choose n (n-k) :=
  begin
    induction k with k ih,
      rw [sum_range_one, div_le_div_iff]; norm_cast, exact nat.choose_pos (nat.sub_le _ _), exact nat.choose_pos (nat.sub_le _ _),
    rw [sum_range_succ, decompose'],
    have: (𝒜#(n - (k + 1)) ∪ ∂decompose' 𝒜 k).card = (𝒜#(n - (k + 1))).card + (∂decompose' 𝒜 k).card,
      apply card_disjoint_union,
      rw disjoint_iff_ne,
      intros A hA B hB m,
      apply antichain_prop hk (lt_add_one k) H A hA B hB,
      rw m, refl,
    rw this,
    have: ↑((𝒜#(n - (k + 1))).card + (∂decompose' 𝒜 k).card) / (nat.choose n (n - nat.succ k) : ℚ) = 
          ((𝒜#(n - (k + 1))).card : ℚ) / (nat.choose n (n - nat.succ k)) + ((∂decompose' 𝒜 k).card : ℚ) / (nat.choose n (n - nat.succ k)),
      rw ← add_div,
      norm_cast,
    rw this,
    apply add_le_add_left,
    transitivity,
      exact ih (le_of_lt hk),
    apply local_lym (nat.le_sub_left_of_add_le hk) (nat.sub_le _ _) (decompose'_layer _ _)
  end

  lemma sum_flip {α : Type*} [add_comm_monoid α] {n : ℕ} (f : ℕ → α) : sum (range (n+1)) (λ r, f (n - r)) = sum (range (n+1)) (λ r, f r) :=
  begin
    induction n with n ih,
      rw [sum_range_one, sum_range_one],
    rw sum_range_succ',
    rw sum_range_succ _ (nat.succ n),
    simp [ih],
  end

  lemma card_decompose_other (H : antichain 𝒜) : 
    (range (n+1)).sum (λ r, ((𝒜#r).card : ℚ) / nat.choose n r) ≤ (decompose' 𝒜 n).card / nat.choose n 0 :=
  begin
    rw [← nat.sub_self n],
    convert ← card_decompose'_other (le_refl n) H using 1,
    apply sum_flip (λ r, ((𝒜#r).card : ℚ) / nat.choose n r), 
  end

  lemma lubell_yamamoto_meshalkin (H : antichain 𝒜) : (range (n+1)).sum (λ r, ((𝒜#r).card : ℚ) / nat.choose n r) ≤ 1 :=
  begin
    transitivity,
      apply card_decompose_other H,
    rw div_le_iff; norm_cast,
      simpa only [card_fin, mul_one, nat.choose_zero_right, nat.sub_self] using size_in_layer (decompose'_layer 𝒜 n),
    apply nat.choose_pos (zero_le n)
  end
end lym

lemma dominate_choose_lt {r n : ℕ} (h : r < n/2) : nat.choose n r ≤ nat.choose n (r+1) :=
begin
  refine le_of_mul_le_mul_right _ (nat.lt_sub_left_of_add_lt (lt_of_lt_of_le h (nat.div_le_self n 2))),
  rw ← nat.choose_succ_right_eq,
  apply nat.mul_le_mul_left,
  rw ← nat.lt_iff_add_one_le,
  apply nat.lt_sub_left_of_add_lt,
  rw ← mul_two,
  exact lt_of_lt_of_le (mul_lt_mul_of_pos_right h zero_lt_two) (nat.div_mul_le_self n 2),
end

lemma dominate_choose_lt' {n r : ℕ} (hr : r ≤ n/2) : nat.choose n r ≤ nat.choose n (n/2) :=
begin
  refine (@nat.decreasing_induction (λ k, k ≤ n/2 → nat.choose n k ≤ nat.choose n (n/2)) _ r (n/2) hr (λ _, by refl)) hr,
  intros m k a,
  cases lt_or_eq_of_le a,
    transitivity nat.choose n (m + 1),
      exact dominate_choose_lt h,
    exact k h,
  rw h,
end 

lemma dominate_choose {r n : ℕ} : nat.choose n r ≤ nat.choose n (n/2) :=
begin
  cases le_or_gt r n with b b,
    cases le_or_gt r (n/2) with a,
      apply dominate_choose_lt' a,
    rw ← nat.choose_symm b,
    apply dominate_choose_lt',
    rw [gt_iff_lt, nat.div_lt_iff_lt_mul _ _ zero_lt_two] at h,
    rw [nat.le_div_iff_mul_le _ _ zero_lt_two, nat.mul_sub_right_distrib, nat.sub_le_iff, mul_two, nat.add_sub_cancel],
    exact le_of_lt h,
  rw nat.choose_eq_zero_of_lt b,
  apply zero_le
end

lemma sum_div {α : Type*} {s : finset α} {f : α → ℚ} {b : ℚ} : s.sum f / b = s.sum (λx, f x / b) :=
calc s.sum f / b = s.sum (λ x, f x * (1 / b)) : by rw [div_eq_mul_one_div, sum_mul]
     ...         = s.sum (λ x, f x / b) : by congr; ext; rw ← div_eq_mul_one_div

lemma sperner (H : antichain 𝒜) : 𝒜.card ≤ nat.choose n (n / 2) := 
begin
  have q1 := lubell_yamamoto_meshalkin H,
  set f := (λ (r : ℕ), ((𝒜#r).card : ℚ) / nat.choose n r),
  set g := (λ (r : ℕ), ((𝒜#r).card : ℚ) / nat.choose n (n/2)),
  have q2 : sum (range (n + 1)) g ≤ sum (range (n + 1)) f,
    apply sum_le_sum,
    intros r hr,
    apply div_le_div_of_le_left; norm_cast,
        apply zero_le,
      apply nat.choose_pos,
      rw mem_range at hr,
      rwa ← nat.lt_succ_iff,
    apply dominate_choose,
  
  have := trans q2 q1,
  rw [← sum_div, ← sum_nat_cast, div_le_one_iff_le] at this,
    swap, norm_cast, apply nat.choose_pos (nat.div_le_self _ _),
  norm_cast at this,
  rw ← card_bind at this,
    suffices m: finset.bind (range (n + 1)) (λ (u : ℕ), 𝒜#u) = 𝒜,
      rwa m at this,
    ext,
    rw mem_bind,
    split, rintro ⟨_,_,q⟩,
      rw mem_slice at q,
      exact q.1,
    intro, 
    refine ⟨a.card, _, _⟩,
      rw [mem_range, nat.lt_succ_iff],
      conv {to_rhs, rw ← card_fin n},
      apply card_le_of_subset (subset_univ a),
    rw mem_slice,
    tauto,
  intros x _ y _ ne,
  rw disjoint_left,
  intros a Ha k,
  exact ne_of_diff_slice Ha k ne rfl
end

lemma sdiff_union_inter {α : Type*} [decidable_eq α] (A B : finset α) : (A \ B) ∪ (A ∩ B) = A :=
by simp only [ext, mem_union, mem_sdiff, mem_inter]; tauto

lemma sdiff_inter_inter {α : Type*} [decidable_eq α] (A B : finset α) : disjoint (A \ B) (A ∩ B) := disjoint_of_subset_right (inter_subset_right _ _) sdiff_disjoint
-- by simp only [ext, mem_inter, mem_sdiff, not_mem_empty]; tauto

namespace ij
section 
  variables (i j : X)
  
  def compress (i j : X) (A : finset X) : finset X := 
  if (j ∈ A ∧ i ∉ A)
    then insert i (A.erase j)
    else A

  local notation `C` := compress i j

  def compressed_set {A : finset X} : ¬ (j ∈ C A ∧ i ∉ C A) :=
  begin
    intro,
    rw compress at a,
    split_ifs at a,
      apply a.2,
      apply mem_insert_self,
    exact h a
  end

  lemma compress_idem (A : finset X) : C (C A) = C A :=
  begin
    rw compress,
    split_ifs,
      exfalso,
      apply compressed_set _ _ h,
    refl
  end

  @[reducible] def compress_motion (𝒜 : finset (finset X)) : finset (finset X) := 𝒜.filter (λ A, C A ∈ 𝒜)
  @[reducible] def compress_remains (𝒜 : finset (finset X)) : finset (finset X) := (𝒜.filter (λ A, C A ∉ 𝒜)).image (λ A, C A)

  def compress_family (i j : X) (𝒜 : finset (finset X)) : finset (finset X) :=
  @compress_remains _ i j 𝒜 ∪ @compress_motion _ i j 𝒜

  local notation `CC` := compress_family i j

  lemma mem_compress_motion (A : finset X) : A ∈ compress_motion i j 𝒜 ↔ A ∈ 𝒜 ∧ C A ∈ 𝒜 :=
  by rw mem_filter

  lemma mem_compress_remains (A : finset X) : A ∈ compress_remains i j 𝒜 ↔ A ∉ 𝒜 ∧ (∃ B ∈ 𝒜, C B = A) :=
  begin
    simp [compress_remains], 
    split; rintro ⟨p, q, r⟩,
      exact ⟨r ▸ q.2, p, ⟨q.1, r⟩⟩,
    exact ⟨q, ⟨r.1, r.2.symm ▸ p⟩, r.2⟩, 
  end

  lemma mem_compress {A : finset X} : A ∈ CC 𝒜 ↔ (A ∉ 𝒜 ∧ (∃ B ∈ 𝒜, C B = A)) ∨ (A ∈ 𝒜 ∧ C A ∈ 𝒜) :=
  by rw [compress_family, mem_union, mem_compress_motion, mem_compress_remains]

  lemma compress_disjoint (i j : fin n) : disjoint (compress_remains i j 𝒜) (compress_motion i j 𝒜) :=
  begin
    rw disjoint_left,
    intros A HA HB,
    rw mem_compress_motion at HB,
    rw mem_compress_remains at HA,
    exact HA.1 HB.1
  end

  lemma inj_ish {i j : X} (A B : finset X) (hA : j ∈ A ∧ i ∉ A) (hY : j ∈ B ∧ i ∉ B) 
    (Z : insert i (erase A j) = insert i (erase B j)) : A = B := 
  begin
    ext x, split,
    all_goals { intro p, 
                by_cases h₁: (x=j), {rw h₁, tauto}, 
                have h₂: x ≠ i, {intro, rw a at p, tauto},
                rw ext at Z,
                replace Z := Z x,
                simp only [mem_insert, mem_erase] at Z,
                tauto }
  end

  lemma compressed_size : (CC 𝒜).card = 𝒜.card :=
  begin
    rw [compress_family, card_disjoint_union (compress_disjoint _ _), card_image_of_inj_on],
      rw [← card_disjoint_union, union_comm, filter_union_filter_neg_eq],
      rw [disjoint_iff_inter_eq_empty, inter_comm],
      apply filter_inter_filter_neg_eq,
    intros A HX Y HY Z,
    rw mem_filter at HX HY,
    rw compress at HX Z,
    split_ifs at HX Z,
      rw compress at HY Z,
      split_ifs at HY Z,
        refine inj_ish A Y h h_1 Z,
      tauto,
    tauto
  end

  lemma insert_erase_comm {i j : fin n} {A : finset X} (h : i ≠ j) : insert i (erase A j) = erase (insert i A) j :=
  begin
    simp only [ext, mem_insert, mem_erase],
    intro x,
    split; intro p,
      cases p, split, rw p, 
    all_goals {tauto},
  end

  lemma compress_moved {i j : X} {A : finset X} (h₁ : A ∈ compress_family i j 𝒜) (h₂ : A ∉ 𝒜) : i ∈ A ∧ j ∉ A ∧ erase (insert j A) i ∈ 𝒜 :=
  begin
    rw mem_compress at h₁,
    rcases h₁ with ⟨_, B, H, HB⟩ | _,
      rw compress at HB,
      split_ifs at HB,
        rw ← HB,
        refine ⟨mem_insert_self _ _, _, _⟩,
          rw mem_insert,
          intro,
          cases a,
            safe,
          apply not_mem_erase j B a,
        have: erase (insert j (insert i (erase B j))) i = B,
          rw [insert_erase_comm, insert_erase (mem_insert_of_mem h.1), erase_insert h.2], 
          safe, 
        rwa this,
      rw HB at H, tauto,
    tauto
  end

  lemma compress_held {i j : X} {A : finset X} (h₁ : j ∈ A) (h₂ : A ∈ compress_family i j 𝒜) : A ∈ 𝒜 :=
  begin
    rw mem_compress at h₂,
    rcases h₂ with ⟨_, B, H, HB⟩ | _,
      rw ← HB at h₁,
      rw compress at HB h₁,
      split_ifs at HB h₁,
        rw mem_insert at h₁,
        cases h₁,
          safe,
        exfalso, apply not_mem_erase _ _ h₁,
      rwa ← HB,
    tauto
  end

  lemma compress_both {i j : X} {A : finset X} (h₁ : A ∈ compress_family i j 𝒜) (h₂ : j ∈ A) (h₃ : i ∉ A) : erase (insert i A) j ∈ 𝒜 :=
  begin
    have: A ∈ 𝒜, apply compress_held ‹_› ‹_›,
    rw mem_compress at h₁,
    replace h₁ : C A ∈ 𝒜, tauto,
    rw compress at h₁,
    have: j ∈ A ∧ i ∉ A := ⟨h₂, h₃⟩,
    split_ifs at h₁,
    rwa ← insert_erase_comm,
    intro, rw a at *, tauto,
  end

  lemma compression_reduces_shadow : (∂ CC 𝒜).card ≤ (∂𝒜).card := 
  begin
    set 𝒜' := CC 𝒜,
    suffices: (∂𝒜' \ ∂𝒜).card ≤ (∂𝒜 \ ∂𝒜').card,
      suffices z: card (∂𝒜' \ ∂𝒜 ∪ ∂𝒜' ∩ ∂𝒜) ≤ card (∂𝒜 \ ∂𝒜' ∪ ∂𝒜 ∩ ∂𝒜'),
        rwa [sdiff_union_inter, sdiff_union_inter] at z,
      rw [card_disjoint_union, card_disjoint_union, inter_comm],
      apply add_le_add_right ‹_›,
      any_goals { apply sdiff_inter_inter },

    have q₁: ∀ B ∈ ∂𝒜' \ ∂𝒜, i ∈ B ∧ j ∉ B ∧ erase (insert j B) i ∈ ∂𝒜 \ ∂𝒜',
      intros B HB,
      obtain ⟨k, k'⟩: B ∈ ∂𝒜' ∧ B ∉ ∂𝒜 := mem_sdiff.1 HB,
      have m: ∀ y ∉ B, insert y B ∉ 𝒜,
        intros y _ _,
        apply k',
        rw mem_shadow',
        exact ⟨y, H, a⟩,
      rcases mem_shadow'.1 k with ⟨x, _, _⟩,
      have q := compress_moved ‹insert x B ∈ 𝒜'› (m _ ‹x ∉ B›),
      rw insert.comm at q,
      have: j ∉ B := q.2.1 ∘ mem_insert_of_mem,
      have: i ≠ j, safe,
      have: x ≠ i, intro a, rw a at *, rw [erase_insert] at q, 
        exact m _ ‹j ∉ B› q.2.2,
        rw mem_insert, tauto,
      have: x ≠ j, intro a, rw a at q, exact q.2.1 (mem_insert_self _ _), 
      have: i ∈ B := mem_of_mem_insert_of_ne q.1 ‹x ≠ i›.symm,
      refine ⟨‹_›, ‹_›, _⟩,
      rw mem_sdiff,
      split,
        rw mem_shadow',
        rw ← insert_erase_comm ‹x ≠ i› at q,
        refine ⟨x, _, q.2.2⟩, 
        intro a, 
        exact ‹x ∉ B› (mem_of_mem_insert_of_ne (mem_of_mem_erase a) ‹x ≠ j›),

      intro a, rw mem_shadow' at a, 
      rcases a with ⟨y, yH, H⟩,
      have: y ≠ i, intro b, rw [b, insert_erase (mem_insert_of_mem ‹i ∈ B›)] at H, 
                  exact m _ ‹j ∉ B› (compress_held (mem_insert_self _ _) H), 
      have: y ≠ j, rw [mem_erase, mem_insert] at yH, tauto,
      have: y ∉ B, rw [mem_erase, mem_insert] at yH, tauto,
      have: j ∈ insert y (erase (insert j B) i), finish,
      have: i ∉ insert y (erase (insert j B) i), finish,
      have := compress_both H ‹_› ‹_›,
      rw [insert.comm, ← insert_erase_comm ‹y ≠ j›, insert_erase (mem_insert_of_mem ‹i ∈ B›), erase_insert ‹j ∉ B›] at this,
      exact m _ ‹y ∉ B› ‹insert y B ∈ 𝒜›,
    
    set f := (λ (B : finset X), erase (insert j B) i),
    apply card_le_card_of_inj_on f,
      intros _ HB,
      exact (q₁ _ HB).2.2,
  
    intros B₁ HB₁ B₂ HB₂ f₁,
    have := q₁ B₁ HB₁,
    have := q₁ B₂ HB₂,
    rw ext at f₁,
    ext,
    split,
    all_goals { intro,
                have p := f₁ a,
                simp only [mem_erase, mem_insert] at p,
                by_cases (a = i),
                  rw h, tauto,
                rw [and_iff_right h, and_iff_right h] at p,
                have z: j ∉ B₁ ∧ j ∉ B₂, tauto,
                have: a ≠ j, safe,
                tauto }
  end
end
end ij

@[simp] lemma sdiff_empty {α : Type*} [decidable_eq α] (s : finset α) : s \ ∅ = s := empty_union s
@[simp] lemma sdiff_idem {α : Type*} [decidable_eq α] (s t : finset α) : s \ t \ t = s \ t := by simp only [ext, mem_sdiff]; tauto
lemma union_sdiff {α : Type*} [decidable_eq α] (s₁ s₂ t : finset α) : (s₁ ∪ s₂) \ t = s₁ \ t ∪ s₂ \ t := by simp only [ext, mem_sdiff, mem_union]; tauto
lemma inter_union_self {α : Type*} [decidable_eq α] (s t : finset α) : s ∩ (t ∪ s) = s := by simp only [ext, mem_inter, mem_union]; tauto
lemma union_sdiff_self {α : Type*} [decidable_eq α] (s t : finset α) : (s ∪ t) \ t = s \ t := by simp only [ext, mem_union, mem_sdiff]; tauto
lemma sdiff_singleton_eq_erase {α : Type*} [decidable_eq α] (a : α) (s : finset α) : s \ finset.singleton a = erase s a := begin ext, rw [mem_erase, mem_sdiff, mem_singleton], tauto end
lemma sdiff_union {α : Type*} [decidable_eq α] (s t₁ t₂ : finset α) : s \ (t₁ ∪ t₂) = (s \ t₁) ∩ (s \ t₂) := by simp only [ext, mem_union, mem_sdiff, mem_inter]; tauto
lemma not_sure {α : Type*} [decidable_eq α] {s t : finset α} (h : t ⊆ s) : s ∪ t = s := by simp only [ext, mem_union]; tauto
lemma new_thing {α : Type*} [decidable_eq α] {s t : finset α} : disjoint s t ↔ s \ t = s := 
begin
  split; intro p,
    rw disjoint_iff_inter_eq_empty at p,
    exact union_empty (s \ t) ▸ (p ▸ sdiff_union_inter s t), 
  rw ← p, apply sdiff_disjoint
end
lemma disjoint_self_iff_empty {α : Type*} [decidable_eq α] (s : finset α) : disjoint s s ↔ s = ∅ :=
disjoint_self

lemma sdiff_subset_left {α : Type*} [decidable_eq α] (s t : finset α) : s \ t ⊆ s := by have := sdiff_subset_sdiff (le_refl s) (empty_subset t); rwa sdiff_empty at this

instance decidable_disjoint (U V : finset X) : decidable (disjoint U V) := 
dite (U ∩ V = ∅) (is_true ∘ disjoint_iff_inter_eq_empty.2) (is_false ∘ mt disjoint_iff_inter_eq_empty.1)

lemma sum_lt_sum {α β : Type*} {s : finset α} {f g : α → β} [decidable_eq α] [ordered_cancel_comm_monoid β] : s ≠ ∅ → (∀x∈s, f x < g x) → s.sum f < s.sum g := 
begin
  apply finset.induction_on s,
    intro a, exfalso, apply a, refl,
  intros x s not_mem ih _ assump,
  rw sum_insert not_mem, rw sum_insert not_mem,
  apply lt_of_lt_of_le,
    rw add_lt_add_iff_right (s.sum f),
    apply assump x (mem_insert_self _ _),
  rw add_le_add_iff_left,
  by_cases (s = ∅),
    rw h,
    rw sum_empty,
    rw sum_empty,
  apply le_of_lt,
  apply ih h,
  intros x hx,
  apply assump,
  apply mem_insert_of_mem hx
end

namespace UV
section 
  variables (U V : finset X)
  
  -- We'll only use this when |U| = |V| and U ∩ V = ∅
  def compress (U V : finset X) (A : finset X) :=
  if disjoint U A ∧ (V ⊆ A)
    then (A ∪ U) \ V
    else A

  local notation `C` := compress U V

  lemma compress_size (A : finset X) (h₁ : disjoint U V) (h₂ : U.card = V.card) : (C A).card = A.card :=
  begin
    rw compress, split_ifs, 
    rw card_sdiff (subset.trans h.2 (subset_union_left _ _)), 
    rw card_disjoint_union h.1.symm, rw h₂, apply nat.add_sub_cancel, 
    refl
  end

  lemma compress_idem (A : finset X) : C (C A) = C A :=
  begin
    rw [compress, compress],
    split_ifs,
        suffices: U = ∅,
          rw [this, union_empty, union_empty, sdiff_idem],
        have: U \ V = U := new_thing.1 (disjoint_of_subset_right h.2 h.1),
        rw ← disjoint_self_iff_empty,
        apply disjoint_of_subset_right (subset_union_right (A\V) _),
        rw [union_sdiff, ‹U \ V = U›] at h_1,
        tauto,
      refl,
    refl,
  end

  @[reducible] def compress_motion (𝒜 : finset (finset X)) : finset (finset X) := 𝒜.filter (λ A, C A ∈ 𝒜)
  @[reducible] def compress_remains (𝒜 : finset (finset X)) : finset (finset X) := (𝒜.filter (λ A, C A ∉ 𝒜)).image (λ A, C A)

  def compress_family (U V : finset X) (𝒜 : finset (finset X)) : finset (finset X) :=
  compress_remains U V 𝒜 ∪ compress_motion U V 𝒜

  local notation `CC` := compress_family U V

  lemma mem_compress_motion (A : finset X) : A ∈ compress_motion U V 𝒜 ↔ A ∈ 𝒜 ∧ C A ∈ 𝒜 :=
  by rw mem_filter

  lemma mem_compress_remains (A : finset X) : A ∈ compress_remains U V 𝒜 ↔ A ∉ 𝒜 ∧ (∃ B ∈ 𝒜, C B = A) :=
  begin
    simp [compress_remains], 
    split; rintro ⟨p, q, r⟩,
      exact ⟨r ▸ q.2, p, ⟨q.1, r⟩⟩,
    exact ⟨q, ⟨r.1, r.2.symm ▸ p⟩, r.2⟩, 
  end

  def is_compressed (𝒜 : finset (finset X)) : Prop := CC 𝒜 = 𝒜

  lemma is_compressed_empty (𝒜 : finset (finset X)) : is_compressed ∅ ∅ 𝒜 := 
  begin
    have q: ∀ (A : finset X), compress ∅ ∅ A = A,
      simp [compress],
    rw [is_compressed, compress_family], 
    ext, rw mem_union, rw mem_compress_remains, rw mem_compress_motion,
    repeat {conv in (compress ∅ ∅ _) {rw q _}},
    safe
  end

  lemma mem_compress {A : finset X} : A ∈ CC 𝒜 ↔ (A ∉ 𝒜 ∧ (∃ B ∈ 𝒜, C B = A)) ∨ (A ∈ 𝒜 ∧ C A ∈ 𝒜) :=
  by rw [compress_family, mem_union, mem_compress_motion, mem_compress_remains]

  lemma compress_family_size (r : ℕ) (𝒜 : finset (finset X)) (h₁ : disjoint U V) (h₂ : U.card = V.card) (h₃ : is_layer 𝒜 r) : is_layer (CC 𝒜) r :=
  begin
    intros A HA,
    rw mem_compress at HA, 
    rcases HA with ⟨_, _, z₁, z₂⟩ | ⟨z₁, _⟩,
      rw ← z₂, rw compress_size _ _ _ h₁ h₂, 
    all_goals {apply h₃ _ z₁}
  end

  lemma compress_family_idempotent (𝒜 : finset (finset X)) : CC (CC 𝒜) = CC 𝒜 :=
  begin
    have: ∀ A ∈ compress_family U V 𝒜, compress U V A ∈ compress_family U V 𝒜,
      intros A HA,
      rw mem_compress at HA ⊢,
      rw [compress_idem, and_self],
      rcases HA with ⟨_, B, _, cB_eq_A⟩ | ⟨_, _⟩,
        left, rw ← cB_eq_A, refine ⟨_, B, ‹_›, _⟩; rw compress_idem,
        rwa cB_eq_A,
      right, assumption,
    have: filter (λ A, compress U V A ∉ compress_family U V 𝒜) (compress_family U V 𝒜) = ∅,
      rw ← filter_false (compress_family U V 𝒜),
      apply filter_congr,
      simpa,
    rw [compress_family, compress_remains, this, image_empty, union_comm, compress_motion, ← this],
    apply filter_union_filter_neg_eq (compress_family U V 𝒜)
  end

  lemma compress_disjoint (U V : finset X) : disjoint (compress_remains U V 𝒜) (compress_motion U V 𝒜) :=
  begin
    rw disjoint_left,
    intros A HA HB,
    rw mem_compress_motion at HB,
    rw mem_compress_remains at HA,
    exact HA.1 HB.1
  end

  lemma inj_ish {U V : finset X} (A B : finset X) (hA : disjoint U A ∧ V ⊆ A) (hB : disjoint U B ∧ V ⊆ B)
    (Z : (A ∪ U) \ V = (B ∪ U) \ V) : A = B :=
  begin
    ext x, split,
    all_goals {
      intro p,
      by_cases h₁: (x ∈ V), 
        { exact hB.2 h₁ <|> exact hA.2 h₁ },
      have := mem_sdiff.2 ⟨mem_union_left U ‹_›, h₁⟩,
      rw Z at this <|> rw ← Z at this,
      rw [mem_sdiff, mem_union] at this,
      suffices: x ∉ U, tauto,
      apply disjoint_right.1 _ p, tauto
    }
  end

  lemma compressed_size : (CC 𝒜).card = 𝒜.card :=
  begin
    rw [compress_family, card_disjoint_union (compress_disjoint _ _), card_image_of_inj_on],
      rw [← card_disjoint_union, union_comm, filter_union_filter_neg_eq],
      rw [disjoint_iff_inter_eq_empty, inter_comm],
      apply filter_inter_filter_neg_eq,
    intros A HX Y HY Z,
    rw mem_filter at HX HY,
    rw compress at HX Z,
    split_ifs at HX Z,
      rw compress at HY Z,
      split_ifs at HY Z,
        refine inj_ish A Y h h_1 Z,
      tauto,
    tauto
  end

  lemma compress_held {U V : finset X} {A : finset X} (h₁ : A ∈ compress_family U V 𝒜) (h₂ : V ⊆ A) (h₃ : U.card = V.card) : A ∈ 𝒜 :=
  begin
    rw mem_compress at h₁,
    rcases h₁ with ⟨_, B, H, HB⟩ | _,
      rw compress at HB,
      split_ifs at HB,
        have: V = ∅,
          apply eq_empty_of_forall_not_mem,
          intros x xV, replace h₂ := h₂ xV, 
          rw [← HB, mem_sdiff] at h₂, exact h₂.2 xV,
        have: U = ∅,
          rwa [← card_eq_zero, h₃, card_eq_zero],
        rw [‹U = ∅›, ‹V = ∅›, union_empty, sdiff_empty] at HB,
        rwa ← HB, 
      rwa ← HB,
    tauto,
  end

  lemma compress_moved {U V : finset X} {A : finset X} (h₁ : A ∈ compress_family U V 𝒜) (h₂ : A ∉ 𝒜) : U ⊆ A ∧ disjoint V A ∧ (A ∪ V) \ U ∈ 𝒜 :=
  begin
    rw mem_compress at h₁,
    rcases h₁ with ⟨_, B, H, HB⟩ | _,
    { rw compress at HB,
      split_ifs at HB, { 
        rw ← HB at *,
        refine ⟨_, disjoint_sdiff, _⟩,
          have: disjoint U V := disjoint_of_subset_right h.2 h.1,
          rw union_sdiff, rw new_thing.1 this, apply subset_union_right _ _,
        rwa [sdiff_union_of_subset, union_sdiff_self, new_thing.1 h.1.symm],
        apply trans h.2 (subset_union_left _ _)},
      { rw HB at *, tauto } },
    tauto
  end

  lemma uncompressed_was_already_there {U V : finset X} {A : finset X} (h₁ : A ∈ compress_family U V 𝒜) (h₂ : V ⊆ A) (h₃ : disjoint U A) : (A ∪ U) \ V ∈ 𝒜 :=
  begin
    rw mem_compress at h₁,
    have: disjoint U A ∧ V ⊆ A := ⟨h₃, h₂⟩,
    rcases h₁ with ⟨_, B, B_in_A, cB_eq_A⟩ | ⟨_, cA_in_A⟩,
    { by_cases a: (A ∪ U) \ V = A,
        have: U \ V = U := new_thing.1 (disjoint_of_subset_right h₂ h₃),
        have: U = ∅,
          rw ← disjoint_self_iff_empty,
          suffices: disjoint U (U \ V), rw ‹U \ V = U› at this, assumption,
          apply disjoint_of_subset_right (subset_union_right (A\V) _),
          rwa [← union_sdiff, a],
        have: V = ∅,
          rw ← disjoint_self_iff_empty, apply disjoint_of_subset_right h₂,
          rw ← a, apply disjoint_sdiff,
        simpa [a, cB_eq_A.symm, compress, ‹U = ∅›, ‹V = ∅›],
      have: compress U V A = (A ∪ U) \ V,
        rw compress, split_ifs, refl,
      exfalso,
      apply a,
      rw [← this, ← cB_eq_A, compress_idem] },
    { rw compress at cA_in_A,
      split_ifs at cA_in_A,
      assumption }
  end

  lemma compression_reduces_shadow (h₁ : ∀ x ∈ U, ∃ y ∈ V, is_compressed (erase U x) (erase V y) 𝒜) (h₂ : U.card = V.card) : 
    (∂ CC 𝒜).card ≤ (∂𝒜).card := 
  begin
    set 𝒜' := CC 𝒜,
    suffices: (∂𝒜' \ ∂𝒜).card ≤ (∂𝒜 \ ∂𝒜').card,
      suffices z: card (∂𝒜' \ ∂𝒜 ∪ ∂𝒜' ∩ ∂𝒜) ≤ card (∂𝒜 \ ∂𝒜' ∪ ∂𝒜 ∩ ∂𝒜'),
        rwa [sdiff_union_inter, sdiff_union_inter] at z,
      rw [card_disjoint_union, card_disjoint_union, inter_comm],
      apply add_le_add_right ‹_›,
      any_goals { apply sdiff_inter_inter },
    
    have q₁: ∀ B ∈ ∂𝒜' \ ∂𝒜, U ⊆ B ∧ disjoint V B ∧ (B ∪ V) \ U ∈ ∂𝒜 \ ∂𝒜',
      intros B HB,
      obtain ⟨k, k'⟩: B ∈ ∂𝒜' ∧ B ∉ ∂𝒜 := mem_sdiff.1 HB,
      have m: ∀ y ∉ B, insert y B ∉ 𝒜 := λ y H a, k' (mem_shadow'.2 ⟨y, H, a⟩),
      rcases mem_shadow'.1 k with ⟨x, _, _⟩,
      have q := compress_moved ‹insert x B ∈ 𝒜'› (m _ ‹x ∉ B›),
      have: disjoint V B := (disjoint_insert_right.1 q.2.1).2,
      have: disjoint V U := disjoint_of_subset_right q.1 q.2.1,
      have: V \ U = V, rwa ← new_thing,
      have: x ∉ U,
        intro a, 
        rcases h₁ x ‹x ∈ U› with ⟨y, Hy, xy_comp⟩,
        apply m y (disjoint_left.1 ‹disjoint V B› Hy),
        rw is_compressed at xy_comp,
        have: (insert x B ∪ V) \ U ∈ compress_family (erase U x) (erase V y) 𝒜, rw xy_comp, exact q.2.2,
        have: ((insert x B ∪ V) \ U ∪ erase U x) \ erase V y ∈ 𝒜,
          apply uncompressed_was_already_there this _ (disjoint_of_subset_left (erase_subset _ _) disjoint_sdiff),
            rw [union_sdiff, ‹V \ U = V›],
            apply subset.trans (erase_subset _ _) (subset_union_right _ _), 
        suffices: ((insert x B ∪ V) \ U ∪ erase U x) \ erase V y = insert y B,
          rwa ← this,
        by calc (((insert x B ∪ V) \ U) ∪ erase U x) \ erase V y 
            = (((insert x B ∪ V) \ finset.singleton x ∪ erase U x) ∩ ((insert x B ∪ V) \ erase U x ∪ erase U x)) \ erase V y : 
                                  by rw [← union_distrib_right, ← sdiff_union, union_singleton_eq_insert, insert_erase a]
        ... = (erase (insert x (B ∪ V)) x ∪ erase U x) ∩ (insert x B ∪ V) \ erase V y : 
                                  by rw sdiff_union_of_subset (trans (erase_subset _ _) (trans q.1 (subset_union_left _ _))); rw insert_union; rw sdiff_singleton_eq_erase 
        ... = (B ∪ erase U x ∪ V) ∩ (insert x B ∪ V) \ erase V y : 
                                  begin rw erase_insert, rw union_right_comm, rw mem_union, exact (λ a_1, disjoint_left.1 ‹disjoint V U› (or.resolve_left a_1 ‹x ∉ B›) ‹x ∈ U›) end
        ... = (B ∪ V) \ erase V y : 
                                  by rw ← union_distrib_right; congr; rw [not_sure (subset_insert_iff.1 q.1), inter_insert_of_not_mem ‹x ∉ B›, inter_self]
        ... = (insert y B ∪ erase V y) \ erase V y :  
                                  by rw [← union_singleton_eq_insert, union_comm _ B, union_assoc, union_singleton_eq_insert, insert_erase ‹y ∈ V›]
        ... = insert y B : 
                                  begin rw [union_sdiff_self, ← new_thing, disjoint_insert_left], refine ⟨not_mem_erase _ _, disjoint_of_subset_right (erase_subset _ _) ‹disjoint V B›.symm⟩ end,
      have: U ⊆ B, rw [← erase_eq_of_not_mem ‹x ∉ U›, ← subset_insert_iff], exact q.1,
      refine ⟨‹_›, ‹_›, _⟩,
      rw mem_sdiff,
      have: x ∉ V := disjoint_right.1 q.2.1 (mem_insert_self _ _),
      split,
        rw mem_shadow',
        refine ⟨x, _, _⟩,
        { simp [mem_sdiff, mem_union], safe },
        have: insert x ((B ∪ V) \ U) = (insert x B ∪ V) \ U,
          simp [ext, mem_sdiff, mem_union, mem_insert], 
          intro a,
          split; intro p,
            cases p,
              rw p at *, tauto,
            tauto,
          tauto,
        rw this, tauto,
      rw mem_shadow',
      rintro ⟨w, _, _⟩,
      by_cases (w ∈ U),
        rcases h₁ w ‹w ∈ U› with ⟨z, Hz, xy_comp⟩,
        apply m z (disjoint_left.1 ‹disjoint V B› Hz),
        have: insert w ((B ∪ V) \ U) ∈ 𝒜, {
          apply compress_held a_h_h _ h₂, 
          apply subset.trans _ (subset_insert _ _),
          rw union_sdiff, rw ‹V \ U = V›, apply subset_union_right
        },
        have: (insert w ((B ∪ V) \ U) ∪ erase U w) \ erase V z ∈ 𝒜,
          refine uncompressed_was_already_there _ _ _, 
              rw is_compressed at xy_comp,
              rwa xy_comp,
            apply subset.trans (erase_subset _ _),
            apply subset.trans _ (subset_insert _ _),
            rw union_sdiff,
            rw ‹V \ U = V›,
            apply subset_union_right,
          rw disjoint_insert_right,
          split, apply not_mem_erase,
          apply disjoint_of_subset_left (erase_subset _ _),
          apply disjoint_sdiff,
        have: (insert w ((B ∪ V) \ U) ∪ erase U w) \ erase V z = insert z B,
        by calc (insert w ((B ∪ V) \ U) ∪ erase U w) \ erase V z = (finset.singleton w ∪ ((B ∪ V) \ U) ∪ erase U w) \ erase V z : begin congr, end
        ... = (((B ∪ V) \ U) ∪ (finset.singleton w ∪ erase U w)) \ erase V z : begin rw [union_left_comm, union_assoc] end
        ... = (((B ∪ V) \ U) ∪ U) \ erase V z : begin congr, rw union_singleton_eq_insert, rw insert_erase h end
        ... = (B ∪ V) \ erase V z : begin rw sdiff_union_of_subset, apply subset.trans ‹U ⊆ B› (subset_union_left _ _) end
        ... = B \ erase V z ∪ V \ erase V z : begin rw union_sdiff end
        ... = B ∪ V \ erase V z : begin congr, rw ← new_thing, apply disjoint_of_subset_right (erase_subset _ _) ‹disjoint V B›.symm end
        ... = B ∪ finset.singleton z : begin congr, ext, simp, split, intro p, by_contra, exact p.2 ‹_› p.1, intro p, rw p, tauto end
        ... = insert z B : begin rw [union_comm, union_singleton_eq_insert] end,
        rwa ← this,
      have: w ∉ V,
        intro, have: w ∈ B ∪ V := mem_union_right _ ‹_›,
        exact a_h_w (mem_sdiff.2 ⟨‹_›, ‹_›⟩),
      have: w ∉ B,
        intro, have: w ∈ B ∪ V := mem_union_left _ ‹_›,
        exact a_h_w (mem_sdiff.2 ⟨‹_›, ‹_›⟩),
      apply m w this,
      
      have: (insert w ((B ∪ V) \ U) ∪ U) \ V ∈ 𝒜, 
      refine uncompressed_was_already_there ‹insert w ((B ∪ V) \ U) ∈ 𝒜'› (trans _ (subset_insert _ _)) _,
          rw union_sdiff,
           rw ‹V \ U = V›,
          apply subset_union_right,
        rw disjoint_insert_right,
        exact ⟨‹_›, disjoint_sdiff⟩,
      suffices: insert w B = (insert w ((B ∪ V) \ U) ∪ U) \ V,
        rwa this,
      rw insert_union,
      rw sdiff_union_of_subset (trans ‹U ⊆ B› (subset_union_left _ _)),
      rw ← insert_union,
      rw union_sdiff_self, 
      conv {to_lhs, rw ← sdiff_union_inter (insert w B) V},
      suffices: insert w B ∩ V = ∅,
        rw this, rw union_empty, 
      rw ← disjoint_iff_inter_eq_empty,
      rw disjoint_insert_left,
      split,
        assumption,
      rwa disjoint.comm,
    set f := (λ B, (B ∪ V) \ U),
    apply card_le_card_of_inj_on f (λ B HB, (q₁ B HB).2.2),
    intros B₁ HB₁ B₂ HB₂ k,
    exact inj_ish B₁ B₂ ⟨(q₁ B₁ HB₁).2.1, (q₁ B₁ HB₁).1⟩ ⟨(q₁ B₂ HB₂).2.1, (q₁ B₂ HB₂).1⟩ k
  end

  def bin_measure (A : finset X) : ℕ := A.sum (λ x, pow 2 x.val)

  lemma binary_sum (k : ℕ) (A : finset ℕ) (h₁ : ∀ x ∈ A, x < k) : A.sum (pow 2) < 2^k :=
  begin
    apply lt_of_le_of_lt (sum_le_sum_of_subset (λ t th, mem_range.2 (h₁ t th))),
    have z := geom_sum_mul_add 1 k, rw [geom_series, mul_one] at z, 
    simp only [nat.pow_eq_pow] at z, rw ← z, apply nat.lt_succ_self
  end

  lemma binary_sum' (k : ℕ) (A : finset X) (h₁ : ∀ (x : X), x ∈ A → x.val < k) : bin_measure A < 2^k :=
  begin
    suffices: bin_measure A = (A.image (λ (x : X), x.val)).sum (pow 2),
      rw this, apply binary_sum, intros t th, rw mem_image at th, rcases th with ⟨_, _, _⟩,
      rw ← th_h_h, apply h₁ _ th_h_w, 
    rw [bin_measure, sum_image], intros x _ y _, exact fin.eq_of_veq,
  end

  lemma bin_lt_of_maxdiff (A B : finset X) : (∃ (k : X), k ∉ A ∧ k ∈ B ∧ (∀ (x : X), x > k → (x ∈ A ↔ x ∈ B))) → bin_measure A < bin_measure B :=
  begin
    rintro ⟨k, notinA, inB, maxi⟩,
    have AeqB: A.filter (λ x, ¬(x ≤ k)) = B.filter (λ x, ¬(x ≤ k)),
    { ext t, rw [mem_filter, mem_filter], 
      by_cases h: (t > k); simp [h], 
      apply maxi, exact h },
    { have Alt: (A.filter (λ x, x ≤ k)).sum (λ x, pow 2 x.val) < pow 2 k.1,
        rw ← bin_measure, apply binary_sum', intro t, rw mem_filter, intro b, 
        cases lt_or_eq_of_le b.2, exact h, rw h at b, exfalso, exact notinA b.1,
      have leB: pow 2 k.1 ≤ (B.filter (λ x, x ≤ k)).sum (λ x, pow 2 x.val),
        apply @single_le_sum _ _ (B.filter (λ x, x ≤ k)) (λ (x : fin n), 2 ^ x.val) _ _ (λ x _, zero_le _) k,
        rw mem_filter, exact ⟨inB, le_refl _⟩, 
      have AltB: (A.filter (λ x, x ≤ k)).sum (λ x, pow 2 x.val) < (B.filter (λ x, x ≤ k)).sum (λ x, pow 2 x.val) := lt_of_lt_of_le Alt leB,
      have := nat.add_lt_add_right AltB (sum (filter (λ (x : fin n), ¬(x ≤ k)) A) (λ (x : fin n), 2 ^ x.val)), 
      rwa [← sum_union, filter_union_filter_neg_eq, AeqB, ← sum_union, filter_union_filter_neg_eq, ← bin_measure, ← bin_measure] at this,
      rw disjoint_iff_inter_eq_empty, apply filter_inter_filter_neg_eq,
      rw disjoint_iff_inter_eq_empty, apply filter_inter_filter_neg_eq }
  end

  lemma bin_iff (A B : finset X) : bin_measure A < bin_measure B ↔ ∃ (k : X), k ∉ A ∧ k ∈ B ∧ (∀ (x : X), x > k → (x ∈ A ↔ x ∈ B)) := 
  begin
    split, 
      intro p,
      set differ := (elems X).filter (λ x, ¬ (x ∈ A ↔ x ∈ B)),
      have h: differ ≠ ∅,
        intro q, suffices: A = B, rw this at p, exact irrefl _ p,
        ext a, by_contra z, have: differ ≠ ∅ := ne_empty_of_mem (mem_filter.2 ⟨complete _, z⟩), 
        exact this q,
      set k := max' differ h, use k,
      have z: ∀ (x : fin n), x > k → (x ∈ A ↔ x ∈ B),
        intros t th, by_contra, apply not_le_of_gt th, apply le_max', simpa [complete], 
      rw ← and.rotate, refine ⟨z, _⟩,
      have el: (k ∈ A ∧ k ∉ B) ∨ (k ∉ A ∧ k ∈ B),
        have := max'_mem differ h, rw mem_filter at this, tauto,
      apply or.resolve_left el,
      intro, apply not_lt_of_gt p (bin_lt_of_maxdiff B A ⟨k, a.2, a.1, λ x xh, (z x xh).symm⟩), 
    exact bin_lt_of_maxdiff _ _,
  end

  -- here
  lemma bin_measure_inj (A B : finset X) : bin_measure A = bin_measure B → A = B :=
  begin
    intro p, set differ := (elems X).filter (λ x, ¬ (x ∈ A ↔ x ∈ B)),
    by_cases h: (differ = ∅),
      ext a, by_contra z, have: differ ≠ ∅ := ne_empty_of_mem (mem_filter.2 ⟨complete _, z⟩), 
      exact this h,
    set k := max' differ h,
    have el: (k ∈ A ∧ k ∉ B) ∨ (k ∉ A ∧ k ∈ B),
      have := max'_mem differ h, rw mem_filter at this, tauto,
    exfalso,
    cases el,
      apply not_le_of_gt ((bin_iff B A).2 ⟨k, el.2, el.1, _⟩) (le_of_eq p), swap,
      apply not_le_of_gt ((bin_iff A B).2 ⟨k, el.1, el.2, _⟩) (ge_of_eq p), 
    all_goals { intros x xh, by_contra, apply not_le_of_gt xh, apply le_max', simp only [complete, true_and, mem_filter], tauto }, 
  end

  def c_measure (𝒜 : finset (finset X)) : ℕ := 𝒜.sum bin_measure

  lemma compression_reduces_bin_measure {U V : finset X} (hU : U ≠ ∅) (hV : V ≠ ∅) (A : finset X) (h : max' U hU < max' V hV) : compress U V A ≠ A → bin_measure (compress U V A) < bin_measure A :=
  begin
    intro a,
    rw compress at a ⊢,
    split_ifs at a ⊢,
    { rw bin_measure, rw bin_measure,
      rw ← add_lt_add_iff_right,
        have q : V ⊆ (A ∪ U) := trans h_1.2 (subset_union_left _ _),
        rw sum_sdiff q,
      rw [sum_union h_1.1.symm, add_lt_add_iff_left],
      set kV := (max' V hV).1,
      set kU := (max' U hU).1,
      have a3: 2^kV ≤ sum V (λ (x : fin n), pow 2 x.val) := @single_le_sum _ _ V (λ x, pow 2 x.val) _ _ (λ t _, zero_le _) _ (max'_mem V hV),
      have a1: sum U (λ (x : fin n), 2 ^ x.val) < 2^(kU+1), 
        { rw ← bin_measure, apply binary_sum', intros x hx, rw nat.lt_succ_iff, apply le_max' U _ _ hx },
      have a2: kU + 1 ≤ kV, exact h,
      apply lt_of_lt_of_le a1,
      transitivity (2^kV), rwa nat.pow_le_iff_le_right (le_refl 2),
      assumption },
    { exfalso, apply a, refl }
  end

  def compression_reduces_measure (U V : finset X) (hU : U ≠ ∅) (hV : V ≠ ∅) (h : max' U hU < max' V hV) (𝒜 : finset (finset X)) : compress_family U V 𝒜 ≠ 𝒜 → c_measure (compress_family U V 𝒜) < c_measure 𝒜 :=
  begin
    rw [compress_family], intro, 
    rw [c_measure, c_measure, sum_union (compress_disjoint U V)],
    conv {to_rhs, rw ← @filter_union_filter_neg_eq _ (λ A, C A ∈ 𝒜) _ _ 𝒜, rw sum_union (disjoint_iff_inter_eq_empty.2 (filter_inter_filter_neg_eq _)) },
    rw [add_comm, add_lt_add_iff_left, sum_image],
      apply sum_lt_sum,
      { intro a₁,
        rw [compress_remains, compress_motion, a₁, image_empty, empty_union] at a,
        apply a,
        conv_rhs {rw ← @filter_union_filter_neg_eq _ (λ A, C A ∈ 𝒜) _ _ 𝒜}, conv {to_lhs, rw ← union_empty (filter _ 𝒜)},
        symmetry,
        rw ← a₁ },
      intros A HA,
      apply compression_reduces_bin_measure _ _ _ h,
      intro a₁, rw [mem_filter, a₁] at HA,
      tauto,
    intros x Hx y Hy k,
    rw mem_filter at Hx Hy,
    have cx: compress U V x ≠ x, intro b, rw b at Hx, tauto,
    have cy: compress U V y ≠ y, intro b, rw b at Hy, tauto,
    rw compress at k Hx cx, split_ifs at k Hx cx,
      rw compress at k Hy cy, split_ifs at k Hy cy,
        apply inj_ish x y h_1 h_2 k,
      tauto,
    tauto,
  end

  def gamma : rel (finset X) (finset X) := (λ U V, ∃ (HU : U ≠ ∅), ∃ (HV : V ≠ ∅), disjoint U V ∧ finset.card U = finset.card V ∧ max' U HU < max' V HV)

  lemma compression_improved {r : ℕ} (U V : finset X) (𝒜 : finset (finset X)) (h : is_layer 𝒜 r) (h₁ : gamma U V) 
    (h₂ : ∀ U₁ V₁, gamma U₁ V₁ ∧ U₁.card < U.card → is_compressed U₁ V₁ 𝒜) (h₃ : ¬ is_compressed U V 𝒜): 
    c_measure (compress_family U V 𝒜) < c_measure 𝒜 ∧ (compress_family U V 𝒜).card = 𝒜.card ∧ is_layer (compress_family U V 𝒜) r ∧ (∂ compress_family U V 𝒜).card ≤ (∂𝒜).card := 
  begin
    rcases h₁ with ⟨Uh, Vh, UVd, same_size, max_lt⟩,
    refine ⟨compression_reduces_measure U V Uh Vh max_lt _ h₃, compressed_size _ _, _, _⟩,
    apply' compress_family_size _ _ _ _ UVd same_size h, 
    apply compression_reduces_shadow U V _ same_size,
    intros x Hx, refine ⟨min' V Vh, min'_mem _ _, _⟩,
    by_cases p: (2 ≤ U.card),
    { apply h₂,
      refine ⟨⟨_, _, _, _, _⟩, card_erase_lt_of_mem Hx⟩,
      { rwa [← card_pos, card_erase_of_mem Hx, nat.lt_pred_iff] },
      { rwa [← card_pos, card_erase_of_mem (min'_mem _ _), ← same_size, nat.lt_pred_iff] },
      { apply disjoint_of_subset_left (erase_subset _ _), apply disjoint_of_subset_right (erase_subset _ _), assumption },
      { rw [card_erase_of_mem (min'_mem _ _), card_erase_of_mem Hx, same_size] },
      { have: max' (erase U _) _ ≤ max' U Uh := max'_le _ _ _ (λ y Hy, le_max' _ Uh _ (mem_of_mem_erase Hy)),
        apply lt_of_le_of_lt this,
        apply lt_of_lt_of_le max_lt,
        apply le_max',
        rw mem_erase,
        refine ⟨_, max'_mem _ _⟩,
        intro,
        rw same_size at p,
        apply not_le_of_gt p,
        apply le_of_eq,
        rw card_eq_one,
        use max' V Vh,
        rw eq_singleton_iff_unique_mem,
        refine ⟨max'_mem _ _, λ t Ht, _⟩,
        apply le_antisymm,
          apply le_max' _ _ _ Ht,
        rw a, apply min'_le _ _ _ Ht } },
    rw ← card_pos at Uh,
    replace p: card U = 1 := le_antisymm (le_of_not_gt p) Uh,
    rw p at same_size,
    have: erase U x = ∅,
      rw [← card_eq_zero, card_erase_of_mem Hx, p], refl,
    have: erase V (min' V Vh) = ∅,
      rw [← card_eq_zero, card_erase_of_mem (min'_mem _ _), ← same_size], refl,
    rw [‹erase U x = ∅›, ‹erase V (min' V Vh) = ∅›],
    apply is_compressed_empty
  end

  instance thing (U V : finset X) : decidable (gamma U V) := by rw gamma; apply_instance
  instance thing2 (U V : finset X) (A : finset (finset X)) : decidable (is_compressed U V A) := by rw is_compressed; apply_instance

  lemma kruskal_katona_helper (r : ℕ) (𝒜 : finset (finset X)) (h : is_layer 𝒜 r) : 
    ∃ (ℬ : finset (finset X)), (∂ℬ).card ≤ (∂𝒜).card ∧ 𝒜.card = ℬ.card ∧ is_layer ℬ r ∧ (∀ U V, gamma U V → is_compressed U V ℬ) := 
  begin
    refine @well_founded.recursion _ _ (measure_wf c_measure) (λ (A : finset (finset X)), is_layer A r → ∃ B, (∂B).card ≤ (∂A).card ∧ A.card = B.card ∧ is_layer B r ∧ ∀ (U V : finset X), gamma U V → is_compressed U V B) _ _ h,
    intros A ih z,
    set usable: finset (finset X × finset X) := filter (λ t, gamma t.1 t.2 ∧ ¬ is_compressed t.1 t.2 A) ((powerset (elems X)).product (powerset (elems X))), 
    by_cases (usable = ∅),
      refine ⟨A, le_refl _, rfl, z, _⟩, intros U V k,
      rw eq_empty_iff_forall_not_mem at h,
      by_contra,
      apply h ⟨U,V⟩,
      simp [a, k], exact ⟨subset_univ _, subset_univ _⟩,
    rcases exists_min usable (λ t, t.1.card) ((nonempty_iff_ne_empty _).2 h) with ⟨⟨U,V⟩, uvh, t⟩, rw mem_filter at uvh,
    have h₂: ∀ U₁ V₁, gamma U₁ V₁ ∧ U₁.card < U.card → is_compressed U₁ V₁ A,
      intros U₁ V₁ h, by_contra, 
      apply not_le_of_gt h.2 (t ⟨U₁, V₁⟩ _),
      simp [h, a], exact ⟨subset_univ _, subset_univ _⟩,
    obtain ⟨small_measure, p2, layered, p1⟩ := compression_improved U V A z uvh.2.1 h₂ uvh.2.2, 
    rw [measure, inv_image] at ih, 
    rcases ih (compress_family U V A) small_measure layered with ⟨B, q1, q2, q3, q4⟩,
    exact ⟨B, trans q1 p1, trans p2.symm q2, q3, q4⟩
  end

  def binary : finset X → finset X → Prop := inv_image (<) bin_measure
  local infix ` ≺ `:50 := binary

  instance : is_trichotomous (finset X) binary := ⟨
    begin
      intros A B,
      rcases lt_trichotomy (bin_measure A) (bin_measure B) with lt|eq|gt,
      { left, exact lt },
      { right, left, exact bin_measure_inj A B eq },
      { right, right, exact gt }
    end
  ⟩

  def is_init_seg_of_colex (𝒜 : finset (finset X)) (r : ℕ) : Prop := is_layer 𝒜 r ∧ (∀ A ∈ 𝒜, ∀ B, B ≺ A ∧ B.card = r → B ∈ 𝒜)

  lemma init_seg_total (𝒜₁ 𝒜₂ : finset (finset X)) (r : ℕ) (h₁ : is_init_seg_of_colex 𝒜₁ r) (h₂ : is_init_seg_of_colex 𝒜₂ r) : 𝒜₁ ⊆ 𝒜₂ ∨ 𝒜₂ ⊆ 𝒜₁ :=
  begin
    rw ← sdiff_eq_empty_iff_subset, rw ← sdiff_eq_empty_iff_subset,
    by_contra a, rw not_or_distrib at a, simp [exists_mem_iff_ne_empty.symm, exists_mem_iff_ne_empty.symm] at a,
    rcases a with ⟨⟨A, Ah₁, Ah₂⟩, ⟨B, Bh₁, Bh₂⟩⟩,
    rcases trichotomous_of binary A B with lt | eq | gt,
      { exact Ah₂ (h₂.2 B Bh₁ A ⟨lt, h₁.1 A Ah₁⟩) },
      { rw eq at Ah₁, exact Bh₂ Ah₁ },
      { exact Bh₂ (h₁.2 A Ah₁ B ⟨gt, h₂.1 B Bh₁⟩) },
  end

  lemma init_seg_of_compressed (ℬ : finset (finset X)) (r : ℕ) (h₁ : is_layer ℬ r) (h₂ : ∀ U V, gamma U V → is_compressed U V ℬ): 
    is_init_seg_of_colex ℬ r := 
  begin
    refine ⟨h₁, _⟩,
    rintros B Bh A ⟨A_lt_B, sizeA⟩,
    by_contra a,
    set U := A \ B,
    set V := B \ A,
    have: A ≠ B, intro t, rw t at a, exact a Bh,
    have: disjoint U B ∧ V ⊆ B := ⟨sdiff_disjoint, sdiff_subset_left _ _⟩,
    have: disjoint V A ∧ U ⊆ A := ⟨sdiff_disjoint, sdiff_subset_left _ _⟩,
    have cB_eq_A: compress U V B = A,
    { rw compress, split_ifs, rw [union_sdiff_self_eq_union, union_sdiff, new_thing.1 disjoint_sdiff, union_comm], 
      apply not_sure,
      intro t, simp only [and_imp, not_and, mem_sdiff, not_not], exact (λ x y, y x) },
    have cA_eq_B: compress V U A = B,
    { rw compress, split_ifs, rw [union_sdiff_self_eq_union, union_sdiff, new_thing.1 disjoint_sdiff, union_comm], 
      apply not_sure,
      intro t, simp only [and_imp, not_and, mem_sdiff, not_not], exact (λ x y, y x) },
    have: card A = card B := trans sizeA (h₁ B Bh).symm,
    have hU: U ≠ ∅,
      { intro t, rw sdiff_eq_empty_iff_subset at t, have: A = B := eq_of_subset_of_card_le t (ge_of_eq ‹_›), rw this at a, exact a Bh },
    have hV: V ≠ ∅,
      { intro t, rw sdiff_eq_empty_iff_subset at t, have: B = A := eq_of_subset_of_card_le t (le_of_eq ‹_›), rw ← this at a, exact a Bh },
    have disj: disjoint U V,
      { exact disjoint_of_subset_left (sdiff_subset_left _ _) disjoint_sdiff },
    have smaller: max' U hU < max' V hV,
      { rcases lt_trichotomy (max' U hU) (max' V hV) with lt | eq | gt,
        { assumption },
        { exfalso, have: max' U hU ∈ U := max'_mem _ _, apply disjoint_left.1 disj this, rw eq, exact max'_mem _ _ },
        { exfalso, have z := compression_reduces_bin_measure hV hU A gt, rw cA_eq_B at z,
          apply irrefl (bin_measure B) (trans (z ‹A ≠ B›.symm) A_lt_B)
        },
      },
    have: gamma U V,
    { refine ⟨hU, hV, disj, _, smaller⟩,
      have: card (A \ B ∪ A ∩ B) = card (B \ A ∪ B ∩ A),
        rwa [sdiff_union_inter, sdiff_union_inter],
      rwa [card_disjoint_union (sdiff_inter_inter _ _), card_disjoint_union (sdiff_inter_inter _ _), inter_comm, add_right_inj] at this
    },
    have Bcomp := h₂ U V this, rw is_compressed at Bcomp,
    suffices: compress U V B ∈ compress_family U V ℬ,
      rw [Bcomp, cB_eq_A] at this, exact a this,
    rw mem_compress, left, refine ⟨_, B, Bh, rfl⟩, rwa cB_eq_A, 
  end

  lemma exists_max {α β : Type*} [decidable_linear_order α] (s : finset β) (f : β → α)
    (h : s ≠ ∅) : ∃ x ∈ s, ∀ x' ∈ s, f x' ≤ f x :=
  begin
    have : s.image f ≠ ∅,
      rwa [ne, image_eq_empty, ← ne.def],
    cases max_of_ne_empty this with y hy,
    rcases mem_image.mp (mem_of_max hy) with ⟨x, hx, rfl⟩,
    exact ⟨x, hx, λ x' hx', le_max_of_mem (mem_image_of_mem f hx') hy⟩,
  end

  def everything_up_to (A : finset X) : finset (finset X) := filter (λ (B : finset X), A.card = B.card ∧ bin_measure B ≤ bin_measure A) (powerset (elems X))

  lemma IS_iff_le_max (𝒜 : finset (finset X)) (r : ℕ) : 𝒜 ≠ ∅ ∧ is_init_seg_of_colex 𝒜 r ↔ ∃ (A : finset X), A ∈ 𝒜 ∧ A.card = r ∧ 𝒜 = everything_up_to A := 
  begin
    rw is_init_seg_of_colex, split, 
    { rintro ⟨ne, layer, IS⟩,
      rcases exists_max 𝒜 bin_measure ne with ⟨A, Ah, Ap⟩,
      refine ⟨A, Ah, layer A Ah, _⟩,
      ext B, rw [everything_up_to, mem_filter, mem_powerset], split; intro p,
        refine ⟨subset_univ _, _, _⟩,
          convert layer A Ah, apply layer B p, 
        apply Ap _ p, 
      cases lt_or_eq_of_le p.2.2 with h h,
        apply IS A Ah B ⟨h, trans p.2.1.symm (layer A Ah)⟩, 
      rwa (bin_measure_inj _ _ h), 
    },
    { rintro ⟨A, Ah, Ac, Ap⟩,
      refine ⟨ne_empty_of_mem Ah, _, _⟩,
        intros B Bh, rw [Ap, everything_up_to, mem_filter] at Bh, exact (trans Bh.2.1.symm Ac),
      intros B₁ Bh₁ B₂ Bh₂, rw [Ap, everything_up_to, mem_filter, mem_powerset], refine ⟨_, _, _⟩,
      { apply subset_univ },
      { exact (trans Ac Bh₂.2.symm) },
      { rw [binary, inv_image] at Bh₂, transitivity, apply le_of_lt Bh₂.1, rw [Ap, everything_up_to, mem_filter] at Bh₁, exact Bh₁.2.2 }
    }
  end

  lemma up_to_is_IS (A : finset X) {r : ℕ} (h₁ : A.card = r) : is_init_seg_of_colex (everything_up_to A) r := 
  and.right $ (IS_iff_le_max _ _).2 
  (by refine ⟨A, _, h₁, rfl⟩; rw [everything_up_to, mem_filter, mem_powerset]; refine ⟨subset_univ _, rfl, le_refl _⟩)

  lemma shadow_of_everything_up_to (A : finset X) (hA : A ≠ ∅) : ∂ (everything_up_to A) = everything_up_to (erase A (min' A hA)) :=
  begin
    ext B, split, 
      rw [mem_shadow', everything_up_to, everything_up_to, mem_filter, mem_powerset], rintro ⟨i, ih, p⟩,
      rw [mem_filter, card_insert_of_not_mem ih] at p, 
      have cards: card (erase A (min' A hA)) = card B,
        rw [card_erase_of_mem (min'_mem _ _), p.2.1], refl,
      refine ⟨subset_univ _, cards, _⟩, 
      cases lt_or_eq_of_le p.2.2 with h h,
      { rw bin_iff at h, rcases h with ⟨k, knotin, kin, h⟩,
        have: k ≠ i, rw mem_insert at knotin, tauto,
        cases lt_or_gt_of_ne this with h₁ h₁,
          have q: i ∈ A := (h _ h₁).1 (mem_insert_self _ _), 
          apply le_of_lt, rw bin_iff,
          refine ⟨i, ih, _, _⟩,
            apply mem_erase_of_ne_of_mem _ q,
            apply ne_of_gt, apply lt_of_le_of_lt _ h₁, 
            apply min'_le _ _ _ kin,
          intros x hx, have z := trans hx h₁, have := h _ z, simp at this ⊢, 
          have a1: ¬x = min' A hA := ne_of_gt (lt_of_le_of_lt (min'_le _ hA _ q) hx), 
          have a2: ¬x = i := ne_of_gt hx, tauto, 
        cases lt_or_eq_of_le (min'_le _ hA _ kin),
          apply le_of_lt, rw bin_iff,
          refine ⟨k, mt mem_insert_of_mem knotin, mem_erase_of_ne_of_mem (ne_of_gt h_1) kin, _⟩,
          intros x hx, have := h _ hx, simp at this ⊢,
          have a1: ¬x = min' A hA := ne_of_gt (lt_of_le_of_lt (min'_le _ hA _ kin) hx), 
          have a2: ¬x = i := ne_of_gt (trans hx h₁), tauto, 
        apply le_of_eq,
        congr, have: erase A (min' A hA) ⊆ B,
          intros t th, rw mem_erase at th, 
          have: t > k := h_1 ▸ (lt_of_le_of_ne (min'_le _ _ _ th.2) th.1.symm),
          apply mem_of_mem_insert_of_ne ((h t this).2 th.2) (ne_of_gt (trans this h₁)),
          symmetry,
          apply eq_of_subset_of_card_le this (le_of_eq cards.symm) },
      { replace h := bin_measure_inj _ _ h,
        have z: i ∈ A, rw ← h, exact mem_insert_self _ _,
        rw [bin_measure, bin_measure, ← sdiff_singleton_eq_erase], 
        rw ← add_le_add_iff_right (sum (finset.singleton i) (λ (x : fin n), 2 ^ x.val)), 
        rw [← sum_union (disjoint_singleton.2 ih), union_comm, union_singleton_eq_insert, h], 
        rw ← sum_sdiff (show finset.singleton (min' A hA) ⊆ A, by intro t; simp; intro th; rw th; exact min'_mem _ _), 
        rw [add_le_add_iff_left, sum_singleton, sum_singleton], apply nat.pow_le_pow_of_le_right zero_lt_two,
        exact min'_le _ _ _ z },
    intro p,
    rw [everything_up_to, mem_filter, mem_powerset] at p,
    simp only [mem_shadow', everything_up_to, mem_filter, mem_powerset], 
    cases eq_or_lt_of_le p.2.2,
      have: B = erase A (min' A hA) := bin_measure_inj _ _ h,
      { rw this, refine ⟨min' A hA, not_mem_erase _ _, _⟩, rw insert_erase (min'_mem _ _), simp [le_refl], apply subset_univ },
    rw bin_iff at h, rcases h with ⟨k, knotin, kin, h⟩,
    have kincomp := mem_sdiff.2 ⟨mem_univ _, knotin⟩,
    have jex: univ \ B ≠ ∅ := ne_empty_of_mem (mem_sdiff.2 ⟨mem_univ _, knotin⟩),
    set j := min' (univ \ B) jex,
    have jnotin: j ∉ B,
      have: j ∈ univ \ B := min'_mem _ _, rw mem_sdiff at this, 
      tauto,
    have cards: card A = card (insert j B),
    { rw [card_insert_of_not_mem jnotin, ← p.2.1, card_erase_of_mem (min'_mem _ _), nat.pred_eq_sub_one, nat.sub_add_cancel], 
      apply nat.pos_of_ne_zero, rw ne, rw card_eq_zero, exact hA },
    refine ⟨j, jnotin, subset_univ _, cards, _⟩,
    cases eq_or_lt_of_le (min'_le _ jex _ kincomp) with h₁ h_1, 
    { have: j = k, rw ← h₁, rw this at *, clear jnotin this j,
      suffices: insert k B = A, apply le_of_eq, rw this, symmetry, 
      apply eq_of_subset_of_card_le, 
      { intros t th, rcases lt_trichotomy t k with lt | rfl | gt,
        { apply mem_insert_of_mem, by_contra, have: t ∈ univ \ B, simpa, apply not_le_of_lt lt, rw ← h₁, apply min'_le _ _ _ this },
        { apply mem_insert_self },
        { apply mem_insert_of_mem, rw (h t gt), rw mem_erase, refine ⟨_, th⟩, apply ne_of_gt, apply lt_of_le_of_lt _ gt, apply min'_le, apply mem_of_mem_erase kin } }, 
      { apply le_of_eq cards.symm } }, 
    { apply le_of_lt, rw bin_iff, refine ⟨k, _, _, _⟩, 
      { rw [mem_insert], have: j ≠ k := ne_of_lt h_1, tauto },
      exact mem_of_mem_erase kin, intros x xh, have use := h x xh, 
      have: x ≠ min' A hA := ne_of_gt (lt_of_le_of_lt (min'_le _ _ _ (mem_of_mem_erase kin)) xh),
      have: x ≠ j := ne_of_gt (trans xh h_1),
      simp at use ⊢, tauto
    }
  end

  -- kill the condition
  lemma shadow_of_IS {𝒜 : finset (finset X)} (r : ℕ) (h₁ : is_init_seg_of_colex 𝒜 r) : is_init_seg_of_colex (∂𝒜) (r - 1) :=
  begin
    cases nat.eq_zero_or_pos r with h0 hr,
      have: 𝒜 ⊆ finset.singleton ∅,
      intros A hA, rw mem_singleton, rw ← card_eq_zero, rw ← h0, apply h₁.1 A hA, rw h0, simp, 
      have := bind_sub_bind_of_sub_left this, rw [← shadow, singleton_bind, all_removals, image_empty, subset_empty] at this, 
      rw this, split, rw [is_layer, forall_mem_empty_iff], trivial, rw forall_mem_empty_iff, trivial, 
    by_cases h₂: 𝒜 = ∅,
      rw h₂, rw shadow, rw bind_empty, rw is_init_seg_of_colex, rw is_layer, rw forall_mem_empty_iff, rw forall_mem_empty_iff, simp,
    replace h₁ := and.intro h₂ h₁,
    rw IS_iff_le_max at h₁,
    rcases h₁ with ⟨B, _, Bcard, rfl⟩, 
    rw shadow_of_everything_up_to, 
    apply up_to_is_IS,
    rw card_erase_of_mem, rw Bcard, refl,
    apply min'_mem, 
    rw ← card_pos, rw Bcard, exact hr
  end
end
end UV

lemma killing {α : Type*} [decidable_eq α] (A : finset α) (i k : ℕ) (h₁ : card A = i + k) : ∃ (B : finset α), B ⊆ A ∧ card B = i :=
begin
  revert A, induction k with k ih,
  simp, intros A hA, use A, exact ⟨subset.refl _, hA⟩,
  intros A hA, have: ∃ i, i ∈ A, rw exists_mem_iff_ne_empty, rw ← ne, rw ← card_pos, rw hA, rw nat.add_succ, apply nat.succ_pos,
  rcases this with ⟨a, ha⟩,
  set A' := erase A a,
  have z: card A' = i + k,
    rw card_erase_of_mem ha, rw hA, rw nat.add_succ, rw nat.pred_succ, 
  rcases ih A' z with ⟨B, hB, cardB⟩,
  refine ⟨B, _, cardB⟩, apply trans hB _, apply erase_subset
end

lemma killing2 {α : Type*} [decidable_eq α] (A B : finset α) (i k : ℕ) (h₁ : card A = i + k + card B) (h₂ : B ⊆ A) : ∃ (C : finset α), B ⊆ C ∧ C ⊆ A ∧ card C = i + card B :=
begin
  revert A, induction k with k ih,
  simp, intros A cards BsubA, refine ⟨A, BsubA, subset.refl _, cards⟩,
  intros A cards BsubA, have: ∃ i, i ∈ A \ B, rw exists_mem_iff_ne_empty, rw [← ne, ← card_pos, card_sdiff BsubA, cards, nat.add_sub_cancel, nat.add_succ], apply nat.succ_pos,
  rcases this with ⟨a, ha⟩,
  set A' := erase A a,
  have z: card A' = i + k + card B,
    rw card_erase_of_mem, rw cards, rw nat.add_succ, rw nat.succ_add, rw nat.pred_succ, rw mem_sdiff at ha, exact ha.1,
  rcases ih A' z _ with ⟨B', hB', B'subA', cards⟩,
  refine ⟨B', hB', trans B'subA' (erase_subset _ _), cards⟩, 
  intros t th, apply mem_erase_of_ne_of_mem, intro, rw mem_sdiff at ha, rw a_1 at th, exact ha.2 th, exact BsubA th,
end

lemma killing2_sets {α : Type*} [decidable_eq α] (A B : finset α) (i : ℕ) (h₁ : card A ≥ i + card B) (h₂ : B ⊆ A) : ∃ (C : finset α), B ⊆ C ∧ C ⊆ A ∧ card C = i + card B :=
begin
  rcases nat.le.dest h₁,
  rw add_right_comm at h, 
  apply killing2 A B i w h.symm h₂,
end

lemma kill_sets {α : Type*} [decidable_eq α] (A : finset α) (i : ℕ) (h₁ : card A ≥ i) : ∃ (B : finset α), B ⊆ A ∧ card B = i := 
begin
  rcases nat.le.dest h₁,
  apply killing A i w h.symm, 
end

section KK
  theorem kruskal_katona (r : ℕ) (𝒜 𝒞 : finset (finset X)) : 
    is_layer 𝒜 r ∧ is_layer 𝒞 r ∧ 𝒜.card = 𝒞.card ∧ UV.is_init_seg_of_colex 𝒞 r 
  → (∂𝒞).card ≤ (∂𝒜).card :=
  begin
    rintros ⟨layerA, layerC, h₃, h₄⟩,
    rcases UV.kruskal_katona_helper r 𝒜 layerA with ⟨ℬ, _, t, layerB, fully_comp⟩,
    have: UV.is_init_seg_of_colex ℬ r := UV.init_seg_of_compressed ℬ r layerB fully_comp,
    suffices: 𝒞 = ℬ,
      rwa this at *,
    have z: card ℬ = card 𝒞 := t.symm.trans h₃,
    cases UV.init_seg_total ℬ 𝒞 r this h₄ with BC CB,
      symmetry, apply eq_of_subset_of_card_le BC (ge_of_eq z),
    apply eq_of_subset_of_card_le CB (le_of_eq z)
  end

  theorem strengthened (r : ℕ) (𝒜 𝒞 : finset (finset X)) : 
    is_layer 𝒜 r ∧ is_layer 𝒞 r ∧ 𝒞.card ≤ 𝒜.card ∧ UV.is_init_seg_of_colex 𝒞 r 
  → (∂𝒞).card ≤ (∂𝒜).card :=
  begin
    rintros ⟨Ar, Cr, cards, colex⟩,
    rcases kill_sets 𝒜 𝒞.card cards with ⟨𝒜', prop, size⟩,
    have := kruskal_katona r 𝒜' 𝒞 ⟨λ A hA, Ar _ (prop hA), Cr, size, colex⟩,
    transitivity, exact this, apply card_le_of_subset, rw [shadow, shadow], apply bind_sub_bind_of_sub_left prop
  end

  theorem lovasz_form {r k : ℕ} {𝒜 : finset (finset X)} (hr1 : r ≥ 1) (hkn : k ≤ n) (hrk : r ≤ k) (h₁ : is_layer 𝒜 r) (h₂ : 𝒜.card ≥ nat.choose k r) : 
    (∂𝒜).card ≥ nat.choose k (r-1) :=
  begin
    set range'k : finset X := attach_fin (range k) (λ m, by rw mem_range; apply forall_lt_iff_le.2 hkn),
    set 𝒞 : finset (finset X) := powerset_len r (range'k),
    have Ccard: 𝒞.card = nat.choose k r,
      rw [card_powerset_len, card_attach_fin, card_range], 
    have: is_layer 𝒞 r, intros A HA, rw mem_powerset_len at HA, exact HA.2,
    suffices this: (∂𝒞).card = nat.choose k (r-1),
    { rw ← this, apply strengthened r _ _ ⟨h₁, ‹is_layer 𝒞 r›, _, _⟩, 
      rwa Ccard, 
      refine ⟨‹_›, _⟩, rintros A HA B ⟨HB₁, HB₂⟩, 
      rw mem_powerset_len, refine ⟨_, ‹_›⟩, 
      intros t th, rw mem_attach_fin, rw mem_range, 
      by_contra, simp at a, 
      rw [UV.binary, inv_image] at HB₁,
      apply not_le_of_gt HB₁, 
      transitivity 2^k,
        apply le_of_lt, 
        apply UV.binary_sum',
        intros x hx, rw mem_powerset_len at HA, exact mem_range.1 ((mem_attach_fin _).1 (HA.1 hx)), 
      have: (λ (x : X), 2^x.val) t ≤ _ := single_le_sum _ th, 
        transitivity, apply nat.pow_le_pow_of_le_right zero_lt_two a, rwa UV.bin_measure,
      intros _ _, apply zero_le },
    suffices: ∂𝒞 = powerset_len (r-1) (range'k),
      rw [this, card_powerset_len, card_attach_fin, card_range], 
    ext A, rw mem_powerset_len, split,
      rw mem_shadow, rintro ⟨B, Bh, i, ih, BA⟩,
      refine ⟨_, _⟩; rw ← BA; rw mem_powerset_len at Bh,
        intro j, rw mem_erase, intro a,
        exact Bh.1 a.2, 
      rw [card_erase_of_mem ih, Bh.2], refl,
    rintro ⟨_, _⟩,
    rw mem_shadow', 
    suffices: ∃ j, j ∈ range'k \ A,
      rcases this with ⟨j,jp⟩, rw mem_sdiff at jp,
      use j, use jp.2, rw mem_powerset_len, split, 
        intros t th, rw mem_insert at th, cases th, 
          rw th, exact jp.1,
        exact a_left th,
      rw [card_insert_of_not_mem jp.2, a_right, nat.sub_add_cancel hr1],
    apply exists_mem_of_ne_empty,
    rw ← card_pos,
    rw card_sdiff a_left, rw card_attach_fin, apply nat.lt_sub_left_of_add_lt, 
    rw [card_range, a_right, add_zero], rw nat.sub_lt_right_iff_lt_add hr1, 
    apply nat.lt_succ_of_le hrk, 
  end

  theorem iterated (r k : ℕ) (𝒜 𝒞 : finset (finset X)) : 
    is_layer 𝒜 r ∧ is_layer 𝒞 r ∧ 𝒞.card ≤ 𝒜.card ∧ UV.is_init_seg_of_colex 𝒞 r 
  → (nat.iterate shadow k 𝒞).card ≤ (nat.iterate shadow k 𝒜).card :=
  begin
    revert r 𝒜 𝒞, induction k,
      intros, simp, exact a.2.2.1,
    rintros r A C ⟨z₁, z₂, z₃, z₄⟩, simp, apply k_ih (r-1), refine ⟨shadow_layer z₁, shadow_layer z₂, _, _⟩,
    apply strengthened r _ _ ⟨z₁, z₂, z₃, z₄⟩, 
    apply UV.shadow_of_IS _ z₄
  end

  theorem lovasz_form_iterate {r k i : ℕ} {𝒜 : finset (finset X)} (hi1 : i ≥ 1) (hir : i < r) (hkn : k ≤ n) (hrk : r ≤ k) (h₁ : is_layer 𝒜 r) (h₂ : 𝒜.card ≥ nat.choose k r) : 
    (nat.iterate shadow i 𝒜).card ≥ nat.choose k (r-i) :=
  begin
    set range'k : finset X := attach_fin (range k) (λ m, by rw mem_range; apply forall_lt_iff_le.2 hkn),
    set 𝒞 : finset (finset X) := powerset_len r (range'k),
    have Ccard: 𝒞.card = nat.choose k r,
      rw [card_powerset_len, card_attach_fin, card_range], 
    have: is_layer 𝒞 r, intros A HA, rw mem_powerset_len at HA, exact HA.2,
    suffices this: (nat.iterate shadow i 𝒞).card = nat.choose k (r-i),
    { rw ← this, apply iterated r _ _ _ ⟨h₁, ‹is_layer 𝒞 r›, _, _⟩, 
      rwa Ccard, 
      refine ⟨‹_›, _⟩, rintros A HA B ⟨HB₁, HB₂⟩, 
      rw mem_powerset_len, refine ⟨_, ‹_›⟩, 
      intros t th, rw mem_attach_fin, rw mem_range, 
      by_contra, simp at a, 
      rw [UV.binary, inv_image] at HB₁,
      apply not_le_of_gt HB₁, 
      transitivity 2^k,
        apply le_of_lt, 
        apply UV.binary_sum',
        intros x hx, rw mem_powerset_len at HA, exact mem_range.1 ((mem_attach_fin _).1 (HA.1 hx)), 
      have: (λ (x : X), 2^x.val) t ≤ _ := single_le_sum _ th, 
        transitivity, apply nat.pow_le_pow_of_le_right zero_lt_two a, rwa UV.bin_measure,
      intros _ _, apply zero_le },
    suffices: nat.iterate shadow i 𝒞 = powerset_len (r-i) range'k, -- sub_iff_shadow_iter
      rw [this, card_powerset_len, card_attach_fin, card_range], 
    ext B, rw mem_powerset_len, rw sub_iff_shadow_iter, 
    split, 
      rintro ⟨A, Ah, BsubA, card_sdiff_i⟩,
      rw mem_powerset_len at Ah, refine ⟨trans BsubA Ah.1, _⟩, symmetry,
      rw nat.sub_eq_iff_eq_add, 
      rw ← Ah.2, rw ← card_sdiff_i, rw ← card_disjoint_union, rw union_sdiff_of_subset BsubA,  apply disjoint_sdiff,
      apply le_of_lt hir,
    rintro ⟨_, _⟩,
    rcases killing2_sets _ _ i _ a_left with ⟨C, BsubC, Csubrange, cards⟩, 
    rw [a_right, ← nat.add_sub_assoc (le_of_lt hir), nat.add_sub_cancel_left] at cards, 
    refine ⟨C, _, BsubC, _⟩,
    rw mem_powerset_len, exact ⟨Csubrange, cards⟩, 
    rw card_sdiff BsubC, rw cards, rw a_right, rw nat.sub_sub_self (le_of_lt hir), 
    rw a_right, rw card_attach_fin, rw card_range, rw ← nat.add_sub_assoc (le_of_lt hir), rwa nat.add_sub_cancel_left, 
  end

end KK

def intersecting (𝒜 : finset (finset X)) : Prop := ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, ¬ disjoint A B

theorem intersecting_all (h : intersecting 𝒜) : 𝒜.card ≤ 2^(n-1) :=
begin
  cases lt_or_le n 1 with b hn,
    have: n = 0, apply nat.eq_zero_of_le_zero (nat.pred_le_pred b),
    suffices: finset.card 𝒜 = 0,
      rw this, apply nat.zero_le,
    rw [card_eq_zero, eq_empty_iff_forall_not_mem],
    intros A HA, apply h A HA A HA, rw disjoint_self_iff_empty, 
    apply eq_empty_of_forall_not_mem, 
    intro x, rw this at x, exact (fin.elim0 ‹_›),
  set f : finset X → finset (finset X) := λ A, insert (univ \ A) (finset.singleton A),
  have disjs: ∀ x ∈ 𝒜, ∀ y ∈ 𝒜, x ≠ y → disjoint (f x) (f y),
    intros A hA B hB k,
    simp [not_or_distrib, and_assoc], refine ⟨_, _, _, _⟩,
      { intro z, apply k, ext a, simp [ext] at z, replace z := z a, tauto },
      intro a, rw ← a at hA, apply h _ hB _ hA disjoint_sdiff, 
      intro a, rw ← a at hB, apply h _ hB _ hA sdiff_disjoint, 
      exact k.symm, 
  have: 𝒜.bind f ⊆ powerset univ,
    intros A hA, rw mem_powerset, apply subset_univ,
  have q := card_le_of_subset this, rw [card_powerset, card_univ, card_fin] at q, 
  rw card_bind disjs at q, dsimp at q,
  have: (λ (u : finset X), card (f u)) =  (λ _, 2),
    funext, rw card_insert_of_not_mem, rw card_singleton, rw mem_singleton, 
    intro, simp [ext] at a, apply a, exact ⟨0, hn⟩,
  rw this at q, rw sum_const at q, rw nat.smul_eq_mul at q, 
  rw ← nat.le_div_iff_mul_le' zero_lt_two at q, 
  conv_rhs at q {rw ← nat.sub_add_cancel hn},
  rw nat.pow_add at q, simp at q, assumption,
end

@[reducible]
def extremal_intersecting (hn : n ≥ 1) : finset (finset X) :=
(powerset univ).filter (λ A, (⟨0, hn⟩: X) ∈ A)

lemma thing {hn : n ≥ 1} : intersecting (extremal_intersecting hn) :=
by intros A HA B HB k; rw [mem_filter] at HA HB; exact disjoint_left.1 k HA.2 HB.2

#print thing
