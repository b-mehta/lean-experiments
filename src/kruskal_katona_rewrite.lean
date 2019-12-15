import algebra.geom_sum
import data.finset
import data.fintype
import data.list
import tactic

open fintype
open finset

-- variables {X : Type*}
-- variables [fintype X] [decidable_eq X]
variables {n : ℕ}
local notation `X` := fin n
variables {𝒜 : finset (finset X)}

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

section shadow
  def all_removals (A : finset X) : finset (finset X) :=
  A.attach.map ⟨λ i, erase A i.1, 
  begin
    rintro ⟨x1, x1p⟩ ⟨x2, x2p⟩ _,
    congr, dsimp at a,
    have: x1 ∉ erase A x1 := not_mem_erase _ _,
    finish [a, mem_erase],
  end
  ⟩

  lemma all_removals_size {A : finset X} {r : ℕ} (h : A.card = r) : is_layer (all_removals A) (r-1) := 
  begin
    intros _ H,
    rw [all_removals, mem_map] at H,
    rcases H with ⟨⟨_, p⟩, _, k⟩,
    dsimp at k,
    rw [← k, card_erase_of_mem p, ‹A.card = r›],
    refl
  end

  def mem_all_removals {A : finset X} {B : finset X} : B ∈ all_removals A ↔ ∃ i ∈ A, erase A i = B :=
  by simp [all_removals, mem_map]

  lemma card_all_removals {A : finset X} {r : ℕ} {H : card A = r} : (all_removals A).card = r :=
  by rw [all_removals, card_map, card_attach, H]

  def shadow (𝒜 : finset (finset X)) : finset (finset X) := 
  𝒜.bind all_removals

  reserve prefix `∂`:90
  notation ∂𝒜 := shadow 𝒜

  def mem_shadow (B : finset X) : B ∈ shadow 𝒜 ↔ ∃ A ∈ 𝒜, ∃ i ∈ A, erase A i = B := 
  by simp [shadow, all_removals]

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
    refine all_removals_size (a _ ‹_›) _ ‹A ∈ all_removals B›,
  end

  def sub_of_shadow {B : finset X} : B ∈ ∂𝒜 → ∃ A ∈ 𝒜, B ⊆ A :=
  begin
    intro k,
    rw mem_shadow at k,
    rcases k with ⟨A, H, _, _, k⟩,
    use A, use H,
    rw ← k,
    apply erase_subset
  end
end shadow

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
  𝒜.bind $ λ A, (all_removals A).map ⟨λ x, (A,x), λ _ _, by simp⟩

  lemma card_the_pairs {r : ℕ} (𝒜 : finset (finset X)) : is_layer 𝒜 r → (the_pairs 𝒜).card = 𝒜.card * r :=
  begin
    intro,
    rw [the_pairs, card_bind],
    transitivity,
        apply (sum_congr rfl _),
          intro, exact r,
        intros,
        rw [card_map, card_all_removals],
        refine (a _ H),
      rw [← nat.smul_eq_mul, ← sum_const],
    intros,
    rw disjoint_iff_ne, finish
  end

  def from_below (𝒜 : finset (finset X)) : finset (finset X × finset X) :=
  (∂𝒜).bind (λ B, (univ \ B).attach.map ⟨λ x, (insert x.1 B, B), 
  begin
    rintros ⟨x1, x1h⟩ ⟨x2, x2h⟩ h,
    injection h, congr,
    have q := mem_insert_self x1 B,
    rw [h_1, mem_insert] at q,
    rw mem_sdiff at x1h,
    tauto
  end
  ⟩)

  lemma mem_the_pairs (A B : finset X) : (A,B) ∈ the_pairs 𝒜 ↔ A ∈ 𝒜 ∧ B ∈ all_removals A :=
  begin
    rw [the_pairs, mem_bind],
    split; intro h,
      rcases h with ⟨a, Ha, h⟩,
      rw mem_map at h,
      rcases h with ⟨b, Hb, h⟩,
      injection h with Ah Bh,
      rw [Ah, Bh] at *,
      exact ⟨Ha, Hb⟩,
    refine ⟨A, h.1, _⟩,
    rw mem_map,
    tauto
  end

  lemma mem_from_below (A B : finset X) : A ∈ 𝒜 ∧ (∃ (i ∉ B), insert i B = A) → (A,B) ∈ from_below 𝒜 :=
  begin
    intro,
    rw [from_below, mem_bind],
    rcases a with ⟨Ah, i, ih, a⟩,
    refine ⟨B, _, _⟩,
      rw mem_shadow',
      refine ⟨i, ih, a.symm ▸ Ah⟩,
    rw mem_map,
    refine ⟨⟨i, mem_sdiff.2 ⟨complete _, ih⟩⟩, mem_attach _ _, by simpa⟩
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
    transitivity,
      apply card_bind_le,
    apply le_of_eq,
    rw [← nat.smul_eq_mul, ← sum_const],
    apply sum_congr rfl,
    intros, 
    rw [card_map, card_attach, card_sdiff (subset_univ _), card_univ, card_fin, shadow_layer a _ H]
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

  lemma layered_slice (𝒜 : finset (finset X)) (r : ℕ) : is_layer (𝒜#r) r :=
  begin
    intros A,
    rw mem_slice,
    tauto
  end

  lemma ne_of_diff_slice {r₁ r₂ : ℕ} {A₁ A₂ : finset X} (h₁ : A₁ ∈ 𝒜#r₁) (h₂ : A₂ ∈ 𝒜#r₂) : r₁ ≠ r₂ → A₁ ≠ A₂ :=
  begin
    intros A' r,
    rw r at *,
    rw mem_slice at h₁ h₂,
    rw h₁.2 at h₂, tauto
  end
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

  def decompose (𝒜 : finset (finset X)) (r : ℕ) : finset (finset X) :=
  decompose' 𝒜 (n-r)

  def decompose_layer (𝒜 : finset (finset X)) (r : ℕ) (hr : r ≤ n) : is_layer (decompose 𝒜 r) r :=
  begin
    rw decompose,
    have := decompose'_layer 𝒜 (n-r),
    rwa nat.sub_sub_self hr at this
  end

  lemma sum_flip {α : Type*} [add_comm_monoid α] {n : ℕ} (f : ℕ → α) : sum (range (n+1)) (λ r, f (n - r)) = sum (range (n+1)) (λ r, f r) :=
  begin
    induction n with n ih,
      rw [sum_range_one, sum_range_one],
    rw sum_range_succ',
    rw sum_range_succ _ (nat.succ n),
    simp [ih]
  end

  lemma card_decompose_other (H : antichain 𝒜) : 
    (range (n+1)).sum (λ r, ((𝒜#r).card : ℚ) / nat.choose n r) ≤ (decompose 𝒜 0).card / nat.choose n 0 :=
  begin
    rw [decompose, nat.sub_zero, ← nat.sub_self],
    by calc 
      (range (n + 1)).sum (λ r, ((𝒜#r).card : ℚ) / nat.choose n r) 
            = (range (n + 1)).sum (λ r, ((𝒜#(n-r)).card : ℚ) / nat.choose n (n-r)) 
                                              : by rw sum_flip (λ r, ((𝒜#r).card : ℚ) / nat.choose n r)
        ... ≤ ((decompose' 𝒜 n).card : ℚ) / nat.choose n (n-n) : card_decompose'_other (le_refl _) H
  end

  lemma lubell_yamamoto_meshalkin (H : antichain 𝒜) : (range (n+1)).sum (λ r, ((𝒜#r).card : ℚ) / nat.choose n r) ≤ 1 :=
  begin
    transitivity,
      apply card_decompose_other H,
    rw div_le_iff; norm_cast,
      rw decompose,
      simpa using size_in_layer (decompose'_layer 𝒜 n),
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

lemma sdiff_inter_inter {α : Type*} [decidable_eq α] (A B : finset α) : (A \ B) ∩ (A ∩ B) = ∅ :=
by simp only [ext, mem_inter, mem_sdiff, not_mem_empty]; tauto

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
      any_goals { rw disjoint_iff_inter_eq_empty,
                  apply sdiff_inter_inter },

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
lemma union_singleton_eq_insert {α : Type*} [decidable_eq α] (a : α) (s : finset α) : finset.singleton a ∪ s = insert a s := begin ext, rw [mem_insert, mem_union, mem_singleton] end
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
      any_goals { rw disjoint_iff_inter_eq_empty,
                  apply sdiff_inter_inter },
    
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

  def binary (A : finset X) : ℕ := A.sum (λ x, pow 2 x.val)

  def c_measure (𝒜 : finset (finset X)) : ℕ := 𝒜.sum binary

  def compression_reduces_binary (U V : finset X) (hU : U ≠ ∅) (hV : V ≠ ∅) (A : finset X) (h : max' U hU < max' V hV) : compress U V A ≠ A → binary (compress U V A) < binary A :=
  begin
    intro a,
    rw compress at a ⊢,
    split_ifs at a ⊢,
    { rw binary,
      rw binary,
      rw ← add_lt_add_iff_right,
        have q : V ⊆ (A ∪ U) := trans h_1.2 (subset_union_left _ _),
        rw sum_sdiff q,
      rw sum_union h_1.1.symm,
      rw add_lt_add_iff_left,
      set kV := (max' V hV).1,
      set kU := (max' U hU).1,
      have: 2^kV ≤ sum V (λ (x : fin n), pow 2 x.val) := @single_le_sum _ _ V (λ x, pow 2 x.val) _ _ (λ t _, zero_le _) _ (max'_mem V hV),
      have: sum U (λ (x : fin n), 2 ^ x.val) < 2^(kU+1), 
        {
          have r := geom_sum_mul_add 1 (kU + 1),
          have p: sum (range (kU + 1)) (pow 2) + 1 = pow 2 (kU + 1),
            simp only [nat.pow_eq_pow, geom_series, mul_one] at r, assumption,
          set f: fin n ↪ ℕ := ⟨λ x, x.val, by rintros ⟨x1, _⟩ ⟨x2, _⟩ k; congr; exact k⟩,
          have s := sum_map U f (pow 2),
          dsimp at s, rw [← s, ← p, nat.lt_succ_iff], apply sum_le_sum_of_subset, 
          intro x, rw mem_map, rintros ⟨y, _, hy⟩,
          rw [mem_range, ← hy, nat.lt_succ_iff], apply le_max' U hU y ‹y ∈ U›
        },
      have: kU + 1 ≤ kV, 
        exact h,
      apply lt_of_lt_of_le,
          assumption,
      transitivity (2^kV),
        rwa nat.pow_le_iff_le_right (le_refl 2),
      assumption },
    { exfalso, apply a, refl }
  end

  def compression_reduces_measure (U V : finset X) (hU : U ≠ ∅) (hV : V ≠ ∅) (h : max' U hU < max' V hV) (𝒜 : finset (finset X)) : compress_family U V 𝒜 ≠ 𝒜 → c_measure (compress_family U V 𝒜) < c_measure 𝒜 :=
  begin
    rw [compress_family], 
    intro, 
    rw c_measure, rw c_measure,
    rw sum_union (compress_disjoint U V),
    conv {to_rhs, rw ← @filter_union_filter_neg_eq _ (λ A, C A ∈ 𝒜) _ _ 𝒜, rw sum_union (disjoint_iff_inter_eq_empty.2 (filter_inter_filter_neg_eq _)) },
    rw [add_comm, add_lt_add_iff_left],
    rw sum_image,
      apply sum_lt_sum,
        intro,
        rw [compress_motion, compress_remains, a_1, image_empty, empty_union] at a,
        apply a,
        conv {to_rhs, rw ← @filter_union_filter_neg_eq _ (λ A, C A ∈ 𝒜) _ _ 𝒜}, conv {to_lhs, rw ← union_empty (filter _ 𝒜)},
        symmetry,
        rw ← a_1,
      intros A HA,
      apply compression_reduces_binary, exact h,
      rw mem_filter at HA,
      intro, rw a_1 at HA,
      tauto,
    intros x Hx y Hy k,
    rw mem_filter at Hx Hy,
    have cx: compress U V x ≠ x,
      intro b, rw b at Hx, tauto,
    have cy: compress U V y ≠ y,
      intro b, rw b at Hy, tauto,
    rw compress at k Hx cx,
    split_ifs at k Hx cx,
      rw compress at k Hy cy,
      split_ifs at k Hy cy,
        apply inj_ish x y h_1 h_2 k,
      tauto,
    tauto,
  end

  def gamma : rel (finset X) (finset X) := (λ U V, ∃ (HU : U ≠ ∅), ∃ (HV : V ≠ ∅), disjoint U V ∧ finset.card U = finset.card V ∧ max' U HU < max' V HV)

  lemma compression_improved (U V : finset X) (𝒜 : finset (finset X)) (h₁ : gamma U V) 
    (h₂ : ∀ U₁ V₁, gamma U₁ V₁ ∧ U₁.card < U.card → is_compressed U₁ V₁ 𝒜) (h₃ : ¬ is_compressed U V 𝒜): 
    c_measure (compress_family U V 𝒜) < c_measure 𝒜 ∧ (compress_family U V 𝒜).card = 𝒜.card ∧ (∂ compress_family U V 𝒜).card ≤ (∂𝒜).card := 
  begin
    rcases h₁ with ⟨Uh, Vh, UVd, same_size, max_lt⟩,
    refine ⟨compression_reduces_measure U V Uh Vh max_lt _ h₃, compressed_size _ _, _⟩,
    apply compression_reduces_shadow U V _ same_size,
    intros x Hx, refine ⟨min' V Vh, min'_mem _ _, _⟩,
    by_cases (2 ≤ U.card),
    { apply h₂,
      refine ⟨⟨_, _, _, _, _⟩, card_erase_lt_of_mem Hx⟩,
      { rwa [← card_pos, card_erase_of_mem Hx, nat.lt_pred_iff] },
      { rwa [← card_pos, card_erase_of_mem (min'_mem _ _), ← same_size, nat.lt_pred_iff] },
      { apply disjoint_of_subset_left (erase_subset _ _), apply disjoint_of_subset_right (erase_subset _ _), assumption },
      { rw [card_erase_of_mem (min'_mem _ _), card_erase_of_mem Hx, same_size] },
      { apply @lt_of_le_of_lt _ _ _ (max' U Uh),
          apply max'_le,
          intros y Hy,
          apply le_max',
          apply mem_of_mem_erase Hy,
        apply lt_of_lt_of_le max_lt,
        apply le_max',
        rw mem_erase,
        refine ⟨_, max'_mem _ _⟩,
        intro,
        rw same_size at h,
        apply not_le_of_gt h,
        apply le_of_eq,
        rw card_eq_one,
        use max' V Vh,
        rw eq_singleton_iff_unique_mem,
        refine ⟨max'_mem _ _, λ t Ht, _⟩,
        apply le_antisymm,
          apply le_max' _ _ _ Ht,
        rw a, apply min'_le _ _ _ Ht
      } 
    },
    rw ← card_pos at Uh,
    replace h: card U = 1 := le_antisymm (le_of_not_gt h) Uh,
    rw h at same_size,
    have: erase U x = ∅,
      rw [← card_eq_zero, card_erase_of_mem Hx, h], refl,
    have: erase V (min' V Vh) = ∅,
      rw [← card_eq_zero, card_erase_of_mem (min'_mem _ _), ← same_size], refl,
    rw [‹erase U x = ∅›, ‹erase V (min' V Vh) = ∅›],
    apply is_compressed_empty
  end
end
end UV