import data.finset
import data.fintype
import data.list
import tactic.omega
import tactic.linarith

open fintype
open finset

variables {X : Type*}
variables [fintype X] [decidable_eq X]
variables {r : ℕ}

lemma mem_powerset_len_iff_card : ∀ (x : finset X), x ∈ powerset_len r (elems X) ↔ card x = r :=
by intro x; rw mem_powerset_len; exact and_iff_right (subset_univ _)

def example1 : finset (finset (fin 5)) :=
{ {0,1,2}, {0,1,3}, {0,2,3}, {0,2,4} } 

section layers
  def is_layer (𝒜 : finset (finset X)) (r : ℕ) : Prop := ∀ A ∈ 𝒜, finset.card A = r

  lemma union_layer {A B : finset (finset X)} {r : ℕ} : is_layer A r ∧ is_layer B r ↔ is_layer (A ∪ B) r :=
  begin
    split; intros p, 
      rw is_layer,
      intros,
      rw finset.mem_union at H,
      cases H,
        exact (p.1 _ H),
        exact (p.2 _ H),
    split,
    all_goals {rw is_layer, intros, apply p, rw finset.mem_union, tauto}, 
  end

  lemma powerset_len_iff_is_layer {𝒜 : finset (finset X)} {r : ℕ} : is_layer 𝒜 r ↔ 𝒜 ⊆ finset.powerset_len r (elems X) :=
  begin
    split; intros p A h,
      rw mem_powerset_len_iff_card,
      exact (p _ h),
    rw ← mem_powerset_len_iff_card, 
    exact p h
  end

  lemma size_in_layer {𝒜 : finset (finset X)} {r : ℕ} (h : is_layer 𝒜 r) : finset.card 𝒜 ≤ nat.choose (card X) r :=
  begin
    rw [fintype.card, ← finset.card_powerset_len],
    apply finset.card_le_of_subset,
    rwa [finset.univ, ← powerset_len_iff_is_layer]
  end
end layers

def all_removals (A : finset X) : finset (finset X) :=
A.attach.map ⟨λ i, erase A i.1, 
begin
  rintro ⟨x1, x1p⟩ ⟨x2, x2p⟩ _,
  congr, dsimp at a,
  have: x1 ∉ finset.erase A x1 := finset.not_mem_erase _ _,
  finish [a, finset.mem_erase],
end
⟩

lemma all_removals_size (A : finset X) (h : A.card = r) : is_layer (all_removals A) (r-1) := 
begin
  intros _ _,
  rw [all_removals, finset.mem_map] at H,
  rcases H with ⟨⟨_, p⟩, _, k⟩,
  dsimp at k,
  rw [← k, finset.card_erase_of_mem p, h],
  refl
end

def mem_all_removals {A : finset X} {B : finset X} : B ∈ all_removals A ↔ ∃ i ∈ A, erase A i = B :=
by simp [all_removals]

lemma card_all_removals {A : finset X} {H : finset.card A = r} : (all_removals A).card = r :=
by rw [all_removals, card_map, card_attach, H]

def shadow (𝒜 : finset (finset X)) : finset (finset X) := 
𝒜.bind all_removals

reserve prefix `∂`:90
notation ∂𝒜 := shadow 𝒜

def mem_shadow {𝒜 : finset (finset X)} (B : finset X) : B ∈ shadow 𝒜 ↔ ∃ A ∈ 𝒜, ∃ i ∈ A, erase A i = B := 
by simp [shadow, all_removals]

def mem_shadow' {𝒜 : finset (finset X)} {B : finset X} : B ∈ shadow 𝒜 ↔ ∃ j ∉ B, insert j B ∈ 𝒜 :=
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

lemma shadow_layer (𝒜 : finset (finset X)) : is_layer 𝒜 r → is_layer (∂𝒜) (r-1) :=
begin
  intros a _ H,
  simp [shadow] at H,
  rcases H with ⟨A, ⟨_, _⟩⟩,
  apply all_removals_size A (a _ ‹_›),
  tauto
end

def sub_of_shadow {𝒜 : finset (finset X)} (B : finset X) : B ∈ shadow 𝒜 → ∃ A ∈ 𝒜, B ⊆ A :=
begin
  intro k,
  rw mem_shadow at k,
  rcases k with ⟨A, H, _, _, k⟩,
  use A, use H,
  rw ← k,
  apply finset.erase_subset
end

lemma multiply_out {A B n r : ℕ} (hr1 : 1 ≤ r) (hr2 : r ≤ n)
  (h : A * r ≤ B * (n - r + 1)) :
  (A : ℚ) / (nat.choose n r) ≤ B / nat.choose n (r-1) :=
begin
  rw div_le_div_iff; norm_cast,
  apply le_of_mul_le_mul_right _,
    exact hr1,
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

lemma card_the_pairs (𝒜 : finset (finset X)) : is_layer 𝒜 r → (the_pairs 𝒜).card = 𝒜.card * r :=
begin
  intro,
  rw [the_pairs, finset.card_bind],
  transitivity,
      apply (finset.sum_congr rfl _),
        intro, exact r,
      intros,
      rw [finset.card_map, card_all_removals],
      refine (a _ H),
    rw [← nat.smul_eq_mul, ← finset.sum_const],
  intros,
  rw finset.disjoint_iff_ne, finish
end

def from_below (𝒜 : finset (finset X)) : finset (finset X × finset X) :=
(∂𝒜).bind (λ B, (finset.univ \ B).attach.map ⟨λ x, (insert x.1 B, B), 
begin
  rintros ⟨x1, x1h⟩ ⟨x2, x2h⟩ h,
  injection h, congr,
  have q := finset.mem_insert_self x1 B,
  rw [h_1, finset.mem_insert] at q,
  rw finset.mem_sdiff at x1h,
  tauto
end
⟩)

lemma mem_the_pairs (𝒜 : finset (finset X)) (A B : finset X) : (A,B) ∈ the_pairs 𝒜 ↔ A ∈ 𝒜 ∧ B ∈ all_removals A :=
begin
  rw [the_pairs, finset.mem_bind],
  split; intro h,
    rcases h with ⟨a, Ha, h⟩,
    rw finset.mem_map at h,
    rcases h with ⟨b, Hb, h⟩,
    injection h with Ah Bh,
    rw [Ah, Bh] at *,
    exact ⟨Ha, Hb⟩,
  refine ⟨A, h.1, _⟩,
  rw finset.mem_map,
  tauto
end

lemma mem_from_below {𝒜 : finset (finset X)} (A B : finset X) :
  A ∈ 𝒜 ∧ (∃ (i ∉ B), insert i B = A) → (A,B) ∈ from_below 𝒜 :=
begin
  intro,
  rw [from_below, finset.mem_bind],
  rcases a with ⟨Ah, i, ih, a⟩,
  refine ⟨B, _, _⟩,
    rw mem_shadow,
    refine ⟨A, Ah, i, _, _⟩;
    rw ← a,
    apply finset.mem_insert_self,
    apply finset.erase_insert ih,
  rw finset.mem_map,
  refine ⟨⟨i, finset.mem_sdiff.2 ⟨complete _, ih⟩⟩, finset.mem_attach _ _, by simpa⟩
end

lemma above_sub_below (𝒜 : finset (finset X)) : the_pairs 𝒜 ⊆ from_below 𝒜 :=
begin
  rintros ⟨A,B⟩ h,
  rw [mem_the_pairs, mem_all_removals] at h,
  apply mem_from_below,
  rcases h with ⟨Ah, i, ih, AeB⟩,
  refine ⟨Ah, i, _, _⟩; rw ← AeB,
  apply finset.not_mem_erase,
  apply finset.insert_erase ih
end

lemma card_from_below {n : ℕ} (𝒜 : finset (finset X)) {h : card X = n}: is_layer 𝒜 (r+1) → (from_below 𝒜).card ≤ (∂𝒜).card * (n - r) :=
begin
  intro,
  rw [from_below],
  transitivity,
    apply finset.card_bind_le,
  apply ge_of_eq,
  symmetry,
  rw [← nat.smul_eq_mul, ← finset.sum_const],
  transitivity,
    apply finset.sum_congr rfl _,
      intro, exact (n-r),
    intros,
    rw [finset.card_map, finset.card_attach, finset.card_sdiff (finset.subset_univ _), finset.card_univ, h],
    have := shadow_layer 𝒜 a _ H,
    rw this,
  simp
end

theorem localLYM {n r : ℕ} (𝒜 : finset (finset X)) {hn : card X = n} {hr1 : r ≥ 1} {hr2 : r ≤ n} {H : is_layer 𝒜 r}:
  (𝒜.card : ℚ) / nat.choose n r ≤ (∂𝒜).card / nat.choose n (r-1) :=
begin
  apply multiply_out hr1 hr2,
  rw ← card_the_pairs _ H,
  transitivity,
    apply finset.card_le_of_subset (above_sub_below _),
  transitivity, 
    apply @card_from_below _ _ _ (r-1) _ _ hn,
    rw nat.sub_add_cancel hr1,
    exact H,
  rw nat.sub_sub_assoc hr2 hr1,
end

def ar (𝒜 : finset (finset X)) (r : ℕ) : finset (finset X) := 𝒜.filter (λ i, finset.card i = r)

reserve infix `#`:100
notation 𝒜#r := ar 𝒜 r

lemma mem_ar {𝒜 : finset (finset X)} (r : ℕ) (A : finset X) : A ∈ 𝒜#r ↔ A ∈ 𝒜 ∧ A.card = r :=
by rw [ar, finset.mem_filter]

lemma layered_ar (𝒜 : finset (finset X)) (r : ℕ) : is_layer (𝒜#r) r :=
begin
  intros A,
  rw mem_ar,
  tauto
end

def antichain (𝒜 : finset (finset X)) : Prop := ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, A ≠ B → ¬(A ⊆ B)

-- TODO: consider rewriting all these using nat.decreasing_induction
def decompose' (n : ℕ) (𝒜 : finset (finset X)) : Π (k : ℕ), finset (finset X)
  | 0 := 𝒜#n
  | (k+1) := 𝒜#(n - (k+1)) ∪ shadow (decompose' k)

def decompose'_layer {n : ℕ} (𝒜 : finset (finset X)) (k : ℕ) : is_layer (decompose' n 𝒜 k) (n-k) :=
begin
  induction k with _ k;
    rw decompose',
    apply layered_ar,
  rw ← union_layer,
  split,
    apply layered_ar,
  apply shadow_layer,
  apply k
end

lemma card_decompose' (𝒜 : finset (finset X)) (k n : ℕ) (h : card X = n) : finset.card (decompose' n 𝒜 k) ≤ nat.choose n (n-k) :=
begin
  have := size_in_layer (decompose'_layer _ _),
  rwa h at this
end

theorem antichain_prop {𝒜 : finset (finset X)} {r k n : ℕ} (hk : k ≤ n) (hr : r < k) 
  (h : card X = n) (H : antichain 𝒜) :
∀ A ∈ 𝒜#(n - k), ∀ B ∈ ∂decompose' n 𝒜 r, ¬(A ⊆ B) :=
begin
  induction r with r ih;
  intros A hA B' hB' m;
  rw [decompose'] at hB';
  rcases sub_of_shadow B' hB' with ⟨B, hB, _⟩;
  have k : A ⊆ B := trans ‹A ⊆ B'› ‹B' ⊆ B›;
  clear h_1_h hB' m B',
    rw [mem_ar] at *,
    apply H _ hA.1 _ hB.1 _ k,
    intro,
    rw [a, hB.2] at hA,
    have := hA.2,
    clear H h _inst_1 _inst_2 hB hA k a A B 𝒜,
    omega,
  rw finset.mem_union at hB,
  cases hB,
    rw [mem_ar] at *,
    apply H _ hA.1 _ hB.1 _ k,
    intro,
    rw [a, hB.2] at hA,
    have := hA.2,
    clear H h ih _inst_1 _inst_2 hB hA k a A B 𝒜,
    omega,
  apply ih (nat.lt_of_succ_lt hr) _ hA _ hB k,
end

lemma card_decompose'_other (𝒜 : finset (finset X)) (k n : ℕ) (hk : k ≤ n) (h : card X = n) (H : antichain 𝒜) : 
  finset.sum (finset.range (k+1)) (λ r, ((𝒜#(n-r)).card : ℚ) / nat.choose n (n-r)) ≤ ((decompose' n 𝒜 k).card : ℚ) / nat.choose n (n-k) :=
begin
  induction k with k ih,
    rw [finset.sum_range_one, div_le_div_iff]; norm_cast, exact nat.choose_pos (nat.sub_le _ _), exact nat.choose_pos (nat.sub_le _ _),
  rw finset.sum_range_succ,
  rw decompose',
  have: (𝒜#(n - (k + 1)) ∪ ∂decompose' n 𝒜 k).card = (𝒜#(n - (k + 1))).card + (∂decompose' n 𝒜 k).card,
    apply finset.card_disjoint_union,
    rw finset.disjoint_iff_ne,
    intros A hA B hB m,
    apply antichain_prop hk (lt_add_one k) h H A hA B hB,
    rw m, refl,
  rw this,
  have: ↑((𝒜#(n - (k + 1))).card + (∂decompose' n 𝒜 k).card) / (nat.choose n (n - nat.succ k) : ℚ) = 
        ((𝒜#(n - (k + 1))).card : ℚ) / (nat.choose n (n - nat.succ k)) + ((∂decompose' n 𝒜 k).card : ℚ) / (nat.choose n (n - nat.succ k)),
    rw ← add_div,
    norm_cast,
  rw this,
  apply add_le_add_left,
  transitivity,
    exact ih (le_of_lt hk),
  apply @localLYM _ _ _ _ _ _ h,
  rotate,
  exact nat.sub_le _ _,
  apply decompose'_layer,
  clear this this ih h H 𝒜 _inst_1 _inst_2,
  omega,
end

def decompose (n : ℕ) (𝒜 : finset (finset X)) (r : ℕ) : finset (finset X) :=
decompose' n 𝒜 (n-r)

def decompose_layer {n : ℕ} (𝒜 : finset (finset X)) (r : ℕ) (hr : r ≤ n) : is_layer (decompose n 𝒜 r) r :=
begin
  rw decompose,
  have := decompose'_layer 𝒜 (n-r),
  rwa nat.sub_sub_self hr at this
end

lemma sum_flip {α : Type*} [add_comm_monoid α] {n : ℕ} (f : ℕ → α) : finset.sum (finset.range (n+1)) (λ r, f (n - r)) = finset.sum (finset.range (n+1)) (λ r, f r) :=
begin
  induction n with n ih,
    rw [finset.sum_range_one, finset.sum_range_one],
  rw finset.sum_range_succ',
  rw finset.sum_range_succ _ (nat.succ n),
  simp [ih]
end

lemma card_decompose_other (𝒜 : finset (finset X)) (r n : ℕ) (h : card X = n) (H : antichain 𝒜) : 
  (finset.range (n+1)).sum (λ r, ((𝒜#r).card : ℚ) / nat.choose n r) ≤ (decompose n 𝒜 0).card / nat.choose n 0 :=
begin
  rw decompose,
  rw nat.sub_zero,
  by calc 
    (finset.range (n + 1)).sum (λ r, ((𝒜#r).card : ℚ) / nat.choose n r) 
          = (finset.range (n + 1)).sum (λ r, ((𝒜#(n-r)).card : ℚ) / nat.choose n (n-r)) 
                                            : by rw sum_flip (λ r, ((𝒜#r).card : ℚ) / nat.choose n r)
      ... ≤ ((decompose' n 𝒜 n).card : ℚ) / nat.choose n (n-n) : begin apply card_decompose'_other, refl, assumption, assumption end
      ... ≤ (decompose' n 𝒜 n).card / nat.choose n 0 : by simp
end

lemma lubell_yamamoto_meshalkin (n : ℕ) (𝒜 : finset (finset (fin n))) (H : antichain 𝒜) :
  (finset.range (n+1)).sum (λ r, ((𝒜#r).card : ℚ) / nat.choose n r) ≤ 1 :=
begin
  transitivity,
    apply card_decompose_other _ n _ (card_fin _) H,
  rw div_le_iff; norm_cast,
  rw decompose,
  have := card_decompose' 𝒜 n n (card_fin _),
  simp at *, assumption,
  apply nat.choose_pos (zero_le n)
end

lemma dominate_choose_lt {r n : ℕ} (h : r < n/2) : nat.choose n r ≤ nat.choose n (r+1) :=
begin
  have q : n - r > 0,
    rw gt_iff_lt,
    rw nat.lt_sub_left_iff_add_lt,
    rw add_zero,
    apply lt_of_lt_of_le h,
    exact nat.div_le_self n 2,
  apply le_of_mul_le_mul_right _ q,
  rw ← nat.choose_succ_right_eq,
  apply nat.mul_le_mul_left,
  rw ← nat.lt_iff_add_one_le,
  apply nat.lt_sub_left_of_add_lt,
  by calc r + r < n/2 + n/2 : add_lt_add h h
            ... = n/2 * 2   : (mul_two _).symm
            ... ≤ n         : nat.div_mul_le_self n 2
end

lemma dominate_choose_lt' {n r : ℕ} (hr : r ≤ n/2) : nat.choose n r ≤ nat.choose n (n/2) :=
begin
  refine (@nat.decreasing_induction (λ k, k ≤ n/2 → nat.choose n k ≤ nat.choose n (n/2)) _ r (n/2) hr (λ _, by refl)) hr,
  intros m k a,
  cases lt_or_eq_of_le a,
    transitivity,
      apply dominate_choose_lt,
      exact h,
    exact k h,
  rw h,
end 

lemma dominate_choose {r n : ℕ} : nat.choose n r ≤ nat.choose n (n/2) :=
begin
  cases le_or_gt r n with b b,
    cases le_or_gt r (n/2) with a,
      apply dominate_choose_lt' a,
    rw ← nat.choose_symm,
    apply dominate_choose_lt',
    rw nat.sub_le_iff,
    transitivity,
      swap,
      exact h,
    rw [nat.sub_le_left_iff_le_add, nat.add_succ, ← two_mul],
    have q := nat.mod_add_div n 2,
    cases nat.mod_two_eq_zero_or_one n with h h; rw h at q,
      rw zero_add at q,
      rw q,
      exact nat.le_succ n,
    rwa [← nat.add_one, nat.add_comm, q], 
  rw nat.choose_eq_zero_of_lt b,
  apply zero_le
end

lemma test {a b : ℕ} : (a : ℚ) * (1 / b) = a / b := 
begin
  rw @div_eq_mul_inv _ _ ↑a,
  rw one_div_eq_inv
end

lemma sperner (n : ℕ) (𝒜 : finset (finset (fin n))) (H : antichain 𝒜) : 𝒜.card ≤ nat.choose n (n / 2) := 
begin
  have q1 := lubell_yamamoto_meshalkin n 𝒜 H,
  set f := (λ (r : ℕ), ((𝒜#r).card : ℚ) / nat.choose n r),
  set g := (λ (r : ℕ), ((𝒜#r).card : ℚ) / nat.choose n (n/2)),
  have q2 : finset.sum (finset.range (n + 1)) g ≤ finset.sum (finset.range (n + 1)) f,
    apply finset.sum_le_sum,
    intros r hr,
    apply div_le_div_of_le_left; norm_cast,
        apply zero_le,
      apply nat.choose_pos,
      rw finset.mem_range at hr,
      rwa ← nat.lt_succ_iff,
    apply dominate_choose,
  have := trans q2 q1,
  set h := (λ (r : ℕ), ((𝒜#r).card : ℚ) * (1 / nat.choose n (n/2))),
  have q: g = h,
    ext r,
    apply test.symm,
  rw [q, ← finset.sum_mul, one_div_eq_inv, ← div_eq_mul_inv, div_le_iff] at this,
    swap, norm_cast, apply nat.choose_pos, apply nat.div_le_self',
  rw [one_mul, ← finset.sum_nat_cast] at this,
  norm_cast at this,
  rw ← finset.card_bind at this,
    suffices m: finset.bind (finset.range (n + 1)) (λ (u : ℕ), 𝒜#u) = 𝒜,
      rwa m at this,
    ext,
    rw finset.mem_bind,
    split, rintro ⟨_,_,q⟩,
      rw mem_ar at q,
      exact q.1,
    intro A, 
    use a.card,
    refine ⟨_, _⟩,
      rw finset.mem_range,
      have k: a.card ≤ (elems (fin n)).card := finset.card_le_of_subset (finset.subset_univ _),
      have: finset.card (elems (fin n)) = fintype.card (fin n), rw [fintype.card, finset.univ],
      rw [this, card_fin] at k,
      rwa nat.lt_succ_iff,
    rw mem_ar,
    tauto,
  intros x _ y _ ne,
  rw finset.disjoint_left,
  intros a Ha,
  finish [mem_ar]
end

variables {n : ℕ} {𝒜 : finset (finset (fin n))}

def compress (A : finset (fin n)) (i j : fin n) : finset (fin n) := 
if (j ∈ A ∧ i ∉ A)
  then insert i (A.erase j)
  else A

local notation `C` := compress

def compressed_set {A : finset (fin n)} {i j : fin n} : ¬ (j ∈ C A i j ∧ i ∉ C A i j) :=
begin
  intro,
  rw compress at a,
  split_ifs at a,
    apply a.2,
    apply mem_insert_self,
  exact h a
end

lemma compress_idem (A : finset (fin n)) (i j : fin n) : C (C A i j) i j = C A i j :=
begin
  rw compress,
  split_ifs,
    exfalso,
    apply compressed_set h,
  refl
end

def compress_family (𝒜 : finset (finset (fin n))) (i j : fin n) : finset (finset (fin n)) :=
𝒜.image (λ A, compress A i j) ∪ 𝒜.filter (λ A, compress A i j ∈ 𝒜)

local notation `CC` := compress_family

@[reducible] def compress_motion (𝒜 : finset (finset (fin n))) (i j : fin n) : finset (finset (fin n)) := 𝒜.filter (λ A, compress A i j ∈ 𝒜)
@[reducible] def compress_remains (𝒜 : finset (finset (fin n))) (i j : fin n) := (𝒜.filter (λ A, compress A i j ∉ 𝒜)).image (λ A, compress A i j)

lemma mem_compress_motion {i j : fin n} (A : finset (fin n)) : A ∈ compress_motion 𝒜 i j ↔ A ∈ 𝒜 ∧ C A i j ∈ 𝒜 :=
by rw mem_filter

lemma mem_compress_remains {i j : fin n} (A : finset (fin n)) : A ∈ compress_remains 𝒜 i j ↔ A ∉ 𝒜 ∧ (∃ B ∈ 𝒜, C B i j = A) :=
begin
  simp [compress_remains], 
  split; rintro ⟨p, q, r⟩,
    exact ⟨r ▸ q.2, p, ⟨q.1, r⟩⟩,
  exact ⟨q, ⟨r.1, r.2.symm ▸ p⟩, r.2⟩, 
end

-- TODO: rewrite this. maybe define CC like this?
lemma compress_eq (i j : fin n) : CC 𝒜 i j = compress_remains 𝒜 i j ∪ compress_motion 𝒜 i j :=
begin
  rw compress_family,
  ext B,
  simp,
  split; intro p; cases p,
  { rcases p with ⟨A, ⟨l, r⟩⟩,
    by_cases (C A i j ∈ 𝒜),
    { left,
      rw [← r, compress_idem],
      tauto },
    { right,
      use A, tauto }},
  { tauto },
  { tauto },
  { rcases p with ⟨A, _⟩,
    left, use A,
    tauto }
end

lemma compress_disjoint (i j : fin n) : disjoint (compress_remains 𝒜 i j) (compress_motion 𝒜 i j) :=
begin
  rw disjoint_left,
  intros A HA HB,
  rw mem_compress_motion at HB,
  rw mem_compress_remains at HA,
  exact HA.1 HB.1
end

lemma inj_ish (X Y : finset (fin n)) (i j : fin n) (hX : j ∈ X ∧ i ∉ X) (hY : j ∈ Y ∧ i ∉ Y) 
  (Z : insert i (erase X j) = insert i (erase Y j)) : X = Y := 
begin
  ext x, split,
  all_goals { intro p, 
              by_cases h₁: (x=j), {rw h₁, tauto}, 
              have h₂: x ≠ i, {intro, rw a at p, tauto},
              rw ext at Z,
              replace Z := Z x,
              rw [mem_insert, mem_erase, mem_insert, mem_erase] at Z,
              tauto
              }
end

lemma compressed_size (i j : fin n) : (CC 𝒜 i j).card = 𝒜.card :=
begin
  rw compress_eq,
  rw card_disjoint_union (compress_disjoint _ _),
  rw card_image_of_inj_on,
    rw ← card_disjoint_union,
      rw union_comm,
      rw filter_union_filter_neg_eq,
    rw disjoint_iff_inter_eq_empty,
    rw inter_comm,
    apply filter_inter_filter_neg_eq,
  intros X HX Y HY Z,
  rw mem_filter at HX HY,
  rw compress at HX Z,
  split_ifs at HX Z,
    rw compress at HY Z,
    split_ifs at HY Z,
      refine inj_ish X Y i j h h_1 Z,
    tauto,
  tauto
end

lemma insert_erase_comm {A : finset (fin n)} {i j : fin n} (h : i ≠ j) : insert i (erase A j) = erase (insert i A) j :=
begin
  simp [ext],
  intro x,
  split; intro p,
    cases p,
      split,
        rw p, tauto,
      tauto,
    tauto,
  tauto,
end

lemma compress_moved {A : finset (fin n)} {i j : fin n} (h₁ : A ∈ CC 𝒜 i j) (h₂ : A ∉ 𝒜) : i ∈ A ∧ j ∉ A ∧ erase (insert j A) i ∈ 𝒜 :=
begin
  rw [compress_eq, mem_union, mem_compress_motion, mem_compress_remains] at h₁,
  cases h₁,
    rcases h₁ with ⟨_, B, H, HB⟩,
    rw compress at HB,
    split_ifs at HB,
      rw ← HB,
      split,
        apply mem_insert_self,
      split,
        rw mem_insert,
        intro,
        cases a,
          safe,
        apply not_mem_erase j B a,
      have: erase (insert j (insert i (erase B j))) i = B,
        rw [insert_erase_comm, insert_erase (mem_insert_of_mem h.1), erase_insert h.2], 
        safe, 
      rw this, assumption,
    rw HB at H, tauto,
  tauto
end

lemma compress_held {A : finset (fin n)} {i j : fin n} (h₁ : j ∈ A) (h₂ : A ∈ CC 𝒜 i j) : A ∈ 𝒜 :=
begin
  rw [compress_eq, mem_union] at h₂,
  cases h₂,
    rw mem_compress_remains at h₂,
    rcases h₂.2 with ⟨B, HB, HB₂⟩,
    rw ← HB₂ at h₁,
    rw compress at HB₂ h₁,
    split_ifs at HB₂ h₁,
      rw mem_insert at h₁,
      cases h₁,
        exfalso, safe,
      exfalso, apply not_mem_erase _ _ h₁,
    rwa ← HB₂,
  rw mem_compress_motion at h₂,
  tauto,
end

lemma compress_both {A : finset (fin n)} {i j : fin n} (h₁ : A ∈ CC 𝒜 i j) (h₂ : j ∈ A) (h₃ : i ∉ A) : erase (insert i A) j ∈ 𝒜 :=
begin
  have: A ∈ 𝒜, apply compress_held ‹_› ‹_›,
  rw [compress_eq, mem_union, mem_compress_motion, mem_compress_remains] at h₁,
  replace h₁ : C A i j ∈ 𝒜, tauto,
  rw compress at h₁,
  have: j ∈ A ∧ i ∉ A := ⟨h₂, h₃⟩,
  split_ifs at h₁,
  rwa ← insert_erase_comm,
  intro, rw a at *, tauto,
end

lemma sdiff_union_inter (A B : finset X) : (A \ B) ∪ (A ∩ B) = A :=
begin
  ext, simp, tauto
end

lemma sdiff_inter_inter (A B : finset X) : (A \ B) ∩ (A ∩ B) = ∅ :=
begin
  ext, simp
end

lemma compression_reduces_shadow' (i j : fin n) : (∂ (CC 𝒜 i j)).card ≤ (∂𝒜).card := 
begin
  set 𝒜' := CC 𝒜 i j,
  suffices: (∂𝒜' \ ∂𝒜).card ≤ (∂𝒜 \ ∂𝒜').card,
    suffices: card (∂𝒜' \ ∂𝒜 ∪ ∂𝒜' ∩ ∂𝒜) ≤ card (∂𝒜 \ ∂𝒜' ∪ ∂𝒜 ∩ ∂𝒜'),
      rwa [sdiff_union_inter, sdiff_union_inter] at this,
    rw [card_disjoint_union (disjoint_iff_inter_eq_empty.2 (sdiff_inter_inter (∂𝒜') (∂𝒜))), 
        card_disjoint_union (disjoint_iff_inter_eq_empty.2 (sdiff_inter_inter (∂𝒜) (∂𝒜'))),
        inter_comm],
    exact add_le_add_right ‹_› _, 

  have q₁: ∀ B ∈ ∂𝒜' \ ∂𝒜, i ∈ B ∧ j ∉ B ∧ erase (insert j B) i ∈ ∂𝒜 \ ∂𝒜',
    intros B HB,
    have k: B ∈ ∂𝒜' ∧ B ∉ ∂𝒜,
      rwa ← mem_sdiff,
    have k' := k.2,
    replace k := k.1,
    have m: ∀ y ∉ B, insert y B ∉ 𝒜,
      intros y _ _,
      apply k',
      rw mem_shadow',
      exact ⟨y, H, a⟩,
    rcases mem_shadow'.1 k with ⟨x, _, _⟩,
    have q := compress_moved ‹insert x B ∈ 𝒜'› (m _ ‹x ∉ B›),
    rw insert.comm at q,
    have: j ∉ B := q.2.1 ∘ mem_insert_of_mem,
    have: i ≠ j, intro a, rw a at q, tauto,
    have x_ne_i: x ≠ i, intro a, rw a at *, rw [erase_insert] at q, 
      exact m _ ‹j ∉ B› q.2.2,
      rw mem_insert, tauto,
    have x_ne_j: x ≠ j, intro a, rw a at q, exact q.2.1 (mem_insert_self _ _), 
    have: i ∈ B := mem_of_mem_insert_of_ne q.1 ‹x ≠ i›.symm,
    refine ⟨‹_›, ‹_›, _⟩,
    rw mem_sdiff,
    split,
      rw mem_shadow',
      rw ← insert_erase_comm ‹x ≠ i› at q,
      refine ⟨x, _, q.2.2⟩, 
      intro a, 
      exact ‹x ∉ B› (mem_of_mem_insert_of_ne (mem_of_mem_erase a) ‹x ≠ j›),

    clear h_w h_h q x_ne_i x_ne_j x,

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
  
  set f := (λ (B : finset (fin n)), erase (insert j B) i),
  apply card_le_card_of_inj_on f,
    intros _ HB,
    exact (q₁ _ HB).2.2,
 
  intros B₁ HB₁ B₂ HB₂ f₁,
  have := q₁ B₁ HB₁,
  have := q₁ B₂ HB₂,
  rw ext at f₁,
  ext,
  split;
  all_goals { intro,
              have p := f₁ a,
              rw [mem_erase, mem_erase, mem_insert, mem_insert] at p,
              by_cases (a = i),
                rw h, tauto,
              rw [and_iff_right h, and_iff_right h] at p,
              have z: j ∉ B₁ ∧ j ∉ B₂, tauto,
              have: a ≠ j, intro lie, rw ← lie at z, tauto,
              tauto }
end