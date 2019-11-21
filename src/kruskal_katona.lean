import data.finset
import data.fin
import data.rat
import data.nat.basic
import data.fintype
import algebra.big_operators
import algebra.group_power
import tactic.omega
import tactic.linarith

open fintype

variables {X : Type*}
variables [fintype X] [decidable_eq X]
variables {r : ℕ}

@[reducible] def rset (r : ℕ) (X) [fintype X] := {x : finset X // x ∈ finset.powerset_len r (elems X)}

def card_of_rset {x : rset r X} : finset.card x.val = r := (finset.mem_powerset_len.1 x.2).2

instance rset_fintype (r : ℕ) : fintype (rset r X) := finset.subtype.fintype _

@[reducible]
def rset_mk (A : finset X) (H : finset.card A = r) : rset r X := 
begin
  refine ⟨A, _⟩,
  rw finset.mem_powerset_len,
  exact ⟨finset.subset_univ _, H⟩,
end

@[reducible] instance : has_mem X (rset r X) := ⟨λ i A, i ∈ A.1⟩

theorem eq_of_veq : ∀ {s t : rset r X}, s.1 = t.1 → s = t
| ⟨s, _⟩ ⟨t, _⟩ rfl := rfl

theorem val_inj {s t : rset r X} : s.1 = t.1 ↔ s = t :=
⟨eq_of_veq, congr_arg _⟩

theorem ext {s₁ s₂ : rset r X} : s₁ = s₂ ↔ (∀ a, a ∈ s₁ ↔ a ∈ s₂) :=
val_inj.symm.trans finset.ext

@[ext]
theorem ext' {s₁ s₂ : rset r X} : (∀ a, a ∈ s₁ ↔ a ∈ s₂) → s₁ = s₂ :=
ext.2

def example1 : rset 4 (fin 9) := rset_mk {0,1,4,5} (by trivial)
def example2 : finset (rset 3 (fin 5)) := 
{rset_mk {0,1,2} (by trivial),
 rset_mk {0,1,3} (by trivial),
 rset_mk {0,2,3} (by trivial),
 rset_mk {0,2,4} (by trivial)
 }

#eval example1
#eval example2

#eval elems (rset 3 (fin 5))

def stretch (A : rset r X) (s : X) (h : s ∉ A) : rset (r+1) X := 
rset_mk (insert s (A.1)) $ by rw [finset.card_insert_of_not_mem h, card_of_rset]

lemma mem_stretch (A : rset r X) (s : X) {h : s ∉ A} (i : X) : i ∈ stretch A s h ↔ i ∈ A ∨ i = s := 
by rw [stretch, finset.mem_insert]; tauto

lemma stretch_subset {A : rset r X} {s : X} (h : s ∉ A) : A.1 ⊆ (stretch A s h).1 := 
finset.subset_insert _ _

lemma mem_stretch_self {A : rset r X} {s : X} (h : s ∉ A) : s ∈ stretch A s h := 
finset.mem_insert_self _ _

lemma mem_stretch_of_mem {A : rset r X} {s t : X} {p : s ∉ A} : t ∈ A → t ∈ stretch A s p := 
finset.mem_insert_of_mem

def erase (A : rset (r+1) X) (s : X) (h : s ∈ A) : rset r X :=
rset_mk (finset.erase (A.1) s) $ by rw [finset.card_erase_of_mem h, card_of_rset]; trivial

lemma mem_erase (A : rset (r+1) X) (s : X) (h : s ∈ A) (i : X) : i ∈ erase A s h ↔ i ∈ A ∧ i ≠ s :=
by rw [erase, finset.mem_erase]; tauto

lemma subset_erase {A : rset (r+1) X} {s : X} (h : s ∈ A) : (erase A s h).1 ⊆ A.1 :=
finset.erase_subset _ _

theorem not_mem_erase_self {A : rset (r+1) X} {s : X} (h : s ∈ A) : s ∉ erase A s h := 
finset.not_mem_erase _ _

lemma erase_iff_stretch {A : rset r X} {B : rset (r+1) X} {s : X} {H1 : s ∉ A} {H2 : s ∈ B} : stretch A s H1 = B ↔ erase B s H2 = A:=
begin
  split; intros p; ext, 
    rw mem_erase,
    split; intro k,
      rw [← p, mem_stretch] at k,
      tauto,
    split,
      exact (p ▸ stretch_subset ‹_› k),
    intro, rw ‹a = s› at k, tauto,
  rw mem_stretch,
  split; intro x,
    cases x,
      rw ← p at x,
      exact (subset_erase ‹_› x),
    rwa x,
  rw [← p, mem_erase], 
  by_cases (a = s),
    right, assumption,
    left, exact ⟨x, h⟩
end

lemma erase_iff_stretch' {A : rset r X} {B : rset (r+1) X} : (∃ i ∉ A, stretch A i H = B) ↔ (∃ i ∈ B, erase B i H = A) := 
begin
  split; rintro ⟨i, Hi, t⟩; use i; refine ⟨_, _⟩, 
    rw ← t, apply mem_stretch_self,
    rw ← erase_iff_stretch, 
    exact t,
  rw ← t, apply not_mem_erase_self,
  rw erase_iff_stretch,
  exact t
end

lemma erase_stretch (A : rset r X) (s : X) (h : s ∉ A) : erase (stretch A s h) s (mem_stretch_self h) = A := 
erase_iff_stretch.1 rfl

lemma stretch_erase (A : rset (r+1) X) (s : X) (h : s ∈ A) : stretch (erase A s h) s (not_mem_erase_self h) = A := 
erase_iff_stretch.2 rfl

theorem rset_card (r : ℕ) : card (rset r X) = nat.choose (card X) r := 
begin
  rw card_of_subtype (finset.powerset_len r (elems X)) (λ _, iff.rfl),
  apply finset.card_powerset_len
end

def all_removals {r : ℕ} (A : rset (r+1) X) : finset (rset r X) :=
begin
  refine A.1.attach.map ⟨λ i, erase A i.1 i.2, _⟩,
  rintros ⟨x1, x1p⟩ ⟨_, _⟩ q,
  dsimp at q,
  rw [erase, erase] at q,
  simp at q,
  congr,
  by_contradiction,
  apply finset.not_mem_erase x1 A.1,
  rw q,
  apply finset.mem_erase_of_ne_of_mem a x1p,
end

def mem_all_removals {r : ℕ} {A : rset (r+1) X} {B : rset r X} : B ∈ all_removals A ↔ ∃ i ∈ A, erase A i H = B :=
by simp [all_removals]

lemma card_map {α β} [decidable_eq β] {f : α ↪ β} {s : finset α} : (s.map f).card = s.card := 
begin
  rw finset.map_eq_image,
  rw finset.card_image_of_injective,
  exact f.2
end

lemma card_all_removals {r : ℕ} {A : rset (r+1) X} : (all_removals A).card = r + 1 :=
by rw [all_removals, card_map, finset.card_attach]; exact card_of_rset

def shadow {r : ℕ} (𝒜 : finset (rset (r+1) X)) : finset (rset r X) := 
𝒜.bind all_removals

reserve prefix `∂`:30
notation ∂𝒜 := shadow 𝒜

#eval ∂example2 -- should be {{0,1}, {0,2}, {0,3}, {0,4}, {1,2}, {1,3}, {2,3}, {2,4}}

def mem_shadow {r : ℕ} {𝒜 : finset (rset (r+1) X)} (B : rset r X) : B ∈ ∂𝒜 ↔ ∃ A ∈ 𝒜, ∃ i ∈ A, erase A i H = B := 
by simp [shadow, all_removals]

#eval rat.mk (finset.card example2) (nat.choose 5 3)
#eval rat.mk (finset.card (∂example2)) (nat.choose 5 2)

#check rat.mk (finset.card (elems (fin 3))) 3
#eval rat.mk (finset.card (elems (fin 3))) 4

def cube_graph : rel (rset r X) (rset (r+1) X) := λ A B, A.1 ⊆ B.1

lemma graph_misses_elem (A : rset r X) (B : rset (r+1) X) : cube_graph A B → ∃ i, i ∈ B ∧ i ∉ A := 
begin
  rw cube_graph, simp, intro p,
  have := finset.card_sdiff p,
  simp [card_of_rset, finset.card_eq_one] at this, 
  cases this with i h,
  use i, rw [← finset.mem_sdiff, h],
  apply finset.mem_singleton_self
end

lemma test {A : rset r X} {B : rset (r+1) X} : finset.card (B.1 \ A.1) = 1 ↔ cube_graph A B := 
begin
  rw cube_graph, unfold,
  rw [← finset.sdiff_eq_empty_iff_subset, ← finset.card_eq_zero],
  have q: finset.card A.1 + finset.card (B.1 \ A.1) = finset.card B.1 + finset.card (A.1 \ B.1),
    rw [← finset.card_disjoint_union (finset.disjoint_sdiff), 
        ← finset.card_disjoint_union (finset.disjoint_sdiff), 
        finset.union_sdiff_symm], 
  simp [card_of_rset] at q,
  rw [q, nat.one_add, nat.succ_inj']
end

lemma stretch_iff_related {A : rset r X} {B : rset (r+1) X} : cube_graph A B ↔ ∃ (i ∉ A), stretch A i H = B := 
begin
  split, intro p,
    cases finset.card_eq_one.1 (test.2 p) with i _, 
    use i,
    have k : i ∈ B.1 ∧ i ∉ A.1 := finset.mem_sdiff.1 (‹B.1 \ A.1 = {i}›.symm ▸ finset.mem_singleton_self i),
    use k.2, ext, rw mem_stretch,
    refine ⟨λ s, s.elim _ (λ v, v.symm ▸ k.1), λ s, _⟩,
      rw cube_graph at p, apply p, 
    by_cases (a = i),
      right, assumption,
    left, by_contra, 
    exact ‹a ≠ i› (finset.mem_singleton.1 (‹B.1 \ A.1 = {i}› ▸ finset.mem_sdiff.2 ⟨‹_›, ‹_›⟩)), 
  rintros ⟨_, _, _⟩,
  rw cube_graph,
  rw ← ‹stretch A _ _ = B›,
  apply stretch_subset
end

lemma erase_iff_related (A : rset r X) (B : rset (r+1) X) : cube_graph A B ↔ ∃ (i ∈ B), erase B i H = A := 
iff.trans stretch_iff_related erase_iff_stretch'

def all_removals_iff_related {r : ℕ} {A : rset r X} {B : rset (r+1) X} : A ∈ all_removals B ↔ cube_graph A B :=
begin
  rw erase_iff_related,
  rw mem_all_removals,
end
-- by rw [erase_iff_related, mem_all_removals]

lemma choose_symm {n k : ℕ} (hk : k ≤ n) : nat.choose n k = nat.choose n (n-k) :=
calc nat.choose n k = nat.fact n / (nat.fact k * nat.fact (n - k)) : nat.choose_eq_fact_div_fact hk
     ...            = nat.fact n / (nat.fact (n - k) * nat.fact k) : by ac_refl
     ...            = nat.choose n (n-k) : by rw [nat.choose_eq_fact_div_fact (nat.sub_le _ _), nat.sub_sub_self hk]

lemma nat.choose_succ_right_eq {n k : ℕ} : nat.choose n (k + 1) * (k + 1) = nat.choose n k * (n - k) :=
begin
  have e : (n+1) * nat.choose n k = nat.choose n k * (k+1) + nat.choose n (k+1) * (k+1),
    rw [← nat.right_distrib, ← nat.choose_succ_succ, nat.succ_mul_choose_eq],
  rw [← nat.sub_eq_of_eq_add e, mul_comm, ← nat.mul_sub_left_distrib],
  simp
end

theorem div_le_div_iff {α} [linear_ordered_field α] {a b c d : α}
  (hc : 0 < c) (hd : 0 < d) : a / c ≤ b / d ↔ a * d ≤ b * c :=
by rw [le_div_iff hd, div_mul_eq_mul_div, div_le_iff hc]

theorem main_lemma {A B n r : ℕ} (hr1 : 1 ≤ r) (hr2 : r ≤ n)
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

lemma union_bound {A : finset (finset X)} : finset.card (A.fold (∪) ∅ id) ≤ A.fold (+) (0 : ℕ) finset.card := 
begin
  apply finset.induction_on A,
    rw [finset.fold_empty, finset.fold_empty, finset.card_empty],
  intros a s h k,
    rw [finset.fold_insert h, finset.fold_insert h], 
    transitivity,
      apply finset.card_union_le,
    apply add_le_add_left', exact k
end

lemma disjoint_all {α} [decidable_eq α] {A : finset (finset α)} {z : finset α} (h : ∀ x ∈ A, disjoint z x) : disjoint z (A.fold (∪) ∅ id) := 
begin
  revert h,
  apply finset.induction_on A,
  { rw finset.fold_empty,
    intro,
    apply finset.disjoint_empty_right },
  { intros a s h₂ ih h,
    rw finset.fold_insert h₂,
    rw finset.disjoint_union_right,
    split,
      exact h _ (finset.mem_insert_self _ _),
    exact ih (λ x hx, h _ (finset.mem_insert_of_mem hx)) }
end

lemma disjoint_union_cards {A : finset (finset X)} : (∀ x ∈ A, ∀ y ∈ A, x ≠ y → disjoint x y) → finset.card (A.fold (∪) ∅ id) = A.fold (+) (0 : ℕ) finset.card :=
begin
  apply finset.induction_on A,
    intro,
    rw [finset.fold_empty, finset.fold_empty, finset.card_empty],
  intros a s h₂ ih h,
    rw [finset.fold_insert h₂, finset.fold_insert h₂],
    rw finset.card_disjoint_union,
      congr,
      apply ih,
      intros x hx y hy t, 
      refine (h _ (finset.mem_insert_of_mem hx) _ (finset.mem_insert_of_mem hy) t),
  apply disjoint_all,
  intros x hx,
  apply h,
      exact finset.mem_insert_self _ _,
    exact finset.mem_insert_of_mem hx,
  dsimp, 
  intro,
  rw a_1 at h₂,
  exact h₂ hx
end

def from_above {n : ℕ} (𝒜 : finset (rset (r+1) (fin n))) : finset (rset (r+1) (fin n) × rset r (fin n)) :=
𝒜.bind $ λ A, (all_removals A).map ⟨λ x, (A, x), λ _ _, by simp⟩

lemma mem_from_above {n : ℕ} {𝒜 : finset (rset (r+1) (fin n))} {A : rset (r+1) (fin n)} {B : rset r (fin n)} : 
  (A,B) ∈ from_above 𝒜 ↔ A ∈ 𝒜 ∧ B ∈ all_removals A :=
begin
  rw [from_above, finset.mem_bind], 
  split; intro h,
    rcases h with ⟨a, Ha, h⟩,
    rw finset.mem_map at h,
    rcases h with ⟨b, Hb, h⟩,
    injection h with Ah Bh,
    rw [Ah, Bh] at *,
    exact ⟨Ha, Hb⟩,
  use A,
  use h.1,
  rw finset.mem_map,
  use B,
  use h.2,
  refl
end

lemma card_from_above {n : ℕ} (𝒜 : finset (rset (r+1) (fin n))) : (from_above 𝒜).card = 𝒜.card * (r+1) :=
begin
  rw [from_above, finset.card_bind],
    rw [← nat.smul_eq_mul, ← finset.sum_const],
    congr, ext,
    rw card_map,
    exact card_all_removals,
  intros,
  rw finset.disjoint_iff_ne,
  intros,
  rw finset.mem_map at *,
  rcases H_2 with ⟨_, _, At⟩,
  rcases H_3 with ⟨_, _, Bt⟩,
  intro,
  have q: a_1.1 = b.1, rw a_2,
  rw [←At, ←Bt] at q,
  exact a q
end

def complement {n : ℕ} (A : rset r (fin n)) : rset (n-r) (fin n) :=
begin
  refine rset_mk (finset.univ \ A.1) _,
  rw [finset.card_sdiff, card_of_rset, finset.card_univ, fintype.card_fin],
  apply finset.subset_univ
end

lemma mem_complement {n : ℕ} {x : fin n} {A : rset r (fin n)} : (x ∉ A ↔ x ∈ complement A) :=
begin
  rw [complement, finset.mem_sdiff],
  simp [complete]
end

def from_below {n : ℕ} (𝒜 : finset (rset (r+1) (fin n))) : finset (rset (r+1) (fin n) × rset r (fin n)) :=
begin
  refine (∂𝒜).bind (λ B, _),
  refine (finset.univ \ B.1).attach.map ⟨λ x, (stretch B x.1 (finset.mem_sdiff.1 x.2).2, B), _⟩,
  rintros ⟨x₁, x₁h⟩ ⟨x₂, x₂h⟩ h,
  rw finset.mem_sdiff at x₂h,
  injection h,
  congr,
  have q := mem_stretch_self x₂h.2,
  rw [← h_1, mem_stretch] at q,
  tauto
end

lemma mem_from_below {n : ℕ} {𝒜 : finset (rset (r+1) (fin n))} {A : rset (r+1) (fin n)} {B : rset r (fin n)} :
  (A,B) ∈ from_above 𝒜 ↔ A ∈ 𝒜 ∧ ∃ (i ∉ B), stretch B i H = A :=
begin
  rw [mem_from_above, ← stretch_iff_related, all_removals_iff_related]
end

lemma mem_from_below' {n : ℕ} {𝒜 : finset (rset (r+1) (fin n))} {A : rset (r+1) (fin n)} {B : rset r (fin n)} :
  A ∈ 𝒜 ∧ (∃ (i ∉ B), stretch B i H = A) → (A,B) ∈ from_below 𝒜 :=
begin
  intro h,
  rw [from_below, finset.mem_bind],
  use B,
  split,
    rw mem_shadow,
    use A,
    use h.1,
    refine erase_iff_stretch'.1 h.2,
  rw [finset.mem_map],
  rcases h.2 with ⟨_, _, _⟩,
  refine ⟨⟨w, finset.mem_sdiff.2 ⟨complete _, ‹_›⟩⟩, by simp, _⟩,
  dsimp,
  rw ‹stretch B w _ = A›
end

lemma above_sub_below {n : ℕ} {𝒜 : finset (rset (r+1) (fin n))} : from_above 𝒜 ⊆ from_below 𝒜 :=
begin
  intros x h,
  have e: x = (x.1, x.2), simp,
  rw e,
  apply mem_from_below',
  rw ← mem_from_below,
  rwa ← e,
end

lemma card_from_below {n : ℕ} (𝒜 : finset (rset (r+1) (fin n))) : (from_below 𝒜).card ≤ (∂𝒜).card * (n-r) :=
begin
  rw [from_below],
  transitivity,
    apply finset.card_bind_le,
  apply ge_of_eq,
  rw [← nat.smul_eq_mul, ← finset.sum_const],
  congr,
  ext,
  rw card_map,
  rw finset.card_attach,
  rw finset.card_sdiff,
  rw card_of_rset,
  rw [finset.card_univ, fintype.card_fin],
  apply finset.subset_univ
end

lemma finally {n r : ℕ} (hr2 : r + 1 ≤ n) : n - (r + 1) + 1 = n - r := 
begin
  rw ← nat.sub_add_comm hr2,
  exact nat.succ_sub_succ _ _
end

theorem localLYM {n r : ℕ} (𝒜 : finset (rset (r+1) (fin n))) {hr2 : r + 1 ≤ n} :
  (𝒜.card : ℚ) / nat.choose n (r+1) ≤ (∂𝒜).card / nat.choose n r :=
begin
  apply main_lemma (by simp) hr2,
  rw [finally hr2],
  exact (
    calc 𝒜.card * (r + 1) = (from_above 𝒜).card : (card_from_above 𝒜).symm
         ... ≤ (from_below 𝒜).card : begin apply finset.card_le_of_subset _, apply above_sub_below end
         ... ≤ finset.card (∂𝒜) * (n - r) : (card_from_below 𝒜)
  )
end