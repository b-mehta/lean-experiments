import data.finset
import data.fin
import data.rat
import data.nat.basic
import data.fintype
import tactic.omega
import tactic.linarith

open fintype

variables {X : Type*}
variables [fintype X] [decidable_eq X]
variables {r : ℕ}

@[reducible] def rset (r : ℕ) (X) [fintype X] := {x : finset X // x ∈ finset.powerset_len r (elems X)}

def card_of_rset (x : rset r X) : finset.card x.val = r := (finset.mem_powerset_len.1 x.2).2

instance rset_fintype (r : ℕ) : fintype (rset r X) := finset.subtype.fintype _

def rset_mk (A : finset X) (H : finset.card A = r) : rset r X := 
begin
  refine ⟨A, _⟩,
  rw finset.mem_powerset_len,
  refine ⟨λ x _, complete x, H⟩,
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
begin
  use (insert s (A.1)),
  rw finset.mem_powerset_len,
  split,
    apply finset.subset_univ,
  rw finset.card_insert_of_not_mem h,
  rw card_of_rset A
end

lemma mem_stretch (A : rset r X) (s : X) {h : s ∉ A} (i : X) : i ∈ stretch A s h ↔ i ∈ A ∨ i = s := 
by rw [stretch, finset.mem_insert]; tauto

lemma stretch_subset {A : rset r X} {s : X} (h : s ∉ A) : A.1 ⊆ (stretch A s h).1 := 
finset.subset_insert _ _

lemma mem_stretch_self {A : rset r X} {s : X} (h : s ∉ A) : s ∈ stretch A s h := 
finset.mem_insert_self _ _

lemma mem_stretch_of_mem (A : rset r X) (s t : X) (p : s ∉ A) : t ∈ A → t ∈ stretch A s p := 
finset.mem_insert_of_mem

def erase (A : rset r X) (s : X) (h : s ∈ A) : rset (r-1) X :=
⟨finset.erase (A.1) s, finset.mem_powerset_len.2 ⟨finset.subset_univ _, 
  begin
    rw finset.card_erase_of_mem h,
    rw card_of_rset A,
    trivial
  end⟩⟩

lemma mem_erase (A : rset r X) (s : X) (h : s ∈ A) (i : X) : i ∈ erase A s h ↔ i ∈ A ∧ i ≠ s :=
by rw [erase, finset.mem_erase]; tauto

lemma subset_erase {A : rset r X} {s : X} (h : s ∈ A) : (erase A s h).1 ⊆ A.1 :=
finset.erase_subset _ _

theorem not_mem_erase_self {A : rset r X} {s : X} (h : s ∈ A) : s ∉ erase A s h := 
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

def shadow {r : ℕ} (𝒜 : finset (rset r X)) : finset (rset (r-1) X) := 
begin
  refine 𝒜.bind (λ A, _),
  refine A.1.attach.map ⟨_, _⟩, 
    intro i,
    apply erase ⟨A.1, A.2⟩ i.1,
    exact i.2,
  rintros ⟨x1, x1p⟩ ⟨_, _⟩ q,
  rw [erase, erase] at q,
  simp at q,
  congr,
  by_contradiction,
  apply finset.not_mem_erase x1 A.1,
  rw q,
  apply finset.mem_erase_of_ne_of_mem a x1p,
end

#eval shadow example2 -- should be {{0,1}, {0,2}, {0,3}, {0,4}, {1,2}, {1,3}, {2,3}, {2,4}}

def mem_shadow {r : ℕ} {𝒜 : finset (rset r X)} (B : rset (r-1) X) : B ∈ shadow 𝒜 ↔ ∃ A ∈ 𝒜, ∃ i ∈ A, erase A i H = B := 
by simp [shadow]

#eval rat.mk (finset.card example2) (nat.choose 5 3)
#eval rat.mk (finset.card (shadow example2)) (nat.choose 5 2)

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

lemma thingy (A : finset X) (B : finset X) : A ∪ (B \ A) = A ∪ B :=
by ext; simp [finset.mem_union, finset.mem_sdiff]; tauto

#print thingy

lemma thingy2 (A : finset X) (B : finset X) : A ∪ (B \ A) = B ∪ (A \ B) :=
by rw [thingy, thingy, finset.union_comm]

lemma thingy3 (A : finset X) (B : finset X) : A \ B = ∅ ↔ A ⊆ B :=
by simp [finset.ext, finset.subset_iff]

lemma thingy5 (A : finset X) : (∃ x, A = finset.singleton x) ↔ ∃! x, x ∈ A := 
begin
  split; rintro ⟨x, t⟩; use x,
    rw t, 
    exact ⟨finset.mem_singleton_self _, λ i, finset.mem_singleton.1⟩, 
  ext, rw finset.mem_singleton, 
  exact ⟨λ r, t.right _ r, λ r, r.symm ▸ t.left⟩
end

lemma thingy4 (A : finset X) : finset.card A = 1 ↔ ∃! x, x ∈ A :=
by rw [← thingy5, finset.card_eq_one]

lemma test {A : rset r X} {B : rset (r+1) X} : finset.card (B.1 \ A.1) = 1 ↔ cube_graph A B := 
begin
  rw cube_graph,
  have : finset.card A.1 + finset.card (B.1 \ A.1) = finset.card B.1 + finset.card (A.1 \ B.1),
    rw [← finset.card_disjoint_union (finset.disjoint_sdiff), ← finset.card_disjoint_union (finset.disjoint_sdiff), thingy2], 
  rw [card_of_rset, card_of_rset] at this,
  simp at this,
  rw this,
  transitivity (finset.card (A.1 \ B.1) = 0),
    split; intro p,
      apply add_left_cancel, assumption,
    rw p,
  simp [thingy3]
end

lemma stretch_iff_related {A : rset r X} {B : rset (r+1) X} : cube_graph A B ↔ ∃ (i ∉ A), stretch A i H = B := 
begin
  split, intro p,
    cases finset.card_eq_one.1 (test.2 p) with i _, use i,
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

lemma sub_sub_assoc {r k n : ℕ} (h1 : k ≤ r) (h2 : r ≤ n) : n - r + k = n - (r - k) := 
by omega

lemma choose_symm {n k : ℕ} (hk : k ≤ n) : nat.choose n k = nat.choose n (n-k) :=
calc nat.choose n k = nat.fact n / (nat.fact k * nat.fact (n - k)) : nat.choose_eq_fact_div_fact hk
     ...            = nat.fact n / (nat.fact (n - k) * nat.fact k) : by rw mul_comm
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

lemma fact_pred {r : ℕ} (h : r > 0) : nat.fact r = r * nat.fact (r-1) := 
calc nat.fact r = nat.fact (nat.succ (r-1))       : by rw [← nat.pred_eq_sub_one, nat.succ_pred_eq_of_pos h]
        ...     = nat.succ (r-1) * nat.fact (r-1) : nat.fact_succ _
        ...     = r * nat.fact (r-1)              : by rw [← nat.pred_eq_sub_one, nat.succ_pred_eq_of_pos h]

lemma choose_lemma {n r : ℕ} (hr1 : 1 ≤ r) (hr2 : r ≤ n) : (n - r + 1) * nat.choose n (r-1) = nat.choose n r * r :=
begin
  have: r - 1 ≤ n := le_trans (nat.pred_le r) ‹r ≤ n›,
  apply nat.eq_of_mul_eq_mul_right (mul_pos (nat.fact_pos (r-1)) (nat.fact_pos (n-r))),
  by calc (n - r + 1) * nat.choose n (r - 1) * (nat.fact (r - 1) * nat.fact (n - r))
        = nat.choose n (r-1) * nat.fact (r-1) * ((n - r + 1) * nat.fact (n - r)) : by ac_refl
    ... = nat.choose n (r-1) * nat.fact (r-1) * nat.fact (n - r + 1)             : by rw ← nat.fact_succ
    ... = nat.choose n (r-1) * nat.fact (r-1) * nat.fact (n - (r - 1))           : by rw sub_sub_assoc hr1 hr2
    ... = nat.fact n                                                             : by rw nat.choose_mul_fact_mul_fact ‹r - 1 ≤ n›
    ... = nat.choose n r * nat.fact r * nat.fact (n - r)                         : by rw ← nat.choose_mul_fact_mul_fact ‹r ≤ n›
    ... = nat.choose n r * (r * nat.fact (r - 1)) * nat.fact (n - r)             : by rw fact_pred ‹r ≥ 1›
    ... = nat.choose n r * r * (nat.fact (r - 1) * nat.fact (n - r))             : by ac_refl,
end

lemma main_lemma {A B n r : ℕ} (hr1 : 1 ≤ r) (hr2 : r ≤ n) : A * r ≤ B * (n - r + 1) → (A : ℚ) / (nat.choose n r) ≤ B / nat.choose n (r-1) := 
begin
  intro k,
  have: r - 1 ≤ n := le_trans (nat.pred_le r) ‹r ≤ n›,
  have: 0 < nat.choose n (r-1) := nat.choose_pos ‹r - 1 ≤ n›,
  have: 0 < nat.choose n r := nat.choose_pos ‹r ≤ n›,
  rw [div_le_iff', mul_comm, div_mul_eq_mul_div, le_div_iff]; norm_cast, rotate, 
    assumption, assumption,
  apply le_of_mul_le_mul_right _,
  exact hr1,
  by calc A * nat.choose n (r - 1) * r = A * r * nat.choose n (r-1) : by ac_refl
          ... ≤ B * (n - r + 1) * nat.choose n (r-1)                : by apply nat.mul_le_mul_right _ k
          ... = B * nat.choose n r * r                              : by rw [mul_assoc, mul_assoc, choose_lemma hr1 hr2]
end

-- @[simp] theorem div_mk_div_cancel_left {a b c : ℤ} (c0 : c ≠ 0) : (a * c) /. (b * c) = a /. b :=
theorem local_lym (n r : ℕ) (𝒜 : finset (rset r (fin n))) {hr1 : 1 ≤ r} {hr2 : r ≤ n} : 
  (finset.card 𝒜 : ℚ) / (nat.choose n r) ≤ (finset.card (shadow 𝒜)) / (nat.choose n (r-1)) := 
begin
  have: r - 1 ≤ n := le_trans (nat.pred_le r) ‹r ≤ n›,
  have: 0 < nat.choose n (r-1) := nat.choose_pos ‹r - 1 ≤ n›,
  have: 0 < nat.choose n r := nat.choose_pos ‹r ≤ n›,
  rw [div_le_iff', mul_comm, div_mul_eq_mul_div, le_div_iff]; norm_cast, rotate, 
    assumption, assumption,

  suffices: finset.card 𝒜 * r ≤ finset.card (shadow 𝒜) * (n - r + 1),
    apply le_of_mul_le_mul_right _,
    swap, exact (nat.fact r * nat.fact (n - r + 1)),
    apply mul_pos, apply nat.fact_pos, apply nat.fact_pos,
    have helper : nat.fact (r-1) * r = nat.fact r, by calc nat.fact (r-1) * r = nat.fact (r-1) * nat.succ (r-1) : sorry
                                                                          ... = nat.fact r : sorry,
    have q : finset.card 𝒜 * nat.choose n (r - 1) * (nat.fact r * nat.fact (n - r + 1)) 
          = finset.card 𝒜 * nat.choose n (r - 1) * nat.fact (r - 1) * nat.fact (n - (r - 1)) * r,
    exact (
      calc finset.card 𝒜 * nat.choose n (r - 1) * (nat.fact r * nat.fact (n - r + 1)) 
               = finset.card 𝒜 * nat.choose n (r - 1) * nat.fact r * nat.fact (n - r + 1) : by rw ← mul_assoc
           ... = finset.card 𝒜 * nat.choose n (r - 1) * (nat.fact (r - 1) * r) * nat.fact (n - (r - 1)) : by rw [helper, sub_sub_assoc ‹_› ‹_›]
           ... = finset.card 𝒜 * nat.choose n (r - 1) * nat.fact (r - 1) * nat.fact (n - (r - 1)) * r : sorry
    ),
  sorry
  -- finset.card 𝒜 * nat.choose n (r - 1) * (nat.fact r * nat.fact (n - r + 1)) ≤
  -- finset.card (shadow 𝒜) * nat.choose n r * (nat.fact r * nat.fact (n - r + 1))

  -- have: r - 1 ≤ n, rw nat.sub_le_right_iff_le_add, apply nat.le_succ_of_le ‹r ≤ n›,
  -- suffices k : rat.mk ↑(finset.card 𝒜)          ↑(nat.choose n r)        / (↑(nat.fact (r-1) * nat.fact (n-r) * r * (n-r+1))) ≤ 
  --              rat.mk ↑(finset.card (shadow 𝒜)) ↑(nat.choose n (r - 1))  / (↑(nat.fact (r-1) * nat.fact (n-r) * r * (n-r+1))),
  --   apply le_of_mul_le_mul_right k _, 
  --   rw inv_eq_one_div,
  --   apply one_div_pos_of_pos,
  --   rw ← rat.num_pos_iff_pos,
  --   rw rat.coe_nat_num, 
  --   rw int.coe_nat_pos,
  --   apply mul_pos,
  --   apply mul_pos,
  --   apply mul_pos,
  --   apply nat.fact_pos,
  --   apply nat.fact_pos,
  --   exact hr1,
  --   exact (calc n - r + 1 ≥ r - r + 1 : by simp
  --               ...       = 1         : by simp
  --               ...       > 0         : by simp),
  
  -- rw [rat.div_num_denom, rat.coe_nat_denom, rat.coe_nat_num], 


  -- rw [rat.mul_def],
  -- rw [rat.mul_def, int.coe_nat_mul.reversed, int.coe_nat_mul.reversed], 

  -- rw rat.le_def _ _, 
  --   swap, rw int.coe_nat_pos, apply nat.choose_pos ‹r ≤ n›, 
  --   swap, rw int.coe_nat_pos, apply nat.choose_pos, exact ‹r - 1 ≤ n›,
  -- rw [← int.coe_nat_mul, ← int.coe_nat_mul, int.coe_nat_le], 
  -- rw [nat.choose_eq_fact_div_fact ‹r - 1 ≤ n›, nat.choose_eq_fact_div_fact ‹r ≤ n›],
end