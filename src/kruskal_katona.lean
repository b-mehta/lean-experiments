import data.finset
import data.fin
import data.rat
import data.nat.basic
import data.fintype

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
  refine ⟨insert s (A.1), _⟩,
  rw finset.mem_powerset_len,
  cases A with a b, 
  rw finset.mem_powerset_len at b,
  cases b,
  refine ⟨finset.insert_subset.2 ⟨complete _, _⟩, _⟩,
    simpa,
  rw finset.card_insert_of_not_mem h,
  congr, 
  rw b_right,
end

lemma mem_stretch (A : rset r X) (s : X) {h : s ∉ A} (i : X) : i ∈ stretch A s h ↔ i ∈ A ∨ i = s := 
by rw [stretch, finset.mem_insert]; tauto

lemma stretch_subset {A : rset r X} {s : X} (h : s ∉ A) : A.1 ⊆ (stretch A s h).1 := 
finset.subset_insert _ _

def erase (A : rset r X) (s : X) (h : s ∈ A) : rset (r-1) X :=
begin
  use (finset.erase (A.1) s),
  rw finset.mem_powerset_len,
  split,
    apply finset.subset_univ,
  rw finset.card_erase_of_mem h,
  rw card_of_rset A,
  trivial
end

lemma mem_erase (A : rset r X) (s : X) (h : s ∈ A) (i : X) : i ∈ erase A s h ↔ i ∈ A ∧ i ≠ s :=
by rw [erase, finset.mem_erase]; tauto

lemma subset_erase {A : rset r X} {s : X} (h : s ∈ A) : (erase A s h).1 ⊆ A.1 :=
finset.erase_subset _ _

lemma erase_iff_stretch (A : rset r X) (B : rset (r+1) X) (s : X) (H1 : s ∉ A) (H2 : s ∈ B) : B = stretch A s H1 ↔ A = erase B s H2 :=
begin
  split; intros p; ext, 
    rw mem_erase,
    split; intro k,
      split,
        exact (p.symm ▸ stretch_subset ‹_› k),
      intro, rw ‹a = s› at k, tauto,
    rw [p, mem_stretch] at k,
    tauto,
  rw mem_stretch,
  split; intro x,
    rw [p, mem_erase], 
    by_cases (a = s),
      right, assumption,
    left,
    exact ⟨‹_›, ‹_›⟩,
  cases x,
    rw p at x,
    exact (subset_erase ‹_› x),
  rwa x
end

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
  rintros ⟨x1, x1p⟩ ⟨x2, x2p⟩ q,
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

-- #check example1.1

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

lemma thingy2 (A : finset X) (B : finset X) : A ∪ (B \ A) = B ∪ (A \ B) :=
by rw [thingy, thingy, finset.union_comm]

lemma thingy3 (A : finset X) (B : finset X) : A \ B = ∅ ↔ A ⊆ B :=
by simp [finset.ext, finset.subset_iff]

lemma thingy5 (A : finset X) : (∃ x, A = finset.singleton x) ↔ (∃! x, x ∈ A) := 
begin
  split; rintro ⟨x, t⟩; use x,
    rw t, 
    refine ⟨finset.mem_singleton_self _, λ i, finset.mem_singleton.1⟩, 
  ext, rw finset.mem_singleton, 
  exact ⟨λ r, t.right _ r, λ r, r.symm ▸ t.left⟩
end

lemma thingy4 (A : finset X) : finset.card A = 1 ↔ ∃! x, x ∈ A :=
by rw [← thingy5, finset.card_eq_one]

lemma test {A : rset r X} {B : rset (r+1) X} : finset.card (B.1 \ A.1) = 1 ↔ cube_graph A B := 
begin
  rw cube_graph,
  have : A.1 ∪ (B.1 \ A.1) = B.1 ∪ (A.1 \ B.1), 
    rw [thingy, thingy, finset.union_comm], 
  have : finset.card A.1 + finset.card (B.1 \ A.1) = finset.card B.1 + finset.card (A.1 \ B.1),
    rw [← finset.card_disjoint_union (finset.disjoint_sdiff), ← finset.card_disjoint_union (finset.disjoint_sdiff)], 
    rw this,
  rw [card_of_rset, card_of_rset] at this,
  simp at this,
  rw this,
  transitivity (finset.card (A.1 \ B.1) = 0),
    split; intro p,
      apply add_left_cancel, assumption,
    rw p,
  simp [thingy3]
end

lemma stretch_iff_related (A : rset r X) (B : rset (r+1) X) : cube_graph A B ↔ ∃ (i ∉ A), stretch A i H = B := 
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

-- lemma cube_rel {r : ℕ} (A : rset r X) (B : rset (r+1) X) : 
--   cube_graph A B ↔ ∃ (x : X) (H : x ∉ A), stretch A x H = B := 
-- begin
--   rw cube_graph, simp, rw finset.card_eq_one, split; rintro ⟨x, h⟩; use x,
--     rw finset.ext at h, simp at h,
    
--   -- rw cube_graph, simp, rw finset.card_eq_one, split; rintro ⟨x, h⟩; use x,
--   --   rw finset.ext at h, simp at h, 
--   --   have q : x ∈ B ∧ x ∉ A := (h x).2 rfl, 
--   --   use q.2,
--   --   ext,
--   --   rw mem_stretch, 
--   --   split; intro p,
--   --     cases p,
--   --       sorry,
--   --     rw p, exact q.1,
--   --   sorry,
--   -- cases h with h m, ext t, rw [finset.mem_singleton, finset.mem_sdiff], split; intro p,
--   --   cases p, rw [← m, mem_stretch] at p_left, tauto,
--   -- rw p, refine ⟨_, h⟩,
--   -- rw ← m, rw mem_stretch, right, refl
-- end

theorem local_lym (n : ℕ) (r : ℕ) (𝒜 : finset (rset r (fin n))) {hr1 : 1 ≤ r} {hr2 : r ≤ n} : 
  rat.mk (finset.card 𝒜) (nat.choose n r) ≤ rat.mk (finset.card (shadow 𝒜)) (nat.choose n (r-1)) := 
begin
  sorry
end