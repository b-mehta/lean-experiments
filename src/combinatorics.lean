import data.finset
import data.fintype
import data.fin
import data.rat

open function
open finset

variables {α : Type*} {β : Type*}
variables [fintype α] [fintype β] 

namespace fintype

theorem card_image_of_injective [decidable_eq β] {f : α → β}: injective f → finset.card ((elems α).image f) = card α :=
  finset.card_image_of_injective (elems α)

end fintype

section surj

open fintype

-- for fintypes (where we can define the image), surjection is equivalent to the image being everything

lemma univ_eq_image_of_surj [decidable_eq β] (f : α → β): surjective f → elems β = image f (elems α) := 
begin
  intro,
  ext b, rw mem_image, apply iff_of_true (complete _), 
  cases ‹surjective f› b with a ha,
  exact ⟨a, complete _, ha⟩, 
end

lemma surj_of_univ_eq_image [decidable_eq β] (f : α → β): elems β = image f (elems α) → surjective f :=
begin
  intros h b,
  have q: b ∈ elems β := complete b,
  rw h at q,
  simp at q,
  rcases q with ⟨a, _, r⟩,
  exact ⟨a, r⟩
end

lemma univ_eq_image_iff_surj [decidable_eq β] (f : α → β): elems β = image f (elems α) ↔ surjective f :=
⟨surj_of_univ_eq_image _, univ_eq_image_of_surj _⟩

-- ed's proof
-- idea: show f is injective as well, so it's bijective, so α and β have the same cardinality: contradiction 
lemma fintype.not_surjective_of_card_lt {f : α → β}
  (hcard : fintype.card α < fintype.card β) (h_surj : surjective f) : false :=
  begin
    have h_inj : injective f,
      intros a1 a2 h,
      refine @finset.inj_on_of_surj_on_of_card_le _ _ (fintype.elems α) (fintype.elems β) (λ a ha, f a)
        (λ a ha, fintype.complete _) _ (le_of_lt hcard) _ _ (fintype.complete _) (fintype.complete _) h,
      refine λ b hb, let ⟨a,ha⟩ := h_surj b in ⟨a,fintype.complete _, eq.symm ha⟩,
    apply ne_of_lt hcard,
    apply fintype.card_congr,
    apply equiv.of_bijective ⟨h_inj, h_surj⟩,
  end

-- my proof 1
-- idea: show f is injective as well, so its image is the same size as α, but it's surjective: contradiction
lemma no_surj_to_smaller_set [decidable_eq β] (hst : card α < card β) (f : α → β) : ¬ surjective f := 
begin
  intro,
  have: injective f,
    intros a1 a2 h,
    refine inj_on_of_surj_on_of_card_le (λ a _, f a) (λ _ _, mem_univ _) (λ b _, _) (le_of_lt hst) (complete _) (complete _) h,
    cases ‹surjective f› b with a _,
    exact ⟨a, complete _, ‹f a = b›.symm⟩,
  apply not_le_of_gt hst,
  rw [← card_image_of_injective ‹injective f›, ← univ_eq_image_of_surj f ‹surjective f›],
  trivial
end

-- my proof 2
-- idea: show f has an injective inverse, so the image of f⁻¹ is the same size as β, but the image is a subset of α, so card α ≥ card β
lemma ge_card_of_surj [decidable_eq α] {f : α → β} : surjective f → card β ≤ card α :=
begin
  intro,
  let f_inv := surj_inv ‹surjective f›,
  have: injective f_inv := injective_surj_inv _,
  rw ← card_image_of_injective ‹injective f_inv›,
  apply card_le_of_subset,
  apply subset_univ
end

-- apply my proof 1 to fins
lemma no_surj_to_smaller_fin (n m : ℕ) (H : n < m) (f : fin n → fin m) : ¬ surjective f :=
begin
  apply no_surj_to_smaller_set,
  repeat {rwa fintype.card_fin},
end

-- apply my proof 2 to fins
lemma no_surj_to_smaller_fin' (n m : ℕ) (H : n < m) (f : fin n → fin m) : ¬ surjective f :=
begin
  intro f_surj,
  apply not_le_of_gt H,
  rw [← fintype.card_fin m, ← fintype.card_fin n], 
  apply ge_card_of_surj f_surj,
end

-- a lemma which might want to belong somewhere (effectively used in my proof 2)
lemma no_inj_to_smaller_set [decidable_eq β] (H : card β < card α) (f : α → β) : ¬ injective f :=
begin
  intro f_inj,
  have := card_image_of_injective f_inj,
  apply not_le_of_gt H,
  rw ← this,
  apply card_le_of_subset,
  apply subset_univ
end

end surj