import data.finset
import data.fintype

open fintype
open finset

variable {n : ℕ} 
local notation `X` := fin n

def compress_family (U V : finset X) (𝒜 : finset (finset X)) : finset (finset X) := sorry

lemma compressed_size (U V : finset X) (𝒜 : finset (finset X)) : (compress_family U V 𝒜).card = 𝒜.card := sorry

def shadow (𝒜 : finset (finset X)) : finset (finset X) := sorry

reserve prefix `∂`:90
notation ∂𝒜 := shadow 𝒜

def is_compressed (U V : finset X) (𝒜 : finset (finset X)) : Prop := compress_family U V 𝒜 = 𝒜

lemma is_compressed_empty (𝒜 : finset (finset X)) : is_compressed ∅ ∅ 𝒜 := sorry

lemma compression_reduces_shadow (U V : finset X) (𝒜 : finset (finset X)) 
  (h₁ : ∀ x ∈ U, ∃ y ∈ V, is_compressed (erase U x) (erase V y) 𝒜) (h₂ : U.card = V.card) : 
  (∂ compress_family U V 𝒜).card ≤ (∂𝒜).card := sorry

def c_measure (𝒜 : finset (finset X)) : ℕ := sorry

def compression_reduces_measure (U V : finset X) (hU : U ≠ ∅) (hV : V ≠ ∅) (h : max' U hU < max' V hV) (𝒜 : finset (finset X)) : 
  compress_family U V 𝒜 ≠ 𝒜 → c_measure (compress_family U V 𝒜) < c_measure 𝒜 := sorry

def gamma : rel (finset X) (finset X) := (λ U V, ∃ (HU : U ≠ ∅), ∃ (HV : V ≠ ∅), disjoint U V ∧ finset.card U = finset.card V ∧ max' U HU < max' V HV)

lemma compression_improved (U V : finset X) (𝒜 : finset (finset X)) (h₁ : gamma U V) 
  (h₂ : ∀ U₁ V₁, gamma U₁ V₁ ∧ U₁.card < U.card → is_compressed U₁ V₁ 𝒜) (h₃ : ¬ is_compressed U V 𝒜): 
  c_measure (compress_family U V 𝒜) < c_measure 𝒜 ∧ (compress_family U V 𝒜).card = 𝒜.card ∧ (∂ compress_family U V 𝒜).card ≤ (∂𝒜).card := sorry

theorem kruskal_katona_helper (𝒜 : finset (finset X)) : ∃ (ℬ : finset (finset X)), 𝒜.card = ℬ.card ∧ (∂ℬ).card ≤ (∂𝒜).card ∧ (∀ U V, gamma U V → is_compressed U V ℬ) := 
sorry