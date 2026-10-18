/-!
A finite map from `Nat` keys to values of any type, stored as an association list kept
strictly sorted by key. Sorted means lookup can stop early, there are never duplicate
keys, and two maps with the same contents are the same list, which gives extensionality.

The invariant is part of the type: a `SortedMap α` is a list together with a proof that
its keys strictly increase, so a value of the type is always well formed.
-/

namespace SortedMap

/-- Keys strictly increase along the list. -/
abbrev Sorted (l : List (Nat × α)) : Prop := l.Pairwise fun p q => p.1 < q.1

/-! ### The list-level operations -/

def findEntries (k : Nat) : List (Nat × α) → Option α
  | [] => none
  | (k', v) :: rest =>
    if k = k' then some v
    -- sorted, so once the keys pass k the answer is none
    else if k < k' then none
    else findEntries k rest

def insertEntries (k : Nat) (v : α) : List (Nat × α) → List (Nat × α)
  | [] => [(k, v)]
  | (k', v') :: rest =>
    if k = k' then (k, v) :: rest
    else if k < k' then (k, v) :: (k', v') :: rest
    else (k', v') :: insertEntries k v rest

def eraseEntries (k : Nat) : List (Nat × α) → List (Nat × α)
  | [] => []
  | (k', v') :: rest =>
    if k = k' then rest
    else if k < k' then (k', v') :: rest
    else (k', v') :: eraseEntries k rest

/-! ### Lookup facts -/

/-- Nothing is found below every key of the list. -/
theorem findEntries_eq_none_of_lt {k : Nat} {l : List (Nat × α)} (h : ∀ p ∈ l, k < p.1) :
    findEntries k l = none := by
  cases l with
  | nil => rfl
  | cons p rest =>
    obtain ⟨k', v'⟩ := p
    have hk : k < k' := h (k', v') (List.mem_cons_self ..)
    simp [findEntries, Nat.ne_of_lt hk, hk]

theorem findEntries_insert_same (k : Nat) (v : α) (l : List (Nat × α)) :
    findEntries k (insertEntries k v l) = some v := by
  induction l with
  | nil => simp [insertEntries, findEntries]
  | cons p rest ih =>
    obtain ⟨k', v'⟩ := p
    simp only [insertEntries]
    split
    · simp [findEntries]
    · split
      · simp [findEntries]
      · rename_i hne hnlt
        simp [findEntries, hne, hnlt, ih]

theorem findEntries_insert_other {k k' : Nat} (v : α) (l : List (Nat × α)) (hne : k' ≠ k) :
    findEntries k' (insertEntries k v l) = findEntries k' l := by
  induction l with
  | nil => simp [insertEntries, findEntries, hne]
  | cons p rest ih =>
    obtain ⟨k₁, v₁⟩ := p
    simp only [insertEntries]
    split
    · rename_i heq
      subst heq
      simp [findEntries, hne]
    · split
      · rename_i hlt
        by_cases hlt' : k' < k
        · have : k' ≠ k₁ := Nat.ne_of_lt (Nat.lt_trans hlt' hlt)
          have : k' < k₁ := Nat.lt_trans hlt' hlt
          simp [findEntries, *]
        · simp [findEntries, hne, hlt']
      · by_cases h₁ : k' = k₁
        · simp [findEntries, h₁]
        · by_cases h₂ : k' < k₁
          · simp [findEntries, h₁, h₂]
          · simp [findEntries, h₁, h₂, ih]

theorem findEntries_erase_same (k : Nat) {l : List (Nat × α)} (hs : Sorted l) :
    findEntries k (eraseEntries k l) = none := by
  induction l with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨k', v'⟩ := p
    replace hs := List.pairwise_cons.1 hs
    simp only [eraseEntries]
    split
    · rename_i heq
      subst heq
      exact findEntries_eq_none_of_lt hs.1
    · split
      · rename_i hne hlt
        simp [findEntries, hne, hlt]
      · rename_i hne hnlt
        simp [findEntries, hne, hnlt, ih hs.2]

theorem findEntries_erase_other {k k' : Nat} {l : List (Nat × α)} (hs : Sorted l) (hne : k' ≠ k) :
    findEntries k' (eraseEntries k l) = findEntries k' l := by
  induction l with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨k₁, v₁⟩ := p
    replace hs := List.pairwise_cons.1 hs
    simp only [eraseEntries]
    split
    · rename_i heq
      subst heq
      by_cases hlt : k' < k
      · rw [findEntries_eq_none_of_lt (fun p hp => Nat.lt_trans hlt (hs.1 p hp))]
        simp [findEntries, hne, hlt]
      · simp [findEntries, hne, hlt]
    · split
      · rfl
      · by_cases h₁ : k' = k₁
        · simp [findEntries, h₁]
        · by_cases h₂ : k' < k₁
          · simp [findEntries, h₁, h₂]
          · simp [findEntries, h₁, h₂, ih hs.2]

/-! ### The invariant survives -/

theorem mem_insertEntries {k : Nat} {v : α} {l : List (Nat × α)} {p : Nat × α}
    (h : p ∈ insertEntries k v l) : p = (k, v) ∨ p ∈ l := by
  induction l with
  | nil => simp [insertEntries] at h; exact Or.inl h
  | cons q rest ih =>
    obtain ⟨k', v'⟩ := q
    simp only [insertEntries] at h
    split at h
    · rcases List.mem_cons.1 h with rfl | h
      · exact Or.inl rfl
      · exact Or.inr (List.mem_cons_of_mem _ h)
    · split at h
      · rcases List.mem_cons.1 h with rfl | h
        · exact Or.inl rfl
        · exact Or.inr h
      · rcases List.mem_cons.1 h with rfl | h
        · exact Or.inr (List.mem_cons_self ..)
        · rcases ih h with h | h
          · exact Or.inl h
          · exact Or.inr (List.mem_cons_of_mem _ h)

theorem sorted_insertEntries (k : Nat) (v : α) {l : List (Nat × α)} (hs : Sorted l) :
    Sorted (insertEntries k v l) := by
  induction l with
  | nil => simp [insertEntries]
  | cons p rest ih =>
    obtain ⟨k', v'⟩ := p
    replace hs := List.pairwise_cons.1 hs
    simp only [insertEntries]
    split
    · rename_i heq
      subst heq
      exact List.pairwise_cons.2 hs
    · split
      · rename_i hne hlt
        refine List.pairwise_cons.2 ⟨?_, List.pairwise_cons.2 hs⟩
        intro q hq
        rcases List.mem_cons.1 hq with rfl | hq
        · exact hlt
        · exact Nat.lt_trans hlt (hs.1 q hq)
      · rename_i hne hnlt
        refine List.pairwise_cons.2 ⟨?_, ih hs.2⟩
        intro q hq
        rcases mem_insertEntries hq with rfl | hq
        · exact Nat.lt_of_le_of_ne (Nat.le_of_not_lt hnlt) (Ne.symm hne)
        · exact hs.1 q hq

theorem eraseEntries_sublist (k : Nat) (l : List (Nat × α)) : (eraseEntries k l).Sublist l := by
  induction l with
  | nil => exact List.Sublist.refl _
  | cons p rest ih =>
    obtain ⟨k', v'⟩ := p
    simp only [eraseEntries]
    split
    · exact List.sublist_cons_self _ _
    · split
      · exact List.Sublist.refl _
      · exact ih.cons_cons _

theorem sorted_eraseEntries (k : Nat) {l : List (Nat × α)} (hs : Sorted l) :
    Sorted (eraseEntries k l) :=
  hs.sublist (eraseEntries_sublist k l)

/-! ### Extensionality -/

theorem findEntries_head {k : Nat} {v : α} {l : List (Nat × α)} :
    findEntries k ((k, v) :: l) = some v := by
  simp [findEntries]

/-- Two sorted lists that agree on every lookup are equal. -/
theorem ext_entries {l₁ l₂ : List (Nat × α)} (h₁ : Sorted l₁) (h₂ : Sorted l₂)
    (h : ∀ k, findEntries k l₁ = findEntries k l₂) : l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => rfl
    | cons p rest =>
      obtain ⟨k, v⟩ := p
      have := h k
      rw [findEntries_head] at this
      cases this
  | cons p rest ih =>
    obtain ⟨k₁, v₁⟩ := p
    cases l₂ with
    | nil =>
      have := h k₁
      rw [findEntries_head] at this
      cases this
    | cons q rest₂ =>
      obtain ⟨k₂, v₂⟩ := q
      replace h₁ := List.pairwise_cons.1 h₁
      replace h₂ := List.pairwise_cons.1 h₂
      -- the heads must have the same key, or one lookup finds nothing
      have hk : k₁ = k₂ := by
        rcases Nat.lt_trichotomy k₁ k₂ with hlt | heq | hgt
        · have := h k₁
          rw [findEntries_head] at this
          simp [findEntries, Nat.ne_of_lt hlt, hlt] at this
        · exact heq
        · have := h k₂
          rw [findEntries_head] at this
          have hne : k₂ ≠ k₁ := Nat.ne_of_lt hgt
          simp [findEntries, hne, hgt] at this
      subst hk
      have hv : v₁ = v₂ := by
        have := h k₁
        rw [findEntries_head, findEntries_head] at this
        exact Option.some.inj this
      subst hv
      congr
      apply ih h₁.2 h₂.2
      intro k
      by_cases hle : k ≤ k₁
      · -- below the head key both tails are empty for k
        rw [findEntries_eq_none_of_lt (fun p hp => Nat.lt_of_le_of_lt hle (h₁.1 p hp)),
          findEntries_eq_none_of_lt (fun p hp => Nat.lt_of_le_of_lt hle (h₂.1 p hp))]
      · have hne : k ≠ k₁ := fun heq => hle (heq ▸ Nat.le_refl _)
        have hnlt : ¬k < k₁ := fun hlt => hle (Nat.le_of_lt hlt)
        have := h k
        simpa [findEntries, hne, hnlt] using this

end SortedMap
