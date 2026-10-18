import SortedMap.Basic

/-!
The map type and its API. Every operation carries its invariant proof, and every lemma
a caller might want is stated here in terms of `find?`.
-/

/-- A map from `Nat` to `α`: a sorted association list with its proof. -/
structure SortedMap (α : Type) where
  entries : List (Nat × α)
  sorted : SortedMap.Sorted entries

namespace SortedMap

variable {α : Type}

def empty : SortedMap α := ⟨[], List.Pairwise.nil⟩

instance : EmptyCollection (SortedMap α) := ⟨empty⟩
instance : Inhabited (SortedMap α) := ⟨empty⟩

def find? (m : SortedMap α) (k : Nat) : Option α := findEntries k m.entries

def contains (m : SortedMap α) (k : Nat) : Bool := (m.find? k).isSome

def insert (m : SortedMap α) (k : Nat) (v : α) : SortedMap α :=
  ⟨insertEntries k v m.entries, sorted_insertEntries k v m.sorted⟩

def erase (m : SortedMap α) (k : Nat) : SortedMap α :=
  ⟨eraseEntries k m.entries, sorted_eraseEntries k m.sorted⟩

def size (m : SortedMap α) : Nat := m.entries.length

def keys (m : SortedMap α) : List Nat := m.entries.map (·.1)

def toList (m : SortedMap α) : List (Nat × α) := m.entries

def fromList (l : List (Nat × α)) : SortedMap α :=
  l.foldl (fun m (k, v) => m.insert k v) empty

def findD (m : SortedMap α) (k : Nat) (default : α) : α := (m.find? k).getD default

/-- Apply a function to the value at `k`, inserting `default` first if the key is absent. -/
def modify (m : SortedMap α) (k : Nat) (default : α) (f : α → α) : SortedMap α :=
  m.insert k (f (m.findD k default))

instance [Repr α] : Repr (SortedMap α) where
  reprPrec m _ := "SortedMap.fromList " ++ repr m.entries

/-! ### The specification -/

@[simp] theorem find_empty (k : Nat) : (empty : SortedMap α).find? k = none := rfl

@[simp] theorem find_insert_same (m : SortedMap α) (k : Nat) (v : α) :
    (m.insert k v).find? k = some v :=
  findEntries_insert_same k v m.entries

theorem find_insert_other (m : SortedMap α) {k k' : Nat} (v : α) (h : k' ≠ k) :
    (m.insert k v).find? k' = m.find? k' :=
  findEntries_insert_other v m.entries h

theorem find_insert (m : SortedMap α) (k k' : Nat) (v : α) :
    (m.insert k v).find? k' = if k' = k then some v else m.find? k' := by
  split
  · rename_i h; subst h; exact find_insert_same m k' v
  · rename_i h; exact find_insert_other m v h

@[simp] theorem find_erase_same (m : SortedMap α) (k : Nat) : (m.erase k).find? k = none :=
  findEntries_erase_same k m.sorted

theorem find_erase_other (m : SortedMap α) {k k' : Nat} (h : k' ≠ k) :
    (m.erase k).find? k' = m.find? k' :=
  findEntries_erase_other m.sorted h

theorem find_erase (m : SortedMap α) (k k' : Nat) :
    (m.erase k).find? k' = if k' = k then none else m.find? k' := by
  split
  · rename_i h; subst h; exact find_erase_same m k'
  · rename_i h; exact find_erase_other m h

theorem contains_iff (m : SortedMap α) (k : Nat) : m.contains k = true ↔ ∃ v, m.find? k = some v := by
  simp [contains, Option.isSome_iff_exists]

theorem findD_eq (m : SortedMap α) (k : Nat) (d : α) :
    m.findD k d = match m.find? k with | some v => v | none => d := by
  unfold findD
  cases m.find? k <;> rfl

/-- Two maps that agree on every key are equal. -/
theorem ext {m₁ m₂ : SortedMap α} (h : ∀ k, m₁.find? k = m₂.find? k) : m₁ = m₂ := by
  obtain ⟨l₁, h₁⟩ := m₁
  obtain ⟨l₂, h₂⟩ := m₂
  have := ext_entries h₁ h₂ h
  subst this
  rfl

theorem ext_iff {m₁ m₂ : SortedMap α} : m₁ = m₂ ↔ ∀ k, m₁.find? k = m₂.find? k :=
  ⟨fun h _ => h ▸ rfl, ext⟩

/-! Algebraic laws, each a few lines through `ext`. -/

theorem insert_insert_same (m : SortedMap α) (k : Nat) (v w : α) :
    (m.insert k v).insert k w = m.insert k w := by
  apply ext
  intro k'
  rw [find_insert, find_insert, find_insert]
  split <;> rfl

theorem insert_comm (m : SortedMap α) {k₁ k₂ : Nat} (v₁ v₂ : α) (h : k₁ ≠ k₂) :
    (m.insert k₁ v₁).insert k₂ v₂ = (m.insert k₂ v₂).insert k₁ v₁ := by
  apply ext
  intro k
  rw [find_insert, find_insert, find_insert, find_insert]
  by_cases h₁ : k = k₁ <;> by_cases h₂ : k = k₂ <;> simp_all

theorem erase_insert_same (m : SortedMap α) (k : Nat) (v : α) :
    (m.insert k v).erase k = m.erase k := by
  apply ext
  intro k'
  rw [find_erase, find_erase, find_insert]
  split <;> simp_all

theorem insert_erase_same (m : SortedMap α) (k : Nat) (v : α) :
    (m.erase k).insert k v = m.insert k v := by
  apply ext
  intro k'
  rw [find_insert, find_insert, find_erase]
  split <;> simp_all

theorem erase_erase (m : SortedMap α) (k : Nat) : (m.erase k).erase k = m.erase k := by
  apply ext
  intro k'
  rw [find_erase, find_erase]
  split <;> rfl

theorem erase_empty (k : Nat) : (empty : SortedMap α).erase k = empty := by
  apply ext
  intro k'
  rw [find_erase]
  split <;> rfl

/-- Erasing an absent key changes nothing. -/
theorem erase_of_find_none (m : SortedMap α) {k : Nat} (h : m.find? k = none) : m.erase k = m := by
  apply ext
  intro k'
  rw [find_erase]
  split
  · rename_i hk; subst hk; exact h.symm
  · rfl

/-- Inserting the value already there changes nothing. -/
theorem insert_of_find_some (m : SortedMap α) {k : Nat} {v : α} (h : m.find? k = some v) :
    m.insert k v = m := by
  apply ext
  intro k'
  rw [find_insert]
  split
  · rename_i hk; subst hk; exact h.symm
  · rfl

/-! Keys and size. -/

theorem keys_sorted (m : SortedMap α) : m.keys.Pairwise (· < ·) := by
  unfold keys
  exact List.Pairwise.map _ (fun _ _ h => h) m.sorted

theorem keys_nodup (m : SortedMap α) : m.keys.Nodup :=
  (keys_sorted m).imp Nat.ne_of_lt

theorem size_insert_le (m : SortedMap α) (k : Nat) (v : α) : (m.insert k v).size ≤ m.size + 1 := by
  unfold size insert
  simp only
  generalize m.entries = l
  induction l with
  | nil => simp [insertEntries]
  | cons p rest ih =>
    obtain ⟨k', v'⟩ := p
    simp only [insertEntries]
    split
    · simp
    · split
      · simp
      · simp only [List.length_cons]
        omega

theorem size_erase_le (m : SortedMap α) (k : Nat) : (m.erase k).size ≤ m.size :=
  (eraseEntries_sublist k m.entries).length_le

end SortedMap
