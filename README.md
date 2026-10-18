# sortedmap

A finite map from `Nat` keys to any value type for Lean 4, with its correctness proved. Entries live in an association list kept strictly sorted by key. The sortedness proof is part of the value, so a `SortedMap α` can never be malformed. Every operation comes with the lemma that says what it does to `find?`, and two maps that agree on every key are equal.

    import SortedMap
    open SortedMap

    def prices : SortedMap String :=
      fromList [(42, "mug"), (7, "pen"), (19, "shirt")]

    #eval prices.find? 19          -- some "shirt"
    #eval prices.keys              -- [7, 19, 42]
    #eval (prices.erase 7).size    -- 2

## API

    empty                 the map with nothing in it
    insert m k v          add or replace
    erase m k             remove, a no-op when the key is absent
    find? m k             Option α
    findD m k default     the value, or default
    contains m k          Bool
    modify m k d f        insert (f (findD m k d)), handy for counting
    size, keys, toList    keys and toList come out in increasing key order
    fromList l            insert left to right, later pairs win

## What is proved

The specification is in terms of `find?`:

    find_insert : (m.insert k v).find? k' = if k' = k then some v else m.find? k'
    find_erase  : (m.erase k).find? k'  = if k' = k then none   else m.find? k'
    find_empty  : empty.find? k = none

and extensionality:

    ext : (∀ k, m₁.find? k = m₂.find? k) → m₁ = m₂

Extensionality is what makes the type pleasant to use. Laws like `insert_comm`, `insert_insert_same`, `erase_insert_same` and `erase_of_find_none` are each a few lines: apply `ext`, rewrite with `find_insert` and `find_erase`, split on the key. Also proved: keys are strictly increasing and have no duplicates, insert grows the size by at most one, erase never grows it.

The proofs live in `SortedMap/Basic.lean` and work on plain lists. The `ext` proof is the interesting one. Two sorted lists with the same lookups must have the same head. Otherwise the smaller head key is found in one list and not the other. After that the tails agree on every key, by the sortedness of both.

## Build and test

    lake build

`Tests.lean` is a set of `#guard` commands, so a failing test fails the build. The audit tool [proofwatch](https://github.com/yashpalnehra/proofwatch) reports 35 theorems in the `SortedMap` module with no `sorry` and nothing beyond the standard axioms.

Lean 4.35.0, no dependencies beyond core.
