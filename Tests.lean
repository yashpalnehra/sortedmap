import SortedMap

/-!
Tests. The lemmas cover all maps, so these check concrete behaviour and the parts with
no proof attached, such as `fromList`, `modify` and `Repr`. `#guard` fails the build.
-/

open SortedMap

def m : SortedMap String :=
  fromList [(5, "five"), (1, "one"), (3, "three"), (1, "uno")]

#guard m.toList == [(1, "uno"), (3, "three"), (5, "five")]
#guard m.keys == [1, 3, 5]
#guard m.size == 3
#guard m.find? 3 == some "three"
#guard m.find? 1 == some "uno"
#guard m.find? 4 == none
#guard m.contains 5
#guard !m.contains 2
#guard m.findD 2 "?" == "?"

#guard (m.insert 4 "four").keys == [1, 3, 4, 5]
#guard (m.insert 0 "zero").keys == [0, 1, 3, 5]
#guard (m.insert 9 "nine").keys == [1, 3, 5, 9]
#guard (m.insert 3 "tres").find? 3 == some "tres"
#guard (m.insert 3 "tres").size == 3

#guard (m.erase 3).keys == [1, 5]
#guard (m.erase 1).keys == [3, 5]
#guard (m.erase 5).keys == [1, 3]
#guard (m.erase 7).keys == [1, 3, 5]
#guard ((m.erase 3).erase 3).size == 2

#guard (empty : SortedMap Nat).size == 0
#guard (empty : SortedMap Nat).find? 0 == none

/-! counting words with modify -/

def counts : SortedMap Nat :=
  [3, 1, 3, 3, 7, 1].foldl (fun acc w => acc.modify w 0 (· + 1)) empty

#guard counts.toList == [(1, 2), (3, 3), (7, 1)]

/-! a map of 1000 keys inserted in reverse order comes out sorted -/

def big : SortedMap Nat := (List.range 1000).reverse.foldl (fun acc k => acc.insert k (k * k)) empty

#guard big.size == 1000
#guard big.keys == List.range 1000
#guard big.find? 999 == some 998001
#guard (big.erase 500).size == 999

#guard toString (repr (fromList [(2, 'b'), (1, 'a')])) == "SortedMap.fromList [(1, 'a'), (2, 'b')]"

/-! the laws, instantiated, as a smoke test that the statements are the intended ones -/

example : (m.insert 3 "x").find? 3 = some "x" := find_insert_same m 3 "x"
example : (m.insert 3 "x").find? 5 = m.find? 5 := find_insert_other m "x" (by decide)
example : (m.erase 3).find? 3 = none := find_erase_same m 3
example : (m.insert 1 "a").insert 1 "b" = m.insert 1 "b" := insert_insert_same m 1 "a" "b"
