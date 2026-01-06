import Mathlib.Data.List.Sort
import Mathlib.Data.List.Count

#check List.mergeSort
#check List.mergeSort_perm
#check List.Perm.count_eq
#check List.Sorted
#check List.Sorted.rel_get_of_le -- guessing
#check List.Sorted.rel_of_mem_take_of_mem_drop
#check List.map_eq_nil

example (l : List ℕ) : l.mergeSort (· ≤ ·) = l.sort (· ≤ ·) := rfl -- check if sort is mergeSort
