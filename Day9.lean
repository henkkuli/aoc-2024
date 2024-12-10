import Mathlib
import Aoc2024
import Std.Internal.Parsec

open Std.Internal.Parsec
open Std.Internal.Parsec.String

def parser : Parser (List Nat) :=
  Array.toList <$> many ((fun c => c.toNat - '0'.toNat) <$> digit) <* pchar '\n' <* eof

def Subarray.popLast? (as : Subarray α) : Option (α × Subarray α) :=
  if h : as.start < as.stop then
    have := Nat.sub_one_lt_of_le (Nat.zero_lt_of_lt h) as.stop_le_array_size
    let last := as.array[as.stop-1]
    let rest := { as with
      stop := as.stop-1,
      start_le_stop := by exact Nat.le_sub_one_of_lt h,
      stop_le_array_size := Nat.le_of_lt this
    }
    some ⟨last, rest⟩
  else
    none

def Subarray.popLast (as : Subarray α) (h : as.size > 0) : α × Subarray α :=
  let r := as.popLast?
  have : r.isSome := by
    unfold r Subarray.popLast?
    split
    case isTrue => rfl
    case isFalse h' => simp_all only [Subarray.size, tsub_pos_iff_lt]
  r.get this

def Subarray.popHead (as : Subarray α) (h : as.size > 0) : α × Subarray α :=
  let r := as.popHead?
  have : r.isSome := by
    unfold r Subarray.popHead?
    split
    case isTrue => rfl
    case isFalse h' => simp_all only [Subarray.size, tsub_pos_iff_lt]
  r.get this

theorem Subarray.length_popHead? (as : Subarray α) : (as.popHead?.map (·.snd.size)).getD 0 = as.size - 1 := by
  unfold Subarray.popHead?
  split
  case isTrue h => rfl
  case isFalse h => simp_all only [Subarray.size, not_lt, Option.map_none', Option.getD_none, Nat.sub_eq_zero_of_le]


theorem Subarray.length_popHead (as : Subarray α) {h : as.size > 0} : (as.popHead h).snd.size = as.size - 1 := by
  simp_all [Subarray.popHead, Subarray.popHead?, Subarray.size]
  rfl

theorem Subarray.length_popLast? (as : Subarray α) : (as.popLast?.map (·.snd.size)).getD 0 = as.size - 1 := by
  unfold Subarray.popLast?
  split
  case isTrue h => exact Nat.sub_right_comm as.stop 1 as.start
  case isFalse h => simp_all only [Subarray.size, not_lt, Option.map_none', Option.getD_none, Nat.sub_eq_zero_of_le]

theorem Subarray.length_popLast (as : Subarray α) {h : as.size > 0} : (as.popLast h).snd.size = as.size - 1 := by
  simp_all [Subarray.popLast, Subarray.popLast?, Subarray.size]
  exact Nat.sub_right_comm as.stop 1 as.start

def part1 (l : List Nat) : Nat :=
  let rec takeAllocated : List Nat → List Nat
  | [] => []
  | x :: [] => [x]
  | x :: _ :: xs => x :: takeAllocated xs

  let fileBlocks := (takeAllocated l |>.enum |>.flatMap fun ⟨id, len⟩ => List.replicate len id).toArray

  let rec loop (fileBlocks : Subarray Nat) (l : List Nat) : List Nat :=
    if h : fileBlocks.size > 0 then
      match l with
      | [] => []        -- We shouldn't really reach this ever
      | _ :: [] => []   -- There's a final file with no space after. The file should have already been allocated
      | 0 :: 0 :: xs => loop fileBlocks xs  -- Block has been filled
      | 0 :: (k+1) :: xs => -- Fill one item from the back
          let ⟨id, rest⟩ := fileBlocks.popLast h
          id :: loop rest (0 :: k :: xs)
      | (k+1) :: y :: xs => -- Fill one item from the front, namely the one that was already there
        let ⟨id, rest⟩ := fileBlocks.popHead h
        id :: loop rest (k :: y :: xs)
    else
      []

  let allocated := loop fileBlocks.toSubarray l
  allocated |>.enum |>.map (Function.uncurry (· * ·)) |>.sum

def findLastFitting (tlen : Nat) : List (Option Nat × Nat) → Option (Nat × Nat × List (Option Nat × Nat))
| [] => none
| (none, len) :: xs => findLastFitting tlen xs |>.map fun (a, b, tail) => (a, b, (none, len) :: tail)
| (some id, len) :: xs =>
  if let some (a, b, tail) := findLastFitting tlen xs then
    some (a, b, (id, len) :: tail)
  else
    if 0 < len ∧ len ≤ tlen then
      some (id, len, (none, len) :: xs)
    else
      none

theorem length_findLastFitting (tlen : Nat) : (l : List (Option Nat × Nat)) → (h : (findLastFitting tlen l).isSome) → ((findLastFitting tlen l).get h).snd.snd.length = l.length
| [], h => by simp [findLastFitting, Option.isSome] at h
| (none, len) :: xs, h => by
  by_cases h' : (findLastFitting tlen xs).isSome
  case pos =>
    have ih := length_findLastFitting tlen xs h'
    simpa [findLastFitting, Option.get_map, List.length_cons]
  case neg =>
    simp [findLastFitting,  Option.not_isSome_iff_eq_none.mp h'] at h

| (some id, len) :: xs, h => by
  unfold findLastFitting
  let flfxs := findLastFitting tlen xs
  cases hf : flfxs
  case some val =>
    unfold flfxs at hf
    have ih := length_findLastFitting tlen xs (by simp_all)
    simp_rw [hf, Option.get_some] at ih
    simp [hf, ih]
  case none =>
    unfold flfxs at hf
    simp [hf]

theorem len_sum_findLastFitting (tlen : Nat) : (l : List (Option Nat × Nat)) → (h : (findLastFitting tlen l).isSome) → (List.map (·.snd) <| List.filter (·.fst.isSome) ((findLastFitting tlen l).get h).snd.snd).sum < (List.map (·.snd) <| List.filter (·.fst.isSome) l).sum
| [], h => by simp [findLastFitting, Option.isSome] at h
| (none, len) :: xs, h => by
  by_cases h' : (findLastFitting tlen xs).isSome
  case pos =>
    simp only [findLastFitting, Option.get_map, List.map_cons, List.sum_cons, add_lt_add_iff_left]
    exact len_sum_findLastFitting tlen xs h'
  case neg =>
    simp [findLastFitting,  Option.not_isSome_iff_eq_none.mp h'] at h

| (some id, len) :: xs, h => by
  unfold findLastFitting
  let flfxs := findLastFitting tlen xs
  cases hf : flfxs
  case some val =>
    unfold flfxs at hf
    have ih := len_sum_findLastFitting tlen xs (by simp_all)
    simp_rw [hf, Option.get_some] at ih
    simp [hf, ih]
  case none =>
    unfold flfxs at hf
    simp_rw [hf]
    cases len
    case zero => simp [findLastFitting, hf] at h
    case succ => simp

def part2 (l : List Nat) : Nat :=
  let rec attachId : Nat → List Nat → List (Option Nat × Nat)
  | _id, [] => []
  | id, x :: [] => [(id, x)]
  | id, x :: y :: tail => (some id, x) :: (none, y) :: attachId (id + 1) tail

  let rec alloc : List (Option Nat × Nat) → List Nat
  | [] => []
  | (none, 0) :: xs => alloc xs
  | (none, len) :: xs =>
    let res := findLastFitting len xs
    if h : res.isSome then
      -- Cannot destrucut these the normal way because then Lean loses the definition of `rest` :E
      let id := (res.get h).1
      let nlen := (res.get h).2.1
      let rest := (res.get h).2.2

      -- Proofs that recursion terminates
      have := length_findLastFitting len xs h
      have := len_sum_findLastFitting len xs h

      List.replicate nlen id ++ alloc ((none, len-nlen) :: rest)
    else
      List.replicate len 0 ++ alloc xs
  | (some id, len) :: xs => List.replicate len id ++ alloc xs
  termination_by l => (l.filter (·.fst.isSome) |>.map (·.snd)).sum + l.length

  attachId 0 l |> alloc |>.enum |>.map (Function.uncurry (· * ·)) |>.sum


def main : IO Unit := do
  let stdin ← IO.getStdin
  let input ← stdin.readToEnd
  let input ← IO.ofExcept $ parser.run input

  -- Part 1
  let _ ← IO.println s!"Part 1: {part1 input}"

  -- Part 2
  let _ ← IO.println s!"Part 2: {part2 input}"
