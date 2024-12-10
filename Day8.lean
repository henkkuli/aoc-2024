import Mathlib
import Aoc2024
import Std.Internal.Parsec

open Std.Internal.Parsec
open Std.Internal.Parsec.String

def parser : Parser (Array (Array Char)) :=
  many (many (satisfy fun c => c ≠ '\n') <* pchar '\n') <* eof

theorem List.dropWhile_length (p : α → Bool) (l : List α) : (List.dropWhile p l).length ≤ l.length := by
  induction l
  case nil => rfl
  case cons head tail ih =>
    by_cases h : p head
    case neg =>
      rw [List.dropWhile_cons_of_neg]
      assumption
    case pos =>
      rw [List.dropWhile_cons_of_pos]
      apply le_trans ih
      exact Nat.le_succ tail.length
      assumption

def findAntennae (map : (Array (Array Char))) : List (Char × List (Nat × Nat)) :=
  let poss : List (Char × (Nat × Nat)) :=
    map.toList.enum >>= fun ⟨y, row⟩ =>
      row.toList.enum >>= fun ⟨x, c⟩ =>
        if c ≠ '.' then
          [(c, y, x)]
        else
          []

  let rec collect (l : List (Char × (Nat × Nat))) : List (Char × List (Nat × Nat)) :=
    match l with
    | [] => []
    | ⟨c, _⟩ :: tail =>
      let a := l.takeWhile (·.fst = c)
      let b := tail.dropWhile (·.fst = c)
      (c, (·.snd) <$> a) :: collect b
    termination_by l.length
    decreasing_by
      exact Nat.lt_add_one_of_le (List.dropWhile_length (fun x => decide (x.1 = c)) tail)

  collect $ poss.mergeSort fun a b => (Ord.lex instOrdChar lexOrd).toLE.le a b

def part1 (map : (Array (Array Char))) : Nat :=
  let antennae := findAntennae map
  let height := map.size
  let width := if h : height ≠ 0 then map[0].size else 0

  let locations (l : List (Nat × Nat)) : List (Int × Int) :=
    l.product l |>.filter (fun ⟨a, b⟩ => a ≠ b) |>.map fun ⟨a, b⟩ =>
      -- ⟨b, a⟩ is also included in the list, so check only one placement here
      let y := 2 * Int.ofNat b.1 - Int.ofNat a.1
      let x := 2 * Int.ofNat b.2 - Int.ofNat a.2
      ⟨y, x⟩

  let isValid : Int × Int → Prop
  | ⟨y, x⟩ => 0 ≤ y ∧ y < height ∧ 0 ≤ x ∧ x < width

  List.length <| List.dedup <| List.filter isValid <| Prod.snd <$> antennae >>= locations


def part2 (map : (Array (Array Char))) : Nat :=
  let antennae := findAntennae map
  let height := map.size
  let width := if h : height ≠ 0 then map[0].size else 0
  let maxRepeats := Nat.max height width

  let locations (l : List (Nat × Nat)) : List (Int × Int) :=
    l.product l |>.filter (fun ⟨a, b⟩ => a ≠ b) |>.flatMap fun ⟨a, b⟩ =>
      -- ⟨b, a⟩ is also included in the list, so check only one placement here
      let dy := Int.ofNat b.1 - Int.ofNat a.1
      let dx := Int.ofNat b.2 - Int.ofNat a.2
      let g := dy.gcd dx
      List.range maxRepeats |>.map fun c => ⟨Int.ofNat b.1 + c * dy, Int.ofNat b.2 + c * dx⟩

  let isValid : Int × Int → Prop
  | ⟨y, x⟩ => 0 ≤ y ∧ y < height ∧ 0 ≤ x ∧ x < width

  List.length <| List.dedup <| List.filter isValid <| Prod.snd <$> antennae >>= locations

def main : IO Unit := do
  let stdin ← IO.getStdin
  let input ← stdin.readToEnd
  let input ← IO.ofExcept $ parser.run input

  -- Part 1
  let _ ← IO.println s!"Part 1: {part1 input}"

  -- Part 2
  let _ ← IO.println s!"Part 2: {part2 input}"
