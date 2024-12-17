import Mathlib
import Aoc2024
import Std.Internal.Parsec

open Std.Internal.Parsec
open Std.Internal.Parsec.String
open Batteries BinaryHeap

structure ProgramState where
  a : Nat
  b : Nat
  c : Nat
  pc : Nat
  mem : Array (Fin 8)
  output : Array (Fin 8)

def parser : Parser ProgramState := do
  skipString "Register A: "
  let a ← digits
  skipString "\nRegister B: "
  let b ← digits
  skipString "\nRegister C: "
  let c ← digits
  skipString "\n\nProgram: "
  let mem ← List.toArray <$> separated (skipChar ',') digit
  skipChar '\n' <* eof
  let mem := mem.map fun c => Fin.ofNat' 8 (c.toNat - '0'.toNat)
  return ⟨a, b, c, 0, mem, #[]⟩

def ProgramState.combo (ps : ProgramState) : Fin 8 → Option Nat
  | 0 => some 0
  | 1 => some 1
  | 2 => some 2
  | 3 => some 3
  | 4 => some ps.a
  | 5 => some ps.b
  | 6 => some ps.c
  | 7 => none       -- Reserved. Won't appear

def ProgramState.step (ps : ProgramState) : Option ProgramState := do
  let op ← ps.mem.get? ps.pc
  let operand ← ps.mem.get? (ps.pc + 1)

  match op with
  | 0 =>
    -- adv
    some { ps with
      a := ps.a.shiftRight (← ps.combo operand)
      pc := ps.pc + 2
    }
  | 1 =>
    -- bxl
    some { ps with
      b := ps.b.xor operand
      pc := ps.pc + 2
    }
  | 2 =>
    -- bst
    some { ps with
      b := (← ps.combo operand).mod 8
      pc := ps.pc + 2
    }
  | 3 =>
    -- jnz
    if ps.a = 0 then
      some { ps with
        pc := ps.pc + 2
      }
    else
      some { ps with
        pc := operand
      }

  | 4 =>
    -- bxc
    some { ps with
      b := ps.b.xor ps.c
      pc := ps.pc + 2
    }
  | 5 =>
    -- out
    some { ps with
      output := ps.output.push (← ps.combo operand)
      pc := ps.pc + 2
    }
  | 6 =>
    -- bdv
    some { ps with
      b := ps.a.shiftRight (← ps.combo operand)
      pc := ps.pc + 2
    }
  | 7 =>
    -- cdv
    some { ps with
      c := ps.a.shiftRight (← ps.combo operand)
      pc := ps.pc + 2
    }

partial def part1.go (ps : ProgramState) : ProgramState :=
  if let some next := ps.step then
    go next
  else
    ps

def part1 (ps : ProgramState) : String :=
  let final := part1.go ps
  let output := final.output.toList
  String.join <| List.intersperse "," <| output.map toString

partial def part2.go (target : List (Fin 8)) (ps : ProgramState) : Bool :=
  if let some 5 := ps.mem.get? ps.pc then
    -- About to output
    if let some operand := ps.mem.get? (ps.pc+1) then
      if let some val := ps.combo operand then
        match target with
        | [] => false -- Program outputted something but it shouldn't have
        | x :: xs => if x == val then
          if let some next := ps.step then
            go xs next
          else
            false
        else
          false   -- Incompatible output
      else
        false     -- Failed to decode operand
    else
      false       -- Operand couldn't be read
  else
    if let some next := ps.step then
      go target next
    else
      -- End of program
      target.isEmpty

partial def part2.go' (target : List (Fin 8)) (ps : ProgramState) : Nat :=
  match target with
  | [] => 0
  | _ :: xs =>
    let tail_res := go' xs ps
    List.range 64 |>.map (· + (tail_res.shiftLeft 3)) |>.find? (fun a =>
      part2.go target { ps with a := a }
    ) |>.getD 0

def part2 (ps : ProgramState) : Nat := Id.run do
  -- The program seems to be of the form "read 3 lowest bits of A, decrypt them and print them out, then shift those bits off of A".
  let target := ps.mem.toList
  part2.go' target ps

def main : IO Unit := do
  let stdin ← IO.getStdin
  let input ← stdin.readToEnd
  let input ← IO.ofExcept $ parser.run input

  -- Part 1
  let _ ← IO.println s!"Part 1: {part1 input}"

  -- Part 2
  let _ ← IO.println s!"Part 2: {part2 input}"
