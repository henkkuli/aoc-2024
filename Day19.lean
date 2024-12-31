import Mathlib
import Aoc2024
import Std.Internal.Parsec

open Std.Internal.Parsec
open Std.Internal.Parsec.String

inductive Color
| white
| blue
| black
| red
| green
deriving BEq, Repr

def Color.parser : Parser Color :=
  (skipChar 'w' *> pure .white) <|> (skipChar 'u' *> pure .blue) <|> (skipChar 'b' *> pure .black) <|> (skipChar 'r' *> pure .red) <|> (skipChar 'g' *> pure .green)

structure Input where
  available : List (List Color)
  wanted : List (List Color)

def parser : Parser Input := do
  let available ← separated (skipString ", ") (Array.toList <$> many Color.parser)
  skipString "\n\n"
  let wanted ← Array.toList <$> many (Array.toList <$> many Color.parser <* skipChar '\n')
  eof
  return {available, wanted}

def canBeCreatedLoop (available : List (List Color)) : List Color → List Bool
| [] => [true]
| design@(_ :: xs) =>
  let tail := canBeCreatedLoop available xs
  let a := available.any fun towel => towel.isPrefixOf design ∧ tail.getD (towel.length-1) false
  a :: tail

def canBeCreated (available : List (List Color)) : List Color → Bool :=
  (List.getD · 0 false) ∘ canBeCreatedLoop available

def part1 (input : Input) : Nat :=
  input.wanted.countP (canBeCreated input.available)

def waysToCreateLoop (available : List (List Color)) : List Color → List Nat
| [] => [1]
| design@(_ :: xs) =>
  let tail := waysToCreateLoop available xs
  let a := available.filter (·.isPrefixOf design) |>.map (fun towel => tail.getD (towel.length-1) 0) |>.sum
  a :: tail

def waysToCreate (available : List (List Color)) : List Color → Nat :=
  (List.getD · 0 0) ∘ waysToCreateLoop available

def part2 (input : Input) : Nat :=
  input.wanted.map (waysToCreate input.available) |>.sum

def main : IO Unit := do
  let stdin ← IO.getStdin
  let input ← stdin.readToEnd
  let input ← IO.ofExcept $ parser.run input

  -- Part 1
  let _ ← IO.println s!"Part 1: {part1 input}"

  -- -- Part 2
  let _ ← IO.println s!"Part 2: {part2 input}"
