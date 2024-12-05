import Std.Internal.Parsec

open Std.Internal.Parsec
open Std.Internal.Parsec.String

partial def IO.FS.Stream.readToEnd (stream : Stream) : IO String := do
  let rec loop (s : String) := do
    let line ← stream.getLine
    if line.isEmpty then
      return s
    else
      loop (s ++ line)
  loop ""

partial def separated (sep : Parser Unit) (value : Parser α) : Parser (List α) :=
  let rec loop (res : Array α) : Parser (Array α) := do
    let res := res.push (←value)
    (sep *> loop res) <|> pure res

  Array.toList <$> loop #[]

def countOccurrences (p : Parser Unit) (v : String) : Nat :=
  let rec loop (it : String.Iterator) : Nat :=
    if it.atEnd then
      0
    else
      let tail_res := loop it.next
      match p it with
      | .success _ _ => (1 + tail_res)
      | .error _ _ => tail_res
  loop v.iter
