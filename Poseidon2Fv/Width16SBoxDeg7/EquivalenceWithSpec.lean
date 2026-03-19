import Poseidon2Fv.Width16SBoxDeg7.Folding
import Poseidon.Hash
import Poseidon.Parameters.BabyBear
import LSpec

open Poseidon2
open BabyBear (p)
open LSpec
open SlimCheck

namespace Poseidon2.EquivalenceWithSpec

def input16 : List ℤ := Array.iota 15 |>.toList

-- Expects width 16
def poseidon2Spec (input : List ℤ) : List ℤ :=
  let inputAsArray : Array <| ZMod p := input |>.toArray
  let output := Poseidon2.hashInputWithCtx BabyBear16.hashProfile BabyBear16.lurkContext inputAsArray
  List.map (fun x ↦ x.cast) output.toList

-- #eval poseidon2Spec input16

end Poseidon2.EquivalenceWithSpec
