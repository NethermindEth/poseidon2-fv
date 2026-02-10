import Mathlib

import Poseidon

namespace Poseidon2Spec

open Poseidon

def add_array [Add α] (v w: Array α) := v.zip w |>.map fun (x, y) => x + y

/--
The internal state for the hashing algorithm
-/
structure State_spec (profile : HashProfile) where
  round : Nat
  state : Array (ZMod profile.p)

def sBox_spec (profile : HashProfile) : ZMod profile.p → ZMod profile.p :=
  match profile.a with
  | .ofNat n => fun x => x^n
  | .negSucc n => fun x => (x.inv)^(n + 1)

structure Hash.Context (profile : HashProfile) where
  internalMatrixDiag : Array (ZMod profile.p)
  fullRoundConstants : Array $ Array (ZMod profile.p)
  partialRoundConstants : Array (ZMod profile.p)

abbrev HashM (profile : HashProfile) := ReaderT (Poseidon2Spec.Hash.Context profile) $ StateM (State_spec profile)

def getPartialRound (round : Nat) (profile : HashProfile) : Nat :=
  let halfFullRound := profile.fullRounds / 2
  round - halfFullRound

def getFullRound (round : Nat) (profile : HashProfile) : Nat :=
  let halfFullRound := profile.fullRounds / 2
  if round <= halfFullRound then round else round - profile.partRounds

variable (profile : HashProfile)

def addFullConst : HashM profile PUnit := do
  let fullRound := getFullRound (← get).round profile
  let const := (← read).fullRoundConstants[fullRound]!
  modify fun ⟨r, vec⟩ => ⟨r, add_array vec const⟩

def addPartialConst : HashM profile PUnit := do
  let partialRound := getPartialRound (← get).round profile
  let const := (← read).partialRoundConstants[partialRound]!
  modify fun ⟨r, vec⟩ => ⟨r, vec.modify 0 (· + const)⟩

def internalMatrixAction (diag : Array (ZMod p)) (vec : Array (ZMod p)) : Array (ZMod p) :=
  let sum := vec.foldl (· + ·) 0
  vec.mapIdx fun idx a => sum + a * diag[idx]!

open YatimaMatrix in
def internalLinearLayer : HashM profile PUnit := do
  let diag := (← read).internalMatrixDiag
  modify (fun ⟨r, vec⟩ => ⟨r, internalMatrixAction diag vec⟩)

-- instance : YatimaRing (ZMod P) where
--   zero := 0
--   one := 1
--   coe := λ x => (x: ZMod P)

def matrix_action{R} [OfNat R (nat_lit 0)] [Add R] [Mul R] (M : Array (Array R)) (v : Array R) : Array R :=
  M.zip v |>.foldl (fun v (col, r) => add_array v (col.map (λ x => x * r))) (Array.replicate v.size 0)

-- depends on `vec` having size 4
def smallMatrixAction (vec : Array (ZMod p)) : Array (ZMod p) :=
  let smallMatrix : Array (Array (ZMod p)) :=
    #[#[2, 1, 1, 3],
      #[3, 2, 1, 1],
      #[1, 3, 2, 1],
      #[1, 1, 3, 2]]
  matrix_action smallMatrix vec

-- depends on `vec` having size 4 * t
def externalMatrixAction (vec : Array (ZMod p)) : Array (ZMod p) := Id.run do
  let t := vec.size / 4
  let mut result := #[]
  for idx in [:t] do
    result := result ++ smallMatrixAction (vec.extract (4 * idx) (4 * (idx + 1)))

  let sums := Array.iota 3 |>.map (fun k =>
                Array.iota (t - 1) |>.map (fun j => result[4 * j + k]!)
                             |>.foldl (· + ·) 0)

  for i in [:vec.size] do
    result := result.modify i (· + sums[i % 4]!)

  return result

open YatimaMatrix in
def externalLinearLayer : HashM profile PUnit := do
  modify (fun ⟨r, vec⟩ => ⟨r, externalMatrixAction vec⟩)

def fullRound : HashM profile PUnit :=
  addFullConst profile *>
  (modify fun ⟨r, vec⟩ => ⟨r.succ, vec.map (sBox_spec profile)⟩) *>
  externalLinearLayer profile

def partialRound : HashM profile PUnit :=
  addPartialConst profile *>
  (modify fun ⟨r, vec⟩ => ⟨r.succ, vec.modify 0 (sBox_spec profile)⟩) *>
  internalLinearLayer profile

open Monad in
def runRounds : HashM profile PUnit :=
  externalLinearLayer profile *>
  repeatM (fullRound profile) (profile.fullRounds / 2) *>
  repeatM (partialRound profile) (profile.partRounds) *>
  repeatM (fullRound profile) (profile.fullRounds / 2)

def initialState {profile : HashProfile} (input : Array (ZMod profile.p)) : State_spec profile := ⟨0, input⟩

def hash (context : Poseidon2Spec.Hash.Context profile) (input : Array (ZMod profile.p)) : State_spec profile :=
  Prod.snd <$> StateT.run (ReaderT.run (runRounds profile) context) (initialState input)

def validateInputs (context : Poseidon2Spec.Hash.Context profile) (input : Array (ZMod profile.p)) : Bool :=
  input.size == profile.t &&
  profile.t % 4 == 0 &&
  true && -- TODO: At some point we should check the sizes of the partial round and full round constants
  profile.t == context.internalMatrixDiag.size

def hashInputWithCtx (context : Poseidon2Spec.Hash.Context profile) (input : Array (ZMod profile.p)) : Array (ZMod profile.p) :=
  if validateInputs profile context input then (hash profile context input).state else #[]

end Poseidon2Spec
