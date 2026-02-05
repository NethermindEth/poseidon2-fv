import LeanZKCircuit_Plonky3.Plonky3.Command.util
import Poseidon2Fv.Extraction.Full
import Poseidon2Fv.Tactics

open Plonky3 Poseidon2.Extraction

namespace Poseidon2.Folding

def eval_sbox_7_1 [Field F] (x3 x : F) : Prop :=
  x3 - (x * x) * x = 0

def apply_full_round_sbox [Field F] (state: Fin 16 → F) : Fin 16 → F :=
  λ x => state x ^ 7

def apply_partial_round_sbox [Field F] (state: Fin 16 → F) : Fin 16 → F
  | 0 => state 0 ^ 7
  | x => state x

def apply_m4 [Field F] (state: Fin 16 → F) (idx: Fin 16) : Fin 4 → F :=
  λ x =>
  let x0 := state idx
  let x1 := state (idx + 1)
  let x2 := state (idx + 2)
  let x3 := state (idx + 3)
  let x01 := x0 + x1
  let x23 := x2 + x3
  let x0123 := x01 + x23
  let x01123 := x0123 + x1
  let x01233 := x0123 + x3
  match x with
    | 0 => x01123 + x01
    | 1 => x01123 + (state (idx + 2) + state (idx + 2))
    | 2 => x01233 + x23
    | 3 => x01233 + (state idx + state idx)
    | _ => 0

def apply_m4_loop [Field F] (state : Fin 16 → F) : Fin 16 → F
  | 0 => apply_m4 state 0 0
  | 1 => apply_m4 state 0 1
  | 2 => apply_m4 state 0 2
  | 3 => apply_m4 state 0 3
  | 4 => apply_m4 state 4 0
  | 5 => apply_m4 state 4 1
  | 6 => apply_m4 state 4 2
  | 7 => apply_m4 state 4 3
  | 8 => apply_m4 state 8 0
  | 9 => apply_m4 state 8 1
  | 10 => apply_m4 state 8 2
  | 11 => apply_m4 state 8 3
  | 12 => apply_m4 state 12 0
  | 13 => apply_m4 state 12 1
  | 14 => apply_m4 state 12 2
  | 15 => apply_m4 state 12 3
  | _ => 0

def apply_m4_sums [Field F] (state : Fin 16 → F) : Fin 4 → F
  | 0 => (apply_m4_loop state 0) + (apply_m4_loop state 4) + (apply_m4_loop state 8) + (apply_m4_loop state 12)
  | 1 => (apply_m4_loop state 1) + (apply_m4_loop state 5) + (apply_m4_loop state 9) + (apply_m4_loop state 13)
  | 2 => (apply_m4_loop state 2) + (apply_m4_loop state 6) + (apply_m4_loop state 10) + (apply_m4_loop state 14)
  | 3 => (apply_m4_loop state 3) + (apply_m4_loop state 7) + (apply_m4_loop state 11) + (apply_m4_loop state 15)

def mds_light_permutation [Field F] (state : Fin 16 → F) : Fin 16 → F
  | 0 => apply_m4_loop state 0 + apply_m4_sums state 0
  | 1 => apply_m4_loop state 1 + apply_m4_sums state 1
  | 2 => apply_m4_loop state 2 + apply_m4_sums state 2
  | 3 => apply_m4_loop state 3 + apply_m4_sums state 3
  | 4 => apply_m4_loop state 4 + apply_m4_sums state 0
  | 5 => apply_m4_loop state 5 + apply_m4_sums state 1
  | 6 => apply_m4_loop state 6 + apply_m4_sums state 2
  | 7 => apply_m4_loop state 7 + apply_m4_sums state 3
  | 8 => apply_m4_loop state 8 + apply_m4_sums state 0
  | 9 => apply_m4_loop state 9 + apply_m4_sums state 1
  | 10 =>apply_m4_loop state 10 + apply_m4_sums state 2
  | 11 =>apply_m4_loop state 11 + apply_m4_sums state 3
  | 12 =>apply_m4_loop state 12 + apply_m4_sums state 0
  | 13 =>apply_m4_loop state 13 + apply_m4_sums state 1
  | 14 =>apply_m4_loop state 14 + apply_m4_sums state 2
  | 15 =>apply_m4_loop state 15 + apply_m4_sums state 3
  | _ => 0

-- BabyBearInternalLayerParameters::
def internal_layer_mat_mul [Field F] (state : Fin 16 → F) (sum : F) : Fin 16 → F
  | 0 => state 0
  | 1 => state 1 + sum
  | 2 => state 2 + state 2 + sum
  | 3 => state 3 / 2 + sum
  | 4 => sum + (state 4 + state 4) + state 4
  | 5 => sum + ((state 5 + state 5) + (state 5 + state 5))
  | 6 => sum - state 6 / 2
  | 7 => sum - (state 7 + state 7 + state 7)
  | 8 => sum - ((state 8 + state 8) + (state 8 + state 8))
  | 9 => state 9 / (2 ^ 8) + sum
  | 10 => state 10 / (2 ^ 2) + sum
  | 11 => state 11 / (2 ^ 3) + sum
  | 12 => state 12 / (2 ^ 27) + sum
  | 13 => sum - state 13 / (2 ^ 8)
  | 14 => sum - state 14 / (2 ^ 4)
  | 15 => sum - state 15 / (2 ^ 27)
  | _ => 0

-- InternalLayerBaseParameters::
def generic_internal_linear_layer [Field F] (state : Fin 16 → F) : Fin 16 → F :=
  let part_sum :=
    state 1 +
    state 2 +
    state 3 +
    state 4 +
    state 5 +
    state 6 +
    state 7 +
    state 8 +
    state 9 +
    state 10 +
    state 11 +
    state 12 +
    state 13 +
    state 14 +
    state 15
  let state' := λ x => match x with
    | 0 => part_sum - state 0
    | x => state x
  internal_layer_mat_mul state' (part_sum + state 0)

-- WIDTH → F
def beginning_full_round_constants [Field F] : Fin 4 → Fin 16 → F :=
  λ x y => match x, y with
    | 0, 0 => 0x69cbb6af
    | 0, 1 => 0x46ad93f9
    | 0, 2 => 0x60a00f4e
    | 0, 3 => 0x6b1297cd
    | 0, 4 => 0x23189afe
    | 0, 5 => 0x732e7bef
    | 0, 6 => 0x72c246de
    | 0, 7 => 0x2c941900
    | 0, 8 => 0x0557eede
    | 0, 9 => 0x1580496f
    | 0, 10 => 0x3a3ea77b
    | 0, 11 => 0x54f3f271
    | 0, 12 => 0x0f49b029
    | 0, 13 => 0x47872fe1
    | 0, 14 => 0x221e2e36
    | 0, 15 => 0x1ab7202e
    | 1, 0 => 0x487779a6
    | 1, 1 => 0x3851c9d8
    | 1, 2 => 0x38dc17c0
    | 1, 3 => 0x209f8849
    | 1, 4 => 0x268dcee8
    | 1, 5 => 0x350c48da
    | 1, 6 => 0x5b9ad32e
    | 1, 7 => 0x0523272b
    | 1, 8 => 0x3f89055b
    | 1, 9 => 0x01e894b2
    | 1, 10 => 0x13ddedde
    | 1, 11 => 0x1b2ef334
    | 1, 12 => 0x7507d8b4
    | 1, 13 => 0x6ceeb94e
    | 1, 14 => 0x52eb6ba2
    | 1, 15 => 0x50642905
    | 2, 0 => 0x05453f3f
    | 2, 1 => 0x06349efc
    | 2, 2 => 0x6922787c
    | 2, 3 => 0x04bfff9c
    | 2, 4 => 0x768c714a
    | 2, 5 => 0x3e9ff21a
    | 2, 6 => 0x15737c9c
    | 2, 7 => 0x2229c807
    | 2, 8 => 0x0d47f88c
    | 2, 9 => 0x097e0ecc
    | 2, 10 => 0x27eadba0
    | 2, 11 => 0x2d7d29e4
    | 2, 12 => 0x3502aaa0
    | 2, 13 => 0x0f475fd7
    | 2, 14 => 0x29fbda49
    | 2, 15 => 0x018afffd
    | 3, 0 => 0x0315b618
    | 3, 1 => 0x6d4497d1
    | 3, 2 => 0x1b171d9e
    | 3, 3 => 0x52861abd
    | 3, 4 => 0x2e5d0501
    | 3, 5 => 0x3ec8646c
    | 3, 6 => 0x6e5f250a
    | 3, 7 => 0x148ae8e6
    | 3, 8 => 0x17f5fa4a
    | 3, 9 => 0x3e66d284
    | 3, 10 => 0x0051aa3b
    | 3, 11 => 0x483f7913
    | 3, 12 => 0x2cfe5f15
    | 3, 13 => 0x023427ca
    | 3, 14 => 0x2cc78315
    | 3, 15 => 0x1e36ea47
    | _, _ => 0

def partial_round_constants [Field F] : Fin 13 → F
  | 0 => 0x5a8053c0
  | 1 => 0x693be639
  | 2 => 0x3858867d
  | 3 => 0x19334f6b
  | 4 => 0x128f0fd8
  | 5 => 0x4e2b1ccb
  | 6 => 0x61210ce0
  | 7 => 0x3c318939
  | 8 => 0x0b5b2f22
  | 9 => 0x2edb11d5
  | 10 => 0x213effdf
  | 11 => 0x0cac4606
  | 12 => 0x241af16d

def add_beginning_full_round_constants [Field F] (state: Fin 16 → F) (round : Fin 4) : Fin 16 → F :=
  λ x => state x + beginning_full_round_constants round x

def beginning_full_round [Field F] (state: Fin 16 → F) (round : Fin 4) : Fin 16 → F :=
  mds_light_permutation (
    apply_full_round_sbox (
      add_beginning_full_round_constants state round
    )
  )

def add_partial_round_constant [Field F] (state: Fin 16 → F) (round : Fin 13) : Fin 16 → F
  | 0 => state 0 + partial_round_constants round
  | x => state x

def partial_round [Field F] (state : Fin 16 → F) (round : Fin 13) : Fin 16 → F :=
  generic_internal_linear_layer (
    apply_partial_round_sbox (
      add_partial_round_constant state round
    )
  )

structure FullRound (F: Type) where
  sbox : Fin 16 → F -- WIDTH sboxes, each of which is 1 register
  post : Fin 16 → F

structure PartialRound (F: Type) where
  sbox : F -- a single one-register sbox
  post_sbox : F -- its result

def inputs
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Fin 16 → F :=
  λ x => (Circuit.main c (1 + x.val) row 0)

-- HALF FULL ROUNDS →
def beginning_full_rounds
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Fin 4 → FullRound F :=
  λ round => {
    sbox := λ x => (Circuit.main c (17 + 32*round.val + x.val) row 0)
    post := λ x => (Circuit.main c (33 + 32*round.val + x.val) row 0)
  }

-- PARTIAL ROUNDS →
def partial_rounds
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row : ℕ)
: Fin 13 → PartialRound F :=
  λ round => {
    sbox := (Circuit.main c (145 + 2*round.val) row 0)
    post_sbox := (Circuit.main c (146 + 2*round.val) row 0)
  }

-- HALF FULL ROUNDS →
def ending_full_rounds
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Fin 4 → FullRound F :=
  λ round => {
    sbox := λ x => (Circuit.main c (171 + 32*round.val + x.val) row 0)
    post := λ x => (Circuit.main c (187 + 32*round.val + x.val) row 0)
  }

end Poseidon2.Folding
