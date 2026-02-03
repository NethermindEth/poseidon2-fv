import LeanZKCircuit_Plonky3.Plonky3.Command.util
import Poseidon2Fv.Extraction.Full
import Poseidon2Fv.Tactics

open Plonky3 Poseidon2.extraction

namespace Poseidon2.Folding

def eval_sbox_7_1 [Field F] (x3 x : F) : Prop :=
  x3 - (x * x) * x = 0

def apply_full_round_sbox [Field F] (state: Fin 16 → F) : Fin 16 → F :=
  λ x => state x ^ 7

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

-- WIDTH → F
def round_constants [Field F] : Fin 4 → Fin 16 → F :=
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

def add_round_constants [Field F] (state: Fin 16 → F) (round : Fin 4) : Fin 16 → F :=
  λ x => state x + round_constants round x

def full_round [Field F] (state: Fin 16 → F) (round : Fin 4) : Fin 16 → F :=
  mds_light_permutation (
    apply_full_round_sbox (
      add_round_constants state round
    )
  )

structure FullRound (F: Type) where
  sbox : Fin 16 → F -- WIDTH sboxes, each of which is 1 register
  post : Fin 16 → F

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

-- Start state
#define_opaque_state 0 4 1

def state0'
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Fin 16 → F :=
  inputs c row

lemma state0_equiv
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
:
  state0 c row = state0' c row
:= by
  unfold state0 state0' inputs
  funext x
  fin_cases x <;> rfl

-- After first external linear layer
#define_opaque_state 1 657 1

def state1'
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Fin 16 → F :=
  mds_light_permutation (state0 c row)

section external_linear_layer_zero
  lemma state1_equiv
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row: ℕ)
  :
    state1 c row = state1' c row
  := by
    unfold state1 state1' mds_light_permutation
    funext x
    fin_cases x
    all_goals (
      simp [
        Poseidon2_expressions,
        state0, apply_m4_sums, apply_m4_loop, apply_m4
      ]
      congr
    )
end external_linear_layer_zero

#define_opaque_state 2 673 6

-- After adding round constants
def state2'
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Fin 16 → F :=
  λ x => state1 c row x + round_constants 0 x

lemma state2_equiv
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
:
  state2 c row = state2' c row
:= by
  unfold state2 state2'
  funext x
  fin_cases x <;> rfl

-- sbox internal state
#define_opaque_state 3 675 6

def state3'
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Fin 16 → F :=
  λ x => state2 c row x ^ 3

section sbox_zero_internal

  #tag_simp_range "e" 674 16 6 "Poseidon2_expressions"
  #tag_simp_range "e" 675 16 6 "Poseidon2_expressions"

  lemma state3_equiv
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row: ℕ)
  :
    state3 c row = state3' c row
  := by
    unfold state3 state3' state2
    funext x
    fin_cases x <;> (
      simp [
        Poseidon2_expressions,
        pow_three'
      ]
    )

end sbox_zero_internal

-- saved sbox internal state
#define_opaque_state 4 20 1

def state4'
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Fin 16 → F :=
  λ x => state3 c row x

section sbox_state_zero
  #tag_simp_range "constraint_" 0 16 1 "Poseidon2_expressions"
  #tag_simp_range "e" 20 16 1 "Poseidon2_expressions"
  #tag_simp_range "e" 673 94 1 "Poseidon2_expressions"
  attribute [local simp]
    eval_sbox_7_1
    round_constants
    beginning_full_rounds
    state1
    state2

  #prove_eval_sbox_constraints 0 0 2 16
end sbox_state_zero


-- sbox result
#define_opaque_state 5 678 6

def state5'
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Fin 16 → F :=
  λ x => state2 c row x ^ 7

#define_constraint_group "full_round_0_sbox_constraints" 0 16

section sbox_zero_external

  #tag_simp_range "constraint_equiv_" 0 16 1 "Poseidon2_constraints"
  #tag_simp_range "e" 20 16 1 "Poseidon2_expressions"
  #tag_simp_range "e" 677 16 6 "Poseidon2_expressions"
  #tag_simp_range "e" 678 16 6 "Poseidon2_expressions"

  lemma state5_equiv
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row: ℕ)
    (h: full_round_0_sbox_constraints c row)
  :
    state5 c row = state5' c row
  := by
    unfold state5 state5' state2
    funext x
    have (x: F) : x * x * x * (x * x * x) * x = x^7 := by grind
    simp [
      full_round_0_sbox_constraints,
      Poseidon2_constraints,
      eval_sbox_7_1,
      beginning_full_rounds,
      state2,
      sub_eq_zero
    ] at h
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
    fin_cases x <;> (
      simp [
        Poseidon2_expressions,
        h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
        this
      ]
    )

end sbox_zero_external

-- After external linear layer
#define_opaque_state 6 825 1

def state6'
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Fin 16 → F :=
  mds_light_permutation (state5 c row)

section external_linear_layer_one
  lemma state6_equiv
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row: ℕ)
  :
    state6 c row = state6' c row
  := by
    unfold state6 state6' mds_light_permutation
    funext x
    fin_cases x
    all_goals (
      simp [
        Poseidon2_expressions,
        state5, apply_m4_sums, apply_m4_loop, apply_m4
      ]
      congr
    )
end external_linear_layer_one

-- Round 0 post
#define_opaque_state 7 825 1

def state7'
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Fin 16 → F :=
  λ x => (Circuit.main c (33 + x.val) row 0)

#define_constraint_group "full_round_0_post_constraints" 16 16

section full_round_0_post

  #tag_simp_range "constraint_" 16 16 1 "Poseidon2_expressions"
  #tag_simp_range "e" 36 16 1 "Poseidon2_expressions"
  #tag_simp_range "e" 841 16 1 "Poseidon2_expressions"
  attribute [local simp]
    eval_sbox_7_1
    beginning_full_rounds
    state7
    sub_eq_zero

  #prove_full_round_post_constraints 16 0 7 16

  lemma state7_equiv
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row: ℕ)
    (h: full_round_0_post_constraints c row)
  :
    state7 c row = state7' c row
  := by
    unfold state7 state7'
    funext x
    simp [
      full_round_0_post_constraints,
      Poseidon2_expressions,
      sub_eq_zero
    ] at h
    obtain ⟨h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩ := h
    fin_cases x <;> (
      simp [
        Poseidon2_expressions,
        h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31
      ]
    )
end full_round_0_post

def full_round_0_constraints
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Prop :=
  full_round_0_sbox_constraints c row ∧
  full_round_0_post_constraints c row

lemma full_round_0
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
  (h: full_round_0_constraints c row)
:
  (beginning_full_rounds c row 0).post =
  full_round (
    mds_light_permutation (
      inputs c row
    )
  ) 0

:= by
  have ⟨h_sbox, h_post⟩ := h

  have := state0_equiv c row
  unfold state0' at this
  rewrite [←this]; clear this

  have := state1_equiv c row
  unfold state1' at this
  rewrite [←this]; clear this

  have := state2_equiv c row
  unfold state2' at this
  unfold full_round add_round_constants
  rewrite [←this]; clear this

  have := state5_equiv c row h_sbox
  unfold state5' at this
  unfold apply_full_round_sbox
  rewrite [←this]; clear this

  have := state6_equiv c row
  unfold state6' at this
  rewrite [←this]; clear this

  have := state7_equiv c row h_post
  unfold state7' at this
  unfold beginning_full_rounds
  simp
  rewrite [←this]; clear this

  rfl

#define_opaque_state 8 857 6

-- After adding round constants
def state8'
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Fin 16 → F :=
  λ x => state7 c row x + round_constants 1 x

lemma state8_equiv
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
  (h: full_round_0_post_constraints c row)
:
  state8 c row = state8' c row
:= by
  unfold state8 state8'
  funext x
  rewrite [state7_equiv c row h]
  fin_cases x <;> rfl

-- sbox internal state
#define_opaque_state 9 859 6

def state9'
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Fin 16 → F :=
  λ x => state8 c row x ^ 3

section sbox_one_internal

  #tag_simp_range "e" 858 16 6 "Poseidon2_expressions"
  #tag_simp_range "e" 859 16 6 "Poseidon2_expressions"

  lemma state9_equiv
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row: ℕ)
  :
    state9 c row = state9' c row
  := by
    unfold state9 state9' state8
    funext x
    fin_cases x <;> (
      simp [
        Poseidon2_expressions,
        pow_three'
      ]
    )

end sbox_one_internal

-- saved sbox internal state
#define_opaque_state 10 52 1

def state10'
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Fin 16 → F :=
  λ x => state10 c row x

section sbox_state_one
  #tag_simp_range "constraint_" 32 16 1 "Poseidon2_expressions"
  #tag_simp_range "e" 52 16 1 "Poseidon2_expressions"
  #tag_simp_range "e" 858 16 6 "Poseidon2_expressions"
  #tag_simp_range "e" 859 16 6 "Poseidon2_expressions"
  #tag_simp_range "e" 860 16 6 "Poseidon2_expressions"
  attribute [local simp]
    eval_sbox_7_1
    round_constants
    beginning_full_rounds
    state8

  #prove_eval_sbox_constraints 32 1 8 16
end sbox_state_one


-- sbox result
#define_opaque_state 11 862 6

def state11'
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Fin 16 → F :=
  λ x => state8 c row x ^ 7

#define_constraint_group "full_round_1_sbox_constraints" 32 16

section sbox_one_external

  #tag_simp_range "constraint_equiv_" 32 16 1 "Poseidon2_constraints"
  #tag_simp_range "e" 52 16 1 "Poseidon2_expressions"
  #tag_simp_range "e" 861 16 6 "Poseidon2_expressions"
  #tag_simp_range "e" 862 16 6 "Poseidon2_expressions"

  lemma state11_equiv
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row: ℕ)
    (h: full_round_1_sbox_constraints c row)
  :
    state11 c row = state11' c row
  := by
    unfold state11 state11' state8
    funext x
    have (x: F) : x * x * x * (x * x * x) * x = x^7 := by grind
    simp [
      full_round_1_sbox_constraints,
      Poseidon2_constraints,
      eval_sbox_7_1,
      beginning_full_rounds,
      state8,
      sub_eq_zero
    ] at h
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
    fin_cases x <;> (
      simp [
        Poseidon2_expressions,
        h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
        this
      ]
    )

end sbox_one_external

-- After external linear layer
#define_opaque_state 12 1009 1

def state12'
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Fin 16 → F :=
  mds_light_permutation (state11 c row)

section external_linear_layer_one
  lemma state12_equiv
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row: ℕ)
  :
    state12 c row = state12' c row
  := by
    unfold state12 state12' mds_light_permutation
    funext x
    fin_cases x
    all_goals (
      simp [
        Poseidon2_expressions,
        state11, apply_m4_sums, apply_m4_loop, apply_m4
      ]
      congr
    )
end external_linear_layer_one

-- Round 1 post
#define_opaque_state 13 1009 1

def state13'
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Fin 16 → F :=
  λ x => (Circuit.main c (65 + x.val) row 0)

#define_constraint_group "full_round_1_post_constraints" 48 16

section full_round_1_post

  #tag_simp_range "constraint_" 48 16 1 "Poseidon2_expressions"
  #tag_simp_range "e" 68 16 1 "Poseidon2_expressions"
  #tag_simp_range "e" 1025 16 1 "Poseidon2_expressions"
  attribute [local simp]
    eval_sbox_7_1
    beginning_full_rounds
    state13
    sub_eq_zero

  #prove_full_round_post_constraints 48 1 13 16

  lemma state13_equiv
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row: ℕ)
    (h: full_round_1_post_constraints c row)
  :
    state13 c row = state13' c row
  := by
    unfold state13 state13'
    funext x
    simp [
      full_round_1_post_constraints,
      Poseidon2_expressions,
      sub_eq_zero
    ] at h
    obtain ⟨h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩ := h
    fin_cases x <;> (
      simp [
        Poseidon2_expressions,
        h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31
      ]
    )
end full_round_1_post

def full_round_1_constraints
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Prop :=
  full_round_1_sbox_constraints c row ∧
  full_round_1_post_constraints c row

lemma full_round_1
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
  (h0: full_round_0_constraints c row)
  (h1: full_round_1_constraints c row)
:
  (beginning_full_rounds c row 1).post =
  full_round (
    (beginning_full_rounds c row 0).post
  ) 1
:= by
  have ⟨h_sbox0, h_post0⟩ := h0
  have ⟨h_sbox1, h_post1⟩ := h1

  have := state7_equiv c row h_post0
  unfold state7' at this
  unfold beginning_full_rounds
  simp
  rewrite [←this]; clear this

  have := state8_equiv c row h_post0
  unfold state8' at this
  unfold full_round add_round_constants
  rewrite [←this]; clear this

  have := state11_equiv c row h_sbox1
  unfold state11' at this
  unfold apply_full_round_sbox
  rewrite [←this]; clear this

  have := state12_equiv c row
  unfold state12' at this
  rewrite [←this]; clear this

  have := state13_equiv c row h_post1
  unfold state13' at this
  rewrite [←this]; clear this

  rfl

#define_opaque_state 14 1041 6

-- After adding round constants
def state14'
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Fin 16 → F :=
  λ x => state13 c row x + round_constants 2 x

lemma state14_equiv
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
  (h: full_round_1_post_constraints c row)
:
  state14 c row = state14' c row
:= by
  unfold state14 state14'
  funext x
  rewrite [state13_equiv c row h]
  fin_cases x <;> rfl

-- sbox internal state
#define_opaque_state 15 1043 6

def state15'
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Fin 16 → F :=
  λ x => state14 c row x ^ 3

section sbox_two_internal

  #tag_simp_range "e" 1042 16 6 "Poseidon2_expressions"
  #tag_simp_range "e" 1043 16 6 "Poseidon2_expressions"

  lemma state15_equiv
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row: ℕ)
  :
    state15 c row = state15' c row
  := by
    unfold state15 state15' state14
    funext x
    fin_cases x <;> (
      simp [
        Poseidon2_expressions,
        pow_three'
      ]
    )

end sbox_two_internal

-- saved sbox internal state
#define_opaque_state 16 84 1

def state16'
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Fin 16 → F :=
  λ x => state16 c row x

section sbox_state_two
  #tag_simp_range "constraint_" 64 16 1 "Poseidon2_expressions"
  #tag_simp_range "e" 84 16 1 "Poseidon2_expressions"
  #tag_simp_range "e" 1042 16 6 "Poseidon2_expressions"
  #tag_simp_range "e" 1043 16 6 "Poseidon2_expressions"
  #tag_simp_range "e" 1044 16 6 "Poseidon2_expressions"
  attribute [local simp]
    eval_sbox_7_1
    round_constants
    beginning_full_rounds
    state14

  #prove_eval_sbox_constraints 64 2 14 16
end sbox_state_two

-- sbox result
#define_opaque_state 17 1046 6

def state17'
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Fin 16 → F :=
  λ x => state14 c row x ^ 7

#define_constraint_group "full_round_2_sbox_constraints" 64 16

section sbox_two_external

  #tag_simp_range "constraint_equiv_" 64 16 1 "Poseidon2_constraints"
  #tag_simp_range "e" 84 16 1 "Poseidon2_expressions"
  #tag_simp_range "e" 1045 16 6 "Poseidon2_expressions"
  #tag_simp_range "e" 1046 16 6 "Poseidon2_expressions"

  lemma state17_equiv
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row: ℕ)
    (h: full_round_2_sbox_constraints c row)
  :
    state17 c row = state17' c row
  := by
    unfold state17 state17' state14
    funext x
    have (x: F) : x * x * x * (x * x * x) * x = x^7 := by grind
    simp [
      full_round_2_sbox_constraints,
      Poseidon2_constraints,
      eval_sbox_7_1,
      beginning_full_rounds,
      state14,
      sub_eq_zero
    ] at h
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
    fin_cases x <;> (
      simp [
        Poseidon2_expressions,
        h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
        this
      ]
    )

end sbox_two_external

-- After external linear layer
#define_opaque_state 18 1193 1

def state18'
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Fin 16 → F :=
  mds_light_permutation (state17 c row)

section external_linear_layer_two

  lemma state18_equiv
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row: ℕ)
  :
    state18 c row = state18' c row
  := by
    unfold state18 state18' mds_light_permutation
    funext x
    fin_cases x
    all_goals (
      simp [
        Poseidon2_expressions,
        state17, apply_m4_sums, apply_m4_loop, apply_m4
      ]
      congr
    )
end external_linear_layer_two

-- Round 2 post
#define_opaque_state 19 1193 1

def state19'
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Fin 16 → F :=
  λ x => (Circuit.main c (97 + x.val) row 0)

#define_constraint_group "full_round_2_post_constraints" 80 16

section full_round_2_post

  #tag_simp_range "constraint_" 80 16 1 "Poseidon2_expressions"
  #tag_simp_range "e" 100 16 1 "Poseidon2_expressions"
  #tag_simp_range "e" 1209 16 1 "Poseidon2_expressions"
  attribute [local simp]
    eval_sbox_7_1
    beginning_full_rounds
    state19
    sub_eq_zero

  #prove_full_round_post_constraints 80 2 19 16

  lemma state19_equiv
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row: ℕ)
    (h: full_round_2_post_constraints c row)
  :
    state19 c row = state19' c row
  := by
    unfold state19 state19'
    funext x
    simp [
      full_round_2_post_constraints,
      Poseidon2_expressions,
      sub_eq_zero
    ] at h
    obtain ⟨h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩ := h
    fin_cases x <;> (
      simp [
        Poseidon2_expressions,
        h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31
      ]
    )
end full_round_2_post

def full_round_2_constraints
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Prop :=
  full_round_2_sbox_constraints c row ∧
  full_round_2_post_constraints c row

lemma full_round_2
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
  (h1: full_round_1_constraints c row)
  (h2: full_round_2_constraints c row)
:
  (beginning_full_rounds c row 2).post =
  full_round (
    (beginning_full_rounds c row 1).post
  ) 2
:= by
  have ⟨h_sbox1, h_post1⟩ := h1
  have ⟨h_sbox2, h_post2⟩ := h2

  have := state13_equiv c row h_post1
  unfold state13' at this
  unfold beginning_full_rounds
  simp
  rewrite [←this]; clear this

  have := state14_equiv c row h_post1
  unfold state14' at this
  unfold full_round add_round_constants
  rewrite [←this]; clear this

  have := state17_equiv c row h_sbox2
  unfold state17' at this
  unfold apply_full_round_sbox
  rewrite [←this]; clear this

  have := state18_equiv c row
  unfold state18' at this
  rewrite [←this]; clear this

  have := state19_equiv c row h_post2
  unfold state19' at this
  rewrite [←this]; clear this

  rfl

#define_opaque_state 20 1225 6

-- After adding round constants
def state20'
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Fin 16 → F :=
  λ x => state19 c row x + round_constants 3 x

lemma state20_equiv
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
  (h: full_round_2_post_constraints c row)
:
  state20 c row = state20' c row
:= by
  unfold state20 state20'
  funext x
  rewrite [state19_equiv c row h]
  fin_cases x <;> rfl

-- sbox internal state
#define_opaque_state 21 1227 6

def state21'
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Fin 16 → F :=
  λ x => state20 c row x ^ 3

section sbox_three_internal

  #tag_simp_range "e" 1226 16 6 "Poseidon2_expressions"
  #tag_simp_range "e" 1227 16 6 "Poseidon2_expressions"

  lemma state21_equiv
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row: ℕ)
  :
    state21 c row = state21' c row
  := by
    unfold state21 state21' state20
    funext x
    fin_cases x <;> (
      simp [
        Poseidon2_expressions,
        pow_three'
      ]
    )

end sbox_three_internal

-- saved sbox internal state
#define_opaque_state 22 116 1

def state22'
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Fin 16 → F :=
  λ x => state22 c row x

section sbox_state_three
  #tag_simp_range "constraint_" 96 16 1 "Poseidon2_expressions"
  #tag_simp_range "e" 116 16 1 "Poseidon2_expressions"
  #tag_simp_range "e" 1226 16 6 "Poseidon2_expressions"
  #tag_simp_range "e" 1227 16 6 "Poseidon2_expressions"
  #tag_simp_range "e" 1228 16 6 "Poseidon2_expressions"
  attribute [local simp]
    eval_sbox_7_1
    round_constants
    beginning_full_rounds
    state20

  #prove_eval_sbox_constraints 96 3 20 16
end sbox_state_three

-- sbox result
#define_opaque_state 23 1230 6

def state23'
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Fin 16 → F :=
  λ x => state20 c row x ^ 7

#define_constraint_group "full_round_3_sbox_constraints" 96 16

section sbox_three_external

  #tag_simp_range "constraint_equiv_" 96 16 1 "Poseidon2_constraints"
  #tag_simp_range "e" 116 16 1 "Poseidon2_expressions"
  #tag_simp_range "e" 1229 16 6 "Poseidon2_expressions"
  #tag_simp_range "e" 1230 16 6 "Poseidon2_expressions"

  lemma state23_equiv
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row: ℕ)
    (h: full_round_3_sbox_constraints c row)
  :
    state23 c row = state23' c row
  := by
    unfold state23 state23' state20
    funext x
    have (x: F) : x * x * x * (x * x * x) * x = x^7 := by grind
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
    simp [
      Poseidon2_constraints,
      eval_sbox_7_1,
      beginning_full_rounds,
      state20,
      sub_eq_zero
    ] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
    fin_cases x <;> (
      simp [
        Poseidon2_expressions,
        h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
        this
      ]
    )

end sbox_three_external

-- After external linear layer
#define_opaque_state 24 1377 1

def state24'
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Fin 16 → F :=
  mds_light_permutation (state23 c row)

section external_linear_layer_three

  lemma state24_equiv
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row: ℕ)
  :
    state24 c row = state24' c row
  := by
    unfold state24 state24' mds_light_permutation
    funext x
    fin_cases x
    all_goals (
      simp [
        Poseidon2_expressions,
        state23, apply_m4_sums, apply_m4_loop, apply_m4
      ]
      congr
    )
end external_linear_layer_three

-- Round 3 post
#define_opaque_state 25 1377 1

def state25'
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Fin 16 → F :=
  λ x => (Circuit.main c (129 + x.val) row 0)

#define_constraint_group "full_round_3_post_constraints" 112 16

section full_round_3_post

  #tag_simp_range "constraint_" 112 16 1 "Poseidon2_expressions"
  #tag_simp_range "e" 132 16 1 "Poseidon2_expressions"
  #tag_simp_range "e" 1393 16 1 "Poseidon2_expressions"
  attribute [local simp]
    eval_sbox_7_1
    beginning_full_rounds
    state25
    sub_eq_zero

  #prove_full_round_post_constraints 112 3 25 16

  lemma state25_equiv
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row: ℕ)
    (h: full_round_3_post_constraints c row)
  :
    state25 c row = state25' c row
  := by
    unfold state25 state25'
    funext x
    simp [
      full_round_3_post_constraints,
      Poseidon2_expressions,
      sub_eq_zero
    ] at h
    obtain ⟨h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩ := h
    fin_cases x <;> (
      simp [
        Poseidon2_expressions,
        h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31
      ]
    )
end full_round_3_post

def full_round_3_constraints
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Prop :=
  full_round_3_sbox_constraints c row ∧
  full_round_3_post_constraints c row

lemma full_round_3
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
  (h2: full_round_2_constraints c row)
  (h3: full_round_3_constraints c row)
:
  (beginning_full_rounds c row 3).post =
  full_round (
    (beginning_full_rounds c row 2).post
  ) 3
:= by
  have ⟨h_sbox2, h_post2⟩ := h2
  have ⟨h_sbox3, h_post3⟩ := h3

  have := state19_equiv c row h_post2
  unfold state19' at this
  unfold beginning_full_rounds
  simp
  rewrite [←this]; clear this

  have := state20_equiv c row h_post2
  unfold state20' at this
  unfold full_round add_round_constants
  rewrite [←this]; clear this

  have := state23_equiv c row h_sbox3
  unfold state23' at this
  unfold apply_full_round_sbox
  rewrite [←this]; clear this

  have := state24_equiv c row
  unfold state24' at this
  rewrite [←this]; clear this

  have := state25_equiv c row h_post3
  unfold state25' at this
  rewrite [←this]; clear this

  rfl

lemma beginning_full_rounds_equiv
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c: C F ExtF) (row: ℕ)
  (h0: full_round_0_constraints c row)
  (h1: full_round_1_constraints c row)
  (h2: full_round_2_constraints c row)
  (h3: full_round_3_constraints c row)
:
  (beginning_full_rounds c row 3).post =
  full_round (
    full_round (
      full_round (
        full_round (
          mds_light_permutation (
            inputs c row
          )
        ) 0
      ) 1
    ) 2
  ) 3
:= by
  rw [
    ←full_round_0 c row h0,
    ←full_round_1 c row h0 h1,
    ←full_round_2 c row h1 h2,
    ←full_round_3 c row h2 h3
  ]











-------------------------------------------------------


-- -- After adding round constants
-- def state6
--   [Field F] [Field ExtF] [Circuit F ExtF C]
--   (c : C F ExtF) (row: ℕ)
-- : Fin 16 → F :=
--   λ x => state5 c row x + round_constants 1 x

-- -- After sbox
-- def state7
--   [Field F] [Field ExtF] [Circuit F ExtF C]
--   (c : C F ExtF) (row: ℕ)
-- : Fin 16 → F :=
--   λ x => state6 c row x ^ 7

-- -- After external linear layer
-- #define_opaque_state 8 1009

-- -- Round 1 post
-- def state9
--   [Field F] [Field ExtF] [Circuit F ExtF C]
--   (c : C F ExtF) (row: ℕ)
-- : Fin 16 → F :=
--   λ x => (Circuit.main c (65 + x.val) row 0)

-- -- After adding round constants
-- def state10
--   [Field F] [Field ExtF] [Circuit F ExtF C]
--   (c : C F ExtF) (row: ℕ)
-- : Fin 16 → F :=
--   λ x => state9 c row x + round_constants 2 x

-- -- After sbox
-- def state11
--   [Field F] [Field ExtF] [Circuit F ExtF C]
--   (c : C F ExtF) (row: ℕ)
-- : Fin 16 → F :=
--   λ x => state10 c row x ^ 7

-- -- After external linear layer
-- #define_opaque_state 12 1193

-- -- Round 1 post
-- def state13
--   [Field F] [Field ExtF] [Circuit F ExtF C]
--   (c : C F ExtF) (row: ℕ)
-- : Fin 16 → F :=
--   λ x => (Circuit.main c (97 + x.val) row 0)

-- -- After adding round constants
-- def state14
--   [Field F] [Field ExtF] [Circuit F ExtF C]
--   (c : C F ExtF) (row: ℕ)
-- : Fin 16 → F :=
--   λ x => state13 c row x + round_constants 3 x

-- -- After sbox
-- def state15
--   [Field F] [Field ExtF] [Circuit F ExtF C]
--   (c : C F ExtF) (row: ℕ)
-- : Fin 16 → F :=
--   λ x => state14 c row x ^ 7

-- -- After external linear layer
-- #define_opaque_state 16 1377


-- section Full_round_1_sbox

--   #tag_simp_range "constraint_" 32 16 1
--   #tag_simp_range "e" 36 16 1
--   #tag_simp_range "e" 52 16 1
--   #tag_simp_range "e" 857 16 6
--   #tag_simp_range "e" 858 16 6
--   #tag_simp_range "e" 859 16 6
--   #tag_simp_range "e" 860 16 6
--   attribute [local simp]
--     eval_sbox_7_1
--     round_constants
--     beginning_full_rounds
--     state5
--     state6

--   #prove_eval_sbox_constraints 32 1 6 16
-- end Full_round_1_sbox

-- section Full_round_2_sbox

--   #tag_simp_range "constraint_" 64 16 1
--   #tag_simp_range "e" 68 16 1
--   #tag_simp_range "e" 84 16 1
--   #tag_simp_range "e" 1041 16 6
--   #tag_simp_range "e" 1042 16 6
--   #tag_simp_range "e" 1043 16 6
--   #tag_simp_range "e" 1044 16 6
--   attribute [local simp]
--     eval_sbox_7_1
--     round_constants
--     beginning_full_rounds
--     state9
--     state10

--   #prove_eval_sbox_constraints 64 2 10 16
-- end Full_round_2_sbox

-- section Full_round_3_sbox

--   #tag_simp_range "constraint_" 96 16 1
--   #tag_simp_range "e" 100 16 1
--   #tag_simp_range "e" 116 16 1
--   #tag_simp_range "e" 1225 16 6
--   #tag_simp_range "e" 1226 16 6
--   #tag_simp_range "e" 1227 16 6
--   #tag_simp_range "e" 1228 16 6
--   attribute [local simp]
--     eval_sbox_7_1
--     round_constants
--     beginning_full_rounds
--     state13
--     state14

--   #prove_eval_sbox_constraints 96 3 14 16
-- end Full_round_3_sbox


-- section Full_round_1_post

--   #tag_simp_range "constraint_" 48 16 1
--   #tag_simp_range "e" 68 16 1
--   #tag_simp_range "e" 1025 16 1
--   attribute [local simp]
--     eval_sbox_7_1
--     beginning_full_rounds
--     state8
--     sub_eq_zero

--   #prove_full_round_post_constraints 48 1 8 16
-- end Full_round_1_post

-- section Full_round_2_post

--   #tag_simp_range "constraint_" 80 16 1
--   #tag_simp_range "e" 100 16 1
--   #tag_simp_range "e" 1209 16 1
--   attribute [local simp]
--     eval_sbox_7_1
--     beginning_full_rounds
--     state12
--     sub_eq_zero

--   #prove_full_round_post_constraints 80 2 12 16
-- end Full_round_2_post

-- section Full_round_3_post

--   #tag_simp_range "constraint_" 112 16 1
--   #tag_simp_range "e" 132 16 1
--   #tag_simp_range "e" 1393 16 1
--   attribute [local simp]
--     eval_sbox_7_1
--     beginning_full_rounds
--     state16
--     sub_eq_zero

--   #prove_full_round_post_constraints 112 3 16 16
-- end Full_round_3_post

end Poseidon2.Folding
