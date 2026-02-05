import Poseidon2Fv.Folding
import Poseidon2Fv.FullRound0

open Plonky3
open Poseidon2.Extraction
open Poseidon2.Folding

-- After adding round constants
#define_opaque_state 8 857 6

def state8'
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Fin 16 → F :=
  λ x => state7 c row x + beginning_full_round_constants 1 x

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
    beginning_full_round_constants
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
  beginning_full_round (
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
  unfold beginning_full_round add_beginning_full_round_constants
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
