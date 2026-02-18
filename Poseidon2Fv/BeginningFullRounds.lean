import Poseidon2Fv.Folding

open Plonky3
open Poseidon2.Extraction
open Poseidon2.Folding

-- Offsets will need to change
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

-- To find these ("2 673 6"):
--    Search for a particular round constant in Extraction.lean (written there in base 10 not hex)
--    Subexpresion before adding the round constant will be the final one from doing the matrix multiplication
--    Width-many before the round constant is the output from the previous output so far

-- How Dom figured this out (for example):
-- In Plonky3/poseidon2-air/src
-- We can look at, e.g., fn eval_sbox in air.rs
-- Click on externalLinearLayer, which takes us to poseidon2/src/generic.rs
-- Which shows how the Rust evaluates sbox

-- Round constant to round constant is the step
#define_opaque_state 2 673 6

-- After adding round constants
def state2'
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Fin 16 → F :=
  λ x => state1 c row x + beginning_full_round_constants 0 x

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

#prove_eval_sbox_constraints 0 0 2 16 "beginning"


-- sbox result
#define_opaque_state 5 678 6

def state5'
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Fin 16 → F :=
  λ x => state2 c row x ^ 7

#define_constraint_group "beginning_full_round_0_sbox_constraints" 0 16

section sbox_zero_external

  -- #tag_simp_range "constraint_equiv_" 0 16 1 "Poseidon2_constraints"
  -- #tag_simp_range "e" 20 16 1 "Poseidon2_expressions"
  -- #tag_simp_range "e" 677 16 6 "Poseidon2_expressions"
  -- #tag_simp_range "e" 678 16 6 "Poseidon2_expressions"

  lemma state5_equiv
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row: ℕ)
    (h: beginning_full_round_0_sbox_constraints c row)
  :
    state5 c row = state5' c row
  := by
    unfold state5 state5' state2
    funext x
    have (x: F) : x * x * x * (x * x * x) * x = x^7 := by grind
    simp [
      beginning_full_round_0_sbox_constraints,
      constraint_equiv_0,
      constraint_equiv_1,
      constraint_equiv_2,
      constraint_equiv_3,
      constraint_equiv_4,
      constraint_equiv_5,
      constraint_equiv_6,
      constraint_equiv_7,
      constraint_equiv_8,
      constraint_equiv_9,
      constraint_equiv_10,
      constraint_equiv_11,
      constraint_equiv_12,
      constraint_equiv_13,
      constraint_equiv_14,
      constraint_equiv_15,
      eval_sbox_7_1,
      beginning_full_rounds,
      state2,
      sub_eq_zero
    ] at h
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
    fin_cases x <;> (
      simp [
        ←this,
        ←h0, ←h1, ←h2, ←h3, ←h4, ←h5, ←h6, ←h7, ←h8, ←h9, ←h10, ←h11, ←h12, ←h13, ←h14, ←h15
      ]
      rfl
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
        -- Poseidon2_expressions,
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

#define_constraint_group "beginning_full_round_0_post_constraints" 16 16

section full_round_0_post

  -- #tag_simp_range "constraint_" 16 16 1 "Poseidon2_expressions"
  -- #tag_simp_range "e" 36 16 1 "Poseidon2_expressions"
  -- #tag_simp_range "e" 841 16 1 "Poseidon2_expressions"
  -- attribute [local simp]
  --   eval_sbox_7_1
  --   beginning_full_rounds
  --   state7
  --   sub_eq_zero

  #prove_full_round_post_constraints 16 0 7 16

  lemma state7_equiv
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row: ℕ)
    (h: beginning_full_round_0_post_constraints c row)
  :
    state7 c row = state7' c row
  := by
    unfold state7 state7'
    funext x
    simp [
      beginning_full_round_0_post_constraints,
      constraint_16,
      constraint_17,
      constraint_18,
      constraint_19,
      constraint_20,
      constraint_21,
      constraint_22,
      constraint_23,
      constraint_24,
      constraint_25,
      constraint_26,
      constraint_27,
      constraint_28,
      constraint_29,
      constraint_30,
      constraint_31,
      e841,
      e842,
      e843,
      e844,
      e845,
      e846,
      e847,
      e848,
      e849,
      e850,
      e851,
      e852,
      e853,
      e854,
      e855,
      e856,
      sub_eq_zero
    ] at h
    simp [h]
    fin_cases x <;> rfl
end full_round_0_post

def beginning_full_round_0_constraints
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Prop :=
  beginning_full_round_0_sbox_constraints c row ∧
  beginning_full_round_0_post_constraints c row

lemma beginning_full_round_0
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
  (h: beginning_full_round_0_constraints c row)
:
  (beginning_full_rounds c row 0).post =
  beginning_full_round (
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
  unfold beginning_full_round add_beginning_full_round_constants
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

#prove_beginning_full_round 1
#prove_beginning_full_round 2
#prove_beginning_full_round 3
