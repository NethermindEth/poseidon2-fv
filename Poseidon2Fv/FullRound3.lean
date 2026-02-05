
import Poseidon2Fv.Folding
import Poseidon2Fv.FullRound2

open Plonky3
open Poseidon2.Extraction
open Poseidon2.Folding

-- After adding round constants
#define_opaque_state 20 1225 6

def state20'
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Fin 16 → F :=
  λ x => state19 c row x + beginning_full_round_constants 3 x

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
    beginning_full_round_constants
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
  beginning_full_round (
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
  unfold beginning_full_round add_beginning_full_round_constants
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
  beginning_full_round (
    beginning_full_round (
      beginning_full_round (
        beginning_full_round (
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
