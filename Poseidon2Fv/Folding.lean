import LeanZKCircuit_Plonky3.Plonky3.Command.util
import Poseidon2Fv.Extraction
import Poseidon2Fv.Tactics

open Plonky3 Poseidon2.Extraction

namespace Poseidon2.Folding

def eval_sbox_11_2_A [Field F] (x3 x : F) : Prop :=
  x3 - ((x * x) * x) = 0

def eval_sbox_11_2_B [Field F] (x9 x3 : F) : Prop :=
  x9 - (x3 ^ 3) = 0

def apply_full_round_sbox [Field F] (state: Fin 24 → F) : Fin 24 → F :=
  λ x => state x ^ 11

def apply_partial_round_sbox [Field F] (state: Fin 24 → F) : Fin 24 → F
  | 0 => state 0 ^ 11
  | x => state x

def apply_m4 [Field F] (state: Fin 24 → F) (idx: Fin 24) : Fin 4 → F :=
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

def apply_m4_loop [Field F] (state : Fin 24 → F) : Fin 24 → F
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
  | 16 => apply_m4 state 14 0
  | 17 => apply_m4 state 14 1
  | 18 => apply_m4 state 14 2
  | 19 => apply_m4 state 14 3
  | 20 => apply_m4 state 16 0
  | 21 => apply_m4 state 16 1
  | 22 => apply_m4 state 16 2
  | 23 => apply_m4 state 16 3
  | ⟨_ + 24, _⟩ => by exfalso; omega

def apply_m4_sums [Field F] (state : Fin 24 → F) : Fin 4 → F
  | 0 => (apply_m4_loop state 0) + (apply_m4_loop state 4) + (apply_m4_loop state 8) + (apply_m4_loop state 12) + (apply_m4_loop state 16) + (apply_m4_loop state 20)
  | 1 => (apply_m4_loop state 1) + (apply_m4_loop state 5) + (apply_m4_loop state 9) + (apply_m4_loop state 13) + (apply_m4_loop state 17) + (apply_m4_loop state 21)
  | 2 => (apply_m4_loop state 2) + (apply_m4_loop state 6) + (apply_m4_loop state 10) + (apply_m4_loop state 14) + (apply_m4_loop state 18) + (apply_m4_loop state 22)
  | 3 => (apply_m4_loop state 3) + (apply_m4_loop state 7) + (apply_m4_loop state 11) + (apply_m4_loop state 15) + (apply_m4_loop state 19) + (apply_m4_loop state 23)

def mds_light_permutation [Field F] (state : Fin 24 → F) : Fin 24 → F
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
  | 16 =>apply_m4_loop state 16 + apply_m4_sums state 0
  | 17 =>apply_m4_loop state 17 + apply_m4_sums state 1
  | 18 =>apply_m4_loop state 18 + apply_m4_sums state 2
  | 19 =>apply_m4_loop state 19 + apply_m4_sums state 3
  | 20 =>apply_m4_loop state 20 + apply_m4_sums state 0
  | 21 =>apply_m4_loop state 21 + apply_m4_sums state 1
  | 22 =>apply_m4_loop state 22 + apply_m4_sums state 2
  | 23 =>apply_m4_loop state 23 + apply_m4_sums state 3
  | ⟨_ + 24, _⟩ => by exfalso; omega

-- BabyBearInternalLayerParameters::
def internal_layer_mat_mul [Field F] (state : Fin 24 → F) (sum : F) : Fin 24 → F
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
  -- state[15] = state[15].div_2exp_u64(27);
  -- state[15] += sum.clone();
  | 15 => sum - state 15 / (2 ^ 27)
  -- state[16] = state[16].div_2exp_u64(8);
  -- state[16] = sum.clone() - state[16].clone();      
  | 16 => sum - state 16 / (2 ^ 8)
  -- state[17] = state[17].div_2exp_u64(2);
  -- state[17] = sum.clone() - state[17].clone();
  | 17 => sum - state 17 / (2 ^ 2)
  -- state[18] = state[18].div_2exp_u64(3);
  -- state[18] = sum.clone() - state[18].clone();
  | 18 => sum - state 18 / (2 ^ 3)
  -- state[19] = state[19].div_2exp_u64(4);
  -- state[19] = sum.clone() - state[19].clone();
  | 19 => sum - state 19 / (2 ^ 4)
  -- state[20] = state[20].div_2exp_u64(5);
  -- state[20] = sum.clone() - state[20].clone();
  | 20 => sum - state 20 / (2 ^ 5)
  -- state[21] = state[21].div_2exp_u64(6);
  -- state[21] = sum.clone() - state[21].clone();
  | 21 => sum - state 21 / (2 ^ 6)
  -- state[22] = state[22].div_2exp_u64(7);
  -- state[22] = sum.clone() - state[22].clone();
  | 22 => sum - state 22 / (2 ^ 7)
  -- state[23] = state[23].div_2exp_u64(27);
  -- state[23] = sum.clone() - state[23].clone();
  | 23 => sum - state 23 / (2 ^ 27)
  | ⟨_ + 24, _⟩ => by exfalso; omega

-- InternalLayerBaseParameters::
def generic_internal_linear_layer [Field F] (state : Fin 24 → F) : Fin 24 → F :=
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
    state 15 +
    state 16 +
    state 17 +
    state 18 +
    state 19 +
    state 20 +
    state 21 +
    state 22 +
    state 23
  let state' := λ x => match x with
    | 0 => part_sum - state 0
    | x => state x
  internal_layer_mat_mul state' (part_sum + state 0)

def beginning_full_round_constants [Field F] : Fin 4 → Fin 24 → F
  | 0, 0 => 0x0fa20c37
  | 0, 1 => 0x0795bb97
  | 0, 2 => 0x12c60b9c
  | 0, 3 => 0x0eabd88e
  | 0, 4 => 0x096485ca
  | 0, 5 => 0x07093527
  | 0, 6 => 0x1b1d4e50
  | 0, 7 => 0x30a01ace
  | 0, 8 => 0x3bd86f5a
  | 0, 9 => 0x69af7c28
  | 0, 10 => 0x3f94775f
  | 0, 11 => 0x731560e8
  | 0, 12 => 0x465a0ecd
  | 0, 13 => 0x574ef807
  | 0, 14 => 0x62fd4870
  | 0, 15 => 0x52ccfe44
  | 0, 16 => 0x14772b14
  | 0, 17 => 0x4dedf371
  | 0, 18 => 0x260acd7c
  | 0, 19 => 0x1f51dc58
  | 0, 20 => 0x75125532
  | 0, 21 => 0x686a4d7b
  | 0, 22 => 0x54bac179
  | 0, 23 => 0x31947706
  | 1, 0 => 0x29799d3b
  | 1, 1 => 0x6e01ae90
  | 1, 2 => 0x203a7a64
  | 1, 3 => 0x4f7e25be
  | 1, 4 => 0x72503f77
  | 1, 5 => 0x45bd3b69
  | 1, 6 => 0x769bd6b4
  | 1, 7 => 0x5a867f08
  | 1, 8 => 0x4fdba082
  | 1, 9 => 0x251c4318
  | 1, 10 => 0x28f06201
  | 1, 11 => 0x6788c43a
  | 1, 12 => 0x4c6d6a99
  | 1, 13 => 0x357784a8
  | 1, 14 => 0x2abaf051
  | 1, 15 => 0x770f7de6
  | 1, 16 => 0x1794b784
  | 1, 17 => 0x4796c57a
  | 1, 18 => 0x724b7a10
  | 1, 19 => 0x449989a7
  | 1, 20 => 0x64935cf1
  | 1, 21 => 0x59e14aac
  | 1, 22 => 0x0e620bb8
  | 1, 23 => 0x3af5a33b
  | 2, 0 => 0x4465cc0e
  | 2, 1 => 0x019df68f
  | 2, 2 => 0x4af8d068
  | 2, 3 => 0x08784f82
  | 2, 4 => 0x0cefdeae
  | 2, 5 => 0x6337a467
  | 2, 6 => 0x32fa7a16
  | 2, 7 => 0x486f62d6
  | 2, 8 => 0x386a7480
  | 2, 9 => 0x20f17c4a
  | 2, 10 => 0x54e50da8
  | 2, 11 => 0x2012cf03
  | 2, 12 => 0x5fe52950
  | 2, 13 => 0x09afb6cd
  | 2, 14 => 0x2523044e
  | 2, 15 => 0x5c54d0ef
  | 2, 16 => 0x71c01f3c
  | 2, 17 => 0x60b2c4fb
  | 2, 18 => 0x4050b379
  | 2, 19 => 0x5e6a70a5
  | 2, 20 => 0x418543f5
  | 2, 21 => 0x71debe56
  | 2, 22 => 0x1aad2994
  | 2, 23 => 0x3368a483
  | 3, 0 => 0x07a86f3a
  | 3, 1 => 0x5ea43ff1
  | 3, 2 => 0x2443780e
  | 3, 3 => 0x4ce444f7
  | 3, 4 => 0x146f9882
  | 3, 5 => 0x3132b089
  | 3, 6 => 0x197ea856
  | 3, 7 => 0x667030c3
  | 3, 8 => 0x2317d5dc
  | 3, 9 => 0x0c2c48a7
  | 3, 10 => 0x56b2df66
  | 3, 11 => 0x67bd81e9
  | 3, 12 => 0x4fcdfb19
  | 3, 13 => 0x4baaef32
  | 3, 14 => 0x0328d30a
  | 3, 15 => 0x6235760d
  | 3, 16 => 0x12432912
  | 3, 17 => 0x0a49e258
  | 3, 18 => 0x030e1b70
  | 3, 19 => 0x48caeb03
  | 3, 20 => 0x49e4d9e9
  | 3, 21 => 0x1051b5c6
  | 3, 22 => 0x6a36dbbe
  | 3, 23 => 0x4cff27a5
  | 0, ⟨_ + 24, _⟩ => by exfalso; omega
  | 1, ⟨_ + 24, _⟩ => by exfalso; omega
  | 2, ⟨_ + 24, _⟩ => by exfalso; omega
  | 3, ⟨_ + 24, _⟩ => by exfalso; omega
 

def ending_full_round_constants [Field F] : Fin 4 → Fin 24 → F
  | 0, 0 => 0x032959ad
  | 0, 1 => 0x2b18af6a
  | 0, 2 => 0x55d3dc8c
  | 0, 3 => 0x43bd26c8
  | 0, 4 => 0x0c41595f
  | 0, 5 => 0x7048d2e2
  | 0, 6 => 0x00db8983
  | 0, 7 => 0x2af563d7
  | 0, 8 => 0x6e84758f
  | 0, 9 => 0x611d64e1
  | 0, 10 => 0x1f9977e2
  | 0, 11 => 0x64163a0a
  | 0, 12 => 0x5c5fc27b
  | 0, 13 => 0x02e22561
  | 0, 14 => 0x3a2d75db
  | 0, 15 => 0x1ba7b71a
  | 0, 16 => 0x34343f64
  | 0, 17 => 0x7406b35d
  | 0, 18 => 0x19df8299
  | 0, 19 => 0x6ff4480a
  | 0, 20 => 0x514a81c8
  | 0, 21 => 0x57ab52ce
  | 0, 22 => 0x6ad69f52
  | 0, 23 => 0x3e0c0e0d
  | 1, 0 => 0x48126114
  | 1, 1 => 0x2a9d62cc
  | 1, 2 => 0x17441f23
  | 1, 3 => 0x485762bb
  | 1, 4 => 0x2f218674
  | 1, 5 => 0x06fdc64a
  | 1, 6 => 0x0861b7f2
  | 1, 7 => 0x3b36eee6
  | 1, 8 => 0x70a11040
  | 1, 9 => 0x04b31737
  | 1, 10 => 0x3722a872
  | 1, 11 => 0x2a351c63
  | 1, 12 => 0x623560dc
  | 1, 13 => 0x62584ab2
  | 1, 14 => 0x382c7c04
  | 1, 15 => 0x3bf9edc7
  | 1, 16 => 0x0e38fe51
  | 1, 17 => 0x376f3b10
  | 1, 18 => 0x5381e178
  | 1, 19 => 0x3afc61c7
  | 1, 20 => 0x5c1bcb4d
  | 1, 21 => 0x6643ce1f
  | 1, 22 => 0x2d0af1c1
  | 1, 23 => 0x08f583cc
  | 2, 0 => 0x5d6ff60f
  | 2, 1 => 0x6324c1e5
  | 2, 2 => 0x74412fb7
  | 2, 3 => 0x70c0192e
  | 2, 4 => 0x0b72f141
  | 2, 5 => 0x4067a111
  | 2, 6 => 0x57388c4f
  | 2, 7 => 0x351009ec
  | 2, 8 => 0x0974c159
  | 2, 9 => 0x539a58b3
  | 2, 10 => 0x038c0cff
  | 2, 11 => 0x476c0392
  | 2, 12 => 0x3f7bc15f
  | 2, 13 => 0x4491dd2c
  | 2, 14 => 0x4d1fef55
  | 2, 15 => 0x04936ae3
  | 2, 16 => 0x58214dd4
  | 2, 17 => 0x683c6aad
  | 2, 18 => 0x1b42f16b
  | 2, 19 => 0x6dc79135
  | 2, 20 => 0x2d4e71ec
  | 2, 21 => 0x3e2946ea
  | 2, 22 => 0x59dce8db
  | 2, 23 => 0x6cee892a
  | 3, 0 => 0x47f07350
  | 3, 1 => 0x7106ce93
  | 3, 2 => 0x3bd4a7a9
  | 3, 3 => 0x2bfe636a
  | 3, 4 => 0x430011e9
  | 3, 5 => 0x001cd66a
  | 3, 6 => 0x307faf5b
  | 3, 7 => 0x0d9ef3fe
  | 3, 8 => 0x6d40043a
  | 3, 9 => 0x2e8f470c
  | 3, 10 => 0x1b6865e8
  | 3, 11 => 0x0c0e6c01
  | 3, 12 => 0x4d41981f
  | 3, 13 => 0x423b9d3d
  | 3, 14 => 0x410408cc
  | 3, 15 => 0x263f0884
  | 3, 16 => 0x5311bbd0
  | 3, 17 => 0x4dae58d8
  | 3, 18 => 0x30401cea
  | 3, 19 => 0x09afa575
  | 3, 20 => 0x4b3d5b42
  | 3, 21 => 0x63ac0b37
  | 3, 22 => 0x5fe5bb14
  | 3, 23 => 0x5244e9d4
  | 0, ⟨_ + 24, _⟩ => by exfalso; omega
  | 1, ⟨_ + 24, _⟩ => by exfalso; omega
  | 2, ⟨_ + 24, _⟩ => by exfalso; omega
  | 3, ⟨_ + 24, _⟩ => by exfalso; omega

def partial_round_constants [Field F] : Fin 21 → F
  | 0 => 0x1da78ec2
  | 1 => 0x730b0924
  | 2 => 0x3eb56cf3
  | 3 => 0x5bd93073
  | 4 => 0x37204c97
  | 5 => 0x51642d89
  | 6 => 0x66e943e8
  | 7 => 0x1a3e72de
  | 8 => 0x70beb1e9
  | 9 => 0x30ff3b3f
  | 10 => 0x4240d1c4
  | 11 => 0x12647b8d
  | 12 => 0x65d86965
  | 13 => 0x49ef4d7c
  | 14 => 0x47785697
  | 15 => 0x46b3969f
  | 16 => 0x5c7b7a0e
  | 17 => 0x7078fc60
  | 18 => 0x4f22d482
  | 19 => 0x482a9aee
  | 20 => 0x6beb839d
  | ⟨_ + 21, _⟩ => by exfalso; omega

def add_beginning_full_round_constants [Field F] (state: Fin 24 → F) (round : Fin 4) : Fin 24 → F :=
  λ x => state x + beginning_full_round_constants round x

def beginning_full_round [Field F] (state: Fin 24 → F) (round : Fin 4) : Fin 24 → F :=
  mds_light_permutation (
    apply_full_round_sbox (
      add_beginning_full_round_constants state round
    )
  )

def add_partial_round_constant [Field F] (state: Fin 24 → F) (round : Fin 21) : Fin 24 → F
  | 0 => state 0 + partial_round_constants round
  | x => state x

def partial_round [Field F] (state : Fin 24 → F) (round : Fin 21) : Fin 24 → F :=
  generic_internal_linear_layer (
    apply_partial_round_sbox (
      add_partial_round_constant state round
    )
  )

def add_ending_full_round_constants [Field F] (state: Fin 24 → F) (round : Fin 4) : Fin 24 → F :=
  λ x => state x + ending_full_round_constants round x

def ending_full_round [Field F] (state: Fin 24 → F) (round : Fin 4) : Fin 24 → F :=
  mds_light_permutation (
    apply_full_round_sbox (
      add_ending_full_round_constants state round
    )
  )

structure FullRound (F: Type) where
  sbox : Fin 24 → F -- WIDTH sboxes, each of which is 1 register
  post : Fin 24 → F

structure PartialRound (F: Type) where
  sbox : F -- a single one-register sbox
  post_sbox : F -- its result

def inputs
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Fin 16 → F :=
  λ x => (Circuit.main c (1 + x.val) row 0)

-- TODO: Column offsets need to change
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

def permutation [Field F] (input : Fin 24 → F) :=
  ending_full_round (
    ending_full_round (
      ending_full_round (
        ending_full_round (
          partial_round (
            partial_round (
              partial_round (
                partial_round (
                  partial_round (
                    partial_round (
                      partial_round (
                        partial_round (
                          partial_round (
                            partial_round (
                              partial_round (
                                partial_round (
                                  partial_round (
                                    partial_round (
                                      partial_round (
                                        partial_round (
                                          partial_round (
                                            partial_round (
                                              partial_round (
                                                partial_round (
                                                  partial_round (
                                                    beginning_full_round (
                                                      beginning_full_round (
                                                        beginning_full_round (
                                                          beginning_full_round (
                                                            mds_light_permutation (
                                                              input
                                                            )
                                                          ) 0
                                                        ) 1
                                                      ) 2
                                                    ) 3
                                                  ) 0
                                                ) 1
                                              ) 2
                                            ) 3
                                          ) 4
                                        ) 5
                                      ) 6
                                    ) 7
                                  ) 8
                                ) 9
                              ) 10
                            ) 11
                          ) 12
                        ) 13
                      ) 14
                    ) 15
                  ) 16
                ) 17
              ) 18
            ) 19
          ) 20
        ) 0
      ) 1
    ) 2
  ) 3

end Poseidon2.Folding
