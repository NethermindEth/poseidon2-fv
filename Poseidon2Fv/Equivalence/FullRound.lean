import Poseidon2Fv.Equivalence.ExternalLinearLayer

def full_round_constants [Fact P.Prime]: Array (Array (ZMod P)) :=
  Array.ofFn (λ x => Array.ofFn (Poseidon2.Folding.beginning_full_round_constants x)) ++
  Array.ofFn (λ x => Array.ofFn (Poseidon2.Folding.ending_full_round_constants x))

lemma get_beginning_full_round_constants
  (start_round: Fin 4)
  [Fact P.Prime]
:
  (@full_round_constants P _)[start_round.val]! =
  Array.ofFn (Poseidon2.Folding.beginning_full_round_constants start_round)
:= by
  fin_cases start_round <;> rfl

lemma get_ending_full_round_constants
  (ending_round: Fin 4)
  [Fact P.Prime]
:
  (@full_round_constants P _)[4 + ending_round.val]! =
  Array.ofFn (Poseidon2.Folding.ending_full_round_constants ending_round)
:= by
  fin_cases ending_round <;> rfl

lemma getFullRound_ending_round
  (ending_round: Fin 4)
:
  Poseidon2.getFullRound (25 + ending_round.val) ⟨profile, 8, 21⟩ =
  4 + ending_round.val
:= by
  simp [
    Poseidon2.getFullRound
  ]
  fin_cases ending_round <;> simp

lemma add_beginning_round_constants_equiv
  (fin_state : Fin 24 → ZMod P)
  [Fact P.Prime]
:
  ((Array.ofFn fin_state).zip
    (Array.ofFn ((Poseidon2.Folding.beginning_full_round_constants) start_round))).map (λ ⟨x1, x2⟩ => x1 + x2) =
  Array.ofFn (Poseidon2.Folding.add_beginning_full_round_constants fin_state start_round)
:= by
  apply Array.toList_inj.mp
  simp [Poseidon2.Folding.add_beginning_full_round_constants]

lemma add_ending_round_constants_equiv
  (fin_state : Fin 24 → ZMod P)
  [Fact P.Prime]
:
  ((Array.ofFn fin_state).zip
    (Array.ofFn ((Poseidon2.Folding.ending_full_round_constants) ending_round))).map (λ ⟨x1, x2⟩ => x1 + x2) =
  Array.ofFn (Poseidon2.Folding.add_ending_full_round_constants fin_state ending_round)
:= by
  apply Array.toList_inj.mp
  simp [Poseidon2.Folding.add_ending_full_round_constants]

lemma apply_full_round_sbox_equiv
  (fin_state : Fin 24 → ZMod P)
  [Fact P.Prime]
:
  Array.map (Poseidon.HashProfile.sBox ⟨⟨a, b, P, 11⟩, full_rounds, partial_rounds⟩) (Array.ofFn fin_state) =
  Array.ofFn (Poseidon2.Folding.apply_full_round_sbox fin_state)
:= by
  apply Array.toList_inj.mp
  simp [Poseidon.HashProfile.sBox, Poseidon2.Folding.apply_full_round_sbox]

lemma beginning_full_round_equiv
  [Fact P.Prime]
:
  Poseidon2.fullRound
    ⟨⟨p1, p2, P, 11⟩, 8, 21⟩
    ⟨diag, full_round_constants, partial_round_constants⟩
    ⟨start_round.val, Array.ofFn fin_state⟩
  =
    ⟨
      PUnit.unit,
      ⟨
        start_round.val + 1,
        Array.ofFn (Poseidon2.Folding.beginning_full_round fin_state start_round)
      ⟩
    ⟩
:= by
  simp [
    Poseidon2.fullRound,
    SeqRight.seqRight,
    StateT.bind,
    bind,
    Poseidon2.addFullConst,
    ReaderT.bind,
    Poseidon2.add_array
  ]
  unfold get instMonadStateOfMonadStateOf getThe MonadStateOf.get instMonadStateOfOfMonadLift liftM monadLift instMonadLiftTOfMonadLift MonadLift.monadLift ReaderT.instMonadLift monadLift instMonadLiftT MonadStateOf.get instMonadStateOfStateTOfMonad StateT.get
  dsimp
  unfold read instMonadReaderOfMonadReaderOf readThe MonadReaderOf.read instMonadReaderOfReaderTOfMonad ReaderT.read pure Applicative.toPure Monad.toApplicative StateT.instMonad StateT.pure
  dsimp
  unfold modify modifyGet instMonadStateOfMonadStateOf MonadStateOf.modifyGet StateT.modifyGet
  dsimp

  simp [
    get_beginning_full_round_constants,
    Poseidon2.getFullRound,
    -Array.map_map,
    add_beginning_round_constants_equiv
  ]
  rewrite [
    apply_full_round_sbox_equiv,
    external_linear_layer_equiv
  ]
  rfl

lemma ending_full_round_equiv
  [Fact P.Prime]
:
  Poseidon2.fullRound
    ⟨⟨p1, p2, P, 11⟩, 8, 21⟩
    ⟨diag, full_round_constants, partial_round_constants⟩
    ⟨25 + ending_round.val, Array.ofFn fin_state⟩
  =
    ⟨
      PUnit.unit,
      ⟨
        25 + ending_round.val + 1,
        Array.ofFn (Poseidon2.Folding.ending_full_round fin_state ending_round)
      ⟩
    ⟩
:= by
  simp [
    Poseidon2.fullRound,
    SeqRight.seqRight,
    StateT.bind,
    bind,
    Poseidon2.addFullConst,
    ReaderT.bind,
    Poseidon2.add_array
  ]
  unfold get instMonadStateOfMonadStateOf getThe MonadStateOf.get instMonadStateOfOfMonadLift liftM monadLift instMonadLiftTOfMonadLift MonadLift.monadLift ReaderT.instMonadLift monadLift instMonadLiftT MonadStateOf.get instMonadStateOfStateTOfMonad StateT.get
  dsimp
  unfold read instMonadReaderOfMonadReaderOf readThe MonadReaderOf.read instMonadReaderOfReaderTOfMonad ReaderT.read pure Applicative.toPure Monad.toApplicative StateT.instMonad StateT.pure
  dsimp
  unfold modify modifyGet instMonadStateOfMonadStateOf MonadStateOf.modifyGet StateT.modifyGet
  dsimp

  simp [
    getFullRound_ending_round,
    get_ending_full_round_constants,
    add_ending_round_constants_equiv,
  ]

  rewrite [
    apply_full_round_sbox_equiv,
    external_linear_layer_equiv
  ]
  rfl
