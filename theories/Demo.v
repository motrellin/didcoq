From DidCoq Require Export PropLogic.

Parameters A B C : Prop.

Goal (~ A \/ B) -> ((~ C \/ ~ B) /\ A) -> ~ (B -> C).
Proof.
  impl_I.
  impl_I.
  neg_I.

  or_E.
  -
    exact H.
  -
    bot_I.
    +
      and_E2.
      exact H0.
    +
      exact H2.
  -
    or_E.
    +
      and_E1.
      exact H0.
    +
      bot_I.
      *
        impl_E.
        --
           exact H2.
        --
           exact H1.
      *
        exact H3.
    +
      bot_I.
      *
        exact H2.
      *
        exact H3.

  Restart.

  impl_I.
  impl_I.
  neg_I.

  or_E.
  exact H.
  bot_I.
  and_E2.
  exact H0.
  exact H2.
  or_E.
  and_E1.
  exact H0.
  bot_I.
  impl_E.
  exact H2.
  exact H1.
  exact H3.
  bot_I.
  exact H2.
  exact H3.
Qed.
