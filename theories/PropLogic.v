From Coq Require Export Classical.

About classic.

Ltac and_I :=
  split.

Example and_I_example (A B : Prop) (H1 : A) (H2 : B) : A /\ B.
Proof.
  and_I.
  -
    exact H1.
  -
    exact H2.
Qed.

Lemma and_E1_helper {A : Prop} : 
  {B : Prop | A /\ B} ->
  A.
Proof.
  intros [B [H1 H2]].
  exact H1.
Qed.

Ltac and_E1 :=
  apply and_E1_helper;
  eexists.

Example and_E1_example (A B : Prop) (H1 : A /\ B) : A.
Proof.
  and_E1.
  exact H1.
Qed.
  
Lemma and_E2_helper {B : Prop} : 
  {A : Prop | A /\ B} ->
  B.
Proof.
  intros [A [H1 H2]].
  exact H2.
Qed.

Ltac and_E2 :=
  apply and_E2_helper;
  eexists.

Example and_E2_example (A B : Prop) (H1 : A /\ B) : B.
Proof.
  and_E2.
  exact H1.
Qed. 

Ltac or_I1 :=
  left.

Example or_I1 (A B : Prop) (H1 : A) : A \/ B.
Proof.
  or_I1.
  exact H1.
Qed.

Ltac or_I2 :=
  right.

Example or_I2 (A B : Prop) (H1 : B) : A \/ B.
Proof.
  or_I2.
  exact H1.
Qed.

Lemma or_E_helper {C : Prop} : 
  {A : Prop & {B : Prop | (A \/ B) /\ (A -> C) /\ (B -> C)}} ->
  C.
Proof.
  intros [A [B [[H1|H1] [H2 H3]]]]; auto.
Qed.

Ltac or_E :=
  apply or_E_helper;
  do 2 eexists;
  (repeat split);
  [|intro|intro].

Example or_E (A B C : Prop) (H1 : A \/ B) (H2 : A -> C) (H3 : B -> C) : C.
Proof.
  or_E.
  -
    exact H1.
  -
    auto.
  -
    auto.
Qed.

Ltac impl_I :=
  intro.

Example impl_I {A B : Prop} (H1 : A -> B) : A -> B.
Proof.
  impl_I.
  auto.
Qed.

Lemma impl_E_helper {B : Prop} :
  {A : Prop | A /\ (A -> B)} ->
  B.
Proof.
  intros [A [H1 H2]].
  auto.
Qed.

Ltac impl_E :=
  apply impl_E_helper;
  eexists;
  split.

Example impl_E {A B : Prop} (H1 : A) (H2 : A -> B) : B.
Proof.
  impl_E.
  -
    exact H1.
  -
    exact H2.
Qed.

Lemma bot_I_helper :
  {A : Prop | A /\ ~ A } ->
  False.
Proof.
  intros [A [H1 H2]].
  contradiction.
Qed.

Ltac bot_I :=
  apply bot_I_helper;
  eexists;
  split.

Example bot_I {A : Prop} (H1 : A) (H2 : ~ A) : False.
Proof.
  bot_I.
  -
    exact H1.
  -
    exact H2.
Qed.

Ltac bot_E :=
  exfalso.

Example bot_E {A : Prop} (H1 : False) : A.
Proof.
  bot_E.
  exact H1.
Qed.

Ltac neg_I :=
  intro.

Example neg_I {A : Prop} (H1 : A -> False) : ~ A.
Proof.
  neg_I.
  auto.
Qed.

Ltac neg_E :=
  apply NNPP.

Example neg_E {A : Prop} (H1 : ~ ~ A) : A.
Proof.
  neg_E.
  exact H1.
Qed.
