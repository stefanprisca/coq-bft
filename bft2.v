Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Export Coq.Strings.String.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Maps.
Require Import String.
Require Import Maps.
Open Scope string_scope.
Require Import Coq.omega.Omega.


Definition ReplicaId := string.

Inductive Replica : Set :=
| FaultyReplica : ReplicaId -> Replica
| NFReplica : ReplicaId -> Replica.

Definition IsNonFaulty (r:Replica) :  Prop :=
  match r with 
    | FaultyReplica _ => False
    | NFReplica _ => True
  end.

Definition State := list (Replica * (list nat)).

Definition ReplicaFun := total_map nat -> State -> State.

Definition nfrValue := 0.
Definition faultyValue := 100.

Fixpoint multicast (st:State) (v:nat) :=
  match st with
  | nil  => nil
  | (r, msgs)::t => (r, v::msgs)::(multicast t v)
  end.

Definition NFReplicaFun (id : ReplicaId) (msgs: total_map nat) (st:State) :=
       multicast st (msgs id).

Definition FaultyReplicaFun (id : ReplicaId) (msgs: total_map nat) (st:State) :=
       multicast st faultyValue.

Definition GetReplicaFun (r:Replica) : ReplicaFun :=
  match r with
  | FaultyReplica id => FaultyReplicaFun id
  | NFReplica id => NFReplicaFun id
  end.

Definition System := list Replica.

Fixpoint countNFR_state (st:State) :=
match st with
  | nil  => 0
  | (NFReplica _, _)::t => S (countNFR_state t)
  | _::t => countNFR_state t
  end.

Fixpoint countNFR_system (sys:System) :=
match sys with
  | nil  => 0
  | (NFReplica _)::t => S (countNFR_system t)
  | _::t => countNFR_system t
  end.


Fixpoint count_state (st:State) :=
match st with
  | nil  => 0
  | _::t => S (count_state t)
  end.


Fixpoint count_system (sys:System) :=
match sys with
  | nil  => 0
  | _::t => S (count_system t)
  end.

Definition initState (sys:list Replica) : State := ( (map (fun r => (r, nil)) sys)).

Definition newPrePrep (msgs : total_map nat) (r: Replica) : total_map nat := 
    match r with 
    | NFReplica id => msgs & {id --> nfrValue}
    | FaultyReplica id => msgs & {id --> nfrValue}
    end.

Definition prePrep (sys:list Replica) := 
    ( (fold_left newPrePrep sys (t_empty nfrValue) )).
Compute prePrep [(FaultyReplica "0"); (NFReplica "1")].


Fixpoint ReplicateRequest (sys : System) (msgs: total_map nat) (st : State):=
match sys with
  | nil => st
  | (r::sys') => (GetReplicaFun r) msgs (ReplicateRequest sys' msgs st)
  end.

Lemma faultyR_countNFR : forall (st:State) (id:ReplicaId) (prePrep : total_map nat),
       countNFR_state (FaultyReplicaFun id prePrep st) = countNFR_state st.
Proof. intros.
  induction st.
    - reflexivity.
    - destruct a. destruct r; simpl; rewrite <- IHst; reflexivity.
Qed.

Lemma nfR_countNFR : forall (st:State) (id:ReplicaId)
                            (prePrep : total_map nat),
       countNFR_state (NFReplicaFun id prePrep st) = countNFR_state st.
Proof. intros.
  induction st.
    - simpl. reflexivity.
    - destruct a. destruct r; simpl; rewrite <- IHst; reflexivity.
Qed.

Lemma initSt_nfrTrans : forall (sys:System),
    countNFR_state (initState sys) = countNFR_system sys.
Proof.
intros. induction sys.
  - auto.
  - destruct a; simpl; rewrite IHsys; auto.
Qed.

Lemma replicate_nfrTrans : forall (sys:System) (msgs : total_map nat) (st:State) ,
   countNFR_state (ReplicateRequest sys msgs st) = countNFR_state st.
Proof. intros sys. induction sys.
  - auto.
  - destruct a.
    + intros. simpl. rewrite faultyR_countNFR. apply IHsys.
    + intros. simpl. rewrite nfR_countNFR. apply IHsys.
Qed.

Lemma countNFR_state_system : forall sys:System,
    countNFR_system sys = countNFR_state (ReplicateRequest sys (prePrep sys) (initState sys)).
Proof. intros. induction sys.
  - reflexivity.
  - destruct a.
    + simpl. rewrite IHsys. 
      rewrite (replicate_nfrTrans sys (prePrep sys) (initState sys)).
      rewrite faultyR_countNFR.
      rewrite (replicate_nfrTrans sys (prePrep (FaultyReplica r :: sys))
                                  ((FaultyReplica r, []) :: initState sys)).
      auto.
    + simpl. rewrite IHsys. 
      rewrite (replicate_nfrTrans sys (prePrep sys) (initState sys)).
      rewrite nfR_countNFR.
      rewrite (replicate_nfrTrans sys (prePrep (NFReplica r :: sys))
                                  ((NFReplica r, []) :: initState sys)).
      auto.
Qed.


Definition CorrectSystem (sys:System) := 
    exists F,
    (count_system sys = 3*F+1) /\ (countNFR_system sys = 2*F+1).

Definition CorrectState (st:State) := 
    exists F,
    (count_state st = 3*F+1) /\ (countNFR_state st = 2*F+1).

Axiom PrimaryNonFaulty : forall (sys:System) (msgs : total_map nat),
     msgs = prePrep sys -> forall (id : ReplicaId), msgs id = nfrValue.

(* 
Fixpoint nfrSubState (st:State) :=
match st with
  | nil => nil
  | (NFReplica id, msgs)::t => (NFReplica id, msgs)::(nfrSubState t)
  | _::t => (nfrSubState t)
end.

Lemma nfrSubstate_countCerts : forall (st:State),
  GatherCertificates st = GatherCertificates (nfrSubState st).
Admitted. *)

Fixpoint countNFR_msgs msgs :=
match msgs with
| nil => 0
| v::t => if (beq_nat v nfrValue) then ( (countNFR_msgs t ) + 1)
          else (countNFR_msgs t )
end.

Fixpoint nfrMsgsIncrementedBy (st1 st2 : State) (n : nat) :=
match st1, st2 with
| nil, _ => True
| (_, m1)::t1 , nil => (countNFR_msgs m1) = n /\ nfrMsgsIncrementedBy t1 nil n
| (_, m1)::t1, (_, m2)::t2 => (countNFR_msgs m1) = ((countNFR_msgs m2) + n)
                                /\ nfrMsgsIncrementedBy t1 t2 n
end.

(* 
Lemma multicast_nfrvInc : forall (st : State),
    nfrMsgsIncrementedBy (multicast st nfrValue) st 1.
Proof.
intros. induction st.
- reflexivity.
- destruct a. simpl. split. { auto. } { assumption. }
Qed.


Lemma nfrIncNfrMsgs : forall (sys : System) (r:Replica),
IsNonFaulty r 
  -> nfrMsgsIncrementedBy (ReplicateRequest (r::sys) (prePrep (r::sys)) ( initState (r::sys) ))
                  (ReplicateRequest (sys) (prePrep (r::sys)) ( initState (r::sys) ))
                  1.
Proof. intros.
  destruct r.
    - inversion H.
    - simpl. unfold NFReplicaFun. 
      rewrite (PrimaryNonFaulty (NFReplica r :: sys) (prePrep (NFReplica r :: sys))). 
      apply multicast_nfrvInc. reflexivity.
Qed. *)

Lemma n_Sn : forall n:nat,
  n + 1 = S n.
Proof.
  apply nat_ind.
  - reflexivity.
  - simpl. intros. rewrite H. reflexivity.
Qed.

Lemma multicastNFV_nfrMsgsInc : forall (st base : State) (n:nat),
    nfrMsgsIncrementedBy st base n
      -> nfrMsgsIncrementedBy (multicast st nfrValue) base ( S n ).
Proof. intros st. induction st; intros; destruct base.
  - simpl. auto.
  - simpl. auto.
  - destruct a. simpl in H. simpl. destruct H. admit.
  - destruct a. destruct p. simpl in H. destruct H. simpl. split.
    + symmetry. rewrite <- n_Sn. rewrite plus_assoc. rewrite H. auto.
    + apply IHst. apply H0.
Admitted. 
 

Lemma multicastFV_nfrMsgsConst : forall (st base : State) (n:nat),
nfrMsgsIncrementedBy st base n
      -> nfrMsgsIncrementedBy (multicast st faultyValue) base n.
Proof.
intros st. simpl. induction st.
  - intros. simpl. auto.
  - intros. destruct a. destruct base.
    + simpl. simpl in H. admit.
    + destruct p. simpl. simpl in H. destruct H. split.
      { apply H. } { apply IHst. apply H0. } 
Admitted.

Lemma replicateReq_nfrMsgsTrans : forall sys,
    nfrMsgsIncrementedBy
              (ReplicateRequest sys (prePrep sys) (initState sys))
              (initState sys) (countNFR_system sys)
    -> forall r:Replica,
        nfrMsgsIncrementedBy
          (ReplicateRequest sys (prePrep (r :: sys))
             ((r, []) :: initState sys))
             ((r, []) :: initState sys) (countNFR_system sys).
Proof. Admitted.
 
Lemma blublap: forall (st base : State) (r1 r2 : Replica) (l1 l2 : list nat) (n : nat),
  nfrMsgsIncrementedBy ((r1, l1) :: st) ((r2, l2) :: base) n
  -> countNFR_msgs l2 = (countNFR_msgs l1) - n.
Admitted.

(* 
Lemma nfr_nfrEq : forall (st base : State) (r : ReplicaId)  (l :list nat),
  nfrMsgsIncrementedBy st ((NFReplica r, l) :: base) (countNFR_state st)
    -> nfrMsgsIncrementedBy st base (S (countNFR_state st)).
Proof. intros. induction st.
  - simpl. auto.
  - destruct a. inversion H. destruct base.
    + simpl. auto.
    + destruct r0; destruct p eqn:eqd.
      { simpl. split. 
        - simpl in H0. simpl in H1. rewrite H0.
Admitted. *)
(* 

Lemma nfrIncrementTrans : forall (st base:State) (r:Replica) (msgs : list nat),
    countNFR_msgs msgs = countNFR_state ((r, msgs) :: st) 
    ->
      nfrMsgsIncrementedBy (st) base
        (countNFR_state (st))
       <-> nfrMsgsIncrementedBy ((r, msgs) :: st) base
          (countNFR_state ((r, msgs) :: st)).
Proof. intros. split.
  - intros. destruct r.
    + simpl. destruct base; auto. destruct p. simpl in H0. split.
      { simpl in H. admit. } 
      { simpl in H. admit. }
    + destruct base. 
      { simpl. auto. }
      { destruct p. simpl. simpl in H. destruct r0. 
        - split.
          + admit.
          + admit.
        - split.
          + admit.
          + admit.
       }
  - intros. Admitted. *)

Lemma procReq_nfrInc: forall (sys :System),
    nfrMsgsIncrementedBy (ReplicateRequest sys (prePrep sys) ( initState sys))
                            (initState sys)
                            (countNFR_system sys).
Proof.
intros. induction sys.
  - simpl. auto.
  - destruct a.
    + simpl. unfold FaultyReplicaFun. 
      apply multicastFV_nfrMsgsConst. apply replicateReq_nfrMsgsTrans. apply IHsys.
    + simpl. unfold NFReplicaFun. 
      rewrite (PrimaryNonFaulty (NFReplica r :: sys) (prePrep (NFReplica r :: sys))).
      {
        apply multicastNFV_nfrMsgsInc. apply replicateReq_nfrMsgsTrans. apply IHsys.
      }
      { auto. }
Qed.

Definition quorumCertified (nfrSS : State) (r: (Replica * list nat)) :=
    match r with
    | (NFReplica _, msgs) => countNFR_msgs msgs >= countNFR_state nfrSS
    | (FaultyReplica _, _) => True
    end.

Definition LedgerAgreement (st : State) := Forall (quorumCertified st) st.

Lemma gt_Sn_n : forall (n m : nat), n >= S m -> n >= m. Admitted.
(* 
Lemma fR_LA : forall (r:ReplicaId) (l : list nat) (st:State),
  LedgerAgreement st -> LedgerAgreement ((FaultyReplica r, l) :: st).
Proof. intros. unfold LedgerAgreement. constructor.
  - simpl. auto.
  - unfold LedgerAgreement in H. unfold quorumCertified. simpl. apply H.
Qed.

Lemma nfR_LA : forall (st:State) (r:ReplicaId) (l : list nat),
  LedgerAgreement st -> LedgerAgreement ((NFReplica r, l) :: st).
Proof. 
Admitted. *)


Definition msgsGte (n : nat) (r: (Replica * list nat)) :=
    match r with
    | (FaultyReplica _, _) => True
    | (NFReplica _, msgs) => countNFR_msgs msgs >= n
    end.


Definition msgsEq (n : nat) (r: (Replica * list nat)) :=
    match r with
    | (FaultyReplica _, _) => True
    | (NFReplica _, msgs) => countNFR_msgs msgs = n
    end.

Lemma blublap1 : forall (st base : State) (l l0 : list nat) (n : nat)  (r r0 : Replica),
  Forall (msgsEq 0) ((r0, l0) :: base)
  -> nfrMsgsIncrementedBy ((r, l) :: st) ((r0, l0) :: base) n
  -> nfrMsgsIncrementedBy st ((r0, l0) :: base) n.
Proof. intros. induction H.
  - induction H0. auto.
  - intros. destruct x. induction H0. destruct st.
    + simpl. auto.
    + admit.
Admitted.

Lemma nfrIncN_nfrMsgs : forall (st base: State) (n : nat),
  nfrMsgsIncrementedBy st base n
    -> Forall (msgsGte n) st.
Proof. intros st. induction st.
  - constructor.
  - intros. constructor.
    + destruct a. simpl in H. simpl. destruct base.
      { destruct H. rewrite H. destruct r; auto. }
      { destruct p. destruct H. rewrite H. admit. }
    + apply (IHst base n). destruct base.
      { destruct a. induction H. apply H0. }
      { 
        destruct a. destruct p.  apply (blublap1 st base l l0 n r r0).
        { admit. } { apply H. }
      }
Admitted.

Lemma quorumCertifiedState : forall (st base : State),
    nfrMsgsIncrementedBy st base (countNFR_state st)
    -> LedgerAgreement st.
Proof.
  intros. unfold LedgerAgreement. unfold quorumCertified. 
      remember (countNFR_state (st)) as n. 
      apply (nfrIncN_nfrMsgs st base n). apply H.
Qed.

Lemma BFT : forall (sys:System),
      LedgerAgreement (ReplicateRequest sys (prePrep sys) (initState sys)).
Proof.
  intros. apply (quorumCertifiedState (ReplicateRequest sys (prePrep sys) (initState sys)) (initState sys)).
    rewrite <- countNFR_state_system. apply procReq_nfrInc.
Qed.
