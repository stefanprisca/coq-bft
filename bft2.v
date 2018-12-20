Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Export Coq.Strings.String.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Maps.
Require Coq.omega.Omega.
Require Import String.
Require Import Maps.
Open Scope string_scope.


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

Fixpoint countNFR_msgs msgs :=
match msgs with
| nil => 0
| v::t => if (beq_nat v nfrValue) then ( (countNFR_msgs t ) + 1)
          else (countNFR_msgs t )
end.

Fixpoint GatherCertificates (st:State) :=
match st with
  | nil => nil
  | (NFReplica id, msgs)::t => (countNFR_msgs msgs)::(GatherCertificates t)
  | _::t => GatherCertificates t
end.

Fixpoint incCertificates (certs : list nat):=
match certs with
| nil => nil
| h::t => (S h) :: (incCertificates t)
end.

Lemma faultyR_gatherCerts : forall (st:State) (id:ReplicaId) (msgs : total_map nat),
       GatherCertificates (FaultyReplicaFun id msgs st) = GatherCertificates st.
Proof. intros.
  induction st.
    - reflexivity.
    - destruct a. destruct r; simpl; rewrite <- IHst; reflexivity.
Qed.


Lemma faultyR_countNFR : forall (st:State) (id:ReplicaId) (msgs : total_map nat),
       countNFR_state (FaultyReplicaFun id msgs st) = countNFR_state st.
Proof. intros.
  induction st.
    - reflexivity.
    - destruct a. destruct r; simpl; rewrite <- IHst; reflexivity.
Qed.


Definition CorrectSystem (sys:System) := 
    exists F,
    (count_system sys = 3*F+1) /\ (countNFR_system sys = 2*F+1).

Axiom PrimaryNonFaulty : forall (sys:System) (msgs : total_map nat),
     msgs = prePrep sys -> forall (id : ReplicaId), msgs id = nfrValue.


Fixpoint nfrSubState (st:State) :=
match st with
  | nil => nil
  | (NFReplica id, msgs)::t => (NFReplica id, msgs)::(nfrSubState t)
  | _::t => (nfrSubState t)
end.

Lemma nfrSubstate_countCerts : forall (st:State),
  GatherCertificates st = GatherCertificates (nfrSubState st).
Admitted.

Fixpoint nfrMsgsIncrementedBy (st1 st2 : State) (n : nat) :=
match st1, st2 with
| (_, m1)::t1, (_, m2)::t2 => (countNFR_msgs m1) = ((countNFR_msgs m2) + n)
                                /\ nfrMsgsIncrementedBy t1 t2 n
| (_, m1)::t1, _ => (countNFR_msgs m1) = n
| _, _ => True
end.

Lemma multicast_nfrvInc : forall (st : State),
    nfrMsgsIncrementedBy (multicast st nfrValue) st 1.
Proof.
intros. induction st.
- reflexivity.
- destruct a. simpl. split. { auto. } { assumption. }
Qed.

Lemma multicast_fvConst : forall (sys : System),
nfrMsgsIncrementedBy
  (ReplicateRequest sys (prePrep sys) (initState sys))
  (initState sys) (countNFR_system sys)    
  ->
    forall (r:ReplicaId),
    nfrMsgsIncrementedBy
      (multicast
         (ReplicateRequest sys (prePrep (FaultyReplica r :: sys))
            ((FaultyReplica r, []) :: initState sys)) faultyValue)
      ((FaultyReplica r, []) :: initState sys) (countNFR_system sys).
Proof.
Admitted.


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
Qed.

Lemma multicastNFRV_transitive : forall (st base : State) (n:nat),
    nfrMsgsIncrementedBy st base n
      -> nfrMsgsIncrementedBy (multicast st nfrValue) base (S n).
Admitted.


Lemma procReqIncNfrMsgs: forall (sys :System),
    nfrMsgsIncrementedBy (ReplicateRequest sys (prePrep sys) ( initState sys))
                            (initState sys)
                            (countNFR_system sys).
Proof.
intros. induction sys.
  - simpl. auto.
  - destruct a.
    + admit.
    + simpl. unfold NFReplicaFun. 
      rewrite (PrimaryNonFaulty (NFReplica r :: sys) (prePrep (NFReplica r :: sys))).
      {
        apply multicastNFRV_transitive. simpl. admit.
      }
      { auto. }
Admitted.

Definition quorumCertified (nfrSS : State) (r: (Replica * list nat)) :=
    match r with
    | (NFReplica _, msgs) => countNFR_msgs msgs >= countNFR_state nfrSS
    | (FaultyReplica _, _) => True
    end.

Definition LedgerAgreement (st : State) := Forall (quorumCertified st) st.

Lemma nfrIncrementTrans : forall (st base:State) (r:Replica) (msgs : list nat),
   nfrMsgsIncrementedBy ((r, msgs) :: st) base
      (countNFR_state ((r, msgs) :: st))
    -> nfrMsgsIncrementedBy (st) base
      (countNFR_state (st)).
Admitted.

Lemma quorumCertifiedState : forall (st base : State),
  nfrMsgsIncrementedBy st base (countNFR_state st)
    -> LedgerAgreement st.
Proof.
  intros. unfold LedgerAgreement. induction st.
    - constructor.
    - destruct a. destruct base.
      + constructor.
        { destruct r.
           - simpl. auto.
           - simpl. admit.
        }
        { destruct r.
          - unfold quorumCertified. unfold quorumCertified in IHst. simpl. apply IHst.
            apply (nfrIncrementTrans st [] (FaultyReplica r) l). apply H.
          - unfold quorumCertified. unfold quorumCertified in IHst. simpl.
            simpl in H. rewrite <- H.
             admit.
        }
      + constructor.
        { destruct r.
           - simpl. auto.
           - simpl. destruct p. simpl in H. inversion H. admit. 
        }
        { destruct r.
          - unfold quorumCertified. unfold quorumCertified in IHst. simpl. apply IHst; clear IHst.
            apply (nfrIncrementTrans st  (p :: base) (FaultyReplica r) l). apply H.
          - unfold quorumCertified. unfold quorumCertified in IHst. simpl.
            simpl in H.
             admit.
        }
Admitted.

Lemma BFT : forall (sys:System) (st:State) (msgs:total_map nat),
      LedgerAgreement (ReplicateRequest sys msgs st).
Proof.
  intros. apply (quorumCertifiedState (ReplicateRequest sys msgs st) st).
Admitted.
