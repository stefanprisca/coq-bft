Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Export Coq.Strings.String.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Maps.

Definition ReplicaId := string.


Inductive Replica : Set :=
| FaultyReplica : Replica
| NFReplica : Replica.

Definition IsNonFaulty (r:Replica) :  Prop :=
  match r with 
    | FaultyReplica => False
    | NFReplica => True
  end.

Print list.

Inductive Message : Type := 
| message: (nat * nat ) -> Message.

Notation "<< i ; n >>" := (message (i, n)).

Inductive State : Type :=
| prePrep: nat -> (Replica * (list Message)) -> State
| prep : nat -> (Replica * (list Message)) -> State -> State.

Definition ReplicaFun := nat -> State -> State.

Definition nfrValue := 0.
Definition faultyValue := 100.
Definition errorNotFound := 400.

Fixpoint multicast (i : nat) (v:nat) :=
  match i with
  | 0 => [<<0;v>>]
  | S i' => <<i;v>>::(multicast i' v)
  end.

Fixpoint getMsgValueAtI (i : nat) (msgs : list Message) :=
  match msgs with
  | nil => None
  | <<i';v>>::t => if (beq_nat i' i) then Some v
                      else getMsgValueAtI i t
end.

Definition beq_opt (on : option nat) (n : nat) :=
match on with 
| None => false
| Some n' => beq_nat n' n
end.

Fixpoint getUniqueMsgVal (msgs:list Message) :=
  match msgs with
  | nil => None
  | <<i;n>> :: t => if (beq_opt (getUniqueMsgVal t) n) then Some n
                    else None
  end.

Inductive NFPrepConsistent : list Message -> Prop :=
| nfpc_empty : NFPrepConsistent nil
| nfpc_ind  : forall (msgs : list Message) ( i n : nat) (r : Replica),
                IsNonFaulty r -> (getUniqueMsgVal msgs) = Some n
                -> NFPrepConsistent (<<i;n>>::msgs).

Lemma multicast_unique_nv: forall (nv : nat) (len : nat),
    getUniqueMsgVal (multicast len nv ) = Some nv.
Admitted.


Lemma multicast_vAtI_nv: forall (nv : nat) (len : nat) (i: nat),
    getMsgValueAtI i (multicast len nv) = Some nv.
Admitted.

Definition multicastOpt (on : option nat) (prePrepMsgs: list Message) :=
match on with
| None => nil
| Some v => multicast (length prePrepMsgs) v
end.

Fixpoint genSequenceNumList (st:State) (i : nat): list Message :=
    match st with
    | prePrep r (P, prePrepMsgs) => 
            multicastOpt (getMsgValueAtI i prePrepMsgs) prePrepMsgs
    | prep _ _ t => genSequenceNumList t i
    end.

Inductive CliqList : list Message -> Prop :=
| cliqL : forall (msgs: list Message),
    ~(exists (i :nat), (getMsgValueAtI i msgs) = None) -> CliqList msgs.


Inductive CliqState : State -> Prop :=
| primary_cc : forall (msgs: list Message),
      CliqList msgs
      -> forall (pI:nat) (p:Replica), CliqState (prePrep pI (p, msgs))
| replica_cc : forall (msgs: list Message),
    CliqList msgs
      -> forall (rI:nat) (r:Replica) (st : State), 
        CliqState st -> CliqState(prep rI (r, msgs) st). 




Fixpoint getPrePrepValue (st:State) (i : nat) :=
match st with
    | prePrep _ (P, pPrepMsgs) => (getMsgValueAtI i pPrepMsgs)
    | prep _ _ t => getPrePrepValue t i
    end.

Fixpoint getPrePrepValues (st:State) :=
  match st with
    | prePrep _ (P, pPrepMsgs) => pPrepMsgs
    | prep _ _ t => getPrePrepValues t
    end.

Lemma genSeqNumList_PrePrepValue : forall (i : nat) (st:State),
  CliqState st ->
  getUniqueMsgVal(genSequenceNumList st i) = getPrePrepValue st i.
Proof. intros. induction H. induction H.
  - simpl. remember (getMsgValueAtI i msgs) as mval. destruct mval.
    + simpl. apply multicast_unique_nv.
    + unfold not in H. repeat destruct H. exists i. rewrite Heqmval. reflexivity.
  - simpl. apply IHCliqState.
Qed.


Definition NFReplicaFun (i : nat) (st:State) :=
       prep i (NFReplica, (genSequenceNumList st i)) st.


Fixpoint genFaultySequenceNumList (st:State) (i : nat): list Message :=
    match st with
    | prePrep _ (P, prePrepMsgs) => multicast (length prePrepMsgs) faultyValue
    | prep _ (r, prepMsgs) t => multicast (length prepMsgs) faultyValue
    end.

Definition FaultyReplicaFun (i : nat) (st:State) :=
       prep i (FaultyReplica, (genFaultySequenceNumList st i)) st.


Definition GetReplicaFun (r:Replica) : ReplicaFun :=
  match r with
  | FaultyReplica => FaultyReplicaFun
  | NFReplica => NFReplicaFun
  end.


Inductive System : Type :=
| primary : nat -> Replica -> System
| replica : Replica -> System -> System.

Fixpoint ProcessRequest (sys : System) (i : nat) : State :=
  match sys with
  | primary len P =>  prePrep i (P, multicast len nfrValue)
  | replica r sys' => ((GetReplicaFun r) i (ProcessRequest sys' (S i) )) 
  end.

Definition qc_incPrePrep ( occ : nat ) (oppv : option nat) :=
  match oppv with
  | Some n => if ( beq_nat n nfrValue) then
                    (S occ)
                else (occ)
  | None => (occ)
  end.

(* Lemma forall i, replica i NF -> forall j, getMsgValueAtI = nfr. *)

(* When the primary is correct, this should be the number of NF replicas in the system *)
(* THIS is your connection to quorums *)
Fixpoint GetQCertificate (st:State) (i:nat) (qc : nat) :=
    match st with
    | prePrep _ (P, _) => S qc
    | prep _ (r, prepMsgs) t => (GetQCertificate t i (qc_incPrePrep qc (getMsgValueAtI i prepMsgs)))
    end.

Fixpoint getLedgersHelper (st originalSt : State) :=
match st with
| prePrep i (P, msgs) => [nfrValue]
| prep i (NFReplica, _) t => (GetQCertificate originalSt i 0)::(getLedgersHelper t originalSt)
| prep _ (FaultyReplica, _) t => getLedgersHelper t originalSt
end.

Definition assertQuorumAgreement (nVotes : nat):= Some(nfrValue).

Definition GetLedgers (st:State) :=
  map assertQuorumAgreement (getLedgersHelper st st).

Inductive LedgerAgreement : (list (option nat)) -> Prop :=
| empty_la : LedgerAgreement [(Some nfrValue)]
| ind_la : forall (n: nat) (l : list (option nat)),
            LedgerAgreement l -> 
              (hd None l) = Some n ->
                LedgerAgreement ((Some n)::l).

Axiom CliqConnected : forall st:State, CliqState st.

Lemma NFR_QCertificates : forall (i:nat) (sys:System),
      GetQCertificate (NFReplicaFun i (ProcessRequest sys (S i))) i 0 = nfrValue.
Admitted.

Lemma NFR_ledger_nfrvalue:  
        forall (sys:System) (r:Replica) (i:nat), 
            IsNonFaulty r
         -> (GetLedgers (ProcessRequest (replica r sys) i))
            = (Some nfrValue)::(GetLedgers (ProcessRequest sys (S i))).
Proof.
  intros. induction r.
    - inversion H.
    - simpl. induction (ProcessRequest sys (S i)).
      + simpl. unfold GetLedgers. destruct p. 
        simpl. auto.
      + simpl. destruct p. simpl. induction l.
        { simpl.
Admitted.



Lemma FaultyR_ledger_novalue:  
        forall (sys:System) (r:Replica) (i:nat), 
            ~(IsNonFaulty r)
         -> (GetLedgers (ProcessRequest (replica r sys) i))
            = (GetLedgers (ProcessRequest sys i)).
Admitted.

Theorem StateValid : forall (sys : System),
      forall i:nat, LedgerAgreement (GetLedgers (ProcessRequest sys i)).
Proof. intros sys. induction sys.
  - simpl. unfold GetLedgers. simpl. rewrite multicast_nv. constructor. 
  - induction r.
    + intros. rewrite FaultyR_ledger_novalue.
        { simpl. apply IHsys. }
        { auto. } 
    + intros. rewrite NFR_ledger_nfrvalue.
      { 
        constructor. 
        { apply IHsys. }
        { induction (IHsys (S i)).
          { reflexivity. }
          { rewrite H in IHl. apply IHl. }
        }
      }
      { reflexivity. }
Qed.

