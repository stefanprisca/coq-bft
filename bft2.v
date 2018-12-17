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

Lemma multicast_nv: forall (nv : nat) (len : nat),
    getUniqueMsgVal (multicast len nv ) = Some nv.
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

Inductive CliqConnected : State -> Prop :=
| primary_cc : forall (msgs: list Message),
      CliqList msgs
      -> forall (pI:nat) (p:Replica), CliqConnected (prePrep pI (p, msgs))

| replica_cc : forall (msgs: list Message),
    CliqList msgs
      -> forall (rI:nat) (r:Replica) (st : State), 
        CliqConnected st -> CliqConnected(prep rI (r, msgs) st). 

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
  CliqConnected st ->
  getUniqueMsgVal(genSequenceNumList st i) = getPrePrepValue st i.
Proof. intros. induction H. induction H.
  - simpl. remember (getMsgValueAtI i msgs) as mval. destruct mval.
    + simpl. apply multicast_nv.
    + unfold not in H. repeat destruct H. exists i. rewrite Heqmval. reflexivity.
  - simpl. apply IHCliqConnected.
Qed.

Lemma getUniqueMsgVal_constIVal: forall (msgs : list Message) (i n:nat),
    getUniqueMsgVal msgs = getMsgValueAtI i msgs.
Admitted.

Lemma prePrepValue_nfrValue : forall (st:State), CliqConnected st ->
    forall (n:nat), getUniqueMsgVal(getPrePrepValues st) = Some (n)
    -> forall (i1 i2 : nat), 
      getUniqueMsgVal(genSequenceNumList st i1) = getUniqueMsgVal(genSequenceNumList st i2).
Admitted.

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

Definition qc_incPrePrep ( ppV occ : nat ) (prepMsgs : list Message) (i : nat):=
  match (getMsgValueAtI i prepMsgs) with
  | Some n => if ( beq_nat n ppV) then
                    (ppV, S occ)
                else (ppV, occ)
  | None => (ppV, occ)
  end.


Definition qc_checkPrePrep ( prevCount : nat*nat) (prepMsgs : list Message) (i : nat):=
  match prevCount with
  | (ppV, occ) => qc_incPrePrep ppV occ prepMsgs i
  end.

Definition qc_setPrePrep (prePrepMsgs : list Message) (i : nat) :=
  match (getMsgValueAtI i prePrepMsgs) with
  | Some ppV => (ppV, 1)
  | None => (0, 0)
  end.

(* When the primary is correct, this should be the number of NF replicas in the system *)
(* THIS is your connection to quorums *)

Fixpoint qc_countPrePrepVals (st:State) (i : nat) :=
  match st with
    | prePrep _ (P, prePrepMsgs) => qc_setPrePrep prePrepMsgs i
    | prep _ (r, prepMsgs) t => qc_checkPrePrep (qc_countPrePrepVals t i) prepMsgs i
    end.


Fixpoint GetQCertificate (st:State) (i:nat) :=
    qc_countPrePrepVals st i.

Definition QC_Value (qc : nat * nat):=
match qc with
  | (v, sign) => v
end. 

Lemma NFR_QCertNFRValue : forall r: Replica, IsNonFaulty r
        -> forall (sys:System) (i:nat),
            QC_Value (GetQCertificate (ProcessRequest (replica r sys) i ) i) = nfrValue.
Proof. intros r. destruct r.
  - intros. inversion H.
  - intros. admit.
Admitted.

Fixpoint getLedgersHelper (st originalSt : State) :=
match st with
| prePrep i (P, msgs) => [getUniqueMsgVal msgs]
| prep i (NFReplica, _) t => (Some (QC_Value (GetQCertificate originalSt i)))::(getLedgersHelper t originalSt)
| prep _ (FaultyReplica, _) t => getLedgersHelper t originalSt
end.


Definition GetLedgers (st:State) :=
  getLedgersHelper st st.

Lemma NFR_ledger_nfrvalue:  
        forall (sys:System) (req:string) (r:Replica) (i:nat), 
            IsNonFaulty r
         -> (GetLedgers (ProcessRequest sys (S i))) 
            = (Some nfrValue)::(GetLedgers (ProcessRequest (replica r sys) i)).
Admitted.

Inductive StateValid : State -> Prop :=
| empty_valid : forall (P:Replica) (i : nat) (msgs: list Message), StateValid (prePrep i (P, msgs))
| nonfaulty_valid : forall (sys:System) (r:Replica) , 
              IsNonFaulty r 
              -> forall i:nat, StateValid (ProcessRequest sys (S i))
                -> (GetLedgers (ProcessRequest sys (S i))) 
                     = (GetLedgers (ProcessRequest (replica r sys) i)) 
                    -> StateValid ((ProcessRequest (replica r sys) i))
| faulty_valid : forall (sys:System) (i:nat) (r:Replica) , ~(IsNonFaulty r) -> 
      StateValid (ProcessRequest sys (S i)) -> StateValid ((ProcessRequest (replica r sys) i)).

Theorem system_safety : forall (sys : System),
      forall i:nat, StateValid (ProcessRequest sys i).
Proof. intros sys. induction sys.
  - constructor.
  - induction r.
    + intros. apply faulty_valid.
      { unfold not. intros contra. inversion contra. }
      { admit. }
    + intros. apply nonfaulty_valid.
      { reflexivity. }
      { admit. }
      { admit. }
Admitted.

