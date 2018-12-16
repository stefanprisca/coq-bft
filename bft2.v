Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Export Coq.Strings.String.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import String.
Require Import Maps.
Open Scope string_scope.

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
| message: (nat * Replica * nat ) -> Message.

Notation "<< i ; r ; n >>" := (message (i, r, n)).

Inductive State : Type :=
| prePrep: nat -> (Replica * (list Message)) -> State
| prep : nat -> (Replica * (list Message)) -> State -> State.

Definition ReplicaFun := nat -> State -> State.

Definition nfrValue := 0.
Definition faultyValue := 100.

Definition replaceWithVal (msg: Message) (v:nat) :=
  match msg with
  | <<i;r;n >> => <<i;r;v>>
  end.

Definition replaceAllWithVal (v:nat) (messages : list Message) :=
      map (fun msg => (replaceWithVal msg v) ) messages.

Fixpoint getMsgValueAtI (i : nat) (msgs : list Message) :=
  match msgs with
  | nil => None
  | <<i';r;v>>::t => if (beq_nat i' i) then Some v
                      else getMsgValueAtI i t
end.

Fixpoint getUniqueMsgVal (msgs:list Message) :=
match msgs with
| nil => None
| <<i;r;n>> :: t => match (getUniqueMsgVal t) with
                    | None => None
                    | Some n' => if (beq_nat n' n) then Some n
                                  else None
                    end
end.

Inductive NFPrepConsistent : list Message -> Prop :=
| nfpc_empty : NFPrepConsistent nil
| nfpc_ind  : forall (msgs : list Message) ( i n : nat) (r : Replica),
                IsNonFaulty r -> (getUniqueMsgVal msgs) = (Some n)
                -> NFPrepConsistent (<<i;r;n>>::msgs).


Lemma replaceAllWithVal_nfpc: forall (nv : nat) (msgs : list Message),
    NFPrepConsistent (replaceAllWithVal nv msgs).
Admitted.

Lemma replaceAllWithVal_nv: forall (nv : nat) (msgs : list Message),
    getUniqueMsgVal (replaceAllWithVal nv msgs) = Some nv.
Admitted.


Definition replaceWithValueAt (i:nat) (msgs: list Message) :=
  let ov := getMsgValueAtI i msgs in
    match ov with 
    | Some v => replaceAllWithVal v msgs
    | None => msgs
    end.
  
Fixpoint genSequenceNumList (st:State) (i : nat): list Message :=
    match st with
    | prePrep _ (P, prePrepMsgs) => (replaceWithValueAt i prePrepMsgs)
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
Proof. intros. induction H.
  - simpl. remember (getMsgValueAtI i msgs) as msg. destruct msg.
    + unfold replaceWithValueAt. rewrite <- Heqmsg. apply replaceAllWithVal_nv.
    + unfold not in H. repeat destruct H. exists i. rewrite Heqmsg. reflexivity.
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
    | prePrep _ (P, prePrepMsgs) => (replaceAllWithVal faultyValue prePrepMsgs)
    | prep _ (r, prepMsgs) t => (replaceAllWithVal faultyValue prepMsgs)
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
  | primary len P =>  prePrep i (P, repeat <<i;NFReplica;nfrValue>> len)
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


Fixpoint GetQCertValue (st:State) (i : nat) :=
    qc_countPrePrepVals st i.


(* TODO: NFR state should be quorum value. *)
Lemma NFR_state_nfrValue: forall r:Replica, IsNonFaulty r
         -> forall (sys:System), 
              ProcessRequest (replica r sys) 
               = (prep (r, nfrValue) (ProcessRequest sys)).
Proof. intros.
  generalize dependent sys. induction r.
  - inversion H.
  - simpl. intros. induction sys.
    + simpl. reflexivity.
    + induction r.
      { simpl. rewrite getPrimaryValue_nfrValue. reflexivity. }
      { simpl. rewrite IHsys. simpl. rewrite getPrimaryValue_nfrValue. reflexivity. }
Qed. 

Definition getLedgerHelper (l:nat) (ledger : option nat) :=
match ledger with
| Some l => Some l
| _ => None
end.

Fixpoint GetLedger (st:State) : option nat :=
match st with
| prePrep (P, n) => Some n
| prep (NFReplica, l) t => getLedgerHelper l (GetLedger t)
| prep (FaultyReplica, l) t => GetLedger t
end.

Lemma NFR_maintains_ledger:  
        forall (sys:System) (req:string) (r:Replica) , 
            IsNonFaulty r
         -> (GetLedger (ProcessRequest sys req)) 
            = (GetLedger (ProcessRequest (replica r sys) req)).
Proof. intros. rewrite NFR_state_nfrValue.
  - induction r.
    + simpl. reflexivity.
    + simpl. remember (GetLedger (ProcessRequest sys req)) as ledger.
      destruct ledger.
      { reflexivity. }
      { reflexivity. }
  - assumption.
Qed.

Inductive StateValid : State -> Prop :=
| empty_valid : forall (P:Replica) (n:nat), StateValid (prePrep (P, n))
| nonfaulty_valid : forall (sys:System) (req:string) (r:Replica) , 
              IsNonFaulty r 
              -> StateValid (ProcessRequest sys req)
                -> (GetLedger (ProcessRequest sys req)) 
                     = (GetLedger (ProcessRequest (replica r sys) req)) 
                    -> StateValid ((ProcessRequest (replica r sys) req))
| faulty_valid : forall (sys:System) (req:string) (r:Replica) , ~(IsNonFaulty r) -> 
      StateValid (ProcessRequest sys req) -> StateValid ((ProcessRequest (replica r sys) req)).

Theorem system_safety : forall (sys : System) (m:string),
      StateValid (ProcessRequest sys m).
Proof. intros. induction sys.
  - constructor.
  - induction r.
    + apply faulty_valid.
      { unfold not. intros contra. inversion contra. }
      { assumption. }
    + apply nonfaulty_valid.
      { reflexivity. }
      { assumption. }
      { apply NFR_maintains_ledger. reflexivity. }
Qed.

