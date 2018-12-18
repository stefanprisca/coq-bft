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
| message: Replica -> nat -> Message.

Notation "<< r ; n >>" := (message r n).

Inductive State : Type :=
| prePrep: (Replica * (list Message)) -> State
| prep : (Replica * (list Message)) -> State -> State.

Definition ReplicaFun := State -> State.

Definition nfrValue := 0.
Definition faultyValue := 100.
Definition errorNotFound := 400.

Fixpoint multicast (st:State) (v:nat) :=
  match st with
  | prePrep (P, _)  => [<<P;v>>]
  | prep (r, _) t => <<r;v>>::(multicast t v)
  end.

Definition getMsgVal msg := match msg with | message r v => v end.
Definition getMsgReplica msg := match msg with | message r v => r end.


Lemma multicast_nv: forall (nv : nat) (st:State),
    Forall (fun m => eq (getMsgVal m) nv) (multicast st nv).
Admitted.

Fixpoint getPrePrepValue (st:State) :=
  match st with
    | prePrep (P, <<_; v>>::pPrepMsgs) => Some v
    | prePrep (P, _) => None
    | prep _ t => getPrePrepValue t
    end.

Inductive CliqState : State -> Prop :=
| cliqPrePrep : forall (st:State),
    ~((getPrePrepValue st) = None) -> CliqState st.

Lemma prePrepValue_constant : forall st:State, CliqState st ->
    forall (a:Replica) (msgs:list Message),
       getPrePrepValue (st) = getPrePrepValue (prep (a, msgs) st).
Admitted.

Definition optVal (on : option nat) :=
 match on with
  | None => faultyValue
  | Some n => n
  end.

Definition NFReplicaFun (st:State) :=
       prep (NFReplica, 
            multicast (prep (NFReplica, nil) st) (optVal (getPrePrepValue st))) st.

Compute (NFReplicaFun (prePrep (NFReplica, [<< NFReplica; 0 >>; << NFReplica; 0 >>]))).

Definition FaultyReplicaFun (st:State) :=
       prep (FaultyReplica, 
              (multicast (prep (FaultyReplica, nil) st) faultyValue)) st.


Definition GetReplicaFun (r:Replica) : ReplicaFun :=
  match r with
  | FaultyReplica => FaultyReplicaFun
  | NFReplica => NFReplicaFun
  end.

Definition System := list Replica.

Fixpoint systemLen (sys:System) :=
match sys with
| nil => 0 
| r::sys' => S (systemLen sys')
end.

Fixpoint stateLen (st:State) :=
match st with
    | prePrep (P, _) => 1
    | prep (r, prepMsgs) t => S (stateLen t)
    end.


Fixpoint countNFR_system (sys:System) :=
match sys with
  | nil => 0 
  | NFReplica::sys' => S (countNFR_system sys')
  | FaultyReplica::sys' => countNFR_system sys'
end.


Fixpoint countNFR_msgs msgs :=
match msgs with
| nil => 0
| <<NFReplica;_>>::t => S (countNFR_msgs t)
| _::t => countNFR_msgs t
end.

Definition countNFR_state (st:State) :=
match st with
  | prePrep (_, pPrepMsgs) => countNFR_msgs pPrepMsgs
  | prep (_, prepMsgs) t => countNFR_msgs prepMsgs
end.

Axiom sysLen : forall (sys : System), exists F:nat, systemLen sys = 3*F+1.
Axiom sysNofNFR : forall (sys : System), exists F:nat, countNFR_system sys = 2*F+1.

Definition initState (sys : System) :=
  prePrep (NFReplica, (map (fun r => <<r ; nfrValue>>) (NFReplica::sys))).

Fixpoint processRequestHelper (sys : System) (st : State) :=
match sys with
  | nil =>  st
  | r::sys' => (GetReplicaFun r) (processRequestHelper sys' st) 
  end.


Definition ProcessRequest (sys : System) : State :=
  processRequestHelper sys (initState sys)
.

Lemma countNFR_IncNF : forall (sys:System) (r:Replica),
    IsNonFaulty r ->
    S (countNFR_state (ProcessRequest sys)) = countNFR_state (ProcessRequest (r::sys)).
Proof. intros. destruct r.
  - inversion H.
  - simpl. remember (initState (NFReplica :: sys)) as st.
        remember (processRequestHelper sys st) as st'. 
        unfold ProcessRequest. remember (initState sys) as st1.
        remember (processRequestHelper sys st1) as st'1.

Lemma stLen_sysLen : forall sys:System,
      stateLen (ProcessRequest sys) = systemLen sys.
Admitted.

Fixpoint splitMsgs (msgs : list Message) :=
match msgs with
| nil => nil
| m::t => [m] ++ (splitMsgs t)
end.

Fixpoint groupMsgs (newMsgs : list Message) (tst : list (list Message)) :=
match newMsgs, tst with
| nil, nil => nil
| m::mt , tstH :: tstT => (m::tstH)::(groupMsgs mt tstT)
| _, _ => nil
end.

Fixpoint transposeState (st:State) :=
match st with
    | prePrep (P, prePrepMsgs) => [(splitMsgs prePrepMsgs)]
    | prep (r, prepMsgs) t => groupMsgs prepMsgs (transposeState t)
    end.


Lemma TState_NFRReplicasRow : forall (sys:System) (tst_row : list Message) (tst : list (list Message)),
    (transposeState (ProcessRequest sys)) = tst_row::tst
    -> countNFR_msgs tst_row = countNFR_state (ProcessRequest sys).
Proof.
  intros sys. induction sys.
  - intros. inversion H. reflexivity.
  - intros. destruct r.
    + simpl.

Definition qc_incPrePrep ( occ : nat ) (oppv : option nat) :=
  match oppv with
  | Some n => if ( beq_nat n nfrValue) then
                    (S occ)
                else (occ)
  | None => (occ)
  end.

Fixpoint countNFRValues (msgs:list Message) :=
| match 

(* Lemma forall i, replica i NF -> forall j, getMsgValueAtI = nfr. *)
Definition countQuorumVotes (st' : State) (i:nat):=
match st with
    | prePrep _ (P, _) => S qc
    | prep _ (r, prepMsgs) t => (GetQCertificate t i (qc_incPrePrep qc (getMsgValueAtI i prepMsgs)))
    end.


(* When the primary is correct, this should be the number of NF replicas in the system *)
(* THIS is your connection to quorums *)
Fixpoint GetQCertificate (st:State) (i:nat) (qc : nat) :=
    

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

