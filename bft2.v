Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Export Coq.Strings.String.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Maps.
Require Coq.omega.Omega.

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

Definition State := list (Replica * (list nat)).

Definition ReplicaFun := nat -> State -> State.

Definition nfrValue := 0.
Definition faultyValue := 100.
Definition errorNotFound := 400.

Fixpoint multicast (st:State) (v:nat) :=
  match st with
  | nil  => nil
  | (r, msgs)::t => (r, v::msgs)::(multicast t v)
  end.

Definition NFReplicaFun (msg:nat) (st:State) :=
       multicast st msg.


Definition FaultyReplicaFun (msg:nat) (st:State) :=
       multicast st faultyValue.

Definition GetReplicaFun (r:Replica) : ReplicaFun :=
  match r with
  | FaultyReplica => FaultyReplicaFun
  | NFReplica => NFReplicaFun
  end.

Definition System := list Replica.

Fixpoint countNFR_system (sys:System) :=
match sys with
  | nil => 0 
  | NFReplica::sys' => S (countNFR_system sys')
  | FaultyReplica::sys' => countNFR_system sys'
end.

Definition F := 10.
Definition CompleteSystem (sys:System) := length sys = 3*F+1 /\ countNFR_system sys = 2*F+1.
Definition QuorumReq := 2*F+1.

Definition initState (sys:list Replica) : State := ( (map (fun r => (r, nil)) sys)).
Definition prePrep (sys:list Replica) := ( (map (fun r => nfrValue) sys)).
Compute prePrep [FaultyReplica; NFReplica].

Fixpoint ReplicateRequest (sys : System) (msg: list nat) (st : State):=
match sys, msg with
  | nil, nil => st
  | (r::sys'), (m::mt) => (GetReplicaFun r) m (ReplicateRequest sys' mt st)
  | _, _ => nil
  end.

Fixpoint countNFR_msgs msgs :=
match msgs with
| nil => 0
| v::t => if (beq_nat v nfrValue) then (S (countNFR_msgs t ))
          else (countNFR_msgs t )
end.

Fixpoint GatherCertificates (st:State) :=
match st with
  | nil => nil
  | (NFReplica, msgs)::t => (countNFR_msgs msgs)::(GatherCertificates t)
  | _::t => GatherCertificates t
end.

Fixpoint incCertificates (certs : list nat):=
match certs with
| nil => nil
| h::t => (S h) :: (incCertificates t)
end.

Lemma FaultyR_GatherCerts : forall (st:State) (m:nat),
        GatherCertificates (FaultyReplicaFun m st) = GatherCertificates st.
Proof. intros.
  induction st.
    - reflexivity.
    - destruct a. destruct r; simpl; rewrite <- IHst; reflexivity.
Qed.

Lemma NFR_GatherCerts : forall (st:State),
        GatherCertificates (NFReplicaFun nfrValue st) = incCertificates (GatherCertificates st).
Proof. intros.
   induction st.
    - reflexivity.
    - destruct a. destruct r.
      + simpl. apply IHst.
      + simpl. rewrite IHst. reflexivity.
Qed.

Inductive LedgerAgreement : (list nat) -> Prop :=
| qcAgreement : forall (certs : list nat), 
            Forall (fun x => ~ (lt x QuorumReq)) certs -> LedgerAgreement certs.

Lemma IncCertificates_MaintainsLedger : forall (certs : list nat),
      LedgerAgreement certs ->
        LedgerAgreement (incCertificates certs).
Proof. intros. induction H. constructor. induction certs.
  - simpl. constructor.
  - simpl. inversion H. constructor.
    + admit.
    + apply IHcerts. apply H3.
Admitted. 

Lemma StateValid : forall (sys:System) (st:State) (msgs:list nat),
        CompleteSystem sys ->
        st = (initState sys) /\ msgs = (prePrep sys) ->
          LedgerAgreement (GatherCertificates (ReplicateRequest sys msgs st)).
Proof.
  intros sys. induction sys.
    + intros. induction H. inversion H1.
    + intros. induction H0. destruct a.
      - simpl. rewrite H1. simpl. rewrite FaultyR_GatherCerts. apply IHsys.
        { admit. } { split. admit. admit. }
      - simpl. rewrite H1. simpl. rewrite NFR_GatherCerts. 
        apply IncCertificates_MaintainsLedger. apply IHsys.
        { admit. } { split. admit. admit. }
Admitted.
