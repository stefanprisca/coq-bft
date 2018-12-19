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
Definition errorNotFound := 400.

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

Fixpoint count_state (st:State) :=
match st with
  | nil  => 0
  | _::t => S (countNFR_state t)
  end.


Fixpoint count_system (sys:System) :=
match sys with
  | nil  => 0
  | _::t => S (count_system t)
  end.

Definition F := 10.
Definition CompleteState (st:State) := count_state st = 3*F+1 /\ countNFR_state st = 2*F+1.
Definition CompleteSystem (sys:System) := count_system sys = 3*F+1.
Definition QuorumRequirement := 2*F+1.

Definition initState (sys:list Replica) : State := ( (map (fun r => (r, nil)) sys)).

Definition newPrePrep (msgs : total_map nat) (r: Replica) : total_map nat := 
    match r with 
    | NFReplica id => msgs & {id --> nfrValue}
    | FaultyReplica id => msgs & {id --> nfrValue}
    end.

Definition prePrep (sys:list Replica) := 
    ( (fold_left newPrePrep sys (t_empty nfrValue) )).
Compute prePrep [(FaultyReplica "0"); (NFReplica "1")].

Definition PrePrepGte (msgs : total_map nat) (sys : System) :=
    msgs = prePrep sys \/ exists sys', msgs = prePrep(sys'++sys).

Lemma PrePrepGte_Ind : forall (msgs : total_map nat) (sys : System) (r:Replica),
    PrePrepGte msgs (r::sys) -> PrePrepGte msgs sys.
Proof. intros. destruct H. 
  - unfold PrePrepGte. right. exists [r]. apply H.
  - unfold PrePrepGte. right. destruct H. exists (app x [r]). rewrite <- app_assoc. apply H.
Qed.

Definition StateGte st sys := st = initState sys \/ exists sys', st = initState (sys'++sys).

Lemma StateGte_Ind : forall (st : State) (sys : System) (r:Replica),
    StateGte st (r::sys) -> StateGte st sys.
Proof. intros. destruct H. 
  - unfold StateGte. right. exists [r]. apply H.
  - unfold StateGte. right. destruct H. exists (app x [r]). rewrite <- app_assoc. apply H.
Qed.

Axiom PrimaryNonFaulty : forall (sys:System) (msgs : total_map nat),
      PrePrepGte msgs sys -> forall (id : ReplicaId), msgs id = nfrValue.

Fixpoint ReplicateRequest (sys : System) (msgs: total_map nat) (st : State):=
match sys with
  | nil => st
  | (r::sys') => (GetReplicaFun r) msgs (ReplicateRequest sys' msgs st)
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
  | (NFReplica id, msgs)::t => (countNFR_msgs msgs)::(GatherCertificates t)
  | _::t => GatherCertificates t
end.

Fixpoint incCertificates (certs : list nat):=
match certs with
| nil => nil
| h::t => (S h) :: (incCertificates t)
end.

Lemma FaultyR_GatherCerts : forall (st:State) (id:ReplicaId) (msgs : total_map nat),
        GatherCertificates (FaultyReplicaFun id msgs st) = GatherCertificates st.
Proof. intros.
  induction st.
    - reflexivity.
    - destruct a. destruct r; simpl; rewrite <- IHst; reflexivity.
Qed.

Lemma NFR_GatherCerts : forall (st:State) (id : ReplicaId) (msgs : total_map nat) (sys:System),
            PrePrepGte msgs ((NFReplica id)::sys)
            -> GatherCertificates (NFReplicaFun id msgs st) = incCertificates (GatherCertificates st).
Proof. intros.
   induction st.
    - reflexivity.
    - destruct a. destruct r.
      + simpl. apply IHst.
      + simpl. rewrite <- IHst. unfold NFReplicaFun. 
         rewrite (PrimaryNonFaulty (NFReplica id :: sys) msgs). reflexivity. assumption.
Qed.


Inductive LedgerAgreement : (list nat) -> Prop :=
| qcAgreement : forall (certs : list nat),
          Forall (fun x => ~ (lt x QuorumRequirement)) certs 
            -> LedgerAgreement certs.

Axiom LedgerAgreementEmpty : forall msgs st,
        LedgerAgreement (GatherCertificates (ReplicateRequest [] msgs st)).

Lemma IncCertificates_MaintainsLedger : forall (certs : list nat),
      LedgerAgreement certs -> LedgerAgreement (incCertificates certs).
Proof. intros. induction H. constructor. induction certs.
  - simpl. constructor.
  - simpl. inversion H. constructor.
    + unfold not. intros. rewrite <- H4 in H2. unfold not in H2. destruct H2.
       auto.
    + apply IHcerts. apply H3.
Qed. 

Lemma StateValid : forall (sys:System) (st:State) (msgs:total_map nat),
      PrePrepGte msgs sys /\ StateGte st sys ->
            LedgerAgreement (GatherCertificates (ReplicateRequest sys msgs st)).
Proof.
  intros sys. induction sys.
    + intros. apply LedgerAgreementEmpty.
    + intros. destruct H. destruct a.
      - simpl. rewrite FaultyR_GatherCerts. apply IHsys.
      { split. 
          - apply (PrePrepGte_Ind msgs sys (FaultyReplica r)). assumption.
          - apply (StateGte_Ind st sys (FaultyReplica r)). assumption.
      }
      - simpl. 
        rewrite (NFR_GatherCerts (ReplicateRequest sys msgs st) r msgs sys). 
        apply IncCertificates_MaintainsLedger. apply IHsys.
         { split. 
            - apply (PrePrepGte_Ind msgs sys (NFReplica r)). assumption.
            - apply (StateGte_Ind st sys (NFReplica r)). assumption.
         }
         { auto. }
Qed.
