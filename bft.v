Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Export Coq.Strings.String.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import String.
Require Import Maps.
Open Scope string_scope.


Definition FNum := 2.
Definition QuorumAcceptanceThreshold := 2*FNum + 1.
Definition MaxMessages := 1000.


Definition ReplicaId := string.
Definition SysView := string.

Inductive Message : Type := 
| reqMsg: string -> ReplicaId -> Message
| pPrepMsg: string -> nat -> ReplicaId -> Message
| prepMsg: string -> nat -> ReplicaId -> Message.

Notation "<<REQ digest , rId >>" := (reqMsg digest rId).
Notation "<<PPREP digest , seqNum , rId >>" := (pPrepMsg digest seqNum rId).
Notation "<<PREP digest , seqNum , rId >>" := (prepMsg digest seqNum rId).


Definition GetRID (msg : Message) : ReplicaId :=
  match msg with
  | reqMsg digest rId => rId
  | pPrepMsg digest seqNum rId => rId
  | prepMsg digest seqNum rId => rId
  end.

Definition GetDigest (msg : Message) : string :=
  match msg with
  | reqMsg digest rId => digest
  | pPrepMsg digest seqNum rId => digest
  | prepMsg digest seqNum rId => digest
  end.

Definition Ledger := list (string * nat).
Definition EmptyLedger : Ledger :=  nil.

Fixpoint beq_ledgers (l1 l2 : Ledger) :=
match l1 with
| nil => match l2 with
          | nil => true
          | _ => false
         end
| (s1, n1)::t => match l2 with
          | nil => false
          | (s2, n2)::t2 => andb (andb (beq_string s1 s2) (beq_nat n1 n2)) (beq_ledgers t t2)
         end
end.

Definition SysState := total_map Ledger.
Definition MessageBox := list Message.


Inductive QCert : Type :=
| qCert : string -> nat -> QCert.

Definition QCerts := total_map (list QCert).

Definition EmptyQCerts : QCerts := fun _ => nil.

Inductive ExecEnvironment : Type :=
| execEnv : list ReplicaId -> SysState -> QCerts -> MessageBox -> ExecEnvironment.


Definition GetEnvState (env : ExecEnvironment) := 
  match env with
  | execEnv _ state _ _  => state
  end.

Definition GetEnvReplicas (env : ExecEnvironment) := 
  match env with
  | execEnv replicas _ _ _  => replicas
  end.


Definition GetEnvMsgBox (env : ExecEnvironment) := 
  match env with
  | execEnv _ _ _  mb => mb
  end.

Definition GetEnvQCerts (env : ExecEnvironment) := 
  match env with
  | execEnv _ _ qcs _ => qcs
  end.

Definition Replica := ExecEnvironment -> Message -> ExecEnvironment.

Definition SysReplicas := list (ReplicaId * Replica).

Inductive System : Type := 
  | system : SysView -> SysState -> SysReplicas -> System.

Definition GetView (sys : System) := 
  match sys with
  | system view _ _ => view
  end.

Definition GetState (sys : System) := 
  match sys with
  | system _ state _ => state
  end.

Fixpoint getReplicaIdsHelper (replicas : SysReplicas) (result : list ReplicaId) :=
  match replicas with
  | nil => result
  | (rId, _)::t => rId::(getReplicaIdsHelper t result)
  end.

Definition GetReplicaIds (sys : System) := 
  match sys with
  | system _ _ replicas => (getReplicaIdsHelper replicas nil)
  end.


Definition GetReplicas (sys : System) := 
  match sys with
  | system _ _ replicas => replicas
  end.

Fixpoint findReplicaHelper (replicas : SysReplicas) (rId : ReplicaId) :=
match replicas with
| nil => None
| (rId', r)::t => if beq_string rId rId' then (Some r)
                  else findReplicaHelper t rId
end.

Definition FindReplica (sys : System) (rId:ReplicaId) :=
let replicas := GetReplicas sys in
  findReplicaHelper replicas rId.


Definition EmptyState : SysState :=  (fun _ => EmptyLedger).
Definition EmptyReplicas : SysReplicas :=  nil.

Fixpoint multicast (from : ReplicaId) (replicas : list ReplicaId) (msgTo : ReplicaId -> Message) (mBox : MessageBox) : MessageBox :=
  match replicas with
  | nil => mBox
  | rId::t => if (beq_string rId from) then multicast from t msgTo mBox
              else (msgTo rId)::(multicast from t msgTo mBox)
  end.

Definition pushCertificate (qCerts : QCerts) (rId : ReplicaId) (qCert : QCert) : QCerts :=
  qCerts & {rId --> qCert::(qCerts rId)}.

Fixpoint seqNumAccepted (l:Ledger) (n:nat) :=
    match l with
    | nil => false
    | (_, v)::t => orb (beq_nat n v) (seqNumAccepted t n)
    end.

Fixpoint hasEnoughQCerts (qCertL : list QCert) (digest : string) (seqNum collected : nat) :=
    match qCertL with
    | nil => beq_nat collected QuorumAcceptanceThreshold
    | (qCert d v)::t => if (andb (beq_string digest d) (beq_nat v seqNum)) then
                           hasEnoughQCerts t digest seqNum (S collected)
                        else
                            hasEnoughQCerts t digest seqNum collected
    end.

Definition isQuorumCertified (qCertsL : list QCert) (digest : string) (seqNum : nat):=
    hasEnoughQCerts qCertsL digest seqNum 0.

Definition pushSequenceNum (st : SysState) (rId : ReplicaId) (digest : string) (seqNum : nat) :=
    st & {rId --> (digest, seqNum)::(st rId)}.

Definition genSeqNum (l : Ledger) :=
    match l with
      | nil => 0
      | (d, v)::t => S v
    end.

Definition NFReplica : Replica := 
  fun env msg => 
      match msg with
      | (reqMsg digest rId) => let n := (genSeqNum ((GetEnvState env) rId)) in
                                let mb' := (multicast rId (GetEnvReplicas env) (pPrepMsg digest n) (GetEnvMsgBox env)) in
                                  let qCerts' := (pushCertificate (GetEnvQCerts env) rId (qCert digest n)) in
                                    execEnv (GetEnvReplicas env) (GetEnvState env) qCerts' mb'
      | (pPrepMsg digest n rId) => if (seqNumAccepted ((GetEnvState env) rId) n) then
                                        env
                                   else
                                      let mb' := (multicast rId (GetEnvReplicas env) (prepMsg digest n) (GetEnvMsgBox env)) in
                                      let qCerts' := (pushCertificate (GetEnvQCerts env) rId (qCert digest n)) in
                                        if (isQuorumCertified (qCerts' rId) digest n) then
                                           let state' := (pushSequenceNum (GetEnvState env) rId digest n) in
                                              execEnv (GetEnvReplicas env) state' qCerts' mb'
                                        else
                                              execEnv (GetEnvReplicas env) (GetEnvState env) qCerts' mb'
      | (prepMsg digest n rId) => if (seqNumAccepted ((GetEnvState env) rId) n) then
                                        env
                                   else
                                      let qCerts' := (pushCertificate (GetEnvQCerts env) rId (qCert digest n)) in
                                        if (isQuorumCertified (qCerts' rId) digest n) then
                                           let state' := (pushSequenceNum (GetEnvState env) rId digest n) in
                                              execEnv (GetEnvReplicas env) state' qCerts' (GetEnvMsgBox env)
                                        else
                                              execEnv (GetEnvReplicas env) (GetEnvState env) qCerts' (GetEnvMsgBox env)
    end.

Definition ProcessMessage (msg:Message) (sys:System) (rId : ReplicaId) (env : ExecEnvironment) :=
 match (FindReplica sys rId) with
    | None => env
    | Some replica => (replica env msg)
  end.

Fixpoint ProcessAllMessages (fuel : nat) (sys:System) (env : ExecEnvironment) := 
  match fuel with
  | 0 => env
  | S f' =>
      match (GetEnvMsgBox env) with
      | nil => env
      | msg::t => let rId := GetRID msg in
                  let envI := (execEnv (GetEnvReplicas env) (GetEnvState env) (GetEnvQCerts env) t) in
                  let env' := ProcessMessage msg sys rId envI in
                    ProcessAllMessages f' sys env'
      end
  end.

Print ExecEnvironment.
Print System.
Definition ProcessRequest (sys : System) (req : Message) : System :=
  let env' := ProcessAllMessages MaxMessages sys (execEnv (GetReplicaIds sys) (GetState sys) EmptyQCerts [req]) in
    (system "" (GetEnvState env') (GetReplicas sys)).

Fixpoint getCommonLedger (state : SysState) (replicas: SysReplicas) (gLedger : Ledger) :=
match replicas with
    | nil => Some gLedger
    | (rId, _)::t => if (beq_ledgers (state rId) gLedger) then (getCommonLedger state t gLedger)
                      else None
end.

Definition GetGlobalLedger (sys:System) : option Ledger :=
  let state := GetState sys in
    let gLedger := state "primary" in
      let replicas := GetReplicas sys in
         getCommonLedger state replicas gLedger.
(*
Definition NonFaulty (rId : ReplicaId) : Prop := True.
Definition MajorityNonFaulty (sys:System) : Prop := True.

Inductive StateValid : System -> Prop :=
| empty_valid : forall sys:System, (GetState sys) = EmptyState 
                  -> StateValid sys.


Lemma system_safety: forall (sys:System),
  MajorityNonFaulty sys
  -> StateValid sys
  -> forall (r:Request), StateValid (ProcessRequest sys r).
Proof. Admitted.

Theorem byzantine_fault_tolerant : forall (sys:System) (msgBox : MessageBox),
    MajorityNonFaulty sys 
    -> StateValid sys
    -> StateValid (ProcessAllMessages sys msgBox).
Proof. intros. destruct sys as [view state replicas].
induction msgBox. 
  - simpl in H0. simpl. apply H0.
  - induction replicas.
    + apply IHmsgBox.
    + apply system_safety; assumption.
Qed.*)

