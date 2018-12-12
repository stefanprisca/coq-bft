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
Definition SysView := string.

Inductive Message : Type := 
| message: ReplicaId -> string -> Message.

Notation "<< rId , pLoad >>" := (message rId pLoad).


Definition get_rId (msg : Message) : ReplicaId :=
  match msg with
  | message x y => x
  end.

Definition get_pLoad (msg : Message) : string :=
  match msg with
  | message x y => y
  end.

Definition Ledger := total_map nat.
Definition SysState := total_map Ledger.
Definition MessageBox := list Message.
Definition Replica := SysState -> Message -> MessageBox -> SysState.
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


Definition empty_ledger : Ledger :=  (fun _ => 0).
Definition empty_state : SysState :=  (fun _ => empty_ledger).
Definition empty_replicas : SysReplicas :=  nil.

Definition ProcessMessage (sys:System) (rId : ReplicaId) (msg:Message) (msgBox : MessageBox) :=
 match (FindReplica sys rId) with
    | None => sys
    | Some replica =>
      let sysState' := (replica (GetState sys) msg msgBox) in
        (system "foo" sysState' (GetReplicas sys))
  end.

Fixpoint ProcessAllMessages (sys:System) (msgBox: MessageBox) : System := 
  match msgBox with
  | nil => sys
  | msg::t => let rId := get_rId msg in
              let sys' := ProcessMessage sys rId msg msgBox in
                ProcessAllMessages sys' t
  end
.

Definition Request := string.

Definition ProcessRequest (sys : System) (req : Request) :=
  ProcessAllMessages sys [<<"foo", req>>].

Definition NonFaulty (rId : ReplicaId) : Prop := True.
Definition MajorityNonFaulty (sys:System) : Prop := True.

Inductive StateValid : System -> Prop :=
| empty_valid : forall sys:System, (GetState sys) = empty_state 
                  -> StateValid sys.


Lemma system_safety: forall (sys:System) (msgBox:MessageBox),
  MajorityNonFaulty sys
  -> StateValid (ProcessAllMessages sys msgBox)
  -> forall (m:Message), StateValid (ProcessAllMessages sys (m::msgBox)).
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
Qed.

