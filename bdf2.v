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

Definition State := list (Replica * nat).

Definition IsNonFaulty (r:Replica) :  Prop :=
  match r with 
    | FaultyReplica => False
    | NFReplica => True
  end.

Definition ReplicaFun := State -> string -> State.

Definition NFReplicaFun (st:State) (msg:string):=
      match st with
      | nil => [(NFReplica, 0)]
      | (h, d)::t => (NFReplica, d)::(h, d)::t
      end
.

Definition NewReplicaFun (r:Replica) : ReplicaFun :=
  match r with
  | FaultyReplica => fun st m => st
  | NFReplica => NFReplicaFun
  end.


Definition System := list (Replica * ReplicaFun).

Fixpoint ProcessRequest (sys : System) (m : string) (st : State) : State :=
  match sys with
  | nil => st
  | (r,rFun)::t => (rFun (ProcessRequest t m st) m) 
  end.

Definition dumb1 := [(NFReplica, NewReplicaFun NFReplica); 
                  (NFReplica, NewReplicaFun NFReplica); (NFReplica, NewReplicaFun NFReplica)].
Compute ProcessRequest dumb1 "bla" nil.

Fixpoint getLedgerHelper (st:State) (l:nat) : option nat :=
match st with
| nil => Some l
| (NFReplica, l)::t => getLedgerHelper t l
| (FaultyReplica, _)::t => getLedgerHelper t l
end.

Fixpoint GetLedger (st:State) : option nat :=
match st with
| nil => None
| (NFReplica, ledger)::t => getLedgerHelper t ledger
| (FaultyReplica, _)::t => GetLedger t
end.

Inductive StateValid : State -> Prop :=
| empty_valid : StateValid nil
| nonfaulty_valid : forall (r: Replica) (st:State) , IsNonFaulty r -> 
                StateValid st -> forall d:nat, (GetLedger st) = Some d -> StateValid ((r, d)::st)
| faulty_valid : forall (r: Replica) (st:State) , ~(IsNonFaulty r) -> StateValid st
                -> forall d:nat, StateValid ((r, d)::st).

(* Need to link the output d from above to the replica R. We need to know that this came from there, and
is not just a random d*)

Theorem system_safety : forall (sys : System) (m:string),
      StateValid (ProcessRequest sys m nil).
Proof. intros. induction ProcessRequest.
  - constructor.
  - destruct a as [r d]. induction r.
    + apply faulty_valid.
      { unfold not. intros contra. inversion contra. }
      { apply IHs. }
    + apply nonfaulty_valid.
      { reflexivity. }
      { apply IHs. }
      { admit. }
Admitted.

