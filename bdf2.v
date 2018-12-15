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

Definition nfrValue := 1.
Definition NFReplicaFun (st:State) (msg:string):=
      match st with
      | nil => [(NFReplica, nfrValue)]
      | (h, d)::t => (NFReplica, nfrValue)::(h, d)::t
      end
.

Definition GetReplicaFun (r:Replica) : ReplicaFun :=
  match r with
  | FaultyReplica => fun st m => st
  | NFReplica => NFReplicaFun
  end.


Definition System := list Replica.


Fixpoint ProcessRequest (sys : System) (m : string) (st : State) : State :=
  match sys with
  | nil => st
  | r::t => ((GetReplicaFun r) (ProcessRequest t m st) m) 
  end.

Lemma NFR_appends_state: forall r:Replica, IsNonFaulty r
         -> forall (sys:System) (req:string), 
              ProcessRequest (r::sys) req nil 
               = ((r, nfrValue)::(ProcessRequest sys req nil)).
Proof. intros.
  generalize dependent sys. induction r.
  - inversion H.
  - simpl. intros. destruct (ProcessRequest sys req []).
    + simpl. reflexivity.
    + destruct p. simpl. reflexivity.
Qed. 


Definition dumb1 := [NFReplica; NFReplica; FaultyReplica; NFReplica].
Compute ProcessRequest dumb1 "bla" nil.

Fixpoint GetLedger (st:State) (d: nat) : option nat :=
match st with
| nil => None
| (NFReplica, l)::t => if (beq_nat d l) then (GetLedger t d)
                        else None
| (FaultyReplica, _)::t => GetLedger t d
end.

Lemma NFR_maintains_ledger:  
        forall (sys:System) (req:string) (r:Replica) , 
            IsNonFaulty r
         -> (GetLedger (ProcessRequest sys req nil) nfrValue) 
            = (GetLedger (ProcessRequest (r::sys) req nil) nfrValue).
Proof. intros. rewrite NFR_appends_state.
  - induction r.
    + simpl. reflexivity.
    + simpl. reflexivity.
  - assumption.
Qed.

Inductive StateValid : State -> Prop :=
| empty_valid : StateValid nil
| nonfaulty_valid : forall (sys:System) (req:string) (r:Replica) , 
              IsNonFaulty r 
              -> StateValid (ProcessRequest sys req nil)
                -> (GetLedger (ProcessRequest sys req nil) nfrValue) 
                     = (GetLedger (ProcessRequest (r::sys) req nil) nfrValue) 
                    -> StateValid ((ProcessRequest (r::sys) req nil))
| faulty_valid : forall (sys:System) (req:string) (r:Replica) , ~(IsNonFaulty r) -> 
      StateValid (ProcessRequest sys req nil) -> StateValid ((ProcessRequest (r::sys) req nil)).

Theorem system_safety : forall (sys : System) (m:string),
      StateValid (ProcessRequest sys m nil).
Proof. intros. induction sys.
  - constructor.
  - induction a.
    + apply faulty_valid.
      { unfold not. intros contra. inversion contra. }
      { assumption. }
    + apply nonfaulty_valid.
      { reflexivity. }
      { assumption. }
      { apply NFR_maintains_ledger. reflexivity. }
Qed.

