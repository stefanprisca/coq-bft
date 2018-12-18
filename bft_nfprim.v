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

Inductive State : Type :=
| prePrep: (Replica * nat) -> State
| prep : (Replica * nat) -> State -> State.

Definition ReplicaFun := State -> string -> State.

Definition nfrValue := 0.
Definition faultyValue := 100.

Fixpoint getPrimaryValue (st:State) : nat :=
    match st with
    | prePrep (P, n) => n
    | prep _ t => getPrimaryValue t
    end.

Definition NFReplicaFun (st:State) (req:string):=
      match st with
      | prePrep (P, n) => prep (NFReplica, n) (prePrep (P, n))
      | st => prep (NFReplica, (getPrimaryValue st)) st
      end
.

Definition GetReplicaFun (r:Replica) : ReplicaFun :=
  match r with
  | FaultyReplica => fun st m => prep (FaultyReplica, faultyValue) st
  | NFReplica => NFReplicaFun
  end.


Inductive System : Type :=
| primary : Replica -> System
| replica : Replica -> System -> System.


Fixpoint ProcessRequest (sys : System) (req : string) : State :=
  match sys with
  | primary P => prePrep (P, nfrValue)
  | replica r sys' => ((GetReplicaFun r) (ProcessRequest sys' req) req) 
  end.


Lemma getPrimaryValue_nfrValue: forall (sys:System) (req: string),
      getPrimaryValue (ProcessRequest sys req) = nfrValue.
Proof. intros. induction sys.
  - reflexivity.
  - remember (ProcessRequest sys req) as st. 
    simpl. rewrite <- Heqst. induction st;
      destruct p; induction r; simpl; simpl in IHsys; apply IHsys.
Qed.

(* TODO: NFR state should be quorum value. *)
Lemma NFR_state_nfrValue: forall r:Replica, IsNonFaulty r
         -> forall (sys:System) (req:string), 
              ProcessRequest (replica r sys) req 
               = (prep (r, nfrValue) (ProcessRequest sys req)).
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

