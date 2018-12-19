
Require Import bft2.

Require Import Arith Bool List ZArith. Import ListNotations.
From QuickChick Require Import QuickChick. Import QcNotation.

(* Suppress some annoying warnings: *)
Set Warnings "-extraction-opaque-accessed,-extraction".

Require Export ExtLib.Structures.Monads.
Export MonadNotation. Open Scope monad_scope.

Require Import String. Local Open Scope string.


Instance showReplica : Show Replica :=
{
  show := fun r:Replica => 
            match r with
            | NFReplica id => "NF_" ++ id
            | FaultyReplica id => "F_" ++ id
            end
}.

Definition F := 2.
Definition SystemSize := 3*F+1.
Definition NofNFReplicas := 2*F+1.

Definition genFaultyReplica (id : nat) : G Replica :=
  elems [(FaultyReplica (show id))].

Definition genNFReplica (id : nat) : G Replica :=
  elems [(NFReplica (show id))].

Fixpoint genSystemSized (sz : nat) (nOf_nfr nOf_f : nat) : G (System) :=
  match sz with
    | O => ret [] 
    | S sz' =>
        if nOf_f =? F then 
          (liftM2 cons (genNFReplica sz') (genSystemSized sz' (S nOf_nfr) nOf_f)) 
        else
          if nOf_nfr =? NofNFReplicas then
            (liftM2 cons (genFaultyReplica sz') (genSystemSized sz' nOf_nfr (S nOf_f)))
          else
          oneOf [ (liftM2 cons (genNFReplica sz') (genSystemSized sz' (S nOf_nfr) nOf_f)) ;
                 (liftM2 cons (genFaultyReplica sz') (genSystemSized sz' nOf_nfr (S nOf_f)))
               ]
  end.

Sample (genSystemSized SystemSize 0 0).

Definition CorrectSystem (sys:System) := 
    andb (count_system sys =? 3*F+1) (countNFR_system sys =? 2*F+1).

QuickChick ( forAll (genSystemSized SystemSize 0 0) CorrectSystem ).

Definition CorrectInitState (sys:System) := 
  CorrectSystem sys ==>
    let st := initState sys in
      andb (count_state st =? 3*F+1) (countNFR_state st =? 2*F+1).

QuickChick ( forAll (genSystemSized SystemSize 0 0) CorrectInitState).

Conjecture CountSize_Consistent : forall (sys:System),
  (count_system sys) = count_state (ReplicateRequest sys (prePrep sys) (initState sys)).

QuickChick CountSize_Consistent.