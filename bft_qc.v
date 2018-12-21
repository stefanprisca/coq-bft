Require Import bft.
Require Import Maps.

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

Definition genFaultyReplica (id : nat) : G Replica :=
  elems [(FaultyReplica (show id))].

Definition genNFReplica (id : nat) : G Replica :=
  elems [(NFReplica (show id))].

Fixpoint genSystemSized (sz : nat) (F NFR nOf_nfr nOf_f : nat) : G (System) :=
  match sz with
    | O => ret [] 
    | S sz' =>
        if nOf_f =? F then 
          (liftM2 cons (genNFReplica sz') (genSystemSized sz'  F NFR (S nOf_nfr) nOf_f)) 
        else
          if nOf_nfr =? NFR then
            (liftM2 cons (genFaultyReplica sz') (genSystemSized sz' F NFR nOf_nfr (S nOf_f)))
          else
          oneOf [ (liftM2 cons (genNFReplica sz') (genSystemSized sz' F NFR (S nOf_nfr) nOf_f)) ;
                 (liftM2 cons (genFaultyReplica sz') (genSystemSized sz' F NFR nOf_nfr (S nOf_f)))
               ]
  end.

Definition newSysGen F := genSystemSized (3*F+1) F (2*F+1) 0 0.

Sample (newSysGen 10).

Definition CorrectSystem (F : nat) (sys:System) := 
   andb (count_system sys =? 3*F+1) (countNFR_system sys =? 2*F+1).

Definition CorrectState (F : nat) (st:bft.State) :=
   andb (count_state st =? 3*F+1) (countNFR_state st =? 2*F+1).

QuickChick ( forAll (newSysGen 10) (CorrectSystem 10)).

Definition CorrectInitState (F : nat) (sys:System) := 
  CorrectSystem F sys ==>
    let st := initState sys in
      andb (count_state st =? 3*F+1) (countNFR_state st =? 2*F+1).

QuickChick ( forAll (newSysGen 10) (CorrectInitState 10)).

Definition CorrectReplicateReqState (F : nat) (sys:System) := 
  CorrectSystem F sys ==>
    let st := ReplicateRequest sys (prePrep sys) (initState sys) in
      andb (count_state st =? 3*F+1) (countNFR_state st =? 2*F+1).

QuickChick ( forAll (newSysGen 10) (CorrectReplicateReqState 10)).

Instance ledgerAgreement_dec (st : bft.State) : Dec (LedgerAgreement st) := {}.
Proof. dec_eq. unfold LedgerAgreement. apply Forall_dec. 
unfold quorumCertified. destruct x. apply ge_dec.
Defined.

Definition LedgerAgreementReplicateReqState (F : nat) (sys:System) := 
  CorrectSystem F sys ==>
    let st := ReplicateRequest sys (prePrep sys) (initState sys) in
      (LedgerAgreement st)?.

QuickChick ( forAll (newSysGen 10) (LedgerAgreementReplicateReqState 10)).

Definition newPrePrep' (r: Replica) (n : nat) (msgs : total_map nat) := 
    match r with 
    | NFReplica id => msgs & {id --> nfrValue}
    | FaultyReplica id => msgs & {id --> nfrValue}
    end.

Fixpoint newPrePrepL (sys:list Replica) (vals : list nat) : (total_map nat):= 
  match sys, vals with
  | nil, nil => t_empty 0
  | (NFReplica id)::sys', v::vals' => (newPrePrepL sys' vals')&{id --> v}
  | (FaultyReplica id)::sys', v::vals' => (newPrePrepL sys' vals')&{id --> v}
  | _, _ => t_empty 0
  end.


Instance showState : Show (list (Replica * (list nat))) :=
{
  show := fun st:bft.State => 
            match st with
            | nil => show nil
            | (r, msgs)::t => "{ " ++ (show r) ++ " : " ++ (show msgs) ++ " }"
            end
}.

Definition ReplicateFaultyPrimary := 
    let size := 10 in
    let sys := (newSysGen size) in
    let vals := (vectorOf size (choose(0,100))) in
       liftM3 ReplicateRequest sys (liftM2 newPrePrepL sys vals) (liftM initState sys).

(* Fails as expected. The primary is faulty so the system does not reach ledger agreement *)
(* *** Failed after 1 tests and 0 shrinks. (0 discards)*)
QuickChick (forAll ReplicateFaultyPrimary (fun st => (LedgerAgreement st)?)).






