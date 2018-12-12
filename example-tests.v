Require Import bft.
Require Import Maps.
Require Import Coq.Lists.List.
Import ListNotations.

Definition one_replicas : SysReplicas := ("foo", fun _ _ _ => empty_state)::empty_replicas.
Definition system1 := (system "foo" empty_state one_replicas).
Definition m1 := <<"foo", "1">>.
Definition twoMsgBox := [m1 ; m1].

Example sysEmptyTest : GetState (ProcessAllMessages system1 twoMsgBox) = empty_state.
Proof. reflexivity. Qed.

Example stValid_ProcMessages_sys1 : StateValid (ProcessAllMessages system1 twoMsgBox).
Proof. constructor. reflexivity.   Qed.

Print Replica.
Print Ledger.

Definition active_replicas : SysReplicas :=  
      ("foo" , fun sysSt msg mb => sysSt & {"foo" --> (empty_ledger & { (get_pLoad msg) --> 1 }) } )
      ::empty_replicas.
Definition systemActive := (system "foo" empty_state active_replicas).
Example stValid_ProcMessages_sysActive : StateValid (ProcessAllMessages systemActive twoMsgBox).
Proof.  repeat apply system_safety; constructor; reflexivity.
Qed.

Definition multiple_active_replicas : SysReplicas :=
      ("foo" , fun sysSt msg mb => sysSt & {"foo" --> (empty_ledger & { (get_pLoad msg) --> 1 }) } )
      :: ("bar" , fun sysSt msg mb => sysSt & {"bar" --> (empty_ledger & { (get_pLoad msg) --> 1 }) } )
      :: ("baz" , fun sysSt msg mb => sysSt & {"baz" --> (empty_ledger & { (get_pLoad msg) --> 1 }) } )
      ::empty_replicas.

Definition multi_replica_sys := (system "" empty_state multiple_active_replicas).
Definition multi_replica_msgBox := [<<"foo", "1">> ; <<"bar" , "1">>; <<"baz" , "1">>].

Example stValid_ProcMessages_multi_replicas : StateValid (ProcessAllMessages multi_replica_sys multi_replica_msgBox).
Proof.  repeat apply system_safety; constructor; reflexivity.
Qed.


