Require Import bft.
Require Import Maps.
Require Import Coq.Lists.List.
Import ListNotations.

Definition replicas1 : SysReplicas := ("foo", fun env _ => env)::EmptyReplicas.
Definition system1 := (system "foo" EmptyState replicas1).
Definition m1 := <<REQ "foo", "1">>.
Definition twoMsgBox := [m1 ; m1].
Print ExecEnvironment.
Definition execEnv1 := (execEnv (GetReplicaIds system1) EmptyState EmptyQCerts nil).

Example sysEmptyTest : GetEnvState (ProcessAllMessages MaxMessages system1 execEnv1) = EmptyState.
Proof. reflexivity. Qed.

Definition activeReplicas1 : SysReplicas :=  
      ("foo" , NFReplica )
      ::EmptyReplicas.
Definition activeSystem1 := (system "" EmptyState activeReplicas1).
Definition activeEnv1 := (execEnv (GetReplicaIds activeSystem1) (EmptyState) EmptyQCerts [<<REQ "1", "foo"  >> ]).

Compute (GetEnvState (ProcessAllMessages MaxMessages activeSystem1 activeEnv1)) "foo".
Example activeSystem1_noState : (GetEnvState (ProcessAllMessages MaxMessages activeSystem1 activeEnv1)) = EmptyState.
Proof. reflexivity. Qed.

Compute (GetEnvQCerts (ProcessAllMessages MaxMessages activeSystem1 activeEnv1)) "foo".
Example activeSystem1_oneCertificate : length ((GetEnvQCerts (ProcessAllMessages MaxMessages activeSystem1 activeEnv1)) "foo") = 1.
Proof. reflexivity. Qed.

Compute (GetEnvMsgBox (ProcessAllMessages MaxMessages activeSystem1 activeEnv1)).
Example activeSystem1_emptyMessages : length (GetEnvMsgBox (ProcessAllMessages MaxMessages activeSystem1 activeEnv1)) = 0.
Proof. reflexivity. Qed.

Definition multipleActiveReplicas : SysReplicas :=
      ("foo" , NFReplica )::("foo1" , NFReplica )::("foo2" , NFReplica )::("primary" , NFReplica )::("foo4" , NFReplica )
      ::("foo5" , NFReplica )::("foo6" , NFReplica )::("foo7" , NFReplica )
      ::("foo9" , NFReplica )::("foo8" , NFReplica )::EmptyReplicas.

Definition multiReplicaSys := (system "" EmptyState multipleActiveReplicas).
Definition multiReplicaEnv := (execEnv (GetReplicaIds multiReplicaSys) (EmptyState) EmptyQCerts [<<REQ "digest", "primary" >>]).

Compute (GetEnvState (ProcessAllMessages MaxMessages multiReplicaSys multiReplicaEnv)) "foo5".
Compute (GetState (ProcessRequest multiReplicaSys <<REQ "digest", "primary" >>)) "foo".

Example procRequest_multiReplicaSys : (GetState (ProcessRequest multiReplicaSys <<REQ "digest", "primary" >>) ) "primary" = [("digest", 0)].
Proof. reflexivity. Qed.

Definition processedSys := ProcessRequest multiReplicaSys <<REQ "digest", "primary" >>.

Example globalLedgerConsistent : let sys' := (ProcessRequest multiReplicaSys <<REQ "digest", "primary" >>) in 
                                  GetGlobalLedger sys' =  Some ((GetState sys') "primary").
Proof. intros. reflexivity. 
Qed.



