Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Export Coq.Strings.String.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import String.
Open Scope string_scope.

Definition total_map (A:Type) := string -> A.


Definition Replica := string.
Definition Ledger := string.

Definition SysView := string.
Definition SysState := string -> Ledger.
Definition SysReplicas := string -> Replica.

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


Definition State_empty : SysState :=  (fun _ => "None").
Definition Replicas_empty : SysReplicas :=  (fun _ => "None").

Check system.

Definition system1 := (system "foo" State_empty Replicas_empty).

