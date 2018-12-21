Require Import Coq.Bool.Bool.
Require Export Coq.Strings.String.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Maps.
Require Import String.
Open Scope string_scope.
Require Import Coq.omega.Omega.
Require PeanoNat.

Definition ReplicaId := string.

Inductive Replica : Set :=
| FaultyReplica : ReplicaId -> Replica
| NFReplica : ReplicaId -> Replica.

Definition IsNonFaulty (r:Replica) :  Prop :=
  match r with 
    | FaultyReplica _ => False
    | NFReplica _ => True
  end.

Definition State := list (Replica * (list nat)).

Definition ReplicaFun := total_map nat -> State -> State.

Definition nfrValue := 0.
Definition faultyValue := 100.

Fixpoint multicast (st:State) (v:nat) :=
  match st with
  | nil  => nil
  | (r, msgs)::t => (r, v::msgs)::(multicast t v)
  end.

Definition NFReplicaFun (id : ReplicaId) (msgs: total_map nat) (st:State) :=
       multicast st (msgs id).

Definition FaultyReplicaFun (id : ReplicaId) (msgs: total_map nat) (st:State) :=
       multicast st faultyValue.

Definition GetReplicaFun (r:Replica) : ReplicaFun :=
  match r with
  | FaultyReplica id => FaultyReplicaFun id
  | NFReplica id => NFReplicaFun id
  end.

Definition System := list Replica.

Fixpoint countNFR_state (st:State) :=
match st with
  | nil  => 0
  | (NFReplica _, _)::t => S (countNFR_state t)
  | _::t => countNFR_state t
  end.

Fixpoint countNFR_system (sys:System) :=
match sys with
  | nil  => 0
  | (NFReplica _)::t => S (countNFR_system t)
  | _::t => countNFR_system t
  end.


Fixpoint count_state (st:State) :=
match st with
  | nil  => 0
  | _::t => S (count_state t)
  end.


Fixpoint count_system (sys:System) :=
match sys with
  | nil  => 0
  | _::t => S (count_system t)
  end.

Definition initState (sys:list Replica) : State := ( (map (fun r => (r, nil)) sys)).

Definition newPrePrep (msgs : total_map nat) (r: Replica) : total_map nat := 
    match r with 
    | NFReplica id => msgs & {id --> nfrValue}
    | FaultyReplica id => msgs & {id --> nfrValue}
    end.

Definition prePrep (sys:list Replica) := 
    ( (fold_left newPrePrep sys (t_empty nfrValue) )).
Compute prePrep [(FaultyReplica "0"); (NFReplica "1")].


Fixpoint ReplicateRequest (sys : System) (msgs: total_map nat) (st : State):=
match sys with
  | nil => st
  | (r::sys') => (GetReplicaFun r) msgs (ReplicateRequest sys' msgs st)
  end.

Lemma faultyR_countNFR : forall (st:State) (id:ReplicaId) (prePrep : total_map nat),
       countNFR_state (FaultyReplicaFun id prePrep st) = countNFR_state st.
Proof. intros.
  induction st.
    - reflexivity.
    - destruct a. destruct r; simpl; rewrite <- IHst; reflexivity.
Qed.

Lemma nfR_countNFR : forall (st:State) (id:ReplicaId)
                            (prePrep : total_map nat),
       countNFR_state (NFReplicaFun id prePrep st) = countNFR_state st.
Proof. intros.
  induction st.
    - simpl. reflexivity.
    - destruct a. destruct r; simpl; rewrite <- IHst; reflexivity.
Qed.

Lemma initSt_nfrTrans : forall (sys:System),
    countNFR_state (initState sys) = countNFR_system sys.
Proof.
intros. induction sys.
  - auto.
  - destruct a; simpl; rewrite IHsys; auto.
Qed.

Lemma replicate_nfrTrans : forall (sys:System) (msgs : total_map nat) (st:State) ,
   countNFR_state (ReplicateRequest sys msgs st) = countNFR_state st.
Proof. intros sys. induction sys.
  - auto.
  - destruct a.
    + intros. simpl. rewrite faultyR_countNFR. apply IHsys.
    + intros. simpl. rewrite nfR_countNFR. apply IHsys.
Qed.

Lemma countNFR_state_system : forall sys:System,
    countNFR_system sys = countNFR_state (ReplicateRequest sys (prePrep sys) (initState sys)).
Proof. intros. induction sys.
  - reflexivity.
  - destruct a.
    + simpl. rewrite IHsys. 
      rewrite (replicate_nfrTrans sys (prePrep sys) (initState sys)).
      rewrite faultyR_countNFR.
      rewrite (replicate_nfrTrans sys (prePrep (FaultyReplica r :: sys))
                                  ((FaultyReplica r, []) :: initState sys)).
      auto.
    + simpl. rewrite IHsys. 
      rewrite (replicate_nfrTrans sys (prePrep sys) (initState sys)).
      rewrite nfR_countNFR.
      rewrite (replicate_nfrTrans sys (prePrep (NFReplica r :: sys))
                                  ((NFReplica r, []) :: initState sys)).
      auto.
Qed.


Definition CorrectSystem (sys:System) := 
    exists F,
    (count_system sys = 3*F+1) /\ (countNFR_system sys = 2*F+1).

Definition CorrectState (st:State) := 
    exists F,
    (count_state st = 3*F+1) /\ (countNFR_state st = 2*F+1).

Definition prePrepExt (msgs : total_map nat) (sys:System) := 
    msgs = prePrep sys \/ exists sys', msgs = prePrep (app sys' sys).

Lemma prePrepExt_refl : forall sys, prePrepExt(prePrep sys) sys.
  Proof. intros. unfold prePrepExt. left. auto.
Qed.

Axiom PrimaryNonFaulty : forall (sys:System) (msgs : total_map nat),
     prePrepExt msgs sys -> forall (id : ReplicaId), msgs id = nfrValue.

Fixpoint countNFR_msgs msgs :=
match msgs with
| nil => 0
| v::t => if (beq_nat v nfrValue) then ( (countNFR_msgs t ) + 1)
          else (countNFR_msgs t )
end.

Fixpoint nfrMsgsIncrementedBy (st1 st2 : State) (n : nat) :=
match st1, st2 with
| nil, _ => True
| (_, m1)::t1 , nil => (countNFR_msgs m1) = n /\ nfrMsgsIncrementedBy t1 nil n
| (_, m1)::t1, (_, m2)::t2 => (countNFR_msgs m1) = ((countNFR_msgs m2) + n)
                                /\ nfrMsgsIncrementedBy t1 t2 n
end.

Lemma nfrMsgsInc_reflexive: forall st:State,
    nfrMsgsIncrementedBy st st 0.
Proof.
  intros. induction st.
  - simpl. auto.
  - destruct a. simpl. split.
    + auto.
    + apply IHst.
Qed.

Lemma n_Sn : forall n:nat,
  n + 1 = S n.
Proof.
  apply nat_ind.
  - reflexivity.
  - simpl. intros. rewrite H. reflexivity.
Qed.

Lemma multicastNFV_nfrMsgsInc : forall (st base : State) (n:nat),
    nfrMsgsIncrementedBy st base n
      -> nfrMsgsIncrementedBy (multicast st nfrValue) base ( S n ).
Proof. intros st. induction st; intros; destruct base.
  - simpl. auto.
  - simpl. auto.
  - destruct a. simpl in H. simpl. destruct H. split.
    + rewrite H. rewrite n_Sn. auto.
    + apply IHst. apply H0.
  - destruct a. destruct p. simpl in H. destruct H. simpl. split.
    + symmetry. rewrite <- n_Sn. rewrite plus_assoc. rewrite H. auto.
    + apply IHst. apply H0.
Qed. 
 

Lemma multicastFV_nfrMsgsConst : forall (st base : State) (n:nat),
nfrMsgsIncrementedBy st base n
      -> nfrMsgsIncrementedBy (multicast st faultyValue) base n.
Proof.
intros st. simpl. induction st.
  - intros. simpl. auto.
  - intros. destruct a. destruct base.
    + simpl. simpl in H. split.
      { apply H. } { apply IHst. apply H. }
    + destruct p. simpl. simpl in H. destruct H. split.
      { apply H. } { apply IHst. apply H0. } 
Qed.

Lemma multicast_nfrvInc : forall (st : State),
    nfrMsgsIncrementedBy (multicast st nfrValue) st 1.
Proof.
intros. induction st.
- reflexivity.
- destruct a. simpl. split. { auto. } { assumption. }
Qed.


Lemma nfrIncNfrMsgs : forall (sys : System) (r:Replica),
IsNonFaulty r 
  -> nfrMsgsIncrementedBy (ReplicateRequest (r::sys) (prePrep (r::sys)) ( initState (r::sys) ))
                  (ReplicateRequest (sys) (prePrep (r::sys)) ( initState (r::sys) ))
                  1.
Proof. intros.
  destruct r.
    - inversion H.
    - simpl. unfold NFReplicaFun. 
      rewrite (PrimaryNonFaulty (NFReplica r :: sys) (prePrep (NFReplica r :: sys))). 
      apply multicast_nfrvInc. unfold prePrepExt. left. auto.
Qed.

Lemma appcons_comm : forall (A:Type) (l1 l2 : list A) (a : A),
    app l1 (a::l2) = app (app l1 [a]) l2. intros.
Proof. destruct l1; destruct l2; simpl; auto.
  - rewrite <- app_assoc. rewrite app_nil_r. auto.
  - rewrite <- app_assoc. simpl. auto.
Qed.

Lemma procReq_nfrInc: forall (sys :System) (st : State) (msgs : total_map nat),
    prePrepExt msgs sys ->
    nfrMsgsIncrementedBy (ReplicateRequest sys msgs st)
                            st
                            (countNFR_system sys).
Proof.
intros sys. remember (countNFR_system sys) as n. generalize dependent n. induction sys.
  - simpl. intros. simpl in Heqn. rewrite Heqn. apply nfrMsgsInc_reflexive.
  - intros. simpl. destruct a.
    + simpl. simpl in Heqn. unfold FaultyReplicaFun. apply multicastFV_nfrMsgsConst.
      apply IHsys. apply Heqn. destruct H.
      { unfold prePrepExt. right. exists [FaultyReplica r].  simpl. apply H. }
      { 
        unfold prePrepExt. right. inversion H. 
        rewrite appcons_comm in H0. exists (app x [FaultyReplica r]). apply H0.
      }
    + simpl. simpl in Heqn. unfold NFReplicaFun. 
      rewrite (PrimaryNonFaulty (NFReplica r :: sys)).
      { rewrite Heqn.
        apply multicastNFV_nfrMsgsInc. apply IHsys.
        - auto.
        - destruct H.
          { unfold prePrepExt. right. exists [FaultyReplica r].  simpl. apply H. }
          { 
            unfold prePrepExt. right. inversion H. 
            rewrite appcons_comm in H0. exists (app x [NFReplica r]). apply H0.
          }
      }
      { apply H. }
Qed.

Definition quorumCertified (nfrSS : State) (r: (Replica * list nat)) :=
    match r with
    | (_, msgs) => countNFR_msgs msgs >= countNFR_state nfrSS
    end.

Definition LedgerAgreement (st : State) := Forall (quorumCertified st) st.

Definition msgsGte (n : nat) (r: (Replica * list nat)) :=
    match r with
    | (_, msgs) => countNFR_msgs msgs >= n
    end.


Definition msgsEq (n : nat) (r: (Replica * list nat)) :=
    match r with
    | (_, msgs) => countNFR_msgs msgs = n
    end.
(* 
Lemma gte_plus : forall n m: nat, m + n >= n.
Proof. intros. induction n; induction m; Omega.omega.
Qed. *)

Lemma nfrMsgsInc_base_ind : forall (st base : State) (r:Replica) (lr: list nat) (n : nat), 
    Forall (msgsEq 0) (((r, lr) :: base))
      -> (nfrMsgsIncrementedBy st base n) = (nfrMsgsIncrementedBy st ((r, lr) :: base) n).
Proof. intros st. induction st. auto.
  - intros. destruct a. destruct base.
    + simpl. inversion H. inversion H2. rewrite H5. simpl. auto.
    + destruct p. simpl. 
      rewrite (IHst base r1 l0 n).
      {
        inversion H; clear H. inversion H3; clear H3. subst. inversion H2; clear H2.
        inversion H5; clear H5. rewrite H0. rewrite H1. auto.
      }
      { inversion H. apply H3. }
Qed.


Lemma nfrMsgsInc_base0 : forall (st base : State) (n : nat), 
         Forall (msgsEq 0) (base)
              -> nfrMsgsIncrementedBy st base n = nfrMsgsIncrementedBy st [] n.
Proof.
  intros. inversion H. destruct H0. 
    - auto.
    - induction st. auto. destruct a. destruct x. simpl.
      simpl in H0. rewrite H0. simpl. rewrite <- IHst. 
      rewrite (nfrMsgsInc_base_ind st l r0 l1 n) . auto.  
      subst. apply H.
Qed.

Lemma nfrMsgsInc_baseCount : forall (st base : State) (r : Replica) (l : list nat) (n : nat),
  nfrMsgsIncrementedBy ((r, l) :: st) base n -> countNFR_msgs l >= n. 
intros. induction base.
  - simpl in H. Omega.omega.
  - destruct a. simpl in H. Omega.omega.
Qed.

Lemma nfrIncN_nfrMsgs : forall (st base: State) (n : nat),
  Forall (msgsEq 0) (base)
   -> nfrMsgsIncrementedBy st base n
    -> Forall (msgsGte n) st.
Proof. intros st base n HBase H. induction st. auto. constructor.
  - destruct a. simpl. apply (nfrMsgsInc_baseCount st base r l n). apply H.
  - apply IHst; clear IHst. destruct base.
    + destruct a. induction H. apply H0.
    + destruct a. destruct p. induction H.
      inversion HBase. rewrite nfrMsgsInc_base0. 
      rewrite nfrMsgsInc_base0 in H0. 
      { apply H0. } { apply H4. } { subst. constructor; assumption. }
Qed.

Lemma quorumCertifiedState : forall (st base : State),
    Forall (msgsEq 0) base
    -> nfrMsgsIncrementedBy st base (countNFR_state st)
    -> LedgerAgreement st.
Proof.
  intros. unfold LedgerAgreement. unfold quorumCertified. 
      remember (countNFR_state (st)) as n. 
      apply (nfrIncN_nfrMsgs st base n). apply H. apply H0.
Qed.

Lemma initSt_msgEq0 : forall sys, Forall (msgsEq 0) (initState sys).
Proof. intros. unfold initState. induction sys.
  - simpl. constructor.
  - simpl. constructor; simpl; auto.
Qed. 

Theorem BFT : forall (sys:System),
      LedgerAgreement (ReplicateRequest sys (prePrep sys) (initState sys)).
Proof.
  intros. 
    apply (quorumCertifiedState (ReplicateRequest sys (prePrep sys) (initState sys)) (initState sys)).
    - apply initSt_msgEq0.
    - rewrite <- countNFR_state_system. apply procReq_nfrInc. apply prePrepExt_refl.
Qed.
