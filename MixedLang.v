Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Arith.Arith.
From PLF Require Import Maps.
From PLF Require Import Imp.
From PLF Require Import Smallstep.
Inductive exp : Type :=
| EId : string -> exp
| ETrue : exp
| EFalse : exp
| ENat : nat -> exp
| EIsZero : exp -> exp.

Inductive value : exp -> Prop :=
| VTrue : value ETrue
| VFalse : value EFalse
| VNat : forall n, value ( ENat n).
Hint Constructors value.

Inductive com : Type :=
| CSkip : com
| CAss : string -> exp -> com
| CSeq : com -> com -> com
| CIf : exp -> com -> com -> com
| CWhile : exp -> com -> com.

Notation "'SKIP'" := CSkip (at level 0 ).
Notation "l '::=' e" := ( CAss l e) (at level 60 ).
Notation "c1 ;; c2" := ( CSeq c1 c2) (at level 80 , right associativity).
Notation "'TEST' b 'THEN' c1 'ELSE' c2 'FI'" := ( CIf b c1 c2) (at level
80 , right associativity).
Notation "'WHILE' b 'DO' c 'END'" := ( CWhile b c) (at level 80 , right
associativity).
Definition state := partial_map exp.


Reserved Notation " t '\' s '--->e' t1 " (at level 40, s at level 39).

Inductive estep  (s : state) : exp -> exp -> Prop :=
  | ES_True:  ETrue \ s --->e ETrue 
  | ES_False:  EFalse \ s --->e EFalse 
  | ES_Nat: forall n, (ENat n) \ s --->e (ENat n)
  | ES_IsZero: forall  x, x \ s --->e ENat 0 -> EIsZero(x) \s --->e ETrue 
  | ES_IsNotZeroNat: forall  x n, 
             x \ s --->e ENat n -> n>0 
                          ->
           EIsZero(x) \ s --->e EFalse
  | ES_EId : forall e v, (s e) = Some(v) -> EId e \ s --->e v


 where " t '\' s '--->e' t1 " := ( estep s t t1).


Reserved Notation " t '\' st '--->c' t' '\' st' " 
                  (at level 40, st at level 39, t' at level 39).

Inductive cstep : (com * state) -> (com * state) -> Prop :=
  | CS_Skip : forall st, SKIP \ st --->c SKIP \ st

  | CS_Ass : forall st i n ex,
       ex \ st --->e n 
            ->
       cstep (<{ CAss i  ex }>,st) (<{ CSkip }>,i!-> Some( n);st) 


  | CS_SeqStep : forall st c1 c1' st' c2,
      c1 \ st --->c c1' \ st' -> (c1=SKIP -> False) ->
      <{ CSeq c1 c2 }> \ st --->c <{ CSeq c1' c2 }> \ st'

   | CS_SeqFinish : forall st c2,
      <{ <{ CSeq CSkip  c2 }> }> \ st --->c c2 \ st

  | CS_IfT: forall st b c1 c2,
       b \ st --->e ETrue  
              ->
       <{ CIf b  c1  c2 }> \ st --->c c1 \ st

  | CS_IfF: forall st b c1 c2,
       b \ st --->e EFalse 
              ->
       <{ CIf b  c1  c2 }> \ st --->c c1 \ st

  | CS_While: forall st b1 c1,
    <{ CWhile  b1  c1  }> \ st  --->c
     <{ CIf b1 <{ CSeq c1 <{ CWhile b1  c1 }> }> <{ CSkip }> }>  \ st 



  where " t '\' st '--->c' t' '\' st' " := (cstep (t,st) (t',st')).




Notation "t1 '-->*' t2" := (multi cstep t1 t2) (at level 40 ).

Notation " c1 '/' st1 '-->*' c2 '/' st2 " :=
(multi cstep (c1,st1) (c2,st2))
(at level 40 , st1 at level 39 , c2 at level 39 ).





                 (* --------------Question 3------------ *)


Ltac rwd H1 H2 := rewrite H1 in H2; discriminate.

Ltac find_rwd :=
  match goal with
    H1: ?E = true,
    H2: ?E = false
    |- _ => rwd H1 H2
 end.

Ltac find_eqn :=
  match goal with
    H1: forall x, ?P x -> ?L = ?R,
    H2: ?P ?X
    |- _ => rewrite (H1 X H2) in *
  end.


Theorem estep_deterministic :
  forall st,
  deterministic (estep st). 
Proof.
  unfold deterministic.
  intros c st y1 y2 E1 E2.
  generalize dependent y2;
  induction E1;
  intros st2 E2; inversion E2; subst; repeat find_eqn;
  try find_rwd; auto. assert(ENat 0 = ENat n). apply IHE1.
  apply H0. inversion H. rewrite <- H3 in H1. inversion H1.
  assert(ENat n= ENat 0). 
  apply IHE1.
  apply H1. inversion H0. rewrite  H3 in H. inversion H. rewrite H in H1. simpl in H1.
  inversion H1. auto. 
Qed.


Theorem cstep_deterministic :
  deterministic (cstep). 
Proof.
  unfold deterministic.
  intros st y1 y2 E1 E2.
  generalize dependent y2;
  induction E1;
  intros st2 E2; inversion E2; subst; repeat find_eqn;
  try find_rwd; auto. 
  * assert(n = n0). generalize H,H4. apply estep_deterministic. rewrite H0. auto.
  * induction c1;try(assert((c1', st') = (c1'0,st'0)));try(apply IHE1);try( apply H4);try(inversion H0);auto.
  * assert(False). apply H. auto. destruct H0.
  * assert(False). apply H4. auto. destruct H.
Qed.



(* Question 2 *)

(* Question 2-a *)

Definition Qa : com :=
<{CSeq <{CAss X (ENat 1)}> <{CAss Y ETrue}> }>.


Example proveA :
forall st st',      
st' = (Y !-> Some(ETrue) ; (X !-> Some (ENat 1) ;st)) ->
Qa / st -->* SKIP/st'.

Proof.
intros. 
eapply multi_step. apply CS_SeqStep. apply CS_Ass. apply ES_Nat.
intros. inversion H0.
 eapply multi_step.
apply CS_SeqFinish.
eapply multi_step.
apply CS_Ass.
apply ES_True.
rewrite <- H.
eapply multi_refl.
Qed.

(* Question 2-b *)
Definition Qb : com :=
<{CIf (EIsZero (EId X)) <{CAss X (ENat 2)}> <{CAss X (ENat 4)}>}>. 

Example proveB:
forall  st' st,
     (st X = Some (ENat 0) -> st' =  (t_update st X  (Some( ENat 2))) ->
     Qb / st  -->* SKIP/ st') 
     /\
     ( forall i, i>0 -> st X = Some (ENat i) -> st' =  (t_update st X  (Some( ENat 4))) ->
     Qb / st  -->* SKIP/ st').

Proof.
intros. split. intros.
eapply multi_step.
apply CS_IfT.
apply ES_IsZero.
apply ES_EId. 
Admitted.
(* rewrite H0 in H.
apply H.
eapply multi_step.
apply CS_Ass.
apply ES_Nat.
rewrite <- H1.
apply multi_refl.
intros.
eapply multi_step.
apply CS_IfF.
apply ES_IsNotZeroNat with i.
apply ES_EId.
apply H.
apply H0.
rewrite H1.
eapply multi_step.
apply CS_Ass.
apply ES_Nat.
Qed. *)

(* Question 2-c *)

Definition Qc : com :=
<{ CWhile <{ ETrue }> <{SKIP}>}>.


Example proveC : forall st st' c',
 cstep (Qc , st) (c' , st') ->  ((c' / st'-->* Qc / st) /\ (Qc=SKIP->False)).
Proof.
Admitted.





Inductive ty : Type :=
| Bool : ty
| Nat : ty.

Definition state_typing := partial_map ty.

Reserved Notation "ST '|-' t '\in' T" (at level 90 ).
Inductive has_type ( ST : state_typing) : exp -> ty -> Prop :=
  | T_True : ST |- ETrue \in Bool
  | T_False : ST |- EFalse \in Bool
  | T_Nat : forall n, ST |- (ENat n) \in Nat
  | T_step : forall x T, ST (x) = Some(T) -> ST |- (EId x) \in T
  | T_Zero : forall n, ST |- n \in Nat -> ST |- EIsZero(n) \in Bool
where " ST |- e '\in' T " := (has_type ST e T ).

Hint Constructors has_type.

Reserved Notation " ST '||-' c " (at level 90 ).
Inductive well_typed ( ST : state_typing) : com -> Prop :=
| WT_Skip : ST ||- SKIP

| WT_Seq : forall c1 c2, (ST ||- c1) -> (ST ||- c2) -> (ST ||- c1 ;; c2)

| WT_Ass : forall l e T, (ST |- e \in T) -> (ST ||- l ::= e)

| WT_If : forall b c1 c2, (ST |- b \in  Bool) -> (ST ||- c1) -> (ST ||- c2) -> (ST ||- TEST b THEN c1 ELSE c2 FI)

| WT_While : forall a b , (ST |- a \in Bool) ->(ST ||- b) ->(ST ||- WHILE a DO b END)

where " ST '||-' c " := (well_typed ST c).

Hint Constructors well_typed.



Definition has_state_type (st : state) ( ST : state_typing) : Prop :=
forall x T ,
ST x = Some T ->
exists e, st x = Some e /\ ( ST |- e \in T ).


Theorem progress_e : forall t st ST T,
     has_state_type st ST ->
     ST |- t \in T ->
     value t \/ (exists t', estep st t t').
Proof.
  intros t.
  induction t; intros; auto.
    - right. inversion H0.
      assert(exists t', st s = Some t' /\ ( ST |- t' \in T )).
       auto. inversion H4. exists x0. apply ES_EId. apply eq_sym. inversion H5. auto.
    - right. inversion H0. inversion H2. destruct n0.
      + exists ETrue. apply ES_IsZero. apply ES_Nat.
      + exists EFalse. apply ES_IsNotZeroNat with (n := S n0). apply ES_Nat. apply Nat.lt_0_succ.
      + assert(value t \/ (exists t' : exp, estep st t t')). apply IHt with (ST:=ST) (st:=st)(T:=Nat);auto.
        inversion H7;subst;try solve_by_invert. 
        inversion H8.  assert(exists e, st x = Some e /\ ( ST |- e \in Nat )). generalize H. auto. inversion H3.
        inversion H5. inversion H9. induction n. assert(EId x \ st --->e x1). apply ES_EId. auto. rewrite <- H10 in H11. assert(x0=ENat 0).
        generalize H11. generalize H1. apply estep_deterministic. exists (ETrue). apply ES_IsZero. auto.
        assert(EId x \ st --->e x1). apply ES_EId. auto. rewrite <- H10 in H11. assert(x0=ENat (S n)).
        generalize H11. generalize H1. apply estep_deterministic. exists (EFalse).  assert(S n >0). apply gt_Sn_O.
        generalize H13. generalize H11. remember (S n) as m.  apply ES_IsNotZeroNat. 
        inversion H7. inversion H13. Admitted.





Theorem preservation_e : forall t t' st ST T,
  has_state_type st ST ->
  ST |- t \in T ->
  estep  st t t' ->
  ST |- t' \in T.
Proof.
intros t t' st ST T H HT HE.
generalize dependent t'.
induction HT;
       intros t' HE;
       try solve_by_invert;auto.
  - inversion HE; subst; clear HE.
    +  apply T_True.
  -  inversion HE; subst; clear HE. apply T_False.
  -  inversion HE; subst; clear HE. apply T_Nat.
  - inversion HE; subst; auto. 
    + assert(exists e, st x = Some e /\ ( ST |- e \in T )). generalize H0. auto.
      inversion H1. destruct H3. assert(Some t' = Some x0). rewrite <-  H2. rewrite <-  H3. auto.
      inversion H5. apply H4.
  - inversion HE; subst; auto. 
Qed.





