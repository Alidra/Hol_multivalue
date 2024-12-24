Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import TRANSITIVE_STEPWISE_LE_EQ_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import EXISTS_REFL_spec.
Require Import LEFT_FORALL_IMP_THM_spec.
Require Import LEFT_IMP_EXISTS_THM_spec.
Require Import LE_EXISTS_spec.
Require Import LE_REFL_spec.
Require Import SWAP_FORALL_THM_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1820_spec.
Require Import thm1821_spec.
Require Import thm1832_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm32_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm89498_spec.
Lemma lem286706 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem286707 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem286708 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem286707 t1) (@lem286706 t1)). Qed.
Lemma lem286709 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem286708 t1 t2). Qed.
Lemma lem286710 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem286711 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem286710 t1 t2) (@lem286709 t1 t2)). Qed.
Lemma lem286712 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem286711 t1 t2 t3). Qed.
Lemma lem286713 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem286714 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem286713 t1 t2 t3) (@lem286712 t1 t2 t3)). Qed.
Lemma lem286715 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem286714 t1 t2 t3)). Qed.
Lemma lem286716 : term7.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem286717 : term8.
Proof. exact (proj2 (@lem286716)). Qed.
Lemma lem286718 : term9.
Proof. exact (proj2 (@lem286717)). Qed.
Lemma lem286719 (m : nat) : term10 m.
Proof. exact (@lem286718 m). Qed.
Lemma lem286720 (m : nat) : (term10 m) = (term11 m).
Proof. exact (eq_refl (term10 m)). Qed.
Lemma lem286721 (m : nat) : term11 m.
Proof. exact (EQ_MP (@lem286720 m) (@lem286719 m)). Qed.
Lemma lem286722 (m : nat) (n : nat) : term12 m n.
Proof. exact (@lem286721 m n). Qed.
Lemma lem286723 (m : nat) (n : nat) : (term12 m n) = ((term13 m n) = (term14 m n)).
Proof. exact (eq_refl (term12 m n)). Qed.
Lemma lem286732 : term15.
Proof. exact (proj1 (@lem286716)). Qed.
Lemma lem286733 (m : nat) : term16 m.
Proof. exact (@lem286732 m). Qed.
Lemma lem286734 (m : nat) : (term16 m) = ((term17 m) = m).
Proof. exact (eq_refl (term16 m)). Qed.
Lemma lem286764 {A : Type'} (a : A) : term18 A a.
Proof. exact (@lem4363 A a). Qed.
Lemma lem286765 {A : Type'} (a : A) : (term18 A a) = (term19 A a).
Proof. exact (eq_refl (term18 A a)). Qed.
Lemma lem286766 {A : Type'} (a : A) : term19 A a.
Proof. exact (EQ_MP (@lem286765 A a) (@lem286764 A a)). Qed.
Lemma lem286767 {A : Type'} (a : A) : (term19 A a) = ((term19 A a) = True).
Proof. exact (@lem7 (term19 A a)). Qed.
Lemma lem286769 {A : Type'} (P : A -> Prop) : term20 A P.
Proof. exact (@lem6754 A P). Qed.
Lemma lem286770 {A : Type'} (P : A -> Prop) : (term20 A P) = (term21 A P).
Proof. exact (eq_refl (term20 A P)). Qed.
Lemma lem286771 {A : Type'} (P : A -> Prop) : term21 A P.
Proof. exact (EQ_MP (@lem286770 A P) (@lem286769 A P)). Qed.
Lemma lem286772 {A : Type'} (P : A -> Prop) (Q : Prop) : term22 A P Q.
Proof. exact (@lem286771 A P Q). Qed.
Lemma lem286773 {A : Type'} (P : A -> Prop) (Q : Prop) : (term22 A P Q) = ((term23 A P Q) = (term24 A P Q)).
Proof. exact (eq_refl (term22 A P Q)). Qed.
Lemma lem286775 {A B : Type'} (P : type1413 A B) : term25 A B P.
Proof. exact (@lem4792 A B P). Qed.
Lemma lem286776 {A B : Type'} (P : type1413 A B) : (term25 A B P) = ((term26 A B P) = (term27 A B P)).
Proof. exact (eq_refl (term25 A B P)). Qed.
Lemma lem286778 {A : Type'} (P : A -> Prop) : term28 A P.
Proof. exact (@lem6644 A P). Qed.
Lemma lem286779 {A : Type'} (P : A -> Prop) : (term28 A P) = (term29 A P).
Proof. exact (eq_refl (term28 A P)). Qed.
Lemma lem286780 {A : Type'} (P : A -> Prop) : term29 A P.
Proof. exact (EQ_MP (@lem286779 A P) (@lem286778 A P)). Qed.
Lemma lem286781 {A : Type'} (P : A -> Prop) (Q : Prop) : term30 A P Q.
Proof. exact (@lem286780 A P Q). Qed.
Lemma lem286782 {A : Type'} (P : A -> Prop) (Q : Prop) : (term30 A P Q) = ((term24 A P Q) = (term23 A P Q)).
Proof. exact (eq_refl (term30 A P Q)). Qed.
Lemma lem286784 (m : nat) : term31 m.
Proof. exact (@lem99708 m). Qed.
Lemma lem286785 (m : nat) : (term31 m) = (term32 m).
Proof. exact (eq_refl (term31 m)). Qed.
Lemma lem286786 (m : nat) : term32 m.
Proof. exact (EQ_MP (@lem286785 m) (@lem286784 m)). Qed.
Lemma lem286787 (m : nat) (n : nat) : term33 m n.
Proof. exact (@lem286786 m n). Qed.
Lemma lem286788 (n : nat) (m : nat) : (term33 m n) = ((Peano.le m n) = (term34 n m)).
Proof. exact (eq_refl (term33 m n)). Qed.
Lemma lem286790 (R : type1605) (h1 : term35 R) : term35 R.
Proof. exact (h1). Qed.
Lemma lem286791 (R : type1605) (h1 : term36 R) : term36 R.
Proof. exact (h1). Qed.
Lemma lem286792 (R : type1605) (h1 : term37 R) : term37 R.
Proof. exact (h1). Qed.
Lemma lem286793 (n : nat) : term38 n.
Proof. exact (@lem91603 n). Qed.
Lemma lem286794 (n : nat) : (term38 n) = (Peano.le n n).
Proof. exact (eq_refl (term38 n)). Qed.
Lemma lem286795 (n : nat) : Peano.le n n.
Proof. exact (EQ_MP (@lem286794 n) (@lem286793 n)). Qed.
Lemma lem286796 (n : nat) : (Peano.le n n) = ((Peano.le n n) = True).
Proof. exact (@lem7 (Peano.le n n)). Qed.
Lemma lem286798 : term39.
Proof. exact (proj2 (@lem89498)). Qed.
Lemma lem286799 (m : nat) : term40 m.
Proof. exact (@lem286798 m). Qed.
Lemma lem286800 (m : nat) : (term40 m) = (term41 m).
Proof. exact (eq_refl (term40 m)). Qed.
Lemma lem286801 (m : nat) : term41 m.
Proof. exact (EQ_MP (@lem286800 m) (@lem286799 m)). Qed.
Lemma lem286802 (m : nat) (n : nat) : term42 m n.
Proof. exact (@lem286801 m n). Qed.
Lemma lem286803 (m : nat) (n : nat) : (term42 m n) = ((term43 m n) = (term44 m n)).
Proof. exact (eq_refl (term42 m n)). Qed.
Lemma lem286861 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term45 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem286862 (p : Prop) (q : Prop) (p' : Prop) : term46 p q p'.
Proof. exact (fun q' : Prop => @lem286861 p q p' q'). Qed.
Lemma lem286863 (p : Prop) (q : Prop) : term47 p q.
Proof. exact (fun p' : Prop => @lem286862 p q p'). Qed.
Lemma lem286864 (R : type1605) : term48 R.
Proof. exact (@lem286863 (term49 R) (term50 R)). Qed.
Lemma lem286865 (R : type1605) (p' : Prop) : term51 R p'.
Proof. exact (@lem286864 R p'). Qed.
Lemma lem286866 (R : type1605) (p' : Prop) : (term51 R p') = (term52 R p').
Proof. exact (eq_refl (term51 R p')). Qed.
Lemma lem286867 (R : type1605) (p' : Prop) : term52 R p'.
Proof. exact (EQ_MP (@lem286866 R p') (@lem286865 R p')). Qed.
Lemma lem286868 (R : type1605) (p' : Prop) (q' : Prop) : term53 R p' q'.
Proof. exact (@lem286867 R p' q'). Qed.
Lemma lem286869 (R : type1605) (p' : Prop) (q' : Prop) : (term53 R p' q') = (term54 R p' q').
Proof. exact (eq_refl (term53 R p' q')). Qed.
Lemma lem286870 (R : type1605) (p' : Prop) (q' : Prop) : term54 R p' q'.
Proof. exact (EQ_MP (@lem286869 R p' q') (@lem286868 R p' q')). Qed.
Lemma lem287168 (R : type1605) : (term49 R) = (term49 R).
Proof. exact (eq_refl (term49 R)). Qed.
Lemma lem287169 (R : type1605) (q' : Prop) : term55 R q'.
Proof. exact (@lem286870 R (term49 R) q'). Qed.
Lemma lem287170 (R : type1605) (q' : Prop) : term56 R q'.
Proof. exact (@lem287169 R q' (@lem287168 R)). Qed.
Lemma lem287171 (R : type1605) (h1 : term49 R) : term49 R.
Proof. exact (h1). Qed.
Lemma lem287172 (m : nat) (R : type1605) (h1 : term49 R) : term57 R m.
Proof. exact (@lem287171 R h1 m). Qed.
Lemma lem287173 (R : type1605) (m : nat) : (term57 R m) = (term58 R m).
Proof. exact (eq_refl (term57 R m)). Qed.
Lemma lem287174 (m : nat) (R : type1605) (h1 : term49 R) : term58 R m.
Proof. exact (EQ_MP (@lem287173 R m) (@lem287172 m R h1)). Qed.
Lemma lem287175 (m : nat) (n : nat) (R : type1605) (h1 : term49 R) : term59 R m n.
Proof. exact (@lem287174 m R h1 n). Qed.
Lemma lem287176 (R : type1605) (m : nat) (n : nat) : (term59 R m n) = (term60 R m n).
Proof. exact (eq_refl (term59 R m n)). Qed.
Lemma lem287177 (m : nat) (n : nat) (R : type1605) (h1 : term49 R) : term60 R m n.
Proof. exact (EQ_MP (@lem287176 R m n) (@lem287175 m n R h1)). Qed.
Lemma lem287178 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem287179 (R : type1605) (m : nat) (n : nat) (h1 : term49 R) (h2 : Peano.le m n) : R m n.
Proof. exact (@lem287177 m n R h1 (@lem287178 m n h2)). Qed.
Lemma lem287180 (R : type1605) (m : nat) (n : nat) : (R m n) = ((R m n) = True).
Proof. exact (@lem7 (R m n)). Qed.
Lemma lem287181 (R : type1605) (m : nat) (n : nat) (h1 : term49 R) (h2 : Peano.le m n) : (R m n) = True.
Proof. exact (EQ_MP (@lem287180 R m n) (@lem287179 R m n h1 h2)). Qed.
Lemma lem287401 (m : nat) (n : nat) (R : type1605) (h1 : term49 R) : term61 R m n.
Proof. exact (fun h0 : Peano.le m n => @lem287181 R m n h1 h0). Qed.
Lemma lem287402 (n : nat) (R : type1605) (h1 : term49 R) : term62 R n.
Proof. exact (@lem287401 n (S n) R h1). Qed.
Lemma lem287404 (m : nat) (n : nat) : (term43 m n) = (term44 m n).
Proof. exact (EQ_MP (@lem286803 m n) (@lem286802 m n)). Qed.
Lemma lem287405 (n : nat) : (term63 n) = (term64 n).
Proof. exact (@lem287404 n n). Qed.
Lemma lem287411 (n : nat) : (Peano.le n n) = True.
Proof. exact (EQ_MP (@lem286796 n) (@lem286795 n)). Qed.
Lemma lem287412 (n : nat) : (term65 n) = (term65 n).
Proof. exact (eq_refl (term65 n)). Qed.
Lemma lem287413 (n : nat) : (term64 n) = (term66 n).
Proof. exact (MK_COMB (@lem287412 n) (@lem287411 n)). Qed.
Lemma lem287415 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem287416 (n : nat) : (term66 n) = True.
Proof. exact (@lem287415 (n = (S n))). Qed.
Lemma lem287417 (n : nat) : (term64 n) = True.
Proof. exact (TRANS (@lem287413 n) (@lem287416 n)). Qed.
Lemma lem287418 (n : nat) : (term63 n) = True.
Proof. exact (TRANS (@lem287405 n) (@lem287417 n)). Qed.
Lemma lem287419 (n : nat) : True = (term63 n).
Proof. exact (SYM (@lem287418 n)). Qed.
Lemma lem287420 (n : nat) : term63 n.
Proof. exact (EQ_MP (@lem287419 n) (@lem0)). Qed.
Lemma lem287421 (n : nat) (R : type1605) (h1 : term49 R) : (term67 R n) = True.
Proof. exact (@lem287402 n R h1 (@lem287420 n)). Qed.
Lemma lem287422 (R : type1605) (h1 : term49 R) : (term68 R) = term69.
Proof. exact (fun_ext (fun n : nat => @lem287421 n R h1)). Qed.
Lemma lem287423 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem287424 (R : type1605) (h1 : term49 R) : (term50 R) = term70.
Proof. exact (MK_COMB (@lem287423) (@lem287422 R h1)). Qed.
Lemma lem287426 {A : Type'} (t : Prop) : (term71 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem287427 (t : Prop) : (term72 t) = t.
Proof. exact (@lem287426 nat t). Qed.
Lemma lem287428 : term70 = True.
Proof. exact (@lem287427 True). Qed.
Lemma lem287429 (R : type1605) (h1 : term49 R) : (term50 R) = True.
Proof. exact (TRANS (@lem287424 R h1) (@lem287428)). Qed.
Lemma lem287430 (R : type1605) : term73 R.
Proof. exact (fun h0 : term49 R => @lem287429 R h0). Qed.
Lemma lem287431 (R : type1605) : term74 R.
Proof. exact (@lem287170 R True). Qed.
Lemma lem287432 (R : type1605) : (term75 R) = (term76 R).
Proof. exact (@lem287431 R (@lem287430 R)). Qed.
Lemma lem287434 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem287435 (R : type1605) : (term76 R) = True.
Proof. exact (@lem287434 (term49 R)). Qed.
Lemma lem287436 (R : type1605) : (term75 R) = True.
Proof. exact (TRANS (@lem287432 R) (@lem287435 R)). Qed.
Lemma lem287437 (R : type1605) : True = (term75 R).
Proof. exact (SYM (@lem287436 R)). Qed.
Lemma lem287438 (R : type1605) : term75 R.
Proof. exact (EQ_MP (@lem287437 R) (@lem0)). Qed.
Lemma lem288396 (R : type1605) (h1 : term50 R) : term50 R.
Proof. exact (h1). Qed.
Lemma lem288408 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term45 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem288409 (p : Prop) (q : Prop) (p' : Prop) : term46 p q p'.
Proof. exact (fun q' : Prop => @lem288408 p q p' q'). Qed.
Lemma lem288410 (p : Prop) (q : Prop) : term47 p q.
Proof. exact (fun p' : Prop => @lem288409 p q p'). Qed.
Lemma lem288411 (R : type1605) (m : nat) (n : nat) : term77 R m n.
Proof. exact (@lem288410 (Peano.le m n) (R m n)). Qed.
Lemma lem288412 (R : type1605) (m : nat) (n : nat) (p' : Prop) : term78 R m n p'.
Proof. exact (@lem288411 R m n p'). Qed.
Lemma lem288413 (R : type1605) (m : nat) (n : nat) (p' : Prop) : (term78 R m n p') = (term79 R m n p').
Proof. exact (eq_refl (term78 R m n p')). Qed.
Lemma lem288414 (R : type1605) (m : nat) (n : nat) (p' : Prop) : term79 R m n p'.
Proof. exact (EQ_MP (@lem288413 R m n p') (@lem288412 R m n p')). Qed.
Lemma lem288415 (R : type1605) (m : nat) (n : nat) (p' : Prop) (q' : Prop) : term80 R m n p' q'.
Proof. exact (@lem288414 R m n p' q'). Qed.
Lemma lem288416 (R : type1605) (m : nat) (n : nat) (p' : Prop) (q' : Prop) : (term80 R m n p' q') = (term81 R m n p' q').
Proof. exact (eq_refl (term80 R m n p' q')). Qed.
Lemma lem288417 (R : type1605) (m : nat) (n : nat) (p' : Prop) (q' : Prop) : term81 R m n p' q'.
Proof. exact (EQ_MP (@lem288416 R m n p' q') (@lem288415 R m n p' q')). Qed.
Lemma lem288419 (n : nat) (m : nat) : (Peano.le m n) = (term34 n m).
Proof. exact (EQ_MP (@lem286788 n m) (@lem286787 m n)). Qed.
Lemma lem288426 (R : type1605) (n : nat) (m : nat) (q' : Prop) : term82 R n m q'.
Proof. exact (@lem288417 R m n (term34 n m) q'). Qed.
Lemma lem288427 (R : type1605) (n : nat) (m : nat) (q' : Prop) : term83 R n m q'.
Proof. exact (@lem288426 R n m q' (@lem288419 n m)). Qed.
Lemma lem288431 (R : type1605) (m : nat) (n : nat) : (R m n) = (R m n).
Proof. exact (eq_refl (R m n)). Qed.
Lemma lem288432 (R : type1605) (m : nat) (n : nat) : term84 R m n.
Proof. exact (fun h0 : term34 n m => @lem288431 R m n). Qed.
Lemma lem288433 (R : type1605) (m : nat) (n : nat) : term85 R m n.
Proof. exact (@lem288427 R n m (R m n)). Qed.
Lemma lem288434 (R : type1605) (m : nat) (n : nat) : (term60 R m n) = (term86 R m n).
Proof. exact (@lem288433 R m n (@lem288432 R m n)). Qed.
Lemma lem288436 {A : Type'} (P : A -> Prop) (Q : Prop) : (term24 A P Q) = (term23 A P Q).
Proof. exact (EQ_MP (@lem286782 A P Q) (@lem286781 A P Q)). Qed.
Lemma lem288437 (P : nat -> Prop) (Q : Prop) : (term87 P Q) = (term88 P Q).
Proof. exact (@lem288436 nat P Q). Qed.
Lemma lem288438 (R : type1605) (m : nat) (n : nat) : (term89 R m n) = (term90 R m n).
Proof. exact (@lem288437 (term91 n m) (R m n)). Qed.
Lemma lem288439 (n : nat) (m : nat) (d : nat) : (term92 n m d) = (n = (Nat.add m d)).
Proof. exact (eq_refl (term92 n m d)). Qed.
Lemma lem288440 (n : nat) (m : nat) : (term93 n m) = (term91 n m).
Proof. exact (fun_ext (fun d : nat => @lem288439 n m d)). Qed.
Lemma lem288441 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem288442 (n : nat) (m : nat) : (term94 n m) = (term34 n m).
Proof. exact (MK_COMB (@lem288441) (@lem288440 n m)). Qed.
Lemma lem288443 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem288444 (n : nat) (m : nat) : (term95 n m) = (term96 n m).
Proof. exact (MK_COMB (@lem288443) (@lem288442 n m)). Qed.
Lemma lem288445 (R : type1605) (m : nat) (n : nat) : (R m n) = (R m n).
Proof. exact (eq_refl (R m n)). Qed.
Lemma lem288446 (R : type1605) (m : nat) (n : nat) : (term89 R m n) = (term86 R m n).
Proof. exact (MK_COMB (@lem288444 n m) (@lem288445 R m n)). Qed.
Lemma lem288447 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem288448 (R : type1605) (m : nat) (n : nat) : (term97 R m n) = (term98 R m n).
Proof. exact (MK_COMB (@lem288447) (@lem288446 R m n)). Qed.
Lemma lem288449 (n : nat) (m : nat) (d : nat) : (term92 n m d) = (n = (Nat.add m d)).
Proof. exact (eq_refl (term92 n m d)). Qed.
Lemma lem288450 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem288451 (n : nat) (m : nat) (d : nat) : (term99 n m d) = (term100 n m d).
Proof. exact (MK_COMB (@lem288450) (@lem288449 n m d)). Qed.
Lemma lem288452 (R : type1605) (m : nat) (n : nat) : (R m n) = (R m n).
Proof. exact (eq_refl (R m n)). Qed.
Lemma lem288453 (d : nat) (R : type1605) (m : nat) (n : nat) : (term101 d R m n) = (term102 d R m n).
Proof. exact (MK_COMB (@lem288451 n m d) (@lem288452 R m n)). Qed.
Lemma lem288454 (R : type1605) (m : nat) (n : nat) : (term103 R m n) = (term104 R m n).
Proof. exact (fun_ext (fun d : nat => @lem288453 d R m n)). Qed.
Lemma lem288455 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem288456 (R : type1605) (m : nat) (n : nat) : (term90 R m n) = (term105 R m n).
Proof. exact (MK_COMB (@lem288455) (@lem288454 R m n)). Qed.
Lemma lem288457 (R : type1605) (m : nat) (n : nat) : ((term89 R m n) = (term90 R m n)) = ((term86 R m n) = (term105 R m n)).
Proof. exact (MK_COMB (@lem288448 R m n) (@lem288456 R m n)). Qed.
Lemma lem288458 (R : type1605) (m : nat) (n : nat) : (term86 R m n) = (term105 R m n).
Proof. exact (EQ_MP (@lem288457 R m n) (@lem288438 R m n)). Qed.
Lemma lem288468 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term45 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem288469 (p : Prop) (q : Prop) (p' : Prop) : term46 p q p'.
Proof. exact (fun q' : Prop => @lem288468 p q p' q'). Qed.
Lemma lem288470 (p : Prop) (q : Prop) : term47 p q.
Proof. exact (fun p' : Prop => @lem288469 p q p'). Qed.
Lemma lem288471 (d : nat) (R : type1605) (m : nat) (n : nat) : term106 d R m n.
Proof. exact (@lem288470 (n = (Nat.add m d)) (R m n)). Qed.
Lemma lem288472 (d : nat) (R : type1605) (m : nat) (n : nat) (p' : Prop) : term107 d R m n p'.
Proof. exact (@lem288471 d R m n p'). Qed.
Lemma lem288473 (d : nat) (R : type1605) (m : nat) (n : nat) (p' : Prop) : (term107 d R m n p') = (term108 d R m n p').
Proof. exact (eq_refl (term107 d R m n p')). Qed.
Lemma lem288474 (d : nat) (R : type1605) (m : nat) (n : nat) (p' : Prop) : term108 d R m n p'.
Proof. exact (EQ_MP (@lem288473 d R m n p') (@lem288472 d R m n p')). Qed.
Lemma lem288475 (d : nat) (R : type1605) (m : nat) (n : nat) (p' : Prop) (q' : Prop) : term109 d R m n p' q'.
Proof. exact (@lem288474 d R m n p' q'). Qed.
Lemma lem288476 (d : nat) (R : type1605) (m : nat) (n : nat) (p' : Prop) (q' : Prop) : (term109 d R m n p' q') = (term110 d R m n p' q').
Proof. exact (eq_refl (term109 d R m n p' q')). Qed.
Lemma lem288477 (d : nat) (R : type1605) (m : nat) (n : nat) (p' : Prop) (q' : Prop) : term110 d R m n p' q'.
Proof. exact (EQ_MP (@lem288476 d R m n p' q') (@lem288475 d R m n p' q')). Qed.
Lemma lem288480 (n : nat) (m : nat) (d : nat) : (n = (Nat.add m d)) = (n = (Nat.add m d)).
Proof. exact (eq_refl (n = (Nat.add m d))). Qed.
Lemma lem288481 (R : type1605) (n : nat) (m : nat) (d : nat) (q' : Prop) : term111 R n m d q'.
Proof. exact (@lem288477 d R m n (n = (Nat.add m d)) q'). Qed.
Lemma lem288482 (R : type1605) (n : nat) (m : nat) (d : nat) (q' : Prop) : term112 R n m d q'.
Proof. exact (@lem288481 R n m d q' (@lem288480 n m d)). Qed.
Lemma lem288485 (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : n = (Nat.add m d).
Proof. exact (h1). Qed.
Lemma lem288486 (R : type1605) (m : nat) : (R m) = (R m).
Proof. exact (eq_refl (R m)). Qed.
Lemma lem288487 (R : type1605) (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : (R m n) = (term113 R m d).
Proof. exact (MK_COMB (@lem288486 R m) (@lem288485 n m d h1)). Qed.
Lemma lem288488 (n : nat) (R : type1605) (m : nat) (d : nat) : term114 n R m d.
Proof. exact (fun h0 : n = (Nat.add m d) => @lem288487 R n m d h0). Qed.
Lemma lem288489 (n : nat) (R : type1605) (m : nat) (d : nat) : term115 n R m d.
Proof. exact (@lem288482 R n m d (term113 R m d)). Qed.
Lemma lem288490 (n : nat) (R : type1605) (m : nat) (d : nat) : (term102 d R m n) = (term116 n R m d).
Proof. exact (@lem288489 n R m d (@lem288488 n R m d)). Qed.
Lemma lem288518 (n : nat) (R : type1605) (m : nat) : (term104 R m n) = (term117 n R m).
Proof. exact (fun_ext (fun d : nat => @lem288490 n R m d)). Qed.
Lemma lem288546 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem288547 (n : nat) (R : type1605) (m : nat) : (term105 R m n) = (term118 n R m).
Proof. exact (MK_COMB (@lem288546) (@lem288518 n R m)). Qed.
Lemma lem288579 (n : nat) (R : type1605) (m : nat) : (term86 R m n) = (term118 n R m).
Proof. exact (TRANS (@lem288458 R m n) (@lem288547 n R m)). Qed.
Lemma lem288580 (n : nat) (R : type1605) (m : nat) : (term60 R m n) = (term118 n R m).
Proof. exact (TRANS (@lem288434 R m n) (@lem288579 n R m)). Qed.
Lemma lem288581 (R : type1605) (m : nat) : (term119 R m) = (term120 R m).
Proof. exact (fun_ext (fun n : nat => @lem288580 n R m)). Qed.
Lemma lem288613 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem288614 (R : type1605) (m : nat) : (term58 R m) = (term121 R m).
Proof. exact (MK_COMB (@lem288613) (@lem288581 R m)). Qed.
Lemma lem288650 (R : type1605) : (term122 R) = (term123 R).
Proof. exact (fun_ext (fun m : nat => @lem288614 R m)). Qed.
Lemma lem288686 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem288687 (R : type1605) : (term49 R) = (term124 R).
Proof. exact (MK_COMB (@lem288686) (@lem288650 R)). Qed.
Lemma lem288727 (R : type1605) : (term124 R) = (term49 R).
Proof. exact (SYM (@lem288687 R)). Qed.
Lemma lem288729 {A B : Type'} (P : type1413 A B) : (term26 A B P) = (term27 A B P).
Proof. exact (EQ_MP (@lem286776 A B P) (@lem286775 A B P)). Qed.
Lemma lem288730 (P : type1605) : (term125 P) = (term126 P).
Proof. exact (@lem288729 nat nat P). Qed.
Lemma lem288731 (R : type1605) (m : nat) : (term127 R m) = (term128 R m).
Proof. exact (@lem288730 (term129 R m)). Qed.
Lemma lem288732 (n : nat) (R : type1605) (m : nat) : (term130 R m n) = (term117 n R m).
Proof. exact (eq_refl (term130 R m n)). Qed.
Lemma lem288733 (d : nat) : d = d.
Proof. exact (eq_refl d). Qed.
Lemma lem288734 (n : nat) (R : type1605) (m : nat) (d : nat) : (term131 R m n d) = (term132 n R m d).
Proof. exact (MK_COMB (@lem288732 n R m) (@lem288733 d)). Qed.
Lemma lem288735 (n : nat) (R : type1605) (m : nat) (d : nat) : (term132 n R m d) = (term116 n R m d).
Proof. exact (eq_refl (term132 n R m d)). Qed.
Lemma lem288736 (n : nat) (R : type1605) (m : nat) (d : nat) : (term131 R m n d) = (term116 n R m d).
Proof. exact (TRANS (@lem288734 n R m d) (@lem288735 n R m d)). Qed.
Lemma lem288737 (n : nat) (R : type1605) (m : nat) : (term133 R m n) = (term117 n R m).
Proof. exact (fun_ext (fun d : nat => @lem288736 n R m d)). Qed.
Lemma lem288738 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem288739 (n : nat) (R : type1605) (m : nat) : (term134 R m n) = (term118 n R m).
Proof. exact (MK_COMB (@lem288738) (@lem288737 n R m)). Qed.
Lemma lem288740 (R : type1605) (m : nat) : (term135 R m) = (term120 R m).
Proof. exact (fun_ext (fun n : nat => @lem288739 n R m)). Qed.
Lemma lem288741 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem288742 (R : type1605) (m : nat) : (term127 R m) = (term121 R m).
Proof. exact (MK_COMB (@lem288741) (@lem288740 R m)). Qed.
Lemma lem288743 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem288744 (R : type1605) (m : nat) : (term136 R m) = (term137 R m).
Proof. exact (MK_COMB (@lem288743) (@lem288742 R m)). Qed.
Lemma lem288745 (n : nat) (R : type1605) (m : nat) : (term130 R m n) = (term117 n R m).
Proof. exact (eq_refl (term130 R m n)). Qed.
Lemma lem288746 (d : nat) : d = d.
Proof. exact (eq_refl d). Qed.
Lemma lem288747 (n : nat) (R : type1605) (m : nat) (d : nat) : (term131 R m n d) = (term132 n R m d).
Proof. exact (MK_COMB (@lem288745 n R m) (@lem288746 d)). Qed.
Lemma lem288748 (n : nat) (R : type1605) (m : nat) (d : nat) : (term132 n R m d) = (term116 n R m d).
Proof. exact (eq_refl (term132 n R m d)). Qed.
Lemma lem288749 (n : nat) (R : type1605) (m : nat) (d : nat) : (term131 R m n d) = (term116 n R m d).
Proof. exact (TRANS (@lem288747 n R m d) (@lem288748 n R m d)). Qed.
Lemma lem288750 (R : type1605) (m : nat) (d : nat) : (term138 R m d) = (term139 R m d).
Proof. exact (fun_ext (fun n : nat => @lem288749 n R m d)). Qed.
Lemma lem288751 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem288752 (R : type1605) (m : nat) (d : nat) : (term140 R m d) = (term141 R m d).
Proof. exact (MK_COMB (@lem288751) (@lem288750 R m d)). Qed.
Lemma lem288753 (R : type1605) (m : nat) : (term142 R m) = (term143 R m).
Proof. exact (fun_ext (fun d : nat => @lem288752 R m d)). Qed.
Lemma lem288754 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem288755 (R : type1605) (m : nat) : (term128 R m) = (term144 R m).
Proof. exact (MK_COMB (@lem288754) (@lem288753 R m)). Qed.
Lemma lem288756 (R : type1605) (m : nat) : ((term127 R m) = (term128 R m)) = ((term121 R m) = (term144 R m)).
Proof. exact (MK_COMB (@lem288744 R m) (@lem288755 R m)). Qed.
Lemma lem288757 (R : type1605) (m : nat) : (term121 R m) = (term144 R m).
Proof. exact (EQ_MP (@lem288756 R m) (@lem288731 R m)). Qed.
Lemma lem288758 (R : type1605) (m : nat) : (term144 R m) = (term121 R m).
Proof. exact (SYM (@lem288757 R m)). Qed.
Lemma lem288764 {A : Type'} (P : A -> Prop) (Q : Prop) : (term23 A P Q) = (term24 A P Q).
Proof. exact (EQ_MP (@lem286773 A P Q) (@lem286772 A P Q)). Qed.
Lemma lem288765 (P : nat -> Prop) (Q : Prop) : (term88 P Q) = (term87 P Q).
Proof. exact (@lem288764 nat P Q). Qed.
Lemma lem288766 (R : type1605) (m : nat) (d : nat) : (term145 R m d) = (term146 R m d).
Proof. exact (@lem288765 (term147 m d) (term113 R m d)). Qed.
Lemma lem288767 (n : nat) (m : nat) (d : nat) : (term148 m d n) = (n = (Nat.add m d)).
Proof. exact (eq_refl (term148 m d n)). Qed.
Lemma lem288768 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem288769 (n : nat) (m : nat) (d : nat) : (term149 m d n) = (term100 n m d).
Proof. exact (MK_COMB (@lem288768) (@lem288767 n m d)). Qed.
Lemma lem288770 (R : type1605) (m : nat) (d : nat) : (term113 R m d) = (term113 R m d).
Proof. exact (eq_refl (term113 R m d)). Qed.
Lemma lem288771 (n : nat) (R : type1605) (m : nat) (d : nat) : (term150 n R m d) = (term116 n R m d).
Proof. exact (MK_COMB (@lem288769 n m d) (@lem288770 R m d)). Qed.
Lemma lem288772 (R : type1605) (m : nat) (d : nat) : (term151 R m d) = (term139 R m d).
Proof. exact (fun_ext (fun n : nat => @lem288771 n R m d)). Qed.
Lemma lem288773 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem288774 (R : type1605) (m : nat) (d : nat) : (term145 R m d) = (term141 R m d).
Proof. exact (MK_COMB (@lem288773) (@lem288772 R m d)). Qed.
Lemma lem288775 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem288776 (R : type1605) (m : nat) (d : nat) : (term152 R m d) = (term153 R m d).
Proof. exact (MK_COMB (@lem288775) (@lem288774 R m d)). Qed.
Lemma lem288777 (n : nat) (m : nat) (d : nat) : (term148 m d n) = (n = (Nat.add m d)).
Proof. exact (eq_refl (term148 m d n)). Qed.
Lemma lem288778 (m : nat) (d : nat) : (term154 m d) = (term147 m d).
Proof. exact (fun_ext (fun n : nat => @lem288777 n m d)). Qed.
Lemma lem288779 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem288780 (m : nat) (d : nat) : (term155 m d) = (term156 m d).
Proof. exact (MK_COMB (@lem288779) (@lem288778 m d)). Qed.
Lemma lem288781 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem288782 (m : nat) (d : nat) : (term157 m d) = (term158 m d).
Proof. exact (MK_COMB (@lem288781) (@lem288780 m d)). Qed.
Lemma lem288783 (R : type1605) (m : nat) (d : nat) : (term113 R m d) = (term113 R m d).
Proof. exact (eq_refl (term113 R m d)). Qed.
Lemma lem288784 (R : type1605) (m : nat) (d : nat) : (term146 R m d) = (term159 R m d).
Proof. exact (MK_COMB (@lem288782 m d) (@lem288783 R m d)). Qed.
Lemma lem288785 (R : type1605) (m : nat) (d : nat) : ((term145 R m d) = (term146 R m d)) = ((term141 R m d) = (term159 R m d)).
Proof. exact (MK_COMB (@lem288776 R m d) (@lem288784 R m d)). Qed.
Lemma lem288786 (R : type1605) (m : nat) (d : nat) : (term141 R m d) = (term159 R m d).
Proof. exact (EQ_MP (@lem288785 R m d) (@lem288766 R m d)). Qed.
Lemma lem288790 {A : Type'} (a : A) : (term19 A a) = True.
Proof. exact (EQ_MP (@lem286767 A a) (@lem286766 A a)). Qed.
Lemma lem288791 (a : nat) : (term160 a) = True.
Proof. exact (@lem288790 nat a). Qed.
Lemma lem288792 (m : nat) (d : nat) : (term156 m d) = True.
Proof. exact (@lem288791 (Nat.add m d)). Qed.
Lemma lem288793 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem288794 (m : nat) (d : nat) : (term158 m d) = (imp True).
Proof. exact (MK_COMB (@lem288793) (@lem288792 m d)). Qed.
Lemma lem288795 (R : type1605) (m : nat) (d : nat) : (term113 R m d) = (term113 R m d).
Proof. exact (eq_refl (term113 R m d)). Qed.
Lemma lem288796 (R : type1605) (m : nat) (d : nat) : (term159 R m d) = (term161 R m d).
Proof. exact (MK_COMB (@lem288794 m d) (@lem288795 R m d)). Qed.
Lemma lem288798 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem288799 (R : type1605) (m : nat) (d : nat) : (term161 R m d) = (term113 R m d).
Proof. exact (@lem288798 (term113 R m d)). Qed.
Lemma lem288800 (R : type1605) (m : nat) (d : nat) : (term159 R m d) = (term113 R m d).
Proof. exact (TRANS (@lem288796 R m d) (@lem288799 R m d)). Qed.
Lemma lem288801 (R : type1605) (m : nat) (d : nat) : (term141 R m d) = (term113 R m d).
Proof. exact (TRANS (@lem288786 R m d) (@lem288800 R m d)). Qed.
Lemma lem288802 (R : type1605) (m : nat) : (term143 R m) = (term162 R m).
Proof. exact (fun_ext (fun d : nat => @lem288801 R m d)). Qed.
Lemma lem288803 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem288804 (R : type1605) (m : nat) : (term144 R m) = (term163 R m).
Proof. exact (MK_COMB (@lem288803) (@lem288802 R m)). Qed.
Lemma lem288809 (R : type1605) (m : nat) : (term163 R m) = (term144 R m).
Proof. exact (SYM (@lem288804 R m)). Qed.
Lemma lem288811 (P : nat -> Prop) : term164 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem288812 (R : type1605) (m : nat) : term165 R m.
Proof. exact (@lem288811 (term162 R m)). Qed.
Lemma lem288813 (R : type1605) (m : nat) : (term166 R m) = (term167 R m).
Proof. exact (eq_refl (term166 R m)). Qed.
Lemma lem288814 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem288815 (R : type1605) (m : nat) : (term168 R m) = (term169 R m).
Proof. exact (MK_COMB (@lem288814) (@lem288813 R m)). Qed.
Lemma lem288816 (R : type1605) (m : nat) (d : nat) : (term170 R m d) = (term113 R m d).
Proof. exact (eq_refl (term170 R m d)). Qed.
Lemma lem288817 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem288818 (R : type1605) (m : nat) (d : nat) : (term171 R m d) = (term172 R m d).
Proof. exact (MK_COMB (@lem288817) (@lem288816 R m d)). Qed.
Lemma lem288819 (R : type1605) (m : nat) (d : nat) : (term173 R m d) = (term174 R m d).
Proof. exact (eq_refl (term173 R m d)). Qed.
Lemma lem288820 (R : type1605) (m : nat) (d : nat) : (term175 R m d) = (term176 R m d).
Proof. exact (MK_COMB (@lem288818 R m d) (@lem288819 R m d)). Qed.
Lemma lem288821 (R : type1605) (m : nat) : (term177 R m) = (term178 R m).
Proof. exact (fun_ext (fun d : nat => @lem288820 R m d)). Qed.
Lemma lem288822 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem288823 (R : type1605) (m : nat) : (term179 R m) = (term180 R m).
Proof. exact (MK_COMB (@lem288822) (@lem288821 R m)). Qed.
Lemma lem288824 (R : type1605) (m : nat) : (term181 R m) = (term182 R m).
Proof. exact (MK_COMB (@lem288815 R m) (@lem288823 R m)). Qed.
Lemma lem288825 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem288826 (R : type1605) (m : nat) : (term183 R m) = (term184 R m).
Proof. exact (MK_COMB (@lem288825) (@lem288824 R m)). Qed.
Lemma lem288827 (R : type1605) (m : nat) (d : nat) : (term170 R m d) = (term113 R m d).
Proof. exact (eq_refl (term170 R m d)). Qed.
Lemma lem288828 (R : type1605) (m : nat) : (term185 R m) = (term162 R m).
Proof. exact (fun_ext (fun d : nat => @lem288827 R m d)). Qed.
Lemma lem288829 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem288830 (R : type1605) (m : nat) : (term186 R m) = (term163 R m).
Proof. exact (MK_COMB (@lem288829) (@lem288828 R m)). Qed.
Lemma lem288831 (R : type1605) (m : nat) : (term165 R m) = (term187 R m).
Proof. exact (MK_COMB (@lem288826 R m) (@lem288830 R m)). Qed.
Lemma lem288832 (R : type1605) (m : nat) : term187 R m.
Proof. exact (EQ_MP (@lem288831 R m) (@lem288812 R m)). Qed.
Lemma lem288833 (R : type1605) (m : nat) (d : nat) (h1 : term113 R m d) : term113 R m d.
Proof. exact (h1). Qed.
Lemma lem288835 (m : nat) : (term17 m) = m.
Proof. exact (EQ_MP (@lem286734 m) (@lem286733 m)). Qed.
Lemma lem288836 (R : type1605) (m : nat) : (R m) = (R m).
Proof. exact (eq_refl (R m)). Qed.
Lemma lem288837 (R : type1605) (m : nat) : (term167 R m) = (R m m).
Proof. exact (MK_COMB (@lem288836 R m) (@lem288835 m)). Qed.
Lemma lem288838 (R : type1605) (m : nat) : (R m m) = (term167 R m).
Proof. exact (SYM (@lem288837 R m)). Qed.
Lemma lem288840 (m : nat) (n : nat) : (term13 m n) = (term14 m n).
Proof. exact (EQ_MP (@lem286723 m n) (@lem286722 m n)). Qed.
Lemma lem288841 (m : nat) (d : nat) : (term13 m d) = (term14 m d).
Proof. exact (@lem288840 m d). Qed.
Lemma lem288842 (R : type1605) (m : nat) : (R m) = (R m).
Proof. exact (eq_refl (R m)). Qed.
Lemma lem288843 (R : type1605) (m : nat) (d : nat) : (term174 R m d) = (term188 R m d).
Proof. exact (MK_COMB (@lem288842 R m) (@lem288841 m d)). Qed.
Lemma lem288844 (R : type1605) (m : nat) (d : nat) : (term188 R m d) = (term174 R m d).
Proof. exact (SYM (@lem288843 R m d)). Qed.
Lemma lem288846 (p : Prop) : p = (term189 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem288847 (R : type1605) (m : nat) : (R m m) = (term190 R m).
Proof. exact (@lem288846 (R m m)). Qed.
Lemma lem288848 (R : type1605) (m : nat) : (term190 R m) = (R m m).
Proof. exact (SYM (@lem288847 R m)). Qed.
Lemma lem288849 (R : type1605) (m : nat) (h1 : term191 R m) : term191 R m.
Proof. exact (h1). Qed.
Lemma lem288852 (R : type1605) (m : nat) (h1 : term192 R m) : term192 R m.
Proof. exact (h1). Qed.
Lemma lem288853 (R : type1605) (m : nat) : term193 R m.
Proof. exact (fun h0 : term192 R m => @lem288852 R m h0). Qed.
Lemma lem288854 (R : type1605) (m : nat) (h1 : term193 R m) : term193 R m.
Proof. exact (h1). Qed.
Lemma lem288855 (R : type1605) (m : nat) (h1 : term192 R m) : term192 R m.
Proof. exact (h1). Qed.
Lemma lem288856 (R : type1605) (m : nat) (h1 : term192 R m) (h2 : term193 R m) : term192 R m.
Proof. exact (@lem288854 R m h2 (@lem288855 R m h1)). Qed.
Lemma lem288857 (R : type1605) (m : nat) (h1 : term192 R m) : term194 R m.
Proof. exact (fun h0 : term193 R m => @lem288856 R m h1 h0). Qed.
Lemma lem288858 (R : type1605) (m : nat) (h1 : term193 R m) : term193 R m.
Proof. exact (h1). Qed.
Lemma lem288859 (R : type1605) (m : nat) (h1 : term192 R m) (h2 : term193 R m) : term192 R m.
Proof. exact (@lem288857 R m h1 (@lem288858 R m h2)). Qed.
Lemma lem288860 (R : type1605) (m : nat) (h1 : term193 R m) : term193 R m.
Proof. exact (fun h0 : term192 R m => @lem288859 R m h0 h1). Qed.
Lemma lem288861 (R : type1605) (m : nat) : term195 R m.
Proof. exact (fun h0 : term193 R m => @lem288860 R m h0). Qed.
Lemma lem288864 (R : type1605) (m : nat) : term193 R m.
Proof. exact (@lem288861 R m (@lem288853 R m)). Qed.
Lemma lem288904 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem288905 (R : type1605) (m : nat) : (term190 R m) = (term196 R m).
Proof. exact (@lem288904 (term191 R m)). Qed.
Lemma lem288907 (t : Prop) : (term197 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem288908 (R : type1605) (m : nat) : (term196 R m) = (R m m).
Proof. exact (@lem288907 (R m m)). Qed.
Lemma lem288909 (R : type1605) (m : nat) : (term190 R m) = (R m m).
Proof. exact (TRANS (@lem288905 R m) (@lem288908 R m)). Qed.
Lemma lem288910 (R : type1605) : (term198 R) = (term198 R).
Proof. exact (eq_refl (term198 R)). Qed.
Lemma lem288911 (R : type1605) (m : nat) : (term199 R m) = (term200 R m).
Proof. exact (MK_COMB (@lem288910 R) (@lem288909 R m)). Qed.
Lemma lem288914 (R : type1605) : (term201 R) = (term201 R).
Proof. exact (eq_refl (term201 R)). Qed.
Lemma lem288915 (R : type1605) (m : nat) : (term202 R m) = (term203 R m).
Proof. exact (MK_COMB (@lem288914 R) (@lem288911 R m)). Qed.
Lemma lem288918 (R : type1605) : (term204 R) = (term204 R).
Proof. exact (eq_refl (term204 R)). Qed.
Lemma lem288919 (R : type1605) (m : nat) : (term192 R m) = (term205 R m).
Proof. exact (MK_COMB (@lem288918 R) (@lem288915 R m)). Qed.
Lemma lem288922 (m : nat) : (term206 m) = (term207 m).
Proof. exact (fun_ext (fun R : type1605 => @lem288919 R m)). Qed.
Lemma lem288923 : (@all (nat -> nat -> Prop)) = (@all (nat -> nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> nat -> Prop))). Qed.
Lemma lem288924 (m : nat) : (term208 m) = (term209 m).
Proof. exact (MK_COMB (@lem288923) (@lem288922 m)). Qed.
Lemma lem288929 : term210 = term211.
Proof. exact (fun_ext (fun m : nat => @lem288924 m)). Qed.
Lemma lem288930 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem288939 : term212 = term213.
Proof. exact (MK_COMB (@lem288930) (@lem288929)). Qed.
Lemma lem288940 (R : type1605) (m : nat) : (R m m) = (R m m).
Proof. exact (eq_refl (R m m)). Qed.
Lemma lem288941 (R : type1605) (n : nat) : (term67 R n) = (term67 R n).
Proof. exact (eq_refl (term67 R n)). Qed.
Lemma lem288942 (R : type1605) : (term68 R) = (term68 R).
Proof. exact (fun_ext (fun n : nat => @lem288941 R n)). Qed.
Lemma lem288943 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem288944 (R : type1605) : (term50 R) = (term50 R).
Proof. exact (MK_COMB (@lem288943) (@lem288942 R)). Qed.
Lemma lem288945 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem288946 (R : type1605) : (term198 R) = (term198 R).
Proof. exact (MK_COMB (@lem288945) (@lem288944 R)). Qed.
Lemma lem288947 (R : type1605) (m : nat) : (term200 R m) = (term200 R m).
Proof. exact (MK_COMB (@lem288946 R) (@lem288940 R m)). Qed.
Lemma lem288956 (y : nat) (R : type1605) (x : nat) (z : nat) : (term214 y R x z) = (term214 y R x z).
Proof. exact (eq_refl (term214 y R x z)). Qed.
Lemma lem288957 (y : nat) (R : type1605) (x : nat) : (term215 y R x) = (term215 y R x).
Proof. exact (fun_ext (fun z : nat => @lem288956 y R x z)). Qed.
Lemma lem288958 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem288959 (y : nat) (R : type1605) (x : nat) : (term216 y R x) = (term216 y R x).
Proof. exact (MK_COMB (@lem288958) (@lem288957 y R x)). Qed.
Lemma lem288960 (R : type1605) (x : nat) : (term217 R x) = (term217 R x).
Proof. exact (fun_ext (fun y : nat => @lem288959 y R x)). Qed.
Lemma lem288961 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem288962 (R : type1605) (x : nat) : (term218 R x) = (term218 R x).
Proof. exact (MK_COMB (@lem288961) (@lem288960 R x)). Qed.
Lemma lem288963 (R : type1605) : (term219 R) = (term219 R).
Proof. exact (fun_ext (fun x : nat => @lem288962 R x)). Qed.
Lemma lem288964 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem288965 (R : type1605) : (term36 R) = (term36 R).
Proof. exact (MK_COMB (@lem288964) (@lem288963 R)). Qed.
Lemma lem288966 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem288967 (R : type1605) : (term201 R) = (term201 R).
Proof. exact (MK_COMB (@lem288966) (@lem288965 R)). Qed.
Lemma lem288968 (R : type1605) (m : nat) : (term203 R m) = (term203 R m).
Proof. exact (MK_COMB (@lem288967 R) (@lem288947 R m)). Qed.
Lemma lem288969 (R : type1605) (x : nat) : (R x x) = (R x x).
Proof. exact (eq_refl (R x x)). Qed.
Lemma lem288970 (R : type1605) : (term220 R) = (term220 R).
Proof. exact (fun_ext (fun x : nat => @lem288969 R x)). Qed.
Lemma lem288971 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem288972 (R : type1605) : (term37 R) = (term37 R).
Proof. exact (MK_COMB (@lem288971) (@lem288970 R)). Qed.
Lemma lem288973 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem288974 (R : type1605) : (term204 R) = (term204 R).
Proof. exact (MK_COMB (@lem288973) (@lem288972 R)). Qed.
Lemma lem288975 (R : type1605) (m : nat) : (term205 R m) = (term205 R m).
Proof. exact (MK_COMB (@lem288974 R) (@lem288968 R m)). Qed.
Lemma lem288976 (m : nat) : (term207 m) = (term207 m).
Proof. exact (fun_ext (fun R : type1605 => @lem288975 R m)). Qed.
Lemma lem288977 : (@all (nat -> nat -> Prop)) = (@all (nat -> nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> nat -> Prop))). Qed.
Lemma lem288978 (m : nat) : (term209 m) = (term209 m).
Proof. exact (MK_COMB (@lem288977) (@lem288976 m)). Qed.
Lemma lem288979 : term211 = term211.
Proof. exact (fun_ext (fun m : nat => @lem288978 m)). Qed.
Lemma lem288980 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem288981 : term213 = term213.
Proof. exact (MK_COMB (@lem288980) (@lem288979)). Qed.
Lemma lem289036 : term212 = term213.
Proof. exact (TRANS (@lem288939) (@lem288981)). Qed.
Lemma lem289037 : term213 = term212.
Proof. exact (SYM (@lem289036)). Qed.
Lemma lem289038 (R : type1605) (h1 : term37 R) : term37 R.
Proof. exact (h1). Qed.
Lemma lem289042 (p : Prop) : p = (term189 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem289043 (R : type1605) (m : nat) : (R m m) = (term190 R m).
Proof. exact (@lem289042 (R m m)). Qed.
Lemma lem289044 (R : type1605) (m : nat) : (term190 R m) = (R m m).
Proof. exact (SYM (@lem289043 R m)). Qed.
Lemma lem289045 (R : type1605) (m : nat) (h1 : term191 R m) : term191 R m.
Proof. exact (h1). Qed.
Lemma lem289046 (R : type1605) (x : nat) : (R x x) = (R x x).
Proof. exact (eq_refl (R x x)). Qed.
Lemma lem289047 (R : type1605) : (term220 R) = (term220 R).
Proof. exact (fun_ext (fun x : nat => @lem289046 R x)). Qed.
Lemma lem289048 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem289057 (R : type1605) : (term37 R) = (term37 R).
Proof. exact (MK_COMB (@lem289048) (@lem289047 R)). Qed.
Lemma lem289058 (R : type1605) (h1 : term37 R) : term37 R.
Proof. exact (EQ_MP (@lem289057 R) (@lem289038 R h1)). Qed.
Lemma lem289160 (R : type1605) (m : nat) (h1 : term191 R m) : term191 R m.
Proof. exact (h1). Qed.
Lemma lem289165 (R : type1605) (x : nat) : (R x x) = (R x x).
Proof. exact (eq_refl (R x x)). Qed.
Lemma lem289166 (R : type1605) : (term220 R) = (term220 R).
Proof. exact (fun_ext (fun x : nat => @lem289165 R x)). Qed.
Lemma lem289167 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem289168 (R : type1605) : (term37 R) = (term37 R).
Proof. exact (MK_COMB (@lem289167) (@lem289166 R)). Qed.
Lemma lem289169 (R : type1605) (h1 : term37 R) : term37 R.
Proof. exact (EQ_MP (@lem289168 R) (@lem289058 R h1)). Qed.
Lemma lem289223 (R : type1605) (m : nat) (h1 : term191 R m) : term191 R m.
Proof. exact (h1). Qed.
Lemma lem289225 (R : type1605) (x : nat) : (R x x) = (R x x).
Proof. exact (eq_refl (R x x)). Qed.
Lemma lem289226 (R : type1605) : (term220 R) = (term220 R).
Proof. exact (fun_ext (fun x : nat => @lem289225 R x)). Qed.
Lemma lem289227 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem289229 (R : type1605) : (term37 R) = (term37 R).
Proof. exact (MK_COMB (@lem289227) (@lem289226 R)). Qed.
Lemma lem289230 (R : type1605) (h1 : term37 R) : term37 R.
Proof. exact (EQ_MP (@lem289229 R) (@lem289169 R h1)). Qed.
Lemma lem289266 (R : type1605) (m : nat) (h1 : term191 R m) : term191 R m.
Proof. exact (h1). Qed.
Lemma lem289267 (_6485 : nat) (R : type1605) (h1 : term37 R) : term221 R _6485.
Proof. exact (@lem289230 R h1 _6485). Qed.
Lemma lem289268 (R : type1605) (_6485 : nat) : (term221 R _6485) = (R _6485 _6485).
Proof. exact (eq_refl (term221 R _6485)). Qed.
Lemma lem289299 (R : type1605) (m : nat) (h1 : term191 R m) : term191 R m.
Proof. exact (h1). Qed.
Lemma lem289301 (_6485 : nat) (R : type1605) (h1 : term37 R) : R _6485 _6485.
Proof. exact (EQ_MP (@lem289268 R _6485) (@lem289267 _6485 R h1)). Qed.
Lemma lem289302 (m : nat) (R : type1605) (h1 : term37 R) : R m m.
Proof. exact (@lem289301 m R h1). Qed.
Lemma lem289303 (m : nat) (R : type1605) (h1 : term37 R) : term222 R m.
Proof. exact (fun h0 : term191 R m => @lem289302 m R h1). Qed.
Lemma lem289305 (p : Prop) : (term223 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem289306 (R : type1605) (m : nat) : (term222 R m) = (R m m).
Proof. exact (@lem289305 (R m m)). Qed.
Lemma lem289307 (m : nat) (R : type1605) (h1 : term37 R) : R m m.
Proof. exact (EQ_MP (@lem289306 R m) (@lem289303 m R h1)). Qed.
Lemma lem289310 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem289312 (R : type1605) (m : nat) : (term191 R m) = (term224 R m).
Proof. exact (@lem289310 (R m m)). Qed.
Lemma lem289315 (R : type1605) (m : nat) (h1 : term191 R m) : term224 R m.
Proof. exact (EQ_MP (@lem289312 R m) (@lem289299 R m h1)). Qed.
Lemma lem289318 (R : type1605) (m : nat) (h1 : term37 R) (h2 : term191 R m) : False.
Proof. exact (@lem289315 R m h2 (@lem289307 m R h1)). Qed.
Lemma lem289319 (R : type1605) (m : nat) (h1 : term37 R) (h2 : term191 R m) : term225.
Proof. exact (fun h0 : ~ False => @lem289318 R m h1 h2). Qed.
Lemma lem289321 (p : Prop) : (term223 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem289322 : term225 = False.
Proof. exact (@lem289321 False). Qed.
Lemma lem289323 (R : type1605) (m : nat) (h1 : term37 R) (h2 : term191 R m) : False.
Proof. exact (EQ_MP (@lem289322) (@lem289319 R m h1 h2)). Qed.
Lemma lem289324 (R : type1605) (m : nat) (h1 : term37 R) (h2 : term191 R m) : (term191 R m) = False.
Proof. exact (prop_ext (fun h3 : term191 R m => @lem289323 R m h1 h2) (fun h3 : False => @lem289299 R m h2)). Qed.
Lemma lem289325 (R : type1605) (m : nat) (h1 : term37 R) (h2 : term191 R m) : False.
Proof. exact (EQ_MP (@lem289324 R m h1 h2) (@lem289299 R m h2)). Qed.
Lemma lem289326 (R : type1605) (m : nat) (h1 : term37 R) (h2 : term191 R m) : (term191 R m) = False.
Proof. exact (prop_ext (fun h3 : term191 R m => @lem289325 R m h1 h2) (fun h3 : False => @lem289266 R m h2)). Qed.
Lemma lem289327 (R : type1605) (m : nat) (h1 : term37 R) (h2 : term191 R m) : False.
Proof. exact (EQ_MP (@lem289326 R m h1 h2) (@lem289266 R m h2)). Qed.
Lemma lem289328 (R : type1605) (m : nat) (h1 : term37 R) (h2 : term191 R m) : (term191 R m) = False.
Proof. exact (prop_ext (fun h3 : term191 R m => @lem289327 R m h1 h2) (fun h3 : False => @lem289266 R m h2)). Qed.
Lemma lem289329 (R : type1605) (m : nat) (h1 : term37 R) (h2 : term191 R m) : False.
Proof. exact (EQ_MP (@lem289328 R m h1 h2) (@lem289266 R m h2)). Qed.
Lemma lem289330 (R : type1605) (m : nat) (h1 : term37 R) (h2 : term191 R m) : (term37 R) = False.
Proof. exact (prop_ext (fun h3 : term37 R => @lem289329 R m h1 h2) (fun h3 : False => @lem289230 R h1)). Qed.
Lemma lem289331 (R : type1605) (m : nat) (h1 : term37 R) (h2 : term191 R m) : False.
Proof. exact (EQ_MP (@lem289330 R m h1 h2) (@lem289230 R h1)). Qed.
Lemma lem289332 (R : type1605) (m : nat) (h1 : term37 R) (h2 : term191 R m) : (term191 R m) = False.
Proof. exact (prop_ext (fun h3 : term191 R m => @lem289331 R m h1 h2) (fun h3 : False => @lem289223 R m h2)). Qed.
Lemma lem289333 (R : type1605) (m : nat) (h1 : term37 R) (h2 : term191 R m) : False.
Proof. exact (EQ_MP (@lem289332 R m h1 h2) (@lem289223 R m h2)). Qed.
Lemma lem289334 (R : type1605) (m : nat) (h1 : term37 R) (h2 : term191 R m) : (term37 R) = False.
Proof. exact (prop_ext (fun h3 : term37 R => @lem289333 R m h1 h2) (fun h3 : False => @lem289169 R h1)). Qed.
Lemma lem289335 (R : type1605) (m : nat) (h1 : term37 R) (h2 : term191 R m) : False.
Proof. exact (EQ_MP (@lem289334 R m h1 h2) (@lem289169 R h1)). Qed.
Lemma lem289336 (R : type1605) (m : nat) (h1 : term37 R) (h2 : term191 R m) : (term191 R m) = False.
Proof. exact (prop_ext (fun h3 : term191 R m => @lem289335 R m h1 h2) (fun h3 : False => @lem289160 R m h2)). Qed.
Lemma lem289337 (R : type1605) (m : nat) (h1 : term37 R) (h2 : term191 R m) : False.
Proof. exact (EQ_MP (@lem289336 R m h1 h2) (@lem289160 R m h2)). Qed.
Lemma lem289338 (R : type1605) (m : nat) (h1 : term37 R) (h2 : term191 R m) : (term37 R) = False.
Proof. exact (prop_ext (fun h3 : term37 R => @lem289337 R m h1 h2) (fun h3 : False => @lem289058 R h1)). Qed.
Lemma lem289339 (R : type1605) (m : nat) (h1 : term37 R) (h2 : term191 R m) : False.
Proof. exact (EQ_MP (@lem289338 R m h1 h2) (@lem289058 R h1)). Qed.
Lemma lem289340 (R : type1605) (m : nat) (h1 : term37 R) (h2 : term191 R m) : (term191 R m) = False.
Proof. exact (prop_ext (fun h3 : term191 R m => @lem289339 R m h1 h2) (fun h3 : False => @lem289045 R m h2)). Qed.
Lemma lem289341 (R : type1605) (m : nat) (h1 : term37 R) (h2 : term191 R m) : False.
Proof. exact (EQ_MP (@lem289340 R m h1 h2) (@lem289045 R m h2)). Qed.
Lemma lem289342 (m : nat) (R : type1605) (h1 : term37 R) : term190 R m.
Proof. exact (fun h0 : term191 R m => @lem289341 R m h1 h0). Qed.
Lemma lem289343 (m : nat) (R : type1605) (h1 : term37 R) : R m m.
Proof. exact (EQ_MP (@lem289044 R m) (@lem289342 m R h1)). Qed.
Lemma lem289344 (m : nat) (R : type1605) (h1 : term37 R) : term200 R m.
Proof. exact (fun h0 : term50 R => @lem289343 m R h1). Qed.
Lemma lem289345 (m : nat) (R : type1605) (h1 : term37 R) : term203 R m.
Proof. exact (fun h0 : term36 R => @lem289344 m R h1). Qed.
Lemma lem289346 (R : type1605) (m : nat) : term205 R m.
Proof. exact (fun h0 : term37 R => @lem289345 m R h0). Qed.
Lemma lem289351 (m : nat) : term209 m.
Proof. exact (fun R : type1605 => @lem289346 R m). Qed.
Lemma lem289356 : term213.
Proof. exact (fun m : nat => @lem289351 m). Qed.
Lemma lem289357 : term212.
Proof. exact (EQ_MP (@lem289037) (@lem289356)). Qed.
Lemma lem289358 (m : nat) : term226 m.
Proof. exact (@lem289357 m). Qed.
Lemma lem289359 (m : nat) : (term226 m) = (term208 m).
Proof. exact (eq_refl (term226 m)). Qed.
Lemma lem289360 (m : nat) : term208 m.
Proof. exact (EQ_MP (@lem289359 m) (@lem289358 m)). Qed.
Lemma lem289361 (m : nat) (R : type1605) : term227 m R.
Proof. exact (@lem289360 m R). Qed.
Lemma lem289362 (R : type1605) (m : nat) : (term227 m R) = (term192 R m).
Proof. exact (eq_refl (term227 m R)). Qed.
Lemma lem289363 (R : type1605) (m : nat) : term192 R m.
Proof. exact (EQ_MP (@lem289362 R m) (@lem289361 m R)). Qed.
Lemma lem289365 (R : type1605) (m : nat) : term192 R m.
Proof. exact (@lem288864 R m (@lem289363 R m)). Qed.
Lemma lem289366 (m : nat) (R : type1605) (h1 : term37 R) : term202 R m.
Proof. exact (@lem289365 R m (@lem286792 R h1)). Qed.
Lemma lem289367 (m : nat) (R : type1605) (h1 : term36 R) (h2 : term37 R) : term199 R m.
Proof. exact (@lem289366 m R h2 (@lem286791 R h1)). Qed.
Lemma lem289368 (m : nat) (R : type1605) (h1 : term36 R) (h2 : term37 R) (h3 : term50 R) : term190 R m.
Proof. exact (@lem289367 m R h1 h2 (@lem288396 R h3)). Qed.
Lemma lem289369 (R : type1605) (m : nat) (h1 : term36 R) (h2 : term37 R) (h3 : term50 R) (h4 : term191 R m) : False.
Proof. exact (@lem289368 m R h1 h2 h3 (@lem288849 R m h4)). Qed.
Lemma lem289370 (R : type1605) (m : nat) (h1 : term36 R) (h2 : term37 R) (h3 : term50 R) (h4 : term191 R m) : (term191 R m) = False.
Proof. exact (prop_ext (fun h5 : term191 R m => @lem289369 R m h1 h2 h3 h4) (fun h5 : False => @lem288849 R m h4)). Qed.
Lemma lem289371 (R : type1605) (m : nat) (h1 : term36 R) (h2 : term37 R) (h3 : term50 R) (h4 : term191 R m) : False.
Proof. exact (EQ_MP (@lem289370 R m h1 h2 h3 h4) (@lem288849 R m h4)). Qed.
Lemma lem289372 (m : nat) (R : type1605) (h1 : term36 R) (h2 : term37 R) (h3 : term50 R) : term190 R m.
Proof. exact (fun h0 : term191 R m => @lem289371 R m h1 h2 h3 h0). Qed.
Lemma lem289373 (m : nat) (R : type1605) (h1 : term36 R) (h2 : term37 R) (h3 : term50 R) : R m m.
Proof. exact (EQ_MP (@lem288848 R m) (@lem289372 m R h1 h2 h3)). Qed.
Lemma lem289375 (p : Prop) : p = (term189 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem289376 (R : type1605) (m : nat) (d : nat) : (term188 R m d) = (term228 R m d).
Proof. exact (@lem289375 (term188 R m d)). Qed.
Lemma lem289377 (R : type1605) (m : nat) (d : nat) : (term228 R m d) = (term188 R m d).
Proof. exact (SYM (@lem289376 R m d)). Qed.
Lemma lem289378 (R : type1605) (m : nat) (d : nat) (h1 : term229 R m d) : term229 R m d.
Proof. exact (h1). Qed.
Lemma lem289381 (R : type1605) (m : nat) (d : nat) (h1 : term230 R m d) : term230 R m d.
Proof. exact (h1). Qed.
Lemma lem289382 (R : type1605) (m : nat) (d : nat) : term231 R m d.
Proof. exact (fun h0 : term230 R m d => @lem289381 R m d h0). Qed.
Lemma lem289383 (R : type1605) (m : nat) (d : nat) (h1 : term231 R m d) : term231 R m d.
Proof. exact (h1). Qed.
Lemma lem289384 (R : type1605) (m : nat) (d : nat) (h1 : term230 R m d) : term230 R m d.
Proof. exact (h1). Qed.
Lemma lem289385 (R : type1605) (m : nat) (d : nat) (h1 : term230 R m d) (h2 : term231 R m d) : term230 R m d.
Proof. exact (@lem289383 R m d h2 (@lem289384 R m d h1)). Qed.
Lemma lem289386 (R : type1605) (m : nat) (d : nat) (h1 : term230 R m d) : term232 R m d.
Proof. exact (fun h0 : term231 R m d => @lem289385 R m d h1 h0). Qed.
Lemma lem289387 (R : type1605) (m : nat) (d : nat) (h1 : term231 R m d) : term231 R m d.
Proof. exact (h1). Qed.
Lemma lem289388 (R : type1605) (m : nat) (d : nat) (h1 : term230 R m d) (h2 : term231 R m d) : term230 R m d.
Proof. exact (@lem289386 R m d h1 (@lem289387 R m d h2)). Qed.
Lemma lem289389 (R : type1605) (m : nat) (d : nat) (h1 : term231 R m d) : term231 R m d.
Proof. exact (fun h0 : term230 R m d => @lem289388 R m d h0 h1). Qed.
Lemma lem289390 (R : type1605) (m : nat) (d : nat) : term233 R m d.
Proof. exact (fun h0 : term231 R m d => @lem289389 R m d h0). Qed.
Lemma lem289393 (R : type1605) (m : nat) (d : nat) : term231 R m d.
Proof. exact (@lem289390 R m d (@lem289382 R m d)). Qed.
Lemma lem289439 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem289440 (R : type1605) (m : nat) (d : nat) : (term228 R m d) = (term234 R m d).
Proof. exact (@lem289439 (term229 R m d)). Qed.
Lemma lem289442 (t : Prop) : (term197 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem289443 (R : type1605) (m : nat) (d : nat) : (term234 R m d) = (term188 R m d).
Proof. exact (@lem289442 (term188 R m d)). Qed.
Lemma lem289444 (R : type1605) (m : nat) (d : nat) : (term228 R m d) = (term188 R m d).
Proof. exact (TRANS (@lem289440 R m d) (@lem289443 R m d)). Qed.
Lemma lem289445 (R : type1605) (m : nat) (d : nat) : (term172 R m d) = (term172 R m d).
Proof. exact (eq_refl (term172 R m d)). Qed.
Lemma lem289446 (R : type1605) (m : nat) (d : nat) : (term235 R m d) = (term236 R m d).
Proof. exact (MK_COMB (@lem289445 R m d) (@lem289444 R m d)). Qed.
Lemma lem289449 (R : type1605) : (term198 R) = (term198 R).
Proof. exact (eq_refl (term198 R)). Qed.
Lemma lem289450 (R : type1605) (m : nat) (d : nat) : (term237 R m d) = (term238 R m d).
Proof. exact (MK_COMB (@lem289449 R) (@lem289446 R m d)). Qed.
Lemma lem289453 (R : type1605) : (term201 R) = (term201 R).
Proof. exact (eq_refl (term201 R)). Qed.
Lemma lem289454 (R : type1605) (m : nat) (d : nat) : (term239 R m d) = (term240 R m d).
Proof. exact (MK_COMB (@lem289453 R) (@lem289450 R m d)). Qed.
Lemma lem289457 (R : type1605) : (term204 R) = (term204 R).
Proof. exact (eq_refl (term204 R)). Qed.
Lemma lem289458 (R : type1605) (m : nat) (d : nat) : (term230 R m d) = (term241 R m d).
Proof. exact (MK_COMB (@lem289457 R) (@lem289454 R m d)). Qed.
Lemma lem289461 (m : nat) (d : nat) : (term242 m d) = (term243 m d).
Proof. exact (fun_ext (fun R : type1605 => @lem289458 R m d)). Qed.
Lemma lem289462 : (@all (nat -> nat -> Prop)) = (@all (nat -> nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> nat -> Prop))). Qed.
Lemma lem289463 (m : nat) (d : nat) : (term244 m d) = (term245 m d).
Proof. exact (MK_COMB (@lem289462) (@lem289461 m d)). Qed.
Lemma lem289468 (d : nat) : (term246 d) = (term247 d).
Proof. exact (fun_ext (fun m : nat => @lem289463 m d)). Qed.
Lemma lem289469 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem289470 (d : nat) : (term248 d) = (term249 d).
Proof. exact (MK_COMB (@lem289469) (@lem289468 d)). Qed.
Lemma lem289475 : term250 = term251.
Proof. exact (fun_ext (fun d : nat => @lem289470 d)). Qed.
Lemma lem289476 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem289485 : term252 = term253.
Proof. exact (MK_COMB (@lem289476) (@lem289475)). Qed.
Lemma lem289490 (R : type1605) (m : nat) (d : nat) : (term236 R m d) = (term236 R m d).
Proof. exact (eq_refl (term236 R m d)). Qed.
Lemma lem289491 (R : type1605) (n : nat) : (term67 R n) = (term67 R n).
Proof. exact (eq_refl (term67 R n)). Qed.
Lemma lem289492 (R : type1605) : (term68 R) = (term68 R).
Proof. exact (fun_ext (fun n : nat => @lem289491 R n)). Qed.
Lemma lem289493 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem289494 (R : type1605) : (term50 R) = (term50 R).
Proof. exact (MK_COMB (@lem289493) (@lem289492 R)). Qed.
Lemma lem289495 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem289496 (R : type1605) : (term198 R) = (term198 R).
Proof. exact (MK_COMB (@lem289495) (@lem289494 R)). Qed.
Lemma lem289497 (R : type1605) (m : nat) (d : nat) : (term238 R m d) = (term238 R m d).
Proof. exact (MK_COMB (@lem289496 R) (@lem289490 R m d)). Qed.
Lemma lem289506 (y : nat) (R : type1605) (x : nat) (z : nat) : (term214 y R x z) = (term214 y R x z).
Proof. exact (eq_refl (term214 y R x z)). Qed.
Lemma lem289507 (y : nat) (R : type1605) (x : nat) : (term215 y R x) = (term215 y R x).
Proof. exact (fun_ext (fun z : nat => @lem289506 y R x z)). Qed.
Lemma lem289508 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem289509 (y : nat) (R : type1605) (x : nat) : (term216 y R x) = (term216 y R x).
Proof. exact (MK_COMB (@lem289508) (@lem289507 y R x)). Qed.
Lemma lem289510 (R : type1605) (x : nat) : (term217 R x) = (term217 R x).
Proof. exact (fun_ext (fun y : nat => @lem289509 y R x)). Qed.
Lemma lem289511 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem289512 (R : type1605) (x : nat) : (term218 R x) = (term218 R x).
Proof. exact (MK_COMB (@lem289511) (@lem289510 R x)). Qed.
Lemma lem289513 (R : type1605) : (term219 R) = (term219 R).
Proof. exact (fun_ext (fun x : nat => @lem289512 R x)). Qed.
Lemma lem289514 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem289515 (R : type1605) : (term36 R) = (term36 R).
Proof. exact (MK_COMB (@lem289514) (@lem289513 R)). Qed.
Lemma lem289516 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem289517 (R : type1605) : (term201 R) = (term201 R).
Proof. exact (MK_COMB (@lem289516) (@lem289515 R)). Qed.
Lemma lem289518 (R : type1605) (m : nat) (d : nat) : (term240 R m d) = (term240 R m d).
Proof. exact (MK_COMB (@lem289517 R) (@lem289497 R m d)). Qed.
Lemma lem289519 (R : type1605) (x : nat) : (R x x) = (R x x).
Proof. exact (eq_refl (R x x)). Qed.
Lemma lem289520 (R : type1605) : (term220 R) = (term220 R).
Proof. exact (fun_ext (fun x : nat => @lem289519 R x)). Qed.
Lemma lem289521 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem289522 (R : type1605) : (term37 R) = (term37 R).
Proof. exact (MK_COMB (@lem289521) (@lem289520 R)). Qed.
Lemma lem289523 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem289524 (R : type1605) : (term204 R) = (term204 R).
Proof. exact (MK_COMB (@lem289523) (@lem289522 R)). Qed.
Lemma lem289525 (R : type1605) (m : nat) (d : nat) : (term241 R m d) = (term241 R m d).
Proof. exact (MK_COMB (@lem289524 R) (@lem289518 R m d)). Qed.
Lemma lem289526 (m : nat) (d : nat) : (term243 m d) = (term243 m d).
Proof. exact (fun_ext (fun R : type1605 => @lem289525 R m d)). Qed.
Lemma lem289527 : (@all (nat -> nat -> Prop)) = (@all (nat -> nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> nat -> Prop))). Qed.
Lemma lem289528 (m : nat) (d : nat) : (term245 m d) = (term245 m d).
Proof. exact (MK_COMB (@lem289527) (@lem289526 m d)). Qed.
Lemma lem289529 (d : nat) : (term247 d) = (term247 d).
Proof. exact (fun_ext (fun m : nat => @lem289528 m d)). Qed.
Lemma lem289530 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem289531 (d : nat) : (term249 d) = (term249 d).
Proof. exact (MK_COMB (@lem289530) (@lem289529 d)). Qed.
Lemma lem289532 : term251 = term251.
Proof. exact (fun_ext (fun d : nat => @lem289531 d)). Qed.
Lemma lem289533 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem289534 : term253 = term253.
Proof. exact (MK_COMB (@lem289533) (@lem289532)). Qed.
Lemma lem289597 : term252 = term253.
Proof. exact (TRANS (@lem289485) (@lem289534)). Qed.
Lemma lem289598 : term253 = term252.
Proof. exact (SYM (@lem289597)). Qed.
Lemma lem289600 (R : type1605) (h1 : term36 R) : term36 R.
Proof. exact (h1). Qed.
Lemma lem289601 (R : type1605) (h1 : term50 R) : term50 R.
Proof. exact (h1). Qed.
Lemma lem289604 (p : Prop) : p = (term189 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem289605 (R : type1605) (m : nat) (d : nat) : (term188 R m d) = (term228 R m d).
Proof. exact (@lem289604 (term188 R m d)). Qed.
Lemma lem289606 (R : type1605) (m : nat) (d : nat) : (term228 R m d) = (term188 R m d).
Proof. exact (SYM (@lem289605 R m d)). Qed.
Lemma lem289607 (R : type1605) (m : nat) (d : nat) (h1 : term229 R m d) : term229 R m d.
Proof. exact (h1). Qed.
Lemma lem289627 (x : nat) (R : type1605) (y : nat) (z : nat) : (term254 x R y z) = (term255 x R y z).
Proof. exact (@lem17045 (R x y) (R y z)). Qed.
Lemma lem289628 (R : type1605) (x : nat) (z : nat) : (R x z) = (R x z).
Proof. exact (eq_refl (R x z)). Qed.
Lemma lem289629 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem289630 (x : nat) (R : type1605) (y : nat) (z : nat) : (term256 x R y z) = (term257 x R y z).
Proof. exact (MK_COMB (@lem289629) (@lem289627 x R y z)). Qed.
Lemma lem289631 (y : nat) (R : type1605) (x : nat) (z : nat) : (term258 y R x z) = (term259 y R x z).
Proof. exact (MK_COMB (@lem289630 x R y z) (@lem289628 R x z)). Qed.
Lemma lem289632 (y : nat) (R : type1605) (x : nat) (z : nat) : (term214 y R x z) = (term258 y R x z).
Proof. exact (@lem17265 (term260 x R y z) (R x z)). Qed.
Lemma lem289633 (y : nat) (R : type1605) (x : nat) (z : nat) : (term214 y R x z) = (term259 y R x z).
Proof. exact (TRANS (@lem289632 y R x z) (@lem289631 y R x z)). Qed.
Lemma lem289634 (y : nat) (R : type1605) (x : nat) : (term215 y R x) = (term261 y R x).
Proof. exact (fun_ext (fun z : nat => @lem289633 y R x z)). Qed.
Lemma lem289635 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem289636 (y : nat) (R : type1605) (x : nat) : (term216 y R x) = (term262 y R x).
Proof. exact (MK_COMB (@lem289635) (@lem289634 y R x)). Qed.
Lemma lem289637 (R : type1605) (x : nat) : (term217 R x) = (term263 R x).
Proof. exact (fun_ext (fun y : nat => @lem289636 y R x)). Qed.
Lemma lem289638 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem289639 (R : type1605) (x : nat) : (term218 R x) = (term264 R x).
Proof. exact (MK_COMB (@lem289638) (@lem289637 R x)). Qed.
Lemma lem289640 (R : type1605) : (term219 R) = (term265 R).
Proof. exact (fun_ext (fun x : nat => @lem289639 R x)). Qed.
Lemma lem289641 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem289702 (R : type1605) : (term36 R) = (term266 R).
Proof. exact (MK_COMB (@lem289641) (@lem289640 R)). Qed.
Lemma lem289703 (R : type1605) (h1 : term36 R) : term266 R.
Proof. exact (EQ_MP (@lem289702 R) (@lem289600 R h1)). Qed.
Lemma lem289704 (R : type1605) (n : nat) : (term67 R n) = (term67 R n).
Proof. exact (eq_refl (term67 R n)). Qed.
Lemma lem289705 (R : type1605) : (term68 R) = (term68 R).
Proof. exact (fun_ext (fun n : nat => @lem289704 R n)). Qed.
Lemma lem289706 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem289715 (R : type1605) : (term50 R) = (term50 R).
Proof. exact (MK_COMB (@lem289706) (@lem289705 R)). Qed.
Lemma lem289716 (R : type1605) (h1 : term50 R) : term50 R.
Proof. exact (EQ_MP (@lem289715 R) (@lem289601 R h1)). Qed.
Lemma lem289722 (R : type1605) (m : nat) (d : nat) (h1 : term113 R m d) : term113 R m d.
Proof. exact (h1). Qed.
Lemma lem289728 (R : type1605) (m : nat) (d : nat) (h1 : term229 R m d) : term229 R m d.
Proof. exact (h1). Qed.
Lemma lem289762 (y : nat) (R : type1605) (x : nat) (z : nat) : (term259 y R x z) = (term259 y R x z).
Proof. exact (eq_refl (term259 y R x z)). Qed.
Lemma lem289763 (y : nat) (R : type1605) (x : nat) : (term261 y R x) = (term261 y R x).
Proof. exact (fun_ext (fun z : nat => @lem289762 y R x z)). Qed.
Lemma lem289764 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem289765 (y : nat) (R : type1605) (x : nat) : (term262 y R x) = (term262 y R x).
Proof. exact (MK_COMB (@lem289764) (@lem289763 y R x)). Qed.
Lemma lem289766 (R : type1605) (x : nat) : (term263 R x) = (term263 R x).
Proof. exact (fun_ext (fun y : nat => @lem289765 y R x)). Qed.
Lemma lem289767 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem289768 (R : type1605) (x : nat) : (term264 R x) = (term264 R x).
Proof. exact (MK_COMB (@lem289767) (@lem289766 R x)). Qed.
Lemma lem289769 (R : type1605) : (term265 R) = (term265 R).
Proof. exact (fun_ext (fun x : nat => @lem289768 R x)). Qed.
Lemma lem289770 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem289771 (R : type1605) : (term266 R) = (term266 R).
Proof. exact (MK_COMB (@lem289770) (@lem289769 R)). Qed.
Lemma lem289772 (R : type1605) (h1 : term36 R) : term266 R.
Proof. exact (EQ_MP (@lem289771 R) (@lem289703 R h1)). Qed.
Lemma lem289779 (R : type1605) (n : nat) : (term67 R n) = (term67 R n).
Proof. exact (eq_refl (term67 R n)). Qed.
Lemma lem289780 (R : type1605) : (term68 R) = (term68 R).
Proof. exact (fun_ext (fun n : nat => @lem289779 R n)). Qed.
Lemma lem289781 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem289782 (R : type1605) : (term50 R) = (term50 R).
Proof. exact (MK_COMB (@lem289781) (@lem289780 R)). Qed.
Lemma lem289783 (R : type1605) (h1 : term50 R) : term50 R.
Proof. exact (EQ_MP (@lem289782 R) (@lem289716 R h1)). Qed.
Lemma lem289793 (R : type1605) (m : nat) (d : nat) (h1 : term113 R m d) : term113 R m d.
Proof. exact (h1). Qed.
Lemma lem289807 (R : type1605) (m : nat) (d : nat) (h1 : term229 R m d) : term229 R m d.
Proof. exact (h1). Qed.
Lemma lem289828 (y : nat) (R : type1605) (x : nat) (z : nat) : (term259 y R x z) = (term259 y R x z).
Proof. exact (eq_refl (term259 y R x z)). Qed.
Lemma lem289829 (y : nat) (R : type1605) (x : nat) : (term261 y R x) = (term261 y R x).
Proof. exact (fun_ext (fun z : nat => @lem289828 y R x z)). Qed.
Lemma lem289830 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem289831 (y : nat) (R : type1605) (x : nat) : (term262 y R x) = (term262 y R x).
Proof. exact (MK_COMB (@lem289830) (@lem289829 y R x)). Qed.
Lemma lem289832 (R : type1605) (x : nat) : (term263 R x) = (term263 R x).
Proof. exact (fun_ext (fun y : nat => @lem289831 y R x)). Qed.
Lemma lem289833 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem289834 (R : type1605) (x : nat) : (term264 R x) = (term264 R x).
Proof. exact (MK_COMB (@lem289833) (@lem289832 R x)). Qed.
Lemma lem289835 (R : type1605) : (term265 R) = (term265 R).
Proof. exact (fun_ext (fun x : nat => @lem289834 R x)). Qed.
Lemma lem289836 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem289838 (R : type1605) : (term266 R) = (term266 R).
Proof. exact (MK_COMB (@lem289836) (@lem289835 R)). Qed.
Lemma lem289839 (R : type1605) (h1 : term36 R) : term266 R.
Proof. exact (EQ_MP (@lem289838 R) (@lem289772 R h1)). Qed.
Lemma lem289841 (R : type1605) (n : nat) : (term67 R n) = (term67 R n).
Proof. exact (eq_refl (term67 R n)). Qed.
Lemma lem289842 (R : type1605) : (term68 R) = (term68 R).
Proof. exact (fun_ext (fun n : nat => @lem289841 R n)). Qed.
Lemma lem289843 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem289845 (R : type1605) : (term50 R) = (term50 R).
Proof. exact (MK_COMB (@lem289843) (@lem289842 R)). Qed.
Lemma lem289846 (R : type1605) (h1 : term50 R) : term50 R.
Proof. exact (EQ_MP (@lem289845 R) (@lem289783 R h1)). Qed.
Lemma lem289850 (R : type1605) (m : nat) (d : nat) (h1 : term113 R m d) : term113 R m d.
Proof. exact (h1). Qed.
Lemma lem289854 (R : type1605) (m : nat) (d : nat) (h1 : term229 R m d) : term229 R m d.
Proof. exact (h1). Qed.
Lemma lem289858 (_6491 : nat) (R : type1605) (h1 : term36 R) : term267 R _6491.
Proof. exact (@lem289839 R h1 _6491). Qed.
Lemma lem289859 (R : type1605) (_6491 : nat) : (term267 R _6491) = (term264 R _6491).
Proof. exact (eq_refl (term267 R _6491)). Qed.
Lemma lem289860 (_6491 : nat) (R : type1605) (h1 : term36 R) : term264 R _6491.
Proof. exact (EQ_MP (@lem289859 R _6491) (@lem289858 _6491 R h1)). Qed.
Lemma lem289861 (_6491 : nat) (_6492 : nat) (R : type1605) (h1 : term36 R) : term268 R _6491 _6492.
Proof. exact (@lem289860 _6491 R h1 _6492). Qed.
Lemma lem289862 (_6492 : nat) (R : type1605) (_6491 : nat) : (term268 R _6491 _6492) = (term262 _6492 R _6491).
Proof. exact (eq_refl (term268 R _6491 _6492)). Qed.
Lemma lem289863 (_6492 : nat) (_6491 : nat) (R : type1605) (h1 : term36 R) : term262 _6492 R _6491.
Proof. exact (EQ_MP (@lem289862 _6492 R _6491) (@lem289861 _6491 _6492 R h1)). Qed.
Lemma lem289864 (_6492 : nat) (_6491 : nat) (_6493 : nat) (R : type1605) (h1 : term36 R) : term269 _6492 R _6491 _6493.
Proof. exact (@lem289863 _6492 _6491 R h1 _6493). Qed.
Lemma lem289865 (_6492 : nat) (R : type1605) (_6491 : nat) (_6493 : nat) : (term269 _6492 R _6491 _6493) = (term259 _6492 R _6491 _6493).
Proof. exact (eq_refl (term269 _6492 R _6491 _6493)). Qed.
Lemma lem289866 (_6492 : nat) (_6491 : nat) (_6493 : nat) (R : type1605) (h1 : term36 R) : term259 _6492 R _6491 _6493.
Proof. exact (EQ_MP (@lem289865 _6492 R _6491 _6493) (@lem289864 _6492 _6491 _6493 R h1)). Qed.
Lemma lem289867 (_6494 : nat) (R : type1605) (h1 : term50 R) : term270 R _6494.
Proof. exact (@lem289846 R h1 _6494). Qed.
Lemma lem289868 (R : type1605) (_6494 : nat) : (term270 R _6494) = (term67 R _6494).
Proof. exact (eq_refl (term270 R _6494)). Qed.
Lemma lem289882 (_6492 : nat) (R : type1605) (_6491 : nat) (_6493 : nat) : (term259 _6492 R _6491 _6493) = (term271 _6492 R _6491 _6493).
Proof. exact (@lem286715 (term272 R _6491 _6492) (term272 R _6492 _6493) (R _6491 _6493)). Qed.
Lemma lem289883 (_6492 : nat) (_6491 : nat) (_6493 : nat) (R : type1605) (h1 : term36 R) : term271 _6492 R _6491 _6493.
Proof. exact (EQ_MP (@lem289882 _6492 R _6491 _6493) (@lem289866 _6492 _6491 _6493 R h1)). Qed.
Lemma lem289887 (R : type1605) (m : nat) (d : nat) (h1 : term113 R m d) : term113 R m d.
Proof. exact (h1). Qed.
Lemma lem289889 (R : type1605) (m : nat) (d : nat) (h1 : term229 R m d) : term229 R m d.
Proof. exact (h1). Qed.
Lemma lem289891 (R : type1605) (m : nat) (d : nat) (h1 : term113 R m d) : term113 R m d.
Proof. exact (h1). Qed.
Lemma lem289892 (R : type1605) (m : nat) (d : nat) (h1 : term113 R m d) : term273 R m d.
Proof. exact (fun h0 : term274 R m d => @lem289891 R m d h1). Qed.
Lemma lem289894 (p : Prop) : (term223 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem289895 (R : type1605) (m : nat) (d : nat) : (term273 R m d) = (term113 R m d).
Proof. exact (@lem289894 (term113 R m d)). Qed.
Lemma lem289896 (R : type1605) (m : nat) (d : nat) (h1 : term113 R m d) : term113 R m d.
Proof. exact (EQ_MP (@lem289895 R m d) (@lem289892 R m d h1)). Qed.
Lemma lem289898 (_6494 : nat) (R : type1605) (h1 : term50 R) : term67 R _6494.
Proof. exact (EQ_MP (@lem289868 R _6494) (@lem289867 _6494 R h1)). Qed.
Lemma lem289899 (m : nat) (d : nat) (R : type1605) (h1 : term50 R) : term275 R m d.
Proof. exact (@lem289898 (Nat.add m d) R h1). Qed.
Lemma lem289900 (m : nat) (d : nat) (R : type1605) (h1 : term50 R) : term276 R m d.
Proof. exact (fun h0 : term277 R m d => @lem289899 m d R h1). Qed.
Lemma lem289902 (p : Prop) : (term223 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem289903 (R : type1605) (m : nat) (d : nat) : (term276 R m d) = (term275 R m d).
Proof. exact (@lem289902 (term275 R m d)). Qed.
Lemma lem289904 (m : nat) (d : nat) (R : type1605) (h1 : term50 R) : term275 R m d.
Proof. exact (EQ_MP (@lem289903 R m d) (@lem289900 m d R h1)). Qed.
Lemma lem289920 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem289921 (_6491 : nat) (R : type1605) (_6492 : nat) (_6493 : nat) : (term278 _6492 R _6491 _6493) = (term279 _6491 R _6492 _6493).
Proof. exact (@lem289920 (R _6491 _6493) (term272 R _6492 _6493)). Qed.
Lemma lem289927 (R : type1605) (_6491 : nat) (_6492 : nat) : (term280 R _6491 _6492) = (term280 R _6491 _6492).
Proof. exact (eq_refl (term280 R _6491 _6492)). Qed.
Lemma lem289928 (_6491 : nat) (R : type1605) (_6492 : nat) (_6493 : nat) : (term271 _6492 R _6491 _6493) = (term281 _6491 R _6492 _6493).
Proof. exact (MK_COMB (@lem289927 R _6491 _6492) (@lem289921 _6491 R _6492 _6493)). Qed.
Lemma lem289932 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem289933 (_6491 : nat) (R : type1605) (_6492 : nat) (_6493 : nat) : (term281 _6491 R _6492 _6493) = (term282 _6491 R _6492 _6493).
Proof. exact (@lem289932 (R _6491 _6493) (term272 R _6491 _6492) (term272 R _6492 _6493)). Qed.
Lemma lem289949 (_6491 : nat) (R : type1605) (_6492 : nat) (_6493 : nat) : (term271 _6492 R _6491 _6493) = (term282 _6491 R _6492 _6493).
Proof. exact (TRANS (@lem289928 _6491 R _6492 _6493) (@lem289933 _6491 R _6492 _6493)). Qed.
Lemma lem289950 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem289951 (_6491 : nat) (R : type1605) (_6492 : nat) (_6493 : nat) : (term283 _6492 R _6491 _6493) = (term284 _6491 R _6492 _6493).
Proof. exact (MK_COMB (@lem289950) (@lem289949 _6491 R _6492 _6493)). Qed.
Lemma lem289967 (_6491 : nat) (R : type1605) (_6492 : nat) (_6493 : nat) : (term282 _6491 R _6492 _6493) = (term282 _6491 R _6492 _6493).
Proof. exact (eq_refl (term282 _6491 R _6492 _6493)). Qed.
Lemma lem289968 (_6491 : nat) (R : type1605) (_6492 : nat) (_6493 : nat) : ((term271 _6492 R _6491 _6493) = (term282 _6491 R _6492 _6493)) = ((term282 _6491 R _6492 _6493) = (term282 _6491 R _6492 _6493)).
Proof. exact (MK_COMB (@lem289951 _6491 R _6492 _6493) (@lem289967 _6491 R _6492 _6493)). Qed.
Lemma lem289970 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem289971 (x : Prop) : (x = x) = True.
Proof. exact (@lem289970 Prop x). Qed.
Lemma lem289972 (_6491 : nat) (R : type1605) (_6492 : nat) (_6493 : nat) : ((term282 _6491 R _6492 _6493) = (term282 _6491 R _6492 _6493)) = True.
Proof. exact (@lem289971 (term282 _6491 R _6492 _6493)). Qed.
Lemma lem289973 (_6491 : nat) (R : type1605) (_6492 : nat) (_6493 : nat) : ((term271 _6492 R _6491 _6493) = (term282 _6491 R _6492 _6493)) = True.
Proof. exact (TRANS (@lem289968 _6491 R _6492 _6493) (@lem289972 _6491 R _6492 _6493)). Qed.
Lemma lem289974 (_6491 : nat) (R : type1605) (_6492 : nat) (_6493 : nat) : True = ((term271 _6492 R _6491 _6493) = (term282 _6491 R _6492 _6493)).
Proof. exact (SYM (@lem289973 _6491 R _6492 _6493)). Qed.
Lemma lem289975 (_6491 : nat) (R : type1605) (_6492 : nat) (_6493 : nat) : (term271 _6492 R _6491 _6493) = (term282 _6491 R _6492 _6493).
Proof. exact (EQ_MP (@lem289974 _6491 R _6492 _6493) (@lem0)). Qed.
Lemma lem289976 (_6491 : nat) (_6492 : nat) (_6493 : nat) (R : type1605) (h1 : term36 R) : term282 _6491 R _6492 _6493.
Proof. exact (EQ_MP (@lem289975 _6491 R _6492 _6493) (@lem289883 _6492 _6491 _6493 R h1)). Qed.
Lemma lem289978 (b : Prop) (a : Prop) : (a \/ b) = (term285 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem289979 (_6492 : nat) (R : type1605) (_6491 : nat) (_6493 : nat) : (term282 _6491 R _6492 _6493) = (term286 _6492 R _6491 _6493).
Proof. exact (@lem289978 (term255 _6491 R _6492 _6493) (R _6491 _6493)). Qed.
Lemma lem289981 (a : Prop) (b : Prop) : (term287 a b) = (term288 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem289982 (_6491 : nat) (R : type1605) (_6492 : nat) (_6493 : nat) : (term289 _6491 R _6492 _6493) = (term290 _6491 R _6492 _6493).
Proof. exact (@lem289981 (term272 R _6491 _6492) (term272 R _6492 _6493)). Qed.
Lemma lem289984 (a : Prop) : (term197 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem289985 (R : type1605) (_6491 : nat) (_6492 : nat) : (term291 R _6491 _6492) = (R _6491 _6492).
Proof. exact (@lem289984 (R _6491 _6492)). Qed.
Lemma lem289986 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem289987 (R : type1605) (_6491 : nat) (_6492 : nat) : (term292 R _6491 _6492) = (term293 R _6491 _6492).
Proof. exact (MK_COMB (@lem289986) (@lem289985 R _6491 _6492)). Qed.
Lemma lem289989 (a : Prop) : (term197 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem289990 (R : type1605) (_6492 : nat) (_6493 : nat) : (term291 R _6492 _6493) = (R _6492 _6493).
Proof. exact (@lem289989 (R _6492 _6493)). Qed.
Lemma lem289991 (_6491 : nat) (R : type1605) (_6492 : nat) (_6493 : nat) : (term290 _6491 R _6492 _6493) = (term260 _6491 R _6492 _6493).
Proof. exact (MK_COMB (@lem289987 R _6491 _6492) (@lem289990 R _6492 _6493)). Qed.
Lemma lem289992 (_6491 : nat) (R : type1605) (_6492 : nat) (_6493 : nat) : (term289 _6491 R _6492 _6493) = (term260 _6491 R _6492 _6493).
Proof. exact (TRANS (@lem289982 _6491 R _6492 _6493) (@lem289991 _6491 R _6492 _6493)). Qed.
Lemma lem289993 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem289994 (_6491 : nat) (R : type1605) (_6492 : nat) (_6493 : nat) : (term294 _6491 R _6492 _6493) = (term295 _6491 R _6492 _6493).
Proof. exact (MK_COMB (@lem289993) (@lem289992 _6491 R _6492 _6493)). Qed.
Lemma lem289995 (R : type1605) (_6491 : nat) (_6493 : nat) : (R _6491 _6493) = (R _6491 _6493).
Proof. exact (eq_refl (R _6491 _6493)). Qed.
Lemma lem289996 (_6492 : nat) (R : type1605) (_6491 : nat) (_6493 : nat) : (term286 _6492 R _6491 _6493) = (term214 _6492 R _6491 _6493).
Proof. exact (MK_COMB (@lem289994 _6491 R _6492 _6493) (@lem289995 R _6491 _6493)). Qed.
Lemma lem289997 (_6492 : nat) (R : type1605) (_6491 : nat) (_6493 : nat) : (term282 _6491 R _6492 _6493) = (term214 _6492 R _6491 _6493).
Proof. exact (TRANS (@lem289979 _6492 R _6491 _6493) (@lem289996 _6492 R _6491 _6493)). Qed.
Lemma lem289999 (R : type1605) (m : nat) (d : nat) (h1 : term50 R) (h2 : term113 R m d) : term296 R m d.
Proof. exact (conj (@lem289896 R m d h2) (@lem289904 m d R h1)). Qed.
Lemma lem290001 (_6492 : nat) (_6491 : nat) (_6493 : nat) (R : type1605) (h1 : term36 R) : term214 _6492 R _6491 _6493.
Proof. exact (EQ_MP (@lem289997 _6492 R _6491 _6493) (@lem289976 _6491 _6492 _6493 R h1)). Qed.
Lemma lem290002 (m : nat) (d : nat) (R : type1605) (h1 : term36 R) : term297 R m d.
Proof. exact (@lem290001 (Nat.add m d) m (term14 m d) R h1). Qed.
Lemma lem290005 (R : type1605) (m : nat) (d : nat) (h1 : term36 R) (h2 : term50 R) (h3 : term113 R m d) : term188 R m d.
Proof. exact (@lem290002 m d R h1 (@lem289999 R m d h2 h3)). Qed.
Lemma lem290006 (R : type1605) (m : nat) (d : nat) (h1 : term36 R) (h2 : term50 R) (h3 : term113 R m d) : term298 R m d.
Proof. exact (fun h0 : term229 R m d => @lem290005 R m d h1 h2 h3). Qed.
Lemma lem290008 (p : Prop) : (term223 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem290009 (R : type1605) (m : nat) (d : nat) : (term298 R m d) = (term188 R m d).
Proof. exact (@lem290008 (term188 R m d)). Qed.
Lemma lem290010 (R : type1605) (m : nat) (d : nat) (h1 : term36 R) (h2 : term50 R) (h3 : term113 R m d) : term188 R m d.
Proof. exact (EQ_MP (@lem290009 R m d) (@lem290006 R m d h1 h2 h3)). Qed.
Lemma lem290013 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem290015 (R : type1605) (m : nat) (d : nat) : (term229 R m d) = (term299 R m d).
Proof. exact (@lem290013 (term188 R m d)). Qed.
Lemma lem290018 (R : type1605) (m : nat) (d : nat) (h1 : term229 R m d) : term299 R m d.
Proof. exact (EQ_MP (@lem290015 R m d) (@lem289889 R m d h1)). Qed.
Lemma lem290021 (R : type1605) (m : nat) (d : nat) (h1 : term36 R) (h2 : term50 R) (h3 : term229 R m d) (h4 : term113 R m d) : False.
Proof. exact (@lem290018 R m d h3 (@lem290010 R m d h1 h2 h4)). Qed.
Lemma lem290022 (R : type1605) (m : nat) (d : nat) (h1 : term36 R) (h2 : term50 R) (h3 : term229 R m d) (h4 : term113 R m d) : term225.
Proof. exact (fun h0 : ~ False => @lem290021 R m d h1 h2 h3 h4). Qed.
Lemma lem290024 (p : Prop) : (term223 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem290025 : term225 = False.
Proof. exact (@lem290024 False). Qed.
Lemma lem290026 (R : type1605) (m : nat) (d : nat) (h1 : term36 R) (h2 : term50 R) (h3 : term229 R m d) (h4 : term113 R m d) : False.
Proof. exact (EQ_MP (@lem290025) (@lem290022 R m d h1 h2 h3 h4)). Qed.
Lemma lem290027 (R : type1605) (m : nat) (d : nat) (h1 : term36 R) (h2 : term50 R) (h3 : term229 R m d) (h4 : term113 R m d) : (term229 R m d) = False.
Proof. exact (prop_ext (fun h5 : term229 R m d => @lem290026 R m d h1 h2 h3 h4) (fun h5 : False => @lem289889 R m d h3)). Qed.
Lemma lem290028 (R : type1605) (m : nat) (d : nat) (h1 : term36 R) (h2 : term50 R) (h3 : term229 R m d) (h4 : term113 R m d) : False.
Proof. exact (EQ_MP (@lem290027 R m d h1 h2 h3 h4) (@lem289889 R m d h3)). Qed.
Lemma lem290029 (R : type1605) (m : nat) (d : nat) (h1 : term36 R) (h2 : term50 R) (h3 : term229 R m d) (h4 : term113 R m d) : (term113 R m d) = False.
Proof. exact (prop_ext (fun h5 : term113 R m d => @lem290028 R m d h1 h2 h3 h4) (fun h5 : False => @lem289887 R m d h4)). Qed.
Lemma lem290030 (R : type1605) (m : nat) (d : nat) (h1 : term36 R) (h2 : term50 R) (h3 : term229 R m d) (h4 : term113 R m d) : False.
Proof. exact (EQ_MP (@lem290029 R m d h1 h2 h3 h4) (@lem289887 R m d h4)). Qed.
Lemma lem290031 (R : type1605) (m : nat) (d : nat) (h1 : term36 R) (h2 : term50 R) (h3 : term229 R m d) (h4 : term113 R m d) : (term229 R m d) = False.
Proof. exact (prop_ext (fun h5 : term229 R m d => @lem290030 R m d h1 h2 h3 h4) (fun h5 : False => @lem289854 R m d h3)). Qed.
Lemma lem290032 (R : type1605) (m : nat) (d : nat) (h1 : term36 R) (h2 : term50 R) (h3 : term229 R m d) (h4 : term113 R m d) : False.
Proof. exact (EQ_MP (@lem290031 R m d h1 h2 h3 h4) (@lem289854 R m d h3)). Qed.
Lemma lem290033 (R : type1605) (m : nat) (d : nat) (h1 : term36 R) (h2 : term50 R) (h3 : term229 R m d) (h4 : term113 R m d) : (term113 R m d) = False.
Proof. exact (prop_ext (fun h5 : term113 R m d => @lem290032 R m d h1 h2 h3 h4) (fun h5 : False => @lem289850 R m d h4)). Qed.
Lemma lem290034 (R : type1605) (m : nat) (d : nat) (h1 : term36 R) (h2 : term50 R) (h3 : term229 R m d) (h4 : term113 R m d) : False.
Proof. exact (EQ_MP (@lem290033 R m d h1 h2 h3 h4) (@lem289850 R m d h4)). Qed.
Lemma lem290035 (R : type1605) (m : nat) (d : nat) (h1 : term36 R) (h2 : term50 R) (h3 : term229 R m d) (h4 : term113 R m d) : (term229 R m d) = False.
Proof. exact (prop_ext (fun h5 : term229 R m d => @lem290034 R m d h1 h2 h3 h4) (fun h5 : False => @lem289854 R m d h3)). Qed.
Lemma lem290036 (R : type1605) (m : nat) (d : nat) (h1 : term36 R) (h2 : term50 R) (h3 : term229 R m d) (h4 : term113 R m d) : False.
Proof. exact (EQ_MP (@lem290035 R m d h1 h2 h3 h4) (@lem289854 R m d h3)). Qed.
Lemma lem290037 (R : type1605) (m : nat) (d : nat) (h1 : term36 R) (h2 : term50 R) (h3 : term229 R m d) (h4 : term113 R m d) : (term113 R m d) = False.
Proof. exact (prop_ext (fun h5 : term113 R m d => @lem290036 R m d h1 h2 h3 h4) (fun h5 : False => @lem289850 R m d h4)). Qed.
Lemma lem290038 (R : type1605) (m : nat) (d : nat) (h1 : term36 R) (h2 : term50 R) (h3 : term229 R m d) (h4 : term113 R m d) : False.
Proof. exact (EQ_MP (@lem290037 R m d h1 h2 h3 h4) (@lem289850 R m d h4)). Qed.
Lemma lem290039 (R : type1605) (m : nat) (d : nat) (h1 : term36 R) (h2 : term50 R) (h3 : term229 R m d) (h4 : term113 R m d) : (term50 R) = False.
Proof. exact (prop_ext (fun h5 : term50 R => @lem290038 R m d h1 h2 h3 h4) (fun h5 : False => @lem289846 R h2)). Qed.
Lemma lem290040 (R : type1605) (m : nat) (d : nat) (h1 : term36 R) (h2 : term50 R) (h3 : term229 R m d) (h4 : term113 R m d) : False.
Proof. exact (EQ_MP (@lem290039 R m d h1 h2 h3 h4) (@lem289846 R h2)). Qed.
Lemma lem290041 (R : type1605) (m : nat) (d : nat) (h1 : term36 R) (h2 : term50 R) (h3 : term229 R m d) (h4 : term113 R m d) : (term229 R m d) = False.
Proof. exact (prop_ext (fun h5 : term229 R m d => @lem290040 R m d h1 h2 h3 h4) (fun h5 : False => @lem289807 R m d h3)). Qed.
Lemma lem290042 (R : type1605) (m : nat) (d : nat) (h1 : term36 R) (h2 : term50 R) (h3 : term229 R m d) (h4 : term113 R m d) : False.
Proof. exact (EQ_MP (@lem290041 R m d h1 h2 h3 h4) (@lem289807 R m d h3)). Qed.
Lemma lem290043 (R : type1605) (m : nat) (d : nat) (h1 : term36 R) (h2 : term50 R) (h3 : term229 R m d) (h4 : term113 R m d) : (term113 R m d) = False.
Proof. exact (prop_ext (fun h5 : term113 R m d => @lem290042 R m d h1 h2 h3 h4) (fun h5 : False => @lem289793 R m d h4)). Qed.
Lemma lem290044 (R : type1605) (m : nat) (d : nat) (h1 : term36 R) (h2 : term50 R) (h3 : term229 R m d) (h4 : term113 R m d) : False.
Proof. exact (EQ_MP (@lem290043 R m d h1 h2 h3 h4) (@lem289793 R m d h4)). Qed.
Lemma lem290045 (R : type1605) (m : nat) (d : nat) (h1 : term36 R) (h2 : term50 R) (h3 : term229 R m d) (h4 : term113 R m d) : (term50 R) = False.
Proof. exact (prop_ext (fun h5 : term50 R => @lem290044 R m d h1 h2 h3 h4) (fun h5 : False => @lem289783 R h2)). Qed.
Lemma lem290046 (R : type1605) (m : nat) (d : nat) (h1 : term36 R) (h2 : term50 R) (h3 : term229 R m d) (h4 : term113 R m d) : False.
Proof. exact (EQ_MP (@lem290045 R m d h1 h2 h3 h4) (@lem289783 R h2)). Qed.
Lemma lem290047 (R : type1605) (m : nat) (d : nat) (h1 : term36 R) (h2 : term50 R) (h3 : term229 R m d) (h4 : term113 R m d) : (term229 R m d) = False.
Proof. exact (prop_ext (fun h5 : term229 R m d => @lem290046 R m d h1 h2 h3 h4) (fun h5 : False => @lem289728 R m d h3)). Qed.
Lemma lem290048 (R : type1605) (m : nat) (d : nat) (h1 : term36 R) (h2 : term50 R) (h3 : term229 R m d) (h4 : term113 R m d) : False.
Proof. exact (EQ_MP (@lem290047 R m d h1 h2 h3 h4) (@lem289728 R m d h3)). Qed.
Lemma lem290049 (R : type1605) (m : nat) (d : nat) (h1 : term36 R) (h2 : term50 R) (h3 : term229 R m d) (h4 : term113 R m d) : (term113 R m d) = False.
Proof. exact (prop_ext (fun h5 : term113 R m d => @lem290048 R m d h1 h2 h3 h4) (fun h5 : False => @lem289722 R m d h4)). Qed.
Lemma lem290050 (R : type1605) (m : nat) (d : nat) (h1 : term36 R) (h2 : term50 R) (h3 : term229 R m d) (h4 : term113 R m d) : False.
Proof. exact (EQ_MP (@lem290049 R m d h1 h2 h3 h4) (@lem289722 R m d h4)). Qed.
Lemma lem290051 (R : type1605) (m : nat) (d : nat) (h1 : term36 R) (h2 : term50 R) (h3 : term229 R m d) (h4 : term113 R m d) : (term50 R) = False.
Proof. exact (prop_ext (fun h5 : term50 R => @lem290050 R m d h1 h2 h3 h4) (fun h5 : False => @lem289716 R h2)). Qed.
Lemma lem290052 (R : type1605) (m : nat) (d : nat) (h1 : term36 R) (h2 : term50 R) (h3 : term229 R m d) (h4 : term113 R m d) : False.
Proof. exact (EQ_MP (@lem290051 R m d h1 h2 h3 h4) (@lem289716 R h2)). Qed.
Lemma lem290053 (R : type1605) (m : nat) (d : nat) (h1 : term36 R) (h2 : term50 R) (h3 : term229 R m d) (h4 : term113 R m d) : (term229 R m d) = False.
Proof. exact (prop_ext (fun h5 : term229 R m d => @lem290052 R m d h1 h2 h3 h4) (fun h5 : False => @lem289607 R m d h3)). Qed.
Lemma lem290054 (R : type1605) (m : nat) (d : nat) (h1 : term36 R) (h2 : term50 R) (h3 : term229 R m d) (h4 : term113 R m d) : False.
Proof. exact (EQ_MP (@lem290053 R m d h1 h2 h3 h4) (@lem289607 R m d h3)). Qed.
Lemma lem290055 (R : type1605) (m : nat) (d : nat) (h1 : term36 R) (h2 : term50 R) (h3 : term113 R m d) : term228 R m d.
Proof. exact (fun h0 : term229 R m d => @lem290054 R m d h1 h2 h0 h3). Qed.
Lemma lem290056 (R : type1605) (m : nat) (d : nat) (h1 : term36 R) (h2 : term50 R) (h3 : term113 R m d) : term188 R m d.
Proof. exact (EQ_MP (@lem289606 R m d) (@lem290055 R m d h1 h2 h3)). Qed.
Lemma lem290057 (m : nat) (d : nat) (R : type1605) (h1 : term36 R) (h2 : term50 R) : term236 R m d.
Proof. exact (fun h0 : term113 R m d => @lem290056 R m d h1 h2 h0). Qed.
Lemma lem290058 (m : nat) (d : nat) (R : type1605) (h1 : term36 R) : term238 R m d.
Proof. exact (fun h0 : term50 R => @lem290057 m d R h1 h0). Qed.
Lemma lem290059 (R : type1605) (m : nat) (d : nat) : term240 R m d.
Proof. exact (fun h0 : term36 R => @lem290058 m d R h0). Qed.
Lemma lem290060 (R : type1605) (m : nat) (d : nat) : term241 R m d.
Proof. exact (fun h0 : term37 R => @lem290059 R m d). Qed.
Lemma lem290065 (m : nat) (d : nat) : term245 m d.
Proof. exact (fun R : type1605 => @lem290060 R m d). Qed.
Lemma lem290070 (d : nat) : term249 d.
Proof. exact (fun m : nat => @lem290065 m d). Qed.
Lemma lem290075 : term253.
Proof. exact (fun d : nat => @lem290070 d). Qed.
Lemma lem290076 : term252.
Proof. exact (EQ_MP (@lem289598) (@lem290075)). Qed.
Lemma lem290077 (d : nat) : term300 d.
Proof. exact (@lem290076 d). Qed.
Lemma lem290078 (d : nat) : (term300 d) = (term248 d).
Proof. exact (eq_refl (term300 d)). Qed.
Lemma lem290079 (d : nat) : term248 d.
Proof. exact (EQ_MP (@lem290078 d) (@lem290077 d)). Qed.
Lemma lem290080 (d : nat) (m : nat) : term301 d m.
Proof. exact (@lem290079 d m). Qed.
Lemma lem290081 (m : nat) (d : nat) : (term301 d m) = (term244 m d).
Proof. exact (eq_refl (term301 d m)). Qed.
Lemma lem290082 (m : nat) (d : nat) : term244 m d.
Proof. exact (EQ_MP (@lem290081 m d) (@lem290080 d m)). Qed.
Lemma lem290083 (m : nat) (d : nat) (R : type1605) : term302 m d R.
Proof. exact (@lem290082 m d R). Qed.
Lemma lem290084 (R : type1605) (m : nat) (d : nat) : (term302 m d R) = (term230 R m d).
Proof. exact (eq_refl (term302 m d R)). Qed.
Lemma lem290085 (R : type1605) (m : nat) (d : nat) : term230 R m d.
Proof. exact (EQ_MP (@lem290084 R m d) (@lem290083 m d R)). Qed.
Lemma lem290087 (R : type1605) (m : nat) (d : nat) : term230 R m d.
Proof. exact (@lem289393 R m d (@lem290085 R m d)). Qed.
Lemma lem290088 (m : nat) (d : nat) (R : type1605) (h1 : term37 R) : term239 R m d.
Proof. exact (@lem290087 R m d (@lem286792 R h1)). Qed.
Lemma lem290089 (m : nat) (d : nat) (R : type1605) (h1 : term36 R) (h2 : term37 R) : term237 R m d.
Proof. exact (@lem290088 m d R h2 (@lem286791 R h1)). Qed.
Lemma lem290090 (m : nat) (d : nat) (R : type1605) (h1 : term36 R) (h2 : term37 R) (h3 : term50 R) : term235 R m d.
Proof. exact (@lem290089 m d R h1 h2 (@lem288396 R h3)). Qed.
Lemma lem290091 (R : type1605) (m : nat) (d : nat) (h1 : term36 R) (h2 : term37 R) (h3 : term50 R) (h4 : term113 R m d) : term228 R m d.
Proof. exact (@lem290090 m d R h1 h2 h3 (@lem288833 R m d h4)). Qed.
Lemma lem290092 (R : type1605) (m : nat) (d : nat) (h1 : term36 R) (h2 : term37 R) (h3 : term50 R) (h4 : term229 R m d) (h5 : term113 R m d) : False.
Proof. exact (@lem290091 R m d h1 h2 h3 h5 (@lem289378 R m d h4)). Qed.
Lemma lem290093 (R : type1605) (m : nat) (d : nat) (h1 : term36 R) (h2 : term37 R) (h3 : term50 R) (h4 : term229 R m d) (h5 : term113 R m d) : (term229 R m d) = False.
Proof. exact (prop_ext (fun h6 : term229 R m d => @lem290092 R m d h1 h2 h3 h4 h5) (fun h6 : False => @lem289378 R m d h4)). Qed.
Lemma lem290094 (R : type1605) (m : nat) (d : nat) (h1 : term36 R) (h2 : term37 R) (h3 : term50 R) (h4 : term229 R m d) (h5 : term113 R m d) : False.
Proof. exact (EQ_MP (@lem290093 R m d h1 h2 h3 h4 h5) (@lem289378 R m d h4)). Qed.
Lemma lem290095 (R : type1605) (m : nat) (d : nat) (h1 : term36 R) (h2 : term37 R) (h3 : term50 R) (h4 : term113 R m d) : term228 R m d.
Proof. exact (fun h0 : term229 R m d => @lem290094 R m d h1 h2 h3 h0 h4). Qed.
Lemma lem290096 (R : type1605) (m : nat) (d : nat) (h1 : term36 R) (h2 : term37 R) (h3 : term50 R) (h4 : term113 R m d) : term188 R m d.
Proof. exact (EQ_MP (@lem289377 R m d) (@lem290095 R m d h1 h2 h3 h4)). Qed.
Lemma lem290097 (R : type1605) (m : nat) (d : nat) (h1 : term36 R) (h2 : term37 R) (h3 : term50 R) (h4 : term113 R m d) : term174 R m d.
Proof. exact (EQ_MP (@lem288844 R m d) (@lem290096 R m d h1 h2 h3 h4)). Qed.
Lemma lem290098 (m : nat) (R : type1605) (h1 : term36 R) (h2 : term37 R) (h3 : term50 R) : term167 R m.
Proof. exact (EQ_MP (@lem288838 R m) (@lem289373 m R h1 h2 h3)). Qed.
Lemma lem290099 (m : nat) (d : nat) (R : type1605) (h1 : term36 R) (h2 : term37 R) (h3 : term50 R) : term176 R m d.
Proof. exact (fun h0 : term113 R m d => @lem290097 R m d h1 h2 h3 h0). Qed.
Lemma lem290104 (m : nat) (R : type1605) (h1 : term36 R) (h2 : term37 R) (h3 : term50 R) : term180 R m.
Proof. exact (fun d : nat => @lem290099 m d R h1 h2 h3). Qed.
Lemma lem290105 (m : nat) (R : type1605) (h1 : term36 R) (h2 : term37 R) (h3 : term50 R) : term182 R m.
Proof. exact (conj (@lem290098 m R h1 h2 h3) (@lem290104 m R h1 h2 h3)). Qed.
Lemma lem290106 (m : nat) (R : type1605) (h1 : term36 R) (h2 : term37 R) (h3 : term50 R) : term163 R m.
Proof. exact (@lem288832 R m (@lem290105 m R h1 h2 h3)). Qed.
Lemma lem290107 (m : nat) (R : type1605) (h1 : term36 R) (h2 : term37 R) (h3 : term50 R) : term144 R m.
Proof. exact (EQ_MP (@lem288809 R m) (@lem290106 m R h1 h2 h3)). Qed.
Lemma lem290108 (m : nat) (R : type1605) (h1 : term36 R) (h2 : term37 R) (h3 : term50 R) : term121 R m.
Proof. exact (EQ_MP (@lem288758 R m) (@lem290107 m R h1 h2 h3)). Qed.
Lemma lem290113 (R : type1605) (h1 : term36 R) (h2 : term37 R) (h3 : term50 R) : term124 R.
Proof. exact (fun m : nat => @lem290108 m R h1 h2 h3). Qed.
Lemma lem290114 (R : type1605) (h1 : term36 R) (h2 : term37 R) (h3 : term50 R) : term49 R.
Proof. exact (EQ_MP (@lem288727 R) (@lem290113 R h1 h2 h3)). Qed.
Lemma lem290116 (R : type1605) (h1 : term36 R) (h2 : term37 R) : term303 R.
Proof. exact (fun h0 : term50 R => @lem290114 R h1 h2 h0). Qed.
Lemma lem290117 (R : type1605) (h1 : term36 R) (h2 : term37 R) : term304 R.
Proof. exact (conj (@lem287438 R) (@lem290116 R h1 h2)). Qed.
Lemma lem290118 (R : type1605) : (term304 R) = ((term49 R) = (term50 R)).
Proof. exact (@lem32 (term49 R) (term50 R)). Qed.
Lemma lem290119 (R : type1605) (h1 : term36 R) (h2 : term37 R) : (term49 R) = (term50 R).
Proof. exact (EQ_MP (@lem290118 R) (@lem290117 R h1 h2)). Qed.
Lemma lem290120 (R : type1605) (h1 : term35 R) : term36 R.
Proof. exact (proj2 (@lem286790 R h1)). Qed.
Lemma lem290121 (R : type1605) (h1 : term35 R) : term37 R.
Proof. exact (proj1 (@lem286790 R h1)). Qed.
Lemma lem290122 (R : type1605) (h1 : term36 R) (h2 : term37 R) : (term36 R) = ((term49 R) = (term50 R)).
Proof. exact (prop_ext (fun h3 : term36 R => @lem290119 R h1 h2) (fun h3 : (term49 R) = (term50 R) => @lem286791 R h1)). Qed.
Lemma lem290123 (R : type1605) (h1 : term36 R) (h2 : term37 R) : (term49 R) = (term50 R).
Proof. exact (EQ_MP (@lem290122 R h1 h2) (@lem286791 R h1)). Qed.
Lemma lem290124 (R : type1605) (h1 : term36 R) (h2 : term37 R) : (term37 R) = ((term49 R) = (term50 R)).
Proof. exact (prop_ext (fun h3 : term37 R => @lem290123 R h1 h2) (fun h3 : (term49 R) = (term50 R) => @lem286792 R h2)). Qed.
Lemma lem290125 (R : type1605) (h1 : term36 R) (h2 : term37 R) : (term49 R) = (term50 R).
Proof. exact (EQ_MP (@lem290124 R h1 h2) (@lem286792 R h2)). Qed.
Lemma lem290126 (R : type1605) (h1 : term37 R) (h2 : term35 R) : (term36 R) = ((term49 R) = (term50 R)).
Proof. exact (prop_ext (fun h3 : term36 R => @lem290125 R h3 h1) (fun h3 : (term49 R) = (term50 R) => @lem290120 R h2)). Qed.
Lemma lem290127 (R : type1605) (h1 : term37 R) (h2 : term35 R) : (term49 R) = (term50 R).
Proof. exact (EQ_MP (@lem290126 R h1 h2) (@lem290120 R h2)). Qed.
Lemma lem290128 (R : type1605) (h1 : term35 R) : (term37 R) = ((term49 R) = (term50 R)).
Proof. exact (prop_ext (fun h2 : term37 R => @lem290127 R h2 h1) (fun h2 : (term49 R) = (term50 R) => @lem290121 R h1)). Qed.
Lemma lem290129 (R : type1605) (h1 : term35 R) : (term49 R) = (term50 R).
Proof. exact (EQ_MP (@lem290128 R h1) (@lem290121 R h1)). Qed.
Lemma lem290130 (R : type1605) : term305 R.
Proof. exact (fun h0 : term35 R => @lem290129 R h0). Qed.
Lemma lem290135 : term306.
Proof. exact (fun R : type1605 => @lem290130 R). Qed.
