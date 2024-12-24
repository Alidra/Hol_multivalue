Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import TRANSITIVE_STEPWISE_LT_EQ_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import EXISTS_REFL_spec.
Require Import LEFT_FORALL_IMP_THM_spec.
Require Import LEFT_IMP_EXISTS_THM_spec.
Require Import LT_EXISTS_spec.
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
Require Import thm1831_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
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
Require Import thm89994_spec.
Lemma lem283488 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem283489 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem283490 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem283489 t1) (@lem283488 t1)). Qed.
Lemma lem283491 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem283490 t1 t2). Qed.
Lemma lem283492 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem283493 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem283492 t1 t2) (@lem283491 t1 t2)). Qed.
Lemma lem283494 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem283493 t1 t2 t3). Qed.
Lemma lem283495 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem283496 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem283495 t1 t2 t3) (@lem283494 t1 t2 t3)). Qed.
Lemma lem283497 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem283496 t1 t2 t3)). Qed.
Lemma lem283498 : term7.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem283499 : term8.
Proof. exact (proj2 (@lem283498)). Qed.
Lemma lem283500 : term9.
Proof. exact (proj2 (@lem283499)). Qed.
Lemma lem283501 (m : nat) : term10 m.
Proof. exact (@lem283500 m). Qed.
Lemma lem283502 (m : nat) : (term10 m) = (term11 m).
Proof. exact (eq_refl (term10 m)). Qed.
Lemma lem283503 (m : nat) : term11 m.
Proof. exact (EQ_MP (@lem283502 m) (@lem283501 m)). Qed.
Lemma lem283504 (m : nat) (n : nat) : term12 m n.
Proof. exact (@lem283503 m n). Qed.
Lemma lem283505 (m : nat) (n : nat) : (term12 m n) = ((term13 m n) = (term14 m n)).
Proof. exact (eq_refl (term12 m n)). Qed.
Lemma lem283514 : term15.
Proof. exact (proj1 (@lem283498)). Qed.
Lemma lem283515 (m : nat) : term16 m.
Proof. exact (@lem283514 m). Qed.
Lemma lem283516 (m : nat) : (term16 m) = ((term17 m) = m).
Proof. exact (eq_refl (term16 m)). Qed.
Lemma lem283522 : term7.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem283523 : term8.
Proof. exact (proj2 (@lem283522)). Qed.
Lemma lem283524 : term9.
Proof. exact (proj2 (@lem283523)). Qed.
Lemma lem283525 (m : nat) : term10 m.
Proof. exact (@lem283524 m). Qed.
Lemma lem283526 (m : nat) : (term10 m) = (term11 m).
Proof. exact (eq_refl (term10 m)). Qed.
Lemma lem283527 (m : nat) : term11 m.
Proof. exact (EQ_MP (@lem283526 m) (@lem283525 m)). Qed.
Lemma lem283528 (m : nat) (n : nat) : term12 m n.
Proof. exact (@lem283527 m n). Qed.
Lemma lem283529 (m : nat) (n : nat) : (term12 m n) = ((term13 m n) = (term14 m n)).
Proof. exact (eq_refl (term12 m n)). Qed.
Lemma lem283546 {A : Type'} (a : A) : term18 A a.
Proof. exact (@lem4363 A a). Qed.
Lemma lem283547 {A : Type'} (a : A) : (term18 A a) = (term19 A a).
Proof. exact (eq_refl (term18 A a)). Qed.
Lemma lem283548 {A : Type'} (a : A) : term19 A a.
Proof. exact (EQ_MP (@lem283547 A a) (@lem283546 A a)). Qed.
Lemma lem283549 {A : Type'} (a : A) : (term19 A a) = ((term19 A a) = True).
Proof. exact (@lem7 (term19 A a)). Qed.
Lemma lem283551 {A : Type'} (P : A -> Prop) : term20 A P.
Proof. exact (@lem6754 A P). Qed.
Lemma lem283552 {A : Type'} (P : A -> Prop) : (term20 A P) = (term21 A P).
Proof. exact (eq_refl (term20 A P)). Qed.
Lemma lem283553 {A : Type'} (P : A -> Prop) : term21 A P.
Proof. exact (EQ_MP (@lem283552 A P) (@lem283551 A P)). Qed.
Lemma lem283554 {A : Type'} (P : A -> Prop) (Q : Prop) : term22 A P Q.
Proof. exact (@lem283553 A P Q). Qed.
Lemma lem283555 {A : Type'} (P : A -> Prop) (Q : Prop) : (term22 A P Q) = ((term23 A P Q) = (term24 A P Q)).
Proof. exact (eq_refl (term22 A P Q)). Qed.
Lemma lem283557 {A B : Type'} (P : type1413 A B) : term25 A B P.
Proof. exact (@lem4792 A B P). Qed.
Lemma lem283558 {A B : Type'} (P : type1413 A B) : (term25 A B P) = ((term26 A B P) = (term27 A B P)).
Proof. exact (eq_refl (term25 A B P)). Qed.
Lemma lem283560 {A : Type'} (P : A -> Prop) : term28 A P.
Proof. exact (@lem6644 A P). Qed.
Lemma lem283561 {A : Type'} (P : A -> Prop) : (term28 A P) = (term29 A P).
Proof. exact (eq_refl (term28 A P)). Qed.
Lemma lem283562 {A : Type'} (P : A -> Prop) : term29 A P.
Proof. exact (EQ_MP (@lem283561 A P) (@lem283560 A P)). Qed.
Lemma lem283563 {A : Type'} (P : A -> Prop) (Q : Prop) : term30 A P Q.
Proof. exact (@lem283562 A P Q). Qed.
Lemma lem283564 {A : Type'} (P : A -> Prop) (Q : Prop) : (term30 A P Q) = ((term24 A P Q) = (term23 A P Q)).
Proof. exact (eq_refl (term30 A P Q)). Qed.
Lemma lem283566 (m : nat) : term31 m.
Proof. exact (@lem100361 m). Qed.
Lemma lem283567 (m : nat) : (term31 m) = (term32 m).
Proof. exact (eq_refl (term31 m)). Qed.
Lemma lem283568 (m : nat) : term32 m.
Proof. exact (EQ_MP (@lem283567 m) (@lem283566 m)). Qed.
Lemma lem283569 (m : nat) (n : nat) : term33 m n.
Proof. exact (@lem283568 m n). Qed.
Lemma lem283570 (n : nat) (m : nat) : (term33 m n) = ((Peano.lt m n) = (term34 n m)).
Proof. exact (eq_refl (term33 m n)). Qed.
Lemma lem283572 (R : type1605) (h1 : term35 R) : term35 R.
Proof. exact (h1). Qed.
Lemma lem283573 : term36.
Proof. exact (proj2 (@lem89994)). Qed.
Lemma lem283574 (m : nat) : term37 m.
Proof. exact (@lem283573 m). Qed.
Lemma lem283575 (m : nat) : (term37 m) = (term38 m).
Proof. exact (eq_refl (term37 m)). Qed.
Lemma lem283576 (m : nat) : term38 m.
Proof. exact (EQ_MP (@lem283575 m) (@lem283574 m)). Qed.
Lemma lem283577 (m : nat) (n : nat) : term39 m n.
Proof. exact (@lem283576 m n). Qed.
Lemma lem283578 (m : nat) (n : nat) : (term39 m n) = ((term40 m n) = (term41 m n)).
Proof. exact (eq_refl (term39 m n)). Qed.
Lemma lem283631 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term42 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem283632 (p : Prop) (q : Prop) (p' : Prop) : term43 p q p'.
Proof. exact (fun q' : Prop => @lem283631 p q p' q'). Qed.
Lemma lem283633 (p : Prop) (q : Prop) : term44 p q.
Proof. exact (fun p' : Prop => @lem283632 p q p'). Qed.
Lemma lem283634 (R : type1605) : term45 R.
Proof. exact (@lem283633 (term46 R) (term47 R)). Qed.
Lemma lem283635 (R : type1605) (p' : Prop) : term48 R p'.
Proof. exact (@lem283634 R p'). Qed.
Lemma lem283636 (R : type1605) (p' : Prop) : (term48 R p') = (term49 R p').
Proof. exact (eq_refl (term48 R p')). Qed.
Lemma lem283637 (R : type1605) (p' : Prop) : term49 R p'.
Proof. exact (EQ_MP (@lem283636 R p') (@lem283635 R p')). Qed.
Lemma lem283638 (R : type1605) (p' : Prop) (q' : Prop) : term50 R p' q'.
Proof. exact (@lem283637 R p' q'). Qed.
Lemma lem283639 (R : type1605) (p' : Prop) (q' : Prop) : (term50 R p' q') = (term51 R p' q').
Proof. exact (eq_refl (term50 R p' q')). Qed.
Lemma lem283640 (R : type1605) (p' : Prop) (q' : Prop) : term51 R p' q'.
Proof. exact (EQ_MP (@lem283639 R p' q') (@lem283638 R p' q')). Qed.
Lemma lem283874 (R : type1605) : (term46 R) = (term46 R).
Proof. exact (eq_refl (term46 R)). Qed.
Lemma lem283875 (R : type1605) (q' : Prop) : term52 R q'.
Proof. exact (@lem283640 R (term46 R) q'). Qed.
Lemma lem283876 (R : type1605) (q' : Prop) : term53 R q'.
Proof. exact (@lem283875 R q' (@lem283874 R)). Qed.
Lemma lem283877 (R : type1605) (h1 : term46 R) : term46 R.
Proof. exact (h1). Qed.
Lemma lem283878 (m : nat) (R : type1605) (h1 : term46 R) : term54 R m.
Proof. exact (@lem283877 R h1 m). Qed.
Lemma lem283879 (R : type1605) (m : nat) : (term54 R m) = (term55 R m).
Proof. exact (eq_refl (term54 R m)). Qed.
Lemma lem283880 (m : nat) (R : type1605) (h1 : term46 R) : term55 R m.
Proof. exact (EQ_MP (@lem283879 R m) (@lem283878 m R h1)). Qed.
Lemma lem283881 (m : nat) (n : nat) (R : type1605) (h1 : term46 R) : term56 R m n.
Proof. exact (@lem283880 m R h1 n). Qed.
Lemma lem283882 (R : type1605) (m : nat) (n : nat) : (term56 R m n) = (term57 R m n).
Proof. exact (eq_refl (term56 R m n)). Qed.
Lemma lem283883 (m : nat) (n : nat) (R : type1605) (h1 : term46 R) : term57 R m n.
Proof. exact (EQ_MP (@lem283882 R m n) (@lem283881 m n R h1)). Qed.
Lemma lem283884 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (h1). Qed.
Lemma lem283885 (R : type1605) (m : nat) (n : nat) (h1 : term46 R) (h2 : Peano.lt m n) : R m n.
Proof. exact (@lem283883 m n R h1 (@lem283884 m n h2)). Qed.
Lemma lem283886 (R : type1605) (m : nat) (n : nat) : (R m n) = ((R m n) = True).
Proof. exact (@lem7 (R m n)). Qed.
Lemma lem283887 (R : type1605) (m : nat) (n : nat) (h1 : term46 R) (h2 : Peano.lt m n) : (R m n) = True.
Proof. exact (EQ_MP (@lem283886 R m n) (@lem283885 R m n h1 h2)). Qed.
Lemma lem284065 (m : nat) (n : nat) (R : type1605) (h1 : term46 R) : term58 R m n.
Proof. exact (fun h0 : Peano.lt m n => @lem283887 R m n h1 h0). Qed.
Lemma lem284066 (n : nat) (R : type1605) (h1 : term46 R) : term59 R n.
Proof. exact (@lem284065 n (S n) R h1). Qed.
Lemma lem284068 (m : nat) (n : nat) : (term40 m n) = (term41 m n).
Proof. exact (EQ_MP (@lem283578 m n) (@lem283577 m n)). Qed.
Lemma lem284069 (n : nat) : (term60 n) = (term61 n).
Proof. exact (@lem284068 n n). Qed.
Lemma lem284073 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem284074 (x : nat) : (x = x) = True.
Proof. exact (@lem284073 nat x). Qed.
Lemma lem284075 (n : nat) : (n = n) = True.
Proof. exact (@lem284074 n). Qed.
Lemma lem284076 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem284077 (n : nat) : (term62 n) = (or True).
Proof. exact (MK_COMB (@lem284076) (@lem284075 n)). Qed.
Lemma lem284078 (n : nat) : (Peano.lt n n) = (Peano.lt n n).
Proof. exact (eq_refl (Peano.lt n n)). Qed.
Lemma lem284079 (n : nat) : (term61 n) = (term63 n).
Proof. exact (MK_COMB (@lem284077 n) (@lem284078 n)). Qed.
Lemma lem284081 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem284082 (n : nat) : (term63 n) = True.
Proof. exact (@lem284081 (Peano.lt n n)). Qed.
Lemma lem284083 (n : nat) : (term61 n) = True.
Proof. exact (TRANS (@lem284079 n) (@lem284082 n)). Qed.
Lemma lem284084 (n : nat) : (term60 n) = True.
Proof. exact (TRANS (@lem284069 n) (@lem284083 n)). Qed.
Lemma lem284085 (n : nat) : True = (term60 n).
Proof. exact (SYM (@lem284084 n)). Qed.
Lemma lem284086 (n : nat) : term60 n.
Proof. exact (EQ_MP (@lem284085 n) (@lem0)). Qed.
Lemma lem284087 (n : nat) (R : type1605) (h1 : term46 R) : (term64 R n) = True.
Proof. exact (@lem284066 n R h1 (@lem284086 n)). Qed.
Lemma lem284088 (R : type1605) (h1 : term46 R) : (term65 R) = term66.
Proof. exact (fun_ext (fun n : nat => @lem284087 n R h1)). Qed.
Lemma lem284089 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem284090 (R : type1605) (h1 : term46 R) : (term47 R) = term67.
Proof. exact (MK_COMB (@lem284089) (@lem284088 R h1)). Qed.
Lemma lem284092 {A : Type'} (t : Prop) : (term68 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem284093 (t : Prop) : (term69 t) = t.
Proof. exact (@lem284092 nat t). Qed.
Lemma lem284094 : term67 = True.
Proof. exact (@lem284093 True). Qed.
Lemma lem284095 (R : type1605) (h1 : term46 R) : (term47 R) = True.
Proof. exact (TRANS (@lem284090 R h1) (@lem284094)). Qed.
Lemma lem284096 (R : type1605) : term70 R.
Proof. exact (fun h0 : term46 R => @lem284095 R h0). Qed.
Lemma lem284097 (R : type1605) : term71 R.
Proof. exact (@lem283876 R True). Qed.
Lemma lem284098 (R : type1605) : (term72 R) = (term73 R).
Proof. exact (@lem284097 R (@lem284096 R)). Qed.
Lemma lem284100 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem284101 (R : type1605) : (term73 R) = True.
Proof. exact (@lem284100 (term46 R)). Qed.
Lemma lem284102 (R : type1605) : (term72 R) = True.
Proof. exact (TRANS (@lem284098 R) (@lem284101 R)). Qed.
Lemma lem284103 (R : type1605) : True = (term72 R).
Proof. exact (SYM (@lem284102 R)). Qed.
Lemma lem284104 (R : type1605) : term72 R.
Proof. exact (EQ_MP (@lem284103 R) (@lem0)). Qed.
Lemma lem284864 (R : type1605) (h1 : term47 R) : term47 R.
Proof. exact (h1). Qed.
Lemma lem284876 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term42 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem284877 (p : Prop) (q : Prop) (p' : Prop) : term43 p q p'.
Proof. exact (fun q' : Prop => @lem284876 p q p' q'). Qed.
Lemma lem284878 (p : Prop) (q : Prop) : term44 p q.
Proof. exact (fun p' : Prop => @lem284877 p q p'). Qed.
Lemma lem284879 (R : type1605) (m : nat) (n : nat) : term74 R m n.
Proof. exact (@lem284878 (Peano.lt m n) (R m n)). Qed.
Lemma lem284880 (R : type1605) (m : nat) (n : nat) (p' : Prop) : term75 R m n p'.
Proof. exact (@lem284879 R m n p'). Qed.
Lemma lem284881 (R : type1605) (m : nat) (n : nat) (p' : Prop) : (term75 R m n p') = (term76 R m n p').
Proof. exact (eq_refl (term75 R m n p')). Qed.
Lemma lem284882 (R : type1605) (m : nat) (n : nat) (p' : Prop) : term76 R m n p'.
Proof. exact (EQ_MP (@lem284881 R m n p') (@lem284880 R m n p')). Qed.
Lemma lem284883 (R : type1605) (m : nat) (n : nat) (p' : Prop) (q' : Prop) : term77 R m n p' q'.
Proof. exact (@lem284882 R m n p' q'). Qed.
Lemma lem284884 (R : type1605) (m : nat) (n : nat) (p' : Prop) (q' : Prop) : (term77 R m n p' q') = (term78 R m n p' q').
Proof. exact (eq_refl (term77 R m n p' q')). Qed.
Lemma lem284885 (R : type1605) (m : nat) (n : nat) (p' : Prop) (q' : Prop) : term78 R m n p' q'.
Proof. exact (EQ_MP (@lem284884 R m n p' q') (@lem284883 R m n p' q')). Qed.
Lemma lem284887 (n : nat) (m : nat) : (Peano.lt m n) = (term34 n m).
Proof. exact (EQ_MP (@lem283570 n m) (@lem283569 m n)). Qed.
Lemma lem284894 (R : type1605) (n : nat) (m : nat) (q' : Prop) : term79 R n m q'.
Proof. exact (@lem284885 R m n (term34 n m) q'). Qed.
Lemma lem284895 (R : type1605) (n : nat) (m : nat) (q' : Prop) : term80 R n m q'.
Proof. exact (@lem284894 R n m q' (@lem284887 n m)). Qed.
Lemma lem284899 (R : type1605) (m : nat) (n : nat) : (R m n) = (R m n).
Proof. exact (eq_refl (R m n)). Qed.
Lemma lem284900 (R : type1605) (m : nat) (n : nat) : term81 R m n.
Proof. exact (fun h0 : term34 n m => @lem284899 R m n). Qed.
Lemma lem284901 (R : type1605) (m : nat) (n : nat) : term82 R m n.
Proof. exact (@lem284895 R n m (R m n)). Qed.
Lemma lem284902 (R : type1605) (m : nat) (n : nat) : (term57 R m n) = (term83 R m n).
Proof. exact (@lem284901 R m n (@lem284900 R m n)). Qed.
Lemma lem284904 {A : Type'} (P : A -> Prop) (Q : Prop) : (term24 A P Q) = (term23 A P Q).
Proof. exact (EQ_MP (@lem283564 A P Q) (@lem283563 A P Q)). Qed.
Lemma lem284905 (P : nat -> Prop) (Q : Prop) : (term84 P Q) = (term85 P Q).
Proof. exact (@lem284904 nat P Q). Qed.
Lemma lem284906 (R : type1605) (m : nat) (n : nat) : (term86 R m n) = (term87 R m n).
Proof. exact (@lem284905 (term88 n m) (R m n)). Qed.
Lemma lem284907 (n : nat) (m : nat) (d : nat) : (term89 n m d) = (n = (term13 m d)).
Proof. exact (eq_refl (term89 n m d)). Qed.
Lemma lem284908 (n : nat) (m : nat) : (term90 n m) = (term88 n m).
Proof. exact (fun_ext (fun d : nat => @lem284907 n m d)). Qed.
Lemma lem284909 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem284910 (n : nat) (m : nat) : (term91 n m) = (term34 n m).
Proof. exact (MK_COMB (@lem284909) (@lem284908 n m)). Qed.
Lemma lem284911 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem284912 (n : nat) (m : nat) : (term92 n m) = (term93 n m).
Proof. exact (MK_COMB (@lem284911) (@lem284910 n m)). Qed.
Lemma lem284913 (R : type1605) (m : nat) (n : nat) : (R m n) = (R m n).
Proof. exact (eq_refl (R m n)). Qed.
Lemma lem284914 (R : type1605) (m : nat) (n : nat) : (term86 R m n) = (term83 R m n).
Proof. exact (MK_COMB (@lem284912 n m) (@lem284913 R m n)). Qed.
Lemma lem284915 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem284916 (R : type1605) (m : nat) (n : nat) : (term94 R m n) = (term95 R m n).
Proof. exact (MK_COMB (@lem284915) (@lem284914 R m n)). Qed.
Lemma lem284917 (n : nat) (m : nat) (d : nat) : (term89 n m d) = (n = (term13 m d)).
Proof. exact (eq_refl (term89 n m d)). Qed.
Lemma lem284918 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem284919 (n : nat) (m : nat) (d : nat) : (term96 n m d) = (term97 n m d).
Proof. exact (MK_COMB (@lem284918) (@lem284917 n m d)). Qed.
Lemma lem284920 (R : type1605) (m : nat) (n : nat) : (R m n) = (R m n).
Proof. exact (eq_refl (R m n)). Qed.
Lemma lem284921 (d : nat) (R : type1605) (m : nat) (n : nat) : (term98 d R m n) = (term99 d R m n).
Proof. exact (MK_COMB (@lem284919 n m d) (@lem284920 R m n)). Qed.
Lemma lem284922 (R : type1605) (m : nat) (n : nat) : (term100 R m n) = (term101 R m n).
Proof. exact (fun_ext (fun d : nat => @lem284921 d R m n)). Qed.
Lemma lem284923 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem284924 (R : type1605) (m : nat) (n : nat) : (term87 R m n) = (term102 R m n).
Proof. exact (MK_COMB (@lem284923) (@lem284922 R m n)). Qed.
Lemma lem284925 (R : type1605) (m : nat) (n : nat) : ((term86 R m n) = (term87 R m n)) = ((term83 R m n) = (term102 R m n)).
Proof. exact (MK_COMB (@lem284916 R m n) (@lem284924 R m n)). Qed.
Lemma lem284926 (R : type1605) (m : nat) (n : nat) : (term83 R m n) = (term102 R m n).
Proof. exact (EQ_MP (@lem284925 R m n) (@lem284906 R m n)). Qed.
Lemma lem284936 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term42 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem284937 (p : Prop) (q : Prop) (p' : Prop) : term43 p q p'.
Proof. exact (fun q' : Prop => @lem284936 p q p' q'). Qed.
Lemma lem284938 (p : Prop) (q : Prop) : term44 p q.
Proof. exact (fun p' : Prop => @lem284937 p q p'). Qed.
Lemma lem284939 (d : nat) (R : type1605) (m : nat) (n : nat) : term103 d R m n.
Proof. exact (@lem284938 (n = (term13 m d)) (R m n)). Qed.
Lemma lem284940 (d : nat) (R : type1605) (m : nat) (n : nat) (p' : Prop) : term104 d R m n p'.
Proof. exact (@lem284939 d R m n p'). Qed.
Lemma lem284941 (d : nat) (R : type1605) (m : nat) (n : nat) (p' : Prop) : (term104 d R m n p') = (term105 d R m n p').
Proof. exact (eq_refl (term104 d R m n p')). Qed.
Lemma lem284942 (d : nat) (R : type1605) (m : nat) (n : nat) (p' : Prop) : term105 d R m n p'.
Proof. exact (EQ_MP (@lem284941 d R m n p') (@lem284940 d R m n p')). Qed.
Lemma lem284943 (d : nat) (R : type1605) (m : nat) (n : nat) (p' : Prop) (q' : Prop) : term106 d R m n p' q'.
Proof. exact (@lem284942 d R m n p' q'). Qed.
Lemma lem284944 (d : nat) (R : type1605) (m : nat) (n : nat) (p' : Prop) (q' : Prop) : (term106 d R m n p' q') = (term107 d R m n p' q').
Proof. exact (eq_refl (term106 d R m n p' q')). Qed.
Lemma lem284945 (d : nat) (R : type1605) (m : nat) (n : nat) (p' : Prop) (q' : Prop) : term107 d R m n p' q'.
Proof. exact (EQ_MP (@lem284944 d R m n p' q') (@lem284943 d R m n p' q')). Qed.
Lemma lem284948 (n : nat) (m : nat) (d : nat) : (n = (term13 m d)) = (n = (term13 m d)).
Proof. exact (eq_refl (n = (term13 m d))). Qed.
Lemma lem284949 (R : type1605) (n : nat) (m : nat) (d : nat) (q' : Prop) : term108 R n m d q'.
Proof. exact (@lem284945 d R m n (n = (term13 m d)) q'). Qed.
Lemma lem284950 (R : type1605) (n : nat) (m : nat) (d : nat) (q' : Prop) : term109 R n m d q'.
Proof. exact (@lem284949 R n m d q' (@lem284948 n m d)). Qed.
Lemma lem284953 (n : nat) (m : nat) (d : nat) (h1 : n = (term13 m d)) : n = (term13 m d).
Proof. exact (h1). Qed.
Lemma lem284954 (R : type1605) (m : nat) : (R m) = (R m).
Proof. exact (eq_refl (R m)). Qed.
Lemma lem284955 (R : type1605) (n : nat) (m : nat) (d : nat) (h1 : n = (term13 m d)) : (R m n) = (term110 R m d).
Proof. exact (MK_COMB (@lem284954 R m) (@lem284953 n m d h1)). Qed.
Lemma lem284956 (n : nat) (R : type1605) (m : nat) (d : nat) : term111 n R m d.
Proof. exact (fun h0 : n = (term13 m d) => @lem284955 R n m d h0). Qed.
Lemma lem284957 (n : nat) (R : type1605) (m : nat) (d : nat) : term112 n R m d.
Proof. exact (@lem284950 R n m d (term110 R m d)). Qed.
Lemma lem284958 (n : nat) (R : type1605) (m : nat) (d : nat) : (term99 d R m n) = (term113 n R m d).
Proof. exact (@lem284957 n R m d (@lem284956 n R m d)). Qed.
Lemma lem284986 (n : nat) (R : type1605) (m : nat) : (term101 R m n) = (term114 n R m).
Proof. exact (fun_ext (fun d : nat => @lem284958 n R m d)). Qed.
Lemma lem285014 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem285015 (n : nat) (R : type1605) (m : nat) : (term102 R m n) = (term115 n R m).
Proof. exact (MK_COMB (@lem285014) (@lem284986 n R m)). Qed.
Lemma lem285047 (n : nat) (R : type1605) (m : nat) : (term83 R m n) = (term115 n R m).
Proof. exact (TRANS (@lem284926 R m n) (@lem285015 n R m)). Qed.
Lemma lem285048 (n : nat) (R : type1605) (m : nat) : (term57 R m n) = (term115 n R m).
Proof. exact (TRANS (@lem284902 R m n) (@lem285047 n R m)). Qed.
Lemma lem285049 (R : type1605) (m : nat) : (term116 R m) = (term117 R m).
Proof. exact (fun_ext (fun n : nat => @lem285048 n R m)). Qed.
Lemma lem285081 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem285082 (R : type1605) (m : nat) : (term55 R m) = (term118 R m).
Proof. exact (MK_COMB (@lem285081) (@lem285049 R m)). Qed.
Lemma lem285118 (R : type1605) : (term119 R) = (term120 R).
Proof. exact (fun_ext (fun m : nat => @lem285082 R m)). Qed.
Lemma lem285154 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem285155 (R : type1605) : (term46 R) = (term121 R).
Proof. exact (MK_COMB (@lem285154) (@lem285118 R)). Qed.
Lemma lem285195 (R : type1605) : (term121 R) = (term46 R).
Proof. exact (SYM (@lem285155 R)). Qed.
Lemma lem285197 {A B : Type'} (P : type1413 A B) : (term26 A B P) = (term27 A B P).
Proof. exact (EQ_MP (@lem283558 A B P) (@lem283557 A B P)). Qed.
Lemma lem285198 (P : type1605) : (term122 P) = (term123 P).
Proof. exact (@lem285197 nat nat P). Qed.
Lemma lem285199 (R : type1605) (m : nat) : (term124 R m) = (term125 R m).
Proof. exact (@lem285198 (term126 R m)). Qed.
Lemma lem285200 (n : nat) (R : type1605) (m : nat) : (term127 R m n) = (term114 n R m).
Proof. exact (eq_refl (term127 R m n)). Qed.
Lemma lem285201 (d : nat) : d = d.
Proof. exact (eq_refl d). Qed.
Lemma lem285202 (n : nat) (R : type1605) (m : nat) (d : nat) : (term128 R m n d) = (term129 n R m d).
Proof. exact (MK_COMB (@lem285200 n R m) (@lem285201 d)). Qed.
Lemma lem285203 (n : nat) (R : type1605) (m : nat) (d : nat) : (term129 n R m d) = (term113 n R m d).
Proof. exact (eq_refl (term129 n R m d)). Qed.
Lemma lem285204 (n : nat) (R : type1605) (m : nat) (d : nat) : (term128 R m n d) = (term113 n R m d).
Proof. exact (TRANS (@lem285202 n R m d) (@lem285203 n R m d)). Qed.
Lemma lem285205 (n : nat) (R : type1605) (m : nat) : (term130 R m n) = (term114 n R m).
Proof. exact (fun_ext (fun d : nat => @lem285204 n R m d)). Qed.
Lemma lem285206 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem285207 (n : nat) (R : type1605) (m : nat) : (term131 R m n) = (term115 n R m).
Proof. exact (MK_COMB (@lem285206) (@lem285205 n R m)). Qed.
Lemma lem285208 (R : type1605) (m : nat) : (term132 R m) = (term117 R m).
Proof. exact (fun_ext (fun n : nat => @lem285207 n R m)). Qed.
Lemma lem285209 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem285210 (R : type1605) (m : nat) : (term124 R m) = (term118 R m).
Proof. exact (MK_COMB (@lem285209) (@lem285208 R m)). Qed.
Lemma lem285211 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem285212 (R : type1605) (m : nat) : (term133 R m) = (term134 R m).
Proof. exact (MK_COMB (@lem285211) (@lem285210 R m)). Qed.
Lemma lem285213 (n : nat) (R : type1605) (m : nat) : (term127 R m n) = (term114 n R m).
Proof. exact (eq_refl (term127 R m n)). Qed.
Lemma lem285214 (d : nat) : d = d.
Proof. exact (eq_refl d). Qed.
Lemma lem285215 (n : nat) (R : type1605) (m : nat) (d : nat) : (term128 R m n d) = (term129 n R m d).
Proof. exact (MK_COMB (@lem285213 n R m) (@lem285214 d)). Qed.
Lemma lem285216 (n : nat) (R : type1605) (m : nat) (d : nat) : (term129 n R m d) = (term113 n R m d).
Proof. exact (eq_refl (term129 n R m d)). Qed.
Lemma lem285217 (n : nat) (R : type1605) (m : nat) (d : nat) : (term128 R m n d) = (term113 n R m d).
Proof. exact (TRANS (@lem285215 n R m d) (@lem285216 n R m d)). Qed.
Lemma lem285218 (R : type1605) (m : nat) (d : nat) : (term135 R m d) = (term136 R m d).
Proof. exact (fun_ext (fun n : nat => @lem285217 n R m d)). Qed.
Lemma lem285219 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem285220 (R : type1605) (m : nat) (d : nat) : (term137 R m d) = (term138 R m d).
Proof. exact (MK_COMB (@lem285219) (@lem285218 R m d)). Qed.
Lemma lem285221 (R : type1605) (m : nat) : (term139 R m) = (term140 R m).
Proof. exact (fun_ext (fun d : nat => @lem285220 R m d)). Qed.
Lemma lem285222 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem285223 (R : type1605) (m : nat) : (term125 R m) = (term141 R m).
Proof. exact (MK_COMB (@lem285222) (@lem285221 R m)). Qed.
Lemma lem285224 (R : type1605) (m : nat) : ((term124 R m) = (term125 R m)) = ((term118 R m) = (term141 R m)).
Proof. exact (MK_COMB (@lem285212 R m) (@lem285223 R m)). Qed.
Lemma lem285225 (R : type1605) (m : nat) : (term118 R m) = (term141 R m).
Proof. exact (EQ_MP (@lem285224 R m) (@lem285199 R m)). Qed.
Lemma lem285226 (R : type1605) (m : nat) : (term141 R m) = (term118 R m).
Proof. exact (SYM (@lem285225 R m)). Qed.
Lemma lem285232 {A : Type'} (P : A -> Prop) (Q : Prop) : (term23 A P Q) = (term24 A P Q).
Proof. exact (EQ_MP (@lem283555 A P Q) (@lem283554 A P Q)). Qed.
Lemma lem285233 (P : nat -> Prop) (Q : Prop) : (term85 P Q) = (term84 P Q).
Proof. exact (@lem285232 nat P Q). Qed.
Lemma lem285234 (R : type1605) (m : nat) (d : nat) : (term142 R m d) = (term143 R m d).
Proof. exact (@lem285233 (term144 m d) (term110 R m d)). Qed.
Lemma lem285235 (n : nat) (m : nat) (d : nat) : (term145 m d n) = (n = (term13 m d)).
Proof. exact (eq_refl (term145 m d n)). Qed.
Lemma lem285236 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem285237 (n : nat) (m : nat) (d : nat) : (term146 m d n) = (term97 n m d).
Proof. exact (MK_COMB (@lem285236) (@lem285235 n m d)). Qed.
Lemma lem285238 (R : type1605) (m : nat) (d : nat) : (term110 R m d) = (term110 R m d).
Proof. exact (eq_refl (term110 R m d)). Qed.
Lemma lem285239 (n : nat) (R : type1605) (m : nat) (d : nat) : (term147 n R m d) = (term113 n R m d).
Proof. exact (MK_COMB (@lem285237 n m d) (@lem285238 R m d)). Qed.
Lemma lem285240 (R : type1605) (m : nat) (d : nat) : (term148 R m d) = (term136 R m d).
Proof. exact (fun_ext (fun n : nat => @lem285239 n R m d)). Qed.
Lemma lem285241 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem285242 (R : type1605) (m : nat) (d : nat) : (term142 R m d) = (term138 R m d).
Proof. exact (MK_COMB (@lem285241) (@lem285240 R m d)). Qed.
Lemma lem285243 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem285244 (R : type1605) (m : nat) (d : nat) : (term149 R m d) = (term150 R m d).
Proof. exact (MK_COMB (@lem285243) (@lem285242 R m d)). Qed.
Lemma lem285245 (n : nat) (m : nat) (d : nat) : (term145 m d n) = (n = (term13 m d)).
Proof. exact (eq_refl (term145 m d n)). Qed.
Lemma lem285246 (m : nat) (d : nat) : (term151 m d) = (term144 m d).
Proof. exact (fun_ext (fun n : nat => @lem285245 n m d)). Qed.
Lemma lem285247 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem285248 (m : nat) (d : nat) : (term152 m d) = (term153 m d).
Proof. exact (MK_COMB (@lem285247) (@lem285246 m d)). Qed.
Lemma lem285249 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem285250 (m : nat) (d : nat) : (term154 m d) = (term155 m d).
Proof. exact (MK_COMB (@lem285249) (@lem285248 m d)). Qed.
Lemma lem285251 (R : type1605) (m : nat) (d : nat) : (term110 R m d) = (term110 R m d).
Proof. exact (eq_refl (term110 R m d)). Qed.
Lemma lem285252 (R : type1605) (m : nat) (d : nat) : (term143 R m d) = (term156 R m d).
Proof. exact (MK_COMB (@lem285250 m d) (@lem285251 R m d)). Qed.
Lemma lem285253 (R : type1605) (m : nat) (d : nat) : ((term142 R m d) = (term143 R m d)) = ((term138 R m d) = (term156 R m d)).
Proof. exact (MK_COMB (@lem285244 R m d) (@lem285252 R m d)). Qed.
Lemma lem285254 (R : type1605) (m : nat) (d : nat) : (term138 R m d) = (term156 R m d).
Proof. exact (EQ_MP (@lem285253 R m d) (@lem285234 R m d)). Qed.
Lemma lem285258 {A : Type'} (a : A) : (term19 A a) = True.
Proof. exact (EQ_MP (@lem283549 A a) (@lem283548 A a)). Qed.
Lemma lem285259 (a : nat) : (term157 a) = True.
Proof. exact (@lem285258 nat a). Qed.
Lemma lem285260 (m : nat) (d : nat) : (term153 m d) = True.
Proof. exact (@lem285259 (term13 m d)). Qed.
Lemma lem285261 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem285262 (m : nat) (d : nat) : (term155 m d) = (imp True).
Proof. exact (MK_COMB (@lem285261) (@lem285260 m d)). Qed.
Lemma lem285264 (m : nat) (n : nat) : (term13 m n) = (term14 m n).
Proof. exact (EQ_MP (@lem283529 m n) (@lem283528 m n)). Qed.
Lemma lem285265 (m : nat) (d : nat) : (term13 m d) = (term14 m d).
Proof. exact (@lem285264 m d). Qed.
Lemma lem285266 (R : type1605) (m : nat) : (R m) = (R m).
Proof. exact (eq_refl (R m)). Qed.
Lemma lem285267 (R : type1605) (m : nat) (d : nat) : (term110 R m d) = (term158 R m d).
Proof. exact (MK_COMB (@lem285266 R m) (@lem285265 m d)). Qed.
Lemma lem285268 (R : type1605) (m : nat) (d : nat) : (term156 R m d) = (term159 R m d).
Proof. exact (MK_COMB (@lem285262 m d) (@lem285267 R m d)). Qed.
Lemma lem285270 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem285271 (R : type1605) (m : nat) (d : nat) : (term159 R m d) = (term158 R m d).
Proof. exact (@lem285270 (term158 R m d)). Qed.
Lemma lem285272 (R : type1605) (m : nat) (d : nat) : (term156 R m d) = (term158 R m d).
Proof. exact (TRANS (@lem285268 R m d) (@lem285271 R m d)). Qed.
Lemma lem285273 (R : type1605) (m : nat) (d : nat) : (term138 R m d) = (term158 R m d).
Proof. exact (TRANS (@lem285254 R m d) (@lem285272 R m d)). Qed.
Lemma lem285274 (R : type1605) (m : nat) : (term140 R m) = (term160 R m).
Proof. exact (fun_ext (fun d : nat => @lem285273 R m d)). Qed.
Lemma lem285275 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem285276 (R : type1605) (m : nat) : (term141 R m) = (term161 R m).
Proof. exact (MK_COMB (@lem285275) (@lem285274 R m)). Qed.
Lemma lem285281 (R : type1605) (m : nat) : (term161 R m) = (term141 R m).
Proof. exact (SYM (@lem285276 R m)). Qed.
Lemma lem285283 (P : nat -> Prop) : term162 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem285284 (R : type1605) (m : nat) : term163 R m.
Proof. exact (@lem285283 (term160 R m)). Qed.
Lemma lem285285 (R : type1605) (m : nat) : (term164 R m) = (term165 R m).
Proof. exact (eq_refl (term164 R m)). Qed.
Lemma lem285286 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem285287 (R : type1605) (m : nat) : (term166 R m) = (term167 R m).
Proof. exact (MK_COMB (@lem285286) (@lem285285 R m)). Qed.
Lemma lem285288 (R : type1605) (m : nat) (d : nat) : (term168 R m d) = (term158 R m d).
Proof. exact (eq_refl (term168 R m d)). Qed.
Lemma lem285289 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem285290 (R : type1605) (m : nat) (d : nat) : (term169 R m d) = (term170 R m d).
Proof. exact (MK_COMB (@lem285289) (@lem285288 R m d)). Qed.
Lemma lem285291 (R : type1605) (m : nat) (d : nat) : (term171 R m d) = (term172 R m d).
Proof. exact (eq_refl (term171 R m d)). Qed.
Lemma lem285292 (R : type1605) (m : nat) (d : nat) : (term173 R m d) = (term174 R m d).
Proof. exact (MK_COMB (@lem285290 R m d) (@lem285291 R m d)). Qed.
Lemma lem285293 (R : type1605) (m : nat) : (term175 R m) = (term176 R m).
Proof. exact (fun_ext (fun d : nat => @lem285292 R m d)). Qed.
Lemma lem285294 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem285295 (R : type1605) (m : nat) : (term177 R m) = (term178 R m).
Proof. exact (MK_COMB (@lem285294) (@lem285293 R m)). Qed.
Lemma lem285296 (R : type1605) (m : nat) : (term179 R m) = (term180 R m).
Proof. exact (MK_COMB (@lem285287 R m) (@lem285295 R m)). Qed.
Lemma lem285297 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem285298 (R : type1605) (m : nat) : (term181 R m) = (term182 R m).
Proof. exact (MK_COMB (@lem285297) (@lem285296 R m)). Qed.
Lemma lem285299 (R : type1605) (m : nat) (d : nat) : (term168 R m d) = (term158 R m d).
Proof. exact (eq_refl (term168 R m d)). Qed.
Lemma lem285300 (R : type1605) (m : nat) : (term183 R m) = (term160 R m).
Proof. exact (fun_ext (fun d : nat => @lem285299 R m d)). Qed.
Lemma lem285301 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem285302 (R : type1605) (m : nat) : (term184 R m) = (term161 R m).
Proof. exact (MK_COMB (@lem285301) (@lem285300 R m)). Qed.
Lemma lem285303 (R : type1605) (m : nat) : (term163 R m) = (term185 R m).
Proof. exact (MK_COMB (@lem285298 R m) (@lem285302 R m)). Qed.
Lemma lem285304 (R : type1605) (m : nat) : term185 R m.
Proof. exact (EQ_MP (@lem285303 R m) (@lem285284 R m)). Qed.
Lemma lem285305 (R : type1605) (m : nat) (d : nat) (h1 : term158 R m d) : term158 R m d.
Proof. exact (h1). Qed.
Lemma lem285307 (m : nat) : (term17 m) = m.
Proof. exact (EQ_MP (@lem283516 m) (@lem283515 m)). Qed.
Lemma lem285308 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem285309 (m : nat) : (term186 m) = (S m).
Proof. exact (MK_COMB (@lem285308) (@lem285307 m)). Qed.
Lemma lem285310 (R : type1605) (m : nat) : (R m) = (R m).
Proof. exact (eq_refl (R m)). Qed.
Lemma lem285311 (R : type1605) (m : nat) : (term165 R m) = (term64 R m).
Proof. exact (MK_COMB (@lem285310 R m) (@lem285309 m)). Qed.
Lemma lem285312 (R : type1605) (m : nat) : (term64 R m) = (term165 R m).
Proof. exact (SYM (@lem285311 R m)). Qed.
Lemma lem285314 (m : nat) (n : nat) : (term13 m n) = (term14 m n).
Proof. exact (EQ_MP (@lem283505 m n) (@lem283504 m n)). Qed.
Lemma lem285315 (m : nat) (d : nat) : (term13 m d) = (term14 m d).
Proof. exact (@lem285314 m d). Qed.
Lemma lem285316 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem285317 (m : nat) (d : nat) : (term187 m d) = (term188 m d).
Proof. exact (MK_COMB (@lem285316) (@lem285315 m d)). Qed.
Lemma lem285318 (R : type1605) (m : nat) : (R m) = (R m).
Proof. exact (eq_refl (R m)). Qed.
Lemma lem285319 (R : type1605) (m : nat) (d : nat) : (term172 R m d) = (term189 R m d).
Proof. exact (MK_COMB (@lem285318 R m) (@lem285317 m d)). Qed.
Lemma lem285320 (R : type1605) (m : nat) (d : nat) : (term189 R m d) = (term172 R m d).
Proof. exact (SYM (@lem285319 R m d)). Qed.
Lemma lem285322 (p : Prop) : p = (term190 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem285323 (R : type1605) (m : nat) : (term64 R m) = (term191 R m).
Proof. exact (@lem285322 (term64 R m)). Qed.
Lemma lem285324 (R : type1605) (m : nat) : (term191 R m) = (term64 R m).
Proof. exact (SYM (@lem285323 R m)). Qed.
Lemma lem285325 (R : type1605) (m : nat) (h1 : term192 R m) : term192 R m.
Proof. exact (h1). Qed.
Lemma lem285328 (R : type1605) (m : nat) (h1 : term193 R m) : term193 R m.
Proof. exact (h1). Qed.
Lemma lem285329 (R : type1605) (m : nat) : term194 R m.
Proof. exact (fun h0 : term193 R m => @lem285328 R m h0). Qed.
Lemma lem285330 (R : type1605) (m : nat) (h1 : term194 R m) : term194 R m.
Proof. exact (h1). Qed.
Lemma lem285331 (R : type1605) (m : nat) (h1 : term193 R m) : term193 R m.
Proof. exact (h1). Qed.
Lemma lem285332 (R : type1605) (m : nat) (h1 : term193 R m) (h2 : term194 R m) : term193 R m.
Proof. exact (@lem285330 R m h2 (@lem285331 R m h1)). Qed.
Lemma lem285333 (R : type1605) (m : nat) (h1 : term193 R m) : term195 R m.
Proof. exact (fun h0 : term194 R m => @lem285332 R m h1 h0). Qed.
Lemma lem285334 (R : type1605) (m : nat) (h1 : term194 R m) : term194 R m.
Proof. exact (h1). Qed.
Lemma lem285335 (R : type1605) (m : nat) (h1 : term193 R m) (h2 : term194 R m) : term193 R m.
Proof. exact (@lem285333 R m h1 (@lem285334 R m h2)). Qed.
Lemma lem285336 (R : type1605) (m : nat) (h1 : term194 R m) : term194 R m.
Proof. exact (fun h0 : term193 R m => @lem285335 R m h0 h1). Qed.
Lemma lem285337 (R : type1605) (m : nat) : term196 R m.
Proof. exact (fun h0 : term194 R m => @lem285336 R m h0). Qed.
Lemma lem285340 (R : type1605) (m : nat) : term194 R m.
Proof. exact (@lem285337 R m (@lem285329 R m)). Qed.
Lemma lem285374 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem285375 (R : type1605) (m : nat) : (term191 R m) = (term197 R m).
Proof. exact (@lem285374 (term192 R m)). Qed.
Lemma lem285377 (t : Prop) : (term198 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem285378 (R : type1605) (m : nat) : (term197 R m) = (term64 R m).
Proof. exact (@lem285377 (term64 R m)). Qed.
Lemma lem285379 (R : type1605) (m : nat) : (term191 R m) = (term64 R m).
Proof. exact (TRANS (@lem285375 R m) (@lem285378 R m)). Qed.
Lemma lem285380 (R : type1605) : (term199 R) = (term199 R).
Proof. exact (eq_refl (term199 R)). Qed.
Lemma lem285381 (R : type1605) (m : nat) : (term200 R m) = (term201 R m).
Proof. exact (MK_COMB (@lem285380 R) (@lem285379 R m)). Qed.
Lemma lem285384 (R : type1605) : (term202 R) = (term202 R).
Proof. exact (eq_refl (term202 R)). Qed.
Lemma lem285385 (R : type1605) (m : nat) : (term193 R m) = (term203 R m).
Proof. exact (MK_COMB (@lem285384 R) (@lem285381 R m)). Qed.
Lemma lem285388 (m : nat) : (term204 m) = (term205 m).
Proof. exact (fun_ext (fun R : type1605 => @lem285385 R m)). Qed.
Lemma lem285389 : (@all (nat -> nat -> Prop)) = (@all (nat -> nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> nat -> Prop))). Qed.
Lemma lem285390 (m : nat) : (term206 m) = (term207 m).
Proof. exact (MK_COMB (@lem285389) (@lem285388 m)). Qed.
Lemma lem285395 : term208 = term209.
Proof. exact (fun_ext (fun m : nat => @lem285390 m)). Qed.
Lemma lem285396 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem285405 : term210 = term211.
Proof. exact (MK_COMB (@lem285396) (@lem285395)). Qed.
Lemma lem285406 (R : type1605) (m : nat) : (term64 R m) = (term64 R m).
Proof. exact (eq_refl (term64 R m)). Qed.
Lemma lem285407 (R : type1605) (n : nat) : (term64 R n) = (term64 R n).
Proof. exact (eq_refl (term64 R n)). Qed.
Lemma lem285408 (R : type1605) : (term65 R) = (term65 R).
Proof. exact (fun_ext (fun n : nat => @lem285407 R n)). Qed.
Lemma lem285409 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem285410 (R : type1605) : (term47 R) = (term47 R).
Proof. exact (MK_COMB (@lem285409) (@lem285408 R)). Qed.
Lemma lem285411 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem285412 (R : type1605) : (term199 R) = (term199 R).
Proof. exact (MK_COMB (@lem285411) (@lem285410 R)). Qed.
Lemma lem285413 (R : type1605) (m : nat) : (term201 R m) = (term201 R m).
Proof. exact (MK_COMB (@lem285412 R) (@lem285406 R m)). Qed.
Lemma lem285422 (y : nat) (R : type1605) (x : nat) (z : nat) : (term212 y R x z) = (term212 y R x z).
Proof. exact (eq_refl (term212 y R x z)). Qed.
Lemma lem285423 (y : nat) (R : type1605) (x : nat) : (term213 y R x) = (term213 y R x).
Proof. exact (fun_ext (fun z : nat => @lem285422 y R x z)). Qed.
Lemma lem285424 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem285425 (y : nat) (R : type1605) (x : nat) : (term214 y R x) = (term214 y R x).
Proof. exact (MK_COMB (@lem285424) (@lem285423 y R x)). Qed.
Lemma lem285426 (R : type1605) (x : nat) : (term215 R x) = (term215 R x).
Proof. exact (fun_ext (fun y : nat => @lem285425 y R x)). Qed.
Lemma lem285427 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem285428 (R : type1605) (x : nat) : (term216 R x) = (term216 R x).
Proof. exact (MK_COMB (@lem285427) (@lem285426 R x)). Qed.
Lemma lem285429 (R : type1605) : (term217 R) = (term217 R).
Proof. exact (fun_ext (fun x : nat => @lem285428 R x)). Qed.
Lemma lem285430 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem285431 (R : type1605) : (term35 R) = (term35 R).
Proof. exact (MK_COMB (@lem285430) (@lem285429 R)). Qed.
Lemma lem285432 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem285433 (R : type1605) : (term202 R) = (term202 R).
Proof. exact (MK_COMB (@lem285432) (@lem285431 R)). Qed.
Lemma lem285434 (R : type1605) (m : nat) : (term203 R m) = (term203 R m).
Proof. exact (MK_COMB (@lem285433 R) (@lem285413 R m)). Qed.
Lemma lem285435 (m : nat) : (term205 m) = (term205 m).
Proof. exact (fun_ext (fun R : type1605 => @lem285434 R m)). Qed.
Lemma lem285436 : (@all (nat -> nat -> Prop)) = (@all (nat -> nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> nat -> Prop))). Qed.
Lemma lem285437 (m : nat) : (term207 m) = (term207 m).
Proof. exact (MK_COMB (@lem285436) (@lem285435 m)). Qed.
Lemma lem285438 : term209 = term209.
Proof. exact (fun_ext (fun m : nat => @lem285437 m)). Qed.
Lemma lem285439 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem285440 : term211 = term211.
Proof. exact (MK_COMB (@lem285439) (@lem285438)). Qed.
Lemma lem285487 : term210 = term211.
Proof. exact (TRANS (@lem285405) (@lem285440)). Qed.
Lemma lem285488 : term211 = term210.
Proof. exact (SYM (@lem285487)). Qed.
Lemma lem285490 (R : type1605) (h1 : term47 R) : term47 R.
Proof. exact (h1). Qed.
Lemma lem285492 (p : Prop) : p = (term190 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem285493 (R : type1605) (m : nat) : (term64 R m) = (term191 R m).
Proof. exact (@lem285492 (term64 R m)). Qed.
Lemma lem285494 (R : type1605) (m : nat) : (term191 R m) = (term64 R m).
Proof. exact (SYM (@lem285493 R m)). Qed.
Lemma lem285495 (R : type1605) (m : nat) (h1 : term192 R m) : term192 R m.
Proof. exact (h1). Qed.
Lemma lem285579 (R : type1605) (n : nat) : (term64 R n) = (term64 R n).
Proof. exact (eq_refl (term64 R n)). Qed.
Lemma lem285580 (R : type1605) : (term65 R) = (term65 R).
Proof. exact (fun_ext (fun n : nat => @lem285579 R n)). Qed.
Lemma lem285581 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem285590 (R : type1605) : (term47 R) = (term47 R).
Proof. exact (MK_COMB (@lem285581) (@lem285580 R)). Qed.
Lemma lem285591 (R : type1605) (h1 : term47 R) : term47 R.
Proof. exact (EQ_MP (@lem285590 R) (@lem285490 R h1)). Qed.
Lemma lem285597 (R : type1605) (m : nat) (h1 : term192 R m) : term192 R m.
Proof. exact (h1). Qed.
Lemma lem285639 (R : type1605) (n : nat) : (term64 R n) = (term64 R n).
Proof. exact (eq_refl (term64 R n)). Qed.
Lemma lem285640 (R : type1605) : (term65 R) = (term65 R).
Proof. exact (fun_ext (fun n : nat => @lem285639 R n)). Qed.
Lemma lem285641 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem285642 (R : type1605) : (term47 R) = (term47 R).
Proof. exact (MK_COMB (@lem285641) (@lem285640 R)). Qed.
Lemma lem285643 (R : type1605) (h1 : term47 R) : term47 R.
Proof. exact (EQ_MP (@lem285642 R) (@lem285591 R h1)). Qed.
Lemma lem285653 (R : type1605) (m : nat) (h1 : term192 R m) : term192 R m.
Proof. exact (h1). Qed.
Lemma lem285680 (R : type1605) (n : nat) : (term64 R n) = (term64 R n).
Proof. exact (eq_refl (term64 R n)). Qed.
Lemma lem285681 (R : type1605) : (term65 R) = (term65 R).
Proof. exact (fun_ext (fun n : nat => @lem285680 R n)). Qed.
Lemma lem285682 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem285684 (R : type1605) : (term47 R) = (term47 R).
Proof. exact (MK_COMB (@lem285682) (@lem285681 R)). Qed.
Lemma lem285685 (R : type1605) (h1 : term47 R) : term47 R.
Proof. exact (EQ_MP (@lem285684 R) (@lem285643 R h1)). Qed.
Lemma lem285689 (R : type1605) (m : nat) (h1 : term192 R m) : term192 R m.
Proof. exact (h1). Qed.
Lemma lem285699 (_6472 : nat) (R : type1605) (h1 : term47 R) : term218 R _6472.
Proof. exact (@lem285685 R h1 _6472). Qed.
Lemma lem285700 (R : type1605) (_6472 : nat) : (term218 R _6472) = (term64 R _6472).
Proof. exact (eq_refl (term218 R _6472)). Qed.
Lemma lem285717 (R : type1605) (m : nat) (h1 : term192 R m) : term192 R m.
Proof. exact (h1). Qed.
Lemma lem285719 (_6472 : nat) (R : type1605) (h1 : term47 R) : term64 R _6472.
Proof. exact (EQ_MP (@lem285700 R _6472) (@lem285699 _6472 R h1)). Qed.
Lemma lem285720 (m : nat) (R : type1605) (h1 : term47 R) : term64 R m.
Proof. exact (@lem285719 m R h1). Qed.
Lemma lem285721 (m : nat) (R : type1605) (h1 : term47 R) : term219 R m.
Proof. exact (fun h0 : term192 R m => @lem285720 m R h1). Qed.
Lemma lem285723 (p : Prop) : (term220 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem285724 (R : type1605) (m : nat) : (term219 R m) = (term64 R m).
Proof. exact (@lem285723 (term64 R m)). Qed.
Lemma lem285725 (m : nat) (R : type1605) (h1 : term47 R) : term64 R m.
Proof. exact (EQ_MP (@lem285724 R m) (@lem285721 m R h1)). Qed.
Lemma lem285728 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem285730 (R : type1605) (m : nat) : (term192 R m) = (term221 R m).
Proof. exact (@lem285728 (term64 R m)). Qed.
Lemma lem285733 (R : type1605) (m : nat) (h1 : term192 R m) : term221 R m.
Proof. exact (EQ_MP (@lem285730 R m) (@lem285717 R m h1)). Qed.
Lemma lem285736 (R : type1605) (m : nat) (h1 : term47 R) (h2 : term192 R m) : False.
Proof. exact (@lem285733 R m h2 (@lem285725 m R h1)). Qed.
Lemma lem285737 (R : type1605) (m : nat) (h1 : term47 R) (h2 : term192 R m) : term222.
Proof. exact (fun h0 : ~ False => @lem285736 R m h1 h2). Qed.
Lemma lem285739 (p : Prop) : (term220 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem285740 : term222 = False.
Proof. exact (@lem285739 False). Qed.
Lemma lem285741 (R : type1605) (m : nat) (h1 : term47 R) (h2 : term192 R m) : False.
Proof. exact (EQ_MP (@lem285740) (@lem285737 R m h1 h2)). Qed.
Lemma lem285742 (R : type1605) (m : nat) (h1 : term47 R) (h2 : term192 R m) : (term192 R m) = False.
Proof. exact (prop_ext (fun h3 : term192 R m => @lem285741 R m h1 h2) (fun h3 : False => @lem285717 R m h2)). Qed.
Lemma lem285743 (R : type1605) (m : nat) (h1 : term47 R) (h2 : term192 R m) : False.
Proof. exact (EQ_MP (@lem285742 R m h1 h2) (@lem285717 R m h2)). Qed.
Lemma lem285744 (R : type1605) (m : nat) (h1 : term47 R) (h2 : term192 R m) : (term192 R m) = False.
Proof. exact (prop_ext (fun h3 : term192 R m => @lem285743 R m h1 h2) (fun h3 : False => @lem285689 R m h2)). Qed.
Lemma lem285745 (R : type1605) (m : nat) (h1 : term47 R) (h2 : term192 R m) : False.
Proof. exact (EQ_MP (@lem285744 R m h1 h2) (@lem285689 R m h2)). Qed.
Lemma lem285746 (R : type1605) (m : nat) (h1 : term47 R) (h2 : term192 R m) : (term192 R m) = False.
Proof. exact (prop_ext (fun h3 : term192 R m => @lem285745 R m h1 h2) (fun h3 : False => @lem285689 R m h2)). Qed.
Lemma lem285747 (R : type1605) (m : nat) (h1 : term47 R) (h2 : term192 R m) : False.
Proof. exact (EQ_MP (@lem285746 R m h1 h2) (@lem285689 R m h2)). Qed.
Lemma lem285748 (R : type1605) (m : nat) (h1 : term47 R) (h2 : term192 R m) : (term47 R) = False.
Proof. exact (prop_ext (fun h3 : term47 R => @lem285747 R m h1 h2) (fun h3 : False => @lem285685 R h1)). Qed.
Lemma lem285749 (R : type1605) (m : nat) (h1 : term47 R) (h2 : term192 R m) : False.
Proof. exact (EQ_MP (@lem285748 R m h1 h2) (@lem285685 R h1)). Qed.
Lemma lem285750 (R : type1605) (m : nat) (h1 : term47 R) (h2 : term192 R m) : (term192 R m) = False.
Proof. exact (prop_ext (fun h3 : term192 R m => @lem285749 R m h1 h2) (fun h3 : False => @lem285653 R m h2)). Qed.
Lemma lem285751 (R : type1605) (m : nat) (h1 : term47 R) (h2 : term192 R m) : False.
Proof. exact (EQ_MP (@lem285750 R m h1 h2) (@lem285653 R m h2)). Qed.
Lemma lem285752 (R : type1605) (m : nat) (h1 : term47 R) (h2 : term192 R m) : (term47 R) = False.
Proof. exact (prop_ext (fun h3 : term47 R => @lem285751 R m h1 h2) (fun h3 : False => @lem285643 R h1)). Qed.
Lemma lem285753 (R : type1605) (m : nat) (h1 : term47 R) (h2 : term192 R m) : False.
Proof. exact (EQ_MP (@lem285752 R m h1 h2) (@lem285643 R h1)). Qed.
Lemma lem285754 (R : type1605) (m : nat) (h1 : term47 R) (h2 : term192 R m) : (term192 R m) = False.
Proof. exact (prop_ext (fun h3 : term192 R m => @lem285753 R m h1 h2) (fun h3 : False => @lem285597 R m h2)). Qed.
Lemma lem285755 (R : type1605) (m : nat) (h1 : term47 R) (h2 : term192 R m) : False.
Proof. exact (EQ_MP (@lem285754 R m h1 h2) (@lem285597 R m h2)). Qed.
Lemma lem285756 (R : type1605) (m : nat) (h1 : term47 R) (h2 : term192 R m) : (term47 R) = False.
Proof. exact (prop_ext (fun h3 : term47 R => @lem285755 R m h1 h2) (fun h3 : False => @lem285591 R h1)). Qed.
Lemma lem285757 (R : type1605) (m : nat) (h1 : term47 R) (h2 : term192 R m) : False.
Proof. exact (EQ_MP (@lem285756 R m h1 h2) (@lem285591 R h1)). Qed.
Lemma lem285758 (R : type1605) (m : nat) (h1 : term47 R) (h2 : term192 R m) : (term192 R m) = False.
Proof. exact (prop_ext (fun h3 : term192 R m => @lem285757 R m h1 h2) (fun h3 : False => @lem285495 R m h2)). Qed.
Lemma lem285759 (R : type1605) (m : nat) (h1 : term47 R) (h2 : term192 R m) : False.
Proof. exact (EQ_MP (@lem285758 R m h1 h2) (@lem285495 R m h2)). Qed.
Lemma lem285760 (m : nat) (R : type1605) (h1 : term47 R) : term191 R m.
Proof. exact (fun h0 : term192 R m => @lem285759 R m h1 h0). Qed.
Lemma lem285761 (m : nat) (R : type1605) (h1 : term47 R) : term64 R m.
Proof. exact (EQ_MP (@lem285494 R m) (@lem285760 m R h1)). Qed.
Lemma lem285762 (R : type1605) (m : nat) : term201 R m.
Proof. exact (fun h0 : term47 R => @lem285761 m R h0). Qed.
Lemma lem285763 (R : type1605) (m : nat) : term203 R m.
Proof. exact (fun h0 : term35 R => @lem285762 R m). Qed.
Lemma lem285768 (m : nat) : term207 m.
Proof. exact (fun R : type1605 => @lem285763 R m). Qed.
Lemma lem285773 : term211.
Proof. exact (fun m : nat => @lem285768 m). Qed.
Lemma lem285774 : term210.
Proof. exact (EQ_MP (@lem285488) (@lem285773)). Qed.
Lemma lem285775 (m : nat) : term223 m.
Proof. exact (@lem285774 m). Qed.
Lemma lem285776 (m : nat) : (term223 m) = (term206 m).
Proof. exact (eq_refl (term223 m)). Qed.
Lemma lem285777 (m : nat) : term206 m.
Proof. exact (EQ_MP (@lem285776 m) (@lem285775 m)). Qed.
Lemma lem285778 (m : nat) (R : type1605) : term224 m R.
Proof. exact (@lem285777 m R). Qed.
Lemma lem285779 (R : type1605) (m : nat) : (term224 m R) = (term193 R m).
Proof. exact (eq_refl (term224 m R)). Qed.
Lemma lem285780 (R : type1605) (m : nat) : term193 R m.
Proof. exact (EQ_MP (@lem285779 R m) (@lem285778 m R)). Qed.
Lemma lem285782 (R : type1605) (m : nat) : term193 R m.
Proof. exact (@lem285340 R m (@lem285780 R m)). Qed.
Lemma lem285783 (m : nat) (R : type1605) (h1 : term35 R) : term200 R m.
Proof. exact (@lem285782 R m (@lem283572 R h1)). Qed.
Lemma lem285784 (m : nat) (R : type1605) (h1 : term35 R) (h2 : term47 R) : term191 R m.
Proof. exact (@lem285783 m R h1 (@lem284864 R h2)). Qed.
Lemma lem285785 (R : type1605) (m : nat) (h1 : term35 R) (h2 : term47 R) (h3 : term192 R m) : False.
Proof. exact (@lem285784 m R h1 h2 (@lem285325 R m h3)). Qed.
Lemma lem285786 (R : type1605) (m : nat) (h1 : term35 R) (h2 : term47 R) (h3 : term192 R m) : (term192 R m) = False.
Proof. exact (prop_ext (fun h4 : term192 R m => @lem285785 R m h1 h2 h3) (fun h4 : False => @lem285325 R m h3)). Qed.
Lemma lem285787 (R : type1605) (m : nat) (h1 : term35 R) (h2 : term47 R) (h3 : term192 R m) : False.
Proof. exact (EQ_MP (@lem285786 R m h1 h2 h3) (@lem285325 R m h3)). Qed.
Lemma lem285788 (m : nat) (R : type1605) (h1 : term35 R) (h2 : term47 R) : term191 R m.
Proof. exact (fun h0 : term192 R m => @lem285787 R m h1 h2 h0). Qed.
Lemma lem285789 (m : nat) (R : type1605) (h1 : term35 R) (h2 : term47 R) : term64 R m.
Proof. exact (EQ_MP (@lem285324 R m) (@lem285788 m R h1 h2)). Qed.
Lemma lem285791 (p : Prop) : p = (term190 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem285792 (R : type1605) (m : nat) (d : nat) : (term189 R m d) = (term225 R m d).
Proof. exact (@lem285791 (term189 R m d)). Qed.
Lemma lem285793 (R : type1605) (m : nat) (d : nat) : (term225 R m d) = (term189 R m d).
Proof. exact (SYM (@lem285792 R m d)). Qed.
Lemma lem285794 (R : type1605) (m : nat) (d : nat) (h1 : term226 R m d) : term226 R m d.
Proof. exact (h1). Qed.
Lemma lem285797 (R : type1605) (m : nat) (d : nat) (h1 : term227 R m d) : term227 R m d.
Proof. exact (h1). Qed.
Lemma lem285798 (R : type1605) (m : nat) (d : nat) : term228 R m d.
Proof. exact (fun h0 : term227 R m d => @lem285797 R m d h0). Qed.
Lemma lem285799 (R : type1605) (m : nat) (d : nat) (h1 : term228 R m d) : term228 R m d.
Proof. exact (h1). Qed.
Lemma lem285800 (R : type1605) (m : nat) (d : nat) (h1 : term227 R m d) : term227 R m d.
Proof. exact (h1). Qed.
Lemma lem285801 (R : type1605) (m : nat) (d : nat) (h1 : term227 R m d) (h2 : term228 R m d) : term227 R m d.
Proof. exact (@lem285799 R m d h2 (@lem285800 R m d h1)). Qed.
Lemma lem285802 (R : type1605) (m : nat) (d : nat) (h1 : term227 R m d) : term229 R m d.
Proof. exact (fun h0 : term228 R m d => @lem285801 R m d h1 h0). Qed.
Lemma lem285803 (R : type1605) (m : nat) (d : nat) (h1 : term228 R m d) : term228 R m d.
Proof. exact (h1). Qed.
Lemma lem285804 (R : type1605) (m : nat) (d : nat) (h1 : term227 R m d) (h2 : term228 R m d) : term227 R m d.
Proof. exact (@lem285802 R m d h1 (@lem285803 R m d h2)). Qed.
Lemma lem285805 (R : type1605) (m : nat) (d : nat) (h1 : term228 R m d) : term228 R m d.
Proof. exact (fun h0 : term227 R m d => @lem285804 R m d h0 h1). Qed.
Lemma lem285806 (R : type1605) (m : nat) (d : nat) : term230 R m d.
Proof. exact (fun h0 : term228 R m d => @lem285805 R m d h0). Qed.
Lemma lem285809 (R : type1605) (m : nat) (d : nat) : term228 R m d.
Proof. exact (@lem285806 R m d (@lem285798 R m d)). Qed.
Lemma lem285849 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem285850 (R : type1605) (m : nat) (d : nat) : (term225 R m d) = (term231 R m d).
Proof. exact (@lem285849 (term226 R m d)). Qed.
Lemma lem285852 (t : Prop) : (term198 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem285853 (R : type1605) (m : nat) (d : nat) : (term231 R m d) = (term189 R m d).
Proof. exact (@lem285852 (term189 R m d)). Qed.
Lemma lem285854 (R : type1605) (m : nat) (d : nat) : (term225 R m d) = (term189 R m d).
Proof. exact (TRANS (@lem285850 R m d) (@lem285853 R m d)). Qed.
Lemma lem285855 (R : type1605) (m : nat) (d : nat) : (term170 R m d) = (term170 R m d).
Proof. exact (eq_refl (term170 R m d)). Qed.
Lemma lem285856 (R : type1605) (m : nat) (d : nat) : (term232 R m d) = (term233 R m d).
Proof. exact (MK_COMB (@lem285855 R m d) (@lem285854 R m d)). Qed.
Lemma lem285859 (R : type1605) : (term199 R) = (term199 R).
Proof. exact (eq_refl (term199 R)). Qed.
Lemma lem285860 (R : type1605) (m : nat) (d : nat) : (term234 R m d) = (term235 R m d).
Proof. exact (MK_COMB (@lem285859 R) (@lem285856 R m d)). Qed.
Lemma lem285863 (R : type1605) : (term202 R) = (term202 R).
Proof. exact (eq_refl (term202 R)). Qed.
Lemma lem285864 (R : type1605) (m : nat) (d : nat) : (term227 R m d) = (term236 R m d).
Proof. exact (MK_COMB (@lem285863 R) (@lem285860 R m d)). Qed.
Lemma lem285867 (m : nat) (d : nat) : (term237 m d) = (term238 m d).
Proof. exact (fun_ext (fun R : type1605 => @lem285864 R m d)). Qed.
Lemma lem285868 : (@all (nat -> nat -> Prop)) = (@all (nat -> nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> nat -> Prop))). Qed.
Lemma lem285869 (m : nat) (d : nat) : (term239 m d) = (term240 m d).
Proof. exact (MK_COMB (@lem285868) (@lem285867 m d)). Qed.
Lemma lem285874 (d : nat) : (term241 d) = (term242 d).
Proof. exact (fun_ext (fun m : nat => @lem285869 m d)). Qed.
Lemma lem285875 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem285876 (d : nat) : (term243 d) = (term244 d).
Proof. exact (MK_COMB (@lem285875) (@lem285874 d)). Qed.
Lemma lem285881 : term245 = term246.
Proof. exact (fun_ext (fun d : nat => @lem285876 d)). Qed.
Lemma lem285882 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem285891 : term247 = term248.
Proof. exact (MK_COMB (@lem285882) (@lem285881)). Qed.
Lemma lem285896 (R : type1605) (m : nat) (d : nat) : (term233 R m d) = (term233 R m d).
Proof. exact (eq_refl (term233 R m d)). Qed.
Lemma lem285897 (R : type1605) (n : nat) : (term64 R n) = (term64 R n).
Proof. exact (eq_refl (term64 R n)). Qed.
Lemma lem285898 (R : type1605) : (term65 R) = (term65 R).
Proof. exact (fun_ext (fun n : nat => @lem285897 R n)). Qed.
Lemma lem285899 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem285900 (R : type1605) : (term47 R) = (term47 R).
Proof. exact (MK_COMB (@lem285899) (@lem285898 R)). Qed.
Lemma lem285901 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem285902 (R : type1605) : (term199 R) = (term199 R).
Proof. exact (MK_COMB (@lem285901) (@lem285900 R)). Qed.
Lemma lem285903 (R : type1605) (m : nat) (d : nat) : (term235 R m d) = (term235 R m d).
Proof. exact (MK_COMB (@lem285902 R) (@lem285896 R m d)). Qed.
Lemma lem285912 (y : nat) (R : type1605) (x : nat) (z : nat) : (term212 y R x z) = (term212 y R x z).
Proof. exact (eq_refl (term212 y R x z)). Qed.
Lemma lem285913 (y : nat) (R : type1605) (x : nat) : (term213 y R x) = (term213 y R x).
Proof. exact (fun_ext (fun z : nat => @lem285912 y R x z)). Qed.
Lemma lem285914 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem285915 (y : nat) (R : type1605) (x : nat) : (term214 y R x) = (term214 y R x).
Proof. exact (MK_COMB (@lem285914) (@lem285913 y R x)). Qed.
Lemma lem285916 (R : type1605) (x : nat) : (term215 R x) = (term215 R x).
Proof. exact (fun_ext (fun y : nat => @lem285915 y R x)). Qed.
Lemma lem285917 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem285918 (R : type1605) (x : nat) : (term216 R x) = (term216 R x).
Proof. exact (MK_COMB (@lem285917) (@lem285916 R x)). Qed.
Lemma lem285919 (R : type1605) : (term217 R) = (term217 R).
Proof. exact (fun_ext (fun x : nat => @lem285918 R x)). Qed.
Lemma lem285920 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem285921 (R : type1605) : (term35 R) = (term35 R).
Proof. exact (MK_COMB (@lem285920) (@lem285919 R)). Qed.
Lemma lem285922 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem285923 (R : type1605) : (term202 R) = (term202 R).
Proof. exact (MK_COMB (@lem285922) (@lem285921 R)). Qed.
Lemma lem285924 (R : type1605) (m : nat) (d : nat) : (term236 R m d) = (term236 R m d).
Proof. exact (MK_COMB (@lem285923 R) (@lem285903 R m d)). Qed.
Lemma lem285925 (m : nat) (d : nat) : (term238 m d) = (term238 m d).
Proof. exact (fun_ext (fun R : type1605 => @lem285924 R m d)). Qed.
Lemma lem285926 : (@all (nat -> nat -> Prop)) = (@all (nat -> nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> nat -> Prop))). Qed.
Lemma lem285927 (m : nat) (d : nat) : (term240 m d) = (term240 m d).
Proof. exact (MK_COMB (@lem285926) (@lem285925 m d)). Qed.
Lemma lem285928 (d : nat) : (term242 d) = (term242 d).
Proof. exact (fun_ext (fun m : nat => @lem285927 m d)). Qed.
Lemma lem285929 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem285930 (d : nat) : (term244 d) = (term244 d).
Proof. exact (MK_COMB (@lem285929) (@lem285928 d)). Qed.
Lemma lem285931 : term246 = term246.
Proof. exact (fun_ext (fun d : nat => @lem285930 d)). Qed.
Lemma lem285932 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem285933 : term248 = term248.
Proof. exact (MK_COMB (@lem285932) (@lem285931)). Qed.
Lemma lem285988 : term247 = term248.
Proof. exact (TRANS (@lem285891) (@lem285933)). Qed.
Lemma lem285989 : term248 = term247.
Proof. exact (SYM (@lem285988)). Qed.
Lemma lem285990 (R : type1605) (h1 : term35 R) : term35 R.
Proof. exact (h1). Qed.
Lemma lem285991 (R : type1605) (h1 : term47 R) : term47 R.
Proof. exact (h1). Qed.
Lemma lem285994 (p : Prop) : p = (term190 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem285995 (R : type1605) (m : nat) (d : nat) : (term189 R m d) = (term225 R m d).
Proof. exact (@lem285994 (term189 R m d)). Qed.
Lemma lem285996 (R : type1605) (m : nat) (d : nat) : (term225 R m d) = (term189 R m d).
Proof. exact (SYM (@lem285995 R m d)). Qed.
Lemma lem285997 (R : type1605) (m : nat) (d : nat) (h1 : term226 R m d) : term226 R m d.
Proof. exact (h1). Qed.
Lemma lem286004 (x : nat) (R : type1605) (y : nat) (z : nat) : (term249 x R y z) = (term250 x R y z).
Proof. exact (@lem17045 (R x y) (R y z)). Qed.
Lemma lem286005 (R : type1605) (x : nat) (z : nat) : (R x z) = (R x z).
Proof. exact (eq_refl (R x z)). Qed.
Lemma lem286006 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem286007 (x : nat) (R : type1605) (y : nat) (z : nat) : (term251 x R y z) = (term252 x R y z).
Proof. exact (MK_COMB (@lem286006) (@lem286004 x R y z)). Qed.
Lemma lem286008 (y : nat) (R : type1605) (x : nat) (z : nat) : (term253 y R x z) = (term254 y R x z).
Proof. exact (MK_COMB (@lem286007 x R y z) (@lem286005 R x z)). Qed.
Lemma lem286009 (y : nat) (R : type1605) (x : nat) (z : nat) : (term212 y R x z) = (term253 y R x z).
Proof. exact (@lem17265 (term255 x R y z) (R x z)). Qed.
Lemma lem286010 (y : nat) (R : type1605) (x : nat) (z : nat) : (term212 y R x z) = (term254 y R x z).
Proof. exact (TRANS (@lem286009 y R x z) (@lem286008 y R x z)). Qed.
Lemma lem286011 (y : nat) (R : type1605) (x : nat) : (term213 y R x) = (term256 y R x).
Proof. exact (fun_ext (fun z : nat => @lem286010 y R x z)). Qed.
Lemma lem286012 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem286013 (y : nat) (R : type1605) (x : nat) : (term214 y R x) = (term257 y R x).
Proof. exact (MK_COMB (@lem286012) (@lem286011 y R x)). Qed.
Lemma lem286014 (R : type1605) (x : nat) : (term215 R x) = (term258 R x).
Proof. exact (fun_ext (fun y : nat => @lem286013 y R x)). Qed.
Lemma lem286015 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem286016 (R : type1605) (x : nat) : (term216 R x) = (term259 R x).
Proof. exact (MK_COMB (@lem286015) (@lem286014 R x)). Qed.
Lemma lem286017 (R : type1605) : (term217 R) = (term260 R).
Proof. exact (fun_ext (fun x : nat => @lem286016 R x)). Qed.
Lemma lem286018 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem286079 (R : type1605) : (term35 R) = (term261 R).
Proof. exact (MK_COMB (@lem286018) (@lem286017 R)). Qed.
Lemma lem286080 (R : type1605) (h1 : term35 R) : term261 R.
Proof. exact (EQ_MP (@lem286079 R) (@lem285990 R h1)). Qed.
Lemma lem286081 (R : type1605) (n : nat) : (term64 R n) = (term64 R n).
Proof. exact (eq_refl (term64 R n)). Qed.
Lemma lem286082 (R : type1605) : (term65 R) = (term65 R).
Proof. exact (fun_ext (fun n : nat => @lem286081 R n)). Qed.
Lemma lem286083 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem286092 (R : type1605) : (term47 R) = (term47 R).
Proof. exact (MK_COMB (@lem286083) (@lem286082 R)). Qed.
Lemma lem286093 (R : type1605) (h1 : term47 R) : term47 R.
Proof. exact (EQ_MP (@lem286092 R) (@lem285991 R h1)). Qed.
Lemma lem286099 (R : type1605) (m : nat) (d : nat) (h1 : term158 R m d) : term158 R m d.
Proof. exact (h1). Qed.
Lemma lem286105 (R : type1605) (m : nat) (d : nat) (h1 : term226 R m d) : term226 R m d.
Proof. exact (h1). Qed.
Lemma lem286130 (y : nat) (R : type1605) (x : nat) (z : nat) : (term254 y R x z) = (term254 y R x z).
Proof. exact (eq_refl (term254 y R x z)). Qed.
Lemma lem286131 (y : nat) (R : type1605) (x : nat) : (term256 y R x) = (term256 y R x).
Proof. exact (fun_ext (fun z : nat => @lem286130 y R x z)). Qed.
Lemma lem286132 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem286133 (y : nat) (R : type1605) (x : nat) : (term257 y R x) = (term257 y R x).
Proof. exact (MK_COMB (@lem286132) (@lem286131 y R x)). Qed.
Lemma lem286134 (R : type1605) (x : nat) : (term258 R x) = (term258 R x).
Proof. exact (fun_ext (fun y : nat => @lem286133 y R x)). Qed.
Lemma lem286135 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem286136 (R : type1605) (x : nat) : (term259 R x) = (term259 R x).
Proof. exact (MK_COMB (@lem286135) (@lem286134 R x)). Qed.
Lemma lem286137 (R : type1605) : (term260 R) = (term260 R).
Proof. exact (fun_ext (fun x : nat => @lem286136 R x)). Qed.
Lemma lem286138 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem286139 (R : type1605) : (term261 R) = (term261 R).
Proof. exact (MK_COMB (@lem286138) (@lem286137 R)). Qed.
Lemma lem286140 (R : type1605) (h1 : term35 R) : term261 R.
Proof. exact (EQ_MP (@lem286139 R) (@lem286080 R h1)). Qed.
Lemma lem286147 (R : type1605) (n : nat) : (term64 R n) = (term64 R n).
Proof. exact (eq_refl (term64 R n)). Qed.
Lemma lem286148 (R : type1605) : (term65 R) = (term65 R).
Proof. exact (fun_ext (fun n : nat => @lem286147 R n)). Qed.
Lemma lem286149 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem286150 (R : type1605) : (term47 R) = (term47 R).
Proof. exact (MK_COMB (@lem286149) (@lem286148 R)). Qed.
Lemma lem286151 (R : type1605) (h1 : term47 R) : term47 R.
Proof. exact (EQ_MP (@lem286150 R) (@lem286093 R h1)). Qed.
Lemma lem286163 (R : type1605) (m : nat) (d : nat) (h1 : term158 R m d) : term158 R m d.
Proof. exact (h1). Qed.
Lemma lem286179 (R : type1605) (m : nat) (d : nat) (h1 : term226 R m d) : term226 R m d.
Proof. exact (h1). Qed.
Lemma lem286193 (y : nat) (R : type1605) (x : nat) (z : nat) : (term254 y R x z) = (term254 y R x z).
Proof. exact (eq_refl (term254 y R x z)). Qed.
Lemma lem286194 (y : nat) (R : type1605) (x : nat) : (term256 y R x) = (term256 y R x).
Proof. exact (fun_ext (fun z : nat => @lem286193 y R x z)). Qed.
Lemma lem286195 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem286196 (y : nat) (R : type1605) (x : nat) : (term257 y R x) = (term257 y R x).
Proof. exact (MK_COMB (@lem286195) (@lem286194 y R x)). Qed.
Lemma lem286197 (R : type1605) (x : nat) : (term258 R x) = (term258 R x).
Proof. exact (fun_ext (fun y : nat => @lem286196 y R x)). Qed.
Lemma lem286198 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem286199 (R : type1605) (x : nat) : (term259 R x) = (term259 R x).
Proof. exact (MK_COMB (@lem286198) (@lem286197 R x)). Qed.
Lemma lem286200 (R : type1605) : (term260 R) = (term260 R).
Proof. exact (fun_ext (fun x : nat => @lem286199 R x)). Qed.
Lemma lem286201 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem286203 (R : type1605) : (term261 R) = (term261 R).
Proof. exact (MK_COMB (@lem286201) (@lem286200 R)). Qed.
Lemma lem286204 (R : type1605) (h1 : term35 R) : term261 R.
Proof. exact (EQ_MP (@lem286203 R) (@lem286140 R h1)). Qed.
Lemma lem286206 (R : type1605) (n : nat) : (term64 R n) = (term64 R n).
Proof. exact (eq_refl (term64 R n)). Qed.
Lemma lem286207 (R : type1605) : (term65 R) = (term65 R).
Proof. exact (fun_ext (fun n : nat => @lem286206 R n)). Qed.
Lemma lem286208 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem286210 (R : type1605) : (term47 R) = (term47 R).
Proof. exact (MK_COMB (@lem286208) (@lem286207 R)). Qed.
Lemma lem286211 (R : type1605) (h1 : term47 R) : term47 R.
Proof. exact (EQ_MP (@lem286210 R) (@lem286151 R h1)). Qed.
Lemma lem286215 (R : type1605) (m : nat) (d : nat) (h1 : term158 R m d) : term158 R m d.
Proof. exact (h1). Qed.
Lemma lem286219 (R : type1605) (m : nat) (d : nat) (h1 : term226 R m d) : term226 R m d.
Proof. exact (h1). Qed.
Lemma lem286220 (_6473 : nat) (R : type1605) (h1 : term35 R) : term262 R _6473.
Proof. exact (@lem286204 R h1 _6473). Qed.
Lemma lem286221 (R : type1605) (_6473 : nat) : (term262 R _6473) = (term259 R _6473).
Proof. exact (eq_refl (term262 R _6473)). Qed.
Lemma lem286222 (_6473 : nat) (R : type1605) (h1 : term35 R) : term259 R _6473.
Proof. exact (EQ_MP (@lem286221 R _6473) (@lem286220 _6473 R h1)). Qed.
Lemma lem286223 (_6473 : nat) (_6474 : nat) (R : type1605) (h1 : term35 R) : term263 R _6473 _6474.
Proof. exact (@lem286222 _6473 R h1 _6474). Qed.
Lemma lem286224 (_6474 : nat) (R : type1605) (_6473 : nat) : (term263 R _6473 _6474) = (term257 _6474 R _6473).
Proof. exact (eq_refl (term263 R _6473 _6474)). Qed.
Lemma lem286225 (_6474 : nat) (_6473 : nat) (R : type1605) (h1 : term35 R) : term257 _6474 R _6473.
Proof. exact (EQ_MP (@lem286224 _6474 R _6473) (@lem286223 _6473 _6474 R h1)). Qed.
Lemma lem286226 (_6474 : nat) (_6473 : nat) (_6475 : nat) (R : type1605) (h1 : term35 R) : term264 _6474 R _6473 _6475.
Proof. exact (@lem286225 _6474 _6473 R h1 _6475). Qed.
Lemma lem286227 (_6474 : nat) (R : type1605) (_6473 : nat) (_6475 : nat) : (term264 _6474 R _6473 _6475) = (term254 _6474 R _6473 _6475).
Proof. exact (eq_refl (term264 _6474 R _6473 _6475)). Qed.
Lemma lem286228 (_6474 : nat) (_6473 : nat) (_6475 : nat) (R : type1605) (h1 : term35 R) : term254 _6474 R _6473 _6475.
Proof. exact (EQ_MP (@lem286227 _6474 R _6473 _6475) (@lem286226 _6474 _6473 _6475 R h1)). Qed.
Lemma lem286229 (_6476 : nat) (R : type1605) (h1 : term47 R) : term218 R _6476.
Proof. exact (@lem286211 R h1 _6476). Qed.
Lemma lem286230 (R : type1605) (_6476 : nat) : (term218 R _6476) = (term64 R _6476).
Proof. exact (eq_refl (term218 R _6476)). Qed.
Lemma lem286242 (_6474 : nat) (R : type1605) (_6473 : nat) (_6475 : nat) : (term254 _6474 R _6473 _6475) = (term265 _6474 R _6473 _6475).
Proof. exact (@lem283497 (term266 R _6473 _6474) (term266 R _6474 _6475) (R _6473 _6475)). Qed.
Lemma lem286243 (_6474 : nat) (_6473 : nat) (_6475 : nat) (R : type1605) (h1 : term35 R) : term265 _6474 R _6473 _6475.
Proof. exact (EQ_MP (@lem286242 _6474 R _6473 _6475) (@lem286228 _6474 _6473 _6475 R h1)). Qed.
Lemma lem286247 (R : type1605) (m : nat) (d : nat) (h1 : term158 R m d) : term158 R m d.
Proof. exact (h1). Qed.
Lemma lem286249 (R : type1605) (m : nat) (d : nat) (h1 : term226 R m d) : term226 R m d.
Proof. exact (h1). Qed.
Lemma lem286251 (R : type1605) (m : nat) (d : nat) (h1 : term158 R m d) : term158 R m d.
Proof. exact (h1). Qed.
Lemma lem286252 (R : type1605) (m : nat) (d : nat) (h1 : term158 R m d) : term267 R m d.
Proof. exact (fun h0 : term268 R m d => @lem286251 R m d h1). Qed.
Lemma lem286254 (p : Prop) : (term220 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem286255 (R : type1605) (m : nat) (d : nat) : (term267 R m d) = (term158 R m d).
Proof. exact (@lem286254 (term158 R m d)). Qed.
Lemma lem286256 (R : type1605) (m : nat) (d : nat) (h1 : term158 R m d) : term158 R m d.
Proof. exact (EQ_MP (@lem286255 R m d) (@lem286252 R m d h1)). Qed.
Lemma lem286258 (_6476 : nat) (R : type1605) (h1 : term47 R) : term64 R _6476.
Proof. exact (EQ_MP (@lem286230 R _6476) (@lem286229 _6476 R h1)). Qed.
Lemma lem286259 (m : nat) (d : nat) (R : type1605) (h1 : term47 R) : term269 R m d.
Proof. exact (@lem286258 (term14 m d) R h1). Qed.
Lemma lem286260 (m : nat) (d : nat) (R : type1605) (h1 : term47 R) : term270 R m d.
Proof. exact (fun h0 : term271 R m d => @lem286259 m d R h1). Qed.
Lemma lem286262 (p : Prop) : (term220 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem286263 (R : type1605) (m : nat) (d : nat) : (term270 R m d) = (term269 R m d).
Proof. exact (@lem286262 (term269 R m d)). Qed.
Lemma lem286264 (m : nat) (d : nat) (R : type1605) (h1 : term47 R) : term269 R m d.
Proof. exact (EQ_MP (@lem286263 R m d) (@lem286260 m d R h1)). Qed.
Lemma lem286280 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem286281 (_6473 : nat) (R : type1605) (_6474 : nat) (_6475 : nat) : (term272 _6474 R _6473 _6475) = (term273 _6473 R _6474 _6475).
Proof. exact (@lem286280 (R _6473 _6475) (term266 R _6474 _6475)). Qed.
Lemma lem286287 (R : type1605) (_6473 : nat) (_6474 : nat) : (term274 R _6473 _6474) = (term274 R _6473 _6474).
Proof. exact (eq_refl (term274 R _6473 _6474)). Qed.
Lemma lem286288 (_6473 : nat) (R : type1605) (_6474 : nat) (_6475 : nat) : (term265 _6474 R _6473 _6475) = (term275 _6473 R _6474 _6475).
Proof. exact (MK_COMB (@lem286287 R _6473 _6474) (@lem286281 _6473 R _6474 _6475)). Qed.
Lemma lem286292 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem286293 (_6473 : nat) (R : type1605) (_6474 : nat) (_6475 : nat) : (term275 _6473 R _6474 _6475) = (term276 _6473 R _6474 _6475).
Proof. exact (@lem286292 (R _6473 _6475) (term266 R _6473 _6474) (term266 R _6474 _6475)). Qed.
Lemma lem286309 (_6473 : nat) (R : type1605) (_6474 : nat) (_6475 : nat) : (term265 _6474 R _6473 _6475) = (term276 _6473 R _6474 _6475).
Proof. exact (TRANS (@lem286288 _6473 R _6474 _6475) (@lem286293 _6473 R _6474 _6475)). Qed.
Lemma lem286310 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem286311 (_6473 : nat) (R : type1605) (_6474 : nat) (_6475 : nat) : (term277 _6474 R _6473 _6475) = (term278 _6473 R _6474 _6475).
Proof. exact (MK_COMB (@lem286310) (@lem286309 _6473 R _6474 _6475)). Qed.
Lemma lem286327 (_6473 : nat) (R : type1605) (_6474 : nat) (_6475 : nat) : (term276 _6473 R _6474 _6475) = (term276 _6473 R _6474 _6475).
Proof. exact (eq_refl (term276 _6473 R _6474 _6475)). Qed.
Lemma lem286328 (_6473 : nat) (R : type1605) (_6474 : nat) (_6475 : nat) : ((term265 _6474 R _6473 _6475) = (term276 _6473 R _6474 _6475)) = ((term276 _6473 R _6474 _6475) = (term276 _6473 R _6474 _6475)).
Proof. exact (MK_COMB (@lem286311 _6473 R _6474 _6475) (@lem286327 _6473 R _6474 _6475)). Qed.
Lemma lem286330 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem286331 (x : Prop) : (x = x) = True.
Proof. exact (@lem286330 Prop x). Qed.
Lemma lem286332 (_6473 : nat) (R : type1605) (_6474 : nat) (_6475 : nat) : ((term276 _6473 R _6474 _6475) = (term276 _6473 R _6474 _6475)) = True.
Proof. exact (@lem286331 (term276 _6473 R _6474 _6475)). Qed.
Lemma lem286333 (_6473 : nat) (R : type1605) (_6474 : nat) (_6475 : nat) : ((term265 _6474 R _6473 _6475) = (term276 _6473 R _6474 _6475)) = True.
Proof. exact (TRANS (@lem286328 _6473 R _6474 _6475) (@lem286332 _6473 R _6474 _6475)). Qed.
Lemma lem286334 (_6473 : nat) (R : type1605) (_6474 : nat) (_6475 : nat) : True = ((term265 _6474 R _6473 _6475) = (term276 _6473 R _6474 _6475)).
Proof. exact (SYM (@lem286333 _6473 R _6474 _6475)). Qed.
Lemma lem286335 (_6473 : nat) (R : type1605) (_6474 : nat) (_6475 : nat) : (term265 _6474 R _6473 _6475) = (term276 _6473 R _6474 _6475).
Proof. exact (EQ_MP (@lem286334 _6473 R _6474 _6475) (@lem0)). Qed.
Lemma lem286336 (_6473 : nat) (_6474 : nat) (_6475 : nat) (R : type1605) (h1 : term35 R) : term276 _6473 R _6474 _6475.
Proof. exact (EQ_MP (@lem286335 _6473 R _6474 _6475) (@lem286243 _6474 _6473 _6475 R h1)). Qed.
Lemma lem286338 (b : Prop) (a : Prop) : (a \/ b) = (term279 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem286339 (_6474 : nat) (R : type1605) (_6473 : nat) (_6475 : nat) : (term276 _6473 R _6474 _6475) = (term280 _6474 R _6473 _6475).
Proof. exact (@lem286338 (term250 _6473 R _6474 _6475) (R _6473 _6475)). Qed.
Lemma lem286341 (a : Prop) (b : Prop) : (term281 a b) = (term282 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem286342 (_6473 : nat) (R : type1605) (_6474 : nat) (_6475 : nat) : (term283 _6473 R _6474 _6475) = (term284 _6473 R _6474 _6475).
Proof. exact (@lem286341 (term266 R _6473 _6474) (term266 R _6474 _6475)). Qed.
Lemma lem286344 (a : Prop) : (term198 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem286345 (R : type1605) (_6473 : nat) (_6474 : nat) : (term285 R _6473 _6474) = (R _6473 _6474).
Proof. exact (@lem286344 (R _6473 _6474)). Qed.
Lemma lem286346 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem286347 (R : type1605) (_6473 : nat) (_6474 : nat) : (term286 R _6473 _6474) = (term287 R _6473 _6474).
Proof. exact (MK_COMB (@lem286346) (@lem286345 R _6473 _6474)). Qed.
Lemma lem286349 (a : Prop) : (term198 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem286350 (R : type1605) (_6474 : nat) (_6475 : nat) : (term285 R _6474 _6475) = (R _6474 _6475).
Proof. exact (@lem286349 (R _6474 _6475)). Qed.
Lemma lem286351 (_6473 : nat) (R : type1605) (_6474 : nat) (_6475 : nat) : (term284 _6473 R _6474 _6475) = (term255 _6473 R _6474 _6475).
Proof. exact (MK_COMB (@lem286347 R _6473 _6474) (@lem286350 R _6474 _6475)). Qed.
Lemma lem286352 (_6473 : nat) (R : type1605) (_6474 : nat) (_6475 : nat) : (term283 _6473 R _6474 _6475) = (term255 _6473 R _6474 _6475).
Proof. exact (TRANS (@lem286342 _6473 R _6474 _6475) (@lem286351 _6473 R _6474 _6475)). Qed.
Lemma lem286353 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem286354 (_6473 : nat) (R : type1605) (_6474 : nat) (_6475 : nat) : (term288 _6473 R _6474 _6475) = (term289 _6473 R _6474 _6475).
Proof. exact (MK_COMB (@lem286353) (@lem286352 _6473 R _6474 _6475)). Qed.
Lemma lem286355 (R : type1605) (_6473 : nat) (_6475 : nat) : (R _6473 _6475) = (R _6473 _6475).
Proof. exact (eq_refl (R _6473 _6475)). Qed.
Lemma lem286356 (_6474 : nat) (R : type1605) (_6473 : nat) (_6475 : nat) : (term280 _6474 R _6473 _6475) = (term212 _6474 R _6473 _6475).
Proof. exact (MK_COMB (@lem286354 _6473 R _6474 _6475) (@lem286355 R _6473 _6475)). Qed.
Lemma lem286357 (_6474 : nat) (R : type1605) (_6473 : nat) (_6475 : nat) : (term276 _6473 R _6474 _6475) = (term212 _6474 R _6473 _6475).
Proof. exact (TRANS (@lem286339 _6474 R _6473 _6475) (@lem286356 _6474 R _6473 _6475)). Qed.
Lemma lem286359 (R : type1605) (m : nat) (d : nat) (h1 : term47 R) (h2 : term158 R m d) : term290 R m d.
Proof. exact (conj (@lem286256 R m d h2) (@lem286264 m d R h1)). Qed.
Lemma lem286361 (_6474 : nat) (_6473 : nat) (_6475 : nat) (R : type1605) (h1 : term35 R) : term212 _6474 R _6473 _6475.
Proof. exact (EQ_MP (@lem286357 _6474 R _6473 _6475) (@lem286336 _6473 _6474 _6475 R h1)). Qed.
Lemma lem286362 (m : nat) (d : nat) (R : type1605) (h1 : term35 R) : term291 R m d.
Proof. exact (@lem286361 (term14 m d) m (term188 m d) R h1). Qed.
Lemma lem286365 (R : type1605) (m : nat) (d : nat) (h1 : term35 R) (h2 : term47 R) (h3 : term158 R m d) : term189 R m d.
Proof. exact (@lem286362 m d R h1 (@lem286359 R m d h2 h3)). Qed.
Lemma lem286366 (R : type1605) (m : nat) (d : nat) (h1 : term35 R) (h2 : term47 R) (h3 : term158 R m d) : term292 R m d.
Proof. exact (fun h0 : term226 R m d => @lem286365 R m d h1 h2 h3). Qed.
Lemma lem286368 (p : Prop) : (term220 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem286369 (R : type1605) (m : nat) (d : nat) : (term292 R m d) = (term189 R m d).
Proof. exact (@lem286368 (term189 R m d)). Qed.
Lemma lem286370 (R : type1605) (m : nat) (d : nat) (h1 : term35 R) (h2 : term47 R) (h3 : term158 R m d) : term189 R m d.
Proof. exact (EQ_MP (@lem286369 R m d) (@lem286366 R m d h1 h2 h3)). Qed.
Lemma lem286373 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem286375 (R : type1605) (m : nat) (d : nat) : (term226 R m d) = (term293 R m d).
Proof. exact (@lem286373 (term189 R m d)). Qed.
Lemma lem286378 (R : type1605) (m : nat) (d : nat) (h1 : term226 R m d) : term293 R m d.
Proof. exact (EQ_MP (@lem286375 R m d) (@lem286249 R m d h1)). Qed.
Lemma lem286381 (R : type1605) (m : nat) (d : nat) (h1 : term35 R) (h2 : term47 R) (h3 : term226 R m d) (h4 : term158 R m d) : False.
Proof. exact (@lem286378 R m d h3 (@lem286370 R m d h1 h2 h4)). Qed.
Lemma lem286382 (R : type1605) (m : nat) (d : nat) (h1 : term35 R) (h2 : term47 R) (h3 : term226 R m d) (h4 : term158 R m d) : term222.
Proof. exact (fun h0 : ~ False => @lem286381 R m d h1 h2 h3 h4). Qed.
Lemma lem286384 (p : Prop) : (term220 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem286385 : term222 = False.
Proof. exact (@lem286384 False). Qed.
Lemma lem286386 (R : type1605) (m : nat) (d : nat) (h1 : term35 R) (h2 : term47 R) (h3 : term226 R m d) (h4 : term158 R m d) : False.
Proof. exact (EQ_MP (@lem286385) (@lem286382 R m d h1 h2 h3 h4)). Qed.
Lemma lem286387 (R : type1605) (m : nat) (d : nat) (h1 : term35 R) (h2 : term47 R) (h3 : term226 R m d) (h4 : term158 R m d) : (term226 R m d) = False.
Proof. exact (prop_ext (fun h5 : term226 R m d => @lem286386 R m d h1 h2 h3 h4) (fun h5 : False => @lem286249 R m d h3)). Qed.
Lemma lem286388 (R : type1605) (m : nat) (d : nat) (h1 : term35 R) (h2 : term47 R) (h3 : term226 R m d) (h4 : term158 R m d) : False.
Proof. exact (EQ_MP (@lem286387 R m d h1 h2 h3 h4) (@lem286249 R m d h3)). Qed.
Lemma lem286389 (R : type1605) (m : nat) (d : nat) (h1 : term35 R) (h2 : term47 R) (h3 : term226 R m d) (h4 : term158 R m d) : (term158 R m d) = False.
Proof. exact (prop_ext (fun h5 : term158 R m d => @lem286388 R m d h1 h2 h3 h4) (fun h5 : False => @lem286247 R m d h4)). Qed.
Lemma lem286390 (R : type1605) (m : nat) (d : nat) (h1 : term35 R) (h2 : term47 R) (h3 : term226 R m d) (h4 : term158 R m d) : False.
Proof. exact (EQ_MP (@lem286389 R m d h1 h2 h3 h4) (@lem286247 R m d h4)). Qed.
Lemma lem286391 (R : type1605) (m : nat) (d : nat) (h1 : term35 R) (h2 : term47 R) (h3 : term226 R m d) (h4 : term158 R m d) : (term226 R m d) = False.
Proof. exact (prop_ext (fun h5 : term226 R m d => @lem286390 R m d h1 h2 h3 h4) (fun h5 : False => @lem286219 R m d h3)). Qed.
Lemma lem286392 (R : type1605) (m : nat) (d : nat) (h1 : term35 R) (h2 : term47 R) (h3 : term226 R m d) (h4 : term158 R m d) : False.
Proof. exact (EQ_MP (@lem286391 R m d h1 h2 h3 h4) (@lem286219 R m d h3)). Qed.
Lemma lem286393 (R : type1605) (m : nat) (d : nat) (h1 : term35 R) (h2 : term47 R) (h3 : term226 R m d) (h4 : term158 R m d) : (term158 R m d) = False.
Proof. exact (prop_ext (fun h5 : term158 R m d => @lem286392 R m d h1 h2 h3 h4) (fun h5 : False => @lem286215 R m d h4)). Qed.
Lemma lem286394 (R : type1605) (m : nat) (d : nat) (h1 : term35 R) (h2 : term47 R) (h3 : term226 R m d) (h4 : term158 R m d) : False.
Proof. exact (EQ_MP (@lem286393 R m d h1 h2 h3 h4) (@lem286215 R m d h4)). Qed.
Lemma lem286395 (R : type1605) (m : nat) (d : nat) (h1 : term35 R) (h2 : term47 R) (h3 : term226 R m d) (h4 : term158 R m d) : (term226 R m d) = False.
Proof. exact (prop_ext (fun h5 : term226 R m d => @lem286394 R m d h1 h2 h3 h4) (fun h5 : False => @lem286219 R m d h3)). Qed.
Lemma lem286396 (R : type1605) (m : nat) (d : nat) (h1 : term35 R) (h2 : term47 R) (h3 : term226 R m d) (h4 : term158 R m d) : False.
Proof. exact (EQ_MP (@lem286395 R m d h1 h2 h3 h4) (@lem286219 R m d h3)). Qed.
Lemma lem286397 (R : type1605) (m : nat) (d : nat) (h1 : term35 R) (h2 : term47 R) (h3 : term226 R m d) (h4 : term158 R m d) : (term158 R m d) = False.
Proof. exact (prop_ext (fun h5 : term158 R m d => @lem286396 R m d h1 h2 h3 h4) (fun h5 : False => @lem286215 R m d h4)). Qed.
Lemma lem286398 (R : type1605) (m : nat) (d : nat) (h1 : term35 R) (h2 : term47 R) (h3 : term226 R m d) (h4 : term158 R m d) : False.
Proof. exact (EQ_MP (@lem286397 R m d h1 h2 h3 h4) (@lem286215 R m d h4)). Qed.
Lemma lem286399 (R : type1605) (m : nat) (d : nat) (h1 : term35 R) (h2 : term47 R) (h3 : term226 R m d) (h4 : term158 R m d) : (term47 R) = False.
Proof. exact (prop_ext (fun h5 : term47 R => @lem286398 R m d h1 h2 h3 h4) (fun h5 : False => @lem286211 R h2)). Qed.
Lemma lem286400 (R : type1605) (m : nat) (d : nat) (h1 : term35 R) (h2 : term47 R) (h3 : term226 R m d) (h4 : term158 R m d) : False.
Proof. exact (EQ_MP (@lem286399 R m d h1 h2 h3 h4) (@lem286211 R h2)). Qed.
Lemma lem286401 (R : type1605) (m : nat) (d : nat) (h1 : term35 R) (h2 : term47 R) (h3 : term226 R m d) (h4 : term158 R m d) : (term226 R m d) = False.
Proof. exact (prop_ext (fun h5 : term226 R m d => @lem286400 R m d h1 h2 h3 h4) (fun h5 : False => @lem286179 R m d h3)). Qed.
Lemma lem286402 (R : type1605) (m : nat) (d : nat) (h1 : term35 R) (h2 : term47 R) (h3 : term226 R m d) (h4 : term158 R m d) : False.
Proof. exact (EQ_MP (@lem286401 R m d h1 h2 h3 h4) (@lem286179 R m d h3)). Qed.
Lemma lem286403 (R : type1605) (m : nat) (d : nat) (h1 : term35 R) (h2 : term47 R) (h3 : term226 R m d) (h4 : term158 R m d) : (term158 R m d) = False.
Proof. exact (prop_ext (fun h5 : term158 R m d => @lem286402 R m d h1 h2 h3 h4) (fun h5 : False => @lem286163 R m d h4)). Qed.
Lemma lem286404 (R : type1605) (m : nat) (d : nat) (h1 : term35 R) (h2 : term47 R) (h3 : term226 R m d) (h4 : term158 R m d) : False.
Proof. exact (EQ_MP (@lem286403 R m d h1 h2 h3 h4) (@lem286163 R m d h4)). Qed.
Lemma lem286405 (R : type1605) (m : nat) (d : nat) (h1 : term35 R) (h2 : term47 R) (h3 : term226 R m d) (h4 : term158 R m d) : (term47 R) = False.
Proof. exact (prop_ext (fun h5 : term47 R => @lem286404 R m d h1 h2 h3 h4) (fun h5 : False => @lem286151 R h2)). Qed.
Lemma lem286406 (R : type1605) (m : nat) (d : nat) (h1 : term35 R) (h2 : term47 R) (h3 : term226 R m d) (h4 : term158 R m d) : False.
Proof. exact (EQ_MP (@lem286405 R m d h1 h2 h3 h4) (@lem286151 R h2)). Qed.
Lemma lem286407 (R : type1605) (m : nat) (d : nat) (h1 : term35 R) (h2 : term47 R) (h3 : term226 R m d) (h4 : term158 R m d) : (term226 R m d) = False.
Proof. exact (prop_ext (fun h5 : term226 R m d => @lem286406 R m d h1 h2 h3 h4) (fun h5 : False => @lem286105 R m d h3)). Qed.
Lemma lem286408 (R : type1605) (m : nat) (d : nat) (h1 : term35 R) (h2 : term47 R) (h3 : term226 R m d) (h4 : term158 R m d) : False.
Proof. exact (EQ_MP (@lem286407 R m d h1 h2 h3 h4) (@lem286105 R m d h3)). Qed.
Lemma lem286409 (R : type1605) (m : nat) (d : nat) (h1 : term35 R) (h2 : term47 R) (h3 : term226 R m d) (h4 : term158 R m d) : (term158 R m d) = False.
Proof. exact (prop_ext (fun h5 : term158 R m d => @lem286408 R m d h1 h2 h3 h4) (fun h5 : False => @lem286099 R m d h4)). Qed.
Lemma lem286410 (R : type1605) (m : nat) (d : nat) (h1 : term35 R) (h2 : term47 R) (h3 : term226 R m d) (h4 : term158 R m d) : False.
Proof. exact (EQ_MP (@lem286409 R m d h1 h2 h3 h4) (@lem286099 R m d h4)). Qed.
Lemma lem286411 (R : type1605) (m : nat) (d : nat) (h1 : term35 R) (h2 : term47 R) (h3 : term226 R m d) (h4 : term158 R m d) : (term47 R) = False.
Proof. exact (prop_ext (fun h5 : term47 R => @lem286410 R m d h1 h2 h3 h4) (fun h5 : False => @lem286093 R h2)). Qed.
Lemma lem286412 (R : type1605) (m : nat) (d : nat) (h1 : term35 R) (h2 : term47 R) (h3 : term226 R m d) (h4 : term158 R m d) : False.
Proof. exact (EQ_MP (@lem286411 R m d h1 h2 h3 h4) (@lem286093 R h2)). Qed.
Lemma lem286413 (R : type1605) (m : nat) (d : nat) (h1 : term35 R) (h2 : term47 R) (h3 : term226 R m d) (h4 : term158 R m d) : (term226 R m d) = False.
Proof. exact (prop_ext (fun h5 : term226 R m d => @lem286412 R m d h1 h2 h3 h4) (fun h5 : False => @lem285997 R m d h3)). Qed.
Lemma lem286414 (R : type1605) (m : nat) (d : nat) (h1 : term35 R) (h2 : term47 R) (h3 : term226 R m d) (h4 : term158 R m d) : False.
Proof. exact (EQ_MP (@lem286413 R m d h1 h2 h3 h4) (@lem285997 R m d h3)). Qed.
Lemma lem286415 (R : type1605) (m : nat) (d : nat) (h1 : term35 R) (h2 : term47 R) (h3 : term158 R m d) : term225 R m d.
Proof. exact (fun h0 : term226 R m d => @lem286414 R m d h1 h2 h0 h3). Qed.
Lemma lem286416 (R : type1605) (m : nat) (d : nat) (h1 : term35 R) (h2 : term47 R) (h3 : term158 R m d) : term189 R m d.
Proof. exact (EQ_MP (@lem285996 R m d) (@lem286415 R m d h1 h2 h3)). Qed.
Lemma lem286417 (m : nat) (d : nat) (R : type1605) (h1 : term35 R) (h2 : term47 R) : term233 R m d.
Proof. exact (fun h0 : term158 R m d => @lem286416 R m d h1 h2 h0). Qed.
Lemma lem286418 (m : nat) (d : nat) (R : type1605) (h1 : term35 R) : term235 R m d.
Proof. exact (fun h0 : term47 R => @lem286417 m d R h1 h0). Qed.
Lemma lem286419 (R : type1605) (m : nat) (d : nat) : term236 R m d.
Proof. exact (fun h0 : term35 R => @lem286418 m d R h0). Qed.
Lemma lem286424 (m : nat) (d : nat) : term240 m d.
Proof. exact (fun R : type1605 => @lem286419 R m d). Qed.
Lemma lem286429 (d : nat) : term244 d.
Proof. exact (fun m : nat => @lem286424 m d). Qed.
Lemma lem286434 : term248.
Proof. exact (fun d : nat => @lem286429 d). Qed.
Lemma lem286435 : term247.
Proof. exact (EQ_MP (@lem285989) (@lem286434)). Qed.
Lemma lem286436 (d : nat) : term294 d.
Proof. exact (@lem286435 d). Qed.
Lemma lem286437 (d : nat) : (term294 d) = (term243 d).
Proof. exact (eq_refl (term294 d)). Qed.
Lemma lem286438 (d : nat) : term243 d.
Proof. exact (EQ_MP (@lem286437 d) (@lem286436 d)). Qed.
Lemma lem286439 (d : nat) (m : nat) : term295 d m.
Proof. exact (@lem286438 d m). Qed.
Lemma lem286440 (m : nat) (d : nat) : (term295 d m) = (term239 m d).
Proof. exact (eq_refl (term295 d m)). Qed.
Lemma lem286441 (m : nat) (d : nat) : term239 m d.
Proof. exact (EQ_MP (@lem286440 m d) (@lem286439 d m)). Qed.
Lemma lem286442 (m : nat) (d : nat) (R : type1605) : term296 m d R.
Proof. exact (@lem286441 m d R). Qed.
Lemma lem286443 (R : type1605) (m : nat) (d : nat) : (term296 m d R) = (term227 R m d).
Proof. exact (eq_refl (term296 m d R)). Qed.
Lemma lem286444 (R : type1605) (m : nat) (d : nat) : term227 R m d.
Proof. exact (EQ_MP (@lem286443 R m d) (@lem286442 m d R)). Qed.
Lemma lem286446 (R : type1605) (m : nat) (d : nat) : term227 R m d.
Proof. exact (@lem285809 R m d (@lem286444 R m d)). Qed.
Lemma lem286447 (m : nat) (d : nat) (R : type1605) (h1 : term35 R) : term234 R m d.
Proof. exact (@lem286446 R m d (@lem283572 R h1)). Qed.
Lemma lem286448 (m : nat) (d : nat) (R : type1605) (h1 : term35 R) (h2 : term47 R) : term232 R m d.
Proof. exact (@lem286447 m d R h1 (@lem284864 R h2)). Qed.
Lemma lem286449 (R : type1605) (m : nat) (d : nat) (h1 : term35 R) (h2 : term47 R) (h3 : term158 R m d) : term225 R m d.
Proof. exact (@lem286448 m d R h1 h2 (@lem285305 R m d h3)). Qed.
Lemma lem286450 (R : type1605) (m : nat) (d : nat) (h1 : term35 R) (h2 : term47 R) (h3 : term226 R m d) (h4 : term158 R m d) : False.
Proof. exact (@lem286449 R m d h1 h2 h4 (@lem285794 R m d h3)). Qed.
Lemma lem286451 (R : type1605) (m : nat) (d : nat) (h1 : term35 R) (h2 : term47 R) (h3 : term226 R m d) (h4 : term158 R m d) : (term226 R m d) = False.
Proof. exact (prop_ext (fun h5 : term226 R m d => @lem286450 R m d h1 h2 h3 h4) (fun h5 : False => @lem285794 R m d h3)). Qed.
Lemma lem286452 (R : type1605) (m : nat) (d : nat) (h1 : term35 R) (h2 : term47 R) (h3 : term226 R m d) (h4 : term158 R m d) : False.
Proof. exact (EQ_MP (@lem286451 R m d h1 h2 h3 h4) (@lem285794 R m d h3)). Qed.
Lemma lem286453 (R : type1605) (m : nat) (d : nat) (h1 : term35 R) (h2 : term47 R) (h3 : term158 R m d) : term225 R m d.
Proof. exact (fun h0 : term226 R m d => @lem286452 R m d h1 h2 h0 h3). Qed.
Lemma lem286454 (R : type1605) (m : nat) (d : nat) (h1 : term35 R) (h2 : term47 R) (h3 : term158 R m d) : term189 R m d.
Proof. exact (EQ_MP (@lem285793 R m d) (@lem286453 R m d h1 h2 h3)). Qed.
Lemma lem286455 (R : type1605) (m : nat) (d : nat) (h1 : term35 R) (h2 : term47 R) (h3 : term158 R m d) : term172 R m d.
Proof. exact (EQ_MP (@lem285320 R m d) (@lem286454 R m d h1 h2 h3)). Qed.
Lemma lem286456 (m : nat) (R : type1605) (h1 : term35 R) (h2 : term47 R) : term165 R m.
Proof. exact (EQ_MP (@lem285312 R m) (@lem285789 m R h1 h2)). Qed.
Lemma lem286457 (m : nat) (d : nat) (R : type1605) (h1 : term35 R) (h2 : term47 R) : term174 R m d.
Proof. exact (fun h0 : term158 R m d => @lem286455 R m d h1 h2 h0). Qed.
Lemma lem286462 (m : nat) (R : type1605) (h1 : term35 R) (h2 : term47 R) : term178 R m.
Proof. exact (fun d : nat => @lem286457 m d R h1 h2). Qed.
Lemma lem286463 (m : nat) (R : type1605) (h1 : term35 R) (h2 : term47 R) : term180 R m.
Proof. exact (conj (@lem286456 m R h1 h2) (@lem286462 m R h1 h2)). Qed.
Lemma lem286464 (m : nat) (R : type1605) (h1 : term35 R) (h2 : term47 R) : term161 R m.
Proof. exact (@lem285304 R m (@lem286463 m R h1 h2)). Qed.
Lemma lem286465 (m : nat) (R : type1605) (h1 : term35 R) (h2 : term47 R) : term141 R m.
Proof. exact (EQ_MP (@lem285281 R m) (@lem286464 m R h1 h2)). Qed.
Lemma lem286466 (m : nat) (R : type1605) (h1 : term35 R) (h2 : term47 R) : term118 R m.
Proof. exact (EQ_MP (@lem285226 R m) (@lem286465 m R h1 h2)). Qed.
Lemma lem286471 (R : type1605) (h1 : term35 R) (h2 : term47 R) : term121 R.
Proof. exact (fun m : nat => @lem286466 m R h1 h2). Qed.
Lemma lem286472 (R : type1605) (h1 : term35 R) (h2 : term47 R) : term46 R.
Proof. exact (EQ_MP (@lem285195 R) (@lem286471 R h1 h2)). Qed.
Lemma lem286474 (R : type1605) (h1 : term35 R) : term297 R.
Proof. exact (fun h0 : term47 R => @lem286472 R h1 h0). Qed.
Lemma lem286475 (R : type1605) (h1 : term35 R) : term298 R.
Proof. exact (conj (@lem284104 R) (@lem286474 R h1)). Qed.
Lemma lem286476 (R : type1605) : (term298 R) = ((term46 R) = (term47 R)).
Proof. exact (@lem32 (term46 R) (term47 R)). Qed.
Lemma lem286477 (R : type1605) (h1 : term35 R) : (term46 R) = (term47 R).
Proof. exact (EQ_MP (@lem286476 R) (@lem286475 R h1)). Qed.
Lemma lem286478 (R : type1605) (h1 : term35 R) : (term35 R) = ((term46 R) = (term47 R)).
Proof. exact (prop_ext (fun h2 : term35 R => @lem286477 R h1) (fun h2 : (term46 R) = (term47 R) => @lem283572 R h1)). Qed.
Lemma lem286479 (R : type1605) (h1 : term35 R) : (term46 R) = (term47 R).
Proof. exact (EQ_MP (@lem286478 R h1) (@lem283572 R h1)). Qed.
Lemma lem286480 (R : type1605) : term299 R.
Proof. exact (fun h0 : term35 R => @lem286479 R h0). Qed.
Lemma lem286485 : term300.
Proof. exact (fun R : type1605 => @lem286480 R). Qed.
