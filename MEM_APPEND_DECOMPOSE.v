Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MEM_APPEND_DECOMPOSE_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import LEFT_IMP_EXISTS_THM_spec.
Require Import MEM_APPEND_spec.
Require Import MEM_APPEND_DECOMPOSE_LEFT_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1103200_spec.
Require Import thm1103201_spec.
Require Import thm16433_spec.
Require Import thm16434_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1820_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm1823_spec.
Require Import thm1831_spec.
Require Import thm1832_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1855_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm4211_spec.
Lemma lem1221481 {A : Type'} (x : A) : term0 A x.
Proof. exact (@lem1221470 A x). Qed.
Lemma lem1221482 {A : Type'} (x : A) : (term0 A x) = (term1 A x).
Proof. exact (eq_refl (term0 A x)). Qed.
Lemma lem1221483 {A : Type'} (x : A) : term1 A x.
Proof. exact (EQ_MP (@lem1221482 A x) (@lem1221481 A x)). Qed.
Lemma lem1221484 {A : Type'} (x : A) (l : list A) : term2 A x l.
Proof. exact (@lem1221483 A x l). Qed.
Lemma lem1221485 {A : Type'} (l : list A) (x : A) : (term2 A x l) = ((@List.In A x l) = (term3 A l x)).
Proof. exact (eq_refl (term2 A x l)). Qed.
Lemma lem1221489 {_26945 : Type'} (x : _26945) : term4 _26945 x.
Proof. exact (@lem1145802 _26945 x). Qed.
Lemma lem1221490 {_26945 : Type'} (x : _26945) : (term4 _26945 x) = (term5 _26945 x).
Proof. exact (eq_refl (term4 _26945 x)). Qed.
Lemma lem1221491 {_26945 : Type'} (x : _26945) : term5 _26945 x.
Proof. exact (EQ_MP (@lem1221490 _26945 x) (@lem1221489 _26945 x)). Qed.
Lemma lem1221492 {_26945 : Type'} (x : _26945) (l1 : list _26945) : term6 _26945 x l1.
Proof. exact (@lem1221491 _26945 x l1). Qed.
Lemma lem1221493 {_26945 : Type'} (l1 : list _26945) (x : _26945) : (term6 _26945 x l1) = (term7 _26945 l1 x).
Proof. exact (eq_refl (term6 _26945 x l1)). Qed.
Lemma lem1221494 {_26945 : Type'} (l1 : list _26945) (x : _26945) : term7 _26945 l1 x.
Proof. exact (EQ_MP (@lem1221493 _26945 l1 x) (@lem1221492 _26945 x l1)). Qed.
Lemma lem1221495 {_26945 : Type'} (l1 : list _26945) (x : _26945) (l2 : list _26945) : term8 _26945 l1 x l2.
Proof. exact (@lem1221494 _26945 l1 x l2). Qed.
Lemma lem1221496 {_26945 : Type'} (l1 : list _26945) (x : _26945) (l2 : list _26945) : (term8 _26945 l1 x l2) = ((term9 _26945 x l1 l2) = (term10 _26945 l1 x l2)).
Proof. exact (eq_refl (term8 _26945 l1 x l2)). Qed.
Lemma lem1221498 {A : Type'} (P : A -> Prop) : term11 A P.
Proof. exact (@lem6644 A P). Qed.
Lemma lem1221499 {A : Type'} (P : A -> Prop) : (term11 A P) = (term12 A P).
Proof. exact (eq_refl (term11 A P)). Qed.
Lemma lem1221500 {A : Type'} (P : A -> Prop) : term12 A P.
Proof. exact (EQ_MP (@lem1221499 A P) (@lem1221498 A P)). Qed.
Lemma lem1221501 {A : Type'} (P : A -> Prop) (Q : Prop) : term13 A P Q.
Proof. exact (@lem1221500 A P Q). Qed.
Lemma lem1221502 {A : Type'} (P : A -> Prop) (Q : Prop) : (term13 A P Q) = ((term14 A P Q) = (term15 A P Q)).
Proof. exact (eq_refl (term13 A P Q)). Qed.
Lemma lem1221516 (p : Prop) : term16 p.
Proof. exact (@lem9851 p). Qed.
Lemma lem1221517 (p : Prop) : (term16 p) = (term17 p).
Proof. exact (eq_refl (term16 p)). Qed.
Lemma lem1221518 (p : Prop) : term17 p.
Proof. exact (EQ_MP (@lem1221517 p) (@lem1221516 p)). Qed.
Lemma lem1221519 (p : Prop) (h1 : p = True) : p = True.
Proof. exact (h1). Qed.
Lemma lem1221520 (p : Prop) (h1 : p = False) : p = False.
Proof. exact (h1). Qed.
Lemma lem1221533 (q : Prop) : (term18 q) = (term18 q).
Proof. exact (eq_refl (term18 q)). Qed.
Lemma lem1221534 (q : Prop) (p : Prop) (h1 : p = True) : (term19 q p) = (term20 q).
Proof. exact (MK_COMB (@lem1221533 q) (@lem1221519 p h1)). Qed.
Lemma lem1221535 (q : Prop) : (term20 q) = ((True = q) = (term21 q)).
Proof. exact (eq_refl (term20 q)). Qed.
Lemma lem1221536 (q : Prop) (p : Prop) : (term22 q p) = (term22 q p).
Proof. exact (eq_refl (term22 q p)). Qed.
Lemma lem1221537 (p : Prop) (q : Prop) : ((term19 q p) = (term20 q)) = ((term19 q p) = ((True = q) = (term21 q))).
Proof. exact (MK_COMB (@lem1221536 q p) (@lem1221535 q)). Qed.
Lemma lem1221538 (q : Prop) (p : Prop) : (term19 q p) = ((p = q) = (term23 q p)).
Proof. exact (eq_refl (term19 q p)). Qed.
Lemma lem1221539 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1221540 (q : Prop) (p : Prop) : (term22 q p) = (term24 q p).
Proof. exact (MK_COMB (@lem1221539) (@lem1221538 q p)). Qed.
Lemma lem1221541 (q : Prop) : ((True = q) = (term21 q)) = ((True = q) = (term21 q)).
Proof. exact (eq_refl ((True = q) = (term21 q))). Qed.
Lemma lem1221542 (p : Prop) (q : Prop) : ((term19 q p) = ((True = q) = (term21 q))) = (((p = q) = (term23 q p)) = ((True = q) = (term21 q))).
Proof. exact (MK_COMB (@lem1221540 q p) (@lem1221541 q)). Qed.
Lemma lem1221543 (p : Prop) (q : Prop) : ((term19 q p) = (term20 q)) = (((p = q) = (term23 q p)) = ((True = q) = (term21 q))).
Proof. exact (TRANS (@lem1221537 p q) (@lem1221542 p q)). Qed.
Lemma lem1221544 (q : Prop) (p : Prop) (h1 : p = True) : ((p = q) = (term23 q p)) = ((True = q) = (term21 q)).
Proof. exact (EQ_MP (@lem1221543 p q) (@lem1221534 q p h1)). Qed.
Lemma lem1221545 (q : Prop) (p : Prop) (h1 : p = True) : ((True = q) = (term21 q)) = ((p = q) = (term23 q p)).
Proof. exact (SYM (@lem1221544 q p h1)). Qed.
Lemma lem1221546 (q : Prop) : (term18 q) = (term18 q).
Proof. exact (eq_refl (term18 q)). Qed.
Lemma lem1221547 (q : Prop) (p : Prop) (h1 : p = False) : (term19 q p) = (term25 q).
Proof. exact (MK_COMB (@lem1221546 q) (@lem1221520 p h1)). Qed.
Lemma lem1221548 (q : Prop) : (term25 q) = ((False = q) = (term26 q)).
Proof. exact (eq_refl (term25 q)). Qed.
Lemma lem1221549 (q : Prop) (p : Prop) : (term22 q p) = (term22 q p).
Proof. exact (eq_refl (term22 q p)). Qed.
Lemma lem1221550 (p : Prop) (q : Prop) : ((term19 q p) = (term25 q)) = ((term19 q p) = ((False = q) = (term26 q))).
Proof. exact (MK_COMB (@lem1221549 q p) (@lem1221548 q)). Qed.
Lemma lem1221551 (q : Prop) (p : Prop) : (term19 q p) = ((p = q) = (term23 q p)).
Proof. exact (eq_refl (term19 q p)). Qed.
Lemma lem1221552 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1221553 (q : Prop) (p : Prop) : (term22 q p) = (term24 q p).
Proof. exact (MK_COMB (@lem1221552) (@lem1221551 q p)). Qed.
Lemma lem1221554 (q : Prop) : ((False = q) = (term26 q)) = ((False = q) = (term26 q)).
Proof. exact (eq_refl ((False = q) = (term26 q))). Qed.
Lemma lem1221555 (p : Prop) (q : Prop) : ((term19 q p) = ((False = q) = (term26 q))) = (((p = q) = (term23 q p)) = ((False = q) = (term26 q))).
Proof. exact (MK_COMB (@lem1221553 q p) (@lem1221554 q)). Qed.
Lemma lem1221556 (p : Prop) (q : Prop) : ((term19 q p) = (term25 q)) = (((p = q) = (term23 q p)) = ((False = q) = (term26 q))).
Proof. exact (TRANS (@lem1221550 p q) (@lem1221555 p q)). Qed.
Lemma lem1221557 (q : Prop) (p : Prop) (h1 : p = False) : ((p = q) = (term23 q p)) = ((False = q) = (term26 q)).
Proof. exact (EQ_MP (@lem1221556 p q) (@lem1221547 q p h1)). Qed.
Lemma lem1221558 (q : Prop) (p : Prop) (h1 : p = False) : ((False = q) = (term26 q)) = ((p = q) = (term23 q p)).
Proof. exact (SYM (@lem1221557 q p h1)). Qed.
Lemma lem1221562 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem1221563 (q : Prop) : (True = q) = q.
Proof. exact (@lem1221562 q). Qed.
Lemma lem1221564 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1221565 (q : Prop) : (term27 q) = (@eq Prop q).
Proof. exact (MK_COMB (@lem1221564) (@lem1221563 q)). Qed.
Lemma lem1221569 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem1221570 (q : Prop) : (True -> q) = q.
Proof. exact (@lem1221569 q). Qed.
Lemma lem1221571 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1221572 (q : Prop) : (term28 q) = (and q).
Proof. exact (MK_COMB (@lem1221571) (@lem1221570 q)). Qed.
Lemma lem1221574 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1221575 (q : Prop) : (q -> True) = True.
Proof. exact (@lem1221574 q). Qed.
Lemma lem1221576 (q : Prop) : (term21 q) = (q /\ True).
Proof. exact (MK_COMB (@lem1221572 q) (@lem1221575 q)). Qed.
Lemma lem1221578 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem1221579 (q : Prop) : (q /\ True) = q.
Proof. exact (@lem1221578 q). Qed.
Lemma lem1221580 (q : Prop) : (term21 q) = q.
Proof. exact (TRANS (@lem1221576 q) (@lem1221579 q)). Qed.
Lemma lem1221581 (q : Prop) : ((True = q) = (term21 q)) = (q = q).
Proof. exact (MK_COMB (@lem1221565 q) (@lem1221580 q)). Qed.
Lemma lem1221583 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1221584 (x : Prop) : (x = x) = True.
Proof. exact (@lem1221583 Prop x). Qed.
Lemma lem1221585 (q : Prop) : (q = q) = True.
Proof. exact (@lem1221584 q). Qed.
Lemma lem1221586 (q : Prop) : ((True = q) = (term21 q)) = True.
Proof. exact (TRANS (@lem1221581 q) (@lem1221585 q)). Qed.
Lemma lem1221587 (q : Prop) : True = ((True = q) = (term21 q)).
Proof. exact (SYM (@lem1221586 q)). Qed.
Lemma lem1221588 (q : Prop) : (True = q) = (term21 q).
Proof. exact (EQ_MP (@lem1221587 q) (@lem0)). Qed.
Lemma lem1221592 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem1221593 (q : Prop) : (False = q) = (~ q).
Proof. exact (@lem1221592 q). Qed.
Lemma lem1221594 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1221595 (q : Prop) : (term29 q) = (term30 q).
Proof. exact (MK_COMB (@lem1221594) (@lem1221593 q)). Qed.
Lemma lem1221599 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem1221600 (q : Prop) : (False -> q) = True.
Proof. exact (@lem1221599 q). Qed.
Lemma lem1221601 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1221602 (q : Prop) : (term31 q) = (and True).
Proof. exact (MK_COMB (@lem1221601) (@lem1221600 q)). Qed.
Lemma lem1221604 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem1221605 (q : Prop) : (q -> False) = (~ q).
Proof. exact (@lem1221604 q). Qed.
Lemma lem1221606 (q : Prop) : (term26 q) = (term32 q).
Proof. exact (MK_COMB (@lem1221602 q) (@lem1221605 q)). Qed.
Lemma lem1221608 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1221609 (q : Prop) : (term32 q) = (~ q).
Proof. exact (@lem1221608 (~ q)). Qed.
Lemma lem1221610 (q : Prop) : (term26 q) = (~ q).
Proof. exact (TRANS (@lem1221606 q) (@lem1221609 q)). Qed.
Lemma lem1221611 (q : Prop) : ((False = q) = (term26 q)) = ((~ q) = (~ q)).
Proof. exact (MK_COMB (@lem1221595 q) (@lem1221610 q)). Qed.
Lemma lem1221613 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1221614 (x : Prop) : (x = x) = True.
Proof. exact (@lem1221613 Prop x). Qed.
Lemma lem1221615 (q : Prop) : ((~ q) = (~ q)) = True.
Proof. exact (@lem1221614 (~ q)). Qed.
Lemma lem1221616 (q : Prop) : ((False = q) = (term26 q)) = True.
Proof. exact (TRANS (@lem1221611 q) (@lem1221615 q)). Qed.
Lemma lem1221617 (q : Prop) : True = ((False = q) = (term26 q)).
Proof. exact (SYM (@lem1221616 q)). Qed.
Lemma lem1221618 (q : Prop) : (False = q) = (term26 q).
Proof. exact (EQ_MP (@lem1221617 q) (@lem0)). Qed.
Lemma lem1221619 (q : Prop) (p : Prop) (h1 : p = False) : (p = q) = (term23 q p).
Proof. exact (EQ_MP (@lem1221558 q p h1) (@lem1221618 q)). Qed.
Lemma lem1221620 (q : Prop) (p : Prop) (h1 : p = True) : (p = q) = (term23 q p).
Proof. exact (EQ_MP (@lem1221545 q p h1) (@lem1221588 q)). Qed.
Lemma lem1221635 (q : Prop) (p : Prop) : (p = q) = (term23 q p).
Proof. exact (or_elim (@lem1221518 p) (fun h0 : p = True => @lem1221620 q p h0) (fun h0 : p = False => @lem1221619 q p h0)). Qed.
Lemma lem1221636 {A : Type'} (x : A) (l : list A) : ((@List.In A x l) = (term33 A l x)) = (term34 A x l).
Proof. exact (@lem1221635 (term33 A l x) (@List.In A x l)). Qed.
Lemma lem1221667 {A : Type'} (x : A) : (term35 A x) = (term36 A x).
Proof. exact (fun_ext (fun l : list A => @lem1221636 A x l)). Qed.
Lemma lem1221668 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1221669 {A : Type'} (x : A) : (term37 A x) = (term38 A x).
Proof. exact (MK_COMB (@lem1221668 A) (@lem1221667 A x)). Qed.
Lemma lem1221674 {A : Type'} : (term39 A) = (term40 A).
Proof. exact (fun_ext (fun x : A => @lem1221669 A x)). Qed.
Lemma lem1221675 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1221676 {A : Type'} : (term41 A) = (term42 A).
Proof. exact (MK_COMB (@lem1221675 A) (@lem1221674 A)). Qed.
Lemma lem1221681 {A : Type'} : (term42 A) = (term41 A).
Proof. exact (SYM (@lem1221676 A)). Qed.
Lemma lem1221736 {A : Type'} (P : A -> Prop) (Q : Prop) : (term14 A P Q) = (term15 A P Q).
Proof. exact (EQ_MP (@lem1221502 A P Q) (@lem1221501 A P Q)). Qed.
Lemma lem1221737 {A : Type'} (P : type1143 A) (Q : Prop) : (term43 A P Q) = (term44 A P Q).
Proof. exact (@lem1221736 (list A) P Q). Qed.
Lemma lem1221738 {A : Type'} (x : A) (l : list A) : (term45 A x l) = (term46 A x l).
Proof. exact (@lem1221737 A (term47 A l x) (@List.In A x l)). Qed.
Lemma lem1221739 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term48 A l x l1) = (term49 A l l1 x).
Proof. exact (eq_refl (term48 A l x l1)). Qed.
Lemma lem1221740 {A : Type'} (l : list A) (x : A) : (term50 A l x) = (term47 A l x).
Proof. exact (fun_ext (fun l1 : list A => @lem1221739 A l l1 x)). Qed.
Lemma lem1221741 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1221742 {A : Type'} (l : list A) (x : A) : (term51 A l x) = (term33 A l x).
Proof. exact (MK_COMB (@lem1221741 A) (@lem1221740 A l x)). Qed.
Lemma lem1221743 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1221744 {A : Type'} (l : list A) (x : A) : (term52 A l x) = (term53 A l x).
Proof. exact (MK_COMB (@lem1221743) (@lem1221742 A l x)). Qed.
Lemma lem1221745 {A : Type'} (x : A) (l : list A) : (@List.In A x l) = (@List.In A x l).
Proof. exact (eq_refl (@List.In A x l)). Qed.
Lemma lem1221746 {A : Type'} (x : A) (l : list A) : (term45 A x l) = (term54 A x l).
Proof. exact (MK_COMB (@lem1221744 A l x) (@lem1221745 A x l)). Qed.
Lemma lem1221747 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1221748 {A : Type'} (x : A) (l : list A) : (term55 A x l) = (term56 A x l).
Proof. exact (MK_COMB (@lem1221747) (@lem1221746 A x l)). Qed.
Lemma lem1221749 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term48 A l x l1) = (term49 A l l1 x).
Proof. exact (eq_refl (term48 A l x l1)). Qed.
Lemma lem1221750 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1221751 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term57 A l x l1) = (term58 A l l1 x).
Proof. exact (MK_COMB (@lem1221750) (@lem1221749 A l l1 x)). Qed.
Lemma lem1221752 {A : Type'} (x : A) (l : list A) : (@List.In A x l) = (@List.In A x l).
Proof. exact (eq_refl (@List.In A x l)). Qed.
Lemma lem1221753 {A : Type'} (l1 : list A) (x : A) (l : list A) : (term59 A l1 x l) = (term60 A l1 x l).
Proof. exact (MK_COMB (@lem1221751 A l l1 x) (@lem1221752 A x l)). Qed.
Lemma lem1221754 {A : Type'} (x : A) (l : list A) : (term61 A x l) = (term62 A x l).
Proof. exact (fun_ext (fun l1 : list A => @lem1221753 A l1 x l)). Qed.
Lemma lem1221755 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1221756 {A : Type'} (x : A) (l : list A) : (term46 A x l) = (term63 A x l).
Proof. exact (MK_COMB (@lem1221755 A) (@lem1221754 A x l)). Qed.
Lemma lem1221757 {A : Type'} (x : A) (l : list A) : ((term45 A x l) = (term46 A x l)) = ((term54 A x l) = (term63 A x l)).
Proof. exact (MK_COMB (@lem1221748 A x l) (@lem1221756 A x l)). Qed.
Lemma lem1221758 {A : Type'} (x : A) (l : list A) : (term54 A x l) = (term63 A x l).
Proof. exact (EQ_MP (@lem1221757 A x l) (@lem1221738 A x l)). Qed.
Lemma lem1221764 {A : Type'} (P : A -> Prop) (Q : Prop) : (term14 A P Q) = (term15 A P Q).
Proof. exact (EQ_MP (@lem1221502 A P Q) (@lem1221501 A P Q)). Qed.
Lemma lem1221765 {A : Type'} (P : type1143 A) (Q : Prop) : (term43 A P Q) = (term44 A P Q).
Proof. exact (@lem1221764 (list A) P Q). Qed.
Lemma lem1221766 {A : Type'} (l1 : list A) (x : A) (l : list A) : (term64 A l1 x l) = (term65 A l1 x l).
Proof. exact (@lem1221765 A (term66 A l l1 x) (@List.In A x l)). Qed.
Lemma lem1221767 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term67 A l l1 x l2) = (l = (term68 A l1 x l2)).
Proof. exact (eq_refl (term67 A l l1 x l2)). Qed.
Lemma lem1221768 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term69 A l l1 x) = (term66 A l l1 x).
Proof. exact (fun_ext (fun l2 : list A => @lem1221767 A l l1 x l2)). Qed.
Lemma lem1221769 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1221770 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term70 A l l1 x) = (term49 A l l1 x).
Proof. exact (MK_COMB (@lem1221769 A) (@lem1221768 A l l1 x)). Qed.
Lemma lem1221771 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1221772 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term71 A l l1 x) = (term58 A l l1 x).
Proof. exact (MK_COMB (@lem1221771) (@lem1221770 A l l1 x)). Qed.
Lemma lem1221773 {A : Type'} (x : A) (l : list A) : (@List.In A x l) = (@List.In A x l).
Proof. exact (eq_refl (@List.In A x l)). Qed.
Lemma lem1221774 {A : Type'} (l1 : list A) (x : A) (l : list A) : (term64 A l1 x l) = (term60 A l1 x l).
Proof. exact (MK_COMB (@lem1221772 A l l1 x) (@lem1221773 A x l)). Qed.
Lemma lem1221775 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1221776 {A : Type'} (l1 : list A) (x : A) (l : list A) : (term72 A l1 x l) = (term73 A l1 x l).
Proof. exact (MK_COMB (@lem1221775) (@lem1221774 A l1 x l)). Qed.
Lemma lem1221777 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term67 A l l1 x l2) = (l = (term68 A l1 x l2)).
Proof. exact (eq_refl (term67 A l l1 x l2)). Qed.
Lemma lem1221778 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1221779 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term74 A l l1 x l2) = (term75 A l l1 x l2).
Proof. exact (MK_COMB (@lem1221778) (@lem1221777 A l l1 x l2)). Qed.
Lemma lem1221780 {A : Type'} (x : A) (l : list A) : (@List.In A x l) = (@List.In A x l).
Proof. exact (eq_refl (@List.In A x l)). Qed.
Lemma lem1221781 {A : Type'} (l1 : list A) (l2 : list A) (x : A) (l : list A) : (term76 A l1 l2 x l) = (term77 A l1 l2 x l).
Proof. exact (MK_COMB (@lem1221779 A l l1 x l2) (@lem1221780 A x l)). Qed.
Lemma lem1221782 {A : Type'} (l1 : list A) (x : A) (l : list A) : (term78 A l1 x l) = (term79 A l1 x l).
Proof. exact (fun_ext (fun l2 : list A => @lem1221781 A l1 l2 x l)). Qed.
Lemma lem1221783 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1221784 {A : Type'} (l1 : list A) (x : A) (l : list A) : (term65 A l1 x l) = (term80 A l1 x l).
Proof. exact (MK_COMB (@lem1221783 A) (@lem1221782 A l1 x l)). Qed.
Lemma lem1221785 {A : Type'} (l1 : list A) (x : A) (l : list A) : ((term64 A l1 x l) = (term65 A l1 x l)) = ((term60 A l1 x l) = (term80 A l1 x l)).
Proof. exact (MK_COMB (@lem1221776 A l1 x l) (@lem1221784 A l1 x l)). Qed.
Lemma lem1221786 {A : Type'} (l1 : list A) (x : A) (l : list A) : (term60 A l1 x l) = (term80 A l1 x l).
Proof. exact (EQ_MP (@lem1221785 A l1 x l) (@lem1221766 A l1 x l)). Qed.
Lemma lem1221796 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term81 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1221797 (p : Prop) (q : Prop) (p' : Prop) : term82 p q p'.
Proof. exact (fun q' : Prop => @lem1221796 p q p' q'). Qed.
Lemma lem1221798 (p : Prop) (q : Prop) : term83 p q.
Proof. exact (fun p' : Prop => @lem1221797 p q p'). Qed.
Lemma lem1221799 {A : Type'} (l1 : list A) (l2 : list A) (x : A) (l : list A) : term84 A l1 l2 x l.
Proof. exact (@lem1221798 (l = (term68 A l1 x l2)) (@List.In A x l)). Qed.
Lemma lem1221800 {A : Type'} (l1 : list A) (l2 : list A) (x : A) (l : list A) (p' : Prop) : term85 A l1 l2 x l p'.
Proof. exact (@lem1221799 A l1 l2 x l p'). Qed.
Lemma lem1221801 {A : Type'} (l1 : list A) (l2 : list A) (x : A) (l : list A) (p' : Prop) : (term85 A l1 l2 x l p') = (term86 A l1 l2 x l p').
Proof. exact (eq_refl (term85 A l1 l2 x l p')). Qed.
Lemma lem1221802 {A : Type'} (l1 : list A) (l2 : list A) (x : A) (l : list A) (p' : Prop) : term86 A l1 l2 x l p'.
Proof. exact (EQ_MP (@lem1221801 A l1 l2 x l p') (@lem1221800 A l1 l2 x l p')). Qed.
Lemma lem1221803 {A : Type'} (l1 : list A) (l2 : list A) (x : A) (l : list A) (p' : Prop) (q' : Prop) : term87 A l1 l2 x l p' q'.
Proof. exact (@lem1221802 A l1 l2 x l p' q'). Qed.
Lemma lem1221804 {A : Type'} (l1 : list A) (l2 : list A) (x : A) (l : list A) (p' : Prop) (q' : Prop) : (term87 A l1 l2 x l p' q') = (term88 A l1 l2 x l p' q').
Proof. exact (eq_refl (term87 A l1 l2 x l p' q')). Qed.
Lemma lem1221805 {A : Type'} (l1 : list A) (l2 : list A) (x : A) (l : list A) (p' : Prop) (q' : Prop) : term88 A l1 l2 x l p' q'.
Proof. exact (EQ_MP (@lem1221804 A l1 l2 x l p' q') (@lem1221803 A l1 l2 x l p' q')). Qed.
Lemma lem1221808 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) : (l = (term68 A l1 x l2)) = (l = (term68 A l1 x l2)).
Proof. exact (eq_refl (l = (term68 A l1 x l2))). Qed.
Lemma lem1221809 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) (q' : Prop) : term89 A l l1 x l2 q'.
Proof. exact (@lem1221805 A l1 l2 x l (l = (term68 A l1 x l2)) q'). Qed.
Lemma lem1221810 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) (q' : Prop) : term90 A l l1 x l2 q'.
Proof. exact (@lem1221809 A l l1 x l2 q' (@lem1221808 A l l1 x l2)). Qed.
Lemma lem1221813 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) (h1 : l = (term68 A l1 x l2)) : l = (term68 A l1 x l2).
Proof. exact (h1). Qed.
Lemma lem1221814 {A : Type'} (x : A) : (@List.In A x) = (@List.In A x).
Proof. exact (eq_refl (@List.In A x)). Qed.
Lemma lem1221815 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) (h1 : l = (term68 A l1 x l2)) : (@List.In A x l) = (term91 A l1 x l2).
Proof. exact (MK_COMB (@lem1221814 A x) (@lem1221813 A l l1 x l2 h1)). Qed.
Lemma lem1221817 {_26945 : Type'} (l1 : list _26945) (x : _26945) (l2 : list _26945) : (term9 _26945 x l1 l2) = (term10 _26945 l1 x l2).
Proof. exact (EQ_MP (@lem1221496 _26945 l1 x l2) (@lem1221495 _26945 l1 x l2)). Qed.
Lemma lem1221818 {A : Type'} (l1 : list A) (x : A) (l2 : list A) : (term9 A x l1 l2) = (term10 A l1 x l2).
Proof. exact (@lem1221817 A l1 x l2). Qed.
Lemma lem1221819 {A : Type'} (l1 : list A) (x : A) (l2 : list A) : (term91 A l1 x l2) = (term92 A l1 x l2).
Proof. exact (@lem1221818 A l1 x (@cons A x l2)). Qed.
Lemma lem1221823 {_25376 : Type'} (h : _25376) (x : _25376) (t : list _25376) : (term93 _25376 x h t) = (term94 _25376 h x t).
Proof. exact (EQ_MP (@lem1103201 _25376 h x t) (@lem1103200 _25376 h x t)). Qed.
Lemma lem1221824 {A : Type'} (h : A) (x : A) (t : list A) : (term93 A x h t) = (term94 A h x t).
Proof. exact (@lem1221823 A h x t). Qed.
Lemma lem1221825 {A : Type'} (x : A) (l2 : list A) : (term95 A x l2) = (term96 A x l2).
Proof. exact (@lem1221824 A x x l2). Qed.
Lemma lem1221829 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1221830 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem1221829 A x). Qed.
Lemma lem1221831 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1221832 {A : Type'} (x : A) : (term97 A x) = (or True).
Proof. exact (MK_COMB (@lem1221831) (@lem1221830 A x)). Qed.
Lemma lem1221833 {A : Type'} (x : A) (l2 : list A) : (@List.In A x l2) = (@List.In A x l2).
Proof. exact (eq_refl (@List.In A x l2)). Qed.
Lemma lem1221834 {A : Type'} (x : A) (l2 : list A) : (term96 A x l2) = (term98 A x l2).
Proof. exact (MK_COMB (@lem1221832 A x) (@lem1221833 A x l2)). Qed.
Lemma lem1221836 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem1221837 {A : Type'} (x : A) (l2 : list A) : (term98 A x l2) = True.
Proof. exact (@lem1221836 (@List.In A x l2)). Qed.
Lemma lem1221838 {A : Type'} (x : A) (l2 : list A) : (term96 A x l2) = True.
Proof. exact (TRANS (@lem1221834 A x l2) (@lem1221837 A x l2)). Qed.
Lemma lem1221839 {A : Type'} (x : A) (l2 : list A) : (term95 A x l2) = True.
Proof. exact (TRANS (@lem1221825 A x l2) (@lem1221838 A x l2)). Qed.
Lemma lem1221840 {A : Type'} (x : A) (l1 : list A) : (term99 A x l1) = (term99 A x l1).
Proof. exact (eq_refl (term99 A x l1)). Qed.
Lemma lem1221841 {A : Type'} (l2 : list A) (x : A) (l1 : list A) : (term92 A l1 x l2) = (term100 A x l1).
Proof. exact (MK_COMB (@lem1221840 A x l1) (@lem1221839 A x l2)). Qed.
Lemma lem1221843 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem1221844 {A : Type'} (x : A) (l1 : list A) : (term100 A x l1) = True.
Proof. exact (@lem1221843 (@List.In A x l1)). Qed.
Lemma lem1221845 {A : Type'} (l1 : list A) (x : A) (l2 : list A) : (term92 A l1 x l2) = True.
Proof. exact (TRANS (@lem1221841 A l2 x l1) (@lem1221844 A x l1)). Qed.
Lemma lem1221846 {A : Type'} (l1 : list A) (x : A) (l2 : list A) : (term91 A l1 x l2) = True.
Proof. exact (TRANS (@lem1221819 A l1 x l2) (@lem1221845 A l1 x l2)). Qed.
Lemma lem1221847 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) (h1 : l = (term68 A l1 x l2)) : (@List.In A x l) = True.
Proof. exact (TRANS (@lem1221815 A l l1 x l2 h1) (@lem1221846 A l1 x l2)). Qed.
Lemma lem1221848 {A : Type'} (l1 : list A) (l2 : list A) (x : A) (l : list A) : term101 A l1 l2 x l.
Proof. exact (fun h0 : l = (term68 A l1 x l2) => @lem1221847 A l l1 x l2 h0). Qed.
Lemma lem1221849 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) : term102 A l l1 x l2.
Proof. exact (@lem1221810 A l l1 x l2 True). Qed.
Lemma lem1221850 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term77 A l1 l2 x l) = (term103 A l l1 x l2).
Proof. exact (@lem1221849 A l l1 x l2 (@lem1221848 A l1 l2 x l)). Qed.
Lemma lem1221854 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1221855 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term103 A l l1 x l2) = True.
Proof. exact (@lem1221854 (l = (term68 A l1 x l2))). Qed.
Lemma lem1221856 {A : Type'} (l1 : list A) (l2 : list A) (x : A) (l : list A) : (term77 A l1 l2 x l) = True.
Proof. exact (TRANS (@lem1221850 A l l1 x l2) (@lem1221855 A l l1 x l2)). Qed.
Lemma lem1221857 {A : Type'} (l1 : list A) (x : A) (l : list A) : (term79 A l1 x l) = (term104 A).
Proof. exact (fun_ext (fun l2 : list A => @lem1221856 A l1 l2 x l)). Qed.
Lemma lem1221858 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1221859 {A : Type'} (l1 : list A) (x : A) (l : list A) : (term80 A l1 x l) = (term105 A).
Proof. exact (MK_COMB (@lem1221858 A) (@lem1221857 A l1 x l)). Qed.
Lemma lem1221861 {A : Type'} (t : Prop) : (term106 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1221862 {A : Type'} (t : Prop) : (term107 A t) = t.
Proof. exact (@lem1221861 (list A) t). Qed.
Lemma lem1221863 {A : Type'} : (term105 A) = True.
Proof. exact (@lem1221862 A True). Qed.
Lemma lem1221864 {A : Type'} (l1 : list A) (x : A) (l : list A) : (term80 A l1 x l) = True.
Proof. exact (TRANS (@lem1221859 A l1 x l) (@lem1221863 A)). Qed.
Lemma lem1221865 {A : Type'} (l1 : list A) (x : A) (l : list A) : (term60 A l1 x l) = True.
Proof. exact (TRANS (@lem1221786 A l1 x l) (@lem1221864 A l1 x l)). Qed.
Lemma lem1221866 {A : Type'} (x : A) (l : list A) : (term62 A x l) = (term104 A).
Proof. exact (fun_ext (fun l1 : list A => @lem1221865 A l1 x l)). Qed.
Lemma lem1221867 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1221868 {A : Type'} (x : A) (l : list A) : (term63 A x l) = (term105 A).
Proof. exact (MK_COMB (@lem1221867 A) (@lem1221866 A x l)). Qed.
Lemma lem1221870 {A : Type'} (t : Prop) : (term106 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1221871 {A : Type'} (t : Prop) : (term107 A t) = t.
Proof. exact (@lem1221870 (list A) t). Qed.
Lemma lem1221872 {A : Type'} : (term105 A) = True.
Proof. exact (@lem1221871 A True). Qed.
Lemma lem1221873 {A : Type'} (x : A) (l : list A) : (term63 A x l) = True.
Proof. exact (TRANS (@lem1221868 A x l) (@lem1221872 A)). Qed.
Lemma lem1221874 {A : Type'} (x : A) (l : list A) : (term54 A x l) = True.
Proof. exact (TRANS (@lem1221758 A x l) (@lem1221873 A x l)). Qed.
Lemma lem1221875 {A : Type'} (l : list A) (x : A) : (term108 A l x) = (term108 A l x).
Proof. exact (eq_refl (term108 A l x)). Qed.
Lemma lem1221876 {A : Type'} (l : list A) (x : A) : (term34 A x l) = (term109 A l x).
Proof. exact (MK_COMB (@lem1221875 A l x) (@lem1221874 A x l)). Qed.
Lemma lem1221878 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem1221879 {A : Type'} (l : list A) (x : A) : (term109 A l x) = (term110 A l x).
Proof. exact (@lem1221878 (term110 A l x)). Qed.
Lemma lem1221923 {A : Type'} (l : list A) (x : A) : (term34 A x l) = (term110 A l x).
Proof. exact (TRANS (@lem1221876 A l x) (@lem1221879 A l x)). Qed.
Lemma lem1221924 {A : Type'} (x : A) : (term36 A x) = (term111 A x).
Proof. exact (fun_ext (fun l : list A => @lem1221923 A l x)). Qed.
Lemma lem1221968 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1221969 {A : Type'} (x : A) : (term38 A x) = (term112 A x).
Proof. exact (MK_COMB (@lem1221968 A) (@lem1221924 A x)). Qed.
Lemma lem1222017 {A : Type'} : (term40 A) = (term113 A).
Proof. exact (fun_ext (fun x : A => @lem1221969 A x)). Qed.
Lemma lem1222065 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1222066 {A : Type'} : (term42 A) = (term114 A).
Proof. exact (MK_COMB (@lem1222065 A) (@lem1222017 A)). Qed.
Lemma lem1222118 {A : Type'} : (term114 A) = (term42 A).
Proof. exact (SYM (@lem1222066 A)). Qed.
Lemma lem1222130 {A : Type'} (l : list A) (x : A) : (@List.In A x l) = (term3 A l x).
Proof. exact (EQ_MP (@lem1221485 A l x) (@lem1221484 A x l)). Qed.
Lemma lem1222131 {A : Type'} (l : list A) (x : A) : (@List.In A x l) = (term3 A l x).
Proof. exact (@lem1222130 A l x). Qed.
Lemma lem1222132 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1222133 {A : Type'} (l : list A) (x : A) : (term115 A x l) = (term116 A l x).
Proof. exact (MK_COMB (@lem1222132) (@lem1222131 A l x)). Qed.
Lemma lem1222144 {A : Type'} (l : list A) (x : A) : (term33 A l x) = (term33 A l x).
Proof. exact (eq_refl (term33 A l x)). Qed.
Lemma lem1222145 {A : Type'} (l : list A) (x : A) : (term110 A l x) = (term117 A l x).
Proof. exact (MK_COMB (@lem1222133 A l x) (@lem1222144 A l x)). Qed.
Lemma lem1222146 {A : Type'} (x : A) : (term111 A x) = (term118 A x).
Proof. exact (fun_ext (fun l : list A => @lem1222145 A l x)). Qed.
Lemma lem1222147 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1222148 {A : Type'} (x : A) : (term112 A x) = (term119 A x).
Proof. exact (MK_COMB (@lem1222147 A) (@lem1222146 A x)). Qed.
Lemma lem1222149 {A : Type'} : (term113 A) = (term120 A).
Proof. exact (fun_ext (fun x : A => @lem1222148 A x)). Qed.
Lemma lem1222150 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1222151 {A : Type'} : (term114 A) = (term121 A).
Proof. exact (MK_COMB (@lem1222150 A) (@lem1222149 A)). Qed.
Lemma lem1222152 {A : Type'} : (term121 A) = (term114 A).
Proof. exact (SYM (@lem1222151 A)). Qed.
Lemma lem1222154 (p : Prop) : p = (term122 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1222155 {A : Type'} : (term121 A) = (term123 A).
Proof. exact (@lem1222154 (term121 A)). Qed.
Lemma lem1222156 {A : Type'} : (term123 A) = (term121 A).
Proof. exact (SYM (@lem1222155 A)). Qed.
Lemma lem1222157 {A : Type'} (h1 : term124 A) : term124 A.
Proof. exact (h1). Qed.
Lemma lem1222160 {A : Type'} (h1 : term123 A) : term123 A.
Proof. exact (h1). Qed.
Lemma lem1222161 {A : Type'} : term125 A.
Proof. exact (fun h0 : term123 A => @lem1222160 A h0). Qed.
Lemma lem1222162 {A : Type'} (h1 : term125 A) : term125 A.
Proof. exact (h1). Qed.
Lemma lem1222163 {A : Type'} (h1 : term123 A) : term123 A.
Proof. exact (h1). Qed.
Lemma lem1222164 {A : Type'} (h1 : term123 A) (h2 : term125 A) : term123 A.
Proof. exact (@lem1222162 A h2 (@lem1222163 A h1)). Qed.
Lemma lem1222165 {A : Type'} (h1 : term123 A) : term126 A.
Proof. exact (fun h0 : term125 A => @lem1222164 A h1 h0). Qed.
Lemma lem1222166 {A : Type'} (h1 : term125 A) : term125 A.
Proof. exact (h1). Qed.
Lemma lem1222167 {A : Type'} (h1 : term123 A) (h2 : term125 A) : term123 A.
Proof. exact (@lem1222165 A h1 (@lem1222166 A h2)). Qed.
Lemma lem1222168 {A : Type'} (h1 : term125 A) : term125 A.
Proof. exact (fun h0 : term123 A => @lem1222167 A h0 h1). Qed.
Lemma lem1222169 {A : Type'} : term127 A.
Proof. exact (fun h0 : term125 A => @lem1222168 A h0). Qed.
Lemma lem1222172 {A : Type'} : term125 A.
Proof. exact (@lem1222169 A (@lem1222161 A)). Qed.
Lemma lem1222173 {A : Type'} : term125 A.
Proof. exact (@lem1222172 A). Qed.
Lemma lem1222175 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1222176 {A : Type'} : (term123 A) = (term128 A).
Proof. exact (@lem1222175 (term124 A)). Qed.
Lemma lem1222178 (t : Prop) : (term129 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem1222179 {A : Type'} : (term128 A) = (term121 A).
Proof. exact (@lem1222178 (term121 A)). Qed.
Lemma lem1222184 {A : Type'} : (term123 A) = (term121 A).
Proof. exact (TRANS (@lem1222176 A) (@lem1222179 A)). Qed.
Lemma lem1222196 {A : Type'} (P : Prop) (Q : A -> Prop) : (term130 A P Q) = (term131 A P Q).
Proof. exact (EQ_MP (@lem16434 A P Q) (@lem16433 A P Q)). Qed.
Lemma lem1222197 {A : Type'} (P : Prop) (Q : type1143 A) : (term132 A P Q) = (term133 A P Q).
Proof. exact (@lem1222196 (list A) P Q). Qed.
Lemma lem1222198 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term134 A l l1 x) = (term135 A l l1 x).
Proof. exact (@lem1222197 A (term136 A x l1) (term66 A l l1 x)). Qed.
Lemma lem1222199 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term67 A l l1 x l2) = (l = (term68 A l1 x l2)).
Proof. exact (eq_refl (term67 A l l1 x l2)). Qed.
Lemma lem1222200 {A : Type'} (x : A) (l1 : list A) : (term137 A x l1) = (term137 A x l1).
Proof. exact (eq_refl (term137 A x l1)). Qed.
Lemma lem1222201 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term138 A l l1 x l2) = (term139 A l l1 x l2).
Proof. exact (MK_COMB (@lem1222200 A x l1) (@lem1222199 A l l1 x l2)). Qed.
Lemma lem1222202 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term140 A l l1 x) = (term141 A l l1 x).
Proof. exact (fun_ext (fun l2 : list A => @lem1222201 A l l1 x l2)). Qed.
Lemma lem1222203 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1222204 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term134 A l l1 x) = (term142 A l l1 x).
Proof. exact (MK_COMB (@lem1222203 A) (@lem1222202 A l l1 x)). Qed.
Lemma lem1222205 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1222206 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term143 A l l1 x) = (term144 A l l1 x).
Proof. exact (MK_COMB (@lem1222205) (@lem1222204 A l l1 x)). Qed.
Lemma lem1222207 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term67 A l l1 x l2) = (l = (term68 A l1 x l2)).
Proof. exact (eq_refl (term67 A l l1 x l2)). Qed.
Lemma lem1222208 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term69 A l l1 x) = (term66 A l l1 x).
Proof. exact (fun_ext (fun l2 : list A => @lem1222207 A l l1 x l2)). Qed.
Lemma lem1222209 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1222210 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term70 A l l1 x) = (term49 A l l1 x).
Proof. exact (MK_COMB (@lem1222209 A) (@lem1222208 A l l1 x)). Qed.
Lemma lem1222211 {A : Type'} (x : A) (l1 : list A) : (term137 A x l1) = (term137 A x l1).
Proof. exact (eq_refl (term137 A x l1)). Qed.
Lemma lem1222212 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term135 A l l1 x) = (term145 A l l1 x).
Proof. exact (MK_COMB (@lem1222211 A x l1) (@lem1222210 A l l1 x)). Qed.
Lemma lem1222213 {A : Type'} (l : list A) (l1 : list A) (x : A) : ((term134 A l l1 x) = (term135 A l l1 x)) = ((term142 A l l1 x) = (term145 A l l1 x)).
Proof. exact (MK_COMB (@lem1222206 A l l1 x) (@lem1222212 A l l1 x)). Qed.
Lemma lem1222214 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term142 A l l1 x) = (term145 A l l1 x).
Proof. exact (EQ_MP (@lem1222213 A l l1 x) (@lem1222198 A l l1 x)). Qed.
Lemma lem1222221 {A : Type'} (l : list A) (x : A) : (term146 A l x) = (term147 A l x).
Proof. exact (fun_ext (fun l1 : list A => @lem1222214 A l l1 x)). Qed.
Lemma lem1222222 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1222223 {A : Type'} (l : list A) (x : A) : (term3 A l x) = (term148 A l x).
Proof. exact (MK_COMB (@lem1222222 A) (@lem1222221 A l x)). Qed.
Lemma lem1222272 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1222273 {A : Type'} (l : list A) (x : A) : (term116 A l x) = (term149 A l x).
Proof. exact (MK_COMB (@lem1222272) (@lem1222223 A l x)). Qed.
Lemma lem1222282 {A : Type'} (l : list A) (x : A) : (term33 A l x) = (term33 A l x).
Proof. exact (eq_refl (term33 A l x)). Qed.
Lemma lem1222283 {A : Type'} (l : list A) (x : A) : (term117 A l x) = (term150 A l x).
Proof. exact (MK_COMB (@lem1222273 A l x) (@lem1222282 A l x)). Qed.
Lemma lem1222286 {A : Type'} (x : A) : (term118 A x) = (term151 A x).
Proof. exact (fun_ext (fun l : list A => @lem1222283 A l x)). Qed.
Lemma lem1222287 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1222288 {A : Type'} (x : A) : (term119 A x) = (term152 A x).
Proof. exact (MK_COMB (@lem1222287 A) (@lem1222286 A x)). Qed.
Lemma lem1222293 {A : Type'} : (term120 A) = (term153 A).
Proof. exact (fun_ext (fun x : A => @lem1222288 A x)). Qed.
Lemma lem1222294 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1222295 {A : Type'} : (term121 A) = (term154 A).
Proof. exact (MK_COMB (@lem1222294 A) (@lem1222293 A)). Qed.
Lemma lem1222304 {A : Type'} : (term123 A) = (term154 A).
Proof. exact (TRANS (@lem1222184 A) (@lem1222295 A)). Qed.
Lemma lem1222305 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) : (l = (term68 A l1 x l2)) = (l = (term68 A l1 x l2)).
Proof. exact (eq_refl (l = (term68 A l1 x l2))). Qed.
Lemma lem1222306 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term66 A l l1 x) = (term66 A l l1 x).
Proof. exact (fun_ext (fun l2 : list A => @lem1222305 A l l1 x l2)). Qed.
Lemma lem1222307 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1222308 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term49 A l l1 x) = (term49 A l l1 x).
Proof. exact (MK_COMB (@lem1222307 A) (@lem1222306 A l l1 x)). Qed.
Lemma lem1222309 {A : Type'} (l : list A) (x : A) : (term47 A l x) = (term47 A l x).
Proof. exact (fun_ext (fun l1 : list A => @lem1222308 A l l1 x)). Qed.
Lemma lem1222310 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1222311 {A : Type'} (l : list A) (x : A) : (term33 A l x) = (term33 A l x).
Proof. exact (MK_COMB (@lem1222310 A) (@lem1222309 A l x)). Qed.
Lemma lem1222312 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) : (l = (term68 A l1 x l2)) = (l = (term68 A l1 x l2)).
Proof. exact (eq_refl (l = (term68 A l1 x l2))). Qed.
Lemma lem1222313 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term66 A l l1 x) = (term66 A l l1 x).
Proof. exact (fun_ext (fun l2 : list A => @lem1222312 A l l1 x l2)). Qed.
Lemma lem1222314 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1222315 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term49 A l l1 x) = (term49 A l l1 x).
Proof. exact (MK_COMB (@lem1222314 A) (@lem1222313 A l l1 x)). Qed.
Lemma lem1222320 {A : Type'} (x : A) (l1 : list A) : (term137 A x l1) = (term137 A x l1).
Proof. exact (eq_refl (term137 A x l1)). Qed.
Lemma lem1222321 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term145 A l l1 x) = (term145 A l l1 x).
Proof. exact (MK_COMB (@lem1222320 A x l1) (@lem1222315 A l l1 x)). Qed.
Lemma lem1222322 {A : Type'} (l : list A) (x : A) : (term147 A l x) = (term147 A l x).
Proof. exact (fun_ext (fun l1 : list A => @lem1222321 A l l1 x)). Qed.
Lemma lem1222323 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1222324 {A : Type'} (l : list A) (x : A) : (term148 A l x) = (term148 A l x).
Proof. exact (MK_COMB (@lem1222323 A) (@lem1222322 A l x)). Qed.
Lemma lem1222325 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1222326 {A : Type'} (l : list A) (x : A) : (term149 A l x) = (term149 A l x).
Proof. exact (MK_COMB (@lem1222325) (@lem1222324 A l x)). Qed.
Lemma lem1222327 {A : Type'} (l : list A) (x : A) : (term150 A l x) = (term150 A l x).
Proof. exact (MK_COMB (@lem1222326 A l x) (@lem1222311 A l x)). Qed.
Lemma lem1222328 {A : Type'} (x : A) : (term151 A x) = (term151 A x).
Proof. exact (fun_ext (fun l : list A => @lem1222327 A l x)). Qed.
Lemma lem1222329 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1222330 {A : Type'} (x : A) : (term152 A x) = (term152 A x).
Proof. exact (MK_COMB (@lem1222329 A) (@lem1222328 A x)). Qed.
Lemma lem1222331 {A : Type'} : (term153 A) = (term153 A).
Proof. exact (fun_ext (fun x : A => @lem1222330 A x)). Qed.
Lemma lem1222332 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1222333 {A : Type'} : (term154 A) = (term154 A).
Proof. exact (MK_COMB (@lem1222332 A) (@lem1222331 A)). Qed.
Lemma lem1222376 {A : Type'} : (term123 A) = (term154 A).
Proof. exact (TRANS (@lem1222304 A) (@lem1222333 A)). Qed.
Lemma lem1222377 {A : Type'} : (term154 A) = (term123 A).
Proof. exact (SYM (@lem1222376 A)). Qed.
Lemma lem1222378 {A : Type'} (l : list A) (x : A) (h1 : term148 A l x) : term148 A l x.
Proof. exact (h1). Qed.
Lemma lem1222380 (p : Prop) : p = (term122 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1222381 {A : Type'} (l : list A) (x : A) : (term33 A l x) = (term155 A l x).
Proof. exact (@lem1222380 (term33 A l x)). Qed.
Lemma lem1222382 {A : Type'} (l : list A) (x : A) : (term155 A l x) = (term33 A l x).
Proof. exact (SYM (@lem1222381 A l x)). Qed.
Lemma lem1222383 {A : Type'} (l : list A) (x : A) (h1 : term156 A l x) : term156 A l x.
Proof. exact (h1). Qed.
Lemma lem1222385 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) : (l = (term68 A l1 x l2)) = (l = (term68 A l1 x l2)).
Proof. exact (eq_refl (l = (term68 A l1 x l2))). Qed.
Lemma lem1222386 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term66 A l l1 x) = (term66 A l l1 x).
Proof. exact (fun_ext (fun l2 : list A => @lem1222385 A l l1 x l2)). Qed.
Lemma lem1222387 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1222388 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term49 A l l1 x) = (term49 A l l1 x).
Proof. exact (MK_COMB (@lem1222387 A) (@lem1222386 A l l1 x)). Qed.
Lemma lem1222390 {A : Type'} (x : A) (l1 : list A) : (term137 A x l1) = (term137 A x l1).
Proof. exact (eq_refl (term137 A x l1)). Qed.
Lemma lem1222391 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term145 A l l1 x) = (term145 A l l1 x).
Proof. exact (MK_COMB (@lem1222390 A x l1) (@lem1222388 A l l1 x)). Qed.
Lemma lem1222392 {A : Type'} (l : list A) (x : A) : (term147 A l x) = (term147 A l x).
Proof. exact (fun_ext (fun l1 : list A => @lem1222391 A l l1 x)). Qed.
Lemma lem1222393 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1222394 {A : Type'} (l : list A) (x : A) : (term148 A l x) = (term148 A l x).
Proof. exact (MK_COMB (@lem1222393 A) (@lem1222392 A l x)). Qed.
Lemma lem1222449 {A : Type'} (P : Prop) (Q : A -> Prop) : (term131 A P Q) = (term130 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem1222450 {A : Type'} (P : Prop) (Q : type1143 A) : (term133 A P Q) = (term132 A P Q).
Proof. exact (@lem1222449 (list A) P Q). Qed.
Lemma lem1222451 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term135 A l l1 x) = (term134 A l l1 x).
Proof. exact (@lem1222450 A (term136 A x l1) (term66 A l l1 x)). Qed.
Lemma lem1222452 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term67 A l l1 x l2) = (l = (term68 A l1 x l2)).
Proof. exact (eq_refl (term67 A l l1 x l2)). Qed.
Lemma lem1222453 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term69 A l l1 x) = (term66 A l l1 x).
Proof. exact (fun_ext (fun l2 : list A => @lem1222452 A l l1 x l2)). Qed.
Lemma lem1222454 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1222455 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term70 A l l1 x) = (term49 A l l1 x).
Proof. exact (MK_COMB (@lem1222454 A) (@lem1222453 A l l1 x)). Qed.
Lemma lem1222456 {A : Type'} (x : A) (l1 : list A) : (term137 A x l1) = (term137 A x l1).
Proof. exact (eq_refl (term137 A x l1)). Qed.
Lemma lem1222457 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term135 A l l1 x) = (term145 A l l1 x).
Proof. exact (MK_COMB (@lem1222456 A x l1) (@lem1222455 A l l1 x)). Qed.
Lemma lem1222458 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1222459 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term157 A l l1 x) = (term158 A l l1 x).
Proof. exact (MK_COMB (@lem1222458) (@lem1222457 A l l1 x)). Qed.
Lemma lem1222460 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term67 A l l1 x l2) = (l = (term68 A l1 x l2)).
Proof. exact (eq_refl (term67 A l l1 x l2)). Qed.
Lemma lem1222461 {A : Type'} (x : A) (l1 : list A) : (term137 A x l1) = (term137 A x l1).
Proof. exact (eq_refl (term137 A x l1)). Qed.
Lemma lem1222462 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term138 A l l1 x l2) = (term139 A l l1 x l2).
Proof. exact (MK_COMB (@lem1222461 A x l1) (@lem1222460 A l l1 x l2)). Qed.
Lemma lem1222463 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term140 A l l1 x) = (term141 A l l1 x).
Proof. exact (fun_ext (fun l2 : list A => @lem1222462 A l l1 x l2)). Qed.
Lemma lem1222464 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1222465 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term134 A l l1 x) = (term142 A l l1 x).
Proof. exact (MK_COMB (@lem1222464 A) (@lem1222463 A l l1 x)). Qed.
Lemma lem1222466 {A : Type'} (l : list A) (l1 : list A) (x : A) : ((term135 A l l1 x) = (term134 A l l1 x)) = ((term145 A l l1 x) = (term142 A l l1 x)).
Proof. exact (MK_COMB (@lem1222459 A l l1 x) (@lem1222465 A l l1 x)). Qed.
Lemma lem1222467 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term145 A l l1 x) = (term142 A l l1 x).
Proof. exact (EQ_MP (@lem1222466 A l l1 x) (@lem1222451 A l l1 x)). Qed.
Lemma lem1222468 {A : Type'} (l : list A) (x : A) : (term147 A l x) = (term146 A l x).
Proof. exact (fun_ext (fun l1 : list A => @lem1222467 A l l1 x)). Qed.
Lemma lem1222469 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1222471 {A : Type'} (l : list A) (x : A) : (term148 A l x) = (term3 A l x).
Proof. exact (MK_COMB (@lem1222469 A) (@lem1222468 A l x)). Qed.
Lemma lem1222472 {A : Type'} (l : list A) (x : A) : (term148 A l x) = (term3 A l x).
Proof. exact (TRANS (@lem1222394 A l x) (@lem1222471 A l x)). Qed.
Lemma lem1222473 {A : Type'} (l : list A) (x : A) (h1 : term148 A l x) : term3 A l x.
Proof. exact (EQ_MP (@lem1222472 A l x) (@lem1222378 A l x h1)). Qed.
Lemma lem1222475 {A : Type'} (P : type1143 A) : (term159 A P) = (term160 A P).
Proof. exact (@lem18394 (list A) P). Qed.
Lemma lem1222476 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term161 A l l1 x) = (term162 A l l1 x).
Proof. exact (@lem1222475 A (term66 A l l1 x)). Qed.
Lemma lem1222477 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term67 A l l1 x l2) = (l = (term68 A l1 x l2)).
Proof. exact (eq_refl (term67 A l l1 x l2)). Qed.
Lemma lem1222478 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1222480 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term163 A l l1 x l2) = (term164 A l l1 x l2).
Proof. exact (MK_COMB (@lem1222478) (@lem1222477 A l l1 x l2)). Qed.
Lemma lem1222481 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term165 A l l1 x) = (term166 A l l1 x).
Proof. exact (fun_ext (fun l2 : list A => @lem1222480 A l l1 x l2)). Qed.
Lemma lem1222482 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1222483 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term162 A l l1 x) = (term167 A l l1 x).
Proof. exact (MK_COMB (@lem1222482 A) (@lem1222481 A l l1 x)). Qed.
Lemma lem1222484 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term161 A l l1 x) = (term167 A l l1 x).
Proof. exact (TRANS (@lem1222476 A l l1 x) (@lem1222483 A l l1 x)). Qed.
Lemma lem1222485 {A : Type'} (P : type1143 A) : (term159 A P) = (term160 A P).
Proof. exact (@lem18394 (list A) P). Qed.
Lemma lem1222486 {A : Type'} (l : list A) (x : A) : (term156 A l x) = (term168 A l x).
Proof. exact (@lem1222485 A (term47 A l x)). Qed.
Lemma lem1222487 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term48 A l x l1) = (term49 A l l1 x).
Proof. exact (eq_refl (term48 A l x l1)). Qed.
Lemma lem1222488 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1222489 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term169 A l x l1) = (term161 A l l1 x).
Proof. exact (MK_COMB (@lem1222488) (@lem1222487 A l l1 x)). Qed.
Lemma lem1222490 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term169 A l x l1) = (term167 A l l1 x).
Proof. exact (TRANS (@lem1222489 A l l1 x) (@lem1222484 A l l1 x)). Qed.
Lemma lem1222491 {A : Type'} (l : list A) (x : A) : (term170 A l x) = (term171 A l x).
Proof. exact (fun_ext (fun l1 : list A => @lem1222490 A l l1 x)). Qed.
Lemma lem1222492 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1222493 {A : Type'} (l : list A) (x : A) : (term168 A l x) = (term172 A l x).
Proof. exact (MK_COMB (@lem1222492 A) (@lem1222491 A l x)). Qed.
Lemma lem1222506 {A : Type'} (l : list A) (x : A) : (term156 A l x) = (term172 A l x).
Proof. exact (TRANS (@lem1222486 A l x) (@lem1222493 A l x)). Qed.
Lemma lem1222507 {A : Type'} (l : list A) (x : A) (h1 : term156 A l x) : term172 A l x.
Proof. exact (EQ_MP (@lem1222506 A l x) (@lem1222383 A l x h1)). Qed.
Lemma lem1222508 {A : Type'} (l : list A) (l1 : list A) (x : A) (h1 : term142 A l l1 x) : term142 A l l1 x.
Proof. exact (h1). Qed.
Lemma lem1222524 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term164 A l l1 x l2) = (term164 A l l1 x l2).
Proof. exact (eq_refl (term164 A l l1 x l2)). Qed.
Lemma lem1222525 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term166 A l l1 x) = (term166 A l l1 x).
Proof. exact (fun_ext (fun l2 : list A => @lem1222524 A l l1 x l2)). Qed.
Lemma lem1222526 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1222527 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term167 A l l1 x) = (term167 A l l1 x).
Proof. exact (MK_COMB (@lem1222526 A) (@lem1222525 A l l1 x)). Qed.
Lemma lem1222528 {A : Type'} (l : list A) (x : A) : (term171 A l x) = (term171 A l x).
Proof. exact (fun_ext (fun l1 : list A => @lem1222527 A l l1 x)). Qed.
Lemma lem1222529 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1222530 {A : Type'} (l : list A) (x : A) : (term172 A l x) = (term172 A l x).
Proof. exact (MK_COMB (@lem1222529 A) (@lem1222528 A l x)). Qed.
Lemma lem1222531 {A : Type'} (l : list A) (x : A) (h1 : term156 A l x) : term172 A l x.
Proof. exact (EQ_MP (@lem1222530 A l x) (@lem1222507 A l x h1)). Qed.
Lemma lem1222555 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) (h1 : term139 A l l1 x l2) : term139 A l l1 x l2.
Proof. exact (h1). Qed.
Lemma lem1222559 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term164 A l l1 x l2) = (term164 A l l1 x l2).
Proof. exact (eq_refl (term164 A l l1 x l2)). Qed.
Lemma lem1222560 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term166 A l l1 x) = (term166 A l l1 x).
Proof. exact (fun_ext (fun l2 : list A => @lem1222559 A l l1 x l2)). Qed.
Lemma lem1222561 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1222562 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term167 A l l1 x) = (term167 A l l1 x).
Proof. exact (MK_COMB (@lem1222561 A) (@lem1222560 A l l1 x)). Qed.
Lemma lem1222563 {A : Type'} (l : list A) (x : A) : (term171 A l x) = (term171 A l x).
Proof. exact (fun_ext (fun l1 : list A => @lem1222562 A l l1 x)). Qed.
Lemma lem1222564 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1222566 {A : Type'} (l : list A) (x : A) : (term172 A l x) = (term172 A l x).
Proof. exact (MK_COMB (@lem1222564 A) (@lem1222563 A l x)). Qed.
Lemma lem1222567 {A : Type'} (l : list A) (x : A) (h1 : term156 A l x) : term172 A l x.
Proof. exact (EQ_MP (@lem1222566 A l x) (@lem1222531 A l x h1)). Qed.
Lemma lem1222576 {A : Type'} (_22380 : list A) (l : list A) (x : A) (h1 : term156 A l x) : term173 A l x _22380.
Proof. exact (@lem1222567 A l x h1 _22380). Qed.
Lemma lem1222577 {A : Type'} (l : list A) (_22380 : list A) (x : A) : (term173 A l x _22380) = (term167 A l _22380 x).
Proof. exact (eq_refl (term173 A l x _22380)). Qed.
Lemma lem1222578 {A : Type'} (_22380 : list A) (l : list A) (x : A) (h1 : term156 A l x) : term167 A l _22380 x.
Proof. exact (EQ_MP (@lem1222577 A l _22380 x) (@lem1222576 A _22380 l x h1)). Qed.
Lemma lem1222579 {A : Type'} (_22380 : list A) (_22381 : list A) (l : list A) (x : A) (h1 : term156 A l x) : term174 A l _22380 x _22381.
Proof. exact (@lem1222578 A _22380 l x h1 _22381). Qed.
Lemma lem1222580 {A : Type'} (l : list A) (_22380 : list A) (x : A) (_22381 : list A) : (term174 A l _22380 x _22381) = (term164 A l _22380 x _22381).
Proof. exact (eq_refl (term174 A l _22380 x _22381)). Qed.
Lemma lem1222583 {A : Type'} (_22380 : list A) (_22381 : list A) (l : list A) (x : A) (h1 : term156 A l x) : term164 A l _22380 x _22381.
Proof. exact (EQ_MP (@lem1222580 A l _22380 x _22381) (@lem1222579 A _22380 _22381 l x h1)). Qed.
Lemma lem1222587 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) (h1 : term139 A l l1 x l2) : l = (term68 A l1 x l2).
Proof. exact (proj2 (@lem1222555 A l l1 x l2 h1)). Qed.
Lemma lem1222602 {A : Type'} (_22380 : list A) (x : A) (_22381 : list A) : (term175 A _22380 x _22381) = (term175 A _22380 x _22381).
Proof. exact (eq_refl (term175 A _22380 x _22381)). Qed.
Lemma lem1222603 {A : Type'} (_22380 : list A) (_22381 : list A) (l : list A) (l1 : list A) (x : A) (l2 : list A) (h1 : term139 A l l1 x l2) : (term176 A _22380 x _22381 l) = (term177 A _22380 _22381 l1 x l2).
Proof. exact (MK_COMB (@lem1222602 A _22380 x _22381) (@lem1222587 A l l1 x l2 h1)). Qed.
Lemma lem1222604 {A : Type'} (l1 : list A) (l2 : list A) (_22380 : list A) (x : A) (_22381 : list A) : (term177 A _22380 _22381 l1 x l2) = (term178 A l1 l2 _22380 x _22381).
Proof. exact (eq_refl (term177 A _22380 _22381 l1 x l2)). Qed.
Lemma lem1222605 {A : Type'} (_22380 : list A) (x : A) (_22381 : list A) (l : list A) : (term179 A _22380 x _22381 l) = (term179 A _22380 x _22381 l).
Proof. exact (eq_refl (term179 A _22380 x _22381 l)). Qed.
Lemma lem1222606 {A : Type'} (l : list A) (l1 : list A) (l2 : list A) (_22380 : list A) (x : A) (_22381 : list A) : ((term176 A _22380 x _22381 l) = (term177 A _22380 _22381 l1 x l2)) = ((term176 A _22380 x _22381 l) = (term178 A l1 l2 _22380 x _22381)).
Proof. exact (MK_COMB (@lem1222605 A _22380 x _22381 l) (@lem1222604 A l1 l2 _22380 x _22381)). Qed.
Lemma lem1222607 {A : Type'} (l : list A) (_22380 : list A) (x : A) (_22381 : list A) : (term176 A _22380 x _22381 l) = (term164 A l _22380 x _22381).
Proof. exact (eq_refl (term176 A _22380 x _22381 l)). Qed.
Lemma lem1222608 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1222609 {A : Type'} (l : list A) (_22380 : list A) (x : A) (_22381 : list A) : (term179 A _22380 x _22381 l) = (term180 A l _22380 x _22381).
Proof. exact (MK_COMB (@lem1222608) (@lem1222607 A l _22380 x _22381)). Qed.
Lemma lem1222610 {A : Type'} (l1 : list A) (l2 : list A) (_22380 : list A) (x : A) (_22381 : list A) : (term178 A l1 l2 _22380 x _22381) = (term178 A l1 l2 _22380 x _22381).
Proof. exact (eq_refl (term178 A l1 l2 _22380 x _22381)). Qed.
Lemma lem1222611 {A : Type'} (l : list A) (l1 : list A) (l2 : list A) (_22380 : list A) (x : A) (_22381 : list A) : ((term176 A _22380 x _22381 l) = (term178 A l1 l2 _22380 x _22381)) = ((term164 A l _22380 x _22381) = (term178 A l1 l2 _22380 x _22381)).
Proof. exact (MK_COMB (@lem1222609 A l _22380 x _22381) (@lem1222610 A l1 l2 _22380 x _22381)). Qed.
Lemma lem1222612 {A : Type'} (l : list A) (l1 : list A) (l2 : list A) (_22380 : list A) (x : A) (_22381 : list A) : ((term176 A _22380 x _22381 l) = (term177 A _22380 _22381 l1 x l2)) = ((term164 A l _22380 x _22381) = (term178 A l1 l2 _22380 x _22381)).
Proof. exact (TRANS (@lem1222606 A l l1 l2 _22380 x _22381) (@lem1222611 A l l1 l2 _22380 x _22381)). Qed.
Lemma lem1222613 {A : Type'} (_22380 : list A) (_22381 : list A) (l : list A) (l1 : list A) (x : A) (l2 : list A) (h1 : term139 A l l1 x l2) : (term164 A l _22380 x _22381) = (term178 A l1 l2 _22380 x _22381).
Proof. exact (EQ_MP (@lem1222612 A l l1 l2 _22380 x _22381) (@lem1222603 A _22380 _22381 l l1 x l2 h1)). Qed.
Lemma lem1222614 {A : Type'} (_22380 : list A) (_22381 : list A) (l : list A) (l1 : list A) (x : A) (l2 : list A) (h1 : term156 A l x) (h2 : term139 A l l1 x l2) : term178 A l1 l2 _22380 x _22381.
Proof. exact (EQ_MP (@lem1222613 A _22380 _22381 l l1 x l2 h2) (@lem1222583 A _22380 _22381 l x h1)). Qed.
Lemma lem1222683 {A : Type'} (x : list A) : x = x.
Proof. exact (@lem21386 (list A) x). Qed.
Lemma lem1222684 {A : Type'} (x : list A) : x = x.
Proof. exact (@lem1222683 A x). Qed.
Lemma lem1222685 {A : Type'} (l1 : list A) (x : A) (l2 : list A) : (term68 A l1 x l2) = (term68 A l1 x l2).
Proof. exact (@lem1222684 A (term68 A l1 x l2)). Qed.
Lemma lem1222686 {A : Type'} (l1 : list A) (x : A) (l2 : list A) : term181 A l1 x l2.
Proof. exact (fun h0 : term182 A l1 x l2 => @lem1222685 A l1 x l2). Qed.
Lemma lem1222688 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1222689 {A : Type'} (l1 : list A) (x : A) (l2 : list A) : (term181 A l1 x l2) = ((term68 A l1 x l2) = (term68 A l1 x l2)).
Proof. exact (@lem1222688 ((term68 A l1 x l2) = (term68 A l1 x l2))). Qed.
Lemma lem1222690 {A : Type'} (l1 : list A) (x : A) (l2 : list A) : (term68 A l1 x l2) = (term68 A l1 x l2).
Proof. exact (EQ_MP (@lem1222689 A l1 x l2) (@lem1222686 A l1 x l2)). Qed.
Lemma lem1222693 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1222695 {A : Type'} (l1 : list A) (l2 : list A) (_22380 : list A) (x : A) (_22381 : list A) : (term178 A l1 l2 _22380 x _22381) = (term184 A l1 l2 _22380 x _22381).
Proof. exact (@lem1222693 ((term68 A l1 x l2) = (term68 A _22380 x _22381))). Qed.
Lemma lem1222698 {A : Type'} (_22380 : list A) (_22381 : list A) (l : list A) (l1 : list A) (x : A) (l2 : list A) (h1 : term156 A l x) (h2 : term139 A l l1 x l2) : term184 A l1 l2 _22380 x _22381.
Proof. exact (EQ_MP (@lem1222695 A l1 l2 _22380 x _22381) (@lem1222614 A _22380 _22381 l l1 x l2 h1 h2)). Qed.
Lemma lem1222699 {A : Type'} (_22380 : list A) (_22381 : list A) (l : list A) (l1 : list A) (x : A) (l2 : list A) (h1 : term156 A l x) (h2 : term139 A l l1 x l2) : term184 A l1 l2 _22380 x _22381.
Proof. exact (@lem1222698 A _22380 _22381 l l1 x l2 h1 h2). Qed.
Lemma lem1222700 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) (h1 : term156 A l x) (h2 : term139 A l l1 x l2) : term185 A l1 x l2.
Proof. exact (@lem1222699 A l1 l2 l l1 x l2 h1 h2). Qed.
Lemma lem1222703 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) (h1 : term156 A l x) (h2 : term139 A l l1 x l2) : False.
Proof. exact (@lem1222700 A l l1 x l2 h1 h2 (@lem1222690 A l1 x l2)). Qed.
Lemma lem1222704 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) (h1 : term156 A l x) (h2 : term139 A l l1 x l2) : term186.
Proof. exact (fun h0 : ~ False => @lem1222703 A l l1 x l2 h1 h2). Qed.
Lemma lem1222706 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1222707 : term186 = False.
Proof. exact (@lem1222706 False). Qed.
Lemma lem1222709 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) (h1 : term156 A l x) (h2 : term139 A l l1 x l2) : False.
Proof. exact (EQ_MP (@lem1222707) (@lem1222704 A l l1 x l2 h1 h2)). Qed.
Lemma lem1222710 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) (h1 : term156 A l x) (h2 : term139 A l l1 x l2) : (term139 A l l1 x l2) = False.
Proof. exact (prop_ext (fun h3 : term139 A l l1 x l2 => @lem1222709 A l l1 x l2 h1 h2) (fun h3 : False => @lem1222555 A l l1 x l2 h2)). Qed.
Lemma lem1222711 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) (h1 : term156 A l x) (h2 : term139 A l l1 x l2) : False.
Proof. exact (EQ_MP (@lem1222710 A l l1 x l2 h1 h2) (@lem1222555 A l l1 x l2 h2)). Qed.
Lemma lem1222712 {A : Type'} (l1 : list A) (l : list A) (x : A) (h1 : term142 A l l1 x) (h2 : term156 A l x) : False.
Proof. exact (ex_elim (@lem1222508 A l l1 x h1) (fun l2 : list A => fun h0 : term141 A l l1 x l2 => @lem1222711 A l l1 x l2 h2 h0)). Qed.
Lemma lem1222713 {A : Type'} (l : list A) (x : A) (h1 : term148 A l x) (h2 : term156 A l x) : False.
Proof. exact (ex_elim (@lem1222473 A l x h1) (fun l1 : list A => fun h0 : term146 A l x l1 => @lem1222712 A l1 l x h0 h2)). Qed.
Lemma lem1222714 {A : Type'} (l : list A) (x : A) (h1 : term148 A l x) (h2 : term156 A l x) : (term156 A l x) = False.
Proof. exact (prop_ext (fun h3 : term156 A l x => @lem1222713 A l x h1 h2) (fun h3 : False => @lem1222383 A l x h2)). Qed.
Lemma lem1222715 {A : Type'} (l : list A) (x : A) (h1 : term148 A l x) (h2 : term156 A l x) : False.
Proof. exact (EQ_MP (@lem1222714 A l x h1 h2) (@lem1222383 A l x h2)). Qed.
Lemma lem1222716 {A : Type'} (l : list A) (x : A) (h1 : term148 A l x) : term155 A l x.
Proof. exact (fun h0 : term156 A l x => @lem1222715 A l x h1 h0). Qed.
Lemma lem1222717 {A : Type'} (l : list A) (x : A) (h1 : term148 A l x) : term33 A l x.
Proof. exact (EQ_MP (@lem1222382 A l x) (@lem1222716 A l x h1)). Qed.
Lemma lem1222718 {A : Type'} (l : list A) (x : A) : term150 A l x.
Proof. exact (fun h0 : term148 A l x => @lem1222717 A l x h0). Qed.
Lemma lem1222723 {A : Type'} (x : A) : term152 A x.
Proof. exact (fun l : list A => @lem1222718 A l x). Qed.
Lemma lem1222728 {A : Type'} : term154 A.
Proof. exact (fun x : A => @lem1222723 A x). Qed.
Lemma lem1222729 {A : Type'} : term123 A.
Proof. exact (EQ_MP (@lem1222377 A) (@lem1222728 A)). Qed.
Lemma lem1222731 {A : Type'} : term123 A.
Proof. exact (@lem1222173 A (@lem1222729 A)). Qed.
Lemma lem1222732 {A : Type'} (h1 : term124 A) : False.
Proof. exact (@lem1222731 A (@lem1222157 A h1)). Qed.
Lemma lem1222733 {A : Type'} (h1 : term124 A) : (term124 A) = False.
Proof. exact (prop_ext (fun h2 : term124 A => @lem1222732 A h1) (fun h2 : False => @lem1222157 A h1)). Qed.
Lemma lem1222734 {A : Type'} (h1 : term124 A) : False.
Proof. exact (EQ_MP (@lem1222733 A h1) (@lem1222157 A h1)). Qed.
Lemma lem1222735 {A : Type'} : term123 A.
Proof. exact (fun h0 : term124 A => @lem1222734 A h0). Qed.
Lemma lem1222736 {A : Type'} : term121 A.
Proof. exact (EQ_MP (@lem1222156 A) (@lem1222735 A)). Qed.
Lemma lem1222737 {A : Type'} : term114 A.
Proof. exact (EQ_MP (@lem1222152 A) (@lem1222736 A)). Qed.
Lemma lem1222738 {A : Type'} : term42 A.
Proof. exact (EQ_MP (@lem1222118 A) (@lem1222737 A)). Qed.
Lemma lem1222739 {A : Type'} : term41 A.
Proof. exact (EQ_MP (@lem1221681 A) (@lem1222738 A)). Qed.
