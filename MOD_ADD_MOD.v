Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MOD_ADD_MOD_term_abbrevs.
Require Import ADD_AC_spec.
Require Import DIVISION_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import MOD_EQ_spec.
Require Import MOD_ZERO_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import REFL_CLAUSE_spec.
Require Import RIGHT_ADD_DISTRIB_spec.
Require Import thm0_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem209602 {A : Type'} (x : A) : term0 A x.
Proof. exact (@lem317 A x). Qed.
Lemma lem209603 {A : Type'} (x : A) : (term0 A x) = ((x = x) = True).
Proof. exact (eq_refl (term0 A x)). Qed.
Lemma lem209605 (n : nat) (m : nat) (p : nat) : term1 n m p.
Proof. exact (proj2 (@lem79120 n m p)). Qed.
Lemma lem209612 (m : nat) (n : nat) (p : nat) : (term2 m n p) = (term3 m n p).
Proof. exact (proj1 (@lem209605 n m p)). Qed.
Lemma lem209613 (a : nat) (b : nat) (c : nat) (d : nat) : (term4 a b c d) = (term5 a b c d).
Proof. exact (@lem209612 a b (Nat.add c d)). Qed.
Lemma lem209629 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem209630 (a : nat) (b : nat) (c : nat) (d : nat) : (term6 a b c d) = (term7 a b c d).
Proof. exact (MK_COMB (@lem209629) (@lem209613 a b c d)). Qed.
Lemma lem209632 (m : nat) (n : nat) (p : nat) : (term2 m n p) = (term3 m n p).
Proof. exact (proj1 (@lem209605 n m p)). Qed.
Lemma lem209633 (c : nat) (a : nat) (d : nat) (b : nat) : (term4 c a d b) = (term5 c a d b).
Proof. exact (@lem209632 c a (Nat.add d b)). Qed.
Lemma lem209635 (n : nat) (m : nat) (p : nat) : (term3 m n p) = (term3 n m p).
Proof. exact (proj2 (@lem209605 n m p)). Qed.
Lemma lem209636 (a : nat) (c : nat) (d : nat) (b : nat) : (term5 c a d b) = (term5 a c d b).
Proof. exact (@lem209635 a c (Nat.add d b)). Qed.
Lemma lem209643 (a : nat) (c : nat) (d : nat) (b : nat) : (term4 c a d b) = (term5 a c d b).
Proof. exact (TRANS (@lem209633 c a d b) (@lem209636 a c d b)). Qed.
Lemma lem209651 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem209652 (b : nat) (d : nat) : (Nat.add d b) = (Nat.add b d).
Proof. exact (@lem209651 b d). Qed.
Lemma lem209656 (c : nat) : (Nat.add c) = (Nat.add c).
Proof. exact (eq_refl (Nat.add c)). Qed.
Lemma lem209657 (c : nat) (b : nat) (d : nat) : (term3 c d b) = (term3 c b d).
Proof. exact (MK_COMB (@lem209656 c) (@lem209652 b d)). Qed.
Lemma lem209659 (n : nat) (m : nat) (p : nat) : (term3 m n p) = (term3 n m p).
Proof. exact (proj2 (@lem209605 n m p)). Qed.
Lemma lem209660 (b : nat) (c : nat) (d : nat) : (term3 c b d) = (term3 b c d).
Proof. exact (@lem209659 b c d). Qed.
Lemma lem209670 (b : nat) (c : nat) (d : nat) : (term3 c d b) = (term3 b c d).
Proof. exact (TRANS (@lem209657 c b d) (@lem209660 b c d)). Qed.
Lemma lem209671 (a : nat) : (Nat.add a) = (Nat.add a).
Proof. exact (eq_refl (Nat.add a)). Qed.
Lemma lem209672 (a : nat) (b : nat) (c : nat) (d : nat) : (term5 a c d b) = (term5 a b c d).
Proof. exact (MK_COMB (@lem209671 a) (@lem209670 b c d)). Qed.
Lemma lem209679 (a : nat) (b : nat) (c : nat) (d : nat) : (term4 c a d b) = (term5 a b c d).
Proof. exact (TRANS (@lem209643 a c d b) (@lem209672 a b c d)). Qed.
Lemma lem209680 (a : nat) (b : nat) (c : nat) (d : nat) : ((term4 a b c d) = (term4 c a d b)) = ((term5 a b c d) = (term5 a b c d)).
Proof. exact (MK_COMB (@lem209630 a b c d) (@lem209679 a b c d)). Qed.
Lemma lem209682 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem209603 A x) (@lem209602 A x)). Qed.
Lemma lem209683 (x : nat) : (x = x) = True.
Proof. exact (@lem209682 nat x). Qed.
Lemma lem209684 (a : nat) (b : nat) (c : nat) (d : nat) : ((term5 a b c d) = (term5 a b c d)) = True.
Proof. exact (@lem209683 (term5 a b c d)). Qed.
Lemma lem209685 (c : nat) (a : nat) (d : nat) (b : nat) : ((term4 a b c d) = (term4 c a d b)) = True.
Proof. exact (TRANS (@lem209680 a b c d) (@lem209684 a b c d)). Qed.
Lemma lem209686 (c : nat) (a : nat) (d : nat) (b : nat) : True = ((term4 a b c d) = (term4 c a d b)).
Proof. exact (SYM (@lem209685 c a d b)). Qed.
Lemma lem209688 (m : nat) : term8 m.
Proof. exact (@lem82128 m). Qed.
Lemma lem209689 (m : nat) : (term8 m) = (term9 m).
Proof. exact (eq_refl (term8 m)). Qed.
Lemma lem209690 (m : nat) : term9 m.
Proof. exact (EQ_MP (@lem209689 m) (@lem209688 m)). Qed.
Lemma lem209691 (m : nat) (n : nat) : term10 m n.
Proof. exact (@lem209690 m n). Qed.
Lemma lem209692 (m : nat) (n : nat) : (term10 m n) = (term11 m n).
Proof. exact (eq_refl (term10 m n)). Qed.
Lemma lem209693 (m : nat) (n : nat) : term11 m n.
Proof. exact (EQ_MP (@lem209692 m n) (@lem209691 m n)). Qed.
Lemma lem209694 (m : nat) (n : nat) (p : nat) : term12 m n p.
Proof. exact (@lem209693 m n p). Qed.
Lemma lem209695 (m : nat) (n : nat) (p : nat) : (term12 m n p) = ((term13 m n p) = (term14 m n p)).
Proof. exact (eq_refl (term12 m n p)). Qed.
Lemma lem209697 (h1 : term15) : term15.
Proof. exact (h1). Qed.
Lemma lem209698 (m : nat) (h1 : term15) : term16 m.
Proof. exact (@lem209697 h1 m). Qed.
Lemma lem209699 (m : nat) : (term16 m) = (term17 m).
Proof. exact (eq_refl (term16 m)). Qed.
Lemma lem209700 (m : nat) (h1 : term15) : term17 m.
Proof. exact (EQ_MP (@lem209699 m) (@lem209698 m h1)). Qed.
Lemma lem209701 (m : nat) (n : nat) (h1 : term15) : term18 m n.
Proof. exact (@lem209700 m h1 n). Qed.
Lemma lem209702 (m : nat) (n : nat) : (term18 m n) = (term19 m n).
Proof. exact (eq_refl (term18 m n)). Qed.
Lemma lem209703 (m : nat) (n : nat) (h1 : term15) : term19 m n.
Proof. exact (EQ_MP (@lem209702 m n) (@lem209701 m n h1)). Qed.
Lemma lem209704 (m : nat) (n : nat) (p : nat) (h1 : term15) : term20 m n p.
Proof. exact (@lem209703 m n h1 p). Qed.
Lemma lem209705 (m : nat) (n : nat) (p : nat) : (term20 m n p) = (term21 m n p).
Proof. exact (eq_refl (term20 m n p)). Qed.
Lemma lem209706 (m : nat) (n : nat) (p : nat) (h1 : term15) : term21 m n p.
Proof. exact (EQ_MP (@lem209705 m n p) (@lem209704 m n p h1)). Qed.
Lemma lem209707 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term15) : term22 m n p q.
Proof. exact (@lem209706 m n p h1 q). Qed.
Lemma lem209708 (q : nat) (m : nat) (n : nat) (p : nat) : (term22 m n p q) = (term23 q m n p).
Proof. exact (eq_refl (term22 m n p q)). Qed.
Lemma lem209709 (q : nat) (m : nat) (n : nat) (p : nat) (h1 : term15) : term23 q m n p.
Proof. exact (EQ_MP (@lem209708 q m n p) (@lem209707 m n p q h1)). Qed.
Lemma lem209710 (m : nat) (n : nat) (q : nat) (p : nat) (h1 : m = (term24 n q p)) : m = (term24 n q p).
Proof. exact (h1). Qed.
Lemma lem209711 (m : nat) (n : nat) (q : nat) (p : nat) (h1 : term15) (h2 : m = (term24 n q p)) : (Nat.modulo m p) = (Nat.modulo n p).
Proof. exact (@lem209709 q m n p h1 (@lem209710 m n q p h2)). Qed.
Lemma lem209712 (m : nat) (n : nat) (q : nat) (p : nat) (h1 : m = (term24 n q p)) : term25 m n p.
Proof. exact (fun h0 : term15 => @lem209711 m n q p h0 h1). Qed.
Lemma lem209713 (m : nat) (n : nat) (p : nat) (h1 : term26 m n p) : term26 m n p.
Proof. exact (h1). Qed.
Lemma lem209714 (m : nat) (n : nat) (p : nat) (h1 : term26 m n p) : term25 m n p.
Proof. exact (ex_elim (@lem209713 m n p h1) (fun q : nat => fun h0 : term27 m n p q => @lem209712 m n q p h0)). Qed.
Lemma lem209715 (h1 : term15) : term15.
Proof. exact (h1). Qed.
Lemma lem209716 (m : nat) (n : nat) (p : nat) (h1 : term15) (h2 : term26 m n p) : (Nat.modulo m p) = (Nat.modulo n p).
Proof. exact (@lem209714 m n p h2 (@lem209715 h1)). Qed.
Lemma lem209717 (m : nat) (n : nat) (p : nat) (h1 : term15) : term28 m n p.
Proof. exact (fun h0 : term26 m n p => @lem209716 m n p h1 h0). Qed.
Lemma lem209718 (m : nat) (n : nat) (h1 : term15) : term29 m n.
Proof. exact (fun p : nat => @lem209717 m n p h1). Qed.
Lemma lem209719 (m : nat) (h1 : term15) : term30 m.
Proof. exact (fun n : nat => @lem209718 m n h1). Qed.
Lemma lem209720 (h1 : term15) : term31.
Proof. exact (fun m : nat => @lem209719 m h1). Qed.
Lemma lem209721 : term32.
Proof. exact (fun h0 : term15 => @lem209720 h0). Qed.
Lemma lem209722 : term31.
Proof. exact (@lem209721 (@lem178251)). Qed.
Lemma lem209723 (m : nat) : term33 m.
Proof. exact (@lem209722 m). Qed.
Lemma lem209724 (m : nat) : (term33 m) = (term30 m).
Proof. exact (eq_refl (term33 m)). Qed.
Lemma lem209725 (m : nat) : term30 m.
Proof. exact (EQ_MP (@lem209724 m) (@lem209723 m)). Qed.
Lemma lem209726 (m : nat) (n : nat) : term34 m n.
Proof. exact (@lem209725 m n). Qed.
Lemma lem209727 (m : nat) (n : nat) : (term34 m n) = (term29 m n).
Proof. exact (eq_refl (term34 m n)). Qed.
Lemma lem209728 (m : nat) (n : nat) : term29 m n.
Proof. exact (EQ_MP (@lem209727 m n) (@lem209726 m n)). Qed.
Lemma lem209729 (m : nat) (n : nat) (p : nat) : term35 m n p.
Proof. exact (@lem209728 m n p). Qed.
Lemma lem209730 (m : nat) (n : nat) (p : nat) : (term35 m n p) = (term28 m n p).
Proof. exact (eq_refl (term35 m n p)). Qed.
Lemma lem209732 (n : nat) : term36 n.
Proof. exact (@lem9784 (n = (NUMERAL 0))). Qed.
Lemma lem209733 (n : nat) : (term36 n) = (term37 n).
Proof. exact (eq_refl (term36 n)). Qed.
Lemma lem209734 (n : nat) : term37 n.
Proof. exact (EQ_MP (@lem209733 n) (@lem209732 n)). Qed.
Lemma lem209736 (n : nat) (h1 : term38 n) : term38 n.
Proof. exact (h1). Qed.
Lemma lem209737 (n : nat) : term39 n.
Proof. exact (@lem159121 n). Qed.
Lemma lem209738 (n : nat) : (term39 n) = ((term40 n) = n).
Proof. exact (eq_refl (term39 n)). Qed.
Lemma lem209743 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem209744 (a : nat) : (Nat.modulo a) = (Nat.modulo a).
Proof. exact (eq_refl (Nat.modulo a)). Qed.
Lemma lem209745 (a : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.modulo a n) = (term40 a).
Proof. exact (MK_COMB (@lem209744 a) (@lem209743 n h1)). Qed.
Lemma lem209747 (n : nat) : (term40 n) = n.
Proof. exact (EQ_MP (@lem209738 n) (@lem209737 n)). Qed.
Lemma lem209748 (a : nat) : (term40 a) = a.
Proof. exact (@lem209747 a). Qed.
Lemma lem209749 (a : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.modulo a n) = a.
Proof. exact (TRANS (@lem209745 a n h1) (@lem209748 a)). Qed.
Lemma lem209750 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem209751 (a : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term41 a n) = (Nat.add a).
Proof. exact (MK_COMB (@lem209750) (@lem209749 a n h1)). Qed.
Lemma lem209753 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem209754 (b : nat) : (Nat.modulo b) = (Nat.modulo b).
Proof. exact (eq_refl (Nat.modulo b)). Qed.
Lemma lem209755 (b : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.modulo b n) = (term40 b).
Proof. exact (MK_COMB (@lem209754 b) (@lem209753 n h1)). Qed.
Lemma lem209757 (n : nat) : (term40 n) = n.
Proof. exact (EQ_MP (@lem209738 n) (@lem209737 n)). Qed.
Lemma lem209758 (b : nat) : (term40 b) = b.
Proof. exact (@lem209757 b). Qed.
Lemma lem209759 (b : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.modulo b n) = b.
Proof. exact (TRANS (@lem209755 b n h1) (@lem209758 b)). Qed.
Lemma lem209760 (a : nat) (b : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term42 a b n) = (Nat.add a b).
Proof. exact (MK_COMB (@lem209751 a n h1) (@lem209759 b n h1)). Qed.
Lemma lem209761 : Nat.modulo = Nat.modulo.
Proof. exact (eq_refl Nat.modulo). Qed.
Lemma lem209762 (a : nat) (b : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term43 a b n) = (term44 a b).
Proof. exact (MK_COMB (@lem209761) (@lem209760 a b n h1)). Qed.
Lemma lem209764 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem209765 (a : nat) (b : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term45 a b n) = (term46 a b).
Proof. exact (MK_COMB (@lem209762 a b n h1) (@lem209764 n h1)). Qed.
Lemma lem209767 (n : nat) : (term40 n) = n.
Proof. exact (EQ_MP (@lem209738 n) (@lem209737 n)). Qed.
Lemma lem209768 (a : nat) (b : nat) : (term46 a b) = (Nat.add a b).
Proof. exact (@lem209767 (Nat.add a b)). Qed.
Lemma lem209769 (a : nat) (b : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term45 a b n) = (Nat.add a b).
Proof. exact (TRANS (@lem209765 a b n h1) (@lem209768 a b)). Qed.
Lemma lem209770 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem209771 (a : nat) (b : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term47 a b n) = (term48 a b).
Proof. exact (MK_COMB (@lem209770) (@lem209769 a b n h1)). Qed.
Lemma lem209773 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem209774 (a : nat) (b : nat) : (term44 a b) = (term44 a b).
Proof. exact (eq_refl (term44 a b)). Qed.
Lemma lem209775 (a : nat) (b : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term49 a b n) = (term46 a b).
Proof. exact (MK_COMB (@lem209774 a b) (@lem209773 n h1)). Qed.
Lemma lem209777 (n : nat) : (term40 n) = n.
Proof. exact (EQ_MP (@lem209738 n) (@lem209737 n)). Qed.
Lemma lem209778 (a : nat) (b : nat) : (term46 a b) = (Nat.add a b).
Proof. exact (@lem209777 (Nat.add a b)). Qed.
Lemma lem209779 (a : nat) (b : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term49 a b n) = (Nat.add a b).
Proof. exact (TRANS (@lem209775 a b n h1) (@lem209778 a b)). Qed.
Lemma lem209780 (a : nat) (b : nat) (n : nat) (h1 : n = (NUMERAL 0)) : ((term45 a b n) = (term49 a b n)) = ((Nat.add a b) = (Nat.add a b)).
Proof. exact (MK_COMB (@lem209771 a b n h1) (@lem209779 a b n h1)). Qed.
Lemma lem209782 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem209783 (x : nat) : (x = x) = True.
Proof. exact (@lem209782 nat x). Qed.
Lemma lem209784 (a : nat) (b : nat) : ((Nat.add a b) = (Nat.add a b)) = True.
Proof. exact (@lem209783 (Nat.add a b)). Qed.
Lemma lem209785 (a : nat) (b : nat) (n : nat) (h1 : n = (NUMERAL 0)) : ((term45 a b n) = (term49 a b n)) = True.
Proof. exact (TRANS (@lem209780 a b n h1) (@lem209784 a b)). Qed.
Lemma lem209786 (a : nat) (b : nat) (n : nat) (h1 : n = (NUMERAL 0)) : True = ((term45 a b n) = (term49 a b n)).
Proof. exact (SYM (@lem209785 a b n h1)). Qed.
Lemma lem209787 (a : nat) (b : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term45 a b n) = (term49 a b n).
Proof. exact (EQ_MP (@lem209786 a b n h1) (@lem0)). Qed.
Lemma lem209808 (a : nat) (b : nat) (n : nat) (h1 : (term45 a b n) = (term49 a b n)) : (term45 a b n) = (term49 a b n).
Proof. exact (h1). Qed.
Lemma lem209809 (a : nat) (b : nat) (n : nat) (h1 : (term45 a b n) = (term49 a b n)) : (term49 a b n) = (term45 a b n).
Proof. exact (SYM (@lem209808 a b n h1)). Qed.
Lemma lem209810 (a : nat) (b : nat) (n : nat) (h1 : (term49 a b n) = (term45 a b n)) : (term49 a b n) = (term45 a b n).
Proof. exact (h1). Qed.
Lemma lem209811 (a : nat) (b : nat) (n : nat) (h1 : (term49 a b n) = (term45 a b n)) : (term45 a b n) = (term49 a b n).
Proof. exact (SYM (@lem209810 a b n h1)). Qed.
Lemma lem209812 (a : nat) (b : nat) (n : nat) : ((term45 a b n) = (term49 a b n)) = ((term49 a b n) = (term45 a b n)).
Proof. exact (prop_ext (fun h1 : (term45 a b n) = (term49 a b n) => @lem209809 a b n h1) (fun h1 : (term49 a b n) = (term45 a b n) => @lem209811 a b n h1)). Qed.
Lemma lem209813 (a : nat) (b : nat) (n : nat) : ((term49 a b n) = (term45 a b n)) = ((term45 a b n) = (term49 a b n)).
Proof. exact (SYM (@lem209812 a b n)). Qed.
Lemma lem209815 (m : nat) (n : nat) (p : nat) : term28 m n p.
Proof. exact (EQ_MP (@lem209730 m n p) (@lem209729 m n p)). Qed.
Lemma lem209816 (a : nat) (b : nat) (n : nat) : term50 a b n.
Proof. exact (@lem209815 (Nat.add a b) (term42 a b n) n). Qed.
Lemma lem209820 (m : nat) (n : nat) (p : nat) : (term13 m n p) = (term14 m n p).
Proof. exact (EQ_MP (@lem209695 m n p) (@lem209694 m n p)). Qed.
Lemma lem209821 (a : nat) (b : nat) (n : nat) : (term51 a b n) = (term52 a b n).
Proof. exact (@lem209820 (Nat.div a n) (Nat.div b n) n). Qed.
Lemma lem209822 (a : nat) (b : nat) (n : nat) : (term53 a b n) = (term53 a b n).
Proof. exact (eq_refl (term53 a b n)). Qed.
Lemma lem209823 (a : nat) (b : nat) (n : nat) : (term54 a b n) = (term55 a b n).
Proof. exact (MK_COMB (@lem209822 a b n) (@lem209821 a b n)). Qed.
Lemma lem209824 (a : nat) (b : nat) : (term48 a b) = (term48 a b).
Proof. exact (eq_refl (term48 a b)). Qed.
Lemma lem209825 (a : nat) (b : nat) (n : nat) : ((Nat.add a b) = (term54 a b n)) = ((Nat.add a b) = (term55 a b n)).
Proof. exact (MK_COMB (@lem209824 a b) (@lem209823 a b n)). Qed.
Lemma lem209828 (a : nat) (b : nat) (n : nat) : ((Nat.add a b) = (term55 a b n)) = ((Nat.add a b) = (term54 a b n)).
Proof. exact (SYM (@lem209825 a b n)). Qed.
Lemma lem209832 (c : nat) (a : nat) (d : nat) (b : nat) : (term4 a b c d) = (term4 c a d b).
Proof. exact (EQ_MP (@lem209686 c a d b) (@lem0)). Qed.
Lemma lem209833 (a : nat) (b : nat) (n : nat) : (term55 a b n) = (term56 a b n).
Proof. exact (@lem209832 (term57 a n) (Nat.modulo a n) (term57 b n) (Nat.modulo b n)). Qed.
Lemma lem209834 (a : nat) (b : nat) : (term48 a b) = (term48 a b).
Proof. exact (eq_refl (term48 a b)). Qed.
Lemma lem209835 (a : nat) (b : nat) (n : nat) : ((Nat.add a b) = (term55 a b n)) = ((Nat.add a b) = (term56 a b n)).
Proof. exact (MK_COMB (@lem209834 a b) (@lem209833 a b n)). Qed.
Lemma lem209836 (a : nat) (b : nat) (n : nat) : ((Nat.add a b) = (term56 a b n)) = ((Nat.add a b) = (term55 a b n)).
Proof. exact (SYM (@lem209835 a b n)). Qed.
Lemma lem209837 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem209838 (m : nat) : term58 m.
Proof. exact (@lem157261 m). Qed.
Lemma lem209839 (m : nat) : (term58 m) = (term59 m).
Proof. exact (eq_refl (term58 m)). Qed.
Lemma lem209840 (m : nat) : term59 m.
Proof. exact (EQ_MP (@lem209839 m) (@lem209838 m)). Qed.
Lemma lem209841 (m : nat) (n : nat) : term60 m n.
Proof. exact (@lem209840 m n). Qed.
Lemma lem209842 (m : nat) (n : nat) : (term60 m n) = (term61 m n).
Proof. exact (eq_refl (term60 m n)). Qed.
Lemma lem209843 (m : nat) (n : nat) : term61 m n.
Proof. exact (EQ_MP (@lem209842 m n) (@lem209841 m n)). Qed.
Lemma lem209844 (n : nat) (h1 : term38 n) : term38 n.
Proof. exact (h1). Qed.
Lemma lem209845 (m : nat) (n : nat) (h1 : term38 n) : term62 m n.
Proof. exact (@lem209843 m n (@lem209844 n h1)). Qed.
Lemma lem209854 (m : nat) (n : nat) (h1 : term38 n) : m = (term63 m n).
Proof. exact (proj1 (@lem209845 m n h1)). Qed.
Lemma lem209859 (m : nat) (n : nat) : term64 m n.
Proof. exact (fun h0 : term38 n => @lem209854 m n h0). Qed.
Lemma lem209860 (n : nat) (h1 : term38 n) : term38 n.
Proof. exact (h1). Qed.
Lemma lem209861 (m : nat) (n : nat) (h1 : term38 n) : m = (term63 m n).
Proof. exact (@lem209859 m n (@lem209860 n h1)). Qed.
Lemma lem209862 (m : nat) (n : nat) : (m = (term63 m n)) = ((m = (term63 m n)) = True).
Proof. exact (@lem7 (m = (term63 m n))). Qed.
Lemma lem209863 (m : nat) (n : nat) (h1 : term38 n) : (m = (term63 m n)) = True.
Proof. exact (EQ_MP (@lem209862 m n) (@lem209861 m n h1)). Qed.
Lemma lem209865 (n : nat) : term65 n.
Proof. exact (@lem82 (n = (NUMERAL 0))). Qed.
Lemma lem209881 (m : nat) (n : nat) : term66 m n.
Proof. exact (fun h0 : term38 n => @lem209863 m n h0). Qed.
Lemma lem209882 (a : nat) (n : nat) : term66 a n.
Proof. exact (@lem209881 a n). Qed.
Lemma lem209888 (n : nat) (h1 : term38 n) : (n = (NUMERAL 0)) = False.
Proof. exact (@lem209865 n (@lem209736 n h1)). Qed.
Lemma lem209891 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem209892 (n : nat) (h1 : term38 n) : (term38 n) = (~ False).
Proof. exact (MK_COMB (@lem209891) (@lem209888 n h1)). Qed.
Lemma lem209894 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem209897 (n : nat) (h1 : term38 n) : (term38 n) = True.
Proof. exact (TRANS (@lem209892 n h1) (@lem209894)). Qed.
Lemma lem209898 (n : nat) (h1 : term38 n) : True = (term38 n).
Proof. exact (SYM (@lem209897 n h1)). Qed.
Lemma lem209899 (n : nat) (h1 : term38 n) : term38 n.
Proof. exact (EQ_MP (@lem209898 n h1) (@lem0)). Qed.
Lemma lem209900 (a : nat) (n : nat) (h1 : term38 n) : (a = (term63 a n)) = True.
Proof. exact (@lem209882 a n (@lem209899 n h1)). Qed.
Lemma lem209903 (a : nat) (n : nat) (h1 : term38 n) : True = (a = (term63 a n)).
Proof. exact (SYM (@lem209900 a n h1)). Qed.
Lemma lem209904 (a : nat) (n : nat) (h1 : term38 n) : a = (term63 a n).
Proof. exact (EQ_MP (@lem209903 a n h1) (@lem0)). Qed.
Lemma lem209905 (m : nat) : term58 m.
Proof. exact (@lem157261 m). Qed.
Lemma lem209906 (m : nat) : (term58 m) = (term59 m).
Proof. exact (eq_refl (term58 m)). Qed.
Lemma lem209907 (m : nat) : term59 m.
Proof. exact (EQ_MP (@lem209906 m) (@lem209905 m)). Qed.
Lemma lem209908 (m : nat) (n : nat) : term60 m n.
Proof. exact (@lem209907 m n). Qed.
Lemma lem209909 (m : nat) (n : nat) : (term60 m n) = (term61 m n).
Proof. exact (eq_refl (term60 m n)). Qed.
Lemma lem209910 (m : nat) (n : nat) : term61 m n.
Proof. exact (EQ_MP (@lem209909 m n) (@lem209908 m n)). Qed.
Lemma lem209911 (n : nat) (h1 : term38 n) : term38 n.
Proof. exact (h1). Qed.
Lemma lem209912 (m : nat) (n : nat) (h1 : term38 n) : term62 m n.
Proof. exact (@lem209910 m n (@lem209911 n h1)). Qed.
Lemma lem209921 (m : nat) (n : nat) (h1 : term38 n) : m = (term63 m n).
Proof. exact (proj1 (@lem209912 m n h1)). Qed.
Lemma lem209926 (m : nat) (n : nat) : term64 m n.
Proof. exact (fun h0 : term38 n => @lem209921 m n h0). Qed.
Lemma lem209927 (n : nat) (h1 : term38 n) : term38 n.
Proof. exact (h1). Qed.
Lemma lem209928 (m : nat) (n : nat) (h1 : term38 n) : m = (term63 m n).
Proof. exact (@lem209926 m n (@lem209927 n h1)). Qed.
Lemma lem209929 (m : nat) (n : nat) : (m = (term63 m n)) = ((m = (term63 m n)) = True).
Proof. exact (@lem7 (m = (term63 m n))). Qed.
Lemma lem209930 (m : nat) (n : nat) (h1 : term38 n) : (m = (term63 m n)) = True.
Proof. exact (EQ_MP (@lem209929 m n) (@lem209928 m n h1)). Qed.
Lemma lem209932 (n : nat) : term65 n.
Proof. exact (@lem82 (n = (NUMERAL 0))). Qed.
Lemma lem209948 (m : nat) (n : nat) : term66 m n.
Proof. exact (fun h0 : term38 n => @lem209930 m n h0). Qed.
Lemma lem209949 (b : nat) (n : nat) : term66 b n.
Proof. exact (@lem209948 b n). Qed.
Lemma lem209955 (n : nat) (h1 : term38 n) : (n = (NUMERAL 0)) = False.
Proof. exact (@lem209932 n (@lem209736 n h1)). Qed.
Lemma lem209958 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem209959 (n : nat) (h1 : term38 n) : (term38 n) = (~ False).
Proof. exact (MK_COMB (@lem209958) (@lem209955 n h1)). Qed.
Lemma lem209961 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem209964 (n : nat) (h1 : term38 n) : (term38 n) = True.
Proof. exact (TRANS (@lem209959 n h1) (@lem209961)). Qed.
Lemma lem209965 (n : nat) (h1 : term38 n) : True = (term38 n).
Proof. exact (SYM (@lem209964 n h1)). Qed.
Lemma lem209966 (n : nat) (h1 : term38 n) : term38 n.
Proof. exact (EQ_MP (@lem209965 n h1) (@lem0)). Qed.
Lemma lem209967 (b : nat) (n : nat) (h1 : term38 n) : (b = (term63 b n)) = True.
Proof. exact (@lem209949 b n (@lem209966 n h1)). Qed.
Lemma lem209970 (b : nat) (n : nat) (h1 : term38 n) : True = (b = (term63 b n)).
Proof. exact (SYM (@lem209967 b n h1)). Qed.
Lemma lem209971 (b : nat) (n : nat) (h1 : term38 n) : b = (term63 b n).
Proof. exact (EQ_MP (@lem209970 b n h1) (@lem0)). Qed.
Lemma lem209972 (a : nat) (n : nat) (h1 : term38 n) : (Nat.add a) = (term67 a n).
Proof. exact (MK_COMB (@lem209837) (@lem209904 a n h1)). Qed.
Lemma lem209973 (a : nat) (b : nat) (n : nat) (h1 : term38 n) : (Nat.add a b) = (term56 a b n).
Proof. exact (MK_COMB (@lem209972 a n h1) (@lem209971 b n h1)). Qed.
Lemma lem209974 (a : nat) (b : nat) (n : nat) (h1 : term38 n) : (Nat.add a b) = (term55 a b n).
Proof. exact (EQ_MP (@lem209836 a b n) (@lem209973 a b n h1)). Qed.
Lemma lem209975 (a : nat) (b : nat) (n : nat) (h1 : term38 n) : (Nat.add a b) = (term54 a b n).
Proof. exact (EQ_MP (@lem209828 a b n) (@lem209974 a b n h1)). Qed.
Lemma lem209976 (a : nat) (b : nat) (n : nat) (h1 : term38 n) : term68 a b n.
Proof. exact (ex_intro (term69 a b n) (term70 a b n) (@lem209975 a b n h1)). Qed.
Lemma lem209977 (a : nat) (b : nat) (n : nat) (h1 : term38 n) : (term49 a b n) = (term45 a b n).
Proof. exact (@lem209816 a b n (@lem209976 a b n h1)). Qed.
Lemma lem209979 (a : nat) (b : nat) (n : nat) (h1 : term38 n) : (term45 a b n) = (term49 a b n).
Proof. exact (EQ_MP (@lem209813 a b n) (@lem209977 a b n h1)). Qed.
Lemma lem209980 (a : nat) (b : nat) (n : nat) : (term45 a b n) = (term49 a b n).
Proof. exact (or_elim (@lem209734 n) (fun h0 : n = (NUMERAL 0) => @lem209787 a b n h0) (fun h0 : term38 n => @lem209979 a b n h0)). Qed.
Lemma lem209985 (a : nat) (b : nat) : term71 a b.
Proof. exact (fun n : nat => @lem209980 a b n). Qed.
Lemma lem209990 (a : nat) : term72 a.
Proof. exact (fun b : nat => @lem209985 a b). Qed.
Lemma lem209995 : term73.
Proof. exact (fun a : nat => @lem209990 a). Qed.
