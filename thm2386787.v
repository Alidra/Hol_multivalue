Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2386787_term_abbrevs.
Require Import SKOLEM_THM_spec.
Require Import thm2385965_spec.
Require Import thm2386686_spec.
Require Import thm9261_spec.
Require Import thm9306_spec.
Lemma lem2386687 : term0 = term1.
Proof. exact (eq_refl term0). Qed.
Lemma lem2386688 : term1.
Proof. exact (EQ_MP (@lem2386687) (@lem2385965)). Qed.
Lemma lem2386689 : term2.
Proof. exact (@lem2386688 term3). Qed.
Lemma lem2386690 : term2 = term4.
Proof. exact (eq_refl term2). Qed.
Lemma lem2386691 : term4.
Proof. exact (EQ_MP (@lem2386690) (@lem2386689)). Qed.
Lemma lem2386692 (h1 : div = term5) : div = term5.
Proof. exact (h1). Qed.
Lemma lem2386693 (h1 : div = term5) : term5 = div.
Proof. exact (SYM (@lem2386692 h1)). Qed.
Lemma lem2386694 (h1 : term5 = div) : term5 = div.
Proof. exact (h1). Qed.
Lemma lem2386695 (h1 : term5 = div) : div = term5.
Proof. exact (SYM (@lem2386694 h1)). Qed.
Lemma lem2386696 : (div = term5) = (term5 = div).
Proof. exact (prop_ext (fun h1 : div = term5 => @lem2386693 h1) (fun h1 : term5 = div => @lem2386695 h1)). Qed.
Lemma lem2386699 : term5 = div.
Proof. exact (EQ_MP (@lem2386696) (@lem2386686)). Qed.
Lemma lem2386700 (m : int) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem2386701 (m : int) : (term6 m) = (div m).
Proof. exact (MK_COMB (@lem2386699) (@lem2386700 m)). Qed.
Lemma lem2386702 (n : int) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem2386703 (m : int) (n : int) : (term7 m n) = (div m n).
Proof. exact (MK_COMB (@lem2386701 m) (@lem2386702 n)). Qed.
Lemma lem2386704 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2386705 (m : int) (n : int) : (term8 m n) = (term9 m n).
Proof. exact (MK_COMB (@lem2386704) (@lem2386703 m n)). Qed.
Lemma lem2386706 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem2386707 (m : int) (n : int) : ((term7 m n) = term10) = ((div m n) = term10).
Proof. exact (MK_COMB (@lem2386705 m n) (@lem2386706)). Qed.
Lemma lem2386708 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2386709 (m : int) (n : int) : (term11 m n) = (term12 m n).
Proof. exact (MK_COMB (@lem2386708) (@lem2386707 m n)). Qed.
Lemma lem2386710 (r : type1551) (n : int) (m : int) : ((r m n) = m) = ((r m n) = m).
Proof. exact (eq_refl ((r m n) = m)). Qed.
Lemma lem2386711 (r : type1551) (n : int) (m : int) : (term13 r n m) = (term14 r n m).
Proof. exact (MK_COMB (@lem2386709 m n) (@lem2386710 r n m)). Qed.
Lemma lem2386712 (n : int) : (term15 n) = (term15 n).
Proof. exact (eq_refl (term15 n)). Qed.
Lemma lem2386713 (r : type1551) (n : int) (m : int) : (term16 r n m) = (term17 r n m).
Proof. exact (MK_COMB (@lem2386712 n) (@lem2386711 r n m)). Qed.
Lemma lem2386715 : term5 = div.
Proof. exact (EQ_MP (@lem2386696) (@lem2386686)). Qed.
Lemma lem2386716 (m : int) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem2386717 (m : int) : (term6 m) = (div m).
Proof. exact (MK_COMB (@lem2386715) (@lem2386716 m)). Qed.
Lemma lem2386718 (n : int) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem2386719 (m : int) (n : int) : (term7 m n) = (div m n).
Proof. exact (MK_COMB (@lem2386717 m) (@lem2386718 n)). Qed.
Lemma lem2386720 : int_mul = int_mul.
Proof. exact (eq_refl int_mul). Qed.
Lemma lem2386721 (m : int) (n : int) : (term18 m n) = (term19 m n).
Proof. exact (MK_COMB (@lem2386720) (@lem2386719 m n)). Qed.
Lemma lem2386722 (n : int) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem2386723 (m : int) (n : int) : (term20 m n) = (term21 m n).
Proof. exact (MK_COMB (@lem2386721 m n) (@lem2386722 n)). Qed.
Lemma lem2386724 : int_add = int_add.
Proof. exact (eq_refl int_add). Qed.
Lemma lem2386725 (m : int) (n : int) : (term22 m n) = (term23 m n).
Proof. exact (MK_COMB (@lem2386724) (@lem2386723 m n)). Qed.
Lemma lem2386726 (r : type1551) (m : int) (n : int) : (r m n) = (r m n).
Proof. exact (eq_refl (r m n)). Qed.
Lemma lem2386727 (r : type1551) (m : int) (n : int) : (term24 r m n) = (term25 r m n).
Proof. exact (MK_COMB (@lem2386725 m n) (@lem2386726 r m n)). Qed.
Lemma lem2386728 (m : int) : (@eq int m) = (@eq int m).
Proof. exact (eq_refl (@eq int m)). Qed.
Lemma lem2386729 (r : type1551) (m : int) (n : int) : (m = (term24 r m n)) = (m = (term25 r m n)).
Proof. exact (MK_COMB (@lem2386728 m) (@lem2386727 r m n)). Qed.
Lemma lem2386730 (r : type1551) (m : int) (n : int) : (term26 r m n) = (term26 r m n).
Proof. exact (eq_refl (term26 r m n)). Qed.
Lemma lem2386731 (r : type1551) (m : int) (n : int) : (term27 r m n) = (term28 r m n).
Proof. exact (MK_COMB (@lem2386730 r m n) (@lem2386729 r m n)). Qed.
Lemma lem2386732 (r : type1551) (m : int) (n : int) : (term29 r m n) = (term29 r m n).
Proof. exact (eq_refl (term29 r m n)). Qed.
Lemma lem2386733 (r : type1551) (m : int) (n : int) : (term30 r m n) = (term31 r m n).
Proof. exact (MK_COMB (@lem2386732 r m n) (@lem2386731 r m n)). Qed.
Lemma lem2386734 (r : type1551) (m : int) (n : int) : (term32 r m n) = (term33 r m n).
Proof. exact (MK_COMB (@lem2386713 r n m) (@lem2386733 r m n)). Qed.
Lemma lem2386735 (r : type1551) (m : int) : (term34 r m) = (term35 r m).
Proof. exact (fun_ext (fun n : int => @lem2386734 r m n)). Qed.
Lemma lem2386736 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2386737 (r : type1551) (m : int) : (term36 r m) = (term37 r m).
Proof. exact (MK_COMB (@lem2386736) (@lem2386735 r m)). Qed.
Lemma lem2386738 (r : type1551) : (term38 r) = (term39 r).
Proof. exact (fun_ext (fun m : int => @lem2386737 r m)). Qed.
Lemma lem2386739 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2386740 (r : type1551) : (term40 r) = (term41 r).
Proof. exact (MK_COMB (@lem2386739) (@lem2386738 r)). Qed.
Lemma lem2386741 : term42 = term43.
Proof. exact (fun_ext (fun r : type1551 => @lem2386740 r)). Qed.
Lemma lem2386742 : (@ex (int -> int -> int)) = (@ex (int -> int -> int)).
Proof. exact (eq_refl (@ex (int -> int -> int))). Qed.
Lemma lem2386743 : term4 = term44.
Proof. exact (MK_COMB (@lem2386742) (@lem2386741)). Qed.
Lemma lem2386744 : term44.
Proof. exact (EQ_MP (@lem2386743) (@lem2386691)). Qed.
Lemma lem2386745 : term45.
Proof. exact (fun _29200 : type1674 => @lem2386744). Qed.
Lemma lem2386746 {A B : Type'} (P : type1413 A B) : term46 A B P.
Proof. exact (@lem13546 A B P). Qed.
Lemma lem2386747 {A B : Type'} (P : type1413 A B) : (term46 A B P) = ((term47 A B P) = (term48 A B P)).
Proof. exact (eq_refl (term46 A B P)). Qed.
Lemma lem2386750 {A B : Type'} (P : type1413 A B) : (term47 A B P) = (term48 A B P).
Proof. exact (EQ_MP (@lem2386747 A B P) (@lem2386746 A B P)). Qed.
Lemma lem2386751 (P : type1299) : (term49 P) = (term50 P).
Proof. exact (@lem2386750 type1674 type1551 P). Qed.
Lemma lem2386752 : term51 = term52.
Proof. exact (@lem2386751 term53). Qed.
Lemma lem2386753 (_29200 : type1674) : (term54 _29200) = term43.
Proof. exact (eq_refl (term54 _29200)). Qed.
Lemma lem2386754 (r : type1551) : r = r.
Proof. exact (eq_refl r). Qed.
Lemma lem2386755 (_29200 : type1674) (r : type1551) : (term55 _29200 r) = (term56 r).
Proof. exact (MK_COMB (@lem2386753 _29200) (@lem2386754 r)). Qed.
Lemma lem2386756 (r : type1551) : (term56 r) = (term41 r).
Proof. exact (eq_refl (term56 r)). Qed.
Lemma lem2386757 (_29200 : type1674) (r : type1551) : (term55 _29200 r) = (term41 r).
Proof. exact (TRANS (@lem2386755 _29200 r) (@lem2386756 r)). Qed.
Lemma lem2386758 (_29200 : type1674) : (term57 _29200) = term43.
Proof. exact (fun_ext (fun r : type1551 => @lem2386757 _29200 r)). Qed.
Lemma lem2386759 : (@ex (int -> int -> int)) = (@ex (int -> int -> int)).
Proof. exact (eq_refl (@ex (int -> int -> int))). Qed.
Lemma lem2386760 (_29200 : type1674) : (term58 _29200) = term44.
Proof. exact (MK_COMB (@lem2386759) (@lem2386758 _29200)). Qed.
Lemma lem2386761 : term59 = term60.
Proof. exact (fun_ext (fun _29200 : type1674 => @lem2386760 _29200)). Qed.
Lemma lem2386762 : (@all (prod nat (prod nat nat))) = (@all (prod nat (prod nat nat))).
Proof. exact (eq_refl (@all (prod nat (prod nat nat)))). Qed.
Lemma lem2386763 : term51 = term45.
Proof. exact (MK_COMB (@lem2386762) (@lem2386761)). Qed.
Lemma lem2386764 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2386765 : term61 = term62.
Proof. exact (MK_COMB (@lem2386764) (@lem2386763)). Qed.
Lemma lem2386766 (_29200 : type1674) : (term54 _29200) = term43.
Proof. exact (eq_refl (term54 _29200)). Qed.
Lemma lem2386767 (r : type1305) (_29200 : type1674) : (r _29200) = (r _29200).
Proof. exact (eq_refl (r _29200)). Qed.
Lemma lem2386768 (r : type1305) (_29200 : type1674) : (term63 r _29200) = (term64 r _29200).
Proof. exact (MK_COMB (@lem2386766 _29200) (@lem2386767 r _29200)). Qed.
Lemma lem2386769 (r : type1305) (_29200 : type1674) : (term64 r _29200) = (term65 r _29200).
Proof. exact (eq_refl (term64 r _29200)). Qed.
Lemma lem2386770 (r : type1305) (_29200 : type1674) : (term63 r _29200) = (term65 r _29200).
Proof. exact (TRANS (@lem2386768 r _29200) (@lem2386769 r _29200)). Qed.
Lemma lem2386771 (r : type1305) : (term66 r) = (term67 r).
Proof. exact (fun_ext (fun _29200 : type1674 => @lem2386770 r _29200)). Qed.
Lemma lem2386772 : (@all (prod nat (prod nat nat))) = (@all (prod nat (prod nat nat))).
Proof. exact (eq_refl (@all (prod nat (prod nat nat)))). Qed.
Lemma lem2386773 (r : type1305) : (term68 r) = (term69 r).
Proof. exact (MK_COMB (@lem2386772) (@lem2386771 r)). Qed.
Lemma lem2386774 : term70 = term71.
Proof. exact (fun_ext (fun r : type1305 => @lem2386773 r)). Qed.
Lemma lem2386775 : (@ex ((prod nat (prod nat nat)) -> int -> int -> int)) = (@ex ((prod nat (prod nat nat)) -> int -> int -> int)).
Proof. exact (eq_refl (@ex ((prod nat (prod nat nat)) -> int -> int -> int))). Qed.
Lemma lem2386776 : term52 = term72.
Proof. exact (MK_COMB (@lem2386775) (@lem2386774)). Qed.
Lemma lem2386777 : (term51 = term52) = (term45 = term72).
Proof. exact (MK_COMB (@lem2386765) (@lem2386776)). Qed.
Lemma lem2386778 : term45 = term72.
Proof. exact (EQ_MP (@lem2386777) (@lem2386752)). Qed.
Lemma lem2386779 : term72.
Proof. exact (EQ_MP (@lem2386778) (@lem2386745)). Qed.
Lemma lem2386781 {A : Type'} : (@ex A) = (term73 A).
Proof. exact (@lem9261 A (@lem9306 A)). Qed.
Lemma lem2386782 : (@ex ((prod nat (prod nat nat)) -> int -> int -> int)) = term74.
Proof. exact (@lem2386781 type1305). Qed.
Lemma lem2386783 : term71 = term71.
Proof. exact (eq_refl term71). Qed.
Lemma lem2386784 : term72 = term75.
Proof. exact (MK_COMB (@lem2386782) (@lem2386783)). Qed.
Lemma lem2386785 : term75 = term76.
Proof. exact (eq_refl term75). Qed.
Lemma lem2386786 : term72 = term76.
Proof. exact (TRANS (@lem2386784) (@lem2386785)). Qed.
Lemma lem2386787 : term76.
Proof. exact (EQ_MP (@lem2386786) (@lem2386779)). Qed.
