Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm85971_term_abbrevs.
Require Import BETA_THM_spec.
Require Import SKOLEM_THM_spec.
Require Import thm75635_spec.
Require Import thm9261_spec.
Require Import thm9306_spec.
Lemma lem85722 {A B : Type'} (f : A -> B) : term0 A B f.
Proof. exact (@lem421 A B f). Qed.
Lemma lem85723 {A B : Type'} (f : A -> B) : (term0 A B f) = (term1 A B f).
Proof. exact (eq_refl (term0 A B f)). Qed.
Lemma lem85724 {A B : Type'} (f : A -> B) : term1 A B f.
Proof. exact (EQ_MP (@lem85723 A B f) (@lem85722 A B f)). Qed.
Lemma lem85725 {A B : Type'} (f : A -> B) (y : A) : term2 A B f y.
Proof. exact (@lem85724 A B f y). Qed.
Lemma lem85726 {A B : Type'} (f : A -> B) (y : A) : (term2 A B f y) = ((term3 A B f y) = (f y)).
Proof. exact (eq_refl (term2 A B f y)). Qed.
Lemma lem85729 (EXP' : type1606) (_2220 : type1606) (h1 : EXP' = (term4 _2220)) : EXP' = (term4 _2220).
Proof. exact (h1). Qed.
Lemma lem85730 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem85731 (m : nat) (EXP' : type1606) (_2220 : type1606) (h1 : EXP' = (term4 _2220)) : (EXP' m) = (term5 _2220 m).
Proof. exact (MK_COMB (@lem85729 EXP' _2220 h1) (@lem85730 m)). Qed.
Lemma lem85733 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem85726 A B f y) (@lem85725 A B f y)). Qed.
Lemma lem85734 (f : type1606) (y : nat) : (term6 f y) = (f y).
Proof. exact (@lem85733 nat (nat -> nat) f y). Qed.
Lemma lem85735 (_2220 : type1606) (m : nat) : (term7 _2220 m) = (term5 _2220 m).
Proof. exact (@lem85734 (term4 _2220) m). Qed.
Lemma lem85736 (_2220 : type1606) (_2218 : nat) : (term5 _2220 _2218) = (term8 _2220 _2218).
Proof. exact (eq_refl (term5 _2220 _2218)). Qed.
Lemma lem85737 (_2220 : type1606) : (term9 _2220) = (term4 _2220).
Proof. exact (fun_ext (fun _2218 : nat => @lem85736 _2220 _2218)). Qed.
Lemma lem85738 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem85739 (_2220 : type1606) (m : nat) : (term7 _2220 m) = (term5 _2220 m).
Proof. exact (MK_COMB (@lem85737 _2220) (@lem85738 m)). Qed.
Lemma lem85740 : (@eq (nat -> nat)) = (@eq (nat -> nat)).
Proof. exact (eq_refl (@eq (nat -> nat))). Qed.
Lemma lem85741 (_2220 : type1606) (m : nat) : (term10 _2220 m) = (term11 _2220 m).
Proof. exact (MK_COMB (@lem85740) (@lem85739 _2220 m)). Qed.
Lemma lem85742 (_2220 : type1606) (m : nat) : (term5 _2220 m) = (term8 _2220 m).
Proof. exact (eq_refl (term5 _2220 m)). Qed.
Lemma lem85743 (_2220 : type1606) (m : nat) : ((term7 _2220 m) = (term5 _2220 m)) = ((term5 _2220 m) = (term8 _2220 m)).
Proof. exact (MK_COMB (@lem85741 _2220 m) (@lem85742 _2220 m)). Qed.
Lemma lem85744 (_2220 : type1606) (m : nat) : (term5 _2220 m) = (term8 _2220 m).
Proof. exact (EQ_MP (@lem85743 _2220 m) (@lem85735 _2220 m)). Qed.
Lemma lem85745 (m : nat) (EXP' : type1606) (_2220 : type1606) (h1 : EXP' = (term4 _2220)) : (EXP' m) = (term8 _2220 m).
Proof. exact (TRANS (@lem85731 m EXP' _2220 h1) (@lem85744 _2220 m)). Qed.
Lemma lem85746 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem85747 (m : nat) (EXP' : type1606) (_2220 : type1606) (h1 : EXP' = (term4 _2220)) : (term12 EXP' m) = (term13 _2220 m).
Proof. exact (MK_COMB (@lem85745 m EXP' _2220 h1) (@lem85746)). Qed.
Lemma lem85749 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem85726 A B f y) (@lem85725 A B f y)). Qed.
Lemma lem85750 (f : nat -> nat) (y : nat) : (term14 f y) = (f y).
Proof. exact (@lem85749 nat nat f y). Qed.
Lemma lem85751 (_2220 : type1606) (m : nat) : (term15 _2220 m) = (term13 _2220 m).
Proof. exact (@lem85750 (term8 _2220 m) (NUMERAL 0)). Qed.
Lemma lem85752 (_2220 : type1606) (_2219 : nat) (m : nat) : (term16 _2220 m _2219) = (_2220 _2219 m).
Proof. exact (eq_refl (term16 _2220 m _2219)). Qed.
Lemma lem85753 (_2220 : type1606) (m : nat) : (term17 _2220 m) = (term8 _2220 m).
Proof. exact (fun_ext (fun _2219 : nat => @lem85752 _2220 _2219 m)). Qed.
Lemma lem85754 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem85755 (_2220 : type1606) (m : nat) : (term15 _2220 m) = (term13 _2220 m).
Proof. exact (MK_COMB (@lem85753 _2220 m) (@lem85754)). Qed.
Lemma lem85756 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem85757 (_2220 : type1606) (m : nat) : (term18 _2220 m) = (term19 _2220 m).
Proof. exact (MK_COMB (@lem85756) (@lem85755 _2220 m)). Qed.
Lemma lem85758 (_2220 : type1606) (m : nat) : (term13 _2220 m) = (term20 _2220 m).
Proof. exact (eq_refl (term13 _2220 m)). Qed.
Lemma lem85759 (_2220 : type1606) (m : nat) : ((term15 _2220 m) = (term13 _2220 m)) = ((term13 _2220 m) = (term20 _2220 m)).
Proof. exact (MK_COMB (@lem85757 _2220 m) (@lem85758 _2220 m)). Qed.
Lemma lem85760 (_2220 : type1606) (m : nat) : (term13 _2220 m) = (term20 _2220 m).
Proof. exact (EQ_MP (@lem85759 _2220 m) (@lem85751 _2220 m)). Qed.
Lemma lem85761 (m : nat) (EXP' : type1606) (_2220 : type1606) (h1 : EXP' = (term4 _2220)) : (term12 EXP' m) = (term20 _2220 m).
Proof. exact (TRANS (@lem85747 m EXP' _2220 h1) (@lem85760 _2220 m)). Qed.
Lemma lem85762 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem85763 (m : nat) (EXP' : type1606) (_2220 : type1606) (h1 : EXP' = (term4 _2220)) : (term21 EXP' m) = (term22 _2220 m).
Proof. exact (MK_COMB (@lem85762) (@lem85761 m EXP' _2220 h1)). Qed.
Lemma lem85764 : term23 = term23.
Proof. exact (eq_refl term23). Qed.
Lemma lem85765 (m : nat) (EXP' : type1606) (_2220 : type1606) (h1 : EXP' = (term4 _2220)) : ((term12 EXP' m) = term23) = ((term20 _2220 m) = term23).
Proof. exact (MK_COMB (@lem85763 m EXP' _2220 h1) (@lem85764)). Qed.
Lemma lem85766 (EXP' : type1606) (_2220 : type1606) (h1 : EXP' = (term4 _2220)) : (term24 EXP') = (term25 _2220).
Proof. exact (fun_ext (fun m : nat => @lem85765 m EXP' _2220 h1)). Qed.
Lemma lem85767 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem85768 (EXP' : type1606) (_2220 : type1606) (h1 : EXP' = (term4 _2220)) : (term26 EXP') = (term27 _2220).
Proof. exact (MK_COMB (@lem85767) (@lem85766 EXP' _2220 h1)). Qed.
Lemma lem85769 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem85770 (EXP' : type1606) (_2220 : type1606) (h1 : EXP' = (term4 _2220)) : (term28 EXP') = (term29 _2220).
Proof. exact (MK_COMB (@lem85769) (@lem85768 EXP' _2220 h1)). Qed.
Lemma lem85772 (EXP' : type1606) (_2220 : type1606) (h1 : EXP' = (term4 _2220)) : EXP' = (term4 _2220).
Proof. exact (h1). Qed.
Lemma lem85773 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem85774 (m : nat) (EXP' : type1606) (_2220 : type1606) (h1 : EXP' = (term4 _2220)) : (EXP' m) = (term5 _2220 m).
Proof. exact (MK_COMB (@lem85772 EXP' _2220 h1) (@lem85773 m)). Qed.
Lemma lem85776 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem85726 A B f y) (@lem85725 A B f y)). Qed.
Lemma lem85777 (f : type1606) (y : nat) : (term6 f y) = (f y).
Proof. exact (@lem85776 nat (nat -> nat) f y). Qed.
Lemma lem85778 (_2220 : type1606) (m : nat) : (term7 _2220 m) = (term5 _2220 m).
Proof. exact (@lem85777 (term4 _2220) m). Qed.
Lemma lem85779 (_2220 : type1606) (_2218 : nat) : (term5 _2220 _2218) = (term8 _2220 _2218).
Proof. exact (eq_refl (term5 _2220 _2218)). Qed.
Lemma lem85780 (_2220 : type1606) : (term9 _2220) = (term4 _2220).
Proof. exact (fun_ext (fun _2218 : nat => @lem85779 _2220 _2218)). Qed.
Lemma lem85781 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem85782 (_2220 : type1606) (m : nat) : (term7 _2220 m) = (term5 _2220 m).
Proof. exact (MK_COMB (@lem85780 _2220) (@lem85781 m)). Qed.
Lemma lem85783 : (@eq (nat -> nat)) = (@eq (nat -> nat)).
Proof. exact (eq_refl (@eq (nat -> nat))). Qed.
Lemma lem85784 (_2220 : type1606) (m : nat) : (term10 _2220 m) = (term11 _2220 m).
Proof. exact (MK_COMB (@lem85783) (@lem85782 _2220 m)). Qed.
Lemma lem85785 (_2220 : type1606) (m : nat) : (term5 _2220 m) = (term8 _2220 m).
Proof. exact (eq_refl (term5 _2220 m)). Qed.
Lemma lem85786 (_2220 : type1606) (m : nat) : ((term7 _2220 m) = (term5 _2220 m)) = ((term5 _2220 m) = (term8 _2220 m)).
Proof. exact (MK_COMB (@lem85784 _2220 m) (@lem85785 _2220 m)). Qed.
Lemma lem85787 (_2220 : type1606) (m : nat) : (term5 _2220 m) = (term8 _2220 m).
Proof. exact (EQ_MP (@lem85786 _2220 m) (@lem85778 _2220 m)). Qed.
Lemma lem85788 (m : nat) (EXP' : type1606) (_2220 : type1606) (h1 : EXP' = (term4 _2220)) : (EXP' m) = (term8 _2220 m).
Proof. exact (TRANS (@lem85774 m EXP' _2220 h1) (@lem85787 _2220 m)). Qed.
Lemma lem85789 (n : nat) : (S n) = (S n).
Proof. exact (eq_refl (S n)). Qed.
Lemma lem85790 (m : nat) (n : nat) (EXP' : type1606) (_2220 : type1606) (h1 : EXP' = (term4 _2220)) : (term30 EXP' m n) = (term31 _2220 m n).
Proof. exact (MK_COMB (@lem85788 m EXP' _2220 h1) (@lem85789 n)). Qed.
Lemma lem85792 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem85726 A B f y) (@lem85725 A B f y)). Qed.
Lemma lem85793 (f : nat -> nat) (y : nat) : (term14 f y) = (f y).
Proof. exact (@lem85792 nat nat f y). Qed.
Lemma lem85794 (_2220 : type1606) (m : nat) (n : nat) : (term32 _2220 m n) = (term31 _2220 m n).
Proof. exact (@lem85793 (term8 _2220 m) (S n)). Qed.
Lemma lem85795 (_2220 : type1606) (_2219 : nat) (m : nat) : (term16 _2220 m _2219) = (_2220 _2219 m).
Proof. exact (eq_refl (term16 _2220 m _2219)). Qed.
Lemma lem85796 (_2220 : type1606) (m : nat) : (term17 _2220 m) = (term8 _2220 m).
Proof. exact (fun_ext (fun _2219 : nat => @lem85795 _2220 _2219 m)). Qed.
Lemma lem85797 (n : nat) : (S n) = (S n).
Proof. exact (eq_refl (S n)). Qed.
Lemma lem85798 (_2220 : type1606) (m : nat) (n : nat) : (term32 _2220 m n) = (term31 _2220 m n).
Proof. exact (MK_COMB (@lem85796 _2220 m) (@lem85797 n)). Qed.
Lemma lem85799 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem85800 (_2220 : type1606) (m : nat) (n : nat) : (term33 _2220 m n) = (term34 _2220 m n).
Proof. exact (MK_COMB (@lem85799) (@lem85798 _2220 m n)). Qed.
Lemma lem85801 (_2220 : type1606) (n : nat) (m : nat) : (term31 _2220 m n) = (term35 _2220 n m).
Proof. exact (eq_refl (term31 _2220 m n)). Qed.
Lemma lem85802 (_2220 : type1606) (n : nat) (m : nat) : ((term32 _2220 m n) = (term31 _2220 m n)) = ((term31 _2220 m n) = (term35 _2220 n m)).
Proof. exact (MK_COMB (@lem85800 _2220 m n) (@lem85801 _2220 n m)). Qed.
Lemma lem85803 (_2220 : type1606) (n : nat) (m : nat) : (term31 _2220 m n) = (term35 _2220 n m).
Proof. exact (EQ_MP (@lem85802 _2220 n m) (@lem85794 _2220 m n)). Qed.
Lemma lem85804 (n : nat) (m : nat) (EXP' : type1606) (_2220 : type1606) (h1 : EXP' = (term4 _2220)) : (term30 EXP' m n) = (term35 _2220 n m).
Proof. exact (TRANS (@lem85790 m n EXP' _2220 h1) (@lem85803 _2220 n m)). Qed.
Lemma lem85805 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem85806 (n : nat) (m : nat) (EXP' : type1606) (_2220 : type1606) (h1 : EXP' = (term4 _2220)) : (term36 EXP' m n) = (term37 _2220 n m).
Proof. exact (MK_COMB (@lem85805) (@lem85804 n m EXP' _2220 h1)). Qed.
Lemma lem85808 (EXP' : type1606) (_2220 : type1606) (h1 : EXP' = (term4 _2220)) : EXP' = (term4 _2220).
Proof. exact (h1). Qed.
Lemma lem85809 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem85810 (m : nat) (EXP' : type1606) (_2220 : type1606) (h1 : EXP' = (term4 _2220)) : (EXP' m) = (term5 _2220 m).
Proof. exact (MK_COMB (@lem85808 EXP' _2220 h1) (@lem85809 m)). Qed.
Lemma lem85812 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem85726 A B f y) (@lem85725 A B f y)). Qed.
Lemma lem85813 (f : type1606) (y : nat) : (term6 f y) = (f y).
Proof. exact (@lem85812 nat (nat -> nat) f y). Qed.
Lemma lem85814 (_2220 : type1606) (m : nat) : (term7 _2220 m) = (term5 _2220 m).
Proof. exact (@lem85813 (term4 _2220) m). Qed.
Lemma lem85815 (_2220 : type1606) (_2218 : nat) : (term5 _2220 _2218) = (term8 _2220 _2218).
Proof. exact (eq_refl (term5 _2220 _2218)). Qed.
Lemma lem85816 (_2220 : type1606) : (term9 _2220) = (term4 _2220).
Proof. exact (fun_ext (fun _2218 : nat => @lem85815 _2220 _2218)). Qed.
Lemma lem85817 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem85818 (_2220 : type1606) (m : nat) : (term7 _2220 m) = (term5 _2220 m).
Proof. exact (MK_COMB (@lem85816 _2220) (@lem85817 m)). Qed.
Lemma lem85819 : (@eq (nat -> nat)) = (@eq (nat -> nat)).
Proof. exact (eq_refl (@eq (nat -> nat))). Qed.
Lemma lem85820 (_2220 : type1606) (m : nat) : (term10 _2220 m) = (term11 _2220 m).
Proof. exact (MK_COMB (@lem85819) (@lem85818 _2220 m)). Qed.
Lemma lem85821 (_2220 : type1606) (m : nat) : (term5 _2220 m) = (term8 _2220 m).
Proof. exact (eq_refl (term5 _2220 m)). Qed.
Lemma lem85822 (_2220 : type1606) (m : nat) : ((term7 _2220 m) = (term5 _2220 m)) = ((term5 _2220 m) = (term8 _2220 m)).
Proof. exact (MK_COMB (@lem85820 _2220 m) (@lem85821 _2220 m)). Qed.
Lemma lem85823 (_2220 : type1606) (m : nat) : (term5 _2220 m) = (term8 _2220 m).
Proof. exact (EQ_MP (@lem85822 _2220 m) (@lem85814 _2220 m)). Qed.
Lemma lem85824 (m : nat) (EXP' : type1606) (_2220 : type1606) (h1 : EXP' = (term4 _2220)) : (EXP' m) = (term8 _2220 m).
Proof. exact (TRANS (@lem85810 m EXP' _2220 h1) (@lem85823 _2220 m)). Qed.
Lemma lem85825 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem85826 (m : nat) (n : nat) (EXP' : type1606) (_2220 : type1606) (h1 : EXP' = (term4 _2220)) : (EXP' m n) = (term16 _2220 m n).
Proof. exact (MK_COMB (@lem85824 m EXP' _2220 h1) (@lem85825 n)). Qed.
Lemma lem85828 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem85726 A B f y) (@lem85725 A B f y)). Qed.
Lemma lem85829 (f : nat -> nat) (y : nat) : (term14 f y) = (f y).
Proof. exact (@lem85828 nat nat f y). Qed.
Lemma lem85830 (_2220 : type1606) (m : nat) (n : nat) : (term38 _2220 m n) = (term16 _2220 m n).
Proof. exact (@lem85829 (term8 _2220 m) n). Qed.
Lemma lem85831 (_2220 : type1606) (_2219 : nat) (m : nat) : (term16 _2220 m _2219) = (_2220 _2219 m).
Proof. exact (eq_refl (term16 _2220 m _2219)). Qed.
Lemma lem85832 (_2220 : type1606) (m : nat) : (term17 _2220 m) = (term8 _2220 m).
Proof. exact (fun_ext (fun _2219 : nat => @lem85831 _2220 _2219 m)). Qed.
Lemma lem85833 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem85834 (_2220 : type1606) (m : nat) (n : nat) : (term38 _2220 m n) = (term16 _2220 m n).
Proof. exact (MK_COMB (@lem85832 _2220 m) (@lem85833 n)). Qed.
Lemma lem85835 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem85836 (_2220 : type1606) (m : nat) (n : nat) : (term39 _2220 m n) = (term40 _2220 m n).
Proof. exact (MK_COMB (@lem85835) (@lem85834 _2220 m n)). Qed.
Lemma lem85837 (_2220 : type1606) (n : nat) (m : nat) : (term16 _2220 m n) = (_2220 n m).
Proof. exact (eq_refl (term16 _2220 m n)). Qed.
Lemma lem85838 (_2220 : type1606) (n : nat) (m : nat) : ((term38 _2220 m n) = (term16 _2220 m n)) = ((term16 _2220 m n) = (_2220 n m)).
Proof. exact (MK_COMB (@lem85836 _2220 m n) (@lem85837 _2220 n m)). Qed.
Lemma lem85839 (_2220 : type1606) (n : nat) (m : nat) : (term16 _2220 m n) = (_2220 n m).
Proof. exact (EQ_MP (@lem85838 _2220 n m) (@lem85830 _2220 m n)). Qed.
Lemma lem85840 (n : nat) (m : nat) (EXP' : type1606) (_2220 : type1606) (h1 : EXP' = (term4 _2220)) : (EXP' m n) = (_2220 n m).
Proof. exact (TRANS (@lem85826 m n EXP' _2220 h1) (@lem85839 _2220 n m)). Qed.
Lemma lem85841 (m : nat) : (Nat.mul m) = (Nat.mul m).
Proof. exact (eq_refl (Nat.mul m)). Qed.
Lemma lem85842 (n : nat) (m : nat) (EXP' : type1606) (_2220 : type1606) (h1 : EXP' = (term4 _2220)) : (term41 EXP' m n) = (term42 _2220 n m).
Proof. exact (MK_COMB (@lem85841 m) (@lem85840 n m EXP' _2220 h1)). Qed.
Lemma lem85843 (n : nat) (m : nat) (EXP' : type1606) (_2220 : type1606) (h1 : EXP' = (term4 _2220)) : ((term30 EXP' m n) = (term41 EXP' m n)) = ((term35 _2220 n m) = (term42 _2220 n m)).
Proof. exact (MK_COMB (@lem85806 n m EXP' _2220 h1) (@lem85842 n m EXP' _2220 h1)). Qed.
Lemma lem85844 (m : nat) (EXP' : type1606) (_2220 : type1606) (h1 : EXP' = (term4 _2220)) : (term43 EXP' m) = (term44 _2220 m).
Proof. exact (fun_ext (fun n : nat => @lem85843 n m EXP' _2220 h1)). Qed.
Lemma lem85845 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem85846 (m : nat) (EXP' : type1606) (_2220 : type1606) (h1 : EXP' = (term4 _2220)) : (term45 EXP' m) = (term46 _2220 m).
Proof. exact (MK_COMB (@lem85845) (@lem85844 m EXP' _2220 h1)). Qed.
Lemma lem85847 (EXP' : type1606) (_2220 : type1606) (h1 : EXP' = (term4 _2220)) : (term47 EXP') = (term48 _2220).
Proof. exact (fun_ext (fun m : nat => @lem85846 m EXP' _2220 h1)). Qed.
Lemma lem85848 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem85849 (EXP' : type1606) (_2220 : type1606) (h1 : EXP' = (term4 _2220)) : (term49 EXP') = (term50 _2220).
Proof. exact (MK_COMB (@lem85848) (@lem85847 EXP' _2220 h1)). Qed.
Lemma lem85850 (EXP' : type1606) (_2220 : type1606) (h1 : EXP' = (term4 _2220)) : (term51 EXP') = (term52 _2220).
Proof. exact (MK_COMB (@lem85770 EXP' _2220 h1) (@lem85849 EXP' _2220 h1)). Qed.
Lemma lem85851 (_2220 : type1606) (h1 : (term53 _2220) = term54) : (term53 _2220) = term54.
Proof. exact (h1). Qed.
Lemma lem85852 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem85853 (m : nat) (_2220 : type1606) (h1 : (term53 _2220) = term54) : (term20 _2220 m) = (term55 m).
Proof. exact (MK_COMB (@lem85851 _2220 h1) (@lem85852 m)). Qed.
Lemma lem85854 (m : nat) : (term55 m) = term23.
Proof. exact (eq_refl (term55 m)). Qed.
Lemma lem85855 (_2220 : type1606) (m : nat) : (term22 _2220 m) = (term22 _2220 m).
Proof. exact (eq_refl (term22 _2220 m)). Qed.
Lemma lem85856 (_2220 : type1606) (m : nat) : ((term20 _2220 m) = (term55 m)) = ((term20 _2220 m) = term23).
Proof. exact (MK_COMB (@lem85855 _2220 m) (@lem85854 m)). Qed.
Lemma lem85857 (m : nat) (_2220 : type1606) (h1 : (term53 _2220) = term54) : (term20 _2220 m) = term23.
Proof. exact (EQ_MP (@lem85856 _2220 m) (@lem85853 m _2220 h1)). Qed.
Lemma lem85858 (_2220 : type1606) (h1 : (term53 _2220) = term54) : term27 _2220.
Proof. exact (fun m : nat => @lem85857 m _2220 h1). Qed.
Lemma lem85859 (_2220 : type1606) (h1 : term56 _2220) : term56 _2220.
Proof. exact (h1). Qed.
Lemma lem85860 (n : nat) (_2220 : type1606) (h1 : term56 _2220) : term57 _2220 n.
Proof. exact (@lem85859 _2220 h1 n). Qed.
Lemma lem85861 (_2220 : type1606) (n : nat) : (term57 _2220 n) = ((term58 _2220 n) = (term59 _2220 n)).
Proof. exact (eq_refl (term57 _2220 n)). Qed.
Lemma lem85862 (n : nat) (_2220 : type1606) (h1 : term56 _2220) : (term58 _2220 n) = (term59 _2220 n).
Proof. exact (EQ_MP (@lem85861 _2220 n) (@lem85860 n _2220 h1)). Qed.
Lemma lem85863 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem85864 (n : nat) (m : nat) (_2220 : type1606) (h1 : term56 _2220) : (term35 _2220 n m) = (term60 _2220 n m).
Proof. exact (MK_COMB (@lem85862 n _2220 h1) (@lem85863 m)). Qed.
Lemma lem85865 (_2220 : type1606) (n : nat) (m : nat) : (term60 _2220 n m) = (term42 _2220 n m).
Proof. exact (eq_refl (term60 _2220 n m)). Qed.
Lemma lem85866 (_2220 : type1606) (n : nat) (m : nat) : (term37 _2220 n m) = (term37 _2220 n m).
Proof. exact (eq_refl (term37 _2220 n m)). Qed.
Lemma lem85867 (_2220 : type1606) (n : nat) (m : nat) : ((term35 _2220 n m) = (term60 _2220 n m)) = ((term35 _2220 n m) = (term42 _2220 n m)).
Proof. exact (MK_COMB (@lem85866 _2220 n m) (@lem85865 _2220 n m)). Qed.
Lemma lem85868 (n : nat) (m : nat) (_2220 : type1606) (h1 : term56 _2220) : (term35 _2220 n m) = (term42 _2220 n m).
Proof. exact (EQ_MP (@lem85867 _2220 n m) (@lem85864 n m _2220 h1)). Qed.
Lemma lem85869 (m : nat) (_2220 : type1606) (h1 : term56 _2220) : term46 _2220 m.
Proof. exact (fun n : nat => @lem85868 n m _2220 h1). Qed.
Lemma lem85870 (_2220 : type1606) (h1 : term56 _2220) : term50 _2220.
Proof. exact (fun m : nat => @lem85869 m _2220 h1). Qed.
Lemma lem85871 (_2220 : type1606) (h1 : term61 _2220) : term61 _2220.
Proof. exact (h1). Qed.
Lemma lem85872 (_2220 : type1606) (h1 : term61 _2220) : term56 _2220.
Proof. exact (proj2 (@lem85871 _2220 h1)). Qed.
Lemma lem85873 (_2220 : type1606) (h1 : term61 _2220) : (term53 _2220) = term54.
Proof. exact (proj1 (@lem85871 _2220 h1)). Qed.
Lemma lem85874 (_2220 : type1606) (h1 : term61 _2220) : ((term53 _2220) = term54) = (term27 _2220).
Proof. exact (prop_ext (fun h2 : (term53 _2220) = term54 => @lem85858 _2220 h2) (fun h2 : term27 _2220 => @lem85873 _2220 h1)). Qed.
Lemma lem85875 (_2220 : type1606) (h1 : term61 _2220) : term27 _2220.
Proof. exact (EQ_MP (@lem85874 _2220 h1) (@lem85873 _2220 h1)). Qed.
Lemma lem85876 (_2220 : type1606) (h1 : term61 _2220) : (term56 _2220) = (term50 _2220).
Proof. exact (prop_ext (fun h2 : term56 _2220 => @lem85870 _2220 h2) (fun h2 : term50 _2220 => @lem85872 _2220 h1)). Qed.
Lemma lem85877 (_2220 : type1606) (h1 : term61 _2220) : term50 _2220.
Proof. exact (EQ_MP (@lem85876 _2220 h1) (@lem85872 _2220 h1)). Qed.
Lemma lem85878 (_2220 : type1606) (h1 : term61 _2220) : term52 _2220.
Proof. exact (conj (@lem85875 _2220 h1) (@lem85877 _2220 h1)). Qed.
Lemma lem85879 {A : Type'} (e : A) : term62 A e.
Proof. exact (@lem75635 A e). Qed.
Lemma lem85880 {A : Type'} (e : A) : (term62 A e) = (term63 A e).
Proof. exact (eq_refl (term62 A e)). Qed.
Lemma lem85881 {A : Type'} (e : A) : term63 A e.
Proof. exact (EQ_MP (@lem85880 A e) (@lem85879 A e)). Qed.
Lemma lem85882 {A : Type'} (e : A) (f : type1423 A) : term64 A e f.
Proof. exact (@lem85881 A e f). Qed.
Lemma lem85883 {A : Type'} (e : A) (f : type1423 A) : (term64 A e f) = (term65 A e f).
Proof. exact (eq_refl (term64 A e f)). Qed.
Lemma lem85884 {A : Type'} (e : A) (f : type1423 A) : term65 A e f.
Proof. exact (EQ_MP (@lem85883 A e f) (@lem85882 A e f)). Qed.
Lemma lem85885 (e : nat -> nat) (f : type1000) : term66 e f.
Proof. exact (@lem85884 (nat -> nat) e f). Qed.
Lemma lem85886 : term67.
Proof. exact (@lem85885 term54 term68). Qed.
Lemma lem85887 (fn : type1606) (n : nat) : (term69 fn n) = (term70 fn n).
Proof. exact (eq_refl (term69 fn n)). Qed.
Lemma lem85888 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem85889 (fn : type1606) (n : nat) : (term71 fn n) = (term72 fn n).
Proof. exact (MK_COMB (@lem85887 fn n) (@lem85888 n)). Qed.
Lemma lem85890 (fn : type1606) (n : nat) : (term72 fn n) = (term59 fn n).
Proof. exact (eq_refl (term72 fn n)). Qed.
Lemma lem85891 (fn : type1606) (n : nat) : (term71 fn n) = (term59 fn n).
Proof. exact (TRANS (@lem85889 fn n) (@lem85890 fn n)). Qed.
Lemma lem85892 (fn : type1606) (n : nat) : (term73 fn n) = (term73 fn n).
Proof. exact (eq_refl (term73 fn n)). Qed.
Lemma lem85893 (fn : type1606) (n : nat) : ((term58 fn n) = (term71 fn n)) = ((term58 fn n) = (term59 fn n)).
Proof. exact (MK_COMB (@lem85892 fn n) (@lem85891 fn n)). Qed.
Lemma lem85894 (fn : type1606) : (term74 fn) = (term75 fn).
Proof. exact (fun_ext (fun n : nat => @lem85893 fn n)). Qed.
Lemma lem85895 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem85896 (fn : type1606) : (term76 fn) = (term56 fn).
Proof. exact (MK_COMB (@lem85895) (@lem85894 fn)). Qed.
Lemma lem85897 (fn : type1606) : (term77 fn) = (term77 fn).
Proof. exact (eq_refl (term77 fn)). Qed.
Lemma lem85898 (fn : type1606) : (term78 fn) = (term61 fn).
Proof. exact (MK_COMB (@lem85897 fn) (@lem85896 fn)). Qed.
Lemma lem85899 : term79 = term80.
Proof. exact (fun_ext (fun fn : type1606 => @lem85898 fn)). Qed.
Lemma lem85900 : (@ex (nat -> nat -> nat)) = (@ex (nat -> nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat -> nat))). Qed.
Lemma lem85901 : term67 = term81.
Proof. exact (MK_COMB (@lem85900) (@lem85899)). Qed.
Lemma lem85902 : term81.
Proof. exact (EQ_MP (@lem85901) (@lem85886)). Qed.
Lemma lem85903 (_2220 : type1606) (h1 : term61 _2220) : term61 _2220.
Proof. exact (h1). Qed.
Lemma lem85904 (_2220 : type1606) (h1 : term61 _2220) : term56 _2220.
Proof. exact (proj2 (@lem85903 _2220 h1)). Qed.
Lemma lem85905 (_2220 : type1606) (h1 : term61 _2220) : (term53 _2220) = term54.
Proof. exact (proj1 (@lem85903 _2220 h1)). Qed.
Lemma lem85906 (_2220 : type1606) (h1 : term61 _2220) : term61 _2220.
Proof. exact (conj (@lem85905 _2220 h1) (@lem85904 _2220 h1)). Qed.
Lemma lem85907 (_2220 : type1606) (h1 : term61 _2220) : term81.
Proof. exact (ex_intro term80 _2220 (@lem85906 _2220 h1)). Qed.
Lemma lem85908 (h1 : term81) : term81.
Proof. exact (h1). Qed.
Lemma lem85909 (h1 : term81) : term81.
Proof. exact (ex_elim (@lem85908 h1) (fun _2220 : type1606 => fun h0 : term80 _2220 => @lem85907 _2220 h0)). Qed.
Lemma lem85910 : term81 = term81.
Proof. exact (prop_ext (fun h1 : term81 => @lem85909 h1) (fun h1 : term81 => @lem85902)). Qed.
Lemma lem85911 : term81.
Proof. exact (EQ_MP (@lem85910) (@lem85902)). Qed.
Lemma lem85912 (_2220 : type1606) (h1 : term61 _2220) : term82.
Proof. exact (ex_intro term83 _2220 (@lem85878 _2220 h1)). Qed.
Lemma lem85913 (h1 : term81) : term81.
Proof. exact (h1). Qed.
Lemma lem85914 (h1 : term81) : term82.
Proof. exact (ex_elim (@lem85913 h1) (fun _2220 : type1606 => fun h0 : term80 _2220 => @lem85912 _2220 h0)). Qed.
Lemma lem85915 : term81 = term82.
Proof. exact (prop_ext (fun h1 : term81 => @lem85914 h1) (fun h1 : term82 => @lem85911)). Qed.
Lemma lem85916 : term82.
Proof. exact (EQ_MP (@lem85915) (@lem85911)). Qed.
Lemma lem85917 (_2220 : type1606) (h1 : term52 _2220) : term52 _2220.
Proof. exact (h1). Qed.
Lemma lem85918 (EXP' : type1606) (_2220 : type1606) (h1 : EXP' = (term4 _2220)) : (term52 _2220) = (term51 EXP').
Proof. exact (SYM (@lem85850 EXP' _2220 h1)). Qed.
Lemma lem85919 (EXP' : type1606) (_2220 : type1606) (h1 : term52 _2220) (h2 : EXP' = (term4 _2220)) : term51 EXP'.
Proof. exact (EQ_MP (@lem85918 EXP' _2220 h2) (@lem85917 _2220 h1)). Qed.
Lemma lem85920 (EXP' : type1606) (_2220 : type1606) (h1 : term52 _2220) (h2 : EXP' = (term4 _2220)) : term84.
Proof. exact (ex_intro term85 EXP' (@lem85919 EXP' _2220 h1 h2)). Qed.
Lemma lem85921 (_2220 : type1606) : (term4 _2220) = (term4 _2220).
Proof. exact (eq_refl (term4 _2220)). Qed.
Lemma lem85922 (EXP' : type1606) (_2220 : type1606) (h1 : term52 _2220) : term86 EXP' _2220.
Proof. exact (fun h0 : EXP' = (term4 _2220) => @lem85920 EXP' _2220 h1 h0). Qed.
Lemma lem85923 (_2220 : type1606) (h1 : term52 _2220) : term87 _2220.
Proof. exact (@lem85922 (term4 _2220) _2220 h1). Qed.
Lemma lem85924 (_2220 : type1606) (h1 : term52 _2220) : term84.
Proof. exact (@lem85923 _2220 h1 (@lem85921 _2220)). Qed.
Lemma lem85925 (h1 : term82) : term82.
Proof. exact (h1). Qed.
Lemma lem85926 (h1 : term82) : term84.
Proof. exact (ex_elim (@lem85925 h1) (fun _2220 : type1606 => fun h0 : term83 _2220 => @lem85924 _2220 h0)). Qed.
Lemma lem85927 : term82 = term84.
Proof. exact (prop_ext (fun h1 : term82 => @lem85926 h1) (fun h1 : term84 => @lem85916)). Qed.
Lemma lem85928 : term84.
Proof. exact (EQ_MP (@lem85927) (@lem85916)). Qed.
Lemma lem85929 : term88.
Proof. exact (fun _2224 : type1674 => @lem85928). Qed.
Lemma lem85930 {A B : Type'} (P : type1413 A B) : term89 A B P.
Proof. exact (@lem13546 A B P). Qed.
Lemma lem85931 {A B : Type'} (P : type1413 A B) : (term89 A B P) = ((term90 A B P) = (term91 A B P)).
Proof. exact (eq_refl (term89 A B P)). Qed.
Lemma lem85934 {A B : Type'} (P : type1413 A B) : (term90 A B P) = (term91 A B P).
Proof. exact (EQ_MP (@lem85931 A B P) (@lem85930 A B P)). Qed.
Lemma lem85935 (P : type1300) : (term92 P) = (term93 P).
Proof. exact (@lem85934 type1674 type1606 P). Qed.
Lemma lem85936 : term94 = term95.
Proof. exact (@lem85935 term96). Qed.
Lemma lem85937 (_2224 : type1674) : (term97 _2224) = term85.
Proof. exact (eq_refl (term97 _2224)). Qed.
Lemma lem85938 (EXP' : type1606) : EXP' = EXP'.
Proof. exact (eq_refl EXP'). Qed.
Lemma lem85939 (_2224 : type1674) (EXP' : type1606) : (term98 _2224 EXP') = (term99 EXP').
Proof. exact (MK_COMB (@lem85937 _2224) (@lem85938 EXP')). Qed.
Lemma lem85940 (EXP' : type1606) : (term99 EXP') = (term51 EXP').
Proof. exact (eq_refl (term99 EXP')). Qed.
Lemma lem85941 (_2224 : type1674) (EXP' : type1606) : (term98 _2224 EXP') = (term51 EXP').
Proof. exact (TRANS (@lem85939 _2224 EXP') (@lem85940 EXP')). Qed.
Lemma lem85942 (_2224 : type1674) : (term100 _2224) = term85.
Proof. exact (fun_ext (fun EXP' : type1606 => @lem85941 _2224 EXP')). Qed.
Lemma lem85943 : (@ex (nat -> nat -> nat)) = (@ex (nat -> nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat -> nat))). Qed.
Lemma lem85944 (_2224 : type1674) : (term101 _2224) = term84.
Proof. exact (MK_COMB (@lem85943) (@lem85942 _2224)). Qed.
Lemma lem85945 : term102 = term103.
Proof. exact (fun_ext (fun _2224 : type1674 => @lem85944 _2224)). Qed.
Lemma lem85946 : (@all (prod nat (prod nat nat))) = (@all (prod nat (prod nat nat))).
Proof. exact (eq_refl (@all (prod nat (prod nat nat)))). Qed.
Lemma lem85947 : term94 = term88.
Proof. exact (MK_COMB (@lem85946) (@lem85945)). Qed.
Lemma lem85948 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem85949 : term104 = term105.
Proof. exact (MK_COMB (@lem85948) (@lem85947)). Qed.
Lemma lem85950 (_2224 : type1674) : (term97 _2224) = term85.
Proof. exact (eq_refl (term97 _2224)). Qed.
Lemma lem85951 (EXP' : type1306) (_2224 : type1674) : (EXP' _2224) = (EXP' _2224).
Proof. exact (eq_refl (EXP' _2224)). Qed.
Lemma lem85952 (EXP' : type1306) (_2224 : type1674) : (term106 EXP' _2224) = (term107 EXP' _2224).
Proof. exact (MK_COMB (@lem85950 _2224) (@lem85951 EXP' _2224)). Qed.
Lemma lem85953 (EXP' : type1306) (_2224 : type1674) : (term107 EXP' _2224) = (term108 EXP' _2224).
Proof. exact (eq_refl (term107 EXP' _2224)). Qed.
Lemma lem85954 (EXP' : type1306) (_2224 : type1674) : (term106 EXP' _2224) = (term108 EXP' _2224).
Proof. exact (TRANS (@lem85952 EXP' _2224) (@lem85953 EXP' _2224)). Qed.
Lemma lem85955 (EXP' : type1306) : (term109 EXP') = (term110 EXP').
Proof. exact (fun_ext (fun _2224 : type1674 => @lem85954 EXP' _2224)). Qed.
Lemma lem85956 : (@all (prod nat (prod nat nat))) = (@all (prod nat (prod nat nat))).
Proof. exact (eq_refl (@all (prod nat (prod nat nat)))). Qed.
Lemma lem85957 (EXP' : type1306) : (term111 EXP') = (term112 EXP').
Proof. exact (MK_COMB (@lem85956) (@lem85955 EXP')). Qed.
Lemma lem85958 : term113 = term114.
Proof. exact (fun_ext (fun EXP' : type1306 => @lem85957 EXP')). Qed.
Lemma lem85959 : (@ex ((prod nat (prod nat nat)) -> nat -> nat -> nat)) = (@ex ((prod nat (prod nat nat)) -> nat -> nat -> nat)).
Proof. exact (eq_refl (@ex ((prod nat (prod nat nat)) -> nat -> nat -> nat))). Qed.
Lemma lem85960 : term95 = term115.
Proof. exact (MK_COMB (@lem85959) (@lem85958)). Qed.
Lemma lem85961 : (term94 = term95) = (term88 = term115).
Proof. exact (MK_COMB (@lem85949) (@lem85960)). Qed.
Lemma lem85962 : term88 = term115.
Proof. exact (EQ_MP (@lem85961) (@lem85936)). Qed.
Lemma lem85963 : term115.
Proof. exact (EQ_MP (@lem85962) (@lem85929)). Qed.
Lemma lem85965 {A : Type'} : (@ex A) = (term116 A).
Proof. exact (@lem9261 A (@lem9306 A)). Qed.
Lemma lem85966 : (@ex ((prod nat (prod nat nat)) -> nat -> nat -> nat)) = term117.
Proof. exact (@lem85965 type1306). Qed.
Lemma lem85967 : term114 = term114.
Proof. exact (eq_refl term114). Qed.
Lemma lem85968 : term115 = term118.
Proof. exact (MK_COMB (@lem85966) (@lem85967)). Qed.
Lemma lem85969 : term118 = term119.
Proof. exact (eq_refl term118). Qed.
Lemma lem85970 : term115 = term119.
Proof. exact (TRANS (@lem85968) (@lem85969)). Qed.
Lemma lem85971 : term119.
Proof. exact (EQ_MP (@lem85970) (@lem85963)). Qed.
