Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1111009_term_abbrevs.
Require Import BETA_THM_spec.
Require Import SKOLEM_THM_spec.
Require Import thm75635_spec.
Require Import thm9261_spec.
Require Import thm9306_spec.
Lemma lem1110758 {A B : Type'} (f : A -> B) : term0 A B f.
Proof. exact (@lem421 A B f). Qed.
Lemma lem1110759 {A B : Type'} (f : A -> B) : (term0 A B f) = (term1 A B f).
Proof. exact (eq_refl (term0 A B f)). Qed.
Lemma lem1110760 {A B : Type'} (f : A -> B) : term1 A B f.
Proof. exact (EQ_MP (@lem1110759 A B f) (@lem1110758 A B f)). Qed.
Lemma lem1110761 {A B : Type'} (f : A -> B) (y : A) : term2 A B f y.
Proof. exact (@lem1110760 A B f y). Qed.
Lemma lem1110762 {A B : Type'} (f : A -> B) (y : A) : (term2 A B f y) = ((term3 A B f y) = (f y)).
Proof. exact (eq_refl (term2 A B f y)). Qed.
Lemma lem1110765 {A : Type'} (list_of_seq' : type971 A) (_18060 : type1582 A) (h1 : list_of_seq' = (term4 A _18060)) : list_of_seq' = (term4 A _18060).
Proof. exact (h1). Qed.
Lemma lem1110766 {A : Type'} (s : nat -> A) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem1110767 {A : Type'} (s : nat -> A) (list_of_seq' : type971 A) (_18060 : type1582 A) (h1 : list_of_seq' = (term4 A _18060)) : (list_of_seq' s) = (term5 A _18060 s).
Proof. exact (MK_COMB (@lem1110765 A list_of_seq' _18060 h1) (@lem1110766 A s)). Qed.
Lemma lem1110769 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1110762 A B f y) (@lem1110761 A B f y)). Qed.
Lemma lem1110770 {A : Type'} (f : type971 A) (y : nat -> A) : (term6 A f y) = (f y).
Proof. exact (@lem1110769 (nat -> A) (type1609 A) f y). Qed.
Lemma lem1110771 {A : Type'} (_18060 : type1582 A) (s : nat -> A) : (term7 A _18060 s) = (term5 A _18060 s).
Proof. exact (@lem1110770 A (term4 A _18060) s). Qed.
Lemma lem1110772 {A : Type'} (_18060 : type1582 A) (_18058 : nat -> A) : (term5 A _18060 _18058) = (term8 A _18060 _18058).
Proof. exact (eq_refl (term5 A _18060 _18058)). Qed.
Lemma lem1110773 {A : Type'} (_18060 : type1582 A) : (term9 A _18060) = (term4 A _18060).
Proof. exact (fun_ext (fun _18058 : nat -> A => @lem1110772 A _18060 _18058)). Qed.
Lemma lem1110774 {A : Type'} (s : nat -> A) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem1110775 {A : Type'} (_18060 : type1582 A) (s : nat -> A) : (term7 A _18060 s) = (term5 A _18060 s).
Proof. exact (MK_COMB (@lem1110773 A _18060) (@lem1110774 A s)). Qed.
Lemma lem1110776 {A : Type'} : (@eq (nat -> list A)) = (@eq (nat -> list A)).
Proof. exact (eq_refl (@eq (nat -> list A))). Qed.
Lemma lem1110777 {A : Type'} (_18060 : type1582 A) (s : nat -> A) : (term10 A _18060 s) = (term11 A _18060 s).
Proof. exact (MK_COMB (@lem1110776 A) (@lem1110775 A _18060 s)). Qed.
Lemma lem1110778 {A : Type'} (_18060 : type1582 A) (s : nat -> A) : (term5 A _18060 s) = (term8 A _18060 s).
Proof. exact (eq_refl (term5 A _18060 s)). Qed.
Lemma lem1110779 {A : Type'} (_18060 : type1582 A) (s : nat -> A) : ((term7 A _18060 s) = (term5 A _18060 s)) = ((term5 A _18060 s) = (term8 A _18060 s)).
Proof. exact (MK_COMB (@lem1110777 A _18060 s) (@lem1110778 A _18060 s)). Qed.
Lemma lem1110780 {A : Type'} (_18060 : type1582 A) (s : nat -> A) : (term5 A _18060 s) = (term8 A _18060 s).
Proof. exact (EQ_MP (@lem1110779 A _18060 s) (@lem1110771 A _18060 s)). Qed.
Lemma lem1110781 {A : Type'} (s : nat -> A) (list_of_seq' : type971 A) (_18060 : type1582 A) (h1 : list_of_seq' = (term4 A _18060)) : (list_of_seq' s) = (term8 A _18060 s).
Proof. exact (TRANS (@lem1110767 A s list_of_seq' _18060 h1) (@lem1110780 A _18060 s)). Qed.
Lemma lem1110782 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem1110783 {A : Type'} (s : nat -> A) (list_of_seq' : type971 A) (_18060 : type1582 A) (h1 : list_of_seq' = (term4 A _18060)) : (term12 A list_of_seq' s) = (term13 A _18060 s).
Proof. exact (MK_COMB (@lem1110781 A s list_of_seq' _18060 h1) (@lem1110782)). Qed.
Lemma lem1110785 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1110762 A B f y) (@lem1110761 A B f y)). Qed.
Lemma lem1110786 {A : Type'} (f : type1609 A) (y : nat) : (term14 A f y) = (f y).
Proof. exact (@lem1110785 nat (list A) f y). Qed.
Lemma lem1110787 {A : Type'} (_18060 : type1582 A) (s : nat -> A) : (term15 A _18060 s) = (term13 A _18060 s).
Proof. exact (@lem1110786 A (term8 A _18060 s) (NUMERAL 0)). Qed.
Lemma lem1110788 {A : Type'} (_18060 : type1582 A) (_18059 : nat) (s : nat -> A) : (term16 A _18060 s _18059) = (_18060 _18059 s).
Proof. exact (eq_refl (term16 A _18060 s _18059)). Qed.
Lemma lem1110789 {A : Type'} (_18060 : type1582 A) (s : nat -> A) : (term17 A _18060 s) = (term8 A _18060 s).
Proof. exact (fun_ext (fun _18059 : nat => @lem1110788 A _18060 _18059 s)). Qed.
Lemma lem1110790 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem1110791 {A : Type'} (_18060 : type1582 A) (s : nat -> A) : (term15 A _18060 s) = (term13 A _18060 s).
Proof. exact (MK_COMB (@lem1110789 A _18060 s) (@lem1110790)). Qed.
Lemma lem1110792 {A : Type'} : (@eq (list A)) = (@eq (list A)).
Proof. exact (eq_refl (@eq (list A))). Qed.
Lemma lem1110793 {A : Type'} (_18060 : type1582 A) (s : nat -> A) : (term18 A _18060 s) = (term19 A _18060 s).
Proof. exact (MK_COMB (@lem1110792 A) (@lem1110791 A _18060 s)). Qed.
Lemma lem1110794 {A : Type'} (_18060 : type1582 A) (s : nat -> A) : (term13 A _18060 s) = (term20 A _18060 s).
Proof. exact (eq_refl (term13 A _18060 s)). Qed.
Lemma lem1110795 {A : Type'} (_18060 : type1582 A) (s : nat -> A) : ((term15 A _18060 s) = (term13 A _18060 s)) = ((term13 A _18060 s) = (term20 A _18060 s)).
Proof. exact (MK_COMB (@lem1110793 A _18060 s) (@lem1110794 A _18060 s)). Qed.
Lemma lem1110796 {A : Type'} (_18060 : type1582 A) (s : nat -> A) : (term13 A _18060 s) = (term20 A _18060 s).
Proof. exact (EQ_MP (@lem1110795 A _18060 s) (@lem1110787 A _18060 s)). Qed.
Lemma lem1110797 {A : Type'} (s : nat -> A) (list_of_seq' : type971 A) (_18060 : type1582 A) (h1 : list_of_seq' = (term4 A _18060)) : (term12 A list_of_seq' s) = (term20 A _18060 s).
Proof. exact (TRANS (@lem1110783 A s list_of_seq' _18060 h1) (@lem1110796 A _18060 s)). Qed.
Lemma lem1110798 {A : Type'} : (@eq (list A)) = (@eq (list A)).
Proof. exact (eq_refl (@eq (list A))). Qed.
Lemma lem1110799 {A : Type'} (s : nat -> A) (list_of_seq' : type971 A) (_18060 : type1582 A) (h1 : list_of_seq' = (term4 A _18060)) : (term21 A list_of_seq' s) = (term22 A _18060 s).
Proof. exact (MK_COMB (@lem1110798 A) (@lem1110797 A s list_of_seq' _18060 h1)). Qed.
Lemma lem1110800 {A : Type'} : (@nil A) = (@nil A).
Proof. exact (eq_refl (@nil A)). Qed.
Lemma lem1110801 {A : Type'} (s : nat -> A) (list_of_seq' : type971 A) (_18060 : type1582 A) (h1 : list_of_seq' = (term4 A _18060)) : ((term12 A list_of_seq' s) = (@nil A)) = ((term20 A _18060 s) = (@nil A)).
Proof. exact (MK_COMB (@lem1110799 A s list_of_seq' _18060 h1) (@lem1110800 A)). Qed.
Lemma lem1110802 {A : Type'} (list_of_seq' : type971 A) (_18060 : type1582 A) (h1 : list_of_seq' = (term4 A _18060)) : (term23 A list_of_seq') = (term24 A _18060).
Proof. exact (fun_ext (fun s : nat -> A => @lem1110801 A s list_of_seq' _18060 h1)). Qed.
Lemma lem1110803 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem1110804 {A : Type'} (list_of_seq' : type971 A) (_18060 : type1582 A) (h1 : list_of_seq' = (term4 A _18060)) : (term25 A list_of_seq') = (term26 A _18060).
Proof. exact (MK_COMB (@lem1110803 A) (@lem1110802 A list_of_seq' _18060 h1)). Qed.
Lemma lem1110805 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1110806 {A : Type'} (list_of_seq' : type971 A) (_18060 : type1582 A) (h1 : list_of_seq' = (term4 A _18060)) : (term27 A list_of_seq') = (term28 A _18060).
Proof. exact (MK_COMB (@lem1110805) (@lem1110804 A list_of_seq' _18060 h1)). Qed.
Lemma lem1110808 {A : Type'} (list_of_seq' : type971 A) (_18060 : type1582 A) (h1 : list_of_seq' = (term4 A _18060)) : list_of_seq' = (term4 A _18060).
Proof. exact (h1). Qed.
Lemma lem1110809 {A : Type'} (s : nat -> A) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem1110810 {A : Type'} (s : nat -> A) (list_of_seq' : type971 A) (_18060 : type1582 A) (h1 : list_of_seq' = (term4 A _18060)) : (list_of_seq' s) = (term5 A _18060 s).
Proof. exact (MK_COMB (@lem1110808 A list_of_seq' _18060 h1) (@lem1110809 A s)). Qed.
Lemma lem1110812 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1110762 A B f y) (@lem1110761 A B f y)). Qed.
Lemma lem1110813 {A : Type'} (f : type971 A) (y : nat -> A) : (term6 A f y) = (f y).
Proof. exact (@lem1110812 (nat -> A) (type1609 A) f y). Qed.
Lemma lem1110814 {A : Type'} (_18060 : type1582 A) (s : nat -> A) : (term7 A _18060 s) = (term5 A _18060 s).
Proof. exact (@lem1110813 A (term4 A _18060) s). Qed.
Lemma lem1110815 {A : Type'} (_18060 : type1582 A) (_18058 : nat -> A) : (term5 A _18060 _18058) = (term8 A _18060 _18058).
Proof. exact (eq_refl (term5 A _18060 _18058)). Qed.
Lemma lem1110816 {A : Type'} (_18060 : type1582 A) : (term9 A _18060) = (term4 A _18060).
Proof. exact (fun_ext (fun _18058 : nat -> A => @lem1110815 A _18060 _18058)). Qed.
Lemma lem1110817 {A : Type'} (s : nat -> A) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem1110818 {A : Type'} (_18060 : type1582 A) (s : nat -> A) : (term7 A _18060 s) = (term5 A _18060 s).
Proof. exact (MK_COMB (@lem1110816 A _18060) (@lem1110817 A s)). Qed.
Lemma lem1110819 {A : Type'} : (@eq (nat -> list A)) = (@eq (nat -> list A)).
Proof. exact (eq_refl (@eq (nat -> list A))). Qed.
Lemma lem1110820 {A : Type'} (_18060 : type1582 A) (s : nat -> A) : (term10 A _18060 s) = (term11 A _18060 s).
Proof. exact (MK_COMB (@lem1110819 A) (@lem1110818 A _18060 s)). Qed.
Lemma lem1110821 {A : Type'} (_18060 : type1582 A) (s : nat -> A) : (term5 A _18060 s) = (term8 A _18060 s).
Proof. exact (eq_refl (term5 A _18060 s)). Qed.
Lemma lem1110822 {A : Type'} (_18060 : type1582 A) (s : nat -> A) : ((term7 A _18060 s) = (term5 A _18060 s)) = ((term5 A _18060 s) = (term8 A _18060 s)).
Proof. exact (MK_COMB (@lem1110820 A _18060 s) (@lem1110821 A _18060 s)). Qed.
Lemma lem1110823 {A : Type'} (_18060 : type1582 A) (s : nat -> A) : (term5 A _18060 s) = (term8 A _18060 s).
Proof. exact (EQ_MP (@lem1110822 A _18060 s) (@lem1110814 A _18060 s)). Qed.
Lemma lem1110824 {A : Type'} (s : nat -> A) (list_of_seq' : type971 A) (_18060 : type1582 A) (h1 : list_of_seq' = (term4 A _18060)) : (list_of_seq' s) = (term8 A _18060 s).
Proof. exact (TRANS (@lem1110810 A s list_of_seq' _18060 h1) (@lem1110823 A _18060 s)). Qed.
Lemma lem1110825 (n : nat) : (S n) = (S n).
Proof. exact (eq_refl (S n)). Qed.
Lemma lem1110826 {A : Type'} (s : nat -> A) (n : nat) (list_of_seq' : type971 A) (_18060 : type1582 A) (h1 : list_of_seq' = (term4 A _18060)) : (term29 A list_of_seq' s n) = (term30 A _18060 s n).
Proof. exact (MK_COMB (@lem1110824 A s list_of_seq' _18060 h1) (@lem1110825 n)). Qed.
Lemma lem1110828 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1110762 A B f y) (@lem1110761 A B f y)). Qed.
Lemma lem1110829 {A : Type'} (f : type1609 A) (y : nat) : (term14 A f y) = (f y).
Proof. exact (@lem1110828 nat (list A) f y). Qed.
Lemma lem1110830 {A : Type'} (_18060 : type1582 A) (s : nat -> A) (n : nat) : (term31 A _18060 s n) = (term30 A _18060 s n).
Proof. exact (@lem1110829 A (term8 A _18060 s) (S n)). Qed.
Lemma lem1110831 {A : Type'} (_18060 : type1582 A) (_18059 : nat) (s : nat -> A) : (term16 A _18060 s _18059) = (_18060 _18059 s).
Proof. exact (eq_refl (term16 A _18060 s _18059)). Qed.
Lemma lem1110832 {A : Type'} (_18060 : type1582 A) (s : nat -> A) : (term17 A _18060 s) = (term8 A _18060 s).
Proof. exact (fun_ext (fun _18059 : nat => @lem1110831 A _18060 _18059 s)). Qed.
Lemma lem1110833 (n : nat) : (S n) = (S n).
Proof. exact (eq_refl (S n)). Qed.
Lemma lem1110834 {A : Type'} (_18060 : type1582 A) (s : nat -> A) (n : nat) : (term31 A _18060 s n) = (term30 A _18060 s n).
Proof. exact (MK_COMB (@lem1110832 A _18060 s) (@lem1110833 n)). Qed.
Lemma lem1110835 {A : Type'} : (@eq (list A)) = (@eq (list A)).
Proof. exact (eq_refl (@eq (list A))). Qed.
Lemma lem1110836 {A : Type'} (_18060 : type1582 A) (s : nat -> A) (n : nat) : (term32 A _18060 s n) = (term33 A _18060 s n).
Proof. exact (MK_COMB (@lem1110835 A) (@lem1110834 A _18060 s n)). Qed.
Lemma lem1110837 {A : Type'} (_18060 : type1582 A) (n : nat) (s : nat -> A) : (term30 A _18060 s n) = (term34 A _18060 n s).
Proof. exact (eq_refl (term30 A _18060 s n)). Qed.
Lemma lem1110838 {A : Type'} (_18060 : type1582 A) (n : nat) (s : nat -> A) : ((term31 A _18060 s n) = (term30 A _18060 s n)) = ((term30 A _18060 s n) = (term34 A _18060 n s)).
Proof. exact (MK_COMB (@lem1110836 A _18060 s n) (@lem1110837 A _18060 n s)). Qed.
Lemma lem1110839 {A : Type'} (_18060 : type1582 A) (n : nat) (s : nat -> A) : (term30 A _18060 s n) = (term34 A _18060 n s).
Proof. exact (EQ_MP (@lem1110838 A _18060 n s) (@lem1110830 A _18060 s n)). Qed.
Lemma lem1110840 {A : Type'} (n : nat) (s : nat -> A) (list_of_seq' : type971 A) (_18060 : type1582 A) (h1 : list_of_seq' = (term4 A _18060)) : (term29 A list_of_seq' s n) = (term34 A _18060 n s).
Proof. exact (TRANS (@lem1110826 A s n list_of_seq' _18060 h1) (@lem1110839 A _18060 n s)). Qed.
Lemma lem1110841 {A : Type'} : (@eq (list A)) = (@eq (list A)).
Proof. exact (eq_refl (@eq (list A))). Qed.
Lemma lem1110842 {A : Type'} (n : nat) (s : nat -> A) (list_of_seq' : type971 A) (_18060 : type1582 A) (h1 : list_of_seq' = (term4 A _18060)) : (term35 A list_of_seq' s n) = (term36 A _18060 n s).
Proof. exact (MK_COMB (@lem1110841 A) (@lem1110840 A n s list_of_seq' _18060 h1)). Qed.
Lemma lem1110844 {A : Type'} (list_of_seq' : type971 A) (_18060 : type1582 A) (h1 : list_of_seq' = (term4 A _18060)) : list_of_seq' = (term4 A _18060).
Proof. exact (h1). Qed.
Lemma lem1110845 {A : Type'} (s : nat -> A) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem1110846 {A : Type'} (s : nat -> A) (list_of_seq' : type971 A) (_18060 : type1582 A) (h1 : list_of_seq' = (term4 A _18060)) : (list_of_seq' s) = (term5 A _18060 s).
Proof. exact (MK_COMB (@lem1110844 A list_of_seq' _18060 h1) (@lem1110845 A s)). Qed.
Lemma lem1110848 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1110762 A B f y) (@lem1110761 A B f y)). Qed.
Lemma lem1110849 {A : Type'} (f : type971 A) (y : nat -> A) : (term6 A f y) = (f y).
Proof. exact (@lem1110848 (nat -> A) (type1609 A) f y). Qed.
Lemma lem1110850 {A : Type'} (_18060 : type1582 A) (s : nat -> A) : (term7 A _18060 s) = (term5 A _18060 s).
Proof. exact (@lem1110849 A (term4 A _18060) s). Qed.
Lemma lem1110851 {A : Type'} (_18060 : type1582 A) (_18058 : nat -> A) : (term5 A _18060 _18058) = (term8 A _18060 _18058).
Proof. exact (eq_refl (term5 A _18060 _18058)). Qed.
Lemma lem1110852 {A : Type'} (_18060 : type1582 A) : (term9 A _18060) = (term4 A _18060).
Proof. exact (fun_ext (fun _18058 : nat -> A => @lem1110851 A _18060 _18058)). Qed.
Lemma lem1110853 {A : Type'} (s : nat -> A) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem1110854 {A : Type'} (_18060 : type1582 A) (s : nat -> A) : (term7 A _18060 s) = (term5 A _18060 s).
Proof. exact (MK_COMB (@lem1110852 A _18060) (@lem1110853 A s)). Qed.
Lemma lem1110855 {A : Type'} : (@eq (nat -> list A)) = (@eq (nat -> list A)).
Proof. exact (eq_refl (@eq (nat -> list A))). Qed.
Lemma lem1110856 {A : Type'} (_18060 : type1582 A) (s : nat -> A) : (term10 A _18060 s) = (term11 A _18060 s).
Proof. exact (MK_COMB (@lem1110855 A) (@lem1110854 A _18060 s)). Qed.
Lemma lem1110857 {A : Type'} (_18060 : type1582 A) (s : nat -> A) : (term5 A _18060 s) = (term8 A _18060 s).
Proof. exact (eq_refl (term5 A _18060 s)). Qed.
Lemma lem1110858 {A : Type'} (_18060 : type1582 A) (s : nat -> A) : ((term7 A _18060 s) = (term5 A _18060 s)) = ((term5 A _18060 s) = (term8 A _18060 s)).
Proof. exact (MK_COMB (@lem1110856 A _18060 s) (@lem1110857 A _18060 s)). Qed.
Lemma lem1110859 {A : Type'} (_18060 : type1582 A) (s : nat -> A) : (term5 A _18060 s) = (term8 A _18060 s).
Proof. exact (EQ_MP (@lem1110858 A _18060 s) (@lem1110850 A _18060 s)). Qed.
Lemma lem1110860 {A : Type'} (s : nat -> A) (list_of_seq' : type971 A) (_18060 : type1582 A) (h1 : list_of_seq' = (term4 A _18060)) : (list_of_seq' s) = (term8 A _18060 s).
Proof. exact (TRANS (@lem1110846 A s list_of_seq' _18060 h1) (@lem1110859 A _18060 s)). Qed.
Lemma lem1110861 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1110862 {A : Type'} (s : nat -> A) (n : nat) (list_of_seq' : type971 A) (_18060 : type1582 A) (h1 : list_of_seq' = (term4 A _18060)) : (list_of_seq' s n) = (term16 A _18060 s n).
Proof. exact (MK_COMB (@lem1110860 A s list_of_seq' _18060 h1) (@lem1110861 n)). Qed.
Lemma lem1110864 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1110762 A B f y) (@lem1110761 A B f y)). Qed.
Lemma lem1110865 {A : Type'} (f : type1609 A) (y : nat) : (term14 A f y) = (f y).
Proof. exact (@lem1110864 nat (list A) f y). Qed.
Lemma lem1110866 {A : Type'} (_18060 : type1582 A) (s : nat -> A) (n : nat) : (term37 A _18060 s n) = (term16 A _18060 s n).
Proof. exact (@lem1110865 A (term8 A _18060 s) n). Qed.
Lemma lem1110867 {A : Type'} (_18060 : type1582 A) (_18059 : nat) (s : nat -> A) : (term16 A _18060 s _18059) = (_18060 _18059 s).
Proof. exact (eq_refl (term16 A _18060 s _18059)). Qed.
Lemma lem1110868 {A : Type'} (_18060 : type1582 A) (s : nat -> A) : (term17 A _18060 s) = (term8 A _18060 s).
Proof. exact (fun_ext (fun _18059 : nat => @lem1110867 A _18060 _18059 s)). Qed.
Lemma lem1110869 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1110870 {A : Type'} (_18060 : type1582 A) (s : nat -> A) (n : nat) : (term37 A _18060 s n) = (term16 A _18060 s n).
Proof. exact (MK_COMB (@lem1110868 A _18060 s) (@lem1110869 n)). Qed.
Lemma lem1110871 {A : Type'} : (@eq (list A)) = (@eq (list A)).
Proof. exact (eq_refl (@eq (list A))). Qed.
Lemma lem1110872 {A : Type'} (_18060 : type1582 A) (s : nat -> A) (n : nat) : (term38 A _18060 s n) = (term39 A _18060 s n).
Proof. exact (MK_COMB (@lem1110871 A) (@lem1110870 A _18060 s n)). Qed.
Lemma lem1110873 {A : Type'} (_18060 : type1582 A) (n : nat) (s : nat -> A) : (term16 A _18060 s n) = (_18060 n s).
Proof. exact (eq_refl (term16 A _18060 s n)). Qed.
Lemma lem1110874 {A : Type'} (_18060 : type1582 A) (n : nat) (s : nat -> A) : ((term37 A _18060 s n) = (term16 A _18060 s n)) = ((term16 A _18060 s n) = (_18060 n s)).
Proof. exact (MK_COMB (@lem1110872 A _18060 s n) (@lem1110873 A _18060 n s)). Qed.
Lemma lem1110875 {A : Type'} (_18060 : type1582 A) (n : nat) (s : nat -> A) : (term16 A _18060 s n) = (_18060 n s).
Proof. exact (EQ_MP (@lem1110874 A _18060 n s) (@lem1110866 A _18060 s n)). Qed.
Lemma lem1110876 {A : Type'} (n : nat) (s : nat -> A) (list_of_seq' : type971 A) (_18060 : type1582 A) (h1 : list_of_seq' = (term4 A _18060)) : (list_of_seq' s n) = (_18060 n s).
Proof. exact (TRANS (@lem1110862 A s n list_of_seq' _18060 h1) (@lem1110875 A _18060 n s)). Qed.
Lemma lem1110877 {A : Type'} : (@List.app A) = (@List.app A).
Proof. exact (eq_refl (@List.app A)). Qed.
Lemma lem1110878 {A : Type'} (n : nat) (s : nat -> A) (list_of_seq' : type971 A) (_18060 : type1582 A) (h1 : list_of_seq' = (term4 A _18060)) : (term40 A list_of_seq' s n) = (term41 A _18060 n s).
Proof. exact (MK_COMB (@lem1110877 A) (@lem1110876 A n s list_of_seq' _18060 h1)). Qed.
Lemma lem1110879 {A : Type'} (s : nat -> A) (n : nat) : (term42 A s n) = (term42 A s n).
Proof. exact (eq_refl (term42 A s n)). Qed.
Lemma lem1110880 {A : Type'} (s : nat -> A) (n : nat) (list_of_seq' : type971 A) (_18060 : type1582 A) (h1 : list_of_seq' = (term4 A _18060)) : (term43 A list_of_seq' s n) = (term44 A _18060 s n).
Proof. exact (MK_COMB (@lem1110878 A n s list_of_seq' _18060 h1) (@lem1110879 A s n)). Qed.
Lemma lem1110881 {A : Type'} (s : nat -> A) (n : nat) (list_of_seq' : type971 A) (_18060 : type1582 A) (h1 : list_of_seq' = (term4 A _18060)) : ((term29 A list_of_seq' s n) = (term43 A list_of_seq' s n)) = ((term34 A _18060 n s) = (term44 A _18060 s n)).
Proof. exact (MK_COMB (@lem1110842 A n s list_of_seq' _18060 h1) (@lem1110880 A s n list_of_seq' _18060 h1)). Qed.
Lemma lem1110882 {A : Type'} (s : nat -> A) (list_of_seq' : type971 A) (_18060 : type1582 A) (h1 : list_of_seq' = (term4 A _18060)) : (term45 A list_of_seq' s) = (term46 A _18060 s).
Proof. exact (fun_ext (fun n : nat => @lem1110881 A s n list_of_seq' _18060 h1)). Qed.
Lemma lem1110883 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1110884 {A : Type'} (s : nat -> A) (list_of_seq' : type971 A) (_18060 : type1582 A) (h1 : list_of_seq' = (term4 A _18060)) : (term47 A list_of_seq' s) = (term48 A _18060 s).
Proof. exact (MK_COMB (@lem1110883) (@lem1110882 A s list_of_seq' _18060 h1)). Qed.
Lemma lem1110885 {A : Type'} (list_of_seq' : type971 A) (_18060 : type1582 A) (h1 : list_of_seq' = (term4 A _18060)) : (term49 A list_of_seq') = (term50 A _18060).
Proof. exact (fun_ext (fun s : nat -> A => @lem1110884 A s list_of_seq' _18060 h1)). Qed.
Lemma lem1110886 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem1110887 {A : Type'} (list_of_seq' : type971 A) (_18060 : type1582 A) (h1 : list_of_seq' = (term4 A _18060)) : (term51 A list_of_seq') = (term52 A _18060).
Proof. exact (MK_COMB (@lem1110886 A) (@lem1110885 A list_of_seq' _18060 h1)). Qed.
Lemma lem1110888 {A : Type'} (list_of_seq' : type971 A) (_18060 : type1582 A) (h1 : list_of_seq' = (term4 A _18060)) : (term53 A list_of_seq') = (term54 A _18060).
Proof. exact (MK_COMB (@lem1110806 A list_of_seq' _18060 h1) (@lem1110887 A list_of_seq' _18060 h1)). Qed.
Lemma lem1110889 {A : Type'} (_18060 : type1582 A) (h1 : (term55 A _18060) = (term56 A)) : (term55 A _18060) = (term56 A).
Proof. exact (h1). Qed.
Lemma lem1110890 {A : Type'} (s : nat -> A) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem1110891 {A : Type'} (s : nat -> A) (_18060 : type1582 A) (h1 : (term55 A _18060) = (term56 A)) : (term20 A _18060 s) = (term57 A s).
Proof. exact (MK_COMB (@lem1110889 A _18060 h1) (@lem1110890 A s)). Qed.
Lemma lem1110892 {A : Type'} (s : nat -> A) : (term57 A s) = (@nil A).
Proof. exact (eq_refl (term57 A s)). Qed.
Lemma lem1110893 {A : Type'} (_18060 : type1582 A) (s : nat -> A) : (term22 A _18060 s) = (term22 A _18060 s).
Proof. exact (eq_refl (term22 A _18060 s)). Qed.
Lemma lem1110894 {A : Type'} (_18060 : type1582 A) (s : nat -> A) : ((term20 A _18060 s) = (term57 A s)) = ((term20 A _18060 s) = (@nil A)).
Proof. exact (MK_COMB (@lem1110893 A _18060 s) (@lem1110892 A s)). Qed.
Lemma lem1110895 {A : Type'} (s : nat -> A) (_18060 : type1582 A) (h1 : (term55 A _18060) = (term56 A)) : (term20 A _18060 s) = (@nil A).
Proof. exact (EQ_MP (@lem1110894 A _18060 s) (@lem1110891 A s _18060 h1)). Qed.
Lemma lem1110896 {A : Type'} (_18060 : type1582 A) (h1 : (term55 A _18060) = (term56 A)) : term26 A _18060.
Proof. exact (fun s : nat -> A => @lem1110895 A s _18060 h1). Qed.
Lemma lem1110897 {A : Type'} (_18060 : type1582 A) (h1 : term58 A _18060) : term58 A _18060.
Proof. exact (h1). Qed.
Lemma lem1110898 {A : Type'} (n : nat) (_18060 : type1582 A) (h1 : term58 A _18060) : term59 A _18060 n.
Proof. exact (@lem1110897 A _18060 h1 n). Qed.
Lemma lem1110899 {A : Type'} (_18060 : type1582 A) (n : nat) : (term59 A _18060 n) = ((term60 A _18060 n) = (term61 A _18060 n)).
Proof. exact (eq_refl (term59 A _18060 n)). Qed.
Lemma lem1110900 {A : Type'} (n : nat) (_18060 : type1582 A) (h1 : term58 A _18060) : (term60 A _18060 n) = (term61 A _18060 n).
Proof. exact (EQ_MP (@lem1110899 A _18060 n) (@lem1110898 A n _18060 h1)). Qed.
Lemma lem1110901 {A : Type'} (s : nat -> A) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem1110902 {A : Type'} (n : nat) (s : nat -> A) (_18060 : type1582 A) (h1 : term58 A _18060) : (term34 A _18060 n s) = (term62 A _18060 n s).
Proof. exact (MK_COMB (@lem1110900 A n _18060 h1) (@lem1110901 A s)). Qed.
Lemma lem1110903 {A : Type'} (_18060 : type1582 A) (s : nat -> A) (n : nat) : (term62 A _18060 n s) = (term44 A _18060 s n).
Proof. exact (eq_refl (term62 A _18060 n s)). Qed.
Lemma lem1110904 {A : Type'} (_18060 : type1582 A) (n : nat) (s : nat -> A) : (term36 A _18060 n s) = (term36 A _18060 n s).
Proof. exact (eq_refl (term36 A _18060 n s)). Qed.
Lemma lem1110905 {A : Type'} (_18060 : type1582 A) (s : nat -> A) (n : nat) : ((term34 A _18060 n s) = (term62 A _18060 n s)) = ((term34 A _18060 n s) = (term44 A _18060 s n)).
Proof. exact (MK_COMB (@lem1110904 A _18060 n s) (@lem1110903 A _18060 s n)). Qed.
Lemma lem1110906 {A : Type'} (s : nat -> A) (n : nat) (_18060 : type1582 A) (h1 : term58 A _18060) : (term34 A _18060 n s) = (term44 A _18060 s n).
Proof. exact (EQ_MP (@lem1110905 A _18060 s n) (@lem1110902 A n s _18060 h1)). Qed.
Lemma lem1110907 {A : Type'} (s : nat -> A) (_18060 : type1582 A) (h1 : term58 A _18060) : term48 A _18060 s.
Proof. exact (fun n : nat => @lem1110906 A s n _18060 h1). Qed.
Lemma lem1110908 {A : Type'} (_18060 : type1582 A) (h1 : term58 A _18060) : term52 A _18060.
Proof. exact (fun s : nat -> A => @lem1110907 A s _18060 h1). Qed.
Lemma lem1110909 {A : Type'} (_18060 : type1582 A) (h1 : term63 A _18060) : term63 A _18060.
Proof. exact (h1). Qed.
Lemma lem1110910 {A : Type'} (_18060 : type1582 A) (h1 : term63 A _18060) : term58 A _18060.
Proof. exact (proj2 (@lem1110909 A _18060 h1)). Qed.
Lemma lem1110911 {A : Type'} (_18060 : type1582 A) (h1 : term63 A _18060) : (term55 A _18060) = (term56 A).
Proof. exact (proj1 (@lem1110909 A _18060 h1)). Qed.
Lemma lem1110912 {A : Type'} (_18060 : type1582 A) (h1 : term63 A _18060) : ((term55 A _18060) = (term56 A)) = (term26 A _18060).
Proof. exact (prop_ext (fun h2 : (term55 A _18060) = (term56 A) => @lem1110896 A _18060 h2) (fun h2 : term26 A _18060 => @lem1110911 A _18060 h1)). Qed.
Lemma lem1110913 {A : Type'} (_18060 : type1582 A) (h1 : term63 A _18060) : term26 A _18060.
Proof. exact (EQ_MP (@lem1110912 A _18060 h1) (@lem1110911 A _18060 h1)). Qed.
Lemma lem1110914 {A : Type'} (_18060 : type1582 A) (h1 : term63 A _18060) : (term58 A _18060) = (term52 A _18060).
Proof. exact (prop_ext (fun h2 : term58 A _18060 => @lem1110908 A _18060 h2) (fun h2 : term52 A _18060 => @lem1110910 A _18060 h1)). Qed.
Lemma lem1110915 {A : Type'} (_18060 : type1582 A) (h1 : term63 A _18060) : term52 A _18060.
Proof. exact (EQ_MP (@lem1110914 A _18060 h1) (@lem1110910 A _18060 h1)). Qed.
Lemma lem1110916 {A : Type'} (_18060 : type1582 A) (h1 : term63 A _18060) : term54 A _18060.
Proof. exact (conj (@lem1110913 A _18060 h1) (@lem1110915 A _18060 h1)). Qed.
Lemma lem1110917 {A : Type'} (e : A) : term64 A e.
Proof. exact (@lem75635 A e). Qed.
Lemma lem1110918 {A : Type'} (e : A) : (term64 A e) = (term65 A e).
Proof. exact (eq_refl (term64 A e)). Qed.
Lemma lem1110919 {A : Type'} (e : A) : term65 A e.
Proof. exact (EQ_MP (@lem1110918 A e) (@lem1110917 A e)). Qed.
Lemma lem1110920 {A : Type'} (e : A) (f : type1423 A) : term66 A e f.
Proof. exact (@lem1110919 A e f). Qed.
Lemma lem1110921 {A : Type'} (e : A) (f : type1423 A) : (term66 A e f) = (term67 A e f).
Proof. exact (eq_refl (term66 A e f)). Qed.
Lemma lem1110922 {A : Type'} (e : A) (f : type1423 A) : term67 A e f.
Proof. exact (EQ_MP (@lem1110921 A e f) (@lem1110920 A e f)). Qed.
Lemma lem1110923 {A : Type'} (e : type974 A) (f : type245 A) : term68 A e f.
Proof. exact (@lem1110922 (type974 A) e f). Qed.
Lemma lem1110924 {A : Type'} : term69 A.
Proof. exact (@lem1110923 A (term56 A) (term70 A)). Qed.
Lemma lem1110925 {A : Type'} (fn : type1582 A) (n : nat) : (term71 A fn n) = (term72 A fn n).
Proof. exact (eq_refl (term71 A fn n)). Qed.
Lemma lem1110926 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1110927 {A : Type'} (fn : type1582 A) (n : nat) : (term73 A fn n) = (term74 A fn n).
Proof. exact (MK_COMB (@lem1110925 A fn n) (@lem1110926 n)). Qed.
Lemma lem1110928 {A : Type'} (fn : type1582 A) (n : nat) : (term74 A fn n) = (term61 A fn n).
Proof. exact (eq_refl (term74 A fn n)). Qed.
Lemma lem1110929 {A : Type'} (fn : type1582 A) (n : nat) : (term73 A fn n) = (term61 A fn n).
Proof. exact (TRANS (@lem1110927 A fn n) (@lem1110928 A fn n)). Qed.
Lemma lem1110930 {A : Type'} (fn : type1582 A) (n : nat) : (term75 A fn n) = (term75 A fn n).
Proof. exact (eq_refl (term75 A fn n)). Qed.
Lemma lem1110931 {A : Type'} (fn : type1582 A) (n : nat) : ((term60 A fn n) = (term73 A fn n)) = ((term60 A fn n) = (term61 A fn n)).
Proof. exact (MK_COMB (@lem1110930 A fn n) (@lem1110929 A fn n)). Qed.
Lemma lem1110932 {A : Type'} (fn : type1582 A) : (term76 A fn) = (term77 A fn).
Proof. exact (fun_ext (fun n : nat => @lem1110931 A fn n)). Qed.
Lemma lem1110933 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1110934 {A : Type'} (fn : type1582 A) : (term78 A fn) = (term58 A fn).
Proof. exact (MK_COMB (@lem1110933) (@lem1110932 A fn)). Qed.
Lemma lem1110935 {A : Type'} (fn : type1582 A) : (term79 A fn) = (term79 A fn).
Proof. exact (eq_refl (term79 A fn)). Qed.
Lemma lem1110936 {A : Type'} (fn : type1582 A) : (term80 A fn) = (term63 A fn).
Proof. exact (MK_COMB (@lem1110935 A fn) (@lem1110934 A fn)). Qed.
Lemma lem1110937 {A : Type'} : (term81 A) = (term82 A).
Proof. exact (fun_ext (fun fn : type1582 A => @lem1110936 A fn)). Qed.
Lemma lem1110938 {A : Type'} : (@ex (nat -> (nat -> A) -> list A)) = (@ex (nat -> (nat -> A) -> list A)).
Proof. exact (eq_refl (@ex (nat -> (nat -> A) -> list A))). Qed.
Lemma lem1110939 {A : Type'} : (term69 A) = (term83 A).
Proof. exact (MK_COMB (@lem1110938 A) (@lem1110937 A)). Qed.
Lemma lem1110940 {A : Type'} : term83 A.
Proof. exact (EQ_MP (@lem1110939 A) (@lem1110924 A)). Qed.
Lemma lem1110941 {A : Type'} (_18060 : type1582 A) (h1 : term63 A _18060) : term63 A _18060.
Proof. exact (h1). Qed.
Lemma lem1110942 {A : Type'} (_18060 : type1582 A) (h1 : term63 A _18060) : term58 A _18060.
Proof. exact (proj2 (@lem1110941 A _18060 h1)). Qed.
Lemma lem1110943 {A : Type'} (_18060 : type1582 A) (h1 : term63 A _18060) : (term55 A _18060) = (term56 A).
Proof. exact (proj1 (@lem1110941 A _18060 h1)). Qed.
Lemma lem1110944 {A : Type'} (_18060 : type1582 A) (h1 : term63 A _18060) : term63 A _18060.
Proof. exact (conj (@lem1110943 A _18060 h1) (@lem1110942 A _18060 h1)). Qed.
Lemma lem1110945 {A : Type'} (_18060 : type1582 A) (h1 : term63 A _18060) : term83 A.
Proof. exact (ex_intro (term82 A) _18060 (@lem1110944 A _18060 h1)). Qed.
Lemma lem1110946 {A : Type'} (h1 : term83 A) : term83 A.
Proof. exact (h1). Qed.
Lemma lem1110947 {A : Type'} (h1 : term83 A) : term83 A.
Proof. exact (ex_elim (@lem1110946 A h1) (fun _18060 : type1582 A => fun h0 : term82 A _18060 => @lem1110945 A _18060 h0)). Qed.
Lemma lem1110948 {A : Type'} : (term83 A) = (term83 A).
Proof. exact (prop_ext (fun h1 : term83 A => @lem1110947 A h1) (fun h1 : term83 A => @lem1110940 A)). Qed.
Lemma lem1110949 {A : Type'} : term83 A.
Proof. exact (EQ_MP (@lem1110948 A) (@lem1110940 A)). Qed.
Lemma lem1110950 {A : Type'} (_18060 : type1582 A) (h1 : term63 A _18060) : term84 A.
Proof. exact (ex_intro (term85 A) _18060 (@lem1110916 A _18060 h1)). Qed.
Lemma lem1110951 {A : Type'} (h1 : term83 A) : term83 A.
Proof. exact (h1). Qed.
Lemma lem1110952 {A : Type'} (h1 : term83 A) : term84 A.
Proof. exact (ex_elim (@lem1110951 A h1) (fun _18060 : type1582 A => fun h0 : term82 A _18060 => @lem1110950 A _18060 h0)). Qed.
Lemma lem1110953 {A : Type'} : (term83 A) = (term84 A).
Proof. exact (prop_ext (fun h1 : term83 A => @lem1110952 A h1) (fun h1 : term84 A => @lem1110949 A)). Qed.
Lemma lem1110954 {A : Type'} : term84 A.
Proof. exact (EQ_MP (@lem1110953 A) (@lem1110949 A)). Qed.
Lemma lem1110955 {A : Type'} (_18060 : type1582 A) (h1 : term54 A _18060) : term54 A _18060.
Proof. exact (h1). Qed.
Lemma lem1110956 {A : Type'} (list_of_seq' : type971 A) (_18060 : type1582 A) (h1 : list_of_seq' = (term4 A _18060)) : (term54 A _18060) = (term53 A list_of_seq').
Proof. exact (SYM (@lem1110888 A list_of_seq' _18060 h1)). Qed.
Lemma lem1110957 {A : Type'} (list_of_seq' : type971 A) (_18060 : type1582 A) (h1 : term54 A _18060) (h2 : list_of_seq' = (term4 A _18060)) : term53 A list_of_seq'.
Proof. exact (EQ_MP (@lem1110956 A list_of_seq' _18060 h2) (@lem1110955 A _18060 h1)). Qed.
Lemma lem1110958 {A : Type'} (list_of_seq' : type971 A) (_18060 : type1582 A) (h1 : term54 A _18060) (h2 : list_of_seq' = (term4 A _18060)) : term86 A.
Proof. exact (ex_intro (term87 A) list_of_seq' (@lem1110957 A list_of_seq' _18060 h1 h2)). Qed.
Lemma lem1110959 {A : Type'} (_18060 : type1582 A) : (term4 A _18060) = (term4 A _18060).
Proof. exact (eq_refl (term4 A _18060)). Qed.
Lemma lem1110960 {A : Type'} (list_of_seq' : type971 A) (_18060 : type1582 A) (h1 : term54 A _18060) : term88 A list_of_seq' _18060.
Proof. exact (fun h0 : list_of_seq' = (term4 A _18060) => @lem1110958 A list_of_seq' _18060 h1 h0). Qed.
Lemma lem1110961 {A : Type'} (_18060 : type1582 A) (h1 : term54 A _18060) : term89 A _18060.
Proof. exact (@lem1110960 A (term4 A _18060) _18060 h1). Qed.
Lemma lem1110962 {A : Type'} (_18060 : type1582 A) (h1 : term54 A _18060) : term86 A.
Proof. exact (@lem1110961 A _18060 h1 (@lem1110959 A _18060)). Qed.
Lemma lem1110963 {A : Type'} (h1 : term84 A) : term84 A.
Proof. exact (h1). Qed.
Lemma lem1110964 {A : Type'} (h1 : term84 A) : term86 A.
Proof. exact (ex_elim (@lem1110963 A h1) (fun _18060 : type1582 A => fun h0 : term85 A _18060 => @lem1110962 A _18060 h0)). Qed.
Lemma lem1110965 {A : Type'} : (term84 A) = (term86 A).
Proof. exact (prop_ext (fun h1 : term84 A => @lem1110964 A h1) (fun h1 : term86 A => @lem1110954 A)). Qed.
Lemma lem1110966 {A : Type'} : term86 A.
Proof. exact (EQ_MP (@lem1110965 A) (@lem1110954 A)). Qed.
Lemma lem1110967 {A : Type'} : term90 A.
Proof. exact (fun _18064 : type1667 => @lem1110966 A). Qed.
Lemma lem1110968 {A B : Type'} (P : type1413 A B) : term91 A B P.
Proof. exact (@lem13546 A B P). Qed.
Lemma lem1110969 {A B : Type'} (P : type1413 A B) : (term91 A B P) = ((term92 A B P) = (term93 A B P)).
Proof. exact (eq_refl (term91 A B P)). Qed.
Lemma lem1110972 {A B : Type'} (P : type1413 A B) : (term92 A B P) = (term93 A B P).
Proof. exact (EQ_MP (@lem1110969 A B P) (@lem1110968 A B P)). Qed.
Lemma lem1110973 {A : Type'} (P : type1235 A) : (term94 A P) = (term95 A P).
Proof. exact (@lem1110972 type1667 (type971 A) P). Qed.
Lemma lem1110974 {A : Type'} : (term96 A) = (term97 A).
Proof. exact (@lem1110973 A (term98 A)). Qed.
Lemma lem1110975 {A : Type'} (_18064 : type1667) : (term99 A _18064) = (term87 A).
Proof. exact (eq_refl (term99 A _18064)). Qed.
Lemma lem1110976 {A : Type'} (list_of_seq' : type971 A) : list_of_seq' = list_of_seq'.
Proof. exact (eq_refl list_of_seq'). Qed.
Lemma lem1110977 {A : Type'} (_18064 : type1667) (list_of_seq' : type971 A) : (term100 A _18064 list_of_seq') = (term101 A list_of_seq').
Proof. exact (MK_COMB (@lem1110975 A _18064) (@lem1110976 A list_of_seq')). Qed.
Lemma lem1110978 {A : Type'} (list_of_seq' : type971 A) : (term101 A list_of_seq') = (term53 A list_of_seq').
Proof. exact (eq_refl (term101 A list_of_seq')). Qed.
Lemma lem1110979 {A : Type'} (_18064 : type1667) (list_of_seq' : type971 A) : (term100 A _18064 list_of_seq') = (term53 A list_of_seq').
Proof. exact (TRANS (@lem1110977 A _18064 list_of_seq') (@lem1110978 A list_of_seq')). Qed.
Lemma lem1110980 {A : Type'} (_18064 : type1667) : (term102 A _18064) = (term87 A).
Proof. exact (fun_ext (fun list_of_seq' : type971 A => @lem1110979 A _18064 list_of_seq')). Qed.
Lemma lem1110981 {A : Type'} : (@ex ((nat -> A) -> nat -> list A)) = (@ex ((nat -> A) -> nat -> list A)).
Proof. exact (eq_refl (@ex ((nat -> A) -> nat -> list A))). Qed.
Lemma lem1110982 {A : Type'} (_18064 : type1667) : (term103 A _18064) = (term86 A).
Proof. exact (MK_COMB (@lem1110981 A) (@lem1110980 A _18064)). Qed.
Lemma lem1110983 {A : Type'} : (term104 A) = (term105 A).
Proof. exact (fun_ext (fun _18064 : type1667 => @lem1110982 A _18064)). Qed.
Lemma lem1110984 : (@all (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))))) = (@all (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))))).
Proof. exact (eq_refl (@all (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))))). Qed.
Lemma lem1110985 {A : Type'} : (term96 A) = (term90 A).
Proof. exact (MK_COMB (@lem1110984) (@lem1110983 A)). Qed.
Lemma lem1110986 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1110987 {A : Type'} : (term106 A) = (term107 A).
Proof. exact (MK_COMB (@lem1110986) (@lem1110985 A)). Qed.
Lemma lem1110988 {A : Type'} (_18064 : type1667) : (term99 A _18064) = (term87 A).
Proof. exact (eq_refl (term99 A _18064)). Qed.
Lemma lem1110989 {A : Type'} (list_of_seq' : type1237 A) (_18064 : type1667) : (list_of_seq' _18064) = (list_of_seq' _18064).
Proof. exact (eq_refl (list_of_seq' _18064)). Qed.
Lemma lem1110990 {A : Type'} (list_of_seq' : type1237 A) (_18064 : type1667) : (term108 A list_of_seq' _18064) = (term109 A list_of_seq' _18064).
Proof. exact (MK_COMB (@lem1110988 A _18064) (@lem1110989 A list_of_seq' _18064)). Qed.
Lemma lem1110991 {A : Type'} (list_of_seq' : type1237 A) (_18064 : type1667) : (term109 A list_of_seq' _18064) = (term110 A list_of_seq' _18064).
Proof. exact (eq_refl (term109 A list_of_seq' _18064)). Qed.
Lemma lem1110992 {A : Type'} (list_of_seq' : type1237 A) (_18064 : type1667) : (term108 A list_of_seq' _18064) = (term110 A list_of_seq' _18064).
Proof. exact (TRANS (@lem1110990 A list_of_seq' _18064) (@lem1110991 A list_of_seq' _18064)). Qed.
Lemma lem1110993 {A : Type'} (list_of_seq' : type1237 A) : (term111 A list_of_seq') = (term112 A list_of_seq').
Proof. exact (fun_ext (fun _18064 : type1667 => @lem1110992 A list_of_seq' _18064)). Qed.
Lemma lem1110994 : (@all (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))))) = (@all (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))))).
Proof. exact (eq_refl (@all (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))))). Qed.
Lemma lem1110995 {A : Type'} (list_of_seq' : type1237 A) : (term113 A list_of_seq') = (term114 A list_of_seq').
Proof. exact (MK_COMB (@lem1110994) (@lem1110993 A list_of_seq')). Qed.
Lemma lem1110996 {A : Type'} : (term115 A) = (term116 A).
Proof. exact (fun_ext (fun list_of_seq' : type1237 A => @lem1110995 A list_of_seq')). Qed.
Lemma lem1110997 {A : Type'} : (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))) -> (nat -> A) -> nat -> list A)) = (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))) -> (nat -> A) -> nat -> list A)).
Proof. exact (eq_refl (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))) -> (nat -> A) -> nat -> list A))). Qed.
Lemma lem1110998 {A : Type'} : (term97 A) = (term117 A).
Proof. exact (MK_COMB (@lem1110997 A) (@lem1110996 A)). Qed.
Lemma lem1110999 {A : Type'} : ((term96 A) = (term97 A)) = ((term90 A) = (term117 A)).
Proof. exact (MK_COMB (@lem1110987 A) (@lem1110998 A)). Qed.
Lemma lem1111000 {A : Type'} : (term90 A) = (term117 A).
Proof. exact (EQ_MP (@lem1110999 A) (@lem1110974 A)). Qed.
Lemma lem1111001 {A : Type'} : term117 A.
Proof. exact (EQ_MP (@lem1111000 A) (@lem1110967 A)). Qed.
Lemma lem1111003 {A : Type'} : (@ex A) = (term118 A).
Proof. exact (@lem9261 A (@lem9306 A)). Qed.
Lemma lem1111004 {A : Type'} : (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))) -> (nat -> A) -> nat -> list A)) = (term119 A).
Proof. exact (@lem1111003 (type1237 A)). Qed.
Lemma lem1111005 {A : Type'} : (term116 A) = (term116 A).
Proof. exact (eq_refl (term116 A)). Qed.
Lemma lem1111006 {A : Type'} : (term117 A) = (term120 A).
Proof. exact (MK_COMB (@lem1111004 A) (@lem1111005 A)). Qed.
Lemma lem1111007 {A : Type'} : (term120 A) = (term121 A).
Proof. exact (eq_refl (term120 A)). Qed.
Lemma lem1111008 {A : Type'} : (term117 A) = (term121 A).
Proof. exact (TRANS (@lem1111006 A) (@lem1111007 A)). Qed.
Lemma lem1111009 {A : Type'} : term121 A.
Proof. exact (EQ_MP (@lem1111008 A) (@lem1111001 A)). Qed.
