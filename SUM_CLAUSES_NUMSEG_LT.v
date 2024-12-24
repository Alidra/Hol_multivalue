Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_CLAUSES_NUMSEG_LT_term_abbrevs.
Require Import ITERATE_CLAUSES_NUMSEG_LT_spec.
Require Import MONOIDAL_REAL_ADD_spec.
Require Import thm0_spec.
Require Import thm1823_spec.
Require Import thm7064097_spec.
Require Import thm7064111_spec.
Require Import thm7064171_spec.
Require Import thm7065437_spec.
Lemma lem7221725 {_123501 : Type'} (f : nat -> _123501) (op : type1400 _123501) : term0 _123501 f op.
Proof. exact (@lem6194987 _123501 f op). Qed.
Lemma lem7221726 {_123501 : Type'} (op : type1400 _123501) (f : nat -> _123501) : (term0 _123501 f op) = (term1 _123501 op f).
Proof. exact (eq_refl (term0 _123501 f op)). Qed.
Lemma lem7221729 {_123501 : Type'} (op : type1400 _123501) (f : nat -> _123501) : term1 _123501 op f.
Proof. exact (EQ_MP (@lem7221726 _123501 op f) (@lem7221725 _123501 f op)). Qed.
Lemma lem7221730 (op : type1627) (f : nat -> real) : term2 op f.
Proof. exact (@lem7221729 real op f). Qed.
Lemma lem7221731 (f : nat -> real) : term3 f.
Proof. exact (@lem7221730 real_add f). Qed.
Lemma lem7221732 (f : nat -> real) : term4 f.
Proof. exact (@lem7221731 f (@lem7067132)). Qed.
Lemma lem7221744 : (@neutral real real_add) = term5.
Proof. exact (EQ_MP (@lem7064171) (@lem7065437)). Qed.
Lemma lem7221745 (f : nat -> real) : (term6 f) = (term6 f).
Proof. exact (eq_refl (term6 f)). Qed.
Lemma lem7221746 (f : nat -> real) : ((term7 f) = (@neutral real real_add)) = ((term7 f) = term5).
Proof. exact (MK_COMB (@lem7221745 f) (@lem7221744)). Qed.
Lemma lem7221749 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7221750 (f : nat -> real) : (term8 f) = (term9 f).
Proof. exact (MK_COMB (@lem7221749) (@lem7221746 f)). Qed.
Lemma lem7221765 (f : nat -> real) : (term10 f) = (term10 f).
Proof. exact (eq_refl (term10 f)). Qed.
Lemma lem7221766 (f : nat -> real) : (term4 f) = (term11 f).
Proof. exact (MK_COMB (@lem7221750 f) (@lem7221765 f)). Qed.
Lemma lem7221769 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7221770 (f : nat -> real) : (term12 f) = (term13 f).
Proof. exact (MK_COMB (@lem7221769) (@lem7221766 f)). Qed.
Lemma lem7221776 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7221777 : (@sum nat) = (@iterate real nat real_add).
Proof. exact (@lem7221776 nat). Qed.
Lemma lem7221782 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem7221783 : term15 = term16.
Proof. exact (MK_COMB (@lem7221777) (@lem7221782)). Qed.
Lemma lem7221784 (f : nat -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7221785 (f : nat -> real) : (term17 f) = (term7 f).
Proof. exact (MK_COMB (@lem7221783) (@lem7221784 f)). Qed.
Lemma lem7221786 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7221787 (f : nat -> real) : (term18 f) = (term6 f).
Proof. exact (MK_COMB (@lem7221786) (@lem7221785 f)). Qed.
Lemma lem7221788 : term5 = term5.
Proof. exact (eq_refl term5). Qed.
Lemma lem7221789 (f : nat -> real) : ((term17 f) = term5) = ((term7 f) = term5).
Proof. exact (MK_COMB (@lem7221787 f) (@lem7221788)). Qed.
Lemma lem7221792 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7221793 (f : nat -> real) : (term19 f) = (term9 f).
Proof. exact (MK_COMB (@lem7221792) (@lem7221789 f)). Qed.
Lemma lem7221801 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7221802 : (@sum nat) = (@iterate real nat real_add).
Proof. exact (@lem7221801 nat). Qed.
Lemma lem7221807 (k : nat) : (term20 k) = (term20 k).
Proof. exact (eq_refl (term20 k)). Qed.
Lemma lem7221808 (k : nat) : (term21 k) = (term22 k).
Proof. exact (MK_COMB (@lem7221802) (@lem7221807 k)). Qed.
Lemma lem7221809 (f : nat -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7221810 (k : nat) (f : nat -> real) : (term23 k f) = (term24 k f).
Proof. exact (MK_COMB (@lem7221808 k) (@lem7221809 f)). Qed.
Lemma lem7221811 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7221812 (k : nat) (f : nat -> real) : (term25 k f) = (term26 k f).
Proof. exact (MK_COMB (@lem7221811) (@lem7221810 k f)). Qed.
Lemma lem7221814 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7221815 : (@sum nat) = (@iterate real nat real_add).
Proof. exact (@lem7221814 nat). Qed.
Lemma lem7221820 (k : nat) : (term27 k) = (term27 k).
Proof. exact (eq_refl (term27 k)). Qed.
Lemma lem7221821 (k : nat) : (term28 k) = (term29 k).
Proof. exact (MK_COMB (@lem7221815) (@lem7221820 k)). Qed.
Lemma lem7221822 (f : nat -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7221823 (k : nat) (f : nat -> real) : (term30 k f) = (term31 k f).
Proof. exact (MK_COMB (@lem7221821 k) (@lem7221822 f)). Qed.
Lemma lem7221824 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7221825 (k : nat) (f : nat -> real) : (term32 k f) = (term33 k f).
Proof. exact (MK_COMB (@lem7221824) (@lem7221823 k f)). Qed.
Lemma lem7221826 (f : nat -> real) (k : nat) : (f k) = (f k).
Proof. exact (eq_refl (f k)). Qed.
Lemma lem7221827 (f : nat -> real) (k : nat) : (term34 f k) = (term35 f k).
Proof. exact (MK_COMB (@lem7221825 k f) (@lem7221826 f k)). Qed.
Lemma lem7221828 (f : nat -> real) (k : nat) : ((term23 k f) = (term34 f k)) = ((term24 k f) = (term35 f k)).
Proof. exact (MK_COMB (@lem7221812 k f) (@lem7221827 f k)). Qed.
Lemma lem7221831 (f : nat -> real) : (term36 f) = (term37 f).
Proof. exact (fun_ext (fun k : nat => @lem7221828 f k)). Qed.
Lemma lem7221832 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7221833 (f : nat -> real) : (term38 f) = (term10 f).
Proof. exact (MK_COMB (@lem7221832) (@lem7221831 f)). Qed.
Lemma lem7221838 (f : nat -> real) : (term39 f) = (term11 f).
Proof. exact (MK_COMB (@lem7221793 f) (@lem7221833 f)). Qed.
Lemma lem7221841 (f : nat -> real) : (term40 f) = (term41 f).
Proof. exact (MK_COMB (@lem7221770 f) (@lem7221838 f)). Qed.
Lemma lem7221843 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem7221844 (f : nat -> real) : (term41 f) = True.
Proof. exact (@lem7221843 (term11 f)). Qed.
Lemma lem7221847 (f : nat -> real) : (term42 f) = (term42 f).
Proof. exact (eq_refl (term42 f)). Qed.
Lemma lem7221848 (f : nat -> real) : (term42 f) = ((term41 f) = True).
Proof. exact (eq_refl (term42 f)). Qed.
Lemma lem7221849 (f : nat -> real) : (term43 f) = (term43 f).
Proof. exact (eq_refl (term43 f)). Qed.
Lemma lem7221850 (f : nat -> real) : ((term42 f) = (term42 f)) = ((term42 f) = ((term41 f) = True)).
Proof. exact (MK_COMB (@lem7221849 f) (@lem7221848 f)). Qed.
Lemma lem7221851 (f : nat -> real) : (term42 f) = ((term41 f) = True).
Proof. exact (eq_refl (term42 f)). Qed.
Lemma lem7221852 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7221853 (f : nat -> real) : (term43 f) = (term44 f).
Proof. exact (MK_COMB (@lem7221852) (@lem7221851 f)). Qed.
Lemma lem7221854 (f : nat -> real) : ((term41 f) = True) = ((term41 f) = True).
Proof. exact (eq_refl ((term41 f) = True)). Qed.
Lemma lem7221855 (f : nat -> real) : ((term42 f) = ((term41 f) = True)) = (((term41 f) = True) = ((term41 f) = True)).
Proof. exact (MK_COMB (@lem7221853 f) (@lem7221854 f)). Qed.
Lemma lem7221856 (f : nat -> real) : ((term42 f) = (term42 f)) = (((term41 f) = True) = ((term41 f) = True)).
Proof. exact (TRANS (@lem7221850 f) (@lem7221855 f)). Qed.
Lemma lem7221857 (f : nat -> real) : ((term41 f) = True) = ((term41 f) = True).
Proof. exact (EQ_MP (@lem7221856 f) (@lem7221847 f)). Qed.
Lemma lem7221858 (f : nat -> real) : (term41 f) = True.
Proof. exact (EQ_MP (@lem7221857 f) (@lem7221844 f)). Qed.
Lemma lem7221859 (f : nat -> real) : (term40 f) = True.
Proof. exact (TRANS (@lem7221841 f) (@lem7221858 f)). Qed.
Lemma lem7221860 (f : nat -> real) : True = (term40 f).
Proof. exact (SYM (@lem7221859 f)). Qed.
Lemma lem7221861 (f : nat -> real) : term40 f.
Proof. exact (EQ_MP (@lem7221860 f) (@lem0)). Qed.
Lemma lem7221862 (f : nat -> real) : term39 f.
Proof. exact (@lem7221861 f (@lem7221732 f)). Qed.
