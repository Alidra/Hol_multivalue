Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LE_ADD_LCANCEL_term_abbrevs.
Require Import ADD_ASSOC_spec.
Require Import EQ_ADD_LCANCEL_spec.
Require Import LE_EXISTS_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem100777 (m : nat) (n : nat) (p : nat) (h1 : (term0 m n p) = (term1 m n p)) : (term0 m n p) = (term1 m n p).
Proof. exact (h1). Qed.
Lemma lem100778 (m : nat) (n : nat) (p : nat) (h1 : (term0 m n p) = (term1 m n p)) : (term1 m n p) = (term0 m n p).
Proof. exact (SYM (@lem100777 m n p h1)). Qed.
Lemma lem100779 (m : nat) (n : nat) (p : nat) (h1 : (term1 m n p) = (term0 m n p)) : (term1 m n p) = (term0 m n p).
Proof. exact (h1). Qed.
Lemma lem100780 (m : nat) (n : nat) (p : nat) (h1 : (term1 m n p) = (term0 m n p)) : (term0 m n p) = (term1 m n p).
Proof. exact (SYM (@lem100779 m n p h1)). Qed.
Lemma lem100781 (m : nat) (n : nat) (p : nat) : ((term0 m n p) = (term1 m n p)) = ((term1 m n p) = (term0 m n p)).
Proof. exact (prop_ext (fun h1 : (term0 m n p) = (term1 m n p) => @lem100778 m n p h1) (fun h1 : (term1 m n p) = (term0 m n p) => @lem100780 m n p h1)). Qed.
Lemma lem100782 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (fun_ext (fun p : nat => @lem100781 m n p)). Qed.
Lemma lem100783 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem100784 (m : nat) (n : nat) : (term4 m n) = (term5 m n).
Proof. exact (MK_COMB (@lem100783) (@lem100782 m n)). Qed.
Lemma lem100785 (m : nat) : (term6 m) = (term7 m).
Proof. exact (fun_ext (fun n : nat => @lem100784 m n)). Qed.
Lemma lem100786 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem100787 (m : nat) : (term8 m) = (term9 m).
Proof. exact (MK_COMB (@lem100786) (@lem100785 m)). Qed.
Lemma lem100788 : term10 = term11.
Proof. exact (fun_ext (fun m : nat => @lem100787 m)). Qed.
Lemma lem100789 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem100790 : term12 = term13.
Proof. exact (MK_COMB (@lem100789) (@lem100788)). Qed.
Lemma lem100791 : term13.
Proof. exact (EQ_MP (@lem100790) (@lem77960)). Qed.
Lemma lem100792 (m : nat) : term14 m.
Proof. exact (@lem79639 m). Qed.
Lemma lem100793 (m : nat) : (term14 m) = (term15 m).
Proof. exact (eq_refl (term14 m)). Qed.
Lemma lem100794 (m : nat) : term15 m.
Proof. exact (EQ_MP (@lem100793 m) (@lem100792 m)). Qed.
Lemma lem100795 (m : nat) (n : nat) : term16 m n.
Proof. exact (@lem100794 m n). Qed.
Lemma lem100796 (m : nat) (n : nat) : (term16 m n) = (term17 m n).
Proof. exact (eq_refl (term16 m n)). Qed.
Lemma lem100797 (m : nat) (n : nat) : term17 m n.
Proof. exact (EQ_MP (@lem100796 m n) (@lem100795 m n)). Qed.
Lemma lem100798 (m : nat) (n : nat) (p : nat) : term18 m n p.
Proof. exact (@lem100797 m n p). Qed.
Lemma lem100799 (m : nat) (n : nat) (p : nat) : (term18 m n p) = (((Nat.add m n) = (Nat.add m p)) = (n = p)).
Proof. exact (eq_refl (term18 m n p)). Qed.
Lemma lem100801 (m : nat) : term19 m.
Proof. exact (@lem100791 m). Qed.
Lemma lem100802 (m : nat) : (term19 m) = (term9 m).
Proof. exact (eq_refl (term19 m)). Qed.
Lemma lem100803 (m : nat) : term9 m.
Proof. exact (EQ_MP (@lem100802 m) (@lem100801 m)). Qed.
Lemma lem100804 (m : nat) (n : nat) : term20 m n.
Proof. exact (@lem100803 m n). Qed.
Lemma lem100805 (m : nat) (n : nat) : (term20 m n) = (term5 m n).
Proof. exact (eq_refl (term20 m n)). Qed.
Lemma lem100806 (m : nat) (n : nat) : term5 m n.
Proof. exact (EQ_MP (@lem100805 m n) (@lem100804 m n)). Qed.
Lemma lem100807 (m : nat) (n : nat) (p : nat) : term21 m n p.
Proof. exact (@lem100806 m n p). Qed.
Lemma lem100808 (m : nat) (n : nat) (p : nat) : (term21 m n p) = ((term1 m n p) = (term0 m n p)).
Proof. exact (eq_refl (term21 m n p)). Qed.
Lemma lem100810 (m : nat) : term22 m.
Proof. exact (@lem99708 m). Qed.
Lemma lem100811 (m : nat) : (term22 m) = (term23 m).
Proof. exact (eq_refl (term22 m)). Qed.
Lemma lem100812 (m : nat) : term23 m.
Proof. exact (EQ_MP (@lem100811 m) (@lem100810 m)). Qed.
Lemma lem100813 (m : nat) (n : nat) : term24 m n.
Proof. exact (@lem100812 m n). Qed.
Lemma lem100814 (n : nat) (m : nat) : (term24 m n) = ((Peano.le m n) = (term25 n m)).
Proof. exact (eq_refl (term24 m n)). Qed.
Lemma lem100831 (n : nat) (m : nat) : (Peano.le m n) = (term25 n m).
Proof. exact (EQ_MP (@lem100814 n m) (@lem100813 m n)). Qed.
Lemma lem100832 (p : nat) (m : nat) (n : nat) : (term26 n m p) = (term27 p m n).
Proof. exact (@lem100831 (Nat.add m p) (Nat.add m n)). Qed.
Lemma lem100842 (m : nat) (n : nat) (p : nat) : (term1 m n p) = (term0 m n p).
Proof. exact (EQ_MP (@lem100808 m n p) (@lem100807 m n p)). Qed.
Lemma lem100843 (m : nat) (n : nat) (d : nat) : (term1 m n d) = (term0 m n d).
Proof. exact (@lem100842 m n d). Qed.
Lemma lem100844 (m : nat) (p : nat) : (term28 m p) = (term28 m p).
Proof. exact (eq_refl (term28 m p)). Qed.
Lemma lem100845 (p : nat) (m : nat) (n : nat) (d : nat) : ((Nat.add m p) = (term1 m n d)) = ((Nat.add m p) = (term0 m n d)).
Proof. exact (MK_COMB (@lem100844 m p) (@lem100843 m n d)). Qed.
Lemma lem100847 (m : nat) (n : nat) (p : nat) : ((Nat.add m n) = (Nat.add m p)) = (n = p).
Proof. exact (EQ_MP (@lem100799 m n p) (@lem100798 m n p)). Qed.
Lemma lem100848 (m : nat) (p : nat) (n : nat) (d : nat) : ((Nat.add m p) = (term0 m n d)) = (p = (Nat.add n d)).
Proof. exact (@lem100847 m p (Nat.add n d)). Qed.
Lemma lem100851 (m : nat) (p : nat) (n : nat) (d : nat) : ((Nat.add m p) = (term1 m n d)) = (p = (Nat.add n d)).
Proof. exact (TRANS (@lem100845 p m n d) (@lem100848 m p n d)). Qed.
Lemma lem100852 (m : nat) (p : nat) (n : nat) : (term29 p m n) = (term30 p n).
Proof. exact (fun_ext (fun d : nat => @lem100851 m p n d)). Qed.
Lemma lem100853 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem100854 (m : nat) (p : nat) (n : nat) : (term27 p m n) = (term25 p n).
Proof. exact (MK_COMB (@lem100853) (@lem100852 m p n)). Qed.
Lemma lem100859 (m : nat) (p : nat) (n : nat) : (term26 n m p) = (term25 p n).
Proof. exact (TRANS (@lem100832 p m n) (@lem100854 m p n)). Qed.
Lemma lem100860 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem100861 (m : nat) (p : nat) (n : nat) : (term31 n m p) = (term32 p n).
Proof. exact (MK_COMB (@lem100860) (@lem100859 m p n)). Qed.
Lemma lem100863 (n : nat) (m : nat) : (Peano.le m n) = (term25 n m).
Proof. exact (EQ_MP (@lem100814 n m) (@lem100813 m n)). Qed.
Lemma lem100864 (p : nat) (n : nat) : (Peano.le n p) = (term25 p n).
Proof. exact (@lem100863 p n). Qed.
Lemma lem100871 (m : nat) (p : nat) (n : nat) : ((term26 n m p) = (Peano.le n p)) = ((term25 p n) = (term25 p n)).
Proof. exact (MK_COMB (@lem100861 m p n) (@lem100864 p n)). Qed.
Lemma lem100873 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem100874 (x : Prop) : (x = x) = True.
Proof. exact (@lem100873 Prop x). Qed.
Lemma lem100875 (p : nat) (n : nat) : ((term25 p n) = (term25 p n)) = True.
Proof. exact (@lem100874 (term25 p n)). Qed.
Lemma lem100876 (m : nat) (n : nat) (p : nat) : ((term26 n m p) = (Peano.le n p)) = True.
Proof. exact (TRANS (@lem100871 m p n) (@lem100875 p n)). Qed.
Lemma lem100877 (m : nat) (n : nat) : (term33 m n) = term34.
Proof. exact (fun_ext (fun p : nat => @lem100876 m n p)). Qed.
Lemma lem100878 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem100879 (m : nat) (n : nat) : (term35 m n) = term36.
Proof. exact (MK_COMB (@lem100878) (@lem100877 m n)). Qed.
Lemma lem100881 {A : Type'} (t : Prop) : (term37 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem100882 (t : Prop) : (term38 t) = t.
Proof. exact (@lem100881 nat t). Qed.
Lemma lem100883 : term36 = True.
Proof. exact (@lem100882 True). Qed.
Lemma lem100884 (m : nat) (n : nat) : (term35 m n) = True.
Proof. exact (TRANS (@lem100879 m n) (@lem100883)). Qed.
Lemma lem100885 (m : nat) : (term39 m) = term34.
Proof. exact (fun_ext (fun n : nat => @lem100884 m n)). Qed.
Lemma lem100886 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem100887 (m : nat) : (term40 m) = term36.
Proof. exact (MK_COMB (@lem100886) (@lem100885 m)). Qed.
Lemma lem100889 {A : Type'} (t : Prop) : (term37 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem100890 (t : Prop) : (term38 t) = t.
Proof. exact (@lem100889 nat t). Qed.
Lemma lem100891 : term36 = True.
Proof. exact (@lem100890 True). Qed.
Lemma lem100892 (m : nat) : (term40 m) = True.
Proof. exact (TRANS (@lem100887 m) (@lem100891)). Qed.
Lemma lem100893 : term41 = term34.
Proof. exact (fun_ext (fun m : nat => @lem100892 m)). Qed.
Lemma lem100894 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem100895 : term42 = term36.
Proof. exact (MK_COMB (@lem100894) (@lem100893)). Qed.
Lemma lem100897 {A : Type'} (t : Prop) : (term37 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem100898 (t : Prop) : (term38 t) = t.
Proof. exact (@lem100897 nat t). Qed.
Lemma lem100899 : term36 = True.
Proof. exact (@lem100898 True). Qed.
Lemma lem100900 : term42 = True.
Proof. exact (TRANS (@lem100895) (@lem100899)). Qed.
Lemma lem100901 : True = term42.
Proof. exact (SYM (@lem100900)). Qed.
Lemma lem100902 : term42.
Proof. exact (EQ_MP (@lem100901) (@lem0)). Qed.
