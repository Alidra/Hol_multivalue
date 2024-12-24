Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NADD_CAUCHY_term_abbrevs.
Require Import ETA_AX_spec.
Require Import is_nadd_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1262764 (x : nat -> nat) (h1 : (is_nadd x) = (term0 x)) : (is_nadd x) = (term0 x).
Proof. exact (h1). Qed.
Lemma lem1262765 (x : nat -> nat) (h1 : (is_nadd x) = (term0 x)) : (term0 x) = (is_nadd x).
Proof. exact (SYM (@lem1262764 x h1)). Qed.
Lemma lem1262766 (x : nat -> nat) (h1 : (term0 x) = (is_nadd x)) : (term0 x) = (is_nadd x).
Proof. exact (h1). Qed.
Lemma lem1262767 (x : nat -> nat) (h1 : (term0 x) = (is_nadd x)) : (is_nadd x) = (term0 x).
Proof. exact (SYM (@lem1262766 x h1)). Qed.
Lemma lem1262768 (x : nat -> nat) : ((is_nadd x) = (term0 x)) = ((term0 x) = (is_nadd x)).
Proof. exact (prop_ext (fun h1 : (is_nadd x) = (term0 x) => @lem1262765 x h1) (fun h1 : (term0 x) = (is_nadd x) => @lem1262767 x h1)). Qed.
Lemma lem1262769 : term1 = term2.
Proof. exact (fun_ext (fun x : nat -> nat => @lem1262768 x)). Qed.
Lemma lem1262770 : (@all (nat -> nat)) = (@all (nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat))). Qed.
Lemma lem1262771 : term3 = term4.
Proof. exact (MK_COMB (@lem1262770) (@lem1262769)). Qed.
Lemma lem1262772 : term4.
Proof. exact (EQ_MP (@lem1262771) (@lem1262615)). Qed.
Lemma lem1262773 {A B : Type'} (t : A -> B) : term5 A B t.
Proof. exact (@lem9121 A B t). Qed.
Lemma lem1262774 {A B : Type'} (t : A -> B) : (term5 A B t) = ((term6 A B t) = t).
Proof. exact (eq_refl (term5 A B t)). Qed.
Lemma lem1262775 {A B : Type'} (t : A -> B) : (term6 A B t) = t.
Proof. exact (EQ_MP (@lem1262774 A B t) (@lem1262773 A B t)). Qed.
Lemma lem1262776 (x : nat -> nat) : term7 x.
Proof. exact (@lem1262772 x). Qed.
Lemma lem1262777 (x : nat -> nat) : (term7 x) = ((term0 x) = (is_nadd x)).
Proof. exact (eq_refl (term7 x)). Qed.
Lemma lem1262784 (x : nat -> nat) : (term0 x) = (is_nadd x).
Proof. exact (EQ_MP (@lem1262777 x) (@lem1262776 x)). Qed.
Lemma lem1262785 (x : nadd) : (term8 x) = (term9 x).
Proof. exact (@lem1262784 (term10 x)). Qed.
Lemma lem1262786 (x : nadd) (n : nat) : (term11 x n) = (dest_nadd x n).
Proof. exact (eq_refl (term11 x n)). Qed.
Lemma lem1262787 (m : nat) : (Nat.mul m) = (Nat.mul m).
Proof. exact (eq_refl (Nat.mul m)). Qed.
Lemma lem1262788 (m : nat) (x : nadd) (n : nat) : (term12 m x n) = (term13 m x n).
Proof. exact (MK_COMB (@lem1262787 m) (@lem1262786 x n)). Qed.
Lemma lem1262789 : (@pair nat nat) = (@pair nat nat).
Proof. exact (eq_refl (@pair nat nat)). Qed.
Lemma lem1262790 (m : nat) (x : nadd) (n : nat) : (term14 m x n) = (term15 m x n).
Proof. exact (MK_COMB (@lem1262789) (@lem1262788 m x n)). Qed.
Lemma lem1262791 (x : nadd) (m : nat) : (term11 x m) = (dest_nadd x m).
Proof. exact (eq_refl (term11 x m)). Qed.
Lemma lem1262792 (n : nat) : (Nat.mul n) = (Nat.mul n).
Proof. exact (eq_refl (Nat.mul n)). Qed.
Lemma lem1262793 (n : nat) (x : nadd) (m : nat) : (term12 n x m) = (term13 n x m).
Proof. exact (MK_COMB (@lem1262792 n) (@lem1262791 x m)). Qed.
Lemma lem1262794 (n : nat) (x : nadd) (m : nat) : (term16 n x m) = (term17 n x m).
Proof. exact (MK_COMB (@lem1262790 m x n) (@lem1262793 n x m)). Qed.
Lemma lem1262795 : dist = dist.
Proof. exact (eq_refl dist). Qed.
Lemma lem1262796 (n : nat) (x : nadd) (m : nat) : (term18 n x m) = (term19 n x m).
Proof. exact (MK_COMB (@lem1262795) (@lem1262794 n x m)). Qed.
Lemma lem1262797 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1262798 (n : nat) (x : nadd) (m : nat) : (term20 n x m) = (term21 n x m).
Proof. exact (MK_COMB (@lem1262797) (@lem1262796 n x m)). Qed.
Lemma lem1262799 (B : nat) (m : nat) (n : nat) : (term22 B m n) = (term22 B m n).
Proof. exact (eq_refl (term22 B m n)). Qed.
Lemma lem1262800 (x : nadd) (B : nat) (m : nat) (n : nat) : (term23 x B m n) = (term24 x B m n).
Proof. exact (MK_COMB (@lem1262798 n x m) (@lem1262799 B m n)). Qed.
Lemma lem1262801 (x : nadd) (B : nat) (m : nat) : (term25 x B m) = (term26 x B m).
Proof. exact (fun_ext (fun n : nat => @lem1262800 x B m n)). Qed.
Lemma lem1262802 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1262803 (x : nadd) (B : nat) (m : nat) : (term27 x B m) = (term28 x B m).
Proof. exact (MK_COMB (@lem1262802) (@lem1262801 x B m)). Qed.
Lemma lem1262804 (x : nadd) (B : nat) : (term29 x B) = (term30 x B).
Proof. exact (fun_ext (fun m : nat => @lem1262803 x B m)). Qed.
Lemma lem1262805 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1262806 (x : nadd) (B : nat) : (term31 x B) = (term32 x B).
Proof. exact (MK_COMB (@lem1262805) (@lem1262804 x B)). Qed.
Lemma lem1262807 (x : nadd) : (term33 x) = (term34 x).
Proof. exact (fun_ext (fun B : nat => @lem1262806 x B)). Qed.
Lemma lem1262808 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1262809 (x : nadd) : (term8 x) = (term35 x).
Proof. exact (MK_COMB (@lem1262808) (@lem1262807 x)). Qed.
Lemma lem1262810 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1262811 (x : nadd) : (term36 x) = (term37 x).
Proof. exact (MK_COMB (@lem1262810) (@lem1262809 x)). Qed.
Lemma lem1262812 (x : nadd) : (term9 x) = (term9 x).
Proof. exact (eq_refl (term9 x)). Qed.
Lemma lem1262813 (x : nadd) : ((term8 x) = (term9 x)) = ((term35 x) = (term9 x)).
Proof. exact (MK_COMB (@lem1262811 x) (@lem1262812 x)). Qed.
Lemma lem1262814 (x : nadd) : (term35 x) = (term9 x).
Proof. exact (EQ_MP (@lem1262813 x) (@lem1262785 x)). Qed.
Lemma lem1262816 (r : nat -> nat) : (is_nadd r) = ((term38 r) = r).
Proof. exact (@axiom_20 r). Qed.
Lemma lem1262817 (x : nadd) : (term9 x) = ((term39 x) = (term10 x)).
Proof. exact (@lem1262816 (term10 x)). Qed.
Lemma lem1262820 (x : nadd) : (term35 x) = ((term39 x) = (term10 x)).
Proof. exact (TRANS (@lem1262814 x) (@lem1262817 x)). Qed.
Lemma lem1262821 (t : nat -> nat) : (term40 t) = t.
Proof. exact (@lem1262775 nat nat t). Qed.
Lemma lem1262822 (x : nadd) : (term10 x) = (dest_nadd x).
Proof. exact (@lem1262821 (dest_nadd x)). Qed.
Lemma lem1262823 : mk_nadd = mk_nadd.
Proof. exact (eq_refl mk_nadd). Qed.
Lemma lem1262824 (x : nadd) : (term41 x) = (term42 x).
Proof. exact (MK_COMB (@lem1262823) (@lem1262822 x)). Qed.
Lemma lem1262826 (a : nadd) : (term42 a) = a.
Proof. exact (@axiom_19 a). Qed.
Lemma lem1262827 (x : nadd) : (term42 x) = x.
Proof. exact (@lem1262826 x). Qed.
Lemma lem1262828 (x : nadd) : (term41 x) = x.
Proof. exact (TRANS (@lem1262824 x) (@lem1262827 x)). Qed.
Lemma lem1262829 : dest_nadd = dest_nadd.
Proof. exact (eq_refl dest_nadd). Qed.
Lemma lem1262830 (x : nadd) : (term39 x) = (dest_nadd x).
Proof. exact (MK_COMB (@lem1262829) (@lem1262828 x)). Qed.
Lemma lem1262831 : (@eq (nat -> nat)) = (@eq (nat -> nat)).
Proof. exact (eq_refl (@eq (nat -> nat))). Qed.
Lemma lem1262832 (x : nadd) : (term43 x) = (term44 x).
Proof. exact (MK_COMB (@lem1262831) (@lem1262830 x)). Qed.
Lemma lem1262833 (t : nat -> nat) : (term40 t) = t.
Proof. exact (@lem1262775 nat nat t). Qed.
Lemma lem1262834 (x : nadd) : (term10 x) = (dest_nadd x).
Proof. exact (@lem1262833 (dest_nadd x)). Qed.
Lemma lem1262835 (x : nadd) : ((term39 x) = (term10 x)) = ((dest_nadd x) = (dest_nadd x)).
Proof. exact (MK_COMB (@lem1262832 x) (@lem1262834 x)). Qed.
Lemma lem1262837 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1262838 (x : nat -> nat) : (x = x) = True.
Proof. exact (@lem1262837 (nat -> nat) x). Qed.
Lemma lem1262839 (x : nadd) : ((dest_nadd x) = (dest_nadd x)) = True.
Proof. exact (@lem1262838 (dest_nadd x)). Qed.
Lemma lem1262840 (x : nadd) : ((term39 x) = (term10 x)) = True.
Proof. exact (TRANS (@lem1262835 x) (@lem1262839 x)). Qed.
Lemma lem1262841 (x : nadd) : (term35 x) = True.
Proof. exact (TRANS (@lem1262820 x) (@lem1262840 x)). Qed.
Lemma lem1262842 : term45 = term46.
Proof. exact (fun_ext (fun x : nadd => @lem1262841 x)). Qed.
Lemma lem1262843 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1262844 : term47 = term48.
Proof. exact (MK_COMB (@lem1262843) (@lem1262842)). Qed.
Lemma lem1262846 {A : Type'} (t : Prop) : (term49 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1262847 (t : Prop) : (term50 t) = t.
Proof. exact (@lem1262846 nadd t). Qed.
Lemma lem1262848 : term48 = True.
Proof. exact (@lem1262847 True). Qed.
Lemma lem1262849 : term47 = True.
Proof. exact (TRANS (@lem1262844) (@lem1262848)). Qed.
Lemma lem1262850 : True = term47.
Proof. exact (SYM (@lem1262849)). Qed.
Lemma lem1262851 : term47.
Proof. exact (EQ_MP (@lem1262850) (@lem0)). Qed.
