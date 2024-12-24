Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EVEN_OR_ODD_term_abbrevs.
Require Import DISJ_SYM_spec.
Require Import NOT_EVEN_spec.
Require Import NOT_ODD_spec.
Require Import thm0_spec.
Require Import thm124233_spec.
Require Import thm124616_spec.
Require Import thm1831_spec.
Require Import thm7_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Lemma lem124809 (t1 : Prop) : term0 t1.
Proof. exact (@lem720 t1). Qed.
Lemma lem124810 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem124811 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem124810 t1) (@lem124809 t1)). Qed.
Lemma lem124812 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem124811 t1 t2). Qed.
Lemma lem124813 (t2 : Prop) (t1 : Prop) : (term2 t1 t2) = ((t1 \/ t2) = (t2 \/ t1)).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem124815 (n : nat) : term3 n.
Proof. exact (@lem124808 n). Qed.
Lemma lem124816 (n : nat) : (term3 n) = ((term4 n) = (Coq.Arith.PeanoNat.Nat.Even n)).
Proof. exact (eq_refl (term3 n)). Qed.
Lemma lem124818 (n : nat) : term5 n.
Proof. exact (@lem124715 n). Qed.
Lemma lem124819 (n : nat) : (term5 n) = ((term6 n) = (Coq.Arith.PeanoNat.Nat.Odd n)).
Proof. exact (eq_refl (term5 n)). Qed.
Lemma lem124821 : term7.
Proof. exact (proj2 (@lem124616)). Qed.
Lemma lem124822 (n : nat) : term8 n.
Proof. exact (@lem124821 n). Qed.
Lemma lem124823 (n : nat) : (term8 n) = ((term9 n) = (term4 n)).
Proof. exact (eq_refl (term8 n)). Qed.
Lemma lem124826 : term10.
Proof. exact (proj2 (@lem124233)). Qed.
Lemma lem124827 (n : nat) : term11 n.
Proof. exact (@lem124826 n). Qed.
Lemma lem124828 (n : nat) : (term11 n) = ((term12 n) = (term6 n)).
Proof. exact (eq_refl (term11 n)). Qed.
Lemma lem124832 (P : nat -> Prop) : term13 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem124833 : term14.
Proof. exact (@lem124832 term15). Qed.
Lemma lem124834 : term16 = term17.
Proof. exact (eq_refl term16). Qed.
Lemma lem124835 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem124836 : term18 = term19.
Proof. exact (MK_COMB (@lem124835) (@lem124834)). Qed.
Lemma lem124837 (n : nat) : (term20 n) = (term21 n).
Proof. exact (eq_refl (term20 n)). Qed.
Lemma lem124838 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem124839 (n : nat) : (term22 n) = (term23 n).
Proof. exact (MK_COMB (@lem124838) (@lem124837 n)). Qed.
Lemma lem124840 (n : nat) : (term24 n) = (term25 n).
Proof. exact (eq_refl (term24 n)). Qed.
Lemma lem124841 (n : nat) : (term26 n) = (term27 n).
Proof. exact (MK_COMB (@lem124839 n) (@lem124840 n)). Qed.
Lemma lem124842 : term28 = term29.
Proof. exact (fun_ext (fun n : nat => @lem124841 n)). Qed.
Lemma lem124843 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem124844 : term30 = term31.
Proof. exact (MK_COMB (@lem124843) (@lem124842)). Qed.
Lemma lem124845 : term32 = term33.
Proof. exact (MK_COMB (@lem124836) (@lem124844)). Qed.
Lemma lem124846 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem124847 : term34 = term35.
Proof. exact (MK_COMB (@lem124846) (@lem124845)). Qed.
Lemma lem124848 (n : nat) : (term20 n) = (term21 n).
Proof. exact (eq_refl (term20 n)). Qed.
Lemma lem124849 : term36 = term15.
Proof. exact (fun_ext (fun n : nat => @lem124848 n)). Qed.
Lemma lem124850 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem124851 : term37 = term38.
Proof. exact (MK_COMB (@lem124850) (@lem124849)). Qed.
Lemma lem124852 : term14 = term39.
Proof. exact (MK_COMB (@lem124847) (@lem124851)). Qed.
Lemma lem124853 : term39.
Proof. exact (EQ_MP (@lem124852) (@lem124833)). Qed.
Lemma lem124854 (n : nat) (h1 : term21 n) : term21 n.
Proof. exact (h1). Qed.
Lemma lem124858 : term40 = True.
Proof. exact (proj1 (@lem124233)). Qed.
Lemma lem124859 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem124860 : term41 = (or True).
Proof. exact (MK_COMB (@lem124859) (@lem124858)). Qed.
Lemma lem124862 : term42 = False.
Proof. exact (proj1 (@lem124616)). Qed.
Lemma lem124863 : term17 = (True \/ False).
Proof. exact (MK_COMB (@lem124860) (@lem124862)). Qed.
Lemma lem124865 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem124866 : (True \/ False) = True.
Proof. exact (@lem124865 False). Qed.
Lemma lem124867 : term17 = True.
Proof. exact (TRANS (@lem124863) (@lem124866)). Qed.
Lemma lem124868 : True = term17.
Proof. exact (SYM (@lem124867)). Qed.
Lemma lem124869 : term17.
Proof. exact (EQ_MP (@lem124868) (@lem0)). Qed.
Lemma lem124873 (n : nat) : (term12 n) = (term6 n).
Proof. exact (EQ_MP (@lem124828 n) (@lem124827 n)). Qed.
Lemma lem124875 (n : nat) : (term6 n) = (Coq.Arith.PeanoNat.Nat.Odd n).
Proof. exact (EQ_MP (@lem124819 n) (@lem124818 n)). Qed.
Lemma lem124876 (n : nat) : (term12 n) = (Coq.Arith.PeanoNat.Nat.Odd n).
Proof. exact (TRANS (@lem124873 n) (@lem124875 n)). Qed.
Lemma lem124877 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem124878 (n : nat) : (term43 n) = (term44 n).
Proof. exact (MK_COMB (@lem124877) (@lem124876 n)). Qed.
Lemma lem124880 (n : nat) : (term9 n) = (term4 n).
Proof. exact (EQ_MP (@lem124823 n) (@lem124822 n)). Qed.
Lemma lem124882 (n : nat) : (term4 n) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (EQ_MP (@lem124816 n) (@lem124815 n)). Qed.
Lemma lem124883 (n : nat) : (term9 n) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (TRANS (@lem124880 n) (@lem124882 n)). Qed.
Lemma lem124884 (n : nat) : (term25 n) = (term45 n).
Proof. exact (MK_COMB (@lem124878 n) (@lem124883 n)). Qed.
Lemma lem124887 (n : nat) : (term45 n) = (term25 n).
Proof. exact (SYM (@lem124884 n)). Qed.
Lemma lem124891 (t2 : Prop) (t1 : Prop) : (t1 \/ t2) = (t2 \/ t1).
Proof. exact (EQ_MP (@lem124813 t2 t1) (@lem124812 t1 t2)). Qed.
Lemma lem124892 (n : nat) : (term45 n) = (term21 n).
Proof. exact (@lem124891 (Coq.Arith.PeanoNat.Nat.Even n) (Coq.Arith.PeanoNat.Nat.Odd n)). Qed.
Lemma lem124893 (n : nat) : (term21 n) = (term45 n).
Proof. exact (SYM (@lem124892 n)). Qed.
Lemma lem124894 (n : nat) : (term21 n) = ((term21 n) = True).
Proof. exact (@lem7 (term21 n)). Qed.
Lemma lem124897 (n : nat) (h1 : term21 n) : (term21 n) = True.
Proof. exact (EQ_MP (@lem124894 n) (@lem124854 n h1)). Qed.
Lemma lem124898 (n : nat) (h1 : term21 n) : True = (term21 n).
Proof. exact (SYM (@lem124897 n h1)). Qed.
Lemma lem124899 (n : nat) (h1 : term21 n) : term21 n.
Proof. exact (EQ_MP (@lem124898 n h1) (@lem0)). Qed.
Lemma lem124900 (n : nat) (h1 : term21 n) : term45 n.
Proof. exact (EQ_MP (@lem124893 n) (@lem124899 n h1)). Qed.
Lemma lem124901 (n : nat) (h1 : term21 n) : term25 n.
Proof. exact (EQ_MP (@lem124887 n) (@lem124900 n h1)). Qed.
Lemma lem124902 (n : nat) : term27 n.
Proof. exact (fun h0 : term21 n => @lem124901 n h0). Qed.
Lemma lem124907 : term31.
Proof. exact (fun n : nat => @lem124902 n). Qed.
Lemma lem124908 : term33.
Proof. exact (conj (@lem124869) (@lem124907)). Qed.
Lemma lem124909 : term38.
Proof. exact (@lem124853 (@lem124908)). Qed.
