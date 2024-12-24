Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1318933_term_abbrevs.
Require Import NADD_OF_NUM_ADD_spec.
Require Import thm1317782_spec.
Require Import thm1317787_spec.
Require Import thm1317906_spec.
Require Import thm1317911_spec.
Require Import thm1318766_spec.
Require Import thm1318767_spec.
Lemma lem1318890 (x : nadd) (y : nadd) : (nadd_eq x y) = ((term0 x) = (term0 y)).
Proof. exact (EQ_MP (@lem1318767 x y) (@lem1318766 x y)). Qed.
Lemma lem1318891 (m : nat) (n : nat) : (term1 m n) = ((term2 m n) = (term3 m n)).
Proof. exact (@lem1318890 (term4 m n) (term5 m n)). Qed.
Lemma lem1318895 (x : nadd) (y : nadd) : (term6 x y) = (term7 x y).
Proof. exact (EQ_MP (@lem1317911 x y) (@lem1317906 x y)). Qed.
Lemma lem1318896 (m : nat) (n : nat) : (term2 m n) = (term8 m n).
Proof. exact (@lem1318895 (nadd_of_num m) (nadd_of_num n)). Qed.
Lemma lem1318898 (m : nat) : (term9 m) = (hreal_of_num m).
Proof. exact (EQ_MP (@lem1317787 m) (@lem1317782 m)). Qed.
Lemma lem1318899 : hreal_add = hreal_add.
Proof. exact (eq_refl hreal_add). Qed.
Lemma lem1318900 (m : nat) : (term10 m) = (term11 m).
Proof. exact (MK_COMB (@lem1318899) (@lem1318898 m)). Qed.
Lemma lem1318902 (m : nat) : (term9 m) = (hreal_of_num m).
Proof. exact (EQ_MP (@lem1317787 m) (@lem1317782 m)). Qed.
Lemma lem1318903 (n : nat) : (term9 n) = (hreal_of_num n).
Proof. exact (@lem1318902 n). Qed.
Lemma lem1318904 (m : nat) (n : nat) : (term8 m n) = (term12 m n).
Proof. exact (MK_COMB (@lem1318900 m) (@lem1318903 n)). Qed.
Lemma lem1318905 (m : nat) (n : nat) : (term2 m n) = (term12 m n).
Proof. exact (TRANS (@lem1318896 m n) (@lem1318904 m n)). Qed.
Lemma lem1318906 : (@eq hreal) = (@eq hreal).
Proof. exact (eq_refl (@eq hreal)). Qed.
Lemma lem1318907 (m : nat) (n : nat) : (term13 m n) = (term14 m n).
Proof. exact (MK_COMB (@lem1318906) (@lem1318905 m n)). Qed.
Lemma lem1318909 (m : nat) : (term9 m) = (hreal_of_num m).
Proof. exact (EQ_MP (@lem1317787 m) (@lem1317782 m)). Qed.
Lemma lem1318910 (m : nat) (n : nat) : (term3 m n) = (term15 m n).
Proof. exact (@lem1318909 (Nat.add m n)). Qed.
Lemma lem1318911 (m : nat) (n : nat) : ((term2 m n) = (term3 m n)) = ((term12 m n) = (term15 m n)).
Proof. exact (MK_COMB (@lem1318907 m n) (@lem1318910 m n)). Qed.
Lemma lem1318914 (m : nat) (n : nat) : (term1 m n) = ((term12 m n) = (term15 m n)).
Proof. exact (TRANS (@lem1318891 m n) (@lem1318911 m n)). Qed.
Lemma lem1318915 (m : nat) : (term16 m) = (term17 m).
Proof. exact (fun_ext (fun n : nat => @lem1318914 m n)). Qed.
Lemma lem1318916 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1318917 (m : nat) : (term18 m) = (term19 m).
Proof. exact (MK_COMB (@lem1318916) (@lem1318915 m)). Qed.
Lemma lem1318924 : term20 = term21.
Proof. exact (fun_ext (fun m : nat => @lem1318917 m)). Qed.
Lemma lem1318925 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1318926 : term22 = term23.
Proof. exact (MK_COMB (@lem1318925) (@lem1318924)). Qed.
Lemma lem1318933 : term23.
Proof. exact (EQ_MP (@lem1318926) (@lem1276280)). Qed.
