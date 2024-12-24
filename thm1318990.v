Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1318990_term_abbrevs.
Require Import NADD_OF_NUM_MUL_spec.
Require Import thm1317782_spec.
Require Import thm1317787_spec.
Require Import thm1318030_spec.
Require Import thm1318035_spec.
Require Import thm1318766_spec.
Require Import thm1318767_spec.
Lemma lem1318947 (x : nadd) (y : nadd) : (nadd_eq x y) = ((term0 x) = (term0 y)).
Proof. exact (EQ_MP (@lem1318767 x y) (@lem1318766 x y)). Qed.
Lemma lem1318948 (m : nat) (n : nat) : (term1 m n) = ((term2 m n) = (term3 m n)).
Proof. exact (@lem1318947 (term4 m n) (term5 m n)). Qed.
Lemma lem1318952 (x : nadd) (y : nadd) : (term6 x y) = (term7 x y).
Proof. exact (EQ_MP (@lem1318035 x y) (@lem1318030 x y)). Qed.
Lemma lem1318953 (m : nat) (n : nat) : (term2 m n) = (term8 m n).
Proof. exact (@lem1318952 (nadd_of_num m) (nadd_of_num n)). Qed.
Lemma lem1318955 (m : nat) : (term9 m) = (hreal_of_num m).
Proof. exact (EQ_MP (@lem1317787 m) (@lem1317782 m)). Qed.
Lemma lem1318956 : hreal_mul = hreal_mul.
Proof. exact (eq_refl hreal_mul). Qed.
Lemma lem1318957 (m : nat) : (term10 m) = (term11 m).
Proof. exact (MK_COMB (@lem1318956) (@lem1318955 m)). Qed.
Lemma lem1318959 (m : nat) : (term9 m) = (hreal_of_num m).
Proof. exact (EQ_MP (@lem1317787 m) (@lem1317782 m)). Qed.
Lemma lem1318960 (n : nat) : (term9 n) = (hreal_of_num n).
Proof. exact (@lem1318959 n). Qed.
Lemma lem1318961 (m : nat) (n : nat) : (term8 m n) = (term12 m n).
Proof. exact (MK_COMB (@lem1318957 m) (@lem1318960 n)). Qed.
Lemma lem1318962 (m : nat) (n : nat) : (term2 m n) = (term12 m n).
Proof. exact (TRANS (@lem1318953 m n) (@lem1318961 m n)). Qed.
Lemma lem1318963 : (@eq hreal) = (@eq hreal).
Proof. exact (eq_refl (@eq hreal)). Qed.
Lemma lem1318964 (m : nat) (n : nat) : (term13 m n) = (term14 m n).
Proof. exact (MK_COMB (@lem1318963) (@lem1318962 m n)). Qed.
Lemma lem1318966 (m : nat) : (term9 m) = (hreal_of_num m).
Proof. exact (EQ_MP (@lem1317787 m) (@lem1317782 m)). Qed.
Lemma lem1318967 (m : nat) (n : nat) : (term3 m n) = (term15 m n).
Proof. exact (@lem1318966 (Nat.mul m n)). Qed.
Lemma lem1318968 (m : nat) (n : nat) : ((term2 m n) = (term3 m n)) = ((term12 m n) = (term15 m n)).
Proof. exact (MK_COMB (@lem1318964 m n) (@lem1318967 m n)). Qed.
Lemma lem1318971 (m : nat) (n : nat) : (term1 m n) = ((term12 m n) = (term15 m n)).
Proof. exact (TRANS (@lem1318948 m n) (@lem1318968 m n)). Qed.
Lemma lem1318972 (m : nat) : (term16 m) = (term17 m).
Proof. exact (fun_ext (fun n : nat => @lem1318971 m n)). Qed.
Lemma lem1318973 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1318974 (m : nat) : (term18 m) = (term19 m).
Proof. exact (MK_COMB (@lem1318973) (@lem1318972 m)). Qed.
Lemma lem1318981 : term20 = term21.
Proof. exact (fun_ext (fun m : nat => @lem1318974 m)). Qed.
Lemma lem1318982 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1318983 : term22 = term23.
Proof. exact (MK_COMB (@lem1318982) (@lem1318981)). Qed.
Lemma lem1318990 : term23.
Proof. exact (EQ_MP (@lem1318983) (@lem1279539)). Qed.
