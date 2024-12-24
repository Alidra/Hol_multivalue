Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NADD_OF_NUM_WELLDEF_term_abbrevs.
Require Import NADD_EQ_REFL_spec.
Lemma lem1268973 (m : nat) (n : nat) (h1 : m = n) : m = n.
Proof. exact (h1). Qed.
Lemma lem1268974 (n : nat) : (term0 n) = (term0 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem1268975 (m : nat) (n : nat) (h1 : m = n) : (term1 n m) = (term2 n).
Proof. exact (MK_COMB (@lem1268974 n) (@lem1268973 m n h1)). Qed.
Lemma lem1268976 (n : nat) : (term2 n) = (term3 n).
Proof. exact (eq_refl (term2 n)). Qed.
Lemma lem1268977 (n : nat) (m : nat) : (term4 n m) = (term4 n m).
Proof. exact (eq_refl (term4 n m)). Qed.
Lemma lem1268978 (m : nat) (n : nat) : ((term1 n m) = (term2 n)) = ((term1 n m) = (term3 n)).
Proof. exact (MK_COMB (@lem1268977 n m) (@lem1268976 n)). Qed.
Lemma lem1268979 (m : nat) (n : nat) : (term1 n m) = (term5 m n).
Proof. exact (eq_refl (term1 n m)). Qed.
Lemma lem1268980 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1268981 (m : nat) (n : nat) : (term4 n m) = (term6 m n).
Proof. exact (MK_COMB (@lem1268980) (@lem1268979 m n)). Qed.
Lemma lem1268982 (n : nat) : (term3 n) = (term3 n).
Proof. exact (eq_refl (term3 n)). Qed.
Lemma lem1268983 (m : nat) (n : nat) : ((term1 n m) = (term3 n)) = ((term5 m n) = (term3 n)).
Proof. exact (MK_COMB (@lem1268981 m n) (@lem1268982 n)). Qed.
Lemma lem1268984 (m : nat) (n : nat) : ((term1 n m) = (term2 n)) = ((term5 m n) = (term3 n)).
Proof. exact (TRANS (@lem1268978 m n) (@lem1268983 m n)). Qed.
Lemma lem1268985 (m : nat) (n : nat) (h1 : m = n) : (term5 m n) = (term3 n).
Proof. exact (EQ_MP (@lem1268984 m n) (@lem1268975 m n h1)). Qed.
Lemma lem1268986 (m : nat) (n : nat) (h1 : m = n) : (term3 n) = (term5 m n).
Proof. exact (SYM (@lem1268985 m n h1)). Qed.
Lemma lem1268987 (x : nadd) : term7 x.
Proof. exact (@lem1267990 x). Qed.
Lemma lem1268988 (x : nadd) : (term7 x) = (nadd_eq x x).
Proof. exact (eq_refl (term7 x)). Qed.
Lemma lem1268991 (x : nadd) : nadd_eq x x.
Proof. exact (EQ_MP (@lem1268988 x) (@lem1268987 x)). Qed.
Lemma lem1268992 (n : nat) : term3 n.
Proof. exact (@lem1268991 (nadd_of_num n)). Qed.
Lemma lem1268993 (m : nat) (n : nat) (h1 : m = n) : term5 m n.
Proof. exact (EQ_MP (@lem1268986 m n h1) (@lem1268992 n)). Qed.
Lemma lem1268994 (m : nat) (n : nat) : term8 m n.
Proof. exact (fun h0 : m = n => @lem1268993 m n h0). Qed.
Lemma lem1268999 (m : nat) : term9 m.
Proof. exact (fun n : nat => @lem1268994 m n). Qed.
Lemma lem1269004 : term10.
Proof. exact (fun m : nat => @lem1268999 m). Qed.
