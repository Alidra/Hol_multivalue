Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIST_SYM_term_abbrevs.
Require Import ADD_SYM_spec.
Require Import dist_spec.
Lemma lem1244937 (n : nat) : term0 n.
Proof. exact (@lem1244710 n). Qed.
Lemma lem1244938 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem1244939 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem1244938 n) (@lem1244937 n)). Qed.
Lemma lem1244940 (n : nat) (m : nat) : term2 n m.
Proof. exact (@lem1244939 n m). Qed.
Lemma lem1244941 (n : nat) (m : nat) : (term2 n m) = ((term3 m n) = (term4 n m)).
Proof. exact (eq_refl (term2 n m)). Qed.
Lemma lem1244954 (n : nat) (m : nat) : (term3 m n) = (term4 n m).
Proof. exact (EQ_MP (@lem1244941 n m) (@lem1244940 n m)). Qed.
Lemma lem1244955 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1244956 (n : nat) (m : nat) : (term5 m n) = (term6 n m).
Proof. exact (MK_COMB (@lem1244955) (@lem1244954 n m)). Qed.
Lemma lem1244958 (n : nat) (m : nat) : (term3 m n) = (term4 n m).
Proof. exact (EQ_MP (@lem1244941 n m) (@lem1244940 n m)). Qed.
Lemma lem1244959 (m : nat) (n : nat) : (term3 n m) = (term4 m n).
Proof. exact (@lem1244958 m n). Qed.
Lemma lem1244960 (m : nat) (n : nat) : ((term3 m n) = (term3 n m)) = ((term4 n m) = (term4 m n)).
Proof. exact (MK_COMB (@lem1244956 n m) (@lem1244959 m n)). Qed.
Lemma lem1244963 (m : nat) : (term7 m) = (term8 m).
Proof. exact (fun_ext (fun n : nat => @lem1244960 m n)). Qed.
Lemma lem1244964 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1244965 (m : nat) : (term9 m) = (term10 m).
Proof. exact (MK_COMB (@lem1244964) (@lem1244963 m)). Qed.
Lemma lem1244970 : term11 = term12.
Proof. exact (fun_ext (fun m : nat => @lem1244965 m)). Qed.
Lemma lem1244971 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1244972 : term13 = term14.
Proof. exact (MK_COMB (@lem1244971) (@lem1244970)). Qed.
Lemma lem1244977 : term14 = term13.
Proof. exact (SYM (@lem1244972)). Qed.
Lemma lem1244978 (m : nat) : term15 m.
Proof. exact (@lem77775 m). Qed.
Lemma lem1244979 (m : nat) : (term15 m) = (term16 m).
Proof. exact (eq_refl (term15 m)). Qed.
Lemma lem1244980 (m : nat) : term16 m.
Proof. exact (EQ_MP (@lem1244979 m) (@lem1244978 m)). Qed.
Lemma lem1244981 (m : nat) (n : nat) : term17 m n.
Proof. exact (@lem1244980 m n). Qed.
Lemma lem1244982 (n : nat) (m : nat) : (term17 m n) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl (term17 m n)). Qed.
Lemma lem1244985 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (EQ_MP (@lem1244982 n m) (@lem1244981 m n)). Qed.
Lemma lem1244986 (m : nat) (n : nat) : (term4 n m) = (term4 m n).
Proof. exact (@lem1244985 (Nat.sub n m) (Nat.sub m n)). Qed.
Lemma lem1244991 (m : nat) : term10 m.
Proof. exact (fun n : nat => @lem1244986 m n). Qed.
Lemma lem1244996 : term14.
Proof. exact (fun m : nat => @lem1244991 m). Qed.
Lemma lem1244997 : term13.
Proof. exact (EQ_MP (@lem1244977) (@lem1244996)). Qed.
