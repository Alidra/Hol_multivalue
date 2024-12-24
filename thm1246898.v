Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1246898_term_abbrevs.
Require Import NOT_LT_spec.
Lemma lem1246887 (n : nat) (m : nat) (h1 : (term0 m n) = (Peano.le n m)) : (term0 m n) = (Peano.le n m).
Proof. exact (h1). Qed.
Lemma lem1246888 (n : nat) (m : nat) (h1 : (term0 m n) = (Peano.le n m)) : (Peano.le n m) = (term0 m n).
Proof. exact (SYM (@lem1246887 n m h1)). Qed.
Lemma lem1246889 (m : nat) (n : nat) (h1 : (Peano.le n m) = (term0 m n)) : (Peano.le n m) = (term0 m n).
Proof. exact (h1). Qed.
Lemma lem1246890 (m : nat) (n : nat) (h1 : (Peano.le n m) = (term0 m n)) : (term0 m n) = (Peano.le n m).
Proof. exact (SYM (@lem1246889 m n h1)). Qed.
Lemma lem1246891 (m : nat) (n : nat) : ((term0 m n) = (Peano.le n m)) = ((Peano.le n m) = (term0 m n)).
Proof. exact (prop_ext (fun h1 : (term0 m n) = (Peano.le n m) => @lem1246888 n m h1) (fun h1 : (Peano.le n m) = (term0 m n) => @lem1246890 m n h1)). Qed.
Lemma lem1246892 (m : nat) : (term1 m) = (term2 m).
Proof. exact (fun_ext (fun n : nat => @lem1246891 m n)). Qed.
Lemma lem1246893 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1246894 (m : nat) : (term3 m) = (term4 m).
Proof. exact (MK_COMB (@lem1246893) (@lem1246892 m)). Qed.
Lemma lem1246895 : term5 = term6.
Proof. exact (fun_ext (fun m : nat => @lem1246894 m)). Qed.
Lemma lem1246896 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1246897 : term7 = term8.
Proof. exact (MK_COMB (@lem1246896) (@lem1246895)). Qed.
Lemma lem1246898 : term8.
Proof. exact (EQ_MP (@lem1246897) (@lem98377)). Qed.
