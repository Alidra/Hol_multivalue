Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NADD_EQ_SYM_term_abbrevs.
Require Import DIST_SYM_spec.
Require Import nadd_eq_spec.
Lemma lem1267991 (m : nat) : term0 m.
Proof. exact (@lem1244997 m). Qed.
Lemma lem1267992 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem1267993 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem1267992 m) (@lem1267991 m)). Qed.
Lemma lem1267994 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem1267993 m n). Qed.
Lemma lem1267995 (n : nat) (m : nat) : (term2 m n) = ((term3 m n) = (term3 n m)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem1267997 (x : nadd) : term4 x.
Proof. exact (@lem1267930 x). Qed.
Lemma lem1267998 (x : nadd) : (term4 x) = (term5 x).
Proof. exact (eq_refl (term4 x)). Qed.
Lemma lem1267999 (x : nadd) : term5 x.
Proof. exact (EQ_MP (@lem1267998 x) (@lem1267997 x)). Qed.
Lemma lem1268000 (x : nadd) (y : nadd) : term6 x y.
Proof. exact (@lem1267999 x y). Qed.
Lemma lem1268001 (x : nadd) (y : nadd) : (term6 x y) = ((nadd_eq x y) = (term7 x y)).
Proof. exact (eq_refl (term6 x y)). Qed.
Lemma lem1268006 (x : nadd) (y : nadd) : (nadd_eq x y) = (term7 x y).
Proof. exact (EQ_MP (@lem1268001 x y) (@lem1268000 x y)). Qed.
Lemma lem1268015 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1268016 (x : nadd) (y : nadd) : (term8 x y) = (term9 x y).
Proof. exact (MK_COMB (@lem1268015) (@lem1268006 x y)). Qed.
Lemma lem1268018 (x : nadd) (y : nadd) : (nadd_eq x y) = (term7 x y).
Proof. exact (EQ_MP (@lem1268001 x y) (@lem1268000 x y)). Qed.
Lemma lem1268019 (y : nadd) (x : nadd) : (nadd_eq y x) = (term7 y x).
Proof. exact (@lem1268018 y x). Qed.
Lemma lem1268028 (y : nadd) (x : nadd) : ((nadd_eq x y) = (nadd_eq y x)) = ((term7 x y) = (term7 y x)).
Proof. exact (MK_COMB (@lem1268016 x y) (@lem1268019 y x)). Qed.
Lemma lem1268031 (y : nadd) (x : nadd) : ((term7 x y) = (term7 y x)) = ((nadd_eq x y) = (nadd_eq y x)).
Proof. exact (SYM (@lem1268028 y x)). Qed.
Lemma lem1268033 (n : nat) (m : nat) : (term3 m n) = (term3 n m).
Proof. exact (EQ_MP (@lem1267995 n m) (@lem1267994 m n)). Qed.
Lemma lem1268034 (x : nadd) (y : nadd) (n : nat) : (term10 y x n) = (term10 x y n).
Proof. exact (@lem1268033 (dest_nadd x n) (dest_nadd y n)). Qed.
Lemma lem1268035 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1268036 (x : nadd) (y : nadd) (n : nat) : (term11 y x n) = (term11 x y n).
Proof. exact (MK_COMB (@lem1268035) (@lem1268034 x y n)). Qed.
Lemma lem1268037 (B : nat) : B = B.
Proof. exact (eq_refl B). Qed.
Lemma lem1268038 (x : nadd) (y : nadd) (n : nat) (B : nat) : (term12 y x n B) = (term12 x y n B).
Proof. exact (MK_COMB (@lem1268036 x y n) (@lem1268037 B)). Qed.
Lemma lem1268039 (x : nadd) (y : nadd) (B : nat) : (term13 y x B) = (term13 x y B).
Proof. exact (fun_ext (fun n : nat => @lem1268038 x y n B)). Qed.
Lemma lem1268040 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1268041 (x : nadd) (y : nadd) (B : nat) : (term14 y x B) = (term14 x y B).
Proof. exact (MK_COMB (@lem1268040) (@lem1268039 x y B)). Qed.
Lemma lem1268042 (x : nadd) (y : nadd) : (term15 y x) = (term15 x y).
Proof. exact (fun_ext (fun B : nat => @lem1268041 x y B)). Qed.
Lemma lem1268043 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1268044 (x : nadd) (y : nadd) : (term7 y x) = (term7 x y).
Proof. exact (MK_COMB (@lem1268043) (@lem1268042 x y)). Qed.
Lemma lem1268045 (x : nadd) (y : nadd) : (term9 x y) = (term9 x y).
Proof. exact (eq_refl (term9 x y)). Qed.
Lemma lem1268046 (x : nadd) (y : nadd) : ((term7 x y) = (term7 y x)) = ((term7 x y) = (term7 x y)).
Proof. exact (MK_COMB (@lem1268045 x y) (@lem1268044 x y)). Qed.
Lemma lem1268047 (y : nadd) (x : nadd) : ((term7 x y) = (term7 x y)) = ((term7 x y) = (term7 y x)).
Proof. exact (SYM (@lem1268046 x y)). Qed.
Lemma lem1268048 (x : nadd) (y : nadd) : (term7 x y) = (term7 x y).
Proof. exact (eq_refl (term7 x y)). Qed.
Lemma lem1268049 (y : nadd) (x : nadd) : (term7 x y) = (term7 y x).
Proof. exact (EQ_MP (@lem1268047 y x) (@lem1268048 x y)). Qed.
Lemma lem1268050 (y : nadd) (x : nadd) : (nadd_eq x y) = (nadd_eq y x).
Proof. exact (EQ_MP (@lem1268031 y x) (@lem1268049 y x)). Qed.
Lemma lem1268055 (x : nadd) : term16 x.
Proof. exact (fun y : nadd => @lem1268050 y x). Qed.
Lemma lem1268060 : term17.
Proof. exact (fun x : nadd => @lem1268055 x). Qed.
