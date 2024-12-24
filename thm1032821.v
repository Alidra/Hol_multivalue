Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1032821_term_abbrevs.
Require Import DIVMOD_ELIM_THM_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Lemma lem1032789 (q : nat) (r : nat) (m : nat) : (term0 q r m) = (term1 q r m).
Proof. exact (@lem17045 (q = (NUMERAL 0)) (r = m)). Qed.
Lemma lem1032791 (n : nat) : (term2 n) = (term2 n).
Proof. exact (eq_refl (term2 n)). Qed.
Lemma lem1032792 (n : nat) (q : nat) (r : nat) (m : nat) : (term3 n q r m) = (term4 n q r m).
Proof. exact (MK_COMB (@lem1032791 n) (@lem1032789 q r m)). Qed.
Lemma lem1032793 (n : nat) (q : nat) (r : nat) (m : nat) : (term5 n q r m) = (term3 n q r m).
Proof. exact (@lem17045 (n = (NUMERAL 0)) (term6 q r m)). Qed.
Lemma lem1032794 (n : nat) (q : nat) (r : nat) (m : nat) : (term5 n q r m) = (term4 n q r m).
Proof. exact (TRANS (@lem1032793 n q r m) (@lem1032792 n q r m)). Qed.
Lemma lem1032801 (m : nat) (q : nat) (r : nat) (n : nat) : (term7 m q r n) = (term8 m q r n).
Proof. exact (@lem17045 (m = (term9 q n r)) (Peano.lt r n)). Qed.
Lemma lem1032802 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1032803 (n : nat) (q : nat) (r : nat) (m : nat) : (term10 n q r m) = (term11 n q r m).
Proof. exact (MK_COMB (@lem1032802) (@lem1032794 n q r m)). Qed.
Lemma lem1032804 (m : nat) (q : nat) (r : nat) (n : nat) : (term12 m q r n) = (term13 m q r n).
Proof. exact (MK_COMB (@lem1032803 n q r m) (@lem1032801 m q r n)). Qed.
Lemma lem1032805 (m : nat) (q : nat) (r : nat) (n : nat) : (term14 m q r n) = (term12 m q r n).
Proof. exact (@lem17160 (term15 n q r m) (term16 m q r n)). Qed.
Lemma lem1032806 (m : nat) (q : nat) (r : nat) (n : nat) : (term14 m q r n) = (term13 m q r n).
Proof. exact (TRANS (@lem1032805 m q r n) (@lem1032804 m q r n)). Qed.
Lemma lem1032807 (P : type1605) (q : nat) (r : nat) : (P q r) = (P q r).
Proof. exact (eq_refl (P q r)). Qed.
Lemma lem1032808 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1032809 (m : nat) (q : nat) (r : nat) (n : nat) : (term17 m q r n) = (term18 m q r n).
Proof. exact (MK_COMB (@lem1032808) (@lem1032806 m q r n)). Qed.
Lemma lem1032810 (m : nat) (n : nat) (P : type1605) (q : nat) (r : nat) : (term19 m n P q r) = (term20 m n P q r).
Proof. exact (MK_COMB (@lem1032809 m q r n) (@lem1032807 P q r)). Qed.
Lemma lem1032811 (m : nat) (n : nat) (P : type1605) (q : nat) (r : nat) : (term21 m n P q r) = (term19 m n P q r).
Proof. exact (@lem17265 (term22 m q r n) (P q r)). Qed.
Lemma lem1032812 (m : nat) (n : nat) (P : type1605) (q : nat) (r : nat) : (term21 m n P q r) = (term20 m n P q r).
Proof. exact (TRANS (@lem1032811 m n P q r) (@lem1032810 m n P q r)). Qed.
Lemma lem1032813 (m : nat) (n : nat) (P : type1605) (q : nat) : (term23 m n P q) = (term24 m n P q).
Proof. exact (fun_ext (fun r : nat => @lem1032812 m n P q r)). Qed.
Lemma lem1032814 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1032815 (m : nat) (n : nat) (P : type1605) (q : nat) : (term25 m n P q) = (term26 m n P q).
Proof. exact (MK_COMB (@lem1032814) (@lem1032813 m n P q)). Qed.
Lemma lem1032816 (m : nat) (n : nat) (P : type1605) : (term27 m n P) = (term28 m n P).
Proof. exact (fun_ext (fun q : nat => @lem1032815 m n P q)). Qed.
Lemma lem1032817 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1032818 (m : nat) (n : nat) (P : type1605) : (term29 m n P) = (term30 m n P).
Proof. exact (MK_COMB (@lem1032817) (@lem1032816 m n P)). Qed.
Lemma lem1032819 (P : type1605) (m : nat) (n : nat) : (term31 P m n) = (term31 P m n).
Proof. exact (eq_refl (term31 P m n)). Qed.
Lemma lem1032820 (m : nat) (n : nat) (P : type1605) : ((term32 P m n) = (term29 m n P)) = ((term32 P m n) = (term30 m n P)).
Proof. exact (MK_COMB (@lem1032819 P m n) (@lem1032818 m n P)). Qed.
Lemma lem1032821 (m : nat) (n : nat) (P : type1605) : (term32 P m n) = (term30 m n P).
Proof. exact (EQ_MP (@lem1032820 m n P) (@lem265011 m n P)). Qed.
