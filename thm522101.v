Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm522101_term_abbrevs.
Require Import ADD_ASSOC_spec.
Lemma lem522080 (m : nat) (n : nat) (p : nat) (h1 : (term0 m n p) = (term1 m n p)) : (term0 m n p) = (term1 m n p).
Proof. exact (h1). Qed.
Lemma lem522081 (m : nat) (n : nat) (p : nat) (h1 : (term0 m n p) = (term1 m n p)) : (term1 m n p) = (term0 m n p).
Proof. exact (SYM (@lem522080 m n p h1)). Qed.
Lemma lem522082 (m : nat) (n : nat) (p : nat) (h1 : (term1 m n p) = (term0 m n p)) : (term1 m n p) = (term0 m n p).
Proof. exact (h1). Qed.
Lemma lem522083 (m : nat) (n : nat) (p : nat) (h1 : (term1 m n p) = (term0 m n p)) : (term0 m n p) = (term1 m n p).
Proof. exact (SYM (@lem522082 m n p h1)). Qed.
Lemma lem522084 (m : nat) (n : nat) (p : nat) : ((term0 m n p) = (term1 m n p)) = ((term1 m n p) = (term0 m n p)).
Proof. exact (prop_ext (fun h1 : (term0 m n p) = (term1 m n p) => @lem522081 m n p h1) (fun h1 : (term1 m n p) = (term0 m n p) => @lem522083 m n p h1)). Qed.
Lemma lem522085 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (fun_ext (fun p : nat => @lem522084 m n p)). Qed.
Lemma lem522086 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem522087 (m : nat) (n : nat) : (term4 m n) = (term5 m n).
Proof. exact (MK_COMB (@lem522086) (@lem522085 m n)). Qed.
Lemma lem522088 (m : nat) : (term6 m) = (term7 m).
Proof. exact (fun_ext (fun n : nat => @lem522087 m n)). Qed.
Lemma lem522089 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem522090 (m : nat) : (term8 m) = (term9 m).
Proof. exact (MK_COMB (@lem522089) (@lem522088 m)). Qed.
Lemma lem522091 : term10 = term11.
Proof. exact (fun_ext (fun m : nat => @lem522090 m)). Qed.
Lemma lem522092 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem522093 : term12 = term13.
Proof. exact (MK_COMB (@lem522092) (@lem522091)). Qed.
Lemma lem522094 : term13.
Proof. exact (EQ_MP (@lem522093) (@lem77960)). Qed.
Lemma lem522095 (m : nat) : term14 m.
Proof. exact (@lem522094 m). Qed.
Lemma lem522096 (m : nat) : (term14 m) = (term9 m).
Proof. exact (eq_refl (term14 m)). Qed.
Lemma lem522097 (m : nat) : term9 m.
Proof. exact (EQ_MP (@lem522096 m) (@lem522095 m)). Qed.
Lemma lem522098 (m : nat) (n : nat) : term15 m n.
Proof. exact (@lem522097 m n). Qed.
Lemma lem522099 (m : nat) (n : nat) : (term15 m n) = (term5 m n).
Proof. exact (eq_refl (term15 m n)). Qed.
Lemma lem522100 (m : nat) (n : nat) : term5 m n.
Proof. exact (EQ_MP (@lem522099 m n) (@lem522098 m n)). Qed.
Lemma lem522101 (m : nat) (n : nat) (p : nat) : term16 m n p.
Proof. exact (@lem522100 m n p). Qed.
