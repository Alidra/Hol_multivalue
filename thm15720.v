Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm15720_term_abbrevs.
Require Import EXISTS_ONE_REP_spec.
Require Import thm9261_spec.
Require Import thm9306_spec.
Lemma lem15714 {A : Type'} : (@ex A) = (term0 A).
Proof. exact (@lem9261 A (@lem9306 A)). Qed.
Lemma lem15715 : (@ex Prop) = term1.
Proof. exact (@lem15714 Prop). Qed.
Lemma lem15716 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem15717 : term3 = term4.
Proof. exact (MK_COMB (@lem15715) (@lem15716)). Qed.
Lemma lem15718 : term4 = term5.
Proof. exact (eq_refl term4). Qed.
Lemma lem15719 : term3 = term5.
Proof. exact (TRANS (@lem15717) (@lem15718)). Qed.
Lemma lem15720 : term5.
Proof. exact (EQ_MP (@lem15719) (@lem15712)). Qed.
