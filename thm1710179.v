Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1710179_term_abbrevs.
Require Import real_sgn_spec.
Lemma lem1710165 (x : real) : term0 x.
Proof. exact (@lem1710164 x). Qed.
Lemma lem1710166 (x : real) : (term0 x) = ((real_sgn x) = (term1 x)).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1710171 (x : real) : (real_sgn x) = (term1 x).
Proof. exact (EQ_MP (@lem1710166 x) (@lem1710165 x)). Qed.
Lemma lem1710172 : term2 = term3.
Proof. exact (@lem1710171 term4). Qed.
Lemma lem1710173 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1710174 : term5 = term6.
Proof. exact (MK_COMB (@lem1710173) (@lem1710172)). Qed.
Lemma lem1710175 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1710176 : (term2 = term4) = (term3 = term4).
Proof. exact (MK_COMB (@lem1710174) (@lem1710175)). Qed.
Lemma lem1710179 : (term3 = term4) = (term2 = term4).
Proof. exact (SYM (@lem1710176)). Qed.
