Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import real_sgn_term_abbrevs.
Lemma lem1710125 : real_sgn = term0.
Proof. exact (@real_sgn_def). Qed.
Lemma lem1710126 (_26471 : real) : _26471 = _26471.
Proof. exact (eq_refl _26471). Qed.
Lemma lem1710127 (_26471 : real) : (real_sgn _26471) = (term1 _26471).
Proof. exact (MK_COMB (@lem1710125) (@lem1710126 _26471)). Qed.
Lemma lem1710128 (_26471 : real) : (term1 _26471) = (term2 _26471).
Proof. exact (eq_refl (term1 _26471)). Qed.
Lemma lem1710129 (_26471 : real) : (real_sgn _26471) = (term2 _26471).
Proof. exact (TRANS (@lem1710127 _26471) (@lem1710128 _26471)). Qed.
Lemma lem1710130 : term3.
Proof. exact (fun _26471 : real => @lem1710129 _26471). Qed.
Lemma lem1710131 (_26471 : real) : term4 _26471.
Proof. exact (@lem1710130 _26471). Qed.
Lemma lem1710132 (_26471 : real) : (term4 _26471) = ((real_sgn _26471) = (term2 _26471)).
Proof. exact (eq_refl (term4 _26471)). Qed.
Lemma lem1710133 (_26471 : real) : (real_sgn _26471) = (term2 _26471).
Proof. exact (EQ_MP (@lem1710132 _26471) (@lem1710131 _26471)). Qed.
Lemma lem1710163 (x : real) : (real_sgn x) = (term2 x).
Proof. exact (@lem1710133 x). Qed.
Lemma lem1710164 : term3.
Proof. exact (fun x : real => @lem1710163 x). Qed.
