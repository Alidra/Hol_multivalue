Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import inf_term_abbrevs.
Lemma lem5204194 : inf = term0.
Proof. exact (@inf_def). Qed.
Lemma lem5204195 (_67904 : real -> Prop) : _67904 = _67904.
Proof. exact (eq_refl _67904). Qed.
Lemma lem5204196 (_67904 : real -> Prop) : (inf _67904) = (term1 _67904).
Proof. exact (MK_COMB (@lem5204194) (@lem5204195 _67904)). Qed.
Lemma lem5204197 (_67904 : real -> Prop) : (term1 _67904) = (term2 _67904).
Proof. exact (eq_refl (term1 _67904)). Qed.
Lemma lem5204198 (_67904 : real -> Prop) : (inf _67904) = (term2 _67904).
Proof. exact (TRANS (@lem5204196 _67904) (@lem5204197 _67904)). Qed.
Lemma lem5204199 : term3.
Proof. exact (fun _67904 : real -> Prop => @lem5204198 _67904). Qed.
Lemma lem5204200 (_67904 : real -> Prop) : term4 _67904.
Proof. exact (@lem5204199 _67904). Qed.
Lemma lem5204201 (_67904 : real -> Prop) : (term4 _67904) = ((inf _67904) = (term2 _67904)).
Proof. exact (eq_refl (term4 _67904)). Qed.
Lemma lem5204202 (_67904 : real -> Prop) : (inf _67904) = (term2 _67904).
Proof. exact (EQ_MP (@lem5204201 _67904) (@lem5204200 _67904)). Qed.
Lemma lem5204232 (s : real -> Prop) : (inf s) = (term2 s).
Proof. exact (@lem5204202 s). Qed.
Lemma lem5204233 : term3.
Proof. exact (fun s : real -> Prop => @lem5204232 s). Qed.
