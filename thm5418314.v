Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm5418314_term_abbrevs.
Require Import thm5400807_spec.
Require Import thm5400808_spec.
Require Import thm5400825_spec.
Require Import thm5400898_spec.
Require Import thm5400903_spec.
Require Import thm5418289_spec.
Require Import thm5418290_spec.
Lemma lem5418305 (m : nat) (h1 : term0 m) : (term1 m) = (@EMPTY nat).
Proof. exact (EQ_MP (@lem5400903 m) (@lem5418289 m h1)). Qed.
Lemma lem5418306 (m : nat) (h1 : term0 m) : (term0 m) = ((term1 m) = (@EMPTY nat)).
Proof. exact (prop_ext (fun h2 : term0 m => @lem5418305 m h1) (fun h2 : (term1 m) = (@EMPTY nat) => @lem5400825 m h1)). Qed.
Lemma lem5418307 (m : nat) (h1 : term0 m) : (term1 m) = (@EMPTY nat).
Proof. exact (EQ_MP (@lem5418306 m h1) (@lem5400825 m h1)). Qed.
Lemma lem5418308 (m : nat) : term2 m.
Proof. exact (fun h0 : term0 m => @lem5418307 m h0). Qed.
Lemma lem5418309 (m : nat) (h1 : m = (NUMERAL 0)) : (term1 m) = term3.
Proof. exact (EQ_MP (@lem5400898 m) (@lem5418290 m h1)). Qed.
Lemma lem5418310 (m : nat) (h1 : m = (NUMERAL 0)) : (m = (NUMERAL 0)) = ((term1 m) = term3).
Proof. exact (prop_ext (fun h2 : m = (NUMERAL 0) => @lem5418309 m h1) (fun h2 : (term1 m) = term3 => @lem5400808 m h1)). Qed.
Lemma lem5418311 (m : nat) (h1 : m = (NUMERAL 0)) : (term1 m) = term3.
Proof. exact (EQ_MP (@lem5418310 m h1) (@lem5400808 m h1)). Qed.
Lemma lem5418312 (m : nat) : term4 m.
Proof. exact (fun h0 : m = (NUMERAL 0) => @lem5418311 m h0). Qed.
Lemma lem5418313 (m : nat) : term5 m.
Proof. exact (conj (@lem5418312 m) (@lem5418308 m)). Qed.
Lemma lem5418314 (m : nat) : (term1 m) = (term6 m).
Proof. exact (EQ_MP (@lem5400807 m) (@lem5418313 m)). Qed.
