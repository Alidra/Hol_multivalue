Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm6920431_term_abbrevs.
Require Import neutral_spec.
Lemma lem6920406 {_119565 : Type'} (op : type1400 _119565) : term0 _119565 op.
Proof. exact (@lem5711574 _119565 op). Qed.
Lemma lem6920407 {_119565 : Type'} (op : type1400 _119565) : (term0 _119565 op) = ((@neutral _119565 op) = (term1 _119565 op)).
Proof. exact (eq_refl (term0 _119565 op)). Qed.
Lemma lem6920412 {_119565 : Type'} (op : type1400 _119565) : (@neutral _119565 op) = (term1 _119565 op).
Proof. exact (EQ_MP (@lem6920407 _119565 op) (@lem6920406 _119565 op)). Qed.
Lemma lem6920413 (op : type1606) : (@neutral nat op) = (term2 op).
Proof. exact (@lem6920412 nat op). Qed.
Lemma lem6920414 : (@neutral nat Nat.add) = term3.
Proof. exact (@lem6920413 Nat.add). Qed.
Lemma lem6920425 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6920426 : term4 = term5.
Proof. exact (MK_COMB (@lem6920425) (@lem6920414)). Qed.
Lemma lem6920427 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem6920428 : ((@neutral nat Nat.add) = (NUMERAL 0)) = (term3 = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem6920426) (@lem6920427)). Qed.
Lemma lem6920431 : (term3 = (NUMERAL 0)) = ((@neutral nat Nat.add) = (NUMERAL 0)).
Proof. exact (SYM (@lem6920428)). Qed.
