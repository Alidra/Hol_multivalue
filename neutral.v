Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import neutral_term_abbrevs.
Lemma lem5711535 {_119565 : Type'} : (@neutral _119565) = (term0 _119565).
Proof. exact (@neutral_def _119565). Qed.
Lemma lem5711536 {_119565 : Type'} (_71604 : type1400 _119565) : _71604 = _71604.
Proof. exact (eq_refl _71604). Qed.
Lemma lem5711537 {_119565 : Type'} (_71604 : type1400 _119565) : (@neutral _119565 _71604) = (term1 _119565 _71604).
Proof. exact (MK_COMB (@lem5711535 _119565) (@lem5711536 _119565 _71604)). Qed.
Lemma lem5711538 {_119565 : Type'} (_71604 : type1400 _119565) : (term1 _119565 _71604) = (term2 _119565 _71604).
Proof. exact (eq_refl (term1 _119565 _71604)). Qed.
Lemma lem5711539 {_119565 : Type'} (_71604 : type1400 _119565) : (@neutral _119565 _71604) = (term2 _119565 _71604).
Proof. exact (TRANS (@lem5711537 _119565 _71604) (@lem5711538 _119565 _71604)). Qed.
Lemma lem5711540 {_119565 : Type'} : term3 _119565.
Proof. exact (fun _71604 : type1400 _119565 => @lem5711539 _119565 _71604). Qed.
Lemma lem5711541 {_119565 : Type'} (_71604 : type1400 _119565) : term4 _119565 _71604.
Proof. exact (@lem5711540 _119565 _71604). Qed.
Lemma lem5711542 {_119565 : Type'} (_71604 : type1400 _119565) : (term4 _119565 _71604) = ((@neutral _119565 _71604) = (term2 _119565 _71604)).
Proof. exact (eq_refl (term4 _119565 _71604)). Qed.
Lemma lem5711543 {_119565 : Type'} (_71604 : type1400 _119565) : (@neutral _119565 _71604) = (term2 _119565 _71604).
Proof. exact (EQ_MP (@lem5711542 _119565 _71604) (@lem5711541 _119565 _71604)). Qed.
Lemma lem5711573 {_119565 : Type'} (op : type1400 _119565) : (@neutral _119565 op) = (term2 _119565 op).
Proof. exact (@lem5711543 _119565 op). Qed.
Lemma lem5711574 {_119565 : Type'} : term3 _119565.
Proof. exact (fun op : type1400 _119565 => @lem5711573 _119565 op). Qed.
