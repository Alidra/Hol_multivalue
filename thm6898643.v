Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm6898643_term_abbrevs.
Require Import neutral_spec.
Lemma lem6898618 {_119565 : Type'} (op : type1400 _119565) : term0 _119565 op.
Proof. exact (@lem5711574 _119565 op). Qed.
Lemma lem6898619 {_119565 : Type'} (op : type1400 _119565) : (term0 _119565 op) = ((@neutral _119565 op) = (term1 _119565 op)).
Proof. exact (eq_refl (term0 _119565 op)). Qed.
Lemma lem6898624 {_119565 : Type'} (op : type1400 _119565) : (@neutral _119565 op) = (term1 _119565 op).
Proof. exact (EQ_MP (@lem6898619 _119565 op) (@lem6898618 _119565 op)). Qed.
Lemma lem6898625 (op : type1606) : (@neutral nat op) = (term2 op).
Proof. exact (@lem6898624 nat op). Qed.
Lemma lem6898626 : (@neutral nat Nat.mul) = term3.
Proof. exact (@lem6898625 Nat.mul). Qed.
Lemma lem6898637 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6898638 : term4 = term5.
Proof. exact (MK_COMB (@lem6898637) (@lem6898626)). Qed.
Lemma lem6898639 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem6898640 : ((@neutral nat Nat.mul) = term6) = (term3 = term6).
Proof. exact (MK_COMB (@lem6898638) (@lem6898639)). Qed.
Lemma lem6898643 : (term3 = term6) = ((@neutral nat Nat.mul) = term6).
Proof. exact (SYM (@lem6898640)). Qed.
