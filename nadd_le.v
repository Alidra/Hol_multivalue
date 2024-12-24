Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import nadd_le_term_abbrevs.
Lemma lem1269631 : nadd_le = term0.
Proof. exact (@nadd_le_def). Qed.
Lemma lem1269632 (_23168 : nadd) : _23168 = _23168.
Proof. exact (eq_refl _23168). Qed.
Lemma lem1269633 (_23168 : nadd) : (nadd_le _23168) = (term1 _23168).
Proof. exact (MK_COMB (@lem1269631) (@lem1269632 _23168)). Qed.
Lemma lem1269634 (_23168 : nadd) : (term1 _23168) = (term2 _23168).
Proof. exact (eq_refl (term1 _23168)). Qed.
Lemma lem1269635 (_23168 : nadd) : (nadd_le _23168) = (term2 _23168).
Proof. exact (TRANS (@lem1269633 _23168) (@lem1269634 _23168)). Qed.
Lemma lem1269636 (_23169 : nadd) : _23169 = _23169.
Proof. exact (eq_refl _23169). Qed.
Lemma lem1269637 (_23168 : nadd) (_23169 : nadd) : (nadd_le _23168 _23169) = (term3 _23168 _23169).
Proof. exact (MK_COMB (@lem1269635 _23168) (@lem1269636 _23169)). Qed.
Lemma lem1269638 (_23168 : nadd) (_23169 : nadd) : (term3 _23168 _23169) = (term4 _23168 _23169).
Proof. exact (eq_refl (term3 _23168 _23169)). Qed.
Lemma lem1269639 (_23168 : nadd) (_23169 : nadd) : (nadd_le _23168 _23169) = (term4 _23168 _23169).
Proof. exact (TRANS (@lem1269637 _23168 _23169) (@lem1269638 _23168 _23169)). Qed.
Lemma lem1269640 (_23168 : nadd) : term5 _23168.
Proof. exact (fun _23169 : nadd => @lem1269639 _23168 _23169). Qed.
Lemma lem1269641 : term6.
Proof. exact (fun _23168 : nadd => @lem1269640 _23168). Qed.
Lemma lem1269642 (_23168 : nadd) : term7 _23168.
Proof. exact (@lem1269641 _23168). Qed.
Lemma lem1269643 (_23168 : nadd) : (term7 _23168) = (term5 _23168).
Proof. exact (eq_refl (term7 _23168)). Qed.
Lemma lem1269644 (_23168 : nadd) : term5 _23168.
Proof. exact (EQ_MP (@lem1269643 _23168) (@lem1269642 _23168)). Qed.
Lemma lem1269645 (_23168 : nadd) (_23169 : nadd) : term8 _23168 _23169.
Proof. exact (@lem1269644 _23168 _23169). Qed.
Lemma lem1269646 (_23168 : nadd) (_23169 : nadd) : (term8 _23168 _23169) = ((nadd_le _23168 _23169) = (term4 _23168 _23169)).
Proof. exact (eq_refl (term8 _23168 _23169)). Qed.
Lemma lem1269647 (_23168 : nadd) (_23169 : nadd) : (nadd_le _23168 _23169) = (term4 _23168 _23169).
Proof. exact (EQ_MP (@lem1269646 _23168 _23169) (@lem1269645 _23168 _23169)). Qed.
Lemma lem1269690 (x : nadd) (y : nadd) : (nadd_le x y) = (term4 x y).
Proof. exact (@lem1269647 x y). Qed.
Lemma lem1269691 (x : nadd) : term5 x.
Proof. exact (fun y : nadd => @lem1269690 x y). Qed.
Lemma lem1269692 : term6.
Proof. exact (fun x : nadd => @lem1269691 x). Qed.
