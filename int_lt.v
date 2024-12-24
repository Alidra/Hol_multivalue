Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import int_lt_term_abbrevs.
Lemma lem2269708 : int_lt = term0.
Proof. exact (@int_lt_def). Qed.
Lemma lem2269709 (_28626 : int) : _28626 = _28626.
Proof. exact (eq_refl _28626). Qed.
Lemma lem2269710 (_28626 : int) : (int_lt _28626) = (term1 _28626).
Proof. exact (MK_COMB (@lem2269708) (@lem2269709 _28626)). Qed.
Lemma lem2269711 (_28626 : int) : (term1 _28626) = (term2 _28626).
Proof. exact (eq_refl (term1 _28626)). Qed.
Lemma lem2269712 (_28626 : int) : (int_lt _28626) = (term2 _28626).
Proof. exact (TRANS (@lem2269710 _28626) (@lem2269711 _28626)). Qed.
Lemma lem2269713 (_28627 : int) : _28627 = _28627.
Proof. exact (eq_refl _28627). Qed.
Lemma lem2269714 (_28626 : int) (_28627 : int) : (int_lt _28626 _28627) = (term3 _28626 _28627).
Proof. exact (MK_COMB (@lem2269712 _28626) (@lem2269713 _28627)). Qed.
Lemma lem2269715 (_28626 : int) (_28627 : int) : (term3 _28626 _28627) = (term4 _28626 _28627).
Proof. exact (eq_refl (term3 _28626 _28627)). Qed.
Lemma lem2269716 (_28626 : int) (_28627 : int) : (int_lt _28626 _28627) = (term4 _28626 _28627).
Proof. exact (TRANS (@lem2269714 _28626 _28627) (@lem2269715 _28626 _28627)). Qed.
Lemma lem2269717 (_28626 : int) : term5 _28626.
Proof. exact (fun _28627 : int => @lem2269716 _28626 _28627). Qed.
Lemma lem2269718 : term6.
Proof. exact (fun _28626 : int => @lem2269717 _28626). Qed.
Lemma lem2269719 (_28626 : int) : term7 _28626.
Proof. exact (@lem2269718 _28626). Qed.
Lemma lem2269720 (_28626 : int) : (term7 _28626) = (term5 _28626).
Proof. exact (eq_refl (term7 _28626)). Qed.
Lemma lem2269721 (_28626 : int) : term5 _28626.
Proof. exact (EQ_MP (@lem2269720 _28626) (@lem2269719 _28626)). Qed.
Lemma lem2269722 (_28626 : int) (_28627 : int) : term8 _28626 _28627.
Proof. exact (@lem2269721 _28626 _28627). Qed.
Lemma lem2269723 (_28626 : int) (_28627 : int) : (term8 _28626 _28627) = ((int_lt _28626 _28627) = (term4 _28626 _28627)).
Proof. exact (eq_refl (term8 _28626 _28627)). Qed.
Lemma lem2269724 (_28626 : int) (_28627 : int) : (int_lt _28626 _28627) = (term4 _28626 _28627).
Proof. exact (EQ_MP (@lem2269723 _28626 _28627) (@lem2269722 _28626 _28627)). Qed.
Lemma lem2269767 (x : int) (y : int) : (int_lt x y) = (term4 x y).
Proof. exact (@lem2269724 x y). Qed.
Lemma lem2269768 (x : int) : term5 x.
Proof. exact (fun y : int => @lem2269767 x y). Qed.
Lemma lem2269769 : term6.
Proof. exact (fun x : int => @lem2269768 x). Qed.
