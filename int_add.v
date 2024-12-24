Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import int_add_term_abbrevs.
Lemma lem2273722 : int_add = term0.
Proof. exact (@int_add_def). Qed.
Lemma lem2273723 (_28676 : int) : _28676 = _28676.
Proof. exact (eq_refl _28676). Qed.
Lemma lem2273724 (_28676 : int) : (int_add _28676) = (term1 _28676).
Proof. exact (MK_COMB (@lem2273722) (@lem2273723 _28676)). Qed.
Lemma lem2273725 (_28676 : int) : (term1 _28676) = (term2 _28676).
Proof. exact (eq_refl (term1 _28676)). Qed.
Lemma lem2273726 (_28676 : int) : (int_add _28676) = (term2 _28676).
Proof. exact (TRANS (@lem2273724 _28676) (@lem2273725 _28676)). Qed.
Lemma lem2273727 (_28677 : int) : _28677 = _28677.
Proof. exact (eq_refl _28677). Qed.
Lemma lem2273728 (_28676 : int) (_28677 : int) : (int_add _28676 _28677) = (term3 _28676 _28677).
Proof. exact (MK_COMB (@lem2273726 _28676) (@lem2273727 _28677)). Qed.
Lemma lem2273729 (_28676 : int) (_28677 : int) : (term3 _28676 _28677) = (term4 _28676 _28677).
Proof. exact (eq_refl (term3 _28676 _28677)). Qed.
Lemma lem2273730 (_28676 : int) (_28677 : int) : (int_add _28676 _28677) = (term4 _28676 _28677).
Proof. exact (TRANS (@lem2273728 _28676 _28677) (@lem2273729 _28676 _28677)). Qed.
Lemma lem2273731 (_28676 : int) : term5 _28676.
Proof. exact (fun _28677 : int => @lem2273730 _28676 _28677). Qed.
Lemma lem2273732 : term6.
Proof. exact (fun _28676 : int => @lem2273731 _28676). Qed.
Lemma lem2273733 (_28676 : int) : term7 _28676.
Proof. exact (@lem2273732 _28676). Qed.
Lemma lem2273734 (_28676 : int) : (term7 _28676) = (term5 _28676).
Proof. exact (eq_refl (term7 _28676)). Qed.
Lemma lem2273735 (_28676 : int) : term5 _28676.
Proof. exact (EQ_MP (@lem2273734 _28676) (@lem2273733 _28676)). Qed.
Lemma lem2273736 (_28676 : int) (_28677 : int) : term8 _28676 _28677.
Proof. exact (@lem2273735 _28676 _28677). Qed.
Lemma lem2273737 (_28676 : int) (_28677 : int) : (term8 _28676 _28677) = ((int_add _28676 _28677) = (term4 _28676 _28677)).
Proof. exact (eq_refl (term8 _28676 _28677)). Qed.
Lemma lem2273738 (_28676 : int) (_28677 : int) : (int_add _28676 _28677) = (term4 _28676 _28677).
Proof. exact (EQ_MP (@lem2273737 _28676 _28677) (@lem2273736 _28676 _28677)). Qed.
Lemma lem2273781 (x : int) (y : int) : (int_add x y) = (term4 x y).
Proof. exact (@lem2273738 x y). Qed.
Lemma lem2273782 (x : int) : term5 x.
Proof. exact (fun y : int => @lem2273781 x y). Qed.
Lemma lem2273783 : term6.
Proof. exact (fun x : int => @lem2273782 x). Qed.
