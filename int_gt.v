Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import int_gt_term_abbrevs.
Lemma lem2271082 : int_gt = term0.
Proof. exact (@int_gt_def). Qed.
Lemma lem2271083 (_28650 : int) : _28650 = _28650.
Proof. exact (eq_refl _28650). Qed.
Lemma lem2271084 (_28650 : int) : (int_gt _28650) = (term1 _28650).
Proof. exact (MK_COMB (@lem2271082) (@lem2271083 _28650)). Qed.
Lemma lem2271085 (_28650 : int) : (term1 _28650) = (term2 _28650).
Proof. exact (eq_refl (term1 _28650)). Qed.
Lemma lem2271086 (_28650 : int) : (int_gt _28650) = (term2 _28650).
Proof. exact (TRANS (@lem2271084 _28650) (@lem2271085 _28650)). Qed.
Lemma lem2271087 (_28651 : int) : _28651 = _28651.
Proof. exact (eq_refl _28651). Qed.
Lemma lem2271088 (_28650 : int) (_28651 : int) : (int_gt _28650 _28651) = (term3 _28650 _28651).
Proof. exact (MK_COMB (@lem2271086 _28650) (@lem2271087 _28651)). Qed.
Lemma lem2271089 (_28650 : int) (_28651 : int) : (term3 _28650 _28651) = (term4 _28650 _28651).
Proof. exact (eq_refl (term3 _28650 _28651)). Qed.
Lemma lem2271090 (_28650 : int) (_28651 : int) : (int_gt _28650 _28651) = (term4 _28650 _28651).
Proof. exact (TRANS (@lem2271088 _28650 _28651) (@lem2271089 _28650 _28651)). Qed.
Lemma lem2271091 (_28650 : int) : term5 _28650.
Proof. exact (fun _28651 : int => @lem2271090 _28650 _28651). Qed.
Lemma lem2271092 : term6.
Proof. exact (fun _28650 : int => @lem2271091 _28650). Qed.
Lemma lem2271093 (_28650 : int) : term7 _28650.
Proof. exact (@lem2271092 _28650). Qed.
Lemma lem2271094 (_28650 : int) : (term7 _28650) = (term5 _28650).
Proof. exact (eq_refl (term7 _28650)). Qed.
Lemma lem2271095 (_28650 : int) : term5 _28650.
Proof. exact (EQ_MP (@lem2271094 _28650) (@lem2271093 _28650)). Qed.
Lemma lem2271096 (_28650 : int) (_28651 : int) : term8 _28650 _28651.
Proof. exact (@lem2271095 _28650 _28651). Qed.
Lemma lem2271097 (_28650 : int) (_28651 : int) : (term8 _28650 _28651) = ((int_gt _28650 _28651) = (term4 _28650 _28651)).
Proof. exact (eq_refl (term8 _28650 _28651)). Qed.
Lemma lem2271098 (_28650 : int) (_28651 : int) : (int_gt _28650 _28651) = (term4 _28650 _28651).
Proof. exact (EQ_MP (@lem2271097 _28650 _28651) (@lem2271096 _28650 _28651)). Qed.
Lemma lem2271141 (x : int) (y : int) : (int_gt x y) = (term4 x y).
Proof. exact (@lem2271098 x y). Qed.
Lemma lem2271142 (x : int) : term5 x.
Proof. exact (fun y : int => @lem2271141 x y). Qed.
Lemma lem2271143 : term6.
Proof. exact (fun x : int => @lem2271142 x). Qed.
