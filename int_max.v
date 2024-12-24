Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import int_max_term_abbrevs.
Lemma lem2292209 : int_max = term0.
Proof. exact (@int_max_def). Qed.
Lemma lem2292210 (_28811 : int) : _28811 = _28811.
Proof. exact (eq_refl _28811). Qed.
Lemma lem2292211 (_28811 : int) : (int_max _28811) = (term1 _28811).
Proof. exact (MK_COMB (@lem2292209) (@lem2292210 _28811)). Qed.
Lemma lem2292212 (_28811 : int) : (term1 _28811) = (term2 _28811).
Proof. exact (eq_refl (term1 _28811)). Qed.
Lemma lem2292213 (_28811 : int) : (int_max _28811) = (term2 _28811).
Proof. exact (TRANS (@lem2292211 _28811) (@lem2292212 _28811)). Qed.
Lemma lem2292214 (_28812 : int) : _28812 = _28812.
Proof. exact (eq_refl _28812). Qed.
Lemma lem2292215 (_28811 : int) (_28812 : int) : (int_max _28811 _28812) = (term3 _28811 _28812).
Proof. exact (MK_COMB (@lem2292213 _28811) (@lem2292214 _28812)). Qed.
Lemma lem2292216 (_28811 : int) (_28812 : int) : (term3 _28811 _28812) = (term4 _28811 _28812).
Proof. exact (eq_refl (term3 _28811 _28812)). Qed.
Lemma lem2292217 (_28811 : int) (_28812 : int) : (int_max _28811 _28812) = (term4 _28811 _28812).
Proof. exact (TRANS (@lem2292215 _28811 _28812) (@lem2292216 _28811 _28812)). Qed.
Lemma lem2292218 (_28811 : int) : term5 _28811.
Proof. exact (fun _28812 : int => @lem2292217 _28811 _28812). Qed.
Lemma lem2292219 : term6.
Proof. exact (fun _28811 : int => @lem2292218 _28811). Qed.
Lemma lem2292220 (_28811 : int) : term7 _28811.
Proof. exact (@lem2292219 _28811). Qed.
Lemma lem2292221 (_28811 : int) : (term7 _28811) = (term5 _28811).
Proof. exact (eq_refl (term7 _28811)). Qed.
Lemma lem2292222 (_28811 : int) : term5 _28811.
Proof. exact (EQ_MP (@lem2292221 _28811) (@lem2292220 _28811)). Qed.
Lemma lem2292223 (_28811 : int) (_28812 : int) : term8 _28811 _28812.
Proof. exact (@lem2292222 _28811 _28812). Qed.
Lemma lem2292224 (_28811 : int) (_28812 : int) : (term8 _28811 _28812) = ((int_max _28811 _28812) = (term4 _28811 _28812)).
Proof. exact (eq_refl (term8 _28811 _28812)). Qed.
Lemma lem2292225 (_28811 : int) (_28812 : int) : (int_max _28811 _28812) = (term4 _28811 _28812).
Proof. exact (EQ_MP (@lem2292224 _28811 _28812) (@lem2292223 _28811 _28812)). Qed.
Lemma lem2292268 (x : int) (y : int) : (int_max x y) = (term4 x y).
Proof. exact (@lem2292225 x y). Qed.
Lemma lem2292269 (x : int) : term5 x.
Proof. exact (fun y : int => @lem2292268 x y). Qed.
Lemma lem2292270 : term6.
Proof. exact (fun x : int => @lem2292269 x). Qed.
