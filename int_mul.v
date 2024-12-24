Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import int_mul_term_abbrevs.
Lemma lem2286246 : int_mul = term0.
Proof. exact (@int_mul_def). Qed.
Lemma lem2286247 (_28720 : int) : _28720 = _28720.
Proof. exact (eq_refl _28720). Qed.
Lemma lem2286248 (_28720 : int) : (int_mul _28720) = (term1 _28720).
Proof. exact (MK_COMB (@lem2286246) (@lem2286247 _28720)). Qed.
Lemma lem2286249 (_28720 : int) : (term1 _28720) = (term2 _28720).
Proof. exact (eq_refl (term1 _28720)). Qed.
Lemma lem2286250 (_28720 : int) : (int_mul _28720) = (term2 _28720).
Proof. exact (TRANS (@lem2286248 _28720) (@lem2286249 _28720)). Qed.
Lemma lem2286251 (_28721 : int) : _28721 = _28721.
Proof. exact (eq_refl _28721). Qed.
Lemma lem2286252 (_28720 : int) (_28721 : int) : (int_mul _28720 _28721) = (term3 _28720 _28721).
Proof. exact (MK_COMB (@lem2286250 _28720) (@lem2286251 _28721)). Qed.
Lemma lem2286253 (_28720 : int) (_28721 : int) : (term3 _28720 _28721) = (term4 _28720 _28721).
Proof. exact (eq_refl (term3 _28720 _28721)). Qed.
Lemma lem2286254 (_28720 : int) (_28721 : int) : (int_mul _28720 _28721) = (term4 _28720 _28721).
Proof. exact (TRANS (@lem2286252 _28720 _28721) (@lem2286253 _28720 _28721)). Qed.
Lemma lem2286255 (_28720 : int) : term5 _28720.
Proof. exact (fun _28721 : int => @lem2286254 _28720 _28721). Qed.
Lemma lem2286256 : term6.
Proof. exact (fun _28720 : int => @lem2286255 _28720). Qed.
Lemma lem2286257 (_28720 : int) : term7 _28720.
Proof. exact (@lem2286256 _28720). Qed.
Lemma lem2286258 (_28720 : int) : (term7 _28720) = (term5 _28720).
Proof. exact (eq_refl (term7 _28720)). Qed.
Lemma lem2286259 (_28720 : int) : term5 _28720.
Proof. exact (EQ_MP (@lem2286258 _28720) (@lem2286257 _28720)). Qed.
Lemma lem2286260 (_28720 : int) (_28721 : int) : term8 _28720 _28721.
Proof. exact (@lem2286259 _28720 _28721). Qed.
Lemma lem2286261 (_28720 : int) (_28721 : int) : (term8 _28720 _28721) = ((int_mul _28720 _28721) = (term4 _28720 _28721)).
Proof. exact (eq_refl (term8 _28720 _28721)). Qed.
Lemma lem2286262 (_28720 : int) (_28721 : int) : (int_mul _28720 _28721) = (term4 _28720 _28721).
Proof. exact (EQ_MP (@lem2286261 _28720 _28721) (@lem2286260 _28720 _28721)). Qed.
Lemma lem2286305 (x : int) (y : int) : (int_mul x y) = (term4 x y).
Proof. exact (@lem2286262 x y). Qed.
Lemma lem2286306 (x : int) : term5 x.
Proof. exact (fun y : int => @lem2286305 x y). Qed.
Lemma lem2286307 : term6.
Proof. exact (fun x : int => @lem2286306 x). Qed.
