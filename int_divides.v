Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import int_divides_term_abbrevs.
Lemma lem2429355 : int_divides = term0.
Proof. exact (@int_divides_def). Qed.
Lemma lem2429356 (_29517 : int) : _29517 = _29517.
Proof. exact (eq_refl _29517). Qed.
Lemma lem2429357 (_29517 : int) : (int_divides _29517) = (term1 _29517).
Proof. exact (MK_COMB (@lem2429355) (@lem2429356 _29517)). Qed.
Lemma lem2429358 (_29517 : int) : (term1 _29517) = (term2 _29517).
Proof. exact (eq_refl (term1 _29517)). Qed.
Lemma lem2429359 (_29517 : int) : (int_divides _29517) = (term2 _29517).
Proof. exact (TRANS (@lem2429357 _29517) (@lem2429358 _29517)). Qed.
Lemma lem2429360 (_29518 : int) : _29518 = _29518.
Proof. exact (eq_refl _29518). Qed.
Lemma lem2429361 (_29517 : int) (_29518 : int) : (int_divides _29517 _29518) = (term3 _29517 _29518).
Proof. exact (MK_COMB (@lem2429359 _29517) (@lem2429360 _29518)). Qed.
Lemma lem2429362 (_29518 : int) (_29517 : int) : (term3 _29517 _29518) = (term4 _29518 _29517).
Proof. exact (eq_refl (term3 _29517 _29518)). Qed.
Lemma lem2429363 (_29518 : int) (_29517 : int) : (int_divides _29517 _29518) = (term4 _29518 _29517).
Proof. exact (TRANS (@lem2429361 _29517 _29518) (@lem2429362 _29518 _29517)). Qed.
Lemma lem2429364 (_29517 : int) : term5 _29517.
Proof. exact (fun _29518 : int => @lem2429363 _29518 _29517). Qed.
Lemma lem2429365 : term6.
Proof. exact (fun _29517 : int => @lem2429364 _29517). Qed.
Lemma lem2429366 (_29517 : int) : term7 _29517.
Proof. exact (@lem2429365 _29517). Qed.
Lemma lem2429367 (_29517 : int) : (term7 _29517) = (term5 _29517).
Proof. exact (eq_refl (term7 _29517)). Qed.
Lemma lem2429368 (_29517 : int) : term5 _29517.
Proof. exact (EQ_MP (@lem2429367 _29517) (@lem2429366 _29517)). Qed.
Lemma lem2429369 (_29517 : int) (_29518 : int) : term8 _29517 _29518.
Proof. exact (@lem2429368 _29517 _29518). Qed.
Lemma lem2429370 (_29518 : int) (_29517 : int) : (term8 _29517 _29518) = ((int_divides _29517 _29518) = (term4 _29518 _29517)).
Proof. exact (eq_refl (term8 _29517 _29518)). Qed.
Lemma lem2429371 (_29518 : int) (_29517 : int) : (int_divides _29517 _29518) = (term4 _29518 _29517).
Proof. exact (EQ_MP (@lem2429370 _29518 _29517) (@lem2429369 _29517 _29518)). Qed.
Lemma lem2429414 (b : int) (a : int) : (int_divides a b) = (term4 b a).
Proof. exact (@lem2429371 b a). Qed.
Lemma lem2429415 (b : int) : term9 b.
Proof. exact (fun a : int => @lem2429414 b a). Qed.
Lemma lem2429416 : term10.
Proof. exact (fun b : int => @lem2429415 b). Qed.
