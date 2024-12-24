Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import real_mod_term_abbrevs.
Lemma lem2428540 : real_mod = term0.
Proof. exact (@real_mod_def). Qed.
Lemma lem2428541 (_29496 : real) : _29496 = _29496.
Proof. exact (eq_refl _29496). Qed.
Lemma lem2428542 (_29496 : real) : (real_mod _29496) = (term1 _29496).
Proof. exact (MK_COMB (@lem2428540) (@lem2428541 _29496)). Qed.
Lemma lem2428543 (_29496 : real) : (term1 _29496) = (term2 _29496).
Proof. exact (eq_refl (term1 _29496)). Qed.
Lemma lem2428544 (_29496 : real) : (real_mod _29496) = (term2 _29496).
Proof. exact (TRANS (@lem2428542 _29496) (@lem2428543 _29496)). Qed.
Lemma lem2428545 (_29497 : real) : _29497 = _29497.
Proof. exact (eq_refl _29497). Qed.
Lemma lem2428546 (_29496 : real) (_29497 : real) : (real_mod _29496 _29497) = (term3 _29496 _29497).
Proof. exact (MK_COMB (@lem2428544 _29496) (@lem2428545 _29497)). Qed.
Lemma lem2428547 (_29497 : real) (_29496 : real) : (term3 _29496 _29497) = (term4 _29497 _29496).
Proof. exact (eq_refl (term3 _29496 _29497)). Qed.
Lemma lem2428548 (_29497 : real) (_29496 : real) : (real_mod _29496 _29497) = (term4 _29497 _29496).
Proof. exact (TRANS (@lem2428546 _29496 _29497) (@lem2428547 _29497 _29496)). Qed.
Lemma lem2428549 (_29498 : real) : _29498 = _29498.
Proof. exact (eq_refl _29498). Qed.
Lemma lem2428550 (_29497 : real) (_29496 : real) (_29498 : real) : (real_mod _29496 _29497 _29498) = (term5 _29497 _29496 _29498).
Proof. exact (MK_COMB (@lem2428548 _29497 _29496) (@lem2428549 _29498)). Qed.
Lemma lem2428551 (_29497 : real) (_29498 : real) (_29496 : real) : (term5 _29497 _29496 _29498) = (term6 _29497 _29498 _29496).
Proof. exact (eq_refl (term5 _29497 _29496 _29498)). Qed.
Lemma lem2428552 (_29497 : real) (_29498 : real) (_29496 : real) : (real_mod _29496 _29497 _29498) = (term6 _29497 _29498 _29496).
Proof. exact (TRANS (@lem2428550 _29497 _29496 _29498) (@lem2428551 _29497 _29498 _29496)). Qed.
Lemma lem2428553 (_29497 : real) (_29496 : real) : term7 _29497 _29496.
Proof. exact (fun _29498 : real => @lem2428552 _29497 _29498 _29496). Qed.
Lemma lem2428554 (_29496 : real) : term8 _29496.
Proof. exact (fun _29497 : real => @lem2428553 _29497 _29496). Qed.
Lemma lem2428555 : term9.
Proof. exact (fun _29496 : real => @lem2428554 _29496). Qed.
Lemma lem2428556 (_29496 : real) : term10 _29496.
Proof. exact (@lem2428555 _29496). Qed.
Lemma lem2428557 (_29496 : real) : (term10 _29496) = (term8 _29496).
Proof. exact (eq_refl (term10 _29496)). Qed.
Lemma lem2428558 (_29496 : real) : term8 _29496.
Proof. exact (EQ_MP (@lem2428557 _29496) (@lem2428556 _29496)). Qed.
Lemma lem2428559 (_29496 : real) (_29497 : real) : term11 _29496 _29497.
Proof. exact (@lem2428558 _29496 _29497). Qed.
Lemma lem2428560 (_29497 : real) (_29496 : real) : (term11 _29496 _29497) = (term7 _29497 _29496).
Proof. exact (eq_refl (term11 _29496 _29497)). Qed.
Lemma lem2428561 (_29497 : real) (_29496 : real) : term7 _29497 _29496.
Proof. exact (EQ_MP (@lem2428560 _29497 _29496) (@lem2428559 _29496 _29497)). Qed.
Lemma lem2428562 (_29497 : real) (_29496 : real) (_29498 : real) : term12 _29497 _29496 _29498.
Proof. exact (@lem2428561 _29497 _29496 _29498). Qed.
Lemma lem2428563 (_29497 : real) (_29498 : real) (_29496 : real) : (term12 _29497 _29496 _29498) = ((real_mod _29496 _29497 _29498) = (term6 _29497 _29498 _29496)).
Proof. exact (eq_refl (term12 _29497 _29496 _29498)). Qed.
Lemma lem2428564 (_29497 : real) (_29498 : real) (_29496 : real) : (real_mod _29496 _29497 _29498) = (term6 _29497 _29498 _29496).
Proof. exact (EQ_MP (@lem2428563 _29497 _29498 _29496) (@lem2428562 _29497 _29496 _29498)). Qed.
Lemma lem2428620 (x : real) (y : real) (n : real) : (real_mod n x y) = (term6 x y n).
Proof. exact (@lem2428564 x y n). Qed.
Lemma lem2428621 (x : real) (y : real) : term13 x y.
Proof. exact (fun n : real => @lem2428620 x y n). Qed.
Lemma lem2428622 (x : real) : term14 x.
Proof. exact (fun y : real => @lem2428621 x y). Qed.
Lemma lem2428623 : term15.
Proof. exact (fun x : real => @lem2428622 x). Qed.
