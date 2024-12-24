Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import real_lt_term_abbrevs.
Lemma lem1341505 : real_lt = term0.
Proof. exact (@real_lt_def). Qed.
Lemma lem1341506 (_23911 : real) : _23911 = _23911.
Proof. exact (eq_refl _23911). Qed.
Lemma lem1341507 (_23911 : real) : (real_lt _23911) = (term1 _23911).
Proof. exact (MK_COMB (@lem1341505) (@lem1341506 _23911)). Qed.
Lemma lem1341508 (_23911 : real) : (term1 _23911) = (term2 _23911).
Proof. exact (eq_refl (term1 _23911)). Qed.
Lemma lem1341509 (_23911 : real) : (real_lt _23911) = (term2 _23911).
Proof. exact (TRANS (@lem1341507 _23911) (@lem1341508 _23911)). Qed.
Lemma lem1341510 (_23912 : real) : _23912 = _23912.
Proof. exact (eq_refl _23912). Qed.
Lemma lem1341511 (_23911 : real) (_23912 : real) : (real_lt _23911 _23912) = (term3 _23911 _23912).
Proof. exact (MK_COMB (@lem1341509 _23911) (@lem1341510 _23912)). Qed.
Lemma lem1341512 (_23912 : real) (_23911 : real) : (term3 _23911 _23912) = (term4 _23912 _23911).
Proof. exact (eq_refl (term3 _23911 _23912)). Qed.
Lemma lem1341513 (_23912 : real) (_23911 : real) : (real_lt _23911 _23912) = (term4 _23912 _23911).
Proof. exact (TRANS (@lem1341511 _23911 _23912) (@lem1341512 _23912 _23911)). Qed.
Lemma lem1341514 (_23911 : real) : term5 _23911.
Proof. exact (fun _23912 : real => @lem1341513 _23912 _23911). Qed.
Lemma lem1341515 : term6.
Proof. exact (fun _23911 : real => @lem1341514 _23911). Qed.
Lemma lem1341516 (_23911 : real) : term7 _23911.
Proof. exact (@lem1341515 _23911). Qed.
Lemma lem1341517 (_23911 : real) : (term7 _23911) = (term5 _23911).
Proof. exact (eq_refl (term7 _23911)). Qed.
Lemma lem1341518 (_23911 : real) : term5 _23911.
Proof. exact (EQ_MP (@lem1341517 _23911) (@lem1341516 _23911)). Qed.
Lemma lem1341519 (_23911 : real) (_23912 : real) : term8 _23911 _23912.
Proof. exact (@lem1341518 _23911 _23912). Qed.
Lemma lem1341520 (_23912 : real) (_23911 : real) : (term8 _23911 _23912) = ((real_lt _23911 _23912) = (term4 _23912 _23911)).
Proof. exact (eq_refl (term8 _23911 _23912)). Qed.
Lemma lem1341521 (_23912 : real) (_23911 : real) : (real_lt _23911 _23912) = (term4 _23912 _23911).
Proof. exact (EQ_MP (@lem1341520 _23912 _23911) (@lem1341519 _23911 _23912)). Qed.
Lemma lem1341564 (y : real) (x : real) : (real_lt x y) = (term4 y x).
Proof. exact (@lem1341521 y x). Qed.
Lemma lem1341565 (y : real) : term9 y.
Proof. exact (fun x : real => @lem1341564 y x). Qed.
Lemma lem1341566 : term10.
Proof. exact (fun y : real => @lem1341565 y). Qed.
