Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1338512_term_abbrevs.
Require Import TREAL_ADD_LID_spec.
Require Import thm1337531_spec.
Require Import thm1337536_spec.
Require Import thm1337747_spec.
Require Import thm1337752_spec.
Require Import thm1338105_spec.
Require Import thm1338106_spec.
Require Import thm1338112_spec.
Require Import thm1338113_spec.
Lemma lem1338459 (x : prod hreal hreal) (y : prod hreal hreal) : (treal_eq x y) = ((term0 x) = (term0 y)).
Proof. exact (EQ_MP (@lem1338113 x y) (@lem1338112 x y)). Qed.
Lemma lem1338460 (x : prod hreal hreal) : (term1 x) = ((term2 x) = (term0 x)).
Proof. exact (@lem1338459 (term3 x) x). Qed.
Lemma lem1338464 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term4 x1 y1) = (term5 x1 y1).
Proof. exact (EQ_MP (@lem1337752 x1 y1) (@lem1337747 x1 y1)). Qed.
Lemma lem1338465 (x : prod hreal hreal) : (term2 x) = (term6 x).
Proof. exact (@lem1338464 term7 x). Qed.
Lemma lem1338467 (m : nat) : (term8 m) = (real_of_num m).
Proof. exact (EQ_MP (@lem1337536 m) (@lem1337531 m)). Qed.
Lemma lem1338468 : term9 = term10.
Proof. exact (@lem1338467 (NUMERAL 0)). Qed.
Lemma lem1338469 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1338470 : term11 = term12.
Proof. exact (MK_COMB (@lem1338469) (@lem1338468)). Qed.
Lemma lem1338471 (x : prod hreal hreal) : (term0 x) = (term0 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1338472 (x : prod hreal hreal) : (term6 x) = (term13 x).
Proof. exact (MK_COMB (@lem1338470) (@lem1338471 x)). Qed.
Lemma lem1338473 (x : prod hreal hreal) : (term2 x) = (term13 x).
Proof. exact (TRANS (@lem1338465 x) (@lem1338472 x)). Qed.
Lemma lem1338474 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1338475 (x : prod hreal hreal) : (term14 x) = (term15 x).
Proof. exact (MK_COMB (@lem1338474) (@lem1338473 x)). Qed.
Lemma lem1338476 (x : prod hreal hreal) : (term0 x) = (term0 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1338477 (x : prod hreal hreal) : ((term2 x) = (term0 x)) = ((term13 x) = (term0 x)).
Proof. exact (MK_COMB (@lem1338475 x) (@lem1338476 x)). Qed.
Lemma lem1338480 (x : prod hreal hreal) : (term1 x) = ((term13 x) = (term0 x)).
Proof. exact (TRANS (@lem1338460 x) (@lem1338477 x)). Qed.
Lemma lem1338481 : term16 = term17.
Proof. exact (fun_ext (fun x : prod hreal hreal => @lem1338480 x)). Qed.
Lemma lem1338482 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1338483 : term18 = term19.
Proof. exact (MK_COMB (@lem1338482) (@lem1338481)). Qed.
Lemma lem1338489 (P : real -> Prop) : (term20 P) = (term21 P).
Proof. exact (EQ_MP (@lem1338106 P) (@lem1338105 P)). Qed.
Lemma lem1338490 : term22 = term23.
Proof. exact (@lem1338489 term24). Qed.
Lemma lem1338491 (x : prod hreal hreal) : (term25 x) = ((term13 x) = (term0 x)).
Proof. exact (eq_refl (term25 x)). Qed.
Lemma lem1338492 : term26 = term17.
Proof. exact (fun_ext (fun x : prod hreal hreal => @lem1338491 x)). Qed.
Lemma lem1338493 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1338494 : term22 = term19.
Proof. exact (MK_COMB (@lem1338493) (@lem1338492)). Qed.
Lemma lem1338495 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1338496 : term27 = term28.
Proof. exact (MK_COMB (@lem1338495) (@lem1338494)). Qed.
Lemma lem1338497 (x : real) : (term29 x) = ((term30 x) = x).
Proof. exact (eq_refl (term29 x)). Qed.
Lemma lem1338498 : term31 = term24.
Proof. exact (fun_ext (fun x : real => @lem1338497 x)). Qed.
Lemma lem1338499 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1338500 : term23 = term32.
Proof. exact (MK_COMB (@lem1338499) (@lem1338498)). Qed.
Lemma lem1338501 : (term22 = term23) = (term19 = term32).
Proof. exact (MK_COMB (@lem1338496) (@lem1338500)). Qed.
Lemma lem1338502 : term19 = term32.
Proof. exact (EQ_MP (@lem1338501) (@lem1338490)). Qed.
Lemma lem1338511 : term18 = term32.
Proof. exact (TRANS (@lem1338483) (@lem1338502)). Qed.
Lemma lem1338512 : term32.
Proof. exact (EQ_MP (@lem1338511) (@lem1328160)). Qed.
