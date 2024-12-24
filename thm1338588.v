Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1338588_term_abbrevs.
Require Import TREAL_ADD_LINV_spec.
Require Import thm1337531_spec.
Require Import thm1337536_spec.
Require Import thm1337622_spec.
Require Import thm1337627_spec.
Require Import thm1337747_spec.
Require Import thm1337752_spec.
Require Import thm1338105_spec.
Require Import thm1338106_spec.
Require Import thm1338112_spec.
Require Import thm1338113_spec.
Lemma lem1338533 (x : prod hreal hreal) (y : prod hreal hreal) : (treal_eq x y) = ((term0 x) = (term0 y)).
Proof. exact (EQ_MP (@lem1338113 x y) (@lem1338112 x y)). Qed.
Lemma lem1338534 (x : prod hreal hreal) : (term1 x) = ((term2 x) = term3).
Proof. exact (@lem1338533 (term4 x) term5). Qed.
Lemma lem1338538 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term6 x1 y1) = (term7 x1 y1).
Proof. exact (EQ_MP (@lem1337752 x1 y1) (@lem1337747 x1 y1)). Qed.
Lemma lem1338539 (x : prod hreal hreal) : (term2 x) = (term8 x).
Proof. exact (@lem1338538 (treal_neg x) x). Qed.
Lemma lem1338541 (x1 : prod hreal hreal) : (term9 x1) = (term10 x1).
Proof. exact (EQ_MP (@lem1337627 x1) (@lem1337622 x1)). Qed.
Lemma lem1338542 (x : prod hreal hreal) : (term9 x) = (term10 x).
Proof. exact (@lem1338541 x). Qed.
Lemma lem1338543 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1338544 (x : prod hreal hreal) : (term11 x) = (term12 x).
Proof. exact (MK_COMB (@lem1338543) (@lem1338542 x)). Qed.
Lemma lem1338545 (x : prod hreal hreal) : (term0 x) = (term0 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1338546 (x : prod hreal hreal) : (term8 x) = (term13 x).
Proof. exact (MK_COMB (@lem1338544 x) (@lem1338545 x)). Qed.
Lemma lem1338547 (x : prod hreal hreal) : (term2 x) = (term13 x).
Proof. exact (TRANS (@lem1338539 x) (@lem1338546 x)). Qed.
Lemma lem1338548 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1338549 (x : prod hreal hreal) : (term14 x) = (term15 x).
Proof. exact (MK_COMB (@lem1338548) (@lem1338547 x)). Qed.
Lemma lem1338551 (m : nat) : (term16 m) = (real_of_num m).
Proof. exact (EQ_MP (@lem1337536 m) (@lem1337531 m)). Qed.
Lemma lem1338552 : term3 = term17.
Proof. exact (@lem1338551 (NUMERAL 0)). Qed.
Lemma lem1338553 (x : prod hreal hreal) : ((term2 x) = term3) = ((term13 x) = term17).
Proof. exact (MK_COMB (@lem1338549 x) (@lem1338552)). Qed.
Lemma lem1338556 (x : prod hreal hreal) : (term1 x) = ((term13 x) = term17).
Proof. exact (TRANS (@lem1338534 x) (@lem1338553 x)). Qed.
Lemma lem1338557 : term18 = term19.
Proof. exact (fun_ext (fun x : prod hreal hreal => @lem1338556 x)). Qed.
Lemma lem1338558 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1338559 : term20 = term21.
Proof. exact (MK_COMB (@lem1338558) (@lem1338557)). Qed.
Lemma lem1338565 (P : real -> Prop) : (term22 P) = (term23 P).
Proof. exact (EQ_MP (@lem1338106 P) (@lem1338105 P)). Qed.
Lemma lem1338566 : term24 = term25.
Proof. exact (@lem1338565 term26). Qed.
Lemma lem1338567 (x : prod hreal hreal) : (term27 x) = ((term13 x) = term17).
Proof. exact (eq_refl (term27 x)). Qed.
Lemma lem1338568 : term28 = term19.
Proof. exact (fun_ext (fun x : prod hreal hreal => @lem1338567 x)). Qed.
Lemma lem1338569 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1338570 : term24 = term21.
Proof. exact (MK_COMB (@lem1338569) (@lem1338568)). Qed.
Lemma lem1338571 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1338572 : term29 = term30.
Proof. exact (MK_COMB (@lem1338571) (@lem1338570)). Qed.
Lemma lem1338573 (x : real) : (term31 x) = ((term32 x) = term17).
Proof. exact (eq_refl (term31 x)). Qed.
Lemma lem1338574 : term33 = term26.
Proof. exact (fun_ext (fun x : real => @lem1338573 x)). Qed.
Lemma lem1338575 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1338576 : term25 = term34.
Proof. exact (MK_COMB (@lem1338575) (@lem1338574)). Qed.
Lemma lem1338577 : (term24 = term25) = (term21 = term34).
Proof. exact (MK_COMB (@lem1338572) (@lem1338576)). Qed.
Lemma lem1338578 : term21 = term34.
Proof. exact (EQ_MP (@lem1338577) (@lem1338566)). Qed.
Lemma lem1338587 : term20 = term34.
Proof. exact (TRANS (@lem1338559) (@lem1338578)). Qed.
Lemma lem1338588 : term34.
Proof. exact (EQ_MP (@lem1338587) (@lem1328320)). Qed.
