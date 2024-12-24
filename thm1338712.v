Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1338712_term_abbrevs.
Require Import TREAL_MUL_SYM_spec.
Require Import thm1337872_spec.
Require Import thm1337877_spec.
Require Import thm1338105_spec.
Require Import thm1338106_spec.
Require Import thm1338112_spec.
Require Import thm1338113_spec.
Lemma lem1338628 (x : prod hreal hreal) (y : prod hreal hreal) : (treal_eq x y) = ((term0 x) = (term0 y)).
Proof. exact (EQ_MP (@lem1338113 x y) (@lem1338112 x y)). Qed.
Lemma lem1338629 (y : prod hreal hreal) (x : prod hreal hreal) : (term1 y x) = ((term2 x y) = (term2 y x)).
Proof. exact (@lem1338628 (treal_mul x y) (treal_mul y x)). Qed.
Lemma lem1338633 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term2 x1 y1) = (term3 x1 y1).
Proof. exact (EQ_MP (@lem1337877 x1 y1) (@lem1337872 x1 y1)). Qed.
Lemma lem1338634 (x : prod hreal hreal) (y : prod hreal hreal) : (term2 x y) = (term3 x y).
Proof. exact (@lem1338633 x y). Qed.
Lemma lem1338635 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1338636 (x : prod hreal hreal) (y : prod hreal hreal) : (term4 x y) = (term5 x y).
Proof. exact (MK_COMB (@lem1338635) (@lem1338634 x y)). Qed.
Lemma lem1338638 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term2 x1 y1) = (term3 x1 y1).
Proof. exact (EQ_MP (@lem1337877 x1 y1) (@lem1337872 x1 y1)). Qed.
Lemma lem1338639 (y : prod hreal hreal) (x : prod hreal hreal) : (term2 y x) = (term3 y x).
Proof. exact (@lem1338638 y x). Qed.
Lemma lem1338640 (y : prod hreal hreal) (x : prod hreal hreal) : ((term2 x y) = (term2 y x)) = ((term3 x y) = (term3 y x)).
Proof. exact (MK_COMB (@lem1338636 x y) (@lem1338639 y x)). Qed.
Lemma lem1338643 (y : prod hreal hreal) (x : prod hreal hreal) : (term1 y x) = ((term3 x y) = (term3 y x)).
Proof. exact (TRANS (@lem1338629 y x) (@lem1338640 y x)). Qed.
Lemma lem1338644 (x : prod hreal hreal) : (term6 x) = (term7 x).
Proof. exact (fun_ext (fun y : prod hreal hreal => @lem1338643 y x)). Qed.
Lemma lem1338645 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1338646 (x : prod hreal hreal) : (term8 x) = (term9 x).
Proof. exact (MK_COMB (@lem1338645) (@lem1338644 x)). Qed.
Lemma lem1338652 (P : real -> Prop) : (term10 P) = (term11 P).
Proof. exact (EQ_MP (@lem1338106 P) (@lem1338105 P)). Qed.
Lemma lem1338653 (x : prod hreal hreal) : (term12 x) = (term13 x).
Proof. exact (@lem1338652 (term14 x)). Qed.
Lemma lem1338654 (y : prod hreal hreal) (x : prod hreal hreal) : (term15 x y) = ((term3 x y) = (term3 y x)).
Proof. exact (eq_refl (term15 x y)). Qed.
Lemma lem1338655 (x : prod hreal hreal) : (term16 x) = (term7 x).
Proof. exact (fun_ext (fun y : prod hreal hreal => @lem1338654 y x)). Qed.
Lemma lem1338656 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1338657 (x : prod hreal hreal) : (term12 x) = (term9 x).
Proof. exact (MK_COMB (@lem1338656) (@lem1338655 x)). Qed.
Lemma lem1338658 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1338659 (x : prod hreal hreal) : (term17 x) = (term18 x).
Proof. exact (MK_COMB (@lem1338658) (@lem1338657 x)). Qed.
Lemma lem1338660 (y : real) (x : prod hreal hreal) : (term19 x y) = ((term20 x y) = (term21 y x)).
Proof. exact (eq_refl (term19 x y)). Qed.
Lemma lem1338661 (x : prod hreal hreal) : (term22 x) = (term14 x).
Proof. exact (fun_ext (fun y : real => @lem1338660 y x)). Qed.
Lemma lem1338662 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1338663 (x : prod hreal hreal) : (term13 x) = (term23 x).
Proof. exact (MK_COMB (@lem1338662) (@lem1338661 x)). Qed.
Lemma lem1338664 (x : prod hreal hreal) : ((term12 x) = (term13 x)) = ((term9 x) = (term23 x)).
Proof. exact (MK_COMB (@lem1338659 x) (@lem1338663 x)). Qed.
Lemma lem1338665 (x : prod hreal hreal) : (term9 x) = (term23 x).
Proof. exact (EQ_MP (@lem1338664 x) (@lem1338653 x)). Qed.
Lemma lem1338674 (x : prod hreal hreal) : (term8 x) = (term23 x).
Proof. exact (TRANS (@lem1338646 x) (@lem1338665 x)). Qed.
Lemma lem1338675 : term24 = term25.
Proof. exact (fun_ext (fun x : prod hreal hreal => @lem1338674 x)). Qed.
Lemma lem1338676 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1338677 : term26 = term27.
Proof. exact (MK_COMB (@lem1338676) (@lem1338675)). Qed.
Lemma lem1338683 (P : real -> Prop) : (term10 P) = (term11 P).
Proof. exact (EQ_MP (@lem1338106 P) (@lem1338105 P)). Qed.
Lemma lem1338684 : term28 = term29.
Proof. exact (@lem1338683 term30). Qed.
Lemma lem1338685 (x : prod hreal hreal) : (term31 x) = (term23 x).
Proof. exact (eq_refl (term31 x)). Qed.
Lemma lem1338686 : term32 = term25.
Proof. exact (fun_ext (fun x : prod hreal hreal => @lem1338685 x)). Qed.
Lemma lem1338687 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1338688 : term28 = term27.
Proof. exact (MK_COMB (@lem1338687) (@lem1338686)). Qed.
Lemma lem1338689 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1338690 : term33 = term34.
Proof. exact (MK_COMB (@lem1338689) (@lem1338688)). Qed.
Lemma lem1338691 (x : real) : (term35 x) = (term36 x).
Proof. exact (eq_refl (term35 x)). Qed.
Lemma lem1338692 : term37 = term30.
Proof. exact (fun_ext (fun x : real => @lem1338691 x)). Qed.
Lemma lem1338693 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1338694 : term29 = term38.
Proof. exact (MK_COMB (@lem1338693) (@lem1338692)). Qed.
Lemma lem1338695 : (term28 = term29) = (term27 = term38).
Proof. exact (MK_COMB (@lem1338690) (@lem1338694)). Qed.
Lemma lem1338696 : term27 = term38.
Proof. exact (EQ_MP (@lem1338695) (@lem1338684)). Qed.
Lemma lem1338711 : term26 = term38.
Proof. exact (TRANS (@lem1338677) (@lem1338696)). Qed.
Lemma lem1338712 : term38.
Proof. exact (EQ_MP (@lem1338711) (@lem1328389)). Qed.
