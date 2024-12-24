Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_ABS_SUP_LE_term_abbrevs.
Require Import REAL_BOUNDS_LE_spec.
Require Import REAL_SUP_BOUNDS_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm7_spec.
Lemma lem5166481 (x : real) (k : real) (h1 : (term0 x k) = (term1 x k)) : (term0 x k) = (term1 x k).
Proof. exact (h1). Qed.
Lemma lem5166482 (x : real) (k : real) (h1 : (term0 x k) = (term1 x k)) : (term1 x k) = (term0 x k).
Proof. exact (SYM (@lem5166481 x k h1)). Qed.
Lemma lem5166483 (x : real) (k : real) (h1 : (term1 x k) = (term0 x k)) : (term1 x k) = (term0 x k).
Proof. exact (h1). Qed.
Lemma lem5166484 (x : real) (k : real) (h1 : (term1 x k) = (term0 x k)) : (term0 x k) = (term1 x k).
Proof. exact (SYM (@lem5166483 x k h1)). Qed.
Lemma lem5166485 (x : real) (k : real) : ((term0 x k) = (term1 x k)) = ((term1 x k) = (term0 x k)).
Proof. exact (prop_ext (fun h1 : (term0 x k) = (term1 x k) => @lem5166482 x k h1) (fun h1 : (term1 x k) = (term0 x k) => @lem5166484 x k h1)). Qed.
Lemma lem5166486 (x : real) : (term2 x) = (term3 x).
Proof. exact (fun_ext (fun k : real => @lem5166485 x k)). Qed.
Lemma lem5166487 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5166488 (x : real) : (term4 x) = (term5 x).
Proof. exact (MK_COMB (@lem5166487) (@lem5166486 x)). Qed.
Lemma lem5166489 : term6 = term7.
Proof. exact (fun_ext (fun x : real => @lem5166488 x)). Qed.
Lemma lem5166490 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5166491 : term8 = term9.
Proof. exact (MK_COMB (@lem5166490) (@lem5166489)). Qed.
Lemma lem5166492 : term9.
Proof. exact (EQ_MP (@lem5166491) (@lem1553652)). Qed.
Lemma lem5166493 (s : real -> Prop) : term10 s.
Proof. exact (@lem5166478 s). Qed.
Lemma lem5166494 (s : real -> Prop) : (term10 s) = (term11 s).
Proof. exact (eq_refl (term10 s)). Qed.
Lemma lem5166495 (s : real -> Prop) : term11 s.
Proof. exact (EQ_MP (@lem5166494 s) (@lem5166493 s)). Qed.
Lemma lem5166496 (s : real -> Prop) (a : real) : term12 s a.
Proof. exact (@lem5166495 s a). Qed.
Lemma lem5166497 (a : real) (s : real -> Prop) : (term12 s a) = (term13 a s).
Proof. exact (eq_refl (term12 s a)). Qed.
Lemma lem5166498 (a : real) (s : real -> Prop) : term13 a s.
Proof. exact (EQ_MP (@lem5166497 a s) (@lem5166496 s a)). Qed.
Lemma lem5166499 (a : real) (s : real -> Prop) (b : real) : term14 a s b.
Proof. exact (@lem5166498 a s b). Qed.
Lemma lem5166500 (a : real) (s : real -> Prop) (b : real) : (term14 a s b) = (term15 a s b).
Proof. exact (eq_refl (term14 a s b)). Qed.
Lemma lem5166501 (a : real) (s : real -> Prop) (b : real) : term15 a s b.
Proof. exact (EQ_MP (@lem5166500 a s b) (@lem5166499 a s b)). Qed.
Lemma lem5166502 (a : real) (s : real -> Prop) (b : real) : (term15 a s b) = ((term15 a s b) = True).
Proof. exact (@lem7 (term15 a s b)). Qed.
Lemma lem5166504 (x : real) : term16 x.
Proof. exact (@lem5166492 x). Qed.
Lemma lem5166505 (x : real) : (term16 x) = (term5 x).
Proof. exact (eq_refl (term16 x)). Qed.
Lemma lem5166506 (x : real) : term5 x.
Proof. exact (EQ_MP (@lem5166505 x) (@lem5166504 x)). Qed.
Lemma lem5166507 (x : real) (k : real) : term17 x k.
Proof. exact (@lem5166506 x k). Qed.
Lemma lem5166508 (x : real) (k : real) : (term17 x k) = ((term1 x k) = (term0 x k)).
Proof. exact (eq_refl (term17 x k)). Qed.
Lemma lem5166531 (x : real) (k : real) : (term1 x k) = (term0 x k).
Proof. exact (EQ_MP (@lem5166508 x k) (@lem5166507 x k)). Qed.
Lemma lem5166532 (x : real) (a : real) : (term1 x a) = (term0 x a).
Proof. exact (@lem5166531 x a). Qed.
Lemma lem5166535 (x : real) (s : real -> Prop) : (term18 x s) = (term18 x s).
Proof. exact (eq_refl (term18 x s)). Qed.
Lemma lem5166536 (s : real -> Prop) (x : real) (a : real) : (term19 s x a) = (term20 s x a).
Proof. exact (MK_COMB (@lem5166535 x s) (@lem5166532 x a)). Qed.
Lemma lem5166539 (s : real -> Prop) (a : real) : (term21 s a) = (term22 s a).
Proof. exact (fun_ext (fun x : real => @lem5166536 s x a)). Qed.
Lemma lem5166540 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5166541 (s : real -> Prop) (a : real) : (term23 s a) = (term24 s a).
Proof. exact (MK_COMB (@lem5166540) (@lem5166539 s a)). Qed.
Lemma lem5166546 (s : real -> Prop) : (term25 s) = (term25 s).
Proof. exact (eq_refl (term25 s)). Qed.
Lemma lem5166547 (s : real -> Prop) (a : real) : (term26 s a) = (term27 s a).
Proof. exact (MK_COMB (@lem5166546 s) (@lem5166541 s a)). Qed.
Lemma lem5166550 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5166551 (s : real -> Prop) (a : real) : (term28 s a) = (term29 s a).
Proof. exact (MK_COMB (@lem5166550) (@lem5166547 s a)). Qed.
Lemma lem5166553 (x : real) (k : real) : (term1 x k) = (term0 x k).
Proof. exact (EQ_MP (@lem5166508 x k) (@lem5166507 x k)). Qed.
Lemma lem5166554 (s : real -> Prop) (a : real) : (term30 s a) = (term31 s a).
Proof. exact (@lem5166553 (sup s) a). Qed.
Lemma lem5166557 (s : real -> Prop) (a : real) : (term32 s a) = (term33 s a).
Proof. exact (MK_COMB (@lem5166551 s a) (@lem5166554 s a)). Qed.
Lemma lem5166559 (a : real) (s : real -> Prop) (b : real) : (term15 a s b) = True.
Proof. exact (EQ_MP (@lem5166502 a s b) (@lem5166501 a s b)). Qed.
Lemma lem5166560 (s : real -> Prop) (a : real) : (term33 s a) = True.
Proof. exact (@lem5166559 (real_neg a) s a). Qed.
Lemma lem5166561 (s : real -> Prop) (a : real) : (term32 s a) = True.
Proof. exact (TRANS (@lem5166557 s a) (@lem5166560 s a)). Qed.
Lemma lem5166562 (s : real -> Prop) : (term34 s) = term35.
Proof. exact (fun_ext (fun a : real => @lem5166561 s a)). Qed.
Lemma lem5166563 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5166564 (s : real -> Prop) : (term36 s) = term37.
Proof. exact (MK_COMB (@lem5166563) (@lem5166562 s)). Qed.
Lemma lem5166566 {A : Type'} (t : Prop) : (term38 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5166567 (t : Prop) : (term39 t) = t.
Proof. exact (@lem5166566 real t). Qed.
Lemma lem5166568 : term37 = True.
Proof. exact (@lem5166567 True). Qed.
Lemma lem5166569 (s : real -> Prop) : (term36 s) = True.
Proof. exact (TRANS (@lem5166564 s) (@lem5166568)). Qed.
Lemma lem5166570 : term40 = term41.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5166569 s)). Qed.
Lemma lem5166571 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5166572 : term42 = term43.
Proof. exact (MK_COMB (@lem5166571) (@lem5166570)). Qed.
Lemma lem5166574 {A : Type'} (t : Prop) : (term38 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5166575 (t : Prop) : (term44 t) = t.
Proof. exact (@lem5166574 (real -> Prop) t). Qed.
Lemma lem5166576 : term43 = True.
Proof. exact (@lem5166575 True). Qed.
Lemma lem5166577 : term42 = True.
Proof. exact (TRANS (@lem5166572) (@lem5166576)). Qed.
Lemma lem5166578 : True = term42.
Proof. exact (SYM (@lem5166577)). Qed.
Lemma lem5166579 : term42.
Proof. exact (EQ_MP (@lem5166578) (@lem0)). Qed.
