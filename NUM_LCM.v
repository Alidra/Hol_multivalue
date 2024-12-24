Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NUM_LCM_term_abbrevs.
Require Import INT_LCM_POS_spec.
Require Import NUM_OF_INT_spec.
Require Import num_lcm_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm7_spec.
Lemma lem3070445 (x : int) (h1 : (term0 x) = ((term1 x) = x)) : (term0 x) = ((term1 x) = x).
Proof. exact (h1). Qed.
Lemma lem3070446 (x : int) (h1 : (term0 x) = ((term1 x) = x)) : ((term1 x) = x) = (term0 x).
Proof. exact (SYM (@lem3070445 x h1)). Qed.
Lemma lem3070447 (x : int) (h1 : ((term1 x) = x) = (term0 x)) : ((term1 x) = x) = (term0 x).
Proof. exact (h1). Qed.
Lemma lem3070448 (x : int) (h1 : ((term1 x) = x) = (term0 x)) : (term0 x) = ((term1 x) = x).
Proof. exact (SYM (@lem3070447 x h1)). Qed.
Lemma lem3070449 (x : int) : ((term0 x) = ((term1 x) = x)) = (((term1 x) = x) = (term0 x)).
Proof. exact (prop_ext (fun h1 : (term0 x) = ((term1 x) = x) => @lem3070446 x h1) (fun h1 : ((term1 x) = x) = (term0 x) => @lem3070448 x h1)). Qed.
Lemma lem3070450 : term2 = term3.
Proof. exact (fun_ext (fun x : int => @lem3070449 x)). Qed.
Lemma lem3070451 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem3070452 : term4 = term5.
Proof. exact (MK_COMB (@lem3070451) (@lem3070450)). Qed.
Lemma lem3070453 : term5.
Proof. exact (EQ_MP (@lem3070452) (@lem2835223)). Qed.
Lemma lem3070454 (m : int) : term6 m.
Proof. exact (@lem2806319 m). Qed.
Lemma lem3070455 (m : int) : (term6 m) = (term7 m).
Proof. exact (eq_refl (term6 m)). Qed.
Lemma lem3070456 (m : int) : term7 m.
Proof. exact (EQ_MP (@lem3070455 m) (@lem3070454 m)). Qed.
Lemma lem3070457 (m : int) (n : int) : term8 m n.
Proof. exact (@lem3070456 m n). Qed.
Lemma lem3070458 (m : int) (n : int) : (term8 m n) = (term9 m n).
Proof. exact (eq_refl (term8 m n)). Qed.
Lemma lem3070459 (m : int) (n : int) : term9 m n.
Proof. exact (EQ_MP (@lem3070458 m n) (@lem3070457 m n)). Qed.
Lemma lem3070460 (m : int) (n : int) : (term9 m n) = ((term9 m n) = True).
Proof. exact (@lem7 (term9 m n)). Qed.
Lemma lem3070462 (x : int) : term10 x.
Proof. exact (@lem3070453 x). Qed.
Lemma lem3070463 (x : int) : (term10 x) = (((term1 x) = x) = (term0 x)).
Proof. exact (eq_refl (term10 x)). Qed.
Lemma lem3070465 (a : nat) : term11 a.
Proof. exact (@lem2840178 a). Qed.
Lemma lem3070466 (a : nat) : (term11 a) = (term12 a).
Proof. exact (eq_refl (term11 a)). Qed.
Lemma lem3070467 (a : nat) : term12 a.
Proof. exact (EQ_MP (@lem3070466 a) (@lem3070465 a)). Qed.
Lemma lem3070468 (a : nat) (b : nat) : term13 a b.
Proof. exact (@lem3070467 a b). Qed.
Lemma lem3070469 (a : nat) (b : nat) : (term13 a b) = ((term14 a b) = (term15 a b)).
Proof. exact (eq_refl (term13 a b)). Qed.
Lemma lem3070482 (a : nat) (b : nat) : (term14 a b) = (term15 a b).
Proof. exact (EQ_MP (@lem3070469 a b) (@lem3070468 a b)). Qed.
Lemma lem3070483 : int_of_num = int_of_num.
Proof. exact (eq_refl int_of_num). Qed.
Lemma lem3070484 (a : nat) (b : nat) : (term16 a b) = (term17 a b).
Proof. exact (MK_COMB (@lem3070483) (@lem3070482 a b)). Qed.
Lemma lem3070485 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem3070486 (a : nat) (b : nat) : (term18 a b) = (term19 a b).
Proof. exact (MK_COMB (@lem3070485) (@lem3070484 a b)). Qed.
Lemma lem3070487 (a : nat) (b : nat) : (term20 a b) = (term20 a b).
Proof. exact (eq_refl (term20 a b)). Qed.
Lemma lem3070488 (a : nat) (b : nat) : ((term16 a b) = (term20 a b)) = ((term17 a b) = (term20 a b)).
Proof. exact (MK_COMB (@lem3070486 a b) (@lem3070487 a b)). Qed.
Lemma lem3070490 (x : int) : ((term1 x) = x) = (term0 x).
Proof. exact (EQ_MP (@lem3070463 x) (@lem3070462 x)). Qed.
Lemma lem3070491 (a : nat) (b : nat) : ((term17 a b) = (term20 a b)) = (term21 a b).
Proof. exact (@lem3070490 (term20 a b)). Qed.
Lemma lem3070493 (m : int) (n : int) : (term9 m n) = True.
Proof. exact (EQ_MP (@lem3070460 m n) (@lem3070459 m n)). Qed.
Lemma lem3070494 (a : nat) (b : nat) : (term21 a b) = True.
Proof. exact (@lem3070493 (int_of_num a) (int_of_num b)). Qed.
Lemma lem3070495 (a : nat) (b : nat) : ((term17 a b) = (term20 a b)) = True.
Proof. exact (TRANS (@lem3070491 a b) (@lem3070494 a b)). Qed.
Lemma lem3070496 (a : nat) (b : nat) : ((term16 a b) = (term20 a b)) = True.
Proof. exact (TRANS (@lem3070488 a b) (@lem3070495 a b)). Qed.
Lemma lem3070497 (a : nat) : (term22 a) = term23.
Proof. exact (fun_ext (fun b : nat => @lem3070496 a b)). Qed.
Lemma lem3070498 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3070499 (a : nat) : (term24 a) = term25.
Proof. exact (MK_COMB (@lem3070498) (@lem3070497 a)). Qed.
Lemma lem3070501 {A : Type'} (t : Prop) : (term26 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3070502 (t : Prop) : (term27 t) = t.
Proof. exact (@lem3070501 nat t). Qed.
Lemma lem3070503 : term25 = True.
Proof. exact (@lem3070502 True). Qed.
Lemma lem3070504 (a : nat) : (term24 a) = True.
Proof. exact (TRANS (@lem3070499 a) (@lem3070503)). Qed.
Lemma lem3070505 : term28 = term23.
Proof. exact (fun_ext (fun a : nat => @lem3070504 a)). Qed.
Lemma lem3070506 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3070507 : term29 = term25.
Proof. exact (MK_COMB (@lem3070506) (@lem3070505)). Qed.
Lemma lem3070509 {A : Type'} (t : Prop) : (term26 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3070510 (t : Prop) : (term27 t) = t.
Proof. exact (@lem3070509 nat t). Qed.
Lemma lem3070511 : term25 = True.
Proof. exact (@lem3070510 True). Qed.
Lemma lem3070512 : term29 = True.
Proof. exact (TRANS (@lem3070507) (@lem3070511)). Qed.
Lemma lem3070513 : True = term29.
Proof. exact (SYM (@lem3070512)). Qed.
Lemma lem3070514 : term29.
Proof. exact (EQ_MP (@lem3070513) (@lem0)). Qed.
