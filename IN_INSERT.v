Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import IN_INSERT_term_abbrevs.
Require Import DISJ_SYM_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Require Import thm3192217_spec.
Lemma lem3205520 {_83095 : Type'} : term0 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem3205521 {_83095 : Type'} (p : _83095 -> Prop) : term1 _83095 p.
Proof. exact (@lem3205520 _83095 p). Qed.
Lemma lem3205522 {_83095 : Type'} (p : _83095 -> Prop) : (term1 _83095 p) = (term2 _83095 p).
Proof. exact (eq_refl (term1 _83095 p)). Qed.
Lemma lem3205523 {_83095 : Type'} (p : _83095 -> Prop) : term2 _83095 p.
Proof. exact (EQ_MP (@lem3205522 _83095 p) (@lem3205521 _83095 p)). Qed.
Lemma lem3205524 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term3 _83095 p x.
Proof. exact (@lem3205523 _83095 p x). Qed.
Lemma lem3205525 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term3 _83095 p x) = ((term4 _83095 x p) = (p x)).
Proof. exact (eq_refl (term3 _83095 p x)). Qed.
Lemma lem3205534 (t1 : Prop) : term5 t1.
Proof. exact (@lem720 t1). Qed.
Lemma lem3205535 (t1 : Prop) : (term5 t1) = (term6 t1).
Proof. exact (eq_refl (term5 t1)). Qed.
Lemma lem3205536 (t1 : Prop) : term6 t1.
Proof. exact (EQ_MP (@lem3205535 t1) (@lem3205534 t1)). Qed.
Lemma lem3205537 (t1 : Prop) (t2 : Prop) : term7 t1 t2.
Proof. exact (@lem3205536 t1 t2). Qed.
Lemma lem3205538 (t2 : Prop) (t1 : Prop) : (term7 t1 t2) = ((t1 \/ t2) = (t2 \/ t1)).
Proof. exact (eq_refl (term7 t1 t2)). Qed.
Lemma lem3205557 (t2 : Prop) (t1 : Prop) : (t1 \/ t2) = (t2 \/ t1).
Proof. exact (EQ_MP (@lem3205538 t2 t1) (@lem3205537 t1 t2)). Qed.
Lemma lem3205558 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term8 A y x s) = (term9 A s x y).
Proof. exact (@lem3205557 (@IN A x s) (x = y)). Qed.
Lemma lem3205559 {A : Type'} (x : A) (y : A) (s : A -> Prop) : (term10 A x y s) = (term10 A x y s).
Proof. exact (eq_refl (term10 A x y s)). Qed.
Lemma lem3205560 {A : Type'} (s : A -> Prop) (x : A) (y : A) : ((term11 A x y s) = (term8 A y x s)) = ((term11 A x y s) = (term9 A s x y)).
Proof. exact (MK_COMB (@lem3205559 A x y s) (@lem3205558 A s x y)). Qed.
Lemma lem3205561 {A : Type'} (x : A) (y : A) : (term12 A y x) = (term13 A x y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3205560 A s x y)). Qed.
Lemma lem3205562 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3205563 {A : Type'} (x : A) (y : A) : (term14 A y x) = (term15 A x y).
Proof. exact (MK_COMB (@lem3205562 A) (@lem3205561 A x y)). Qed.
Lemma lem3205564 {A : Type'} (x : A) : (term16 A x) = (term17 A x).
Proof. exact (fun_ext (fun y : A => @lem3205563 A x y)). Qed.
Lemma lem3205565 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3205566 {A : Type'} (x : A) : (term18 A x) = (term19 A x).
Proof. exact (MK_COMB (@lem3205565 A) (@lem3205564 A x)). Qed.
Lemma lem3205567 {A : Type'} : (term20 A) = (term21 A).
Proof. exact (fun_ext (fun x : A => @lem3205566 A x)). Qed.
Lemma lem3205568 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3205569 {A : Type'} : (term22 A) = (term23 A).
Proof. exact (MK_COMB (@lem3205568 A) (@lem3205567 A)). Qed.
Lemma lem3205570 {A : Type'} : (term23 A) = (term22 A).
Proof. exact (SYM (@lem3205569 A)). Qed.
Lemma lem3205586 {A : Type'} (s : A -> Prop) (x : A) : (@INSERT A x s) = (term24 A s x).
Proof. exact (EQ_MP (@lem3192217 A s x) (@lem0)). Qed.
Lemma lem3205587 {A : Type'} (s : A -> Prop) (x : A) : (@INSERT A x s) = (term24 A s x).
Proof. exact (@lem3205586 A s x). Qed.
Lemma lem3205588 {A : Type'} (s : A -> Prop) (y : A) : (@INSERT A y s) = (term24 A s y).
Proof. exact (@lem3205587 A s y). Qed.
Lemma lem3205597 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem3205598 {A : Type'} (x : A) (s : A -> Prop) (y : A) : (term11 A x y s) = (term25 A x s y).
Proof. exact (MK_COMB (@lem3205597 A x) (@lem3205588 A s y)). Qed.
Lemma lem3205600 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term4 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3205525 _83095 p x) (@lem3205524 _83095 p x)). Qed.
Lemma lem3205601 {A : Type'} (p : A -> Prop) (x : A) : (term4 A x p) = (p x).
Proof. exact (@lem3205600 A p x). Qed.
Lemma lem3205602 {A : Type'} (s : A -> Prop) (y : A) (x : A) : (term26 A x s y) = (term27 A s y x).
Proof. exact (@lem3205601 A (term28 A s y) x). Qed.
Lemma lem3205603 {A : Type'} (s : A -> Prop) (y' : A) (y : A) : (term27 A s y y') = (term9 A s y' y).
Proof. exact (eq_refl (term27 A s y y')). Qed.
Lemma lem3205604 {A : Type'} (GEN_PVAR_5 : A) : (@SETSPEC A GEN_PVAR_5) = (@SETSPEC A GEN_PVAR_5).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_5)). Qed.
Lemma lem3205605 {A : Type'} (GEN_PVAR_5 : A) (s : A -> Prop) (y' : A) (y : A) : (term29 A GEN_PVAR_5 s y y') = (term30 A GEN_PVAR_5 s y' y).
Proof. exact (MK_COMB (@lem3205604 A GEN_PVAR_5) (@lem3205603 A s y' y)). Qed.
Lemma lem3205606 {A : Type'} (y' : A) : y' = y'.
Proof. exact (eq_refl y'). Qed.
Lemma lem3205607 {A : Type'} (GEN_PVAR_5 : A) (s : A -> Prop) (y : A) (y' : A) : (term31 A GEN_PVAR_5 s y y') = (term32 A GEN_PVAR_5 s y y').
Proof. exact (MK_COMB (@lem3205605 A GEN_PVAR_5 s y' y) (@lem3205606 A y')). Qed.
Lemma lem3205608 {A : Type'} (GEN_PVAR_5 : A) (s : A -> Prop) (y : A) : (term33 A GEN_PVAR_5 s y) = (term34 A GEN_PVAR_5 s y).
Proof. exact (fun_ext (fun y' : A => @lem3205607 A GEN_PVAR_5 s y y')). Qed.
Lemma lem3205609 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3205610 {A : Type'} (GEN_PVAR_5 : A) (s : A -> Prop) (y : A) : (term35 A GEN_PVAR_5 s y) = (term36 A GEN_PVAR_5 s y).
Proof. exact (MK_COMB (@lem3205609 A) (@lem3205608 A GEN_PVAR_5 s y)). Qed.
Lemma lem3205611 {A : Type'} (s : A -> Prop) (y : A) : (term37 A s y) = (term38 A s y).
Proof. exact (fun_ext (fun GEN_PVAR_5 : A => @lem3205610 A GEN_PVAR_5 s y)). Qed.
Lemma lem3205612 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem3205613 {A : Type'} (s : A -> Prop) (y : A) : (term39 A s y) = (term24 A s y).
Proof. exact (MK_COMB (@lem3205612 A) (@lem3205611 A s y)). Qed.
Lemma lem3205614 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem3205615 {A : Type'} (x : A) (s : A -> Prop) (y : A) : (term26 A x s y) = (term25 A x s y).
Proof. exact (MK_COMB (@lem3205614 A x) (@lem3205613 A s y)). Qed.
Lemma lem3205616 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3205617 {A : Type'} (x : A) (s : A -> Prop) (y : A) : (term40 A x s y) = (term41 A x s y).
Proof. exact (MK_COMB (@lem3205616) (@lem3205615 A x s y)). Qed.
Lemma lem3205618 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term27 A s y x) = (term9 A s x y).
Proof. exact (eq_refl (term27 A s y x)). Qed.
Lemma lem3205619 {A : Type'} (s : A -> Prop) (x : A) (y : A) : ((term26 A x s y) = (term27 A s y x)) = ((term25 A x s y) = (term9 A s x y)).
Proof. exact (MK_COMB (@lem3205617 A x s y) (@lem3205618 A s x y)). Qed.
Lemma lem3205620 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term25 A x s y) = (term9 A s x y).
Proof. exact (EQ_MP (@lem3205619 A s x y) (@lem3205602 A s y x)). Qed.
Lemma lem3205625 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term11 A x y s) = (term9 A s x y).
Proof. exact (TRANS (@lem3205598 A x s y) (@lem3205620 A s x y)). Qed.
Lemma lem3205626 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3205627 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term10 A x y s) = (term42 A s x y).
Proof. exact (MK_COMB (@lem3205626) (@lem3205625 A s x y)). Qed.
Lemma lem3205632 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term9 A s x y) = (term9 A s x y).
Proof. exact (eq_refl (term9 A s x y)). Qed.
Lemma lem3205633 {A : Type'} (s : A -> Prop) (x : A) (y : A) : ((term11 A x y s) = (term9 A s x y)) = ((term9 A s x y) = (term9 A s x y)).
Proof. exact (MK_COMB (@lem3205627 A s x y) (@lem3205632 A s x y)). Qed.
Lemma lem3205635 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3205636 (x : Prop) : (x = x) = True.
Proof. exact (@lem3205635 Prop x). Qed.
Lemma lem3205637 {A : Type'} (s : A -> Prop) (x : A) (y : A) : ((term9 A s x y) = (term9 A s x y)) = True.
Proof. exact (@lem3205636 (term9 A s x y)). Qed.
Lemma lem3205638 {A : Type'} (s : A -> Prop) (x : A) (y : A) : ((term11 A x y s) = (term9 A s x y)) = True.
Proof. exact (TRANS (@lem3205633 A s x y) (@lem3205637 A s x y)). Qed.
Lemma lem3205639 {A : Type'} (x : A) (y : A) : (term13 A x y) = (term43 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3205638 A s x y)). Qed.
Lemma lem3205640 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3205641 {A : Type'} (x : A) (y : A) : (term15 A x y) = (term44 A).
Proof. exact (MK_COMB (@lem3205640 A) (@lem3205639 A x y)). Qed.
Lemma lem3205643 {A : Type'} (t : Prop) : (term45 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3205644 {A : Type'} (t : Prop) : (term46 A t) = t.
Proof. exact (@lem3205643 (A -> Prop) t). Qed.
Lemma lem3205645 {A : Type'} : (term44 A) = True.
Proof. exact (@lem3205644 A True). Qed.
Lemma lem3205646 {A : Type'} (x : A) (y : A) : (term15 A x y) = True.
Proof. exact (TRANS (@lem3205641 A x y) (@lem3205645 A)). Qed.
Lemma lem3205647 {A : Type'} (x : A) : (term17 A x) = (term47 A).
Proof. exact (fun_ext (fun y : A => @lem3205646 A x y)). Qed.
Lemma lem3205648 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3205649 {A : Type'} (x : A) : (term19 A x) = (term48 A).
Proof. exact (MK_COMB (@lem3205648 A) (@lem3205647 A x)). Qed.
Lemma lem3205651 {A : Type'} (t : Prop) : (term45 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3205652 {A : Type'} (t : Prop) : (term45 A t) = t.
Proof. exact (@lem3205651 A t). Qed.
Lemma lem3205653 {A : Type'} : (term48 A) = True.
Proof. exact (@lem3205652 A True). Qed.
Lemma lem3205654 {A : Type'} (x : A) : (term19 A x) = True.
Proof. exact (TRANS (@lem3205649 A x) (@lem3205653 A)). Qed.
Lemma lem3205655 {A : Type'} : (term21 A) = (term47 A).
Proof. exact (fun_ext (fun x : A => @lem3205654 A x)). Qed.
Lemma lem3205656 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3205657 {A : Type'} : (term23 A) = (term48 A).
Proof. exact (MK_COMB (@lem3205656 A) (@lem3205655 A)). Qed.
Lemma lem3205659 {A : Type'} (t : Prop) : (term45 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3205660 {A : Type'} (t : Prop) : (term45 A t) = t.
Proof. exact (@lem3205659 A t). Qed.
Lemma lem3205661 {A : Type'} : (term48 A) = True.
Proof. exact (@lem3205660 A True). Qed.
Lemma lem3205662 {A : Type'} : (term23 A) = True.
Proof. exact (TRANS (@lem3205657 A) (@lem3205661 A)). Qed.
Lemma lem3205663 {A : Type'} : True = (term23 A).
Proof. exact (SYM (@lem3205662 A)). Qed.
Lemma lem3205664 {A : Type'} : term23 A.
Proof. exact (EQ_MP (@lem3205663 A) (@lem0)). Qed.
Lemma lem3205665 {A : Type'} : term22 A.
Proof. exact (EQ_MP (@lem3205570 A) (@lem3205664 A)). Qed.
