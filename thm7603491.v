Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7603491_term_abbrevs.
Require Import DIMINDEX_GE_1_spec.
Require Import IN_NUMSEG_spec.
Require Import LE_REFL_spec.
Require Import thm0_spec.
Require Import thm1842_spec.
Require Import thm7_spec.
Require Import thm9261_spec.
Require Import thm9306_spec.
Lemma lem7603429 {A : Type'} (s : A -> Prop) : term0 A s.
Proof. exact (@lem7594654 A s). Qed.
Lemma lem7603430 {A : Type'} (s : A -> Prop) : (term0 A s) = (term1 A s).
Proof. exact (eq_refl (term0 A s)). Qed.
Lemma lem7603431 {A : Type'} (s : A -> Prop) : term1 A s.
Proof. exact (EQ_MP (@lem7603430 A s) (@lem7603429 A s)). Qed.
Lemma lem7603432 {A : Type'} (s : A -> Prop) : (term1 A s) = ((term1 A s) = True).
Proof. exact (@lem7 (term1 A s)). Qed.
Lemma lem7603434 (n : nat) : term2 n.
Proof. exact (@lem91603 n). Qed.
Lemma lem7603435 (n : nat) : (term2 n) = (Peano.le n n).
Proof. exact (eq_refl (term2 n)). Qed.
Lemma lem7603436 (n : nat) : Peano.le n n.
Proof. exact (EQ_MP (@lem7603435 n) (@lem7603434 n)). Qed.
Lemma lem7603437 (n : nat) : (Peano.le n n) = ((Peano.le n n) = True).
Proof. exact (@lem7 (Peano.le n n)). Qed.
Lemma lem7603439 (m : nat) : term3 m.
Proof. exact (@lem5371273 m). Qed.
Lemma lem7603440 (m : nat) : (term3 m) = (term4 m).
Proof. exact (eq_refl (term3 m)). Qed.
Lemma lem7603441 (m : nat) : term4 m.
Proof. exact (EQ_MP (@lem7603440 m) (@lem7603439 m)). Qed.
Lemma lem7603442 (m : nat) (n : nat) : term5 m n.
Proof. exact (@lem7603441 m n). Qed.
Lemma lem7603443 (m : nat) (n : nat) : (term5 m n) = (term6 m n).
Proof. exact (eq_refl (term5 m n)). Qed.
Lemma lem7603444 (m : nat) (n : nat) : term6 m n.
Proof. exact (EQ_MP (@lem7603443 m n) (@lem7603442 m n)). Qed.
Lemma lem7603445 (m : nat) (n : nat) (p : nat) : term7 m n p.
Proof. exact (@lem7603444 m n p). Qed.
Lemma lem7603446 (m : nat) (p : nat) (n : nat) : (term7 m n p) = ((term8 p m n) = (term9 m p n)).
Proof. exact (eq_refl (term7 m n p)). Qed.
Lemma lem7603449 (m : nat) (p : nat) (n : nat) : (term8 p m n) = (term9 m p n).
Proof. exact (EQ_MP (@lem7603446 m p n) (@lem7603445 m n p)). Qed.
Lemma lem7603450 {A : Type'} : (term10 A) = (term11 A).
Proof. exact (@lem7603449 term12 term12 (@dimindex A (@UNIV A))). Qed.
Lemma lem7603454 (n : nat) : (Peano.le n n) = True.
Proof. exact (EQ_MP (@lem7603437 n) (@lem7603436 n)). Qed.
Lemma lem7603455 : term13 = True.
Proof. exact (@lem7603454 term12). Qed.
Lemma lem7603456 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7603457 : term14 = (and True).
Proof. exact (MK_COMB (@lem7603456) (@lem7603455)). Qed.
Lemma lem7603459 {A : Type'} (s : A -> Prop) : (term1 A s) = True.
Proof. exact (EQ_MP (@lem7603432 A s) (@lem7603431 A s)). Qed.
Lemma lem7603460 {A : Type'} (s : A -> Prop) : (term1 A s) = True.
Proof. exact (@lem7603459 A s). Qed.
Lemma lem7603461 {A : Type'} : (term15 A) = True.
Proof. exact (@lem7603460 A (@UNIV A)). Qed.
Lemma lem7603462 {A : Type'} : (term11 A) = (True /\ True).
Proof. exact (MK_COMB (@lem7603457) (@lem7603461 A)). Qed.
Lemma lem7603464 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7603465 : (True /\ True) = True.
Proof. exact (@lem7603464 True). Qed.
Lemma lem7603466 {A : Type'} : (term11 A) = True.
Proof. exact (TRANS (@lem7603462 A) (@lem7603465)). Qed.
Lemma lem7603467 {A : Type'} : (term10 A) = True.
Proof. exact (TRANS (@lem7603450 A) (@lem7603466 A)). Qed.
Lemma lem7603468 {A : Type'} : True = (term10 A).
Proof. exact (SYM (@lem7603467 A)). Qed.
Lemma lem7603469 {A : Type'} : term10 A.
Proof. exact (EQ_MP (@lem7603468 A) (@lem0)). Qed.
Lemma lem7603470 {A : Type'} : term16 A.
Proof. exact (ex_intro (term17 A) term12 (@lem7603469 A)). Qed.
Lemma lem7603472 {A : Type'} : (@ex A) = (term18 A).
Proof. exact (@lem9261 A (@lem9306 A)). Qed.
Lemma lem7603473 : (@ex nat) = term19.
Proof. exact (@lem7603472 nat). Qed.
Lemma lem7603474 {A : Type'} : (term17 A) = (term17 A).
Proof. exact (eq_refl (term17 A)). Qed.
Lemma lem7603475 {A : Type'} : (term16 A) = (term20 A).
Proof. exact (MK_COMB (@lem7603473) (@lem7603474 A)). Qed.
Lemma lem7603476 {A : Type'} : (term20 A) = (term21 A).
Proof. exact (eq_refl (term20 A)). Qed.
Lemma lem7603477 {A : Type'} : (term16 A) = (term21 A).
Proof. exact (TRANS (@lem7603475 A) (@lem7603476 A)). Qed.
Lemma lem7603478 {A : Type'} : term21 A.
Proof. exact (EQ_MP (@lem7603477 A) (@lem7603470 A)). Qed.
Lemma lem7603479 {A : Type'} (a : finite_image A) : (term22 A a) = a.
Proof. exact (@axiom_27 A a). Qed.
Lemma lem7603480 {A : Type'} (r : nat) : (term23 A r) = ((term24 A r) = r).
Proof. exact (@axiom_28 A r). Qed.
Lemma lem7603483 {A : Type'} (r : nat) : (term23 A r) = (term25 A r).
Proof. exact (eq_refl (term23 A r)). Qed.
Lemma lem7603484 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7603485 {A : Type'} (r : nat) : (term26 A r) = (term27 A r).
Proof. exact (MK_COMB (@lem7603484) (@lem7603483 A r)). Qed.
Lemma lem7603486 {A : Type'} (r : nat) : ((term24 A r) = r) = ((term24 A r) = r).
Proof. exact (eq_refl ((term24 A r) = r)). Qed.
Lemma lem7603487 {A : Type'} (r : nat) : ((term23 A r) = ((term24 A r) = r)) = ((term25 A r) = ((term24 A r) = r)).
Proof. exact (MK_COMB (@lem7603485 A r) (@lem7603486 A r)). Qed.
Lemma lem7603488 {A : Type'} (r : nat) : (term25 A r) = ((term24 A r) = r).
Proof. exact (EQ_MP (@lem7603487 A r) (@lem7603480 A r)). Qed.
Lemma lem7603489 {A : Type'} : term28 A.
Proof. exact (fun r : nat => @lem7603488 A r). Qed.
Lemma lem7603490 {A : Type'} : term29 A.
Proof. exact (fun a : finite_image A => @lem7603479 A a). Qed.
Lemma lem7603491 {A : Type'} : term30 A.
Proof. exact (conj (@lem7603490 A) (@lem7603489 A)). Qed.
