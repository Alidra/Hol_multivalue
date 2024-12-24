Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import WF_SUBSET_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import WF_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm19490_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Lemma lem358373 {A : Type'} (lt2 : type1402 A) : term0 A lt2.
Proof. exact (@lem303045 A lt2). Qed.
Lemma lem358374 {A : Type'} (lt2 : type1402 A) : (term0 A lt2) = ((@WF A lt2) = (term1 A lt2)).
Proof. exact (eq_refl (term0 A lt2)). Qed.
Lemma lem358376 {A : Type'} (lt2 : type1402 A) (lt3 : type1402 A) (h1 : term2 A lt2 lt3) : term2 A lt2 lt3.
Proof. exact (h1). Qed.
Lemma lem358377 {A : Type'} (lt3 : type1402 A) (h1 : @WF A lt3) : @WF A lt3.
Proof. exact (h1). Qed.
Lemma lem358378 {A : Type'} (lt2 : type1402 A) (lt3 : type1402 A) (h1 : term3 A lt2 lt3) : term3 A lt2 lt3.
Proof. exact (h1). Qed.
Lemma lem358382 {A : Type'} (lt2 : type1402 A) : (@WF A lt2) = (term1 A lt2).
Proof. exact (EQ_MP (@lem358374 A lt2) (@lem358373 A lt2)). Qed.
Lemma lem358383 {A : Type'} (lt2 : type1402 A) : (@WF A lt2) = (term1 A lt2).
Proof. exact (@lem358382 A lt2). Qed.
Lemma lem358384 {A : Type'} (lt3 : type1402 A) : (@WF A lt3) = (term1 A lt3).
Proof. exact (@lem358383 A lt3). Qed.
Lemma lem358407 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem358408 {A : Type'} (lt3 : type1402 A) : (term4 A lt3) = (term5 A lt3).
Proof. exact (MK_COMB (@lem358407) (@lem358384 A lt3)). Qed.
Lemma lem358410 {A : Type'} (lt2 : type1402 A) : (@WF A lt2) = (term1 A lt2).
Proof. exact (EQ_MP (@lem358374 A lt2) (@lem358373 A lt2)). Qed.
Lemma lem358411 {A : Type'} (lt2 : type1402 A) : (@WF A lt2) = (term1 A lt2).
Proof. exact (@lem358410 A lt2). Qed.
Lemma lem358434 {A : Type'} (lt3 : type1402 A) (lt2 : type1402 A) : (term6 A lt3 lt2) = (term7 A lt3 lt2).
Proof. exact (MK_COMB (@lem358408 A lt3) (@lem358411 A lt2)). Qed.
Lemma lem358437 {A : Type'} (lt3 : type1402 A) (lt2 : type1402 A) : (term7 A lt3 lt2) = (term6 A lt3 lt2).
Proof. exact (SYM (@lem358434 A lt3 lt2)). Qed.
Lemma lem358438 {A : Type'} (lt3 : type1402 A) (h1 : term1 A lt3) : term1 A lt3.
Proof. exact (h1). Qed.
Lemma lem358439 {A : Type'} (P : A -> Prop) (h1 : term8 A P) : term8 A P.
Proof. exact (h1). Qed.
Lemma lem358448 {A : Type'} (P : A -> Prop) (lt3 : type1402 A) (h1 : term1 A lt3) : term9 A lt3 P.
Proof. exact (@lem358438 A lt3 h1 P). Qed.
Lemma lem358449 {A : Type'} (lt3 : type1402 A) (P : A -> Prop) : (term9 A lt3 P) = (term10 A lt3 P).
Proof. exact (eq_refl (term9 A lt3 P)). Qed.
Lemma lem358452 {A : Type'} (P : A -> Prop) (lt3 : type1402 A) (h1 : term1 A lt3) : term10 A lt3 P.
Proof. exact (EQ_MP (@lem358449 A lt3 P) (@lem358448 A P lt3 h1)). Qed.
Lemma lem358453 {A : Type'} (P : A -> Prop) (lt3 : type1402 A) (h1 : term1 A lt3) : term10 A lt3 P.
Proof. exact (@lem358452 A P lt3 h1). Qed.
Lemma lem358454 {A : Type'} (lt3 : type1402 A) (P : A -> Prop) (h1 : term1 A lt3) (h2 : term8 A P) : term11 A lt3 P.
Proof. exact (@lem358453 A P lt3 h1 (@lem358439 A P h2)). Qed.
Lemma lem358456 (p : Prop) : p = (term12 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem358457 {A : Type'} (lt3 : type1402 A) (lt2 : type1402 A) (P : A -> Prop) : (term13 A lt3 lt2 P) = (term14 A lt3 lt2 P).
Proof. exact (@lem358456 (term13 A lt3 lt2 P)). Qed.
Lemma lem358458 {A : Type'} (lt3 : type1402 A) (lt2 : type1402 A) (P : A -> Prop) : (term14 A lt3 lt2 P) = (term13 A lt3 lt2 P).
Proof. exact (SYM (@lem358457 A lt3 lt2 P)). Qed.
Lemma lem358459 {A : Type'} (lt3 : type1402 A) (lt2 : type1402 A) (P : A -> Prop) (h1 : term15 A lt3 lt2 P) : term15 A lt3 lt2 P.
Proof. exact (h1). Qed.
Lemma lem358462 {A : Type'} (lt3 : type1402 A) (lt2 : type1402 A) (P : A -> Prop) (h1 : term14 A lt3 lt2 P) : term14 A lt3 lt2 P.
Proof. exact (h1). Qed.
Lemma lem358463 {A : Type'} (lt3 : type1402 A) (lt2 : type1402 A) (P : A -> Prop) : term16 A lt3 lt2 P.
Proof. exact (fun h0 : term14 A lt3 lt2 P => @lem358462 A lt3 lt2 P h0). Qed.
Lemma lem358464 {A : Type'} (lt3 : type1402 A) (lt2 : type1402 A) (P : A -> Prop) (h1 : term16 A lt3 lt2 P) : term16 A lt3 lt2 P.
Proof. exact (h1). Qed.
Lemma lem358465 {A : Type'} (lt3 : type1402 A) (lt2 : type1402 A) (P : A -> Prop) (h1 : term14 A lt3 lt2 P) : term14 A lt3 lt2 P.
Proof. exact (h1). Qed.
Lemma lem358466 {A : Type'} (lt3 : type1402 A) (lt2 : type1402 A) (P : A -> Prop) (h1 : term14 A lt3 lt2 P) (h2 : term16 A lt3 lt2 P) : term14 A lt3 lt2 P.
Proof. exact (@lem358464 A lt3 lt2 P h2 (@lem358465 A lt3 lt2 P h1)). Qed.
Lemma lem358467 {A : Type'} (lt3 : type1402 A) (lt2 : type1402 A) (P : A -> Prop) (h1 : term14 A lt3 lt2 P) : term17 A lt3 lt2 P.
Proof. exact (fun h0 : term16 A lt3 lt2 P => @lem358466 A lt3 lt2 P h1 h0). Qed.
Lemma lem358468 {A : Type'} (lt3 : type1402 A) (lt2 : type1402 A) (P : A -> Prop) (h1 : term16 A lt3 lt2 P) : term16 A lt3 lt2 P.
Proof. exact (h1). Qed.
Lemma lem358469 {A : Type'} (lt3 : type1402 A) (lt2 : type1402 A) (P : A -> Prop) (h1 : term14 A lt3 lt2 P) (h2 : term16 A lt3 lt2 P) : term14 A lt3 lt2 P.
Proof. exact (@lem358467 A lt3 lt2 P h1 (@lem358468 A lt3 lt2 P h2)). Qed.
Lemma lem358470 {A : Type'} (lt3 : type1402 A) (lt2 : type1402 A) (P : A -> Prop) (h1 : term16 A lt3 lt2 P) : term16 A lt3 lt2 P.
Proof. exact (fun h0 : term14 A lt3 lt2 P => @lem358469 A lt3 lt2 P h0 h1). Qed.
Lemma lem358471 {A : Type'} (lt3 : type1402 A) (lt2 : type1402 A) (P : A -> Prop) : term18 A lt3 lt2 P.
Proof. exact (fun h0 : term16 A lt3 lt2 P => @lem358470 A lt3 lt2 P h0). Qed.
Lemma lem358474 {A : Type'} (lt3 : type1402 A) (lt2 : type1402 A) (P : A -> Prop) : term16 A lt3 lt2 P.
Proof. exact (@lem358471 A lt3 lt2 P (@lem358463 A lt3 lt2 P)). Qed.
Lemma lem358475 {A : Type'} (lt3 : type1402 A) (lt2 : type1402 A) (P : A -> Prop) : term16 A lt3 lt2 P.
Proof. exact (@lem358474 A lt3 lt2 P). Qed.
Lemma lem358489 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem358490 {A : Type'} (lt3 : type1402 A) (lt2 : type1402 A) (P : A -> Prop) : (term14 A lt3 lt2 P) = (term19 A lt3 lt2 P).
Proof. exact (@lem358489 (term15 A lt3 lt2 P)). Qed.
Lemma lem358492 (t : Prop) : (term20 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem358493 {A : Type'} (lt3 : type1402 A) (lt2 : type1402 A) (P : A -> Prop) : (term19 A lt3 lt2 P) = (term13 A lt3 lt2 P).
Proof. exact (@lem358492 (term13 A lt3 lt2 P)). Qed.
Lemma lem358496 {A : Type'} (lt3 : type1402 A) (lt2 : type1402 A) (P : A -> Prop) : (term14 A lt3 lt2 P) = (term13 A lt3 lt2 P).
Proof. exact (TRANS (@lem358490 A lt3 lt2 P) (@lem358493 A lt3 lt2 P)). Qed.
Lemma lem358581 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term21 A lt2 P) = (term22 A lt2 P).
Proof. exact (fun_ext (fun lt3 : type1402 A => @lem358496 A lt3 lt2 P)). Qed.
Lemma lem358582 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem358583 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term23 A lt2 P) = (term24 A lt2 P).
Proof. exact (MK_COMB (@lem358582 A) (@lem358581 A lt2 P)). Qed.
Lemma lem358588 {A : Type'} (P : A -> Prop) : (term25 A P) = (term26 A P).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem358583 A lt2 P)). Qed.
Lemma lem358589 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem358590 {A : Type'} (P : A -> Prop) : (term27 A P) = (term28 A P).
Proof. exact (MK_COMB (@lem358589 A) (@lem358588 A P)). Qed.
Lemma lem358595 {A : Type'} : (term29 A) = (term30 A).
Proof. exact (fun_ext (fun P : A -> Prop => @lem358590 A P)). Qed.
Lemma lem358596 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem358605 {A : Type'} : (term31 A) = (term32 A).
Proof. exact (MK_COMB (@lem358596 A) (@lem358595 A)). Qed.
Lemma lem358612 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term33 A lt2 x P y) = (term33 A lt2 x P y).
Proof. exact (eq_refl (term33 A lt2 x P y)). Qed.
Lemma lem358613 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term34 A lt2 x P) = (term34 A lt2 x P).
Proof. exact (fun_ext (fun y : A => @lem358612 A lt2 x P y)). Qed.
Lemma lem358614 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem358615 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term35 A lt2 x P) = (term35 A lt2 x P).
Proof. exact (MK_COMB (@lem358614 A) (@lem358613 A lt2 x P)). Qed.
Lemma lem358618 {A : Type'} (P : A -> Prop) (x : A) : (term36 A P x) = (term36 A P x).
Proof. exact (eq_refl (term36 A P x)). Qed.
Lemma lem358619 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term37 A lt2 x P) = (term37 A lt2 x P).
Proof. exact (MK_COMB (@lem358618 A P x) (@lem358615 A lt2 x P)). Qed.
Lemma lem358620 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term38 A lt2 P) = (term38 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem358619 A lt2 x P)). Qed.
Lemma lem358621 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem358622 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term11 A lt2 P) = (term11 A lt2 P).
Proof. exact (MK_COMB (@lem358621 A) (@lem358620 A lt2 P)). Qed.
Lemma lem358629 {A : Type'} (lt3 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term33 A lt3 x P y) = (term33 A lt3 x P y).
Proof. exact (eq_refl (term33 A lt3 x P y)). Qed.
Lemma lem358630 {A : Type'} (lt3 : type1402 A) (x : A) (P : A -> Prop) : (term34 A lt3 x P) = (term34 A lt3 x P).
Proof. exact (fun_ext (fun y : A => @lem358629 A lt3 x P y)). Qed.
Lemma lem358631 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem358632 {A : Type'} (lt3 : type1402 A) (x : A) (P : A -> Prop) : (term35 A lt3 x P) = (term35 A lt3 x P).
Proof. exact (MK_COMB (@lem358631 A) (@lem358630 A lt3 x P)). Qed.
Lemma lem358635 {A : Type'} (P : A -> Prop) (x : A) : (term36 A P x) = (term36 A P x).
Proof. exact (eq_refl (term36 A P x)). Qed.
Lemma lem358636 {A : Type'} (lt3 : type1402 A) (x : A) (P : A -> Prop) : (term37 A lt3 x P) = (term37 A lt3 x P).
Proof. exact (MK_COMB (@lem358635 A P x) (@lem358632 A lt3 x P)). Qed.
Lemma lem358637 {A : Type'} (lt3 : type1402 A) (P : A -> Prop) : (term38 A lt3 P) = (term38 A lt3 P).
Proof. exact (fun_ext (fun x : A => @lem358636 A lt3 x P)). Qed.
Lemma lem358638 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem358639 {A : Type'} (lt3 : type1402 A) (P : A -> Prop) : (term11 A lt3 P) = (term11 A lt3 P).
Proof. exact (MK_COMB (@lem358638 A) (@lem358637 A lt3 P)). Qed.
Lemma lem358640 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem358641 {A : Type'} (lt3 : type1402 A) (P : A -> Prop) : (term39 A lt3 P) = (term39 A lt3 P).
Proof. exact (MK_COMB (@lem358640) (@lem358639 A lt3 P)). Qed.
Lemma lem358642 {A : Type'} (lt3 : type1402 A) (lt2 : type1402 A) (P : A -> Prop) : (term40 A lt3 lt2 P) = (term40 A lt3 lt2 P).
Proof. exact (MK_COMB (@lem358641 A lt3 P) (@lem358622 A lt2 P)). Qed.
Lemma lem358647 {A : Type'} (lt2 : type1402 A) (lt3 : type1402 A) (x : A) (y : A) : (term41 A lt2 lt3 x y) = (term41 A lt2 lt3 x y).
Proof. exact (eq_refl (term41 A lt2 lt3 x y)). Qed.
Lemma lem358648 {A : Type'} (lt2 : type1402 A) (lt3 : type1402 A) (x : A) : (term42 A lt2 lt3 x) = (term42 A lt2 lt3 x).
Proof. exact (fun_ext (fun y : A => @lem358647 A lt2 lt3 x y)). Qed.
Lemma lem358649 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem358650 {A : Type'} (lt2 : type1402 A) (lt3 : type1402 A) (x : A) : (term43 A lt2 lt3 x) = (term43 A lt2 lt3 x).
Proof. exact (MK_COMB (@lem358649 A) (@lem358648 A lt2 lt3 x)). Qed.
Lemma lem358651 {A : Type'} (lt2 : type1402 A) (lt3 : type1402 A) : (term44 A lt2 lt3) = (term44 A lt2 lt3).
Proof. exact (fun_ext (fun x : A => @lem358650 A lt2 lt3 x)). Qed.
Lemma lem358652 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem358653 {A : Type'} (lt2 : type1402 A) (lt3 : type1402 A) : (term3 A lt2 lt3) = (term3 A lt2 lt3).
Proof. exact (MK_COMB (@lem358652 A) (@lem358651 A lt2 lt3)). Qed.
Lemma lem358654 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem358655 {A : Type'} (lt2 : type1402 A) (lt3 : type1402 A) : (term45 A lt2 lt3) = (term45 A lt2 lt3).
Proof. exact (MK_COMB (@lem358654) (@lem358653 A lt2 lt3)). Qed.
Lemma lem358656 {A : Type'} (lt3 : type1402 A) (lt2 : type1402 A) (P : A -> Prop) : (term13 A lt3 lt2 P) = (term13 A lt3 lt2 P).
Proof. exact (MK_COMB (@lem358655 A lt2 lt3) (@lem358642 A lt3 lt2 P)). Qed.
Lemma lem358657 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term22 A lt2 P) = (term22 A lt2 P).
Proof. exact (fun_ext (fun lt3 : type1402 A => @lem358656 A lt3 lt2 P)). Qed.
Lemma lem358658 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem358659 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term24 A lt2 P) = (term24 A lt2 P).
Proof. exact (MK_COMB (@lem358658 A) (@lem358657 A lt2 P)). Qed.
Lemma lem358660 {A : Type'} (P : A -> Prop) : (term26 A P) = (term26 A P).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem358659 A lt2 P)). Qed.
Lemma lem358661 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem358662 {A : Type'} (P : A -> Prop) : (term28 A P) = (term28 A P).
Proof. exact (MK_COMB (@lem358661 A) (@lem358660 A P)). Qed.
Lemma lem358663 {A : Type'} : (term30 A) = (term30 A).
Proof. exact (fun_ext (fun P : A -> Prop => @lem358662 A P)). Qed.
Lemma lem358664 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem358665 {A : Type'} : (term32 A) = (term32 A).
Proof. exact (MK_COMB (@lem358664 A) (@lem358663 A)). Qed.
Lemma lem358736 {A : Type'} : (term31 A) = (term32 A).
Proof. exact (TRANS (@lem358605 A) (@lem358665 A)). Qed.
Lemma lem358737 {A : Type'} : (term32 A) = (term31 A).
Proof. exact (SYM (@lem358736 A)). Qed.
Lemma lem358738 {A : Type'} (lt2 : type1402 A) (lt3 : type1402 A) (h1 : term3 A lt2 lt3) : term3 A lt2 lt3.
Proof. exact (h1). Qed.
Lemma lem358739 {A : Type'} (lt3 : type1402 A) (P : A -> Prop) (h1 : term11 A lt3 P) : term11 A lt3 P.
Proof. exact (h1). Qed.
Lemma lem358741 (p : Prop) : p = (term12 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem358742 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term11 A lt2 P) = (term46 A lt2 P).
Proof. exact (@lem358741 (term11 A lt2 P)). Qed.
Lemma lem358743 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term46 A lt2 P) = (term11 A lt2 P).
Proof. exact (SYM (@lem358742 A lt2 P)). Qed.
Lemma lem358744 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term47 A lt2 P) : term47 A lt2 P.
Proof. exact (h1). Qed.
Lemma lem358751 {A : Type'} (lt2 : type1402 A) (lt3 : type1402 A) (x : A) (y : A) : (term41 A lt2 lt3 x y) = (term48 A lt2 lt3 x y).
Proof. exact (@lem17265 (lt2 x y) (lt3 x y)). Qed.
Lemma lem358752 {A : Type'} (lt2 : type1402 A) (lt3 : type1402 A) (x : A) : (term42 A lt2 lt3 x) = (term49 A lt2 lt3 x).
Proof. exact (fun_ext (fun y : A => @lem358751 A lt2 lt3 x y)). Qed.
Lemma lem358753 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem358754 {A : Type'} (lt2 : type1402 A) (lt3 : type1402 A) (x : A) : (term43 A lt2 lt3 x) = (term50 A lt2 lt3 x).
Proof. exact (MK_COMB (@lem358753 A) (@lem358752 A lt2 lt3 x)). Qed.
Lemma lem358755 {A : Type'} (lt2 : type1402 A) (lt3 : type1402 A) : (term44 A lt2 lt3) = (term51 A lt2 lt3).
Proof. exact (fun_ext (fun x : A => @lem358754 A lt2 lt3 x)). Qed.
Lemma lem358756 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem358813 {A : Type'} (lt2 : type1402 A) (lt3 : type1402 A) : (term3 A lt2 lt3) = (term52 A lt2 lt3).
Proof. exact (MK_COMB (@lem358756 A) (@lem358755 A lt2 lt3)). Qed.
Lemma lem358814 {A : Type'} (lt2 : type1402 A) (lt3 : type1402 A) (h1 : term3 A lt2 lt3) : term52 A lt2 lt3.
Proof. exact (EQ_MP (@lem358813 A lt2 lt3) (@lem358738 A lt2 lt3 h1)). Qed.
Lemma lem358822 {A : Type'} (lt3 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term33 A lt3 x P y) = (term53 A lt3 x P y).
Proof. exact (@lem17265 (lt3 y x) (term54 A P y)). Qed.
Lemma lem358823 {A : Type'} (lt3 : type1402 A) (x : A) (P : A -> Prop) : (term34 A lt3 x P) = (term55 A lt3 x P).
Proof. exact (fun_ext (fun y : A => @lem358822 A lt3 x P y)). Qed.
Lemma lem358824 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem358825 {A : Type'} (lt3 : type1402 A) (x : A) (P : A -> Prop) : (term35 A lt3 x P) = (term56 A lt3 x P).
Proof. exact (MK_COMB (@lem358824 A) (@lem358823 A lt3 x P)). Qed.
Lemma lem358827 {A : Type'} (P : A -> Prop) (x : A) : (term36 A P x) = (term36 A P x).
Proof. exact (eq_refl (term36 A P x)). Qed.
Lemma lem358828 {A : Type'} (lt3 : type1402 A) (x : A) (P : A -> Prop) : (term37 A lt3 x P) = (term57 A lt3 x P).
Proof. exact (MK_COMB (@lem358827 A P x) (@lem358825 A lt3 x P)). Qed.
Lemma lem358829 {A : Type'} (lt3 : type1402 A) (P : A -> Prop) : (term38 A lt3 P) = (term58 A lt3 P).
Proof. exact (fun_ext (fun x : A => @lem358828 A lt3 x P)). Qed.
Lemma lem358830 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem358911 {A : Type'} (lt3 : type1402 A) (P : A -> Prop) : (term11 A lt3 P) = (term59 A lt3 P).
Proof. exact (MK_COMB (@lem358830 A) (@lem358829 A lt3 P)). Qed.
Lemma lem358912 {A : Type'} (lt3 : type1402 A) (P : A -> Prop) (h1 : term11 A lt3 P) : term59 A lt3 P.
Proof. exact (EQ_MP (@lem358911 A lt3 P) (@lem358739 A lt3 P h1)). Qed.
Lemma lem358917 {A : Type'} (P : A -> Prop) (y : A) : (term60 A P y) = (P y).
Proof. exact (@lem16933 (P y)). Qed.
Lemma lem358919 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) : (term61 A lt2 y x) = (term61 A lt2 y x).
Proof. exact (eq_refl (term61 A lt2 y x)). Qed.
Lemma lem358920 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term62 A lt2 x P y) = (term63 A lt2 x P y).
Proof. exact (MK_COMB (@lem358919 A lt2 y x) (@lem358917 A P y)). Qed.
Lemma lem358921 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term64 A lt2 x P y) = (term62 A lt2 x P y).
Proof. exact (@lem17362 (lt2 y x) (term54 A P y)). Qed.
Lemma lem358922 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term64 A lt2 x P y) = (term63 A lt2 x P y).
Proof. exact (TRANS (@lem358921 A lt2 x P y) (@lem358920 A lt2 x P y)). Qed.
Lemma lem358923 {A : Type'} (P : A -> Prop) : (term65 A P) = (term66 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem358924 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term67 A lt2 x P) = (term68 A lt2 x P).
Proof. exact (@lem358923 A (term34 A lt2 x P)). Qed.
Lemma lem358925 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term69 A lt2 x P y) = (term33 A lt2 x P y).
Proof. exact (eq_refl (term69 A lt2 x P y)). Qed.
Lemma lem358926 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem358927 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term70 A lt2 x P y) = (term64 A lt2 x P y).
Proof. exact (MK_COMB (@lem358926) (@lem358925 A lt2 x P y)). Qed.
Lemma lem358928 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term70 A lt2 x P y) = (term63 A lt2 x P y).
Proof. exact (TRANS (@lem358927 A lt2 x P y) (@lem358922 A lt2 x P y)). Qed.
Lemma lem358929 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term71 A lt2 x P) = (term72 A lt2 x P).
Proof. exact (fun_ext (fun y : A => @lem358928 A lt2 x P y)). Qed.
Lemma lem358930 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem358931 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term68 A lt2 x P) = (term73 A lt2 x P).
Proof. exact (MK_COMB (@lem358930 A) (@lem358929 A lt2 x P)). Qed.
Lemma lem358932 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term67 A lt2 x P) = (term73 A lt2 x P).
Proof. exact (TRANS (@lem358924 A lt2 x P) (@lem358931 A lt2 x P)). Qed.
Lemma lem358934 {A : Type'} (P : A -> Prop) (x : A) : (term74 A P x) = (term74 A P x).
Proof. exact (eq_refl (term74 A P x)). Qed.
Lemma lem358935 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term75 A lt2 x P) = (term76 A lt2 x P).
Proof. exact (MK_COMB (@lem358934 A P x) (@lem358932 A lt2 x P)). Qed.
Lemma lem358936 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term77 A lt2 x P) = (term75 A lt2 x P).
Proof. exact (@lem17045 (P x) (term35 A lt2 x P)). Qed.
Lemma lem358937 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term77 A lt2 x P) = (term76 A lt2 x P).
Proof. exact (TRANS (@lem358936 A lt2 x P) (@lem358935 A lt2 x P)). Qed.
Lemma lem358938 {A : Type'} (P : A -> Prop) : (term78 A P) = (term79 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem358939 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term47 A lt2 P) = (term80 A lt2 P).
Proof. exact (@lem358938 A (term38 A lt2 P)). Qed.
Lemma lem358940 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term81 A lt2 P x) = (term37 A lt2 x P).
Proof. exact (eq_refl (term81 A lt2 P x)). Qed.
Lemma lem358941 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem358942 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term82 A lt2 P x) = (term77 A lt2 x P).
Proof. exact (MK_COMB (@lem358941) (@lem358940 A lt2 x P)). Qed.
Lemma lem358943 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term82 A lt2 P x) = (term76 A lt2 x P).
Proof. exact (TRANS (@lem358942 A lt2 x P) (@lem358937 A lt2 x P)). Qed.
Lemma lem358944 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term83 A lt2 P) = (term84 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem358943 A lt2 x P)). Qed.
Lemma lem358945 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem358946 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term80 A lt2 P) = (term85 A lt2 P).
Proof. exact (MK_COMB (@lem358945 A) (@lem358944 A lt2 P)). Qed.
Lemma lem358947 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term47 A lt2 P) = (term85 A lt2 P).
Proof. exact (TRANS (@lem358939 A lt2 P) (@lem358946 A lt2 P)). Qed.
Lemma lem359030 {A : Type'} (P : Prop) (Q : A -> Prop) : (term86 A P Q) = (term87 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem359031 {A : Type'} (P : Prop) (Q : A -> Prop) : (term86 A P Q) = (term87 A P Q).
Proof. exact (@lem359030 A P Q). Qed.
Lemma lem359032 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term88 A lt2 x P) = (term89 A lt2 x P).
Proof. exact (@lem359031 A (term54 A P x) (term72 A lt2 x P)). Qed.
Lemma lem359033 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term90 A lt2 x P y) = (term63 A lt2 x P y).
Proof. exact (eq_refl (term90 A lt2 x P y)). Qed.
Lemma lem359034 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term91 A lt2 x P) = (term72 A lt2 x P).
Proof. exact (fun_ext (fun y : A => @lem359033 A lt2 x P y)). Qed.
Lemma lem359035 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem359036 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term92 A lt2 x P) = (term73 A lt2 x P).
Proof. exact (MK_COMB (@lem359035 A) (@lem359034 A lt2 x P)). Qed.
Lemma lem359037 {A : Type'} (P : A -> Prop) (x : A) : (term74 A P x) = (term74 A P x).
Proof. exact (eq_refl (term74 A P x)). Qed.
Lemma lem359038 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term88 A lt2 x P) = (term76 A lt2 x P).
Proof. exact (MK_COMB (@lem359037 A P x) (@lem359036 A lt2 x P)). Qed.
Lemma lem359039 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem359040 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term93 A lt2 x P) = (term94 A lt2 x P).
Proof. exact (MK_COMB (@lem359039) (@lem359038 A lt2 x P)). Qed.
Lemma lem359041 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term90 A lt2 x P y) = (term63 A lt2 x P y).
Proof. exact (eq_refl (term90 A lt2 x P y)). Qed.
Lemma lem359042 {A : Type'} (P : A -> Prop) (x : A) : (term74 A P x) = (term74 A P x).
Proof. exact (eq_refl (term74 A P x)). Qed.
Lemma lem359043 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term95 A lt2 x P y) = (term96 A lt2 x P y).
Proof. exact (MK_COMB (@lem359042 A P x) (@lem359041 A lt2 x P y)). Qed.
Lemma lem359044 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term97 A lt2 x P) = (term98 A lt2 x P).
Proof. exact (fun_ext (fun y : A => @lem359043 A lt2 x P y)). Qed.
Lemma lem359045 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem359046 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term89 A lt2 x P) = (term99 A lt2 x P).
Proof. exact (MK_COMB (@lem359045 A) (@lem359044 A lt2 x P)). Qed.
Lemma lem359047 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : ((term88 A lt2 x P) = (term89 A lt2 x P)) = ((term76 A lt2 x P) = (term99 A lt2 x P)).
Proof. exact (MK_COMB (@lem359040 A lt2 x P) (@lem359046 A lt2 x P)). Qed.
Lemma lem359048 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term76 A lt2 x P) = (term99 A lt2 x P).
Proof. exact (EQ_MP (@lem359047 A lt2 x P) (@lem359032 A lt2 x P)). Qed.
Lemma lem359049 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term84 A lt2 P) = (term100 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem359048 A lt2 x P)). Qed.
Lemma lem359050 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem359051 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term85 A lt2 P) = (term101 A lt2 P).
Proof. exact (MK_COMB (@lem359050 A) (@lem359049 A lt2 P)). Qed.
Lemma lem359053 {A B : Type'} (P : type1413 A B) : (term102 A B P) = (term103 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem359054 {A : Type'} (P : type1402 A) : (term104 A P) = (term105 A P).
Proof. exact (@lem359053 A A P). Qed.
Lemma lem359055 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term106 A lt2 P) = (term107 A lt2 P).
Proof. exact (@lem359054 A (term108 A lt2 P)). Qed.
Lemma lem359056 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term109 A lt2 P x) = (term98 A lt2 x P).
Proof. exact (eq_refl (term109 A lt2 P x)). Qed.
Lemma lem359057 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem359058 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term110 A lt2 P x y) = (term111 A lt2 x P y).
Proof. exact (MK_COMB (@lem359056 A lt2 x P) (@lem359057 A y)). Qed.
Lemma lem359059 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term111 A lt2 x P y) = (term96 A lt2 x P y).
Proof. exact (eq_refl (term111 A lt2 x P y)). Qed.
Lemma lem359060 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term110 A lt2 P x y) = (term96 A lt2 x P y).
Proof. exact (TRANS (@lem359058 A lt2 x P y) (@lem359059 A lt2 x P y)). Qed.
Lemma lem359061 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term112 A lt2 P x) = (term98 A lt2 x P).
Proof. exact (fun_ext (fun y : A => @lem359060 A lt2 x P y)). Qed.
Lemma lem359062 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem359063 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term113 A lt2 P x) = (term99 A lt2 x P).
Proof. exact (MK_COMB (@lem359062 A) (@lem359061 A lt2 x P)). Qed.
Lemma lem359064 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term114 A lt2 P) = (term100 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem359063 A lt2 x P)). Qed.
Lemma lem359065 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem359066 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term106 A lt2 P) = (term101 A lt2 P).
Proof. exact (MK_COMB (@lem359065 A) (@lem359064 A lt2 P)). Qed.
Lemma lem359067 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem359068 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term115 A lt2 P) = (term116 A lt2 P).
Proof. exact (MK_COMB (@lem359067) (@lem359066 A lt2 P)). Qed.
Lemma lem359069 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term109 A lt2 P x) = (term98 A lt2 x P).
Proof. exact (eq_refl (term109 A lt2 P x)). Qed.
Lemma lem359070 {A : Type'} (y : A -> A) (x : A) : (y x) = (y x).
Proof. exact (eq_refl (y x)). Qed.
Lemma lem359071 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (x : A) : (term117 A lt2 P y x) = (term118 A lt2 P y x).
Proof. exact (MK_COMB (@lem359069 A lt2 x P) (@lem359070 A y x)). Qed.
Lemma lem359072 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (x : A) : (term118 A lt2 P y x) = (term119 A lt2 P y x).
Proof. exact (eq_refl (term118 A lt2 P y x)). Qed.
Lemma lem359073 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (x : A) : (term117 A lt2 P y x) = (term119 A lt2 P y x).
Proof. exact (TRANS (@lem359071 A lt2 P y x) (@lem359072 A lt2 P y x)). Qed.
Lemma lem359074 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term120 A lt2 P y) = (term121 A lt2 P y).
Proof. exact (fun_ext (fun x : A => @lem359073 A lt2 P y x)). Qed.
Lemma lem359075 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem359076 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term122 A lt2 P y) = (term123 A lt2 P y).
Proof. exact (MK_COMB (@lem359075 A) (@lem359074 A lt2 P y)). Qed.
Lemma lem359077 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term124 A lt2 P) = (term125 A lt2 P).
Proof. exact (fun_ext (fun y : A -> A => @lem359076 A lt2 P y)). Qed.
Lemma lem359078 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem359079 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term107 A lt2 P) = (term126 A lt2 P).
Proof. exact (MK_COMB (@lem359078 A) (@lem359077 A lt2 P)). Qed.
Lemma lem359080 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : ((term106 A lt2 P) = (term107 A lt2 P)) = ((term101 A lt2 P) = (term126 A lt2 P)).
Proof. exact (MK_COMB (@lem359068 A lt2 P) (@lem359079 A lt2 P)). Qed.
Lemma lem359081 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term101 A lt2 P) = (term126 A lt2 P).
Proof. exact (EQ_MP (@lem359080 A lt2 P) (@lem359055 A lt2 P)). Qed.
Lemma lem359083 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term85 A lt2 P) = (term126 A lt2 P).
Proof. exact (TRANS (@lem359051 A lt2 P) (@lem359081 A lt2 P)). Qed.
Lemma lem359084 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term47 A lt2 P) = (term126 A lt2 P).
Proof. exact (TRANS (@lem358947 A lt2 P) (@lem359083 A lt2 P)). Qed.
Lemma lem359085 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term47 A lt2 P) : term126 A lt2 P.
Proof. exact (EQ_MP (@lem359084 A lt2 P) (@lem358744 A lt2 P h1)). Qed.
Lemma lem359086 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term123 A lt2 P y) : term123 A lt2 P y.
Proof. exact (h1). Qed.
Lemma lem359087 {A : Type'} (lt3 : type1402 A) (x : A) (P : A -> Prop) (h1 : term57 A lt3 x P) : term57 A lt3 x P.
Proof. exact (h1). Qed.
Lemma lem359102 {A : Type'} (lt2 : type1402 A) (lt3 : type1402 A) (x : A) (y : A) : (term48 A lt2 lt3 x y) = (term48 A lt2 lt3 x y).
Proof. exact (eq_refl (term48 A lt2 lt3 x y)). Qed.
Lemma lem359103 {A : Type'} (lt2 : type1402 A) (lt3 : type1402 A) (x : A) : (term49 A lt2 lt3 x) = (term49 A lt2 lt3 x).
Proof. exact (fun_ext (fun y : A => @lem359102 A lt2 lt3 x y)). Qed.
Lemma lem359104 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem359105 {A : Type'} (lt2 : type1402 A) (lt3 : type1402 A) (x : A) : (term50 A lt2 lt3 x) = (term50 A lt2 lt3 x).
Proof. exact (MK_COMB (@lem359104 A) (@lem359103 A lt2 lt3 x)). Qed.
Lemma lem359106 {A : Type'} (lt2 : type1402 A) (lt3 : type1402 A) : (term51 A lt2 lt3) = (term51 A lt2 lt3).
Proof. exact (fun_ext (fun x : A => @lem359105 A lt2 lt3 x)). Qed.
Lemma lem359107 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem359108 {A : Type'} (lt2 : type1402 A) (lt3 : type1402 A) : (term52 A lt2 lt3) = (term52 A lt2 lt3).
Proof. exact (MK_COMB (@lem359107 A) (@lem359106 A lt2 lt3)). Qed.
Lemma lem359109 {A : Type'} (lt2 : type1402 A) (lt3 : type1402 A) (h1 : term3 A lt2 lt3) : term52 A lt2 lt3.
Proof. exact (EQ_MP (@lem359108 A lt2 lt3) (@lem358814 A lt2 lt3 h1)). Qed.
Lemma lem359132 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (x : A) : (term119 A lt2 P y x) = (term119 A lt2 P y x).
Proof. exact (eq_refl (term119 A lt2 P y x)). Qed.
Lemma lem359133 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term121 A lt2 P y) = (term121 A lt2 P y).
Proof. exact (fun_ext (fun x : A => @lem359132 A lt2 P y x)). Qed.
Lemma lem359134 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem359135 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term123 A lt2 P y) = (term123 A lt2 P y).
Proof. exact (MK_COMB (@lem359134 A) (@lem359133 A lt2 P y)). Qed.
Lemma lem359136 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term123 A lt2 P y) : term123 A lt2 P y.
Proof. exact (EQ_MP (@lem359135 A lt2 P y) (@lem359086 A lt2 P y h1)). Qed.
Lemma lem359151 {A : Type'} (lt3 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term53 A lt3 x P y) = (term53 A lt3 x P y).
Proof. exact (eq_refl (term53 A lt3 x P y)). Qed.
Lemma lem359152 {A : Type'} (lt3 : type1402 A) (x : A) (P : A -> Prop) : (term55 A lt3 x P) = (term55 A lt3 x P).
Proof. exact (fun_ext (fun y : A => @lem359151 A lt3 x P y)). Qed.
Lemma lem359153 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem359154 {A : Type'} (lt3 : type1402 A) (x : A) (P : A -> Prop) : (term56 A lt3 x P) = (term56 A lt3 x P).
Proof. exact (MK_COMB (@lem359153 A) (@lem359152 A lt3 x P)). Qed.
Lemma lem359159 {A : Type'} (P : A -> Prop) (x : A) : (term36 A P x) = (term36 A P x).
Proof. exact (eq_refl (term36 A P x)). Qed.
Lemma lem359160 {A : Type'} (lt3 : type1402 A) (x : A) (P : A -> Prop) : (term57 A lt3 x P) = (term57 A lt3 x P).
Proof. exact (MK_COMB (@lem359159 A P x) (@lem359154 A lt3 x P)). Qed.
Lemma lem359161 {A : Type'} (lt3 : type1402 A) (x : A) (P : A -> Prop) (h1 : term57 A lt3 x P) : term57 A lt3 x P.
Proof. exact (EQ_MP (@lem359160 A lt3 x P) (@lem359087 A lt3 x P h1)). Qed.
Lemma lem359162 {A : Type'} (lt3 : type1402 A) (x : A) (P : A -> Prop) (h1 : term57 A lt3 x P) : term56 A lt3 x P.
Proof. exact (proj2 (@lem359161 A lt3 x P h1)). Qed.
Lemma lem359171 {A : Type'} (lt2 : type1402 A) (lt3 : type1402 A) (x : A) (y : A) : (term48 A lt2 lt3 x y) = (term48 A lt2 lt3 x y).
Proof. exact (eq_refl (term48 A lt2 lt3 x y)). Qed.
Lemma lem359172 {A : Type'} (lt2 : type1402 A) (lt3 : type1402 A) (x : A) : (term49 A lt2 lt3 x) = (term49 A lt2 lt3 x).
Proof. exact (fun_ext (fun y : A => @lem359171 A lt2 lt3 x y)). Qed.
Lemma lem359173 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem359174 {A : Type'} (lt2 : type1402 A) (lt3 : type1402 A) (x : A) : (term50 A lt2 lt3 x) = (term50 A lt2 lt3 x).
Proof. exact (MK_COMB (@lem359173 A) (@lem359172 A lt2 lt3 x)). Qed.
Lemma lem359175 {A : Type'} (lt2 : type1402 A) (lt3 : type1402 A) : (term51 A lt2 lt3) = (term51 A lt2 lt3).
Proof. exact (fun_ext (fun x : A => @lem359174 A lt2 lt3 x)). Qed.
Lemma lem359176 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem359178 {A : Type'} (lt2 : type1402 A) (lt3 : type1402 A) : (term52 A lt2 lt3) = (term52 A lt2 lt3).
Proof. exact (MK_COMB (@lem359176 A) (@lem359175 A lt2 lt3)). Qed.
Lemma lem359179 {A : Type'} (lt2 : type1402 A) (lt3 : type1402 A) (h1 : term3 A lt2 lt3) : term52 A lt2 lt3.
Proof. exact (EQ_MP (@lem359178 A lt2 lt3) (@lem359109 A lt2 lt3 h1)). Qed.
Lemma lem359197 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (x : A) : (term119 A lt2 P y x) = (term127 A lt2 P y x).
Proof. exact (@lem19490 (term128 A lt2 y x) (term54 A P x) (term129 A P y x)). Qed.
Lemma lem359198 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term121 A lt2 P y) = (term130 A lt2 P y).
Proof. exact (fun_ext (fun x : A => @lem359197 A lt2 P y x)). Qed.
Lemma lem359199 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem359201 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term123 A lt2 P y) = (term131 A lt2 P y).
Proof. exact (MK_COMB (@lem359199 A) (@lem359198 A lt2 P y)). Qed.
Lemma lem359202 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term123 A lt2 P y) : term131 A lt2 P y.
Proof. exact (EQ_MP (@lem359201 A lt2 P y) (@lem359136 A lt2 P y h1)). Qed.
Lemma lem359214 {A : Type'} (lt3 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term53 A lt3 x P y) = (term53 A lt3 x P y).
Proof. exact (eq_refl (term53 A lt3 x P y)). Qed.
Lemma lem359215 {A : Type'} (lt3 : type1402 A) (x : A) (P : A -> Prop) : (term55 A lt3 x P) = (term55 A lt3 x P).
Proof. exact (fun_ext (fun y : A => @lem359214 A lt3 x P y)). Qed.
Lemma lem359216 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem359218 {A : Type'} (lt3 : type1402 A) (x : A) (P : A -> Prop) : (term56 A lt3 x P) = (term56 A lt3 x P).
Proof. exact (MK_COMB (@lem359216 A) (@lem359215 A lt3 x P)). Qed.
Lemma lem359219 {A : Type'} (lt3 : type1402 A) (x : A) (P : A -> Prop) (h1 : term57 A lt3 x P) : term56 A lt3 x P.
Proof. exact (EQ_MP (@lem359218 A lt3 x P) (@lem359162 A lt3 x P h1)). Qed.
Lemma lem359220 {A : Type'} (_7791 : A) (lt2 : type1402 A) (lt3 : type1402 A) (h1 : term3 A lt2 lt3) : term132 A lt2 lt3 _7791.
Proof. exact (@lem359179 A lt2 lt3 h1 _7791). Qed.
Lemma lem359221 {A : Type'} (lt2 : type1402 A) (lt3 : type1402 A) (_7791 : A) : (term132 A lt2 lt3 _7791) = (term50 A lt2 lt3 _7791).
Proof. exact (eq_refl (term132 A lt2 lt3 _7791)). Qed.
Lemma lem359222 {A : Type'} (_7791 : A) (lt2 : type1402 A) (lt3 : type1402 A) (h1 : term3 A lt2 lt3) : term50 A lt2 lt3 _7791.
Proof. exact (EQ_MP (@lem359221 A lt2 lt3 _7791) (@lem359220 A _7791 lt2 lt3 h1)). Qed.
Lemma lem359223 {A : Type'} (_7791 : A) (_7792 : A) (lt2 : type1402 A) (lt3 : type1402 A) (h1 : term3 A lt2 lt3) : term133 A lt2 lt3 _7791 _7792.
Proof. exact (@lem359222 A _7791 lt2 lt3 h1 _7792). Qed.
Lemma lem359224 {A : Type'} (lt2 : type1402 A) (lt3 : type1402 A) (_7791 : A) (_7792 : A) : (term133 A lt2 lt3 _7791 _7792) = (term48 A lt2 lt3 _7791 _7792).
Proof. exact (eq_refl (term133 A lt2 lt3 _7791 _7792)). Qed.
Lemma lem359226 {A : Type'} (_7793 : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term123 A lt2 P y) : term134 A lt2 P y _7793.
Proof. exact (@lem359202 A lt2 P y h1 _7793). Qed.
Lemma lem359227 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (_7793 : A) : (term134 A lt2 P y _7793) = (term127 A lt2 P y _7793).
Proof. exact (eq_refl (term134 A lt2 P y _7793)). Qed.
Lemma lem359228 {A : Type'} (_7793 : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term123 A lt2 P y) : term127 A lt2 P y _7793.
Proof. exact (EQ_MP (@lem359227 A lt2 P y _7793) (@lem359226 A _7793 lt2 P y h1)). Qed.
Lemma lem359229 {A : Type'} (_7794 : A) (lt3 : type1402 A) (x : A) (P : A -> Prop) (h1 : term57 A lt3 x P) : term135 A lt3 x P _7794.
Proof. exact (@lem359219 A lt3 x P h1 _7794). Qed.
Lemma lem359230 {A : Type'} (lt3 : type1402 A) (x : A) (P : A -> Prop) (_7794 : A) : (term135 A lt3 x P _7794) = (term53 A lt3 x P _7794).
Proof. exact (eq_refl (term135 A lt3 x P _7794)). Qed.
Lemma lem359239 {A : Type'} (_7791 : A) (_7792 : A) (lt2 : type1402 A) (lt3 : type1402 A) (h1 : term3 A lt2 lt3) : term48 A lt2 lt3 _7791 _7792.
Proof. exact (EQ_MP (@lem359224 A lt2 lt3 _7791 _7792) (@lem359223 A _7791 _7792 lt2 lt3 h1)). Qed.
Lemma lem359247 {A : Type'} (_7794 : A) (lt3 : type1402 A) (x : A) (P : A -> Prop) (h1 : term57 A lt3 x P) : term53 A lt3 x P _7794.
Proof. exact (EQ_MP (@lem359230 A lt3 x P _7794) (@lem359229 A _7794 lt3 x P h1)). Qed.
Lemma lem359253 {A : Type'} (_7793 : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term123 A lt2 P y) : term136 A P lt2 y _7793.
Proof. exact (proj1 (@lem359228 A _7793 lt2 P y h1)). Qed.
Lemma lem359259 {A : Type'} (_7793 : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term123 A lt2 P y) : term137 A P y _7793.
Proof. exact (proj2 (@lem359228 A _7793 lt2 P y h1)). Qed.
Lemma lem359261 {A : Type'} (lt3 : type1402 A) (x : A) (P : A -> Prop) (h1 : term57 A lt3 x P) : P x.
Proof. exact (proj1 (@lem359161 A lt3 x P h1)). Qed.
Lemma lem359262 {A : Type'} (lt3 : type1402 A) (x : A) (P : A -> Prop) (h1 : term57 A lt3 x P) : term138 A P x.
Proof. exact (fun h0 : term54 A P x => @lem359261 A lt3 x P h1). Qed.
Lemma lem359264 (p : Prop) : (term139 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem359265 {A : Type'} (P : A -> Prop) (x : A) : (term138 A P x) = (P x).
Proof. exact (@lem359264 (P x)). Qed.
Lemma lem359266 {A : Type'} (lt3 : type1402 A) (x : A) (P : A -> Prop) (h1 : term57 A lt3 x P) : P x.
Proof. exact (EQ_MP (@lem359265 A P x) (@lem359262 A lt3 x P h1)). Qed.
Lemma lem359272 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem359273 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (_7793 : A) : (term136 A P lt2 y _7793) = (term140 A lt2 y P _7793).
Proof. exact (@lem359272 (term128 A lt2 y _7793) (term54 A P _7793)). Qed.
Lemma lem359279 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem359280 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (_7793 : A) : (term141 A P lt2 y _7793) = (term142 A lt2 y P _7793).
Proof. exact (MK_COMB (@lem359279) (@lem359273 A lt2 y P _7793)). Qed.
Lemma lem359286 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (_7793 : A) : (term140 A lt2 y P _7793) = (term140 A lt2 y P _7793).
Proof. exact (eq_refl (term140 A lt2 y P _7793)). Qed.
Lemma lem359287 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (_7793 : A) : ((term136 A P lt2 y _7793) = (term140 A lt2 y P _7793)) = ((term140 A lt2 y P _7793) = (term140 A lt2 y P _7793)).
Proof. exact (MK_COMB (@lem359280 A lt2 y P _7793) (@lem359286 A lt2 y P _7793)). Qed.
Lemma lem359289 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem359290 (x : Prop) : (x = x) = True.
Proof. exact (@lem359289 Prop x). Qed.
Lemma lem359291 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (_7793 : A) : ((term140 A lt2 y P _7793) = (term140 A lt2 y P _7793)) = True.
Proof. exact (@lem359290 (term140 A lt2 y P _7793)). Qed.
Lemma lem359292 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (_7793 : A) : ((term136 A P lt2 y _7793) = (term140 A lt2 y P _7793)) = True.
Proof. exact (TRANS (@lem359287 A lt2 y P _7793) (@lem359291 A lt2 y P _7793)). Qed.
Lemma lem359293 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (_7793 : A) : True = ((term136 A P lt2 y _7793) = (term140 A lt2 y P _7793)).
Proof. exact (SYM (@lem359292 A lt2 y P _7793)). Qed.
Lemma lem359294 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (_7793 : A) : (term136 A P lt2 y _7793) = (term140 A lt2 y P _7793).
Proof. exact (EQ_MP (@lem359293 A lt2 y P _7793) (@lem0)). Qed.
Lemma lem359295 {A : Type'} (_7793 : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term123 A lt2 P y) : term140 A lt2 y P _7793.
Proof. exact (EQ_MP (@lem359294 A lt2 y P _7793) (@lem359253 A _7793 lt2 P y h1)). Qed.
Lemma lem359297 (b : Prop) (a : Prop) : (a \/ b) = (term143 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem359298 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (y : A -> A) (_7793 : A) : (term140 A lt2 y P _7793) = (term144 A P lt2 y _7793).
Proof. exact (@lem359297 (term54 A P _7793) (term128 A lt2 y _7793)). Qed.
Lemma lem359300 (a : Prop) : (term20 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem359301 {A : Type'} (P : A -> Prop) (_7793 : A) : (term60 A P _7793) = (P _7793).
Proof. exact (@lem359300 (P _7793)). Qed.
Lemma lem359302 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem359303 {A : Type'} (P : A -> Prop) (_7793 : A) : (term145 A P _7793) = (term146 A P _7793).
Proof. exact (MK_COMB (@lem359302) (@lem359301 A P _7793)). Qed.
Lemma lem359304 {A : Type'} (lt2 : type1402 A) (y : A -> A) (_7793 : A) : (term128 A lt2 y _7793) = (term128 A lt2 y _7793).
Proof. exact (eq_refl (term128 A lt2 y _7793)). Qed.
Lemma lem359305 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (y : A -> A) (_7793 : A) : (term144 A P lt2 y _7793) = (term147 A P lt2 y _7793).
Proof. exact (MK_COMB (@lem359303 A P _7793) (@lem359304 A lt2 y _7793)). Qed.
Lemma lem359306 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (y : A -> A) (_7793 : A) : (term140 A lt2 y P _7793) = (term147 A P lt2 y _7793).
Proof. exact (TRANS (@lem359298 A P lt2 y _7793) (@lem359305 A P lt2 y _7793)). Qed.
Lemma lem359309 {A : Type'} (_7793 : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term123 A lt2 P y) : term147 A P lt2 y _7793.
Proof. exact (EQ_MP (@lem359306 A P lt2 y _7793) (@lem359295 A _7793 lt2 P y h1)). Qed.
Lemma lem359310 {A : Type'} (_7793 : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term123 A lt2 P y) : term147 A P lt2 y _7793.
Proof. exact (@lem359309 A _7793 lt2 P y h1). Qed.
Lemma lem359311 {A : Type'} (x : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term123 A lt2 P y) : term147 A P lt2 y x.
Proof. exact (@lem359310 A x lt2 P y h1). Qed.
Lemma lem359314 {A : Type'} (lt2 : type1402 A) (y : A -> A) (lt3 : type1402 A) (x : A) (P : A -> Prop) (h1 : term123 A lt2 P y) (h2 : term57 A lt3 x P) : term128 A lt2 y x.
Proof. exact (@lem359311 A x lt2 P y h1 (@lem359266 A lt3 x P h2)). Qed.
Lemma lem359315 {A : Type'} (lt2 : type1402 A) (y : A -> A) (lt3 : type1402 A) (x : A) (P : A -> Prop) (h1 : term123 A lt2 P y) (h2 : term57 A lt3 x P) : term148 A lt2 y x.
Proof. exact (fun h0 : term149 A lt2 y x => @lem359314 A lt2 y lt3 x P h1 h2). Qed.
Lemma lem359317 (p : Prop) : (term139 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem359318 {A : Type'} (lt2 : type1402 A) (y : A -> A) (x : A) : (term148 A lt2 y x) = (term128 A lt2 y x).
Proof. exact (@lem359317 (term128 A lt2 y x)). Qed.
Lemma lem359319 {A : Type'} (lt2 : type1402 A) (y : A -> A) (lt3 : type1402 A) (x : A) (P : A -> Prop) (h1 : term123 A lt2 P y) (h2 : term57 A lt3 x P) : term128 A lt2 y x.
Proof. exact (EQ_MP (@lem359318 A lt2 y x) (@lem359315 A lt2 y lt3 x P h1 h2)). Qed.
Lemma lem359325 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem359326 {A : Type'} (lt3 : type1402 A) (lt2 : type1402 A) (_7791 : A) (_7792 : A) : (term48 A lt2 lt3 _7791 _7792) = (term150 A lt3 lt2 _7791 _7792).
Proof. exact (@lem359325 (lt3 _7791 _7792) (term151 A lt2 _7791 _7792)). Qed.
Lemma lem359332 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem359333 {A : Type'} (lt3 : type1402 A) (lt2 : type1402 A) (_7791 : A) (_7792 : A) : (term152 A lt2 lt3 _7791 _7792) = (term153 A lt3 lt2 _7791 _7792).
Proof. exact (MK_COMB (@lem359332) (@lem359326 A lt3 lt2 _7791 _7792)). Qed.
Lemma lem359339 {A : Type'} (lt3 : type1402 A) (lt2 : type1402 A) (_7791 : A) (_7792 : A) : (term150 A lt3 lt2 _7791 _7792) = (term150 A lt3 lt2 _7791 _7792).
Proof. exact (eq_refl (term150 A lt3 lt2 _7791 _7792)). Qed.
Lemma lem359340 {A : Type'} (lt3 : type1402 A) (lt2 : type1402 A) (_7791 : A) (_7792 : A) : ((term48 A lt2 lt3 _7791 _7792) = (term150 A lt3 lt2 _7791 _7792)) = ((term150 A lt3 lt2 _7791 _7792) = (term150 A lt3 lt2 _7791 _7792)).
Proof. exact (MK_COMB (@lem359333 A lt3 lt2 _7791 _7792) (@lem359339 A lt3 lt2 _7791 _7792)). Qed.
Lemma lem359342 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem359343 (x : Prop) : (x = x) = True.
Proof. exact (@lem359342 Prop x). Qed.
Lemma lem359344 {A : Type'} (lt3 : type1402 A) (lt2 : type1402 A) (_7791 : A) (_7792 : A) : ((term150 A lt3 lt2 _7791 _7792) = (term150 A lt3 lt2 _7791 _7792)) = True.
Proof. exact (@lem359343 (term150 A lt3 lt2 _7791 _7792)). Qed.
Lemma lem359345 {A : Type'} (lt3 : type1402 A) (lt2 : type1402 A) (_7791 : A) (_7792 : A) : ((term48 A lt2 lt3 _7791 _7792) = (term150 A lt3 lt2 _7791 _7792)) = True.
Proof. exact (TRANS (@lem359340 A lt3 lt2 _7791 _7792) (@lem359344 A lt3 lt2 _7791 _7792)). Qed.
Lemma lem359346 {A : Type'} (lt3 : type1402 A) (lt2 : type1402 A) (_7791 : A) (_7792 : A) : True = ((term48 A lt2 lt3 _7791 _7792) = (term150 A lt3 lt2 _7791 _7792)).
Proof. exact (SYM (@lem359345 A lt3 lt2 _7791 _7792)). Qed.
Lemma lem359347 {A : Type'} (lt3 : type1402 A) (lt2 : type1402 A) (_7791 : A) (_7792 : A) : (term48 A lt2 lt3 _7791 _7792) = (term150 A lt3 lt2 _7791 _7792).
Proof. exact (EQ_MP (@lem359346 A lt3 lt2 _7791 _7792) (@lem0)). Qed.
Lemma lem359348 {A : Type'} (_7791 : A) (_7792 : A) (lt2 : type1402 A) (lt3 : type1402 A) (h1 : term3 A lt2 lt3) : term150 A lt3 lt2 _7791 _7792.
Proof. exact (EQ_MP (@lem359347 A lt3 lt2 _7791 _7792) (@lem359239 A _7791 _7792 lt2 lt3 h1)). Qed.
Lemma lem359350 (b : Prop) (a : Prop) : (a \/ b) = (term143 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem359351 {A : Type'} (lt2 : type1402 A) (lt3 : type1402 A) (_7791 : A) (_7792 : A) : (term150 A lt3 lt2 _7791 _7792) = (term154 A lt2 lt3 _7791 _7792).
Proof. exact (@lem359350 (term151 A lt2 _7791 _7792) (lt3 _7791 _7792)). Qed.
Lemma lem359353 (a : Prop) : (term20 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem359354 {A : Type'} (lt2 : type1402 A) (_7791 : A) (_7792 : A) : (term155 A lt2 _7791 _7792) = (lt2 _7791 _7792).
Proof. exact (@lem359353 (lt2 _7791 _7792)). Qed.
Lemma lem359355 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem359356 {A : Type'} (lt2 : type1402 A) (_7791 : A) (_7792 : A) : (term156 A lt2 _7791 _7792) = (term157 A lt2 _7791 _7792).
Proof. exact (MK_COMB (@lem359355) (@lem359354 A lt2 _7791 _7792)). Qed.
Lemma lem359357 {A : Type'} (lt3 : type1402 A) (_7791 : A) (_7792 : A) : (lt3 _7791 _7792) = (lt3 _7791 _7792).
Proof. exact (eq_refl (lt3 _7791 _7792)). Qed.
Lemma lem359358 {A : Type'} (lt2 : type1402 A) (lt3 : type1402 A) (_7791 : A) (_7792 : A) : (term154 A lt2 lt3 _7791 _7792) = (term41 A lt2 lt3 _7791 _7792).
Proof. exact (MK_COMB (@lem359356 A lt2 _7791 _7792) (@lem359357 A lt3 _7791 _7792)). Qed.
Lemma lem359359 {A : Type'} (lt2 : type1402 A) (lt3 : type1402 A) (_7791 : A) (_7792 : A) : (term150 A lt3 lt2 _7791 _7792) = (term41 A lt2 lt3 _7791 _7792).
Proof. exact (TRANS (@lem359351 A lt2 lt3 _7791 _7792) (@lem359358 A lt2 lt3 _7791 _7792)). Qed.
Lemma lem359362 {A : Type'} (_7791 : A) (_7792 : A) (lt2 : type1402 A) (lt3 : type1402 A) (h1 : term3 A lt2 lt3) : term41 A lt2 lt3 _7791 _7792.
Proof. exact (EQ_MP (@lem359359 A lt2 lt3 _7791 _7792) (@lem359348 A _7791 _7792 lt2 lt3 h1)). Qed.
Lemma lem359363 {A : Type'} (_7791 : A) (_7792 : A) (lt2 : type1402 A) (lt3 : type1402 A) (h1 : term3 A lt2 lt3) : term41 A lt2 lt3 _7791 _7792.
Proof. exact (@lem359362 A _7791 _7792 lt2 lt3 h1). Qed.
Lemma lem359364 {A : Type'} (y : A -> A) (x : A) (lt2 : type1402 A) (lt3 : type1402 A) (h1 : term3 A lt2 lt3) : term158 A lt2 lt3 y x.
Proof. exact (@lem359363 A (y x) x lt2 lt3 h1). Qed.
Lemma lem359367 {A : Type'} (lt2 : type1402 A) (y : A -> A) (lt3 : type1402 A) (x : A) (P : A -> Prop) (h1 : term3 A lt2 lt3) (h2 : term123 A lt2 P y) (h3 : term57 A lt3 x P) : term128 A lt3 y x.
Proof. exact (@lem359364 A y x lt2 lt3 h1 (@lem359319 A lt2 y lt3 x P h2 h3)). Qed.
Lemma lem359368 {A : Type'} (lt2 : type1402 A) (y : A -> A) (lt3 : type1402 A) (x : A) (P : A -> Prop) (h1 : term3 A lt2 lt3) (h2 : term123 A lt2 P y) (h3 : term57 A lt3 x P) : term148 A lt3 y x.
Proof. exact (fun h0 : term149 A lt3 y x => @lem359367 A lt2 y lt3 x P h1 h2 h3). Qed.
Lemma lem359370 (p : Prop) : (term139 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem359371 {A : Type'} (lt3 : type1402 A) (y : A -> A) (x : A) : (term148 A lt3 y x) = (term128 A lt3 y x).
Proof. exact (@lem359370 (term128 A lt3 y x)). Qed.
Lemma lem359372 {A : Type'} (lt2 : type1402 A) (y : A -> A) (lt3 : type1402 A) (x : A) (P : A -> Prop) (h1 : term3 A lt2 lt3) (h2 : term123 A lt2 P y) (h3 : term57 A lt3 x P) : term128 A lt3 y x.
Proof. exact (EQ_MP (@lem359371 A lt3 y x) (@lem359368 A lt2 y lt3 x P h1 h2 h3)). Qed.
Lemma lem359374 {A : Type'} (lt3 : type1402 A) (x : A) (P : A -> Prop) (h1 : term57 A lt3 x P) : P x.
Proof. exact (proj1 (@lem359161 A lt3 x P h1)). Qed.
Lemma lem359375 {A : Type'} (lt3 : type1402 A) (x : A) (P : A -> Prop) (h1 : term57 A lt3 x P) : term138 A P x.
Proof. exact (fun h0 : term54 A P x => @lem359374 A lt3 x P h1). Qed.
Lemma lem359377 (p : Prop) : (term139 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem359378 {A : Type'} (P : A -> Prop) (x : A) : (term138 A P x) = (P x).
Proof. exact (@lem359377 (P x)). Qed.
Lemma lem359379 {A : Type'} (lt3 : type1402 A) (x : A) (P : A -> Prop) (h1 : term57 A lt3 x P) : P x.
Proof. exact (EQ_MP (@lem359378 A P x) (@lem359375 A lt3 x P h1)). Qed.
Lemma lem359385 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem359386 {A : Type'} (y : A -> A) (P : A -> Prop) (_7793 : A) : (term137 A P y _7793) = (term159 A y P _7793).
Proof. exact (@lem359385 (term129 A P y _7793) (term54 A P _7793)). Qed.
Lemma lem359392 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem359393 {A : Type'} (y : A -> A) (P : A -> Prop) (_7793 : A) : (term160 A P y _7793) = (term161 A y P _7793).
Proof. exact (MK_COMB (@lem359392) (@lem359386 A y P _7793)). Qed.
Lemma lem359399 {A : Type'} (y : A -> A) (P : A -> Prop) (_7793 : A) : (term159 A y P _7793) = (term159 A y P _7793).
Proof. exact (eq_refl (term159 A y P _7793)). Qed.
Lemma lem359400 {A : Type'} (y : A -> A) (P : A -> Prop) (_7793 : A) : ((term137 A P y _7793) = (term159 A y P _7793)) = ((term159 A y P _7793) = (term159 A y P _7793)).
Proof. exact (MK_COMB (@lem359393 A y P _7793) (@lem359399 A y P _7793)). Qed.
Lemma lem359402 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem359403 (x : Prop) : (x = x) = True.
Proof. exact (@lem359402 Prop x). Qed.
Lemma lem359404 {A : Type'} (y : A -> A) (P : A -> Prop) (_7793 : A) : ((term159 A y P _7793) = (term159 A y P _7793)) = True.
Proof. exact (@lem359403 (term159 A y P _7793)). Qed.
Lemma lem359405 {A : Type'} (y : A -> A) (P : A -> Prop) (_7793 : A) : ((term137 A P y _7793) = (term159 A y P _7793)) = True.
Proof. exact (TRANS (@lem359400 A y P _7793) (@lem359404 A y P _7793)). Qed.
Lemma lem359406 {A : Type'} (y : A -> A) (P : A -> Prop) (_7793 : A) : True = ((term137 A P y _7793) = (term159 A y P _7793)).
Proof. exact (SYM (@lem359405 A y P _7793)). Qed.
Lemma lem359407 {A : Type'} (y : A -> A) (P : A -> Prop) (_7793 : A) : (term137 A P y _7793) = (term159 A y P _7793).
Proof. exact (EQ_MP (@lem359406 A y P _7793) (@lem0)). Qed.
Lemma lem359408 {A : Type'} (_7793 : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term123 A lt2 P y) : term159 A y P _7793.
Proof. exact (EQ_MP (@lem359407 A y P _7793) (@lem359259 A _7793 lt2 P y h1)). Qed.
Lemma lem359410 (b : Prop) (a : Prop) : (a \/ b) = (term143 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem359411 {A : Type'} (P : A -> Prop) (y : A -> A) (_7793 : A) : (term159 A y P _7793) = (term162 A P y _7793).
Proof. exact (@lem359410 (term54 A P _7793) (term129 A P y _7793)). Qed.
Lemma lem359413 (a : Prop) : (term20 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem359414 {A : Type'} (P : A -> Prop) (_7793 : A) : (term60 A P _7793) = (P _7793).
Proof. exact (@lem359413 (P _7793)). Qed.
Lemma lem359415 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem359416 {A : Type'} (P : A -> Prop) (_7793 : A) : (term145 A P _7793) = (term146 A P _7793).
Proof. exact (MK_COMB (@lem359415) (@lem359414 A P _7793)). Qed.
Lemma lem359417 {A : Type'} (P : A -> Prop) (y : A -> A) (_7793 : A) : (term129 A P y _7793) = (term129 A P y _7793).
Proof. exact (eq_refl (term129 A P y _7793)). Qed.
Lemma lem359418 {A : Type'} (P : A -> Prop) (y : A -> A) (_7793 : A) : (term162 A P y _7793) = (term163 A P y _7793).
Proof. exact (MK_COMB (@lem359416 A P _7793) (@lem359417 A P y _7793)). Qed.
Lemma lem359419 {A : Type'} (P : A -> Prop) (y : A -> A) (_7793 : A) : (term159 A y P _7793) = (term163 A P y _7793).
Proof. exact (TRANS (@lem359411 A P y _7793) (@lem359418 A P y _7793)). Qed.
Lemma lem359422 {A : Type'} (_7793 : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term123 A lt2 P y) : term163 A P y _7793.
Proof. exact (EQ_MP (@lem359419 A P y _7793) (@lem359408 A _7793 lt2 P y h1)). Qed.
Lemma lem359423 {A : Type'} (_7793 : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term123 A lt2 P y) : term163 A P y _7793.
Proof. exact (@lem359422 A _7793 lt2 P y h1). Qed.
Lemma lem359424 {A : Type'} (x : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term123 A lt2 P y) : term163 A P y x.
Proof. exact (@lem359423 A x lt2 P y h1). Qed.
Lemma lem359427 {A : Type'} (lt2 : type1402 A) (y : A -> A) (lt3 : type1402 A) (x : A) (P : A -> Prop) (h1 : term123 A lt2 P y) (h2 : term57 A lt3 x P) : term129 A P y x.
Proof. exact (@lem359424 A x lt2 P y h1 (@lem359379 A lt3 x P h2)). Qed.
Lemma lem359428 {A : Type'} (lt2 : type1402 A) (y : A -> A) (lt3 : type1402 A) (x : A) (P : A -> Prop) (h1 : term123 A lt2 P y) (h2 : term57 A lt3 x P) : term164 A P y x.
Proof. exact (fun h0 : term165 A P y x => @lem359427 A lt2 y lt3 x P h1 h2). Qed.
Lemma lem359430 (p : Prop) : (term139 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem359431 {A : Type'} (P : A -> Prop) (y : A -> A) (x : A) : (term164 A P y x) = (term129 A P y x).
Proof. exact (@lem359430 (term129 A P y x)). Qed.
Lemma lem359432 {A : Type'} (lt2 : type1402 A) (y : A -> A) (lt3 : type1402 A) (x : A) (P : A -> Prop) (h1 : term123 A lt2 P y) (h2 : term57 A lt3 x P) : term129 A P y x.
Proof. exact (EQ_MP (@lem359431 A P y x) (@lem359428 A lt2 y lt3 x P h1 h2)). Qed.
Lemma lem359434 (a : Prop) (b : Prop) : (term166 a b) = (term167 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem359435 {A : Type'} (lt3 : type1402 A) (x : A) (P : A -> Prop) (_7794 : A) : (term53 A lt3 x P _7794) = (term168 A lt3 x P _7794).
Proof. exact (@lem359434 (lt3 _7794 x) (P _7794)). Qed.
Lemma lem359437 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem359438 {A : Type'} (lt3 : type1402 A) (x : A) (P : A -> Prop) (_7794 : A) : (term168 A lt3 x P _7794) = (term169 A lt3 x P _7794).
Proof. exact (@lem359437 (term63 A lt3 x P _7794)). Qed.
Lemma lem359439 {A : Type'} (lt3 : type1402 A) (x : A) (P : A -> Prop) (_7794 : A) : (term53 A lt3 x P _7794) = (term169 A lt3 x P _7794).
Proof. exact (TRANS (@lem359435 A lt3 x P _7794) (@lem359438 A lt3 x P _7794)). Qed.
Lemma lem359441 {A : Type'} (lt2 : type1402 A) (y : A -> A) (lt3 : type1402 A) (x : A) (P : A -> Prop) (h1 : term3 A lt2 lt3) (h2 : term123 A lt2 P y) (h3 : term57 A lt3 x P) : term170 A lt3 P y x.
Proof. exact (conj (@lem359372 A lt2 y lt3 x P h1 h2 h3) (@lem359432 A lt2 y lt3 x P h2 h3)). Qed.
Lemma lem359443 {A : Type'} (_7794 : A) (lt3 : type1402 A) (x : A) (P : A -> Prop) (h1 : term57 A lt3 x P) : term169 A lt3 x P _7794.
Proof. exact (EQ_MP (@lem359439 A lt3 x P _7794) (@lem359247 A _7794 lt3 x P h1)). Qed.
Lemma lem359444 {A : Type'} (_7794 : A) (lt3 : type1402 A) (x : A) (P : A -> Prop) (h1 : term57 A lt3 x P) : term169 A lt3 x P _7794.
Proof. exact (@lem359443 A _7794 lt3 x P h1). Qed.
Lemma lem359445 {A : Type'} (y : A -> A) (lt3 : type1402 A) (x : A) (P : A -> Prop) (h1 : term57 A lt3 x P) : term171 A lt3 P y x.
Proof. exact (@lem359444 A (y x) lt3 x P h1). Qed.
Lemma lem359448 {A : Type'} (lt2 : type1402 A) (y : A -> A) (lt3 : type1402 A) (x : A) (P : A -> Prop) (h1 : term3 A lt2 lt3) (h2 : term123 A lt2 P y) (h3 : term57 A lt3 x P) : False.
Proof. exact (@lem359445 A y lt3 x P h3 (@lem359441 A lt2 y lt3 x P h1 h2 h3)). Qed.
Lemma lem359449 {A : Type'} (lt2 : type1402 A) (y : A -> A) (lt3 : type1402 A) (x : A) (P : A -> Prop) (h1 : term3 A lt2 lt3) (h2 : term123 A lt2 P y) (h3 : term57 A lt3 x P) : term172.
Proof. exact (fun h0 : ~ False => @lem359448 A lt2 y lt3 x P h1 h2 h3). Qed.
Lemma lem359451 (p : Prop) : (term139 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem359452 : term172 = False.
Proof. exact (@lem359451 False). Qed.
Lemma lem359453 {A : Type'} (lt2 : type1402 A) (y : A -> A) (lt3 : type1402 A) (x : A) (P : A -> Prop) (h1 : term3 A lt2 lt3) (h2 : term123 A lt2 P y) (h3 : term57 A lt3 x P) : False.
Proof. exact (EQ_MP (@lem359452) (@lem359449 A lt2 y lt3 x P h1 h2 h3)). Qed.
Lemma lem359454 {A : Type'} (lt2 : type1402 A) (y : A -> A) (lt3 : type1402 A) (x : A) (P : A -> Prop) (h1 : term3 A lt2 lt3) (h2 : term123 A lt2 P y) (h3 : term57 A lt3 x P) : (term57 A lt3 x P) = False.
Proof. exact (prop_ext (fun h4 : term57 A lt3 x P => @lem359453 A lt2 y lt3 x P h1 h2 h3) (fun h4 : False => @lem359161 A lt3 x P h3)). Qed.
Lemma lem359455 {A : Type'} (lt2 : type1402 A) (y : A -> A) (lt3 : type1402 A) (x : A) (P : A -> Prop) (h1 : term3 A lt2 lt3) (h2 : term123 A lt2 P y) (h3 : term57 A lt3 x P) : False.
Proof. exact (EQ_MP (@lem359454 A lt2 y lt3 x P h1 h2 h3) (@lem359161 A lt3 x P h3)). Qed.
Lemma lem359456 {A : Type'} (lt2 : type1402 A) (y : A -> A) (lt3 : type1402 A) (x : A) (P : A -> Prop) (h1 : term3 A lt2 lt3) (h2 : term123 A lt2 P y) (h3 : term57 A lt3 x P) : (term123 A lt2 P y) = False.
Proof. exact (prop_ext (fun h4 : term123 A lt2 P y => @lem359455 A lt2 y lt3 x P h1 h2 h3) (fun h4 : False => @lem359136 A lt2 P y h2)). Qed.
Lemma lem359457 {A : Type'} (lt2 : type1402 A) (y : A -> A) (lt3 : type1402 A) (x : A) (P : A -> Prop) (h1 : term3 A lt2 lt3) (h2 : term123 A lt2 P y) (h3 : term57 A lt3 x P) : False.
Proof. exact (EQ_MP (@lem359456 A lt2 y lt3 x P h1 h2 h3) (@lem359136 A lt2 P y h2)). Qed.
Lemma lem359458 {A : Type'} (lt2 : type1402 A) (y : A -> A) (lt3 : type1402 A) (P : A -> Prop) (h1 : term3 A lt2 lt3) (h2 : term123 A lt2 P y) (h3 : term11 A lt3 P) : False.
Proof. exact (ex_elim (@lem358912 A lt3 P h3) (fun x : A => fun h0 : term58 A lt3 P x => @lem359457 A lt2 y lt3 x P h1 h2 h0)). Qed.
Lemma lem359459 {A : Type'} (lt3 : type1402 A) (lt2 : type1402 A) (P : A -> Prop) (h1 : term3 A lt2 lt3) (h2 : term11 A lt3 P) (h3 : term47 A lt2 P) : False.
Proof. exact (ex_elim (@lem359085 A lt2 P h3) (fun y : A -> A => fun h0 : term125 A lt2 P y => @lem359458 A lt2 y lt3 P h1 h0 h2)). Qed.
Lemma lem359460 {A : Type'} (lt3 : type1402 A) (lt2 : type1402 A) (P : A -> Prop) (h1 : term3 A lt2 lt3) (h2 : term11 A lt3 P) (h3 : term47 A lt2 P) : (term47 A lt2 P) = False.
Proof. exact (prop_ext (fun h4 : term47 A lt2 P => @lem359459 A lt3 lt2 P h1 h2 h3) (fun h4 : False => @lem358744 A lt2 P h3)). Qed.
Lemma lem359461 {A : Type'} (lt3 : type1402 A) (lt2 : type1402 A) (P : A -> Prop) (h1 : term3 A lt2 lt3) (h2 : term11 A lt3 P) (h3 : term47 A lt2 P) : False.
Proof. exact (EQ_MP (@lem359460 A lt3 lt2 P h1 h2 h3) (@lem358744 A lt2 P h3)). Qed.
Lemma lem359462 {A : Type'} (lt2 : type1402 A) (lt3 : type1402 A) (P : A -> Prop) (h1 : term3 A lt2 lt3) (h2 : term11 A lt3 P) : term46 A lt2 P.
Proof. exact (fun h0 : term47 A lt2 P => @lem359461 A lt3 lt2 P h1 h2 h0). Qed.
Lemma lem359463 {A : Type'} (lt2 : type1402 A) (lt3 : type1402 A) (P : A -> Prop) (h1 : term3 A lt2 lt3) (h2 : term11 A lt3 P) : term11 A lt2 P.
Proof. exact (EQ_MP (@lem358743 A lt2 P) (@lem359462 A lt2 lt3 P h1 h2)). Qed.
Lemma lem359464 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (lt3 : type1402 A) (h1 : term3 A lt2 lt3) : term40 A lt3 lt2 P.
Proof. exact (fun h0 : term11 A lt3 P => @lem359463 A lt2 lt3 P h1 h0). Qed.
Lemma lem359465 {A : Type'} (lt3 : type1402 A) (lt2 : type1402 A) (P : A -> Prop) : term13 A lt3 lt2 P.
Proof. exact (fun h0 : term3 A lt2 lt3 => @lem359464 A P lt2 lt3 h0). Qed.
Lemma lem359470 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : term24 A lt2 P.
Proof. exact (fun lt3 : type1402 A => @lem359465 A lt3 lt2 P). Qed.
Lemma lem359475 {A : Type'} (P : A -> Prop) : term28 A P.
Proof. exact (fun lt2 : type1402 A => @lem359470 A lt2 P). Qed.
Lemma lem359480 {A : Type'} : term32 A.
Proof. exact (fun P : A -> Prop => @lem359475 A P). Qed.
Lemma lem359481 {A : Type'} : term31 A.
Proof. exact (EQ_MP (@lem358737 A) (@lem359480 A)). Qed.
Lemma lem359482 {A : Type'} (P : A -> Prop) : term173 A P.
Proof. exact (@lem359481 A P). Qed.
Lemma lem359483 {A : Type'} (P : A -> Prop) : (term173 A P) = (term27 A P).
Proof. exact (eq_refl (term173 A P)). Qed.
Lemma lem359484 {A : Type'} (P : A -> Prop) : term27 A P.
Proof. exact (EQ_MP (@lem359483 A P) (@lem359482 A P)). Qed.
Lemma lem359485 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : term174 A P lt2.
Proof. exact (@lem359484 A P lt2). Qed.
Lemma lem359486 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term174 A P lt2) = (term23 A lt2 P).
Proof. exact (eq_refl (term174 A P lt2)). Qed.
Lemma lem359487 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : term23 A lt2 P.
Proof. exact (EQ_MP (@lem359486 A lt2 P) (@lem359485 A P lt2)). Qed.
Lemma lem359488 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (lt3 : type1402 A) : term175 A lt2 P lt3.
Proof. exact (@lem359487 A lt2 P lt3). Qed.
Lemma lem359489 {A : Type'} (lt3 : type1402 A) (lt2 : type1402 A) (P : A -> Prop) : (term175 A lt2 P lt3) = (term14 A lt3 lt2 P).
Proof. exact (eq_refl (term175 A lt2 P lt3)). Qed.
Lemma lem359490 {A : Type'} (lt3 : type1402 A) (lt2 : type1402 A) (P : A -> Prop) : term14 A lt3 lt2 P.
Proof. exact (EQ_MP (@lem359489 A lt3 lt2 P) (@lem359488 A lt2 P lt3)). Qed.
Lemma lem359492 {A : Type'} (lt3 : type1402 A) (lt2 : type1402 A) (P : A -> Prop) : term14 A lt3 lt2 P.
Proof. exact (@lem358475 A lt3 lt2 P (@lem359490 A lt3 lt2 P)). Qed.
Lemma lem359493 {A : Type'} (lt3 : type1402 A) (lt2 : type1402 A) (P : A -> Prop) (h1 : term15 A lt3 lt2 P) : False.
Proof. exact (@lem359492 A lt3 lt2 P (@lem358459 A lt3 lt2 P h1)). Qed.
Lemma lem359494 {A : Type'} (lt3 : type1402 A) (lt2 : type1402 A) (P : A -> Prop) (h1 : term15 A lt3 lt2 P) : (term15 A lt3 lt2 P) = False.
Proof. exact (prop_ext (fun h2 : term15 A lt3 lt2 P => @lem359493 A lt3 lt2 P h1) (fun h2 : False => @lem358459 A lt3 lt2 P h1)). Qed.
Lemma lem359495 {A : Type'} (lt3 : type1402 A) (lt2 : type1402 A) (P : A -> Prop) (h1 : term15 A lt3 lt2 P) : False.
Proof. exact (EQ_MP (@lem359494 A lt3 lt2 P h1) (@lem358459 A lt3 lt2 P h1)). Qed.
Lemma lem359496 {A : Type'} (lt3 : type1402 A) (lt2 : type1402 A) (P : A -> Prop) : term14 A lt3 lt2 P.
Proof. exact (fun h0 : term15 A lt3 lt2 P => @lem359495 A lt3 lt2 P h0). Qed.
Lemma lem359497 {A : Type'} (lt3 : type1402 A) (lt2 : type1402 A) (P : A -> Prop) : term13 A lt3 lt2 P.
Proof. exact (EQ_MP (@lem358458 A lt3 lt2 P) (@lem359496 A lt3 lt2 P)). Qed.
Lemma lem359498 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (lt3 : type1402 A) (h1 : term3 A lt2 lt3) : term40 A lt3 lt2 P.
Proof. exact (@lem359497 A lt3 lt2 P (@lem358378 A lt2 lt3 h1)). Qed.
Lemma lem359499 {A : Type'} (lt2 : type1402 A) (lt3 : type1402 A) (P : A -> Prop) (h1 : term3 A lt2 lt3) (h2 : term1 A lt3) (h3 : term8 A P) : term11 A lt2 P.
Proof. exact (@lem359498 A P lt2 lt3 h1 (@lem358454 A lt3 P h2 h3)). Qed.
Lemma lem359500 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (lt3 : type1402 A) (h1 : term3 A lt2 lt3) (h2 : term1 A lt3) : term10 A lt2 P.
Proof. exact (fun h0 : term8 A P => @lem359499 A lt2 lt3 P h1 h2 h0). Qed.
Lemma lem359505 {A : Type'} (lt2 : type1402 A) (lt3 : type1402 A) (h1 : term3 A lt2 lt3) (h2 : term1 A lt3) : term1 A lt2.
Proof. exact (fun P : A -> Prop => @lem359500 A P lt2 lt3 h1 h2). Qed.
Lemma lem359506 {A : Type'} (lt2 : type1402 A) (lt3 : type1402 A) (h1 : term3 A lt2 lt3) : term7 A lt3 lt2.
Proof. exact (fun h0 : term1 A lt3 => @lem359505 A lt2 lt3 h1 h0). Qed.
Lemma lem359507 {A : Type'} (lt2 : type1402 A) (lt3 : type1402 A) (h1 : term3 A lt2 lt3) : term6 A lt3 lt2.
Proof. exact (EQ_MP (@lem358437 A lt3 lt2) (@lem359506 A lt2 lt3 h1)). Qed.
Lemma lem359508 {A : Type'} (lt2 : type1402 A) (lt3 : type1402 A) (h1 : term2 A lt2 lt3) : @WF A lt3.
Proof. exact (proj2 (@lem358376 A lt2 lt3 h1)). Qed.
Lemma lem359509 {A : Type'} (lt2 : type1402 A) (lt3 : type1402 A) (h1 : term2 A lt2 lt3) : term3 A lt2 lt3.
Proof. exact (proj1 (@lem358376 A lt2 lt3 h1)). Qed.
Lemma lem359510 {A : Type'} (lt2 : type1402 A) (lt3 : type1402 A) (h1 : term3 A lt2 lt3) (h2 : @WF A lt3) : @WF A lt2.
Proof. exact (@lem359507 A lt2 lt3 h1 (@lem358377 A lt3 h2)). Qed.
Lemma lem359511 {A : Type'} (lt2 : type1402 A) (lt3 : type1402 A) (h1 : term3 A lt2 lt3) (h2 : @WF A lt3) : (term3 A lt2 lt3) = (@WF A lt2).
Proof. exact (prop_ext (fun h3 : term3 A lt2 lt3 => @lem359510 A lt2 lt3 h1 h2) (fun h3 : @WF A lt2 => @lem358378 A lt2 lt3 h1)). Qed.
Lemma lem359512 {A : Type'} (lt2 : type1402 A) (lt3 : type1402 A) (h1 : term3 A lt2 lt3) (h2 : @WF A lt3) : @WF A lt2.
Proof. exact (EQ_MP (@lem359511 A lt2 lt3 h1 h2) (@lem358378 A lt2 lt3 h1)). Qed.
Lemma lem359513 {A : Type'} (lt2 : type1402 A) (lt3 : type1402 A) (h1 : term3 A lt2 lt3) (h2 : term2 A lt2 lt3) : (@WF A lt3) = (@WF A lt2).
Proof. exact (prop_ext (fun h3 : @WF A lt3 => @lem359512 A lt2 lt3 h1 h3) (fun h3 : @WF A lt2 => @lem359508 A lt2 lt3 h2)). Qed.
Lemma lem359514 {A : Type'} (lt2 : type1402 A) (lt3 : type1402 A) (h1 : term3 A lt2 lt3) (h2 : term2 A lt2 lt3) : @WF A lt2.
Proof. exact (EQ_MP (@lem359513 A lt2 lt3 h1 h2) (@lem359508 A lt2 lt3 h2)). Qed.
Lemma lem359515 {A : Type'} (lt2 : type1402 A) (lt3 : type1402 A) (h1 : term2 A lt2 lt3) : (term3 A lt2 lt3) = (@WF A lt2).
Proof. exact (prop_ext (fun h2 : term3 A lt2 lt3 => @lem359514 A lt2 lt3 h2 h1) (fun h2 : @WF A lt2 => @lem359509 A lt2 lt3 h1)). Qed.
Lemma lem359516 {A : Type'} (lt2 : type1402 A) (lt3 : type1402 A) (h1 : term2 A lt2 lt3) : @WF A lt2.
Proof. exact (EQ_MP (@lem359515 A lt2 lt3 h1) (@lem359509 A lt2 lt3 h1)). Qed.
Lemma lem359517 {A : Type'} (lt3 : type1402 A) (lt2 : type1402 A) : term176 A lt3 lt2.
Proof. exact (fun h0 : term2 A lt2 lt3 => @lem359516 A lt2 lt3 h0). Qed.
Lemma lem359522 {A : Type'} (lt2 : type1402 A) : term177 A lt2.
Proof. exact (fun lt3 : type1402 A => @lem359517 A lt3 lt2). Qed.
Lemma lem359527 {A : Type'} : term178 A.
Proof. exact (fun lt2 : type1402 A => @lem359522 A lt2). Qed.
