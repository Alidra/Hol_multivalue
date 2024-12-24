Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import IN_DELETE_EQ_term_abbrevs.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17500_spec.
Require Import thm17646_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211683_spec.
Require Import thm3211684_spec.
Lemma lem3304406 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3304407 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3304406 A P x). Qed.
Lemma lem3304408 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3304407 A s x). Qed.
Lemma lem3304409 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3304410 {A : Type'} (s : A -> Prop) (x : A) : (term0 A x s) = (term1 A s x).
Proof. exact (MK_COMB (@lem3304409) (@lem3304408 A s x)). Qed.
Lemma lem3304412 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3304413 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3304412 A P x). Qed.
Lemma lem3304414 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3304413 A s x'). Qed.
Lemma lem3304415 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : ((@IN A x s) = (@IN A x' s)) = ((s x) = (s x')).
Proof. exact (MK_COMB (@lem3304410 A s x) (@lem3304414 A s x')). Qed.
Lemma lem3304418 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3304419 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term2 A x x' s) = (term3 A x s x').
Proof. exact (MK_COMB (@lem3304418) (@lem3304415 A x s x')). Qed.
Lemma lem3304423 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term4 A x s y) = (term5 A s x y).
Proof. exact (EQ_MP (@lem3211684 A s x y) (@lem3211683 A s x y)). Qed.
Lemma lem3304424 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term4 A x s y) = (term5 A s x y).
Proof. exact (@lem3304423 A s x y). Qed.
Lemma lem3304425 {A : Type'} (s : A -> Prop) (x : A) (x' : A) : (term4 A x s x') = (term5 A s x x').
Proof. exact (@lem3304424 A s x x'). Qed.
Lemma lem3304429 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3304430 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3304429 A P x). Qed.
Lemma lem3304431 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3304430 A s x). Qed.
Lemma lem3304432 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3304433 {A : Type'} (s : A -> Prop) (x : A) : (term6 A x s) = (term7 A s x).
Proof. exact (MK_COMB (@lem3304432) (@lem3304431 A s x)). Qed.
Lemma lem3304436 {A : Type'} (x : A) (x' : A) : (term8 A x x') = (term8 A x x').
Proof. exact (eq_refl (term8 A x x')). Qed.
Lemma lem3304437 {A : Type'} (s : A -> Prop) (x : A) (x' : A) : (term5 A s x x') = (term9 A s x x').
Proof. exact (MK_COMB (@lem3304433 A s x) (@lem3304436 A x x')). Qed.
Lemma lem3304440 {A : Type'} (s : A -> Prop) (x : A) (x' : A) : (term4 A x s x') = (term9 A s x x').
Proof. exact (TRANS (@lem3304425 A s x x') (@lem3304437 A s x x')). Qed.
Lemma lem3304441 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3304442 {A : Type'} (s : A -> Prop) (x : A) (x' : A) : (term10 A x s x') = (term11 A s x x').
Proof. exact (MK_COMB (@lem3304441) (@lem3304440 A s x x')). Qed.
Lemma lem3304444 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term4 A x s y) = (term5 A s x y).
Proof. exact (EQ_MP (@lem3211684 A s x y) (@lem3211683 A s x y)). Qed.
Lemma lem3304445 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term4 A x s y) = (term5 A s x y).
Proof. exact (@lem3304444 A s x y). Qed.
Lemma lem3304446 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term4 A x' s x) = (term5 A s x' x).
Proof. exact (@lem3304445 A s x' x). Qed.
Lemma lem3304450 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3304451 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3304450 A P x). Qed.
Lemma lem3304452 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3304451 A s x'). Qed.
Lemma lem3304453 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3304454 {A : Type'} (s : A -> Prop) (x' : A) : (term6 A x' s) = (term7 A s x').
Proof. exact (MK_COMB (@lem3304453) (@lem3304452 A s x')). Qed.
Lemma lem3304457 {A : Type'} (x' : A) (x : A) : (term8 A x' x) = (term8 A x' x).
Proof. exact (eq_refl (term8 A x' x)). Qed.
Lemma lem3304458 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term5 A s x' x) = (term9 A s x' x).
Proof. exact (MK_COMB (@lem3304454 A s x') (@lem3304457 A x' x)). Qed.
Lemma lem3304461 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term4 A x' s x) = (term9 A s x' x).
Proof. exact (TRANS (@lem3304446 A s x' x) (@lem3304458 A s x' x)). Qed.
Lemma lem3304462 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : ((term4 A x s x') = (term4 A x' s x)) = ((term9 A s x x') = (term9 A s x' x)).
Proof. exact (MK_COMB (@lem3304442 A s x x') (@lem3304461 A s x' x)). Qed.
Lemma lem3304465 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (((@IN A x s) = (@IN A x' s)) = ((term4 A x s x') = (term4 A x' s x))) = (((s x) = (s x')) = ((term9 A s x x') = (term9 A s x' x))).
Proof. exact (MK_COMB (@lem3304419 A x s x') (@lem3304462 A s x' x)). Qed.
Lemma lem3304468 {A : Type'} (s : A -> Prop) (x : A) : (term12 A s x) = (term13 A s x).
Proof. exact (fun_ext (fun x' : A => @lem3304465 A s x' x)). Qed.
Lemma lem3304469 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3304470 {A : Type'} (s : A -> Prop) (x : A) : (term14 A s x) = (term15 A s x).
Proof. exact (MK_COMB (@lem3304469 A) (@lem3304468 A s x)). Qed.
Lemma lem3304475 {A : Type'} (s : A -> Prop) : (term16 A s) = (term17 A s).
Proof. exact (fun_ext (fun x : A => @lem3304470 A s x)). Qed.
Lemma lem3304476 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3304477 {A : Type'} (s : A -> Prop) : (term18 A s) = (term19 A s).
Proof. exact (MK_COMB (@lem3304476 A) (@lem3304475 A s)). Qed.
Lemma lem3304482 {A : Type'} : (term20 A) = (term21 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3304477 A s)). Qed.
Lemma lem3304483 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3304484 {A : Type'} : (term22 A) = (term23 A).
Proof. exact (MK_COMB (@lem3304483 A) (@lem3304482 A)). Qed.
Lemma lem3304489 {A : Type'} : (term23 A) = (term22 A).
Proof. exact (SYM (@lem3304484 A)). Qed.
Lemma lem3304491 (p : Prop) : p = (term24 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3304492 {A : Type'} : (term23 A) = (term25 A).
Proof. exact (@lem3304491 (term23 A)). Qed.
Lemma lem3304493 {A : Type'} : (term25 A) = (term23 A).
Proof. exact (SYM (@lem3304492 A)). Qed.
Lemma lem3304494 {A : Type'} (h1 : term26 A) : term26 A.
Proof. exact (h1). Qed.
Lemma lem3304497 {A : Type'} (h1 : term25 A) : term25 A.
Proof. exact (h1). Qed.
Lemma lem3304498 {A : Type'} : term27 A.
Proof. exact (fun h0 : term25 A => @lem3304497 A h0). Qed.
Lemma lem3304499 {A : Type'} (h1 : term27 A) : term27 A.
Proof. exact (h1). Qed.
Lemma lem3304500 {A : Type'} (h1 : term25 A) : term25 A.
Proof. exact (h1). Qed.
Lemma lem3304501 {A : Type'} (h1 : term25 A) (h2 : term27 A) : term25 A.
Proof. exact (@lem3304499 A h2 (@lem3304500 A h1)). Qed.
Lemma lem3304502 {A : Type'} (h1 : term25 A) : term28 A.
Proof. exact (fun h0 : term27 A => @lem3304501 A h1 h0). Qed.
Lemma lem3304503 {A : Type'} (h1 : term27 A) : term27 A.
Proof. exact (h1). Qed.
Lemma lem3304504 {A : Type'} (h1 : term25 A) (h2 : term27 A) : term25 A.
Proof. exact (@lem3304502 A h1 (@lem3304503 A h2)). Qed.
Lemma lem3304505 {A : Type'} (h1 : term27 A) : term27 A.
Proof. exact (fun h0 : term25 A => @lem3304504 A h0 h1). Qed.
Lemma lem3304506 {A : Type'} : term29 A.
Proof. exact (fun h0 : term27 A => @lem3304505 A h0). Qed.
Lemma lem3304509 {A : Type'} : term27 A.
Proof. exact (@lem3304506 A (@lem3304498 A)). Qed.
Lemma lem3304510 {A : Type'} : term27 A.
Proof. exact (@lem3304509 A). Qed.
Lemma lem3304512 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3304513 {A : Type'} : (term25 A) = (term30 A).
Proof. exact (@lem3304512 (term26 A)). Qed.
Lemma lem3304515 (t : Prop) : (term31 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3304516 {A : Type'} : (term30 A) = (term23 A).
Proof. exact (@lem3304515 (term23 A)). Qed.
Lemma lem3304537 {A : Type'} : (term25 A) = (term23 A).
Proof. exact (TRANS (@lem3304513 A) (@lem3304516 A)). Qed.
Lemma lem3304562 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (((s x) = (s x')) = ((term9 A s x x') = (term9 A s x' x))) = (((s x) = (s x')) = ((term9 A s x x') = (term9 A s x' x))).
Proof. exact (eq_refl (((s x) = (s x')) = ((term9 A s x x') = (term9 A s x' x)))). Qed.
Lemma lem3304563 {A : Type'} (s : A -> Prop) (x : A) : (term13 A s x) = (term13 A s x).
Proof. exact (fun_ext (fun x' : A => @lem3304562 A s x' x)). Qed.
Lemma lem3304564 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3304565 {A : Type'} (s : A -> Prop) (x : A) : (term15 A s x) = (term15 A s x).
Proof. exact (MK_COMB (@lem3304564 A) (@lem3304563 A s x)). Qed.
Lemma lem3304566 {A : Type'} (s : A -> Prop) : (term17 A s) = (term17 A s).
Proof. exact (fun_ext (fun x : A => @lem3304565 A s x)). Qed.
Lemma lem3304567 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3304568 {A : Type'} (s : A -> Prop) : (term19 A s) = (term19 A s).
Proof. exact (MK_COMB (@lem3304567 A) (@lem3304566 A s)). Qed.
Lemma lem3304569 {A : Type'} : (term21 A) = (term21 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3304568 A s)). Qed.
Lemma lem3304570 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3304571 {A : Type'} : (term23 A) = (term23 A).
Proof. exact (MK_COMB (@lem3304570 A) (@lem3304569 A)). Qed.
Lemma lem3304596 {A : Type'} : (term25 A) = (term23 A).
Proof. exact (TRANS (@lem3304537 A) (@lem3304571 A)). Qed.
Lemma lem3304597 {A : Type'} : (term23 A) = (term25 A).
Proof. exact (SYM (@lem3304596 A)). Qed.
Lemma lem3304599 (p : Prop) : p = (term24 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3304600 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (((s x) = (s x')) = ((term9 A s x x') = (term9 A s x' x))) = (term32 A s x' x).
Proof. exact (@lem3304599 (((s x) = (s x')) = ((term9 A s x x') = (term9 A s x' x)))). Qed.
Lemma lem3304601 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term32 A s x' x) = (((s x) = (s x')) = ((term9 A s x x') = (term9 A s x' x))).
Proof. exact (SYM (@lem3304600 A s x' x)). Qed.
Lemma lem3304602 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term33 A s x' x) : term33 A s x' x.
Proof. exact (h1). Qed.
Lemma lem3304617 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term34 A x s x') = (term35 A x s x').
Proof. exact (@lem17646 (s x) (s x')). Qed.
Lemma lem3304628 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : ((s x) = (s x')) = (term36 A x s x').
Proof. exact (@lem17500 (s x) (s x')). Qed.
Lemma lem3304634 {A : Type'} (x : A) (x' : A) : (term37 A x x') = (x = x').
Proof. exact (@lem16933 (x = x')). Qed.
Lemma lem3304636 {A : Type'} (s : A -> Prop) (x : A) : (term38 A s x) = (term38 A s x).
Proof. exact (eq_refl (term38 A s x)). Qed.
Lemma lem3304637 {A : Type'} (s : A -> Prop) (x : A) (x' : A) : (term39 A s x x') = (term40 A s x x').
Proof. exact (MK_COMB (@lem3304636 A s x) (@lem3304634 A x x')). Qed.
Lemma lem3304638 {A : Type'} (s : A -> Prop) (x : A) (x' : A) : (term41 A s x x') = (term39 A s x x').
Proof. exact (@lem17045 (s x) (term8 A x x')). Qed.
Lemma lem3304639 {A : Type'} (s : A -> Prop) (x : A) (x' : A) : (term41 A s x x') = (term40 A s x x').
Proof. exact (TRANS (@lem3304638 A s x x') (@lem3304637 A s x x')). Qed.
Lemma lem3304648 {A : Type'} (x' : A) (x : A) : (term37 A x' x) = (x' = x).
Proof. exact (@lem16933 (x' = x)). Qed.
Lemma lem3304650 {A : Type'} (s : A -> Prop) (x' : A) : (term38 A s x') = (term38 A s x').
Proof. exact (eq_refl (term38 A s x')). Qed.
Lemma lem3304651 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term39 A s x' x) = (term40 A s x' x).
Proof. exact (MK_COMB (@lem3304650 A s x') (@lem3304648 A x' x)). Qed.
Lemma lem3304652 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term41 A s x' x) = (term39 A s x' x).
Proof. exact (@lem17045 (s x') (term8 A x' x)). Qed.
Lemma lem3304653 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term41 A s x' x) = (term40 A s x' x).
Proof. exact (TRANS (@lem3304652 A s x' x) (@lem3304651 A s x' x)). Qed.
Lemma lem3304656 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term9 A s x' x) = (term9 A s x' x).
Proof. exact (eq_refl (term9 A s x' x)). Qed.
Lemma lem3304657 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3304658 {A : Type'} (s : A -> Prop) (x : A) (x' : A) : (term42 A s x x') = (term43 A s x x').
Proof. exact (MK_COMB (@lem3304657) (@lem3304639 A s x x')). Qed.
Lemma lem3304659 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term44 A s x' x) = (term45 A s x' x).
Proof. exact (MK_COMB (@lem3304658 A s x x') (@lem3304656 A s x' x)). Qed.
Lemma lem3304661 {A : Type'} (s : A -> Prop) (x : A) (x' : A) : (term46 A s x x') = (term46 A s x x').
Proof. exact (eq_refl (term46 A s x x')). Qed.
Lemma lem3304662 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term47 A s x' x) = (term48 A s x' x).
Proof. exact (MK_COMB (@lem3304661 A s x x') (@lem3304653 A s x' x)). Qed.
Lemma lem3304663 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3304664 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term49 A s x' x) = (term50 A s x' x).
Proof. exact (MK_COMB (@lem3304663) (@lem3304662 A s x' x)). Qed.
Lemma lem3304665 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term51 A s x' x) = (term52 A s x' x).
Proof. exact (MK_COMB (@lem3304664 A s x' x) (@lem3304659 A s x' x)). Qed.
Lemma lem3304666 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term53 A s x' x) = (term51 A s x' x).
Proof. exact (@lem17646 (term9 A s x x') (term9 A s x' x)). Qed.
Lemma lem3304667 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term53 A s x' x) = (term52 A s x' x).
Proof. exact (TRANS (@lem3304666 A s x' x) (@lem3304665 A s x' x)). Qed.
Lemma lem3304668 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3304669 {A : Type'} (s : A -> Prop) (x : A) (x' : A) : (term42 A s x x') = (term43 A s x x').
Proof. exact (MK_COMB (@lem3304668) (@lem3304639 A s x x')). Qed.
Lemma lem3304670 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term54 A s x' x) = (term55 A s x' x).
Proof. exact (MK_COMB (@lem3304669 A s x x') (@lem3304653 A s x' x)). Qed.
Lemma lem3304675 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term56 A s x' x) = (term56 A s x' x).
Proof. exact (eq_refl (term56 A s x' x)). Qed.
Lemma lem3304676 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term57 A s x' x) = (term58 A s x' x).
Proof. exact (MK_COMB (@lem3304675 A s x' x) (@lem3304670 A s x' x)). Qed.
Lemma lem3304677 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : ((term9 A s x x') = (term9 A s x' x)) = (term57 A s x' x).
Proof. exact (@lem17500 (term9 A s x x') (term9 A s x' x)). Qed.
Lemma lem3304678 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : ((term9 A s x x') = (term9 A s x' x)) = (term58 A s x' x).
Proof. exact (TRANS (@lem3304677 A s x' x) (@lem3304676 A s x' x)). Qed.
Lemma lem3304679 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3304680 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term59 A x s x') = (term60 A x s x').
Proof. exact (MK_COMB (@lem3304679) (@lem3304617 A x s x')). Qed.
Lemma lem3304681 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term61 A s x' x) = (term62 A s x' x).
Proof. exact (MK_COMB (@lem3304680 A x s x') (@lem3304678 A s x' x)). Qed.
Lemma lem3304682 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3304683 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term63 A x s x') = (term64 A x s x').
Proof. exact (MK_COMB (@lem3304682) (@lem3304628 A x s x')). Qed.
Lemma lem3304684 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term65 A s x' x) = (term66 A s x' x).
Proof. exact (MK_COMB (@lem3304683 A x s x') (@lem3304667 A s x' x)). Qed.
Lemma lem3304685 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3304686 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term67 A s x' x) = (term68 A s x' x).
Proof. exact (MK_COMB (@lem3304685) (@lem3304684 A s x' x)). Qed.
Lemma lem3304687 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term69 A s x' x) = (term70 A s x' x).
Proof. exact (MK_COMB (@lem3304686 A s x' x) (@lem3304681 A s x' x)). Qed.
Lemma lem3304688 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term33 A s x' x) = (term69 A s x' x).
Proof. exact (@lem17646 ((s x) = (s x')) ((term9 A s x x') = (term9 A s x' x))). Qed.
Lemma lem3304693 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term33 A s x' x) = (term70 A s x' x).
Proof. exact (TRANS (@lem3304688 A s x' x) (@lem3304687 A s x' x)). Qed.
Lemma lem3304876 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term33 A s x' x) : term70 A s x' x.
Proof. exact (EQ_MP (@lem3304693 A s x' x) (@lem3304602 A s x' x h1)). Qed.
Lemma lem3304877 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term66 A s x' x) : term66 A s x' x.
Proof. exact (h1). Qed.
Lemma lem3304878 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term62 A s x' x) : term62 A s x' x.
Proof. exact (h1). Qed.
Lemma lem3304879 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term66 A s x' x) : term52 A s x' x.
Proof. exact (proj2 (@lem3304877 A s x' x h1)). Qed.
Lemma lem3304880 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term66 A s x' x) : term36 A x s x'.
Proof. exact (proj1 (@lem3304877 A s x' x h1)). Qed.
Lemma lem3304881 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term48 A s x' x) : term48 A s x' x.
Proof. exact (h1). Qed.
Lemma lem3304882 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term45 A s x' x) : term45 A s x' x.
Proof. exact (h1). Qed.
Lemma lem3304883 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term48 A s x' x) : term40 A s x' x.
Proof. exact (proj2 (@lem3304881 A s x' x h1)). Qed.
Lemma lem3304884 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term48 A s x' x) : term9 A s x x'.
Proof. exact (proj1 (@lem3304881 A s x' x h1)). Qed.
Lemma lem3304889 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term71 A x s x') : term71 A x s x'.
Proof. exact (h1). Qed.
Lemma lem3304890 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term72 A x s x') : term72 A x s x'.
Proof. exact (h1). Qed.
Lemma lem3304896 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term72 A x s x') : term72 A x s x'.
Proof. exact (h1). Qed.
Lemma lem3304901 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term45 A s x' x) : term9 A s x' x.
Proof. exact (proj2 (@lem3304882 A s x' x h1)). Qed.
Lemma lem3304902 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term45 A s x' x) : term40 A s x x'.
Proof. exact (proj1 (@lem3304882 A s x' x h1)). Qed.
Lemma lem3304907 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term71 A x s x') : term71 A x s x'.
Proof. exact (h1). Qed.
Lemma lem3304908 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term72 A x s x') : term72 A x s x'.
Proof. exact (h1). Qed.
Lemma lem3304914 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term72 A x s x') : term72 A x s x'.
Proof. exact (h1). Qed.
Lemma lem3304919 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term62 A s x' x) : term58 A s x' x.
Proof. exact (proj2 (@lem3304878 A s x' x h1)). Qed.
Lemma lem3304920 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term62 A s x' x) : term35 A x s x'.
Proof. exact (proj1 (@lem3304878 A s x' x h1)). Qed.
Lemma lem3304921 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term73 A s x' x) : term73 A s x' x.
Proof. exact (h1). Qed.
Lemma lem3304922 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term55 A s x' x) : term55 A s x' x.
Proof. exact (h1). Qed.
Lemma lem3304923 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term73 A s x' x) : term9 A s x' x.
Proof. exact (proj2 (@lem3304921 A s x' x h1)). Qed.
Lemma lem3304924 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term73 A s x' x) : term9 A s x x'.
Proof. exact (proj1 (@lem3304921 A s x' x h1)). Qed.
Lemma lem3304929 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term74 A x s x') : term74 A x s x'.
Proof. exact (h1). Qed.
Lemma lem3304930 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term75 A x s x') : term75 A x s x'.
Proof. exact (h1). Qed.
Lemma lem3304935 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term55 A s x' x) : term40 A s x' x.
Proof. exact (proj2 (@lem3304922 A s x' x h1)). Qed.
Lemma lem3304936 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term55 A s x' x) : term40 A s x x'.
Proof. exact (proj1 (@lem3304922 A s x' x h1)). Qed.
Lemma lem3304941 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term74 A x s x') : term74 A x s x'.
Proof. exact (h1). Qed.
Lemma lem3304942 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term75 A x s x') : term75 A x s x'.
Proof. exact (h1). Qed.
Lemma lem3304947 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term74 A x s x') : term74 A x s x'.
Proof. exact (h1). Qed.
Lemma lem3304948 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term75 A x s x') : term75 A x s x'.
Proof. exact (h1). Qed.
Lemma lem3304955 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term74 A x s x') : term74 A x s x'.
Proof. exact (h1). Qed.
Lemma lem3304956 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term75 A x s x') : term75 A x s x'.
Proof. exact (h1). Qed.
Lemma lem3304961 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term74 A x s x') : term74 A x s x'.
Proof. exact (h1). Qed.
Lemma lem3304962 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term75 A x s x') : term75 A x s x'.
Proof. exact (h1). Qed.
Lemma lem3304978 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term76 A s x') : term76 A s x'.
Proof. exact (h1). Qed.
Lemma lem3305018 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3305038 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3305058 {A : Type'} (s : A -> Prop) (x : A) (h1 : term76 A s x) : term76 A s x.
Proof. exact (h1). Qed.
Lemma lem3305098 {A : Type'} (x : A) (x' : A) (h1 : x = x') : x = x'.
Proof. exact (h1). Qed.
Lemma lem3305182 {A : Type'} (s : A -> Prop) (x : A) (h1 : term76 A s x) : term76 A s x.
Proof. exact (h1). Qed.
Lemma lem3305194 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term76 A s x') : term76 A s x'.
Proof. exact (h1). Qed.
Lemma lem3305214 {A : Type'} (x : A) (x' : A) (h1 : x = x') : x = x'.
Proof. exact (h1). Qed.
Lemma lem3305230 {A : Type'} (x : A) (x' : A) (h1 : x = x') : x = x'.
Proof. exact (h1). Qed.
Lemma lem3305242 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3305258 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3305278 {A : Type'} (x : A) (x' : A) (h1 : x = x') : x = x'.
Proof. exact (h1). Qed.
Lemma lem3305294 {A : Type'} (x : A) (x' : A) (h1 : x = x') : x = x'.
Proof. exact (h1). Qed.
Lemma lem3305308 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term76 A s x') : term76 A s x'.
Proof. exact (h1). Qed.
Lemma lem3305320 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term72 A x s x') : term76 A s x.
Proof. exact (proj1 (@lem3304890 A x s x' h1)). Qed.
Lemma lem3305326 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term48 A s x' x) : term8 A x x'.
Proof. exact (proj2 (@lem3304884 A s x' x h1)). Qed.
Lemma lem3305328 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3305338 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3305342 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term72 A x s x') : term76 A s x'.
Proof. exact (proj2 (@lem3304896 A x s x' h1)). Qed.
Lemma lem3305348 {A : Type'} (s : A -> Prop) (x : A) (h1 : term76 A s x) : term76 A s x.
Proof. exact (h1). Qed.
Lemma lem3305362 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term72 A x s x') : term76 A s x'.
Proof. exact (proj2 (@lem3304908 A x s x' h1)). Qed.
Lemma lem3305366 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term45 A s x' x) : term8 A x' x.
Proof. exact (proj2 (@lem3304901 A s x' x h1)). Qed.
Lemma lem3305368 {A : Type'} (x : A) (x' : A) (h1 : x = x') : x = x'.
Proof. exact (h1). Qed.
Lemma lem3305394 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term74 A x s x') : term76 A s x'.
Proof. exact (proj2 (@lem3304929 A x s x' h1)). Qed.
Lemma lem3305404 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term75 A x s x') : term76 A s x.
Proof. exact (proj1 (@lem3304930 A x s x' h1)). Qed.
Lemma lem3305410 {A : Type'} (s : A -> Prop) (x : A) (h1 : term76 A s x) : term76 A s x.
Proof. exact (h1). Qed.
Lemma lem3305416 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term76 A s x') : term76 A s x'.
Proof. exact (h1). Qed.
Lemma lem3305426 {A : Type'} (x : A) (x' : A) (h1 : x = x') : x = x'.
Proof. exact (h1). Qed.
Lemma lem3305428 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term74 A x s x') : s x.
Proof. exact (proj1 (@lem3304947 A x s x' h1)). Qed.
Lemma lem3305434 {A : Type'} (x : A) (x' : A) (h1 : x = x') : x = x'.
Proof. exact (h1). Qed.
Lemma lem3305436 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term75 A x s x') : term76 A s x.
Proof. exact (proj1 (@lem3304948 A x s x' h1)). Qed.
Lemma lem3305440 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3305446 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term74 A x s x') : term76 A s x'.
Proof. exact (proj2 (@lem3304955 A x s x' h1)). Qed.
Lemma lem3305448 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3305454 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term75 A x s x') : s x'.
Proof. exact (proj2 (@lem3304956 A x s x' h1)). Qed.
Lemma lem3305458 {A : Type'} (x : A) (x' : A) (h1 : x = x') : x = x'.
Proof. exact (h1). Qed.
Lemma lem3305460 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term74 A x s x') : s x.
Proof. exact (proj1 (@lem3304961 A x s x' h1)). Qed.
Lemma lem3305466 {A : Type'} (x : A) (x' : A) (h1 : x = x') : x = x'.
Proof. exact (h1). Qed.
Lemma lem3305468 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term75 A x s x') : term76 A s x.
Proof. exact (proj1 (@lem3304962 A x s x' h1)). Qed.
Lemma lem3305499 {A : Type'} (x : A) : (term77 A x) = (term77 A x).
Proof. exact (eq_refl (term77 A x)). Qed.
Lemma lem3305500 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term78 A x x') = (term79 A x).
Proof. exact (MK_COMB (@lem3305499 A x) (@lem3305328 A x' x h1)). Qed.
Lemma lem3305501 {A : Type'} (x : A) : (term79 A x) = (term80 A x).
Proof. exact (eq_refl (term79 A x)). Qed.
Lemma lem3305502 {A : Type'} (x : A) (x' : A) : (term81 A x x') = (term81 A x x').
Proof. exact (eq_refl (term81 A x x')). Qed.
Lemma lem3305503 {A : Type'} (x' : A) (x : A) : ((term78 A x x') = (term79 A x)) = ((term78 A x x') = (term80 A x)).
Proof. exact (MK_COMB (@lem3305502 A x x') (@lem3305501 A x)). Qed.
Lemma lem3305504 {A : Type'} (x : A) (x' : A) : (term78 A x x') = (term8 A x x').
Proof. exact (eq_refl (term78 A x x')). Qed.
Lemma lem3305505 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3305506 {A : Type'} (x : A) (x' : A) : (term81 A x x') = (term82 A x x').
Proof. exact (MK_COMB (@lem3305505) (@lem3305504 A x x')). Qed.
Lemma lem3305507 {A : Type'} (x : A) : (term80 A x) = (term80 A x).
Proof. exact (eq_refl (term80 A x)). Qed.
Lemma lem3305508 {A : Type'} (x' : A) (x : A) : ((term78 A x x') = (term80 A x)) = ((term8 A x x') = (term80 A x)).
Proof. exact (MK_COMB (@lem3305506 A x x') (@lem3305507 A x)). Qed.
Lemma lem3305509 {A : Type'} (x' : A) (x : A) : ((term78 A x x') = (term79 A x)) = ((term8 A x x') = (term80 A x)).
Proof. exact (TRANS (@lem3305503 A x' x) (@lem3305508 A x' x)). Qed.
Lemma lem3305510 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term8 A x x') = (term80 A x).
Proof. exact (EQ_MP (@lem3305509 A x' x) (@lem3305500 A x' x h1)). Qed.
Lemma lem3305511 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term48 A s x' x) (h2 : x' = x) : term80 A x.
Proof. exact (EQ_MP (@lem3305510 A x' x h2) (@lem3305326 A s x' x h1)). Qed.
Lemma lem3305594 {A : Type'} (s : A -> Prop) : (term83 A s) = (term83 A s).
Proof. exact (eq_refl (term83 A s)). Qed.
Lemma lem3305595 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : x' = x) : (term84 A s x') = (term84 A s x).
Proof. exact (MK_COMB (@lem3305594 A s) (@lem3305338 A x' x h1)). Qed.
Lemma lem3305596 {A : Type'} (s : A -> Prop) (x : A) : (term84 A s x) = (term76 A s x).
Proof. exact (eq_refl (term84 A s x)). Qed.
Lemma lem3305597 {A : Type'} (s : A -> Prop) (x' : A) : (term85 A s x') = (term85 A s x').
Proof. exact (eq_refl (term85 A s x')). Qed.
Lemma lem3305598 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : ((term84 A s x') = (term84 A s x)) = ((term84 A s x') = (term76 A s x)).
Proof. exact (MK_COMB (@lem3305597 A s x') (@lem3305596 A s x)). Qed.
Lemma lem3305599 {A : Type'} (s : A -> Prop) (x' : A) : (term84 A s x') = (term76 A s x').
Proof. exact (eq_refl (term84 A s x')). Qed.
Lemma lem3305600 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3305601 {A : Type'} (s : A -> Prop) (x' : A) : (term85 A s x') = (term86 A s x').
Proof. exact (MK_COMB (@lem3305600) (@lem3305599 A s x')). Qed.
Lemma lem3305602 {A : Type'} (s : A -> Prop) (x : A) : (term76 A s x) = (term76 A s x).
Proof. exact (eq_refl (term76 A s x)). Qed.
Lemma lem3305603 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : ((term84 A s x') = (term76 A s x)) = ((term76 A s x') = (term76 A s x)).
Proof. exact (MK_COMB (@lem3305601 A s x') (@lem3305602 A s x)). Qed.
Lemma lem3305604 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : ((term84 A s x') = (term84 A s x)) = ((term76 A s x') = (term76 A s x)).
Proof. exact (TRANS (@lem3305598 A x' s x) (@lem3305603 A x' s x)). Qed.
Lemma lem3305605 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : x' = x) : (term76 A s x') = (term76 A s x).
Proof. exact (EQ_MP (@lem3305604 A x' s x) (@lem3305595 A s x' x h1)). Qed.
Lemma lem3305606 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term72 A x s x') (h2 : x' = x) : term76 A s x.
Proof. exact (EQ_MP (@lem3305605 A s x' x h2) (@lem3305342 A x s x' h1)). Qed.
Lemma lem3305635 {A : Type'} (x' : A) : (term77 A x') = (term77 A x').
Proof. exact (eq_refl (term77 A x')). Qed.
Lemma lem3305636 {A : Type'} (x : A) (x' : A) (h1 : x = x') : (term78 A x' x) = (term79 A x').
Proof. exact (MK_COMB (@lem3305635 A x') (@lem3305368 A x x' h1)). Qed.
Lemma lem3305637 {A : Type'} (x' : A) : (term79 A x') = (term80 A x').
Proof. exact (eq_refl (term79 A x')). Qed.
Lemma lem3305638 {A : Type'} (x' : A) (x : A) : (term81 A x' x) = (term81 A x' x).
Proof. exact (eq_refl (term81 A x' x)). Qed.
Lemma lem3305639 {A : Type'} (x : A) (x' : A) : ((term78 A x' x) = (term79 A x')) = ((term78 A x' x) = (term80 A x')).
Proof. exact (MK_COMB (@lem3305638 A x' x) (@lem3305637 A x')). Qed.
Lemma lem3305640 {A : Type'} (x' : A) (x : A) : (term78 A x' x) = (term8 A x' x).
Proof. exact (eq_refl (term78 A x' x)). Qed.
Lemma lem3305641 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3305642 {A : Type'} (x' : A) (x : A) : (term81 A x' x) = (term82 A x' x).
Proof. exact (MK_COMB (@lem3305641) (@lem3305640 A x' x)). Qed.
Lemma lem3305643 {A : Type'} (x' : A) : (term80 A x') = (term80 A x').
Proof. exact (eq_refl (term80 A x')). Qed.
Lemma lem3305644 {A : Type'} (x : A) (x' : A) : ((term78 A x' x) = (term80 A x')) = ((term8 A x' x) = (term80 A x')).
Proof. exact (MK_COMB (@lem3305642 A x' x) (@lem3305643 A x')). Qed.
Lemma lem3305645 {A : Type'} (x : A) (x' : A) : ((term78 A x' x) = (term79 A x')) = ((term8 A x' x) = (term80 A x')).
Proof. exact (TRANS (@lem3305639 A x x') (@lem3305644 A x x')). Qed.
Lemma lem3305646 {A : Type'} (x : A) (x' : A) (h1 : x = x') : (term8 A x' x) = (term80 A x').
Proof. exact (EQ_MP (@lem3305645 A x x') (@lem3305636 A x x' h1)). Qed.
Lemma lem3305647 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (h1 : term45 A s x' x) (h2 : x = x') : term80 A x'.
Proof. exact (EQ_MP (@lem3305646 A x x' h2) (@lem3305366 A s x' x h1)). Qed.
Lemma lem3305742 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term72 A x s x') : term76 A s x'.
Proof. exact (proj2 (@lem3304914 A x s x' h1)). Qed.
Lemma lem3305771 {A : Type'} (s : A -> Prop) : (term87 A s) = (term87 A s).
Proof. exact (eq_refl (term87 A s)). Qed.
Lemma lem3305772 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (h1 : x = x') : (term88 A s x) = (term88 A s x').
Proof. exact (MK_COMB (@lem3305771 A s) (@lem3305426 A x x' h1)). Qed.
Lemma lem3305773 {A : Type'} (s : A -> Prop) (x' : A) : (term88 A s x') = (s x').
Proof. exact (eq_refl (term88 A s x')). Qed.
Lemma lem3305774 {A : Type'} (s : A -> Prop) (x : A) : (term89 A s x) = (term89 A s x).
Proof. exact (eq_refl (term89 A s x)). Qed.
Lemma lem3305775 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : ((term88 A s x) = (term88 A s x')) = ((term88 A s x) = (s x')).
Proof. exact (MK_COMB (@lem3305774 A s x) (@lem3305773 A s x')). Qed.
Lemma lem3305776 {A : Type'} (s : A -> Prop) (x : A) : (term88 A s x) = (s x).
Proof. exact (eq_refl (term88 A s x)). Qed.
Lemma lem3305777 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3305778 {A : Type'} (s : A -> Prop) (x : A) : (term89 A s x) = (term1 A s x).
Proof. exact (MK_COMB (@lem3305777) (@lem3305776 A s x)). Qed.
Lemma lem3305779 {A : Type'} (s : A -> Prop) (x' : A) : (s x') = (s x').
Proof. exact (eq_refl (s x')). Qed.
Lemma lem3305780 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : ((term88 A s x) = (s x')) = ((s x) = (s x')).
Proof. exact (MK_COMB (@lem3305778 A s x) (@lem3305779 A s x')). Qed.
Lemma lem3305781 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : ((term88 A s x) = (term88 A s x')) = ((s x) = (s x')).
Proof. exact (TRANS (@lem3305775 A x s x') (@lem3305780 A x s x')). Qed.
Lemma lem3305782 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (h1 : x = x') : (s x) = (s x').
Proof. exact (EQ_MP (@lem3305781 A x s x') (@lem3305772 A s x x' h1)). Qed.
Lemma lem3305797 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term74 A x s x') : term76 A s x'.
Proof. exact (proj2 (@lem3304947 A x s x' h1)). Qed.
Lemma lem3305826 {A : Type'} (s : A -> Prop) : (term83 A s) = (term83 A s).
Proof. exact (eq_refl (term83 A s)). Qed.
Lemma lem3305827 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (h1 : x = x') : (term84 A s x) = (term84 A s x').
Proof. exact (MK_COMB (@lem3305826 A s) (@lem3305434 A x x' h1)). Qed.
Lemma lem3305828 {A : Type'} (s : A -> Prop) (x' : A) : (term84 A s x') = (term76 A s x').
Proof. exact (eq_refl (term84 A s x')). Qed.
Lemma lem3305829 {A : Type'} (s : A -> Prop) (x : A) : (term85 A s x) = (term85 A s x).
Proof. exact (eq_refl (term85 A s x)). Qed.
Lemma lem3305830 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : ((term84 A s x) = (term84 A s x')) = ((term84 A s x) = (term76 A s x')).
Proof. exact (MK_COMB (@lem3305829 A s x) (@lem3305828 A s x')). Qed.
Lemma lem3305831 {A : Type'} (s : A -> Prop) (x : A) : (term84 A s x) = (term76 A s x).
Proof. exact (eq_refl (term84 A s x)). Qed.
Lemma lem3305832 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3305833 {A : Type'} (s : A -> Prop) (x : A) : (term85 A s x) = (term86 A s x).
Proof. exact (MK_COMB (@lem3305832) (@lem3305831 A s x)). Qed.
Lemma lem3305834 {A : Type'} (s : A -> Prop) (x' : A) : (term76 A s x') = (term76 A s x').
Proof. exact (eq_refl (term76 A s x')). Qed.
Lemma lem3305835 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : ((term84 A s x) = (term76 A s x')) = ((term76 A s x) = (term76 A s x')).
Proof. exact (MK_COMB (@lem3305833 A s x) (@lem3305834 A s x')). Qed.
Lemma lem3305836 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : ((term84 A s x) = (term84 A s x')) = ((term76 A s x) = (term76 A s x')).
Proof. exact (TRANS (@lem3305830 A x s x') (@lem3305835 A x s x')). Qed.
Lemma lem3305837 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (h1 : x = x') : (term76 A s x) = (term76 A s x').
Proof. exact (EQ_MP (@lem3305836 A x s x') (@lem3305827 A s x x' h1)). Qed.
Lemma lem3305838 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (h1 : term75 A x s x') (h2 : x = x') : term76 A s x'.
Proof. exact (EQ_MP (@lem3305837 A s x x' h2) (@lem3305436 A x s x' h1)). Qed.
Lemma lem3305895 {A : Type'} (s : A -> Prop) : (term83 A s) = (term83 A s).
Proof. exact (eq_refl (term83 A s)). Qed.
Lemma lem3305896 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : x' = x) : (term84 A s x') = (term84 A s x).
Proof. exact (MK_COMB (@lem3305895 A s) (@lem3305440 A x' x h1)). Qed.
Lemma lem3305897 {A : Type'} (s : A -> Prop) (x : A) : (term84 A s x) = (term76 A s x).
Proof. exact (eq_refl (term84 A s x)). Qed.
Lemma lem3305898 {A : Type'} (s : A -> Prop) (x' : A) : (term85 A s x') = (term85 A s x').
Proof. exact (eq_refl (term85 A s x')). Qed.
Lemma lem3305899 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : ((term84 A s x') = (term84 A s x)) = ((term84 A s x') = (term76 A s x)).
Proof. exact (MK_COMB (@lem3305898 A s x') (@lem3305897 A s x)). Qed.
Lemma lem3305900 {A : Type'} (s : A -> Prop) (x' : A) : (term84 A s x') = (term76 A s x').
Proof. exact (eq_refl (term84 A s x')). Qed.
Lemma lem3305901 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3305902 {A : Type'} (s : A -> Prop) (x' : A) : (term85 A s x') = (term86 A s x').
Proof. exact (MK_COMB (@lem3305901) (@lem3305900 A s x')). Qed.
Lemma lem3305903 {A : Type'} (s : A -> Prop) (x : A) : (term76 A s x) = (term76 A s x).
Proof. exact (eq_refl (term76 A s x)). Qed.
Lemma lem3305904 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : ((term84 A s x') = (term76 A s x)) = ((term76 A s x') = (term76 A s x)).
Proof. exact (MK_COMB (@lem3305902 A s x') (@lem3305903 A s x)). Qed.
Lemma lem3305905 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : ((term84 A s x') = (term84 A s x)) = ((term76 A s x') = (term76 A s x)).
Proof. exact (TRANS (@lem3305899 A x' s x) (@lem3305904 A x' s x)). Qed.
Lemma lem3305906 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : x' = x) : (term76 A s x') = (term76 A s x).
Proof. exact (EQ_MP (@lem3305905 A x' s x) (@lem3305896 A s x' x h1)). Qed.
Lemma lem3305907 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term74 A x s x') (h2 : x' = x) : term76 A s x.
Proof. exact (EQ_MP (@lem3305906 A s x' x h2) (@lem3305446 A x s x' h1)). Qed.
Lemma lem3305949 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term75 A x s x') : term76 A s x.
Proof. exact (proj1 (@lem3304956 A x s x' h1)). Qed.
Lemma lem3305950 {A : Type'} (s : A -> Prop) : (term87 A s) = (term87 A s).
Proof. exact (eq_refl (term87 A s)). Qed.
Lemma lem3305951 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : x' = x) : (term88 A s x') = (term88 A s x).
Proof. exact (MK_COMB (@lem3305950 A s) (@lem3305448 A x' x h1)). Qed.
Lemma lem3305952 {A : Type'} (s : A -> Prop) (x : A) : (term88 A s x) = (s x).
Proof. exact (eq_refl (term88 A s x)). Qed.
Lemma lem3305953 {A : Type'} (s : A -> Prop) (x' : A) : (term89 A s x') = (term89 A s x').
Proof. exact (eq_refl (term89 A s x')). Qed.
Lemma lem3305954 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : ((term88 A s x') = (term88 A s x)) = ((term88 A s x') = (s x)).
Proof. exact (MK_COMB (@lem3305953 A s x') (@lem3305952 A s x)). Qed.
Lemma lem3305955 {A : Type'} (s : A -> Prop) (x' : A) : (term88 A s x') = (s x').
Proof. exact (eq_refl (term88 A s x')). Qed.
Lemma lem3305956 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3305957 {A : Type'} (s : A -> Prop) (x' : A) : (term89 A s x') = (term1 A s x').
Proof. exact (MK_COMB (@lem3305956) (@lem3305955 A s x')). Qed.
Lemma lem3305958 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem3305959 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : ((term88 A s x') = (s x)) = ((s x') = (s x)).
Proof. exact (MK_COMB (@lem3305957 A s x') (@lem3305958 A s x)). Qed.
Lemma lem3305960 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : ((term88 A s x') = (term88 A s x)) = ((s x') = (s x)).
Proof. exact (TRANS (@lem3305954 A x' s x) (@lem3305959 A x' s x)). Qed.
Lemma lem3305961 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : x' = x) : (s x') = (s x).
Proof. exact (EQ_MP (@lem3305960 A x' s x) (@lem3305951 A s x' x h1)). Qed.
Lemma lem3305990 {A : Type'} (s : A -> Prop) : (term87 A s) = (term87 A s).
Proof. exact (eq_refl (term87 A s)). Qed.
Lemma lem3305991 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (h1 : x = x') : (term88 A s x) = (term88 A s x').
Proof. exact (MK_COMB (@lem3305990 A s) (@lem3305458 A x x' h1)). Qed.
Lemma lem3305992 {A : Type'} (s : A -> Prop) (x' : A) : (term88 A s x') = (s x').
Proof. exact (eq_refl (term88 A s x')). Qed.
Lemma lem3305993 {A : Type'} (s : A -> Prop) (x : A) : (term89 A s x) = (term89 A s x).
Proof. exact (eq_refl (term89 A s x)). Qed.
Lemma lem3305994 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : ((term88 A s x) = (term88 A s x')) = ((term88 A s x) = (s x')).
Proof. exact (MK_COMB (@lem3305993 A s x) (@lem3305992 A s x')). Qed.
Lemma lem3305995 {A : Type'} (s : A -> Prop) (x : A) : (term88 A s x) = (s x).
Proof. exact (eq_refl (term88 A s x)). Qed.
Lemma lem3305996 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3305997 {A : Type'} (s : A -> Prop) (x : A) : (term89 A s x) = (term1 A s x).
Proof. exact (MK_COMB (@lem3305996) (@lem3305995 A s x)). Qed.
Lemma lem3305998 {A : Type'} (s : A -> Prop) (x' : A) : (s x') = (s x').
Proof. exact (eq_refl (s x')). Qed.
Lemma lem3305999 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : ((term88 A s x) = (s x')) = ((s x) = (s x')).
Proof. exact (MK_COMB (@lem3305997 A s x) (@lem3305998 A s x')). Qed.
Lemma lem3306000 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : ((term88 A s x) = (term88 A s x')) = ((s x) = (s x')).
Proof. exact (TRANS (@lem3305994 A x s x') (@lem3305999 A x s x')). Qed.
Lemma lem3306001 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (h1 : x = x') : (s x) = (s x').
Proof. exact (EQ_MP (@lem3306000 A x s x') (@lem3305991 A s x x' h1)). Qed.
Lemma lem3306016 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term74 A x s x') : term76 A s x'.
Proof. exact (proj2 (@lem3304961 A x s x' h1)). Qed.
Lemma lem3306044 {A : Type'} (s : A -> Prop) : (term83 A s) = (term83 A s).
Proof. exact (eq_refl (term83 A s)). Qed.
Lemma lem3306045 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (h1 : x = x') : (term84 A s x) = (term84 A s x').
Proof. exact (MK_COMB (@lem3306044 A s) (@lem3305466 A x x' h1)). Qed.
Lemma lem3306046 {A : Type'} (s : A -> Prop) (x' : A) : (term84 A s x') = (term76 A s x').
Proof. exact (eq_refl (term84 A s x')). Qed.
Lemma lem3306047 {A : Type'} (s : A -> Prop) (x : A) : (term85 A s x) = (term85 A s x).
Proof. exact (eq_refl (term85 A s x)). Qed.
Lemma lem3306048 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : ((term84 A s x) = (term84 A s x')) = ((term84 A s x) = (term76 A s x')).
Proof. exact (MK_COMB (@lem3306047 A s x) (@lem3306046 A s x')). Qed.
Lemma lem3306049 {A : Type'} (s : A -> Prop) (x : A) : (term84 A s x) = (term76 A s x).
Proof. exact (eq_refl (term84 A s x)). Qed.
Lemma lem3306050 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3306051 {A : Type'} (s : A -> Prop) (x : A) : (term85 A s x) = (term86 A s x).
Proof. exact (MK_COMB (@lem3306050) (@lem3306049 A s x)). Qed.
Lemma lem3306052 {A : Type'} (s : A -> Prop) (x' : A) : (term76 A s x') = (term76 A s x').
Proof. exact (eq_refl (term76 A s x')). Qed.
Lemma lem3306053 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : ((term84 A s x) = (term76 A s x')) = ((term76 A s x) = (term76 A s x')).
Proof. exact (MK_COMB (@lem3306051 A s x) (@lem3306052 A s x')). Qed.
Lemma lem3306054 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : ((term84 A s x) = (term84 A s x')) = ((term76 A s x) = (term76 A s x')).
Proof. exact (TRANS (@lem3306048 A x s x') (@lem3306053 A x s x')). Qed.
Lemma lem3306055 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (h1 : x = x') : (term76 A s x) = (term76 A s x').
Proof. exact (EQ_MP (@lem3306054 A x s x') (@lem3306045 A s x x' h1)). Qed.
Lemma lem3306056 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (h1 : term75 A x s x') (h2 : x = x') : term76 A s x'.
Proof. exact (EQ_MP (@lem3306055 A s x x' h2) (@lem3305468 A x s x' h1)). Qed.
Lemma lem3306086 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term71 A x s x') : s x'.
Proof. exact (proj2 (@lem3304889 A x s x' h1)). Qed.
Lemma lem3306087 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term71 A x s x') : term90 A s x'.
Proof. exact (fun h0 : term76 A s x' => @lem3306086 A x s x' h1). Qed.
Lemma lem3306089 (p : Prop) : (term91 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3306090 {A : Type'} (s : A -> Prop) (x' : A) : (term90 A s x') = (s x').
Proof. exact (@lem3306089 (s x')). Qed.
Lemma lem3306091 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term71 A x s x') : s x'.
Proof. exact (EQ_MP (@lem3306090 A s x') (@lem3306087 A x s x' h1)). Qed.
Lemma lem3306094 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3306096 {A : Type'} (s : A -> Prop) (x' : A) : (term76 A s x') = (term92 A s x').
Proof. exact (@lem3306094 (s x')). Qed.
Lemma lem3306099 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term76 A s x') : term92 A s x'.
Proof. exact (EQ_MP (@lem3306096 A s x') (@lem3305308 A s x' h1)). Qed.
Lemma lem3306102 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term76 A s x') (h2 : term71 A x s x') : False.
Proof. exact (@lem3306099 A s x' h1 (@lem3306091 A x s x' h2)). Qed.
Lemma lem3306103 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term76 A s x') (h2 : term71 A x s x') : term93.
Proof. exact (fun h0 : ~ False => @lem3306102 A x s x' h1 h2). Qed.
Lemma lem3306105 (p : Prop) : (term91 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3306106 : term93 = False.
Proof. exact (@lem3306105 False). Qed.
Lemma lem3306107 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term76 A s x') (h2 : term71 A x s x') : False.
Proof. exact (EQ_MP (@lem3306106) (@lem3306103 A x s x' h1 h2)). Qed.
Lemma lem3306123 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term48 A s x' x) : s x.
Proof. exact (proj1 (@lem3304884 A s x' x h1)). Qed.
Lemma lem3306124 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term48 A s x' x) : term90 A s x.
Proof. exact (fun h0 : term76 A s x => @lem3306123 A s x' x h1). Qed.
Lemma lem3306126 (p : Prop) : (term91 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3306127 {A : Type'} (s : A -> Prop) (x : A) : (term90 A s x) = (s x).
Proof. exact (@lem3306126 (s x)). Qed.
Lemma lem3306128 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term48 A s x' x) : s x.
Proof. exact (EQ_MP (@lem3306127 A s x) (@lem3306124 A s x' x h1)). Qed.
Lemma lem3306131 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3306133 {A : Type'} (s : A -> Prop) (x : A) : (term76 A s x) = (term92 A s x).
Proof. exact (@lem3306131 (s x)). Qed.
Lemma lem3306136 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term72 A x s x') : term92 A s x.
Proof. exact (EQ_MP (@lem3306133 A s x) (@lem3305320 A x s x' h1)). Qed.
Lemma lem3306139 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term72 A x s x') (h2 : term48 A s x' x) : False.
Proof. exact (@lem3306136 A x s x' h1 (@lem3306128 A s x' x h2)). Qed.
Lemma lem3306140 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term72 A x s x') (h2 : term48 A s x' x) : term93.
Proof. exact (fun h0 : ~ False => @lem3306139 A s x' x h1 h2). Qed.
Lemma lem3306142 (p : Prop) : (term91 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3306143 : term93 = False.
Proof. exact (@lem3306142 False). Qed.
Lemma lem3306144 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term72 A x s x') (h2 : term48 A s x' x) : False.
Proof. exact (EQ_MP (@lem3306143) (@lem3306140 A s x' x h1 h2)). Qed.
Lemma lem3306160 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3306161 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3306160 A x). Qed.
Lemma lem3306162 {A : Type'} (x : A) : term94 A x.
Proof. exact (fun h0 : term80 A x => @lem3306161 A x). Qed.
Lemma lem3306164 (p : Prop) : (term91 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3306165 {A : Type'} (x : A) : (term94 A x) = (x = x).
Proof. exact (@lem3306164 (x = x)). Qed.
Lemma lem3306166 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem3306165 A x) (@lem3306162 A x)). Qed.
Lemma lem3306169 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3306171 {A : Type'} (x : A) : (term80 A x) = (term95 A x).
Proof. exact (@lem3306169 (x = x)). Qed.
Lemma lem3306174 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term48 A s x' x) (h2 : x' = x) : term95 A x.
Proof. exact (EQ_MP (@lem3306171 A x) (@lem3305511 A s x' x h1 h2)). Qed.
Lemma lem3306177 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term48 A s x' x) (h2 : x' = x) : False.
Proof. exact (@lem3306174 A s x' x h1 h2 (@lem3306166 A x)). Qed.
Lemma lem3306178 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term48 A s x' x) (h2 : x' = x) : term93.
Proof. exact (fun h0 : ~ False => @lem3306177 A s x' x h1 h2). Qed.
Lemma lem3306180 (p : Prop) : (term91 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3306181 : term93 = False.
Proof. exact (@lem3306180 False). Qed.
Lemma lem3306198 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term48 A s x' x) : s x.
Proof. exact (proj1 (@lem3304884 A s x' x h1)). Qed.
Lemma lem3306199 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term48 A s x' x) : term90 A s x.
Proof. exact (fun h0 : term76 A s x => @lem3306198 A s x' x h1). Qed.
Lemma lem3306201 (p : Prop) : (term91 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3306202 {A : Type'} (s : A -> Prop) (x : A) : (term90 A s x) = (s x).
Proof. exact (@lem3306201 (s x)). Qed.
Lemma lem3306203 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term48 A s x' x) : s x.
Proof. exact (EQ_MP (@lem3306202 A s x) (@lem3306199 A s x' x h1)). Qed.
Lemma lem3306206 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3306208 {A : Type'} (s : A -> Prop) (x : A) : (term76 A s x) = (term92 A s x).
Proof. exact (@lem3306206 (s x)). Qed.
Lemma lem3306211 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term72 A x s x') (h2 : x' = x) : term92 A s x.
Proof. exact (EQ_MP (@lem3306208 A s x) (@lem3305606 A s x' x h1 h2)). Qed.
Lemma lem3306214 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term72 A x s x') (h2 : term48 A s x' x) (h3 : x' = x) : False.
Proof. exact (@lem3306211 A s x' x h1 h3 (@lem3306203 A s x' x h2)). Qed.
Lemma lem3306215 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term72 A x s x') (h2 : term48 A s x' x) (h3 : x' = x) : term93.
Proof. exact (fun h0 : ~ False => @lem3306214 A s x' x h1 h2 h3). Qed.
Lemma lem3306217 (p : Prop) : (term91 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3306218 : term93 = False.
Proof. exact (@lem3306217 False). Qed.
Lemma lem3306235 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term71 A x s x') : s x.
Proof. exact (proj1 (@lem3304907 A x s x' h1)). Qed.
Lemma lem3306236 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term71 A x s x') : term90 A s x.
Proof. exact (fun h0 : term76 A s x => @lem3306235 A x s x' h1). Qed.
Lemma lem3306238 (p : Prop) : (term91 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3306239 {A : Type'} (s : A -> Prop) (x : A) : (term90 A s x) = (s x).
Proof. exact (@lem3306238 (s x)). Qed.
Lemma lem3306240 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term71 A x s x') : s x.
Proof. exact (EQ_MP (@lem3306239 A s x) (@lem3306236 A x s x' h1)). Qed.
Lemma lem3306243 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3306245 {A : Type'} (s : A -> Prop) (x : A) : (term76 A s x) = (term92 A s x).
Proof. exact (@lem3306243 (s x)). Qed.
Lemma lem3306248 {A : Type'} (s : A -> Prop) (x : A) (h1 : term76 A s x) : term92 A s x.
Proof. exact (EQ_MP (@lem3306245 A s x) (@lem3305348 A s x h1)). Qed.
Lemma lem3306251 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term76 A s x) (h2 : term71 A x s x') : False.
Proof. exact (@lem3306248 A s x h1 (@lem3306240 A x s x' h2)). Qed.
Lemma lem3306252 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term76 A s x) (h2 : term71 A x s x') : term93.
Proof. exact (fun h0 : ~ False => @lem3306251 A x s x' h1 h2). Qed.
Lemma lem3306254 (p : Prop) : (term91 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3306255 : term93 = False.
Proof. exact (@lem3306254 False). Qed.
Lemma lem3306256 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term76 A s x) (h2 : term71 A x s x') : False.
Proof. exact (EQ_MP (@lem3306255) (@lem3306252 A x s x' h1 h2)). Qed.
Lemma lem3306272 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term45 A s x' x) : s x'.
Proof. exact (proj1 (@lem3304901 A s x' x h1)). Qed.
Lemma lem3306273 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term45 A s x' x) : term90 A s x'.
Proof. exact (fun h0 : term76 A s x' => @lem3306272 A s x' x h1). Qed.
Lemma lem3306275 (p : Prop) : (term91 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3306276 {A : Type'} (s : A -> Prop) (x' : A) : (term90 A s x') = (s x').
Proof. exact (@lem3306275 (s x')). Qed.
Lemma lem3306277 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term45 A s x' x) : s x'.
Proof. exact (EQ_MP (@lem3306276 A s x') (@lem3306273 A s x' x h1)). Qed.
Lemma lem3306280 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3306282 {A : Type'} (s : A -> Prop) (x' : A) : (term76 A s x') = (term92 A s x').
Proof. exact (@lem3306280 (s x')). Qed.
Lemma lem3306285 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term72 A x s x') : term92 A s x'.
Proof. exact (EQ_MP (@lem3306282 A s x') (@lem3305362 A x s x' h1)). Qed.
Lemma lem3306288 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term72 A x s x') (h2 : term45 A s x' x) : False.
Proof. exact (@lem3306285 A x s x' h1 (@lem3306277 A s x' x h2)). Qed.
Lemma lem3306289 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term72 A x s x') (h2 : term45 A s x' x) : term93.
Proof. exact (fun h0 : ~ False => @lem3306288 A s x' x h1 h2). Qed.
Lemma lem3306291 (p : Prop) : (term91 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3306292 : term93 = False.
Proof. exact (@lem3306291 False). Qed.
Lemma lem3306293 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term72 A x s x') (h2 : term45 A s x' x) : False.
Proof. exact (EQ_MP (@lem3306292) (@lem3306289 A s x' x h1 h2)). Qed.
Lemma lem3306309 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3306310 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3306309 A x). Qed.
Lemma lem3306311 {A : Type'} (x' : A) : x' = x'.
Proof. exact (@lem3306310 A x'). Qed.
Lemma lem3306312 {A : Type'} (x' : A) : term94 A x'.
Proof. exact (fun h0 : term80 A x' => @lem3306311 A x'). Qed.
Lemma lem3306314 (p : Prop) : (term91 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3306315 {A : Type'} (x' : A) : (term94 A x') = (x' = x').
Proof. exact (@lem3306314 (x' = x')). Qed.
Lemma lem3306316 {A : Type'} (x' : A) : x' = x'.
Proof. exact (EQ_MP (@lem3306315 A x') (@lem3306312 A x')). Qed.
Lemma lem3306319 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3306321 {A : Type'} (x' : A) : (term80 A x') = (term95 A x').
Proof. exact (@lem3306319 (x' = x')). Qed.
Lemma lem3306324 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (h1 : term45 A s x' x) (h2 : x = x') : term95 A x'.
Proof. exact (EQ_MP (@lem3306321 A x') (@lem3305647 A s x x' h1 h2)). Qed.
Lemma lem3306327 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (h1 : term45 A s x' x) (h2 : x = x') : False.
Proof. exact (@lem3306324 A s x x' h1 h2 (@lem3306316 A x')). Qed.
Lemma lem3306328 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (h1 : term45 A s x' x) (h2 : x = x') : term93.
Proof. exact (fun h0 : ~ False => @lem3306327 A s x x' h1 h2). Qed.
Lemma lem3306330 (p : Prop) : (term91 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3306331 : term93 = False.
Proof. exact (@lem3306330 False). Qed.
Lemma lem3306348 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term45 A s x' x) : s x'.
Proof. exact (proj1 (@lem3304901 A s x' x h1)). Qed.
Lemma lem3306349 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term45 A s x' x) : term90 A s x'.
Proof. exact (fun h0 : term76 A s x' => @lem3306348 A s x' x h1). Qed.
Lemma lem3306351 (p : Prop) : (term91 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3306352 {A : Type'} (s : A -> Prop) (x' : A) : (term90 A s x') = (s x').
Proof. exact (@lem3306351 (s x')). Qed.
Lemma lem3306353 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term45 A s x' x) : s x'.
Proof. exact (EQ_MP (@lem3306352 A s x') (@lem3306349 A s x' x h1)). Qed.
Lemma lem3306356 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3306358 {A : Type'} (s : A -> Prop) (x' : A) : (term76 A s x') = (term92 A s x').
Proof. exact (@lem3306356 (s x')). Qed.
Lemma lem3306361 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term72 A x s x') : term92 A s x'.
Proof. exact (EQ_MP (@lem3306358 A s x') (@lem3305742 A x s x' h1)). Qed.
Lemma lem3306364 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term72 A x s x') (h2 : term45 A s x' x) : False.
Proof. exact (@lem3306361 A x s x' h1 (@lem3306353 A s x' x h2)). Qed.
Lemma lem3306365 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term72 A x s x') (h2 : term45 A s x' x) : term93.
Proof. exact (fun h0 : ~ False => @lem3306364 A s x' x h1 h2). Qed.
Lemma lem3306367 (p : Prop) : (term91 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3306368 : term93 = False.
Proof. exact (@lem3306367 False). Qed.
Lemma lem3306385 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term73 A s x' x) : s x'.
Proof. exact (proj1 (@lem3304923 A s x' x h1)). Qed.
Lemma lem3306386 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term73 A s x' x) : term90 A s x'.
Proof. exact (fun h0 : term76 A s x' => @lem3306385 A s x' x h1). Qed.
Lemma lem3306388 (p : Prop) : (term91 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3306389 {A : Type'} (s : A -> Prop) (x' : A) : (term90 A s x') = (s x').
Proof. exact (@lem3306388 (s x')). Qed.
Lemma lem3306390 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term73 A s x' x) : s x'.
Proof. exact (EQ_MP (@lem3306389 A s x') (@lem3306386 A s x' x h1)). Qed.
Lemma lem3306393 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3306395 {A : Type'} (s : A -> Prop) (x' : A) : (term76 A s x') = (term92 A s x').
Proof. exact (@lem3306393 (s x')). Qed.
Lemma lem3306398 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term74 A x s x') : term92 A s x'.
Proof. exact (EQ_MP (@lem3306395 A s x') (@lem3305394 A x s x' h1)). Qed.
Lemma lem3306401 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term74 A x s x') (h2 : term73 A s x' x) : False.
Proof. exact (@lem3306398 A x s x' h1 (@lem3306390 A s x' x h2)). Qed.
Lemma lem3306402 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term74 A x s x') (h2 : term73 A s x' x) : term93.
Proof. exact (fun h0 : ~ False => @lem3306401 A s x' x h1 h2). Qed.
Lemma lem3306404 (p : Prop) : (term91 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3306405 : term93 = False.
Proof. exact (@lem3306404 False). Qed.
Lemma lem3306406 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term74 A x s x') (h2 : term73 A s x' x) : False.
Proof. exact (EQ_MP (@lem3306405) (@lem3306402 A s x' x h1 h2)). Qed.
Lemma lem3306422 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term73 A s x' x) : s x.
Proof. exact (proj1 (@lem3304924 A s x' x h1)). Qed.
Lemma lem3306423 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term73 A s x' x) : term90 A s x.
Proof. exact (fun h0 : term76 A s x => @lem3306422 A s x' x h1). Qed.
Lemma lem3306425 (p : Prop) : (term91 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3306426 {A : Type'} (s : A -> Prop) (x : A) : (term90 A s x) = (s x).
Proof. exact (@lem3306425 (s x)). Qed.
Lemma lem3306427 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term73 A s x' x) : s x.
Proof. exact (EQ_MP (@lem3306426 A s x) (@lem3306423 A s x' x h1)). Qed.
Lemma lem3306430 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3306432 {A : Type'} (s : A -> Prop) (x : A) : (term76 A s x) = (term92 A s x).
Proof. exact (@lem3306430 (s x)). Qed.
Lemma lem3306435 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term75 A x s x') : term92 A s x.
Proof. exact (EQ_MP (@lem3306432 A s x) (@lem3305404 A x s x' h1)). Qed.
Lemma lem3306438 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term75 A x s x') (h2 : term73 A s x' x) : False.
Proof. exact (@lem3306435 A x s x' h1 (@lem3306427 A s x' x h2)). Qed.
Lemma lem3306439 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term75 A x s x') (h2 : term73 A s x' x) : term93.
Proof. exact (fun h0 : ~ False => @lem3306438 A s x' x h1 h2). Qed.
Lemma lem3306441 (p : Prop) : (term91 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3306442 : term93 = False.
Proof. exact (@lem3306441 False). Qed.
Lemma lem3306443 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term75 A x s x') (h2 : term73 A s x' x) : False.
Proof. exact (EQ_MP (@lem3306442) (@lem3306439 A s x' x h1 h2)). Qed.
Lemma lem3306445 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term74 A x s x') : s x.
Proof. exact (proj1 (@lem3304941 A x s x' h1)). Qed.
Lemma lem3306446 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term74 A x s x') : term90 A s x.
Proof. exact (fun h0 : term76 A s x => @lem3306445 A x s x' h1). Qed.
Lemma lem3306448 (p : Prop) : (term91 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3306449 {A : Type'} (s : A -> Prop) (x : A) : (term90 A s x) = (s x).
Proof. exact (@lem3306448 (s x)). Qed.
Lemma lem3306450 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term74 A x s x') : s x.
Proof. exact (EQ_MP (@lem3306449 A s x) (@lem3306446 A x s x' h1)). Qed.
Lemma lem3306453 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3306455 {A : Type'} (s : A -> Prop) (x : A) : (term76 A s x) = (term92 A s x).
Proof. exact (@lem3306453 (s x)). Qed.
Lemma lem3306458 {A : Type'} (s : A -> Prop) (x : A) (h1 : term76 A s x) : term92 A s x.
Proof. exact (EQ_MP (@lem3306455 A s x) (@lem3305410 A s x h1)). Qed.
Lemma lem3306461 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term76 A s x) (h2 : term74 A x s x') : False.
Proof. exact (@lem3306458 A s x h1 (@lem3306450 A x s x' h2)). Qed.
Lemma lem3306462 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term76 A s x) (h2 : term74 A x s x') : term93.
Proof. exact (fun h0 : ~ False => @lem3306461 A x s x' h1 h2). Qed.
Lemma lem3306464 (p : Prop) : (term91 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3306465 : term93 = False.
Proof. exact (@lem3306464 False). Qed.
Lemma lem3306466 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term76 A s x) (h2 : term74 A x s x') : False.
Proof. exact (EQ_MP (@lem3306465) (@lem3306462 A x s x' h1 h2)). Qed.
Lemma lem3306468 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term75 A x s x') : s x'.
Proof. exact (proj2 (@lem3304942 A x s x' h1)). Qed.
Lemma lem3306469 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term75 A x s x') : term90 A s x'.
Proof. exact (fun h0 : term76 A s x' => @lem3306468 A x s x' h1). Qed.
Lemma lem3306471 (p : Prop) : (term91 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3306472 {A : Type'} (s : A -> Prop) (x' : A) : (term90 A s x') = (s x').
Proof. exact (@lem3306471 (s x')). Qed.
Lemma lem3306473 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term75 A x s x') : s x'.
Proof. exact (EQ_MP (@lem3306472 A s x') (@lem3306469 A x s x' h1)). Qed.
Lemma lem3306476 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3306478 {A : Type'} (s : A -> Prop) (x' : A) : (term76 A s x') = (term92 A s x').
Proof. exact (@lem3306476 (s x')). Qed.
Lemma lem3306481 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term76 A s x') : term92 A s x'.
Proof. exact (EQ_MP (@lem3306478 A s x') (@lem3305416 A s x' h1)). Qed.
Lemma lem3306484 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term76 A s x') (h2 : term75 A x s x') : False.
Proof. exact (@lem3306481 A s x' h1 (@lem3306473 A x s x' h2)). Qed.
Lemma lem3306485 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term76 A s x') (h2 : term75 A x s x') : term93.
Proof. exact (fun h0 : ~ False => @lem3306484 A x s x' h1 h2). Qed.
Lemma lem3306487 (p : Prop) : (term91 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3306488 : term93 = False.
Proof. exact (@lem3306487 False). Qed.
Lemma lem3306489 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term76 A s x') (h2 : term75 A x s x') : False.
Proof. exact (EQ_MP (@lem3306488) (@lem3306485 A x s x' h1 h2)). Qed.
Lemma lem3306491 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (h1 : term74 A x s x') (h2 : x = x') : s x'.
Proof. exact (EQ_MP (@lem3305782 A s x x' h2) (@lem3305428 A x s x' h1)). Qed.
Lemma lem3306492 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (h1 : term74 A x s x') (h2 : x = x') : term90 A s x'.
Proof. exact (fun h0 : term76 A s x' => @lem3306491 A s x x' h1 h2). Qed.
Lemma lem3306494 (p : Prop) : (term91 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3306495 {A : Type'} (s : A -> Prop) (x' : A) : (term90 A s x') = (s x').
Proof. exact (@lem3306494 (s x')). Qed.
Lemma lem3306496 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (h1 : term74 A x s x') (h2 : x = x') : s x'.
Proof. exact (EQ_MP (@lem3306495 A s x') (@lem3306492 A s x x' h1 h2)). Qed.
Lemma lem3306499 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3306501 {A : Type'} (s : A -> Prop) (x' : A) : (term76 A s x') = (term92 A s x').
Proof. exact (@lem3306499 (s x')). Qed.
Lemma lem3306504 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term74 A x s x') : term92 A s x'.
Proof. exact (EQ_MP (@lem3306501 A s x') (@lem3305797 A x s x' h1)). Qed.
Lemma lem3306507 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (h1 : term74 A x s x') (h2 : x = x') : False.
Proof. exact (@lem3306504 A x s x' h1 (@lem3306496 A s x x' h1 h2)). Qed.
Lemma lem3306508 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (h1 : term74 A x s x') (h2 : x = x') : term93.
Proof. exact (fun h0 : ~ False => @lem3306507 A s x x' h1 h2). Qed.
Lemma lem3306510 (p : Prop) : (term91 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3306511 : term93 = False.
Proof. exact (@lem3306510 False). Qed.
Lemma lem3306514 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term75 A x s x') : s x'.
Proof. exact (proj2 (@lem3304948 A x s x' h1)). Qed.
Lemma lem3306515 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term75 A x s x') : term90 A s x'.
Proof. exact (fun h0 : term76 A s x' => @lem3306514 A x s x' h1). Qed.
Lemma lem3306517 (p : Prop) : (term91 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3306518 {A : Type'} (s : A -> Prop) (x' : A) : (term90 A s x') = (s x').
Proof. exact (@lem3306517 (s x')). Qed.
Lemma lem3306519 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term75 A x s x') : s x'.
Proof. exact (EQ_MP (@lem3306518 A s x') (@lem3306515 A x s x' h1)). Qed.
Lemma lem3306522 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3306524 {A : Type'} (s : A -> Prop) (x' : A) : (term76 A s x') = (term92 A s x').
Proof. exact (@lem3306522 (s x')). Qed.
Lemma lem3306527 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (h1 : term75 A x s x') (h2 : x = x') : term92 A s x'.
Proof. exact (EQ_MP (@lem3306524 A s x') (@lem3305838 A s x x' h1 h2)). Qed.
Lemma lem3306530 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (h1 : term75 A x s x') (h2 : x = x') : False.
Proof. exact (@lem3306527 A s x x' h1 h2 (@lem3306519 A x s x' h1)). Qed.
Lemma lem3306531 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (h1 : term75 A x s x') (h2 : x = x') : term93.
Proof. exact (fun h0 : ~ False => @lem3306530 A s x x' h1 h2). Qed.
Lemma lem3306533 (p : Prop) : (term91 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3306534 : term93 = False.
Proof. exact (@lem3306533 False). Qed.
Lemma lem3306537 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term74 A x s x') : s x.
Proof. exact (proj1 (@lem3304955 A x s x' h1)). Qed.
Lemma lem3306538 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term74 A x s x') : term90 A s x.
Proof. exact (fun h0 : term76 A s x => @lem3306537 A x s x' h1). Qed.
Lemma lem3306540 (p : Prop) : (term91 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3306541 {A : Type'} (s : A -> Prop) (x : A) : (term90 A s x) = (s x).
Proof. exact (@lem3306540 (s x)). Qed.
Lemma lem3306542 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term74 A x s x') : s x.
Proof. exact (EQ_MP (@lem3306541 A s x) (@lem3306538 A x s x' h1)). Qed.
Lemma lem3306545 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3306547 {A : Type'} (s : A -> Prop) (x : A) : (term76 A s x) = (term92 A s x).
Proof. exact (@lem3306545 (s x)). Qed.
Lemma lem3306550 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term74 A x s x') (h2 : x' = x) : term92 A s x.
Proof. exact (EQ_MP (@lem3306547 A s x) (@lem3305907 A s x' x h1 h2)). Qed.
Lemma lem3306553 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term74 A x s x') (h2 : x' = x) : False.
Proof. exact (@lem3306550 A s x' x h1 h2 (@lem3306542 A x s x' h1)). Qed.
Lemma lem3306554 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term74 A x s x') (h2 : x' = x) : term93.
Proof. exact (fun h0 : ~ False => @lem3306553 A s x' x h1 h2). Qed.
Lemma lem3306556 (p : Prop) : (term91 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3306557 : term93 = False.
Proof. exact (@lem3306556 False). Qed.
Lemma lem3306560 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term75 A x s x') (h2 : x' = x) : s x.
Proof. exact (EQ_MP (@lem3305961 A s x' x h2) (@lem3305454 A x s x' h1)). Qed.
Lemma lem3306561 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term75 A x s x') (h2 : x' = x) : term90 A s x.
Proof. exact (fun h0 : term76 A s x => @lem3306560 A s x' x h1 h2). Qed.
Lemma lem3306563 (p : Prop) : (term91 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3306564 {A : Type'} (s : A -> Prop) (x : A) : (term90 A s x) = (s x).
Proof. exact (@lem3306563 (s x)). Qed.
Lemma lem3306565 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term75 A x s x') (h2 : x' = x) : s x.
Proof. exact (EQ_MP (@lem3306564 A s x) (@lem3306561 A s x' x h1 h2)). Qed.
Lemma lem3306568 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3306570 {A : Type'} (s : A -> Prop) (x : A) : (term76 A s x) = (term92 A s x).
Proof. exact (@lem3306568 (s x)). Qed.
Lemma lem3306573 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term75 A x s x') : term92 A s x.
Proof. exact (EQ_MP (@lem3306570 A s x) (@lem3305949 A x s x' h1)). Qed.
Lemma lem3306576 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term75 A x s x') (h2 : x' = x) : False.
Proof. exact (@lem3306573 A x s x' h1 (@lem3306565 A s x' x h1 h2)). Qed.
Lemma lem3306577 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term75 A x s x') (h2 : x' = x) : term93.
Proof. exact (fun h0 : ~ False => @lem3306576 A s x' x h1 h2). Qed.
Lemma lem3306579 (p : Prop) : (term91 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3306580 : term93 = False.
Proof. exact (@lem3306579 False). Qed.
Lemma lem3306583 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (h1 : term74 A x s x') (h2 : x = x') : s x'.
Proof. exact (EQ_MP (@lem3306001 A s x x' h2) (@lem3305460 A x s x' h1)). Qed.
Lemma lem3306584 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (h1 : term74 A x s x') (h2 : x = x') : term90 A s x'.
Proof. exact (fun h0 : term76 A s x' => @lem3306583 A s x x' h1 h2). Qed.
Lemma lem3306586 (p : Prop) : (term91 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3306587 {A : Type'} (s : A -> Prop) (x' : A) : (term90 A s x') = (s x').
Proof. exact (@lem3306586 (s x')). Qed.
Lemma lem3306588 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (h1 : term74 A x s x') (h2 : x = x') : s x'.
Proof. exact (EQ_MP (@lem3306587 A s x') (@lem3306584 A s x x' h1 h2)). Qed.
Lemma lem3306591 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3306593 {A : Type'} (s : A -> Prop) (x' : A) : (term76 A s x') = (term92 A s x').
Proof. exact (@lem3306591 (s x')). Qed.
Lemma lem3306596 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term74 A x s x') : term92 A s x'.
Proof. exact (EQ_MP (@lem3306593 A s x') (@lem3306016 A x s x' h1)). Qed.
Lemma lem3306599 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (h1 : term74 A x s x') (h2 : x = x') : False.
Proof. exact (@lem3306596 A x s x' h1 (@lem3306588 A s x x' h1 h2)). Qed.
Lemma lem3306600 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (h1 : term74 A x s x') (h2 : x = x') : term93.
Proof. exact (fun h0 : ~ False => @lem3306599 A s x x' h1 h2). Qed.
Lemma lem3306602 (p : Prop) : (term91 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3306603 : term93 = False.
Proof. exact (@lem3306602 False). Qed.
Lemma lem3306606 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term75 A x s x') : s x'.
Proof. exact (proj2 (@lem3304962 A x s x' h1)). Qed.
Lemma lem3306607 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term75 A x s x') : term90 A s x'.
Proof. exact (fun h0 : term76 A s x' => @lem3306606 A x s x' h1). Qed.
Lemma lem3306609 (p : Prop) : (term91 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3306610 {A : Type'} (s : A -> Prop) (x' : A) : (term90 A s x') = (s x').
Proof. exact (@lem3306609 (s x')). Qed.
Lemma lem3306611 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term75 A x s x') : s x'.
Proof. exact (EQ_MP (@lem3306610 A s x') (@lem3306607 A x s x' h1)). Qed.
Lemma lem3306614 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3306616 {A : Type'} (s : A -> Prop) (x' : A) : (term76 A s x') = (term92 A s x').
Proof. exact (@lem3306614 (s x')). Qed.
Lemma lem3306619 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (h1 : term75 A x s x') (h2 : x = x') : term92 A s x'.
Proof. exact (EQ_MP (@lem3306616 A s x') (@lem3306056 A s x x' h1 h2)). Qed.
Lemma lem3306622 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (h1 : term75 A x s x') (h2 : x = x') : False.
Proof. exact (@lem3306619 A s x x' h1 h2 (@lem3306611 A x s x' h1)). Qed.
Lemma lem3306623 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (h1 : term75 A x s x') (h2 : x = x') : term93.
Proof. exact (fun h0 : ~ False => @lem3306622 A s x x' h1 h2). Qed.
Lemma lem3306625 (p : Prop) : (term91 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3306626 : term93 = False.
Proof. exact (@lem3306625 False). Qed.
Lemma lem3306628 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (h1 : term75 A x s x') (h2 : x = x') : False.
Proof. exact (EQ_MP (@lem3306626) (@lem3306623 A s x x' h1 h2)). Qed.
Lemma lem3306629 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (h1 : term74 A x s x') (h2 : x = x') : False.
Proof. exact (EQ_MP (@lem3306603) (@lem3306600 A s x x' h1 h2)). Qed.
Lemma lem3306630 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term75 A x s x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3306580) (@lem3306577 A s x' x h1 h2)). Qed.
Lemma lem3306631 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term74 A x s x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3306557) (@lem3306554 A s x' x h1 h2)). Qed.
Lemma lem3306632 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (h1 : term75 A x s x') (h2 : x = x') : False.
Proof. exact (EQ_MP (@lem3306534) (@lem3306531 A s x x' h1 h2)). Qed.
Lemma lem3306633 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (h1 : term74 A x s x') (h2 : x = x') : False.
Proof. exact (EQ_MP (@lem3306511) (@lem3306508 A s x x' h1 h2)). Qed.
Lemma lem3306634 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term72 A x s x') (h2 : term45 A s x' x) : False.
Proof. exact (EQ_MP (@lem3306368) (@lem3306365 A s x' x h1 h2)). Qed.
Lemma lem3306635 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (h1 : term45 A s x' x) (h2 : x = x') : False.
Proof. exact (EQ_MP (@lem3306331) (@lem3306328 A s x x' h1 h2)). Qed.
Lemma lem3306636 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term72 A x s x') (h2 : term48 A s x' x) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3306218) (@lem3306215 A s x' x h1 h2 h3)). Qed.
Lemma lem3306637 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term48 A s x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3306181) (@lem3306178 A s x' x h1 h2)). Qed.
Lemma lem3306638 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (h1 : term75 A x s x') (h2 : x = x') : (x = x') = False.
Proof. exact (prop_ext (fun h3 : x = x' => @lem3306628 A s x x' h1 h2) (fun h3 : False => @lem3305466 A x x' h2)). Qed.
Lemma lem3306639 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (h1 : term75 A x s x') (h2 : x = x') : False.
Proof. exact (EQ_MP (@lem3306638 A s x x' h1 h2) (@lem3305466 A x x' h2)). Qed.
Lemma lem3306640 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (h1 : term74 A x s x') (h2 : x = x') : (x = x') = False.
Proof. exact (prop_ext (fun h3 : x = x' => @lem3306629 A s x x' h1 h2) (fun h3 : False => @lem3305458 A x x' h2)). Qed.
Lemma lem3306641 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (h1 : term74 A x s x') (h2 : x = x') : False.
Proof. exact (EQ_MP (@lem3306640 A s x x' h1 h2) (@lem3305458 A x x' h2)). Qed.
Lemma lem3306642 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term75 A x s x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3306630 A s x' x h1 h2) (fun h3 : False => @lem3305448 A x' x h2)). Qed.
Lemma lem3306643 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term75 A x s x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3306642 A s x' x h1 h2) (@lem3305448 A x' x h2)). Qed.
Lemma lem3306644 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term74 A x s x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3306631 A s x' x h1 h2) (fun h3 : False => @lem3305440 A x' x h2)). Qed.
Lemma lem3306645 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term74 A x s x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3306644 A s x' x h1 h2) (@lem3305440 A x' x h2)). Qed.
Lemma lem3306646 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (h1 : term75 A x s x') (h2 : x = x') : (x = x') = False.
Proof. exact (prop_ext (fun h3 : x = x' => @lem3306632 A s x x' h1 h2) (fun h3 : False => @lem3305434 A x x' h2)). Qed.
Lemma lem3306647 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (h1 : term75 A x s x') (h2 : x = x') : False.
Proof. exact (EQ_MP (@lem3306646 A s x x' h1 h2) (@lem3305434 A x x' h2)). Qed.
Lemma lem3306648 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (h1 : term74 A x s x') (h2 : x = x') : (x = x') = False.
Proof. exact (prop_ext (fun h3 : x = x' => @lem3306633 A s x x' h1 h2) (fun h3 : False => @lem3305426 A x x' h2)). Qed.
Lemma lem3306649 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (h1 : term74 A x s x') (h2 : x = x') : False.
Proof. exact (EQ_MP (@lem3306648 A s x x' h1 h2) (@lem3305426 A x x' h2)). Qed.
Lemma lem3306650 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term76 A s x') (h2 : term75 A x s x') : (term76 A s x') = False.
Proof. exact (prop_ext (fun h3 : term76 A s x' => @lem3306489 A x s x' h1 h2) (fun h3 : False => @lem3305416 A s x' h1)). Qed.
Lemma lem3306651 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term76 A s x') (h2 : term75 A x s x') : False.
Proof. exact (EQ_MP (@lem3306650 A x s x' h1 h2) (@lem3305416 A s x' h1)). Qed.
Lemma lem3306652 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term76 A s x) (h2 : term74 A x s x') : (term76 A s x) = False.
Proof. exact (prop_ext (fun h3 : term76 A s x => @lem3306466 A x s x' h1 h2) (fun h3 : False => @lem3305410 A s x h1)). Qed.
Lemma lem3306653 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term76 A s x) (h2 : term74 A x s x') : False.
Proof. exact (EQ_MP (@lem3306652 A x s x' h1 h2) (@lem3305410 A s x h1)). Qed.
Lemma lem3306654 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (h1 : term45 A s x' x) (h2 : x = x') : (x = x') = False.
Proof. exact (prop_ext (fun h3 : x = x' => @lem3306635 A s x x' h1 h2) (fun h3 : False => @lem3305368 A x x' h2)). Qed.
Lemma lem3306655 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (h1 : term45 A s x' x) (h2 : x = x') : False.
Proof. exact (EQ_MP (@lem3306654 A s x x' h1 h2) (@lem3305368 A x x' h2)). Qed.
Lemma lem3306656 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term76 A s x) (h2 : term71 A x s x') : (term76 A s x) = False.
Proof. exact (prop_ext (fun h3 : term76 A s x => @lem3306256 A x s x' h1 h2) (fun h3 : False => @lem3305348 A s x h1)). Qed.
Lemma lem3306657 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term76 A s x) (h2 : term71 A x s x') : False.
Proof. exact (EQ_MP (@lem3306656 A x s x' h1 h2) (@lem3305348 A s x h1)). Qed.
Lemma lem3306658 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term72 A x s x') (h2 : term48 A s x' x) (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3306636 A s x' x h1 h2 h3) (fun h4 : False => @lem3305338 A x' x h3)). Qed.
Lemma lem3306659 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term72 A x s x') (h2 : term48 A s x' x) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3306658 A s x' x h1 h2 h3) (@lem3305338 A x' x h3)). Qed.
Lemma lem3306660 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term48 A s x' x) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3306637 A s x' x h1 h2) (fun h3 : False => @lem3305328 A x' x h2)). Qed.
Lemma lem3306661 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term48 A s x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3306660 A s x' x h1 h2) (@lem3305328 A x' x h2)). Qed.
Lemma lem3306662 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term76 A s x') (h2 : term71 A x s x') : (term76 A s x') = False.
Proof. exact (prop_ext (fun h3 : term76 A s x' => @lem3306107 A x s x' h1 h2) (fun h3 : False => @lem3305308 A s x' h1)). Qed.
Lemma lem3306663 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term76 A s x') (h2 : term71 A x s x') : False.
Proof. exact (EQ_MP (@lem3306662 A x s x' h1 h2) (@lem3305308 A s x' h1)). Qed.
Lemma lem3306664 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (h1 : term75 A x s x') (h2 : x = x') : (x = x') = False.
Proof. exact (prop_ext (fun h3 : x = x' => @lem3306639 A s x x' h1 h2) (fun h3 : False => @lem3305294 A x x' h2)). Qed.
Lemma lem3306665 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (h1 : term75 A x s x') (h2 : x = x') : False.
Proof. exact (EQ_MP (@lem3306664 A s x x' h1 h2) (@lem3305294 A x x' h2)). Qed.
Lemma lem3306666 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (h1 : term74 A x s x') (h2 : x = x') : (x = x') = False.
Proof. exact (prop_ext (fun h3 : x = x' => @lem3306641 A s x x' h1 h2) (fun h3 : False => @lem3305278 A x x' h2)). Qed.
Lemma lem3306667 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (h1 : term74 A x s x') (h2 : x = x') : False.
Proof. exact (EQ_MP (@lem3306666 A s x x' h1 h2) (@lem3305278 A x x' h2)). Qed.
Lemma lem3306668 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term75 A x s x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3306643 A s x' x h1 h2) (fun h3 : False => @lem3305258 A x' x h2)). Qed.
Lemma lem3306669 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term75 A x s x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3306668 A s x' x h1 h2) (@lem3305258 A x' x h2)). Qed.
Lemma lem3306670 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term74 A x s x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3306645 A s x' x h1 h2) (fun h3 : False => @lem3305242 A x' x h2)). Qed.
Lemma lem3306671 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term74 A x s x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3306670 A s x' x h1 h2) (@lem3305242 A x' x h2)). Qed.
Lemma lem3306672 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (h1 : term75 A x s x') (h2 : x = x') : (x = x') = False.
Proof. exact (prop_ext (fun h3 : x = x' => @lem3306647 A s x x' h1 h2) (fun h3 : False => @lem3305230 A x x' h2)). Qed.
Lemma lem3306673 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (h1 : term75 A x s x') (h2 : x = x') : False.
Proof. exact (EQ_MP (@lem3306672 A s x x' h1 h2) (@lem3305230 A x x' h2)). Qed.
Lemma lem3306674 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (h1 : term74 A x s x') (h2 : x = x') : (x = x') = False.
Proof. exact (prop_ext (fun h3 : x = x' => @lem3306649 A s x x' h1 h2) (fun h3 : False => @lem3305214 A x x' h2)). Qed.
Lemma lem3306675 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (h1 : term74 A x s x') (h2 : x = x') : False.
Proof. exact (EQ_MP (@lem3306674 A s x x' h1 h2) (@lem3305214 A x x' h2)). Qed.
Lemma lem3306676 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term76 A s x') (h2 : term75 A x s x') : (term76 A s x') = False.
Proof. exact (prop_ext (fun h3 : term76 A s x' => @lem3306651 A x s x' h1 h2) (fun h3 : False => @lem3305194 A s x' h1)). Qed.
Lemma lem3306677 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term76 A s x') (h2 : term75 A x s x') : False.
Proof. exact (EQ_MP (@lem3306676 A x s x' h1 h2) (@lem3305194 A s x' h1)). Qed.
Lemma lem3306678 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term76 A s x) (h2 : term74 A x s x') : (term76 A s x) = False.
Proof. exact (prop_ext (fun h3 : term76 A s x => @lem3306653 A x s x' h1 h2) (fun h3 : False => @lem3305182 A s x h1)). Qed.
Lemma lem3306679 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term76 A s x) (h2 : term74 A x s x') : False.
Proof. exact (EQ_MP (@lem3306678 A x s x' h1 h2) (@lem3305182 A s x h1)). Qed.
Lemma lem3306680 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (h1 : term45 A s x' x) (h2 : x = x') : (x = x') = False.
Proof. exact (prop_ext (fun h3 : x = x' => @lem3306655 A s x x' h1 h2) (fun h3 : False => @lem3305098 A x x' h2)). Qed.
Lemma lem3306681 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (h1 : term45 A s x' x) (h2 : x = x') : False.
Proof. exact (EQ_MP (@lem3306680 A s x x' h1 h2) (@lem3305098 A x x' h2)). Qed.
Lemma lem3306682 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term76 A s x) (h2 : term71 A x s x') : (term76 A s x) = False.
Proof. exact (prop_ext (fun h3 : term76 A s x => @lem3306657 A x s x' h1 h2) (fun h3 : False => @lem3305058 A s x h1)). Qed.
Lemma lem3306683 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term76 A s x) (h2 : term71 A x s x') : False.
Proof. exact (EQ_MP (@lem3306682 A x s x' h1 h2) (@lem3305058 A s x h1)). Qed.
Lemma lem3306684 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term72 A x s x') (h2 : term48 A s x' x) (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3306659 A s x' x h1 h2 h3) (fun h4 : False => @lem3305038 A x' x h3)). Qed.
Lemma lem3306685 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term72 A x s x') (h2 : term48 A s x' x) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3306684 A s x' x h1 h2 h3) (@lem3305038 A x' x h3)). Qed.
Lemma lem3306686 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term48 A s x' x) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3306661 A s x' x h1 h2) (fun h3 : False => @lem3305018 A x' x h2)). Qed.
Lemma lem3306687 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term48 A s x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3306686 A s x' x h1 h2) (@lem3305018 A x' x h2)). Qed.
Lemma lem3306688 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term76 A s x') (h2 : term71 A x s x') : (term76 A s x') = False.
Proof. exact (prop_ext (fun h3 : term76 A s x' => @lem3306663 A x s x' h1 h2) (fun h3 : False => @lem3304978 A s x' h1)). Qed.
Lemma lem3306689 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term76 A s x') (h2 : term71 A x s x') : False.
Proof. exact (EQ_MP (@lem3306688 A x s x' h1 h2) (@lem3304978 A s x' h1)). Qed.
Lemma lem3306690 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (h1 : term75 A x s x') (h2 : x = x') : (x = x') = False.
Proof. exact (prop_ext (fun h3 : x = x' => @lem3306665 A s x x' h1 h2) (fun h3 : False => @lem3305294 A x x' h2)). Qed.
Lemma lem3306691 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (h1 : term75 A x s x') (h2 : x = x') : False.
Proof. exact (EQ_MP (@lem3306690 A s x x' h1 h2) (@lem3305294 A x x' h2)). Qed.
Lemma lem3306692 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (h1 : term74 A x s x') (h2 : x = x') : (x = x') = False.
Proof. exact (prop_ext (fun h3 : x = x' => @lem3306667 A s x x' h1 h2) (fun h3 : False => @lem3305278 A x x' h2)). Qed.
Lemma lem3306693 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (h1 : term74 A x s x') (h2 : x = x') : False.
Proof. exact (EQ_MP (@lem3306692 A s x x' h1 h2) (@lem3305278 A x x' h2)). Qed.
Lemma lem3306694 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term75 A x s x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3306669 A s x' x h1 h2) (fun h3 : False => @lem3305258 A x' x h2)). Qed.
Lemma lem3306695 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term75 A x s x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3306694 A s x' x h1 h2) (@lem3305258 A x' x h2)). Qed.
Lemma lem3306696 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term74 A x s x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3306671 A s x' x h1 h2) (fun h3 : False => @lem3305242 A x' x h2)). Qed.
Lemma lem3306697 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term74 A x s x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3306696 A s x' x h1 h2) (@lem3305242 A x' x h2)). Qed.
Lemma lem3306698 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (h1 : term75 A x s x') (h2 : x = x') : (x = x') = False.
Proof. exact (prop_ext (fun h3 : x = x' => @lem3306673 A s x x' h1 h2) (fun h3 : False => @lem3305230 A x x' h2)). Qed.
Lemma lem3306699 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (h1 : term75 A x s x') (h2 : x = x') : False.
Proof. exact (EQ_MP (@lem3306698 A s x x' h1 h2) (@lem3305230 A x x' h2)). Qed.
Lemma lem3306700 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (h1 : term74 A x s x') (h2 : x = x') : (x = x') = False.
Proof. exact (prop_ext (fun h3 : x = x' => @lem3306675 A s x x' h1 h2) (fun h3 : False => @lem3305214 A x x' h2)). Qed.
Lemma lem3306701 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (h1 : term74 A x s x') (h2 : x = x') : False.
Proof. exact (EQ_MP (@lem3306700 A s x x' h1 h2) (@lem3305214 A x x' h2)). Qed.
Lemma lem3306702 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term76 A s x') (h2 : term75 A x s x') : (term76 A s x') = False.
Proof. exact (prop_ext (fun h3 : term76 A s x' => @lem3306677 A x s x' h1 h2) (fun h3 : False => @lem3305194 A s x' h1)). Qed.
Lemma lem3306703 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term76 A s x') (h2 : term75 A x s x') : False.
Proof. exact (EQ_MP (@lem3306702 A x s x' h1 h2) (@lem3305194 A s x' h1)). Qed.
Lemma lem3306704 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term76 A s x) (h2 : term74 A x s x') : (term76 A s x) = False.
Proof. exact (prop_ext (fun h3 : term76 A s x => @lem3306679 A x s x' h1 h2) (fun h3 : False => @lem3305182 A s x h1)). Qed.
Lemma lem3306705 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term76 A s x) (h2 : term74 A x s x') : False.
Proof. exact (EQ_MP (@lem3306704 A x s x' h1 h2) (@lem3305182 A s x h1)). Qed.
Lemma lem3306706 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (h1 : term45 A s x' x) (h2 : x = x') : (x = x') = False.
Proof. exact (prop_ext (fun h3 : x = x' => @lem3306681 A s x x' h1 h2) (fun h3 : False => @lem3305098 A x x' h2)). Qed.
Lemma lem3306707 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (h1 : term45 A s x' x) (h2 : x = x') : False.
Proof. exact (EQ_MP (@lem3306706 A s x x' h1 h2) (@lem3305098 A x x' h2)). Qed.
Lemma lem3306708 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term76 A s x) (h2 : term71 A x s x') : (term76 A s x) = False.
Proof. exact (prop_ext (fun h3 : term76 A s x => @lem3306683 A x s x' h1 h2) (fun h3 : False => @lem3305058 A s x h1)). Qed.
Lemma lem3306709 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term76 A s x) (h2 : term71 A x s x') : False.
Proof. exact (EQ_MP (@lem3306708 A x s x' h1 h2) (@lem3305058 A s x h1)). Qed.
Lemma lem3306710 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term72 A x s x') (h2 : term48 A s x' x) (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3306685 A s x' x h1 h2 h3) (fun h4 : False => @lem3305038 A x' x h3)). Qed.
Lemma lem3306711 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term72 A x s x') (h2 : term48 A s x' x) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3306710 A s x' x h1 h2 h3) (@lem3305038 A x' x h3)). Qed.
Lemma lem3306712 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term48 A s x' x) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3306687 A s x' x h1 h2) (fun h3 : False => @lem3305018 A x' x h2)). Qed.
Lemma lem3306713 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term48 A s x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3306712 A s x' x h1 h2) (@lem3305018 A x' x h2)). Qed.
Lemma lem3306714 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term76 A s x') (h2 : term71 A x s x') : (term76 A s x') = False.
Proof. exact (prop_ext (fun h3 : term76 A s x' => @lem3306689 A x s x' h1 h2) (fun h3 : False => @lem3304978 A s x' h1)). Qed.
Lemma lem3306715 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term76 A s x') (h2 : term71 A x s x') : False.
Proof. exact (EQ_MP (@lem3306714 A x s x' h1 h2) (@lem3304978 A s x' h1)). Qed.
Lemma lem3306716 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (h1 : term62 A s x' x) (h2 : x = x') : False.
Proof. exact (or_elim (@lem3304920 A s x' x h1) (fun h0 : term74 A x s x' => @lem3306693 A s x x' h0 h2) (fun h0 : term75 A x s x' => @lem3306691 A s x x' h0 h2)). Qed.
Lemma lem3306717 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term62 A s x' x) (h2 : x' = x) : False.
Proof. exact (or_elim (@lem3304920 A s x' x h1) (fun h0 : term74 A x s x' => @lem3306697 A s x' x h0 h2) (fun h0 : term75 A x s x' => @lem3306695 A s x' x h0 h2)). Qed.
Lemma lem3306718 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term55 A s x' x) (h2 : term62 A s x' x) (h3 : x' = x) : False.
Proof. exact (or_elim (@lem3304936 A s x' x h1) (fun h0 : term76 A s x => @lem3306717 A s x' x h2 h3) (fun h0 : x = x' => @lem3306716 A s x x' h2 h0)). Qed.
Lemma lem3306719 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (h1 : term62 A s x' x) (h2 : x = x') : False.
Proof. exact (or_elim (@lem3304920 A s x' x h1) (fun h0 : term74 A x s x' => @lem3306701 A s x x' h0 h2) (fun h0 : term75 A x s x' => @lem3306699 A s x x' h0 h2)). Qed.
Lemma lem3306720 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term76 A s x) (h2 : term76 A s x') (h3 : term62 A s x' x) : False.
Proof. exact (or_elim (@lem3304920 A s x' x h3) (fun h0 : term74 A x s x' => @lem3306705 A x s x' h1 h0) (fun h0 : term75 A x s x' => @lem3306703 A x s x' h2 h0)). Qed.
Lemma lem3306721 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term76 A s x') (h2 : term55 A s x' x) (h3 : term62 A s x' x) : False.
Proof. exact (or_elim (@lem3304936 A s x' x h2) (fun h0 : term76 A s x => @lem3306720 A s x' x h0 h1 h3) (fun h0 : x = x' => @lem3306719 A s x x' h3 h0)). Qed.
Lemma lem3306722 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term55 A s x' x) (h2 : term62 A s x' x) : False.
Proof. exact (or_elim (@lem3304935 A s x' x h1) (fun h0 : term76 A s x' => @lem3306721 A s x' x h0 h1 h2) (fun h0 : x' = x => @lem3306718 A s x' x h1 h2 h0)). Qed.
Lemma lem3306723 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term73 A s x' x) (h2 : term62 A s x' x) : False.
Proof. exact (or_elim (@lem3304920 A s x' x h2) (fun h0 : term74 A x s x' => @lem3306406 A s x' x h0 h1) (fun h0 : term75 A x s x' => @lem3306443 A s x' x h0 h1)). Qed.
Lemma lem3306724 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term62 A s x' x) : False.
Proof. exact (or_elim (@lem3304919 A s x' x h1) (fun h0 : term73 A s x' x => @lem3306723 A s x' x h0 h1) (fun h0 : term55 A s x' x => @lem3306722 A s x' x h0 h1)). Qed.
Lemma lem3306725 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (h1 : term45 A s x' x) (h2 : term66 A s x' x) (h3 : x = x') : False.
Proof. exact (or_elim (@lem3304880 A s x' x h2) (fun h0 : term71 A x s x' => @lem3306707 A s x x' h1 h3) (fun h0 : term72 A x s x' => @lem3306634 A s x' x h0 h1)). Qed.
Lemma lem3306726 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term76 A s x) (h2 : term45 A s x' x) (h3 : term66 A s x' x) : False.
Proof. exact (or_elim (@lem3304880 A s x' x h3) (fun h0 : term71 A x s x' => @lem3306709 A x s x' h1 h0) (fun h0 : term72 A x s x' => @lem3306293 A s x' x h0 h2)). Qed.
Lemma lem3306727 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term45 A s x' x) (h2 : term66 A s x' x) : False.
Proof. exact (or_elim (@lem3304902 A s x' x h1) (fun h0 : term76 A s x => @lem3306726 A s x' x h0 h1 h2) (fun h0 : x = x' => @lem3306725 A s x x' h1 h2 h0)). Qed.
Lemma lem3306728 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term48 A s x' x) (h2 : term66 A s x' x) (h3 : x' = x) : False.
Proof. exact (or_elim (@lem3304880 A s x' x h2) (fun h0 : term71 A x s x' => @lem3306713 A s x' x h1 h3) (fun h0 : term72 A x s x' => @lem3306711 A s x' x h0 h1 h3)). Qed.
Lemma lem3306729 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term76 A s x') (h2 : term48 A s x' x) (h3 : term66 A s x' x) : False.
Proof. exact (or_elim (@lem3304880 A s x' x h3) (fun h0 : term71 A x s x' => @lem3306715 A x s x' h1 h0) (fun h0 : term72 A x s x' => @lem3306144 A s x' x h0 h2)). Qed.
Lemma lem3306730 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term48 A s x' x) (h2 : term66 A s x' x) : False.
Proof. exact (or_elim (@lem3304883 A s x' x h1) (fun h0 : term76 A s x' => @lem3306729 A s x' x h0 h1 h2) (fun h0 : x' = x => @lem3306728 A s x' x h1 h2 h0)). Qed.
Lemma lem3306731 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term66 A s x' x) : False.
Proof. exact (or_elim (@lem3304879 A s x' x h1) (fun h0 : term48 A s x' x => @lem3306730 A s x' x h0 h1) (fun h0 : term45 A s x' x => @lem3306727 A s x' x h0 h1)). Qed.
Lemma lem3306732 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term33 A s x' x) : False.
Proof. exact (or_elim (@lem3304876 A s x' x h1) (fun h0 : term66 A s x' x => @lem3306731 A s x' x h0) (fun h0 : term62 A s x' x => @lem3306724 A s x' x h0)). Qed.
Lemma lem3306733 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term33 A s x' x) : (term33 A s x' x) = False.
Proof. exact (prop_ext (fun h2 : term33 A s x' x => @lem3306732 A s x' x h1) (fun h2 : False => @lem3304602 A s x' x h1)). Qed.
Lemma lem3306734 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term33 A s x' x) : False.
Proof. exact (EQ_MP (@lem3306733 A s x' x h1) (@lem3304602 A s x' x h1)). Qed.
Lemma lem3306735 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : term32 A s x' x.
Proof. exact (fun h0 : term33 A s x' x => @lem3306734 A s x' x h0). Qed.
Lemma lem3306736 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : ((s x) = (s x')) = ((term9 A s x x') = (term9 A s x' x)).
Proof. exact (EQ_MP (@lem3304601 A s x' x) (@lem3306735 A s x' x)). Qed.
Lemma lem3306741 {A : Type'} (s : A -> Prop) (x : A) : term15 A s x.
Proof. exact (fun x' : A => @lem3306736 A s x' x). Qed.
Lemma lem3306746 {A : Type'} (s : A -> Prop) : term19 A s.
Proof. exact (fun x : A => @lem3306741 A s x). Qed.
Lemma lem3306751 {A : Type'} : term23 A.
Proof. exact (fun s : A -> Prop => @lem3306746 A s). Qed.
Lemma lem3306752 {A : Type'} : term25 A.
Proof. exact (EQ_MP (@lem3304597 A) (@lem3306751 A)). Qed.
Lemma lem3306754 {A : Type'} : term25 A.
Proof. exact (@lem3304510 A (@lem3306752 A)). Qed.
Lemma lem3306755 {A : Type'} (h1 : term26 A) : False.
Proof. exact (@lem3306754 A (@lem3304494 A h1)). Qed.
Lemma lem3306756 {A : Type'} (h1 : term26 A) : (term26 A) = False.
Proof. exact (prop_ext (fun h2 : term26 A => @lem3306755 A h1) (fun h2 : False => @lem3304494 A h1)). Qed.
Lemma lem3306757 {A : Type'} (h1 : term26 A) : False.
Proof. exact (EQ_MP (@lem3306756 A h1) (@lem3304494 A h1)). Qed.
Lemma lem3306758 {A : Type'} : term25 A.
Proof. exact (fun h0 : term26 A => @lem3306757 A h0). Qed.
Lemma lem3306759 {A : Type'} : term23 A.
Proof. exact (EQ_MP (@lem3304493 A) (@lem3306758 A)). Qed.
Lemma lem3306761 {A : Type'} : term22 A.
Proof. exact (EQ_MP (@lem3304489 A) (@lem3306759 A)). Qed.
