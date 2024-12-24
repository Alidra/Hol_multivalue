Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CHOICE_DEF_term_abbrevs.
Require Import CHOICE_spec.
Require Import EXTENSION_spec.
Require Import NOT_FORALL_THM_spec.
Require Import NOT_IN_EMPTY_spec.
Require Import thm0_spec.
Require Import thm10416_spec.
Require Import thm10417_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1823_spec.
Require Import thm1857_spec.
Require Import thm82_spec.
Require Import thm9261_spec.
Require Import thm9306_spec.
Lemma lem3211465 {A : Type'} (P : A -> Prop) : term0 A P.
Proof. exact (@lem10884 A P). Qed.
Lemma lem3211466 {A : Type'} (P : A -> Prop) : (term0 A P) = ((term1 A P) = (term2 A P)).
Proof. exact (eq_refl (term0 A P)). Qed.
Lemma lem3211468 {A : Type'} (x : A) : term3 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem3211469 {A : Type'} (x : A) : (term3 A x) = (term4 A x).
Proof. exact (eq_refl (term3 A x)). Qed.
Lemma lem3211470 {A : Type'} (x : A) : term4 A x.
Proof. exact (EQ_MP (@lem3211469 A x) (@lem3211468 A x)). Qed.
Lemma lem3211471 {A : Type'} (x : A) : term5 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem3211473 {A : Type'} (s : A -> Prop) : term6 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem3211474 {A : Type'} (s : A -> Prop) : (term6 A s) = (term7 A s).
Proof. exact (eq_refl (term6 A s)). Qed.
Lemma lem3211475 {A : Type'} (s : A -> Prop) : term7 A s.
Proof. exact (EQ_MP (@lem3211474 A s) (@lem3211473 A s)). Qed.
Lemma lem3211476 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term8 A s t.
Proof. exact (@lem3211475 A s t). Qed.
Lemma lem3211477 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term8 A s t) = ((s = t) = (term9 A s t)).
Proof. exact (eq_refl (term8 A s t)). Qed.
Lemma lem3211479 {A : Type'} (s : A -> Prop) : term10 A s.
Proof. exact (@lem3203700 A s). Qed.
Lemma lem3211480 {A : Type'} (s : A -> Prop) : (term10 A s) = ((@CHOICE A s) = (term11 A s)).
Proof. exact (eq_refl (term10 A s)). Qed.
Lemma lem3211491 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term9 A s t).
Proof. exact (EQ_MP (@lem3211477 A s t) (@lem3211476 A s t)). Qed.
Lemma lem3211492 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term9 A s t).
Proof. exact (@lem3211491 A s t). Qed.
Lemma lem3211493 {A : Type'} (s : A -> Prop) : (s = (@EMPTY A)) = (term12 A s).
Proof. exact (@lem3211492 A s (@EMPTY A)). Qed.
Lemma lem3211503 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211471 A x (@lem3211470 A x)). Qed.
Lemma lem3211504 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211503 A x). Qed.
Lemma lem3211505 {A : Type'} (x : A) (s : A -> Prop) : (term13 A x s) = (term13 A x s).
Proof. exact (eq_refl (term13 A x s)). Qed.
Lemma lem3211506 {A : Type'} (x : A) (s : A -> Prop) : ((@IN A x s) = (@IN A x (@EMPTY A))) = ((@IN A x s) = False).
Proof. exact (MK_COMB (@lem3211505 A x s) (@lem3211504 A x)). Qed.
Lemma lem3211508 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem3211509 {A : Type'} (x : A) (s : A -> Prop) : ((@IN A x s) = False) = (term14 A x s).
Proof. exact (@lem3211508 (@IN A x s)). Qed.
Lemma lem3211510 {A : Type'} (x : A) (s : A -> Prop) : ((@IN A x s) = (@IN A x (@EMPTY A))) = (term14 A x s).
Proof. exact (TRANS (@lem3211506 A x s) (@lem3211509 A x s)). Qed.
Lemma lem3211511 {A : Type'} (s : A -> Prop) : (term15 A s) = (term16 A s).
Proof. exact (fun_ext (fun x : A => @lem3211510 A x s)). Qed.
Lemma lem3211512 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3211513 {A : Type'} (s : A -> Prop) : (term12 A s) = (term17 A s).
Proof. exact (MK_COMB (@lem3211512 A) (@lem3211511 A s)). Qed.
Lemma lem3211518 {A : Type'} (s : A -> Prop) : (s = (@EMPTY A)) = (term17 A s).
Proof. exact (TRANS (@lem3211493 A s) (@lem3211513 A s)). Qed.
Lemma lem3211519 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3211520 {A : Type'} (s : A -> Prop) : (term18 A s) = (term19 A s).
Proof. exact (MK_COMB (@lem3211519) (@lem3211518 A s)). Qed.
Lemma lem3211522 {A : Type'} (P : A -> Prop) : (term1 A P) = (term2 A P).
Proof. exact (EQ_MP (@lem3211466 A P) (@lem3211465 A P)). Qed.
Lemma lem3211523 {A : Type'} (P : A -> Prop) : (term1 A P) = (term2 A P).
Proof. exact (@lem3211522 A P). Qed.
Lemma lem3211524 {A : Type'} (s : A -> Prop) : (term20 A s) = (term21 A s).
Proof. exact (@lem3211523 A (term16 A s)). Qed.
Lemma lem3211525 {A : Type'} (x : A) (s : A -> Prop) : (term22 A s x) = (term14 A x s).
Proof. exact (eq_refl (term22 A s x)). Qed.
Lemma lem3211526 {A : Type'} (s : A -> Prop) : (term23 A s) = (term16 A s).
Proof. exact (fun_ext (fun x : A => @lem3211525 A x s)). Qed.
Lemma lem3211527 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3211528 {A : Type'} (s : A -> Prop) : (term24 A s) = (term17 A s).
Proof. exact (MK_COMB (@lem3211527 A) (@lem3211526 A s)). Qed.
Lemma lem3211529 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3211530 {A : Type'} (s : A -> Prop) : (term20 A s) = (term19 A s).
Proof. exact (MK_COMB (@lem3211529) (@lem3211528 A s)). Qed.
Lemma lem3211531 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3211532 {A : Type'} (s : A -> Prop) : (term25 A s) = (term26 A s).
Proof. exact (MK_COMB (@lem3211531) (@lem3211530 A s)). Qed.
Lemma lem3211533 {A : Type'} (x : A) (s : A -> Prop) : (term22 A s x) = (term14 A x s).
Proof. exact (eq_refl (term22 A s x)). Qed.
Lemma lem3211534 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3211535 {A : Type'} (x : A) (s : A -> Prop) : (term27 A s x) = (term28 A x s).
Proof. exact (MK_COMB (@lem3211534) (@lem3211533 A x s)). Qed.
Lemma lem3211536 {A : Type'} (s : A -> Prop) : (term29 A s) = (term30 A s).
Proof. exact (fun_ext (fun x : A => @lem3211535 A x s)). Qed.
Lemma lem3211537 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3211538 {A : Type'} (s : A -> Prop) : (term21 A s) = (term31 A s).
Proof. exact (MK_COMB (@lem3211537 A) (@lem3211536 A s)). Qed.
Lemma lem3211539 {A : Type'} (s : A -> Prop) : ((term20 A s) = (term21 A s)) = ((term19 A s) = (term31 A s)).
Proof. exact (MK_COMB (@lem3211532 A s) (@lem3211538 A s)). Qed.
Lemma lem3211540 {A : Type'} (s : A -> Prop) : (term19 A s) = (term31 A s).
Proof. exact (EQ_MP (@lem3211539 A s) (@lem3211524 A s)). Qed.
Lemma lem3211546 {A : Type'} : (@ex A) = (term32 A).
Proof. exact (@lem9261 A (@lem9306 A)). Qed.
Lemma lem3211548 (t : Prop) : (term33 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem3211549 {A : Type'} (x : A) (s : A -> Prop) : (term28 A x s) = (@IN A x s).
Proof. exact (@lem3211548 (@IN A x s)). Qed.
Lemma lem3211550 {A : Type'} (s : A -> Prop) : (term30 A s) = (term34 A s).
Proof. exact (fun_ext (fun x : A => @lem3211549 A x s)). Qed.
Lemma lem3211551 {A : Type'} (s : A -> Prop) : (term31 A s) = (term35 A s).
Proof. exact (MK_COMB (@lem3211546 A) (@lem3211550 A s)). Qed.
Lemma lem3211553 {A B : Type'} (f : A -> B) (y : A) : (term36 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3211554 {A : Type'} (f : type686 A) (y : A -> Prop) : (term37 A f y) = (f y).
Proof. exact (@lem3211553 (A -> Prop) Prop f y). Qed.
Lemma lem3211555 {A : Type'} (s : A -> Prop) : (term38 A s) = (term35 A s).
Proof. exact (@lem3211554 A (term32 A) (term34 A s)). Qed.
Lemma lem3211556 {A : Type'} (P : A -> Prop) : (term39 A P) = (term40 A P).
Proof. exact (eq_refl (term39 A P)). Qed.
Lemma lem3211557 {A : Type'} : (term41 A) = (term32 A).
Proof. exact (fun_ext (fun P : A -> Prop => @lem3211556 A P)). Qed.
Lemma lem3211558 {A : Type'} (s : A -> Prop) : (term34 A s) = (term34 A s).
Proof. exact (eq_refl (term34 A s)). Qed.
Lemma lem3211559 {A : Type'} (s : A -> Prop) : (term38 A s) = (term35 A s).
Proof. exact (MK_COMB (@lem3211557 A) (@lem3211558 A s)). Qed.
Lemma lem3211560 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3211561 {A : Type'} (s : A -> Prop) : (term42 A s) = (term43 A s).
Proof. exact (MK_COMB (@lem3211560) (@lem3211559 A s)). Qed.
Lemma lem3211562 {A : Type'} (s : A -> Prop) : (term35 A s) = (term44 A s).
Proof. exact (eq_refl (term35 A s)). Qed.
Lemma lem3211563 {A : Type'} (s : A -> Prop) : ((term38 A s) = (term35 A s)) = ((term35 A s) = (term44 A s)).
Proof. exact (MK_COMB (@lem3211561 A s) (@lem3211562 A s)). Qed.
Lemma lem3211564 {A : Type'} (s : A -> Prop) : (term35 A s) = (term44 A s).
Proof. exact (EQ_MP (@lem3211563 A s) (@lem3211555 A s)). Qed.
Lemma lem3211566 {A B : Type'} (f : A -> B) (y : A) : (term36 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3211567 {A : Type'} (f : A -> Prop) (y : A) : (term45 A f y) = (f y).
Proof. exact (@lem3211566 A Prop f y). Qed.
Lemma lem3211568 {A : Type'} (s : A -> Prop) : (term46 A s) = (term44 A s).
Proof. exact (@lem3211567 A (term34 A s) (term11 A s)). Qed.
Lemma lem3211569 {A : Type'} (x : A) (s : A -> Prop) : (term47 A s x) = (@IN A x s).
Proof. exact (eq_refl (term47 A s x)). Qed.
Lemma lem3211570 {A : Type'} (s : A -> Prop) : (term48 A s) = (term34 A s).
Proof. exact (fun_ext (fun x : A => @lem3211569 A x s)). Qed.
Lemma lem3211571 {A : Type'} (s : A -> Prop) : (term11 A s) = (term11 A s).
Proof. exact (eq_refl (term11 A s)). Qed.
Lemma lem3211572 {A : Type'} (s : A -> Prop) : (term46 A s) = (term44 A s).
Proof. exact (MK_COMB (@lem3211570 A s) (@lem3211571 A s)). Qed.
Lemma lem3211573 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3211574 {A : Type'} (s : A -> Prop) : (term49 A s) = (term50 A s).
Proof. exact (MK_COMB (@lem3211573) (@lem3211572 A s)). Qed.
Lemma lem3211575 {A : Type'} (s : A -> Prop) : (term44 A s) = (term51 A s).
Proof. exact (eq_refl (term44 A s)). Qed.
Lemma lem3211576 {A : Type'} (s : A -> Prop) : ((term46 A s) = (term44 A s)) = ((term44 A s) = (term51 A s)).
Proof. exact (MK_COMB (@lem3211574 A s) (@lem3211575 A s)). Qed.
Lemma lem3211577 {A : Type'} (s : A -> Prop) : (term44 A s) = (term51 A s).
Proof. exact (EQ_MP (@lem3211576 A s) (@lem3211568 A s)). Qed.
Lemma lem3211578 {A : Type'} (s : A -> Prop) : (term35 A s) = (term51 A s).
Proof. exact (TRANS (@lem3211564 A s) (@lem3211577 A s)). Qed.
Lemma lem3211579 {A : Type'} (s : A -> Prop) : (term31 A s) = (term51 A s).
Proof. exact (TRANS (@lem3211551 A s) (@lem3211578 A s)). Qed.
Lemma lem3211580 {A : Type'} (s : A -> Prop) : (term19 A s) = (term51 A s).
Proof. exact (TRANS (@lem3211540 A s) (@lem3211579 A s)). Qed.
Lemma lem3211581 {A : Type'} (s : A -> Prop) : (term18 A s) = (term51 A s).
Proof. exact (TRANS (@lem3211520 A s) (@lem3211580 A s)). Qed.
Lemma lem3211582 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3211583 {A : Type'} (s : A -> Prop) : (term52 A s) = (term53 A s).
Proof. exact (MK_COMB (@lem3211582) (@lem3211581 A s)). Qed.
Lemma lem3211585 {A : Type'} (s : A -> Prop) : (@CHOICE A s) = (term11 A s).
Proof. exact (EQ_MP (@lem3211480 A s) (@lem3211479 A s)). Qed.
Lemma lem3211586 {A : Type'} (s : A -> Prop) : (@CHOICE A s) = (term11 A s).
Proof. exact (@lem3211585 A s). Qed.
Lemma lem3211587 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem3211588 {A : Type'} (s : A -> Prop) : (term54 A s) = (term55 A s).
Proof. exact (MK_COMB (@lem3211587 A) (@lem3211586 A s)). Qed.
Lemma lem3211589 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3211590 {A : Type'} (s : A -> Prop) : (term56 A s) = (term51 A s).
Proof. exact (MK_COMB (@lem3211588 A s) (@lem3211589 A s)). Qed.
Lemma lem3211591 {A : Type'} (s : A -> Prop) : (term57 A s) = (term58 A s).
Proof. exact (MK_COMB (@lem3211583 A s) (@lem3211590 A s)). Qed.
Lemma lem3211593 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem3211594 {A : Type'} (s : A -> Prop) : (term58 A s) = True.
Proof. exact (@lem3211593 (term51 A s)). Qed.
Lemma lem3211595 {A : Type'} (s : A -> Prop) : (term57 A s) = True.
Proof. exact (TRANS (@lem3211591 A s) (@lem3211594 A s)). Qed.
Lemma lem3211596 {A : Type'} : (term59 A) = (term60 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3211595 A s)). Qed.
Lemma lem3211597 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3211598 {A : Type'} : (term61 A) = (term62 A).
Proof. exact (MK_COMB (@lem3211597 A) (@lem3211596 A)). Qed.
Lemma lem3211600 {A : Type'} (t : Prop) : (term63 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3211601 {A : Type'} (t : Prop) : (term64 A t) = t.
Proof. exact (@lem3211600 (A -> Prop) t). Qed.
Lemma lem3211602 {A : Type'} : (term62 A) = True.
Proof. exact (@lem3211601 A True). Qed.
Lemma lem3211603 {A : Type'} : (term61 A) = True.
Proof. exact (TRANS (@lem3211598 A) (@lem3211602 A)). Qed.
Lemma lem3211604 {A : Type'} : True = (term61 A).
Proof. exact (SYM (@lem3211603 A)). Qed.
Lemma lem3211605 {A : Type'} : term61 A.
Proof. exact (EQ_MP (@lem3211604 A) (@lem0)). Qed.
