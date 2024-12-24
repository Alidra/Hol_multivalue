Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INJN_INJ_term_abbrevs.
Require Import INJN_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1823_spec.
Require Import thm1855_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm32_spec.
Lemma lem1055409 {A : Type'} (m : nat) : term0 A m.
Proof. exact (@lem1055402 A m). Qed.
Lemma lem1055410 {A : Type'} (m : nat) : (term0 A m) = ((@INJN A m) = (term1 A m)).
Proof. exact (eq_refl (term0 A m)). Qed.
Lemma lem1055412 {A : Type'} (n1 : nat) (n2 : nat) (h1 : (@INJN A n1) = (@INJN A n2)) : (@INJN A n1) = (@INJN A n2).
Proof. exact (h1). Qed.
Lemma lem1055421 (n1 : nat) (n2 : nat) (h1 : n1 = n2) : n1 = n2.
Proof. exact (h1). Qed.
Lemma lem1055422 {A : Type'} : (@INJN A) = (@INJN A).
Proof. exact (eq_refl (@INJN A)). Qed.
Lemma lem1055423 {A : Type'} (n1 : nat) (n2 : nat) (h1 : n1 = n2) : (@INJN A n1) = (@INJN A n2).
Proof. exact (MK_COMB (@lem1055422 A) (@lem1055421 n1 n2 h1)). Qed.
Lemma lem1055424 {A : Type'} : (@eq (nat -> A -> Prop)) = (@eq (nat -> A -> Prop)).
Proof. exact (eq_refl (@eq (nat -> A -> Prop))). Qed.
Lemma lem1055425 {A : Type'} (n1 : nat) (n2 : nat) (h1 : n1 = n2) : (term2 A n1) = (term2 A n2).
Proof. exact (MK_COMB (@lem1055424 A) (@lem1055423 A n1 n2 h1)). Qed.
Lemma lem1055426 {A : Type'} (n2 : nat) : (@INJN A n2) = (@INJN A n2).
Proof. exact (eq_refl (@INJN A n2)). Qed.
Lemma lem1055427 {A : Type'} (n1 : nat) (n2 : nat) (h1 : n1 = n2) : ((@INJN A n1) = (@INJN A n2)) = ((@INJN A n2) = (@INJN A n2)).
Proof. exact (MK_COMB (@lem1055425 A n1 n2 h1) (@lem1055426 A n2)). Qed.
Lemma lem1055429 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1055430 {A : Type'} (x : type1597 A) : (x = x) = True.
Proof. exact (@lem1055429 (type1597 A) x). Qed.
Lemma lem1055431 {A : Type'} (n2 : nat) : ((@INJN A n2) = (@INJN A n2)) = True.
Proof. exact (@lem1055430 A (@INJN A n2)). Qed.
Lemma lem1055432 {A : Type'} (n1 : nat) (n2 : nat) (h1 : n1 = n2) : ((@INJN A n1) = (@INJN A n2)) = True.
Proof. exact (TRANS (@lem1055427 A n1 n2 h1) (@lem1055431 A n2)). Qed.
Lemma lem1055433 {A : Type'} (n1 : nat) (n2 : nat) (h1 : n1 = n2) : True = ((@INJN A n1) = (@INJN A n2)).
Proof. exact (SYM (@lem1055432 A n1 n2 h1)). Qed.
Lemma lem1055434 {A : Type'} (n1 : nat) (n2 : nat) (h1 : n1 = n2) : (@INJN A n1) = (@INJN A n2).
Proof. exact (EQ_MP (@lem1055433 A n1 n2 h1) (@lem0)). Qed.
Lemma lem1055438 {A : Type'} (m : nat) : (@INJN A m) = (term1 A m).
Proof. exact (EQ_MP (@lem1055410 A m) (@lem1055409 A m)). Qed.
Lemma lem1055439 {A : Type'} (n1 : nat) : (@INJN A n1) = (term1 A n1).
Proof. exact (@lem1055438 A n1). Qed.
Lemma lem1055442 {A : Type'} : (@eq (nat -> A -> Prop)) = (@eq (nat -> A -> Prop)).
Proof. exact (eq_refl (@eq (nat -> A -> Prop))). Qed.
Lemma lem1055443 {A : Type'} (n1 : nat) : (term2 A n1) = (term3 A n1).
Proof. exact (MK_COMB (@lem1055442 A) (@lem1055439 A n1)). Qed.
Lemma lem1055445 {A : Type'} (m : nat) : (@INJN A m) = (term1 A m).
Proof. exact (EQ_MP (@lem1055410 A m) (@lem1055409 A m)). Qed.
Lemma lem1055446 {A : Type'} (n2 : nat) : (@INJN A n2) = (term1 A n2).
Proof. exact (@lem1055445 A n2). Qed.
Lemma lem1055449 {A : Type'} (n1 : nat) (n2 : nat) : ((@INJN A n1) = (@INJN A n2)) = ((term1 A n1) = (term1 A n2)).
Proof. exact (MK_COMB (@lem1055443 A n1) (@lem1055446 A n2)). Qed.
Lemma lem1055452 {A : Type'} (n1 : nat) (n2 : nat) (h1 : (@INJN A n1) = (@INJN A n2)) : (term1 A n1) = (term1 A n2).
Proof. exact (EQ_MP (@lem1055449 A n1 n2) (@lem1055412 A n1 n2 h1)). Qed.
Lemma lem1055453 (n1 : nat) : n1 = n1.
Proof. exact (eq_refl n1). Qed.
Lemma lem1055454 {A : Type'} (n1 : nat) (n2 : nat) (h1 : (@INJN A n1) = (@INJN A n2)) : (term4 A n1) = (term5 A n2 n1).
Proof. exact (MK_COMB (@lem1055452 A n1 n2 h1) (@lem1055453 n1)). Qed.
Lemma lem1055455 {A : Type'} (n2 : nat) (n1 : nat) (h1 : (term4 A n1) = (term5 A n2 n1)) : (term4 A n1) = (term5 A n2 n1).
Proof. exact (h1). Qed.
Lemma lem1055456 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1055457 {A : Type'} (a : A) (n2 : nat) (n1 : nat) (h1 : (term4 A n1) = (term5 A n2 n1)) : (term6 A n1 a) = (term7 A n2 n1 a).
Proof. exact (MK_COMB (@lem1055455 A n2 n1 h1) (@lem1055456 A a)). Qed.
Lemma lem1055465 {A B : Type'} (f : A -> B) (y : A) : (term8 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1055466 {A : Type'} (f : type1597 A) (y : nat) : (term9 A f y) = (f y).
Proof. exact (@lem1055465 nat (A -> Prop) f y). Qed.
Lemma lem1055467 {A : Type'} (n1 : nat) : (term10 A n1) = (term4 A n1).
Proof. exact (@lem1055466 A (term1 A n1) n1). Qed.
Lemma lem1055468 {A : Type'} (n : nat) (n1 : nat) : (term5 A n1 n) = (term11 A n n1).
Proof. exact (eq_refl (term5 A n1 n)). Qed.
Lemma lem1055469 {A : Type'} (n1 : nat) : (term12 A n1) = (term1 A n1).
Proof. exact (fun_ext (fun n : nat => @lem1055468 A n n1)). Qed.
Lemma lem1055470 (n1 : nat) : n1 = n1.
Proof. exact (eq_refl n1). Qed.
Lemma lem1055471 {A : Type'} (n1 : nat) : (term10 A n1) = (term4 A n1).
Proof. exact (MK_COMB (@lem1055469 A n1) (@lem1055470 n1)). Qed.
Lemma lem1055472 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem1055473 {A : Type'} (n1 : nat) : (term13 A n1) = (term14 A n1).
Proof. exact (MK_COMB (@lem1055472 A) (@lem1055471 A n1)). Qed.
Lemma lem1055474 {A : Type'} (n1 : nat) : (term4 A n1) = (term15 A n1).
Proof. exact (eq_refl (term4 A n1)). Qed.
Lemma lem1055475 {A : Type'} (n1 : nat) : ((term10 A n1) = (term4 A n1)) = ((term4 A n1) = (term15 A n1)).
Proof. exact (MK_COMB (@lem1055473 A n1) (@lem1055474 A n1)). Qed.
Lemma lem1055476 {A : Type'} (n1 : nat) : (term4 A n1) = (term15 A n1).
Proof. exact (EQ_MP (@lem1055475 A n1) (@lem1055467 A n1)). Qed.
Lemma lem1055478 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1055479 (x : nat) : (x = x) = True.
Proof. exact (@lem1055478 nat x). Qed.
Lemma lem1055480 (n1 : nat) : (n1 = n1) = True.
Proof. exact (@lem1055479 n1). Qed.
Lemma lem1055481 {A : Type'} (n1 : nat) : (term15 A n1) = (term16 A).
Proof. exact (fun_ext (fun a : A => @lem1055480 n1)). Qed.
Lemma lem1055482 {A : Type'} (n1 : nat) : (term4 A n1) = (term16 A).
Proof. exact (TRANS (@lem1055476 A n1) (@lem1055481 A n1)). Qed.
Lemma lem1055483 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1055484 {A : Type'} (n1 : nat) (a : A) : (term6 A n1 a) = (term17 A a).
Proof. exact (MK_COMB (@lem1055482 A n1) (@lem1055483 A a)). Qed.
Lemma lem1055486 {A B : Type'} (f : A -> B) (y : A) : (term8 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1055487 {A : Type'} (f : A -> Prop) (y : A) : (term18 A f y) = (f y).
Proof. exact (@lem1055486 A Prop f y). Qed.
Lemma lem1055488 {A : Type'} (a : A) : (term19 A a) = (term17 A a).
Proof. exact (@lem1055487 A (term16 A) a). Qed.
Lemma lem1055489 {A : Type'} (a : A) : (term17 A a) = True.
Proof. exact (eq_refl (term17 A a)). Qed.
Lemma lem1055490 {A : Type'} : (term20 A) = (term16 A).
Proof. exact (fun_ext (fun a : A => @lem1055489 A a)). Qed.
Lemma lem1055491 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1055492 {A : Type'} (a : A) : (term19 A a) = (term17 A a).
Proof. exact (MK_COMB (@lem1055490 A) (@lem1055491 A a)). Qed.
Lemma lem1055493 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1055494 {A : Type'} (a : A) : (term21 A a) = (term22 A a).
Proof. exact (MK_COMB (@lem1055493) (@lem1055492 A a)). Qed.
Lemma lem1055495 {A : Type'} (a : A) : (term17 A a) = True.
Proof. exact (eq_refl (term17 A a)). Qed.
Lemma lem1055496 {A : Type'} (a : A) : ((term19 A a) = (term17 A a)) = ((term17 A a) = True).
Proof. exact (MK_COMB (@lem1055494 A a) (@lem1055495 A a)). Qed.
Lemma lem1055497 {A : Type'} (a : A) : (term17 A a) = True.
Proof. exact (EQ_MP (@lem1055496 A a) (@lem1055488 A a)). Qed.
Lemma lem1055498 {A : Type'} (n1 : nat) (a : A) : (term6 A n1 a) = True.
Proof. exact (TRANS (@lem1055484 A n1 a) (@lem1055497 A a)). Qed.
Lemma lem1055499 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1055500 {A : Type'} (n1 : nat) (a : A) : (term23 A n1 a) = (@eq Prop True).
Proof. exact (MK_COMB (@lem1055499) (@lem1055498 A n1 a)). Qed.
Lemma lem1055502 {A B : Type'} (f : A -> B) (y : A) : (term8 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1055503 {A : Type'} (f : type1597 A) (y : nat) : (term9 A f y) = (f y).
Proof. exact (@lem1055502 nat (A -> Prop) f y). Qed.
Lemma lem1055504 {A : Type'} (n2 : nat) (n1 : nat) : (term24 A n2 n1) = (term5 A n2 n1).
Proof. exact (@lem1055503 A (term1 A n2) n1). Qed.
Lemma lem1055505 {A : Type'} (n : nat) (n2 : nat) : (term5 A n2 n) = (term11 A n n2).
Proof. exact (eq_refl (term5 A n2 n)). Qed.
Lemma lem1055506 {A : Type'} (n2 : nat) : (term12 A n2) = (term1 A n2).
Proof. exact (fun_ext (fun n : nat => @lem1055505 A n n2)). Qed.
Lemma lem1055507 (n1 : nat) : n1 = n1.
Proof. exact (eq_refl n1). Qed.
Lemma lem1055508 {A : Type'} (n2 : nat) (n1 : nat) : (term24 A n2 n1) = (term5 A n2 n1).
Proof. exact (MK_COMB (@lem1055506 A n2) (@lem1055507 n1)). Qed.
Lemma lem1055509 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem1055510 {A : Type'} (n2 : nat) (n1 : nat) : (term25 A n2 n1) = (term26 A n2 n1).
Proof. exact (MK_COMB (@lem1055509 A) (@lem1055508 A n2 n1)). Qed.
Lemma lem1055511 {A : Type'} (n1 : nat) (n2 : nat) : (term5 A n2 n1) = (term11 A n1 n2).
Proof. exact (eq_refl (term5 A n2 n1)). Qed.
Lemma lem1055512 {A : Type'} (n1 : nat) (n2 : nat) : ((term24 A n2 n1) = (term5 A n2 n1)) = ((term5 A n2 n1) = (term11 A n1 n2)).
Proof. exact (MK_COMB (@lem1055510 A n2 n1) (@lem1055511 A n1 n2)). Qed.
Lemma lem1055513 {A : Type'} (n1 : nat) (n2 : nat) : (term5 A n2 n1) = (term11 A n1 n2).
Proof. exact (EQ_MP (@lem1055512 A n1 n2) (@lem1055504 A n2 n1)). Qed.
Lemma lem1055516 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1055517 {A : Type'} (n1 : nat) (n2 : nat) (a : A) : (term7 A n2 n1 a) = (term27 A n1 n2 a).
Proof. exact (MK_COMB (@lem1055513 A n1 n2) (@lem1055516 A a)). Qed.
Lemma lem1055519 {A B : Type'} (f : A -> B) (y : A) : (term8 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1055520 {A : Type'} (f : A -> Prop) (y : A) : (term18 A f y) = (f y).
Proof. exact (@lem1055519 A Prop f y). Qed.
Lemma lem1055521 {A : Type'} (n1 : nat) (n2 : nat) (a : A) : (term28 A n1 n2 a) = (term27 A n1 n2 a).
Proof. exact (@lem1055520 A (term11 A n1 n2) a). Qed.
Lemma lem1055522 {A : Type'} (a : A) (n1 : nat) (n2 : nat) : (term27 A n1 n2 a) = (n1 = n2).
Proof. exact (eq_refl (term27 A n1 n2 a)). Qed.
Lemma lem1055523 {A : Type'} (n1 : nat) (n2 : nat) : (term29 A n1 n2) = (term11 A n1 n2).
Proof. exact (fun_ext (fun a : A => @lem1055522 A a n1 n2)). Qed.
Lemma lem1055524 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1055525 {A : Type'} (n1 : nat) (n2 : nat) (a : A) : (term28 A n1 n2 a) = (term27 A n1 n2 a).
Proof. exact (MK_COMB (@lem1055523 A n1 n2) (@lem1055524 A a)). Qed.
Lemma lem1055526 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1055527 {A : Type'} (n1 : nat) (n2 : nat) (a : A) : (term30 A n1 n2 a) = (term31 A n1 n2 a).
Proof. exact (MK_COMB (@lem1055526) (@lem1055525 A n1 n2 a)). Qed.
Lemma lem1055528 {A : Type'} (a : A) (n1 : nat) (n2 : nat) : (term27 A n1 n2 a) = (n1 = n2).
Proof. exact (eq_refl (term27 A n1 n2 a)). Qed.
Lemma lem1055529 {A : Type'} (a : A) (n1 : nat) (n2 : nat) : ((term28 A n1 n2 a) = (term27 A n1 n2 a)) = ((term27 A n1 n2 a) = (n1 = n2)).
Proof. exact (MK_COMB (@lem1055527 A n1 n2 a) (@lem1055528 A a n1 n2)). Qed.
Lemma lem1055530 {A : Type'} (a : A) (n1 : nat) (n2 : nat) : (term27 A n1 n2 a) = (n1 = n2).
Proof. exact (EQ_MP (@lem1055529 A a n1 n2) (@lem1055521 A n1 n2 a)). Qed.
Lemma lem1055533 {A : Type'} (a : A) (n1 : nat) (n2 : nat) : (term7 A n2 n1 a) = (n1 = n2).
Proof. exact (TRANS (@lem1055517 A n1 n2 a) (@lem1055530 A a n1 n2)). Qed.
Lemma lem1055534 {A : Type'} (a : A) (n1 : nat) (n2 : nat) : ((term6 A n1 a) = (term7 A n2 n1 a)) = (True = (n1 = n2)).
Proof. exact (MK_COMB (@lem1055500 A n1 a) (@lem1055533 A a n1 n2)). Qed.
Lemma lem1055536 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem1055537 (n1 : nat) (n2 : nat) : (True = (n1 = n2)) = (n1 = n2).
Proof. exact (@lem1055536 (n1 = n2)). Qed.
Lemma lem1055540 {A : Type'} (a : A) (n1 : nat) (n2 : nat) : ((term6 A n1 a) = (term7 A n2 n1 a)) = (n1 = n2).
Proof. exact (TRANS (@lem1055534 A a n1 n2) (@lem1055537 n1 n2)). Qed.
Lemma lem1055541 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1055542 {A : Type'} (a : A) (n1 : nat) (n2 : nat) : (term32 A n2 n1 a) = (term33 n1 n2).
Proof. exact (MK_COMB (@lem1055541) (@lem1055540 A a n1 n2)). Qed.
Lemma lem1055545 (n1 : nat) (n2 : nat) : (n1 = n2) = (n1 = n2).
Proof. exact (eq_refl (n1 = n2)). Qed.
Lemma lem1055546 {A : Type'} (a : A) (n1 : nat) (n2 : nat) : (term34 A a n1 n2) = (term35 n1 n2).
Proof. exact (MK_COMB (@lem1055542 A a n1 n2) (@lem1055545 n1 n2)). Qed.
Lemma lem1055550 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem1055551 (n1 : nat) (n2 : nat) : (term35 n1 n2) = True.
Proof. exact (@lem1055550 (n1 = n2)). Qed.
Lemma lem1055552 {A : Type'} (a : A) (n1 : nat) (n2 : nat) : (term34 A a n1 n2) = True.
Proof. exact (TRANS (@lem1055546 A a n1 n2) (@lem1055551 n1 n2)). Qed.
Lemma lem1055553 {A : Type'} (a : A) (n1 : nat) (n2 : nat) : True = (term34 A a n1 n2).
Proof. exact (SYM (@lem1055552 A a n1 n2)). Qed.
Lemma lem1055554 {A : Type'} (a : A) (n1 : nat) (n2 : nat) : term34 A a n1 n2.
Proof. exact (EQ_MP (@lem1055553 A a n1 n2) (@lem0)). Qed.
Lemma lem1055555 {A : Type'} (n2 : nat) (n1 : nat) (h1 : (term4 A n1) = (term5 A n2 n1)) : n1 = n2.
Proof. exact (@lem1055554 A (@el A) n1 n2 (@lem1055457 A (@el A) n2 n1 h1)). Qed.
Lemma lem1055556 {A : Type'} (n1 : nat) (n2 : nat) : term36 A n1 n2.
Proof. exact (fun h0 : (term4 A n1) = (term5 A n2 n1) => @lem1055555 A n2 n1 h0). Qed.
Lemma lem1055558 {A : Type'} (n1 : nat) (n2 : nat) (h1 : (@INJN A n1) = (@INJN A n2)) : n1 = n2.
Proof. exact (@lem1055556 A n1 n2 (@lem1055454 A n1 n2 h1)). Qed.
Lemma lem1055559 {A : Type'} (n1 : nat) (n2 : nat) : term37 A n1 n2.
Proof. exact (fun h0 : n1 = n2 => @lem1055434 A n1 n2 h0). Qed.
Lemma lem1055560 {A : Type'} (n1 : nat) (n2 : nat) : term38 A n1 n2.
Proof. exact (fun h0 : (@INJN A n1) = (@INJN A n2) => @lem1055558 A n1 n2 h0). Qed.
Lemma lem1055561 {A : Type'} (n1 : nat) (n2 : nat) : term39 A n1 n2.
Proof. exact (conj (@lem1055560 A n1 n2) (@lem1055559 A n1 n2)). Qed.
Lemma lem1055562 {A : Type'} (n1 : nat) (n2 : nat) : (term39 A n1 n2) = (((@INJN A n1) = (@INJN A n2)) = (n1 = n2)).
Proof. exact (@lem32 ((@INJN A n1) = (@INJN A n2)) (n1 = n2)). Qed.
Lemma lem1055563 {A : Type'} (n1 : nat) (n2 : nat) : ((@INJN A n1) = (@INJN A n2)) = (n1 = n2).
Proof. exact (EQ_MP (@lem1055562 A n1 n2) (@lem1055561 A n1 n2)). Qed.
Lemma lem1055568 {A : Type'} (n1 : nat) : term40 A n1.
Proof. exact (fun n2 : nat => @lem1055563 A n1 n2). Qed.
Lemma lem1055573 {A : Type'} : term41 A.
Proof. exact (fun n1 : nat => @lem1055568 A n1). Qed.
