Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INJF_INJ_term_abbrevs.
Require Import FUN_EQ_THM_spec.
Require Import INJF_spec.
Require Import thm0_spec.
Require Import thm1052803_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1823_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm32_spec.
Lemma lem1056445 (x : nat) : term0 x.
Proof. exact (@lem1052803 x). Qed.
Lemma lem1056446 (x : nat) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1056447 (x : nat) : term1 x.
Proof. exact (EQ_MP (@lem1056446 x) (@lem1056445 x)). Qed.
Lemma lem1056448 (x : nat) (y : nat) : term2 x y.
Proof. exact (@lem1056447 x y). Qed.
Lemma lem1056449 (x : nat) (y : nat) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem1056450 (x : nat) (y : nat) : term3 x y.
Proof. exact (EQ_MP (@lem1056449 x y) (@lem1056448 x y)). Qed.
Lemma lem1056453 {A : Type'} (f : type1600 A) : term4 A f.
Proof. exact (@lem1056444 A f). Qed.
Lemma lem1056454 {A : Type'} (f : type1600 A) : (term4 A f) = ((@INJF A f) = (term5 A f)).
Proof. exact (eq_refl (term4 A f)). Qed.
Lemma lem1056456 {A B : Type'} (f : A -> B) : term6 A B f.
Proof. exact (@lem9220 A B f). Qed.
Lemma lem1056457 {A B : Type'} (f : A -> B) : (term6 A B f) = (term7 A B f).
Proof. exact (eq_refl (term6 A B f)). Qed.
Lemma lem1056458 {A B : Type'} (f : A -> B) : term7 A B f.
Proof. exact (EQ_MP (@lem1056457 A B f) (@lem1056456 A B f)). Qed.
Lemma lem1056459 {A B : Type'} (f : A -> B) (g : A -> B) : term8 A B f g.
Proof. exact (@lem1056458 A B f g). Qed.
Lemma lem1056460 {A B : Type'} (f : A -> B) (g : A -> B) : (term8 A B f g) = ((f = g) = (term9 A B f g)).
Proof. exact (eq_refl (term8 A B f g)). Qed.
Lemma lem1056462 {A : Type'} (f1 : type1600 A) (f2 : type1600 A) (h1 : (@INJF A f1) = (@INJF A f2)) : (@INJF A f1) = (@INJF A f2).
Proof. exact (h1). Qed.
Lemma lem1056471 {A : Type'} (f1 : type1600 A) (f2 : type1600 A) (h1 : f1 = f2) : f1 = f2.
Proof. exact (h1). Qed.
Lemma lem1056472 {A : Type'} : (@INJF A) = (@INJF A).
Proof. exact (eq_refl (@INJF A)). Qed.
Lemma lem1056473 {A : Type'} (f1 : type1600 A) (f2 : type1600 A) (h1 : f1 = f2) : (@INJF A f1) = (@INJF A f2).
Proof. exact (MK_COMB (@lem1056472 A) (@lem1056471 A f1 f2 h1)). Qed.
Lemma lem1056474 {A : Type'} : (@eq (nat -> A -> Prop)) = (@eq (nat -> A -> Prop)).
Proof. exact (eq_refl (@eq (nat -> A -> Prop))). Qed.
Lemma lem1056475 {A : Type'} (f1 : type1600 A) (f2 : type1600 A) (h1 : f1 = f2) : (term10 A f1) = (term10 A f2).
Proof. exact (MK_COMB (@lem1056474 A) (@lem1056473 A f1 f2 h1)). Qed.
Lemma lem1056476 {A : Type'} (f2 : type1600 A) : (@INJF A f2) = (@INJF A f2).
Proof. exact (eq_refl (@INJF A f2)). Qed.
Lemma lem1056477 {A : Type'} (f1 : type1600 A) (f2 : type1600 A) (h1 : f1 = f2) : ((@INJF A f1) = (@INJF A f2)) = ((@INJF A f2) = (@INJF A f2)).
Proof. exact (MK_COMB (@lem1056475 A f1 f2 h1) (@lem1056476 A f2)). Qed.
Lemma lem1056479 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1056480 {A : Type'} (x : type1597 A) : (x = x) = True.
Proof. exact (@lem1056479 (type1597 A) x). Qed.
Lemma lem1056481 {A : Type'} (f2 : type1600 A) : ((@INJF A f2) = (@INJF A f2)) = True.
Proof. exact (@lem1056480 A (@INJF A f2)). Qed.
Lemma lem1056482 {A : Type'} (f1 : type1600 A) (f2 : type1600 A) (h1 : f1 = f2) : ((@INJF A f1) = (@INJF A f2)) = True.
Proof. exact (TRANS (@lem1056477 A f1 f2 h1) (@lem1056481 A f2)). Qed.
Lemma lem1056483 {A : Type'} (f1 : type1600 A) (f2 : type1600 A) (h1 : f1 = f2) : True = ((@INJF A f1) = (@INJF A f2)).
Proof. exact (SYM (@lem1056482 A f1 f2 h1)). Qed.
Lemma lem1056484 {A : Type'} (f1 : type1600 A) (f2 : type1600 A) (h1 : f1 = f2) : (@INJF A f1) = (@INJF A f2).
Proof. exact (EQ_MP (@lem1056483 A f1 f2 h1) (@lem0)). Qed.
Lemma lem1056488 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term9 A B f g).
Proof. exact (EQ_MP (@lem1056460 A B f g) (@lem1056459 A B f g)). Qed.
Lemma lem1056489 {A : Type'} (f : type1600 A) (g : type1600 A) : (f = g) = (term11 A f g).
Proof. exact (@lem1056488 nat (type1597 A) f g). Qed.
Lemma lem1056490 {A : Type'} (f1 : type1600 A) (f2 : type1600 A) : (f1 = f2) = (term11 A f1 f2).
Proof. exact (@lem1056489 A f1 f2). Qed.
Lemma lem1056498 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term9 A B f g).
Proof. exact (EQ_MP (@lem1056460 A B f g) (@lem1056459 A B f g)). Qed.
Lemma lem1056499 {A : Type'} (f : type1597 A) (g : type1597 A) : (f = g) = (term12 A f g).
Proof. exact (@lem1056498 nat (A -> Prop) f g). Qed.
Lemma lem1056500 {A : Type'} (f1 : type1600 A) (f2 : type1600 A) (x : nat) : ((f1 x) = (f2 x)) = (term13 A f1 f2 x).
Proof. exact (@lem1056499 A (f1 x) (f2 x)). Qed.
Lemma lem1056508 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term9 A B f g).
Proof. exact (EQ_MP (@lem1056460 A B f g) (@lem1056459 A B f g)). Qed.
Lemma lem1056509 {A : Type'} (f : A -> Prop) (g : A -> Prop) : (f = g) = (term14 A f g).
Proof. exact (@lem1056508 A Prop f g). Qed.
Lemma lem1056510 {A : Type'} (f1 : type1600 A) (f2 : type1600 A) (x : nat) (x' : nat) : ((f1 x x') = (f2 x x')) = (term15 A f1 f2 x x').
Proof. exact (@lem1056509 A (f1 x x') (f2 x x')). Qed.
Lemma lem1056519 {A : Type'} (f1 : type1600 A) (f2 : type1600 A) (x : nat) : (term16 A f1 f2 x) = (term17 A f1 f2 x).
Proof. exact (fun_ext (fun x' : nat => @lem1056510 A f1 f2 x x')). Qed.
Lemma lem1056520 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1056521 {A : Type'} (f1 : type1600 A) (f2 : type1600 A) (x : nat) : (term13 A f1 f2 x) = (term18 A f1 f2 x).
Proof. exact (MK_COMB (@lem1056520) (@lem1056519 A f1 f2 x)). Qed.
Lemma lem1056526 {A : Type'} (f1 : type1600 A) (f2 : type1600 A) (x : nat) : ((f1 x) = (f2 x)) = (term18 A f1 f2 x).
Proof. exact (TRANS (@lem1056500 A f1 f2 x) (@lem1056521 A f1 f2 x)). Qed.
Lemma lem1056527 {A : Type'} (f1 : type1600 A) (f2 : type1600 A) : (term19 A f1 f2) = (term20 A f1 f2).
Proof. exact (fun_ext (fun x : nat => @lem1056526 A f1 f2 x)). Qed.
Lemma lem1056528 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1056529 {A : Type'} (f1 : type1600 A) (f2 : type1600 A) : (term11 A f1 f2) = (term21 A f1 f2).
Proof. exact (MK_COMB (@lem1056528) (@lem1056527 A f1 f2)). Qed.
Lemma lem1056534 {A : Type'} (f1 : type1600 A) (f2 : type1600 A) : (f1 = f2) = (term21 A f1 f2).
Proof. exact (TRANS (@lem1056490 A f1 f2) (@lem1056529 A f1 f2)). Qed.
Lemma lem1056535 {A : Type'} (f1 : type1600 A) (f2 : type1600 A) : (term21 A f1 f2) = (f1 = f2).
Proof. exact (SYM (@lem1056534 A f1 f2)). Qed.
Lemma lem1056539 {A : Type'} (f : type1600 A) : (@INJF A f) = (term5 A f).
Proof. exact (EQ_MP (@lem1056454 A f) (@lem1056453 A f)). Qed.
Lemma lem1056540 {A : Type'} (f : type1600 A) : (@INJF A f) = (term5 A f).
Proof. exact (@lem1056539 A f). Qed.
Lemma lem1056541 {A : Type'} (f1 : type1600 A) : (@INJF A f1) = (term5 A f1).
Proof. exact (@lem1056540 A f1). Qed.
Lemma lem1056542 {A : Type'} : (@eq (nat -> A -> Prop)) = (@eq (nat -> A -> Prop)).
Proof. exact (eq_refl (@eq (nat -> A -> Prop))). Qed.
Lemma lem1056543 {A : Type'} (f1 : type1600 A) : (term10 A f1) = (term22 A f1).
Proof. exact (MK_COMB (@lem1056542 A) (@lem1056541 A f1)). Qed.
Lemma lem1056545 {A : Type'} (f : type1600 A) : (@INJF A f) = (term5 A f).
Proof. exact (EQ_MP (@lem1056454 A f) (@lem1056453 A f)). Qed.
Lemma lem1056546 {A : Type'} (f : type1600 A) : (@INJF A f) = (term5 A f).
Proof. exact (@lem1056545 A f). Qed.
Lemma lem1056547 {A : Type'} (f2 : type1600 A) : (@INJF A f2) = (term5 A f2).
Proof. exact (@lem1056546 A f2). Qed.
Lemma lem1056548 {A : Type'} (f1 : type1600 A) (f2 : type1600 A) : ((@INJF A f1) = (@INJF A f2)) = ((term5 A f1) = (term5 A f2)).
Proof. exact (MK_COMB (@lem1056543 A f1) (@lem1056547 A f2)). Qed.
Lemma lem1056551 {A : Type'} (f1 : type1600 A) (f2 : type1600 A) (h1 : (@INJF A f1) = (@INJF A f2)) : (term5 A f1) = (term5 A f2).
Proof. exact (EQ_MP (@lem1056548 A f1 f2) (@lem1056462 A f1 f2 h1)). Qed.
Lemma lem1056552 {A : Type'} (f1 : type1600 A) (f2 : type1600 A) (h1 : (term5 A f1) = (term5 A f2)) : (term5 A f1) = (term5 A f2).
Proof. exact (h1). Qed.
Lemma lem1056553 (n : nat) (m : nat) : (NUMPAIR n m) = (NUMPAIR n m).
Proof. exact (eq_refl (NUMPAIR n m)). Qed.
Lemma lem1056554 {A : Type'} (n : nat) (m : nat) (f1 : type1600 A) (f2 : type1600 A) (h1 : (term5 A f1) = (term5 A f2)) : (term23 A f1 n m) = (term23 A f2 n m).
Proof. exact (MK_COMB (@lem1056552 A f1 f2 h1) (@lem1056553 n m)). Qed.
Lemma lem1056555 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1056556 {A : Type'} (n : nat) (m : nat) (a : A) (f1 : type1600 A) (f2 : type1600 A) (h1 : (term5 A f1) = (term5 A f2)) : (term24 A f1 n m a) = (term24 A f2 n m a).
Proof. exact (MK_COMB (@lem1056554 A n m f1 f2 h1) (@lem1056555 A a)). Qed.
Lemma lem1056564 {A B : Type'} (f : A -> B) (y : A) : (term25 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1056565 {A : Type'} (f : type1597 A) (y : nat) : (term26 A f y) = (f y).
Proof. exact (@lem1056564 nat (A -> Prop) f y). Qed.
Lemma lem1056566 {A : Type'} (f1 : type1600 A) (n : nat) (m : nat) : (term27 A f1 n m) = (term23 A f1 n m).
Proof. exact (@lem1056565 A (term5 A f1) (NUMPAIR n m)). Qed.
Lemma lem1056567 {A : Type'} (f1 : type1600 A) (n : nat) : (term28 A f1 n) = (term29 A f1 n).
Proof. exact (eq_refl (term28 A f1 n)). Qed.
Lemma lem1056568 {A : Type'} (f1 : type1600 A) : (term30 A f1) = (term5 A f1).
Proof. exact (fun_ext (fun n : nat => @lem1056567 A f1 n)). Qed.
Lemma lem1056569 (n : nat) (m : nat) : (NUMPAIR n m) = (NUMPAIR n m).
Proof. exact (eq_refl (NUMPAIR n m)). Qed.
Lemma lem1056570 {A : Type'} (f1 : type1600 A) (n : nat) (m : nat) : (term27 A f1 n m) = (term23 A f1 n m).
Proof. exact (MK_COMB (@lem1056568 A f1) (@lem1056569 n m)). Qed.
Lemma lem1056571 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem1056572 {A : Type'} (f1 : type1600 A) (n : nat) (m : nat) : (term31 A f1 n m) = (term32 A f1 n m).
Proof. exact (MK_COMB (@lem1056571 A) (@lem1056570 A f1 n m)). Qed.
Lemma lem1056573 {A : Type'} (f1 : type1600 A) (n : nat) (m : nat) : (term23 A f1 n m) = (term33 A f1 n m).
Proof. exact (eq_refl (term23 A f1 n m)). Qed.
Lemma lem1056574 {A : Type'} (f1 : type1600 A) (n : nat) (m : nat) : ((term27 A f1 n m) = (term23 A f1 n m)) = ((term23 A f1 n m) = (term33 A f1 n m)).
Proof. exact (MK_COMB (@lem1056572 A f1 n m) (@lem1056573 A f1 n m)). Qed.
Lemma lem1056575 {A : Type'} (f1 : type1600 A) (n : nat) (m : nat) : (term23 A f1 n m) = (term33 A f1 n m).
Proof. exact (EQ_MP (@lem1056574 A f1 n m) (@lem1056566 A f1 n m)). Qed.
Lemma lem1056577 (y : nat) (x : nat) : (term34 x y) = x.
Proof. exact (proj1 (@lem1056450 x y)). Qed.
Lemma lem1056578 (m : nat) (n : nat) : (term34 n m) = n.
Proof. exact (@lem1056577 m n). Qed.
Lemma lem1056579 {A : Type'} (f1 : type1600 A) : f1 = f1.
Proof. exact (eq_refl f1). Qed.
Lemma lem1056580 {A : Type'} (m : nat) (f1 : type1600 A) (n : nat) : (term35 A f1 n m) = (f1 n).
Proof. exact (MK_COMB (@lem1056579 A f1) (@lem1056578 m n)). Qed.
Lemma lem1056582 (x : nat) (y : nat) : (term36 x y) = y.
Proof. exact (proj2 (@lem1056450 x y)). Qed.
Lemma lem1056583 (n : nat) (m : nat) : (term36 n m) = m.
Proof. exact (@lem1056582 n m). Qed.
Lemma lem1056584 {A : Type'} (f1 : type1600 A) (n : nat) (m : nat) : (term33 A f1 n m) = (f1 n m).
Proof. exact (MK_COMB (@lem1056580 A m f1 n) (@lem1056583 n m)). Qed.
Lemma lem1056585 {A : Type'} (f1 : type1600 A) (n : nat) (m : nat) : (term23 A f1 n m) = (f1 n m).
Proof. exact (TRANS (@lem1056575 A f1 n m) (@lem1056584 A f1 n m)). Qed.
Lemma lem1056586 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1056587 {A : Type'} (f1 : type1600 A) (n : nat) (m : nat) (a : A) : (term24 A f1 n m a) = (f1 n m a).
Proof. exact (MK_COMB (@lem1056585 A f1 n m) (@lem1056586 A a)). Qed.
Lemma lem1056588 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1056589 {A : Type'} (f1 : type1600 A) (n : nat) (m : nat) (a : A) : (term37 A f1 n m a) = (term38 A f1 n m a).
Proof. exact (MK_COMB (@lem1056588) (@lem1056587 A f1 n m a)). Qed.
Lemma lem1056591 {A B : Type'} (f : A -> B) (y : A) : (term25 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1056592 {A : Type'} (f : type1597 A) (y : nat) : (term26 A f y) = (f y).
Proof. exact (@lem1056591 nat (A -> Prop) f y). Qed.
Lemma lem1056593 {A : Type'} (f2 : type1600 A) (n : nat) (m : nat) : (term27 A f2 n m) = (term23 A f2 n m).
Proof. exact (@lem1056592 A (term5 A f2) (NUMPAIR n m)). Qed.
Lemma lem1056594 {A : Type'} (f2 : type1600 A) (n : nat) : (term28 A f2 n) = (term29 A f2 n).
Proof. exact (eq_refl (term28 A f2 n)). Qed.
Lemma lem1056595 {A : Type'} (f2 : type1600 A) : (term30 A f2) = (term5 A f2).
Proof. exact (fun_ext (fun n : nat => @lem1056594 A f2 n)). Qed.
Lemma lem1056596 (n : nat) (m : nat) : (NUMPAIR n m) = (NUMPAIR n m).
Proof. exact (eq_refl (NUMPAIR n m)). Qed.
Lemma lem1056597 {A : Type'} (f2 : type1600 A) (n : nat) (m : nat) : (term27 A f2 n m) = (term23 A f2 n m).
Proof. exact (MK_COMB (@lem1056595 A f2) (@lem1056596 n m)). Qed.
Lemma lem1056598 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem1056599 {A : Type'} (f2 : type1600 A) (n : nat) (m : nat) : (term31 A f2 n m) = (term32 A f2 n m).
Proof. exact (MK_COMB (@lem1056598 A) (@lem1056597 A f2 n m)). Qed.
Lemma lem1056600 {A : Type'} (f2 : type1600 A) (n : nat) (m : nat) : (term23 A f2 n m) = (term33 A f2 n m).
Proof. exact (eq_refl (term23 A f2 n m)). Qed.
Lemma lem1056601 {A : Type'} (f2 : type1600 A) (n : nat) (m : nat) : ((term27 A f2 n m) = (term23 A f2 n m)) = ((term23 A f2 n m) = (term33 A f2 n m)).
Proof. exact (MK_COMB (@lem1056599 A f2 n m) (@lem1056600 A f2 n m)). Qed.
Lemma lem1056602 {A : Type'} (f2 : type1600 A) (n : nat) (m : nat) : (term23 A f2 n m) = (term33 A f2 n m).
Proof. exact (EQ_MP (@lem1056601 A f2 n m) (@lem1056593 A f2 n m)). Qed.
Lemma lem1056604 (y : nat) (x : nat) : (term34 x y) = x.
Proof. exact (proj1 (@lem1056450 x y)). Qed.
Lemma lem1056605 (m : nat) (n : nat) : (term34 n m) = n.
Proof. exact (@lem1056604 m n). Qed.
Lemma lem1056606 {A : Type'} (f2 : type1600 A) : f2 = f2.
Proof. exact (eq_refl f2). Qed.
Lemma lem1056607 {A : Type'} (m : nat) (f2 : type1600 A) (n : nat) : (term35 A f2 n m) = (f2 n).
Proof. exact (MK_COMB (@lem1056606 A f2) (@lem1056605 m n)). Qed.
Lemma lem1056609 (x : nat) (y : nat) : (term36 x y) = y.
Proof. exact (proj2 (@lem1056450 x y)). Qed.
Lemma lem1056610 (n : nat) (m : nat) : (term36 n m) = m.
Proof. exact (@lem1056609 n m). Qed.
Lemma lem1056611 {A : Type'} (f2 : type1600 A) (n : nat) (m : nat) : (term33 A f2 n m) = (f2 n m).
Proof. exact (MK_COMB (@lem1056607 A m f2 n) (@lem1056610 n m)). Qed.
Lemma lem1056612 {A : Type'} (f2 : type1600 A) (n : nat) (m : nat) : (term23 A f2 n m) = (f2 n m).
Proof. exact (TRANS (@lem1056602 A f2 n m) (@lem1056611 A f2 n m)). Qed.
Lemma lem1056613 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1056614 {A : Type'} (f2 : type1600 A) (n : nat) (m : nat) (a : A) : (term24 A f2 n m a) = (f2 n m a).
Proof. exact (MK_COMB (@lem1056612 A f2 n m) (@lem1056613 A a)). Qed.
Lemma lem1056615 {A : Type'} (f1 : type1600 A) (f2 : type1600 A) (n : nat) (m : nat) (a : A) : ((term24 A f1 n m a) = (term24 A f2 n m a)) = ((f1 n m a) = (f2 n m a)).
Proof. exact (MK_COMB (@lem1056589 A f1 n m a) (@lem1056614 A f2 n m a)). Qed.
Lemma lem1056618 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1056619 {A : Type'} (f1 : type1600 A) (f2 : type1600 A) (n : nat) (m : nat) (a : A) : (term39 A f1 f2 n m a) = (term40 A f1 f2 n m a).
Proof. exact (MK_COMB (@lem1056618) (@lem1056615 A f1 f2 n m a)). Qed.
Lemma lem1056622 {A : Type'} (f1 : type1600 A) (f2 : type1600 A) (n : nat) (m : nat) (a : A) : ((f1 n m a) = (f2 n m a)) = ((f1 n m a) = (f2 n m a)).
Proof. exact (eq_refl ((f1 n m a) = (f2 n m a))). Qed.
Lemma lem1056623 {A : Type'} (f1 : type1600 A) (f2 : type1600 A) (n : nat) (m : nat) (a : A) : (term41 A f1 f2 n m a) = (term42 A f1 f2 n m a).
Proof. exact (MK_COMB (@lem1056619 A f1 f2 n m a) (@lem1056622 A f1 f2 n m a)). Qed.
Lemma lem1056627 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem1056628 {A : Type'} (f1 : type1600 A) (f2 : type1600 A) (n : nat) (m : nat) (a : A) : (term42 A f1 f2 n m a) = True.
Proof. exact (@lem1056627 ((f1 n m a) = (f2 n m a))). Qed.
Lemma lem1056629 {A : Type'} (f1 : type1600 A) (f2 : type1600 A) (n : nat) (m : nat) (a : A) : (term41 A f1 f2 n m a) = True.
Proof. exact (TRANS (@lem1056623 A f1 f2 n m a) (@lem1056628 A f1 f2 n m a)). Qed.
Lemma lem1056630 {A : Type'} (f1 : type1600 A) (f2 : type1600 A) (n : nat) (m : nat) (a : A) : True = (term41 A f1 f2 n m a).
Proof. exact (SYM (@lem1056629 A f1 f2 n m a)). Qed.
Lemma lem1056631 {A : Type'} (f1 : type1600 A) (f2 : type1600 A) (n : nat) (m : nat) (a : A) : term41 A f1 f2 n m a.
Proof. exact (EQ_MP (@lem1056630 A f1 f2 n m a) (@lem0)). Qed.
Lemma lem1056632 {A : Type'} (n : nat) (m : nat) (a : A) (f1 : type1600 A) (f2 : type1600 A) (h1 : (term5 A f1) = (term5 A f2)) : (f1 n m a) = (f2 n m a).
Proof. exact (@lem1056631 A f1 f2 n m a (@lem1056556 A n m a f1 f2 h1)). Qed.
Lemma lem1056633 {A : Type'} (f1 : type1600 A) (f2 : type1600 A) (n : nat) (m : nat) (a : A) : term43 A f1 f2 n m a.
Proof. exact (fun h0 : (term5 A f1) = (term5 A f2) => @lem1056632 A n m a f1 f2 h0). Qed.
Lemma lem1056634 {A : Type'} (n : nat) (m : nat) (a : A) (f1 : type1600 A) (f2 : type1600 A) (h1 : (@INJF A f1) = (@INJF A f2)) : (f1 n m a) = (f2 n m a).
Proof. exact (@lem1056633 A f1 f2 n m a (@lem1056551 A f1 f2 h1)). Qed.
Lemma lem1056639 {A : Type'} (n : nat) (m : nat) (f1 : type1600 A) (f2 : type1600 A) (h1 : (@INJF A f1) = (@INJF A f2)) : term15 A f1 f2 n m.
Proof. exact (fun a : A => @lem1056634 A n m a f1 f2 h1). Qed.
Lemma lem1056644 {A : Type'} (n : nat) (f1 : type1600 A) (f2 : type1600 A) (h1 : (@INJF A f1) = (@INJF A f2)) : term18 A f1 f2 n.
Proof. exact (fun m : nat => @lem1056639 A n m f1 f2 h1). Qed.
Lemma lem1056649 {A : Type'} (f1 : type1600 A) (f2 : type1600 A) (h1 : (@INJF A f1) = (@INJF A f2)) : term21 A f1 f2.
Proof. exact (fun n : nat => @lem1056644 A n f1 f2 h1). Qed.
Lemma lem1056651 {A : Type'} (f1 : type1600 A) (f2 : type1600 A) (h1 : (@INJF A f1) = (@INJF A f2)) : f1 = f2.
Proof. exact (EQ_MP (@lem1056535 A f1 f2) (@lem1056649 A f1 f2 h1)). Qed.
Lemma lem1056652 {A : Type'} (f1 : type1600 A) (f2 : type1600 A) : term44 A f1 f2.
Proof. exact (fun h0 : f1 = f2 => @lem1056484 A f1 f2 h0). Qed.
Lemma lem1056653 {A : Type'} (f1 : type1600 A) (f2 : type1600 A) : term45 A f1 f2.
Proof. exact (fun h0 : (@INJF A f1) = (@INJF A f2) => @lem1056651 A f1 f2 h0). Qed.
Lemma lem1056654 {A : Type'} (f1 : type1600 A) (f2 : type1600 A) : term46 A f1 f2.
Proof. exact (conj (@lem1056653 A f1 f2) (@lem1056652 A f1 f2)). Qed.
Lemma lem1056655 {A : Type'} (f1 : type1600 A) (f2 : type1600 A) : (term46 A f1 f2) = (((@INJF A f1) = (@INJF A f2)) = (f1 = f2)).
Proof. exact (@lem32 ((@INJF A f1) = (@INJF A f2)) (f1 = f2)). Qed.
Lemma lem1056656 {A : Type'} (f1 : type1600 A) (f2 : type1600 A) : ((@INJF A f1) = (@INJF A f2)) = (f1 = f2).
Proof. exact (EQ_MP (@lem1056655 A f1 f2) (@lem1056654 A f1 f2)). Qed.
Lemma lem1056661 {A : Type'} (f1 : type1600 A) : term47 A f1.
Proof. exact (fun f2 : type1600 A => @lem1056656 A f1 f2). Qed.
Lemma lem1056666 {A : Type'} : term48 A.
Proof. exact (fun f1 : type1600 A => @lem1056661 A f1). Qed.
