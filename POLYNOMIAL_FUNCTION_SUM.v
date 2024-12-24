Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import POLYNOMIAL_FUNCTION_SUM_term_abbrevs.
Require Import FINITE_INDUCT_STRONG_spec.
Require Import FORALL_IN_INSERT_spec.
Require Import POLYNOMIAL_FUNCTION_ADD_spec.
Require Import POLYNOMIAL_FUNCTION_CONST_spec.
Require Import RIGHT_FORALL_IMP_THM_spec.
Require Import SUM_CLAUSES_spec.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Require Import thm885_spec.
Require Import thm886_spec.
Lemma lem7577428 (p : real -> real) : term0 p.
Proof. exact (@lem7567170 p). Qed.
Lemma lem7577429 (p : real -> real) : (term0 p) = (term1 p).
Proof. exact (eq_refl (term0 p)). Qed.
Lemma lem7577430 (p : real -> real) : term1 p.
Proof. exact (EQ_MP (@lem7577429 p) (@lem7577428 p)). Qed.
Lemma lem7577431 (p : real -> real) (q : real -> real) : term2 p q.
Proof. exact (@lem7577430 p q). Qed.
Lemma lem7577432 (p : real -> real) (q : real -> real) : (term2 p q) = (term3 p q).
Proof. exact (eq_refl (term2 p q)). Qed.
Lemma lem7577433 (p : real -> real) (q : real -> real) : term3 p q.
Proof. exact (EQ_MP (@lem7577432 p q) (@lem7577431 p q)). Qed.
Lemma lem7577434 (p : real -> real) (q : real -> real) (h1 : term4 p q) : term4 p q.
Proof. exact (h1). Qed.
Lemma lem7577435 (p : real -> real) (q : real -> real) (h1 : term4 p q) : term5 p q.
Proof. exact (@lem7577433 p q (@lem7577434 p q h1)). Qed.
Lemma lem7577436 (p : real -> real) (q : real -> real) : (term5 p q) = ((term5 p q) = True).
Proof. exact (@lem7 (term5 p q)). Qed.
Lemma lem7577437 (p : real -> real) (q : real -> real) (h1 : term4 p q) : (term5 p q) = True.
Proof. exact (EQ_MP (@lem7577436 p q) (@lem7577435 p q h1)). Qed.
Lemma lem7577443 {_83983 : Type'} (P : _83983 -> Prop) : term6 _83983 P.
Proof. exact (@lem3207453 _83983 P). Qed.
Lemma lem7577444 {_83983 : Type'} (P : _83983 -> Prop) : (term6 _83983 P) = (term7 _83983 P).
Proof. exact (eq_refl (term6 _83983 P)). Qed.
Lemma lem7577445 {_83983 : Type'} (P : _83983 -> Prop) : term7 _83983 P.
Proof. exact (EQ_MP (@lem7577444 _83983 P) (@lem7577443 _83983 P)). Qed.
Lemma lem7577446 {_83983 : Type'} (P : _83983 -> Prop) (a : _83983) : term8 _83983 P a.
Proof. exact (@lem7577445 _83983 P a). Qed.
Lemma lem7577447 {_83983 : Type'} (a : _83983) (P : _83983 -> Prop) : (term8 _83983 P a) = (term9 _83983 a P).
Proof. exact (eq_refl (term8 _83983 P a)). Qed.
Lemma lem7577448 {_83983 : Type'} (a : _83983) (P : _83983 -> Prop) : term9 _83983 a P.
Proof. exact (EQ_MP (@lem7577447 _83983 a P) (@lem7577446 _83983 P a)). Qed.
Lemma lem7577449 {_83983 : Type'} (a : _83983) (P : _83983 -> Prop) (s : _83983 -> Prop) : term10 _83983 a P s.
Proof. exact (@lem7577448 _83983 a P s). Qed.
Lemma lem7577450 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term10 _83983 a P s) = ((term11 _83983 a s P) = (term12 _83983 a s P)).
Proof. exact (eq_refl (term10 _83983 a P s)). Qed.
Lemma lem7577452 (c : real) : term13 c.
Proof. exact (@lem7553635 c). Qed.
Lemma lem7577453 (c : real) : (term13 c) = (term14 c).
Proof. exact (eq_refl (term13 c)). Qed.
Lemma lem7577454 (c : real) : term14 c.
Proof. exact (EQ_MP (@lem7577453 c) (@lem7577452 c)). Qed.
Lemma lem7577455 (c : real) : (term14 c) = ((term14 c) = True).
Proof. exact (@lem7 (term14 c)). Qed.
Lemma lem7577457 {_131524 : Type'} : term15 _131524.
Proof. exact (proj2 (@lem7067645 Prop _131524)). Qed.
Lemma lem7577458 {_131524 : Type'} (x : _131524) : term16 _131524 x.
Proof. exact (@lem7577457 _131524 x). Qed.
Lemma lem7577459 {_131524 : Type'} (x : _131524) : (term16 _131524 x) = (term17 _131524 x).
Proof. exact (eq_refl (term16 _131524 x)). Qed.
Lemma lem7577460 {_131524 : Type'} (x : _131524) : term17 _131524 x.
Proof. exact (EQ_MP (@lem7577459 _131524 x) (@lem7577458 _131524 x)). Qed.
Lemma lem7577461 {_131524 : Type'} (x : _131524) (f : _131524 -> real) : term18 _131524 x f.
Proof. exact (@lem7577460 _131524 x f). Qed.
Lemma lem7577462 {_131524 : Type'} (x : _131524) (f : _131524 -> real) : (term18 _131524 x f) = (term19 _131524 x f).
Proof. exact (eq_refl (term18 _131524 x f)). Qed.
Lemma lem7577463 {_131524 : Type'} (x : _131524) (f : _131524 -> real) : term19 _131524 x f.
Proof. exact (EQ_MP (@lem7577462 _131524 x f) (@lem7577461 _131524 x f)). Qed.
Lemma lem7577464 {_131524 : Type'} (x : _131524) (f : _131524 -> real) (s : _131524 -> Prop) : term20 _131524 x f s.
Proof. exact (@lem7577463 _131524 x f s). Qed.
Lemma lem7577465 {_131524 : Type'} (x : _131524) (s : _131524 -> Prop) (f : _131524 -> real) : (term20 _131524 x f s) = (term21 _131524 x s f).
Proof. exact (eq_refl (term20 _131524 x f s)). Qed.
Lemma lem7577466 {_131524 : Type'} (x : _131524) (s : _131524 -> Prop) (f : _131524 -> real) : term21 _131524 x s f.
Proof. exact (EQ_MP (@lem7577465 _131524 x s f) (@lem7577464 _131524 x f s)). Qed.
Lemma lem7577467 {_131524 : Type'} (s : _131524 -> Prop) (h1 : @FINITE _131524 s) : @FINITE _131524 s.
Proof. exact (h1). Qed.
Lemma lem7577468 {_131524 : Type'} (x : _131524) (f : _131524 -> real) (s : _131524 -> Prop) (h1 : @FINITE _131524 s) : (term22 _131524 x s f) = (term23 _131524 x s f).
Proof. exact (@lem7577466 _131524 x s f (@lem7577467 _131524 s h1)). Qed.
Lemma lem7577474 {_131483 : Type'} : term24 _131483.
Proof. exact (proj1 (@lem7067645 _131483 Prop)). Qed.
Lemma lem7577475 {_131483 : Type'} (f : _131483 -> real) : term25 _131483 f.
Proof. exact (@lem7577474 _131483 f). Qed.
Lemma lem7577476 {_131483 : Type'} (f : _131483 -> real) : (term25 _131483 f) = ((@sum _131483 (@EMPTY _131483) f) = term26).
Proof. exact (eq_refl (term25 _131483 f)). Qed.
Lemma lem7577478 {A : Type'} (h1 : term27 A) : term27 A.
Proof. exact (h1). Qed.
Lemma lem7577479 {A : Type'} (P : type686 A) (h1 : term27 A) : term28 A P.
Proof. exact (@lem7577478 A h1 P). Qed.
Lemma lem7577480 {A : Type'} (P : type686 A) : (term28 A P) = (term29 A P).
Proof. exact (eq_refl (term28 A P)). Qed.
Lemma lem7577481 {A : Type'} (P : type686 A) (h1 : term27 A) : term29 A P.
Proof. exact (EQ_MP (@lem7577480 A P) (@lem7577479 A P h1)). Qed.
Lemma lem7577482 {A : Type'} (P : type686 A) (h1 : term30 A P) : term30 A P.
Proof. exact (h1). Qed.
Lemma lem7577483 {A : Type'} (P : type686 A) (h1 : term27 A) (h2 : term30 A P) : term31 A P.
Proof. exact (@lem7577481 A P h1 (@lem7577482 A P h2)). Qed.
Lemma lem7577484 {A : Type'} (P : type686 A) (h1 : term30 A P) : term32 A P.
Proof. exact (fun h0 : term27 A => @lem7577483 A P h0 h1). Qed.
Lemma lem7577485 {A : Type'} (h1 : term27 A) : term27 A.
Proof. exact (h1). Qed.
Lemma lem7577486 {A : Type'} (P : type686 A) (h1 : term27 A) (h2 : term30 A P) : term31 A P.
Proof. exact (@lem7577484 A P h2 (@lem7577485 A h1)). Qed.
Lemma lem7577487 {A : Type'} (P : type686 A) (h1 : term27 A) : term29 A P.
Proof. exact (fun h0 : term30 A P => @lem7577486 A P h1 h0). Qed.
Lemma lem7577488 {A : Type'} (h1 : term27 A) : term27 A.
Proof. exact (fun P : type686 A => @lem7577487 A P h1). Qed.
Lemma lem7577489 {A : Type'} : term33 A.
Proof. exact (fun h0 : term27 A => @lem7577488 A h0). Qed.
Lemma lem7577490 {A : Type'} : term27 A.
Proof. exact (@lem7577489 A (@lem3558722 A)). Qed.
Lemma lem7577491 {A : Type'} (P : type686 A) : term28 A P.
Proof. exact (@lem7577490 A P). Qed.
Lemma lem7577492 {A : Type'} (P : type686 A) : (term28 A P) = (term29 A P).
Proof. exact (eq_refl (term28 A P)). Qed.
Lemma lem7577494 {A : Type'} (P : Prop) : term34 A P.
Proof. exact (@lem6534 A P). Qed.
Lemma lem7577495 {A : Type'} (P : Prop) : (term34 A P) = (term35 A P).
Proof. exact (eq_refl (term34 A P)). Qed.
Lemma lem7577496 {A : Type'} (P : Prop) : term35 A P.
Proof. exact (EQ_MP (@lem7577495 A P) (@lem7577494 A P)). Qed.
Lemma lem7577497 {A : Type'} (P : Prop) (Q : A -> Prop) : term36 A P Q.
Proof. exact (@lem7577496 A P Q). Qed.
Lemma lem7577498 {A : Type'} (P : Prop) (Q : A -> Prop) : (term36 A P Q) = ((term37 A P Q) = (term38 A P Q)).
Proof. exact (eq_refl (term36 A P Q)). Qed.
Lemma lem7577529 (p : Prop) (q : Prop) (r : Prop) : (term39 p q r) = (term40 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem7577530 {A : Type'} (s : A -> Prop) (p : type1621 A) : (term41 A s p) = (term42 A s p).
Proof. exact (@lem7577529 (@FINITE A s) (term43 A s p) (term44 A s p)). Qed.
Lemma lem7577561 {A : Type'} (s : A -> Prop) : (term45 A s) = (term46 A s).
Proof. exact (fun_ext (fun p : type1621 A => @lem7577530 A s p)). Qed.
Lemma lem7577562 {A : Type'} : (@all (real -> A -> real)) = (@all (real -> A -> real)).
Proof. exact (eq_refl (@all (real -> A -> real))). Qed.
Lemma lem7577563 {A : Type'} (s : A -> Prop) : (term47 A s) = (term48 A s).
Proof. exact (MK_COMB (@lem7577562 A) (@lem7577561 A s)). Qed.
Lemma lem7577565 {A : Type'} (P : Prop) (Q : A -> Prop) : (term37 A P Q) = (term38 A P Q).
Proof. exact (EQ_MP (@lem7577498 A P Q) (@lem7577497 A P Q)). Qed.
Lemma lem7577566 {A : Type'} (P : Prop) (Q : type1012 A) : (term49 A P Q) = (term50 A P Q).
Proof. exact (@lem7577565 (type1621 A) P Q). Qed.
Lemma lem7577567 {A : Type'} (s : A -> Prop) : (term51 A s) = (term52 A s).
Proof. exact (@lem7577566 A (@FINITE A s) (term53 A s)). Qed.
Lemma lem7577568 {A : Type'} (s : A -> Prop) (p : type1621 A) : (term54 A s p) = (term55 A s p).
Proof. exact (eq_refl (term54 A s p)). Qed.
Lemma lem7577569 {A : Type'} (s : A -> Prop) : (term56 A s) = (term56 A s).
Proof. exact (eq_refl (term56 A s)). Qed.
Lemma lem7577570 {A : Type'} (s : A -> Prop) (p : type1621 A) : (term57 A s p) = (term42 A s p).
Proof. exact (MK_COMB (@lem7577569 A s) (@lem7577568 A s p)). Qed.
Lemma lem7577571 {A : Type'} (s : A -> Prop) : (term58 A s) = (term46 A s).
Proof. exact (fun_ext (fun p : type1621 A => @lem7577570 A s p)). Qed.
Lemma lem7577572 {A : Type'} : (@all (real -> A -> real)) = (@all (real -> A -> real)).
Proof. exact (eq_refl (@all (real -> A -> real))). Qed.
Lemma lem7577573 {A : Type'} (s : A -> Prop) : (term51 A s) = (term48 A s).
Proof. exact (MK_COMB (@lem7577572 A) (@lem7577571 A s)). Qed.
Lemma lem7577574 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7577575 {A : Type'} (s : A -> Prop) : (term59 A s) = (term60 A s).
Proof. exact (MK_COMB (@lem7577574) (@lem7577573 A s)). Qed.
Lemma lem7577576 {A : Type'} (s : A -> Prop) (p : type1621 A) : (term54 A s p) = (term55 A s p).
Proof. exact (eq_refl (term54 A s p)). Qed.
Lemma lem7577577 {A : Type'} (s : A -> Prop) : (term61 A s) = (term53 A s).
Proof. exact (fun_ext (fun p : type1621 A => @lem7577576 A s p)). Qed.
Lemma lem7577578 {A : Type'} : (@all (real -> A -> real)) = (@all (real -> A -> real)).
Proof. exact (eq_refl (@all (real -> A -> real))). Qed.
Lemma lem7577579 {A : Type'} (s : A -> Prop) : (term62 A s) = (term63 A s).
Proof. exact (MK_COMB (@lem7577578 A) (@lem7577577 A s)). Qed.
Lemma lem7577580 {A : Type'} (s : A -> Prop) : (term56 A s) = (term56 A s).
Proof. exact (eq_refl (term56 A s)). Qed.
Lemma lem7577581 {A : Type'} (s : A -> Prop) : (term52 A s) = (term64 A s).
Proof. exact (MK_COMB (@lem7577580 A s) (@lem7577579 A s)). Qed.
Lemma lem7577582 {A : Type'} (s : A -> Prop) : ((term51 A s) = (term52 A s)) = ((term48 A s) = (term64 A s)).
Proof. exact (MK_COMB (@lem7577575 A s) (@lem7577581 A s)). Qed.
Lemma lem7577583 {A : Type'} (s : A -> Prop) : (term48 A s) = (term64 A s).
Proof. exact (EQ_MP (@lem7577582 A s) (@lem7577567 A s)). Qed.
Lemma lem7577638 {A : Type'} (s : A -> Prop) : (term47 A s) = (term64 A s).
Proof. exact (TRANS (@lem7577563 A s) (@lem7577583 A s)). Qed.
Lemma lem7577639 {A : Type'} : (term65 A) = (term66 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7577638 A s)). Qed.
Lemma lem7577640 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7577641 {A : Type'} : (term67 A) = (term68 A).
Proof. exact (MK_COMB (@lem7577640 A) (@lem7577639 A)). Qed.
Lemma lem7577666 {A : Type'} : (term68 A) = (term67 A).
Proof. exact (SYM (@lem7577641 A)). Qed.
Lemma lem7577668 {A : Type'} (P : type686 A) : term29 A P.
Proof. exact (EQ_MP (@lem7577492 A P) (@lem7577491 A P)). Qed.
Lemma lem7577669 {A : Type'} (P : type686 A) : term29 A P.
Proof. exact (@lem7577668 A P). Qed.
Lemma lem7577670 {A : Type'} : term69 A.
Proof. exact (@lem7577669 A (term70 A)). Qed.
Lemma lem7577671 {A : Type'} : (term71 A) = (term72 A).
Proof. exact (eq_refl (term71 A)). Qed.
Lemma lem7577672 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7577673 {A : Type'} : (term73 A) = (term74 A).
Proof. exact (MK_COMB (@lem7577672) (@lem7577671 A)). Qed.
Lemma lem7577674 {A : Type'} (s : A -> Prop) : (term75 A s) = (term63 A s).
Proof. exact (eq_refl (term75 A s)). Qed.
Lemma lem7577675 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7577676 {A : Type'} (s : A -> Prop) : (term76 A s) = (term77 A s).
Proof. exact (MK_COMB (@lem7577675) (@lem7577674 A s)). Qed.
Lemma lem7577677 {A : Type'} (x : A) (s : A -> Prop) : (term78 A x s) = (term78 A x s).
Proof. exact (eq_refl (term78 A x s)). Qed.
Lemma lem7577678 {A : Type'} (x : A) (s : A -> Prop) : (term79 A x s) = (term80 A x s).
Proof. exact (MK_COMB (@lem7577676 A s) (@lem7577677 A x s)). Qed.
Lemma lem7577679 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7577680 {A : Type'} (x : A) (s : A -> Prop) : (term81 A x s) = (term82 A x s).
Proof. exact (MK_COMB (@lem7577679) (@lem7577678 A x s)). Qed.
Lemma lem7577681 {A : Type'} (x : A) (s : A -> Prop) : (term83 A x s) = (term84 A x s).
Proof. exact (eq_refl (term83 A x s)). Qed.
Lemma lem7577682 {A : Type'} (x : A) (s : A -> Prop) : (term85 A x s) = (term86 A x s).
Proof. exact (MK_COMB (@lem7577680 A x s) (@lem7577681 A x s)). Qed.
Lemma lem7577683 {A : Type'} (x : A) : (term87 A x) = (term88 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7577682 A x s)). Qed.
Lemma lem7577684 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7577685 {A : Type'} (x : A) : (term89 A x) = (term90 A x).
Proof. exact (MK_COMB (@lem7577684 A) (@lem7577683 A x)). Qed.
Lemma lem7577686 {A : Type'} : (term91 A) = (term92 A).
Proof. exact (fun_ext (fun x : A => @lem7577685 A x)). Qed.
Lemma lem7577687 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7577688 {A : Type'} : (term93 A) = (term94 A).
Proof. exact (MK_COMB (@lem7577687 A) (@lem7577686 A)). Qed.
Lemma lem7577689 {A : Type'} : (term95 A) = (term96 A).
Proof. exact (MK_COMB (@lem7577673 A) (@lem7577688 A)). Qed.
Lemma lem7577690 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7577691 {A : Type'} : (term97 A) = (term98 A).
Proof. exact (MK_COMB (@lem7577690) (@lem7577689 A)). Qed.
Lemma lem7577692 {A : Type'} (s : A -> Prop) : (term75 A s) = (term63 A s).
Proof. exact (eq_refl (term75 A s)). Qed.
Lemma lem7577693 {A : Type'} (s : A -> Prop) : (term56 A s) = (term56 A s).
Proof. exact (eq_refl (term56 A s)). Qed.
Lemma lem7577694 {A : Type'} (s : A -> Prop) : (term99 A s) = (term64 A s).
Proof. exact (MK_COMB (@lem7577693 A s) (@lem7577692 A s)). Qed.
Lemma lem7577695 {A : Type'} : (term100 A) = (term66 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7577694 A s)). Qed.
Lemma lem7577696 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7577697 {A : Type'} : (term101 A) = (term68 A).
Proof. exact (MK_COMB (@lem7577696 A) (@lem7577695 A)). Qed.
Lemma lem7577698 {A : Type'} : (term69 A) = (term102 A).
Proof. exact (MK_COMB (@lem7577691 A) (@lem7577697 A)). Qed.
Lemma lem7577699 {A : Type'} : term102 A.
Proof. exact (EQ_MP (@lem7577698 A) (@lem7577670 A)). Qed.
Lemma lem7577709 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term103 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7577710 (p : Prop) (q : Prop) (p' : Prop) : term104 p q p'.
Proof. exact (fun q' : Prop => @lem7577709 p q p' q'). Qed.
Lemma lem7577711 (p : Prop) (q : Prop) : term105 p q.
Proof. exact (fun p' : Prop => @lem7577710 p q p'). Qed.
Lemma lem7577712 {A : Type'} (p : type1621 A) : term106 A p.
Proof. exact (@lem7577711 (term107 A p) (term108 A p)). Qed.
Lemma lem7577713 {A : Type'} (p : type1621 A) (p' : Prop) : term109 A p p'.
Proof. exact (@lem7577712 A p p'). Qed.
Lemma lem7577714 {A : Type'} (p : type1621 A) (p' : Prop) : (term109 A p p') = (term110 A p p').
Proof. exact (eq_refl (term109 A p p')). Qed.
Lemma lem7577715 {A : Type'} (p : type1621 A) (p' : Prop) : term110 A p p'.
Proof. exact (EQ_MP (@lem7577714 A p p') (@lem7577713 A p p')). Qed.
Lemma lem7577716 {A : Type'} (p : type1621 A) (p' : Prop) (q' : Prop) : term111 A p p' q'.
Proof. exact (@lem7577715 A p p' q'). Qed.
Lemma lem7577717 {A : Type'} (p : type1621 A) (p' : Prop) (q' : Prop) : (term111 A p p' q') = (term112 A p p' q').
Proof. exact (eq_refl (term111 A p p' q')). Qed.
Lemma lem7577718 {A : Type'} (p : type1621 A) (p' : Prop) (q' : Prop) : term112 A p p' q'.
Proof. exact (EQ_MP (@lem7577717 A p p' q') (@lem7577716 A p p' q')). Qed.
Lemma lem7577752 {A : Type'} (p : type1621 A) : (term107 A p) = (term107 A p).
Proof. exact (eq_refl (term107 A p)). Qed.
Lemma lem7577753 {A : Type'} (p : type1621 A) (q' : Prop) : term113 A p q'.
Proof. exact (@lem7577718 A p (term107 A p) q'). Qed.
Lemma lem7577754 {A : Type'} (p : type1621 A) (q' : Prop) : term114 A p q'.
Proof. exact (@lem7577753 A p q' (@lem7577752 A p)). Qed.
Lemma lem7577772 {_131483 : Type'} (f : _131483 -> real) : (@sum _131483 (@EMPTY _131483) f) = term26.
Proof. exact (EQ_MP (@lem7577476 _131483 f) (@lem7577475 _131483 f)). Qed.
Lemma lem7577773 {A : Type'} (f : A -> real) : (@sum A (@EMPTY A) f) = term26.
Proof. exact (@lem7577772 A f). Qed.
Lemma lem7577774 {A : Type'} (p : type1621 A) (x : real) : (term115 A p x) = term26.
Proof. exact (@lem7577773 A (p x)). Qed.
Lemma lem7577775 {A : Type'} (p : type1621 A) : (term116 A p) = term117.
Proof. exact (fun_ext (fun x : real => @lem7577774 A p x)). Qed.
Lemma lem7577776 : polynomial_function = polynomial_function.
Proof. exact (eq_refl polynomial_function). Qed.
Lemma lem7577777 {A : Type'} (p : type1621 A) : (term108 A p) = term118.
Proof. exact (MK_COMB (@lem7577776) (@lem7577775 A p)). Qed.
Lemma lem7577779 (c : real) : (term14 c) = True.
Proof. exact (EQ_MP (@lem7577455 c) (@lem7577454 c)). Qed.
Lemma lem7577780 : term118 = True.
Proof. exact (@lem7577779 term26). Qed.
Lemma lem7577781 {A : Type'} (p : type1621 A) : (term108 A p) = True.
Proof. exact (TRANS (@lem7577777 A p) (@lem7577780)). Qed.
Lemma lem7577782 {A : Type'} (p : type1621 A) : term119 A p.
Proof. exact (fun h0 : term107 A p => @lem7577781 A p). Qed.
Lemma lem7577783 {A : Type'} (p : type1621 A) : term120 A p.
Proof. exact (@lem7577754 A p True). Qed.
Lemma lem7577784 {A : Type'} (p : type1621 A) : (term121 A p) = (term122 A p).
Proof. exact (@lem7577783 A p (@lem7577782 A p)). Qed.
Lemma lem7577786 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7577787 {A : Type'} (p : type1621 A) : (term122 A p) = True.
Proof. exact (@lem7577786 (term107 A p)). Qed.
Lemma lem7577788 {A : Type'} (p : type1621 A) : (term121 A p) = True.
Proof. exact (TRANS (@lem7577784 A p) (@lem7577787 A p)). Qed.
Lemma lem7577789 {A : Type'} : (term123 A) = (term124 A).
Proof. exact (fun_ext (fun p : type1621 A => @lem7577788 A p)). Qed.
Lemma lem7577790 {A : Type'} : (@all (real -> A -> real)) = (@all (real -> A -> real)).
Proof. exact (eq_refl (@all (real -> A -> real))). Qed.
Lemma lem7577791 {A : Type'} : (term72 A) = (term125 A).
Proof. exact (MK_COMB (@lem7577790 A) (@lem7577789 A)). Qed.
Lemma lem7577793 {A : Type'} (t : Prop) : (term126 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7577794 {A : Type'} (t : Prop) : (term127 A t) = t.
Proof. exact (@lem7577793 (type1621 A) t). Qed.
Lemma lem7577795 {A : Type'} : (term125 A) = True.
Proof. exact (@lem7577794 A True). Qed.
Lemma lem7577796 {A : Type'} : (term72 A) = True.
Proof. exact (TRANS (@lem7577791 A) (@lem7577795 A)). Qed.
Lemma lem7577797 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7577798 {A : Type'} : (term74 A) = (and True).
Proof. exact (MK_COMB (@lem7577797) (@lem7577796 A)). Qed.
Lemma lem7577810 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term103 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7577811 (p : Prop) (q : Prop) (p' : Prop) : term104 p q p'.
Proof. exact (fun q' : Prop => @lem7577810 p q p' q'). Qed.
Lemma lem7577812 (p : Prop) (q : Prop) : term105 p q.
Proof. exact (fun p' : Prop => @lem7577811 p q p'). Qed.
Lemma lem7577813 {A : Type'} (x : A) (s : A -> Prop) : term128 A x s.
Proof. exact (@lem7577812 (term80 A x s) (term84 A x s)). Qed.
Lemma lem7577814 {A : Type'} (x : A) (s : A -> Prop) (p' : Prop) : term129 A x s p'.
Proof. exact (@lem7577813 A x s p'). Qed.
Lemma lem7577815 {A : Type'} (x : A) (s : A -> Prop) (p' : Prop) : (term129 A x s p') = (term130 A x s p').
Proof. exact (eq_refl (term129 A x s p')). Qed.
Lemma lem7577816 {A : Type'} (x : A) (s : A -> Prop) (p' : Prop) : term130 A x s p'.
Proof. exact (EQ_MP (@lem7577815 A x s p') (@lem7577814 A x s p')). Qed.
Lemma lem7577817 {A : Type'} (x : A) (s : A -> Prop) (p' : Prop) (q' : Prop) : term131 A x s p' q'.
Proof. exact (@lem7577816 A x s p' q'). Qed.
Lemma lem7577818 {A : Type'} (x : A) (s : A -> Prop) (p' : Prop) (q' : Prop) : (term131 A x s p' q') = (term132 A x s p' q').
Proof. exact (eq_refl (term131 A x s p' q')). Qed.
Lemma lem7577819 {A : Type'} (x : A) (s : A -> Prop) (p' : Prop) (q' : Prop) : term132 A x s p' q'.
Proof. exact (EQ_MP (@lem7577818 A x s p' q') (@lem7577817 A x s p' q')). Qed.
Lemma lem7577933 {A : Type'} (x : A) (s : A -> Prop) : (term80 A x s) = (term80 A x s).
Proof. exact (eq_refl (term80 A x s)). Qed.
Lemma lem7577934 {A : Type'} (x : A) (s : A -> Prop) (q' : Prop) : term133 A x s q'.
Proof. exact (@lem7577819 A x s (term80 A x s) q'). Qed.
Lemma lem7577935 {A : Type'} (x : A) (s : A -> Prop) (q' : Prop) : term134 A x s q'.
Proof. exact (@lem7577934 A x s q' (@lem7577933 A x s)). Qed.
Lemma lem7577936 {A : Type'} (x : A) (s : A -> Prop) (h1 : term80 A x s) : term80 A x s.
Proof. exact (h1). Qed.
Lemma lem7577937 {A : Type'} (x : A) (s : A -> Prop) (h1 : term80 A x s) : term78 A x s.
Proof. exact (proj2 (@lem7577936 A x s h1)). Qed.
Lemma lem7577938 {A : Type'} (x : A) (s : A -> Prop) (h1 : term80 A x s) : @FINITE A s.
Proof. exact (proj2 (@lem7577937 A x s h1)). Qed.
Lemma lem7577939 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem7577941 {A : Type'} (x : A) (s : A -> Prop) (h1 : term80 A x s) : term135 A x s.
Proof. exact (proj1 (@lem7577937 A x s h1)). Qed.
Lemma lem7577942 {A : Type'} (x : A) (s : A -> Prop) : term136 A x s.
Proof. exact (@lem82 (@IN A x s)). Qed.
Lemma lem7577964 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term103 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7577965 (p : Prop) (q : Prop) (p' : Prop) : term104 p q p'.
Proof. exact (fun q' : Prop => @lem7577964 p q p' q'). Qed.
Lemma lem7577966 (p : Prop) (q : Prop) : term105 p q.
Proof. exact (fun p' : Prop => @lem7577965 p q p'). Qed.
Lemma lem7577967 {A : Type'} (x : A) (s : A -> Prop) (p : type1621 A) : term137 A x s p.
Proof. exact (@lem7577966 (term138 A x s p) (term139 A x s p)). Qed.
Lemma lem7577968 {A : Type'} (x : A) (s : A -> Prop) (p : type1621 A) (p' : Prop) : term140 A x s p p'.
Proof. exact (@lem7577967 A x s p p'). Qed.
Lemma lem7577969 {A : Type'} (x : A) (s : A -> Prop) (p : type1621 A) (p' : Prop) : (term140 A x s p p') = (term141 A x s p p').
Proof. exact (eq_refl (term140 A x s p p')). Qed.
Lemma lem7577970 {A : Type'} (x : A) (s : A -> Prop) (p : type1621 A) (p' : Prop) : term141 A x s p p'.
Proof. exact (EQ_MP (@lem7577969 A x s p p') (@lem7577968 A x s p p')). Qed.
Lemma lem7577971 {A : Type'} (x : A) (s : A -> Prop) (p : type1621 A) (p' : Prop) (q' : Prop) : term142 A x s p p' q'.
Proof. exact (@lem7577970 A x s p p' q'). Qed.
Lemma lem7577972 {A : Type'} (x : A) (s : A -> Prop) (p : type1621 A) (p' : Prop) (q' : Prop) : (term142 A x s p p' q') = (term143 A x s p p' q').
Proof. exact (eq_refl (term142 A x s p p' q')). Qed.
Lemma lem7577973 {A : Type'} (x : A) (s : A -> Prop) (p : type1621 A) (p' : Prop) (q' : Prop) : term143 A x s p p' q'.
Proof. exact (EQ_MP (@lem7577972 A x s p p' q') (@lem7577971 A x s p p' q')). Qed.
Lemma lem7578007 {A : Type'} (x : A) (s : A -> Prop) (p : type1621 A) : (term138 A x s p) = (term138 A x s p).
Proof. exact (eq_refl (term138 A x s p)). Qed.
Lemma lem7578008 {A : Type'} (x : A) (s : A -> Prop) (p : type1621 A) (q' : Prop) : term144 A x s p q'.
Proof. exact (@lem7577973 A x s p (term138 A x s p) q'). Qed.
Lemma lem7578009 {A : Type'} (x : A) (s : A -> Prop) (p : type1621 A) (q' : Prop) : term145 A x s p q'.
Proof. exact (@lem7578008 A x s p q' (@lem7578007 A x s p)). Qed.
Lemma lem7578027 {_131524 : Type'} (x : _131524) (s : _131524 -> Prop) (f : _131524 -> real) : term21 _131524 x s f.
Proof. exact (fun h0 : @FINITE _131524 s => @lem7577468 _131524 x f s h0). Qed.
Lemma lem7578028 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) : term21 A x s f.
Proof. exact (@lem7578027 A x s f). Qed.
Lemma lem7578029 {A : Type'} (x : A) (s : A -> Prop) (p : type1621 A) (x' : real) : term146 A x s p x'.
Proof. exact (@lem7578028 A x s (p x')). Qed.
Lemma lem7578031 {A : Type'} (x : A) (s : A -> Prop) (h1 : term80 A x s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem7577939 A s) (@lem7577938 A x s h1)). Qed.
Lemma lem7578032 {A : Type'} (x : A) (s : A -> Prop) (h1 : term80 A x s) : True = (@FINITE A s).
Proof. exact (SYM (@lem7578031 A x s h1)). Qed.
Lemma lem7578033 {A : Type'} (x : A) (s : A -> Prop) (h1 : term80 A x s) : @FINITE A s.
Proof. exact (EQ_MP (@lem7578032 A x s h1) (@lem0)). Qed.
Lemma lem7578034 {A : Type'} (p : type1621 A) (x : real) (x' : A) (s : A -> Prop) (h1 : term80 A x' s) : (term147 A x' s p x) = (term148 A x' s p x).
Proof. exact (@lem7578029 A x' s p x (@lem7578033 A x' s h1)). Qed.
Lemma lem7578036 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term149 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem7578037 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term150 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem7578036 _2963 g t e g' t' e'). Qed.
Lemma lem7578038 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term151 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem7578037 _2963 g t e g' t'). Qed.
Lemma lem7578039 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term152 _2963 g t e.
Proof. exact (fun g' : Prop => @lem7578038 _2963 g t e g'). Qed.
Lemma lem7578040 (g : Prop) (t : real) (e : real) : term153 g t e.
Proof. exact (@lem7578039 real g t e). Qed.
Lemma lem7578041 {A : Type'} (x : A) (s : A -> Prop) (p : type1621 A) (x' : real) : term154 A x s p x'.
Proof. exact (@lem7578040 (@IN A x s) (term155 A s p x') (term156 A x s p x')). Qed.
Lemma lem7578042 {A : Type'} (x : A) (s : A -> Prop) (p : type1621 A) (x' : real) (g' : Prop) : term157 A x s p x' g'.
Proof. exact (@lem7578041 A x s p x' g'). Qed.
Lemma lem7578043 {A : Type'} (x : A) (s : A -> Prop) (p : type1621 A) (x' : real) (g' : Prop) : (term157 A x s p x' g') = (term158 A x s p x' g').
Proof. exact (eq_refl (term157 A x s p x' g')). Qed.
Lemma lem7578044 {A : Type'} (x : A) (s : A -> Prop) (p : type1621 A) (x' : real) (g' : Prop) : term158 A x s p x' g'.
Proof. exact (EQ_MP (@lem7578043 A x s p x' g') (@lem7578042 A x s p x' g')). Qed.
Lemma lem7578045 {A : Type'} (x : A) (s : A -> Prop) (p : type1621 A) (x' : real) (g' : Prop) (t' : real) : term159 A x s p x' g' t'.
Proof. exact (@lem7578044 A x s p x' g' t'). Qed.
Lemma lem7578046 {A : Type'} (x : A) (s : A -> Prop) (p : type1621 A) (x' : real) (g' : Prop) (t' : real) : (term159 A x s p x' g' t') = (term160 A x s p x' g' t').
Proof. exact (eq_refl (term159 A x s p x' g' t')). Qed.
Lemma lem7578047 {A : Type'} (x : A) (s : A -> Prop) (p : type1621 A) (x' : real) (g' : Prop) (t' : real) : term160 A x s p x' g' t'.
Proof. exact (EQ_MP (@lem7578046 A x s p x' g' t') (@lem7578045 A x s p x' g' t')). Qed.
Lemma lem7578048 {A : Type'} (x : A) (s : A -> Prop) (p : type1621 A) (x' : real) (g' : Prop) (t' : real) (e' : real) : term161 A x s p x' g' t' e'.
Proof. exact (@lem7578047 A x s p x' g' t' e'). Qed.
Lemma lem7578049 {A : Type'} (x : A) (s : A -> Prop) (p : type1621 A) (x' : real) (g' : Prop) (t' : real) (e' : real) : (term161 A x s p x' g' t' e') = (term162 A x s p x' g' t' e').
Proof. exact (eq_refl (term161 A x s p x' g' t' e')). Qed.
Lemma lem7578050 {A : Type'} (x : A) (s : A -> Prop) (p : type1621 A) (x' : real) (g' : Prop) (t' : real) (e' : real) : term162 A x s p x' g' t' e'.
Proof. exact (EQ_MP (@lem7578049 A x s p x' g' t' e') (@lem7578048 A x s p x' g' t' e')). Qed.
Lemma lem7578052 {A : Type'} (x : A) (s : A -> Prop) (h1 : term80 A x s) : (@IN A x s) = False.
Proof. exact (@lem7577942 A x s (@lem7577941 A x s h1)). Qed.
Lemma lem7578053 {A : Type'} (x : A) (s : A -> Prop) (p : type1621 A) (x' : real) (t' : real) (e' : real) : term163 A x s p x' t' e'.
Proof. exact (@lem7578050 A x s p x' False t' e'). Qed.
Lemma lem7578054 {A : Type'} (p : type1621 A) (x : real) (t' : real) (e' : real) (x' : A) (s : A -> Prop) (h1 : term80 A x' s) : term164 A x' s p x t' e'.
Proof. exact (@lem7578053 A x' s p x t' e' (@lem7578052 A x' s h1)). Qed.
Lemma lem7578058 {A : Type'} (s : A -> Prop) (p : type1621 A) (x : real) : (term155 A s p x) = (term155 A s p x).
Proof. exact (eq_refl (term155 A s p x)). Qed.
Lemma lem7578059 {A : Type'} (s : A -> Prop) (p : type1621 A) (x : real) : term165 A s p x.
Proof. exact (fun h0 : False => @lem7578058 A s p x). Qed.
Lemma lem7578060 {A : Type'} (p : type1621 A) (x : real) (e' : real) (x' : A) (s : A -> Prop) (h1 : term80 A x' s) : term166 A x' s p x e'.
Proof. exact (@lem7578054 A p x (term155 A s p x) e' x' s h1). Qed.
Lemma lem7578061 {A : Type'} (p : type1621 A) (x : real) (e' : real) (x' : A) (s : A -> Prop) (h1 : term80 A x' s) : term167 A x' s p x e'.
Proof. exact (@lem7578060 A p x e' x' s h1 (@lem7578059 A s p x)). Qed.
Lemma lem7578067 {A : Type'} (x : A) (s : A -> Prop) (p : type1621 A) (x' : real) : (term156 A x s p x') = (term156 A x s p x').
Proof. exact (eq_refl (term156 A x s p x')). Qed.
Lemma lem7578068 {A : Type'} (x : A) (s : A -> Prop) (p : type1621 A) (x' : real) : term168 A x s p x'.
Proof. exact (fun h0 : ~ False => @lem7578067 A x s p x'). Qed.
Lemma lem7578069 {A : Type'} (p : type1621 A) (x : real) (x' : A) (s : A -> Prop) (h1 : term80 A x' s) : term169 A x' s p x.
Proof. exact (@lem7578061 A p x (term156 A x' s p x) x' s h1). Qed.
Lemma lem7578070 {A : Type'} (p : type1621 A) (x : real) (x' : A) (s : A -> Prop) (h1 : term80 A x' s) : (term148 A x' s p x) = (term170 A x' s p x).
Proof. exact (@lem7578069 A p x x' s h1 (@lem7578068 A x' s p x)). Qed.
Lemma lem7578072 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem7578073 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem7578072 real t1 t2). Qed.
Lemma lem7578074 {A : Type'} (x : A) (s : A -> Prop) (p : type1621 A) (x' : real) : (term170 A x s p x') = (term156 A x s p x').
Proof. exact (@lem7578073 (term155 A s p x') (term156 A x s p x')). Qed.
Lemma lem7578075 {A : Type'} (p : type1621 A) (x : real) (x' : A) (s : A -> Prop) (h1 : term80 A x' s) : (term148 A x' s p x) = (term156 A x' s p x).
Proof. exact (TRANS (@lem7578070 A p x x' s h1) (@lem7578074 A x' s p x)). Qed.
Lemma lem7578076 {A : Type'} (p : type1621 A) (x : real) (x' : A) (s : A -> Prop) (h1 : term80 A x' s) : (term147 A x' s p x) = (term156 A x' s p x).
Proof. exact (TRANS (@lem7578034 A p x x' s h1) (@lem7578075 A p x x' s h1)). Qed.
Lemma lem7578077 {A : Type'} (p : type1621 A) (x : A) (s : A -> Prop) (h1 : term80 A x s) : (term171 A x s p) = (term172 A x s p).
Proof. exact (fun_ext (fun x' : real => @lem7578076 A p x' x s h1)). Qed.
Lemma lem7578078 : polynomial_function = polynomial_function.
Proof. exact (eq_refl polynomial_function). Qed.
Lemma lem7578079 {A : Type'} (p : type1621 A) (x : A) (s : A -> Prop) (h1 : term80 A x s) : (term139 A x s p) = (term173 A x s p).
Proof. exact (MK_COMB (@lem7578078) (@lem7578077 A p x s h1)). Qed.
Lemma lem7578083 {A : Type'} (p : type1621 A) (x : A) (s : A -> Prop) (h1 : term80 A x s) : term174 A x s p.
Proof. exact (fun h0 : term138 A x s p => @lem7578079 A p x s h1). Qed.
Lemma lem7578084 {A : Type'} (x : A) (s : A -> Prop) (p : type1621 A) : term175 A x s p.
Proof. exact (@lem7578009 A x s p (term173 A x s p)). Qed.
Lemma lem7578085 {A : Type'} (p : type1621 A) (x : A) (s : A -> Prop) (h1 : term80 A x s) : (term176 A x s p) = (term177 A x s p).
Proof. exact (@lem7578084 A x s p (@lem7578083 A p x s h1)). Qed.
Lemma lem7578191 {A : Type'} (x : A) (s : A -> Prop) (h1 : term80 A x s) : (term178 A x s) = (term179 A x s).
Proof. exact (fun_ext (fun p : type1621 A => @lem7578085 A p x s h1)). Qed.
Lemma lem7578297 {A : Type'} : (@all (real -> A -> real)) = (@all (real -> A -> real)).
Proof. exact (eq_refl (@all (real -> A -> real))). Qed.
Lemma lem7578298 {A : Type'} (x : A) (s : A -> Prop) (h1 : term80 A x s) : (term84 A x s) = (term180 A x s).
Proof. exact (MK_COMB (@lem7578297 A) (@lem7578191 A x s h1)). Qed.
Lemma lem7578408 {A : Type'} (x : A) (s : A -> Prop) : term181 A x s.
Proof. exact (fun h0 : term80 A x s => @lem7578298 A x s h0). Qed.
Lemma lem7578409 {A : Type'} (x : A) (s : A -> Prop) : term182 A x s.
Proof. exact (@lem7577935 A x s (term180 A x s)). Qed.
Lemma lem7578410 {A : Type'} (x : A) (s : A -> Prop) : (term86 A x s) = (term183 A x s).
Proof. exact (@lem7578409 A x s (@lem7578408 A x s)). Qed.
Lemma lem7578896 {A : Type'} (x : A) : (term88 A x) = (term184 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7578410 A x s)). Qed.
Lemma lem7579382 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7579383 {A : Type'} (x : A) : (term90 A x) = (term185 A x).
Proof. exact (MK_COMB (@lem7579382 A) (@lem7578896 A x)). Qed.
Lemma lem7579873 {A : Type'} : (term92 A) = (term186 A).
Proof. exact (fun_ext (fun x : A => @lem7579383 A x)). Qed.
Lemma lem7580363 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7580364 {A : Type'} : (term94 A) = (term187 A).
Proof. exact (MK_COMB (@lem7580363 A) (@lem7579873 A)). Qed.
Lemma lem7580858 {A : Type'} : (term96 A) = (term188 A).
Proof. exact (MK_COMB (@lem7577798 A) (@lem7580364 A)). Qed.
Lemma lem7580860 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7580861 {A : Type'} : (term188 A) = (term187 A).
Proof. exact (@lem7580860 (term187 A)). Qed.
Lemma lem7581355 {A : Type'} : (term96 A) = (term187 A).
Proof. exact (TRANS (@lem7580858 A) (@lem7580861 A)). Qed.
Lemma lem7581356 {A : Type'} : (term187 A) = (term96 A).
Proof. exact (SYM (@lem7581355 A)). Qed.
Lemma lem7581368 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term103 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7581369 (p : Prop) (q : Prop) (p' : Prop) : term104 p q p'.
Proof. exact (fun q' : Prop => @lem7581368 p q p' q'). Qed.
Lemma lem7581370 (p : Prop) (q : Prop) : term105 p q.
Proof. exact (fun p' : Prop => @lem7581369 p q p'). Qed.
Lemma lem7581371 {A : Type'} (x : A) (s : A -> Prop) : term189 A x s.
Proof. exact (@lem7581370 (term80 A x s) (term180 A x s)). Qed.
Lemma lem7581372 {A : Type'} (x : A) (s : A -> Prop) (p' : Prop) : term190 A x s p'.
Proof. exact (@lem7581371 A x s p'). Qed.
Lemma lem7581373 {A : Type'} (x : A) (s : A -> Prop) (p' : Prop) : (term190 A x s p') = (term191 A x s p').
Proof. exact (eq_refl (term190 A x s p')). Qed.
Lemma lem7581374 {A : Type'} (x : A) (s : A -> Prop) (p' : Prop) : term191 A x s p'.
Proof. exact (EQ_MP (@lem7581373 A x s p') (@lem7581372 A x s p')). Qed.
Lemma lem7581375 {A : Type'} (x : A) (s : A -> Prop) (p' : Prop) (q' : Prop) : term192 A x s p' q'.
Proof. exact (@lem7581374 A x s p' q'). Qed.
Lemma lem7581376 {A : Type'} (x : A) (s : A -> Prop) (p' : Prop) (q' : Prop) : (term192 A x s p' q') = (term193 A x s p' q').
Proof. exact (eq_refl (term192 A x s p' q')). Qed.
Lemma lem7581377 {A : Type'} (x : A) (s : A -> Prop) (p' : Prop) (q' : Prop) : term193 A x s p' q'.
Proof. exact (EQ_MP (@lem7581376 A x s p' q') (@lem7581375 A x s p' q')). Qed.
Lemma lem7581473 {A : Type'} (x : A) (s : A -> Prop) : (term80 A x s) = (term80 A x s).
Proof. exact (eq_refl (term80 A x s)). Qed.
Lemma lem7581474 {A : Type'} (x : A) (s : A -> Prop) (q' : Prop) : term194 A x s q'.
Proof. exact (@lem7581377 A x s (term80 A x s) q'). Qed.
Lemma lem7581475 {A : Type'} (x : A) (s : A -> Prop) (q' : Prop) : term195 A x s q'.
Proof. exact (@lem7581474 A x s q' (@lem7581473 A x s)). Qed.
Lemma lem7581476 {A : Type'} (x : A) (s : A -> Prop) (h1 : term80 A x s) : term80 A x s.
Proof. exact (h1). Qed.
Lemma lem7581484 {A : Type'} (x : A) (s : A -> Prop) (h1 : term80 A x s) : term63 A s.
Proof. exact (proj1 (@lem7581476 A x s h1)). Qed.
Lemma lem7581485 {A : Type'} (p : type1621 A) (x : A) (s : A -> Prop) (h1 : term80 A x s) : term54 A s p.
Proof. exact (@lem7581484 A x s h1 p). Qed.
Lemma lem7581486 {A : Type'} (s : A -> Prop) (p : type1621 A) : (term54 A s p) = (term55 A s p).
Proof. exact (eq_refl (term54 A s p)). Qed.
Lemma lem7581487 {A : Type'} (p : type1621 A) (x : A) (s : A -> Prop) (h1 : term80 A x s) : term55 A s p.
Proof. exact (EQ_MP (@lem7581486 A s p) (@lem7581485 A p x s h1)). Qed.
Lemma lem7581488 {A : Type'} (s : A -> Prop) (p : type1621 A) (h1 : term43 A s p) : term43 A s p.
Proof. exact (h1). Qed.
Lemma lem7581489 {A : Type'} (p : type1621 A) (x : A) (s : A -> Prop) (h1 : term43 A s p) (h2 : term80 A x s) : term44 A s p.
Proof. exact (@lem7581487 A p x s h2 (@lem7581488 A s p h1)). Qed.
Lemma lem7581490 {A : Type'} (s : A -> Prop) (p : type1621 A) : (term44 A s p) = ((term44 A s p) = True).
Proof. exact (@lem7 (term44 A s p)). Qed.
Lemma lem7581491 {A : Type'} (p : type1621 A) (x : A) (s : A -> Prop) (h1 : term43 A s p) (h2 : term80 A x s) : (term44 A s p) = True.
Proof. exact (EQ_MP (@lem7581490 A s p) (@lem7581489 A p x s h1 h2)). Qed.
Lemma lem7581504 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term103 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7581505 (p : Prop) (q : Prop) (p' : Prop) : term104 p q p'.
Proof. exact (fun q' : Prop => @lem7581504 p q p' q'). Qed.
Lemma lem7581506 (p : Prop) (q : Prop) : term105 p q.
Proof. exact (fun p' : Prop => @lem7581505 p q p'). Qed.
Lemma lem7581507 {A : Type'} (x : A) (s : A -> Prop) (p : type1621 A) : term196 A x s p.
Proof. exact (@lem7581506 (term138 A x s p) (term173 A x s p)). Qed.
Lemma lem7581508 {A : Type'} (x : A) (s : A -> Prop) (p : type1621 A) (p' : Prop) : term197 A x s p p'.
Proof. exact (@lem7581507 A x s p p'). Qed.
Lemma lem7581509 {A : Type'} (x : A) (s : A -> Prop) (p : type1621 A) (p' : Prop) : (term197 A x s p p') = (term198 A x s p p').
Proof. exact (eq_refl (term197 A x s p p')). Qed.
Lemma lem7581510 {A : Type'} (x : A) (s : A -> Prop) (p : type1621 A) (p' : Prop) : term198 A x s p p'.
Proof. exact (EQ_MP (@lem7581509 A x s p p') (@lem7581508 A x s p p')). Qed.
Lemma lem7581511 {A : Type'} (x : A) (s : A -> Prop) (p : type1621 A) (p' : Prop) (q' : Prop) : term199 A x s p p' q'.
Proof. exact (@lem7581510 A x s p p' q'). Qed.
Lemma lem7581512 {A : Type'} (x : A) (s : A -> Prop) (p : type1621 A) (p' : Prop) (q' : Prop) : (term199 A x s p p' q') = (term200 A x s p p' q').
Proof. exact (eq_refl (term199 A x s p p' q')). Qed.
Lemma lem7581513 {A : Type'} (x : A) (s : A -> Prop) (p : type1621 A) (p' : Prop) (q' : Prop) : term200 A x s p p' q'.
Proof. exact (EQ_MP (@lem7581512 A x s p p' q') (@lem7581511 A x s p p' q')). Qed.
Lemma lem7581515 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term11 _83983 a s P) = (term12 _83983 a s P).
Proof. exact (EQ_MP (@lem7577450 _83983 a s P) (@lem7577449 _83983 a P s)). Qed.
Lemma lem7581516 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : (term11 A a s P) = (term12 A a s P).
Proof. exact (@lem7581515 A a s P). Qed.
Lemma lem7581517 {A : Type'} (x : A) (s : A -> Prop) (p : type1621 A) : (term201 A x s p) = (term202 A x s p).
Proof. exact (@lem7581516 A x s (term203 A p)). Qed.
Lemma lem7581518 {A : Type'} (p : type1621 A) (i : A) : (term204 A p i) = (term205 A p i).
Proof. exact (eq_refl (term204 A p i)). Qed.
Lemma lem7581519 {A : Type'} (i : A) (x : A) (s : A -> Prop) : (term206 A i x s) = (term206 A i x s).
Proof. exact (eq_refl (term206 A i x s)). Qed.
Lemma lem7581520 {A : Type'} (x : A) (s : A -> Prop) (p : type1621 A) (i : A) : (term207 A x s p i) = (term208 A x s p i).
Proof. exact (MK_COMB (@lem7581519 A i x s) (@lem7581518 A p i)). Qed.
Lemma lem7581521 {A : Type'} (x : A) (s : A -> Prop) (p : type1621 A) : (term209 A x s p) = (term210 A x s p).
Proof. exact (fun_ext (fun i : A => @lem7581520 A x s p i)). Qed.
Lemma lem7581522 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7581523 {A : Type'} (x : A) (s : A -> Prop) (p : type1621 A) : (term201 A x s p) = (term138 A x s p).
Proof. exact (MK_COMB (@lem7581522 A) (@lem7581521 A x s p)). Qed.
Lemma lem7581524 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7581525 {A : Type'} (x : A) (s : A -> Prop) (p : type1621 A) : (term211 A x s p) = (term212 A x s p).
Proof. exact (MK_COMB (@lem7581524) (@lem7581523 A x s p)). Qed.
Lemma lem7581526 {A : Type'} (p : type1621 A) (x : A) : (term204 A p x) = (term205 A p x).
Proof. exact (eq_refl (term204 A p x)). Qed.
Lemma lem7581527 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7581528 {A : Type'} (p : type1621 A) (x : A) : (term213 A p x) = (term214 A p x).
Proof. exact (MK_COMB (@lem7581527) (@lem7581526 A p x)). Qed.
Lemma lem7581529 {A : Type'} (p : type1621 A) (i : A) : (term204 A p i) = (term205 A p i).
Proof. exact (eq_refl (term204 A p i)). Qed.
Lemma lem7581530 {A : Type'} (i : A) (s : A -> Prop) : (term215 A i s) = (term215 A i s).
Proof. exact (eq_refl (term215 A i s)). Qed.
Lemma lem7581531 {A : Type'} (s : A -> Prop) (p : type1621 A) (i : A) : (term216 A s p i) = (term217 A s p i).
Proof. exact (MK_COMB (@lem7581530 A i s) (@lem7581529 A p i)). Qed.
Lemma lem7581532 {A : Type'} (s : A -> Prop) (p : type1621 A) : (term218 A s p) = (term219 A s p).
Proof. exact (fun_ext (fun i : A => @lem7581531 A s p i)). Qed.
Lemma lem7581533 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7581534 {A : Type'} (s : A -> Prop) (p : type1621 A) : (term220 A s p) = (term43 A s p).
Proof. exact (MK_COMB (@lem7581533 A) (@lem7581532 A s p)). Qed.
Lemma lem7581535 {A : Type'} (x : A) (s : A -> Prop) (p : type1621 A) : (term202 A x s p) = (term221 A x s p).
Proof. exact (MK_COMB (@lem7581528 A p x) (@lem7581534 A s p)). Qed.
Lemma lem7581536 {A : Type'} (x : A) (s : A -> Prop) (p : type1621 A) : ((term201 A x s p) = (term202 A x s p)) = ((term138 A x s p) = (term221 A x s p)).
Proof. exact (MK_COMB (@lem7581525 A x s p) (@lem7581535 A x s p)). Qed.
Lemma lem7581537 {A : Type'} (x : A) (s : A -> Prop) (p : type1621 A) : (term138 A x s p) = (term221 A x s p).
Proof. exact (EQ_MP (@lem7581536 A x s p) (@lem7581517 A x s p)). Qed.
Lemma lem7581567 {A : Type'} (x : A) (s : A -> Prop) (p : type1621 A) (q' : Prop) : term222 A x s p q'.
Proof. exact (@lem7581513 A x s p (term221 A x s p) q'). Qed.
Lemma lem7581568 {A : Type'} (x : A) (s : A -> Prop) (p : type1621 A) (q' : Prop) : term223 A x s p q'.
Proof. exact (@lem7581567 A x s p q' (@lem7581537 A x s p)). Qed.
Lemma lem7581569 {A : Type'} (x : A) (s : A -> Prop) (p : type1621 A) (h1 : term221 A x s p) : term221 A x s p.
Proof. exact (h1). Qed.
Lemma lem7581570 {A : Type'} (x : A) (s : A -> Prop) (p : type1621 A) (h1 : term221 A x s p) : term43 A s p.
Proof. exact (proj2 (@lem7581569 A x s p h1)). Qed.
Lemma lem7581571 {A : Type'} (i : A) (x : A) (s : A -> Prop) (p : type1621 A) (h1 : term221 A x s p) : term224 A s p i.
Proof. exact (@lem7581570 A x s p h1 i). Qed.
Lemma lem7581572 {A : Type'} (s : A -> Prop) (p : type1621 A) (i : A) : (term224 A s p i) = (term217 A s p i).
Proof. exact (eq_refl (term224 A s p i)). Qed.
Lemma lem7581573 {A : Type'} (i : A) (x : A) (s : A -> Prop) (p : type1621 A) (h1 : term221 A x s p) : term217 A s p i.
Proof. exact (EQ_MP (@lem7581572 A s p i) (@lem7581571 A i x s p h1)). Qed.
Lemma lem7581574 {A : Type'} (i : A) (s : A -> Prop) (h1 : @IN A i s) : @IN A i s.
Proof. exact (h1). Qed.
Lemma lem7581575 {A : Type'} (x : A) (p : type1621 A) (i : A) (s : A -> Prop) (h1 : term221 A x s p) (h2 : @IN A i s) : term205 A p i.
Proof. exact (@lem7581573 A i x s p h1 (@lem7581574 A i s h2)). Qed.
Lemma lem7581576 {A : Type'} (p : type1621 A) (i : A) : (term205 A p i) = ((term205 A p i) = True).
Proof. exact (@lem7 (term205 A p i)). Qed.
Lemma lem7581577 {A : Type'} (x : A) (p : type1621 A) (i : A) (s : A -> Prop) (h1 : term221 A x s p) (h2 : @IN A i s) : (term205 A p i) = True.
Proof. exact (EQ_MP (@lem7581576 A p i) (@lem7581575 A x p i s h1 h2)). Qed.
Lemma lem7581583 {A : Type'} (x : A) (s : A -> Prop) (p : type1621 A) (h1 : term221 A x s p) : term205 A p x.
Proof. exact (proj1 (@lem7581569 A x s p h1)). Qed.
Lemma lem7581584 {A : Type'} (p : type1621 A) (x : A) : (term205 A p x) = ((term205 A p x) = True).
Proof. exact (@lem7 (term205 A p x)). Qed.
Lemma lem7581587 (p : real -> real) (q : real -> real) : term225 p q.
Proof. exact (fun h0 : term4 p q => @lem7577437 p q h0). Qed.
Lemma lem7581588 {A : Type'} (x : A) (s : A -> Prop) (p : type1621 A) : term226 A x s p.
Proof. exact (@lem7581587 (term227 A p x) (term228 A s p)). Qed.
Lemma lem7581589 {A : Type'} (p : type1621 A) (x : real) (x' : A) : (term229 A p x' x) = (p x x').
Proof. exact (eq_refl (term229 A p x' x)). Qed.
Lemma lem7581590 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7581591 {A : Type'} (p : type1621 A) (x : real) (x' : A) : (term230 A p x' x) = (term231 A p x x').
Proof. exact (MK_COMB (@lem7581590) (@lem7581589 A p x x')). Qed.
Lemma lem7581592 {A : Type'} (s : A -> Prop) (p : type1621 A) (x : real) : (term232 A s p x) = (term155 A s p x).
Proof. exact (eq_refl (term232 A s p x)). Qed.
Lemma lem7581593 {A : Type'} (x : A) (s : A -> Prop) (p : type1621 A) (x' : real) : (term233 A x s p x') = (term156 A x s p x').
Proof. exact (MK_COMB (@lem7581591 A p x' x) (@lem7581592 A s p x')). Qed.
Lemma lem7581594 {A : Type'} (x : A) (s : A -> Prop) (p : type1621 A) : (term234 A x s p) = (term172 A x s p).
Proof. exact (fun_ext (fun x' : real => @lem7581593 A x s p x')). Qed.
Lemma lem7581595 : polynomial_function = polynomial_function.
Proof. exact (eq_refl polynomial_function). Qed.
Lemma lem7581596 {A : Type'} (x : A) (s : A -> Prop) (p : type1621 A) : (term235 A x s p) = (term173 A x s p).
Proof. exact (MK_COMB (@lem7581595) (@lem7581594 A x s p)). Qed.
Lemma lem7581597 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7581598 {A : Type'} (x : A) (s : A -> Prop) (p : type1621 A) : (term236 A x s p) = (term237 A x s p).
Proof. exact (MK_COMB (@lem7581597) (@lem7581596 A x s p)). Qed.
Lemma lem7581599 : True = True.
Proof. exact (eq_refl True). Qed.
Lemma lem7581600 {A : Type'} (x : A) (s : A -> Prop) (p : type1621 A) : ((term235 A x s p) = True) = ((term173 A x s p) = True).
Proof. exact (MK_COMB (@lem7581598 A x s p) (@lem7581599)). Qed.
Lemma lem7581601 {A : Type'} (x : A) (s : A -> Prop) (p : type1621 A) : (term238 A x s p) = (term238 A x s p).
Proof. exact (eq_refl (term238 A x s p)). Qed.
Lemma lem7581602 {A : Type'} (x : A) (s : A -> Prop) (p : type1621 A) : (term226 A x s p) = (term239 A x s p).
Proof. exact (MK_COMB (@lem7581601 A x s p) (@lem7581600 A x s p)). Qed.
Lemma lem7581603 {A : Type'} (x : A) (s : A -> Prop) (p : type1621 A) : term239 A x s p.
Proof. exact (EQ_MP (@lem7581602 A x s p) (@lem7581588 A x s p)). Qed.
Lemma lem7581607 {A : Type'} (x : A) (s : A -> Prop) (p : type1621 A) (h1 : term221 A x s p) : (term205 A p x) = True.
Proof. exact (EQ_MP (@lem7581584 A p x) (@lem7581583 A x s p h1)). Qed.
Lemma lem7581608 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7581609 {A : Type'} (x : A) (s : A -> Prop) (p : type1621 A) (h1 : term221 A x s p) : (term214 A p x) = (and True).
Proof. exact (MK_COMB (@lem7581608) (@lem7581607 A x s p h1)). Qed.
Lemma lem7581611 {A : Type'} (p : type1621 A) (x : A) (s : A -> Prop) (h1 : term80 A x s) : term240 A s p.
Proof. exact (fun h0 : term43 A s p => @lem7581491 A p x s h0 h1). Qed.
Lemma lem7581619 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term103 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7581620 (p : Prop) (q : Prop) (p' : Prop) : term104 p q p'.
Proof. exact (fun q' : Prop => @lem7581619 p q p' q'). Qed.
Lemma lem7581621 (p : Prop) (q : Prop) : term105 p q.
Proof. exact (fun p' : Prop => @lem7581620 p q p'). Qed.
Lemma lem7581622 {A : Type'} (s : A -> Prop) (p : type1621 A) (i : A) : term241 A s p i.
Proof. exact (@lem7581621 (@IN A i s) (term205 A p i)). Qed.
Lemma lem7581623 {A : Type'} (s : A -> Prop) (p : type1621 A) (i : A) (p' : Prop) : term242 A s p i p'.
Proof. exact (@lem7581622 A s p i p'). Qed.
Lemma lem7581624 {A : Type'} (s : A -> Prop) (p : type1621 A) (i : A) (p' : Prop) : (term242 A s p i p') = (term243 A s p i p').
Proof. exact (eq_refl (term242 A s p i p')). Qed.
Lemma lem7581625 {A : Type'} (s : A -> Prop) (p : type1621 A) (i : A) (p' : Prop) : term243 A s p i p'.
Proof. exact (EQ_MP (@lem7581624 A s p i p') (@lem7581623 A s p i p')). Qed.
Lemma lem7581626 {A : Type'} (s : A -> Prop) (p : type1621 A) (i : A) (p' : Prop) (q' : Prop) : term244 A s p i p' q'.
Proof. exact (@lem7581625 A s p i p' q'). Qed.
Lemma lem7581627 {A : Type'} (s : A -> Prop) (p : type1621 A) (i : A) (p' : Prop) (q' : Prop) : (term244 A s p i p' q') = (term245 A s p i p' q').
Proof. exact (eq_refl (term244 A s p i p' q')). Qed.
Lemma lem7581628 {A : Type'} (s : A -> Prop) (p : type1621 A) (i : A) (p' : Prop) (q' : Prop) : term245 A s p i p' q'.
Proof. exact (EQ_MP (@lem7581627 A s p i p' q') (@lem7581626 A s p i p' q')). Qed.
Lemma lem7581629 {A : Type'} (i : A) (s : A -> Prop) : (@IN A i s) = (@IN A i s).
Proof. exact (eq_refl (@IN A i s)). Qed.
Lemma lem7581630 {A : Type'} (p : type1621 A) (i : A) (s : A -> Prop) (q' : Prop) : term246 A p i s q'.
Proof. exact (@lem7581628 A s p i (@IN A i s) q'). Qed.
Lemma lem7581631 {A : Type'} (p : type1621 A) (i : A) (s : A -> Prop) (q' : Prop) : term247 A p i s q'.
Proof. exact (@lem7581630 A p i s q' (@lem7581629 A i s)). Qed.
Lemma lem7581632 {A : Type'} (i : A) (s : A -> Prop) (h1 : @IN A i s) : @IN A i s.
Proof. exact (h1). Qed.
Lemma lem7581633 {A : Type'} (i : A) (s : A -> Prop) : (@IN A i s) = ((@IN A i s) = True).
Proof. exact (@lem7 (@IN A i s)). Qed.
Lemma lem7581636 {A : Type'} (i : A) (x : A) (s : A -> Prop) (p : type1621 A) (h1 : term221 A x s p) : term248 A s p i.
Proof. exact (fun h0 : @IN A i s => @lem7581577 A x p i s h1 h0). Qed.
Lemma lem7581637 {A : Type'} (i : A) (x : A) (s : A -> Prop) (p : type1621 A) (h1 : term221 A x s p) : term248 A s p i.
Proof. exact (@lem7581636 A i x s p h1). Qed.
Lemma lem7581639 {A : Type'} (i : A) (s : A -> Prop) (h1 : @IN A i s) : (@IN A i s) = True.
Proof. exact (EQ_MP (@lem7581633 A i s) (@lem7581632 A i s h1)). Qed.
Lemma lem7581640 {A : Type'} (i : A) (s : A -> Prop) (h1 : @IN A i s) : True = (@IN A i s).
Proof. exact (SYM (@lem7581639 A i s h1)). Qed.
Lemma lem7581641 {A : Type'} (i : A) (s : A -> Prop) (h1 : @IN A i s) : @IN A i s.
Proof. exact (EQ_MP (@lem7581640 A i s h1) (@lem0)). Qed.
Lemma lem7581642 {A : Type'} (x : A) (p : type1621 A) (i : A) (s : A -> Prop) (h1 : term221 A x s p) (h2 : @IN A i s) : (term205 A p i) = True.
Proof. exact (@lem7581637 A i x s p h1 (@lem7581641 A i s h2)). Qed.
Lemma lem7581643 {A : Type'} (i : A) (x : A) (s : A -> Prop) (p : type1621 A) (h1 : term221 A x s p) : term248 A s p i.
Proof. exact (fun h0 : @IN A i s => @lem7581642 A x p i s h1 h0). Qed.
Lemma lem7581644 {A : Type'} (p : type1621 A) (i : A) (s : A -> Prop) : term249 A p i s.
Proof. exact (@lem7581631 A p i s True). Qed.
Lemma lem7581645 {A : Type'} (i : A) (x : A) (s : A -> Prop) (p : type1621 A) (h1 : term221 A x s p) : (term217 A s p i) = (term250 A i s).
Proof. exact (@lem7581644 A p i s (@lem7581643 A i x s p h1)). Qed.
Lemma lem7581647 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7581648 {A : Type'} (i : A) (s : A -> Prop) : (term250 A i s) = True.
Proof. exact (@lem7581647 (@IN A i s)). Qed.
Lemma lem7581649 {A : Type'} (i : A) (x : A) (s : A -> Prop) (p : type1621 A) (h1 : term221 A x s p) : (term217 A s p i) = True.
Proof. exact (TRANS (@lem7581645 A i x s p h1) (@lem7581648 A i s)). Qed.
Lemma lem7581650 {A : Type'} (x : A) (s : A -> Prop) (p : type1621 A) (h1 : term221 A x s p) : (term219 A s p) = (term251 A).
Proof. exact (fun_ext (fun i : A => @lem7581649 A i x s p h1)). Qed.
Lemma lem7581651 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7581652 {A : Type'} (x : A) (s : A -> Prop) (p : type1621 A) (h1 : term221 A x s p) : (term43 A s p) = (term252 A).
Proof. exact (MK_COMB (@lem7581651 A) (@lem7581650 A x s p h1)). Qed.
Lemma lem7581654 {A : Type'} (t : Prop) : (term126 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7581655 {A : Type'} (t : Prop) : (term126 A t) = t.
Proof. exact (@lem7581654 A t). Qed.
Lemma lem7581656 {A : Type'} : (term252 A) = True.
Proof. exact (@lem7581655 A True). Qed.
Lemma lem7581657 {A : Type'} (x : A) (s : A -> Prop) (p : type1621 A) (h1 : term221 A x s p) : (term43 A s p) = True.
Proof. exact (TRANS (@lem7581652 A x s p h1) (@lem7581656 A)). Qed.
Lemma lem7581658 {A : Type'} (x : A) (s : A -> Prop) (p : type1621 A) (h1 : term221 A x s p) : True = (term43 A s p).
Proof. exact (SYM (@lem7581657 A x s p h1)). Qed.
Lemma lem7581659 {A : Type'} (x : A) (s : A -> Prop) (p : type1621 A) (h1 : term221 A x s p) : term43 A s p.
Proof. exact (EQ_MP (@lem7581658 A x s p h1) (@lem0)). Qed.
Lemma lem7581660 {A : Type'} (x : A) (s : A -> Prop) (p : type1621 A) (h1 : term80 A x s) (h2 : term221 A x s p) : (term44 A s p) = True.
Proof. exact (@lem7581611 A p x s h1 (@lem7581659 A x s p h2)). Qed.
Lemma lem7581661 {A : Type'} (x : A) (s : A -> Prop) (p : type1621 A) (h1 : term80 A x s) (h2 : term221 A x s p) : (term253 A x s p) = (True /\ True).
Proof. exact (MK_COMB (@lem7581609 A x s p h2) (@lem7581660 A x s p h1 h2)). Qed.
Lemma lem7581663 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7581664 : (True /\ True) = True.
Proof. exact (@lem7581663 True). Qed.
Lemma lem7581665 {A : Type'} (x : A) (s : A -> Prop) (p : type1621 A) (h1 : term80 A x s) (h2 : term221 A x s p) : (term253 A x s p) = True.
Proof. exact (TRANS (@lem7581661 A x s p h1 h2) (@lem7581664)). Qed.
Lemma lem7581666 {A : Type'} (x : A) (s : A -> Prop) (p : type1621 A) (h1 : term80 A x s) (h2 : term221 A x s p) : True = (term253 A x s p).
Proof. exact (SYM (@lem7581665 A x s p h1 h2)). Qed.
Lemma lem7581667 {A : Type'} (x : A) (s : A -> Prop) (p : type1621 A) (h1 : term80 A x s) (h2 : term221 A x s p) : term253 A x s p.
Proof. exact (EQ_MP (@lem7581666 A x s p h1 h2) (@lem0)). Qed.
Lemma lem7581668 {A : Type'} (x : A) (s : A -> Prop) (p : type1621 A) (h1 : term80 A x s) (h2 : term221 A x s p) : (term173 A x s p) = True.
Proof. exact (@lem7581603 A x s p (@lem7581667 A x s p h1 h2)). Qed.
Lemma lem7581669 {A : Type'} (p : type1621 A) (x : A) (s : A -> Prop) (h1 : term80 A x s) : term254 A x s p.
Proof. exact (fun h0 : term221 A x s p => @lem7581668 A x s p h1 h0). Qed.
Lemma lem7581670 {A : Type'} (x : A) (s : A -> Prop) (p : type1621 A) : term255 A x s p.
Proof. exact (@lem7581568 A x s p True). Qed.
Lemma lem7581671 {A : Type'} (p : type1621 A) (x : A) (s : A -> Prop) (h1 : term80 A x s) : (term177 A x s p) = (term256 A x s p).
Proof. exact (@lem7581670 A x s p (@lem7581669 A p x s h1)). Qed.
Lemma lem7581673 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7581674 {A : Type'} (x : A) (s : A -> Prop) (p : type1621 A) : (term256 A x s p) = True.
Proof. exact (@lem7581673 (term221 A x s p)). Qed.
Lemma lem7581675 {A : Type'} (p : type1621 A) (x : A) (s : A -> Prop) (h1 : term80 A x s) : (term177 A x s p) = True.
Proof. exact (TRANS (@lem7581671 A p x s h1) (@lem7581674 A x s p)). Qed.
Lemma lem7581676 {A : Type'} (x : A) (s : A -> Prop) (h1 : term80 A x s) : (term179 A x s) = (term124 A).
Proof. exact (fun_ext (fun p : type1621 A => @lem7581675 A p x s h1)). Qed.
Lemma lem7581677 {A : Type'} : (@all (real -> A -> real)) = (@all (real -> A -> real)).
Proof. exact (eq_refl (@all (real -> A -> real))). Qed.
Lemma lem7581678 {A : Type'} (x : A) (s : A -> Prop) (h1 : term80 A x s) : (term180 A x s) = (term125 A).
Proof. exact (MK_COMB (@lem7581677 A) (@lem7581676 A x s h1)). Qed.
Lemma lem7581680 {A : Type'} (t : Prop) : (term126 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7581681 {A : Type'} (t : Prop) : (term127 A t) = t.
Proof. exact (@lem7581680 (type1621 A) t). Qed.
Lemma lem7581682 {A : Type'} : (term125 A) = True.
Proof. exact (@lem7581681 A True). Qed.
Lemma lem7581683 {A : Type'} (x : A) (s : A -> Prop) (h1 : term80 A x s) : (term180 A x s) = True.
Proof. exact (TRANS (@lem7581678 A x s h1) (@lem7581682 A)). Qed.
Lemma lem7581684 {A : Type'} (x : A) (s : A -> Prop) : term257 A x s.
Proof. exact (fun h0 : term80 A x s => @lem7581683 A x s h0). Qed.
Lemma lem7581685 {A : Type'} (x : A) (s : A -> Prop) : term258 A x s.
Proof. exact (@lem7581475 A x s True). Qed.
Lemma lem7581686 {A : Type'} (x : A) (s : A -> Prop) : (term183 A x s) = (term259 A x s).
Proof. exact (@lem7581685 A x s (@lem7581684 A x s)). Qed.
Lemma lem7581688 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7581689 {A : Type'} (x : A) (s : A -> Prop) : (term259 A x s) = True.
Proof. exact (@lem7581688 (term80 A x s)). Qed.
Lemma lem7581690 {A : Type'} (x : A) (s : A -> Prop) : (term183 A x s) = True.
Proof. exact (TRANS (@lem7581686 A x s) (@lem7581689 A x s)). Qed.
Lemma lem7581691 {A : Type'} (x : A) : (term184 A x) = (term260 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7581690 A x s)). Qed.
Lemma lem7581692 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7581693 {A : Type'} (x : A) : (term185 A x) = (term261 A).
Proof. exact (MK_COMB (@lem7581692 A) (@lem7581691 A x)). Qed.
Lemma lem7581695 {A : Type'} (t : Prop) : (term126 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7581696 {A : Type'} (t : Prop) : (term262 A t) = t.
Proof. exact (@lem7581695 (A -> Prop) t). Qed.
Lemma lem7581697 {A : Type'} : (term261 A) = True.
Proof. exact (@lem7581696 A True). Qed.
Lemma lem7581698 {A : Type'} (x : A) : (term185 A x) = True.
Proof. exact (TRANS (@lem7581693 A x) (@lem7581697 A)). Qed.
Lemma lem7581699 {A : Type'} : (term186 A) = (term251 A).
Proof. exact (fun_ext (fun x : A => @lem7581698 A x)). Qed.
Lemma lem7581700 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7581701 {A : Type'} : (term187 A) = (term252 A).
Proof. exact (MK_COMB (@lem7581700 A) (@lem7581699 A)). Qed.
Lemma lem7581703 {A : Type'} (t : Prop) : (term126 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7581704 {A : Type'} (t : Prop) : (term126 A t) = t.
Proof. exact (@lem7581703 A t). Qed.
Lemma lem7581705 {A : Type'} : (term252 A) = True.
Proof. exact (@lem7581704 A True). Qed.
Lemma lem7581706 {A : Type'} : (term187 A) = True.
Proof. exact (TRANS (@lem7581701 A) (@lem7581705 A)). Qed.
Lemma lem7581707 {A : Type'} : True = (term187 A).
Proof. exact (SYM (@lem7581706 A)). Qed.
Lemma lem7581708 {A : Type'} : term187 A.
Proof. exact (EQ_MP (@lem7581707 A) (@lem0)). Qed.
Lemma lem7581709 {A : Type'} : term96 A.
Proof. exact (EQ_MP (@lem7581356 A) (@lem7581708 A)). Qed.
Lemma lem7581710 {A : Type'} : term68 A.
Proof. exact (@lem7577699 A (@lem7581709 A)). Qed.
Lemma lem7581711 {A : Type'} : term67 A.
Proof. exact (EQ_MP (@lem7577666 A) (@lem7581710 A)). Qed.
