Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_CROSS_EQ_term_abbrevs.
Require Import CROSS_EMPTY_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import EXISTS_PAIR_THM_spec.
Require Import FINITE_CROSS_spec.
Require Import FINITE_EMPTY_spec.
Require Import FINITE_IMAGE_spec.
Require Import FINITE_SUBSET_spec.
Require Import IN_CROSS_spec.
Require Import IN_IMAGE_spec.
Require Import SUBSET_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16433_spec.
Require Import thm16434_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm1831_spec.
Require Import thm1833_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1855_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm32_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm48213_spec.
Require Import thm48214_spec.
Require Import thm48219_spec.
Require Import thm48220_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Require Import thm951_spec.
Require Import thm952_spec.
Lemma lem4327457 {_103718 _103721 : Type'} (x : _103718) : term0 _103718 _103721 x.
Proof. exact (@lem4325365 _103718 _103721 x). Qed.
Lemma lem4327458 {_103718 _103721 : Type'} (x : _103718) : (term0 _103718 _103721 x) = (term1 _103718 _103721 x).
Proof. exact (eq_refl (term0 _103718 _103721 x)). Qed.
Lemma lem4327459 {_103718 _103721 : Type'} (x : _103718) : term1 _103718 _103721 x.
Proof. exact (EQ_MP (@lem4327458 _103718 _103721 x) (@lem4327457 _103718 _103721 x)). Qed.
Lemma lem4327460 {_103718 _103721 : Type'} (x : _103718) (y : _103721) : term2 _103718 _103721 x y.
Proof. exact (@lem4327459 _103718 _103721 x y). Qed.
Lemma lem4327461 {_103718 _103721 : Type'} (x : _103718) (y : _103721) : (term2 _103718 _103721 x y) = (term3 _103718 _103721 x y).
Proof. exact (eq_refl (term2 _103718 _103721 x y)). Qed.
Lemma lem4327462 {_103718 _103721 : Type'} (x : _103718) (y : _103721) : term3 _103718 _103721 x y.
Proof. exact (EQ_MP (@lem4327461 _103718 _103721 x y) (@lem4327460 _103718 _103721 x y)). Qed.
Lemma lem4327463 {_103718 _103721 : Type'} (x : _103718) (y : _103721) (s : _103718 -> Prop) : term4 _103718 _103721 x y s.
Proof. exact (@lem4327462 _103718 _103721 x y s). Qed.
Lemma lem4327464 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) : (term4 _103718 _103721 x y s) = (term5 _103718 _103721 x s y).
Proof. exact (eq_refl (term4 _103718 _103721 x y s)). Qed.
Lemma lem4327465 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) : term5 _103718 _103721 x s y.
Proof. exact (EQ_MP (@lem4327464 _103718 _103721 x s y) (@lem4327463 _103718 _103721 x y s)). Qed.
Lemma lem4327466 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : term6 _103718 _103721 x s y t.
Proof. exact (@lem4327465 _103718 _103721 x s y t). Qed.
Lemma lem4327467 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term6 _103718 _103721 x s y t) = ((term7 _103718 _103721 x y s t) = (term8 _103718 _103721 x s y t)).
Proof. exact (eq_refl (term6 _103718 _103721 x s y t)). Qed.
Lemma lem4327469 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : term9 _5131 _5132 P.
Proof. exact (@lem51006 _5131 _5132 P). Qed.
Lemma lem4327470 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term9 _5131 _5132 P) = ((term10 _5131 _5132 P) = (term11 _5131 _5132 P)).
Proof. exact (eq_refl (term9 _5131 _5132 P)). Qed.
Lemma lem4327472 {A B : Type'} (y : B) : term12 A B y.
Proof. exact (@lem3206070 A B y). Qed.
Lemma lem4327473 {A B : Type'} (y : B) : (term12 A B y) = (term13 A B y).
Proof. exact (eq_refl (term12 A B y)). Qed.
Lemma lem4327474 {A B : Type'} (y : B) : term13 A B y.
Proof. exact (EQ_MP (@lem4327473 A B y) (@lem4327472 A B y)). Qed.
Lemma lem4327475 {A B : Type'} (y : B) (s : A -> Prop) : term14 A B y s.
Proof. exact (@lem4327474 A B y s). Qed.
Lemma lem4327476 {A B : Type'} (y : B) (s : A -> Prop) : (term14 A B y s) = (term15 A B y s).
Proof. exact (eq_refl (term14 A B y s)). Qed.
Lemma lem4327477 {A B : Type'} (y : B) (s : A -> Prop) : term15 A B y s.
Proof. exact (EQ_MP (@lem4327476 A B y s) (@lem4327475 A B y s)). Qed.
Lemma lem4327478 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) : term16 A B y s f.
Proof. exact (@lem4327477 A B y s f). Qed.
Lemma lem4327479 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term16 A B y s f) = ((term17 A B y f s) = (term18 A B y f s)).
Proof. exact (eq_refl (term16 A B y s f)). Qed.
Lemma lem4327481 {A : Type'} (s : A -> Prop) : term19 A s.
Proof. exact (@lem3194148 A s). Qed.
Lemma lem4327482 {A : Type'} (s : A -> Prop) : (term19 A s) = (term20 A s).
Proof. exact (eq_refl (term19 A s)). Qed.
Lemma lem4327483 {A : Type'} (s : A -> Prop) : term20 A s.
Proof. exact (EQ_MP (@lem4327482 A s) (@lem4327481 A s)). Qed.
Lemma lem4327484 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term21 A s t.
Proof. exact (@lem4327483 A s t). Qed.
Lemma lem4327485 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term21 A s t) = ((@SUBSET A s t) = (term22 A s t)).
Proof. exact (eq_refl (term21 A s t)). Qed.
Lemma lem4327496 (q : Prop) (p : Prop) (r : Prop) : (term23 p q r) = (term24 q p r).
Proof. exact (EQ_MP (@lem952 q p r) (@lem951 p q r)). Qed.
Lemma lem4327497 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term25 A t s) = (term26 A t s).
Proof. exact (@lem4327496 (@SUBSET A s t) (@FINITE A t) (@FINITE A s)). Qed.
Lemma lem4327502 {A : Type'} (s : A -> Prop) : (term27 A s) = (term28 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4327497 A t s)). Qed.
Lemma lem4327503 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4327504 {A : Type'} (s : A -> Prop) : (term29 A s) = (term30 A s).
Proof. exact (MK_COMB (@lem4327503 A) (@lem4327502 A s)). Qed.
Lemma lem4327509 {A : Type'} : (term31 A) = (term32 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4327504 A s)). Qed.
Lemma lem4327510 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4327511 {A : Type'} : (term33 A) = (term34 A).
Proof. exact (MK_COMB (@lem4327510 A) (@lem4327509 A)). Qed.
Lemma lem4327516 {A : Type'} : term34 A.
Proof. exact (EQ_MP (@lem4327511 A) (@lem3599924 A)). Qed.
Lemma lem4327517 {A : Type'} (h1 : term34 A) : term34 A.
Proof. exact (h1). Qed.
Lemma lem4327518 {A : Type'} (s : A -> Prop) (h1 : term34 A) : term35 A s.
Proof. exact (@lem4327517 A h1 s). Qed.
Lemma lem4327519 {A : Type'} (s : A -> Prop) : (term35 A s) = (term30 A s).
Proof. exact (eq_refl (term35 A s)). Qed.
Lemma lem4327520 {A : Type'} (s : A -> Prop) (h1 : term34 A) : term30 A s.
Proof. exact (EQ_MP (@lem4327519 A s) (@lem4327518 A s h1)). Qed.
Lemma lem4327521 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term34 A) : term36 A s t.
Proof. exact (@lem4327520 A s h1 t). Qed.
Lemma lem4327522 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term36 A s t) = (term26 A t s).
Proof. exact (eq_refl (term36 A s t)). Qed.
Lemma lem4327523 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term34 A) : term26 A t s.
Proof. exact (EQ_MP (@lem4327522 A t s) (@lem4327521 A s t h1)). Qed.
Lemma lem4327524 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : @SUBSET A s t) : @SUBSET A s t.
Proof. exact (h1). Qed.
Lemma lem4327525 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term34 A) (h2 : @SUBSET A s t) : term37 A t s.
Proof. exact (@lem4327523 A t s h1 (@lem4327524 A s t h2)). Qed.
Lemma lem4327526 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : @SUBSET A s t) : term38 A t s.
Proof. exact (fun h0 : term34 A => @lem4327525 A s t h0 h1). Qed.
Lemma lem4327527 {A : Type'} (h1 : term34 A) : term34 A.
Proof. exact (h1). Qed.
Lemma lem4327528 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term34 A) (h2 : @SUBSET A s t) : term37 A t s.
Proof. exact (@lem4327526 A s t h2 (@lem4327527 A h1)). Qed.
Lemma lem4327529 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term34 A) : term26 A t s.
Proof. exact (fun h0 : @SUBSET A s t => @lem4327528 A s t h1 h0). Qed.
Lemma lem4327530 {A : Type'} (t : A -> Prop) (h1 : term34 A) : term39 A t.
Proof. exact (fun s : A -> Prop => @lem4327529 A t s h1). Qed.
Lemma lem4327531 {A : Type'} (h1 : term34 A) : term40 A.
Proof. exact (fun t : A -> Prop => @lem4327530 A t h1). Qed.
Lemma lem4327532 {A : Type'} : term41 A.
Proof. exact (fun h0 : term34 A => @lem4327531 A h0). Qed.
Lemma lem4327533 {A : Type'} : term40 A.
Proof. exact (@lem4327532 A (@lem4327516 A)). Qed.
Lemma lem4327534 {A : Type'} (t : A -> Prop) : term42 A t.
Proof. exact (@lem4327533 A t). Qed.
Lemma lem4327535 {A : Type'} (t : A -> Prop) : (term42 A t) = (term39 A t).
Proof. exact (eq_refl (term42 A t)). Qed.
Lemma lem4327536 {A : Type'} (t : A -> Prop) : term39 A t.
Proof. exact (EQ_MP (@lem4327535 A t) (@lem4327534 A t)). Qed.
Lemma lem4327537 {A : Type'} (t : A -> Prop) (s : A -> Prop) : term43 A t s.
Proof. exact (@lem4327536 A t s). Qed.
Lemma lem4327538 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term43 A t s) = (term26 A t s).
Proof. exact (eq_refl (term43 A t s)). Qed.
Lemma lem4327540 {A B : Type'} : term44 A B.
Proof. exact (@lem3615104 (prod A B) B). Qed.
Lemma lem4327541 {A B : Type'} : term45 A B.
Proof. exact (@lem4327540 A B (@snd A B)). Qed.
Lemma lem4327542 {A B : Type'} : (term45 A B) = (term46 A B).
Proof. exact (eq_refl (term45 A B)). Qed.
Lemma lem4327543 {A B : Type'} : term46 A B.
Proof. exact (EQ_MP (@lem4327542 A B) (@lem4327541 A B)). Qed.
Lemma lem4327544 {A B : Type'} (s : type1210 A B) : term47 A B s.
Proof. exact (@lem4327543 A B s). Qed.
Lemma lem4327545 {A B : Type'} (s : type1210 A B) : (term47 A B s) = (term48 A B s).
Proof. exact (eq_refl (term47 A B s)). Qed.
Lemma lem4327547 {A B : Type'} : term49 A B.
Proof. exact (@lem3615104 (prod A B) A). Qed.
Lemma lem4327548 {A B : Type'} : term50 A B.
Proof. exact (@lem4327547 A B (@fst A B)). Qed.
Lemma lem4327549 {A B : Type'} : (term50 A B) = (term51 A B).
Proof. exact (eq_refl (term50 A B)). Qed.
Lemma lem4327550 {A B : Type'} : term51 A B.
Proof. exact (EQ_MP (@lem4327549 A B) (@lem4327548 A B)). Qed.
Lemma lem4327551 {A B : Type'} (s : type1210 A B) : term52 A B s.
Proof. exact (@lem4327550 A B s). Qed.
Lemma lem4327552 {A B : Type'} (s : type1210 A B) : (term52 A B s) = (term53 A B s).
Proof. exact (eq_refl (term52 A B s)). Qed.
Lemma lem4327554 {_103774 _103776 : Type'} (s : _103774 -> Prop) : term54 _103774 _103776 s.
Proof. exact (@lem4325576 _103774 _103776 s). Qed.
Lemma lem4327555 {_103774 _103776 : Type'} (s : _103774 -> Prop) : (term54 _103774 _103776 s) = (term55 _103774 _103776 s).
Proof. exact (eq_refl (term54 _103774 _103776 s)). Qed.
Lemma lem4327556 {_103774 _103776 : Type'} (s : _103774 -> Prop) : term55 _103774 _103776 s.
Proof. exact (EQ_MP (@lem4327555 _103774 _103776 s) (@lem4327554 _103774 _103776 s)). Qed.
Lemma lem4327557 {_103774 _103776 : Type'} (s : _103774 -> Prop) (t : _103776 -> Prop) : term56 _103774 _103776 s t.
Proof. exact (@lem4327556 _103774 _103776 s t). Qed.
Lemma lem4327558 {_103774 _103776 : Type'} (s : _103774 -> Prop) (t : _103776 -> Prop) : (term56 _103774 _103776 s t) = (term57 _103774 _103776 s t).
Proof. exact (eq_refl (term56 _103774 _103776 s t)). Qed.
Lemma lem4327559 {_103774 _103776 : Type'} (s : _103774 -> Prop) (t : _103776 -> Prop) : term57 _103774 _103776 s t.
Proof. exact (EQ_MP (@lem4327558 _103774 _103776 s t) (@lem4327557 _103774 _103776 s t)). Qed.
Lemma lem4327560 {_103774 _103776 : Type'} (s : _103774 -> Prop) (t : _103776 -> Prop) : (term57 _103774 _103776 s t) = ((term57 _103774 _103776 s t) = True).
Proof. exact (@lem7 (term57 _103774 _103776 s t)). Qed.
Lemma lem4327562 {B : Type'} (t : B -> Prop) : term58 B t.
Proof. exact (@lem9784 (t = (@EMPTY B))). Qed.
Lemma lem4327563 {B : Type'} (t : B -> Prop) : (term58 B t) = (term59 B t).
Proof. exact (eq_refl (term58 B t)). Qed.
Lemma lem4327564 {B : Type'} (t : B -> Prop) : term59 B t.
Proof. exact (EQ_MP (@lem4327563 B t) (@lem4327562 B t)). Qed.
Lemma lem4327566 {B : Type'} (t : B -> Prop) (h1 : term60 B t) : term60 B t.
Proof. exact (h1). Qed.
Lemma lem4327567 {A : Type'} (s : A -> Prop) : term58 A s.
Proof. exact (@lem9784 (s = (@EMPTY A))). Qed.
Lemma lem4327568 {A : Type'} (s : A -> Prop) : (term58 A s) = (term59 A s).
Proof. exact (eq_refl (term58 A s)). Qed.
Lemma lem4327569 {A : Type'} (s : A -> Prop) : term59 A s.
Proof. exact (EQ_MP (@lem4327568 A s) (@lem4327567 A s)). Qed.
Lemma lem4327571 {A : Type'} (s : A -> Prop) (h1 : term60 A s) : term60 A s.
Proof. exact (h1). Qed.
Lemma lem4327572 {_92140 : Type'} : (@FINITE _92140 (@EMPTY _92140)) = ((@FINITE _92140 (@EMPTY _92140)) = True).
Proof. exact (@lem7 (@FINITE _92140 (@EMPTY _92140))). Qed.
Lemma lem4327574 {_103872 B : Type'} : term61 _103872 B.
Proof. exact (proj2 (@lem4327078 Prop _103872 Prop B)). Qed.
Lemma lem4327575 {_103872 B : Type'} (t : B -> Prop) : term62 _103872 B t.
Proof. exact (@lem4327574 _103872 B t). Qed.
Lemma lem4327576 {_103872 B : Type'} (t : B -> Prop) : (term62 _103872 B t) = ((@CROSS B _103872 (@EMPTY _103872) t) = (@EMPTY (prod _103872 B))).
Proof. exact (eq_refl (term62 _103872 B t)). Qed.
Lemma lem4327585 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : s = (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem4327586 {A B : Type'} : (@CROSS B A) = (@CROSS B A).
Proof. exact (eq_refl (@CROSS B A)). Qed.
Lemma lem4327587 {A B : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : (@CROSS B A s) = (@CROSS B A (@EMPTY A)).
Proof. exact (MK_COMB (@lem4327586 A B) (@lem4327585 A s h1)). Qed.
Lemma lem4327588 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4327589 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : s = (@EMPTY A)) : (@CROSS B A s t) = (@CROSS B A (@EMPTY A) t).
Proof. exact (MK_COMB (@lem4327587 A B s h1) (@lem4327588 B t)). Qed.
Lemma lem4327591 {_103872 B : Type'} (t : B -> Prop) : (@CROSS B _103872 (@EMPTY _103872) t) = (@EMPTY (prod _103872 B)).
Proof. exact (EQ_MP (@lem4327576 _103872 B t) (@lem4327575 _103872 B t)). Qed.
Lemma lem4327592 {A B : Type'} (t : B -> Prop) : (@CROSS B A (@EMPTY A) t) = (@EMPTY (prod A B)).
Proof. exact (@lem4327591 A B t). Qed.
Lemma lem4327593 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : s = (@EMPTY A)) : (@CROSS B A s t) = (@EMPTY (prod A B)).
Proof. exact (TRANS (@lem4327589 A B t s h1) (@lem4327592 A B t)). Qed.
Lemma lem4327594 {A B : Type'} : (@FINITE (prod A B)) = (@FINITE (prod A B)).
Proof. exact (eq_refl (@FINITE (prod A B))). Qed.
Lemma lem4327595 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term63 A B s t) = (@FINITE (prod A B) (@EMPTY (prod A B))).
Proof. exact (MK_COMB (@lem4327594 A B) (@lem4327593 A B t s h1)). Qed.
Lemma lem4327597 {_92140 : Type'} : (@FINITE _92140 (@EMPTY _92140)) = True.
Proof. exact (EQ_MP (@lem4327572 _92140) (@lem3596285 _92140)). Qed.
Lemma lem4327598 {A B : Type'} : (@FINITE (prod A B) (@EMPTY (prod A B))) = True.
Proof. exact (@lem4327597 (prod A B)). Qed.
Lemma lem4327599 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term63 A B s t) = True.
Proof. exact (TRANS (@lem4327595 A B t s h1) (@lem4327598 A B)). Qed.
Lemma lem4327600 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4327601 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term64 A B s t) = (@eq Prop True).
Proof. exact (MK_COMB (@lem4327600) (@lem4327599 A B t s h1)). Qed.
Lemma lem4327607 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : s = (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem4327608 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4327609 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : (@eq (A -> Prop) s) = (@eq (A -> Prop) (@EMPTY A)).
Proof. exact (MK_COMB (@lem4327608 A) (@lem4327607 A s h1)). Qed.
Lemma lem4327610 {A : Type'} : (@EMPTY A) = (@EMPTY A).
Proof. exact (eq_refl (@EMPTY A)). Qed.
Lemma lem4327611 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : (s = (@EMPTY A)) = ((@EMPTY A) = (@EMPTY A)).
Proof. exact (MK_COMB (@lem4327609 A s h1) (@lem4327610 A)). Qed.
Lemma lem4327613 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4327614 {A : Type'} (x : A -> Prop) : (x = x) = True.
Proof. exact (@lem4327613 (A -> Prop) x). Qed.
Lemma lem4327615 {A : Type'} : ((@EMPTY A) = (@EMPTY A)) = True.
Proof. exact (@lem4327614 A (@EMPTY A)). Qed.
Lemma lem4327616 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : (s = (@EMPTY A)) = True.
Proof. exact (TRANS (@lem4327611 A s h1) (@lem4327615 A)). Qed.
Lemma lem4327617 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4327618 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term65 A s) = (or True).
Proof. exact (MK_COMB (@lem4327617) (@lem4327616 A s h1)). Qed.
Lemma lem4327626 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : s = (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem4327627 {A : Type'} : (@FINITE A) = (@FINITE A).
Proof. exact (eq_refl (@FINITE A)). Qed.
Lemma lem4327628 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : (@FINITE A s) = (@FINITE A (@EMPTY A)).
Proof. exact (MK_COMB (@lem4327627 A) (@lem4327626 A s h1)). Qed.
Lemma lem4327630 {_92140 : Type'} : (@FINITE _92140 (@EMPTY _92140)) = True.
Proof. exact (EQ_MP (@lem4327572 _92140) (@lem3596285 _92140)). Qed.
Lemma lem4327631 {A : Type'} : (@FINITE A (@EMPTY A)) = True.
Proof. exact (@lem4327630 A). Qed.
Lemma lem4327632 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : (@FINITE A s) = True.
Proof. exact (TRANS (@lem4327628 A s h1) (@lem4327631 A)). Qed.
Lemma lem4327633 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4327634 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term66 A s) = (and True).
Proof. exact (MK_COMB (@lem4327633) (@lem4327632 A s h1)). Qed.
Lemma lem4327635 {B : Type'} (t : B -> Prop) : (@FINITE B t) = (@FINITE B t).
Proof. exact (eq_refl (@FINITE B t)). Qed.
Lemma lem4327636 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term67 A B s t) = (term68 B t).
Proof. exact (MK_COMB (@lem4327634 A s h1) (@lem4327635 B t)). Qed.
Lemma lem4327638 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4327639 {B : Type'} (t : B -> Prop) : (term68 B t) = (@FINITE B t).
Proof. exact (@lem4327638 (@FINITE B t)). Qed.
Lemma lem4327640 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term67 A B s t) = (@FINITE B t).
Proof. exact (TRANS (@lem4327636 A B t s h1) (@lem4327639 B t)). Qed.
Lemma lem4327641 {B : Type'} (t : B -> Prop) : (term65 B t) = (term65 B t).
Proof. exact (eq_refl (term65 B t)). Qed.
Lemma lem4327642 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term69 A B s t) = (term70 B t).
Proof. exact (MK_COMB (@lem4327641 B t) (@lem4327640 A B t s h1)). Qed.
Lemma lem4327645 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term71 A B s t) = (term72 B t).
Proof. exact (MK_COMB (@lem4327618 A s h1) (@lem4327642 A B t s h1)). Qed.
Lemma lem4327647 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem4327648 {B : Type'} (t : B -> Prop) : (term72 B t) = True.
Proof. exact (@lem4327647 (term70 B t)). Qed.
Lemma lem4327649 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term71 A B s t) = True.
Proof. exact (TRANS (@lem4327645 A B t s h1) (@lem4327648 B t)). Qed.
Lemma lem4327650 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : s = (@EMPTY A)) : ((term63 A B s t) = (term71 A B s t)) = (True = True).
Proof. exact (MK_COMB (@lem4327601 A B t s h1) (@lem4327649 A B t s h1)). Qed.
Lemma lem4327652 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem4327653 : (True = True) = True.
Proof. exact (@lem4327652 True). Qed.
Lemma lem4327654 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : s = (@EMPTY A)) : ((term63 A B s t) = (term71 A B s t)) = True.
Proof. exact (TRANS (@lem4327650 A B t s h1) (@lem4327653)). Qed.
Lemma lem4327655 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : s = (@EMPTY A)) : True = ((term63 A B s t) = (term71 A B s t)).
Proof. exact (SYM (@lem4327654 A B t s h1)). Qed.
Lemma lem4327656 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term63 A B s t) = (term71 A B s t).
Proof. exact (EQ_MP (@lem4327655 A B t s h1) (@lem0)). Qed.
Lemma lem4327667 {A : Type'} (s : A -> Prop) : term73 A s.
Proof. exact (@lem82 (s = (@EMPTY A))). Qed.
Lemma lem4327685 {A : Type'} (s : A -> Prop) (h1 : term60 A s) : (s = (@EMPTY A)) = False.
Proof. exact (@lem4327667 A s (@lem4327571 A s h1)). Qed.
Lemma lem4327686 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4327687 {A : Type'} (s : A -> Prop) (h1 : term60 A s) : (term65 A s) = (or False).
Proof. exact (MK_COMB (@lem4327686) (@lem4327685 A s h1)). Qed.
Lemma lem4327694 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term69 A B s t) = (term69 A B s t).
Proof. exact (eq_refl (term69 A B s t)). Qed.
Lemma lem4327695 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term60 A s) : (term71 A B s t) = (term74 A B s t).
Proof. exact (MK_COMB (@lem4327687 A s h1) (@lem4327694 A B s t)). Qed.
Lemma lem4327697 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem4327698 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term74 A B s t) = (term69 A B s t).
Proof. exact (@lem4327697 (term69 A B s t)). Qed.
Lemma lem4327705 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term60 A s) : (term71 A B s t) = (term69 A B s t).
Proof. exact (TRANS (@lem4327695 A B t s h1) (@lem4327698 A B s t)). Qed.
Lemma lem4327706 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term64 A B s t) = (term64 A B s t).
Proof. exact (eq_refl (term64 A B s t)). Qed.
Lemma lem4327707 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term60 A s) : ((term63 A B s t) = (term71 A B s t)) = ((term63 A B s t) = (term69 A B s t)).
Proof. exact (MK_COMB (@lem4327706 A B s t) (@lem4327705 A B t s h1)). Qed.
Lemma lem4327710 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term60 A s) : ((term63 A B s t) = (term69 A B s t)) = ((term63 A B s t) = (term71 A B s t)).
Proof. exact (SYM (@lem4327707 A B t s h1)). Qed.
Lemma lem4327711 {_92140 : Type'} : (@FINITE _92140 (@EMPTY _92140)) = ((@FINITE _92140 (@EMPTY _92140)) = True).
Proof. exact (@lem7 (@FINITE _92140 (@EMPTY _92140))). Qed.
Lemma lem4327717 {_103859 A : Type'} : term75 _103859 A.
Proof. exact (proj1 (@lem4327078 _103859 Prop A Prop)). Qed.
Lemma lem4327718 {_103859 A : Type'} (s : A -> Prop) : term76 _103859 A s.
Proof. exact (@lem4327717 _103859 A s). Qed.
Lemma lem4327719 {_103859 A : Type'} (s : A -> Prop) : (term76 _103859 A s) = ((@CROSS _103859 A s (@EMPTY _103859)) = (@EMPTY (prod A _103859))).
Proof. exact (eq_refl (term76 _103859 A s)). Qed.
Lemma lem4327737 {B : Type'} (t : B -> Prop) (h1 : t = (@EMPTY B)) : t = (@EMPTY B).
Proof. exact (h1). Qed.
Lemma lem4327738 {A B : Type'} (s : A -> Prop) : (@CROSS B A s) = (@CROSS B A s).
Proof. exact (eq_refl (@CROSS B A s)). Qed.
Lemma lem4327739 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : t = (@EMPTY B)) : (@CROSS B A s t) = (@CROSS B A s (@EMPTY B)).
Proof. exact (MK_COMB (@lem4327738 A B s) (@lem4327737 B t h1)). Qed.
Lemma lem4327741 {_103859 A : Type'} (s : A -> Prop) : (@CROSS _103859 A s (@EMPTY _103859)) = (@EMPTY (prod A _103859)).
Proof. exact (EQ_MP (@lem4327719 _103859 A s) (@lem4327718 _103859 A s)). Qed.
Lemma lem4327742 {A B : Type'} (s : A -> Prop) : (@CROSS B A s (@EMPTY B)) = (@EMPTY (prod A B)).
Proof. exact (@lem4327741 B A s). Qed.
Lemma lem4327743 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : t = (@EMPTY B)) : (@CROSS B A s t) = (@EMPTY (prod A B)).
Proof. exact (TRANS (@lem4327739 A B s t h1) (@lem4327742 A B s)). Qed.
Lemma lem4327744 {A B : Type'} : (@FINITE (prod A B)) = (@FINITE (prod A B)).
Proof. exact (eq_refl (@FINITE (prod A B))). Qed.
Lemma lem4327745 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : t = (@EMPTY B)) : (term63 A B s t) = (@FINITE (prod A B) (@EMPTY (prod A B))).
Proof. exact (MK_COMB (@lem4327744 A B) (@lem4327743 A B s t h1)). Qed.
Lemma lem4327747 {_92140 : Type'} : (@FINITE _92140 (@EMPTY _92140)) = True.
Proof. exact (EQ_MP (@lem4327711 _92140) (@lem3596285 _92140)). Qed.
Lemma lem4327748 {A B : Type'} : (@FINITE (prod A B) (@EMPTY (prod A B))) = True.
Proof. exact (@lem4327747 (prod A B)). Qed.
Lemma lem4327749 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : t = (@EMPTY B)) : (term63 A B s t) = True.
Proof. exact (TRANS (@lem4327745 A B s t h1) (@lem4327748 A B)). Qed.
Lemma lem4327750 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4327751 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : t = (@EMPTY B)) : (term64 A B s t) = (@eq Prop True).
Proof. exact (MK_COMB (@lem4327750) (@lem4327749 A B s t h1)). Qed.
Lemma lem4327757 {B : Type'} (t : B -> Prop) (h1 : t = (@EMPTY B)) : t = (@EMPTY B).
Proof. exact (h1). Qed.
Lemma lem4327758 {B : Type'} : (@eq (B -> Prop)) = (@eq (B -> Prop)).
Proof. exact (eq_refl (@eq (B -> Prop))). Qed.
Lemma lem4327759 {B : Type'} (t : B -> Prop) (h1 : t = (@EMPTY B)) : (@eq (B -> Prop) t) = (@eq (B -> Prop) (@EMPTY B)).
Proof. exact (MK_COMB (@lem4327758 B) (@lem4327757 B t h1)). Qed.
Lemma lem4327760 {B : Type'} : (@EMPTY B) = (@EMPTY B).
Proof. exact (eq_refl (@EMPTY B)). Qed.
Lemma lem4327761 {B : Type'} (t : B -> Prop) (h1 : t = (@EMPTY B)) : (t = (@EMPTY B)) = ((@EMPTY B) = (@EMPTY B)).
Proof. exact (MK_COMB (@lem4327759 B t h1) (@lem4327760 B)). Qed.
Lemma lem4327763 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4327764 {B : Type'} (x : B -> Prop) : (x = x) = True.
Proof. exact (@lem4327763 (B -> Prop) x). Qed.
Lemma lem4327765 {B : Type'} : ((@EMPTY B) = (@EMPTY B)) = True.
Proof. exact (@lem4327764 B (@EMPTY B)). Qed.
Lemma lem4327766 {B : Type'} (t : B -> Prop) (h1 : t = (@EMPTY B)) : (t = (@EMPTY B)) = True.
Proof. exact (TRANS (@lem4327761 B t h1) (@lem4327765 B)). Qed.
Lemma lem4327767 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4327768 {B : Type'} (t : B -> Prop) (h1 : t = (@EMPTY B)) : (term65 B t) = (or True).
Proof. exact (MK_COMB (@lem4327767) (@lem4327766 B t h1)). Qed.
Lemma lem4327772 {B : Type'} (t : B -> Prop) (h1 : t = (@EMPTY B)) : t = (@EMPTY B).
Proof. exact (h1). Qed.
Lemma lem4327773 {B : Type'} : (@FINITE B) = (@FINITE B).
Proof. exact (eq_refl (@FINITE B)). Qed.
Lemma lem4327774 {B : Type'} (t : B -> Prop) (h1 : t = (@EMPTY B)) : (@FINITE B t) = (@FINITE B (@EMPTY B)).
Proof. exact (MK_COMB (@lem4327773 B) (@lem4327772 B t h1)). Qed.
Lemma lem4327776 {_92140 : Type'} : (@FINITE _92140 (@EMPTY _92140)) = True.
Proof. exact (EQ_MP (@lem4327711 _92140) (@lem3596285 _92140)). Qed.
Lemma lem4327777 {B : Type'} : (@FINITE B (@EMPTY B)) = True.
Proof. exact (@lem4327776 B). Qed.
Lemma lem4327778 {B : Type'} (t : B -> Prop) (h1 : t = (@EMPTY B)) : (@FINITE B t) = True.
Proof. exact (TRANS (@lem4327774 B t h1) (@lem4327777 B)). Qed.
Lemma lem4327779 {A : Type'} (s : A -> Prop) : (term66 A s) = (term66 A s).
Proof. exact (eq_refl (term66 A s)). Qed.
Lemma lem4327780 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : t = (@EMPTY B)) : (term67 A B s t) = (term77 A s).
Proof. exact (MK_COMB (@lem4327779 A s) (@lem4327778 B t h1)). Qed.
Lemma lem4327782 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem4327783 {A : Type'} (s : A -> Prop) : (term77 A s) = (@FINITE A s).
Proof. exact (@lem4327782 (@FINITE A s)). Qed.
Lemma lem4327784 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : t = (@EMPTY B)) : (term67 A B s t) = (@FINITE A s).
Proof. exact (TRANS (@lem4327780 A B s t h1) (@lem4327783 A s)). Qed.
Lemma lem4327785 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : t = (@EMPTY B)) : (term69 A B s t) = (term78 A s).
Proof. exact (MK_COMB (@lem4327768 B t h1) (@lem4327784 A B s t h1)). Qed.
Lemma lem4327787 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem4327788 {A : Type'} (s : A -> Prop) : (term78 A s) = True.
Proof. exact (@lem4327787 (@FINITE A s)). Qed.
Lemma lem4327789 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : t = (@EMPTY B)) : (term69 A B s t) = True.
Proof. exact (TRANS (@lem4327785 A B s t h1) (@lem4327788 A s)). Qed.
Lemma lem4327790 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : t = (@EMPTY B)) : ((term63 A B s t) = (term69 A B s t)) = (True = True).
Proof. exact (MK_COMB (@lem4327751 A B s t h1) (@lem4327789 A B s t h1)). Qed.
Lemma lem4327792 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem4327793 : (True = True) = True.
Proof. exact (@lem4327792 True). Qed.
Lemma lem4327794 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : t = (@EMPTY B)) : ((term63 A B s t) = (term69 A B s t)) = True.
Proof. exact (TRANS (@lem4327790 A B s t h1) (@lem4327793)). Qed.
Lemma lem4327795 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : t = (@EMPTY B)) : True = ((term63 A B s t) = (term69 A B s t)).
Proof. exact (SYM (@lem4327794 A B s t h1)). Qed.
Lemma lem4327796 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : t = (@EMPTY B)) : (term63 A B s t) = (term69 A B s t).
Proof. exact (EQ_MP (@lem4327795 A B s t h1) (@lem0)). Qed.
Lemma lem4327820 {B : Type'} (t : B -> Prop) : term73 B t.
Proof. exact (@lem82 (t = (@EMPTY B))). Qed.
Lemma lem4327838 {B : Type'} (t : B -> Prop) (h1 : term60 B t) : (t = (@EMPTY B)) = False.
Proof. exact (@lem4327820 B t (@lem4327566 B t h1)). Qed.
Lemma lem4327839 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4327840 {B : Type'} (t : B -> Prop) (h1 : term60 B t) : (term65 B t) = (or False).
Proof. exact (MK_COMB (@lem4327839) (@lem4327838 B t h1)). Qed.
Lemma lem4327843 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term67 A B s t) = (term67 A B s t).
Proof. exact (eq_refl (term67 A B s t)). Qed.
Lemma lem4327844 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term60 B t) : (term69 A B s t) = (term79 A B s t).
Proof. exact (MK_COMB (@lem4327840 B t h1) (@lem4327843 A B s t)). Qed.
Lemma lem4327846 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem4327847 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term79 A B s t) = (term67 A B s t).
Proof. exact (@lem4327846 (term67 A B s t)). Qed.
Lemma lem4327850 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term60 B t) : (term69 A B s t) = (term67 A B s t).
Proof. exact (TRANS (@lem4327844 A B s t h1) (@lem4327847 A B s t)). Qed.
Lemma lem4327851 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term64 A B s t) = (term64 A B s t).
Proof. exact (eq_refl (term64 A B s t)). Qed.
Lemma lem4327852 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term60 B t) : ((term63 A B s t) = (term69 A B s t)) = ((term63 A B s t) = (term67 A B s t)).
Proof. exact (MK_COMB (@lem4327851 A B s t) (@lem4327850 A B s t h1)). Qed.
Lemma lem4327855 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term60 B t) : ((term63 A B s t) = (term67 A B s t)) = ((term63 A B s t) = (term69 A B s t)).
Proof. exact (SYM (@lem4327852 A B s t h1)). Qed.
Lemma lem4327863 {_103774 _103776 : Type'} (s : _103774 -> Prop) (t : _103776 -> Prop) : (term57 _103774 _103776 s t) = True.
Proof. exact (EQ_MP (@lem4327560 _103774 _103776 s t) (@lem4327559 _103774 _103776 s t)). Qed.
Lemma lem4327864 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term57 A B s t) = True.
Proof. exact (@lem4327863 A B s t). Qed.
Lemma lem4327865 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : True = (term57 A B s t).
Proof. exact (SYM (@lem4327864 A B s t)). Qed.
Lemma lem4327866 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term57 A B s t.
Proof. exact (EQ_MP (@lem4327865 A B s t) (@lem0)). Qed.
Lemma lem4327867 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term63 A B s t) : term63 A B s t.
Proof. exact (h1). Qed.
Lemma lem4327869 {A B : Type'} (s : type1210 A B) : term53 A B s.
Proof. exact (EQ_MP (@lem4327552 A B s) (@lem4327551 A B s)). Qed.
Lemma lem4327870 {A B : Type'} (s : type1210 A B) : term53 A B s.
Proof. exact (@lem4327869 A B s). Qed.
Lemma lem4327871 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term80 A B s t.
Proof. exact (@lem4327870 A B (@CROSS B A s t)). Qed.
Lemma lem4327872 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term63 A B s t) : term81 A B s t.
Proof. exact (@lem4327871 A B s t (@lem4327867 A B s t h1)). Qed.
Lemma lem4327874 {A B : Type'} (s : type1210 A B) : term48 A B s.
Proof. exact (EQ_MP (@lem4327545 A B s) (@lem4327544 A B s)). Qed.
Lemma lem4327875 {A B : Type'} (s : type1210 A B) : term48 A B s.
Proof. exact (@lem4327874 A B s). Qed.
Lemma lem4327876 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term82 A B s t.
Proof. exact (@lem4327875 A B (@CROSS B A s t)). Qed.
Lemma lem4327877 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term63 A B s t) : term83 A B s t.
Proof. exact (@lem4327876 A B s t (@lem4327867 A B s t h1)). Qed.
Lemma lem4327879 {A : Type'} (t : A -> Prop) (s : A -> Prop) : term26 A t s.
Proof. exact (EQ_MP (@lem4327538 A t s) (@lem4327537 A t s)). Qed.
Lemma lem4327880 {A : Type'} (t : A -> Prop) (s : A -> Prop) : term26 A t s.
Proof. exact (@lem4327879 A t s). Qed.
Lemma lem4327881 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : term84 A B t s.
Proof. exact (@lem4327880 A (term85 A B s t) s). Qed.
Lemma lem4327883 {A : Type'} (t : A -> Prop) (s : A -> Prop) : term26 A t s.
Proof. exact (EQ_MP (@lem4327538 A t s) (@lem4327537 A t s)). Qed.
Lemma lem4327884 {B : Type'} (t : B -> Prop) (s : B -> Prop) : term26 B t s.
Proof. exact (@lem4327883 B t s). Qed.
Lemma lem4327885 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term86 A B s t.
Proof. exact (@lem4327884 B (term87 A B s t) t). Qed.
Lemma lem4327887 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term22 A s t).
Proof. exact (EQ_MP (@lem4327485 A s t) (@lem4327484 A s t)). Qed.
Lemma lem4327888 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term22 A s t).
Proof. exact (@lem4327887 A s t). Qed.
Lemma lem4327889 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term88 A B s t) = (term89 A B s t).
Proof. exact (@lem4327888 A s (term85 A B s t)). Qed.
Lemma lem4327897 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term17 A B y f s) = (term18 A B y f s).
Proof. exact (EQ_MP (@lem4327479 A B y f s) (@lem4327478 A B y s f)). Qed.
Lemma lem4327898 {A B : Type'} (y : A) (f : type1207 A B) (s : type1210 A B) : (term90 A B y f s) = (term91 A B y f s).
Proof. exact (@lem4327897 (prod A B) A y f s). Qed.
Lemma lem4327899 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) : (term92 A B x s t) = (term93 A B x s t).
Proof. exact (@lem4327898 A B x (@fst A B) (@CROSS B A s t)). Qed.
Lemma lem4327905 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term10 _5131 _5132 P) = (term11 _5131 _5132 P).
Proof. exact (EQ_MP (@lem4327470 _5131 _5132 P) (@lem4327469 _5131 _5132 P)). Qed.
Lemma lem4327906 {A B : Type'} (P : type1210 A B) : (term94 A B P) = (term95 A B P).
Proof. exact (@lem4327905 B A P). Qed.
Lemma lem4327907 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) : (term96 A B x s t) = (term97 A B x s t).
Proof. exact (@lem4327906 A B (term98 A B x s t)). Qed.
Lemma lem4327908 {A B : Type'} (x : A) (x' : prod A B) (s : A -> Prop) (t : B -> Prop) : (term99 A B x s t x') = (term100 A B x x' s t).
Proof. exact (eq_refl (term99 A B x s t x')). Qed.
Lemma lem4327909 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) : (term101 A B x s t) = (term98 A B x s t).
Proof. exact (fun_ext (fun x' : prod A B => @lem4327908 A B x x' s t)). Qed.
Lemma lem4327910 {A B : Type'} : (@ex (prod A B)) = (@ex (prod A B)).
Proof. exact (eq_refl (@ex (prod A B))). Qed.
Lemma lem4327911 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) : (term96 A B x s t) = (term93 A B x s t).
Proof. exact (MK_COMB (@lem4327910 A B) (@lem4327909 A B x s t)). Qed.
Lemma lem4327912 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4327913 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) : (term102 A B x s t) = (term103 A B x s t).
Proof. exact (MK_COMB (@lem4327912) (@lem4327911 A B x s t)). Qed.
Lemma lem4327914 {A B : Type'} (x : A) (p1 : A) (p2 : B) (s : A -> Prop) (t : B -> Prop) : (term104 A B x s t p1 p2) = (term105 A B x p1 p2 s t).
Proof. exact (eq_refl (term104 A B x s t p1 p2)). Qed.
Lemma lem4327915 {A B : Type'} (x : A) (p1 : A) (s : A -> Prop) (t : B -> Prop) : (term106 A B x s t p1) = (term107 A B x p1 s t).
Proof. exact (fun_ext (fun p2 : B => @lem4327914 A B x p1 p2 s t)). Qed.
Lemma lem4327916 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4327917 {A B : Type'} (x : A) (p1 : A) (s : A -> Prop) (t : B -> Prop) : (term108 A B x s t p1) = (term109 A B x p1 s t).
Proof. exact (MK_COMB (@lem4327916 B) (@lem4327915 A B x p1 s t)). Qed.
Lemma lem4327918 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) : (term110 A B x s t) = (term111 A B x s t).
Proof. exact (fun_ext (fun p1 : A => @lem4327917 A B x p1 s t)). Qed.
Lemma lem4327919 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4327920 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) : (term97 A B x s t) = (term112 A B x s t).
Proof. exact (MK_COMB (@lem4327919 A) (@lem4327918 A B x s t)). Qed.
Lemma lem4327921 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) : ((term96 A B x s t) = (term97 A B x s t)) = ((term93 A B x s t) = (term112 A B x s t)).
Proof. exact (MK_COMB (@lem4327913 A B x s t) (@lem4327920 A B x s t)). Qed.
Lemma lem4327922 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) : (term93 A B x s t) = (term112 A B x s t).
Proof. exact (EQ_MP (@lem4327921 A B x s t) (@lem4327907 A B x s t)). Qed.
Lemma lem4327929 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) : (term92 A B x s t) = (term112 A B x s t).
Proof. exact (TRANS (@lem4327899 A B x s t) (@lem4327922 A B x s t)). Qed.
Lemma lem4327941 {A B : Type'} (y : B) (x : A) : (term113 A B x y) = x.
Proof. exact (EQ_MP (@lem48220 A B y x) (@lem48219 A B x y)). Qed.
Lemma lem4327942 {A B : Type'} (y : B) (x : A) : (term113 A B x y) = x.
Proof. exact (@lem4327941 A B y x). Qed.
Lemma lem4327943 {A B : Type'} (p2 : B) (p1 : A) : (term113 A B p1 p2) = p1.
Proof. exact (@lem4327942 A B p2 p1). Qed.
Lemma lem4327944 {A : Type'} (x : A) : (@eq A x) = (@eq A x).
Proof. exact (eq_refl (@eq A x)). Qed.
Lemma lem4327945 {A B : Type'} (p2 : B) (x : A) (p1 : A) : (x = (term113 A B p1 p2)) = (x = p1).
Proof. exact (MK_COMB (@lem4327944 A x) (@lem4327943 A B p2 p1)). Qed.
Lemma lem4327948 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4327949 {A B : Type'} (p2 : B) (x : A) (p1 : A) : (term114 A B x p1 p2) = (term115 A x p1).
Proof. exact (MK_COMB (@lem4327948) (@lem4327945 A B p2 x p1)). Qed.
Lemma lem4327951 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term7 _103718 _103721 x y s t) = (term8 _103718 _103721 x s y t).
Proof. exact (EQ_MP (@lem4327467 _103718 _103721 x s y t) (@lem4327466 _103718 _103721 x s y t)). Qed.
Lemma lem4327952 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (t : B -> Prop) : (term7 A B x y s t) = (term8 A B x s y t).
Proof. exact (@lem4327951 A B x s y t). Qed.
Lemma lem4327953 {A B : Type'} (p1 : A) (s : A -> Prop) (p2 : B) (t : B -> Prop) : (term7 A B p1 p2 s t) = (term8 A B p1 s p2 t).
Proof. exact (@lem4327952 A B p1 s p2 t). Qed.
Lemma lem4327956 {A B : Type'} (x : A) (p1 : A) (s : A -> Prop) (p2 : B) (t : B -> Prop) : (term105 A B x p1 p2 s t) = (term116 A B x p1 s p2 t).
Proof. exact (MK_COMB (@lem4327949 A B p2 x p1) (@lem4327953 A B p1 s p2 t)). Qed.
Lemma lem4327959 {A B : Type'} (x : A) (p1 : A) (s : A -> Prop) (t : B -> Prop) : (term107 A B x p1 s t) = (term117 A B x p1 s t).
Proof. exact (fun_ext (fun p2 : B => @lem4327956 A B x p1 s p2 t)). Qed.
Lemma lem4327960 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4327961 {A B : Type'} (x : A) (p1 : A) (s : A -> Prop) (t : B -> Prop) : (term109 A B x p1 s t) = (term118 A B x p1 s t).
Proof. exact (MK_COMB (@lem4327960 B) (@lem4327959 A B x p1 s t)). Qed.
Lemma lem4327968 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) : (term111 A B x s t) = (term119 A B x s t).
Proof. exact (fun_ext (fun p1 : A => @lem4327961 A B x p1 s t)). Qed.
Lemma lem4327969 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4327970 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) : (term112 A B x s t) = (term120 A B x s t).
Proof. exact (MK_COMB (@lem4327969 A) (@lem4327968 A B x s t)). Qed.
Lemma lem4327977 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) : (term92 A B x s t) = (term120 A B x s t).
Proof. exact (TRANS (@lem4327929 A B x s t) (@lem4327970 A B x s t)). Qed.
Lemma lem4327978 {A : Type'} (x : A) (s : A -> Prop) : (term121 A x s) = (term121 A x s).
Proof. exact (eq_refl (term121 A x s)). Qed.
Lemma lem4327979 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) : (term122 A B x s t) = (term123 A B x s t).
Proof. exact (MK_COMB (@lem4327978 A x s) (@lem4327977 A B x s t)). Qed.
Lemma lem4327982 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term124 A B s t) = (term125 A B s t).
Proof. exact (fun_ext (fun x : A => @lem4327979 A B x s t)). Qed.
Lemma lem4327983 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4327984 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term89 A B s t) = (term126 A B s t).
Proof. exact (MK_COMB (@lem4327983 A) (@lem4327982 A B s t)). Qed.
Lemma lem4327989 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term88 A B s t) = (term126 A B s t).
Proof. exact (TRANS (@lem4327889 A B s t) (@lem4327984 A B s t)). Qed.
Lemma lem4327990 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term126 A B s t) = (term88 A B s t).
Proof. exact (SYM (@lem4327989 A B s t)). Qed.
Lemma lem4327992 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term22 A s t).
Proof. exact (EQ_MP (@lem4327485 A s t) (@lem4327484 A s t)). Qed.
Lemma lem4327993 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (@SUBSET B s t) = (term22 B s t).
Proof. exact (@lem4327992 B s t). Qed.
Lemma lem4327994 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term127 A B s t) = (term128 A B s t).
Proof. exact (@lem4327993 B t (term87 A B s t)). Qed.
Lemma lem4328002 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term17 A B y f s) = (term18 A B y f s).
Proof. exact (EQ_MP (@lem4327479 A B y f s) (@lem4327478 A B y s f)). Qed.
Lemma lem4328003 {A B : Type'} (y : B) (f : type1208 A B) (s : type1210 A B) : (term129 A B y f s) = (term130 A B y f s).
Proof. exact (@lem4328002 (prod A B) B y f s). Qed.
Lemma lem4328004 {A B : Type'} (x : B) (s : A -> Prop) (t : B -> Prop) : (term131 A B x s t) = (term132 A B x s t).
Proof. exact (@lem4328003 A B x (@snd A B) (@CROSS B A s t)). Qed.
Lemma lem4328010 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term10 _5131 _5132 P) = (term11 _5131 _5132 P).
Proof. exact (EQ_MP (@lem4327470 _5131 _5132 P) (@lem4327469 _5131 _5132 P)). Qed.
Lemma lem4328011 {A B : Type'} (P : type1210 A B) : (term94 A B P) = (term95 A B P).
Proof. exact (@lem4328010 B A P). Qed.
Lemma lem4328012 {A B : Type'} (x : B) (s : A -> Prop) (t : B -> Prop) : (term133 A B x s t) = (term134 A B x s t).
Proof. exact (@lem4328011 A B (term135 A B x s t)). Qed.
Lemma lem4328013 {A B : Type'} (x : B) (x' : prod A B) (s : A -> Prop) (t : B -> Prop) : (term136 A B x s t x') = (term137 A B x x' s t).
Proof. exact (eq_refl (term136 A B x s t x')). Qed.
Lemma lem4328014 {A B : Type'} (x : B) (s : A -> Prop) (t : B -> Prop) : (term138 A B x s t) = (term135 A B x s t).
Proof. exact (fun_ext (fun x' : prod A B => @lem4328013 A B x x' s t)). Qed.
Lemma lem4328015 {A B : Type'} : (@ex (prod A B)) = (@ex (prod A B)).
Proof. exact (eq_refl (@ex (prod A B))). Qed.
Lemma lem4328016 {A B : Type'} (x : B) (s : A -> Prop) (t : B -> Prop) : (term133 A B x s t) = (term132 A B x s t).
Proof. exact (MK_COMB (@lem4328015 A B) (@lem4328014 A B x s t)). Qed.
Lemma lem4328017 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4328018 {A B : Type'} (x : B) (s : A -> Prop) (t : B -> Prop) : (term139 A B x s t) = (term140 A B x s t).
Proof. exact (MK_COMB (@lem4328017) (@lem4328016 A B x s t)). Qed.
Lemma lem4328019 {A B : Type'} (x : B) (p1 : A) (p2 : B) (s : A -> Prop) (t : B -> Prop) : (term141 A B x s t p1 p2) = (term142 A B x p1 p2 s t).
Proof. exact (eq_refl (term141 A B x s t p1 p2)). Qed.
Lemma lem4328020 {A B : Type'} (x : B) (p1 : A) (s : A -> Prop) (t : B -> Prop) : (term143 A B x s t p1) = (term144 A B x p1 s t).
Proof. exact (fun_ext (fun p2 : B => @lem4328019 A B x p1 p2 s t)). Qed.
Lemma lem4328021 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4328022 {A B : Type'} (x : B) (p1 : A) (s : A -> Prop) (t : B -> Prop) : (term145 A B x s t p1) = (term146 A B x p1 s t).
Proof. exact (MK_COMB (@lem4328021 B) (@lem4328020 A B x p1 s t)). Qed.
Lemma lem4328023 {A B : Type'} (x : B) (s : A -> Prop) (t : B -> Prop) : (term147 A B x s t) = (term148 A B x s t).
Proof. exact (fun_ext (fun p1 : A => @lem4328022 A B x p1 s t)). Qed.
Lemma lem4328024 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4328025 {A B : Type'} (x : B) (s : A -> Prop) (t : B -> Prop) : (term134 A B x s t) = (term149 A B x s t).
Proof. exact (MK_COMB (@lem4328024 A) (@lem4328023 A B x s t)). Qed.
Lemma lem4328026 {A B : Type'} (x : B) (s : A -> Prop) (t : B -> Prop) : ((term133 A B x s t) = (term134 A B x s t)) = ((term132 A B x s t) = (term149 A B x s t)).
Proof. exact (MK_COMB (@lem4328018 A B x s t) (@lem4328025 A B x s t)). Qed.
Lemma lem4328027 {A B : Type'} (x : B) (s : A -> Prop) (t : B -> Prop) : (term132 A B x s t) = (term149 A B x s t).
Proof. exact (EQ_MP (@lem4328026 A B x s t) (@lem4328012 A B x s t)). Qed.
Lemma lem4328034 {A B : Type'} (x : B) (s : A -> Prop) (t : B -> Prop) : (term131 A B x s t) = (term149 A B x s t).
Proof. exact (TRANS (@lem4328004 A B x s t) (@lem4328027 A B x s t)). Qed.
Lemma lem4328046 {A B : Type'} (x : A) (y : B) : (term150 A B x y) = y.
Proof. exact (EQ_MP (@lem48214 A B x y) (@lem48213 A B x y)). Qed.
Lemma lem4328047 {A B : Type'} (x : A) (y : B) : (term150 A B x y) = y.
Proof. exact (@lem4328046 A B x y). Qed.
Lemma lem4328048 {A B : Type'} (p1 : A) (p2 : B) : (term150 A B p1 p2) = p2.
Proof. exact (@lem4328047 A B p1 p2). Qed.
Lemma lem4328049 {B : Type'} (x : B) : (@eq B x) = (@eq B x).
Proof. exact (eq_refl (@eq B x)). Qed.
Lemma lem4328050 {A B : Type'} (p1 : A) (x : B) (p2 : B) : (x = (term150 A B p1 p2)) = (x = p2).
Proof. exact (MK_COMB (@lem4328049 B x) (@lem4328048 A B p1 p2)). Qed.
Lemma lem4328053 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4328054 {A B : Type'} (p1 : A) (x : B) (p2 : B) : (term151 A B x p1 p2) = (term115 B x p2).
Proof. exact (MK_COMB (@lem4328053) (@lem4328050 A B p1 x p2)). Qed.
Lemma lem4328056 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term7 _103718 _103721 x y s t) = (term8 _103718 _103721 x s y t).
Proof. exact (EQ_MP (@lem4327467 _103718 _103721 x s y t) (@lem4327466 _103718 _103721 x s y t)). Qed.
Lemma lem4328057 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (t : B -> Prop) : (term7 A B x y s t) = (term8 A B x s y t).
Proof. exact (@lem4328056 A B x s y t). Qed.
Lemma lem4328058 {A B : Type'} (p1 : A) (s : A -> Prop) (p2 : B) (t : B -> Prop) : (term7 A B p1 p2 s t) = (term8 A B p1 s p2 t).
Proof. exact (@lem4328057 A B p1 s p2 t). Qed.
Lemma lem4328061 {A B : Type'} (x : B) (p1 : A) (s : A -> Prop) (p2 : B) (t : B -> Prop) : (term142 A B x p1 p2 s t) = (term152 A B x p1 s p2 t).
Proof. exact (MK_COMB (@lem4328054 A B p1 x p2) (@lem4328058 A B p1 s p2 t)). Qed.
Lemma lem4328064 {A B : Type'} (x : B) (p1 : A) (s : A -> Prop) (t : B -> Prop) : (term144 A B x p1 s t) = (term153 A B x p1 s t).
Proof. exact (fun_ext (fun p2 : B => @lem4328061 A B x p1 s p2 t)). Qed.
Lemma lem4328065 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4328066 {A B : Type'} (x : B) (p1 : A) (s : A -> Prop) (t : B -> Prop) : (term146 A B x p1 s t) = (term154 A B x p1 s t).
Proof. exact (MK_COMB (@lem4328065 B) (@lem4328064 A B x p1 s t)). Qed.
Lemma lem4328073 {A B : Type'} (x : B) (s : A -> Prop) (t : B -> Prop) : (term148 A B x s t) = (term155 A B x s t).
Proof. exact (fun_ext (fun p1 : A => @lem4328066 A B x p1 s t)). Qed.
Lemma lem4328074 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4328075 {A B : Type'} (x : B) (s : A -> Prop) (t : B -> Prop) : (term149 A B x s t) = (term156 A B x s t).
Proof. exact (MK_COMB (@lem4328074 A) (@lem4328073 A B x s t)). Qed.
Lemma lem4328082 {A B : Type'} (x : B) (s : A -> Prop) (t : B -> Prop) : (term131 A B x s t) = (term156 A B x s t).
Proof. exact (TRANS (@lem4328034 A B x s t) (@lem4328075 A B x s t)). Qed.
Lemma lem4328083 {B : Type'} (x : B) (t : B -> Prop) : (term121 B x t) = (term121 B x t).
Proof. exact (eq_refl (term121 B x t)). Qed.
Lemma lem4328084 {A B : Type'} (x : B) (s : A -> Prop) (t : B -> Prop) : (term157 A B x s t) = (term158 A B x s t).
Proof. exact (MK_COMB (@lem4328083 B x t) (@lem4328082 A B x s t)). Qed.
Lemma lem4328087 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term159 A B s t) = (term160 A B s t).
Proof. exact (fun_ext (fun x : B => @lem4328084 A B x s t)). Qed.
Lemma lem4328088 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4328089 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term128 A B s t) = (term161 A B s t).
Proof. exact (MK_COMB (@lem4328088 B) (@lem4328087 A B s t)). Qed.
Lemma lem4328094 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term127 A B s t) = (term161 A B s t).
Proof. exact (TRANS (@lem4327994 A B s t) (@lem4328089 A B s t)). Qed.
Lemma lem4328095 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term161 A B s t) = (term127 A B s t).
Proof. exact (SYM (@lem4328094 A B s t)). Qed.
Lemma lem4328106 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term60 A s) (h2 : term60 B t) : term162 A B t s.
Proof. exact (conj (@lem4327566 B t h2) (@lem4327571 A s h1)). Qed.
Lemma lem4328107 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term63 A B s t) (h2 : term60 A s) (h3 : term60 B t) : term163 A B t s.
Proof. exact (conj (@lem4327867 A B s t h1) (@lem4328106 A B s t h2 h3)). Qed.
Lemma lem4328117 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term164 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem4328118 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (s = t) = (term164 B s t).
Proof. exact (@lem4328117 B s t). Qed.
Lemma lem4328119 {B : Type'} (t : B -> Prop) : (t = (@EMPTY B)) = (term165 B t).
Proof. exact (@lem4328118 B t (@EMPTY B)). Qed.
Lemma lem4328128 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4328129 {B : Type'} (t : B -> Prop) : (term60 B t) = (term166 B t).
Proof. exact (MK_COMB (@lem4328128) (@lem4328119 B t)). Qed.
Lemma lem4328130 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4328131 {B : Type'} (t : B -> Prop) : (term167 B t) = (term168 B t).
Proof. exact (MK_COMB (@lem4328130) (@lem4328129 B t)). Qed.
Lemma lem4328135 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term164 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem4328136 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term164 A s t).
Proof. exact (@lem4328135 A s t). Qed.
Lemma lem4328137 {A : Type'} (s : A -> Prop) : (s = (@EMPTY A)) = (term165 A s).
Proof. exact (@lem4328136 A s (@EMPTY A)). Qed.
Lemma lem4328146 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4328147 {A : Type'} (s : A -> Prop) : (term60 A s) = (term166 A s).
Proof. exact (MK_COMB (@lem4328146) (@lem4328137 A s)). Qed.
Lemma lem4328148 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term162 A B t s) = (term169 A B t s).
Proof. exact (MK_COMB (@lem4328131 B t) (@lem4328147 A s)). Qed.
Lemma lem4328151 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term170 A B s t) = (term170 A B s t).
Proof. exact (eq_refl (term170 A B s t)). Qed.
Lemma lem4328152 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term163 A B t s) = (term171 A B t s).
Proof. exact (MK_COMB (@lem4328151 A B s t) (@lem4328148 A B t s)). Qed.
Lemma lem4328155 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4328156 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term172 A B t s) = (term173 A B t s).
Proof. exact (MK_COMB (@lem4328155) (@lem4328152 A B t s)). Qed.
Lemma lem4328179 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term126 A B s t) = (term126 A B s t).
Proof. exact (eq_refl (term126 A B s t)). Qed.
Lemma lem4328180 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term174 A B s t) = (term175 A B s t).
Proof. exact (MK_COMB (@lem4328156 A B t s) (@lem4328179 A B s t)). Qed.
Lemma lem4328183 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term175 A B s t) = (term174 A B s t).
Proof. exact (SYM (@lem4328180 A B s t)). Qed.
Lemma lem4328197 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4328198 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem4328197 B P x). Qed.
Lemma lem4328199 {B : Type'} (t : B -> Prop) (x : B) : (@IN B x t) = (t x).
Proof. exact (@lem4328198 B t x). Qed.
Lemma lem4328200 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4328201 {B : Type'} (t : B -> Prop) (x : B) : (term176 B x t) = (term177 B t x).
Proof. exact (MK_COMB (@lem4328200) (@lem4328199 B t x)). Qed.
Lemma lem4328203 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem4328204 {B : Type'} (x : B) : (@IN B x (@EMPTY B)) = False.
Proof. exact (@lem4328203 B x). Qed.
Lemma lem4328205 {B : Type'} (t : B -> Prop) (x : B) : ((@IN B x t) = (@IN B x (@EMPTY B))) = ((t x) = False).
Proof. exact (MK_COMB (@lem4328201 B t x) (@lem4328204 B x)). Qed.
Lemma lem4328207 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem4328208 {B : Type'} (t : B -> Prop) (x : B) : ((t x) = False) = (term178 B t x).
Proof. exact (@lem4328207 (t x)). Qed.
Lemma lem4328209 {B : Type'} (t : B -> Prop) (x : B) : ((@IN B x t) = (@IN B x (@EMPTY B))) = (term178 B t x).
Proof. exact (TRANS (@lem4328205 B t x) (@lem4328208 B t x)). Qed.
Lemma lem4328210 {B : Type'} (t : B -> Prop) : (term179 B t) = (term180 B t).
Proof. exact (fun_ext (fun x : B => @lem4328209 B t x)). Qed.
Lemma lem4328211 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4328212 {B : Type'} (t : B -> Prop) : (term165 B t) = (term181 B t).
Proof. exact (MK_COMB (@lem4328211 B) (@lem4328210 B t)). Qed.
Lemma lem4328217 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4328218 {B : Type'} (t : B -> Prop) : (term166 B t) = (term182 B t).
Proof. exact (MK_COMB (@lem4328217) (@lem4328212 B t)). Qed.
Lemma lem4328219 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4328220 {B : Type'} (t : B -> Prop) : (term168 B t) = (term183 B t).
Proof. exact (MK_COMB (@lem4328219) (@lem4328218 B t)). Qed.
Lemma lem4328228 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4328229 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4328228 A P x). Qed.
Lemma lem4328230 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4328229 A s x). Qed.
Lemma lem4328231 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4328232 {A : Type'} (s : A -> Prop) (x : A) : (term176 A x s) = (term177 A s x).
Proof. exact (MK_COMB (@lem4328231) (@lem4328230 A s x)). Qed.
Lemma lem4328234 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem4328235 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4328234 A x). Qed.
Lemma lem4328236 {A : Type'} (s : A -> Prop) (x : A) : ((@IN A x s) = (@IN A x (@EMPTY A))) = ((s x) = False).
Proof. exact (MK_COMB (@lem4328232 A s x) (@lem4328235 A x)). Qed.
Lemma lem4328238 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem4328239 {A : Type'} (s : A -> Prop) (x : A) : ((s x) = False) = (term178 A s x).
Proof. exact (@lem4328238 (s x)). Qed.
Lemma lem4328240 {A : Type'} (s : A -> Prop) (x : A) : ((@IN A x s) = (@IN A x (@EMPTY A))) = (term178 A s x).
Proof. exact (TRANS (@lem4328236 A s x) (@lem4328239 A s x)). Qed.
Lemma lem4328241 {A : Type'} (s : A -> Prop) : (term179 A s) = (term180 A s).
Proof. exact (fun_ext (fun x : A => @lem4328240 A s x)). Qed.
Lemma lem4328242 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4328243 {A : Type'} (s : A -> Prop) : (term165 A s) = (term181 A s).
Proof. exact (MK_COMB (@lem4328242 A) (@lem4328241 A s)). Qed.
Lemma lem4328248 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4328249 {A : Type'} (s : A -> Prop) : (term166 A s) = (term182 A s).
Proof. exact (MK_COMB (@lem4328248) (@lem4328243 A s)). Qed.
Lemma lem4328250 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term169 A B t s) = (term184 A B t s).
Proof. exact (MK_COMB (@lem4328220 B t) (@lem4328249 A s)). Qed.
Lemma lem4328253 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term170 A B s t) = (term170 A B s t).
Proof. exact (eq_refl (term170 A B s t)). Qed.
Lemma lem4328254 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term171 A B t s) = (term185 A B t s).
Proof. exact (MK_COMB (@lem4328253 A B s t) (@lem4328250 A B t s)). Qed.
Lemma lem4328257 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4328258 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term173 A B t s) = (term186 A B t s).
Proof. exact (MK_COMB (@lem4328257) (@lem4328254 A B t s)). Qed.
Lemma lem4328266 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4328267 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4328266 A P x). Qed.
Lemma lem4328268 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4328267 A s x). Qed.
Lemma lem4328269 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4328270 {A : Type'} (s : A -> Prop) (x : A) : (term121 A x s) = (term187 A s x).
Proof. exact (MK_COMB (@lem4328269) (@lem4328268 A s x)). Qed.
Lemma lem4328286 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4328287 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4328286 A P x). Qed.
Lemma lem4328288 {A : Type'} (s : A -> Prop) (p1 : A) : (@IN A p1 s) = (s p1).
Proof. exact (@lem4328287 A s p1). Qed.
Lemma lem4328289 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4328290 {A : Type'} (s : A -> Prop) (p1 : A) : (term188 A p1 s) = (term189 A s p1).
Proof. exact (MK_COMB (@lem4328289) (@lem4328288 A s p1)). Qed.
Lemma lem4328292 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4328293 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem4328292 B P x). Qed.
Lemma lem4328294 {B : Type'} (t : B -> Prop) (p2 : B) : (@IN B p2 t) = (t p2).
Proof. exact (@lem4328293 B t p2). Qed.
Lemma lem4328295 {A B : Type'} (s : A -> Prop) (p1 : A) (t : B -> Prop) (p2 : B) : (term8 A B p1 s p2 t) = (term190 A B s p1 t p2).
Proof. exact (MK_COMB (@lem4328290 A s p1) (@lem4328294 B t p2)). Qed.
Lemma lem4328298 {A : Type'} (x : A) (p1 : A) : (term115 A x p1) = (term115 A x p1).
Proof. exact (eq_refl (term115 A x p1)). Qed.
Lemma lem4328299 {A B : Type'} (x : A) (s : A -> Prop) (p1 : A) (t : B -> Prop) (p2 : B) : (term116 A B x p1 s p2 t) = (term191 A B x s p1 t p2).
Proof. exact (MK_COMB (@lem4328298 A x p1) (@lem4328295 A B s p1 t p2)). Qed.
Lemma lem4328302 {A B : Type'} (x : A) (s : A -> Prop) (p1 : A) (t : B -> Prop) : (term117 A B x p1 s t) = (term192 A B x s p1 t).
Proof. exact (fun_ext (fun p2 : B => @lem4328299 A B x s p1 t p2)). Qed.
Lemma lem4328303 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4328304 {A B : Type'} (x : A) (s : A -> Prop) (p1 : A) (t : B -> Prop) : (term118 A B x p1 s t) = (term193 A B x s p1 t).
Proof. exact (MK_COMB (@lem4328303 B) (@lem4328302 A B x s p1 t)). Qed.
Lemma lem4328309 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) : (term119 A B x s t) = (term194 A B x s t).
Proof. exact (fun_ext (fun p1 : A => @lem4328304 A B x s p1 t)). Qed.
Lemma lem4328310 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4328311 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) : (term120 A B x s t) = (term195 A B x s t).
Proof. exact (MK_COMB (@lem4328310 A) (@lem4328309 A B x s t)). Qed.
Lemma lem4328316 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) : (term123 A B x s t) = (term196 A B x s t).
Proof. exact (MK_COMB (@lem4328270 A s x) (@lem4328311 A B x s t)). Qed.
Lemma lem4328319 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term125 A B s t) = (term197 A B s t).
Proof. exact (fun_ext (fun x : A => @lem4328316 A B x s t)). Qed.
Lemma lem4328320 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4328321 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term126 A B s t) = (term198 A B s t).
Proof. exact (MK_COMB (@lem4328320 A) (@lem4328319 A B s t)). Qed.
Lemma lem4328326 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term175 A B s t) = (term199 A B s t).
Proof. exact (MK_COMB (@lem4328258 A B t s) (@lem4328321 A B s t)). Qed.
Lemma lem4328329 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term199 A B s t) = (term175 A B s t).
Proof. exact (SYM (@lem4328326 A B s t)). Qed.
Lemma lem4328331 (p : Prop) : p = (term200 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4328332 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term199 A B s t) = (term201 A B s t).
Proof. exact (@lem4328331 (term199 A B s t)). Qed.
Lemma lem4328333 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term201 A B s t) = (term199 A B s t).
Proof. exact (SYM (@lem4328332 A B s t)). Qed.
Lemma lem4328334 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term202 A B s t) : term202 A B s t.
Proof. exact (h1). Qed.
Lemma lem4328337 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term201 A B s t) : term201 A B s t.
Proof. exact (h1). Qed.
Lemma lem4328338 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term203 A B s t.
Proof. exact (fun h0 : term201 A B s t => @lem4328337 A B s t h0). Qed.
Lemma lem4328339 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term203 A B s t) : term203 A B s t.
Proof. exact (h1). Qed.
Lemma lem4328340 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term201 A B s t) : term201 A B s t.
Proof. exact (h1). Qed.
Lemma lem4328341 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term201 A B s t) (h2 : term203 A B s t) : term201 A B s t.
Proof. exact (@lem4328339 A B s t h2 (@lem4328340 A B s t h1)). Qed.
Lemma lem4328342 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term201 A B s t) : term204 A B s t.
Proof. exact (fun h0 : term203 A B s t => @lem4328341 A B s t h1 h0). Qed.
Lemma lem4328343 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term203 A B s t) : term203 A B s t.
Proof. exact (h1). Qed.
Lemma lem4328344 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term201 A B s t) (h2 : term203 A B s t) : term201 A B s t.
Proof. exact (@lem4328342 A B s t h1 (@lem4328343 A B s t h2)). Qed.
Lemma lem4328345 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term203 A B s t) : term203 A B s t.
Proof. exact (fun h0 : term201 A B s t => @lem4328344 A B s t h0 h1). Qed.
Lemma lem4328346 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term205 A B s t.
Proof. exact (fun h0 : term203 A B s t => @lem4328345 A B s t h0). Qed.
Lemma lem4328349 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term203 A B s t.
Proof. exact (@lem4328346 A B s t (@lem4328338 A B s t)). Qed.
Lemma lem4328350 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term203 A B s t.
Proof. exact (@lem4328349 A B s t). Qed.
Lemma lem4328360 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4328361 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term201 A B s t) = (term206 A B s t).
Proof. exact (@lem4328360 (term202 A B s t)). Qed.
Lemma lem4328363 (t : Prop) : (term207 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4328364 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term206 A B s t) = (term199 A B s t).
Proof. exact (@lem4328363 (term199 A B s t)). Qed.
Lemma lem4328367 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term201 A B s t) = (term199 A B s t).
Proof. exact (TRANS (@lem4328361 A B s t) (@lem4328364 A B s t)). Qed.
Lemma lem4328391 {A : Type'} (P : Prop) (Q : A -> Prop) : (term208 A P Q) = (term209 A P Q).
Proof. exact (EQ_MP (@lem16434 A P Q) (@lem16433 A P Q)). Qed.
Lemma lem4328392 {B : Type'} (P : Prop) (Q : B -> Prop) : (term208 B P Q) = (term209 B P Q).
Proof. exact (@lem4328391 B P Q). Qed.
Lemma lem4328393 {A B : Type'} (x : A) (s : A -> Prop) (p1 : A) (t : B -> Prop) : (term210 A B x s p1 t) = (term211 A B x s p1 t).
Proof. exact (@lem4328392 B (x = p1) (term212 A B s p1 t)). Qed.
Lemma lem4328394 {A B : Type'} (s : A -> Prop) (p1 : A) (t : B -> Prop) (p2 : B) : (term213 A B s p1 t p2) = (term190 A B s p1 t p2).
Proof. exact (eq_refl (term213 A B s p1 t p2)). Qed.
Lemma lem4328395 {A : Type'} (x : A) (p1 : A) : (term115 A x p1) = (term115 A x p1).
Proof. exact (eq_refl (term115 A x p1)). Qed.
Lemma lem4328396 {A B : Type'} (x : A) (s : A -> Prop) (p1 : A) (t : B -> Prop) (p2 : B) : (term214 A B x s p1 t p2) = (term191 A B x s p1 t p2).
Proof. exact (MK_COMB (@lem4328395 A x p1) (@lem4328394 A B s p1 t p2)). Qed.
Lemma lem4328397 {A B : Type'} (x : A) (s : A -> Prop) (p1 : A) (t : B -> Prop) : (term215 A B x s p1 t) = (term192 A B x s p1 t).
Proof. exact (fun_ext (fun p2 : B => @lem4328396 A B x s p1 t p2)). Qed.
Lemma lem4328398 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4328399 {A B : Type'} (x : A) (s : A -> Prop) (p1 : A) (t : B -> Prop) : (term210 A B x s p1 t) = (term193 A B x s p1 t).
Proof. exact (MK_COMB (@lem4328398 B) (@lem4328397 A B x s p1 t)). Qed.
Lemma lem4328400 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4328401 {A B : Type'} (x : A) (s : A -> Prop) (p1 : A) (t : B -> Prop) : (term216 A B x s p1 t) = (term217 A B x s p1 t).
Proof. exact (MK_COMB (@lem4328400) (@lem4328399 A B x s p1 t)). Qed.
Lemma lem4328402 {A B : Type'} (s : A -> Prop) (p1 : A) (t : B -> Prop) (p2 : B) : (term213 A B s p1 t p2) = (term190 A B s p1 t p2).
Proof. exact (eq_refl (term213 A B s p1 t p2)). Qed.
Lemma lem4328403 {A B : Type'} (s : A -> Prop) (p1 : A) (t : B -> Prop) : (term218 A B s p1 t) = (term212 A B s p1 t).
Proof. exact (fun_ext (fun p2 : B => @lem4328402 A B s p1 t p2)). Qed.
Lemma lem4328404 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4328405 {A B : Type'} (s : A -> Prop) (p1 : A) (t : B -> Prop) : (term219 A B s p1 t) = (term220 A B s p1 t).
Proof. exact (MK_COMB (@lem4328404 B) (@lem4328403 A B s p1 t)). Qed.
Lemma lem4328406 {A : Type'} (x : A) (p1 : A) : (term115 A x p1) = (term115 A x p1).
Proof. exact (eq_refl (term115 A x p1)). Qed.
Lemma lem4328407 {A B : Type'} (x : A) (s : A -> Prop) (p1 : A) (t : B -> Prop) : (term211 A B x s p1 t) = (term221 A B x s p1 t).
Proof. exact (MK_COMB (@lem4328406 A x p1) (@lem4328405 A B s p1 t)). Qed.
Lemma lem4328408 {A B : Type'} (x : A) (s : A -> Prop) (p1 : A) (t : B -> Prop) : ((term210 A B x s p1 t) = (term211 A B x s p1 t)) = ((term193 A B x s p1 t) = (term221 A B x s p1 t)).
Proof. exact (MK_COMB (@lem4328401 A B x s p1 t) (@lem4328407 A B x s p1 t)). Qed.
Lemma lem4328409 {A B : Type'} (x : A) (s : A -> Prop) (p1 : A) (t : B -> Prop) : (term193 A B x s p1 t) = (term221 A B x s p1 t).
Proof. exact (EQ_MP (@lem4328408 A B x s p1 t) (@lem4328393 A B x s p1 t)). Qed.
Lemma lem4328413 {A : Type'} (P : Prop) (Q : A -> Prop) : (term208 A P Q) = (term209 A P Q).
Proof. exact (EQ_MP (@lem16434 A P Q) (@lem16433 A P Q)). Qed.
Lemma lem4328414 {B : Type'} (P : Prop) (Q : B -> Prop) : (term208 B P Q) = (term209 B P Q).
Proof. exact (@lem4328413 B P Q). Qed.
Lemma lem4328415 {A B : Type'} (s : A -> Prop) (p1 : A) (t : B -> Prop) : (term220 A B s p1 t) = (term222 A B s p1 t).
Proof. exact (@lem4328414 B (s p1) t). Qed.
Lemma lem4328422 {A : Type'} (x : A) (p1 : A) : (term115 A x p1) = (term115 A x p1).
Proof. exact (eq_refl (term115 A x p1)). Qed.
Lemma lem4328423 {A B : Type'} (x : A) (s : A -> Prop) (p1 : A) (t : B -> Prop) : (term221 A B x s p1 t) = (term223 A B x s p1 t).
Proof. exact (MK_COMB (@lem4328422 A x p1) (@lem4328415 A B s p1 t)). Qed.
Lemma lem4328426 {A B : Type'} (x : A) (s : A -> Prop) (p1 : A) (t : B -> Prop) : (term193 A B x s p1 t) = (term223 A B x s p1 t).
Proof. exact (TRANS (@lem4328409 A B x s p1 t) (@lem4328423 A B x s p1 t)). Qed.
Lemma lem4328427 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) : (term194 A B x s t) = (term224 A B x s t).
Proof. exact (fun_ext (fun p1 : A => @lem4328426 A B x s p1 t)). Qed.
Lemma lem4328428 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4328429 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) : (term195 A B x s t) = (term225 A B x s t).
Proof. exact (MK_COMB (@lem4328428 A) (@lem4328427 A B x s t)). Qed.
Lemma lem4328478 {A : Type'} (s : A -> Prop) (x : A) : (term187 A s x) = (term187 A s x).
Proof. exact (eq_refl (term187 A s x)). Qed.
Lemma lem4328479 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) : (term196 A B x s t) = (term226 A B x s t).
Proof. exact (MK_COMB (@lem4328478 A s x) (@lem4328429 A B x s t)). Qed.
Lemma lem4328482 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term197 A B s t) = (term227 A B s t).
Proof. exact (fun_ext (fun x : A => @lem4328479 A B x s t)). Qed.
Lemma lem4328483 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4328484 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term198 A B s t) = (term228 A B s t).
Proof. exact (MK_COMB (@lem4328483 A) (@lem4328482 A B s t)). Qed.
Lemma lem4328489 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term186 A B t s) = (term186 A B t s).
Proof. exact (eq_refl (term186 A B t s)). Qed.
Lemma lem4328490 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term199 A B s t) = (term229 A B s t).
Proof. exact (MK_COMB (@lem4328489 A B t s) (@lem4328484 A B s t)). Qed.
Lemma lem4328493 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term201 A B s t) = (term229 A B s t).
Proof. exact (TRANS (@lem4328367 A B s t) (@lem4328490 A B s t)). Qed.
Lemma lem4328494 {A B : Type'} (t : B -> Prop) : (term230 A B t) = (term231 A B t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4328493 A B s t)). Qed.
Lemma lem4328495 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4328496 {A B : Type'} (t : B -> Prop) : (term232 A B t) = (term233 A B t).
Proof. exact (MK_COMB (@lem4328495 A) (@lem4328494 A B t)). Qed.
Lemma lem4328501 {A B : Type'} : (term234 A B) = (term235 A B).
Proof. exact (fun_ext (fun t : B -> Prop => @lem4328496 A B t)). Qed.
Lemma lem4328502 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4328511 {A B : Type'} : (term236 A B) = (term237 A B).
Proof. exact (MK_COMB (@lem4328502 B) (@lem4328501 A B)). Qed.
Lemma lem4328512 {B : Type'} (t : B -> Prop) (p2 : B) : (t p2) = (t p2).
Proof. exact (eq_refl (t p2)). Qed.
Lemma lem4328513 {B : Type'} (t : B -> Prop) : (term238 B t) = (term238 B t).
Proof. exact (fun_ext (fun p2 : B => @lem4328512 B t p2)). Qed.
Lemma lem4328514 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4328515 {B : Type'} (t : B -> Prop) : (term239 B t) = (term239 B t).
Proof. exact (MK_COMB (@lem4328514 B) (@lem4328513 B t)). Qed.
Lemma lem4328518 {A : Type'} (s : A -> Prop) (p1 : A) : (term189 A s p1) = (term189 A s p1).
Proof. exact (eq_refl (term189 A s p1)). Qed.
Lemma lem4328519 {A B : Type'} (s : A -> Prop) (p1 : A) (t : B -> Prop) : (term222 A B s p1 t) = (term222 A B s p1 t).
Proof. exact (MK_COMB (@lem4328518 A s p1) (@lem4328515 B t)). Qed.
Lemma lem4328522 {A : Type'} (x : A) (p1 : A) : (term115 A x p1) = (term115 A x p1).
Proof. exact (eq_refl (term115 A x p1)). Qed.
Lemma lem4328523 {A B : Type'} (x : A) (s : A -> Prop) (p1 : A) (t : B -> Prop) : (term223 A B x s p1 t) = (term223 A B x s p1 t).
Proof. exact (MK_COMB (@lem4328522 A x p1) (@lem4328519 A B s p1 t)). Qed.
Lemma lem4328524 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) : (term224 A B x s t) = (term224 A B x s t).
Proof. exact (fun_ext (fun p1 : A => @lem4328523 A B x s p1 t)). Qed.
Lemma lem4328525 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4328526 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) : (term225 A B x s t) = (term225 A B x s t).
Proof. exact (MK_COMB (@lem4328525 A) (@lem4328524 A B x s t)). Qed.
Lemma lem4328529 {A : Type'} (s : A -> Prop) (x : A) : (term187 A s x) = (term187 A s x).
Proof. exact (eq_refl (term187 A s x)). Qed.
Lemma lem4328530 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) : (term226 A B x s t) = (term226 A B x s t).
Proof. exact (MK_COMB (@lem4328529 A s x) (@lem4328526 A B x s t)). Qed.
Lemma lem4328531 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term227 A B s t) = (term227 A B s t).
Proof. exact (fun_ext (fun x : A => @lem4328530 A B x s t)). Qed.
Lemma lem4328532 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4328533 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term228 A B s t) = (term228 A B s t).
Proof. exact (MK_COMB (@lem4328532 A) (@lem4328531 A B s t)). Qed.
Lemma lem4328536 {A : Type'} (s : A -> Prop) (x : A) : (term178 A s x) = (term178 A s x).
Proof. exact (eq_refl (term178 A s x)). Qed.
Lemma lem4328537 {A : Type'} (s : A -> Prop) : (term180 A s) = (term180 A s).
Proof. exact (fun_ext (fun x : A => @lem4328536 A s x)). Qed.
Lemma lem4328538 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4328539 {A : Type'} (s : A -> Prop) : (term181 A s) = (term181 A s).
Proof. exact (MK_COMB (@lem4328538 A) (@lem4328537 A s)). Qed.
Lemma lem4328540 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4328541 {A : Type'} (s : A -> Prop) : (term182 A s) = (term182 A s).
Proof. exact (MK_COMB (@lem4328540) (@lem4328539 A s)). Qed.
Lemma lem4328544 {B : Type'} (t : B -> Prop) (x : B) : (term178 B t x) = (term178 B t x).
Proof. exact (eq_refl (term178 B t x)). Qed.
Lemma lem4328545 {B : Type'} (t : B -> Prop) : (term180 B t) = (term180 B t).
Proof. exact (fun_ext (fun x : B => @lem4328544 B t x)). Qed.
Lemma lem4328546 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4328547 {B : Type'} (t : B -> Prop) : (term181 B t) = (term181 B t).
Proof. exact (MK_COMB (@lem4328546 B) (@lem4328545 B t)). Qed.
Lemma lem4328548 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4328549 {B : Type'} (t : B -> Prop) : (term182 B t) = (term182 B t).
Proof. exact (MK_COMB (@lem4328548) (@lem4328547 B t)). Qed.
Lemma lem4328550 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4328551 {B : Type'} (t : B -> Prop) : (term183 B t) = (term183 B t).
Proof. exact (MK_COMB (@lem4328550) (@lem4328549 B t)). Qed.
Lemma lem4328552 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term184 A B t s) = (term184 A B t s).
Proof. exact (MK_COMB (@lem4328551 B t) (@lem4328541 A s)). Qed.
Lemma lem4328555 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term170 A B s t) = (term170 A B s t).
Proof. exact (eq_refl (term170 A B s t)). Qed.
Lemma lem4328556 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term185 A B t s) = (term185 A B t s).
Proof. exact (MK_COMB (@lem4328555 A B s t) (@lem4328552 A B t s)). Qed.
Lemma lem4328557 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4328558 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term186 A B t s) = (term186 A B t s).
Proof. exact (MK_COMB (@lem4328557) (@lem4328556 A B t s)). Qed.
Lemma lem4328559 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term229 A B s t) = (term229 A B s t).
Proof. exact (MK_COMB (@lem4328558 A B t s) (@lem4328533 A B s t)). Qed.
Lemma lem4328560 {A B : Type'} (t : B -> Prop) : (term231 A B t) = (term231 A B t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4328559 A B s t)). Qed.
Lemma lem4328561 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4328562 {A B : Type'} (t : B -> Prop) : (term233 A B t) = (term233 A B t).
Proof. exact (MK_COMB (@lem4328561 A) (@lem4328560 A B t)). Qed.
Lemma lem4328563 {A B : Type'} : (term235 A B) = (term235 A B).
Proof. exact (fun_ext (fun t : B -> Prop => @lem4328562 A B t)). Qed.
Lemma lem4328564 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4328565 {A B : Type'} : (term237 A B) = (term237 A B).
Proof. exact (MK_COMB (@lem4328564 B) (@lem4328563 A B)). Qed.
Lemma lem4328622 {A B : Type'} : (term236 A B) = (term237 A B).
Proof. exact (TRANS (@lem4328511 A B) (@lem4328565 A B)). Qed.
Lemma lem4328623 {A B : Type'} : (term237 A B) = (term236 A B).
Proof. exact (SYM (@lem4328622 A B)). Qed.
Lemma lem4328624 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term185 A B t s) : term185 A B t s.
Proof. exact (h1). Qed.
Lemma lem4328627 (p : Prop) : p = (term200 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4328628 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) : (term225 A B x s t) = (term240 A B x s t).
Proof. exact (@lem4328627 (term225 A B x s t)). Qed.
Lemma lem4328629 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) : (term240 A B x s t) = (term225 A B x s t).
Proof. exact (SYM (@lem4328628 A B x s t)). Qed.
Lemma lem4328630 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (h1 : term241 A B x s t) : term241 A B x s t.
Proof. exact (h1). Qed.
Lemma lem4328634 {B : Type'} (t : B -> Prop) (x : B) : (term242 B t x) = (t x).
Proof. exact (@lem16933 (t x)). Qed.
Lemma lem4328635 {B : Type'} (P : B -> Prop) : (term243 B P) = (term244 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem4328636 {B : Type'} (t : B -> Prop) : (term182 B t) = (term245 B t).
Proof. exact (@lem4328635 B (term180 B t)). Qed.
Lemma lem4328637 {B : Type'} (t : B -> Prop) (x : B) : (term246 B t x) = (term178 B t x).
Proof. exact (eq_refl (term246 B t x)). Qed.
Lemma lem4328638 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4328639 {B : Type'} (t : B -> Prop) (x : B) : (term247 B t x) = (term242 B t x).
Proof. exact (MK_COMB (@lem4328638) (@lem4328637 B t x)). Qed.
Lemma lem4328640 {B : Type'} (t : B -> Prop) (x : B) : (term247 B t x) = (t x).
Proof. exact (TRANS (@lem4328639 B t x) (@lem4328634 B t x)). Qed.
Lemma lem4328641 {B : Type'} (t : B -> Prop) : (term248 B t) = (term238 B t).
Proof. exact (fun_ext (fun x : B => @lem4328640 B t x)). Qed.
Lemma lem4328642 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4328643 {B : Type'} (t : B -> Prop) : (term245 B t) = (term239 B t).
Proof. exact (MK_COMB (@lem4328642 B) (@lem4328641 B t)). Qed.
Lemma lem4328644 {B : Type'} (t : B -> Prop) : (term182 B t) = (term239 B t).
Proof. exact (TRANS (@lem4328636 B t) (@lem4328643 B t)). Qed.
Lemma lem4328647 {A : Type'} (s : A -> Prop) (x : A) : (term242 A s x) = (s x).
Proof. exact (@lem16933 (s x)). Qed.
Lemma lem4328648 {A : Type'} (P : A -> Prop) : (term243 A P) = (term244 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem4328649 {A : Type'} (s : A -> Prop) : (term182 A s) = (term245 A s).
Proof. exact (@lem4328648 A (term180 A s)). Qed.
Lemma lem4328650 {A : Type'} (s : A -> Prop) (x : A) : (term246 A s x) = (term178 A s x).
Proof. exact (eq_refl (term246 A s x)). Qed.
Lemma lem4328651 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4328652 {A : Type'} (s : A -> Prop) (x : A) : (term247 A s x) = (term242 A s x).
Proof. exact (MK_COMB (@lem4328651) (@lem4328650 A s x)). Qed.
Lemma lem4328653 {A : Type'} (s : A -> Prop) (x : A) : (term247 A s x) = (s x).
Proof. exact (TRANS (@lem4328652 A s x) (@lem4328647 A s x)). Qed.
Lemma lem4328654 {A : Type'} (s : A -> Prop) : (term248 A s) = (term238 A s).
Proof. exact (fun_ext (fun x : A => @lem4328653 A s x)). Qed.
Lemma lem4328655 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4328656 {A : Type'} (s : A -> Prop) : (term245 A s) = (term239 A s).
Proof. exact (MK_COMB (@lem4328655 A) (@lem4328654 A s)). Qed.
Lemma lem4328657 {A : Type'} (s : A -> Prop) : (term182 A s) = (term239 A s).
Proof. exact (TRANS (@lem4328649 A s) (@lem4328656 A s)). Qed.
Lemma lem4328658 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4328659 {B : Type'} (t : B -> Prop) : (term183 B t) = (term249 B t).
Proof. exact (MK_COMB (@lem4328658) (@lem4328644 B t)). Qed.
Lemma lem4328660 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term184 A B t s) = (term250 A B t s).
Proof. exact (MK_COMB (@lem4328659 B t) (@lem4328657 A s)). Qed.
Lemma lem4328662 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term170 A B s t) = (term170 A B s t).
Proof. exact (eq_refl (term170 A B s t)). Qed.
Lemma lem4328663 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term185 A B t s) = (term251 A B t s).
Proof. exact (MK_COMB (@lem4328662 A B s t) (@lem4328660 A B t s)). Qed.
Lemma lem4328674 {A : Type'} (P : A -> Prop) (Q : Prop) : (term252 A P Q) = (term253 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4328675 {B : Type'} (P : B -> Prop) (Q : Prop) : (term252 B P Q) = (term253 B P Q).
Proof. exact (@lem4328674 B P Q). Qed.
Lemma lem4328676 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term250 A B t s) = (term254 A B t s).
Proof. exact (@lem4328675 B t (term239 A s)). Qed.
Lemma lem4328678 {A : Type'} (P : Prop) (Q : A -> Prop) : (term209 A P Q) = (term208 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4328679 {A : Type'} (P : Prop) (Q : A -> Prop) : (term209 A P Q) = (term208 A P Q).
Proof. exact (@lem4328678 A P Q). Qed.
Lemma lem4328680 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) : (term255 A B t x s) = (term256 A B t x s).
Proof. exact (@lem4328679 A (t x) s). Qed.
Lemma lem4328681 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term257 A B t s) = (term258 A B t s).
Proof. exact (fun_ext (fun x : B => @lem4328680 A B t x s)). Qed.
Lemma lem4328682 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4328683 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term254 A B t s) = (term259 A B t s).
Proof. exact (MK_COMB (@lem4328682 B) (@lem4328681 A B t s)). Qed.
Lemma lem4328684 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term250 A B t s) = (term259 A B t s).
Proof. exact (TRANS (@lem4328676 A B t s) (@lem4328683 A B t s)). Qed.
Lemma lem4328685 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term170 A B s t) = (term170 A B s t).
Proof. exact (eq_refl (term170 A B s t)). Qed.
Lemma lem4328686 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term251 A B t s) = (term260 A B t s).
Proof. exact (MK_COMB (@lem4328685 A B s t) (@lem4328684 A B t s)). Qed.
Lemma lem4328688 {A : Type'} (P : Prop) (Q : A -> Prop) : (term209 A P Q) = (term208 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4328689 {B : Type'} (P : Prop) (Q : B -> Prop) : (term209 B P Q) = (term208 B P Q).
Proof. exact (@lem4328688 B P Q). Qed.
Lemma lem4328690 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term261 A B t s) = (term262 A B t s).
Proof. exact (@lem4328689 B (term63 A B s t) (term258 A B t s)). Qed.
Lemma lem4328691 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) : (term263 A B t s x) = (term256 A B t x s).
Proof. exact (eq_refl (term263 A B t s x)). Qed.
Lemma lem4328692 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term264 A B t s) = (term258 A B t s).
Proof. exact (fun_ext (fun x : B => @lem4328691 A B t x s)). Qed.
Lemma lem4328693 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4328694 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term265 A B t s) = (term259 A B t s).
Proof. exact (MK_COMB (@lem4328693 B) (@lem4328692 A B t s)). Qed.
Lemma lem4328695 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term170 A B s t) = (term170 A B s t).
Proof. exact (eq_refl (term170 A B s t)). Qed.
Lemma lem4328696 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term261 A B t s) = (term260 A B t s).
Proof. exact (MK_COMB (@lem4328695 A B s t) (@lem4328694 A B t s)). Qed.
Lemma lem4328697 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4328698 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term266 A B t s) = (term267 A B t s).
Proof. exact (MK_COMB (@lem4328697) (@lem4328696 A B t s)). Qed.
Lemma lem4328699 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) : (term263 A B t s x) = (term256 A B t x s).
Proof. exact (eq_refl (term263 A B t s x)). Qed.
Lemma lem4328700 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term170 A B s t) = (term170 A B s t).
Proof. exact (eq_refl (term170 A B s t)). Qed.
Lemma lem4328701 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) : (term268 A B t s x) = (term269 A B t x s).
Proof. exact (MK_COMB (@lem4328700 A B s t) (@lem4328699 A B t x s)). Qed.
Lemma lem4328702 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term270 A B t s) = (term271 A B t s).
Proof. exact (fun_ext (fun x : B => @lem4328701 A B t x s)). Qed.
Lemma lem4328703 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4328704 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term262 A B t s) = (term272 A B t s).
Proof. exact (MK_COMB (@lem4328703 B) (@lem4328702 A B t s)). Qed.
Lemma lem4328705 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : ((term261 A B t s) = (term262 A B t s)) = ((term260 A B t s) = (term272 A B t s)).
Proof. exact (MK_COMB (@lem4328698 A B t s) (@lem4328704 A B t s)). Qed.
Lemma lem4328706 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term260 A B t s) = (term272 A B t s).
Proof. exact (EQ_MP (@lem4328705 A B t s) (@lem4328690 A B t s)). Qed.
Lemma lem4328708 {A : Type'} (P : Prop) (Q : A -> Prop) : (term209 A P Q) = (term208 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4328709 {A : Type'} (P : Prop) (Q : A -> Prop) : (term209 A P Q) = (term208 A P Q).
Proof. exact (@lem4328708 A P Q). Qed.
Lemma lem4328710 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) : (term273 A B t x s) = (term274 A B t x s).
Proof. exact (@lem4328709 A (term63 A B s t) (term275 A B t x s)). Qed.
Lemma lem4328711 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (x' : A) : (term276 A B t x s x') = (term277 A B t x s x').
Proof. exact (eq_refl (term276 A B t x s x')). Qed.
Lemma lem4328712 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) : (term278 A B t x s) = (term275 A B t x s).
Proof. exact (fun_ext (fun x' : A => @lem4328711 A B t x s x')). Qed.
Lemma lem4328713 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4328714 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) : (term279 A B t x s) = (term256 A B t x s).
Proof. exact (MK_COMB (@lem4328713 A) (@lem4328712 A B t x s)). Qed.
Lemma lem4328715 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term170 A B s t) = (term170 A B s t).
Proof. exact (eq_refl (term170 A B s t)). Qed.
Lemma lem4328716 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) : (term273 A B t x s) = (term269 A B t x s).
Proof. exact (MK_COMB (@lem4328715 A B s t) (@lem4328714 A B t x s)). Qed.
Lemma lem4328717 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4328718 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) : (term280 A B t x s) = (term281 A B t x s).
Proof. exact (MK_COMB (@lem4328717) (@lem4328716 A B t x s)). Qed.
Lemma lem4328719 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (x' : A) : (term276 A B t x s x') = (term277 A B t x s x').
Proof. exact (eq_refl (term276 A B t x s x')). Qed.
Lemma lem4328720 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term170 A B s t) = (term170 A B s t).
Proof. exact (eq_refl (term170 A B s t)). Qed.
Lemma lem4328721 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (x' : A) : (term282 A B t x s x') = (term283 A B t x s x').
Proof. exact (MK_COMB (@lem4328720 A B s t) (@lem4328719 A B t x s x')). Qed.
Lemma lem4328722 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) : (term284 A B t x s) = (term285 A B t x s).
Proof. exact (fun_ext (fun x' : A => @lem4328721 A B t x s x')). Qed.
Lemma lem4328723 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4328724 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) : (term274 A B t x s) = (term286 A B t x s).
Proof. exact (MK_COMB (@lem4328723 A) (@lem4328722 A B t x s)). Qed.
Lemma lem4328725 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) : ((term273 A B t x s) = (term274 A B t x s)) = ((term269 A B t x s) = (term286 A B t x s)).
Proof. exact (MK_COMB (@lem4328718 A B t x s) (@lem4328724 A B t x s)). Qed.
Lemma lem4328726 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) : (term269 A B t x s) = (term286 A B t x s).
Proof. exact (EQ_MP (@lem4328725 A B t x s) (@lem4328710 A B t x s)). Qed.
Lemma lem4328727 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term271 A B t s) = (term287 A B t s).
Proof. exact (fun_ext (fun x : B => @lem4328726 A B t x s)). Qed.
Lemma lem4328728 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4328729 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term272 A B t s) = (term288 A B t s).
Proof. exact (MK_COMB (@lem4328728 B) (@lem4328727 A B t s)). Qed.
Lemma lem4328730 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term260 A B t s) = (term288 A B t s).
Proof. exact (TRANS (@lem4328706 A B t s) (@lem4328729 A B t s)). Qed.
Lemma lem4328732 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term251 A B t s) = (term288 A B t s).
Proof. exact (TRANS (@lem4328686 A B t s) (@lem4328730 A B t s)). Qed.
Lemma lem4328733 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term185 A B t s) = (term288 A B t s).
Proof. exact (TRANS (@lem4328663 A B t s) (@lem4328732 A B t s)). Qed.
Lemma lem4328734 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term185 A B t s) : term288 A B t s.
Proof. exact (EQ_MP (@lem4328733 A B t s) (@lem4328624 A B t s h1)). Qed.
Lemma lem4328740 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem4328744 {B : Type'} (P : B -> Prop) : (term289 B P) = (term181 B P).
Proof. exact (@lem18394 B P). Qed.
Lemma lem4328745 {B : Type'} (t : B -> Prop) : (term290 B t) = (term291 B t).
Proof. exact (@lem4328744 B (term238 B t)). Qed.
Lemma lem4328746 {B : Type'} (t : B -> Prop) (p2 : B) : (term292 B t p2) = (t p2).
Proof. exact (eq_refl (term292 B t p2)). Qed.
Lemma lem4328747 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4328749 {B : Type'} (t : B -> Prop) (p2 : B) : (term293 B t p2) = (term178 B t p2).
Proof. exact (MK_COMB (@lem4328747) (@lem4328746 B t p2)). Qed.
Lemma lem4328750 {B : Type'} (t : B -> Prop) : (term294 B t) = (term180 B t).
Proof. exact (fun_ext (fun p2 : B => @lem4328749 B t p2)). Qed.
Lemma lem4328751 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4328752 {B : Type'} (t : B -> Prop) : (term291 B t) = (term181 B t).
Proof. exact (MK_COMB (@lem4328751 B) (@lem4328750 B t)). Qed.
Lemma lem4328753 {B : Type'} (t : B -> Prop) : (term290 B t) = (term181 B t).
Proof. exact (TRANS (@lem4328745 B t) (@lem4328752 B t)). Qed.
Lemma lem4328755 {A : Type'} (s : A -> Prop) (p1 : A) : (term295 A s p1) = (term295 A s p1).
Proof. exact (eq_refl (term295 A s p1)). Qed.
Lemma lem4328756 {A B : Type'} (s : A -> Prop) (p1 : A) (t : B -> Prop) : (term296 A B s p1 t) = (term297 A B s p1 t).
Proof. exact (MK_COMB (@lem4328755 A s p1) (@lem4328753 B t)). Qed.
Lemma lem4328757 {A B : Type'} (s : A -> Prop) (p1 : A) (t : B -> Prop) : (term298 A B s p1 t) = (term296 A B s p1 t).
Proof. exact (@lem17045 (s p1) (term239 B t)). Qed.
Lemma lem4328758 {A B : Type'} (s : A -> Prop) (p1 : A) (t : B -> Prop) : (term298 A B s p1 t) = (term297 A B s p1 t).
Proof. exact (TRANS (@lem4328757 A B s p1 t) (@lem4328756 A B s p1 t)). Qed.
Lemma lem4328760 {A : Type'} (x : A) (p1 : A) : (term299 A x p1) = (term299 A x p1).
Proof. exact (eq_refl (term299 A x p1)). Qed.
Lemma lem4328761 {A B : Type'} (x : A) (s : A -> Prop) (p1 : A) (t : B -> Prop) : (term300 A B x s p1 t) = (term301 A B x s p1 t).
Proof. exact (MK_COMB (@lem4328760 A x p1) (@lem4328758 A B s p1 t)). Qed.
Lemma lem4328762 {A B : Type'} (x : A) (s : A -> Prop) (p1 : A) (t : B -> Prop) : (term302 A B x s p1 t) = (term300 A B x s p1 t).
Proof. exact (@lem17045 (x = p1) (term222 A B s p1 t)). Qed.
Lemma lem4328763 {A B : Type'} (x : A) (s : A -> Prop) (p1 : A) (t : B -> Prop) : (term302 A B x s p1 t) = (term301 A B x s p1 t).
Proof. exact (TRANS (@lem4328762 A B x s p1 t) (@lem4328761 A B x s p1 t)). Qed.
Lemma lem4328764 {A : Type'} (P : A -> Prop) : (term289 A P) = (term181 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem4328765 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) : (term241 A B x s t) = (term303 A B x s t).
Proof. exact (@lem4328764 A (term224 A B x s t)). Qed.
Lemma lem4328766 {A B : Type'} (x : A) (s : A -> Prop) (p1 : A) (t : B -> Prop) : (term304 A B x s t p1) = (term223 A B x s p1 t).
Proof. exact (eq_refl (term304 A B x s t p1)). Qed.
Lemma lem4328767 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4328768 {A B : Type'} (x : A) (s : A -> Prop) (p1 : A) (t : B -> Prop) : (term305 A B x s t p1) = (term302 A B x s p1 t).
Proof. exact (MK_COMB (@lem4328767) (@lem4328766 A B x s p1 t)). Qed.
Lemma lem4328769 {A B : Type'} (x : A) (s : A -> Prop) (p1 : A) (t : B -> Prop) : (term305 A B x s t p1) = (term301 A B x s p1 t).
Proof. exact (TRANS (@lem4328768 A B x s p1 t) (@lem4328763 A B x s p1 t)). Qed.
Lemma lem4328770 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) : (term306 A B x s t) = (term307 A B x s t).
Proof. exact (fun_ext (fun p1 : A => @lem4328769 A B x s p1 t)). Qed.
Lemma lem4328771 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4328772 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) : (term303 A B x s t) = (term308 A B x s t).
Proof. exact (MK_COMB (@lem4328771 A) (@lem4328770 A B x s t)). Qed.
Lemma lem4328829 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) : (term241 A B x s t) = (term308 A B x s t).
Proof. exact (TRANS (@lem4328765 A B x s t) (@lem4328772 A B x s t)). Qed.
Lemma lem4328830 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (h1 : term241 A B x s t) : term308 A B x s t.
Proof. exact (EQ_MP (@lem4328829 A B x s t) (@lem4328630 A B x s t h1)). Qed.
Lemma lem4328831 {A B : Type'} (t : B -> Prop) (x' : B) (s : A -> Prop) (h1 : term286 A B t x' s) : term286 A B t x' s.
Proof. exact (h1). Qed.
Lemma lem4328832 {A B : Type'} (t : B -> Prop) (x' : B) (s : A -> Prop) (x'' : A) (h1 : term283 A B t x' s x'') : term283 A B t x' s x''.
Proof. exact (h1). Qed.
Lemma lem4328837 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4328838 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4328837 A Prop f x). Qed.
Lemma lem4328840 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem4328838 A s x). Qed.
Lemma lem4328842 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4328847 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4328848 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem4328847 B Prop f x). Qed.
Lemma lem4328850 {B : Type'} (t : B -> Prop) (p2 : B) : (t p2) = (@I (B -> Prop) t p2).
Proof. exact (@lem4328848 B t p2). Qed.
Lemma lem4328851 {B : Type'} (t : B -> Prop) (p2 : B) : (term178 B t p2) = (term309 B t p2).
Proof. exact (MK_COMB (@lem4328842) (@lem4328850 B t p2)). Qed.
Lemma lem4328852 {B : Type'} (t : B -> Prop) : (term180 B t) = (term310 B t).
Proof. exact (fun_ext (fun p2 : B => @lem4328851 B t p2)). Qed.
Lemma lem4328853 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4328854 {B : Type'} (t : B -> Prop) : (term181 B t) = (term311 B t).
Proof. exact (MK_COMB (@lem4328853 B) (@lem4328852 B t)). Qed.
Lemma lem4328855 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4328860 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4328861 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4328860 A Prop f x). Qed.
Lemma lem4328863 {A : Type'} (s : A -> Prop) (p1 : A) : (s p1) = (@I (A -> Prop) s p1).
Proof. exact (@lem4328861 A s p1). Qed.
Lemma lem4328864 {A : Type'} (s : A -> Prop) (p1 : A) : (term178 A s p1) = (term309 A s p1).
Proof. exact (MK_COMB (@lem4328855) (@lem4328863 A s p1)). Qed.
Lemma lem4328865 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4328866 {A : Type'} (s : A -> Prop) (p1 : A) : (term295 A s p1) = (term312 A s p1).
Proof. exact (MK_COMB (@lem4328865) (@lem4328864 A s p1)). Qed.
Lemma lem4328867 {A B : Type'} (s : A -> Prop) (p1 : A) (t : B -> Prop) : (term297 A B s p1 t) = (term313 A B s p1 t).
Proof. exact (MK_COMB (@lem4328866 A s p1) (@lem4328854 B t)). Qed.
Lemma lem4328876 {A : Type'} (x : A) (p1 : A) : (term299 A x p1) = (term299 A x p1).
Proof. exact (eq_refl (term299 A x p1)). Qed.
Lemma lem4328877 {A B : Type'} (x : A) (s : A -> Prop) (p1 : A) (t : B -> Prop) : (term301 A B x s p1 t) = (term314 A B x s p1 t).
Proof. exact (MK_COMB (@lem4328876 A x p1) (@lem4328867 A B s p1 t)). Qed.
Lemma lem4328878 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) : (term307 A B x s t) = (term315 A B x s t).
Proof. exact (fun_ext (fun p1 : A => @lem4328877 A B x s p1 t)). Qed.
Lemma lem4328879 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4328880 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) : (term308 A B x s t) = (term316 A B x s t).
Proof. exact (MK_COMB (@lem4328879 A) (@lem4328878 A B x s t)). Qed.
Lemma lem4328881 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (h1 : term241 A B x s t) : term316 A B x s t.
Proof. exact (EQ_MP (@lem4328880 A B x s t) (@lem4328830 A B x s t h1)). Qed.
Lemma lem4328886 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4328887 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4328886 A Prop f x). Qed.
Lemma lem4328889 {A : Type'} (s : A -> Prop) (x'' : A) : (s x'') = (@I (A -> Prop) s x'').
Proof. exact (@lem4328887 A s x''). Qed.
Lemma lem4328894 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4328895 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem4328894 B Prop f x). Qed.
Lemma lem4328897 {B : Type'} (t : B -> Prop) (x' : B) : (t x') = (@I (B -> Prop) t x').
Proof. exact (@lem4328895 B t x'). Qed.
Lemma lem4328898 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4328899 {B : Type'} (t : B -> Prop) (x' : B) : (term189 B t x') = (term317 B t x').
Proof. exact (MK_COMB (@lem4328898) (@lem4328897 B t x')). Qed.
Lemma lem4328900 {A B : Type'} (t : B -> Prop) (x' : B) (s : A -> Prop) (x'' : A) : (term277 A B t x' s x'') = (term318 A B t x' s x'').
Proof. exact (MK_COMB (@lem4328899 B t x') (@lem4328889 A s x'')). Qed.
Lemma lem4328909 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term170 A B s t) = (term170 A B s t).
Proof. exact (eq_refl (term170 A B s t)). Qed.
Lemma lem4328910 {A B : Type'} (t : B -> Prop) (x' : B) (s : A -> Prop) (x'' : A) : (term283 A B t x' s x'') = (term319 A B t x' s x'').
Proof. exact (MK_COMB (@lem4328909 A B s t) (@lem4328900 A B t x' s x'')). Qed.
Lemma lem4328911 {A B : Type'} (t : B -> Prop) (x' : B) (s : A -> Prop) (x'' : A) (h1 : term283 A B t x' s x'') : term319 A B t x' s x''.
Proof. exact (EQ_MP (@lem4328910 A B t x' s x'') (@lem4328832 A B t x' s x'' h1)). Qed.
Lemma lem4328912 {A B : Type'} (t : B -> Prop) (x' : B) (s : A -> Prop) (x'' : A) (h1 : term283 A B t x' s x'') : term318 A B t x' s x''.
Proof. exact (proj2 (@lem4328911 A B t x' s x'' h1)). Qed.
Lemma lem4328921 {A : Type'} (P : Prop) (Q : A -> Prop) : (term320 A P Q) = (term321 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem4328922 {B : Type'} (P : Prop) (Q : B -> Prop) : (term320 B P Q) = (term321 B P Q).
Proof. exact (@lem4328921 B P Q). Qed.
Lemma lem4328923 {A B : Type'} (s : A -> Prop) (p1 : A) (t : B -> Prop) : (term322 A B s p1 t) = (term323 A B s p1 t).
Proof. exact (@lem4328922 B (term309 A s p1) (term310 B t)). Qed.
Lemma lem4328924 {B : Type'} (t : B -> Prop) (p2 : B) : (term324 B t p2) = (term309 B t p2).
Proof. exact (eq_refl (term324 B t p2)). Qed.
Lemma lem4328925 {B : Type'} (t : B -> Prop) : (term325 B t) = (term310 B t).
Proof. exact (fun_ext (fun p2 : B => @lem4328924 B t p2)). Qed.
Lemma lem4328926 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4328927 {B : Type'} (t : B -> Prop) : (term326 B t) = (term311 B t).
Proof. exact (MK_COMB (@lem4328926 B) (@lem4328925 B t)). Qed.
Lemma lem4328928 {A : Type'} (s : A -> Prop) (p1 : A) : (term312 A s p1) = (term312 A s p1).
Proof. exact (eq_refl (term312 A s p1)). Qed.
Lemma lem4328929 {A B : Type'} (s : A -> Prop) (p1 : A) (t : B -> Prop) : (term322 A B s p1 t) = (term313 A B s p1 t).
Proof. exact (MK_COMB (@lem4328928 A s p1) (@lem4328927 B t)). Qed.
Lemma lem4328930 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4328931 {A B : Type'} (s : A -> Prop) (p1 : A) (t : B -> Prop) : (term327 A B s p1 t) = (term328 A B s p1 t).
Proof. exact (MK_COMB (@lem4328930) (@lem4328929 A B s p1 t)). Qed.
Lemma lem4328932 {B : Type'} (t : B -> Prop) (p2 : B) : (term324 B t p2) = (term309 B t p2).
Proof. exact (eq_refl (term324 B t p2)). Qed.
Lemma lem4328933 {A : Type'} (s : A -> Prop) (p1 : A) : (term312 A s p1) = (term312 A s p1).
Proof. exact (eq_refl (term312 A s p1)). Qed.
Lemma lem4328934 {A B : Type'} (s : A -> Prop) (p1 : A) (t : B -> Prop) (p2 : B) : (term329 A B s p1 t p2) = (term330 A B s p1 t p2).
Proof. exact (MK_COMB (@lem4328933 A s p1) (@lem4328932 B t p2)). Qed.
Lemma lem4328935 {A B : Type'} (s : A -> Prop) (p1 : A) (t : B -> Prop) : (term331 A B s p1 t) = (term332 A B s p1 t).
Proof. exact (fun_ext (fun p2 : B => @lem4328934 A B s p1 t p2)). Qed.
Lemma lem4328936 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4328937 {A B : Type'} (s : A -> Prop) (p1 : A) (t : B -> Prop) : (term323 A B s p1 t) = (term333 A B s p1 t).
Proof. exact (MK_COMB (@lem4328936 B) (@lem4328935 A B s p1 t)). Qed.
Lemma lem4328938 {A B : Type'} (s : A -> Prop) (p1 : A) (t : B -> Prop) : ((term322 A B s p1 t) = (term323 A B s p1 t)) = ((term313 A B s p1 t) = (term333 A B s p1 t)).
Proof. exact (MK_COMB (@lem4328931 A B s p1 t) (@lem4328937 A B s p1 t)). Qed.
Lemma lem4328939 {A B : Type'} (s : A -> Prop) (p1 : A) (t : B -> Prop) : (term313 A B s p1 t) = (term333 A B s p1 t).
Proof. exact (EQ_MP (@lem4328938 A B s p1 t) (@lem4328923 A B s p1 t)). Qed.
Lemma lem4328940 {A : Type'} (x : A) (p1 : A) : (term299 A x p1) = (term299 A x p1).
Proof. exact (eq_refl (term299 A x p1)). Qed.
Lemma lem4328941 {A B : Type'} (x : A) (s : A -> Prop) (p1 : A) (t : B -> Prop) : (term314 A B x s p1 t) = (term334 A B x s p1 t).
Proof. exact (MK_COMB (@lem4328940 A x p1) (@lem4328939 A B s p1 t)). Qed.
Lemma lem4328943 {A : Type'} (P : Prop) (Q : A -> Prop) : (term320 A P Q) = (term321 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem4328944 {B : Type'} (P : Prop) (Q : B -> Prop) : (term320 B P Q) = (term321 B P Q).
Proof. exact (@lem4328943 B P Q). Qed.
Lemma lem4328945 {A B : Type'} (x : A) (s : A -> Prop) (p1 : A) (t : B -> Prop) : (term335 A B x s p1 t) = (term336 A B x s p1 t).
Proof. exact (@lem4328944 B (term337 A x p1) (term332 A B s p1 t)). Qed.
Lemma lem4328946 {A B : Type'} (s : A -> Prop) (p1 : A) (t : B -> Prop) (p2 : B) : (term338 A B s p1 t p2) = (term330 A B s p1 t p2).
Proof. exact (eq_refl (term338 A B s p1 t p2)). Qed.
Lemma lem4328947 {A B : Type'} (s : A -> Prop) (p1 : A) (t : B -> Prop) : (term339 A B s p1 t) = (term332 A B s p1 t).
Proof. exact (fun_ext (fun p2 : B => @lem4328946 A B s p1 t p2)). Qed.
Lemma lem4328948 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4328949 {A B : Type'} (s : A -> Prop) (p1 : A) (t : B -> Prop) : (term340 A B s p1 t) = (term333 A B s p1 t).
Proof. exact (MK_COMB (@lem4328948 B) (@lem4328947 A B s p1 t)). Qed.
Lemma lem4328950 {A : Type'} (x : A) (p1 : A) : (term299 A x p1) = (term299 A x p1).
Proof. exact (eq_refl (term299 A x p1)). Qed.
Lemma lem4328951 {A B : Type'} (x : A) (s : A -> Prop) (p1 : A) (t : B -> Prop) : (term335 A B x s p1 t) = (term334 A B x s p1 t).
Proof. exact (MK_COMB (@lem4328950 A x p1) (@lem4328949 A B s p1 t)). Qed.
Lemma lem4328952 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4328953 {A B : Type'} (x : A) (s : A -> Prop) (p1 : A) (t : B -> Prop) : (term341 A B x s p1 t) = (term342 A B x s p1 t).
Proof. exact (MK_COMB (@lem4328952) (@lem4328951 A B x s p1 t)). Qed.
Lemma lem4328954 {A B : Type'} (s : A -> Prop) (p1 : A) (t : B -> Prop) (p2 : B) : (term338 A B s p1 t p2) = (term330 A B s p1 t p2).
Proof. exact (eq_refl (term338 A B s p1 t p2)). Qed.
Lemma lem4328955 {A : Type'} (x : A) (p1 : A) : (term299 A x p1) = (term299 A x p1).
Proof. exact (eq_refl (term299 A x p1)). Qed.
Lemma lem4328956 {A B : Type'} (x : A) (s : A -> Prop) (p1 : A) (t : B -> Prop) (p2 : B) : (term343 A B x s p1 t p2) = (term344 A B x s p1 t p2).
Proof. exact (MK_COMB (@lem4328955 A x p1) (@lem4328954 A B s p1 t p2)). Qed.
Lemma lem4328957 {A B : Type'} (x : A) (s : A -> Prop) (p1 : A) (t : B -> Prop) : (term345 A B x s p1 t) = (term346 A B x s p1 t).
Proof. exact (fun_ext (fun p2 : B => @lem4328956 A B x s p1 t p2)). Qed.
Lemma lem4328958 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4328959 {A B : Type'} (x : A) (s : A -> Prop) (p1 : A) (t : B -> Prop) : (term336 A B x s p1 t) = (term347 A B x s p1 t).
Proof. exact (MK_COMB (@lem4328958 B) (@lem4328957 A B x s p1 t)). Qed.
Lemma lem4328960 {A B : Type'} (x : A) (s : A -> Prop) (p1 : A) (t : B -> Prop) : ((term335 A B x s p1 t) = (term336 A B x s p1 t)) = ((term334 A B x s p1 t) = (term347 A B x s p1 t)).
Proof. exact (MK_COMB (@lem4328953 A B x s p1 t) (@lem4328959 A B x s p1 t)). Qed.
Lemma lem4328961 {A B : Type'} (x : A) (s : A -> Prop) (p1 : A) (t : B -> Prop) : (term334 A B x s p1 t) = (term347 A B x s p1 t).
Proof. exact (EQ_MP (@lem4328960 A B x s p1 t) (@lem4328945 A B x s p1 t)). Qed.
Lemma lem4328962 {A B : Type'} (x : A) (s : A -> Prop) (p1 : A) (t : B -> Prop) : (term314 A B x s p1 t) = (term347 A B x s p1 t).
Proof. exact (TRANS (@lem4328941 A B x s p1 t) (@lem4328961 A B x s p1 t)). Qed.
Lemma lem4328963 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) : (term315 A B x s t) = (term348 A B x s t).
Proof. exact (fun_ext (fun p1 : A => @lem4328962 A B x s p1 t)). Qed.
Lemma lem4328964 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4328965 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) : (term316 A B x s t) = (term349 A B x s t).
Proof. exact (MK_COMB (@lem4328964 A) (@lem4328963 A B x s t)). Qed.
Lemma lem4328978 {A B : Type'} (x : A) (s : A -> Prop) (p1 : A) (t : B -> Prop) (p2 : B) : (term344 A B x s p1 t p2) = (term344 A B x s p1 t p2).
Proof. exact (eq_refl (term344 A B x s p1 t p2)). Qed.
Lemma lem4328979 {A B : Type'} (x : A) (s : A -> Prop) (p1 : A) (t : B -> Prop) : (term346 A B x s p1 t) = (term346 A B x s p1 t).
Proof. exact (fun_ext (fun p2 : B => @lem4328978 A B x s p1 t p2)). Qed.
Lemma lem4328980 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4328981 {A B : Type'} (x : A) (s : A -> Prop) (p1 : A) (t : B -> Prop) : (term347 A B x s p1 t) = (term347 A B x s p1 t).
Proof. exact (MK_COMB (@lem4328980 B) (@lem4328979 A B x s p1 t)). Qed.
Lemma lem4328982 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) : (term348 A B x s t) = (term348 A B x s t).
Proof. exact (fun_ext (fun p1 : A => @lem4328981 A B x s p1 t)). Qed.
Lemma lem4328983 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4328984 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) : (term349 A B x s t) = (term349 A B x s t).
Proof. exact (MK_COMB (@lem4328983 A) (@lem4328982 A B x s t)). Qed.
Lemma lem4328985 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) : (term316 A B x s t) = (term349 A B x s t).
Proof. exact (TRANS (@lem4328965 A B x s t) (@lem4328984 A B x s t)). Qed.
Lemma lem4328986 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (h1 : term241 A B x s t) : term349 A B x s t.
Proof. exact (EQ_MP (@lem4328985 A B x s t) (@lem4328881 A B x s t h1)). Qed.
Lemma lem4328999 {A B : Type'} (_49294 : A) (x : A) (s : A -> Prop) (t : B -> Prop) (h1 : term241 A B x s t) : term350 A B x s t _49294.
Proof. exact (@lem4328986 A B x s t h1 _49294). Qed.
Lemma lem4329000 {A B : Type'} (x : A) (s : A -> Prop) (_49294 : A) (t : B -> Prop) : (term350 A B x s t _49294) = (term347 A B x s _49294 t).
Proof. exact (eq_refl (term350 A B x s t _49294)). Qed.
Lemma lem4329001 {A B : Type'} (_49294 : A) (x : A) (s : A -> Prop) (t : B -> Prop) (h1 : term241 A B x s t) : term347 A B x s _49294 t.
Proof. exact (EQ_MP (@lem4329000 A B x s _49294 t) (@lem4328999 A B _49294 x s t h1)). Qed.
Lemma lem4329002 {A B : Type'} (_49294 : A) (_49295 : B) (x : A) (s : A -> Prop) (t : B -> Prop) (h1 : term241 A B x s t) : term351 A B x s _49294 t _49295.
Proof. exact (@lem4329001 A B _49294 x s t h1 _49295). Qed.
Lemma lem4329003 {A B : Type'} (x : A) (s : A -> Prop) (_49294 : A) (t : B -> Prop) (_49295 : B) : (term351 A B x s _49294 t _49295) = (term344 A B x s _49294 t _49295).
Proof. exact (eq_refl (term351 A B x s _49294 t _49295)). Qed.
Lemma lem4329016 {A B : Type'} (_49294 : A) (_49295 : B) (x : A) (s : A -> Prop) (t : B -> Prop) (h1 : term241 A B x s t) : term344 A B x s _49294 t _49295.
Proof. exact (EQ_MP (@lem4329003 A B x s _49294 t _49295) (@lem4329002 A B _49294 _49295 x s t h1)). Qed.
Lemma lem4329099 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem4329100 {A : Type'} (x : A) : x = x.
Proof. exact (@lem4329099 A x). Qed.
Lemma lem4329101 {A : Type'} (x : A) : term352 A x.
Proof. exact (fun h0 : term353 A x => @lem4329100 A x). Qed.
Lemma lem4329103 (p : Prop) : (term354 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4329104 {A : Type'} (x : A) : (term352 A x) = (x = x).
Proof. exact (@lem4329103 (x = x)). Qed.
Lemma lem4329105 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem4329104 A x) (@lem4329101 A x)). Qed.
Lemma lem4329107 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : @I (A -> Prop) s x.
Proof. exact (EQ_MP (@lem4328840 A s x) (@lem4328740 A s x h1)). Qed.
Lemma lem4329108 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : term355 A s x.
Proof. exact (fun h0 : term309 A s x => @lem4329107 A s x h1). Qed.
Lemma lem4329110 (p : Prop) : (term354 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4329111 {A : Type'} (s : A -> Prop) (x : A) : (term355 A s x) = (@I (A -> Prop) s x).
Proof. exact (@lem4329110 (@I (A -> Prop) s x)). Qed.
Lemma lem4329112 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : @I (A -> Prop) s x.
Proof. exact (EQ_MP (@lem4329111 A s x) (@lem4329108 A s x h1)). Qed.
Lemma lem4329114 {A B : Type'} (t : B -> Prop) (x' : B) (s : A -> Prop) (x'' : A) (h1 : term283 A B t x' s x'') : @I (B -> Prop) t x'.
Proof. exact (proj1 (@lem4328912 A B t x' s x'' h1)). Qed.
Lemma lem4329115 {A B : Type'} (t : B -> Prop) (x' : B) (s : A -> Prop) (x'' : A) (h1 : term283 A B t x' s x'') : term355 B t x'.
Proof. exact (fun h0 : term309 B t x' => @lem4329114 A B t x' s x'' h1). Qed.
Lemma lem4329117 (p : Prop) : (term354 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4329118 {B : Type'} (t : B -> Prop) (x' : B) : (term355 B t x') = (@I (B -> Prop) t x').
Proof. exact (@lem4329117 (@I (B -> Prop) t x')). Qed.
Lemma lem4329119 {A B : Type'} (t : B -> Prop) (x' : B) (s : A -> Prop) (x'' : A) (h1 : term283 A B t x' s x'') : @I (B -> Prop) t x'.
Proof. exact (EQ_MP (@lem4329118 B t x') (@lem4329115 A B t x' s x'' h1)). Qed.
Lemma lem4329121 (a : Prop) (b : Prop) : (term356 a b) = (term357 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4329122 {A B : Type'} (s : A -> Prop) (_49294 : A) (t : B -> Prop) (_49295 : B) : (term330 A B s _49294 t _49295) = (term358 A B s _49294 t _49295).
Proof. exact (@lem4329121 (@I (A -> Prop) s _49294) (@I (B -> Prop) t _49295)). Qed.
Lemma lem4329123 {A : Type'} (x : A) (_49294 : A) : (term299 A x _49294) = (term299 A x _49294).
Proof. exact (eq_refl (term299 A x _49294)). Qed.
Lemma lem4329124 {A B : Type'} (x : A) (s : A -> Prop) (_49294 : A) (t : B -> Prop) (_49295 : B) : (term344 A B x s _49294 t _49295) = (term359 A B x s _49294 t _49295).
Proof. exact (MK_COMB (@lem4329123 A x _49294) (@lem4329122 A B s _49294 t _49295)). Qed.
Lemma lem4329126 (a : Prop) (b : Prop) : (term356 a b) = (term357 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4329127 {A B : Type'} (x : A) (s : A -> Prop) (_49294 : A) (t : B -> Prop) (_49295 : B) : (term359 A B x s _49294 t _49295) = (term360 A B x s _49294 t _49295).
Proof. exact (@lem4329126 (x = _49294) (term361 A B s _49294 t _49295)). Qed.
Lemma lem4329128 {A B : Type'} (x : A) (s : A -> Prop) (_49294 : A) (t : B -> Prop) (_49295 : B) : (term344 A B x s _49294 t _49295) = (term360 A B x s _49294 t _49295).
Proof. exact (TRANS (@lem4329124 A B x s _49294 t _49295) (@lem4329127 A B x s _49294 t _49295)). Qed.
Lemma lem4329130 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4329131 {A B : Type'} (x : A) (s : A -> Prop) (_49294 : A) (t : B -> Prop) (_49295 : B) : (term360 A B x s _49294 t _49295) = (term362 A B x s _49294 t _49295).
Proof. exact (@lem4329130 (term363 A B x s _49294 t _49295)). Qed.
Lemma lem4329132 {A B : Type'} (x : A) (s : A -> Prop) (_49294 : A) (t : B -> Prop) (_49295 : B) : (term344 A B x s _49294 t _49295) = (term362 A B x s _49294 t _49295).
Proof. exact (TRANS (@lem4329128 A B x s _49294 t _49295) (@lem4329131 A B x s _49294 t _49295)). Qed.
Lemma lem4329134 {A B : Type'} (x : A) (t : B -> Prop) (x' : B) (s : A -> Prop) (x'' : A) (h1 : s x) (h2 : term283 A B t x' s x'') : term361 A B s x t x'.
Proof. exact (conj (@lem4329112 A s x h1) (@lem4329119 A B t x' s x'' h2)). Qed.
Lemma lem4329135 {A B : Type'} (x : A) (t : B -> Prop) (x' : B) (s : A -> Prop) (x'' : A) (h1 : s x) (h2 : term283 A B t x' s x'') : term364 A B s x t x'.
Proof. exact (conj (@lem4329105 A x) (@lem4329134 A B x t x' s x'' h1 h2)). Qed.
Lemma lem4329137 {A B : Type'} (_49294 : A) (_49295 : B) (x : A) (s : A -> Prop) (t : B -> Prop) (h1 : term241 A B x s t) : term362 A B x s _49294 t _49295.
Proof. exact (EQ_MP (@lem4329132 A B x s _49294 t _49295) (@lem4329016 A B _49294 _49295 x s t h1)). Qed.
Lemma lem4329138 {A B : Type'} (_49294 : A) (_49295 : B) (x : A) (s : A -> Prop) (t : B -> Prop) (h1 : term241 A B x s t) : term362 A B x s _49294 t _49295.
Proof. exact (@lem4329137 A B _49294 _49295 x s t h1). Qed.
Lemma lem4329139 {A B : Type'} (x' : B) (x : A) (s : A -> Prop) (t : B -> Prop) (h1 : term241 A B x s t) : term365 A B s x t x'.
Proof. exact (@lem4329138 A B x x' x s t h1). Qed.
Lemma lem4329142 {A B : Type'} (x : A) (t : B -> Prop) (x' : B) (s : A -> Prop) (x'' : A) (h1 : term241 A B x s t) (h2 : s x) (h3 : term283 A B t x' s x'') : False.
Proof. exact (@lem4329139 A B x' x s t h1 (@lem4329135 A B x t x' s x'' h2 h3)). Qed.
Lemma lem4329143 {A B : Type'} (x : A) (t : B -> Prop) (x' : B) (s : A -> Prop) (x'' : A) (h1 : term241 A B x s t) (h2 : s x) (h3 : term283 A B t x' s x'') : term366.
Proof. exact (fun h0 : ~ False => @lem4329142 A B x t x' s x'' h1 h2 h3). Qed.
Lemma lem4329145 (p : Prop) : (term354 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4329146 : term366 = False.
Proof. exact (@lem4329145 False). Qed.
Lemma lem4329147 {A B : Type'} (x : A) (t : B -> Prop) (x' : B) (s : A -> Prop) (x'' : A) (h1 : term241 A B x s t) (h2 : s x) (h3 : term283 A B t x' s x'') : False.
Proof. exact (EQ_MP (@lem4329146) (@lem4329143 A B x t x' s x'' h1 h2 h3)). Qed.
Lemma lem4329148 {A B : Type'} (x' : B) (t : B -> Prop) (s : A -> Prop) (x : A) (h1 : term286 A B t x' s) (h2 : term241 A B x s t) (h3 : s x) : False.
Proof. exact (ex_elim (@lem4328831 A B t x' s h1) (fun x'' : A => fun h0 : term285 A B t x' s x'' => @lem4329147 A B x t x' s x'' h2 h3 h0)). Qed.
Lemma lem4329149 {A B : Type'} (x : A) (t : B -> Prop) (s : A -> Prop) (h1 : term241 A B x s t) (h2 : s x) (h3 : term185 A B t s) : False.
Proof. exact (ex_elim (@lem4328734 A B t s h3) (fun x' : B => fun h0 : term287 A B t s x' => @lem4329148 A B x' t s x h0 h1 h2)). Qed.
Lemma lem4329150 {A B : Type'} (x : A) (t : B -> Prop) (s : A -> Prop) (h1 : term241 A B x s t) (h2 : s x) (h3 : term185 A B t s) : (s x) = False.
Proof. exact (prop_ext (fun h4 : s x => @lem4329149 A B x t s h1 h2 h3) (fun h4 : False => @lem4328740 A s x h2)). Qed.
Lemma lem4329151 {A B : Type'} (x : A) (t : B -> Prop) (s : A -> Prop) (h1 : term241 A B x s t) (h2 : s x) (h3 : term185 A B t s) : False.
Proof. exact (EQ_MP (@lem4329150 A B x t s h1 h2 h3) (@lem4328740 A s x h2)). Qed.
Lemma lem4329152 {A B : Type'} (x : A) (t : B -> Prop) (s : A -> Prop) (h1 : term241 A B x s t) (h2 : s x) (h3 : term185 A B t s) : (term241 A B x s t) = False.
Proof. exact (prop_ext (fun h4 : term241 A B x s t => @lem4329151 A B x t s h1 h2 h3) (fun h4 : False => @lem4328630 A B x s t h1)). Qed.
Lemma lem4329153 {A B : Type'} (x : A) (t : B -> Prop) (s : A -> Prop) (h1 : term241 A B x s t) (h2 : s x) (h3 : term185 A B t s) : False.
Proof. exact (EQ_MP (@lem4329152 A B x t s h1 h2 h3) (@lem4328630 A B x s t h1)). Qed.
Lemma lem4329154 {A B : Type'} (x : A) (t : B -> Prop) (s : A -> Prop) (h1 : s x) (h2 : term185 A B t s) : term240 A B x s t.
Proof. exact (fun h0 : term241 A B x s t => @lem4329153 A B x t s h0 h1 h2). Qed.
Lemma lem4329155 {A B : Type'} (x : A) (t : B -> Prop) (s : A -> Prop) (h1 : s x) (h2 : term185 A B t s) : term225 A B x s t.
Proof. exact (EQ_MP (@lem4328629 A B x s t) (@lem4329154 A B x t s h1 h2)). Qed.
Lemma lem4329156 {A B : Type'} (x : A) (t : B -> Prop) (s : A -> Prop) (h1 : term185 A B t s) : term226 A B x s t.
Proof. exact (fun h0 : s x => @lem4329155 A B x t s h0 h1). Qed.
Lemma lem4329161 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term185 A B t s) : term228 A B s t.
Proof. exact (fun x : A => @lem4329156 A B x t s h1). Qed.
Lemma lem4329162 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term229 A B s t.
Proof. exact (fun h0 : term185 A B t s => @lem4329161 A B t s h0). Qed.
Lemma lem4329167 {A B : Type'} (t : B -> Prop) : term233 A B t.
Proof. exact (fun s : A -> Prop => @lem4329162 A B s t). Qed.
Lemma lem4329172 {A B : Type'} : term237 A B.
Proof. exact (fun t : B -> Prop => @lem4329167 A B t). Qed.
Lemma lem4329173 {A B : Type'} : term236 A B.
Proof. exact (EQ_MP (@lem4328623 A B) (@lem4329172 A B)). Qed.
Lemma lem4329174 {A B : Type'} (t : B -> Prop) : term367 A B t.
Proof. exact (@lem4329173 A B t). Qed.
Lemma lem4329175 {A B : Type'} (t : B -> Prop) : (term367 A B t) = (term232 A B t).
Proof. exact (eq_refl (term367 A B t)). Qed.
Lemma lem4329176 {A B : Type'} (t : B -> Prop) : term232 A B t.
Proof. exact (EQ_MP (@lem4329175 A B t) (@lem4329174 A B t)). Qed.
Lemma lem4329177 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : term368 A B t s.
Proof. exact (@lem4329176 A B t s). Qed.
Lemma lem4329178 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term368 A B t s) = (term201 A B s t).
Proof. exact (eq_refl (term368 A B t s)). Qed.
Lemma lem4329179 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term201 A B s t.
Proof. exact (EQ_MP (@lem4329178 A B s t) (@lem4329177 A B t s)). Qed.
Lemma lem4329181 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term201 A B s t.
Proof. exact (@lem4328350 A B s t (@lem4329179 A B s t)). Qed.
Lemma lem4329182 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term202 A B s t) : False.
Proof. exact (@lem4329181 A B s t (@lem4328334 A B s t h1)). Qed.
Lemma lem4329183 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term202 A B s t) : (term202 A B s t) = False.
Proof. exact (prop_ext (fun h2 : term202 A B s t => @lem4329182 A B s t h1) (fun h2 : False => @lem4328334 A B s t h1)). Qed.
Lemma lem4329184 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term202 A B s t) : False.
Proof. exact (EQ_MP (@lem4329183 A B s t h1) (@lem4328334 A B s t h1)). Qed.
Lemma lem4329185 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term201 A B s t.
Proof. exact (fun h0 : term202 A B s t => @lem4329184 A B s t h0). Qed.
Lemma lem4329186 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term199 A B s t.
Proof. exact (EQ_MP (@lem4328333 A B s t) (@lem4329185 A B s t)). Qed.
Lemma lem4329187 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term175 A B s t.
Proof. exact (EQ_MP (@lem4328329 A B s t) (@lem4329186 A B s t)). Qed.
Lemma lem4329188 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term174 A B s t.
Proof. exact (EQ_MP (@lem4328183 A B s t) (@lem4329187 A B s t)). Qed.
Lemma lem4329189 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term63 A B s t) (h2 : term60 A s) (h3 : term60 B t) : term126 A B s t.
Proof. exact (@lem4329188 A B s t (@lem4328107 A B s t h1 h2 h3)). Qed.
Lemma lem4329200 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term60 A s) (h2 : term60 B t) : term162 A B t s.
Proof. exact (conj (@lem4327566 B t h2) (@lem4327571 A s h1)). Qed.
Lemma lem4329201 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term63 A B s t) (h2 : term60 A s) (h3 : term60 B t) : term163 A B t s.
Proof. exact (conj (@lem4327867 A B s t h1) (@lem4329200 A B s t h2 h3)). Qed.
Lemma lem4329211 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term164 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem4329212 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (s = t) = (term164 B s t).
Proof. exact (@lem4329211 B s t). Qed.
Lemma lem4329213 {B : Type'} (t : B -> Prop) : (t = (@EMPTY B)) = (term165 B t).
Proof. exact (@lem4329212 B t (@EMPTY B)). Qed.
Lemma lem4329222 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4329223 {B : Type'} (t : B -> Prop) : (term60 B t) = (term166 B t).
Proof. exact (MK_COMB (@lem4329222) (@lem4329213 B t)). Qed.
Lemma lem4329224 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4329225 {B : Type'} (t : B -> Prop) : (term167 B t) = (term168 B t).
Proof. exact (MK_COMB (@lem4329224) (@lem4329223 B t)). Qed.
Lemma lem4329229 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term164 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem4329230 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term164 A s t).
Proof. exact (@lem4329229 A s t). Qed.
Lemma lem4329231 {A : Type'} (s : A -> Prop) : (s = (@EMPTY A)) = (term165 A s).
Proof. exact (@lem4329230 A s (@EMPTY A)). Qed.
Lemma lem4329240 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4329241 {A : Type'} (s : A -> Prop) : (term60 A s) = (term166 A s).
Proof. exact (MK_COMB (@lem4329240) (@lem4329231 A s)). Qed.
Lemma lem4329242 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term162 A B t s) = (term169 A B t s).
Proof. exact (MK_COMB (@lem4329225 B t) (@lem4329241 A s)). Qed.
Lemma lem4329245 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term170 A B s t) = (term170 A B s t).
Proof. exact (eq_refl (term170 A B s t)). Qed.
Lemma lem4329246 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term163 A B t s) = (term171 A B t s).
Proof. exact (MK_COMB (@lem4329245 A B s t) (@lem4329242 A B t s)). Qed.
Lemma lem4329249 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4329250 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term172 A B t s) = (term173 A B t s).
Proof. exact (MK_COMB (@lem4329249) (@lem4329246 A B t s)). Qed.
Lemma lem4329273 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term161 A B s t) = (term161 A B s t).
Proof. exact (eq_refl (term161 A B s t)). Qed.
Lemma lem4329274 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term369 A B s t) = (term370 A B s t).
Proof. exact (MK_COMB (@lem4329250 A B t s) (@lem4329273 A B s t)). Qed.
Lemma lem4329277 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term370 A B s t) = (term369 A B s t).
Proof. exact (SYM (@lem4329274 A B s t)). Qed.
Lemma lem4329291 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4329292 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem4329291 B P x). Qed.
Lemma lem4329293 {B : Type'} (t : B -> Prop) (x : B) : (@IN B x t) = (t x).
Proof. exact (@lem4329292 B t x). Qed.
Lemma lem4329294 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4329295 {B : Type'} (t : B -> Prop) (x : B) : (term176 B x t) = (term177 B t x).
Proof. exact (MK_COMB (@lem4329294) (@lem4329293 B t x)). Qed.
Lemma lem4329297 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem4329298 {B : Type'} (x : B) : (@IN B x (@EMPTY B)) = False.
Proof. exact (@lem4329297 B x). Qed.
Lemma lem4329299 {B : Type'} (t : B -> Prop) (x : B) : ((@IN B x t) = (@IN B x (@EMPTY B))) = ((t x) = False).
Proof. exact (MK_COMB (@lem4329295 B t x) (@lem4329298 B x)). Qed.
Lemma lem4329301 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem4329302 {B : Type'} (t : B -> Prop) (x : B) : ((t x) = False) = (term178 B t x).
Proof. exact (@lem4329301 (t x)). Qed.
Lemma lem4329303 {B : Type'} (t : B -> Prop) (x : B) : ((@IN B x t) = (@IN B x (@EMPTY B))) = (term178 B t x).
Proof. exact (TRANS (@lem4329299 B t x) (@lem4329302 B t x)). Qed.
Lemma lem4329304 {B : Type'} (t : B -> Prop) : (term179 B t) = (term180 B t).
Proof. exact (fun_ext (fun x : B => @lem4329303 B t x)). Qed.
Lemma lem4329305 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4329306 {B : Type'} (t : B -> Prop) : (term165 B t) = (term181 B t).
Proof. exact (MK_COMB (@lem4329305 B) (@lem4329304 B t)). Qed.
Lemma lem4329311 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4329312 {B : Type'} (t : B -> Prop) : (term166 B t) = (term182 B t).
Proof. exact (MK_COMB (@lem4329311) (@lem4329306 B t)). Qed.
Lemma lem4329313 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4329314 {B : Type'} (t : B -> Prop) : (term168 B t) = (term183 B t).
Proof. exact (MK_COMB (@lem4329313) (@lem4329312 B t)). Qed.
Lemma lem4329322 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4329323 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4329322 A P x). Qed.
Lemma lem4329324 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4329323 A s x). Qed.
Lemma lem4329325 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4329326 {A : Type'} (s : A -> Prop) (x : A) : (term176 A x s) = (term177 A s x).
Proof. exact (MK_COMB (@lem4329325) (@lem4329324 A s x)). Qed.
Lemma lem4329328 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem4329329 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4329328 A x). Qed.
Lemma lem4329330 {A : Type'} (s : A -> Prop) (x : A) : ((@IN A x s) = (@IN A x (@EMPTY A))) = ((s x) = False).
Proof. exact (MK_COMB (@lem4329326 A s x) (@lem4329329 A x)). Qed.
Lemma lem4329332 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem4329333 {A : Type'} (s : A -> Prop) (x : A) : ((s x) = False) = (term178 A s x).
Proof. exact (@lem4329332 (s x)). Qed.
Lemma lem4329334 {A : Type'} (s : A -> Prop) (x : A) : ((@IN A x s) = (@IN A x (@EMPTY A))) = (term178 A s x).
Proof. exact (TRANS (@lem4329330 A s x) (@lem4329333 A s x)). Qed.
Lemma lem4329335 {A : Type'} (s : A -> Prop) : (term179 A s) = (term180 A s).
Proof. exact (fun_ext (fun x : A => @lem4329334 A s x)). Qed.
Lemma lem4329336 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4329337 {A : Type'} (s : A -> Prop) : (term165 A s) = (term181 A s).
Proof. exact (MK_COMB (@lem4329336 A) (@lem4329335 A s)). Qed.
Lemma lem4329342 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4329343 {A : Type'} (s : A -> Prop) : (term166 A s) = (term182 A s).
Proof. exact (MK_COMB (@lem4329342) (@lem4329337 A s)). Qed.
Lemma lem4329344 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term169 A B t s) = (term184 A B t s).
Proof. exact (MK_COMB (@lem4329314 B t) (@lem4329343 A s)). Qed.
Lemma lem4329347 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term170 A B s t) = (term170 A B s t).
Proof. exact (eq_refl (term170 A B s t)). Qed.
Lemma lem4329348 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term171 A B t s) = (term185 A B t s).
Proof. exact (MK_COMB (@lem4329347 A B s t) (@lem4329344 A B t s)). Qed.
Lemma lem4329351 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4329352 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term173 A B t s) = (term186 A B t s).
Proof. exact (MK_COMB (@lem4329351) (@lem4329348 A B t s)). Qed.
Lemma lem4329360 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4329361 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem4329360 B P x). Qed.
Lemma lem4329362 {B : Type'} (t : B -> Prop) (x : B) : (@IN B x t) = (t x).
Proof. exact (@lem4329361 B t x). Qed.
Lemma lem4329363 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4329364 {B : Type'} (t : B -> Prop) (x : B) : (term121 B x t) = (term187 B t x).
Proof. exact (MK_COMB (@lem4329363) (@lem4329362 B t x)). Qed.
Lemma lem4329380 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4329381 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4329380 A P x). Qed.
Lemma lem4329382 {A : Type'} (s : A -> Prop) (p1 : A) : (@IN A p1 s) = (s p1).
Proof. exact (@lem4329381 A s p1). Qed.
Lemma lem4329383 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4329384 {A : Type'} (s : A -> Prop) (p1 : A) : (term188 A p1 s) = (term189 A s p1).
Proof. exact (MK_COMB (@lem4329383) (@lem4329382 A s p1)). Qed.
Lemma lem4329386 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4329387 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem4329386 B P x). Qed.
Lemma lem4329388 {B : Type'} (t : B -> Prop) (p2 : B) : (@IN B p2 t) = (t p2).
Proof. exact (@lem4329387 B t p2). Qed.
Lemma lem4329389 {A B : Type'} (s : A -> Prop) (p1 : A) (t : B -> Prop) (p2 : B) : (term8 A B p1 s p2 t) = (term190 A B s p1 t p2).
Proof. exact (MK_COMB (@lem4329384 A s p1) (@lem4329388 B t p2)). Qed.
Lemma lem4329392 {B : Type'} (x : B) (p2 : B) : (term115 B x p2) = (term115 B x p2).
Proof. exact (eq_refl (term115 B x p2)). Qed.
Lemma lem4329393 {A B : Type'} (x : B) (s : A -> Prop) (p1 : A) (t : B -> Prop) (p2 : B) : (term152 A B x p1 s p2 t) = (term371 A B x s p1 t p2).
Proof. exact (MK_COMB (@lem4329392 B x p2) (@lem4329389 A B s p1 t p2)). Qed.
Lemma lem4329396 {A B : Type'} (x : B) (s : A -> Prop) (p1 : A) (t : B -> Prop) : (term153 A B x p1 s t) = (term372 A B x s p1 t).
Proof. exact (fun_ext (fun p2 : B => @lem4329393 A B x s p1 t p2)). Qed.
Lemma lem4329397 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4329398 {A B : Type'} (x : B) (s : A -> Prop) (p1 : A) (t : B -> Prop) : (term154 A B x p1 s t) = (term373 A B x s p1 t).
Proof. exact (MK_COMB (@lem4329397 B) (@lem4329396 A B x s p1 t)). Qed.
Lemma lem4329403 {A B : Type'} (x : B) (s : A -> Prop) (t : B -> Prop) : (term155 A B x s t) = (term374 A B x s t).
Proof. exact (fun_ext (fun p1 : A => @lem4329398 A B x s p1 t)). Qed.
Lemma lem4329404 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4329405 {A B : Type'} (x : B) (s : A -> Prop) (t : B -> Prop) : (term156 A B x s t) = (term375 A B x s t).
Proof. exact (MK_COMB (@lem4329404 A) (@lem4329403 A B x s t)). Qed.
Lemma lem4329410 {A B : Type'} (x : B) (s : A -> Prop) (t : B -> Prop) : (term158 A B x s t) = (term376 A B x s t).
Proof. exact (MK_COMB (@lem4329364 B t x) (@lem4329405 A B x s t)). Qed.
Lemma lem4329413 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term160 A B s t) = (term377 A B s t).
Proof. exact (fun_ext (fun x : B => @lem4329410 A B x s t)). Qed.
Lemma lem4329414 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4329415 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term161 A B s t) = (term378 A B s t).
Proof. exact (MK_COMB (@lem4329414 B) (@lem4329413 A B s t)). Qed.
Lemma lem4329420 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term370 A B s t) = (term379 A B s t).
Proof. exact (MK_COMB (@lem4329352 A B t s) (@lem4329415 A B s t)). Qed.
Lemma lem4329423 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term379 A B s t) = (term370 A B s t).
Proof. exact (SYM (@lem4329420 A B s t)). Qed.
Lemma lem4329425 (p : Prop) : p = (term200 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4329426 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term379 A B s t) = (term380 A B s t).
Proof. exact (@lem4329425 (term379 A B s t)). Qed.
Lemma lem4329427 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term380 A B s t) = (term379 A B s t).
Proof. exact (SYM (@lem4329426 A B s t)). Qed.
Lemma lem4329428 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term381 A B s t) : term381 A B s t.
Proof. exact (h1). Qed.
Lemma lem4329431 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term380 A B s t) : term380 A B s t.
Proof. exact (h1). Qed.
Lemma lem4329432 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term382 A B s t.
Proof. exact (fun h0 : term380 A B s t => @lem4329431 A B s t h0). Qed.
Lemma lem4329433 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term382 A B s t) : term382 A B s t.
Proof. exact (h1). Qed.
Lemma lem4329434 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term380 A B s t) : term380 A B s t.
Proof. exact (h1). Qed.
Lemma lem4329435 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term380 A B s t) (h2 : term382 A B s t) : term380 A B s t.
Proof. exact (@lem4329433 A B s t h2 (@lem4329434 A B s t h1)). Qed.
Lemma lem4329436 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term380 A B s t) : term383 A B s t.
Proof. exact (fun h0 : term382 A B s t => @lem4329435 A B s t h1 h0). Qed.
Lemma lem4329437 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term382 A B s t) : term382 A B s t.
Proof. exact (h1). Qed.
Lemma lem4329438 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term380 A B s t) (h2 : term382 A B s t) : term380 A B s t.
Proof. exact (@lem4329436 A B s t h1 (@lem4329437 A B s t h2)). Qed.
Lemma lem4329439 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term382 A B s t) : term382 A B s t.
Proof. exact (fun h0 : term380 A B s t => @lem4329438 A B s t h0 h1). Qed.
Lemma lem4329440 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term384 A B s t.
Proof. exact (fun h0 : term382 A B s t => @lem4329439 A B s t h0). Qed.
Lemma lem4329443 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term382 A B s t.
Proof. exact (@lem4329440 A B s t (@lem4329432 A B s t)). Qed.
Lemma lem4329444 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term382 A B s t.
Proof. exact (@lem4329443 A B s t). Qed.
Lemma lem4329454 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4329455 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term380 A B s t) = (term385 A B s t).
Proof. exact (@lem4329454 (term381 A B s t)). Qed.
Lemma lem4329457 (t : Prop) : (term207 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4329458 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term385 A B s t) = (term379 A B s t).
Proof. exact (@lem4329457 (term379 A B s t)). Qed.
Lemma lem4329461 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term380 A B s t) = (term379 A B s t).
Proof. exact (TRANS (@lem4329455 A B s t) (@lem4329458 A B s t)). Qed.
Lemma lem4329536 {A B : Type'} (t : B -> Prop) : (term386 A B t) = (term387 A B t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4329461 A B s t)). Qed.
Lemma lem4329537 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4329538 {A B : Type'} (t : B -> Prop) : (term388 A B t) = (term389 A B t).
Proof. exact (MK_COMB (@lem4329537 A) (@lem4329536 A B t)). Qed.
Lemma lem4329543 {A B : Type'} : (term390 A B) = (term391 A B).
Proof. exact (fun_ext (fun t : B -> Prop => @lem4329538 A B t)). Qed.
Lemma lem4329544 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4329553 {A B : Type'} : (term392 A B) = (term393 A B).
Proof. exact (MK_COMB (@lem4329544 B) (@lem4329543 A B)). Qed.
Lemma lem4329562 {A B : Type'} (x : B) (s : A -> Prop) (p1 : A) (t : B -> Prop) (p2 : B) : (term371 A B x s p1 t p2) = (term371 A B x s p1 t p2).
Proof. exact (eq_refl (term371 A B x s p1 t p2)). Qed.
Lemma lem4329563 {A B : Type'} (x : B) (s : A -> Prop) (p1 : A) (t : B -> Prop) : (term372 A B x s p1 t) = (term372 A B x s p1 t).
Proof. exact (fun_ext (fun p2 : B => @lem4329562 A B x s p1 t p2)). Qed.
Lemma lem4329564 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4329565 {A B : Type'} (x : B) (s : A -> Prop) (p1 : A) (t : B -> Prop) : (term373 A B x s p1 t) = (term373 A B x s p1 t).
Proof. exact (MK_COMB (@lem4329564 B) (@lem4329563 A B x s p1 t)). Qed.
Lemma lem4329566 {A B : Type'} (x : B) (s : A -> Prop) (t : B -> Prop) : (term374 A B x s t) = (term374 A B x s t).
Proof. exact (fun_ext (fun p1 : A => @lem4329565 A B x s p1 t)). Qed.
Lemma lem4329567 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4329568 {A B : Type'} (x : B) (s : A -> Prop) (t : B -> Prop) : (term375 A B x s t) = (term375 A B x s t).
Proof. exact (MK_COMB (@lem4329567 A) (@lem4329566 A B x s t)). Qed.
Lemma lem4329571 {B : Type'} (t : B -> Prop) (x : B) : (term187 B t x) = (term187 B t x).
Proof. exact (eq_refl (term187 B t x)). Qed.
Lemma lem4329572 {A B : Type'} (x : B) (s : A -> Prop) (t : B -> Prop) : (term376 A B x s t) = (term376 A B x s t).
Proof. exact (MK_COMB (@lem4329571 B t x) (@lem4329568 A B x s t)). Qed.
Lemma lem4329573 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term377 A B s t) = (term377 A B s t).
Proof. exact (fun_ext (fun x : B => @lem4329572 A B x s t)). Qed.
Lemma lem4329574 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4329575 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term378 A B s t) = (term378 A B s t).
Proof. exact (MK_COMB (@lem4329574 B) (@lem4329573 A B s t)). Qed.
Lemma lem4329578 {A : Type'} (s : A -> Prop) (x : A) : (term178 A s x) = (term178 A s x).
Proof. exact (eq_refl (term178 A s x)). Qed.
Lemma lem4329579 {A : Type'} (s : A -> Prop) : (term180 A s) = (term180 A s).
Proof. exact (fun_ext (fun x : A => @lem4329578 A s x)). Qed.
Lemma lem4329580 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4329581 {A : Type'} (s : A -> Prop) : (term181 A s) = (term181 A s).
Proof. exact (MK_COMB (@lem4329580 A) (@lem4329579 A s)). Qed.
Lemma lem4329582 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4329583 {A : Type'} (s : A -> Prop) : (term182 A s) = (term182 A s).
Proof. exact (MK_COMB (@lem4329582) (@lem4329581 A s)). Qed.
Lemma lem4329586 {B : Type'} (t : B -> Prop) (x : B) : (term178 B t x) = (term178 B t x).
Proof. exact (eq_refl (term178 B t x)). Qed.
Lemma lem4329587 {B : Type'} (t : B -> Prop) : (term180 B t) = (term180 B t).
Proof. exact (fun_ext (fun x : B => @lem4329586 B t x)). Qed.
Lemma lem4329588 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4329589 {B : Type'} (t : B -> Prop) : (term181 B t) = (term181 B t).
Proof. exact (MK_COMB (@lem4329588 B) (@lem4329587 B t)). Qed.
Lemma lem4329590 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4329591 {B : Type'} (t : B -> Prop) : (term182 B t) = (term182 B t).
Proof. exact (MK_COMB (@lem4329590) (@lem4329589 B t)). Qed.
Lemma lem4329592 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4329593 {B : Type'} (t : B -> Prop) : (term183 B t) = (term183 B t).
Proof. exact (MK_COMB (@lem4329592) (@lem4329591 B t)). Qed.
Lemma lem4329594 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term184 A B t s) = (term184 A B t s).
Proof. exact (MK_COMB (@lem4329593 B t) (@lem4329583 A s)). Qed.
Lemma lem4329597 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term170 A B s t) = (term170 A B s t).
Proof. exact (eq_refl (term170 A B s t)). Qed.
Lemma lem4329598 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term185 A B t s) = (term185 A B t s).
Proof. exact (MK_COMB (@lem4329597 A B s t) (@lem4329594 A B t s)). Qed.
Lemma lem4329599 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4329600 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term186 A B t s) = (term186 A B t s).
Proof. exact (MK_COMB (@lem4329599) (@lem4329598 A B t s)). Qed.
Lemma lem4329601 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term379 A B s t) = (term379 A B s t).
Proof. exact (MK_COMB (@lem4329600 A B t s) (@lem4329575 A B s t)). Qed.
Lemma lem4329602 {A B : Type'} (t : B -> Prop) : (term387 A B t) = (term387 A B t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4329601 A B s t)). Qed.
Lemma lem4329603 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4329604 {A B : Type'} (t : B -> Prop) : (term389 A B t) = (term389 A B t).
Proof. exact (MK_COMB (@lem4329603 A) (@lem4329602 A B t)). Qed.
Lemma lem4329605 {A B : Type'} : (term391 A B) = (term391 A B).
Proof. exact (fun_ext (fun t : B -> Prop => @lem4329604 A B t)). Qed.
Lemma lem4329606 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4329607 {A B : Type'} : (term393 A B) = (term393 A B).
Proof. exact (MK_COMB (@lem4329606 B) (@lem4329605 A B)). Qed.
Lemma lem4329664 {A B : Type'} : (term392 A B) = (term393 A B).
Proof. exact (TRANS (@lem4329553 A B) (@lem4329607 A B)). Qed.
Lemma lem4329665 {A B : Type'} : (term393 A B) = (term392 A B).
Proof. exact (SYM (@lem4329664 A B)). Qed.
Lemma lem4329666 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term185 A B t s) : term185 A B t s.
Proof. exact (h1). Qed.
Lemma lem4329669 (p : Prop) : p = (term200 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4329670 {A B : Type'} (x : B) (s : A -> Prop) (t : B -> Prop) : (term375 A B x s t) = (term394 A B x s t).
Proof. exact (@lem4329669 (term375 A B x s t)). Qed.
Lemma lem4329671 {A B : Type'} (x : B) (s : A -> Prop) (t : B -> Prop) : (term394 A B x s t) = (term375 A B x s t).
Proof. exact (SYM (@lem4329670 A B x s t)). Qed.
Lemma lem4329672 {A B : Type'} (x : B) (s : A -> Prop) (t : B -> Prop) (h1 : term395 A B x s t) : term395 A B x s t.
Proof. exact (h1). Qed.
Lemma lem4329676 {B : Type'} (t : B -> Prop) (x : B) : (term242 B t x) = (t x).
Proof. exact (@lem16933 (t x)). Qed.
Lemma lem4329677 {B : Type'} (P : B -> Prop) : (term243 B P) = (term244 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem4329678 {B : Type'} (t : B -> Prop) : (term182 B t) = (term245 B t).
Proof. exact (@lem4329677 B (term180 B t)). Qed.
Lemma lem4329679 {B : Type'} (t : B -> Prop) (x : B) : (term246 B t x) = (term178 B t x).
Proof. exact (eq_refl (term246 B t x)). Qed.
Lemma lem4329680 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4329681 {B : Type'} (t : B -> Prop) (x : B) : (term247 B t x) = (term242 B t x).
Proof. exact (MK_COMB (@lem4329680) (@lem4329679 B t x)). Qed.
Lemma lem4329682 {B : Type'} (t : B -> Prop) (x : B) : (term247 B t x) = (t x).
Proof. exact (TRANS (@lem4329681 B t x) (@lem4329676 B t x)). Qed.
Lemma lem4329683 {B : Type'} (t : B -> Prop) : (term248 B t) = (term238 B t).
Proof. exact (fun_ext (fun x : B => @lem4329682 B t x)). Qed.
Lemma lem4329684 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4329685 {B : Type'} (t : B -> Prop) : (term245 B t) = (term239 B t).
Proof. exact (MK_COMB (@lem4329684 B) (@lem4329683 B t)). Qed.
Lemma lem4329686 {B : Type'} (t : B -> Prop) : (term182 B t) = (term239 B t).
Proof. exact (TRANS (@lem4329678 B t) (@lem4329685 B t)). Qed.
Lemma lem4329689 {A : Type'} (s : A -> Prop) (x : A) : (term242 A s x) = (s x).
Proof. exact (@lem16933 (s x)). Qed.
Lemma lem4329690 {A : Type'} (P : A -> Prop) : (term243 A P) = (term244 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem4329691 {A : Type'} (s : A -> Prop) : (term182 A s) = (term245 A s).
Proof. exact (@lem4329690 A (term180 A s)). Qed.
Lemma lem4329692 {A : Type'} (s : A -> Prop) (x : A) : (term246 A s x) = (term178 A s x).
Proof. exact (eq_refl (term246 A s x)). Qed.
Lemma lem4329693 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4329694 {A : Type'} (s : A -> Prop) (x : A) : (term247 A s x) = (term242 A s x).
Proof. exact (MK_COMB (@lem4329693) (@lem4329692 A s x)). Qed.
Lemma lem4329695 {A : Type'} (s : A -> Prop) (x : A) : (term247 A s x) = (s x).
Proof. exact (TRANS (@lem4329694 A s x) (@lem4329689 A s x)). Qed.
Lemma lem4329696 {A : Type'} (s : A -> Prop) : (term248 A s) = (term238 A s).
Proof. exact (fun_ext (fun x : A => @lem4329695 A s x)). Qed.
Lemma lem4329697 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4329698 {A : Type'} (s : A -> Prop) : (term245 A s) = (term239 A s).
Proof. exact (MK_COMB (@lem4329697 A) (@lem4329696 A s)). Qed.
Lemma lem4329699 {A : Type'} (s : A -> Prop) : (term182 A s) = (term239 A s).
Proof. exact (TRANS (@lem4329691 A s) (@lem4329698 A s)). Qed.
Lemma lem4329700 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4329701 {B : Type'} (t : B -> Prop) : (term183 B t) = (term249 B t).
Proof. exact (MK_COMB (@lem4329700) (@lem4329686 B t)). Qed.
Lemma lem4329702 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term184 A B t s) = (term250 A B t s).
Proof. exact (MK_COMB (@lem4329701 B t) (@lem4329699 A s)). Qed.
Lemma lem4329704 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term170 A B s t) = (term170 A B s t).
Proof. exact (eq_refl (term170 A B s t)). Qed.
Lemma lem4329705 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term185 A B t s) = (term251 A B t s).
Proof. exact (MK_COMB (@lem4329704 A B s t) (@lem4329702 A B t s)). Qed.
Lemma lem4329716 {A : Type'} (P : A -> Prop) (Q : Prop) : (term252 A P Q) = (term253 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4329717 {B : Type'} (P : B -> Prop) (Q : Prop) : (term252 B P Q) = (term253 B P Q).
Proof. exact (@lem4329716 B P Q). Qed.
Lemma lem4329718 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term250 A B t s) = (term254 A B t s).
Proof. exact (@lem4329717 B t (term239 A s)). Qed.
Lemma lem4329720 {A : Type'} (P : Prop) (Q : A -> Prop) : (term209 A P Q) = (term208 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4329721 {A : Type'} (P : Prop) (Q : A -> Prop) : (term209 A P Q) = (term208 A P Q).
Proof. exact (@lem4329720 A P Q). Qed.
Lemma lem4329722 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) : (term255 A B t x s) = (term256 A B t x s).
Proof. exact (@lem4329721 A (t x) s). Qed.
Lemma lem4329723 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term257 A B t s) = (term258 A B t s).
Proof. exact (fun_ext (fun x : B => @lem4329722 A B t x s)). Qed.
Lemma lem4329724 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4329725 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term254 A B t s) = (term259 A B t s).
Proof. exact (MK_COMB (@lem4329724 B) (@lem4329723 A B t s)). Qed.
Lemma lem4329726 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term250 A B t s) = (term259 A B t s).
Proof. exact (TRANS (@lem4329718 A B t s) (@lem4329725 A B t s)). Qed.
Lemma lem4329727 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term170 A B s t) = (term170 A B s t).
Proof. exact (eq_refl (term170 A B s t)). Qed.
Lemma lem4329728 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term251 A B t s) = (term260 A B t s).
Proof. exact (MK_COMB (@lem4329727 A B s t) (@lem4329726 A B t s)). Qed.
Lemma lem4329730 {A : Type'} (P : Prop) (Q : A -> Prop) : (term209 A P Q) = (term208 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4329731 {B : Type'} (P : Prop) (Q : B -> Prop) : (term209 B P Q) = (term208 B P Q).
Proof. exact (@lem4329730 B P Q). Qed.
Lemma lem4329732 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term261 A B t s) = (term262 A B t s).
Proof. exact (@lem4329731 B (term63 A B s t) (term258 A B t s)). Qed.
Lemma lem4329733 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) : (term263 A B t s x) = (term256 A B t x s).
Proof. exact (eq_refl (term263 A B t s x)). Qed.
Lemma lem4329734 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term264 A B t s) = (term258 A B t s).
Proof. exact (fun_ext (fun x : B => @lem4329733 A B t x s)). Qed.
Lemma lem4329735 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4329736 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term265 A B t s) = (term259 A B t s).
Proof. exact (MK_COMB (@lem4329735 B) (@lem4329734 A B t s)). Qed.
Lemma lem4329737 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term170 A B s t) = (term170 A B s t).
Proof. exact (eq_refl (term170 A B s t)). Qed.
Lemma lem4329738 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term261 A B t s) = (term260 A B t s).
Proof. exact (MK_COMB (@lem4329737 A B s t) (@lem4329736 A B t s)). Qed.
Lemma lem4329739 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4329740 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term266 A B t s) = (term267 A B t s).
Proof. exact (MK_COMB (@lem4329739) (@lem4329738 A B t s)). Qed.
Lemma lem4329741 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) : (term263 A B t s x) = (term256 A B t x s).
Proof. exact (eq_refl (term263 A B t s x)). Qed.
Lemma lem4329742 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term170 A B s t) = (term170 A B s t).
Proof. exact (eq_refl (term170 A B s t)). Qed.
Lemma lem4329743 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) : (term268 A B t s x) = (term269 A B t x s).
Proof. exact (MK_COMB (@lem4329742 A B s t) (@lem4329741 A B t x s)). Qed.
Lemma lem4329744 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term270 A B t s) = (term271 A B t s).
Proof. exact (fun_ext (fun x : B => @lem4329743 A B t x s)). Qed.
Lemma lem4329745 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4329746 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term262 A B t s) = (term272 A B t s).
Proof. exact (MK_COMB (@lem4329745 B) (@lem4329744 A B t s)). Qed.
Lemma lem4329747 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : ((term261 A B t s) = (term262 A B t s)) = ((term260 A B t s) = (term272 A B t s)).
Proof. exact (MK_COMB (@lem4329740 A B t s) (@lem4329746 A B t s)). Qed.
Lemma lem4329748 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term260 A B t s) = (term272 A B t s).
Proof. exact (EQ_MP (@lem4329747 A B t s) (@lem4329732 A B t s)). Qed.
Lemma lem4329750 {A : Type'} (P : Prop) (Q : A -> Prop) : (term209 A P Q) = (term208 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4329751 {A : Type'} (P : Prop) (Q : A -> Prop) : (term209 A P Q) = (term208 A P Q).
Proof. exact (@lem4329750 A P Q). Qed.
Lemma lem4329752 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) : (term273 A B t x s) = (term274 A B t x s).
Proof. exact (@lem4329751 A (term63 A B s t) (term275 A B t x s)). Qed.
Lemma lem4329753 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (x' : A) : (term276 A B t x s x') = (term277 A B t x s x').
Proof. exact (eq_refl (term276 A B t x s x')). Qed.
Lemma lem4329754 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) : (term278 A B t x s) = (term275 A B t x s).
Proof. exact (fun_ext (fun x' : A => @lem4329753 A B t x s x')). Qed.
Lemma lem4329755 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4329756 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) : (term279 A B t x s) = (term256 A B t x s).
Proof. exact (MK_COMB (@lem4329755 A) (@lem4329754 A B t x s)). Qed.
Lemma lem4329757 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term170 A B s t) = (term170 A B s t).
Proof. exact (eq_refl (term170 A B s t)). Qed.
Lemma lem4329758 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) : (term273 A B t x s) = (term269 A B t x s).
Proof. exact (MK_COMB (@lem4329757 A B s t) (@lem4329756 A B t x s)). Qed.
Lemma lem4329759 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4329760 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) : (term280 A B t x s) = (term281 A B t x s).
Proof. exact (MK_COMB (@lem4329759) (@lem4329758 A B t x s)). Qed.
Lemma lem4329761 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (x' : A) : (term276 A B t x s x') = (term277 A B t x s x').
Proof. exact (eq_refl (term276 A B t x s x')). Qed.
Lemma lem4329762 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term170 A B s t) = (term170 A B s t).
Proof. exact (eq_refl (term170 A B s t)). Qed.
Lemma lem4329763 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (x' : A) : (term282 A B t x s x') = (term283 A B t x s x').
Proof. exact (MK_COMB (@lem4329762 A B s t) (@lem4329761 A B t x s x')). Qed.
Lemma lem4329764 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) : (term284 A B t x s) = (term285 A B t x s).
Proof. exact (fun_ext (fun x' : A => @lem4329763 A B t x s x')). Qed.
Lemma lem4329765 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4329766 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) : (term274 A B t x s) = (term286 A B t x s).
Proof. exact (MK_COMB (@lem4329765 A) (@lem4329764 A B t x s)). Qed.
Lemma lem4329767 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) : ((term273 A B t x s) = (term274 A B t x s)) = ((term269 A B t x s) = (term286 A B t x s)).
Proof. exact (MK_COMB (@lem4329760 A B t x s) (@lem4329766 A B t x s)). Qed.
Lemma lem4329768 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) : (term269 A B t x s) = (term286 A B t x s).
Proof. exact (EQ_MP (@lem4329767 A B t x s) (@lem4329752 A B t x s)). Qed.
Lemma lem4329769 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term271 A B t s) = (term287 A B t s).
Proof. exact (fun_ext (fun x : B => @lem4329768 A B t x s)). Qed.
Lemma lem4329770 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4329771 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term272 A B t s) = (term288 A B t s).
Proof. exact (MK_COMB (@lem4329770 B) (@lem4329769 A B t s)). Qed.
Lemma lem4329772 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term260 A B t s) = (term288 A B t s).
Proof. exact (TRANS (@lem4329748 A B t s) (@lem4329771 A B t s)). Qed.
Lemma lem4329774 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term251 A B t s) = (term288 A B t s).
Proof. exact (TRANS (@lem4329728 A B t s) (@lem4329772 A B t s)). Qed.
Lemma lem4329775 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term185 A B t s) = (term288 A B t s).
Proof. exact (TRANS (@lem4329705 A B t s) (@lem4329774 A B t s)). Qed.
Lemma lem4329776 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term185 A B t s) : term288 A B t s.
Proof. exact (EQ_MP (@lem4329775 A B t s) (@lem4329666 A B t s h1)). Qed.
Lemma lem4329782 {B : Type'} (t : B -> Prop) (x : B) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem4329790 {A B : Type'} (s : A -> Prop) (p1 : A) (t : B -> Prop) (p2 : B) : (term396 A B s p1 t p2) = (term397 A B s p1 t p2).
Proof. exact (@lem17045 (s p1) (t p2)). Qed.
Lemma lem4329792 {B : Type'} (x : B) (p2 : B) : (term299 B x p2) = (term299 B x p2).
Proof. exact (eq_refl (term299 B x p2)). Qed.
Lemma lem4329793 {A B : Type'} (x : B) (s : A -> Prop) (p1 : A) (t : B -> Prop) (p2 : B) : (term398 A B x s p1 t p2) = (term399 A B x s p1 t p2).
Proof. exact (MK_COMB (@lem4329792 B x p2) (@lem4329790 A B s p1 t p2)). Qed.
Lemma lem4329794 {A B : Type'} (x : B) (s : A -> Prop) (p1 : A) (t : B -> Prop) (p2 : B) : (term400 A B x s p1 t p2) = (term398 A B x s p1 t p2).
Proof. exact (@lem17045 (x = p2) (term190 A B s p1 t p2)). Qed.
Lemma lem4329795 {A B : Type'} (x : B) (s : A -> Prop) (p1 : A) (t : B -> Prop) (p2 : B) : (term400 A B x s p1 t p2) = (term399 A B x s p1 t p2).
Proof. exact (TRANS (@lem4329794 A B x s p1 t p2) (@lem4329793 A B x s p1 t p2)). Qed.
Lemma lem4329796 {B : Type'} (P : B -> Prop) : (term289 B P) = (term181 B P).
Proof. exact (@lem18394 B P). Qed.
Lemma lem4329797 {A B : Type'} (x : B) (s : A -> Prop) (p1 : A) (t : B -> Prop) : (term401 A B x s p1 t) = (term402 A B x s p1 t).
Proof. exact (@lem4329796 B (term372 A B x s p1 t)). Qed.
Lemma lem4329798 {A B : Type'} (x : B) (s : A -> Prop) (p1 : A) (t : B -> Prop) (p2 : B) : (term403 A B x s p1 t p2) = (term371 A B x s p1 t p2).
Proof. exact (eq_refl (term403 A B x s p1 t p2)). Qed.
Lemma lem4329799 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4329800 {A B : Type'} (x : B) (s : A -> Prop) (p1 : A) (t : B -> Prop) (p2 : B) : (term404 A B x s p1 t p2) = (term400 A B x s p1 t p2).
Proof. exact (MK_COMB (@lem4329799) (@lem4329798 A B x s p1 t p2)). Qed.
Lemma lem4329801 {A B : Type'} (x : B) (s : A -> Prop) (p1 : A) (t : B -> Prop) (p2 : B) : (term404 A B x s p1 t p2) = (term399 A B x s p1 t p2).
Proof. exact (TRANS (@lem4329800 A B x s p1 t p2) (@lem4329795 A B x s p1 t p2)). Qed.
Lemma lem4329802 {A B : Type'} (x : B) (s : A -> Prop) (p1 : A) (t : B -> Prop) : (term405 A B x s p1 t) = (term406 A B x s p1 t).
Proof. exact (fun_ext (fun p2 : B => @lem4329801 A B x s p1 t p2)). Qed.
Lemma lem4329803 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4329804 {A B : Type'} (x : B) (s : A -> Prop) (p1 : A) (t : B -> Prop) : (term402 A B x s p1 t) = (term407 A B x s p1 t).
Proof. exact (MK_COMB (@lem4329803 B) (@lem4329802 A B x s p1 t)). Qed.
Lemma lem4329805 {A B : Type'} (x : B) (s : A -> Prop) (p1 : A) (t : B -> Prop) : (term401 A B x s p1 t) = (term407 A B x s p1 t).
Proof. exact (TRANS (@lem4329797 A B x s p1 t) (@lem4329804 A B x s p1 t)). Qed.
Lemma lem4329806 {A : Type'} (P : A -> Prop) : (term289 A P) = (term181 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem4329807 {A B : Type'} (x : B) (s : A -> Prop) (t : B -> Prop) : (term395 A B x s t) = (term408 A B x s t).
Proof. exact (@lem4329806 A (term374 A B x s t)). Qed.
Lemma lem4329808 {A B : Type'} (x : B) (s : A -> Prop) (p1 : A) (t : B -> Prop) : (term409 A B x s t p1) = (term373 A B x s p1 t).
Proof. exact (eq_refl (term409 A B x s t p1)). Qed.
Lemma lem4329809 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4329810 {A B : Type'} (x : B) (s : A -> Prop) (p1 : A) (t : B -> Prop) : (term410 A B x s t p1) = (term401 A B x s p1 t).
Proof. exact (MK_COMB (@lem4329809) (@lem4329808 A B x s p1 t)). Qed.
Lemma lem4329811 {A B : Type'} (x : B) (s : A -> Prop) (p1 : A) (t : B -> Prop) : (term410 A B x s t p1) = (term407 A B x s p1 t).
Proof. exact (TRANS (@lem4329810 A B x s p1 t) (@lem4329805 A B x s p1 t)). Qed.
Lemma lem4329812 {A B : Type'} (x : B) (s : A -> Prop) (t : B -> Prop) : (term411 A B x s t) = (term412 A B x s t).
Proof. exact (fun_ext (fun p1 : A => @lem4329811 A B x s p1 t)). Qed.
Lemma lem4329813 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4329814 {A B : Type'} (x : B) (s : A -> Prop) (t : B -> Prop) : (term408 A B x s t) = (term413 A B x s t).
Proof. exact (MK_COMB (@lem4329813 A) (@lem4329812 A B x s t)). Qed.
Lemma lem4329871 {A B : Type'} (x : B) (s : A -> Prop) (t : B -> Prop) : (term395 A B x s t) = (term413 A B x s t).
Proof. exact (TRANS (@lem4329807 A B x s t) (@lem4329814 A B x s t)). Qed.
Lemma lem4329872 {A B : Type'} (x : B) (s : A -> Prop) (t : B -> Prop) (h1 : term395 A B x s t) : term413 A B x s t.
Proof. exact (EQ_MP (@lem4329871 A B x s t) (@lem4329672 A B x s t h1)). Qed.
Lemma lem4329873 {A B : Type'} (t : B -> Prop) (x' : B) (s : A -> Prop) (h1 : term286 A B t x' s) : term286 A B t x' s.
Proof. exact (h1). Qed.
Lemma lem4329874 {A B : Type'} (t : B -> Prop) (x' : B) (s : A -> Prop) (x'' : A) (h1 : term283 A B t x' s x'') : term283 A B t x' s x''.
Proof. exact (h1). Qed.
Lemma lem4329879 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4329880 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem4329879 B Prop f x). Qed.
Lemma lem4329882 {B : Type'} (t : B -> Prop) (x : B) : (t x) = (@I (B -> Prop) t x).
Proof. exact (@lem4329880 B t x). Qed.
Lemma lem4329884 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4329889 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4329890 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem4329889 B Prop f x). Qed.
Lemma lem4329892 {B : Type'} (t : B -> Prop) (p2 : B) : (t p2) = (@I (B -> Prop) t p2).
Proof. exact (@lem4329890 B t p2). Qed.
Lemma lem4329893 {B : Type'} (t : B -> Prop) (p2 : B) : (term178 B t p2) = (term309 B t p2).
Proof. exact (MK_COMB (@lem4329884) (@lem4329892 B t p2)). Qed.
Lemma lem4329894 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4329899 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4329900 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4329899 A Prop f x). Qed.
Lemma lem4329902 {A : Type'} (s : A -> Prop) (p1 : A) : (s p1) = (@I (A -> Prop) s p1).
Proof. exact (@lem4329900 A s p1). Qed.
Lemma lem4329903 {A : Type'} (s : A -> Prop) (p1 : A) : (term178 A s p1) = (term309 A s p1).
Proof. exact (MK_COMB (@lem4329894) (@lem4329902 A s p1)). Qed.
Lemma lem4329904 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4329905 {A : Type'} (s : A -> Prop) (p1 : A) : (term295 A s p1) = (term312 A s p1).
Proof. exact (MK_COMB (@lem4329904) (@lem4329903 A s p1)). Qed.
Lemma lem4329906 {A B : Type'} (s : A -> Prop) (p1 : A) (t : B -> Prop) (p2 : B) : (term397 A B s p1 t p2) = (term330 A B s p1 t p2).
Proof. exact (MK_COMB (@lem4329905 A s p1) (@lem4329893 B t p2)). Qed.
Lemma lem4329915 {B : Type'} (x : B) (p2 : B) : (term299 B x p2) = (term299 B x p2).
Proof. exact (eq_refl (term299 B x p2)). Qed.
Lemma lem4329916 {A B : Type'} (x : B) (s : A -> Prop) (p1 : A) (t : B -> Prop) (p2 : B) : (term399 A B x s p1 t p2) = (term414 A B x s p1 t p2).
Proof. exact (MK_COMB (@lem4329915 B x p2) (@lem4329906 A B s p1 t p2)). Qed.
Lemma lem4329917 {A B : Type'} (x : B) (s : A -> Prop) (p1 : A) (t : B -> Prop) : (term406 A B x s p1 t) = (term415 A B x s p1 t).
Proof. exact (fun_ext (fun p2 : B => @lem4329916 A B x s p1 t p2)). Qed.
Lemma lem4329918 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4329919 {A B : Type'} (x : B) (s : A -> Prop) (p1 : A) (t : B -> Prop) : (term407 A B x s p1 t) = (term416 A B x s p1 t).
Proof. exact (MK_COMB (@lem4329918 B) (@lem4329917 A B x s p1 t)). Qed.
Lemma lem4329920 {A B : Type'} (x : B) (s : A -> Prop) (t : B -> Prop) : (term412 A B x s t) = (term417 A B x s t).
Proof. exact (fun_ext (fun p1 : A => @lem4329919 A B x s p1 t)). Qed.
Lemma lem4329921 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4329922 {A B : Type'} (x : B) (s : A -> Prop) (t : B -> Prop) : (term413 A B x s t) = (term418 A B x s t).
Proof. exact (MK_COMB (@lem4329921 A) (@lem4329920 A B x s t)). Qed.
Lemma lem4329923 {A B : Type'} (x : B) (s : A -> Prop) (t : B -> Prop) (h1 : term395 A B x s t) : term418 A B x s t.
Proof. exact (EQ_MP (@lem4329922 A B x s t) (@lem4329872 A B x s t h1)). Qed.
Lemma lem4329928 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4329929 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4329928 A Prop f x). Qed.
Lemma lem4329931 {A : Type'} (s : A -> Prop) (x'' : A) : (s x'') = (@I (A -> Prop) s x'').
Proof. exact (@lem4329929 A s x''). Qed.
Lemma lem4329936 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4329937 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem4329936 B Prop f x). Qed.
Lemma lem4329939 {B : Type'} (t : B -> Prop) (x' : B) : (t x') = (@I (B -> Prop) t x').
Proof. exact (@lem4329937 B t x'). Qed.
Lemma lem4329940 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4329941 {B : Type'} (t : B -> Prop) (x' : B) : (term189 B t x') = (term317 B t x').
Proof. exact (MK_COMB (@lem4329940) (@lem4329939 B t x')). Qed.
Lemma lem4329942 {A B : Type'} (t : B -> Prop) (x' : B) (s : A -> Prop) (x'' : A) : (term277 A B t x' s x'') = (term318 A B t x' s x'').
Proof. exact (MK_COMB (@lem4329941 B t x') (@lem4329931 A s x'')). Qed.
Lemma lem4329951 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term170 A B s t) = (term170 A B s t).
Proof. exact (eq_refl (term170 A B s t)). Qed.
Lemma lem4329952 {A B : Type'} (t : B -> Prop) (x' : B) (s : A -> Prop) (x'' : A) : (term283 A B t x' s x'') = (term319 A B t x' s x'').
Proof. exact (MK_COMB (@lem4329951 A B s t) (@lem4329942 A B t x' s x'')). Qed.
Lemma lem4329953 {A B : Type'} (t : B -> Prop) (x' : B) (s : A -> Prop) (x'' : A) (h1 : term283 A B t x' s x'') : term319 A B t x' s x''.
Proof. exact (EQ_MP (@lem4329952 A B t x' s x'') (@lem4329874 A B t x' s x'' h1)). Qed.
Lemma lem4329954 {A B : Type'} (t : B -> Prop) (x' : B) (s : A -> Prop) (x'' : A) (h1 : term283 A B t x' s x'') : term318 A B t x' s x''.
Proof. exact (proj2 (@lem4329953 A B t x' s x'' h1)). Qed.
Lemma lem4329975 {A B : Type'} (x : B) (s : A -> Prop) (p1 : A) (t : B -> Prop) (p2 : B) : (term414 A B x s p1 t p2) = (term414 A B x s p1 t p2).
Proof. exact (eq_refl (term414 A B x s p1 t p2)). Qed.
Lemma lem4329976 {A B : Type'} (x : B) (s : A -> Prop) (p1 : A) (t : B -> Prop) : (term415 A B x s p1 t) = (term415 A B x s p1 t).
Proof. exact (fun_ext (fun p2 : B => @lem4329975 A B x s p1 t p2)). Qed.
Lemma lem4329977 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4329978 {A B : Type'} (x : B) (s : A -> Prop) (p1 : A) (t : B -> Prop) : (term416 A B x s p1 t) = (term416 A B x s p1 t).
Proof. exact (MK_COMB (@lem4329977 B) (@lem4329976 A B x s p1 t)). Qed.
Lemma lem4329979 {A B : Type'} (x : B) (s : A -> Prop) (t : B -> Prop) : (term417 A B x s t) = (term417 A B x s t).
Proof. exact (fun_ext (fun p1 : A => @lem4329978 A B x s p1 t)). Qed.
Lemma lem4329980 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4329982 {A B : Type'} (x : B) (s : A -> Prop) (t : B -> Prop) : (term418 A B x s t) = (term418 A B x s t).
Proof. exact (MK_COMB (@lem4329980 A) (@lem4329979 A B x s t)). Qed.
Lemma lem4329983 {A B : Type'} (x : B) (s : A -> Prop) (t : B -> Prop) (h1 : term395 A B x s t) : term418 A B x s t.
Proof. exact (EQ_MP (@lem4329982 A B x s t) (@lem4329923 A B x s t h1)). Qed.
Lemma lem4329996 {A B : Type'} (_49310 : A) (x : B) (s : A -> Prop) (t : B -> Prop) (h1 : term395 A B x s t) : term419 A B x s t _49310.
Proof. exact (@lem4329983 A B x s t h1 _49310). Qed.
Lemma lem4329997 {A B : Type'} (x : B) (s : A -> Prop) (_49310 : A) (t : B -> Prop) : (term419 A B x s t _49310) = (term416 A B x s _49310 t).
Proof. exact (eq_refl (term419 A B x s t _49310)). Qed.
Lemma lem4329998 {A B : Type'} (_49310 : A) (x : B) (s : A -> Prop) (t : B -> Prop) (h1 : term395 A B x s t) : term416 A B x s _49310 t.
Proof. exact (EQ_MP (@lem4329997 A B x s _49310 t) (@lem4329996 A B _49310 x s t h1)). Qed.
Lemma lem4329999 {A B : Type'} (_49310 : A) (_49311 : B) (x : B) (s : A -> Prop) (t : B -> Prop) (h1 : term395 A B x s t) : term420 A B x s _49310 t _49311.
Proof. exact (@lem4329998 A B _49310 x s t h1 _49311). Qed.
Lemma lem4330000 {A B : Type'} (x : B) (s : A -> Prop) (_49310 : A) (t : B -> Prop) (_49311 : B) : (term420 A B x s _49310 t _49311) = (term414 A B x s _49310 t _49311).
Proof. exact (eq_refl (term420 A B x s _49310 t _49311)). Qed.
Lemma lem4330013 {A B : Type'} (_49310 : A) (_49311 : B) (x : B) (s : A -> Prop) (t : B -> Prop) (h1 : term395 A B x s t) : term414 A B x s _49310 t _49311.
Proof. exact (EQ_MP (@lem4330000 A B x s _49310 t _49311) (@lem4329999 A B _49310 _49311 x s t h1)). Qed.
Lemma lem4330096 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem4330097 {B : Type'} (x : B) : x = x.
Proof. exact (@lem4330096 B x). Qed.
Lemma lem4330098 {B : Type'} (x : B) : term352 B x.
Proof. exact (fun h0 : term353 B x => @lem4330097 B x). Qed.
Lemma lem4330100 (p : Prop) : (term354 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4330101 {B : Type'} (x : B) : (term352 B x) = (x = x).
Proof. exact (@lem4330100 (x = x)). Qed.
Lemma lem4330102 {B : Type'} (x : B) : x = x.
Proof. exact (EQ_MP (@lem4330101 B x) (@lem4330098 B x)). Qed.
Lemma lem4330104 {A B : Type'} (t : B -> Prop) (x' : B) (s : A -> Prop) (x'' : A) (h1 : term283 A B t x' s x'') : @I (A -> Prop) s x''.
Proof. exact (proj2 (@lem4329954 A B t x' s x'' h1)). Qed.
Lemma lem4330105 {A B : Type'} (t : B -> Prop) (x' : B) (s : A -> Prop) (x'' : A) (h1 : term283 A B t x' s x'') : term355 A s x''.
Proof. exact (fun h0 : term309 A s x'' => @lem4330104 A B t x' s x'' h1). Qed.
Lemma lem4330107 (p : Prop) : (term354 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4330108 {A : Type'} (s : A -> Prop) (x'' : A) : (term355 A s x'') = (@I (A -> Prop) s x'').
Proof. exact (@lem4330107 (@I (A -> Prop) s x'')). Qed.
Lemma lem4330109 {A B : Type'} (t : B -> Prop) (x' : B) (s : A -> Prop) (x'' : A) (h1 : term283 A B t x' s x'') : @I (A -> Prop) s x''.
Proof. exact (EQ_MP (@lem4330108 A s x'') (@lem4330105 A B t x' s x'' h1)). Qed.
Lemma lem4330111 {B : Type'} (t : B -> Prop) (x : B) (h1 : t x) : @I (B -> Prop) t x.
Proof. exact (EQ_MP (@lem4329882 B t x) (@lem4329782 B t x h1)). Qed.
Lemma lem4330112 {B : Type'} (t : B -> Prop) (x : B) (h1 : t x) : term355 B t x.
Proof. exact (fun h0 : term309 B t x => @lem4330111 B t x h1). Qed.
Lemma lem4330114 (p : Prop) : (term354 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4330115 {B : Type'} (t : B -> Prop) (x : B) : (term355 B t x) = (@I (B -> Prop) t x).
Proof. exact (@lem4330114 (@I (B -> Prop) t x)). Qed.
Lemma lem4330116 {B : Type'} (t : B -> Prop) (x : B) (h1 : t x) : @I (B -> Prop) t x.
Proof. exact (EQ_MP (@lem4330115 B t x) (@lem4330112 B t x h1)). Qed.
Lemma lem4330118 (a : Prop) (b : Prop) : (term356 a b) = (term357 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4330119 {A B : Type'} (s : A -> Prop) (_49310 : A) (t : B -> Prop) (_49311 : B) : (term330 A B s _49310 t _49311) = (term358 A B s _49310 t _49311).
Proof. exact (@lem4330118 (@I (A -> Prop) s _49310) (@I (B -> Prop) t _49311)). Qed.
Lemma lem4330120 {B : Type'} (x : B) (_49311 : B) : (term299 B x _49311) = (term299 B x _49311).
Proof. exact (eq_refl (term299 B x _49311)). Qed.
Lemma lem4330121 {A B : Type'} (x : B) (s : A -> Prop) (_49310 : A) (t : B -> Prop) (_49311 : B) : (term414 A B x s _49310 t _49311) = (term421 A B x s _49310 t _49311).
Proof. exact (MK_COMB (@lem4330120 B x _49311) (@lem4330119 A B s _49310 t _49311)). Qed.
Lemma lem4330123 (a : Prop) (b : Prop) : (term356 a b) = (term357 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4330124 {A B : Type'} (x : B) (s : A -> Prop) (_49310 : A) (t : B -> Prop) (_49311 : B) : (term421 A B x s _49310 t _49311) = (term422 A B x s _49310 t _49311).
Proof. exact (@lem4330123 (x = _49311) (term361 A B s _49310 t _49311)). Qed.
Lemma lem4330125 {A B : Type'} (x : B) (s : A -> Prop) (_49310 : A) (t : B -> Prop) (_49311 : B) : (term414 A B x s _49310 t _49311) = (term422 A B x s _49310 t _49311).
Proof. exact (TRANS (@lem4330121 A B x s _49310 t _49311) (@lem4330124 A B x s _49310 t _49311)). Qed.
Lemma lem4330127 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4330128 {A B : Type'} (x : B) (s : A -> Prop) (_49310 : A) (t : B -> Prop) (_49311 : B) : (term422 A B x s _49310 t _49311) = (term423 A B x s _49310 t _49311).
Proof. exact (@lem4330127 (term424 A B x s _49310 t _49311)). Qed.
Lemma lem4330129 {A B : Type'} (x : B) (s : A -> Prop) (_49310 : A) (t : B -> Prop) (_49311 : B) : (term414 A B x s _49310 t _49311) = (term423 A B x s _49310 t _49311).
Proof. exact (TRANS (@lem4330125 A B x s _49310 t _49311) (@lem4330128 A B x s _49310 t _49311)). Qed.
Lemma lem4330131 {A B : Type'} (x : B) (t : B -> Prop) (x' : B) (s : A -> Prop) (x'' : A) (h1 : t x) (h2 : term283 A B t x' s x'') : term361 A B s x'' t x.
Proof. exact (conj (@lem4330109 A B t x' s x'' h2) (@lem4330116 B t x h1)). Qed.
Lemma lem4330132 {A B : Type'} (x : B) (t : B -> Prop) (x' : B) (s : A -> Prop) (x'' : A) (h1 : t x) (h2 : term283 A B t x' s x'') : term425 A B s x'' t x.
Proof. exact (conj (@lem4330102 B x) (@lem4330131 A B x t x' s x'' h1 h2)). Qed.
Lemma lem4330134 {A B : Type'} (_49310 : A) (_49311 : B) (x : B) (s : A -> Prop) (t : B -> Prop) (h1 : term395 A B x s t) : term423 A B x s _49310 t _49311.
Proof. exact (EQ_MP (@lem4330129 A B x s _49310 t _49311) (@lem4330013 A B _49310 _49311 x s t h1)). Qed.
Lemma lem4330135 {A B : Type'} (_49310 : A) (_49311 : B) (x : B) (s : A -> Prop) (t : B -> Prop) (h1 : term395 A B x s t) : term423 A B x s _49310 t _49311.
Proof. exact (@lem4330134 A B _49310 _49311 x s t h1). Qed.
Lemma lem4330136 {A B : Type'} (x'' : A) (x : B) (s : A -> Prop) (t : B -> Prop) (h1 : term395 A B x s t) : term426 A B s x'' t x.
Proof. exact (@lem4330135 A B x'' x x s t h1). Qed.
Lemma lem4330139 {A B : Type'} (x : B) (t : B -> Prop) (x' : B) (s : A -> Prop) (x'' : A) (h1 : term395 A B x s t) (h2 : t x) (h3 : term283 A B t x' s x'') : False.
Proof. exact (@lem4330136 A B x'' x s t h1 (@lem4330132 A B x t x' s x'' h2 h3)). Qed.
Lemma lem4330140 {A B : Type'} (x : B) (t : B -> Prop) (x' : B) (s : A -> Prop) (x'' : A) (h1 : term395 A B x s t) (h2 : t x) (h3 : term283 A B t x' s x'') : term366.
Proof. exact (fun h0 : ~ False => @lem4330139 A B x t x' s x'' h1 h2 h3). Qed.
Lemma lem4330142 (p : Prop) : (term354 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4330143 : term366 = False.
Proof. exact (@lem4330142 False). Qed.
Lemma lem4330144 {A B : Type'} (x : B) (t : B -> Prop) (x' : B) (s : A -> Prop) (x'' : A) (h1 : term395 A B x s t) (h2 : t x) (h3 : term283 A B t x' s x'') : False.
Proof. exact (EQ_MP (@lem4330143) (@lem4330140 A B x t x' s x'' h1 h2 h3)). Qed.
Lemma lem4330145 {A B : Type'} (x' : B) (s : A -> Prop) (t : B -> Prop) (x : B) (h1 : term286 A B t x' s) (h2 : term395 A B x s t) (h3 : t x) : False.
Proof. exact (ex_elim (@lem4329873 A B t x' s h1) (fun x'' : A => fun h0 : term285 A B t x' s x'' => @lem4330144 A B x t x' s x'' h2 h3 h0)). Qed.
Lemma lem4330146 {A B : Type'} (x : B) (t : B -> Prop) (s : A -> Prop) (h1 : term395 A B x s t) (h2 : t x) (h3 : term185 A B t s) : False.
Proof. exact (ex_elim (@lem4329776 A B t s h3) (fun x' : B => fun h0 : term287 A B t s x' => @lem4330145 A B x' s t x h0 h1 h2)). Qed.
Lemma lem4330147 {A B : Type'} (x : B) (t : B -> Prop) (s : A -> Prop) (h1 : term395 A B x s t) (h2 : t x) (h3 : term185 A B t s) : (t x) = False.
Proof. exact (prop_ext (fun h4 : t x => @lem4330146 A B x t s h1 h2 h3) (fun h4 : False => @lem4329782 B t x h2)). Qed.
Lemma lem4330148 {A B : Type'} (x : B) (t : B -> Prop) (s : A -> Prop) (h1 : term395 A B x s t) (h2 : t x) (h3 : term185 A B t s) : False.
Proof. exact (EQ_MP (@lem4330147 A B x t s h1 h2 h3) (@lem4329782 B t x h2)). Qed.
Lemma lem4330149 {A B : Type'} (x : B) (t : B -> Prop) (s : A -> Prop) (h1 : term395 A B x s t) (h2 : t x) (h3 : term185 A B t s) : (term395 A B x s t) = False.
Proof. exact (prop_ext (fun h4 : term395 A B x s t => @lem4330148 A B x t s h1 h2 h3) (fun h4 : False => @lem4329672 A B x s t h1)). Qed.
Lemma lem4330150 {A B : Type'} (x : B) (t : B -> Prop) (s : A -> Prop) (h1 : term395 A B x s t) (h2 : t x) (h3 : term185 A B t s) : False.
Proof. exact (EQ_MP (@lem4330149 A B x t s h1 h2 h3) (@lem4329672 A B x s t h1)). Qed.
Lemma lem4330151 {A B : Type'} (x : B) (t : B -> Prop) (s : A -> Prop) (h1 : t x) (h2 : term185 A B t s) : term394 A B x s t.
Proof. exact (fun h0 : term395 A B x s t => @lem4330150 A B x t s h0 h1 h2). Qed.
Lemma lem4330152 {A B : Type'} (x : B) (t : B -> Prop) (s : A -> Prop) (h1 : t x) (h2 : term185 A B t s) : term375 A B x s t.
Proof. exact (EQ_MP (@lem4329671 A B x s t) (@lem4330151 A B x t s h1 h2)). Qed.
Lemma lem4330153 {A B : Type'} (x : B) (t : B -> Prop) (s : A -> Prop) (h1 : term185 A B t s) : term376 A B x s t.
Proof. exact (fun h0 : t x => @lem4330152 A B x t s h0 h1). Qed.
Lemma lem4330158 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term185 A B t s) : term378 A B s t.
Proof. exact (fun x : B => @lem4330153 A B x t s h1). Qed.
Lemma lem4330159 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term379 A B s t.
Proof. exact (fun h0 : term185 A B t s => @lem4330158 A B t s h0). Qed.
Lemma lem4330164 {A B : Type'} (t : B -> Prop) : term389 A B t.
Proof. exact (fun s : A -> Prop => @lem4330159 A B s t). Qed.
Lemma lem4330169 {A B : Type'} : term393 A B.
Proof. exact (fun t : B -> Prop => @lem4330164 A B t). Qed.
Lemma lem4330170 {A B : Type'} : term392 A B.
Proof. exact (EQ_MP (@lem4329665 A B) (@lem4330169 A B)). Qed.
Lemma lem4330171 {A B : Type'} (t : B -> Prop) : term427 A B t.
Proof. exact (@lem4330170 A B t). Qed.
Lemma lem4330172 {A B : Type'} (t : B -> Prop) : (term427 A B t) = (term388 A B t).
Proof. exact (eq_refl (term427 A B t)). Qed.
Lemma lem4330173 {A B : Type'} (t : B -> Prop) : term388 A B t.
Proof. exact (EQ_MP (@lem4330172 A B t) (@lem4330171 A B t)). Qed.
Lemma lem4330174 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : term428 A B t s.
Proof. exact (@lem4330173 A B t s). Qed.
Lemma lem4330175 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term428 A B t s) = (term380 A B s t).
Proof. exact (eq_refl (term428 A B t s)). Qed.
Lemma lem4330176 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term380 A B s t.
Proof. exact (EQ_MP (@lem4330175 A B s t) (@lem4330174 A B t s)). Qed.
Lemma lem4330178 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term380 A B s t.
Proof. exact (@lem4329444 A B s t (@lem4330176 A B s t)). Qed.
Lemma lem4330179 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term381 A B s t) : False.
Proof. exact (@lem4330178 A B s t (@lem4329428 A B s t h1)). Qed.
Lemma lem4330180 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term381 A B s t) : (term381 A B s t) = False.
Proof. exact (prop_ext (fun h2 : term381 A B s t => @lem4330179 A B s t h1) (fun h2 : False => @lem4329428 A B s t h1)). Qed.
Lemma lem4330181 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term381 A B s t) : False.
Proof. exact (EQ_MP (@lem4330180 A B s t h1) (@lem4329428 A B s t h1)). Qed.
Lemma lem4330182 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term380 A B s t.
Proof. exact (fun h0 : term381 A B s t => @lem4330181 A B s t h0). Qed.
Lemma lem4330183 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term379 A B s t.
Proof. exact (EQ_MP (@lem4329427 A B s t) (@lem4330182 A B s t)). Qed.
Lemma lem4330184 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term370 A B s t.
Proof. exact (EQ_MP (@lem4329423 A B s t) (@lem4330183 A B s t)). Qed.
Lemma lem4330185 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term369 A B s t.
Proof. exact (EQ_MP (@lem4329277 A B s t) (@lem4330184 A B s t)). Qed.
Lemma lem4330186 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term63 A B s t) (h2 : term60 A s) (h3 : term60 B t) : term161 A B s t.
Proof. exact (@lem4330185 A B s t (@lem4329201 A B s t h1 h2 h3)). Qed.
Lemma lem4330187 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term63 A B s t) (h2 : term60 A s) (h3 : term60 B t) : term127 A B s t.
Proof. exact (EQ_MP (@lem4328095 A B s t) (@lem4330186 A B s t h1 h2 h3)). Qed.
Lemma lem4330188 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term63 A B s t) (h2 : term60 A s) (h3 : term60 B t) : term88 A B s t.
Proof. exact (EQ_MP (@lem4327990 A B s t) (@lem4329189 A B s t h1 h2 h3)). Qed.
Lemma lem4330189 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term63 A B s t) (h2 : term60 A s) (h3 : term60 B t) : term429 A B s t.
Proof. exact (@lem4327885 A B s t (@lem4330187 A B s t h1 h2 h3)). Qed.
Lemma lem4330190 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term63 A B s t) (h2 : term60 A s) (h3 : term60 B t) : term430 A B t s.
Proof. exact (@lem4327881 A B t s (@lem4330188 A B s t h1 h2 h3)). Qed.
Lemma lem4330191 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term63 A B s t) (h2 : term60 A s) (h3 : term60 B t) : @FINITE B t.
Proof. exact (@lem4330189 A B s t h1 h2 h3 (@lem4327877 A B s t h1)). Qed.
Lemma lem4330192 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term63 A B s t) (h2 : term60 A s) (h3 : term60 B t) : @FINITE A s.
Proof. exact (@lem4330190 A B s t h1 h2 h3 (@lem4327872 A B s t h1)). Qed.
Lemma lem4330193 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term63 A B s t) (h2 : term60 A s) (h3 : term60 B t) : term67 A B s t.
Proof. exact (conj (@lem4330192 A B s t h1 h2 h3) (@lem4330191 A B s t h1 h2 h3)). Qed.
Lemma lem4330194 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term63 A B s t) (h2 : term60 A s) (h3 : term60 B t) : (term63 A B s t) = (term67 A B s t).
Proof. exact (prop_ext (fun h4 : term63 A B s t => @lem4330193 A B s t h1 h2 h3) (fun h4 : term67 A B s t => @lem4327867 A B s t h1)). Qed.
Lemma lem4330195 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term63 A B s t) (h2 : term60 A s) (h3 : term60 B t) : term67 A B s t.
Proof. exact (EQ_MP (@lem4330194 A B s t h1 h2 h3) (@lem4327867 A B s t h1)). Qed.
Lemma lem4330197 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term60 A s) (h2 : term60 B t) : term431 A B s t.
Proof. exact (fun h0 : term63 A B s t => @lem4330195 A B s t h0 h1 h2). Qed.
Lemma lem4330198 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term60 A s) (h2 : term60 B t) : term432 A B s t.
Proof. exact (conj (@lem4330197 A B s t h1 h2) (@lem4327866 A B s t)). Qed.
Lemma lem4330199 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term432 A B s t) = ((term63 A B s t) = (term67 A B s t)).
Proof. exact (@lem32 (term63 A B s t) (term67 A B s t)). Qed.
Lemma lem4330200 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term60 A s) (h2 : term60 B t) : (term63 A B s t) = (term67 A B s t).
Proof. exact (EQ_MP (@lem4330199 A B s t) (@lem4330198 A B s t h1 h2)). Qed.
Lemma lem4330201 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term60 A s) (h2 : term60 B t) : (term63 A B s t) = (term69 A B s t).
Proof. exact (EQ_MP (@lem4327855 A B s t h2) (@lem4330200 A B s t h1 h2)). Qed.
Lemma lem4330202 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term60 A s) : (term63 A B s t) = (term69 A B s t).
Proof. exact (or_elim (@lem4327564 B t) (fun h0 : t = (@EMPTY B) => @lem4327796 A B s t h0) (fun h0 : term60 B t => @lem4330201 A B s t h1 h0)). Qed.
Lemma lem4330203 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term60 A s) : (term63 A B s t) = (term71 A B s t).
Proof. exact (EQ_MP (@lem4327710 A B t s h1) (@lem4330202 A B t s h1)). Qed.
Lemma lem4330204 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term63 A B s t) = (term71 A B s t).
Proof. exact (or_elim (@lem4327569 A s) (fun h0 : s = (@EMPTY A) => @lem4327656 A B t s h0) (fun h0 : term60 A s => @lem4330203 A B t s h0)). Qed.
Lemma lem4330209 {A B : Type'} (s : A -> Prop) : term433 A B s.
Proof. exact (fun t : B -> Prop => @lem4330204 A B s t). Qed.
Lemma lem4330214 {A B : Type'} : term434 A B.
Proof. exact (fun s : A -> Prop => @lem4330209 A B s). Qed.
