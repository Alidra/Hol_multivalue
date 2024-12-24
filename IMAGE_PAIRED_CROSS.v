Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import IMAGE_PAIRED_CROSS_term_abbrevs.
Require Import DISJ_ASSOC_spec.
Require Import EXISTS_PAIR_THM_spec.
Require Import EXTENSION_spec.
Require Import FORALL_PAIR_THM_spec.
Require Import IN_CROSS_spec.
Require Import IN_IMAGE_spec.
Require Import PAIR_EQ_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm18394_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm48805_spec.
Require Import thm48806_spec.
Require Import thm48811_spec.
Require Import thm48812_spec.
Require Import thm48920_spec.
Require Import thm51128_spec.
Require Import thm51159_spec.
Lemma lem4357469 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem4357470 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem4357471 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem4357470 t1) (@lem4357469 t1)). Qed.
Lemma lem4357472 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem4357471 t1 t2). Qed.
Lemma lem4357473 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem4357474 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem4357473 t1 t2) (@lem4357472 t1 t2)). Qed.
Lemma lem4357475 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem4357474 t1 t2 t3). Qed.
Lemma lem4357476 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem4357477 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem4357476 t1 t2 t3) (@lem4357475 t1 t2 t3)). Qed.
Lemma lem4357478 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem4357477 t1 t2 t3)). Qed.
Lemma lem4357479 {A B : Type'} (x : A) : term7 A B x.
Proof. exact (@lem47438 A B x). Qed.
Lemma lem4357480 {A B : Type'} (x : A) : (term7 A B x) = (term8 A B x).
Proof. exact (eq_refl (term7 A B x)). Qed.
Lemma lem4357481 {A B : Type'} (x : A) : term8 A B x.
Proof. exact (EQ_MP (@lem4357480 A B x) (@lem4357479 A B x)). Qed.
Lemma lem4357482 {A B : Type'} (x : A) (y : B) : term9 A B x y.
Proof. exact (@lem4357481 A B x y). Qed.
Lemma lem4357483 {A B : Type'} (x : A) (y : B) : (term9 A B x y) = (term10 A B x y).
Proof. exact (eq_refl (term9 A B x y)). Qed.
Lemma lem4357484 {A B : Type'} (x : A) (y : B) : term10 A B x y.
Proof. exact (EQ_MP (@lem4357483 A B x y) (@lem4357482 A B x y)). Qed.
Lemma lem4357485 {A B : Type'} (x : A) (y : B) (a : A) : term11 A B x y a.
Proof. exact (@lem4357484 A B x y a). Qed.
Lemma lem4357486 {A B : Type'} (x : A) (a : A) (y : B) : (term11 A B x y a) = (term12 A B x a y).
Proof. exact (eq_refl (term11 A B x y a)). Qed.
Lemma lem4357487 {A B : Type'} (x : A) (a : A) (y : B) : term12 A B x a y.
Proof. exact (EQ_MP (@lem4357486 A B x a y) (@lem4357485 A B x y a)). Qed.
Lemma lem4357488 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : term13 A B x a y b.
Proof. exact (@lem4357487 A B x a y b). Qed.
Lemma lem4357489 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : (term13 A B x a y b) = (((@pair A B x y) = (@pair A B a b)) = (term14 A B x a y b)).
Proof. exact (eq_refl (term13 A B x a y b)). Qed.
Lemma lem4357491 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : term15 _5106 _5107 P.
Proof. exact (@lem49909 _5106 _5107 P). Qed.
Lemma lem4357492 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term15 _5106 _5107 P) = ((term16 _5106 _5107 P) = (term17 _5106 _5107 P)).
Proof. exact (eq_refl (term15 _5106 _5107 P)). Qed.
Lemma lem4357494 {_103718 _103721 : Type'} (x : _103718) : term18 _103718 _103721 x.
Proof. exact (@lem4325365 _103718 _103721 x). Qed.
Lemma lem4357495 {_103718 _103721 : Type'} (x : _103718) : (term18 _103718 _103721 x) = (term19 _103718 _103721 x).
Proof. exact (eq_refl (term18 _103718 _103721 x)). Qed.
Lemma lem4357496 {_103718 _103721 : Type'} (x : _103718) : term19 _103718 _103721 x.
Proof. exact (EQ_MP (@lem4357495 _103718 _103721 x) (@lem4357494 _103718 _103721 x)). Qed.
Lemma lem4357497 {_103718 _103721 : Type'} (x : _103718) (y : _103721) : term20 _103718 _103721 x y.
Proof. exact (@lem4357496 _103718 _103721 x y). Qed.
Lemma lem4357498 {_103718 _103721 : Type'} (x : _103718) (y : _103721) : (term20 _103718 _103721 x y) = (term21 _103718 _103721 x y).
Proof. exact (eq_refl (term20 _103718 _103721 x y)). Qed.
Lemma lem4357499 {_103718 _103721 : Type'} (x : _103718) (y : _103721) : term21 _103718 _103721 x y.
Proof. exact (EQ_MP (@lem4357498 _103718 _103721 x y) (@lem4357497 _103718 _103721 x y)). Qed.
Lemma lem4357500 {_103718 _103721 : Type'} (x : _103718) (y : _103721) (s : _103718 -> Prop) : term22 _103718 _103721 x y s.
Proof. exact (@lem4357499 _103718 _103721 x y s). Qed.
Lemma lem4357501 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) : (term22 _103718 _103721 x y s) = (term23 _103718 _103721 x s y).
Proof. exact (eq_refl (term22 _103718 _103721 x y s)). Qed.
Lemma lem4357502 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) : term23 _103718 _103721 x s y.
Proof. exact (EQ_MP (@lem4357501 _103718 _103721 x s y) (@lem4357500 _103718 _103721 x y s)). Qed.
Lemma lem4357503 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : term24 _103718 _103721 x s y t.
Proof. exact (@lem4357502 _103718 _103721 x s y t). Qed.
Lemma lem4357504 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term24 _103718 _103721 x s y t) = ((term25 _103718 _103721 x y s t) = (term26 _103718 _103721 x s y t)).
Proof. exact (eq_refl (term24 _103718 _103721 x s y t)). Qed.
Lemma lem4357506 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : term27 _5131 _5132 P.
Proof. exact (@lem51006 _5131 _5132 P). Qed.
Lemma lem4357507 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term27 _5131 _5132 P) = ((term28 _5131 _5132 P) = (term29 _5131 _5132 P)).
Proof. exact (eq_refl (term27 _5131 _5132 P)). Qed.
Lemma lem4357509 {A B : Type'} (y : B) : term30 A B y.
Proof. exact (@lem3206070 A B y). Qed.
Lemma lem4357510 {A B : Type'} (y : B) : (term30 A B y) = (term31 A B y).
Proof. exact (eq_refl (term30 A B y)). Qed.
Lemma lem4357511 {A B : Type'} (y : B) : term31 A B y.
Proof. exact (EQ_MP (@lem4357510 A B y) (@lem4357509 A B y)). Qed.
Lemma lem4357512 {A B : Type'} (y : B) (s : A -> Prop) : term32 A B y s.
Proof. exact (@lem4357511 A B y s). Qed.
Lemma lem4357513 {A B : Type'} (y : B) (s : A -> Prop) : (term32 A B y s) = (term33 A B y s).
Proof. exact (eq_refl (term32 A B y s)). Qed.
Lemma lem4357514 {A B : Type'} (y : B) (s : A -> Prop) : term33 A B y s.
Proof. exact (EQ_MP (@lem4357513 A B y s) (@lem4357512 A B y s)). Qed.
Lemma lem4357515 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) : term34 A B y s f.
Proof. exact (@lem4357514 A B y s f). Qed.
Lemma lem4357516 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term34 A B y s f) = ((term35 A B y f s) = (term36 A B y f s)).
Proof. exact (eq_refl (term34 A B y s f)). Qed.
Lemma lem4357518 {A : Type'} (s : A -> Prop) : term37 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem4357519 {A : Type'} (s : A -> Prop) : (term37 A s) = (term38 A s).
Proof. exact (eq_refl (term37 A s)). Qed.
Lemma lem4357520 {A : Type'} (s : A -> Prop) : term38 A s.
Proof. exact (EQ_MP (@lem4357519 A s) (@lem4357518 A s)). Qed.
Lemma lem4357521 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term39 A s t.
Proof. exact (@lem4357520 A s t). Qed.
Lemma lem4357522 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term39 A s t) = ((s = t) = (term40 A s t)).
Proof. exact (eq_refl (term39 A s t)). Qed.
Lemma lem4357551 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term40 A s t).
Proof. exact (EQ_MP (@lem4357522 A s t) (@lem4357521 A s t)). Qed.
Lemma lem4357552 {B D : Type'} (s : type1210 B D) (t : type1210 B D) : (s = t) = (term41 B D s t).
Proof. exact (@lem4357551 (prod B D) s t). Qed.
Lemma lem4357553 {A B C D : Type'} (f : A -> B) (s : A -> Prop) (g : C -> D) (t : C -> Prop) : ((term42 A B C D f g s t) = (term43 A B C D f s g t)) = (term44 A B C D f s g t).
Proof. exact (@lem4357552 B D (term42 A B C D f g s t) (term43 A B C D f s g t)). Qed.
Lemma lem4357559 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term16 _5106 _5107 P) = (term17 _5106 _5107 P).
Proof. exact (EQ_MP (@lem4357492 _5106 _5107 P) (@lem4357491 _5106 _5107 P)). Qed.
Lemma lem4357560 {B D : Type'} (P : type1210 B D) : (term45 B D P) = (term46 B D P).
Proof. exact (@lem4357559 D B P). Qed.
Lemma lem4357561 {A B C D : Type'} (f : A -> B) (s : A -> Prop) (g : C -> D) (t : C -> Prop) : (term47 A B C D f s g t) = (term48 A B C D f s g t).
Proof. exact (@lem4357560 B D (term49 A B C D f s g t)). Qed.
Lemma lem4357562 {A B C D : Type'} (x : prod B D) (f : A -> B) (s : A -> Prop) (g : C -> D) (t : C -> Prop) : (term50 A B C D f s g t x) = ((term51 A B C D x f g s t) = (term52 A B C D x f s g t)).
Proof. exact (eq_refl (term50 A B C D f s g t x)). Qed.
Lemma lem4357563 {A B C D : Type'} (f : A -> B) (s : A -> Prop) (g : C -> D) (t : C -> Prop) : (term53 A B C D f s g t) = (term49 A B C D f s g t).
Proof. exact (fun_ext (fun x : prod B D => @lem4357562 A B C D x f s g t)). Qed.
Lemma lem4357564 {B D : Type'} : (@all (prod B D)) = (@all (prod B D)).
Proof. exact (eq_refl (@all (prod B D))). Qed.
Lemma lem4357565 {A B C D : Type'} (f : A -> B) (s : A -> Prop) (g : C -> D) (t : C -> Prop) : (term47 A B C D f s g t) = (term44 A B C D f s g t).
Proof. exact (MK_COMB (@lem4357564 B D) (@lem4357563 A B C D f s g t)). Qed.
Lemma lem4357566 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4357567 {A B C D : Type'} (f : A -> B) (s : A -> Prop) (g : C -> D) (t : C -> Prop) : (term54 A B C D f s g t) = (term55 A B C D f s g t).
Proof. exact (MK_COMB (@lem4357566) (@lem4357565 A B C D f s g t)). Qed.
Lemma lem4357568 {A B C D : Type'} (p1 : B) (p2 : D) (f : A -> B) (s : A -> Prop) (g : C -> D) (t : C -> Prop) : (term56 A B C D f s g t p1 p2) = ((term57 A B C D p1 p2 f g s t) = (term58 A B C D p1 p2 f s g t)).
Proof. exact (eq_refl (term56 A B C D f s g t p1 p2)). Qed.
Lemma lem4357569 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (g : C -> D) (t : C -> Prop) : (term59 A B C D f s g t p1) = (term60 A B C D p1 f s g t).
Proof. exact (fun_ext (fun p2 : D => @lem4357568 A B C D p1 p2 f s g t)). Qed.
Lemma lem4357570 {D : Type'} : (@all D) = (@all D).
Proof. exact (eq_refl (@all D)). Qed.
Lemma lem4357571 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (g : C -> D) (t : C -> Prop) : (term61 A B C D f s g t p1) = (term62 A B C D p1 f s g t).
Proof. exact (MK_COMB (@lem4357570 D) (@lem4357569 A B C D p1 f s g t)). Qed.
Lemma lem4357572 {A B C D : Type'} (f : A -> B) (s : A -> Prop) (g : C -> D) (t : C -> Prop) : (term63 A B C D f s g t) = (term64 A B C D f s g t).
Proof. exact (fun_ext (fun p1 : B => @lem4357571 A B C D p1 f s g t)). Qed.
Lemma lem4357573 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4357574 {A B C D : Type'} (f : A -> B) (s : A -> Prop) (g : C -> D) (t : C -> Prop) : (term48 A B C D f s g t) = (term65 A B C D f s g t).
Proof. exact (MK_COMB (@lem4357573 B) (@lem4357572 A B C D f s g t)). Qed.
Lemma lem4357575 {A B C D : Type'} (f : A -> B) (s : A -> Prop) (g : C -> D) (t : C -> Prop) : ((term47 A B C D f s g t) = (term48 A B C D f s g t)) = ((term44 A B C D f s g t) = (term65 A B C D f s g t)).
Proof. exact (MK_COMB (@lem4357567 A B C D f s g t) (@lem4357574 A B C D f s g t)). Qed.
Lemma lem4357576 {A B C D : Type'} (f : A -> B) (s : A -> Prop) (g : C -> D) (t : C -> Prop) : (term44 A B C D f s g t) = (term65 A B C D f s g t).
Proof. exact (EQ_MP (@lem4357575 A B C D f s g t) (@lem4357561 A B C D f s g t)). Qed.
Lemma lem4357583 {A B C D : Type'} (f : A -> B) (s : A -> Prop) (g : C -> D) (t : C -> Prop) : ((term42 A B C D f g s t) = (term43 A B C D f s g t)) = (term65 A B C D f s g t).
Proof. exact (TRANS (@lem4357553 A B C D f s g t) (@lem4357576 A B C D f s g t)). Qed.
Lemma lem4357595 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term35 A B y f s) = (term36 A B y f s).
Proof. exact (EQ_MP (@lem4357516 A B y f s) (@lem4357515 A B y s f)). Qed.
Lemma lem4357596 {A B C D : Type'} (y : prod B D) (f : type1214 A B C D) (s : type1210 A C) : (term66 A B C D y f s) = (term67 A B C D y f s).
Proof. exact (@lem4357595 (prod A C) (prod B D) y f s). Qed.
Lemma lem4357597 {A B C D : Type'} (p1 : B) (p2 : D) (f : A -> B) (g : C -> D) (s : A -> Prop) (t : C -> Prop) : (term57 A B C D p1 p2 f g s t) = (term68 A B C D p1 p2 f g s t).
Proof. exact (@lem4357596 A B C D (@pair B D p1 p2) (term69 A B C D f g) (@CROSS C A s t)). Qed.
Lemma lem4357603 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term28 _5131 _5132 P) = (term29 _5131 _5132 P).
Proof. exact (EQ_MP (@lem4357507 _5131 _5132 P) (@lem4357506 _5131 _5132 P)). Qed.
Lemma lem4357604 {A C : Type'} (P : type1210 A C) : (term70 A C P) = (term71 A C P).
Proof. exact (@lem4357603 C A P). Qed.
Lemma lem4357605 {A B C D : Type'} (p1 : B) (p2 : D) (f : A -> B) (g : C -> D) (s : A -> Prop) (t : C -> Prop) : (term72 A B C D p1 p2 f g s t) = (term73 A B C D p1 p2 f g s t).
Proof. exact (@lem4357604 A C (term74 A B C D p1 p2 f g s t)). Qed.
Lemma lem4357606 {A B C D : Type'} (p1 : B) (p2 : D) (f : A -> B) (g : C -> D) (x : prod A C) (s : A -> Prop) (t : C -> Prop) : (term75 A B C D p1 p2 f g s t x) = (term76 A B C D p1 p2 f g x s t).
Proof. exact (eq_refl (term75 A B C D p1 p2 f g s t x)). Qed.
Lemma lem4357607 {A B C D : Type'} (p1 : B) (p2 : D) (f : A -> B) (g : C -> D) (s : A -> Prop) (t : C -> Prop) : (term77 A B C D p1 p2 f g s t) = (term74 A B C D p1 p2 f g s t).
Proof. exact (fun_ext (fun x : prod A C => @lem4357606 A B C D p1 p2 f g x s t)). Qed.
Lemma lem4357608 {A C : Type'} : (@ex (prod A C)) = (@ex (prod A C)).
Proof. exact (eq_refl (@ex (prod A C))). Qed.
Lemma lem4357609 {A B C D : Type'} (p1 : B) (p2 : D) (f : A -> B) (g : C -> D) (s : A -> Prop) (t : C -> Prop) : (term72 A B C D p1 p2 f g s t) = (term68 A B C D p1 p2 f g s t).
Proof. exact (MK_COMB (@lem4357608 A C) (@lem4357607 A B C D p1 p2 f g s t)). Qed.
Lemma lem4357610 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4357611 {A B C D : Type'} (p1 : B) (p2 : D) (f : A -> B) (g : C -> D) (s : A -> Prop) (t : C -> Prop) : (term78 A B C D p1 p2 f g s t) = (term79 A B C D p1 p2 f g s t).
Proof. exact (MK_COMB (@lem4357610) (@lem4357609 A B C D p1 p2 f g s t)). Qed.
Lemma lem4357612 {A B C D : Type'} (p1 : B) (p2 : D) (f : A -> B) (g : C -> D) (p1' : A) (p2' : C) (s : A -> Prop) (t : C -> Prop) : (term80 A B C D p1 p2 f g s t p1' p2') = (term81 A B C D p1 p2 f g p1' p2' s t).
Proof. exact (eq_refl (term80 A B C D p1 p2 f g s t p1' p2')). Qed.
Lemma lem4357613 {A B C D : Type'} (p1 : B) (p2 : D) (f : A -> B) (g : C -> D) (p1' : A) (s : A -> Prop) (t : C -> Prop) : (term82 A B C D p1 p2 f g s t p1') = (term83 A B C D p1 p2 f g p1' s t).
Proof. exact (fun_ext (fun p2' : C => @lem4357612 A B C D p1 p2 f g p1' p2' s t)). Qed.
Lemma lem4357614 {C : Type'} : (@ex C) = (@ex C).
Proof. exact (eq_refl (@ex C)). Qed.
Lemma lem4357615 {A B C D : Type'} (p1 : B) (p2 : D) (f : A -> B) (g : C -> D) (p1' : A) (s : A -> Prop) (t : C -> Prop) : (term84 A B C D p1 p2 f g s t p1') = (term85 A B C D p1 p2 f g p1' s t).
Proof. exact (MK_COMB (@lem4357614 C) (@lem4357613 A B C D p1 p2 f g p1' s t)). Qed.
Lemma lem4357616 {A B C D : Type'} (p1 : B) (p2 : D) (f : A -> B) (g : C -> D) (s : A -> Prop) (t : C -> Prop) : (term86 A B C D p1 p2 f g s t) = (term87 A B C D p1 p2 f g s t).
Proof. exact (fun_ext (fun p1' : A => @lem4357615 A B C D p1 p2 f g p1' s t)). Qed.
Lemma lem4357617 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4357618 {A B C D : Type'} (p1 : B) (p2 : D) (f : A -> B) (g : C -> D) (s : A -> Prop) (t : C -> Prop) : (term73 A B C D p1 p2 f g s t) = (term88 A B C D p1 p2 f g s t).
Proof. exact (MK_COMB (@lem4357617 A) (@lem4357616 A B C D p1 p2 f g s t)). Qed.
Lemma lem4357619 {A B C D : Type'} (p1 : B) (p2 : D) (f : A -> B) (g : C -> D) (s : A -> Prop) (t : C -> Prop) : ((term72 A B C D p1 p2 f g s t) = (term73 A B C D p1 p2 f g s t)) = ((term68 A B C D p1 p2 f g s t) = (term88 A B C D p1 p2 f g s t)).
Proof. exact (MK_COMB (@lem4357611 A B C D p1 p2 f g s t) (@lem4357618 A B C D p1 p2 f g s t)). Qed.
Lemma lem4357620 {A B C D : Type'} (p1 : B) (p2 : D) (f : A -> B) (g : C -> D) (s : A -> Prop) (t : C -> Prop) : (term68 A B C D p1 p2 f g s t) = (term88 A B C D p1 p2 f g s t).
Proof. exact (EQ_MP (@lem4357619 A B C D p1 p2 f g s t) (@lem4357605 A B C D p1 p2 f g s t)). Qed.
Lemma lem4357627 {A B C D : Type'} (p1 : B) (p2 : D) (f : A -> B) (g : C -> D) (s : A -> Prop) (t : C -> Prop) : (term57 A B C D p1 p2 f g s t) = (term88 A B C D p1 p2 f g s t).
Proof. exact (TRANS (@lem4357597 A B C D p1 p2 f g s t) (@lem4357620 A B C D p1 p2 f g s t)). Qed.
Lemma lem4357640 {A C : Type'} (a0 : A) (a1 : C) : a0 = (term89 A C a0 a1).
Proof. exact (@lem51128 A C a0 a1). Qed.
Lemma lem4357641 {A C : Type'} (x : A) (y : C) : x = (term89 A C x y).
Proof. exact (@lem4357640 A C x y). Qed.
Lemma lem4357642 {A C : Type'} (a0 : A) (a1 : C) : a1 = (term90 A C a0 a1).
Proof. exact (@lem51159 A C a0 a1). Qed.
Lemma lem4357643 {A C : Type'} (x : A) (y : C) : y = (term90 A C x y).
Proof. exact (@lem4357642 A C x y). Qed.
Lemma lem4357644 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4357645 {A : Type'} : (term91 A) = (term91 A).
Proof. exact (eq_refl (term91 A)). Qed.
Lemma lem4357646 {A C : Type'} (x : A) (y : C) : (term92 A x) = (term93 A C x y).
Proof. exact (MK_COMB (@lem4357645 A) (@lem4357641 A C x y)). Qed.
Lemma lem4357647 {A C : Type'} (x : A) (y : C) : (term93 A C x y) = (term89 A C x y).
Proof. exact (eq_refl (term93 A C x y)). Qed.
Lemma lem4357648 {A : Type'} (x : A) : (term94 A x) = (term94 A x).
Proof. exact (eq_refl (term94 A x)). Qed.
Lemma lem4357649 {A C : Type'} (x : A) (y : C) : ((term92 A x) = (term93 A C x y)) = ((term92 A x) = (term89 A C x y)).
Proof. exact (MK_COMB (@lem4357648 A x) (@lem4357647 A C x y)). Qed.
Lemma lem4357650 {A : Type'} (x : A) : (term92 A x) = x.
Proof. exact (eq_refl (term92 A x)). Qed.
Lemma lem4357651 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem4357652 {A : Type'} (x : A) : (term94 A x) = (@eq A x).
Proof. exact (MK_COMB (@lem4357651 A) (@lem4357650 A x)). Qed.
Lemma lem4357653 {A C : Type'} (x : A) (y : C) : (term89 A C x y) = (term89 A C x y).
Proof. exact (eq_refl (term89 A C x y)). Qed.
Lemma lem4357654 {A C : Type'} (x : A) (y : C) : ((term92 A x) = (term89 A C x y)) = (x = (term89 A C x y)).
Proof. exact (MK_COMB (@lem4357652 A x) (@lem4357653 A C x y)). Qed.
Lemma lem4357655 {A C : Type'} (x : A) (y : C) : ((term92 A x) = (term93 A C x y)) = (x = (term89 A C x y)).
Proof. exact (TRANS (@lem4357649 A C x y) (@lem4357654 A C x y)). Qed.
Lemma lem4357656 {A C : Type'} (x : A) (y : C) : x = (term89 A C x y).
Proof. exact (EQ_MP (@lem4357655 A C x y) (@lem4357646 A C x y)). Qed.
Lemma lem4357657 {A : Type'} (x : A) : (@eq A x) = (@eq A x).
Proof. exact (eq_refl (@eq A x)). Qed.
Lemma lem4357658 {A C : Type'} (x : A) (y : C) : (x = x) = (x = (term89 A C x y)).
Proof. exact (MK_COMB (@lem4357657 A x) (@lem4357656 A C x y)). Qed.
Lemma lem4357659 {A C : Type'} (x : A) (y : C) : x = (term89 A C x y).
Proof. exact (EQ_MP (@lem4357658 A C x y) (@lem4357644 A x)). Qed.
Lemma lem4357660 {C : Type'} (y : C) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem4357661 {C : Type'} : (term91 C) = (term91 C).
Proof. exact (eq_refl (term91 C)). Qed.
Lemma lem4357662 {A C : Type'} (x : A) (y : C) : (term92 C y) = (term95 A C x y).
Proof. exact (MK_COMB (@lem4357661 C) (@lem4357643 A C x y)). Qed.
Lemma lem4357663 {A C : Type'} (x : A) (y : C) : (term95 A C x y) = (term90 A C x y).
Proof. exact (eq_refl (term95 A C x y)). Qed.
Lemma lem4357664 {C : Type'} (y : C) : (term94 C y) = (term94 C y).
Proof. exact (eq_refl (term94 C y)). Qed.
Lemma lem4357665 {A C : Type'} (x : A) (y : C) : ((term92 C y) = (term95 A C x y)) = ((term92 C y) = (term90 A C x y)).
Proof. exact (MK_COMB (@lem4357664 C y) (@lem4357663 A C x y)). Qed.
Lemma lem4357666 {C : Type'} (y : C) : (term92 C y) = y.
Proof. exact (eq_refl (term92 C y)). Qed.
Lemma lem4357667 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem4357668 {C : Type'} (y : C) : (term94 C y) = (@eq C y).
Proof. exact (MK_COMB (@lem4357667 C) (@lem4357666 C y)). Qed.
Lemma lem4357669 {A C : Type'} (x : A) (y : C) : (term90 A C x y) = (term90 A C x y).
Proof. exact (eq_refl (term90 A C x y)). Qed.
Lemma lem4357670 {A C : Type'} (x : A) (y : C) : ((term92 C y) = (term90 A C x y)) = (y = (term90 A C x y)).
Proof. exact (MK_COMB (@lem4357668 C y) (@lem4357669 A C x y)). Qed.
Lemma lem4357671 {A C : Type'} (x : A) (y : C) : ((term92 C y) = (term95 A C x y)) = (y = (term90 A C x y)).
Proof. exact (TRANS (@lem4357665 A C x y) (@lem4357670 A C x y)). Qed.
Lemma lem4357672 {A C : Type'} (x : A) (y : C) : y = (term90 A C x y).
Proof. exact (EQ_MP (@lem4357671 A C x y) (@lem4357662 A C x y)). Qed.
Lemma lem4357673 {C : Type'} (y : C) : (@eq C y) = (@eq C y).
Proof. exact (eq_refl (@eq C y)). Qed.
Lemma lem4357674 {A C : Type'} (x : A) (y : C) : (y = y) = (y = (term90 A C x y)).
Proof. exact (MK_COMB (@lem4357673 C y) (@lem4357672 A C x y)). Qed.
Lemma lem4357675 {A C : Type'} (x : A) (y : C) : y = (term90 A C x y).
Proof. exact (EQ_MP (@lem4357674 A C x y) (@lem4357660 C y)). Qed.
Lemma lem4357676 {A B C D : Type'} (f : A -> B) (g : C -> D) : (term96 A B C D f g) = (term96 A B C D f g).
Proof. exact (eq_refl (term96 A B C D f g)). Qed.
Lemma lem4357677 {A B C D : Type'} (f : A -> B) (g : C -> D) (x : A) (y : C) : (term97 A B C D f g x) = (term98 A B C D f g x y).
Proof. exact (MK_COMB (@lem4357676 A B C D f g) (@lem4357659 A C x y)). Qed.
Lemma lem4357678 {A B C D : Type'} (f : A -> B) (x : A) (y : C) (g : C -> D) : (term98 A B C D f g x y) = (term99 A B C D f x y g).
Proof. exact (eq_refl (term98 A B C D f g x y)). Qed.
Lemma lem4357679 {A B C D : Type'} (f : A -> B) (g : C -> D) (x : A) : (term100 A B C D f g x) = (term100 A B C D f g x).
Proof. exact (eq_refl (term100 A B C D f g x)). Qed.
Lemma lem4357680 {A B C D : Type'} (f : A -> B) (x : A) (y : C) (g : C -> D) : ((term97 A B C D f g x) = (term98 A B C D f g x y)) = ((term97 A B C D f g x) = (term99 A B C D f x y g)).
Proof. exact (MK_COMB (@lem4357679 A B C D f g x) (@lem4357678 A B C D f x y g)). Qed.
Lemma lem4357681 {A B C D : Type'} (f : A -> B) (x : A) (g : C -> D) : (term97 A B C D f g x) = (term101 A B C D f x g).
Proof. exact (eq_refl (term97 A B C D f g x)). Qed.
Lemma lem4357682 {B C D : Type'} : (@eq (C -> prod B D)) = (@eq (C -> prod B D)).
Proof. exact (eq_refl (@eq (C -> prod B D))). Qed.
Lemma lem4357683 {A B C D : Type'} (f : A -> B) (x : A) (g : C -> D) : (term100 A B C D f g x) = (term102 A B C D f x g).
Proof. exact (MK_COMB (@lem4357682 B C D) (@lem4357681 A B C D f x g)). Qed.
Lemma lem4357684 {A B C D : Type'} (f : A -> B) (x : A) (y : C) (g : C -> D) : (term99 A B C D f x y g) = (term99 A B C D f x y g).
Proof. exact (eq_refl (term99 A B C D f x y g)). Qed.
Lemma lem4357685 {A B C D : Type'} (f : A -> B) (x : A) (y : C) (g : C -> D) : ((term97 A B C D f g x) = (term99 A B C D f x y g)) = ((term101 A B C D f x g) = (term99 A B C D f x y g)).
Proof. exact (MK_COMB (@lem4357683 A B C D f x g) (@lem4357684 A B C D f x y g)). Qed.
Lemma lem4357686 {A B C D : Type'} (f : A -> B) (x : A) (y : C) (g : C -> D) : ((term97 A B C D f g x) = (term98 A B C D f g x y)) = ((term101 A B C D f x g) = (term99 A B C D f x y g)).
Proof. exact (TRANS (@lem4357680 A B C D f x y g) (@lem4357685 A B C D f x y g)). Qed.
Lemma lem4357687 {A B C D : Type'} (f : A -> B) (x : A) (y : C) (g : C -> D) : (term101 A B C D f x g) = (term99 A B C D f x y g).
Proof. exact (EQ_MP (@lem4357686 A B C D f x y g) (@lem4357677 A B C D f g x y)). Qed.
Lemma lem4357688 {A B C D : Type'} (f : A -> B) (g : C -> D) (x : A) (y : C) : (term103 A B C D f x g y) = (term104 A B C D f g x y).
Proof. exact (MK_COMB (@lem4357687 A B C D f x y g) (@lem4357675 A C x y)). Qed.
Lemma lem4357689 {A B C D : Type'} (f : A -> B) (g : C -> D) (x : A) (y : C) : (term104 A B C D f g x y) = (term105 A B C D f g x y).
Proof. exact (eq_refl (term104 A B C D f g x y)). Qed.
Lemma lem4357690 {A B C D : Type'} (f : A -> B) (x : A) (g : C -> D) (y : C) : (term106 A B C D f x g y) = (term106 A B C D f x g y).
Proof. exact (eq_refl (term106 A B C D f x g y)). Qed.
Lemma lem4357691 {A B C D : Type'} (f : A -> B) (g : C -> D) (x : A) (y : C) : ((term103 A B C D f x g y) = (term104 A B C D f g x y)) = ((term103 A B C D f x g y) = (term105 A B C D f g x y)).
Proof. exact (MK_COMB (@lem4357690 A B C D f x g y) (@lem4357689 A B C D f g x y)). Qed.
Lemma lem4357692 {A B C D : Type'} (f : A -> B) (x : A) (g : C -> D) (y : C) : (term103 A B C D f x g y) = (term107 A B C D f x g y).
Proof. exact (eq_refl (term103 A B C D f x g y)). Qed.
Lemma lem4357693 {B D : Type'} : (@eq (prod B D)) = (@eq (prod B D)).
Proof. exact (eq_refl (@eq (prod B D))). Qed.
Lemma lem4357694 {A B C D : Type'} (f : A -> B) (x : A) (g : C -> D) (y : C) : (term106 A B C D f x g y) = (term108 A B C D f x g y).
Proof. exact (MK_COMB (@lem4357693 B D) (@lem4357692 A B C D f x g y)). Qed.
Lemma lem4357695 {A B C D : Type'} (f : A -> B) (g : C -> D) (x : A) (y : C) : (term105 A B C D f g x y) = (term105 A B C D f g x y).
Proof. exact (eq_refl (term105 A B C D f g x y)). Qed.
Lemma lem4357696 {A B C D : Type'} (f : A -> B) (g : C -> D) (x : A) (y : C) : ((term103 A B C D f x g y) = (term105 A B C D f g x y)) = ((term107 A B C D f x g y) = (term105 A B C D f g x y)).
Proof. exact (MK_COMB (@lem4357694 A B C D f x g y) (@lem4357695 A B C D f g x y)). Qed.
Lemma lem4357697 {A B C D : Type'} (f : A -> B) (g : C -> D) (x : A) (y : C) : ((term103 A B C D f x g y) = (term104 A B C D f g x y)) = ((term107 A B C D f x g y) = (term105 A B C D f g x y)).
Proof. exact (TRANS (@lem4357691 A B C D f g x y) (@lem4357696 A B C D f g x y)). Qed.
Lemma lem4357698 {A B C D : Type'} (f : A -> B) (g : C -> D) (x : A) (y : C) : (term107 A B C D f x g y) = (term105 A B C D f g x y).
Proof. exact (EQ_MP (@lem4357697 A B C D f g x y) (@lem4357688 A B C D f g x y)). Qed.
Lemma lem4357699 {A B C D : Type'} (f : A -> B) (x : A) (g : C -> D) (y : C) : (term105 A B C D f g x y) = (term107 A B C D f x g y).
Proof. exact (SYM (@lem4357698 A B C D f g x y)). Qed.
Lemma lem4357700 {A B C D : Type'} (f : A -> B) (g : C -> D) (x : A) (y : C) : (term109 A B C D f g x y) = (term105 A B C D f g x y).
Proof. exact (eq_refl (term109 A B C D f g x y)). Qed.
Lemma lem4357701 {A B C D : Type'} (f : A -> B) (x : A) (g : C -> D) (y : C) : (term109 A B C D f g x y) = (term107 A B C D f x g y).
Proof. exact (TRANS (@lem4357700 A B C D f g x y) (@lem4357699 A B C D f x g y)). Qed.
Lemma lem4357702 {A B C D : Type'} (f : A -> B) (x : A) (g : C -> D) : term110 A B C D f x g.
Proof. exact (fun y : C => @lem4357701 A B C D f x g y). Qed.
Lemma lem4357703 {A B C D : Type'} (f : A -> B) (g : C -> D) : term111 A B C D f g.
Proof. exact (fun x : A => @lem4357702 A B C D f x g). Qed.
Lemma lem4357704 {A B C D : Type'} (f : A -> B) (g : C -> D) : term112 A B C D f g.
Proof. exact (ex_intro (term113 A B C D f g) (term114 A B C D f g) (@lem4357703 A B C D f g)). Qed.
Lemma lem4357706 {A : Type'} (a : A) (b : A) : (a = b) = (@GEQ A a b).
Proof. exact (EQ_MP (@lem48806 A a b) (@lem48805 A a b)). Qed.
Lemma lem4357707 {B D : Type'} (a : prod B D) (b : prod B D) : (a = b) = (@GEQ (prod B D) a b).
Proof. exact (@lem4357706 (prod B D) a b). Qed.
Lemma lem4357708 {A B C D : Type'} (_49844 : type1214 A B C D) (f : A -> B) (x : A) (g : C -> D) (y : C) : ((term115 A B C D _49844 x y) = (term107 A B C D f x g y)) = (term116 A B C D _49844 f x g y).
Proof. exact (@lem4357707 B D (term115 A B C D _49844 x y) (term107 A B C D f x g y)). Qed.
Lemma lem4357709 {A B C D : Type'} (_49844 : type1214 A B C D) (f : A -> B) (x : A) (g : C -> D) : (term117 A B C D _49844 f x g) = (term118 A B C D _49844 f x g).
Proof. exact (fun_ext (fun y : C => @lem4357708 A B C D _49844 f x g y)). Qed.
Lemma lem4357710 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem4357711 {A B C D : Type'} (_49844 : type1214 A B C D) (f : A -> B) (x : A) (g : C -> D) : (term119 A B C D _49844 f x g) = (term120 A B C D _49844 f x g).
Proof. exact (MK_COMB (@lem4357710 C) (@lem4357709 A B C D _49844 f x g)). Qed.
Lemma lem4357712 {A B C D : Type'} (_49844 : type1214 A B C D) (f : A -> B) (g : C -> D) : (term121 A B C D _49844 f g) = (term122 A B C D _49844 f g).
Proof. exact (fun_ext (fun x : A => @lem4357711 A B C D _49844 f x g)). Qed.
Lemma lem4357713 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4357714 {A B C D : Type'} (_49844 : type1214 A B C D) (f : A -> B) (g : C -> D) : (term123 A B C D _49844 f g) = (term124 A B C D _49844 f g).
Proof. exact (MK_COMB (@lem4357713 A) (@lem4357712 A B C D _49844 f g)). Qed.
Lemma lem4357715 {A B C D : Type'} (f : A -> B) (g : C -> D) : (term113 A B C D f g) = (term125 A B C D f g).
Proof. exact (fun_ext (fun _49844 : type1214 A B C D => @lem4357714 A B C D _49844 f g)). Qed.
Lemma lem4357716 {A B C D : Type'} : (@ex ((prod A C) -> prod B D)) = (@ex ((prod A C) -> prod B D)).
Proof. exact (eq_refl (@ex ((prod A C) -> prod B D))). Qed.
Lemma lem4357717 {A B C D : Type'} (f : A -> B) (g : C -> D) : (term112 A B C D f g) = (term126 A B C D f g).
Proof. exact (MK_COMB (@lem4357716 A B C D) (@lem4357715 A B C D f g)). Qed.
Lemma lem4357718 {A B C D : Type'} (f : A -> B) (g : C -> D) : term126 A B C D f g.
Proof. exact (EQ_MP (@lem4357717 A B C D f g) (@lem4357704 A B C D f g)). Qed.
Lemma lem4357720 {_5076 : Type'} (P : _5076 -> Prop) : term127 _5076 P.
Proof. exact (EQ_MP (@lem48920 _5076 P) (@lem0)). Qed.
Lemma lem4357721 {A B C D : Type'} (P : type325 A B C D) : term128 A B C D P.
Proof. exact (@lem4357720 (type1214 A B C D) P). Qed.
Lemma lem4357722 {A B C D : Type'} (f : A -> B) (g : C -> D) : term129 A B C D f g.
Proof. exact (@lem4357721 A B C D (term125 A B C D f g)). Qed.
Lemma lem4357723 {A B C D : Type'} (f : A -> B) (g : C -> D) : term130 A B C D f g.
Proof. exact (@lem4357722 A B C D f g (@lem4357718 A B C D f g)). Qed.
Lemma lem4357724 {A B C D : Type'} (f : A -> B) (g : C -> D) : (term130 A B C D f g) = (term131 A B C D f g).
Proof. exact (eq_refl (term130 A B C D f g)). Qed.
Lemma lem4357725 {A B C D : Type'} (f : A -> B) (g : C -> D) : term131 A B C D f g.
Proof. exact (EQ_MP (@lem4357724 A B C D f g) (@lem4357723 A B C D f g)). Qed.
Lemma lem4357726 {A B C D : Type'} (f : A -> B) (g : C -> D) (x : A) : term132 A B C D f g x.
Proof. exact (@lem4357725 A B C D f g x). Qed.
Lemma lem4357727 {A B C D : Type'} (f : A -> B) (x : A) (g : C -> D) : (term132 A B C D f g x) = (term133 A B C D f x g).
Proof. exact (eq_refl (term132 A B C D f g x)). Qed.
Lemma lem4357728 {A B C D : Type'} (f : A -> B) (x : A) (g : C -> D) : term133 A B C D f x g.
Proof. exact (EQ_MP (@lem4357727 A B C D f x g) (@lem4357726 A B C D f g x)). Qed.
Lemma lem4357729 {A B C D : Type'} (f : A -> B) (x : A) (g : C -> D) (y : C) : term134 A B C D f x g y.
Proof. exact (@lem4357728 A B C D f x g y). Qed.
Lemma lem4357730 {A B C D : Type'} (f : A -> B) (x : A) (g : C -> D) (y : C) : (term134 A B C D f x g y) = (term135 A B C D f x g y).
Proof. exact (eq_refl (term134 A B C D f x g y)). Qed.
Lemma lem4357731 {A B C D : Type'} (f : A -> B) (x : A) (g : C -> D) (y : C) : term135 A B C D f x g y.
Proof. exact (EQ_MP (@lem4357730 A B C D f x g y) (@lem4357729 A B C D f x g y)). Qed.
Lemma lem4357733 {A : Type'} (a : A) (b : A) : (@GEQ A a b) = (a = b).
Proof. exact (EQ_MP (@lem48812 A a b) (@lem48811 A a b)). Qed.
Lemma lem4357734 {B D : Type'} (a : prod B D) (b : prod B D) : (@GEQ (prod B D) a b) = (a = b).
Proof. exact (@lem4357733 (prod B D) a b). Qed.
Lemma lem4357735 {A B C D : Type'} (f : A -> B) (x : A) (g : C -> D) (y : C) : (term135 A B C D f x g y) = ((term136 A B C D f g x y) = (term107 A B C D f x g y)).
Proof. exact (@lem4357734 B D (term136 A B C D f g x y) (term107 A B C D f x g y)). Qed.
Lemma lem4357736 {A B C D : Type'} (f : A -> B) (x : A) (g : C -> D) (y : C) : (term136 A B C D f g x y) = (term107 A B C D f x g y).
Proof. exact (EQ_MP (@lem4357735 A B C D f x g y) (@lem4357731 A B C D f x g y)). Qed.
Lemma lem4357737 {A B C D : Type'} (f : A -> B) (x : A) (g : C -> D) (y : C) : (term136 A B C D f g x y) = (term107 A B C D f x g y).
Proof. exact (@lem4357736 A B C D f x g y). Qed.
Lemma lem4357738 {A B C D : Type'} (f : A -> B) (p1 : A) (g : C -> D) (p2 : C) : (term136 A B C D f g p1 p2) = (term107 A B C D f p1 g p2).
Proof. exact (@lem4357737 A B C D f p1 g p2). Qed.
Lemma lem4357739 {B D : Type'} (p1 : B) (p2 : D) : (term137 B D p1 p2) = (term137 B D p1 p2).
Proof. exact (eq_refl (term137 B D p1 p2)). Qed.
Lemma lem4357740 {A B C D : Type'} (p1 : B) (p2 : D) (f : A -> B) (p1' : A) (g : C -> D) (p2' : C) : ((@pair B D p1 p2) = (term136 A B C D f g p1' p2')) = ((@pair B D p1 p2) = (term107 A B C D f p1' g p2')).
Proof. exact (MK_COMB (@lem4357739 B D p1 p2) (@lem4357738 A B C D f p1' g p2')). Qed.
Lemma lem4357742 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : ((@pair A B x y) = (@pair A B a b)) = (term14 A B x a y b).
Proof. exact (EQ_MP (@lem4357489 A B x a y b) (@lem4357488 A B x a y b)). Qed.
Lemma lem4357743 {B D : Type'} (x : B) (a : B) (y : D) (b : D) : ((@pair B D x y) = (@pair B D a b)) = (term14 B D x a y b).
Proof. exact (@lem4357742 B D x a y b). Qed.
Lemma lem4357744 {A B C D : Type'} (p1 : B) (f : A -> B) (p1' : A) (p2 : D) (g : C -> D) (p2' : C) : ((@pair B D p1 p2) = (term107 A B C D f p1' g p2')) = (term138 A B C D p1 f p1' p2 g p2').
Proof. exact (@lem4357743 B D p1 (f p1') p2 (g p2')). Qed.
Lemma lem4357755 {A B C D : Type'} (p1 : B) (f : A -> B) (p1' : A) (p2 : D) (g : C -> D) (p2' : C) : ((@pair B D p1 p2) = (term136 A B C D f g p1' p2')) = (term138 A B C D p1 f p1' p2 g p2').
Proof. exact (TRANS (@lem4357740 A B C D p1 p2 f p1' g p2') (@lem4357744 A B C D p1 f p1' p2 g p2')). Qed.
Lemma lem4357756 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4357757 {A B C D : Type'} (p1 : B) (f : A -> B) (p1' : A) (p2 : D) (g : C -> D) (p2' : C) : (term139 A B C D p1 p2 f g p1' p2') = (term140 A B C D p1 f p1' p2 g p2').
Proof. exact (MK_COMB (@lem4357756) (@lem4357755 A B C D p1 f p1' p2 g p2')). Qed.
Lemma lem4357759 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term25 _103718 _103721 x y s t) = (term26 _103718 _103721 x s y t).
Proof. exact (EQ_MP (@lem4357504 _103718 _103721 x s y t) (@lem4357503 _103718 _103721 x s y t)). Qed.
Lemma lem4357760 {A C : Type'} (x : A) (s : A -> Prop) (y : C) (t : C -> Prop) : (term25 A C x y s t) = (term26 A C x s y t).
Proof. exact (@lem4357759 A C x s y t). Qed.
Lemma lem4357761 {A C : Type'} (p1 : A) (s : A -> Prop) (p2 : C) (t : C -> Prop) : (term25 A C p1 p2 s t) = (term26 A C p1 s p2 t).
Proof. exact (@lem4357760 A C p1 s p2 t). Qed.
Lemma lem4357764 {A B C D : Type'} (p1 : B) (f : A -> B) (p2 : D) (g : C -> D) (p1' : A) (s : A -> Prop) (p2' : C) (t : C -> Prop) : (term81 A B C D p1 p2 f g p1' p2' s t) = (term141 A B C D p1 f p2 g p1' s p2' t).
Proof. exact (MK_COMB (@lem4357757 A B C D p1 f p1' p2 g p2') (@lem4357761 A C p1' s p2' t)). Qed.
Lemma lem4357767 {A B C D : Type'} (p1 : B) (f : A -> B) (p2 : D) (g : C -> D) (p1' : A) (s : A -> Prop) (t : C -> Prop) : (term83 A B C D p1 p2 f g p1' s t) = (term142 A B C D p1 f p2 g p1' s t).
Proof. exact (fun_ext (fun p2' : C => @lem4357764 A B C D p1 f p2 g p1' s p2' t)). Qed.
Lemma lem4357768 {C : Type'} : (@ex C) = (@ex C).
Proof. exact (eq_refl (@ex C)). Qed.
Lemma lem4357769 {A B C D : Type'} (p1 : B) (f : A -> B) (p2 : D) (g : C -> D) (p1' : A) (s : A -> Prop) (t : C -> Prop) : (term85 A B C D p1 p2 f g p1' s t) = (term143 A B C D p1 f p2 g p1' s t).
Proof. exact (MK_COMB (@lem4357768 C) (@lem4357767 A B C D p1 f p2 g p1' s t)). Qed.
Lemma lem4357776 {A B C D : Type'} (p1 : B) (f : A -> B) (p2 : D) (g : C -> D) (s : A -> Prop) (t : C -> Prop) : (term87 A B C D p1 p2 f g s t) = (term144 A B C D p1 f p2 g s t).
Proof. exact (fun_ext (fun p1' : A => @lem4357769 A B C D p1 f p2 g p1' s t)). Qed.
Lemma lem4357777 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4357778 {A B C D : Type'} (p1 : B) (f : A -> B) (p2 : D) (g : C -> D) (s : A -> Prop) (t : C -> Prop) : (term88 A B C D p1 p2 f g s t) = (term145 A B C D p1 f p2 g s t).
Proof. exact (MK_COMB (@lem4357777 A) (@lem4357776 A B C D p1 f p2 g s t)). Qed.
Lemma lem4357785 {A B C D : Type'} (p1 : B) (f : A -> B) (p2 : D) (g : C -> D) (s : A -> Prop) (t : C -> Prop) : (term57 A B C D p1 p2 f g s t) = (term145 A B C D p1 f p2 g s t).
Proof. exact (TRANS (@lem4357627 A B C D p1 p2 f g s t) (@lem4357778 A B C D p1 f p2 g s t)). Qed.
Lemma lem4357786 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4357787 {A B C D : Type'} (p1 : B) (f : A -> B) (p2 : D) (g : C -> D) (s : A -> Prop) (t : C -> Prop) : (term146 A B C D p1 p2 f g s t) = (term147 A B C D p1 f p2 g s t).
Proof. exact (MK_COMB (@lem4357786) (@lem4357785 A B C D p1 f p2 g s t)). Qed.
Lemma lem4357789 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term25 _103718 _103721 x y s t) = (term26 _103718 _103721 x s y t).
Proof. exact (EQ_MP (@lem4357504 _103718 _103721 x s y t) (@lem4357503 _103718 _103721 x s y t)). Qed.
Lemma lem4357790 {B D : Type'} (x : B) (s : B -> Prop) (y : D) (t : D -> Prop) : (term25 B D x y s t) = (term26 B D x s y t).
Proof. exact (@lem4357789 B D x s y t). Qed.
Lemma lem4357791 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term58 A B C D p1 p2 f s g t) = (term148 A B C D p1 f s p2 g t).
Proof. exact (@lem4357790 B D p1 (@IMAGE A B f s) p2 (@IMAGE C D g t)). Qed.
Lemma lem4357795 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term35 A B y f s) = (term36 A B y f s).
Proof. exact (EQ_MP (@lem4357516 A B y f s) (@lem4357515 A B y s f)). Qed.
Lemma lem4357796 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term35 A B y f s) = (term36 A B y f s).
Proof. exact (@lem4357795 A B y f s). Qed.
Lemma lem4357797 {A B : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) : (term35 A B p1 f s) = (term36 A B p1 f s).
Proof. exact (@lem4357796 A B p1 f s). Qed.
Lemma lem4357810 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4357811 {A B : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) : (term149 A B p1 f s) = (term150 A B p1 f s).
Proof. exact (MK_COMB (@lem4357810) (@lem4357797 A B p1 f s)). Qed.
Lemma lem4357813 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term35 A B y f s) = (term36 A B y f s).
Proof. exact (EQ_MP (@lem4357516 A B y f s) (@lem4357515 A B y s f)). Qed.
Lemma lem4357814 {C D : Type'} (y : D) (f : C -> D) (s : C -> Prop) : (term35 C D y f s) = (term36 C D y f s).
Proof. exact (@lem4357813 C D y f s). Qed.
Lemma lem4357815 {C D : Type'} (p2 : D) (g : C -> D) (t : C -> Prop) : (term35 C D p2 g t) = (term36 C D p2 g t).
Proof. exact (@lem4357814 C D p2 g t). Qed.
Lemma lem4357828 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term148 A B C D p1 f s p2 g t) = (term151 A B C D p1 f s p2 g t).
Proof. exact (MK_COMB (@lem4357811 A B p1 f s) (@lem4357815 C D p2 g t)). Qed.
Lemma lem4357831 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term58 A B C D p1 p2 f s g t) = (term151 A B C D p1 f s p2 g t).
Proof. exact (TRANS (@lem4357791 A B C D p1 f s p2 g t) (@lem4357828 A B C D p1 f s p2 g t)). Qed.
Lemma lem4357832 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : ((term57 A B C D p1 p2 f g s t) = (term58 A B C D p1 p2 f s g t)) = ((term145 A B C D p1 f p2 g s t) = (term151 A B C D p1 f s p2 g t)).
Proof. exact (MK_COMB (@lem4357787 A B C D p1 f p2 g s t) (@lem4357831 A B C D p1 f s p2 g t)). Qed.
Lemma lem4357837 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (g : C -> D) (t : C -> Prop) : (term60 A B C D p1 f s g t) = (term152 A B C D p1 f s g t).
Proof. exact (fun_ext (fun p2 : D => @lem4357832 A B C D p1 f s p2 g t)). Qed.
Lemma lem4357838 {D : Type'} : (@all D) = (@all D).
Proof. exact (eq_refl (@all D)). Qed.
Lemma lem4357839 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (g : C -> D) (t : C -> Prop) : (term62 A B C D p1 f s g t) = (term153 A B C D p1 f s g t).
Proof. exact (MK_COMB (@lem4357838 D) (@lem4357837 A B C D p1 f s g t)). Qed.
Lemma lem4357846 {A B C D : Type'} (f : A -> B) (s : A -> Prop) (g : C -> D) (t : C -> Prop) : (term64 A B C D f s g t) = (term154 A B C D f s g t).
Proof. exact (fun_ext (fun p1 : B => @lem4357839 A B C D p1 f s g t)). Qed.
Lemma lem4357847 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4357848 {A B C D : Type'} (f : A -> B) (s : A -> Prop) (g : C -> D) (t : C -> Prop) : (term65 A B C D f s g t) = (term155 A B C D f s g t).
Proof. exact (MK_COMB (@lem4357847 B) (@lem4357846 A B C D f s g t)). Qed.
Lemma lem4357855 {A B C D : Type'} (f : A -> B) (s : A -> Prop) (g : C -> D) (t : C -> Prop) : ((term42 A B C D f g s t) = (term43 A B C D f s g t)) = (term155 A B C D f s g t).
Proof. exact (TRANS (@lem4357583 A B C D f s g t) (@lem4357848 A B C D f s g t)). Qed.
Lemma lem4357856 {A B C D : Type'} (f : A -> B) (s : A -> Prop) (g : C -> D) : (term156 A B C D f s g) = (term157 A B C D f s g).
Proof. exact (fun_ext (fun t : C -> Prop => @lem4357855 A B C D f s g t)). Qed.
Lemma lem4357857 {C : Type'} : (@all (C -> Prop)) = (@all (C -> Prop)).
Proof. exact (eq_refl (@all (C -> Prop))). Qed.
Lemma lem4357858 {A B C D : Type'} (f : A -> B) (s : A -> Prop) (g : C -> D) : (term158 A B C D f s g) = (term159 A B C D f s g).
Proof. exact (MK_COMB (@lem4357857 C) (@lem4357856 A B C D f s g)). Qed.
Lemma lem4357865 {A B C D : Type'} (f : A -> B) (g : C -> D) : (term160 A B C D f g) = (term161 A B C D f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4357858 A B C D f s g)). Qed.
Lemma lem4357866 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4357867 {A B C D : Type'} (f : A -> B) (g : C -> D) : (term162 A B C D f g) = (term163 A B C D f g).
Proof. exact (MK_COMB (@lem4357866 A) (@lem4357865 A B C D f g)). Qed.
Lemma lem4357874 {A B C D : Type'} (f : A -> B) : (term164 A B C D f) = (term165 A B C D f).
Proof. exact (fun_ext (fun g : C -> D => @lem4357867 A B C D f g)). Qed.
Lemma lem4357875 {C D : Type'} : (@all (C -> D)) = (@all (C -> D)).
Proof. exact (eq_refl (@all (C -> D))). Qed.
Lemma lem4357876 {A B C D : Type'} (f : A -> B) : (term166 A B C D f) = (term167 A B C D f).
Proof. exact (MK_COMB (@lem4357875 C D) (@lem4357874 A B C D f)). Qed.
Lemma lem4357883 {A B C D : Type'} : (term168 A B C D) = (term169 A B C D).
Proof. exact (fun_ext (fun f : A -> B => @lem4357876 A B C D f)). Qed.
Lemma lem4357884 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4357885 {A B C D : Type'} : (term170 A B C D) = (term171 A B C D).
Proof. exact (MK_COMB (@lem4357884 A B) (@lem4357883 A B C D)). Qed.
Lemma lem4357892 {A B C D : Type'} : (term171 A B C D) = (term170 A B C D).
Proof. exact (SYM (@lem4357885 A B C D)). Qed.
Lemma lem4357894 (p : Prop) : p = (term172 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4357895 {A B C D : Type'} : (term171 A B C D) = (term173 A B C D).
Proof. exact (@lem4357894 (term171 A B C D)). Qed.
Lemma lem4357896 {A B C D : Type'} : (term173 A B C D) = (term171 A B C D).
Proof. exact (SYM (@lem4357895 A B C D)). Qed.
Lemma lem4357897 {A B C D : Type'} (h1 : term174 A B C D) : term174 A B C D.
Proof. exact (h1). Qed.
Lemma lem4357900 {A B C D : Type'} (h1 : term173 A B C D) : term173 A B C D.
Proof. exact (h1). Qed.
Lemma lem4357901 {A B C D : Type'} : term175 A B C D.
Proof. exact (fun h0 : term173 A B C D => @lem4357900 A B C D h0). Qed.
Lemma lem4357902 {A B C D : Type'} (h1 : term175 A B C D) : term175 A B C D.
Proof. exact (h1). Qed.
Lemma lem4357903 {A B C D : Type'} (h1 : term173 A B C D) : term173 A B C D.
Proof. exact (h1). Qed.
Lemma lem4357904 {A B C D : Type'} (h1 : term173 A B C D) (h2 : term175 A B C D) : term173 A B C D.
Proof. exact (@lem4357902 A B C D h2 (@lem4357903 A B C D h1)). Qed.
Lemma lem4357905 {A B C D : Type'} (h1 : term173 A B C D) : term176 A B C D.
Proof. exact (fun h0 : term175 A B C D => @lem4357904 A B C D h1 h0). Qed.
Lemma lem4357906 {A B C D : Type'} (h1 : term175 A B C D) : term175 A B C D.
Proof. exact (h1). Qed.
Lemma lem4357907 {A B C D : Type'} (h1 : term173 A B C D) (h2 : term175 A B C D) : term173 A B C D.
Proof. exact (@lem4357905 A B C D h1 (@lem4357906 A B C D h2)). Qed.
Lemma lem4357908 {A B C D : Type'} (h1 : term175 A B C D) : term175 A B C D.
Proof. exact (fun h0 : term173 A B C D => @lem4357907 A B C D h0 h1). Qed.
Lemma lem4357909 {A B C D : Type'} : term177 A B C D.
Proof. exact (fun h0 : term175 A B C D => @lem4357908 A B C D h0). Qed.
Lemma lem4357912 {A B C D : Type'} : term175 A B C D.
Proof. exact (@lem4357909 A B C D (@lem4357901 A B C D)). Qed.
Lemma lem4357913 {A B C D : Type'} : term175 A B C D.
Proof. exact (@lem4357912 A B C D). Qed.
Lemma lem4357915 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4357916 {A B C D : Type'} : (term173 A B C D) = (term178 A B C D).
Proof. exact (@lem4357915 (term174 A B C D)). Qed.
Lemma lem4357918 (t : Prop) : (term179 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4357919 {A B C D : Type'} : (term178 A B C D) = (term171 A B C D).
Proof. exact (@lem4357918 (term171 A B C D)). Qed.
Lemma lem4358108 {A B C D : Type'} : (term173 A B C D) = (term171 A B C D).
Proof. exact (TRANS (@lem4357916 A B C D) (@lem4357919 A B C D)). Qed.
Lemma lem4358113 {C D : Type'} (p2 : D) (g : C -> D) (x : C) (t : C -> Prop) : (term180 C D p2 g x t) = (term180 C D p2 g x t).
Proof. exact (eq_refl (term180 C D p2 g x t)). Qed.
Lemma lem4358114 {C D : Type'} (p2 : D) (g : C -> D) (t : C -> Prop) : (term181 C D p2 g t) = (term181 C D p2 g t).
Proof. exact (fun_ext (fun x : C => @lem4358113 C D p2 g x t)). Qed.
Lemma lem4358115 {C : Type'} : (@ex C) = (@ex C).
Proof. exact (eq_refl (@ex C)). Qed.
Lemma lem4358116 {C D : Type'} (p2 : D) (g : C -> D) (t : C -> Prop) : (term36 C D p2 g t) = (term36 C D p2 g t).
Proof. exact (MK_COMB (@lem4358115 C) (@lem4358114 C D p2 g t)). Qed.
Lemma lem4358121 {A B : Type'} (p1 : B) (f : A -> B) (x : A) (s : A -> Prop) : (term180 A B p1 f x s) = (term180 A B p1 f x s).
Proof. exact (eq_refl (term180 A B p1 f x s)). Qed.
Lemma lem4358122 {A B : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) : (term181 A B p1 f s) = (term181 A B p1 f s).
Proof. exact (fun_ext (fun x : A => @lem4358121 A B p1 f x s)). Qed.
Lemma lem4358123 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4358124 {A B : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) : (term36 A B p1 f s) = (term36 A B p1 f s).
Proof. exact (MK_COMB (@lem4358123 A) (@lem4358122 A B p1 f s)). Qed.
Lemma lem4358125 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4358126 {A B : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) : (term150 A B p1 f s) = (term150 A B p1 f s).
Proof. exact (MK_COMB (@lem4358125) (@lem4358124 A B p1 f s)). Qed.
Lemma lem4358127 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term151 A B C D p1 f s p2 g t) = (term151 A B C D p1 f s p2 g t).
Proof. exact (MK_COMB (@lem4358126 A B p1 f s) (@lem4358116 C D p2 g t)). Qed.
Lemma lem4358140 {A B C D : Type'} (p1 : B) (f : A -> B) (p2 : D) (g : C -> D) (p1' : A) (s : A -> Prop) (p2' : C) (t : C -> Prop) : (term141 A B C D p1 f p2 g p1' s p2' t) = (term141 A B C D p1 f p2 g p1' s p2' t).
Proof. exact (eq_refl (term141 A B C D p1 f p2 g p1' s p2' t)). Qed.
Lemma lem4358141 {A B C D : Type'} (p1 : B) (f : A -> B) (p2 : D) (g : C -> D) (p1' : A) (s : A -> Prop) (t : C -> Prop) : (term142 A B C D p1 f p2 g p1' s t) = (term142 A B C D p1 f p2 g p1' s t).
Proof. exact (fun_ext (fun p2' : C => @lem4358140 A B C D p1 f p2 g p1' s p2' t)). Qed.
Lemma lem4358142 {C : Type'} : (@ex C) = (@ex C).
Proof. exact (eq_refl (@ex C)). Qed.
Lemma lem4358143 {A B C D : Type'} (p1 : B) (f : A -> B) (p2 : D) (g : C -> D) (p1' : A) (s : A -> Prop) (t : C -> Prop) : (term143 A B C D p1 f p2 g p1' s t) = (term143 A B C D p1 f p2 g p1' s t).
Proof. exact (MK_COMB (@lem4358142 C) (@lem4358141 A B C D p1 f p2 g p1' s t)). Qed.
Lemma lem4358144 {A B C D : Type'} (p1 : B) (f : A -> B) (p2 : D) (g : C -> D) (s : A -> Prop) (t : C -> Prop) : (term144 A B C D p1 f p2 g s t) = (term144 A B C D p1 f p2 g s t).
Proof. exact (fun_ext (fun p1' : A => @lem4358143 A B C D p1 f p2 g p1' s t)). Qed.
Lemma lem4358145 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4358146 {A B C D : Type'} (p1 : B) (f : A -> B) (p2 : D) (g : C -> D) (s : A -> Prop) (t : C -> Prop) : (term145 A B C D p1 f p2 g s t) = (term145 A B C D p1 f p2 g s t).
Proof. exact (MK_COMB (@lem4358145 A) (@lem4358144 A B C D p1 f p2 g s t)). Qed.
Lemma lem4358147 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4358148 {A B C D : Type'} (p1 : B) (f : A -> B) (p2 : D) (g : C -> D) (s : A -> Prop) (t : C -> Prop) : (term147 A B C D p1 f p2 g s t) = (term147 A B C D p1 f p2 g s t).
Proof. exact (MK_COMB (@lem4358147) (@lem4358146 A B C D p1 f p2 g s t)). Qed.
Lemma lem4358149 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : ((term145 A B C D p1 f p2 g s t) = (term151 A B C D p1 f s p2 g t)) = ((term145 A B C D p1 f p2 g s t) = (term151 A B C D p1 f s p2 g t)).
Proof. exact (MK_COMB (@lem4358148 A B C D p1 f p2 g s t) (@lem4358127 A B C D p1 f s p2 g t)). Qed.
Lemma lem4358150 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (g : C -> D) (t : C -> Prop) : (term152 A B C D p1 f s g t) = (term152 A B C D p1 f s g t).
Proof. exact (fun_ext (fun p2 : D => @lem4358149 A B C D p1 f s p2 g t)). Qed.
Lemma lem4358151 {D : Type'} : (@all D) = (@all D).
Proof. exact (eq_refl (@all D)). Qed.
Lemma lem4358152 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (g : C -> D) (t : C -> Prop) : (term153 A B C D p1 f s g t) = (term153 A B C D p1 f s g t).
Proof. exact (MK_COMB (@lem4358151 D) (@lem4358150 A B C D p1 f s g t)). Qed.
Lemma lem4358153 {A B C D : Type'} (f : A -> B) (s : A -> Prop) (g : C -> D) (t : C -> Prop) : (term154 A B C D f s g t) = (term154 A B C D f s g t).
Proof. exact (fun_ext (fun p1 : B => @lem4358152 A B C D p1 f s g t)). Qed.
Lemma lem4358154 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4358155 {A B C D : Type'} (f : A -> B) (s : A -> Prop) (g : C -> D) (t : C -> Prop) : (term155 A B C D f s g t) = (term155 A B C D f s g t).
Proof. exact (MK_COMB (@lem4358154 B) (@lem4358153 A B C D f s g t)). Qed.
Lemma lem4358156 {A B C D : Type'} (f : A -> B) (s : A -> Prop) (g : C -> D) : (term157 A B C D f s g) = (term157 A B C D f s g).
Proof. exact (fun_ext (fun t : C -> Prop => @lem4358155 A B C D f s g t)). Qed.
Lemma lem4358157 {C : Type'} : (@all (C -> Prop)) = (@all (C -> Prop)).
Proof. exact (eq_refl (@all (C -> Prop))). Qed.
Lemma lem4358158 {A B C D : Type'} (f : A -> B) (s : A -> Prop) (g : C -> D) : (term159 A B C D f s g) = (term159 A B C D f s g).
Proof. exact (MK_COMB (@lem4358157 C) (@lem4358156 A B C D f s g)). Qed.
Lemma lem4358159 {A B C D : Type'} (f : A -> B) (g : C -> D) : (term161 A B C D f g) = (term161 A B C D f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4358158 A B C D f s g)). Qed.
Lemma lem4358160 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4358161 {A B C D : Type'} (f : A -> B) (g : C -> D) : (term163 A B C D f g) = (term163 A B C D f g).
Proof. exact (MK_COMB (@lem4358160 A) (@lem4358159 A B C D f g)). Qed.
Lemma lem4358162 {A B C D : Type'} (f : A -> B) : (term165 A B C D f) = (term165 A B C D f).
Proof. exact (fun_ext (fun g : C -> D => @lem4358161 A B C D f g)). Qed.
Lemma lem4358163 {C D : Type'} : (@all (C -> D)) = (@all (C -> D)).
Proof. exact (eq_refl (@all (C -> D))). Qed.
Lemma lem4358164 {A B C D : Type'} (f : A -> B) : (term167 A B C D f) = (term167 A B C D f).
Proof. exact (MK_COMB (@lem4358163 C D) (@lem4358162 A B C D f)). Qed.
Lemma lem4358165 {A B C D : Type'} : (term169 A B C D) = (term169 A B C D).
Proof. exact (fun_ext (fun f : A -> B => @lem4358164 A B C D f)). Qed.
Lemma lem4358166 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4358167 {A B C D : Type'} : (term171 A B C D) = (term171 A B C D).
Proof. exact (MK_COMB (@lem4358166 A B) (@lem4358165 A B C D)). Qed.
Lemma lem4358242 {A B C D : Type'} : (term173 A B C D) = (term171 A B C D).
Proof. exact (TRANS (@lem4358108 A B C D) (@lem4358167 A B C D)). Qed.
Lemma lem4358243 {A B C D : Type'} : (term171 A B C D) = (term173 A B C D).
Proof. exact (SYM (@lem4358242 A B C D)). Qed.
Lemma lem4358245 (p : Prop) : p = (term172 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4358246 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : ((term145 A B C D p1 f p2 g s t) = (term151 A B C D p1 f s p2 g t)) = (term182 A B C D p1 f s p2 g t).
Proof. exact (@lem4358245 ((term145 A B C D p1 f p2 g s t) = (term151 A B C D p1 f s p2 g t))). Qed.
Lemma lem4358247 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term182 A B C D p1 f s p2 g t) = ((term145 A B C D p1 f p2 g s t) = (term151 A B C D p1 f s p2 g t)).
Proof. exact (SYM (@lem4358246 A B C D p1 f s p2 g t)). Qed.
Lemma lem4358248 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) (h1 : term183 A B C D p1 f s p2 g t) : term183 A B C D p1 f s p2 g t.
Proof. exact (h1). Qed.
Lemma lem4358257 {A B C D : Type'} (p1 : B) (f : A -> B) (p1' : A) (p2 : D) (g : C -> D) (p2' : C) : (term184 A B C D p1 f p1' p2 g p2') = (term185 A B C D p1 f p1' p2 g p2').
Proof. exact (@lem17045 (p1 = (f p1')) (p2 = (g p2'))). Qed.
Lemma lem4358269 {A C : Type'} (p1 : A) (s : A -> Prop) (p2 : C) (t : C -> Prop) : (term186 A C p1 s p2 t) = (term187 A C p1 s p2 t).
Proof. exact (@lem17045 (@IN A p1 s) (@IN C p2 t)). Qed.
Lemma lem4358273 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4358274 {A B C D : Type'} (p1 : B) (f : A -> B) (p1' : A) (p2 : D) (g : C -> D) (p2' : C) : (term188 A B C D p1 f p1' p2 g p2') = (term189 A B C D p1 f p1' p2 g p2').
Proof. exact (MK_COMB (@lem4358273) (@lem4358257 A B C D p1 f p1' p2 g p2')). Qed.
Lemma lem4358275 {A B C D : Type'} (p1 : B) (f : A -> B) (p2 : D) (g : C -> D) (p1' : A) (s : A -> Prop) (p2' : C) (t : C -> Prop) : (term190 A B C D p1 f p2 g p1' s p2' t) = (term191 A B C D p1 f p2 g p1' s p2' t).
Proof. exact (MK_COMB (@lem4358274 A B C D p1 f p1' p2 g p2') (@lem4358269 A C p1' s p2' t)). Qed.
Lemma lem4358276 {A B C D : Type'} (p1 : B) (f : A -> B) (p2 : D) (g : C -> D) (p1' : A) (s : A -> Prop) (p2' : C) (t : C -> Prop) : (term192 A B C D p1 f p2 g p1' s p2' t) = (term190 A B C D p1 f p2 g p1' s p2' t).
Proof. exact (@lem17045 (term138 A B C D p1 f p1' p2 g p2') (term26 A C p1' s p2' t)). Qed.
Lemma lem4358277 {A B C D : Type'} (p1 : B) (f : A -> B) (p2 : D) (g : C -> D) (p1' : A) (s : A -> Prop) (p2' : C) (t : C -> Prop) : (term192 A B C D p1 f p2 g p1' s p2' t) = (term191 A B C D p1 f p2 g p1' s p2' t).
Proof. exact (TRANS (@lem4358276 A B C D p1 f p2 g p1' s p2' t) (@lem4358275 A B C D p1 f p2 g p1' s p2' t)). Qed.
Lemma lem4358280 {A B C D : Type'} (p1 : B) (f : A -> B) (p2 : D) (g : C -> D) (p1' : A) (s : A -> Prop) (p2' : C) (t : C -> Prop) : (term141 A B C D p1 f p2 g p1' s p2' t) = (term141 A B C D p1 f p2 g p1' s p2' t).
Proof. exact (eq_refl (term141 A B C D p1 f p2 g p1' s p2' t)). Qed.
Lemma lem4358281 {C : Type'} (P : C -> Prop) : (term193 C P) = (term194 C P).
Proof. exact (@lem18394 C P). Qed.
Lemma lem4358282 {A B C D : Type'} (p1 : B) (f : A -> B) (p2 : D) (g : C -> D) (p1' : A) (s : A -> Prop) (t : C -> Prop) : (term195 A B C D p1 f p2 g p1' s t) = (term196 A B C D p1 f p2 g p1' s t).
Proof. exact (@lem4358281 C (term142 A B C D p1 f p2 g p1' s t)). Qed.
Lemma lem4358283 {A B C D : Type'} (p1 : B) (f : A -> B) (p2 : D) (g : C -> D) (p1' : A) (s : A -> Prop) (p2' : C) (t : C -> Prop) : (term197 A B C D p1 f p2 g p1' s t p2') = (term141 A B C D p1 f p2 g p1' s p2' t).
Proof. exact (eq_refl (term197 A B C D p1 f p2 g p1' s t p2')). Qed.
Lemma lem4358284 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4358285 {A B C D : Type'} (p1 : B) (f : A -> B) (p2 : D) (g : C -> D) (p1' : A) (s : A -> Prop) (p2' : C) (t : C -> Prop) : (term198 A B C D p1 f p2 g p1' s t p2') = (term192 A B C D p1 f p2 g p1' s p2' t).
Proof. exact (MK_COMB (@lem4358284) (@lem4358283 A B C D p1 f p2 g p1' s p2' t)). Qed.
Lemma lem4358286 {A B C D : Type'} (p1 : B) (f : A -> B) (p2 : D) (g : C -> D) (p1' : A) (s : A -> Prop) (p2' : C) (t : C -> Prop) : (term198 A B C D p1 f p2 g p1' s t p2') = (term191 A B C D p1 f p2 g p1' s p2' t).
Proof. exact (TRANS (@lem4358285 A B C D p1 f p2 g p1' s p2' t) (@lem4358277 A B C D p1 f p2 g p1' s p2' t)). Qed.
Lemma lem4358287 {A B C D : Type'} (p1 : B) (f : A -> B) (p2 : D) (g : C -> D) (p1' : A) (s : A -> Prop) (t : C -> Prop) : (term199 A B C D p1 f p2 g p1' s t) = (term200 A B C D p1 f p2 g p1' s t).
Proof. exact (fun_ext (fun p2' : C => @lem4358286 A B C D p1 f p2 g p1' s p2' t)). Qed.
Lemma lem4358288 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem4358289 {A B C D : Type'} (p1 : B) (f : A -> B) (p2 : D) (g : C -> D) (p1' : A) (s : A -> Prop) (t : C -> Prop) : (term196 A B C D p1 f p2 g p1' s t) = (term201 A B C D p1 f p2 g p1' s t).
Proof. exact (MK_COMB (@lem4358288 C) (@lem4358287 A B C D p1 f p2 g p1' s t)). Qed.
Lemma lem4358290 {A B C D : Type'} (p1 : B) (f : A -> B) (p2 : D) (g : C -> D) (p1' : A) (s : A -> Prop) (t : C -> Prop) : (term195 A B C D p1 f p2 g p1' s t) = (term201 A B C D p1 f p2 g p1' s t).
Proof. exact (TRANS (@lem4358282 A B C D p1 f p2 g p1' s t) (@lem4358289 A B C D p1 f p2 g p1' s t)). Qed.
Lemma lem4358291 {A B C D : Type'} (p1 : B) (f : A -> B) (p2 : D) (g : C -> D) (p1' : A) (s : A -> Prop) (t : C -> Prop) : (term142 A B C D p1 f p2 g p1' s t) = (term142 A B C D p1 f p2 g p1' s t).
Proof. exact (fun_ext (fun p2' : C => @lem4358280 A B C D p1 f p2 g p1' s p2' t)). Qed.
Lemma lem4358292 {C : Type'} : (@ex C) = (@ex C).
Proof. exact (eq_refl (@ex C)). Qed.
Lemma lem4358293 {A B C D : Type'} (p1 : B) (f : A -> B) (p2 : D) (g : C -> D) (p1' : A) (s : A -> Prop) (t : C -> Prop) : (term143 A B C D p1 f p2 g p1' s t) = (term143 A B C D p1 f p2 g p1' s t).
Proof. exact (MK_COMB (@lem4358292 C) (@lem4358291 A B C D p1 f p2 g p1' s t)). Qed.
Lemma lem4358294 {A : Type'} (P : A -> Prop) : (term193 A P) = (term194 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem4358295 {A B C D : Type'} (p1 : B) (f : A -> B) (p2 : D) (g : C -> D) (s : A -> Prop) (t : C -> Prop) : (term202 A B C D p1 f p2 g s t) = (term203 A B C D p1 f p2 g s t).
Proof. exact (@lem4358294 A (term144 A B C D p1 f p2 g s t)). Qed.
Lemma lem4358296 {A B C D : Type'} (p1 : B) (f : A -> B) (p2 : D) (g : C -> D) (p1' : A) (s : A -> Prop) (t : C -> Prop) : (term204 A B C D p1 f p2 g s t p1') = (term143 A B C D p1 f p2 g p1' s t).
Proof. exact (eq_refl (term204 A B C D p1 f p2 g s t p1')). Qed.
Lemma lem4358297 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4358298 {A B C D : Type'} (p1 : B) (f : A -> B) (p2 : D) (g : C -> D) (p1' : A) (s : A -> Prop) (t : C -> Prop) : (term205 A B C D p1 f p2 g s t p1') = (term195 A B C D p1 f p2 g p1' s t).
Proof. exact (MK_COMB (@lem4358297) (@lem4358296 A B C D p1 f p2 g p1' s t)). Qed.
Lemma lem4358299 {A B C D : Type'} (p1 : B) (f : A -> B) (p2 : D) (g : C -> D) (p1' : A) (s : A -> Prop) (t : C -> Prop) : (term205 A B C D p1 f p2 g s t p1') = (term201 A B C D p1 f p2 g p1' s t).
Proof. exact (TRANS (@lem4358298 A B C D p1 f p2 g p1' s t) (@lem4358290 A B C D p1 f p2 g p1' s t)). Qed.
Lemma lem4358300 {A B C D : Type'} (p1 : B) (f : A -> B) (p2 : D) (g : C -> D) (s : A -> Prop) (t : C -> Prop) : (term206 A B C D p1 f p2 g s t) = (term207 A B C D p1 f p2 g s t).
Proof. exact (fun_ext (fun p1' : A => @lem4358299 A B C D p1 f p2 g p1' s t)). Qed.
Lemma lem4358301 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4358302 {A B C D : Type'} (p1 : B) (f : A -> B) (p2 : D) (g : C -> D) (s : A -> Prop) (t : C -> Prop) : (term203 A B C D p1 f p2 g s t) = (term208 A B C D p1 f p2 g s t).
Proof. exact (MK_COMB (@lem4358301 A) (@lem4358300 A B C D p1 f p2 g s t)). Qed.
Lemma lem4358303 {A B C D : Type'} (p1 : B) (f : A -> B) (p2 : D) (g : C -> D) (s : A -> Prop) (t : C -> Prop) : (term202 A B C D p1 f p2 g s t) = (term208 A B C D p1 f p2 g s t).
Proof. exact (TRANS (@lem4358295 A B C D p1 f p2 g s t) (@lem4358302 A B C D p1 f p2 g s t)). Qed.
Lemma lem4358304 {A B C D : Type'} (p1 : B) (f : A -> B) (p2 : D) (g : C -> D) (s : A -> Prop) (t : C -> Prop) : (term144 A B C D p1 f p2 g s t) = (term144 A B C D p1 f p2 g s t).
Proof. exact (fun_ext (fun p1' : A => @lem4358293 A B C D p1 f p2 g p1' s t)). Qed.
Lemma lem4358305 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4358306 {A B C D : Type'} (p1 : B) (f : A -> B) (p2 : D) (g : C -> D) (s : A -> Prop) (t : C -> Prop) : (term145 A B C D p1 f p2 g s t) = (term145 A B C D p1 f p2 g s t).
Proof. exact (MK_COMB (@lem4358305 A) (@lem4358304 A B C D p1 f p2 g s t)). Qed.
Lemma lem4358315 {A B : Type'} (p1 : B) (f : A -> B) (x : A) (s : A -> Prop) : (term209 A B p1 f x s) = (term210 A B p1 f x s).
Proof. exact (@lem17045 (p1 = (f x)) (@IN A x s)). Qed.
Lemma lem4358318 {A B : Type'} (p1 : B) (f : A -> B) (x : A) (s : A -> Prop) : (term180 A B p1 f x s) = (term180 A B p1 f x s).
Proof. exact (eq_refl (term180 A B p1 f x s)). Qed.
Lemma lem4358319 {A : Type'} (P : A -> Prop) : (term193 A P) = (term194 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem4358320 {A B : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) : (term211 A B p1 f s) = (term212 A B p1 f s).
Proof. exact (@lem4358319 A (term181 A B p1 f s)). Qed.
Lemma lem4358321 {A B : Type'} (p1 : B) (f : A -> B) (x : A) (s : A -> Prop) : (term213 A B p1 f s x) = (term180 A B p1 f x s).
Proof. exact (eq_refl (term213 A B p1 f s x)). Qed.
Lemma lem4358322 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4358323 {A B : Type'} (p1 : B) (f : A -> B) (x : A) (s : A -> Prop) : (term214 A B p1 f s x) = (term209 A B p1 f x s).
Proof. exact (MK_COMB (@lem4358322) (@lem4358321 A B p1 f x s)). Qed.
Lemma lem4358324 {A B : Type'} (p1 : B) (f : A -> B) (x : A) (s : A -> Prop) : (term214 A B p1 f s x) = (term210 A B p1 f x s).
Proof. exact (TRANS (@lem4358323 A B p1 f x s) (@lem4358315 A B p1 f x s)). Qed.
Lemma lem4358325 {A B : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) : (term215 A B p1 f s) = (term216 A B p1 f s).
Proof. exact (fun_ext (fun x : A => @lem4358324 A B p1 f x s)). Qed.
Lemma lem4358326 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4358327 {A B : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) : (term212 A B p1 f s) = (term217 A B p1 f s).
Proof. exact (MK_COMB (@lem4358326 A) (@lem4358325 A B p1 f s)). Qed.
Lemma lem4358328 {A B : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) : (term211 A B p1 f s) = (term217 A B p1 f s).
Proof. exact (TRANS (@lem4358320 A B p1 f s) (@lem4358327 A B p1 f s)). Qed.
Lemma lem4358329 {A B : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) : (term181 A B p1 f s) = (term181 A B p1 f s).
Proof. exact (fun_ext (fun x : A => @lem4358318 A B p1 f x s)). Qed.
Lemma lem4358330 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4358331 {A B : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) : (term36 A B p1 f s) = (term36 A B p1 f s).
Proof. exact (MK_COMB (@lem4358330 A) (@lem4358329 A B p1 f s)). Qed.
Lemma lem4358340 {C D : Type'} (p2 : D) (g : C -> D) (x : C) (t : C -> Prop) : (term209 C D p2 g x t) = (term210 C D p2 g x t).
Proof. exact (@lem17045 (p2 = (g x)) (@IN C x t)). Qed.
Lemma lem4358343 {C D : Type'} (p2 : D) (g : C -> D) (x : C) (t : C -> Prop) : (term180 C D p2 g x t) = (term180 C D p2 g x t).
Proof. exact (eq_refl (term180 C D p2 g x t)). Qed.
Lemma lem4358344 {C : Type'} (P : C -> Prop) : (term193 C P) = (term194 C P).
Proof. exact (@lem18394 C P). Qed.
Lemma lem4358345 {C D : Type'} (p2 : D) (g : C -> D) (t : C -> Prop) : (term211 C D p2 g t) = (term212 C D p2 g t).
Proof. exact (@lem4358344 C (term181 C D p2 g t)). Qed.
Lemma lem4358346 {C D : Type'} (p2 : D) (g : C -> D) (x : C) (t : C -> Prop) : (term213 C D p2 g t x) = (term180 C D p2 g x t).
Proof. exact (eq_refl (term213 C D p2 g t x)). Qed.
Lemma lem4358347 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4358348 {C D : Type'} (p2 : D) (g : C -> D) (x : C) (t : C -> Prop) : (term214 C D p2 g t x) = (term209 C D p2 g x t).
Proof. exact (MK_COMB (@lem4358347) (@lem4358346 C D p2 g x t)). Qed.
Lemma lem4358349 {C D : Type'} (p2 : D) (g : C -> D) (x : C) (t : C -> Prop) : (term214 C D p2 g t x) = (term210 C D p2 g x t).
Proof. exact (TRANS (@lem4358348 C D p2 g x t) (@lem4358340 C D p2 g x t)). Qed.
Lemma lem4358350 {C D : Type'} (p2 : D) (g : C -> D) (t : C -> Prop) : (term215 C D p2 g t) = (term216 C D p2 g t).
Proof. exact (fun_ext (fun x : C => @lem4358349 C D p2 g x t)). Qed.
Lemma lem4358351 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem4358352 {C D : Type'} (p2 : D) (g : C -> D) (t : C -> Prop) : (term212 C D p2 g t) = (term217 C D p2 g t).
Proof. exact (MK_COMB (@lem4358351 C) (@lem4358350 C D p2 g t)). Qed.
Lemma lem4358353 {C D : Type'} (p2 : D) (g : C -> D) (t : C -> Prop) : (term211 C D p2 g t) = (term217 C D p2 g t).
Proof. exact (TRANS (@lem4358345 C D p2 g t) (@lem4358352 C D p2 g t)). Qed.
Lemma lem4358354 {C D : Type'} (p2 : D) (g : C -> D) (t : C -> Prop) : (term181 C D p2 g t) = (term181 C D p2 g t).
Proof. exact (fun_ext (fun x : C => @lem4358343 C D p2 g x t)). Qed.
Lemma lem4358355 {C : Type'} : (@ex C) = (@ex C).
Proof. exact (eq_refl (@ex C)). Qed.
Lemma lem4358356 {C D : Type'} (p2 : D) (g : C -> D) (t : C -> Prop) : (term36 C D p2 g t) = (term36 C D p2 g t).
Proof. exact (MK_COMB (@lem4358355 C) (@lem4358354 C D p2 g t)). Qed.
Lemma lem4358357 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4358358 {A B : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) : (term218 A B p1 f s) = (term219 A B p1 f s).
Proof. exact (MK_COMB (@lem4358357) (@lem4358328 A B p1 f s)). Qed.
Lemma lem4358359 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term220 A B C D p1 f s p2 g t) = (term221 A B C D p1 f s p2 g t).
Proof. exact (MK_COMB (@lem4358358 A B p1 f s) (@lem4358353 C D p2 g t)). Qed.
Lemma lem4358360 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term222 A B C D p1 f s p2 g t) = (term220 A B C D p1 f s p2 g t).
Proof. exact (@lem17045 (term36 A B p1 f s) (term36 C D p2 g t)). Qed.
Lemma lem4358361 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term222 A B C D p1 f s p2 g t) = (term221 A B C D p1 f s p2 g t).
Proof. exact (TRANS (@lem4358360 A B C D p1 f s p2 g t) (@lem4358359 A B C D p1 f s p2 g t)). Qed.
Lemma lem4358362 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4358363 {A B : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) : (term150 A B p1 f s) = (term150 A B p1 f s).
Proof. exact (MK_COMB (@lem4358362) (@lem4358331 A B p1 f s)). Qed.
Lemma lem4358364 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term151 A B C D p1 f s p2 g t) = (term151 A B C D p1 f s p2 g t).
Proof. exact (MK_COMB (@lem4358363 A B p1 f s) (@lem4358356 C D p2 g t)). Qed.
Lemma lem4358365 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4358366 {A B C D : Type'} (p1 : B) (f : A -> B) (p2 : D) (g : C -> D) (s : A -> Prop) (t : C -> Prop) : (term223 A B C D p1 f p2 g s t) = (term224 A B C D p1 f p2 g s t).
Proof. exact (MK_COMB (@lem4358365) (@lem4358303 A B C D p1 f p2 g s t)). Qed.
Lemma lem4358367 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term225 A B C D p1 f s p2 g t) = (term226 A B C D p1 f s p2 g t).
Proof. exact (MK_COMB (@lem4358366 A B C D p1 f p2 g s t) (@lem4358364 A B C D p1 f s p2 g t)). Qed.
Lemma lem4358368 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4358369 {A B C D : Type'} (p1 : B) (f : A -> B) (p2 : D) (g : C -> D) (s : A -> Prop) (t : C -> Prop) : (term227 A B C D p1 f p2 g s t) = (term227 A B C D p1 f p2 g s t).
Proof. exact (MK_COMB (@lem4358368) (@lem4358306 A B C D p1 f p2 g s t)). Qed.
Lemma lem4358370 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term228 A B C D p1 f s p2 g t) = (term229 A B C D p1 f s p2 g t).
Proof. exact (MK_COMB (@lem4358369 A B C D p1 f p2 g s t) (@lem4358361 A B C D p1 f s p2 g t)). Qed.
Lemma lem4358371 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4358372 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term230 A B C D p1 f s p2 g t) = (term231 A B C D p1 f s p2 g t).
Proof. exact (MK_COMB (@lem4358371) (@lem4358370 A B C D p1 f s p2 g t)). Qed.
Lemma lem4358373 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term232 A B C D p1 f s p2 g t) = (term233 A B C D p1 f s p2 g t).
Proof. exact (MK_COMB (@lem4358372 A B C D p1 f s p2 g t) (@lem4358367 A B C D p1 f s p2 g t)). Qed.
Lemma lem4358374 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term183 A B C D p1 f s p2 g t) = (term232 A B C D p1 f s p2 g t).
Proof. exact (@lem17646 (term145 A B C D p1 f p2 g s t) (term151 A B C D p1 f s p2 g t)). Qed.
Lemma lem4358375 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term183 A B C D p1 f s p2 g t) = (term233 A B C D p1 f s p2 g t).
Proof. exact (TRANS (@lem4358374 A B C D p1 f s p2 g t) (@lem4358373 A B C D p1 f s p2 g t)). Qed.
Lemma lem4358674 {A : Type'} (P : A -> Prop) (Q : Prop) : (term234 A P Q) = (term235 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4358675 {A : Type'} (P : A -> Prop) (Q : Prop) : (term234 A P Q) = (term235 A P Q).
Proof. exact (@lem4358674 A P Q). Qed.
Lemma lem4358676 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term236 A B C D p1 f s p2 g t) = (term237 A B C D p1 f s p2 g t).
Proof. exact (@lem4358675 A (term144 A B C D p1 f p2 g s t) (term221 A B C D p1 f s p2 g t)). Qed.
Lemma lem4358677 {A B C D : Type'} (p1 : B) (f : A -> B) (p2 : D) (g : C -> D) (p1' : A) (s : A -> Prop) (t : C -> Prop) : (term204 A B C D p1 f p2 g s t p1') = (term143 A B C D p1 f p2 g p1' s t).
Proof. exact (eq_refl (term204 A B C D p1 f p2 g s t p1')). Qed.
Lemma lem4358678 {A B C D : Type'} (p1 : B) (f : A -> B) (p2 : D) (g : C -> D) (s : A -> Prop) (t : C -> Prop) : (term238 A B C D p1 f p2 g s t) = (term144 A B C D p1 f p2 g s t).
Proof. exact (fun_ext (fun p1' : A => @lem4358677 A B C D p1 f p2 g p1' s t)). Qed.
Lemma lem4358679 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4358680 {A B C D : Type'} (p1 : B) (f : A -> B) (p2 : D) (g : C -> D) (s : A -> Prop) (t : C -> Prop) : (term239 A B C D p1 f p2 g s t) = (term145 A B C D p1 f p2 g s t).
Proof. exact (MK_COMB (@lem4358679 A) (@lem4358678 A B C D p1 f p2 g s t)). Qed.
Lemma lem4358681 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4358682 {A B C D : Type'} (p1 : B) (f : A -> B) (p2 : D) (g : C -> D) (s : A -> Prop) (t : C -> Prop) : (term240 A B C D p1 f p2 g s t) = (term227 A B C D p1 f p2 g s t).
Proof. exact (MK_COMB (@lem4358681) (@lem4358680 A B C D p1 f p2 g s t)). Qed.
Lemma lem4358683 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term221 A B C D p1 f s p2 g t) = (term221 A B C D p1 f s p2 g t).
Proof. exact (eq_refl (term221 A B C D p1 f s p2 g t)). Qed.
Lemma lem4358684 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term236 A B C D p1 f s p2 g t) = (term229 A B C D p1 f s p2 g t).
Proof. exact (MK_COMB (@lem4358682 A B C D p1 f p2 g s t) (@lem4358683 A B C D p1 f s p2 g t)). Qed.
Lemma lem4358685 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4358686 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term241 A B C D p1 f s p2 g t) = (term242 A B C D p1 f s p2 g t).
Proof. exact (MK_COMB (@lem4358685) (@lem4358684 A B C D p1 f s p2 g t)). Qed.
Lemma lem4358687 {A B C D : Type'} (p1 : B) (f : A -> B) (p2 : D) (g : C -> D) (p1' : A) (s : A -> Prop) (t : C -> Prop) : (term204 A B C D p1 f p2 g s t p1') = (term143 A B C D p1 f p2 g p1' s t).
Proof. exact (eq_refl (term204 A B C D p1 f p2 g s t p1')). Qed.
Lemma lem4358688 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4358689 {A B C D : Type'} (p1 : B) (f : A -> B) (p2 : D) (g : C -> D) (p1' : A) (s : A -> Prop) (t : C -> Prop) : (term243 A B C D p1 f p2 g s t p1') = (term244 A B C D p1 f p2 g p1' s t).
Proof. exact (MK_COMB (@lem4358688) (@lem4358687 A B C D p1 f p2 g p1' s t)). Qed.
Lemma lem4358690 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term221 A B C D p1 f s p2 g t) = (term221 A B C D p1 f s p2 g t).
Proof. exact (eq_refl (term221 A B C D p1 f s p2 g t)). Qed.
Lemma lem4358691 {A B C D : Type'} (p1 : A) (p1' : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term245 A B C D p1 p1' f s p2 g t) = (term246 A B C D p1 p1' f s p2 g t).
Proof. exact (MK_COMB (@lem4358689 A B C D p1' f p2 g p1 s t) (@lem4358690 A B C D p1' f s p2 g t)). Qed.
Lemma lem4358692 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term247 A B C D p1 f s p2 g t) = (term248 A B C D p1 f s p2 g t).
Proof. exact (fun_ext (fun p1' : A => @lem4358691 A B C D p1' p1 f s p2 g t)). Qed.
Lemma lem4358693 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4358694 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term237 A B C D p1 f s p2 g t) = (term249 A B C D p1 f s p2 g t).
Proof. exact (MK_COMB (@lem4358693 A) (@lem4358692 A B C D p1 f s p2 g t)). Qed.
Lemma lem4358695 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : ((term236 A B C D p1 f s p2 g t) = (term237 A B C D p1 f s p2 g t)) = ((term229 A B C D p1 f s p2 g t) = (term249 A B C D p1 f s p2 g t)).
Proof. exact (MK_COMB (@lem4358686 A B C D p1 f s p2 g t) (@lem4358694 A B C D p1 f s p2 g t)). Qed.
Lemma lem4358696 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term229 A B C D p1 f s p2 g t) = (term249 A B C D p1 f s p2 g t).
Proof. exact (EQ_MP (@lem4358695 A B C D p1 f s p2 g t) (@lem4358676 A B C D p1 f s p2 g t)). Qed.
Lemma lem4358698 {A : Type'} (P : A -> Prop) (Q : Prop) : (term234 A P Q) = (term235 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4358699 {C : Type'} (P : C -> Prop) (Q : Prop) : (term234 C P Q) = (term235 C P Q).
Proof. exact (@lem4358698 C P Q). Qed.
Lemma lem4358700 {A B C D : Type'} (p1 : A) (p1' : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term250 A B C D p1 p1' f s p2 g t) = (term251 A B C D p1 p1' f s p2 g t).
Proof. exact (@lem4358699 C (term142 A B C D p1' f p2 g p1 s t) (term221 A B C D p1' f s p2 g t)). Qed.
Lemma lem4358701 {A B C D : Type'} (p1 : B) (f : A -> B) (p2 : D) (g : C -> D) (p1' : A) (s : A -> Prop) (p2' : C) (t : C -> Prop) : (term197 A B C D p1 f p2 g p1' s t p2') = (term141 A B C D p1 f p2 g p1' s p2' t).
Proof. exact (eq_refl (term197 A B C D p1 f p2 g p1' s t p2')). Qed.
Lemma lem4358702 {A B C D : Type'} (p1 : B) (f : A -> B) (p2 : D) (g : C -> D) (p1' : A) (s : A -> Prop) (t : C -> Prop) : (term252 A B C D p1 f p2 g p1' s t) = (term142 A B C D p1 f p2 g p1' s t).
Proof. exact (fun_ext (fun p2' : C => @lem4358701 A B C D p1 f p2 g p1' s p2' t)). Qed.
Lemma lem4358703 {C : Type'} : (@ex C) = (@ex C).
Proof. exact (eq_refl (@ex C)). Qed.
Lemma lem4358704 {A B C D : Type'} (p1 : B) (f : A -> B) (p2 : D) (g : C -> D) (p1' : A) (s : A -> Prop) (t : C -> Prop) : (term253 A B C D p1 f p2 g p1' s t) = (term143 A B C D p1 f p2 g p1' s t).
Proof. exact (MK_COMB (@lem4358703 C) (@lem4358702 A B C D p1 f p2 g p1' s t)). Qed.
Lemma lem4358705 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4358706 {A B C D : Type'} (p1 : B) (f : A -> B) (p2 : D) (g : C -> D) (p1' : A) (s : A -> Prop) (t : C -> Prop) : (term254 A B C D p1 f p2 g p1' s t) = (term244 A B C D p1 f p2 g p1' s t).
Proof. exact (MK_COMB (@lem4358705) (@lem4358704 A B C D p1 f p2 g p1' s t)). Qed.
Lemma lem4358707 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term221 A B C D p1 f s p2 g t) = (term221 A B C D p1 f s p2 g t).
Proof. exact (eq_refl (term221 A B C D p1 f s p2 g t)). Qed.
Lemma lem4358708 {A B C D : Type'} (p1 : A) (p1' : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term250 A B C D p1 p1' f s p2 g t) = (term246 A B C D p1 p1' f s p2 g t).
Proof. exact (MK_COMB (@lem4358706 A B C D p1' f p2 g p1 s t) (@lem4358707 A B C D p1' f s p2 g t)). Qed.
Lemma lem4358709 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4358710 {A B C D : Type'} (p1 : A) (p1' : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term255 A B C D p1 p1' f s p2 g t) = (term256 A B C D p1 p1' f s p2 g t).
Proof. exact (MK_COMB (@lem4358709) (@lem4358708 A B C D p1 p1' f s p2 g t)). Qed.
Lemma lem4358711 {A B C D : Type'} (p1 : B) (f : A -> B) (p2 : D) (g : C -> D) (p1' : A) (s : A -> Prop) (p2' : C) (t : C -> Prop) : (term197 A B C D p1 f p2 g p1' s t p2') = (term141 A B C D p1 f p2 g p1' s p2' t).
Proof. exact (eq_refl (term197 A B C D p1 f p2 g p1' s t p2')). Qed.
Lemma lem4358712 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4358713 {A B C D : Type'} (p1 : B) (f : A -> B) (p2 : D) (g : C -> D) (p1' : A) (s : A -> Prop) (p2' : C) (t : C -> Prop) : (term257 A B C D p1 f p2 g p1' s t p2') = (term258 A B C D p1 f p2 g p1' s p2' t).
Proof. exact (MK_COMB (@lem4358712) (@lem4358711 A B C D p1 f p2 g p1' s p2' t)). Qed.
Lemma lem4358714 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term221 A B C D p1 f s p2 g t) = (term221 A B C D p1 f s p2 g t).
Proof. exact (eq_refl (term221 A B C D p1 f s p2 g t)). Qed.
Lemma lem4358715 {A B C D : Type'} (p1 : A) (p2 : C) (p1' : B) (f : A -> B) (s : A -> Prop) (p2' : D) (g : C -> D) (t : C -> Prop) : (term259 A B C D p1 p2 p1' f s p2' g t) = (term260 A B C D p1 p2 p1' f s p2' g t).
Proof. exact (MK_COMB (@lem4358713 A B C D p1' f p2' g p1 s p2 t) (@lem4358714 A B C D p1' f s p2' g t)). Qed.
Lemma lem4358716 {A B C D : Type'} (p1 : A) (p1' : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term261 A B C D p1 p1' f s p2 g t) = (term262 A B C D p1 p1' f s p2 g t).
Proof. exact (fun_ext (fun p2' : C => @lem4358715 A B C D p1 p2' p1' f s p2 g t)). Qed.
Lemma lem4358717 {C : Type'} : (@ex C) = (@ex C).
Proof. exact (eq_refl (@ex C)). Qed.
Lemma lem4358718 {A B C D : Type'} (p1 : A) (p1' : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term251 A B C D p1 p1' f s p2 g t) = (term263 A B C D p1 p1' f s p2 g t).
Proof. exact (MK_COMB (@lem4358717 C) (@lem4358716 A B C D p1 p1' f s p2 g t)). Qed.
Lemma lem4358719 {A B C D : Type'} (p1 : A) (p1' : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : ((term250 A B C D p1 p1' f s p2 g t) = (term251 A B C D p1 p1' f s p2 g t)) = ((term246 A B C D p1 p1' f s p2 g t) = (term263 A B C D p1 p1' f s p2 g t)).
Proof. exact (MK_COMB (@lem4358710 A B C D p1 p1' f s p2 g t) (@lem4358718 A B C D p1 p1' f s p2 g t)). Qed.
Lemma lem4358720 {A B C D : Type'} (p1 : A) (p1' : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term246 A B C D p1 p1' f s p2 g t) = (term263 A B C D p1 p1' f s p2 g t).
Proof. exact (EQ_MP (@lem4358719 A B C D p1 p1' f s p2 g t) (@lem4358700 A B C D p1 p1' f s p2 g t)). Qed.
Lemma lem4358721 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term248 A B C D p1 f s p2 g t) = (term264 A B C D p1 f s p2 g t).
Proof. exact (fun_ext (fun p1' : A => @lem4358720 A B C D p1' p1 f s p2 g t)). Qed.
Lemma lem4358722 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4358723 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term249 A B C D p1 f s p2 g t) = (term265 A B C D p1 f s p2 g t).
Proof. exact (MK_COMB (@lem4358722 A) (@lem4358721 A B C D p1 f s p2 g t)). Qed.
Lemma lem4358724 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term229 A B C D p1 f s p2 g t) = (term265 A B C D p1 f s p2 g t).
Proof. exact (TRANS (@lem4358696 A B C D p1 f s p2 g t) (@lem4358723 A B C D p1 f s p2 g t)). Qed.
Lemma lem4358725 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4358726 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term231 A B C D p1 f s p2 g t) = (term266 A B C D p1 f s p2 g t).
Proof. exact (MK_COMB (@lem4358725) (@lem4358724 A B C D p1 f s p2 g t)). Qed.
Lemma lem4358728 {A : Type'} (P : A -> Prop) (Q : Prop) : (term234 A P Q) = (term235 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4358729 {A : Type'} (P : A -> Prop) (Q : Prop) : (term234 A P Q) = (term235 A P Q).
Proof. exact (@lem4358728 A P Q). Qed.
Lemma lem4358730 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term267 A B C D p1 f s p2 g t) = (term268 A B C D p1 f s p2 g t).
Proof. exact (@lem4358729 A (term181 A B p1 f s) (term36 C D p2 g t)). Qed.
Lemma lem4358731 {A B : Type'} (p1 : B) (f : A -> B) (x : A) (s : A -> Prop) : (term213 A B p1 f s x) = (term180 A B p1 f x s).
Proof. exact (eq_refl (term213 A B p1 f s x)). Qed.
Lemma lem4358732 {A B : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) : (term269 A B p1 f s) = (term181 A B p1 f s).
Proof. exact (fun_ext (fun x : A => @lem4358731 A B p1 f x s)). Qed.
Lemma lem4358733 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4358734 {A B : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) : (term270 A B p1 f s) = (term36 A B p1 f s).
Proof. exact (MK_COMB (@lem4358733 A) (@lem4358732 A B p1 f s)). Qed.
Lemma lem4358735 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4358736 {A B : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) : (term271 A B p1 f s) = (term150 A B p1 f s).
Proof. exact (MK_COMB (@lem4358735) (@lem4358734 A B p1 f s)). Qed.
Lemma lem4358737 {C D : Type'} (p2 : D) (g : C -> D) (t : C -> Prop) : (term36 C D p2 g t) = (term36 C D p2 g t).
Proof. exact (eq_refl (term36 C D p2 g t)). Qed.
Lemma lem4358738 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term267 A B C D p1 f s p2 g t) = (term151 A B C D p1 f s p2 g t).
Proof. exact (MK_COMB (@lem4358736 A B p1 f s) (@lem4358737 C D p2 g t)). Qed.
Lemma lem4358739 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4358740 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term272 A B C D p1 f s p2 g t) = (term273 A B C D p1 f s p2 g t).
Proof. exact (MK_COMB (@lem4358739) (@lem4358738 A B C D p1 f s p2 g t)). Qed.
Lemma lem4358741 {A B : Type'} (p1 : B) (f : A -> B) (x : A) (s : A -> Prop) : (term213 A B p1 f s x) = (term180 A B p1 f x s).
Proof. exact (eq_refl (term213 A B p1 f s x)). Qed.
Lemma lem4358742 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4358743 {A B : Type'} (p1 : B) (f : A -> B) (x : A) (s : A -> Prop) : (term274 A B p1 f s x) = (term275 A B p1 f x s).
Proof. exact (MK_COMB (@lem4358742) (@lem4358741 A B p1 f x s)). Qed.
Lemma lem4358744 {C D : Type'} (p2 : D) (g : C -> D) (t : C -> Prop) : (term36 C D p2 g t) = (term36 C D p2 g t).
Proof. exact (eq_refl (term36 C D p2 g t)). Qed.
Lemma lem4358745 {A B C D : Type'} (p1 : B) (f : A -> B) (x : A) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term276 A B C D p1 f s x p2 g t) = (term277 A B C D p1 f x s p2 g t).
Proof. exact (MK_COMB (@lem4358743 A B p1 f x s) (@lem4358744 C D p2 g t)). Qed.
Lemma lem4358746 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term278 A B C D p1 f s p2 g t) = (term279 A B C D p1 f s p2 g t).
Proof. exact (fun_ext (fun x : A => @lem4358745 A B C D p1 f x s p2 g t)). Qed.
Lemma lem4358747 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4358748 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term268 A B C D p1 f s p2 g t) = (term280 A B C D p1 f s p2 g t).
Proof. exact (MK_COMB (@lem4358747 A) (@lem4358746 A B C D p1 f s p2 g t)). Qed.
Lemma lem4358749 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : ((term267 A B C D p1 f s p2 g t) = (term268 A B C D p1 f s p2 g t)) = ((term151 A B C D p1 f s p2 g t) = (term280 A B C D p1 f s p2 g t)).
Proof. exact (MK_COMB (@lem4358740 A B C D p1 f s p2 g t) (@lem4358748 A B C D p1 f s p2 g t)). Qed.
Lemma lem4358750 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term151 A B C D p1 f s p2 g t) = (term280 A B C D p1 f s p2 g t).
Proof. exact (EQ_MP (@lem4358749 A B C D p1 f s p2 g t) (@lem4358730 A B C D p1 f s p2 g t)). Qed.
Lemma lem4358752 {A : Type'} (P : Prop) (Q : A -> Prop) : (term281 A P Q) = (term282 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4358753 {C : Type'} (P : Prop) (Q : C -> Prop) : (term281 C P Q) = (term282 C P Q).
Proof. exact (@lem4358752 C P Q). Qed.
Lemma lem4358754 {A B C D : Type'} (p1 : B) (f : A -> B) (x : A) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term283 A B C D p1 f x s p2 g t) = (term284 A B C D p1 f x s p2 g t).
Proof. exact (@lem4358753 C (term180 A B p1 f x s) (term181 C D p2 g t)). Qed.
Lemma lem4358755 {C D : Type'} (p2 : D) (g : C -> D) (x : C) (t : C -> Prop) : (term213 C D p2 g t x) = (term180 C D p2 g x t).
Proof. exact (eq_refl (term213 C D p2 g t x)). Qed.
Lemma lem4358756 {C D : Type'} (p2 : D) (g : C -> D) (t : C -> Prop) : (term269 C D p2 g t) = (term181 C D p2 g t).
Proof. exact (fun_ext (fun x : C => @lem4358755 C D p2 g x t)). Qed.
Lemma lem4358757 {C : Type'} : (@ex C) = (@ex C).
Proof. exact (eq_refl (@ex C)). Qed.
Lemma lem4358758 {C D : Type'} (p2 : D) (g : C -> D) (t : C -> Prop) : (term270 C D p2 g t) = (term36 C D p2 g t).
Proof. exact (MK_COMB (@lem4358757 C) (@lem4358756 C D p2 g t)). Qed.
Lemma lem4358759 {A B : Type'} (p1 : B) (f : A -> B) (x : A) (s : A -> Prop) : (term275 A B p1 f x s) = (term275 A B p1 f x s).
Proof. exact (eq_refl (term275 A B p1 f x s)). Qed.
Lemma lem4358760 {A B C D : Type'} (p1 : B) (f : A -> B) (x : A) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term283 A B C D p1 f x s p2 g t) = (term277 A B C D p1 f x s p2 g t).
Proof. exact (MK_COMB (@lem4358759 A B p1 f x s) (@lem4358758 C D p2 g t)). Qed.
Lemma lem4358761 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4358762 {A B C D : Type'} (p1 : B) (f : A -> B) (x : A) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term285 A B C D p1 f x s p2 g t) = (term286 A B C D p1 f x s p2 g t).
Proof. exact (MK_COMB (@lem4358761) (@lem4358760 A B C D p1 f x s p2 g t)). Qed.
Lemma lem4358763 {C D : Type'} (p2 : D) (g : C -> D) (x : C) (t : C -> Prop) : (term213 C D p2 g t x) = (term180 C D p2 g x t).
Proof. exact (eq_refl (term213 C D p2 g t x)). Qed.
Lemma lem4358764 {A B : Type'} (p1 : B) (f : A -> B) (x : A) (s : A -> Prop) : (term275 A B p1 f x s) = (term275 A B p1 f x s).
Proof. exact (eq_refl (term275 A B p1 f x s)). Qed.
Lemma lem4358765 {A B C D : Type'} (p1 : B) (f : A -> B) (x : A) (s : A -> Prop) (p2 : D) (g : C -> D) (x' : C) (t : C -> Prop) : (term287 A B C D p1 f x s p2 g t x') = (term288 A B C D p1 f x s p2 g x' t).
Proof. exact (MK_COMB (@lem4358764 A B p1 f x s) (@lem4358763 C D p2 g x' t)). Qed.
Lemma lem4358766 {A B C D : Type'} (p1 : B) (f : A -> B) (x : A) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term289 A B C D p1 f x s p2 g t) = (term290 A B C D p1 f x s p2 g t).
Proof. exact (fun_ext (fun x' : C => @lem4358765 A B C D p1 f x s p2 g x' t)). Qed.
Lemma lem4358767 {C : Type'} : (@ex C) = (@ex C).
Proof. exact (eq_refl (@ex C)). Qed.
Lemma lem4358768 {A B C D : Type'} (p1 : B) (f : A -> B) (x : A) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term284 A B C D p1 f x s p2 g t) = (term291 A B C D p1 f x s p2 g t).
Proof. exact (MK_COMB (@lem4358767 C) (@lem4358766 A B C D p1 f x s p2 g t)). Qed.
Lemma lem4358769 {A B C D : Type'} (p1 : B) (f : A -> B) (x : A) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : ((term283 A B C D p1 f x s p2 g t) = (term284 A B C D p1 f x s p2 g t)) = ((term277 A B C D p1 f x s p2 g t) = (term291 A B C D p1 f x s p2 g t)).
Proof. exact (MK_COMB (@lem4358762 A B C D p1 f x s p2 g t) (@lem4358768 A B C D p1 f x s p2 g t)). Qed.
Lemma lem4358770 {A B C D : Type'} (p1 : B) (f : A -> B) (x : A) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term277 A B C D p1 f x s p2 g t) = (term291 A B C D p1 f x s p2 g t).
Proof. exact (EQ_MP (@lem4358769 A B C D p1 f x s p2 g t) (@lem4358754 A B C D p1 f x s p2 g t)). Qed.
Lemma lem4358771 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term279 A B C D p1 f s p2 g t) = (term292 A B C D p1 f s p2 g t).
Proof. exact (fun_ext (fun x : A => @lem4358770 A B C D p1 f x s p2 g t)). Qed.
Lemma lem4358772 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4358773 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term280 A B C D p1 f s p2 g t) = (term293 A B C D p1 f s p2 g t).
Proof. exact (MK_COMB (@lem4358772 A) (@lem4358771 A B C D p1 f s p2 g t)). Qed.
Lemma lem4358774 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term151 A B C D p1 f s p2 g t) = (term293 A B C D p1 f s p2 g t).
Proof. exact (TRANS (@lem4358750 A B C D p1 f s p2 g t) (@lem4358773 A B C D p1 f s p2 g t)). Qed.
Lemma lem4358775 {A B C D : Type'} (p1 : B) (f : A -> B) (p2 : D) (g : C -> D) (s : A -> Prop) (t : C -> Prop) : (term224 A B C D p1 f p2 g s t) = (term224 A B C D p1 f p2 g s t).
Proof. exact (eq_refl (term224 A B C D p1 f p2 g s t)). Qed.
Lemma lem4358776 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term226 A B C D p1 f s p2 g t) = (term294 A B C D p1 f s p2 g t).
Proof. exact (MK_COMB (@lem4358775 A B C D p1 f p2 g s t) (@lem4358774 A B C D p1 f s p2 g t)). Qed.
Lemma lem4358778 {A : Type'} (P : Prop) (Q : A -> Prop) : (term281 A P Q) = (term282 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4358779 {A : Type'} (P : Prop) (Q : A -> Prop) : (term281 A P Q) = (term282 A P Q).
Proof. exact (@lem4358778 A P Q). Qed.
Lemma lem4358780 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term295 A B C D p1 f s p2 g t) = (term296 A B C D p1 f s p2 g t).
Proof. exact (@lem4358779 A (term208 A B C D p1 f p2 g s t) (term292 A B C D p1 f s p2 g t)). Qed.
Lemma lem4358781 {A B C D : Type'} (p1 : B) (f : A -> B) (x : A) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term297 A B C D p1 f s p2 g t x) = (term291 A B C D p1 f x s p2 g t).
Proof. exact (eq_refl (term297 A B C D p1 f s p2 g t x)). Qed.
Lemma lem4358782 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term298 A B C D p1 f s p2 g t) = (term292 A B C D p1 f s p2 g t).
Proof. exact (fun_ext (fun x : A => @lem4358781 A B C D p1 f x s p2 g t)). Qed.
Lemma lem4358783 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4358784 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term299 A B C D p1 f s p2 g t) = (term293 A B C D p1 f s p2 g t).
Proof. exact (MK_COMB (@lem4358783 A) (@lem4358782 A B C D p1 f s p2 g t)). Qed.
Lemma lem4358785 {A B C D : Type'} (p1 : B) (f : A -> B) (p2 : D) (g : C -> D) (s : A -> Prop) (t : C -> Prop) : (term224 A B C D p1 f p2 g s t) = (term224 A B C D p1 f p2 g s t).
Proof. exact (eq_refl (term224 A B C D p1 f p2 g s t)). Qed.
Lemma lem4358786 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term295 A B C D p1 f s p2 g t) = (term294 A B C D p1 f s p2 g t).
Proof. exact (MK_COMB (@lem4358785 A B C D p1 f p2 g s t) (@lem4358784 A B C D p1 f s p2 g t)). Qed.
Lemma lem4358787 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4358788 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term300 A B C D p1 f s p2 g t) = (term301 A B C D p1 f s p2 g t).
Proof. exact (MK_COMB (@lem4358787) (@lem4358786 A B C D p1 f s p2 g t)). Qed.
Lemma lem4358789 {A B C D : Type'} (p1 : B) (f : A -> B) (x : A) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term297 A B C D p1 f s p2 g t x) = (term291 A B C D p1 f x s p2 g t).
Proof. exact (eq_refl (term297 A B C D p1 f s p2 g t x)). Qed.
Lemma lem4358790 {A B C D : Type'} (p1 : B) (f : A -> B) (p2 : D) (g : C -> D) (s : A -> Prop) (t : C -> Prop) : (term224 A B C D p1 f p2 g s t) = (term224 A B C D p1 f p2 g s t).
Proof. exact (eq_refl (term224 A B C D p1 f p2 g s t)). Qed.
Lemma lem4358791 {A B C D : Type'} (p1 : B) (f : A -> B) (x : A) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term302 A B C D p1 f s p2 g t x) = (term303 A B C D p1 f x s p2 g t).
Proof. exact (MK_COMB (@lem4358790 A B C D p1 f p2 g s t) (@lem4358789 A B C D p1 f x s p2 g t)). Qed.
Lemma lem4358792 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term304 A B C D p1 f s p2 g t) = (term305 A B C D p1 f s p2 g t).
Proof. exact (fun_ext (fun x : A => @lem4358791 A B C D p1 f x s p2 g t)). Qed.
Lemma lem4358793 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4358794 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term296 A B C D p1 f s p2 g t) = (term306 A B C D p1 f s p2 g t).
Proof. exact (MK_COMB (@lem4358793 A) (@lem4358792 A B C D p1 f s p2 g t)). Qed.
Lemma lem4358795 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : ((term295 A B C D p1 f s p2 g t) = (term296 A B C D p1 f s p2 g t)) = ((term294 A B C D p1 f s p2 g t) = (term306 A B C D p1 f s p2 g t)).
Proof. exact (MK_COMB (@lem4358788 A B C D p1 f s p2 g t) (@lem4358794 A B C D p1 f s p2 g t)). Qed.
Lemma lem4358796 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term294 A B C D p1 f s p2 g t) = (term306 A B C D p1 f s p2 g t).
Proof. exact (EQ_MP (@lem4358795 A B C D p1 f s p2 g t) (@lem4358780 A B C D p1 f s p2 g t)). Qed.
Lemma lem4358798 {A : Type'} (P : Prop) (Q : A -> Prop) : (term281 A P Q) = (term282 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4358799 {C : Type'} (P : Prop) (Q : C -> Prop) : (term281 C P Q) = (term282 C P Q).
Proof. exact (@lem4358798 C P Q). Qed.
Lemma lem4358800 {A B C D : Type'} (p1 : B) (f : A -> B) (x : A) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term307 A B C D p1 f x s p2 g t) = (term308 A B C D p1 f x s p2 g t).
Proof. exact (@lem4358799 C (term208 A B C D p1 f p2 g s t) (term290 A B C D p1 f x s p2 g t)). Qed.
Lemma lem4358801 {A B C D : Type'} (p1 : B) (f : A -> B) (x : A) (s : A -> Prop) (p2 : D) (g : C -> D) (x' : C) (t : C -> Prop) : (term309 A B C D p1 f x s p2 g t x') = (term288 A B C D p1 f x s p2 g x' t).
Proof. exact (eq_refl (term309 A B C D p1 f x s p2 g t x')). Qed.
Lemma lem4358802 {A B C D : Type'} (p1 : B) (f : A -> B) (x : A) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term310 A B C D p1 f x s p2 g t) = (term290 A B C D p1 f x s p2 g t).
Proof. exact (fun_ext (fun x' : C => @lem4358801 A B C D p1 f x s p2 g x' t)). Qed.
Lemma lem4358803 {C : Type'} : (@ex C) = (@ex C).
Proof. exact (eq_refl (@ex C)). Qed.
Lemma lem4358804 {A B C D : Type'} (p1 : B) (f : A -> B) (x : A) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term311 A B C D p1 f x s p2 g t) = (term291 A B C D p1 f x s p2 g t).
Proof. exact (MK_COMB (@lem4358803 C) (@lem4358802 A B C D p1 f x s p2 g t)). Qed.
Lemma lem4358805 {A B C D : Type'} (p1 : B) (f : A -> B) (p2 : D) (g : C -> D) (s : A -> Prop) (t : C -> Prop) : (term224 A B C D p1 f p2 g s t) = (term224 A B C D p1 f p2 g s t).
Proof. exact (eq_refl (term224 A B C D p1 f p2 g s t)). Qed.
Lemma lem4358806 {A B C D : Type'} (p1 : B) (f : A -> B) (x : A) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term307 A B C D p1 f x s p2 g t) = (term303 A B C D p1 f x s p2 g t).
Proof. exact (MK_COMB (@lem4358805 A B C D p1 f p2 g s t) (@lem4358804 A B C D p1 f x s p2 g t)). Qed.
Lemma lem4358807 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4358808 {A B C D : Type'} (p1 : B) (f : A -> B) (x : A) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term312 A B C D p1 f x s p2 g t) = (term313 A B C D p1 f x s p2 g t).
Proof. exact (MK_COMB (@lem4358807) (@lem4358806 A B C D p1 f x s p2 g t)). Qed.
Lemma lem4358809 {A B C D : Type'} (p1 : B) (f : A -> B) (x : A) (s : A -> Prop) (p2 : D) (g : C -> D) (x' : C) (t : C -> Prop) : (term309 A B C D p1 f x s p2 g t x') = (term288 A B C D p1 f x s p2 g x' t).
Proof. exact (eq_refl (term309 A B C D p1 f x s p2 g t x')). Qed.
Lemma lem4358810 {A B C D : Type'} (p1 : B) (f : A -> B) (p2 : D) (g : C -> D) (s : A -> Prop) (t : C -> Prop) : (term224 A B C D p1 f p2 g s t) = (term224 A B C D p1 f p2 g s t).
Proof. exact (eq_refl (term224 A B C D p1 f p2 g s t)). Qed.
Lemma lem4358811 {A B C D : Type'} (p1 : B) (f : A -> B) (x : A) (s : A -> Prop) (p2 : D) (g : C -> D) (x' : C) (t : C -> Prop) : (term314 A B C D p1 f x s p2 g t x') = (term315 A B C D p1 f x s p2 g x' t).
Proof. exact (MK_COMB (@lem4358810 A B C D p1 f p2 g s t) (@lem4358809 A B C D p1 f x s p2 g x' t)). Qed.
Lemma lem4358812 {A B C D : Type'} (p1 : B) (f : A -> B) (x : A) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term316 A B C D p1 f x s p2 g t) = (term317 A B C D p1 f x s p2 g t).
Proof. exact (fun_ext (fun x' : C => @lem4358811 A B C D p1 f x s p2 g x' t)). Qed.
Lemma lem4358813 {C : Type'} : (@ex C) = (@ex C).
Proof. exact (eq_refl (@ex C)). Qed.
Lemma lem4358814 {A B C D : Type'} (p1 : B) (f : A -> B) (x : A) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term308 A B C D p1 f x s p2 g t) = (term318 A B C D p1 f x s p2 g t).
Proof. exact (MK_COMB (@lem4358813 C) (@lem4358812 A B C D p1 f x s p2 g t)). Qed.
Lemma lem4358815 {A B C D : Type'} (p1 : B) (f : A -> B) (x : A) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : ((term307 A B C D p1 f x s p2 g t) = (term308 A B C D p1 f x s p2 g t)) = ((term303 A B C D p1 f x s p2 g t) = (term318 A B C D p1 f x s p2 g t)).
Proof. exact (MK_COMB (@lem4358808 A B C D p1 f x s p2 g t) (@lem4358814 A B C D p1 f x s p2 g t)). Qed.
Lemma lem4358816 {A B C D : Type'} (p1 : B) (f : A -> B) (x : A) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term303 A B C D p1 f x s p2 g t) = (term318 A B C D p1 f x s p2 g t).
Proof. exact (EQ_MP (@lem4358815 A B C D p1 f x s p2 g t) (@lem4358800 A B C D p1 f x s p2 g t)). Qed.
Lemma lem4358817 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term305 A B C D p1 f s p2 g t) = (term319 A B C D p1 f s p2 g t).
Proof. exact (fun_ext (fun x : A => @lem4358816 A B C D p1 f x s p2 g t)). Qed.
Lemma lem4358818 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4358819 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term306 A B C D p1 f s p2 g t) = (term320 A B C D p1 f s p2 g t).
Proof. exact (MK_COMB (@lem4358818 A) (@lem4358817 A B C D p1 f s p2 g t)). Qed.
Lemma lem4358820 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term294 A B C D p1 f s p2 g t) = (term320 A B C D p1 f s p2 g t).
Proof. exact (TRANS (@lem4358796 A B C D p1 f s p2 g t) (@lem4358819 A B C D p1 f s p2 g t)). Qed.
Lemma lem4358821 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term226 A B C D p1 f s p2 g t) = (term320 A B C D p1 f s p2 g t).
Proof. exact (TRANS (@lem4358776 A B C D p1 f s p2 g t) (@lem4358820 A B C D p1 f s p2 g t)). Qed.
Lemma lem4358822 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term233 A B C D p1 f s p2 g t) = (term321 A B C D p1 f s p2 g t).
Proof. exact (MK_COMB (@lem4358726 A B C D p1 f s p2 g t) (@lem4358821 A B C D p1 f s p2 g t)). Qed.
Lemma lem4358824 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term322 A P Q) = (term323 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4358825 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term322 A P Q) = (term323 A P Q).
Proof. exact (@lem4358824 A P Q). Qed.
Lemma lem4358826 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term324 A B C D p1 f s p2 g t) = (term325 A B C D p1 f s p2 g t).
Proof. exact (@lem4358825 A (term264 A B C D p1 f s p2 g t) (term319 A B C D p1 f s p2 g t)). Qed.
Lemma lem4358827 {A B C D : Type'} (p1 : A) (p1' : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term326 A B C D p1' f s p2 g t p1) = (term263 A B C D p1 p1' f s p2 g t).
Proof. exact (eq_refl (term326 A B C D p1' f s p2 g t p1)). Qed.
Lemma lem4358828 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term327 A B C D p1 f s p2 g t) = (term264 A B C D p1 f s p2 g t).
Proof. exact (fun_ext (fun p1' : A => @lem4358827 A B C D p1' p1 f s p2 g t)). Qed.
Lemma lem4358829 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4358830 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term328 A B C D p1 f s p2 g t) = (term265 A B C D p1 f s p2 g t).
Proof. exact (MK_COMB (@lem4358829 A) (@lem4358828 A B C D p1 f s p2 g t)). Qed.
Lemma lem4358831 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4358832 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term329 A B C D p1 f s p2 g t) = (term266 A B C D p1 f s p2 g t).
Proof. exact (MK_COMB (@lem4358831) (@lem4358830 A B C D p1 f s p2 g t)). Qed.
Lemma lem4358833 {A B C D : Type'} (p1 : B) (f : A -> B) (p1' : A) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term330 A B C D p1 f s p2 g t p1') = (term318 A B C D p1 f p1' s p2 g t).
Proof. exact (eq_refl (term330 A B C D p1 f s p2 g t p1')). Qed.
Lemma lem4358834 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term331 A B C D p1 f s p2 g t) = (term319 A B C D p1 f s p2 g t).
Proof. exact (fun_ext (fun p1' : A => @lem4358833 A B C D p1 f p1' s p2 g t)). Qed.
Lemma lem4358835 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4358836 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term332 A B C D p1 f s p2 g t) = (term320 A B C D p1 f s p2 g t).
Proof. exact (MK_COMB (@lem4358835 A) (@lem4358834 A B C D p1 f s p2 g t)). Qed.
Lemma lem4358837 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term324 A B C D p1 f s p2 g t) = (term321 A B C D p1 f s p2 g t).
Proof. exact (MK_COMB (@lem4358832 A B C D p1 f s p2 g t) (@lem4358836 A B C D p1 f s p2 g t)). Qed.
Lemma lem4358838 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4358839 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term333 A B C D p1 f s p2 g t) = (term334 A B C D p1 f s p2 g t).
Proof. exact (MK_COMB (@lem4358838) (@lem4358837 A B C D p1 f s p2 g t)). Qed.
Lemma lem4358840 {A B C D : Type'} (p1 : A) (p1' : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term326 A B C D p1' f s p2 g t p1) = (term263 A B C D p1 p1' f s p2 g t).
Proof. exact (eq_refl (term326 A B C D p1' f s p2 g t p1)). Qed.
Lemma lem4358841 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4358842 {A B C D : Type'} (p1 : A) (p1' : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term335 A B C D p1' f s p2 g t p1) = (term336 A B C D p1 p1' f s p2 g t).
Proof. exact (MK_COMB (@lem4358841) (@lem4358840 A B C D p1 p1' f s p2 g t)). Qed.
Lemma lem4358843 {A B C D : Type'} (p1 : B) (f : A -> B) (p1' : A) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term330 A B C D p1 f s p2 g t p1') = (term318 A B C D p1 f p1' s p2 g t).
Proof. exact (eq_refl (term330 A B C D p1 f s p2 g t p1')). Qed.
Lemma lem4358844 {A B C D : Type'} (p1 : B) (f : A -> B) (p1' : A) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term337 A B C D p1 f s p2 g t p1') = (term338 A B C D p1 f p1' s p2 g t).
Proof. exact (MK_COMB (@lem4358842 A B C D p1' p1 f s p2 g t) (@lem4358843 A B C D p1 f p1' s p2 g t)). Qed.
Lemma lem4358845 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term339 A B C D p1 f s p2 g t) = (term340 A B C D p1 f s p2 g t).
Proof. exact (fun_ext (fun p1' : A => @lem4358844 A B C D p1 f p1' s p2 g t)). Qed.
Lemma lem4358846 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4358847 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term325 A B C D p1 f s p2 g t) = (term341 A B C D p1 f s p2 g t).
Proof. exact (MK_COMB (@lem4358846 A) (@lem4358845 A B C D p1 f s p2 g t)). Qed.
Lemma lem4358848 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : ((term324 A B C D p1 f s p2 g t) = (term325 A B C D p1 f s p2 g t)) = ((term321 A B C D p1 f s p2 g t) = (term341 A B C D p1 f s p2 g t)).
Proof. exact (MK_COMB (@lem4358839 A B C D p1 f s p2 g t) (@lem4358847 A B C D p1 f s p2 g t)). Qed.
Lemma lem4358849 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term321 A B C D p1 f s p2 g t) = (term341 A B C D p1 f s p2 g t).
Proof. exact (EQ_MP (@lem4358848 A B C D p1 f s p2 g t) (@lem4358826 A B C D p1 f s p2 g t)). Qed.
Lemma lem4358852 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term342 A B C D p1 f s p2 g t) = (term342 A B C D p1 f s p2 g t).
Proof. exact (eq_refl (term342 A B C D p1 f s p2 g t)). Qed.
Lemma lem4358853 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term342 A B C D p1 f s p2 g t) = ((term321 A B C D p1 f s p2 g t) = (term341 A B C D p1 f s p2 g t)).
Proof. exact (eq_refl (term342 A B C D p1 f s p2 g t)). Qed.
Lemma lem4358854 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term343 A B C D p1 f s p2 g t) = (term343 A B C D p1 f s p2 g t).
Proof. exact (eq_refl (term343 A B C D p1 f s p2 g t)). Qed.
Lemma lem4358855 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : ((term342 A B C D p1 f s p2 g t) = (term342 A B C D p1 f s p2 g t)) = ((term342 A B C D p1 f s p2 g t) = ((term321 A B C D p1 f s p2 g t) = (term341 A B C D p1 f s p2 g t))).
Proof. exact (MK_COMB (@lem4358854 A B C D p1 f s p2 g t) (@lem4358853 A B C D p1 f s p2 g t)). Qed.
Lemma lem4358856 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term342 A B C D p1 f s p2 g t) = ((term321 A B C D p1 f s p2 g t) = (term341 A B C D p1 f s p2 g t)).
Proof. exact (eq_refl (term342 A B C D p1 f s p2 g t)). Qed.
Lemma lem4358857 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4358858 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term343 A B C D p1 f s p2 g t) = (term344 A B C D p1 f s p2 g t).
Proof. exact (MK_COMB (@lem4358857) (@lem4358856 A B C D p1 f s p2 g t)). Qed.
Lemma lem4358859 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : ((term321 A B C D p1 f s p2 g t) = (term341 A B C D p1 f s p2 g t)) = ((term321 A B C D p1 f s p2 g t) = (term341 A B C D p1 f s p2 g t)).
Proof. exact (eq_refl ((term321 A B C D p1 f s p2 g t) = (term341 A B C D p1 f s p2 g t))). Qed.
Lemma lem4358860 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : ((term342 A B C D p1 f s p2 g t) = ((term321 A B C D p1 f s p2 g t) = (term341 A B C D p1 f s p2 g t))) = (((term321 A B C D p1 f s p2 g t) = (term341 A B C D p1 f s p2 g t)) = ((term321 A B C D p1 f s p2 g t) = (term341 A B C D p1 f s p2 g t))).
Proof. exact (MK_COMB (@lem4358858 A B C D p1 f s p2 g t) (@lem4358859 A B C D p1 f s p2 g t)). Qed.
Lemma lem4358861 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : ((term342 A B C D p1 f s p2 g t) = (term342 A B C D p1 f s p2 g t)) = (((term321 A B C D p1 f s p2 g t) = (term341 A B C D p1 f s p2 g t)) = ((term321 A B C D p1 f s p2 g t) = (term341 A B C D p1 f s p2 g t))).
Proof. exact (TRANS (@lem4358855 A B C D p1 f s p2 g t) (@lem4358860 A B C D p1 f s p2 g t)). Qed.
Lemma lem4358862 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : ((term321 A B C D p1 f s p2 g t) = (term341 A B C D p1 f s p2 g t)) = ((term321 A B C D p1 f s p2 g t) = (term341 A B C D p1 f s p2 g t)).
Proof. exact (EQ_MP (@lem4358861 A B C D p1 f s p2 g t) (@lem4358852 A B C D p1 f s p2 g t)). Qed.
Lemma lem4358863 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term321 A B C D p1 f s p2 g t) = (term341 A B C D p1 f s p2 g t).
Proof. exact (EQ_MP (@lem4358862 A B C D p1 f s p2 g t) (@lem4358849 A B C D p1 f s p2 g t)). Qed.
Lemma lem4358865 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term322 A P Q) = (term323 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4358866 {C : Type'} (P : C -> Prop) (Q : C -> Prop) : (term322 C P Q) = (term323 C P Q).
Proof. exact (@lem4358865 C P Q). Qed.
Lemma lem4358867 {A B C D : Type'} (p1 : B) (f : A -> B) (p1' : A) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term345 A B C D p1 f p1' s p2 g t) = (term346 A B C D p1 f p1' s p2 g t).
Proof. exact (@lem4358866 C (term262 A B C D p1' p1 f s p2 g t) (term317 A B C D p1 f p1' s p2 g t)). Qed.
Lemma lem4358868 {A B C D : Type'} (p1 : A) (p2 : C) (p1' : B) (f : A -> B) (s : A -> Prop) (p2' : D) (g : C -> D) (t : C -> Prop) : (term347 A B C D p1 p1' f s p2' g t p2) = (term260 A B C D p1 p2 p1' f s p2' g t).
Proof. exact (eq_refl (term347 A B C D p1 p1' f s p2' g t p2)). Qed.
Lemma lem4358869 {A B C D : Type'} (p1 : A) (p1' : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term348 A B C D p1 p1' f s p2 g t) = (term262 A B C D p1 p1' f s p2 g t).
Proof. exact (fun_ext (fun p2' : C => @lem4358868 A B C D p1 p2' p1' f s p2 g t)). Qed.
Lemma lem4358870 {C : Type'} : (@ex C) = (@ex C).
Proof. exact (eq_refl (@ex C)). Qed.
Lemma lem4358871 {A B C D : Type'} (p1 : A) (p1' : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term349 A B C D p1 p1' f s p2 g t) = (term263 A B C D p1 p1' f s p2 g t).
Proof. exact (MK_COMB (@lem4358870 C) (@lem4358869 A B C D p1 p1' f s p2 g t)). Qed.
Lemma lem4358872 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4358873 {A B C D : Type'} (p1 : A) (p1' : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term350 A B C D p1 p1' f s p2 g t) = (term336 A B C D p1 p1' f s p2 g t).
Proof. exact (MK_COMB (@lem4358872) (@lem4358871 A B C D p1 p1' f s p2 g t)). Qed.
Lemma lem4358874 {A B C D : Type'} (p1 : B) (f : A -> B) (p1' : A) (s : A -> Prop) (p2 : D) (g : C -> D) (p2' : C) (t : C -> Prop) : (term351 A B C D p1 f p1' s p2 g t p2') = (term315 A B C D p1 f p1' s p2 g p2' t).
Proof. exact (eq_refl (term351 A B C D p1 f p1' s p2 g t p2')). Qed.
Lemma lem4358875 {A B C D : Type'} (p1 : B) (f : A -> B) (p1' : A) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term352 A B C D p1 f p1' s p2 g t) = (term317 A B C D p1 f p1' s p2 g t).
Proof. exact (fun_ext (fun p2' : C => @lem4358874 A B C D p1 f p1' s p2 g p2' t)). Qed.
Lemma lem4358876 {C : Type'} : (@ex C) = (@ex C).
Proof. exact (eq_refl (@ex C)). Qed.
Lemma lem4358877 {A B C D : Type'} (p1 : B) (f : A -> B) (p1' : A) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term353 A B C D p1 f p1' s p2 g t) = (term318 A B C D p1 f p1' s p2 g t).
Proof. exact (MK_COMB (@lem4358876 C) (@lem4358875 A B C D p1 f p1' s p2 g t)). Qed.
Lemma lem4358878 {A B C D : Type'} (p1 : B) (f : A -> B) (p1' : A) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term345 A B C D p1 f p1' s p2 g t) = (term338 A B C D p1 f p1' s p2 g t).
Proof. exact (MK_COMB (@lem4358873 A B C D p1' p1 f s p2 g t) (@lem4358877 A B C D p1 f p1' s p2 g t)). Qed.
Lemma lem4358879 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4358880 {A B C D : Type'} (p1 : B) (f : A -> B) (p1' : A) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term354 A B C D p1 f p1' s p2 g t) = (term355 A B C D p1 f p1' s p2 g t).
Proof. exact (MK_COMB (@lem4358879) (@lem4358878 A B C D p1 f p1' s p2 g t)). Qed.
Lemma lem4358881 {A B C D : Type'} (p1 : A) (p2 : C) (p1' : B) (f : A -> B) (s : A -> Prop) (p2' : D) (g : C -> D) (t : C -> Prop) : (term347 A B C D p1 p1' f s p2' g t p2) = (term260 A B C D p1 p2 p1' f s p2' g t).
Proof. exact (eq_refl (term347 A B C D p1 p1' f s p2' g t p2)). Qed.
Lemma lem4358882 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4358883 {A B C D : Type'} (p1 : A) (p2 : C) (p1' : B) (f : A -> B) (s : A -> Prop) (p2' : D) (g : C -> D) (t : C -> Prop) : (term356 A B C D p1 p1' f s p2' g t p2) = (term357 A B C D p1 p2 p1' f s p2' g t).
Proof. exact (MK_COMB (@lem4358882) (@lem4358881 A B C D p1 p2 p1' f s p2' g t)). Qed.
Lemma lem4358884 {A B C D : Type'} (p1 : B) (f : A -> B) (p1' : A) (s : A -> Prop) (p2 : D) (g : C -> D) (p2' : C) (t : C -> Prop) : (term351 A B C D p1 f p1' s p2 g t p2') = (term315 A B C D p1 f p1' s p2 g p2' t).
Proof. exact (eq_refl (term351 A B C D p1 f p1' s p2 g t p2')). Qed.
Lemma lem4358885 {A B C D : Type'} (p1 : B) (f : A -> B) (p1' : A) (s : A -> Prop) (p2 : D) (g : C -> D) (p2' : C) (t : C -> Prop) : (term358 A B C D p1 f p1' s p2 g t p2') = (term359 A B C D p1 f p1' s p2 g p2' t).
Proof. exact (MK_COMB (@lem4358883 A B C D p1' p2' p1 f s p2 g t) (@lem4358884 A B C D p1 f p1' s p2 g p2' t)). Qed.
Lemma lem4358886 {A B C D : Type'} (p1 : B) (f : A -> B) (p1' : A) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term360 A B C D p1 f p1' s p2 g t) = (term361 A B C D p1 f p1' s p2 g t).
Proof. exact (fun_ext (fun p2' : C => @lem4358885 A B C D p1 f p1' s p2 g p2' t)). Qed.
Lemma lem4358887 {C : Type'} : (@ex C) = (@ex C).
Proof. exact (eq_refl (@ex C)). Qed.
Lemma lem4358888 {A B C D : Type'} (p1 : B) (f : A -> B) (p1' : A) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term346 A B C D p1 f p1' s p2 g t) = (term362 A B C D p1 f p1' s p2 g t).
Proof. exact (MK_COMB (@lem4358887 C) (@lem4358886 A B C D p1 f p1' s p2 g t)). Qed.
Lemma lem4358889 {A B C D : Type'} (p1 : B) (f : A -> B) (p1' : A) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : ((term345 A B C D p1 f p1' s p2 g t) = (term346 A B C D p1 f p1' s p2 g t)) = ((term338 A B C D p1 f p1' s p2 g t) = (term362 A B C D p1 f p1' s p2 g t)).
Proof. exact (MK_COMB (@lem4358880 A B C D p1 f p1' s p2 g t) (@lem4358888 A B C D p1 f p1' s p2 g t)). Qed.
Lemma lem4358890 {A B C D : Type'} (p1 : B) (f : A -> B) (p1' : A) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term338 A B C D p1 f p1' s p2 g t) = (term362 A B C D p1 f p1' s p2 g t).
Proof. exact (EQ_MP (@lem4358889 A B C D p1 f p1' s p2 g t) (@lem4358867 A B C D p1 f p1' s p2 g t)). Qed.
Lemma lem4358893 {A B C D : Type'} (p1 : B) (f : A -> B) (p1' : A) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term363 A B C D p1 f p1' s p2 g t) = (term363 A B C D p1 f p1' s p2 g t).
Proof. exact (eq_refl (term363 A B C D p1 f p1' s p2 g t)). Qed.
Lemma lem4358894 {A B C D : Type'} (p1 : B) (f : A -> B) (p1' : A) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term363 A B C D p1 f p1' s p2 g t) = ((term338 A B C D p1 f p1' s p2 g t) = (term362 A B C D p1 f p1' s p2 g t)).
Proof. exact (eq_refl (term363 A B C D p1 f p1' s p2 g t)). Qed.
Lemma lem4358895 {A B C D : Type'} (p1 : B) (f : A -> B) (p1' : A) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term364 A B C D p1 f p1' s p2 g t) = (term364 A B C D p1 f p1' s p2 g t).
Proof. exact (eq_refl (term364 A B C D p1 f p1' s p2 g t)). Qed.
Lemma lem4358896 {A B C D : Type'} (p1 : B) (f : A -> B) (p1' : A) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : ((term363 A B C D p1 f p1' s p2 g t) = (term363 A B C D p1 f p1' s p2 g t)) = ((term363 A B C D p1 f p1' s p2 g t) = ((term338 A B C D p1 f p1' s p2 g t) = (term362 A B C D p1 f p1' s p2 g t))).
Proof. exact (MK_COMB (@lem4358895 A B C D p1 f p1' s p2 g t) (@lem4358894 A B C D p1 f p1' s p2 g t)). Qed.
Lemma lem4358897 {A B C D : Type'} (p1 : B) (f : A -> B) (p1' : A) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term363 A B C D p1 f p1' s p2 g t) = ((term338 A B C D p1 f p1' s p2 g t) = (term362 A B C D p1 f p1' s p2 g t)).
Proof. exact (eq_refl (term363 A B C D p1 f p1' s p2 g t)). Qed.
Lemma lem4358898 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4358899 {A B C D : Type'} (p1 : B) (f : A -> B) (p1' : A) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term364 A B C D p1 f p1' s p2 g t) = (term365 A B C D p1 f p1' s p2 g t).
Proof. exact (MK_COMB (@lem4358898) (@lem4358897 A B C D p1 f p1' s p2 g t)). Qed.
Lemma lem4358900 {A B C D : Type'} (p1 : B) (f : A -> B) (p1' : A) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : ((term338 A B C D p1 f p1' s p2 g t) = (term362 A B C D p1 f p1' s p2 g t)) = ((term338 A B C D p1 f p1' s p2 g t) = (term362 A B C D p1 f p1' s p2 g t)).
Proof. exact (eq_refl ((term338 A B C D p1 f p1' s p2 g t) = (term362 A B C D p1 f p1' s p2 g t))). Qed.
Lemma lem4358901 {A B C D : Type'} (p1 : B) (f : A -> B) (p1' : A) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : ((term363 A B C D p1 f p1' s p2 g t) = ((term338 A B C D p1 f p1' s p2 g t) = (term362 A B C D p1 f p1' s p2 g t))) = (((term338 A B C D p1 f p1' s p2 g t) = (term362 A B C D p1 f p1' s p2 g t)) = ((term338 A B C D p1 f p1' s p2 g t) = (term362 A B C D p1 f p1' s p2 g t))).
Proof. exact (MK_COMB (@lem4358899 A B C D p1 f p1' s p2 g t) (@lem4358900 A B C D p1 f p1' s p2 g t)). Qed.
Lemma lem4358902 {A B C D : Type'} (p1 : B) (f : A -> B) (p1' : A) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : ((term363 A B C D p1 f p1' s p2 g t) = (term363 A B C D p1 f p1' s p2 g t)) = (((term338 A B C D p1 f p1' s p2 g t) = (term362 A B C D p1 f p1' s p2 g t)) = ((term338 A B C D p1 f p1' s p2 g t) = (term362 A B C D p1 f p1' s p2 g t))).
Proof. exact (TRANS (@lem4358896 A B C D p1 f p1' s p2 g t) (@lem4358901 A B C D p1 f p1' s p2 g t)). Qed.
Lemma lem4358903 {A B C D : Type'} (p1 : B) (f : A -> B) (p1' : A) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : ((term338 A B C D p1 f p1' s p2 g t) = (term362 A B C D p1 f p1' s p2 g t)) = ((term338 A B C D p1 f p1' s p2 g t) = (term362 A B C D p1 f p1' s p2 g t)).
Proof. exact (EQ_MP (@lem4358902 A B C D p1 f p1' s p2 g t) (@lem4358893 A B C D p1 f p1' s p2 g t)). Qed.
Lemma lem4358904 {A B C D : Type'} (p1 : B) (f : A -> B) (p1' : A) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term338 A B C D p1 f p1' s p2 g t) = (term362 A B C D p1 f p1' s p2 g t).
Proof. exact (EQ_MP (@lem4358903 A B C D p1 f p1' s p2 g t) (@lem4358890 A B C D p1 f p1' s p2 g t)). Qed.
Lemma lem4358905 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term340 A B C D p1 f s p2 g t) = (term366 A B C D p1 f s p2 g t).
Proof. exact (fun_ext (fun p1' : A => @lem4358904 A B C D p1 f p1' s p2 g t)). Qed.
Lemma lem4358906 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4358907 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term341 A B C D p1 f s p2 g t) = (term367 A B C D p1 f s p2 g t).
Proof. exact (MK_COMB (@lem4358906 A) (@lem4358905 A B C D p1 f s p2 g t)). Qed.
Lemma lem4358908 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term321 A B C D p1 f s p2 g t) = (term367 A B C D p1 f s p2 g t).
Proof. exact (TRANS (@lem4358863 A B C D p1 f s p2 g t) (@lem4358907 A B C D p1 f s p2 g t)). Qed.
Lemma lem4358910 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term233 A B C D p1 f s p2 g t) = (term367 A B C D p1 f s p2 g t).
Proof. exact (TRANS (@lem4358822 A B C D p1 f s p2 g t) (@lem4358908 A B C D p1 f s p2 g t)). Qed.
Lemma lem4358911 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term183 A B C D p1 f s p2 g t) = (term367 A B C D p1 f s p2 g t).
Proof. exact (TRANS (@lem4358375 A B C D p1 f s p2 g t) (@lem4358910 A B C D p1 f s p2 g t)). Qed.
Lemma lem4358912 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) (h1 : term183 A B C D p1 f s p2 g t) : term367 A B C D p1 f s p2 g t.
Proof. exact (EQ_MP (@lem4358911 A B C D p1 f s p2 g t) (@lem4358248 A B C D p1 f s p2 g t h1)). Qed.
Lemma lem4358913 {A B C D : Type'} (p1 : B) (f : A -> B) (p1' : A) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) (h1 : term362 A B C D p1 f p1' s p2 g t) : term362 A B C D p1 f p1' s p2 g t.
Proof. exact (h1). Qed.
Lemma lem4358914 {A B C D : Type'} (p1 : B) (f : A -> B) (p1' : A) (s : A -> Prop) (p2 : D) (g : C -> D) (p2' : C) (t : C -> Prop) (h1 : term359 A B C D p1 f p1' s p2 g p2' t) : term359 A B C D p1 f p1' s p2 g p2' t.
Proof. exact (h1). Qed.
Lemma lem4358947 {A B C D : Type'} (p1 : B) (f : A -> B) (p1' : A) (s : A -> Prop) (p2 : D) (g : C -> D) (p2' : C) (t : C -> Prop) : (term288 A B C D p1 f p1' s p2 g p2' t) = (term288 A B C D p1 f p1' s p2 g p2' t).
Proof. exact (eq_refl (term288 A B C D p1 f p1' s p2 g p2' t)). Qed.
Lemma lem4358988 {A B C D : Type'} (p1 : B) (f : A -> B) (p2 : D) (g : C -> D) (p1' : A) (s : A -> Prop) (p2' : C) (t : C -> Prop) : (term191 A B C D p1 f p2 g p1' s p2' t) = (term191 A B C D p1 f p2 g p1' s p2' t).
Proof. exact (eq_refl (term191 A B C D p1 f p2 g p1' s p2' t)). Qed.
Lemma lem4358989 {A B C D : Type'} (p1 : B) (f : A -> B) (p2 : D) (g : C -> D) (p1' : A) (s : A -> Prop) (t : C -> Prop) : (term200 A B C D p1 f p2 g p1' s t) = (term200 A B C D p1 f p2 g p1' s t).
Proof. exact (fun_ext (fun p2' : C => @lem4358988 A B C D p1 f p2 g p1' s p2' t)). Qed.
Lemma lem4358990 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem4358991 {A B C D : Type'} (p1 : B) (f : A -> B) (p2 : D) (g : C -> D) (p1' : A) (s : A -> Prop) (t : C -> Prop) : (term201 A B C D p1 f p2 g p1' s t) = (term201 A B C D p1 f p2 g p1' s t).
Proof. exact (MK_COMB (@lem4358990 C) (@lem4358989 A B C D p1 f p2 g p1' s t)). Qed.
Lemma lem4358992 {A B C D : Type'} (p1 : B) (f : A -> B) (p2 : D) (g : C -> D) (s : A -> Prop) (t : C -> Prop) : (term207 A B C D p1 f p2 g s t) = (term207 A B C D p1 f p2 g s t).
Proof. exact (fun_ext (fun p1' : A => @lem4358991 A B C D p1 f p2 g p1' s t)). Qed.
Lemma lem4358993 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4358994 {A B C D : Type'} (p1 : B) (f : A -> B) (p2 : D) (g : C -> D) (s : A -> Prop) (t : C -> Prop) : (term208 A B C D p1 f p2 g s t) = (term208 A B C D p1 f p2 g s t).
Proof. exact (MK_COMB (@lem4358993 A) (@lem4358992 A B C D p1 f p2 g s t)). Qed.
Lemma lem4358995 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4358996 {A B C D : Type'} (p1 : B) (f : A -> B) (p2 : D) (g : C -> D) (s : A -> Prop) (t : C -> Prop) : (term224 A B C D p1 f p2 g s t) = (term224 A B C D p1 f p2 g s t).
Proof. exact (MK_COMB (@lem4358995) (@lem4358994 A B C D p1 f p2 g s t)). Qed.
Lemma lem4358997 {A B C D : Type'} (p1 : B) (f : A -> B) (p1' : A) (s : A -> Prop) (p2 : D) (g : C -> D) (p2' : C) (t : C -> Prop) : (term315 A B C D p1 f p1' s p2 g p2' t) = (term315 A B C D p1 f p1' s p2 g p2' t).
Proof. exact (MK_COMB (@lem4358996 A B C D p1 f p2 g s t) (@lem4358947 A B C D p1 f p1' s p2 g p2' t)). Qed.
Lemma lem4359016 {C D : Type'} (p2 : D) (g : C -> D) (x : C) (t : C -> Prop) : (term210 C D p2 g x t) = (term210 C D p2 g x t).
Proof. exact (eq_refl (term210 C D p2 g x t)). Qed.
Lemma lem4359017 {C D : Type'} (p2 : D) (g : C -> D) (t : C -> Prop) : (term216 C D p2 g t) = (term216 C D p2 g t).
Proof. exact (fun_ext (fun x : C => @lem4359016 C D p2 g x t)). Qed.
Lemma lem4359018 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem4359019 {C D : Type'} (p2 : D) (g : C -> D) (t : C -> Prop) : (term217 C D p2 g t) = (term217 C D p2 g t).
Proof. exact (MK_COMB (@lem4359018 C) (@lem4359017 C D p2 g t)). Qed.
Lemma lem4359038 {A B : Type'} (p1 : B) (f : A -> B) (x : A) (s : A -> Prop) : (term210 A B p1 f x s) = (term210 A B p1 f x s).
Proof. exact (eq_refl (term210 A B p1 f x s)). Qed.
Lemma lem4359039 {A B : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) : (term216 A B p1 f s) = (term216 A B p1 f s).
Proof. exact (fun_ext (fun x : A => @lem4359038 A B p1 f x s)). Qed.
Lemma lem4359040 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4359041 {A B : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) : (term217 A B p1 f s) = (term217 A B p1 f s).
Proof. exact (MK_COMB (@lem4359040 A) (@lem4359039 A B p1 f s)). Qed.
Lemma lem4359042 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4359043 {A B : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) : (term219 A B p1 f s) = (term219 A B p1 f s).
Proof. exact (MK_COMB (@lem4359042) (@lem4359041 A B p1 f s)). Qed.
Lemma lem4359044 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term221 A B C D p1 f s p2 g t) = (term221 A B C D p1 f s p2 g t).
Proof. exact (MK_COMB (@lem4359043 A B p1 f s) (@lem4359019 C D p2 g t)). Qed.
Lemma lem4359079 {A B C D : Type'} (p1 : B) (f : A -> B) (p2 : D) (g : C -> D) (p1' : A) (s : A -> Prop) (p2' : C) (t : C -> Prop) : (term258 A B C D p1 f p2 g p1' s p2' t) = (term258 A B C D p1 f p2 g p1' s p2' t).
Proof. exact (eq_refl (term258 A B C D p1 f p2 g p1' s p2' t)). Qed.
Lemma lem4359080 {A B C D : Type'} (p1' : A) (p2' : C) (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term260 A B C D p1' p2' p1 f s p2 g t) = (term260 A B C D p1' p2' p1 f s p2 g t).
Proof. exact (MK_COMB (@lem4359079 A B C D p1 f p2 g p1' s p2' t) (@lem4359044 A B C D p1 f s p2 g t)). Qed.
Lemma lem4359081 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4359082 {A B C D : Type'} (p1' : A) (p2' : C) (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term357 A B C D p1' p2' p1 f s p2 g t) = (term357 A B C D p1' p2' p1 f s p2 g t).
Proof. exact (MK_COMB (@lem4359081) (@lem4359080 A B C D p1' p2' p1 f s p2 g t)). Qed.
Lemma lem4359083 {A B C D : Type'} (p1 : B) (f : A -> B) (p1' : A) (s : A -> Prop) (p2 : D) (g : C -> D) (p2' : C) (t : C -> Prop) : (term359 A B C D p1 f p1' s p2 g p2' t) = (term359 A B C D p1 f p1' s p2 g p2' t).
Proof. exact (MK_COMB (@lem4359082 A B C D p1' p2' p1 f s p2 g t) (@lem4358997 A B C D p1 f p1' s p2 g p2' t)). Qed.
Lemma lem4359084 {A B C D : Type'} (p1 : B) (f : A -> B) (p1' : A) (s : A -> Prop) (p2 : D) (g : C -> D) (p2' : C) (t : C -> Prop) (h1 : term359 A B C D p1 f p1' s p2 g p2' t) : term359 A B C D p1 f p1' s p2 g p2' t.
Proof. exact (EQ_MP (@lem4359083 A B C D p1 f p1' s p2 g p2' t) (@lem4358914 A B C D p1 f p1' s p2 g p2' t h1)). Qed.
Lemma lem4359085 {A B C D : Type'} (p1' : A) (p2' : C) (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) (h1 : term260 A B C D p1' p2' p1 f s p2 g t) : term260 A B C D p1' p2' p1 f s p2 g t.
Proof. exact (h1). Qed.
Lemma lem4359086 {A B C D : Type'} (p1 : B) (f : A -> B) (p1' : A) (s : A -> Prop) (p2 : D) (g : C -> D) (p2' : C) (t : C -> Prop) (h1 : term315 A B C D p1 f p1' s p2 g p2' t) : term315 A B C D p1 f p1' s p2 g p2' t.
Proof. exact (h1). Qed.
Lemma lem4359087 {A B C D : Type'} (p1' : A) (p2' : C) (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) (h1 : term260 A B C D p1' p2' p1 f s p2 g t) : term221 A B C D p1 f s p2 g t.
Proof. exact (proj2 (@lem4359085 A B C D p1' p2' p1 f s p2 g t h1)). Qed.
Lemma lem4359088 {A B C D : Type'} (p1' : A) (p2' : C) (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) (h1 : term260 A B C D p1' p2' p1 f s p2 g t) : term141 A B C D p1 f p2 g p1' s p2' t.
Proof. exact (proj1 (@lem4359085 A B C D p1' p2' p1 f s p2 g t h1)). Qed.
Lemma lem4359089 {A B C D : Type'} (p1' : A) (p2' : C) (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) (h1 : term260 A B C D p1' p2' p1 f s p2 g t) : term26 A C p1' s p2' t.
Proof. exact (proj2 (@lem4359088 A B C D p1' p2' p1 f s p2 g t h1)). Qed.
Lemma lem4359090 {A B C D : Type'} (p1' : A) (p2' : C) (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) (h1 : term260 A B C D p1' p2' p1 f s p2 g t) : term138 A B C D p1 f p1' p2 g p2'.
Proof. exact (proj1 (@lem4359088 A B C D p1' p2' p1 f s p2 g t h1)). Qed.
Lemma lem4359095 {A B : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (h1 : term217 A B p1 f s) : term217 A B p1 f s.
Proof. exact (h1). Qed.
Lemma lem4359096 {C D : Type'} (p2 : D) (g : C -> D) (t : C -> Prop) (h1 : term217 C D p2 g t) : term217 C D p2 g t.
Proof. exact (h1). Qed.
Lemma lem4359097 {A B C D : Type'} (p1 : B) (f : A -> B) (p1' : A) (s : A -> Prop) (p2 : D) (g : C -> D) (p2' : C) (t : C -> Prop) (h1 : term315 A B C D p1 f p1' s p2 g p2' t) : term288 A B C D p1 f p1' s p2 g p2' t.
Proof. exact (proj2 (@lem4359086 A B C D p1 f p1' s p2 g p2' t h1)). Qed.
Lemma lem4359098 {A B C D : Type'} (p1 : B) (f : A -> B) (p1' : A) (s : A -> Prop) (p2 : D) (g : C -> D) (p2' : C) (t : C -> Prop) (h1 : term315 A B C D p1 f p1' s p2 g p2' t) : term208 A B C D p1 f p2 g s t.
Proof. exact (proj1 (@lem4359086 A B C D p1 f p1' s p2 g p2' t h1)). Qed.
Lemma lem4359099 {A B C D : Type'} (p1 : B) (f : A -> B) (p1' : A) (s : A -> Prop) (p2 : D) (g : C -> D) (p2' : C) (t : C -> Prop) (h1 : term315 A B C D p1 f p1' s p2 g p2' t) : term180 C D p2 g p2' t.
Proof. exact (proj2 (@lem4359097 A B C D p1 f p1' s p2 g p2' t h1)). Qed.
Lemma lem4359100 {A B C D : Type'} (p1 : B) (f : A -> B) (p1' : A) (s : A -> Prop) (p2 : D) (g : C -> D) (p2' : C) (t : C -> Prop) (h1 : term315 A B C D p1 f p1' s p2 g p2' t) : term180 A B p1 f p1' s.
Proof. exact (proj1 (@lem4359097 A B C D p1 f p1' s p2 g p2' t h1)). Qed.
Lemma lem4359128 {A B : Type'} (p1 : B) (f : A -> B) (x : A) (s : A -> Prop) : (term210 A B p1 f x s) = (term210 A B p1 f x s).
Proof. exact (eq_refl (term210 A B p1 f x s)). Qed.
Lemma lem4359129 {A B : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) : (term216 A B p1 f s) = (term216 A B p1 f s).
Proof. exact (fun_ext (fun x : A => @lem4359128 A B p1 f x s)). Qed.
Lemma lem4359130 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4359132 {A B : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) : (term217 A B p1 f s) = (term217 A B p1 f s).
Proof. exact (MK_COMB (@lem4359130 A) (@lem4359129 A B p1 f s)). Qed.
Lemma lem4359133 {A B : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (h1 : term217 A B p1 f s) : term217 A B p1 f s.
Proof. exact (EQ_MP (@lem4359132 A B p1 f s) (@lem4359095 A B p1 f s h1)). Qed.
Lemma lem4359157 {C D : Type'} (p2 : D) (g : C -> D) (x : C) (t : C -> Prop) : (term210 C D p2 g x t) = (term210 C D p2 g x t).
Proof. exact (eq_refl (term210 C D p2 g x t)). Qed.
Lemma lem4359158 {C D : Type'} (p2 : D) (g : C -> D) (t : C -> Prop) : (term216 C D p2 g t) = (term216 C D p2 g t).
Proof. exact (fun_ext (fun x : C => @lem4359157 C D p2 g x t)). Qed.
Lemma lem4359159 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem4359161 {C D : Type'} (p2 : D) (g : C -> D) (t : C -> Prop) : (term217 C D p2 g t) = (term217 C D p2 g t).
Proof. exact (MK_COMB (@lem4359159 C) (@lem4359158 C D p2 g t)). Qed.
Lemma lem4359162 {C D : Type'} (p2 : D) (g : C -> D) (t : C -> Prop) (h1 : term217 C D p2 g t) : term217 C D p2 g t.
Proof. exact (EQ_MP (@lem4359161 C D p2 g t) (@lem4359096 C D p2 g t h1)). Qed.
Lemma lem4359182 {A B C D : Type'} (p1 : B) (f : A -> B) (p2 : D) (g : C -> D) (p1' : A) (s : A -> Prop) (p2' : C) (t : C -> Prop) : (term191 A B C D p1 f p2 g p1' s p2' t) = (term191 A B C D p1 f p2 g p1' s p2' t).
Proof. exact (eq_refl (term191 A B C D p1 f p2 g p1' s p2' t)). Qed.
Lemma lem4359183 {A B C D : Type'} (p1 : B) (f : A -> B) (p2 : D) (g : C -> D) (p1' : A) (s : A -> Prop) (t : C -> Prop) : (term200 A B C D p1 f p2 g p1' s t) = (term200 A B C D p1 f p2 g p1' s t).
Proof. exact (fun_ext (fun p2' : C => @lem4359182 A B C D p1 f p2 g p1' s p2' t)). Qed.
Lemma lem4359184 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem4359185 {A B C D : Type'} (p1 : B) (f : A -> B) (p2 : D) (g : C -> D) (p1' : A) (s : A -> Prop) (t : C -> Prop) : (term201 A B C D p1 f p2 g p1' s t) = (term201 A B C D p1 f p2 g p1' s t).
Proof. exact (MK_COMB (@lem4359184 C) (@lem4359183 A B C D p1 f p2 g p1' s t)). Qed.
Lemma lem4359186 {A B C D : Type'} (p1 : B) (f : A -> B) (p2 : D) (g : C -> D) (s : A -> Prop) (t : C -> Prop) : (term207 A B C D p1 f p2 g s t) = (term207 A B C D p1 f p2 g s t).
Proof. exact (fun_ext (fun p1' : A => @lem4359185 A B C D p1 f p2 g p1' s t)). Qed.
Lemma lem4359187 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4359189 {A B C D : Type'} (p1 : B) (f : A -> B) (p2 : D) (g : C -> D) (s : A -> Prop) (t : C -> Prop) : (term208 A B C D p1 f p2 g s t) = (term208 A B C D p1 f p2 g s t).
Proof. exact (MK_COMB (@lem4359187 A) (@lem4359186 A B C D p1 f p2 g s t)). Qed.
Lemma lem4359190 {A B C D : Type'} (p1 : B) (f : A -> B) (p1' : A) (s : A -> Prop) (p2 : D) (g : C -> D) (p2' : C) (t : C -> Prop) (h1 : term315 A B C D p1 f p1' s p2 g p2' t) : term208 A B C D p1 f p2 g s t.
Proof. exact (EQ_MP (@lem4359189 A B C D p1 f p2 g s t) (@lem4359098 A B C D p1 f p1' s p2 g p2' t h1)). Qed.
Lemma lem4359207 {A B : Type'} (_49850 : A) (p1 : B) (f : A -> B) (s : A -> Prop) (h1 : term217 A B p1 f s) : term368 A B p1 f s _49850.
Proof. exact (@lem4359133 A B p1 f s h1 _49850). Qed.
Lemma lem4359208 {A B : Type'} (p1 : B) (f : A -> B) (_49850 : A) (s : A -> Prop) : (term368 A B p1 f s _49850) = (term210 A B p1 f _49850 s).
Proof. exact (eq_refl (term368 A B p1 f s _49850)). Qed.
Lemma lem4359210 {C D : Type'} (_49851 : C) (p2 : D) (g : C -> D) (t : C -> Prop) (h1 : term217 C D p2 g t) : term368 C D p2 g t _49851.
Proof. exact (@lem4359162 C D p2 g t h1 _49851). Qed.
Lemma lem4359211 {C D : Type'} (p2 : D) (g : C -> D) (_49851 : C) (t : C -> Prop) : (term368 C D p2 g t _49851) = (term210 C D p2 g _49851 t).
Proof. exact (eq_refl (term368 C D p2 g t _49851)). Qed.
Lemma lem4359213 {A B C D : Type'} (_49852 : A) (p1 : B) (f : A -> B) (p1' : A) (s : A -> Prop) (p2 : D) (g : C -> D) (p2' : C) (t : C -> Prop) (h1 : term315 A B C D p1 f p1' s p2 g p2' t) : term369 A B C D p1 f p2 g s t _49852.
Proof. exact (@lem4359190 A B C D p1 f p1' s p2 g p2' t h1 _49852). Qed.
Lemma lem4359214 {A B C D : Type'} (p1 : B) (f : A -> B) (p2 : D) (g : C -> D) (_49852 : A) (s : A -> Prop) (t : C -> Prop) : (term369 A B C D p1 f p2 g s t _49852) = (term201 A B C D p1 f p2 g _49852 s t).
Proof. exact (eq_refl (term369 A B C D p1 f p2 g s t _49852)). Qed.
Lemma lem4359215 {A B C D : Type'} (_49852 : A) (p1 : B) (f : A -> B) (p1' : A) (s : A -> Prop) (p2 : D) (g : C -> D) (p2' : C) (t : C -> Prop) (h1 : term315 A B C D p1 f p1' s p2 g p2' t) : term201 A B C D p1 f p2 g _49852 s t.
Proof. exact (EQ_MP (@lem4359214 A B C D p1 f p2 g _49852 s t) (@lem4359213 A B C D _49852 p1 f p1' s p2 g p2' t h1)). Qed.
Lemma lem4359216 {A B C D : Type'} (_49852 : A) (_49853 : C) (p1 : B) (f : A -> B) (p1' : A) (s : A -> Prop) (p2 : D) (g : C -> D) (p2' : C) (t : C -> Prop) (h1 : term315 A B C D p1 f p1' s p2 g p2' t) : term370 A B C D p1 f p2 g _49852 s t _49853.
Proof. exact (@lem4359215 A B C D _49852 p1 f p1' s p2 g p2' t h1 _49853). Qed.
Lemma lem4359217 {A B C D : Type'} (p1 : B) (f : A -> B) (p2 : D) (g : C -> D) (_49852 : A) (s : A -> Prop) (_49853 : C) (t : C -> Prop) : (term370 A B C D p1 f p2 g _49852 s t _49853) = (term191 A B C D p1 f p2 g _49852 s _49853 t).
Proof. exact (eq_refl (term370 A B C D p1 f p2 g _49852 s t _49853)). Qed.
Lemma lem4359218 {A B C D : Type'} (_49852 : A) (_49853 : C) (p1 : B) (f : A -> B) (p1' : A) (s : A -> Prop) (p2 : D) (g : C -> D) (p2' : C) (t : C -> Prop) (h1 : term315 A B C D p1 f p1' s p2 g p2' t) : term191 A B C D p1 f p2 g _49852 s _49853 t.
Proof. exact (EQ_MP (@lem4359217 A B C D p1 f p2 g _49852 s _49853 t) (@lem4359216 A B C D _49852 _49853 p1 f p1' s p2 g p2' t h1)). Qed.
Lemma lem4359240 {A B C D : Type'} (p1' : A) (p2' : C) (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) (h1 : term260 A B C D p1' p2' p1 f s p2 g t) : p2 = (g p2').
Proof. exact (proj2 (@lem4359090 A B C D p1' p2' p1 f s p2 g t h1)). Qed.
Lemma lem4359246 {C D : Type'} (_49851 : C) (p2 : D) (g : C -> D) (t : C -> Prop) (h1 : term217 C D p2 g t) : term210 C D p2 g _49851 t.
Proof. exact (EQ_MP (@lem4359211 C D p2 g _49851 t) (@lem4359210 C D _49851 p2 g t h1)). Qed.
Lemma lem4359261 {A B C D : Type'} (p1 : B) (f : A -> B) (p2 : D) (g : C -> D) (_49852 : A) (s : A -> Prop) (_49853 : C) (t : C -> Prop) : (term191 A B C D p1 f p2 g _49852 s _49853 t) = (term371 A B C D p1 f p2 g _49852 s _49853 t).
Proof. exact (@lem4357478 (term372 A B p1 f _49852) (term372 C D p2 g _49853) (term187 A C _49852 s _49853 t)). Qed.
Lemma lem4359262 {A B C D : Type'} (_49852 : A) (_49853 : C) (p1 : B) (f : A -> B) (p1' : A) (s : A -> Prop) (p2 : D) (g : C -> D) (p2' : C) (t : C -> Prop) (h1 : term315 A B C D p1 f p1' s p2 g p2' t) : term371 A B C D p1 f p2 g _49852 s _49853 t.
Proof. exact (EQ_MP (@lem4359261 A B C D p1 f p2 g _49852 s _49853 t) (@lem4359218 A B C D _49852 _49853 p1 f p1' s p2 g p2' t h1)). Qed.
Lemma lem4359268 {A B C D : Type'} (p1 : B) (f : A -> B) (p1' : A) (s : A -> Prop) (p2 : D) (g : C -> D) (p2' : C) (t : C -> Prop) (h1 : term315 A B C D p1 f p1' s p2 g p2' t) : p1 = (f p1').
Proof. exact (proj1 (@lem4359100 A B C D p1 f p1' s p2 g p2' t h1)). Qed.
Lemma lem4359326 {A B C D : Type'} (p1' : A) (p2' : C) (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) (h1 : term260 A B C D p1' p2' p1 f s p2 g t) : p1 = (f p1').
Proof. exact (proj1 (@lem4359090 A B C D p1' p2' p1 f s p2 g t h1)). Qed.
Lemma lem4359340 {A B : Type'} (_49850 : A) (p1 : B) (f : A -> B) (s : A -> Prop) (h1 : term217 A B p1 f s) : term210 A B p1 f _49850 s.
Proof. exact (EQ_MP (@lem4359208 A B p1 f _49850 s) (@lem4359207 A B _49850 p1 f s h1)). Qed.
Lemma lem4359383 {A B : Type'} (f : A -> B) (_49850 : A) (s : A -> Prop) : (term373 A B f _49850 s) = (term373 A B f _49850 s).
Proof. exact (eq_refl (term373 A B f _49850 s)). Qed.
Lemma lem4359384 {A B C D : Type'} (_49850 : A) (p1' : A) (p2' : C) (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) (h1 : term260 A B C D p1' p2' p1 f s p2 g t) : (term374 A B f _49850 s p1) = (term375 A B _49850 s f p1').
Proof. exact (MK_COMB (@lem4359383 A B f _49850 s) (@lem4359326 A B C D p1' p2' p1 f s p2 g t h1)). Qed.
Lemma lem4359385 {A B : Type'} (p1' : A) (f : A -> B) (_49850 : A) (s : A -> Prop) : (term375 A B _49850 s f p1') = (term376 A B p1' f _49850 s).
Proof. exact (eq_refl (term375 A B _49850 s f p1')). Qed.
Lemma lem4359386 {A B : Type'} (f : A -> B) (_49850 : A) (s : A -> Prop) (p1 : B) : (term377 A B f _49850 s p1) = (term377 A B f _49850 s p1).
Proof. exact (eq_refl (term377 A B f _49850 s p1)). Qed.
Lemma lem4359387 {A B : Type'} (p1 : B) (p1' : A) (f : A -> B) (_49850 : A) (s : A -> Prop) : ((term374 A B f _49850 s p1) = (term375 A B _49850 s f p1')) = ((term374 A B f _49850 s p1) = (term376 A B p1' f _49850 s)).
Proof. exact (MK_COMB (@lem4359386 A B f _49850 s p1) (@lem4359385 A B p1' f _49850 s)). Qed.
Lemma lem4359388 {A B : Type'} (p1 : B) (f : A -> B) (_49850 : A) (s : A -> Prop) : (term374 A B f _49850 s p1) = (term210 A B p1 f _49850 s).
Proof. exact (eq_refl (term374 A B f _49850 s p1)). Qed.
Lemma lem4359389 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4359390 {A B : Type'} (p1 : B) (f : A -> B) (_49850 : A) (s : A -> Prop) : (term377 A B f _49850 s p1) = (term378 A B p1 f _49850 s).
Proof. exact (MK_COMB (@lem4359389) (@lem4359388 A B p1 f _49850 s)). Qed.
Lemma lem4359391 {A B : Type'} (p1' : A) (f : A -> B) (_49850 : A) (s : A -> Prop) : (term376 A B p1' f _49850 s) = (term376 A B p1' f _49850 s).
Proof. exact (eq_refl (term376 A B p1' f _49850 s)). Qed.
Lemma lem4359392 {A B : Type'} (p1 : B) (p1' : A) (f : A -> B) (_49850 : A) (s : A -> Prop) : ((term374 A B f _49850 s p1) = (term376 A B p1' f _49850 s)) = ((term210 A B p1 f _49850 s) = (term376 A B p1' f _49850 s)).
Proof. exact (MK_COMB (@lem4359390 A B p1 f _49850 s) (@lem4359391 A B p1' f _49850 s)). Qed.
Lemma lem4359393 {A B : Type'} (p1 : B) (p1' : A) (f : A -> B) (_49850 : A) (s : A -> Prop) : ((term374 A B f _49850 s p1) = (term375 A B _49850 s f p1')) = ((term210 A B p1 f _49850 s) = (term376 A B p1' f _49850 s)).
Proof. exact (TRANS (@lem4359387 A B p1 p1' f _49850 s) (@lem4359392 A B p1 p1' f _49850 s)). Qed.
Lemma lem4359394 {A B C D : Type'} (_49850 : A) (p1' : A) (p2' : C) (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) (h1 : term260 A B C D p1' p2' p1 f s p2 g t) : (term210 A B p1 f _49850 s) = (term376 A B p1' f _49850 s).
Proof. exact (EQ_MP (@lem4359393 A B p1 p1' f _49850 s) (@lem4359384 A B C D _49850 p1' p2' p1 f s p2 g t h1)). Qed.
Lemma lem4359395 {A B C D : Type'} (_49850 : A) (p1' : A) (p2' : C) (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) (h1 : term217 A B p1 f s) (h2 : term260 A B C D p1' p2' p1 f s p2 g t) : term376 A B p1' f _49850 s.
Proof. exact (EQ_MP (@lem4359394 A B C D _49850 p1' p2' p1 f s p2 g t h2) (@lem4359340 A B _49850 p1 f s h1)). Qed.
Lemma lem4359452 {C D : Type'} (g : C -> D) (_49851 : C) (t : C -> Prop) : (term373 C D g _49851 t) = (term373 C D g _49851 t).
Proof. exact (eq_refl (term373 C D g _49851 t)). Qed.
Lemma lem4359453 {A B C D : Type'} (_49851 : C) (p1' : A) (p2' : C) (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) (h1 : term260 A B C D p1' p2' p1 f s p2 g t) : (term374 C D g _49851 t p2) = (term375 C D _49851 t g p2').
Proof. exact (MK_COMB (@lem4359452 C D g _49851 t) (@lem4359240 A B C D p1' p2' p1 f s p2 g t h1)). Qed.
Lemma lem4359454 {C D : Type'} (p2' : C) (g : C -> D) (_49851 : C) (t : C -> Prop) : (term375 C D _49851 t g p2') = (term376 C D p2' g _49851 t).
Proof. exact (eq_refl (term375 C D _49851 t g p2')). Qed.
Lemma lem4359455 {C D : Type'} (g : C -> D) (_49851 : C) (t : C -> Prop) (p2 : D) : (term377 C D g _49851 t p2) = (term377 C D g _49851 t p2).
Proof. exact (eq_refl (term377 C D g _49851 t p2)). Qed.
Lemma lem4359456 {C D : Type'} (p2 : D) (p2' : C) (g : C -> D) (_49851 : C) (t : C -> Prop) : ((term374 C D g _49851 t p2) = (term375 C D _49851 t g p2')) = ((term374 C D g _49851 t p2) = (term376 C D p2' g _49851 t)).
Proof. exact (MK_COMB (@lem4359455 C D g _49851 t p2) (@lem4359454 C D p2' g _49851 t)). Qed.
Lemma lem4359457 {C D : Type'} (p2 : D) (g : C -> D) (_49851 : C) (t : C -> Prop) : (term374 C D g _49851 t p2) = (term210 C D p2 g _49851 t).
Proof. exact (eq_refl (term374 C D g _49851 t p2)). Qed.
Lemma lem4359458 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4359459 {C D : Type'} (p2 : D) (g : C -> D) (_49851 : C) (t : C -> Prop) : (term377 C D g _49851 t p2) = (term378 C D p2 g _49851 t).
Proof. exact (MK_COMB (@lem4359458) (@lem4359457 C D p2 g _49851 t)). Qed.
Lemma lem4359460 {C D : Type'} (p2' : C) (g : C -> D) (_49851 : C) (t : C -> Prop) : (term376 C D p2' g _49851 t) = (term376 C D p2' g _49851 t).
Proof. exact (eq_refl (term376 C D p2' g _49851 t)). Qed.
Lemma lem4359461 {C D : Type'} (p2 : D) (p2' : C) (g : C -> D) (_49851 : C) (t : C -> Prop) : ((term374 C D g _49851 t p2) = (term376 C D p2' g _49851 t)) = ((term210 C D p2 g _49851 t) = (term376 C D p2' g _49851 t)).
Proof. exact (MK_COMB (@lem4359459 C D p2 g _49851 t) (@lem4359460 C D p2' g _49851 t)). Qed.
Lemma lem4359462 {C D : Type'} (p2 : D) (p2' : C) (g : C -> D) (_49851 : C) (t : C -> Prop) : ((term374 C D g _49851 t p2) = (term375 C D _49851 t g p2')) = ((term210 C D p2 g _49851 t) = (term376 C D p2' g _49851 t)).
Proof. exact (TRANS (@lem4359456 C D p2 p2' g _49851 t) (@lem4359461 C D p2 p2' g _49851 t)). Qed.
Lemma lem4359463 {A B C D : Type'} (_49851 : C) (p1' : A) (p2' : C) (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) (h1 : term260 A B C D p1' p2' p1 f s p2 g t) : (term210 C D p2 g _49851 t) = (term376 C D p2' g _49851 t).
Proof. exact (EQ_MP (@lem4359462 C D p2 p2' g _49851 t) (@lem4359453 A B C D _49851 p1' p2' p1 f s p2 g t h1)). Qed.
Lemma lem4359520 {A B C D : Type'} (_49851 : C) (p1' : A) (p2' : C) (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) (h1 : term217 C D p2 g t) (h2 : term260 A B C D p1' p2' p1 f s p2 g t) : term376 C D p2' g _49851 t.
Proof. exact (EQ_MP (@lem4359463 A B C D _49851 p1' p2' p1 f s p2 g t h2) (@lem4359246 C D _49851 p2 g t h1)). Qed.
Lemma lem4359535 {A B C D : Type'} (f : A -> B) (p2 : D) (g : C -> D) (_49852 : A) (s : A -> Prop) (_49853 : C) (t : C -> Prop) : (term379 A B C D f p2 g _49852 s _49853 t) = (term379 A B C D f p2 g _49852 s _49853 t).
Proof. exact (eq_refl (term379 A B C D f p2 g _49852 s _49853 t)). Qed.
Lemma lem4359536 {A B C D : Type'} (_49852 : A) (_49853 : C) (p1 : B) (f : A -> B) (p1' : A) (s : A -> Prop) (p2 : D) (g : C -> D) (p2' : C) (t : C -> Prop) (h1 : term315 A B C D p1 f p1' s p2 g p2' t) : (term380 A B C D f p2 g _49852 s _49853 t p1) = (term381 A B C D p2 g _49852 s _49853 t f p1').
Proof. exact (MK_COMB (@lem4359535 A B C D f p2 g _49852 s _49853 t) (@lem4359268 A B C D p1 f p1' s p2 g p2' t h1)). Qed.
Lemma lem4359537 {A B C D : Type'} (p1' : A) (f : A -> B) (p2 : D) (g : C -> D) (_49852 : A) (s : A -> Prop) (_49853 : C) (t : C -> Prop) : (term381 A B C D p2 g _49852 s _49853 t f p1') = (term382 A B C D p1' f p2 g _49852 s _49853 t).
Proof. exact (eq_refl (term381 A B C D p2 g _49852 s _49853 t f p1')). Qed.
Lemma lem4359538 {A B C D : Type'} (f : A -> B) (p2 : D) (g : C -> D) (_49852 : A) (s : A -> Prop) (_49853 : C) (t : C -> Prop) (p1 : B) : (term383 A B C D f p2 g _49852 s _49853 t p1) = (term383 A B C D f p2 g _49852 s _49853 t p1).
Proof. exact (eq_refl (term383 A B C D f p2 g _49852 s _49853 t p1)). Qed.
Lemma lem4359539 {A B C D : Type'} (p1 : B) (p1' : A) (f : A -> B) (p2 : D) (g : C -> D) (_49852 : A) (s : A -> Prop) (_49853 : C) (t : C -> Prop) : ((term380 A B C D f p2 g _49852 s _49853 t p1) = (term381 A B C D p2 g _49852 s _49853 t f p1')) = ((term380 A B C D f p2 g _49852 s _49853 t p1) = (term382 A B C D p1' f p2 g _49852 s _49853 t)).
Proof. exact (MK_COMB (@lem4359538 A B C D f p2 g _49852 s _49853 t p1) (@lem4359537 A B C D p1' f p2 g _49852 s _49853 t)). Qed.
Lemma lem4359540 {A B C D : Type'} (p1 : B) (f : A -> B) (p2 : D) (g : C -> D) (_49852 : A) (s : A -> Prop) (_49853 : C) (t : C -> Prop) : (term380 A B C D f p2 g _49852 s _49853 t p1) = (term371 A B C D p1 f p2 g _49852 s _49853 t).
Proof. exact (eq_refl (term380 A B C D f p2 g _49852 s _49853 t p1)). Qed.
Lemma lem4359541 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4359542 {A B C D : Type'} (p1 : B) (f : A -> B) (p2 : D) (g : C -> D) (_49852 : A) (s : A -> Prop) (_49853 : C) (t : C -> Prop) : (term383 A B C D f p2 g _49852 s _49853 t p1) = (term384 A B C D p1 f p2 g _49852 s _49853 t).
Proof. exact (MK_COMB (@lem4359541) (@lem4359540 A B C D p1 f p2 g _49852 s _49853 t)). Qed.
Lemma lem4359543 {A B C D : Type'} (p1' : A) (f : A -> B) (p2 : D) (g : C -> D) (_49852 : A) (s : A -> Prop) (_49853 : C) (t : C -> Prop) : (term382 A B C D p1' f p2 g _49852 s _49853 t) = (term382 A B C D p1' f p2 g _49852 s _49853 t).
Proof. exact (eq_refl (term382 A B C D p1' f p2 g _49852 s _49853 t)). Qed.
Lemma lem4359544 {A B C D : Type'} (p1 : B) (p1' : A) (f : A -> B) (p2 : D) (g : C -> D) (_49852 : A) (s : A -> Prop) (_49853 : C) (t : C -> Prop) : ((term380 A B C D f p2 g _49852 s _49853 t p1) = (term382 A B C D p1' f p2 g _49852 s _49853 t)) = ((term371 A B C D p1 f p2 g _49852 s _49853 t) = (term382 A B C D p1' f p2 g _49852 s _49853 t)).
Proof. exact (MK_COMB (@lem4359542 A B C D p1 f p2 g _49852 s _49853 t) (@lem4359543 A B C D p1' f p2 g _49852 s _49853 t)). Qed.
Lemma lem4359545 {A B C D : Type'} (p1 : B) (p1' : A) (f : A -> B) (p2 : D) (g : C -> D) (_49852 : A) (s : A -> Prop) (_49853 : C) (t : C -> Prop) : ((term380 A B C D f p2 g _49852 s _49853 t p1) = (term381 A B C D p2 g _49852 s _49853 t f p1')) = ((term371 A B C D p1 f p2 g _49852 s _49853 t) = (term382 A B C D p1' f p2 g _49852 s _49853 t)).
Proof. exact (TRANS (@lem4359539 A B C D p1 p1' f p2 g _49852 s _49853 t) (@lem4359544 A B C D p1 p1' f p2 g _49852 s _49853 t)). Qed.
Lemma lem4359546 {A B C D : Type'} (_49852 : A) (_49853 : C) (p1 : B) (f : A -> B) (p1' : A) (s : A -> Prop) (p2 : D) (g : C -> D) (p2' : C) (t : C -> Prop) (h1 : term315 A B C D p1 f p1' s p2 g p2' t) : (term371 A B C D p1 f p2 g _49852 s _49853 t) = (term382 A B C D p1' f p2 g _49852 s _49853 t).
Proof. exact (EQ_MP (@lem4359545 A B C D p1 p1' f p2 g _49852 s _49853 t) (@lem4359536 A B C D _49852 _49853 p1 f p1' s p2 g p2' t h1)). Qed.
Lemma lem4359547 {A B C D : Type'} (_49852 : A) (_49853 : C) (p1 : B) (f : A -> B) (p1' : A) (s : A -> Prop) (p2 : D) (g : C -> D) (p2' : C) (t : C -> Prop) (h1 : term315 A B C D p1 f p1' s p2 g p2' t) : term382 A B C D p1' f p2 g _49852 s _49853 t.
Proof. exact (EQ_MP (@lem4359546 A B C D _49852 _49853 p1 f p1' s p2 g p2' t h1) (@lem4359262 A B C D _49852 _49853 p1 f p1' s p2 g p2' t h1)). Qed.
Lemma lem4359561 {A B C D : Type'} (p1 : B) (f : A -> B) (p1' : A) (s : A -> Prop) (p2 : D) (g : C -> D) (p2' : C) (t : C -> Prop) (h1 : term315 A B C D p1 f p1' s p2 g p2' t) : p2 = (g p2').
Proof. exact (proj1 (@lem4359099 A B C D p1 f p1' s p2 g p2' t h1)). Qed.
Lemma lem4359604 {A B C D : Type'} (p1' : A) (f : A -> B) (g : C -> D) (_49852 : A) (s : A -> Prop) (_49853 : C) (t : C -> Prop) : (term385 A B C D p1' f g _49852 s _49853 t) = (term385 A B C D p1' f g _49852 s _49853 t).
Proof. exact (eq_refl (term385 A B C D p1' f g _49852 s _49853 t)). Qed.
Lemma lem4359605 {A B C D : Type'} (_49852 : A) (_49853 : C) (p1 : B) (f : A -> B) (p1' : A) (s : A -> Prop) (p2 : D) (g : C -> D) (p2' : C) (t : C -> Prop) (h1 : term315 A B C D p1 f p1' s p2 g p2' t) : (term386 A B C D p1' f g _49852 s _49853 t p2) = (term387 A B C D p1' f _49852 s _49853 t g p2').
Proof. exact (MK_COMB (@lem4359604 A B C D p1' f g _49852 s _49853 t) (@lem4359561 A B C D p1 f p1' s p2 g p2' t h1)). Qed.
Lemma lem4359606 {A B C D : Type'} (p1' : A) (f : A -> B) (p2' : C) (g : C -> D) (_49852 : A) (s : A -> Prop) (_49853 : C) (t : C -> Prop) : (term387 A B C D p1' f _49852 s _49853 t g p2') = (term388 A B C D p1' f p2' g _49852 s _49853 t).
Proof. exact (eq_refl (term387 A B C D p1' f _49852 s _49853 t g p2')). Qed.
Lemma lem4359607 {A B C D : Type'} (p1' : A) (f : A -> B) (g : C -> D) (_49852 : A) (s : A -> Prop) (_49853 : C) (t : C -> Prop) (p2 : D) : (term389 A B C D p1' f g _49852 s _49853 t p2) = (term389 A B C D p1' f g _49852 s _49853 t p2).
Proof. exact (eq_refl (term389 A B C D p1' f g _49852 s _49853 t p2)). Qed.
Lemma lem4359608 {A B C D : Type'} (p2 : D) (p1' : A) (f : A -> B) (p2' : C) (g : C -> D) (_49852 : A) (s : A -> Prop) (_49853 : C) (t : C -> Prop) : ((term386 A B C D p1' f g _49852 s _49853 t p2) = (term387 A B C D p1' f _49852 s _49853 t g p2')) = ((term386 A B C D p1' f g _49852 s _49853 t p2) = (term388 A B C D p1' f p2' g _49852 s _49853 t)).
Proof. exact (MK_COMB (@lem4359607 A B C D p1' f g _49852 s _49853 t p2) (@lem4359606 A B C D p1' f p2' g _49852 s _49853 t)). Qed.
Lemma lem4359609 {A B C D : Type'} (p1' : A) (f : A -> B) (p2 : D) (g : C -> D) (_49852 : A) (s : A -> Prop) (_49853 : C) (t : C -> Prop) : (term386 A B C D p1' f g _49852 s _49853 t p2) = (term382 A B C D p1' f p2 g _49852 s _49853 t).
Proof. exact (eq_refl (term386 A B C D p1' f g _49852 s _49853 t p2)). Qed.
Lemma lem4359610 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4359611 {A B C D : Type'} (p1' : A) (f : A -> B) (p2 : D) (g : C -> D) (_49852 : A) (s : A -> Prop) (_49853 : C) (t : C -> Prop) : (term389 A B C D p1' f g _49852 s _49853 t p2) = (term390 A B C D p1' f p2 g _49852 s _49853 t).
Proof. exact (MK_COMB (@lem4359610) (@lem4359609 A B C D p1' f p2 g _49852 s _49853 t)). Qed.
Lemma lem4359612 {A B C D : Type'} (p1' : A) (f : A -> B) (p2' : C) (g : C -> D) (_49852 : A) (s : A -> Prop) (_49853 : C) (t : C -> Prop) : (term388 A B C D p1' f p2' g _49852 s _49853 t) = (term388 A B C D p1' f p2' g _49852 s _49853 t).
Proof. exact (eq_refl (term388 A B C D p1' f p2' g _49852 s _49853 t)). Qed.
Lemma lem4359613 {A B C D : Type'} (p2 : D) (p1' : A) (f : A -> B) (p2' : C) (g : C -> D) (_49852 : A) (s : A -> Prop) (_49853 : C) (t : C -> Prop) : ((term386 A B C D p1' f g _49852 s _49853 t p2) = (term388 A B C D p1' f p2' g _49852 s _49853 t)) = ((term382 A B C D p1' f p2 g _49852 s _49853 t) = (term388 A B C D p1' f p2' g _49852 s _49853 t)).
Proof. exact (MK_COMB (@lem4359611 A B C D p1' f p2 g _49852 s _49853 t) (@lem4359612 A B C D p1' f p2' g _49852 s _49853 t)). Qed.
Lemma lem4359614 {A B C D : Type'} (p2 : D) (p1' : A) (f : A -> B) (p2' : C) (g : C -> D) (_49852 : A) (s : A -> Prop) (_49853 : C) (t : C -> Prop) : ((term386 A B C D p1' f g _49852 s _49853 t p2) = (term387 A B C D p1' f _49852 s _49853 t g p2')) = ((term382 A B C D p1' f p2 g _49852 s _49853 t) = (term388 A B C D p1' f p2' g _49852 s _49853 t)).
Proof. exact (TRANS (@lem4359608 A B C D p2 p1' f p2' g _49852 s _49853 t) (@lem4359613 A B C D p2 p1' f p2' g _49852 s _49853 t)). Qed.
Lemma lem4359615 {A B C D : Type'} (_49852 : A) (_49853 : C) (p1 : B) (f : A -> B) (p1' : A) (s : A -> Prop) (p2 : D) (g : C -> D) (p2' : C) (t : C -> Prop) (h1 : term315 A B C D p1 f p1' s p2 g p2' t) : (term382 A B C D p1' f p2 g _49852 s _49853 t) = (term388 A B C D p1' f p2' g _49852 s _49853 t).
Proof. exact (EQ_MP (@lem4359614 A B C D p2 p1' f p2' g _49852 s _49853 t) (@lem4359605 A B C D _49852 _49853 p1 f p1' s p2 g p2' t h1)). Qed.
Lemma lem4359616 {A B C D : Type'} (_49852 : A) (_49853 : C) (p1 : B) (f : A -> B) (p1' : A) (s : A -> Prop) (p2 : D) (g : C -> D) (p2' : C) (t : C -> Prop) (h1 : term315 A B C D p1 f p1' s p2 g p2' t) : term388 A B C D p1' f p2' g _49852 s _49853 t.
Proof. exact (EQ_MP (@lem4359615 A B C D _49852 _49853 p1 f p1' s p2 g p2' t h1) (@lem4359547 A B C D _49852 _49853 p1 f p1' s p2 g p2' t h1)). Qed.
Lemma lem4359702 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem4359703 {B : Type'} (x : B) : x = x.
Proof. exact (@lem4359702 B x). Qed.
Lemma lem4359704 {A B : Type'} (f : A -> B) (p1' : A) : (f p1') = (f p1').
Proof. exact (@lem4359703 B (f p1')). Qed.
Lemma lem4359705 {A B : Type'} (f : A -> B) (p1' : A) : term391 A B f p1'.
Proof. exact (fun h0 : term392 A B f p1' => @lem4359704 A B f p1'). Qed.
Lemma lem4359707 (p : Prop) : (term393 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4359708 {A B : Type'} (f : A -> B) (p1' : A) : (term391 A B f p1') = ((f p1') = (f p1')).
Proof. exact (@lem4359707 ((f p1') = (f p1'))). Qed.
Lemma lem4359709 {A B : Type'} (f : A -> B) (p1' : A) : (f p1') = (f p1').
Proof. exact (EQ_MP (@lem4359708 A B f p1') (@lem4359705 A B f p1')). Qed.
Lemma lem4359711 {A B C D : Type'} (p1' : A) (p2' : C) (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) (h1 : term260 A B C D p1' p2' p1 f s p2 g t) : @IN A p1' s.
Proof. exact (proj1 (@lem4359089 A B C D p1' p2' p1 f s p2 g t h1)). Qed.
Lemma lem4359712 {A B C D : Type'} (p1' : A) (p2' : C) (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) (h1 : term260 A B C D p1' p2' p1 f s p2 g t) : term394 A p1' s.
Proof. exact (fun h0 : term395 A p1' s => @lem4359711 A B C D p1' p2' p1 f s p2 g t h1). Qed.
Lemma lem4359714 (p : Prop) : (term393 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4359715 {A : Type'} (p1' : A) (s : A -> Prop) : (term394 A p1' s) = (@IN A p1' s).
Proof. exact (@lem4359714 (@IN A p1' s)). Qed.
Lemma lem4359716 {A B C D : Type'} (p1' : A) (p2' : C) (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) (h1 : term260 A B C D p1' p2' p1 f s p2 g t) : @IN A p1' s.
Proof. exact (EQ_MP (@lem4359715 A p1' s) (@lem4359712 A B C D p1' p2' p1 f s p2 g t h1)). Qed.
Lemma lem4359718 (a : Prop) (b : Prop) : (term396 a b) = (term397 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4359719 {A B : Type'} (p1' : A) (f : A -> B) (_49850 : A) (s : A -> Prop) : (term376 A B p1' f _49850 s) = (term398 A B p1' f _49850 s).
Proof. exact (@lem4359718 ((f p1') = (f _49850)) (@IN A _49850 s)). Qed.
Lemma lem4359721 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4359722 {A B : Type'} (p1' : A) (f : A -> B) (_49850 : A) (s : A -> Prop) : (term398 A B p1' f _49850 s) = (term399 A B p1' f _49850 s).
Proof. exact (@lem4359721 (term400 A B p1' f _49850 s)). Qed.
Lemma lem4359723 {A B : Type'} (p1' : A) (f : A -> B) (_49850 : A) (s : A -> Prop) : (term376 A B p1' f _49850 s) = (term399 A B p1' f _49850 s).
Proof. exact (TRANS (@lem4359719 A B p1' f _49850 s) (@lem4359722 A B p1' f _49850 s)). Qed.
Lemma lem4359725 {A B C D : Type'} (p1' : A) (p2' : C) (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) (h1 : term260 A B C D p1' p2' p1 f s p2 g t) : term401 A B f p1' s.
Proof. exact (conj (@lem4359709 A B f p1') (@lem4359716 A B C D p1' p2' p1 f s p2 g t h1)). Qed.
Lemma lem4359727 {A B C D : Type'} (_49850 : A) (p1' : A) (p2' : C) (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) (h1 : term217 A B p1 f s) (h2 : term260 A B C D p1' p2' p1 f s p2 g t) : term399 A B p1' f _49850 s.
Proof. exact (EQ_MP (@lem4359723 A B p1' f _49850 s) (@lem4359395 A B C D _49850 p1' p2' p1 f s p2 g t h1 h2)). Qed.
Lemma lem4359728 {A B C D : Type'} (_49850 : A) (p1' : A) (p2' : C) (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) (h1 : term217 A B p1 f s) (h2 : term260 A B C D p1' p2' p1 f s p2 g t) : term399 A B p1' f _49850 s.
Proof. exact (@lem4359727 A B C D _49850 p1' p2' p1 f s p2 g t h1 h2). Qed.
Lemma lem4359729 {A B C D : Type'} (p1' : A) (p2' : C) (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) (h1 : term217 A B p1 f s) (h2 : term260 A B C D p1' p2' p1 f s p2 g t) : term402 A B f p1' s.
Proof. exact (@lem4359728 A B C D p1' p1' p2' p1 f s p2 g t h1 h2). Qed.
Lemma lem4359732 {A B C D : Type'} (p1' : A) (p2' : C) (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) (h1 : term217 A B p1 f s) (h2 : term260 A B C D p1' p2' p1 f s p2 g t) : False.
Proof. exact (@lem4359729 A B C D p1' p2' p1 f s p2 g t h1 h2 (@lem4359725 A B C D p1' p2' p1 f s p2 g t h2)). Qed.
Lemma lem4359733 {A B C D : Type'} (p1' : A) (p2' : C) (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) (h1 : term217 A B p1 f s) (h2 : term260 A B C D p1' p2' p1 f s p2 g t) : term403.
Proof. exact (fun h0 : ~ False => @lem4359732 A B C D p1' p2' p1 f s p2 g t h1 h2). Qed.
Lemma lem4359735 (p : Prop) : (term393 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4359736 : term403 = False.
Proof. exact (@lem4359735 False). Qed.
Lemma lem4359795 {D : Type'} (x : D) : x = x.
Proof. exact (@lem21386 D x). Qed.
Lemma lem4359796 {D : Type'} (x : D) : x = x.
Proof. exact (@lem4359795 D x). Qed.
Lemma lem4359797 {C D : Type'} (g : C -> D) (p2' : C) : (g p2') = (g p2').
Proof. exact (@lem4359796 D (g p2')). Qed.
Lemma lem4359798 {C D : Type'} (g : C -> D) (p2' : C) : term391 C D g p2'.
Proof. exact (fun h0 : term392 C D g p2' => @lem4359797 C D g p2'). Qed.
Lemma lem4359800 (p : Prop) : (term393 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4359801 {C D : Type'} (g : C -> D) (p2' : C) : (term391 C D g p2') = ((g p2') = (g p2')).
Proof. exact (@lem4359800 ((g p2') = (g p2'))). Qed.
Lemma lem4359802 {C D : Type'} (g : C -> D) (p2' : C) : (g p2') = (g p2').
Proof. exact (EQ_MP (@lem4359801 C D g p2') (@lem4359798 C D g p2')). Qed.
Lemma lem4359804 {A B C D : Type'} (p1' : A) (p2' : C) (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) (h1 : term260 A B C D p1' p2' p1 f s p2 g t) : @IN C p2' t.
Proof. exact (proj2 (@lem4359089 A B C D p1' p2' p1 f s p2 g t h1)). Qed.
Lemma lem4359805 {A B C D : Type'} (p1' : A) (p2' : C) (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) (h1 : term260 A B C D p1' p2' p1 f s p2 g t) : term394 C p2' t.
Proof. exact (fun h0 : term395 C p2' t => @lem4359804 A B C D p1' p2' p1 f s p2 g t h1). Qed.
Lemma lem4359807 (p : Prop) : (term393 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4359808 {C : Type'} (p2' : C) (t : C -> Prop) : (term394 C p2' t) = (@IN C p2' t).
Proof. exact (@lem4359807 (@IN C p2' t)). Qed.
Lemma lem4359809 {A B C D : Type'} (p1' : A) (p2' : C) (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) (h1 : term260 A B C D p1' p2' p1 f s p2 g t) : @IN C p2' t.
Proof. exact (EQ_MP (@lem4359808 C p2' t) (@lem4359805 A B C D p1' p2' p1 f s p2 g t h1)). Qed.
Lemma lem4359811 (a : Prop) (b : Prop) : (term396 a b) = (term397 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4359812 {C D : Type'} (p2' : C) (g : C -> D) (_49851 : C) (t : C -> Prop) : (term376 C D p2' g _49851 t) = (term398 C D p2' g _49851 t).
Proof. exact (@lem4359811 ((g p2') = (g _49851)) (@IN C _49851 t)). Qed.
Lemma lem4359814 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4359815 {C D : Type'} (p2' : C) (g : C -> D) (_49851 : C) (t : C -> Prop) : (term398 C D p2' g _49851 t) = (term399 C D p2' g _49851 t).
Proof. exact (@lem4359814 (term400 C D p2' g _49851 t)). Qed.
Lemma lem4359816 {C D : Type'} (p2' : C) (g : C -> D) (_49851 : C) (t : C -> Prop) : (term376 C D p2' g _49851 t) = (term399 C D p2' g _49851 t).
Proof. exact (TRANS (@lem4359812 C D p2' g _49851 t) (@lem4359815 C D p2' g _49851 t)). Qed.
Lemma lem4359818 {A B C D : Type'} (p1' : A) (p2' : C) (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) (h1 : term260 A B C D p1' p2' p1 f s p2 g t) : term401 C D g p2' t.
Proof. exact (conj (@lem4359802 C D g p2') (@lem4359809 A B C D p1' p2' p1 f s p2 g t h1)). Qed.
Lemma lem4359820 {A B C D : Type'} (_49851 : C) (p1' : A) (p2' : C) (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) (h1 : term217 C D p2 g t) (h2 : term260 A B C D p1' p2' p1 f s p2 g t) : term399 C D p2' g _49851 t.
Proof. exact (EQ_MP (@lem4359816 C D p2' g _49851 t) (@lem4359520 A B C D _49851 p1' p2' p1 f s p2 g t h1 h2)). Qed.
Lemma lem4359821 {A B C D : Type'} (_49851 : C) (p1' : A) (p2' : C) (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) (h1 : term217 C D p2 g t) (h2 : term260 A B C D p1' p2' p1 f s p2 g t) : term399 C D p2' g _49851 t.
Proof. exact (@lem4359820 A B C D _49851 p1' p2' p1 f s p2 g t h1 h2). Qed.
Lemma lem4359822 {A B C D : Type'} (p1' : A) (p2' : C) (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) (h1 : term217 C D p2 g t) (h2 : term260 A B C D p1' p2' p1 f s p2 g t) : term402 C D g p2' t.
Proof. exact (@lem4359821 A B C D p2' p1' p2' p1 f s p2 g t h1 h2). Qed.
Lemma lem4359825 {A B C D : Type'} (p1' : A) (p2' : C) (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) (h1 : term217 C D p2 g t) (h2 : term260 A B C D p1' p2' p1 f s p2 g t) : False.
Proof. exact (@lem4359822 A B C D p1' p2' p1 f s p2 g t h1 h2 (@lem4359818 A B C D p1' p2' p1 f s p2 g t h2)). Qed.
Lemma lem4359826 {A B C D : Type'} (p1' : A) (p2' : C) (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) (h1 : term217 C D p2 g t) (h2 : term260 A B C D p1' p2' p1 f s p2 g t) : term403.
Proof. exact (fun h0 : ~ False => @lem4359825 A B C D p1' p2' p1 f s p2 g t h1 h2). Qed.
Lemma lem4359828 (p : Prop) : (term393 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4359829 : term403 = False.
Proof. exact (@lem4359828 False). Qed.
Lemma lem4359898 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem4359899 {B : Type'} (x : B) : x = x.
Proof. exact (@lem4359898 B x). Qed.
Lemma lem4359900 {A B : Type'} (f : A -> B) (p1' : A) : (f p1') = (f p1').
Proof. exact (@lem4359899 B (f p1')). Qed.
Lemma lem4359901 {A B : Type'} (f : A -> B) (p1' : A) : term391 A B f p1'.
Proof. exact (fun h0 : term392 A B f p1' => @lem4359900 A B f p1'). Qed.
Lemma lem4359903 (p : Prop) : (term393 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4359904 {A B : Type'} (f : A -> B) (p1' : A) : (term391 A B f p1') = ((f p1') = (f p1')).
Proof. exact (@lem4359903 ((f p1') = (f p1'))). Qed.
Lemma lem4359905 {A B : Type'} (f : A -> B) (p1' : A) : (f p1') = (f p1').
Proof. exact (EQ_MP (@lem4359904 A B f p1') (@lem4359901 A B f p1')). Qed.
Lemma lem4359907 {D : Type'} (x : D) : x = x.
Proof. exact (@lem21386 D x). Qed.
Lemma lem4359908 {D : Type'} (x : D) : x = x.
Proof. exact (@lem4359907 D x). Qed.
Lemma lem4359909 {C D : Type'} (g : C -> D) (p2' : C) : (g p2') = (g p2').
Proof. exact (@lem4359908 D (g p2')). Qed.
Lemma lem4359910 {C D : Type'} (g : C -> D) (p2' : C) : term391 C D g p2'.
Proof. exact (fun h0 : term392 C D g p2' => @lem4359909 C D g p2'). Qed.
Lemma lem4359912 (p : Prop) : (term393 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4359913 {C D : Type'} (g : C -> D) (p2' : C) : (term391 C D g p2') = ((g p2') = (g p2')).
Proof. exact (@lem4359912 ((g p2') = (g p2'))). Qed.
Lemma lem4359914 {C D : Type'} (g : C -> D) (p2' : C) : (g p2') = (g p2').
Proof. exact (EQ_MP (@lem4359913 C D g p2') (@lem4359910 C D g p2')). Qed.
Lemma lem4359916 {A B C D : Type'} (p1 : B) (f : A -> B) (p1' : A) (s : A -> Prop) (p2 : D) (g : C -> D) (p2' : C) (t : C -> Prop) (h1 : term315 A B C D p1 f p1' s p2 g p2' t) : @IN A p1' s.
Proof. exact (proj2 (@lem4359100 A B C D p1 f p1' s p2 g p2' t h1)). Qed.
Lemma lem4359917 {A B C D : Type'} (p1 : B) (f : A -> B) (p1' : A) (s : A -> Prop) (p2 : D) (g : C -> D) (p2' : C) (t : C -> Prop) (h1 : term315 A B C D p1 f p1' s p2 g p2' t) : term394 A p1' s.
Proof. exact (fun h0 : term395 A p1' s => @lem4359916 A B C D p1 f p1' s p2 g p2' t h1). Qed.
Lemma lem4359919 (p : Prop) : (term393 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4359920 {A : Type'} (p1' : A) (s : A -> Prop) : (term394 A p1' s) = (@IN A p1' s).
Proof. exact (@lem4359919 (@IN A p1' s)). Qed.
Lemma lem4359921 {A B C D : Type'} (p1 : B) (f : A -> B) (p1' : A) (s : A -> Prop) (p2 : D) (g : C -> D) (p2' : C) (t : C -> Prop) (h1 : term315 A B C D p1 f p1' s p2 g p2' t) : @IN A p1' s.
Proof. exact (EQ_MP (@lem4359920 A p1' s) (@lem4359917 A B C D p1 f p1' s p2 g p2' t h1)). Qed.
Lemma lem4359923 {A B C D : Type'} (p1 : B) (f : A -> B) (p1' : A) (s : A -> Prop) (p2 : D) (g : C -> D) (p2' : C) (t : C -> Prop) (h1 : term315 A B C D p1 f p1' s p2 g p2' t) : @IN C p2' t.
Proof. exact (proj2 (@lem4359099 A B C D p1 f p1' s p2 g p2' t h1)). Qed.
Lemma lem4359924 {A B C D : Type'} (p1 : B) (f : A -> B) (p1' : A) (s : A -> Prop) (p2 : D) (g : C -> D) (p2' : C) (t : C -> Prop) (h1 : term315 A B C D p1 f p1' s p2 g p2' t) : term394 C p2' t.
Proof. exact (fun h0 : term395 C p2' t => @lem4359923 A B C D p1 f p1' s p2 g p2' t h1). Qed.
Lemma lem4359926 (p : Prop) : (term393 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4359927 {C : Type'} (p2' : C) (t : C -> Prop) : (term394 C p2' t) = (@IN C p2' t).
Proof. exact (@lem4359926 (@IN C p2' t)). Qed.
Lemma lem4359928 {A B C D : Type'} (p1 : B) (f : A -> B) (p1' : A) (s : A -> Prop) (p2 : D) (g : C -> D) (p2' : C) (t : C -> Prop) (h1 : term315 A B C D p1 f p1' s p2 g p2' t) : @IN C p2' t.
Proof. exact (EQ_MP (@lem4359927 C p2' t) (@lem4359924 A B C D p1 f p1' s p2 g p2' t h1)). Qed.
Lemma lem4359930 (a : Prop) (b : Prop) : (term396 a b) = (term397 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4359931 {A C : Type'} (_49852 : A) (s : A -> Prop) (_49853 : C) (t : C -> Prop) : (term187 A C _49852 s _49853 t) = (term186 A C _49852 s _49853 t).
Proof. exact (@lem4359930 (@IN A _49852 s) (@IN C _49853 t)). Qed.
Lemma lem4359932 {C D : Type'} (p2' : C) (g : C -> D) (_49853 : C) : (term404 C D p2' g _49853) = (term404 C D p2' g _49853).
Proof. exact (eq_refl (term404 C D p2' g _49853)). Qed.
Lemma lem4359933 {A C D : Type'} (p2' : C) (g : C -> D) (_49852 : A) (s : A -> Prop) (_49853 : C) (t : C -> Prop) : (term405 A C D p2' g _49852 s _49853 t) = (term406 A C D p2' g _49852 s _49853 t).
Proof. exact (MK_COMB (@lem4359932 C D p2' g _49853) (@lem4359931 A C _49852 s _49853 t)). Qed.
Lemma lem4359935 (a : Prop) (b : Prop) : (term396 a b) = (term397 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4359936 {A C D : Type'} (p2' : C) (g : C -> D) (_49852 : A) (s : A -> Prop) (_49853 : C) (t : C -> Prop) : (term406 A C D p2' g _49852 s _49853 t) = (term407 A C D p2' g _49852 s _49853 t).
Proof. exact (@lem4359935 ((g p2') = (g _49853)) (term26 A C _49852 s _49853 t)). Qed.
Lemma lem4359937 {A C D : Type'} (p2' : C) (g : C -> D) (_49852 : A) (s : A -> Prop) (_49853 : C) (t : C -> Prop) : (term405 A C D p2' g _49852 s _49853 t) = (term407 A C D p2' g _49852 s _49853 t).
Proof. exact (TRANS (@lem4359933 A C D p2' g _49852 s _49853 t) (@lem4359936 A C D p2' g _49852 s _49853 t)). Qed.
Lemma lem4359938 {A B : Type'} (p1' : A) (f : A -> B) (_49852 : A) : (term404 A B p1' f _49852) = (term404 A B p1' f _49852).
Proof. exact (eq_refl (term404 A B p1' f _49852)). Qed.
Lemma lem4359939 {A B C D : Type'} (p1' : A) (f : A -> B) (p2' : C) (g : C -> D) (_49852 : A) (s : A -> Prop) (_49853 : C) (t : C -> Prop) : (term388 A B C D p1' f p2' g _49852 s _49853 t) = (term408 A B C D p1' f p2' g _49852 s _49853 t).
Proof. exact (MK_COMB (@lem4359938 A B p1' f _49852) (@lem4359937 A C D p2' g _49852 s _49853 t)). Qed.
Lemma lem4359941 (a : Prop) (b : Prop) : (term396 a b) = (term397 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4359942 {A B C D : Type'} (p1' : A) (f : A -> B) (p2' : C) (g : C -> D) (_49852 : A) (s : A -> Prop) (_49853 : C) (t : C -> Prop) : (term408 A B C D p1' f p2' g _49852 s _49853 t) = (term409 A B C D p1' f p2' g _49852 s _49853 t).
Proof. exact (@lem4359941 ((f p1') = (f _49852)) (term410 A C D p2' g _49852 s _49853 t)). Qed.
Lemma lem4359943 {A B C D : Type'} (p1' : A) (f : A -> B) (p2' : C) (g : C -> D) (_49852 : A) (s : A -> Prop) (_49853 : C) (t : C -> Prop) : (term388 A B C D p1' f p2' g _49852 s _49853 t) = (term409 A B C D p1' f p2' g _49852 s _49853 t).
Proof. exact (TRANS (@lem4359939 A B C D p1' f p2' g _49852 s _49853 t) (@lem4359942 A B C D p1' f p2' g _49852 s _49853 t)). Qed.
Lemma lem4359945 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4359946 {A B C D : Type'} (p1' : A) (f : A -> B) (p2' : C) (g : C -> D) (_49852 : A) (s : A -> Prop) (_49853 : C) (t : C -> Prop) : (term409 A B C D p1' f p2' g _49852 s _49853 t) = (term411 A B C D p1' f p2' g _49852 s _49853 t).
Proof. exact (@lem4359945 (term412 A B C D p1' f p2' g _49852 s _49853 t)). Qed.
Lemma lem4359947 {A B C D : Type'} (p1' : A) (f : A -> B) (p2' : C) (g : C -> D) (_49852 : A) (s : A -> Prop) (_49853 : C) (t : C -> Prop) : (term388 A B C D p1' f p2' g _49852 s _49853 t) = (term411 A B C D p1' f p2' g _49852 s _49853 t).
Proof. exact (TRANS (@lem4359943 A B C D p1' f p2' g _49852 s _49853 t) (@lem4359946 A B C D p1' f p2' g _49852 s _49853 t)). Qed.
Lemma lem4359949 {A B C D : Type'} (p1 : B) (f : A -> B) (p1' : A) (s : A -> Prop) (p2 : D) (g : C -> D) (p2' : C) (t : C -> Prop) (h1 : term315 A B C D p1 f p1' s p2 g p2' t) : term26 A C p1' s p2' t.
Proof. exact (conj (@lem4359921 A B C D p1 f p1' s p2 g p2' t h1) (@lem4359928 A B C D p1 f p1' s p2 g p2' t h1)). Qed.
Lemma lem4359950 {A B C D : Type'} (p1 : B) (f : A -> B) (p1' : A) (s : A -> Prop) (p2 : D) (g : C -> D) (p2' : C) (t : C -> Prop) (h1 : term315 A B C D p1 f p1' s p2 g p2' t) : term413 A C D g p1' s p2' t.
Proof. exact (conj (@lem4359914 C D g p2') (@lem4359949 A B C D p1 f p1' s p2 g p2' t h1)). Qed.
Lemma lem4359951 {A B C D : Type'} (p1 : B) (f : A -> B) (p1' : A) (s : A -> Prop) (p2 : D) (g : C -> D) (p2' : C) (t : C -> Prop) (h1 : term315 A B C D p1 f p1' s p2 g p2' t) : term414 A B C D f g p1' s p2' t.
Proof. exact (conj (@lem4359905 A B f p1') (@lem4359950 A B C D p1 f p1' s p2 g p2' t h1)). Qed.
Lemma lem4359953 {A B C D : Type'} (_49852 : A) (_49853 : C) (p1 : B) (f : A -> B) (p1' : A) (s : A -> Prop) (p2 : D) (g : C -> D) (p2' : C) (t : C -> Prop) (h1 : term315 A B C D p1 f p1' s p2 g p2' t) : term411 A B C D p1' f p2' g _49852 s _49853 t.
Proof. exact (EQ_MP (@lem4359947 A B C D p1' f p2' g _49852 s _49853 t) (@lem4359616 A B C D _49852 _49853 p1 f p1' s p2 g p2' t h1)). Qed.
Lemma lem4359954 {A B C D : Type'} (_49852 : A) (_49853 : C) (p1 : B) (f : A -> B) (p1' : A) (s : A -> Prop) (p2 : D) (g : C -> D) (p2' : C) (t : C -> Prop) (h1 : term315 A B C D p1 f p1' s p2 g p2' t) : term411 A B C D p1' f p2' g _49852 s _49853 t.
Proof. exact (@lem4359953 A B C D _49852 _49853 p1 f p1' s p2 g p2' t h1). Qed.
Lemma lem4359955 {A B C D : Type'} (p1 : B) (f : A -> B) (p1' : A) (s : A -> Prop) (p2 : D) (g : C -> D) (p2' : C) (t : C -> Prop) (h1 : term315 A B C D p1 f p1' s p2 g p2' t) : term415 A B C D f g p1' s p2' t.
Proof. exact (@lem4359954 A B C D p1' p2' p1 f p1' s p2 g p2' t h1). Qed.
Lemma lem4359958 {A B C D : Type'} (p1 : B) (f : A -> B) (p1' : A) (s : A -> Prop) (p2 : D) (g : C -> D) (p2' : C) (t : C -> Prop) (h1 : term315 A B C D p1 f p1' s p2 g p2' t) : False.
Proof. exact (@lem4359955 A B C D p1 f p1' s p2 g p2' t h1 (@lem4359951 A B C D p1 f p1' s p2 g p2' t h1)). Qed.
Lemma lem4359959 {A B C D : Type'} (p1 : B) (f : A -> B) (p1' : A) (s : A -> Prop) (p2 : D) (g : C -> D) (p2' : C) (t : C -> Prop) (h1 : term315 A B C D p1 f p1' s p2 g p2' t) : term403.
Proof. exact (fun h0 : ~ False => @lem4359958 A B C D p1 f p1' s p2 g p2' t h1). Qed.
Lemma lem4359961 (p : Prop) : (term393 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4359962 : term403 = False.
Proof. exact (@lem4359961 False). Qed.
Lemma lem4359965 {A B C D : Type'} (p1 : B) (f : A -> B) (p1' : A) (s : A -> Prop) (p2 : D) (g : C -> D) (p2' : C) (t : C -> Prop) (h1 : term315 A B C D p1 f p1' s p2 g p2' t) : False.
Proof. exact (EQ_MP (@lem4359962) (@lem4359959 A B C D p1 f p1' s p2 g p2' t h1)). Qed.
Lemma lem4359967 {A B C D : Type'} (p1' : A) (p2' : C) (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) (h1 : term217 C D p2 g t) (h2 : term260 A B C D p1' p2' p1 f s p2 g t) : False.
Proof. exact (EQ_MP (@lem4359829) (@lem4359826 A B C D p1' p2' p1 f s p2 g t h1 h2)). Qed.
Lemma lem4359969 {A B C D : Type'} (p1' : A) (p2' : C) (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) (h1 : term217 A B p1 f s) (h2 : term260 A B C D p1' p2' p1 f s p2 g t) : False.
Proof. exact (EQ_MP (@lem4359736) (@lem4359733 A B C D p1' p2' p1 f s p2 g t h1 h2)). Qed.
Lemma lem4359970 {A B C D : Type'} (p1' : A) (p2' : C) (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) (h1 : term217 C D p2 g t) (h2 : term260 A B C D p1' p2' p1 f s p2 g t) : (term217 C D p2 g t) = False.
Proof. exact (prop_ext (fun h3 : term217 C D p2 g t => @lem4359967 A B C D p1' p2' p1 f s p2 g t h1 h2) (fun h3 : False => @lem4359162 C D p2 g t h1)). Qed.
Lemma lem4359971 {A B C D : Type'} (p1' : A) (p2' : C) (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) (h1 : term217 C D p2 g t) (h2 : term260 A B C D p1' p2' p1 f s p2 g t) : False.
Proof. exact (EQ_MP (@lem4359970 A B C D p1' p2' p1 f s p2 g t h1 h2) (@lem4359162 C D p2 g t h1)). Qed.
Lemma lem4359972 {A B C D : Type'} (p1' : A) (p2' : C) (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) (h1 : term217 A B p1 f s) (h2 : term260 A B C D p1' p2' p1 f s p2 g t) : (term217 A B p1 f s) = False.
Proof. exact (prop_ext (fun h3 : term217 A B p1 f s => @lem4359969 A B C D p1' p2' p1 f s p2 g t h1 h2) (fun h3 : False => @lem4359133 A B p1 f s h1)). Qed.
Lemma lem4359973 {A B C D : Type'} (p1' : A) (p2' : C) (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) (h1 : term217 A B p1 f s) (h2 : term260 A B C D p1' p2' p1 f s p2 g t) : False.
Proof. exact (EQ_MP (@lem4359972 A B C D p1' p2' p1 f s p2 g t h1 h2) (@lem4359133 A B p1 f s h1)). Qed.
Lemma lem4359974 {A B C D : Type'} (p1' : A) (p2' : C) (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) (h1 : term260 A B C D p1' p2' p1 f s p2 g t) : False.
Proof. exact (or_elim (@lem4359087 A B C D p1' p2' p1 f s p2 g t h1) (fun h0 : term217 A B p1 f s => @lem4359973 A B C D p1' p2' p1 f s p2 g t h0 h1) (fun h0 : term217 C D p2 g t => @lem4359971 A B C D p1' p2' p1 f s p2 g t h0 h1)). Qed.
Lemma lem4359975 {A B C D : Type'} (p1 : B) (f : A -> B) (p1' : A) (s : A -> Prop) (p2 : D) (g : C -> D) (p2' : C) (t : C -> Prop) (h1 : term359 A B C D p1 f p1' s p2 g p2' t) : False.
Proof. exact (or_elim (@lem4359084 A B C D p1 f p1' s p2 g p2' t h1) (fun h0 : term260 A B C D p1' p2' p1 f s p2 g t => @lem4359974 A B C D p1' p2' p1 f s p2 g t h0) (fun h0 : term315 A B C D p1 f p1' s p2 g p2' t => @lem4359965 A B C D p1 f p1' s p2 g p2' t h0)). Qed.
Lemma lem4359976 {A B C D : Type'} (p1 : B) (f : A -> B) (p1' : A) (s : A -> Prop) (p2 : D) (g : C -> D) (p2' : C) (t : C -> Prop) (h1 : term359 A B C D p1 f p1' s p2 g p2' t) : (term359 A B C D p1 f p1' s p2 g p2' t) = False.
Proof. exact (prop_ext (fun h2 : term359 A B C D p1 f p1' s p2 g p2' t => @lem4359975 A B C D p1 f p1' s p2 g p2' t h1) (fun h2 : False => @lem4359084 A B C D p1 f p1' s p2 g p2' t h1)). Qed.
Lemma lem4359977 {A B C D : Type'} (p1 : B) (f : A -> B) (p1' : A) (s : A -> Prop) (p2 : D) (g : C -> D) (p2' : C) (t : C -> Prop) (h1 : term359 A B C D p1 f p1' s p2 g p2' t) : False.
Proof. exact (EQ_MP (@lem4359976 A B C D p1 f p1' s p2 g p2' t h1) (@lem4359084 A B C D p1 f p1' s p2 g p2' t h1)). Qed.
Lemma lem4359978 {A B C D : Type'} (p1 : B) (f : A -> B) (p1' : A) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) (h1 : term362 A B C D p1 f p1' s p2 g t) : False.
Proof. exact (ex_elim (@lem4358913 A B C D p1 f p1' s p2 g t h1) (fun p2' : C => fun h0 : term361 A B C D p1 f p1' s p2 g t p2' => @lem4359977 A B C D p1 f p1' s p2 g p2' t h0)). Qed.
Lemma lem4359979 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) (h1 : term183 A B C D p1 f s p2 g t) : False.
Proof. exact (ex_elim (@lem4358912 A B C D p1 f s p2 g t h1) (fun p1' : A => fun h0 : term366 A B C D p1 f s p2 g t p1' => @lem4359978 A B C D p1 f p1' s p2 g t h0)). Qed.
Lemma lem4359980 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) (h1 : term183 A B C D p1 f s p2 g t) : (term183 A B C D p1 f s p2 g t) = False.
Proof. exact (prop_ext (fun h2 : term183 A B C D p1 f s p2 g t => @lem4359979 A B C D p1 f s p2 g t h1) (fun h2 : False => @lem4358248 A B C D p1 f s p2 g t h1)). Qed.
Lemma lem4359981 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) (h1 : term183 A B C D p1 f s p2 g t) : False.
Proof. exact (EQ_MP (@lem4359980 A B C D p1 f s p2 g t h1) (@lem4358248 A B C D p1 f s p2 g t h1)). Qed.
Lemma lem4359982 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : term182 A B C D p1 f s p2 g t.
Proof. exact (fun h0 : term183 A B C D p1 f s p2 g t => @lem4359981 A B C D p1 f s p2 g t h0). Qed.
Lemma lem4359983 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (p2 : D) (g : C -> D) (t : C -> Prop) : (term145 A B C D p1 f p2 g s t) = (term151 A B C D p1 f s p2 g t).
Proof. exact (EQ_MP (@lem4358247 A B C D p1 f s p2 g t) (@lem4359982 A B C D p1 f s p2 g t)). Qed.
Lemma lem4359988 {A B C D : Type'} (p1 : B) (f : A -> B) (s : A -> Prop) (g : C -> D) (t : C -> Prop) : term153 A B C D p1 f s g t.
Proof. exact (fun p2 : D => @lem4359983 A B C D p1 f s p2 g t). Qed.
Lemma lem4359993 {A B C D : Type'} (f : A -> B) (s : A -> Prop) (g : C -> D) (t : C -> Prop) : term155 A B C D f s g t.
Proof. exact (fun p1 : B => @lem4359988 A B C D p1 f s g t). Qed.
Lemma lem4359998 {A B C D : Type'} (f : A -> B) (s : A -> Prop) (g : C -> D) : term159 A B C D f s g.
Proof. exact (fun t : C -> Prop => @lem4359993 A B C D f s g t). Qed.
Lemma lem4360003 {A B C D : Type'} (f : A -> B) (g : C -> D) : term163 A B C D f g.
Proof. exact (fun s : A -> Prop => @lem4359998 A B C D f s g). Qed.
Lemma lem4360008 {A B C D : Type'} (f : A -> B) : term167 A B C D f.
Proof. exact (fun g : C -> D => @lem4360003 A B C D f g). Qed.
Lemma lem4360013 {A B C D : Type'} : term171 A B C D.
Proof. exact (fun f : A -> B => @lem4360008 A B C D f). Qed.
Lemma lem4360014 {A B C D : Type'} : term173 A B C D.
Proof. exact (EQ_MP (@lem4358243 A B C D) (@lem4360013 A B C D)). Qed.
Lemma lem4360016 {A B C D : Type'} : term173 A B C D.
Proof. exact (@lem4357913 A B C D (@lem4360014 A B C D)). Qed.
Lemma lem4360017 {A B C D : Type'} (h1 : term174 A B C D) : False.
Proof. exact (@lem4360016 A B C D (@lem4357897 A B C D h1)). Qed.
Lemma lem4360018 {A B C D : Type'} (h1 : term174 A B C D) : (term174 A B C D) = False.
Proof. exact (prop_ext (fun h2 : term174 A B C D => @lem4360017 A B C D h1) (fun h2 : False => @lem4357897 A B C D h1)). Qed.
Lemma lem4360019 {A B C D : Type'} (h1 : term174 A B C D) : False.
Proof. exact (EQ_MP (@lem4360018 A B C D h1) (@lem4357897 A B C D h1)). Qed.
Lemma lem4360020 {A B C D : Type'} : term173 A B C D.
Proof. exact (fun h0 : term174 A B C D => @lem4360019 A B C D h0). Qed.
Lemma lem4360021 {A B C D : Type'} : term171 A B C D.
Proof. exact (EQ_MP (@lem4357896 A B C D) (@lem4360020 A B C D)). Qed.
Lemma lem4360022 {A B C D : Type'} : term170 A B C D.
Proof. exact (EQ_MP (@lem4357892 A B C D) (@lem4360021 A B C D)). Qed.
