Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import IMAGE_FST_CROSS_term_abbrevs.
Require Import CONJ_SYM_spec.
Require Import CROSS_EMPTY_spec.
Require Import EXISTS_IN_CROSS_spec.
Require Import EXTENSION_spec.
Require Import IMAGE_CLAUSES_spec.
Require Import IN_IMAGE_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm13473_spec.
Require Import thm16433_spec.
Require Import thm16434_spec.
Require Import thm16439_spec.
Require Import thm16440_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm48219_spec.
Require Import thm48220_spec.
Lemma lem4354445 {_104151 _104152 : Type'} (P : type1223 _104151 _104152) : term0 _104151 _104152 P.
Proof. exact (@lem4334566 _104151 _104152 P). Qed.
Lemma lem4354446 {_104151 _104152 : Type'} (P : type1223 _104151 _104152) : (term0 _104151 _104152 P) = (term1 _104151 _104152 P).
Proof. exact (eq_refl (term0 _104151 _104152 P)). Qed.
Lemma lem4354447 {_104151 _104152 : Type'} (P : type1223 _104151 _104152) : term1 _104151 _104152 P.
Proof. exact (EQ_MP (@lem4354446 _104151 _104152 P) (@lem4354445 _104151 _104152 P)). Qed.
Lemma lem4354448 {_104151 _104152 : Type'} (P : type1223 _104151 _104152) (s : _104152 -> Prop) : term2 _104151 _104152 P s.
Proof. exact (@lem4354447 _104151 _104152 P s). Qed.
Lemma lem4354449 {_104151 _104152 : Type'} (s : _104152 -> Prop) (P : type1223 _104151 _104152) : (term2 _104151 _104152 P s) = (term3 _104151 _104152 s P).
Proof. exact (eq_refl (term2 _104151 _104152 P s)). Qed.
Lemma lem4354450 {_104151 _104152 : Type'} (s : _104152 -> Prop) (P : type1223 _104151 _104152) : term3 _104151 _104152 s P.
Proof. exact (EQ_MP (@lem4354449 _104151 _104152 s P) (@lem4354448 _104151 _104152 P s)). Qed.
Lemma lem4354451 {_104151 _104152 : Type'} (s : _104152 -> Prop) (P : type1223 _104151 _104152) (t : _104151 -> Prop) : term4 _104151 _104152 s P t.
Proof. exact (@lem4354450 _104151 _104152 s P t). Qed.
Lemma lem4354452 {_104151 _104152 : Type'} (s : _104152 -> Prop) (t : _104151 -> Prop) (P : type1223 _104151 _104152) : (term4 _104151 _104152 s P t) = ((term5 _104151 _104152 s t P) = (term6 _104151 _104152 s t P)).
Proof. exact (eq_refl (term4 _104151 _104152 s P t)). Qed.
Lemma lem4354454 (t1 : Prop) : term7 t1.
Proof. exact (@lem539 t1). Qed.
Lemma lem4354455 (t1 : Prop) : (term7 t1) = (term8 t1).
Proof. exact (eq_refl (term7 t1)). Qed.
Lemma lem4354456 (t1 : Prop) : term8 t1.
Proof. exact (EQ_MP (@lem4354455 t1) (@lem4354454 t1)). Qed.
Lemma lem4354457 (t1 : Prop) (t2 : Prop) : term9 t1 t2.
Proof. exact (@lem4354456 t1 t2). Qed.
Lemma lem4354458 (t2 : Prop) (t1 : Prop) : (term9 t1 t2) = ((t1 /\ t2) = (t2 /\ t1)).
Proof. exact (eq_refl (term9 t1 t2)). Qed.
Lemma lem4354460 {A B : Type'} (y : B) : term10 A B y.
Proof. exact (@lem3206070 A B y). Qed.
Lemma lem4354461 {A B : Type'} (y : B) : (term10 A B y) = (term11 A B y).
Proof. exact (eq_refl (term10 A B y)). Qed.
Lemma lem4354462 {A B : Type'} (y : B) : term11 A B y.
Proof. exact (EQ_MP (@lem4354461 A B y) (@lem4354460 A B y)). Qed.
Lemma lem4354463 {A B : Type'} (y : B) (s : A -> Prop) : term12 A B y s.
Proof. exact (@lem4354462 A B y s). Qed.
Lemma lem4354464 {A B : Type'} (y : B) (s : A -> Prop) : (term12 A B y s) = (term13 A B y s).
Proof. exact (eq_refl (term12 A B y s)). Qed.
Lemma lem4354465 {A B : Type'} (y : B) (s : A -> Prop) : term13 A B y s.
Proof. exact (EQ_MP (@lem4354464 A B y s) (@lem4354463 A B y s)). Qed.
Lemma lem4354466 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) : term14 A B y s f.
Proof. exact (@lem4354465 A B y s f). Qed.
Lemma lem4354467 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term14 A B y s f) = ((term15 A B y f s) = (term16 A B y f s)).
Proof. exact (eq_refl (term14 A B y s f)). Qed.
Lemma lem4354469 {A : Type'} (s : A -> Prop) : term17 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem4354470 {A : Type'} (s : A -> Prop) : (term17 A s) = (term18 A s).
Proof. exact (eq_refl (term17 A s)). Qed.
Lemma lem4354471 {A : Type'} (s : A -> Prop) : term18 A s.
Proof. exact (EQ_MP (@lem4354470 A s) (@lem4354469 A s)). Qed.
Lemma lem4354472 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term19 A s t.
Proof. exact (@lem4354471 A s t). Qed.
Lemma lem4354473 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term19 A s t) = ((s = t) = (term20 A s t)).
Proof. exact (eq_refl (term19 A s t)). Qed.
Lemma lem4354475 {A : Type'} (_474 : A -> Prop) (_475 : Prop) (_476 : type686 A) (_477 : A -> Prop) : (term21 A _476 _475 _474 _477) = (term22 A _474 _475 _476 _477).
Proof. exact (@lem13473 (A -> Prop) _474 _475 _476 _477). Qed.
Lemma lem4354476 {A B : Type'} (_474 : A -> Prop) (_475 : Prop) (s : A -> Prop) (t : B -> Prop) (_477 : A -> Prop) : (term23 A B s t _475 _474 _477) = (term24 A B _474 _475 s t _477).
Proof. exact (@lem4354475 A _474 _475 (term25 A B s t) _477). Qed.
Lemma lem4354477 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term26 A B t s) = (term27 A B t s).
Proof. exact (@lem4354476 A B (@EMPTY A) (t = (@EMPTY B)) s t s). Qed.
Lemma lem4354478 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term28 A B t s) = ((term29 A B s t) = s).
Proof. exact (eq_refl (term28 A B t s)). Qed.
Lemma lem4354479 {B : Type'} (t : B -> Prop) : (term30 B t) = (term30 B t).
Proof. exact (eq_refl (term30 B t)). Qed.
Lemma lem4354480 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term31 A B t s) = (term32 A B t s).
Proof. exact (MK_COMB (@lem4354479 B t) (@lem4354478 A B t s)). Qed.
Lemma lem4354481 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term33 A B s t) = ((term29 A B s t) = (@EMPTY A)).
Proof. exact (eq_refl (term33 A B s t)). Qed.
Lemma lem4354482 {B : Type'} (t : B -> Prop) : (term34 B t) = (term34 B t).
Proof. exact (eq_refl (term34 B t)). Qed.
Lemma lem4354483 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term35 A B s t) = (term36 A B s t).
Proof. exact (MK_COMB (@lem4354482 B t) (@lem4354481 A B s t)). Qed.
Lemma lem4354484 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4354485 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term37 A B s t) = (term38 A B s t).
Proof. exact (MK_COMB (@lem4354484) (@lem4354483 A B s t)). Qed.
Lemma lem4354486 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term27 A B t s) = (term39 A B t s).
Proof. exact (MK_COMB (@lem4354485 A B s t) (@lem4354480 A B t s)). Qed.
Lemma lem4354487 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term26 A B t s) = ((term29 A B s t) = (term40 A B t s)).
Proof. exact (eq_refl (term26 A B t s)). Qed.
Lemma lem4354488 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4354489 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term41 A B t s) = (term42 A B t s).
Proof. exact (MK_COMB (@lem4354488) (@lem4354487 A B t s)). Qed.
Lemma lem4354490 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : ((term26 A B t s) = (term27 A B t s)) = (((term29 A B s t) = (term40 A B t s)) = (term39 A B t s)).
Proof. exact (MK_COMB (@lem4354489 A B t s) (@lem4354486 A B t s)). Qed.
Lemma lem4354491 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : ((term29 A B s t) = (term40 A B t s)) = (term39 A B t s).
Proof. exact (EQ_MP (@lem4354490 A B t s) (@lem4354477 A B t s)). Qed.
Lemma lem4354492 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term39 A B t s) = ((term29 A B s t) = (term40 A B t s)).
Proof. exact (SYM (@lem4354491 A B t s)). Qed.
Lemma lem4354493 {B : Type'} (t : B -> Prop) (h1 : t = (@EMPTY B)) : t = (@EMPTY B).
Proof. exact (h1). Qed.
Lemma lem4354510 {B : Type'} (t : B -> Prop) (h1 : term43 B t) : term43 B t.
Proof. exact (h1). Qed.
Lemma lem4354533 {_103859 A : Type'} : term44 _103859 A.
Proof. exact (proj1 (@lem4327078 _103859 Prop A Prop)). Qed.
Lemma lem4354534 {_103859 A : Type'} (s : A -> Prop) : term45 _103859 A s.
Proof. exact (@lem4354533 _103859 A s). Qed.
Lemma lem4354535 {_103859 A : Type'} (s : A -> Prop) : (term45 _103859 A s) = ((@CROSS _103859 A s (@EMPTY _103859)) = (@EMPTY (prod A _103859))).
Proof. exact (eq_refl (term45 _103859 A s)). Qed.
Lemma lem4354540 {B : Type'} (t : B -> Prop) (h1 : t = (@EMPTY B)) : t = (@EMPTY B).
Proof. exact (h1). Qed.
Lemma lem4354541 {A B : Type'} (s : A -> Prop) : (@CROSS B A s) = (@CROSS B A s).
Proof. exact (eq_refl (@CROSS B A s)). Qed.
Lemma lem4354542 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : t = (@EMPTY B)) : (@CROSS B A s t) = (@CROSS B A s (@EMPTY B)).
Proof. exact (MK_COMB (@lem4354541 A B s) (@lem4354540 B t h1)). Qed.
Lemma lem4354544 {_103859 A : Type'} (s : A -> Prop) : (@CROSS _103859 A s (@EMPTY _103859)) = (@EMPTY (prod A _103859)).
Proof. exact (EQ_MP (@lem4354535 _103859 A s) (@lem4354534 _103859 A s)). Qed.
Lemma lem4354545 {A B : Type'} (s : A -> Prop) : (@CROSS B A s (@EMPTY B)) = (@EMPTY (prod A B)).
Proof. exact (@lem4354544 B A s). Qed.
Lemma lem4354546 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : t = (@EMPTY B)) : (@CROSS B A s t) = (@EMPTY (prod A B)).
Proof. exact (TRANS (@lem4354542 A B s t h1) (@lem4354545 A B s)). Qed.
Lemma lem4354547 {A B : Type'} : (@IMAGE (prod A B) A (@fst A B)) = (@IMAGE (prod A B) A (@fst A B)).
Proof. exact (eq_refl (@IMAGE (prod A B) A (@fst A B))). Qed.
Lemma lem4354548 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : t = (@EMPTY B)) : (term29 A B s t) = (@IMAGE (prod A B) A (@fst A B) (@EMPTY (prod A B))).
Proof. exact (MK_COMB (@lem4354547 A B) (@lem4354546 A B s t h1)). Qed.
Lemma lem4354550 {_87477 _87481 : Type'} (f : _87477 -> _87481) : (@IMAGE _87477 _87481 f (@EMPTY _87477)) = (@EMPTY _87481).
Proof. exact (proj1 (@lem3366870 _87477 _87481 (@el _87477) f (@el (_87477 -> Prop)))). Qed.
Lemma lem4354551 {A B : Type'} (f : type1207 A B) : (@IMAGE (prod A B) A f (@EMPTY (prod A B))) = (@EMPTY A).
Proof. exact (@lem4354550 (prod A B) A f). Qed.
Lemma lem4354552 {A B : Type'} : (@IMAGE (prod A B) A (@fst A B) (@EMPTY (prod A B))) = (@EMPTY A).
Proof. exact (@lem4354551 A B (@fst A B)). Qed.
Lemma lem4354553 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : t = (@EMPTY B)) : (term29 A B s t) = (@EMPTY A).
Proof. exact (TRANS (@lem4354548 A B s t h1) (@lem4354552 A B)). Qed.
Lemma lem4354554 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4354555 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : t = (@EMPTY B)) : (term46 A B s t) = (@eq (A -> Prop) (@EMPTY A)).
Proof. exact (MK_COMB (@lem4354554 A) (@lem4354553 A B s t h1)). Qed.
Lemma lem4354556 {A : Type'} : (@EMPTY A) = (@EMPTY A).
Proof. exact (eq_refl (@EMPTY A)). Qed.
Lemma lem4354557 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : t = (@EMPTY B)) : ((term29 A B s t) = (@EMPTY A)) = ((@EMPTY A) = (@EMPTY A)).
Proof. exact (MK_COMB (@lem4354555 A B s t h1) (@lem4354556 A)). Qed.
Lemma lem4354559 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4354560 {A : Type'} (x : A -> Prop) : (x = x) = True.
Proof. exact (@lem4354559 (A -> Prop) x). Qed.
Lemma lem4354561 {A : Type'} : ((@EMPTY A) = (@EMPTY A)) = True.
Proof. exact (@lem4354560 A (@EMPTY A)). Qed.
Lemma lem4354562 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : t = (@EMPTY B)) : ((term29 A B s t) = (@EMPTY A)) = True.
Proof. exact (TRANS (@lem4354557 A B s t h1) (@lem4354561 A)). Qed.
Lemma lem4354563 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : t = (@EMPTY B)) : True = ((term29 A B s t) = (@EMPTY A)).
Proof. exact (SYM (@lem4354562 A B s t h1)). Qed.
Lemma lem4354595 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term20 A s t).
Proof. exact (EQ_MP (@lem4354473 A s t) (@lem4354472 A s t)). Qed.
Lemma lem4354596 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term20 A s t).
Proof. exact (@lem4354595 A s t). Qed.
Lemma lem4354597 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : ((term29 A B s t) = s) = (term47 A B t s).
Proof. exact (@lem4354596 A (term29 A B s t) s). Qed.
Lemma lem4354607 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term15 A B y f s) = (term16 A B y f s).
Proof. exact (EQ_MP (@lem4354467 A B y f s) (@lem4354466 A B y s f)). Qed.
Lemma lem4354608 {A B : Type'} (y : A) (f : type1207 A B) (s : type1210 A B) : (term48 A B y f s) = (term49 A B y f s).
Proof. exact (@lem4354607 (prod A B) A y f s). Qed.
Lemma lem4354609 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) : (term50 A B x s t) = (term51 A B x s t).
Proof. exact (@lem4354608 A B x (@fst A B) (@CROSS B A s t)). Qed.
Lemma lem4354620 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4354621 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) : (term52 A B x s t) = (term53 A B x s t).
Proof. exact (MK_COMB (@lem4354620) (@lem4354609 A B x s t)). Qed.
Lemma lem4354622 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@IN A x s).
Proof. exact (eq_refl (@IN A x s)). Qed.
Lemma lem4354623 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) : ((term50 A B x s t) = (@IN A x s)) = ((term51 A B x s t) = (@IN A x s)).
Proof. exact (MK_COMB (@lem4354621 A B x s t) (@lem4354622 A x s)). Qed.
Lemma lem4354628 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term54 A B t s) = (term55 A B t s).
Proof. exact (fun_ext (fun x : A => @lem4354623 A B t x s)). Qed.
Lemma lem4354629 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4354630 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term47 A B t s) = (term56 A B t s).
Proof. exact (MK_COMB (@lem4354629 A) (@lem4354628 A B t s)). Qed.
Lemma lem4354635 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : ((term29 A B s t) = s) = (term56 A B t s).
Proof. exact (TRANS (@lem4354597 A B t s) (@lem4354630 A B t s)). Qed.
Lemma lem4354636 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term56 A B t s) = ((term29 A B s t) = s).
Proof. exact (SYM (@lem4354635 A B t s)). Qed.
Lemma lem4354650 (t2 : Prop) (t1 : Prop) : (t1 /\ t2) = (t2 /\ t1).
Proof. exact (EQ_MP (@lem4354458 t2 t1) (@lem4354457 t1 t2)). Qed.
Lemma lem4354651 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) (x' : prod A B) : (term57 A B x x' s t) = (term58 A B s t x x').
Proof. exact (@lem4354650 (term59 A B x' s t) (x = (@fst A B x'))). Qed.
Lemma lem4354652 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) : (term60 A B x s t) = (term61 A B s t x).
Proof. exact (fun_ext (fun x' : prod A B => @lem4354651 A B s t x x')). Qed.
Lemma lem4354653 {A B : Type'} : (@ex (prod A B)) = (@ex (prod A B)).
Proof. exact (eq_refl (@ex (prod A B))). Qed.
Lemma lem4354654 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) : (term51 A B x s t) = (term62 A B s t x).
Proof. exact (MK_COMB (@lem4354653 A B) (@lem4354652 A B s t x)). Qed.
Lemma lem4354655 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4354656 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) : (term53 A B x s t) = (term63 A B s t x).
Proof. exact (MK_COMB (@lem4354655) (@lem4354654 A B s t x)). Qed.
Lemma lem4354657 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@IN A x s).
Proof. exact (eq_refl (@IN A x s)). Qed.
Lemma lem4354658 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) : ((term51 A B x s t) = (@IN A x s)) = ((term62 A B s t x) = (@IN A x s)).
Proof. exact (MK_COMB (@lem4354656 A B s t x) (@lem4354657 A x s)). Qed.
Lemma lem4354659 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term55 A B t s) = (term64 A B t s).
Proof. exact (fun_ext (fun x : A => @lem4354658 A B t x s)). Qed.
Lemma lem4354660 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4354661 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term56 A B t s) = (term65 A B t s).
Proof. exact (MK_COMB (@lem4354660 A) (@lem4354659 A B t s)). Qed.
Lemma lem4354662 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term65 A B t s) = (term56 A B t s).
Proof. exact (SYM (@lem4354661 A B t s)). Qed.
Lemma lem4354670 {_104151 _104152 : Type'} (s : _104152 -> Prop) (t : _104151 -> Prop) (P : type1223 _104151 _104152) : (term5 _104151 _104152 s t P) = (term6 _104151 _104152 s t P).
Proof. exact (EQ_MP (@lem4354452 _104151 _104152 s t P) (@lem4354451 _104151 _104152 s P t)). Qed.
Lemma lem4354671 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (P : type1210 A B) : (term66 A B s t P) = (term67 A B s t P).
Proof. exact (@lem4354670 B A s t P). Qed.
Lemma lem4354672 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) : (term68 A B s t x) = (term69 A B s t x).
Proof. exact (@lem4354671 A B s t (term70 A B x)). Qed.
Lemma lem4354673 {A B : Type'} (x : A) (x' : prod A B) : (term71 A B x x') = (x = (@fst A B x')).
Proof. exact (eq_refl (term71 A B x x')). Qed.
Lemma lem4354674 {A B : Type'} (x : prod A B) (s : A -> Prop) (t : B -> Prop) : (term72 A B x s t) = (term72 A B x s t).
Proof. exact (eq_refl (term72 A B x s t)). Qed.
Lemma lem4354675 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) (x' : prod A B) : (term73 A B s t x x') = (term58 A B s t x x').
Proof. exact (MK_COMB (@lem4354674 A B x' s t) (@lem4354673 A B x x')). Qed.
Lemma lem4354676 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) : (term74 A B s t x) = (term61 A B s t x).
Proof. exact (fun_ext (fun x' : prod A B => @lem4354675 A B s t x x')). Qed.
Lemma lem4354677 {A B : Type'} : (@ex (prod A B)) = (@ex (prod A B)).
Proof. exact (eq_refl (@ex (prod A B))). Qed.
Lemma lem4354678 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) : (term68 A B s t x) = (term62 A B s t x).
Proof. exact (MK_COMB (@lem4354677 A B) (@lem4354676 A B s t x)). Qed.
Lemma lem4354679 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4354680 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) : (term75 A B s t x) = (term63 A B s t x).
Proof. exact (MK_COMB (@lem4354679) (@lem4354678 A B s t x)). Qed.
Lemma lem4354681 {A B : Type'} (x : A) (x' : A) (y : B) : (term76 A B x x' y) = (x = (term77 A B x' y)).
Proof. exact (eq_refl (term76 A B x x' y)). Qed.
Lemma lem4354682 {B : Type'} (y : B) (t : B -> Prop) : (term78 B y t) = (term78 B y t).
Proof. exact (eq_refl (term78 B y t)). Qed.
Lemma lem4354683 {A B : Type'} (t : B -> Prop) (x : A) (x' : A) (y : B) : (term79 A B t x x' y) = (term80 A B t x x' y).
Proof. exact (MK_COMB (@lem4354682 B y t) (@lem4354681 A B x x' y)). Qed.
Lemma lem4354684 {A : Type'} (x' : A) (s : A -> Prop) : (term78 A x' s) = (term78 A x' s).
Proof. exact (eq_refl (term78 A x' s)). Qed.
Lemma lem4354685 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) (x' : A) (y : B) : (term81 A B s t x x' y) = (term82 A B s t x x' y).
Proof. exact (MK_COMB (@lem4354684 A x' s) (@lem4354683 A B t x x' y)). Qed.
Lemma lem4354686 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) (x' : A) : (term83 A B s t x x') = (term84 A B s t x x').
Proof. exact (fun_ext (fun y : B => @lem4354685 A B s t x x' y)). Qed.
Lemma lem4354687 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4354688 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) (x' : A) : (term85 A B s t x x') = (term86 A B s t x x').
Proof. exact (MK_COMB (@lem4354687 B) (@lem4354686 A B s t x x')). Qed.
Lemma lem4354689 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) : (term87 A B s t x) = (term88 A B s t x).
Proof. exact (fun_ext (fun x' : A => @lem4354688 A B s t x x')). Qed.
Lemma lem4354690 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4354691 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) : (term69 A B s t x) = (term89 A B s t x).
Proof. exact (MK_COMB (@lem4354690 A) (@lem4354689 A B s t x)). Qed.
Lemma lem4354692 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) : ((term68 A B s t x) = (term69 A B s t x)) = ((term62 A B s t x) = (term89 A B s t x)).
Proof. exact (MK_COMB (@lem4354680 A B s t x) (@lem4354691 A B s t x)). Qed.
Lemma lem4354693 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) : (term62 A B s t x) = (term89 A B s t x).
Proof. exact (EQ_MP (@lem4354692 A B s t x) (@lem4354672 A B s t x)). Qed.
Lemma lem4354709 {A B : Type'} (y : B) (x : A) : (term77 A B x y) = x.
Proof. exact (EQ_MP (@lem48220 A B y x) (@lem48219 A B x y)). Qed.
Lemma lem4354710 {A B : Type'} (y : B) (x : A) : (term77 A B x y) = x.
Proof. exact (@lem4354709 A B y x). Qed.
Lemma lem4354711 {A B : Type'} (y : B) (x' : A) : (term77 A B x' y) = x'.
Proof. exact (@lem4354710 A B y x'). Qed.
Lemma lem4354712 {A : Type'} (x : A) : (@eq A x) = (@eq A x).
Proof. exact (eq_refl (@eq A x)). Qed.
Lemma lem4354713 {A B : Type'} (y : B) (x : A) (x' : A) : (x = (term77 A B x' y)) = (x = x').
Proof. exact (MK_COMB (@lem4354712 A x) (@lem4354711 A B y x')). Qed.
Lemma lem4354716 {B : Type'} (y : B) (t : B -> Prop) : (term78 B y t) = (term78 B y t).
Proof. exact (eq_refl (term78 B y t)). Qed.
Lemma lem4354717 {A B : Type'} (y : B) (t : B -> Prop) (x : A) (x' : A) : (term80 A B t x x' y) = (term90 A B y t x x').
Proof. exact (MK_COMB (@lem4354716 B y t) (@lem4354713 A B y x x')). Qed.
Lemma lem4354720 {A : Type'} (x' : A) (s : A -> Prop) : (term78 A x' s) = (term78 A x' s).
Proof. exact (eq_refl (term78 A x' s)). Qed.
Lemma lem4354721 {A B : Type'} (s : A -> Prop) (y : B) (t : B -> Prop) (x : A) (x' : A) : (term82 A B s t x x' y) = (term91 A B s y t x x').
Proof. exact (MK_COMB (@lem4354720 A x' s) (@lem4354717 A B y t x x')). Qed.
Lemma lem4354724 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) (x' : A) : (term84 A B s t x x') = (term92 A B s t x x').
Proof. exact (fun_ext (fun y : B => @lem4354721 A B s y t x x')). Qed.
Lemma lem4354725 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4354726 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) (x' : A) : (term86 A B s t x x') = (term93 A B s t x x').
Proof. exact (MK_COMB (@lem4354725 B) (@lem4354724 A B s t x x')). Qed.
Lemma lem4354731 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) : (term88 A B s t x) = (term94 A B s t x).
Proof. exact (fun_ext (fun x' : A => @lem4354726 A B s t x x')). Qed.
Lemma lem4354732 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4354733 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) : (term89 A B s t x) = (term95 A B s t x).
Proof. exact (MK_COMB (@lem4354732 A) (@lem4354731 A B s t x)). Qed.
Lemma lem4354738 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) : (term62 A B s t x) = (term95 A B s t x).
Proof. exact (TRANS (@lem4354693 A B s t x) (@lem4354733 A B s t x)). Qed.
Lemma lem4354739 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4354740 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) : (term63 A B s t x) = (term96 A B s t x).
Proof. exact (MK_COMB (@lem4354739) (@lem4354738 A B s t x)). Qed.
Lemma lem4354741 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@IN A x s).
Proof. exact (eq_refl (@IN A x s)). Qed.
Lemma lem4354742 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) : ((term62 A B s t x) = (@IN A x s)) = ((term95 A B s t x) = (@IN A x s)).
Proof. exact (MK_COMB (@lem4354740 A B s t x) (@lem4354741 A x s)). Qed.
Lemma lem4354745 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term64 A B t s) = (term97 A B t s).
Proof. exact (fun_ext (fun x : A => @lem4354742 A B t x s)). Qed.
Lemma lem4354746 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4354747 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term65 A B t s) = (term98 A B t s).
Proof. exact (MK_COMB (@lem4354746 A) (@lem4354745 A B t s)). Qed.
Lemma lem4354752 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term98 A B t s) = (term65 A B t s).
Proof. exact (SYM (@lem4354747 A B t s)). Qed.
Lemma lem4354768 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term20 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem4354769 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (s = t) = (term20 B s t).
Proof. exact (@lem4354768 B s t). Qed.
Lemma lem4354770 {B : Type'} (t : B -> Prop) : (t = (@EMPTY B)) = (term99 B t).
Proof. exact (@lem4354769 B t (@EMPTY B)). Qed.
Lemma lem4354779 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4354780 {B : Type'} (t : B -> Prop) : (term43 B t) = (term100 B t).
Proof. exact (MK_COMB (@lem4354779) (@lem4354770 B t)). Qed.
Lemma lem4354781 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4354782 {B : Type'} (t : B -> Prop) : (term30 B t) = (term101 B t).
Proof. exact (MK_COMB (@lem4354781) (@lem4354780 B t)). Qed.
Lemma lem4354807 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term98 A B t s) = (term98 A B t s).
Proof. exact (eq_refl (term98 A B t s)). Qed.
Lemma lem4354808 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term102 A B t s) = (term103 A B t s).
Proof. exact (MK_COMB (@lem4354782 B t) (@lem4354807 A B t s)). Qed.
Lemma lem4354811 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term103 A B t s) = (term102 A B t s).
Proof. exact (SYM (@lem4354808 A B t s)). Qed.
Lemma lem4354821 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4354822 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem4354821 B P x). Qed.
Lemma lem4354823 {B : Type'} (t : B -> Prop) (x : B) : (@IN B x t) = (t x).
Proof. exact (@lem4354822 B t x). Qed.
Lemma lem4354824 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4354825 {B : Type'} (t : B -> Prop) (x : B) : (term104 B x t) = (term105 B t x).
Proof. exact (MK_COMB (@lem4354824) (@lem4354823 B t x)). Qed.
Lemma lem4354827 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem4354828 {B : Type'} (x : B) : (@IN B x (@EMPTY B)) = False.
Proof. exact (@lem4354827 B x). Qed.
Lemma lem4354829 {B : Type'} (t : B -> Prop) (x : B) : ((@IN B x t) = (@IN B x (@EMPTY B))) = ((t x) = False).
Proof. exact (MK_COMB (@lem4354825 B t x) (@lem4354828 B x)). Qed.
Lemma lem4354831 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem4354832 {B : Type'} (t : B -> Prop) (x : B) : ((t x) = False) = (term106 B t x).
Proof. exact (@lem4354831 (t x)). Qed.
Lemma lem4354833 {B : Type'} (t : B -> Prop) (x : B) : ((@IN B x t) = (@IN B x (@EMPTY B))) = (term106 B t x).
Proof. exact (TRANS (@lem4354829 B t x) (@lem4354832 B t x)). Qed.
Lemma lem4354834 {B : Type'} (t : B -> Prop) : (term107 B t) = (term108 B t).
Proof. exact (fun_ext (fun x : B => @lem4354833 B t x)). Qed.
Lemma lem4354835 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4354836 {B : Type'} (t : B -> Prop) : (term99 B t) = (term109 B t).
Proof. exact (MK_COMB (@lem4354835 B) (@lem4354834 B t)). Qed.
Lemma lem4354841 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4354842 {B : Type'} (t : B -> Prop) : (term100 B t) = (term110 B t).
Proof. exact (MK_COMB (@lem4354841) (@lem4354836 B t)). Qed.
Lemma lem4354843 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4354844 {B : Type'} (t : B -> Prop) : (term101 B t) = (term111 B t).
Proof. exact (MK_COMB (@lem4354843) (@lem4354842 B t)). Qed.
Lemma lem4354862 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4354863 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4354862 A P x). Qed.
Lemma lem4354864 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem4354863 A s x'). Qed.
Lemma lem4354865 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4354866 {A : Type'} (s : A -> Prop) (x' : A) : (term78 A x' s) = (term112 A s x').
Proof. exact (MK_COMB (@lem4354865) (@lem4354864 A s x')). Qed.
Lemma lem4354870 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4354871 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem4354870 B P x). Qed.
Lemma lem4354872 {B : Type'} (t : B -> Prop) (y : B) : (@IN B y t) = (t y).
Proof. exact (@lem4354871 B t y). Qed.
Lemma lem4354873 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4354874 {B : Type'} (t : B -> Prop) (y : B) : (term78 B y t) = (term112 B t y).
Proof. exact (MK_COMB (@lem4354873) (@lem4354872 B t y)). Qed.
Lemma lem4354877 {A : Type'} (x : A) (x' : A) : (x = x') = (x = x').
Proof. exact (eq_refl (x = x')). Qed.
Lemma lem4354878 {A B : Type'} (t : B -> Prop) (y : B) (x : A) (x' : A) : (term90 A B y t x x') = (term113 A B t y x x').
Proof. exact (MK_COMB (@lem4354874 B t y) (@lem4354877 A x x')). Qed.
Lemma lem4354881 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (y : B) (x : A) (x' : A) : (term91 A B s y t x x') = (term114 A B s t y x x').
Proof. exact (MK_COMB (@lem4354866 A s x') (@lem4354878 A B t y x x')). Qed.
Lemma lem4354884 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) (x' : A) : (term92 A B s t x x') = (term115 A B s t x x').
Proof. exact (fun_ext (fun y : B => @lem4354881 A B s t y x x')). Qed.
Lemma lem4354885 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4354886 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) (x' : A) : (term93 A B s t x x') = (term116 A B s t x x').
Proof. exact (MK_COMB (@lem4354885 B) (@lem4354884 A B s t x x')). Qed.
Lemma lem4354891 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) : (term94 A B s t x) = (term117 A B s t x).
Proof. exact (fun_ext (fun x' : A => @lem4354886 A B s t x x')). Qed.
Lemma lem4354892 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4354893 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) : (term95 A B s t x) = (term118 A B s t x).
Proof. exact (MK_COMB (@lem4354892 A) (@lem4354891 A B s t x)). Qed.
Lemma lem4354898 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4354899 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) : (term96 A B s t x) = (term119 A B s t x).
Proof. exact (MK_COMB (@lem4354898) (@lem4354893 A B s t x)). Qed.
Lemma lem4354901 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4354902 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4354901 A P x). Qed.
Lemma lem4354903 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4354902 A s x). Qed.
Lemma lem4354904 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) : ((term95 A B s t x) = (@IN A x s)) = ((term118 A B s t x) = (s x)).
Proof. exact (MK_COMB (@lem4354899 A B s t x) (@lem4354903 A s x)). Qed.
Lemma lem4354907 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term97 A B t s) = (term120 A B t s).
Proof. exact (fun_ext (fun x : A => @lem4354904 A B t s x)). Qed.
Lemma lem4354908 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4354909 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term98 A B t s) = (term121 A B t s).
Proof. exact (MK_COMB (@lem4354908 A) (@lem4354907 A B t s)). Qed.
Lemma lem4354914 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term103 A B t s) = (term122 A B t s).
Proof. exact (MK_COMB (@lem4354844 B t) (@lem4354909 A B t s)). Qed.
Lemma lem4354917 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term122 A B t s) = (term103 A B t s).
Proof. exact (SYM (@lem4354914 A B t s)). Qed.
Lemma lem4354919 (p : Prop) : p = (term123 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4354920 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term122 A B t s) = (term124 A B t s).
Proof. exact (@lem4354919 (term122 A B t s)). Qed.
Lemma lem4354921 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term124 A B t s) = (term122 A B t s).
Proof. exact (SYM (@lem4354920 A B t s)). Qed.
Lemma lem4354922 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term125 A B t s) : term125 A B t s.
Proof. exact (h1). Qed.
Lemma lem4354925 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term124 A B t s) : term124 A B t s.
Proof. exact (h1). Qed.
Lemma lem4354926 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : term126 A B t s.
Proof. exact (fun h0 : term124 A B t s => @lem4354925 A B t s h0). Qed.
Lemma lem4354927 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term126 A B t s) : term126 A B t s.
Proof. exact (h1). Qed.
Lemma lem4354928 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term124 A B t s) : term124 A B t s.
Proof. exact (h1). Qed.
Lemma lem4354929 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term124 A B t s) (h2 : term126 A B t s) : term124 A B t s.
Proof. exact (@lem4354927 A B t s h2 (@lem4354928 A B t s h1)). Qed.
Lemma lem4354930 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term124 A B t s) : term127 A B t s.
Proof. exact (fun h0 : term126 A B t s => @lem4354929 A B t s h1 h0). Qed.
Lemma lem4354931 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term126 A B t s) : term126 A B t s.
Proof. exact (h1). Qed.
Lemma lem4354932 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term124 A B t s) (h2 : term126 A B t s) : term124 A B t s.
Proof. exact (@lem4354930 A B t s h1 (@lem4354931 A B t s h2)). Qed.
Lemma lem4354933 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term126 A B t s) : term126 A B t s.
Proof. exact (fun h0 : term124 A B t s => @lem4354932 A B t s h0 h1). Qed.
Lemma lem4354934 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : term128 A B t s.
Proof. exact (fun h0 : term126 A B t s => @lem4354933 A B t s h0). Qed.
Lemma lem4354937 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : term126 A B t s.
Proof. exact (@lem4354934 A B t s (@lem4354926 A B t s)). Qed.
Lemma lem4354938 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : term126 A B t s.
Proof. exact (@lem4354937 A B t s). Qed.
Lemma lem4354948 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4354949 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term124 A B t s) = (term129 A B t s).
Proof. exact (@lem4354948 (term125 A B t s)). Qed.
Lemma lem4354951 (t : Prop) : (term130 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4354952 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term129 A B t s) = (term122 A B t s).
Proof. exact (@lem4354951 (term122 A B t s)). Qed.
Lemma lem4354955 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term124 A B t s) = (term122 A B t s).
Proof. exact (TRANS (@lem4354949 A B t s) (@lem4354952 A B t s)). Qed.
Lemma lem4354969 {A : Type'} (P : Prop) (Q : A -> Prop) : (term131 A P Q) = (term132 A P Q).
Proof. exact (EQ_MP (@lem16434 A P Q) (@lem16433 A P Q)). Qed.
Lemma lem4354970 {B : Type'} (P : Prop) (Q : B -> Prop) : (term131 B P Q) = (term132 B P Q).
Proof. exact (@lem4354969 B P Q). Qed.
Lemma lem4354971 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) (x' : A) : (term133 A B s t x x') = (term134 A B s t x x').
Proof. exact (@lem4354970 B (s x') (term135 A B t x x')). Qed.
Lemma lem4354972 {A B : Type'} (t : B -> Prop) (y : B) (x : A) (x' : A) : (term136 A B t x x' y) = (term113 A B t y x x').
Proof. exact (eq_refl (term136 A B t x x' y)). Qed.
Lemma lem4354973 {A : Type'} (s : A -> Prop) (x' : A) : (term112 A s x') = (term112 A s x').
Proof. exact (eq_refl (term112 A s x')). Qed.
Lemma lem4354974 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (y : B) (x : A) (x' : A) : (term137 A B s t x x' y) = (term114 A B s t y x x').
Proof. exact (MK_COMB (@lem4354973 A s x') (@lem4354972 A B t y x x')). Qed.
Lemma lem4354975 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) (x' : A) : (term138 A B s t x x') = (term115 A B s t x x').
Proof. exact (fun_ext (fun y : B => @lem4354974 A B s t y x x')). Qed.
Lemma lem4354976 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4354977 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) (x' : A) : (term133 A B s t x x') = (term116 A B s t x x').
Proof. exact (MK_COMB (@lem4354976 B) (@lem4354975 A B s t x x')). Qed.
Lemma lem4354978 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4354979 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) (x' : A) : (term139 A B s t x x') = (term140 A B s t x x').
Proof. exact (MK_COMB (@lem4354978) (@lem4354977 A B s t x x')). Qed.
Lemma lem4354980 {A B : Type'} (t : B -> Prop) (y : B) (x : A) (x' : A) : (term136 A B t x x' y) = (term113 A B t y x x').
Proof. exact (eq_refl (term136 A B t x x' y)). Qed.
Lemma lem4354981 {A B : Type'} (t : B -> Prop) (x : A) (x' : A) : (term141 A B t x x') = (term135 A B t x x').
Proof. exact (fun_ext (fun y : B => @lem4354980 A B t y x x')). Qed.
Lemma lem4354982 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4354983 {A B : Type'} (t : B -> Prop) (x : A) (x' : A) : (term142 A B t x x') = (term143 A B t x x').
Proof. exact (MK_COMB (@lem4354982 B) (@lem4354981 A B t x x')). Qed.
Lemma lem4354984 {A : Type'} (s : A -> Prop) (x' : A) : (term112 A s x') = (term112 A s x').
Proof. exact (eq_refl (term112 A s x')). Qed.
Lemma lem4354985 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) (x' : A) : (term134 A B s t x x') = (term144 A B s t x x').
Proof. exact (MK_COMB (@lem4354984 A s x') (@lem4354983 A B t x x')). Qed.
Lemma lem4354986 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) (x' : A) : ((term133 A B s t x x') = (term134 A B s t x x')) = ((term116 A B s t x x') = (term144 A B s t x x')).
Proof. exact (MK_COMB (@lem4354979 A B s t x x') (@lem4354985 A B s t x x')). Qed.
Lemma lem4354987 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) (x' : A) : (term116 A B s t x x') = (term144 A B s t x x').
Proof. exact (EQ_MP (@lem4354986 A B s t x x') (@lem4354971 A B s t x x')). Qed.
Lemma lem4355011 {A : Type'} (P : A -> Prop) (Q : Prop) : (term145 A P Q) = (term146 A P Q).
Proof. exact (EQ_MP (@lem16440 A P Q) (@lem16439 A P Q)). Qed.
Lemma lem4355012 {B : Type'} (P : B -> Prop) (Q : Prop) : (term145 B P Q) = (term146 B P Q).
Proof. exact (@lem4355011 B P Q). Qed.
Lemma lem4355013 {A B : Type'} (t : B -> Prop) (x : A) (x' : A) : (term143 A B t x x') = (term147 A B t x x').
Proof. exact (@lem4355012 B t (x = x')). Qed.
Lemma lem4355020 {A : Type'} (s : A -> Prop) (x' : A) : (term112 A s x') = (term112 A s x').
Proof. exact (eq_refl (term112 A s x')). Qed.
Lemma lem4355021 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) (x' : A) : (term144 A B s t x x') = (term148 A B s t x x').
Proof. exact (MK_COMB (@lem4355020 A s x') (@lem4355013 A B t x x')). Qed.
Lemma lem4355024 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) (x' : A) : (term116 A B s t x x') = (term148 A B s t x x').
Proof. exact (TRANS (@lem4354987 A B s t x x') (@lem4355021 A B s t x x')). Qed.
Lemma lem4355025 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) : (term117 A B s t x) = (term149 A B s t x).
Proof. exact (fun_ext (fun x' : A => @lem4355024 A B s t x x')). Qed.
Lemma lem4355026 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4355027 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) : (term118 A B s t x) = (term150 A B s t x).
Proof. exact (MK_COMB (@lem4355026 A) (@lem4355025 A B s t x)). Qed.
Lemma lem4355056 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4355057 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) : (term119 A B s t x) = (term151 A B s t x).
Proof. exact (MK_COMB (@lem4355056) (@lem4355027 A B s t x)). Qed.
Lemma lem4355058 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem4355059 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) : ((term118 A B s t x) = (s x)) = ((term150 A B s t x) = (s x)).
Proof. exact (MK_COMB (@lem4355057 A B s t x) (@lem4355058 A s x)). Qed.
Lemma lem4355060 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term120 A B t s) = (term152 A B t s).
Proof. exact (fun_ext (fun x : A => @lem4355059 A B t s x)). Qed.
Lemma lem4355061 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4355062 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term121 A B t s) = (term153 A B t s).
Proof. exact (MK_COMB (@lem4355061 A) (@lem4355060 A B t s)). Qed.
Lemma lem4355067 {B : Type'} (t : B -> Prop) : (term111 B t) = (term111 B t).
Proof. exact (eq_refl (term111 B t)). Qed.
Lemma lem4355068 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term122 A B t s) = (term154 A B t s).
Proof. exact (MK_COMB (@lem4355067 B t) (@lem4355062 A B t s)). Qed.
Lemma lem4355071 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term124 A B t s) = (term154 A B t s).
Proof. exact (TRANS (@lem4354955 A B t s) (@lem4355068 A B t s)). Qed.
Lemma lem4355072 {A B : Type'} (s : A -> Prop) : (term155 A B s) = (term156 A B s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem4355071 A B t s)). Qed.
Lemma lem4355073 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4355074 {A B : Type'} (s : A -> Prop) : (term157 A B s) = (term158 A B s).
Proof. exact (MK_COMB (@lem4355073 B) (@lem4355072 A B s)). Qed.
Lemma lem4355079 {A B : Type'} : (term159 A B) = (term160 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4355074 A B s)). Qed.
Lemma lem4355080 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4355089 {A B : Type'} : (term161 A B) = (term162 A B).
Proof. exact (MK_COMB (@lem4355080 A) (@lem4355079 A B)). Qed.
Lemma lem4355090 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem4355091 {A : Type'} (x : A) (x' : A) : (x = x') = (x = x').
Proof. exact (eq_refl (x = x')). Qed.
Lemma lem4355092 {B : Type'} (t : B -> Prop) (y : B) : (t y) = (t y).
Proof. exact (eq_refl (t y)). Qed.
Lemma lem4355093 {B : Type'} (t : B -> Prop) : (term163 B t) = (term163 B t).
Proof. exact (fun_ext (fun y : B => @lem4355092 B t y)). Qed.
Lemma lem4355094 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4355095 {B : Type'} (t : B -> Prop) : (term164 B t) = (term164 B t).
Proof. exact (MK_COMB (@lem4355094 B) (@lem4355093 B t)). Qed.
Lemma lem4355096 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4355097 {B : Type'} (t : B -> Prop) : (term165 B t) = (term165 B t).
Proof. exact (MK_COMB (@lem4355096) (@lem4355095 B t)). Qed.
Lemma lem4355098 {A B : Type'} (t : B -> Prop) (x : A) (x' : A) : (term147 A B t x x') = (term147 A B t x x').
Proof. exact (MK_COMB (@lem4355097 B t) (@lem4355091 A x x')). Qed.
Lemma lem4355101 {A : Type'} (s : A -> Prop) (x' : A) : (term112 A s x') = (term112 A s x').
Proof. exact (eq_refl (term112 A s x')). Qed.
Lemma lem4355102 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) (x' : A) : (term148 A B s t x x') = (term148 A B s t x x').
Proof. exact (MK_COMB (@lem4355101 A s x') (@lem4355098 A B t x x')). Qed.
Lemma lem4355103 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) : (term149 A B s t x) = (term149 A B s t x).
Proof. exact (fun_ext (fun x' : A => @lem4355102 A B s t x x')). Qed.
Lemma lem4355104 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4355105 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) : (term150 A B s t x) = (term150 A B s t x).
Proof. exact (MK_COMB (@lem4355104 A) (@lem4355103 A B s t x)). Qed.
Lemma lem4355106 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4355107 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) : (term151 A B s t x) = (term151 A B s t x).
Proof. exact (MK_COMB (@lem4355106) (@lem4355105 A B s t x)). Qed.
Lemma lem4355108 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) : ((term150 A B s t x) = (s x)) = ((term150 A B s t x) = (s x)).
Proof. exact (MK_COMB (@lem4355107 A B s t x) (@lem4355090 A s x)). Qed.
Lemma lem4355109 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term152 A B t s) = (term152 A B t s).
Proof. exact (fun_ext (fun x : A => @lem4355108 A B t s x)). Qed.
Lemma lem4355110 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4355111 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term153 A B t s) = (term153 A B t s).
Proof. exact (MK_COMB (@lem4355110 A) (@lem4355109 A B t s)). Qed.
Lemma lem4355114 {B : Type'} (t : B -> Prop) (x : B) : (term106 B t x) = (term106 B t x).
Proof. exact (eq_refl (term106 B t x)). Qed.
Lemma lem4355115 {B : Type'} (t : B -> Prop) : (term108 B t) = (term108 B t).
Proof. exact (fun_ext (fun x : B => @lem4355114 B t x)). Qed.
Lemma lem4355116 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4355117 {B : Type'} (t : B -> Prop) : (term109 B t) = (term109 B t).
Proof. exact (MK_COMB (@lem4355116 B) (@lem4355115 B t)). Qed.
Lemma lem4355118 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4355119 {B : Type'} (t : B -> Prop) : (term110 B t) = (term110 B t).
Proof. exact (MK_COMB (@lem4355118) (@lem4355117 B t)). Qed.
Lemma lem4355120 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4355121 {B : Type'} (t : B -> Prop) : (term111 B t) = (term111 B t).
Proof. exact (MK_COMB (@lem4355120) (@lem4355119 B t)). Qed.
Lemma lem4355122 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term154 A B t s) = (term154 A B t s).
Proof. exact (MK_COMB (@lem4355121 B t) (@lem4355111 A B t s)). Qed.
Lemma lem4355123 {A B : Type'} (s : A -> Prop) : (term156 A B s) = (term156 A B s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem4355122 A B t s)). Qed.
Lemma lem4355124 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4355125 {A B : Type'} (s : A -> Prop) : (term158 A B s) = (term158 A B s).
Proof. exact (MK_COMB (@lem4355124 B) (@lem4355123 A B s)). Qed.
Lemma lem4355126 {A B : Type'} : (term160 A B) = (term160 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4355125 A B s)). Qed.
Lemma lem4355127 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4355128 {A B : Type'} : (term162 A B) = (term162 A B).
Proof. exact (MK_COMB (@lem4355127 A) (@lem4355126 A B)). Qed.
Lemma lem4355173 {A B : Type'} : (term161 A B) = (term162 A B).
Proof. exact (TRANS (@lem4355089 A B) (@lem4355128 A B)). Qed.
Lemma lem4355174 {A B : Type'} : (term162 A B) = (term161 A B).
Proof. exact (SYM (@lem4355173 A B)). Qed.
Lemma lem4355175 {B : Type'} (t : B -> Prop) (h1 : term110 B t) : term110 B t.
Proof. exact (h1). Qed.
Lemma lem4355177 (p : Prop) : p = (term123 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4355178 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) : ((term150 A B s t x) = (s x)) = (term166 A B t s x).
Proof. exact (@lem4355177 ((term150 A B s t x) = (s x))). Qed.
Lemma lem4355179 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) : (term166 A B t s x) = ((term150 A B s t x) = (s x)).
Proof. exact (SYM (@lem4355178 A B t s x)). Qed.
Lemma lem4355180 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) (h1 : term167 A B t s x) : term167 A B t s x.
Proof. exact (h1). Qed.
Lemma lem4355183 {B : Type'} (t : B -> Prop) (x : B) : (term168 B t x) = (t x).
Proof. exact (@lem16933 (t x)). Qed.
Lemma lem4355184 {B : Type'} (P : B -> Prop) : (term169 B P) = (term170 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem4355185 {B : Type'} (t : B -> Prop) : (term110 B t) = (term171 B t).
Proof. exact (@lem4355184 B (term108 B t)). Qed.
Lemma lem4355186 {B : Type'} (t : B -> Prop) (x : B) : (term172 B t x) = (term106 B t x).
Proof. exact (eq_refl (term172 B t x)). Qed.
Lemma lem4355187 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4355188 {B : Type'} (t : B -> Prop) (x : B) : (term173 B t x) = (term168 B t x).
Proof. exact (MK_COMB (@lem4355187) (@lem4355186 B t x)). Qed.
Lemma lem4355189 {B : Type'} (t : B -> Prop) (x : B) : (term173 B t x) = (t x).
Proof. exact (TRANS (@lem4355188 B t x) (@lem4355183 B t x)). Qed.
Lemma lem4355190 {B : Type'} (t : B -> Prop) : (term174 B t) = (term163 B t).
Proof. exact (fun_ext (fun x : B => @lem4355189 B t x)). Qed.
Lemma lem4355191 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4355192 {B : Type'} (t : B -> Prop) : (term171 B t) = (term164 B t).
Proof. exact (MK_COMB (@lem4355191 B) (@lem4355190 B t)). Qed.
Lemma lem4355201 {B : Type'} (t : B -> Prop) : (term110 B t) = (term164 B t).
Proof. exact (TRANS (@lem4355185 B t) (@lem4355192 B t)). Qed.
Lemma lem4355202 {B : Type'} (t : B -> Prop) (h1 : term110 B t) : term164 B t.
Proof. exact (EQ_MP (@lem4355201 B t) (@lem4355175 B t h1)). Qed.
Lemma lem4355206 {B : Type'} (t : B -> Prop) (y : B) : (t y) = (t y).
Proof. exact (eq_refl (t y)). Qed.
Lemma lem4355207 {B : Type'} (P : B -> Prop) : (term175 B P) = (term109 B P).
Proof. exact (@lem18394 B P). Qed.
Lemma lem4355208 {B : Type'} (t : B -> Prop) : (term176 B t) = (term177 B t).
Proof. exact (@lem4355207 B (term163 B t)). Qed.
Lemma lem4355209 {B : Type'} (t : B -> Prop) (y : B) : (term178 B t y) = (t y).
Proof. exact (eq_refl (term178 B t y)). Qed.
Lemma lem4355210 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4355212 {B : Type'} (t : B -> Prop) (y : B) : (term179 B t y) = (term106 B t y).
Proof. exact (MK_COMB (@lem4355210) (@lem4355209 B t y)). Qed.
Lemma lem4355213 {B : Type'} (t : B -> Prop) : (term180 B t) = (term108 B t).
Proof. exact (fun_ext (fun y : B => @lem4355212 B t y)). Qed.
Lemma lem4355214 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4355215 {B : Type'} (t : B -> Prop) : (term177 B t) = (term109 B t).
Proof. exact (MK_COMB (@lem4355214 B) (@lem4355213 B t)). Qed.
Lemma lem4355216 {B : Type'} (t : B -> Prop) : (term176 B t) = (term109 B t).
Proof. exact (TRANS (@lem4355208 B t) (@lem4355215 B t)). Qed.
Lemma lem4355217 {B : Type'} (t : B -> Prop) : (term163 B t) = (term163 B t).
Proof. exact (fun_ext (fun y : B => @lem4355206 B t y)). Qed.
Lemma lem4355218 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4355219 {B : Type'} (t : B -> Prop) : (term164 B t) = (term164 B t).
Proof. exact (MK_COMB (@lem4355218 B) (@lem4355217 B t)). Qed.
Lemma lem4355220 {A : Type'} (x : A) (x' : A) : (term181 A x x') = (term181 A x x').
Proof. exact (eq_refl (term181 A x x')). Qed.
Lemma lem4355221 {A : Type'} (x : A) (x' : A) : (x = x') = (x = x').
Proof. exact (eq_refl (x = x')). Qed.
Lemma lem4355222 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4355223 {B : Type'} (t : B -> Prop) : (term182 B t) = (term183 B t).
Proof. exact (MK_COMB (@lem4355222) (@lem4355216 B t)). Qed.
Lemma lem4355224 {A B : Type'} (t : B -> Prop) (x : A) (x' : A) : (term184 A B t x x') = (term185 A B t x x').
Proof. exact (MK_COMB (@lem4355223 B t) (@lem4355220 A x x')). Qed.
Lemma lem4355225 {A B : Type'} (t : B -> Prop) (x : A) (x' : A) : (term186 A B t x x') = (term184 A B t x x').
Proof. exact (@lem17045 (term164 B t) (x = x')). Qed.
Lemma lem4355226 {A B : Type'} (t : B -> Prop) (x : A) (x' : A) : (term186 A B t x x') = (term185 A B t x x').
Proof. exact (TRANS (@lem4355225 A B t x x') (@lem4355224 A B t x x')). Qed.
Lemma lem4355227 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4355228 {B : Type'} (t : B -> Prop) : (term165 B t) = (term165 B t).
Proof. exact (MK_COMB (@lem4355227) (@lem4355219 B t)). Qed.
Lemma lem4355229 {A B : Type'} (t : B -> Prop) (x : A) (x' : A) : (term147 A B t x x') = (term147 A B t x x').
Proof. exact (MK_COMB (@lem4355228 B t) (@lem4355221 A x x')). Qed.
Lemma lem4355231 {A : Type'} (s : A -> Prop) (x' : A) : (term187 A s x') = (term187 A s x').
Proof. exact (eq_refl (term187 A s x')). Qed.
Lemma lem4355232 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) (x' : A) : (term188 A B s t x x') = (term189 A B s t x x').
Proof. exact (MK_COMB (@lem4355231 A s x') (@lem4355226 A B t x x')). Qed.
Lemma lem4355233 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) (x' : A) : (term190 A B s t x x') = (term188 A B s t x x').
Proof. exact (@lem17045 (s x') (term147 A B t x x')). Qed.
Lemma lem4355234 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) (x' : A) : (term190 A B s t x x') = (term189 A B s t x x').
Proof. exact (TRANS (@lem4355233 A B s t x x') (@lem4355232 A B s t x x')). Qed.
Lemma lem4355236 {A : Type'} (s : A -> Prop) (x' : A) : (term112 A s x') = (term112 A s x').
Proof. exact (eq_refl (term112 A s x')). Qed.
Lemma lem4355237 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) (x' : A) : (term148 A B s t x x') = (term148 A B s t x x').
Proof. exact (MK_COMB (@lem4355236 A s x') (@lem4355229 A B t x x')). Qed.
Lemma lem4355238 {A : Type'} (P : A -> Prop) : (term175 A P) = (term109 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem4355239 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) : (term191 A B s t x) = (term192 A B s t x).
Proof. exact (@lem4355238 A (term149 A B s t x)). Qed.
Lemma lem4355240 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) (x' : A) : (term193 A B s t x x') = (term148 A B s t x x').
Proof. exact (eq_refl (term193 A B s t x x')). Qed.
Lemma lem4355241 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4355242 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) (x' : A) : (term194 A B s t x x') = (term190 A B s t x x').
Proof. exact (MK_COMB (@lem4355241) (@lem4355240 A B s t x x')). Qed.
Lemma lem4355243 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) (x' : A) : (term194 A B s t x x') = (term189 A B s t x x').
Proof. exact (TRANS (@lem4355242 A B s t x x') (@lem4355234 A B s t x x')). Qed.
Lemma lem4355244 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) : (term195 A B s t x) = (term196 A B s t x).
Proof. exact (fun_ext (fun x' : A => @lem4355243 A B s t x x')). Qed.
Lemma lem4355245 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4355246 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) : (term192 A B s t x) = (term197 A B s t x).
Proof. exact (MK_COMB (@lem4355245 A) (@lem4355244 A B s t x)). Qed.
Lemma lem4355247 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) : (term191 A B s t x) = (term197 A B s t x).
Proof. exact (TRANS (@lem4355239 A B s t x) (@lem4355246 A B s t x)). Qed.
Lemma lem4355248 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) : (term149 A B s t x) = (term149 A B s t x).
Proof. exact (fun_ext (fun x' : A => @lem4355237 A B s t x x')). Qed.
Lemma lem4355249 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4355250 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) : (term150 A B s t x) = (term150 A B s t x).
Proof. exact (MK_COMB (@lem4355249 A) (@lem4355248 A B s t x)). Qed.
Lemma lem4355251 {A : Type'} (s : A -> Prop) (x : A) : (term106 A s x) = (term106 A s x).
Proof. exact (eq_refl (term106 A s x)). Qed.
Lemma lem4355252 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem4355253 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4355254 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) : (term198 A B s t x) = (term199 A B s t x).
Proof. exact (MK_COMB (@lem4355253) (@lem4355247 A B s t x)). Qed.
Lemma lem4355255 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) : (term200 A B t s x) = (term201 A B t s x).
Proof. exact (MK_COMB (@lem4355254 A B s t x) (@lem4355252 A s x)). Qed.
Lemma lem4355256 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4355257 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) : (term202 A B s t x) = (term202 A B s t x).
Proof. exact (MK_COMB (@lem4355256) (@lem4355250 A B s t x)). Qed.
Lemma lem4355258 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) : (term203 A B t s x) = (term203 A B t s x).
Proof. exact (MK_COMB (@lem4355257 A B s t x) (@lem4355251 A s x)). Qed.
Lemma lem4355259 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4355260 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) : (term204 A B t s x) = (term204 A B t s x).
Proof. exact (MK_COMB (@lem4355259) (@lem4355258 A B t s x)). Qed.
Lemma lem4355261 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) : (term205 A B t s x) = (term206 A B t s x).
Proof. exact (MK_COMB (@lem4355260 A B t s x) (@lem4355255 A B t s x)). Qed.
Lemma lem4355262 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) : (term167 A B t s x) = (term205 A B t s x).
Proof. exact (@lem17646 (term150 A B s t x) (s x)). Qed.
Lemma lem4355263 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) : (term167 A B t s x) = (term206 A B t s x).
Proof. exact (TRANS (@lem4355262 A B t s x) (@lem4355261 A B t s x)). Qed.
Lemma lem4355350 {A : Type'} (P : A -> Prop) (Q : Prop) : (term146 A P Q) = (term145 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4355351 {B : Type'} (P : B -> Prop) (Q : Prop) : (term146 B P Q) = (term145 B P Q).
Proof. exact (@lem4355350 B P Q). Qed.
Lemma lem4355352 {A B : Type'} (t : B -> Prop) (x : A) (x' : A) : (term147 A B t x x') = (term143 A B t x x').
Proof. exact (@lem4355351 B t (x = x')). Qed.
Lemma lem4355353 {A : Type'} (s : A -> Prop) (x' : A) : (term112 A s x') = (term112 A s x').
Proof. exact (eq_refl (term112 A s x')). Qed.
Lemma lem4355354 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) (x' : A) : (term148 A B s t x x') = (term144 A B s t x x').
Proof. exact (MK_COMB (@lem4355353 A s x') (@lem4355352 A B t x x')). Qed.
Lemma lem4355356 {A : Type'} (P : Prop) (Q : A -> Prop) : (term132 A P Q) = (term131 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4355357 {B : Type'} (P : Prop) (Q : B -> Prop) : (term132 B P Q) = (term131 B P Q).
Proof. exact (@lem4355356 B P Q). Qed.
Lemma lem4355358 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) (x' : A) : (term134 A B s t x x') = (term133 A B s t x x').
Proof. exact (@lem4355357 B (s x') (term135 A B t x x')). Qed.
Lemma lem4355359 {A B : Type'} (t : B -> Prop) (y : B) (x : A) (x' : A) : (term136 A B t x x' y) = (term113 A B t y x x').
Proof. exact (eq_refl (term136 A B t x x' y)). Qed.
Lemma lem4355360 {A B : Type'} (t : B -> Prop) (x : A) (x' : A) : (term141 A B t x x') = (term135 A B t x x').
Proof. exact (fun_ext (fun y : B => @lem4355359 A B t y x x')). Qed.
Lemma lem4355361 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4355362 {A B : Type'} (t : B -> Prop) (x : A) (x' : A) : (term142 A B t x x') = (term143 A B t x x').
Proof. exact (MK_COMB (@lem4355361 B) (@lem4355360 A B t x x')). Qed.
Lemma lem4355363 {A : Type'} (s : A -> Prop) (x' : A) : (term112 A s x') = (term112 A s x').
Proof. exact (eq_refl (term112 A s x')). Qed.
Lemma lem4355364 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) (x' : A) : (term134 A B s t x x') = (term144 A B s t x x').
Proof. exact (MK_COMB (@lem4355363 A s x') (@lem4355362 A B t x x')). Qed.
Lemma lem4355365 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4355366 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) (x' : A) : (term207 A B s t x x') = (term208 A B s t x x').
Proof. exact (MK_COMB (@lem4355365) (@lem4355364 A B s t x x')). Qed.
Lemma lem4355367 {A B : Type'} (t : B -> Prop) (y : B) (x : A) (x' : A) : (term136 A B t x x' y) = (term113 A B t y x x').
Proof. exact (eq_refl (term136 A B t x x' y)). Qed.
Lemma lem4355368 {A : Type'} (s : A -> Prop) (x' : A) : (term112 A s x') = (term112 A s x').
Proof. exact (eq_refl (term112 A s x')). Qed.
Lemma lem4355369 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (y : B) (x : A) (x' : A) : (term137 A B s t x x' y) = (term114 A B s t y x x').
Proof. exact (MK_COMB (@lem4355368 A s x') (@lem4355367 A B t y x x')). Qed.
Lemma lem4355370 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) (x' : A) : (term138 A B s t x x') = (term115 A B s t x x').
Proof. exact (fun_ext (fun y : B => @lem4355369 A B s t y x x')). Qed.
Lemma lem4355371 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4355372 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) (x' : A) : (term133 A B s t x x') = (term116 A B s t x x').
Proof. exact (MK_COMB (@lem4355371 B) (@lem4355370 A B s t x x')). Qed.
Lemma lem4355373 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) (x' : A) : ((term134 A B s t x x') = (term133 A B s t x x')) = ((term144 A B s t x x') = (term116 A B s t x x')).
Proof. exact (MK_COMB (@lem4355366 A B s t x x') (@lem4355372 A B s t x x')). Qed.
Lemma lem4355374 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) (x' : A) : (term144 A B s t x x') = (term116 A B s t x x').
Proof. exact (EQ_MP (@lem4355373 A B s t x x') (@lem4355358 A B s t x x')). Qed.
Lemma lem4355375 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) (x' : A) : (term148 A B s t x x') = (term116 A B s t x x').
Proof. exact (TRANS (@lem4355354 A B s t x x') (@lem4355374 A B s t x x')). Qed.
Lemma lem4355376 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) : (term149 A B s t x) = (term117 A B s t x).
Proof. exact (fun_ext (fun x' : A => @lem4355375 A B s t x x')). Qed.
Lemma lem4355377 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4355378 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) : (term150 A B s t x) = (term118 A B s t x).
Proof. exact (MK_COMB (@lem4355377 A) (@lem4355376 A B s t x)). Qed.
Lemma lem4355379 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4355380 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) : (term202 A B s t x) = (term209 A B s t x).
Proof. exact (MK_COMB (@lem4355379) (@lem4355378 A B s t x)). Qed.
Lemma lem4355381 {A : Type'} (s : A -> Prop) (x : A) : (term106 A s x) = (term106 A s x).
Proof. exact (eq_refl (term106 A s x)). Qed.
Lemma lem4355382 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) : (term203 A B t s x) = (term210 A B t s x).
Proof. exact (MK_COMB (@lem4355380 A B s t x) (@lem4355381 A s x)). Qed.
Lemma lem4355384 {A : Type'} (P : A -> Prop) (Q : Prop) : (term146 A P Q) = (term145 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4355385 {A : Type'} (P : A -> Prop) (Q : Prop) : (term146 A P Q) = (term145 A P Q).
Proof. exact (@lem4355384 A P Q). Qed.
Lemma lem4355386 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) : (term211 A B t s x) = (term212 A B t s x).
Proof. exact (@lem4355385 A (term117 A B s t x) (term106 A s x)). Qed.
Lemma lem4355387 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) (x' : A) : (term213 A B s t x x') = (term116 A B s t x x').
Proof. exact (eq_refl (term213 A B s t x x')). Qed.
Lemma lem4355388 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) : (term214 A B s t x) = (term117 A B s t x).
Proof. exact (fun_ext (fun x' : A => @lem4355387 A B s t x x')). Qed.
Lemma lem4355389 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4355390 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) : (term215 A B s t x) = (term118 A B s t x).
Proof. exact (MK_COMB (@lem4355389 A) (@lem4355388 A B s t x)). Qed.
Lemma lem4355391 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4355392 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) : (term216 A B s t x) = (term209 A B s t x).
Proof. exact (MK_COMB (@lem4355391) (@lem4355390 A B s t x)). Qed.
Lemma lem4355393 {A : Type'} (s : A -> Prop) (x : A) : (term106 A s x) = (term106 A s x).
Proof. exact (eq_refl (term106 A s x)). Qed.
Lemma lem4355394 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) : (term211 A B t s x) = (term210 A B t s x).
Proof. exact (MK_COMB (@lem4355392 A B s t x) (@lem4355393 A s x)). Qed.
Lemma lem4355395 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4355396 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) : (term217 A B t s x) = (term218 A B t s x).
Proof. exact (MK_COMB (@lem4355395) (@lem4355394 A B t s x)). Qed.
Lemma lem4355397 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) (x' : A) : (term213 A B s t x x') = (term116 A B s t x x').
Proof. exact (eq_refl (term213 A B s t x x')). Qed.
Lemma lem4355398 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4355399 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) (x' : A) : (term219 A B s t x x') = (term220 A B s t x x').
Proof. exact (MK_COMB (@lem4355398) (@lem4355397 A B s t x x')). Qed.
Lemma lem4355400 {A : Type'} (s : A -> Prop) (x : A) : (term106 A s x) = (term106 A s x).
Proof. exact (eq_refl (term106 A s x)). Qed.
Lemma lem4355401 {A B : Type'} (t : B -> Prop) (x' : A) (s : A -> Prop) (x : A) : (term221 A B t x' s x) = (term222 A B t x' s x).
Proof. exact (MK_COMB (@lem4355399 A B s t x x') (@lem4355400 A s x)). Qed.
Lemma lem4355402 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) : (term223 A B t s x) = (term224 A B t s x).
Proof. exact (fun_ext (fun x' : A => @lem4355401 A B t x' s x)). Qed.
Lemma lem4355403 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4355404 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) : (term212 A B t s x) = (term225 A B t s x).
Proof. exact (MK_COMB (@lem4355403 A) (@lem4355402 A B t s x)). Qed.
Lemma lem4355405 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) : ((term211 A B t s x) = (term212 A B t s x)) = ((term210 A B t s x) = (term225 A B t s x)).
Proof. exact (MK_COMB (@lem4355396 A B t s x) (@lem4355404 A B t s x)). Qed.
Lemma lem4355406 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) : (term210 A B t s x) = (term225 A B t s x).
Proof. exact (EQ_MP (@lem4355405 A B t s x) (@lem4355386 A B t s x)). Qed.
Lemma lem4355408 {A : Type'} (P : A -> Prop) (Q : Prop) : (term146 A P Q) = (term145 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4355409 {B : Type'} (P : B -> Prop) (Q : Prop) : (term146 B P Q) = (term145 B P Q).
Proof. exact (@lem4355408 B P Q). Qed.
Lemma lem4355410 {A B : Type'} (t : B -> Prop) (x' : A) (s : A -> Prop) (x : A) : (term226 A B t x' s x) = (term227 A B t x' s x).
Proof. exact (@lem4355409 B (term115 A B s t x x') (term106 A s x)). Qed.
Lemma lem4355411 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (y : B) (x : A) (x' : A) : (term228 A B s t x x' y) = (term114 A B s t y x x').
Proof. exact (eq_refl (term228 A B s t x x' y)). Qed.
Lemma lem4355412 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) (x' : A) : (term229 A B s t x x') = (term115 A B s t x x').
Proof. exact (fun_ext (fun y : B => @lem4355411 A B s t y x x')). Qed.
Lemma lem4355413 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4355414 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) (x' : A) : (term230 A B s t x x') = (term116 A B s t x x').
Proof. exact (MK_COMB (@lem4355413 B) (@lem4355412 A B s t x x')). Qed.
Lemma lem4355415 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4355416 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) (x' : A) : (term231 A B s t x x') = (term220 A B s t x x').
Proof. exact (MK_COMB (@lem4355415) (@lem4355414 A B s t x x')). Qed.
Lemma lem4355417 {A : Type'} (s : A -> Prop) (x : A) : (term106 A s x) = (term106 A s x).
Proof. exact (eq_refl (term106 A s x)). Qed.
Lemma lem4355418 {A B : Type'} (t : B -> Prop) (x' : A) (s : A -> Prop) (x : A) : (term226 A B t x' s x) = (term222 A B t x' s x).
Proof. exact (MK_COMB (@lem4355416 A B s t x x') (@lem4355417 A s x)). Qed.
Lemma lem4355419 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4355420 {A B : Type'} (t : B -> Prop) (x' : A) (s : A -> Prop) (x : A) : (term232 A B t x' s x) = (term233 A B t x' s x).
Proof. exact (MK_COMB (@lem4355419) (@lem4355418 A B t x' s x)). Qed.
Lemma lem4355421 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (y : B) (x : A) (x' : A) : (term228 A B s t x x' y) = (term114 A B s t y x x').
Proof. exact (eq_refl (term228 A B s t x x' y)). Qed.
Lemma lem4355422 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4355423 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (y : B) (x : A) (x' : A) : (term234 A B s t x x' y) = (term235 A B s t y x x').
Proof. exact (MK_COMB (@lem4355422) (@lem4355421 A B s t y x x')). Qed.
Lemma lem4355424 {A : Type'} (s : A -> Prop) (x : A) : (term106 A s x) = (term106 A s x).
Proof. exact (eq_refl (term106 A s x)). Qed.
Lemma lem4355425 {A B : Type'} (t : B -> Prop) (y : B) (x' : A) (s : A -> Prop) (x : A) : (term236 A B t x' y s x) = (term237 A B t y x' s x).
Proof. exact (MK_COMB (@lem4355423 A B s t y x x') (@lem4355424 A s x)). Qed.
Lemma lem4355426 {A B : Type'} (t : B -> Prop) (x' : A) (s : A -> Prop) (x : A) : (term238 A B t x' s x) = (term239 A B t x' s x).
Proof. exact (fun_ext (fun y : B => @lem4355425 A B t y x' s x)). Qed.
Lemma lem4355427 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4355428 {A B : Type'} (t : B -> Prop) (x' : A) (s : A -> Prop) (x : A) : (term227 A B t x' s x) = (term240 A B t x' s x).
Proof. exact (MK_COMB (@lem4355427 B) (@lem4355426 A B t x' s x)). Qed.
Lemma lem4355429 {A B : Type'} (t : B -> Prop) (x' : A) (s : A -> Prop) (x : A) : ((term226 A B t x' s x) = (term227 A B t x' s x)) = ((term222 A B t x' s x) = (term240 A B t x' s x)).
Proof. exact (MK_COMB (@lem4355420 A B t x' s x) (@lem4355428 A B t x' s x)). Qed.
Lemma lem4355430 {A B : Type'} (t : B -> Prop) (x' : A) (s : A -> Prop) (x : A) : (term222 A B t x' s x) = (term240 A B t x' s x).
Proof. exact (EQ_MP (@lem4355429 A B t x' s x) (@lem4355410 A B t x' s x)). Qed.
Lemma lem4355431 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) : (term224 A B t s x) = (term241 A B t s x).
Proof. exact (fun_ext (fun x' : A => @lem4355430 A B t x' s x)). Qed.
Lemma lem4355432 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4355433 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) : (term225 A B t s x) = (term242 A B t s x).
Proof. exact (MK_COMB (@lem4355432 A) (@lem4355431 A B t s x)). Qed.
Lemma lem4355434 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) : (term210 A B t s x) = (term242 A B t s x).
Proof. exact (TRANS (@lem4355406 A B t s x) (@lem4355433 A B t s x)). Qed.
Lemma lem4355435 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) : (term203 A B t s x) = (term242 A B t s x).
Proof. exact (TRANS (@lem4355382 A B t s x) (@lem4355434 A B t s x)). Qed.
Lemma lem4355436 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4355437 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) : (term204 A B t s x) = (term243 A B t s x).
Proof. exact (MK_COMB (@lem4355436) (@lem4355435 A B t s x)). Qed.
Lemma lem4355438 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) : (term201 A B t s x) = (term201 A B t s x).
Proof. exact (eq_refl (term201 A B t s x)). Qed.
Lemma lem4355439 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) : (term206 A B t s x) = (term244 A B t s x).
Proof. exact (MK_COMB (@lem4355437 A B t s x) (@lem4355438 A B t s x)). Qed.
Lemma lem4355441 {A : Type'} (P : A -> Prop) (Q : Prop) : (term245 A P Q) = (term246 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4355442 {A : Type'} (P : A -> Prop) (Q : Prop) : (term245 A P Q) = (term246 A P Q).
Proof. exact (@lem4355441 A P Q). Qed.
Lemma lem4355443 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) : (term247 A B t s x) = (term248 A B t s x).
Proof. exact (@lem4355442 A (term241 A B t s x) (term201 A B t s x)). Qed.
Lemma lem4355444 {A B : Type'} (t : B -> Prop) (x' : A) (s : A -> Prop) (x : A) : (term249 A B t s x x') = (term240 A B t x' s x).
Proof. exact (eq_refl (term249 A B t s x x')). Qed.
Lemma lem4355445 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) : (term250 A B t s x) = (term241 A B t s x).
Proof. exact (fun_ext (fun x' : A => @lem4355444 A B t x' s x)). Qed.
Lemma lem4355446 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4355447 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) : (term251 A B t s x) = (term242 A B t s x).
Proof. exact (MK_COMB (@lem4355446 A) (@lem4355445 A B t s x)). Qed.
Lemma lem4355448 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4355449 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) : (term252 A B t s x) = (term243 A B t s x).
Proof. exact (MK_COMB (@lem4355448) (@lem4355447 A B t s x)). Qed.
Lemma lem4355450 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) : (term201 A B t s x) = (term201 A B t s x).
Proof. exact (eq_refl (term201 A B t s x)). Qed.
Lemma lem4355451 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) : (term247 A B t s x) = (term244 A B t s x).
Proof. exact (MK_COMB (@lem4355449 A B t s x) (@lem4355450 A B t s x)). Qed.
Lemma lem4355452 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4355453 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) : (term253 A B t s x) = (term254 A B t s x).
Proof. exact (MK_COMB (@lem4355452) (@lem4355451 A B t s x)). Qed.
Lemma lem4355454 {A B : Type'} (t : B -> Prop) (x' : A) (s : A -> Prop) (x : A) : (term249 A B t s x x') = (term240 A B t x' s x).
Proof. exact (eq_refl (term249 A B t s x x')). Qed.
Lemma lem4355455 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4355456 {A B : Type'} (t : B -> Prop) (x' : A) (s : A -> Prop) (x : A) : (term255 A B t s x x') = (term256 A B t x' s x).
Proof. exact (MK_COMB (@lem4355455) (@lem4355454 A B t x' s x)). Qed.
Lemma lem4355457 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) : (term201 A B t s x) = (term201 A B t s x).
Proof. exact (eq_refl (term201 A B t s x)). Qed.
Lemma lem4355458 {A B : Type'} (x' : A) (t : B -> Prop) (s : A -> Prop) (x : A) : (term257 A B x' t s x) = (term258 A B x' t s x).
Proof. exact (MK_COMB (@lem4355456 A B t x' s x) (@lem4355457 A B t s x)). Qed.
Lemma lem4355459 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) : (term259 A B t s x) = (term260 A B t s x).
Proof. exact (fun_ext (fun x' : A => @lem4355458 A B x' t s x)). Qed.
Lemma lem4355460 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4355461 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) : (term248 A B t s x) = (term261 A B t s x).
Proof. exact (MK_COMB (@lem4355460 A) (@lem4355459 A B t s x)). Qed.
Lemma lem4355462 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) : ((term247 A B t s x) = (term248 A B t s x)) = ((term244 A B t s x) = (term261 A B t s x)).
Proof. exact (MK_COMB (@lem4355453 A B t s x) (@lem4355461 A B t s x)). Qed.
Lemma lem4355463 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) : (term244 A B t s x) = (term261 A B t s x).
Proof. exact (EQ_MP (@lem4355462 A B t s x) (@lem4355443 A B t s x)). Qed.
Lemma lem4355465 {A : Type'} (P : A -> Prop) (Q : Prop) : (term245 A P Q) = (term246 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4355466 {B : Type'} (P : B -> Prop) (Q : Prop) : (term245 B P Q) = (term246 B P Q).
Proof. exact (@lem4355465 B P Q). Qed.
Lemma lem4355467 {A B : Type'} (x' : A) (t : B -> Prop) (s : A -> Prop) (x : A) : (term262 A B x' t s x) = (term263 A B x' t s x).
Proof. exact (@lem4355466 B (term239 A B t x' s x) (term201 A B t s x)). Qed.
Lemma lem4355468 {A B : Type'} (t : B -> Prop) (y : B) (x' : A) (s : A -> Prop) (x : A) : (term264 A B t x' s x y) = (term237 A B t y x' s x).
Proof. exact (eq_refl (term264 A B t x' s x y)). Qed.
Lemma lem4355469 {A B : Type'} (t : B -> Prop) (x' : A) (s : A -> Prop) (x : A) : (term265 A B t x' s x) = (term239 A B t x' s x).
Proof. exact (fun_ext (fun y : B => @lem4355468 A B t y x' s x)). Qed.
Lemma lem4355470 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4355471 {A B : Type'} (t : B -> Prop) (x' : A) (s : A -> Prop) (x : A) : (term266 A B t x' s x) = (term240 A B t x' s x).
Proof. exact (MK_COMB (@lem4355470 B) (@lem4355469 A B t x' s x)). Qed.
Lemma lem4355472 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4355473 {A B : Type'} (t : B -> Prop) (x' : A) (s : A -> Prop) (x : A) : (term267 A B t x' s x) = (term256 A B t x' s x).
Proof. exact (MK_COMB (@lem4355472) (@lem4355471 A B t x' s x)). Qed.
Lemma lem4355474 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) : (term201 A B t s x) = (term201 A B t s x).
Proof. exact (eq_refl (term201 A B t s x)). Qed.
Lemma lem4355475 {A B : Type'} (x' : A) (t : B -> Prop) (s : A -> Prop) (x : A) : (term262 A B x' t s x) = (term258 A B x' t s x).
Proof. exact (MK_COMB (@lem4355473 A B t x' s x) (@lem4355474 A B t s x)). Qed.
Lemma lem4355476 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4355477 {A B : Type'} (x' : A) (t : B -> Prop) (s : A -> Prop) (x : A) : (term268 A B x' t s x) = (term269 A B x' t s x).
Proof. exact (MK_COMB (@lem4355476) (@lem4355475 A B x' t s x)). Qed.
Lemma lem4355478 {A B : Type'} (t : B -> Prop) (y : B) (x' : A) (s : A -> Prop) (x : A) : (term264 A B t x' s x y) = (term237 A B t y x' s x).
Proof. exact (eq_refl (term264 A B t x' s x y)). Qed.
Lemma lem4355479 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4355480 {A B : Type'} (t : B -> Prop) (y : B) (x' : A) (s : A -> Prop) (x : A) : (term270 A B t x' s x y) = (term271 A B t y x' s x).
Proof. exact (MK_COMB (@lem4355479) (@lem4355478 A B t y x' s x)). Qed.
Lemma lem4355481 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) : (term201 A B t s x) = (term201 A B t s x).
Proof. exact (eq_refl (term201 A B t s x)). Qed.
Lemma lem4355482 {A B : Type'} (y : B) (x' : A) (t : B -> Prop) (s : A -> Prop) (x : A) : (term272 A B x' y t s x) = (term273 A B y x' t s x).
Proof. exact (MK_COMB (@lem4355480 A B t y x' s x) (@lem4355481 A B t s x)). Qed.
Lemma lem4355483 {A B : Type'} (x' : A) (t : B -> Prop) (s : A -> Prop) (x : A) : (term274 A B x' t s x) = (term275 A B x' t s x).
Proof. exact (fun_ext (fun y : B => @lem4355482 A B y x' t s x)). Qed.
Lemma lem4355484 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4355485 {A B : Type'} (x' : A) (t : B -> Prop) (s : A -> Prop) (x : A) : (term263 A B x' t s x) = (term276 A B x' t s x).
Proof. exact (MK_COMB (@lem4355484 B) (@lem4355483 A B x' t s x)). Qed.
Lemma lem4355486 {A B : Type'} (x' : A) (t : B -> Prop) (s : A -> Prop) (x : A) : ((term262 A B x' t s x) = (term263 A B x' t s x)) = ((term258 A B x' t s x) = (term276 A B x' t s x)).
Proof. exact (MK_COMB (@lem4355477 A B x' t s x) (@lem4355485 A B x' t s x)). Qed.
Lemma lem4355487 {A B : Type'} (x' : A) (t : B -> Prop) (s : A -> Prop) (x : A) : (term258 A B x' t s x) = (term276 A B x' t s x).
Proof. exact (EQ_MP (@lem4355486 A B x' t s x) (@lem4355467 A B x' t s x)). Qed.
Lemma lem4355488 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) : (term260 A B t s x) = (term277 A B t s x).
Proof. exact (fun_ext (fun x' : A => @lem4355487 A B x' t s x)). Qed.
Lemma lem4355489 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4355490 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) : (term261 A B t s x) = (term278 A B t s x).
Proof. exact (MK_COMB (@lem4355489 A) (@lem4355488 A B t s x)). Qed.
Lemma lem4355491 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) : (term244 A B t s x) = (term278 A B t s x).
Proof. exact (TRANS (@lem4355463 A B t s x) (@lem4355490 A B t s x)). Qed.
Lemma lem4355493 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) : (term206 A B t s x) = (term278 A B t s x).
Proof. exact (TRANS (@lem4355439 A B t s x) (@lem4355491 A B t s x)). Qed.
Lemma lem4355494 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) : (term167 A B t s x) = (term278 A B t s x).
Proof. exact (TRANS (@lem4355263 A B t s x) (@lem4355493 A B t s x)). Qed.
Lemma lem4355495 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) (h1 : term167 A B t s x) : term278 A B t s x.
Proof. exact (EQ_MP (@lem4355494 A B t s x) (@lem4355180 A B t s x h1)). Qed.
Lemma lem4355496 {A B : Type'} (x' : A) (t : B -> Prop) (s : A -> Prop) (x : A) (h1 : term276 A B x' t s x) : term276 A B x' t s x.
Proof. exact (h1). Qed.
Lemma lem4355497 {A B : Type'} (y : B) (x' : A) (t : B -> Prop) (s : A -> Prop) (x : A) (h1 : term273 A B y x' t s x) : term273 A B y x' t s x.
Proof. exact (h1). Qed.
Lemma lem4355501 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem4355508 {A : Type'} (x : A) (x' : A) : (term181 A x x') = (term181 A x x').
Proof. exact (eq_refl (term181 A x x')). Qed.
Lemma lem4355513 {B : Type'} (t : B -> Prop) (y : B) : (term106 B t y) = (term106 B t y).
Proof. exact (eq_refl (term106 B t y)). Qed.
Lemma lem4355514 {B : Type'} (t : B -> Prop) : (term108 B t) = (term108 B t).
Proof. exact (fun_ext (fun y : B => @lem4355513 B t y)). Qed.
Lemma lem4355515 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4355516 {B : Type'} (t : B -> Prop) : (term109 B t) = (term109 B t).
Proof. exact (MK_COMB (@lem4355515 B) (@lem4355514 B t)). Qed.
Lemma lem4355517 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4355518 {B : Type'} (t : B -> Prop) : (term183 B t) = (term183 B t).
Proof. exact (MK_COMB (@lem4355517) (@lem4355516 B t)). Qed.
Lemma lem4355519 {A B : Type'} (t : B -> Prop) (x : A) (x' : A) : (term185 A B t x x') = (term185 A B t x x').
Proof. exact (MK_COMB (@lem4355518 B t) (@lem4355508 A x x')). Qed.
Lemma lem4355526 {A : Type'} (s : A -> Prop) (x' : A) : (term187 A s x') = (term187 A s x').
Proof. exact (eq_refl (term187 A s x')). Qed.
Lemma lem4355527 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) (x' : A) : (term189 A B s t x x') = (term189 A B s t x x').
Proof. exact (MK_COMB (@lem4355526 A s x') (@lem4355519 A B t x x')). Qed.
Lemma lem4355528 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) : (term196 A B s t x) = (term196 A B s t x).
Proof. exact (fun_ext (fun x' : A => @lem4355527 A B s t x x')). Qed.
Lemma lem4355529 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4355530 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) : (term197 A B s t x) = (term197 A B s t x).
Proof. exact (MK_COMB (@lem4355529 A) (@lem4355528 A B s t x)). Qed.
Lemma lem4355531 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4355532 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) : (term199 A B s t x) = (term199 A B s t x).
Proof. exact (MK_COMB (@lem4355531) (@lem4355530 A B s t x)). Qed.
Lemma lem4355533 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) : (term201 A B t s x) = (term201 A B t s x).
Proof. exact (MK_COMB (@lem4355532 A B s t x) (@lem4355501 A s x)). Qed.
Lemma lem4355560 {A B : Type'} (t : B -> Prop) (y : B) (x' : A) (s : A -> Prop) (x : A) : (term271 A B t y x' s x) = (term271 A B t y x' s x).
Proof. exact (eq_refl (term271 A B t y x' s x)). Qed.
Lemma lem4355561 {A B : Type'} (y : B) (x' : A) (t : B -> Prop) (s : A -> Prop) (x : A) : (term273 A B y x' t s x) = (term273 A B y x' t s x).
Proof. exact (MK_COMB (@lem4355560 A B t y x' s x) (@lem4355533 A B t s x)). Qed.
Lemma lem4355562 {A B : Type'} (y : B) (x' : A) (t : B -> Prop) (s : A -> Prop) (x : A) (h1 : term273 A B y x' t s x) : term273 A B y x' t s x.
Proof. exact (EQ_MP (@lem4355561 A B y x' t s x) (@lem4355497 A B y x' t s x h1)). Qed.
Lemma lem4355566 {B : Type'} (t : B -> Prop) (x'' : B) (h1 : t x'') : t x''.
Proof. exact (h1). Qed.
Lemma lem4355567 {A B : Type'} (t : B -> Prop) (y : B) (x' : A) (s : A -> Prop) (x : A) (h1 : term237 A B t y x' s x) : term237 A B t y x' s x.
Proof. exact (h1). Qed.
Lemma lem4355568 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) (h1 : term201 A B t s x) : term201 A B t s x.
Proof. exact (h1). Qed.
Lemma lem4355570 {A B : Type'} (t : B -> Prop) (y : B) (x' : A) (s : A -> Prop) (x : A) (h1 : term237 A B t y x' s x) : term114 A B s t y x x'.
Proof. exact (proj1 (@lem4355567 A B t y x' s x h1)). Qed.
Lemma lem4355571 {A B : Type'} (t : B -> Prop) (y : B) (x' : A) (s : A -> Prop) (x : A) (h1 : term237 A B t y x' s x) : term113 A B t y x x'.
Proof. exact (proj2 (@lem4355570 A B t y x' s x h1)). Qed.
Lemma lem4355576 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) (h1 : term201 A B t s x) : term197 A B s t x.
Proof. exact (proj1 (@lem4355568 A B t s x h1)). Qed.
Lemma lem4355600 {B : Type'} (t : B -> Prop) (x'' : B) (h1 : t x'') : t x''.
Proof. exact (h1). Qed.
Lemma lem4355602 {A : Type'} (P : A -> Prop) (Q : Prop) : (term279 A P Q) = (term280 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem4355603 {B : Type'} (P : B -> Prop) (Q : Prop) : (term279 B P Q) = (term280 B P Q).
Proof. exact (@lem4355602 B P Q). Qed.
Lemma lem4355604 {A B : Type'} (t : B -> Prop) (x : A) (x' : A) : (term281 A B t x x') = (term282 A B t x x').
Proof. exact (@lem4355603 B (term108 B t) (term181 A x x')). Qed.
Lemma lem4355605 {B : Type'} (t : B -> Prop) (y : B) : (term172 B t y) = (term106 B t y).
Proof. exact (eq_refl (term172 B t y)). Qed.
Lemma lem4355606 {B : Type'} (t : B -> Prop) : (term283 B t) = (term108 B t).
Proof. exact (fun_ext (fun y : B => @lem4355605 B t y)). Qed.
Lemma lem4355607 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4355608 {B : Type'} (t : B -> Prop) : (term284 B t) = (term109 B t).
Proof. exact (MK_COMB (@lem4355607 B) (@lem4355606 B t)). Qed.
Lemma lem4355609 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4355610 {B : Type'} (t : B -> Prop) : (term285 B t) = (term183 B t).
Proof. exact (MK_COMB (@lem4355609) (@lem4355608 B t)). Qed.
Lemma lem4355611 {A : Type'} (x : A) (x' : A) : (term181 A x x') = (term181 A x x').
Proof. exact (eq_refl (term181 A x x')). Qed.
Lemma lem4355612 {A B : Type'} (t : B -> Prop) (x : A) (x' : A) : (term281 A B t x x') = (term185 A B t x x').
Proof. exact (MK_COMB (@lem4355610 B t) (@lem4355611 A x x')). Qed.
Lemma lem4355613 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4355614 {A B : Type'} (t : B -> Prop) (x : A) (x' : A) : (term286 A B t x x') = (term287 A B t x x').
Proof. exact (MK_COMB (@lem4355613) (@lem4355612 A B t x x')). Qed.
Lemma lem4355615 {B : Type'} (t : B -> Prop) (y : B) : (term172 B t y) = (term106 B t y).
Proof. exact (eq_refl (term172 B t y)). Qed.
Lemma lem4355616 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4355617 {B : Type'} (t : B -> Prop) (y : B) : (term288 B t y) = (term187 B t y).
Proof. exact (MK_COMB (@lem4355616) (@lem4355615 B t y)). Qed.
Lemma lem4355618 {A : Type'} (x : A) (x' : A) : (term181 A x x') = (term181 A x x').
Proof. exact (eq_refl (term181 A x x')). Qed.
Lemma lem4355619 {A B : Type'} (t : B -> Prop) (y : B) (x : A) (x' : A) : (term289 A B t y x x') = (term290 A B t y x x').
Proof. exact (MK_COMB (@lem4355617 B t y) (@lem4355618 A x x')). Qed.
Lemma lem4355620 {A B : Type'} (t : B -> Prop) (x : A) (x' : A) : (term291 A B t x x') = (term292 A B t x x').
Proof. exact (fun_ext (fun y : B => @lem4355619 A B t y x x')). Qed.
Lemma lem4355621 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4355622 {A B : Type'} (t : B -> Prop) (x : A) (x' : A) : (term282 A B t x x') = (term293 A B t x x').
Proof. exact (MK_COMB (@lem4355621 B) (@lem4355620 A B t x x')). Qed.
Lemma lem4355623 {A B : Type'} (t : B -> Prop) (x : A) (x' : A) : ((term281 A B t x x') = (term282 A B t x x')) = ((term185 A B t x x') = (term293 A B t x x')).
Proof. exact (MK_COMB (@lem4355614 A B t x x') (@lem4355622 A B t x x')). Qed.
Lemma lem4355624 {A B : Type'} (t : B -> Prop) (x : A) (x' : A) : (term185 A B t x x') = (term293 A B t x x').
Proof. exact (EQ_MP (@lem4355623 A B t x x') (@lem4355604 A B t x x')). Qed.
Lemma lem4355625 {A : Type'} (s : A -> Prop) (x' : A) : (term187 A s x') = (term187 A s x').
Proof. exact (eq_refl (term187 A s x')). Qed.
Lemma lem4355626 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) (x' : A) : (term189 A B s t x x') = (term294 A B s t x x').
Proof. exact (MK_COMB (@lem4355625 A s x') (@lem4355624 A B t x x')). Qed.
Lemma lem4355628 {A : Type'} (P : Prop) (Q : A -> Prop) : (term295 A P Q) = (term296 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem4355629 {B : Type'} (P : Prop) (Q : B -> Prop) : (term295 B P Q) = (term296 B P Q).
Proof. exact (@lem4355628 B P Q). Qed.
Lemma lem4355630 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) (x' : A) : (term297 A B s t x x') = (term298 A B s t x x').
Proof. exact (@lem4355629 B (term106 A s x') (term292 A B t x x')). Qed.
Lemma lem4355631 {A B : Type'} (t : B -> Prop) (y : B) (x : A) (x' : A) : (term299 A B t x x' y) = (term290 A B t y x x').
Proof. exact (eq_refl (term299 A B t x x' y)). Qed.
Lemma lem4355632 {A B : Type'} (t : B -> Prop) (x : A) (x' : A) : (term300 A B t x x') = (term292 A B t x x').
Proof. exact (fun_ext (fun y : B => @lem4355631 A B t y x x')). Qed.
Lemma lem4355633 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4355634 {A B : Type'} (t : B -> Prop) (x : A) (x' : A) : (term301 A B t x x') = (term293 A B t x x').
Proof. exact (MK_COMB (@lem4355633 B) (@lem4355632 A B t x x')). Qed.
Lemma lem4355635 {A : Type'} (s : A -> Prop) (x' : A) : (term187 A s x') = (term187 A s x').
Proof. exact (eq_refl (term187 A s x')). Qed.
Lemma lem4355636 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) (x' : A) : (term297 A B s t x x') = (term294 A B s t x x').
Proof. exact (MK_COMB (@lem4355635 A s x') (@lem4355634 A B t x x')). Qed.
Lemma lem4355637 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4355638 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) (x' : A) : (term302 A B s t x x') = (term303 A B s t x x').
Proof. exact (MK_COMB (@lem4355637) (@lem4355636 A B s t x x')). Qed.
Lemma lem4355639 {A B : Type'} (t : B -> Prop) (y : B) (x : A) (x' : A) : (term299 A B t x x' y) = (term290 A B t y x x').
Proof. exact (eq_refl (term299 A B t x x' y)). Qed.
Lemma lem4355640 {A : Type'} (s : A -> Prop) (x' : A) : (term187 A s x') = (term187 A s x').
Proof. exact (eq_refl (term187 A s x')). Qed.
Lemma lem4355641 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (y : B) (x : A) (x' : A) : (term304 A B s t x x' y) = (term305 A B s t y x x').
Proof. exact (MK_COMB (@lem4355640 A s x') (@lem4355639 A B t y x x')). Qed.
Lemma lem4355642 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) (x' : A) : (term306 A B s t x x') = (term307 A B s t x x').
Proof. exact (fun_ext (fun y : B => @lem4355641 A B s t y x x')). Qed.
Lemma lem4355643 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4355644 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) (x' : A) : (term298 A B s t x x') = (term308 A B s t x x').
Proof. exact (MK_COMB (@lem4355643 B) (@lem4355642 A B s t x x')). Qed.
Lemma lem4355645 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) (x' : A) : ((term297 A B s t x x') = (term298 A B s t x x')) = ((term294 A B s t x x') = (term308 A B s t x x')).
Proof. exact (MK_COMB (@lem4355638 A B s t x x') (@lem4355644 A B s t x x')). Qed.
Lemma lem4355646 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) (x' : A) : (term294 A B s t x x') = (term308 A B s t x x').
Proof. exact (EQ_MP (@lem4355645 A B s t x x') (@lem4355630 A B s t x x')). Qed.
Lemma lem4355647 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) (x' : A) : (term189 A B s t x x') = (term308 A B s t x x').
Proof. exact (TRANS (@lem4355626 A B s t x x') (@lem4355646 A B s t x x')). Qed.
Lemma lem4355648 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) : (term196 A B s t x) = (term309 A B s t x).
Proof. exact (fun_ext (fun x' : A => @lem4355647 A B s t x x')). Qed.
Lemma lem4355649 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4355650 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) : (term197 A B s t x) = (term310 A B s t x).
Proof. exact (MK_COMB (@lem4355649 A) (@lem4355648 A B s t x)). Qed.
Lemma lem4355663 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (y : B) (x : A) (x' : A) : (term305 A B s t y x x') = (term305 A B s t y x x').
Proof. exact (eq_refl (term305 A B s t y x x')). Qed.
Lemma lem4355664 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) (x' : A) : (term307 A B s t x x') = (term307 A B s t x x').
Proof. exact (fun_ext (fun y : B => @lem4355663 A B s t y x x')). Qed.
Lemma lem4355665 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4355666 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) (x' : A) : (term308 A B s t x x') = (term308 A B s t x x').
Proof. exact (MK_COMB (@lem4355665 B) (@lem4355664 A B s t x x')). Qed.
Lemma lem4355667 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) : (term309 A B s t x) = (term309 A B s t x).
Proof. exact (fun_ext (fun x' : A => @lem4355666 A B s t x x')). Qed.
Lemma lem4355668 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4355669 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) : (term310 A B s t x) = (term310 A B s t x).
Proof. exact (MK_COMB (@lem4355668 A) (@lem4355667 A B s t x)). Qed.
Lemma lem4355670 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) : (term197 A B s t x) = (term310 A B s t x).
Proof. exact (TRANS (@lem4355650 A B s t x) (@lem4355669 A B s t x)). Qed.
Lemma lem4355671 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) (h1 : term201 A B t s x) : term310 A B s t x.
Proof. exact (EQ_MP (@lem4355670 A B s t x) (@lem4355576 A B t s x h1)). Qed.
Lemma lem4355676 {A B : Type'} (_49796 : A) (t : B -> Prop) (s : A -> Prop) (x : A) (h1 : term201 A B t s x) : term311 A B s t x _49796.
Proof. exact (@lem4355671 A B t s x h1 _49796). Qed.
Lemma lem4355677 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : A) (_49796 : A) : (term311 A B s t x _49796) = (term308 A B s t x _49796).
Proof. exact (eq_refl (term311 A B s t x _49796)). Qed.
Lemma lem4355678 {A B : Type'} (_49796 : A) (t : B -> Prop) (s : A -> Prop) (x : A) (h1 : term201 A B t s x) : term308 A B s t x _49796.
Proof. exact (EQ_MP (@lem4355677 A B s t x _49796) (@lem4355676 A B _49796 t s x h1)). Qed.
Lemma lem4355679 {A B : Type'} (_49796 : A) (_49797 : B) (t : B -> Prop) (s : A -> Prop) (x : A) (h1 : term201 A B t s x) : term312 A B s t x _49796 _49797.
Proof. exact (@lem4355678 A B _49796 t s x h1 _49797). Qed.
Lemma lem4355680 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (_49797 : B) (x : A) (_49796 : A) : (term312 A B s t x _49796 _49797) = (term305 A B s t _49797 x _49796).
Proof. exact (eq_refl (term312 A B s t x _49796 _49797)). Qed.
Lemma lem4355685 {A B : Type'} (t : B -> Prop) (y : B) (x' : A) (s : A -> Prop) (x : A) (h1 : term237 A B t y x' s x) : term106 A s x.
Proof. exact (proj2 (@lem4355567 A B t y x' s x h1)). Qed.
Lemma lem4355691 {A B : Type'} (t : B -> Prop) (y : B) (x' : A) (s : A -> Prop) (x : A) (h1 : term237 A B t y x' s x) : x = x'.
Proof. exact (proj2 (@lem4355571 A B t y x' s x h1)). Qed.
Lemma lem4355693 {B : Type'} (t : B -> Prop) (x'' : B) (h1 : t x'') : t x''.
Proof. exact (h1). Qed.
Lemma lem4355703 {A B : Type'} (_49797 : B) (_49796 : A) (t : B -> Prop) (s : A -> Prop) (x : A) (h1 : term201 A B t s x) : term305 A B s t _49797 x _49796.
Proof. exact (EQ_MP (@lem4355680 A B s t _49797 x _49796) (@lem4355679 A B _49796 _49797 t s x h1)). Qed.
Lemma lem4355734 {A : Type'} (s : A -> Prop) : (term108 A s) = (term108 A s).
Proof. exact (eq_refl (term108 A s)). Qed.
Lemma lem4355735 {A B : Type'} (t : B -> Prop) (y : B) (x' : A) (s : A -> Prop) (x : A) (h1 : term237 A B t y x' s x) : (term172 A s x) = (term172 A s x').
Proof. exact (MK_COMB (@lem4355734 A s) (@lem4355691 A B t y x' s x h1)). Qed.
Lemma lem4355736 {A : Type'} (s : A -> Prop) (x' : A) : (term172 A s x') = (term106 A s x').
Proof. exact (eq_refl (term172 A s x')). Qed.
Lemma lem4355737 {A : Type'} (s : A -> Prop) (x : A) : (term313 A s x) = (term313 A s x).
Proof. exact (eq_refl (term313 A s x)). Qed.
Lemma lem4355738 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : ((term172 A s x) = (term172 A s x')) = ((term172 A s x) = (term106 A s x')).
Proof. exact (MK_COMB (@lem4355737 A s x) (@lem4355736 A s x')). Qed.
Lemma lem4355739 {A : Type'} (s : A -> Prop) (x : A) : (term172 A s x) = (term106 A s x).
Proof. exact (eq_refl (term172 A s x)). Qed.
Lemma lem4355740 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4355741 {A : Type'} (s : A -> Prop) (x : A) : (term313 A s x) = (term314 A s x).
Proof. exact (MK_COMB (@lem4355740) (@lem4355739 A s x)). Qed.
Lemma lem4355742 {A : Type'} (s : A -> Prop) (x' : A) : (term106 A s x') = (term106 A s x').
Proof. exact (eq_refl (term106 A s x')). Qed.
Lemma lem4355743 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : ((term172 A s x) = (term106 A s x')) = ((term106 A s x) = (term106 A s x')).
Proof. exact (MK_COMB (@lem4355741 A s x) (@lem4355742 A s x')). Qed.
Lemma lem4355744 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : ((term172 A s x) = (term172 A s x')) = ((term106 A s x) = (term106 A s x')).
Proof. exact (TRANS (@lem4355738 A x s x') (@lem4355743 A x s x')). Qed.
Lemma lem4355745 {A B : Type'} (t : B -> Prop) (y : B) (x' : A) (s : A -> Prop) (x : A) (h1 : term237 A B t y x' s x) : (term106 A s x) = (term106 A s x').
Proof. exact (EQ_MP (@lem4355744 A x s x') (@lem4355735 A B t y x' s x h1)). Qed.
Lemma lem4355746 {A B : Type'} (t : B -> Prop) (y : B) (x' : A) (s : A -> Prop) (x : A) (h1 : term237 A B t y x' s x) : term106 A s x'.
Proof. exact (EQ_MP (@lem4355745 A B t y x' s x h1) (@lem4355685 A B t y x' s x h1)). Qed.
Lemma lem4355776 {A B : Type'} (t : B -> Prop) (y : B) (x' : A) (s : A -> Prop) (x : A) (h1 : term237 A B t y x' s x) : s x'.
Proof. exact (proj1 (@lem4355570 A B t y x' s x h1)). Qed.
Lemma lem4355777 {A B : Type'} (t : B -> Prop) (y : B) (x' : A) (s : A -> Prop) (x : A) (h1 : term237 A B t y x' s x) : term315 A s x'.
Proof. exact (fun h0 : term106 A s x' => @lem4355776 A B t y x' s x h1). Qed.
Lemma lem4355779 (p : Prop) : (term316 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4355780 {A : Type'} (s : A -> Prop) (x' : A) : (term315 A s x') = (s x').
Proof. exact (@lem4355779 (s x')). Qed.
Lemma lem4355781 {A B : Type'} (t : B -> Prop) (y : B) (x' : A) (s : A -> Prop) (x : A) (h1 : term237 A B t y x' s x) : s x'.
Proof. exact (EQ_MP (@lem4355780 A s x') (@lem4355777 A B t y x' s x h1)). Qed.
Lemma lem4355784 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4355786 {A : Type'} (s : A -> Prop) (x' : A) : (term106 A s x') = (term317 A s x').
Proof. exact (@lem4355784 (s x')). Qed.
Lemma lem4355789 {A B : Type'} (t : B -> Prop) (y : B) (x' : A) (s : A -> Prop) (x : A) (h1 : term237 A B t y x' s x) : term317 A s x'.
Proof. exact (EQ_MP (@lem4355786 A s x') (@lem4355746 A B t y x' s x h1)). Qed.
Lemma lem4355792 {A B : Type'} (t : B -> Prop) (y : B) (x' : A) (s : A -> Prop) (x : A) (h1 : term237 A B t y x' s x) : False.
Proof. exact (@lem4355789 A B t y x' s x h1 (@lem4355781 A B t y x' s x h1)). Qed.
Lemma lem4355793 {A B : Type'} (t : B -> Prop) (y : B) (x' : A) (s : A -> Prop) (x : A) (h1 : term237 A B t y x' s x) : term318.
Proof. exact (fun h0 : ~ False => @lem4355792 A B t y x' s x h1). Qed.
Lemma lem4355795 (p : Prop) : (term316 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4355796 : term318 = False.
Proof. exact (@lem4355795 False). Qed.
Lemma lem4355827 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) (h1 : term201 A B t s x) : s x.
Proof. exact (proj2 (@lem4355568 A B t s x h1)). Qed.
Lemma lem4355828 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) (h1 : term201 A B t s x) : term315 A s x.
Proof. exact (fun h0 : term106 A s x => @lem4355827 A B t s x h1). Qed.
Lemma lem4355830 (p : Prop) : (term316 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4355831 {A : Type'} (s : A -> Prop) (x : A) : (term315 A s x) = (s x).
Proof. exact (@lem4355830 (s x)). Qed.
Lemma lem4355832 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) (h1 : term201 A B t s x) : s x.
Proof. exact (EQ_MP (@lem4355831 A s x) (@lem4355828 A B t s x h1)). Qed.
Lemma lem4355834 {B : Type'} (t : B -> Prop) (x'' : B) (h1 : t x'') : t x''.
Proof. exact (h1). Qed.
Lemma lem4355835 {B : Type'} (t : B -> Prop) (x'' : B) (h1 : t x'') : term315 B t x''.
Proof. exact (fun h0 : term106 B t x'' => @lem4355834 B t x'' h1). Qed.
Lemma lem4355837 (p : Prop) : (term316 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4355838 {B : Type'} (t : B -> Prop) (x'' : B) : (term315 B t x'') = (t x'').
Proof. exact (@lem4355837 (t x'')). Qed.
Lemma lem4355839 {B : Type'} (t : B -> Prop) (x'' : B) (h1 : t x'') : t x''.
Proof. exact (EQ_MP (@lem4355838 B t x'') (@lem4355835 B t x'' h1)). Qed.
Lemma lem4355841 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem4355842 {A : Type'} (x : A) : x = x.
Proof. exact (@lem4355841 A x). Qed.
Lemma lem4355843 {A : Type'} (x : A) : term319 A x.
Proof. exact (fun h0 : term320 A x => @lem4355842 A x). Qed.
Lemma lem4355845 (p : Prop) : (term316 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4355846 {A : Type'} (x : A) : (term319 A x) = (x = x).
Proof. exact (@lem4355845 (x = x)). Qed.
Lemma lem4355847 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem4355846 A x) (@lem4355843 A x)). Qed.
Lemma lem4355849 (a : Prop) (b : Prop) : (term321 a b) = (term322 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4355850 {A B : Type'} (t : B -> Prop) (_49797 : B) (x : A) (_49796 : A) : (term290 A B t _49797 x _49796) = (term323 A B t _49797 x _49796).
Proof. exact (@lem4355849 (t _49797) (x = _49796)). Qed.
Lemma lem4355851 {A : Type'} (s : A -> Prop) (_49796 : A) : (term187 A s _49796) = (term187 A s _49796).
Proof. exact (eq_refl (term187 A s _49796)). Qed.
Lemma lem4355852 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (_49797 : B) (x : A) (_49796 : A) : (term305 A B s t _49797 x _49796) = (term324 A B s t _49797 x _49796).
Proof. exact (MK_COMB (@lem4355851 A s _49796) (@lem4355850 A B t _49797 x _49796)). Qed.
Lemma lem4355854 (a : Prop) (b : Prop) : (term321 a b) = (term322 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4355855 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (_49797 : B) (x : A) (_49796 : A) : (term324 A B s t _49797 x _49796) = (term325 A B s t _49797 x _49796).
Proof. exact (@lem4355854 (s _49796) (term113 A B t _49797 x _49796)). Qed.
Lemma lem4355856 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (_49797 : B) (x : A) (_49796 : A) : (term305 A B s t _49797 x _49796) = (term325 A B s t _49797 x _49796).
Proof. exact (TRANS (@lem4355852 A B s t _49797 x _49796) (@lem4355855 A B s t _49797 x _49796)). Qed.
Lemma lem4355858 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4355859 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (_49797 : B) (x : A) (_49796 : A) : (term325 A B s t _49797 x _49796) = (term326 A B s t _49797 x _49796).
Proof. exact (@lem4355858 (term114 A B s t _49797 x _49796)). Qed.
Lemma lem4355860 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (_49797 : B) (x : A) (_49796 : A) : (term305 A B s t _49797 x _49796) = (term326 A B s t _49797 x _49796).
Proof. exact (TRANS (@lem4355856 A B s t _49797 x _49796) (@lem4355859 A B s t _49797 x _49796)). Qed.
Lemma lem4355862 {A B : Type'} (x : A) (t : B -> Prop) (x'' : B) (h1 : t x'') : term327 A B t x'' x.
Proof. exact (conj (@lem4355839 B t x'' h1) (@lem4355847 A x)). Qed.
Lemma lem4355863 {A B : Type'} (x'' : B) (t : B -> Prop) (s : A -> Prop) (x : A) (h1 : t x'') (h2 : term201 A B t s x) : term328 A B s t x'' x.
Proof. exact (conj (@lem4355832 A B t s x h2) (@lem4355862 A B x t x'' h1)). Qed.
Lemma lem4355865 {A B : Type'} (_49797 : B) (_49796 : A) (t : B -> Prop) (s : A -> Prop) (x : A) (h1 : term201 A B t s x) : term326 A B s t _49797 x _49796.
Proof. exact (EQ_MP (@lem4355860 A B s t _49797 x _49796) (@lem4355703 A B _49797 _49796 t s x h1)). Qed.
Lemma lem4355866 {A B : Type'} (_49797 : B) (_49796 : A) (t : B -> Prop) (s : A -> Prop) (x : A) (h1 : term201 A B t s x) : term326 A B s t _49797 x _49796.
Proof. exact (@lem4355865 A B _49797 _49796 t s x h1). Qed.
Lemma lem4355867 {A B : Type'} (x'' : B) (t : B -> Prop) (s : A -> Prop) (x : A) (h1 : term201 A B t s x) : term329 A B s t x'' x.
Proof. exact (@lem4355866 A B x'' x t s x h1). Qed.
Lemma lem4355870 {A B : Type'} (x'' : B) (t : B -> Prop) (s : A -> Prop) (x : A) (h1 : t x'') (h2 : term201 A B t s x) : False.
Proof. exact (@lem4355867 A B x'' t s x h2 (@lem4355863 A B x'' t s x h1 h2)). Qed.
Lemma lem4355871 {A B : Type'} (x'' : B) (t : B -> Prop) (s : A -> Prop) (x : A) (h1 : t x'') (h2 : term201 A B t s x) : term318.
Proof. exact (fun h0 : ~ False => @lem4355870 A B x'' t s x h1 h2). Qed.
Lemma lem4355873 (p : Prop) : (term316 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4355874 : term318 = False.
Proof. exact (@lem4355873 False). Qed.
Lemma lem4355875 {A B : Type'} (x'' : B) (t : B -> Prop) (s : A -> Prop) (x : A) (h1 : t x'') (h2 : term201 A B t s x) : False.
Proof. exact (EQ_MP (@lem4355874) (@lem4355871 A B x'' t s x h1 h2)). Qed.
Lemma lem4355876 {A B : Type'} (t : B -> Prop) (y : B) (x' : A) (s : A -> Prop) (x : A) (h1 : term237 A B t y x' s x) : False.
Proof. exact (EQ_MP (@lem4355796) (@lem4355793 A B t y x' s x h1)). Qed.
Lemma lem4355877 {A B : Type'} (x'' : B) (t : B -> Prop) (s : A -> Prop) (x : A) (h1 : t x'') (h2 : term201 A B t s x) : (t x'') = False.
Proof. exact (prop_ext (fun h3 : t x'' => @lem4355875 A B x'' t s x h1 h2) (fun h3 : False => @lem4355693 B t x'' h1)). Qed.
Lemma lem4355878 {A B : Type'} (x'' : B) (t : B -> Prop) (s : A -> Prop) (x : A) (h1 : t x'') (h2 : term201 A B t s x) : False.
Proof. exact (EQ_MP (@lem4355877 A B x'' t s x h1 h2) (@lem4355693 B t x'' h1)). Qed.
Lemma lem4355879 {A B : Type'} (x'' : B) (t : B -> Prop) (s : A -> Prop) (x : A) (h1 : t x'') (h2 : term201 A B t s x) : (t x'') = False.
Proof. exact (prop_ext (fun h3 : t x'' => @lem4355878 A B x'' t s x h1 h2) (fun h3 : False => @lem4355600 B t x'' h1)). Qed.
Lemma lem4355880 {A B : Type'} (x'' : B) (t : B -> Prop) (s : A -> Prop) (x : A) (h1 : t x'') (h2 : term201 A B t s x) : False.
Proof. exact (EQ_MP (@lem4355879 A B x'' t s x h1 h2) (@lem4355600 B t x'' h1)). Qed.
Lemma lem4355881 {A B : Type'} (x'' : B) (t : B -> Prop) (s : A -> Prop) (x : A) (h1 : t x'') (h2 : term201 A B t s x) : (t x'') = False.
Proof. exact (prop_ext (fun h3 : t x'' => @lem4355880 A B x'' t s x h1 h2) (fun h3 : False => @lem4355600 B t x'' h1)). Qed.
Lemma lem4355882 {A B : Type'} (x'' : B) (t : B -> Prop) (s : A -> Prop) (x : A) (h1 : t x'') (h2 : term201 A B t s x) : False.
Proof. exact (EQ_MP (@lem4355881 A B x'' t s x h1 h2) (@lem4355600 B t x'' h1)). Qed.
Lemma lem4355883 {A B : Type'} (x'' : B) (y : B) (x' : A) (t : B -> Prop) (s : A -> Prop) (x : A) (h1 : t x'') (h2 : term273 A B y x' t s x) : False.
Proof. exact (or_elim (@lem4355562 A B y x' t s x h2) (fun h0 : term237 A B t y x' s x => @lem4355876 A B t y x' s x h0) (fun h0 : term201 A B t s x => @lem4355882 A B x'' t s x h1 h0)). Qed.
Lemma lem4355884 {A B : Type'} (x'' : B) (y : B) (x' : A) (t : B -> Prop) (s : A -> Prop) (x : A) (h1 : t x'') (h2 : term273 A B y x' t s x) : (t x'') = False.
Proof. exact (prop_ext (fun h3 : t x'' => @lem4355883 A B x'' y x' t s x h1 h2) (fun h3 : False => @lem4355566 B t x'' h1)). Qed.
Lemma lem4355885 {A B : Type'} (x'' : B) (y : B) (x' : A) (t : B -> Prop) (s : A -> Prop) (x : A) (h1 : t x'') (h2 : term273 A B y x' t s x) : False.
Proof. exact (EQ_MP (@lem4355884 A B x'' y x' t s x h1 h2) (@lem4355566 B t x'' h1)). Qed.
Lemma lem4355886 {A B : Type'} (x'' : B) (y : B) (x' : A) (t : B -> Prop) (s : A -> Prop) (x : A) (h1 : t x'') (h2 : term273 A B y x' t s x) : (term273 A B y x' t s x) = False.
Proof. exact (prop_ext (fun h3 : term273 A B y x' t s x => @lem4355885 A B x'' y x' t s x h1 h2) (fun h3 : False => @lem4355562 A B y x' t s x h2)). Qed.
Lemma lem4355887 {A B : Type'} (x'' : B) (y : B) (x' : A) (t : B -> Prop) (s : A -> Prop) (x : A) (h1 : t x'') (h2 : term273 A B y x' t s x) : False.
Proof. exact (EQ_MP (@lem4355886 A B x'' y x' t s x h1 h2) (@lem4355562 A B y x' t s x h2)). Qed.
Lemma lem4355888 {A B : Type'} (y : B) (x' : A) (t : B -> Prop) (s : A -> Prop) (x : A) (h1 : term110 B t) (h2 : term273 A B y x' t s x) : False.
Proof. exact (ex_elim (@lem4355202 B t h1) (fun x'' : B => fun h0 : term163 B t x'' => @lem4355887 A B x'' y x' t s x h0 h2)). Qed.
Lemma lem4355889 {A B : Type'} (x' : A) (s : A -> Prop) (x : A) (t : B -> Prop) (h1 : term276 A B x' t s x) (h2 : term110 B t) : False.
Proof. exact (ex_elim (@lem4355496 A B x' t s x h1) (fun y : B => fun h0 : term275 A B x' t s x y => @lem4355888 A B y x' t s x h2 h0)). Qed.
Lemma lem4355890 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) (h1 : term110 B t) (h2 : term167 A B t s x) : False.
Proof. exact (ex_elim (@lem4355495 A B t s x h2) (fun x' : A => fun h0 : term277 A B t s x x' => @lem4355889 A B x' s x t h0 h1)). Qed.
Lemma lem4355891 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) (h1 : term110 B t) (h2 : term167 A B t s x) : (term167 A B t s x) = False.
Proof. exact (prop_ext (fun h3 : term167 A B t s x => @lem4355890 A B t s x h1 h2) (fun h3 : False => @lem4355180 A B t s x h2)). Qed.
Lemma lem4355892 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) (h1 : term110 B t) (h2 : term167 A B t s x) : False.
Proof. exact (EQ_MP (@lem4355891 A B t s x h1 h2) (@lem4355180 A B t s x h2)). Qed.
Lemma lem4355893 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (h1 : term110 B t) : term166 A B t s x.
Proof. exact (fun h0 : term167 A B t s x => @lem4355892 A B t s x h1 h0). Qed.
Lemma lem4355894 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (h1 : term110 B t) : (term150 A B s t x) = (s x).
Proof. exact (EQ_MP (@lem4355179 A B t s x) (@lem4355893 A B s x t h1)). Qed.
Lemma lem4355899 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term110 B t) : term153 A B t s.
Proof. exact (fun x : A => @lem4355894 A B s x t h1). Qed.
Lemma lem4355900 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : term154 A B t s.
Proof. exact (fun h0 : term110 B t => @lem4355899 A B s t h0). Qed.
Lemma lem4355905 {A B : Type'} (s : A -> Prop) : term158 A B s.
Proof. exact (fun t : B -> Prop => @lem4355900 A B t s). Qed.
Lemma lem4355910 {A B : Type'} : term162 A B.
Proof. exact (fun s : A -> Prop => @lem4355905 A B s). Qed.
Lemma lem4355911 {A B : Type'} : term161 A B.
Proof. exact (EQ_MP (@lem4355174 A B) (@lem4355910 A B)). Qed.
Lemma lem4355912 {A B : Type'} (s : A -> Prop) : term330 A B s.
Proof. exact (@lem4355911 A B s). Qed.
Lemma lem4355913 {A B : Type'} (s : A -> Prop) : (term330 A B s) = (term157 A B s).
Proof. exact (eq_refl (term330 A B s)). Qed.
Lemma lem4355914 {A B : Type'} (s : A -> Prop) : term157 A B s.
Proof. exact (EQ_MP (@lem4355913 A B s) (@lem4355912 A B s)). Qed.
Lemma lem4355915 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term331 A B s t.
Proof. exact (@lem4355914 A B s t). Qed.
Lemma lem4355916 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term331 A B s t) = (term124 A B t s).
Proof. exact (eq_refl (term331 A B s t)). Qed.
Lemma lem4355917 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : term124 A B t s.
Proof. exact (EQ_MP (@lem4355916 A B t s) (@lem4355915 A B s t)). Qed.
Lemma lem4355919 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : term124 A B t s.
Proof. exact (@lem4354938 A B t s (@lem4355917 A B t s)). Qed.
Lemma lem4355920 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term125 A B t s) : False.
Proof. exact (@lem4355919 A B t s (@lem4354922 A B t s h1)). Qed.
Lemma lem4355921 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term125 A B t s) : (term125 A B t s) = False.
Proof. exact (prop_ext (fun h2 : term125 A B t s => @lem4355920 A B t s h1) (fun h2 : False => @lem4354922 A B t s h1)). Qed.
Lemma lem4355922 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term125 A B t s) : False.
Proof. exact (EQ_MP (@lem4355921 A B t s h1) (@lem4354922 A B t s h1)). Qed.
Lemma lem4355923 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : term124 A B t s.
Proof. exact (fun h0 : term125 A B t s => @lem4355922 A B t s h0). Qed.
Lemma lem4355924 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : term122 A B t s.
Proof. exact (EQ_MP (@lem4354921 A B t s) (@lem4355923 A B t s)). Qed.
Lemma lem4355925 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : term103 A B t s.
Proof. exact (EQ_MP (@lem4354917 A B t s) (@lem4355924 A B t s)). Qed.
Lemma lem4355926 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : term102 A B t s.
Proof. exact (EQ_MP (@lem4354811 A B t s) (@lem4355925 A B t s)). Qed.
Lemma lem4355927 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term43 B t) : term98 A B t s.
Proof. exact (@lem4355926 A B t s (@lem4354510 B t h1)). Qed.
Lemma lem4355928 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term43 B t) : term65 A B t s.
Proof. exact (EQ_MP (@lem4354752 A B t s) (@lem4355927 A B s t h1)). Qed.
Lemma lem4355929 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term43 B t) : term56 A B t s.
Proof. exact (EQ_MP (@lem4354662 A B t s) (@lem4355928 A B s t h1)). Qed.
Lemma lem4355932 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term43 B t) : (term29 A B s t) = s.
Proof. exact (EQ_MP (@lem4354636 A B t s) (@lem4355929 A B s t h1)). Qed.
Lemma lem4355933 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term43 B t) : (term43 B t) = ((term29 A B s t) = s).
Proof. exact (prop_ext (fun h2 : term43 B t => @lem4355932 A B s t h1) (fun h2 : (term29 A B s t) = s => @lem4354510 B t h1)). Qed.
Lemma lem4355934 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term43 B t) : (term29 A B s t) = s.
Proof. exact (EQ_MP (@lem4355933 A B s t h1) (@lem4354510 B t h1)). Qed.
Lemma lem4355935 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : term32 A B t s.
Proof. exact (fun h0 : term43 B t => @lem4355934 A B s t h0). Qed.
Lemma lem4355936 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : t = (@EMPTY B)) : (term29 A B s t) = (@EMPTY A).
Proof. exact (EQ_MP (@lem4354563 A B s t h1) (@lem0)). Qed.
Lemma lem4355937 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : t = (@EMPTY B)) : (t = (@EMPTY B)) = ((term29 A B s t) = (@EMPTY A)).
Proof. exact (prop_ext (fun h2 : t = (@EMPTY B) => @lem4355936 A B s t h1) (fun h2 : (term29 A B s t) = (@EMPTY A) => @lem4354493 B t h1)). Qed.
Lemma lem4355938 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : t = (@EMPTY B)) : (term29 A B s t) = (@EMPTY A).
Proof. exact (EQ_MP (@lem4355937 A B s t h1) (@lem4354493 B t h1)). Qed.
Lemma lem4355939 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term36 A B s t.
Proof. exact (fun h0 : t = (@EMPTY B) => @lem4355938 A B s t h0). Qed.
Lemma lem4355940 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : term39 A B t s.
Proof. exact (conj (@lem4355939 A B s t) (@lem4355935 A B t s)). Qed.
Lemma lem4355941 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term29 A B s t) = (term40 A B t s).
Proof. exact (EQ_MP (@lem4354492 A B t s) (@lem4355940 A B t s)). Qed.
Lemma lem4355946 {A B : Type'} (s : A -> Prop) : term332 A B s.
Proof. exact (fun t : B -> Prop => @lem4355941 A B t s). Qed.
Lemma lem4355951 {A B : Type'} : term333 A B.
Proof. exact (fun s : A -> Prop => @lem4355946 A B s). Qed.
