Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm4372722_term_abbrevs.
Require Import EXTENSION_spec.
Require Import FORALL_PAIR_THM_spec.
Require Import IN_CROSS_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Require Import thm3464405_spec.
Require Import thm3464408_spec.
Lemma lem4372444 {_103718 _103721 : Type'} (x : _103718) : term0 _103718 _103721 x.
Proof. exact (@lem4325365 _103718 _103721 x). Qed.
Lemma lem4372445 {_103718 _103721 : Type'} (x : _103718) : (term0 _103718 _103721 x) = (term1 _103718 _103721 x).
Proof. exact (eq_refl (term0 _103718 _103721 x)). Qed.
Lemma lem4372446 {_103718 _103721 : Type'} (x : _103718) : term1 _103718 _103721 x.
Proof. exact (EQ_MP (@lem4372445 _103718 _103721 x) (@lem4372444 _103718 _103721 x)). Qed.
Lemma lem4372447 {_103718 _103721 : Type'} (x : _103718) (y : _103721) : term2 _103718 _103721 x y.
Proof. exact (@lem4372446 _103718 _103721 x y). Qed.
Lemma lem4372448 {_103718 _103721 : Type'} (x : _103718) (y : _103721) : (term2 _103718 _103721 x y) = (term3 _103718 _103721 x y).
Proof. exact (eq_refl (term2 _103718 _103721 x y)). Qed.
Lemma lem4372449 {_103718 _103721 : Type'} (x : _103718) (y : _103721) : term3 _103718 _103721 x y.
Proof. exact (EQ_MP (@lem4372448 _103718 _103721 x y) (@lem4372447 _103718 _103721 x y)). Qed.
Lemma lem4372450 {_103718 _103721 : Type'} (x : _103718) (y : _103721) (s : _103718 -> Prop) : term4 _103718 _103721 x y s.
Proof. exact (@lem4372449 _103718 _103721 x y s). Qed.
Lemma lem4372451 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) : (term4 _103718 _103721 x y s) = (term5 _103718 _103721 x s y).
Proof. exact (eq_refl (term4 _103718 _103721 x y s)). Qed.
Lemma lem4372452 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) : term5 _103718 _103721 x s y.
Proof. exact (EQ_MP (@lem4372451 _103718 _103721 x s y) (@lem4372450 _103718 _103721 x y s)). Qed.
Lemma lem4372453 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : term6 _103718 _103721 x s y t.
Proof. exact (@lem4372452 _103718 _103721 x s y t). Qed.
Lemma lem4372454 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term6 _103718 _103721 x s y t) = ((term7 _103718 _103721 x y s t) = (term8 _103718 _103721 x s y t)).
Proof. exact (eq_refl (term6 _103718 _103721 x s y t)). Qed.
Lemma lem4372480 {_83095 : Type'} : term9 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem4372481 {_83095 : Type'} (p : _83095 -> Prop) : term10 _83095 p.
Proof. exact (@lem4372480 _83095 p). Qed.
Lemma lem4372482 {_83095 : Type'} (p : _83095 -> Prop) : (term10 _83095 p) = (term11 _83095 p).
Proof. exact (eq_refl (term10 _83095 p)). Qed.
Lemma lem4372483 {_83095 : Type'} (p : _83095 -> Prop) : term11 _83095 p.
Proof. exact (EQ_MP (@lem4372482 _83095 p) (@lem4372481 _83095 p)). Qed.
Lemma lem4372484 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term12 _83095 p x.
Proof. exact (@lem4372483 _83095 p x). Qed.
Lemma lem4372485 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term12 _83095 p x) = ((term13 _83095 x p) = (p x)).
Proof. exact (eq_refl (term12 _83095 p x)). Qed.
Lemma lem4372494 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : term14 _5106 _5107 P.
Proof. exact (@lem49909 _5106 _5107 P). Qed.
Lemma lem4372495 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term14 _5106 _5107 P) = ((term15 _5106 _5107 P) = (term16 _5106 _5107 P)).
Proof. exact (eq_refl (term14 _5106 _5107 P)). Qed.
Lemma lem4372497 {A : Type'} (s : A -> Prop) : term17 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem4372498 {A : Type'} (s : A -> Prop) : (term17 A s) = (term18 A s).
Proof. exact (eq_refl (term17 A s)). Qed.
Lemma lem4372499 {A : Type'} (s : A -> Prop) : term18 A s.
Proof. exact (EQ_MP (@lem4372498 A s) (@lem4372497 A s)). Qed.
Lemma lem4372500 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term19 A s t.
Proof. exact (@lem4372499 A s t). Qed.
Lemma lem4372501 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term19 A s t) = ((s = t) = (term20 A s t)).
Proof. exact (eq_refl (term19 A s t)). Qed.
Lemma lem4372518 {_89711 _89725 : Type'} : term21 _89711 _89725.
Proof. exact (EQ_MP (@lem3464408 _89711 _89725) (@lem3464405 _89711 _89725)). Qed.
Lemma lem4372519 {_89711 _89725 : Type'} (P : _89725 -> Prop) : term22 _89711 _89725 P.
Proof. exact (@lem4372518 _89711 _89725 P). Qed.
Lemma lem4372520 {_89711 _89725 : Type'} (P : _89725 -> Prop) : (term22 _89711 _89725 P) = (term23 _89711 _89725 P).
Proof. exact (eq_refl (term22 _89711 _89725 P)). Qed.
Lemma lem4372521 {_89711 _89725 : Type'} (P : _89725 -> Prop) : term23 _89711 _89725 P.
Proof. exact (EQ_MP (@lem4372520 _89711 _89725 P) (@lem4372519 _89711 _89725 P)). Qed.
Lemma lem4372522 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) : term24 _89711 _89725 P f.
Proof. exact (@lem4372521 _89711 _89725 P f). Qed.
Lemma lem4372523 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) : (term24 _89711 _89725 P f) = ((term25 _89711 _89725 P f) = (term26 _89711 _89725 P f)).
Proof. exact (eq_refl (term24 _89711 _89725 P f)). Qed.
Lemma lem4372528 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term20 A s t).
Proof. exact (EQ_MP (@lem4372501 A s t) (@lem4372500 A s t)). Qed.
Lemma lem4372529 {_104907 _104908 : Type'} (s : type1210 _104907 _104908) (t : type1210 _104907 _104908) : (s = t) = (term27 _104907 _104908 s t).
Proof. exact (@lem4372528 (prod _104907 _104908) s t). Qed.
Lemma lem4372530 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : ((term28 _104907 _104908 f g) = (term29 _104907 _104908 g)) = (term30 _104907 _104908 f g).
Proof. exact (@lem4372529 _104907 _104908 (term28 _104907 _104908 f g) (term29 _104907 _104908 g)). Qed.
Lemma lem4372536 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term15 _5106 _5107 P) = (term16 _5106 _5107 P).
Proof. exact (EQ_MP (@lem4372495 _5106 _5107 P) (@lem4372494 _5106 _5107 P)). Qed.
Lemma lem4372537 {_104907 _104908 : Type'} (P : type1210 _104907 _104908) : (term31 _104907 _104908 P) = (term32 _104907 _104908 P).
Proof. exact (@lem4372536 _104908 _104907 P). Qed.
Lemma lem4372538 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : (term33 _104907 _104908 f g) = (term34 _104907 _104908 f g).
Proof. exact (@lem4372537 _104907 _104908 (term35 _104907 _104908 f g)). Qed.
Lemma lem4372539 {_104907 _104908 : Type'} (f : type686 _104907) (x : prod _104907 _104908) (g : type686 _104908) : (term36 _104907 _104908 f g x) = ((term37 _104907 _104908 x f g) = (term38 _104907 _104908 x g)).
Proof. exact (eq_refl (term36 _104907 _104908 f g x)). Qed.
Lemma lem4372540 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : (term39 _104907 _104908 f g) = (term35 _104907 _104908 f g).
Proof. exact (fun_ext (fun x : prod _104907 _104908 => @lem4372539 _104907 _104908 f x g)). Qed.
Lemma lem4372541 {_104907 _104908 : Type'} : (@all (prod _104907 _104908)) = (@all (prod _104907 _104908)).
Proof. exact (eq_refl (@all (prod _104907 _104908))). Qed.
Lemma lem4372542 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : (term33 _104907 _104908 f g) = (term30 _104907 _104908 f g).
Proof. exact (MK_COMB (@lem4372541 _104907 _104908) (@lem4372540 _104907 _104908 f g)). Qed.
Lemma lem4372543 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4372544 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : (term40 _104907 _104908 f g) = (term41 _104907 _104908 f g).
Proof. exact (MK_COMB (@lem4372543) (@lem4372542 _104907 _104908 f g)). Qed.
Lemma lem4372545 {_104907 _104908 : Type'} (f : type686 _104907) (p1 : _104907) (p2 : _104908) (g : type686 _104908) : (term42 _104907 _104908 f g p1 p2) = ((term43 _104907 _104908 p1 p2 f g) = (term44 _104907 _104908 p1 p2 g)).
Proof. exact (eq_refl (term42 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4372546 {_104907 _104908 : Type'} (f : type686 _104907) (p1 : _104907) (g : type686 _104908) : (term45 _104907 _104908 f g p1) = (term46 _104907 _104908 f p1 g).
Proof. exact (fun_ext (fun p2 : _104908 => @lem4372545 _104907 _104908 f p1 p2 g)). Qed.
Lemma lem4372547 {_104908 : Type'} : (@all _104908) = (@all _104908).
Proof. exact (eq_refl (@all _104908)). Qed.
Lemma lem4372548 {_104907 _104908 : Type'} (f : type686 _104907) (p1 : _104907) (g : type686 _104908) : (term47 _104907 _104908 f g p1) = (term48 _104907 _104908 f p1 g).
Proof. exact (MK_COMB (@lem4372547 _104908) (@lem4372546 _104907 _104908 f p1 g)). Qed.
Lemma lem4372549 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : (term49 _104907 _104908 f g) = (term50 _104907 _104908 f g).
Proof. exact (fun_ext (fun p1 : _104907 => @lem4372548 _104907 _104908 f p1 g)). Qed.
Lemma lem4372550 {_104907 : Type'} : (@all _104907) = (@all _104907).
Proof. exact (eq_refl (@all _104907)). Qed.
Lemma lem4372551 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : (term34 _104907 _104908 f g) = (term51 _104907 _104908 f g).
Proof. exact (MK_COMB (@lem4372550 _104907) (@lem4372549 _104907 _104908 f g)). Qed.
Lemma lem4372552 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : ((term33 _104907 _104908 f g) = (term34 _104907 _104908 f g)) = ((term30 _104907 _104908 f g) = (term51 _104907 _104908 f g)).
Proof. exact (MK_COMB (@lem4372544 _104907 _104908 f g) (@lem4372551 _104907 _104908 f g)). Qed.
Lemma lem4372553 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : (term30 _104907 _104908 f g) = (term51 _104907 _104908 f g).
Proof. exact (EQ_MP (@lem4372552 _104907 _104908 f g) (@lem4372538 _104907 _104908 f g)). Qed.
Lemma lem4372560 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : ((term28 _104907 _104908 f g) = (term29 _104907 _104908 g)) = (term51 _104907 _104908 f g).
Proof. exact (TRANS (@lem4372530 _104907 _104908 f g) (@lem4372553 _104907 _104908 f g)). Qed.
Lemma lem4372572 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term7 _103718 _103721 x y s t) = (term8 _103718 _103721 x s y t).
Proof. exact (EQ_MP (@lem4372454 _103718 _103721 x s y t) (@lem4372453 _103718 _103721 x s y t)). Qed.
Lemma lem4372573 {_104907 _104908 : Type'} (x : _104907) (s : _104907 -> Prop) (y : _104908) (t : _104908 -> Prop) : (term7 _104907 _104908 x y s t) = (term8 _104907 _104908 x s y t).
Proof. exact (@lem4372572 _104907 _104908 x s y t). Qed.
Lemma lem4372574 {_104907 _104908 : Type'} (p1 : _104907) (f : type686 _104907) (p2 : _104908) (g : type686 _104908) : (term43 _104907 _104908 p1 p2 f g) = (term52 _104907 _104908 p1 f p2 g).
Proof. exact (@lem4372573 _104907 _104908 p1 (@INTERS _104907 f) p2 (@INTERS _104908 g)). Qed.
Lemma lem4372578 {_104907 : Type'} (f : type686 _104907) (h1 : f = (@EMPTY (_104907 -> Prop))) : f = (@EMPTY (_104907 -> Prop)).
Proof. exact (h1). Qed.
Lemma lem4372579 {_104907 : Type'} : (@INTERS _104907) = (@INTERS _104907).
Proof. exact (eq_refl (@INTERS _104907)). Qed.
Lemma lem4372580 {_104907 : Type'} (f : type686 _104907) (h1 : f = (@EMPTY (_104907 -> Prop))) : (@INTERS _104907 f) = (@INTERS _104907 (@EMPTY (_104907 -> Prop))).
Proof. exact (MK_COMB (@lem4372579 _104907) (@lem4372578 _104907 f h1)). Qed.
Lemma lem4372581 {_104907 : Type'} (p1 : _104907) : (@IN _104907 p1) = (@IN _104907 p1).
Proof. exact (eq_refl (@IN _104907 p1)). Qed.
Lemma lem4372582 {_104907 : Type'} (p1 : _104907) (f : type686 _104907) (h1 : f = (@EMPTY (_104907 -> Prop))) : (term53 _104907 p1 f) = (term54 _104907 p1).
Proof. exact (MK_COMB (@lem4372581 _104907 p1) (@lem4372580 _104907 f h1)). Qed.
Lemma lem4372583 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4372584 {_104907 : Type'} (p1 : _104907) (f : type686 _104907) (h1 : f = (@EMPTY (_104907 -> Prop))) : (term55 _104907 p1 f) = (term56 _104907 p1).
Proof. exact (MK_COMB (@lem4372583) (@lem4372582 _104907 p1 f h1)). Qed.
Lemma lem4372585 {_104908 : Type'} (p2 : _104908) (g : type686 _104908) : (term53 _104908 p2 g) = (term53 _104908 p2 g).
Proof. exact (eq_refl (term53 _104908 p2 g)). Qed.
Lemma lem4372586 {_104907 _104908 : Type'} (p1 : _104907) (p2 : _104908) (g : type686 _104908) (f : type686 _104907) (h1 : f = (@EMPTY (_104907 -> Prop))) : (term52 _104907 _104908 p1 f p2 g) = (term57 _104907 _104908 p1 p2 g).
Proof. exact (MK_COMB (@lem4372584 _104907 p1 f h1) (@lem4372585 _104908 p2 g)). Qed.
Lemma lem4372589 {_104907 _104908 : Type'} (p1 : _104907) (p2 : _104908) (g : type686 _104908) (f : type686 _104907) (h1 : f = (@EMPTY (_104907 -> Prop))) : (term43 _104907 _104908 p1 p2 f g) = (term57 _104907 _104908 p1 p2 g).
Proof. exact (TRANS (@lem4372574 _104907 _104908 p1 f p2 g) (@lem4372586 _104907 _104908 p1 p2 g f h1)). Qed.
Lemma lem4372590 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4372591 {_104907 _104908 : Type'} (p1 : _104907) (p2 : _104908) (g : type686 _104908) (f : type686 _104907) (h1 : f = (@EMPTY (_104907 -> Prop))) : (term58 _104907 _104908 p1 p2 f g) = (term59 _104907 _104908 p1 p2 g).
Proof. exact (MK_COMB (@lem4372590) (@lem4372589 _104907 _104908 p1 p2 g f h1)). Qed.
Lemma lem4372593 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) : (term25 _89711 _89725 P f) = (term26 _89711 _89725 P f).
Proof. exact (EQ_MP (@lem4372523 _89711 _89725 P f) (@lem4372522 _89711 _89725 P f)). Qed.
Lemma lem4372594 {_104907 _104908 : Type'} (P : type686 _104908) (f : type857 _104907 _104908) : (term60 _104907 _104908 P f) = (term61 _104907 _104908 P f).
Proof. exact (@lem4372593 (prod _104907 _104908) (_104908 -> Prop) P f). Qed.
Lemma lem4372595 {_104907 _104908 : Type'} (g : type686 _104908) : (term62 _104907 _104908 g) = (term63 _104907 _104908 g).
Proof. exact (@lem4372594 _104907 _104908 (term64 _104908 g) (term65 _104907 _104908)). Qed.
Lemma lem4372596 {_104908 : Type'} (t : _104908 -> Prop) (g : type686 _104908) : (term66 _104908 g t) = (@IN (_104908 -> Prop) t g).
Proof. exact (eq_refl (term66 _104908 g t)). Qed.
Lemma lem4372597 {_104907 _104908 : Type'} (GEN_PVAR_134 : type1210 _104907 _104908) : (@SETSPEC ((prod _104907 _104908) -> Prop) GEN_PVAR_134) = (@SETSPEC ((prod _104907 _104908) -> Prop) GEN_PVAR_134).
Proof. exact (eq_refl (@SETSPEC ((prod _104907 _104908) -> Prop) GEN_PVAR_134)). Qed.
Lemma lem4372598 {_104907 _104908 : Type'} (GEN_PVAR_134 : type1210 _104907 _104908) (t : _104908 -> Prop) (g : type686 _104908) : (term67 _104907 _104908 GEN_PVAR_134 g t) = (term68 _104907 _104908 GEN_PVAR_134 t g).
Proof. exact (MK_COMB (@lem4372597 _104907 _104908 GEN_PVAR_134) (@lem4372596 _104908 t g)). Qed.
Lemma lem4372599 {_104907 _104908 : Type'} (t : _104908 -> Prop) : (term69 _104907 _104908 t) = (@CROSS _104908 _104907 (@UNIV _104907) t).
Proof. exact (eq_refl (term69 _104907 _104908 t)). Qed.
Lemma lem4372600 {_104907 _104908 : Type'} (GEN_PVAR_134 : type1210 _104907 _104908) (g : type686 _104908) (t : _104908 -> Prop) : (term70 _104907 _104908 GEN_PVAR_134 g t) = (term71 _104907 _104908 GEN_PVAR_134 g t).
Proof. exact (MK_COMB (@lem4372598 _104907 _104908 GEN_PVAR_134 t g) (@lem4372599 _104907 _104908 t)). Qed.
Lemma lem4372601 {_104907 _104908 : Type'} (GEN_PVAR_134 : type1210 _104907 _104908) (g : type686 _104908) : (term72 _104907 _104908 GEN_PVAR_134 g) = (term73 _104907 _104908 GEN_PVAR_134 g).
Proof. exact (fun_ext (fun t : _104908 -> Prop => @lem4372600 _104907 _104908 GEN_PVAR_134 g t)). Qed.
Lemma lem4372602 {_104908 : Type'} : (@ex (_104908 -> Prop)) = (@ex (_104908 -> Prop)).
Proof. exact (eq_refl (@ex (_104908 -> Prop))). Qed.
Lemma lem4372603 {_104907 _104908 : Type'} (GEN_PVAR_134 : type1210 _104907 _104908) (g : type686 _104908) : (term74 _104907 _104908 GEN_PVAR_134 g) = (term75 _104907 _104908 GEN_PVAR_134 g).
Proof. exact (MK_COMB (@lem4372602 _104908) (@lem4372601 _104907 _104908 GEN_PVAR_134 g)). Qed.
Lemma lem4372604 {_104907 _104908 : Type'} (g : type686 _104908) : (term76 _104907 _104908 g) = (term77 _104907 _104908 g).
Proof. exact (fun_ext (fun GEN_PVAR_134 : type1210 _104907 _104908 => @lem4372603 _104907 _104908 GEN_PVAR_134 g)). Qed.
Lemma lem4372605 {_104907 _104908 : Type'} : (@GSPEC ((prod _104907 _104908) -> Prop)) = (@GSPEC ((prod _104907 _104908) -> Prop)).
Proof. exact (eq_refl (@GSPEC ((prod _104907 _104908) -> Prop))). Qed.
Lemma lem4372606 {_104907 _104908 : Type'} (g : type686 _104908) : (term78 _104907 _104908 g) = (term79 _104907 _104908 g).
Proof. exact (MK_COMB (@lem4372605 _104907 _104908) (@lem4372604 _104907 _104908 g)). Qed.
Lemma lem4372607 {_104907 _104908 : Type'} : (@INTERS (prod _104907 _104908)) = (@INTERS (prod _104907 _104908)).
Proof. exact (eq_refl (@INTERS (prod _104907 _104908))). Qed.
Lemma lem4372608 {_104907 _104908 : Type'} (g : type686 _104908) : (term62 _104907 _104908 g) = (term29 _104907 _104908 g).
Proof. exact (MK_COMB (@lem4372607 _104907 _104908) (@lem4372606 _104907 _104908 g)). Qed.
Lemma lem4372609 {_104907 _104908 : Type'} : (@eq ((prod _104907 _104908) -> Prop)) = (@eq ((prod _104907 _104908) -> Prop)).
Proof. exact (eq_refl (@eq ((prod _104907 _104908) -> Prop))). Qed.
Lemma lem4372610 {_104907 _104908 : Type'} (g : type686 _104908) : (term80 _104907 _104908 g) = (term81 _104907 _104908 g).
Proof. exact (MK_COMB (@lem4372609 _104907 _104908) (@lem4372608 _104907 _104908 g)). Qed.
Lemma lem4372611 {_104908 : Type'} (t : _104908 -> Prop) (g : type686 _104908) : (term66 _104908 g t) = (@IN (_104908 -> Prop) t g).
Proof. exact (eq_refl (term66 _104908 g t)). Qed.
Lemma lem4372612 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4372613 {_104908 : Type'} (t : _104908 -> Prop) (g : type686 _104908) : (term82 _104908 g t) = (term83 _104908 t g).
Proof. exact (MK_COMB (@lem4372612) (@lem4372611 _104908 t g)). Qed.
Lemma lem4372614 {_104907 _104908 : Type'} (t : _104908 -> Prop) : (term69 _104907 _104908 t) = (@CROSS _104908 _104907 (@UNIV _104907) t).
Proof. exact (eq_refl (term69 _104907 _104908 t)). Qed.
Lemma lem4372615 {_104907 _104908 : Type'} (a : prod _104907 _104908) : (@IN (prod _104907 _104908) a) = (@IN (prod _104907 _104908) a).
Proof. exact (eq_refl (@IN (prod _104907 _104908) a)). Qed.
Lemma lem4372616 {_104907 _104908 : Type'} (a : prod _104907 _104908) (t : _104908 -> Prop) : (term84 _104907 _104908 a t) = (term85 _104907 _104908 a t).
Proof. exact (MK_COMB (@lem4372615 _104907 _104908 a) (@lem4372614 _104907 _104908 t)). Qed.
Lemma lem4372617 {_104907 _104908 : Type'} (g : type686 _104908) (a : prod _104907 _104908) (t : _104908 -> Prop) : (term86 _104907 _104908 g a t) = (term87 _104907 _104908 g a t).
Proof. exact (MK_COMB (@lem4372613 _104908 t g) (@lem4372616 _104907 _104908 a t)). Qed.
Lemma lem4372618 {_104907 _104908 : Type'} (g : type686 _104908) (a : prod _104907 _104908) : (term88 _104907 _104908 g a) = (term89 _104907 _104908 g a).
Proof. exact (fun_ext (fun t : _104908 -> Prop => @lem4372617 _104907 _104908 g a t)). Qed.
Lemma lem4372619 {_104908 : Type'} : (@all (_104908 -> Prop)) = (@all (_104908 -> Prop)).
Proof. exact (eq_refl (@all (_104908 -> Prop))). Qed.
Lemma lem4372620 {_104907 _104908 : Type'} (g : type686 _104908) (a : prod _104907 _104908) : (term90 _104907 _104908 g a) = (term91 _104907 _104908 g a).
Proof. exact (MK_COMB (@lem4372619 _104908) (@lem4372618 _104907 _104908 g a)). Qed.
Lemma lem4372621 {_104907 _104908 : Type'} (GEN_PVAR_56 : prod _104907 _104908) : (@SETSPEC (prod _104907 _104908) GEN_PVAR_56) = (@SETSPEC (prod _104907 _104908) GEN_PVAR_56).
Proof. exact (eq_refl (@SETSPEC (prod _104907 _104908) GEN_PVAR_56)). Qed.
Lemma lem4372622 {_104907 _104908 : Type'} (GEN_PVAR_56 : prod _104907 _104908) (g : type686 _104908) (a : prod _104907 _104908) : (term92 _104907 _104908 GEN_PVAR_56 g a) = (term93 _104907 _104908 GEN_PVAR_56 g a).
Proof. exact (MK_COMB (@lem4372621 _104907 _104908 GEN_PVAR_56) (@lem4372620 _104907 _104908 g a)). Qed.
Lemma lem4372623 {_104907 _104908 : Type'} (a : prod _104907 _104908) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem4372624 {_104907 _104908 : Type'} (GEN_PVAR_56 : prod _104907 _104908) (g : type686 _104908) (a : prod _104907 _104908) : (term94 _104907 _104908 GEN_PVAR_56 g a) = (term95 _104907 _104908 GEN_PVAR_56 g a).
Proof. exact (MK_COMB (@lem4372622 _104907 _104908 GEN_PVAR_56 g a) (@lem4372623 _104907 _104908 a)). Qed.
Lemma lem4372625 {_104907 _104908 : Type'} (GEN_PVAR_56 : prod _104907 _104908) (g : type686 _104908) : (term96 _104907 _104908 GEN_PVAR_56 g) = (term97 _104907 _104908 GEN_PVAR_56 g).
Proof. exact (fun_ext (fun a : prod _104907 _104908 => @lem4372624 _104907 _104908 GEN_PVAR_56 g a)). Qed.
Lemma lem4372626 {_104907 _104908 : Type'} : (@ex (prod _104907 _104908)) = (@ex (prod _104907 _104908)).
Proof. exact (eq_refl (@ex (prod _104907 _104908))). Qed.
Lemma lem4372627 {_104907 _104908 : Type'} (GEN_PVAR_56 : prod _104907 _104908) (g : type686 _104908) : (term98 _104907 _104908 GEN_PVAR_56 g) = (term99 _104907 _104908 GEN_PVAR_56 g).
Proof. exact (MK_COMB (@lem4372626 _104907 _104908) (@lem4372625 _104907 _104908 GEN_PVAR_56 g)). Qed.
Lemma lem4372628 {_104907 _104908 : Type'} (g : type686 _104908) : (term100 _104907 _104908 g) = (term101 _104907 _104908 g).
Proof. exact (fun_ext (fun GEN_PVAR_56 : prod _104907 _104908 => @lem4372627 _104907 _104908 GEN_PVAR_56 g)). Qed.
Lemma lem4372629 {_104907 _104908 : Type'} : (@GSPEC (prod _104907 _104908)) = (@GSPEC (prod _104907 _104908)).
Proof. exact (eq_refl (@GSPEC (prod _104907 _104908))). Qed.
Lemma lem4372630 {_104907 _104908 : Type'} (g : type686 _104908) : (term63 _104907 _104908 g) = (term102 _104907 _104908 g).
Proof. exact (MK_COMB (@lem4372629 _104907 _104908) (@lem4372628 _104907 _104908 g)). Qed.
Lemma lem4372631 {_104907 _104908 : Type'} (g : type686 _104908) : ((term62 _104907 _104908 g) = (term63 _104907 _104908 g)) = ((term29 _104907 _104908 g) = (term102 _104907 _104908 g)).
Proof. exact (MK_COMB (@lem4372610 _104907 _104908 g) (@lem4372630 _104907 _104908 g)). Qed.
Lemma lem4372632 {_104907 _104908 : Type'} (g : type686 _104908) : (term29 _104907 _104908 g) = (term102 _104907 _104908 g).
Proof. exact (EQ_MP (@lem4372631 _104907 _104908 g) (@lem4372595 _104907 _104908 g)). Qed.
Lemma lem4372645 {_104907 _104908 : Type'} (p1 : _104907) (p2 : _104908) : (term103 _104907 _104908 p1 p2) = (term103 _104907 _104908 p1 p2).
Proof. exact (eq_refl (term103 _104907 _104908 p1 p2)). Qed.
Lemma lem4372646 {_104907 _104908 : Type'} (p1 : _104907) (p2 : _104908) (g : type686 _104908) : (term44 _104907 _104908 p1 p2 g) = (term104 _104907 _104908 p1 p2 g).
Proof. exact (MK_COMB (@lem4372645 _104907 _104908 p1 p2) (@lem4372632 _104907 _104908 g)). Qed.
Lemma lem4372648 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term13 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem4372485 _83095 p x) (@lem4372484 _83095 p x)). Qed.
Lemma lem4372649 {_104907 _104908 : Type'} (p : type1210 _104907 _104908) (x : prod _104907 _104908) : (term105 _104907 _104908 x p) = (p x).
Proof. exact (@lem4372648 (prod _104907 _104908) p x). Qed.
Lemma lem4372650 {_104907 _104908 : Type'} (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term106 _104907 _104908 p1 p2 g) = (term107 _104907 _104908 g p1 p2).
Proof. exact (@lem4372649 _104907 _104908 (term108 _104907 _104908 g) (@pair _104907 _104908 p1 p2)). Qed.
Lemma lem4372651 {_104907 _104908 : Type'} (g : type686 _104908) (a : prod _104907 _104908) : (term109 _104907 _104908 g a) = (term91 _104907 _104908 g a).
Proof. exact (eq_refl (term109 _104907 _104908 g a)). Qed.
Lemma lem4372652 {_104907 _104908 : Type'} (GEN_PVAR_56 : prod _104907 _104908) : (@SETSPEC (prod _104907 _104908) GEN_PVAR_56) = (@SETSPEC (prod _104907 _104908) GEN_PVAR_56).
Proof. exact (eq_refl (@SETSPEC (prod _104907 _104908) GEN_PVAR_56)). Qed.
Lemma lem4372653 {_104907 _104908 : Type'} (GEN_PVAR_56 : prod _104907 _104908) (g : type686 _104908) (a : prod _104907 _104908) : (term110 _104907 _104908 GEN_PVAR_56 g a) = (term93 _104907 _104908 GEN_PVAR_56 g a).
Proof. exact (MK_COMB (@lem4372652 _104907 _104908 GEN_PVAR_56) (@lem4372651 _104907 _104908 g a)). Qed.
Lemma lem4372654 {_104907 _104908 : Type'} (a : prod _104907 _104908) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem4372655 {_104907 _104908 : Type'} (GEN_PVAR_56 : prod _104907 _104908) (g : type686 _104908) (a : prod _104907 _104908) : (term111 _104907 _104908 GEN_PVAR_56 g a) = (term95 _104907 _104908 GEN_PVAR_56 g a).
Proof. exact (MK_COMB (@lem4372653 _104907 _104908 GEN_PVAR_56 g a) (@lem4372654 _104907 _104908 a)). Qed.
Lemma lem4372656 {_104907 _104908 : Type'} (GEN_PVAR_56 : prod _104907 _104908) (g : type686 _104908) : (term112 _104907 _104908 GEN_PVAR_56 g) = (term97 _104907 _104908 GEN_PVAR_56 g).
Proof. exact (fun_ext (fun a : prod _104907 _104908 => @lem4372655 _104907 _104908 GEN_PVAR_56 g a)). Qed.
Lemma lem4372657 {_104907 _104908 : Type'} : (@ex (prod _104907 _104908)) = (@ex (prod _104907 _104908)).
Proof. exact (eq_refl (@ex (prod _104907 _104908))). Qed.
Lemma lem4372658 {_104907 _104908 : Type'} (GEN_PVAR_56 : prod _104907 _104908) (g : type686 _104908) : (term113 _104907 _104908 GEN_PVAR_56 g) = (term99 _104907 _104908 GEN_PVAR_56 g).
Proof. exact (MK_COMB (@lem4372657 _104907 _104908) (@lem4372656 _104907 _104908 GEN_PVAR_56 g)). Qed.
Lemma lem4372659 {_104907 _104908 : Type'} (g : type686 _104908) : (term114 _104907 _104908 g) = (term101 _104907 _104908 g).
Proof. exact (fun_ext (fun GEN_PVAR_56 : prod _104907 _104908 => @lem4372658 _104907 _104908 GEN_PVAR_56 g)). Qed.
Lemma lem4372660 {_104907 _104908 : Type'} : (@GSPEC (prod _104907 _104908)) = (@GSPEC (prod _104907 _104908)).
Proof. exact (eq_refl (@GSPEC (prod _104907 _104908))). Qed.
Lemma lem4372661 {_104907 _104908 : Type'} (g : type686 _104908) : (term115 _104907 _104908 g) = (term102 _104907 _104908 g).
Proof. exact (MK_COMB (@lem4372660 _104907 _104908) (@lem4372659 _104907 _104908 g)). Qed.
Lemma lem4372662 {_104907 _104908 : Type'} (p1 : _104907) (p2 : _104908) : (term103 _104907 _104908 p1 p2) = (term103 _104907 _104908 p1 p2).
Proof. exact (eq_refl (term103 _104907 _104908 p1 p2)). Qed.
Lemma lem4372663 {_104907 _104908 : Type'} (p1 : _104907) (p2 : _104908) (g : type686 _104908) : (term106 _104907 _104908 p1 p2 g) = (term104 _104907 _104908 p1 p2 g).
Proof. exact (MK_COMB (@lem4372662 _104907 _104908 p1 p2) (@lem4372661 _104907 _104908 g)). Qed.
Lemma lem4372664 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4372665 {_104907 _104908 : Type'} (p1 : _104907) (p2 : _104908) (g : type686 _104908) : (term116 _104907 _104908 p1 p2 g) = (term117 _104907 _104908 p1 p2 g).
Proof. exact (MK_COMB (@lem4372664) (@lem4372663 _104907 _104908 p1 p2 g)). Qed.
Lemma lem4372666 {_104907 _104908 : Type'} (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term107 _104907 _104908 g p1 p2) = (term118 _104907 _104908 g p1 p2).
Proof. exact (eq_refl (term107 _104907 _104908 g p1 p2)). Qed.
Lemma lem4372667 {_104907 _104908 : Type'} (g : type686 _104908) (p1 : _104907) (p2 : _104908) : ((term106 _104907 _104908 p1 p2 g) = (term107 _104907 _104908 g p1 p2)) = ((term104 _104907 _104908 p1 p2 g) = (term118 _104907 _104908 g p1 p2)).
Proof. exact (MK_COMB (@lem4372665 _104907 _104908 p1 p2 g) (@lem4372666 _104907 _104908 g p1 p2)). Qed.
Lemma lem4372668 {_104907 _104908 : Type'} (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term104 _104907 _104908 p1 p2 g) = (term118 _104907 _104908 g p1 p2).
Proof. exact (EQ_MP (@lem4372667 _104907 _104908 g p1 p2) (@lem4372650 _104907 _104908 g p1 p2)). Qed.
Lemma lem4372678 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term7 _103718 _103721 x y s t) = (term8 _103718 _103721 x s y t).
Proof. exact (EQ_MP (@lem4372454 _103718 _103721 x s y t) (@lem4372453 _103718 _103721 x s y t)). Qed.
Lemma lem4372679 {_104907 _104908 : Type'} (x : _104907) (s : _104907 -> Prop) (y : _104908) (t : _104908 -> Prop) : (term7 _104907 _104908 x y s t) = (term8 _104907 _104908 x s y t).
Proof. exact (@lem4372678 _104907 _104908 x s y t). Qed.
Lemma lem4372680 {_104907 _104908 : Type'} (p1 : _104907) (p2 : _104908) (t : _104908 -> Prop) : (term119 _104907 _104908 p1 p2 t) = (term120 _104907 _104908 p1 p2 t).
Proof. exact (@lem4372679 _104907 _104908 p1 (@UNIV _104907) p2 t). Qed.
Lemma lem4372683 {_104908 : Type'} (t : _104908 -> Prop) (g : type686 _104908) : (term83 _104908 t g) = (term83 _104908 t g).
Proof. exact (eq_refl (term83 _104908 t g)). Qed.
Lemma lem4372684 {_104907 _104908 : Type'} (g : type686 _104908) (p1 : _104907) (p2 : _104908) (t : _104908 -> Prop) : (term121 _104907 _104908 g p1 p2 t) = (term122 _104907 _104908 g p1 p2 t).
Proof. exact (MK_COMB (@lem4372683 _104908 t g) (@lem4372680 _104907 _104908 p1 p2 t)). Qed.
Lemma lem4372687 {_104907 _104908 : Type'} (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term123 _104907 _104908 g p1 p2) = (term124 _104907 _104908 g p1 p2).
Proof. exact (fun_ext (fun t : _104908 -> Prop => @lem4372684 _104907 _104908 g p1 p2 t)). Qed.
Lemma lem4372688 {_104908 : Type'} : (@all (_104908 -> Prop)) = (@all (_104908 -> Prop)).
Proof. exact (eq_refl (@all (_104908 -> Prop))). Qed.
Lemma lem4372689 {_104907 _104908 : Type'} (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term118 _104907 _104908 g p1 p2) = (term125 _104907 _104908 g p1 p2).
Proof. exact (MK_COMB (@lem4372688 _104908) (@lem4372687 _104907 _104908 g p1 p2)). Qed.
Lemma lem4372696 {_104907 _104908 : Type'} (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term104 _104907 _104908 p1 p2 g) = (term125 _104907 _104908 g p1 p2).
Proof. exact (TRANS (@lem4372668 _104907 _104908 g p1 p2) (@lem4372689 _104907 _104908 g p1 p2)). Qed.
Lemma lem4372697 {_104907 _104908 : Type'} (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term44 _104907 _104908 p1 p2 g) = (term125 _104907 _104908 g p1 p2).
Proof. exact (TRANS (@lem4372646 _104907 _104908 p1 p2 g) (@lem4372696 _104907 _104908 g p1 p2)). Qed.
Lemma lem4372698 {_104907 _104908 : Type'} (g : type686 _104908) (p1 : _104907) (p2 : _104908) (f : type686 _104907) (h1 : f = (@EMPTY (_104907 -> Prop))) : ((term43 _104907 _104908 p1 p2 f g) = (term44 _104907 _104908 p1 p2 g)) = ((term57 _104907 _104908 p1 p2 g) = (term125 _104907 _104908 g p1 p2)).
Proof. exact (MK_COMB (@lem4372591 _104907 _104908 p1 p2 g f h1) (@lem4372697 _104907 _104908 g p1 p2)). Qed.
Lemma lem4372703 {_104907 _104908 : Type'} (g : type686 _104908) (p1 : _104907) (f : type686 _104907) (h1 : f = (@EMPTY (_104907 -> Prop))) : (term46 _104907 _104908 f p1 g) = (term126 _104907 _104908 g p1).
Proof. exact (fun_ext (fun p2 : _104908 => @lem4372698 _104907 _104908 g p1 p2 f h1)). Qed.
Lemma lem4372704 {_104908 : Type'} : (@all _104908) = (@all _104908).
Proof. exact (eq_refl (@all _104908)). Qed.
Lemma lem4372705 {_104907 _104908 : Type'} (g : type686 _104908) (p1 : _104907) (f : type686 _104907) (h1 : f = (@EMPTY (_104907 -> Prop))) : (term48 _104907 _104908 f p1 g) = (term127 _104907 _104908 g p1).
Proof. exact (MK_COMB (@lem4372704 _104908) (@lem4372703 _104907 _104908 g p1 f h1)). Qed.
Lemma lem4372712 {_104907 _104908 : Type'} (g : type686 _104908) (f : type686 _104907) (h1 : f = (@EMPTY (_104907 -> Prop))) : (term50 _104907 _104908 f g) = (term128 _104907 _104908 g).
Proof. exact (fun_ext (fun p1 : _104907 => @lem4372705 _104907 _104908 g p1 f h1)). Qed.
Lemma lem4372713 {_104907 : Type'} : (@all _104907) = (@all _104907).
Proof. exact (eq_refl (@all _104907)). Qed.
Lemma lem4372714 {_104907 _104908 : Type'} (g : type686 _104908) (f : type686 _104907) (h1 : f = (@EMPTY (_104907 -> Prop))) : (term51 _104907 _104908 f g) = (term129 _104907 _104908 g).
Proof. exact (MK_COMB (@lem4372713 _104907) (@lem4372712 _104907 _104908 g f h1)). Qed.
Lemma lem4372721 {_104907 _104908 : Type'} (g : type686 _104908) (f : type686 _104907) (h1 : f = (@EMPTY (_104907 -> Prop))) : ((term28 _104907 _104908 f g) = (term29 _104907 _104908 g)) = (term129 _104907 _104908 g).
Proof. exact (TRANS (@lem4372560 _104907 _104908 f g) (@lem4372714 _104907 _104908 g f h1)). Qed.
Lemma lem4372722 {_104907 _104908 : Type'} (g : type686 _104908) (f : type686 _104907) (h1 : f = (@EMPTY (_104907 -> Prop))) : (term129 _104907 _104908 g) = ((term28 _104907 _104908 f g) = (term29 _104907 _104908 g)).
Proof. exact (SYM (@lem4372721 _104907 _104908 g f h1)). Qed.
