Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INTER_CROSS_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import EXTENSION_spec.
Require Import FORALL_PAIR_THM_spec.
Require Import IN_CROSS_spec.
Require Import IN_INTER_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1845_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem4362405 {_103718 _103721 : Type'} (x : _103718) : term0 _103718 _103721 x.
Proof. exact (@lem4325365 _103718 _103721 x). Qed.
Lemma lem4362406 {_103718 _103721 : Type'} (x : _103718) : (term0 _103718 _103721 x) = (term1 _103718 _103721 x).
Proof. exact (eq_refl (term0 _103718 _103721 x)). Qed.
Lemma lem4362407 {_103718 _103721 : Type'} (x : _103718) : term1 _103718 _103721 x.
Proof. exact (EQ_MP (@lem4362406 _103718 _103721 x) (@lem4362405 _103718 _103721 x)). Qed.
Lemma lem4362408 {_103718 _103721 : Type'} (x : _103718) (y : _103721) : term2 _103718 _103721 x y.
Proof. exact (@lem4362407 _103718 _103721 x y). Qed.
Lemma lem4362409 {_103718 _103721 : Type'} (x : _103718) (y : _103721) : (term2 _103718 _103721 x y) = (term3 _103718 _103721 x y).
Proof. exact (eq_refl (term2 _103718 _103721 x y)). Qed.
Lemma lem4362410 {_103718 _103721 : Type'} (x : _103718) (y : _103721) : term3 _103718 _103721 x y.
Proof. exact (EQ_MP (@lem4362409 _103718 _103721 x y) (@lem4362408 _103718 _103721 x y)). Qed.
Lemma lem4362411 {_103718 _103721 : Type'} (x : _103718) (y : _103721) (s : _103718 -> Prop) : term4 _103718 _103721 x y s.
Proof. exact (@lem4362410 _103718 _103721 x y s). Qed.
Lemma lem4362412 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) : (term4 _103718 _103721 x y s) = (term5 _103718 _103721 x s y).
Proof. exact (eq_refl (term4 _103718 _103721 x y s)). Qed.
Lemma lem4362413 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) : term5 _103718 _103721 x s y.
Proof. exact (EQ_MP (@lem4362412 _103718 _103721 x s y) (@lem4362411 _103718 _103721 x y s)). Qed.
Lemma lem4362414 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : term6 _103718 _103721 x s y t.
Proof. exact (@lem4362413 _103718 _103721 x s y t). Qed.
Lemma lem4362415 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term6 _103718 _103721 x s y t) = ((term7 _103718 _103721 x y s t) = (term8 _103718 _103721 x s y t)).
Proof. exact (eq_refl (term6 _103718 _103721 x s y t)). Qed.
Lemma lem4362417 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : term9 _5106 _5107 P.
Proof. exact (@lem49909 _5106 _5107 P). Qed.
Lemma lem4362418 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term9 _5106 _5107 P) = ((term10 _5106 _5107 P) = (term11 _5106 _5107 P)).
Proof. exact (eq_refl (term9 _5106 _5107 P)). Qed.
Lemma lem4362420 {A : Type'} (s : A -> Prop) : term12 A s.
Proof. exact (@lem3205222 A s). Qed.
Lemma lem4362421 {A : Type'} (s : A -> Prop) : (term12 A s) = (term13 A s).
Proof. exact (eq_refl (term12 A s)). Qed.
Lemma lem4362422 {A : Type'} (s : A -> Prop) : term13 A s.
Proof. exact (EQ_MP (@lem4362421 A s) (@lem4362420 A s)). Qed.
Lemma lem4362423 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term14 A s t.
Proof. exact (@lem4362422 A s t). Qed.
Lemma lem4362424 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term14 A s t) = (term15 A s t).
Proof. exact (eq_refl (term14 A s t)). Qed.
Lemma lem4362425 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term15 A s t.
Proof. exact (EQ_MP (@lem4362424 A s t) (@lem4362423 A s t)). Qed.
Lemma lem4362426 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : term16 A s t x.
Proof. exact (@lem4362425 A s t x). Qed.
Lemma lem4362427 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term16 A s t x) = ((term17 A x s t) = (term18 A s x t)).
Proof. exact (eq_refl (term16 A s t x)). Qed.
Lemma lem4362429 {A : Type'} (s : A -> Prop) : term19 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem4362430 {A : Type'} (s : A -> Prop) : (term19 A s) = (term20 A s).
Proof. exact (eq_refl (term19 A s)). Qed.
Lemma lem4362431 {A : Type'} (s : A -> Prop) : term20 A s.
Proof. exact (EQ_MP (@lem4362430 A s) (@lem4362429 A s)). Qed.
Lemma lem4362432 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term21 A s t.
Proof. exact (@lem4362431 A s t). Qed.
Lemma lem4362433 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term21 A s t) = ((s = t) = (term22 A s t)).
Proof. exact (eq_refl (term21 A s t)). Qed.
Lemma lem4362462 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term22 A s t).
Proof. exact (EQ_MP (@lem4362433 A s t) (@lem4362432 A s t)). Qed.
Lemma lem4362463 {_104663 _104666 : Type'} (s : type1210 _104663 _104666) (t : type1210 _104663 _104666) : (s = t) = (term23 _104663 _104666 s t).
Proof. exact (@lem4362462 (prod _104663 _104666) s t). Qed.
Lemma lem4362464 {_104663 _104666 : Type'} (s : _104663 -> Prop) (s' : _104663 -> Prop) (t : _104666 -> Prop) (t' : _104666 -> Prop) : ((term24 _104663 _104666 s t s' t') = (term25 _104663 _104666 s s' t t')) = (term26 _104663 _104666 s s' t t').
Proof. exact (@lem4362463 _104663 _104666 (term24 _104663 _104666 s t s' t') (term25 _104663 _104666 s s' t t')). Qed.
Lemma lem4362470 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term10 _5106 _5107 P) = (term11 _5106 _5107 P).
Proof. exact (EQ_MP (@lem4362418 _5106 _5107 P) (@lem4362417 _5106 _5107 P)). Qed.
Lemma lem4362471 {_104663 _104666 : Type'} (P : type1210 _104663 _104666) : (term27 _104663 _104666 P) = (term28 _104663 _104666 P).
Proof. exact (@lem4362470 _104666 _104663 P). Qed.
Lemma lem4362472 {_104663 _104666 : Type'} (s : _104663 -> Prop) (s' : _104663 -> Prop) (t : _104666 -> Prop) (t' : _104666 -> Prop) : (term29 _104663 _104666 s s' t t') = (term30 _104663 _104666 s s' t t').
Proof. exact (@lem4362471 _104663 _104666 (term31 _104663 _104666 s s' t t')). Qed.
Lemma lem4362473 {_104663 _104666 : Type'} (x : prod _104663 _104666) (s : _104663 -> Prop) (s' : _104663 -> Prop) (t : _104666 -> Prop) (t' : _104666 -> Prop) : (term32 _104663 _104666 s s' t t' x) = ((term33 _104663 _104666 x s t s' t') = (term34 _104663 _104666 x s s' t t')).
Proof. exact (eq_refl (term32 _104663 _104666 s s' t t' x)). Qed.
Lemma lem4362474 {_104663 _104666 : Type'} (s : _104663 -> Prop) (s' : _104663 -> Prop) (t : _104666 -> Prop) (t' : _104666 -> Prop) : (term35 _104663 _104666 s s' t t') = (term31 _104663 _104666 s s' t t').
Proof. exact (fun_ext (fun x : prod _104663 _104666 => @lem4362473 _104663 _104666 x s s' t t')). Qed.
Lemma lem4362475 {_104663 _104666 : Type'} : (@all (prod _104663 _104666)) = (@all (prod _104663 _104666)).
Proof. exact (eq_refl (@all (prod _104663 _104666))). Qed.
Lemma lem4362476 {_104663 _104666 : Type'} (s : _104663 -> Prop) (s' : _104663 -> Prop) (t : _104666 -> Prop) (t' : _104666 -> Prop) : (term29 _104663 _104666 s s' t t') = (term26 _104663 _104666 s s' t t').
Proof. exact (MK_COMB (@lem4362475 _104663 _104666) (@lem4362474 _104663 _104666 s s' t t')). Qed.
Lemma lem4362477 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4362478 {_104663 _104666 : Type'} (s : _104663 -> Prop) (s' : _104663 -> Prop) (t : _104666 -> Prop) (t' : _104666 -> Prop) : (term36 _104663 _104666 s s' t t') = (term37 _104663 _104666 s s' t t').
Proof. exact (MK_COMB (@lem4362477) (@lem4362476 _104663 _104666 s s' t t')). Qed.
Lemma lem4362479 {_104663 _104666 : Type'} (p1 : _104663) (p2 : _104666) (s : _104663 -> Prop) (s' : _104663 -> Prop) (t : _104666 -> Prop) (t' : _104666 -> Prop) : (term38 _104663 _104666 s s' t t' p1 p2) = ((term39 _104663 _104666 p1 p2 s t s' t') = (term40 _104663 _104666 p1 p2 s s' t t')).
Proof. exact (eq_refl (term38 _104663 _104666 s s' t t' p1 p2)). Qed.
Lemma lem4362480 {_104663 _104666 : Type'} (p1 : _104663) (s : _104663 -> Prop) (s' : _104663 -> Prop) (t : _104666 -> Prop) (t' : _104666 -> Prop) : (term41 _104663 _104666 s s' t t' p1) = (term42 _104663 _104666 p1 s s' t t').
Proof. exact (fun_ext (fun p2 : _104666 => @lem4362479 _104663 _104666 p1 p2 s s' t t')). Qed.
Lemma lem4362481 {_104666 : Type'} : (@all _104666) = (@all _104666).
Proof. exact (eq_refl (@all _104666)). Qed.
Lemma lem4362482 {_104663 _104666 : Type'} (p1 : _104663) (s : _104663 -> Prop) (s' : _104663 -> Prop) (t : _104666 -> Prop) (t' : _104666 -> Prop) : (term43 _104663 _104666 s s' t t' p1) = (term44 _104663 _104666 p1 s s' t t').
Proof. exact (MK_COMB (@lem4362481 _104666) (@lem4362480 _104663 _104666 p1 s s' t t')). Qed.
Lemma lem4362483 {_104663 _104666 : Type'} (s : _104663 -> Prop) (s' : _104663 -> Prop) (t : _104666 -> Prop) (t' : _104666 -> Prop) : (term45 _104663 _104666 s s' t t') = (term46 _104663 _104666 s s' t t').
Proof. exact (fun_ext (fun p1 : _104663 => @lem4362482 _104663 _104666 p1 s s' t t')). Qed.
Lemma lem4362484 {_104663 : Type'} : (@all _104663) = (@all _104663).
Proof. exact (eq_refl (@all _104663)). Qed.
Lemma lem4362485 {_104663 _104666 : Type'} (s : _104663 -> Prop) (s' : _104663 -> Prop) (t : _104666 -> Prop) (t' : _104666 -> Prop) : (term30 _104663 _104666 s s' t t') = (term47 _104663 _104666 s s' t t').
Proof. exact (MK_COMB (@lem4362484 _104663) (@lem4362483 _104663 _104666 s s' t t')). Qed.
Lemma lem4362486 {_104663 _104666 : Type'} (s : _104663 -> Prop) (s' : _104663 -> Prop) (t : _104666 -> Prop) (t' : _104666 -> Prop) : ((term29 _104663 _104666 s s' t t') = (term30 _104663 _104666 s s' t t')) = ((term26 _104663 _104666 s s' t t') = (term47 _104663 _104666 s s' t t')).
Proof. exact (MK_COMB (@lem4362478 _104663 _104666 s s' t t') (@lem4362485 _104663 _104666 s s' t t')). Qed.
Lemma lem4362487 {_104663 _104666 : Type'} (s : _104663 -> Prop) (s' : _104663 -> Prop) (t : _104666 -> Prop) (t' : _104666 -> Prop) : (term26 _104663 _104666 s s' t t') = (term47 _104663 _104666 s s' t t').
Proof. exact (EQ_MP (@lem4362486 _104663 _104666 s s' t t') (@lem4362472 _104663 _104666 s s' t t')). Qed.
Lemma lem4362494 {_104663 _104666 : Type'} (s : _104663 -> Prop) (s' : _104663 -> Prop) (t : _104666 -> Prop) (t' : _104666 -> Prop) : ((term24 _104663 _104666 s t s' t') = (term25 _104663 _104666 s s' t t')) = (term47 _104663 _104666 s s' t t').
Proof. exact (TRANS (@lem4362464 _104663 _104666 s s' t t') (@lem4362487 _104663 _104666 s s' t t')). Qed.
Lemma lem4362506 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term17 A x s t) = (term18 A s x t).
Proof. exact (EQ_MP (@lem4362427 A s x t) (@lem4362426 A s t x)). Qed.
Lemma lem4362507 {_104663 _104666 : Type'} (s : type1210 _104663 _104666) (x : prod _104663 _104666) (t : type1210 _104663 _104666) : (term48 _104663 _104666 x s t) = (term49 _104663 _104666 s x t).
Proof. exact (@lem4362506 (prod _104663 _104666) s x t). Qed.
Lemma lem4362508 {_104663 _104666 : Type'} (s : _104663 -> Prop) (t : _104666 -> Prop) (p1 : _104663) (p2 : _104666) (s' : _104663 -> Prop) (t' : _104666 -> Prop) : (term39 _104663 _104666 p1 p2 s t s' t') = (term50 _104663 _104666 s t p1 p2 s' t').
Proof. exact (@lem4362507 _104663 _104666 (@CROSS _104666 _104663 s t) (@pair _104663 _104666 p1 p2) (@CROSS _104666 _104663 s' t')). Qed.
Lemma lem4362512 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term7 _103718 _103721 x y s t) = (term8 _103718 _103721 x s y t).
Proof. exact (EQ_MP (@lem4362415 _103718 _103721 x s y t) (@lem4362414 _103718 _103721 x s y t)). Qed.
Lemma lem4362513 {_104663 _104666 : Type'} (x : _104663) (s : _104663 -> Prop) (y : _104666) (t : _104666 -> Prop) : (term7 _104663 _104666 x y s t) = (term8 _104663 _104666 x s y t).
Proof. exact (@lem4362512 _104663 _104666 x s y t). Qed.
Lemma lem4362514 {_104663 _104666 : Type'} (p1 : _104663) (s : _104663 -> Prop) (p2 : _104666) (t : _104666 -> Prop) : (term7 _104663 _104666 p1 p2 s t) = (term8 _104663 _104666 p1 s p2 t).
Proof. exact (@lem4362513 _104663 _104666 p1 s p2 t). Qed.
Lemma lem4362517 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4362518 {_104663 _104666 : Type'} (p1 : _104663) (s : _104663 -> Prop) (p2 : _104666) (t : _104666 -> Prop) : (term51 _104663 _104666 p1 p2 s t) = (term52 _104663 _104666 p1 s p2 t).
Proof. exact (MK_COMB (@lem4362517) (@lem4362514 _104663 _104666 p1 s p2 t)). Qed.
Lemma lem4362520 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term7 _103718 _103721 x y s t) = (term8 _103718 _103721 x s y t).
Proof. exact (EQ_MP (@lem4362415 _103718 _103721 x s y t) (@lem4362414 _103718 _103721 x s y t)). Qed.
Lemma lem4362521 {_104663 _104666 : Type'} (x : _104663) (s : _104663 -> Prop) (y : _104666) (t : _104666 -> Prop) : (term7 _104663 _104666 x y s t) = (term8 _104663 _104666 x s y t).
Proof. exact (@lem4362520 _104663 _104666 x s y t). Qed.
Lemma lem4362522 {_104663 _104666 : Type'} (p1 : _104663) (s' : _104663 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : (term7 _104663 _104666 p1 p2 s' t') = (term8 _104663 _104666 p1 s' p2 t').
Proof. exact (@lem4362521 _104663 _104666 p1 s' p2 t'). Qed.
Lemma lem4362525 {_104663 _104666 : Type'} (s : _104663 -> Prop) (t : _104666 -> Prop) (p1 : _104663) (s' : _104663 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : (term50 _104663 _104666 s t p1 p2 s' t') = (term53 _104663 _104666 s t p1 s' p2 t').
Proof. exact (MK_COMB (@lem4362518 _104663 _104666 p1 s p2 t) (@lem4362522 _104663 _104666 p1 s' p2 t')). Qed.
Lemma lem4362528 {_104663 _104666 : Type'} (s : _104663 -> Prop) (t : _104666 -> Prop) (p1 : _104663) (s' : _104663 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : (term39 _104663 _104666 p1 p2 s t s' t') = (term53 _104663 _104666 s t p1 s' p2 t').
Proof. exact (TRANS (@lem4362508 _104663 _104666 s t p1 p2 s' t') (@lem4362525 _104663 _104666 s t p1 s' p2 t')). Qed.
Lemma lem4362529 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4362530 {_104663 _104666 : Type'} (s : _104663 -> Prop) (t : _104666 -> Prop) (p1 : _104663) (s' : _104663 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : (term54 _104663 _104666 p1 p2 s t s' t') = (term55 _104663 _104666 s t p1 s' p2 t').
Proof. exact (MK_COMB (@lem4362529) (@lem4362528 _104663 _104666 s t p1 s' p2 t')). Qed.
Lemma lem4362532 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term7 _103718 _103721 x y s t) = (term8 _103718 _103721 x s y t).
Proof. exact (EQ_MP (@lem4362415 _103718 _103721 x s y t) (@lem4362414 _103718 _103721 x s y t)). Qed.
Lemma lem4362533 {_104663 _104666 : Type'} (x : _104663) (s : _104663 -> Prop) (y : _104666) (t : _104666 -> Prop) : (term7 _104663 _104666 x y s t) = (term8 _104663 _104666 x s y t).
Proof. exact (@lem4362532 _104663 _104666 x s y t). Qed.
Lemma lem4362534 {_104663 _104666 : Type'} (p1 : _104663) (s : _104663 -> Prop) (s' : _104663 -> Prop) (p2 : _104666) (t : _104666 -> Prop) (t' : _104666 -> Prop) : (term40 _104663 _104666 p1 p2 s s' t t') = (term56 _104663 _104666 p1 s s' p2 t t').
Proof. exact (@lem4362533 _104663 _104666 p1 (@INTER _104663 s s') p2 (@INTER _104666 t t')). Qed.
Lemma lem4362538 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term17 A x s t) = (term18 A s x t).
Proof. exact (EQ_MP (@lem4362427 A s x t) (@lem4362426 A s t x)). Qed.
Lemma lem4362539 {_104663 : Type'} (s : _104663 -> Prop) (x : _104663) (t : _104663 -> Prop) : (term17 _104663 x s t) = (term18 _104663 s x t).
Proof. exact (@lem4362538 _104663 s x t). Qed.
Lemma lem4362540 {_104663 : Type'} (s : _104663 -> Prop) (p1 : _104663) (s' : _104663 -> Prop) : (term17 _104663 p1 s s') = (term18 _104663 s p1 s').
Proof. exact (@lem4362539 _104663 s p1 s'). Qed.
Lemma lem4362543 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4362544 {_104663 : Type'} (s : _104663 -> Prop) (p1 : _104663) (s' : _104663 -> Prop) : (term57 _104663 p1 s s') = (term58 _104663 s p1 s').
Proof. exact (MK_COMB (@lem4362543) (@lem4362540 _104663 s p1 s')). Qed.
Lemma lem4362546 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term17 A x s t) = (term18 A s x t).
Proof. exact (EQ_MP (@lem4362427 A s x t) (@lem4362426 A s t x)). Qed.
Lemma lem4362547 {_104666 : Type'} (s : _104666 -> Prop) (x : _104666) (t : _104666 -> Prop) : (term17 _104666 x s t) = (term18 _104666 s x t).
Proof. exact (@lem4362546 _104666 s x t). Qed.
Lemma lem4362548 {_104666 : Type'} (t : _104666 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : (term17 _104666 p2 t t') = (term18 _104666 t p2 t').
Proof. exact (@lem4362547 _104666 t p2 t'). Qed.
Lemma lem4362551 {_104663 _104666 : Type'} (s : _104663 -> Prop) (p1 : _104663) (s' : _104663 -> Prop) (t : _104666 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : (term56 _104663 _104666 p1 s s' p2 t t') = (term59 _104663 _104666 s p1 s' t p2 t').
Proof. exact (MK_COMB (@lem4362544 _104663 s p1 s') (@lem4362548 _104666 t p2 t')). Qed.
Lemma lem4362554 {_104663 _104666 : Type'} (s : _104663 -> Prop) (p1 : _104663) (s' : _104663 -> Prop) (t : _104666 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : (term40 _104663 _104666 p1 p2 s s' t t') = (term59 _104663 _104666 s p1 s' t p2 t').
Proof. exact (TRANS (@lem4362534 _104663 _104666 p1 s s' p2 t t') (@lem4362551 _104663 _104666 s p1 s' t p2 t')). Qed.
Lemma lem4362555 {_104663 _104666 : Type'} (s : _104663 -> Prop) (p1 : _104663) (s' : _104663 -> Prop) (t : _104666 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : ((term39 _104663 _104666 p1 p2 s t s' t') = (term40 _104663 _104666 p1 p2 s s' t t')) = ((term53 _104663 _104666 s t p1 s' p2 t') = (term59 _104663 _104666 s p1 s' t p2 t')).
Proof. exact (MK_COMB (@lem4362530 _104663 _104666 s t p1 s' p2 t') (@lem4362554 _104663 _104666 s p1 s' t p2 t')). Qed.
Lemma lem4362560 {_104663 _104666 : Type'} (s : _104663 -> Prop) (p1 : _104663) (s' : _104663 -> Prop) (t : _104666 -> Prop) (t' : _104666 -> Prop) : (term42 _104663 _104666 p1 s s' t t') = (term60 _104663 _104666 s p1 s' t t').
Proof. exact (fun_ext (fun p2 : _104666 => @lem4362555 _104663 _104666 s p1 s' t p2 t')). Qed.
Lemma lem4362561 {_104666 : Type'} : (@all _104666) = (@all _104666).
Proof. exact (eq_refl (@all _104666)). Qed.
Lemma lem4362562 {_104663 _104666 : Type'} (s : _104663 -> Prop) (p1 : _104663) (s' : _104663 -> Prop) (t : _104666 -> Prop) (t' : _104666 -> Prop) : (term44 _104663 _104666 p1 s s' t t') = (term61 _104663 _104666 s p1 s' t t').
Proof. exact (MK_COMB (@lem4362561 _104666) (@lem4362560 _104663 _104666 s p1 s' t t')). Qed.
Lemma lem4362569 {_104663 _104666 : Type'} (s : _104663 -> Prop) (s' : _104663 -> Prop) (t : _104666 -> Prop) (t' : _104666 -> Prop) : (term46 _104663 _104666 s s' t t') = (term62 _104663 _104666 s s' t t').
Proof. exact (fun_ext (fun p1 : _104663 => @lem4362562 _104663 _104666 s p1 s' t t')). Qed.
Lemma lem4362570 {_104663 : Type'} : (@all _104663) = (@all _104663).
Proof. exact (eq_refl (@all _104663)). Qed.
Lemma lem4362571 {_104663 _104666 : Type'} (s : _104663 -> Prop) (s' : _104663 -> Prop) (t : _104666 -> Prop) (t' : _104666 -> Prop) : (term47 _104663 _104666 s s' t t') = (term63 _104663 _104666 s s' t t').
Proof. exact (MK_COMB (@lem4362570 _104663) (@lem4362569 _104663 _104666 s s' t t')). Qed.
Lemma lem4362578 {_104663 _104666 : Type'} (s : _104663 -> Prop) (s' : _104663 -> Prop) (t : _104666 -> Prop) (t' : _104666 -> Prop) : ((term24 _104663 _104666 s t s' t') = (term25 _104663 _104666 s s' t t')) = (term63 _104663 _104666 s s' t t').
Proof. exact (TRANS (@lem4362494 _104663 _104666 s s' t t') (@lem4362571 _104663 _104666 s s' t t')). Qed.
Lemma lem4362579 {_104663 _104666 : Type'} (s : _104663 -> Prop) (s' : _104663 -> Prop) (t : _104666 -> Prop) : (term64 _104663 _104666 s s' t) = (term65 _104663 _104666 s s' t).
Proof. exact (fun_ext (fun t' : _104666 -> Prop => @lem4362578 _104663 _104666 s s' t t')). Qed.
Lemma lem4362580 {_104666 : Type'} : (@all (_104666 -> Prop)) = (@all (_104666 -> Prop)).
Proof. exact (eq_refl (@all (_104666 -> Prop))). Qed.
Lemma lem4362581 {_104663 _104666 : Type'} (s : _104663 -> Prop) (s' : _104663 -> Prop) (t : _104666 -> Prop) : (term66 _104663 _104666 s s' t) = (term67 _104663 _104666 s s' t).
Proof. exact (MK_COMB (@lem4362580 _104666) (@lem4362579 _104663 _104666 s s' t)). Qed.
Lemma lem4362588 {_104663 _104666 : Type'} (s : _104663 -> Prop) (s' : _104663 -> Prop) : (term68 _104663 _104666 s s') = (term69 _104663 _104666 s s').
Proof. exact (fun_ext (fun t : _104666 -> Prop => @lem4362581 _104663 _104666 s s' t)). Qed.
Lemma lem4362589 {_104666 : Type'} : (@all (_104666 -> Prop)) = (@all (_104666 -> Prop)).
Proof. exact (eq_refl (@all (_104666 -> Prop))). Qed.
Lemma lem4362590 {_104663 _104666 : Type'} (s : _104663 -> Prop) (s' : _104663 -> Prop) : (term70 _104663 _104666 s s') = (term71 _104663 _104666 s s').
Proof. exact (MK_COMB (@lem4362589 _104666) (@lem4362588 _104663 _104666 s s')). Qed.
Lemma lem4362597 {_104663 _104666 : Type'} (s : _104663 -> Prop) : (term72 _104663 _104666 s) = (term73 _104663 _104666 s).
Proof. exact (fun_ext (fun s' : _104663 -> Prop => @lem4362590 _104663 _104666 s s')). Qed.
Lemma lem4362598 {_104663 : Type'} : (@all (_104663 -> Prop)) = (@all (_104663 -> Prop)).
Proof. exact (eq_refl (@all (_104663 -> Prop))). Qed.
Lemma lem4362599 {_104663 _104666 : Type'} (s : _104663 -> Prop) : (term74 _104663 _104666 s) = (term75 _104663 _104666 s).
Proof. exact (MK_COMB (@lem4362598 _104663) (@lem4362597 _104663 _104666 s)). Qed.
Lemma lem4362606 {_104663 _104666 : Type'} : (term76 _104663 _104666) = (term77 _104663 _104666).
Proof. exact (fun_ext (fun s : _104663 -> Prop => @lem4362599 _104663 _104666 s)). Qed.
Lemma lem4362607 {_104663 : Type'} : (@all (_104663 -> Prop)) = (@all (_104663 -> Prop)).
Proof. exact (eq_refl (@all (_104663 -> Prop))). Qed.
Lemma lem4362608 {_104663 _104666 : Type'} : (term78 _104663 _104666) = (term79 _104663 _104666).
Proof. exact (MK_COMB (@lem4362607 _104663) (@lem4362606 _104663 _104666)). Qed.
Lemma lem4362615 {_104663 _104666 : Type'} : (term79 _104663 _104666) = (term78 _104663 _104666).
Proof. exact (SYM (@lem4362608 _104663 _104666)). Qed.
Lemma lem4362632 {_104663 : Type'} (p1 : _104663) (s : _104663 -> Prop) : term80 _104663 p1 s.
Proof. exact (@lem9851 (@IN _104663 p1 s)). Qed.
Lemma lem4362633 {_104663 : Type'} (p1 : _104663) (s : _104663 -> Prop) : (term80 _104663 p1 s) = (term81 _104663 p1 s).
Proof. exact (eq_refl (term80 _104663 p1 s)). Qed.
Lemma lem4362634 {_104663 : Type'} (p1 : _104663) (s : _104663 -> Prop) : term81 _104663 p1 s.
Proof. exact (EQ_MP (@lem4362633 _104663 p1 s) (@lem4362632 _104663 p1 s)). Qed.
Lemma lem4362635 {_104663 : Type'} (p1 : _104663) (s : _104663 -> Prop) (h1 : (@IN _104663 p1 s) = True) : (@IN _104663 p1 s) = True.
Proof. exact (h1). Qed.
Lemma lem4362636 {_104663 : Type'} (p1 : _104663) (s : _104663 -> Prop) (h1 : (@IN _104663 p1 s) = False) : (@IN _104663 p1 s) = False.
Proof. exact (h1). Qed.
Lemma lem4362653 {_104663 _104666 : Type'} (p1 : _104663) (s' : _104663 -> Prop) (t : _104666 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : (term82 _104663 _104666 p1 s' t p2 t') = (term82 _104663 _104666 p1 s' t p2 t').
Proof. exact (eq_refl (term82 _104663 _104666 p1 s' t p2 t')). Qed.
Lemma lem4362654 {_104663 _104666 : Type'} (s' : _104663 -> Prop) (t : _104666 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) (p1 : _104663) (s : _104663 -> Prop) (h1 : (@IN _104663 p1 s) = True) : (term83 _104663 _104666 s' t p2 t' p1 s) = (term84 _104663 _104666 p1 s' t p2 t').
Proof. exact (MK_COMB (@lem4362653 _104663 _104666 p1 s' t p2 t') (@lem4362635 _104663 p1 s h1)). Qed.
Lemma lem4362655 {_104663 _104666 : Type'} (p1 : _104663) (s' : _104663 -> Prop) (t : _104666 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : (term84 _104663 _104666 p1 s' t p2 t') = ((term85 _104663 _104666 t p1 s' p2 t') = (term86 _104663 _104666 p1 s' t p2 t')).
Proof. exact (eq_refl (term84 _104663 _104666 p1 s' t p2 t')). Qed.
Lemma lem4362656 {_104663 _104666 : Type'} (s' : _104663 -> Prop) (t : _104666 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) (p1 : _104663) (s : _104663 -> Prop) : (term87 _104663 _104666 s' t p2 t' p1 s) = (term87 _104663 _104666 s' t p2 t' p1 s).
Proof. exact (eq_refl (term87 _104663 _104666 s' t p2 t' p1 s)). Qed.
Lemma lem4362657 {_104663 _104666 : Type'} (s : _104663 -> Prop) (p1 : _104663) (s' : _104663 -> Prop) (t : _104666 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : ((term83 _104663 _104666 s' t p2 t' p1 s) = (term84 _104663 _104666 p1 s' t p2 t')) = ((term83 _104663 _104666 s' t p2 t' p1 s) = ((term85 _104663 _104666 t p1 s' p2 t') = (term86 _104663 _104666 p1 s' t p2 t'))).
Proof. exact (MK_COMB (@lem4362656 _104663 _104666 s' t p2 t' p1 s) (@lem4362655 _104663 _104666 p1 s' t p2 t')). Qed.
Lemma lem4362658 {_104663 _104666 : Type'} (s : _104663 -> Prop) (p1 : _104663) (s' : _104663 -> Prop) (t : _104666 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : (term83 _104663 _104666 s' t p2 t' p1 s) = ((term53 _104663 _104666 s t p1 s' p2 t') = (term59 _104663 _104666 s p1 s' t p2 t')).
Proof. exact (eq_refl (term83 _104663 _104666 s' t p2 t' p1 s)). Qed.
Lemma lem4362659 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4362660 {_104663 _104666 : Type'} (s : _104663 -> Prop) (p1 : _104663) (s' : _104663 -> Prop) (t : _104666 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : (term87 _104663 _104666 s' t p2 t' p1 s) = (term88 _104663 _104666 s p1 s' t p2 t').
Proof. exact (MK_COMB (@lem4362659) (@lem4362658 _104663 _104666 s p1 s' t p2 t')). Qed.
Lemma lem4362661 {_104663 _104666 : Type'} (p1 : _104663) (s' : _104663 -> Prop) (t : _104666 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : ((term85 _104663 _104666 t p1 s' p2 t') = (term86 _104663 _104666 p1 s' t p2 t')) = ((term85 _104663 _104666 t p1 s' p2 t') = (term86 _104663 _104666 p1 s' t p2 t')).
Proof. exact (eq_refl ((term85 _104663 _104666 t p1 s' p2 t') = (term86 _104663 _104666 p1 s' t p2 t'))). Qed.
Lemma lem4362662 {_104663 _104666 : Type'} (s : _104663 -> Prop) (p1 : _104663) (s' : _104663 -> Prop) (t : _104666 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : ((term83 _104663 _104666 s' t p2 t' p1 s) = ((term85 _104663 _104666 t p1 s' p2 t') = (term86 _104663 _104666 p1 s' t p2 t'))) = (((term53 _104663 _104666 s t p1 s' p2 t') = (term59 _104663 _104666 s p1 s' t p2 t')) = ((term85 _104663 _104666 t p1 s' p2 t') = (term86 _104663 _104666 p1 s' t p2 t'))).
Proof. exact (MK_COMB (@lem4362660 _104663 _104666 s p1 s' t p2 t') (@lem4362661 _104663 _104666 p1 s' t p2 t')). Qed.
Lemma lem4362663 {_104663 _104666 : Type'} (s : _104663 -> Prop) (p1 : _104663) (s' : _104663 -> Prop) (t : _104666 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : ((term83 _104663 _104666 s' t p2 t' p1 s) = (term84 _104663 _104666 p1 s' t p2 t')) = (((term53 _104663 _104666 s t p1 s' p2 t') = (term59 _104663 _104666 s p1 s' t p2 t')) = ((term85 _104663 _104666 t p1 s' p2 t') = (term86 _104663 _104666 p1 s' t p2 t'))).
Proof. exact (TRANS (@lem4362657 _104663 _104666 s p1 s' t p2 t') (@lem4362662 _104663 _104666 s p1 s' t p2 t')). Qed.
Lemma lem4362664 {_104663 _104666 : Type'} (s' : _104663 -> Prop) (t : _104666 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) (p1 : _104663) (s : _104663 -> Prop) (h1 : (@IN _104663 p1 s) = True) : ((term53 _104663 _104666 s t p1 s' p2 t') = (term59 _104663 _104666 s p1 s' t p2 t')) = ((term85 _104663 _104666 t p1 s' p2 t') = (term86 _104663 _104666 p1 s' t p2 t')).
Proof. exact (EQ_MP (@lem4362663 _104663 _104666 s p1 s' t p2 t') (@lem4362654 _104663 _104666 s' t p2 t' p1 s h1)). Qed.
Lemma lem4362665 {_104663 _104666 : Type'} (s' : _104663 -> Prop) (t : _104666 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) (p1 : _104663) (s : _104663 -> Prop) (h1 : (@IN _104663 p1 s) = True) : ((term85 _104663 _104666 t p1 s' p2 t') = (term86 _104663 _104666 p1 s' t p2 t')) = ((term53 _104663 _104666 s t p1 s' p2 t') = (term59 _104663 _104666 s p1 s' t p2 t')).
Proof. exact (SYM (@lem4362664 _104663 _104666 s' t p2 t' p1 s h1)). Qed.
Lemma lem4362666 {_104663 _104666 : Type'} (p1 : _104663) (s' : _104663 -> Prop) (t : _104666 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : (term82 _104663 _104666 p1 s' t p2 t') = (term82 _104663 _104666 p1 s' t p2 t').
Proof. exact (eq_refl (term82 _104663 _104666 p1 s' t p2 t')). Qed.
Lemma lem4362667 {_104663 _104666 : Type'} (s' : _104663 -> Prop) (t : _104666 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) (p1 : _104663) (s : _104663 -> Prop) (h1 : (@IN _104663 p1 s) = False) : (term83 _104663 _104666 s' t p2 t' p1 s) = (term89 _104663 _104666 p1 s' t p2 t').
Proof. exact (MK_COMB (@lem4362666 _104663 _104666 p1 s' t p2 t') (@lem4362636 _104663 p1 s h1)). Qed.
Lemma lem4362668 {_104663 _104666 : Type'} (p1 : _104663) (s' : _104663 -> Prop) (t : _104666 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : (term89 _104663 _104666 p1 s' t p2 t') = ((term90 _104663 _104666 t p1 s' p2 t') = (term91 _104663 _104666 p1 s' t p2 t')).
Proof. exact (eq_refl (term89 _104663 _104666 p1 s' t p2 t')). Qed.
Lemma lem4362669 {_104663 _104666 : Type'} (s' : _104663 -> Prop) (t : _104666 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) (p1 : _104663) (s : _104663 -> Prop) : (term87 _104663 _104666 s' t p2 t' p1 s) = (term87 _104663 _104666 s' t p2 t' p1 s).
Proof. exact (eq_refl (term87 _104663 _104666 s' t p2 t' p1 s)). Qed.
Lemma lem4362670 {_104663 _104666 : Type'} (s : _104663 -> Prop) (p1 : _104663) (s' : _104663 -> Prop) (t : _104666 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : ((term83 _104663 _104666 s' t p2 t' p1 s) = (term89 _104663 _104666 p1 s' t p2 t')) = ((term83 _104663 _104666 s' t p2 t' p1 s) = ((term90 _104663 _104666 t p1 s' p2 t') = (term91 _104663 _104666 p1 s' t p2 t'))).
Proof. exact (MK_COMB (@lem4362669 _104663 _104666 s' t p2 t' p1 s) (@lem4362668 _104663 _104666 p1 s' t p2 t')). Qed.
Lemma lem4362671 {_104663 _104666 : Type'} (s : _104663 -> Prop) (p1 : _104663) (s' : _104663 -> Prop) (t : _104666 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : (term83 _104663 _104666 s' t p2 t' p1 s) = ((term53 _104663 _104666 s t p1 s' p2 t') = (term59 _104663 _104666 s p1 s' t p2 t')).
Proof. exact (eq_refl (term83 _104663 _104666 s' t p2 t' p1 s)). Qed.
Lemma lem4362672 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4362673 {_104663 _104666 : Type'} (s : _104663 -> Prop) (p1 : _104663) (s' : _104663 -> Prop) (t : _104666 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : (term87 _104663 _104666 s' t p2 t' p1 s) = (term88 _104663 _104666 s p1 s' t p2 t').
Proof. exact (MK_COMB (@lem4362672) (@lem4362671 _104663 _104666 s p1 s' t p2 t')). Qed.
Lemma lem4362674 {_104663 _104666 : Type'} (p1 : _104663) (s' : _104663 -> Prop) (t : _104666 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : ((term90 _104663 _104666 t p1 s' p2 t') = (term91 _104663 _104666 p1 s' t p2 t')) = ((term90 _104663 _104666 t p1 s' p2 t') = (term91 _104663 _104666 p1 s' t p2 t')).
Proof. exact (eq_refl ((term90 _104663 _104666 t p1 s' p2 t') = (term91 _104663 _104666 p1 s' t p2 t'))). Qed.
Lemma lem4362675 {_104663 _104666 : Type'} (s : _104663 -> Prop) (p1 : _104663) (s' : _104663 -> Prop) (t : _104666 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : ((term83 _104663 _104666 s' t p2 t' p1 s) = ((term90 _104663 _104666 t p1 s' p2 t') = (term91 _104663 _104666 p1 s' t p2 t'))) = (((term53 _104663 _104666 s t p1 s' p2 t') = (term59 _104663 _104666 s p1 s' t p2 t')) = ((term90 _104663 _104666 t p1 s' p2 t') = (term91 _104663 _104666 p1 s' t p2 t'))).
Proof. exact (MK_COMB (@lem4362673 _104663 _104666 s p1 s' t p2 t') (@lem4362674 _104663 _104666 p1 s' t p2 t')). Qed.
Lemma lem4362676 {_104663 _104666 : Type'} (s : _104663 -> Prop) (p1 : _104663) (s' : _104663 -> Prop) (t : _104666 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : ((term83 _104663 _104666 s' t p2 t' p1 s) = (term89 _104663 _104666 p1 s' t p2 t')) = (((term53 _104663 _104666 s t p1 s' p2 t') = (term59 _104663 _104666 s p1 s' t p2 t')) = ((term90 _104663 _104666 t p1 s' p2 t') = (term91 _104663 _104666 p1 s' t p2 t'))).
Proof. exact (TRANS (@lem4362670 _104663 _104666 s p1 s' t p2 t') (@lem4362675 _104663 _104666 s p1 s' t p2 t')). Qed.
Lemma lem4362677 {_104663 _104666 : Type'} (s' : _104663 -> Prop) (t : _104666 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) (p1 : _104663) (s : _104663 -> Prop) (h1 : (@IN _104663 p1 s) = False) : ((term53 _104663 _104666 s t p1 s' p2 t') = (term59 _104663 _104666 s p1 s' t p2 t')) = ((term90 _104663 _104666 t p1 s' p2 t') = (term91 _104663 _104666 p1 s' t p2 t')).
Proof. exact (EQ_MP (@lem4362676 _104663 _104666 s p1 s' t p2 t') (@lem4362667 _104663 _104666 s' t p2 t' p1 s h1)). Qed.
Lemma lem4362678 {_104663 _104666 : Type'} (s' : _104663 -> Prop) (t : _104666 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) (p1 : _104663) (s : _104663 -> Prop) (h1 : (@IN _104663 p1 s) = False) : ((term90 _104663 _104666 t p1 s' p2 t') = (term91 _104663 _104666 p1 s' t p2 t')) = ((term53 _104663 _104666 s t p1 s' p2 t') = (term59 _104663 _104666 s p1 s' t p2 t')).
Proof. exact (SYM (@lem4362677 _104663 _104666 s' t p2 t' p1 s h1)). Qed.
Lemma lem4362684 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4362685 {_104666 : Type'} (p2 : _104666) (t : _104666 -> Prop) : (term92 _104666 p2 t) = (@IN _104666 p2 t).
Proof. exact (@lem4362684 (@IN _104666 p2 t)). Qed.
Lemma lem4362686 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4362687 {_104666 : Type'} (p2 : _104666) (t : _104666 -> Prop) : (term93 _104666 p2 t) = (term94 _104666 p2 t).
Proof. exact (MK_COMB (@lem4362686) (@lem4362685 _104666 p2 t)). Qed.
Lemma lem4362690 {_104663 _104666 : Type'} (p1 : _104663) (s' : _104663 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : (term8 _104663 _104666 p1 s' p2 t') = (term8 _104663 _104666 p1 s' p2 t').
Proof. exact (eq_refl (term8 _104663 _104666 p1 s' p2 t')). Qed.
Lemma lem4362691 {_104663 _104666 : Type'} (t : _104666 -> Prop) (p1 : _104663) (s' : _104663 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : (term85 _104663 _104666 t p1 s' p2 t') = (term95 _104663 _104666 t p1 s' p2 t').
Proof. exact (MK_COMB (@lem4362687 _104666 p2 t) (@lem4362690 _104663 _104666 p1 s' p2 t')). Qed.
Lemma lem4362694 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4362695 {_104663 _104666 : Type'} (t : _104666 -> Prop) (p1 : _104663) (s' : _104663 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : (term96 _104663 _104666 t p1 s' p2 t') = (term97 _104663 _104666 t p1 s' p2 t').
Proof. exact (MK_COMB (@lem4362694) (@lem4362691 _104663 _104666 t p1 s' p2 t')). Qed.
Lemma lem4362699 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4362700 {_104663 : Type'} (p1 : _104663) (s' : _104663 -> Prop) : (term92 _104663 p1 s') = (@IN _104663 p1 s').
Proof. exact (@lem4362699 (@IN _104663 p1 s')). Qed.
Lemma lem4362701 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4362702 {_104663 : Type'} (p1 : _104663) (s' : _104663 -> Prop) : (term93 _104663 p1 s') = (term94 _104663 p1 s').
Proof. exact (MK_COMB (@lem4362701) (@lem4362700 _104663 p1 s')). Qed.
Lemma lem4362705 {_104666 : Type'} (t : _104666 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : (term18 _104666 t p2 t') = (term18 _104666 t p2 t').
Proof. exact (eq_refl (term18 _104666 t p2 t')). Qed.
Lemma lem4362706 {_104663 _104666 : Type'} (p1 : _104663) (s' : _104663 -> Prop) (t : _104666 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : (term86 _104663 _104666 p1 s' t p2 t') = (term98 _104663 _104666 p1 s' t p2 t').
Proof. exact (MK_COMB (@lem4362702 _104663 p1 s') (@lem4362705 _104666 t p2 t')). Qed.
Lemma lem4362709 {_104663 _104666 : Type'} (p1 : _104663) (s' : _104663 -> Prop) (t : _104666 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : ((term85 _104663 _104666 t p1 s' p2 t') = (term86 _104663 _104666 p1 s' t p2 t')) = ((term95 _104663 _104666 t p1 s' p2 t') = (term98 _104663 _104666 p1 s' t p2 t')).
Proof. exact (MK_COMB (@lem4362695 _104663 _104666 t p1 s' p2 t') (@lem4362706 _104663 _104666 p1 s' t p2 t')). Qed.
Lemma lem4362712 {_104663 _104666 : Type'} (p1 : _104663) (s' : _104663 -> Prop) (t : _104666 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : ((term95 _104663 _104666 t p1 s' p2 t') = (term98 _104663 _104666 p1 s' t p2 t')) = ((term85 _104663 _104666 t p1 s' p2 t') = (term86 _104663 _104666 p1 s' t p2 t')).
Proof. exact (SYM (@lem4362709 _104663 _104666 p1 s' t p2 t')). Qed.
Lemma lem4362713 {_104666 : Type'} (p2 : _104666) (t : _104666 -> Prop) : term80 _104666 p2 t.
Proof. exact (@lem9851 (@IN _104666 p2 t)). Qed.
Lemma lem4362714 {_104666 : Type'} (p2 : _104666) (t : _104666 -> Prop) : (term80 _104666 p2 t) = (term81 _104666 p2 t).
Proof. exact (eq_refl (term80 _104666 p2 t)). Qed.
Lemma lem4362715 {_104666 : Type'} (p2 : _104666) (t : _104666 -> Prop) : term81 _104666 p2 t.
Proof. exact (EQ_MP (@lem4362714 _104666 p2 t) (@lem4362713 _104666 p2 t)). Qed.
Lemma lem4362716 {_104666 : Type'} (p2 : _104666) (t : _104666 -> Prop) (h1 : (@IN _104666 p2 t) = True) : (@IN _104666 p2 t) = True.
Proof. exact (h1). Qed.
Lemma lem4362717 {_104666 : Type'} (p2 : _104666) (t : _104666 -> Prop) (h1 : (@IN _104666 p2 t) = False) : (@IN _104666 p2 t) = False.
Proof. exact (h1). Qed.
Lemma lem4362730 {_104663 _104666 : Type'} (p1 : _104663) (s' : _104663 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : (term99 _104663 _104666 p1 s' p2 t') = (term99 _104663 _104666 p1 s' p2 t').
Proof. exact (eq_refl (term99 _104663 _104666 p1 s' p2 t')). Qed.
Lemma lem4362731 {_104663 _104666 : Type'} (p1 : _104663) (s' : _104663 -> Prop) (t' : _104666 -> Prop) (p2 : _104666) (t : _104666 -> Prop) (h1 : (@IN _104666 p2 t) = True) : (term100 _104663 _104666 p1 s' t' p2 t) = (term101 _104663 _104666 p1 s' p2 t').
Proof. exact (MK_COMB (@lem4362730 _104663 _104666 p1 s' p2 t') (@lem4362716 _104666 p2 t h1)). Qed.
Lemma lem4362732 {_104663 _104666 : Type'} (p1 : _104663) (s' : _104663 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : (term101 _104663 _104666 p1 s' p2 t') = ((term102 _104663 _104666 p1 s' p2 t') = (term103 _104663 _104666 p1 s' p2 t')).
Proof. exact (eq_refl (term101 _104663 _104666 p1 s' p2 t')). Qed.
Lemma lem4362733 {_104663 _104666 : Type'} (p1 : _104663) (s' : _104663 -> Prop) (t' : _104666 -> Prop) (p2 : _104666) (t : _104666 -> Prop) : (term104 _104663 _104666 p1 s' t' p2 t) = (term104 _104663 _104666 p1 s' t' p2 t).
Proof. exact (eq_refl (term104 _104663 _104666 p1 s' t' p2 t)). Qed.
Lemma lem4362734 {_104663 _104666 : Type'} (t : _104666 -> Prop) (p1 : _104663) (s' : _104663 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : ((term100 _104663 _104666 p1 s' t' p2 t) = (term101 _104663 _104666 p1 s' p2 t')) = ((term100 _104663 _104666 p1 s' t' p2 t) = ((term102 _104663 _104666 p1 s' p2 t') = (term103 _104663 _104666 p1 s' p2 t'))).
Proof. exact (MK_COMB (@lem4362733 _104663 _104666 p1 s' t' p2 t) (@lem4362732 _104663 _104666 p1 s' p2 t')). Qed.
Lemma lem4362735 {_104663 _104666 : Type'} (p1 : _104663) (s' : _104663 -> Prop) (t : _104666 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : (term100 _104663 _104666 p1 s' t' p2 t) = ((term95 _104663 _104666 t p1 s' p2 t') = (term98 _104663 _104666 p1 s' t p2 t')).
Proof. exact (eq_refl (term100 _104663 _104666 p1 s' t' p2 t)). Qed.
Lemma lem4362736 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4362737 {_104663 _104666 : Type'} (p1 : _104663) (s' : _104663 -> Prop) (t : _104666 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : (term104 _104663 _104666 p1 s' t' p2 t) = (term105 _104663 _104666 p1 s' t p2 t').
Proof. exact (MK_COMB (@lem4362736) (@lem4362735 _104663 _104666 p1 s' t p2 t')). Qed.
Lemma lem4362738 {_104663 _104666 : Type'} (p1 : _104663) (s' : _104663 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : ((term102 _104663 _104666 p1 s' p2 t') = (term103 _104663 _104666 p1 s' p2 t')) = ((term102 _104663 _104666 p1 s' p2 t') = (term103 _104663 _104666 p1 s' p2 t')).
Proof. exact (eq_refl ((term102 _104663 _104666 p1 s' p2 t') = (term103 _104663 _104666 p1 s' p2 t'))). Qed.
Lemma lem4362739 {_104663 _104666 : Type'} (t : _104666 -> Prop) (p1 : _104663) (s' : _104663 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : ((term100 _104663 _104666 p1 s' t' p2 t) = ((term102 _104663 _104666 p1 s' p2 t') = (term103 _104663 _104666 p1 s' p2 t'))) = (((term95 _104663 _104666 t p1 s' p2 t') = (term98 _104663 _104666 p1 s' t p2 t')) = ((term102 _104663 _104666 p1 s' p2 t') = (term103 _104663 _104666 p1 s' p2 t'))).
Proof. exact (MK_COMB (@lem4362737 _104663 _104666 p1 s' t p2 t') (@lem4362738 _104663 _104666 p1 s' p2 t')). Qed.
Lemma lem4362740 {_104663 _104666 : Type'} (t : _104666 -> Prop) (p1 : _104663) (s' : _104663 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : ((term100 _104663 _104666 p1 s' t' p2 t) = (term101 _104663 _104666 p1 s' p2 t')) = (((term95 _104663 _104666 t p1 s' p2 t') = (term98 _104663 _104666 p1 s' t p2 t')) = ((term102 _104663 _104666 p1 s' p2 t') = (term103 _104663 _104666 p1 s' p2 t'))).
Proof. exact (TRANS (@lem4362734 _104663 _104666 t p1 s' p2 t') (@lem4362739 _104663 _104666 t p1 s' p2 t')). Qed.
Lemma lem4362741 {_104663 _104666 : Type'} (p1 : _104663) (s' : _104663 -> Prop) (t' : _104666 -> Prop) (p2 : _104666) (t : _104666 -> Prop) (h1 : (@IN _104666 p2 t) = True) : ((term95 _104663 _104666 t p1 s' p2 t') = (term98 _104663 _104666 p1 s' t p2 t')) = ((term102 _104663 _104666 p1 s' p2 t') = (term103 _104663 _104666 p1 s' p2 t')).
Proof. exact (EQ_MP (@lem4362740 _104663 _104666 t p1 s' p2 t') (@lem4362731 _104663 _104666 p1 s' t' p2 t h1)). Qed.
Lemma lem4362742 {_104663 _104666 : Type'} (p1 : _104663) (s' : _104663 -> Prop) (t' : _104666 -> Prop) (p2 : _104666) (t : _104666 -> Prop) (h1 : (@IN _104666 p2 t) = True) : ((term102 _104663 _104666 p1 s' p2 t') = (term103 _104663 _104666 p1 s' p2 t')) = ((term95 _104663 _104666 t p1 s' p2 t') = (term98 _104663 _104666 p1 s' t p2 t')).
Proof. exact (SYM (@lem4362741 _104663 _104666 p1 s' t' p2 t h1)). Qed.
Lemma lem4362743 {_104663 _104666 : Type'} (p1 : _104663) (s' : _104663 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : (term99 _104663 _104666 p1 s' p2 t') = (term99 _104663 _104666 p1 s' p2 t').
Proof. exact (eq_refl (term99 _104663 _104666 p1 s' p2 t')). Qed.
Lemma lem4362744 {_104663 _104666 : Type'} (p1 : _104663) (s' : _104663 -> Prop) (t' : _104666 -> Prop) (p2 : _104666) (t : _104666 -> Prop) (h1 : (@IN _104666 p2 t) = False) : (term100 _104663 _104666 p1 s' t' p2 t) = (term106 _104663 _104666 p1 s' p2 t').
Proof. exact (MK_COMB (@lem4362743 _104663 _104666 p1 s' p2 t') (@lem4362717 _104666 p2 t h1)). Qed.
Lemma lem4362745 {_104663 _104666 : Type'} (p1 : _104663) (s' : _104663 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : (term106 _104663 _104666 p1 s' p2 t') = ((term107 _104663 _104666 p1 s' p2 t') = (term108 _104663 _104666 p1 s' p2 t')).
Proof. exact (eq_refl (term106 _104663 _104666 p1 s' p2 t')). Qed.
Lemma lem4362746 {_104663 _104666 : Type'} (p1 : _104663) (s' : _104663 -> Prop) (t' : _104666 -> Prop) (p2 : _104666) (t : _104666 -> Prop) : (term104 _104663 _104666 p1 s' t' p2 t) = (term104 _104663 _104666 p1 s' t' p2 t).
Proof. exact (eq_refl (term104 _104663 _104666 p1 s' t' p2 t)). Qed.
Lemma lem4362747 {_104663 _104666 : Type'} (t : _104666 -> Prop) (p1 : _104663) (s' : _104663 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : ((term100 _104663 _104666 p1 s' t' p2 t) = (term106 _104663 _104666 p1 s' p2 t')) = ((term100 _104663 _104666 p1 s' t' p2 t) = ((term107 _104663 _104666 p1 s' p2 t') = (term108 _104663 _104666 p1 s' p2 t'))).
Proof. exact (MK_COMB (@lem4362746 _104663 _104666 p1 s' t' p2 t) (@lem4362745 _104663 _104666 p1 s' p2 t')). Qed.
Lemma lem4362748 {_104663 _104666 : Type'} (p1 : _104663) (s' : _104663 -> Prop) (t : _104666 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : (term100 _104663 _104666 p1 s' t' p2 t) = ((term95 _104663 _104666 t p1 s' p2 t') = (term98 _104663 _104666 p1 s' t p2 t')).
Proof. exact (eq_refl (term100 _104663 _104666 p1 s' t' p2 t)). Qed.
Lemma lem4362749 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4362750 {_104663 _104666 : Type'} (p1 : _104663) (s' : _104663 -> Prop) (t : _104666 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : (term104 _104663 _104666 p1 s' t' p2 t) = (term105 _104663 _104666 p1 s' t p2 t').
Proof. exact (MK_COMB (@lem4362749) (@lem4362748 _104663 _104666 p1 s' t p2 t')). Qed.
Lemma lem4362751 {_104663 _104666 : Type'} (p1 : _104663) (s' : _104663 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : ((term107 _104663 _104666 p1 s' p2 t') = (term108 _104663 _104666 p1 s' p2 t')) = ((term107 _104663 _104666 p1 s' p2 t') = (term108 _104663 _104666 p1 s' p2 t')).
Proof. exact (eq_refl ((term107 _104663 _104666 p1 s' p2 t') = (term108 _104663 _104666 p1 s' p2 t'))). Qed.
Lemma lem4362752 {_104663 _104666 : Type'} (t : _104666 -> Prop) (p1 : _104663) (s' : _104663 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : ((term100 _104663 _104666 p1 s' t' p2 t) = ((term107 _104663 _104666 p1 s' p2 t') = (term108 _104663 _104666 p1 s' p2 t'))) = (((term95 _104663 _104666 t p1 s' p2 t') = (term98 _104663 _104666 p1 s' t p2 t')) = ((term107 _104663 _104666 p1 s' p2 t') = (term108 _104663 _104666 p1 s' p2 t'))).
Proof. exact (MK_COMB (@lem4362750 _104663 _104666 p1 s' t p2 t') (@lem4362751 _104663 _104666 p1 s' p2 t')). Qed.
Lemma lem4362753 {_104663 _104666 : Type'} (t : _104666 -> Prop) (p1 : _104663) (s' : _104663 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : ((term100 _104663 _104666 p1 s' t' p2 t) = (term106 _104663 _104666 p1 s' p2 t')) = (((term95 _104663 _104666 t p1 s' p2 t') = (term98 _104663 _104666 p1 s' t p2 t')) = ((term107 _104663 _104666 p1 s' p2 t') = (term108 _104663 _104666 p1 s' p2 t'))).
Proof. exact (TRANS (@lem4362747 _104663 _104666 t p1 s' p2 t') (@lem4362752 _104663 _104666 t p1 s' p2 t')). Qed.
Lemma lem4362754 {_104663 _104666 : Type'} (p1 : _104663) (s' : _104663 -> Prop) (t' : _104666 -> Prop) (p2 : _104666) (t : _104666 -> Prop) (h1 : (@IN _104666 p2 t) = False) : ((term95 _104663 _104666 t p1 s' p2 t') = (term98 _104663 _104666 p1 s' t p2 t')) = ((term107 _104663 _104666 p1 s' p2 t') = (term108 _104663 _104666 p1 s' p2 t')).
Proof. exact (EQ_MP (@lem4362753 _104663 _104666 t p1 s' p2 t') (@lem4362744 _104663 _104666 p1 s' t' p2 t h1)). Qed.
Lemma lem4362755 {_104663 _104666 : Type'} (p1 : _104663) (s' : _104663 -> Prop) (t' : _104666 -> Prop) (p2 : _104666) (t : _104666 -> Prop) (h1 : (@IN _104666 p2 t) = False) : ((term107 _104663 _104666 p1 s' p2 t') = (term108 _104663 _104666 p1 s' p2 t')) = ((term95 _104663 _104666 t p1 s' p2 t') = (term98 _104663 _104666 p1 s' t p2 t')).
Proof. exact (SYM (@lem4362754 _104663 _104666 p1 s' t' p2 t h1)). Qed.
Lemma lem4362759 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4362760 {_104663 _104666 : Type'} (p1 : _104663) (s' : _104663 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : (term102 _104663 _104666 p1 s' p2 t') = (term8 _104663 _104666 p1 s' p2 t').
Proof. exact (@lem4362759 (term8 _104663 _104666 p1 s' p2 t')). Qed.
Lemma lem4362763 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4362764 {_104663 _104666 : Type'} (p1 : _104663) (s' : _104663 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : (term109 _104663 _104666 p1 s' p2 t') = (term110 _104663 _104666 p1 s' p2 t').
Proof. exact (MK_COMB (@lem4362763) (@lem4362760 _104663 _104666 p1 s' p2 t')). Qed.
Lemma lem4362768 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4362769 {_104666 : Type'} (p2 : _104666) (t' : _104666 -> Prop) : (term92 _104666 p2 t') = (@IN _104666 p2 t').
Proof. exact (@lem4362768 (@IN _104666 p2 t')). Qed.
Lemma lem4362770 {_104663 : Type'} (p1 : _104663) (s' : _104663 -> Prop) : (term94 _104663 p1 s') = (term94 _104663 p1 s').
Proof. exact (eq_refl (term94 _104663 p1 s')). Qed.
Lemma lem4362771 {_104663 _104666 : Type'} (p1 : _104663) (s' : _104663 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : (term103 _104663 _104666 p1 s' p2 t') = (term8 _104663 _104666 p1 s' p2 t').
Proof. exact (MK_COMB (@lem4362770 _104663 p1 s') (@lem4362769 _104666 p2 t')). Qed.
Lemma lem4362774 {_104663 _104666 : Type'} (p1 : _104663) (s' : _104663 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : ((term102 _104663 _104666 p1 s' p2 t') = (term103 _104663 _104666 p1 s' p2 t')) = ((term8 _104663 _104666 p1 s' p2 t') = (term8 _104663 _104666 p1 s' p2 t')).
Proof. exact (MK_COMB (@lem4362764 _104663 _104666 p1 s' p2 t') (@lem4362771 _104663 _104666 p1 s' p2 t')). Qed.
Lemma lem4362776 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4362777 (x : Prop) : (x = x) = True.
Proof. exact (@lem4362776 Prop x). Qed.
Lemma lem4362778 {_104663 _104666 : Type'} (p1 : _104663) (s' : _104663 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : ((term8 _104663 _104666 p1 s' p2 t') = (term8 _104663 _104666 p1 s' p2 t')) = True.
Proof. exact (@lem4362777 (term8 _104663 _104666 p1 s' p2 t')). Qed.
Lemma lem4362779 {_104663 _104666 : Type'} (p1 : _104663) (s' : _104663 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : ((term102 _104663 _104666 p1 s' p2 t') = (term103 _104663 _104666 p1 s' p2 t')) = True.
Proof. exact (TRANS (@lem4362774 _104663 _104666 p1 s' p2 t') (@lem4362778 _104663 _104666 p1 s' p2 t')). Qed.
Lemma lem4362780 {_104663 _104666 : Type'} (p1 : _104663) (s' : _104663 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : True = ((term102 _104663 _104666 p1 s' p2 t') = (term103 _104663 _104666 p1 s' p2 t')).
Proof. exact (SYM (@lem4362779 _104663 _104666 p1 s' p2 t')). Qed.
Lemma lem4362781 {_104663 _104666 : Type'} (p1 : _104663) (s' : _104663 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : (term102 _104663 _104666 p1 s' p2 t') = (term103 _104663 _104666 p1 s' p2 t').
Proof. exact (EQ_MP (@lem4362780 _104663 _104666 p1 s' p2 t') (@lem0)). Qed.
Lemma lem4362785 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem4362786 {_104663 _104666 : Type'} (p1 : _104663) (s' : _104663 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : (term107 _104663 _104666 p1 s' p2 t') = False.
Proof. exact (@lem4362785 (term8 _104663 _104666 p1 s' p2 t')). Qed.
Lemma lem4362787 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4362788 {_104663 _104666 : Type'} (p1 : _104663) (s' : _104663 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : (term111 _104663 _104666 p1 s' p2 t') = (@eq Prop False).
Proof. exact (MK_COMB (@lem4362787) (@lem4362786 _104663 _104666 p1 s' p2 t')). Qed.
Lemma lem4362792 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem4362793 {_104666 : Type'} (p2 : _104666) (t' : _104666 -> Prop) : (term112 _104666 p2 t') = False.
Proof. exact (@lem4362792 (@IN _104666 p2 t')). Qed.
Lemma lem4362794 {_104663 : Type'} (p1 : _104663) (s' : _104663 -> Prop) : (term94 _104663 p1 s') = (term94 _104663 p1 s').
Proof. exact (eq_refl (term94 _104663 p1 s')). Qed.
Lemma lem4362795 {_104663 _104666 : Type'} (p2 : _104666) (t' : _104666 -> Prop) (p1 : _104663) (s' : _104663 -> Prop) : (term108 _104663 _104666 p1 s' p2 t') = (term113 _104663 p1 s').
Proof. exact (MK_COMB (@lem4362794 _104663 p1 s') (@lem4362793 _104666 p2 t')). Qed.
Lemma lem4362797 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem4362798 {_104663 : Type'} (p1 : _104663) (s' : _104663 -> Prop) : (term113 _104663 p1 s') = False.
Proof. exact (@lem4362797 (@IN _104663 p1 s')). Qed.
Lemma lem4362799 {_104663 _104666 : Type'} (p1 : _104663) (s' : _104663 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : (term108 _104663 _104666 p1 s' p2 t') = False.
Proof. exact (TRANS (@lem4362795 _104663 _104666 p2 t' p1 s') (@lem4362798 _104663 p1 s')). Qed.
Lemma lem4362800 {_104663 _104666 : Type'} (p1 : _104663) (s' : _104663 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : ((term107 _104663 _104666 p1 s' p2 t') = (term108 _104663 _104666 p1 s' p2 t')) = (False = False).
Proof. exact (MK_COMB (@lem4362788 _104663 _104666 p1 s' p2 t') (@lem4362799 _104663 _104666 p1 s' p2 t')). Qed.
Lemma lem4362802 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem4362803 : (False = False) = (~ False).
Proof. exact (@lem4362802 False). Qed.
Lemma lem4362805 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem4362806 : (False = False) = True.
Proof. exact (TRANS (@lem4362803) (@lem4362805)). Qed.
Lemma lem4362807 {_104663 _104666 : Type'} (p1 : _104663) (s' : _104663 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : ((term107 _104663 _104666 p1 s' p2 t') = (term108 _104663 _104666 p1 s' p2 t')) = True.
Proof. exact (TRANS (@lem4362800 _104663 _104666 p1 s' p2 t') (@lem4362806)). Qed.
Lemma lem4362808 {_104663 _104666 : Type'} (p1 : _104663) (s' : _104663 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : True = ((term107 _104663 _104666 p1 s' p2 t') = (term108 _104663 _104666 p1 s' p2 t')).
Proof. exact (SYM (@lem4362807 _104663 _104666 p1 s' p2 t')). Qed.
Lemma lem4362809 {_104663 _104666 : Type'} (p1 : _104663) (s' : _104663 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : (term107 _104663 _104666 p1 s' p2 t') = (term108 _104663 _104666 p1 s' p2 t').
Proof. exact (EQ_MP (@lem4362808 _104663 _104666 p1 s' p2 t') (@lem0)). Qed.
Lemma lem4362810 {_104663 _104666 : Type'} (p1 : _104663) (s' : _104663 -> Prop) (t' : _104666 -> Prop) (p2 : _104666) (t : _104666 -> Prop) (h1 : (@IN _104666 p2 t) = False) : (term95 _104663 _104666 t p1 s' p2 t') = (term98 _104663 _104666 p1 s' t p2 t').
Proof. exact (EQ_MP (@lem4362755 _104663 _104666 p1 s' t' p2 t h1) (@lem4362809 _104663 _104666 p1 s' p2 t')). Qed.
Lemma lem4362811 {_104663 _104666 : Type'} (p1 : _104663) (s' : _104663 -> Prop) (t' : _104666 -> Prop) (p2 : _104666) (t : _104666 -> Prop) (h1 : (@IN _104666 p2 t) = True) : (term95 _104663 _104666 t p1 s' p2 t') = (term98 _104663 _104666 p1 s' t p2 t').
Proof. exact (EQ_MP (@lem4362742 _104663 _104666 p1 s' t' p2 t h1) (@lem4362781 _104663 _104666 p1 s' p2 t')). Qed.
Lemma lem4362813 {_104663 _104666 : Type'} (p1 : _104663) (s' : _104663 -> Prop) (t : _104666 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : (term95 _104663 _104666 t p1 s' p2 t') = (term98 _104663 _104666 p1 s' t p2 t').
Proof. exact (or_elim (@lem4362715 _104666 p2 t) (fun h0 : (@IN _104666 p2 t) = True => @lem4362811 _104663 _104666 p1 s' t' p2 t h0) (fun h0 : (@IN _104666 p2 t) = False => @lem4362810 _104663 _104666 p1 s' t' p2 t h0)). Qed.
Lemma lem4362814 {_104663 _104666 : Type'} (p1 : _104663) (s' : _104663 -> Prop) (t : _104666 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : (term85 _104663 _104666 t p1 s' p2 t') = (term86 _104663 _104666 p1 s' t p2 t').
Proof. exact (EQ_MP (@lem4362712 _104663 _104666 p1 s' t p2 t') (@lem4362813 _104663 _104666 p1 s' t p2 t')). Qed.
Lemma lem4362820 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem4362821 {_104666 : Type'} (p2 : _104666) (t : _104666 -> Prop) : (term112 _104666 p2 t) = False.
Proof. exact (@lem4362820 (@IN _104666 p2 t)). Qed.
Lemma lem4362822 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4362823 {_104666 : Type'} (p2 : _104666) (t : _104666 -> Prop) : (term114 _104666 p2 t) = (and False).
Proof. exact (MK_COMB (@lem4362822) (@lem4362821 _104666 p2 t)). Qed.
Lemma lem4362826 {_104663 _104666 : Type'} (p1 : _104663) (s' : _104663 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : (term8 _104663 _104666 p1 s' p2 t') = (term8 _104663 _104666 p1 s' p2 t').
Proof. exact (eq_refl (term8 _104663 _104666 p1 s' p2 t')). Qed.
Lemma lem4362827 {_104663 _104666 : Type'} (t : _104666 -> Prop) (p1 : _104663) (s' : _104663 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : (term90 _104663 _104666 t p1 s' p2 t') = (term107 _104663 _104666 p1 s' p2 t').
Proof. exact (MK_COMB (@lem4362823 _104666 p2 t) (@lem4362826 _104663 _104666 p1 s' p2 t')). Qed.
Lemma lem4362829 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem4362830 {_104663 _104666 : Type'} (p1 : _104663) (s' : _104663 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : (term107 _104663 _104666 p1 s' p2 t') = False.
Proof. exact (@lem4362829 (term8 _104663 _104666 p1 s' p2 t')). Qed.
Lemma lem4362831 {_104663 _104666 : Type'} (t : _104666 -> Prop) (p1 : _104663) (s' : _104663 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : (term90 _104663 _104666 t p1 s' p2 t') = False.
Proof. exact (TRANS (@lem4362827 _104663 _104666 t p1 s' p2 t') (@lem4362830 _104663 _104666 p1 s' p2 t')). Qed.
Lemma lem4362832 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4362833 {_104663 _104666 : Type'} (t : _104666 -> Prop) (p1 : _104663) (s' : _104663 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : (term115 _104663 _104666 t p1 s' p2 t') = (@eq Prop False).
Proof. exact (MK_COMB (@lem4362832) (@lem4362831 _104663 _104666 t p1 s' p2 t')). Qed.
Lemma lem4362837 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem4362838 {_104663 : Type'} (p1 : _104663) (s' : _104663 -> Prop) : (term112 _104663 p1 s') = False.
Proof. exact (@lem4362837 (@IN _104663 p1 s')). Qed.
Lemma lem4362839 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4362840 {_104663 : Type'} (p1 : _104663) (s' : _104663 -> Prop) : (term114 _104663 p1 s') = (and False).
Proof. exact (MK_COMB (@lem4362839) (@lem4362838 _104663 p1 s')). Qed.
Lemma lem4362843 {_104666 : Type'} (t : _104666 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : (term18 _104666 t p2 t') = (term18 _104666 t p2 t').
Proof. exact (eq_refl (term18 _104666 t p2 t')). Qed.
Lemma lem4362844 {_104663 _104666 : Type'} (p1 : _104663) (s' : _104663 -> Prop) (t : _104666 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : (term91 _104663 _104666 p1 s' t p2 t') = (term116 _104666 t p2 t').
Proof. exact (MK_COMB (@lem4362840 _104663 p1 s') (@lem4362843 _104666 t p2 t')). Qed.
Lemma lem4362846 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem4362847 {_104666 : Type'} (t : _104666 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : (term116 _104666 t p2 t') = False.
Proof. exact (@lem4362846 (term18 _104666 t p2 t')). Qed.
Lemma lem4362848 {_104663 _104666 : Type'} (p1 : _104663) (s' : _104663 -> Prop) (t : _104666 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : (term91 _104663 _104666 p1 s' t p2 t') = False.
Proof. exact (TRANS (@lem4362844 _104663 _104666 p1 s' t p2 t') (@lem4362847 _104666 t p2 t')). Qed.
Lemma lem4362849 {_104663 _104666 : Type'} (p1 : _104663) (s' : _104663 -> Prop) (t : _104666 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : ((term90 _104663 _104666 t p1 s' p2 t') = (term91 _104663 _104666 p1 s' t p2 t')) = (False = False).
Proof. exact (MK_COMB (@lem4362833 _104663 _104666 t p1 s' p2 t') (@lem4362848 _104663 _104666 p1 s' t p2 t')). Qed.
Lemma lem4362851 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem4362852 : (False = False) = (~ False).
Proof. exact (@lem4362851 False). Qed.
Lemma lem4362854 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem4362855 : (False = False) = True.
Proof. exact (TRANS (@lem4362852) (@lem4362854)). Qed.
Lemma lem4362856 {_104663 _104666 : Type'} (p1 : _104663) (s' : _104663 -> Prop) (t : _104666 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : ((term90 _104663 _104666 t p1 s' p2 t') = (term91 _104663 _104666 p1 s' t p2 t')) = True.
Proof. exact (TRANS (@lem4362849 _104663 _104666 p1 s' t p2 t') (@lem4362855)). Qed.
Lemma lem4362857 {_104663 _104666 : Type'} (p1 : _104663) (s' : _104663 -> Prop) (t : _104666 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : True = ((term90 _104663 _104666 t p1 s' p2 t') = (term91 _104663 _104666 p1 s' t p2 t')).
Proof. exact (SYM (@lem4362856 _104663 _104666 p1 s' t p2 t')). Qed.
Lemma lem4362858 {_104663 _104666 : Type'} (p1 : _104663) (s' : _104663 -> Prop) (t : _104666 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : (term90 _104663 _104666 t p1 s' p2 t') = (term91 _104663 _104666 p1 s' t p2 t').
Proof. exact (EQ_MP (@lem4362857 _104663 _104666 p1 s' t p2 t') (@lem0)). Qed.
Lemma lem4362859 {_104663 _104666 : Type'} (s' : _104663 -> Prop) (t : _104666 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) (p1 : _104663) (s : _104663 -> Prop) (h1 : (@IN _104663 p1 s) = False) : (term53 _104663 _104666 s t p1 s' p2 t') = (term59 _104663 _104666 s p1 s' t p2 t').
Proof. exact (EQ_MP (@lem4362678 _104663 _104666 s' t p2 t' p1 s h1) (@lem4362858 _104663 _104666 p1 s' t p2 t')). Qed.
Lemma lem4362860 {_104663 _104666 : Type'} (s' : _104663 -> Prop) (t : _104666 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) (p1 : _104663) (s : _104663 -> Prop) (h1 : (@IN _104663 p1 s) = True) : (term53 _104663 _104666 s t p1 s' p2 t') = (term59 _104663 _104666 s p1 s' t p2 t').
Proof. exact (EQ_MP (@lem4362665 _104663 _104666 s' t p2 t' p1 s h1) (@lem4362814 _104663 _104666 p1 s' t p2 t')). Qed.
Lemma lem4362863 {_104663 _104666 : Type'} (s : _104663 -> Prop) (p1 : _104663) (s' : _104663 -> Prop) (t : _104666 -> Prop) (p2 : _104666) (t' : _104666 -> Prop) : (term53 _104663 _104666 s t p1 s' p2 t') = (term59 _104663 _104666 s p1 s' t p2 t').
Proof. exact (or_elim (@lem4362634 _104663 p1 s) (fun h0 : (@IN _104663 p1 s) = True => @lem4362860 _104663 _104666 s' t p2 t' p1 s h0) (fun h0 : (@IN _104663 p1 s) = False => @lem4362859 _104663 _104666 s' t p2 t' p1 s h0)). Qed.
Lemma lem4362868 {_104663 _104666 : Type'} (s : _104663 -> Prop) (p1 : _104663) (s' : _104663 -> Prop) (t : _104666 -> Prop) (t' : _104666 -> Prop) : term61 _104663 _104666 s p1 s' t t'.
Proof. exact (fun p2 : _104666 => @lem4362863 _104663 _104666 s p1 s' t p2 t'). Qed.
Lemma lem4362873 {_104663 _104666 : Type'} (s : _104663 -> Prop) (s' : _104663 -> Prop) (t : _104666 -> Prop) (t' : _104666 -> Prop) : term63 _104663 _104666 s s' t t'.
Proof. exact (fun p1 : _104663 => @lem4362868 _104663 _104666 s p1 s' t t'). Qed.
Lemma lem4362878 {_104663 _104666 : Type'} (s : _104663 -> Prop) (s' : _104663 -> Prop) (t : _104666 -> Prop) : term67 _104663 _104666 s s' t.
Proof. exact (fun t' : _104666 -> Prop => @lem4362873 _104663 _104666 s s' t t'). Qed.
Lemma lem4362883 {_104663 _104666 : Type'} (s : _104663 -> Prop) (s' : _104663 -> Prop) : term71 _104663 _104666 s s'.
Proof. exact (fun t : _104666 -> Prop => @lem4362878 _104663 _104666 s s' t). Qed.
Lemma lem4362888 {_104663 _104666 : Type'} (s : _104663 -> Prop) : term75 _104663 _104666 s.
Proof. exact (fun s' : _104663 -> Prop => @lem4362883 _104663 _104666 s s'). Qed.
Lemma lem4362893 {_104663 _104666 : Type'} : term79 _104663 _104666.
Proof. exact (fun s : _104663 -> Prop => @lem4362888 _104663 _104666 s). Qed.
Lemma lem4362894 {_104663 _104666 : Type'} : term78 _104663 _104666.
Proof. exact (EQ_MP (@lem4362615 _104663 _104666) (@lem4362893 _104663 _104666)). Qed.
