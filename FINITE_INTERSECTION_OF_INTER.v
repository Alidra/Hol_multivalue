Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_INTERSECTION_OF_INTER_term_abbrevs.
Require Import FINITE_EMPTY_spec.
Require Import FINITE_INSERT_spec.
Require Import FINITE_INTERSECTION_OF_INTERS_spec.
Require Import FORALL_IN_INSERT_spec.
Require Import INTERS_2_spec.
Require Import NOT_IN_EMPTY_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1822_spec.
Require Import thm1842_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem4887422 {A : Type'} (x : A) : term0 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem4887423 {A : Type'} (x : A) : (term0 A x) = (term1 A x).
Proof. exact (eq_refl (term0 A x)). Qed.
Lemma lem4887424 {A : Type'} (x : A) : term1 A x.
Proof. exact (EQ_MP (@lem4887423 A x) (@lem4887422 A x)). Qed.
Lemma lem4887425 {A : Type'} (x : A) : term2 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem4887427 {_92140 : Type'} : (@FINITE _92140 (@EMPTY _92140)) = ((@FINITE _92140 (@EMPTY _92140)) = True).
Proof. exact (@lem7 (@FINITE _92140 (@EMPTY _92140))). Qed.
Lemma lem4887429 {A : Type'} (h1 : term3 A) : term3 A.
Proof. exact (h1). Qed.
Lemma lem4887430 {A : Type'} (P : type686 A) (h1 : term3 A) : term4 A P.
Proof. exact (@lem4887429 A h1 P). Qed.
Lemma lem4887431 {A : Type'} (P : type686 A) : (term4 A P) = (term5 A P).
Proof. exact (eq_refl (term4 A P)). Qed.
Lemma lem4887432 {A : Type'} (P : type686 A) (h1 : term3 A) : term5 A P.
Proof. exact (EQ_MP (@lem4887431 A P) (@lem4887430 A P h1)). Qed.
Lemma lem4887433 {A : Type'} (P : type686 A) (u : type686 A) (h1 : term3 A) : term6 A P u.
Proof. exact (@lem4887432 A P h1 u). Qed.
Lemma lem4887434 {A : Type'} (P : type686 A) (u : type686 A) : (term6 A P u) = (term7 A P u).
Proof. exact (eq_refl (term6 A P u)). Qed.
Lemma lem4887435 {A : Type'} (P : type686 A) (u : type686 A) (h1 : term3 A) : term7 A P u.
Proof. exact (EQ_MP (@lem4887434 A P u) (@lem4887433 A P u h1)). Qed.
Lemma lem4887436 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term8 A u P) : term8 A u P.
Proof. exact (h1). Qed.
Lemma lem4887437 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term3 A) (h2 : term8 A u P) : term9 A P u.
Proof. exact (@lem4887435 A P u h1 (@lem4887436 A u P h2)). Qed.
Lemma lem4887438 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term8 A u P) : term10 A P u.
Proof. exact (fun h0 : term3 A => @lem4887437 A u P h0 h1). Qed.
Lemma lem4887439 {A : Type'} (h1 : term3 A) : term3 A.
Proof. exact (h1). Qed.
Lemma lem4887440 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term3 A) (h2 : term8 A u P) : term9 A P u.
Proof. exact (@lem4887438 A u P h2 (@lem4887439 A h1)). Qed.
Lemma lem4887441 {A : Type'} (P : type686 A) (u : type686 A) (h1 : term3 A) : term7 A P u.
Proof. exact (fun h0 : term8 A u P => @lem4887440 A u P h1 h0). Qed.
Lemma lem4887442 {A : Type'} (P : type686 A) (h1 : term3 A) : term5 A P.
Proof. exact (fun u : type686 A => @lem4887441 A P u h1). Qed.
Lemma lem4887443 {A : Type'} (h1 : term3 A) : term3 A.
Proof. exact (fun P : type686 A => @lem4887442 A P h1). Qed.
Lemma lem4887444 {A : Type'} : term11 A.
Proof. exact (fun h0 : term3 A => @lem4887443 A h0). Qed.
Lemma lem4887445 {A : Type'} : term3 A.
Proof. exact (@lem4887444 A (@lem4887421 A)). Qed.
Lemma lem4887446 {A : Type'} (P : type686 A) : term4 A P.
Proof. exact (@lem4887445 A P). Qed.
Lemma lem4887447 {A : Type'} (P : type686 A) : (term4 A P) = (term5 A P).
Proof. exact (eq_refl (term4 A P)). Qed.
Lemma lem4887448 {A : Type'} (P : type686 A) : term5 A P.
Proof. exact (EQ_MP (@lem4887447 A P) (@lem4887446 A P)). Qed.
Lemma lem4887449 {A : Type'} (P : type686 A) (u : type686 A) : term6 A P u.
Proof. exact (@lem4887448 A P u). Qed.
Lemma lem4887450 {A : Type'} (P : type686 A) (u : type686 A) : (term6 A P u) = (term7 A P u).
Proof. exact (eq_refl (term6 A P u)). Qed.
Lemma lem4887452 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (h1 : (term12 _87260 s t) = (@INTER _87260 s t)) : (term12 _87260 s t) = (@INTER _87260 s t).
Proof. exact (h1). Qed.
Lemma lem4887453 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (h1 : (term12 _87260 s t) = (@INTER _87260 s t)) : (@INTER _87260 s t) = (term12 _87260 s t).
Proof. exact (SYM (@lem4887452 _87260 s t h1)). Qed.
Lemma lem4887454 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (h1 : (@INTER _87260 s t) = (term12 _87260 s t)) : (@INTER _87260 s t) = (term12 _87260 s t).
Proof. exact (h1). Qed.
Lemma lem4887455 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (h1 : (@INTER _87260 s t) = (term12 _87260 s t)) : (term12 _87260 s t) = (@INTER _87260 s t).
Proof. exact (SYM (@lem4887454 _87260 s t h1)). Qed.
Lemma lem4887456 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) : ((term12 _87260 s t) = (@INTER _87260 s t)) = ((@INTER _87260 s t) = (term12 _87260 s t)).
Proof. exact (prop_ext (fun h1 : (term12 _87260 s t) = (@INTER _87260 s t) => @lem4887453 _87260 s t h1) (fun h1 : (@INTER _87260 s t) = (term12 _87260 s t) => @lem4887455 _87260 s t h1)). Qed.
Lemma lem4887458 {_112528 : Type'} (s : _112528 -> Prop) (P : type686 _112528) (t : _112528 -> Prop) (h1 : term13 _112528 s P t) : term13 _112528 s P t.
Proof. exact (h1). Qed.
Lemma lem4887459 {_112528 : Type'} (P : type686 _112528) (t : _112528 -> Prop) (h1 : @INTERSECTION_OF _112528 (@FINITE (_112528 -> Prop)) P t) : @INTERSECTION_OF _112528 (@FINITE (_112528 -> Prop)) P t.
Proof. exact (h1). Qed.
Lemma lem4887460 {_112528 : Type'} (P : type686 _112528) (s : _112528 -> Prop) (h1 : @INTERSECTION_OF _112528 (@FINITE (_112528 -> Prop)) P s) : @INTERSECTION_OF _112528 (@FINITE (_112528 -> Prop)) P s.
Proof. exact (h1). Qed.
Lemma lem4887462 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) : (@INTER _87260 s t) = (term12 _87260 s t).
Proof. exact (EQ_MP (@lem4887456 _87260 s t) (@lem3356566 _87260 s t)). Qed.
Lemma lem4887463 {_112528 : Type'} (s : _112528 -> Prop) (t : _112528 -> Prop) : (@INTER _112528 s t) = (term12 _112528 s t).
Proof. exact (@lem4887462 _112528 s t). Qed.
Lemma lem4887464 {_112528 : Type'} (P : type686 _112528) : (@INTERSECTION_OF _112528 (@FINITE (_112528 -> Prop)) P) = (@INTERSECTION_OF _112528 (@FINITE (_112528 -> Prop)) P).
Proof. exact (eq_refl (@INTERSECTION_OF _112528 (@FINITE (_112528 -> Prop)) P)). Qed.
Lemma lem4887465 {_112528 : Type'} (P : type686 _112528) (s : _112528 -> Prop) (t : _112528 -> Prop) : (term14 _112528 P s t) = (term15 _112528 P s t).
Proof. exact (MK_COMB (@lem4887464 _112528 P) (@lem4887463 _112528 s t)). Qed.
Lemma lem4887466 {_112528 : Type'} (P : type686 _112528) (s : _112528 -> Prop) (t : _112528 -> Prop) : (term15 _112528 P s t) = (term14 _112528 P s t).
Proof. exact (SYM (@lem4887465 _112528 P s t)). Qed.
Lemma lem4887468 {A : Type'} (P : type686 A) (u : type686 A) : term7 A P u.
Proof. exact (EQ_MP (@lem4887450 A P u) (@lem4887449 A P u)). Qed.
Lemma lem4887469 {_112528 : Type'} (P : type686 _112528) (u : type686 _112528) : term7 _112528 P u.
Proof. exact (@lem4887468 _112528 P u). Qed.
Lemma lem4887470 {_112528 : Type'} (P : type686 _112528) (s : _112528 -> Prop) (t : _112528 -> Prop) : term16 _112528 P s t.
Proof. exact (@lem4887469 _112528 P (term17 _112528 s t)). Qed.
Lemma lem4887471 {_83983 : Type'} (P : _83983 -> Prop) : term18 _83983 P.
Proof. exact (@lem3207453 _83983 P). Qed.
Lemma lem4887472 {_83983 : Type'} (P : _83983 -> Prop) : (term18 _83983 P) = (term19 _83983 P).
Proof. exact (eq_refl (term18 _83983 P)). Qed.
Lemma lem4887473 {_83983 : Type'} (P : _83983 -> Prop) : term19 _83983 P.
Proof. exact (EQ_MP (@lem4887472 _83983 P) (@lem4887471 _83983 P)). Qed.
Lemma lem4887474 {_83983 : Type'} (P : _83983 -> Prop) (a : _83983) : term20 _83983 P a.
Proof. exact (@lem4887473 _83983 P a). Qed.
Lemma lem4887475 {_83983 : Type'} (a : _83983) (P : _83983 -> Prop) : (term20 _83983 P a) = (term21 _83983 a P).
Proof. exact (eq_refl (term20 _83983 P a)). Qed.
Lemma lem4887476 {_83983 : Type'} (a : _83983) (P : _83983 -> Prop) : term21 _83983 a P.
Proof. exact (EQ_MP (@lem4887475 _83983 a P) (@lem4887474 _83983 P a)). Qed.
Lemma lem4887477 {_83983 : Type'} (a : _83983) (P : _83983 -> Prop) (s : _83983 -> Prop) : term22 _83983 a P s.
Proof. exact (@lem4887476 _83983 a P s). Qed.
Lemma lem4887478 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term22 _83983 a P s) = ((term23 _83983 a s P) = (term24 _83983 a s P)).
Proof. exact (eq_refl (term22 _83983 a P s)). Qed.
Lemma lem4887480 {A : Type'} (s : A -> Prop) : term25 A s.
Proof. exact (@lem3608316 A s). Qed.
Lemma lem4887481 {A : Type'} (s : A -> Prop) : (term25 A s) = (term26 A s).
Proof. exact (eq_refl (term25 A s)). Qed.
Lemma lem4887482 {A : Type'} (s : A -> Prop) : term26 A s.
Proof. exact (EQ_MP (@lem4887481 A s) (@lem4887480 A s)). Qed.
Lemma lem4887483 {A : Type'} (s : A -> Prop) (x : A) : term27 A s x.
Proof. exact (@lem4887482 A s x). Qed.
Lemma lem4887484 {A : Type'} (x : A) (s : A -> Prop) : (term27 A s x) = ((term28 A x s) = (@FINITE A s)).
Proof. exact (eq_refl (term27 A s x)). Qed.
Lemma lem4887486 {_112528 : Type'} (P : type686 _112528) (s : _112528 -> Prop) : (@INTERSECTION_OF _112528 (@FINITE (_112528 -> Prop)) P s) = ((@INTERSECTION_OF _112528 (@FINITE (_112528 -> Prop)) P s) = True).
Proof. exact (@lem7 (@INTERSECTION_OF _112528 (@FINITE (_112528 -> Prop)) P s)). Qed.
Lemma lem4887488 {_112528 : Type'} (P : type686 _112528) (t : _112528 -> Prop) : (@INTERSECTION_OF _112528 (@FINITE (_112528 -> Prop)) P t) = ((@INTERSECTION_OF _112528 (@FINITE (_112528 -> Prop)) P t) = True).
Proof. exact (@lem7 (@INTERSECTION_OF _112528 (@FINITE (_112528 -> Prop)) P t)). Qed.
Lemma lem4887493 {A : Type'} (x : A) (s : A -> Prop) : (term28 A x s) = (@FINITE A s).
Proof. exact (EQ_MP (@lem4887484 A x s) (@lem4887483 A s x)). Qed.
Lemma lem4887494 {_112528 : Type'} (x : _112528 -> Prop) (s : type686 _112528) : (term29 _112528 x s) = (@FINITE (_112528 -> Prop) s).
Proof. exact (@lem4887493 (_112528 -> Prop) x s). Qed.
Lemma lem4887495 {_112528 : Type'} (s : _112528 -> Prop) (t : _112528 -> Prop) : (term30 _112528 s t) = (term31 _112528 t).
Proof. exact (@lem4887494 _112528 s (@INSERT (_112528 -> Prop) t (@EMPTY (_112528 -> Prop)))). Qed.
Lemma lem4887497 {A : Type'} (x : A) (s : A -> Prop) : (term28 A x s) = (@FINITE A s).
Proof. exact (EQ_MP (@lem4887484 A x s) (@lem4887483 A s x)). Qed.
Lemma lem4887498 {_112528 : Type'} (x : _112528 -> Prop) (s : type686 _112528) : (term29 _112528 x s) = (@FINITE (_112528 -> Prop) s).
Proof. exact (@lem4887497 (_112528 -> Prop) x s). Qed.
Lemma lem4887499 {_112528 : Type'} (t : _112528 -> Prop) : (term31 _112528 t) = (@FINITE (_112528 -> Prop) (@EMPTY (_112528 -> Prop))).
Proof. exact (@lem4887498 _112528 t (@EMPTY (_112528 -> Prop))). Qed.
Lemma lem4887500 {_112528 : Type'} (s : _112528 -> Prop) (t : _112528 -> Prop) : (term30 _112528 s t) = (@FINITE (_112528 -> Prop) (@EMPTY (_112528 -> Prop))).
Proof. exact (TRANS (@lem4887495 _112528 s t) (@lem4887499 _112528 t)). Qed.
Lemma lem4887501 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4887502 {_112528 : Type'} (s : _112528 -> Prop) (t : _112528 -> Prop) : (term32 _112528 s t) = (term33 _112528).
Proof. exact (MK_COMB (@lem4887501) (@lem4887500 _112528 s t)). Qed.
Lemma lem4887504 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term23 _83983 a s P) = (term24 _83983 a s P).
Proof. exact (EQ_MP (@lem4887478 _83983 a s P) (@lem4887477 _83983 a P s)). Qed.
Lemma lem4887505 {_112528 : Type'} (a : _112528 -> Prop) (s : type686 _112528) (P : type686 _112528) : (term34 _112528 a s P) = (term35 _112528 a s P).
Proof. exact (@lem4887504 (_112528 -> Prop) a s P). Qed.
Lemma lem4887506 {_112528 : Type'} (s : _112528 -> Prop) (t : _112528 -> Prop) (P : type686 _112528) : (term36 _112528 s t P) = (term37 _112528 s t P).
Proof. exact (@lem4887505 _112528 s (@INSERT (_112528 -> Prop) t (@EMPTY (_112528 -> Prop))) (term38 _112528 P)). Qed.
Lemma lem4887507 {_112528 : Type'} (P : type686 _112528) (s' : _112528 -> Prop) : (term39 _112528 P s') = (@INTERSECTION_OF _112528 (@FINITE (_112528 -> Prop)) P s').
Proof. exact (eq_refl (term39 _112528 P s')). Qed.
Lemma lem4887508 {_112528 : Type'} (s' : _112528 -> Prop) (s : _112528 -> Prop) (t : _112528 -> Prop) : (term40 _112528 s' s t) = (term40 _112528 s' s t).
Proof. exact (eq_refl (term40 _112528 s' s t)). Qed.
Lemma lem4887509 {_112528 : Type'} (s : _112528 -> Prop) (t : _112528 -> Prop) (P : type686 _112528) (s' : _112528 -> Prop) : (term41 _112528 s t P s') = (term42 _112528 s t P s').
Proof. exact (MK_COMB (@lem4887508 _112528 s' s t) (@lem4887507 _112528 P s')). Qed.
Lemma lem4887510 {_112528 : Type'} (s : _112528 -> Prop) (t : _112528 -> Prop) (P : type686 _112528) : (term43 _112528 s t P) = (term44 _112528 s t P).
Proof. exact (fun_ext (fun s' : _112528 -> Prop => @lem4887509 _112528 s t P s')). Qed.
Lemma lem4887511 {_112528 : Type'} : (@all (_112528 -> Prop)) = (@all (_112528 -> Prop)).
Proof. exact (eq_refl (@all (_112528 -> Prop))). Qed.
Lemma lem4887512 {_112528 : Type'} (s : _112528 -> Prop) (t : _112528 -> Prop) (P : type686 _112528) : (term36 _112528 s t P) = (term45 _112528 s t P).
Proof. exact (MK_COMB (@lem4887511 _112528) (@lem4887510 _112528 s t P)). Qed.
Lemma lem4887513 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4887514 {_112528 : Type'} (s : _112528 -> Prop) (t : _112528 -> Prop) (P : type686 _112528) : (term46 _112528 s t P) = (term47 _112528 s t P).
Proof. exact (MK_COMB (@lem4887513) (@lem4887512 _112528 s t P)). Qed.
Lemma lem4887515 {_112528 : Type'} (P : type686 _112528) (s : _112528 -> Prop) : (term39 _112528 P s) = (@INTERSECTION_OF _112528 (@FINITE (_112528 -> Prop)) P s).
Proof. exact (eq_refl (term39 _112528 P s)). Qed.
Lemma lem4887516 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4887517 {_112528 : Type'} (P : type686 _112528) (s : _112528 -> Prop) : (term48 _112528 P s) = (term49 _112528 P s).
Proof. exact (MK_COMB (@lem4887516) (@lem4887515 _112528 P s)). Qed.
Lemma lem4887518 {_112528 : Type'} (P : type686 _112528) (s' : _112528 -> Prop) : (term39 _112528 P s') = (@INTERSECTION_OF _112528 (@FINITE (_112528 -> Prop)) P s').
Proof. exact (eq_refl (term39 _112528 P s')). Qed.
Lemma lem4887519 {_112528 : Type'} (s' : _112528 -> Prop) (t : _112528 -> Prop) : (term50 _112528 s' t) = (term50 _112528 s' t).
Proof. exact (eq_refl (term50 _112528 s' t)). Qed.
Lemma lem4887520 {_112528 : Type'} (t : _112528 -> Prop) (P : type686 _112528) (s' : _112528 -> Prop) : (term51 _112528 t P s') = (term52 _112528 t P s').
Proof. exact (MK_COMB (@lem4887519 _112528 s' t) (@lem4887518 _112528 P s')). Qed.
Lemma lem4887521 {_112528 : Type'} (t : _112528 -> Prop) (P : type686 _112528) : (term53 _112528 t P) = (term54 _112528 t P).
Proof. exact (fun_ext (fun s' : _112528 -> Prop => @lem4887520 _112528 t P s')). Qed.
Lemma lem4887522 {_112528 : Type'} : (@all (_112528 -> Prop)) = (@all (_112528 -> Prop)).
Proof. exact (eq_refl (@all (_112528 -> Prop))). Qed.
Lemma lem4887523 {_112528 : Type'} (t : _112528 -> Prop) (P : type686 _112528) : (term55 _112528 t P) = (term56 _112528 t P).
Proof. exact (MK_COMB (@lem4887522 _112528) (@lem4887521 _112528 t P)). Qed.
Lemma lem4887524 {_112528 : Type'} (s : _112528 -> Prop) (t : _112528 -> Prop) (P : type686 _112528) : (term37 _112528 s t P) = (term57 _112528 s t P).
Proof. exact (MK_COMB (@lem4887517 _112528 P s) (@lem4887523 _112528 t P)). Qed.
Lemma lem4887525 {_112528 : Type'} (s : _112528 -> Prop) (t : _112528 -> Prop) (P : type686 _112528) : ((term36 _112528 s t P) = (term37 _112528 s t P)) = ((term45 _112528 s t P) = (term57 _112528 s t P)).
Proof. exact (MK_COMB (@lem4887514 _112528 s t P) (@lem4887524 _112528 s t P)). Qed.
Lemma lem4887526 {_112528 : Type'} (s : _112528 -> Prop) (t : _112528 -> Prop) (P : type686 _112528) : (term45 _112528 s t P) = (term57 _112528 s t P).
Proof. exact (EQ_MP (@lem4887525 _112528 s t P) (@lem4887506 _112528 s t P)). Qed.
Lemma lem4887530 {_112528 : Type'} (P : type686 _112528) (s : _112528 -> Prop) (h1 : @INTERSECTION_OF _112528 (@FINITE (_112528 -> Prop)) P s) : (@INTERSECTION_OF _112528 (@FINITE (_112528 -> Prop)) P s) = True.
Proof. exact (EQ_MP (@lem4887486 _112528 P s) (@lem4887460 _112528 P s h1)). Qed.
Lemma lem4887531 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4887532 {_112528 : Type'} (P : type686 _112528) (s : _112528 -> Prop) (h1 : @INTERSECTION_OF _112528 (@FINITE (_112528 -> Prop)) P s) : (term49 _112528 P s) = (and True).
Proof. exact (MK_COMB (@lem4887531) (@lem4887530 _112528 P s h1)). Qed.
Lemma lem4887534 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term23 _83983 a s P) = (term24 _83983 a s P).
Proof. exact (EQ_MP (@lem4887478 _83983 a s P) (@lem4887477 _83983 a P s)). Qed.
Lemma lem4887535 {_112528 : Type'} (a : _112528 -> Prop) (s : type686 _112528) (P : type686 _112528) : (term34 _112528 a s P) = (term35 _112528 a s P).
Proof. exact (@lem4887534 (_112528 -> Prop) a s P). Qed.
Lemma lem4887536 {_112528 : Type'} (t : _112528 -> Prop) (P : type686 _112528) : (term55 _112528 t P) = (term58 _112528 t P).
Proof. exact (@lem4887535 _112528 t (@EMPTY (_112528 -> Prop)) (term38 _112528 P)). Qed.
Lemma lem4887537 {_112528 : Type'} (P : type686 _112528) (s' : _112528 -> Prop) : (term39 _112528 P s') = (@INTERSECTION_OF _112528 (@FINITE (_112528 -> Prop)) P s').
Proof. exact (eq_refl (term39 _112528 P s')). Qed.
Lemma lem4887538 {_112528 : Type'} (s' : _112528 -> Prop) (t : _112528 -> Prop) : (term50 _112528 s' t) = (term50 _112528 s' t).
Proof. exact (eq_refl (term50 _112528 s' t)). Qed.
Lemma lem4887539 {_112528 : Type'} (t : _112528 -> Prop) (P : type686 _112528) (s' : _112528 -> Prop) : (term51 _112528 t P s') = (term52 _112528 t P s').
Proof. exact (MK_COMB (@lem4887538 _112528 s' t) (@lem4887537 _112528 P s')). Qed.
Lemma lem4887540 {_112528 : Type'} (t : _112528 -> Prop) (P : type686 _112528) : (term53 _112528 t P) = (term54 _112528 t P).
Proof. exact (fun_ext (fun s' : _112528 -> Prop => @lem4887539 _112528 t P s')). Qed.
Lemma lem4887541 {_112528 : Type'} : (@all (_112528 -> Prop)) = (@all (_112528 -> Prop)).
Proof. exact (eq_refl (@all (_112528 -> Prop))). Qed.
Lemma lem4887542 {_112528 : Type'} (t : _112528 -> Prop) (P : type686 _112528) : (term55 _112528 t P) = (term56 _112528 t P).
Proof. exact (MK_COMB (@lem4887541 _112528) (@lem4887540 _112528 t P)). Qed.
Lemma lem4887543 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4887544 {_112528 : Type'} (t : _112528 -> Prop) (P : type686 _112528) : (term59 _112528 t P) = (term60 _112528 t P).
Proof. exact (MK_COMB (@lem4887543) (@lem4887542 _112528 t P)). Qed.
Lemma lem4887545 {_112528 : Type'} (P : type686 _112528) (t : _112528 -> Prop) : (term39 _112528 P t) = (@INTERSECTION_OF _112528 (@FINITE (_112528 -> Prop)) P t).
Proof. exact (eq_refl (term39 _112528 P t)). Qed.
Lemma lem4887546 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4887547 {_112528 : Type'} (P : type686 _112528) (t : _112528 -> Prop) : (term48 _112528 P t) = (term49 _112528 P t).
Proof. exact (MK_COMB (@lem4887546) (@lem4887545 _112528 P t)). Qed.
Lemma lem4887548 {_112528 : Type'} (P : type686 _112528) (s' : _112528 -> Prop) : (term39 _112528 P s') = (@INTERSECTION_OF _112528 (@FINITE (_112528 -> Prop)) P s').
Proof. exact (eq_refl (term39 _112528 P s')). Qed.
Lemma lem4887549 {_112528 : Type'} (s' : _112528 -> Prop) : (term61 _112528 s') = (term61 _112528 s').
Proof. exact (eq_refl (term61 _112528 s')). Qed.
Lemma lem4887550 {_112528 : Type'} (P : type686 _112528) (s' : _112528 -> Prop) : (term62 _112528 P s') = (term63 _112528 P s').
Proof. exact (MK_COMB (@lem4887549 _112528 s') (@lem4887548 _112528 P s')). Qed.
Lemma lem4887551 {_112528 : Type'} (P : type686 _112528) : (term64 _112528 P) = (term65 _112528 P).
Proof. exact (fun_ext (fun s' : _112528 -> Prop => @lem4887550 _112528 P s')). Qed.
Lemma lem4887552 {_112528 : Type'} : (@all (_112528 -> Prop)) = (@all (_112528 -> Prop)).
Proof. exact (eq_refl (@all (_112528 -> Prop))). Qed.
Lemma lem4887553 {_112528 : Type'} (P : type686 _112528) : (term66 _112528 P) = (term67 _112528 P).
Proof. exact (MK_COMB (@lem4887552 _112528) (@lem4887551 _112528 P)). Qed.
Lemma lem4887554 {_112528 : Type'} (t : _112528 -> Prop) (P : type686 _112528) : (term58 _112528 t P) = (term68 _112528 t P).
Proof. exact (MK_COMB (@lem4887547 _112528 P t) (@lem4887553 _112528 P)). Qed.
Lemma lem4887555 {_112528 : Type'} (t : _112528 -> Prop) (P : type686 _112528) : ((term55 _112528 t P) = (term58 _112528 t P)) = ((term56 _112528 t P) = (term68 _112528 t P)).
Proof. exact (MK_COMB (@lem4887544 _112528 t P) (@lem4887554 _112528 t P)). Qed.
Lemma lem4887556 {_112528 : Type'} (t : _112528 -> Prop) (P : type686 _112528) : (term56 _112528 t P) = (term68 _112528 t P).
Proof. exact (EQ_MP (@lem4887555 _112528 t P) (@lem4887536 _112528 t P)). Qed.
Lemma lem4887560 {_112528 : Type'} (P : type686 _112528) (t : _112528 -> Prop) (h1 : @INTERSECTION_OF _112528 (@FINITE (_112528 -> Prop)) P t) : (@INTERSECTION_OF _112528 (@FINITE (_112528 -> Prop)) P t) = True.
Proof. exact (EQ_MP (@lem4887488 _112528 P t) (@lem4887459 _112528 P t h1)). Qed.
Lemma lem4887561 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4887562 {_112528 : Type'} (P : type686 _112528) (t : _112528 -> Prop) (h1 : @INTERSECTION_OF _112528 (@FINITE (_112528 -> Prop)) P t) : (term49 _112528 P t) = (and True).
Proof. exact (MK_COMB (@lem4887561) (@lem4887560 _112528 P t h1)). Qed.
Lemma lem4887569 {_112528 : Type'} (P : type686 _112528) : (term67 _112528 P) = (term67 _112528 P).
Proof. exact (eq_refl (term67 _112528 P)). Qed.
Lemma lem4887570 {_112528 : Type'} (P : type686 _112528) (t : _112528 -> Prop) (h1 : @INTERSECTION_OF _112528 (@FINITE (_112528 -> Prop)) P t) : (term68 _112528 t P) = (term69 _112528 P).
Proof. exact (MK_COMB (@lem4887562 _112528 P t h1) (@lem4887569 _112528 P)). Qed.
Lemma lem4887572 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4887573 {_112528 : Type'} (P : type686 _112528) : (term69 _112528 P) = (term67 _112528 P).
Proof. exact (@lem4887572 (term67 _112528 P)). Qed.
Lemma lem4887580 {_112528 : Type'} (P : type686 _112528) (t : _112528 -> Prop) (h1 : @INTERSECTION_OF _112528 (@FINITE (_112528 -> Prop)) P t) : (term68 _112528 t P) = (term67 _112528 P).
Proof. exact (TRANS (@lem4887570 _112528 P t h1) (@lem4887573 _112528 P)). Qed.
Lemma lem4887581 {_112528 : Type'} (P : type686 _112528) (t : _112528 -> Prop) (h1 : @INTERSECTION_OF _112528 (@FINITE (_112528 -> Prop)) P t) : (term56 _112528 t P) = (term67 _112528 P).
Proof. exact (TRANS (@lem4887556 _112528 t P) (@lem4887580 _112528 P t h1)). Qed.
Lemma lem4887582 {_112528 : Type'} (s : _112528 -> Prop) (P : type686 _112528) (t : _112528 -> Prop) (h1 : @INTERSECTION_OF _112528 (@FINITE (_112528 -> Prop)) P s) (h2 : @INTERSECTION_OF _112528 (@FINITE (_112528 -> Prop)) P t) : (term57 _112528 s t P) = (term69 _112528 P).
Proof. exact (MK_COMB (@lem4887532 _112528 P s h1) (@lem4887581 _112528 P t h2)). Qed.
Lemma lem4887584 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4887585 {_112528 : Type'} (P : type686 _112528) : (term69 _112528 P) = (term67 _112528 P).
Proof. exact (@lem4887584 (term67 _112528 P)). Qed.
Lemma lem4887592 {_112528 : Type'} (s : _112528 -> Prop) (P : type686 _112528) (t : _112528 -> Prop) (h1 : @INTERSECTION_OF _112528 (@FINITE (_112528 -> Prop)) P s) (h2 : @INTERSECTION_OF _112528 (@FINITE (_112528 -> Prop)) P t) : (term57 _112528 s t P) = (term67 _112528 P).
Proof. exact (TRANS (@lem4887582 _112528 s P t h1 h2) (@lem4887585 _112528 P)). Qed.
Lemma lem4887593 {_112528 : Type'} (s : _112528 -> Prop) (P : type686 _112528) (t : _112528 -> Prop) (h1 : @INTERSECTION_OF _112528 (@FINITE (_112528 -> Prop)) P s) (h2 : @INTERSECTION_OF _112528 (@FINITE (_112528 -> Prop)) P t) : (term45 _112528 s t P) = (term67 _112528 P).
Proof. exact (TRANS (@lem4887526 _112528 s t P) (@lem4887592 _112528 s P t h1 h2)). Qed.
Lemma lem4887594 {_112528 : Type'} (s : _112528 -> Prop) (P : type686 _112528) (t : _112528 -> Prop) (h1 : @INTERSECTION_OF _112528 (@FINITE (_112528 -> Prop)) P s) (h2 : @INTERSECTION_OF _112528 (@FINITE (_112528 -> Prop)) P t) : (term70 _112528 s t P) = (term71 _112528 P).
Proof. exact (MK_COMB (@lem4887502 _112528 s t) (@lem4887593 _112528 s P t h1 h2)). Qed.
Lemma lem4887597 {_112528 : Type'} (s : _112528 -> Prop) (P : type686 _112528) (t : _112528 -> Prop) (h1 : @INTERSECTION_OF _112528 (@FINITE (_112528 -> Prop)) P s) (h2 : @INTERSECTION_OF _112528 (@FINITE (_112528 -> Prop)) P t) : (term71 _112528 P) = (term70 _112528 s t P).
Proof. exact (SYM (@lem4887594 _112528 s P t h1 h2)). Qed.
Lemma lem4887601 {_92140 : Type'} : (@FINITE _92140 (@EMPTY _92140)) = True.
Proof. exact (EQ_MP (@lem4887427 _92140) (@lem3596285 _92140)). Qed.
Lemma lem4887602 {_112528 : Type'} : (@FINITE (_112528 -> Prop) (@EMPTY (_112528 -> Prop))) = True.
Proof. exact (@lem4887601 (_112528 -> Prop)). Qed.
Lemma lem4887603 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4887604 {_112528 : Type'} : (term33 _112528) = (and True).
Proof. exact (MK_COMB (@lem4887603) (@lem4887602 _112528)). Qed.
Lemma lem4887612 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4887425 A x (@lem4887424 A x)). Qed.
Lemma lem4887613 {_112528 : Type'} (x : _112528 -> Prop) : (@IN (_112528 -> Prop) x (@EMPTY (_112528 -> Prop))) = False.
Proof. exact (@lem4887612 (_112528 -> Prop) x). Qed.
Lemma lem4887614 {_112528 : Type'} (s' : _112528 -> Prop) : (@IN (_112528 -> Prop) s' (@EMPTY (_112528 -> Prop))) = False.
Proof. exact (@lem4887613 _112528 s'). Qed.
Lemma lem4887615 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4887616 {_112528 : Type'} (s' : _112528 -> Prop) : (term61 _112528 s') = (imp False).
Proof. exact (MK_COMB (@lem4887615) (@lem4887614 _112528 s')). Qed.
Lemma lem4887617 {_112528 : Type'} (P : type686 _112528) (s' : _112528 -> Prop) : (@INTERSECTION_OF _112528 (@FINITE (_112528 -> Prop)) P s') = (@INTERSECTION_OF _112528 (@FINITE (_112528 -> Prop)) P s').
Proof. exact (eq_refl (@INTERSECTION_OF _112528 (@FINITE (_112528 -> Prop)) P s')). Qed.
Lemma lem4887618 {_112528 : Type'} (P : type686 _112528) (s' : _112528 -> Prop) : (term63 _112528 P s') = (term72 _112528 P s').
Proof. exact (MK_COMB (@lem4887616 _112528 s') (@lem4887617 _112528 P s')). Qed.
Lemma lem4887620 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem4887621 {_112528 : Type'} (P : type686 _112528) (s' : _112528 -> Prop) : (term72 _112528 P s') = True.
Proof. exact (@lem4887620 (@INTERSECTION_OF _112528 (@FINITE (_112528 -> Prop)) P s')). Qed.
Lemma lem4887622 {_112528 : Type'} (P : type686 _112528) (s' : _112528 -> Prop) : (term63 _112528 P s') = True.
Proof. exact (TRANS (@lem4887618 _112528 P s') (@lem4887621 _112528 P s')). Qed.
Lemma lem4887623 {_112528 : Type'} (P : type686 _112528) : (term65 _112528 P) = (term73 _112528).
Proof. exact (fun_ext (fun s' : _112528 -> Prop => @lem4887622 _112528 P s')). Qed.
Lemma lem4887624 {_112528 : Type'} : (@all (_112528 -> Prop)) = (@all (_112528 -> Prop)).
Proof. exact (eq_refl (@all (_112528 -> Prop))). Qed.
Lemma lem4887625 {_112528 : Type'} (P : type686 _112528) : (term67 _112528 P) = (term74 _112528).
Proof. exact (MK_COMB (@lem4887624 _112528) (@lem4887623 _112528 P)). Qed.
Lemma lem4887627 {A : Type'} (t : Prop) : (term75 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4887628 {_112528 : Type'} (t : Prop) : (term76 _112528 t) = t.
Proof. exact (@lem4887627 (_112528 -> Prop) t). Qed.
Lemma lem4887629 {_112528 : Type'} : (term74 _112528) = True.
Proof. exact (@lem4887628 _112528 True). Qed.
Lemma lem4887630 {_112528 : Type'} (P : type686 _112528) : (term67 _112528 P) = True.
Proof. exact (TRANS (@lem4887625 _112528 P) (@lem4887629 _112528)). Qed.
Lemma lem4887631 {_112528 : Type'} (P : type686 _112528) : (term71 _112528 P) = (True /\ True).
Proof. exact (MK_COMB (@lem4887604 _112528) (@lem4887630 _112528 P)). Qed.
Lemma lem4887633 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4887634 : (True /\ True) = True.
Proof. exact (@lem4887633 True). Qed.
Lemma lem4887635 {_112528 : Type'} (P : type686 _112528) : (term71 _112528 P) = True.
Proof. exact (TRANS (@lem4887631 _112528 P) (@lem4887634)). Qed.
Lemma lem4887636 {_112528 : Type'} (P : type686 _112528) : True = (term71 _112528 P).
Proof. exact (SYM (@lem4887635 _112528 P)). Qed.
Lemma lem4887637 {_112528 : Type'} (P : type686 _112528) : term71 _112528 P.
Proof. exact (EQ_MP (@lem4887636 _112528 P) (@lem0)). Qed.
Lemma lem4887638 {_112528 : Type'} (s : _112528 -> Prop) (P : type686 _112528) (t : _112528 -> Prop) (h1 : @INTERSECTION_OF _112528 (@FINITE (_112528 -> Prop)) P s) (h2 : @INTERSECTION_OF _112528 (@FINITE (_112528 -> Prop)) P t) : term70 _112528 s t P.
Proof. exact (EQ_MP (@lem4887597 _112528 s P t h1 h2) (@lem4887637 _112528 P)). Qed.
Lemma lem4887639 {_112528 : Type'} (s : _112528 -> Prop) (P : type686 _112528) (t : _112528 -> Prop) (h1 : @INTERSECTION_OF _112528 (@FINITE (_112528 -> Prop)) P s) (h2 : @INTERSECTION_OF _112528 (@FINITE (_112528 -> Prop)) P t) : term15 _112528 P s t.
Proof. exact (@lem4887470 _112528 P s t (@lem4887638 _112528 s P t h1 h2)). Qed.
Lemma lem4887640 {_112528 : Type'} (s : _112528 -> Prop) (P : type686 _112528) (t : _112528 -> Prop) (h1 : @INTERSECTION_OF _112528 (@FINITE (_112528 -> Prop)) P s) (h2 : @INTERSECTION_OF _112528 (@FINITE (_112528 -> Prop)) P t) : term14 _112528 P s t.
Proof. exact (EQ_MP (@lem4887466 _112528 P s t) (@lem4887639 _112528 s P t h1 h2)). Qed.
Lemma lem4887641 {_112528 : Type'} (s : _112528 -> Prop) (P : type686 _112528) (t : _112528 -> Prop) (h1 : term13 _112528 s P t) : @INTERSECTION_OF _112528 (@FINITE (_112528 -> Prop)) P t.
Proof. exact (proj2 (@lem4887458 _112528 s P t h1)). Qed.
Lemma lem4887642 {_112528 : Type'} (s : _112528 -> Prop) (P : type686 _112528) (t : _112528 -> Prop) (h1 : term13 _112528 s P t) : @INTERSECTION_OF _112528 (@FINITE (_112528 -> Prop)) P s.
Proof. exact (proj1 (@lem4887458 _112528 s P t h1)). Qed.
Lemma lem4887643 {_112528 : Type'} (s : _112528 -> Prop) (P : type686 _112528) (t : _112528 -> Prop) (h1 : @INTERSECTION_OF _112528 (@FINITE (_112528 -> Prop)) P s) (h2 : @INTERSECTION_OF _112528 (@FINITE (_112528 -> Prop)) P t) : (@INTERSECTION_OF _112528 (@FINITE (_112528 -> Prop)) P t) = (term14 _112528 P s t).
Proof. exact (prop_ext (fun h3 : @INTERSECTION_OF _112528 (@FINITE (_112528 -> Prop)) P t => @lem4887640 _112528 s P t h1 h2) (fun h3 : term14 _112528 P s t => @lem4887459 _112528 P t h2)). Qed.
Lemma lem4887644 {_112528 : Type'} (s : _112528 -> Prop) (P : type686 _112528) (t : _112528 -> Prop) (h1 : @INTERSECTION_OF _112528 (@FINITE (_112528 -> Prop)) P s) (h2 : @INTERSECTION_OF _112528 (@FINITE (_112528 -> Prop)) P t) : term14 _112528 P s t.
Proof. exact (EQ_MP (@lem4887643 _112528 s P t h1 h2) (@lem4887459 _112528 P t h2)). Qed.
Lemma lem4887645 {_112528 : Type'} (s : _112528 -> Prop) (P : type686 _112528) (t : _112528 -> Prop) (h1 : @INTERSECTION_OF _112528 (@FINITE (_112528 -> Prop)) P s) (h2 : @INTERSECTION_OF _112528 (@FINITE (_112528 -> Prop)) P t) : (@INTERSECTION_OF _112528 (@FINITE (_112528 -> Prop)) P s) = (term14 _112528 P s t).
Proof. exact (prop_ext (fun h3 : @INTERSECTION_OF _112528 (@FINITE (_112528 -> Prop)) P s => @lem4887644 _112528 s P t h1 h2) (fun h3 : term14 _112528 P s t => @lem4887460 _112528 P s h1)). Qed.
Lemma lem4887646 {_112528 : Type'} (s : _112528 -> Prop) (P : type686 _112528) (t : _112528 -> Prop) (h1 : @INTERSECTION_OF _112528 (@FINITE (_112528 -> Prop)) P s) (h2 : @INTERSECTION_OF _112528 (@FINITE (_112528 -> Prop)) P t) : term14 _112528 P s t.
Proof. exact (EQ_MP (@lem4887645 _112528 s P t h1 h2) (@lem4887460 _112528 P s h1)). Qed.
Lemma lem4887647 {_112528 : Type'} (t : _112528 -> Prop) (P : type686 _112528) (s : _112528 -> Prop) (h1 : term13 _112528 s P t) (h2 : @INTERSECTION_OF _112528 (@FINITE (_112528 -> Prop)) P s) : (@INTERSECTION_OF _112528 (@FINITE (_112528 -> Prop)) P t) = (term14 _112528 P s t).
Proof. exact (prop_ext (fun h3 : @INTERSECTION_OF _112528 (@FINITE (_112528 -> Prop)) P t => @lem4887646 _112528 s P t h2 h3) (fun h3 : term14 _112528 P s t => @lem4887641 _112528 s P t h1)). Qed.
Lemma lem4887648 {_112528 : Type'} (t : _112528 -> Prop) (P : type686 _112528) (s : _112528 -> Prop) (h1 : term13 _112528 s P t) (h2 : @INTERSECTION_OF _112528 (@FINITE (_112528 -> Prop)) P s) : term14 _112528 P s t.
Proof. exact (EQ_MP (@lem4887647 _112528 t P s h1 h2) (@lem4887641 _112528 s P t h1)). Qed.
Lemma lem4887649 {_112528 : Type'} (s : _112528 -> Prop) (P : type686 _112528) (t : _112528 -> Prop) (h1 : term13 _112528 s P t) : (@INTERSECTION_OF _112528 (@FINITE (_112528 -> Prop)) P s) = (term14 _112528 P s t).
Proof. exact (prop_ext (fun h2 : @INTERSECTION_OF _112528 (@FINITE (_112528 -> Prop)) P s => @lem4887648 _112528 t P s h1 h2) (fun h2 : term14 _112528 P s t => @lem4887642 _112528 s P t h1)). Qed.
Lemma lem4887650 {_112528 : Type'} (s : _112528 -> Prop) (P : type686 _112528) (t : _112528 -> Prop) (h1 : term13 _112528 s P t) : term14 _112528 P s t.
Proof. exact (EQ_MP (@lem4887649 _112528 s P t h1) (@lem4887642 _112528 s P t h1)). Qed.
Lemma lem4887651 {_112528 : Type'} (P : type686 _112528) (s : _112528 -> Prop) (t : _112528 -> Prop) : term77 _112528 P s t.
Proof. exact (fun h0 : term13 _112528 s P t => @lem4887650 _112528 s P t h0). Qed.
Lemma lem4887656 {_112528 : Type'} (P : type686 _112528) (s : _112528 -> Prop) : term78 _112528 P s.
Proof. exact (fun t : _112528 -> Prop => @lem4887651 _112528 P s t). Qed.
Lemma lem4887661 {_112528 : Type'} (P : type686 _112528) : term79 _112528 P.
Proof. exact (fun s : _112528 -> Prop => @lem4887656 _112528 P s). Qed.
Lemma lem4887666 {_112528 : Type'} : term80 _112528.
Proof. exact (fun P : type686 _112528 => @lem4887661 _112528 P). Qed.
