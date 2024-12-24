Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CARTESIAN_PRODUCT_UNIV_term_abbrevs.
Require Import EXTENSION_spec.
Require Import EXTENSIONAL_UNIV_spec.
Require Import IN_UNIV_spec.
Require Import cartesian_product_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1820_spec.
Require Import thm1843_spec.
Require Import thm1856_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Require Import thm7_spec.
Lemma lem4432367 {_105178 A : Type'} (f : A -> _105178) : term0 _105178 A f.
Proof. exact (@lem4383466 _105178 A f). Qed.
Lemma lem4432368 {_105178 A : Type'} (f : A -> _105178) : (term0 _105178 A f) = (@EXTENSIONAL A _105178 (@UNIV A) f).
Proof. exact (eq_refl (term0 _105178 A f)). Qed.
Lemma lem4432369 {_105178 A : Type'} (f : A -> _105178) : @EXTENSIONAL A _105178 (@UNIV A) f.
Proof. exact (EQ_MP (@lem4432368 _105178 A f) (@lem4432367 _105178 A f)). Qed.
Lemma lem4432370 {_105178 A : Type'} (f : A -> _105178) : (@EXTENSIONAL A _105178 (@UNIV A) f) = ((@EXTENSIONAL A _105178 (@UNIV A) f) = True).
Proof. exact (@lem7 (@EXTENSIONAL A _105178 (@UNIV A) f)). Qed.
Lemma lem4432396 {_83095 : Type'} : term1 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem4432397 {_83095 : Type'} (p : _83095 -> Prop) : term2 _83095 p.
Proof. exact (@lem4432396 _83095 p). Qed.
Lemma lem4432398 {_83095 : Type'} (p : _83095 -> Prop) : (term2 _83095 p) = (term3 _83095 p).
Proof. exact (eq_refl (term2 _83095 p)). Qed.
Lemma lem4432399 {_83095 : Type'} (p : _83095 -> Prop) : term3 _83095 p.
Proof. exact (EQ_MP (@lem4432398 _83095 p) (@lem4432397 _83095 p)). Qed.
Lemma lem4432400 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term4 _83095 p x.
Proof. exact (@lem4432399 _83095 p x). Qed.
Lemma lem4432401 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term4 _83095 p x) = ((term5 _83095 x p) = (p x)).
Proof. exact (eq_refl (term4 _83095 p x)). Qed.
Lemma lem4432410 {A K : Type'} (k : K -> Prop) : term6 A K k.
Proof. exact (@lem4399444 A K k). Qed.
Lemma lem4432411 {A K : Type'} (k : K -> Prop) : (term6 A K k) = (term7 A K k).
Proof. exact (eq_refl (term6 A K k)). Qed.
Lemma lem4432412 {A K : Type'} (k : K -> Prop) : term7 A K k.
Proof. exact (EQ_MP (@lem4432411 A K k) (@lem4432410 A K k)). Qed.
Lemma lem4432413 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term8 A K k s.
Proof. exact (@lem4432412 A K k s). Qed.
Lemma lem4432414 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term8 A K k s) = ((@cartesian_product A K k s) = (term9 A K k s)).
Proof. exact (eq_refl (term8 A K k s)). Qed.
Lemma lem4432416 {A : Type'} (x : A) : term10 A x.
Proof. exact (@lem3204818 A x). Qed.
Lemma lem4432417 {A : Type'} (x : A) : (term10 A x) = (@IN A x (@UNIV A)).
Proof. exact (eq_refl (term10 A x)). Qed.
Lemma lem4432418 {A : Type'} (x : A) : @IN A x (@UNIV A).
Proof. exact (EQ_MP (@lem4432417 A x) (@lem4432416 A x)). Qed.
Lemma lem4432419 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = ((@IN A x (@UNIV A)) = True).
Proof. exact (@lem7 (@IN A x (@UNIV A))). Qed.
Lemma lem4432421 {A : Type'} (s : A -> Prop) : term11 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem4432422 {A : Type'} (s : A -> Prop) : (term11 A s) = (term12 A s).
Proof. exact (eq_refl (term11 A s)). Qed.
Lemma lem4432423 {A : Type'} (s : A -> Prop) : term12 A s.
Proof. exact (EQ_MP (@lem4432422 A s) (@lem4432421 A s)). Qed.
Lemma lem4432424 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term13 A s t.
Proof. exact (@lem4432423 A s t). Qed.
Lemma lem4432425 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term13 A s t) = ((s = t) = (term14 A s t)).
Proof. exact (eq_refl (term13 A s t)). Qed.
Lemma lem4432430 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term14 A s t).
Proof. exact (EQ_MP (@lem4432425 A s t) (@lem4432424 A s t)). Qed.
Lemma lem4432431 {A K : Type'} (s : type805 A K) (t : type805 A K) : (s = t) = (term15 A K s t).
Proof. exact (@lem4432430 (K -> A) s t). Qed.
Lemma lem4432432 {A K : Type'} : ((term16 A K) = (@UNIV (K -> A))) = (term17 A K).
Proof. exact (@lem4432431 A K (term16 A K) (@UNIV (K -> A))). Qed.
Lemma lem4432442 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@cartesian_product A K k s) = (term9 A K k s).
Proof. exact (EQ_MP (@lem4432414 A K k s) (@lem4432413 A K k s)). Qed.
Lemma lem4432443 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@cartesian_product A K k s) = (term9 A K k s).
Proof. exact (@lem4432442 A K k s). Qed.
Lemma lem4432444 {A K : Type'} : (term16 A K) = (term18 A K).
Proof. exact (@lem4432443 A K (@UNIV K) (term19 A K)). Qed.
Lemma lem4432458 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem4432419 A x) (@lem4432418 A x)). Qed.
Lemma lem4432459 {K : Type'} (x : K) : (@IN K x (@UNIV K)) = True.
Proof. exact (@lem4432458 K x). Qed.
Lemma lem4432460 {K : Type'} (i : K) : (@IN K i (@UNIV K)) = True.
Proof. exact (@lem4432459 K i). Qed.
Lemma lem4432461 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4432462 {K : Type'} (i : K) : (term20 K i) = (imp True).
Proof. exact (MK_COMB (@lem4432461) (@lem4432460 K i)). Qed.
Lemma lem4432464 {A B : Type'} (f : A -> B) (y : A) : (term21 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4432465 {A K : Type'} (f : type1470 A K) (y : K) : (term22 A K f y) = (f y).
Proof. exact (@lem4432464 K (A -> Prop) f y). Qed.
Lemma lem4432466 {A K : Type'} (i : K) : (term23 A K i) = (term24 A K i).
Proof. exact (@lem4432465 A K (term19 A K) i). Qed.
Lemma lem4432467 {A K : Type'} (i : K) : (term24 A K i) = (@UNIV A).
Proof. exact (eq_refl (term24 A K i)). Qed.
Lemma lem4432468 {A K : Type'} : (term25 A K) = (term19 A K).
Proof. exact (fun_ext (fun i : K => @lem4432467 A K i)). Qed.
Lemma lem4432469 {K : Type'} (i : K) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem4432470 {A K : Type'} (i : K) : (term23 A K i) = (term24 A K i).
Proof. exact (MK_COMB (@lem4432468 A K) (@lem4432469 K i)). Qed.
Lemma lem4432471 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4432472 {A K : Type'} (i : K) : (term26 A K i) = (term27 A K i).
Proof. exact (MK_COMB (@lem4432471 A) (@lem4432470 A K i)). Qed.
Lemma lem4432473 {A K : Type'} (i : K) : (term24 A K i) = (@UNIV A).
Proof. exact (eq_refl (term24 A K i)). Qed.
Lemma lem4432474 {A K : Type'} (i : K) : ((term23 A K i) = (term24 A K i)) = ((term24 A K i) = (@UNIV A)).
Proof. exact (MK_COMB (@lem4432472 A K i) (@lem4432473 A K i)). Qed.
Lemma lem4432475 {A K : Type'} (i : K) : (term24 A K i) = (@UNIV A).
Proof. exact (EQ_MP (@lem4432474 A K i) (@lem4432466 A K i)). Qed.
Lemma lem4432476 {A K : Type'} (f : K -> A) (i : K) : (term28 A K f i) = (term28 A K f i).
Proof. exact (eq_refl (term28 A K f i)). Qed.
Lemma lem4432477 {A K : Type'} (f : K -> A) (i : K) : (term29 A K f i) = (term30 A K f i).
Proof. exact (MK_COMB (@lem4432476 A K f i) (@lem4432475 A K i)). Qed.
Lemma lem4432479 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem4432419 A x) (@lem4432418 A x)). Qed.
Lemma lem4432480 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (@lem4432479 A x). Qed.
Lemma lem4432481 {A K : Type'} (f : K -> A) (i : K) : (term30 A K f i) = True.
Proof. exact (@lem4432480 A (f i)). Qed.
Lemma lem4432482 {A K : Type'} (f : K -> A) (i : K) : (term29 A K f i) = True.
Proof. exact (TRANS (@lem4432477 A K f i) (@lem4432481 A K f i)). Qed.
Lemma lem4432483 {A K : Type'} (f : K -> A) (i : K) : (term31 A K f i) = (True -> True).
Proof. exact (MK_COMB (@lem4432462 K i) (@lem4432482 A K f i)). Qed.
Lemma lem4432485 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem4432486 : (True -> True) = True.
Proof. exact (@lem4432485 True). Qed.
Lemma lem4432487 {A K : Type'} (f : K -> A) (i : K) : (term31 A K f i) = True.
Proof. exact (TRANS (@lem4432483 A K f i) (@lem4432486)). Qed.
Lemma lem4432488 {A K : Type'} (f : K -> A) : (term32 A K f) = (term33 K).
Proof. exact (fun_ext (fun i : K => @lem4432487 A K f i)). Qed.
Lemma lem4432489 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4432490 {A K : Type'} (f : K -> A) : (term34 A K f) = (term35 K).
Proof. exact (MK_COMB (@lem4432489 K) (@lem4432488 A K f)). Qed.
Lemma lem4432492 {A : Type'} (t : Prop) : (term36 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4432493 {K : Type'} (t : Prop) : (term36 K t) = t.
Proof. exact (@lem4432492 K t). Qed.
Lemma lem4432494 {K : Type'} : (term35 K) = True.
Proof. exact (@lem4432493 K True). Qed.
Lemma lem4432495 {A K : Type'} (f : K -> A) : (term34 A K f) = True.
Proof. exact (TRANS (@lem4432490 A K f) (@lem4432494 K)). Qed.
Lemma lem4432496 {A K : Type'} (f : K -> A) : (term37 A K f) = (term37 A K f).
Proof. exact (eq_refl (term37 A K f)). Qed.
Lemma lem4432497 {A K : Type'} (f : K -> A) : (term38 A K f) = (term39 A K f).
Proof. exact (MK_COMB (@lem4432496 A K f) (@lem4432495 A K f)). Qed.
Lemma lem4432499 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem4432500 {A K : Type'} (f : K -> A) : (term39 A K f) = (@EXTENSIONAL K A (@UNIV K) f).
Proof. exact (@lem4432499 (@EXTENSIONAL K A (@UNIV K) f)). Qed.
Lemma lem4432501 {A K : Type'} (f : K -> A) : (term38 A K f) = (@EXTENSIONAL K A (@UNIV K) f).
Proof. exact (TRANS (@lem4432497 A K f) (@lem4432500 A K f)). Qed.
Lemma lem4432502 {A K : Type'} (GEN_PVAR_140 : K -> A) : (@SETSPEC (K -> A) GEN_PVAR_140) = (@SETSPEC (K -> A) GEN_PVAR_140).
Proof. exact (eq_refl (@SETSPEC (K -> A) GEN_PVAR_140)). Qed.
Lemma lem4432503 {A K : Type'} (GEN_PVAR_140 : K -> A) (f : K -> A) : (term40 A K GEN_PVAR_140 f) = (term41 A K GEN_PVAR_140 f).
Proof. exact (MK_COMB (@lem4432502 A K GEN_PVAR_140) (@lem4432501 A K f)). Qed.
Lemma lem4432504 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4432505 {A K : Type'} (GEN_PVAR_140 : K -> A) (f : K -> A) : (term42 A K GEN_PVAR_140 f) = (term43 A K GEN_PVAR_140 f).
Proof. exact (MK_COMB (@lem4432503 A K GEN_PVAR_140 f) (@lem4432504 A K f)). Qed.
Lemma lem4432506 {A K : Type'} (GEN_PVAR_140 : K -> A) : (term44 A K GEN_PVAR_140) = (term45 A K GEN_PVAR_140).
Proof. exact (fun_ext (fun f : K -> A => @lem4432505 A K GEN_PVAR_140 f)). Qed.
Lemma lem4432507 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4432508 {A K : Type'} (GEN_PVAR_140 : K -> A) : (term46 A K GEN_PVAR_140) = (term47 A K GEN_PVAR_140).
Proof. exact (MK_COMB (@lem4432507 A K) (@lem4432506 A K GEN_PVAR_140)). Qed.
Lemma lem4432513 {A K : Type'} : (term48 A K) = (term49 A K).
Proof. exact (fun_ext (fun GEN_PVAR_140 : K -> A => @lem4432508 A K GEN_PVAR_140)). Qed.
Lemma lem4432514 {A K : Type'} : (@GSPEC (K -> A)) = (@GSPEC (K -> A)).
Proof. exact (eq_refl (@GSPEC (K -> A))). Qed.
Lemma lem4432515 {A K : Type'} : (term18 A K) = (term50 A K).
Proof. exact (MK_COMB (@lem4432514 A K) (@lem4432513 A K)). Qed.
Lemma lem4432516 {A K : Type'} : (term16 A K) = (term50 A K).
Proof. exact (TRANS (@lem4432444 A K) (@lem4432515 A K)). Qed.
Lemma lem4432517 {A K : Type'} (x : K -> A) : (@IN (K -> A) x) = (@IN (K -> A) x).
Proof. exact (eq_refl (@IN (K -> A) x)). Qed.
Lemma lem4432518 {A K : Type'} (x : K -> A) : (term51 A K x) = (term52 A K x).
Proof. exact (MK_COMB (@lem4432517 A K x) (@lem4432516 A K)). Qed.
Lemma lem4432520 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term5 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem4432401 _83095 p x) (@lem4432400 _83095 p x)). Qed.
Lemma lem4432521 {A K : Type'} (p : type805 A K) (x : K -> A) : (term53 A K x p) = (p x).
Proof. exact (@lem4432520 (K -> A) p x). Qed.
Lemma lem4432522 {A K : Type'} (x : K -> A) : (term54 A K x) = (term0 A K x).
Proof. exact (@lem4432521 A K (term55 A K) x). Qed.
Lemma lem4432523 {A K : Type'} (f : K -> A) : (term0 A K f) = (@EXTENSIONAL K A (@UNIV K) f).
Proof. exact (eq_refl (term0 A K f)). Qed.
Lemma lem4432524 {A K : Type'} (GEN_PVAR_140 : K -> A) : (@SETSPEC (K -> A) GEN_PVAR_140) = (@SETSPEC (K -> A) GEN_PVAR_140).
Proof. exact (eq_refl (@SETSPEC (K -> A) GEN_PVAR_140)). Qed.
Lemma lem4432525 {A K : Type'} (GEN_PVAR_140 : K -> A) (f : K -> A) : (term56 A K GEN_PVAR_140 f) = (term41 A K GEN_PVAR_140 f).
Proof. exact (MK_COMB (@lem4432524 A K GEN_PVAR_140) (@lem4432523 A K f)). Qed.
Lemma lem4432526 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4432527 {A K : Type'} (GEN_PVAR_140 : K -> A) (f : K -> A) : (term57 A K GEN_PVAR_140 f) = (term43 A K GEN_PVAR_140 f).
Proof. exact (MK_COMB (@lem4432525 A K GEN_PVAR_140 f) (@lem4432526 A K f)). Qed.
Lemma lem4432528 {A K : Type'} (GEN_PVAR_140 : K -> A) : (term58 A K GEN_PVAR_140) = (term45 A K GEN_PVAR_140).
Proof. exact (fun_ext (fun f : K -> A => @lem4432527 A K GEN_PVAR_140 f)). Qed.
Lemma lem4432529 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4432530 {A K : Type'} (GEN_PVAR_140 : K -> A) : (term59 A K GEN_PVAR_140) = (term47 A K GEN_PVAR_140).
Proof. exact (MK_COMB (@lem4432529 A K) (@lem4432528 A K GEN_PVAR_140)). Qed.
Lemma lem4432531 {A K : Type'} : (term60 A K) = (term49 A K).
Proof. exact (fun_ext (fun GEN_PVAR_140 : K -> A => @lem4432530 A K GEN_PVAR_140)). Qed.
Lemma lem4432532 {A K : Type'} : (@GSPEC (K -> A)) = (@GSPEC (K -> A)).
Proof. exact (eq_refl (@GSPEC (K -> A))). Qed.
Lemma lem4432533 {A K : Type'} : (term61 A K) = (term50 A K).
Proof. exact (MK_COMB (@lem4432532 A K) (@lem4432531 A K)). Qed.
Lemma lem4432534 {A K : Type'} (x : K -> A) : (@IN (K -> A) x) = (@IN (K -> A) x).
Proof. exact (eq_refl (@IN (K -> A) x)). Qed.
Lemma lem4432535 {A K : Type'} (x : K -> A) : (term54 A K x) = (term52 A K x).
Proof. exact (MK_COMB (@lem4432534 A K x) (@lem4432533 A K)). Qed.
Lemma lem4432536 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4432537 {A K : Type'} (x : K -> A) : (term62 A K x) = (term63 A K x).
Proof. exact (MK_COMB (@lem4432536) (@lem4432535 A K x)). Qed.
Lemma lem4432538 {A K : Type'} (x : K -> A) : (term0 A K x) = (@EXTENSIONAL K A (@UNIV K) x).
Proof. exact (eq_refl (term0 A K x)). Qed.
Lemma lem4432539 {A K : Type'} (x : K -> A) : ((term54 A K x) = (term0 A K x)) = ((term52 A K x) = (@EXTENSIONAL K A (@UNIV K) x)).
Proof. exact (MK_COMB (@lem4432537 A K x) (@lem4432538 A K x)). Qed.
Lemma lem4432540 {A K : Type'} (x : K -> A) : (term52 A K x) = (@EXTENSIONAL K A (@UNIV K) x).
Proof. exact (EQ_MP (@lem4432539 A K x) (@lem4432522 A K x)). Qed.
Lemma lem4432541 {A K : Type'} (x : K -> A) : (term51 A K x) = (@EXTENSIONAL K A (@UNIV K) x).
Proof. exact (TRANS (@lem4432518 A K x) (@lem4432540 A K x)). Qed.
Lemma lem4432542 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4432543 {A K : Type'} (x : K -> A) : (term64 A K x) = (term65 A K x).
Proof. exact (MK_COMB (@lem4432542) (@lem4432541 A K x)). Qed.
Lemma lem4432545 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem4432419 A x) (@lem4432418 A x)). Qed.
Lemma lem4432546 {A K : Type'} (x : K -> A) : (@IN (K -> A) x (@UNIV (K -> A))) = True.
Proof. exact (@lem4432545 (K -> A) x). Qed.
Lemma lem4432547 {A K : Type'} (x : K -> A) : ((term51 A K x) = (@IN (K -> A) x (@UNIV (K -> A)))) = ((@EXTENSIONAL K A (@UNIV K) x) = True).
Proof. exact (MK_COMB (@lem4432543 A K x) (@lem4432546 A K x)). Qed.
Lemma lem4432549 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem4432550 {A K : Type'} (x : K -> A) : ((@EXTENSIONAL K A (@UNIV K) x) = True) = (@EXTENSIONAL K A (@UNIV K) x).
Proof. exact (@lem4432549 (@EXTENSIONAL K A (@UNIV K) x)). Qed.
Lemma lem4432551 {A K : Type'} (x : K -> A) : ((term51 A K x) = (@IN (K -> A) x (@UNIV (K -> A)))) = (@EXTENSIONAL K A (@UNIV K) x).
Proof. exact (TRANS (@lem4432547 A K x) (@lem4432550 A K x)). Qed.
Lemma lem4432552 {A K : Type'} : (term66 A K) = (term55 A K).
Proof. exact (fun_ext (fun x : K -> A => @lem4432551 A K x)). Qed.
Lemma lem4432553 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4432554 {A K : Type'} : (term17 A K) = (term67 A K).
Proof. exact (MK_COMB (@lem4432553 A K) (@lem4432552 A K)). Qed.
Lemma lem4432559 {A K : Type'} : ((term16 A K) = (@UNIV (K -> A))) = (term67 A K).
Proof. exact (TRANS (@lem4432432 A K) (@lem4432554 A K)). Qed.
Lemma lem4432560 {A K : Type'} : (term67 A K) = ((term16 A K) = (@UNIV (K -> A))).
Proof. exact (SYM (@lem4432559 A K)). Qed.
Lemma lem4432566 {_105178 A : Type'} (f : A -> _105178) : (@EXTENSIONAL A _105178 (@UNIV A) f) = True.
Proof. exact (EQ_MP (@lem4432370 _105178 A f) (@lem4432369 _105178 A f)). Qed.
Lemma lem4432567 {A K : Type'} (f : K -> A) : (@EXTENSIONAL K A (@UNIV K) f) = True.
Proof. exact (@lem4432566 A K f). Qed.
Lemma lem4432568 {A K : Type'} (x : K -> A) : (@EXTENSIONAL K A (@UNIV K) x) = True.
Proof. exact (@lem4432567 A K x). Qed.
Lemma lem4432569 {A K : Type'} : (term55 A K) = (term68 A K).
Proof. exact (fun_ext (fun x : K -> A => @lem4432568 A K x)). Qed.
Lemma lem4432570 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4432571 {A K : Type'} : (term67 A K) = (term69 A K).
Proof. exact (MK_COMB (@lem4432570 A K) (@lem4432569 A K)). Qed.
Lemma lem4432573 {A : Type'} (t : Prop) : (term36 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4432574 {A K : Type'} (t : Prop) : (term70 A K t) = t.
Proof. exact (@lem4432573 (K -> A) t). Qed.
Lemma lem4432575 {A K : Type'} : (term69 A K) = True.
Proof. exact (@lem4432574 A K True). Qed.
Lemma lem4432576 {A K : Type'} : (term67 A K) = True.
Proof. exact (TRANS (@lem4432571 A K) (@lem4432575 A K)). Qed.
Lemma lem4432577 {A K : Type'} : True = (term67 A K).
Proof. exact (SYM (@lem4432576 A K)). Qed.
Lemma lem4432578 {A K : Type'} : term67 A K.
Proof. exact (EQ_MP (@lem4432577 A K) (@lem0)). Qed.
Lemma lem4432579 {A K : Type'} : (term16 A K) = (@UNIV (K -> A)).
Proof. exact (EQ_MP (@lem4432560 A K) (@lem4432578 A K)). Qed.
