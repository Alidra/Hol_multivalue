Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm4373533_term_abbrevs.
Require Import EXTENSION_spec.
Require Import FORALL_PAIR_THM_spec.
Require Import IN_CROSS_spec.
Lemma lem4373357 {_103718 _103721 : Type'} (x : _103718) : term0 _103718 _103721 x.
Proof. exact (@lem4325365 _103718 _103721 x). Qed.
Lemma lem4373358 {_103718 _103721 : Type'} (x : _103718) : (term0 _103718 _103721 x) = (term1 _103718 _103721 x).
Proof. exact (eq_refl (term0 _103718 _103721 x)). Qed.
Lemma lem4373359 {_103718 _103721 : Type'} (x : _103718) : term1 _103718 _103721 x.
Proof. exact (EQ_MP (@lem4373358 _103718 _103721 x) (@lem4373357 _103718 _103721 x)). Qed.
Lemma lem4373360 {_103718 _103721 : Type'} (x : _103718) (y : _103721) : term2 _103718 _103721 x y.
Proof. exact (@lem4373359 _103718 _103721 x y). Qed.
Lemma lem4373361 {_103718 _103721 : Type'} (x : _103718) (y : _103721) : (term2 _103718 _103721 x y) = (term3 _103718 _103721 x y).
Proof. exact (eq_refl (term2 _103718 _103721 x y)). Qed.
Lemma lem4373362 {_103718 _103721 : Type'} (x : _103718) (y : _103721) : term3 _103718 _103721 x y.
Proof. exact (EQ_MP (@lem4373361 _103718 _103721 x y) (@lem4373360 _103718 _103721 x y)). Qed.
Lemma lem4373363 {_103718 _103721 : Type'} (x : _103718) (y : _103721) (s : _103718 -> Prop) : term4 _103718 _103721 x y s.
Proof. exact (@lem4373362 _103718 _103721 x y s). Qed.
Lemma lem4373364 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) : (term4 _103718 _103721 x y s) = (term5 _103718 _103721 x s y).
Proof. exact (eq_refl (term4 _103718 _103721 x y s)). Qed.
Lemma lem4373365 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) : term5 _103718 _103721 x s y.
Proof. exact (EQ_MP (@lem4373364 _103718 _103721 x s y) (@lem4373363 _103718 _103721 x y s)). Qed.
Lemma lem4373366 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : term6 _103718 _103721 x s y t.
Proof. exact (@lem4373365 _103718 _103721 x s y t). Qed.
Lemma lem4373367 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term6 _103718 _103721 x s y t) = ((term7 _103718 _103721 x y s t) = (term8 _103718 _103721 x s y t)).
Proof. exact (eq_refl (term6 _103718 _103721 x s y t)). Qed.
Lemma lem4373407 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : term9 _5106 _5107 P.
Proof. exact (@lem49909 _5106 _5107 P). Qed.
Lemma lem4373408 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term9 _5106 _5107 P) = ((term10 _5106 _5107 P) = (term11 _5106 _5107 P)).
Proof. exact (eq_refl (term9 _5106 _5107 P)). Qed.
Lemma lem4373410 {A : Type'} (s : A -> Prop) : term12 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem4373411 {A : Type'} (s : A -> Prop) : (term12 A s) = (term13 A s).
Proof. exact (eq_refl (term12 A s)). Qed.
Lemma lem4373412 {A : Type'} (s : A -> Prop) : term13 A s.
Proof. exact (EQ_MP (@lem4373411 A s) (@lem4373410 A s)). Qed.
Lemma lem4373413 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term14 A s t.
Proof. exact (@lem4373412 A s t). Qed.
Lemma lem4373414 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term14 A s t) = ((s = t) = (term15 A s t)).
Proof. exact (eq_refl (term14 A s t)). Qed.
Lemma lem4373441 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term15 A s t).
Proof. exact (EQ_MP (@lem4373414 A s t) (@lem4373413 A s t)). Qed.
Lemma lem4373442 {_104960 _104961 : Type'} (s : type1210 _104960 _104961) (t : type1210 _104960 _104961) : (s = t) = (term16 _104960 _104961 s t).
Proof. exact (@lem4373441 (prod _104960 _104961) s t). Qed.
Lemma lem4373443 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : ((term17 _104960 _104961 s f) = (@CROSS _104961 _104960 s (@UNIV _104961))) = (term18 _104960 _104961 f s).
Proof. exact (@lem4373442 _104960 _104961 (term17 _104960 _104961 s f) (@CROSS _104961 _104960 s (@UNIV _104961))). Qed.
Lemma lem4373449 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term10 _5106 _5107 P) = (term11 _5106 _5107 P).
Proof. exact (EQ_MP (@lem4373408 _5106 _5107 P) (@lem4373407 _5106 _5107 P)). Qed.
Lemma lem4373450 {_104960 _104961 : Type'} (P : type1210 _104960 _104961) : (term19 _104960 _104961 P) = (term20 _104960 _104961 P).
Proof. exact (@lem4373449 _104961 _104960 P). Qed.
Lemma lem4373451 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : (term21 _104960 _104961 f s) = (term22 _104960 _104961 f s).
Proof. exact (@lem4373450 _104960 _104961 (term23 _104960 _104961 f s)). Qed.
Lemma lem4373452 {_104960 _104961 : Type'} (f : type686 _104961) (x : prod _104960 _104961) (s : _104960 -> Prop) : (term24 _104960 _104961 f s x) = ((term25 _104960 _104961 x s f) = (term26 _104960 _104961 x s)).
Proof. exact (eq_refl (term24 _104960 _104961 f s x)). Qed.
Lemma lem4373453 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : (term27 _104960 _104961 f s) = (term23 _104960 _104961 f s).
Proof. exact (fun_ext (fun x : prod _104960 _104961 => @lem4373452 _104960 _104961 f x s)). Qed.
Lemma lem4373454 {_104960 _104961 : Type'} : (@all (prod _104960 _104961)) = (@all (prod _104960 _104961)).
Proof. exact (eq_refl (@all (prod _104960 _104961))). Qed.
Lemma lem4373455 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : (term21 _104960 _104961 f s) = (term18 _104960 _104961 f s).
Proof. exact (MK_COMB (@lem4373454 _104960 _104961) (@lem4373453 _104960 _104961 f s)). Qed.
Lemma lem4373456 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4373457 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : (term28 _104960 _104961 f s) = (term29 _104960 _104961 f s).
Proof. exact (MK_COMB (@lem4373456) (@lem4373455 _104960 _104961 f s)). Qed.
Lemma lem4373458 {_104960 _104961 : Type'} (f : type686 _104961) (p1 : _104960) (p2 : _104961) (s : _104960 -> Prop) : (term30 _104960 _104961 f s p1 p2) = ((term31 _104960 _104961 p1 p2 s f) = (term32 _104960 _104961 p1 p2 s)).
Proof. exact (eq_refl (term30 _104960 _104961 f s p1 p2)). Qed.
Lemma lem4373459 {_104960 _104961 : Type'} (f : type686 _104961) (p1 : _104960) (s : _104960 -> Prop) : (term33 _104960 _104961 f s p1) = (term34 _104960 _104961 f p1 s).
Proof. exact (fun_ext (fun p2 : _104961 => @lem4373458 _104960 _104961 f p1 p2 s)). Qed.
Lemma lem4373460 {_104961 : Type'} : (@all _104961) = (@all _104961).
Proof. exact (eq_refl (@all _104961)). Qed.
Lemma lem4373461 {_104960 _104961 : Type'} (f : type686 _104961) (p1 : _104960) (s : _104960 -> Prop) : (term35 _104960 _104961 f s p1) = (term36 _104960 _104961 f p1 s).
Proof. exact (MK_COMB (@lem4373460 _104961) (@lem4373459 _104960 _104961 f p1 s)). Qed.
Lemma lem4373462 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : (term37 _104960 _104961 f s) = (term38 _104960 _104961 f s).
Proof. exact (fun_ext (fun p1 : _104960 => @lem4373461 _104960 _104961 f p1 s)). Qed.
Lemma lem4373463 {_104960 : Type'} : (@all _104960) = (@all _104960).
Proof. exact (eq_refl (@all _104960)). Qed.
Lemma lem4373464 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : (term22 _104960 _104961 f s) = (term39 _104960 _104961 f s).
Proof. exact (MK_COMB (@lem4373463 _104960) (@lem4373462 _104960 _104961 f s)). Qed.
Lemma lem4373465 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : ((term21 _104960 _104961 f s) = (term22 _104960 _104961 f s)) = ((term18 _104960 _104961 f s) = (term39 _104960 _104961 f s)).
Proof. exact (MK_COMB (@lem4373457 _104960 _104961 f s) (@lem4373464 _104960 _104961 f s)). Qed.
Lemma lem4373466 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : (term18 _104960 _104961 f s) = (term39 _104960 _104961 f s).
Proof. exact (EQ_MP (@lem4373465 _104960 _104961 f s) (@lem4373451 _104960 _104961 f s)). Qed.
Lemma lem4373473 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : ((term17 _104960 _104961 s f) = (@CROSS _104961 _104960 s (@UNIV _104961))) = (term39 _104960 _104961 f s).
Proof. exact (TRANS (@lem4373443 _104960 _104961 f s) (@lem4373466 _104960 _104961 f s)). Qed.
Lemma lem4373485 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term7 _103718 _103721 x y s t) = (term8 _103718 _103721 x s y t).
Proof. exact (EQ_MP (@lem4373367 _103718 _103721 x s y t) (@lem4373366 _103718 _103721 x s y t)). Qed.
Lemma lem4373486 {_104960 _104961 : Type'} (x : _104960) (s : _104960 -> Prop) (y : _104961) (t : _104961 -> Prop) : (term7 _104960 _104961 x y s t) = (term8 _104960 _104961 x s y t).
Proof. exact (@lem4373485 _104960 _104961 x s y t). Qed.
Lemma lem4373487 {_104960 _104961 : Type'} (p1 : _104960) (s : _104960 -> Prop) (p2 : _104961) (f : type686 _104961) : (term31 _104960 _104961 p1 p2 s f) = (term40 _104960 _104961 p1 s p2 f).
Proof. exact (@lem4373486 _104960 _104961 p1 s p2 (@INTERS _104961 f)). Qed.
Lemma lem4373491 {_104961 : Type'} (f : type686 _104961) (h1 : f = (@EMPTY (_104961 -> Prop))) : f = (@EMPTY (_104961 -> Prop)).
Proof. exact (h1). Qed.
Lemma lem4373492 {_104961 : Type'} : (@INTERS _104961) = (@INTERS _104961).
Proof. exact (eq_refl (@INTERS _104961)). Qed.
Lemma lem4373493 {_104961 : Type'} (f : type686 _104961) (h1 : f = (@EMPTY (_104961 -> Prop))) : (@INTERS _104961 f) = (@INTERS _104961 (@EMPTY (_104961 -> Prop))).
Proof. exact (MK_COMB (@lem4373492 _104961) (@lem4373491 _104961 f h1)). Qed.
Lemma lem4373494 {_104961 : Type'} (p2 : _104961) : (@IN _104961 p2) = (@IN _104961 p2).
Proof. exact (eq_refl (@IN _104961 p2)). Qed.
Lemma lem4373495 {_104961 : Type'} (p2 : _104961) (f : type686 _104961) (h1 : f = (@EMPTY (_104961 -> Prop))) : (term41 _104961 p2 f) = (term42 _104961 p2).
Proof. exact (MK_COMB (@lem4373494 _104961 p2) (@lem4373493 _104961 f h1)). Qed.
Lemma lem4373496 {_104960 : Type'} (p1 : _104960) (s : _104960 -> Prop) : (term43 _104960 p1 s) = (term43 _104960 p1 s).
Proof. exact (eq_refl (term43 _104960 p1 s)). Qed.
Lemma lem4373497 {_104960 _104961 : Type'} (p1 : _104960) (s : _104960 -> Prop) (p2 : _104961) (f : type686 _104961) (h1 : f = (@EMPTY (_104961 -> Prop))) : (term40 _104960 _104961 p1 s p2 f) = (term44 _104960 _104961 p1 s p2).
Proof. exact (MK_COMB (@lem4373496 _104960 p1 s) (@lem4373495 _104961 p2 f h1)). Qed.
Lemma lem4373500 {_104960 _104961 : Type'} (p1 : _104960) (s : _104960 -> Prop) (p2 : _104961) (f : type686 _104961) (h1 : f = (@EMPTY (_104961 -> Prop))) : (term31 _104960 _104961 p1 p2 s f) = (term44 _104960 _104961 p1 s p2).
Proof. exact (TRANS (@lem4373487 _104960 _104961 p1 s p2 f) (@lem4373497 _104960 _104961 p1 s p2 f h1)). Qed.
Lemma lem4373501 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4373502 {_104960 _104961 : Type'} (p1 : _104960) (s : _104960 -> Prop) (p2 : _104961) (f : type686 _104961) (h1 : f = (@EMPTY (_104961 -> Prop))) : (term45 _104960 _104961 p1 p2 s f) = (term46 _104960 _104961 p1 s p2).
Proof. exact (MK_COMB (@lem4373501) (@lem4373500 _104960 _104961 p1 s p2 f h1)). Qed.
Lemma lem4373504 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term7 _103718 _103721 x y s t) = (term8 _103718 _103721 x s y t).
Proof. exact (EQ_MP (@lem4373367 _103718 _103721 x s y t) (@lem4373366 _103718 _103721 x s y t)). Qed.
Lemma lem4373505 {_104960 _104961 : Type'} (x : _104960) (s : _104960 -> Prop) (y : _104961) (t : _104961 -> Prop) : (term7 _104960 _104961 x y s t) = (term8 _104960 _104961 x s y t).
Proof. exact (@lem4373504 _104960 _104961 x s y t). Qed.
Lemma lem4373506 {_104960 _104961 : Type'} (p1 : _104960) (s : _104960 -> Prop) (p2 : _104961) : (term32 _104960 _104961 p1 p2 s) = (term47 _104960 _104961 p1 s p2).
Proof. exact (@lem4373505 _104960 _104961 p1 s p2 (@UNIV _104961)). Qed.
Lemma lem4373509 {_104960 _104961 : Type'} (p1 : _104960) (s : _104960 -> Prop) (p2 : _104961) (f : type686 _104961) (h1 : f = (@EMPTY (_104961 -> Prop))) : ((term31 _104960 _104961 p1 p2 s f) = (term32 _104960 _104961 p1 p2 s)) = ((term44 _104960 _104961 p1 s p2) = (term47 _104960 _104961 p1 s p2)).
Proof. exact (MK_COMB (@lem4373502 _104960 _104961 p1 s p2 f h1) (@lem4373506 _104960 _104961 p1 s p2)). Qed.
Lemma lem4373514 {_104960 _104961 : Type'} (p1 : _104960) (s : _104960 -> Prop) (f : type686 _104961) (h1 : f = (@EMPTY (_104961 -> Prop))) : (term34 _104960 _104961 f p1 s) = (term48 _104960 _104961 p1 s).
Proof. exact (fun_ext (fun p2 : _104961 => @lem4373509 _104960 _104961 p1 s p2 f h1)). Qed.
Lemma lem4373515 {_104961 : Type'} : (@all _104961) = (@all _104961).
Proof. exact (eq_refl (@all _104961)). Qed.
Lemma lem4373516 {_104960 _104961 : Type'} (p1 : _104960) (s : _104960 -> Prop) (f : type686 _104961) (h1 : f = (@EMPTY (_104961 -> Prop))) : (term36 _104960 _104961 f p1 s) = (term49 _104960 _104961 p1 s).
Proof. exact (MK_COMB (@lem4373515 _104961) (@lem4373514 _104960 _104961 p1 s f h1)). Qed.
Lemma lem4373523 {_104960 _104961 : Type'} (s : _104960 -> Prop) (f : type686 _104961) (h1 : f = (@EMPTY (_104961 -> Prop))) : (term38 _104960 _104961 f s) = (term50 _104960 _104961 s).
Proof. exact (fun_ext (fun p1 : _104960 => @lem4373516 _104960 _104961 p1 s f h1)). Qed.
Lemma lem4373524 {_104960 : Type'} : (@all _104960) = (@all _104960).
Proof. exact (eq_refl (@all _104960)). Qed.
Lemma lem4373525 {_104960 _104961 : Type'} (s : _104960 -> Prop) (f : type686 _104961) (h1 : f = (@EMPTY (_104961 -> Prop))) : (term39 _104960 _104961 f s) = (term51 _104960 _104961 s).
Proof. exact (MK_COMB (@lem4373524 _104960) (@lem4373523 _104960 _104961 s f h1)). Qed.
Lemma lem4373532 {_104960 _104961 : Type'} (s : _104960 -> Prop) (f : type686 _104961) (h1 : f = (@EMPTY (_104961 -> Prop))) : ((term17 _104960 _104961 s f) = (@CROSS _104961 _104960 s (@UNIV _104961))) = (term51 _104960 _104961 s).
Proof. exact (TRANS (@lem4373473 _104960 _104961 f s) (@lem4373525 _104960 _104961 s f h1)). Qed.
Lemma lem4373533 {_104960 _104961 : Type'} (s : _104960 -> Prop) (f : type686 _104961) (h1 : f = (@EMPTY (_104961 -> Prop))) : (term51 _104960 _104961 s) = ((term17 _104960 _104961 s f) = (@CROSS _104961 _104960 s (@UNIV _104961))).
Proof. exact (SYM (@lem4373532 _104960 _104961 s f h1)). Qed.
