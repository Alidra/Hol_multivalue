Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FORALL_CARTESIAN_PRODUCT_ELEMENTS_EQ_term_abbrevs.
Require Import FORALL_CARTESIAN_PRODUCT_ELEMENTS_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1833_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm82_spec.
Lemma lem4452399 {A K : Type'} (P : type1470 A K) : term0 A K P.
Proof. exact (@lem4452398 A K P). Qed.
Lemma lem4452400 {A K : Type'} (P : type1470 A K) : (term0 A K P) = (term1 A K P).
Proof. exact (eq_refl (term0 A K P)). Qed.
Lemma lem4452401 {A K : Type'} (P : type1470 A K) : term1 A K P.
Proof. exact (EQ_MP (@lem4452400 A K P) (@lem4452399 A K P)). Qed.
Lemma lem4452402 {A K : Type'} (P : type1470 A K) (k : K -> Prop) : term2 A K P k.
Proof. exact (@lem4452401 A K P k). Qed.
Lemma lem4452403 {A K : Type'} (k : K -> Prop) (P : type1470 A K) : (term2 A K P k) = (term3 A K k P).
Proof. exact (eq_refl (term2 A K P k)). Qed.
Lemma lem4452404 {A K : Type'} (k : K -> Prop) (P : type1470 A K) : term3 A K k P.
Proof. exact (EQ_MP (@lem4452403 A K k P) (@lem4452402 A K P k)). Qed.
Lemma lem4452405 {A K : Type'} (k : K -> Prop) (P : type1470 A K) (s : type1470 A K) : term4 A K k P s.
Proof. exact (@lem4452404 A K k P s). Qed.
Lemma lem4452406 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term4 A K k P s) = ((term5 A K s k P) = (term6 A K k s P)).
Proof. exact (eq_refl (term4 A K k P s)). Qed.
Lemma lem4452423 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term7 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4452424 (p : Prop) (q : Prop) (p' : Prop) : term8 p q p'.
Proof. exact (fun q' : Prop => @lem4452423 p q p' q'). Qed.
Lemma lem4452425 (p : Prop) (q : Prop) : term9 p q.
Proof. exact (fun p' : Prop => @lem4452424 p q p'). Qed.
Lemma lem4452426 {_106843 _106845 : Type'} (s : type1470 _106843 _106845) (k : _106845 -> Prop) (P : type1470 _106843 _106845) : term10 _106843 _106845 s k P.
Proof. exact (@lem4452425 (term11 _106843 _106845 k s) ((term12 _106843 _106845 k s P) = (term5 _106843 _106845 s k P))). Qed.
Lemma lem4452427 {_106843 _106845 : Type'} (s : type1470 _106843 _106845) (k : _106845 -> Prop) (P : type1470 _106843 _106845) (p' : Prop) : term13 _106843 _106845 s k P p'.
Proof. exact (@lem4452426 _106843 _106845 s k P p'). Qed.
Lemma lem4452428 {_106843 _106845 : Type'} (s : type1470 _106843 _106845) (k : _106845 -> Prop) (P : type1470 _106843 _106845) (p' : Prop) : (term13 _106843 _106845 s k P p') = (term14 _106843 _106845 s k P p').
Proof. exact (eq_refl (term13 _106843 _106845 s k P p')). Qed.
Lemma lem4452429 {_106843 _106845 : Type'} (s : type1470 _106843 _106845) (k : _106845 -> Prop) (P : type1470 _106843 _106845) (p' : Prop) : term14 _106843 _106845 s k P p'.
Proof. exact (EQ_MP (@lem4452428 _106843 _106845 s k P p') (@lem4452427 _106843 _106845 s k P p')). Qed.
Lemma lem4452430 {_106843 _106845 : Type'} (s : type1470 _106843 _106845) (k : _106845 -> Prop) (P : type1470 _106843 _106845) (p' : Prop) (q' : Prop) : term15 _106843 _106845 s k P p' q'.
Proof. exact (@lem4452429 _106843 _106845 s k P p' q'). Qed.
Lemma lem4452431 {_106843 _106845 : Type'} (s : type1470 _106843 _106845) (k : _106845 -> Prop) (P : type1470 _106843 _106845) (p' : Prop) (q' : Prop) : (term15 _106843 _106845 s k P p' q') = (term16 _106843 _106845 s k P p' q').
Proof. exact (eq_refl (term15 _106843 _106845 s k P p' q')). Qed.
Lemma lem4452432 {_106843 _106845 : Type'} (s : type1470 _106843 _106845) (k : _106845 -> Prop) (P : type1470 _106843 _106845) (p' : Prop) (q' : Prop) : term16 _106843 _106845 s k P p' q'.
Proof. exact (EQ_MP (@lem4452431 _106843 _106845 s k P p' q') (@lem4452430 _106843 _106845 s k P p' q')). Qed.
Lemma lem4452435 {_106843 _106845 : Type'} (k : _106845 -> Prop) (s : type1470 _106843 _106845) : (term11 _106843 _106845 k s) = (term11 _106843 _106845 k s).
Proof. exact (eq_refl (term11 _106843 _106845 k s)). Qed.
Lemma lem4452436 {_106843 _106845 : Type'} (P : type1470 _106843 _106845) (k : _106845 -> Prop) (s : type1470 _106843 _106845) (q' : Prop) : term17 _106843 _106845 P k s q'.
Proof. exact (@lem4452432 _106843 _106845 s k P (term11 _106843 _106845 k s) q'). Qed.
Lemma lem4452437 {_106843 _106845 : Type'} (P : type1470 _106843 _106845) (k : _106845 -> Prop) (s : type1470 _106843 _106845) (q' : Prop) : term18 _106843 _106845 P k s q'.
Proof. exact (@lem4452436 _106843 _106845 P k s q' (@lem4452435 _106843 _106845 k s)). Qed.
Lemma lem4452438 {_106843 _106845 : Type'} (k : _106845 -> Prop) (s : type1470 _106843 _106845) (h1 : term11 _106843 _106845 k s) : term11 _106843 _106845 k s.
Proof. exact (h1). Qed.
Lemma lem4452439 {_106843 _106845 : Type'} (k : _106845 -> Prop) (s : type1470 _106843 _106845) : term19 _106843 _106845 k s.
Proof. exact (@lem82 ((@cartesian_product _106843 _106845 k s) = (@EMPTY (_106845 -> _106843)))). Qed.
Lemma lem4452494 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term5 A K s k P) = (term6 A K k s P).
Proof. exact (EQ_MP (@lem4452406 A K k s P) (@lem4452405 A K k P s)). Qed.
Lemma lem4452495 {_106843 _106845 : Type'} (k : _106845 -> Prop) (s : type1470 _106843 _106845) (P : type1470 _106843 _106845) : (term5 _106843 _106845 s k P) = (term6 _106843 _106845 k s P).
Proof. exact (@lem4452494 _106843 _106845 k s P). Qed.
Lemma lem4452499 {_106843 _106845 : Type'} (k : _106845 -> Prop) (s : type1470 _106843 _106845) (h1 : term11 _106843 _106845 k s) : ((@cartesian_product _106843 _106845 k s) = (@EMPTY (_106845 -> _106843))) = False.
Proof. exact (@lem4452439 _106843 _106845 k s (@lem4452438 _106843 _106845 k s h1)). Qed.
Lemma lem4452500 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4452501 {_106843 _106845 : Type'} (k : _106845 -> Prop) (s : type1470 _106843 _106845) (h1 : term11 _106843 _106845 k s) : (term20 _106843 _106845 k s) = (or False).
Proof. exact (MK_COMB (@lem4452500) (@lem4452499 _106843 _106845 k s h1)). Qed.
Lemma lem4452541 {_106843 _106845 : Type'} (k : _106845 -> Prop) (s : type1470 _106843 _106845) (P : type1470 _106843 _106845) : (term12 _106843 _106845 k s P) = (term12 _106843 _106845 k s P).
Proof. exact (eq_refl (term12 _106843 _106845 k s P)). Qed.
Lemma lem4452542 {_106843 _106845 : Type'} (P : type1470 _106843 _106845) (k : _106845 -> Prop) (s : type1470 _106843 _106845) (h1 : term11 _106843 _106845 k s) : (term6 _106843 _106845 k s P) = (term21 _106843 _106845 k s P).
Proof. exact (MK_COMB (@lem4452501 _106843 _106845 k s h1) (@lem4452541 _106843 _106845 k s P)). Qed.
Lemma lem4452544 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem4452545 {_106843 _106845 : Type'} (k : _106845 -> Prop) (s : type1470 _106843 _106845) (P : type1470 _106843 _106845) : (term21 _106843 _106845 k s P) = (term12 _106843 _106845 k s P).
Proof. exact (@lem4452544 (term12 _106843 _106845 k s P)). Qed.
Lemma lem4452585 {_106843 _106845 : Type'} (P : type1470 _106843 _106845) (k : _106845 -> Prop) (s : type1470 _106843 _106845) (h1 : term11 _106843 _106845 k s) : (term6 _106843 _106845 k s P) = (term12 _106843 _106845 k s P).
Proof. exact (TRANS (@lem4452542 _106843 _106845 P k s h1) (@lem4452545 _106843 _106845 k s P)). Qed.
Lemma lem4452586 {_106843 _106845 : Type'} (P : type1470 _106843 _106845) (k : _106845 -> Prop) (s : type1470 _106843 _106845) (h1 : term11 _106843 _106845 k s) : (term5 _106843 _106845 s k P) = (term12 _106843 _106845 k s P).
Proof. exact (TRANS (@lem4452495 _106843 _106845 k s P) (@lem4452585 _106843 _106845 P k s h1)). Qed.
Lemma lem4452587 {_106843 _106845 : Type'} (k : _106845 -> Prop) (s : type1470 _106843 _106845) (P : type1470 _106843 _106845) : (term22 _106843 _106845 k s P) = (term22 _106843 _106845 k s P).
Proof. exact (eq_refl (term22 _106843 _106845 k s P)). Qed.
Lemma lem4452588 {_106843 _106845 : Type'} (P : type1470 _106843 _106845) (k : _106845 -> Prop) (s : type1470 _106843 _106845) (h1 : term11 _106843 _106845 k s) : ((term12 _106843 _106845 k s P) = (term5 _106843 _106845 s k P)) = ((term12 _106843 _106845 k s P) = (term12 _106843 _106845 k s P)).
Proof. exact (MK_COMB (@lem4452587 _106843 _106845 k s P) (@lem4452586 _106843 _106845 P k s h1)). Qed.
Lemma lem4452590 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4452591 (x : Prop) : (x = x) = True.
Proof. exact (@lem4452590 Prop x). Qed.
Lemma lem4452592 {_106843 _106845 : Type'} (k : _106845 -> Prop) (s : type1470 _106843 _106845) (P : type1470 _106843 _106845) : ((term12 _106843 _106845 k s P) = (term12 _106843 _106845 k s P)) = True.
Proof. exact (@lem4452591 (term12 _106843 _106845 k s P)). Qed.
Lemma lem4452593 {_106843 _106845 : Type'} (P : type1470 _106843 _106845) (k : _106845 -> Prop) (s : type1470 _106843 _106845) (h1 : term11 _106843 _106845 k s) : ((term12 _106843 _106845 k s P) = (term5 _106843 _106845 s k P)) = True.
Proof. exact (TRANS (@lem4452588 _106843 _106845 P k s h1) (@lem4452592 _106843 _106845 k s P)). Qed.
Lemma lem4452594 {_106843 _106845 : Type'} (s : type1470 _106843 _106845) (k : _106845 -> Prop) (P : type1470 _106843 _106845) : term23 _106843 _106845 s k P.
Proof. exact (fun h0 : term11 _106843 _106845 k s => @lem4452593 _106843 _106845 P k s h0). Qed.
Lemma lem4452595 {_106843 _106845 : Type'} (P : type1470 _106843 _106845) (k : _106845 -> Prop) (s : type1470 _106843 _106845) : term24 _106843 _106845 P k s.
Proof. exact (@lem4452437 _106843 _106845 P k s True). Qed.
Lemma lem4452596 {_106843 _106845 : Type'} (P : type1470 _106843 _106845) (k : _106845 -> Prop) (s : type1470 _106843 _106845) : (term25 _106843 _106845 s k P) = (term26 _106843 _106845 k s).
Proof. exact (@lem4452595 _106843 _106845 P k s (@lem4452594 _106843 _106845 s k P)). Qed.
Lemma lem4452598 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem4452599 {_106843 _106845 : Type'} (k : _106845 -> Prop) (s : type1470 _106843 _106845) : (term26 _106843 _106845 k s) = True.
Proof. exact (@lem4452598 (term11 _106843 _106845 k s)). Qed.
Lemma lem4452600 {_106843 _106845 : Type'} (s : type1470 _106843 _106845) (k : _106845 -> Prop) (P : type1470 _106843 _106845) : (term25 _106843 _106845 s k P) = True.
Proof. exact (TRANS (@lem4452596 _106843 _106845 P k s) (@lem4452599 _106843 _106845 k s)). Qed.
Lemma lem4452601 {_106843 _106845 : Type'} (k : _106845 -> Prop) (P : type1470 _106843 _106845) : (term27 _106843 _106845 k P) = (term28 _106843 _106845).
Proof. exact (fun_ext (fun s : type1470 _106843 _106845 => @lem4452600 _106843 _106845 s k P)). Qed.
Lemma lem4452602 {_106843 _106845 : Type'} : (@all (_106845 -> _106843 -> Prop)) = (@all (_106845 -> _106843 -> Prop)).
Proof. exact (eq_refl (@all (_106845 -> _106843 -> Prop))). Qed.
Lemma lem4452603 {_106843 _106845 : Type'} (k : _106845 -> Prop) (P : type1470 _106843 _106845) : (term29 _106843 _106845 k P) = (term30 _106843 _106845).
Proof. exact (MK_COMB (@lem4452602 _106843 _106845) (@lem4452601 _106843 _106845 k P)). Qed.
Lemma lem4452605 {A : Type'} (t : Prop) : (term31 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4452606 {_106843 _106845 : Type'} (t : Prop) : (term32 _106843 _106845 t) = t.
Proof. exact (@lem4452605 (type1470 _106843 _106845) t). Qed.
Lemma lem4452607 {_106843 _106845 : Type'} : (term30 _106843 _106845) = True.
Proof. exact (@lem4452606 _106843 _106845 True). Qed.
Lemma lem4452608 {_106843 _106845 : Type'} (k : _106845 -> Prop) (P : type1470 _106843 _106845) : (term29 _106843 _106845 k P) = True.
Proof. exact (TRANS (@lem4452603 _106843 _106845 k P) (@lem4452607 _106843 _106845)). Qed.
Lemma lem4452609 {_106843 _106845 : Type'} (P : type1470 _106843 _106845) : (term33 _106843 _106845 P) = (term34 _106845).
Proof. exact (fun_ext (fun k : _106845 -> Prop => @lem4452608 _106843 _106845 k P)). Qed.
Lemma lem4452610 {_106845 : Type'} : (@all (_106845 -> Prop)) = (@all (_106845 -> Prop)).
Proof. exact (eq_refl (@all (_106845 -> Prop))). Qed.
Lemma lem4452611 {_106843 _106845 : Type'} (P : type1470 _106843 _106845) : (term35 _106843 _106845 P) = (term36 _106845).
Proof. exact (MK_COMB (@lem4452610 _106845) (@lem4452609 _106843 _106845 P)). Qed.
Lemma lem4452613 {A : Type'} (t : Prop) : (term31 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4452614 {_106845 : Type'} (t : Prop) : (term37 _106845 t) = t.
Proof. exact (@lem4452613 (_106845 -> Prop) t). Qed.
Lemma lem4452615 {_106845 : Type'} : (term36 _106845) = True.
Proof. exact (@lem4452614 _106845 True). Qed.
Lemma lem4452616 {_106843 _106845 : Type'} (P : type1470 _106843 _106845) : (term35 _106843 _106845 P) = True.
Proof. exact (TRANS (@lem4452611 _106843 _106845 P) (@lem4452615 _106845)). Qed.
Lemma lem4452617 {_106843 _106845 : Type'} : (term38 _106843 _106845) = (term28 _106843 _106845).
Proof. exact (fun_ext (fun P : type1470 _106843 _106845 => @lem4452616 _106843 _106845 P)). Qed.
Lemma lem4452618 {_106843 _106845 : Type'} : (@all (_106845 -> _106843 -> Prop)) = (@all (_106845 -> _106843 -> Prop)).
Proof. exact (eq_refl (@all (_106845 -> _106843 -> Prop))). Qed.
Lemma lem4452619 {_106843 _106845 : Type'} : (term39 _106843 _106845) = (term30 _106843 _106845).
Proof. exact (MK_COMB (@lem4452618 _106843 _106845) (@lem4452617 _106843 _106845)). Qed.
Lemma lem4452621 {A : Type'} (t : Prop) : (term31 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4452622 {_106843 _106845 : Type'} (t : Prop) : (term32 _106843 _106845 t) = t.
Proof. exact (@lem4452621 (type1470 _106843 _106845) t). Qed.
Lemma lem4452623 {_106843 _106845 : Type'} : (term30 _106843 _106845) = True.
Proof. exact (@lem4452622 _106843 _106845 True). Qed.
Lemma lem4452624 {_106843 _106845 : Type'} : (term39 _106843 _106845) = True.
Proof. exact (TRANS (@lem4452619 _106843 _106845) (@lem4452623 _106843 _106845)). Qed.
Lemma lem4452625 {_106843 _106845 : Type'} : True = (term39 _106843 _106845).
Proof. exact (SYM (@lem4452624 _106843 _106845)). Qed.
Lemma lem4452626 {_106843 _106845 : Type'} : term39 _106843 _106845.
Proof. exact (EQ_MP (@lem4452625 _106843 _106845) (@lem0)). Qed.
