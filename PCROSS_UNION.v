Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import PCROSS_UNION_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import EXTENSION_spec.
Require Import IN_UNION_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import PASTECART_IN_PCROSS_spec.
Require Import thm0_spec.
Require Import thm1831_spec.
Require Import thm1833_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1845_spec.
Require Import thm1855_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7660850_spec.
Require Import thm7662539_spec.
Lemma lem8037492 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) : term0 _141927 _141928 _141929 s.
Proof. exact (@lem8004229 _141927 _141928 _141929 s). Qed.
Lemma lem8037493 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) : (term0 _141927 _141928 _141929 s) = (term1 _141927 _141928 _141929 s).
Proof. exact (eq_refl (term0 _141927 _141928 _141929 s)). Qed.
Lemma lem8037494 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) : term1 _141927 _141928 _141929 s.
Proof. exact (EQ_MP (@lem8037493 _141927 _141928 _141929 s) (@lem8037492 _141927 _141928 _141929 s)). Qed.
Lemma lem8037495 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) (t : type24 _141927 _141929) : term2 _141927 _141928 _141929 s t.
Proof. exact (@lem8037494 _141927 _141928 _141929 s t). Qed.
Lemma lem8037496 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) (t : type24 _141927 _141929) : (term2 _141927 _141928 _141929 s t) = (term3 _141927 _141928 _141929 s t).
Proof. exact (eq_refl (term2 _141927 _141928 _141929 s t)). Qed.
Lemma lem8037497 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) (t : type24 _141927 _141929) : term3 _141927 _141928 _141929 s t.
Proof. exact (EQ_MP (@lem8037496 _141927 _141928 _141929 s t) (@lem8037495 _141927 _141928 _141929 s t)). Qed.
Lemma lem8037498 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) (t : type24 _141927 _141929) (x : cart _141927 _141928) : term4 _141927 _141928 _141929 s t x.
Proof. exact (@lem8037497 _141927 _141928 _141929 s t x). Qed.
Lemma lem8037499 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (t : type24 _141927 _141929) : (term4 _141927 _141928 _141929 s t x) = (term5 _141927 _141928 _141929 x s t).
Proof. exact (eq_refl (term4 _141927 _141928 _141929 s t x)). Qed.
Lemma lem8037500 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (t : type24 _141927 _141929) : term5 _141927 _141928 _141929 x s t.
Proof. exact (EQ_MP (@lem8037499 _141927 _141928 _141929 x s t) (@lem8037498 _141927 _141928 _141929 s t x)). Qed.
Lemma lem8037501 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (t : type24 _141927 _141929) (y : cart _141927 _141929) : term6 _141927 _141928 _141929 x s t y.
Proof. exact (@lem8037500 _141927 _141928 _141929 x s t y). Qed.
Lemma lem8037502 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (y : cart _141927 _141929) (t : type24 _141927 _141929) : (term6 _141927 _141928 _141929 x s t y) = ((term7 _141927 _141928 _141929 x y s t) = (term8 _141927 _141928 _141929 x s y t)).
Proof. exact (eq_refl (term6 _141927 _141928 _141929 x s t y)). Qed.
Lemma lem8037504 {A : Type'} (s : A -> Prop) : term9 A s.
Proof. exact (@lem3204949 A s). Qed.
Lemma lem8037505 {A : Type'} (s : A -> Prop) : (term9 A s) = (term10 A s).
Proof. exact (eq_refl (term9 A s)). Qed.
Lemma lem8037506 {A : Type'} (s : A -> Prop) : term10 A s.
Proof. exact (EQ_MP (@lem8037505 A s) (@lem8037504 A s)). Qed.
Lemma lem8037507 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term11 A s t.
Proof. exact (@lem8037506 A s t). Qed.
Lemma lem8037508 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term11 A s t) = (term12 A s t).
Proof. exact (eq_refl (term11 A s t)). Qed.
Lemma lem8037509 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term12 A s t.
Proof. exact (EQ_MP (@lem8037508 A s t) (@lem8037507 A s t)). Qed.
Lemma lem8037510 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : term13 A s t x.
Proof. exact (@lem8037509 A s t x). Qed.
Lemma lem8037511 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term13 A s t x) = ((term14 A x s t) = (term15 A s x t)).
Proof. exact (eq_refl (term13 A s t x)). Qed.
Lemma lem8037513 {A : Type'} (s : A -> Prop) : term16 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem8037514 {A : Type'} (s : A -> Prop) : (term16 A s) = (term17 A s).
Proof. exact (eq_refl (term16 A s)). Qed.
Lemma lem8037515 {A : Type'} (s : A -> Prop) : term17 A s.
Proof. exact (EQ_MP (@lem8037514 A s) (@lem8037513 A s)). Qed.
Lemma lem8037516 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term18 A s t.
Proof. exact (@lem8037515 A s t). Qed.
Lemma lem8037517 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term18 A s t) = ((s = t) = (term19 A s t)).
Proof. exact (eq_refl (term18 A s t)). Qed.
Lemma lem8037542 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term19 A s t).
Proof. exact (EQ_MP (@lem8037517 A s t) (@lem8037516 A s t)). Qed.
Lemma lem8037543 {_142544 _142545 _142546 : Type'} (s : type16 _142544 _142545 _142546) (t : type16 _142544 _142545 _142546) : (s = t) = (term20 _142544 _142545 _142546 s t).
Proof. exact (@lem8037542 (type2 _142544 _142545 _142546) s t). Qed.
Lemma lem8037544 {_142544 _142545 _142546 : Type'} (t : type24 _142544 _142546) (s : type24 _142544 _142545) (u : type24 _142544 _142546) : ((term21 _142544 _142545 _142546 s t u) = (term22 _142544 _142545 _142546 t s u)) = (term23 _142544 _142545 _142546 t s u).
Proof. exact (@lem8037543 _142544 _142545 _142546 (term21 _142544 _142545 _142546 s t u) (term22 _142544 _142545 _142546 t s u)). Qed.
Lemma lem8037550 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term24 _140454 _140455 _140456 P) = (term25 _140454 _140455 _140456 P).
Proof. exact (EQ_MP (@lem7660850 _140454 _140455 _140456 P) (@lem7662539 _140454 _140455 _140456 P)). Qed.
Lemma lem8037551 {_142544 _142545 _142546 : Type'} (P : type16 _142544 _142545 _142546) : (term24 _142544 _142545 _142546 P) = (term25 _142544 _142545 _142546 P).
Proof. exact (@lem8037550 _142544 _142545 _142546 P). Qed.
Lemma lem8037552 {_142544 _142545 _142546 : Type'} (t : type24 _142544 _142546) (s : type24 _142544 _142545) (u : type24 _142544 _142546) : (term26 _142544 _142545 _142546 t s u) = (term27 _142544 _142545 _142546 t s u).
Proof. exact (@lem8037551 _142544 _142545 _142546 (term28 _142544 _142545 _142546 t s u)). Qed.
Lemma lem8037553 {_142544 _142545 _142546 : Type'} (x : type2 _142544 _142545 _142546) (t : type24 _142544 _142546) (s : type24 _142544 _142545) (u : type24 _142544 _142546) : (term29 _142544 _142545 _142546 t s u x) = ((term30 _142544 _142545 _142546 x s t u) = (term31 _142544 _142545 _142546 x t s u)).
Proof. exact (eq_refl (term29 _142544 _142545 _142546 t s u x)). Qed.
Lemma lem8037554 {_142544 _142545 _142546 : Type'} (t : type24 _142544 _142546) (s : type24 _142544 _142545) (u : type24 _142544 _142546) : (term32 _142544 _142545 _142546 t s u) = (term28 _142544 _142545 _142546 t s u).
Proof. exact (fun_ext (fun x : type2 _142544 _142545 _142546 => @lem8037553 _142544 _142545 _142546 x t s u)). Qed.
Lemma lem8037555 {_142544 _142545 _142546 : Type'} : (@all (cart _142544 (finite_sum _142545 _142546))) = (@all (cart _142544 (finite_sum _142545 _142546))).
Proof. exact (eq_refl (@all (cart _142544 (finite_sum _142545 _142546)))). Qed.
Lemma lem8037556 {_142544 _142545 _142546 : Type'} (t : type24 _142544 _142546) (s : type24 _142544 _142545) (u : type24 _142544 _142546) : (term26 _142544 _142545 _142546 t s u) = (term23 _142544 _142545 _142546 t s u).
Proof. exact (MK_COMB (@lem8037555 _142544 _142545 _142546) (@lem8037554 _142544 _142545 _142546 t s u)). Qed.
Lemma lem8037557 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8037558 {_142544 _142545 _142546 : Type'} (t : type24 _142544 _142546) (s : type24 _142544 _142545) (u : type24 _142544 _142546) : (term33 _142544 _142545 _142546 t s u) = (term34 _142544 _142545 _142546 t s u).
Proof. exact (MK_COMB (@lem8037557) (@lem8037556 _142544 _142545 _142546 t s u)). Qed.
Lemma lem8037559 {_142544 _142545 _142546 : Type'} (x : cart _142544 _142545) (y : cart _142544 _142546) (t : type24 _142544 _142546) (s : type24 _142544 _142545) (u : type24 _142544 _142546) : (term35 _142544 _142545 _142546 t s u x y) = ((term36 _142544 _142545 _142546 x y s t u) = (term37 _142544 _142545 _142546 x y t s u)).
Proof. exact (eq_refl (term35 _142544 _142545 _142546 t s u x y)). Qed.
Lemma lem8037560 {_142544 _142545 _142546 : Type'} (x : cart _142544 _142545) (t : type24 _142544 _142546) (s : type24 _142544 _142545) (u : type24 _142544 _142546) : (term38 _142544 _142545 _142546 t s u x) = (term39 _142544 _142545 _142546 x t s u).
Proof. exact (fun_ext (fun y : cart _142544 _142546 => @lem8037559 _142544 _142545 _142546 x y t s u)). Qed.
Lemma lem8037561 {_142544 _142546 : Type'} : (@all (cart _142544 _142546)) = (@all (cart _142544 _142546)).
Proof. exact (eq_refl (@all (cart _142544 _142546))). Qed.
Lemma lem8037562 {_142544 _142545 _142546 : Type'} (x : cart _142544 _142545) (t : type24 _142544 _142546) (s : type24 _142544 _142545) (u : type24 _142544 _142546) : (term40 _142544 _142545 _142546 t s u x) = (term41 _142544 _142545 _142546 x t s u).
Proof. exact (MK_COMB (@lem8037561 _142544 _142546) (@lem8037560 _142544 _142545 _142546 x t s u)). Qed.
Lemma lem8037563 {_142544 _142545 _142546 : Type'} (t : type24 _142544 _142546) (s : type24 _142544 _142545) (u : type24 _142544 _142546) : (term42 _142544 _142545 _142546 t s u) = (term43 _142544 _142545 _142546 t s u).
Proof. exact (fun_ext (fun x : cart _142544 _142545 => @lem8037562 _142544 _142545 _142546 x t s u)). Qed.
Lemma lem8037564 {_142544 _142545 : Type'} : (@all (cart _142544 _142545)) = (@all (cart _142544 _142545)).
Proof. exact (eq_refl (@all (cart _142544 _142545))). Qed.
Lemma lem8037565 {_142544 _142545 _142546 : Type'} (t : type24 _142544 _142546) (s : type24 _142544 _142545) (u : type24 _142544 _142546) : (term27 _142544 _142545 _142546 t s u) = (term44 _142544 _142545 _142546 t s u).
Proof. exact (MK_COMB (@lem8037564 _142544 _142545) (@lem8037563 _142544 _142545 _142546 t s u)). Qed.
Lemma lem8037566 {_142544 _142545 _142546 : Type'} (t : type24 _142544 _142546) (s : type24 _142544 _142545) (u : type24 _142544 _142546) : ((term26 _142544 _142545 _142546 t s u) = (term27 _142544 _142545 _142546 t s u)) = ((term23 _142544 _142545 _142546 t s u) = (term44 _142544 _142545 _142546 t s u)).
Proof. exact (MK_COMB (@lem8037558 _142544 _142545 _142546 t s u) (@lem8037565 _142544 _142545 _142546 t s u)). Qed.
Lemma lem8037567 {_142544 _142545 _142546 : Type'} (t : type24 _142544 _142546) (s : type24 _142544 _142545) (u : type24 _142544 _142546) : (term23 _142544 _142545 _142546 t s u) = (term44 _142544 _142545 _142546 t s u).
Proof. exact (EQ_MP (@lem8037566 _142544 _142545 _142546 t s u) (@lem8037552 _142544 _142545 _142546 t s u)). Qed.
Lemma lem8037574 {_142544 _142545 _142546 : Type'} (t : type24 _142544 _142546) (s : type24 _142544 _142545) (u : type24 _142544 _142546) : ((term21 _142544 _142545 _142546 s t u) = (term22 _142544 _142545 _142546 t s u)) = (term44 _142544 _142545 _142546 t s u).
Proof. exact (TRANS (@lem8037544 _142544 _142545 _142546 t s u) (@lem8037567 _142544 _142545 _142546 t s u)). Qed.
Lemma lem8037586 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (y : cart _141927 _141929) (t : type24 _141927 _141929) : (term7 _141927 _141928 _141929 x y s t) = (term8 _141927 _141928 _141929 x s y t).
Proof. exact (EQ_MP (@lem8037502 _141927 _141928 _141929 x s y t) (@lem8037501 _141927 _141928 _141929 x s t y)). Qed.
Lemma lem8037587 {_142544 _142545 _142546 : Type'} (x : cart _142544 _142545) (s : type24 _142544 _142545) (y : cart _142544 _142546) (t : type24 _142544 _142546) : (term7 _142544 _142545 _142546 x y s t) = (term8 _142544 _142545 _142546 x s y t).
Proof. exact (@lem8037586 _142544 _142545 _142546 x s y t). Qed.
Lemma lem8037588 {_142544 _142545 _142546 : Type'} (x : cart _142544 _142545) (s : type24 _142544 _142545) (y : cart _142544 _142546) (t : type24 _142544 _142546) (u : type24 _142544 _142546) : (term36 _142544 _142545 _142546 x y s t u) = (term45 _142544 _142545 _142546 x s y t u).
Proof. exact (@lem8037587 _142544 _142545 _142546 x s y (@UNION (cart _142544 _142546) t u)). Qed.
Lemma lem8037592 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term14 A x s t) = (term15 A s x t).
Proof. exact (EQ_MP (@lem8037511 A s x t) (@lem8037510 A s t x)). Qed.
Lemma lem8037593 {_142544 _142546 : Type'} (s : type24 _142544 _142546) (x : cart _142544 _142546) (t : type24 _142544 _142546) : (term46 _142544 _142546 x s t) = (term47 _142544 _142546 s x t).
Proof. exact (@lem8037592 (cart _142544 _142546) s x t). Qed.
Lemma lem8037594 {_142544 _142546 : Type'} (t : type24 _142544 _142546) (y : cart _142544 _142546) (u : type24 _142544 _142546) : (term46 _142544 _142546 y t u) = (term47 _142544 _142546 t y u).
Proof. exact (@lem8037593 _142544 _142546 t y u). Qed.
Lemma lem8037597 {_142544 _142545 : Type'} (x : cart _142544 _142545) (s : type24 _142544 _142545) : (term48 _142544 _142545 x s) = (term48 _142544 _142545 x s).
Proof. exact (eq_refl (term48 _142544 _142545 x s)). Qed.
Lemma lem8037598 {_142544 _142545 _142546 : Type'} (x : cart _142544 _142545) (s : type24 _142544 _142545) (t : type24 _142544 _142546) (y : cart _142544 _142546) (u : type24 _142544 _142546) : (term45 _142544 _142545 _142546 x s y t u) = (term49 _142544 _142545 _142546 x s t y u).
Proof. exact (MK_COMB (@lem8037597 _142544 _142545 x s) (@lem8037594 _142544 _142546 t y u)). Qed.
Lemma lem8037601 {_142544 _142545 _142546 : Type'} (x : cart _142544 _142545) (s : type24 _142544 _142545) (t : type24 _142544 _142546) (y : cart _142544 _142546) (u : type24 _142544 _142546) : (term36 _142544 _142545 _142546 x y s t u) = (term49 _142544 _142545 _142546 x s t y u).
Proof. exact (TRANS (@lem8037588 _142544 _142545 _142546 x s y t u) (@lem8037598 _142544 _142545 _142546 x s t y u)). Qed.
Lemma lem8037602 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8037603 {_142544 _142545 _142546 : Type'} (x : cart _142544 _142545) (s : type24 _142544 _142545) (t : type24 _142544 _142546) (y : cart _142544 _142546) (u : type24 _142544 _142546) : (term50 _142544 _142545 _142546 x y s t u) = (term51 _142544 _142545 _142546 x s t y u).
Proof. exact (MK_COMB (@lem8037602) (@lem8037601 _142544 _142545 _142546 x s t y u)). Qed.
Lemma lem8037605 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term14 A x s t) = (term15 A s x t).
Proof. exact (EQ_MP (@lem8037511 A s x t) (@lem8037510 A s t x)). Qed.
Lemma lem8037606 {_142544 _142545 _142546 : Type'} (s : type16 _142544 _142545 _142546) (x : type2 _142544 _142545 _142546) (t : type16 _142544 _142545 _142546) : (term52 _142544 _142545 _142546 x s t) = (term53 _142544 _142545 _142546 s x t).
Proof. exact (@lem8037605 (type2 _142544 _142545 _142546) s x t). Qed.
Lemma lem8037607 {_142544 _142545 _142546 : Type'} (t : type24 _142544 _142546) (x : cart _142544 _142545) (y : cart _142544 _142546) (s : type24 _142544 _142545) (u : type24 _142544 _142546) : (term37 _142544 _142545 _142546 x y t s u) = (term54 _142544 _142545 _142546 t x y s u).
Proof. exact (@lem8037606 _142544 _142545 _142546 (@PCROSS _142544 _142545 _142546 s t) (@pastecart _142544 _142545 _142546 x y) (@PCROSS _142544 _142545 _142546 s u)). Qed.
Lemma lem8037611 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (y : cart _141927 _141929) (t : type24 _141927 _141929) : (term7 _141927 _141928 _141929 x y s t) = (term8 _141927 _141928 _141929 x s y t).
Proof. exact (EQ_MP (@lem8037502 _141927 _141928 _141929 x s y t) (@lem8037501 _141927 _141928 _141929 x s t y)). Qed.
Lemma lem8037612 {_142544 _142545 _142546 : Type'} (x : cart _142544 _142545) (s : type24 _142544 _142545) (y : cart _142544 _142546) (t : type24 _142544 _142546) : (term7 _142544 _142545 _142546 x y s t) = (term8 _142544 _142545 _142546 x s y t).
Proof. exact (@lem8037611 _142544 _142545 _142546 x s y t). Qed.
Lemma lem8037615 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8037616 {_142544 _142545 _142546 : Type'} (x : cart _142544 _142545) (s : type24 _142544 _142545) (y : cart _142544 _142546) (t : type24 _142544 _142546) : (term55 _142544 _142545 _142546 x y s t) = (term56 _142544 _142545 _142546 x s y t).
Proof. exact (MK_COMB (@lem8037615) (@lem8037612 _142544 _142545 _142546 x s y t)). Qed.
Lemma lem8037618 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (y : cart _141927 _141929) (t : type24 _141927 _141929) : (term7 _141927 _141928 _141929 x y s t) = (term8 _141927 _141928 _141929 x s y t).
Proof. exact (EQ_MP (@lem8037502 _141927 _141928 _141929 x s y t) (@lem8037501 _141927 _141928 _141929 x s t y)). Qed.
Lemma lem8037619 {_142544 _142545 _142546 : Type'} (x : cart _142544 _142545) (s : type24 _142544 _142545) (y : cart _142544 _142546) (t : type24 _142544 _142546) : (term7 _142544 _142545 _142546 x y s t) = (term8 _142544 _142545 _142546 x s y t).
Proof. exact (@lem8037618 _142544 _142545 _142546 x s y t). Qed.
Lemma lem8037620 {_142544 _142545 _142546 : Type'} (x : cart _142544 _142545) (s : type24 _142544 _142545) (y : cart _142544 _142546) (u : type24 _142544 _142546) : (term7 _142544 _142545 _142546 x y s u) = (term8 _142544 _142545 _142546 x s y u).
Proof. exact (@lem8037619 _142544 _142545 _142546 x s y u). Qed.
Lemma lem8037623 {_142544 _142545 _142546 : Type'} (t : type24 _142544 _142546) (x : cart _142544 _142545) (s : type24 _142544 _142545) (y : cart _142544 _142546) (u : type24 _142544 _142546) : (term54 _142544 _142545 _142546 t x y s u) = (term57 _142544 _142545 _142546 t x s y u).
Proof. exact (MK_COMB (@lem8037616 _142544 _142545 _142546 x s y t) (@lem8037620 _142544 _142545 _142546 x s y u)). Qed.
Lemma lem8037626 {_142544 _142545 _142546 : Type'} (t : type24 _142544 _142546) (x : cart _142544 _142545) (s : type24 _142544 _142545) (y : cart _142544 _142546) (u : type24 _142544 _142546) : (term37 _142544 _142545 _142546 x y t s u) = (term57 _142544 _142545 _142546 t x s y u).
Proof. exact (TRANS (@lem8037607 _142544 _142545 _142546 t x y s u) (@lem8037623 _142544 _142545 _142546 t x s y u)). Qed.
Lemma lem8037627 {_142544 _142545 _142546 : Type'} (t : type24 _142544 _142546) (x : cart _142544 _142545) (s : type24 _142544 _142545) (y : cart _142544 _142546) (u : type24 _142544 _142546) : ((term36 _142544 _142545 _142546 x y s t u) = (term37 _142544 _142545 _142546 x y t s u)) = ((term49 _142544 _142545 _142546 x s t y u) = (term57 _142544 _142545 _142546 t x s y u)).
Proof. exact (MK_COMB (@lem8037603 _142544 _142545 _142546 x s t y u) (@lem8037626 _142544 _142545 _142546 t x s y u)). Qed.
Lemma lem8037632 {_142544 _142545 _142546 : Type'} (t : type24 _142544 _142546) (x : cart _142544 _142545) (s : type24 _142544 _142545) (u : type24 _142544 _142546) : (term39 _142544 _142545 _142546 x t s u) = (term58 _142544 _142545 _142546 t x s u).
Proof. exact (fun_ext (fun y : cart _142544 _142546 => @lem8037627 _142544 _142545 _142546 t x s y u)). Qed.
Lemma lem8037633 {_142544 _142546 : Type'} : (@all (cart _142544 _142546)) = (@all (cart _142544 _142546)).
Proof. exact (eq_refl (@all (cart _142544 _142546))). Qed.
Lemma lem8037634 {_142544 _142545 _142546 : Type'} (t : type24 _142544 _142546) (x : cart _142544 _142545) (s : type24 _142544 _142545) (u : type24 _142544 _142546) : (term41 _142544 _142545 _142546 x t s u) = (term59 _142544 _142545 _142546 t x s u).
Proof. exact (MK_COMB (@lem8037633 _142544 _142546) (@lem8037632 _142544 _142545 _142546 t x s u)). Qed.
Lemma lem8037641 {_142544 _142545 _142546 : Type'} (t : type24 _142544 _142546) (s : type24 _142544 _142545) (u : type24 _142544 _142546) : (term43 _142544 _142545 _142546 t s u) = (term60 _142544 _142545 _142546 t s u).
Proof. exact (fun_ext (fun x : cart _142544 _142545 => @lem8037634 _142544 _142545 _142546 t x s u)). Qed.
Lemma lem8037642 {_142544 _142545 : Type'} : (@all (cart _142544 _142545)) = (@all (cart _142544 _142545)).
Proof. exact (eq_refl (@all (cart _142544 _142545))). Qed.
Lemma lem8037643 {_142544 _142545 _142546 : Type'} (t : type24 _142544 _142546) (s : type24 _142544 _142545) (u : type24 _142544 _142546) : (term44 _142544 _142545 _142546 t s u) = (term61 _142544 _142545 _142546 t s u).
Proof. exact (MK_COMB (@lem8037642 _142544 _142545) (@lem8037641 _142544 _142545 _142546 t s u)). Qed.
Lemma lem8037650 {_142544 _142545 _142546 : Type'} (t : type24 _142544 _142546) (s : type24 _142544 _142545) (u : type24 _142544 _142546) : ((term21 _142544 _142545 _142546 s t u) = (term22 _142544 _142545 _142546 t s u)) = (term61 _142544 _142545 _142546 t s u).
Proof. exact (TRANS (@lem8037574 _142544 _142545 _142546 t s u) (@lem8037643 _142544 _142545 _142546 t s u)). Qed.
Lemma lem8037651 {_142544 _142545 _142546 : Type'} (t : type24 _142544 _142546) (s : type24 _142544 _142545) : (term62 _142544 _142545 _142546 t s) = (term63 _142544 _142545 _142546 t s).
Proof. exact (fun_ext (fun u : type24 _142544 _142546 => @lem8037650 _142544 _142545 _142546 t s u)). Qed.
Lemma lem8037652 {_142544 _142546 : Type'} : (@all ((cart _142544 _142546) -> Prop)) = (@all ((cart _142544 _142546) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142544 _142546) -> Prop))). Qed.
Lemma lem8037653 {_142544 _142545 _142546 : Type'} (t : type24 _142544 _142546) (s : type24 _142544 _142545) : (term64 _142544 _142545 _142546 t s) = (term65 _142544 _142545 _142546 t s).
Proof. exact (MK_COMB (@lem8037652 _142544 _142546) (@lem8037651 _142544 _142545 _142546 t s)). Qed.
Lemma lem8037660 {_142544 _142545 _142546 : Type'} (s : type24 _142544 _142545) : (term66 _142544 _142545 _142546 s) = (term67 _142544 _142545 _142546 s).
Proof. exact (fun_ext (fun t : type24 _142544 _142546 => @lem8037653 _142544 _142545 _142546 t s)). Qed.
Lemma lem8037661 {_142544 _142546 : Type'} : (@all ((cart _142544 _142546) -> Prop)) = (@all ((cart _142544 _142546) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142544 _142546) -> Prop))). Qed.
Lemma lem8037662 {_142544 _142545 _142546 : Type'} (s : type24 _142544 _142545) : (term68 _142544 _142545 _142546 s) = (term69 _142544 _142545 _142546 s).
Proof. exact (MK_COMB (@lem8037661 _142544 _142546) (@lem8037660 _142544 _142545 _142546 s)). Qed.
Lemma lem8037669 {_142544 _142545 _142546 : Type'} : (term70 _142544 _142545 _142546) = (term71 _142544 _142545 _142546).
Proof. exact (fun_ext (fun s : type24 _142544 _142545 => @lem8037662 _142544 _142545 _142546 s)). Qed.
Lemma lem8037670 {_142544 _142545 : Type'} : (@all ((cart _142544 _142545) -> Prop)) = (@all ((cart _142544 _142545) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142544 _142545) -> Prop))). Qed.
Lemma lem8037671 {_142544 _142545 _142546 : Type'} : (term72 _142544 _142545 _142546) = (term73 _142544 _142545 _142546).
Proof. exact (MK_COMB (@lem8037670 _142544 _142545) (@lem8037669 _142544 _142545 _142546)). Qed.
Lemma lem8037678 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8037679 {_142544 _142545 _142546 : Type'} : (term74 _142544 _142545 _142546) = (term75 _142544 _142545 _142546).
Proof. exact (MK_COMB (@lem8037678) (@lem8037671 _142544 _142545 _142546)). Qed.
Lemma lem8037701 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term19 A s t).
Proof. exact (EQ_MP (@lem8037517 A s t) (@lem8037516 A s t)). Qed.
Lemma lem8037702 {_142580 _142581 _142582 : Type'} (s : type16 _142580 _142581 _142582) (t : type16 _142580 _142581 _142582) : (s = t) = (term20 _142580 _142581 _142582 s t).
Proof. exact (@lem8037701 (type2 _142580 _142581 _142582) s t). Qed.
Lemma lem8037703 {_142580 _142581 _142582 : Type'} (s : type24 _142580 _142581) (t : type24 _142580 _142581) (u : type24 _142580 _142582) : ((term76 _142580 _142581 _142582 s t u) = (term77 _142580 _142581 _142582 s t u)) = (term78 _142580 _142581 _142582 s t u).
Proof. exact (@lem8037702 _142580 _142581 _142582 (term76 _142580 _142581 _142582 s t u) (term77 _142580 _142581 _142582 s t u)). Qed.
Lemma lem8037709 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term24 _140454 _140455 _140456 P) = (term25 _140454 _140455 _140456 P).
Proof. exact (EQ_MP (@lem7660850 _140454 _140455 _140456 P) (@lem7662539 _140454 _140455 _140456 P)). Qed.
Lemma lem8037710 {_142580 _142581 _142582 : Type'} (P : type16 _142580 _142581 _142582) : (term24 _142580 _142581 _142582 P) = (term25 _142580 _142581 _142582 P).
Proof. exact (@lem8037709 _142580 _142581 _142582 P). Qed.
Lemma lem8037711 {_142580 _142581 _142582 : Type'} (s : type24 _142580 _142581) (t : type24 _142580 _142581) (u : type24 _142580 _142582) : (term79 _142580 _142581 _142582 s t u) = (term80 _142580 _142581 _142582 s t u).
Proof. exact (@lem8037710 _142580 _142581 _142582 (term81 _142580 _142581 _142582 s t u)). Qed.
Lemma lem8037712 {_142580 _142581 _142582 : Type'} (x : type2 _142580 _142581 _142582) (s : type24 _142580 _142581) (t : type24 _142580 _142581) (u : type24 _142580 _142582) : (term82 _142580 _142581 _142582 s t u x) = ((term83 _142580 _142581 _142582 x s t u) = (term84 _142580 _142581 _142582 x s t u)).
Proof. exact (eq_refl (term82 _142580 _142581 _142582 s t u x)). Qed.
Lemma lem8037713 {_142580 _142581 _142582 : Type'} (s : type24 _142580 _142581) (t : type24 _142580 _142581) (u : type24 _142580 _142582) : (term85 _142580 _142581 _142582 s t u) = (term81 _142580 _142581 _142582 s t u).
Proof. exact (fun_ext (fun x : type2 _142580 _142581 _142582 => @lem8037712 _142580 _142581 _142582 x s t u)). Qed.
Lemma lem8037714 {_142580 _142581 _142582 : Type'} : (@all (cart _142580 (finite_sum _142581 _142582))) = (@all (cart _142580 (finite_sum _142581 _142582))).
Proof. exact (eq_refl (@all (cart _142580 (finite_sum _142581 _142582)))). Qed.
Lemma lem8037715 {_142580 _142581 _142582 : Type'} (s : type24 _142580 _142581) (t : type24 _142580 _142581) (u : type24 _142580 _142582) : (term79 _142580 _142581 _142582 s t u) = (term78 _142580 _142581 _142582 s t u).
Proof. exact (MK_COMB (@lem8037714 _142580 _142581 _142582) (@lem8037713 _142580 _142581 _142582 s t u)). Qed.
Lemma lem8037716 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8037717 {_142580 _142581 _142582 : Type'} (s : type24 _142580 _142581) (t : type24 _142580 _142581) (u : type24 _142580 _142582) : (term86 _142580 _142581 _142582 s t u) = (term87 _142580 _142581 _142582 s t u).
Proof. exact (MK_COMB (@lem8037716) (@lem8037715 _142580 _142581 _142582 s t u)). Qed.
Lemma lem8037718 {_142580 _142581 _142582 : Type'} (x : cart _142580 _142581) (y : cart _142580 _142582) (s : type24 _142580 _142581) (t : type24 _142580 _142581) (u : type24 _142580 _142582) : (term88 _142580 _142581 _142582 s t u x y) = ((term89 _142580 _142581 _142582 x y s t u) = (term90 _142580 _142581 _142582 x y s t u)).
Proof. exact (eq_refl (term88 _142580 _142581 _142582 s t u x y)). Qed.
Lemma lem8037719 {_142580 _142581 _142582 : Type'} (x : cart _142580 _142581) (s : type24 _142580 _142581) (t : type24 _142580 _142581) (u : type24 _142580 _142582) : (term91 _142580 _142581 _142582 s t u x) = (term92 _142580 _142581 _142582 x s t u).
Proof. exact (fun_ext (fun y : cart _142580 _142582 => @lem8037718 _142580 _142581 _142582 x y s t u)). Qed.
Lemma lem8037720 {_142580 _142582 : Type'} : (@all (cart _142580 _142582)) = (@all (cart _142580 _142582)).
Proof. exact (eq_refl (@all (cart _142580 _142582))). Qed.
Lemma lem8037721 {_142580 _142581 _142582 : Type'} (x : cart _142580 _142581) (s : type24 _142580 _142581) (t : type24 _142580 _142581) (u : type24 _142580 _142582) : (term93 _142580 _142581 _142582 s t u x) = (term94 _142580 _142581 _142582 x s t u).
Proof. exact (MK_COMB (@lem8037720 _142580 _142582) (@lem8037719 _142580 _142581 _142582 x s t u)). Qed.
Lemma lem8037722 {_142580 _142581 _142582 : Type'} (s : type24 _142580 _142581) (t : type24 _142580 _142581) (u : type24 _142580 _142582) : (term95 _142580 _142581 _142582 s t u) = (term96 _142580 _142581 _142582 s t u).
Proof. exact (fun_ext (fun x : cart _142580 _142581 => @lem8037721 _142580 _142581 _142582 x s t u)). Qed.
Lemma lem8037723 {_142580 _142581 : Type'} : (@all (cart _142580 _142581)) = (@all (cart _142580 _142581)).
Proof. exact (eq_refl (@all (cart _142580 _142581))). Qed.
Lemma lem8037724 {_142580 _142581 _142582 : Type'} (s : type24 _142580 _142581) (t : type24 _142580 _142581) (u : type24 _142580 _142582) : (term80 _142580 _142581 _142582 s t u) = (term97 _142580 _142581 _142582 s t u).
Proof. exact (MK_COMB (@lem8037723 _142580 _142581) (@lem8037722 _142580 _142581 _142582 s t u)). Qed.
Lemma lem8037725 {_142580 _142581 _142582 : Type'} (s : type24 _142580 _142581) (t : type24 _142580 _142581) (u : type24 _142580 _142582) : ((term79 _142580 _142581 _142582 s t u) = (term80 _142580 _142581 _142582 s t u)) = ((term78 _142580 _142581 _142582 s t u) = (term97 _142580 _142581 _142582 s t u)).
Proof. exact (MK_COMB (@lem8037717 _142580 _142581 _142582 s t u) (@lem8037724 _142580 _142581 _142582 s t u)). Qed.
Lemma lem8037726 {_142580 _142581 _142582 : Type'} (s : type24 _142580 _142581) (t : type24 _142580 _142581) (u : type24 _142580 _142582) : (term78 _142580 _142581 _142582 s t u) = (term97 _142580 _142581 _142582 s t u).
Proof. exact (EQ_MP (@lem8037725 _142580 _142581 _142582 s t u) (@lem8037711 _142580 _142581 _142582 s t u)). Qed.
Lemma lem8037733 {_142580 _142581 _142582 : Type'} (s : type24 _142580 _142581) (t : type24 _142580 _142581) (u : type24 _142580 _142582) : ((term76 _142580 _142581 _142582 s t u) = (term77 _142580 _142581 _142582 s t u)) = (term97 _142580 _142581 _142582 s t u).
Proof. exact (TRANS (@lem8037703 _142580 _142581 _142582 s t u) (@lem8037726 _142580 _142581 _142582 s t u)). Qed.
Lemma lem8037745 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (y : cart _141927 _141929) (t : type24 _141927 _141929) : (term7 _141927 _141928 _141929 x y s t) = (term8 _141927 _141928 _141929 x s y t).
Proof. exact (EQ_MP (@lem8037502 _141927 _141928 _141929 x s y t) (@lem8037501 _141927 _141928 _141929 x s t y)). Qed.
Lemma lem8037746 {_142580 _142581 _142582 : Type'} (x : cart _142580 _142581) (s : type24 _142580 _142581) (y : cart _142580 _142582) (t : type24 _142580 _142582) : (term7 _142580 _142581 _142582 x y s t) = (term8 _142580 _142581 _142582 x s y t).
Proof. exact (@lem8037745 _142580 _142581 _142582 x s y t). Qed.
Lemma lem8037747 {_142580 _142581 _142582 : Type'} (x : cart _142580 _142581) (s : type24 _142580 _142581) (t : type24 _142580 _142581) (y : cart _142580 _142582) (u : type24 _142580 _142582) : (term89 _142580 _142581 _142582 x y s t u) = (term98 _142580 _142581 _142582 x s t y u).
Proof. exact (@lem8037746 _142580 _142581 _142582 x (@UNION (cart _142580 _142581) s t) y u). Qed.
Lemma lem8037751 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term14 A x s t) = (term15 A s x t).
Proof. exact (EQ_MP (@lem8037511 A s x t) (@lem8037510 A s t x)). Qed.
Lemma lem8037752 {_142580 _142581 : Type'} (s : type24 _142580 _142581) (x : cart _142580 _142581) (t : type24 _142580 _142581) : (term46 _142580 _142581 x s t) = (term47 _142580 _142581 s x t).
Proof. exact (@lem8037751 (cart _142580 _142581) s x t). Qed.
Lemma lem8037755 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8037756 {_142580 _142581 : Type'} (s : type24 _142580 _142581) (x : cart _142580 _142581) (t : type24 _142580 _142581) : (term99 _142580 _142581 x s t) = (term100 _142580 _142581 s x t).
Proof. exact (MK_COMB (@lem8037755) (@lem8037752 _142580 _142581 s x t)). Qed.
Lemma lem8037757 {_142580 _142582 : Type'} (y : cart _142580 _142582) (u : type24 _142580 _142582) : (@IN (cart _142580 _142582) y u) = (@IN (cart _142580 _142582) y u).
Proof. exact (eq_refl (@IN (cart _142580 _142582) y u)). Qed.
Lemma lem8037758 {_142580 _142581 _142582 : Type'} (s : type24 _142580 _142581) (x : cart _142580 _142581) (t : type24 _142580 _142581) (y : cart _142580 _142582) (u : type24 _142580 _142582) : (term98 _142580 _142581 _142582 x s t y u) = (term101 _142580 _142581 _142582 s x t y u).
Proof. exact (MK_COMB (@lem8037756 _142580 _142581 s x t) (@lem8037757 _142580 _142582 y u)). Qed.
Lemma lem8037761 {_142580 _142581 _142582 : Type'} (s : type24 _142580 _142581) (x : cart _142580 _142581) (t : type24 _142580 _142581) (y : cart _142580 _142582) (u : type24 _142580 _142582) : (term89 _142580 _142581 _142582 x y s t u) = (term101 _142580 _142581 _142582 s x t y u).
Proof. exact (TRANS (@lem8037747 _142580 _142581 _142582 x s t y u) (@lem8037758 _142580 _142581 _142582 s x t y u)). Qed.
Lemma lem8037762 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8037763 {_142580 _142581 _142582 : Type'} (s : type24 _142580 _142581) (x : cart _142580 _142581) (t : type24 _142580 _142581) (y : cart _142580 _142582) (u : type24 _142580 _142582) : (term102 _142580 _142581 _142582 x y s t u) = (term103 _142580 _142581 _142582 s x t y u).
Proof. exact (MK_COMB (@lem8037762) (@lem8037761 _142580 _142581 _142582 s x t y u)). Qed.
Lemma lem8037765 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term14 A x s t) = (term15 A s x t).
Proof. exact (EQ_MP (@lem8037511 A s x t) (@lem8037510 A s t x)). Qed.
Lemma lem8037766 {_142580 _142581 _142582 : Type'} (s : type16 _142580 _142581 _142582) (x : type2 _142580 _142581 _142582) (t : type16 _142580 _142581 _142582) : (term52 _142580 _142581 _142582 x s t) = (term53 _142580 _142581 _142582 s x t).
Proof. exact (@lem8037765 (type2 _142580 _142581 _142582) s x t). Qed.
Lemma lem8037767 {_142580 _142581 _142582 : Type'} (s : type24 _142580 _142581) (x : cart _142580 _142581) (y : cart _142580 _142582) (t : type24 _142580 _142581) (u : type24 _142580 _142582) : (term90 _142580 _142581 _142582 x y s t u) = (term104 _142580 _142581 _142582 s x y t u).
Proof. exact (@lem8037766 _142580 _142581 _142582 (@PCROSS _142580 _142581 _142582 s u) (@pastecart _142580 _142581 _142582 x y) (@PCROSS _142580 _142581 _142582 t u)). Qed.
Lemma lem8037771 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (y : cart _141927 _141929) (t : type24 _141927 _141929) : (term7 _141927 _141928 _141929 x y s t) = (term8 _141927 _141928 _141929 x s y t).
Proof. exact (EQ_MP (@lem8037502 _141927 _141928 _141929 x s y t) (@lem8037501 _141927 _141928 _141929 x s t y)). Qed.
Lemma lem8037772 {_142580 _142581 _142582 : Type'} (x : cart _142580 _142581) (s : type24 _142580 _142581) (y : cart _142580 _142582) (t : type24 _142580 _142582) : (term7 _142580 _142581 _142582 x y s t) = (term8 _142580 _142581 _142582 x s y t).
Proof. exact (@lem8037771 _142580 _142581 _142582 x s y t). Qed.
Lemma lem8037773 {_142580 _142581 _142582 : Type'} (x : cart _142580 _142581) (s : type24 _142580 _142581) (y : cart _142580 _142582) (u : type24 _142580 _142582) : (term7 _142580 _142581 _142582 x y s u) = (term8 _142580 _142581 _142582 x s y u).
Proof. exact (@lem8037772 _142580 _142581 _142582 x s y u). Qed.
Lemma lem8037776 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8037777 {_142580 _142581 _142582 : Type'} (x : cart _142580 _142581) (s : type24 _142580 _142581) (y : cart _142580 _142582) (u : type24 _142580 _142582) : (term55 _142580 _142581 _142582 x y s u) = (term56 _142580 _142581 _142582 x s y u).
Proof. exact (MK_COMB (@lem8037776) (@lem8037773 _142580 _142581 _142582 x s y u)). Qed.
Lemma lem8037779 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (y : cart _141927 _141929) (t : type24 _141927 _141929) : (term7 _141927 _141928 _141929 x y s t) = (term8 _141927 _141928 _141929 x s y t).
Proof. exact (EQ_MP (@lem8037502 _141927 _141928 _141929 x s y t) (@lem8037501 _141927 _141928 _141929 x s t y)). Qed.
Lemma lem8037780 {_142580 _142581 _142582 : Type'} (x : cart _142580 _142581) (s : type24 _142580 _142581) (y : cart _142580 _142582) (t : type24 _142580 _142582) : (term7 _142580 _142581 _142582 x y s t) = (term8 _142580 _142581 _142582 x s y t).
Proof. exact (@lem8037779 _142580 _142581 _142582 x s y t). Qed.
Lemma lem8037781 {_142580 _142581 _142582 : Type'} (x : cart _142580 _142581) (t : type24 _142580 _142581) (y : cart _142580 _142582) (u : type24 _142580 _142582) : (term7 _142580 _142581 _142582 x y t u) = (term8 _142580 _142581 _142582 x t y u).
Proof. exact (@lem8037780 _142580 _142581 _142582 x t y u). Qed.
Lemma lem8037784 {_142580 _142581 _142582 : Type'} (s : type24 _142580 _142581) (x : cart _142580 _142581) (t : type24 _142580 _142581) (y : cart _142580 _142582) (u : type24 _142580 _142582) : (term104 _142580 _142581 _142582 s x y t u) = (term105 _142580 _142581 _142582 s x t y u).
Proof. exact (MK_COMB (@lem8037777 _142580 _142581 _142582 x s y u) (@lem8037781 _142580 _142581 _142582 x t y u)). Qed.
Lemma lem8037787 {_142580 _142581 _142582 : Type'} (s : type24 _142580 _142581) (x : cart _142580 _142581) (t : type24 _142580 _142581) (y : cart _142580 _142582) (u : type24 _142580 _142582) : (term90 _142580 _142581 _142582 x y s t u) = (term105 _142580 _142581 _142582 s x t y u).
Proof. exact (TRANS (@lem8037767 _142580 _142581 _142582 s x y t u) (@lem8037784 _142580 _142581 _142582 s x t y u)). Qed.
Lemma lem8037788 {_142580 _142581 _142582 : Type'} (s : type24 _142580 _142581) (x : cart _142580 _142581) (t : type24 _142580 _142581) (y : cart _142580 _142582) (u : type24 _142580 _142582) : ((term89 _142580 _142581 _142582 x y s t u) = (term90 _142580 _142581 _142582 x y s t u)) = ((term101 _142580 _142581 _142582 s x t y u) = (term105 _142580 _142581 _142582 s x t y u)).
Proof. exact (MK_COMB (@lem8037763 _142580 _142581 _142582 s x t y u) (@lem8037787 _142580 _142581 _142582 s x t y u)). Qed.
Lemma lem8037793 {_142580 _142581 _142582 : Type'} (s : type24 _142580 _142581) (x : cart _142580 _142581) (t : type24 _142580 _142581) (u : type24 _142580 _142582) : (term92 _142580 _142581 _142582 x s t u) = (term106 _142580 _142581 _142582 s x t u).
Proof. exact (fun_ext (fun y : cart _142580 _142582 => @lem8037788 _142580 _142581 _142582 s x t y u)). Qed.
Lemma lem8037794 {_142580 _142582 : Type'} : (@all (cart _142580 _142582)) = (@all (cart _142580 _142582)).
Proof. exact (eq_refl (@all (cart _142580 _142582))). Qed.
Lemma lem8037795 {_142580 _142581 _142582 : Type'} (s : type24 _142580 _142581) (x : cart _142580 _142581) (t : type24 _142580 _142581) (u : type24 _142580 _142582) : (term94 _142580 _142581 _142582 x s t u) = (term107 _142580 _142581 _142582 s x t u).
Proof. exact (MK_COMB (@lem8037794 _142580 _142582) (@lem8037793 _142580 _142581 _142582 s x t u)). Qed.
Lemma lem8037802 {_142580 _142581 _142582 : Type'} (s : type24 _142580 _142581) (t : type24 _142580 _142581) (u : type24 _142580 _142582) : (term96 _142580 _142581 _142582 s t u) = (term108 _142580 _142581 _142582 s t u).
Proof. exact (fun_ext (fun x : cart _142580 _142581 => @lem8037795 _142580 _142581 _142582 s x t u)). Qed.
Lemma lem8037803 {_142580 _142581 : Type'} : (@all (cart _142580 _142581)) = (@all (cart _142580 _142581)).
Proof. exact (eq_refl (@all (cart _142580 _142581))). Qed.
Lemma lem8037804 {_142580 _142581 _142582 : Type'} (s : type24 _142580 _142581) (t : type24 _142580 _142581) (u : type24 _142580 _142582) : (term97 _142580 _142581 _142582 s t u) = (term109 _142580 _142581 _142582 s t u).
Proof. exact (MK_COMB (@lem8037803 _142580 _142581) (@lem8037802 _142580 _142581 _142582 s t u)). Qed.
Lemma lem8037811 {_142580 _142581 _142582 : Type'} (s : type24 _142580 _142581) (t : type24 _142580 _142581) (u : type24 _142580 _142582) : ((term76 _142580 _142581 _142582 s t u) = (term77 _142580 _142581 _142582 s t u)) = (term109 _142580 _142581 _142582 s t u).
Proof. exact (TRANS (@lem8037733 _142580 _142581 _142582 s t u) (@lem8037804 _142580 _142581 _142582 s t u)). Qed.
Lemma lem8037812 {_142580 _142581 _142582 : Type'} (s : type24 _142580 _142581) (t : type24 _142580 _142581) : (term110 _142580 _142581 _142582 s t) = (term111 _142580 _142581 _142582 s t).
Proof. exact (fun_ext (fun u : type24 _142580 _142582 => @lem8037811 _142580 _142581 _142582 s t u)). Qed.
Lemma lem8037813 {_142580 _142582 : Type'} : (@all ((cart _142580 _142582) -> Prop)) = (@all ((cart _142580 _142582) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142580 _142582) -> Prop))). Qed.
Lemma lem8037814 {_142580 _142581 _142582 : Type'} (s : type24 _142580 _142581) (t : type24 _142580 _142581) : (term112 _142580 _142581 _142582 s t) = (term113 _142580 _142581 _142582 s t).
Proof. exact (MK_COMB (@lem8037813 _142580 _142582) (@lem8037812 _142580 _142581 _142582 s t)). Qed.
Lemma lem8037821 {_142580 _142581 _142582 : Type'} (s : type24 _142580 _142581) : (term114 _142580 _142581 _142582 s) = (term115 _142580 _142581 _142582 s).
Proof. exact (fun_ext (fun t : type24 _142580 _142581 => @lem8037814 _142580 _142581 _142582 s t)). Qed.
Lemma lem8037822 {_142580 _142581 : Type'} : (@all ((cart _142580 _142581) -> Prop)) = (@all ((cart _142580 _142581) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142580 _142581) -> Prop))). Qed.
Lemma lem8037823 {_142580 _142581 _142582 : Type'} (s : type24 _142580 _142581) : (term116 _142580 _142581 _142582 s) = (term117 _142580 _142581 _142582 s).
Proof. exact (MK_COMB (@lem8037822 _142580 _142581) (@lem8037821 _142580 _142581 _142582 s)). Qed.
Lemma lem8037830 {_142580 _142581 _142582 : Type'} : (term118 _142580 _142581 _142582) = (term119 _142580 _142581 _142582).
Proof. exact (fun_ext (fun s : type24 _142580 _142581 => @lem8037823 _142580 _142581 _142582 s)). Qed.
Lemma lem8037831 {_142580 _142581 : Type'} : (@all ((cart _142580 _142581) -> Prop)) = (@all ((cart _142580 _142581) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142580 _142581) -> Prop))). Qed.
Lemma lem8037832 {_142580 _142581 _142582 : Type'} : (term120 _142580 _142581 _142582) = (term121 _142580 _142581 _142582).
Proof. exact (MK_COMB (@lem8037831 _142580 _142581) (@lem8037830 _142580 _142581 _142582)). Qed.
Lemma lem8037839 {_142544 _142545 _142546 _142580 _142581 _142582 : Type'} : (term122 _142544 _142545 _142546 _142580 _142581 _142582) = (term123 _142544 _142545 _142546 _142580 _142581 _142582).
Proof. exact (MK_COMB (@lem8037679 _142544 _142545 _142546) (@lem8037832 _142580 _142581 _142582)). Qed.
Lemma lem8037842 {_142544 _142545 _142546 _142580 _142581 _142582 : Type'} : (term123 _142544 _142545 _142546 _142580 _142581 _142582) = (term122 _142544 _142545 _142546 _142580 _142581 _142582).
Proof. exact (SYM (@lem8037839 _142544 _142545 _142546 _142580 _142581 _142582)). Qed.
Lemma lem8037857 {_142544 _142545 : Type'} (x : cart _142544 _142545) (s : type24 _142544 _142545) : term124 _142544 _142545 x s.
Proof. exact (@lem9851 (@IN (cart _142544 _142545) x s)). Qed.
Lemma lem8037858 {_142544 _142545 : Type'} (x : cart _142544 _142545) (s : type24 _142544 _142545) : (term124 _142544 _142545 x s) = (term125 _142544 _142545 x s).
Proof. exact (eq_refl (term124 _142544 _142545 x s)). Qed.
Lemma lem8037859 {_142544 _142545 : Type'} (x : cart _142544 _142545) (s : type24 _142544 _142545) : term125 _142544 _142545 x s.
Proof. exact (EQ_MP (@lem8037858 _142544 _142545 x s) (@lem8037857 _142544 _142545 x s)). Qed.
Lemma lem8037860 {_142544 _142545 : Type'} (x : cart _142544 _142545) (s : type24 _142544 _142545) (h1 : (@IN (cart _142544 _142545) x s) = True) : (@IN (cart _142544 _142545) x s) = True.
Proof. exact (h1). Qed.
Lemma lem8037861 {_142544 _142545 : Type'} (x : cart _142544 _142545) (s : type24 _142544 _142545) (h1 : (@IN (cart _142544 _142545) x s) = False) : (@IN (cart _142544 _142545) x s) = False.
Proof. exact (h1). Qed.
Lemma lem8037876 {_142544 _142546 : Type'} (t : type24 _142544 _142546) (y : cart _142544 _142546) (u : type24 _142544 _142546) : (term126 _142544 _142546 t y u) = (term126 _142544 _142546 t y u).
Proof. exact (eq_refl (term126 _142544 _142546 t y u)). Qed.
Lemma lem8037877 {_142544 _142545 _142546 : Type'} (t : type24 _142544 _142546) (y : cart _142544 _142546) (u : type24 _142544 _142546) (x : cart _142544 _142545) (s : type24 _142544 _142545) (h1 : (@IN (cart _142544 _142545) x s) = True) : (term127 _142544 _142545 _142546 t y u x s) = (term128 _142544 _142546 t y u).
Proof. exact (MK_COMB (@lem8037876 _142544 _142546 t y u) (@lem8037860 _142544 _142545 x s h1)). Qed.
Lemma lem8037878 {_142544 _142546 : Type'} (t : type24 _142544 _142546) (y : cart _142544 _142546) (u : type24 _142544 _142546) : (term128 _142544 _142546 t y u) = ((term129 _142544 _142546 t y u) = (term130 _142544 _142546 t y u)).
Proof. exact (eq_refl (term128 _142544 _142546 t y u)). Qed.
Lemma lem8037879 {_142544 _142545 _142546 : Type'} (t : type24 _142544 _142546) (y : cart _142544 _142546) (u : type24 _142544 _142546) (x : cart _142544 _142545) (s : type24 _142544 _142545) : (term131 _142544 _142545 _142546 t y u x s) = (term131 _142544 _142545 _142546 t y u x s).
Proof. exact (eq_refl (term131 _142544 _142545 _142546 t y u x s)). Qed.
Lemma lem8037880 {_142544 _142545 _142546 : Type'} (x : cart _142544 _142545) (s : type24 _142544 _142545) (t : type24 _142544 _142546) (y : cart _142544 _142546) (u : type24 _142544 _142546) : ((term127 _142544 _142545 _142546 t y u x s) = (term128 _142544 _142546 t y u)) = ((term127 _142544 _142545 _142546 t y u x s) = ((term129 _142544 _142546 t y u) = (term130 _142544 _142546 t y u))).
Proof. exact (MK_COMB (@lem8037879 _142544 _142545 _142546 t y u x s) (@lem8037878 _142544 _142546 t y u)). Qed.
Lemma lem8037881 {_142544 _142545 _142546 : Type'} (t : type24 _142544 _142546) (x : cart _142544 _142545) (s : type24 _142544 _142545) (y : cart _142544 _142546) (u : type24 _142544 _142546) : (term127 _142544 _142545 _142546 t y u x s) = ((term49 _142544 _142545 _142546 x s t y u) = (term57 _142544 _142545 _142546 t x s y u)).
Proof. exact (eq_refl (term127 _142544 _142545 _142546 t y u x s)). Qed.
Lemma lem8037882 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8037883 {_142544 _142545 _142546 : Type'} (t : type24 _142544 _142546) (x : cart _142544 _142545) (s : type24 _142544 _142545) (y : cart _142544 _142546) (u : type24 _142544 _142546) : (term131 _142544 _142545 _142546 t y u x s) = (term132 _142544 _142545 _142546 t x s y u).
Proof. exact (MK_COMB (@lem8037882) (@lem8037881 _142544 _142545 _142546 t x s y u)). Qed.
Lemma lem8037884 {_142544 _142546 : Type'} (t : type24 _142544 _142546) (y : cart _142544 _142546) (u : type24 _142544 _142546) : ((term129 _142544 _142546 t y u) = (term130 _142544 _142546 t y u)) = ((term129 _142544 _142546 t y u) = (term130 _142544 _142546 t y u)).
Proof. exact (eq_refl ((term129 _142544 _142546 t y u) = (term130 _142544 _142546 t y u))). Qed.
Lemma lem8037885 {_142544 _142545 _142546 : Type'} (x : cart _142544 _142545) (s : type24 _142544 _142545) (t : type24 _142544 _142546) (y : cart _142544 _142546) (u : type24 _142544 _142546) : ((term127 _142544 _142545 _142546 t y u x s) = ((term129 _142544 _142546 t y u) = (term130 _142544 _142546 t y u))) = (((term49 _142544 _142545 _142546 x s t y u) = (term57 _142544 _142545 _142546 t x s y u)) = ((term129 _142544 _142546 t y u) = (term130 _142544 _142546 t y u))).
Proof. exact (MK_COMB (@lem8037883 _142544 _142545 _142546 t x s y u) (@lem8037884 _142544 _142546 t y u)). Qed.
Lemma lem8037886 {_142544 _142545 _142546 : Type'} (x : cart _142544 _142545) (s : type24 _142544 _142545) (t : type24 _142544 _142546) (y : cart _142544 _142546) (u : type24 _142544 _142546) : ((term127 _142544 _142545 _142546 t y u x s) = (term128 _142544 _142546 t y u)) = (((term49 _142544 _142545 _142546 x s t y u) = (term57 _142544 _142545 _142546 t x s y u)) = ((term129 _142544 _142546 t y u) = (term130 _142544 _142546 t y u))).
Proof. exact (TRANS (@lem8037880 _142544 _142545 _142546 x s t y u) (@lem8037885 _142544 _142545 _142546 x s t y u)). Qed.
Lemma lem8037887 {_142544 _142545 _142546 : Type'} (t : type24 _142544 _142546) (y : cart _142544 _142546) (u : type24 _142544 _142546) (x : cart _142544 _142545) (s : type24 _142544 _142545) (h1 : (@IN (cart _142544 _142545) x s) = True) : ((term49 _142544 _142545 _142546 x s t y u) = (term57 _142544 _142545 _142546 t x s y u)) = ((term129 _142544 _142546 t y u) = (term130 _142544 _142546 t y u)).
Proof. exact (EQ_MP (@lem8037886 _142544 _142545 _142546 x s t y u) (@lem8037877 _142544 _142545 _142546 t y u x s h1)). Qed.
Lemma lem8037888 {_142544 _142545 _142546 : Type'} (t : type24 _142544 _142546) (y : cart _142544 _142546) (u : type24 _142544 _142546) (x : cart _142544 _142545) (s : type24 _142544 _142545) (h1 : (@IN (cart _142544 _142545) x s) = True) : ((term129 _142544 _142546 t y u) = (term130 _142544 _142546 t y u)) = ((term49 _142544 _142545 _142546 x s t y u) = (term57 _142544 _142545 _142546 t x s y u)).
Proof. exact (SYM (@lem8037887 _142544 _142545 _142546 t y u x s h1)). Qed.
Lemma lem8037889 {_142544 _142546 : Type'} (t : type24 _142544 _142546) (y : cart _142544 _142546) (u : type24 _142544 _142546) : (term126 _142544 _142546 t y u) = (term126 _142544 _142546 t y u).
Proof. exact (eq_refl (term126 _142544 _142546 t y u)). Qed.
Lemma lem8037890 {_142544 _142545 _142546 : Type'} (t : type24 _142544 _142546) (y : cart _142544 _142546) (u : type24 _142544 _142546) (x : cart _142544 _142545) (s : type24 _142544 _142545) (h1 : (@IN (cart _142544 _142545) x s) = False) : (term127 _142544 _142545 _142546 t y u x s) = (term133 _142544 _142546 t y u).
Proof. exact (MK_COMB (@lem8037889 _142544 _142546 t y u) (@lem8037861 _142544 _142545 x s h1)). Qed.
Lemma lem8037891 {_142544 _142546 : Type'} (t : type24 _142544 _142546) (y : cart _142544 _142546) (u : type24 _142544 _142546) : (term133 _142544 _142546 t y u) = ((term134 _142544 _142546 t y u) = (term135 _142544 _142546 t y u)).
Proof. exact (eq_refl (term133 _142544 _142546 t y u)). Qed.
Lemma lem8037892 {_142544 _142545 _142546 : Type'} (t : type24 _142544 _142546) (y : cart _142544 _142546) (u : type24 _142544 _142546) (x : cart _142544 _142545) (s : type24 _142544 _142545) : (term131 _142544 _142545 _142546 t y u x s) = (term131 _142544 _142545 _142546 t y u x s).
Proof. exact (eq_refl (term131 _142544 _142545 _142546 t y u x s)). Qed.
Lemma lem8037893 {_142544 _142545 _142546 : Type'} (x : cart _142544 _142545) (s : type24 _142544 _142545) (t : type24 _142544 _142546) (y : cart _142544 _142546) (u : type24 _142544 _142546) : ((term127 _142544 _142545 _142546 t y u x s) = (term133 _142544 _142546 t y u)) = ((term127 _142544 _142545 _142546 t y u x s) = ((term134 _142544 _142546 t y u) = (term135 _142544 _142546 t y u))).
Proof. exact (MK_COMB (@lem8037892 _142544 _142545 _142546 t y u x s) (@lem8037891 _142544 _142546 t y u)). Qed.
Lemma lem8037894 {_142544 _142545 _142546 : Type'} (t : type24 _142544 _142546) (x : cart _142544 _142545) (s : type24 _142544 _142545) (y : cart _142544 _142546) (u : type24 _142544 _142546) : (term127 _142544 _142545 _142546 t y u x s) = ((term49 _142544 _142545 _142546 x s t y u) = (term57 _142544 _142545 _142546 t x s y u)).
Proof. exact (eq_refl (term127 _142544 _142545 _142546 t y u x s)). Qed.
Lemma lem8037895 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8037896 {_142544 _142545 _142546 : Type'} (t : type24 _142544 _142546) (x : cart _142544 _142545) (s : type24 _142544 _142545) (y : cart _142544 _142546) (u : type24 _142544 _142546) : (term131 _142544 _142545 _142546 t y u x s) = (term132 _142544 _142545 _142546 t x s y u).
Proof. exact (MK_COMB (@lem8037895) (@lem8037894 _142544 _142545 _142546 t x s y u)). Qed.
Lemma lem8037897 {_142544 _142546 : Type'} (t : type24 _142544 _142546) (y : cart _142544 _142546) (u : type24 _142544 _142546) : ((term134 _142544 _142546 t y u) = (term135 _142544 _142546 t y u)) = ((term134 _142544 _142546 t y u) = (term135 _142544 _142546 t y u)).
Proof. exact (eq_refl ((term134 _142544 _142546 t y u) = (term135 _142544 _142546 t y u))). Qed.
Lemma lem8037898 {_142544 _142545 _142546 : Type'} (x : cart _142544 _142545) (s : type24 _142544 _142545) (t : type24 _142544 _142546) (y : cart _142544 _142546) (u : type24 _142544 _142546) : ((term127 _142544 _142545 _142546 t y u x s) = ((term134 _142544 _142546 t y u) = (term135 _142544 _142546 t y u))) = (((term49 _142544 _142545 _142546 x s t y u) = (term57 _142544 _142545 _142546 t x s y u)) = ((term134 _142544 _142546 t y u) = (term135 _142544 _142546 t y u))).
Proof. exact (MK_COMB (@lem8037896 _142544 _142545 _142546 t x s y u) (@lem8037897 _142544 _142546 t y u)). Qed.
Lemma lem8037899 {_142544 _142545 _142546 : Type'} (x : cart _142544 _142545) (s : type24 _142544 _142545) (t : type24 _142544 _142546) (y : cart _142544 _142546) (u : type24 _142544 _142546) : ((term127 _142544 _142545 _142546 t y u x s) = (term133 _142544 _142546 t y u)) = (((term49 _142544 _142545 _142546 x s t y u) = (term57 _142544 _142545 _142546 t x s y u)) = ((term134 _142544 _142546 t y u) = (term135 _142544 _142546 t y u))).
Proof. exact (TRANS (@lem8037893 _142544 _142545 _142546 x s t y u) (@lem8037898 _142544 _142545 _142546 x s t y u)). Qed.
Lemma lem8037900 {_142544 _142545 _142546 : Type'} (t : type24 _142544 _142546) (y : cart _142544 _142546) (u : type24 _142544 _142546) (x : cart _142544 _142545) (s : type24 _142544 _142545) (h1 : (@IN (cart _142544 _142545) x s) = False) : ((term49 _142544 _142545 _142546 x s t y u) = (term57 _142544 _142545 _142546 t x s y u)) = ((term134 _142544 _142546 t y u) = (term135 _142544 _142546 t y u)).
Proof. exact (EQ_MP (@lem8037899 _142544 _142545 _142546 x s t y u) (@lem8037890 _142544 _142545 _142546 t y u x s h1)). Qed.
Lemma lem8037901 {_142544 _142545 _142546 : Type'} (t : type24 _142544 _142546) (y : cart _142544 _142546) (u : type24 _142544 _142546) (x : cart _142544 _142545) (s : type24 _142544 _142545) (h1 : (@IN (cart _142544 _142545) x s) = False) : ((term134 _142544 _142546 t y u) = (term135 _142544 _142546 t y u)) = ((term49 _142544 _142545 _142546 x s t y u) = (term57 _142544 _142545 _142546 t x s y u)).
Proof. exact (SYM (@lem8037900 _142544 _142545 _142546 t y u x s h1)). Qed.
Lemma lem8037905 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8037906 {_142544 _142546 : Type'} (t : type24 _142544 _142546) (y : cart _142544 _142546) (u : type24 _142544 _142546) : (term129 _142544 _142546 t y u) = (term47 _142544 _142546 t y u).
Proof. exact (@lem8037905 (term47 _142544 _142546 t y u)). Qed.
Lemma lem8037909 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8037910 {_142544 _142546 : Type'} (t : type24 _142544 _142546) (y : cart _142544 _142546) (u : type24 _142544 _142546) : (term136 _142544 _142546 t y u) = (term137 _142544 _142546 t y u).
Proof. exact (MK_COMB (@lem8037909) (@lem8037906 _142544 _142546 t y u)). Qed.
Lemma lem8037914 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8037915 {_142544 _142546 : Type'} (y : cart _142544 _142546) (t : type24 _142544 _142546) : (term138 _142544 _142546 y t) = (@IN (cart _142544 _142546) y t).
Proof. exact (@lem8037914 (@IN (cart _142544 _142546) y t)). Qed.
Lemma lem8037916 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8037917 {_142544 _142546 : Type'} (y : cart _142544 _142546) (t : type24 _142544 _142546) : (term139 _142544 _142546 y t) = (term140 _142544 _142546 y t).
Proof. exact (MK_COMB (@lem8037916) (@lem8037915 _142544 _142546 y t)). Qed.
Lemma lem8037919 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8037920 {_142544 _142546 : Type'} (y : cart _142544 _142546) (u : type24 _142544 _142546) : (term138 _142544 _142546 y u) = (@IN (cart _142544 _142546) y u).
Proof. exact (@lem8037919 (@IN (cart _142544 _142546) y u)). Qed.
Lemma lem8037921 {_142544 _142546 : Type'} (t : type24 _142544 _142546) (y : cart _142544 _142546) (u : type24 _142544 _142546) : (term130 _142544 _142546 t y u) = (term47 _142544 _142546 t y u).
Proof. exact (MK_COMB (@lem8037917 _142544 _142546 y t) (@lem8037920 _142544 _142546 y u)). Qed.
Lemma lem8037924 {_142544 _142546 : Type'} (t : type24 _142544 _142546) (y : cart _142544 _142546) (u : type24 _142544 _142546) : ((term129 _142544 _142546 t y u) = (term130 _142544 _142546 t y u)) = ((term47 _142544 _142546 t y u) = (term47 _142544 _142546 t y u)).
Proof. exact (MK_COMB (@lem8037910 _142544 _142546 t y u) (@lem8037921 _142544 _142546 t y u)). Qed.
Lemma lem8037926 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem8037927 (x : Prop) : (x = x) = True.
Proof. exact (@lem8037926 Prop x). Qed.
Lemma lem8037928 {_142544 _142546 : Type'} (t : type24 _142544 _142546) (y : cart _142544 _142546) (u : type24 _142544 _142546) : ((term47 _142544 _142546 t y u) = (term47 _142544 _142546 t y u)) = True.
Proof. exact (@lem8037927 (term47 _142544 _142546 t y u)). Qed.
Lemma lem8037929 {_142544 _142546 : Type'} (t : type24 _142544 _142546) (y : cart _142544 _142546) (u : type24 _142544 _142546) : ((term129 _142544 _142546 t y u) = (term130 _142544 _142546 t y u)) = True.
Proof. exact (TRANS (@lem8037924 _142544 _142546 t y u) (@lem8037928 _142544 _142546 t y u)). Qed.
Lemma lem8037930 {_142544 _142546 : Type'} (t : type24 _142544 _142546) (y : cart _142544 _142546) (u : type24 _142544 _142546) : True = ((term129 _142544 _142546 t y u) = (term130 _142544 _142546 t y u)).
Proof. exact (SYM (@lem8037929 _142544 _142546 t y u)). Qed.
Lemma lem8037931 {_142544 _142546 : Type'} (t : type24 _142544 _142546) (y : cart _142544 _142546) (u : type24 _142544 _142546) : (term129 _142544 _142546 t y u) = (term130 _142544 _142546 t y u).
Proof. exact (EQ_MP (@lem8037930 _142544 _142546 t y u) (@lem0)). Qed.
Lemma lem8037935 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem8037936 {_142544 _142546 : Type'} (t : type24 _142544 _142546) (y : cart _142544 _142546) (u : type24 _142544 _142546) : (term134 _142544 _142546 t y u) = False.
Proof. exact (@lem8037935 (term47 _142544 _142546 t y u)). Qed.
Lemma lem8037937 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8037938 {_142544 _142546 : Type'} (t : type24 _142544 _142546) (y : cart _142544 _142546) (u : type24 _142544 _142546) : (term141 _142544 _142546 t y u) = (@eq Prop False).
Proof. exact (MK_COMB (@lem8037937) (@lem8037936 _142544 _142546 t y u)). Qed.
Lemma lem8037942 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem8037943 {_142544 _142546 : Type'} (y : cart _142544 _142546) (t : type24 _142544 _142546) : (term142 _142544 _142546 y t) = False.
Proof. exact (@lem8037942 (@IN (cart _142544 _142546) y t)). Qed.
Lemma lem8037944 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8037945 {_142544 _142546 : Type'} (y : cart _142544 _142546) (t : type24 _142544 _142546) : (term143 _142544 _142546 y t) = (or False).
Proof. exact (MK_COMB (@lem8037944) (@lem8037943 _142544 _142546 y t)). Qed.
Lemma lem8037947 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem8037948 {_142544 _142546 : Type'} (y : cart _142544 _142546) (u : type24 _142544 _142546) : (term142 _142544 _142546 y u) = False.
Proof. exact (@lem8037947 (@IN (cart _142544 _142546) y u)). Qed.
Lemma lem8037949 {_142544 _142546 : Type'} (t : type24 _142544 _142546) (y : cart _142544 _142546) (u : type24 _142544 _142546) : (term135 _142544 _142546 t y u) = (False \/ False).
Proof. exact (MK_COMB (@lem8037945 _142544 _142546 y t) (@lem8037948 _142544 _142546 y u)). Qed.
Lemma lem8037951 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem8037952 : (False \/ False) = False.
Proof. exact (@lem8037951 False). Qed.
Lemma lem8037953 {_142544 _142546 : Type'} (t : type24 _142544 _142546) (y : cart _142544 _142546) (u : type24 _142544 _142546) : (term135 _142544 _142546 t y u) = False.
Proof. exact (TRANS (@lem8037949 _142544 _142546 t y u) (@lem8037952)). Qed.
Lemma lem8037954 {_142544 _142546 : Type'} (t : type24 _142544 _142546) (y : cart _142544 _142546) (u : type24 _142544 _142546) : ((term134 _142544 _142546 t y u) = (term135 _142544 _142546 t y u)) = (False = False).
Proof. exact (MK_COMB (@lem8037938 _142544 _142546 t y u) (@lem8037953 _142544 _142546 t y u)). Qed.
Lemma lem8037956 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem8037957 : (False = False) = (~ False).
Proof. exact (@lem8037956 False). Qed.
Lemma lem8037959 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem8037960 : (False = False) = True.
Proof. exact (TRANS (@lem8037957) (@lem8037959)). Qed.
Lemma lem8037961 {_142544 _142546 : Type'} (t : type24 _142544 _142546) (y : cart _142544 _142546) (u : type24 _142544 _142546) : ((term134 _142544 _142546 t y u) = (term135 _142544 _142546 t y u)) = True.
Proof. exact (TRANS (@lem8037954 _142544 _142546 t y u) (@lem8037960)). Qed.
Lemma lem8037962 {_142544 _142546 : Type'} (t : type24 _142544 _142546) (y : cart _142544 _142546) (u : type24 _142544 _142546) : True = ((term134 _142544 _142546 t y u) = (term135 _142544 _142546 t y u)).
Proof. exact (SYM (@lem8037961 _142544 _142546 t y u)). Qed.
Lemma lem8037963 {_142544 _142546 : Type'} (t : type24 _142544 _142546) (y : cart _142544 _142546) (u : type24 _142544 _142546) : (term134 _142544 _142546 t y u) = (term135 _142544 _142546 t y u).
Proof. exact (EQ_MP (@lem8037962 _142544 _142546 t y u) (@lem0)). Qed.
Lemma lem8037964 {_142544 _142545 _142546 : Type'} (t : type24 _142544 _142546) (y : cart _142544 _142546) (u : type24 _142544 _142546) (x : cart _142544 _142545) (s : type24 _142544 _142545) (h1 : (@IN (cart _142544 _142545) x s) = False) : (term49 _142544 _142545 _142546 x s t y u) = (term57 _142544 _142545 _142546 t x s y u).
Proof. exact (EQ_MP (@lem8037901 _142544 _142545 _142546 t y u x s h1) (@lem8037963 _142544 _142546 t y u)). Qed.
Lemma lem8037965 {_142544 _142545 _142546 : Type'} (t : type24 _142544 _142546) (y : cart _142544 _142546) (u : type24 _142544 _142546) (x : cart _142544 _142545) (s : type24 _142544 _142545) (h1 : (@IN (cart _142544 _142545) x s) = True) : (term49 _142544 _142545 _142546 x s t y u) = (term57 _142544 _142545 _142546 t x s y u).
Proof. exact (EQ_MP (@lem8037888 _142544 _142545 _142546 t y u x s h1) (@lem8037931 _142544 _142546 t y u)). Qed.
Lemma lem8037968 {_142544 _142545 _142546 : Type'} (t : type24 _142544 _142546) (x : cart _142544 _142545) (s : type24 _142544 _142545) (y : cart _142544 _142546) (u : type24 _142544 _142546) : (term49 _142544 _142545 _142546 x s t y u) = (term57 _142544 _142545 _142546 t x s y u).
Proof. exact (or_elim (@lem8037859 _142544 _142545 x s) (fun h0 : (@IN (cart _142544 _142545) x s) = True => @lem8037965 _142544 _142545 _142546 t y u x s h0) (fun h0 : (@IN (cart _142544 _142545) x s) = False => @lem8037964 _142544 _142545 _142546 t y u x s h0)). Qed.
Lemma lem8037983 {_142580 _142581 : Type'} (x : cart _142580 _142581) (s : type24 _142580 _142581) : term124 _142580 _142581 x s.
Proof. exact (@lem9851 (@IN (cart _142580 _142581) x s)). Qed.
Lemma lem8037984 {_142580 _142581 : Type'} (x : cart _142580 _142581) (s : type24 _142580 _142581) : (term124 _142580 _142581 x s) = (term125 _142580 _142581 x s).
Proof. exact (eq_refl (term124 _142580 _142581 x s)). Qed.
Lemma lem8037985 {_142580 _142581 : Type'} (x : cart _142580 _142581) (s : type24 _142580 _142581) : term125 _142580 _142581 x s.
Proof. exact (EQ_MP (@lem8037984 _142580 _142581 x s) (@lem8037983 _142580 _142581 x s)). Qed.
Lemma lem8037986 {_142580 _142581 : Type'} (x : cart _142580 _142581) (s : type24 _142580 _142581) (h1 : (@IN (cart _142580 _142581) x s) = True) : (@IN (cart _142580 _142581) x s) = True.
Proof. exact (h1). Qed.
Lemma lem8037987 {_142580 _142581 : Type'} (x : cart _142580 _142581) (s : type24 _142580 _142581) (h1 : (@IN (cart _142580 _142581) x s) = False) : (@IN (cart _142580 _142581) x s) = False.
Proof. exact (h1). Qed.
Lemma lem8038002 {_142580 _142581 _142582 : Type'} (x : cart _142580 _142581) (t : type24 _142580 _142581) (y : cart _142580 _142582) (u : type24 _142580 _142582) : (term144 _142580 _142581 _142582 x t y u) = (term144 _142580 _142581 _142582 x t y u).
Proof. exact (eq_refl (term144 _142580 _142581 _142582 x t y u)). Qed.
Lemma lem8038003 {_142580 _142581 _142582 : Type'} (t : type24 _142580 _142581) (y : cart _142580 _142582) (u : type24 _142580 _142582) (x : cart _142580 _142581) (s : type24 _142580 _142581) (h1 : (@IN (cart _142580 _142581) x s) = True) : (term145 _142580 _142581 _142582 t y u x s) = (term146 _142580 _142581 _142582 x t y u).
Proof. exact (MK_COMB (@lem8038002 _142580 _142581 _142582 x t y u) (@lem8037986 _142580 _142581 x s h1)). Qed.
Lemma lem8038004 {_142580 _142581 _142582 : Type'} (x : cart _142580 _142581) (t : type24 _142580 _142581) (y : cart _142580 _142582) (u : type24 _142580 _142582) : (term146 _142580 _142581 _142582 x t y u) = ((term147 _142580 _142581 _142582 x t y u) = (term148 _142580 _142581 _142582 x t y u)).
Proof. exact (eq_refl (term146 _142580 _142581 _142582 x t y u)). Qed.
Lemma lem8038005 {_142580 _142581 _142582 : Type'} (t : type24 _142580 _142581) (y : cart _142580 _142582) (u : type24 _142580 _142582) (x : cart _142580 _142581) (s : type24 _142580 _142581) : (term149 _142580 _142581 _142582 t y u x s) = (term149 _142580 _142581 _142582 t y u x s).
Proof. exact (eq_refl (term149 _142580 _142581 _142582 t y u x s)). Qed.
Lemma lem8038006 {_142580 _142581 _142582 : Type'} (s : type24 _142580 _142581) (x : cart _142580 _142581) (t : type24 _142580 _142581) (y : cart _142580 _142582) (u : type24 _142580 _142582) : ((term145 _142580 _142581 _142582 t y u x s) = (term146 _142580 _142581 _142582 x t y u)) = ((term145 _142580 _142581 _142582 t y u x s) = ((term147 _142580 _142581 _142582 x t y u) = (term148 _142580 _142581 _142582 x t y u))).
Proof. exact (MK_COMB (@lem8038005 _142580 _142581 _142582 t y u x s) (@lem8038004 _142580 _142581 _142582 x t y u)). Qed.
Lemma lem8038007 {_142580 _142581 _142582 : Type'} (s : type24 _142580 _142581) (x : cart _142580 _142581) (t : type24 _142580 _142581) (y : cart _142580 _142582) (u : type24 _142580 _142582) : (term145 _142580 _142581 _142582 t y u x s) = ((term101 _142580 _142581 _142582 s x t y u) = (term105 _142580 _142581 _142582 s x t y u)).
Proof. exact (eq_refl (term145 _142580 _142581 _142582 t y u x s)). Qed.
Lemma lem8038008 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8038009 {_142580 _142581 _142582 : Type'} (s : type24 _142580 _142581) (x : cart _142580 _142581) (t : type24 _142580 _142581) (y : cart _142580 _142582) (u : type24 _142580 _142582) : (term149 _142580 _142581 _142582 t y u x s) = (term150 _142580 _142581 _142582 s x t y u).
Proof. exact (MK_COMB (@lem8038008) (@lem8038007 _142580 _142581 _142582 s x t y u)). Qed.
Lemma lem8038010 {_142580 _142581 _142582 : Type'} (x : cart _142580 _142581) (t : type24 _142580 _142581) (y : cart _142580 _142582) (u : type24 _142580 _142582) : ((term147 _142580 _142581 _142582 x t y u) = (term148 _142580 _142581 _142582 x t y u)) = ((term147 _142580 _142581 _142582 x t y u) = (term148 _142580 _142581 _142582 x t y u)).
Proof. exact (eq_refl ((term147 _142580 _142581 _142582 x t y u) = (term148 _142580 _142581 _142582 x t y u))). Qed.
Lemma lem8038011 {_142580 _142581 _142582 : Type'} (s : type24 _142580 _142581) (x : cart _142580 _142581) (t : type24 _142580 _142581) (y : cart _142580 _142582) (u : type24 _142580 _142582) : ((term145 _142580 _142581 _142582 t y u x s) = ((term147 _142580 _142581 _142582 x t y u) = (term148 _142580 _142581 _142582 x t y u))) = (((term101 _142580 _142581 _142582 s x t y u) = (term105 _142580 _142581 _142582 s x t y u)) = ((term147 _142580 _142581 _142582 x t y u) = (term148 _142580 _142581 _142582 x t y u))).
Proof. exact (MK_COMB (@lem8038009 _142580 _142581 _142582 s x t y u) (@lem8038010 _142580 _142581 _142582 x t y u)). Qed.
Lemma lem8038012 {_142580 _142581 _142582 : Type'} (s : type24 _142580 _142581) (x : cart _142580 _142581) (t : type24 _142580 _142581) (y : cart _142580 _142582) (u : type24 _142580 _142582) : ((term145 _142580 _142581 _142582 t y u x s) = (term146 _142580 _142581 _142582 x t y u)) = (((term101 _142580 _142581 _142582 s x t y u) = (term105 _142580 _142581 _142582 s x t y u)) = ((term147 _142580 _142581 _142582 x t y u) = (term148 _142580 _142581 _142582 x t y u))).
Proof. exact (TRANS (@lem8038006 _142580 _142581 _142582 s x t y u) (@lem8038011 _142580 _142581 _142582 s x t y u)). Qed.
Lemma lem8038013 {_142580 _142581 _142582 : Type'} (t : type24 _142580 _142581) (y : cart _142580 _142582) (u : type24 _142580 _142582) (x : cart _142580 _142581) (s : type24 _142580 _142581) (h1 : (@IN (cart _142580 _142581) x s) = True) : ((term101 _142580 _142581 _142582 s x t y u) = (term105 _142580 _142581 _142582 s x t y u)) = ((term147 _142580 _142581 _142582 x t y u) = (term148 _142580 _142581 _142582 x t y u)).
Proof. exact (EQ_MP (@lem8038012 _142580 _142581 _142582 s x t y u) (@lem8038003 _142580 _142581 _142582 t y u x s h1)). Qed.
Lemma lem8038014 {_142580 _142581 _142582 : Type'} (t : type24 _142580 _142581) (y : cart _142580 _142582) (u : type24 _142580 _142582) (x : cart _142580 _142581) (s : type24 _142580 _142581) (h1 : (@IN (cart _142580 _142581) x s) = True) : ((term147 _142580 _142581 _142582 x t y u) = (term148 _142580 _142581 _142582 x t y u)) = ((term101 _142580 _142581 _142582 s x t y u) = (term105 _142580 _142581 _142582 s x t y u)).
Proof. exact (SYM (@lem8038013 _142580 _142581 _142582 t y u x s h1)). Qed.
Lemma lem8038015 {_142580 _142581 _142582 : Type'} (x : cart _142580 _142581) (t : type24 _142580 _142581) (y : cart _142580 _142582) (u : type24 _142580 _142582) : (term144 _142580 _142581 _142582 x t y u) = (term144 _142580 _142581 _142582 x t y u).
Proof. exact (eq_refl (term144 _142580 _142581 _142582 x t y u)). Qed.
Lemma lem8038016 {_142580 _142581 _142582 : Type'} (t : type24 _142580 _142581) (y : cart _142580 _142582) (u : type24 _142580 _142582) (x : cart _142580 _142581) (s : type24 _142580 _142581) (h1 : (@IN (cart _142580 _142581) x s) = False) : (term145 _142580 _142581 _142582 t y u x s) = (term151 _142580 _142581 _142582 x t y u).
Proof. exact (MK_COMB (@lem8038015 _142580 _142581 _142582 x t y u) (@lem8037987 _142580 _142581 x s h1)). Qed.
Lemma lem8038017 {_142580 _142581 _142582 : Type'} (x : cart _142580 _142581) (t : type24 _142580 _142581) (y : cart _142580 _142582) (u : type24 _142580 _142582) : (term151 _142580 _142581 _142582 x t y u) = ((term152 _142580 _142581 _142582 x t y u) = (term153 _142580 _142581 _142582 x t y u)).
Proof. exact (eq_refl (term151 _142580 _142581 _142582 x t y u)). Qed.
Lemma lem8038018 {_142580 _142581 _142582 : Type'} (t : type24 _142580 _142581) (y : cart _142580 _142582) (u : type24 _142580 _142582) (x : cart _142580 _142581) (s : type24 _142580 _142581) : (term149 _142580 _142581 _142582 t y u x s) = (term149 _142580 _142581 _142582 t y u x s).
Proof. exact (eq_refl (term149 _142580 _142581 _142582 t y u x s)). Qed.
Lemma lem8038019 {_142580 _142581 _142582 : Type'} (s : type24 _142580 _142581) (x : cart _142580 _142581) (t : type24 _142580 _142581) (y : cart _142580 _142582) (u : type24 _142580 _142582) : ((term145 _142580 _142581 _142582 t y u x s) = (term151 _142580 _142581 _142582 x t y u)) = ((term145 _142580 _142581 _142582 t y u x s) = ((term152 _142580 _142581 _142582 x t y u) = (term153 _142580 _142581 _142582 x t y u))).
Proof. exact (MK_COMB (@lem8038018 _142580 _142581 _142582 t y u x s) (@lem8038017 _142580 _142581 _142582 x t y u)). Qed.
Lemma lem8038020 {_142580 _142581 _142582 : Type'} (s : type24 _142580 _142581) (x : cart _142580 _142581) (t : type24 _142580 _142581) (y : cart _142580 _142582) (u : type24 _142580 _142582) : (term145 _142580 _142581 _142582 t y u x s) = ((term101 _142580 _142581 _142582 s x t y u) = (term105 _142580 _142581 _142582 s x t y u)).
Proof. exact (eq_refl (term145 _142580 _142581 _142582 t y u x s)). Qed.
Lemma lem8038021 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8038022 {_142580 _142581 _142582 : Type'} (s : type24 _142580 _142581) (x : cart _142580 _142581) (t : type24 _142580 _142581) (y : cart _142580 _142582) (u : type24 _142580 _142582) : (term149 _142580 _142581 _142582 t y u x s) = (term150 _142580 _142581 _142582 s x t y u).
Proof. exact (MK_COMB (@lem8038021) (@lem8038020 _142580 _142581 _142582 s x t y u)). Qed.
Lemma lem8038023 {_142580 _142581 _142582 : Type'} (x : cart _142580 _142581) (t : type24 _142580 _142581) (y : cart _142580 _142582) (u : type24 _142580 _142582) : ((term152 _142580 _142581 _142582 x t y u) = (term153 _142580 _142581 _142582 x t y u)) = ((term152 _142580 _142581 _142582 x t y u) = (term153 _142580 _142581 _142582 x t y u)).
Proof. exact (eq_refl ((term152 _142580 _142581 _142582 x t y u) = (term153 _142580 _142581 _142582 x t y u))). Qed.
Lemma lem8038024 {_142580 _142581 _142582 : Type'} (s : type24 _142580 _142581) (x : cart _142580 _142581) (t : type24 _142580 _142581) (y : cart _142580 _142582) (u : type24 _142580 _142582) : ((term145 _142580 _142581 _142582 t y u x s) = ((term152 _142580 _142581 _142582 x t y u) = (term153 _142580 _142581 _142582 x t y u))) = (((term101 _142580 _142581 _142582 s x t y u) = (term105 _142580 _142581 _142582 s x t y u)) = ((term152 _142580 _142581 _142582 x t y u) = (term153 _142580 _142581 _142582 x t y u))).
Proof. exact (MK_COMB (@lem8038022 _142580 _142581 _142582 s x t y u) (@lem8038023 _142580 _142581 _142582 x t y u)). Qed.
Lemma lem8038025 {_142580 _142581 _142582 : Type'} (s : type24 _142580 _142581) (x : cart _142580 _142581) (t : type24 _142580 _142581) (y : cart _142580 _142582) (u : type24 _142580 _142582) : ((term145 _142580 _142581 _142582 t y u x s) = (term151 _142580 _142581 _142582 x t y u)) = (((term101 _142580 _142581 _142582 s x t y u) = (term105 _142580 _142581 _142582 s x t y u)) = ((term152 _142580 _142581 _142582 x t y u) = (term153 _142580 _142581 _142582 x t y u))).
Proof. exact (TRANS (@lem8038019 _142580 _142581 _142582 s x t y u) (@lem8038024 _142580 _142581 _142582 s x t y u)). Qed.
Lemma lem8038026 {_142580 _142581 _142582 : Type'} (t : type24 _142580 _142581) (y : cart _142580 _142582) (u : type24 _142580 _142582) (x : cart _142580 _142581) (s : type24 _142580 _142581) (h1 : (@IN (cart _142580 _142581) x s) = False) : ((term101 _142580 _142581 _142582 s x t y u) = (term105 _142580 _142581 _142582 s x t y u)) = ((term152 _142580 _142581 _142582 x t y u) = (term153 _142580 _142581 _142582 x t y u)).
Proof. exact (EQ_MP (@lem8038025 _142580 _142581 _142582 s x t y u) (@lem8038016 _142580 _142581 _142582 t y u x s h1)). Qed.
Lemma lem8038027 {_142580 _142581 _142582 : Type'} (t : type24 _142580 _142581) (y : cart _142580 _142582) (u : type24 _142580 _142582) (x : cart _142580 _142581) (s : type24 _142580 _142581) (h1 : (@IN (cart _142580 _142581) x s) = False) : ((term152 _142580 _142581 _142582 x t y u) = (term153 _142580 _142581 _142582 x t y u)) = ((term101 _142580 _142581 _142582 s x t y u) = (term105 _142580 _142581 _142582 s x t y u)).
Proof. exact (SYM (@lem8038026 _142580 _142581 _142582 t y u x s h1)). Qed.
Lemma lem8038033 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem8038034 {_142580 _142581 : Type'} (x : cart _142580 _142581) (t : type24 _142580 _142581) : (term154 _142580 _142581 x t) = True.
Proof. exact (@lem8038033 (@IN (cart _142580 _142581) x t)). Qed.
Lemma lem8038035 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8038036 {_142580 _142581 : Type'} (x : cart _142580 _142581) (t : type24 _142580 _142581) : (term155 _142580 _142581 x t) = (and True).
Proof. exact (MK_COMB (@lem8038035) (@lem8038034 _142580 _142581 x t)). Qed.
Lemma lem8038037 {_142580 _142582 : Type'} (y : cart _142580 _142582) (u : type24 _142580 _142582) : (@IN (cart _142580 _142582) y u) = (@IN (cart _142580 _142582) y u).
Proof. exact (eq_refl (@IN (cart _142580 _142582) y u)). Qed.
Lemma lem8038038 {_142580 _142581 _142582 : Type'} (x : cart _142580 _142581) (t : type24 _142580 _142581) (y : cart _142580 _142582) (u : type24 _142580 _142582) : (term147 _142580 _142581 _142582 x t y u) = (term138 _142580 _142582 y u).
Proof. exact (MK_COMB (@lem8038036 _142580 _142581 x t) (@lem8038037 _142580 _142582 y u)). Qed.
Lemma lem8038040 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8038041 {_142580 _142582 : Type'} (y : cart _142580 _142582) (u : type24 _142580 _142582) : (term138 _142580 _142582 y u) = (@IN (cart _142580 _142582) y u).
Proof. exact (@lem8038040 (@IN (cart _142580 _142582) y u)). Qed.
Lemma lem8038042 {_142580 _142581 _142582 : Type'} (x : cart _142580 _142581) (t : type24 _142580 _142581) (y : cart _142580 _142582) (u : type24 _142580 _142582) : (term147 _142580 _142581 _142582 x t y u) = (@IN (cart _142580 _142582) y u).
Proof. exact (TRANS (@lem8038038 _142580 _142581 _142582 x t y u) (@lem8038041 _142580 _142582 y u)). Qed.
Lemma lem8038043 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8038044 {_142580 _142581 _142582 : Type'} (x : cart _142580 _142581) (t : type24 _142580 _142581) (y : cart _142580 _142582) (u : type24 _142580 _142582) : (term156 _142580 _142581 _142582 x t y u) = (term157 _142580 _142582 y u).
Proof. exact (MK_COMB (@lem8038043) (@lem8038042 _142580 _142581 _142582 x t y u)). Qed.
Lemma lem8038048 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8038049 {_142580 _142582 : Type'} (y : cart _142580 _142582) (u : type24 _142580 _142582) : (term138 _142580 _142582 y u) = (@IN (cart _142580 _142582) y u).
Proof. exact (@lem8038048 (@IN (cart _142580 _142582) y u)). Qed.
Lemma lem8038050 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8038051 {_142580 _142582 : Type'} (y : cart _142580 _142582) (u : type24 _142580 _142582) : (term139 _142580 _142582 y u) = (term140 _142580 _142582 y u).
Proof. exact (MK_COMB (@lem8038050) (@lem8038049 _142580 _142582 y u)). Qed.
Lemma lem8038054 {_142580 _142581 _142582 : Type'} (x : cart _142580 _142581) (t : type24 _142580 _142581) (y : cart _142580 _142582) (u : type24 _142580 _142582) : (term8 _142580 _142581 _142582 x t y u) = (term8 _142580 _142581 _142582 x t y u).
Proof. exact (eq_refl (term8 _142580 _142581 _142582 x t y u)). Qed.
Lemma lem8038055 {_142580 _142581 _142582 : Type'} (x : cart _142580 _142581) (t : type24 _142580 _142581) (y : cart _142580 _142582) (u : type24 _142580 _142582) : (term148 _142580 _142581 _142582 x t y u) = (term158 _142580 _142581 _142582 x t y u).
Proof. exact (MK_COMB (@lem8038051 _142580 _142582 y u) (@lem8038054 _142580 _142581 _142582 x t y u)). Qed.
Lemma lem8038058 {_142580 _142581 _142582 : Type'} (x : cart _142580 _142581) (t : type24 _142580 _142581) (y : cart _142580 _142582) (u : type24 _142580 _142582) : ((term147 _142580 _142581 _142582 x t y u) = (term148 _142580 _142581 _142582 x t y u)) = ((@IN (cart _142580 _142582) y u) = (term158 _142580 _142581 _142582 x t y u)).
Proof. exact (MK_COMB (@lem8038044 _142580 _142581 _142582 x t y u) (@lem8038055 _142580 _142581 _142582 x t y u)). Qed.
Lemma lem8038061 {_142580 _142581 _142582 : Type'} (x : cart _142580 _142581) (t : type24 _142580 _142581) (y : cart _142580 _142582) (u : type24 _142580 _142582) : ((@IN (cart _142580 _142582) y u) = (term158 _142580 _142581 _142582 x t y u)) = ((term147 _142580 _142581 _142582 x t y u) = (term148 _142580 _142581 _142582 x t y u)).
Proof. exact (SYM (@lem8038058 _142580 _142581 _142582 x t y u)). Qed.
Lemma lem8038062 {_142580 _142582 : Type'} (y : cart _142580 _142582) (u : type24 _142580 _142582) : term124 _142580 _142582 y u.
Proof. exact (@lem9851 (@IN (cart _142580 _142582) y u)). Qed.
Lemma lem8038063 {_142580 _142582 : Type'} (y : cart _142580 _142582) (u : type24 _142580 _142582) : (term124 _142580 _142582 y u) = (term125 _142580 _142582 y u).
Proof. exact (eq_refl (term124 _142580 _142582 y u)). Qed.
Lemma lem8038064 {_142580 _142582 : Type'} (y : cart _142580 _142582) (u : type24 _142580 _142582) : term125 _142580 _142582 y u.
Proof. exact (EQ_MP (@lem8038063 _142580 _142582 y u) (@lem8038062 _142580 _142582 y u)). Qed.
Lemma lem8038065 {_142580 _142582 : Type'} (y : cart _142580 _142582) (u : type24 _142580 _142582) (h1 : (@IN (cart _142580 _142582) y u) = True) : (@IN (cart _142580 _142582) y u) = True.
Proof. exact (h1). Qed.
Lemma lem8038066 {_142580 _142582 : Type'} (y : cart _142580 _142582) (u : type24 _142580 _142582) (h1 : (@IN (cart _142580 _142582) y u) = False) : (@IN (cart _142580 _142582) y u) = False.
Proof. exact (h1). Qed.
Lemma lem8038075 {_142580 _142581 : Type'} (x : cart _142580 _142581) (t : type24 _142580 _142581) : (term159 _142580 _142581 x t) = (term159 _142580 _142581 x t).
Proof. exact (eq_refl (term159 _142580 _142581 x t)). Qed.
Lemma lem8038076 {_142580 _142581 _142582 : Type'} (x : cart _142580 _142581) (t : type24 _142580 _142581) (y : cart _142580 _142582) (u : type24 _142580 _142582) (h1 : (@IN (cart _142580 _142582) y u) = True) : (term160 _142580 _142581 _142582 x t y u) = (term161 _142580 _142581 x t).
Proof. exact (MK_COMB (@lem8038075 _142580 _142581 x t) (@lem8038065 _142580 _142582 y u h1)). Qed.
Lemma lem8038077 {_142580 _142581 : Type'} (x : cart _142580 _142581) (t : type24 _142580 _142581) : (term161 _142580 _142581 x t) = (True = (term162 _142580 _142581 x t)).
Proof. exact (eq_refl (term161 _142580 _142581 x t)). Qed.
Lemma lem8038078 {_142580 _142581 _142582 : Type'} (x : cart _142580 _142581) (t : type24 _142580 _142581) (y : cart _142580 _142582) (u : type24 _142580 _142582) : (term163 _142580 _142581 _142582 x t y u) = (term163 _142580 _142581 _142582 x t y u).
Proof. exact (eq_refl (term163 _142580 _142581 _142582 x t y u)). Qed.
Lemma lem8038079 {_142580 _142581 _142582 : Type'} (y : cart _142580 _142582) (u : type24 _142580 _142582) (x : cart _142580 _142581) (t : type24 _142580 _142581) : ((term160 _142580 _142581 _142582 x t y u) = (term161 _142580 _142581 x t)) = ((term160 _142580 _142581 _142582 x t y u) = (True = (term162 _142580 _142581 x t))).
Proof. exact (MK_COMB (@lem8038078 _142580 _142581 _142582 x t y u) (@lem8038077 _142580 _142581 x t)). Qed.
Lemma lem8038080 {_142580 _142581 _142582 : Type'} (x : cart _142580 _142581) (t : type24 _142580 _142581) (y : cart _142580 _142582) (u : type24 _142580 _142582) : (term160 _142580 _142581 _142582 x t y u) = ((@IN (cart _142580 _142582) y u) = (term158 _142580 _142581 _142582 x t y u)).
Proof. exact (eq_refl (term160 _142580 _142581 _142582 x t y u)). Qed.
Lemma lem8038081 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8038082 {_142580 _142581 _142582 : Type'} (x : cart _142580 _142581) (t : type24 _142580 _142581) (y : cart _142580 _142582) (u : type24 _142580 _142582) : (term163 _142580 _142581 _142582 x t y u) = (term164 _142580 _142581 _142582 x t y u).
Proof. exact (MK_COMB (@lem8038081) (@lem8038080 _142580 _142581 _142582 x t y u)). Qed.
Lemma lem8038083 {_142580 _142581 : Type'} (x : cart _142580 _142581) (t : type24 _142580 _142581) : (True = (term162 _142580 _142581 x t)) = (True = (term162 _142580 _142581 x t)).
Proof. exact (eq_refl (True = (term162 _142580 _142581 x t))). Qed.
Lemma lem8038084 {_142580 _142581 _142582 : Type'} (y : cart _142580 _142582) (u : type24 _142580 _142582) (x : cart _142580 _142581) (t : type24 _142580 _142581) : ((term160 _142580 _142581 _142582 x t y u) = (True = (term162 _142580 _142581 x t))) = (((@IN (cart _142580 _142582) y u) = (term158 _142580 _142581 _142582 x t y u)) = (True = (term162 _142580 _142581 x t))).
Proof. exact (MK_COMB (@lem8038082 _142580 _142581 _142582 x t y u) (@lem8038083 _142580 _142581 x t)). Qed.
Lemma lem8038085 {_142580 _142581 _142582 : Type'} (y : cart _142580 _142582) (u : type24 _142580 _142582) (x : cart _142580 _142581) (t : type24 _142580 _142581) : ((term160 _142580 _142581 _142582 x t y u) = (term161 _142580 _142581 x t)) = (((@IN (cart _142580 _142582) y u) = (term158 _142580 _142581 _142582 x t y u)) = (True = (term162 _142580 _142581 x t))).
Proof. exact (TRANS (@lem8038079 _142580 _142581 _142582 y u x t) (@lem8038084 _142580 _142581 _142582 y u x t)). Qed.
Lemma lem8038086 {_142580 _142581 _142582 : Type'} (x : cart _142580 _142581) (t : type24 _142580 _142581) (y : cart _142580 _142582) (u : type24 _142580 _142582) (h1 : (@IN (cart _142580 _142582) y u) = True) : ((@IN (cart _142580 _142582) y u) = (term158 _142580 _142581 _142582 x t y u)) = (True = (term162 _142580 _142581 x t)).
Proof. exact (EQ_MP (@lem8038085 _142580 _142581 _142582 y u x t) (@lem8038076 _142580 _142581 _142582 x t y u h1)). Qed.
Lemma lem8038087 {_142580 _142581 _142582 : Type'} (x : cart _142580 _142581) (t : type24 _142580 _142581) (y : cart _142580 _142582) (u : type24 _142580 _142582) (h1 : (@IN (cart _142580 _142582) y u) = True) : (True = (term162 _142580 _142581 x t)) = ((@IN (cart _142580 _142582) y u) = (term158 _142580 _142581 _142582 x t y u)).
Proof. exact (SYM (@lem8038086 _142580 _142581 _142582 x t y u h1)). Qed.
Lemma lem8038088 {_142580 _142581 : Type'} (x : cart _142580 _142581) (t : type24 _142580 _142581) : (term159 _142580 _142581 x t) = (term159 _142580 _142581 x t).
Proof. exact (eq_refl (term159 _142580 _142581 x t)). Qed.
Lemma lem8038089 {_142580 _142581 _142582 : Type'} (x : cart _142580 _142581) (t : type24 _142580 _142581) (y : cart _142580 _142582) (u : type24 _142580 _142582) (h1 : (@IN (cart _142580 _142582) y u) = False) : (term160 _142580 _142581 _142582 x t y u) = (term165 _142580 _142581 x t).
Proof. exact (MK_COMB (@lem8038088 _142580 _142581 x t) (@lem8038066 _142580 _142582 y u h1)). Qed.
Lemma lem8038090 {_142580 _142581 : Type'} (x : cart _142580 _142581) (t : type24 _142580 _142581) : (term165 _142580 _142581 x t) = (False = (term166 _142580 _142581 x t)).
Proof. exact (eq_refl (term165 _142580 _142581 x t)). Qed.
Lemma lem8038091 {_142580 _142581 _142582 : Type'} (x : cart _142580 _142581) (t : type24 _142580 _142581) (y : cart _142580 _142582) (u : type24 _142580 _142582) : (term163 _142580 _142581 _142582 x t y u) = (term163 _142580 _142581 _142582 x t y u).
Proof. exact (eq_refl (term163 _142580 _142581 _142582 x t y u)). Qed.
Lemma lem8038092 {_142580 _142581 _142582 : Type'} (y : cart _142580 _142582) (u : type24 _142580 _142582) (x : cart _142580 _142581) (t : type24 _142580 _142581) : ((term160 _142580 _142581 _142582 x t y u) = (term165 _142580 _142581 x t)) = ((term160 _142580 _142581 _142582 x t y u) = (False = (term166 _142580 _142581 x t))).
Proof. exact (MK_COMB (@lem8038091 _142580 _142581 _142582 x t y u) (@lem8038090 _142580 _142581 x t)). Qed.
Lemma lem8038093 {_142580 _142581 _142582 : Type'} (x : cart _142580 _142581) (t : type24 _142580 _142581) (y : cart _142580 _142582) (u : type24 _142580 _142582) : (term160 _142580 _142581 _142582 x t y u) = ((@IN (cart _142580 _142582) y u) = (term158 _142580 _142581 _142582 x t y u)).
Proof. exact (eq_refl (term160 _142580 _142581 _142582 x t y u)). Qed.
Lemma lem8038094 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8038095 {_142580 _142581 _142582 : Type'} (x : cart _142580 _142581) (t : type24 _142580 _142581) (y : cart _142580 _142582) (u : type24 _142580 _142582) : (term163 _142580 _142581 _142582 x t y u) = (term164 _142580 _142581 _142582 x t y u).
Proof. exact (MK_COMB (@lem8038094) (@lem8038093 _142580 _142581 _142582 x t y u)). Qed.
Lemma lem8038096 {_142580 _142581 : Type'} (x : cart _142580 _142581) (t : type24 _142580 _142581) : (False = (term166 _142580 _142581 x t)) = (False = (term166 _142580 _142581 x t)).
Proof. exact (eq_refl (False = (term166 _142580 _142581 x t))). Qed.
Lemma lem8038097 {_142580 _142581 _142582 : Type'} (y : cart _142580 _142582) (u : type24 _142580 _142582) (x : cart _142580 _142581) (t : type24 _142580 _142581) : ((term160 _142580 _142581 _142582 x t y u) = (False = (term166 _142580 _142581 x t))) = (((@IN (cart _142580 _142582) y u) = (term158 _142580 _142581 _142582 x t y u)) = (False = (term166 _142580 _142581 x t))).
Proof. exact (MK_COMB (@lem8038095 _142580 _142581 _142582 x t y u) (@lem8038096 _142580 _142581 x t)). Qed.
Lemma lem8038098 {_142580 _142581 _142582 : Type'} (y : cart _142580 _142582) (u : type24 _142580 _142582) (x : cart _142580 _142581) (t : type24 _142580 _142581) : ((term160 _142580 _142581 _142582 x t y u) = (term165 _142580 _142581 x t)) = (((@IN (cart _142580 _142582) y u) = (term158 _142580 _142581 _142582 x t y u)) = (False = (term166 _142580 _142581 x t))).
Proof. exact (TRANS (@lem8038092 _142580 _142581 _142582 y u x t) (@lem8038097 _142580 _142581 _142582 y u x t)). Qed.
Lemma lem8038099 {_142580 _142581 _142582 : Type'} (x : cart _142580 _142581) (t : type24 _142580 _142581) (y : cart _142580 _142582) (u : type24 _142580 _142582) (h1 : (@IN (cart _142580 _142582) y u) = False) : ((@IN (cart _142580 _142582) y u) = (term158 _142580 _142581 _142582 x t y u)) = (False = (term166 _142580 _142581 x t)).
Proof. exact (EQ_MP (@lem8038098 _142580 _142581 _142582 y u x t) (@lem8038089 _142580 _142581 _142582 x t y u h1)). Qed.
Lemma lem8038100 {_142580 _142581 _142582 : Type'} (x : cart _142580 _142581) (t : type24 _142580 _142581) (y : cart _142580 _142582) (u : type24 _142580 _142582) (h1 : (@IN (cart _142580 _142582) y u) = False) : (False = (term166 _142580 _142581 x t)) = ((@IN (cart _142580 _142582) y u) = (term158 _142580 _142581 _142582 x t y u)).
Proof. exact (SYM (@lem8038099 _142580 _142581 _142582 x t y u h1)). Qed.
Lemma lem8038102 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem8038103 {_142580 _142581 : Type'} (x : cart _142580 _142581) (t : type24 _142580 _142581) : (True = (term162 _142580 _142581 x t)) = (term162 _142580 _142581 x t).
Proof. exact (@lem8038102 (term162 _142580 _142581 x t)). Qed.
Lemma lem8038105 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem8038106 {_142580 _142581 : Type'} (x : cart _142580 _142581) (t : type24 _142580 _142581) : (term162 _142580 _142581 x t) = True.
Proof. exact (@lem8038105 (term167 _142580 _142581 x t)). Qed.
Lemma lem8038107 {_142580 _142581 : Type'} (x : cart _142580 _142581) (t : type24 _142580 _142581) : (True = (term162 _142580 _142581 x t)) = True.
Proof. exact (TRANS (@lem8038103 _142580 _142581 x t) (@lem8038106 _142580 _142581 x t)). Qed.
Lemma lem8038108 {_142580 _142581 : Type'} (x : cart _142580 _142581) (t : type24 _142580 _142581) : True = (True = (term162 _142580 _142581 x t)).
Proof. exact (SYM (@lem8038107 _142580 _142581 x t)). Qed.
Lemma lem8038109 {_142580 _142581 : Type'} (x : cart _142580 _142581) (t : type24 _142580 _142581) : True = (term162 _142580 _142581 x t).
Proof. exact (EQ_MP (@lem8038108 _142580 _142581 x t) (@lem0)). Qed.
Lemma lem8038111 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem8038112 {_142580 _142581 : Type'} (x : cart _142580 _142581) (t : type24 _142580 _142581) : (False = (term166 _142580 _142581 x t)) = (term168 _142580 _142581 x t).
Proof. exact (@lem8038111 (term166 _142580 _142581 x t)). Qed.
Lemma lem8038114 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem8038115 {_142580 _142581 : Type'} (x : cart _142580 _142581) (t : type24 _142580 _142581) : (term166 _142580 _142581 x t) = (term169 _142580 _142581 x t).
Proof. exact (@lem8038114 (term169 _142580 _142581 x t)). Qed.
Lemma lem8038117 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem8038118 {_142580 _142581 : Type'} (x : cart _142580 _142581) (t : type24 _142580 _142581) : (term169 _142580 _142581 x t) = False.
Proof. exact (@lem8038117 (@IN (cart _142580 _142581) x t)). Qed.
Lemma lem8038119 {_142580 _142581 : Type'} (x : cart _142580 _142581) (t : type24 _142580 _142581) : (term166 _142580 _142581 x t) = False.
Proof. exact (TRANS (@lem8038115 _142580 _142581 x t) (@lem8038118 _142580 _142581 x t)). Qed.
Lemma lem8038120 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8038121 {_142580 _142581 : Type'} (x : cart _142580 _142581) (t : type24 _142580 _142581) : (term168 _142580 _142581 x t) = (~ False).
Proof. exact (MK_COMB (@lem8038120) (@lem8038119 _142580 _142581 x t)). Qed.
Lemma lem8038123 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem8038124 {_142580 _142581 : Type'} (x : cart _142580 _142581) (t : type24 _142580 _142581) : (term168 _142580 _142581 x t) = True.
Proof. exact (TRANS (@lem8038121 _142580 _142581 x t) (@lem8038123)). Qed.
Lemma lem8038125 {_142580 _142581 : Type'} (x : cart _142580 _142581) (t : type24 _142580 _142581) : (False = (term166 _142580 _142581 x t)) = True.
Proof. exact (TRANS (@lem8038112 _142580 _142581 x t) (@lem8038124 _142580 _142581 x t)). Qed.
Lemma lem8038126 {_142580 _142581 : Type'} (x : cart _142580 _142581) (t : type24 _142580 _142581) : True = (False = (term166 _142580 _142581 x t)).
Proof. exact (SYM (@lem8038125 _142580 _142581 x t)). Qed.
Lemma lem8038127 {_142580 _142581 : Type'} (x : cart _142580 _142581) (t : type24 _142580 _142581) : False = (term166 _142580 _142581 x t).
Proof. exact (EQ_MP (@lem8038126 _142580 _142581 x t) (@lem0)). Qed.
Lemma lem8038128 {_142580 _142581 _142582 : Type'} (x : cart _142580 _142581) (t : type24 _142580 _142581) (y : cart _142580 _142582) (u : type24 _142580 _142582) (h1 : (@IN (cart _142580 _142582) y u) = False) : (@IN (cart _142580 _142582) y u) = (term158 _142580 _142581 _142582 x t y u).
Proof. exact (EQ_MP (@lem8038100 _142580 _142581 _142582 x t y u h1) (@lem8038127 _142580 _142581 x t)). Qed.
Lemma lem8038129 {_142580 _142581 _142582 : Type'} (x : cart _142580 _142581) (t : type24 _142580 _142581) (y : cart _142580 _142582) (u : type24 _142580 _142582) (h1 : (@IN (cart _142580 _142582) y u) = True) : (@IN (cart _142580 _142582) y u) = (term158 _142580 _142581 _142582 x t y u).
Proof. exact (EQ_MP (@lem8038087 _142580 _142581 _142582 x t y u h1) (@lem8038109 _142580 _142581 x t)). Qed.
Lemma lem8038131 {_142580 _142581 _142582 : Type'} (x : cart _142580 _142581) (t : type24 _142580 _142581) (y : cart _142580 _142582) (u : type24 _142580 _142582) : (@IN (cart _142580 _142582) y u) = (term158 _142580 _142581 _142582 x t y u).
Proof. exact (or_elim (@lem8038064 _142580 _142582 y u) (fun h0 : (@IN (cart _142580 _142582) y u) = True => @lem8038129 _142580 _142581 _142582 x t y u h0) (fun h0 : (@IN (cart _142580 _142582) y u) = False => @lem8038128 _142580 _142581 _142582 x t y u h0)). Qed.
Lemma lem8038132 {_142580 _142581 _142582 : Type'} (x : cart _142580 _142581) (t : type24 _142580 _142581) (y : cart _142580 _142582) (u : type24 _142580 _142582) : (term147 _142580 _142581 _142582 x t y u) = (term148 _142580 _142581 _142582 x t y u).
Proof. exact (EQ_MP (@lem8038061 _142580 _142581 _142582 x t y u) (@lem8038131 _142580 _142581 _142582 x t y u)). Qed.
Lemma lem8038138 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem8038139 {_142580 _142581 : Type'} (x : cart _142580 _142581) (t : type24 _142580 _142581) : (term170 _142580 _142581 x t) = (@IN (cart _142580 _142581) x t).
Proof. exact (@lem8038138 (@IN (cart _142580 _142581) x t)). Qed.
Lemma lem8038140 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8038141 {_142580 _142581 : Type'} (x : cart _142580 _142581) (t : type24 _142580 _142581) : (term171 _142580 _142581 x t) = (term48 _142580 _142581 x t).
Proof. exact (MK_COMB (@lem8038140) (@lem8038139 _142580 _142581 x t)). Qed.
Lemma lem8038142 {_142580 _142582 : Type'} (y : cart _142580 _142582) (u : type24 _142580 _142582) : (@IN (cart _142580 _142582) y u) = (@IN (cart _142580 _142582) y u).
Proof. exact (eq_refl (@IN (cart _142580 _142582) y u)). Qed.
Lemma lem8038143 {_142580 _142581 _142582 : Type'} (x : cart _142580 _142581) (t : type24 _142580 _142581) (y : cart _142580 _142582) (u : type24 _142580 _142582) : (term152 _142580 _142581 _142582 x t y u) = (term8 _142580 _142581 _142582 x t y u).
Proof. exact (MK_COMB (@lem8038141 _142580 _142581 x t) (@lem8038142 _142580 _142582 y u)). Qed.
Lemma lem8038146 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8038147 {_142580 _142581 _142582 : Type'} (x : cart _142580 _142581) (t : type24 _142580 _142581) (y : cart _142580 _142582) (u : type24 _142580 _142582) : (term172 _142580 _142581 _142582 x t y u) = (term173 _142580 _142581 _142582 x t y u).
Proof. exact (MK_COMB (@lem8038146) (@lem8038143 _142580 _142581 _142582 x t y u)). Qed.
Lemma lem8038151 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem8038152 {_142580 _142582 : Type'} (y : cart _142580 _142582) (u : type24 _142580 _142582) : (term142 _142580 _142582 y u) = False.
Proof. exact (@lem8038151 (@IN (cart _142580 _142582) y u)). Qed.
Lemma lem8038153 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8038154 {_142580 _142582 : Type'} (y : cart _142580 _142582) (u : type24 _142580 _142582) : (term143 _142580 _142582 y u) = (or False).
Proof. exact (MK_COMB (@lem8038153) (@lem8038152 _142580 _142582 y u)). Qed.
Lemma lem8038157 {_142580 _142581 _142582 : Type'} (x : cart _142580 _142581) (t : type24 _142580 _142581) (y : cart _142580 _142582) (u : type24 _142580 _142582) : (term8 _142580 _142581 _142582 x t y u) = (term8 _142580 _142581 _142582 x t y u).
Proof. exact (eq_refl (term8 _142580 _142581 _142582 x t y u)). Qed.
Lemma lem8038158 {_142580 _142581 _142582 : Type'} (x : cart _142580 _142581) (t : type24 _142580 _142581) (y : cart _142580 _142582) (u : type24 _142580 _142582) : (term153 _142580 _142581 _142582 x t y u) = (term174 _142580 _142581 _142582 x t y u).
Proof. exact (MK_COMB (@lem8038154 _142580 _142582 y u) (@lem8038157 _142580 _142581 _142582 x t y u)). Qed.
Lemma lem8038160 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem8038161 {_142580 _142581 _142582 : Type'} (x : cart _142580 _142581) (t : type24 _142580 _142581) (y : cart _142580 _142582) (u : type24 _142580 _142582) : (term174 _142580 _142581 _142582 x t y u) = (term8 _142580 _142581 _142582 x t y u).
Proof. exact (@lem8038160 (term8 _142580 _142581 _142582 x t y u)). Qed.
Lemma lem8038164 {_142580 _142581 _142582 : Type'} (x : cart _142580 _142581) (t : type24 _142580 _142581) (y : cart _142580 _142582) (u : type24 _142580 _142582) : (term153 _142580 _142581 _142582 x t y u) = (term8 _142580 _142581 _142582 x t y u).
Proof. exact (TRANS (@lem8038158 _142580 _142581 _142582 x t y u) (@lem8038161 _142580 _142581 _142582 x t y u)). Qed.
Lemma lem8038165 {_142580 _142581 _142582 : Type'} (x : cart _142580 _142581) (t : type24 _142580 _142581) (y : cart _142580 _142582) (u : type24 _142580 _142582) : ((term152 _142580 _142581 _142582 x t y u) = (term153 _142580 _142581 _142582 x t y u)) = ((term8 _142580 _142581 _142582 x t y u) = (term8 _142580 _142581 _142582 x t y u)).
Proof. exact (MK_COMB (@lem8038147 _142580 _142581 _142582 x t y u) (@lem8038164 _142580 _142581 _142582 x t y u)). Qed.
Lemma lem8038167 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem8038168 (x : Prop) : (x = x) = True.
Proof. exact (@lem8038167 Prop x). Qed.
Lemma lem8038169 {_142580 _142581 _142582 : Type'} (x : cart _142580 _142581) (t : type24 _142580 _142581) (y : cart _142580 _142582) (u : type24 _142580 _142582) : ((term8 _142580 _142581 _142582 x t y u) = (term8 _142580 _142581 _142582 x t y u)) = True.
Proof. exact (@lem8038168 (term8 _142580 _142581 _142582 x t y u)). Qed.
Lemma lem8038170 {_142580 _142581 _142582 : Type'} (x : cart _142580 _142581) (t : type24 _142580 _142581) (y : cart _142580 _142582) (u : type24 _142580 _142582) : ((term152 _142580 _142581 _142582 x t y u) = (term153 _142580 _142581 _142582 x t y u)) = True.
Proof. exact (TRANS (@lem8038165 _142580 _142581 _142582 x t y u) (@lem8038169 _142580 _142581 _142582 x t y u)). Qed.
Lemma lem8038171 {_142580 _142581 _142582 : Type'} (x : cart _142580 _142581) (t : type24 _142580 _142581) (y : cart _142580 _142582) (u : type24 _142580 _142582) : True = ((term152 _142580 _142581 _142582 x t y u) = (term153 _142580 _142581 _142582 x t y u)).
Proof. exact (SYM (@lem8038170 _142580 _142581 _142582 x t y u)). Qed.
Lemma lem8038172 {_142580 _142581 _142582 : Type'} (x : cart _142580 _142581) (t : type24 _142580 _142581) (y : cart _142580 _142582) (u : type24 _142580 _142582) : (term152 _142580 _142581 _142582 x t y u) = (term153 _142580 _142581 _142582 x t y u).
Proof. exact (EQ_MP (@lem8038171 _142580 _142581 _142582 x t y u) (@lem0)). Qed.
Lemma lem8038173 {_142580 _142581 _142582 : Type'} (t : type24 _142580 _142581) (y : cart _142580 _142582) (u : type24 _142580 _142582) (x : cart _142580 _142581) (s : type24 _142580 _142581) (h1 : (@IN (cart _142580 _142581) x s) = False) : (term101 _142580 _142581 _142582 s x t y u) = (term105 _142580 _142581 _142582 s x t y u).
Proof. exact (EQ_MP (@lem8038027 _142580 _142581 _142582 t y u x s h1) (@lem8038172 _142580 _142581 _142582 x t y u)). Qed.
Lemma lem8038174 {_142580 _142581 _142582 : Type'} (t : type24 _142580 _142581) (y : cart _142580 _142582) (u : type24 _142580 _142582) (x : cart _142580 _142581) (s : type24 _142580 _142581) (h1 : (@IN (cart _142580 _142581) x s) = True) : (term101 _142580 _142581 _142582 s x t y u) = (term105 _142580 _142581 _142582 s x t y u).
Proof. exact (EQ_MP (@lem8038014 _142580 _142581 _142582 t y u x s h1) (@lem8038132 _142580 _142581 _142582 x t y u)). Qed.
Lemma lem8038177 {_142580 _142581 _142582 : Type'} (s : type24 _142580 _142581) (x : cart _142580 _142581) (t : type24 _142580 _142581) (y : cart _142580 _142582) (u : type24 _142580 _142582) : (term101 _142580 _142581 _142582 s x t y u) = (term105 _142580 _142581 _142582 s x t y u).
Proof. exact (or_elim (@lem8037985 _142580 _142581 x s) (fun h0 : (@IN (cart _142580 _142581) x s) = True => @lem8038174 _142580 _142581 _142582 t y u x s h0) (fun h0 : (@IN (cart _142580 _142581) x s) = False => @lem8038173 _142580 _142581 _142582 t y u x s h0)). Qed.
Lemma lem8038182 {_142580 _142581 _142582 : Type'} (s : type24 _142580 _142581) (x : cart _142580 _142581) (t : type24 _142580 _142581) (u : type24 _142580 _142582) : term107 _142580 _142581 _142582 s x t u.
Proof. exact (fun y : cart _142580 _142582 => @lem8038177 _142580 _142581 _142582 s x t y u). Qed.
Lemma lem8038187 {_142580 _142581 _142582 : Type'} (s : type24 _142580 _142581) (t : type24 _142580 _142581) (u : type24 _142580 _142582) : term109 _142580 _142581 _142582 s t u.
Proof. exact (fun x : cart _142580 _142581 => @lem8038182 _142580 _142581 _142582 s x t u). Qed.
Lemma lem8038192 {_142580 _142581 _142582 : Type'} (s : type24 _142580 _142581) (t : type24 _142580 _142581) : term113 _142580 _142581 _142582 s t.
Proof. exact (fun u : type24 _142580 _142582 => @lem8038187 _142580 _142581 _142582 s t u). Qed.
Lemma lem8038197 {_142580 _142581 _142582 : Type'} (s : type24 _142580 _142581) : term117 _142580 _142581 _142582 s.
Proof. exact (fun t : type24 _142580 _142581 => @lem8038192 _142580 _142581 _142582 s t). Qed.
Lemma lem8038202 {_142580 _142581 _142582 : Type'} : term121 _142580 _142581 _142582.
Proof. exact (fun s : type24 _142580 _142581 => @lem8038197 _142580 _142581 _142582 s). Qed.
Lemma lem8038207 {_142544 _142545 _142546 : Type'} (t : type24 _142544 _142546) (x : cart _142544 _142545) (s : type24 _142544 _142545) (u : type24 _142544 _142546) : term59 _142544 _142545 _142546 t x s u.
Proof. exact (fun y : cart _142544 _142546 => @lem8037968 _142544 _142545 _142546 t x s y u). Qed.
Lemma lem8038212 {_142544 _142545 _142546 : Type'} (t : type24 _142544 _142546) (s : type24 _142544 _142545) (u : type24 _142544 _142546) : term61 _142544 _142545 _142546 t s u.
Proof. exact (fun x : cart _142544 _142545 => @lem8038207 _142544 _142545 _142546 t x s u). Qed.
Lemma lem8038217 {_142544 _142545 _142546 : Type'} (t : type24 _142544 _142546) (s : type24 _142544 _142545) : term65 _142544 _142545 _142546 t s.
Proof. exact (fun u : type24 _142544 _142546 => @lem8038212 _142544 _142545 _142546 t s u). Qed.
Lemma lem8038222 {_142544 _142545 _142546 : Type'} (s : type24 _142544 _142545) : term69 _142544 _142545 _142546 s.
Proof. exact (fun t : type24 _142544 _142546 => @lem8038217 _142544 _142545 _142546 t s). Qed.
Lemma lem8038227 {_142544 _142545 _142546 : Type'} : term73 _142544 _142545 _142546.
Proof. exact (fun s : type24 _142544 _142545 => @lem8038222 _142544 _142545 _142546 s). Qed.
Lemma lem8038228 {_142544 _142545 _142546 _142580 _142581 _142582 : Type'} : term123 _142544 _142545 _142546 _142580 _142581 _142582.
Proof. exact (conj (@lem8038227 _142544 _142545 _142546) (@lem8038202 _142580 _142581 _142582)). Qed.
Lemma lem8038229 {_142544 _142545 _142546 _142580 _142581 _142582 : Type'} : term122 _142544 _142545 _142546 _142580 _142581 _142582.
Proof. exact (EQ_MP (@lem8037842 _142544 _142545 _142546 _142580 _142581 _142582) (@lem8038228 _142544 _142545 _142546 _142580 _142581 _142582)). Qed.
