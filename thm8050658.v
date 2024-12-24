Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm8050658_term_abbrevs.
Require Import EXTENSION_spec.
Require Import PASTECART_IN_PCROSS_spec.
Require Import thm7660850_spec.
Require Import thm7662539_spec.
Lemma lem8050483 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) : term0 _141927 _141928 _141929 s.
Proof. exact (@lem8004229 _141927 _141928 _141929 s). Qed.
Lemma lem8050484 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) : (term0 _141927 _141928 _141929 s) = (term1 _141927 _141928 _141929 s).
Proof. exact (eq_refl (term0 _141927 _141928 _141929 s)). Qed.
Lemma lem8050485 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) : term1 _141927 _141928 _141929 s.
Proof. exact (EQ_MP (@lem8050484 _141927 _141928 _141929 s) (@lem8050483 _141927 _141928 _141929 s)). Qed.
Lemma lem8050486 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) (t : type24 _141927 _141929) : term2 _141927 _141928 _141929 s t.
Proof. exact (@lem8050485 _141927 _141928 _141929 s t). Qed.
Lemma lem8050487 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) (t : type24 _141927 _141929) : (term2 _141927 _141928 _141929 s t) = (term3 _141927 _141928 _141929 s t).
Proof. exact (eq_refl (term2 _141927 _141928 _141929 s t)). Qed.
Lemma lem8050488 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) (t : type24 _141927 _141929) : term3 _141927 _141928 _141929 s t.
Proof. exact (EQ_MP (@lem8050487 _141927 _141928 _141929 s t) (@lem8050486 _141927 _141928 _141929 s t)). Qed.
Lemma lem8050489 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) (t : type24 _141927 _141929) (x : cart _141927 _141928) : term4 _141927 _141928 _141929 s t x.
Proof. exact (@lem8050488 _141927 _141928 _141929 s t x). Qed.
Lemma lem8050490 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (t : type24 _141927 _141929) : (term4 _141927 _141928 _141929 s t x) = (term5 _141927 _141928 _141929 x s t).
Proof. exact (eq_refl (term4 _141927 _141928 _141929 s t x)). Qed.
Lemma lem8050491 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (t : type24 _141927 _141929) : term5 _141927 _141928 _141929 x s t.
Proof. exact (EQ_MP (@lem8050490 _141927 _141928 _141929 x s t) (@lem8050489 _141927 _141928 _141929 s t x)). Qed.
Lemma lem8050492 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (t : type24 _141927 _141929) (y : cart _141927 _141929) : term6 _141927 _141928 _141929 x s t y.
Proof. exact (@lem8050491 _141927 _141928 _141929 x s t y). Qed.
Lemma lem8050493 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (y : cart _141927 _141929) (t : type24 _141927 _141929) : (term6 _141927 _141928 _141929 x s t y) = ((term7 _141927 _141928 _141929 x y s t) = (term8 _141927 _141928 _141929 x s y t)).
Proof. exact (eq_refl (term6 _141927 _141928 _141929 x s t y)). Qed.
Lemma lem8050533 {A : Type'} (s : A -> Prop) : term9 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem8050534 {A : Type'} (s : A -> Prop) : (term9 A s) = (term10 A s).
Proof. exact (eq_refl (term9 A s)). Qed.
Lemma lem8050535 {A : Type'} (s : A -> Prop) : term10 A s.
Proof. exact (EQ_MP (@lem8050534 A s) (@lem8050533 A s)). Qed.
Lemma lem8050536 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term11 A s t.
Proof. exact (@lem8050535 A s t). Qed.
Lemma lem8050537 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term11 A s t) = ((s = t) = (term12 A s t)).
Proof. exact (eq_refl (term11 A s t)). Qed.
Lemma lem8050564 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term12 A s t).
Proof. exact (EQ_MP (@lem8050537 A s t) (@lem8050536 A s t)). Qed.
Lemma lem8050565 {_143061 _143062 _143063 : Type'} (s : type16 _143061 _143062 _143063) (t : type16 _143061 _143062 _143063) : (s = t) = (term13 _143061 _143062 _143063 s t).
Proof. exact (@lem8050564 (type2 _143061 _143062 _143063) s t). Qed.
Lemma lem8050566 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : ((term14 _143061 _143062 _143063 f t) = (@PCROSS _143061 _143062 _143063 (@UNIV (cart _143061 _143062)) t)) = (term15 _143061 _143062 _143063 f t).
Proof. exact (@lem8050565 _143061 _143062 _143063 (term14 _143061 _143062 _143063 f t) (@PCROSS _143061 _143062 _143063 (@UNIV (cart _143061 _143062)) t)). Qed.
Lemma lem8050572 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term16 _140454 _140455 _140456 P) = (term17 _140454 _140455 _140456 P).
Proof. exact (EQ_MP (@lem7660850 _140454 _140455 _140456 P) (@lem7662539 _140454 _140455 _140456 P)). Qed.
Lemma lem8050573 {_143061 _143062 _143063 : Type'} (P : type16 _143061 _143062 _143063) : (term16 _143061 _143062 _143063 P) = (term17 _143061 _143062 _143063 P).
Proof. exact (@lem8050572 _143061 _143062 _143063 P). Qed.
Lemma lem8050574 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : (term18 _143061 _143062 _143063 f t) = (term19 _143061 _143062 _143063 f t).
Proof. exact (@lem8050573 _143061 _143062 _143063 (term20 _143061 _143062 _143063 f t)). Qed.
Lemma lem8050575 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : type2 _143061 _143062 _143063) (t : type24 _143061 _143063) : (term21 _143061 _143062 _143063 f t x) = ((term22 _143061 _143062 _143063 x f t) = (term23 _143061 _143062 _143063 x t)).
Proof. exact (eq_refl (term21 _143061 _143062 _143063 f t x)). Qed.
Lemma lem8050576 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : (term24 _143061 _143062 _143063 f t) = (term20 _143061 _143062 _143063 f t).
Proof. exact (fun_ext (fun x : type2 _143061 _143062 _143063 => @lem8050575 _143061 _143062 _143063 f x t)). Qed.
Lemma lem8050577 {_143061 _143062 _143063 : Type'} : (@all (cart _143061 (finite_sum _143062 _143063))) = (@all (cart _143061 (finite_sum _143062 _143063))).
Proof. exact (eq_refl (@all (cart _143061 (finite_sum _143062 _143063)))). Qed.
Lemma lem8050578 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : (term18 _143061 _143062 _143063 f t) = (term15 _143061 _143062 _143063 f t).
Proof. exact (MK_COMB (@lem8050577 _143061 _143062 _143063) (@lem8050576 _143061 _143062 _143063 f t)). Qed.
Lemma lem8050579 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8050580 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : (term25 _143061 _143062 _143063 f t) = (term26 _143061 _143062 _143063 f t).
Proof. exact (MK_COMB (@lem8050579) (@lem8050578 _143061 _143062 _143063 f t)). Qed.
Lemma lem8050581 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (y : cart _143061 _143063) (t : type24 _143061 _143063) : (term27 _143061 _143062 _143063 f t x y) = ((term28 _143061 _143062 _143063 x y f t) = (term29 _143061 _143062 _143063 x y t)).
Proof. exact (eq_refl (term27 _143061 _143062 _143063 f t x y)). Qed.
Lemma lem8050582 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) : (term30 _143061 _143062 _143063 f t x) = (term31 _143061 _143062 _143063 f x t).
Proof. exact (fun_ext (fun y : cart _143061 _143063 => @lem8050581 _143061 _143062 _143063 f x y t)). Qed.
Lemma lem8050583 {_143061 _143063 : Type'} : (@all (cart _143061 _143063)) = (@all (cart _143061 _143063)).
Proof. exact (eq_refl (@all (cart _143061 _143063))). Qed.
Lemma lem8050584 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) : (term32 _143061 _143062 _143063 f t x) = (term33 _143061 _143062 _143063 f x t).
Proof. exact (MK_COMB (@lem8050583 _143061 _143063) (@lem8050582 _143061 _143062 _143063 f x t)). Qed.
Lemma lem8050585 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : (term34 _143061 _143062 _143063 f t) = (term35 _143061 _143062 _143063 f t).
Proof. exact (fun_ext (fun x : cart _143061 _143062 => @lem8050584 _143061 _143062 _143063 f x t)). Qed.
Lemma lem8050586 {_143061 _143062 : Type'} : (@all (cart _143061 _143062)) = (@all (cart _143061 _143062)).
Proof. exact (eq_refl (@all (cart _143061 _143062))). Qed.
Lemma lem8050587 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : (term19 _143061 _143062 _143063 f t) = (term36 _143061 _143062 _143063 f t).
Proof. exact (MK_COMB (@lem8050586 _143061 _143062) (@lem8050585 _143061 _143062 _143063 f t)). Qed.
Lemma lem8050588 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : ((term18 _143061 _143062 _143063 f t) = (term19 _143061 _143062 _143063 f t)) = ((term15 _143061 _143062 _143063 f t) = (term36 _143061 _143062 _143063 f t)).
Proof. exact (MK_COMB (@lem8050580 _143061 _143062 _143063 f t) (@lem8050587 _143061 _143062 _143063 f t)). Qed.
Lemma lem8050589 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : (term15 _143061 _143062 _143063 f t) = (term36 _143061 _143062 _143063 f t).
Proof. exact (EQ_MP (@lem8050588 _143061 _143062 _143063 f t) (@lem8050574 _143061 _143062 _143063 f t)). Qed.
Lemma lem8050596 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : ((term14 _143061 _143062 _143063 f t) = (@PCROSS _143061 _143062 _143063 (@UNIV (cart _143061 _143062)) t)) = (term36 _143061 _143062 _143063 f t).
Proof. exact (TRANS (@lem8050566 _143061 _143062 _143063 f t) (@lem8050589 _143061 _143062 _143063 f t)). Qed.
Lemma lem8050608 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (y : cart _141927 _141929) (t : type24 _141927 _141929) : (term7 _141927 _141928 _141929 x y s t) = (term8 _141927 _141928 _141929 x s y t).
Proof. exact (EQ_MP (@lem8050493 _141927 _141928 _141929 x s y t) (@lem8050492 _141927 _141928 _141929 x s t y)). Qed.
Lemma lem8050609 {_143061 _143062 _143063 : Type'} (x : cart _143061 _143062) (s : type24 _143061 _143062) (y : cart _143061 _143063) (t : type24 _143061 _143063) : (term7 _143061 _143062 _143063 x y s t) = (term8 _143061 _143062 _143063 x s y t).
Proof. exact (@lem8050608 _143061 _143062 _143063 x s y t). Qed.
Lemma lem8050610 {_143061 _143062 _143063 : Type'} (x : cart _143061 _143062) (f : type56 _143061 _143062) (y : cart _143061 _143063) (t : type24 _143061 _143063) : (term28 _143061 _143062 _143063 x y f t) = (term37 _143061 _143062 _143063 x f y t).
Proof. exact (@lem8050609 _143061 _143062 _143063 x (@INTERS (cart _143061 _143062) f) y t). Qed.
Lemma lem8050614 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (h1 : f = (@EMPTY ((cart _143061 _143062) -> Prop))) : f = (@EMPTY ((cart _143061 _143062) -> Prop)).
Proof. exact (h1). Qed.
Lemma lem8050615 {_143061 _143062 : Type'} : (@INTERS (cart _143061 _143062)) = (@INTERS (cart _143061 _143062)).
Proof. exact (eq_refl (@INTERS (cart _143061 _143062))). Qed.
Lemma lem8050616 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (h1 : f = (@EMPTY ((cart _143061 _143062) -> Prop))) : (@INTERS (cart _143061 _143062) f) = (@INTERS (cart _143061 _143062) (@EMPTY ((cart _143061 _143062) -> Prop))).
Proof. exact (MK_COMB (@lem8050615 _143061 _143062) (@lem8050614 _143061 _143062 f h1)). Qed.
Lemma lem8050617 {_143061 _143062 : Type'} (x : cart _143061 _143062) : (@IN (cart _143061 _143062) x) = (@IN (cart _143061 _143062) x).
Proof. exact (eq_refl (@IN (cart _143061 _143062) x)). Qed.
Lemma lem8050618 {_143061 _143062 : Type'} (x : cart _143061 _143062) (f : type56 _143061 _143062) (h1 : f = (@EMPTY ((cart _143061 _143062) -> Prop))) : (term38 _143061 _143062 x f) = (term39 _143061 _143062 x).
Proof. exact (MK_COMB (@lem8050617 _143061 _143062 x) (@lem8050616 _143061 _143062 f h1)). Qed.
Lemma lem8050619 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8050620 {_143061 _143062 : Type'} (x : cart _143061 _143062) (f : type56 _143061 _143062) (h1 : f = (@EMPTY ((cart _143061 _143062) -> Prop))) : (term40 _143061 _143062 x f) = (term41 _143061 _143062 x).
Proof. exact (MK_COMB (@lem8050619) (@lem8050618 _143061 _143062 x f h1)). Qed.
Lemma lem8050621 {_143061 _143063 : Type'} (y : cart _143061 _143063) (t : type24 _143061 _143063) : (@IN (cart _143061 _143063) y t) = (@IN (cart _143061 _143063) y t).
Proof. exact (eq_refl (@IN (cart _143061 _143063) y t)). Qed.
Lemma lem8050622 {_143061 _143062 _143063 : Type'} (x : cart _143061 _143062) (y : cart _143061 _143063) (t : type24 _143061 _143063) (f : type56 _143061 _143062) (h1 : f = (@EMPTY ((cart _143061 _143062) -> Prop))) : (term37 _143061 _143062 _143063 x f y t) = (term42 _143061 _143062 _143063 x y t).
Proof. exact (MK_COMB (@lem8050620 _143061 _143062 x f h1) (@lem8050621 _143061 _143063 y t)). Qed.
Lemma lem8050625 {_143061 _143062 _143063 : Type'} (x : cart _143061 _143062) (y : cart _143061 _143063) (t : type24 _143061 _143063) (f : type56 _143061 _143062) (h1 : f = (@EMPTY ((cart _143061 _143062) -> Prop))) : (term28 _143061 _143062 _143063 x y f t) = (term42 _143061 _143062 _143063 x y t).
Proof. exact (TRANS (@lem8050610 _143061 _143062 _143063 x f y t) (@lem8050622 _143061 _143062 _143063 x y t f h1)). Qed.
Lemma lem8050626 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8050627 {_143061 _143062 _143063 : Type'} (x : cart _143061 _143062) (y : cart _143061 _143063) (t : type24 _143061 _143063) (f : type56 _143061 _143062) (h1 : f = (@EMPTY ((cart _143061 _143062) -> Prop))) : (term43 _143061 _143062 _143063 x y f t) = (term44 _143061 _143062 _143063 x y t).
Proof. exact (MK_COMB (@lem8050626) (@lem8050625 _143061 _143062 _143063 x y t f h1)). Qed.
Lemma lem8050629 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (y : cart _141927 _141929) (t : type24 _141927 _141929) : (term7 _141927 _141928 _141929 x y s t) = (term8 _141927 _141928 _141929 x s y t).
Proof. exact (EQ_MP (@lem8050493 _141927 _141928 _141929 x s y t) (@lem8050492 _141927 _141928 _141929 x s t y)). Qed.
Lemma lem8050630 {_143061 _143062 _143063 : Type'} (x : cart _143061 _143062) (s : type24 _143061 _143062) (y : cart _143061 _143063) (t : type24 _143061 _143063) : (term7 _143061 _143062 _143063 x y s t) = (term8 _143061 _143062 _143063 x s y t).
Proof. exact (@lem8050629 _143061 _143062 _143063 x s y t). Qed.
Lemma lem8050631 {_143061 _143062 _143063 : Type'} (x : cart _143061 _143062) (y : cart _143061 _143063) (t : type24 _143061 _143063) : (term29 _143061 _143062 _143063 x y t) = (term45 _143061 _143062 _143063 x y t).
Proof. exact (@lem8050630 _143061 _143062 _143063 x (@UNIV (cart _143061 _143062)) y t). Qed.
Lemma lem8050634 {_143061 _143062 _143063 : Type'} (x : cart _143061 _143062) (y : cart _143061 _143063) (t : type24 _143061 _143063) (f : type56 _143061 _143062) (h1 : f = (@EMPTY ((cart _143061 _143062) -> Prop))) : ((term28 _143061 _143062 _143063 x y f t) = (term29 _143061 _143062 _143063 x y t)) = ((term42 _143061 _143062 _143063 x y t) = (term45 _143061 _143062 _143063 x y t)).
Proof. exact (MK_COMB (@lem8050627 _143061 _143062 _143063 x y t f h1) (@lem8050631 _143061 _143062 _143063 x y t)). Qed.
Lemma lem8050639 {_143061 _143062 _143063 : Type'} (x : cart _143061 _143062) (t : type24 _143061 _143063) (f : type56 _143061 _143062) (h1 : f = (@EMPTY ((cart _143061 _143062) -> Prop))) : (term31 _143061 _143062 _143063 f x t) = (term46 _143061 _143062 _143063 x t).
Proof. exact (fun_ext (fun y : cart _143061 _143063 => @lem8050634 _143061 _143062 _143063 x y t f h1)). Qed.
Lemma lem8050640 {_143061 _143063 : Type'} : (@all (cart _143061 _143063)) = (@all (cart _143061 _143063)).
Proof. exact (eq_refl (@all (cart _143061 _143063))). Qed.
Lemma lem8050641 {_143061 _143062 _143063 : Type'} (x : cart _143061 _143062) (t : type24 _143061 _143063) (f : type56 _143061 _143062) (h1 : f = (@EMPTY ((cart _143061 _143062) -> Prop))) : (term33 _143061 _143062 _143063 f x t) = (term47 _143061 _143062 _143063 x t).
Proof. exact (MK_COMB (@lem8050640 _143061 _143063) (@lem8050639 _143061 _143062 _143063 x t f h1)). Qed.
Lemma lem8050648 {_143061 _143062 _143063 : Type'} (t : type24 _143061 _143063) (f : type56 _143061 _143062) (h1 : f = (@EMPTY ((cart _143061 _143062) -> Prop))) : (term35 _143061 _143062 _143063 f t) = (term48 _143061 _143062 _143063 t).
Proof. exact (fun_ext (fun x : cart _143061 _143062 => @lem8050641 _143061 _143062 _143063 x t f h1)). Qed.
Lemma lem8050649 {_143061 _143062 : Type'} : (@all (cart _143061 _143062)) = (@all (cart _143061 _143062)).
Proof. exact (eq_refl (@all (cart _143061 _143062))). Qed.
Lemma lem8050650 {_143061 _143062 _143063 : Type'} (t : type24 _143061 _143063) (f : type56 _143061 _143062) (h1 : f = (@EMPTY ((cart _143061 _143062) -> Prop))) : (term36 _143061 _143062 _143063 f t) = (term49 _143061 _143062 _143063 t).
Proof. exact (MK_COMB (@lem8050649 _143061 _143062) (@lem8050648 _143061 _143062 _143063 t f h1)). Qed.
Lemma lem8050657 {_143061 _143062 _143063 : Type'} (t : type24 _143061 _143063) (f : type56 _143061 _143062) (h1 : f = (@EMPTY ((cart _143061 _143062) -> Prop))) : ((term14 _143061 _143062 _143063 f t) = (@PCROSS _143061 _143062 _143063 (@UNIV (cart _143061 _143062)) t)) = (term49 _143061 _143062 _143063 t).
Proof. exact (TRANS (@lem8050596 _143061 _143062 _143063 f t) (@lem8050650 _143061 _143062 _143063 t f h1)). Qed.
Lemma lem8050658 {_143061 _143062 _143063 : Type'} (t : type24 _143061 _143063) (f : type56 _143061 _143062) (h1 : f = (@EMPTY ((cart _143061 _143062) -> Prop))) : (term49 _143061 _143062 _143063 t) = ((term14 _143061 _143062 _143063 f t) = (@PCROSS _143061 _143062 _143063 (@UNIV (cart _143061 _143062)) t)).
Proof. exact (SYM (@lem8050657 _143061 _143062 _143063 t f h1)). Qed.
