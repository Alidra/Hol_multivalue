Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7603578_term_abbrevs.
Require Import EXTENSION_spec.
Require Import IN_IMAGE_spec.
Require Import IN_UNIV_spec.
Require Import thm1855_spec.
Require Import thm7_spec.
Lemma lem7603502 {A B : Type'} (y : B) : term0 A B y.
Proof. exact (@lem3206070 A B y). Qed.
Lemma lem7603503 {A B : Type'} (y : B) : (term0 A B y) = (term1 A B y).
Proof. exact (eq_refl (term0 A B y)). Qed.
Lemma lem7603504 {A B : Type'} (y : B) : term1 A B y.
Proof. exact (EQ_MP (@lem7603503 A B y) (@lem7603502 A B y)). Qed.
Lemma lem7603505 {A B : Type'} (y : B) (s : A -> Prop) : term2 A B y s.
Proof. exact (@lem7603504 A B y s). Qed.
Lemma lem7603506 {A B : Type'} (y : B) (s : A -> Prop) : (term2 A B y s) = (term3 A B y s).
Proof. exact (eq_refl (term2 A B y s)). Qed.
Lemma lem7603507 {A B : Type'} (y : B) (s : A -> Prop) : term3 A B y s.
Proof. exact (EQ_MP (@lem7603506 A B y s) (@lem7603505 A B y s)). Qed.
Lemma lem7603508 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) : term4 A B y s f.
Proof. exact (@lem7603507 A B y s f). Qed.
Lemma lem7603509 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term4 A B y s f) = ((term5 A B y f s) = (term6 A B y f s)).
Proof. exact (eq_refl (term4 A B y s f)). Qed.
Lemma lem7603511 {A : Type'} (x : A) : term7 A x.
Proof. exact (@lem3204818 A x). Qed.
Lemma lem7603512 {A : Type'} (x : A) : (term7 A x) = (@IN A x (@UNIV A)).
Proof. exact (eq_refl (term7 A x)). Qed.
Lemma lem7603513 {A : Type'} (x : A) : @IN A x (@UNIV A).
Proof. exact (EQ_MP (@lem7603512 A x) (@lem7603511 A x)). Qed.
Lemma lem7603514 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = ((@IN A x (@UNIV A)) = True).
Proof. exact (@lem7 (@IN A x (@UNIV A))). Qed.
Lemma lem7603516 {A : Type'} (s : A -> Prop) : term8 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem7603517 {A : Type'} (s : A -> Prop) : (term8 A s) = (term9 A s).
Proof. exact (eq_refl (term8 A s)). Qed.
Lemma lem7603518 {A : Type'} (s : A -> Prop) : term9 A s.
Proof. exact (EQ_MP (@lem7603517 A s) (@lem7603516 A s)). Qed.
Lemma lem7603519 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term10 A s t.
Proof. exact (@lem7603518 A s t). Qed.
Lemma lem7603520 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term10 A s t) = ((s = t) = (term11 A s t)).
Proof. exact (eq_refl (term10 A s t)). Qed.
Lemma lem7603525 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term11 A s t).
Proof. exact (EQ_MP (@lem7603520 A s t) (@lem7603519 A s t)). Qed.
Lemma lem7603526 {A : Type'} (s : type33 A) (t : type33 A) : (s = t) = (term12 A s t).
Proof. exact (@lem7603525 (finite_image A) s t). Qed.
Lemma lem7603527 {A : Type'} : ((@UNIV (finite_image A)) = (term13 A)) = (term14 A).
Proof. exact (@lem7603526 A (@UNIV (finite_image A)) (term13 A)). Qed.
Lemma lem7603537 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem7603514 A x) (@lem7603513 A x)). Qed.
Lemma lem7603538 {A : Type'} (x : finite_image A) : (@IN (finite_image A) x (@UNIV (finite_image A))) = True.
Proof. exact (@lem7603537 (finite_image A) x). Qed.
Lemma lem7603539 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7603540 {A : Type'} (x : finite_image A) : (term15 A x) = (@eq Prop True).
Proof. exact (MK_COMB (@lem7603539) (@lem7603538 A x)). Qed.
Lemma lem7603542 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term5 A B y f s) = (term6 A B y f s).
Proof. exact (EQ_MP (@lem7603509 A B y f s) (@lem7603508 A B y s f)). Qed.
Lemma lem7603543 {A : Type'} (y : finite_image A) (f : type1557 A) (s : nat -> Prop) : (term16 A y f s) = (term17 A y f s).
Proof. exact (@lem7603542 nat (finite_image A) y f s). Qed.
Lemma lem7603544 {A : Type'} (x : finite_image A) : (term18 A x) = (term19 A x).
Proof. exact (@lem7603543 A x (@finite_index A) (term20 A)). Qed.
Lemma lem7603555 {A : Type'} (x : finite_image A) : ((@IN (finite_image A) x (@UNIV (finite_image A))) = (term18 A x)) = (True = (term19 A x)).
Proof. exact (MK_COMB (@lem7603540 A x) (@lem7603544 A x)). Qed.
Lemma lem7603557 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem7603558 {A : Type'} (x : finite_image A) : (True = (term19 A x)) = (term19 A x).
Proof. exact (@lem7603557 (term19 A x)). Qed.
Lemma lem7603569 {A : Type'} (x : finite_image A) : ((@IN (finite_image A) x (@UNIV (finite_image A))) = (term18 A x)) = (term19 A x).
Proof. exact (TRANS (@lem7603555 A x) (@lem7603558 A x)). Qed.
Lemma lem7603570 {A : Type'} : (term21 A) = (term22 A).
Proof. exact (fun_ext (fun x : finite_image A => @lem7603569 A x)). Qed.
Lemma lem7603571 {A : Type'} : (@all (finite_image A)) = (@all (finite_image A)).
Proof. exact (eq_refl (@all (finite_image A))). Qed.
Lemma lem7603572 {A : Type'} : (term14 A) = (term23 A).
Proof. exact (MK_COMB (@lem7603571 A) (@lem7603570 A)). Qed.
Lemma lem7603577 {A : Type'} : ((@UNIV (finite_image A)) = (term13 A)) = (term23 A).
Proof. exact (TRANS (@lem7603527 A) (@lem7603572 A)). Qed.
Lemma lem7603578 {A : Type'} : (term23 A) = ((@UNIV (finite_image A)) = (term13 A)).
Proof. exact (SYM (@lem7603577 A)). Qed.
