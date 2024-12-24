Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import IMAGE_INTER_SUBSET_term_abbrevs.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm18394_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211656_spec.
Require Import thm3211657_spec.
Require Import thm3211710_spec.
Require Import thm3211711_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Lemma lem3487360 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3487361 {_90546 : Type'} (s : _90546 -> Prop) (t : _90546 -> Prop) : (@SUBSET _90546 s t) = (term0 _90546 s t).
Proof. exact (@lem3487360 _90546 s t). Qed.
Lemma lem3487362 {_90535 _90546 : Type'} (s : _90535 -> Prop) (f : _90535 -> _90546) (t : _90535 -> Prop) : (term1 _90535 _90546 s f t) = (term2 _90535 _90546 s f t).
Proof. exact (@lem3487361 _90546 (term3 _90535 _90546 f s t) (term4 _90535 _90546 s f t)). Qed.
Lemma lem3487369 {_90535 _90546 : Type'} (s : _90535 -> Prop) (f : _90535 -> _90546) : (term5 _90535 _90546 s f) = (term6 _90535 _90546 s f).
Proof. exact (fun_ext (fun t : _90535 -> Prop => @lem3487362 _90535 _90546 s f t)). Qed.
Lemma lem3487370 {_90535 : Type'} : (@all (_90535 -> Prop)) = (@all (_90535 -> Prop)).
Proof. exact (eq_refl (@all (_90535 -> Prop))). Qed.
Lemma lem3487371 {_90535 _90546 : Type'} (s : _90535 -> Prop) (f : _90535 -> _90546) : (term7 _90535 _90546 s f) = (term8 _90535 _90546 s f).
Proof. exact (MK_COMB (@lem3487370 _90535) (@lem3487369 _90535 _90546 s f)). Qed.
Lemma lem3487376 {_90535 _90546 : Type'} (f : _90535 -> _90546) : (term9 _90535 _90546 f) = (term10 _90535 _90546 f).
Proof. exact (fun_ext (fun s : _90535 -> Prop => @lem3487371 _90535 _90546 s f)). Qed.
Lemma lem3487377 {_90535 : Type'} : (@all (_90535 -> Prop)) = (@all (_90535 -> Prop)).
Proof. exact (eq_refl (@all (_90535 -> Prop))). Qed.
Lemma lem3487378 {_90535 _90546 : Type'} (f : _90535 -> _90546) : (term11 _90535 _90546 f) = (term12 _90535 _90546 f).
Proof. exact (MK_COMB (@lem3487377 _90535) (@lem3487376 _90535 _90546 f)). Qed.
Lemma lem3487383 {_90535 _90546 : Type'} : (term13 _90535 _90546) = (term14 _90535 _90546).
Proof. exact (fun_ext (fun f : _90535 -> _90546 => @lem3487378 _90535 _90546 f)). Qed.
Lemma lem3487384 {_90535 _90546 : Type'} : (@all (_90535 -> _90546)) = (@all (_90535 -> _90546)).
Proof. exact (eq_refl (@all (_90535 -> _90546))). Qed.
Lemma lem3487385 {_90535 _90546 : Type'} : (term15 _90535 _90546) = (term16 _90535 _90546).
Proof. exact (MK_COMB (@lem3487384 _90535 _90546) (@lem3487383 _90535 _90546)). Qed.
Lemma lem3487390 {_90535 _90546 : Type'} : (term16 _90535 _90546) = (term15 _90535 _90546).
Proof. exact (SYM (@lem3487385 _90535 _90546)). Qed.
Lemma lem3487410 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term17 A B y f s) = (term18 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem3487411 {_90535 _90546 : Type'} (y : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) : (term17 _90535 _90546 y f s) = (term18 _90535 _90546 y f s).
Proof. exact (@lem3487410 _90535 _90546 y f s). Qed.
Lemma lem3487412 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) (t : _90535 -> Prop) : (term19 _90535 _90546 x f s t) = (term20 _90535 _90546 x f s t).
Proof. exact (@lem3487411 _90535 _90546 x f (@INTER _90535 s t)). Qed.
Lemma lem3487422 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term21 A x s t) = (term22 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3487423 {_90535 : Type'} (s : _90535 -> Prop) (x : _90535) (t : _90535 -> Prop) : (term21 _90535 x s t) = (term22 _90535 s x t).
Proof. exact (@lem3487422 _90535 s x t). Qed.
Lemma lem3487427 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3487428 {_90535 : Type'} (P : _90535 -> Prop) (x : _90535) : (@IN _90535 x P) = (P x).
Proof. exact (@lem3487427 _90535 P x). Qed.
Lemma lem3487429 {_90535 : Type'} (s : _90535 -> Prop) (x : _90535) : (@IN _90535 x s) = (s x).
Proof. exact (@lem3487428 _90535 s x). Qed.
Lemma lem3487430 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3487431 {_90535 : Type'} (s : _90535 -> Prop) (x : _90535) : (term23 _90535 x s) = (term24 _90535 s x).
Proof. exact (MK_COMB (@lem3487430) (@lem3487429 _90535 s x)). Qed.
Lemma lem3487433 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3487434 {_90535 : Type'} (P : _90535 -> Prop) (x : _90535) : (@IN _90535 x P) = (P x).
Proof. exact (@lem3487433 _90535 P x). Qed.
Lemma lem3487435 {_90535 : Type'} (t : _90535 -> Prop) (x : _90535) : (@IN _90535 x t) = (t x).
Proof. exact (@lem3487434 _90535 t x). Qed.
Lemma lem3487436 {_90535 : Type'} (s : _90535 -> Prop) (t : _90535 -> Prop) (x : _90535) : (term22 _90535 s x t) = (term25 _90535 s t x).
Proof. exact (MK_COMB (@lem3487431 _90535 s x) (@lem3487435 _90535 t x)). Qed.
Lemma lem3487439 {_90535 : Type'} (s : _90535 -> Prop) (t : _90535 -> Prop) (x : _90535) : (term21 _90535 x s t) = (term25 _90535 s t x).
Proof. exact (TRANS (@lem3487423 _90535 s x t) (@lem3487436 _90535 s t x)). Qed.
Lemma lem3487440 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (x' : _90535) : (term26 _90535 _90546 x f x') = (term26 _90535 _90546 x f x').
Proof. exact (eq_refl (term26 _90535 _90546 x f x')). Qed.
Lemma lem3487441 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) (t : _90535 -> Prop) (x' : _90535) : (term27 _90535 _90546 x f x' s t) = (term28 _90535 _90546 x f s t x').
Proof. exact (MK_COMB (@lem3487440 _90535 _90546 x f x') (@lem3487439 _90535 s t x')). Qed.
Lemma lem3487444 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) (t : _90535 -> Prop) : (term29 _90535 _90546 x f s t) = (term30 _90535 _90546 x f s t).
Proof. exact (fun_ext (fun x' : _90535 => @lem3487441 _90535 _90546 x f s t x')). Qed.
Lemma lem3487445 {_90535 : Type'} : (@ex _90535) = (@ex _90535).
Proof. exact (eq_refl (@ex _90535)). Qed.
Lemma lem3487446 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) (t : _90535 -> Prop) : (term20 _90535 _90546 x f s t) = (term31 _90535 _90546 x f s t).
Proof. exact (MK_COMB (@lem3487445 _90535) (@lem3487444 _90535 _90546 x f s t)). Qed.
Lemma lem3487451 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) (t : _90535 -> Prop) : (term19 _90535 _90546 x f s t) = (term31 _90535 _90546 x f s t).
Proof. exact (TRANS (@lem3487412 _90535 _90546 x f s t) (@lem3487446 _90535 _90546 x f s t)). Qed.
Lemma lem3487452 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3487453 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) (t : _90535 -> Prop) : (term32 _90535 _90546 x f s t) = (term33 _90535 _90546 x f s t).
Proof. exact (MK_COMB (@lem3487452) (@lem3487451 _90535 _90546 x f s t)). Qed.
Lemma lem3487455 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term21 A x s t) = (term22 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3487456 {_90546 : Type'} (s : _90546 -> Prop) (x : _90546) (t : _90546 -> Prop) : (term21 _90546 x s t) = (term22 _90546 s x t).
Proof. exact (@lem3487455 _90546 s x t). Qed.
Lemma lem3487457 {_90535 _90546 : Type'} (s : _90535 -> Prop) (x : _90546) (f : _90535 -> _90546) (t : _90535 -> Prop) : (term34 _90535 _90546 x s f t) = (term35 _90535 _90546 s x f t).
Proof. exact (@lem3487456 _90546 (@IMAGE _90535 _90546 f s) x (@IMAGE _90535 _90546 f t)). Qed.
Lemma lem3487461 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term17 A B y f s) = (term18 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem3487462 {_90535 _90546 : Type'} (y : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) : (term17 _90535 _90546 y f s) = (term18 _90535 _90546 y f s).
Proof. exact (@lem3487461 _90535 _90546 y f s). Qed.
Lemma lem3487463 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) : (term17 _90535 _90546 x f s) = (term18 _90535 _90546 x f s).
Proof. exact (@lem3487462 _90535 _90546 x f s). Qed.
Lemma lem3487473 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3487474 {_90535 : Type'} (P : _90535 -> Prop) (x : _90535) : (@IN _90535 x P) = (P x).
Proof. exact (@lem3487473 _90535 P x). Qed.
Lemma lem3487475 {_90535 : Type'} (s : _90535 -> Prop) (x : _90535) : (@IN _90535 x s) = (s x).
Proof. exact (@lem3487474 _90535 s x). Qed.
Lemma lem3487476 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (x' : _90535) : (term26 _90535 _90546 x f x') = (term26 _90535 _90546 x f x').
Proof. exact (eq_refl (term26 _90535 _90546 x f x')). Qed.
Lemma lem3487477 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) (x' : _90535) : (term36 _90535 _90546 x f x' s) = (term37 _90535 _90546 x f s x').
Proof. exact (MK_COMB (@lem3487476 _90535 _90546 x f x') (@lem3487475 _90535 s x')). Qed.
Lemma lem3487480 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) : (term38 _90535 _90546 x f s) = (term39 _90535 _90546 x f s).
Proof. exact (fun_ext (fun x' : _90535 => @lem3487477 _90535 _90546 x f s x')). Qed.
Lemma lem3487481 {_90535 : Type'} : (@ex _90535) = (@ex _90535).
Proof. exact (eq_refl (@ex _90535)). Qed.
Lemma lem3487482 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) : (term18 _90535 _90546 x f s) = (term40 _90535 _90546 x f s).
Proof. exact (MK_COMB (@lem3487481 _90535) (@lem3487480 _90535 _90546 x f s)). Qed.
Lemma lem3487487 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) : (term17 _90535 _90546 x f s) = (term40 _90535 _90546 x f s).
Proof. exact (TRANS (@lem3487463 _90535 _90546 x f s) (@lem3487482 _90535 _90546 x f s)). Qed.
Lemma lem3487488 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3487489 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) : (term41 _90535 _90546 x f s) = (term42 _90535 _90546 x f s).
Proof. exact (MK_COMB (@lem3487488) (@lem3487487 _90535 _90546 x f s)). Qed.
Lemma lem3487491 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term17 A B y f s) = (term18 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem3487492 {_90535 _90546 : Type'} (y : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) : (term17 _90535 _90546 y f s) = (term18 _90535 _90546 y f s).
Proof. exact (@lem3487491 _90535 _90546 y f s). Qed.
Lemma lem3487493 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (t : _90535 -> Prop) : (term17 _90535 _90546 x f t) = (term18 _90535 _90546 x f t).
Proof. exact (@lem3487492 _90535 _90546 x f t). Qed.
Lemma lem3487503 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3487504 {_90535 : Type'} (P : _90535 -> Prop) (x : _90535) : (@IN _90535 x P) = (P x).
Proof. exact (@lem3487503 _90535 P x). Qed.
Lemma lem3487505 {_90535 : Type'} (t : _90535 -> Prop) (x : _90535) : (@IN _90535 x t) = (t x).
Proof. exact (@lem3487504 _90535 t x). Qed.
Lemma lem3487506 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (x' : _90535) : (term26 _90535 _90546 x f x') = (term26 _90535 _90546 x f x').
Proof. exact (eq_refl (term26 _90535 _90546 x f x')). Qed.
Lemma lem3487507 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (t : _90535 -> Prop) (x' : _90535) : (term36 _90535 _90546 x f x' t) = (term37 _90535 _90546 x f t x').
Proof. exact (MK_COMB (@lem3487506 _90535 _90546 x f x') (@lem3487505 _90535 t x')). Qed.
Lemma lem3487510 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (t : _90535 -> Prop) : (term38 _90535 _90546 x f t) = (term39 _90535 _90546 x f t).
Proof. exact (fun_ext (fun x' : _90535 => @lem3487507 _90535 _90546 x f t x')). Qed.
Lemma lem3487511 {_90535 : Type'} : (@ex _90535) = (@ex _90535).
Proof. exact (eq_refl (@ex _90535)). Qed.
Lemma lem3487512 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (t : _90535 -> Prop) : (term18 _90535 _90546 x f t) = (term40 _90535 _90546 x f t).
Proof. exact (MK_COMB (@lem3487511 _90535) (@lem3487510 _90535 _90546 x f t)). Qed.
Lemma lem3487517 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (t : _90535 -> Prop) : (term17 _90535 _90546 x f t) = (term40 _90535 _90546 x f t).
Proof. exact (TRANS (@lem3487493 _90535 _90546 x f t) (@lem3487512 _90535 _90546 x f t)). Qed.
Lemma lem3487518 {_90535 _90546 : Type'} (s : _90535 -> Prop) (x : _90546) (f : _90535 -> _90546) (t : _90535 -> Prop) : (term35 _90535 _90546 s x f t) = (term43 _90535 _90546 s x f t).
Proof. exact (MK_COMB (@lem3487489 _90535 _90546 x f s) (@lem3487517 _90535 _90546 x f t)). Qed.
Lemma lem3487521 {_90535 _90546 : Type'} (s : _90535 -> Prop) (x : _90546) (f : _90535 -> _90546) (t : _90535 -> Prop) : (term34 _90535 _90546 x s f t) = (term43 _90535 _90546 s x f t).
Proof. exact (TRANS (@lem3487457 _90535 _90546 s x f t) (@lem3487518 _90535 _90546 s x f t)). Qed.
Lemma lem3487522 {_90535 _90546 : Type'} (s : _90535 -> Prop) (x : _90546) (f : _90535 -> _90546) (t : _90535 -> Prop) : (term44 _90535 _90546 x s f t) = (term45 _90535 _90546 s x f t).
Proof. exact (MK_COMB (@lem3487453 _90535 _90546 x f s t) (@lem3487521 _90535 _90546 s x f t)). Qed.
Lemma lem3487525 {_90535 _90546 : Type'} (s : _90535 -> Prop) (f : _90535 -> _90546) (t : _90535 -> Prop) : (term46 _90535 _90546 s f t) = (term47 _90535 _90546 s f t).
Proof. exact (fun_ext (fun x : _90546 => @lem3487522 _90535 _90546 s x f t)). Qed.
Lemma lem3487526 {_90546 : Type'} : (@all _90546) = (@all _90546).
Proof. exact (eq_refl (@all _90546)). Qed.
Lemma lem3487527 {_90535 _90546 : Type'} (s : _90535 -> Prop) (f : _90535 -> _90546) (t : _90535 -> Prop) : (term2 _90535 _90546 s f t) = (term48 _90535 _90546 s f t).
Proof. exact (MK_COMB (@lem3487526 _90546) (@lem3487525 _90535 _90546 s f t)). Qed.
Lemma lem3487532 {_90535 _90546 : Type'} (s : _90535 -> Prop) (f : _90535 -> _90546) : (term6 _90535 _90546 s f) = (term49 _90535 _90546 s f).
Proof. exact (fun_ext (fun t : _90535 -> Prop => @lem3487527 _90535 _90546 s f t)). Qed.
Lemma lem3487533 {_90535 : Type'} : (@all (_90535 -> Prop)) = (@all (_90535 -> Prop)).
Proof. exact (eq_refl (@all (_90535 -> Prop))). Qed.
Lemma lem3487534 {_90535 _90546 : Type'} (s : _90535 -> Prop) (f : _90535 -> _90546) : (term8 _90535 _90546 s f) = (term50 _90535 _90546 s f).
Proof. exact (MK_COMB (@lem3487533 _90535) (@lem3487532 _90535 _90546 s f)). Qed.
Lemma lem3487539 {_90535 _90546 : Type'} (f : _90535 -> _90546) : (term10 _90535 _90546 f) = (term51 _90535 _90546 f).
Proof. exact (fun_ext (fun s : _90535 -> Prop => @lem3487534 _90535 _90546 s f)). Qed.
Lemma lem3487540 {_90535 : Type'} : (@all (_90535 -> Prop)) = (@all (_90535 -> Prop)).
Proof. exact (eq_refl (@all (_90535 -> Prop))). Qed.
Lemma lem3487541 {_90535 _90546 : Type'} (f : _90535 -> _90546) : (term12 _90535 _90546 f) = (term52 _90535 _90546 f).
Proof. exact (MK_COMB (@lem3487540 _90535) (@lem3487539 _90535 _90546 f)). Qed.
Lemma lem3487546 {_90535 _90546 : Type'} : (term14 _90535 _90546) = (term53 _90535 _90546).
Proof. exact (fun_ext (fun f : _90535 -> _90546 => @lem3487541 _90535 _90546 f)). Qed.
Lemma lem3487547 {_90535 _90546 : Type'} : (@all (_90535 -> _90546)) = (@all (_90535 -> _90546)).
Proof. exact (eq_refl (@all (_90535 -> _90546))). Qed.
Lemma lem3487548 {_90535 _90546 : Type'} : (term16 _90535 _90546) = (term54 _90535 _90546).
Proof. exact (MK_COMB (@lem3487547 _90535 _90546) (@lem3487546 _90535 _90546)). Qed.
Lemma lem3487553 {_90535 _90546 : Type'} : (term54 _90535 _90546) = (term16 _90535 _90546).
Proof. exact (SYM (@lem3487548 _90535 _90546)). Qed.
Lemma lem3487555 (p : Prop) : p = (term55 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3487556 {_90535 _90546 : Type'} : (term54 _90535 _90546) = (term56 _90535 _90546).
Proof. exact (@lem3487555 (term54 _90535 _90546)). Qed.
Lemma lem3487557 {_90535 _90546 : Type'} : (term56 _90535 _90546) = (term54 _90535 _90546).
Proof. exact (SYM (@lem3487556 _90535 _90546)). Qed.
Lemma lem3487558 {_90535 _90546 : Type'} (h1 : term57 _90535 _90546) : term57 _90535 _90546.
Proof. exact (h1). Qed.
Lemma lem3487561 {_90535 _90546 : Type'} (h1 : term56 _90535 _90546) : term56 _90535 _90546.
Proof. exact (h1). Qed.
Lemma lem3487562 {_90535 _90546 : Type'} : term58 _90535 _90546.
Proof. exact (fun h0 : term56 _90535 _90546 => @lem3487561 _90535 _90546 h0). Qed.
Lemma lem3487563 {_90535 _90546 : Type'} (h1 : term58 _90535 _90546) : term58 _90535 _90546.
Proof. exact (h1). Qed.
Lemma lem3487564 {_90535 _90546 : Type'} (h1 : term56 _90535 _90546) : term56 _90535 _90546.
Proof. exact (h1). Qed.
Lemma lem3487565 {_90535 _90546 : Type'} (h1 : term56 _90535 _90546) (h2 : term58 _90535 _90546) : term56 _90535 _90546.
Proof. exact (@lem3487563 _90535 _90546 h2 (@lem3487564 _90535 _90546 h1)). Qed.
Lemma lem3487566 {_90535 _90546 : Type'} (h1 : term56 _90535 _90546) : term59 _90535 _90546.
Proof. exact (fun h0 : term58 _90535 _90546 => @lem3487565 _90535 _90546 h1 h0). Qed.
Lemma lem3487567 {_90535 _90546 : Type'} (h1 : term58 _90535 _90546) : term58 _90535 _90546.
Proof. exact (h1). Qed.
Lemma lem3487568 {_90535 _90546 : Type'} (h1 : term56 _90535 _90546) (h2 : term58 _90535 _90546) : term56 _90535 _90546.
Proof. exact (@lem3487566 _90535 _90546 h1 (@lem3487567 _90535 _90546 h2)). Qed.
Lemma lem3487569 {_90535 _90546 : Type'} (h1 : term58 _90535 _90546) : term58 _90535 _90546.
Proof. exact (fun h0 : term56 _90535 _90546 => @lem3487568 _90535 _90546 h0 h1). Qed.
Lemma lem3487570 {_90535 _90546 : Type'} : term60 _90535 _90546.
Proof. exact (fun h0 : term58 _90535 _90546 => @lem3487569 _90535 _90546 h0). Qed.
Lemma lem3487573 {_90535 _90546 : Type'} : term58 _90535 _90546.
Proof. exact (@lem3487570 _90535 _90546 (@lem3487562 _90535 _90546)). Qed.
Lemma lem3487574 {_90535 _90546 : Type'} : term58 _90535 _90546.
Proof. exact (@lem3487573 _90535 _90546). Qed.
Lemma lem3487576 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3487577 {_90535 _90546 : Type'} : (term56 _90535 _90546) = (term61 _90535 _90546).
Proof. exact (@lem3487576 (term57 _90535 _90546)). Qed.
Lemma lem3487579 (t : Prop) : (term62 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3487580 {_90535 _90546 : Type'} : (term61 _90535 _90546) = (term54 _90535 _90546).
Proof. exact (@lem3487579 (term54 _90535 _90546)). Qed.
Lemma lem3487725 {_90535 _90546 : Type'} : (term56 _90535 _90546) = (term54 _90535 _90546).
Proof. exact (TRANS (@lem3487577 _90535 _90546) (@lem3487580 _90535 _90546)). Qed.
Lemma lem3487730 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (t : _90535 -> Prop) (x' : _90535) : (term37 _90535 _90546 x f t x') = (term37 _90535 _90546 x f t x').
Proof. exact (eq_refl (term37 _90535 _90546 x f t x')). Qed.
Lemma lem3487731 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (t : _90535 -> Prop) : (term39 _90535 _90546 x f t) = (term39 _90535 _90546 x f t).
Proof. exact (fun_ext (fun x' : _90535 => @lem3487730 _90535 _90546 x f t x')). Qed.
Lemma lem3487732 {_90535 : Type'} : (@ex _90535) = (@ex _90535).
Proof. exact (eq_refl (@ex _90535)). Qed.
Lemma lem3487733 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (t : _90535 -> Prop) : (term40 _90535 _90546 x f t) = (term40 _90535 _90546 x f t).
Proof. exact (MK_COMB (@lem3487732 _90535) (@lem3487731 _90535 _90546 x f t)). Qed.
Lemma lem3487738 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) (x' : _90535) : (term37 _90535 _90546 x f s x') = (term37 _90535 _90546 x f s x').
Proof. exact (eq_refl (term37 _90535 _90546 x f s x')). Qed.
Lemma lem3487739 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) : (term39 _90535 _90546 x f s) = (term39 _90535 _90546 x f s).
Proof. exact (fun_ext (fun x' : _90535 => @lem3487738 _90535 _90546 x f s x')). Qed.
Lemma lem3487740 {_90535 : Type'} : (@ex _90535) = (@ex _90535).
Proof. exact (eq_refl (@ex _90535)). Qed.
Lemma lem3487741 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) : (term40 _90535 _90546 x f s) = (term40 _90535 _90546 x f s).
Proof. exact (MK_COMB (@lem3487740 _90535) (@lem3487739 _90535 _90546 x f s)). Qed.
Lemma lem3487742 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3487743 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) : (term42 _90535 _90546 x f s) = (term42 _90535 _90546 x f s).
Proof. exact (MK_COMB (@lem3487742) (@lem3487741 _90535 _90546 x f s)). Qed.
Lemma lem3487744 {_90535 _90546 : Type'} (s : _90535 -> Prop) (x : _90546) (f : _90535 -> _90546) (t : _90535 -> Prop) : (term43 _90535 _90546 s x f t) = (term43 _90535 _90546 s x f t).
Proof. exact (MK_COMB (@lem3487743 _90535 _90546 x f s) (@lem3487733 _90535 _90546 x f t)). Qed.
Lemma lem3487753 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) (t : _90535 -> Prop) (x' : _90535) : (term28 _90535 _90546 x f s t x') = (term28 _90535 _90546 x f s t x').
Proof. exact (eq_refl (term28 _90535 _90546 x f s t x')). Qed.
Lemma lem3487754 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) (t : _90535 -> Prop) : (term30 _90535 _90546 x f s t) = (term30 _90535 _90546 x f s t).
Proof. exact (fun_ext (fun x' : _90535 => @lem3487753 _90535 _90546 x f s t x')). Qed.
Lemma lem3487755 {_90535 : Type'} : (@ex _90535) = (@ex _90535).
Proof. exact (eq_refl (@ex _90535)). Qed.
Lemma lem3487756 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) (t : _90535 -> Prop) : (term31 _90535 _90546 x f s t) = (term31 _90535 _90546 x f s t).
Proof. exact (MK_COMB (@lem3487755 _90535) (@lem3487754 _90535 _90546 x f s t)). Qed.
Lemma lem3487757 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3487758 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) (t : _90535 -> Prop) : (term33 _90535 _90546 x f s t) = (term33 _90535 _90546 x f s t).
Proof. exact (MK_COMB (@lem3487757) (@lem3487756 _90535 _90546 x f s t)). Qed.
Lemma lem3487759 {_90535 _90546 : Type'} (s : _90535 -> Prop) (x : _90546) (f : _90535 -> _90546) (t : _90535 -> Prop) : (term45 _90535 _90546 s x f t) = (term45 _90535 _90546 s x f t).
Proof. exact (MK_COMB (@lem3487758 _90535 _90546 x f s t) (@lem3487744 _90535 _90546 s x f t)). Qed.
Lemma lem3487760 {_90535 _90546 : Type'} (s : _90535 -> Prop) (f : _90535 -> _90546) (t : _90535 -> Prop) : (term47 _90535 _90546 s f t) = (term47 _90535 _90546 s f t).
Proof. exact (fun_ext (fun x : _90546 => @lem3487759 _90535 _90546 s x f t)). Qed.
Lemma lem3487761 {_90546 : Type'} : (@all _90546) = (@all _90546).
Proof. exact (eq_refl (@all _90546)). Qed.
Lemma lem3487762 {_90535 _90546 : Type'} (s : _90535 -> Prop) (f : _90535 -> _90546) (t : _90535 -> Prop) : (term48 _90535 _90546 s f t) = (term48 _90535 _90546 s f t).
Proof. exact (MK_COMB (@lem3487761 _90546) (@lem3487760 _90535 _90546 s f t)). Qed.
Lemma lem3487763 {_90535 _90546 : Type'} (s : _90535 -> Prop) (f : _90535 -> _90546) : (term49 _90535 _90546 s f) = (term49 _90535 _90546 s f).
Proof. exact (fun_ext (fun t : _90535 -> Prop => @lem3487762 _90535 _90546 s f t)). Qed.
Lemma lem3487764 {_90535 : Type'} : (@all (_90535 -> Prop)) = (@all (_90535 -> Prop)).
Proof. exact (eq_refl (@all (_90535 -> Prop))). Qed.
Lemma lem3487765 {_90535 _90546 : Type'} (s : _90535 -> Prop) (f : _90535 -> _90546) : (term50 _90535 _90546 s f) = (term50 _90535 _90546 s f).
Proof. exact (MK_COMB (@lem3487764 _90535) (@lem3487763 _90535 _90546 s f)). Qed.
Lemma lem3487766 {_90535 _90546 : Type'} (f : _90535 -> _90546) : (term51 _90535 _90546 f) = (term51 _90535 _90546 f).
Proof. exact (fun_ext (fun s : _90535 -> Prop => @lem3487765 _90535 _90546 s f)). Qed.
Lemma lem3487767 {_90535 : Type'} : (@all (_90535 -> Prop)) = (@all (_90535 -> Prop)).
Proof. exact (eq_refl (@all (_90535 -> Prop))). Qed.
Lemma lem3487768 {_90535 _90546 : Type'} (f : _90535 -> _90546) : (term52 _90535 _90546 f) = (term52 _90535 _90546 f).
Proof. exact (MK_COMB (@lem3487767 _90535) (@lem3487766 _90535 _90546 f)). Qed.
Lemma lem3487769 {_90535 _90546 : Type'} : (term53 _90535 _90546) = (term53 _90535 _90546).
Proof. exact (fun_ext (fun f : _90535 -> _90546 => @lem3487768 _90535 _90546 f)). Qed.
Lemma lem3487770 {_90535 _90546 : Type'} : (@all (_90535 -> _90546)) = (@all (_90535 -> _90546)).
Proof. exact (eq_refl (@all (_90535 -> _90546))). Qed.
Lemma lem3487771 {_90535 _90546 : Type'} : (term54 _90535 _90546) = (term54 _90535 _90546).
Proof. exact (MK_COMB (@lem3487770 _90535 _90546) (@lem3487769 _90535 _90546)). Qed.
Lemma lem3487828 {_90535 _90546 : Type'} : (term56 _90535 _90546) = (term54 _90535 _90546).
Proof. exact (TRANS (@lem3487725 _90535 _90546) (@lem3487771 _90535 _90546)). Qed.
Lemma lem3487829 {_90535 _90546 : Type'} : (term54 _90535 _90546) = (term56 _90535 _90546).
Proof. exact (SYM (@lem3487828 _90535 _90546)). Qed.
Lemma lem3487830 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) (t : _90535 -> Prop) (h1 : term31 _90535 _90546 x f s t) : term31 _90535 _90546 x f s t.
Proof. exact (h1). Qed.
Lemma lem3487832 (p : Prop) : p = (term55 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3487833 {_90535 _90546 : Type'} (s : _90535 -> Prop) (x : _90546) (f : _90535 -> _90546) (t : _90535 -> Prop) : (term43 _90535 _90546 s x f t) = (term63 _90535 _90546 s x f t).
Proof. exact (@lem3487832 (term43 _90535 _90546 s x f t)). Qed.
Lemma lem3487834 {_90535 _90546 : Type'} (s : _90535 -> Prop) (x : _90546) (f : _90535 -> _90546) (t : _90535 -> Prop) : (term63 _90535 _90546 s x f t) = (term43 _90535 _90546 s x f t).
Proof. exact (SYM (@lem3487833 _90535 _90546 s x f t)). Qed.
Lemma lem3487835 {_90535 _90546 : Type'} (s : _90535 -> Prop) (x : _90546) (f : _90535 -> _90546) (t : _90535 -> Prop) (h1 : term64 _90535 _90546 s x f t) : term64 _90535 _90546 s x f t.
Proof. exact (h1). Qed.
Lemma lem3487844 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) (t : _90535 -> Prop) (x' : _90535) : (term28 _90535 _90546 x f s t x') = (term28 _90535 _90546 x f s t x').
Proof. exact (eq_refl (term28 _90535 _90546 x f s t x')). Qed.
Lemma lem3487845 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) (t : _90535 -> Prop) : (term30 _90535 _90546 x f s t) = (term30 _90535 _90546 x f s t).
Proof. exact (fun_ext (fun x' : _90535 => @lem3487844 _90535 _90546 x f s t x')). Qed.
Lemma lem3487846 {_90535 : Type'} : (@ex _90535) = (@ex _90535).
Proof. exact (eq_refl (@ex _90535)). Qed.
Lemma lem3487899 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) (t : _90535 -> Prop) : (term31 _90535 _90546 x f s t) = (term31 _90535 _90546 x f s t).
Proof. exact (MK_COMB (@lem3487846 _90535) (@lem3487845 _90535 _90546 x f s t)). Qed.
Lemma lem3487900 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) (t : _90535 -> Prop) (h1 : term31 _90535 _90546 x f s t) : term31 _90535 _90546 x f s t.
Proof. exact (EQ_MP (@lem3487899 _90535 _90546 x f s t) (@lem3487830 _90535 _90546 x f s t h1)). Qed.
Lemma lem3487907 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) (x' : _90535) : (term65 _90535 _90546 x f s x') = (term66 _90535 _90546 x f s x').
Proof. exact (@lem17045 (x = (f x')) (s x')). Qed.
Lemma lem3487908 {_90535 : Type'} (P : _90535 -> Prop) : (term67 _90535 P) = (term68 _90535 P).
Proof. exact (@lem18394 _90535 P). Qed.
Lemma lem3487909 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) : (term69 _90535 _90546 x f s) = (term70 _90535 _90546 x f s).
Proof. exact (@lem3487908 _90535 (term39 _90535 _90546 x f s)). Qed.
Lemma lem3487910 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) (x' : _90535) : (term71 _90535 _90546 x f s x') = (term37 _90535 _90546 x f s x').
Proof. exact (eq_refl (term71 _90535 _90546 x f s x')). Qed.
Lemma lem3487911 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3487912 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) (x' : _90535) : (term72 _90535 _90546 x f s x') = (term65 _90535 _90546 x f s x').
Proof. exact (MK_COMB (@lem3487911) (@lem3487910 _90535 _90546 x f s x')). Qed.
Lemma lem3487913 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) (x' : _90535) : (term72 _90535 _90546 x f s x') = (term66 _90535 _90546 x f s x').
Proof. exact (TRANS (@lem3487912 _90535 _90546 x f s x') (@lem3487907 _90535 _90546 x f s x')). Qed.
Lemma lem3487914 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) : (term73 _90535 _90546 x f s) = (term74 _90535 _90546 x f s).
Proof. exact (fun_ext (fun x' : _90535 => @lem3487913 _90535 _90546 x f s x')). Qed.
Lemma lem3487915 {_90535 : Type'} : (@all _90535) = (@all _90535).
Proof. exact (eq_refl (@all _90535)). Qed.
Lemma lem3487916 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) : (term70 _90535 _90546 x f s) = (term75 _90535 _90546 x f s).
Proof. exact (MK_COMB (@lem3487915 _90535) (@lem3487914 _90535 _90546 x f s)). Qed.
Lemma lem3487917 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) : (term69 _90535 _90546 x f s) = (term75 _90535 _90546 x f s).
Proof. exact (TRANS (@lem3487909 _90535 _90546 x f s) (@lem3487916 _90535 _90546 x f s)). Qed.
Lemma lem3487924 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (t : _90535 -> Prop) (x' : _90535) : (term65 _90535 _90546 x f t x') = (term66 _90535 _90546 x f t x').
Proof. exact (@lem17045 (x = (f x')) (t x')). Qed.
Lemma lem3487925 {_90535 : Type'} (P : _90535 -> Prop) : (term67 _90535 P) = (term68 _90535 P).
Proof. exact (@lem18394 _90535 P). Qed.
Lemma lem3487926 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (t : _90535 -> Prop) : (term69 _90535 _90546 x f t) = (term70 _90535 _90546 x f t).
Proof. exact (@lem3487925 _90535 (term39 _90535 _90546 x f t)). Qed.
Lemma lem3487927 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (t : _90535 -> Prop) (x' : _90535) : (term71 _90535 _90546 x f t x') = (term37 _90535 _90546 x f t x').
Proof. exact (eq_refl (term71 _90535 _90546 x f t x')). Qed.
Lemma lem3487928 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3487929 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (t : _90535 -> Prop) (x' : _90535) : (term72 _90535 _90546 x f t x') = (term65 _90535 _90546 x f t x').
Proof. exact (MK_COMB (@lem3487928) (@lem3487927 _90535 _90546 x f t x')). Qed.
Lemma lem3487930 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (t : _90535 -> Prop) (x' : _90535) : (term72 _90535 _90546 x f t x') = (term66 _90535 _90546 x f t x').
Proof. exact (TRANS (@lem3487929 _90535 _90546 x f t x') (@lem3487924 _90535 _90546 x f t x')). Qed.
Lemma lem3487931 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (t : _90535 -> Prop) : (term73 _90535 _90546 x f t) = (term74 _90535 _90546 x f t).
Proof. exact (fun_ext (fun x' : _90535 => @lem3487930 _90535 _90546 x f t x')). Qed.
Lemma lem3487932 {_90535 : Type'} : (@all _90535) = (@all _90535).
Proof. exact (eq_refl (@all _90535)). Qed.
Lemma lem3487933 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (t : _90535 -> Prop) : (term70 _90535 _90546 x f t) = (term75 _90535 _90546 x f t).
Proof. exact (MK_COMB (@lem3487932 _90535) (@lem3487931 _90535 _90546 x f t)). Qed.
Lemma lem3487934 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (t : _90535 -> Prop) : (term69 _90535 _90546 x f t) = (term75 _90535 _90546 x f t).
Proof. exact (TRANS (@lem3487926 _90535 _90546 x f t) (@lem3487933 _90535 _90546 x f t)). Qed.
Lemma lem3487935 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3487936 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) : (term76 _90535 _90546 x f s) = (term77 _90535 _90546 x f s).
Proof. exact (MK_COMB (@lem3487935) (@lem3487917 _90535 _90546 x f s)). Qed.
Lemma lem3487937 {_90535 _90546 : Type'} (s : _90535 -> Prop) (x : _90546) (f : _90535 -> _90546) (t : _90535 -> Prop) : (term78 _90535 _90546 s x f t) = (term79 _90535 _90546 s x f t).
Proof. exact (MK_COMB (@lem3487936 _90535 _90546 x f s) (@lem3487934 _90535 _90546 x f t)). Qed.
Lemma lem3487938 {_90535 _90546 : Type'} (s : _90535 -> Prop) (x : _90546) (f : _90535 -> _90546) (t : _90535 -> Prop) : (term64 _90535 _90546 s x f t) = (term78 _90535 _90546 s x f t).
Proof. exact (@lem17045 (term40 _90535 _90546 x f s) (term40 _90535 _90546 x f t)). Qed.
Lemma lem3488039 {_90535 _90546 : Type'} (s : _90535 -> Prop) (x : _90546) (f : _90535 -> _90546) (t : _90535 -> Prop) : (term64 _90535 _90546 s x f t) = (term79 _90535 _90546 s x f t).
Proof. exact (TRANS (@lem3487938 _90535 _90546 s x f t) (@lem3487937 _90535 _90546 s x f t)). Qed.
Lemma lem3488040 {_90535 _90546 : Type'} (s : _90535 -> Prop) (x : _90546) (f : _90535 -> _90546) (t : _90535 -> Prop) (h1 : term64 _90535 _90546 s x f t) : term79 _90535 _90546 s x f t.
Proof. exact (EQ_MP (@lem3488039 _90535 _90546 s x f t) (@lem3487835 _90535 _90546 s x f t h1)). Qed.
Lemma lem3488058 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (t : _90535 -> Prop) (x' : _90535) : (term66 _90535 _90546 x f t x') = (term66 _90535 _90546 x f t x').
Proof. exact (eq_refl (term66 _90535 _90546 x f t x')). Qed.
Lemma lem3488059 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (t : _90535 -> Prop) : (term74 _90535 _90546 x f t) = (term74 _90535 _90546 x f t).
Proof. exact (fun_ext (fun x' : _90535 => @lem3488058 _90535 _90546 x f t x')). Qed.
Lemma lem3488060 {_90535 : Type'} : (@all _90535) = (@all _90535).
Proof. exact (eq_refl (@all _90535)). Qed.
Lemma lem3488061 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (t : _90535 -> Prop) : (term75 _90535 _90546 x f t) = (term75 _90535 _90546 x f t).
Proof. exact (MK_COMB (@lem3488060 _90535) (@lem3488059 _90535 _90546 x f t)). Qed.
Lemma lem3488078 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) (x' : _90535) : (term66 _90535 _90546 x f s x') = (term66 _90535 _90546 x f s x').
Proof. exact (eq_refl (term66 _90535 _90546 x f s x')). Qed.
Lemma lem3488079 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) : (term74 _90535 _90546 x f s) = (term74 _90535 _90546 x f s).
Proof. exact (fun_ext (fun x' : _90535 => @lem3488078 _90535 _90546 x f s x')). Qed.
Lemma lem3488080 {_90535 : Type'} : (@all _90535) = (@all _90535).
Proof. exact (eq_refl (@all _90535)). Qed.
Lemma lem3488081 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) : (term75 _90535 _90546 x f s) = (term75 _90535 _90546 x f s).
Proof. exact (MK_COMB (@lem3488080 _90535) (@lem3488079 _90535 _90546 x f s)). Qed.
Lemma lem3488082 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3488083 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) : (term77 _90535 _90546 x f s) = (term77 _90535 _90546 x f s).
Proof. exact (MK_COMB (@lem3488082) (@lem3488081 _90535 _90546 x f s)). Qed.
Lemma lem3488084 {_90535 _90546 : Type'} (s : _90535 -> Prop) (x : _90546) (f : _90535 -> _90546) (t : _90535 -> Prop) : (term79 _90535 _90546 s x f t) = (term79 _90535 _90546 s x f t).
Proof. exact (MK_COMB (@lem3488083 _90535 _90546 x f s) (@lem3488061 _90535 _90546 x f t)). Qed.
Lemma lem3488085 {_90535 _90546 : Type'} (s : _90535 -> Prop) (x : _90546) (f : _90535 -> _90546) (t : _90535 -> Prop) (h1 : term64 _90535 _90546 s x f t) : term79 _90535 _90546 s x f t.
Proof. exact (EQ_MP (@lem3488084 _90535 _90546 s x f t) (@lem3488040 _90535 _90546 s x f t h1)). Qed.
Lemma lem3488105 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) (t : _90535 -> Prop) (x' : _90535) (h1 : term28 _90535 _90546 x f s t x') : term28 _90535 _90546 x f s t x'.
Proof. exact (h1). Qed.
Lemma lem3488106 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) (t : _90535 -> Prop) (x' : _90535) (h1 : term28 _90535 _90546 x f s t x') : term25 _90535 s t x'.
Proof. exact (proj2 (@lem3488105 _90535 _90546 x f s t x' h1)). Qed.
Lemma lem3488110 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) (h1 : term75 _90535 _90546 x f s) : term75 _90535 _90546 x f s.
Proof. exact (h1). Qed.
Lemma lem3488111 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (t : _90535 -> Prop) (h1 : term75 _90535 _90546 x f t) : term75 _90535 _90546 x f t.
Proof. exact (h1). Qed.
Lemma lem3488131 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) (x' : _90535) : (term66 _90535 _90546 x f s x') = (term66 _90535 _90546 x f s x').
Proof. exact (eq_refl (term66 _90535 _90546 x f s x')). Qed.
Lemma lem3488132 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) : (term74 _90535 _90546 x f s) = (term74 _90535 _90546 x f s).
Proof. exact (fun_ext (fun x' : _90535 => @lem3488131 _90535 _90546 x f s x')). Qed.
Lemma lem3488133 {_90535 : Type'} : (@all _90535) = (@all _90535).
Proof. exact (eq_refl (@all _90535)). Qed.
Lemma lem3488135 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) : (term75 _90535 _90546 x f s) = (term75 _90535 _90546 x f s).
Proof. exact (MK_COMB (@lem3488133 _90535) (@lem3488132 _90535 _90546 x f s)). Qed.
Lemma lem3488136 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) (h1 : term75 _90535 _90546 x f s) : term75 _90535 _90546 x f s.
Proof. exact (EQ_MP (@lem3488135 _90535 _90546 x f s) (@lem3488110 _90535 _90546 x f s h1)). Qed.
Lemma lem3488156 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (t : _90535 -> Prop) (x' : _90535) : (term66 _90535 _90546 x f t x') = (term66 _90535 _90546 x f t x').
Proof. exact (eq_refl (term66 _90535 _90546 x f t x')). Qed.
Lemma lem3488157 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (t : _90535 -> Prop) : (term74 _90535 _90546 x f t) = (term74 _90535 _90546 x f t).
Proof. exact (fun_ext (fun x' : _90535 => @lem3488156 _90535 _90546 x f t x')). Qed.
Lemma lem3488158 {_90535 : Type'} : (@all _90535) = (@all _90535).
Proof. exact (eq_refl (@all _90535)). Qed.
Lemma lem3488160 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (t : _90535 -> Prop) : (term75 _90535 _90546 x f t) = (term75 _90535 _90546 x f t).
Proof. exact (MK_COMB (@lem3488158 _90535) (@lem3488157 _90535 _90546 x f t)). Qed.
Lemma lem3488161 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (t : _90535 -> Prop) (h1 : term75 _90535 _90546 x f t) : term75 _90535 _90546 x f t.
Proof. exact (EQ_MP (@lem3488160 _90535 _90546 x f t) (@lem3488111 _90535 _90546 x f t h1)). Qed.
Lemma lem3488162 {_90535 _90546 : Type'} (_36743 : _90535) (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) (h1 : term75 _90535 _90546 x f s) : term80 _90535 _90546 x f s _36743.
Proof. exact (@lem3488136 _90535 _90546 x f s h1 _36743). Qed.
Lemma lem3488163 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) (_36743 : _90535) : (term80 _90535 _90546 x f s _36743) = (term66 _90535 _90546 x f s _36743).
Proof. exact (eq_refl (term80 _90535 _90546 x f s _36743)). Qed.
Lemma lem3488165 {_90535 _90546 : Type'} (_36744 : _90535) (x : _90546) (f : _90535 -> _90546) (t : _90535 -> Prop) (h1 : term75 _90535 _90546 x f t) : term80 _90535 _90546 x f t _36744.
Proof. exact (@lem3488161 _90535 _90546 x f t h1 _36744). Qed.
Lemma lem3488166 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (t : _90535 -> Prop) (_36744 : _90535) : (term80 _90535 _90546 x f t _36744) = (term66 _90535 _90546 x f t _36744).
Proof. exact (eq_refl (term80 _90535 _90546 x f t _36744)). Qed.
Lemma lem3488169 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) (t : _90535 -> Prop) (x' : _90535) (h1 : term28 _90535 _90546 x f s t x') : x = (f x').
Proof. exact (proj1 (@lem3488105 _90535 _90546 x f s t x' h1)). Qed.
Lemma lem3488179 {_90535 _90546 : Type'} (_36743 : _90535) (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) (h1 : term75 _90535 _90546 x f s) : term66 _90535 _90546 x f s _36743.
Proof. exact (EQ_MP (@lem3488163 _90535 _90546 x f s _36743) (@lem3488162 _90535 _90546 _36743 x f s h1)). Qed.
Lemma lem3488181 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) (t : _90535 -> Prop) (x' : _90535) (h1 : term28 _90535 _90546 x f s t x') : x = (f x').
Proof. exact (proj1 (@lem3488105 _90535 _90546 x f s t x' h1)). Qed.
Lemma lem3488191 {_90535 _90546 : Type'} (_36744 : _90535) (x : _90546) (f : _90535 -> _90546) (t : _90535 -> Prop) (h1 : term75 _90535 _90546 x f t) : term66 _90535 _90546 x f t _36744.
Proof. exact (EQ_MP (@lem3488166 _90535 _90546 x f t _36744) (@lem3488165 _90535 _90546 _36744 x f t h1)). Qed.
Lemma lem3488234 {_90535 _90546 : Type'} (f : _90535 -> _90546) (s : _90535 -> Prop) (_36743 : _90535) : (term81 _90535 _90546 f s _36743) = (term81 _90535 _90546 f s _36743).
Proof. exact (eq_refl (term81 _90535 _90546 f s _36743)). Qed.
Lemma lem3488235 {_90535 _90546 : Type'} (_36743 : _90535) (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) (t : _90535 -> Prop) (x' : _90535) (h1 : term28 _90535 _90546 x f s t x') : (term82 _90535 _90546 f s _36743 x) = (term83 _90535 _90546 s _36743 f x').
Proof. exact (MK_COMB (@lem3488234 _90535 _90546 f s _36743) (@lem3488169 _90535 _90546 x f s t x' h1)). Qed.
Lemma lem3488236 {_90535 _90546 : Type'} (x' : _90535) (f : _90535 -> _90546) (s : _90535 -> Prop) (_36743 : _90535) : (term83 _90535 _90546 s _36743 f x') = (term84 _90535 _90546 x' f s _36743).
Proof. exact (eq_refl (term83 _90535 _90546 s _36743 f x')). Qed.
Lemma lem3488237 {_90535 _90546 : Type'} (f : _90535 -> _90546) (s : _90535 -> Prop) (_36743 : _90535) (x : _90546) : (term85 _90535 _90546 f s _36743 x) = (term85 _90535 _90546 f s _36743 x).
Proof. exact (eq_refl (term85 _90535 _90546 f s _36743 x)). Qed.
Lemma lem3488238 {_90535 _90546 : Type'} (x : _90546) (x' : _90535) (f : _90535 -> _90546) (s : _90535 -> Prop) (_36743 : _90535) : ((term82 _90535 _90546 f s _36743 x) = (term83 _90535 _90546 s _36743 f x')) = ((term82 _90535 _90546 f s _36743 x) = (term84 _90535 _90546 x' f s _36743)).
Proof. exact (MK_COMB (@lem3488237 _90535 _90546 f s _36743 x) (@lem3488236 _90535 _90546 x' f s _36743)). Qed.
Lemma lem3488239 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) (_36743 : _90535) : (term82 _90535 _90546 f s _36743 x) = (term66 _90535 _90546 x f s _36743).
Proof. exact (eq_refl (term82 _90535 _90546 f s _36743 x)). Qed.
Lemma lem3488240 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3488241 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) (_36743 : _90535) : (term85 _90535 _90546 f s _36743 x) = (term86 _90535 _90546 x f s _36743).
Proof. exact (MK_COMB (@lem3488240) (@lem3488239 _90535 _90546 x f s _36743)). Qed.
Lemma lem3488242 {_90535 _90546 : Type'} (x' : _90535) (f : _90535 -> _90546) (s : _90535 -> Prop) (_36743 : _90535) : (term84 _90535 _90546 x' f s _36743) = (term84 _90535 _90546 x' f s _36743).
Proof. exact (eq_refl (term84 _90535 _90546 x' f s _36743)). Qed.
Lemma lem3488243 {_90535 _90546 : Type'} (x : _90546) (x' : _90535) (f : _90535 -> _90546) (s : _90535 -> Prop) (_36743 : _90535) : ((term82 _90535 _90546 f s _36743 x) = (term84 _90535 _90546 x' f s _36743)) = ((term66 _90535 _90546 x f s _36743) = (term84 _90535 _90546 x' f s _36743)).
Proof. exact (MK_COMB (@lem3488241 _90535 _90546 x f s _36743) (@lem3488242 _90535 _90546 x' f s _36743)). Qed.
Lemma lem3488244 {_90535 _90546 : Type'} (x : _90546) (x' : _90535) (f : _90535 -> _90546) (s : _90535 -> Prop) (_36743 : _90535) : ((term82 _90535 _90546 f s _36743 x) = (term83 _90535 _90546 s _36743 f x')) = ((term66 _90535 _90546 x f s _36743) = (term84 _90535 _90546 x' f s _36743)).
Proof. exact (TRANS (@lem3488238 _90535 _90546 x x' f s _36743) (@lem3488243 _90535 _90546 x x' f s _36743)). Qed.
Lemma lem3488245 {_90535 _90546 : Type'} (_36743 : _90535) (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) (t : _90535 -> Prop) (x' : _90535) (h1 : term28 _90535 _90546 x f s t x') : (term66 _90535 _90546 x f s _36743) = (term84 _90535 _90546 x' f s _36743).
Proof. exact (EQ_MP (@lem3488244 _90535 _90546 x x' f s _36743) (@lem3488235 _90535 _90546 _36743 x f s t x' h1)). Qed.
Lemma lem3488246 {_90535 _90546 : Type'} (_36743 : _90535) (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) (t : _90535 -> Prop) (x' : _90535) (h1 : term75 _90535 _90546 x f s) (h2 : term28 _90535 _90546 x f s t x') : term84 _90535 _90546 x' f s _36743.
Proof. exact (EQ_MP (@lem3488245 _90535 _90546 _36743 x f s t x' h2) (@lem3488179 _90535 _90546 _36743 x f s h1)). Qed.
Lemma lem3488289 {_90535 _90546 : Type'} (f : _90535 -> _90546) (t : _90535 -> Prop) (_36744 : _90535) : (term81 _90535 _90546 f t _36744) = (term81 _90535 _90546 f t _36744).
Proof. exact (eq_refl (term81 _90535 _90546 f t _36744)). Qed.
Lemma lem3488290 {_90535 _90546 : Type'} (_36744 : _90535) (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) (t : _90535 -> Prop) (x' : _90535) (h1 : term28 _90535 _90546 x f s t x') : (term82 _90535 _90546 f t _36744 x) = (term83 _90535 _90546 t _36744 f x').
Proof. exact (MK_COMB (@lem3488289 _90535 _90546 f t _36744) (@lem3488181 _90535 _90546 x f s t x' h1)). Qed.
Lemma lem3488291 {_90535 _90546 : Type'} (x' : _90535) (f : _90535 -> _90546) (t : _90535 -> Prop) (_36744 : _90535) : (term83 _90535 _90546 t _36744 f x') = (term84 _90535 _90546 x' f t _36744).
Proof. exact (eq_refl (term83 _90535 _90546 t _36744 f x')). Qed.
Lemma lem3488292 {_90535 _90546 : Type'} (f : _90535 -> _90546) (t : _90535 -> Prop) (_36744 : _90535) (x : _90546) : (term85 _90535 _90546 f t _36744 x) = (term85 _90535 _90546 f t _36744 x).
Proof. exact (eq_refl (term85 _90535 _90546 f t _36744 x)). Qed.
Lemma lem3488293 {_90535 _90546 : Type'} (x : _90546) (x' : _90535) (f : _90535 -> _90546) (t : _90535 -> Prop) (_36744 : _90535) : ((term82 _90535 _90546 f t _36744 x) = (term83 _90535 _90546 t _36744 f x')) = ((term82 _90535 _90546 f t _36744 x) = (term84 _90535 _90546 x' f t _36744)).
Proof. exact (MK_COMB (@lem3488292 _90535 _90546 f t _36744 x) (@lem3488291 _90535 _90546 x' f t _36744)). Qed.
Lemma lem3488294 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (t : _90535 -> Prop) (_36744 : _90535) : (term82 _90535 _90546 f t _36744 x) = (term66 _90535 _90546 x f t _36744).
Proof. exact (eq_refl (term82 _90535 _90546 f t _36744 x)). Qed.
Lemma lem3488295 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3488296 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (t : _90535 -> Prop) (_36744 : _90535) : (term85 _90535 _90546 f t _36744 x) = (term86 _90535 _90546 x f t _36744).
Proof. exact (MK_COMB (@lem3488295) (@lem3488294 _90535 _90546 x f t _36744)). Qed.
Lemma lem3488297 {_90535 _90546 : Type'} (x' : _90535) (f : _90535 -> _90546) (t : _90535 -> Prop) (_36744 : _90535) : (term84 _90535 _90546 x' f t _36744) = (term84 _90535 _90546 x' f t _36744).
Proof. exact (eq_refl (term84 _90535 _90546 x' f t _36744)). Qed.
Lemma lem3488298 {_90535 _90546 : Type'} (x : _90546) (x' : _90535) (f : _90535 -> _90546) (t : _90535 -> Prop) (_36744 : _90535) : ((term82 _90535 _90546 f t _36744 x) = (term84 _90535 _90546 x' f t _36744)) = ((term66 _90535 _90546 x f t _36744) = (term84 _90535 _90546 x' f t _36744)).
Proof. exact (MK_COMB (@lem3488296 _90535 _90546 x f t _36744) (@lem3488297 _90535 _90546 x' f t _36744)). Qed.
Lemma lem3488299 {_90535 _90546 : Type'} (x : _90546) (x' : _90535) (f : _90535 -> _90546) (t : _90535 -> Prop) (_36744 : _90535) : ((term82 _90535 _90546 f t _36744 x) = (term83 _90535 _90546 t _36744 f x')) = ((term66 _90535 _90546 x f t _36744) = (term84 _90535 _90546 x' f t _36744)).
Proof. exact (TRANS (@lem3488293 _90535 _90546 x x' f t _36744) (@lem3488298 _90535 _90546 x x' f t _36744)). Qed.
Lemma lem3488300 {_90535 _90546 : Type'} (_36744 : _90535) (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) (t : _90535 -> Prop) (x' : _90535) (h1 : term28 _90535 _90546 x f s t x') : (term66 _90535 _90546 x f t _36744) = (term84 _90535 _90546 x' f t _36744).
Proof. exact (EQ_MP (@lem3488299 _90535 _90546 x x' f t _36744) (@lem3488290 _90535 _90546 _36744 x f s t x' h1)). Qed.
Lemma lem3488301 {_90535 _90546 : Type'} (_36744 : _90535) (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) (t : _90535 -> Prop) (x' : _90535) (h1 : term75 _90535 _90546 x f t) (h2 : term28 _90535 _90546 x f s t x') : term84 _90535 _90546 x' f t _36744.
Proof. exact (EQ_MP (@lem3488300 _90535 _90546 _36744 x f s t x' h2) (@lem3488191 _90535 _90546 _36744 x f t h1)). Qed.
Lemma lem3488339 {_90546 : Type'} (x : _90546) : x = x.
Proof. exact (@lem21386 _90546 x). Qed.
Lemma lem3488340 {_90546 : Type'} (x : _90546) : x = x.
Proof. exact (@lem3488339 _90546 x). Qed.
Lemma lem3488341 {_90535 _90546 : Type'} (f : _90535 -> _90546) (x' : _90535) : (f x') = (f x').
Proof. exact (@lem3488340 _90546 (f x')). Qed.
Lemma lem3488342 {_90535 _90546 : Type'} (f : _90535 -> _90546) (x' : _90535) : term87 _90535 _90546 f x'.
Proof. exact (fun h0 : term88 _90535 _90546 f x' => @lem3488341 _90535 _90546 f x'). Qed.
Lemma lem3488344 (p : Prop) : (term89 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3488345 {_90535 _90546 : Type'} (f : _90535 -> _90546) (x' : _90535) : (term87 _90535 _90546 f x') = ((f x') = (f x')).
Proof. exact (@lem3488344 ((f x') = (f x'))). Qed.
Lemma lem3488346 {_90535 _90546 : Type'} (f : _90535 -> _90546) (x' : _90535) : (f x') = (f x').
Proof. exact (EQ_MP (@lem3488345 _90535 _90546 f x') (@lem3488342 _90535 _90546 f x')). Qed.
Lemma lem3488348 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) (t : _90535 -> Prop) (x' : _90535) (h1 : term28 _90535 _90546 x f s t x') : s x'.
Proof. exact (proj1 (@lem3488106 _90535 _90546 x f s t x' h1)). Qed.
Lemma lem3488349 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) (t : _90535 -> Prop) (x' : _90535) (h1 : term28 _90535 _90546 x f s t x') : term90 _90535 s x'.
Proof. exact (fun h0 : term91 _90535 s x' => @lem3488348 _90535 _90546 x f s t x' h1). Qed.
Lemma lem3488351 (p : Prop) : (term89 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3488352 {_90535 : Type'} (s : _90535 -> Prop) (x' : _90535) : (term90 _90535 s x') = (s x').
Proof. exact (@lem3488351 (s x')). Qed.
Lemma lem3488353 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) (t : _90535 -> Prop) (x' : _90535) (h1 : term28 _90535 _90546 x f s t x') : s x'.
Proof. exact (EQ_MP (@lem3488352 _90535 s x') (@lem3488349 _90535 _90546 x f s t x' h1)). Qed.
Lemma lem3488355 (a : Prop) (b : Prop) : (term92 a b) = (term93 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3488356 {_90535 _90546 : Type'} (x' : _90535) (f : _90535 -> _90546) (s : _90535 -> Prop) (_36743 : _90535) : (term84 _90535 _90546 x' f s _36743) = (term94 _90535 _90546 x' f s _36743).
Proof. exact (@lem3488355 ((f x') = (f _36743)) (s _36743)). Qed.
Lemma lem3488358 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3488359 {_90535 _90546 : Type'} (x' : _90535) (f : _90535 -> _90546) (s : _90535 -> Prop) (_36743 : _90535) : (term94 _90535 _90546 x' f s _36743) = (term95 _90535 _90546 x' f s _36743).
Proof. exact (@lem3488358 (term96 _90535 _90546 x' f s _36743)). Qed.
Lemma lem3488360 {_90535 _90546 : Type'} (x' : _90535) (f : _90535 -> _90546) (s : _90535 -> Prop) (_36743 : _90535) : (term84 _90535 _90546 x' f s _36743) = (term95 _90535 _90546 x' f s _36743).
Proof. exact (TRANS (@lem3488356 _90535 _90546 x' f s _36743) (@lem3488359 _90535 _90546 x' f s _36743)). Qed.
Lemma lem3488362 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) (t : _90535 -> Prop) (x' : _90535) (h1 : term28 _90535 _90546 x f s t x') : term97 _90535 _90546 f s x'.
Proof. exact (conj (@lem3488346 _90535 _90546 f x') (@lem3488353 _90535 _90546 x f s t x' h1)). Qed.
Lemma lem3488364 {_90535 _90546 : Type'} (_36743 : _90535) (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) (t : _90535 -> Prop) (x' : _90535) (h1 : term75 _90535 _90546 x f s) (h2 : term28 _90535 _90546 x f s t x') : term95 _90535 _90546 x' f s _36743.
Proof. exact (EQ_MP (@lem3488360 _90535 _90546 x' f s _36743) (@lem3488246 _90535 _90546 _36743 x f s t x' h1 h2)). Qed.
Lemma lem3488365 {_90535 _90546 : Type'} (_36743 : _90535) (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) (t : _90535 -> Prop) (x' : _90535) (h1 : term75 _90535 _90546 x f s) (h2 : term28 _90535 _90546 x f s t x') : term95 _90535 _90546 x' f s _36743.
Proof. exact (@lem3488364 _90535 _90546 _36743 x f s t x' h1 h2). Qed.
Lemma lem3488366 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) (t : _90535 -> Prop) (x' : _90535) (h1 : term75 _90535 _90546 x f s) (h2 : term28 _90535 _90546 x f s t x') : term98 _90535 _90546 f s x'.
Proof. exact (@lem3488365 _90535 _90546 x' x f s t x' h1 h2). Qed.
Lemma lem3488369 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) (t : _90535 -> Prop) (x' : _90535) (h1 : term75 _90535 _90546 x f s) (h2 : term28 _90535 _90546 x f s t x') : False.
Proof. exact (@lem3488366 _90535 _90546 x f s t x' h1 h2 (@lem3488362 _90535 _90546 x f s t x' h2)). Qed.
Lemma lem3488370 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) (t : _90535 -> Prop) (x' : _90535) (h1 : term75 _90535 _90546 x f s) (h2 : term28 _90535 _90546 x f s t x') : term99.
Proof. exact (fun h0 : ~ False => @lem3488369 _90535 _90546 x f s t x' h1 h2). Qed.
Lemma lem3488372 (p : Prop) : (term89 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3488373 : term99 = False.
Proof. exact (@lem3488372 False). Qed.
Lemma lem3488412 {_90546 : Type'} (x : _90546) : x = x.
Proof. exact (@lem21386 _90546 x). Qed.
Lemma lem3488413 {_90546 : Type'} (x : _90546) : x = x.
Proof. exact (@lem3488412 _90546 x). Qed.
Lemma lem3488414 {_90535 _90546 : Type'} (f : _90535 -> _90546) (x' : _90535) : (f x') = (f x').
Proof. exact (@lem3488413 _90546 (f x')). Qed.
Lemma lem3488415 {_90535 _90546 : Type'} (f : _90535 -> _90546) (x' : _90535) : term87 _90535 _90546 f x'.
Proof. exact (fun h0 : term88 _90535 _90546 f x' => @lem3488414 _90535 _90546 f x'). Qed.
Lemma lem3488417 (p : Prop) : (term89 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3488418 {_90535 _90546 : Type'} (f : _90535 -> _90546) (x' : _90535) : (term87 _90535 _90546 f x') = ((f x') = (f x')).
Proof. exact (@lem3488417 ((f x') = (f x'))). Qed.
Lemma lem3488419 {_90535 _90546 : Type'} (f : _90535 -> _90546) (x' : _90535) : (f x') = (f x').
Proof. exact (EQ_MP (@lem3488418 _90535 _90546 f x') (@lem3488415 _90535 _90546 f x')). Qed.
Lemma lem3488421 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) (t : _90535 -> Prop) (x' : _90535) (h1 : term28 _90535 _90546 x f s t x') : t x'.
Proof. exact (proj2 (@lem3488106 _90535 _90546 x f s t x' h1)). Qed.
Lemma lem3488422 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) (t : _90535 -> Prop) (x' : _90535) (h1 : term28 _90535 _90546 x f s t x') : term90 _90535 t x'.
Proof. exact (fun h0 : term91 _90535 t x' => @lem3488421 _90535 _90546 x f s t x' h1). Qed.
Lemma lem3488424 (p : Prop) : (term89 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3488425 {_90535 : Type'} (t : _90535 -> Prop) (x' : _90535) : (term90 _90535 t x') = (t x').
Proof. exact (@lem3488424 (t x')). Qed.
Lemma lem3488426 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) (t : _90535 -> Prop) (x' : _90535) (h1 : term28 _90535 _90546 x f s t x') : t x'.
Proof. exact (EQ_MP (@lem3488425 _90535 t x') (@lem3488422 _90535 _90546 x f s t x' h1)). Qed.
Lemma lem3488428 (a : Prop) (b : Prop) : (term92 a b) = (term93 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3488429 {_90535 _90546 : Type'} (x' : _90535) (f : _90535 -> _90546) (t : _90535 -> Prop) (_36744 : _90535) : (term84 _90535 _90546 x' f t _36744) = (term94 _90535 _90546 x' f t _36744).
Proof. exact (@lem3488428 ((f x') = (f _36744)) (t _36744)). Qed.
Lemma lem3488431 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3488432 {_90535 _90546 : Type'} (x' : _90535) (f : _90535 -> _90546) (t : _90535 -> Prop) (_36744 : _90535) : (term94 _90535 _90546 x' f t _36744) = (term95 _90535 _90546 x' f t _36744).
Proof. exact (@lem3488431 (term96 _90535 _90546 x' f t _36744)). Qed.
Lemma lem3488433 {_90535 _90546 : Type'} (x' : _90535) (f : _90535 -> _90546) (t : _90535 -> Prop) (_36744 : _90535) : (term84 _90535 _90546 x' f t _36744) = (term95 _90535 _90546 x' f t _36744).
Proof. exact (TRANS (@lem3488429 _90535 _90546 x' f t _36744) (@lem3488432 _90535 _90546 x' f t _36744)). Qed.
Lemma lem3488435 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) (t : _90535 -> Prop) (x' : _90535) (h1 : term28 _90535 _90546 x f s t x') : term97 _90535 _90546 f t x'.
Proof. exact (conj (@lem3488419 _90535 _90546 f x') (@lem3488426 _90535 _90546 x f s t x' h1)). Qed.
Lemma lem3488437 {_90535 _90546 : Type'} (_36744 : _90535) (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) (t : _90535 -> Prop) (x' : _90535) (h1 : term75 _90535 _90546 x f t) (h2 : term28 _90535 _90546 x f s t x') : term95 _90535 _90546 x' f t _36744.
Proof. exact (EQ_MP (@lem3488433 _90535 _90546 x' f t _36744) (@lem3488301 _90535 _90546 _36744 x f s t x' h1 h2)). Qed.
Lemma lem3488438 {_90535 _90546 : Type'} (_36744 : _90535) (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) (t : _90535 -> Prop) (x' : _90535) (h1 : term75 _90535 _90546 x f t) (h2 : term28 _90535 _90546 x f s t x') : term95 _90535 _90546 x' f t _36744.
Proof. exact (@lem3488437 _90535 _90546 _36744 x f s t x' h1 h2). Qed.
Lemma lem3488439 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) (t : _90535 -> Prop) (x' : _90535) (h1 : term75 _90535 _90546 x f t) (h2 : term28 _90535 _90546 x f s t x') : term98 _90535 _90546 f t x'.
Proof. exact (@lem3488438 _90535 _90546 x' x f s t x' h1 h2). Qed.
Lemma lem3488442 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) (t : _90535 -> Prop) (x' : _90535) (h1 : term75 _90535 _90546 x f t) (h2 : term28 _90535 _90546 x f s t x') : False.
Proof. exact (@lem3488439 _90535 _90546 x f s t x' h1 h2 (@lem3488435 _90535 _90546 x f s t x' h2)). Qed.
Lemma lem3488443 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) (t : _90535 -> Prop) (x' : _90535) (h1 : term75 _90535 _90546 x f t) (h2 : term28 _90535 _90546 x f s t x') : term99.
Proof. exact (fun h0 : ~ False => @lem3488442 _90535 _90546 x f s t x' h1 h2). Qed.
Lemma lem3488445 (p : Prop) : (term89 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3488446 : term99 = False.
Proof. exact (@lem3488445 False). Qed.
Lemma lem3488448 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) (t : _90535 -> Prop) (x' : _90535) (h1 : term75 _90535 _90546 x f t) (h2 : term28 _90535 _90546 x f s t x') : False.
Proof. exact (EQ_MP (@lem3488446) (@lem3488443 _90535 _90546 x f s t x' h1 h2)). Qed.
Lemma lem3488449 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) (t : _90535 -> Prop) (x' : _90535) (h1 : term75 _90535 _90546 x f s) (h2 : term28 _90535 _90546 x f s t x') : False.
Proof. exact (EQ_MP (@lem3488373) (@lem3488370 _90535 _90546 x f s t x' h1 h2)). Qed.
Lemma lem3488450 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) (t : _90535 -> Prop) (x' : _90535) (h1 : term75 _90535 _90546 x f t) (h2 : term28 _90535 _90546 x f s t x') : (term75 _90535 _90546 x f t) = False.
Proof. exact (prop_ext (fun h3 : term75 _90535 _90546 x f t => @lem3488448 _90535 _90546 x f s t x' h1 h2) (fun h3 : False => @lem3488161 _90535 _90546 x f t h1)). Qed.
Lemma lem3488451 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) (t : _90535 -> Prop) (x' : _90535) (h1 : term75 _90535 _90546 x f t) (h2 : term28 _90535 _90546 x f s t x') : False.
Proof. exact (EQ_MP (@lem3488450 _90535 _90546 x f s t x' h1 h2) (@lem3488161 _90535 _90546 x f t h1)). Qed.
Lemma lem3488452 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) (t : _90535 -> Prop) (x' : _90535) (h1 : term75 _90535 _90546 x f s) (h2 : term28 _90535 _90546 x f s t x') : (term75 _90535 _90546 x f s) = False.
Proof. exact (prop_ext (fun h3 : term75 _90535 _90546 x f s => @lem3488449 _90535 _90546 x f s t x' h1 h2) (fun h3 : False => @lem3488136 _90535 _90546 x f s h1)). Qed.
Lemma lem3488453 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) (t : _90535 -> Prop) (x' : _90535) (h1 : term75 _90535 _90546 x f s) (h2 : term28 _90535 _90546 x f s t x') : False.
Proof. exact (EQ_MP (@lem3488452 _90535 _90546 x f s t x' h1 h2) (@lem3488136 _90535 _90546 x f s h1)). Qed.
Lemma lem3488454 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) (t : _90535 -> Prop) (x' : _90535) (h1 : term64 _90535 _90546 s x f t) (h2 : term28 _90535 _90546 x f s t x') : False.
Proof. exact (or_elim (@lem3488085 _90535 _90546 s x f t h1) (fun h0 : term75 _90535 _90546 x f s => @lem3488453 _90535 _90546 x f s t x' h0 h2) (fun h0 : term75 _90535 _90546 x f t => @lem3488451 _90535 _90546 x f s t x' h0 h2)). Qed.
Lemma lem3488455 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) (t : _90535 -> Prop) (x' : _90535) (h1 : term64 _90535 _90546 s x f t) (h2 : term28 _90535 _90546 x f s t x') : (term28 _90535 _90546 x f s t x') = False.
Proof. exact (prop_ext (fun h3 : term28 _90535 _90546 x f s t x' => @lem3488454 _90535 _90546 x f s t x' h1 h2) (fun h3 : False => @lem3488105 _90535 _90546 x f s t x' h2)). Qed.
Lemma lem3488456 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) (t : _90535 -> Prop) (x' : _90535) (h1 : term64 _90535 _90546 s x f t) (h2 : term28 _90535 _90546 x f s t x') : False.
Proof. exact (EQ_MP (@lem3488455 _90535 _90546 x f s t x' h1 h2) (@lem3488105 _90535 _90546 x f s t x' h2)). Qed.
Lemma lem3488457 {_90535 _90546 : Type'} (s : _90535 -> Prop) (x : _90546) (f : _90535 -> _90546) (t : _90535 -> Prop) (h1 : term31 _90535 _90546 x f s t) (h2 : term64 _90535 _90546 s x f t) : False.
Proof. exact (ex_elim (@lem3487900 _90535 _90546 x f s t h1) (fun x' : _90535 => fun h0 : term30 _90535 _90546 x f s t x' => @lem3488456 _90535 _90546 x f s t x' h2 h0)). Qed.
Lemma lem3488458 {_90535 _90546 : Type'} (s : _90535 -> Prop) (x : _90546) (f : _90535 -> _90546) (t : _90535 -> Prop) (h1 : term31 _90535 _90546 x f s t) (h2 : term64 _90535 _90546 s x f t) : (term31 _90535 _90546 x f s t) = False.
Proof. exact (prop_ext (fun h3 : term31 _90535 _90546 x f s t => @lem3488457 _90535 _90546 s x f t h1 h2) (fun h3 : False => @lem3487900 _90535 _90546 x f s t h1)). Qed.
Lemma lem3488459 {_90535 _90546 : Type'} (s : _90535 -> Prop) (x : _90546) (f : _90535 -> _90546) (t : _90535 -> Prop) (h1 : term31 _90535 _90546 x f s t) (h2 : term64 _90535 _90546 s x f t) : False.
Proof. exact (EQ_MP (@lem3488458 _90535 _90546 s x f t h1 h2) (@lem3487900 _90535 _90546 x f s t h1)). Qed.
Lemma lem3488460 {_90535 _90546 : Type'} (s : _90535 -> Prop) (x : _90546) (f : _90535 -> _90546) (t : _90535 -> Prop) (h1 : term31 _90535 _90546 x f s t) (h2 : term64 _90535 _90546 s x f t) : (term64 _90535 _90546 s x f t) = False.
Proof. exact (prop_ext (fun h3 : term64 _90535 _90546 s x f t => @lem3488459 _90535 _90546 s x f t h1 h2) (fun h3 : False => @lem3487835 _90535 _90546 s x f t h2)). Qed.
Lemma lem3488461 {_90535 _90546 : Type'} (s : _90535 -> Prop) (x : _90546) (f : _90535 -> _90546) (t : _90535 -> Prop) (h1 : term31 _90535 _90546 x f s t) (h2 : term64 _90535 _90546 s x f t) : False.
Proof. exact (EQ_MP (@lem3488460 _90535 _90546 s x f t h1 h2) (@lem3487835 _90535 _90546 s x f t h2)). Qed.
Lemma lem3488462 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) (t : _90535 -> Prop) (h1 : term31 _90535 _90546 x f s t) : term63 _90535 _90546 s x f t.
Proof. exact (fun h0 : term64 _90535 _90546 s x f t => @lem3488461 _90535 _90546 s x f t h1 h0). Qed.
Lemma lem3488463 {_90535 _90546 : Type'} (x : _90546) (f : _90535 -> _90546) (s : _90535 -> Prop) (t : _90535 -> Prop) (h1 : term31 _90535 _90546 x f s t) : term43 _90535 _90546 s x f t.
Proof. exact (EQ_MP (@lem3487834 _90535 _90546 s x f t) (@lem3488462 _90535 _90546 x f s t h1)). Qed.
Lemma lem3488464 {_90535 _90546 : Type'} (s : _90535 -> Prop) (x : _90546) (f : _90535 -> _90546) (t : _90535 -> Prop) : term45 _90535 _90546 s x f t.
Proof. exact (fun h0 : term31 _90535 _90546 x f s t => @lem3488463 _90535 _90546 x f s t h0). Qed.
Lemma lem3488469 {_90535 _90546 : Type'} (s : _90535 -> Prop) (f : _90535 -> _90546) (t : _90535 -> Prop) : term48 _90535 _90546 s f t.
Proof. exact (fun x : _90546 => @lem3488464 _90535 _90546 s x f t). Qed.
Lemma lem3488474 {_90535 _90546 : Type'} (s : _90535 -> Prop) (f : _90535 -> _90546) : term50 _90535 _90546 s f.
Proof. exact (fun t : _90535 -> Prop => @lem3488469 _90535 _90546 s f t). Qed.
Lemma lem3488479 {_90535 _90546 : Type'} (f : _90535 -> _90546) : term52 _90535 _90546 f.
Proof. exact (fun s : _90535 -> Prop => @lem3488474 _90535 _90546 s f). Qed.
Lemma lem3488484 {_90535 _90546 : Type'} : term54 _90535 _90546.
Proof. exact (fun f : _90535 -> _90546 => @lem3488479 _90535 _90546 f). Qed.
Lemma lem3488485 {_90535 _90546 : Type'} : term56 _90535 _90546.
Proof. exact (EQ_MP (@lem3487829 _90535 _90546) (@lem3488484 _90535 _90546)). Qed.
Lemma lem3488487 {_90535 _90546 : Type'} : term56 _90535 _90546.
Proof. exact (@lem3487574 _90535 _90546 (@lem3488485 _90535 _90546)). Qed.
Lemma lem3488488 {_90535 _90546 : Type'} (h1 : term57 _90535 _90546) : False.
Proof. exact (@lem3488487 _90535 _90546 (@lem3487558 _90535 _90546 h1)). Qed.
Lemma lem3488489 {_90535 _90546 : Type'} (h1 : term57 _90535 _90546) : (term57 _90535 _90546) = False.
Proof. exact (prop_ext (fun h2 : term57 _90535 _90546 => @lem3488488 _90535 _90546 h1) (fun h2 : False => @lem3487558 _90535 _90546 h1)). Qed.
Lemma lem3488490 {_90535 _90546 : Type'} (h1 : term57 _90535 _90546) : False.
Proof. exact (EQ_MP (@lem3488489 _90535 _90546 h1) (@lem3487558 _90535 _90546 h1)). Qed.
Lemma lem3488491 {_90535 _90546 : Type'} : term56 _90535 _90546.
Proof. exact (fun h0 : term57 _90535 _90546 => @lem3488490 _90535 _90546 h0). Qed.
Lemma lem3488492 {_90535 _90546 : Type'} : term54 _90535 _90546.
Proof. exact (EQ_MP (@lem3487557 _90535 _90546) (@lem3488491 _90535 _90546)). Qed.
Lemma lem3488493 {_90535 _90546 : Type'} : term16 _90535 _90546.
Proof. exact (EQ_MP (@lem3487553 _90535 _90546) (@lem3488492 _90535 _90546)). Qed.
Lemma lem3488494 {_90535 _90546 : Type'} : term15 _90535 _90546.
Proof. exact (EQ_MP (@lem3487390 _90535 _90546) (@lem3488493 _90535 _90546)). Qed.
