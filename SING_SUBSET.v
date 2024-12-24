Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SING_SUBSET_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm1834_spec.
Require Import thm18392_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211692_spec.
Require Import thm3211693_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Lemma lem3220356 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3220357 {_84443 : Type'} (s : _84443 -> Prop) (t : _84443 -> Prop) : (@SUBSET _84443 s t) = (term0 _84443 s t).
Proof. exact (@lem3220356 _84443 s t). Qed.
Lemma lem3220358 {_84443 : Type'} (x : _84443) (s : _84443 -> Prop) : (term1 _84443 x s) = (term2 _84443 x s).
Proof. exact (@lem3220357 _84443 (@INSERT _84443 x (@EMPTY _84443)) s). Qed.
Lemma lem3220365 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3220366 {_84443 : Type'} (x : _84443) (s : _84443 -> Prop) : (term3 _84443 x s) = (term4 _84443 x s).
Proof. exact (MK_COMB (@lem3220365) (@lem3220358 _84443 x s)). Qed.
Lemma lem3220367 {_84443 : Type'} (x : _84443) (s : _84443 -> Prop) : (@IN _84443 x s) = (@IN _84443 x s).
Proof. exact (eq_refl (@IN _84443 x s)). Qed.
Lemma lem3220368 {_84443 : Type'} (x : _84443) (s : _84443 -> Prop) : ((term1 _84443 x s) = (@IN _84443 x s)) = ((term2 _84443 x s) = (@IN _84443 x s)).
Proof. exact (MK_COMB (@lem3220366 _84443 x s) (@lem3220367 _84443 x s)). Qed.
Lemma lem3220373 {_84443 : Type'} (s : _84443 -> Prop) : (term5 _84443 s) = (term6 _84443 s).
Proof. exact (fun_ext (fun x : _84443 => @lem3220368 _84443 x s)). Qed.
Lemma lem3220374 {_84443 : Type'} : (@all _84443) = (@all _84443).
Proof. exact (eq_refl (@all _84443)). Qed.
Lemma lem3220375 {_84443 : Type'} (s : _84443 -> Prop) : (term7 _84443 s) = (term8 _84443 s).
Proof. exact (MK_COMB (@lem3220374 _84443) (@lem3220373 _84443 s)). Qed.
Lemma lem3220380 {_84443 : Type'} : (term9 _84443) = (term10 _84443).
Proof. exact (fun_ext (fun s : _84443 -> Prop => @lem3220375 _84443 s)). Qed.
Lemma lem3220381 {_84443 : Type'} : (@all (_84443 -> Prop)) = (@all (_84443 -> Prop)).
Proof. exact (eq_refl (@all (_84443 -> Prop))). Qed.
Lemma lem3220382 {_84443 : Type'} : (term11 _84443) = (term12 _84443).
Proof. exact (MK_COMB (@lem3220381 _84443) (@lem3220380 _84443)). Qed.
Lemma lem3220387 {_84443 : Type'} : (term12 _84443) = (term11 _84443).
Proof. exact (SYM (@lem3220382 _84443)). Qed.
Lemma lem3220405 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term13 A x y s) = (term14 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3220406 {_84443 : Type'} (y : _84443) (x : _84443) (s : _84443 -> Prop) : (term13 _84443 x y s) = (term14 _84443 y x s).
Proof. exact (@lem3220405 _84443 y x s). Qed.
Lemma lem3220407 {_84443 : Type'} (x : _84443) (x' : _84443) : (term15 _84443 x' x) = (term16 _84443 x x').
Proof. exact (@lem3220406 _84443 x x' (@EMPTY _84443)). Qed.
Lemma lem3220413 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3220414 {_84443 : Type'} (x : _84443) : (@IN _84443 x (@EMPTY _84443)) = False.
Proof. exact (@lem3220413 _84443 x). Qed.
Lemma lem3220415 {_84443 : Type'} (x' : _84443) : (@IN _84443 x' (@EMPTY _84443)) = False.
Proof. exact (@lem3220414 _84443 x'). Qed.
Lemma lem3220416 {_84443 : Type'} (x' : _84443) (x : _84443) : (term17 _84443 x' x) = (term17 _84443 x' x).
Proof. exact (eq_refl (term17 _84443 x' x)). Qed.
Lemma lem3220417 {_84443 : Type'} (x' : _84443) (x : _84443) : (term16 _84443 x x') = (term18 _84443 x' x).
Proof. exact (MK_COMB (@lem3220416 _84443 x' x) (@lem3220415 _84443 x')). Qed.
Lemma lem3220419 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem3220420 {_84443 : Type'} (x' : _84443) (x : _84443) : (term18 _84443 x' x) = (x' = x).
Proof. exact (@lem3220419 (x' = x)). Qed.
Lemma lem3220423 {_84443 : Type'} (x' : _84443) (x : _84443) : (term16 _84443 x x') = (x' = x).
Proof. exact (TRANS (@lem3220417 _84443 x' x) (@lem3220420 _84443 x' x)). Qed.
Lemma lem3220424 {_84443 : Type'} (x' : _84443) (x : _84443) : (term15 _84443 x' x) = (x' = x).
Proof. exact (TRANS (@lem3220407 _84443 x x') (@lem3220423 _84443 x' x)). Qed.
Lemma lem3220425 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3220426 {_84443 : Type'} (x' : _84443) (x : _84443) : (term19 _84443 x' x) = (term20 _84443 x' x).
Proof. exact (MK_COMB (@lem3220425) (@lem3220424 _84443 x' x)). Qed.
Lemma lem3220428 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3220429 {_84443 : Type'} (P : _84443 -> Prop) (x : _84443) : (@IN _84443 x P) = (P x).
Proof. exact (@lem3220428 _84443 P x). Qed.
Lemma lem3220430 {_84443 : Type'} (s : _84443 -> Prop) (x' : _84443) : (@IN _84443 x' s) = (s x').
Proof. exact (@lem3220429 _84443 s x'). Qed.
Lemma lem3220431 {_84443 : Type'} (x : _84443) (s : _84443 -> Prop) (x' : _84443) : (term21 _84443 x x' s) = (term22 _84443 x s x').
Proof. exact (MK_COMB (@lem3220426 _84443 x' x) (@lem3220430 _84443 s x')). Qed.
Lemma lem3220436 {_84443 : Type'} (x : _84443) (s : _84443 -> Prop) : (term23 _84443 x s) = (term24 _84443 x s).
Proof. exact (fun_ext (fun x' : _84443 => @lem3220431 _84443 x s x')). Qed.
Lemma lem3220437 {_84443 : Type'} : (@all _84443) = (@all _84443).
Proof. exact (eq_refl (@all _84443)). Qed.
Lemma lem3220438 {_84443 : Type'} (x : _84443) (s : _84443 -> Prop) : (term2 _84443 x s) = (term25 _84443 x s).
Proof. exact (MK_COMB (@lem3220437 _84443) (@lem3220436 _84443 x s)). Qed.
Lemma lem3220443 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3220444 {_84443 : Type'} (x : _84443) (s : _84443 -> Prop) : (term4 _84443 x s) = (term26 _84443 x s).
Proof. exact (MK_COMB (@lem3220443) (@lem3220438 _84443 x s)). Qed.
Lemma lem3220446 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3220447 {_84443 : Type'} (P : _84443 -> Prop) (x : _84443) : (@IN _84443 x P) = (P x).
Proof. exact (@lem3220446 _84443 P x). Qed.
Lemma lem3220448 {_84443 : Type'} (s : _84443 -> Prop) (x : _84443) : (@IN _84443 x s) = (s x).
Proof. exact (@lem3220447 _84443 s x). Qed.
Lemma lem3220449 {_84443 : Type'} (s : _84443 -> Prop) (x : _84443) : ((term2 _84443 x s) = (@IN _84443 x s)) = ((term25 _84443 x s) = (s x)).
Proof. exact (MK_COMB (@lem3220444 _84443 x s) (@lem3220448 _84443 s x)). Qed.
Lemma lem3220452 {_84443 : Type'} (s : _84443 -> Prop) : (term6 _84443 s) = (term27 _84443 s).
Proof. exact (fun_ext (fun x : _84443 => @lem3220449 _84443 s x)). Qed.
Lemma lem3220453 {_84443 : Type'} : (@all _84443) = (@all _84443).
Proof. exact (eq_refl (@all _84443)). Qed.
Lemma lem3220454 {_84443 : Type'} (s : _84443 -> Prop) : (term8 _84443 s) = (term28 _84443 s).
Proof. exact (MK_COMB (@lem3220453 _84443) (@lem3220452 _84443 s)). Qed.
Lemma lem3220459 {_84443 : Type'} : (term10 _84443) = (term29 _84443).
Proof. exact (fun_ext (fun s : _84443 -> Prop => @lem3220454 _84443 s)). Qed.
Lemma lem3220460 {_84443 : Type'} : (@all (_84443 -> Prop)) = (@all (_84443 -> Prop)).
Proof. exact (eq_refl (@all (_84443 -> Prop))). Qed.
Lemma lem3220461 {_84443 : Type'} : (term12 _84443) = (term30 _84443).
Proof. exact (MK_COMB (@lem3220460 _84443) (@lem3220459 _84443)). Qed.
Lemma lem3220466 {_84443 : Type'} : (term30 _84443) = (term12 _84443).
Proof. exact (SYM (@lem3220461 _84443)). Qed.
Lemma lem3220468 (p : Prop) : p = (term31 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3220469 {_84443 : Type'} : (term30 _84443) = (term32 _84443).
Proof. exact (@lem3220468 (term30 _84443)). Qed.
Lemma lem3220470 {_84443 : Type'} : (term32 _84443) = (term30 _84443).
Proof. exact (SYM (@lem3220469 _84443)). Qed.
Lemma lem3220471 {_84443 : Type'} (h1 : term33 _84443) : term33 _84443.
Proof. exact (h1). Qed.
Lemma lem3220474 {_84443 : Type'} (h1 : term32 _84443) : term32 _84443.
Proof. exact (h1). Qed.
Lemma lem3220475 {_84443 : Type'} : term34 _84443.
Proof. exact (fun h0 : term32 _84443 => @lem3220474 _84443 h0). Qed.
Lemma lem3220476 {_84443 : Type'} (h1 : term34 _84443) : term34 _84443.
Proof. exact (h1). Qed.
Lemma lem3220477 {_84443 : Type'} (h1 : term32 _84443) : term32 _84443.
Proof. exact (h1). Qed.
Lemma lem3220478 {_84443 : Type'} (h1 : term32 _84443) (h2 : term34 _84443) : term32 _84443.
Proof. exact (@lem3220476 _84443 h2 (@lem3220477 _84443 h1)). Qed.
Lemma lem3220479 {_84443 : Type'} (h1 : term32 _84443) : term35 _84443.
Proof. exact (fun h0 : term34 _84443 => @lem3220478 _84443 h1 h0). Qed.
Lemma lem3220480 {_84443 : Type'} (h1 : term34 _84443) : term34 _84443.
Proof. exact (h1). Qed.
Lemma lem3220481 {_84443 : Type'} (h1 : term32 _84443) (h2 : term34 _84443) : term32 _84443.
Proof. exact (@lem3220479 _84443 h1 (@lem3220480 _84443 h2)). Qed.
Lemma lem3220482 {_84443 : Type'} (h1 : term34 _84443) : term34 _84443.
Proof. exact (fun h0 : term32 _84443 => @lem3220481 _84443 h0 h1). Qed.
Lemma lem3220483 {_84443 : Type'} : term36 _84443.
Proof. exact (fun h0 : term34 _84443 => @lem3220482 _84443 h0). Qed.
Lemma lem3220486 {_84443 : Type'} : term34 _84443.
Proof. exact (@lem3220483 _84443 (@lem3220475 _84443)). Qed.
Lemma lem3220487 {_84443 : Type'} : term34 _84443.
Proof. exact (@lem3220486 _84443). Qed.
Lemma lem3220489 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3220490 {_84443 : Type'} : (term32 _84443) = (term37 _84443).
Proof. exact (@lem3220489 (term33 _84443)). Qed.
Lemma lem3220492 (t : Prop) : (term38 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3220493 {_84443 : Type'} : (term37 _84443) = (term30 _84443).
Proof. exact (@lem3220492 (term30 _84443)). Qed.
Lemma lem3220512 {_84443 : Type'} : (term32 _84443) = (term30 _84443).
Proof. exact (TRANS (@lem3220490 _84443) (@lem3220493 _84443)). Qed.
Lemma lem3220513 {_84443 : Type'} (s : _84443 -> Prop) (x : _84443) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem3220518 {_84443 : Type'} (x : _84443) (s : _84443 -> Prop) (x' : _84443) : (term22 _84443 x s x') = (term22 _84443 x s x').
Proof. exact (eq_refl (term22 _84443 x s x')). Qed.
Lemma lem3220519 {_84443 : Type'} (x : _84443) (s : _84443 -> Prop) : (term24 _84443 x s) = (term24 _84443 x s).
Proof. exact (fun_ext (fun x' : _84443 => @lem3220518 _84443 x s x')). Qed.
Lemma lem3220520 {_84443 : Type'} : (@all _84443) = (@all _84443).
Proof. exact (eq_refl (@all _84443)). Qed.
Lemma lem3220521 {_84443 : Type'} (x : _84443) (s : _84443 -> Prop) : (term25 _84443 x s) = (term25 _84443 x s).
Proof. exact (MK_COMB (@lem3220520 _84443) (@lem3220519 _84443 x s)). Qed.
Lemma lem3220522 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3220523 {_84443 : Type'} (x : _84443) (s : _84443 -> Prop) : (term26 _84443 x s) = (term26 _84443 x s).
Proof. exact (MK_COMB (@lem3220522) (@lem3220521 _84443 x s)). Qed.
Lemma lem3220524 {_84443 : Type'} (s : _84443 -> Prop) (x : _84443) : ((term25 _84443 x s) = (s x)) = ((term25 _84443 x s) = (s x)).
Proof. exact (MK_COMB (@lem3220523 _84443 x s) (@lem3220513 _84443 s x)). Qed.
Lemma lem3220525 {_84443 : Type'} (s : _84443 -> Prop) : (term27 _84443 s) = (term27 _84443 s).
Proof. exact (fun_ext (fun x : _84443 => @lem3220524 _84443 s x)). Qed.
Lemma lem3220526 {_84443 : Type'} : (@all _84443) = (@all _84443).
Proof. exact (eq_refl (@all _84443)). Qed.
Lemma lem3220527 {_84443 : Type'} (s : _84443 -> Prop) : (term28 _84443 s) = (term28 _84443 s).
Proof. exact (MK_COMB (@lem3220526 _84443) (@lem3220525 _84443 s)). Qed.
Lemma lem3220528 {_84443 : Type'} : (term29 _84443) = (term29 _84443).
Proof. exact (fun_ext (fun s : _84443 -> Prop => @lem3220527 _84443 s)). Qed.
Lemma lem3220529 {_84443 : Type'} : (@all (_84443 -> Prop)) = (@all (_84443 -> Prop)).
Proof. exact (eq_refl (@all (_84443 -> Prop))). Qed.
Lemma lem3220530 {_84443 : Type'} : (term30 _84443) = (term30 _84443).
Proof. exact (MK_COMB (@lem3220529 _84443) (@lem3220528 _84443)). Qed.
Lemma lem3220553 {_84443 : Type'} : (term32 _84443) = (term30 _84443).
Proof. exact (TRANS (@lem3220512 _84443) (@lem3220530 _84443)). Qed.
Lemma lem3220554 {_84443 : Type'} : (term30 _84443) = (term32 _84443).
Proof. exact (SYM (@lem3220553 _84443)). Qed.
Lemma lem3220556 (p : Prop) : p = (term31 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3220557 {_84443 : Type'} (s : _84443 -> Prop) (x : _84443) : ((term25 _84443 x s) = (s x)) = (term39 _84443 s x).
Proof. exact (@lem3220556 ((term25 _84443 x s) = (s x))). Qed.
Lemma lem3220558 {_84443 : Type'} (s : _84443 -> Prop) (x : _84443) : (term39 _84443 s x) = ((term25 _84443 x s) = (s x)).
Proof. exact (SYM (@lem3220557 _84443 s x)). Qed.
Lemma lem3220559 {_84443 : Type'} (s : _84443 -> Prop) (x : _84443) (h1 : term40 _84443 s x) : term40 _84443 s x.
Proof. exact (h1). Qed.
Lemma lem3220568 {_84443 : Type'} (x : _84443) (s : _84443 -> Prop) (x' : _84443) : (term41 _84443 x s x') = (term42 _84443 x s x').
Proof. exact (@lem17362 (x' = x) (s x')). Qed.
Lemma lem3220573 {_84443 : Type'} (x : _84443) (s : _84443 -> Prop) (x' : _84443) : (term22 _84443 x s x') = (term43 _84443 x s x').
Proof. exact (@lem17265 (x' = x) (s x')). Qed.
Lemma lem3220574 {_84443 : Type'} (P : _84443 -> Prop) : (term44 _84443 P) = (term45 _84443 P).
Proof. exact (@lem18392 _84443 P). Qed.
Lemma lem3220575 {_84443 : Type'} (x : _84443) (s : _84443 -> Prop) : (term46 _84443 x s) = (term47 _84443 x s).
Proof. exact (@lem3220574 _84443 (term24 _84443 x s)). Qed.
Lemma lem3220576 {_84443 : Type'} (x : _84443) (s : _84443 -> Prop) (x' : _84443) : (term48 _84443 x s x') = (term22 _84443 x s x').
Proof. exact (eq_refl (term48 _84443 x s x')). Qed.
Lemma lem3220577 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3220578 {_84443 : Type'} (x : _84443) (s : _84443 -> Prop) (x' : _84443) : (term49 _84443 x s x') = (term41 _84443 x s x').
Proof. exact (MK_COMB (@lem3220577) (@lem3220576 _84443 x s x')). Qed.
Lemma lem3220579 {_84443 : Type'} (x : _84443) (s : _84443 -> Prop) (x' : _84443) : (term49 _84443 x s x') = (term42 _84443 x s x').
Proof. exact (TRANS (@lem3220578 _84443 x s x') (@lem3220568 _84443 x s x')). Qed.
Lemma lem3220580 {_84443 : Type'} (x : _84443) (s : _84443 -> Prop) : (term50 _84443 x s) = (term51 _84443 x s).
Proof. exact (fun_ext (fun x' : _84443 => @lem3220579 _84443 x s x')). Qed.
Lemma lem3220581 {_84443 : Type'} : (@ex _84443) = (@ex _84443).
Proof. exact (eq_refl (@ex _84443)). Qed.
Lemma lem3220582 {_84443 : Type'} (x : _84443) (s : _84443 -> Prop) : (term47 _84443 x s) = (term52 _84443 x s).
Proof. exact (MK_COMB (@lem3220581 _84443) (@lem3220580 _84443 x s)). Qed.
Lemma lem3220583 {_84443 : Type'} (x : _84443) (s : _84443 -> Prop) : (term46 _84443 x s) = (term52 _84443 x s).
Proof. exact (TRANS (@lem3220575 _84443 x s) (@lem3220582 _84443 x s)). Qed.
Lemma lem3220584 {_84443 : Type'} (x : _84443) (s : _84443 -> Prop) : (term24 _84443 x s) = (term53 _84443 x s).
Proof. exact (fun_ext (fun x' : _84443 => @lem3220573 _84443 x s x')). Qed.
Lemma lem3220585 {_84443 : Type'} : (@all _84443) = (@all _84443).
Proof. exact (eq_refl (@all _84443)). Qed.
Lemma lem3220586 {_84443 : Type'} (x : _84443) (s : _84443 -> Prop) : (term25 _84443 x s) = (term54 _84443 x s).
Proof. exact (MK_COMB (@lem3220585 _84443) (@lem3220584 _84443 x s)). Qed.
Lemma lem3220587 {_84443 : Type'} (s : _84443 -> Prop) (x : _84443) : (term55 _84443 s x) = (term55 _84443 s x).
Proof. exact (eq_refl (term55 _84443 s x)). Qed.
Lemma lem3220588 {_84443 : Type'} (s : _84443 -> Prop) (x : _84443) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem3220589 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3220590 {_84443 : Type'} (x : _84443) (s : _84443 -> Prop) : (term56 _84443 x s) = (term57 _84443 x s).
Proof. exact (MK_COMB (@lem3220589) (@lem3220583 _84443 x s)). Qed.
Lemma lem3220591 {_84443 : Type'} (s : _84443 -> Prop) (x : _84443) : (term58 _84443 s x) = (term59 _84443 s x).
Proof. exact (MK_COMB (@lem3220590 _84443 x s) (@lem3220588 _84443 s x)). Qed.
Lemma lem3220592 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3220593 {_84443 : Type'} (x : _84443) (s : _84443 -> Prop) : (term60 _84443 x s) = (term61 _84443 x s).
Proof. exact (MK_COMB (@lem3220592) (@lem3220586 _84443 x s)). Qed.
Lemma lem3220594 {_84443 : Type'} (s : _84443 -> Prop) (x : _84443) : (term62 _84443 s x) = (term63 _84443 s x).
Proof. exact (MK_COMB (@lem3220593 _84443 x s) (@lem3220587 _84443 s x)). Qed.
Lemma lem3220595 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3220596 {_84443 : Type'} (s : _84443 -> Prop) (x : _84443) : (term64 _84443 s x) = (term65 _84443 s x).
Proof. exact (MK_COMB (@lem3220595) (@lem3220594 _84443 s x)). Qed.
Lemma lem3220597 {_84443 : Type'} (s : _84443 -> Prop) (x : _84443) : (term66 _84443 s x) = (term67 _84443 s x).
Proof. exact (MK_COMB (@lem3220596 _84443 s x) (@lem3220591 _84443 s x)). Qed.
Lemma lem3220598 {_84443 : Type'} (s : _84443 -> Prop) (x : _84443) : (term40 _84443 s x) = (term66 _84443 s x).
Proof. exact (@lem17646 (term25 _84443 x s) (s x)). Qed.
Lemma lem3220599 {_84443 : Type'} (s : _84443 -> Prop) (x : _84443) : (term40 _84443 s x) = (term67 _84443 s x).
Proof. exact (TRANS (@lem3220598 _84443 s x) (@lem3220597 _84443 s x)). Qed.
Lemma lem3220682 {A : Type'} (P : A -> Prop) (Q : Prop) : (term68 A P Q) = (term69 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3220683 {_84443 : Type'} (P : _84443 -> Prop) (Q : Prop) : (term68 _84443 P Q) = (term69 _84443 P Q).
Proof. exact (@lem3220682 _84443 P Q). Qed.
Lemma lem3220684 {_84443 : Type'} (s : _84443 -> Prop) (x : _84443) : (term70 _84443 s x) = (term71 _84443 s x).
Proof. exact (@lem3220683 _84443 (term51 _84443 x s) (s x)). Qed.
Lemma lem3220685 {_84443 : Type'} (x : _84443) (s : _84443 -> Prop) (x' : _84443) : (term72 _84443 x s x') = (term42 _84443 x s x').
Proof. exact (eq_refl (term72 _84443 x s x')). Qed.
Lemma lem3220686 {_84443 : Type'} (x : _84443) (s : _84443 -> Prop) : (term73 _84443 x s) = (term51 _84443 x s).
Proof. exact (fun_ext (fun x' : _84443 => @lem3220685 _84443 x s x')). Qed.
Lemma lem3220687 {_84443 : Type'} : (@ex _84443) = (@ex _84443).
Proof. exact (eq_refl (@ex _84443)). Qed.
Lemma lem3220688 {_84443 : Type'} (x : _84443) (s : _84443 -> Prop) : (term74 _84443 x s) = (term52 _84443 x s).
Proof. exact (MK_COMB (@lem3220687 _84443) (@lem3220686 _84443 x s)). Qed.
Lemma lem3220689 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3220690 {_84443 : Type'} (x : _84443) (s : _84443 -> Prop) : (term75 _84443 x s) = (term57 _84443 x s).
Proof. exact (MK_COMB (@lem3220689) (@lem3220688 _84443 x s)). Qed.
Lemma lem3220691 {_84443 : Type'} (s : _84443 -> Prop) (x : _84443) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem3220692 {_84443 : Type'} (s : _84443 -> Prop) (x : _84443) : (term70 _84443 s x) = (term59 _84443 s x).
Proof. exact (MK_COMB (@lem3220690 _84443 x s) (@lem3220691 _84443 s x)). Qed.
Lemma lem3220693 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3220694 {_84443 : Type'} (s : _84443 -> Prop) (x : _84443) : (term76 _84443 s x) = (term77 _84443 s x).
Proof. exact (MK_COMB (@lem3220693) (@lem3220692 _84443 s x)). Qed.
Lemma lem3220695 {_84443 : Type'} (x : _84443) (s : _84443 -> Prop) (x' : _84443) : (term72 _84443 x s x') = (term42 _84443 x s x').
Proof. exact (eq_refl (term72 _84443 x s x')). Qed.
Lemma lem3220696 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3220697 {_84443 : Type'} (x : _84443) (s : _84443 -> Prop) (x' : _84443) : (term78 _84443 x s x') = (term79 _84443 x s x').
Proof. exact (MK_COMB (@lem3220696) (@lem3220695 _84443 x s x')). Qed.
Lemma lem3220698 {_84443 : Type'} (s : _84443 -> Prop) (x : _84443) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem3220699 {_84443 : Type'} (x' : _84443) (s : _84443 -> Prop) (x : _84443) : (term80 _84443 x' s x) = (term81 _84443 x' s x).
Proof. exact (MK_COMB (@lem3220697 _84443 x s x') (@lem3220698 _84443 s x)). Qed.
Lemma lem3220700 {_84443 : Type'} (s : _84443 -> Prop) (x : _84443) : (term82 _84443 s x) = (term83 _84443 s x).
Proof. exact (fun_ext (fun x' : _84443 => @lem3220699 _84443 x' s x)). Qed.
Lemma lem3220701 {_84443 : Type'} : (@ex _84443) = (@ex _84443).
Proof. exact (eq_refl (@ex _84443)). Qed.
Lemma lem3220702 {_84443 : Type'} (s : _84443 -> Prop) (x : _84443) : (term71 _84443 s x) = (term84 _84443 s x).
Proof. exact (MK_COMB (@lem3220701 _84443) (@lem3220700 _84443 s x)). Qed.
Lemma lem3220703 {_84443 : Type'} (s : _84443 -> Prop) (x : _84443) : ((term70 _84443 s x) = (term71 _84443 s x)) = ((term59 _84443 s x) = (term84 _84443 s x)).
Proof. exact (MK_COMB (@lem3220694 _84443 s x) (@lem3220702 _84443 s x)). Qed.
Lemma lem3220704 {_84443 : Type'} (s : _84443 -> Prop) (x : _84443) : (term59 _84443 s x) = (term84 _84443 s x).
Proof. exact (EQ_MP (@lem3220703 _84443 s x) (@lem3220684 _84443 s x)). Qed.
Lemma lem3220705 {_84443 : Type'} (s : _84443 -> Prop) (x : _84443) : (term65 _84443 s x) = (term65 _84443 s x).
Proof. exact (eq_refl (term65 _84443 s x)). Qed.
Lemma lem3220706 {_84443 : Type'} (s : _84443 -> Prop) (x : _84443) : (term67 _84443 s x) = (term85 _84443 s x).
Proof. exact (MK_COMB (@lem3220705 _84443 s x) (@lem3220704 _84443 s x)). Qed.
Lemma lem3220708 {A : Type'} (P : Prop) (Q : A -> Prop) : (term86 A P Q) = (term87 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3220709 {_84443 : Type'} (P : Prop) (Q : _84443 -> Prop) : (term86 _84443 P Q) = (term87 _84443 P Q).
Proof. exact (@lem3220708 _84443 P Q). Qed.
Lemma lem3220710 {_84443 : Type'} (s : _84443 -> Prop) (x : _84443) : (term88 _84443 s x) = (term89 _84443 s x).
Proof. exact (@lem3220709 _84443 (term63 _84443 s x) (term83 _84443 s x)). Qed.
Lemma lem3220711 {_84443 : Type'} (x' : _84443) (s : _84443 -> Prop) (x : _84443) : (term90 _84443 s x x') = (term81 _84443 x' s x).
Proof. exact (eq_refl (term90 _84443 s x x')). Qed.
Lemma lem3220712 {_84443 : Type'} (s : _84443 -> Prop) (x : _84443) : (term91 _84443 s x) = (term83 _84443 s x).
Proof. exact (fun_ext (fun x' : _84443 => @lem3220711 _84443 x' s x)). Qed.
Lemma lem3220713 {_84443 : Type'} : (@ex _84443) = (@ex _84443).
Proof. exact (eq_refl (@ex _84443)). Qed.
Lemma lem3220714 {_84443 : Type'} (s : _84443 -> Prop) (x : _84443) : (term92 _84443 s x) = (term84 _84443 s x).
Proof. exact (MK_COMB (@lem3220713 _84443) (@lem3220712 _84443 s x)). Qed.
Lemma lem3220715 {_84443 : Type'} (s : _84443 -> Prop) (x : _84443) : (term65 _84443 s x) = (term65 _84443 s x).
Proof. exact (eq_refl (term65 _84443 s x)). Qed.
Lemma lem3220716 {_84443 : Type'} (s : _84443 -> Prop) (x : _84443) : (term88 _84443 s x) = (term85 _84443 s x).
Proof. exact (MK_COMB (@lem3220715 _84443 s x) (@lem3220714 _84443 s x)). Qed.
Lemma lem3220717 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3220718 {_84443 : Type'} (s : _84443 -> Prop) (x : _84443) : (term93 _84443 s x) = (term94 _84443 s x).
Proof. exact (MK_COMB (@lem3220717) (@lem3220716 _84443 s x)). Qed.
Lemma lem3220719 {_84443 : Type'} (x' : _84443) (s : _84443 -> Prop) (x : _84443) : (term90 _84443 s x x') = (term81 _84443 x' s x).
Proof. exact (eq_refl (term90 _84443 s x x')). Qed.
Lemma lem3220720 {_84443 : Type'} (s : _84443 -> Prop) (x : _84443) : (term65 _84443 s x) = (term65 _84443 s x).
Proof. exact (eq_refl (term65 _84443 s x)). Qed.
Lemma lem3220721 {_84443 : Type'} (x' : _84443) (s : _84443 -> Prop) (x : _84443) : (term95 _84443 s x x') = (term96 _84443 x' s x).
Proof. exact (MK_COMB (@lem3220720 _84443 s x) (@lem3220719 _84443 x' s x)). Qed.
Lemma lem3220722 {_84443 : Type'} (s : _84443 -> Prop) (x : _84443) : (term97 _84443 s x) = (term98 _84443 s x).
Proof. exact (fun_ext (fun x' : _84443 => @lem3220721 _84443 x' s x)). Qed.
Lemma lem3220723 {_84443 : Type'} : (@ex _84443) = (@ex _84443).
Proof. exact (eq_refl (@ex _84443)). Qed.
Lemma lem3220724 {_84443 : Type'} (s : _84443 -> Prop) (x : _84443) : (term89 _84443 s x) = (term99 _84443 s x).
Proof. exact (MK_COMB (@lem3220723 _84443) (@lem3220722 _84443 s x)). Qed.
Lemma lem3220725 {_84443 : Type'} (s : _84443 -> Prop) (x : _84443) : ((term88 _84443 s x) = (term89 _84443 s x)) = ((term85 _84443 s x) = (term99 _84443 s x)).
Proof. exact (MK_COMB (@lem3220718 _84443 s x) (@lem3220724 _84443 s x)). Qed.
Lemma lem3220726 {_84443 : Type'} (s : _84443 -> Prop) (x : _84443) : (term85 _84443 s x) = (term99 _84443 s x).
Proof. exact (EQ_MP (@lem3220725 _84443 s x) (@lem3220710 _84443 s x)). Qed.
Lemma lem3220728 {_84443 : Type'} (s : _84443 -> Prop) (x : _84443) : (term67 _84443 s x) = (term99 _84443 s x).
Proof. exact (TRANS (@lem3220706 _84443 s x) (@lem3220726 _84443 s x)). Qed.
Lemma lem3220729 {_84443 : Type'} (s : _84443 -> Prop) (x : _84443) : (term40 _84443 s x) = (term99 _84443 s x).
Proof. exact (TRANS (@lem3220599 _84443 s x) (@lem3220728 _84443 s x)). Qed.
Lemma lem3220730 {_84443 : Type'} (s : _84443 -> Prop) (x : _84443) (h1 : term40 _84443 s x) : term99 _84443 s x.
Proof. exact (EQ_MP (@lem3220729 _84443 s x) (@lem3220559 _84443 s x h1)). Qed.
Lemma lem3220731 {_84443 : Type'} (x' : _84443) (s : _84443 -> Prop) (x : _84443) (h1 : term96 _84443 x' s x) : term96 _84443 x' s x.
Proof. exact (h1). Qed.
Lemma lem3220750 {_84443 : Type'} (x' : _84443) (s : _84443 -> Prop) (x : _84443) : (term81 _84443 x' s x) = (term81 _84443 x' s x).
Proof. exact (eq_refl (term81 _84443 x' s x)). Qed.
Lemma lem3220755 {_84443 : Type'} (s : _84443 -> Prop) (x : _84443) : (term55 _84443 s x) = (term55 _84443 s x).
Proof. exact (eq_refl (term55 _84443 s x)). Qed.
Lemma lem3220768 {_84443 : Type'} (x : _84443) (s : _84443 -> Prop) (x' : _84443) : (term43 _84443 x s x') = (term43 _84443 x s x').
Proof. exact (eq_refl (term43 _84443 x s x')). Qed.
Lemma lem3220769 {_84443 : Type'} (x : _84443) (s : _84443 -> Prop) : (term53 _84443 x s) = (term53 _84443 x s).
Proof. exact (fun_ext (fun x' : _84443 => @lem3220768 _84443 x s x')). Qed.
Lemma lem3220770 {_84443 : Type'} : (@all _84443) = (@all _84443).
Proof. exact (eq_refl (@all _84443)). Qed.
Lemma lem3220771 {_84443 : Type'} (x : _84443) (s : _84443 -> Prop) : (term54 _84443 x s) = (term54 _84443 x s).
Proof. exact (MK_COMB (@lem3220770 _84443) (@lem3220769 _84443 x s)). Qed.
Lemma lem3220772 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3220773 {_84443 : Type'} (x : _84443) (s : _84443 -> Prop) : (term61 _84443 x s) = (term61 _84443 x s).
Proof. exact (MK_COMB (@lem3220772) (@lem3220771 _84443 x s)). Qed.
Lemma lem3220774 {_84443 : Type'} (s : _84443 -> Prop) (x : _84443) : (term63 _84443 s x) = (term63 _84443 s x).
Proof. exact (MK_COMB (@lem3220773 _84443 x s) (@lem3220755 _84443 s x)). Qed.
Lemma lem3220775 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3220776 {_84443 : Type'} (s : _84443 -> Prop) (x : _84443) : (term65 _84443 s x) = (term65 _84443 s x).
Proof. exact (MK_COMB (@lem3220775) (@lem3220774 _84443 s x)). Qed.
Lemma lem3220777 {_84443 : Type'} (x' : _84443) (s : _84443 -> Prop) (x : _84443) : (term96 _84443 x' s x) = (term96 _84443 x' s x).
Proof. exact (MK_COMB (@lem3220776 _84443 s x) (@lem3220750 _84443 x' s x)). Qed.
Lemma lem3220778 {_84443 : Type'} (x' : _84443) (s : _84443 -> Prop) (x : _84443) (h1 : term96 _84443 x' s x) : term96 _84443 x' s x.
Proof. exact (EQ_MP (@lem3220777 _84443 x' s x) (@lem3220731 _84443 x' s x h1)). Qed.
Lemma lem3220779 {_84443 : Type'} (s : _84443 -> Prop) (x : _84443) (h1 : term63 _84443 s x) : term63 _84443 s x.
Proof. exact (h1). Qed.
Lemma lem3220780 {_84443 : Type'} (x' : _84443) (s : _84443 -> Prop) (x : _84443) (h1 : term81 _84443 x' s x) : term81 _84443 x' s x.
Proof. exact (h1). Qed.
Lemma lem3220782 {_84443 : Type'} (s : _84443 -> Prop) (x : _84443) (h1 : term63 _84443 s x) : term54 _84443 x s.
Proof. exact (proj1 (@lem3220779 _84443 s x h1)). Qed.
Lemma lem3220784 {_84443 : Type'} (x' : _84443) (s : _84443 -> Prop) (x : _84443) (h1 : term81 _84443 x' s x) : term42 _84443 x s x'.
Proof. exact (proj1 (@lem3220780 _84443 x' s x h1)). Qed.
Lemma lem3220794 {_84443 : Type'} (x : _84443) (s : _84443 -> Prop) (x' : _84443) : (term43 _84443 x s x') = (term43 _84443 x s x').
Proof. exact (eq_refl (term43 _84443 x s x')). Qed.
Lemma lem3220795 {_84443 : Type'} (x : _84443) (s : _84443 -> Prop) : (term53 _84443 x s) = (term53 _84443 x s).
Proof. exact (fun_ext (fun x' : _84443 => @lem3220794 _84443 x s x')). Qed.
Lemma lem3220796 {_84443 : Type'} : (@all _84443) = (@all _84443).
Proof. exact (eq_refl (@all _84443)). Qed.
Lemma lem3220798 {_84443 : Type'} (x : _84443) (s : _84443 -> Prop) : (term54 _84443 x s) = (term54 _84443 x s).
Proof. exact (MK_COMB (@lem3220796 _84443) (@lem3220795 _84443 x s)). Qed.
Lemma lem3220799 {_84443 : Type'} (s : _84443 -> Prop) (x : _84443) (h1 : term63 _84443 s x) : term54 _84443 x s.
Proof. exact (EQ_MP (@lem3220798 _84443 x s) (@lem3220782 _84443 s x h1)). Qed.
Lemma lem3220816 {_84443 : Type'} (_33118 : _84443) (s : _84443 -> Prop) (x : _84443) (h1 : term63 _84443 s x) : term100 _84443 x s _33118.
Proof. exact (@lem3220799 _84443 s x h1 _33118). Qed.
Lemma lem3220817 {_84443 : Type'} (x : _84443) (s : _84443 -> Prop) (_33118 : _84443) : (term100 _84443 x s _33118) = (term43 _84443 x s _33118).
Proof. exact (eq_refl (term100 _84443 x s _33118)). Qed.
Lemma lem3220824 {_84443 : Type'} (_33118 : _84443) (s : _84443 -> Prop) (x : _84443) (h1 : term63 _84443 s x) : term43 _84443 x s _33118.
Proof. exact (EQ_MP (@lem3220817 _84443 x s _33118) (@lem3220816 _84443 _33118 s x h1)). Qed.
Lemma lem3220826 {_84443 : Type'} (s : _84443 -> Prop) (x : _84443) (h1 : term63 _84443 s x) : term55 _84443 s x.
Proof. exact (proj2 (@lem3220779 _84443 s x h1)). Qed.
Lemma lem3220830 {_84443 : Type'} (x' : _84443) (s : _84443 -> Prop) (x : _84443) (h1 : term81 _84443 x' s x) : x' = x.
Proof. exact (proj1 (@lem3220784 _84443 x' s x h1)). Qed.
Lemma lem3220832 {_84443 : Type'} (x' : _84443) (s : _84443 -> Prop) (x : _84443) (h1 : term81 _84443 x' s x) : term55 _84443 s x'.
Proof. exact (proj2 (@lem3220784 _84443 x' s x h1)). Qed.
Lemma lem3220861 {_84443 : Type'} (s : _84443 -> Prop) : (term101 _84443 s) = (term101 _84443 s).
Proof. exact (eq_refl (term101 _84443 s)). Qed.
Lemma lem3220862 {_84443 : Type'} (x' : _84443) (s : _84443 -> Prop) (x : _84443) (h1 : term81 _84443 x' s x) : (term102 _84443 s x') = (term102 _84443 s x).
Proof. exact (MK_COMB (@lem3220861 _84443 s) (@lem3220830 _84443 x' s x h1)). Qed.
Lemma lem3220863 {_84443 : Type'} (s : _84443 -> Prop) (x : _84443) : (term102 _84443 s x) = (term55 _84443 s x).
Proof. exact (eq_refl (term102 _84443 s x)). Qed.
Lemma lem3220864 {_84443 : Type'} (s : _84443 -> Prop) (x' : _84443) : (term103 _84443 s x') = (term103 _84443 s x').
Proof. exact (eq_refl (term103 _84443 s x')). Qed.
Lemma lem3220865 {_84443 : Type'} (x' : _84443) (s : _84443 -> Prop) (x : _84443) : ((term102 _84443 s x') = (term102 _84443 s x)) = ((term102 _84443 s x') = (term55 _84443 s x)).
Proof. exact (MK_COMB (@lem3220864 _84443 s x') (@lem3220863 _84443 s x)). Qed.
Lemma lem3220866 {_84443 : Type'} (s : _84443 -> Prop) (x' : _84443) : (term102 _84443 s x') = (term55 _84443 s x').
Proof. exact (eq_refl (term102 _84443 s x')). Qed.
Lemma lem3220867 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3220868 {_84443 : Type'} (s : _84443 -> Prop) (x' : _84443) : (term103 _84443 s x') = (term104 _84443 s x').
Proof. exact (MK_COMB (@lem3220867) (@lem3220866 _84443 s x')). Qed.
Lemma lem3220869 {_84443 : Type'} (s : _84443 -> Prop) (x : _84443) : (term55 _84443 s x) = (term55 _84443 s x).
Proof. exact (eq_refl (term55 _84443 s x)). Qed.
Lemma lem3220870 {_84443 : Type'} (x' : _84443) (s : _84443 -> Prop) (x : _84443) : ((term102 _84443 s x') = (term55 _84443 s x)) = ((term55 _84443 s x') = (term55 _84443 s x)).
Proof. exact (MK_COMB (@lem3220868 _84443 s x') (@lem3220869 _84443 s x)). Qed.
Lemma lem3220871 {_84443 : Type'} (x' : _84443) (s : _84443 -> Prop) (x : _84443) : ((term102 _84443 s x') = (term102 _84443 s x)) = ((term55 _84443 s x') = (term55 _84443 s x)).
Proof. exact (TRANS (@lem3220865 _84443 x' s x) (@lem3220870 _84443 x' s x)). Qed.
Lemma lem3220872 {_84443 : Type'} (x' : _84443) (s : _84443 -> Prop) (x : _84443) (h1 : term81 _84443 x' s x) : (term55 _84443 s x') = (term55 _84443 s x).
Proof. exact (EQ_MP (@lem3220871 _84443 x' s x) (@lem3220862 _84443 x' s x h1)). Qed.
Lemma lem3220873 {_84443 : Type'} (x' : _84443) (s : _84443 -> Prop) (x : _84443) (h1 : term81 _84443 x' s x) : term55 _84443 s x.
Proof. exact (EQ_MP (@lem3220872 _84443 x' s x h1) (@lem3220832 _84443 x' s x h1)). Qed.
Lemma lem3220889 {_84443 : Type'} (x : _84443) : x = x.
Proof. exact (@lem21386 _84443 x). Qed.
Lemma lem3220890 {_84443 : Type'} (x : _84443) : x = x.
Proof. exact (@lem3220889 _84443 x). Qed.
Lemma lem3220891 {_84443 : Type'} (x : _84443) : term105 _84443 x.
Proof. exact (fun h0 : term106 _84443 x => @lem3220890 _84443 x). Qed.
Lemma lem3220893 (p : Prop) : (term107 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3220894 {_84443 : Type'} (x : _84443) : (term105 _84443 x) = (x = x).
Proof. exact (@lem3220893 (x = x)). Qed.
Lemma lem3220895 {_84443 : Type'} (x : _84443) : x = x.
Proof. exact (EQ_MP (@lem3220894 _84443 x) (@lem3220891 _84443 x)). Qed.
Lemma lem3220901 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3220902 {_84443 : Type'} (s : _84443 -> Prop) (_33118 : _84443) (x : _84443) : (term43 _84443 x s _33118) = (term108 _84443 s _33118 x).
Proof. exact (@lem3220901 (s _33118) (term109 _84443 _33118 x)). Qed.
Lemma lem3220910 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3220911 {_84443 : Type'} (s : _84443 -> Prop) (_33118 : _84443) (x : _84443) : (term110 _84443 x s _33118) = (term111 _84443 s _33118 x).
Proof. exact (MK_COMB (@lem3220910) (@lem3220902 _84443 s _33118 x)). Qed.
Lemma lem3220919 {_84443 : Type'} (s : _84443 -> Prop) (_33118 : _84443) (x : _84443) : (term108 _84443 s _33118 x) = (term108 _84443 s _33118 x).
Proof. exact (eq_refl (term108 _84443 s _33118 x)). Qed.
Lemma lem3220920 {_84443 : Type'} (s : _84443 -> Prop) (_33118 : _84443) (x : _84443) : ((term43 _84443 x s _33118) = (term108 _84443 s _33118 x)) = ((term108 _84443 s _33118 x) = (term108 _84443 s _33118 x)).
Proof. exact (MK_COMB (@lem3220911 _84443 s _33118 x) (@lem3220919 _84443 s _33118 x)). Qed.
Lemma lem3220922 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3220923 (x : Prop) : (x = x) = True.
Proof. exact (@lem3220922 Prop x). Qed.
Lemma lem3220924 {_84443 : Type'} (s : _84443 -> Prop) (_33118 : _84443) (x : _84443) : ((term108 _84443 s _33118 x) = (term108 _84443 s _33118 x)) = True.
Proof. exact (@lem3220923 (term108 _84443 s _33118 x)). Qed.
Lemma lem3220925 {_84443 : Type'} (s : _84443 -> Prop) (_33118 : _84443) (x : _84443) : ((term43 _84443 x s _33118) = (term108 _84443 s _33118 x)) = True.
Proof. exact (TRANS (@lem3220920 _84443 s _33118 x) (@lem3220924 _84443 s _33118 x)). Qed.
Lemma lem3220926 {_84443 : Type'} (s : _84443 -> Prop) (_33118 : _84443) (x : _84443) : True = ((term43 _84443 x s _33118) = (term108 _84443 s _33118 x)).
Proof. exact (SYM (@lem3220925 _84443 s _33118 x)). Qed.
Lemma lem3220927 {_84443 : Type'} (s : _84443 -> Prop) (_33118 : _84443) (x : _84443) : (term43 _84443 x s _33118) = (term108 _84443 s _33118 x).
Proof. exact (EQ_MP (@lem3220926 _84443 s _33118 x) (@lem0)). Qed.
Lemma lem3220928 {_84443 : Type'} (_33118 : _84443) (s : _84443 -> Prop) (x : _84443) (h1 : term63 _84443 s x) : term108 _84443 s _33118 x.
Proof. exact (EQ_MP (@lem3220927 _84443 s _33118 x) (@lem3220824 _84443 _33118 s x h1)). Qed.
Lemma lem3220930 (b : Prop) (a : Prop) : (a \/ b) = (term112 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3220931 {_84443 : Type'} (x : _84443) (s : _84443 -> Prop) (_33118 : _84443) : (term108 _84443 s _33118 x) = (term113 _84443 x s _33118).
Proof. exact (@lem3220930 (term109 _84443 _33118 x) (s _33118)). Qed.
Lemma lem3220933 (a : Prop) : (term38 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3220934 {_84443 : Type'} (_33118 : _84443) (x : _84443) : (term114 _84443 _33118 x) = (_33118 = x).
Proof. exact (@lem3220933 (_33118 = x)). Qed.
Lemma lem3220935 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3220936 {_84443 : Type'} (_33118 : _84443) (x : _84443) : (term115 _84443 _33118 x) = (term20 _84443 _33118 x).
Proof. exact (MK_COMB (@lem3220935) (@lem3220934 _84443 _33118 x)). Qed.
Lemma lem3220937 {_84443 : Type'} (s : _84443 -> Prop) (_33118 : _84443) : (s _33118) = (s _33118).
Proof. exact (eq_refl (s _33118)). Qed.
Lemma lem3220938 {_84443 : Type'} (x : _84443) (s : _84443 -> Prop) (_33118 : _84443) : (term113 _84443 x s _33118) = (term22 _84443 x s _33118).
Proof. exact (MK_COMB (@lem3220936 _84443 _33118 x) (@lem3220937 _84443 s _33118)). Qed.
Lemma lem3220939 {_84443 : Type'} (x : _84443) (s : _84443 -> Prop) (_33118 : _84443) : (term108 _84443 s _33118 x) = (term22 _84443 x s _33118).
Proof. exact (TRANS (@lem3220931 _84443 x s _33118) (@lem3220938 _84443 x s _33118)). Qed.
Lemma lem3220942 {_84443 : Type'} (_33118 : _84443) (s : _84443 -> Prop) (x : _84443) (h1 : term63 _84443 s x) : term22 _84443 x s _33118.
Proof. exact (EQ_MP (@lem3220939 _84443 x s _33118) (@lem3220928 _84443 _33118 s x h1)). Qed.
Lemma lem3220943 {_84443 : Type'} (_33118 : _84443) (s : _84443 -> Prop) (x : _84443) (h1 : term63 _84443 s x) : term22 _84443 x s _33118.
Proof. exact (@lem3220942 _84443 _33118 s x h1). Qed.
Lemma lem3220944 {_84443 : Type'} (s : _84443 -> Prop) (x : _84443) (h1 : term63 _84443 s x) : term116 _84443 s x.
Proof. exact (@lem3220943 _84443 x s x h1). Qed.
Lemma lem3220947 {_84443 : Type'} (s : _84443 -> Prop) (x : _84443) (h1 : term63 _84443 s x) : s x.
Proof. exact (@lem3220944 _84443 s x h1 (@lem3220895 _84443 x)). Qed.
Lemma lem3220948 {_84443 : Type'} (s : _84443 -> Prop) (x : _84443) (h1 : term63 _84443 s x) : term117 _84443 s x.
Proof. exact (fun h0 : term55 _84443 s x => @lem3220947 _84443 s x h1). Qed.
Lemma lem3220950 (p : Prop) : (term107 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3220951 {_84443 : Type'} (s : _84443 -> Prop) (x : _84443) : (term117 _84443 s x) = (s x).
Proof. exact (@lem3220950 (s x)). Qed.
Lemma lem3220952 {_84443 : Type'} (s : _84443 -> Prop) (x : _84443) (h1 : term63 _84443 s x) : s x.
Proof. exact (EQ_MP (@lem3220951 _84443 s x) (@lem3220948 _84443 s x h1)). Qed.
Lemma lem3220955 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3220957 {_84443 : Type'} (s : _84443 -> Prop) (x : _84443) : (term55 _84443 s x) = (term118 _84443 s x).
Proof. exact (@lem3220955 (s x)). Qed.
Lemma lem3220960 {_84443 : Type'} (s : _84443 -> Prop) (x : _84443) (h1 : term63 _84443 s x) : term118 _84443 s x.
Proof. exact (EQ_MP (@lem3220957 _84443 s x) (@lem3220826 _84443 s x h1)). Qed.
Lemma lem3220963 {_84443 : Type'} (s : _84443 -> Prop) (x : _84443) (h1 : term63 _84443 s x) : False.
Proof. exact (@lem3220960 _84443 s x h1 (@lem3220952 _84443 s x h1)). Qed.
Lemma lem3220964 {_84443 : Type'} (s : _84443 -> Prop) (x : _84443) (h1 : term63 _84443 s x) : term119.
Proof. exact (fun h0 : ~ False => @lem3220963 _84443 s x h1). Qed.
Lemma lem3220966 (p : Prop) : (term107 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3220967 : term119 = False.
Proof. exact (@lem3220966 False). Qed.
Lemma lem3220968 {_84443 : Type'} (s : _84443 -> Prop) (x : _84443) (h1 : term63 _84443 s x) : False.
Proof. exact (EQ_MP (@lem3220967) (@lem3220964 _84443 s x h1)). Qed.
Lemma lem3220970 {_84443 : Type'} (x' : _84443) (s : _84443 -> Prop) (x : _84443) (h1 : term81 _84443 x' s x) : s x.
Proof. exact (proj2 (@lem3220780 _84443 x' s x h1)). Qed.
Lemma lem3220971 {_84443 : Type'} (x' : _84443) (s : _84443 -> Prop) (x : _84443) (h1 : term81 _84443 x' s x) : term117 _84443 s x.
Proof. exact (fun h0 : term55 _84443 s x => @lem3220970 _84443 x' s x h1). Qed.
Lemma lem3220973 (p : Prop) : (term107 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3220974 {_84443 : Type'} (s : _84443 -> Prop) (x : _84443) : (term117 _84443 s x) = (s x).
Proof. exact (@lem3220973 (s x)). Qed.
Lemma lem3220975 {_84443 : Type'} (x' : _84443) (s : _84443 -> Prop) (x : _84443) (h1 : term81 _84443 x' s x) : s x.
Proof. exact (EQ_MP (@lem3220974 _84443 s x) (@lem3220971 _84443 x' s x h1)). Qed.
Lemma lem3220978 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3220980 {_84443 : Type'} (s : _84443 -> Prop) (x : _84443) : (term55 _84443 s x) = (term118 _84443 s x).
Proof. exact (@lem3220978 (s x)). Qed.
Lemma lem3220983 {_84443 : Type'} (x' : _84443) (s : _84443 -> Prop) (x : _84443) (h1 : term81 _84443 x' s x) : term118 _84443 s x.
Proof. exact (EQ_MP (@lem3220980 _84443 s x) (@lem3220873 _84443 x' s x h1)). Qed.
Lemma lem3220986 {_84443 : Type'} (x' : _84443) (s : _84443 -> Prop) (x : _84443) (h1 : term81 _84443 x' s x) : False.
Proof. exact (@lem3220983 _84443 x' s x h1 (@lem3220975 _84443 x' s x h1)). Qed.
Lemma lem3220987 {_84443 : Type'} (x' : _84443) (s : _84443 -> Prop) (x : _84443) (h1 : term81 _84443 x' s x) : term119.
Proof. exact (fun h0 : ~ False => @lem3220986 _84443 x' s x h1). Qed.
Lemma lem3220989 (p : Prop) : (term107 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3220990 : term119 = False.
Proof. exact (@lem3220989 False). Qed.
Lemma lem3220992 {_84443 : Type'} (x' : _84443) (s : _84443 -> Prop) (x : _84443) (h1 : term81 _84443 x' s x) : False.
Proof. exact (EQ_MP (@lem3220990) (@lem3220987 _84443 x' s x h1)). Qed.
Lemma lem3220993 {_84443 : Type'} (x' : _84443) (s : _84443 -> Prop) (x : _84443) (h1 : term96 _84443 x' s x) : False.
Proof. exact (or_elim (@lem3220778 _84443 x' s x h1) (fun h0 : term63 _84443 s x => @lem3220968 _84443 s x h0) (fun h0 : term81 _84443 x' s x => @lem3220992 _84443 x' s x h0)). Qed.
Lemma lem3220994 {_84443 : Type'} (x' : _84443) (s : _84443 -> Prop) (x : _84443) (h1 : term96 _84443 x' s x) : (term96 _84443 x' s x) = False.
Proof. exact (prop_ext (fun h2 : term96 _84443 x' s x => @lem3220993 _84443 x' s x h1) (fun h2 : False => @lem3220778 _84443 x' s x h1)). Qed.
Lemma lem3220995 {_84443 : Type'} (x' : _84443) (s : _84443 -> Prop) (x : _84443) (h1 : term96 _84443 x' s x) : False.
Proof. exact (EQ_MP (@lem3220994 _84443 x' s x h1) (@lem3220778 _84443 x' s x h1)). Qed.
Lemma lem3220996 {_84443 : Type'} (s : _84443 -> Prop) (x : _84443) (h1 : term40 _84443 s x) : False.
Proof. exact (ex_elim (@lem3220730 _84443 s x h1) (fun x' : _84443 => fun h0 : term98 _84443 s x x' => @lem3220995 _84443 x' s x h0)). Qed.
Lemma lem3220997 {_84443 : Type'} (s : _84443 -> Prop) (x : _84443) (h1 : term40 _84443 s x) : (term40 _84443 s x) = False.
Proof. exact (prop_ext (fun h2 : term40 _84443 s x => @lem3220996 _84443 s x h1) (fun h2 : False => @lem3220559 _84443 s x h1)). Qed.
Lemma lem3220998 {_84443 : Type'} (s : _84443 -> Prop) (x : _84443) (h1 : term40 _84443 s x) : False.
Proof. exact (EQ_MP (@lem3220997 _84443 s x h1) (@lem3220559 _84443 s x h1)). Qed.
Lemma lem3220999 {_84443 : Type'} (s : _84443 -> Prop) (x : _84443) : term39 _84443 s x.
Proof. exact (fun h0 : term40 _84443 s x => @lem3220998 _84443 s x h0). Qed.
Lemma lem3221000 {_84443 : Type'} (s : _84443 -> Prop) (x : _84443) : (term25 _84443 x s) = (s x).
Proof. exact (EQ_MP (@lem3220558 _84443 s x) (@lem3220999 _84443 s x)). Qed.
Lemma lem3221005 {_84443 : Type'} (s : _84443 -> Prop) : term28 _84443 s.
Proof. exact (fun x : _84443 => @lem3221000 _84443 s x). Qed.
Lemma lem3221010 {_84443 : Type'} : term30 _84443.
Proof. exact (fun s : _84443 -> Prop => @lem3221005 _84443 s). Qed.
Lemma lem3221011 {_84443 : Type'} : term32 _84443.
Proof. exact (EQ_MP (@lem3220554 _84443) (@lem3221010 _84443)). Qed.
Lemma lem3221013 {_84443 : Type'} : term32 _84443.
Proof. exact (@lem3220487 _84443 (@lem3221011 _84443)). Qed.
Lemma lem3221014 {_84443 : Type'} (h1 : term33 _84443) : False.
Proof. exact (@lem3221013 _84443 (@lem3220471 _84443 h1)). Qed.
Lemma lem3221015 {_84443 : Type'} (h1 : term33 _84443) : (term33 _84443) = False.
Proof. exact (prop_ext (fun h2 : term33 _84443 => @lem3221014 _84443 h1) (fun h2 : False => @lem3220471 _84443 h1)). Qed.
Lemma lem3221016 {_84443 : Type'} (h1 : term33 _84443) : False.
Proof. exact (EQ_MP (@lem3221015 _84443 h1) (@lem3220471 _84443 h1)). Qed.
Lemma lem3221017 {_84443 : Type'} : term32 _84443.
Proof. exact (fun h0 : term33 _84443 => @lem3221016 _84443 h0). Qed.
Lemma lem3221018 {_84443 : Type'} : term30 _84443.
Proof. exact (EQ_MP (@lem3220470 _84443) (@lem3221017 _84443)). Qed.
Lemma lem3221019 {_84443 : Type'} : term12 _84443.
Proof. exact (EQ_MP (@lem3220466 _84443) (@lem3221018 _84443)). Qed.
Lemma lem3221020 {_84443 : Type'} : term11 _84443.
Proof. exact (EQ_MP (@lem3220387 _84443) (@lem3221019 _84443)). Qed.
