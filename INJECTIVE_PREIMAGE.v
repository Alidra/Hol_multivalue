Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INJECTIVE_PREIMAGE_term_abbrevs.
Require Import INJECTIVE_ON_PREIMAGE_spec.
Require Import IN_UNIV_spec.
Require Import SUBSET_UNIV_spec.
Require Import thm0_spec.
Require Import thm1820_spec.
Require Import thm1823_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1856_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211640_spec.
Require Import thm3211641_spec.
Require Import thm3211656_spec.
Require Import thm3211657_spec.
Require Import thm3211724_spec.
Require Import thm3211725_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm7_spec.
Lemma lem5055309 {A : Type'} (s : A -> Prop) : term0 A s.
Proof. exact (@lem3220196 A s). Qed.
Lemma lem5055310 {A : Type'} (s : A -> Prop) : (term0 A s) = (@SUBSET A s (@UNIV A)).
Proof. exact (eq_refl (term0 A s)). Qed.
Lemma lem5055311 {A : Type'} (s : A -> Prop) : @SUBSET A s (@UNIV A).
Proof. exact (EQ_MP (@lem5055310 A s) (@lem5055309 A s)). Qed.
Lemma lem5055312 {A : Type'} (s : A -> Prop) : (@SUBSET A s (@UNIV A)) = ((@SUBSET A s (@UNIV A)) = True).
Proof. exact (@lem7 (@SUBSET A s (@UNIV A))). Qed.
Lemma lem5055314 {A : Type'} (x : A) : term1 A x.
Proof. exact (@lem3204818 A x). Qed.
Lemma lem5055315 {A : Type'} (x : A) : (term1 A x) = (@IN A x (@UNIV A)).
Proof. exact (eq_refl (term1 A x)). Qed.
Lemma lem5055316 {A : Type'} (x : A) : @IN A x (@UNIV A).
Proof. exact (EQ_MP (@lem5055315 A x) (@lem5055314 A x)). Qed.
Lemma lem5055317 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = ((@IN A x (@UNIV A)) = True).
Proof. exact (@lem7 (@IN A x (@UNIV A))). Qed.
Lemma lem5055319 {A B : Type'} : term2 A B.
Proof. exact (@lem5047839 A B). Qed.
Lemma lem5055320 {A B : Type'} (f : A -> B) : term3 A B f.
Proof. exact (@lem5055319 A B f). Qed.
Lemma lem5055321 {A B : Type'} (f : A -> B) : (term3 A B f) = (term4 A B f).
Proof. exact (eq_refl (term3 A B f)). Qed.
Lemma lem5055322 {A B : Type'} (f : A -> B) : term4 A B f.
Proof. exact (EQ_MP (@lem5055321 A B f) (@lem5055320 A B f)). Qed.
Lemma lem5055323 {A B : Type'} (f : A -> B) : term5 A B f.
Proof. exact (@lem5055322 A B f (@UNIV A)). Qed.
Lemma lem5055324 {A B : Type'} (f : A -> B) : (term5 A B f) = (term6 A B f).
Proof. exact (eq_refl (term5 A B f)). Qed.
Lemma lem5055325 {A B : Type'} (f : A -> B) : term6 A B f.
Proof. exact (EQ_MP (@lem5055324 A B f) (@lem5055323 A B f)). Qed.
Lemma lem5055326 {A B : Type'} (f : A -> B) : term7 A B f.
Proof. exact (@lem5055325 A B f (@UNIV B)). Qed.
Lemma lem5055327 {A B : Type'} (f : A -> B) : (term7 A B f) = ((term8 A B f) = (term9 A B f)).
Proof. exact (eq_refl (term7 A B f)). Qed.
Lemma lem5055328 {A B : Type'} (f : A -> B) : (term8 A B f) = (term9 A B f).
Proof. exact (EQ_MP (@lem5055327 A B f) (@lem5055326 A B f)). Qed.
Lemma lem5055348 {A : Type'} (s : A -> Prop) : (@SUBSET A s (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem5055312 A s) (@lem5055311 A s)). Qed.
Lemma lem5055349 {B : Type'} (s : B -> Prop) : (@SUBSET B s (@UNIV B)) = True.
Proof. exact (@lem5055348 B s). Qed.
Lemma lem5055350 {B : Type'} (t : B -> Prop) : (@SUBSET B t (@UNIV B)) = True.
Proof. exact (@lem5055349 B t). Qed.
Lemma lem5055351 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5055352 {B : Type'} (t : B -> Prop) : (term10 B t) = (and True).
Proof. exact (MK_COMB (@lem5055351) (@lem5055350 B t)). Qed.
Lemma lem5055356 {A : Type'} (s : A -> Prop) : (@SUBSET A s (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem5055312 A s) (@lem5055311 A s)). Qed.
Lemma lem5055357 {B : Type'} (s : B -> Prop) : (@SUBSET B s (@UNIV B)) = True.
Proof. exact (@lem5055356 B s). Qed.
Lemma lem5055358 {B : Type'} (t' : B -> Prop) : (@SUBSET B t' (@UNIV B)) = True.
Proof. exact (@lem5055357 B t'). Qed.
Lemma lem5055359 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5055360 {B : Type'} (t' : B -> Prop) : (term10 B t') = (and True).
Proof. exact (MK_COMB (@lem5055359) (@lem5055358 B t')). Qed.
Lemma lem5055370 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem5055317 A x) (@lem5055316 A x)). Qed.
Lemma lem5055371 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (@lem5055370 A x). Qed.
Lemma lem5055372 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5055373 {A : Type'} (x : A) : (term11 A x) = (and True).
Proof. exact (MK_COMB (@lem5055372) (@lem5055371 A x)). Qed.
Lemma lem5055374 {A B : Type'} (f : A -> B) (x : A) (t : B -> Prop) : (term12 A B f x t) = (term12 A B f x t).
Proof. exact (eq_refl (term12 A B f x t)). Qed.
Lemma lem5055375 {A B : Type'} (f : A -> B) (x : A) (t : B -> Prop) : (term13 A B f x t) = (term14 A B f x t).
Proof. exact (MK_COMB (@lem5055373 A x) (@lem5055374 A B f x t)). Qed.
Lemma lem5055377 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5055378 {A B : Type'} (f : A -> B) (x : A) (t : B -> Prop) : (term14 A B f x t) = (term12 A B f x t).
Proof. exact (@lem5055377 (term12 A B f x t)). Qed.
Lemma lem5055379 {A B : Type'} (f : A -> B) (x : A) (t : B -> Prop) : (term13 A B f x t) = (term12 A B f x t).
Proof. exact (TRANS (@lem5055375 A B f x t) (@lem5055378 A B f x t)). Qed.
Lemma lem5055380 {A : Type'} (GEN_PVAR_220 : A) : (@SETSPEC A GEN_PVAR_220) = (@SETSPEC A GEN_PVAR_220).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_220)). Qed.
Lemma lem5055381 {A B : Type'} (GEN_PVAR_220 : A) (f : A -> B) (x : A) (t : B -> Prop) : (term15 A B GEN_PVAR_220 f x t) = (term16 A B GEN_PVAR_220 f x t).
Proof. exact (MK_COMB (@lem5055380 A GEN_PVAR_220) (@lem5055379 A B f x t)). Qed.
Lemma lem5055382 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5055383 {A B : Type'} (GEN_PVAR_220 : A) (f : A -> B) (t : B -> Prop) (x : A) : (term17 A B GEN_PVAR_220 f t x) = (term18 A B GEN_PVAR_220 f t x).
Proof. exact (MK_COMB (@lem5055381 A B GEN_PVAR_220 f x t) (@lem5055382 A x)). Qed.
Lemma lem5055384 {A B : Type'} (GEN_PVAR_220 : A) (f : A -> B) (t : B -> Prop) : (term19 A B GEN_PVAR_220 f t) = (term20 A B GEN_PVAR_220 f t).
Proof. exact (fun_ext (fun x : A => @lem5055383 A B GEN_PVAR_220 f t x)). Qed.
Lemma lem5055385 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5055386 {A B : Type'} (GEN_PVAR_220 : A) (f : A -> B) (t : B -> Prop) : (term21 A B GEN_PVAR_220 f t) = (term22 A B GEN_PVAR_220 f t).
Proof. exact (MK_COMB (@lem5055385 A) (@lem5055384 A B GEN_PVAR_220 f t)). Qed.
Lemma lem5055391 {A B : Type'} (f : A -> B) (t : B -> Prop) : (term23 A B f t) = (term24 A B f t).
Proof. exact (fun_ext (fun GEN_PVAR_220 : A => @lem5055386 A B GEN_PVAR_220 f t)). Qed.
Lemma lem5055392 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem5055393 {A B : Type'} (f : A -> B) (t : B -> Prop) : (term25 A B f t) = (term26 A B f t).
Proof. exact (MK_COMB (@lem5055392 A) (@lem5055391 A B f t)). Qed.
Lemma lem5055394 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem5055395 {A B : Type'} (f : A -> B) (t : B -> Prop) : (term27 A B f t) = (term28 A B f t).
Proof. exact (MK_COMB (@lem5055394 A) (@lem5055393 A B f t)). Qed.
Lemma lem5055403 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem5055317 A x) (@lem5055316 A x)). Qed.
Lemma lem5055404 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (@lem5055403 A x). Qed.
Lemma lem5055405 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5055406 {A : Type'} (x : A) : (term11 A x) = (and True).
Proof. exact (MK_COMB (@lem5055405) (@lem5055404 A x)). Qed.
Lemma lem5055407 {A B : Type'} (f : A -> B) (x : A) (t' : B -> Prop) : (term12 A B f x t') = (term12 A B f x t').
Proof. exact (eq_refl (term12 A B f x t')). Qed.
Lemma lem5055408 {A B : Type'} (f : A -> B) (x : A) (t' : B -> Prop) : (term13 A B f x t') = (term14 A B f x t').
Proof. exact (MK_COMB (@lem5055406 A x) (@lem5055407 A B f x t')). Qed.
Lemma lem5055410 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5055411 {A B : Type'} (f : A -> B) (x : A) (t' : B -> Prop) : (term14 A B f x t') = (term12 A B f x t').
Proof. exact (@lem5055410 (term12 A B f x t')). Qed.
Lemma lem5055412 {A B : Type'} (f : A -> B) (x : A) (t' : B -> Prop) : (term13 A B f x t') = (term12 A B f x t').
Proof. exact (TRANS (@lem5055408 A B f x t') (@lem5055411 A B f x t')). Qed.
Lemma lem5055413 {A : Type'} (GEN_PVAR_221 : A) : (@SETSPEC A GEN_PVAR_221) = (@SETSPEC A GEN_PVAR_221).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_221)). Qed.
Lemma lem5055414 {A B : Type'} (GEN_PVAR_221 : A) (f : A -> B) (x : A) (t' : B -> Prop) : (term15 A B GEN_PVAR_221 f x t') = (term16 A B GEN_PVAR_221 f x t').
Proof. exact (MK_COMB (@lem5055413 A GEN_PVAR_221) (@lem5055412 A B f x t')). Qed.
Lemma lem5055415 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5055416 {A B : Type'} (GEN_PVAR_221 : A) (f : A -> B) (t' : B -> Prop) (x : A) : (term17 A B GEN_PVAR_221 f t' x) = (term18 A B GEN_PVAR_221 f t' x).
Proof. exact (MK_COMB (@lem5055414 A B GEN_PVAR_221 f x t') (@lem5055415 A x)). Qed.
Lemma lem5055417 {A B : Type'} (GEN_PVAR_221 : A) (f : A -> B) (t' : B -> Prop) : (term19 A B GEN_PVAR_221 f t') = (term20 A B GEN_PVAR_221 f t').
Proof. exact (fun_ext (fun x : A => @lem5055416 A B GEN_PVAR_221 f t' x)). Qed.
Lemma lem5055418 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5055419 {A B : Type'} (GEN_PVAR_221 : A) (f : A -> B) (t' : B -> Prop) : (term21 A B GEN_PVAR_221 f t') = (term22 A B GEN_PVAR_221 f t').
Proof. exact (MK_COMB (@lem5055418 A) (@lem5055417 A B GEN_PVAR_221 f t')). Qed.
Lemma lem5055424 {A B : Type'} (f : A -> B) (t' : B -> Prop) : (term23 A B f t') = (term24 A B f t').
Proof. exact (fun_ext (fun GEN_PVAR_221 : A => @lem5055419 A B GEN_PVAR_221 f t')). Qed.
Lemma lem5055425 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem5055426 {A B : Type'} (f : A -> B) (t' : B -> Prop) : (term25 A B f t') = (term26 A B f t').
Proof. exact (MK_COMB (@lem5055425 A) (@lem5055424 A B f t')). Qed.
Lemma lem5055427 {A B : Type'} (t : B -> Prop) (f : A -> B) (t' : B -> Prop) : ((term25 A B f t) = (term25 A B f t')) = ((term26 A B f t) = (term26 A B f t')).
Proof. exact (MK_COMB (@lem5055395 A B f t) (@lem5055426 A B f t')). Qed.
Lemma lem5055430 {A B : Type'} (t : B -> Prop) (f : A -> B) (t' : B -> Prop) : (term29 A B t f t') = (term30 A B t f t').
Proof. exact (MK_COMB (@lem5055360 B t') (@lem5055427 A B t f t')). Qed.
Lemma lem5055432 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5055433 {A B : Type'} (t : B -> Prop) (f : A -> B) (t' : B -> Prop) : (term30 A B t f t') = ((term26 A B f t) = (term26 A B f t')).
Proof. exact (@lem5055432 ((term26 A B f t) = (term26 A B f t'))). Qed.
Lemma lem5055444 {A B : Type'} (t : B -> Prop) (f : A -> B) (t' : B -> Prop) : (term29 A B t f t') = ((term26 A B f t) = (term26 A B f t')).
Proof. exact (TRANS (@lem5055430 A B t f t') (@lem5055433 A B t f t')). Qed.
Lemma lem5055445 {A B : Type'} (t : B -> Prop) (f : A -> B) (t' : B -> Prop) : (term31 A B t f t') = (term30 A B t f t').
Proof. exact (MK_COMB (@lem5055352 B t) (@lem5055444 A B t f t')). Qed.
Lemma lem5055447 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5055448 {A B : Type'} (t : B -> Prop) (f : A -> B) (t' : B -> Prop) : (term30 A B t f t') = ((term26 A B f t) = (term26 A B f t')).
Proof. exact (@lem5055447 ((term26 A B f t) = (term26 A B f t'))). Qed.
Lemma lem5055459 {A B : Type'} (t : B -> Prop) (f : A -> B) (t' : B -> Prop) : (term31 A B t f t') = ((term26 A B f t) = (term26 A B f t')).
Proof. exact (TRANS (@lem5055445 A B t f t') (@lem5055448 A B t f t')). Qed.
Lemma lem5055460 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5055461 {A B : Type'} (t : B -> Prop) (f : A -> B) (t' : B -> Prop) : (term32 A B t f t') = (term33 A B t f t').
Proof. exact (MK_COMB (@lem5055460) (@lem5055459 A B t f t')). Qed.
Lemma lem5055464 {B : Type'} (t : B -> Prop) (t' : B -> Prop) : (t = t') = (t = t').
Proof. exact (eq_refl (t = t')). Qed.
Lemma lem5055465 {A B : Type'} (f : A -> B) (t : B -> Prop) (t' : B -> Prop) : (term34 A B f t t') = (term35 A B f t t').
Proof. exact (MK_COMB (@lem5055461 A B t f t') (@lem5055464 B t t')). Qed.
Lemma lem5055470 {A B : Type'} (f : A -> B) (t : B -> Prop) : (term36 A B f t) = (term37 A B f t).
Proof. exact (fun_ext (fun t' : B -> Prop => @lem5055465 A B f t t')). Qed.
Lemma lem5055471 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5055472 {A B : Type'} (f : A -> B) (t : B -> Prop) : (term38 A B f t) = (term39 A B f t).
Proof. exact (MK_COMB (@lem5055471 B) (@lem5055470 A B f t)). Qed.
Lemma lem5055477 {A B : Type'} (f : A -> B) : (term40 A B f) = (term41 A B f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5055472 A B f t)). Qed.
Lemma lem5055478 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5055479 {A B : Type'} (f : A -> B) : (term8 A B f) = (term42 A B f).
Proof. exact (MK_COMB (@lem5055478 B) (@lem5055477 A B f)). Qed.
Lemma lem5055484 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5055485 {A B : Type'} (f : A -> B) : (term43 A B f) = (term44 A B f).
Proof. exact (MK_COMB (@lem5055484) (@lem5055479 A B f)). Qed.
Lemma lem5055486 {A B : Type'} (f : A -> B) : (term9 A B f) = (term9 A B f).
Proof. exact (eq_refl (term9 A B f)). Qed.
Lemma lem5055487 {A B : Type'} (f : A -> B) : ((term8 A B f) = (term9 A B f)) = ((term42 A B f) = (term9 A B f)).
Proof. exact (MK_COMB (@lem5055485 A B f) (@lem5055486 A B f)). Qed.
Lemma lem5055490 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5055491 {A B : Type'} (f : A -> B) : (term45 A B f) = (term46 A B f).
Proof. exact (MK_COMB (@lem5055490) (@lem5055487 A B f)). Qed.
Lemma lem5055520 {A B : Type'} (f : A -> B) : ((term42 A B f) = ((@IMAGE A B f (@UNIV A)) = (@UNIV B))) = ((term42 A B f) = ((@IMAGE A B f (@UNIV A)) = (@UNIV B))).
Proof. exact (eq_refl ((term42 A B f) = ((@IMAGE A B f (@UNIV A)) = (@UNIV B)))). Qed.
Lemma lem5055521 {A B : Type'} (f : A -> B) : (term47 A B f) = (term48 A B f).
Proof. exact (MK_COMB (@lem5055491 A B f) (@lem5055520 A B f)). Qed.
Lemma lem5055526 {A B : Type'} (f : A -> B) : (term48 A B f) = (term47 A B f).
Proof. exact (SYM (@lem5055521 A B f)). Qed.
Lemma lem5055550 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term49 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem5055551 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term49 A s t).
Proof. exact (@lem5055550 A s t). Qed.
Lemma lem5055552 {A B : Type'} (t : B -> Prop) (f : A -> B) (t' : B -> Prop) : ((term26 A B f t) = (term26 A B f t')) = (term50 A B t f t').
Proof. exact (@lem5055551 A (term26 A B f t) (term26 A B f t')). Qed.
Lemma lem5055569 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5055570 {A B : Type'} (t : B -> Prop) (f : A -> B) (t' : B -> Prop) : (term33 A B t f t') = (term51 A B t f t').
Proof. exact (MK_COMB (@lem5055569) (@lem5055552 A B t f t')). Qed.
Lemma lem5055574 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term49 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem5055575 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (s = t) = (term49 B s t).
Proof. exact (@lem5055574 B s t). Qed.
Lemma lem5055576 {B : Type'} (t : B -> Prop) (t' : B -> Prop) : (t = t') = (term49 B t t').
Proof. exact (@lem5055575 B t t'). Qed.
Lemma lem5055585 {A B : Type'} (f : A -> B) (t : B -> Prop) (t' : B -> Prop) : (term35 A B f t t') = (term52 A B f t t').
Proof. exact (MK_COMB (@lem5055570 A B t f t') (@lem5055576 B t t')). Qed.
Lemma lem5055588 {A B : Type'} (f : A -> B) (t : B -> Prop) : (term37 A B f t) = (term53 A B f t).
Proof. exact (fun_ext (fun t' : B -> Prop => @lem5055585 A B f t t')). Qed.
Lemma lem5055589 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5055590 {A B : Type'} (f : A -> B) (t : B -> Prop) : (term39 A B f t) = (term54 A B f t).
Proof. exact (MK_COMB (@lem5055589 B) (@lem5055588 A B f t)). Qed.
Lemma lem5055595 {A B : Type'} (f : A -> B) : (term41 A B f) = (term55 A B f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5055590 A B f t)). Qed.
Lemma lem5055596 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5055597 {A B : Type'} (f : A -> B) : (term42 A B f) = (term56 A B f).
Proof. exact (MK_COMB (@lem5055596 B) (@lem5055595 A B f)). Qed.
Lemma lem5055602 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5055603 {A B : Type'} (f : A -> B) : (term44 A B f) = (term57 A B f).
Proof. exact (MK_COMB (@lem5055602) (@lem5055597 A B f)). Qed.
Lemma lem5055605 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term58 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem5055606 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (@SUBSET B s t) = (term58 B s t).
Proof. exact (@lem5055605 B s t). Qed.
Lemma lem5055607 {A B : Type'} (f : A -> B) : (term9 A B f) = (term59 A B f).
Proof. exact (@lem5055606 B (@UNIV B) (@IMAGE A B f (@UNIV A))). Qed.
Lemma lem5055614 {A B : Type'} (f : A -> B) : ((term42 A B f) = (term9 A B f)) = ((term56 A B f) = (term59 A B f)).
Proof. exact (MK_COMB (@lem5055603 A B f) (@lem5055607 A B f)). Qed.
Lemma lem5055619 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5055620 {A B : Type'} (f : A -> B) : (term46 A B f) = (term60 A B f).
Proof. exact (MK_COMB (@lem5055619) (@lem5055614 A B f)). Qed.
Lemma lem5055640 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term49 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem5055641 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term49 A s t).
Proof. exact (@lem5055640 A s t). Qed.
Lemma lem5055642 {A B : Type'} (t : B -> Prop) (f : A -> B) (t' : B -> Prop) : ((term26 A B f t) = (term26 A B f t')) = (term50 A B t f t').
Proof. exact (@lem5055641 A (term26 A B f t) (term26 A B f t')). Qed.
Lemma lem5055659 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5055660 {A B : Type'} (t : B -> Prop) (f : A -> B) (t' : B -> Prop) : (term33 A B t f t') = (term51 A B t f t').
Proof. exact (MK_COMB (@lem5055659) (@lem5055642 A B t f t')). Qed.
Lemma lem5055664 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term49 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem5055665 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (s = t) = (term49 B s t).
Proof. exact (@lem5055664 B s t). Qed.
Lemma lem5055666 {B : Type'} (t : B -> Prop) (t' : B -> Prop) : (t = t') = (term49 B t t').
Proof. exact (@lem5055665 B t t'). Qed.
Lemma lem5055675 {A B : Type'} (f : A -> B) (t : B -> Prop) (t' : B -> Prop) : (term35 A B f t t') = (term52 A B f t t').
Proof. exact (MK_COMB (@lem5055660 A B t f t') (@lem5055666 B t t')). Qed.
Lemma lem5055678 {A B : Type'} (f : A -> B) (t : B -> Prop) : (term37 A B f t) = (term53 A B f t).
Proof. exact (fun_ext (fun t' : B -> Prop => @lem5055675 A B f t t')). Qed.
Lemma lem5055679 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5055680 {A B : Type'} (f : A -> B) (t : B -> Prop) : (term39 A B f t) = (term54 A B f t).
Proof. exact (MK_COMB (@lem5055679 B) (@lem5055678 A B f t)). Qed.
Lemma lem5055685 {A B : Type'} (f : A -> B) : (term41 A B f) = (term55 A B f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5055680 A B f t)). Qed.
Lemma lem5055686 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5055687 {A B : Type'} (f : A -> B) : (term42 A B f) = (term56 A B f).
Proof. exact (MK_COMB (@lem5055686 B) (@lem5055685 A B f)). Qed.
Lemma lem5055692 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5055693 {A B : Type'} (f : A -> B) : (term44 A B f) = (term57 A B f).
Proof. exact (MK_COMB (@lem5055692) (@lem5055687 A B f)). Qed.
Lemma lem5055697 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term49 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem5055698 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (s = t) = (term49 B s t).
Proof. exact (@lem5055697 B s t). Qed.
Lemma lem5055699 {A B : Type'} (f : A -> B) : ((@IMAGE A B f (@UNIV A)) = (@UNIV B)) = (term61 A B f).
Proof. exact (@lem5055698 B (@IMAGE A B f (@UNIV A)) (@UNIV B)). Qed.
Lemma lem5055708 {A B : Type'} (f : A -> B) : ((term42 A B f) = ((@IMAGE A B f (@UNIV A)) = (@UNIV B))) = ((term56 A B f) = (term61 A B f)).
Proof. exact (MK_COMB (@lem5055693 A B f) (@lem5055699 A B f)). Qed.
Lemma lem5055713 {A B : Type'} (f : A -> B) : (term48 A B f) = (term62 A B f).
Proof. exact (MK_COMB (@lem5055620 A B f) (@lem5055708 A B f)). Qed.
Lemma lem5055718 {A B : Type'} (f : A -> B) : (term62 A B f) = (term48 A B f).
Proof. exact (SYM (@lem5055713 A B f)). Qed.
Lemma lem5055742 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term63 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem5055743 {A : Type'} (p : A -> Prop) (x : A) : (term63 A x p) = (p x).
Proof. exact (@lem5055742 A p x). Qed.
Lemma lem5055744 {A B : Type'} (f : A -> B) (t : B -> Prop) (x : A) : (term64 A B x f t) = (term65 A B f t x).
Proof. exact (@lem5055743 A (term66 A B f t) x). Qed.
Lemma lem5055745 {A B : Type'} (f : A -> B) (x : A) (t : B -> Prop) : (term65 A B f t x) = (term12 A B f x t).
Proof. exact (eq_refl (term65 A B f t x)). Qed.
Lemma lem5055746 {A : Type'} (GEN_PVAR_220 : A) : (@SETSPEC A GEN_PVAR_220) = (@SETSPEC A GEN_PVAR_220).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_220)). Qed.
Lemma lem5055747 {A B : Type'} (GEN_PVAR_220 : A) (f : A -> B) (x : A) (t : B -> Prop) : (term67 A B GEN_PVAR_220 f t x) = (term16 A B GEN_PVAR_220 f x t).
Proof. exact (MK_COMB (@lem5055746 A GEN_PVAR_220) (@lem5055745 A B f x t)). Qed.
Lemma lem5055748 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5055749 {A B : Type'} (GEN_PVAR_220 : A) (f : A -> B) (t : B -> Prop) (x : A) : (term68 A B GEN_PVAR_220 f t x) = (term18 A B GEN_PVAR_220 f t x).
Proof. exact (MK_COMB (@lem5055747 A B GEN_PVAR_220 f x t) (@lem5055748 A x)). Qed.
Lemma lem5055750 {A B : Type'} (GEN_PVAR_220 : A) (f : A -> B) (t : B -> Prop) : (term69 A B GEN_PVAR_220 f t) = (term20 A B GEN_PVAR_220 f t).
Proof. exact (fun_ext (fun x : A => @lem5055749 A B GEN_PVAR_220 f t x)). Qed.
Lemma lem5055751 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5055752 {A B : Type'} (GEN_PVAR_220 : A) (f : A -> B) (t : B -> Prop) : (term70 A B GEN_PVAR_220 f t) = (term22 A B GEN_PVAR_220 f t).
Proof. exact (MK_COMB (@lem5055751 A) (@lem5055750 A B GEN_PVAR_220 f t)). Qed.
Lemma lem5055753 {A B : Type'} (f : A -> B) (t : B -> Prop) : (term71 A B f t) = (term24 A B f t).
Proof. exact (fun_ext (fun GEN_PVAR_220 : A => @lem5055752 A B GEN_PVAR_220 f t)). Qed.
Lemma lem5055754 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem5055755 {A B : Type'} (f : A -> B) (t : B -> Prop) : (term72 A B f t) = (term26 A B f t).
Proof. exact (MK_COMB (@lem5055754 A) (@lem5055753 A B f t)). Qed.
Lemma lem5055756 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem5055757 {A B : Type'} (x : A) (f : A -> B) (t : B -> Prop) : (term64 A B x f t) = (term73 A B x f t).
Proof. exact (MK_COMB (@lem5055756 A x) (@lem5055755 A B f t)). Qed.
Lemma lem5055758 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5055759 {A B : Type'} (x : A) (f : A -> B) (t : B -> Prop) : (term74 A B x f t) = (term75 A B x f t).
Proof. exact (MK_COMB (@lem5055758) (@lem5055757 A B x f t)). Qed.
Lemma lem5055760 {A B : Type'} (f : A -> B) (x : A) (t : B -> Prop) : (term65 A B f t x) = (term12 A B f x t).
Proof. exact (eq_refl (term65 A B f t x)). Qed.
Lemma lem5055761 {A B : Type'} (f : A -> B) (x : A) (t : B -> Prop) : ((term64 A B x f t) = (term65 A B f t x)) = ((term73 A B x f t) = (term12 A B f x t)).
Proof. exact (MK_COMB (@lem5055759 A B x f t) (@lem5055760 A B f x t)). Qed.
Lemma lem5055762 {A B : Type'} (f : A -> B) (x : A) (t : B -> Prop) : (term73 A B x f t) = (term12 A B f x t).
Proof. exact (EQ_MP (@lem5055761 A B f x t) (@lem5055744 A B f t x)). Qed.
Lemma lem5055764 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5055765 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem5055764 B P x). Qed.
Lemma lem5055766 {A B : Type'} (t : B -> Prop) (f : A -> B) (x : A) : (term12 A B f x t) = (term76 A B t f x).
Proof. exact (@lem5055765 B t (f x)). Qed.
Lemma lem5055767 {A B : Type'} (t : B -> Prop) (f : A -> B) (x : A) : (term73 A B x f t) = (term76 A B t f x).
Proof. exact (TRANS (@lem5055762 A B f x t) (@lem5055766 A B t f x)). Qed.
Lemma lem5055768 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5055769 {A B : Type'} (t : B -> Prop) (f : A -> B) (x : A) : (term75 A B x f t) = (term77 A B t f x).
Proof. exact (MK_COMB (@lem5055768) (@lem5055767 A B t f x)). Qed.
Lemma lem5055771 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term63 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem5055772 {A : Type'} (p : A -> Prop) (x : A) : (term63 A x p) = (p x).
Proof. exact (@lem5055771 A p x). Qed.
Lemma lem5055773 {A B : Type'} (f : A -> B) (t' : B -> Prop) (x : A) : (term64 A B x f t') = (term65 A B f t' x).
Proof. exact (@lem5055772 A (term66 A B f t') x). Qed.
Lemma lem5055774 {A B : Type'} (f : A -> B) (x : A) (t' : B -> Prop) : (term65 A B f t' x) = (term12 A B f x t').
Proof. exact (eq_refl (term65 A B f t' x)). Qed.
Lemma lem5055775 {A : Type'} (GEN_PVAR_221 : A) : (@SETSPEC A GEN_PVAR_221) = (@SETSPEC A GEN_PVAR_221).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_221)). Qed.
Lemma lem5055776 {A B : Type'} (GEN_PVAR_221 : A) (f : A -> B) (x : A) (t' : B -> Prop) : (term67 A B GEN_PVAR_221 f t' x) = (term16 A B GEN_PVAR_221 f x t').
Proof. exact (MK_COMB (@lem5055775 A GEN_PVAR_221) (@lem5055774 A B f x t')). Qed.
Lemma lem5055777 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5055778 {A B : Type'} (GEN_PVAR_221 : A) (f : A -> B) (t' : B -> Prop) (x : A) : (term68 A B GEN_PVAR_221 f t' x) = (term18 A B GEN_PVAR_221 f t' x).
Proof. exact (MK_COMB (@lem5055776 A B GEN_PVAR_221 f x t') (@lem5055777 A x)). Qed.
Lemma lem5055779 {A B : Type'} (GEN_PVAR_221 : A) (f : A -> B) (t' : B -> Prop) : (term69 A B GEN_PVAR_221 f t') = (term20 A B GEN_PVAR_221 f t').
Proof. exact (fun_ext (fun x : A => @lem5055778 A B GEN_PVAR_221 f t' x)). Qed.
Lemma lem5055780 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5055781 {A B : Type'} (GEN_PVAR_221 : A) (f : A -> B) (t' : B -> Prop) : (term70 A B GEN_PVAR_221 f t') = (term22 A B GEN_PVAR_221 f t').
Proof. exact (MK_COMB (@lem5055780 A) (@lem5055779 A B GEN_PVAR_221 f t')). Qed.
Lemma lem5055782 {A B : Type'} (f : A -> B) (t' : B -> Prop) : (term71 A B f t') = (term24 A B f t').
Proof. exact (fun_ext (fun GEN_PVAR_221 : A => @lem5055781 A B GEN_PVAR_221 f t')). Qed.
Lemma lem5055783 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem5055784 {A B : Type'} (f : A -> B) (t' : B -> Prop) : (term72 A B f t') = (term26 A B f t').
Proof. exact (MK_COMB (@lem5055783 A) (@lem5055782 A B f t')). Qed.
Lemma lem5055785 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem5055786 {A B : Type'} (x : A) (f : A -> B) (t' : B -> Prop) : (term64 A B x f t') = (term73 A B x f t').
Proof. exact (MK_COMB (@lem5055785 A x) (@lem5055784 A B f t')). Qed.
Lemma lem5055787 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5055788 {A B : Type'} (x : A) (f : A -> B) (t' : B -> Prop) : (term74 A B x f t') = (term75 A B x f t').
Proof. exact (MK_COMB (@lem5055787) (@lem5055786 A B x f t')). Qed.
Lemma lem5055789 {A B : Type'} (f : A -> B) (x : A) (t' : B -> Prop) : (term65 A B f t' x) = (term12 A B f x t').
Proof. exact (eq_refl (term65 A B f t' x)). Qed.
Lemma lem5055790 {A B : Type'} (f : A -> B) (x : A) (t' : B -> Prop) : ((term64 A B x f t') = (term65 A B f t' x)) = ((term73 A B x f t') = (term12 A B f x t')).
Proof. exact (MK_COMB (@lem5055788 A B x f t') (@lem5055789 A B f x t')). Qed.
Lemma lem5055791 {A B : Type'} (f : A -> B) (x : A) (t' : B -> Prop) : (term73 A B x f t') = (term12 A B f x t').
Proof. exact (EQ_MP (@lem5055790 A B f x t') (@lem5055773 A B f t' x)). Qed.
Lemma lem5055793 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5055794 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem5055793 B P x). Qed.
Lemma lem5055795 {A B : Type'} (t' : B -> Prop) (f : A -> B) (x : A) : (term12 A B f x t') = (term76 A B t' f x).
Proof. exact (@lem5055794 B t' (f x)). Qed.
Lemma lem5055796 {A B : Type'} (t' : B -> Prop) (f : A -> B) (x : A) : (term73 A B x f t') = (term76 A B t' f x).
Proof. exact (TRANS (@lem5055791 A B f x t') (@lem5055795 A B t' f x)). Qed.
Lemma lem5055797 {A B : Type'} (t : B -> Prop) (t' : B -> Prop) (f : A -> B) (x : A) : ((term73 A B x f t) = (term73 A B x f t')) = ((term76 A B t f x) = (term76 A B t' f x)).
Proof. exact (MK_COMB (@lem5055769 A B t f x) (@lem5055796 A B t' f x)). Qed.
Lemma lem5055800 {A B : Type'} (t : B -> Prop) (t' : B -> Prop) (f : A -> B) : (term78 A B t f t') = (term79 A B t t' f).
Proof. exact (fun_ext (fun x : A => @lem5055797 A B t t' f x)). Qed.
Lemma lem5055801 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5055802 {A B : Type'} (t : B -> Prop) (t' : B -> Prop) (f : A -> B) : (term50 A B t f t') = (term80 A B t t' f).
Proof. exact (MK_COMB (@lem5055801 A) (@lem5055800 A B t t' f)). Qed.
Lemma lem5055807 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5055808 {A B : Type'} (t : B -> Prop) (t' : B -> Prop) (f : A -> B) : (term51 A B t f t') = (term81 A B t t' f).
Proof. exact (MK_COMB (@lem5055807) (@lem5055802 A B t t' f)). Qed.
Lemma lem5055816 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5055817 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem5055816 B P x). Qed.
Lemma lem5055818 {B : Type'} (t : B -> Prop) (x : B) : (@IN B x t) = (t x).
Proof. exact (@lem5055817 B t x). Qed.
Lemma lem5055819 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5055820 {B : Type'} (t : B -> Prop) (x : B) : (term82 B x t) = (term83 B t x).
Proof. exact (MK_COMB (@lem5055819) (@lem5055818 B t x)). Qed.
Lemma lem5055822 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5055823 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem5055822 B P x). Qed.
Lemma lem5055824 {B : Type'} (t' : B -> Prop) (x : B) : (@IN B x t') = (t' x).
Proof. exact (@lem5055823 B t' x). Qed.
Lemma lem5055825 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x : B) : ((@IN B x t) = (@IN B x t')) = ((t x) = (t' x)).
Proof. exact (MK_COMB (@lem5055820 B t x) (@lem5055824 B t' x)). Qed.
Lemma lem5055828 {B : Type'} (t : B -> Prop) (t' : B -> Prop) : (term84 B t t') = (term85 B t t').
Proof. exact (fun_ext (fun x : B => @lem5055825 B t t' x)). Qed.
Lemma lem5055829 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5055830 {B : Type'} (t : B -> Prop) (t' : B -> Prop) : (term49 B t t') = (term86 B t t').
Proof. exact (MK_COMB (@lem5055829 B) (@lem5055828 B t t')). Qed.
Lemma lem5055835 {A B : Type'} (f : A -> B) (t : B -> Prop) (t' : B -> Prop) : (term52 A B f t t') = (term87 A B f t t').
Proof. exact (MK_COMB (@lem5055808 A B t t' f) (@lem5055830 B t t')). Qed.
Lemma lem5055838 {A B : Type'} (f : A -> B) (t : B -> Prop) : (term53 A B f t) = (term88 A B f t).
Proof. exact (fun_ext (fun t' : B -> Prop => @lem5055835 A B f t t')). Qed.
Lemma lem5055839 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5055840 {A B : Type'} (f : A -> B) (t : B -> Prop) : (term54 A B f t) = (term89 A B f t).
Proof. exact (MK_COMB (@lem5055839 B) (@lem5055838 A B f t)). Qed.
Lemma lem5055845 {A B : Type'} (f : A -> B) : (term55 A B f) = (term90 A B f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5055840 A B f t)). Qed.
Lemma lem5055846 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5055847 {A B : Type'} (f : A -> B) : (term56 A B f) = (term91 A B f).
Proof. exact (MK_COMB (@lem5055846 B) (@lem5055845 A B f)). Qed.
Lemma lem5055852 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5055853 {A B : Type'} (f : A -> B) : (term57 A B f) = (term92 A B f).
Proof. exact (MK_COMB (@lem5055852) (@lem5055847 A B f)). Qed.
Lemma lem5055861 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3211725 A x) (@lem3211724 A x)). Qed.
Lemma lem5055862 {B : Type'} (x : B) : (@IN B x (@UNIV B)) = True.
Proof. exact (@lem5055861 B x). Qed.
Lemma lem5055863 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5055864 {B : Type'} (x : B) : (term93 B x) = (imp True).
Proof. exact (MK_COMB (@lem5055863) (@lem5055862 B x)). Qed.
Lemma lem5055866 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term94 A B y f s) = (term95 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem5055867 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term94 A B y f s) = (term95 A B y f s).
Proof. exact (@lem5055866 A B y f s). Qed.
Lemma lem5055868 {A B : Type'} (x : B) (f : A -> B) : (term96 A B x f) = (term97 A B x f).
Proof. exact (@lem5055867 A B x f (@UNIV A)). Qed.
Lemma lem5055878 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3211725 A x) (@lem3211724 A x)). Qed.
Lemma lem5055879 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (@lem5055878 A x). Qed.
Lemma lem5055880 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term98 A B x f x') = (term98 A B x f x').
Proof. exact (eq_refl (term98 A B x f x')). Qed.
Lemma lem5055881 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term99 A B x f x') = (term100 A B x f x').
Proof. exact (MK_COMB (@lem5055880 A B x f x') (@lem5055879 A x')). Qed.
Lemma lem5055883 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem5055884 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term100 A B x f x') = (x = (f x')).
Proof. exact (@lem5055883 (x = (f x'))). Qed.
Lemma lem5055887 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term99 A B x f x') = (x = (f x')).
Proof. exact (TRANS (@lem5055881 A B x f x') (@lem5055884 A B x f x')). Qed.
Lemma lem5055888 {A B : Type'} (x : B) (f : A -> B) : (term101 A B x f) = (term102 A B x f).
Proof. exact (fun_ext (fun x' : A => @lem5055887 A B x f x')). Qed.
Lemma lem5055889 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5055890 {A B : Type'} (x : B) (f : A -> B) : (term97 A B x f) = (term103 A B x f).
Proof. exact (MK_COMB (@lem5055889 A) (@lem5055888 A B x f)). Qed.
Lemma lem5055895 {A B : Type'} (x : B) (f : A -> B) : (term96 A B x f) = (term103 A B x f).
Proof. exact (TRANS (@lem5055868 A B x f) (@lem5055890 A B x f)). Qed.
Lemma lem5055896 {A B : Type'} (x : B) (f : A -> B) : (term104 A B x f) = (term105 A B x f).
Proof. exact (MK_COMB (@lem5055864 B x) (@lem5055895 A B x f)). Qed.
Lemma lem5055898 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem5055899 {A B : Type'} (x : B) (f : A -> B) : (term105 A B x f) = (term103 A B x f).
Proof. exact (@lem5055898 (term103 A B x f)). Qed.
Lemma lem5055906 {A B : Type'} (x : B) (f : A -> B) : (term104 A B x f) = (term103 A B x f).
Proof. exact (TRANS (@lem5055896 A B x f) (@lem5055899 A B x f)). Qed.
Lemma lem5055907 {A B : Type'} (f : A -> B) : (term106 A B f) = (term107 A B f).
Proof. exact (fun_ext (fun x : B => @lem5055906 A B x f)). Qed.
Lemma lem5055908 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5055909 {A B : Type'} (f : A -> B) : (term59 A B f) = (term108 A B f).
Proof. exact (MK_COMB (@lem5055908 B) (@lem5055907 A B f)). Qed.
Lemma lem5055914 {A B : Type'} (f : A -> B) : ((term56 A B f) = (term59 A B f)) = ((term91 A B f) = (term108 A B f)).
Proof. exact (MK_COMB (@lem5055853 A B f) (@lem5055909 A B f)). Qed.
Lemma lem5055917 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5055918 {A B : Type'} (f : A -> B) : (term60 A B f) = (term109 A B f).
Proof. exact (MK_COMB (@lem5055917) (@lem5055914 A B f)). Qed.
Lemma lem5055938 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term63 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem5055939 {A : Type'} (p : A -> Prop) (x : A) : (term63 A x p) = (p x).
Proof. exact (@lem5055938 A p x). Qed.
Lemma lem5055940 {A B : Type'} (f : A -> B) (t : B -> Prop) (x : A) : (term64 A B x f t) = (term65 A B f t x).
Proof. exact (@lem5055939 A (term66 A B f t) x). Qed.
Lemma lem5055941 {A B : Type'} (f : A -> B) (x : A) (t : B -> Prop) : (term65 A B f t x) = (term12 A B f x t).
Proof. exact (eq_refl (term65 A B f t x)). Qed.
Lemma lem5055942 {A : Type'} (GEN_PVAR_223 : A) : (@SETSPEC A GEN_PVAR_223) = (@SETSPEC A GEN_PVAR_223).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_223)). Qed.
Lemma lem5055943 {A B : Type'} (GEN_PVAR_223 : A) (f : A -> B) (x : A) (t : B -> Prop) : (term67 A B GEN_PVAR_223 f t x) = (term16 A B GEN_PVAR_223 f x t).
Proof. exact (MK_COMB (@lem5055942 A GEN_PVAR_223) (@lem5055941 A B f x t)). Qed.
Lemma lem5055944 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5055945 {A B : Type'} (GEN_PVAR_223 : A) (f : A -> B) (t : B -> Prop) (x : A) : (term68 A B GEN_PVAR_223 f t x) = (term18 A B GEN_PVAR_223 f t x).
Proof. exact (MK_COMB (@lem5055943 A B GEN_PVAR_223 f x t) (@lem5055944 A x)). Qed.
Lemma lem5055946 {A B : Type'} (GEN_PVAR_223 : A) (f : A -> B) (t : B -> Prop) : (term69 A B GEN_PVAR_223 f t) = (term20 A B GEN_PVAR_223 f t).
Proof. exact (fun_ext (fun x : A => @lem5055945 A B GEN_PVAR_223 f t x)). Qed.
Lemma lem5055947 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5055948 {A B : Type'} (GEN_PVAR_223 : A) (f : A -> B) (t : B -> Prop) : (term70 A B GEN_PVAR_223 f t) = (term22 A B GEN_PVAR_223 f t).
Proof. exact (MK_COMB (@lem5055947 A) (@lem5055946 A B GEN_PVAR_223 f t)). Qed.
Lemma lem5055949 {A B : Type'} (f : A -> B) (t : B -> Prop) : (term71 A B f t) = (term24 A B f t).
Proof. exact (fun_ext (fun GEN_PVAR_223 : A => @lem5055948 A B GEN_PVAR_223 f t)). Qed.
Lemma lem5055950 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem5055951 {A B : Type'} (f : A -> B) (t : B -> Prop) : (term72 A B f t) = (term26 A B f t).
Proof. exact (MK_COMB (@lem5055950 A) (@lem5055949 A B f t)). Qed.
Lemma lem5055952 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem5055953 {A B : Type'} (x : A) (f : A -> B) (t : B -> Prop) : (term64 A B x f t) = (term73 A B x f t).
Proof. exact (MK_COMB (@lem5055952 A x) (@lem5055951 A B f t)). Qed.
Lemma lem5055954 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5055955 {A B : Type'} (x : A) (f : A -> B) (t : B -> Prop) : (term74 A B x f t) = (term75 A B x f t).
Proof. exact (MK_COMB (@lem5055954) (@lem5055953 A B x f t)). Qed.
Lemma lem5055956 {A B : Type'} (f : A -> B) (x : A) (t : B -> Prop) : (term65 A B f t x) = (term12 A B f x t).
Proof. exact (eq_refl (term65 A B f t x)). Qed.
Lemma lem5055957 {A B : Type'} (f : A -> B) (x : A) (t : B -> Prop) : ((term64 A B x f t) = (term65 A B f t x)) = ((term73 A B x f t) = (term12 A B f x t)).
Proof. exact (MK_COMB (@lem5055955 A B x f t) (@lem5055956 A B f x t)). Qed.
Lemma lem5055958 {A B : Type'} (f : A -> B) (x : A) (t : B -> Prop) : (term73 A B x f t) = (term12 A B f x t).
Proof. exact (EQ_MP (@lem5055957 A B f x t) (@lem5055940 A B f t x)). Qed.
Lemma lem5055960 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5055961 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem5055960 B P x). Qed.
Lemma lem5055962 {A B : Type'} (t : B -> Prop) (f : A -> B) (x : A) : (term12 A B f x t) = (term76 A B t f x).
Proof. exact (@lem5055961 B t (f x)). Qed.
Lemma lem5055963 {A B : Type'} (t : B -> Prop) (f : A -> B) (x : A) : (term73 A B x f t) = (term76 A B t f x).
Proof. exact (TRANS (@lem5055958 A B f x t) (@lem5055962 A B t f x)). Qed.
Lemma lem5055964 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5055965 {A B : Type'} (t : B -> Prop) (f : A -> B) (x : A) : (term75 A B x f t) = (term77 A B t f x).
Proof. exact (MK_COMB (@lem5055964) (@lem5055963 A B t f x)). Qed.
Lemma lem5055967 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term63 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem5055968 {A : Type'} (p : A -> Prop) (x : A) : (term63 A x p) = (p x).
Proof. exact (@lem5055967 A p x). Qed.
Lemma lem5055969 {A B : Type'} (f : A -> B) (t' : B -> Prop) (x : A) : (term64 A B x f t') = (term65 A B f t' x).
Proof. exact (@lem5055968 A (term66 A B f t') x). Qed.
Lemma lem5055970 {A B : Type'} (f : A -> B) (x : A) (t' : B -> Prop) : (term65 A B f t' x) = (term12 A B f x t').
Proof. exact (eq_refl (term65 A B f t' x)). Qed.
Lemma lem5055971 {A : Type'} (GEN_PVAR_224 : A) : (@SETSPEC A GEN_PVAR_224) = (@SETSPEC A GEN_PVAR_224).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_224)). Qed.
Lemma lem5055972 {A B : Type'} (GEN_PVAR_224 : A) (f : A -> B) (x : A) (t' : B -> Prop) : (term67 A B GEN_PVAR_224 f t' x) = (term16 A B GEN_PVAR_224 f x t').
Proof. exact (MK_COMB (@lem5055971 A GEN_PVAR_224) (@lem5055970 A B f x t')). Qed.
Lemma lem5055973 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5055974 {A B : Type'} (GEN_PVAR_224 : A) (f : A -> B) (t' : B -> Prop) (x : A) : (term68 A B GEN_PVAR_224 f t' x) = (term18 A B GEN_PVAR_224 f t' x).
Proof. exact (MK_COMB (@lem5055972 A B GEN_PVAR_224 f x t') (@lem5055973 A x)). Qed.
Lemma lem5055975 {A B : Type'} (GEN_PVAR_224 : A) (f : A -> B) (t' : B -> Prop) : (term69 A B GEN_PVAR_224 f t') = (term20 A B GEN_PVAR_224 f t').
Proof. exact (fun_ext (fun x : A => @lem5055974 A B GEN_PVAR_224 f t' x)). Qed.
Lemma lem5055976 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5055977 {A B : Type'} (GEN_PVAR_224 : A) (f : A -> B) (t' : B -> Prop) : (term70 A B GEN_PVAR_224 f t') = (term22 A B GEN_PVAR_224 f t').
Proof. exact (MK_COMB (@lem5055976 A) (@lem5055975 A B GEN_PVAR_224 f t')). Qed.
Lemma lem5055978 {A B : Type'} (f : A -> B) (t' : B -> Prop) : (term71 A B f t') = (term24 A B f t').
Proof. exact (fun_ext (fun GEN_PVAR_224 : A => @lem5055977 A B GEN_PVAR_224 f t')). Qed.
Lemma lem5055979 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem5055980 {A B : Type'} (f : A -> B) (t' : B -> Prop) : (term72 A B f t') = (term26 A B f t').
Proof. exact (MK_COMB (@lem5055979 A) (@lem5055978 A B f t')). Qed.
Lemma lem5055981 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem5055982 {A B : Type'} (x : A) (f : A -> B) (t' : B -> Prop) : (term64 A B x f t') = (term73 A B x f t').
Proof. exact (MK_COMB (@lem5055981 A x) (@lem5055980 A B f t')). Qed.
Lemma lem5055983 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5055984 {A B : Type'} (x : A) (f : A -> B) (t' : B -> Prop) : (term74 A B x f t') = (term75 A B x f t').
Proof. exact (MK_COMB (@lem5055983) (@lem5055982 A B x f t')). Qed.
Lemma lem5055985 {A B : Type'} (f : A -> B) (x : A) (t' : B -> Prop) : (term65 A B f t' x) = (term12 A B f x t').
Proof. exact (eq_refl (term65 A B f t' x)). Qed.
Lemma lem5055986 {A B : Type'} (f : A -> B) (x : A) (t' : B -> Prop) : ((term64 A B x f t') = (term65 A B f t' x)) = ((term73 A B x f t') = (term12 A B f x t')).
Proof. exact (MK_COMB (@lem5055984 A B x f t') (@lem5055985 A B f x t')). Qed.
Lemma lem5055987 {A B : Type'} (f : A -> B) (x : A) (t' : B -> Prop) : (term73 A B x f t') = (term12 A B f x t').
Proof. exact (EQ_MP (@lem5055986 A B f x t') (@lem5055969 A B f t' x)). Qed.
Lemma lem5055989 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5055990 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem5055989 B P x). Qed.
Lemma lem5055991 {A B : Type'} (t' : B -> Prop) (f : A -> B) (x : A) : (term12 A B f x t') = (term76 A B t' f x).
Proof. exact (@lem5055990 B t' (f x)). Qed.
Lemma lem5055992 {A B : Type'} (t' : B -> Prop) (f : A -> B) (x : A) : (term73 A B x f t') = (term76 A B t' f x).
Proof. exact (TRANS (@lem5055987 A B f x t') (@lem5055991 A B t' f x)). Qed.
Lemma lem5055993 {A B : Type'} (t : B -> Prop) (t' : B -> Prop) (f : A -> B) (x : A) : ((term73 A B x f t) = (term73 A B x f t')) = ((term76 A B t f x) = (term76 A B t' f x)).
Proof. exact (MK_COMB (@lem5055965 A B t f x) (@lem5055992 A B t' f x)). Qed.
Lemma lem5055996 {A B : Type'} (t : B -> Prop) (t' : B -> Prop) (f : A -> B) : (term78 A B t f t') = (term79 A B t t' f).
Proof. exact (fun_ext (fun x : A => @lem5055993 A B t t' f x)). Qed.
Lemma lem5055997 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5055998 {A B : Type'} (t : B -> Prop) (t' : B -> Prop) (f : A -> B) : (term50 A B t f t') = (term80 A B t t' f).
Proof. exact (MK_COMB (@lem5055997 A) (@lem5055996 A B t t' f)). Qed.
Lemma lem5056003 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5056004 {A B : Type'} (t : B -> Prop) (t' : B -> Prop) (f : A -> B) : (term51 A B t f t') = (term81 A B t t' f).
Proof. exact (MK_COMB (@lem5056003) (@lem5055998 A B t t' f)). Qed.
Lemma lem5056012 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5056013 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem5056012 B P x). Qed.
Lemma lem5056014 {B : Type'} (t : B -> Prop) (x : B) : (@IN B x t) = (t x).
Proof. exact (@lem5056013 B t x). Qed.
Lemma lem5056015 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5056016 {B : Type'} (t : B -> Prop) (x : B) : (term82 B x t) = (term83 B t x).
Proof. exact (MK_COMB (@lem5056015) (@lem5056014 B t x)). Qed.
Lemma lem5056018 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5056019 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem5056018 B P x). Qed.
Lemma lem5056020 {B : Type'} (t' : B -> Prop) (x : B) : (@IN B x t') = (t' x).
Proof. exact (@lem5056019 B t' x). Qed.
Lemma lem5056021 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x : B) : ((@IN B x t) = (@IN B x t')) = ((t x) = (t' x)).
Proof. exact (MK_COMB (@lem5056016 B t x) (@lem5056020 B t' x)). Qed.
Lemma lem5056024 {B : Type'} (t : B -> Prop) (t' : B -> Prop) : (term84 B t t') = (term85 B t t').
Proof. exact (fun_ext (fun x : B => @lem5056021 B t t' x)). Qed.
Lemma lem5056025 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5056026 {B : Type'} (t : B -> Prop) (t' : B -> Prop) : (term49 B t t') = (term86 B t t').
Proof. exact (MK_COMB (@lem5056025 B) (@lem5056024 B t t')). Qed.
Lemma lem5056031 {A B : Type'} (f : A -> B) (t : B -> Prop) (t' : B -> Prop) : (term52 A B f t t') = (term87 A B f t t').
Proof. exact (MK_COMB (@lem5056004 A B t t' f) (@lem5056026 B t t')). Qed.
Lemma lem5056034 {A B : Type'} (f : A -> B) (t : B -> Prop) : (term53 A B f t) = (term88 A B f t).
Proof. exact (fun_ext (fun t' : B -> Prop => @lem5056031 A B f t t')). Qed.
Lemma lem5056035 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5056036 {A B : Type'} (f : A -> B) (t : B -> Prop) : (term54 A B f t) = (term89 A B f t).
Proof. exact (MK_COMB (@lem5056035 B) (@lem5056034 A B f t)). Qed.
Lemma lem5056041 {A B : Type'} (f : A -> B) : (term55 A B f) = (term90 A B f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5056036 A B f t)). Qed.
Lemma lem5056042 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5056043 {A B : Type'} (f : A -> B) : (term56 A B f) = (term91 A B f).
Proof. exact (MK_COMB (@lem5056042 B) (@lem5056041 A B f)). Qed.
Lemma lem5056048 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5056049 {A B : Type'} (f : A -> B) : (term57 A B f) = (term92 A B f).
Proof. exact (MK_COMB (@lem5056048) (@lem5056043 A B f)). Qed.
Lemma lem5056057 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term94 A B y f s) = (term95 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem5056058 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term94 A B y f s) = (term95 A B y f s).
Proof. exact (@lem5056057 A B y f s). Qed.
Lemma lem5056059 {A B : Type'} (x : B) (f : A -> B) : (term96 A B x f) = (term97 A B x f).
Proof. exact (@lem5056058 A B x f (@UNIV A)). Qed.
Lemma lem5056069 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3211725 A x) (@lem3211724 A x)). Qed.
Lemma lem5056070 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (@lem5056069 A x). Qed.
Lemma lem5056071 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term98 A B x f x') = (term98 A B x f x').
Proof. exact (eq_refl (term98 A B x f x')). Qed.
Lemma lem5056072 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term99 A B x f x') = (term100 A B x f x').
Proof. exact (MK_COMB (@lem5056071 A B x f x') (@lem5056070 A x')). Qed.
Lemma lem5056074 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem5056075 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term100 A B x f x') = (x = (f x')).
Proof. exact (@lem5056074 (x = (f x'))). Qed.
Lemma lem5056078 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term99 A B x f x') = (x = (f x')).
Proof. exact (TRANS (@lem5056072 A B x f x') (@lem5056075 A B x f x')). Qed.
Lemma lem5056079 {A B : Type'} (x : B) (f : A -> B) : (term101 A B x f) = (term102 A B x f).
Proof. exact (fun_ext (fun x' : A => @lem5056078 A B x f x')). Qed.
Lemma lem5056080 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5056081 {A B : Type'} (x : B) (f : A -> B) : (term97 A B x f) = (term103 A B x f).
Proof. exact (MK_COMB (@lem5056080 A) (@lem5056079 A B x f)). Qed.
Lemma lem5056086 {A B : Type'} (x : B) (f : A -> B) : (term96 A B x f) = (term103 A B x f).
Proof. exact (TRANS (@lem5056059 A B x f) (@lem5056081 A B x f)). Qed.
Lemma lem5056087 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5056088 {A B : Type'} (x : B) (f : A -> B) : (term110 A B x f) = (term111 A B x f).
Proof. exact (MK_COMB (@lem5056087) (@lem5056086 A B x f)). Qed.
Lemma lem5056090 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3211725 A x) (@lem3211724 A x)). Qed.
Lemma lem5056091 {B : Type'} (x : B) : (@IN B x (@UNIV B)) = True.
Proof. exact (@lem5056090 B x). Qed.
Lemma lem5056092 {A B : Type'} (x : B) (f : A -> B) : ((term96 A B x f) = (@IN B x (@UNIV B))) = ((term103 A B x f) = True).
Proof. exact (MK_COMB (@lem5056088 A B x f) (@lem5056091 B x)). Qed.
Lemma lem5056094 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem5056095 {A B : Type'} (x : B) (f : A -> B) : ((term103 A B x f) = True) = (term103 A B x f).
Proof. exact (@lem5056094 (term103 A B x f)). Qed.
Lemma lem5056102 {A B : Type'} (x : B) (f : A -> B) : ((term96 A B x f) = (@IN B x (@UNIV B))) = (term103 A B x f).
Proof. exact (TRANS (@lem5056092 A B x f) (@lem5056095 A B x f)). Qed.
Lemma lem5056103 {A B : Type'} (f : A -> B) : (term112 A B f) = (term107 A B f).
Proof. exact (fun_ext (fun x : B => @lem5056102 A B x f)). Qed.
Lemma lem5056104 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5056105 {A B : Type'} (f : A -> B) : (term61 A B f) = (term108 A B f).
Proof. exact (MK_COMB (@lem5056104 B) (@lem5056103 A B f)). Qed.
Lemma lem5056110 {A B : Type'} (f : A -> B) : ((term56 A B f) = (term61 A B f)) = ((term91 A B f) = (term108 A B f)).
Proof. exact (MK_COMB (@lem5056049 A B f) (@lem5056105 A B f)). Qed.
Lemma lem5056113 {A B : Type'} (f : A -> B) : (term62 A B f) = (term113 A B f).
Proof. exact (MK_COMB (@lem5055918 A B f) (@lem5056110 A B f)). Qed.
Lemma lem5056117 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem5056118 {A B : Type'} (f : A -> B) : (term113 A B f) = True.
Proof. exact (@lem5056117 ((term91 A B f) = (term108 A B f))). Qed.
Lemma lem5056119 {A B : Type'} (f : A -> B) : (term62 A B f) = True.
Proof. exact (TRANS (@lem5056113 A B f) (@lem5056118 A B f)). Qed.
Lemma lem5056120 {A B : Type'} (f : A -> B) : True = (term62 A B f).
Proof. exact (SYM (@lem5056119 A B f)). Qed.
Lemma lem5056121 {A B : Type'} (f : A -> B) : term62 A B f.
Proof. exact (EQ_MP (@lem5056120 A B f) (@lem0)). Qed.
Lemma lem5056122 {A B : Type'} (f : A -> B) : term48 A B f.
Proof. exact (EQ_MP (@lem5055718 A B f) (@lem5056121 A B f)). Qed.
Lemma lem5056123 {A B : Type'} (f : A -> B) : term47 A B f.
Proof. exact (EQ_MP (@lem5055526 A B f) (@lem5056122 A B f)). Qed.
Lemma lem5056124 {A B : Type'} (f : A -> B) : (term42 A B f) = ((@IMAGE A B f (@UNIV A)) = (@UNIV B)).
Proof. exact (@lem5056123 A B f (@lem5055328 A B f)). Qed.
Lemma lem5056129 {A B : Type'} : term114 A B.
Proof. exact (fun f : A -> B => @lem5056124 A B f). Qed.
