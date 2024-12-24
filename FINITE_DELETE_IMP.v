Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_DELETE_IMP_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import FINITE_SUBSET_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm19490_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211683_spec.
Require Import thm3211684_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Lemma lem3608357 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem3608358 {A : Type'} (s : A -> Prop) (h1 : term0 A) : term1 A s.
Proof. exact (@lem3608357 A h1 s). Qed.
Lemma lem3608359 {A : Type'} (s : A -> Prop) : (term1 A s) = (term2 A s).
Proof. exact (eq_refl (term1 A s)). Qed.
Lemma lem3608360 {A : Type'} (s : A -> Prop) (h1 : term0 A) : term2 A s.
Proof. exact (EQ_MP (@lem3608359 A s) (@lem3608358 A s h1)). Qed.
Lemma lem3608361 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term0 A) : term3 A s t.
Proof. exact (@lem3608360 A s h1 t). Qed.
Lemma lem3608362 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term3 A s t) = (term4 A t s).
Proof. exact (eq_refl (term3 A s t)). Qed.
Lemma lem3608363 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term0 A) : term4 A t s.
Proof. exact (EQ_MP (@lem3608362 A t s) (@lem3608361 A s t h1)). Qed.
Lemma lem3608364 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term5 A s t) : term5 A s t.
Proof. exact (h1). Qed.
Lemma lem3608365 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term0 A) (h2 : term5 A s t) : @FINITE A s.
Proof. exact (@lem3608363 A t s h1 (@lem3608364 A s t h2)). Qed.
Lemma lem3608366 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term5 A s t) : term6 A s.
Proof. exact (fun h0 : term0 A => @lem3608365 A s t h0 h1). Qed.
Lemma lem3608367 {A : Type'} (s : A -> Prop) (h1 : term7 A s) : term7 A s.
Proof. exact (h1). Qed.
Lemma lem3608368 {A : Type'} (s : A -> Prop) (h1 : term7 A s) : term6 A s.
Proof. exact (ex_elim (@lem3608367 A s h1) (fun t : A -> Prop => fun h0 : term8 A s t => @lem3608366 A s t h0)). Qed.
Lemma lem3608369 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem3608370 {A : Type'} (s : A -> Prop) (h1 : term0 A) (h2 : term7 A s) : @FINITE A s.
Proof. exact (@lem3608368 A s h2 (@lem3608369 A h1)). Qed.
Lemma lem3608371 {A : Type'} (s : A -> Prop) (h1 : term0 A) : term9 A s.
Proof. exact (fun h0 : term7 A s => @lem3608370 A s h1 h0). Qed.
Lemma lem3608372 {A : Type'} (h1 : term0 A) : term10 A.
Proof. exact (fun s : A -> Prop => @lem3608371 A s h1). Qed.
Lemma lem3608373 {A : Type'} : term11 A.
Proof. exact (fun h0 : term0 A => @lem3608372 A h0). Qed.
Lemma lem3608374 {A : Type'} : term10 A.
Proof. exact (@lem3608373 A (@lem3599924 A)). Qed.
Lemma lem3608375 {A : Type'} (s : A -> Prop) : term12 A s.
Proof. exact (@lem3608374 A s). Qed.
Lemma lem3608376 {A : Type'} (s : A -> Prop) : (term12 A s) = (term9 A s).
Proof. exact (eq_refl (term12 A s)). Qed.
Lemma lem3608378 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem3608380 {A : Type'} (s : A -> Prop) : term9 A s.
Proof. exact (EQ_MP (@lem3608376 A s) (@lem3608375 A s)). Qed.
Lemma lem3608381 {A : Type'} (s : A -> Prop) : term9 A s.
Proof. exact (@lem3608380 A s). Qed.
Lemma lem3608382 {A : Type'} (s : A -> Prop) (x : A) : term13 A s x.
Proof. exact (@lem3608381 A (@DELETE A s x)). Qed.
Lemma lem3608412 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term14 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3608413 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term14 A s t).
Proof. exact (@lem3608412 A s t). Qed.
Lemma lem3608414 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term15 A s x t) = (term16 A s x t).
Proof. exact (@lem3608413 A (@DELETE A s x) t). Qed.
Lemma lem3608421 {A : Type'} (t : A -> Prop) : (term17 A t) = (term17 A t).
Proof. exact (eq_refl (term17 A t)). Qed.
Lemma lem3608422 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term18 A s x t) = (term19 A s x t).
Proof. exact (MK_COMB (@lem3608421 A t) (@lem3608414 A s x t)). Qed.
Lemma lem3608425 {A : Type'} (s : A -> Prop) (x : A) : (term20 A s x) = (term21 A s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3608422 A s x t)). Qed.
Lemma lem3608426 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3608427 {A : Type'} (s : A -> Prop) (x : A) : (term22 A s x) = (term23 A s x).
Proof. exact (MK_COMB (@lem3608426 A) (@lem3608425 A s x)). Qed.
Lemma lem3608432 {A : Type'} (s : A -> Prop) : (term24 A s) = (term24 A s).
Proof. exact (eq_refl (term24 A s)). Qed.
Lemma lem3608433 {A : Type'} (s : A -> Prop) (x : A) : (term25 A s x) = (term26 A s x).
Proof. exact (MK_COMB (@lem3608432 A s) (@lem3608427 A s x)). Qed.
Lemma lem3608436 {A : Type'} (s : A -> Prop) (x : A) : (term26 A s x) = (term25 A s x).
Proof. exact (SYM (@lem3608433 A s x)). Qed.
Lemma lem3608452 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term27 A x s y) = (term28 A s x y).
Proof. exact (EQ_MP (@lem3211684 A s x y) (@lem3211683 A s x y)). Qed.
Lemma lem3608453 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term27 A x s y) = (term28 A s x y).
Proof. exact (@lem3608452 A s x y). Qed.
Lemma lem3608454 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term27 A x' s x) = (term28 A s x' x).
Proof. exact (@lem3608453 A s x' x). Qed.
Lemma lem3608458 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3608459 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3608458 A P x). Qed.
Lemma lem3608460 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3608459 A s x'). Qed.
Lemma lem3608461 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3608462 {A : Type'} (s : A -> Prop) (x' : A) : (term29 A x' s) = (term30 A s x').
Proof. exact (MK_COMB (@lem3608461) (@lem3608460 A s x')). Qed.
Lemma lem3608465 {A : Type'} (x' : A) (x : A) : (term31 A x' x) = (term31 A x' x).
Proof. exact (eq_refl (term31 A x' x)). Qed.
Lemma lem3608466 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term28 A s x' x) = (term32 A s x' x).
Proof. exact (MK_COMB (@lem3608462 A s x') (@lem3608465 A x' x)). Qed.
Lemma lem3608469 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term27 A x' s x) = (term32 A s x' x).
Proof. exact (TRANS (@lem3608454 A s x' x) (@lem3608466 A s x' x)). Qed.
Lemma lem3608470 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3608471 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term33 A x' s x) = (term34 A s x' x).
Proof. exact (MK_COMB (@lem3608470) (@lem3608469 A s x' x)). Qed.
Lemma lem3608473 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3608474 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3608473 A P x). Qed.
Lemma lem3608475 {A : Type'} (t : A -> Prop) (x' : A) : (@IN A x' t) = (t x').
Proof. exact (@lem3608474 A t x'). Qed.
Lemma lem3608476 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term35 A s x x' t) = (term36 A s x t x').
Proof. exact (MK_COMB (@lem3608471 A s x' x) (@lem3608475 A t x')). Qed.
Lemma lem3608479 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term37 A s x t) = (term38 A s x t).
Proof. exact (fun_ext (fun x' : A => @lem3608476 A s x t x')). Qed.
Lemma lem3608480 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3608481 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term16 A s x t) = (term39 A s x t).
Proof. exact (MK_COMB (@lem3608480 A) (@lem3608479 A s x t)). Qed.
Lemma lem3608486 {A : Type'} (t : A -> Prop) : (term17 A t) = (term17 A t).
Proof. exact (eq_refl (term17 A t)). Qed.
Lemma lem3608487 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term19 A s x t) = (term40 A s x t).
Proof. exact (MK_COMB (@lem3608486 A t) (@lem3608481 A s x t)). Qed.
Lemma lem3608490 {A : Type'} (s : A -> Prop) (x : A) : (term21 A s x) = (term41 A s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3608487 A s x t)). Qed.
Lemma lem3608491 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3608492 {A : Type'} (s : A -> Prop) (x : A) : (term23 A s x) = (term42 A s x).
Proof. exact (MK_COMB (@lem3608491 A) (@lem3608490 A s x)). Qed.
Lemma lem3608497 {A : Type'} (s : A -> Prop) : (term24 A s) = (term24 A s).
Proof. exact (eq_refl (term24 A s)). Qed.
Lemma lem3608498 {A : Type'} (s : A -> Prop) (x : A) : (term26 A s x) = (term43 A s x).
Proof. exact (MK_COMB (@lem3608497 A s) (@lem3608492 A s x)). Qed.
Lemma lem3608501 {A : Type'} (s : A -> Prop) (x : A) : (term43 A s x) = (term26 A s x).
Proof. exact (SYM (@lem3608498 A s x)). Qed.
Lemma lem3608503 (p : Prop) : p = (term44 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3608504 {A : Type'} (s : A -> Prop) (x : A) : (term43 A s x) = (term45 A s x).
Proof. exact (@lem3608503 (term43 A s x)). Qed.
Lemma lem3608505 {A : Type'} (s : A -> Prop) (x : A) : (term45 A s x) = (term43 A s x).
Proof. exact (SYM (@lem3608504 A s x)). Qed.
Lemma lem3608506 {A : Type'} (s : A -> Prop) (x : A) (h1 : term46 A s x) : term46 A s x.
Proof. exact (h1). Qed.
Lemma lem3608509 {A : Type'} (s : A -> Prop) (x : A) (h1 : term45 A s x) : term45 A s x.
Proof. exact (h1). Qed.
Lemma lem3608510 {A : Type'} (s : A -> Prop) (x : A) : term47 A s x.
Proof. exact (fun h0 : term45 A s x => @lem3608509 A s x h0). Qed.
Lemma lem3608511 {A : Type'} (s : A -> Prop) (x : A) (h1 : term47 A s x) : term47 A s x.
Proof. exact (h1). Qed.
Lemma lem3608512 {A : Type'} (s : A -> Prop) (x : A) (h1 : term45 A s x) : term45 A s x.
Proof. exact (h1). Qed.
Lemma lem3608513 {A : Type'} (s : A -> Prop) (x : A) (h1 : term45 A s x) (h2 : term47 A s x) : term45 A s x.
Proof. exact (@lem3608511 A s x h2 (@lem3608512 A s x h1)). Qed.
Lemma lem3608514 {A : Type'} (s : A -> Prop) (x : A) (h1 : term45 A s x) : term48 A s x.
Proof. exact (fun h0 : term47 A s x => @lem3608513 A s x h1 h0). Qed.
Lemma lem3608515 {A : Type'} (s : A -> Prop) (x : A) (h1 : term47 A s x) : term47 A s x.
Proof. exact (h1). Qed.
Lemma lem3608516 {A : Type'} (s : A -> Prop) (x : A) (h1 : term45 A s x) (h2 : term47 A s x) : term45 A s x.
Proof. exact (@lem3608514 A s x h1 (@lem3608515 A s x h2)). Qed.
Lemma lem3608517 {A : Type'} (s : A -> Prop) (x : A) (h1 : term47 A s x) : term47 A s x.
Proof. exact (fun h0 : term45 A s x => @lem3608516 A s x h0 h1). Qed.
Lemma lem3608518 {A : Type'} (s : A -> Prop) (x : A) : term49 A s x.
Proof. exact (fun h0 : term47 A s x => @lem3608517 A s x h0). Qed.
Lemma lem3608521 {A : Type'} (s : A -> Prop) (x : A) : term47 A s x.
Proof. exact (@lem3608518 A s x (@lem3608510 A s x)). Qed.
Lemma lem3608522 {A : Type'} (s : A -> Prop) (x : A) : term47 A s x.
Proof. exact (@lem3608521 A s x). Qed.
Lemma lem3608532 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3608533 {A : Type'} (s : A -> Prop) (x : A) : (term45 A s x) = (term50 A s x).
Proof. exact (@lem3608532 (term46 A s x)). Qed.
Lemma lem3608535 (t : Prop) : (term51 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3608536 {A : Type'} (s : A -> Prop) (x : A) : (term50 A s x) = (term43 A s x).
Proof. exact (@lem3608535 (term43 A s x)). Qed.
Lemma lem3608539 {A : Type'} (s : A -> Prop) (x : A) : (term45 A s x) = (term43 A s x).
Proof. exact (TRANS (@lem3608533 A s x) (@lem3608536 A s x)). Qed.
Lemma lem3608578 {A : Type'} (x : A) : (term52 A x) = (term53 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3608539 A s x)). Qed.
Lemma lem3608579 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3608580 {A : Type'} (x : A) : (term54 A x) = (term55 A x).
Proof. exact (MK_COMB (@lem3608579 A) (@lem3608578 A x)). Qed.
Lemma lem3608585 {A : Type'} : (term56 A) = (term57 A).
Proof. exact (fun_ext (fun x : A => @lem3608580 A x)). Qed.
Lemma lem3608586 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3608595 {A : Type'} : (term58 A) = (term59 A).
Proof. exact (MK_COMB (@lem3608586 A) (@lem3608585 A)). Qed.
Lemma lem3608606 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term36 A s x t x') = (term36 A s x t x').
Proof. exact (eq_refl (term36 A s x t x')). Qed.
Lemma lem3608607 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term38 A s x t) = (term38 A s x t).
Proof. exact (fun_ext (fun x' : A => @lem3608606 A s x t x')). Qed.
Lemma lem3608608 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3608609 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term39 A s x t) = (term39 A s x t).
Proof. exact (MK_COMB (@lem3608608 A) (@lem3608607 A s x t)). Qed.
Lemma lem3608612 {A : Type'} (t : A -> Prop) : (term17 A t) = (term17 A t).
Proof. exact (eq_refl (term17 A t)). Qed.
Lemma lem3608613 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term40 A s x t) = (term40 A s x t).
Proof. exact (MK_COMB (@lem3608612 A t) (@lem3608609 A s x t)). Qed.
Lemma lem3608614 {A : Type'} (s : A -> Prop) (x : A) : (term41 A s x) = (term41 A s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3608613 A s x t)). Qed.
Lemma lem3608615 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3608616 {A : Type'} (s : A -> Prop) (x : A) : (term42 A s x) = (term42 A s x).
Proof. exact (MK_COMB (@lem3608615 A) (@lem3608614 A s x)). Qed.
Lemma lem3608619 {A : Type'} (s : A -> Prop) : (term24 A s) = (term24 A s).
Proof. exact (eq_refl (term24 A s)). Qed.
Lemma lem3608620 {A : Type'} (s : A -> Prop) (x : A) : (term43 A s x) = (term43 A s x).
Proof. exact (MK_COMB (@lem3608619 A s) (@lem3608616 A s x)). Qed.
Lemma lem3608621 {A : Type'} (x : A) : (term53 A x) = (term53 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3608620 A s x)). Qed.
Lemma lem3608622 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3608623 {A : Type'} (x : A) : (term55 A x) = (term55 A x).
Proof. exact (MK_COMB (@lem3608622 A) (@lem3608621 A x)). Qed.
Lemma lem3608624 {A : Type'} : (term57 A) = (term57 A).
Proof. exact (fun_ext (fun x : A => @lem3608623 A x)). Qed.
Lemma lem3608625 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3608626 {A : Type'} : (term59 A) = (term59 A).
Proof. exact (MK_COMB (@lem3608625 A) (@lem3608624 A)). Qed.
Lemma lem3608661 {A : Type'} : (term58 A) = (term59 A).
Proof. exact (TRANS (@lem3608595 A) (@lem3608626 A)). Qed.
Lemma lem3608662 {A : Type'} : (term59 A) = (term58 A).
Proof. exact (SYM (@lem3608661 A)). Qed.
Lemma lem3608665 (p : Prop) : p = (term44 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3608666 {A : Type'} (s : A -> Prop) (x : A) : (term42 A s x) = (term60 A s x).
Proof. exact (@lem3608665 (term42 A s x)). Qed.
Lemma lem3608667 {A : Type'} (s : A -> Prop) (x : A) : (term60 A s x) = (term42 A s x).
Proof. exact (SYM (@lem3608666 A s x)). Qed.
Lemma lem3608668 {A : Type'} (s : A -> Prop) (x : A) (h1 : term61 A s x) : term61 A s x.
Proof. exact (h1). Qed.
Lemma lem3608674 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem3608686 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term62 A s x t x') = (term63 A s x t x').
Proof. exact (@lem17362 (term32 A s x' x) (t x')). Qed.
Lemma lem3608687 {A : Type'} (P : A -> Prop) : (term64 A P) = (term65 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3608688 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term66 A s x t) = (term67 A s x t).
Proof. exact (@lem3608687 A (term38 A s x t)). Qed.
Lemma lem3608689 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term68 A s x t x') = (term36 A s x t x').
Proof. exact (eq_refl (term68 A s x t x')). Qed.
Lemma lem3608690 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3608691 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term69 A s x t x') = (term62 A s x t x').
Proof. exact (MK_COMB (@lem3608690) (@lem3608689 A s x t x')). Qed.
Lemma lem3608692 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term69 A s x t x') = (term63 A s x t x').
Proof. exact (TRANS (@lem3608691 A s x t x') (@lem3608686 A s x t x')). Qed.
Lemma lem3608693 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term70 A s x t) = (term71 A s x t).
Proof. exact (fun_ext (fun x' : A => @lem3608692 A s x t x')). Qed.
Lemma lem3608694 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3608695 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term67 A s x t) = (term72 A s x t).
Proof. exact (MK_COMB (@lem3608694 A) (@lem3608693 A s x t)). Qed.
Lemma lem3608696 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term66 A s x t) = (term72 A s x t).
Proof. exact (TRANS (@lem3608688 A s x t) (@lem3608695 A s x t)). Qed.
Lemma lem3608698 {A : Type'} (t : A -> Prop) : (term73 A t) = (term73 A t).
Proof. exact (eq_refl (term73 A t)). Qed.
Lemma lem3608699 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term74 A s x t) = (term75 A s x t).
Proof. exact (MK_COMB (@lem3608698 A t) (@lem3608696 A s x t)). Qed.
Lemma lem3608700 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term76 A s x t) = (term74 A s x t).
Proof. exact (@lem17045 (@FINITE A t) (term39 A s x t)). Qed.
Lemma lem3608701 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term76 A s x t) = (term75 A s x t).
Proof. exact (TRANS (@lem3608700 A s x t) (@lem3608699 A s x t)). Qed.
Lemma lem3608702 {A : Type'} (P : type686 A) : (term77 A P) = (term78 A P).
Proof. exact (@lem18394 (A -> Prop) P). Qed.
Lemma lem3608703 {A : Type'} (s : A -> Prop) (x : A) : (term61 A s x) = (term79 A s x).
Proof. exact (@lem3608702 A (term41 A s x)). Qed.
Lemma lem3608704 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term80 A s x t) = (term40 A s x t).
Proof. exact (eq_refl (term80 A s x t)). Qed.
Lemma lem3608705 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3608706 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term81 A s x t) = (term76 A s x t).
Proof. exact (MK_COMB (@lem3608705) (@lem3608704 A s x t)). Qed.
Lemma lem3608707 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term81 A s x t) = (term75 A s x t).
Proof. exact (TRANS (@lem3608706 A s x t) (@lem3608701 A s x t)). Qed.
Lemma lem3608708 {A : Type'} (s : A -> Prop) (x : A) : (term82 A s x) = (term83 A s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3608707 A s x t)). Qed.
Lemma lem3608709 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3608710 {A : Type'} (s : A -> Prop) (x : A) : (term79 A s x) = (term84 A s x).
Proof. exact (MK_COMB (@lem3608709 A) (@lem3608708 A s x)). Qed.
Lemma lem3608711 {A : Type'} (s : A -> Prop) (x : A) : (term61 A s x) = (term84 A s x).
Proof. exact (TRANS (@lem3608703 A s x) (@lem3608710 A s x)). Qed.
Lemma lem3608810 {A : Type'} (P : Prop) (Q : A -> Prop) : (term85 A P Q) = (term86 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3608811 {A : Type'} (P : Prop) (Q : A -> Prop) : (term85 A P Q) = (term86 A P Q).
Proof. exact (@lem3608810 A P Q). Qed.
Lemma lem3608812 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term87 A s x t) = (term88 A s x t).
Proof. exact (@lem3608811 A (term89 A t) (term71 A s x t)). Qed.
Lemma lem3608813 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term90 A s x t x') = (term63 A s x t x').
Proof. exact (eq_refl (term90 A s x t x')). Qed.
Lemma lem3608814 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term91 A s x t) = (term71 A s x t).
Proof. exact (fun_ext (fun x' : A => @lem3608813 A s x t x')). Qed.
Lemma lem3608815 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3608816 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term92 A s x t) = (term72 A s x t).
Proof. exact (MK_COMB (@lem3608815 A) (@lem3608814 A s x t)). Qed.
Lemma lem3608817 {A : Type'} (t : A -> Prop) : (term73 A t) = (term73 A t).
Proof. exact (eq_refl (term73 A t)). Qed.
Lemma lem3608818 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term87 A s x t) = (term75 A s x t).
Proof. exact (MK_COMB (@lem3608817 A t) (@lem3608816 A s x t)). Qed.
Lemma lem3608819 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3608820 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term93 A s x t) = (term94 A s x t).
Proof. exact (MK_COMB (@lem3608819) (@lem3608818 A s x t)). Qed.
Lemma lem3608821 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term90 A s x t x') = (term63 A s x t x').
Proof. exact (eq_refl (term90 A s x t x')). Qed.
Lemma lem3608822 {A : Type'} (t : A -> Prop) : (term73 A t) = (term73 A t).
Proof. exact (eq_refl (term73 A t)). Qed.
Lemma lem3608823 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term95 A s x t x') = (term96 A s x t x').
Proof. exact (MK_COMB (@lem3608822 A t) (@lem3608821 A s x t x')). Qed.
Lemma lem3608824 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term97 A s x t) = (term98 A s x t).
Proof. exact (fun_ext (fun x' : A => @lem3608823 A s x t x')). Qed.
Lemma lem3608825 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3608826 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term88 A s x t) = (term99 A s x t).
Proof. exact (MK_COMB (@lem3608825 A) (@lem3608824 A s x t)). Qed.
Lemma lem3608827 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : ((term87 A s x t) = (term88 A s x t)) = ((term75 A s x t) = (term99 A s x t)).
Proof. exact (MK_COMB (@lem3608820 A s x t) (@lem3608826 A s x t)). Qed.
Lemma lem3608828 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term75 A s x t) = (term99 A s x t).
Proof. exact (EQ_MP (@lem3608827 A s x t) (@lem3608812 A s x t)). Qed.
Lemma lem3608829 {A : Type'} (s : A -> Prop) (x : A) : (term83 A s x) = (term100 A s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3608828 A s x t)). Qed.
Lemma lem3608830 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3608831 {A : Type'} (s : A -> Prop) (x : A) : (term84 A s x) = (term101 A s x).
Proof. exact (MK_COMB (@lem3608830 A) (@lem3608829 A s x)). Qed.
Lemma lem3608833 {A B : Type'} (P : type1413 A B) : (term102 A B P) = (term103 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3608834 {A : Type'} (P : type672 A) : (term104 A P) = (term105 A P).
Proof. exact (@lem3608833 (A -> Prop) A P). Qed.
Lemma lem3608835 {A : Type'} (s : A -> Prop) (x : A) : (term106 A s x) = (term107 A s x).
Proof. exact (@lem3608834 A (term108 A s x)). Qed.
Lemma lem3608836 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term109 A s x t) = (term98 A s x t).
Proof. exact (eq_refl (term109 A s x t)). Qed.
Lemma lem3608837 {A : Type'} (x' : A) : x' = x'.
Proof. exact (eq_refl x'). Qed.
Lemma lem3608838 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term110 A s x t x') = (term111 A s x t x').
Proof. exact (MK_COMB (@lem3608836 A s x t) (@lem3608837 A x')). Qed.
Lemma lem3608839 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term111 A s x t x') = (term96 A s x t x').
Proof. exact (eq_refl (term111 A s x t x')). Qed.
Lemma lem3608840 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term110 A s x t x') = (term96 A s x t x').
Proof. exact (TRANS (@lem3608838 A s x t x') (@lem3608839 A s x t x')). Qed.
Lemma lem3608841 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term112 A s x t) = (term98 A s x t).
Proof. exact (fun_ext (fun x' : A => @lem3608840 A s x t x')). Qed.
Lemma lem3608842 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3608843 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term113 A s x t) = (term99 A s x t).
Proof. exact (MK_COMB (@lem3608842 A) (@lem3608841 A s x t)). Qed.
Lemma lem3608844 {A : Type'} (s : A -> Prop) (x : A) : (term114 A s x) = (term100 A s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3608843 A s x t)). Qed.
Lemma lem3608845 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3608846 {A : Type'} (s : A -> Prop) (x : A) : (term106 A s x) = (term101 A s x).
Proof. exact (MK_COMB (@lem3608845 A) (@lem3608844 A s x)). Qed.
Lemma lem3608847 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3608848 {A : Type'} (s : A -> Prop) (x : A) : (term115 A s x) = (term116 A s x).
Proof. exact (MK_COMB (@lem3608847) (@lem3608846 A s x)). Qed.
Lemma lem3608849 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term109 A s x t) = (term98 A s x t).
Proof. exact (eq_refl (term109 A s x t)). Qed.
Lemma lem3608850 {A : Type'} (x' : type684 A) (t : A -> Prop) : (x' t) = (x' t).
Proof. exact (eq_refl (x' t)). Qed.
Lemma lem3608851 {A : Type'} (s : A -> Prop) (x : A) (x' : type684 A) (t : A -> Prop) : (term117 A s x x' t) = (term118 A s x x' t).
Proof. exact (MK_COMB (@lem3608849 A s x t) (@lem3608850 A x' t)). Qed.
Lemma lem3608852 {A : Type'} (s : A -> Prop) (x : A) (x' : type684 A) (t : A -> Prop) : (term118 A s x x' t) = (term119 A s x x' t).
Proof. exact (eq_refl (term118 A s x x' t)). Qed.
Lemma lem3608853 {A : Type'} (s : A -> Prop) (x : A) (x' : type684 A) (t : A -> Prop) : (term117 A s x x' t) = (term119 A s x x' t).
Proof. exact (TRANS (@lem3608851 A s x x' t) (@lem3608852 A s x x' t)). Qed.
Lemma lem3608854 {A : Type'} (s : A -> Prop) (x : A) (x' : type684 A) : (term120 A s x x') = (term121 A s x x').
Proof. exact (fun_ext (fun t : A -> Prop => @lem3608853 A s x x' t)). Qed.
Lemma lem3608855 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3608856 {A : Type'} (s : A -> Prop) (x : A) (x' : type684 A) : (term122 A s x x') = (term123 A s x x').
Proof. exact (MK_COMB (@lem3608855 A) (@lem3608854 A s x x')). Qed.
Lemma lem3608857 {A : Type'} (s : A -> Prop) (x : A) : (term124 A s x) = (term125 A s x).
Proof. exact (fun_ext (fun x' : type684 A => @lem3608856 A s x x')). Qed.
Lemma lem3608858 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem3608859 {A : Type'} (s : A -> Prop) (x : A) : (term107 A s x) = (term126 A s x).
Proof. exact (MK_COMB (@lem3608858 A) (@lem3608857 A s x)). Qed.
Lemma lem3608860 {A : Type'} (s : A -> Prop) (x : A) : ((term106 A s x) = (term107 A s x)) = ((term101 A s x) = (term126 A s x)).
Proof. exact (MK_COMB (@lem3608848 A s x) (@lem3608859 A s x)). Qed.
Lemma lem3608861 {A : Type'} (s : A -> Prop) (x : A) : (term101 A s x) = (term126 A s x).
Proof. exact (EQ_MP (@lem3608860 A s x) (@lem3608835 A s x)). Qed.
Lemma lem3608863 {A : Type'} (s : A -> Prop) (x : A) : (term84 A s x) = (term126 A s x).
Proof. exact (TRANS (@lem3608831 A s x) (@lem3608861 A s x)). Qed.
Lemma lem3608864 {A : Type'} (s : A -> Prop) (x : A) : (term61 A s x) = (term126 A s x).
Proof. exact (TRANS (@lem3608711 A s x) (@lem3608863 A s x)). Qed.
Lemma lem3608865 {A : Type'} (s : A -> Prop) (x : A) (h1 : term61 A s x) : term126 A s x.
Proof. exact (EQ_MP (@lem3608864 A s x) (@lem3608668 A s x h1)). Qed.
Lemma lem3608866 {A : Type'} (s : A -> Prop) (x : A) (x' : type684 A) (h1 : term123 A s x x') : term123 A s x x'.
Proof. exact (h1). Qed.
Lemma lem3608871 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3608872 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3608871 (A -> Prop) Prop f x). Qed.
Lemma lem3608874 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@I ((A -> Prop) -> Prop) (@FINITE A) s).
Proof. exact (@lem3608872 A (@FINITE A) s). Qed.
Lemma lem3608876 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3608877 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem3608882 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3608883 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem3608882 (A -> Prop) A f x). Qed.
Lemma lem3608885 {A : Type'} (x' : type684 A) (t : A -> Prop) : (x' t) = (@I ((A -> Prop) -> A) x' t).
Proof. exact (@lem3608883 A x' t). Qed.
Lemma lem3608886 {A : Type'} (x' : type684 A) (t : A -> Prop) : (term127 A x' t) = (term128 A x' t).
Proof. exact (MK_COMB (@lem3608877 A t) (@lem3608885 A x' t)). Qed.
Lemma lem3608888 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3608889 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3608888 A Prop f x). Qed.
Lemma lem3608890 {A : Type'} (x' : type684 A) (t : A -> Prop) : (term128 A x' t) = (term129 A x' t).
Proof. exact (@lem3608889 A t (@I ((A -> Prop) -> A) x' t)). Qed.
Lemma lem3608891 {A : Type'} (x' : type684 A) (t : A -> Prop) : (term127 A x' t) = (term129 A x' t).
Proof. exact (TRANS (@lem3608886 A x' t) (@lem3608890 A x' t)). Qed.
Lemma lem3608892 {A : Type'} (x' : type684 A) (t : A -> Prop) : (term130 A x' t) = (term131 A x' t).
Proof. exact (MK_COMB (@lem3608876) (@lem3608891 A x' t)). Qed.
Lemma lem3608893 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3608894 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem3608899 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3608900 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem3608899 (A -> Prop) A f x). Qed.
Lemma lem3608902 {A : Type'} (x' : type684 A) (t : A -> Prop) : (x' t) = (@I ((A -> Prop) -> A) x' t).
Proof. exact (@lem3608900 A x' t). Qed.
Lemma lem3608903 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3608904 {A : Type'} (x' : type684 A) (t : A -> Prop) : (term132 A x' t) = (term133 A x' t).
Proof. exact (MK_COMB (@lem3608894 A) (@lem3608902 A x' t)). Qed.
Lemma lem3608905 {A : Type'} (x' : type684 A) (t : A -> Prop) (x : A) : ((x' t) = x) = ((@I ((A -> Prop) -> A) x' t) = x).
Proof. exact (MK_COMB (@lem3608904 A x' t) (@lem3608903 A x)). Qed.
Lemma lem3608906 {A : Type'} (x' : type684 A) (t : A -> Prop) (x : A) : (term134 A x' t x) = (term135 A x' t x).
Proof. exact (MK_COMB (@lem3608893) (@lem3608905 A x' t x)). Qed.
Lemma lem3608907 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3608912 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3608913 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem3608912 (A -> Prop) A f x). Qed.
Lemma lem3608915 {A : Type'} (x' : type684 A) (t : A -> Prop) : (x' t) = (@I ((A -> Prop) -> A) x' t).
Proof. exact (@lem3608913 A x' t). Qed.
Lemma lem3608916 {A : Type'} (s : A -> Prop) (x' : type684 A) (t : A -> Prop) : (term136 A s x' t) = (term137 A s x' t).
Proof. exact (MK_COMB (@lem3608907 A s) (@lem3608915 A x' t)). Qed.
Lemma lem3608918 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3608919 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3608918 A Prop f x). Qed.
Lemma lem3608920 {A : Type'} (s : A -> Prop) (x' : type684 A) (t : A -> Prop) : (term137 A s x' t) = (term138 A s x' t).
Proof. exact (@lem3608919 A s (@I ((A -> Prop) -> A) x' t)). Qed.
Lemma lem3608921 {A : Type'} (s : A -> Prop) (x' : type684 A) (t : A -> Prop) : (term136 A s x' t) = (term138 A s x' t).
Proof. exact (TRANS (@lem3608916 A s x' t) (@lem3608920 A s x' t)). Qed.
Lemma lem3608922 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3608923 {A : Type'} (s : A -> Prop) (x' : type684 A) (t : A -> Prop) : (term139 A s x' t) = (term140 A s x' t).
Proof. exact (MK_COMB (@lem3608922) (@lem3608921 A s x' t)). Qed.
Lemma lem3608924 {A : Type'} (s : A -> Prop) (x' : type684 A) (t : A -> Prop) (x : A) : (term141 A s x' t x) = (term142 A s x' t x).
Proof. exact (MK_COMB (@lem3608923 A s x' t) (@lem3608906 A x' t x)). Qed.
Lemma lem3608925 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3608926 {A : Type'} (s : A -> Prop) (x' : type684 A) (t : A -> Prop) (x : A) : (term143 A s x' t x) = (term144 A s x' t x).
Proof. exact (MK_COMB (@lem3608925) (@lem3608924 A s x' t x)). Qed.
Lemma lem3608927 {A : Type'} (s : A -> Prop) (x : A) (x' : type684 A) (t : A -> Prop) : (term145 A s x x' t) = (term146 A s x x' t).
Proof. exact (MK_COMB (@lem3608926 A s x' t x) (@lem3608892 A x' t)). Qed.
Lemma lem3608928 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3608933 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3608934 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3608933 (A -> Prop) Prop f x). Qed.
Lemma lem3608936 {A : Type'} (t : A -> Prop) : (@FINITE A t) = (@I ((A -> Prop) -> Prop) (@FINITE A) t).
Proof. exact (@lem3608934 A (@FINITE A) t). Qed.
Lemma lem3608937 {A : Type'} (t : A -> Prop) : (term89 A t) = (term147 A t).
Proof. exact (MK_COMB (@lem3608928) (@lem3608936 A t)). Qed.
Lemma lem3608938 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3608939 {A : Type'} (t : A -> Prop) : (term73 A t) = (term148 A t).
Proof. exact (MK_COMB (@lem3608938) (@lem3608937 A t)). Qed.
Lemma lem3608940 {A : Type'} (s : A -> Prop) (x : A) (x' : type684 A) (t : A -> Prop) : (term119 A s x x' t) = (term149 A s x x' t).
Proof. exact (MK_COMB (@lem3608939 A t) (@lem3608927 A s x x' t)). Qed.
Lemma lem3608941 {A : Type'} (s : A -> Prop) (x : A) (x' : type684 A) : (term121 A s x x') = (term150 A s x x').
Proof. exact (fun_ext (fun t : A -> Prop => @lem3608940 A s x x' t)). Qed.
Lemma lem3608942 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3608943 {A : Type'} (s : A -> Prop) (x : A) (x' : type684 A) : (term123 A s x x') = (term151 A s x x').
Proof. exact (MK_COMB (@lem3608942 A) (@lem3608941 A s x x')). Qed.
Lemma lem3608944 {A : Type'} (s : A -> Prop) (x : A) (x' : type684 A) (h1 : term123 A s x x') : term151 A s x x'.
Proof. exact (EQ_MP (@lem3608943 A s x x') (@lem3608866 A s x x' h1)). Qed.
Lemma lem3608963 {A : Type'} (s : A -> Prop) (x : A) (x' : type684 A) (t : A -> Prop) : (term149 A s x x' t) = (term152 A s x x' t).
Proof. exact (@lem19490 (term142 A s x' t x) (term147 A t) (term131 A x' t)). Qed.
Lemma lem3608964 {A : Type'} (x' : type684 A) (t : A -> Prop) : (term153 A x' t) = (term153 A x' t).
Proof. exact (eq_refl (term153 A x' t)). Qed.
Lemma lem3608971 {A : Type'} (s : A -> Prop) (x' : type684 A) (t : A -> Prop) (x : A) : (term154 A s x' t x) = (term155 A s x' t x).
Proof. exact (@lem19490 (term138 A s x' t) (term147 A t) (term135 A x' t x)). Qed.
Lemma lem3608972 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3608973 {A : Type'} (s : A -> Prop) (x' : type684 A) (t : A -> Prop) (x : A) : (term156 A s x' t x) = (term157 A s x' t x).
Proof. exact (MK_COMB (@lem3608972) (@lem3608971 A s x' t x)). Qed.
Lemma lem3608974 {A : Type'} (s : A -> Prop) (x : A) (x' : type684 A) (t : A -> Prop) : (term152 A s x x' t) = (term158 A s x x' t).
Proof. exact (MK_COMB (@lem3608973 A s x' t x) (@lem3608964 A x' t)). Qed.
Lemma lem3608976 {A : Type'} (s : A -> Prop) (x : A) (x' : type684 A) (t : A -> Prop) : (term149 A s x x' t) = (term158 A s x x' t).
Proof. exact (TRANS (@lem3608963 A s x x' t) (@lem3608974 A s x x' t)). Qed.
Lemma lem3608977 {A : Type'} (s : A -> Prop) (x : A) (x' : type684 A) : (term150 A s x x') = (term159 A s x x').
Proof. exact (fun_ext (fun t : A -> Prop => @lem3608976 A s x x' t)). Qed.
Lemma lem3608978 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3608980 {A : Type'} (s : A -> Prop) (x : A) (x' : type684 A) : (term151 A s x x') = (term160 A s x x').
Proof. exact (MK_COMB (@lem3608978 A) (@lem3608977 A s x x')). Qed.
Lemma lem3608981 {A : Type'} (s : A -> Prop) (x : A) (x' : type684 A) (h1 : term123 A s x x') : term160 A s x x'.
Proof. exact (EQ_MP (@lem3608980 A s x x') (@lem3608944 A s x x' h1)). Qed.
Lemma lem3608982 {A : Type'} (_39099 : A -> Prop) (s : A -> Prop) (x : A) (x' : type684 A) (h1 : term123 A s x x') : term161 A s x x' _39099.
Proof. exact (@lem3608981 A s x x' h1 _39099). Qed.
Lemma lem3608983 {A : Type'} (s : A -> Prop) (x : A) (x' : type684 A) (_39099 : A -> Prop) : (term161 A s x x' _39099) = (term158 A s x x' _39099).
Proof. exact (eq_refl (term161 A s x x' _39099)). Qed.
Lemma lem3608984 {A : Type'} (_39099 : A -> Prop) (s : A -> Prop) (x : A) (x' : type684 A) (h1 : term123 A s x x') : term158 A s x x' _39099.
Proof. exact (EQ_MP (@lem3608983 A s x x' _39099) (@lem3608982 A _39099 s x x' h1)). Qed.
Lemma lem3608986 {A : Type'} (_39099 : A -> Prop) (s : A -> Prop) (x : A) (x' : type684 A) (h1 : term123 A s x x') : term155 A s x' _39099 x.
Proof. exact (proj1 (@lem3608984 A _39099 s x x' h1)). Qed.
Lemma lem3608996 {A : Type'} (_39099 : A -> Prop) (s : A -> Prop) (x : A) (x' : type684 A) (h1 : term123 A s x x') : term153 A x' _39099.
Proof. exact (proj2 (@lem3608984 A _39099 s x x' h1)). Qed.
Lemma lem3609002 {A : Type'} (_39099 : A -> Prop) (s : A -> Prop) (x : A) (x' : type684 A) (h1 : term123 A s x x') : term162 A s x' _39099.
Proof. exact (proj1 (@lem3608986 A _39099 s x x' h1)). Qed.
Lemma lem3609071 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @I ((A -> Prop) -> Prop) (@FINITE A) s.
Proof. exact (EQ_MP (@lem3608874 A s) (@lem3608674 A s h1)). Qed.
Lemma lem3609072 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : term163 A s.
Proof. exact (fun h0 : term147 A s => @lem3609071 A s h1). Qed.
Lemma lem3609074 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3609075 {A : Type'} (s : A -> Prop) : (term163 A s) = (@I ((A -> Prop) -> Prop) (@FINITE A) s).
Proof. exact (@lem3609074 (@I ((A -> Prop) -> Prop) (@FINITE A) s)). Qed.
Lemma lem3609076 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @I ((A -> Prop) -> Prop) (@FINITE A) s.
Proof. exact (EQ_MP (@lem3609075 A s) (@lem3609072 A s h1)). Qed.
Lemma lem3609078 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @I ((A -> Prop) -> Prop) (@FINITE A) s.
Proof. exact (EQ_MP (@lem3608874 A s) (@lem3608674 A s h1)). Qed.
Lemma lem3609079 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : term163 A s.
Proof. exact (fun h0 : term147 A s => @lem3609078 A s h1). Qed.
Lemma lem3609081 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3609082 {A : Type'} (s : A -> Prop) : (term163 A s) = (@I ((A -> Prop) -> Prop) (@FINITE A) s).
Proof. exact (@lem3609081 (@I ((A -> Prop) -> Prop) (@FINITE A) s)). Qed.
Lemma lem3609083 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @I ((A -> Prop) -> Prop) (@FINITE A) s.
Proof. exact (EQ_MP (@lem3609082 A s) (@lem3609079 A s h1)). Qed.
Lemma lem3609089 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3609090 {A : Type'} (s : A -> Prop) (x' : type684 A) (_39099 : A -> Prop) : (term162 A s x' _39099) = (term165 A s x' _39099).
Proof. exact (@lem3609089 (term138 A s x' _39099) (term147 A _39099)). Qed.
Lemma lem3609096 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3609097 {A : Type'} (s : A -> Prop) (x' : type684 A) (_39099 : A -> Prop) : (term166 A s x' _39099) = (term167 A s x' _39099).
Proof. exact (MK_COMB (@lem3609096) (@lem3609090 A s x' _39099)). Qed.
Lemma lem3609103 {A : Type'} (s : A -> Prop) (x' : type684 A) (_39099 : A -> Prop) : (term165 A s x' _39099) = (term165 A s x' _39099).
Proof. exact (eq_refl (term165 A s x' _39099)). Qed.
Lemma lem3609104 {A : Type'} (s : A -> Prop) (x' : type684 A) (_39099 : A -> Prop) : ((term162 A s x' _39099) = (term165 A s x' _39099)) = ((term165 A s x' _39099) = (term165 A s x' _39099)).
Proof. exact (MK_COMB (@lem3609097 A s x' _39099) (@lem3609103 A s x' _39099)). Qed.
Lemma lem3609106 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3609107 (x : Prop) : (x = x) = True.
Proof. exact (@lem3609106 Prop x). Qed.
Lemma lem3609108 {A : Type'} (s : A -> Prop) (x' : type684 A) (_39099 : A -> Prop) : ((term165 A s x' _39099) = (term165 A s x' _39099)) = True.
Proof. exact (@lem3609107 (term165 A s x' _39099)). Qed.
Lemma lem3609109 {A : Type'} (s : A -> Prop) (x' : type684 A) (_39099 : A -> Prop) : ((term162 A s x' _39099) = (term165 A s x' _39099)) = True.
Proof. exact (TRANS (@lem3609104 A s x' _39099) (@lem3609108 A s x' _39099)). Qed.
Lemma lem3609110 {A : Type'} (s : A -> Prop) (x' : type684 A) (_39099 : A -> Prop) : True = ((term162 A s x' _39099) = (term165 A s x' _39099)).
Proof. exact (SYM (@lem3609109 A s x' _39099)). Qed.
Lemma lem3609111 {A : Type'} (s : A -> Prop) (x' : type684 A) (_39099 : A -> Prop) : (term162 A s x' _39099) = (term165 A s x' _39099).
Proof. exact (EQ_MP (@lem3609110 A s x' _39099) (@lem0)). Qed.
Lemma lem3609112 {A : Type'} (_39099 : A -> Prop) (s : A -> Prop) (x : A) (x' : type684 A) (h1 : term123 A s x x') : term165 A s x' _39099.
Proof. exact (EQ_MP (@lem3609111 A s x' _39099) (@lem3609002 A _39099 s x x' h1)). Qed.
Lemma lem3609114 (b : Prop) (a : Prop) : (a \/ b) = (term168 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3609115 {A : Type'} (s : A -> Prop) (x' : type684 A) (_39099 : A -> Prop) : (term165 A s x' _39099) = (term169 A s x' _39099).
Proof. exact (@lem3609114 (term147 A _39099) (term138 A s x' _39099)). Qed.
Lemma lem3609117 (a : Prop) : (term51 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3609118 {A : Type'} (_39099 : A -> Prop) : (term170 A _39099) = (@I ((A -> Prop) -> Prop) (@FINITE A) _39099).
Proof. exact (@lem3609117 (@I ((A -> Prop) -> Prop) (@FINITE A) _39099)). Qed.
Lemma lem3609119 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3609120 {A : Type'} (_39099 : A -> Prop) : (term171 A _39099) = (term172 A _39099).
Proof. exact (MK_COMB (@lem3609119) (@lem3609118 A _39099)). Qed.
Lemma lem3609121 {A : Type'} (s : A -> Prop) (x' : type684 A) (_39099 : A -> Prop) : (term138 A s x' _39099) = (term138 A s x' _39099).
Proof. exact (eq_refl (term138 A s x' _39099)). Qed.
Lemma lem3609122 {A : Type'} (s : A -> Prop) (x' : type684 A) (_39099 : A -> Prop) : (term169 A s x' _39099) = (term173 A s x' _39099).
Proof. exact (MK_COMB (@lem3609120 A _39099) (@lem3609121 A s x' _39099)). Qed.
Lemma lem3609123 {A : Type'} (s : A -> Prop) (x' : type684 A) (_39099 : A -> Prop) : (term165 A s x' _39099) = (term173 A s x' _39099).
Proof. exact (TRANS (@lem3609115 A s x' _39099) (@lem3609122 A s x' _39099)). Qed.
Lemma lem3609126 {A : Type'} (_39099 : A -> Prop) (s : A -> Prop) (x : A) (x' : type684 A) (h1 : term123 A s x x') : term173 A s x' _39099.
Proof. exact (EQ_MP (@lem3609123 A s x' _39099) (@lem3609112 A _39099 s x x' h1)). Qed.
Lemma lem3609127 {A : Type'} (_39099 : A -> Prop) (s : A -> Prop) (x : A) (x' : type684 A) (h1 : term123 A s x x') : term173 A s x' _39099.
Proof. exact (@lem3609126 A _39099 s x x' h1). Qed.
Lemma lem3609128 {A : Type'} (s : A -> Prop) (x : A) (x' : type684 A) (h1 : term123 A s x x') : term174 A x' s.
Proof. exact (@lem3609127 A s s x x' h1). Qed.
Lemma lem3609131 {A : Type'} (x : A) (x' : type684 A) (s : A -> Prop) (h1 : term123 A s x x') (h2 : @FINITE A s) : term129 A x' s.
Proof. exact (@lem3609128 A s x x' h1 (@lem3609083 A s h2)). Qed.
Lemma lem3609132 {A : Type'} (x : A) (x' : type684 A) (s : A -> Prop) (h1 : term123 A s x x') (h2 : @FINITE A s) : term175 A x' s.
Proof. exact (fun h0 : term131 A x' s => @lem3609131 A x x' s h1 h2). Qed.
Lemma lem3609134 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3609135 {A : Type'} (x' : type684 A) (s : A -> Prop) : (term175 A x' s) = (term129 A x' s).
Proof. exact (@lem3609134 (term129 A x' s)). Qed.
Lemma lem3609136 {A : Type'} (x : A) (x' : type684 A) (s : A -> Prop) (h1 : term123 A s x x') (h2 : @FINITE A s) : term129 A x' s.
Proof. exact (EQ_MP (@lem3609135 A x' s) (@lem3609132 A x x' s h1 h2)). Qed.
Lemma lem3609138 (a : Prop) (b : Prop) : (term176 a b) = (term177 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3609139 {A : Type'} (x' : type684 A) (_39099 : A -> Prop) : (term153 A x' _39099) = (term178 A x' _39099).
Proof. exact (@lem3609138 (@I ((A -> Prop) -> Prop) (@FINITE A) _39099) (term129 A x' _39099)). Qed.
Lemma lem3609141 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3609142 {A : Type'} (x' : type684 A) (_39099 : A -> Prop) : (term178 A x' _39099) = (term179 A x' _39099).
Proof. exact (@lem3609141 (term180 A x' _39099)). Qed.
Lemma lem3609143 {A : Type'} (x' : type684 A) (_39099 : A -> Prop) : (term153 A x' _39099) = (term179 A x' _39099).
Proof. exact (TRANS (@lem3609139 A x' _39099) (@lem3609142 A x' _39099)). Qed.
Lemma lem3609145 {A : Type'} (x : A) (x' : type684 A) (s : A -> Prop) (h1 : term123 A s x x') (h2 : @FINITE A s) : term180 A x' s.
Proof. exact (conj (@lem3609076 A s h2) (@lem3609136 A x x' s h1 h2)). Qed.
Lemma lem3609147 {A : Type'} (_39099 : A -> Prop) (s : A -> Prop) (x : A) (x' : type684 A) (h1 : term123 A s x x') : term179 A x' _39099.
Proof. exact (EQ_MP (@lem3609143 A x' _39099) (@lem3608996 A _39099 s x x' h1)). Qed.
Lemma lem3609148 {A : Type'} (_39099 : A -> Prop) (s : A -> Prop) (x : A) (x' : type684 A) (h1 : term123 A s x x') : term179 A x' _39099.
Proof. exact (@lem3609147 A _39099 s x x' h1). Qed.
Lemma lem3609149 {A : Type'} (s : A -> Prop) (x : A) (x' : type684 A) (h1 : term123 A s x x') : term179 A x' s.
Proof. exact (@lem3609148 A s s x x' h1). Qed.
Lemma lem3609152 {A : Type'} (x : A) (x' : type684 A) (s : A -> Prop) (h1 : term123 A s x x') (h2 : @FINITE A s) : False.
Proof. exact (@lem3609149 A s x x' h1 (@lem3609145 A x x' s h1 h2)). Qed.
Lemma lem3609153 {A : Type'} (x : A) (x' : type684 A) (s : A -> Prop) (h1 : term123 A s x x') (h2 : @FINITE A s) : term181.
Proof. exact (fun h0 : ~ False => @lem3609152 A x x' s h1 h2). Qed.
Lemma lem3609155 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3609156 : term181 = False.
Proof. exact (@lem3609155 False). Qed.
Lemma lem3609157 {A : Type'} (x : A) (x' : type684 A) (s : A -> Prop) (h1 : term123 A s x x') (h2 : @FINITE A s) : False.
Proof. exact (EQ_MP (@lem3609156) (@lem3609153 A x x' s h1 h2)). Qed.
Lemma lem3609158 {A : Type'} (s : A -> Prop) (x : A) (h1 : @FINITE A s) (h2 : term61 A s x) : False.
Proof. exact (ex_elim (@lem3608865 A s x h2) (fun x' : type684 A => fun h0 : term125 A s x x' => @lem3609157 A x x' s h0 h1)). Qed.
Lemma lem3609159 {A : Type'} (s : A -> Prop) (x : A) (h1 : @FINITE A s) (h2 : term61 A s x) : (@FINITE A s) = False.
Proof. exact (prop_ext (fun h3 : @FINITE A s => @lem3609158 A s x h1 h2) (fun h3 : False => @lem3608674 A s h1)). Qed.
Lemma lem3609160 {A : Type'} (s : A -> Prop) (x : A) (h1 : @FINITE A s) (h2 : term61 A s x) : False.
Proof. exact (EQ_MP (@lem3609159 A s x h1 h2) (@lem3608674 A s h1)). Qed.
Lemma lem3609161 {A : Type'} (s : A -> Prop) (x : A) (h1 : @FINITE A s) (h2 : term61 A s x) : (term61 A s x) = False.
Proof. exact (prop_ext (fun h3 : term61 A s x => @lem3609160 A s x h1 h2) (fun h3 : False => @lem3608668 A s x h2)). Qed.
Lemma lem3609162 {A : Type'} (s : A -> Prop) (x : A) (h1 : @FINITE A s) (h2 : term61 A s x) : False.
Proof. exact (EQ_MP (@lem3609161 A s x h1 h2) (@lem3608668 A s x h2)). Qed.
Lemma lem3609163 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : term60 A s x.
Proof. exact (fun h0 : term61 A s x => @lem3609162 A s x h1 h0). Qed.
Lemma lem3609164 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : term42 A s x.
Proof. exact (EQ_MP (@lem3608667 A s x) (@lem3609163 A x s h1)). Qed.
Lemma lem3609165 {A : Type'} (s : A -> Prop) (x : A) : term43 A s x.
Proof. exact (fun h0 : @FINITE A s => @lem3609164 A x s h0). Qed.
Lemma lem3609170 {A : Type'} (x : A) : term55 A x.
Proof. exact (fun s : A -> Prop => @lem3609165 A s x). Qed.
Lemma lem3609175 {A : Type'} : term59 A.
Proof. exact (fun x : A => @lem3609170 A x). Qed.
Lemma lem3609176 {A : Type'} : term58 A.
Proof. exact (EQ_MP (@lem3608662 A) (@lem3609175 A)). Qed.
Lemma lem3609177 {A : Type'} (x : A) : term182 A x.
Proof. exact (@lem3609176 A x). Qed.
Lemma lem3609178 {A : Type'} (x : A) : (term182 A x) = (term54 A x).
Proof. exact (eq_refl (term182 A x)). Qed.
Lemma lem3609179 {A : Type'} (x : A) : term54 A x.
Proof. exact (EQ_MP (@lem3609178 A x) (@lem3609177 A x)). Qed.
Lemma lem3609180 {A : Type'} (x : A) (s : A -> Prop) : term183 A x s.
Proof. exact (@lem3609179 A x s). Qed.
Lemma lem3609181 {A : Type'} (s : A -> Prop) (x : A) : (term183 A x s) = (term45 A s x).
Proof. exact (eq_refl (term183 A x s)). Qed.
Lemma lem3609182 {A : Type'} (s : A -> Prop) (x : A) : term45 A s x.
Proof. exact (EQ_MP (@lem3609181 A s x) (@lem3609180 A x s)). Qed.
Lemma lem3609184 {A : Type'} (s : A -> Prop) (x : A) : term45 A s x.
Proof. exact (@lem3608522 A s x (@lem3609182 A s x)). Qed.
Lemma lem3609185 {A : Type'} (s : A -> Prop) (x : A) (h1 : term46 A s x) : False.
Proof. exact (@lem3609184 A s x (@lem3608506 A s x h1)). Qed.
Lemma lem3609186 {A : Type'} (s : A -> Prop) (x : A) (h1 : term46 A s x) : (term46 A s x) = False.
Proof. exact (prop_ext (fun h2 : term46 A s x => @lem3609185 A s x h1) (fun h2 : False => @lem3608506 A s x h1)). Qed.
Lemma lem3609187 {A : Type'} (s : A -> Prop) (x : A) (h1 : term46 A s x) : False.
Proof. exact (EQ_MP (@lem3609186 A s x h1) (@lem3608506 A s x h1)). Qed.
Lemma lem3609188 {A : Type'} (s : A -> Prop) (x : A) : term45 A s x.
Proof. exact (fun h0 : term46 A s x => @lem3609187 A s x h0). Qed.
Lemma lem3609189 {A : Type'} (s : A -> Prop) (x : A) : term43 A s x.
Proof. exact (EQ_MP (@lem3608505 A s x) (@lem3609188 A s x)). Qed.
Lemma lem3609190 {A : Type'} (s : A -> Prop) (x : A) : term26 A s x.
Proof. exact (EQ_MP (@lem3608501 A s x) (@lem3609189 A s x)). Qed.
Lemma lem3609191 {A : Type'} (s : A -> Prop) (x : A) : term25 A s x.
Proof. exact (EQ_MP (@lem3608436 A s x) (@lem3609190 A s x)). Qed.
Lemma lem3609193 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : term22 A s x.
Proof. exact (@lem3609191 A s x (@lem3608378 A s h1)). Qed.
Lemma lem3609194 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : term184 A s x.
Proof. exact (@lem3608382 A s x (@lem3609193 A x s h1)). Qed.
Lemma lem3609195 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = (term184 A s x).
Proof. exact (prop_ext (fun h2 : @FINITE A s => @lem3609194 A x s h1) (fun h2 : term184 A s x => @lem3608378 A s h1)). Qed.
Lemma lem3609196 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : term184 A s x.
Proof. exact (EQ_MP (@lem3609195 A x s h1) (@lem3608378 A s h1)). Qed.
Lemma lem3609197 {A : Type'} (s : A -> Prop) (x : A) : term185 A s x.
Proof. exact (fun h0 : @FINITE A s => @lem3609196 A x s h0). Qed.
Lemma lem3609202 {A : Type'} (s : A -> Prop) : term186 A s.
Proof. exact (fun x : A => @lem3609197 A s x). Qed.
Lemma lem3609207 {A : Type'} : term187 A.
Proof. exact (fun s : A -> Prop => @lem3609202 A s). Qed.
