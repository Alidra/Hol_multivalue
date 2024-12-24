Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import IN_GSPEC_term_abbrevs.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211640_spec.
Require Import thm3211641_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3400403 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3400404 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (@lem3400403 A s t). Qed.
Lemma lem3400405 {A : Type'} (s : A -> Prop) : ((term1 A s) = s) = (term2 A s).
Proof. exact (@lem3400404 A (term1 A s) s). Qed.
Lemma lem3400418 {A : Type'} : (term3 A) = (term4 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3400405 A s)). Qed.
Lemma lem3400419 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3400420 {A : Type'} : (term5 A) = (term6 A).
Proof. exact (MK_COMB (@lem3400419 A) (@lem3400418 A)). Qed.
Lemma lem3400425 {A : Type'} : (term6 A) = (term5 A).
Proof. exact (SYM (@lem3400420 A)). Qed.
Lemma lem3400437 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term7 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem3400438 {A : Type'} (p : A -> Prop) (x : A) : (term7 A x p) = (p x).
Proof. exact (@lem3400437 A p x). Qed.
Lemma lem3400439 {A : Type'} (s : A -> Prop) (x : A) : (term8 A x s) = (term9 A s x).
Proof. exact (@lem3400438 A (term10 A s) x). Qed.
Lemma lem3400440 {A : Type'} (x : A) (s : A -> Prop) : (term9 A s x) = (@IN A x s).
Proof. exact (eq_refl (term9 A s x)). Qed.
Lemma lem3400441 {A : Type'} (GEN_PVAR_30 : A) : (@SETSPEC A GEN_PVAR_30) = (@SETSPEC A GEN_PVAR_30).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_30)). Qed.
Lemma lem3400442 {A : Type'} (GEN_PVAR_30 : A) (x : A) (s : A -> Prop) : (term11 A GEN_PVAR_30 s x) = (term12 A GEN_PVAR_30 x s).
Proof. exact (MK_COMB (@lem3400441 A GEN_PVAR_30) (@lem3400440 A x s)). Qed.
Lemma lem3400443 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3400444 {A : Type'} (GEN_PVAR_30 : A) (s : A -> Prop) (x : A) : (term13 A GEN_PVAR_30 s x) = (term14 A GEN_PVAR_30 s x).
Proof. exact (MK_COMB (@lem3400442 A GEN_PVAR_30 x s) (@lem3400443 A x)). Qed.
Lemma lem3400445 {A : Type'} (GEN_PVAR_30 : A) (s : A -> Prop) : (term15 A GEN_PVAR_30 s) = (term16 A GEN_PVAR_30 s).
Proof. exact (fun_ext (fun x : A => @lem3400444 A GEN_PVAR_30 s x)). Qed.
Lemma lem3400446 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3400447 {A : Type'} (GEN_PVAR_30 : A) (s : A -> Prop) : (term17 A GEN_PVAR_30 s) = (term18 A GEN_PVAR_30 s).
Proof. exact (MK_COMB (@lem3400446 A) (@lem3400445 A GEN_PVAR_30 s)). Qed.
Lemma lem3400448 {A : Type'} (s : A -> Prop) : (term19 A s) = (term20 A s).
Proof. exact (fun_ext (fun GEN_PVAR_30 : A => @lem3400447 A GEN_PVAR_30 s)). Qed.
Lemma lem3400449 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem3400450 {A : Type'} (s : A -> Prop) : (term21 A s) = (term1 A s).
Proof. exact (MK_COMB (@lem3400449 A) (@lem3400448 A s)). Qed.
Lemma lem3400451 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem3400452 {A : Type'} (x : A) (s : A -> Prop) : (term8 A x s) = (term22 A x s).
Proof. exact (MK_COMB (@lem3400451 A x) (@lem3400450 A s)). Qed.
Lemma lem3400453 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3400454 {A : Type'} (x : A) (s : A -> Prop) : (term23 A x s) = (term24 A x s).
Proof. exact (MK_COMB (@lem3400453) (@lem3400452 A x s)). Qed.
Lemma lem3400455 {A : Type'} (x : A) (s : A -> Prop) : (term9 A s x) = (@IN A x s).
Proof. exact (eq_refl (term9 A s x)). Qed.
Lemma lem3400456 {A : Type'} (x : A) (s : A -> Prop) : ((term8 A x s) = (term9 A s x)) = ((term22 A x s) = (@IN A x s)).
Proof. exact (MK_COMB (@lem3400454 A x s) (@lem3400455 A x s)). Qed.
Lemma lem3400457 {A : Type'} (x : A) (s : A -> Prop) : (term22 A x s) = (@IN A x s).
Proof. exact (EQ_MP (@lem3400456 A x s) (@lem3400439 A s x)). Qed.
Lemma lem3400459 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3400460 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3400459 A P x). Qed.
Lemma lem3400461 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3400460 A s x). Qed.
Lemma lem3400462 {A : Type'} (s : A -> Prop) (x : A) : (term22 A x s) = (s x).
Proof. exact (TRANS (@lem3400457 A x s) (@lem3400461 A s x)). Qed.
Lemma lem3400463 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3400464 {A : Type'} (s : A -> Prop) (x : A) : (term24 A x s) = (term25 A s x).
Proof. exact (MK_COMB (@lem3400463) (@lem3400462 A s x)). Qed.
Lemma lem3400466 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3400467 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3400466 A P x). Qed.
Lemma lem3400468 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3400467 A s x). Qed.
Lemma lem3400469 {A : Type'} (s : A -> Prop) (x : A) : ((term22 A x s) = (@IN A x s)) = ((s x) = (s x)).
Proof. exact (MK_COMB (@lem3400464 A s x) (@lem3400468 A s x)). Qed.
Lemma lem3400471 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3400472 (x : Prop) : (x = x) = True.
Proof. exact (@lem3400471 Prop x). Qed.
Lemma lem3400473 {A : Type'} (s : A -> Prop) (x : A) : ((s x) = (s x)) = True.
Proof. exact (@lem3400472 (s x)). Qed.
Lemma lem3400474 {A : Type'} (x : A) (s : A -> Prop) : ((term22 A x s) = (@IN A x s)) = True.
Proof. exact (TRANS (@lem3400469 A s x) (@lem3400473 A s x)). Qed.
Lemma lem3400475 {A : Type'} (s : A -> Prop) : (term26 A s) = (term27 A).
Proof. exact (fun_ext (fun x : A => @lem3400474 A x s)). Qed.
Lemma lem3400476 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3400477 {A : Type'} (s : A -> Prop) : (term2 A s) = (term28 A).
Proof. exact (MK_COMB (@lem3400476 A) (@lem3400475 A s)). Qed.
Lemma lem3400479 {A : Type'} (t : Prop) : (term29 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3400480 {A : Type'} (t : Prop) : (term29 A t) = t.
Proof. exact (@lem3400479 A t). Qed.
Lemma lem3400481 {A : Type'} : (term28 A) = True.
Proof. exact (@lem3400480 A True). Qed.
Lemma lem3400482 {A : Type'} (s : A -> Prop) : (term2 A s) = True.
Proof. exact (TRANS (@lem3400477 A s) (@lem3400481 A)). Qed.
Lemma lem3400483 {A : Type'} : (term4 A) = (term30 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3400482 A s)). Qed.
Lemma lem3400484 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3400485 {A : Type'} : (term6 A) = (term31 A).
Proof. exact (MK_COMB (@lem3400484 A) (@lem3400483 A)). Qed.
Lemma lem3400487 {A : Type'} (t : Prop) : (term29 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3400488 {A : Type'} (t : Prop) : (term32 A t) = t.
Proof. exact (@lem3400487 (A -> Prop) t). Qed.
Lemma lem3400489 {A : Type'} : (term31 A) = True.
Proof. exact (@lem3400488 A True). Qed.
Lemma lem3400490 {A : Type'} : (term6 A) = True.
Proof. exact (TRANS (@lem3400485 A) (@lem3400489 A)). Qed.
Lemma lem3400491 {A : Type'} : True = (term6 A).
Proof. exact (SYM (@lem3400490 A)). Qed.
Lemma lem3400492 {A : Type'} : term6 A.
Proof. exact (EQ_MP (@lem3400491 A) (@lem0)). Qed.
Lemma lem3400493 {A : Type'} : term5 A.
Proof. exact (EQ_MP (@lem3400425 A) (@lem3400492 A)). Qed.
