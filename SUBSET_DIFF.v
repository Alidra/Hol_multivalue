Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUBSET_DIFF_term_abbrevs.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211701_spec.
Require Import thm3211702_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Lemma lem3270392 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3270393 {_85745 : Type'} (s : _85745 -> Prop) (t : _85745 -> Prop) : (@SUBSET _85745 s t) = (term0 _85745 s t).
Proof. exact (@lem3270392 _85745 s t). Qed.
Lemma lem3270394 {_85745 : Type'} (t : _85745 -> Prop) (s : _85745 -> Prop) : (term1 _85745 t s) = (term2 _85745 t s).
Proof. exact (@lem3270393 _85745 (@DIFF _85745 s t) s). Qed.
Lemma lem3270401 {_85745 : Type'} (s : _85745 -> Prop) : (term3 _85745 s) = (term4 _85745 s).
Proof. exact (fun_ext (fun t : _85745 -> Prop => @lem3270394 _85745 t s)). Qed.
Lemma lem3270402 {_85745 : Type'} : (@all (_85745 -> Prop)) = (@all (_85745 -> Prop)).
Proof. exact (eq_refl (@all (_85745 -> Prop))). Qed.
Lemma lem3270403 {_85745 : Type'} (s : _85745 -> Prop) : (term5 _85745 s) = (term6 _85745 s).
Proof. exact (MK_COMB (@lem3270402 _85745) (@lem3270401 _85745 s)). Qed.
Lemma lem3270408 {_85745 : Type'} : (term7 _85745) = (term8 _85745).
Proof. exact (fun_ext (fun s : _85745 -> Prop => @lem3270403 _85745 s)). Qed.
Lemma lem3270409 {_85745 : Type'} : (@all (_85745 -> Prop)) = (@all (_85745 -> Prop)).
Proof. exact (eq_refl (@all (_85745 -> Prop))). Qed.
Lemma lem3270410 {_85745 : Type'} : (term9 _85745) = (term10 _85745).
Proof. exact (MK_COMB (@lem3270409 _85745) (@lem3270408 _85745)). Qed.
Lemma lem3270415 {_85745 : Type'} : (term10 _85745) = (term9 _85745).
Proof. exact (SYM (@lem3270410 _85745)). Qed.
Lemma lem3270431 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term11 A x s t) = (term12 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem3270432 {_85745 : Type'} (s : _85745 -> Prop) (x : _85745) (t : _85745 -> Prop) : (term11 _85745 x s t) = (term12 _85745 s x t).
Proof. exact (@lem3270431 _85745 s x t). Qed.
Lemma lem3270436 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3270437 {_85745 : Type'} (P : _85745 -> Prop) (x : _85745) : (@IN _85745 x P) = (P x).
Proof. exact (@lem3270436 _85745 P x). Qed.
Lemma lem3270438 {_85745 : Type'} (s : _85745 -> Prop) (x : _85745) : (@IN _85745 x s) = (s x).
Proof. exact (@lem3270437 _85745 s x). Qed.
Lemma lem3270439 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3270440 {_85745 : Type'} (s : _85745 -> Prop) (x : _85745) : (term13 _85745 x s) = (term14 _85745 s x).
Proof. exact (MK_COMB (@lem3270439) (@lem3270438 _85745 s x)). Qed.
Lemma lem3270442 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3270443 {_85745 : Type'} (P : _85745 -> Prop) (x : _85745) : (@IN _85745 x P) = (P x).
Proof. exact (@lem3270442 _85745 P x). Qed.
Lemma lem3270444 {_85745 : Type'} (t : _85745 -> Prop) (x : _85745) : (@IN _85745 x t) = (t x).
Proof. exact (@lem3270443 _85745 t x). Qed.
Lemma lem3270445 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3270446 {_85745 : Type'} (t : _85745 -> Prop) (x : _85745) : (term15 _85745 x t) = (term16 _85745 t x).
Proof. exact (MK_COMB (@lem3270445) (@lem3270444 _85745 t x)). Qed.
Lemma lem3270447 {_85745 : Type'} (s : _85745 -> Prop) (t : _85745 -> Prop) (x : _85745) : (term12 _85745 s x t) = (term17 _85745 s t x).
Proof. exact (MK_COMB (@lem3270440 _85745 s x) (@lem3270446 _85745 t x)). Qed.
Lemma lem3270450 {_85745 : Type'} (s : _85745 -> Prop) (t : _85745 -> Prop) (x : _85745) : (term11 _85745 x s t) = (term17 _85745 s t x).
Proof. exact (TRANS (@lem3270432 _85745 s x t) (@lem3270447 _85745 s t x)). Qed.
Lemma lem3270451 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3270452 {_85745 : Type'} (s : _85745 -> Prop) (t : _85745 -> Prop) (x : _85745) : (term18 _85745 x s t) = (term19 _85745 s t x).
Proof. exact (MK_COMB (@lem3270451) (@lem3270450 _85745 s t x)). Qed.
Lemma lem3270454 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3270455 {_85745 : Type'} (P : _85745 -> Prop) (x : _85745) : (@IN _85745 x P) = (P x).
Proof. exact (@lem3270454 _85745 P x). Qed.
Lemma lem3270456 {_85745 : Type'} (s : _85745 -> Prop) (x : _85745) : (@IN _85745 x s) = (s x).
Proof. exact (@lem3270455 _85745 s x). Qed.
Lemma lem3270457 {_85745 : Type'} (t : _85745 -> Prop) (s : _85745 -> Prop) (x : _85745) : (term20 _85745 t x s) = (term21 _85745 t s x).
Proof. exact (MK_COMB (@lem3270452 _85745 s t x) (@lem3270456 _85745 s x)). Qed.
Lemma lem3270460 {_85745 : Type'} (t : _85745 -> Prop) (s : _85745 -> Prop) : (term22 _85745 t s) = (term23 _85745 t s).
Proof. exact (fun_ext (fun x : _85745 => @lem3270457 _85745 t s x)). Qed.
Lemma lem3270461 {_85745 : Type'} : (@all _85745) = (@all _85745).
Proof. exact (eq_refl (@all _85745)). Qed.
Lemma lem3270462 {_85745 : Type'} (t : _85745 -> Prop) (s : _85745 -> Prop) : (term2 _85745 t s) = (term24 _85745 t s).
Proof. exact (MK_COMB (@lem3270461 _85745) (@lem3270460 _85745 t s)). Qed.
Lemma lem3270467 {_85745 : Type'} (s : _85745 -> Prop) : (term4 _85745 s) = (term25 _85745 s).
Proof. exact (fun_ext (fun t : _85745 -> Prop => @lem3270462 _85745 t s)). Qed.
Lemma lem3270468 {_85745 : Type'} : (@all (_85745 -> Prop)) = (@all (_85745 -> Prop)).
Proof. exact (eq_refl (@all (_85745 -> Prop))). Qed.
Lemma lem3270469 {_85745 : Type'} (s : _85745 -> Prop) : (term6 _85745 s) = (term26 _85745 s).
Proof. exact (MK_COMB (@lem3270468 _85745) (@lem3270467 _85745 s)). Qed.
Lemma lem3270474 {_85745 : Type'} : (term8 _85745) = (term27 _85745).
Proof. exact (fun_ext (fun s : _85745 -> Prop => @lem3270469 _85745 s)). Qed.
Lemma lem3270475 {_85745 : Type'} : (@all (_85745 -> Prop)) = (@all (_85745 -> Prop)).
Proof. exact (eq_refl (@all (_85745 -> Prop))). Qed.
Lemma lem3270476 {_85745 : Type'} : (term10 _85745) = (term28 _85745).
Proof. exact (MK_COMB (@lem3270475 _85745) (@lem3270474 _85745)). Qed.
Lemma lem3270481 {_85745 : Type'} : (term28 _85745) = (term10 _85745).
Proof. exact (SYM (@lem3270476 _85745)). Qed.
Lemma lem3270483 (p : Prop) : p = (term29 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3270484 {_85745 : Type'} : (term28 _85745) = (term30 _85745).
Proof. exact (@lem3270483 (term28 _85745)). Qed.
Lemma lem3270485 {_85745 : Type'} : (term30 _85745) = (term28 _85745).
Proof. exact (SYM (@lem3270484 _85745)). Qed.
Lemma lem3270486 {_85745 : Type'} (h1 : term31 _85745) : term31 _85745.
Proof. exact (h1). Qed.
Lemma lem3270489 {_85745 : Type'} (h1 : term30 _85745) : term30 _85745.
Proof. exact (h1). Qed.
Lemma lem3270490 {_85745 : Type'} : term32 _85745.
Proof. exact (fun h0 : term30 _85745 => @lem3270489 _85745 h0). Qed.
Lemma lem3270491 {_85745 : Type'} (h1 : term32 _85745) : term32 _85745.
Proof. exact (h1). Qed.
Lemma lem3270492 {_85745 : Type'} (h1 : term30 _85745) : term30 _85745.
Proof. exact (h1). Qed.
Lemma lem3270493 {_85745 : Type'} (h1 : term30 _85745) (h2 : term32 _85745) : term30 _85745.
Proof. exact (@lem3270491 _85745 h2 (@lem3270492 _85745 h1)). Qed.
Lemma lem3270494 {_85745 : Type'} (h1 : term30 _85745) : term33 _85745.
Proof. exact (fun h0 : term32 _85745 => @lem3270493 _85745 h1 h0). Qed.
Lemma lem3270495 {_85745 : Type'} (h1 : term32 _85745) : term32 _85745.
Proof. exact (h1). Qed.
Lemma lem3270496 {_85745 : Type'} (h1 : term30 _85745) (h2 : term32 _85745) : term30 _85745.
Proof. exact (@lem3270494 _85745 h1 (@lem3270495 _85745 h2)). Qed.
Lemma lem3270497 {_85745 : Type'} (h1 : term32 _85745) : term32 _85745.
Proof. exact (fun h0 : term30 _85745 => @lem3270496 _85745 h0 h1). Qed.
Lemma lem3270498 {_85745 : Type'} : term34 _85745.
Proof. exact (fun h0 : term32 _85745 => @lem3270497 _85745 h0). Qed.
Lemma lem3270501 {_85745 : Type'} : term32 _85745.
Proof. exact (@lem3270498 _85745 (@lem3270490 _85745)). Qed.
Lemma lem3270502 {_85745 : Type'} : term32 _85745.
Proof. exact (@lem3270501 _85745). Qed.
Lemma lem3270504 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3270505 {_85745 : Type'} : (term30 _85745) = (term35 _85745).
Proof. exact (@lem3270504 (term31 _85745)). Qed.
Lemma lem3270507 (t : Prop) : (term36 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3270508 {_85745 : Type'} : (term35 _85745) = (term28 _85745).
Proof. exact (@lem3270507 (term28 _85745)). Qed.
Lemma lem3270529 {_85745 : Type'} : (term30 _85745) = (term28 _85745).
Proof. exact (TRANS (@lem3270505 _85745) (@lem3270508 _85745)). Qed.
Lemma lem3270540 {_85745 : Type'} (t : _85745 -> Prop) (s : _85745 -> Prop) (x : _85745) : (term21 _85745 t s x) = (term21 _85745 t s x).
Proof. exact (eq_refl (term21 _85745 t s x)). Qed.
Lemma lem3270541 {_85745 : Type'} (t : _85745 -> Prop) (s : _85745 -> Prop) : (term23 _85745 t s) = (term23 _85745 t s).
Proof. exact (fun_ext (fun x : _85745 => @lem3270540 _85745 t s x)). Qed.
Lemma lem3270542 {_85745 : Type'} : (@all _85745) = (@all _85745).
Proof. exact (eq_refl (@all _85745)). Qed.
Lemma lem3270543 {_85745 : Type'} (t : _85745 -> Prop) (s : _85745 -> Prop) : (term24 _85745 t s) = (term24 _85745 t s).
Proof. exact (MK_COMB (@lem3270542 _85745) (@lem3270541 _85745 t s)). Qed.
Lemma lem3270544 {_85745 : Type'} (s : _85745 -> Prop) : (term25 _85745 s) = (term25 _85745 s).
Proof. exact (fun_ext (fun t : _85745 -> Prop => @lem3270543 _85745 t s)). Qed.
Lemma lem3270545 {_85745 : Type'} : (@all (_85745 -> Prop)) = (@all (_85745 -> Prop)).
Proof. exact (eq_refl (@all (_85745 -> Prop))). Qed.
Lemma lem3270546 {_85745 : Type'} (s : _85745 -> Prop) : (term26 _85745 s) = (term26 _85745 s).
Proof. exact (MK_COMB (@lem3270545 _85745) (@lem3270544 _85745 s)). Qed.
Lemma lem3270547 {_85745 : Type'} : (term27 _85745) = (term27 _85745).
Proof. exact (fun_ext (fun s : _85745 -> Prop => @lem3270546 _85745 s)). Qed.
Lemma lem3270548 {_85745 : Type'} : (@all (_85745 -> Prop)) = (@all (_85745 -> Prop)).
Proof. exact (eq_refl (@all (_85745 -> Prop))). Qed.
Lemma lem3270549 {_85745 : Type'} : (term28 _85745) = (term28 _85745).
Proof. exact (MK_COMB (@lem3270548 _85745) (@lem3270547 _85745)). Qed.
Lemma lem3270574 {_85745 : Type'} : (term30 _85745) = (term28 _85745).
Proof. exact (TRANS (@lem3270529 _85745) (@lem3270549 _85745)). Qed.
Lemma lem3270575 {_85745 : Type'} : (term28 _85745) = (term30 _85745).
Proof. exact (SYM (@lem3270574 _85745)). Qed.
Lemma lem3270578 (p : Prop) : p = (term29 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3270579 {_85745 : Type'} (s : _85745 -> Prop) (x : _85745) : (s x) = (term37 _85745 s x).
Proof. exact (@lem3270578 (s x)). Qed.
Lemma lem3270580 {_85745 : Type'} (s : _85745 -> Prop) (x : _85745) : (term37 _85745 s x) = (s x).
Proof. exact (SYM (@lem3270579 _85745 s x)). Qed.
Lemma lem3270581 {_85745 : Type'} (s : _85745 -> Prop) (x : _85745) (h1 : term16 _85745 s x) : term16 _85745 s x.
Proof. exact (h1). Qed.
Lemma lem3270591 {_85745 : Type'} (s : _85745 -> Prop) (t : _85745 -> Prop) (x : _85745) (h1 : term17 _85745 s t x) : term17 _85745 s t x.
Proof. exact (h1). Qed.
Lemma lem3270597 {_85745 : Type'} (s : _85745 -> Prop) (x : _85745) (h1 : term16 _85745 s x) : term16 _85745 s x.
Proof. exact (h1). Qed.
Lemma lem3270609 {_85745 : Type'} (s : _85745 -> Prop) (t : _85745 -> Prop) (x : _85745) (h1 : term17 _85745 s t x) : term17 _85745 s t x.
Proof. exact (h1). Qed.
Lemma lem3270615 {_85745 : Type'} (s : _85745 -> Prop) (x : _85745) (h1 : term16 _85745 s x) : term16 _85745 s x.
Proof. exact (h1). Qed.
Lemma lem3270621 {_85745 : Type'} (s : _85745 -> Prop) (x : _85745) (h1 : term16 _85745 s x) : term16 _85745 s x.
Proof. exact (h1). Qed.
Lemma lem3270631 {_85745 : Type'} (s : _85745 -> Prop) (x : _85745) (h1 : term16 _85745 s x) : term16 _85745 s x.
Proof. exact (h1). Qed.
Lemma lem3270637 {_85745 : Type'} (s : _85745 -> Prop) (t : _85745 -> Prop) (x : _85745) (h1 : term17 _85745 s t x) : s x.
Proof. exact (proj1 (@lem3270609 _85745 s t x h1)). Qed.
Lemma lem3270638 {_85745 : Type'} (s : _85745 -> Prop) (t : _85745 -> Prop) (x : _85745) (h1 : term17 _85745 s t x) : term38 _85745 s x.
Proof. exact (fun h0 : term16 _85745 s x => @lem3270637 _85745 s t x h1). Qed.
Lemma lem3270640 (p : Prop) : (term39 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3270641 {_85745 : Type'} (s : _85745 -> Prop) (x : _85745) : (term38 _85745 s x) = (s x).
Proof. exact (@lem3270640 (s x)). Qed.
Lemma lem3270642 {_85745 : Type'} (s : _85745 -> Prop) (t : _85745 -> Prop) (x : _85745) (h1 : term17 _85745 s t x) : s x.
Proof. exact (EQ_MP (@lem3270641 _85745 s x) (@lem3270638 _85745 s t x h1)). Qed.
Lemma lem3270645 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3270647 {_85745 : Type'} (s : _85745 -> Prop) (x : _85745) : (term16 _85745 s x) = (term40 _85745 s x).
Proof. exact (@lem3270645 (s x)). Qed.
Lemma lem3270650 {_85745 : Type'} (s : _85745 -> Prop) (x : _85745) (h1 : term16 _85745 s x) : term40 _85745 s x.
Proof. exact (EQ_MP (@lem3270647 _85745 s x) (@lem3270631 _85745 s x h1)). Qed.
Lemma lem3270653 {_85745 : Type'} (s : _85745 -> Prop) (t : _85745 -> Prop) (x : _85745) (h1 : term16 _85745 s x) (h2 : term17 _85745 s t x) : False.
Proof. exact (@lem3270650 _85745 s x h1 (@lem3270642 _85745 s t x h2)). Qed.
Lemma lem3270654 {_85745 : Type'} (s : _85745 -> Prop) (t : _85745 -> Prop) (x : _85745) (h1 : term16 _85745 s x) (h2 : term17 _85745 s t x) : term41.
Proof. exact (fun h0 : ~ False => @lem3270653 _85745 s t x h1 h2). Qed.
Lemma lem3270656 (p : Prop) : (term39 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3270657 : term41 = False.
Proof. exact (@lem3270656 False). Qed.
Lemma lem3270658 {_85745 : Type'} (s : _85745 -> Prop) (t : _85745 -> Prop) (x : _85745) (h1 : term16 _85745 s x) (h2 : term17 _85745 s t x) : False.
Proof. exact (EQ_MP (@lem3270657) (@lem3270654 _85745 s t x h1 h2)). Qed.
Lemma lem3270659 {_85745 : Type'} (s : _85745 -> Prop) (t : _85745 -> Prop) (x : _85745) (h1 : term16 _85745 s x) (h2 : term17 _85745 s t x) : (term16 _85745 s x) = False.
Proof. exact (prop_ext (fun h3 : term16 _85745 s x => @lem3270658 _85745 s t x h1 h2) (fun h3 : False => @lem3270631 _85745 s x h1)). Qed.
Lemma lem3270660 {_85745 : Type'} (s : _85745 -> Prop) (t : _85745 -> Prop) (x : _85745) (h1 : term16 _85745 s x) (h2 : term17 _85745 s t x) : False.
Proof. exact (EQ_MP (@lem3270659 _85745 s t x h1 h2) (@lem3270631 _85745 s x h1)). Qed.
Lemma lem3270661 {_85745 : Type'} (s : _85745 -> Prop) (t : _85745 -> Prop) (x : _85745) (h1 : term16 _85745 s x) (h2 : term17 _85745 s t x) : (term16 _85745 s x) = False.
Proof. exact (prop_ext (fun h3 : term16 _85745 s x => @lem3270660 _85745 s t x h1 h2) (fun h3 : False => @lem3270621 _85745 s x h1)). Qed.
Lemma lem3270662 {_85745 : Type'} (s : _85745 -> Prop) (t : _85745 -> Prop) (x : _85745) (h1 : term16 _85745 s x) (h2 : term17 _85745 s t x) : False.
Proof. exact (EQ_MP (@lem3270661 _85745 s t x h1 h2) (@lem3270621 _85745 s x h1)). Qed.
Lemma lem3270663 {_85745 : Type'} (s : _85745 -> Prop) (t : _85745 -> Prop) (x : _85745) (h1 : term16 _85745 s x) (h2 : term17 _85745 s t x) : (term16 _85745 s x) = False.
Proof. exact (prop_ext (fun h3 : term16 _85745 s x => @lem3270662 _85745 s t x h1 h2) (fun h3 : False => @lem3270621 _85745 s x h1)). Qed.
Lemma lem3270664 {_85745 : Type'} (s : _85745 -> Prop) (t : _85745 -> Prop) (x : _85745) (h1 : term16 _85745 s x) (h2 : term17 _85745 s t x) : False.
Proof. exact (EQ_MP (@lem3270663 _85745 s t x h1 h2) (@lem3270621 _85745 s x h1)). Qed.
Lemma lem3270665 {_85745 : Type'} (s : _85745 -> Prop) (t : _85745 -> Prop) (x : _85745) (h1 : term16 _85745 s x) (h2 : term17 _85745 s t x) : (term16 _85745 s x) = False.
Proof. exact (prop_ext (fun h3 : term16 _85745 s x => @lem3270664 _85745 s t x h1 h2) (fun h3 : False => @lem3270615 _85745 s x h1)). Qed.
Lemma lem3270666 {_85745 : Type'} (s : _85745 -> Prop) (t : _85745 -> Prop) (x : _85745) (h1 : term16 _85745 s x) (h2 : term17 _85745 s t x) : False.
Proof. exact (EQ_MP (@lem3270665 _85745 s t x h1 h2) (@lem3270615 _85745 s x h1)). Qed.
Lemma lem3270667 {_85745 : Type'} (s : _85745 -> Prop) (t : _85745 -> Prop) (x : _85745) (h1 : term16 _85745 s x) (h2 : term17 _85745 s t x) : (term17 _85745 s t x) = False.
Proof. exact (prop_ext (fun h3 : term17 _85745 s t x => @lem3270666 _85745 s t x h1 h2) (fun h3 : False => @lem3270609 _85745 s t x h2)). Qed.
Lemma lem3270668 {_85745 : Type'} (s : _85745 -> Prop) (t : _85745 -> Prop) (x : _85745) (h1 : term16 _85745 s x) (h2 : term17 _85745 s t x) : False.
Proof. exact (EQ_MP (@lem3270667 _85745 s t x h1 h2) (@lem3270609 _85745 s t x h2)). Qed.
Lemma lem3270669 {_85745 : Type'} (s : _85745 -> Prop) (t : _85745 -> Prop) (x : _85745) (h1 : term16 _85745 s x) (h2 : term17 _85745 s t x) : (term16 _85745 s x) = False.
Proof. exact (prop_ext (fun h3 : term16 _85745 s x => @lem3270668 _85745 s t x h1 h2) (fun h3 : False => @lem3270597 _85745 s x h1)). Qed.
Lemma lem3270670 {_85745 : Type'} (s : _85745 -> Prop) (t : _85745 -> Prop) (x : _85745) (h1 : term16 _85745 s x) (h2 : term17 _85745 s t x) : False.
Proof. exact (EQ_MP (@lem3270669 _85745 s t x h1 h2) (@lem3270597 _85745 s x h1)). Qed.
Lemma lem3270671 {_85745 : Type'} (s : _85745 -> Prop) (t : _85745 -> Prop) (x : _85745) (h1 : term16 _85745 s x) (h2 : term17 _85745 s t x) : (term17 _85745 s t x) = False.
Proof. exact (prop_ext (fun h3 : term17 _85745 s t x => @lem3270670 _85745 s t x h1 h2) (fun h3 : False => @lem3270591 _85745 s t x h2)). Qed.
Lemma lem3270672 {_85745 : Type'} (s : _85745 -> Prop) (t : _85745 -> Prop) (x : _85745) (h1 : term16 _85745 s x) (h2 : term17 _85745 s t x) : False.
Proof. exact (EQ_MP (@lem3270671 _85745 s t x h1 h2) (@lem3270591 _85745 s t x h2)). Qed.
Lemma lem3270673 {_85745 : Type'} (s : _85745 -> Prop) (t : _85745 -> Prop) (x : _85745) (h1 : term16 _85745 s x) (h2 : term17 _85745 s t x) : (term16 _85745 s x) = False.
Proof. exact (prop_ext (fun h3 : term16 _85745 s x => @lem3270672 _85745 s t x h1 h2) (fun h3 : False => @lem3270581 _85745 s x h1)). Qed.
Lemma lem3270674 {_85745 : Type'} (s : _85745 -> Prop) (t : _85745 -> Prop) (x : _85745) (h1 : term16 _85745 s x) (h2 : term17 _85745 s t x) : False.
Proof. exact (EQ_MP (@lem3270673 _85745 s t x h1 h2) (@lem3270581 _85745 s x h1)). Qed.
Lemma lem3270675 {_85745 : Type'} (s : _85745 -> Prop) (t : _85745 -> Prop) (x : _85745) (h1 : term17 _85745 s t x) : term37 _85745 s x.
Proof. exact (fun h0 : term16 _85745 s x => @lem3270674 _85745 s t x h0 h1). Qed.
Lemma lem3270676 {_85745 : Type'} (s : _85745 -> Prop) (t : _85745 -> Prop) (x : _85745) (h1 : term17 _85745 s t x) : s x.
Proof. exact (EQ_MP (@lem3270580 _85745 s x) (@lem3270675 _85745 s t x h1)). Qed.
Lemma lem3270677 {_85745 : Type'} (t : _85745 -> Prop) (s : _85745 -> Prop) (x : _85745) : term21 _85745 t s x.
Proof. exact (fun h0 : term17 _85745 s t x => @lem3270676 _85745 s t x h0). Qed.
Lemma lem3270682 {_85745 : Type'} (t : _85745 -> Prop) (s : _85745 -> Prop) : term24 _85745 t s.
Proof. exact (fun x : _85745 => @lem3270677 _85745 t s x). Qed.
Lemma lem3270687 {_85745 : Type'} (s : _85745 -> Prop) : term26 _85745 s.
Proof. exact (fun t : _85745 -> Prop => @lem3270682 _85745 t s). Qed.
Lemma lem3270692 {_85745 : Type'} : term28 _85745.
Proof. exact (fun s : _85745 -> Prop => @lem3270687 _85745 s). Qed.
Lemma lem3270693 {_85745 : Type'} : term30 _85745.
Proof. exact (EQ_MP (@lem3270575 _85745) (@lem3270692 _85745)). Qed.
Lemma lem3270695 {_85745 : Type'} : term30 _85745.
Proof. exact (@lem3270502 _85745 (@lem3270693 _85745)). Qed.
Lemma lem3270696 {_85745 : Type'} (h1 : term31 _85745) : False.
Proof. exact (@lem3270695 _85745 (@lem3270486 _85745 h1)). Qed.
Lemma lem3270697 {_85745 : Type'} (h1 : term31 _85745) : (term31 _85745) = False.
Proof. exact (prop_ext (fun h2 : term31 _85745 => @lem3270696 _85745 h1) (fun h2 : False => @lem3270486 _85745 h1)). Qed.
Lemma lem3270698 {_85745 : Type'} (h1 : term31 _85745) : False.
Proof. exact (EQ_MP (@lem3270697 _85745 h1) (@lem3270486 _85745 h1)). Qed.
Lemma lem3270699 {_85745 : Type'} : term30 _85745.
Proof. exact (fun h0 : term31 _85745 => @lem3270698 _85745 h0). Qed.
Lemma lem3270700 {_85745 : Type'} : term28 _85745.
Proof. exact (EQ_MP (@lem3270485 _85745) (@lem3270699 _85745)). Qed.
Lemma lem3270701 {_85745 : Type'} : term10 _85745.
Proof. exact (EQ_MP (@lem3270481 _85745) (@lem3270700 _85745)). Qed.
Lemma lem3270702 {_85745 : Type'} : term9 _85745.
Proof. exact (EQ_MP (@lem3270415 _85745) (@lem3270701 _85745)). Qed.
