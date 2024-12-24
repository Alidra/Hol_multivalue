Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import UNIONS_SINGS_GEN_term_abbrevs.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm1834_spec.
Require Import thm18394_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3211640_spec.
Require Import thm3211641_spec.
Require Import thm3211692_spec.
Require Import thm3211693_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm3458971_spec.
Require Import thm3458974_spec.
Lemma lem3464436 {_89520 _89534 : Type'} : term0 _89520 _89534.
Proof. exact (EQ_MP (@lem3458974 _89520 _89534) (@lem3458971 _89520 _89534)). Qed.
Lemma lem3464437 {_89520 _89534 : Type'} (P : _89534 -> Prop) : term1 _89520 _89534 P.
Proof. exact (@lem3464436 _89520 _89534 P). Qed.
Lemma lem3464438 {_89520 _89534 : Type'} (P : _89534 -> Prop) : (term1 _89520 _89534 P) = (term2 _89520 _89534 P).
Proof. exact (eq_refl (term1 _89520 _89534 P)). Qed.
Lemma lem3464439 {_89520 _89534 : Type'} (P : _89534 -> Prop) : term2 _89520 _89534 P.
Proof. exact (EQ_MP (@lem3464438 _89520 _89534 P) (@lem3464437 _89520 _89534 P)). Qed.
Lemma lem3464440 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) : term3 _89520 _89534 P f.
Proof. exact (@lem3464439 _89520 _89534 P f). Qed.
Lemma lem3464441 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) : (term3 _89520 _89534 P f) = ((term4 _89520 _89534 P f) = (term5 _89520 _89534 P f)).
Proof. exact (eq_refl (term3 _89520 _89534 P f)). Qed.
Lemma lem3464450 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) : (term4 _89520 _89534 P f) = (term5 _89520 _89534 P f).
Proof. exact (EQ_MP (@lem3464441 _89520 _89534 P f) (@lem3464440 _89520 _89534 P f)). Qed.
Lemma lem3464451 {A : Type'} (P : A -> Prop) (f : type1402 A) : (term6 A P f) = (term7 A P f).
Proof. exact (@lem3464450 A A P f). Qed.
Lemma lem3464452 {A : Type'} (P : A -> Prop) : (term8 A P) = (term9 A P).
Proof. exact (@lem3464451 A P (term10 A)). Qed.
Lemma lem3464453 {A : Type'} (x : A) : (term11 A x) = (@INSERT A x (@EMPTY A)).
Proof. exact (eq_refl (term11 A x)). Qed.
Lemma lem3464454 {A : Type'} (GEN_PVAR_61 : A -> Prop) (P : A -> Prop) (x : A) : (term12 A GEN_PVAR_61 P x) = (term12 A GEN_PVAR_61 P x).
Proof. exact (eq_refl (term12 A GEN_PVAR_61 P x)). Qed.
Lemma lem3464455 {A : Type'} (GEN_PVAR_61 : A -> Prop) (P : A -> Prop) (x : A) : (term13 A GEN_PVAR_61 P x) = (term14 A GEN_PVAR_61 P x).
Proof. exact (MK_COMB (@lem3464454 A GEN_PVAR_61 P x) (@lem3464453 A x)). Qed.
Lemma lem3464456 {A : Type'} (GEN_PVAR_61 : A -> Prop) (P : A -> Prop) : (term15 A GEN_PVAR_61 P) = (term16 A GEN_PVAR_61 P).
Proof. exact (fun_ext (fun x : A => @lem3464455 A GEN_PVAR_61 P x)). Qed.
Lemma lem3464457 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3464458 {A : Type'} (GEN_PVAR_61 : A -> Prop) (P : A -> Prop) : (term17 A GEN_PVAR_61 P) = (term18 A GEN_PVAR_61 P).
Proof. exact (MK_COMB (@lem3464457 A) (@lem3464456 A GEN_PVAR_61 P)). Qed.
Lemma lem3464459 {A : Type'} (P : A -> Prop) : (term19 A P) = (term20 A P).
Proof. exact (fun_ext (fun GEN_PVAR_61 : A -> Prop => @lem3464458 A GEN_PVAR_61 P)). Qed.
Lemma lem3464460 {A : Type'} : (@GSPEC (A -> Prop)) = (@GSPEC (A -> Prop)).
Proof. exact (eq_refl (@GSPEC (A -> Prop))). Qed.
Lemma lem3464461 {A : Type'} (P : A -> Prop) : (term21 A P) = (term22 A P).
Proof. exact (MK_COMB (@lem3464460 A) (@lem3464459 A P)). Qed.
Lemma lem3464462 {A : Type'} : (@UNIONS A) = (@UNIONS A).
Proof. exact (eq_refl (@UNIONS A)). Qed.
Lemma lem3464463 {A : Type'} (P : A -> Prop) : (term8 A P) = (term23 A P).
Proof. exact (MK_COMB (@lem3464462 A) (@lem3464461 A P)). Qed.
Lemma lem3464464 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem3464465 {A : Type'} (P : A -> Prop) : (term24 A P) = (term25 A P).
Proof. exact (MK_COMB (@lem3464464 A) (@lem3464463 A P)). Qed.
Lemma lem3464466 {A : Type'} (x : A) : (term11 A x) = (@INSERT A x (@EMPTY A)).
Proof. exact (eq_refl (term11 A x)). Qed.
Lemma lem3464467 {A : Type'} (a : A) : (@IN A a) = (@IN A a).
Proof. exact (eq_refl (@IN A a)). Qed.
Lemma lem3464468 {A : Type'} (a : A) (x : A) : (term26 A a x) = (term27 A a x).
Proof. exact (MK_COMB (@lem3464467 A a) (@lem3464466 A x)). Qed.
Lemma lem3464469 {A : Type'} (P : A -> Prop) (x : A) : (term28 A P x) = (term28 A P x).
Proof. exact (eq_refl (term28 A P x)). Qed.
Lemma lem3464470 {A : Type'} (P : A -> Prop) (a : A) (x : A) : (term29 A P a x) = (term30 A P a x).
Proof. exact (MK_COMB (@lem3464469 A P x) (@lem3464468 A a x)). Qed.
Lemma lem3464471 {A : Type'} (P : A -> Prop) (a : A) : (term31 A P a) = (term32 A P a).
Proof. exact (fun_ext (fun x : A => @lem3464470 A P a x)). Qed.
Lemma lem3464472 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3464473 {A : Type'} (P : A -> Prop) (a : A) : (term33 A P a) = (term34 A P a).
Proof. exact (MK_COMB (@lem3464472 A) (@lem3464471 A P a)). Qed.
Lemma lem3464474 {A : Type'} (GEN_PVAR_50 : A) : (@SETSPEC A GEN_PVAR_50) = (@SETSPEC A GEN_PVAR_50).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_50)). Qed.
Lemma lem3464475 {A : Type'} (GEN_PVAR_50 : A) (P : A -> Prop) (a : A) : (term35 A GEN_PVAR_50 P a) = (term36 A GEN_PVAR_50 P a).
Proof. exact (MK_COMB (@lem3464474 A GEN_PVAR_50) (@lem3464473 A P a)). Qed.
Lemma lem3464476 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem3464477 {A : Type'} (GEN_PVAR_50 : A) (P : A -> Prop) (a : A) : (term37 A GEN_PVAR_50 P a) = (term38 A GEN_PVAR_50 P a).
Proof. exact (MK_COMB (@lem3464475 A GEN_PVAR_50 P a) (@lem3464476 A a)). Qed.
Lemma lem3464478 {A : Type'} (GEN_PVAR_50 : A) (P : A -> Prop) : (term39 A GEN_PVAR_50 P) = (term40 A GEN_PVAR_50 P).
Proof. exact (fun_ext (fun a : A => @lem3464477 A GEN_PVAR_50 P a)). Qed.
Lemma lem3464479 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3464480 {A : Type'} (GEN_PVAR_50 : A) (P : A -> Prop) : (term41 A GEN_PVAR_50 P) = (term42 A GEN_PVAR_50 P).
Proof. exact (MK_COMB (@lem3464479 A) (@lem3464478 A GEN_PVAR_50 P)). Qed.
Lemma lem3464481 {A : Type'} (P : A -> Prop) : (term43 A P) = (term44 A P).
Proof. exact (fun_ext (fun GEN_PVAR_50 : A => @lem3464480 A GEN_PVAR_50 P)). Qed.
Lemma lem3464482 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem3464483 {A : Type'} (P : A -> Prop) : (term9 A P) = (term45 A P).
Proof. exact (MK_COMB (@lem3464482 A) (@lem3464481 A P)). Qed.
Lemma lem3464484 {A : Type'} (P : A -> Prop) : ((term8 A P) = (term9 A P)) = ((term23 A P) = (term45 A P)).
Proof. exact (MK_COMB (@lem3464465 A P) (@lem3464483 A P)). Qed.
Lemma lem3464485 {A : Type'} (P : A -> Prop) : (term23 A P) = (term45 A P).
Proof. exact (EQ_MP (@lem3464484 A P) (@lem3464452 A P)). Qed.
Lemma lem3464496 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem3464497 {A : Type'} (P : A -> Prop) : (term25 A P) = (term46 A P).
Proof. exact (MK_COMB (@lem3464496 A) (@lem3464485 A P)). Qed.
Lemma lem3464502 {A : Type'} (P : A -> Prop) : (term47 A P) = (term47 A P).
Proof. exact (eq_refl (term47 A P)). Qed.
Lemma lem3464503 {A : Type'} (P : A -> Prop) : ((term23 A P) = (term47 A P)) = ((term45 A P) = (term47 A P)).
Proof. exact (MK_COMB (@lem3464497 A P) (@lem3464502 A P)). Qed.
Lemma lem3464506 {A : Type'} : (term48 A) = (term49 A).
Proof. exact (fun_ext (fun P : A -> Prop => @lem3464503 A P)). Qed.
Lemma lem3464507 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3464508 {A : Type'} : (term50 A) = (term51 A).
Proof. exact (MK_COMB (@lem3464507 A) (@lem3464506 A)). Qed.
Lemma lem3464513 {A : Type'} : (term51 A) = (term50 A).
Proof. exact (SYM (@lem3464508 A)). Qed.
Lemma lem3464521 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term52 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3464522 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term52 A s t).
Proof. exact (@lem3464521 A s t). Qed.
Lemma lem3464523 {A : Type'} (P : A -> Prop) : ((term45 A P) = (term47 A P)) = (term53 A P).
Proof. exact (@lem3464522 A (term45 A P) (term47 A P)). Qed.
Lemma lem3464546 {A : Type'} : (term49 A) = (term54 A).
Proof. exact (fun_ext (fun P : A -> Prop => @lem3464523 A P)). Qed.
Lemma lem3464547 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3464548 {A : Type'} : (term51 A) = (term55 A).
Proof. exact (MK_COMB (@lem3464547 A) (@lem3464546 A)). Qed.
Lemma lem3464553 {A : Type'} : (term55 A) = (term51 A).
Proof. exact (SYM (@lem3464548 A)). Qed.
Lemma lem3464565 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term56 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem3464566 {A : Type'} (p : A -> Prop) (x : A) : (term56 A x p) = (p x).
Proof. exact (@lem3464565 A p x). Qed.
Lemma lem3464567 {A : Type'} (P : A -> Prop) (x : A) : (term57 A x P) = (term58 A P x).
Proof. exact (@lem3464566 A (term59 A P) x). Qed.
Lemma lem3464568 {A : Type'} (P : A -> Prop) (a : A) : (term58 A P a) = (term34 A P a).
Proof. exact (eq_refl (term58 A P a)). Qed.
Lemma lem3464569 {A : Type'} (GEN_PVAR_50 : A) : (@SETSPEC A GEN_PVAR_50) = (@SETSPEC A GEN_PVAR_50).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_50)). Qed.
Lemma lem3464570 {A : Type'} (GEN_PVAR_50 : A) (P : A -> Prop) (a : A) : (term60 A GEN_PVAR_50 P a) = (term36 A GEN_PVAR_50 P a).
Proof. exact (MK_COMB (@lem3464569 A GEN_PVAR_50) (@lem3464568 A P a)). Qed.
Lemma lem3464571 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem3464572 {A : Type'} (GEN_PVAR_50 : A) (P : A -> Prop) (a : A) : (term61 A GEN_PVAR_50 P a) = (term38 A GEN_PVAR_50 P a).
Proof. exact (MK_COMB (@lem3464570 A GEN_PVAR_50 P a) (@lem3464571 A a)). Qed.
Lemma lem3464573 {A : Type'} (GEN_PVAR_50 : A) (P : A -> Prop) : (term62 A GEN_PVAR_50 P) = (term40 A GEN_PVAR_50 P).
Proof. exact (fun_ext (fun a : A => @lem3464572 A GEN_PVAR_50 P a)). Qed.
Lemma lem3464574 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3464575 {A : Type'} (GEN_PVAR_50 : A) (P : A -> Prop) : (term63 A GEN_PVAR_50 P) = (term42 A GEN_PVAR_50 P).
Proof. exact (MK_COMB (@lem3464574 A) (@lem3464573 A GEN_PVAR_50 P)). Qed.
Lemma lem3464576 {A : Type'} (P : A -> Prop) : (term64 A P) = (term44 A P).
Proof. exact (fun_ext (fun GEN_PVAR_50 : A => @lem3464575 A GEN_PVAR_50 P)). Qed.
Lemma lem3464577 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem3464578 {A : Type'} (P : A -> Prop) : (term65 A P) = (term45 A P).
Proof. exact (MK_COMB (@lem3464577 A) (@lem3464576 A P)). Qed.
Lemma lem3464579 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem3464580 {A : Type'} (x : A) (P : A -> Prop) : (term57 A x P) = (term66 A x P).
Proof. exact (MK_COMB (@lem3464579 A x) (@lem3464578 A P)). Qed.
Lemma lem3464581 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3464582 {A : Type'} (x : A) (P : A -> Prop) : (term67 A x P) = (term68 A x P).
Proof. exact (MK_COMB (@lem3464581) (@lem3464580 A x P)). Qed.
Lemma lem3464583 {A : Type'} (P : A -> Prop) (x : A) : (term58 A P x) = (term34 A P x).
Proof. exact (eq_refl (term58 A P x)). Qed.
Lemma lem3464584 {A : Type'} (P : A -> Prop) (x : A) : ((term57 A x P) = (term58 A P x)) = ((term66 A x P) = (term34 A P x)).
Proof. exact (MK_COMB (@lem3464582 A x P) (@lem3464583 A P x)). Qed.
Lemma lem3464585 {A : Type'} (P : A -> Prop) (x : A) : (term66 A x P) = (term34 A P x).
Proof. exact (EQ_MP (@lem3464584 A P x) (@lem3464567 A P x)). Qed.
Lemma lem3464593 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term69 A x y s) = (term70 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3464594 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term69 A x y s) = (term70 A y x s).
Proof. exact (@lem3464593 A y x s). Qed.
Lemma lem3464595 {A : Type'} (x' : A) (x : A) : (term27 A x x') = (term71 A x' x).
Proof. exact (@lem3464594 A x' x (@EMPTY A)). Qed.
Lemma lem3464601 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3464602 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3464601 A x). Qed.
Lemma lem3464603 {A : Type'} (x : A) (x' : A) : (term72 A x x') = (term72 A x x').
Proof. exact (eq_refl (term72 A x x')). Qed.
Lemma lem3464604 {A : Type'} (x : A) (x' : A) : (term71 A x' x) = (term73 A x x').
Proof. exact (MK_COMB (@lem3464603 A x x') (@lem3464602 A x)). Qed.
Lemma lem3464606 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem3464607 {A : Type'} (x : A) (x' : A) : (term73 A x x') = (x = x').
Proof. exact (@lem3464606 (x = x')). Qed.
Lemma lem3464610 {A : Type'} (x : A) (x' : A) : (term71 A x' x) = (x = x').
Proof. exact (TRANS (@lem3464604 A x x') (@lem3464607 A x x')). Qed.
Lemma lem3464611 {A : Type'} (x : A) (x' : A) : (term27 A x x') = (x = x').
Proof. exact (TRANS (@lem3464595 A x' x) (@lem3464610 A x x')). Qed.
Lemma lem3464612 {A : Type'} (P : A -> Prop) (x' : A) : (term28 A P x') = (term28 A P x').
Proof. exact (eq_refl (term28 A P x')). Qed.
Lemma lem3464613 {A : Type'} (P : A -> Prop) (x : A) (x' : A) : (term30 A P x x') = (term74 A P x x').
Proof. exact (MK_COMB (@lem3464612 A P x') (@lem3464611 A x x')). Qed.
Lemma lem3464616 {A : Type'} (P : A -> Prop) (x : A) : (term32 A P x) = (term75 A P x).
Proof. exact (fun_ext (fun x' : A => @lem3464613 A P x x')). Qed.
Lemma lem3464617 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3464618 {A : Type'} (P : A -> Prop) (x : A) : (term34 A P x) = (term76 A P x).
Proof. exact (MK_COMB (@lem3464617 A) (@lem3464616 A P x)). Qed.
Lemma lem3464623 {A : Type'} (P : A -> Prop) (x : A) : (term66 A x P) = (term76 A P x).
Proof. exact (TRANS (@lem3464585 A P x) (@lem3464618 A P x)). Qed.
Lemma lem3464624 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3464625 {A : Type'} (P : A -> Prop) (x : A) : (term68 A x P) = (term77 A P x).
Proof. exact (MK_COMB (@lem3464624) (@lem3464623 A P x)). Qed.
Lemma lem3464627 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term56 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem3464628 {A : Type'} (p : A -> Prop) (x : A) : (term56 A x p) = (p x).
Proof. exact (@lem3464627 A p x). Qed.
Lemma lem3464629 {A : Type'} (P : A -> Prop) (x : A) : (term56 A x P) = (P x).
Proof. exact (@lem3464628 A P x). Qed.
Lemma lem3464630 {A : Type'} (P : A -> Prop) (x : A) : ((term66 A x P) = (term56 A x P)) = ((term76 A P x) = (P x)).
Proof. exact (MK_COMB (@lem3464625 A P x) (@lem3464629 A P x)). Qed.
Lemma lem3464633 {A : Type'} (P : A -> Prop) : (term78 A P) = (term79 A P).
Proof. exact (fun_ext (fun x : A => @lem3464630 A P x)). Qed.
Lemma lem3464634 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3464635 {A : Type'} (P : A -> Prop) : (term53 A P) = (term80 A P).
Proof. exact (MK_COMB (@lem3464634 A) (@lem3464633 A P)). Qed.
Lemma lem3464640 {A : Type'} : (term54 A) = (term81 A).
Proof. exact (fun_ext (fun P : A -> Prop => @lem3464635 A P)). Qed.
Lemma lem3464641 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3464642 {A : Type'} : (term55 A) = (term82 A).
Proof. exact (MK_COMB (@lem3464641 A) (@lem3464640 A)). Qed.
Lemma lem3464647 {A : Type'} : (term82 A) = (term55 A).
Proof. exact (SYM (@lem3464642 A)). Qed.
Lemma lem3464649 (p : Prop) : p = (term83 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3464650 {A : Type'} : (term82 A) = (term84 A).
Proof. exact (@lem3464649 (term82 A)). Qed.
Lemma lem3464651 {A : Type'} : (term84 A) = (term82 A).
Proof. exact (SYM (@lem3464650 A)). Qed.
Lemma lem3464652 {A : Type'} (h1 : term85 A) : term85 A.
Proof. exact (h1). Qed.
Lemma lem3464655 {A : Type'} (h1 : term84 A) : term84 A.
Proof. exact (h1). Qed.
Lemma lem3464656 {A : Type'} : term86 A.
Proof. exact (fun h0 : term84 A => @lem3464655 A h0). Qed.
Lemma lem3464657 {A : Type'} (h1 : term86 A) : term86 A.
Proof. exact (h1). Qed.
Lemma lem3464658 {A : Type'} (h1 : term84 A) : term84 A.
Proof. exact (h1). Qed.
Lemma lem3464659 {A : Type'} (h1 : term84 A) (h2 : term86 A) : term84 A.
Proof. exact (@lem3464657 A h2 (@lem3464658 A h1)). Qed.
Lemma lem3464660 {A : Type'} (h1 : term84 A) : term87 A.
Proof. exact (fun h0 : term86 A => @lem3464659 A h1 h0). Qed.
Lemma lem3464661 {A : Type'} (h1 : term86 A) : term86 A.
Proof. exact (h1). Qed.
Lemma lem3464662 {A : Type'} (h1 : term84 A) (h2 : term86 A) : term84 A.
Proof. exact (@lem3464660 A h1 (@lem3464661 A h2)). Qed.
Lemma lem3464663 {A : Type'} (h1 : term86 A) : term86 A.
Proof. exact (fun h0 : term84 A => @lem3464662 A h0 h1). Qed.
Lemma lem3464664 {A : Type'} : term88 A.
Proof. exact (fun h0 : term86 A => @lem3464663 A h0). Qed.
Lemma lem3464667 {A : Type'} : term86 A.
Proof. exact (@lem3464664 A (@lem3464656 A)). Qed.
Lemma lem3464668 {A : Type'} : term86 A.
Proof. exact (@lem3464667 A). Qed.
Lemma lem3464670 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3464671 {A : Type'} : (term84 A) = (term89 A).
Proof. exact (@lem3464670 (term85 A)). Qed.
Lemma lem3464673 (t : Prop) : (term90 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3464674 {A : Type'} : (term89 A) = (term82 A).
Proof. exact (@lem3464673 (term82 A)). Qed.
Lemma lem3464717 {A : Type'} : (term84 A) = (term82 A).
Proof. exact (TRANS (@lem3464671 A) (@lem3464674 A)). Qed.
Lemma lem3464718 {A : Type'} (P : A -> Prop) (x : A) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem3464723 {A : Type'} (P : A -> Prop) (x : A) (x' : A) : (term74 A P x x') = (term74 A P x x').
Proof. exact (eq_refl (term74 A P x x')). Qed.
Lemma lem3464724 {A : Type'} (P : A -> Prop) (x : A) : (term75 A P x) = (term75 A P x).
Proof. exact (fun_ext (fun x' : A => @lem3464723 A P x x')). Qed.
Lemma lem3464725 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3464726 {A : Type'} (P : A -> Prop) (x : A) : (term76 A P x) = (term76 A P x).
Proof. exact (MK_COMB (@lem3464725 A) (@lem3464724 A P x)). Qed.
Lemma lem3464727 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3464728 {A : Type'} (P : A -> Prop) (x : A) : (term77 A P x) = (term77 A P x).
Proof. exact (MK_COMB (@lem3464727) (@lem3464726 A P x)). Qed.
Lemma lem3464729 {A : Type'} (P : A -> Prop) (x : A) : ((term76 A P x) = (P x)) = ((term76 A P x) = (P x)).
Proof. exact (MK_COMB (@lem3464728 A P x) (@lem3464718 A P x)). Qed.
Lemma lem3464730 {A : Type'} (P : A -> Prop) : (term79 A P) = (term79 A P).
Proof. exact (fun_ext (fun x : A => @lem3464729 A P x)). Qed.
Lemma lem3464731 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3464732 {A : Type'} (P : A -> Prop) : (term80 A P) = (term80 A P).
Proof. exact (MK_COMB (@lem3464731 A) (@lem3464730 A P)). Qed.
Lemma lem3464733 {A : Type'} : (term81 A) = (term81 A).
Proof. exact (fun_ext (fun P : A -> Prop => @lem3464732 A P)). Qed.
Lemma lem3464734 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3464735 {A : Type'} : (term82 A) = (term82 A).
Proof. exact (MK_COMB (@lem3464734 A) (@lem3464733 A)). Qed.
Lemma lem3464758 {A : Type'} : (term84 A) = (term82 A).
Proof. exact (TRANS (@lem3464717 A) (@lem3464735 A)). Qed.
Lemma lem3464759 {A : Type'} : (term82 A) = (term84 A).
Proof. exact (SYM (@lem3464758 A)). Qed.
Lemma lem3464761 (p : Prop) : p = (term83 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3464762 {A : Type'} (P : A -> Prop) (x : A) : ((term76 A P x) = (P x)) = (term91 A P x).
Proof. exact (@lem3464761 ((term76 A P x) = (P x))). Qed.
Lemma lem3464763 {A : Type'} (P : A -> Prop) (x : A) : (term91 A P x) = ((term76 A P x) = (P x)).
Proof. exact (SYM (@lem3464762 A P x)). Qed.
Lemma lem3464764 {A : Type'} (P : A -> Prop) (x : A) (h1 : term92 A P x) : term92 A P x.
Proof. exact (h1). Qed.
Lemma lem3464773 {A : Type'} (P : A -> Prop) (x : A) (x' : A) : (term93 A P x x') = (term94 A P x x').
Proof. exact (@lem17045 (P x') (x = x')). Qed.
Lemma lem3464776 {A : Type'} (P : A -> Prop) (x : A) (x' : A) : (term74 A P x x') = (term74 A P x x').
Proof. exact (eq_refl (term74 A P x x')). Qed.
Lemma lem3464777 {A : Type'} (P : A -> Prop) : (term95 A P) = (term96 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem3464778 {A : Type'} (P : A -> Prop) (x : A) : (term97 A P x) = (term98 A P x).
Proof. exact (@lem3464777 A (term75 A P x)). Qed.
Lemma lem3464779 {A : Type'} (P : A -> Prop) (x : A) (x' : A) : (term99 A P x x') = (term74 A P x x').
Proof. exact (eq_refl (term99 A P x x')). Qed.
Lemma lem3464780 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3464781 {A : Type'} (P : A -> Prop) (x : A) (x' : A) : (term100 A P x x') = (term93 A P x x').
Proof. exact (MK_COMB (@lem3464780) (@lem3464779 A P x x')). Qed.
Lemma lem3464782 {A : Type'} (P : A -> Prop) (x : A) (x' : A) : (term100 A P x x') = (term94 A P x x').
Proof. exact (TRANS (@lem3464781 A P x x') (@lem3464773 A P x x')). Qed.
Lemma lem3464783 {A : Type'} (P : A -> Prop) (x : A) : (term101 A P x) = (term102 A P x).
Proof. exact (fun_ext (fun x' : A => @lem3464782 A P x x')). Qed.
Lemma lem3464784 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3464785 {A : Type'} (P : A -> Prop) (x : A) : (term98 A P x) = (term103 A P x).
Proof. exact (MK_COMB (@lem3464784 A) (@lem3464783 A P x)). Qed.
Lemma lem3464786 {A : Type'} (P : A -> Prop) (x : A) : (term97 A P x) = (term103 A P x).
Proof. exact (TRANS (@lem3464778 A P x) (@lem3464785 A P x)). Qed.
Lemma lem3464787 {A : Type'} (P : A -> Prop) (x : A) : (term75 A P x) = (term75 A P x).
Proof. exact (fun_ext (fun x' : A => @lem3464776 A P x x')). Qed.
Lemma lem3464788 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3464789 {A : Type'} (P : A -> Prop) (x : A) : (term76 A P x) = (term76 A P x).
Proof. exact (MK_COMB (@lem3464788 A) (@lem3464787 A P x)). Qed.
Lemma lem3464790 {A : Type'} (P : A -> Prop) (x : A) : (term104 A P x) = (term104 A P x).
Proof. exact (eq_refl (term104 A P x)). Qed.
Lemma lem3464791 {A : Type'} (P : A -> Prop) (x : A) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem3464792 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3464793 {A : Type'} (P : A -> Prop) (x : A) : (term105 A P x) = (term106 A P x).
Proof. exact (MK_COMB (@lem3464792) (@lem3464786 A P x)). Qed.
Lemma lem3464794 {A : Type'} (P : A -> Prop) (x : A) : (term107 A P x) = (term108 A P x).
Proof. exact (MK_COMB (@lem3464793 A P x) (@lem3464791 A P x)). Qed.
Lemma lem3464795 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3464796 {A : Type'} (P : A -> Prop) (x : A) : (term109 A P x) = (term109 A P x).
Proof. exact (MK_COMB (@lem3464795) (@lem3464789 A P x)). Qed.
Lemma lem3464797 {A : Type'} (P : A -> Prop) (x : A) : (term110 A P x) = (term110 A P x).
Proof. exact (MK_COMB (@lem3464796 A P x) (@lem3464790 A P x)). Qed.
Lemma lem3464798 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3464799 {A : Type'} (P : A -> Prop) (x : A) : (term111 A P x) = (term111 A P x).
Proof. exact (MK_COMB (@lem3464798) (@lem3464797 A P x)). Qed.
Lemma lem3464800 {A : Type'} (P : A -> Prop) (x : A) : (term112 A P x) = (term113 A P x).
Proof. exact (MK_COMB (@lem3464799 A P x) (@lem3464794 A P x)). Qed.
Lemma lem3464801 {A : Type'} (P : A -> Prop) (x : A) : (term92 A P x) = (term112 A P x).
Proof. exact (@lem17646 (term76 A P x) (P x)). Qed.
Lemma lem3464802 {A : Type'} (P : A -> Prop) (x : A) : (term92 A P x) = (term113 A P x).
Proof. exact (TRANS (@lem3464801 A P x) (@lem3464800 A P x)). Qed.
Lemma lem3464881 {A : Type'} (P : A -> Prop) (Q : Prop) : (term114 A P Q) = (term115 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3464882 {A : Type'} (P : A -> Prop) (Q : Prop) : (term114 A P Q) = (term115 A P Q).
Proof. exact (@lem3464881 A P Q). Qed.
Lemma lem3464883 {A : Type'} (P : A -> Prop) (x : A) : (term116 A P x) = (term117 A P x).
Proof. exact (@lem3464882 A (term75 A P x) (term104 A P x)). Qed.
Lemma lem3464884 {A : Type'} (P : A -> Prop) (x : A) (x' : A) : (term99 A P x x') = (term74 A P x x').
Proof. exact (eq_refl (term99 A P x x')). Qed.
Lemma lem3464885 {A : Type'} (P : A -> Prop) (x : A) : (term118 A P x) = (term75 A P x).
Proof. exact (fun_ext (fun x' : A => @lem3464884 A P x x')). Qed.
Lemma lem3464886 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3464887 {A : Type'} (P : A -> Prop) (x : A) : (term119 A P x) = (term76 A P x).
Proof. exact (MK_COMB (@lem3464886 A) (@lem3464885 A P x)). Qed.
Lemma lem3464888 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3464889 {A : Type'} (P : A -> Prop) (x : A) : (term120 A P x) = (term109 A P x).
Proof. exact (MK_COMB (@lem3464888) (@lem3464887 A P x)). Qed.
Lemma lem3464890 {A : Type'} (P : A -> Prop) (x : A) : (term104 A P x) = (term104 A P x).
Proof. exact (eq_refl (term104 A P x)). Qed.
Lemma lem3464891 {A : Type'} (P : A -> Prop) (x : A) : (term116 A P x) = (term110 A P x).
Proof. exact (MK_COMB (@lem3464889 A P x) (@lem3464890 A P x)). Qed.
Lemma lem3464892 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3464893 {A : Type'} (P : A -> Prop) (x : A) : (term121 A P x) = (term122 A P x).
Proof. exact (MK_COMB (@lem3464892) (@lem3464891 A P x)). Qed.
Lemma lem3464894 {A : Type'} (P : A -> Prop) (x : A) (x' : A) : (term99 A P x x') = (term74 A P x x').
Proof. exact (eq_refl (term99 A P x x')). Qed.
Lemma lem3464895 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3464896 {A : Type'} (P : A -> Prop) (x : A) (x' : A) : (term123 A P x x') = (term124 A P x x').
Proof. exact (MK_COMB (@lem3464895) (@lem3464894 A P x x')). Qed.
Lemma lem3464897 {A : Type'} (P : A -> Prop) (x : A) : (term104 A P x) = (term104 A P x).
Proof. exact (eq_refl (term104 A P x)). Qed.
Lemma lem3464898 {A : Type'} (x' : A) (P : A -> Prop) (x : A) : (term125 A x' P x) = (term126 A x' P x).
Proof. exact (MK_COMB (@lem3464896 A P x x') (@lem3464897 A P x)). Qed.
Lemma lem3464899 {A : Type'} (P : A -> Prop) (x : A) : (term127 A P x) = (term128 A P x).
Proof. exact (fun_ext (fun x' : A => @lem3464898 A x' P x)). Qed.
Lemma lem3464900 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3464901 {A : Type'} (P : A -> Prop) (x : A) : (term117 A P x) = (term129 A P x).
Proof. exact (MK_COMB (@lem3464900 A) (@lem3464899 A P x)). Qed.
Lemma lem3464902 {A : Type'} (P : A -> Prop) (x : A) : ((term116 A P x) = (term117 A P x)) = ((term110 A P x) = (term129 A P x)).
Proof. exact (MK_COMB (@lem3464893 A P x) (@lem3464901 A P x)). Qed.
Lemma lem3464903 {A : Type'} (P : A -> Prop) (x : A) : (term110 A P x) = (term129 A P x).
Proof. exact (EQ_MP (@lem3464902 A P x) (@lem3464883 A P x)). Qed.
Lemma lem3464904 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3464905 {A : Type'} (P : A -> Prop) (x : A) : (term111 A P x) = (term130 A P x).
Proof. exact (MK_COMB (@lem3464904) (@lem3464903 A P x)). Qed.
Lemma lem3464906 {A : Type'} (P : A -> Prop) (x : A) : (term108 A P x) = (term108 A P x).
Proof. exact (eq_refl (term108 A P x)). Qed.
Lemma lem3464907 {A : Type'} (P : A -> Prop) (x : A) : (term113 A P x) = (term131 A P x).
Proof. exact (MK_COMB (@lem3464905 A P x) (@lem3464906 A P x)). Qed.
Lemma lem3464909 {A : Type'} (P : A -> Prop) (Q : Prop) : (term132 A P Q) = (term133 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3464910 {A : Type'} (P : A -> Prop) (Q : Prop) : (term132 A P Q) = (term133 A P Q).
Proof. exact (@lem3464909 A P Q). Qed.
Lemma lem3464911 {A : Type'} (P : A -> Prop) (x : A) : (term134 A P x) = (term135 A P x).
Proof. exact (@lem3464910 A (term128 A P x) (term108 A P x)). Qed.
Lemma lem3464912 {A : Type'} (x' : A) (P : A -> Prop) (x : A) : (term136 A P x x') = (term126 A x' P x).
Proof. exact (eq_refl (term136 A P x x')). Qed.
Lemma lem3464913 {A : Type'} (P : A -> Prop) (x : A) : (term137 A P x) = (term128 A P x).
Proof. exact (fun_ext (fun x' : A => @lem3464912 A x' P x)). Qed.
Lemma lem3464914 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3464915 {A : Type'} (P : A -> Prop) (x : A) : (term138 A P x) = (term129 A P x).
Proof. exact (MK_COMB (@lem3464914 A) (@lem3464913 A P x)). Qed.
Lemma lem3464916 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3464917 {A : Type'} (P : A -> Prop) (x : A) : (term139 A P x) = (term130 A P x).
Proof. exact (MK_COMB (@lem3464916) (@lem3464915 A P x)). Qed.
Lemma lem3464918 {A : Type'} (P : A -> Prop) (x : A) : (term108 A P x) = (term108 A P x).
Proof. exact (eq_refl (term108 A P x)). Qed.
Lemma lem3464919 {A : Type'} (P : A -> Prop) (x : A) : (term134 A P x) = (term131 A P x).
Proof. exact (MK_COMB (@lem3464917 A P x) (@lem3464918 A P x)). Qed.
Lemma lem3464920 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3464921 {A : Type'} (P : A -> Prop) (x : A) : (term140 A P x) = (term141 A P x).
Proof. exact (MK_COMB (@lem3464920) (@lem3464919 A P x)). Qed.
Lemma lem3464922 {A : Type'} (x' : A) (P : A -> Prop) (x : A) : (term136 A P x x') = (term126 A x' P x).
Proof. exact (eq_refl (term136 A P x x')). Qed.
Lemma lem3464923 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3464924 {A : Type'} (x' : A) (P : A -> Prop) (x : A) : (term142 A P x x') = (term143 A x' P x).
Proof. exact (MK_COMB (@lem3464923) (@lem3464922 A x' P x)). Qed.
Lemma lem3464925 {A : Type'} (P : A -> Prop) (x : A) : (term108 A P x) = (term108 A P x).
Proof. exact (eq_refl (term108 A P x)). Qed.
Lemma lem3464926 {A : Type'} (x' : A) (P : A -> Prop) (x : A) : (term144 A x' P x) = (term145 A x' P x).
Proof. exact (MK_COMB (@lem3464924 A x' P x) (@lem3464925 A P x)). Qed.
Lemma lem3464927 {A : Type'} (P : A -> Prop) (x : A) : (term146 A P x) = (term147 A P x).
Proof. exact (fun_ext (fun x' : A => @lem3464926 A x' P x)). Qed.
Lemma lem3464928 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3464929 {A : Type'} (P : A -> Prop) (x : A) : (term135 A P x) = (term148 A P x).
Proof. exact (MK_COMB (@lem3464928 A) (@lem3464927 A P x)). Qed.
Lemma lem3464930 {A : Type'} (P : A -> Prop) (x : A) : ((term134 A P x) = (term135 A P x)) = ((term131 A P x) = (term148 A P x)).
Proof. exact (MK_COMB (@lem3464921 A P x) (@lem3464929 A P x)). Qed.
Lemma lem3464931 {A : Type'} (P : A -> Prop) (x : A) : (term131 A P x) = (term148 A P x).
Proof. exact (EQ_MP (@lem3464930 A P x) (@lem3464911 A P x)). Qed.
Lemma lem3464933 {A : Type'} (P : A -> Prop) (x : A) : (term113 A P x) = (term148 A P x).
Proof. exact (TRANS (@lem3464907 A P x) (@lem3464931 A P x)). Qed.
Lemma lem3464934 {A : Type'} (P : A -> Prop) (x : A) : (term92 A P x) = (term148 A P x).
Proof. exact (TRANS (@lem3464802 A P x) (@lem3464933 A P x)). Qed.
Lemma lem3464935 {A : Type'} (P : A -> Prop) (x : A) (h1 : term92 A P x) : term148 A P x.
Proof. exact (EQ_MP (@lem3464934 A P x) (@lem3464764 A P x h1)). Qed.
Lemma lem3464936 {A : Type'} (x' : A) (P : A -> Prop) (x : A) (h1 : term145 A x' P x) : term145 A x' P x.
Proof. exact (h1). Qed.
Lemma lem3464939 {A : Type'} (P : A -> Prop) (x : A) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem3464954 {A : Type'} (P : A -> Prop) (x : A) (x' : A) : (term94 A P x x') = (term94 A P x x').
Proof. exact (eq_refl (term94 A P x x')). Qed.
Lemma lem3464955 {A : Type'} (P : A -> Prop) (x : A) : (term102 A P x) = (term102 A P x).
Proof. exact (fun_ext (fun x' : A => @lem3464954 A P x x')). Qed.
Lemma lem3464956 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3464957 {A : Type'} (P : A -> Prop) (x : A) : (term103 A P x) = (term103 A P x).
Proof. exact (MK_COMB (@lem3464956 A) (@lem3464955 A P x)). Qed.
Lemma lem3464958 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3464959 {A : Type'} (P : A -> Prop) (x : A) : (term106 A P x) = (term106 A P x).
Proof. exact (MK_COMB (@lem3464958) (@lem3464957 A P x)). Qed.
Lemma lem3464960 {A : Type'} (P : A -> Prop) (x : A) : (term108 A P x) = (term108 A P x).
Proof. exact (MK_COMB (@lem3464959 A P x) (@lem3464939 A P x)). Qed.
Lemma lem3464981 {A : Type'} (x' : A) (P : A -> Prop) (x : A) : (term143 A x' P x) = (term143 A x' P x).
Proof. exact (eq_refl (term143 A x' P x)). Qed.
Lemma lem3464982 {A : Type'} (x' : A) (P : A -> Prop) (x : A) : (term145 A x' P x) = (term145 A x' P x).
Proof. exact (MK_COMB (@lem3464981 A x' P x) (@lem3464960 A P x)). Qed.
Lemma lem3464983 {A : Type'} (x' : A) (P : A -> Prop) (x : A) (h1 : term145 A x' P x) : term145 A x' P x.
Proof. exact (EQ_MP (@lem3464982 A x' P x) (@lem3464936 A x' P x h1)). Qed.
Lemma lem3464984 {A : Type'} (x' : A) (P : A -> Prop) (x : A) (h1 : term126 A x' P x) : term126 A x' P x.
Proof. exact (h1). Qed.
Lemma lem3464985 {A : Type'} (P : A -> Prop) (x : A) (h1 : term108 A P x) : term108 A P x.
Proof. exact (h1). Qed.
Lemma lem3464987 {A : Type'} (x' : A) (P : A -> Prop) (x : A) (h1 : term126 A x' P x) : term74 A P x x'.
Proof. exact (proj1 (@lem3464984 A x' P x h1)). Qed.
Lemma lem3464991 {A : Type'} (P : A -> Prop) (x : A) (h1 : term108 A P x) : term103 A P x.
Proof. exact (proj1 (@lem3464985 A P x h1)). Qed.
Lemma lem3465011 {A : Type'} (P : A -> Prop) (x : A) (x' : A) : (term94 A P x x') = (term94 A P x x').
Proof. exact (eq_refl (term94 A P x x')). Qed.
Lemma lem3465012 {A : Type'} (P : A -> Prop) (x : A) : (term102 A P x) = (term102 A P x).
Proof. exact (fun_ext (fun x' : A => @lem3465011 A P x x')). Qed.
Lemma lem3465013 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3465015 {A : Type'} (P : A -> Prop) (x : A) : (term103 A P x) = (term103 A P x).
Proof. exact (MK_COMB (@lem3465013 A) (@lem3465012 A P x)). Qed.
Lemma lem3465016 {A : Type'} (P : A -> Prop) (x : A) (h1 : term108 A P x) : term103 A P x.
Proof. exact (EQ_MP (@lem3465015 A P x) (@lem3464991 A P x h1)). Qed.
Lemma lem3465021 {A : Type'} (_36595 : A) (P : A -> Prop) (x : A) (h1 : term108 A P x) : term149 A P x _36595.
Proof. exact (@lem3465016 A P x h1 _36595). Qed.
Lemma lem3465022 {A : Type'} (P : A -> Prop) (x : A) (_36595 : A) : (term149 A P x _36595) = (term94 A P x _36595).
Proof. exact (eq_refl (term149 A P x _36595)). Qed.
Lemma lem3465025 {A : Type'} (x' : A) (P : A -> Prop) (x : A) (h1 : term126 A x' P x) : term104 A P x.
Proof. exact (proj2 (@lem3464984 A x' P x h1)). Qed.
Lemma lem3465029 {A : Type'} (x' : A) (P : A -> Prop) (x : A) (h1 : term126 A x' P x) : x = x'.
Proof. exact (proj2 (@lem3464987 A x' P x h1)). Qed.
Lemma lem3465035 {A : Type'} (_36595 : A) (P : A -> Prop) (x : A) (h1 : term108 A P x) : term94 A P x _36595.
Proof. exact (EQ_MP (@lem3465022 A P x _36595) (@lem3465021 A _36595 P x h1)). Qed.
Lemma lem3465052 {A : Type'} (P : A -> Prop) : (term150 A P) = (term150 A P).
Proof. exact (eq_refl (term150 A P)). Qed.
Lemma lem3465053 {A : Type'} (x' : A) (P : A -> Prop) (x : A) (h1 : term126 A x' P x) : (term151 A P x) = (term151 A P x').
Proof. exact (MK_COMB (@lem3465052 A P) (@lem3465029 A x' P x h1)). Qed.
Lemma lem3465054 {A : Type'} (P : A -> Prop) (x' : A) : (term151 A P x') = (term104 A P x').
Proof. exact (eq_refl (term151 A P x')). Qed.
Lemma lem3465055 {A : Type'} (P : A -> Prop) (x : A) : (term152 A P x) = (term152 A P x).
Proof. exact (eq_refl (term152 A P x)). Qed.
Lemma lem3465056 {A : Type'} (x : A) (P : A -> Prop) (x' : A) : ((term151 A P x) = (term151 A P x')) = ((term151 A P x) = (term104 A P x')).
Proof. exact (MK_COMB (@lem3465055 A P x) (@lem3465054 A P x')). Qed.
Lemma lem3465057 {A : Type'} (P : A -> Prop) (x : A) : (term151 A P x) = (term104 A P x).
Proof. exact (eq_refl (term151 A P x)). Qed.
Lemma lem3465058 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3465059 {A : Type'} (P : A -> Prop) (x : A) : (term152 A P x) = (term153 A P x).
Proof. exact (MK_COMB (@lem3465058) (@lem3465057 A P x)). Qed.
Lemma lem3465060 {A : Type'} (P : A -> Prop) (x' : A) : (term104 A P x') = (term104 A P x').
Proof. exact (eq_refl (term104 A P x')). Qed.
Lemma lem3465061 {A : Type'} (x : A) (P : A -> Prop) (x' : A) : ((term151 A P x) = (term104 A P x')) = ((term104 A P x) = (term104 A P x')).
Proof. exact (MK_COMB (@lem3465059 A P x) (@lem3465060 A P x')). Qed.
Lemma lem3465062 {A : Type'} (x : A) (P : A -> Prop) (x' : A) : ((term151 A P x) = (term151 A P x')) = ((term104 A P x) = (term104 A P x')).
Proof. exact (TRANS (@lem3465056 A x P x') (@lem3465061 A x P x')). Qed.
Lemma lem3465063 {A : Type'} (x' : A) (P : A -> Prop) (x : A) (h1 : term126 A x' P x) : (term104 A P x) = (term104 A P x').
Proof. exact (EQ_MP (@lem3465062 A x P x') (@lem3465053 A x' P x h1)). Qed.
Lemma lem3465064 {A : Type'} (x' : A) (P : A -> Prop) (x : A) (h1 : term126 A x' P x) : term104 A P x'.
Proof. exact (EQ_MP (@lem3465063 A x' P x h1) (@lem3465025 A x' P x h1)). Qed.
Lemma lem3465080 {A : Type'} (x' : A) (P : A -> Prop) (x : A) (h1 : term126 A x' P x) : P x'.
Proof. exact (proj1 (@lem3464987 A x' P x h1)). Qed.
Lemma lem3465081 {A : Type'} (x' : A) (P : A -> Prop) (x : A) (h1 : term126 A x' P x) : term154 A P x'.
Proof. exact (fun h0 : term104 A P x' => @lem3465080 A x' P x h1). Qed.
Lemma lem3465083 (p : Prop) : (term155 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3465084 {A : Type'} (P : A -> Prop) (x' : A) : (term154 A P x') = (P x').
Proof. exact (@lem3465083 (P x')). Qed.
Lemma lem3465085 {A : Type'} (x' : A) (P : A -> Prop) (x : A) (h1 : term126 A x' P x) : P x'.
Proof. exact (EQ_MP (@lem3465084 A P x') (@lem3465081 A x' P x h1)). Qed.
Lemma lem3465088 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3465090 {A : Type'} (P : A -> Prop) (x' : A) : (term104 A P x') = (term156 A P x').
Proof. exact (@lem3465088 (P x')). Qed.
Lemma lem3465093 {A : Type'} (x' : A) (P : A -> Prop) (x : A) (h1 : term126 A x' P x) : term156 A P x'.
Proof. exact (EQ_MP (@lem3465090 A P x') (@lem3465064 A x' P x h1)). Qed.
Lemma lem3465096 {A : Type'} (x' : A) (P : A -> Prop) (x : A) (h1 : term126 A x' P x) : False.
Proof. exact (@lem3465093 A x' P x h1 (@lem3465085 A x' P x h1)). Qed.
Lemma lem3465097 {A : Type'} (x' : A) (P : A -> Prop) (x : A) (h1 : term126 A x' P x) : term157.
Proof. exact (fun h0 : ~ False => @lem3465096 A x' P x h1). Qed.
Lemma lem3465099 (p : Prop) : (term155 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3465100 : term157 = False.
Proof. exact (@lem3465099 False). Qed.
Lemma lem3465117 {A : Type'} (P : A -> Prop) (x : A) (h1 : term108 A P x) : P x.
Proof. exact (proj2 (@lem3464985 A P x h1)). Qed.
Lemma lem3465118 {A : Type'} (P : A -> Prop) (x : A) (h1 : term108 A P x) : term154 A P x.
Proof. exact (fun h0 : term104 A P x => @lem3465117 A P x h1). Qed.
Lemma lem3465120 (p : Prop) : (term155 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3465121 {A : Type'} (P : A -> Prop) (x : A) : (term154 A P x) = (P x).
Proof. exact (@lem3465120 (P x)). Qed.
Lemma lem3465122 {A : Type'} (P : A -> Prop) (x : A) (h1 : term108 A P x) : P x.
Proof. exact (EQ_MP (@lem3465121 A P x) (@lem3465118 A P x h1)). Qed.
Lemma lem3465124 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3465125 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3465124 A x). Qed.
Lemma lem3465126 {A : Type'} (x : A) : term158 A x.
Proof. exact (fun h0 : term159 A x => @lem3465125 A x). Qed.
Lemma lem3465128 (p : Prop) : (term155 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3465129 {A : Type'} (x : A) : (term158 A x) = (x = x).
Proof. exact (@lem3465128 (x = x)). Qed.
Lemma lem3465130 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem3465129 A x) (@lem3465126 A x)). Qed.
Lemma lem3465132 (a : Prop) (b : Prop) : (term160 a b) = (term161 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3465133 {A : Type'} (P : A -> Prop) (x : A) (_36595 : A) : (term94 A P x _36595) = (term93 A P x _36595).
Proof. exact (@lem3465132 (P _36595) (x = _36595)). Qed.
Lemma lem3465135 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3465136 {A : Type'} (P : A -> Prop) (x : A) (_36595 : A) : (term93 A P x _36595) = (term162 A P x _36595).
Proof. exact (@lem3465135 (term74 A P x _36595)). Qed.
Lemma lem3465137 {A : Type'} (P : A -> Prop) (x : A) (_36595 : A) : (term94 A P x _36595) = (term162 A P x _36595).
Proof. exact (TRANS (@lem3465133 A P x _36595) (@lem3465136 A P x _36595)). Qed.
Lemma lem3465139 {A : Type'} (P : A -> Prop) (x : A) (h1 : term108 A P x) : term163 A P x.
Proof. exact (conj (@lem3465122 A P x h1) (@lem3465130 A x)). Qed.
Lemma lem3465141 {A : Type'} (_36595 : A) (P : A -> Prop) (x : A) (h1 : term108 A P x) : term162 A P x _36595.
Proof. exact (EQ_MP (@lem3465137 A P x _36595) (@lem3465035 A _36595 P x h1)). Qed.
Lemma lem3465142 {A : Type'} (_36595 : A) (P : A -> Prop) (x : A) (h1 : term108 A P x) : term162 A P x _36595.
Proof. exact (@lem3465141 A _36595 P x h1). Qed.
Lemma lem3465143 {A : Type'} (P : A -> Prop) (x : A) (h1 : term108 A P x) : term164 A P x.
Proof. exact (@lem3465142 A x P x h1). Qed.
Lemma lem3465146 {A : Type'} (P : A -> Prop) (x : A) (h1 : term108 A P x) : False.
Proof. exact (@lem3465143 A P x h1 (@lem3465139 A P x h1)). Qed.
Lemma lem3465147 {A : Type'} (P : A -> Prop) (x : A) (h1 : term108 A P x) : term157.
Proof. exact (fun h0 : ~ False => @lem3465146 A P x h1). Qed.
Lemma lem3465149 (p : Prop) : (term155 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3465150 : term157 = False.
Proof. exact (@lem3465149 False). Qed.
Lemma lem3465151 {A : Type'} (P : A -> Prop) (x : A) (h1 : term108 A P x) : False.
Proof. exact (EQ_MP (@lem3465150) (@lem3465147 A P x h1)). Qed.
Lemma lem3465152 {A : Type'} (x' : A) (P : A -> Prop) (x : A) (h1 : term126 A x' P x) : False.
Proof. exact (EQ_MP (@lem3465100) (@lem3465097 A x' P x h1)). Qed.
Lemma lem3465153 {A : Type'} (x' : A) (P : A -> Prop) (x : A) (h1 : term145 A x' P x) : False.
Proof. exact (or_elim (@lem3464983 A x' P x h1) (fun h0 : term126 A x' P x => @lem3465152 A x' P x h0) (fun h0 : term108 A P x => @lem3465151 A P x h0)). Qed.
Lemma lem3465154 {A : Type'} (x' : A) (P : A -> Prop) (x : A) (h1 : term145 A x' P x) : (term145 A x' P x) = False.
Proof. exact (prop_ext (fun h2 : term145 A x' P x => @lem3465153 A x' P x h1) (fun h2 : False => @lem3464983 A x' P x h1)). Qed.
Lemma lem3465155 {A : Type'} (x' : A) (P : A -> Prop) (x : A) (h1 : term145 A x' P x) : False.
Proof. exact (EQ_MP (@lem3465154 A x' P x h1) (@lem3464983 A x' P x h1)). Qed.
Lemma lem3465156 {A : Type'} (P : A -> Prop) (x : A) (h1 : term92 A P x) : False.
Proof. exact (ex_elim (@lem3464935 A P x h1) (fun x' : A => fun h0 : term147 A P x x' => @lem3465155 A x' P x h0)). Qed.
Lemma lem3465157 {A : Type'} (P : A -> Prop) (x : A) (h1 : term92 A P x) : (term92 A P x) = False.
Proof. exact (prop_ext (fun h2 : term92 A P x => @lem3465156 A P x h1) (fun h2 : False => @lem3464764 A P x h1)). Qed.
Lemma lem3465158 {A : Type'} (P : A -> Prop) (x : A) (h1 : term92 A P x) : False.
Proof. exact (EQ_MP (@lem3465157 A P x h1) (@lem3464764 A P x h1)). Qed.
Lemma lem3465159 {A : Type'} (P : A -> Prop) (x : A) : term91 A P x.
Proof. exact (fun h0 : term92 A P x => @lem3465158 A P x h0). Qed.
Lemma lem3465160 {A : Type'} (P : A -> Prop) (x : A) : (term76 A P x) = (P x).
Proof. exact (EQ_MP (@lem3464763 A P x) (@lem3465159 A P x)). Qed.
Lemma lem3465165 {A : Type'} (P : A -> Prop) : term80 A P.
Proof. exact (fun x : A => @lem3465160 A P x). Qed.
Lemma lem3465170 {A : Type'} : term82 A.
Proof. exact (fun P : A -> Prop => @lem3465165 A P). Qed.
Lemma lem3465171 {A : Type'} : term84 A.
Proof. exact (EQ_MP (@lem3464759 A) (@lem3465170 A)). Qed.
Lemma lem3465173 {A : Type'} : term84 A.
Proof. exact (@lem3464668 A (@lem3465171 A)). Qed.
Lemma lem3465174 {A : Type'} (h1 : term85 A) : False.
Proof. exact (@lem3465173 A (@lem3464652 A h1)). Qed.
Lemma lem3465175 {A : Type'} (h1 : term85 A) : (term85 A) = False.
Proof. exact (prop_ext (fun h2 : term85 A => @lem3465174 A h1) (fun h2 : False => @lem3464652 A h1)). Qed.
Lemma lem3465176 {A : Type'} (h1 : term85 A) : False.
Proof. exact (EQ_MP (@lem3465175 A h1) (@lem3464652 A h1)). Qed.
Lemma lem3465177 {A : Type'} : term84 A.
Proof. exact (fun h0 : term85 A => @lem3465176 A h0). Qed.
Lemma lem3465178 {A : Type'} : term82 A.
Proof. exact (EQ_MP (@lem3464651 A) (@lem3465177 A)). Qed.
Lemma lem3465179 {A : Type'} : term55 A.
Proof. exact (EQ_MP (@lem3464647 A) (@lem3465178 A)). Qed.
Lemma lem3465180 {A : Type'} : term51 A.
Proof. exact (EQ_MP (@lem3464553 A) (@lem3465179 A)). Qed.
Lemma lem3465181 {A : Type'} : term50 A.
Proof. exact (EQ_MP (@lem3464513 A) (@lem3465180 A)). Qed.
