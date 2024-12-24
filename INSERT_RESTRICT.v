Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INSERT_RESTRICT_term_abbrevs.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm13473_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17646_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211640_spec.
Require Import thm3211641_spec.
Require Import thm3211692_spec.
Require Import thm3211693_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3213432 {A : Type'} (_474 : A -> Prop) (_475 : Prop) (_476 : type686 A) (_477 : A -> Prop) : (term0 A _476 _475 _474 _477) = (term1 A _474 _475 _476 _477).
Proof. exact (@lem13473 (A -> Prop) _474 _475 _476 _477). Qed.
Lemma lem3213433 {A : Type'} (_474 : A -> Prop) (_475 : Prop) (a : A) (s : A -> Prop) (P : A -> Prop) (_477 : A -> Prop) : (term2 A a s P _475 _474 _477) = (term3 A _474 _475 a s P _477).
Proof. exact (@lem3213432 A _474 _475 (term4 A a s P) _477). Qed.
Lemma lem3213434 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : (term5 A a s P) = (term6 A a s P).
Proof. exact (@lem3213433 A (term7 A a s P) (P a) a s P (term8 A s P)). Qed.
Lemma lem3213435 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : (term9 A a s P) = ((term10 A a s P) = (term8 A s P)).
Proof. exact (eq_refl (term9 A a s P)). Qed.
Lemma lem3213436 {A : Type'} (P : A -> Prop) (a : A) : (term11 A P a) = (term11 A P a).
Proof. exact (eq_refl (term11 A P a)). Qed.
Lemma lem3213437 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : (term12 A a s P) = (term13 A a s P).
Proof. exact (MK_COMB (@lem3213436 A P a) (@lem3213435 A a s P)). Qed.
Lemma lem3213438 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : (term14 A a s P) = ((term10 A a s P) = (term7 A a s P)).
Proof. exact (eq_refl (term14 A a s P)). Qed.
Lemma lem3213439 {A : Type'} (P : A -> Prop) (a : A) : (term15 A P a) = (term15 A P a).
Proof. exact (eq_refl (term15 A P a)). Qed.
Lemma lem3213440 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : (term16 A a s P) = (term17 A a s P).
Proof. exact (MK_COMB (@lem3213439 A P a) (@lem3213438 A a s P)). Qed.
Lemma lem3213441 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3213442 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : (term18 A a s P) = (term19 A a s P).
Proof. exact (MK_COMB (@lem3213441) (@lem3213440 A a s P)). Qed.
Lemma lem3213443 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : (term6 A a s P) = (term20 A a s P).
Proof. exact (MK_COMB (@lem3213442 A a s P) (@lem3213437 A a s P)). Qed.
Lemma lem3213444 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : (term5 A a s P) = ((term10 A a s P) = (term21 A a s P)).
Proof. exact (eq_refl (term5 A a s P)). Qed.
Lemma lem3213445 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3213446 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : (term22 A a s P) = (term23 A a s P).
Proof. exact (MK_COMB (@lem3213445) (@lem3213444 A a s P)). Qed.
Lemma lem3213447 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : ((term5 A a s P) = (term6 A a s P)) = (((term10 A a s P) = (term21 A a s P)) = (term20 A a s P)).
Proof. exact (MK_COMB (@lem3213446 A a s P) (@lem3213443 A a s P)). Qed.
Lemma lem3213448 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : ((term10 A a s P) = (term21 A a s P)) = (term20 A a s P).
Proof. exact (EQ_MP (@lem3213447 A a s P) (@lem3213434 A a s P)). Qed.
Lemma lem3213449 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : (term20 A a s P) = ((term10 A a s P) = (term21 A a s P)).
Proof. exact (SYM (@lem3213448 A a s P)). Qed.
Lemma lem3213450 {A : Type'} (P : A -> Prop) (a : A) (h1 : P a) : P a.
Proof. exact (h1). Qed.
Lemma lem3213467 {A : Type'} (P : A -> Prop) (a : A) (h1 : term24 A P a) : term24 A P a.
Proof. exact (h1). Qed.
Lemma lem3213499 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term25 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3213500 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term25 A s t).
Proof. exact (@lem3213499 A s t). Qed.
Lemma lem3213501 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : ((term10 A a s P) = (term7 A a s P)) = (term26 A a s P).
Proof. exact (@lem3213500 A (term10 A a s P) (term7 A a s P)). Qed.
Lemma lem3213522 {A : Type'} (P : A -> Prop) (a : A) : (term15 A P a) = (term15 A P a).
Proof. exact (eq_refl (term15 A P a)). Qed.
Lemma lem3213523 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : (term17 A a s P) = (term27 A a s P).
Proof. exact (MK_COMB (@lem3213522 A P a) (@lem3213501 A a s P)). Qed.
Lemma lem3213526 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : (term27 A a s P) = (term17 A a s P).
Proof. exact (SYM (@lem3213523 A a s P)). Qed.
Lemma lem3213536 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term28 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem3213537 {A : Type'} (p : A -> Prop) (x : A) : (term28 A x p) = (p x).
Proof. exact (@lem3213536 A p x). Qed.
Lemma lem3213538 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term29 A x a s P) = (term30 A a s P x).
Proof. exact (@lem3213537 A (term31 A a s P) x). Qed.
Lemma lem3213539 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term30 A a s P x) = (term32 A a s P x).
Proof. exact (eq_refl (term30 A a s P x)). Qed.
Lemma lem3213540 {A : Type'} (GEN_PVAR_8 : A) : (@SETSPEC A GEN_PVAR_8) = (@SETSPEC A GEN_PVAR_8).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_8)). Qed.
Lemma lem3213541 {A : Type'} (GEN_PVAR_8 : A) (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term33 A GEN_PVAR_8 a s P x) = (term34 A GEN_PVAR_8 a s P x).
Proof. exact (MK_COMB (@lem3213540 A GEN_PVAR_8) (@lem3213539 A a s P x)). Qed.
Lemma lem3213542 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3213543 {A : Type'} (GEN_PVAR_8 : A) (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term35 A GEN_PVAR_8 a s P x) = (term36 A GEN_PVAR_8 a s P x).
Proof. exact (MK_COMB (@lem3213541 A GEN_PVAR_8 a s P x) (@lem3213542 A x)). Qed.
Lemma lem3213544 {A : Type'} (GEN_PVAR_8 : A) (a : A) (s : A -> Prop) (P : A -> Prop) : (term37 A GEN_PVAR_8 a s P) = (term38 A GEN_PVAR_8 a s P).
Proof. exact (fun_ext (fun x : A => @lem3213543 A GEN_PVAR_8 a s P x)). Qed.
Lemma lem3213545 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3213546 {A : Type'} (GEN_PVAR_8 : A) (a : A) (s : A -> Prop) (P : A -> Prop) : (term39 A GEN_PVAR_8 a s P) = (term40 A GEN_PVAR_8 a s P).
Proof. exact (MK_COMB (@lem3213545 A) (@lem3213544 A GEN_PVAR_8 a s P)). Qed.
Lemma lem3213547 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : (term41 A a s P) = (term42 A a s P).
Proof. exact (fun_ext (fun GEN_PVAR_8 : A => @lem3213546 A GEN_PVAR_8 a s P)). Qed.
Lemma lem3213548 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem3213549 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : (term43 A a s P) = (term10 A a s P).
Proof. exact (MK_COMB (@lem3213548 A) (@lem3213547 A a s P)). Qed.
Lemma lem3213550 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem3213551 {A : Type'} (x : A) (a : A) (s : A -> Prop) (P : A -> Prop) : (term29 A x a s P) = (term44 A x a s P).
Proof. exact (MK_COMB (@lem3213550 A x) (@lem3213549 A a s P)). Qed.
Lemma lem3213552 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3213553 {A : Type'} (x : A) (a : A) (s : A -> Prop) (P : A -> Prop) : (term45 A x a s P) = (term46 A x a s P).
Proof. exact (MK_COMB (@lem3213552) (@lem3213551 A x a s P)). Qed.
Lemma lem3213554 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term30 A a s P x) = (term32 A a s P x).
Proof. exact (eq_refl (term30 A a s P x)). Qed.
Lemma lem3213555 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) : ((term29 A x a s P) = (term30 A a s P x)) = ((term44 A x a s P) = (term32 A a s P x)).
Proof. exact (MK_COMB (@lem3213553 A x a s P) (@lem3213554 A a s P x)). Qed.
Lemma lem3213556 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term44 A x a s P) = (term32 A a s P x).
Proof. exact (EQ_MP (@lem3213555 A a s P x) (@lem3213538 A a s P x)). Qed.
Lemma lem3213560 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term47 A x y s) = (term48 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3213561 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term47 A x y s) = (term48 A y x s).
Proof. exact (@lem3213560 A y x s). Qed.
Lemma lem3213562 {A : Type'} (a : A) (x : A) (s : A -> Prop) : (term47 A x a s) = (term48 A a x s).
Proof. exact (@lem3213561 A a x s). Qed.
Lemma lem3213568 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3213569 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3213568 A P x). Qed.
Lemma lem3213570 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3213569 A s x). Qed.
Lemma lem3213571 {A : Type'} (x : A) (a : A) : (term49 A x a) = (term49 A x a).
Proof. exact (eq_refl (term49 A x a)). Qed.
Lemma lem3213572 {A : Type'} (a : A) (s : A -> Prop) (x : A) : (term48 A a x s) = (term50 A a s x).
Proof. exact (MK_COMB (@lem3213571 A x a) (@lem3213570 A s x)). Qed.
Lemma lem3213575 {A : Type'} (a : A) (s : A -> Prop) (x : A) : (term47 A x a s) = (term50 A a s x).
Proof. exact (TRANS (@lem3213562 A a x s) (@lem3213572 A a s x)). Qed.
Lemma lem3213576 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3213577 {A : Type'} (a : A) (s : A -> Prop) (x : A) : (term51 A x a s) = (term52 A a s x).
Proof. exact (MK_COMB (@lem3213576) (@lem3213575 A a s x)). Qed.
Lemma lem3213578 {A : Type'} (P : A -> Prop) (x : A) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem3213579 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term32 A a s P x) = (term53 A a s P x).
Proof. exact (MK_COMB (@lem3213577 A a s x) (@lem3213578 A P x)). Qed.
Lemma lem3213582 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term44 A x a s P) = (term53 A a s P x).
Proof. exact (TRANS (@lem3213556 A a s P x) (@lem3213579 A a s P x)). Qed.
Lemma lem3213583 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3213584 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term46 A x a s P) = (term54 A a s P x).
Proof. exact (MK_COMB (@lem3213583) (@lem3213582 A a s P x)). Qed.
Lemma lem3213586 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term47 A x y s) = (term48 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3213587 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term47 A x y s) = (term48 A y x s).
Proof. exact (@lem3213586 A y x s). Qed.
Lemma lem3213588 {A : Type'} (a : A) (x : A) (s : A -> Prop) (P : A -> Prop) : (term55 A x a s P) = (term56 A a x s P).
Proof. exact (@lem3213587 A a x (term8 A s P)). Qed.
Lemma lem3213594 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term28 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem3213595 {A : Type'} (p : A -> Prop) (x : A) : (term28 A x p) = (p x).
Proof. exact (@lem3213594 A p x). Qed.
Lemma lem3213596 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term57 A x s P) = (term58 A s P x).
Proof. exact (@lem3213595 A (term59 A s P) x). Qed.
Lemma lem3213597 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term58 A s P x) = (term60 A s P x).
Proof. exact (eq_refl (term58 A s P x)). Qed.
Lemma lem3213598 {A : Type'} (GEN_PVAR_9 : A) : (@SETSPEC A GEN_PVAR_9) = (@SETSPEC A GEN_PVAR_9).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_9)). Qed.
Lemma lem3213599 {A : Type'} (GEN_PVAR_9 : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term61 A GEN_PVAR_9 s P x) = (term62 A GEN_PVAR_9 s P x).
Proof. exact (MK_COMB (@lem3213598 A GEN_PVAR_9) (@lem3213597 A s P x)). Qed.
Lemma lem3213600 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3213601 {A : Type'} (GEN_PVAR_9 : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term63 A GEN_PVAR_9 s P x) = (term64 A GEN_PVAR_9 s P x).
Proof. exact (MK_COMB (@lem3213599 A GEN_PVAR_9 s P x) (@lem3213600 A x)). Qed.
Lemma lem3213602 {A : Type'} (GEN_PVAR_9 : A) (s : A -> Prop) (P : A -> Prop) : (term65 A GEN_PVAR_9 s P) = (term66 A GEN_PVAR_9 s P).
Proof. exact (fun_ext (fun x : A => @lem3213601 A GEN_PVAR_9 s P x)). Qed.
Lemma lem3213603 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3213604 {A : Type'} (GEN_PVAR_9 : A) (s : A -> Prop) (P : A -> Prop) : (term67 A GEN_PVAR_9 s P) = (term68 A GEN_PVAR_9 s P).
Proof. exact (MK_COMB (@lem3213603 A) (@lem3213602 A GEN_PVAR_9 s P)). Qed.
Lemma lem3213605 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term69 A s P) = (term70 A s P).
Proof. exact (fun_ext (fun GEN_PVAR_9 : A => @lem3213604 A GEN_PVAR_9 s P)). Qed.
Lemma lem3213606 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem3213607 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term71 A s P) = (term8 A s P).
Proof. exact (MK_COMB (@lem3213606 A) (@lem3213605 A s P)). Qed.
Lemma lem3213608 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem3213609 {A : Type'} (x : A) (s : A -> Prop) (P : A -> Prop) : (term57 A x s P) = (term72 A x s P).
Proof. exact (MK_COMB (@lem3213608 A x) (@lem3213607 A s P)). Qed.
Lemma lem3213610 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3213611 {A : Type'} (x : A) (s : A -> Prop) (P : A -> Prop) : (term73 A x s P) = (term74 A x s P).
Proof. exact (MK_COMB (@lem3213610) (@lem3213609 A x s P)). Qed.
Lemma lem3213612 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term58 A s P x) = (term60 A s P x).
Proof. exact (eq_refl (term58 A s P x)). Qed.
Lemma lem3213613 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : ((term57 A x s P) = (term58 A s P x)) = ((term72 A x s P) = (term60 A s P x)).
Proof. exact (MK_COMB (@lem3213611 A x s P) (@lem3213612 A s P x)). Qed.
Lemma lem3213614 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term72 A x s P) = (term60 A s P x).
Proof. exact (EQ_MP (@lem3213613 A s P x) (@lem3213596 A s P x)). Qed.
Lemma lem3213618 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3213619 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3213618 A P x). Qed.
Lemma lem3213620 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3213619 A s x). Qed.
Lemma lem3213621 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3213622 {A : Type'} (s : A -> Prop) (x : A) : (term75 A x s) = (term76 A s x).
Proof. exact (MK_COMB (@lem3213621) (@lem3213620 A s x)). Qed.
Lemma lem3213623 {A : Type'} (P : A -> Prop) (x : A) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem3213624 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term60 A s P x) = (term77 A s P x).
Proof. exact (MK_COMB (@lem3213622 A s x) (@lem3213623 A P x)). Qed.
Lemma lem3213627 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term72 A x s P) = (term77 A s P x).
Proof. exact (TRANS (@lem3213614 A s P x) (@lem3213624 A s P x)). Qed.
Lemma lem3213628 {A : Type'} (x : A) (a : A) : (term49 A x a) = (term49 A x a).
Proof. exact (eq_refl (term49 A x a)). Qed.
Lemma lem3213629 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term56 A a x s P) = (term78 A a s P x).
Proof. exact (MK_COMB (@lem3213628 A x a) (@lem3213627 A s P x)). Qed.
Lemma lem3213632 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term55 A x a s P) = (term78 A a s P x).
Proof. exact (TRANS (@lem3213588 A a x s P) (@lem3213629 A a s P x)). Qed.
Lemma lem3213633 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) : ((term44 A x a s P) = (term55 A x a s P)) = ((term53 A a s P x) = (term78 A a s P x)).
Proof. exact (MK_COMB (@lem3213584 A a s P x) (@lem3213632 A a s P x)). Qed.
Lemma lem3213636 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : (term79 A a s P) = (term80 A a s P).
Proof. exact (fun_ext (fun x : A => @lem3213633 A a s P x)). Qed.
Lemma lem3213637 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3213638 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : (term26 A a s P) = (term81 A a s P).
Proof. exact (MK_COMB (@lem3213637 A) (@lem3213636 A a s P)). Qed.
Lemma lem3213643 {A : Type'} (P : A -> Prop) (a : A) : (term15 A P a) = (term15 A P a).
Proof. exact (eq_refl (term15 A P a)). Qed.
Lemma lem3213644 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : (term27 A a s P) = (term82 A a s P).
Proof. exact (MK_COMB (@lem3213643 A P a) (@lem3213638 A a s P)). Qed.
Lemma lem3213647 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : (term82 A a s P) = (term27 A a s P).
Proof. exact (SYM (@lem3213644 A a s P)). Qed.
Lemma lem3213649 (p : Prop) : p = (term83 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3213650 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : (term82 A a s P) = (term84 A a s P).
Proof. exact (@lem3213649 (term82 A a s P)). Qed.
Lemma lem3213651 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : (term84 A a s P) = (term82 A a s P).
Proof. exact (SYM (@lem3213650 A a s P)). Qed.
Lemma lem3213652 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (h1 : term85 A a s P) : term85 A a s P.
Proof. exact (h1). Qed.
Lemma lem3213655 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (h1 : term84 A a s P) : term84 A a s P.
Proof. exact (h1). Qed.
Lemma lem3213656 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : term86 A a s P.
Proof. exact (fun h0 : term84 A a s P => @lem3213655 A a s P h0). Qed.
Lemma lem3213657 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (h1 : term86 A a s P) : term86 A a s P.
Proof. exact (h1). Qed.
Lemma lem3213658 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (h1 : term84 A a s P) : term84 A a s P.
Proof. exact (h1). Qed.
Lemma lem3213659 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (h1 : term84 A a s P) (h2 : term86 A a s P) : term84 A a s P.
Proof. exact (@lem3213657 A a s P h2 (@lem3213658 A a s P h1)). Qed.
Lemma lem3213660 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (h1 : term84 A a s P) : term87 A a s P.
Proof. exact (fun h0 : term86 A a s P => @lem3213659 A a s P h1 h0). Qed.
Lemma lem3213661 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (h1 : term86 A a s P) : term86 A a s P.
Proof. exact (h1). Qed.
Lemma lem3213662 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (h1 : term84 A a s P) (h2 : term86 A a s P) : term84 A a s P.
Proof. exact (@lem3213660 A a s P h1 (@lem3213661 A a s P h2)). Qed.
Lemma lem3213663 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (h1 : term86 A a s P) : term86 A a s P.
Proof. exact (fun h0 : term84 A a s P => @lem3213662 A a s P h0 h1). Qed.
Lemma lem3213664 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : term88 A a s P.
Proof. exact (fun h0 : term86 A a s P => @lem3213663 A a s P h0). Qed.
Lemma lem3213667 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : term86 A a s P.
Proof. exact (@lem3213664 A a s P (@lem3213656 A a s P)). Qed.
Lemma lem3213668 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : term86 A a s P.
Proof. exact (@lem3213667 A a s P). Qed.
Lemma lem3213682 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3213683 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : (term84 A a s P) = (term89 A a s P).
Proof. exact (@lem3213682 (term85 A a s P)). Qed.
Lemma lem3213685 (t : Prop) : (term90 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3213686 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : (term89 A a s P) = (term82 A a s P).
Proof. exact (@lem3213685 (term82 A a s P)). Qed.
Lemma lem3213689 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : (term84 A a s P) = (term82 A a s P).
Proof. exact (TRANS (@lem3213683 A a s P) (@lem3213686 A a s P)). Qed.
Lemma lem3213702 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term91 A s P) = (term92 A s P).
Proof. exact (fun_ext (fun a : A => @lem3213689 A a s P)). Qed.
Lemma lem3213703 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3213704 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term93 A s P) = (term94 A s P).
Proof. exact (MK_COMB (@lem3213703 A) (@lem3213702 A s P)). Qed.
Lemma lem3213709 {A : Type'} (P : A -> Prop) : (term95 A P) = (term96 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3213704 A s P)). Qed.
Lemma lem3213710 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3213711 {A : Type'} (P : A -> Prop) : (term97 A P) = (term98 A P).
Proof. exact (MK_COMB (@lem3213710 A) (@lem3213709 A P)). Qed.
Lemma lem3213716 {A : Type'} : (term99 A) = (term100 A).
Proof. exact (fun_ext (fun P : A -> Prop => @lem3213711 A P)). Qed.
Lemma lem3213717 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3213726 {A : Type'} : (term101 A) = (term102 A).
Proof. exact (MK_COMB (@lem3213717 A) (@lem3213716 A)). Qed.
Lemma lem3213747 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) : ((term53 A a s P x) = (term78 A a s P x)) = ((term53 A a s P x) = (term78 A a s P x)).
Proof. exact (eq_refl ((term53 A a s P x) = (term78 A a s P x))). Qed.
Lemma lem3213748 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : (term80 A a s P) = (term80 A a s P).
Proof. exact (fun_ext (fun x : A => @lem3213747 A a s P x)). Qed.
Lemma lem3213749 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3213750 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : (term81 A a s P) = (term81 A a s P).
Proof. exact (MK_COMB (@lem3213749 A) (@lem3213748 A a s P)). Qed.
Lemma lem3213753 {A : Type'} (P : A -> Prop) (a : A) : (term15 A P a) = (term15 A P a).
Proof. exact (eq_refl (term15 A P a)). Qed.
Lemma lem3213754 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : (term82 A a s P) = (term82 A a s P).
Proof. exact (MK_COMB (@lem3213753 A P a) (@lem3213750 A a s P)). Qed.
Lemma lem3213755 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term92 A s P) = (term92 A s P).
Proof. exact (fun_ext (fun a : A => @lem3213754 A a s P)). Qed.
Lemma lem3213756 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3213757 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term94 A s P) = (term94 A s P).
Proof. exact (MK_COMB (@lem3213756 A) (@lem3213755 A s P)). Qed.
Lemma lem3213758 {A : Type'} (P : A -> Prop) : (term96 A P) = (term96 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3213757 A s P)). Qed.
Lemma lem3213759 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3213760 {A : Type'} (P : A -> Prop) : (term98 A P) = (term98 A P).
Proof. exact (MK_COMB (@lem3213759 A) (@lem3213758 A P)). Qed.
Lemma lem3213761 {A : Type'} : (term100 A) = (term100 A).
Proof. exact (fun_ext (fun P : A -> Prop => @lem3213760 A P)). Qed.
Lemma lem3213762 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3213763 {A : Type'} : (term102 A) = (term102 A).
Proof. exact (MK_COMB (@lem3213762 A) (@lem3213761 A)). Qed.
Lemma lem3213800 {A : Type'} : (term101 A) = (term102 A).
Proof. exact (TRANS (@lem3213726 A) (@lem3213763 A)). Qed.
Lemma lem3213801 {A : Type'} : (term102 A) = (term101 A).
Proof. exact (SYM (@lem3213800 A)). Qed.
Lemma lem3213804 (p : Prop) : p = (term83 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3213805 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) : ((term53 A a s P x) = (term78 A a s P x)) = (term103 A a s P x).
Proof. exact (@lem3213804 ((term53 A a s P x) = (term78 A a s P x))). Qed.
Lemma lem3213806 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term103 A a s P x) = ((term53 A a s P x) = (term78 A a s P x)).
Proof. exact (SYM (@lem3213805 A a s P x)). Qed.
Lemma lem3213807 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term104 A a s P x) : term104 A a s P x.
Proof. exact (h1). Qed.
Lemma lem3213813 {A : Type'} (P : A -> Prop) (a : A) (h1 : P a) : P a.
Proof. exact (h1). Qed.
Lemma lem3213822 {A : Type'} (a : A) (s : A -> Prop) (x : A) : (term105 A a s x) = (term106 A a s x).
Proof. exact (@lem17160 (x = a) (s x)). Qed.
Lemma lem3213826 {A : Type'} (P : A -> Prop) (x : A) : (term24 A P x) = (term24 A P x).
Proof. exact (eq_refl (term24 A P x)). Qed.
Lemma lem3213828 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3213829 {A : Type'} (a : A) (s : A -> Prop) (x : A) : (term107 A a s x) = (term108 A a s x).
Proof. exact (MK_COMB (@lem3213828) (@lem3213822 A a s x)). Qed.
Lemma lem3213830 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term109 A a s P x) = (term110 A a s P x).
Proof. exact (MK_COMB (@lem3213829 A a s x) (@lem3213826 A P x)). Qed.
Lemma lem3213831 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term111 A a s P x) = (term109 A a s P x).
Proof. exact (@lem17045 (term50 A a s x) (P x)). Qed.
Lemma lem3213832 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term111 A a s P x) = (term110 A a s P x).
Proof. exact (TRANS (@lem3213831 A a s P x) (@lem3213830 A a s P x)). Qed.
Lemma lem3213846 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term112 A s P x) = (term113 A s P x).
Proof. exact (@lem17045 (s x) (P x)). Qed.
Lemma lem3213851 {A : Type'} (x : A) (a : A) : (term114 A x a) = (term114 A x a).
Proof. exact (eq_refl (term114 A x a)). Qed.
Lemma lem3213852 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term115 A a s P x) = (term116 A a s P x).
Proof. exact (MK_COMB (@lem3213851 A x a) (@lem3213846 A s P x)). Qed.
Lemma lem3213853 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term117 A a s P x) = (term115 A a s P x).
Proof. exact (@lem17160 (x = a) (term77 A s P x)). Qed.
Lemma lem3213854 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term117 A a s P x) = (term116 A a s P x).
Proof. exact (TRANS (@lem3213853 A a s P x) (@lem3213852 A a s P x)). Qed.
Lemma lem3213857 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term78 A a s P x) = (term78 A a s P x).
Proof. exact (eq_refl (term78 A a s P x)). Qed.
Lemma lem3213858 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3213859 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term118 A a s P x) = (term119 A a s P x).
Proof. exact (MK_COMB (@lem3213858) (@lem3213832 A a s P x)). Qed.
Lemma lem3213860 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term120 A a s P x) = (term121 A a s P x).
Proof. exact (MK_COMB (@lem3213859 A a s P x) (@lem3213857 A a s P x)). Qed.
Lemma lem3213862 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term122 A a s P x) = (term122 A a s P x).
Proof. exact (eq_refl (term122 A a s P x)). Qed.
Lemma lem3213863 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term123 A a s P x) = (term124 A a s P x).
Proof. exact (MK_COMB (@lem3213862 A a s P x) (@lem3213854 A a s P x)). Qed.
Lemma lem3213864 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3213865 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term125 A a s P x) = (term126 A a s P x).
Proof. exact (MK_COMB (@lem3213864) (@lem3213863 A a s P x)). Qed.
Lemma lem3213866 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term127 A a s P x) = (term128 A a s P x).
Proof. exact (MK_COMB (@lem3213865 A a s P x) (@lem3213860 A a s P x)). Qed.
Lemma lem3213867 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term104 A a s P x) = (term127 A a s P x).
Proof. exact (@lem17646 (term53 A a s P x) (term78 A a s P x)). Qed.
Lemma lem3213872 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term104 A a s P x) = (term128 A a s P x).
Proof. exact (TRANS (@lem3213867 A a s P x) (@lem3213866 A a s P x)). Qed.
Lemma lem3213877 {A : Type'} (P : A -> Prop) (a : A) (h1 : P a) : P a.
Proof. exact (h1). Qed.
Lemma lem3213967 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term104 A a s P x) : term128 A a s P x.
Proof. exact (EQ_MP (@lem3213872 A a s P x) (@lem3213807 A a s P x h1)). Qed.
Lemma lem3213968 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term124 A a s P x) : term124 A a s P x.
Proof. exact (h1). Qed.
Lemma lem3213969 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term121 A a s P x) : term121 A a s P x.
Proof. exact (h1). Qed.
Lemma lem3213970 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term124 A a s P x) : term116 A a s P x.
Proof. exact (proj2 (@lem3213968 A a s P x h1)). Qed.
Lemma lem3213971 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term124 A a s P x) : term53 A a s P x.
Proof. exact (proj1 (@lem3213968 A a s P x h1)). Qed.
Lemma lem3213972 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term124 A a s P x) : term113 A s P x.
Proof. exact (proj2 (@lem3213970 A a s P x h1)). Qed.
Lemma lem3213975 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term124 A a s P x) : term50 A a s x.
Proof. exact (proj1 (@lem3213971 A a s P x h1)). Qed.
Lemma lem3213982 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term121 A a s P x) : term78 A a s P x.
Proof. exact (proj2 (@lem3213969 A a s P x h1)). Qed.
Lemma lem3213983 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term121 A a s P x) : term110 A a s P x.
Proof. exact (proj1 (@lem3213969 A a s P x h1)). Qed.
Lemma lem3213985 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term77 A s P x) : term77 A s P x.
Proof. exact (h1). Qed.
Lemma lem3213986 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : term106 A a s x) : term106 A a s x.
Proof. exact (h1). Qed.
Lemma lem3213992 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : term106 A a s x) : term106 A a s x.
Proof. exact (h1). Qed.
Lemma lem3214011 {A : Type'} (x : A) (a : A) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem3214031 {A : Type'} (x : A) (a : A) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem3214035 {A : Type'} (P : A -> Prop) (x : A) (h1 : term24 A P x) : term24 A P x.
Proof. exact (h1). Qed.
Lemma lem3214051 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3214055 {A : Type'} (s : A -> Prop) (x : A) (h1 : term24 A s x) : term24 A s x.
Proof. exact (h1). Qed.
Lemma lem3214075 {A : Type'} (P : A -> Prop) (x : A) (h1 : term24 A P x) : term24 A P x.
Proof. exact (h1). Qed.
Lemma lem3214083 {A : Type'} (x : A) (a : A) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem3214095 {A : Type'} (P : A -> Prop) (a : A) (h1 : P a) : P a.
Proof. exact (h1). Qed.
Lemma lem3214099 {A : Type'} (x : A) (a : A) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem3214103 {A : Type'} (P : A -> Prop) (x : A) (h1 : term24 A P x) : term24 A P x.
Proof. exact (h1). Qed.
Lemma lem3214139 {A : Type'} (P : A -> Prop) (x : A) (h1 : term24 A P x) : term24 A P x.
Proof. exact (h1). Qed.
Lemma lem3214143 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term124 A a s P x) : term129 A x a.
Proof. exact (proj1 (@lem3213970 A a s P x h1)). Qed.
Lemma lem3214147 {A : Type'} (x : A) (a : A) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem3214155 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term124 A a s P x) : P x.
Proof. exact (proj2 (@lem3213971 A a s P x h1)). Qed.
Lemma lem3214157 {A : Type'} (x : A) (a : A) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem3214159 {A : Type'} (P : A -> Prop) (x : A) (h1 : term24 A P x) : term24 A P x.
Proof. exact (h1). Qed.
Lemma lem3214167 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3214169 {A : Type'} (s : A -> Prop) (x : A) (h1 : term24 A s x) : term24 A s x.
Proof. exact (h1). Qed.
Lemma lem3214179 {A : Type'} (P : A -> Prop) (x : A) (h1 : term24 A P x) : term24 A P x.
Proof. exact (h1). Qed.
Lemma lem3214183 {A : Type'} (x : A) (a : A) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem3214185 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : term106 A a s x) : term129 A x a.
Proof. exact (proj1 (@lem3213986 A a s x h1)). Qed.
Lemma lem3214189 {A : Type'} (P : A -> Prop) (a : A) (h1 : P a) : P a.
Proof. exact (h1). Qed.
Lemma lem3214191 {A : Type'} (x : A) (a : A) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem3214193 {A : Type'} (P : A -> Prop) (x : A) (h1 : term24 A P x) : term24 A P x.
Proof. exact (h1). Qed.
Lemma lem3214203 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : term106 A a s x) : term24 A s x.
Proof. exact (proj2 (@lem3213992 A a s x h1)). Qed.
Lemma lem3214211 {A : Type'} (P : A -> Prop) (x : A) (h1 : term24 A P x) : term24 A P x.
Proof. exact (h1). Qed.
Lemma lem3214240 {A : Type'} (a : A) : (term130 A a) = (term130 A a).
Proof. exact (eq_refl (term130 A a)). Qed.
Lemma lem3214241 {A : Type'} (x : A) (a : A) (h1 : x = a) : (term131 A a x) = (term132 A a).
Proof. exact (MK_COMB (@lem3214240 A a) (@lem3214147 A x a h1)). Qed.
Lemma lem3214242 {A : Type'} (a : A) : (term132 A a) = (term133 A a).
Proof. exact (eq_refl (term132 A a)). Qed.
Lemma lem3214243 {A : Type'} (a : A) (x : A) : (term134 A a x) = (term134 A a x).
Proof. exact (eq_refl (term134 A a x)). Qed.
Lemma lem3214244 {A : Type'} (x : A) (a : A) : ((term131 A a x) = (term132 A a)) = ((term131 A a x) = (term133 A a)).
Proof. exact (MK_COMB (@lem3214243 A a x) (@lem3214242 A a)). Qed.
Lemma lem3214245 {A : Type'} (x : A) (a : A) : (term131 A a x) = (term129 A x a).
Proof. exact (eq_refl (term131 A a x)). Qed.
Lemma lem3214246 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3214247 {A : Type'} (x : A) (a : A) : (term134 A a x) = (term135 A x a).
Proof. exact (MK_COMB (@lem3214246) (@lem3214245 A x a)). Qed.
Lemma lem3214248 {A : Type'} (a : A) : (term133 A a) = (term133 A a).
Proof. exact (eq_refl (term133 A a)). Qed.
Lemma lem3214249 {A : Type'} (x : A) (a : A) : ((term131 A a x) = (term133 A a)) = ((term129 A x a) = (term133 A a)).
Proof. exact (MK_COMB (@lem3214247 A x a) (@lem3214248 A a)). Qed.
Lemma lem3214250 {A : Type'} (x : A) (a : A) : ((term131 A a x) = (term132 A a)) = ((term129 A x a) = (term133 A a)).
Proof. exact (TRANS (@lem3214244 A x a) (@lem3214249 A x a)). Qed.
Lemma lem3214251 {A : Type'} (x : A) (a : A) (h1 : x = a) : (term129 A x a) = (term133 A a).
Proof. exact (EQ_MP (@lem3214250 A x a) (@lem3214241 A x a h1)). Qed.
Lemma lem3214252 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (a : A) (h1 : term124 A a s P x) (h2 : x = a) : term133 A a.
Proof. exact (EQ_MP (@lem3214251 A x a h2) (@lem3214143 A a s P x h1)). Qed.
Lemma lem3214320 {A : Type'} (P : A -> Prop) : (term136 A P) = (term136 A P).
Proof. exact (eq_refl (term136 A P)). Qed.
Lemma lem3214321 {A : Type'} (P : A -> Prop) (x : A) (a : A) (h1 : x = a) : (term137 A P x) = (term137 A P a).
Proof. exact (MK_COMB (@lem3214320 A P) (@lem3214157 A x a h1)). Qed.
Lemma lem3214322 {A : Type'} (P : A -> Prop) (a : A) : (term137 A P a) = (P a).
Proof. exact (eq_refl (term137 A P a)). Qed.
Lemma lem3214323 {A : Type'} (P : A -> Prop) (x : A) : (term138 A P x) = (term138 A P x).
Proof. exact (eq_refl (term138 A P x)). Qed.
Lemma lem3214324 {A : Type'} (x : A) (P : A -> Prop) (a : A) : ((term137 A P x) = (term137 A P a)) = ((term137 A P x) = (P a)).
Proof. exact (MK_COMB (@lem3214323 A P x) (@lem3214322 A P a)). Qed.
Lemma lem3214325 {A : Type'} (P : A -> Prop) (x : A) : (term137 A P x) = (P x).
Proof. exact (eq_refl (term137 A P x)). Qed.
Lemma lem3214326 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3214327 {A : Type'} (P : A -> Prop) (x : A) : (term138 A P x) = (term139 A P x).
Proof. exact (MK_COMB (@lem3214326) (@lem3214325 A P x)). Qed.
Lemma lem3214328 {A : Type'} (P : A -> Prop) (a : A) : (P a) = (P a).
Proof. exact (eq_refl (P a)). Qed.
Lemma lem3214329 {A : Type'} (x : A) (P : A -> Prop) (a : A) : ((term137 A P x) = (P a)) = ((P x) = (P a)).
Proof. exact (MK_COMB (@lem3214327 A P x) (@lem3214328 A P a)). Qed.
Lemma lem3214330 {A : Type'} (x : A) (P : A -> Prop) (a : A) : ((term137 A P x) = (term137 A P a)) = ((P x) = (P a)).
Proof. exact (TRANS (@lem3214324 A x P a) (@lem3214329 A x P a)). Qed.
Lemma lem3214331 {A : Type'} (P : A -> Prop) (x : A) (a : A) (h1 : x = a) : (P x) = (P a).
Proof. exact (EQ_MP (@lem3214330 A x P a) (@lem3214321 A P x a h1)). Qed.
Lemma lem3214333 {A : Type'} (P : A -> Prop) : (term140 A P) = (term140 A P).
Proof. exact (eq_refl (term140 A P)). Qed.
Lemma lem3214334 {A : Type'} (P : A -> Prop) (x : A) (a : A) (h1 : x = a) : (term141 A P x) = (term141 A P a).
Proof. exact (MK_COMB (@lem3214333 A P) (@lem3214157 A x a h1)). Qed.
Lemma lem3214335 {A : Type'} (P : A -> Prop) (a : A) : (term141 A P a) = (term24 A P a).
Proof. exact (eq_refl (term141 A P a)). Qed.
Lemma lem3214336 {A : Type'} (P : A -> Prop) (x : A) : (term142 A P x) = (term142 A P x).
Proof. exact (eq_refl (term142 A P x)). Qed.
Lemma lem3214337 {A : Type'} (x : A) (P : A -> Prop) (a : A) : ((term141 A P x) = (term141 A P a)) = ((term141 A P x) = (term24 A P a)).
Proof. exact (MK_COMB (@lem3214336 A P x) (@lem3214335 A P a)). Qed.
Lemma lem3214338 {A : Type'} (P : A -> Prop) (x : A) : (term141 A P x) = (term24 A P x).
Proof. exact (eq_refl (term141 A P x)). Qed.
Lemma lem3214339 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3214340 {A : Type'} (P : A -> Prop) (x : A) : (term142 A P x) = (term143 A P x).
Proof. exact (MK_COMB (@lem3214339) (@lem3214338 A P x)). Qed.
Lemma lem3214341 {A : Type'} (P : A -> Prop) (a : A) : (term24 A P a) = (term24 A P a).
Proof. exact (eq_refl (term24 A P a)). Qed.
Lemma lem3214342 {A : Type'} (x : A) (P : A -> Prop) (a : A) : ((term141 A P x) = (term24 A P a)) = ((term24 A P x) = (term24 A P a)).
Proof. exact (MK_COMB (@lem3214340 A P x) (@lem3214341 A P a)). Qed.
Lemma lem3214343 {A : Type'} (x : A) (P : A -> Prop) (a : A) : ((term141 A P x) = (term141 A P a)) = ((term24 A P x) = (term24 A P a)).
Proof. exact (TRANS (@lem3214337 A x P a) (@lem3214342 A x P a)). Qed.
Lemma lem3214344 {A : Type'} (P : A -> Prop) (x : A) (a : A) (h1 : x = a) : (term24 A P x) = (term24 A P a).
Proof. exact (EQ_MP (@lem3214343 A x P a) (@lem3214334 A P x a h1)). Qed.
Lemma lem3214345 {A : Type'} (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P x) (h2 : x = a) : term24 A P a.
Proof. exact (EQ_MP (@lem3214344 A P x a h2) (@lem3214159 A P x h1)). Qed.
Lemma lem3214374 {A : Type'} (a : A) : (term130 A a) = (term130 A a).
Proof. exact (eq_refl (term130 A a)). Qed.
Lemma lem3214375 {A : Type'} (x : A) (a : A) (h1 : x = a) : (term131 A a x) = (term132 A a).
Proof. exact (MK_COMB (@lem3214374 A a) (@lem3214183 A x a h1)). Qed.
Lemma lem3214376 {A : Type'} (a : A) : (term132 A a) = (term133 A a).
Proof. exact (eq_refl (term132 A a)). Qed.
Lemma lem3214377 {A : Type'} (a : A) (x : A) : (term134 A a x) = (term134 A a x).
Proof. exact (eq_refl (term134 A a x)). Qed.
Lemma lem3214378 {A : Type'} (x : A) (a : A) : ((term131 A a x) = (term132 A a)) = ((term131 A a x) = (term133 A a)).
Proof. exact (MK_COMB (@lem3214377 A a x) (@lem3214376 A a)). Qed.
Lemma lem3214379 {A : Type'} (x : A) (a : A) : (term131 A a x) = (term129 A x a).
Proof. exact (eq_refl (term131 A a x)). Qed.
Lemma lem3214380 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3214381 {A : Type'} (x : A) (a : A) : (term134 A a x) = (term135 A x a).
Proof. exact (MK_COMB (@lem3214380) (@lem3214379 A x a)). Qed.
Lemma lem3214382 {A : Type'} (a : A) : (term133 A a) = (term133 A a).
Proof. exact (eq_refl (term133 A a)). Qed.
Lemma lem3214383 {A : Type'} (x : A) (a : A) : ((term131 A a x) = (term133 A a)) = ((term129 A x a) = (term133 A a)).
Proof. exact (MK_COMB (@lem3214381 A x a) (@lem3214382 A a)). Qed.
Lemma lem3214384 {A : Type'} (x : A) (a : A) : ((term131 A a x) = (term132 A a)) = ((term129 A x a) = (term133 A a)).
Proof. exact (TRANS (@lem3214378 A x a) (@lem3214383 A x a)). Qed.
Lemma lem3214385 {A : Type'} (x : A) (a : A) (h1 : x = a) : (term129 A x a) = (term133 A a).
Proof. exact (EQ_MP (@lem3214384 A x a) (@lem3214375 A x a h1)). Qed.
Lemma lem3214386 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term106 A a s x) (h2 : x = a) : term133 A a.
Proof. exact (EQ_MP (@lem3214385 A x a h2) (@lem3214185 A a s x h1)). Qed.
Lemma lem3214427 {A : Type'} (P : A -> Prop) (a : A) (h1 : P a) : P a.
Proof. exact (h1). Qed.
Lemma lem3214428 {A : Type'} (P : A -> Prop) : (term140 A P) = (term140 A P).
Proof. exact (eq_refl (term140 A P)). Qed.
Lemma lem3214429 {A : Type'} (P : A -> Prop) (x : A) (a : A) (h1 : x = a) : (term141 A P x) = (term141 A P a).
Proof. exact (MK_COMB (@lem3214428 A P) (@lem3214191 A x a h1)). Qed.
Lemma lem3214430 {A : Type'} (P : A -> Prop) (a : A) : (term141 A P a) = (term24 A P a).
Proof. exact (eq_refl (term141 A P a)). Qed.
Lemma lem3214431 {A : Type'} (P : A -> Prop) (x : A) : (term142 A P x) = (term142 A P x).
Proof. exact (eq_refl (term142 A P x)). Qed.
Lemma lem3214432 {A : Type'} (x : A) (P : A -> Prop) (a : A) : ((term141 A P x) = (term141 A P a)) = ((term141 A P x) = (term24 A P a)).
Proof. exact (MK_COMB (@lem3214431 A P x) (@lem3214430 A P a)). Qed.
Lemma lem3214433 {A : Type'} (P : A -> Prop) (x : A) : (term141 A P x) = (term24 A P x).
Proof. exact (eq_refl (term141 A P x)). Qed.
Lemma lem3214434 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3214435 {A : Type'} (P : A -> Prop) (x : A) : (term142 A P x) = (term143 A P x).
Proof. exact (MK_COMB (@lem3214434) (@lem3214433 A P x)). Qed.
Lemma lem3214436 {A : Type'} (P : A -> Prop) (a : A) : (term24 A P a) = (term24 A P a).
Proof. exact (eq_refl (term24 A P a)). Qed.
Lemma lem3214437 {A : Type'} (x : A) (P : A -> Prop) (a : A) : ((term141 A P x) = (term24 A P a)) = ((term24 A P x) = (term24 A P a)).
Proof. exact (MK_COMB (@lem3214435 A P x) (@lem3214436 A P a)). Qed.
Lemma lem3214438 {A : Type'} (x : A) (P : A -> Prop) (a : A) : ((term141 A P x) = (term141 A P a)) = ((term24 A P x) = (term24 A P a)).
Proof. exact (TRANS (@lem3214432 A x P a) (@lem3214437 A x P a)). Qed.
Lemma lem3214439 {A : Type'} (P : A -> Prop) (x : A) (a : A) (h1 : x = a) : (term24 A P x) = (term24 A P a).
Proof. exact (EQ_MP (@lem3214438 A x P a) (@lem3214429 A P x a h1)). Qed.
Lemma lem3214440 {A : Type'} (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P x) (h2 : x = a) : term24 A P a.
Proof. exact (EQ_MP (@lem3214439 A P x a h2) (@lem3214193 A P x h1)). Qed.
Lemma lem3214468 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3214469 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3214468 A x). Qed.
Lemma lem3214470 {A : Type'} (a : A) : a = a.
Proof. exact (@lem3214469 A a). Qed.
Lemma lem3214471 {A : Type'} (a : A) : term144 A a.
Proof. exact (fun h0 : term133 A a => @lem3214470 A a). Qed.
Lemma lem3214473 (p : Prop) : (term145 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3214474 {A : Type'} (a : A) : (term144 A a) = (a = a).
Proof. exact (@lem3214473 (a = a)). Qed.
Lemma lem3214475 {A : Type'} (a : A) : a = a.
Proof. exact (EQ_MP (@lem3214474 A a) (@lem3214471 A a)). Qed.
Lemma lem3214478 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3214480 {A : Type'} (a : A) : (term133 A a) = (term146 A a).
Proof. exact (@lem3214478 (a = a)). Qed.
Lemma lem3214483 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (a : A) (h1 : term124 A a s P x) (h2 : x = a) : term146 A a.
Proof. exact (EQ_MP (@lem3214480 A a) (@lem3214252 A s P x a h1 h2)). Qed.
Lemma lem3214486 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (a : A) (h1 : term124 A a s P x) (h2 : x = a) : False.
Proof. exact (@lem3214483 A s P x a h1 h2 (@lem3214475 A a)). Qed.
Lemma lem3214487 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (a : A) (h1 : term124 A a s P x) (h2 : x = a) : term147.
Proof. exact (fun h0 : ~ False => @lem3214486 A s P x a h1 h2). Qed.
Lemma lem3214489 (p : Prop) : (term145 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3214490 : term147 = False.
Proof. exact (@lem3214489 False). Qed.
Lemma lem3214507 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (a : A) (h1 : term124 A a s P x) (h2 : x = a) : P a.
Proof. exact (EQ_MP (@lem3214331 A P x a h2) (@lem3214155 A a s P x h1)). Qed.
Lemma lem3214508 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (a : A) (h1 : term124 A a s P x) (h2 : x = a) : term148 A P a.
Proof. exact (fun h0 : term24 A P a => @lem3214507 A s P x a h1 h2). Qed.
Lemma lem3214510 (p : Prop) : (term145 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3214511 {A : Type'} (P : A -> Prop) (a : A) : (term148 A P a) = (P a).
Proof. exact (@lem3214510 (P a)). Qed.
Lemma lem3214512 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (a : A) (h1 : term124 A a s P x) (h2 : x = a) : P a.
Proof. exact (EQ_MP (@lem3214511 A P a) (@lem3214508 A s P x a h1 h2)). Qed.
Lemma lem3214515 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3214517 {A : Type'} (P : A -> Prop) (a : A) : (term24 A P a) = (term149 A P a).
Proof. exact (@lem3214515 (P a)). Qed.
Lemma lem3214520 {A : Type'} (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P x) (h2 : x = a) : term149 A P a.
Proof. exact (EQ_MP (@lem3214517 A P a) (@lem3214345 A P x a h1 h2)). Qed.
Lemma lem3214523 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P x) (h2 : term124 A a s P x) (h3 : x = a) : False.
Proof. exact (@lem3214520 A P x a h1 h3 (@lem3214512 A s P x a h2 h3)). Qed.
Lemma lem3214524 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P x) (h2 : term124 A a s P x) (h3 : x = a) : term147.
Proof. exact (fun h0 : ~ False => @lem3214523 A s P x a h1 h2 h3). Qed.
Lemma lem3214526 (p : Prop) : (term145 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3214527 : term147 = False.
Proof. exact (@lem3214526 False). Qed.
Lemma lem3214556 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3214557 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : term148 A s x.
Proof. exact (fun h0 : term24 A s x => @lem3214556 A s x h1). Qed.
Lemma lem3214559 (p : Prop) : (term145 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3214560 {A : Type'} (s : A -> Prop) (x : A) : (term148 A s x) = (s x).
Proof. exact (@lem3214559 (s x)). Qed.
Lemma lem3214561 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (EQ_MP (@lem3214560 A s x) (@lem3214557 A s x h1)). Qed.
Lemma lem3214564 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3214566 {A : Type'} (s : A -> Prop) (x : A) : (term24 A s x) = (term149 A s x).
Proof. exact (@lem3214564 (s x)). Qed.
Lemma lem3214569 {A : Type'} (s : A -> Prop) (x : A) (h1 : term24 A s x) : term149 A s x.
Proof. exact (EQ_MP (@lem3214566 A s x) (@lem3214169 A s x h1)). Qed.
Lemma lem3214572 {A : Type'} (s : A -> Prop) (x : A) (h1 : term24 A s x) (h2 : s x) : False.
Proof. exact (@lem3214569 A s x h1 (@lem3214561 A s x h2)). Qed.
Lemma lem3214573 {A : Type'} (s : A -> Prop) (x : A) (h1 : term24 A s x) (h2 : s x) : term147.
Proof. exact (fun h0 : ~ False => @lem3214572 A s x h1 h2). Qed.
Lemma lem3214575 (p : Prop) : (term145 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3214576 : term147 = False.
Proof. exact (@lem3214575 False). Qed.
Lemma lem3214577 {A : Type'} (s : A -> Prop) (x : A) (h1 : term24 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3214576) (@lem3214573 A s x h1 h2)). Qed.
Lemma lem3214605 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term124 A a s P x) : P x.
Proof. exact (proj2 (@lem3213971 A a s P x h1)). Qed.
Lemma lem3214606 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term124 A a s P x) : term148 A P x.
Proof. exact (fun h0 : term24 A P x => @lem3214605 A a s P x h1). Qed.
Lemma lem3214608 (p : Prop) : (term145 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3214609 {A : Type'} (P : A -> Prop) (x : A) : (term148 A P x) = (P x).
Proof. exact (@lem3214608 (P x)). Qed.
Lemma lem3214610 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term124 A a s P x) : P x.
Proof. exact (EQ_MP (@lem3214609 A P x) (@lem3214606 A a s P x h1)). Qed.
Lemma lem3214613 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3214615 {A : Type'} (P : A -> Prop) (x : A) : (term24 A P x) = (term149 A P x).
Proof. exact (@lem3214613 (P x)). Qed.
Lemma lem3214618 {A : Type'} (P : A -> Prop) (x : A) (h1 : term24 A P x) : term149 A P x.
Proof. exact (EQ_MP (@lem3214615 A P x) (@lem3214179 A P x h1)). Qed.
Lemma lem3214621 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term24 A P x) (h2 : term124 A a s P x) : False.
Proof. exact (@lem3214618 A P x h1 (@lem3214610 A a s P x h2)). Qed.
Lemma lem3214622 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term24 A P x) (h2 : term124 A a s P x) : term147.
Proof. exact (fun h0 : ~ False => @lem3214621 A a s P x h1 h2). Qed.
Lemma lem3214624 (p : Prop) : (term145 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3214625 : term147 = False.
Proof. exact (@lem3214624 False). Qed.
Lemma lem3214626 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term24 A P x) (h2 : term124 A a s P x) : False.
Proof. exact (EQ_MP (@lem3214625) (@lem3214622 A a s P x h1 h2)). Qed.
Lemma lem3214654 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3214655 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3214654 A x). Qed.
Lemma lem3214656 {A : Type'} (a : A) : a = a.
Proof. exact (@lem3214655 A a). Qed.
Lemma lem3214657 {A : Type'} (a : A) : term144 A a.
Proof. exact (fun h0 : term133 A a => @lem3214656 A a). Qed.
Lemma lem3214659 (p : Prop) : (term145 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3214660 {A : Type'} (a : A) : (term144 A a) = (a = a).
Proof. exact (@lem3214659 (a = a)). Qed.
Lemma lem3214661 {A : Type'} (a : A) : a = a.
Proof. exact (EQ_MP (@lem3214660 A a) (@lem3214657 A a)). Qed.
Lemma lem3214664 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3214666 {A : Type'} (a : A) : (term133 A a) = (term146 A a).
Proof. exact (@lem3214664 (a = a)). Qed.
Lemma lem3214669 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term106 A a s x) (h2 : x = a) : term146 A a.
Proof. exact (EQ_MP (@lem3214666 A a) (@lem3214386 A s x a h1 h2)). Qed.
Lemma lem3214672 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term106 A a s x) (h2 : x = a) : False.
Proof. exact (@lem3214669 A s x a h1 h2 (@lem3214661 A a)). Qed.
Lemma lem3214673 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term106 A a s x) (h2 : x = a) : term147.
Proof. exact (fun h0 : ~ False => @lem3214672 A s x a h1 h2). Qed.
Lemma lem3214675 (p : Prop) : (term145 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3214676 : term147 = False.
Proof. exact (@lem3214675 False). Qed.
Lemma lem3214679 {A : Type'} (P : A -> Prop) (a : A) (h1 : P a) : P a.
Proof. exact (h1). Qed.
Lemma lem3214680 {A : Type'} (P : A -> Prop) (a : A) (h1 : P a) : term148 A P a.
Proof. exact (fun h0 : term24 A P a => @lem3214679 A P a h1). Qed.
Lemma lem3214682 (p : Prop) : (term145 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3214683 {A : Type'} (P : A -> Prop) (a : A) : (term148 A P a) = (P a).
Proof. exact (@lem3214682 (P a)). Qed.
Lemma lem3214684 {A : Type'} (P : A -> Prop) (a : A) (h1 : P a) : P a.
Proof. exact (EQ_MP (@lem3214683 A P a) (@lem3214680 A P a h1)). Qed.
Lemma lem3214687 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3214689 {A : Type'} (P : A -> Prop) (a : A) : (term24 A P a) = (term149 A P a).
Proof. exact (@lem3214687 (P a)). Qed.
Lemma lem3214692 {A : Type'} (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P x) (h2 : x = a) : term149 A P a.
Proof. exact (EQ_MP (@lem3214689 A P a) (@lem3214440 A P x a h1 h2)). Qed.
Lemma lem3214695 {A : Type'} (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P x) (h2 : P a) (h3 : x = a) : False.
Proof. exact (@lem3214692 A P x a h1 h3 (@lem3214684 A P a h2)). Qed.
Lemma lem3214696 {A : Type'} (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P x) (h2 : P a) (h3 : x = a) : term147.
Proof. exact (fun h0 : ~ False => @lem3214695 A P x a h1 h2 h3). Qed.
Lemma lem3214698 (p : Prop) : (term145 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3214699 : term147 = False.
Proof. exact (@lem3214698 False). Qed.
Lemma lem3214700 {A : Type'} (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P x) (h2 : P a) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem3214699) (@lem3214696 A P x a h1 h2 h3)). Qed.
Lemma lem3214728 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term77 A s P x) : s x.
Proof. exact (proj1 (@lem3213985 A s P x h1)). Qed.
Lemma lem3214729 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term77 A s P x) : term148 A s x.
Proof. exact (fun h0 : term24 A s x => @lem3214728 A s P x h1). Qed.
Lemma lem3214731 (p : Prop) : (term145 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3214732 {A : Type'} (s : A -> Prop) (x : A) : (term148 A s x) = (s x).
Proof. exact (@lem3214731 (s x)). Qed.
Lemma lem3214733 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term77 A s P x) : s x.
Proof. exact (EQ_MP (@lem3214732 A s x) (@lem3214729 A s P x h1)). Qed.
Lemma lem3214736 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3214738 {A : Type'} (s : A -> Prop) (x : A) : (term24 A s x) = (term149 A s x).
Proof. exact (@lem3214736 (s x)). Qed.
Lemma lem3214741 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : term106 A a s x) : term149 A s x.
Proof. exact (EQ_MP (@lem3214738 A s x) (@lem3214203 A a s x h1)). Qed.
Lemma lem3214744 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term106 A a s x) (h2 : term77 A s P x) : False.
Proof. exact (@lem3214741 A a s x h1 (@lem3214733 A s P x h2)). Qed.
Lemma lem3214745 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term106 A a s x) (h2 : term77 A s P x) : term147.
Proof. exact (fun h0 : ~ False => @lem3214744 A a s P x h1 h2). Qed.
Lemma lem3214747 (p : Prop) : (term145 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3214748 : term147 = False.
Proof. exact (@lem3214747 False). Qed.
Lemma lem3214749 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term106 A a s x) (h2 : term77 A s P x) : False.
Proof. exact (EQ_MP (@lem3214748) (@lem3214745 A a s P x h1 h2)). Qed.
Lemma lem3214751 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term77 A s P x) : P x.
Proof. exact (proj2 (@lem3213985 A s P x h1)). Qed.
Lemma lem3214752 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term77 A s P x) : term148 A P x.
Proof. exact (fun h0 : term24 A P x => @lem3214751 A s P x h1). Qed.
Lemma lem3214754 (p : Prop) : (term145 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3214755 {A : Type'} (P : A -> Prop) (x : A) : (term148 A P x) = (P x).
Proof. exact (@lem3214754 (P x)). Qed.
Lemma lem3214756 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term77 A s P x) : P x.
Proof. exact (EQ_MP (@lem3214755 A P x) (@lem3214752 A s P x h1)). Qed.
Lemma lem3214759 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3214761 {A : Type'} (P : A -> Prop) (x : A) : (term24 A P x) = (term149 A P x).
Proof. exact (@lem3214759 (P x)). Qed.
Lemma lem3214764 {A : Type'} (P : A -> Prop) (x : A) (h1 : term24 A P x) : term149 A P x.
Proof. exact (EQ_MP (@lem3214761 A P x) (@lem3214211 A P x h1)). Qed.
Lemma lem3214767 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term24 A P x) (h2 : term77 A s P x) : False.
Proof. exact (@lem3214764 A P x h1 (@lem3214756 A s P x h2)). Qed.
Lemma lem3214768 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term24 A P x) (h2 : term77 A s P x) : term147.
Proof. exact (fun h0 : ~ False => @lem3214767 A s P x h1 h2). Qed.
Lemma lem3214770 (p : Prop) : (term145 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3214771 : term147 = False.
Proof. exact (@lem3214770 False). Qed.
Lemma lem3214772 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term24 A P x) (h2 : term77 A s P x) : False.
Proof. exact (EQ_MP (@lem3214771) (@lem3214768 A s P x h1 h2)). Qed.
Lemma lem3214773 {A : Type'} (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P x) (h2 : P a) (h3 : x = a) : (P a) = False.
Proof. exact (prop_ext (fun h4 : P a => @lem3214700 A P x a h1 h2 h3) (fun h4 : False => @lem3214427 A P a h2)). Qed.
Lemma lem3214775 {A : Type'} (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P x) (h2 : P a) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem3214773 A P x a h1 h2 h3) (@lem3214427 A P a h2)). Qed.
Lemma lem3214776 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term106 A a s x) (h2 : x = a) : False.
Proof. exact (EQ_MP (@lem3214676) (@lem3214673 A s x a h1 h2)). Qed.
Lemma lem3214777 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P x) (h2 : term124 A a s P x) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem3214527) (@lem3214524 A s P x a h1 h2 h3)). Qed.
Lemma lem3214778 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (a : A) (h1 : term124 A a s P x) (h2 : x = a) : False.
Proof. exact (EQ_MP (@lem3214490) (@lem3214487 A s P x a h1 h2)). Qed.
Lemma lem3214779 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term24 A P x) (h2 : term77 A s P x) : (term24 A P x) = False.
Proof. exact (prop_ext (fun h3 : term24 A P x => @lem3214772 A s P x h1 h2) (fun h3 : False => @lem3214211 A P x h1)). Qed.
Lemma lem3214780 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term24 A P x) (h2 : term77 A s P x) : False.
Proof. exact (EQ_MP (@lem3214779 A s P x h1 h2) (@lem3214211 A P x h1)). Qed.
Lemma lem3214781 {A : Type'} (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P x) (h2 : P a) (h3 : x = a) : (term24 A P x) = False.
Proof. exact (prop_ext (fun h4 : term24 A P x => @lem3214775 A P x a h1 h2 h3) (fun h4 : False => @lem3214193 A P x h1)). Qed.
Lemma lem3214782 {A : Type'} (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P x) (h2 : P a) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem3214781 A P x a h1 h2 h3) (@lem3214193 A P x h1)). Qed.
Lemma lem3214783 {A : Type'} (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P x) (h2 : P a) (h3 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h4 : x = a => @lem3214782 A P x a h1 h2 h3) (fun h4 : False => @lem3214191 A x a h3)). Qed.
Lemma lem3214784 {A : Type'} (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P x) (h2 : P a) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem3214783 A P x a h1 h2 h3) (@lem3214191 A x a h3)). Qed.
Lemma lem3214785 {A : Type'} (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P x) (h2 : P a) (h3 : x = a) : (P a) = False.
Proof. exact (prop_ext (fun h4 : P a => @lem3214784 A P x a h1 h2 h3) (fun h4 : False => @lem3214189 A P a h2)). Qed.
Lemma lem3214786 {A : Type'} (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P x) (h2 : P a) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem3214785 A P x a h1 h2 h3) (@lem3214189 A P a h2)). Qed.
Lemma lem3214787 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term106 A a s x) (h2 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h3 : x = a => @lem3214776 A s x a h1 h2) (fun h3 : False => @lem3214183 A x a h2)). Qed.
Lemma lem3214788 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term106 A a s x) (h2 : x = a) : False.
Proof. exact (EQ_MP (@lem3214787 A s x a h1 h2) (@lem3214183 A x a h2)). Qed.
Lemma lem3214789 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term24 A P x) (h2 : term124 A a s P x) : (term24 A P x) = False.
Proof. exact (prop_ext (fun h3 : term24 A P x => @lem3214626 A a s P x h1 h2) (fun h3 : False => @lem3214179 A P x h1)). Qed.
Lemma lem3214790 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term24 A P x) (h2 : term124 A a s P x) : False.
Proof. exact (EQ_MP (@lem3214789 A a s P x h1 h2) (@lem3214179 A P x h1)). Qed.
Lemma lem3214791 {A : Type'} (s : A -> Prop) (x : A) (h1 : term24 A s x) (h2 : s x) : (term24 A s x) = False.
Proof. exact (prop_ext (fun h3 : term24 A s x => @lem3214577 A s x h1 h2) (fun h3 : False => @lem3214169 A s x h1)). Qed.
Lemma lem3214792 {A : Type'} (s : A -> Prop) (x : A) (h1 : term24 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3214791 A s x h1 h2) (@lem3214169 A s x h1)). Qed.
Lemma lem3214793 {A : Type'} (s : A -> Prop) (x : A) (h1 : term24 A s x) (h2 : s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3214792 A s x h1 h2) (fun h3 : False => @lem3214167 A s x h2)). Qed.
Lemma lem3214794 {A : Type'} (s : A -> Prop) (x : A) (h1 : term24 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3214793 A s x h1 h2) (@lem3214167 A s x h2)). Qed.
Lemma lem3214795 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P x) (h2 : term124 A a s P x) (h3 : x = a) : (term24 A P x) = False.
Proof. exact (prop_ext (fun h4 : term24 A P x => @lem3214777 A s P x a h1 h2 h3) (fun h4 : False => @lem3214159 A P x h1)). Qed.
Lemma lem3214796 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P x) (h2 : term124 A a s P x) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem3214795 A s P x a h1 h2 h3) (@lem3214159 A P x h1)). Qed.
Lemma lem3214797 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P x) (h2 : term124 A a s P x) (h3 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h4 : x = a => @lem3214796 A s P x a h1 h2 h3) (fun h4 : False => @lem3214157 A x a h3)). Qed.
Lemma lem3214798 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P x) (h2 : term124 A a s P x) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem3214797 A s P x a h1 h2 h3) (@lem3214157 A x a h3)). Qed.
Lemma lem3214799 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (a : A) (h1 : term124 A a s P x) (h2 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h3 : x = a => @lem3214778 A s P x a h1 h2) (fun h3 : False => @lem3214147 A x a h2)). Qed.
Lemma lem3214800 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (a : A) (h1 : term124 A a s P x) (h2 : x = a) : False.
Proof. exact (EQ_MP (@lem3214799 A s P x a h1 h2) (@lem3214147 A x a h2)). Qed.
Lemma lem3214801 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term24 A P x) (h2 : term77 A s P x) : (term24 A P x) = False.
Proof. exact (prop_ext (fun h3 : term24 A P x => @lem3214780 A s P x h1 h2) (fun h3 : False => @lem3214139 A P x h1)). Qed.
Lemma lem3214802 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term24 A P x) (h2 : term77 A s P x) : False.
Proof. exact (EQ_MP (@lem3214801 A s P x h1 h2) (@lem3214139 A P x h1)). Qed.
Lemma lem3214803 {A : Type'} (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P x) (h2 : P a) (h3 : x = a) : (term24 A P x) = False.
Proof. exact (prop_ext (fun h4 : term24 A P x => @lem3214786 A P x a h1 h2 h3) (fun h4 : False => @lem3214103 A P x h1)). Qed.
Lemma lem3214804 {A : Type'} (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P x) (h2 : P a) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem3214803 A P x a h1 h2 h3) (@lem3214103 A P x h1)). Qed.
Lemma lem3214805 {A : Type'} (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P x) (h2 : P a) (h3 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h4 : x = a => @lem3214804 A P x a h1 h2 h3) (fun h4 : False => @lem3214099 A x a h3)). Qed.
Lemma lem3214806 {A : Type'} (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P x) (h2 : P a) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem3214805 A P x a h1 h2 h3) (@lem3214099 A x a h3)). Qed.
Lemma lem3214807 {A : Type'} (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P x) (h2 : P a) (h3 : x = a) : (P a) = False.
Proof. exact (prop_ext (fun h4 : P a => @lem3214806 A P x a h1 h2 h3) (fun h4 : False => @lem3214095 A P a h2)). Qed.
Lemma lem3214808 {A : Type'} (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P x) (h2 : P a) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem3214807 A P x a h1 h2 h3) (@lem3214095 A P a h2)). Qed.
Lemma lem3214809 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term106 A a s x) (h2 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h3 : x = a => @lem3214788 A s x a h1 h2) (fun h3 : False => @lem3214083 A x a h2)). Qed.
Lemma lem3214810 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term106 A a s x) (h2 : x = a) : False.
Proof. exact (EQ_MP (@lem3214809 A s x a h1 h2) (@lem3214083 A x a h2)). Qed.
Lemma lem3214811 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term24 A P x) (h2 : term124 A a s P x) : (term24 A P x) = False.
Proof. exact (prop_ext (fun h3 : term24 A P x => @lem3214790 A a s P x h1 h2) (fun h3 : False => @lem3214075 A P x h1)). Qed.
Lemma lem3214812 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term24 A P x) (h2 : term124 A a s P x) : False.
Proof. exact (EQ_MP (@lem3214811 A a s P x h1 h2) (@lem3214075 A P x h1)). Qed.
Lemma lem3214813 {A : Type'} (s : A -> Prop) (x : A) (h1 : term24 A s x) (h2 : s x) : (term24 A s x) = False.
Proof. exact (prop_ext (fun h3 : term24 A s x => @lem3214794 A s x h1 h2) (fun h3 : False => @lem3214055 A s x h1)). Qed.
Lemma lem3214814 {A : Type'} (s : A -> Prop) (x : A) (h1 : term24 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3214813 A s x h1 h2) (@lem3214055 A s x h1)). Qed.
Lemma lem3214815 {A : Type'} (s : A -> Prop) (x : A) (h1 : term24 A s x) (h2 : s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3214814 A s x h1 h2) (fun h3 : False => @lem3214051 A s x h2)). Qed.
Lemma lem3214816 {A : Type'} (s : A -> Prop) (x : A) (h1 : term24 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3214815 A s x h1 h2) (@lem3214051 A s x h2)). Qed.
Lemma lem3214817 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P x) (h2 : term124 A a s P x) (h3 : x = a) : (term24 A P x) = False.
Proof. exact (prop_ext (fun h4 : term24 A P x => @lem3214798 A s P x a h1 h2 h3) (fun h4 : False => @lem3214035 A P x h1)). Qed.
Lemma lem3214818 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P x) (h2 : term124 A a s P x) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem3214817 A s P x a h1 h2 h3) (@lem3214035 A P x h1)). Qed.
Lemma lem3214819 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P x) (h2 : term124 A a s P x) (h3 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h4 : x = a => @lem3214818 A s P x a h1 h2 h3) (fun h4 : False => @lem3214031 A x a h3)). Qed.
Lemma lem3214820 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P x) (h2 : term124 A a s P x) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem3214819 A s P x a h1 h2 h3) (@lem3214031 A x a h3)). Qed.
Lemma lem3214821 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (a : A) (h1 : term124 A a s P x) (h2 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h3 : x = a => @lem3214800 A s P x a h1 h2) (fun h3 : False => @lem3214011 A x a h2)). Qed.
Lemma lem3214822 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (a : A) (h1 : term124 A a s P x) (h2 : x = a) : False.
Proof. exact (EQ_MP (@lem3214821 A s P x a h1 h2) (@lem3214011 A x a h2)). Qed.
Lemma lem3214823 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term24 A P x) (h2 : term77 A s P x) : (term24 A P x) = False.
Proof. exact (prop_ext (fun h3 : term24 A P x => @lem3214802 A s P x h1 h2) (fun h3 : False => @lem3214139 A P x h1)). Qed.
Lemma lem3214824 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term24 A P x) (h2 : term77 A s P x) : False.
Proof. exact (EQ_MP (@lem3214823 A s P x h1 h2) (@lem3214139 A P x h1)). Qed.
Lemma lem3214825 {A : Type'} (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P x) (h2 : P a) (h3 : x = a) : (term24 A P x) = False.
Proof. exact (prop_ext (fun h4 : term24 A P x => @lem3214808 A P x a h1 h2 h3) (fun h4 : False => @lem3214103 A P x h1)). Qed.
Lemma lem3214826 {A : Type'} (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P x) (h2 : P a) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem3214825 A P x a h1 h2 h3) (@lem3214103 A P x h1)). Qed.
Lemma lem3214827 {A : Type'} (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P x) (h2 : P a) (h3 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h4 : x = a => @lem3214826 A P x a h1 h2 h3) (fun h4 : False => @lem3214099 A x a h3)). Qed.
Lemma lem3214828 {A : Type'} (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P x) (h2 : P a) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem3214827 A P x a h1 h2 h3) (@lem3214099 A x a h3)). Qed.
Lemma lem3214829 {A : Type'} (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P x) (h2 : P a) (h3 : x = a) : (P a) = False.
Proof. exact (prop_ext (fun h4 : P a => @lem3214828 A P x a h1 h2 h3) (fun h4 : False => @lem3214095 A P a h2)). Qed.
Lemma lem3214830 {A : Type'} (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P x) (h2 : P a) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem3214829 A P x a h1 h2 h3) (@lem3214095 A P a h2)). Qed.
Lemma lem3214831 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term106 A a s x) (h2 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h3 : x = a => @lem3214810 A s x a h1 h2) (fun h3 : False => @lem3214083 A x a h2)). Qed.
Lemma lem3214832 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term106 A a s x) (h2 : x = a) : False.
Proof. exact (EQ_MP (@lem3214831 A s x a h1 h2) (@lem3214083 A x a h2)). Qed.
Lemma lem3214833 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term24 A P x) (h2 : term124 A a s P x) : (term24 A P x) = False.
Proof. exact (prop_ext (fun h3 : term24 A P x => @lem3214812 A a s P x h1 h2) (fun h3 : False => @lem3214075 A P x h1)). Qed.
Lemma lem3214834 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term24 A P x) (h2 : term124 A a s P x) : False.
Proof. exact (EQ_MP (@lem3214833 A a s P x h1 h2) (@lem3214075 A P x h1)). Qed.
Lemma lem3214835 {A : Type'} (s : A -> Prop) (x : A) (h1 : term24 A s x) (h2 : s x) : (term24 A s x) = False.
Proof. exact (prop_ext (fun h3 : term24 A s x => @lem3214816 A s x h1 h2) (fun h3 : False => @lem3214055 A s x h1)). Qed.
Lemma lem3214836 {A : Type'} (s : A -> Prop) (x : A) (h1 : term24 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3214835 A s x h1 h2) (@lem3214055 A s x h1)). Qed.
Lemma lem3214837 {A : Type'} (s : A -> Prop) (x : A) (h1 : term24 A s x) (h2 : s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3214836 A s x h1 h2) (fun h3 : False => @lem3214051 A s x h2)). Qed.
Lemma lem3214838 {A : Type'} (s : A -> Prop) (x : A) (h1 : term24 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3214837 A s x h1 h2) (@lem3214051 A s x h2)). Qed.
Lemma lem3214839 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P x) (h2 : term124 A a s P x) (h3 : x = a) : (term24 A P x) = False.
Proof. exact (prop_ext (fun h4 : term24 A P x => @lem3214820 A s P x a h1 h2 h3) (fun h4 : False => @lem3214035 A P x h1)). Qed.
Lemma lem3214840 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P x) (h2 : term124 A a s P x) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem3214839 A s P x a h1 h2 h3) (@lem3214035 A P x h1)). Qed.
Lemma lem3214841 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P x) (h2 : term124 A a s P x) (h3 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h4 : x = a => @lem3214840 A s P x a h1 h2 h3) (fun h4 : False => @lem3214031 A x a h3)). Qed.
Lemma lem3214842 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P x) (h2 : term124 A a s P x) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem3214841 A s P x a h1 h2 h3) (@lem3214031 A x a h3)). Qed.
Lemma lem3214843 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (a : A) (h1 : term124 A a s P x) (h2 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h3 : x = a => @lem3214822 A s P x a h1 h2) (fun h3 : False => @lem3214011 A x a h2)). Qed.
Lemma lem3214844 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (a : A) (h1 : term124 A a s P x) (h2 : x = a) : False.
Proof. exact (EQ_MP (@lem3214843 A s P x a h1 h2) (@lem3214011 A x a h2)). Qed.
Lemma lem3214845 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term77 A s P x) (h2 : term121 A a s P x) : False.
Proof. exact (or_elim (@lem3213983 A a s P x h2) (fun h0 : term106 A a s x => @lem3214749 A a s P x h0 h1) (fun h0 : term24 A P x => @lem3214824 A s P x h0 h1)). Qed.
Lemma lem3214846 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (a : A) (h1 : P a) (h2 : term121 A a s P x) (h3 : x = a) : False.
Proof. exact (or_elim (@lem3213983 A a s P x h2) (fun h0 : term106 A a s x => @lem3214832 A s x a h0 h3) (fun h0 : term24 A P x => @lem3214830 A P x a h0 h1 h3)). Qed.
Lemma lem3214847 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : P a) (h2 : term121 A a s P x) : False.
Proof. exact (or_elim (@lem3213982 A a s P x h2) (fun h0 : x = a => @lem3214846 A s P x a h1 h2 h0) (fun h0 : term77 A s P x => @lem3214845 A a s P x h0 h2)). Qed.
Lemma lem3214848 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : s x) (h2 : term124 A a s P x) : False.
Proof. exact (or_elim (@lem3213972 A a s P x h2) (fun h0 : term24 A s x => @lem3214838 A s x h0 h1) (fun h0 : term24 A P x => @lem3214834 A a s P x h0 h2)). Qed.
Lemma lem3214849 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (a : A) (h1 : term124 A a s P x) (h2 : x = a) : False.
Proof. exact (or_elim (@lem3213972 A a s P x h1) (fun h0 : term24 A s x => @lem3214844 A s P x a h1 h2) (fun h0 : term24 A P x => @lem3214842 A s P x a h0 h1 h2)). Qed.
Lemma lem3214850 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term124 A a s P x) : False.
Proof. exact (or_elim (@lem3213975 A a s P x h1) (fun h0 : x = a => @lem3214849 A s P x a h1 h0) (fun h0 : s x => @lem3214848 A a s P x h0 h1)). Qed.
Lemma lem3214851 {A : Type'} (s : A -> Prop) (x : A) (P : A -> Prop) (a : A) (h1 : term104 A a s P x) (h2 : P a) : False.
Proof. exact (or_elim (@lem3213967 A a s P x h1) (fun h0 : term124 A a s P x => @lem3214850 A a s P x h0) (fun h0 : term121 A a s P x => @lem3214847 A a s P x h2 h0)). Qed.
Lemma lem3214852 {A : Type'} (s : A -> Prop) (x : A) (P : A -> Prop) (a : A) (h1 : term104 A a s P x) (h2 : P a) : (P a) = False.
Proof. exact (prop_ext (fun h3 : P a => @lem3214851 A s x P a h1 h2) (fun h3 : False => @lem3213877 A P a h2)). Qed.
Lemma lem3214853 {A : Type'} (s : A -> Prop) (x : A) (P : A -> Prop) (a : A) (h1 : term104 A a s P x) (h2 : P a) : False.
Proof. exact (EQ_MP (@lem3214852 A s x P a h1 h2) (@lem3213877 A P a h2)). Qed.
Lemma lem3214854 {A : Type'} (s : A -> Prop) (x : A) (P : A -> Prop) (a : A) (h1 : term104 A a s P x) (h2 : P a) : (P a) = False.
Proof. exact (prop_ext (fun h3 : P a => @lem3214853 A s x P a h1 h2) (fun h3 : False => @lem3213813 A P a h2)). Qed.
Lemma lem3214855 {A : Type'} (s : A -> Prop) (x : A) (P : A -> Prop) (a : A) (h1 : term104 A a s P x) (h2 : P a) : False.
Proof. exact (EQ_MP (@lem3214854 A s x P a h1 h2) (@lem3213813 A P a h2)). Qed.
Lemma lem3214856 {A : Type'} (s : A -> Prop) (x : A) (P : A -> Prop) (a : A) (h1 : term104 A a s P x) (h2 : P a) : (term104 A a s P x) = False.
Proof. exact (prop_ext (fun h3 : term104 A a s P x => @lem3214855 A s x P a h1 h2) (fun h3 : False => @lem3213807 A a s P x h1)). Qed.
Lemma lem3214857 {A : Type'} (s : A -> Prop) (x : A) (P : A -> Prop) (a : A) (h1 : term104 A a s P x) (h2 : P a) : False.
Proof. exact (EQ_MP (@lem3214856 A s x P a h1 h2) (@lem3213807 A a s P x h1)). Qed.
Lemma lem3214858 {A : Type'} (s : A -> Prop) (x : A) (P : A -> Prop) (a : A) (h1 : P a) : term103 A a s P x.
Proof. exact (fun h0 : term104 A a s P x => @lem3214857 A s x P a h0 h1). Qed.
Lemma lem3214859 {A : Type'} (s : A -> Prop) (x : A) (P : A -> Prop) (a : A) (h1 : P a) : (term53 A a s P x) = (term78 A a s P x).
Proof. exact (EQ_MP (@lem3213806 A a s P x) (@lem3214858 A s x P a h1)). Qed.
Lemma lem3214864 {A : Type'} (s : A -> Prop) (P : A -> Prop) (a : A) (h1 : P a) : term81 A a s P.
Proof. exact (fun x : A => @lem3214859 A s x P a h1). Qed.
Lemma lem3214865 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : term82 A a s P.
Proof. exact (fun h0 : P a => @lem3214864 A s P a h0). Qed.
Lemma lem3214870 {A : Type'} (s : A -> Prop) (P : A -> Prop) : term94 A s P.
Proof. exact (fun a : A => @lem3214865 A a s P). Qed.
Lemma lem3214875 {A : Type'} (P : A -> Prop) : term98 A P.
Proof. exact (fun s : A -> Prop => @lem3214870 A s P). Qed.
Lemma lem3214880 {A : Type'} : term102 A.
Proof. exact (fun P : A -> Prop => @lem3214875 A P). Qed.
Lemma lem3214881 {A : Type'} : term101 A.
Proof. exact (EQ_MP (@lem3213801 A) (@lem3214880 A)). Qed.
Lemma lem3214882 {A : Type'} (P : A -> Prop) : term150 A P.
Proof. exact (@lem3214881 A P). Qed.
Lemma lem3214883 {A : Type'} (P : A -> Prop) : (term150 A P) = (term97 A P).
Proof. exact (eq_refl (term150 A P)). Qed.
Lemma lem3214884 {A : Type'} (P : A -> Prop) : term97 A P.
Proof. exact (EQ_MP (@lem3214883 A P) (@lem3214882 A P)). Qed.
Lemma lem3214885 {A : Type'} (P : A -> Prop) (s : A -> Prop) : term151 A P s.
Proof. exact (@lem3214884 A P s). Qed.
Lemma lem3214886 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term151 A P s) = (term93 A s P).
Proof. exact (eq_refl (term151 A P s)). Qed.
Lemma lem3214887 {A : Type'} (s : A -> Prop) (P : A -> Prop) : term93 A s P.
Proof. exact (EQ_MP (@lem3214886 A s P) (@lem3214885 A P s)). Qed.
Lemma lem3214888 {A : Type'} (s : A -> Prop) (P : A -> Prop) (a : A) : term152 A s P a.
Proof. exact (@lem3214887 A s P a). Qed.
Lemma lem3214889 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : (term152 A s P a) = (term84 A a s P).
Proof. exact (eq_refl (term152 A s P a)). Qed.
Lemma lem3214890 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : term84 A a s P.
Proof. exact (EQ_MP (@lem3214889 A a s P) (@lem3214888 A s P a)). Qed.
Lemma lem3214892 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : term84 A a s P.
Proof. exact (@lem3213668 A a s P (@lem3214890 A a s P)). Qed.
Lemma lem3214893 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (h1 : term85 A a s P) : False.
Proof. exact (@lem3214892 A a s P (@lem3213652 A a s P h1)). Qed.
Lemma lem3214894 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (h1 : term85 A a s P) : (term85 A a s P) = False.
Proof. exact (prop_ext (fun h2 : term85 A a s P => @lem3214893 A a s P h1) (fun h2 : False => @lem3213652 A a s P h1)). Qed.
Lemma lem3214895 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (h1 : term85 A a s P) : False.
Proof. exact (EQ_MP (@lem3214894 A a s P h1) (@lem3213652 A a s P h1)). Qed.
Lemma lem3214896 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : term84 A a s P.
Proof. exact (fun h0 : term85 A a s P => @lem3214895 A a s P h0). Qed.
Lemma lem3214897 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : term82 A a s P.
Proof. exact (EQ_MP (@lem3213651 A a s P) (@lem3214896 A a s P)). Qed.
Lemma lem3214898 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : term27 A a s P.
Proof. exact (EQ_MP (@lem3213647 A a s P) (@lem3214897 A a s P)). Qed.
Lemma lem3214899 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : term17 A a s P.
Proof. exact (EQ_MP (@lem3213526 A a s P) (@lem3214898 A a s P)). Qed.
Lemma lem3214916 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term25 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3214917 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term25 A s t).
Proof. exact (@lem3214916 A s t). Qed.
Lemma lem3214918 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : ((term10 A a s P) = (term8 A s P)) = (term153 A a s P).
Proof. exact (@lem3214917 A (term10 A a s P) (term8 A s P)). Qed.
Lemma lem3214939 {A : Type'} (P : A -> Prop) (a : A) : (term11 A P a) = (term11 A P a).
Proof. exact (eq_refl (term11 A P a)). Qed.
Lemma lem3214940 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : (term13 A a s P) = (term154 A a s P).
Proof. exact (MK_COMB (@lem3214939 A P a) (@lem3214918 A a s P)). Qed.
Lemma lem3214943 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : (term154 A a s P) = (term13 A a s P).
Proof. exact (SYM (@lem3214940 A a s P)). Qed.
Lemma lem3214953 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term28 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem3214954 {A : Type'} (p : A -> Prop) (x : A) : (term28 A x p) = (p x).
Proof. exact (@lem3214953 A p x). Qed.
Lemma lem3214955 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term29 A x a s P) = (term30 A a s P x).
Proof. exact (@lem3214954 A (term31 A a s P) x). Qed.
Lemma lem3214956 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term30 A a s P x) = (term32 A a s P x).
Proof. exact (eq_refl (term30 A a s P x)). Qed.
Lemma lem3214957 {A : Type'} (GEN_PVAR_8 : A) : (@SETSPEC A GEN_PVAR_8) = (@SETSPEC A GEN_PVAR_8).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_8)). Qed.
Lemma lem3214958 {A : Type'} (GEN_PVAR_8 : A) (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term33 A GEN_PVAR_8 a s P x) = (term34 A GEN_PVAR_8 a s P x).
Proof. exact (MK_COMB (@lem3214957 A GEN_PVAR_8) (@lem3214956 A a s P x)). Qed.
Lemma lem3214959 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3214960 {A : Type'} (GEN_PVAR_8 : A) (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term35 A GEN_PVAR_8 a s P x) = (term36 A GEN_PVAR_8 a s P x).
Proof. exact (MK_COMB (@lem3214958 A GEN_PVAR_8 a s P x) (@lem3214959 A x)). Qed.
Lemma lem3214961 {A : Type'} (GEN_PVAR_8 : A) (a : A) (s : A -> Prop) (P : A -> Prop) : (term37 A GEN_PVAR_8 a s P) = (term38 A GEN_PVAR_8 a s P).
Proof. exact (fun_ext (fun x : A => @lem3214960 A GEN_PVAR_8 a s P x)). Qed.
Lemma lem3214962 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3214963 {A : Type'} (GEN_PVAR_8 : A) (a : A) (s : A -> Prop) (P : A -> Prop) : (term39 A GEN_PVAR_8 a s P) = (term40 A GEN_PVAR_8 a s P).
Proof. exact (MK_COMB (@lem3214962 A) (@lem3214961 A GEN_PVAR_8 a s P)). Qed.
Lemma lem3214964 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : (term41 A a s P) = (term42 A a s P).
Proof. exact (fun_ext (fun GEN_PVAR_8 : A => @lem3214963 A GEN_PVAR_8 a s P)). Qed.
Lemma lem3214965 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem3214966 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : (term43 A a s P) = (term10 A a s P).
Proof. exact (MK_COMB (@lem3214965 A) (@lem3214964 A a s P)). Qed.
Lemma lem3214967 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem3214968 {A : Type'} (x : A) (a : A) (s : A -> Prop) (P : A -> Prop) : (term29 A x a s P) = (term44 A x a s P).
Proof. exact (MK_COMB (@lem3214967 A x) (@lem3214966 A a s P)). Qed.
Lemma lem3214969 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3214970 {A : Type'} (x : A) (a : A) (s : A -> Prop) (P : A -> Prop) : (term45 A x a s P) = (term46 A x a s P).
Proof. exact (MK_COMB (@lem3214969) (@lem3214968 A x a s P)). Qed.
Lemma lem3214971 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term30 A a s P x) = (term32 A a s P x).
Proof. exact (eq_refl (term30 A a s P x)). Qed.
Lemma lem3214972 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) : ((term29 A x a s P) = (term30 A a s P x)) = ((term44 A x a s P) = (term32 A a s P x)).
Proof. exact (MK_COMB (@lem3214970 A x a s P) (@lem3214971 A a s P x)). Qed.
Lemma lem3214973 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term44 A x a s P) = (term32 A a s P x).
Proof. exact (EQ_MP (@lem3214972 A a s P x) (@lem3214955 A a s P x)). Qed.
Lemma lem3214977 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term47 A x y s) = (term48 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3214978 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term47 A x y s) = (term48 A y x s).
Proof. exact (@lem3214977 A y x s). Qed.
Lemma lem3214979 {A : Type'} (a : A) (x : A) (s : A -> Prop) : (term47 A x a s) = (term48 A a x s).
Proof. exact (@lem3214978 A a x s). Qed.
Lemma lem3214985 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3214986 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3214985 A P x). Qed.
Lemma lem3214987 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3214986 A s x). Qed.
Lemma lem3214988 {A : Type'} (x : A) (a : A) : (term49 A x a) = (term49 A x a).
Proof. exact (eq_refl (term49 A x a)). Qed.
Lemma lem3214989 {A : Type'} (a : A) (s : A -> Prop) (x : A) : (term48 A a x s) = (term50 A a s x).
Proof. exact (MK_COMB (@lem3214988 A x a) (@lem3214987 A s x)). Qed.
Lemma lem3214992 {A : Type'} (a : A) (s : A -> Prop) (x : A) : (term47 A x a s) = (term50 A a s x).
Proof. exact (TRANS (@lem3214979 A a x s) (@lem3214989 A a s x)). Qed.
Lemma lem3214993 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3214994 {A : Type'} (a : A) (s : A -> Prop) (x : A) : (term51 A x a s) = (term52 A a s x).
Proof. exact (MK_COMB (@lem3214993) (@lem3214992 A a s x)). Qed.
Lemma lem3214995 {A : Type'} (P : A -> Prop) (x : A) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem3214996 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term32 A a s P x) = (term53 A a s P x).
Proof. exact (MK_COMB (@lem3214994 A a s x) (@lem3214995 A P x)). Qed.
Lemma lem3214999 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term44 A x a s P) = (term53 A a s P x).
Proof. exact (TRANS (@lem3214973 A a s P x) (@lem3214996 A a s P x)). Qed.
Lemma lem3215000 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3215001 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term46 A x a s P) = (term54 A a s P x).
Proof. exact (MK_COMB (@lem3215000) (@lem3214999 A a s P x)). Qed.
Lemma lem3215003 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term28 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem3215004 {A : Type'} (p : A -> Prop) (x : A) : (term28 A x p) = (p x).
Proof. exact (@lem3215003 A p x). Qed.
Lemma lem3215005 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term57 A x s P) = (term58 A s P x).
Proof. exact (@lem3215004 A (term59 A s P) x). Qed.
Lemma lem3215006 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term58 A s P x) = (term60 A s P x).
Proof. exact (eq_refl (term58 A s P x)). Qed.
Lemma lem3215007 {A : Type'} (GEN_PVAR_10 : A) : (@SETSPEC A GEN_PVAR_10) = (@SETSPEC A GEN_PVAR_10).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_10)). Qed.
Lemma lem3215008 {A : Type'} (GEN_PVAR_10 : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term61 A GEN_PVAR_10 s P x) = (term62 A GEN_PVAR_10 s P x).
Proof. exact (MK_COMB (@lem3215007 A GEN_PVAR_10) (@lem3215006 A s P x)). Qed.
Lemma lem3215009 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3215010 {A : Type'} (GEN_PVAR_10 : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term63 A GEN_PVAR_10 s P x) = (term64 A GEN_PVAR_10 s P x).
Proof. exact (MK_COMB (@lem3215008 A GEN_PVAR_10 s P x) (@lem3215009 A x)). Qed.
Lemma lem3215011 {A : Type'} (GEN_PVAR_10 : A) (s : A -> Prop) (P : A -> Prop) : (term65 A GEN_PVAR_10 s P) = (term66 A GEN_PVAR_10 s P).
Proof. exact (fun_ext (fun x : A => @lem3215010 A GEN_PVAR_10 s P x)). Qed.
Lemma lem3215012 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3215013 {A : Type'} (GEN_PVAR_10 : A) (s : A -> Prop) (P : A -> Prop) : (term67 A GEN_PVAR_10 s P) = (term68 A GEN_PVAR_10 s P).
Proof. exact (MK_COMB (@lem3215012 A) (@lem3215011 A GEN_PVAR_10 s P)). Qed.
Lemma lem3215014 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term69 A s P) = (term70 A s P).
Proof. exact (fun_ext (fun GEN_PVAR_10 : A => @lem3215013 A GEN_PVAR_10 s P)). Qed.
Lemma lem3215015 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem3215016 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term71 A s P) = (term8 A s P).
Proof. exact (MK_COMB (@lem3215015 A) (@lem3215014 A s P)). Qed.
Lemma lem3215017 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem3215018 {A : Type'} (x : A) (s : A -> Prop) (P : A -> Prop) : (term57 A x s P) = (term72 A x s P).
Proof. exact (MK_COMB (@lem3215017 A x) (@lem3215016 A s P)). Qed.
Lemma lem3215019 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3215020 {A : Type'} (x : A) (s : A -> Prop) (P : A -> Prop) : (term73 A x s P) = (term74 A x s P).
Proof. exact (MK_COMB (@lem3215019) (@lem3215018 A x s P)). Qed.
Lemma lem3215021 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term58 A s P x) = (term60 A s P x).
Proof. exact (eq_refl (term58 A s P x)). Qed.
Lemma lem3215022 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : ((term57 A x s P) = (term58 A s P x)) = ((term72 A x s P) = (term60 A s P x)).
Proof. exact (MK_COMB (@lem3215020 A x s P) (@lem3215021 A s P x)). Qed.
Lemma lem3215023 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term72 A x s P) = (term60 A s P x).
Proof. exact (EQ_MP (@lem3215022 A s P x) (@lem3215005 A s P x)). Qed.
Lemma lem3215027 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3215028 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3215027 A P x). Qed.
Lemma lem3215029 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3215028 A s x). Qed.
Lemma lem3215030 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3215031 {A : Type'} (s : A -> Prop) (x : A) : (term75 A x s) = (term76 A s x).
Proof. exact (MK_COMB (@lem3215030) (@lem3215029 A s x)). Qed.
Lemma lem3215032 {A : Type'} (P : A -> Prop) (x : A) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem3215033 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term60 A s P x) = (term77 A s P x).
Proof. exact (MK_COMB (@lem3215031 A s x) (@lem3215032 A P x)). Qed.
Lemma lem3215036 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term72 A x s P) = (term77 A s P x).
Proof. exact (TRANS (@lem3215023 A s P x) (@lem3215033 A s P x)). Qed.
Lemma lem3215037 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) : ((term44 A x a s P) = (term72 A x s P)) = ((term53 A a s P x) = (term77 A s P x)).
Proof. exact (MK_COMB (@lem3215001 A a s P x) (@lem3215036 A s P x)). Qed.
Lemma lem3215040 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : (term155 A a s P) = (term156 A a s P).
Proof. exact (fun_ext (fun x : A => @lem3215037 A a s P x)). Qed.
Lemma lem3215041 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3215042 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : (term153 A a s P) = (term157 A a s P).
Proof. exact (MK_COMB (@lem3215041 A) (@lem3215040 A a s P)). Qed.
Lemma lem3215047 {A : Type'} (P : A -> Prop) (a : A) : (term11 A P a) = (term11 A P a).
Proof. exact (eq_refl (term11 A P a)). Qed.
Lemma lem3215048 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : (term154 A a s P) = (term158 A a s P).
Proof. exact (MK_COMB (@lem3215047 A P a) (@lem3215042 A a s P)). Qed.
Lemma lem3215051 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : (term158 A a s P) = (term154 A a s P).
Proof. exact (SYM (@lem3215048 A a s P)). Qed.
Lemma lem3215053 (p : Prop) : p = (term83 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3215054 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : (term158 A a s P) = (term159 A a s P).
Proof. exact (@lem3215053 (term158 A a s P)). Qed.
Lemma lem3215055 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : (term159 A a s P) = (term158 A a s P).
Proof. exact (SYM (@lem3215054 A a s P)). Qed.
Lemma lem3215056 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (h1 : term160 A a s P) : term160 A a s P.
Proof. exact (h1). Qed.
Lemma lem3215059 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (h1 : term159 A a s P) : term159 A a s P.
Proof. exact (h1). Qed.
Lemma lem3215060 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : term161 A a s P.
Proof. exact (fun h0 : term159 A a s P => @lem3215059 A a s P h0). Qed.
Lemma lem3215061 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (h1 : term161 A a s P) : term161 A a s P.
Proof. exact (h1). Qed.
Lemma lem3215062 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (h1 : term159 A a s P) : term159 A a s P.
Proof. exact (h1). Qed.
Lemma lem3215063 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (h1 : term159 A a s P) (h2 : term161 A a s P) : term159 A a s P.
Proof. exact (@lem3215061 A a s P h2 (@lem3215062 A a s P h1)). Qed.
Lemma lem3215064 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (h1 : term159 A a s P) : term162 A a s P.
Proof. exact (fun h0 : term161 A a s P => @lem3215063 A a s P h1 h0). Qed.
Lemma lem3215065 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (h1 : term161 A a s P) : term161 A a s P.
Proof. exact (h1). Qed.
Lemma lem3215066 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (h1 : term159 A a s P) (h2 : term161 A a s P) : term159 A a s P.
Proof. exact (@lem3215064 A a s P h1 (@lem3215065 A a s P h2)). Qed.
Lemma lem3215067 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (h1 : term161 A a s P) : term161 A a s P.
Proof. exact (fun h0 : term159 A a s P => @lem3215066 A a s P h0 h1). Qed.
Lemma lem3215068 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : term163 A a s P.
Proof. exact (fun h0 : term161 A a s P => @lem3215067 A a s P h0). Qed.
Lemma lem3215071 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : term161 A a s P.
Proof. exact (@lem3215068 A a s P (@lem3215060 A a s P)). Qed.
Lemma lem3215072 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : term161 A a s P.
Proof. exact (@lem3215071 A a s P). Qed.
Lemma lem3215086 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3215087 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : (term159 A a s P) = (term164 A a s P).
Proof. exact (@lem3215086 (term160 A a s P)). Qed.
Lemma lem3215089 (t : Prop) : (term90 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3215090 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : (term164 A a s P) = (term158 A a s P).
Proof. exact (@lem3215089 (term158 A a s P)). Qed.
Lemma lem3215093 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : (term159 A a s P) = (term158 A a s P).
Proof. exact (TRANS (@lem3215087 A a s P) (@lem3215090 A a s P)). Qed.
Lemma lem3215104 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term165 A s P) = (term166 A s P).
Proof. exact (fun_ext (fun a : A => @lem3215093 A a s P)). Qed.
Lemma lem3215105 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3215106 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term167 A s P) = (term168 A s P).
Proof. exact (MK_COMB (@lem3215105 A) (@lem3215104 A s P)). Qed.
Lemma lem3215111 {A : Type'} (P : A -> Prop) : (term169 A P) = (term170 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3215106 A s P)). Qed.
Lemma lem3215112 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3215113 {A : Type'} (P : A -> Prop) : (term171 A P) = (term172 A P).
Proof. exact (MK_COMB (@lem3215112 A) (@lem3215111 A P)). Qed.
Lemma lem3215118 {A : Type'} : (term173 A) = (term174 A).
Proof. exact (fun_ext (fun P : A -> Prop => @lem3215113 A P)). Qed.
Lemma lem3215119 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3215128 {A : Type'} : (term175 A) = (term176 A).
Proof. exact (MK_COMB (@lem3215119 A) (@lem3215118 A)). Qed.
Lemma lem3215145 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) : ((term53 A a s P x) = (term77 A s P x)) = ((term53 A a s P x) = (term77 A s P x)).
Proof. exact (eq_refl ((term53 A a s P x) = (term77 A s P x))). Qed.
Lemma lem3215146 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : (term156 A a s P) = (term156 A a s P).
Proof. exact (fun_ext (fun x : A => @lem3215145 A a s P x)). Qed.
Lemma lem3215147 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3215148 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : (term157 A a s P) = (term157 A a s P).
Proof. exact (MK_COMB (@lem3215147 A) (@lem3215146 A a s P)). Qed.
Lemma lem3215153 {A : Type'} (P : A -> Prop) (a : A) : (term11 A P a) = (term11 A P a).
Proof. exact (eq_refl (term11 A P a)). Qed.
Lemma lem3215154 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : (term158 A a s P) = (term158 A a s P).
Proof. exact (MK_COMB (@lem3215153 A P a) (@lem3215148 A a s P)). Qed.
Lemma lem3215155 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term166 A s P) = (term166 A s P).
Proof. exact (fun_ext (fun a : A => @lem3215154 A a s P)). Qed.
Lemma lem3215156 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3215157 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term168 A s P) = (term168 A s P).
Proof. exact (MK_COMB (@lem3215156 A) (@lem3215155 A s P)). Qed.
Lemma lem3215158 {A : Type'} (P : A -> Prop) : (term170 A P) = (term170 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3215157 A s P)). Qed.
Lemma lem3215159 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3215160 {A : Type'} (P : A -> Prop) : (term172 A P) = (term172 A P).
Proof. exact (MK_COMB (@lem3215159 A) (@lem3215158 A P)). Qed.
Lemma lem3215161 {A : Type'} : (term174 A) = (term174 A).
Proof. exact (fun_ext (fun P : A -> Prop => @lem3215160 A P)). Qed.
Lemma lem3215162 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3215163 {A : Type'} : (term176 A) = (term176 A).
Proof. exact (MK_COMB (@lem3215162 A) (@lem3215161 A)). Qed.
Lemma lem3215198 {A : Type'} : (term175 A) = (term176 A).
Proof. exact (TRANS (@lem3215128 A) (@lem3215163 A)). Qed.
Lemma lem3215199 {A : Type'} : (term176 A) = (term175 A).
Proof. exact (SYM (@lem3215198 A)). Qed.
Lemma lem3215202 (p : Prop) : p = (term83 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3215203 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) : ((term53 A a s P x) = (term77 A s P x)) = (term177 A a s P x).
Proof. exact (@lem3215202 ((term53 A a s P x) = (term77 A s P x))). Qed.
Lemma lem3215204 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term177 A a s P x) = ((term53 A a s P x) = (term77 A s P x)).
Proof. exact (SYM (@lem3215203 A a s P x)). Qed.
Lemma lem3215205 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term178 A a s P x) : term178 A a s P x.
Proof. exact (h1). Qed.
Lemma lem3215211 {A : Type'} (P : A -> Prop) (a : A) (h1 : term24 A P a) : term24 A P a.
Proof. exact (h1). Qed.
Lemma lem3215220 {A : Type'} (a : A) (s : A -> Prop) (x : A) : (term105 A a s x) = (term106 A a s x).
Proof. exact (@lem17160 (x = a) (s x)). Qed.
Lemma lem3215224 {A : Type'} (P : A -> Prop) (x : A) : (term24 A P x) = (term24 A P x).
Proof. exact (eq_refl (term24 A P x)). Qed.
Lemma lem3215226 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3215227 {A : Type'} (a : A) (s : A -> Prop) (x : A) : (term107 A a s x) = (term108 A a s x).
Proof. exact (MK_COMB (@lem3215226) (@lem3215220 A a s x)). Qed.
Lemma lem3215228 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term109 A a s P x) = (term110 A a s P x).
Proof. exact (MK_COMB (@lem3215227 A a s x) (@lem3215224 A P x)). Qed.
Lemma lem3215229 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term111 A a s P x) = (term109 A a s P x).
Proof. exact (@lem17045 (term50 A a s x) (P x)). Qed.
Lemma lem3215230 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term111 A a s P x) = (term110 A a s P x).
Proof. exact (TRANS (@lem3215229 A a s P x) (@lem3215228 A a s P x)). Qed.
Lemma lem3215242 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term112 A s P x) = (term113 A s P x).
Proof. exact (@lem17045 (s x) (P x)). Qed.
Lemma lem3215245 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term77 A s P x) = (term77 A s P x).
Proof. exact (eq_refl (term77 A s P x)). Qed.
Lemma lem3215246 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3215247 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term118 A a s P x) = (term119 A a s P x).
Proof. exact (MK_COMB (@lem3215246) (@lem3215230 A a s P x)). Qed.
Lemma lem3215248 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term179 A a s P x) = (term180 A a s P x).
Proof. exact (MK_COMB (@lem3215247 A a s P x) (@lem3215245 A s P x)). Qed.
Lemma lem3215250 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term122 A a s P x) = (term122 A a s P x).
Proof. exact (eq_refl (term122 A a s P x)). Qed.
Lemma lem3215251 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term181 A a s P x) = (term182 A a s P x).
Proof. exact (MK_COMB (@lem3215250 A a s P x) (@lem3215242 A s P x)). Qed.
Lemma lem3215252 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3215253 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term183 A a s P x) = (term184 A a s P x).
Proof. exact (MK_COMB (@lem3215252) (@lem3215251 A a s P x)). Qed.
Lemma lem3215254 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term185 A a s P x) = (term186 A a s P x).
Proof. exact (MK_COMB (@lem3215253 A a s P x) (@lem3215248 A a s P x)). Qed.
Lemma lem3215255 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term178 A a s P x) = (term185 A a s P x).
Proof. exact (@lem17646 (term53 A a s P x) (term77 A s P x)). Qed.
Lemma lem3215260 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term178 A a s P x) = (term186 A a s P x).
Proof. exact (TRANS (@lem3215255 A a s P x) (@lem3215254 A a s P x)). Qed.
Lemma lem3215267 {A : Type'} (P : A -> Prop) (a : A) (h1 : term24 A P a) : term24 A P a.
Proof. exact (h1). Qed.
Lemma lem3215339 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term178 A a s P x) : term186 A a s P x.
Proof. exact (EQ_MP (@lem3215260 A a s P x) (@lem3215205 A a s P x h1)). Qed.
Lemma lem3215340 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term182 A a s P x) : term182 A a s P x.
Proof. exact (h1). Qed.
Lemma lem3215341 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term180 A a s P x) : term180 A a s P x.
Proof. exact (h1). Qed.
Lemma lem3215342 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term182 A a s P x) : term113 A s P x.
Proof. exact (proj2 (@lem3215340 A a s P x h1)). Qed.
Lemma lem3215343 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term182 A a s P x) : term53 A a s P x.
Proof. exact (proj1 (@lem3215340 A a s P x h1)). Qed.
Lemma lem3215345 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term182 A a s P x) : term50 A a s x.
Proof. exact (proj1 (@lem3215343 A a s P x h1)). Qed.
Lemma lem3215352 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term180 A a s P x) : term77 A s P x.
Proof. exact (proj2 (@lem3215341 A a s P x h1)). Qed.
Lemma lem3215353 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term180 A a s P x) : term110 A a s P x.
Proof. exact (proj1 (@lem3215341 A a s P x h1)). Qed.
Lemma lem3215356 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : term106 A a s x) : term106 A a s x.
Proof. exact (h1). Qed.
Lemma lem3215363 {A : Type'} (P : A -> Prop) (a : A) (h1 : term24 A P a) : term24 A P a.
Proof. exact (h1). Qed.
Lemma lem3215371 {A : Type'} (x : A) (a : A) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem3215387 {A : Type'} (x : A) (a : A) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem3215391 {A : Type'} (P : A -> Prop) (x : A) (h1 : term24 A P x) : term24 A P x.
Proof. exact (h1). Qed.
Lemma lem3215403 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3215407 {A : Type'} (s : A -> Prop) (x : A) (h1 : term24 A s x) : term24 A s x.
Proof. exact (h1). Qed.
Lemma lem3215423 {A : Type'} (P : A -> Prop) (x : A) (h1 : term24 A P x) : term24 A P x.
Proof. exact (h1). Qed.
Lemma lem3215459 {A : Type'} (P : A -> Prop) (x : A) (h1 : term24 A P x) : term24 A P x.
Proof. exact (h1). Qed.
Lemma lem3215461 {A : Type'} (P : A -> Prop) (a : A) (h1 : term24 A P a) : term24 A P a.
Proof. exact (h1). Qed.
Lemma lem3215463 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term182 A a s P x) : P x.
Proof. exact (proj2 (@lem3215343 A a s P x h1)). Qed.
Lemma lem3215465 {A : Type'} (x : A) (a : A) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem3215471 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term182 A a s P x) : P x.
Proof. exact (proj2 (@lem3215343 A a s P x h1)). Qed.
Lemma lem3215473 {A : Type'} (x : A) (a : A) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem3215475 {A : Type'} (P : A -> Prop) (x : A) (h1 : term24 A P x) : term24 A P x.
Proof. exact (h1). Qed.
Lemma lem3215481 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3215483 {A : Type'} (s : A -> Prop) (x : A) (h1 : term24 A s x) : term24 A s x.
Proof. exact (h1). Qed.
Lemma lem3215491 {A : Type'} (P : A -> Prop) (x : A) (h1 : term24 A P x) : term24 A P x.
Proof. exact (h1). Qed.
Lemma lem3215501 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : term106 A a s x) : term24 A s x.
Proof. exact (proj2 (@lem3215356 A a s x h1)). Qed.
Lemma lem3215509 {A : Type'} (P : A -> Prop) (x : A) (h1 : term24 A P x) : term24 A P x.
Proof. exact (h1). Qed.
Lemma lem3215537 {A : Type'} (P : A -> Prop) (a : A) (h1 : term24 A P a) : term24 A P a.
Proof. exact (h1). Qed.
Lemma lem3215538 {A : Type'} (P : A -> Prop) : (term136 A P) = (term136 A P).
Proof. exact (eq_refl (term136 A P)). Qed.
Lemma lem3215539 {A : Type'} (P : A -> Prop) (x : A) (a : A) (h1 : x = a) : (term137 A P x) = (term137 A P a).
Proof. exact (MK_COMB (@lem3215538 A P) (@lem3215465 A x a h1)). Qed.
Lemma lem3215540 {A : Type'} (P : A -> Prop) (a : A) : (term137 A P a) = (P a).
Proof. exact (eq_refl (term137 A P a)). Qed.
Lemma lem3215541 {A : Type'} (P : A -> Prop) (x : A) : (term138 A P x) = (term138 A P x).
Proof. exact (eq_refl (term138 A P x)). Qed.
Lemma lem3215542 {A : Type'} (x : A) (P : A -> Prop) (a : A) : ((term137 A P x) = (term137 A P a)) = ((term137 A P x) = (P a)).
Proof. exact (MK_COMB (@lem3215541 A P x) (@lem3215540 A P a)). Qed.
Lemma lem3215543 {A : Type'} (P : A -> Prop) (x : A) : (term137 A P x) = (P x).
Proof. exact (eq_refl (term137 A P x)). Qed.
Lemma lem3215544 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3215545 {A : Type'} (P : A -> Prop) (x : A) : (term138 A P x) = (term139 A P x).
Proof. exact (MK_COMB (@lem3215544) (@lem3215543 A P x)). Qed.
Lemma lem3215546 {A : Type'} (P : A -> Prop) (a : A) : (P a) = (P a).
Proof. exact (eq_refl (P a)). Qed.
Lemma lem3215547 {A : Type'} (x : A) (P : A -> Prop) (a : A) : ((term137 A P x) = (P a)) = ((P x) = (P a)).
Proof. exact (MK_COMB (@lem3215545 A P x) (@lem3215546 A P a)). Qed.
Lemma lem3215548 {A : Type'} (x : A) (P : A -> Prop) (a : A) : ((term137 A P x) = (term137 A P a)) = ((P x) = (P a)).
Proof. exact (TRANS (@lem3215542 A x P a) (@lem3215547 A x P a)). Qed.
Lemma lem3215549 {A : Type'} (P : A -> Prop) (x : A) (a : A) (h1 : x = a) : (P x) = (P a).
Proof. exact (EQ_MP (@lem3215548 A x P a) (@lem3215539 A P x a h1)). Qed.
Lemma lem3215592 {A : Type'} (P : A -> Prop) : (term136 A P) = (term136 A P).
Proof. exact (eq_refl (term136 A P)). Qed.
Lemma lem3215593 {A : Type'} (P : A -> Prop) (x : A) (a : A) (h1 : x = a) : (term137 A P x) = (term137 A P a).
Proof. exact (MK_COMB (@lem3215592 A P) (@lem3215473 A x a h1)). Qed.
Lemma lem3215594 {A : Type'} (P : A -> Prop) (a : A) : (term137 A P a) = (P a).
Proof. exact (eq_refl (term137 A P a)). Qed.
Lemma lem3215595 {A : Type'} (P : A -> Prop) (x : A) : (term138 A P x) = (term138 A P x).
Proof. exact (eq_refl (term138 A P x)). Qed.
Lemma lem3215596 {A : Type'} (x : A) (P : A -> Prop) (a : A) : ((term137 A P x) = (term137 A P a)) = ((term137 A P x) = (P a)).
Proof. exact (MK_COMB (@lem3215595 A P x) (@lem3215594 A P a)). Qed.
Lemma lem3215597 {A : Type'} (P : A -> Prop) (x : A) : (term137 A P x) = (P x).
Proof. exact (eq_refl (term137 A P x)). Qed.
Lemma lem3215598 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3215599 {A : Type'} (P : A -> Prop) (x : A) : (term138 A P x) = (term139 A P x).
Proof. exact (MK_COMB (@lem3215598) (@lem3215597 A P x)). Qed.
Lemma lem3215600 {A : Type'} (P : A -> Prop) (a : A) : (P a) = (P a).
Proof. exact (eq_refl (P a)). Qed.
Lemma lem3215601 {A : Type'} (x : A) (P : A -> Prop) (a : A) : ((term137 A P x) = (P a)) = ((P x) = (P a)).
Proof. exact (MK_COMB (@lem3215599 A P x) (@lem3215600 A P a)). Qed.
Lemma lem3215602 {A : Type'} (x : A) (P : A -> Prop) (a : A) : ((term137 A P x) = (term137 A P a)) = ((P x) = (P a)).
Proof. exact (TRANS (@lem3215596 A x P a) (@lem3215601 A x P a)). Qed.
Lemma lem3215603 {A : Type'} (P : A -> Prop) (x : A) (a : A) (h1 : x = a) : (P x) = (P a).
Proof. exact (EQ_MP (@lem3215602 A x P a) (@lem3215593 A P x a h1)). Qed.
Lemma lem3215605 {A : Type'} (P : A -> Prop) : (term140 A P) = (term140 A P).
Proof. exact (eq_refl (term140 A P)). Qed.
Lemma lem3215606 {A : Type'} (P : A -> Prop) (x : A) (a : A) (h1 : x = a) : (term141 A P x) = (term141 A P a).
Proof. exact (MK_COMB (@lem3215605 A P) (@lem3215473 A x a h1)). Qed.
Lemma lem3215607 {A : Type'} (P : A -> Prop) (a : A) : (term141 A P a) = (term24 A P a).
Proof. exact (eq_refl (term141 A P a)). Qed.
Lemma lem3215608 {A : Type'} (P : A -> Prop) (x : A) : (term142 A P x) = (term142 A P x).
Proof. exact (eq_refl (term142 A P x)). Qed.
Lemma lem3215609 {A : Type'} (x : A) (P : A -> Prop) (a : A) : ((term141 A P x) = (term141 A P a)) = ((term141 A P x) = (term24 A P a)).
Proof. exact (MK_COMB (@lem3215608 A P x) (@lem3215607 A P a)). Qed.
Lemma lem3215610 {A : Type'} (P : A -> Prop) (x : A) : (term141 A P x) = (term24 A P x).
Proof. exact (eq_refl (term141 A P x)). Qed.
Lemma lem3215611 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3215612 {A : Type'} (P : A -> Prop) (x : A) : (term142 A P x) = (term143 A P x).
Proof. exact (MK_COMB (@lem3215611) (@lem3215610 A P x)). Qed.
Lemma lem3215613 {A : Type'} (P : A -> Prop) (a : A) : (term24 A P a) = (term24 A P a).
Proof. exact (eq_refl (term24 A P a)). Qed.
Lemma lem3215614 {A : Type'} (x : A) (P : A -> Prop) (a : A) : ((term141 A P x) = (term24 A P a)) = ((term24 A P x) = (term24 A P a)).
Proof. exact (MK_COMB (@lem3215612 A P x) (@lem3215613 A P a)). Qed.
Lemma lem3215615 {A : Type'} (x : A) (P : A -> Prop) (a : A) : ((term141 A P x) = (term141 A P a)) = ((term24 A P x) = (term24 A P a)).
Proof. exact (TRANS (@lem3215609 A x P a) (@lem3215614 A x P a)). Qed.
Lemma lem3215616 {A : Type'} (P : A -> Prop) (x : A) (a : A) (h1 : x = a) : (term24 A P x) = (term24 A P a).
Proof. exact (EQ_MP (@lem3215615 A x P a) (@lem3215606 A P x a h1)). Qed.
Lemma lem3215617 {A : Type'} (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P x) (h2 : x = a) : term24 A P a.
Proof. exact (EQ_MP (@lem3215616 A P x a h2) (@lem3215475 A P x h1)). Qed.
Lemma lem3215619 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (a : A) (h1 : term182 A a s P x) (h2 : x = a) : P a.
Proof. exact (EQ_MP (@lem3215549 A P x a h2) (@lem3215463 A a s P x h1)). Qed.
Lemma lem3215620 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (a : A) (h1 : term182 A a s P x) (h2 : x = a) : term148 A P a.
Proof. exact (fun h0 : term24 A P a => @lem3215619 A s P x a h1 h2). Qed.
Lemma lem3215622 (p : Prop) : (term145 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3215623 {A : Type'} (P : A -> Prop) (a : A) : (term148 A P a) = (P a).
Proof. exact (@lem3215622 (P a)). Qed.
Lemma lem3215624 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (a : A) (h1 : term182 A a s P x) (h2 : x = a) : P a.
Proof. exact (EQ_MP (@lem3215623 A P a) (@lem3215620 A s P x a h1 h2)). Qed.
Lemma lem3215627 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3215629 {A : Type'} (P : A -> Prop) (a : A) : (term24 A P a) = (term149 A P a).
Proof. exact (@lem3215627 (P a)). Qed.
Lemma lem3215632 {A : Type'} (P : A -> Prop) (a : A) (h1 : term24 A P a) : term149 A P a.
Proof. exact (EQ_MP (@lem3215629 A P a) (@lem3215537 A P a h1)). Qed.
Lemma lem3215635 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P a) (h2 : term182 A a s P x) (h3 : x = a) : False.
Proof. exact (@lem3215632 A P a h1 (@lem3215624 A s P x a h2 h3)). Qed.
Lemma lem3215636 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P a) (h2 : term182 A a s P x) (h3 : x = a) : term147.
Proof. exact (fun h0 : ~ False => @lem3215635 A s P x a h1 h2 h3). Qed.
Lemma lem3215638 (p : Prop) : (term145 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3215639 : term147 = False.
Proof. exact (@lem3215638 False). Qed.
Lemma lem3215640 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P a) (h2 : term182 A a s P x) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem3215639) (@lem3215636 A s P x a h1 h2 h3)). Qed.
Lemma lem3215642 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (a : A) (h1 : term182 A a s P x) (h2 : x = a) : P a.
Proof. exact (EQ_MP (@lem3215603 A P x a h2) (@lem3215471 A a s P x h1)). Qed.
Lemma lem3215643 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (a : A) (h1 : term182 A a s P x) (h2 : x = a) : term148 A P a.
Proof. exact (fun h0 : term24 A P a => @lem3215642 A s P x a h1 h2). Qed.
Lemma lem3215645 (p : Prop) : (term145 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3215646 {A : Type'} (P : A -> Prop) (a : A) : (term148 A P a) = (P a).
Proof. exact (@lem3215645 (P a)). Qed.
Lemma lem3215647 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (a : A) (h1 : term182 A a s P x) (h2 : x = a) : P a.
Proof. exact (EQ_MP (@lem3215646 A P a) (@lem3215643 A s P x a h1 h2)). Qed.
Lemma lem3215650 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3215652 {A : Type'} (P : A -> Prop) (a : A) : (term24 A P a) = (term149 A P a).
Proof. exact (@lem3215650 (P a)). Qed.
Lemma lem3215655 {A : Type'} (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P x) (h2 : x = a) : term149 A P a.
Proof. exact (EQ_MP (@lem3215652 A P a) (@lem3215617 A P x a h1 h2)). Qed.
Lemma lem3215658 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P x) (h2 : term182 A a s P x) (h3 : x = a) : False.
Proof. exact (@lem3215655 A P x a h1 h3 (@lem3215647 A s P x a h2 h3)). Qed.
Lemma lem3215659 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P x) (h2 : term182 A a s P x) (h3 : x = a) : term147.
Proof. exact (fun h0 : ~ False => @lem3215658 A s P x a h1 h2 h3). Qed.
Lemma lem3215661 (p : Prop) : (term145 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3215662 : term147 = False.
Proof. exact (@lem3215661 False). Qed.
Lemma lem3215665 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3215666 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : term148 A s x.
Proof. exact (fun h0 : term24 A s x => @lem3215665 A s x h1). Qed.
Lemma lem3215668 (p : Prop) : (term145 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3215669 {A : Type'} (s : A -> Prop) (x : A) : (term148 A s x) = (s x).
Proof. exact (@lem3215668 (s x)). Qed.
Lemma lem3215670 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (EQ_MP (@lem3215669 A s x) (@lem3215666 A s x h1)). Qed.
Lemma lem3215673 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3215675 {A : Type'} (s : A -> Prop) (x : A) : (term24 A s x) = (term149 A s x).
Proof. exact (@lem3215673 (s x)). Qed.
Lemma lem3215678 {A : Type'} (s : A -> Prop) (x : A) (h1 : term24 A s x) : term149 A s x.
Proof. exact (EQ_MP (@lem3215675 A s x) (@lem3215483 A s x h1)). Qed.
Lemma lem3215681 {A : Type'} (s : A -> Prop) (x : A) (h1 : term24 A s x) (h2 : s x) : False.
Proof. exact (@lem3215678 A s x h1 (@lem3215670 A s x h2)). Qed.
Lemma lem3215682 {A : Type'} (s : A -> Prop) (x : A) (h1 : term24 A s x) (h2 : s x) : term147.
Proof. exact (fun h0 : ~ False => @lem3215681 A s x h1 h2). Qed.
Lemma lem3215684 (p : Prop) : (term145 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3215685 : term147 = False.
Proof. exact (@lem3215684 False). Qed.
Lemma lem3215686 {A : Type'} (s : A -> Prop) (x : A) (h1 : term24 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3215685) (@lem3215682 A s x h1 h2)). Qed.
Lemma lem3215688 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term182 A a s P x) : P x.
Proof. exact (proj2 (@lem3215343 A a s P x h1)). Qed.
Lemma lem3215689 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term182 A a s P x) : term148 A P x.
Proof. exact (fun h0 : term24 A P x => @lem3215688 A a s P x h1). Qed.
Lemma lem3215691 (p : Prop) : (term145 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3215692 {A : Type'} (P : A -> Prop) (x : A) : (term148 A P x) = (P x).
Proof. exact (@lem3215691 (P x)). Qed.
Lemma lem3215693 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term182 A a s P x) : P x.
Proof. exact (EQ_MP (@lem3215692 A P x) (@lem3215689 A a s P x h1)). Qed.
Lemma lem3215696 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3215698 {A : Type'} (P : A -> Prop) (x : A) : (term24 A P x) = (term149 A P x).
Proof. exact (@lem3215696 (P x)). Qed.
Lemma lem3215701 {A : Type'} (P : A -> Prop) (x : A) (h1 : term24 A P x) : term149 A P x.
Proof. exact (EQ_MP (@lem3215698 A P x) (@lem3215491 A P x h1)). Qed.
Lemma lem3215704 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term24 A P x) (h2 : term182 A a s P x) : False.
Proof. exact (@lem3215701 A P x h1 (@lem3215693 A a s P x h2)). Qed.
Lemma lem3215705 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term24 A P x) (h2 : term182 A a s P x) : term147.
Proof. exact (fun h0 : ~ False => @lem3215704 A a s P x h1 h2). Qed.
Lemma lem3215707 (p : Prop) : (term145 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3215708 : term147 = False.
Proof. exact (@lem3215707 False). Qed.
Lemma lem3215709 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term24 A P x) (h2 : term182 A a s P x) : False.
Proof. exact (EQ_MP (@lem3215708) (@lem3215705 A a s P x h1 h2)). Qed.
Lemma lem3215737 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term180 A a s P x) : s x.
Proof. exact (proj1 (@lem3215352 A a s P x h1)). Qed.
Lemma lem3215738 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term180 A a s P x) : term148 A s x.
Proof. exact (fun h0 : term24 A s x => @lem3215737 A a s P x h1). Qed.
Lemma lem3215740 (p : Prop) : (term145 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3215741 {A : Type'} (s : A -> Prop) (x : A) : (term148 A s x) = (s x).
Proof. exact (@lem3215740 (s x)). Qed.
Lemma lem3215742 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term180 A a s P x) : s x.
Proof. exact (EQ_MP (@lem3215741 A s x) (@lem3215738 A a s P x h1)). Qed.
Lemma lem3215745 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3215747 {A : Type'} (s : A -> Prop) (x : A) : (term24 A s x) = (term149 A s x).
Proof. exact (@lem3215745 (s x)). Qed.
Lemma lem3215750 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : term106 A a s x) : term149 A s x.
Proof. exact (EQ_MP (@lem3215747 A s x) (@lem3215501 A a s x h1)). Qed.
Lemma lem3215753 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term106 A a s x) (h2 : term180 A a s P x) : False.
Proof. exact (@lem3215750 A a s x h1 (@lem3215742 A a s P x h2)). Qed.
Lemma lem3215754 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term106 A a s x) (h2 : term180 A a s P x) : term147.
Proof. exact (fun h0 : ~ False => @lem3215753 A a s P x h1 h2). Qed.
Lemma lem3215756 (p : Prop) : (term145 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3215757 : term147 = False.
Proof. exact (@lem3215756 False). Qed.
Lemma lem3215758 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term106 A a s x) (h2 : term180 A a s P x) : False.
Proof. exact (EQ_MP (@lem3215757) (@lem3215754 A a s P x h1 h2)). Qed.
Lemma lem3215760 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term180 A a s P x) : P x.
Proof. exact (proj2 (@lem3215352 A a s P x h1)). Qed.
Lemma lem3215761 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term180 A a s P x) : term148 A P x.
Proof. exact (fun h0 : term24 A P x => @lem3215760 A a s P x h1). Qed.
Lemma lem3215763 (p : Prop) : (term145 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3215764 {A : Type'} (P : A -> Prop) (x : A) : (term148 A P x) = (P x).
Proof. exact (@lem3215763 (P x)). Qed.
Lemma lem3215765 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term180 A a s P x) : P x.
Proof. exact (EQ_MP (@lem3215764 A P x) (@lem3215761 A a s P x h1)). Qed.
Lemma lem3215768 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3215770 {A : Type'} (P : A -> Prop) (x : A) : (term24 A P x) = (term149 A P x).
Proof. exact (@lem3215768 (P x)). Qed.
Lemma lem3215773 {A : Type'} (P : A -> Prop) (x : A) (h1 : term24 A P x) : term149 A P x.
Proof. exact (EQ_MP (@lem3215770 A P x) (@lem3215509 A P x h1)). Qed.
Lemma lem3215776 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term24 A P x) (h2 : term180 A a s P x) : False.
Proof. exact (@lem3215773 A P x h1 (@lem3215765 A a s P x h2)). Qed.
Lemma lem3215777 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term24 A P x) (h2 : term180 A a s P x) : term147.
Proof. exact (fun h0 : ~ False => @lem3215776 A a s P x h1 h2). Qed.
Lemma lem3215779 (p : Prop) : (term145 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3215780 : term147 = False.
Proof. exact (@lem3215779 False). Qed.
Lemma lem3215781 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term24 A P x) (h2 : term180 A a s P x) : False.
Proof. exact (EQ_MP (@lem3215780) (@lem3215777 A a s P x h1 h2)). Qed.
Lemma lem3215782 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P x) (h2 : term182 A a s P x) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem3215662) (@lem3215659 A s P x a h1 h2 h3)). Qed.
Lemma lem3215783 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P a) (h2 : term182 A a s P x) (h3 : x = a) : (term24 A P a) = False.
Proof. exact (prop_ext (fun h4 : term24 A P a => @lem3215640 A s P x a h1 h2 h3) (fun h4 : False => @lem3215537 A P a h1)). Qed.
Lemma lem3215785 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P a) (h2 : term182 A a s P x) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem3215783 A s P x a h1 h2 h3) (@lem3215537 A P a h1)). Qed.
Lemma lem3215786 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term24 A P x) (h2 : term180 A a s P x) : (term24 A P x) = False.
Proof. exact (prop_ext (fun h3 : term24 A P x => @lem3215781 A a s P x h1 h2) (fun h3 : False => @lem3215509 A P x h1)). Qed.
Lemma lem3215787 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term24 A P x) (h2 : term180 A a s P x) : False.
Proof. exact (EQ_MP (@lem3215786 A a s P x h1 h2) (@lem3215509 A P x h1)). Qed.
Lemma lem3215788 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term24 A P x) (h2 : term182 A a s P x) : (term24 A P x) = False.
Proof. exact (prop_ext (fun h3 : term24 A P x => @lem3215709 A a s P x h1 h2) (fun h3 : False => @lem3215491 A P x h1)). Qed.
Lemma lem3215789 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term24 A P x) (h2 : term182 A a s P x) : False.
Proof. exact (EQ_MP (@lem3215788 A a s P x h1 h2) (@lem3215491 A P x h1)). Qed.
Lemma lem3215790 {A : Type'} (s : A -> Prop) (x : A) (h1 : term24 A s x) (h2 : s x) : (term24 A s x) = False.
Proof. exact (prop_ext (fun h3 : term24 A s x => @lem3215686 A s x h1 h2) (fun h3 : False => @lem3215483 A s x h1)). Qed.
Lemma lem3215791 {A : Type'} (s : A -> Prop) (x : A) (h1 : term24 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3215790 A s x h1 h2) (@lem3215483 A s x h1)). Qed.
Lemma lem3215792 {A : Type'} (s : A -> Prop) (x : A) (h1 : term24 A s x) (h2 : s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3215791 A s x h1 h2) (fun h3 : False => @lem3215481 A s x h2)). Qed.
Lemma lem3215793 {A : Type'} (s : A -> Prop) (x : A) (h1 : term24 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3215792 A s x h1 h2) (@lem3215481 A s x h2)). Qed.
Lemma lem3215794 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P x) (h2 : term182 A a s P x) (h3 : x = a) : (term24 A P x) = False.
Proof. exact (prop_ext (fun h4 : term24 A P x => @lem3215782 A s P x a h1 h2 h3) (fun h4 : False => @lem3215475 A P x h1)). Qed.
Lemma lem3215795 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P x) (h2 : term182 A a s P x) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem3215794 A s P x a h1 h2 h3) (@lem3215475 A P x h1)). Qed.
Lemma lem3215796 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P x) (h2 : term182 A a s P x) (h3 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h4 : x = a => @lem3215795 A s P x a h1 h2 h3) (fun h4 : False => @lem3215473 A x a h3)). Qed.
Lemma lem3215797 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P x) (h2 : term182 A a s P x) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem3215796 A s P x a h1 h2 h3) (@lem3215473 A x a h3)). Qed.
Lemma lem3215798 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P a) (h2 : term182 A a s P x) (h3 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h4 : x = a => @lem3215785 A s P x a h1 h2 h3) (fun h4 : False => @lem3215465 A x a h3)). Qed.
Lemma lem3215799 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P a) (h2 : term182 A a s P x) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem3215798 A s P x a h1 h2 h3) (@lem3215465 A x a h3)). Qed.
Lemma lem3215800 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P a) (h2 : term182 A a s P x) (h3 : x = a) : (term24 A P a) = False.
Proof. exact (prop_ext (fun h4 : term24 A P a => @lem3215799 A s P x a h1 h2 h3) (fun h4 : False => @lem3215461 A P a h1)). Qed.
Lemma lem3215801 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P a) (h2 : term182 A a s P x) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem3215800 A s P x a h1 h2 h3) (@lem3215461 A P a h1)). Qed.
Lemma lem3215802 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term24 A P x) (h2 : term180 A a s P x) : (term24 A P x) = False.
Proof. exact (prop_ext (fun h3 : term24 A P x => @lem3215787 A a s P x h1 h2) (fun h3 : False => @lem3215459 A P x h1)). Qed.
Lemma lem3215803 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term24 A P x) (h2 : term180 A a s P x) : False.
Proof. exact (EQ_MP (@lem3215802 A a s P x h1 h2) (@lem3215459 A P x h1)). Qed.
Lemma lem3215804 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term24 A P x) (h2 : term182 A a s P x) : (term24 A P x) = False.
Proof. exact (prop_ext (fun h3 : term24 A P x => @lem3215789 A a s P x h1 h2) (fun h3 : False => @lem3215423 A P x h1)). Qed.
Lemma lem3215805 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term24 A P x) (h2 : term182 A a s P x) : False.
Proof. exact (EQ_MP (@lem3215804 A a s P x h1 h2) (@lem3215423 A P x h1)). Qed.
Lemma lem3215806 {A : Type'} (s : A -> Prop) (x : A) (h1 : term24 A s x) (h2 : s x) : (term24 A s x) = False.
Proof. exact (prop_ext (fun h3 : term24 A s x => @lem3215793 A s x h1 h2) (fun h3 : False => @lem3215407 A s x h1)). Qed.
Lemma lem3215807 {A : Type'} (s : A -> Prop) (x : A) (h1 : term24 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3215806 A s x h1 h2) (@lem3215407 A s x h1)). Qed.
Lemma lem3215808 {A : Type'} (s : A -> Prop) (x : A) (h1 : term24 A s x) (h2 : s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3215807 A s x h1 h2) (fun h3 : False => @lem3215403 A s x h2)). Qed.
Lemma lem3215809 {A : Type'} (s : A -> Prop) (x : A) (h1 : term24 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3215808 A s x h1 h2) (@lem3215403 A s x h2)). Qed.
Lemma lem3215810 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P x) (h2 : term182 A a s P x) (h3 : x = a) : (term24 A P x) = False.
Proof. exact (prop_ext (fun h4 : term24 A P x => @lem3215797 A s P x a h1 h2 h3) (fun h4 : False => @lem3215391 A P x h1)). Qed.
Lemma lem3215811 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P x) (h2 : term182 A a s P x) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem3215810 A s P x a h1 h2 h3) (@lem3215391 A P x h1)). Qed.
Lemma lem3215812 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P x) (h2 : term182 A a s P x) (h3 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h4 : x = a => @lem3215811 A s P x a h1 h2 h3) (fun h4 : False => @lem3215387 A x a h3)). Qed.
Lemma lem3215813 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P x) (h2 : term182 A a s P x) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem3215812 A s P x a h1 h2 h3) (@lem3215387 A x a h3)). Qed.
Lemma lem3215814 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P a) (h2 : term182 A a s P x) (h3 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h4 : x = a => @lem3215801 A s P x a h1 h2 h3) (fun h4 : False => @lem3215371 A x a h3)). Qed.
Lemma lem3215815 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P a) (h2 : term182 A a s P x) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem3215814 A s P x a h1 h2 h3) (@lem3215371 A x a h3)). Qed.
Lemma lem3215816 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P a) (h2 : term182 A a s P x) (h3 : x = a) : (term24 A P a) = False.
Proof. exact (prop_ext (fun h4 : term24 A P a => @lem3215815 A s P x a h1 h2 h3) (fun h4 : False => @lem3215363 A P a h1)). Qed.
Lemma lem3215817 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P a) (h2 : term182 A a s P x) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem3215816 A s P x a h1 h2 h3) (@lem3215363 A P a h1)). Qed.
Lemma lem3215818 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term24 A P x) (h2 : term180 A a s P x) : (term24 A P x) = False.
Proof. exact (prop_ext (fun h3 : term24 A P x => @lem3215803 A a s P x h1 h2) (fun h3 : False => @lem3215459 A P x h1)). Qed.
Lemma lem3215819 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term24 A P x) (h2 : term180 A a s P x) : False.
Proof. exact (EQ_MP (@lem3215818 A a s P x h1 h2) (@lem3215459 A P x h1)). Qed.
Lemma lem3215820 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term24 A P x) (h2 : term182 A a s P x) : (term24 A P x) = False.
Proof. exact (prop_ext (fun h3 : term24 A P x => @lem3215805 A a s P x h1 h2) (fun h3 : False => @lem3215423 A P x h1)). Qed.
Lemma lem3215821 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term24 A P x) (h2 : term182 A a s P x) : False.
Proof. exact (EQ_MP (@lem3215820 A a s P x h1 h2) (@lem3215423 A P x h1)). Qed.
Lemma lem3215822 {A : Type'} (s : A -> Prop) (x : A) (h1 : term24 A s x) (h2 : s x) : (term24 A s x) = False.
Proof. exact (prop_ext (fun h3 : term24 A s x => @lem3215809 A s x h1 h2) (fun h3 : False => @lem3215407 A s x h1)). Qed.
Lemma lem3215823 {A : Type'} (s : A -> Prop) (x : A) (h1 : term24 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3215822 A s x h1 h2) (@lem3215407 A s x h1)). Qed.
Lemma lem3215824 {A : Type'} (s : A -> Prop) (x : A) (h1 : term24 A s x) (h2 : s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3215823 A s x h1 h2) (fun h3 : False => @lem3215403 A s x h2)). Qed.
Lemma lem3215825 {A : Type'} (s : A -> Prop) (x : A) (h1 : term24 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3215824 A s x h1 h2) (@lem3215403 A s x h2)). Qed.
Lemma lem3215826 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P x) (h2 : term182 A a s P x) (h3 : x = a) : (term24 A P x) = False.
Proof. exact (prop_ext (fun h4 : term24 A P x => @lem3215813 A s P x a h1 h2 h3) (fun h4 : False => @lem3215391 A P x h1)). Qed.
Lemma lem3215827 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P x) (h2 : term182 A a s P x) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem3215826 A s P x a h1 h2 h3) (@lem3215391 A P x h1)). Qed.
Lemma lem3215828 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P x) (h2 : term182 A a s P x) (h3 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h4 : x = a => @lem3215827 A s P x a h1 h2 h3) (fun h4 : False => @lem3215387 A x a h3)). Qed.
Lemma lem3215829 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P x) (h2 : term182 A a s P x) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem3215828 A s P x a h1 h2 h3) (@lem3215387 A x a h3)). Qed.
Lemma lem3215830 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P a) (h2 : term182 A a s P x) (h3 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h4 : x = a => @lem3215817 A s P x a h1 h2 h3) (fun h4 : False => @lem3215371 A x a h3)). Qed.
Lemma lem3215831 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P a) (h2 : term182 A a s P x) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem3215830 A s P x a h1 h2 h3) (@lem3215371 A x a h3)). Qed.
Lemma lem3215832 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P a) (h2 : term182 A a s P x) (h3 : x = a) : (term24 A P a) = False.
Proof. exact (prop_ext (fun h4 : term24 A P a => @lem3215831 A s P x a h1 h2 h3) (fun h4 : False => @lem3215363 A P a h1)). Qed.
Lemma lem3215833 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P a) (h2 : term182 A a s P x) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem3215832 A s P x a h1 h2 h3) (@lem3215363 A P a h1)). Qed.
Lemma lem3215834 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term180 A a s P x) : False.
Proof. exact (or_elim (@lem3215353 A a s P x h1) (fun h0 : term106 A a s x => @lem3215758 A a s P x h0 h1) (fun h0 : term24 A P x => @lem3215819 A a s P x h0 h1)). Qed.
Lemma lem3215835 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : s x) (h2 : term182 A a s P x) : False.
Proof. exact (or_elim (@lem3215342 A a s P x h2) (fun h0 : term24 A s x => @lem3215825 A s x h0 h1) (fun h0 : term24 A P x => @lem3215821 A a s P x h0 h2)). Qed.
Lemma lem3215836 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (a : A) (h1 : term24 A P a) (h2 : term182 A a s P x) (h3 : x = a) : False.
Proof. exact (or_elim (@lem3215342 A a s P x h2) (fun h0 : term24 A s x => @lem3215833 A s P x a h1 h2 h3) (fun h0 : term24 A P x => @lem3215829 A s P x a h0 h2 h3)). Qed.
Lemma lem3215837 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term24 A P a) (h2 : term182 A a s P x) : False.
Proof. exact (or_elim (@lem3215345 A a s P x h2) (fun h0 : x = a => @lem3215836 A s P x a h1 h2 h0) (fun h0 : s x => @lem3215835 A a s P x h0 h2)). Qed.
Lemma lem3215838 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term24 A P a) (h2 : term178 A a s P x) : False.
Proof. exact (or_elim (@lem3215339 A a s P x h2) (fun h0 : term182 A a s P x => @lem3215837 A a s P x h1 h0) (fun h0 : term180 A a s P x => @lem3215834 A a s P x h0)). Qed.
Lemma lem3215839 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term24 A P a) (h2 : term178 A a s P x) : (term24 A P a) = False.
Proof. exact (prop_ext (fun h3 : term24 A P a => @lem3215838 A a s P x h1 h2) (fun h3 : False => @lem3215267 A P a h1)). Qed.
Lemma lem3215840 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term24 A P a) (h2 : term178 A a s P x) : False.
Proof. exact (EQ_MP (@lem3215839 A a s P x h1 h2) (@lem3215267 A P a h1)). Qed.
Lemma lem3215841 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term24 A P a) (h2 : term178 A a s P x) : (term24 A P a) = False.
Proof. exact (prop_ext (fun h3 : term24 A P a => @lem3215840 A a s P x h1 h2) (fun h3 : False => @lem3215211 A P a h1)). Qed.
Lemma lem3215842 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term24 A P a) (h2 : term178 A a s P x) : False.
Proof. exact (EQ_MP (@lem3215841 A a s P x h1 h2) (@lem3215211 A P a h1)). Qed.
Lemma lem3215843 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term24 A P a) (h2 : term178 A a s P x) : (term178 A a s P x) = False.
Proof. exact (prop_ext (fun h3 : term178 A a s P x => @lem3215842 A a s P x h1 h2) (fun h3 : False => @lem3215205 A a s P x h2)). Qed.
Lemma lem3215844 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term24 A P a) (h2 : term178 A a s P x) : False.
Proof. exact (EQ_MP (@lem3215843 A a s P x h1 h2) (@lem3215205 A a s P x h2)). Qed.
Lemma lem3215845 {A : Type'} (s : A -> Prop) (x : A) (P : A -> Prop) (a : A) (h1 : term24 A P a) : term177 A a s P x.
Proof. exact (fun h0 : term178 A a s P x => @lem3215844 A a s P x h1 h0). Qed.
Lemma lem3215846 {A : Type'} (s : A -> Prop) (x : A) (P : A -> Prop) (a : A) (h1 : term24 A P a) : (term53 A a s P x) = (term77 A s P x).
Proof. exact (EQ_MP (@lem3215204 A a s P x) (@lem3215845 A s x P a h1)). Qed.
Lemma lem3215851 {A : Type'} (s : A -> Prop) (P : A -> Prop) (a : A) (h1 : term24 A P a) : term157 A a s P.
Proof. exact (fun x : A => @lem3215846 A s x P a h1). Qed.
Lemma lem3215852 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : term158 A a s P.
Proof. exact (fun h0 : term24 A P a => @lem3215851 A s P a h0). Qed.
Lemma lem3215857 {A : Type'} (s : A -> Prop) (P : A -> Prop) : term168 A s P.
Proof. exact (fun a : A => @lem3215852 A a s P). Qed.
Lemma lem3215862 {A : Type'} (P : A -> Prop) : term172 A P.
Proof. exact (fun s : A -> Prop => @lem3215857 A s P). Qed.
Lemma lem3215867 {A : Type'} : term176 A.
Proof. exact (fun P : A -> Prop => @lem3215862 A P). Qed.
Lemma lem3215868 {A : Type'} : term175 A.
Proof. exact (EQ_MP (@lem3215199 A) (@lem3215867 A)). Qed.
Lemma lem3215869 {A : Type'} (P : A -> Prop) : term187 A P.
Proof. exact (@lem3215868 A P). Qed.
Lemma lem3215870 {A : Type'} (P : A -> Prop) : (term187 A P) = (term171 A P).
Proof. exact (eq_refl (term187 A P)). Qed.
Lemma lem3215871 {A : Type'} (P : A -> Prop) : term171 A P.
Proof. exact (EQ_MP (@lem3215870 A P) (@lem3215869 A P)). Qed.
Lemma lem3215872 {A : Type'} (P : A -> Prop) (s : A -> Prop) : term188 A P s.
Proof. exact (@lem3215871 A P s). Qed.
Lemma lem3215873 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term188 A P s) = (term167 A s P).
Proof. exact (eq_refl (term188 A P s)). Qed.
Lemma lem3215874 {A : Type'} (s : A -> Prop) (P : A -> Prop) : term167 A s P.
Proof. exact (EQ_MP (@lem3215873 A s P) (@lem3215872 A P s)). Qed.
Lemma lem3215875 {A : Type'} (s : A -> Prop) (P : A -> Prop) (a : A) : term189 A s P a.
Proof. exact (@lem3215874 A s P a). Qed.
Lemma lem3215876 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : (term189 A s P a) = (term159 A a s P).
Proof. exact (eq_refl (term189 A s P a)). Qed.
Lemma lem3215877 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : term159 A a s P.
Proof. exact (EQ_MP (@lem3215876 A a s P) (@lem3215875 A s P a)). Qed.
Lemma lem3215879 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : term159 A a s P.
Proof. exact (@lem3215072 A a s P (@lem3215877 A a s P)). Qed.
Lemma lem3215880 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (h1 : term160 A a s P) : False.
Proof. exact (@lem3215879 A a s P (@lem3215056 A a s P h1)). Qed.
Lemma lem3215881 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (h1 : term160 A a s P) : (term160 A a s P) = False.
Proof. exact (prop_ext (fun h2 : term160 A a s P => @lem3215880 A a s P h1) (fun h2 : False => @lem3215056 A a s P h1)). Qed.
Lemma lem3215882 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) (h1 : term160 A a s P) : False.
Proof. exact (EQ_MP (@lem3215881 A a s P h1) (@lem3215056 A a s P h1)). Qed.
Lemma lem3215883 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : term159 A a s P.
Proof. exact (fun h0 : term160 A a s P => @lem3215882 A a s P h0). Qed.
Lemma lem3215884 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : term158 A a s P.
Proof. exact (EQ_MP (@lem3215055 A a s P) (@lem3215883 A a s P)). Qed.
Lemma lem3215885 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : term154 A a s P.
Proof. exact (EQ_MP (@lem3215051 A a s P) (@lem3215884 A a s P)). Qed.
Lemma lem3215886 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : term13 A a s P.
Proof. exact (EQ_MP (@lem3214943 A a s P) (@lem3215885 A a s P)). Qed.
Lemma lem3215888 {A : Type'} (s : A -> Prop) (P : A -> Prop) (a : A) (h1 : term24 A P a) : (term10 A a s P) = (term8 A s P).
Proof. exact (@lem3215886 A a s P (@lem3213467 A P a h1)). Qed.
Lemma lem3215889 {A : Type'} (s : A -> Prop) (P : A -> Prop) (a : A) (h1 : term24 A P a) : (term24 A P a) = ((term10 A a s P) = (term8 A s P)).
Proof. exact (prop_ext (fun h2 : term24 A P a => @lem3215888 A s P a h1) (fun h2 : (term10 A a s P) = (term8 A s P) => @lem3213467 A P a h1)). Qed.
Lemma lem3215890 {A : Type'} (s : A -> Prop) (P : A -> Prop) (a : A) (h1 : term24 A P a) : (term10 A a s P) = (term8 A s P).
Proof. exact (EQ_MP (@lem3215889 A s P a h1) (@lem3213467 A P a h1)). Qed.
Lemma lem3215891 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : term13 A a s P.
Proof. exact (fun h0 : term24 A P a => @lem3215890 A s P a h0). Qed.
Lemma lem3215892 {A : Type'} (s : A -> Prop) (P : A -> Prop) (a : A) (h1 : P a) : (term10 A a s P) = (term7 A a s P).
Proof. exact (@lem3214899 A a s P (@lem3213450 A P a h1)). Qed.
Lemma lem3215893 {A : Type'} (s : A -> Prop) (P : A -> Prop) (a : A) (h1 : P a) : (P a) = ((term10 A a s P) = (term7 A a s P)).
Proof. exact (prop_ext (fun h2 : P a => @lem3215892 A s P a h1) (fun h2 : (term10 A a s P) = (term7 A a s P) => @lem3213450 A P a h1)). Qed.
Lemma lem3215894 {A : Type'} (s : A -> Prop) (P : A -> Prop) (a : A) (h1 : P a) : (term10 A a s P) = (term7 A a s P).
Proof. exact (EQ_MP (@lem3215893 A s P a h1) (@lem3213450 A P a h1)). Qed.
Lemma lem3215895 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : term17 A a s P.
Proof. exact (fun h0 : P a => @lem3215894 A s P a h0). Qed.
Lemma lem3215896 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : term20 A a s P.
Proof. exact (conj (@lem3215895 A a s P) (@lem3215891 A a s P)). Qed.
Lemma lem3215897 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : (term10 A a s P) = (term21 A a s P).
Proof. exact (EQ_MP (@lem3213449 A a s P) (@lem3215896 A a s P)). Qed.
Lemma lem3215902 {A : Type'} (s : A -> Prop) (P : A -> Prop) : term190 A s P.
Proof. exact (fun a : A => @lem3215897 A a s P). Qed.
Lemma lem3215907 {A : Type'} (P : A -> Prop) : term191 A P.
Proof. exact (fun s : A -> Prop => @lem3215902 A s P). Qed.
Lemma lem3215912 {A : Type'} : term192 A.
Proof. exact (fun P : A -> Prop => @lem3215907 A P). Qed.
