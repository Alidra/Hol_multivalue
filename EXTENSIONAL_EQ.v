Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EXTENSIONAL_EQ_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import FUN_EQ_THM_spec.
Require Import IN_EXTENSIONAL_UNDEFINED_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Lemma lem4383467 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem4383468 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem4383469 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem4383468 t1) (@lem4383467 t1)). Qed.
Lemma lem4383470 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem4383469 t1 t2). Qed.
Lemma lem4383471 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem4383472 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem4383471 t1 t2) (@lem4383470 t1 t2)). Qed.
Lemma lem4383473 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem4383472 t1 t2 t3). Qed.
Lemma lem4383474 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem4383475 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem4383474 t1 t2 t3) (@lem4383473 t1 t2 t3)). Qed.
Lemma lem4383476 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem4383475 t1 t2 t3)). Qed.
Lemma lem4383477 {A : Type'} (x : A) (s : A -> Prop) : term7 A x s.
Proof. exact (@lem9784 (@IN A x s)). Qed.
Lemma lem4383478 {A : Type'} (x : A) (s : A -> Prop) : (term7 A x s) = (term8 A x s).
Proof. exact (eq_refl (term7 A x s)). Qed.
Lemma lem4383479 {A : Type'} (x : A) (s : A -> Prop) : term8 A x s.
Proof. exact (EQ_MP (@lem4383478 A x s) (@lem4383477 A x s)). Qed.
Lemma lem4383480 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem4383481 {A : Type'} (x : A) (s : A -> Prop) (h1 : term9 A x s) : term9 A x s.
Proof. exact (h1). Qed.
Lemma lem4383482 {A B : Type'} (f : A -> B) : term10 A B f.
Proof. exact (@lem9220 A B f). Qed.
Lemma lem4383483 {A B : Type'} (f : A -> B) : (term10 A B f) = (term11 A B f).
Proof. exact (eq_refl (term10 A B f)). Qed.
Lemma lem4383484 {A B : Type'} (f : A -> B) : term11 A B f.
Proof. exact (EQ_MP (@lem4383483 A B f) (@lem4383482 A B f)). Qed.
Lemma lem4383485 {A B : Type'} (f : A -> B) (g : A -> B) : term12 A B f g.
Proof. exact (@lem4383484 A B f g). Qed.
Lemma lem4383486 {A B : Type'} (f : A -> B) (g : A -> B) : (term12 A B f g) = ((f = g) = (term13 A B f g)).
Proof. exact (eq_refl (term12 A B f g)). Qed.
Lemma lem4383488 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term14 A B s f g) : term14 A B s f g.
Proof. exact (h1). Qed.
Lemma lem4383489 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term15 A B s f g) : term15 A B s f g.
Proof. exact (h1). Qed.
Lemma lem4383490 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term16 A B f s) : term16 A B f s.
Proof. exact (h1). Qed.
Lemma lem4383491 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term17 A B s f g) : term17 A B s f g.
Proof. exact (h1). Qed.
Lemma lem4383492 {A B : Type'} (g : A -> B) (s : A -> Prop) (h1 : term16 A B g s) : term16 A B g s.
Proof. exact (h1). Qed.
Lemma lem4383496 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term13 A B f g).
Proof. exact (EQ_MP (@lem4383486 A B f g) (@lem4383485 A B f g)). Qed.
Lemma lem4383497 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term13 A B f g).
Proof. exact (@lem4383496 A B f g). Qed.
Lemma lem4383506 {A B : Type'} (f : A -> B) (g : A -> B) : (term13 A B f g) = (f = g).
Proof. exact (SYM (@lem4383497 A B f g)). Qed.
Lemma lem4383511 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term17 A B s f g) : term18 A B s f g x.
Proof. exact (@lem4383491 A B s f g h1 x). Qed.
Lemma lem4383512 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term18 A B s f g x) = (term19 A B s f g x).
Proof. exact (eq_refl (term18 A B s f g x)). Qed.
Lemma lem4383513 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term17 A B s f g) : term19 A B s f g x.
Proof. exact (EQ_MP (@lem4383512 A B s f g x) (@lem4383511 A B x s f g h1)). Qed.
Lemma lem4383514 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem4383515 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) (s : A -> Prop) (h1 : term17 A B s f g) (h2 : @IN A x s) : (f x) = (g x).
Proof. exact (@lem4383513 A B x s f g h1 (@lem4383514 A x s h2)). Qed.
Lemma lem4383521 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = ((@IN A x s) = True).
Proof. exact (@lem7 (@IN A x s)). Qed.
Lemma lem4383526 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term17 A B s f g) : term19 A B s f g x.
Proof. exact (fun h0 : @IN A x s => @lem4383515 A B f g x s h1 h0). Qed.
Lemma lem4383527 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term17 A B s f g) : term19 A B s f g x.
Proof. exact (@lem4383526 A B x s f g h1). Qed.
Lemma lem4383529 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : (@IN A x s) = True.
Proof. exact (EQ_MP (@lem4383521 A x s) (@lem4383480 A x s h1)). Qed.
Lemma lem4383530 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : True = (@IN A x s).
Proof. exact (SYM (@lem4383529 A x s h1)). Qed.
Lemma lem4383531 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (EQ_MP (@lem4383530 A x s h1) (@lem0)). Qed.
Lemma lem4383532 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) (s : A -> Prop) (h1 : term17 A B s f g) (h2 : @IN A x s) : (f x) = (g x).
Proof. exact (@lem4383527 A B x s f g h1 (@lem4383531 A x s h2)). Qed.
Lemma lem4383533 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem4383534 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) (s : A -> Prop) (h1 : term17 A B s f g) (h2 : @IN A x s) : (term20 A B f x) = (term20 A B g x).
Proof. exact (MK_COMB (@lem4383533 B) (@lem4383532 A B f g x s h1 h2)). Qed.
Lemma lem4383535 {A B : Type'} (g : A -> B) (x : A) : (g x) = (g x).
Proof. exact (eq_refl (g x)). Qed.
Lemma lem4383536 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) (s : A -> Prop) (h1 : term17 A B s f g) (h2 : @IN A x s) : ((f x) = (g x)) = ((g x) = (g x)).
Proof. exact (MK_COMB (@lem4383534 A B f g x s h1 h2) (@lem4383535 A B g x)). Qed.
Lemma lem4383538 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4383539 {B : Type'} (x : B) : (x = x) = True.
Proof. exact (@lem4383538 B x). Qed.
Lemma lem4383540 {A B : Type'} (g : A -> B) (x : A) : ((g x) = (g x)) = True.
Proof. exact (@lem4383539 B (g x)). Qed.
Lemma lem4383541 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) (s : A -> Prop) (h1 : term17 A B s f g) (h2 : @IN A x s) : ((f x) = (g x)) = True.
Proof. exact (TRANS (@lem4383536 A B f g x s h1 h2) (@lem4383540 A B g x)). Qed.
Lemma lem4383542 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) (s : A -> Prop) (h1 : term17 A B s f g) (h2 : @IN A x s) : True = ((f x) = (g x)).
Proof. exact (SYM (@lem4383541 A B f g x s h1 h2)). Qed.
Lemma lem4383543 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) (s : A -> Prop) (h1 : term17 A B s f g) (h2 : @IN A x s) : (f x) = (g x).
Proof. exact (EQ_MP (@lem4383542 A B f g x s h1 h2) (@lem0)). Qed.
Lemma lem4383545 (p : Prop) : p = (term21 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4383546 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) : ((f x) = (g x)) = (term22 A B f g x).
Proof. exact (@lem4383545 ((f x) = (g x))). Qed.
Lemma lem4383547 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) : (term22 A B f g x) = ((f x) = (g x)).
Proof. exact (SYM (@lem4383546 A B f g x)). Qed.
Lemma lem4383548 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) (h1 : term23 A B f g x) : term23 A B f g x.
Proof. exact (h1). Qed.
Lemma lem4383549 {A B : Type'} : term24 A B.
Proof. exact (@lem4383142 A B). Qed.
Lemma lem4383551 {A B : Type'} : term25 A B.
Proof. exact (@lem4383142 (A -> B) B). Qed.
Lemma lem4383556 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term26 A B s f g x) : term26 A B s f g x.
Proof. exact (h1). Qed.
Lemma lem4383557 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : term27 A B s f g x.
Proof. exact (fun h0 : term26 A B s f g x => @lem4383556 A B s f g x h0). Qed.
Lemma lem4383558 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term27 A B s f g x) : term27 A B s f g x.
Proof. exact (h1). Qed.
Lemma lem4383559 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term26 A B s f g x) : term26 A B s f g x.
Proof. exact (h1). Qed.
Lemma lem4383560 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term27 A B s f g x) (h2 : term26 A B s f g x) : term26 A B s f g x.
Proof. exact (@lem4383558 A B s f g x h1 (@lem4383559 A B s f g x h2)). Qed.
Lemma lem4383561 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term26 A B s f g x) : term28 A B s f g x.
Proof. exact (fun h0 : term27 A B s f g x => @lem4383560 A B s f g x h0 h1). Qed.
Lemma lem4383562 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term27 A B s f g x) : term27 A B s f g x.
Proof. exact (h1). Qed.
Lemma lem4383563 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term27 A B s f g x) (h2 : term26 A B s f g x) : term26 A B s f g x.
Proof. exact (@lem4383561 A B s f g x h2 (@lem4383562 A B s f g x h1)). Qed.
Lemma lem4383564 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term27 A B s f g x) : term27 A B s f g x.
Proof. exact (fun h0 : term26 A B s f g x => @lem4383563 A B s f g x h1 h0). Qed.
Lemma lem4383565 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : term29 A B s f g x.
Proof. exact (fun h0 : term27 A B s f g x => @lem4383564 A B s f g x h0). Qed.
Lemma lem4383568 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : term27 A B s f g x.
Proof. exact (@lem4383565 A B s f g x (@lem4383557 A B s f g x)). Qed.
Lemma lem4383569 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : term27 A B s f g x.
Proof. exact (@lem4383568 A B s f g x). Qed.
Lemma lem4383621 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4383622 {A B : Type'} : (term30 A B) = (term31 A B).
Proof. exact (@lem4383621 (term25 A B)). Qed.
Lemma lem4383639 {A B : Type'} : (term32 A B) = (term32 A B).
Proof. exact (eq_refl (term32 A B)). Qed.
Lemma lem4383640 {A B : Type'} : (term33 A B) = (term34 A B).
Proof. exact (MK_COMB (@lem4383639 A B) (@lem4383622 A B)). Qed.
Lemma lem4383643 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) : (term35 A B f g x) = (term35 A B f g x).
Proof. exact (eq_refl (term35 A B f g x)). Qed.
Lemma lem4383644 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) : (term36 A B f g x) = (term37 A B f g x).
Proof. exact (MK_COMB (@lem4383643 A B f g x) (@lem4383640 A B)). Qed.
Lemma lem4383647 {A : Type'} (x : A) (s : A -> Prop) : (term38 A x s) = (term38 A x s).
Proof. exact (eq_refl (term38 A x s)). Qed.
Lemma lem4383648 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term39 A B s f g x) = (term40 A B s f g x).
Proof. exact (MK_COMB (@lem4383647 A x s) (@lem4383644 A B f g x)). Qed.
Lemma lem4383651 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term41 A B s f g) = (term41 A B s f g).
Proof. exact (eq_refl (term41 A B s f g)). Qed.
Lemma lem4383652 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term42 A B s f g x) = (term43 A B s f g x).
Proof. exact (MK_COMB (@lem4383651 A B s f g) (@lem4383648 A B s f g x)). Qed.
Lemma lem4383655 {A B : Type'} (g : A -> B) (s : A -> Prop) : (term44 A B g s) = (term44 A B g s).
Proof. exact (eq_refl (term44 A B g s)). Qed.
Lemma lem4383656 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term45 A B s f g x) = (term46 A B s f g x).
Proof. exact (MK_COMB (@lem4383655 A B g s) (@lem4383652 A B s f g x)). Qed.
Lemma lem4383659 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term44 A B f s) = (term44 A B f s).
Proof. exact (eq_refl (term44 A B f s)). Qed.
Lemma lem4383660 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term26 A B s f g x) = (term47 A B s f g x).
Proof. exact (MK_COMB (@lem4383659 A B f s) (@lem4383656 A B s f g x)). Qed.
Lemma lem4383663 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) : (term48 A B f g x) = (term49 A B f g x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4383660 A B s f g x)). Qed.
Lemma lem4383664 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4383665 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) : (term50 A B f g x) = (term51 A B f g x).
Proof. exact (MK_COMB (@lem4383664 A) (@lem4383663 A B f g x)). Qed.
Lemma lem4383670 {A B : Type'} (g : A -> B) (x : A) : (term52 A B g x) = (term53 A B g x).
Proof. exact (fun_ext (fun f : A -> B => @lem4383665 A B f g x)). Qed.
Lemma lem4383671 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4383672 {A B : Type'} (g : A -> B) (x : A) : (term54 A B g x) = (term55 A B g x).
Proof. exact (MK_COMB (@lem4383671 A B) (@lem4383670 A B g x)). Qed.
Lemma lem4383677 {A B : Type'} (x : A) : (term56 A B x) = (term57 A B x).
Proof. exact (fun_ext (fun g : A -> B => @lem4383672 A B g x)). Qed.
Lemma lem4383678 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4383679 {A B : Type'} (x : A) : (term58 A B x) = (term59 A B x).
Proof. exact (MK_COMB (@lem4383678 A B) (@lem4383677 A B x)). Qed.
Lemma lem4383684 {A B : Type'} : (term60 A B) = (term61 A B).
Proof. exact (fun_ext (fun x : A => @lem4383679 A B x)). Qed.
Lemma lem4383685 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4383694 {A B : Type'} : (term62 A B) = (term63 A B).
Proof. exact (MK_COMB (@lem4383685 A) (@lem4383684 A B)). Qed.
Lemma lem4383705 {A B : Type'} (s : type572 A B) (f : type570 A B) (x : A -> B) : (term64 A B s f x) = (term64 A B s f x).
Proof. exact (eq_refl (term64 A B s f x)). Qed.
Lemma lem4383706 {A B : Type'} (s : type572 A B) (f : type570 A B) : (term65 A B s f) = (term65 A B s f).
Proof. exact (fun_ext (fun x : A -> B => @lem4383705 A B s f x)). Qed.
Lemma lem4383707 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4383708 {A B : Type'} (s : type572 A B) (f : type570 A B) : (term66 A B s f) = (term66 A B s f).
Proof. exact (MK_COMB (@lem4383707 A B) (@lem4383706 A B s f)). Qed.
Lemma lem4383709 {A B : Type'} (s : type572 A B) : (term67 A B s) = (term67 A B s).
Proof. exact (fun_ext (fun f : type570 A B => @lem4383708 A B s f)). Qed.
Lemma lem4383710 {A B : Type'} : (@all ((A -> B) -> B)) = (@all ((A -> B) -> B)).
Proof. exact (eq_refl (@all ((A -> B) -> B))). Qed.
Lemma lem4383711 {A B : Type'} (s : type572 A B) : (term68 A B s) = (term68 A B s).
Proof. exact (MK_COMB (@lem4383710 A B) (@lem4383709 A B s)). Qed.
Lemma lem4383712 {A B : Type'} : (term69 A B) = (term69 A B).
Proof. exact (fun_ext (fun s : type572 A B => @lem4383711 A B s)). Qed.
Lemma lem4383713 {A B : Type'} : (@all ((A -> B) -> Prop)) = (@all ((A -> B) -> Prop)).
Proof. exact (eq_refl (@all ((A -> B) -> Prop))). Qed.
Lemma lem4383714 {A B : Type'} : (term25 A B) = (term25 A B).
Proof. exact (MK_COMB (@lem4383713 A B) (@lem4383712 A B)). Qed.
Lemma lem4383715 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4383716 {A B : Type'} : (term31 A B) = (term31 A B).
Proof. exact (MK_COMB (@lem4383715) (@lem4383714 A B)). Qed.
Lemma lem4383727 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term70 A B s f x) = (term70 A B s f x).
Proof. exact (eq_refl (term70 A B s f x)). Qed.
Lemma lem4383728 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term71 A B s f) = (term71 A B s f).
Proof. exact (fun_ext (fun x : A => @lem4383727 A B s f x)). Qed.
Lemma lem4383729 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4383730 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term72 A B s f) = (term72 A B s f).
Proof. exact (MK_COMB (@lem4383729 A) (@lem4383728 A B s f)). Qed.
Lemma lem4383731 {A B : Type'} (s : A -> Prop) : (term73 A B s) = (term73 A B s).
Proof. exact (fun_ext (fun f : A -> B => @lem4383730 A B s f)). Qed.
Lemma lem4383732 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4383733 {A B : Type'} (s : A -> Prop) : (term74 A B s) = (term74 A B s).
Proof. exact (MK_COMB (@lem4383732 A B) (@lem4383731 A B s)). Qed.
Lemma lem4383734 {A B : Type'} : (term75 A B) = (term75 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4383733 A B s)). Qed.
Lemma lem4383735 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4383736 {A B : Type'} : (term24 A B) = (term24 A B).
Proof. exact (MK_COMB (@lem4383735 A) (@lem4383734 A B)). Qed.
Lemma lem4383737 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4383738 {A B : Type'} : (term32 A B) = (term32 A B).
Proof. exact (MK_COMB (@lem4383737) (@lem4383736 A B)). Qed.
Lemma lem4383739 {A B : Type'} : (term34 A B) = (term34 A B).
Proof. exact (MK_COMB (@lem4383738 A B) (@lem4383716 A B)). Qed.
Lemma lem4383744 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) : (term35 A B f g x) = (term35 A B f g x).
Proof. exact (eq_refl (term35 A B f g x)). Qed.
Lemma lem4383745 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) : (term37 A B f g x) = (term37 A B f g x).
Proof. exact (MK_COMB (@lem4383744 A B f g x) (@lem4383739 A B)). Qed.
Lemma lem4383750 {A : Type'} (x : A) (s : A -> Prop) : (term38 A x s) = (term38 A x s).
Proof. exact (eq_refl (term38 A x s)). Qed.
Lemma lem4383751 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term40 A B s f g x) = (term40 A B s f g x).
Proof. exact (MK_COMB (@lem4383750 A x s) (@lem4383745 A B f g x)). Qed.
Lemma lem4383756 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term19 A B s f g x) = (term19 A B s f g x).
Proof. exact (eq_refl (term19 A B s f g x)). Qed.
Lemma lem4383757 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term76 A B s f g) = (term76 A B s f g).
Proof. exact (fun_ext (fun x : A => @lem4383756 A B s f g x)). Qed.
Lemma lem4383758 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4383759 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term17 A B s f g) = (term17 A B s f g).
Proof. exact (MK_COMB (@lem4383758 A) (@lem4383757 A B s f g)). Qed.
Lemma lem4383760 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4383761 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term41 A B s f g) = (term41 A B s f g).
Proof. exact (MK_COMB (@lem4383760) (@lem4383759 A B s f g)). Qed.
Lemma lem4383762 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term43 A B s f g x) = (term43 A B s f g x).
Proof. exact (MK_COMB (@lem4383761 A B s f g) (@lem4383751 A B s f g x)). Qed.
Lemma lem4383765 {A B : Type'} (g : A -> B) (s : A -> Prop) : (term44 A B g s) = (term44 A B g s).
Proof. exact (eq_refl (term44 A B g s)). Qed.
Lemma lem4383766 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term46 A B s f g x) = (term46 A B s f g x).
Proof. exact (MK_COMB (@lem4383765 A B g s) (@lem4383762 A B s f g x)). Qed.
Lemma lem4383769 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term44 A B f s) = (term44 A B f s).
Proof. exact (eq_refl (term44 A B f s)). Qed.
Lemma lem4383770 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term47 A B s f g x) = (term47 A B s f g x).
Proof. exact (MK_COMB (@lem4383769 A B f s) (@lem4383766 A B s f g x)). Qed.
Lemma lem4383771 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) : (term49 A B f g x) = (term49 A B f g x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4383770 A B s f g x)). Qed.
Lemma lem4383772 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4383773 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) : (term51 A B f g x) = (term51 A B f g x).
Proof. exact (MK_COMB (@lem4383772 A) (@lem4383771 A B f g x)). Qed.
Lemma lem4383774 {A B : Type'} (g : A -> B) (x : A) : (term53 A B g x) = (term53 A B g x).
Proof. exact (fun_ext (fun f : A -> B => @lem4383773 A B f g x)). Qed.
Lemma lem4383775 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4383776 {A B : Type'} (g : A -> B) (x : A) : (term55 A B g x) = (term55 A B g x).
Proof. exact (MK_COMB (@lem4383775 A B) (@lem4383774 A B g x)). Qed.
Lemma lem4383777 {A B : Type'} (x : A) : (term57 A B x) = (term57 A B x).
Proof. exact (fun_ext (fun g : A -> B => @lem4383776 A B g x)). Qed.
Lemma lem4383778 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4383779 {A B : Type'} (x : A) : (term59 A B x) = (term59 A B x).
Proof. exact (MK_COMB (@lem4383778 A B) (@lem4383777 A B x)). Qed.
Lemma lem4383780 {A B : Type'} : (term61 A B) = (term61 A B).
Proof. exact (fun_ext (fun x : A => @lem4383779 A B x)). Qed.
Lemma lem4383781 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4383782 {A B : Type'} : (term63 A B) = (term63 A B).
Proof. exact (MK_COMB (@lem4383781 A) (@lem4383780 A B)). Qed.
Lemma lem4383873 {A B : Type'} : (term62 A B) = (term63 A B).
Proof. exact (TRANS (@lem4383694 A B) (@lem4383782 A B)). Qed.
Lemma lem4383874 {A B : Type'} : (term63 A B) = (term62 A B).
Proof. exact (SYM (@lem4383873 A B)). Qed.
Lemma lem4383880 {A B : Type'} (h1 : term24 A B) : term24 A B.
Proof. exact (h1). Qed.
Lemma lem4383887 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term16 A B f s) : term16 A B f s.
Proof. exact (h1). Qed.
Lemma lem4383893 {A B : Type'} (g : A -> B) (s : A -> Prop) (h1 : term16 A B g s) : term16 A B g s.
Proof. exact (h1). Qed.
Lemma lem4383962 {A : Type'} (x : A) (s : A -> Prop) (h1 : term9 A x s) : term9 A x s.
Proof. exact (h1). Qed.
Lemma lem4383968 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) (h1 : term23 A B f g x) : term23 A B f g x.
Proof. exact (h1). Qed.
Lemma lem4383972 {A : Type'} (x : A) (s : A -> Prop) : (term77 A x s) = (@IN A x s).
Proof. exact (@lem16933 (@IN A x s)). Qed.
Lemma lem4383974 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term78 A B f s) = (term78 A B f s).
Proof. exact (eq_refl (term78 A B f s)). Qed.
Lemma lem4383975 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : (term79 A B f x s) = (term80 A B f x s).
Proof. exact (MK_COMB (@lem4383974 A B f s) (@lem4383972 A x s)). Qed.
Lemma lem4383976 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : (term81 A B f x s) = (term79 A B f x s).
Proof. exact (@lem17045 (term16 A B f s) (term9 A x s)). Qed.
Lemma lem4383977 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : (term81 A B f x s) = (term80 A B f x s).
Proof. exact (TRANS (@lem4383976 A B f x s) (@lem4383975 A B f x s)). Qed.
Lemma lem4383978 {A B : Type'} (f : A -> B) (x : A) : ((f x) = (@ARB B)) = ((f x) = (@ARB B)).
Proof. exact (eq_refl ((f x) = (@ARB B))). Qed.
Lemma lem4383979 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4383980 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : (term82 A B f x s) = (term83 A B f x s).
Proof. exact (MK_COMB (@lem4383979) (@lem4383977 A B f x s)). Qed.
Lemma lem4383981 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term84 A B s f x) = (term85 A B s f x).
Proof. exact (MK_COMB (@lem4383980 A B f x s) (@lem4383978 A B f x)). Qed.
Lemma lem4383982 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term70 A B s f x) = (term84 A B s f x).
Proof. exact (@lem17265 (term86 A B f x s) ((f x) = (@ARB B))). Qed.
Lemma lem4383983 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term70 A B s f x) = (term85 A B s f x).
Proof. exact (TRANS (@lem4383982 A B s f x) (@lem4383981 A B s f x)). Qed.
Lemma lem4383984 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term71 A B s f) = (term87 A B s f).
Proof. exact (fun_ext (fun x : A => @lem4383983 A B s f x)). Qed.
Lemma lem4383985 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4383986 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term72 A B s f) = (term88 A B s f).
Proof. exact (MK_COMB (@lem4383985 A) (@lem4383984 A B s f)). Qed.
Lemma lem4383987 {A B : Type'} (s : A -> Prop) : (term73 A B s) = (term89 A B s).
Proof. exact (fun_ext (fun f : A -> B => @lem4383986 A B s f)). Qed.
Lemma lem4383988 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4383989 {A B : Type'} (s : A -> Prop) : (term74 A B s) = (term90 A B s).
Proof. exact (MK_COMB (@lem4383988 A B) (@lem4383987 A B s)). Qed.
Lemma lem4383990 {A B : Type'} : (term75 A B) = (term91 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4383989 A B s)). Qed.
Lemma lem4383991 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4384052 {A B : Type'} : (term24 A B) = (term92 A B).
Proof. exact (MK_COMB (@lem4383991 A) (@lem4383990 A B)). Qed.
Lemma lem4384053 {A B : Type'} (h1 : term24 A B) : term92 A B.
Proof. exact (EQ_MP (@lem4384052 A B) (@lem4383880 A B h1)). Qed.
Lemma lem4384145 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4384146 {A B : Type'} (f : type633 A B) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> B) -> Prop) f x).
Proof. exact (@lem4384145 (A -> Prop) (type572 A B) f x). Qed.
Lemma lem4384148 {A B : Type'} (s : A -> Prop) : (@EXTENSIONAL A B s) = (@I ((A -> Prop) -> (A -> B) -> Prop) (@EXTENSIONAL A B) s).
Proof. exact (@lem4384146 A B (@EXTENSIONAL A B) s). Qed.
Lemma lem4384149 {A B : Type'} (f : A -> B) : (@IN (A -> B) f) = (@IN (A -> B) f).
Proof. exact (eq_refl (@IN (A -> B) f)). Qed.
Lemma lem4384150 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term16 A B f s) = (term93 A B f s).
Proof. exact (MK_COMB (@lem4384149 A B f) (@lem4384148 A B s)). Qed.
Lemma lem4384152 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4384153 {A B : Type'} (f : type500 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> ((A -> B) -> Prop) -> Prop) f x).
Proof. exact (@lem4384152 (A -> B) (type122 A B) f x). Qed.
Lemma lem4384154 {A B : Type'} (f : A -> B) : (@IN (A -> B) f) = (@I ((A -> B) -> ((A -> B) -> Prop) -> Prop) (@IN (A -> B)) f).
Proof. exact (@lem4384153 A B (@IN (A -> B)) f). Qed.
Lemma lem4384155 {A B : Type'} (s : A -> Prop) : (@I ((A -> Prop) -> (A -> B) -> Prop) (@EXTENSIONAL A B) s) = (@I ((A -> Prop) -> (A -> B) -> Prop) (@EXTENSIONAL A B) s).
Proof. exact (eq_refl (@I ((A -> Prop) -> (A -> B) -> Prop) (@EXTENSIONAL A B) s)). Qed.
Lemma lem4384156 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term93 A B f s) = (term94 A B f s).
Proof. exact (MK_COMB (@lem4384154 A B f) (@lem4384155 A B s)). Qed.
Lemma lem4384158 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4384159 {A B : Type'} (f : type122 A B) (x : type572 A B) : (f x) = (@I (((A -> B) -> Prop) -> Prop) f x).
Proof. exact (@lem4384158 (type572 A B) Prop f x). Qed.
Lemma lem4384160 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term94 A B f s) = (term95 A B f s).
Proof. exact (@lem4384159 A B (@I ((A -> B) -> ((A -> B) -> Prop) -> Prop) (@IN (A -> B)) f) (@I ((A -> Prop) -> (A -> B) -> Prop) (@EXTENSIONAL A B) s)). Qed.
Lemma lem4384161 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term93 A B f s) = (term95 A B f s).
Proof. exact (TRANS (@lem4384156 A B f s) (@lem4384160 A B f s)). Qed.
Lemma lem4384162 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term16 A B f s) = (term95 A B f s).
Proof. exact (TRANS (@lem4384150 A B f s) (@lem4384161 A B f s)). Qed.
Lemma lem4384170 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4384171 {A B : Type'} (f : type633 A B) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> B) -> Prop) f x).
Proof. exact (@lem4384170 (A -> Prop) (type572 A B) f x). Qed.
Lemma lem4384173 {A B : Type'} (s : A -> Prop) : (@EXTENSIONAL A B s) = (@I ((A -> Prop) -> (A -> B) -> Prop) (@EXTENSIONAL A B) s).
Proof. exact (@lem4384171 A B (@EXTENSIONAL A B) s). Qed.
Lemma lem4384174 {A B : Type'} (g : A -> B) : (@IN (A -> B) g) = (@IN (A -> B) g).
Proof. exact (eq_refl (@IN (A -> B) g)). Qed.
Lemma lem4384175 {A B : Type'} (g : A -> B) (s : A -> Prop) : (term16 A B g s) = (term93 A B g s).
Proof. exact (MK_COMB (@lem4384174 A B g) (@lem4384173 A B s)). Qed.
Lemma lem4384177 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4384178 {A B : Type'} (f : type500 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> ((A -> B) -> Prop) -> Prop) f x).
Proof. exact (@lem4384177 (A -> B) (type122 A B) f x). Qed.
Lemma lem4384179 {A B : Type'} (g : A -> B) : (@IN (A -> B) g) = (@I ((A -> B) -> ((A -> B) -> Prop) -> Prop) (@IN (A -> B)) g).
Proof. exact (@lem4384178 A B (@IN (A -> B)) g). Qed.
Lemma lem4384180 {A B : Type'} (s : A -> Prop) : (@I ((A -> Prop) -> (A -> B) -> Prop) (@EXTENSIONAL A B) s) = (@I ((A -> Prop) -> (A -> B) -> Prop) (@EXTENSIONAL A B) s).
Proof. exact (eq_refl (@I ((A -> Prop) -> (A -> B) -> Prop) (@EXTENSIONAL A B) s)). Qed.
Lemma lem4384181 {A B : Type'} (g : A -> B) (s : A -> Prop) : (term93 A B g s) = (term94 A B g s).
Proof. exact (MK_COMB (@lem4384179 A B g) (@lem4384180 A B s)). Qed.
Lemma lem4384183 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4384184 {A B : Type'} (f : type122 A B) (x : type572 A B) : (f x) = (@I (((A -> B) -> Prop) -> Prop) f x).
Proof. exact (@lem4384183 (type572 A B) Prop f x). Qed.
Lemma lem4384185 {A B : Type'} (g : A -> B) (s : A -> Prop) : (term94 A B g s) = (term95 A B g s).
Proof. exact (@lem4384184 A B (@I ((A -> B) -> ((A -> B) -> Prop) -> Prop) (@IN (A -> B)) g) (@I ((A -> Prop) -> (A -> B) -> Prop) (@EXTENSIONAL A B) s)). Qed.
Lemma lem4384186 {A B : Type'} (g : A -> B) (s : A -> Prop) : (term93 A B g s) = (term95 A B g s).
Proof. exact (TRANS (@lem4384181 A B g s) (@lem4384185 A B g s)). Qed.
Lemma lem4384187 {A B : Type'} (g : A -> B) (s : A -> Prop) : (term16 A B g s) = (term95 A B g s).
Proof. exact (TRANS (@lem4384175 A B g s) (@lem4384186 A B g s)). Qed.
Lemma lem4384233 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4384240 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4384241 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4384240 A (type686 A) f x). Qed.
Lemma lem4384242 {A : Type'} (x : A) : (@IN A x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x).
Proof. exact (@lem4384241 A (@IN A) x). Qed.
Lemma lem4384243 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4384244 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x s).
Proof. exact (MK_COMB (@lem4384242 A x) (@lem4384243 A s)). Qed.
Lemma lem4384246 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4384247 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4384246 (A -> Prop) Prop f x). Qed.
Lemma lem4384248 {A : Type'} (x : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x s) = (term96 A x s).
Proof. exact (@lem4384247 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x) s). Qed.
Lemma lem4384250 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (term96 A x s).
Proof. exact (TRANS (@lem4384244 A x s) (@lem4384248 A x s)). Qed.
Lemma lem4384251 {A : Type'} (x : A) (s : A -> Prop) : (term9 A x s) = (term97 A x s).
Proof. exact (MK_COMB (@lem4384233) (@lem4384250 A x s)). Qed.
Lemma lem4384253 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4384254 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem4384259 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4384261 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem4384259 A B f x). Qed.
Lemma lem4384266 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4384267 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem4384266 A B f x). Qed.
Lemma lem4384269 {A B : Type'} (g : A -> B) (x : A) : (g x) = (@I (A -> B) g x).
Proof. exact (@lem4384267 A B g x). Qed.
Lemma lem4384270 {A B : Type'} (f : A -> B) (x : A) : (term20 A B f x) = (term98 A B f x).
Proof. exact (MK_COMB (@lem4384254 B) (@lem4384261 A B f x)). Qed.
Lemma lem4384271 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) : ((f x) = (g x)) = ((@I (A -> B) f x) = (@I (A -> B) g x)).
Proof. exact (MK_COMB (@lem4384270 A B f x) (@lem4384269 A B g x)). Qed.
Lemma lem4384272 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) : (term23 A B f g x) = (term99 A B f g x).
Proof. exact (MK_COMB (@lem4384253) (@lem4384271 A B f g x)). Qed.
Lemma lem4384274 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem4384279 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4384281 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem4384279 A B f x). Qed.
Lemma lem4384282 {B : Type'} : (@ARB B) = (@ARB B).
Proof. exact (eq_refl (@ARB B)). Qed.
Lemma lem4384283 {A B : Type'} (f : A -> B) (x : A) : (term20 A B f x) = (term98 A B f x).
Proof. exact (MK_COMB (@lem4384274 B) (@lem4384281 A B f x)). Qed.
Lemma lem4384284 {A B : Type'} (f : A -> B) (x : A) : ((f x) = (@ARB B)) = ((@I (A -> B) f x) = (@ARB B)).
Proof. exact (MK_COMB (@lem4384283 A B f x) (@lem4384282 B)). Qed.
Lemma lem4384291 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4384292 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4384291 A (type686 A) f x). Qed.
Lemma lem4384293 {A : Type'} (x : A) : (@IN A x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x).
Proof. exact (@lem4384292 A (@IN A) x). Qed.
Lemma lem4384294 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4384295 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x s).
Proof. exact (MK_COMB (@lem4384293 A x) (@lem4384294 A s)). Qed.
Lemma lem4384297 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4384298 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4384297 (A -> Prop) Prop f x). Qed.
Lemma lem4384299 {A : Type'} (x : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x s) = (term96 A x s).
Proof. exact (@lem4384298 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x) s). Qed.
Lemma lem4384301 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (term96 A x s).
Proof. exact (TRANS (@lem4384295 A x s) (@lem4384299 A x s)). Qed.
Lemma lem4384302 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4384309 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4384310 {A B : Type'} (f : type633 A B) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> B) -> Prop) f x).
Proof. exact (@lem4384309 (A -> Prop) (type572 A B) f x). Qed.
Lemma lem4384312 {A B : Type'} (s : A -> Prop) : (@EXTENSIONAL A B s) = (@I ((A -> Prop) -> (A -> B) -> Prop) (@EXTENSIONAL A B) s).
Proof. exact (@lem4384310 A B (@EXTENSIONAL A B) s). Qed.
Lemma lem4384313 {A B : Type'} (f : A -> B) : (@IN (A -> B) f) = (@IN (A -> B) f).
Proof. exact (eq_refl (@IN (A -> B) f)). Qed.
Lemma lem4384314 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term16 A B f s) = (term93 A B f s).
Proof. exact (MK_COMB (@lem4384313 A B f) (@lem4384312 A B s)). Qed.
Lemma lem4384316 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4384317 {A B : Type'} (f : type500 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> ((A -> B) -> Prop) -> Prop) f x).
Proof. exact (@lem4384316 (A -> B) (type122 A B) f x). Qed.
Lemma lem4384318 {A B : Type'} (f : A -> B) : (@IN (A -> B) f) = (@I ((A -> B) -> ((A -> B) -> Prop) -> Prop) (@IN (A -> B)) f).
Proof. exact (@lem4384317 A B (@IN (A -> B)) f). Qed.
Lemma lem4384319 {A B : Type'} (s : A -> Prop) : (@I ((A -> Prop) -> (A -> B) -> Prop) (@EXTENSIONAL A B) s) = (@I ((A -> Prop) -> (A -> B) -> Prop) (@EXTENSIONAL A B) s).
Proof. exact (eq_refl (@I ((A -> Prop) -> (A -> B) -> Prop) (@EXTENSIONAL A B) s)). Qed.
Lemma lem4384320 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term93 A B f s) = (term94 A B f s).
Proof. exact (MK_COMB (@lem4384318 A B f) (@lem4384319 A B s)). Qed.
Lemma lem4384322 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4384323 {A B : Type'} (f : type122 A B) (x : type572 A B) : (f x) = (@I (((A -> B) -> Prop) -> Prop) f x).
Proof. exact (@lem4384322 (type572 A B) Prop f x). Qed.
Lemma lem4384324 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term94 A B f s) = (term95 A B f s).
Proof. exact (@lem4384323 A B (@I ((A -> B) -> ((A -> B) -> Prop) -> Prop) (@IN (A -> B)) f) (@I ((A -> Prop) -> (A -> B) -> Prop) (@EXTENSIONAL A B) s)). Qed.
Lemma lem4384325 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term93 A B f s) = (term95 A B f s).
Proof. exact (TRANS (@lem4384320 A B f s) (@lem4384324 A B f s)). Qed.
Lemma lem4384326 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term16 A B f s) = (term95 A B f s).
Proof. exact (TRANS (@lem4384314 A B f s) (@lem4384325 A B f s)). Qed.
Lemma lem4384327 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term100 A B f s) = (term101 A B f s).
Proof. exact (MK_COMB (@lem4384302) (@lem4384326 A B f s)). Qed.
Lemma lem4384328 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4384329 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term78 A B f s) = (term102 A B f s).
Proof. exact (MK_COMB (@lem4384328) (@lem4384327 A B f s)). Qed.
Lemma lem4384330 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : (term80 A B f x s) = (term103 A B f x s).
Proof. exact (MK_COMB (@lem4384329 A B f s) (@lem4384301 A x s)). Qed.
Lemma lem4384331 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4384332 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : (term83 A B f x s) = (term104 A B f x s).
Proof. exact (MK_COMB (@lem4384331) (@lem4384330 A B f x s)). Qed.
Lemma lem4384333 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term85 A B s f x) = (term105 A B s f x).
Proof. exact (MK_COMB (@lem4384332 A B f x s) (@lem4384284 A B f x)). Qed.
Lemma lem4384334 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term87 A B s f) = (term106 A B s f).
Proof. exact (fun_ext (fun x : A => @lem4384333 A B s f x)). Qed.
Lemma lem4384335 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4384336 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term88 A B s f) = (term107 A B s f).
Proof. exact (MK_COMB (@lem4384335 A) (@lem4384334 A B s f)). Qed.
Lemma lem4384337 {A B : Type'} (s : A -> Prop) : (term89 A B s) = (term108 A B s).
Proof. exact (fun_ext (fun f : A -> B => @lem4384336 A B s f)). Qed.
Lemma lem4384338 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4384339 {A B : Type'} (s : A -> Prop) : (term90 A B s) = (term109 A B s).
Proof. exact (MK_COMB (@lem4384338 A B) (@lem4384337 A B s)). Qed.
Lemma lem4384340 {A B : Type'} : (term91 A B) = (term110 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4384339 A B s)). Qed.
Lemma lem4384341 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4384342 {A B : Type'} : (term92 A B) = (term111 A B).
Proof. exact (MK_COMB (@lem4384341 A) (@lem4384340 A B)). Qed.
Lemma lem4384343 {A B : Type'} (h1 : term24 A B) : term111 A B.
Proof. exact (EQ_MP (@lem4384342 A B) (@lem4384053 A B h1)). Qed.
Lemma lem4384456 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term105 A B s f x) = (term105 A B s f x).
Proof. exact (eq_refl (term105 A B s f x)). Qed.
Lemma lem4384457 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term106 A B s f) = (term106 A B s f).
Proof. exact (fun_ext (fun x : A => @lem4384456 A B s f x)). Qed.
Lemma lem4384458 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4384459 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term107 A B s f) = (term107 A B s f).
Proof. exact (MK_COMB (@lem4384458 A) (@lem4384457 A B s f)). Qed.
Lemma lem4384460 {A B : Type'} (s : A -> Prop) : (term108 A B s) = (term108 A B s).
Proof. exact (fun_ext (fun f : A -> B => @lem4384459 A B s f)). Qed.
Lemma lem4384461 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4384462 {A B : Type'} (s : A -> Prop) : (term109 A B s) = (term109 A B s).
Proof. exact (MK_COMB (@lem4384461 A B) (@lem4384460 A B s)). Qed.
Lemma lem4384463 {A B : Type'} : (term110 A B) = (term110 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4384462 A B s)). Qed.
Lemma lem4384464 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4384466 {A B : Type'} : (term111 A B) = (term111 A B).
Proof. exact (MK_COMB (@lem4384464 A) (@lem4384463 A B)). Qed.
Lemma lem4384467 {A B : Type'} (h1 : term24 A B) : term111 A B.
Proof. exact (EQ_MP (@lem4384466 A B) (@lem4384343 A B h1)). Qed.
Lemma lem4384496 {A B : Type'} (_50052 : A -> Prop) (h1 : term24 A B) : term112 A B _50052.
Proof. exact (@lem4384467 A B h1 _50052). Qed.
Lemma lem4384497 {A B : Type'} (_50052 : A -> Prop) : (term112 A B _50052) = (term109 A B _50052).
Proof. exact (eq_refl (term112 A B _50052)). Qed.
Lemma lem4384498 {A B : Type'} (_50052 : A -> Prop) (h1 : term24 A B) : term109 A B _50052.
Proof. exact (EQ_MP (@lem4384497 A B _50052) (@lem4384496 A B _50052 h1)). Qed.
Lemma lem4384499 {A B : Type'} (_50052 : A -> Prop) (_50053 : A -> B) (h1 : term24 A B) : term113 A B _50052 _50053.
Proof. exact (@lem4384498 A B _50052 h1 _50053). Qed.
Lemma lem4384500 {A B : Type'} (_50052 : A -> Prop) (_50053 : A -> B) : (term113 A B _50052 _50053) = (term107 A B _50052 _50053).
Proof. exact (eq_refl (term113 A B _50052 _50053)). Qed.
Lemma lem4384501 {A B : Type'} (_50052 : A -> Prop) (_50053 : A -> B) (h1 : term24 A B) : term107 A B _50052 _50053.
Proof. exact (EQ_MP (@lem4384500 A B _50052 _50053) (@lem4384499 A B _50052 _50053 h1)). Qed.
Lemma lem4384502 {A B : Type'} (_50052 : A -> Prop) (_50053 : A -> B) (_50054 : A) (h1 : term24 A B) : term114 A B _50052 _50053 _50054.
Proof. exact (@lem4384501 A B _50052 _50053 h1 _50054). Qed.
Lemma lem4384503 {A B : Type'} (_50052 : A -> Prop) (_50053 : A -> B) (_50054 : A) : (term114 A B _50052 _50053 _50054) = (term105 A B _50052 _50053 _50054).
Proof. exact (eq_refl (term114 A B _50052 _50053 _50054)). Qed.
Lemma lem4384504 {A B : Type'} (_50052 : A -> Prop) (_50053 : A -> B) (_50054 : A) (h1 : term24 A B) : term105 A B _50052 _50053 _50054.
Proof. exact (EQ_MP (@lem4384503 A B _50052 _50053 _50054) (@lem4384502 A B _50052 _50053 _50054 h1)). Qed.
Lemma lem4384525 {A : Type'} (x : A) (s : A -> Prop) (h1 : term9 A x s) : term97 A x s.
Proof. exact (EQ_MP (@lem4384251 A x s) (@lem4383962 A x s h1)). Qed.
Lemma lem4384538 {A B : Type'} (_50052 : A -> Prop) (_50053 : A -> B) (_50054 : A) : (term105 A B _50052 _50053 _50054) = (term115 A B _50052 _50053 _50054).
Proof. exact (@lem4383476 (term101 A B _50053 _50052) (term96 A _50054 _50052) ((@I (A -> B) _50053 _50054) = (@ARB B))). Qed.
Lemma lem4384539 {A B : Type'} (_50052 : A -> Prop) (_50053 : A -> B) (_50054 : A) (h1 : term24 A B) : term115 A B _50052 _50053 _50054.
Proof. exact (EQ_MP (@lem4384538 A B _50052 _50053 _50054) (@lem4384504 A B _50052 _50053 _50054 h1)). Qed.
Lemma lem4384727 {B : Type'} (x : B) (y : B) (z : B) : term116 B x y z.
Proof. exact (@lem21385 B x y z). Qed.
Lemma lem4384745 {A B : Type'} (g : A -> B) (s : A -> Prop) (h1 : term16 A B g s) : term95 A B g s.
Proof. exact (EQ_MP (@lem4384187 A B g s) (@lem4383893 A B g s h1)). Qed.
Lemma lem4384746 {A B : Type'} (g : A -> B) (s : A -> Prop) (h1 : term16 A B g s) : term117 A B g s.
Proof. exact (fun h0 : term101 A B g s => @lem4384745 A B g s h1). Qed.
Lemma lem4384748 (p : Prop) : (term118 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4384749 {A B : Type'} (g : A -> B) (s : A -> Prop) : (term117 A B g s) = (term95 A B g s).
Proof. exact (@lem4384748 (term95 A B g s)). Qed.
Lemma lem4384750 {A B : Type'} (g : A -> B) (s : A -> Prop) (h1 : term16 A B g s) : term95 A B g s.
Proof. exact (EQ_MP (@lem4384749 A B g s) (@lem4384746 A B g s h1)). Qed.
Lemma lem4384752 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem4384753 {B : Type'} (x : B) : x = x.
Proof. exact (@lem4384752 B x). Qed.
Lemma lem4384754 {A B : Type'} (g : A -> B) (x : A) : (@I (A -> B) g x) = (@I (A -> B) g x).
Proof. exact (@lem4384753 B (@I (A -> B) g x)). Qed.
Lemma lem4384755 {A B : Type'} (g : A -> B) (x : A) : term119 A B g x.
Proof. exact (fun h0 : term120 A B g x => @lem4384754 A B g x). Qed.
Lemma lem4384757 (p : Prop) : (term118 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4384758 {A B : Type'} (g : A -> B) (x : A) : (term119 A B g x) = ((@I (A -> B) g x) = (@I (A -> B) g x)).
Proof. exact (@lem4384757 ((@I (A -> B) g x) = (@I (A -> B) g x))). Qed.
Lemma lem4384759 {A B : Type'} (g : A -> B) (x : A) : (@I (A -> B) g x) = (@I (A -> B) g x).
Proof. exact (EQ_MP (@lem4384758 A B g x) (@lem4384755 A B g x)). Qed.
Lemma lem4384761 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term16 A B f s) : term95 A B f s.
Proof. exact (EQ_MP (@lem4384162 A B f s) (@lem4383887 A B f s h1)). Qed.
Lemma lem4384762 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term16 A B f s) : term117 A B f s.
Proof. exact (fun h0 : term101 A B f s => @lem4384761 A B f s h1). Qed.
Lemma lem4384764 (p : Prop) : (term118 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4384765 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term117 A B f s) = (term95 A B f s).
Proof. exact (@lem4384764 (term95 A B f s)). Qed.
Lemma lem4384766 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term16 A B f s) : term95 A B f s.
Proof. exact (EQ_MP (@lem4384765 A B f s) (@lem4384762 A B f s h1)). Qed.
Lemma lem4384769 {A : Type'} (x : A) (s : A -> Prop) (h1 : term97 A x s) : term97 A x s.
Proof. exact (h1). Qed.
Lemma lem4384770 {A : Type'} (x : A) (s : A -> Prop) (h1 : term97 A x s) : term121 A x s.
Proof. exact (fun h0 : term96 A x s => @lem4384769 A x s h1). Qed.
Lemma lem4384772 (p : Prop) : (term122 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4384773 {A : Type'} (x : A) (s : A -> Prop) : (term121 A x s) = (term97 A x s).
Proof. exact (@lem4384772 (term96 A x s)). Qed.
Lemma lem4384774 {A : Type'} (x : A) (s : A -> Prop) (h1 : term97 A x s) : term97 A x s.
Proof. exact (EQ_MP (@lem4384773 A x s) (@lem4384770 A x s h1)). Qed.
Lemma lem4384780 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4384781 {A B : Type'} (_50052 : A -> Prop) (_50053 : A -> B) (_50054 : A) : (term115 A B _50052 _50053 _50054) = (term123 A B _50052 _50053 _50054).
Proof. exact (@lem4384780 (term96 A _50054 _50052) (term101 A B _50053 _50052) ((@I (A -> B) _50053 _50054) = (@ARB B))). Qed.
Lemma lem4384795 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4384796 {A B : Type'} (_50054 : A) (_50053 : A -> B) (_50052 : A -> Prop) : (term124 A B _50052 _50053 _50054) = (term125 A B _50054 _50053 _50052).
Proof. exact (@lem4384795 ((@I (A -> B) _50053 _50054) = (@ARB B)) (term101 A B _50053 _50052)). Qed.
Lemma lem4384804 {A : Type'} (_50054 : A) (_50052 : A -> Prop) : (term126 A _50054 _50052) = (term126 A _50054 _50052).
Proof. exact (eq_refl (term126 A _50054 _50052)). Qed.
Lemma lem4384805 {A B : Type'} (_50054 : A) (_50053 : A -> B) (_50052 : A -> Prop) : (term123 A B _50052 _50053 _50054) = (term127 A B _50054 _50053 _50052).
Proof. exact (MK_COMB (@lem4384804 A _50054 _50052) (@lem4384796 A B _50054 _50053 _50052)). Qed.
Lemma lem4384809 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4384810 {A B : Type'} (_50054 : A) (_50053 : A -> B) (_50052 : A -> Prop) : (term127 A B _50054 _50053 _50052) = (term128 A B _50054 _50053 _50052).
Proof. exact (@lem4384809 ((@I (A -> B) _50053 _50054) = (@ARB B)) (term96 A _50054 _50052) (term101 A B _50053 _50052)). Qed.
Lemma lem4384828 {A B : Type'} (_50054 : A) (_50053 : A -> B) (_50052 : A -> Prop) : (term123 A B _50052 _50053 _50054) = (term128 A B _50054 _50053 _50052).
Proof. exact (TRANS (@lem4384805 A B _50054 _50053 _50052) (@lem4384810 A B _50054 _50053 _50052)). Qed.
Lemma lem4384829 {A B : Type'} (_50054 : A) (_50053 : A -> B) (_50052 : A -> Prop) : (term115 A B _50052 _50053 _50054) = (term128 A B _50054 _50053 _50052).
Proof. exact (TRANS (@lem4384781 A B _50052 _50053 _50054) (@lem4384828 A B _50054 _50053 _50052)). Qed.
Lemma lem4384830 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4384831 {A B : Type'} (_50054 : A) (_50053 : A -> B) (_50052 : A -> Prop) : (term129 A B _50052 _50053 _50054) = (term130 A B _50054 _50053 _50052).
Proof. exact (MK_COMB (@lem4384830) (@lem4384829 A B _50054 _50053 _50052)). Qed.
Lemma lem4384847 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4384848 {A B : Type'} (_50054 : A) (_50053 : A -> B) (_50052 : A -> Prop) : (term103 A B _50053 _50054 _50052) = (term131 A B _50054 _50053 _50052).
Proof. exact (@lem4384847 (term96 A _50054 _50052) (term101 A B _50053 _50052)). Qed.
Lemma lem4384854 {A B : Type'} (_50053 : A -> B) (_50054 : A) : (term132 A B _50053 _50054) = (term132 A B _50053 _50054).
Proof. exact (eq_refl (term132 A B _50053 _50054)). Qed.
Lemma lem4384855 {A B : Type'} (_50054 : A) (_50053 : A -> B) (_50052 : A -> Prop) : (term133 A B _50053 _50054 _50052) = (term128 A B _50054 _50053 _50052).
Proof. exact (MK_COMB (@lem4384854 A B _50053 _50054) (@lem4384848 A B _50054 _50053 _50052)). Qed.
Lemma lem4384866 {A B : Type'} (_50054 : A) (_50053 : A -> B) (_50052 : A -> Prop) : ((term115 A B _50052 _50053 _50054) = (term133 A B _50053 _50054 _50052)) = ((term128 A B _50054 _50053 _50052) = (term128 A B _50054 _50053 _50052)).
Proof. exact (MK_COMB (@lem4384831 A B _50054 _50053 _50052) (@lem4384855 A B _50054 _50053 _50052)). Qed.
Lemma lem4384868 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4384869 (x : Prop) : (x = x) = True.
Proof. exact (@lem4384868 Prop x). Qed.
Lemma lem4384870 {A B : Type'} (_50054 : A) (_50053 : A -> B) (_50052 : A -> Prop) : ((term128 A B _50054 _50053 _50052) = (term128 A B _50054 _50053 _50052)) = True.
Proof. exact (@lem4384869 (term128 A B _50054 _50053 _50052)). Qed.
Lemma lem4384871 {A B : Type'} (_50053 : A -> B) (_50054 : A) (_50052 : A -> Prop) : ((term115 A B _50052 _50053 _50054) = (term133 A B _50053 _50054 _50052)) = True.
Proof. exact (TRANS (@lem4384866 A B _50054 _50053 _50052) (@lem4384870 A B _50054 _50053 _50052)). Qed.
Lemma lem4384872 {A B : Type'} (_50053 : A -> B) (_50054 : A) (_50052 : A -> Prop) : True = ((term115 A B _50052 _50053 _50054) = (term133 A B _50053 _50054 _50052)).
Proof. exact (SYM (@lem4384871 A B _50053 _50054 _50052)). Qed.
Lemma lem4384873 {A B : Type'} (_50053 : A -> B) (_50054 : A) (_50052 : A -> Prop) : (term115 A B _50052 _50053 _50054) = (term133 A B _50053 _50054 _50052).
Proof. exact (EQ_MP (@lem4384872 A B _50053 _50054 _50052) (@lem0)). Qed.
Lemma lem4384874 {A B : Type'} (_50053 : A -> B) (_50054 : A) (_50052 : A -> Prop) (h1 : term24 A B) : term133 A B _50053 _50054 _50052.
Proof. exact (EQ_MP (@lem4384873 A B _50053 _50054 _50052) (@lem4384539 A B _50052 _50053 _50054 h1)). Qed.
Lemma lem4384876 (b : Prop) (a : Prop) : (a \/ b) = (term134 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4384877 {A B : Type'} (_50052 : A -> Prop) (_50053 : A -> B) (_50054 : A) : (term133 A B _50053 _50054 _50052) = (term135 A B _50052 _50053 _50054).
Proof. exact (@lem4384876 (term103 A B _50053 _50054 _50052) ((@I (A -> B) _50053 _50054) = (@ARB B))). Qed.
Lemma lem4384879 (a : Prop) (b : Prop) : (term136 a b) = (term137 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4384880 {A B : Type'} (_50053 : A -> B) (_50054 : A) (_50052 : A -> Prop) : (term138 A B _50053 _50054 _50052) = (term139 A B _50053 _50054 _50052).
Proof. exact (@lem4384879 (term101 A B _50053 _50052) (term96 A _50054 _50052)). Qed.
Lemma lem4384882 (a : Prop) : (term140 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4384883 {A B : Type'} (_50053 : A -> B) (_50052 : A -> Prop) : (term141 A B _50053 _50052) = (term95 A B _50053 _50052).
Proof. exact (@lem4384882 (term95 A B _50053 _50052)). Qed.
Lemma lem4384884 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4384885 {A B : Type'} (_50053 : A -> B) (_50052 : A -> Prop) : (term142 A B _50053 _50052) = (term143 A B _50053 _50052).
Proof. exact (MK_COMB (@lem4384884) (@lem4384883 A B _50053 _50052)). Qed.
Lemma lem4384886 {A : Type'} (_50054 : A) (_50052 : A -> Prop) : (term97 A _50054 _50052) = (term97 A _50054 _50052).
Proof. exact (eq_refl (term97 A _50054 _50052)). Qed.
Lemma lem4384887 {A B : Type'} (_50053 : A -> B) (_50054 : A) (_50052 : A -> Prop) : (term139 A B _50053 _50054 _50052) = (term144 A B _50053 _50054 _50052).
Proof. exact (MK_COMB (@lem4384885 A B _50053 _50052) (@lem4384886 A _50054 _50052)). Qed.
Lemma lem4384888 {A B : Type'} (_50053 : A -> B) (_50054 : A) (_50052 : A -> Prop) : (term138 A B _50053 _50054 _50052) = (term144 A B _50053 _50054 _50052).
Proof. exact (TRANS (@lem4384880 A B _50053 _50054 _50052) (@lem4384887 A B _50053 _50054 _50052)). Qed.
Lemma lem4384889 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4384890 {A B : Type'} (_50053 : A -> B) (_50054 : A) (_50052 : A -> Prop) : (term145 A B _50053 _50054 _50052) = (term146 A B _50053 _50054 _50052).
Proof. exact (MK_COMB (@lem4384889) (@lem4384888 A B _50053 _50054 _50052)). Qed.
Lemma lem4384891 {A B : Type'} (_50053 : A -> B) (_50054 : A) : ((@I (A -> B) _50053 _50054) = (@ARB B)) = ((@I (A -> B) _50053 _50054) = (@ARB B)).
Proof. exact (eq_refl ((@I (A -> B) _50053 _50054) = (@ARB B))). Qed.
Lemma lem4384892 {A B : Type'} (_50052 : A -> Prop) (_50053 : A -> B) (_50054 : A) : (term135 A B _50052 _50053 _50054) = (term147 A B _50052 _50053 _50054).
Proof. exact (MK_COMB (@lem4384890 A B _50053 _50054 _50052) (@lem4384891 A B _50053 _50054)). Qed.
Lemma lem4384893 {A B : Type'} (_50052 : A -> Prop) (_50053 : A -> B) (_50054 : A) : (term133 A B _50053 _50054 _50052) = (term147 A B _50052 _50053 _50054).
Proof. exact (TRANS (@lem4384877 A B _50052 _50053 _50054) (@lem4384892 A B _50052 _50053 _50054)). Qed.
Lemma lem4384895 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term97 A x s) (h2 : term16 A B f s) : term144 A B f x s.
Proof. exact (conj (@lem4384766 A B f s h2) (@lem4384774 A x s h1)). Qed.
Lemma lem4384897 {A B : Type'} (_50052 : A -> Prop) (_50053 : A -> B) (_50054 : A) (h1 : term24 A B) : term147 A B _50052 _50053 _50054.
Proof. exact (EQ_MP (@lem4384893 A B _50052 _50053 _50054) (@lem4384874 A B _50053 _50054 _50052 h1)). Qed.
Lemma lem4384898 {A B : Type'} (_50052 : A -> Prop) (_50053 : A -> B) (_50054 : A) (h1 : term24 A B) : term147 A B _50052 _50053 _50054.
Proof. exact (@lem4384897 A B _50052 _50053 _50054 h1). Qed.
Lemma lem4384899 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : term24 A B) : term147 A B s f x.
Proof. exact (@lem4384898 A B s f x h1). Qed.
Lemma lem4384902 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term24 A B) (h2 : term97 A x s) (h3 : term16 A B f s) : (@I (A -> B) f x) = (@ARB B).
Proof. exact (@lem4384899 A B s f x h1 (@lem4384895 A B x f s h2 h3)). Qed.
Lemma lem4384903 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term24 A B) (h2 : term97 A x s) (h3 : term16 A B f s) : term148 A B f x.
Proof. exact (fun h0 : term149 A B f x => @lem4384902 A B x f s h1 h2 h3). Qed.
Lemma lem4384905 (p : Prop) : (term118 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4384906 {A B : Type'} (f : A -> B) (x : A) : (term148 A B f x) = ((@I (A -> B) f x) = (@ARB B)).
Proof. exact (@lem4384905 ((@I (A -> B) f x) = (@ARB B))). Qed.
Lemma lem4384907 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term24 A B) (h2 : term97 A x s) (h3 : term16 A B f s) : (@I (A -> B) f x) = (@ARB B).
Proof. exact (EQ_MP (@lem4384906 A B f x) (@lem4384903 A B x f s h1 h2 h3)). Qed.
Lemma lem4384909 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem4384910 {B : Type'} (x : B) : x = x.
Proof. exact (@lem4384909 B x). Qed.
Lemma lem4384911 {A B : Type'} (f : A -> B) (x : A) : (@I (A -> B) f x) = (@I (A -> B) f x).
Proof. exact (@lem4384910 B (@I (A -> B) f x)). Qed.
Lemma lem4384912 {A B : Type'} (f : A -> B) (x : A) : term119 A B f x.
Proof. exact (fun h0 : term120 A B f x => @lem4384911 A B f x). Qed.
Lemma lem4384914 (p : Prop) : (term118 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4384915 {A B : Type'} (f : A -> B) (x : A) : (term119 A B f x) = ((@I (A -> B) f x) = (@I (A -> B) f x)).
Proof. exact (@lem4384914 ((@I (A -> B) f x) = (@I (A -> B) f x))). Qed.
Lemma lem4384916 {A B : Type'} (f : A -> B) (x : A) : (@I (A -> B) f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem4384915 A B f x) (@lem4384912 A B f x)). Qed.
Lemma lem4384934 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4384935 {B : Type'} (y : B) (x : B) (z : B) : (term150 B x y z) = (term151 B y x z).
Proof. exact (@lem4384934 (y = z) (term152 B x z)). Qed.
Lemma lem4384945 {B : Type'} (x : B) (y : B) : (term153 B x y) = (term153 B x y).
Proof. exact (eq_refl (term153 B x y)). Qed.
Lemma lem4384946 {B : Type'} (y : B) (x : B) (z : B) : (term116 B x y z) = (term154 B y x z).
Proof. exact (MK_COMB (@lem4384945 B x y) (@lem4384935 B y x z)). Qed.
Lemma lem4384950 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4384951 {B : Type'} (y : B) (x : B) (z : B) : (term154 B y x z) = (term155 B y x z).
Proof. exact (@lem4384950 (y = z) (term152 B x y) (term152 B x z)). Qed.
Lemma lem4384973 {B : Type'} (y : B) (x : B) (z : B) : (term116 B x y z) = (term155 B y x z).
Proof. exact (TRANS (@lem4384946 B y x z) (@lem4384951 B y x z)). Qed.
Lemma lem4384974 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4384975 {B : Type'} (y : B) (x : B) (z : B) : (term156 B x y z) = (term157 B y x z).
Proof. exact (MK_COMB (@lem4384974) (@lem4384973 B y x z)). Qed.
Lemma lem4384997 {B : Type'} (y : B) (x : B) (z : B) : (term155 B y x z) = (term155 B y x z).
Proof. exact (eq_refl (term155 B y x z)). Qed.
Lemma lem4384998 {B : Type'} (y : B) (x : B) (z : B) : ((term116 B x y z) = (term155 B y x z)) = ((term155 B y x z) = (term155 B y x z)).
Proof. exact (MK_COMB (@lem4384975 B y x z) (@lem4384997 B y x z)). Qed.
Lemma lem4385000 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4385001 (x : Prop) : (x = x) = True.
Proof. exact (@lem4385000 Prop x). Qed.
Lemma lem4385002 {B : Type'} (y : B) (x : B) (z : B) : ((term155 B y x z) = (term155 B y x z)) = True.
Proof. exact (@lem4385001 (term155 B y x z)). Qed.
Lemma lem4385003 {B : Type'} (y : B) (x : B) (z : B) : ((term116 B x y z) = (term155 B y x z)) = True.
Proof. exact (TRANS (@lem4384998 B y x z) (@lem4385002 B y x z)). Qed.
Lemma lem4385004 {B : Type'} (y : B) (x : B) (z : B) : True = ((term116 B x y z) = (term155 B y x z)).
Proof. exact (SYM (@lem4385003 B y x z)). Qed.
Lemma lem4385005 {B : Type'} (y : B) (x : B) (z : B) : (term116 B x y z) = (term155 B y x z).
Proof. exact (EQ_MP (@lem4385004 B y x z) (@lem0)). Qed.
Lemma lem4385006 {B : Type'} (y : B) (x : B) (z : B) : term155 B y x z.
Proof. exact (EQ_MP (@lem4385005 B y x z) (@lem4384727 B x y z)). Qed.
Lemma lem4385008 (b : Prop) (a : Prop) : (a \/ b) = (term134 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4385009 {B : Type'} (x : B) (y : B) (z : B) : (term155 B y x z) = (term158 B x y z).
Proof. exact (@lem4385008 (term159 B y x z) (y = z)). Qed.
Lemma lem4385011 (a : Prop) (b : Prop) : (term136 a b) = (term137 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4385012 {B : Type'} (y : B) (x : B) (z : B) : (term160 B y x z) = (term161 B y x z).
Proof. exact (@lem4385011 (term152 B x y) (term152 B x z)). Qed.
Lemma lem4385014 (a : Prop) : (term140 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4385015 {B : Type'} (x : B) (y : B) : (term162 B x y) = (x = y).
Proof. exact (@lem4385014 (x = y)). Qed.
Lemma lem4385016 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4385017 {B : Type'} (x : B) (y : B) : (term163 B x y) = (term164 B x y).
Proof. exact (MK_COMB (@lem4385016) (@lem4385015 B x y)). Qed.
Lemma lem4385019 (a : Prop) : (term140 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4385020 {B : Type'} (x : B) (z : B) : (term162 B x z) = (x = z).
Proof. exact (@lem4385019 (x = z)). Qed.
Lemma lem4385021 {B : Type'} (y : B) (x : B) (z : B) : (term161 B y x z) = (term165 B y x z).
Proof. exact (MK_COMB (@lem4385017 B x y) (@lem4385020 B x z)). Qed.
Lemma lem4385022 {B : Type'} (y : B) (x : B) (z : B) : (term160 B y x z) = (term165 B y x z).
Proof. exact (TRANS (@lem4385012 B y x z) (@lem4385021 B y x z)). Qed.
Lemma lem4385023 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4385024 {B : Type'} (y : B) (x : B) (z : B) : (term166 B y x z) = (term167 B y x z).
Proof. exact (MK_COMB (@lem4385023) (@lem4385022 B y x z)). Qed.
Lemma lem4385025 {B : Type'} (y : B) (z : B) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem4385026 {B : Type'} (x : B) (y : B) (z : B) : (term158 B x y z) = (term168 B x y z).
Proof. exact (MK_COMB (@lem4385024 B y x z) (@lem4385025 B y z)). Qed.
Lemma lem4385027 {B : Type'} (x : B) (y : B) (z : B) : (term155 B y x z) = (term168 B x y z).
Proof. exact (TRANS (@lem4385009 B x y z) (@lem4385026 B x y z)). Qed.
Lemma lem4385029 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term24 A B) (h2 : term97 A x s) (h3 : term16 A B f s) : term169 A B f x.
Proof. exact (conj (@lem4384907 A B x f s h1 h2 h3) (@lem4384916 A B f x)). Qed.
Lemma lem4385031 {B : Type'} (x : B) (y : B) (z : B) : term168 B x y z.
Proof. exact (EQ_MP (@lem4385027 B x y z) (@lem4385006 B y x z)). Qed.
Lemma lem4385032 {B : Type'} (x : B) (y : B) (z : B) : term168 B x y z.
Proof. exact (@lem4385031 B x y z). Qed.
Lemma lem4385033 {A B : Type'} (f : A -> B) (x : A) : term170 A B f x.
Proof. exact (@lem4385032 B (@I (A -> B) f x) (@ARB B) (@I (A -> B) f x)). Qed.
Lemma lem4385036 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term24 A B) (h2 : term97 A x s) (h3 : term16 A B f s) : (@ARB B) = (@I (A -> B) f x).
Proof. exact (@lem4385033 A B f x (@lem4385029 A B x f s h1 h2 h3)). Qed.
Lemma lem4385037 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term24 A B) (h2 : term97 A x s) (h3 : term16 A B f s) : term171 A B f x.
Proof. exact (fun h0 : term172 A B f x => @lem4385036 A B x f s h1 h2 h3). Qed.
Lemma lem4385039 (p : Prop) : (term118 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4385040 {A B : Type'} (f : A -> B) (x : A) : (term171 A B f x) = ((@ARB B) = (@I (A -> B) f x)).
Proof. exact (@lem4385039 ((@ARB B) = (@I (A -> B) f x))). Qed.
Lemma lem4385041 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term24 A B) (h2 : term97 A x s) (h3 : term16 A B f s) : (@ARB B) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem4385040 A B f x) (@lem4385037 A B x f s h1 h2 h3)). Qed.
Lemma lem4385043 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) (h1 : term23 A B f g x) : term99 A B f g x.
Proof. exact (EQ_MP (@lem4384272 A B f g x) (@lem4383968 A B f g x h1)). Qed.
Lemma lem4385044 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) (h1 : term23 A B f g x) : term173 A B f g x.
Proof. exact (fun h0 : (@I (A -> B) f x) = (@I (A -> B) g x) => @lem4385043 A B f g x h1). Qed.
Lemma lem4385046 (p : Prop) : (term122 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4385047 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) : (term173 A B f g x) = (term99 A B f g x).
Proof. exact (@lem4385046 ((@I (A -> B) f x) = (@I (A -> B) g x))). Qed.
Lemma lem4385048 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) (h1 : term23 A B f g x) : term99 A B f g x.
Proof. exact (EQ_MP (@lem4385047 A B f g x) (@lem4385044 A B f g x h1)). Qed.
Lemma lem4385066 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4385067 {B : Type'} (y : B) (x : B) (z : B) : (term150 B x y z) = (term151 B y x z).
Proof. exact (@lem4385066 (y = z) (term152 B x z)). Qed.
Lemma lem4385077 {B : Type'} (x : B) (y : B) : (term153 B x y) = (term153 B x y).
Proof. exact (eq_refl (term153 B x y)). Qed.
Lemma lem4385078 {B : Type'} (y : B) (x : B) (z : B) : (term116 B x y z) = (term154 B y x z).
Proof. exact (MK_COMB (@lem4385077 B x y) (@lem4385067 B y x z)). Qed.
Lemma lem4385082 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4385083 {B : Type'} (y : B) (x : B) (z : B) : (term154 B y x z) = (term155 B y x z).
Proof. exact (@lem4385082 (y = z) (term152 B x y) (term152 B x z)). Qed.
Lemma lem4385105 {B : Type'} (y : B) (x : B) (z : B) : (term116 B x y z) = (term155 B y x z).
Proof. exact (TRANS (@lem4385078 B y x z) (@lem4385083 B y x z)). Qed.
Lemma lem4385106 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4385107 {B : Type'} (y : B) (x : B) (z : B) : (term156 B x y z) = (term157 B y x z).
Proof. exact (MK_COMB (@lem4385106) (@lem4385105 B y x z)). Qed.
Lemma lem4385111 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4385112 {B : Type'} (x : B) (y : B) (z : B) : (term174 B x y z) = (term116 B x y z).
Proof. exact (@lem4385111 (term152 B x y) (term152 B x z) (y = z)). Qed.
Lemma lem4385128 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4385129 {B : Type'} (y : B) (x : B) (z : B) : (term150 B x y z) = (term151 B y x z).
Proof. exact (@lem4385128 (y = z) (term152 B x z)). Qed.
Lemma lem4385139 {B : Type'} (x : B) (y : B) : (term153 B x y) = (term153 B x y).
Proof. exact (eq_refl (term153 B x y)). Qed.
Lemma lem4385140 {B : Type'} (y : B) (x : B) (z : B) : (term116 B x y z) = (term154 B y x z).
Proof. exact (MK_COMB (@lem4385139 B x y) (@lem4385129 B y x z)). Qed.
Lemma lem4385144 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4385145 {B : Type'} (y : B) (x : B) (z : B) : (term154 B y x z) = (term155 B y x z).
Proof. exact (@lem4385144 (y = z) (term152 B x y) (term152 B x z)). Qed.
Lemma lem4385167 {B : Type'} (y : B) (x : B) (z : B) : (term116 B x y z) = (term155 B y x z).
Proof. exact (TRANS (@lem4385140 B y x z) (@lem4385145 B y x z)). Qed.
Lemma lem4385168 {B : Type'} (y : B) (x : B) (z : B) : (term174 B x y z) = (term155 B y x z).
Proof. exact (TRANS (@lem4385112 B x y z) (@lem4385167 B y x z)). Qed.
Lemma lem4385169 {B : Type'} (y : B) (x : B) (z : B) : ((term116 B x y z) = (term174 B x y z)) = ((term155 B y x z) = (term155 B y x z)).
Proof. exact (MK_COMB (@lem4385107 B y x z) (@lem4385168 B y x z)). Qed.
Lemma lem4385171 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4385172 (x : Prop) : (x = x) = True.
Proof. exact (@lem4385171 Prop x). Qed.
Lemma lem4385173 {B : Type'} (y : B) (x : B) (z : B) : ((term155 B y x z) = (term155 B y x z)) = True.
Proof. exact (@lem4385172 (term155 B y x z)). Qed.
Lemma lem4385174 {B : Type'} (x : B) (y : B) (z : B) : ((term116 B x y z) = (term174 B x y z)) = True.
Proof. exact (TRANS (@lem4385169 B y x z) (@lem4385173 B y x z)). Qed.
Lemma lem4385175 {B : Type'} (x : B) (y : B) (z : B) : True = ((term116 B x y z) = (term174 B x y z)).
Proof. exact (SYM (@lem4385174 B x y z)). Qed.
Lemma lem4385176 {B : Type'} (x : B) (y : B) (z : B) : (term116 B x y z) = (term174 B x y z).
Proof. exact (EQ_MP (@lem4385175 B x y z) (@lem0)). Qed.
Lemma lem4385177 {B : Type'} (x : B) (y : B) (z : B) : term174 B x y z.
Proof. exact (EQ_MP (@lem4385176 B x y z) (@lem4384727 B x y z)). Qed.
Lemma lem4385179 (b : Prop) (a : Prop) : (a \/ b) = (term134 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4385180 {B : Type'} (y : B) (x : B) (z : B) : (term174 B x y z) = (term175 B y x z).
Proof. exact (@lem4385179 (term176 B x y z) (term152 B x z)). Qed.
Lemma lem4385182 (a : Prop) (b : Prop) : (term136 a b) = (term137 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4385183 {B : Type'} (x : B) (y : B) (z : B) : (term177 B x y z) = (term178 B x y z).
Proof. exact (@lem4385182 (term152 B x y) (y = z)). Qed.
Lemma lem4385185 (a : Prop) : (term140 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4385186 {B : Type'} (x : B) (y : B) : (term162 B x y) = (x = y).
Proof. exact (@lem4385185 (x = y)). Qed.
Lemma lem4385187 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4385188 {B : Type'} (x : B) (y : B) : (term163 B x y) = (term164 B x y).
Proof. exact (MK_COMB (@lem4385187) (@lem4385186 B x y)). Qed.
Lemma lem4385189 {B : Type'} (y : B) (z : B) : (term152 B y z) = (term152 B y z).
Proof. exact (eq_refl (term152 B y z)). Qed.
Lemma lem4385190 {B : Type'} (x : B) (y : B) (z : B) : (term178 B x y z) = (term179 B x y z).
Proof. exact (MK_COMB (@lem4385188 B x y) (@lem4385189 B y z)). Qed.
Lemma lem4385191 {B : Type'} (x : B) (y : B) (z : B) : (term177 B x y z) = (term179 B x y z).
Proof. exact (TRANS (@lem4385183 B x y z) (@lem4385190 B x y z)). Qed.
Lemma lem4385192 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4385193 {B : Type'} (x : B) (y : B) (z : B) : (term180 B x y z) = (term181 B x y z).
Proof. exact (MK_COMB (@lem4385192) (@lem4385191 B x y z)). Qed.
Lemma lem4385194 {B : Type'} (x : B) (z : B) : (term152 B x z) = (term152 B x z).
Proof. exact (eq_refl (term152 B x z)). Qed.
Lemma lem4385195 {B : Type'} (y : B) (x : B) (z : B) : (term175 B y x z) = (term182 B y x z).
Proof. exact (MK_COMB (@lem4385193 B x y z) (@lem4385194 B x z)). Qed.
Lemma lem4385196 {B : Type'} (y : B) (x : B) (z : B) : (term174 B x y z) = (term182 B y x z).
Proof. exact (TRANS (@lem4385180 B y x z) (@lem4385195 B y x z)). Qed.
Lemma lem4385198 {A B : Type'} (g : A -> B) (x : A) (f : A -> B) (s : A -> Prop) (h1 : term24 A B) (h2 : term23 A B f g x) (h3 : term97 A x s) (h4 : term16 A B f s) : term183 A B f g x.
Proof. exact (conj (@lem4385041 A B x f s h1 h3 h4) (@lem4385048 A B f g x h2)). Qed.
Lemma lem4385200 {B : Type'} (y : B) (x : B) (z : B) : term182 B y x z.
Proof. exact (EQ_MP (@lem4385196 B y x z) (@lem4385177 B x y z)). Qed.
Lemma lem4385201 {B : Type'} (y : B) (x : B) (z : B) : term182 B y x z.
Proof. exact (@lem4385200 B y x z). Qed.
Lemma lem4385202 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) : term184 A B f g x.
Proof. exact (@lem4385201 B (@I (A -> B) f x) (@ARB B) (@I (A -> B) g x)). Qed.
Lemma lem4385205 {A B : Type'} (g : A -> B) (x : A) (f : A -> B) (s : A -> Prop) (h1 : term24 A B) (h2 : term23 A B f g x) (h3 : term97 A x s) (h4 : term16 A B f s) : term172 A B g x.
Proof. exact (@lem4385202 A B f g x (@lem4385198 A B g x f s h1 h2 h3 h4)). Qed.
Lemma lem4385206 {A B : Type'} (g : A -> B) (x : A) (f : A -> B) (s : A -> Prop) (h1 : term24 A B) (h2 : term23 A B f g x) (h3 : term97 A x s) (h4 : term16 A B f s) : term185 A B g x.
Proof. exact (fun h0 : (@ARB B) = (@I (A -> B) g x) => @lem4385205 A B g x f s h1 h2 h3 h4). Qed.
Lemma lem4385208 (p : Prop) : (term122 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4385209 {A B : Type'} (g : A -> B) (x : A) : (term185 A B g x) = (term172 A B g x).
Proof. exact (@lem4385208 ((@ARB B) = (@I (A -> B) g x))). Qed.
Lemma lem4385210 {A B : Type'} (g : A -> B) (x : A) (f : A -> B) (s : A -> Prop) (h1 : term24 A B) (h2 : term23 A B f g x) (h3 : term97 A x s) (h4 : term16 A B f s) : term172 A B g x.
Proof. exact (EQ_MP (@lem4385209 A B g x) (@lem4385206 A B g x f s h1 h2 h3 h4)). Qed.
Lemma lem4385212 (b : Prop) (a : Prop) : (a \/ b) = (term134 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4385213 {B : Type'} (z : B) (x : B) (y : B) : (term116 B x y z) = (term186 B z x y).
Proof. exact (@lem4385212 (term150 B x y z) (term152 B x y)). Qed.
Lemma lem4385215 (a : Prop) (b : Prop) : (term136 a b) = (term137 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4385216 {B : Type'} (x : B) (y : B) (z : B) : (term187 B x y z) = (term188 B x y z).
Proof. exact (@lem4385215 (term152 B x z) (y = z)). Qed.
Lemma lem4385218 (a : Prop) : (term140 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4385219 {B : Type'} (x : B) (z : B) : (term162 B x z) = (x = z).
Proof. exact (@lem4385218 (x = z)). Qed.
Lemma lem4385220 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4385221 {B : Type'} (x : B) (z : B) : (term163 B x z) = (term164 B x z).
Proof. exact (MK_COMB (@lem4385220) (@lem4385219 B x z)). Qed.
Lemma lem4385222 {B : Type'} (y : B) (z : B) : (term152 B y z) = (term152 B y z).
Proof. exact (eq_refl (term152 B y z)). Qed.
Lemma lem4385223 {B : Type'} (x : B) (y : B) (z : B) : (term188 B x y z) = (term189 B x y z).
Proof. exact (MK_COMB (@lem4385221 B x z) (@lem4385222 B y z)). Qed.
Lemma lem4385224 {B : Type'} (x : B) (y : B) (z : B) : (term187 B x y z) = (term189 B x y z).
Proof. exact (TRANS (@lem4385216 B x y z) (@lem4385223 B x y z)). Qed.
Lemma lem4385225 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4385226 {B : Type'} (x : B) (y : B) (z : B) : (term190 B x y z) = (term191 B x y z).
Proof. exact (MK_COMB (@lem4385225) (@lem4385224 B x y z)). Qed.
Lemma lem4385227 {B : Type'} (x : B) (y : B) : (term152 B x y) = (term152 B x y).
Proof. exact (eq_refl (term152 B x y)). Qed.
Lemma lem4385228 {B : Type'} (z : B) (x : B) (y : B) : (term186 B z x y) = (term192 B z x y).
Proof. exact (MK_COMB (@lem4385226 B x y z) (@lem4385227 B x y)). Qed.
Lemma lem4385229 {B : Type'} (z : B) (x : B) (y : B) : (term116 B x y z) = (term192 B z x y).
Proof. exact (TRANS (@lem4385213 B z x y) (@lem4385228 B z x y)). Qed.
Lemma lem4385231 {A B : Type'} (g : A -> B) (x : A) (f : A -> B) (s : A -> Prop) (h1 : term24 A B) (h2 : term23 A B f g x) (h3 : term97 A x s) (h4 : term16 A B f s) : term193 A B g x.
Proof. exact (conj (@lem4384759 A B g x) (@lem4385210 A B g x f s h1 h2 h3 h4)). Qed.
Lemma lem4385233 {B : Type'} (z : B) (x : B) (y : B) : term192 B z x y.
Proof. exact (EQ_MP (@lem4385229 B z x y) (@lem4384727 B x y z)). Qed.
Lemma lem4385234 {B : Type'} (z : B) (x : B) (y : B) : term192 B z x y.
Proof. exact (@lem4385233 B z x y). Qed.
Lemma lem4385235 {A B : Type'} (g : A -> B) (x : A) : term194 A B g x.
Proof. exact (@lem4385234 B (@I (A -> B) g x) (@I (A -> B) g x) (@ARB B)). Qed.
Lemma lem4385238 {A B : Type'} (g : A -> B) (x : A) (f : A -> B) (s : A -> Prop) (h1 : term24 A B) (h2 : term23 A B f g x) (h3 : term97 A x s) (h4 : term16 A B f s) : term149 A B g x.
Proof. exact (@lem4385235 A B g x (@lem4385231 A B g x f s h1 h2 h3 h4)). Qed.
Lemma lem4385239 {A B : Type'} (g : A -> B) (x : A) (f : A -> B) (s : A -> Prop) (h1 : term24 A B) (h2 : term23 A B f g x) (h3 : term97 A x s) (h4 : term16 A B f s) : term195 A B g x.
Proof. exact (fun h0 : (@I (A -> B) g x) = (@ARB B) => @lem4385238 A B g x f s h1 h2 h3 h4). Qed.
Lemma lem4385241 (p : Prop) : (term122 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4385242 {A B : Type'} (g : A -> B) (x : A) : (term195 A B g x) = (term149 A B g x).
Proof. exact (@lem4385241 ((@I (A -> B) g x) = (@ARB B))). Qed.
Lemma lem4385243 {A B : Type'} (g : A -> B) (x : A) (f : A -> B) (s : A -> Prop) (h1 : term24 A B) (h2 : term23 A B f g x) (h3 : term97 A x s) (h4 : term16 A B f s) : term149 A B g x.
Proof. exact (EQ_MP (@lem4385242 A B g x) (@lem4385239 A B g x f s h1 h2 h3 h4)). Qed.
Lemma lem4385249 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4385250 {A B : Type'} (_50052 : A -> Prop) (_50053 : A -> B) (_50054 : A) : (term115 A B _50052 _50053 _50054) = (term123 A B _50052 _50053 _50054).
Proof. exact (@lem4385249 (term96 A _50054 _50052) (term101 A B _50053 _50052) ((@I (A -> B) _50053 _50054) = (@ARB B))). Qed.
Lemma lem4385264 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4385265 {A B : Type'} (_50054 : A) (_50053 : A -> B) (_50052 : A -> Prop) : (term124 A B _50052 _50053 _50054) = (term125 A B _50054 _50053 _50052).
Proof. exact (@lem4385264 ((@I (A -> B) _50053 _50054) = (@ARB B)) (term101 A B _50053 _50052)). Qed.
Lemma lem4385273 {A : Type'} (_50054 : A) (_50052 : A -> Prop) : (term126 A _50054 _50052) = (term126 A _50054 _50052).
Proof. exact (eq_refl (term126 A _50054 _50052)). Qed.
Lemma lem4385274 {A B : Type'} (_50054 : A) (_50053 : A -> B) (_50052 : A -> Prop) : (term123 A B _50052 _50053 _50054) = (term127 A B _50054 _50053 _50052).
Proof. exact (MK_COMB (@lem4385273 A _50054 _50052) (@lem4385265 A B _50054 _50053 _50052)). Qed.
Lemma lem4385278 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4385279 {A B : Type'} (_50054 : A) (_50053 : A -> B) (_50052 : A -> Prop) : (term127 A B _50054 _50053 _50052) = (term128 A B _50054 _50053 _50052).
Proof. exact (@lem4385278 ((@I (A -> B) _50053 _50054) = (@ARB B)) (term96 A _50054 _50052) (term101 A B _50053 _50052)). Qed.
Lemma lem4385297 {A B : Type'} (_50054 : A) (_50053 : A -> B) (_50052 : A -> Prop) : (term123 A B _50052 _50053 _50054) = (term128 A B _50054 _50053 _50052).
Proof. exact (TRANS (@lem4385274 A B _50054 _50053 _50052) (@lem4385279 A B _50054 _50053 _50052)). Qed.
Lemma lem4385298 {A B : Type'} (_50054 : A) (_50053 : A -> B) (_50052 : A -> Prop) : (term115 A B _50052 _50053 _50054) = (term128 A B _50054 _50053 _50052).
Proof. exact (TRANS (@lem4385250 A B _50052 _50053 _50054) (@lem4385297 A B _50054 _50053 _50052)). Qed.
Lemma lem4385299 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4385300 {A B : Type'} (_50054 : A) (_50053 : A -> B) (_50052 : A -> Prop) : (term129 A B _50052 _50053 _50054) = (term130 A B _50054 _50053 _50052).
Proof. exact (MK_COMB (@lem4385299) (@lem4385298 A B _50054 _50053 _50052)). Qed.
Lemma lem4385314 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4385315 {A B : Type'} (_50054 : A) (_50053 : A -> B) (_50052 : A -> Prop) : (term124 A B _50052 _50053 _50054) = (term125 A B _50054 _50053 _50052).
Proof. exact (@lem4385314 ((@I (A -> B) _50053 _50054) = (@ARB B)) (term101 A B _50053 _50052)). Qed.
Lemma lem4385323 {A : Type'} (_50054 : A) (_50052 : A -> Prop) : (term126 A _50054 _50052) = (term126 A _50054 _50052).
Proof. exact (eq_refl (term126 A _50054 _50052)). Qed.
Lemma lem4385324 {A B : Type'} (_50054 : A) (_50053 : A -> B) (_50052 : A -> Prop) : (term123 A B _50052 _50053 _50054) = (term127 A B _50054 _50053 _50052).
Proof. exact (MK_COMB (@lem4385323 A _50054 _50052) (@lem4385315 A B _50054 _50053 _50052)). Qed.
Lemma lem4385328 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4385329 {A B : Type'} (_50054 : A) (_50053 : A -> B) (_50052 : A -> Prop) : (term127 A B _50054 _50053 _50052) = (term128 A B _50054 _50053 _50052).
Proof. exact (@lem4385328 ((@I (A -> B) _50053 _50054) = (@ARB B)) (term96 A _50054 _50052) (term101 A B _50053 _50052)). Qed.
Lemma lem4385347 {A B : Type'} (_50054 : A) (_50053 : A -> B) (_50052 : A -> Prop) : (term123 A B _50052 _50053 _50054) = (term128 A B _50054 _50053 _50052).
Proof. exact (TRANS (@lem4385324 A B _50054 _50053 _50052) (@lem4385329 A B _50054 _50053 _50052)). Qed.
Lemma lem4385348 {A B : Type'} (_50054 : A) (_50053 : A -> B) (_50052 : A -> Prop) : ((term115 A B _50052 _50053 _50054) = (term123 A B _50052 _50053 _50054)) = ((term128 A B _50054 _50053 _50052) = (term128 A B _50054 _50053 _50052)).
Proof. exact (MK_COMB (@lem4385300 A B _50054 _50053 _50052) (@lem4385347 A B _50054 _50053 _50052)). Qed.
Lemma lem4385350 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4385351 (x : Prop) : (x = x) = True.
Proof. exact (@lem4385350 Prop x). Qed.
Lemma lem4385352 {A B : Type'} (_50054 : A) (_50053 : A -> B) (_50052 : A -> Prop) : ((term128 A B _50054 _50053 _50052) = (term128 A B _50054 _50053 _50052)) = True.
Proof. exact (@lem4385351 (term128 A B _50054 _50053 _50052)). Qed.
Lemma lem4385353 {A B : Type'} (_50052 : A -> Prop) (_50053 : A -> B) (_50054 : A) : ((term115 A B _50052 _50053 _50054) = (term123 A B _50052 _50053 _50054)) = True.
Proof. exact (TRANS (@lem4385348 A B _50054 _50053 _50052) (@lem4385352 A B _50054 _50053 _50052)). Qed.
Lemma lem4385354 {A B : Type'} (_50052 : A -> Prop) (_50053 : A -> B) (_50054 : A) : True = ((term115 A B _50052 _50053 _50054) = (term123 A B _50052 _50053 _50054)).
Proof. exact (SYM (@lem4385353 A B _50052 _50053 _50054)). Qed.
Lemma lem4385355 {A B : Type'} (_50052 : A -> Prop) (_50053 : A -> B) (_50054 : A) : (term115 A B _50052 _50053 _50054) = (term123 A B _50052 _50053 _50054).
Proof. exact (EQ_MP (@lem4385354 A B _50052 _50053 _50054) (@lem0)). Qed.
Lemma lem4385356 {A B : Type'} (_50052 : A -> Prop) (_50053 : A -> B) (_50054 : A) (h1 : term24 A B) : term123 A B _50052 _50053 _50054.
Proof. exact (EQ_MP (@lem4385355 A B _50052 _50053 _50054) (@lem4384539 A B _50052 _50053 _50054 h1)). Qed.
Lemma lem4385358 (b : Prop) (a : Prop) : (a \/ b) = (term134 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4385359 {A B : Type'} (_50053 : A -> B) (_50054 : A) (_50052 : A -> Prop) : (term123 A B _50052 _50053 _50054) = (term196 A B _50053 _50054 _50052).
Proof. exact (@lem4385358 (term124 A B _50052 _50053 _50054) (term96 A _50054 _50052)). Qed.
Lemma lem4385361 (a : Prop) (b : Prop) : (term136 a b) = (term137 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4385362 {A B : Type'} (_50052 : A -> Prop) (_50053 : A -> B) (_50054 : A) : (term197 A B _50052 _50053 _50054) = (term198 A B _50052 _50053 _50054).
Proof. exact (@lem4385361 (term101 A B _50053 _50052) ((@I (A -> B) _50053 _50054) = (@ARB B))). Qed.
Lemma lem4385364 (a : Prop) : (term140 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4385365 {A B : Type'} (_50053 : A -> B) (_50052 : A -> Prop) : (term141 A B _50053 _50052) = (term95 A B _50053 _50052).
Proof. exact (@lem4385364 (term95 A B _50053 _50052)). Qed.
Lemma lem4385366 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4385367 {A B : Type'} (_50053 : A -> B) (_50052 : A -> Prop) : (term142 A B _50053 _50052) = (term143 A B _50053 _50052).
Proof. exact (MK_COMB (@lem4385366) (@lem4385365 A B _50053 _50052)). Qed.
Lemma lem4385368 {A B : Type'} (_50053 : A -> B) (_50054 : A) : (term149 A B _50053 _50054) = (term149 A B _50053 _50054).
Proof. exact (eq_refl (term149 A B _50053 _50054)). Qed.
Lemma lem4385369 {A B : Type'} (_50052 : A -> Prop) (_50053 : A -> B) (_50054 : A) : (term198 A B _50052 _50053 _50054) = (term199 A B _50052 _50053 _50054).
Proof. exact (MK_COMB (@lem4385367 A B _50053 _50052) (@lem4385368 A B _50053 _50054)). Qed.
Lemma lem4385370 {A B : Type'} (_50052 : A -> Prop) (_50053 : A -> B) (_50054 : A) : (term197 A B _50052 _50053 _50054) = (term199 A B _50052 _50053 _50054).
Proof. exact (TRANS (@lem4385362 A B _50052 _50053 _50054) (@lem4385369 A B _50052 _50053 _50054)). Qed.
Lemma lem4385371 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4385372 {A B : Type'} (_50052 : A -> Prop) (_50053 : A -> B) (_50054 : A) : (term200 A B _50052 _50053 _50054) = (term201 A B _50052 _50053 _50054).
Proof. exact (MK_COMB (@lem4385371) (@lem4385370 A B _50052 _50053 _50054)). Qed.
Lemma lem4385373 {A : Type'} (_50054 : A) (_50052 : A -> Prop) : (term96 A _50054 _50052) = (term96 A _50054 _50052).
Proof. exact (eq_refl (term96 A _50054 _50052)). Qed.
Lemma lem4385374 {A B : Type'} (_50053 : A -> B) (_50054 : A) (_50052 : A -> Prop) : (term196 A B _50053 _50054 _50052) = (term202 A B _50053 _50054 _50052).
Proof. exact (MK_COMB (@lem4385372 A B _50052 _50053 _50054) (@lem4385373 A _50054 _50052)). Qed.
Lemma lem4385375 {A B : Type'} (_50053 : A -> B) (_50054 : A) (_50052 : A -> Prop) : (term123 A B _50052 _50053 _50054) = (term202 A B _50053 _50054 _50052).
Proof. exact (TRANS (@lem4385359 A B _50053 _50054 _50052) (@lem4385374 A B _50053 _50054 _50052)). Qed.
Lemma lem4385377 {A B : Type'} (x : A) (f : A -> B) (g : A -> B) (s : A -> Prop) (h1 : term24 A B) (h2 : term23 A B f g x) (h3 : term97 A x s) (h4 : term16 A B f s) (h5 : term16 A B g s) : term199 A B s g x.
Proof. exact (conj (@lem4384750 A B g s h5) (@lem4385243 A B g x f s h1 h2 h3 h4)). Qed.
Lemma lem4385379 {A B : Type'} (_50053 : A -> B) (_50054 : A) (_50052 : A -> Prop) (h1 : term24 A B) : term202 A B _50053 _50054 _50052.
Proof. exact (EQ_MP (@lem4385375 A B _50053 _50054 _50052) (@lem4385356 A B _50052 _50053 _50054 h1)). Qed.
Lemma lem4385380 {A B : Type'} (_50053 : A -> B) (_50054 : A) (_50052 : A -> Prop) (h1 : term24 A B) : term202 A B _50053 _50054 _50052.
Proof. exact (@lem4385379 A B _50053 _50054 _50052 h1). Qed.
Lemma lem4385381 {A B : Type'} (g : A -> B) (x : A) (s : A -> Prop) (h1 : term24 A B) : term202 A B g x s.
Proof. exact (@lem4385380 A B g x s h1). Qed.
Lemma lem4385384 {A B : Type'} (x : A) (f : A -> B) (g : A -> B) (s : A -> Prop) (h1 : term24 A B) (h2 : term23 A B f g x) (h3 : term97 A x s) (h4 : term16 A B f s) (h5 : term16 A B g s) : term96 A x s.
Proof. exact (@lem4385381 A B g x s h1 (@lem4385377 A B x f g s h1 h2 h3 h4 h5)). Qed.
Lemma lem4385385 {A B : Type'} (x : A) (f : A -> B) (g : A -> B) (s : A -> Prop) (h1 : term24 A B) (h2 : term23 A B f g x) (h3 : term16 A B f s) (h4 : term16 A B g s) : term203 A x s.
Proof. exact (fun h0 : term97 A x s => @lem4385384 A B x f g s h1 h2 h0 h3 h4). Qed.
Lemma lem4385387 (p : Prop) : (term118 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4385388 {A : Type'} (x : A) (s : A -> Prop) : (term203 A x s) = (term96 A x s).
Proof. exact (@lem4385387 (term96 A x s)). Qed.
Lemma lem4385389 {A B : Type'} (x : A) (f : A -> B) (g : A -> B) (s : A -> Prop) (h1 : term24 A B) (h2 : term23 A B f g x) (h3 : term16 A B f s) (h4 : term16 A B g s) : term96 A x s.
Proof. exact (EQ_MP (@lem4385388 A x s) (@lem4385385 A B x f g s h1 h2 h3 h4)). Qed.
Lemma lem4385392 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4385394 {A : Type'} (x : A) (s : A -> Prop) : (term97 A x s) = (term204 A x s).
Proof. exact (@lem4385392 (term96 A x s)). Qed.
Lemma lem4385397 {A : Type'} (x : A) (s : A -> Prop) (h1 : term9 A x s) : term204 A x s.
Proof. exact (EQ_MP (@lem4385394 A x s) (@lem4384525 A x s h1)). Qed.
Lemma lem4385400 {A B : Type'} (x : A) (f : A -> B) (g : A -> B) (s : A -> Prop) (h1 : term24 A B) (h2 : term23 A B f g x) (h3 : term9 A x s) (h4 : term16 A B f s) (h5 : term16 A B g s) : False.
Proof. exact (@lem4385397 A x s h3 (@lem4385389 A B x f g s h1 h2 h4 h5)). Qed.
Lemma lem4385401 {A B : Type'} (x : A) (f : A -> B) (g : A -> B) (s : A -> Prop) (h1 : term24 A B) (h2 : term23 A B f g x) (h3 : term9 A x s) (h4 : term16 A B f s) (h5 : term16 A B g s) : term205.
Proof. exact (fun h0 : ~ False => @lem4385400 A B x f g s h1 h2 h3 h4 h5). Qed.
Lemma lem4385403 (p : Prop) : (term118 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4385404 : term205 = False.
Proof. exact (@lem4385403 False). Qed.
Lemma lem4385405 {A B : Type'} (x : A) (f : A -> B) (g : A -> B) (s : A -> Prop) (h1 : term24 A B) (h2 : term23 A B f g x) (h3 : term9 A x s) (h4 : term16 A B f s) (h5 : term16 A B g s) : False.
Proof. exact (EQ_MP (@lem4385404) (@lem4385401 A B x f g s h1 h2 h3 h4 h5)). Qed.
Lemma lem4385406 {A B : Type'} (x : A) (f : A -> B) (g : A -> B) (s : A -> Prop) (h1 : term24 A B) (h2 : term23 A B f g x) (h3 : term9 A x s) (h4 : term16 A B f s) (h5 : term16 A B g s) : (term23 A B f g x) = False.
Proof. exact (prop_ext (fun h6 : term23 A B f g x => @lem4385405 A B x f g s h1 h2 h3 h4 h5) (fun h6 : False => @lem4383968 A B f g x h2)). Qed.
Lemma lem4385407 {A B : Type'} (x : A) (f : A -> B) (g : A -> B) (s : A -> Prop) (h1 : term24 A B) (h2 : term23 A B f g x) (h3 : term9 A x s) (h4 : term16 A B f s) (h5 : term16 A B g s) : False.
Proof. exact (EQ_MP (@lem4385406 A B x f g s h1 h2 h3 h4 h5) (@lem4383968 A B f g x h2)). Qed.
Lemma lem4385408 {A B : Type'} (x : A) (f : A -> B) (g : A -> B) (s : A -> Prop) (h1 : term24 A B) (h2 : term23 A B f g x) (h3 : term9 A x s) (h4 : term16 A B f s) (h5 : term16 A B g s) : (term9 A x s) = False.
Proof. exact (prop_ext (fun h6 : term9 A x s => @lem4385407 A B x f g s h1 h2 h3 h4 h5) (fun h6 : False => @lem4383962 A x s h3)). Qed.
Lemma lem4385409 {A B : Type'} (x : A) (f : A -> B) (g : A -> B) (s : A -> Prop) (h1 : term24 A B) (h2 : term23 A B f g x) (h3 : term9 A x s) (h4 : term16 A B f s) (h5 : term16 A B g s) : False.
Proof. exact (EQ_MP (@lem4385408 A B x f g s h1 h2 h3 h4 h5) (@lem4383962 A x s h3)). Qed.
Lemma lem4385410 {A B : Type'} (x : A) (f : A -> B) (g : A -> B) (s : A -> Prop) (h1 : term24 A B) (h2 : term23 A B f g x) (h3 : term9 A x s) (h4 : term16 A B f s) (h5 : term16 A B g s) : (term16 A B g s) = False.
Proof. exact (prop_ext (fun h6 : term16 A B g s => @lem4385409 A B x f g s h1 h2 h3 h4 h5) (fun h6 : False => @lem4383893 A B g s h5)). Qed.
Lemma lem4385411 {A B : Type'} (x : A) (f : A -> B) (g : A -> B) (s : A -> Prop) (h1 : term24 A B) (h2 : term23 A B f g x) (h3 : term9 A x s) (h4 : term16 A B f s) (h5 : term16 A B g s) : False.
Proof. exact (EQ_MP (@lem4385410 A B x f g s h1 h2 h3 h4 h5) (@lem4383893 A B g s h5)). Qed.
Lemma lem4385412 {A B : Type'} (x : A) (f : A -> B) (g : A -> B) (s : A -> Prop) (h1 : term24 A B) (h2 : term23 A B f g x) (h3 : term9 A x s) (h4 : term16 A B f s) (h5 : term16 A B g s) : (term16 A B f s) = False.
Proof. exact (prop_ext (fun h6 : term16 A B f s => @lem4385411 A B x f g s h1 h2 h3 h4 h5) (fun h6 : False => @lem4383887 A B f s h4)). Qed.
Lemma lem4385413 {A B : Type'} (x : A) (f : A -> B) (g : A -> B) (s : A -> Prop) (h1 : term24 A B) (h2 : term23 A B f g x) (h3 : term9 A x s) (h4 : term16 A B f s) (h5 : term16 A B g s) : False.
Proof. exact (EQ_MP (@lem4385412 A B x f g s h1 h2 h3 h4 h5) (@lem4383887 A B f s h4)). Qed.
Lemma lem4385414 {A B : Type'} (x : A) (f : A -> B) (g : A -> B) (s : A -> Prop) (h1 : term24 A B) (h2 : term23 A B f g x) (h3 : term9 A x s) (h4 : term16 A B f s) (h5 : term16 A B g s) : term30 A B.
Proof. exact (fun h0 : term25 A B => @lem4385413 A B x f g s h1 h2 h3 h4 h5). Qed.
Lemma lem4385415 {A B : Type'} : (term30 A B) = (term31 A B).
Proof. exact (@lem69 (term25 A B)). Qed.
Lemma lem4385416 {A B : Type'} (x : A) (f : A -> B) (g : A -> B) (s : A -> Prop) (h1 : term24 A B) (h2 : term23 A B f g x) (h3 : term9 A x s) (h4 : term16 A B f s) (h5 : term16 A B g s) : term31 A B.
Proof. exact (EQ_MP (@lem4385415 A B) (@lem4385414 A B x f g s h1 h2 h3 h4 h5)). Qed.
Lemma lem4385417 {A B : Type'} (x : A) (f : A -> B) (g : A -> B) (s : A -> Prop) (h1 : term23 A B f g x) (h2 : term9 A x s) (h3 : term16 A B f s) (h4 : term16 A B g s) : term34 A B.
Proof. exact (fun h0 : term24 A B => @lem4385416 A B x f g s h0 h1 h2 h3 h4). Qed.
Lemma lem4385418 {A B : Type'} (x : A) (f : A -> B) (g : A -> B) (s : A -> Prop) (h1 : term9 A x s) (h2 : term16 A B f s) (h3 : term16 A B g s) : term37 A B f g x.
Proof. exact (fun h0 : term23 A B f g x => @lem4385417 A B x f g s h0 h1 h2 h3). Qed.
Lemma lem4385419 {A B : Type'} (x : A) (f : A -> B) (g : A -> B) (s : A -> Prop) (h1 : term16 A B f s) (h2 : term16 A B g s) : term40 A B s f g x.
Proof. exact (fun h0 : term9 A x s => @lem4385418 A B x f g s h0 h1 h2). Qed.
Lemma lem4385420 {A B : Type'} (x : A) (f : A -> B) (g : A -> B) (s : A -> Prop) (h1 : term16 A B f s) (h2 : term16 A B g s) : term43 A B s f g x.
Proof. exact (fun h0 : term17 A B s f g => @lem4385419 A B x f g s h1 h2). Qed.
Lemma lem4385421 {A B : Type'} (g : A -> B) (x : A) (f : A -> B) (s : A -> Prop) (h1 : term16 A B f s) : term46 A B s f g x.
Proof. exact (fun h0 : term16 A B g s => @lem4385420 A B x f g s h1 h0). Qed.
Lemma lem4385422 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : term47 A B s f g x.
Proof. exact (fun h0 : term16 A B f s => @lem4385421 A B g x f s h0). Qed.
Lemma lem4385427 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) : term51 A B f g x.
Proof. exact (fun s : A -> Prop => @lem4385422 A B s f g x). Qed.
Lemma lem4385432 {A B : Type'} (g : A -> B) (x : A) : term55 A B g x.
Proof. exact (fun f : A -> B => @lem4385427 A B f g x). Qed.
Lemma lem4385437 {A B : Type'} (x : A) : term59 A B x.
Proof. exact (fun g : A -> B => @lem4385432 A B g x). Qed.
Lemma lem4385442 {A B : Type'} : term63 A B.
Proof. exact (fun x : A => @lem4385437 A B x). Qed.
Lemma lem4385443 {A B : Type'} : term62 A B.
Proof. exact (EQ_MP (@lem4383874 A B) (@lem4385442 A B)). Qed.
Lemma lem4385444 {A B : Type'} (x : A) : term206 A B x.
Proof. exact (@lem4385443 A B x). Qed.
Lemma lem4385445 {A B : Type'} (x : A) : (term206 A B x) = (term58 A B x).
Proof. exact (eq_refl (term206 A B x)). Qed.
Lemma lem4385446 {A B : Type'} (x : A) : term58 A B x.
Proof. exact (EQ_MP (@lem4385445 A B x) (@lem4385444 A B x)). Qed.
Lemma lem4385447 {A B : Type'} (x : A) (g : A -> B) : term207 A B x g.
Proof. exact (@lem4385446 A B x g). Qed.
Lemma lem4385448 {A B : Type'} (g : A -> B) (x : A) : (term207 A B x g) = (term54 A B g x).
Proof. exact (eq_refl (term207 A B x g)). Qed.
Lemma lem4385449 {A B : Type'} (g : A -> B) (x : A) : term54 A B g x.
Proof. exact (EQ_MP (@lem4385448 A B g x) (@lem4385447 A B x g)). Qed.
Lemma lem4385450 {A B : Type'} (g : A -> B) (x : A) (f : A -> B) : term208 A B g x f.
Proof. exact (@lem4385449 A B g x f). Qed.
Lemma lem4385451 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) : (term208 A B g x f) = (term50 A B f g x).
Proof. exact (eq_refl (term208 A B g x f)). Qed.
Lemma lem4385452 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) : term50 A B f g x.
Proof. exact (EQ_MP (@lem4385451 A B f g x) (@lem4385450 A B g x f)). Qed.
Lemma lem4385453 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) (s : A -> Prop) : term209 A B f g x s.
Proof. exact (@lem4385452 A B f g x s). Qed.
Lemma lem4385454 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term209 A B f g x s) = (term26 A B s f g x).
Proof. exact (eq_refl (term209 A B f g x s)). Qed.
Lemma lem4385455 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : term26 A B s f g x.
Proof. exact (EQ_MP (@lem4385454 A B s f g x) (@lem4385453 A B f g x s)). Qed.
Lemma lem4385457 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : term26 A B s f g x.
Proof. exact (@lem4383569 A B s f g x (@lem4385455 A B s f g x)). Qed.
Lemma lem4385458 {A B : Type'} (g : A -> B) (x : A) (f : A -> B) (s : A -> Prop) (h1 : term16 A B f s) : term45 A B s f g x.
Proof. exact (@lem4385457 A B s f g x (@lem4383490 A B f s h1)). Qed.
Lemma lem4385459 {A B : Type'} (x : A) (f : A -> B) (g : A -> B) (s : A -> Prop) (h1 : term16 A B f s) (h2 : term16 A B g s) : term42 A B s f g x.
Proof. exact (@lem4385458 A B g x f s h1 (@lem4383492 A B g s h2)). Qed.
Lemma lem4385460 {A B : Type'} (x : A) (f : A -> B) (g : A -> B) (s : A -> Prop) (h1 : term17 A B s f g) (h2 : term16 A B f s) (h3 : term16 A B g s) : term39 A B s f g x.
Proof. exact (@lem4385459 A B x f g s h2 h3 (@lem4383491 A B s f g h1)). Qed.
Lemma lem4385461 {A B : Type'} (x : A) (f : A -> B) (g : A -> B) (s : A -> Prop) (h1 : term17 A B s f g) (h2 : term9 A x s) (h3 : term16 A B f s) (h4 : term16 A B g s) : term36 A B f g x.
Proof. exact (@lem4385460 A B x f g s h1 h3 h4 (@lem4383481 A x s h2)). Qed.
Lemma lem4385462 {A B : Type'} (x : A) (f : A -> B) (g : A -> B) (s : A -> Prop) (h1 : term17 A B s f g) (h2 : term23 A B f g x) (h3 : term9 A x s) (h4 : term16 A B f s) (h5 : term16 A B g s) : term33 A B.
Proof. exact (@lem4385461 A B x f g s h1 h3 h4 h5 (@lem4383548 A B f g x h2)). Qed.
Lemma lem4385463 {A B : Type'} (x : A) (f : A -> B) (g : A -> B) (s : A -> Prop) (h1 : term17 A B s f g) (h2 : term23 A B f g x) (h3 : term9 A x s) (h4 : term16 A B f s) (h5 : term16 A B g s) : term30 A B.
Proof. exact (@lem4385462 A B x f g s h1 h2 h3 h4 h5 (@lem4383549 A B)). Qed.
Lemma lem4385464 {A B : Type'} (x : A) (f : A -> B) (g : A -> B) (s : A -> Prop) (h1 : term17 A B s f g) (h2 : term23 A B f g x) (h3 : term9 A x s) (h4 : term16 A B f s) (h5 : term16 A B g s) : False.
Proof. exact (@lem4385463 A B x f g s h1 h2 h3 h4 h5 (@lem4383551 A B)). Qed.
Lemma lem4385465 {A B : Type'} (x : A) (f : A -> B) (g : A -> B) (s : A -> Prop) (h1 : term17 A B s f g) (h2 : term23 A B f g x) (h3 : term9 A x s) (h4 : term16 A B f s) (h5 : term16 A B g s) : (term23 A B f g x) = False.
Proof. exact (prop_ext (fun h6 : term23 A B f g x => @lem4385464 A B x f g s h1 h2 h3 h4 h5) (fun h6 : False => @lem4383548 A B f g x h2)). Qed.
Lemma lem4385466 {A B : Type'} (x : A) (f : A -> B) (g : A -> B) (s : A -> Prop) (h1 : term17 A B s f g) (h2 : term23 A B f g x) (h3 : term9 A x s) (h4 : term16 A B f s) (h5 : term16 A B g s) : False.
Proof. exact (EQ_MP (@lem4385465 A B x f g s h1 h2 h3 h4 h5) (@lem4383548 A B f g x h2)). Qed.
Lemma lem4385467 {A B : Type'} (x : A) (f : A -> B) (g : A -> B) (s : A -> Prop) (h1 : term17 A B s f g) (h2 : term9 A x s) (h3 : term16 A B f s) (h4 : term16 A B g s) : term22 A B f g x.
Proof. exact (fun h0 : term23 A B f g x => @lem4385466 A B x f g s h1 h0 h2 h3 h4). Qed.
Lemma lem4385468 {A B : Type'} (x : A) (f : A -> B) (g : A -> B) (s : A -> Prop) (h1 : term17 A B s f g) (h2 : term9 A x s) (h3 : term16 A B f s) (h4 : term16 A B g s) : (f x) = (g x).
Proof. exact (EQ_MP (@lem4383547 A B f g x) (@lem4385467 A B x f g s h1 h2 h3 h4)). Qed.
Lemma lem4385469 {A B : Type'} (x : A) (f : A -> B) (g : A -> B) (s : A -> Prop) (h1 : term17 A B s f g) (h2 : term16 A B f s) (h3 : term16 A B g s) : (f x) = (g x).
Proof. exact (or_elim (@lem4383479 A x s) (fun h0 : @IN A x s => @lem4383543 A B f g x s h1 h0) (fun h0 : term9 A x s => @lem4385468 A B x f g s h1 h0 h2 h3)). Qed.
Lemma lem4385474 {A B : Type'} (f : A -> B) (g : A -> B) (s : A -> Prop) (h1 : term17 A B s f g) (h2 : term16 A B f s) (h3 : term16 A B g s) : term13 A B f g.
Proof. exact (fun x : A => @lem4385469 A B x f g s h1 h2 h3). Qed.
Lemma lem4385475 {A B : Type'} (f : A -> B) (g : A -> B) (s : A -> Prop) (h1 : term17 A B s f g) (h2 : term16 A B f s) (h3 : term16 A B g s) : f = g.
Proof. exact (EQ_MP (@lem4383506 A B f g) (@lem4385474 A B f g s h1 h2 h3)). Qed.
Lemma lem4385476 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term14 A B s f g) : term15 A B s f g.
Proof. exact (proj2 (@lem4383488 A B s f g h1)). Qed.
Lemma lem4385477 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term14 A B s f g) : term16 A B f s.
Proof. exact (proj1 (@lem4383488 A B s f g h1)). Qed.
Lemma lem4385478 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term15 A B s f g) : term17 A B s f g.
Proof. exact (proj2 (@lem4383489 A B s f g h1)). Qed.
Lemma lem4385479 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term15 A B s f g) : term16 A B g s.
Proof. exact (proj1 (@lem4383489 A B s f g h1)). Qed.
Lemma lem4385480 {A B : Type'} (f : A -> B) (g : A -> B) (s : A -> Prop) (h1 : term17 A B s f g) (h2 : term16 A B f s) (h3 : term16 A B g s) : (term17 A B s f g) = (f = g).
Proof. exact (prop_ext (fun h4 : term17 A B s f g => @lem4385475 A B f g s h1 h2 h3) (fun h4 : f = g => @lem4383491 A B s f g h1)). Qed.
Lemma lem4385481 {A B : Type'} (f : A -> B) (g : A -> B) (s : A -> Prop) (h1 : term17 A B s f g) (h2 : term16 A B f s) (h3 : term16 A B g s) : f = g.
Proof. exact (EQ_MP (@lem4385480 A B f g s h1 h2 h3) (@lem4383491 A B s f g h1)). Qed.
Lemma lem4385482 {A B : Type'} (f : A -> B) (g : A -> B) (s : A -> Prop) (h1 : term17 A B s f g) (h2 : term16 A B f s) (h3 : term16 A B g s) : (term16 A B g s) = (f = g).
Proof. exact (prop_ext (fun h4 : term16 A B g s => @lem4385481 A B f g s h1 h2 h3) (fun h4 : f = g => @lem4383492 A B g s h3)). Qed.
Lemma lem4385483 {A B : Type'} (f : A -> B) (g : A -> B) (s : A -> Prop) (h1 : term17 A B s f g) (h2 : term16 A B f s) (h3 : term16 A B g s) : f = g.
Proof. exact (EQ_MP (@lem4385482 A B f g s h1 h2 h3) (@lem4383492 A B g s h3)). Qed.
Lemma lem4385484 {A B : Type'} (f : A -> B) (g : A -> B) (s : A -> Prop) (h1 : term15 A B s f g) (h2 : term16 A B f s) (h3 : term16 A B g s) : (term17 A B s f g) = (f = g).
Proof. exact (prop_ext (fun h4 : term17 A B s f g => @lem4385483 A B f g s h4 h2 h3) (fun h4 : f = g => @lem4385478 A B s f g h1)). Qed.
Lemma lem4385485 {A B : Type'} (f : A -> B) (g : A -> B) (s : A -> Prop) (h1 : term15 A B s f g) (h2 : term16 A B f s) (h3 : term16 A B g s) : f = g.
Proof. exact (EQ_MP (@lem4385484 A B f g s h1 h2 h3) (@lem4385478 A B s f g h1)). Qed.
Lemma lem4385486 {A B : Type'} (g : A -> B) (f : A -> B) (s : A -> Prop) (h1 : term15 A B s f g) (h2 : term16 A B f s) : (term16 A B g s) = (f = g).
Proof. exact (prop_ext (fun h3 : term16 A B g s => @lem4385485 A B f g s h1 h2 h3) (fun h3 : f = g => @lem4385479 A B s f g h1)). Qed.
Lemma lem4385487 {A B : Type'} (g : A -> B) (f : A -> B) (s : A -> Prop) (h1 : term15 A B s f g) (h2 : term16 A B f s) : f = g.
Proof. exact (EQ_MP (@lem4385486 A B g f s h1 h2) (@lem4385479 A B s f g h1)). Qed.
Lemma lem4385488 {A B : Type'} (g : A -> B) (f : A -> B) (s : A -> Prop) (h1 : term15 A B s f g) (h2 : term16 A B f s) : (term16 A B f s) = (f = g).
Proof. exact (prop_ext (fun h3 : term16 A B f s => @lem4385487 A B g f s h1 h2) (fun h3 : f = g => @lem4383490 A B f s h2)). Qed.
Lemma lem4385489 {A B : Type'} (g : A -> B) (f : A -> B) (s : A -> Prop) (h1 : term15 A B s f g) (h2 : term16 A B f s) : f = g.
Proof. exact (EQ_MP (@lem4385488 A B g f s h1 h2) (@lem4383490 A B f s h2)). Qed.
Lemma lem4385490 {A B : Type'} (g : A -> B) (f : A -> B) (s : A -> Prop) (h1 : term14 A B s f g) (h2 : term16 A B f s) : (term15 A B s f g) = (f = g).
Proof. exact (prop_ext (fun h3 : term15 A B s f g => @lem4385489 A B g f s h3 h2) (fun h3 : f = g => @lem4385476 A B s f g h1)). Qed.
Lemma lem4385491 {A B : Type'} (g : A -> B) (f : A -> B) (s : A -> Prop) (h1 : term14 A B s f g) (h2 : term16 A B f s) : f = g.
Proof. exact (EQ_MP (@lem4385490 A B g f s h1 h2) (@lem4385476 A B s f g h1)). Qed.
Lemma lem4385492 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term14 A B s f g) : (term16 A B f s) = (f = g).
Proof. exact (prop_ext (fun h2 : term16 A B f s => @lem4385491 A B g f s h1 h2) (fun h2 : f = g => @lem4385477 A B s f g h1)). Qed.
Lemma lem4385493 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term14 A B s f g) : f = g.
Proof. exact (EQ_MP (@lem4385492 A B s f g h1) (@lem4385477 A B s f g h1)). Qed.
Lemma lem4385494 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : term210 A B s f g.
Proof. exact (fun h0 : term14 A B s f g => @lem4385493 A B s f g h0). Qed.
Lemma lem4385499 {A B : Type'} (s : A -> Prop) (f : A -> B) : term211 A B s f.
Proof. exact (fun g : A -> B => @lem4385494 A B s f g). Qed.
Lemma lem4385504 {A B : Type'} (s : A -> Prop) : term212 A B s.
Proof. exact (fun f : A -> B => @lem4385499 A B s f). Qed.
Lemma lem4385509 {A B : Type'} : term213 A B.
Proof. exact (fun s : A -> Prop => @lem4385504 A B s). Qed.
