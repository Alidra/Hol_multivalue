Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_ADD_GEN_term_abbrevs.
Require Import ITERATE_OP_GEN_spec.
Require Import MONOIDAL_ADD_spec.
Require Import NEUTRAL_ADD_spec.
Require Import support_spec.
Require Import thm6920357_spec.
Require Import thm6920371_spec.
Lemma lem6930478 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (h1). Qed.
Lemma lem6930479 {A B : Type'} (op : type1400 B) (h1 : term0 A B) : term1 A B op.
Proof. exact (@lem6930478 A B h1 op). Qed.
Lemma lem6930480 {A B : Type'} (op : type1400 B) : (term1 A B op) = (term2 A B op).
Proof. exact (eq_refl (term1 A B op)). Qed.
Lemma lem6930481 {A B : Type'} (op : type1400 B) (h1 : term0 A B) : term2 A B op.
Proof. exact (EQ_MP (@lem6930480 A B op) (@lem6930479 A B op h1)). Qed.
Lemma lem6930482 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : @monoidal B op.
Proof. exact (h1). Qed.
Lemma lem6930483 {A B : Type'} (op : type1400 B) (h1 : term0 A B) (h2 : @monoidal B op) : term3 A B op.
Proof. exact (@lem6930481 A B op h1 (@lem6930482 B op h2)). Qed.
Lemma lem6930484 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term4 A B op.
Proof. exact (fun h0 : term0 A B => @lem6930483 A B op h0 h1). Qed.
Lemma lem6930485 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (h1). Qed.
Lemma lem6930486 {A B : Type'} (op : type1400 B) (h1 : term0 A B) (h2 : @monoidal B op) : term3 A B op.
Proof. exact (@lem6930484 A B op h2 (@lem6930485 A B h1)). Qed.
Lemma lem6930487 {A B : Type'} (op : type1400 B) (h1 : term0 A B) : term2 A B op.
Proof. exact (fun h0 : @monoidal B op => @lem6930486 A B op h1 h0). Qed.
Lemma lem6930488 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (fun op : type1400 B => @lem6930487 A B op h1). Qed.
Lemma lem6930489 {A B : Type'} : term5 A B.
Proof. exact (fun h0 : term0 A B => @lem6930488 A B h0). Qed.
Lemma lem6930490 {A B : Type'} : term0 A B.
Proof. exact (@lem6930489 A B (@lem6184258 A B)). Qed.
Lemma lem6930491 {A B : Type'} (op : type1400 B) : term1 A B op.
Proof. exact (@lem6930490 A B op). Qed.
Lemma lem6930492 {A B : Type'} (op : type1400 B) : (term1 A B op) = (term2 A B op).
Proof. exact (eq_refl (term1 A B op)). Qed.
Lemma lem6930497 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : (@support A B op f s) = (term6 A B s f op)) : (@support A B op f s) = (term6 A B s f op).
Proof. exact (h1). Qed.
Lemma lem6930498 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : (@support A B op f s) = (term6 A B s f op)) : (term6 A B s f op) = (@support A B op f s).
Proof. exact (SYM (@lem6930497 A B s f op h1)). Qed.
Lemma lem6930499 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : (term6 A B s f op) = (@support A B op f s)) : (term6 A B s f op) = (@support A B op f s).
Proof. exact (h1). Qed.
Lemma lem6930500 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : (term6 A B s f op) = (@support A B op f s)) : (@support A B op f s) = (term6 A B s f op).
Proof. exact (SYM (@lem6930499 A B op f s h1)). Qed.
Lemma lem6930501 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : ((@support A B op f s) = (term6 A B s f op)) = ((term6 A B s f op) = (@support A B op f s)).
Proof. exact (prop_ext (fun h1 : (@support A B op f s) = (term6 A B s f op) => @lem6930498 A B s f op h1) (fun h1 : (term6 A B s f op) = (@support A B op f s) => @lem6930500 A B op f s h1)). Qed.
Lemma lem6930502 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term7 A B s f) = (term8 A B f s).
Proof. exact (fun_ext (fun op : type1400 B => @lem6930501 A B op f s)). Qed.
Lemma lem6930503 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem6930504 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term9 A B s f) = (term10 A B f s).
Proof. exact (MK_COMB (@lem6930503 B) (@lem6930502 A B f s)). Qed.
Lemma lem6930505 {A B : Type'} (s : A -> Prop) : (term11 A B s) = (term12 A B s).
Proof. exact (fun_ext (fun f : A -> B => @lem6930504 A B f s)). Qed.
Lemma lem6930506 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem6930507 {A B : Type'} (s : A -> Prop) : (term13 A B s) = (term14 A B s).
Proof. exact (MK_COMB (@lem6930506 A B) (@lem6930505 A B s)). Qed.
Lemma lem6930508 {A B : Type'} : (term15 A B) = (term16 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6930507 A B s)). Qed.
Lemma lem6930509 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6930510 {A B : Type'} : (term17 A B) = (term18 A B).
Proof. exact (MK_COMB (@lem6930509 A) (@lem6930508 A B)). Qed.
Lemma lem6930511 {A B : Type'} : term18 A B.
Proof. exact (EQ_MP (@lem6930510 A B) (@lem5716761 A B)). Qed.
Lemma lem6930512 (h1 : (@neutral nat Nat.add) = (NUMERAL 0)) : (@neutral nat Nat.add) = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem6930513 (h1 : (@neutral nat Nat.add) = (NUMERAL 0)) : (NUMERAL 0) = (@neutral nat Nat.add).
Proof. exact (SYM (@lem6930512 h1)). Qed.
Lemma lem6930514 (h1 : (NUMERAL 0) = (@neutral nat Nat.add)) : (NUMERAL 0) = (@neutral nat Nat.add).
Proof. exact (h1). Qed.
Lemma lem6930515 (h1 : (NUMERAL 0) = (@neutral nat Nat.add)) : (@neutral nat Nat.add) = (NUMERAL 0).
Proof. exact (SYM (@lem6930514 h1)). Qed.
Lemma lem6930516 : ((@neutral nat Nat.add) = (NUMERAL 0)) = ((NUMERAL 0) = (@neutral nat Nat.add)).
Proof. exact (prop_ext (fun h1 : (@neutral nat Nat.add) = (NUMERAL 0) => @lem6930513 h1) (fun h1 : (NUMERAL 0) = (@neutral nat Nat.add) => @lem6930515 h1)). Qed.
Lemma lem6930518 {A B : Type'} (s : A -> Prop) : term19 A B s.
Proof. exact (@lem6930511 A B s). Qed.
Lemma lem6930519 {A B : Type'} (s : A -> Prop) : (term19 A B s) = (term14 A B s).
Proof. exact (eq_refl (term19 A B s)). Qed.
Lemma lem6930520 {A B : Type'} (s : A -> Prop) : term14 A B s.
Proof. exact (EQ_MP (@lem6930519 A B s) (@lem6930518 A B s)). Qed.
Lemma lem6930521 {A B : Type'} (s : A -> Prop) (f : A -> B) : term20 A B s f.
Proof. exact (@lem6930520 A B s f). Qed.
Lemma lem6930522 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term20 A B s f) = (term10 A B f s).
Proof. exact (eq_refl (term20 A B s f)). Qed.
Lemma lem6930523 {A B : Type'} (f : A -> B) (s : A -> Prop) : term10 A B f s.
Proof. exact (EQ_MP (@lem6930522 A B f s) (@lem6930521 A B s f)). Qed.
Lemma lem6930524 {A B : Type'} (f : A -> B) (s : A -> Prop) (op : type1400 B) : term21 A B f s op.
Proof. exact (@lem6930523 A B f s op). Qed.
Lemma lem6930525 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term21 A B f s op) = ((term6 A B s f op) = (@support A B op f s)).
Proof. exact (eq_refl (term21 A B f s op)). Qed.
Lemma lem6930552 : (NUMERAL 0) = (@neutral nat Nat.add).
Proof. exact (EQ_MP (@lem6930516) (@lem6921993)). Qed.
Lemma lem6930553 {_126816 : Type'} (f : _126816 -> nat) (x : _126816) : (term22 _126816 f x) = (term22 _126816 f x).
Proof. exact (eq_refl (term22 _126816 f x)). Qed.
Lemma lem6930554 {_126816 : Type'} (f : _126816 -> nat) (x : _126816) : ((f x) = (NUMERAL 0)) = ((f x) = (@neutral nat Nat.add)).
Proof. exact (MK_COMB (@lem6930553 _126816 f x) (@lem6930552)). Qed.
Lemma lem6930557 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6930558 {_126816 : Type'} (f : _126816 -> nat) (x : _126816) : (term23 _126816 f x) = (term24 _126816 f x).
Proof. exact (MK_COMB (@lem6930557) (@lem6930554 _126816 f x)). Qed.
Lemma lem6930559 {_126816 : Type'} (x : _126816) (s : _126816 -> Prop) : (term25 _126816 x s) = (term25 _126816 x s).
Proof. exact (eq_refl (term25 _126816 x s)). Qed.
Lemma lem6930560 {_126816 : Type'} (s : _126816 -> Prop) (f : _126816 -> nat) (x : _126816) : (term26 _126816 s f x) = (term27 _126816 s f x).
Proof. exact (MK_COMB (@lem6930559 _126816 x s) (@lem6930558 _126816 f x)). Qed.
Lemma lem6930563 {_126816 : Type'} (GEN_PVAR_285 : _126816) : (@SETSPEC _126816 GEN_PVAR_285) = (@SETSPEC _126816 GEN_PVAR_285).
Proof. exact (eq_refl (@SETSPEC _126816 GEN_PVAR_285)). Qed.
Lemma lem6930564 {_126816 : Type'} (GEN_PVAR_285 : _126816) (s : _126816 -> Prop) (f : _126816 -> nat) (x : _126816) : (term28 _126816 GEN_PVAR_285 s f x) = (term29 _126816 GEN_PVAR_285 s f x).
Proof. exact (MK_COMB (@lem6930563 _126816 GEN_PVAR_285) (@lem6930560 _126816 s f x)). Qed.
Lemma lem6930565 {_126816 : Type'} (x : _126816) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6930566 {_126816 : Type'} (GEN_PVAR_285 : _126816) (s : _126816 -> Prop) (f : _126816 -> nat) (x : _126816) : (term30 _126816 GEN_PVAR_285 s f x) = (term31 _126816 GEN_PVAR_285 s f x).
Proof. exact (MK_COMB (@lem6930564 _126816 GEN_PVAR_285 s f x) (@lem6930565 _126816 x)). Qed.
Lemma lem6930567 {_126816 : Type'} (GEN_PVAR_285 : _126816) (s : _126816 -> Prop) (f : _126816 -> nat) : (term32 _126816 GEN_PVAR_285 s f) = (term33 _126816 GEN_PVAR_285 s f).
Proof. exact (fun_ext (fun x : _126816 => @lem6930566 _126816 GEN_PVAR_285 s f x)). Qed.
Lemma lem6930568 {_126816 : Type'} : (@ex _126816) = (@ex _126816).
Proof. exact (eq_refl (@ex _126816)). Qed.
Lemma lem6930569 {_126816 : Type'} (GEN_PVAR_285 : _126816) (s : _126816 -> Prop) (f : _126816 -> nat) : (term34 _126816 GEN_PVAR_285 s f) = (term35 _126816 GEN_PVAR_285 s f).
Proof. exact (MK_COMB (@lem6930568 _126816) (@lem6930567 _126816 GEN_PVAR_285 s f)). Qed.
Lemma lem6930574 {_126816 : Type'} (s : _126816 -> Prop) (f : _126816 -> nat) : (term36 _126816 s f) = (term37 _126816 s f).
Proof. exact (fun_ext (fun GEN_PVAR_285 : _126816 => @lem6930569 _126816 GEN_PVAR_285 s f)). Qed.
Lemma lem6930575 {_126816 : Type'} : (@GSPEC _126816) = (@GSPEC _126816).
Proof. exact (eq_refl (@GSPEC _126816)). Qed.
Lemma lem6930576 {_126816 : Type'} (s : _126816 -> Prop) (f : _126816 -> nat) : (term38 _126816 s f) = (term39 _126816 s f).
Proof. exact (MK_COMB (@lem6930575 _126816) (@lem6930574 _126816 s f)). Qed.
Lemma lem6930578 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term6 A B s f op) = (@support A B op f s).
Proof. exact (EQ_MP (@lem6930525 A B op f s) (@lem6930524 A B f s op)). Qed.
Lemma lem6930579 {_126816 : Type'} (op : type1606) (f : _126816 -> nat) (s : _126816 -> Prop) : (term40 _126816 s f op) = (@support _126816 nat op f s).
Proof. exact (@lem6930578 _126816 nat op f s). Qed.
Lemma lem6930580 {_126816 : Type'} (f : _126816 -> nat) (s : _126816 -> Prop) : (term39 _126816 s f) = (@support _126816 nat Nat.add f s).
Proof. exact (@lem6930579 _126816 Nat.add f s). Qed.
Lemma lem6930581 {_126816 : Type'} (f : _126816 -> nat) (s : _126816 -> Prop) : (term38 _126816 s f) = (@support _126816 nat Nat.add f s).
Proof. exact (TRANS (@lem6930576 _126816 s f) (@lem6930580 _126816 f s)). Qed.
Lemma lem6930582 {_126816 : Type'} : (@FINITE _126816) = (@FINITE _126816).
Proof. exact (eq_refl (@FINITE _126816)). Qed.
Lemma lem6930583 {_126816 : Type'} (f : _126816 -> nat) (s : _126816 -> Prop) : (term41 _126816 s f) = (term42 _126816 f s).
Proof. exact (MK_COMB (@lem6930582 _126816) (@lem6930581 _126816 f s)). Qed.
Lemma lem6930584 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6930585 {_126816 : Type'} (f : _126816 -> nat) (s : _126816 -> Prop) : (term43 _126816 s f) = (term44 _126816 f s).
Proof. exact (MK_COMB (@lem6930584) (@lem6930583 _126816 f s)). Qed.
Lemma lem6930595 : (NUMERAL 0) = (@neutral nat Nat.add).
Proof. exact (EQ_MP (@lem6930516) (@lem6921993)). Qed.
Lemma lem6930596 {_126816 : Type'} (g : _126816 -> nat) (x : _126816) : (term22 _126816 g x) = (term22 _126816 g x).
Proof. exact (eq_refl (term22 _126816 g x)). Qed.
Lemma lem6930597 {_126816 : Type'} (g : _126816 -> nat) (x : _126816) : ((g x) = (NUMERAL 0)) = ((g x) = (@neutral nat Nat.add)).
Proof. exact (MK_COMB (@lem6930596 _126816 g x) (@lem6930595)). Qed.
Lemma lem6930600 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6930601 {_126816 : Type'} (g : _126816 -> nat) (x : _126816) : (term23 _126816 g x) = (term24 _126816 g x).
Proof. exact (MK_COMB (@lem6930600) (@lem6930597 _126816 g x)). Qed.
Lemma lem6930602 {_126816 : Type'} (x : _126816) (s : _126816 -> Prop) : (term25 _126816 x s) = (term25 _126816 x s).
Proof. exact (eq_refl (term25 _126816 x s)). Qed.
Lemma lem6930603 {_126816 : Type'} (s : _126816 -> Prop) (g : _126816 -> nat) (x : _126816) : (term26 _126816 s g x) = (term27 _126816 s g x).
Proof. exact (MK_COMB (@lem6930602 _126816 x s) (@lem6930601 _126816 g x)). Qed.
Lemma lem6930606 {_126816 : Type'} (GEN_PVAR_286 : _126816) : (@SETSPEC _126816 GEN_PVAR_286) = (@SETSPEC _126816 GEN_PVAR_286).
Proof. exact (eq_refl (@SETSPEC _126816 GEN_PVAR_286)). Qed.
Lemma lem6930607 {_126816 : Type'} (GEN_PVAR_286 : _126816) (s : _126816 -> Prop) (g : _126816 -> nat) (x : _126816) : (term28 _126816 GEN_PVAR_286 s g x) = (term29 _126816 GEN_PVAR_286 s g x).
Proof. exact (MK_COMB (@lem6930606 _126816 GEN_PVAR_286) (@lem6930603 _126816 s g x)). Qed.
Lemma lem6930608 {_126816 : Type'} (x : _126816) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6930609 {_126816 : Type'} (GEN_PVAR_286 : _126816) (s : _126816 -> Prop) (g : _126816 -> nat) (x : _126816) : (term30 _126816 GEN_PVAR_286 s g x) = (term31 _126816 GEN_PVAR_286 s g x).
Proof. exact (MK_COMB (@lem6930607 _126816 GEN_PVAR_286 s g x) (@lem6930608 _126816 x)). Qed.
Lemma lem6930610 {_126816 : Type'} (GEN_PVAR_286 : _126816) (s : _126816 -> Prop) (g : _126816 -> nat) : (term32 _126816 GEN_PVAR_286 s g) = (term33 _126816 GEN_PVAR_286 s g).
Proof. exact (fun_ext (fun x : _126816 => @lem6930609 _126816 GEN_PVAR_286 s g x)). Qed.
Lemma lem6930611 {_126816 : Type'} : (@ex _126816) = (@ex _126816).
Proof. exact (eq_refl (@ex _126816)). Qed.
Lemma lem6930612 {_126816 : Type'} (GEN_PVAR_286 : _126816) (s : _126816 -> Prop) (g : _126816 -> nat) : (term34 _126816 GEN_PVAR_286 s g) = (term35 _126816 GEN_PVAR_286 s g).
Proof. exact (MK_COMB (@lem6930611 _126816) (@lem6930610 _126816 GEN_PVAR_286 s g)). Qed.
Lemma lem6930617 {_126816 : Type'} (s : _126816 -> Prop) (g : _126816 -> nat) : (term36 _126816 s g) = (term37 _126816 s g).
Proof. exact (fun_ext (fun GEN_PVAR_286 : _126816 => @lem6930612 _126816 GEN_PVAR_286 s g)). Qed.
Lemma lem6930618 {_126816 : Type'} : (@GSPEC _126816) = (@GSPEC _126816).
Proof. exact (eq_refl (@GSPEC _126816)). Qed.
Lemma lem6930619 {_126816 : Type'} (s : _126816 -> Prop) (g : _126816 -> nat) : (term38 _126816 s g) = (term39 _126816 s g).
Proof. exact (MK_COMB (@lem6930618 _126816) (@lem6930617 _126816 s g)). Qed.
Lemma lem6930621 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term6 A B s f op) = (@support A B op f s).
Proof. exact (EQ_MP (@lem6930525 A B op f s) (@lem6930524 A B f s op)). Qed.
Lemma lem6930622 {_126816 : Type'} (op : type1606) (f : _126816 -> nat) (s : _126816 -> Prop) : (term40 _126816 s f op) = (@support _126816 nat op f s).
Proof. exact (@lem6930621 _126816 nat op f s). Qed.
Lemma lem6930623 {_126816 : Type'} (g : _126816 -> nat) (s : _126816 -> Prop) : (term39 _126816 s g) = (@support _126816 nat Nat.add g s).
Proof. exact (@lem6930622 _126816 Nat.add g s). Qed.
Lemma lem6930624 {_126816 : Type'} (g : _126816 -> nat) (s : _126816 -> Prop) : (term38 _126816 s g) = (@support _126816 nat Nat.add g s).
Proof. exact (TRANS (@lem6930619 _126816 s g) (@lem6930623 _126816 g s)). Qed.
Lemma lem6930625 {_126816 : Type'} : (@FINITE _126816) = (@FINITE _126816).
Proof. exact (eq_refl (@FINITE _126816)). Qed.
Lemma lem6930626 {_126816 : Type'} (g : _126816 -> nat) (s : _126816 -> Prop) : (term41 _126816 s g) = (term42 _126816 g s).
Proof. exact (MK_COMB (@lem6930625 _126816) (@lem6930624 _126816 g s)). Qed.
Lemma lem6930627 {_126816 : Type'} (f : _126816 -> nat) (g : _126816 -> nat) (s : _126816 -> Prop) : (term45 _126816 f s g) = (term46 _126816 f g s).
Proof. exact (MK_COMB (@lem6930585 _126816 f s) (@lem6930626 _126816 g s)). Qed.
Lemma lem6930630 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6930631 {_126816 : Type'} (f : _126816 -> nat) (g : _126816 -> nat) (s : _126816 -> Prop) : (term47 _126816 f s g) = (term48 _126816 f g s).
Proof. exact (MK_COMB (@lem6930630) (@lem6930627 _126816 f g s)). Qed.
Lemma lem6930635 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem6930636 {_126816 : Type'} : (@nsum _126816) = (@iterate nat _126816 Nat.add).
Proof. exact (@lem6930635 _126816). Qed.
Lemma lem6930637 {_126816 : Type'} (s : _126816 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6930638 {_126816 : Type'} (s : _126816 -> Prop) : (@nsum _126816 s) = (@iterate nat _126816 Nat.add s).
Proof. exact (MK_COMB (@lem6930636 _126816) (@lem6930637 _126816 s)). Qed.
Lemma lem6930639 {_126816 : Type'} (f : _126816 -> nat) (g : _126816 -> nat) : (term49 _126816 f g) = (term49 _126816 f g).
Proof. exact (eq_refl (term49 _126816 f g)). Qed.
Lemma lem6930640 {_126816 : Type'} (s : _126816 -> Prop) (f : _126816 -> nat) (g : _126816 -> nat) : (term50 _126816 s f g) = (term51 _126816 s f g).
Proof. exact (MK_COMB (@lem6930638 _126816 s) (@lem6930639 _126816 f g)). Qed.
Lemma lem6930641 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6930642 {_126816 : Type'} (s : _126816 -> Prop) (f : _126816 -> nat) (g : _126816 -> nat) : (term52 _126816 s f g) = (term53 _126816 s f g).
Proof. exact (MK_COMB (@lem6930641) (@lem6930640 _126816 s f g)). Qed.
Lemma lem6930644 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem6930645 {_126816 : Type'} : (@nsum _126816) = (@iterate nat _126816 Nat.add).
Proof. exact (@lem6930644 _126816). Qed.
Lemma lem6930646 {_126816 : Type'} (s : _126816 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6930647 {_126816 : Type'} (s : _126816 -> Prop) : (@nsum _126816 s) = (@iterate nat _126816 Nat.add s).
Proof. exact (MK_COMB (@lem6930645 _126816) (@lem6930646 _126816 s)). Qed.
Lemma lem6930648 {_126816 : Type'} (f : _126816 -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6930649 {_126816 : Type'} (s : _126816 -> Prop) (f : _126816 -> nat) : (@nsum _126816 s f) = (@iterate nat _126816 Nat.add s f).
Proof. exact (MK_COMB (@lem6930647 _126816 s) (@lem6930648 _126816 f)). Qed.
Lemma lem6930650 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem6930651 {_126816 : Type'} (s : _126816 -> Prop) (f : _126816 -> nat) : (term54 _126816 s f) = (term55 _126816 s f).
Proof. exact (MK_COMB (@lem6930650) (@lem6930649 _126816 s f)). Qed.
Lemma lem6930653 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem6930654 {_126816 : Type'} : (@nsum _126816) = (@iterate nat _126816 Nat.add).
Proof. exact (@lem6930653 _126816). Qed.
Lemma lem6930655 {_126816 : Type'} (s : _126816 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6930656 {_126816 : Type'} (s : _126816 -> Prop) : (@nsum _126816 s) = (@iterate nat _126816 Nat.add s).
Proof. exact (MK_COMB (@lem6930654 _126816) (@lem6930655 _126816 s)). Qed.
Lemma lem6930657 {_126816 : Type'} (g : _126816 -> nat) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem6930658 {_126816 : Type'} (s : _126816 -> Prop) (g : _126816 -> nat) : (@nsum _126816 s g) = (@iterate nat _126816 Nat.add s g).
Proof. exact (MK_COMB (@lem6930656 _126816 s) (@lem6930657 _126816 g)). Qed.
Lemma lem6930659 {_126816 : Type'} (f : _126816 -> nat) (s : _126816 -> Prop) (g : _126816 -> nat) : (term56 _126816 f s g) = (term57 _126816 f s g).
Proof. exact (MK_COMB (@lem6930651 _126816 s f) (@lem6930658 _126816 s g)). Qed.
Lemma lem6930660 {_126816 : Type'} (f : _126816 -> nat) (s : _126816 -> Prop) (g : _126816 -> nat) : ((term50 _126816 s f g) = (term56 _126816 f s g)) = ((term51 _126816 s f g) = (term57 _126816 f s g)).
Proof. exact (MK_COMB (@lem6930642 _126816 s f g) (@lem6930659 _126816 f s g)). Qed.
Lemma lem6930663 {_126816 : Type'} (f : _126816 -> nat) (s : _126816 -> Prop) (g : _126816 -> nat) : (term58 _126816 f s g) = (term59 _126816 f s g).
Proof. exact (MK_COMB (@lem6930631 _126816 f g s) (@lem6930660 _126816 f s g)). Qed.
Lemma lem6930666 {_126816 : Type'} (f : _126816 -> nat) (g : _126816 -> nat) : (term60 _126816 f g) = (term61 _126816 f g).
Proof. exact (fun_ext (fun s : _126816 -> Prop => @lem6930663 _126816 f s g)). Qed.
Lemma lem6930667 {_126816 : Type'} : (@all (_126816 -> Prop)) = (@all (_126816 -> Prop)).
Proof. exact (eq_refl (@all (_126816 -> Prop))). Qed.
Lemma lem6930668 {_126816 : Type'} (f : _126816 -> nat) (g : _126816 -> nat) : (term62 _126816 f g) = (term63 _126816 f g).
Proof. exact (MK_COMB (@lem6930667 _126816) (@lem6930666 _126816 f g)). Qed.
Lemma lem6930673 {_126816 : Type'} (f : _126816 -> nat) : (term64 _126816 f) = (term65 _126816 f).
Proof. exact (fun_ext (fun g : _126816 -> nat => @lem6930668 _126816 f g)). Qed.
Lemma lem6930674 {_126816 : Type'} : (@all (_126816 -> nat)) = (@all (_126816 -> nat)).
Proof. exact (eq_refl (@all (_126816 -> nat))). Qed.
Lemma lem6930675 {_126816 : Type'} (f : _126816 -> nat) : (term66 _126816 f) = (term67 _126816 f).
Proof. exact (MK_COMB (@lem6930674 _126816) (@lem6930673 _126816 f)). Qed.
Lemma lem6930680 {_126816 : Type'} : (term68 _126816) = (term69 _126816).
Proof. exact (fun_ext (fun f : _126816 -> nat => @lem6930675 _126816 f)). Qed.
Lemma lem6930681 {_126816 : Type'} : (@all (_126816 -> nat)) = (@all (_126816 -> nat)).
Proof. exact (eq_refl (@all (_126816 -> nat))). Qed.
Lemma lem6930682 {_126816 : Type'} : (term70 _126816) = (term71 _126816).
Proof. exact (MK_COMB (@lem6930681 _126816) (@lem6930680 _126816)). Qed.
Lemma lem6930687 {_126816 : Type'} : (term71 _126816) = (term70 _126816).
Proof. exact (SYM (@lem6930682 _126816)). Qed.
Lemma lem6930689 {A B : Type'} (op : type1400 B) : term2 A B op.
Proof. exact (EQ_MP (@lem6930492 A B op) (@lem6930491 A B op)). Qed.
Lemma lem6930690 {_126816 : Type'} (op : type1606) : term72 _126816 op.
Proof. exact (@lem6930689 _126816 nat op). Qed.
Lemma lem6930691 {_126816 : Type'} : term73 _126816.
Proof. exact (@lem6930690 _126816 Nat.add). Qed.
Lemma lem6930692 {_126816 : Type'} : term71 _126816.
Proof. exact (@lem6930691 _126816 (@lem6924403)). Qed.
Lemma lem6930693 {_126816 : Type'} : term70 _126816.
Proof. exact (EQ_MP (@lem6930687 _126816) (@lem6930692 _126816)). Qed.
