Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7637129_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm69_spec.
Require Import thm7631335_spec.
Lemma lem7635343 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7635344 {A B : Type'} : (term1 A B) = (term2 A B).
Proof. exact (@lem7635343 (term1 A B)). Qed.
Lemma lem7635345 {A B : Type'} : (term2 A B) = (term1 A B).
Proof. exact (SYM (@lem7635344 A B)). Qed.
Lemma lem7635346 {A B : Type'} (h1 : term3 A B) : term3 A B.
Proof. exact (h1). Qed.
Lemma lem7635347 {A B : Type'} : term4 A B.
Proof. exact (@lem7631335 A B). Qed.
Lemma lem7635350 {B : Type'} : term5 B.
Proof. exact (@lem7631335 B B). Qed.
Lemma lem7635353 {A : Type'} : term5 A.
Proof. exact (@lem7631335 A A). Qed.
Lemma lem7635359 {A B : Type'} (h1 : term6 A B) : term6 A B.
Proof. exact (h1). Qed.
Lemma lem7635360 {A B : Type'} : term7 A B.
Proof. exact (fun h0 : term6 A B => @lem7635359 A B h0). Qed.
Lemma lem7635361 {A B : Type'} (h1 : term7 A B) : term7 A B.
Proof. exact (h1). Qed.
Lemma lem7635362 {A B : Type'} (h1 : term6 A B) : term6 A B.
Proof. exact (h1). Qed.
Lemma lem7635363 {A B : Type'} (h1 : term6 A B) (h2 : term7 A B) : term6 A B.
Proof. exact (@lem7635361 A B h2 (@lem7635362 A B h1)). Qed.
Lemma lem7635364 {A B : Type'} (h1 : term6 A B) : term8 A B.
Proof. exact (fun h0 : term7 A B => @lem7635363 A B h1 h0). Qed.
Lemma lem7635365 {A B : Type'} (h1 : term7 A B) : term7 A B.
Proof. exact (h1). Qed.
Lemma lem7635366 {A B : Type'} (h1 : term6 A B) (h2 : term7 A B) : term6 A B.
Proof. exact (@lem7635364 A B h1 (@lem7635365 A B h2)). Qed.
Lemma lem7635367 {A B : Type'} (h1 : term7 A B) : term7 A B.
Proof. exact (fun h0 : term6 A B => @lem7635366 A B h0 h1). Qed.
Lemma lem7635368 {A B : Type'} : term9 A B.
Proof. exact (fun h0 : term7 A B => @lem7635367 A B h0). Qed.
Lemma lem7635371 {A B : Type'} : term7 A B.
Proof. exact (@lem7635368 A B (@lem7635360 A B)). Qed.
Lemma lem7635372 {A B : Type'} : term7 A B.
Proof. exact (@lem7635371 A B). Qed.
Lemma lem7635454 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7635455 {B : Type'} : (term10 B) = (term11 B).
Proof. exact (@lem7635454 (term5 B)). Qed.
Lemma lem7635466 {A B : Type'} : (term12 A B) = (term12 A B).
Proof. exact (eq_refl (term12 A B)). Qed.
Lemma lem7635467 {A B : Type'} : (term13 A B) = (term14 A B).
Proof. exact (MK_COMB (@lem7635466 A B) (@lem7635455 B)). Qed.
Lemma lem7635470 {A : Type'} : (term15 A) = (term15 A).
Proof. exact (eq_refl (term15 A)). Qed.
Lemma lem7635471 {A B : Type'} : (term16 A B) = (term17 A B).
Proof. exact (MK_COMB (@lem7635470 A) (@lem7635467 A B)). Qed.
Lemma lem7635474 {A B : Type'} : (term18 A B) = (term18 A B).
Proof. exact (eq_refl (term18 A B)). Qed.
Lemma lem7635481 {A B : Type'} : (term6 A B) = (term19 A B).
Proof. exact (MK_COMB (@lem7635474 A B) (@lem7635471 A B)). Qed.
Lemma lem7635486 {B : Type'} (r : nat) : ((term20 B r) = ((term21 B r) = r)) = ((term20 B r) = ((term21 B r) = r)).
Proof. exact (eq_refl ((term20 B r) = ((term21 B r) = r))). Qed.
Lemma lem7635487 {B : Type'} : (term22 B) = (term22 B).
Proof. exact (fun_ext (fun r : nat => @lem7635486 B r)). Qed.
Lemma lem7635488 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7635489 {B : Type'} : (term23 B) = (term23 B).
Proof. exact (MK_COMB (@lem7635488) (@lem7635487 B)). Qed.
Lemma lem7635490 {B : Type'} (a : finite_sum B B) : ((term24 B a) = a) = ((term24 B a) = a).
Proof. exact (eq_refl ((term24 B a) = a)). Qed.
Lemma lem7635491 {B : Type'} : (term25 B) = (term25 B).
Proof. exact (fun_ext (fun a : finite_sum B B => @lem7635490 B a)). Qed.
Lemma lem7635492 {B : Type'} : (@all (finite_sum B B)) = (@all (finite_sum B B)).
Proof. exact (eq_refl (@all (finite_sum B B))). Qed.
Lemma lem7635493 {B : Type'} : (term26 B) = (term26 B).
Proof. exact (MK_COMB (@lem7635492 B) (@lem7635491 B)). Qed.
Lemma lem7635494 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7635495 {B : Type'} : (term27 B) = (term27 B).
Proof. exact (MK_COMB (@lem7635494) (@lem7635493 B)). Qed.
Lemma lem7635496 {B : Type'} : (term5 B) = (term5 B).
Proof. exact (MK_COMB (@lem7635495 B) (@lem7635489 B)). Qed.
Lemma lem7635497 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7635498 {B : Type'} : (term11 B) = (term11 B).
Proof. exact (MK_COMB (@lem7635497) (@lem7635496 B)). Qed.
Lemma lem7635503 {A B : Type'} (r : nat) : ((term28 A B r) = ((term29 A B r) = r)) = ((term28 A B r) = ((term29 A B r) = r)).
Proof. exact (eq_refl ((term28 A B r) = ((term29 A B r) = r))). Qed.
Lemma lem7635504 {A B : Type'} : (term30 A B) = (term30 A B).
Proof. exact (fun_ext (fun r : nat => @lem7635503 A B r)). Qed.
Lemma lem7635505 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7635506 {A B : Type'} : (term31 A B) = (term31 A B).
Proof. exact (MK_COMB (@lem7635505) (@lem7635504 A B)). Qed.
Lemma lem7635507 {A B : Type'} (a : finite_sum A B) : ((term32 A B a) = a) = ((term32 A B a) = a).
Proof. exact (eq_refl ((term32 A B a) = a)). Qed.
Lemma lem7635508 {A B : Type'} : (term33 A B) = (term33 A B).
Proof. exact (fun_ext (fun a : finite_sum A B => @lem7635507 A B a)). Qed.
Lemma lem7635509 {A B : Type'} : (@all (finite_sum A B)) = (@all (finite_sum A B)).
Proof. exact (eq_refl (@all (finite_sum A B))). Qed.
Lemma lem7635510 {A B : Type'} : (term34 A B) = (term34 A B).
Proof. exact (MK_COMB (@lem7635509 A B) (@lem7635508 A B)). Qed.
Lemma lem7635511 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7635512 {A B : Type'} : (term35 A B) = (term35 A B).
Proof. exact (MK_COMB (@lem7635511) (@lem7635510 A B)). Qed.
Lemma lem7635513 {A B : Type'} : (term4 A B) = (term4 A B).
Proof. exact (MK_COMB (@lem7635512 A B) (@lem7635506 A B)). Qed.
Lemma lem7635514 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7635515 {A B : Type'} : (term12 A B) = (term12 A B).
Proof. exact (MK_COMB (@lem7635514) (@lem7635513 A B)). Qed.
Lemma lem7635516 {A B : Type'} : (term14 A B) = (term14 A B).
Proof. exact (MK_COMB (@lem7635515 A B) (@lem7635498 B)). Qed.
Lemma lem7635521 {A : Type'} (r : nat) : ((term20 A r) = ((term21 A r) = r)) = ((term20 A r) = ((term21 A r) = r)).
Proof. exact (eq_refl ((term20 A r) = ((term21 A r) = r))). Qed.
Lemma lem7635522 {A : Type'} : (term22 A) = (term22 A).
Proof. exact (fun_ext (fun r : nat => @lem7635521 A r)). Qed.
Lemma lem7635523 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7635524 {A : Type'} : (term23 A) = (term23 A).
Proof. exact (MK_COMB (@lem7635523) (@lem7635522 A)). Qed.
Lemma lem7635525 {A : Type'} (a : finite_sum A A) : ((term24 A a) = a) = ((term24 A a) = a).
Proof. exact (eq_refl ((term24 A a) = a)). Qed.
Lemma lem7635526 {A : Type'} : (term25 A) = (term25 A).
Proof. exact (fun_ext (fun a : finite_sum A A => @lem7635525 A a)). Qed.
Lemma lem7635527 {A : Type'} : (@all (finite_sum A A)) = (@all (finite_sum A A)).
Proof. exact (eq_refl (@all (finite_sum A A))). Qed.
Lemma lem7635528 {A : Type'} : (term26 A) = (term26 A).
Proof. exact (MK_COMB (@lem7635527 A) (@lem7635526 A)). Qed.
Lemma lem7635529 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7635530 {A : Type'} : (term27 A) = (term27 A).
Proof. exact (MK_COMB (@lem7635529) (@lem7635528 A)). Qed.
Lemma lem7635531 {A : Type'} : (term5 A) = (term5 A).
Proof. exact (MK_COMB (@lem7635530 A) (@lem7635524 A)). Qed.
Lemma lem7635532 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7635533 {A : Type'} : (term15 A) = (term15 A).
Proof. exact (MK_COMB (@lem7635532) (@lem7635531 A)). Qed.
Lemma lem7635534 {A B : Type'} : (term17 A B) = (term17 A B).
Proof. exact (MK_COMB (@lem7635533 A) (@lem7635516 A B)). Qed.
Lemma lem7635539 {A B : Type'} (x : finite_sum A B) (x' : nat) : (term36 A B x x') = (term36 A B x x').
Proof. exact (eq_refl (term36 A B x x')). Qed.
Lemma lem7635540 {A B : Type'} (x : finite_sum A B) : (term37 A B x) = (term37 A B x).
Proof. exact (fun_ext (fun x' : nat => @lem7635539 A B x x')). Qed.
Lemma lem7635541 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7635542 {A B : Type'} (x : finite_sum A B) : (term38 A B x) = (term38 A B x).
Proof. exact (MK_COMB (@lem7635541) (@lem7635540 A B x)). Qed.
Lemma lem7635543 {A B : Type'} : (term39 A B) = (term39 A B).
Proof. exact (fun_ext (fun x : finite_sum A B => @lem7635542 A B x)). Qed.
Lemma lem7635544 {A B : Type'} : (@all (finite_sum A B)) = (@all (finite_sum A B)).
Proof. exact (eq_refl (@all (finite_sum A B))). Qed.
Lemma lem7635545 {A B : Type'} : (term1 A B) = (term1 A B).
Proof. exact (MK_COMB (@lem7635544 A B) (@lem7635543 A B)). Qed.
Lemma lem7635546 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7635547 {A B : Type'} : (term3 A B) = (term3 A B).
Proof. exact (MK_COMB (@lem7635546) (@lem7635545 A B)). Qed.
Lemma lem7635548 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7635549 {A B : Type'} : (term18 A B) = (term18 A B).
Proof. exact (MK_COMB (@lem7635548) (@lem7635547 A B)). Qed.
Lemma lem7635550 {A B : Type'} : (term19 A B) = (term19 A B).
Proof. exact (MK_COMB (@lem7635549 A B) (@lem7635534 A B)). Qed.
Lemma lem7635615 {A B : Type'} : (term6 A B) = (term19 A B).
Proof. exact (TRANS (@lem7635481 A B) (@lem7635550 A B)). Qed.
Lemma lem7635616 {A B : Type'} : (term19 A B) = (term6 A B).
Proof. exact (SYM (@lem7635615 A B)). Qed.
Lemma lem7635617 {A B : Type'} (h1 : term3 A B) : term3 A B.
Proof. exact (h1). Qed.
Lemma lem7635619 {A B : Type'} (h1 : term4 A B) : term4 A B.
Proof. exact (h1). Qed.
Lemma lem7635627 {A B : Type'} (x : finite_sum A B) (x' : nat) : (term40 A B x x') = (term41 A B x x').
Proof. exact (@lem17045 (x = (@mk_finite_sum A B x')) (term28 A B x')). Qed.
Lemma lem7635628 (P : nat -> Prop) : (term42 P) = (term43 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem7635629 {A B : Type'} (x : finite_sum A B) : (term44 A B x) = (term45 A B x).
Proof. exact (@lem7635628 (term37 A B x)). Qed.
Lemma lem7635630 {A B : Type'} (x : finite_sum A B) (x' : nat) : (term46 A B x x') = (term36 A B x x').
Proof. exact (eq_refl (term46 A B x x')). Qed.
Lemma lem7635631 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7635632 {A B : Type'} (x : finite_sum A B) (x' : nat) : (term47 A B x x') = (term40 A B x x').
Proof. exact (MK_COMB (@lem7635631) (@lem7635630 A B x x')). Qed.
Lemma lem7635633 {A B : Type'} (x : finite_sum A B) (x' : nat) : (term47 A B x x') = (term41 A B x x').
Proof. exact (TRANS (@lem7635632 A B x x') (@lem7635627 A B x x')). Qed.
Lemma lem7635634 {A B : Type'} (x : finite_sum A B) : (term48 A B x) = (term49 A B x).
Proof. exact (fun_ext (fun x' : nat => @lem7635633 A B x x')). Qed.
Lemma lem7635635 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7635636 {A B : Type'} (x : finite_sum A B) : (term45 A B x) = (term50 A B x).
Proof. exact (MK_COMB (@lem7635635) (@lem7635634 A B x)). Qed.
Lemma lem7635637 {A B : Type'} (x : finite_sum A B) : (term44 A B x) = (term50 A B x).
Proof. exact (TRANS (@lem7635629 A B x) (@lem7635636 A B x)). Qed.
Lemma lem7635638 {A B : Type'} (P : type49 A B) : (term51 A B P) = (term52 A B P).
Proof. exact (@lem18392 (finite_sum A B) P). Qed.
Lemma lem7635639 {A B : Type'} : (term3 A B) = (term53 A B).
Proof. exact (@lem7635638 A B (term39 A B)). Qed.
Lemma lem7635640 {A B : Type'} (x : finite_sum A B) : (term54 A B x) = (term38 A B x).
Proof. exact (eq_refl (term54 A B x)). Qed.
Lemma lem7635641 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7635642 {A B : Type'} (x : finite_sum A B) : (term55 A B x) = (term44 A B x).
Proof. exact (MK_COMB (@lem7635641) (@lem7635640 A B x)). Qed.
Lemma lem7635643 {A B : Type'} (x : finite_sum A B) : (term55 A B x) = (term50 A B x).
Proof. exact (TRANS (@lem7635642 A B x) (@lem7635637 A B x)). Qed.
Lemma lem7635644 {A B : Type'} : (term56 A B) = (term57 A B).
Proof. exact (fun_ext (fun x : finite_sum A B => @lem7635643 A B x)). Qed.
Lemma lem7635645 {A B : Type'} : (@ex (finite_sum A B)) = (@ex (finite_sum A B)).
Proof. exact (eq_refl (@ex (finite_sum A B))). Qed.
Lemma lem7635646 {A B : Type'} : (term53 A B) = (term58 A B).
Proof. exact (MK_COMB (@lem7635645 A B) (@lem7635644 A B)). Qed.
Lemma lem7635703 {A B : Type'} : (term3 A B) = (term58 A B).
Proof. exact (TRANS (@lem7635639 A B) (@lem7635646 A B)). Qed.
Lemma lem7635704 {A B : Type'} (h1 : term3 A B) : term58 A B.
Proof. exact (EQ_MP (@lem7635703 A B) (@lem7635617 A B h1)). Qed.
Lemma lem7635863 {A B : Type'} (a : finite_sum A B) : ((term32 A B a) = a) = ((term32 A B a) = a).
Proof. exact (eq_refl ((term32 A B a) = a)). Qed.
Lemma lem7635864 {A B : Type'} : (term33 A B) = (term33 A B).
Proof. exact (fun_ext (fun a : finite_sum A B => @lem7635863 A B a)). Qed.
Lemma lem7635865 {A B : Type'} : (@all (finite_sum A B)) = (@all (finite_sum A B)).
Proof. exact (eq_refl (@all (finite_sum A B))). Qed.
Lemma lem7635866 {A B : Type'} : (term34 A B) = (term34 A B).
Proof. exact (MK_COMB (@lem7635865 A B) (@lem7635864 A B)). Qed.
Lemma lem7635881 {A B : Type'} (r : nat) : ((term28 A B r) = ((term29 A B r) = r)) = (term59 A B r).
Proof. exact (@lem17784 (term28 A B r) ((term29 A B r) = r)). Qed.
Lemma lem7635882 {A B : Type'} : (term30 A B) = (term60 A B).
Proof. exact (fun_ext (fun r : nat => @lem7635881 A B r)). Qed.
Lemma lem7635883 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7635884 {A B : Type'} : (term31 A B) = (term61 A B).
Proof. exact (MK_COMB (@lem7635883) (@lem7635882 A B)). Qed.
Lemma lem7635885 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7635886 {A B : Type'} : (term35 A B) = (term35 A B).
Proof. exact (MK_COMB (@lem7635885) (@lem7635866 A B)). Qed.
Lemma lem7635887 {A B : Type'} : (term4 A B) = (term62 A B).
Proof. exact (MK_COMB (@lem7635886 A B) (@lem7635884 A B)). Qed.
Lemma lem7635893 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term63 A P Q) = (term64 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7635894 (P : nat -> Prop) (Q : nat -> Prop) : (term65 P Q) = (term66 P Q).
Proof. exact (@lem7635893 nat P Q). Qed.
Lemma lem7635895 {A B : Type'} : (term67 A B) = (term68 A B).
Proof. exact (@lem7635894 (term69 A B) (term70 A B)). Qed.
Lemma lem7635896 {A B : Type'} (r : nat) : (term71 A B r) = (term72 A B r).
Proof. exact (eq_refl (term71 A B r)). Qed.
Lemma lem7635897 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7635898 {A B : Type'} (r : nat) : (term73 A B r) = (term74 A B r).
Proof. exact (MK_COMB (@lem7635897) (@lem7635896 A B r)). Qed.
Lemma lem7635899 {A B : Type'} (r : nat) : (term75 A B r) = (term76 A B r).
Proof. exact (eq_refl (term75 A B r)). Qed.
Lemma lem7635900 {A B : Type'} (r : nat) : (term77 A B r) = (term59 A B r).
Proof. exact (MK_COMB (@lem7635898 A B r) (@lem7635899 A B r)). Qed.
Lemma lem7635901 {A B : Type'} : (term78 A B) = (term60 A B).
Proof. exact (fun_ext (fun r : nat => @lem7635900 A B r)). Qed.
Lemma lem7635902 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7635903 {A B : Type'} : (term67 A B) = (term61 A B).
Proof. exact (MK_COMB (@lem7635902) (@lem7635901 A B)). Qed.
Lemma lem7635904 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7635905 {A B : Type'} : (term79 A B) = (term80 A B).
Proof. exact (MK_COMB (@lem7635904) (@lem7635903 A B)). Qed.
Lemma lem7635906 {A B : Type'} (r : nat) : (term71 A B r) = (term72 A B r).
Proof. exact (eq_refl (term71 A B r)). Qed.
Lemma lem7635907 {A B : Type'} : (term81 A B) = (term69 A B).
Proof. exact (fun_ext (fun r : nat => @lem7635906 A B r)). Qed.
Lemma lem7635908 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7635909 {A B : Type'} : (term82 A B) = (term83 A B).
Proof. exact (MK_COMB (@lem7635908) (@lem7635907 A B)). Qed.
Lemma lem7635910 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7635911 {A B : Type'} : (term84 A B) = (term85 A B).
Proof. exact (MK_COMB (@lem7635910) (@lem7635909 A B)). Qed.
Lemma lem7635912 {A B : Type'} (r : nat) : (term75 A B r) = (term76 A B r).
Proof. exact (eq_refl (term75 A B r)). Qed.
Lemma lem7635913 {A B : Type'} : (term86 A B) = (term70 A B).
Proof. exact (fun_ext (fun r : nat => @lem7635912 A B r)). Qed.
Lemma lem7635914 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7635915 {A B : Type'} : (term87 A B) = (term88 A B).
Proof. exact (MK_COMB (@lem7635914) (@lem7635913 A B)). Qed.
Lemma lem7635916 {A B : Type'} : (term68 A B) = (term89 A B).
Proof. exact (MK_COMB (@lem7635911 A B) (@lem7635915 A B)). Qed.
Lemma lem7635917 {A B : Type'} : ((term67 A B) = (term68 A B)) = ((term61 A B) = (term89 A B)).
Proof. exact (MK_COMB (@lem7635905 A B) (@lem7635916 A B)). Qed.
Lemma lem7635918 {A B : Type'} : (term61 A B) = (term89 A B).
Proof. exact (EQ_MP (@lem7635917 A B) (@lem7635895 A B)). Qed.
Lemma lem7636015 {A B : Type'} : (term35 A B) = (term35 A B).
Proof. exact (eq_refl (term35 A B)). Qed.
Lemma lem7636018 {A B : Type'} : (term62 A B) = (term90 A B).
Proof. exact (MK_COMB (@lem7636015 A B) (@lem7635918 A B)). Qed.
Lemma lem7636019 {A B : Type'} : (term4 A B) = (term90 A B).
Proof. exact (TRANS (@lem7635887 A B) (@lem7636018 A B)). Qed.
Lemma lem7636020 {A B : Type'} (h1 : term4 A B) : term90 A B.
Proof. exact (EQ_MP (@lem7636019 A B) (@lem7635619 A B h1)). Qed.
Lemma lem7636179 {A B : Type'} (x : finite_sum A B) (h1 : term50 A B x) : term50 A B x.
Proof. exact (h1). Qed.
Lemma lem7636309 {A B : Type'} (r : nat) : (term76 A B r) = (term76 A B r).
Proof. exact (eq_refl (term76 A B r)). Qed.
Lemma lem7636310 {A B : Type'} : (term70 A B) = (term70 A B).
Proof. exact (fun_ext (fun r : nat => @lem7636309 A B r)). Qed.
Lemma lem7636311 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7636312 {A B : Type'} : (term88 A B) = (term88 A B).
Proof. exact (MK_COMB (@lem7636311) (@lem7636310 A B)). Qed.
Lemma lem7636347 {A B : Type'} (r : nat) : (term72 A B r) = (term72 A B r).
Proof. exact (eq_refl (term72 A B r)). Qed.
Lemma lem7636348 {A B : Type'} : (term69 A B) = (term69 A B).
Proof. exact (fun_ext (fun r : nat => @lem7636347 A B r)). Qed.
Lemma lem7636349 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7636350 {A B : Type'} : (term83 A B) = (term83 A B).
Proof. exact (MK_COMB (@lem7636349) (@lem7636348 A B)). Qed.
Lemma lem7636351 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7636352 {A B : Type'} : (term85 A B) = (term85 A B).
Proof. exact (MK_COMB (@lem7636351) (@lem7636350 A B)). Qed.
Lemma lem7636353 {A B : Type'} : (term89 A B) = (term89 A B).
Proof. exact (MK_COMB (@lem7636352 A B) (@lem7636312 A B)). Qed.
Lemma lem7636362 {A B : Type'} (a : finite_sum A B) : ((term32 A B a) = a) = ((term32 A B a) = a).
Proof. exact (eq_refl ((term32 A B a) = a)). Qed.
Lemma lem7636363 {A B : Type'} : (term33 A B) = (term33 A B).
Proof. exact (fun_ext (fun a : finite_sum A B => @lem7636362 A B a)). Qed.
Lemma lem7636364 {A B : Type'} : (@all (finite_sum A B)) = (@all (finite_sum A B)).
Proof. exact (eq_refl (@all (finite_sum A B))). Qed.
Lemma lem7636365 {A B : Type'} : (term34 A B) = (term34 A B).
Proof. exact (MK_COMB (@lem7636364 A B) (@lem7636363 A B)). Qed.
Lemma lem7636366 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7636367 {A B : Type'} : (term35 A B) = (term35 A B).
Proof. exact (MK_COMB (@lem7636366) (@lem7636365 A B)). Qed.
Lemma lem7636368 {A B : Type'} : (term90 A B) = (term90 A B).
Proof. exact (MK_COMB (@lem7636367 A B) (@lem7636353 A B)). Qed.
Lemma lem7636369 {A B : Type'} (h1 : term4 A B) : term90 A B.
Proof. exact (EQ_MP (@lem7636368 A B) (@lem7636020 A B h1)). Qed.
Lemma lem7636499 {A B : Type'} (x : finite_sum A B) (x' : nat) : (term41 A B x x') = (term41 A B x x').
Proof. exact (eq_refl (term41 A B x x')). Qed.
Lemma lem7636500 {A B : Type'} (x : finite_sum A B) : (term49 A B x) = (term49 A B x).
Proof. exact (fun_ext (fun x' : nat => @lem7636499 A B x x')). Qed.
Lemma lem7636501 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7636502 {A B : Type'} (x : finite_sum A B) : (term50 A B x) = (term50 A B x).
Proof. exact (MK_COMB (@lem7636501) (@lem7636500 A B x)). Qed.
Lemma lem7636503 {A B : Type'} (x : finite_sum A B) (h1 : term50 A B x) : term50 A B x.
Proof. exact (EQ_MP (@lem7636502 A B x) (@lem7636179 A B x h1)). Qed.
Lemma lem7636508 {A B : Type'} (h1 : term4 A B) : term89 A B.
Proof. exact (proj2 (@lem7636369 A B h1)). Qed.
Lemma lem7636509 {A B : Type'} (h1 : term4 A B) : term34 A B.
Proof. exact (proj1 (@lem7636369 A B h1)). Qed.
Lemma lem7636511 {A B : Type'} (h1 : term4 A B) : term83 A B.
Proof. exact (proj1 (@lem7636508 A B h1)). Qed.
Lemma lem7636523 {A B : Type'} (x : finite_sum A B) (x' : nat) : (term41 A B x x') = (term41 A B x x').
Proof. exact (eq_refl (term41 A B x x')). Qed.
Lemma lem7636524 {A B : Type'} (x : finite_sum A B) : (term49 A B x) = (term49 A B x).
Proof. exact (fun_ext (fun x' : nat => @lem7636523 A B x x')). Qed.
Lemma lem7636525 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7636527 {A B : Type'} (x : finite_sum A B) : (term50 A B x) = (term50 A B x).
Proof. exact (MK_COMB (@lem7636525) (@lem7636524 A B x)). Qed.
Lemma lem7636528 {A B : Type'} (x : finite_sum A B) (h1 : term50 A B x) : term50 A B x.
Proof. exact (EQ_MP (@lem7636527 A B x) (@lem7636503 A B x h1)). Qed.
Lemma lem7636563 {A B : Type'} (a : finite_sum A B) : ((term32 A B a) = a) = ((term32 A B a) = a).
Proof. exact (eq_refl ((term32 A B a) = a)). Qed.
Lemma lem7636564 {A B : Type'} : (term33 A B) = (term33 A B).
Proof. exact (fun_ext (fun a : finite_sum A B => @lem7636563 A B a)). Qed.
Lemma lem7636565 {A B : Type'} : (@all (finite_sum A B)) = (@all (finite_sum A B)).
Proof. exact (eq_refl (@all (finite_sum A B))). Qed.
Lemma lem7636567 {A B : Type'} : (term34 A B) = (term34 A B).
Proof. exact (MK_COMB (@lem7636565 A B) (@lem7636564 A B)). Qed.
Lemma lem7636568 {A B : Type'} (h1 : term4 A B) : term34 A B.
Proof. exact (EQ_MP (@lem7636567 A B) (@lem7636509 A B h1)). Qed.
Lemma lem7636576 {A B : Type'} (r : nat) : (term72 A B r) = (term72 A B r).
Proof. exact (eq_refl (term72 A B r)). Qed.
Lemma lem7636577 {A B : Type'} : (term69 A B) = (term69 A B).
Proof. exact (fun_ext (fun r : nat => @lem7636576 A B r)). Qed.
Lemma lem7636578 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7636580 {A B : Type'} : (term83 A B) = (term83 A B).
Proof. exact (MK_COMB (@lem7636578) (@lem7636577 A B)). Qed.
Lemma lem7636581 {A B : Type'} (h1 : term4 A B) : term83 A B.
Proof. exact (EQ_MP (@lem7636580 A B) (@lem7636511 A B h1)). Qed.
Lemma lem7636628 {A B : Type'} (_98378 : nat) (x : finite_sum A B) (h1 : term50 A B x) : term91 A B x _98378.
Proof. exact (@lem7636528 A B x h1 _98378). Qed.
Lemma lem7636629 {A B : Type'} (x : finite_sum A B) (_98378 : nat) : (term91 A B x _98378) = (term41 A B x _98378).
Proof. exact (eq_refl (term91 A B x _98378)). Qed.
Lemma lem7636640 {A B : Type'} (_98382 : finite_sum A B) (h1 : term4 A B) : term92 A B _98382.
Proof. exact (@lem7636568 A B h1 _98382). Qed.
Lemma lem7636641 {A B : Type'} (_98382 : finite_sum A B) : (term92 A B _98382) = ((term32 A B _98382) = _98382).
Proof. exact (eq_refl (term92 A B _98382)). Qed.
Lemma lem7636643 {A B : Type'} (_98383 : nat) (h1 : term4 A B) : term71 A B _98383.
Proof. exact (@lem7636581 A B h1 _98383). Qed.
Lemma lem7636644 {A B : Type'} (_98383 : nat) : (term71 A B _98383) = (term72 A B _98383).
Proof. exact (eq_refl (term71 A B _98383)). Qed.
Lemma lem7636663 {A B : Type'} (_98378 : nat) (x : finite_sum A B) (h1 : term50 A B x) : term41 A B x _98378.
Proof. exact (EQ_MP (@lem7636629 A B x _98378) (@lem7636628 A B _98378 x h1)). Qed.
Lemma lem7636685 {A B : Type'} (_98383 : nat) (h1 : term4 A B) : term72 A B _98383.
Proof. exact (EQ_MP (@lem7636644 A B _98383) (@lem7636643 A B _98383 h1)). Qed.
Lemma lem7636741 {A B : Type'} : (@dest_finite_sum A B) = (@dest_finite_sum A B).
Proof. exact (eq_refl (@dest_finite_sum A B)). Qed.
Lemma lem7636742 {A B : Type'} (_98396 : finite_sum A B) (_98397 : finite_sum A B) (h1 : _98396 = _98397) : _98396 = _98397.
Proof. exact (h1). Qed.
Lemma lem7636743 {A B : Type'} (_98396 : finite_sum A B) (_98397 : finite_sum A B) (h1 : _98396 = _98397) : (@dest_finite_sum A B _98396) = (@dest_finite_sum A B _98397).
Proof. exact (MK_COMB (@lem7636741 A B) (@lem7636742 A B _98396 _98397 h1)). Qed.
Lemma lem7636744 {A B : Type'} (_98396 : finite_sum A B) (_98397 : finite_sum A B) : term93 A B _98396 _98397.
Proof. exact (fun h0 : _98396 = _98397 => @lem7636743 A B _98396 _98397 h0). Qed.
Lemma lem7636746 (a : Prop) (b : Prop) : (a -> b) = (term94 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem7636747 {A B : Type'} (_98396 : finite_sum A B) (_98397 : finite_sum A B) : (term93 A B _98396 _98397) = (term95 A B _98396 _98397).
Proof. exact (@lem7636746 (_98396 = _98397) ((@dest_finite_sum A B _98396) = (@dest_finite_sum A B _98397))). Qed.
Lemma lem7636748 {A B : Type'} (_98396 : finite_sum A B) (_98397 : finite_sum A B) : term95 A B _98396 _98397.
Proof. exact (EQ_MP (@lem7636747 A B _98396 _98397) (@lem7636744 A B _98396 _98397)). Qed.
Lemma lem7636844 {A B : Type'} (x : finite_sum A B) (y : finite_sum A B) (z : finite_sum A B) : term96 A B x y z.
Proof. exact (@lem21385 (finite_sum A B) x y z). Qed.
Lemma lem7636850 {A B : Type'} (_98382 : finite_sum A B) (h1 : term4 A B) : (term32 A B _98382) = _98382.
Proof. exact (EQ_MP (@lem7636641 A B _98382) (@lem7636640 A B _98382 h1)). Qed.
Lemma lem7636851 {A B : Type'} (_98382 : finite_sum A B) (h1 : term4 A B) : (term32 A B _98382) = _98382.
Proof. exact (@lem7636850 A B _98382 h1). Qed.
Lemma lem7636852 {A B : Type'} (x : finite_sum A B) (h1 : term4 A B) : (term32 A B x) = x.
Proof. exact (@lem7636851 A B x h1). Qed.
Lemma lem7636853 {A B : Type'} (x : finite_sum A B) (h1 : term4 A B) : term97 A B x.
Proof. exact (fun h0 : term98 A B x => @lem7636852 A B x h1). Qed.
Lemma lem7636855 (p : Prop) : (term99 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7636856 {A B : Type'} (x : finite_sum A B) : (term97 A B x) = ((term32 A B x) = x).
Proof. exact (@lem7636855 ((term32 A B x) = x)). Qed.
Lemma lem7636857 {A B : Type'} (x : finite_sum A B) (h1 : term4 A B) : (term32 A B x) = x.
Proof. exact (EQ_MP (@lem7636856 A B x) (@lem7636853 A B x h1)). Qed.
Lemma lem7636859 {A B : Type'} (x : finite_sum A B) : x = x.
Proof. exact (@lem21386 (finite_sum A B) x). Qed.
Lemma lem7636860 {A B : Type'} (x : finite_sum A B) : x = x.
Proof. exact (@lem7636859 A B x). Qed.
Lemma lem7636861 {A B : Type'} (x : finite_sum A B) : (term32 A B x) = (term32 A B x).
Proof. exact (@lem7636860 A B (term32 A B x)). Qed.
Lemma lem7636862 {A B : Type'} (x : finite_sum A B) : term100 A B x.
Proof. exact (fun h0 : term101 A B x => @lem7636861 A B x). Qed.
Lemma lem7636864 (p : Prop) : (term99 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7636865 {A B : Type'} (x : finite_sum A B) : (term100 A B x) = ((term32 A B x) = (term32 A B x)).
Proof. exact (@lem7636864 ((term32 A B x) = (term32 A B x))). Qed.
Lemma lem7636866 {A B : Type'} (x : finite_sum A B) : (term32 A B x) = (term32 A B x).
Proof. exact (EQ_MP (@lem7636865 A B x) (@lem7636862 A B x)). Qed.
Lemma lem7636884 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7636885 {A B : Type'} (y : finite_sum A B) (x : finite_sum A B) (z : finite_sum A B) : (term102 A B x y z) = (term103 A B y x z).
Proof. exact (@lem7636884 (y = z) (term104 A B x z)). Qed.
Lemma lem7636895 {A B : Type'} (x : finite_sum A B) (y : finite_sum A B) : (term105 A B x y) = (term105 A B x y).
Proof. exact (eq_refl (term105 A B x y)). Qed.
Lemma lem7636896 {A B : Type'} (y : finite_sum A B) (x : finite_sum A B) (z : finite_sum A B) : (term96 A B x y z) = (term106 A B y x z).
Proof. exact (MK_COMB (@lem7636895 A B x y) (@lem7636885 A B y x z)). Qed.
Lemma lem7636900 (q : Prop) (p : Prop) (r : Prop) : (term107 p q r) = (term107 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7636901 {A B : Type'} (y : finite_sum A B) (x : finite_sum A B) (z : finite_sum A B) : (term106 A B y x z) = (term108 A B y x z).
Proof. exact (@lem7636900 (y = z) (term104 A B x y) (term104 A B x z)). Qed.
Lemma lem7636923 {A B : Type'} (y : finite_sum A B) (x : finite_sum A B) (z : finite_sum A B) : (term96 A B x y z) = (term108 A B y x z).
Proof. exact (TRANS (@lem7636896 A B y x z) (@lem7636901 A B y x z)). Qed.
Lemma lem7636924 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7636925 {A B : Type'} (y : finite_sum A B) (x : finite_sum A B) (z : finite_sum A B) : (term109 A B x y z) = (term110 A B y x z).
Proof. exact (MK_COMB (@lem7636924) (@lem7636923 A B y x z)). Qed.
Lemma lem7636947 {A B : Type'} (y : finite_sum A B) (x : finite_sum A B) (z : finite_sum A B) : (term108 A B y x z) = (term108 A B y x z).
Proof. exact (eq_refl (term108 A B y x z)). Qed.
Lemma lem7636948 {A B : Type'} (y : finite_sum A B) (x : finite_sum A B) (z : finite_sum A B) : ((term96 A B x y z) = (term108 A B y x z)) = ((term108 A B y x z) = (term108 A B y x z)).
Proof. exact (MK_COMB (@lem7636925 A B y x z) (@lem7636947 A B y x z)). Qed.
Lemma lem7636950 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7636951 (x : Prop) : (x = x) = True.
Proof. exact (@lem7636950 Prop x). Qed.
Lemma lem7636952 {A B : Type'} (y : finite_sum A B) (x : finite_sum A B) (z : finite_sum A B) : ((term108 A B y x z) = (term108 A B y x z)) = True.
Proof. exact (@lem7636951 (term108 A B y x z)). Qed.
Lemma lem7636953 {A B : Type'} (y : finite_sum A B) (x : finite_sum A B) (z : finite_sum A B) : ((term96 A B x y z) = (term108 A B y x z)) = True.
Proof. exact (TRANS (@lem7636948 A B y x z) (@lem7636952 A B y x z)). Qed.
Lemma lem7636954 {A B : Type'} (y : finite_sum A B) (x : finite_sum A B) (z : finite_sum A B) : True = ((term96 A B x y z) = (term108 A B y x z)).
Proof. exact (SYM (@lem7636953 A B y x z)). Qed.
Lemma lem7636955 {A B : Type'} (y : finite_sum A B) (x : finite_sum A B) (z : finite_sum A B) : (term96 A B x y z) = (term108 A B y x z).
Proof. exact (EQ_MP (@lem7636954 A B y x z) (@lem0)). Qed.
Lemma lem7636956 {A B : Type'} (y : finite_sum A B) (x : finite_sum A B) (z : finite_sum A B) : term108 A B y x z.
Proof. exact (EQ_MP (@lem7636955 A B y x z) (@lem7636844 A B x y z)). Qed.
Lemma lem7636958 (b : Prop) (a : Prop) : (a \/ b) = (term111 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7636959 {A B : Type'} (x : finite_sum A B) (y : finite_sum A B) (z : finite_sum A B) : (term108 A B y x z) = (term112 A B x y z).
Proof. exact (@lem7636958 (term113 A B y x z) (y = z)). Qed.
Lemma lem7636961 (a : Prop) (b : Prop) : (term114 a b) = (term115 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7636962 {A B : Type'} (y : finite_sum A B) (x : finite_sum A B) (z : finite_sum A B) : (term116 A B y x z) = (term117 A B y x z).
Proof. exact (@lem7636961 (term104 A B x y) (term104 A B x z)). Qed.
Lemma lem7636964 (a : Prop) : (term118 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7636965 {A B : Type'} (x : finite_sum A B) (y : finite_sum A B) : (term119 A B x y) = (x = y).
Proof. exact (@lem7636964 (x = y)). Qed.
Lemma lem7636966 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7636967 {A B : Type'} (x : finite_sum A B) (y : finite_sum A B) : (term120 A B x y) = (term121 A B x y).
Proof. exact (MK_COMB (@lem7636966) (@lem7636965 A B x y)). Qed.
Lemma lem7636969 (a : Prop) : (term118 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7636970 {A B : Type'} (x : finite_sum A B) (z : finite_sum A B) : (term119 A B x z) = (x = z).
Proof. exact (@lem7636969 (x = z)). Qed.
Lemma lem7636971 {A B : Type'} (y : finite_sum A B) (x : finite_sum A B) (z : finite_sum A B) : (term117 A B y x z) = (term122 A B y x z).
Proof. exact (MK_COMB (@lem7636967 A B x y) (@lem7636970 A B x z)). Qed.
Lemma lem7636972 {A B : Type'} (y : finite_sum A B) (x : finite_sum A B) (z : finite_sum A B) : (term116 A B y x z) = (term122 A B y x z).
Proof. exact (TRANS (@lem7636962 A B y x z) (@lem7636971 A B y x z)). Qed.
Lemma lem7636973 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7636974 {A B : Type'} (y : finite_sum A B) (x : finite_sum A B) (z : finite_sum A B) : (term123 A B y x z) = (term124 A B y x z).
Proof. exact (MK_COMB (@lem7636973) (@lem7636972 A B y x z)). Qed.
Lemma lem7636975 {A B : Type'} (y : finite_sum A B) (z : finite_sum A B) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem7636976 {A B : Type'} (x : finite_sum A B) (y : finite_sum A B) (z : finite_sum A B) : (term112 A B x y z) = (term125 A B x y z).
Proof. exact (MK_COMB (@lem7636974 A B y x z) (@lem7636975 A B y z)). Qed.
Lemma lem7636977 {A B : Type'} (x : finite_sum A B) (y : finite_sum A B) (z : finite_sum A B) : (term108 A B y x z) = (term125 A B x y z).
Proof. exact (TRANS (@lem7636959 A B x y z) (@lem7636976 A B x y z)). Qed.
Lemma lem7636979 {A B : Type'} (x : finite_sum A B) (h1 : term4 A B) : term126 A B x.
Proof. exact (conj (@lem7636857 A B x h1) (@lem7636866 A B x)). Qed.
Lemma lem7636981 {A B : Type'} (x : finite_sum A B) (y : finite_sum A B) (z : finite_sum A B) : term125 A B x y z.
Proof. exact (EQ_MP (@lem7636977 A B x y z) (@lem7636956 A B y x z)). Qed.
Lemma lem7636982 {A B : Type'} (x : finite_sum A B) (y : finite_sum A B) (z : finite_sum A B) : term125 A B x y z.
Proof. exact (@lem7636981 A B x y z). Qed.
Lemma lem7636983 {A B : Type'} (x : finite_sum A B) : term127 A B x.
Proof. exact (@lem7636982 A B (term32 A B x) x (term32 A B x)). Qed.
Lemma lem7636986 {A B : Type'} (x : finite_sum A B) (h1 : term4 A B) : x = (term32 A B x).
Proof. exact (@lem7636983 A B x (@lem7636979 A B x h1)). Qed.
Lemma lem7636987 {A B : Type'} (x : finite_sum A B) (h1 : term4 A B) : x = (term32 A B x).
Proof. exact (@lem7636986 A B x h1). Qed.
Lemma lem7636988 {A B : Type'} (x : finite_sum A B) (h1 : term4 A B) : term128 A B x.
Proof. exact (fun h0 : term129 A B x => @lem7636987 A B x h1). Qed.
Lemma lem7636990 (p : Prop) : (term99 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7636991 {A B : Type'} (x : finite_sum A B) : (term128 A B x) = (x = (term32 A B x)).
Proof. exact (@lem7636990 (x = (term32 A B x))). Qed.
Lemma lem7636992 {A B : Type'} (x : finite_sum A B) (h1 : term4 A B) : x = (term32 A B x).
Proof. exact (EQ_MP (@lem7636991 A B x) (@lem7636988 A B x h1)). Qed.
Lemma lem7636994 {A B : Type'} (_98382 : finite_sum A B) (h1 : term4 A B) : (term32 A B _98382) = _98382.
Proof. exact (EQ_MP (@lem7636641 A B _98382) (@lem7636640 A B _98382 h1)). Qed.
Lemma lem7636995 {A B : Type'} (_98382 : finite_sum A B) (h1 : term4 A B) : (term32 A B _98382) = _98382.
Proof. exact (@lem7636994 A B _98382 h1). Qed.
Lemma lem7636996 {A B : Type'} (x : finite_sum A B) (h1 : term4 A B) : (term32 A B x) = x.
Proof. exact (@lem7636995 A B x h1). Qed.
Lemma lem7636997 {A B : Type'} (x : finite_sum A B) (h1 : term4 A B) : term97 A B x.
Proof. exact (fun h0 : term98 A B x => @lem7636996 A B x h1). Qed.
Lemma lem7636999 (p : Prop) : (term99 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7637000 {A B : Type'} (x : finite_sum A B) : (term97 A B x) = ((term32 A B x) = x).
Proof. exact (@lem7636999 ((term32 A B x) = x)). Qed.
Lemma lem7637001 {A B : Type'} (x : finite_sum A B) (h1 : term4 A B) : (term32 A B x) = x.
Proof. exact (EQ_MP (@lem7637000 A B x) (@lem7636997 A B x h1)). Qed.
Lemma lem7637007 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7637008 {A B : Type'} (_98396 : finite_sum A B) (_98397 : finite_sum A B) : (term95 A B _98396 _98397) = (term130 A B _98396 _98397).
Proof. exact (@lem7637007 ((@dest_finite_sum A B _98396) = (@dest_finite_sum A B _98397)) (term104 A B _98396 _98397)). Qed.
Lemma lem7637018 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7637019 {A B : Type'} (_98396 : finite_sum A B) (_98397 : finite_sum A B) : (term131 A B _98396 _98397) = (term132 A B _98396 _98397).
Proof. exact (MK_COMB (@lem7637018) (@lem7637008 A B _98396 _98397)). Qed.
Lemma lem7637029 {A B : Type'} (_98396 : finite_sum A B) (_98397 : finite_sum A B) : (term130 A B _98396 _98397) = (term130 A B _98396 _98397).
Proof. exact (eq_refl (term130 A B _98396 _98397)). Qed.
Lemma lem7637030 {A B : Type'} (_98396 : finite_sum A B) (_98397 : finite_sum A B) : ((term95 A B _98396 _98397) = (term130 A B _98396 _98397)) = ((term130 A B _98396 _98397) = (term130 A B _98396 _98397)).
Proof. exact (MK_COMB (@lem7637019 A B _98396 _98397) (@lem7637029 A B _98396 _98397)). Qed.
Lemma lem7637032 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7637033 (x : Prop) : (x = x) = True.
Proof. exact (@lem7637032 Prop x). Qed.
Lemma lem7637034 {A B : Type'} (_98396 : finite_sum A B) (_98397 : finite_sum A B) : ((term130 A B _98396 _98397) = (term130 A B _98396 _98397)) = True.
Proof. exact (@lem7637033 (term130 A B _98396 _98397)). Qed.
Lemma lem7637035 {A B : Type'} (_98396 : finite_sum A B) (_98397 : finite_sum A B) : ((term95 A B _98396 _98397) = (term130 A B _98396 _98397)) = True.
Proof. exact (TRANS (@lem7637030 A B _98396 _98397) (@lem7637034 A B _98396 _98397)). Qed.
Lemma lem7637036 {A B : Type'} (_98396 : finite_sum A B) (_98397 : finite_sum A B) : True = ((term95 A B _98396 _98397) = (term130 A B _98396 _98397)).
Proof. exact (SYM (@lem7637035 A B _98396 _98397)). Qed.
Lemma lem7637037 {A B : Type'} (_98396 : finite_sum A B) (_98397 : finite_sum A B) : (term95 A B _98396 _98397) = (term130 A B _98396 _98397).
Proof. exact (EQ_MP (@lem7637036 A B _98396 _98397) (@lem0)). Qed.
Lemma lem7637038 {A B : Type'} (_98396 : finite_sum A B) (_98397 : finite_sum A B) : term130 A B _98396 _98397.
Proof. exact (EQ_MP (@lem7637037 A B _98396 _98397) (@lem7636748 A B _98396 _98397)). Qed.
Lemma lem7637040 (b : Prop) (a : Prop) : (a \/ b) = (term111 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7637041 {A B : Type'} (_98396 : finite_sum A B) (_98397 : finite_sum A B) : (term130 A B _98396 _98397) = (term133 A B _98396 _98397).
Proof. exact (@lem7637040 (term104 A B _98396 _98397) ((@dest_finite_sum A B _98396) = (@dest_finite_sum A B _98397))). Qed.
Lemma lem7637043 (a : Prop) : (term118 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7637044 {A B : Type'} (_98396 : finite_sum A B) (_98397 : finite_sum A B) : (term119 A B _98396 _98397) = (_98396 = _98397).
Proof. exact (@lem7637043 (_98396 = _98397)). Qed.
Lemma lem7637045 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7637046 {A B : Type'} (_98396 : finite_sum A B) (_98397 : finite_sum A B) : (term134 A B _98396 _98397) = (term135 A B _98396 _98397).
Proof. exact (MK_COMB (@lem7637045) (@lem7637044 A B _98396 _98397)). Qed.
Lemma lem7637047 {A B : Type'} (_98396 : finite_sum A B) (_98397 : finite_sum A B) : ((@dest_finite_sum A B _98396) = (@dest_finite_sum A B _98397)) = ((@dest_finite_sum A B _98396) = (@dest_finite_sum A B _98397)).
Proof. exact (eq_refl ((@dest_finite_sum A B _98396) = (@dest_finite_sum A B _98397))). Qed.
Lemma lem7637048 {A B : Type'} (_98396 : finite_sum A B) (_98397 : finite_sum A B) : (term133 A B _98396 _98397) = (term93 A B _98396 _98397).
Proof. exact (MK_COMB (@lem7637046 A B _98396 _98397) (@lem7637047 A B _98396 _98397)). Qed.
Lemma lem7637049 {A B : Type'} (_98396 : finite_sum A B) (_98397 : finite_sum A B) : (term130 A B _98396 _98397) = (term93 A B _98396 _98397).
Proof. exact (TRANS (@lem7637041 A B _98396 _98397) (@lem7637048 A B _98396 _98397)). Qed.
Lemma lem7637052 {A B : Type'} (_98396 : finite_sum A B) (_98397 : finite_sum A B) : term93 A B _98396 _98397.
Proof. exact (EQ_MP (@lem7637049 A B _98396 _98397) (@lem7637038 A B _98396 _98397)). Qed.
Lemma lem7637053 {A B : Type'} (_98396 : finite_sum A B) (_98397 : finite_sum A B) : term93 A B _98396 _98397.
Proof. exact (@lem7637052 A B _98396 _98397). Qed.
Lemma lem7637054 {A B : Type'} (x : finite_sum A B) : term136 A B x.
Proof. exact (@lem7637053 A B (term32 A B x) x). Qed.
Lemma lem7637057 {A B : Type'} (x : finite_sum A B) (h1 : term4 A B) : (term137 A B x) = (@dest_finite_sum A B x).
Proof. exact (@lem7637054 A B x (@lem7637001 A B x h1)). Qed.
Lemma lem7637058 {A B : Type'} (x : finite_sum A B) (h1 : term4 A B) : (term137 A B x) = (@dest_finite_sum A B x).
Proof. exact (@lem7637057 A B x h1). Qed.
Lemma lem7637059 {A B : Type'} (x : finite_sum A B) (h1 : term4 A B) : term138 A B x.
Proof. exact (fun h0 : term139 A B x => @lem7637058 A B x h1). Qed.
Lemma lem7637061 (p : Prop) : (term99 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7637062 {A B : Type'} (x : finite_sum A B) : (term138 A B x) = ((term137 A B x) = (@dest_finite_sum A B x)).
Proof. exact (@lem7637061 ((term137 A B x) = (@dest_finite_sum A B x))). Qed.
Lemma lem7637063 {A B : Type'} (x : finite_sum A B) (h1 : term4 A B) : (term137 A B x) = (@dest_finite_sum A B x).
Proof. exact (EQ_MP (@lem7637062 A B x) (@lem7637059 A B x h1)). Qed.
Lemma lem7637065 (b : Prop) (a : Prop) : (a \/ b) = (term111 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7637066 {A B : Type'} (_98383 : nat) : (term72 A B _98383) = (term140 A B _98383).
Proof. exact (@lem7637065 (term141 A B _98383) (term28 A B _98383)). Qed.
Lemma lem7637068 (a : Prop) : (term118 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7637069 {A B : Type'} (_98383 : nat) : (term142 A B _98383) = ((term29 A B _98383) = _98383).
Proof. exact (@lem7637068 ((term29 A B _98383) = _98383)). Qed.
Lemma lem7637070 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7637071 {A B : Type'} (_98383 : nat) : (term143 A B _98383) = (term144 A B _98383).
Proof. exact (MK_COMB (@lem7637070) (@lem7637069 A B _98383)). Qed.
Lemma lem7637072 {A B : Type'} (_98383 : nat) : (term28 A B _98383) = (term28 A B _98383).
Proof. exact (eq_refl (term28 A B _98383)). Qed.
Lemma lem7637073 {A B : Type'} (_98383 : nat) : (term140 A B _98383) = (term145 A B _98383).
Proof. exact (MK_COMB (@lem7637071 A B _98383) (@lem7637072 A B _98383)). Qed.
Lemma lem7637074 {A B : Type'} (_98383 : nat) : (term72 A B _98383) = (term145 A B _98383).
Proof. exact (TRANS (@lem7637066 A B _98383) (@lem7637073 A B _98383)). Qed.
Lemma lem7637077 {A B : Type'} (_98383 : nat) (h1 : term4 A B) : term145 A B _98383.
Proof. exact (EQ_MP (@lem7637074 A B _98383) (@lem7636685 A B _98383 h1)). Qed.
Lemma lem7637078 {A B : Type'} (x : finite_sum A B) (h1 : term4 A B) : term146 A B x.
Proof. exact (@lem7637077 A B (@dest_finite_sum A B x) h1). Qed.
Lemma lem7637081 {A B : Type'} (x : finite_sum A B) (h1 : term4 A B) : term147 A B x.
Proof. exact (@lem7637078 A B x h1 (@lem7637063 A B x h1)). Qed.
Lemma lem7637082 {A B : Type'} (x : finite_sum A B) (h1 : term4 A B) : term147 A B x.
Proof. exact (@lem7637081 A B x h1). Qed.
Lemma lem7637083 {A B : Type'} (x : finite_sum A B) (h1 : term4 A B) : term148 A B x.
Proof. exact (fun h0 : term149 A B x => @lem7637082 A B x h1). Qed.
Lemma lem7637085 (p : Prop) : (term99 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7637086 {A B : Type'} (x : finite_sum A B) : (term148 A B x) = (term147 A B x).
Proof. exact (@lem7637085 (term147 A B x)). Qed.
Lemma lem7637087 {A B : Type'} (x : finite_sum A B) (h1 : term4 A B) : term147 A B x.
Proof. exact (EQ_MP (@lem7637086 A B x) (@lem7637083 A B x h1)). Qed.
Lemma lem7637089 (a : Prop) (b : Prop) : (term150 a b) = (term151 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem7637090 {A B : Type'} (x : finite_sum A B) (_98378 : nat) : (term41 A B x _98378) = (term40 A B x _98378).
Proof. exact (@lem7637089 (x = (@mk_finite_sum A B _98378)) (term28 A B _98378)). Qed.
Lemma lem7637092 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7637093 {A B : Type'} (x : finite_sum A B) (_98378 : nat) : (term40 A B x _98378) = (term152 A B x _98378).
Proof. exact (@lem7637092 (term36 A B x _98378)). Qed.
Lemma lem7637094 {A B : Type'} (x : finite_sum A B) (_98378 : nat) : (term41 A B x _98378) = (term152 A B x _98378).
Proof. exact (TRANS (@lem7637090 A B x _98378) (@lem7637093 A B x _98378)). Qed.
Lemma lem7637096 {A B : Type'} (x : finite_sum A B) (h1 : term4 A B) : term153 A B x.
Proof. exact (conj (@lem7636992 A B x h1) (@lem7637087 A B x h1)). Qed.
Lemma lem7637098 {A B : Type'} (_98378 : nat) (x : finite_sum A B) (h1 : term50 A B x) : term152 A B x _98378.
Proof. exact (EQ_MP (@lem7637094 A B x _98378) (@lem7636663 A B _98378 x h1)). Qed.
Lemma lem7637099 {A B : Type'} (x : finite_sum A B) (h1 : term50 A B x) : term154 A B x.
Proof. exact (@lem7637098 A B (@dest_finite_sum A B x) x h1). Qed.
Lemma lem7637102 {A B : Type'} (x : finite_sum A B) (h1 : term50 A B x) (h2 : term4 A B) : False.
Proof. exact (@lem7637099 A B x h1 (@lem7637096 A B x h2)). Qed.
Lemma lem7637103 {A B : Type'} (x : finite_sum A B) (h1 : term50 A B x) (h2 : term4 A B) : term155.
Proof. exact (fun h0 : ~ False => @lem7637102 A B x h1 h2). Qed.
Lemma lem7637105 (p : Prop) : (term99 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7637106 : term155 = False.
Proof. exact (@lem7637105 False). Qed.
Lemma lem7637107 {A B : Type'} (x : finite_sum A B) (h1 : term50 A B x) (h2 : term4 A B) : False.
Proof. exact (EQ_MP (@lem7637106) (@lem7637103 A B x h1 h2)). Qed.
Lemma lem7637108 {A B : Type'} (x : finite_sum A B) (h1 : term50 A B x) (h2 : term4 A B) : (term50 A B x) = False.
Proof. exact (prop_ext (fun h3 : term50 A B x => @lem7637107 A B x h1 h2) (fun h3 : False => @lem7636528 A B x h1)). Qed.
Lemma lem7637109 {A B : Type'} (x : finite_sum A B) (h1 : term50 A B x) (h2 : term4 A B) : False.
Proof. exact (EQ_MP (@lem7637108 A B x h1 h2) (@lem7636528 A B x h1)). Qed.
Lemma lem7637110 {A B : Type'} (x : finite_sum A B) (h1 : term50 A B x) (h2 : term4 A B) : (term50 A B x) = False.
Proof. exact (prop_ext (fun h3 : term50 A B x => @lem7637109 A B x h1 h2) (fun h3 : False => @lem7636503 A B x h1)). Qed.
Lemma lem7637111 {A B : Type'} (x : finite_sum A B) (h1 : term50 A B x) (h2 : term4 A B) : False.
Proof. exact (EQ_MP (@lem7637110 A B x h1 h2) (@lem7636503 A B x h1)). Qed.
Lemma lem7637112 {A B : Type'} (h1 : term3 A B) (h2 : term4 A B) : False.
Proof. exact (ex_elim (@lem7635704 A B h1) (fun x : finite_sum A B => fun h0 : term57 A B x => @lem7637111 A B x h0 h2)). Qed.
Lemma lem7637113 {A B : Type'} (h1 : term3 A B) (h2 : term4 A B) : term10 B.
Proof. exact (fun h0 : term5 B => @lem7637112 A B h1 h2). Qed.
Lemma lem7637114 {B : Type'} : (term10 B) = (term11 B).
Proof. exact (@lem69 (term5 B)). Qed.
Lemma lem7637115 {A B : Type'} (h1 : term3 A B) (h2 : term4 A B) : term11 B.
Proof. exact (EQ_MP (@lem7637114 B) (@lem7637113 A B h1 h2)). Qed.
Lemma lem7637116 {A B : Type'} (h1 : term3 A B) : term14 A B.
Proof. exact (fun h0 : term4 A B => @lem7637115 A B h1 h0). Qed.
Lemma lem7637117 {A B : Type'} (h1 : term3 A B) : term17 A B.
Proof. exact (fun h0 : term5 A => @lem7637116 A B h1). Qed.
Lemma lem7637118 {A B : Type'} : term19 A B.
Proof. exact (fun h0 : term3 A B => @lem7637117 A B h0). Qed.
Lemma lem7637119 {A B : Type'} : term6 A B.
Proof. exact (EQ_MP (@lem7635616 A B) (@lem7637118 A B)). Qed.
Lemma lem7637121 {A B : Type'} : term6 A B.
Proof. exact (@lem7635372 A B (@lem7637119 A B)). Qed.
Lemma lem7637122 {A B : Type'} (h1 : term3 A B) : term16 A B.
Proof. exact (@lem7637121 A B (@lem7635346 A B h1)). Qed.
Lemma lem7637123 {A B : Type'} (h1 : term3 A B) : term13 A B.
Proof. exact (@lem7637122 A B h1 (@lem7635353 A)). Qed.
Lemma lem7637124 {A B : Type'} (h1 : term3 A B) : term10 B.
Proof. exact (@lem7637123 A B h1 (@lem7635347 A B)). Qed.
Lemma lem7637125 {A B : Type'} (h1 : term3 A B) : False.
Proof. exact (@lem7637124 A B h1 (@lem7635350 B)). Qed.
Lemma lem7637126 {A B : Type'} (h1 : term3 A B) : (term3 A B) = False.
Proof. exact (prop_ext (fun h2 : term3 A B => @lem7637125 A B h1) (fun h2 : False => @lem7635346 A B h1)). Qed.
Lemma lem7637127 {A B : Type'} (h1 : term3 A B) : False.
Proof. exact (EQ_MP (@lem7637126 A B h1) (@lem7635346 A B h1)). Qed.
Lemma lem7637128 {A B : Type'} : term2 A B.
Proof. exact (fun h0 : term3 A B => @lem7637127 A B h0). Qed.
Lemma lem7637129 {A B : Type'} : term1 A B.
Proof. exact (EQ_MP (@lem7635345 A B) (@lem7637128 A B)). Qed.
