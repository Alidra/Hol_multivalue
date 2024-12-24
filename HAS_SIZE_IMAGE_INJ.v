Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import HAS_SIZE_IMAGE_INJ_term_abbrevs.
Require Import CARD_IMAGE_INJ_spec.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import FINITE_IMAGE_spec.
Require Import HAS_SIZE_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm1842_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm19699_spec.
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
Require Import thm4211_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Lemma lem3996359 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem3996360 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem3996361 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem3996360 t1) (@lem3996359 t1)). Qed.
Lemma lem3996362 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem3996361 t1 t2). Qed.
Lemma lem3996363 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem3996364 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem3996363 t1 t2) (@lem3996362 t1 t2)). Qed.
Lemma lem3996365 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem3996364 t1 t2 t3). Qed.
Lemma lem3996366 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem3996367 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem3996366 t1 t2 t3) (@lem3996365 t1 t2 t3)). Qed.
Lemma lem3996368 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem3996367 t1 t2 t3)). Qed.
Lemma lem3996369 {A B : Type'} (f : A -> B) : term7 A B f.
Proof. exact (@lem3615104 A B f). Qed.
Lemma lem3996370 {A B : Type'} (f : A -> B) : (term7 A B f) = (term8 A B f).
Proof. exact (eq_refl (term7 A B f)). Qed.
Lemma lem3996371 {A B : Type'} (f : A -> B) : term8 A B f.
Proof. exact (EQ_MP (@lem3996370 A B f) (@lem3996369 A B f)). Qed.
Lemma lem3996372 {A B : Type'} (f : A -> B) (s : A -> Prop) : term9 A B f s.
Proof. exact (@lem3996371 A B f s). Qed.
Lemma lem3996373 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term9 A B f s) = (term10 A B f s).
Proof. exact (eq_refl (term9 A B f s)). Qed.
Lemma lem3996374 {A B : Type'} (f : A -> B) (s : A -> Prop) : term10 A B f s.
Proof. exact (EQ_MP (@lem3996373 A B f s) (@lem3996372 A B f s)). Qed.
Lemma lem3996375 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem3996376 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : term11 A B f s.
Proof. exact (@lem3996374 A B f s (@lem3996375 A s h1)). Qed.
Lemma lem3996377 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term11 A B f s) = ((term11 A B f s) = True).
Proof. exact (@lem7 (term11 A B f s)). Qed.
Lemma lem3996378 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : (term11 A B f s) = True.
Proof. exact (EQ_MP (@lem3996377 A B f s) (@lem3996376 A B f s h1)). Qed.
Lemma lem3996384 {_100044 : Type'} (s : _100044 -> Prop) : term12 _100044 s.
Proof. exact (@lem3863773 _100044 s). Qed.
Lemma lem3996385 {_100044 : Type'} (s : _100044 -> Prop) : (term12 _100044 s) = (term13 _100044 s).
Proof. exact (eq_refl (term12 _100044 s)). Qed.
Lemma lem3996386 {_100044 : Type'} (s : _100044 -> Prop) : term13 _100044 s.
Proof. exact (EQ_MP (@lem3996385 _100044 s) (@lem3996384 _100044 s)). Qed.
Lemma lem3996387 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : term14 _100044 s n.
Proof. exact (@lem3996386 _100044 s n). Qed.
Lemma lem3996388 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (term14 _100044 s n) = ((@HAS_SIZE _100044 s n) = (term15 _100044 s n)).
Proof. exact (eq_refl (term14 _100044 s n)). Qed.
Lemma lem3996405 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term16 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem3996406 (p : Prop) (q : Prop) (p' : Prop) : term17 p q p'.
Proof. exact (fun q' : Prop => @lem3996405 p q p' q'). Qed.
Lemma lem3996407 (p : Prop) (q : Prop) : term18 p q.
Proof. exact (fun p' : Prop => @lem3996406 p q p'). Qed.
Lemma lem3996408 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : term19 A B f s n.
Proof. exact (@lem3996407 (term20 A B f s n) (term21 A B f s n)). Qed.
Lemma lem3996409 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (p' : Prop) : term22 A B f s n p'.
Proof. exact (@lem3996408 A B f s n p'). Qed.
Lemma lem3996410 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (p' : Prop) : (term22 A B f s n p') = (term23 A B f s n p').
Proof. exact (eq_refl (term22 A B f s n p')). Qed.
Lemma lem3996411 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (p' : Prop) : term23 A B f s n p'.
Proof. exact (EQ_MP (@lem3996410 A B f s n p') (@lem3996409 A B f s n p')). Qed.
Lemma lem3996412 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (p' : Prop) (q' : Prop) : term24 A B f s n p' q'.
Proof. exact (@lem3996411 A B f s n p' q'). Qed.
Lemma lem3996413 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (p' : Prop) (q' : Prop) : (term24 A B f s n p' q') = (term25 A B f s n p' q').
Proof. exact (eq_refl (term24 A B f s n p' q')). Qed.
Lemma lem3996414 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (p' : Prop) (q' : Prop) : term25 A B f s n p' q'.
Proof. exact (EQ_MP (@lem3996413 A B f s n p' q') (@lem3996412 A B f s n p' q')). Qed.
Lemma lem3996471 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (@HAS_SIZE _100044 s n) = (term15 _100044 s n).
Proof. exact (EQ_MP (@lem3996388 _100044 s n) (@lem3996387 _100044 s n)). Qed.
Lemma lem3996472 {A : Type'} (s : A -> Prop) (n : nat) : (@HAS_SIZE A s n) = (term15 A s n).
Proof. exact (@lem3996471 A s n). Qed.
Lemma lem3996477 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term26 A B s f) = (term26 A B s f).
Proof. exact (eq_refl (term26 A B s f)). Qed.
Lemma lem3996478 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term20 A B f s n) = (term27 A B f s n).
Proof. exact (MK_COMB (@lem3996477 A B s f) (@lem3996472 A s n)). Qed.
Lemma lem3996538 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (q' : Prop) : term28 A B f s n q'.
Proof. exact (@lem3996414 A B f s n (term27 A B f s n) q'). Qed.
Lemma lem3996539 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (q' : Prop) : term29 A B f s n q'.
Proof. exact (@lem3996538 A B f s n q' (@lem3996478 A B f s n)). Qed.
Lemma lem3996540 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term27 A B f s n) : term27 A B f s n.
Proof. exact (h1). Qed.
Lemma lem3996541 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term27 A B f s n) : term15 A s n.
Proof. exact (proj2 (@lem3996540 A B f s n h1)). Qed.
Lemma lem3996543 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term27 A B f s n) : @FINITE A s.
Proof. exact (proj1 (@lem3996541 A B f s n h1)). Qed.
Lemma lem3996544 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem3996561 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (@HAS_SIZE _100044 s n) = (term15 _100044 s n).
Proof. exact (EQ_MP (@lem3996388 _100044 s n) (@lem3996387 _100044 s n)). Qed.
Lemma lem3996562 {B : Type'} (s : B -> Prop) (n : nat) : (@HAS_SIZE B s n) = (term15 B s n).
Proof. exact (@lem3996561 B s n). Qed.
Lemma lem3996563 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term21 A B f s n) = (term30 A B f s n).
Proof. exact (@lem3996562 B (@IMAGE A B f s) n). Qed.
Lemma lem3996579 {A B : Type'} (f : A -> B) (s : A -> Prop) : term31 A B f s.
Proof. exact (fun h0 : @FINITE A s => @lem3996378 A B f s h0). Qed.
Lemma lem3996580 {A B : Type'} (f : A -> B) (s : A -> Prop) : term31 A B f s.
Proof. exact (@lem3996579 A B f s). Qed.
Lemma lem3996582 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term27 A B f s n) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem3996544 A s) (@lem3996543 A B f s n h1)). Qed.
Lemma lem3996587 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term27 A B f s n) : True = (@FINITE A s).
Proof. exact (SYM (@lem3996582 A B f s n h1)). Qed.
Lemma lem3996588 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term27 A B f s n) : @FINITE A s.
Proof. exact (EQ_MP (@lem3996587 A B f s n h1) (@lem0)). Qed.
Lemma lem3996589 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term27 A B f s n) : (term11 A B f s) = True.
Proof. exact (@lem3996580 A B f s (@lem3996588 A B f s n h1)). Qed.
Lemma lem3996594 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3996595 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term27 A B f s n) : (term32 A B f s) = (and True).
Proof. exact (MK_COMB (@lem3996594) (@lem3996589 A B f s n h1)). Qed.
Lemma lem3996654 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : ((term33 A B f s) = n) = ((term33 A B f s) = n).
Proof. exact (eq_refl ((term33 A B f s) = n)). Qed.
Lemma lem3996655 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term27 A B f s n) : (term30 A B f s n) = (term34 A B f s n).
Proof. exact (MK_COMB (@lem3996595 A B f s n h1) (@lem3996654 A B f s n)). Qed.
Lemma lem3996657 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3996658 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term34 A B f s n) = ((term33 A B f s) = n).
Proof. exact (@lem3996657 ((term33 A B f s) = n)). Qed.
Lemma lem3996705 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term27 A B f s n) : (term30 A B f s n) = ((term33 A B f s) = n).
Proof. exact (TRANS (@lem3996655 A B f s n h1) (@lem3996658 A B f s n)). Qed.
Lemma lem3996706 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term27 A B f s n) : (term21 A B f s n) = ((term33 A B f s) = n).
Proof. exact (TRANS (@lem3996563 A B f s n) (@lem3996705 A B f s n h1)). Qed.
Lemma lem3996707 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : term35 A B f s n.
Proof. exact (fun h0 : term27 A B f s n => @lem3996706 A B f s n h0). Qed.
Lemma lem3996708 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : term36 A B f s n.
Proof. exact (@lem3996539 A B f s n ((term33 A B f s) = n)). Qed.
Lemma lem3996709 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term37 A B f s n) = (term38 A B f s n).
Proof. exact (@lem3996708 A B f s n (@lem3996707 A B f s n)). Qed.
Lemma lem3996916 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term39 A B f s) = (term40 A B f s).
Proof. exact (fun_ext (fun n : nat => @lem3996709 A B f s n)). Qed.
Lemma lem3997123 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3997124 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term41 A B f s) = (term42 A B f s).
Proof. exact (MK_COMB (@lem3997123) (@lem3996916 A B f s)). Qed.
Lemma lem3997335 {A B : Type'} (f : A -> B) : (term43 A B f) = (term44 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3997124 A B f s)). Qed.
Lemma lem3997546 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3997547 {A B : Type'} (f : A -> B) : (term45 A B f) = (term46 A B f).
Proof. exact (MK_COMB (@lem3997546 A) (@lem3997335 A B f)). Qed.
Lemma lem3997762 {A B : Type'} : (term47 A B) = (term48 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3997547 A B f)). Qed.
Lemma lem3997977 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3997978 {A B : Type'} : (term49 A B) = (term50 A B).
Proof. exact (MK_COMB (@lem3997977 A B) (@lem3997762 A B)). Qed.
Lemma lem3998197 {A B : Type'} : (term50 A B) = (term49 A B).
Proof. exact (SYM (@lem3997978 A B)). Qed.
Lemma lem3998199 (p : Prop) : p = (term51 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3998200 {A B : Type'} : (term50 A B) = (term52 A B).
Proof. exact (@lem3998199 (term50 A B)). Qed.
Lemma lem3998201 {A B : Type'} : (term52 A B) = (term50 A B).
Proof. exact (SYM (@lem3998200 A B)). Qed.
Lemma lem3998202 {A B : Type'} (h1 : term53 A B) : term53 A B.
Proof. exact (h1). Qed.
Lemma lem3998203 {A B : Type'} : term54 A B.
Proof. exact (@lem3996358 A B). Qed.
Lemma lem3998205 {A : Type'} : term55 A.
Proof. exact (@lem3996358 A A). Qed.
Lemma lem3998206 {A : Type'} : term56 A.
Proof. exact (@lem3996358 A nat). Qed.
Lemma lem3998207 {B : Type'} : term55 B.
Proof. exact (@lem3996358 B B). Qed.
Lemma lem3998209 {B : Type'} : term57 B.
Proof. exact (@lem3996358 nat B). Qed.
Lemma lem3998218 {A B : Type'} (h1 : term58 A B) : term58 A B.
Proof. exact (h1). Qed.
Lemma lem3998219 {A B : Type'} : term59 A B.
Proof. exact (fun h0 : term58 A B => @lem3998218 A B h0). Qed.
Lemma lem3998220 {A B : Type'} (h1 : term59 A B) : term59 A B.
Proof. exact (h1). Qed.
Lemma lem3998221 {A B : Type'} (h1 : term58 A B) : term58 A B.
Proof. exact (h1). Qed.
Lemma lem3998222 {A B : Type'} (h1 : term58 A B) (h2 : term59 A B) : term58 A B.
Proof. exact (@lem3998220 A B h2 (@lem3998221 A B h1)). Qed.
Lemma lem3998223 {A B : Type'} (h1 : term58 A B) : term60 A B.
Proof. exact (fun h0 : term59 A B => @lem3998222 A B h1 h0). Qed.
Lemma lem3998224 {A B : Type'} (h1 : term59 A B) : term59 A B.
Proof. exact (h1). Qed.
Lemma lem3998225 {A B : Type'} (h1 : term58 A B) (h2 : term59 A B) : term58 A B.
Proof. exact (@lem3998223 A B h1 (@lem3998224 A B h2)). Qed.
Lemma lem3998226 {A B : Type'} (h1 : term59 A B) : term59 A B.
Proof. exact (fun h0 : term58 A B => @lem3998225 A B h0 h1). Qed.
Lemma lem3998227 {A B : Type'} : term61 A B.
Proof. exact (fun h0 : term59 A B => @lem3998226 A B h0). Qed.
Lemma lem3998230 {A B : Type'} : term59 A B.
Proof. exact (@lem3998227 A B (@lem3998219 A B)). Qed.
Lemma lem3998231 {A B : Type'} : term59 A B.
Proof. exact (@lem3998230 A B). Qed.
Lemma lem3998379 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3998380 {B : Type'} : (term62 B) = (term63 B).
Proof. exact (@lem3998379 (term57 B)). Qed.
Lemma lem3998407 {B : Type'} : (term64 B) = (term64 B).
Proof. exact (eq_refl (term64 B)). Qed.
Lemma lem3998408 {B : Type'} : (term65 B) = (term66 B).
Proof. exact (MK_COMB (@lem3998407 B) (@lem3998380 B)). Qed.
Lemma lem3998411 {A : Type'} : (term67 A) = (term67 A).
Proof. exact (eq_refl (term67 A)). Qed.
Lemma lem3998412 {A B : Type'} : (term68 A B) = (term69 A B).
Proof. exact (MK_COMB (@lem3998411 A) (@lem3998408 B)). Qed.
Lemma lem3998415 {A B : Type'} : (term70 A B) = (term70 A B).
Proof. exact (eq_refl (term70 A B)). Qed.
Lemma lem3998416 {A B : Type'} : (term71 A B) = (term72 A B).
Proof. exact (MK_COMB (@lem3998415 A B) (@lem3998412 A B)). Qed.
Lemma lem3998419 {A : Type'} : (term64 A) = (term64 A).
Proof. exact (eq_refl (term64 A)). Qed.
Lemma lem3998420 {A B : Type'} : (term73 A B) = (term74 A B).
Proof. exact (MK_COMB (@lem3998419 A) (@lem3998416 A B)). Qed.
Lemma lem3998423 {A B : Type'} : (term75 A B) = (term75 A B).
Proof. exact (eq_refl (term75 A B)). Qed.
Lemma lem3998430 {A B : Type'} : (term58 A B) = (term76 A B).
Proof. exact (MK_COMB (@lem3998423 A B) (@lem3998420 A B)). Qed.
Lemma lem3998431 {B : Type'} (f : nat -> B) (s : nat -> Prop) : ((term77 B f s) = (@CARD nat s)) = ((term77 B f s) = (@CARD nat s)).
Proof. exact (eq_refl ((term77 B f s) = (@CARD nat s))). Qed.
Lemma lem3998432 (s : nat -> Prop) : (@FINITE nat s) = (@FINITE nat s).
Proof. exact (eq_refl (@FINITE nat s)). Qed.
Lemma lem3998445 {B : Type'} (s : nat -> Prop) (f : nat -> B) (x : nat) (y : nat) : (term78 B s f x y) = (term78 B s f x y).
Proof. exact (eq_refl (term78 B s f x y)). Qed.
Lemma lem3998446 {B : Type'} (s : nat -> Prop) (f : nat -> B) (x : nat) : (term79 B s f x) = (term79 B s f x).
Proof. exact (fun_ext (fun y : nat => @lem3998445 B s f x y)). Qed.
Lemma lem3998447 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3998448 {B : Type'} (s : nat -> Prop) (f : nat -> B) (x : nat) : (term80 B s f x) = (term80 B s f x).
Proof. exact (MK_COMB (@lem3998447) (@lem3998446 B s f x)). Qed.
Lemma lem3998449 {B : Type'} (s : nat -> Prop) (f : nat -> B) : (term81 B s f) = (term81 B s f).
Proof. exact (fun_ext (fun x : nat => @lem3998448 B s f x)). Qed.
Lemma lem3998450 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3998451 {B : Type'} (s : nat -> Prop) (f : nat -> B) : (term82 B s f) = (term82 B s f).
Proof. exact (MK_COMB (@lem3998450) (@lem3998449 B s f)). Qed.
Lemma lem3998452 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3998453 {B : Type'} (s : nat -> Prop) (f : nat -> B) : (term83 B s f) = (term83 B s f).
Proof. exact (MK_COMB (@lem3998452) (@lem3998451 B s f)). Qed.
Lemma lem3998454 {B : Type'} (f : nat -> B) (s : nat -> Prop) : (term84 B f s) = (term84 B f s).
Proof. exact (MK_COMB (@lem3998453 B s f) (@lem3998432 s)). Qed.
Lemma lem3998455 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3998456 {B : Type'} (f : nat -> B) (s : nat -> Prop) : (term85 B f s) = (term85 B f s).
Proof. exact (MK_COMB (@lem3998455) (@lem3998454 B f s)). Qed.
Lemma lem3998457 {B : Type'} (f : nat -> B) (s : nat -> Prop) : (term86 B f s) = (term86 B f s).
Proof. exact (MK_COMB (@lem3998456 B f s) (@lem3998431 B f s)). Qed.
Lemma lem3998458 {B : Type'} (f : nat -> B) : (term87 B f) = (term87 B f).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem3998457 B f s)). Qed.
Lemma lem3998459 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem3998460 {B : Type'} (f : nat -> B) : (term88 B f) = (term88 B f).
Proof. exact (MK_COMB (@lem3998459) (@lem3998458 B f)). Qed.
Lemma lem3998461 {B : Type'} : (term89 B) = (term89 B).
Proof. exact (fun_ext (fun f : nat -> B => @lem3998460 B f)). Qed.
Lemma lem3998462 {B : Type'} : (@all (nat -> B)) = (@all (nat -> B)).
Proof. exact (eq_refl (@all (nat -> B))). Qed.
Lemma lem3998463 {B : Type'} : (term57 B) = (term57 B).
Proof. exact (MK_COMB (@lem3998462 B) (@lem3998461 B)). Qed.
Lemma lem3998464 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3998465 {B : Type'} : (term63 B) = (term63 B).
Proof. exact (MK_COMB (@lem3998464) (@lem3998463 B)). Qed.
Lemma lem3998466 {B : Type'} (f : B -> B) (s : B -> Prop) : ((term90 B f s) = (@CARD B s)) = ((term90 B f s) = (@CARD B s)).
Proof. exact (eq_refl ((term90 B f s) = (@CARD B s))). Qed.
Lemma lem3998467 {B : Type'} (s : B -> Prop) : (@FINITE B s) = (@FINITE B s).
Proof. exact (eq_refl (@FINITE B s)). Qed.
Lemma lem3998480 {B : Type'} (s : B -> Prop) (f : B -> B) (x : B) (y : B) : (term91 B s f x y) = (term91 B s f x y).
Proof. exact (eq_refl (term91 B s f x y)). Qed.
Lemma lem3998481 {B : Type'} (s : B -> Prop) (f : B -> B) (x : B) : (term92 B s f x) = (term92 B s f x).
Proof. exact (fun_ext (fun y : B => @lem3998480 B s f x y)). Qed.
Lemma lem3998482 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3998483 {B : Type'} (s : B -> Prop) (f : B -> B) (x : B) : (term93 B s f x) = (term93 B s f x).
Proof. exact (MK_COMB (@lem3998482 B) (@lem3998481 B s f x)). Qed.
Lemma lem3998484 {B : Type'} (s : B -> Prop) (f : B -> B) : (term94 B s f) = (term94 B s f).
Proof. exact (fun_ext (fun x : B => @lem3998483 B s f x)). Qed.
Lemma lem3998485 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3998486 {B : Type'} (s : B -> Prop) (f : B -> B) : (term95 B s f) = (term95 B s f).
Proof. exact (MK_COMB (@lem3998485 B) (@lem3998484 B s f)). Qed.
Lemma lem3998487 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3998488 {B : Type'} (s : B -> Prop) (f : B -> B) : (term96 B s f) = (term96 B s f).
Proof. exact (MK_COMB (@lem3998487) (@lem3998486 B s f)). Qed.
Lemma lem3998489 {B : Type'} (f : B -> B) (s : B -> Prop) : (term97 B f s) = (term97 B f s).
Proof. exact (MK_COMB (@lem3998488 B s f) (@lem3998467 B s)). Qed.
Lemma lem3998490 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3998491 {B : Type'} (f : B -> B) (s : B -> Prop) : (term98 B f s) = (term98 B f s).
Proof. exact (MK_COMB (@lem3998490) (@lem3998489 B f s)). Qed.
Lemma lem3998492 {B : Type'} (f : B -> B) (s : B -> Prop) : (term99 B f s) = (term99 B f s).
Proof. exact (MK_COMB (@lem3998491 B f s) (@lem3998466 B f s)). Qed.
Lemma lem3998493 {B : Type'} (f : B -> B) : (term100 B f) = (term100 B f).
Proof. exact (fun_ext (fun s : B -> Prop => @lem3998492 B f s)). Qed.
Lemma lem3998494 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3998495 {B : Type'} (f : B -> B) : (term101 B f) = (term101 B f).
Proof. exact (MK_COMB (@lem3998494 B) (@lem3998493 B f)). Qed.
Lemma lem3998496 {B : Type'} : (term102 B) = (term102 B).
Proof. exact (fun_ext (fun f : B -> B => @lem3998495 B f)). Qed.
Lemma lem3998497 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem3998498 {B : Type'} : (term55 B) = (term55 B).
Proof. exact (MK_COMB (@lem3998497 B) (@lem3998496 B)). Qed.
Lemma lem3998499 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3998500 {B : Type'} : (term64 B) = (term64 B).
Proof. exact (MK_COMB (@lem3998499) (@lem3998498 B)). Qed.
Lemma lem3998501 {B : Type'} : (term66 B) = (term66 B).
Proof. exact (MK_COMB (@lem3998500 B) (@lem3998465 B)). Qed.
Lemma lem3998502 {A : Type'} (f : A -> nat) (s : A -> Prop) : ((term103 A f s) = (@CARD A s)) = ((term103 A f s) = (@CARD A s)).
Proof. exact (eq_refl ((term103 A f s) = (@CARD A s))). Qed.
Lemma lem3998503 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem3998516 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (y : A) : (term104 A s f x y) = (term104 A s f x y).
Proof. exact (eq_refl (term104 A s f x y)). Qed.
Lemma lem3998517 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : (term105 A s f x) = (term105 A s f x).
Proof. exact (fun_ext (fun y : A => @lem3998516 A s f x y)). Qed.
Lemma lem3998518 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3998519 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : (term106 A s f x) = (term106 A s f x).
Proof. exact (MK_COMB (@lem3998518 A) (@lem3998517 A s f x)). Qed.
Lemma lem3998520 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term107 A s f) = (term107 A s f).
Proof. exact (fun_ext (fun x : A => @lem3998519 A s f x)). Qed.
Lemma lem3998521 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3998522 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term108 A s f) = (term108 A s f).
Proof. exact (MK_COMB (@lem3998521 A) (@lem3998520 A s f)). Qed.
Lemma lem3998523 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3998524 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term109 A s f) = (term109 A s f).
Proof. exact (MK_COMB (@lem3998523) (@lem3998522 A s f)). Qed.
Lemma lem3998525 {A : Type'} (f : A -> nat) (s : A -> Prop) : (term110 A f s) = (term110 A f s).
Proof. exact (MK_COMB (@lem3998524 A s f) (@lem3998503 A s)). Qed.
Lemma lem3998526 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3998527 {A : Type'} (f : A -> nat) (s : A -> Prop) : (term111 A f s) = (term111 A f s).
Proof. exact (MK_COMB (@lem3998526) (@lem3998525 A f s)). Qed.
Lemma lem3998528 {A : Type'} (f : A -> nat) (s : A -> Prop) : (term112 A f s) = (term112 A f s).
Proof. exact (MK_COMB (@lem3998527 A f s) (@lem3998502 A f s)). Qed.
Lemma lem3998529 {A : Type'} (f : A -> nat) : (term113 A f) = (term113 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3998528 A f s)). Qed.
Lemma lem3998530 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3998531 {A : Type'} (f : A -> nat) : (term114 A f) = (term114 A f).
Proof. exact (MK_COMB (@lem3998530 A) (@lem3998529 A f)). Qed.
Lemma lem3998532 {A : Type'} : (term115 A) = (term115 A).
Proof. exact (fun_ext (fun f : A -> nat => @lem3998531 A f)). Qed.
Lemma lem3998533 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem3998534 {A : Type'} : (term56 A) = (term56 A).
Proof. exact (MK_COMB (@lem3998533 A) (@lem3998532 A)). Qed.
Lemma lem3998535 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3998536 {A : Type'} : (term67 A) = (term67 A).
Proof. exact (MK_COMB (@lem3998535) (@lem3998534 A)). Qed.
Lemma lem3998537 {A B : Type'} : (term69 A B) = (term69 A B).
Proof. exact (MK_COMB (@lem3998536 A) (@lem3998501 B)). Qed.
Lemma lem3998538 {A B : Type'} (f : A -> B) (s : A -> Prop) : ((term33 A B f s) = (@CARD A s)) = ((term33 A B f s) = (@CARD A s)).
Proof. exact (eq_refl ((term33 A B f s) = (@CARD A s))). Qed.
Lemma lem3998539 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem3998552 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term116 A B s f x y) = (term116 A B s f x y).
Proof. exact (eq_refl (term116 A B s f x y)). Qed.
Lemma lem3998553 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term117 A B s f x) = (term117 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem3998552 A B s f x y)). Qed.
Lemma lem3998554 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3998555 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term118 A B s f x) = (term118 A B s f x).
Proof. exact (MK_COMB (@lem3998554 A) (@lem3998553 A B s f x)). Qed.
Lemma lem3998556 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term119 A B s f) = (term119 A B s f).
Proof. exact (fun_ext (fun x : A => @lem3998555 A B s f x)). Qed.
Lemma lem3998557 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3998558 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term120 A B s f) = (term120 A B s f).
Proof. exact (MK_COMB (@lem3998557 A) (@lem3998556 A B s f)). Qed.
Lemma lem3998559 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3998560 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term26 A B s f) = (term26 A B s f).
Proof. exact (MK_COMB (@lem3998559) (@lem3998558 A B s f)). Qed.
Lemma lem3998561 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term121 A B f s) = (term121 A B f s).
Proof. exact (MK_COMB (@lem3998560 A B s f) (@lem3998539 A s)). Qed.
Lemma lem3998562 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3998563 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term122 A B f s) = (term122 A B f s).
Proof. exact (MK_COMB (@lem3998562) (@lem3998561 A B f s)). Qed.
Lemma lem3998564 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term123 A B f s) = (term123 A B f s).
Proof. exact (MK_COMB (@lem3998563 A B f s) (@lem3998538 A B f s)). Qed.
Lemma lem3998565 {A B : Type'} (f : A -> B) : (term124 A B f) = (term124 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3998564 A B f s)). Qed.
Lemma lem3998566 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3998567 {A B : Type'} (f : A -> B) : (term125 A B f) = (term125 A B f).
Proof. exact (MK_COMB (@lem3998566 A) (@lem3998565 A B f)). Qed.
Lemma lem3998568 {A B : Type'} : (term126 A B) = (term126 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3998567 A B f)). Qed.
Lemma lem3998569 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3998570 {A B : Type'} : (term54 A B) = (term54 A B).
Proof. exact (MK_COMB (@lem3998569 A B) (@lem3998568 A B)). Qed.
Lemma lem3998571 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3998572 {A B : Type'} : (term70 A B) = (term70 A B).
Proof. exact (MK_COMB (@lem3998571) (@lem3998570 A B)). Qed.
Lemma lem3998573 {A B : Type'} : (term72 A B) = (term72 A B).
Proof. exact (MK_COMB (@lem3998572 A B) (@lem3998537 A B)). Qed.
Lemma lem3998574 {A : Type'} (f : A -> A) (s : A -> Prop) : ((term90 A f s) = (@CARD A s)) = ((term90 A f s) = (@CARD A s)).
Proof. exact (eq_refl ((term90 A f s) = (@CARD A s))). Qed.
Lemma lem3998575 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem3998588 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (y : A) : (term91 A s f x y) = (term91 A s f x y).
Proof. exact (eq_refl (term91 A s f x y)). Qed.
Lemma lem3998589 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term92 A s f x) = (term92 A s f x).
Proof. exact (fun_ext (fun y : A => @lem3998588 A s f x y)). Qed.
Lemma lem3998590 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3998591 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term93 A s f x) = (term93 A s f x).
Proof. exact (MK_COMB (@lem3998590 A) (@lem3998589 A s f x)). Qed.
Lemma lem3998592 {A : Type'} (s : A -> Prop) (f : A -> A) : (term94 A s f) = (term94 A s f).
Proof. exact (fun_ext (fun x : A => @lem3998591 A s f x)). Qed.
Lemma lem3998593 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3998594 {A : Type'} (s : A -> Prop) (f : A -> A) : (term95 A s f) = (term95 A s f).
Proof. exact (MK_COMB (@lem3998593 A) (@lem3998592 A s f)). Qed.
Lemma lem3998595 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3998596 {A : Type'} (s : A -> Prop) (f : A -> A) : (term96 A s f) = (term96 A s f).
Proof. exact (MK_COMB (@lem3998595) (@lem3998594 A s f)). Qed.
Lemma lem3998597 {A : Type'} (f : A -> A) (s : A -> Prop) : (term97 A f s) = (term97 A f s).
Proof. exact (MK_COMB (@lem3998596 A s f) (@lem3998575 A s)). Qed.
Lemma lem3998598 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3998599 {A : Type'} (f : A -> A) (s : A -> Prop) : (term98 A f s) = (term98 A f s).
Proof. exact (MK_COMB (@lem3998598) (@lem3998597 A f s)). Qed.
Lemma lem3998600 {A : Type'} (f : A -> A) (s : A -> Prop) : (term99 A f s) = (term99 A f s).
Proof. exact (MK_COMB (@lem3998599 A f s) (@lem3998574 A f s)). Qed.
Lemma lem3998601 {A : Type'} (f : A -> A) : (term100 A f) = (term100 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3998600 A f s)). Qed.
Lemma lem3998602 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3998603 {A : Type'} (f : A -> A) : (term101 A f) = (term101 A f).
Proof. exact (MK_COMB (@lem3998602 A) (@lem3998601 A f)). Qed.
Lemma lem3998604 {A : Type'} : (term102 A) = (term102 A).
Proof. exact (fun_ext (fun f : A -> A => @lem3998603 A f)). Qed.
Lemma lem3998605 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem3998606 {A : Type'} : (term55 A) = (term55 A).
Proof. exact (MK_COMB (@lem3998605 A) (@lem3998604 A)). Qed.
Lemma lem3998607 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3998608 {A : Type'} : (term64 A) = (term64 A).
Proof. exact (MK_COMB (@lem3998607) (@lem3998606 A)). Qed.
Lemma lem3998609 {A B : Type'} : (term74 A B) = (term74 A B).
Proof. exact (MK_COMB (@lem3998608 A) (@lem3998573 A B)). Qed.
Lemma lem3998610 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : ((term33 A B f s) = n) = ((term33 A B f s) = n).
Proof. exact (eq_refl ((term33 A B f s) = n)). Qed.
Lemma lem3998615 {A : Type'} (s : A -> Prop) (n : nat) : (term15 A s n) = (term15 A s n).
Proof. exact (eq_refl (term15 A s n)). Qed.
Lemma lem3998628 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term116 A B s f x y) = (term116 A B s f x y).
Proof. exact (eq_refl (term116 A B s f x y)). Qed.
Lemma lem3998629 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term117 A B s f x) = (term117 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem3998628 A B s f x y)). Qed.
Lemma lem3998630 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3998631 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term118 A B s f x) = (term118 A B s f x).
Proof. exact (MK_COMB (@lem3998630 A) (@lem3998629 A B s f x)). Qed.
Lemma lem3998632 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term119 A B s f) = (term119 A B s f).
Proof. exact (fun_ext (fun x : A => @lem3998631 A B s f x)). Qed.
Lemma lem3998633 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3998634 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term120 A B s f) = (term120 A B s f).
Proof. exact (MK_COMB (@lem3998633 A) (@lem3998632 A B s f)). Qed.
Lemma lem3998635 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3998636 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term26 A B s f) = (term26 A B s f).
Proof. exact (MK_COMB (@lem3998635) (@lem3998634 A B s f)). Qed.
Lemma lem3998637 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term27 A B f s n) = (term27 A B f s n).
Proof. exact (MK_COMB (@lem3998636 A B s f) (@lem3998615 A s n)). Qed.
Lemma lem3998638 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3998639 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term127 A B f s n) = (term127 A B f s n).
Proof. exact (MK_COMB (@lem3998638) (@lem3998637 A B f s n)). Qed.
Lemma lem3998640 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term38 A B f s n) = (term38 A B f s n).
Proof. exact (MK_COMB (@lem3998639 A B f s n) (@lem3998610 A B f s n)). Qed.
Lemma lem3998641 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term40 A B f s) = (term40 A B f s).
Proof. exact (fun_ext (fun n : nat => @lem3998640 A B f s n)). Qed.
Lemma lem3998642 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3998643 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term42 A B f s) = (term42 A B f s).
Proof. exact (MK_COMB (@lem3998642) (@lem3998641 A B f s)). Qed.
Lemma lem3998644 {A B : Type'} (f : A -> B) : (term44 A B f) = (term44 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3998643 A B f s)). Qed.
Lemma lem3998645 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3998646 {A B : Type'} (f : A -> B) : (term46 A B f) = (term46 A B f).
Proof. exact (MK_COMB (@lem3998645 A) (@lem3998644 A B f)). Qed.
Lemma lem3998647 {A B : Type'} : (term48 A B) = (term48 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3998646 A B f)). Qed.
Lemma lem3998648 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3998649 {A B : Type'} : (term50 A B) = (term50 A B).
Proof. exact (MK_COMB (@lem3998648 A B) (@lem3998647 A B)). Qed.
Lemma lem3998650 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3998651 {A B : Type'} : (term53 A B) = (term53 A B).
Proof. exact (MK_COMB (@lem3998650) (@lem3998649 A B)). Qed.
Lemma lem3998652 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3998653 {A B : Type'} : (term75 A B) = (term75 A B).
Proof. exact (MK_COMB (@lem3998652) (@lem3998651 A B)). Qed.
Lemma lem3998654 {A B : Type'} : (term76 A B) = (term76 A B).
Proof. exact (MK_COMB (@lem3998653 A B) (@lem3998609 A B)). Qed.
Lemma lem3998879 {A B : Type'} : (term58 A B) = (term76 A B).
Proof. exact (TRANS (@lem3998430 A B) (@lem3998654 A B)). Qed.
Lemma lem3998880 {A B : Type'} : (term76 A B) = (term58 A B).
Proof. exact (SYM (@lem3998879 A B)). Qed.
Lemma lem3998881 {A B : Type'} (h1 : term53 A B) : term53 A B.
Proof. exact (h1). Qed.
Lemma lem3998882 {A : Type'} (h1 : term55 A) : term55 A.
Proof. exact (h1). Qed.
Lemma lem3998883 {A B : Type'} (h1 : term54 A B) : term54 A B.
Proof. exact (h1). Qed.
Lemma lem3998884 {A : Type'} (h1 : term56 A) : term56 A.
Proof. exact (h1). Qed.
Lemma lem3998885 {B : Type'} (h1 : term55 B) : term55 B.
Proof. exact (h1). Qed.
Lemma lem3998886 {B : Type'} (h1 : term57 B) : term57 B.
Proof. exact (h1). Qed.
Lemma lem3998894 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term128 A B s x f y) = (term129 A B s x f y).
Proof. exact (@lem17045 (@IN A y s) ((f x) = (f y))). Qed.
Lemma lem3998896 {A : Type'} (x : A) (s : A -> Prop) : (term130 A x s) = (term130 A x s).
Proof. exact (eq_refl (term130 A x s)). Qed.
Lemma lem3998897 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term131 A B s x f y) = (term132 A B s x f y).
Proof. exact (MK_COMB (@lem3998896 A x s) (@lem3998894 A B s x f y)). Qed.
Lemma lem3998898 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term133 A B s x f y) = (term131 A B s x f y).
Proof. exact (@lem17045 (@IN A x s) (term134 A B s x f y)). Qed.
Lemma lem3998899 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term133 A B s x f y) = (term132 A B s x f y).
Proof. exact (TRANS (@lem3998898 A B s x f y) (@lem3998897 A B s x f y)). Qed.
Lemma lem3998900 {A : Type'} (x : A) (y : A) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem3998901 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3998902 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term135 A B s x f y) = (term136 A B s x f y).
Proof. exact (MK_COMB (@lem3998901) (@lem3998899 A B s x f y)). Qed.
Lemma lem3998903 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term137 A B s f x y) = (term138 A B s f x y).
Proof. exact (MK_COMB (@lem3998902 A B s x f y) (@lem3998900 A x y)). Qed.
Lemma lem3998904 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term116 A B s f x y) = (term137 A B s f x y).
Proof. exact (@lem17265 (term139 A B s x f y) (x = y)). Qed.
Lemma lem3998905 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term116 A B s f x y) = (term138 A B s f x y).
Proof. exact (TRANS (@lem3998904 A B s f x y) (@lem3998903 A B s f x y)). Qed.
Lemma lem3998906 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term117 A B s f x) = (term140 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem3998905 A B s f x y)). Qed.
Lemma lem3998907 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3998908 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term118 A B s f x) = (term141 A B s f x).
Proof. exact (MK_COMB (@lem3998907 A) (@lem3998906 A B s f x)). Qed.
Lemma lem3998909 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term119 A B s f) = (term142 A B s f).
Proof. exact (fun_ext (fun x : A => @lem3998908 A B s f x)). Qed.
Lemma lem3998910 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3998911 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term120 A B s f) = (term143 A B s f).
Proof. exact (MK_COMB (@lem3998910 A) (@lem3998909 A B s f)). Qed.
Lemma lem3998916 {A : Type'} (s : A -> Prop) (n : nat) : (term15 A s n) = (term15 A s n).
Proof. exact (eq_refl (term15 A s n)). Qed.
Lemma lem3998917 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3998918 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term26 A B s f) = (term144 A B s f).
Proof. exact (MK_COMB (@lem3998917) (@lem3998911 A B s f)). Qed.
Lemma lem3998919 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term27 A B f s n) = (term145 A B f s n).
Proof. exact (MK_COMB (@lem3998918 A B s f) (@lem3998916 A s n)). Qed.
Lemma lem3998920 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term146 A B f s n) = (term146 A B f s n).
Proof. exact (eq_refl (term146 A B f s n)). Qed.
Lemma lem3998921 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3998922 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term147 A B f s n) = (term148 A B f s n).
Proof. exact (MK_COMB (@lem3998921) (@lem3998919 A B f s n)). Qed.
Lemma lem3998923 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term149 A B f s n) = (term150 A B f s n).
Proof. exact (MK_COMB (@lem3998922 A B f s n) (@lem3998920 A B f s n)). Qed.
Lemma lem3998924 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term151 A B f s n) = (term149 A B f s n).
Proof. exact (@lem17362 (term27 A B f s n) ((term33 A B f s) = n)). Qed.
Lemma lem3998925 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term151 A B f s n) = (term150 A B f s n).
Proof. exact (TRANS (@lem3998924 A B f s n) (@lem3998923 A B f s n)). Qed.
Lemma lem3998926 (P : nat -> Prop) : (term152 P) = (term153 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem3998927 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term154 A B f s) = (term155 A B f s).
Proof. exact (@lem3998926 (term40 A B f s)). Qed.
Lemma lem3998928 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term156 A B f s n) = (term38 A B f s n).
Proof. exact (eq_refl (term156 A B f s n)). Qed.
Lemma lem3998929 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3998930 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term157 A B f s n) = (term151 A B f s n).
Proof. exact (MK_COMB (@lem3998929) (@lem3998928 A B f s n)). Qed.
Lemma lem3998931 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term157 A B f s n) = (term150 A B f s n).
Proof. exact (TRANS (@lem3998930 A B f s n) (@lem3998925 A B f s n)). Qed.
Lemma lem3998932 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term158 A B f s) = (term159 A B f s).
Proof. exact (fun_ext (fun n : nat => @lem3998931 A B f s n)). Qed.
Lemma lem3998933 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem3998934 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term155 A B f s) = (term160 A B f s).
Proof. exact (MK_COMB (@lem3998933) (@lem3998932 A B f s)). Qed.
Lemma lem3998935 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term154 A B f s) = (term160 A B f s).
Proof. exact (TRANS (@lem3998927 A B f s) (@lem3998934 A B f s)). Qed.
Lemma lem3998936 {A : Type'} (P : type686 A) : (term161 A P) = (term162 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem3998937 {A B : Type'} (f : A -> B) : (term163 A B f) = (term164 A B f).
Proof. exact (@lem3998936 A (term44 A B f)). Qed.
Lemma lem3998938 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term165 A B f s) = (term42 A B f s).
Proof. exact (eq_refl (term165 A B f s)). Qed.
Lemma lem3998939 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3998940 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term166 A B f s) = (term154 A B f s).
Proof. exact (MK_COMB (@lem3998939) (@lem3998938 A B f s)). Qed.
Lemma lem3998941 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term166 A B f s) = (term160 A B f s).
Proof. exact (TRANS (@lem3998940 A B f s) (@lem3998935 A B f s)). Qed.
Lemma lem3998942 {A B : Type'} (f : A -> B) : (term167 A B f) = (term168 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3998941 A B f s)). Qed.
Lemma lem3998943 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3998944 {A B : Type'} (f : A -> B) : (term164 A B f) = (term169 A B f).
Proof. exact (MK_COMB (@lem3998943 A) (@lem3998942 A B f)). Qed.
Lemma lem3998945 {A B : Type'} (f : A -> B) : (term163 A B f) = (term169 A B f).
Proof. exact (TRANS (@lem3998937 A B f) (@lem3998944 A B f)). Qed.
Lemma lem3998946 {A B : Type'} (P : type572 A B) : (term170 A B P) = (term171 A B P).
Proof. exact (@lem18392 (A -> B) P). Qed.
Lemma lem3998947 {A B : Type'} : (term53 A B) = (term172 A B).
Proof. exact (@lem3998946 A B (term48 A B)). Qed.
Lemma lem3998948 {A B : Type'} (f : A -> B) : (term173 A B f) = (term46 A B f).
Proof. exact (eq_refl (term173 A B f)). Qed.
Lemma lem3998949 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3998950 {A B : Type'} (f : A -> B) : (term174 A B f) = (term163 A B f).
Proof. exact (MK_COMB (@lem3998949) (@lem3998948 A B f)). Qed.
Lemma lem3998951 {A B : Type'} (f : A -> B) : (term174 A B f) = (term169 A B f).
Proof. exact (TRANS (@lem3998950 A B f) (@lem3998945 A B f)). Qed.
Lemma lem3998952 {A B : Type'} : (term175 A B) = (term176 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3998951 A B f)). Qed.
Lemma lem3998953 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem3998954 {A B : Type'} : (term172 A B) = (term177 A B).
Proof. exact (MK_COMB (@lem3998953 A B) (@lem3998952 A B)). Qed.
Lemma lem3999067 {A B : Type'} : (term53 A B) = (term177 A B).
Proof. exact (TRANS (@lem3998947 A B) (@lem3998954 A B)). Qed.
Lemma lem3999068 {A B : Type'} (h1 : term53 A B) : term177 A B.
Proof. exact (EQ_MP (@lem3999067 A B) (@lem3998881 A B h1)). Qed.
Lemma lem3999083 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (y : A) : (term178 A s f x y) = (term179 A s f x y).
Proof. exact (@lem17362 (term180 A s x f y) (x = y)). Qed.
Lemma lem3999084 {A : Type'} (P : A -> Prop) : (term181 A P) = (term182 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3999085 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term183 A s f x) = (term184 A s f x).
Proof. exact (@lem3999084 A (term92 A s f x)). Qed.
Lemma lem3999086 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (y : A) : (term185 A s f x y) = (term91 A s f x y).
Proof. exact (eq_refl (term185 A s f x y)). Qed.
Lemma lem3999087 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3999088 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (y : A) : (term186 A s f x y) = (term178 A s f x y).
Proof. exact (MK_COMB (@lem3999087) (@lem3999086 A s f x y)). Qed.
Lemma lem3999089 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (y : A) : (term186 A s f x y) = (term179 A s f x y).
Proof. exact (TRANS (@lem3999088 A s f x y) (@lem3999083 A s f x y)). Qed.
Lemma lem3999090 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term187 A s f x) = (term188 A s f x).
Proof. exact (fun_ext (fun y : A => @lem3999089 A s f x y)). Qed.
Lemma lem3999091 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3999092 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term184 A s f x) = (term189 A s f x).
Proof. exact (MK_COMB (@lem3999091 A) (@lem3999090 A s f x)). Qed.
Lemma lem3999093 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term183 A s f x) = (term189 A s f x).
Proof. exact (TRANS (@lem3999085 A s f x) (@lem3999092 A s f x)). Qed.
Lemma lem3999094 {A : Type'} (P : A -> Prop) : (term181 A P) = (term182 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3999095 {A : Type'} (s : A -> Prop) (f : A -> A) : (term190 A s f) = (term191 A s f).
Proof. exact (@lem3999094 A (term94 A s f)). Qed.
Lemma lem3999096 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term192 A s f x) = (term93 A s f x).
Proof. exact (eq_refl (term192 A s f x)). Qed.
Lemma lem3999097 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3999098 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term193 A s f x) = (term183 A s f x).
Proof. exact (MK_COMB (@lem3999097) (@lem3999096 A s f x)). Qed.
Lemma lem3999099 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term193 A s f x) = (term189 A s f x).
Proof. exact (TRANS (@lem3999098 A s f x) (@lem3999093 A s f x)). Qed.
Lemma lem3999100 {A : Type'} (s : A -> Prop) (f : A -> A) : (term194 A s f) = (term195 A s f).
Proof. exact (fun_ext (fun x : A => @lem3999099 A s f x)). Qed.
Lemma lem3999101 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3999102 {A : Type'} (s : A -> Prop) (f : A -> A) : (term191 A s f) = (term196 A s f).
Proof. exact (MK_COMB (@lem3999101 A) (@lem3999100 A s f)). Qed.
Lemma lem3999103 {A : Type'} (s : A -> Prop) (f : A -> A) : (term190 A s f) = (term196 A s f).
Proof. exact (TRANS (@lem3999095 A s f) (@lem3999102 A s f)). Qed.
Lemma lem3999104 {A : Type'} (s : A -> Prop) : (term197 A s) = (term197 A s).
Proof. exact (eq_refl (term197 A s)). Qed.
Lemma lem3999105 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3999106 {A : Type'} (s : A -> Prop) (f : A -> A) : (term198 A s f) = (term199 A s f).
Proof. exact (MK_COMB (@lem3999105) (@lem3999103 A s f)). Qed.
Lemma lem3999107 {A : Type'} (f : A -> A) (s : A -> Prop) : (term200 A f s) = (term201 A f s).
Proof. exact (MK_COMB (@lem3999106 A s f) (@lem3999104 A s)). Qed.
Lemma lem3999108 {A : Type'} (f : A -> A) (s : A -> Prop) : (term202 A f s) = (term200 A f s).
Proof. exact (@lem17045 (term95 A s f) (@FINITE A s)). Qed.
Lemma lem3999109 {A : Type'} (f : A -> A) (s : A -> Prop) : (term202 A f s) = (term201 A f s).
Proof. exact (TRANS (@lem3999108 A f s) (@lem3999107 A f s)). Qed.
Lemma lem3999110 {A : Type'} (f : A -> A) (s : A -> Prop) : ((term90 A f s) = (@CARD A s)) = ((term90 A f s) = (@CARD A s)).
Proof. exact (eq_refl ((term90 A f s) = (@CARD A s))). Qed.
Lemma lem3999111 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3999112 {A : Type'} (f : A -> A) (s : A -> Prop) : (term203 A f s) = (term204 A f s).
Proof. exact (MK_COMB (@lem3999111) (@lem3999109 A f s)). Qed.
Lemma lem3999113 {A : Type'} (f : A -> A) (s : A -> Prop) : (term205 A f s) = (term206 A f s).
Proof. exact (MK_COMB (@lem3999112 A f s) (@lem3999110 A f s)). Qed.
Lemma lem3999114 {A : Type'} (f : A -> A) (s : A -> Prop) : (term99 A f s) = (term205 A f s).
Proof. exact (@lem17265 (term97 A f s) ((term90 A f s) = (@CARD A s))). Qed.
Lemma lem3999115 {A : Type'} (f : A -> A) (s : A -> Prop) : (term99 A f s) = (term206 A f s).
Proof. exact (TRANS (@lem3999114 A f s) (@lem3999113 A f s)). Qed.
Lemma lem3999116 {A : Type'} (f : A -> A) : (term100 A f) = (term207 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3999115 A f s)). Qed.
Lemma lem3999117 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3999118 {A : Type'} (f : A -> A) : (term101 A f) = (term208 A f).
Proof. exact (MK_COMB (@lem3999117 A) (@lem3999116 A f)). Qed.
Lemma lem3999119 {A : Type'} : (term102 A) = (term209 A).
Proof. exact (fun_ext (fun f : A -> A => @lem3999118 A f)). Qed.
Lemma lem3999120 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem3999121 {A : Type'} : (term55 A) = (term210 A).
Proof. exact (MK_COMB (@lem3999120 A) (@lem3999119 A)). Qed.
Lemma lem3999228 {A : Type'} (P : A -> Prop) (Q : Prop) : (term211 A P Q) = (term212 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3999229 {A : Type'} (P : A -> Prop) (Q : Prop) : (term211 A P Q) = (term212 A P Q).
Proof. exact (@lem3999228 A P Q). Qed.
Lemma lem3999230 {A : Type'} (f : A -> A) (s : A -> Prop) : (term213 A f s) = (term214 A f s).
Proof. exact (@lem3999229 A (term195 A s f) (term197 A s)). Qed.
Lemma lem3999231 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term215 A s f x) = (term189 A s f x).
Proof. exact (eq_refl (term215 A s f x)). Qed.
Lemma lem3999232 {A : Type'} (s : A -> Prop) (f : A -> A) : (term216 A s f) = (term195 A s f).
Proof. exact (fun_ext (fun x : A => @lem3999231 A s f x)). Qed.
Lemma lem3999233 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3999234 {A : Type'} (s : A -> Prop) (f : A -> A) : (term217 A s f) = (term196 A s f).
Proof. exact (MK_COMB (@lem3999233 A) (@lem3999232 A s f)). Qed.
Lemma lem3999235 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3999236 {A : Type'} (s : A -> Prop) (f : A -> A) : (term218 A s f) = (term199 A s f).
Proof. exact (MK_COMB (@lem3999235) (@lem3999234 A s f)). Qed.
Lemma lem3999237 {A : Type'} (s : A -> Prop) : (term197 A s) = (term197 A s).
Proof. exact (eq_refl (term197 A s)). Qed.
Lemma lem3999238 {A : Type'} (f : A -> A) (s : A -> Prop) : (term213 A f s) = (term201 A f s).
Proof. exact (MK_COMB (@lem3999236 A s f) (@lem3999237 A s)). Qed.
Lemma lem3999239 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3999240 {A : Type'} (f : A -> A) (s : A -> Prop) : (term219 A f s) = (term220 A f s).
Proof. exact (MK_COMB (@lem3999239) (@lem3999238 A f s)). Qed.
Lemma lem3999241 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term215 A s f x) = (term189 A s f x).
Proof. exact (eq_refl (term215 A s f x)). Qed.
Lemma lem3999242 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3999243 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term221 A s f x) = (term222 A s f x).
Proof. exact (MK_COMB (@lem3999242) (@lem3999241 A s f x)). Qed.
Lemma lem3999244 {A : Type'} (s : A -> Prop) : (term197 A s) = (term197 A s).
Proof. exact (eq_refl (term197 A s)). Qed.
Lemma lem3999245 {A : Type'} (f : A -> A) (x : A) (s : A -> Prop) : (term223 A f x s) = (term224 A f x s).
Proof. exact (MK_COMB (@lem3999243 A s f x) (@lem3999244 A s)). Qed.
Lemma lem3999246 {A : Type'} (f : A -> A) (s : A -> Prop) : (term225 A f s) = (term226 A f s).
Proof. exact (fun_ext (fun x : A => @lem3999245 A f x s)). Qed.
Lemma lem3999247 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3999248 {A : Type'} (f : A -> A) (s : A -> Prop) : (term214 A f s) = (term227 A f s).
Proof. exact (MK_COMB (@lem3999247 A) (@lem3999246 A f s)). Qed.
Lemma lem3999249 {A : Type'} (f : A -> A) (s : A -> Prop) : ((term213 A f s) = (term214 A f s)) = ((term201 A f s) = (term227 A f s)).
Proof. exact (MK_COMB (@lem3999240 A f s) (@lem3999248 A f s)). Qed.
Lemma lem3999250 {A : Type'} (f : A -> A) (s : A -> Prop) : (term201 A f s) = (term227 A f s).
Proof. exact (EQ_MP (@lem3999249 A f s) (@lem3999230 A f s)). Qed.
Lemma lem3999252 {A : Type'} (P : A -> Prop) (Q : Prop) : (term211 A P Q) = (term212 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3999253 {A : Type'} (P : A -> Prop) (Q : Prop) : (term211 A P Q) = (term212 A P Q).
Proof. exact (@lem3999252 A P Q). Qed.
Lemma lem3999254 {A : Type'} (f : A -> A) (x : A) (s : A -> Prop) : (term228 A f x s) = (term229 A f x s).
Proof. exact (@lem3999253 A (term188 A s f x) (term197 A s)). Qed.
Lemma lem3999255 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (y : A) : (term230 A s f x y) = (term179 A s f x y).
Proof. exact (eq_refl (term230 A s f x y)). Qed.
Lemma lem3999256 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term231 A s f x) = (term188 A s f x).
Proof. exact (fun_ext (fun y : A => @lem3999255 A s f x y)). Qed.
Lemma lem3999257 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3999258 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term232 A s f x) = (term189 A s f x).
Proof. exact (MK_COMB (@lem3999257 A) (@lem3999256 A s f x)). Qed.
Lemma lem3999259 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3999260 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term233 A s f x) = (term222 A s f x).
Proof. exact (MK_COMB (@lem3999259) (@lem3999258 A s f x)). Qed.
Lemma lem3999261 {A : Type'} (s : A -> Prop) : (term197 A s) = (term197 A s).
Proof. exact (eq_refl (term197 A s)). Qed.
Lemma lem3999262 {A : Type'} (f : A -> A) (x : A) (s : A -> Prop) : (term228 A f x s) = (term224 A f x s).
Proof. exact (MK_COMB (@lem3999260 A s f x) (@lem3999261 A s)). Qed.
Lemma lem3999263 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3999264 {A : Type'} (f : A -> A) (x : A) (s : A -> Prop) : (term234 A f x s) = (term235 A f x s).
Proof. exact (MK_COMB (@lem3999263) (@lem3999262 A f x s)). Qed.
Lemma lem3999265 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (y : A) : (term230 A s f x y) = (term179 A s f x y).
Proof. exact (eq_refl (term230 A s f x y)). Qed.
Lemma lem3999266 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3999267 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (y : A) : (term236 A s f x y) = (term237 A s f x y).
Proof. exact (MK_COMB (@lem3999266) (@lem3999265 A s f x y)). Qed.
Lemma lem3999268 {A : Type'} (s : A -> Prop) : (term197 A s) = (term197 A s).
Proof. exact (eq_refl (term197 A s)). Qed.
Lemma lem3999269 {A : Type'} (f : A -> A) (x : A) (y : A) (s : A -> Prop) : (term238 A f x y s) = (term239 A f x y s).
Proof. exact (MK_COMB (@lem3999267 A s f x y) (@lem3999268 A s)). Qed.
Lemma lem3999270 {A : Type'} (f : A -> A) (x : A) (s : A -> Prop) : (term240 A f x s) = (term241 A f x s).
Proof. exact (fun_ext (fun y : A => @lem3999269 A f x y s)). Qed.
Lemma lem3999271 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3999272 {A : Type'} (f : A -> A) (x : A) (s : A -> Prop) : (term229 A f x s) = (term242 A f x s).
Proof. exact (MK_COMB (@lem3999271 A) (@lem3999270 A f x s)). Qed.
Lemma lem3999273 {A : Type'} (f : A -> A) (x : A) (s : A -> Prop) : ((term228 A f x s) = (term229 A f x s)) = ((term224 A f x s) = (term242 A f x s)).
Proof. exact (MK_COMB (@lem3999264 A f x s) (@lem3999272 A f x s)). Qed.
Lemma lem3999274 {A : Type'} (f : A -> A) (x : A) (s : A -> Prop) : (term224 A f x s) = (term242 A f x s).
Proof. exact (EQ_MP (@lem3999273 A f x s) (@lem3999254 A f x s)). Qed.
Lemma lem3999275 {A : Type'} (f : A -> A) (s : A -> Prop) : (term226 A f s) = (term243 A f s).
Proof. exact (fun_ext (fun x : A => @lem3999274 A f x s)). Qed.
Lemma lem3999276 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3999277 {A : Type'} (f : A -> A) (s : A -> Prop) : (term227 A f s) = (term244 A f s).
Proof. exact (MK_COMB (@lem3999276 A) (@lem3999275 A f s)). Qed.
Lemma lem3999278 {A : Type'} (f : A -> A) (s : A -> Prop) : (term201 A f s) = (term244 A f s).
Proof. exact (TRANS (@lem3999250 A f s) (@lem3999277 A f s)). Qed.
Lemma lem3999279 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3999280 {A : Type'} (f : A -> A) (s : A -> Prop) : (term204 A f s) = (term245 A f s).
Proof. exact (MK_COMB (@lem3999279) (@lem3999278 A f s)). Qed.
Lemma lem3999281 {A : Type'} (f : A -> A) (s : A -> Prop) : ((term90 A f s) = (@CARD A s)) = ((term90 A f s) = (@CARD A s)).
Proof. exact (eq_refl ((term90 A f s) = (@CARD A s))). Qed.
Lemma lem3999282 {A : Type'} (f : A -> A) (s : A -> Prop) : (term206 A f s) = (term246 A f s).
Proof. exact (MK_COMB (@lem3999280 A f s) (@lem3999281 A f s)). Qed.
Lemma lem3999284 {A : Type'} (P : A -> Prop) (Q : Prop) : (term211 A P Q) = (term212 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3999285 {A : Type'} (P : A -> Prop) (Q : Prop) : (term211 A P Q) = (term212 A P Q).
Proof. exact (@lem3999284 A P Q). Qed.
Lemma lem3999286 {A : Type'} (f : A -> A) (s : A -> Prop) : (term247 A f s) = (term248 A f s).
Proof. exact (@lem3999285 A (term243 A f s) ((term90 A f s) = (@CARD A s))). Qed.
Lemma lem3999287 {A : Type'} (f : A -> A) (x : A) (s : A -> Prop) : (term249 A f s x) = (term242 A f x s).
Proof. exact (eq_refl (term249 A f s x)). Qed.
Lemma lem3999288 {A : Type'} (f : A -> A) (s : A -> Prop) : (term250 A f s) = (term243 A f s).
Proof. exact (fun_ext (fun x : A => @lem3999287 A f x s)). Qed.
Lemma lem3999289 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3999290 {A : Type'} (f : A -> A) (s : A -> Prop) : (term251 A f s) = (term244 A f s).
Proof. exact (MK_COMB (@lem3999289 A) (@lem3999288 A f s)). Qed.
Lemma lem3999291 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3999292 {A : Type'} (f : A -> A) (s : A -> Prop) : (term252 A f s) = (term245 A f s).
Proof. exact (MK_COMB (@lem3999291) (@lem3999290 A f s)). Qed.
Lemma lem3999293 {A : Type'} (f : A -> A) (s : A -> Prop) : ((term90 A f s) = (@CARD A s)) = ((term90 A f s) = (@CARD A s)).
Proof. exact (eq_refl ((term90 A f s) = (@CARD A s))). Qed.
Lemma lem3999294 {A : Type'} (f : A -> A) (s : A -> Prop) : (term247 A f s) = (term246 A f s).
Proof. exact (MK_COMB (@lem3999292 A f s) (@lem3999293 A f s)). Qed.
Lemma lem3999295 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3999296 {A : Type'} (f : A -> A) (s : A -> Prop) : (term253 A f s) = (term254 A f s).
Proof. exact (MK_COMB (@lem3999295) (@lem3999294 A f s)). Qed.
Lemma lem3999297 {A : Type'} (f : A -> A) (x : A) (s : A -> Prop) : (term249 A f s x) = (term242 A f x s).
Proof. exact (eq_refl (term249 A f s x)). Qed.
Lemma lem3999298 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3999299 {A : Type'} (f : A -> A) (x : A) (s : A -> Prop) : (term255 A f s x) = (term256 A f x s).
Proof. exact (MK_COMB (@lem3999298) (@lem3999297 A f x s)). Qed.
Lemma lem3999300 {A : Type'} (f : A -> A) (s : A -> Prop) : ((term90 A f s) = (@CARD A s)) = ((term90 A f s) = (@CARD A s)).
Proof. exact (eq_refl ((term90 A f s) = (@CARD A s))). Qed.
Lemma lem3999301 {A : Type'} (x : A) (f : A -> A) (s : A -> Prop) : (term257 A x f s) = (term258 A x f s).
Proof. exact (MK_COMB (@lem3999299 A f x s) (@lem3999300 A f s)). Qed.
Lemma lem3999302 {A : Type'} (f : A -> A) (s : A -> Prop) : (term259 A f s) = (term260 A f s).
Proof. exact (fun_ext (fun x : A => @lem3999301 A x f s)). Qed.
Lemma lem3999303 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3999304 {A : Type'} (f : A -> A) (s : A -> Prop) : (term248 A f s) = (term261 A f s).
Proof. exact (MK_COMB (@lem3999303 A) (@lem3999302 A f s)). Qed.
Lemma lem3999305 {A : Type'} (f : A -> A) (s : A -> Prop) : ((term247 A f s) = (term248 A f s)) = ((term246 A f s) = (term261 A f s)).
Proof. exact (MK_COMB (@lem3999296 A f s) (@lem3999304 A f s)). Qed.
Lemma lem3999306 {A : Type'} (f : A -> A) (s : A -> Prop) : (term246 A f s) = (term261 A f s).
Proof. exact (EQ_MP (@lem3999305 A f s) (@lem3999286 A f s)). Qed.
Lemma lem3999308 {A : Type'} (P : A -> Prop) (Q : Prop) : (term211 A P Q) = (term212 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3999309 {A : Type'} (P : A -> Prop) (Q : Prop) : (term211 A P Q) = (term212 A P Q).
Proof. exact (@lem3999308 A P Q). Qed.
Lemma lem3999310 {A : Type'} (x : A) (f : A -> A) (s : A -> Prop) : (term262 A x f s) = (term263 A x f s).
Proof. exact (@lem3999309 A (term241 A f x s) ((term90 A f s) = (@CARD A s))). Qed.
Lemma lem3999311 {A : Type'} (f : A -> A) (x : A) (y : A) (s : A -> Prop) : (term264 A f x s y) = (term239 A f x y s).
Proof. exact (eq_refl (term264 A f x s y)). Qed.
Lemma lem3999312 {A : Type'} (f : A -> A) (x : A) (s : A -> Prop) : (term265 A f x s) = (term241 A f x s).
Proof. exact (fun_ext (fun y : A => @lem3999311 A f x y s)). Qed.
Lemma lem3999313 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3999314 {A : Type'} (f : A -> A) (x : A) (s : A -> Prop) : (term266 A f x s) = (term242 A f x s).
Proof. exact (MK_COMB (@lem3999313 A) (@lem3999312 A f x s)). Qed.
Lemma lem3999315 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3999316 {A : Type'} (f : A -> A) (x : A) (s : A -> Prop) : (term267 A f x s) = (term256 A f x s).
Proof. exact (MK_COMB (@lem3999315) (@lem3999314 A f x s)). Qed.
Lemma lem3999317 {A : Type'} (f : A -> A) (s : A -> Prop) : ((term90 A f s) = (@CARD A s)) = ((term90 A f s) = (@CARD A s)).
Proof. exact (eq_refl ((term90 A f s) = (@CARD A s))). Qed.
Lemma lem3999318 {A : Type'} (x : A) (f : A -> A) (s : A -> Prop) : (term262 A x f s) = (term258 A x f s).
Proof. exact (MK_COMB (@lem3999316 A f x s) (@lem3999317 A f s)). Qed.
Lemma lem3999319 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3999320 {A : Type'} (x : A) (f : A -> A) (s : A -> Prop) : (term268 A x f s) = (term269 A x f s).
Proof. exact (MK_COMB (@lem3999319) (@lem3999318 A x f s)). Qed.
Lemma lem3999321 {A : Type'} (f : A -> A) (x : A) (y : A) (s : A -> Prop) : (term264 A f x s y) = (term239 A f x y s).
Proof. exact (eq_refl (term264 A f x s y)). Qed.
Lemma lem3999322 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3999323 {A : Type'} (f : A -> A) (x : A) (y : A) (s : A -> Prop) : (term270 A f x s y) = (term271 A f x y s).
Proof. exact (MK_COMB (@lem3999322) (@lem3999321 A f x y s)). Qed.
Lemma lem3999324 {A : Type'} (f : A -> A) (s : A -> Prop) : ((term90 A f s) = (@CARD A s)) = ((term90 A f s) = (@CARD A s)).
Proof. exact (eq_refl ((term90 A f s) = (@CARD A s))). Qed.
Lemma lem3999325 {A : Type'} (x : A) (y : A) (f : A -> A) (s : A -> Prop) : (term272 A x y f s) = (term273 A x y f s).
Proof. exact (MK_COMB (@lem3999323 A f x y s) (@lem3999324 A f s)). Qed.
Lemma lem3999326 {A : Type'} (x : A) (f : A -> A) (s : A -> Prop) : (term274 A x f s) = (term275 A x f s).
Proof. exact (fun_ext (fun y : A => @lem3999325 A x y f s)). Qed.
Lemma lem3999327 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3999328 {A : Type'} (x : A) (f : A -> A) (s : A -> Prop) : (term263 A x f s) = (term276 A x f s).
Proof. exact (MK_COMB (@lem3999327 A) (@lem3999326 A x f s)). Qed.
Lemma lem3999329 {A : Type'} (x : A) (f : A -> A) (s : A -> Prop) : ((term262 A x f s) = (term263 A x f s)) = ((term258 A x f s) = (term276 A x f s)).
Proof. exact (MK_COMB (@lem3999320 A x f s) (@lem3999328 A x f s)). Qed.
Lemma lem3999330 {A : Type'} (x : A) (f : A -> A) (s : A -> Prop) : (term258 A x f s) = (term276 A x f s).
Proof. exact (EQ_MP (@lem3999329 A x f s) (@lem3999310 A x f s)). Qed.
Lemma lem3999331 {A : Type'} (f : A -> A) (s : A -> Prop) : (term260 A f s) = (term277 A f s).
Proof. exact (fun_ext (fun x : A => @lem3999330 A x f s)). Qed.
Lemma lem3999332 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3999333 {A : Type'} (f : A -> A) (s : A -> Prop) : (term261 A f s) = (term278 A f s).
Proof. exact (MK_COMB (@lem3999332 A) (@lem3999331 A f s)). Qed.
Lemma lem3999334 {A : Type'} (f : A -> A) (s : A -> Prop) : (term246 A f s) = (term278 A f s).
Proof. exact (TRANS (@lem3999306 A f s) (@lem3999333 A f s)). Qed.
Lemma lem3999335 {A : Type'} (f : A -> A) (s : A -> Prop) : (term206 A f s) = (term278 A f s).
Proof. exact (TRANS (@lem3999282 A f s) (@lem3999334 A f s)). Qed.
Lemma lem3999336 {A : Type'} (f : A -> A) : (term207 A f) = (term279 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3999335 A f s)). Qed.
Lemma lem3999337 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3999338 {A : Type'} (f : A -> A) : (term208 A f) = (term280 A f).
Proof. exact (MK_COMB (@lem3999337 A) (@lem3999336 A f)). Qed.
Lemma lem3999340 {A B : Type'} (P : type1413 A B) : (term281 A B P) = (term282 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3999341 {A : Type'} (P : type672 A) : (term283 A P) = (term284 A P).
Proof. exact (@lem3999340 (A -> Prop) A P). Qed.
Lemma lem3999342 {A : Type'} (f : A -> A) : (term285 A f) = (term286 A f).
Proof. exact (@lem3999341 A (term287 A f)). Qed.
Lemma lem3999343 {A : Type'} (f : A -> A) (s : A -> Prop) : (term288 A f s) = (term277 A f s).
Proof. exact (eq_refl (term288 A f s)). Qed.
Lemma lem3999344 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3999345 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) : (term289 A f s x) = (term290 A f s x).
Proof. exact (MK_COMB (@lem3999343 A f s) (@lem3999344 A x)). Qed.
Lemma lem3999346 {A : Type'} (x : A) (f : A -> A) (s : A -> Prop) : (term290 A f s x) = (term276 A x f s).
Proof. exact (eq_refl (term290 A f s x)). Qed.
Lemma lem3999347 {A : Type'} (x : A) (f : A -> A) (s : A -> Prop) : (term289 A f s x) = (term276 A x f s).
Proof. exact (TRANS (@lem3999345 A f s x) (@lem3999346 A x f s)). Qed.
Lemma lem3999348 {A : Type'} (f : A -> A) (s : A -> Prop) : (term291 A f s) = (term277 A f s).
Proof. exact (fun_ext (fun x : A => @lem3999347 A x f s)). Qed.
Lemma lem3999349 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3999350 {A : Type'} (f : A -> A) (s : A -> Prop) : (term292 A f s) = (term278 A f s).
Proof. exact (MK_COMB (@lem3999349 A) (@lem3999348 A f s)). Qed.
Lemma lem3999351 {A : Type'} (f : A -> A) : (term293 A f) = (term279 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3999350 A f s)). Qed.
Lemma lem3999352 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3999353 {A : Type'} (f : A -> A) : (term285 A f) = (term280 A f).
Proof. exact (MK_COMB (@lem3999352 A) (@lem3999351 A f)). Qed.
Lemma lem3999354 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3999355 {A : Type'} (f : A -> A) : (term294 A f) = (term295 A f).
Proof. exact (MK_COMB (@lem3999354) (@lem3999353 A f)). Qed.
Lemma lem3999356 {A : Type'} (f : A -> A) (s : A -> Prop) : (term288 A f s) = (term277 A f s).
Proof. exact (eq_refl (term288 A f s)). Qed.
Lemma lem3999357 {A : Type'} (x : type684 A) (s : A -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem3999358 {A : Type'} (f : A -> A) (x : type684 A) (s : A -> Prop) : (term296 A f x s) = (term297 A f x s).
Proof. exact (MK_COMB (@lem3999356 A f s) (@lem3999357 A x s)). Qed.
Lemma lem3999359 {A : Type'} (x : type684 A) (f : A -> A) (s : A -> Prop) : (term297 A f x s) = (term298 A x f s).
Proof. exact (eq_refl (term297 A f x s)). Qed.
Lemma lem3999360 {A : Type'} (x : type684 A) (f : A -> A) (s : A -> Prop) : (term296 A f x s) = (term298 A x f s).
Proof. exact (TRANS (@lem3999358 A f x s) (@lem3999359 A x f s)). Qed.
Lemma lem3999361 {A : Type'} (x : type684 A) (f : A -> A) : (term299 A f x) = (term300 A x f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3999360 A x f s)). Qed.
Lemma lem3999362 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3999363 {A : Type'} (x : type684 A) (f : A -> A) : (term301 A f x) = (term302 A x f).
Proof. exact (MK_COMB (@lem3999362 A) (@lem3999361 A x f)). Qed.
Lemma lem3999364 {A : Type'} (f : A -> A) : (term303 A f) = (term304 A f).
Proof. exact (fun_ext (fun x : type684 A => @lem3999363 A x f)). Qed.
Lemma lem3999365 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem3999366 {A : Type'} (f : A -> A) : (term286 A f) = (term305 A f).
Proof. exact (MK_COMB (@lem3999365 A) (@lem3999364 A f)). Qed.
Lemma lem3999367 {A : Type'} (f : A -> A) : ((term285 A f) = (term286 A f)) = ((term280 A f) = (term305 A f)).
Proof. exact (MK_COMB (@lem3999355 A f) (@lem3999366 A f)). Qed.
Lemma lem3999368 {A : Type'} (f : A -> A) : (term280 A f) = (term305 A f).
Proof. exact (EQ_MP (@lem3999367 A f) (@lem3999342 A f)). Qed.
Lemma lem3999370 {A B : Type'} (P : type1413 A B) : (term281 A B P) = (term282 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3999371 {A : Type'} (P : type672 A) : (term283 A P) = (term284 A P).
Proof. exact (@lem3999370 (A -> Prop) A P). Qed.
Lemma lem3999372 {A : Type'} (x : type684 A) (f : A -> A) : (term306 A x f) = (term307 A x f).
Proof. exact (@lem3999371 A (term308 A x f)). Qed.
Lemma lem3999373 {A : Type'} (x : type684 A) (f : A -> A) (s : A -> Prop) : (term309 A x f s) = (term310 A x f s).
Proof. exact (eq_refl (term309 A x f s)). Qed.
Lemma lem3999374 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem3999375 {A : Type'} (x : type684 A) (f : A -> A) (s : A -> Prop) (y : A) : (term311 A x f s y) = (term312 A x f s y).
Proof. exact (MK_COMB (@lem3999373 A x f s) (@lem3999374 A y)). Qed.
Lemma lem3999376 {A : Type'} (x : type684 A) (y : A) (f : A -> A) (s : A -> Prop) : (term312 A x f s y) = (term313 A x y f s).
Proof. exact (eq_refl (term312 A x f s y)). Qed.
Lemma lem3999377 {A : Type'} (x : type684 A) (y : A) (f : A -> A) (s : A -> Prop) : (term311 A x f s y) = (term313 A x y f s).
Proof. exact (TRANS (@lem3999375 A x f s y) (@lem3999376 A x y f s)). Qed.
Lemma lem3999378 {A : Type'} (x : type684 A) (f : A -> A) (s : A -> Prop) : (term314 A x f s) = (term310 A x f s).
Proof. exact (fun_ext (fun y : A => @lem3999377 A x y f s)). Qed.
Lemma lem3999379 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3999380 {A : Type'} (x : type684 A) (f : A -> A) (s : A -> Prop) : (term315 A x f s) = (term298 A x f s).
Proof. exact (MK_COMB (@lem3999379 A) (@lem3999378 A x f s)). Qed.
Lemma lem3999381 {A : Type'} (x : type684 A) (f : A -> A) : (term316 A x f) = (term300 A x f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3999380 A x f s)). Qed.
Lemma lem3999382 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3999383 {A : Type'} (x : type684 A) (f : A -> A) : (term306 A x f) = (term302 A x f).
Proof. exact (MK_COMB (@lem3999382 A) (@lem3999381 A x f)). Qed.
Lemma lem3999384 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3999385 {A : Type'} (x : type684 A) (f : A -> A) : (term317 A x f) = (term318 A x f).
Proof. exact (MK_COMB (@lem3999384) (@lem3999383 A x f)). Qed.
Lemma lem3999386 {A : Type'} (x : type684 A) (f : A -> A) (s : A -> Prop) : (term309 A x f s) = (term310 A x f s).
Proof. exact (eq_refl (term309 A x f s)). Qed.
Lemma lem3999387 {A : Type'} (y : type684 A) (s : A -> Prop) : (y s) = (y s).
Proof. exact (eq_refl (y s)). Qed.
Lemma lem3999388 {A : Type'} (x : type684 A) (f : A -> A) (y : type684 A) (s : A -> Prop) : (term319 A x f y s) = (term320 A x f y s).
Proof. exact (MK_COMB (@lem3999386 A x f s) (@lem3999387 A y s)). Qed.
Lemma lem3999389 {A : Type'} (x : type684 A) (y : type684 A) (f : A -> A) (s : A -> Prop) : (term320 A x f y s) = (term321 A x y f s).
Proof. exact (eq_refl (term320 A x f y s)). Qed.
Lemma lem3999390 {A : Type'} (x : type684 A) (y : type684 A) (f : A -> A) (s : A -> Prop) : (term319 A x f y s) = (term321 A x y f s).
Proof. exact (TRANS (@lem3999388 A x f y s) (@lem3999389 A x y f s)). Qed.
Lemma lem3999391 {A : Type'} (x : type684 A) (y : type684 A) (f : A -> A) : (term322 A x f y) = (term323 A x y f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3999390 A x y f s)). Qed.
Lemma lem3999392 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3999393 {A : Type'} (x : type684 A) (y : type684 A) (f : A -> A) : (term324 A x f y) = (term325 A x y f).
Proof. exact (MK_COMB (@lem3999392 A) (@lem3999391 A x y f)). Qed.
Lemma lem3999394 {A : Type'} (x : type684 A) (f : A -> A) : (term326 A x f) = (term327 A x f).
Proof. exact (fun_ext (fun y : type684 A => @lem3999393 A x y f)). Qed.
Lemma lem3999395 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem3999396 {A : Type'} (x : type684 A) (f : A -> A) : (term307 A x f) = (term328 A x f).
Proof. exact (MK_COMB (@lem3999395 A) (@lem3999394 A x f)). Qed.
Lemma lem3999397 {A : Type'} (x : type684 A) (f : A -> A) : ((term306 A x f) = (term307 A x f)) = ((term302 A x f) = (term328 A x f)).
Proof. exact (MK_COMB (@lem3999385 A x f) (@lem3999396 A x f)). Qed.
Lemma lem3999398 {A : Type'} (x : type684 A) (f : A -> A) : (term302 A x f) = (term328 A x f).
Proof. exact (EQ_MP (@lem3999397 A x f) (@lem3999372 A x f)). Qed.
Lemma lem3999399 {A : Type'} (f : A -> A) : (term304 A f) = (term329 A f).
Proof. exact (fun_ext (fun x : type684 A => @lem3999398 A x f)). Qed.
Lemma lem3999400 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem3999401 {A : Type'} (f : A -> A) : (term305 A f) = (term330 A f).
Proof. exact (MK_COMB (@lem3999400 A) (@lem3999399 A f)). Qed.
Lemma lem3999402 {A : Type'} (f : A -> A) : (term280 A f) = (term330 A f).
Proof. exact (TRANS (@lem3999368 A f) (@lem3999401 A f)). Qed.
Lemma lem3999403 {A : Type'} (f : A -> A) : (term208 A f) = (term330 A f).
Proof. exact (TRANS (@lem3999338 A f) (@lem3999402 A f)). Qed.
Lemma lem3999404 {A : Type'} : (term209 A) = (term331 A).
Proof. exact (fun_ext (fun f : A -> A => @lem3999403 A f)). Qed.
Lemma lem3999405 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem3999406 {A : Type'} : (term210 A) = (term332 A).
Proof. exact (MK_COMB (@lem3999405 A) (@lem3999404 A)). Qed.
Lemma lem3999408 {A B : Type'} (P : type1413 A B) : (term281 A B P) = (term282 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3999409 {A : Type'} (P : type481 A) : (term333 A P) = (term334 A P).
Proof. exact (@lem3999408 (A -> A) (type684 A) P). Qed.
Lemma lem3999410 {A : Type'} : (term335 A) = (term336 A).
Proof. exact (@lem3999409 A (term337 A)). Qed.
Lemma lem3999411 {A : Type'} (f : A -> A) : (term338 A f) = (term329 A f).
Proof. exact (eq_refl (term338 A f)). Qed.
Lemma lem3999412 {A : Type'} (x : type684 A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3999413 {A : Type'} (f : A -> A) (x : type684 A) : (term339 A f x) = (term340 A f x).
Proof. exact (MK_COMB (@lem3999411 A f) (@lem3999412 A x)). Qed.
Lemma lem3999414 {A : Type'} (x : type684 A) (f : A -> A) : (term340 A f x) = (term328 A x f).
Proof. exact (eq_refl (term340 A f x)). Qed.
Lemma lem3999415 {A : Type'} (x : type684 A) (f : A -> A) : (term339 A f x) = (term328 A x f).
Proof. exact (TRANS (@lem3999413 A f x) (@lem3999414 A x f)). Qed.
Lemma lem3999416 {A : Type'} (f : A -> A) : (term341 A f) = (term329 A f).
Proof. exact (fun_ext (fun x : type684 A => @lem3999415 A x f)). Qed.
Lemma lem3999417 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem3999418 {A : Type'} (f : A -> A) : (term342 A f) = (term330 A f).
Proof. exact (MK_COMB (@lem3999417 A) (@lem3999416 A f)). Qed.
Lemma lem3999419 {A : Type'} : (term343 A) = (term331 A).
Proof. exact (fun_ext (fun f : A -> A => @lem3999418 A f)). Qed.
Lemma lem3999420 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem3999421 {A : Type'} : (term335 A) = (term332 A).
Proof. exact (MK_COMB (@lem3999420 A) (@lem3999419 A)). Qed.
Lemma lem3999422 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3999423 {A : Type'} : (term344 A) = (term345 A).
Proof. exact (MK_COMB (@lem3999422) (@lem3999421 A)). Qed.
Lemma lem3999424 {A : Type'} (f : A -> A) : (term338 A f) = (term329 A f).
Proof. exact (eq_refl (term338 A f)). Qed.
Lemma lem3999425 {A : Type'} (x : type485 A) (f : A -> A) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem3999426 {A : Type'} (x : type485 A) (f : A -> A) : (term346 A x f) = (term347 A x f).
Proof. exact (MK_COMB (@lem3999424 A f) (@lem3999425 A x f)). Qed.
Lemma lem3999427 {A : Type'} (x : type485 A) (f : A -> A) : (term347 A x f) = (term348 A x f).
Proof. exact (eq_refl (term347 A x f)). Qed.
Lemma lem3999428 {A : Type'} (x : type485 A) (f : A -> A) : (term346 A x f) = (term348 A x f).
Proof. exact (TRANS (@lem3999426 A x f) (@lem3999427 A x f)). Qed.
Lemma lem3999429 {A : Type'} (x : type485 A) : (term349 A x) = (term350 A x).
Proof. exact (fun_ext (fun f : A -> A => @lem3999428 A x f)). Qed.
Lemma lem3999430 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem3999431 {A : Type'} (x : type485 A) : (term351 A x) = (term352 A x).
Proof. exact (MK_COMB (@lem3999430 A) (@lem3999429 A x)). Qed.
Lemma lem3999432 {A : Type'} : (term353 A) = (term354 A).
Proof. exact (fun_ext (fun x : type485 A => @lem3999431 A x)). Qed.
Lemma lem3999433 {A : Type'} : (@ex ((A -> A) -> (A -> Prop) -> A)) = (@ex ((A -> A) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> A) -> (A -> Prop) -> A))). Qed.
Lemma lem3999434 {A : Type'} : (term336 A) = (term355 A).
Proof. exact (MK_COMB (@lem3999433 A) (@lem3999432 A)). Qed.
Lemma lem3999435 {A : Type'} : ((term335 A) = (term336 A)) = ((term332 A) = (term355 A)).
Proof. exact (MK_COMB (@lem3999423 A) (@lem3999434 A)). Qed.
Lemma lem3999436 {A : Type'} : (term332 A) = (term355 A).
Proof. exact (EQ_MP (@lem3999435 A) (@lem3999410 A)). Qed.
Lemma lem3999438 {A B : Type'} (P : type1413 A B) : (term281 A B P) = (term282 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3999439 {A : Type'} (P : type481 A) : (term333 A P) = (term334 A P).
Proof. exact (@lem3999438 (A -> A) (type684 A) P). Qed.
Lemma lem3999440 {A : Type'} (x : type485 A) : (term356 A x) = (term357 A x).
Proof. exact (@lem3999439 A (term358 A x)). Qed.
Lemma lem3999441 {A : Type'} (x : type485 A) (f : A -> A) : (term359 A x f) = (term360 A x f).
Proof. exact (eq_refl (term359 A x f)). Qed.
Lemma lem3999442 {A : Type'} (y : type684 A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem3999443 {A : Type'} (x : type485 A) (f : A -> A) (y : type684 A) : (term361 A x f y) = (term362 A x f y).
Proof. exact (MK_COMB (@lem3999441 A x f) (@lem3999442 A y)). Qed.
Lemma lem3999444 {A : Type'} (x : type485 A) (y : type684 A) (f : A -> A) : (term362 A x f y) = (term363 A x y f).
Proof. exact (eq_refl (term362 A x f y)). Qed.
Lemma lem3999445 {A : Type'} (x : type485 A) (y : type684 A) (f : A -> A) : (term361 A x f y) = (term363 A x y f).
Proof. exact (TRANS (@lem3999443 A x f y) (@lem3999444 A x y f)). Qed.
Lemma lem3999446 {A : Type'} (x : type485 A) (f : A -> A) : (term364 A x f) = (term360 A x f).
Proof. exact (fun_ext (fun y : type684 A => @lem3999445 A x y f)). Qed.
Lemma lem3999447 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem3999448 {A : Type'} (x : type485 A) (f : A -> A) : (term365 A x f) = (term348 A x f).
Proof. exact (MK_COMB (@lem3999447 A) (@lem3999446 A x f)). Qed.
Lemma lem3999449 {A : Type'} (x : type485 A) : (term366 A x) = (term350 A x).
Proof. exact (fun_ext (fun f : A -> A => @lem3999448 A x f)). Qed.
Lemma lem3999450 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem3999451 {A : Type'} (x : type485 A) : (term356 A x) = (term352 A x).
Proof. exact (MK_COMB (@lem3999450 A) (@lem3999449 A x)). Qed.
Lemma lem3999452 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3999453 {A : Type'} (x : type485 A) : (term367 A x) = (term368 A x).
Proof. exact (MK_COMB (@lem3999452) (@lem3999451 A x)). Qed.
Lemma lem3999454 {A : Type'} (x : type485 A) (f : A -> A) : (term359 A x f) = (term360 A x f).
Proof. exact (eq_refl (term359 A x f)). Qed.
Lemma lem3999455 {A : Type'} (y : type485 A) (f : A -> A) : (y f) = (y f).
Proof. exact (eq_refl (y f)). Qed.
Lemma lem3999456 {A : Type'} (x : type485 A) (y : type485 A) (f : A -> A) : (term369 A x y f) = (term370 A x y f).
Proof. exact (MK_COMB (@lem3999454 A x f) (@lem3999455 A y f)). Qed.
Lemma lem3999457 {A : Type'} (x : type485 A) (y : type485 A) (f : A -> A) : (term370 A x y f) = (term371 A x y f).
Proof. exact (eq_refl (term370 A x y f)). Qed.
Lemma lem3999458 {A : Type'} (x : type485 A) (y : type485 A) (f : A -> A) : (term369 A x y f) = (term371 A x y f).
Proof. exact (TRANS (@lem3999456 A x y f) (@lem3999457 A x y f)). Qed.
Lemma lem3999459 {A : Type'} (x : type485 A) (y : type485 A) : (term372 A x y) = (term373 A x y).
Proof. exact (fun_ext (fun f : A -> A => @lem3999458 A x y f)). Qed.
Lemma lem3999460 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem3999461 {A : Type'} (x : type485 A) (y : type485 A) : (term374 A x y) = (term375 A x y).
Proof. exact (MK_COMB (@lem3999460 A) (@lem3999459 A x y)). Qed.
Lemma lem3999462 {A : Type'} (x : type485 A) : (term376 A x) = (term377 A x).
Proof. exact (fun_ext (fun y : type485 A => @lem3999461 A x y)). Qed.
Lemma lem3999463 {A : Type'} : (@ex ((A -> A) -> (A -> Prop) -> A)) = (@ex ((A -> A) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> A) -> (A -> Prop) -> A))). Qed.
Lemma lem3999464 {A : Type'} (x : type485 A) : (term357 A x) = (term378 A x).
Proof. exact (MK_COMB (@lem3999463 A) (@lem3999462 A x)). Qed.
Lemma lem3999465 {A : Type'} (x : type485 A) : ((term356 A x) = (term357 A x)) = ((term352 A x) = (term378 A x)).
Proof. exact (MK_COMB (@lem3999453 A x) (@lem3999464 A x)). Qed.
Lemma lem3999466 {A : Type'} (x : type485 A) : (term352 A x) = (term378 A x).
Proof. exact (EQ_MP (@lem3999465 A x) (@lem3999440 A x)). Qed.
Lemma lem3999467 {A : Type'} : (term354 A) = (term379 A).
Proof. exact (fun_ext (fun x : type485 A => @lem3999466 A x)). Qed.
Lemma lem3999468 {A : Type'} : (@ex ((A -> A) -> (A -> Prop) -> A)) = (@ex ((A -> A) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> A) -> (A -> Prop) -> A))). Qed.
Lemma lem3999469 {A : Type'} : (term355 A) = (term380 A).
Proof. exact (MK_COMB (@lem3999468 A) (@lem3999467 A)). Qed.
Lemma lem3999470 {A : Type'} : (term332 A) = (term380 A).
Proof. exact (TRANS (@lem3999436 A) (@lem3999469 A)). Qed.
Lemma lem3999472 {A : Type'} : (term210 A) = (term380 A).
Proof. exact (TRANS (@lem3999406 A) (@lem3999470 A)). Qed.
Lemma lem3999473 {A : Type'} : (term55 A) = (term380 A).
Proof. exact (TRANS (@lem3999121 A) (@lem3999472 A)). Qed.
Lemma lem3999474 {A : Type'} (h1 : term55 A) : term380 A.
Proof. exact (EQ_MP (@lem3999473 A) (@lem3998882 A h1)). Qed.
Lemma lem3999489 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term381 A B s f x y) = (term382 A B s f x y).
Proof. exact (@lem17362 (term139 A B s x f y) (x = y)). Qed.
Lemma lem3999490 {A : Type'} (P : A -> Prop) : (term181 A P) = (term182 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3999491 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term383 A B s f x) = (term384 A B s f x).
Proof. exact (@lem3999490 A (term117 A B s f x)). Qed.
Lemma lem3999492 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term385 A B s f x y) = (term116 A B s f x y).
Proof. exact (eq_refl (term385 A B s f x y)). Qed.
Lemma lem3999493 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3999494 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term386 A B s f x y) = (term381 A B s f x y).
Proof. exact (MK_COMB (@lem3999493) (@lem3999492 A B s f x y)). Qed.
Lemma lem3999495 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term386 A B s f x y) = (term382 A B s f x y).
Proof. exact (TRANS (@lem3999494 A B s f x y) (@lem3999489 A B s f x y)). Qed.
Lemma lem3999496 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term387 A B s f x) = (term388 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem3999495 A B s f x y)). Qed.
Lemma lem3999497 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3999498 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term384 A B s f x) = (term389 A B s f x).
Proof. exact (MK_COMB (@lem3999497 A) (@lem3999496 A B s f x)). Qed.
Lemma lem3999499 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term383 A B s f x) = (term389 A B s f x).
Proof. exact (TRANS (@lem3999491 A B s f x) (@lem3999498 A B s f x)). Qed.
Lemma lem3999500 {A : Type'} (P : A -> Prop) : (term181 A P) = (term182 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3999501 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term390 A B s f) = (term391 A B s f).
Proof. exact (@lem3999500 A (term119 A B s f)). Qed.
Lemma lem3999502 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term392 A B s f x) = (term118 A B s f x).
Proof. exact (eq_refl (term392 A B s f x)). Qed.
Lemma lem3999503 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3999504 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term393 A B s f x) = (term383 A B s f x).
Proof. exact (MK_COMB (@lem3999503) (@lem3999502 A B s f x)). Qed.
Lemma lem3999505 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term393 A B s f x) = (term389 A B s f x).
Proof. exact (TRANS (@lem3999504 A B s f x) (@lem3999499 A B s f x)). Qed.
Lemma lem3999506 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term394 A B s f) = (term395 A B s f).
Proof. exact (fun_ext (fun x : A => @lem3999505 A B s f x)). Qed.
Lemma lem3999507 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3999508 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term391 A B s f) = (term396 A B s f).
Proof. exact (MK_COMB (@lem3999507 A) (@lem3999506 A B s f)). Qed.
Lemma lem3999509 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term390 A B s f) = (term396 A B s f).
Proof. exact (TRANS (@lem3999501 A B s f) (@lem3999508 A B s f)). Qed.
Lemma lem3999510 {A : Type'} (s : A -> Prop) : (term197 A s) = (term197 A s).
Proof. exact (eq_refl (term197 A s)). Qed.
Lemma lem3999511 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3999512 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term397 A B s f) = (term398 A B s f).
Proof. exact (MK_COMB (@lem3999511) (@lem3999509 A B s f)). Qed.
Lemma lem3999513 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term399 A B f s) = (term400 A B f s).
Proof. exact (MK_COMB (@lem3999512 A B s f) (@lem3999510 A s)). Qed.
Lemma lem3999514 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term401 A B f s) = (term399 A B f s).
Proof. exact (@lem17045 (term120 A B s f) (@FINITE A s)). Qed.
Lemma lem3999515 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term401 A B f s) = (term400 A B f s).
Proof. exact (TRANS (@lem3999514 A B f s) (@lem3999513 A B f s)). Qed.
Lemma lem3999516 {A B : Type'} (f : A -> B) (s : A -> Prop) : ((term33 A B f s) = (@CARD A s)) = ((term33 A B f s) = (@CARD A s)).
Proof. exact (eq_refl ((term33 A B f s) = (@CARD A s))). Qed.
Lemma lem3999517 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3999518 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term402 A B f s) = (term403 A B f s).
Proof. exact (MK_COMB (@lem3999517) (@lem3999515 A B f s)). Qed.
Lemma lem3999519 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term404 A B f s) = (term405 A B f s).
Proof. exact (MK_COMB (@lem3999518 A B f s) (@lem3999516 A B f s)). Qed.
Lemma lem3999520 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term123 A B f s) = (term404 A B f s).
Proof. exact (@lem17265 (term121 A B f s) ((term33 A B f s) = (@CARD A s))). Qed.
Lemma lem3999521 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term123 A B f s) = (term405 A B f s).
Proof. exact (TRANS (@lem3999520 A B f s) (@lem3999519 A B f s)). Qed.
Lemma lem3999522 {A B : Type'} (f : A -> B) : (term124 A B f) = (term406 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3999521 A B f s)). Qed.
Lemma lem3999523 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3999524 {A B : Type'} (f : A -> B) : (term125 A B f) = (term407 A B f).
Proof. exact (MK_COMB (@lem3999523 A) (@lem3999522 A B f)). Qed.
Lemma lem3999525 {A B : Type'} : (term126 A B) = (term408 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3999524 A B f)). Qed.
Lemma lem3999526 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3999527 {A B : Type'} : (term54 A B) = (term409 A B).
Proof. exact (MK_COMB (@lem3999526 A B) (@lem3999525 A B)). Qed.
Lemma lem3999634 {A : Type'} (P : A -> Prop) (Q : Prop) : (term211 A P Q) = (term212 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3999635 {A : Type'} (P : A -> Prop) (Q : Prop) : (term211 A P Q) = (term212 A P Q).
Proof. exact (@lem3999634 A P Q). Qed.
Lemma lem3999636 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term410 A B f s) = (term411 A B f s).
Proof. exact (@lem3999635 A (term395 A B s f) (term197 A s)). Qed.
Lemma lem3999637 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term412 A B s f x) = (term389 A B s f x).
Proof. exact (eq_refl (term412 A B s f x)). Qed.
Lemma lem3999638 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term413 A B s f) = (term395 A B s f).
Proof. exact (fun_ext (fun x : A => @lem3999637 A B s f x)). Qed.
Lemma lem3999639 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3999640 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term414 A B s f) = (term396 A B s f).
Proof. exact (MK_COMB (@lem3999639 A) (@lem3999638 A B s f)). Qed.
Lemma lem3999641 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3999642 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term415 A B s f) = (term398 A B s f).
Proof. exact (MK_COMB (@lem3999641) (@lem3999640 A B s f)). Qed.
Lemma lem3999643 {A : Type'} (s : A -> Prop) : (term197 A s) = (term197 A s).
Proof. exact (eq_refl (term197 A s)). Qed.
Lemma lem3999644 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term410 A B f s) = (term400 A B f s).
Proof. exact (MK_COMB (@lem3999642 A B s f) (@lem3999643 A s)). Qed.
Lemma lem3999645 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3999646 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term416 A B f s) = (term417 A B f s).
Proof. exact (MK_COMB (@lem3999645) (@lem3999644 A B f s)). Qed.
Lemma lem3999647 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term412 A B s f x) = (term389 A B s f x).
Proof. exact (eq_refl (term412 A B s f x)). Qed.
Lemma lem3999648 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3999649 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term418 A B s f x) = (term419 A B s f x).
Proof. exact (MK_COMB (@lem3999648) (@lem3999647 A B s f x)). Qed.
Lemma lem3999650 {A : Type'} (s : A -> Prop) : (term197 A s) = (term197 A s).
Proof. exact (eq_refl (term197 A s)). Qed.
Lemma lem3999651 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : (term420 A B f x s) = (term421 A B f x s).
Proof. exact (MK_COMB (@lem3999649 A B s f x) (@lem3999650 A s)). Qed.
Lemma lem3999652 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term422 A B f s) = (term423 A B f s).
Proof. exact (fun_ext (fun x : A => @lem3999651 A B f x s)). Qed.
Lemma lem3999653 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3999654 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term411 A B f s) = (term424 A B f s).
Proof. exact (MK_COMB (@lem3999653 A) (@lem3999652 A B f s)). Qed.
Lemma lem3999655 {A B : Type'} (f : A -> B) (s : A -> Prop) : ((term410 A B f s) = (term411 A B f s)) = ((term400 A B f s) = (term424 A B f s)).
Proof. exact (MK_COMB (@lem3999646 A B f s) (@lem3999654 A B f s)). Qed.
Lemma lem3999656 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term400 A B f s) = (term424 A B f s).
Proof. exact (EQ_MP (@lem3999655 A B f s) (@lem3999636 A B f s)). Qed.
Lemma lem3999658 {A : Type'} (P : A -> Prop) (Q : Prop) : (term211 A P Q) = (term212 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3999659 {A : Type'} (P : A -> Prop) (Q : Prop) : (term211 A P Q) = (term212 A P Q).
Proof. exact (@lem3999658 A P Q). Qed.
Lemma lem3999660 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : (term425 A B f x s) = (term426 A B f x s).
Proof. exact (@lem3999659 A (term388 A B s f x) (term197 A s)). Qed.
Lemma lem3999661 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term427 A B s f x y) = (term382 A B s f x y).
Proof. exact (eq_refl (term427 A B s f x y)). Qed.
Lemma lem3999662 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term428 A B s f x) = (term388 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem3999661 A B s f x y)). Qed.
Lemma lem3999663 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3999664 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term429 A B s f x) = (term389 A B s f x).
Proof. exact (MK_COMB (@lem3999663 A) (@lem3999662 A B s f x)). Qed.
Lemma lem3999665 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3999666 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term430 A B s f x) = (term419 A B s f x).
Proof. exact (MK_COMB (@lem3999665) (@lem3999664 A B s f x)). Qed.
Lemma lem3999667 {A : Type'} (s : A -> Prop) : (term197 A s) = (term197 A s).
Proof. exact (eq_refl (term197 A s)). Qed.
Lemma lem3999668 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : (term425 A B f x s) = (term421 A B f x s).
Proof. exact (MK_COMB (@lem3999666 A B s f x) (@lem3999667 A s)). Qed.
Lemma lem3999669 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3999670 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : (term431 A B f x s) = (term432 A B f x s).
Proof. exact (MK_COMB (@lem3999669) (@lem3999668 A B f x s)). Qed.
Lemma lem3999671 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term427 A B s f x y) = (term382 A B s f x y).
Proof. exact (eq_refl (term427 A B s f x y)). Qed.
Lemma lem3999672 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3999673 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term433 A B s f x y) = (term434 A B s f x y).
Proof. exact (MK_COMB (@lem3999672) (@lem3999671 A B s f x y)). Qed.
Lemma lem3999674 {A : Type'} (s : A -> Prop) : (term197 A s) = (term197 A s).
Proof. exact (eq_refl (term197 A s)). Qed.
Lemma lem3999675 {A B : Type'} (f : A -> B) (x : A) (y : A) (s : A -> Prop) : (term435 A B f x y s) = (term436 A B f x y s).
Proof. exact (MK_COMB (@lem3999673 A B s f x y) (@lem3999674 A s)). Qed.
Lemma lem3999676 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : (term437 A B f x s) = (term438 A B f x s).
Proof. exact (fun_ext (fun y : A => @lem3999675 A B f x y s)). Qed.
Lemma lem3999677 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3999678 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : (term426 A B f x s) = (term439 A B f x s).
Proof. exact (MK_COMB (@lem3999677 A) (@lem3999676 A B f x s)). Qed.
Lemma lem3999679 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : ((term425 A B f x s) = (term426 A B f x s)) = ((term421 A B f x s) = (term439 A B f x s)).
Proof. exact (MK_COMB (@lem3999670 A B f x s) (@lem3999678 A B f x s)). Qed.
Lemma lem3999680 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : (term421 A B f x s) = (term439 A B f x s).
Proof. exact (EQ_MP (@lem3999679 A B f x s) (@lem3999660 A B f x s)). Qed.
Lemma lem3999681 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term423 A B f s) = (term440 A B f s).
Proof. exact (fun_ext (fun x : A => @lem3999680 A B f x s)). Qed.
Lemma lem3999682 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3999683 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term424 A B f s) = (term441 A B f s).
Proof. exact (MK_COMB (@lem3999682 A) (@lem3999681 A B f s)). Qed.
Lemma lem3999684 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term400 A B f s) = (term441 A B f s).
Proof. exact (TRANS (@lem3999656 A B f s) (@lem3999683 A B f s)). Qed.
Lemma lem3999685 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3999686 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term403 A B f s) = (term442 A B f s).
Proof. exact (MK_COMB (@lem3999685) (@lem3999684 A B f s)). Qed.
Lemma lem3999687 {A B : Type'} (f : A -> B) (s : A -> Prop) : ((term33 A B f s) = (@CARD A s)) = ((term33 A B f s) = (@CARD A s)).
Proof. exact (eq_refl ((term33 A B f s) = (@CARD A s))). Qed.
Lemma lem3999688 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term405 A B f s) = (term443 A B f s).
Proof. exact (MK_COMB (@lem3999686 A B f s) (@lem3999687 A B f s)). Qed.
Lemma lem3999690 {A : Type'} (P : A -> Prop) (Q : Prop) : (term211 A P Q) = (term212 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3999691 {A : Type'} (P : A -> Prop) (Q : Prop) : (term211 A P Q) = (term212 A P Q).
Proof. exact (@lem3999690 A P Q). Qed.
Lemma lem3999692 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term444 A B f s) = (term445 A B f s).
Proof. exact (@lem3999691 A (term440 A B f s) ((term33 A B f s) = (@CARD A s))). Qed.
Lemma lem3999693 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : (term446 A B f s x) = (term439 A B f x s).
Proof. exact (eq_refl (term446 A B f s x)). Qed.
Lemma lem3999694 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term447 A B f s) = (term440 A B f s).
Proof. exact (fun_ext (fun x : A => @lem3999693 A B f x s)). Qed.
Lemma lem3999695 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3999696 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term448 A B f s) = (term441 A B f s).
Proof. exact (MK_COMB (@lem3999695 A) (@lem3999694 A B f s)). Qed.
Lemma lem3999697 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3999698 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term449 A B f s) = (term442 A B f s).
Proof. exact (MK_COMB (@lem3999697) (@lem3999696 A B f s)). Qed.
Lemma lem3999699 {A B : Type'} (f : A -> B) (s : A -> Prop) : ((term33 A B f s) = (@CARD A s)) = ((term33 A B f s) = (@CARD A s)).
Proof. exact (eq_refl ((term33 A B f s) = (@CARD A s))). Qed.
Lemma lem3999700 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term444 A B f s) = (term443 A B f s).
Proof. exact (MK_COMB (@lem3999698 A B f s) (@lem3999699 A B f s)). Qed.
Lemma lem3999701 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3999702 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term450 A B f s) = (term451 A B f s).
Proof. exact (MK_COMB (@lem3999701) (@lem3999700 A B f s)). Qed.
Lemma lem3999703 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : (term446 A B f s x) = (term439 A B f x s).
Proof. exact (eq_refl (term446 A B f s x)). Qed.
Lemma lem3999704 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3999705 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : (term452 A B f s x) = (term453 A B f x s).
Proof. exact (MK_COMB (@lem3999704) (@lem3999703 A B f x s)). Qed.
Lemma lem3999706 {A B : Type'} (f : A -> B) (s : A -> Prop) : ((term33 A B f s) = (@CARD A s)) = ((term33 A B f s) = (@CARD A s)).
Proof. exact (eq_refl ((term33 A B f s) = (@CARD A s))). Qed.
Lemma lem3999707 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term454 A B x f s) = (term455 A B x f s).
Proof. exact (MK_COMB (@lem3999705 A B f x s) (@lem3999706 A B f s)). Qed.
Lemma lem3999708 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term456 A B f s) = (term457 A B f s).
Proof. exact (fun_ext (fun x : A => @lem3999707 A B x f s)). Qed.
Lemma lem3999709 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3999710 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term445 A B f s) = (term458 A B f s).
Proof. exact (MK_COMB (@lem3999709 A) (@lem3999708 A B f s)). Qed.
Lemma lem3999711 {A B : Type'} (f : A -> B) (s : A -> Prop) : ((term444 A B f s) = (term445 A B f s)) = ((term443 A B f s) = (term458 A B f s)).
Proof. exact (MK_COMB (@lem3999702 A B f s) (@lem3999710 A B f s)). Qed.
Lemma lem3999712 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term443 A B f s) = (term458 A B f s).
Proof. exact (EQ_MP (@lem3999711 A B f s) (@lem3999692 A B f s)). Qed.
Lemma lem3999714 {A : Type'} (P : A -> Prop) (Q : Prop) : (term211 A P Q) = (term212 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3999715 {A : Type'} (P : A -> Prop) (Q : Prop) : (term211 A P Q) = (term212 A P Q).
Proof. exact (@lem3999714 A P Q). Qed.
Lemma lem3999716 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term459 A B x f s) = (term460 A B x f s).
Proof. exact (@lem3999715 A (term438 A B f x s) ((term33 A B f s) = (@CARD A s))). Qed.
Lemma lem3999717 {A B : Type'} (f : A -> B) (x : A) (y : A) (s : A -> Prop) : (term461 A B f x s y) = (term436 A B f x y s).
Proof. exact (eq_refl (term461 A B f x s y)). Qed.
Lemma lem3999718 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : (term462 A B f x s) = (term438 A B f x s).
Proof. exact (fun_ext (fun y : A => @lem3999717 A B f x y s)). Qed.
Lemma lem3999719 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3999720 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : (term463 A B f x s) = (term439 A B f x s).
Proof. exact (MK_COMB (@lem3999719 A) (@lem3999718 A B f x s)). Qed.
Lemma lem3999721 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3999722 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : (term464 A B f x s) = (term453 A B f x s).
Proof. exact (MK_COMB (@lem3999721) (@lem3999720 A B f x s)). Qed.
Lemma lem3999723 {A B : Type'} (f : A -> B) (s : A -> Prop) : ((term33 A B f s) = (@CARD A s)) = ((term33 A B f s) = (@CARD A s)).
Proof. exact (eq_refl ((term33 A B f s) = (@CARD A s))). Qed.
Lemma lem3999724 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term459 A B x f s) = (term455 A B x f s).
Proof. exact (MK_COMB (@lem3999722 A B f x s) (@lem3999723 A B f s)). Qed.
Lemma lem3999725 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3999726 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term465 A B x f s) = (term466 A B x f s).
Proof. exact (MK_COMB (@lem3999725) (@lem3999724 A B x f s)). Qed.
Lemma lem3999727 {A B : Type'} (f : A -> B) (x : A) (y : A) (s : A -> Prop) : (term461 A B f x s y) = (term436 A B f x y s).
Proof. exact (eq_refl (term461 A B f x s y)). Qed.
Lemma lem3999728 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3999729 {A B : Type'} (f : A -> B) (x : A) (y : A) (s : A -> Prop) : (term467 A B f x s y) = (term468 A B f x y s).
Proof. exact (MK_COMB (@lem3999728) (@lem3999727 A B f x y s)). Qed.
Lemma lem3999730 {A B : Type'} (f : A -> B) (s : A -> Prop) : ((term33 A B f s) = (@CARD A s)) = ((term33 A B f s) = (@CARD A s)).
Proof. exact (eq_refl ((term33 A B f s) = (@CARD A s))). Qed.
Lemma lem3999731 {A B : Type'} (x : A) (y : A) (f : A -> B) (s : A -> Prop) : (term469 A B x y f s) = (term470 A B x y f s).
Proof. exact (MK_COMB (@lem3999729 A B f x y s) (@lem3999730 A B f s)). Qed.
Lemma lem3999732 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term471 A B x f s) = (term472 A B x f s).
Proof. exact (fun_ext (fun y : A => @lem3999731 A B x y f s)). Qed.
Lemma lem3999733 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3999734 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term460 A B x f s) = (term473 A B x f s).
Proof. exact (MK_COMB (@lem3999733 A) (@lem3999732 A B x f s)). Qed.
Lemma lem3999735 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : ((term459 A B x f s) = (term460 A B x f s)) = ((term455 A B x f s) = (term473 A B x f s)).
Proof. exact (MK_COMB (@lem3999726 A B x f s) (@lem3999734 A B x f s)). Qed.
Lemma lem3999736 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term455 A B x f s) = (term473 A B x f s).
Proof. exact (EQ_MP (@lem3999735 A B x f s) (@lem3999716 A B x f s)). Qed.
Lemma lem3999737 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term457 A B f s) = (term474 A B f s).
Proof. exact (fun_ext (fun x : A => @lem3999736 A B x f s)). Qed.
Lemma lem3999738 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3999739 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term458 A B f s) = (term475 A B f s).
Proof. exact (MK_COMB (@lem3999738 A) (@lem3999737 A B f s)). Qed.
Lemma lem3999740 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term443 A B f s) = (term475 A B f s).
Proof. exact (TRANS (@lem3999712 A B f s) (@lem3999739 A B f s)). Qed.
Lemma lem3999741 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term405 A B f s) = (term475 A B f s).
Proof. exact (TRANS (@lem3999688 A B f s) (@lem3999740 A B f s)). Qed.
Lemma lem3999742 {A B : Type'} (f : A -> B) : (term406 A B f) = (term476 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3999741 A B f s)). Qed.
Lemma lem3999743 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3999744 {A B : Type'} (f : A -> B) : (term407 A B f) = (term477 A B f).
Proof. exact (MK_COMB (@lem3999743 A) (@lem3999742 A B f)). Qed.
Lemma lem3999746 {A B : Type'} (P : type1413 A B) : (term281 A B P) = (term282 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3999747 {A : Type'} (P : type672 A) : (term283 A P) = (term284 A P).
Proof. exact (@lem3999746 (A -> Prop) A P). Qed.
Lemma lem3999748 {A B : Type'} (f : A -> B) : (term478 A B f) = (term479 A B f).
Proof. exact (@lem3999747 A (term480 A B f)). Qed.
Lemma lem3999749 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term481 A B f s) = (term474 A B f s).
Proof. exact (eq_refl (term481 A B f s)). Qed.
Lemma lem3999750 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3999751 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term482 A B f s x) = (term483 A B f s x).
Proof. exact (MK_COMB (@lem3999749 A B f s) (@lem3999750 A x)). Qed.
Lemma lem3999752 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term483 A B f s x) = (term473 A B x f s).
Proof. exact (eq_refl (term483 A B f s x)). Qed.
Lemma lem3999753 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term482 A B f s x) = (term473 A B x f s).
Proof. exact (TRANS (@lem3999751 A B f s x) (@lem3999752 A B x f s)). Qed.
Lemma lem3999754 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term484 A B f s) = (term474 A B f s).
Proof. exact (fun_ext (fun x : A => @lem3999753 A B x f s)). Qed.
Lemma lem3999755 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3999756 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term485 A B f s) = (term475 A B f s).
Proof. exact (MK_COMB (@lem3999755 A) (@lem3999754 A B f s)). Qed.
Lemma lem3999757 {A B : Type'} (f : A -> B) : (term486 A B f) = (term476 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3999756 A B f s)). Qed.
Lemma lem3999758 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3999759 {A B : Type'} (f : A -> B) : (term478 A B f) = (term477 A B f).
Proof. exact (MK_COMB (@lem3999758 A) (@lem3999757 A B f)). Qed.
Lemma lem3999760 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3999761 {A B : Type'} (f : A -> B) : (term487 A B f) = (term488 A B f).
Proof. exact (MK_COMB (@lem3999760) (@lem3999759 A B f)). Qed.
Lemma lem3999762 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term481 A B f s) = (term474 A B f s).
Proof. exact (eq_refl (term481 A B f s)). Qed.
Lemma lem3999763 {A : Type'} (x : type684 A) (s : A -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem3999764 {A B : Type'} (f : A -> B) (x : type684 A) (s : A -> Prop) : (term489 A B f x s) = (term490 A B f x s).
Proof. exact (MK_COMB (@lem3999762 A B f s) (@lem3999763 A x s)). Qed.
Lemma lem3999765 {A B : Type'} (x : type684 A) (f : A -> B) (s : A -> Prop) : (term490 A B f x s) = (term491 A B x f s).
Proof. exact (eq_refl (term490 A B f x s)). Qed.
Lemma lem3999766 {A B : Type'} (x : type684 A) (f : A -> B) (s : A -> Prop) : (term489 A B f x s) = (term491 A B x f s).
Proof. exact (TRANS (@lem3999764 A B f x s) (@lem3999765 A B x f s)). Qed.
Lemma lem3999767 {A B : Type'} (x : type684 A) (f : A -> B) : (term492 A B f x) = (term493 A B x f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3999766 A B x f s)). Qed.
Lemma lem3999768 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3999769 {A B : Type'} (x : type684 A) (f : A -> B) : (term494 A B f x) = (term495 A B x f).
Proof. exact (MK_COMB (@lem3999768 A) (@lem3999767 A B x f)). Qed.
Lemma lem3999770 {A B : Type'} (f : A -> B) : (term496 A B f) = (term497 A B f).
Proof. exact (fun_ext (fun x : type684 A => @lem3999769 A B x f)). Qed.
Lemma lem3999771 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem3999772 {A B : Type'} (f : A -> B) : (term479 A B f) = (term498 A B f).
Proof. exact (MK_COMB (@lem3999771 A) (@lem3999770 A B f)). Qed.
Lemma lem3999773 {A B : Type'} (f : A -> B) : ((term478 A B f) = (term479 A B f)) = ((term477 A B f) = (term498 A B f)).
Proof. exact (MK_COMB (@lem3999761 A B f) (@lem3999772 A B f)). Qed.
Lemma lem3999774 {A B : Type'} (f : A -> B) : (term477 A B f) = (term498 A B f).
Proof. exact (EQ_MP (@lem3999773 A B f) (@lem3999748 A B f)). Qed.
Lemma lem3999776 {A B : Type'} (P : type1413 A B) : (term281 A B P) = (term282 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3999777 {A : Type'} (P : type672 A) : (term283 A P) = (term284 A P).
Proof. exact (@lem3999776 (A -> Prop) A P). Qed.
Lemma lem3999778 {A B : Type'} (x : type684 A) (f : A -> B) : (term499 A B x f) = (term500 A B x f).
Proof. exact (@lem3999777 A (term501 A B x f)). Qed.
Lemma lem3999779 {A B : Type'} (x : type684 A) (f : A -> B) (s : A -> Prop) : (term502 A B x f s) = (term503 A B x f s).
Proof. exact (eq_refl (term502 A B x f s)). Qed.
Lemma lem3999780 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem3999781 {A B : Type'} (x : type684 A) (f : A -> B) (s : A -> Prop) (y : A) : (term504 A B x f s y) = (term505 A B x f s y).
Proof. exact (MK_COMB (@lem3999779 A B x f s) (@lem3999780 A y)). Qed.
Lemma lem3999782 {A B : Type'} (x : type684 A) (y : A) (f : A -> B) (s : A -> Prop) : (term505 A B x f s y) = (term506 A B x y f s).
Proof. exact (eq_refl (term505 A B x f s y)). Qed.
Lemma lem3999783 {A B : Type'} (x : type684 A) (y : A) (f : A -> B) (s : A -> Prop) : (term504 A B x f s y) = (term506 A B x y f s).
Proof. exact (TRANS (@lem3999781 A B x f s y) (@lem3999782 A B x y f s)). Qed.
Lemma lem3999784 {A B : Type'} (x : type684 A) (f : A -> B) (s : A -> Prop) : (term507 A B x f s) = (term503 A B x f s).
Proof. exact (fun_ext (fun y : A => @lem3999783 A B x y f s)). Qed.
Lemma lem3999785 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3999786 {A B : Type'} (x : type684 A) (f : A -> B) (s : A -> Prop) : (term508 A B x f s) = (term491 A B x f s).
Proof. exact (MK_COMB (@lem3999785 A) (@lem3999784 A B x f s)). Qed.
Lemma lem3999787 {A B : Type'} (x : type684 A) (f : A -> B) : (term509 A B x f) = (term493 A B x f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3999786 A B x f s)). Qed.
Lemma lem3999788 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3999789 {A B : Type'} (x : type684 A) (f : A -> B) : (term499 A B x f) = (term495 A B x f).
Proof. exact (MK_COMB (@lem3999788 A) (@lem3999787 A B x f)). Qed.
Lemma lem3999790 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3999791 {A B : Type'} (x : type684 A) (f : A -> B) : (term510 A B x f) = (term511 A B x f).
Proof. exact (MK_COMB (@lem3999790) (@lem3999789 A B x f)). Qed.
Lemma lem3999792 {A B : Type'} (x : type684 A) (f : A -> B) (s : A -> Prop) : (term502 A B x f s) = (term503 A B x f s).
Proof. exact (eq_refl (term502 A B x f s)). Qed.
Lemma lem3999793 {A : Type'} (y : type684 A) (s : A -> Prop) : (y s) = (y s).
Proof. exact (eq_refl (y s)). Qed.
Lemma lem3999794 {A B : Type'} (x : type684 A) (f : A -> B) (y : type684 A) (s : A -> Prop) : (term512 A B x f y s) = (term513 A B x f y s).
Proof. exact (MK_COMB (@lem3999792 A B x f s) (@lem3999793 A y s)). Qed.
Lemma lem3999795 {A B : Type'} (x : type684 A) (y : type684 A) (f : A -> B) (s : A -> Prop) : (term513 A B x f y s) = (term514 A B x y f s).
Proof. exact (eq_refl (term513 A B x f y s)). Qed.
Lemma lem3999796 {A B : Type'} (x : type684 A) (y : type684 A) (f : A -> B) (s : A -> Prop) : (term512 A B x f y s) = (term514 A B x y f s).
Proof. exact (TRANS (@lem3999794 A B x f y s) (@lem3999795 A B x y f s)). Qed.
Lemma lem3999797 {A B : Type'} (x : type684 A) (y : type684 A) (f : A -> B) : (term515 A B x f y) = (term516 A B x y f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3999796 A B x y f s)). Qed.
Lemma lem3999798 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3999799 {A B : Type'} (x : type684 A) (y : type684 A) (f : A -> B) : (term517 A B x f y) = (term518 A B x y f).
Proof. exact (MK_COMB (@lem3999798 A) (@lem3999797 A B x y f)). Qed.
Lemma lem3999800 {A B : Type'} (x : type684 A) (f : A -> B) : (term519 A B x f) = (term520 A B x f).
Proof. exact (fun_ext (fun y : type684 A => @lem3999799 A B x y f)). Qed.
Lemma lem3999801 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem3999802 {A B : Type'} (x : type684 A) (f : A -> B) : (term500 A B x f) = (term521 A B x f).
Proof. exact (MK_COMB (@lem3999801 A) (@lem3999800 A B x f)). Qed.
Lemma lem3999803 {A B : Type'} (x : type684 A) (f : A -> B) : ((term499 A B x f) = (term500 A B x f)) = ((term495 A B x f) = (term521 A B x f)).
Proof. exact (MK_COMB (@lem3999791 A B x f) (@lem3999802 A B x f)). Qed.
Lemma lem3999804 {A B : Type'} (x : type684 A) (f : A -> B) : (term495 A B x f) = (term521 A B x f).
Proof. exact (EQ_MP (@lem3999803 A B x f) (@lem3999778 A B x f)). Qed.
Lemma lem3999805 {A B : Type'} (f : A -> B) : (term497 A B f) = (term522 A B f).
Proof. exact (fun_ext (fun x : type684 A => @lem3999804 A B x f)). Qed.
Lemma lem3999806 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem3999807 {A B : Type'} (f : A -> B) : (term498 A B f) = (term523 A B f).
Proof. exact (MK_COMB (@lem3999806 A) (@lem3999805 A B f)). Qed.
Lemma lem3999808 {A B : Type'} (f : A -> B) : (term477 A B f) = (term523 A B f).
Proof. exact (TRANS (@lem3999774 A B f) (@lem3999807 A B f)). Qed.
Lemma lem3999809 {A B : Type'} (f : A -> B) : (term407 A B f) = (term523 A B f).
Proof. exact (TRANS (@lem3999744 A B f) (@lem3999808 A B f)). Qed.
Lemma lem3999810 {A B : Type'} : (term408 A B) = (term524 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3999809 A B f)). Qed.
Lemma lem3999811 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3999812 {A B : Type'} : (term409 A B) = (term525 A B).
Proof. exact (MK_COMB (@lem3999811 A B) (@lem3999810 A B)). Qed.
Lemma lem3999814 {A B : Type'} (P : type1413 A B) : (term281 A B P) = (term282 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3999815 {A B : Type'} (P : type503 A B) : (term526 A B P) = (term527 A B P).
Proof. exact (@lem3999814 (A -> B) (type684 A) P). Qed.
Lemma lem3999816 {A B : Type'} : (term528 A B) = (term529 A B).
Proof. exact (@lem3999815 A B (term530 A B)). Qed.
Lemma lem3999817 {A B : Type'} (f : A -> B) : (term531 A B f) = (term522 A B f).
Proof. exact (eq_refl (term531 A B f)). Qed.
Lemma lem3999818 {A : Type'} (x : type684 A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3999819 {A B : Type'} (f : A -> B) (x : type684 A) : (term532 A B f x) = (term533 A B f x).
Proof. exact (MK_COMB (@lem3999817 A B f) (@lem3999818 A x)). Qed.
Lemma lem3999820 {A B : Type'} (x : type684 A) (f : A -> B) : (term533 A B f x) = (term521 A B x f).
Proof. exact (eq_refl (term533 A B f x)). Qed.
Lemma lem3999821 {A B : Type'} (x : type684 A) (f : A -> B) : (term532 A B f x) = (term521 A B x f).
Proof. exact (TRANS (@lem3999819 A B f x) (@lem3999820 A B x f)). Qed.
Lemma lem3999822 {A B : Type'} (f : A -> B) : (term534 A B f) = (term522 A B f).
Proof. exact (fun_ext (fun x : type684 A => @lem3999821 A B x f)). Qed.
Lemma lem3999823 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem3999824 {A B : Type'} (f : A -> B) : (term535 A B f) = (term523 A B f).
Proof. exact (MK_COMB (@lem3999823 A) (@lem3999822 A B f)). Qed.
Lemma lem3999825 {A B : Type'} : (term536 A B) = (term524 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3999824 A B f)). Qed.
Lemma lem3999826 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3999827 {A B : Type'} : (term528 A B) = (term525 A B).
Proof. exact (MK_COMB (@lem3999826 A B) (@lem3999825 A B)). Qed.
Lemma lem3999828 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3999829 {A B : Type'} : (term537 A B) = (term538 A B).
Proof. exact (MK_COMB (@lem3999828) (@lem3999827 A B)). Qed.
Lemma lem3999830 {A B : Type'} (f : A -> B) : (term531 A B f) = (term522 A B f).
Proof. exact (eq_refl (term531 A B f)). Qed.
Lemma lem3999831 {A B : Type'} (x : type529 A B) (f : A -> B) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem3999832 {A B : Type'} (x : type529 A B) (f : A -> B) : (term539 A B x f) = (term540 A B x f).
Proof. exact (MK_COMB (@lem3999830 A B f) (@lem3999831 A B x f)). Qed.
Lemma lem3999833 {A B : Type'} (x : type529 A B) (f : A -> B) : (term540 A B x f) = (term541 A B x f).
Proof. exact (eq_refl (term540 A B x f)). Qed.
Lemma lem3999834 {A B : Type'} (x : type529 A B) (f : A -> B) : (term539 A B x f) = (term541 A B x f).
Proof. exact (TRANS (@lem3999832 A B x f) (@lem3999833 A B x f)). Qed.
Lemma lem3999835 {A B : Type'} (x : type529 A B) : (term542 A B x) = (term543 A B x).
Proof. exact (fun_ext (fun f : A -> B => @lem3999834 A B x f)). Qed.
Lemma lem3999836 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3999837 {A B : Type'} (x : type529 A B) : (term544 A B x) = (term545 A B x).
Proof. exact (MK_COMB (@lem3999836 A B) (@lem3999835 A B x)). Qed.
Lemma lem3999838 {A B : Type'} : (term546 A B) = (term547 A B).
Proof. exact (fun_ext (fun x : type529 A B => @lem3999837 A B x)). Qed.
Lemma lem3999839 {A B : Type'} : (@ex ((A -> B) -> (A -> Prop) -> A)) = (@ex ((A -> B) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> (A -> Prop) -> A))). Qed.
Lemma lem3999840 {A B : Type'} : (term529 A B) = (term548 A B).
Proof. exact (MK_COMB (@lem3999839 A B) (@lem3999838 A B)). Qed.
Lemma lem3999841 {A B : Type'} : ((term528 A B) = (term529 A B)) = ((term525 A B) = (term548 A B)).
Proof. exact (MK_COMB (@lem3999829 A B) (@lem3999840 A B)). Qed.
Lemma lem3999842 {A B : Type'} : (term525 A B) = (term548 A B).
Proof. exact (EQ_MP (@lem3999841 A B) (@lem3999816 A B)). Qed.
Lemma lem3999844 {A B : Type'} (P : type1413 A B) : (term281 A B P) = (term282 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3999845 {A B : Type'} (P : type503 A B) : (term526 A B P) = (term527 A B P).
Proof. exact (@lem3999844 (A -> B) (type684 A) P). Qed.
Lemma lem3999846 {A B : Type'} (x : type529 A B) : (term549 A B x) = (term550 A B x).
Proof. exact (@lem3999845 A B (term551 A B x)). Qed.
Lemma lem3999847 {A B : Type'} (x : type529 A B) (f : A -> B) : (term552 A B x f) = (term553 A B x f).
Proof. exact (eq_refl (term552 A B x f)). Qed.
Lemma lem3999848 {A : Type'} (y : type684 A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem3999849 {A B : Type'} (x : type529 A B) (f : A -> B) (y : type684 A) : (term554 A B x f y) = (term555 A B x f y).
Proof. exact (MK_COMB (@lem3999847 A B x f) (@lem3999848 A y)). Qed.
Lemma lem3999850 {A B : Type'} (x : type529 A B) (y : type684 A) (f : A -> B) : (term555 A B x f y) = (term556 A B x y f).
Proof. exact (eq_refl (term555 A B x f y)). Qed.
Lemma lem3999851 {A B : Type'} (x : type529 A B) (y : type684 A) (f : A -> B) : (term554 A B x f y) = (term556 A B x y f).
Proof. exact (TRANS (@lem3999849 A B x f y) (@lem3999850 A B x y f)). Qed.
Lemma lem3999852 {A B : Type'} (x : type529 A B) (f : A -> B) : (term557 A B x f) = (term553 A B x f).
Proof. exact (fun_ext (fun y : type684 A => @lem3999851 A B x y f)). Qed.
Lemma lem3999853 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem3999854 {A B : Type'} (x : type529 A B) (f : A -> B) : (term558 A B x f) = (term541 A B x f).
Proof. exact (MK_COMB (@lem3999853 A) (@lem3999852 A B x f)). Qed.
Lemma lem3999855 {A B : Type'} (x : type529 A B) : (term559 A B x) = (term543 A B x).
Proof. exact (fun_ext (fun f : A -> B => @lem3999854 A B x f)). Qed.
Lemma lem3999856 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3999857 {A B : Type'} (x : type529 A B) : (term549 A B x) = (term545 A B x).
Proof. exact (MK_COMB (@lem3999856 A B) (@lem3999855 A B x)). Qed.
Lemma lem3999858 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3999859 {A B : Type'} (x : type529 A B) : (term560 A B x) = (term561 A B x).
Proof. exact (MK_COMB (@lem3999858) (@lem3999857 A B x)). Qed.
Lemma lem3999860 {A B : Type'} (x : type529 A B) (f : A -> B) : (term552 A B x f) = (term553 A B x f).
Proof. exact (eq_refl (term552 A B x f)). Qed.
Lemma lem3999861 {A B : Type'} (y : type529 A B) (f : A -> B) : (y f) = (y f).
Proof. exact (eq_refl (y f)). Qed.
Lemma lem3999862 {A B : Type'} (x : type529 A B) (y : type529 A B) (f : A -> B) : (term562 A B x y f) = (term563 A B x y f).
Proof. exact (MK_COMB (@lem3999860 A B x f) (@lem3999861 A B y f)). Qed.
Lemma lem3999863 {A B : Type'} (x : type529 A B) (y : type529 A B) (f : A -> B) : (term563 A B x y f) = (term564 A B x y f).
Proof. exact (eq_refl (term563 A B x y f)). Qed.
Lemma lem3999864 {A B : Type'} (x : type529 A B) (y : type529 A B) (f : A -> B) : (term562 A B x y f) = (term564 A B x y f).
Proof. exact (TRANS (@lem3999862 A B x y f) (@lem3999863 A B x y f)). Qed.
Lemma lem3999865 {A B : Type'} (x : type529 A B) (y : type529 A B) : (term565 A B x y) = (term566 A B x y).
Proof. exact (fun_ext (fun f : A -> B => @lem3999864 A B x y f)). Qed.
Lemma lem3999866 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3999867 {A B : Type'} (x : type529 A B) (y : type529 A B) : (term567 A B x y) = (term568 A B x y).
Proof. exact (MK_COMB (@lem3999866 A B) (@lem3999865 A B x y)). Qed.
Lemma lem3999868 {A B : Type'} (x : type529 A B) : (term569 A B x) = (term570 A B x).
Proof. exact (fun_ext (fun y : type529 A B => @lem3999867 A B x y)). Qed.
Lemma lem3999869 {A B : Type'} : (@ex ((A -> B) -> (A -> Prop) -> A)) = (@ex ((A -> B) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> (A -> Prop) -> A))). Qed.
Lemma lem3999870 {A B : Type'} (x : type529 A B) : (term550 A B x) = (term571 A B x).
Proof. exact (MK_COMB (@lem3999869 A B) (@lem3999868 A B x)). Qed.
Lemma lem3999871 {A B : Type'} (x : type529 A B) : ((term549 A B x) = (term550 A B x)) = ((term545 A B x) = (term571 A B x)).
Proof. exact (MK_COMB (@lem3999859 A B x) (@lem3999870 A B x)). Qed.
Lemma lem3999872 {A B : Type'} (x : type529 A B) : (term545 A B x) = (term571 A B x).
Proof. exact (EQ_MP (@lem3999871 A B x) (@lem3999846 A B x)). Qed.
Lemma lem3999873 {A B : Type'} : (term547 A B) = (term572 A B).
Proof. exact (fun_ext (fun x : type529 A B => @lem3999872 A B x)). Qed.
Lemma lem3999874 {A B : Type'} : (@ex ((A -> B) -> (A -> Prop) -> A)) = (@ex ((A -> B) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> (A -> Prop) -> A))). Qed.
Lemma lem3999875 {A B : Type'} : (term548 A B) = (term573 A B).
Proof. exact (MK_COMB (@lem3999874 A B) (@lem3999873 A B)). Qed.
Lemma lem3999876 {A B : Type'} : (term525 A B) = (term573 A B).
Proof. exact (TRANS (@lem3999842 A B) (@lem3999875 A B)). Qed.
Lemma lem3999878 {A B : Type'} : (term409 A B) = (term573 A B).
Proof. exact (TRANS (@lem3999812 A B) (@lem3999876 A B)). Qed.
Lemma lem3999879 {A B : Type'} : (term54 A B) = (term573 A B).
Proof. exact (TRANS (@lem3999527 A B) (@lem3999878 A B)). Qed.
Lemma lem3999880 {A B : Type'} (h1 : term54 A B) : term573 A B.
Proof. exact (EQ_MP (@lem3999879 A B) (@lem3998883 A B h1)). Qed.
Lemma lem3999895 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (y : A) : (term574 A s f x y) = (term575 A s f x y).
Proof. exact (@lem17362 (term576 A s x f y) (x = y)). Qed.
Lemma lem3999896 {A : Type'} (P : A -> Prop) : (term181 A P) = (term182 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3999897 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : (term577 A s f x) = (term578 A s f x).
Proof. exact (@lem3999896 A (term105 A s f x)). Qed.
Lemma lem3999898 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (y : A) : (term579 A s f x y) = (term104 A s f x y).
Proof. exact (eq_refl (term579 A s f x y)). Qed.
Lemma lem3999899 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3999900 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (y : A) : (term580 A s f x y) = (term574 A s f x y).
Proof. exact (MK_COMB (@lem3999899) (@lem3999898 A s f x y)). Qed.
Lemma lem3999901 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (y : A) : (term580 A s f x y) = (term575 A s f x y).
Proof. exact (TRANS (@lem3999900 A s f x y) (@lem3999895 A s f x y)). Qed.
Lemma lem3999902 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : (term581 A s f x) = (term582 A s f x).
Proof. exact (fun_ext (fun y : A => @lem3999901 A s f x y)). Qed.
Lemma lem3999903 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3999904 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : (term578 A s f x) = (term583 A s f x).
Proof. exact (MK_COMB (@lem3999903 A) (@lem3999902 A s f x)). Qed.
Lemma lem3999905 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : (term577 A s f x) = (term583 A s f x).
Proof. exact (TRANS (@lem3999897 A s f x) (@lem3999904 A s f x)). Qed.
Lemma lem3999906 {A : Type'} (P : A -> Prop) : (term181 A P) = (term182 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3999907 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term584 A s f) = (term585 A s f).
Proof. exact (@lem3999906 A (term107 A s f)). Qed.
Lemma lem3999908 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : (term586 A s f x) = (term106 A s f x).
Proof. exact (eq_refl (term586 A s f x)). Qed.
Lemma lem3999909 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3999910 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : (term587 A s f x) = (term577 A s f x).
Proof. exact (MK_COMB (@lem3999909) (@lem3999908 A s f x)). Qed.
Lemma lem3999911 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : (term587 A s f x) = (term583 A s f x).
Proof. exact (TRANS (@lem3999910 A s f x) (@lem3999905 A s f x)). Qed.
Lemma lem3999912 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term588 A s f) = (term589 A s f).
Proof. exact (fun_ext (fun x : A => @lem3999911 A s f x)). Qed.
Lemma lem3999913 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3999914 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term585 A s f) = (term590 A s f).
Proof. exact (MK_COMB (@lem3999913 A) (@lem3999912 A s f)). Qed.
Lemma lem3999915 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term584 A s f) = (term590 A s f).
Proof. exact (TRANS (@lem3999907 A s f) (@lem3999914 A s f)). Qed.
Lemma lem3999916 {A : Type'} (s : A -> Prop) : (term197 A s) = (term197 A s).
Proof. exact (eq_refl (term197 A s)). Qed.
Lemma lem3999917 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3999918 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term591 A s f) = (term592 A s f).
Proof. exact (MK_COMB (@lem3999917) (@lem3999915 A s f)). Qed.
Lemma lem3999919 {A : Type'} (f : A -> nat) (s : A -> Prop) : (term593 A f s) = (term594 A f s).
Proof. exact (MK_COMB (@lem3999918 A s f) (@lem3999916 A s)). Qed.
Lemma lem3999920 {A : Type'} (f : A -> nat) (s : A -> Prop) : (term595 A f s) = (term593 A f s).
Proof. exact (@lem17045 (term108 A s f) (@FINITE A s)). Qed.
Lemma lem3999921 {A : Type'} (f : A -> nat) (s : A -> Prop) : (term595 A f s) = (term594 A f s).
Proof. exact (TRANS (@lem3999920 A f s) (@lem3999919 A f s)). Qed.
Lemma lem3999922 {A : Type'} (f : A -> nat) (s : A -> Prop) : ((term103 A f s) = (@CARD A s)) = ((term103 A f s) = (@CARD A s)).
Proof. exact (eq_refl ((term103 A f s) = (@CARD A s))). Qed.
Lemma lem3999923 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3999924 {A : Type'} (f : A -> nat) (s : A -> Prop) : (term596 A f s) = (term597 A f s).
Proof. exact (MK_COMB (@lem3999923) (@lem3999921 A f s)). Qed.
Lemma lem3999925 {A : Type'} (f : A -> nat) (s : A -> Prop) : (term598 A f s) = (term599 A f s).
Proof. exact (MK_COMB (@lem3999924 A f s) (@lem3999922 A f s)). Qed.
Lemma lem3999926 {A : Type'} (f : A -> nat) (s : A -> Prop) : (term112 A f s) = (term598 A f s).
Proof. exact (@lem17265 (term110 A f s) ((term103 A f s) = (@CARD A s))). Qed.
Lemma lem3999927 {A : Type'} (f : A -> nat) (s : A -> Prop) : (term112 A f s) = (term599 A f s).
Proof. exact (TRANS (@lem3999926 A f s) (@lem3999925 A f s)). Qed.
Lemma lem3999928 {A : Type'} (f : A -> nat) : (term113 A f) = (term600 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3999927 A f s)). Qed.
Lemma lem3999929 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3999930 {A : Type'} (f : A -> nat) : (term114 A f) = (term601 A f).
Proof. exact (MK_COMB (@lem3999929 A) (@lem3999928 A f)). Qed.
Lemma lem3999931 {A : Type'} : (term115 A) = (term602 A).
Proof. exact (fun_ext (fun f : A -> nat => @lem3999930 A f)). Qed.
Lemma lem3999932 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem3999933 {A : Type'} : (term56 A) = (term603 A).
Proof. exact (MK_COMB (@lem3999932 A) (@lem3999931 A)). Qed.
Lemma lem4000040 {A : Type'} (P : A -> Prop) (Q : Prop) : (term211 A P Q) = (term212 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4000041 {A : Type'} (P : A -> Prop) (Q : Prop) : (term211 A P Q) = (term212 A P Q).
Proof. exact (@lem4000040 A P Q). Qed.
Lemma lem4000042 {A : Type'} (f : A -> nat) (s : A -> Prop) : (term604 A f s) = (term605 A f s).
Proof. exact (@lem4000041 A (term589 A s f) (term197 A s)). Qed.
Lemma lem4000043 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : (term606 A s f x) = (term583 A s f x).
Proof. exact (eq_refl (term606 A s f x)). Qed.
Lemma lem4000044 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term607 A s f) = (term589 A s f).
Proof. exact (fun_ext (fun x : A => @lem4000043 A s f x)). Qed.
Lemma lem4000045 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4000046 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term608 A s f) = (term590 A s f).
Proof. exact (MK_COMB (@lem4000045 A) (@lem4000044 A s f)). Qed.
Lemma lem4000047 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4000048 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term609 A s f) = (term592 A s f).
Proof. exact (MK_COMB (@lem4000047) (@lem4000046 A s f)). Qed.
Lemma lem4000049 {A : Type'} (s : A -> Prop) : (term197 A s) = (term197 A s).
Proof. exact (eq_refl (term197 A s)). Qed.
Lemma lem4000050 {A : Type'} (f : A -> nat) (s : A -> Prop) : (term604 A f s) = (term594 A f s).
Proof. exact (MK_COMB (@lem4000048 A s f) (@lem4000049 A s)). Qed.
Lemma lem4000051 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4000052 {A : Type'} (f : A -> nat) (s : A -> Prop) : (term610 A f s) = (term611 A f s).
Proof. exact (MK_COMB (@lem4000051) (@lem4000050 A f s)). Qed.
Lemma lem4000053 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : (term606 A s f x) = (term583 A s f x).
Proof. exact (eq_refl (term606 A s f x)). Qed.
Lemma lem4000054 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4000055 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : (term612 A s f x) = (term613 A s f x).
Proof. exact (MK_COMB (@lem4000054) (@lem4000053 A s f x)). Qed.
Lemma lem4000056 {A : Type'} (s : A -> Prop) : (term197 A s) = (term197 A s).
Proof. exact (eq_refl (term197 A s)). Qed.
Lemma lem4000057 {A : Type'} (f : A -> nat) (x : A) (s : A -> Prop) : (term614 A f x s) = (term615 A f x s).
Proof. exact (MK_COMB (@lem4000055 A s f x) (@lem4000056 A s)). Qed.
Lemma lem4000058 {A : Type'} (f : A -> nat) (s : A -> Prop) : (term616 A f s) = (term617 A f s).
Proof. exact (fun_ext (fun x : A => @lem4000057 A f x s)). Qed.
Lemma lem4000059 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4000060 {A : Type'} (f : A -> nat) (s : A -> Prop) : (term605 A f s) = (term618 A f s).
Proof. exact (MK_COMB (@lem4000059 A) (@lem4000058 A f s)). Qed.
Lemma lem4000061 {A : Type'} (f : A -> nat) (s : A -> Prop) : ((term604 A f s) = (term605 A f s)) = ((term594 A f s) = (term618 A f s)).
Proof. exact (MK_COMB (@lem4000052 A f s) (@lem4000060 A f s)). Qed.
Lemma lem4000062 {A : Type'} (f : A -> nat) (s : A -> Prop) : (term594 A f s) = (term618 A f s).
Proof. exact (EQ_MP (@lem4000061 A f s) (@lem4000042 A f s)). Qed.
Lemma lem4000064 {A : Type'} (P : A -> Prop) (Q : Prop) : (term211 A P Q) = (term212 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4000065 {A : Type'} (P : A -> Prop) (Q : Prop) : (term211 A P Q) = (term212 A P Q).
Proof. exact (@lem4000064 A P Q). Qed.
Lemma lem4000066 {A : Type'} (f : A -> nat) (x : A) (s : A -> Prop) : (term619 A f x s) = (term620 A f x s).
Proof. exact (@lem4000065 A (term582 A s f x) (term197 A s)). Qed.
Lemma lem4000067 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (y : A) : (term621 A s f x y) = (term575 A s f x y).
Proof. exact (eq_refl (term621 A s f x y)). Qed.
Lemma lem4000068 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : (term622 A s f x) = (term582 A s f x).
Proof. exact (fun_ext (fun y : A => @lem4000067 A s f x y)). Qed.
Lemma lem4000069 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4000070 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : (term623 A s f x) = (term583 A s f x).
Proof. exact (MK_COMB (@lem4000069 A) (@lem4000068 A s f x)). Qed.
Lemma lem4000071 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4000072 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : (term624 A s f x) = (term613 A s f x).
Proof. exact (MK_COMB (@lem4000071) (@lem4000070 A s f x)). Qed.
Lemma lem4000073 {A : Type'} (s : A -> Prop) : (term197 A s) = (term197 A s).
Proof. exact (eq_refl (term197 A s)). Qed.
Lemma lem4000074 {A : Type'} (f : A -> nat) (x : A) (s : A -> Prop) : (term619 A f x s) = (term615 A f x s).
Proof. exact (MK_COMB (@lem4000072 A s f x) (@lem4000073 A s)). Qed.
Lemma lem4000075 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4000076 {A : Type'} (f : A -> nat) (x : A) (s : A -> Prop) : (term625 A f x s) = (term626 A f x s).
Proof. exact (MK_COMB (@lem4000075) (@lem4000074 A f x s)). Qed.
Lemma lem4000077 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (y : A) : (term621 A s f x y) = (term575 A s f x y).
Proof. exact (eq_refl (term621 A s f x y)). Qed.
Lemma lem4000078 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4000079 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (y : A) : (term627 A s f x y) = (term628 A s f x y).
Proof. exact (MK_COMB (@lem4000078) (@lem4000077 A s f x y)). Qed.
Lemma lem4000080 {A : Type'} (s : A -> Prop) : (term197 A s) = (term197 A s).
Proof. exact (eq_refl (term197 A s)). Qed.
Lemma lem4000081 {A : Type'} (f : A -> nat) (x : A) (y : A) (s : A -> Prop) : (term629 A f x y s) = (term630 A f x y s).
Proof. exact (MK_COMB (@lem4000079 A s f x y) (@lem4000080 A s)). Qed.
Lemma lem4000082 {A : Type'} (f : A -> nat) (x : A) (s : A -> Prop) : (term631 A f x s) = (term632 A f x s).
Proof. exact (fun_ext (fun y : A => @lem4000081 A f x y s)). Qed.
Lemma lem4000083 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4000084 {A : Type'} (f : A -> nat) (x : A) (s : A -> Prop) : (term620 A f x s) = (term633 A f x s).
Proof. exact (MK_COMB (@lem4000083 A) (@lem4000082 A f x s)). Qed.
Lemma lem4000085 {A : Type'} (f : A -> nat) (x : A) (s : A -> Prop) : ((term619 A f x s) = (term620 A f x s)) = ((term615 A f x s) = (term633 A f x s)).
Proof. exact (MK_COMB (@lem4000076 A f x s) (@lem4000084 A f x s)). Qed.
Lemma lem4000086 {A : Type'} (f : A -> nat) (x : A) (s : A -> Prop) : (term615 A f x s) = (term633 A f x s).
Proof. exact (EQ_MP (@lem4000085 A f x s) (@lem4000066 A f x s)). Qed.
Lemma lem4000087 {A : Type'} (f : A -> nat) (s : A -> Prop) : (term617 A f s) = (term634 A f s).
Proof. exact (fun_ext (fun x : A => @lem4000086 A f x s)). Qed.
Lemma lem4000088 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4000089 {A : Type'} (f : A -> nat) (s : A -> Prop) : (term618 A f s) = (term635 A f s).
Proof. exact (MK_COMB (@lem4000088 A) (@lem4000087 A f s)). Qed.
Lemma lem4000090 {A : Type'} (f : A -> nat) (s : A -> Prop) : (term594 A f s) = (term635 A f s).
Proof. exact (TRANS (@lem4000062 A f s) (@lem4000089 A f s)). Qed.
Lemma lem4000091 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4000092 {A : Type'} (f : A -> nat) (s : A -> Prop) : (term597 A f s) = (term636 A f s).
Proof. exact (MK_COMB (@lem4000091) (@lem4000090 A f s)). Qed.
Lemma lem4000093 {A : Type'} (f : A -> nat) (s : A -> Prop) : ((term103 A f s) = (@CARD A s)) = ((term103 A f s) = (@CARD A s)).
Proof. exact (eq_refl ((term103 A f s) = (@CARD A s))). Qed.
Lemma lem4000094 {A : Type'} (f : A -> nat) (s : A -> Prop) : (term599 A f s) = (term637 A f s).
Proof. exact (MK_COMB (@lem4000092 A f s) (@lem4000093 A f s)). Qed.
Lemma lem4000096 {A : Type'} (P : A -> Prop) (Q : Prop) : (term211 A P Q) = (term212 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4000097 {A : Type'} (P : A -> Prop) (Q : Prop) : (term211 A P Q) = (term212 A P Q).
Proof. exact (@lem4000096 A P Q). Qed.
Lemma lem4000098 {A : Type'} (f : A -> nat) (s : A -> Prop) : (term638 A f s) = (term639 A f s).
Proof. exact (@lem4000097 A (term634 A f s) ((term103 A f s) = (@CARD A s))). Qed.
Lemma lem4000099 {A : Type'} (f : A -> nat) (x : A) (s : A -> Prop) : (term640 A f s x) = (term633 A f x s).
Proof. exact (eq_refl (term640 A f s x)). Qed.
Lemma lem4000100 {A : Type'} (f : A -> nat) (s : A -> Prop) : (term641 A f s) = (term634 A f s).
Proof. exact (fun_ext (fun x : A => @lem4000099 A f x s)). Qed.
Lemma lem4000101 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4000102 {A : Type'} (f : A -> nat) (s : A -> Prop) : (term642 A f s) = (term635 A f s).
Proof. exact (MK_COMB (@lem4000101 A) (@lem4000100 A f s)). Qed.
Lemma lem4000103 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4000104 {A : Type'} (f : A -> nat) (s : A -> Prop) : (term643 A f s) = (term636 A f s).
Proof. exact (MK_COMB (@lem4000103) (@lem4000102 A f s)). Qed.
Lemma lem4000105 {A : Type'} (f : A -> nat) (s : A -> Prop) : ((term103 A f s) = (@CARD A s)) = ((term103 A f s) = (@CARD A s)).
Proof. exact (eq_refl ((term103 A f s) = (@CARD A s))). Qed.
Lemma lem4000106 {A : Type'} (f : A -> nat) (s : A -> Prop) : (term638 A f s) = (term637 A f s).
Proof. exact (MK_COMB (@lem4000104 A f s) (@lem4000105 A f s)). Qed.
Lemma lem4000107 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4000108 {A : Type'} (f : A -> nat) (s : A -> Prop) : (term644 A f s) = (term645 A f s).
Proof. exact (MK_COMB (@lem4000107) (@lem4000106 A f s)). Qed.
Lemma lem4000109 {A : Type'} (f : A -> nat) (x : A) (s : A -> Prop) : (term640 A f s x) = (term633 A f x s).
Proof. exact (eq_refl (term640 A f s x)). Qed.
Lemma lem4000110 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4000111 {A : Type'} (f : A -> nat) (x : A) (s : A -> Prop) : (term646 A f s x) = (term647 A f x s).
Proof. exact (MK_COMB (@lem4000110) (@lem4000109 A f x s)). Qed.
Lemma lem4000112 {A : Type'} (f : A -> nat) (s : A -> Prop) : ((term103 A f s) = (@CARD A s)) = ((term103 A f s) = (@CARD A s)).
Proof. exact (eq_refl ((term103 A f s) = (@CARD A s))). Qed.
Lemma lem4000113 {A : Type'} (x : A) (f : A -> nat) (s : A -> Prop) : (term648 A x f s) = (term649 A x f s).
Proof. exact (MK_COMB (@lem4000111 A f x s) (@lem4000112 A f s)). Qed.
Lemma lem4000114 {A : Type'} (f : A -> nat) (s : A -> Prop) : (term650 A f s) = (term651 A f s).
Proof. exact (fun_ext (fun x : A => @lem4000113 A x f s)). Qed.
Lemma lem4000115 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4000116 {A : Type'} (f : A -> nat) (s : A -> Prop) : (term639 A f s) = (term652 A f s).
Proof. exact (MK_COMB (@lem4000115 A) (@lem4000114 A f s)). Qed.
Lemma lem4000117 {A : Type'} (f : A -> nat) (s : A -> Prop) : ((term638 A f s) = (term639 A f s)) = ((term637 A f s) = (term652 A f s)).
Proof. exact (MK_COMB (@lem4000108 A f s) (@lem4000116 A f s)). Qed.
Lemma lem4000118 {A : Type'} (f : A -> nat) (s : A -> Prop) : (term637 A f s) = (term652 A f s).
Proof. exact (EQ_MP (@lem4000117 A f s) (@lem4000098 A f s)). Qed.
Lemma lem4000120 {A : Type'} (P : A -> Prop) (Q : Prop) : (term211 A P Q) = (term212 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4000121 {A : Type'} (P : A -> Prop) (Q : Prop) : (term211 A P Q) = (term212 A P Q).
Proof. exact (@lem4000120 A P Q). Qed.
Lemma lem4000122 {A : Type'} (x : A) (f : A -> nat) (s : A -> Prop) : (term653 A x f s) = (term654 A x f s).
Proof. exact (@lem4000121 A (term632 A f x s) ((term103 A f s) = (@CARD A s))). Qed.
Lemma lem4000123 {A : Type'} (f : A -> nat) (x : A) (y : A) (s : A -> Prop) : (term655 A f x s y) = (term630 A f x y s).
Proof. exact (eq_refl (term655 A f x s y)). Qed.
Lemma lem4000124 {A : Type'} (f : A -> nat) (x : A) (s : A -> Prop) : (term656 A f x s) = (term632 A f x s).
Proof. exact (fun_ext (fun y : A => @lem4000123 A f x y s)). Qed.
Lemma lem4000125 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4000126 {A : Type'} (f : A -> nat) (x : A) (s : A -> Prop) : (term657 A f x s) = (term633 A f x s).
Proof. exact (MK_COMB (@lem4000125 A) (@lem4000124 A f x s)). Qed.
Lemma lem4000127 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4000128 {A : Type'} (f : A -> nat) (x : A) (s : A -> Prop) : (term658 A f x s) = (term647 A f x s).
Proof. exact (MK_COMB (@lem4000127) (@lem4000126 A f x s)). Qed.
Lemma lem4000129 {A : Type'} (f : A -> nat) (s : A -> Prop) : ((term103 A f s) = (@CARD A s)) = ((term103 A f s) = (@CARD A s)).
Proof. exact (eq_refl ((term103 A f s) = (@CARD A s))). Qed.
Lemma lem4000130 {A : Type'} (x : A) (f : A -> nat) (s : A -> Prop) : (term653 A x f s) = (term649 A x f s).
Proof. exact (MK_COMB (@lem4000128 A f x s) (@lem4000129 A f s)). Qed.
Lemma lem4000131 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4000132 {A : Type'} (x : A) (f : A -> nat) (s : A -> Prop) : (term659 A x f s) = (term660 A x f s).
Proof. exact (MK_COMB (@lem4000131) (@lem4000130 A x f s)). Qed.
Lemma lem4000133 {A : Type'} (f : A -> nat) (x : A) (y : A) (s : A -> Prop) : (term655 A f x s y) = (term630 A f x y s).
Proof. exact (eq_refl (term655 A f x s y)). Qed.
Lemma lem4000134 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4000135 {A : Type'} (f : A -> nat) (x : A) (y : A) (s : A -> Prop) : (term661 A f x s y) = (term662 A f x y s).
Proof. exact (MK_COMB (@lem4000134) (@lem4000133 A f x y s)). Qed.
Lemma lem4000136 {A : Type'} (f : A -> nat) (s : A -> Prop) : ((term103 A f s) = (@CARD A s)) = ((term103 A f s) = (@CARD A s)).
Proof. exact (eq_refl ((term103 A f s) = (@CARD A s))). Qed.
Lemma lem4000137 {A : Type'} (x : A) (y : A) (f : A -> nat) (s : A -> Prop) : (term663 A x y f s) = (term664 A x y f s).
Proof. exact (MK_COMB (@lem4000135 A f x y s) (@lem4000136 A f s)). Qed.
Lemma lem4000138 {A : Type'} (x : A) (f : A -> nat) (s : A -> Prop) : (term665 A x f s) = (term666 A x f s).
Proof. exact (fun_ext (fun y : A => @lem4000137 A x y f s)). Qed.
Lemma lem4000139 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4000140 {A : Type'} (x : A) (f : A -> nat) (s : A -> Prop) : (term654 A x f s) = (term667 A x f s).
Proof. exact (MK_COMB (@lem4000139 A) (@lem4000138 A x f s)). Qed.
Lemma lem4000141 {A : Type'} (x : A) (f : A -> nat) (s : A -> Prop) : ((term653 A x f s) = (term654 A x f s)) = ((term649 A x f s) = (term667 A x f s)).
Proof. exact (MK_COMB (@lem4000132 A x f s) (@lem4000140 A x f s)). Qed.
Lemma lem4000142 {A : Type'} (x : A) (f : A -> nat) (s : A -> Prop) : (term649 A x f s) = (term667 A x f s).
Proof. exact (EQ_MP (@lem4000141 A x f s) (@lem4000122 A x f s)). Qed.
Lemma lem4000143 {A : Type'} (f : A -> nat) (s : A -> Prop) : (term651 A f s) = (term668 A f s).
Proof. exact (fun_ext (fun x : A => @lem4000142 A x f s)). Qed.
Lemma lem4000144 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4000145 {A : Type'} (f : A -> nat) (s : A -> Prop) : (term652 A f s) = (term669 A f s).
Proof. exact (MK_COMB (@lem4000144 A) (@lem4000143 A f s)). Qed.
Lemma lem4000146 {A : Type'} (f : A -> nat) (s : A -> Prop) : (term637 A f s) = (term669 A f s).
Proof. exact (TRANS (@lem4000118 A f s) (@lem4000145 A f s)). Qed.
Lemma lem4000147 {A : Type'} (f : A -> nat) (s : A -> Prop) : (term599 A f s) = (term669 A f s).
Proof. exact (TRANS (@lem4000094 A f s) (@lem4000146 A f s)). Qed.
Lemma lem4000148 {A : Type'} (f : A -> nat) : (term600 A f) = (term670 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4000147 A f s)). Qed.
Lemma lem4000149 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4000150 {A : Type'} (f : A -> nat) : (term601 A f) = (term671 A f).
Proof. exact (MK_COMB (@lem4000149 A) (@lem4000148 A f)). Qed.
Lemma lem4000152 {A B : Type'} (P : type1413 A B) : (term281 A B P) = (term282 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4000153 {A : Type'} (P : type672 A) : (term283 A P) = (term284 A P).
Proof. exact (@lem4000152 (A -> Prop) A P). Qed.
Lemma lem4000154 {A : Type'} (f : A -> nat) : (term672 A f) = (term673 A f).
Proof. exact (@lem4000153 A (term674 A f)). Qed.
Lemma lem4000155 {A : Type'} (f : A -> nat) (s : A -> Prop) : (term675 A f s) = (term668 A f s).
Proof. exact (eq_refl (term675 A f s)). Qed.
Lemma lem4000156 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4000157 {A : Type'} (f : A -> nat) (s : A -> Prop) (x : A) : (term676 A f s x) = (term677 A f s x).
Proof. exact (MK_COMB (@lem4000155 A f s) (@lem4000156 A x)). Qed.
Lemma lem4000158 {A : Type'} (x : A) (f : A -> nat) (s : A -> Prop) : (term677 A f s x) = (term667 A x f s).
Proof. exact (eq_refl (term677 A f s x)). Qed.
Lemma lem4000159 {A : Type'} (x : A) (f : A -> nat) (s : A -> Prop) : (term676 A f s x) = (term667 A x f s).
Proof. exact (TRANS (@lem4000157 A f s x) (@lem4000158 A x f s)). Qed.
Lemma lem4000160 {A : Type'} (f : A -> nat) (s : A -> Prop) : (term678 A f s) = (term668 A f s).
Proof. exact (fun_ext (fun x : A => @lem4000159 A x f s)). Qed.
Lemma lem4000161 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4000162 {A : Type'} (f : A -> nat) (s : A -> Prop) : (term679 A f s) = (term669 A f s).
Proof. exact (MK_COMB (@lem4000161 A) (@lem4000160 A f s)). Qed.
Lemma lem4000163 {A : Type'} (f : A -> nat) : (term680 A f) = (term670 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4000162 A f s)). Qed.
Lemma lem4000164 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4000165 {A : Type'} (f : A -> nat) : (term672 A f) = (term671 A f).
Proof. exact (MK_COMB (@lem4000164 A) (@lem4000163 A f)). Qed.
Lemma lem4000166 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4000167 {A : Type'} (f : A -> nat) : (term681 A f) = (term682 A f).
Proof. exact (MK_COMB (@lem4000166) (@lem4000165 A f)). Qed.
Lemma lem4000168 {A : Type'} (f : A -> nat) (s : A -> Prop) : (term675 A f s) = (term668 A f s).
Proof. exact (eq_refl (term675 A f s)). Qed.
Lemma lem4000169 {A : Type'} (x : type684 A) (s : A -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem4000170 {A : Type'} (f : A -> nat) (x : type684 A) (s : A -> Prop) : (term683 A f x s) = (term684 A f x s).
Proof. exact (MK_COMB (@lem4000168 A f s) (@lem4000169 A x s)). Qed.
Lemma lem4000171 {A : Type'} (x : type684 A) (f : A -> nat) (s : A -> Prop) : (term684 A f x s) = (term685 A x f s).
Proof. exact (eq_refl (term684 A f x s)). Qed.
Lemma lem4000172 {A : Type'} (x : type684 A) (f : A -> nat) (s : A -> Prop) : (term683 A f x s) = (term685 A x f s).
Proof. exact (TRANS (@lem4000170 A f x s) (@lem4000171 A x f s)). Qed.
Lemma lem4000173 {A : Type'} (x : type684 A) (f : A -> nat) : (term686 A f x) = (term687 A x f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4000172 A x f s)). Qed.
Lemma lem4000174 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4000175 {A : Type'} (x : type684 A) (f : A -> nat) : (term688 A f x) = (term689 A x f).
Proof. exact (MK_COMB (@lem4000174 A) (@lem4000173 A x f)). Qed.
Lemma lem4000176 {A : Type'} (f : A -> nat) : (term690 A f) = (term691 A f).
Proof. exact (fun_ext (fun x : type684 A => @lem4000175 A x f)). Qed.
Lemma lem4000177 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem4000178 {A : Type'} (f : A -> nat) : (term673 A f) = (term692 A f).
Proof. exact (MK_COMB (@lem4000177 A) (@lem4000176 A f)). Qed.
Lemma lem4000179 {A : Type'} (f : A -> nat) : ((term672 A f) = (term673 A f)) = ((term671 A f) = (term692 A f)).
Proof. exact (MK_COMB (@lem4000167 A f) (@lem4000178 A f)). Qed.
Lemma lem4000180 {A : Type'} (f : A -> nat) : (term671 A f) = (term692 A f).
Proof. exact (EQ_MP (@lem4000179 A f) (@lem4000154 A f)). Qed.
Lemma lem4000182 {A B : Type'} (P : type1413 A B) : (term281 A B P) = (term282 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4000183 {A : Type'} (P : type672 A) : (term283 A P) = (term284 A P).
Proof. exact (@lem4000182 (A -> Prop) A P). Qed.
Lemma lem4000184 {A : Type'} (x : type684 A) (f : A -> nat) : (term693 A x f) = (term694 A x f).
Proof. exact (@lem4000183 A (term695 A x f)). Qed.
Lemma lem4000185 {A : Type'} (x : type684 A) (f : A -> nat) (s : A -> Prop) : (term696 A x f s) = (term697 A x f s).
Proof. exact (eq_refl (term696 A x f s)). Qed.
Lemma lem4000186 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem4000187 {A : Type'} (x : type684 A) (f : A -> nat) (s : A -> Prop) (y : A) : (term698 A x f s y) = (term699 A x f s y).
Proof. exact (MK_COMB (@lem4000185 A x f s) (@lem4000186 A y)). Qed.
Lemma lem4000188 {A : Type'} (x : type684 A) (y : A) (f : A -> nat) (s : A -> Prop) : (term699 A x f s y) = (term700 A x y f s).
Proof. exact (eq_refl (term699 A x f s y)). Qed.
Lemma lem4000189 {A : Type'} (x : type684 A) (y : A) (f : A -> nat) (s : A -> Prop) : (term698 A x f s y) = (term700 A x y f s).
Proof. exact (TRANS (@lem4000187 A x f s y) (@lem4000188 A x y f s)). Qed.
Lemma lem4000190 {A : Type'} (x : type684 A) (f : A -> nat) (s : A -> Prop) : (term701 A x f s) = (term697 A x f s).
Proof. exact (fun_ext (fun y : A => @lem4000189 A x y f s)). Qed.
Lemma lem4000191 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4000192 {A : Type'} (x : type684 A) (f : A -> nat) (s : A -> Prop) : (term702 A x f s) = (term685 A x f s).
Proof. exact (MK_COMB (@lem4000191 A) (@lem4000190 A x f s)). Qed.
Lemma lem4000193 {A : Type'} (x : type684 A) (f : A -> nat) : (term703 A x f) = (term687 A x f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4000192 A x f s)). Qed.
Lemma lem4000194 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4000195 {A : Type'} (x : type684 A) (f : A -> nat) : (term693 A x f) = (term689 A x f).
Proof. exact (MK_COMB (@lem4000194 A) (@lem4000193 A x f)). Qed.
Lemma lem4000196 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4000197 {A : Type'} (x : type684 A) (f : A -> nat) : (term704 A x f) = (term705 A x f).
Proof. exact (MK_COMB (@lem4000196) (@lem4000195 A x f)). Qed.
Lemma lem4000198 {A : Type'} (x : type684 A) (f : A -> nat) (s : A -> Prop) : (term696 A x f s) = (term697 A x f s).
Proof. exact (eq_refl (term696 A x f s)). Qed.
Lemma lem4000199 {A : Type'} (y : type684 A) (s : A -> Prop) : (y s) = (y s).
Proof. exact (eq_refl (y s)). Qed.
Lemma lem4000200 {A : Type'} (x : type684 A) (f : A -> nat) (y : type684 A) (s : A -> Prop) : (term706 A x f y s) = (term707 A x f y s).
Proof. exact (MK_COMB (@lem4000198 A x f s) (@lem4000199 A y s)). Qed.
Lemma lem4000201 {A : Type'} (x : type684 A) (y : type684 A) (f : A -> nat) (s : A -> Prop) : (term707 A x f y s) = (term708 A x y f s).
Proof. exact (eq_refl (term707 A x f y s)). Qed.
Lemma lem4000202 {A : Type'} (x : type684 A) (y : type684 A) (f : A -> nat) (s : A -> Prop) : (term706 A x f y s) = (term708 A x y f s).
Proof. exact (TRANS (@lem4000200 A x f y s) (@lem4000201 A x y f s)). Qed.
Lemma lem4000203 {A : Type'} (x : type684 A) (y : type684 A) (f : A -> nat) : (term709 A x f y) = (term710 A x y f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4000202 A x y f s)). Qed.
Lemma lem4000204 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4000205 {A : Type'} (x : type684 A) (y : type684 A) (f : A -> nat) : (term711 A x f y) = (term712 A x y f).
Proof. exact (MK_COMB (@lem4000204 A) (@lem4000203 A x y f)). Qed.
Lemma lem4000206 {A : Type'} (x : type684 A) (f : A -> nat) : (term713 A x f) = (term714 A x f).
Proof. exact (fun_ext (fun y : type684 A => @lem4000205 A x y f)). Qed.
Lemma lem4000207 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem4000208 {A : Type'} (x : type684 A) (f : A -> nat) : (term694 A x f) = (term715 A x f).
Proof. exact (MK_COMB (@lem4000207 A) (@lem4000206 A x f)). Qed.
Lemma lem4000209 {A : Type'} (x : type684 A) (f : A -> nat) : ((term693 A x f) = (term694 A x f)) = ((term689 A x f) = (term715 A x f)).
Proof. exact (MK_COMB (@lem4000197 A x f) (@lem4000208 A x f)). Qed.
Lemma lem4000210 {A : Type'} (x : type684 A) (f : A -> nat) : (term689 A x f) = (term715 A x f).
Proof. exact (EQ_MP (@lem4000209 A x f) (@lem4000184 A x f)). Qed.
Lemma lem4000211 {A : Type'} (f : A -> nat) : (term691 A f) = (term716 A f).
Proof. exact (fun_ext (fun x : type684 A => @lem4000210 A x f)). Qed.
Lemma lem4000212 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem4000213 {A : Type'} (f : A -> nat) : (term692 A f) = (term717 A f).
Proof. exact (MK_COMB (@lem4000212 A) (@lem4000211 A f)). Qed.
Lemma lem4000214 {A : Type'} (f : A -> nat) : (term671 A f) = (term717 A f).
Proof. exact (TRANS (@lem4000180 A f) (@lem4000213 A f)). Qed.
Lemma lem4000215 {A : Type'} (f : A -> nat) : (term601 A f) = (term717 A f).
Proof. exact (TRANS (@lem4000150 A f) (@lem4000214 A f)). Qed.
Lemma lem4000216 {A : Type'} : (term602 A) = (term718 A).
Proof. exact (fun_ext (fun f : A -> nat => @lem4000215 A f)). Qed.
Lemma lem4000217 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem4000218 {A : Type'} : (term603 A) = (term719 A).
Proof. exact (MK_COMB (@lem4000217 A) (@lem4000216 A)). Qed.
Lemma lem4000220 {A B : Type'} (P : type1413 A B) : (term281 A B P) = (term282 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4000221 {A : Type'} (P : type690 A) : (term720 A P) = (term721 A P).
Proof. exact (@lem4000220 (A -> nat) (type684 A) P). Qed.
Lemma lem4000222 {A : Type'} : (term722 A) = (term723 A).
Proof. exact (@lem4000221 A (term724 A)). Qed.
Lemma lem4000223 {A : Type'} (f : A -> nat) : (term725 A f) = (term716 A f).
Proof. exact (eq_refl (term725 A f)). Qed.
Lemma lem4000224 {A : Type'} (x : type684 A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4000225 {A : Type'} (f : A -> nat) (x : type684 A) : (term726 A f x) = (term727 A f x).
Proof. exact (MK_COMB (@lem4000223 A f) (@lem4000224 A x)). Qed.
Lemma lem4000226 {A : Type'} (x : type684 A) (f : A -> nat) : (term727 A f x) = (term715 A x f).
Proof. exact (eq_refl (term727 A f x)). Qed.
Lemma lem4000227 {A : Type'} (x : type684 A) (f : A -> nat) : (term726 A f x) = (term715 A x f).
Proof. exact (TRANS (@lem4000225 A f x) (@lem4000226 A x f)). Qed.
Lemma lem4000228 {A : Type'} (f : A -> nat) : (term728 A f) = (term716 A f).
Proof. exact (fun_ext (fun x : type684 A => @lem4000227 A x f)). Qed.
Lemma lem4000229 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem4000230 {A : Type'} (f : A -> nat) : (term729 A f) = (term717 A f).
Proof. exact (MK_COMB (@lem4000229 A) (@lem4000228 A f)). Qed.
Lemma lem4000231 {A : Type'} : (term730 A) = (term718 A).
Proof. exact (fun_ext (fun f : A -> nat => @lem4000230 A f)). Qed.
Lemma lem4000232 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem4000233 {A : Type'} : (term722 A) = (term719 A).
Proof. exact (MK_COMB (@lem4000232 A) (@lem4000231 A)). Qed.
Lemma lem4000234 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4000235 {A : Type'} : (term731 A) = (term732 A).
Proof. exact (MK_COMB (@lem4000234) (@lem4000233 A)). Qed.
Lemma lem4000236 {A : Type'} (f : A -> nat) : (term725 A f) = (term716 A f).
Proof. exact (eq_refl (term725 A f)). Qed.
Lemma lem4000237 {A : Type'} (x : type694 A) (f : A -> nat) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem4000238 {A : Type'} (x : type694 A) (f : A -> nat) : (term733 A x f) = (term734 A x f).
Proof. exact (MK_COMB (@lem4000236 A f) (@lem4000237 A x f)). Qed.
Lemma lem4000239 {A : Type'} (x : type694 A) (f : A -> nat) : (term734 A x f) = (term735 A x f).
Proof. exact (eq_refl (term734 A x f)). Qed.
Lemma lem4000240 {A : Type'} (x : type694 A) (f : A -> nat) : (term733 A x f) = (term735 A x f).
Proof. exact (TRANS (@lem4000238 A x f) (@lem4000239 A x f)). Qed.
Lemma lem4000241 {A : Type'} (x : type694 A) : (term736 A x) = (term737 A x).
Proof. exact (fun_ext (fun f : A -> nat => @lem4000240 A x f)). Qed.
Lemma lem4000242 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem4000243 {A : Type'} (x : type694 A) : (term738 A x) = (term739 A x).
Proof. exact (MK_COMB (@lem4000242 A) (@lem4000241 A x)). Qed.
Lemma lem4000244 {A : Type'} : (term740 A) = (term741 A).
Proof. exact (fun_ext (fun x : type694 A => @lem4000243 A x)). Qed.
Lemma lem4000245 {A : Type'} : (@ex ((A -> nat) -> (A -> Prop) -> A)) = (@ex ((A -> nat) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> nat) -> (A -> Prop) -> A))). Qed.
Lemma lem4000246 {A : Type'} : (term723 A) = (term742 A).
Proof. exact (MK_COMB (@lem4000245 A) (@lem4000244 A)). Qed.
Lemma lem4000247 {A : Type'} : ((term722 A) = (term723 A)) = ((term719 A) = (term742 A)).
Proof. exact (MK_COMB (@lem4000235 A) (@lem4000246 A)). Qed.
Lemma lem4000248 {A : Type'} : (term719 A) = (term742 A).
Proof. exact (EQ_MP (@lem4000247 A) (@lem4000222 A)). Qed.
Lemma lem4000250 {A B : Type'} (P : type1413 A B) : (term281 A B P) = (term282 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4000251 {A : Type'} (P : type690 A) : (term720 A P) = (term721 A P).
Proof. exact (@lem4000250 (A -> nat) (type684 A) P). Qed.
Lemma lem4000252 {A : Type'} (x : type694 A) : (term743 A x) = (term744 A x).
Proof. exact (@lem4000251 A (term745 A x)). Qed.
Lemma lem4000253 {A : Type'} (x : type694 A) (f : A -> nat) : (term746 A x f) = (term747 A x f).
Proof. exact (eq_refl (term746 A x f)). Qed.
Lemma lem4000254 {A : Type'} (y : type684 A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem4000255 {A : Type'} (x : type694 A) (f : A -> nat) (y : type684 A) : (term748 A x f y) = (term749 A x f y).
Proof. exact (MK_COMB (@lem4000253 A x f) (@lem4000254 A y)). Qed.
Lemma lem4000256 {A : Type'} (x : type694 A) (y : type684 A) (f : A -> nat) : (term749 A x f y) = (term750 A x y f).
Proof. exact (eq_refl (term749 A x f y)). Qed.
Lemma lem4000257 {A : Type'} (x : type694 A) (y : type684 A) (f : A -> nat) : (term748 A x f y) = (term750 A x y f).
Proof. exact (TRANS (@lem4000255 A x f y) (@lem4000256 A x y f)). Qed.
Lemma lem4000258 {A : Type'} (x : type694 A) (f : A -> nat) : (term751 A x f) = (term747 A x f).
Proof. exact (fun_ext (fun y : type684 A => @lem4000257 A x y f)). Qed.
Lemma lem4000259 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem4000260 {A : Type'} (x : type694 A) (f : A -> nat) : (term752 A x f) = (term735 A x f).
Proof. exact (MK_COMB (@lem4000259 A) (@lem4000258 A x f)). Qed.
Lemma lem4000261 {A : Type'} (x : type694 A) : (term753 A x) = (term737 A x).
Proof. exact (fun_ext (fun f : A -> nat => @lem4000260 A x f)). Qed.
Lemma lem4000262 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem4000263 {A : Type'} (x : type694 A) : (term743 A x) = (term739 A x).
Proof. exact (MK_COMB (@lem4000262 A) (@lem4000261 A x)). Qed.
Lemma lem4000264 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4000265 {A : Type'} (x : type694 A) : (term754 A x) = (term755 A x).
Proof. exact (MK_COMB (@lem4000264) (@lem4000263 A x)). Qed.
Lemma lem4000266 {A : Type'} (x : type694 A) (f : A -> nat) : (term746 A x f) = (term747 A x f).
Proof. exact (eq_refl (term746 A x f)). Qed.
Lemma lem4000267 {A : Type'} (y : type694 A) (f : A -> nat) : (y f) = (y f).
Proof. exact (eq_refl (y f)). Qed.
Lemma lem4000268 {A : Type'} (x : type694 A) (y : type694 A) (f : A -> nat) : (term756 A x y f) = (term757 A x y f).
Proof. exact (MK_COMB (@lem4000266 A x f) (@lem4000267 A y f)). Qed.
Lemma lem4000269 {A : Type'} (x : type694 A) (y : type694 A) (f : A -> nat) : (term757 A x y f) = (term758 A x y f).
Proof. exact (eq_refl (term757 A x y f)). Qed.
Lemma lem4000270 {A : Type'} (x : type694 A) (y : type694 A) (f : A -> nat) : (term756 A x y f) = (term758 A x y f).
Proof. exact (TRANS (@lem4000268 A x y f) (@lem4000269 A x y f)). Qed.
Lemma lem4000271 {A : Type'} (x : type694 A) (y : type694 A) : (term759 A x y) = (term760 A x y).
Proof. exact (fun_ext (fun f : A -> nat => @lem4000270 A x y f)). Qed.
Lemma lem4000272 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem4000273 {A : Type'} (x : type694 A) (y : type694 A) : (term761 A x y) = (term762 A x y).
Proof. exact (MK_COMB (@lem4000272 A) (@lem4000271 A x y)). Qed.
Lemma lem4000274 {A : Type'} (x : type694 A) : (term763 A x) = (term764 A x).
Proof. exact (fun_ext (fun y : type694 A => @lem4000273 A x y)). Qed.
Lemma lem4000275 {A : Type'} : (@ex ((A -> nat) -> (A -> Prop) -> A)) = (@ex ((A -> nat) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> nat) -> (A -> Prop) -> A))). Qed.
Lemma lem4000276 {A : Type'} (x : type694 A) : (term744 A x) = (term765 A x).
Proof. exact (MK_COMB (@lem4000275 A) (@lem4000274 A x)). Qed.
Lemma lem4000277 {A : Type'} (x : type694 A) : ((term743 A x) = (term744 A x)) = ((term739 A x) = (term765 A x)).
Proof. exact (MK_COMB (@lem4000265 A x) (@lem4000276 A x)). Qed.
Lemma lem4000278 {A : Type'} (x : type694 A) : (term739 A x) = (term765 A x).
Proof. exact (EQ_MP (@lem4000277 A x) (@lem4000252 A x)). Qed.
Lemma lem4000279 {A : Type'} : (term741 A) = (term766 A).
Proof. exact (fun_ext (fun x : type694 A => @lem4000278 A x)). Qed.
Lemma lem4000280 {A : Type'} : (@ex ((A -> nat) -> (A -> Prop) -> A)) = (@ex ((A -> nat) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> nat) -> (A -> Prop) -> A))). Qed.
Lemma lem4000281 {A : Type'} : (term742 A) = (term767 A).
Proof. exact (MK_COMB (@lem4000280 A) (@lem4000279 A)). Qed.
Lemma lem4000282 {A : Type'} : (term719 A) = (term767 A).
Proof. exact (TRANS (@lem4000248 A) (@lem4000281 A)). Qed.
Lemma lem4000284 {A : Type'} : (term603 A) = (term767 A).
Proof. exact (TRANS (@lem4000218 A) (@lem4000282 A)). Qed.
Lemma lem4000285 {A : Type'} : (term56 A) = (term767 A).
Proof. exact (TRANS (@lem3999933 A) (@lem4000284 A)). Qed.
Lemma lem4000286 {A : Type'} (h1 : term56 A) : term767 A.
Proof. exact (EQ_MP (@lem4000285 A) (@lem3998884 A h1)). Qed.
Lemma lem4000301 {B : Type'} (s : B -> Prop) (f : B -> B) (x : B) (y : B) : (term178 B s f x y) = (term179 B s f x y).
Proof. exact (@lem17362 (term180 B s x f y) (x = y)). Qed.
Lemma lem4000302 {B : Type'} (P : B -> Prop) : (term181 B P) = (term182 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem4000303 {B : Type'} (s : B -> Prop) (f : B -> B) (x : B) : (term183 B s f x) = (term184 B s f x).
Proof. exact (@lem4000302 B (term92 B s f x)). Qed.
Lemma lem4000304 {B : Type'} (s : B -> Prop) (f : B -> B) (x : B) (y : B) : (term185 B s f x y) = (term91 B s f x y).
Proof. exact (eq_refl (term185 B s f x y)). Qed.
Lemma lem4000305 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4000306 {B : Type'} (s : B -> Prop) (f : B -> B) (x : B) (y : B) : (term186 B s f x y) = (term178 B s f x y).
Proof. exact (MK_COMB (@lem4000305) (@lem4000304 B s f x y)). Qed.
Lemma lem4000307 {B : Type'} (s : B -> Prop) (f : B -> B) (x : B) (y : B) : (term186 B s f x y) = (term179 B s f x y).
Proof. exact (TRANS (@lem4000306 B s f x y) (@lem4000301 B s f x y)). Qed.
Lemma lem4000308 {B : Type'} (s : B -> Prop) (f : B -> B) (x : B) : (term187 B s f x) = (term188 B s f x).
Proof. exact (fun_ext (fun y : B => @lem4000307 B s f x y)). Qed.
Lemma lem4000309 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4000310 {B : Type'} (s : B -> Prop) (f : B -> B) (x : B) : (term184 B s f x) = (term189 B s f x).
Proof. exact (MK_COMB (@lem4000309 B) (@lem4000308 B s f x)). Qed.
Lemma lem4000311 {B : Type'} (s : B -> Prop) (f : B -> B) (x : B) : (term183 B s f x) = (term189 B s f x).
Proof. exact (TRANS (@lem4000303 B s f x) (@lem4000310 B s f x)). Qed.
Lemma lem4000312 {B : Type'} (P : B -> Prop) : (term181 B P) = (term182 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem4000313 {B : Type'} (s : B -> Prop) (f : B -> B) : (term190 B s f) = (term191 B s f).
Proof. exact (@lem4000312 B (term94 B s f)). Qed.
Lemma lem4000314 {B : Type'} (s : B -> Prop) (f : B -> B) (x : B) : (term192 B s f x) = (term93 B s f x).
Proof. exact (eq_refl (term192 B s f x)). Qed.
Lemma lem4000315 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4000316 {B : Type'} (s : B -> Prop) (f : B -> B) (x : B) : (term193 B s f x) = (term183 B s f x).
Proof. exact (MK_COMB (@lem4000315) (@lem4000314 B s f x)). Qed.
Lemma lem4000317 {B : Type'} (s : B -> Prop) (f : B -> B) (x : B) : (term193 B s f x) = (term189 B s f x).
Proof. exact (TRANS (@lem4000316 B s f x) (@lem4000311 B s f x)). Qed.
Lemma lem4000318 {B : Type'} (s : B -> Prop) (f : B -> B) : (term194 B s f) = (term195 B s f).
Proof. exact (fun_ext (fun x : B => @lem4000317 B s f x)). Qed.
Lemma lem4000319 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4000320 {B : Type'} (s : B -> Prop) (f : B -> B) : (term191 B s f) = (term196 B s f).
Proof. exact (MK_COMB (@lem4000319 B) (@lem4000318 B s f)). Qed.
Lemma lem4000321 {B : Type'} (s : B -> Prop) (f : B -> B) : (term190 B s f) = (term196 B s f).
Proof. exact (TRANS (@lem4000313 B s f) (@lem4000320 B s f)). Qed.
Lemma lem4000322 {B : Type'} (s : B -> Prop) : (term197 B s) = (term197 B s).
Proof. exact (eq_refl (term197 B s)). Qed.
Lemma lem4000323 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4000324 {B : Type'} (s : B -> Prop) (f : B -> B) : (term198 B s f) = (term199 B s f).
Proof. exact (MK_COMB (@lem4000323) (@lem4000321 B s f)). Qed.
Lemma lem4000325 {B : Type'} (f : B -> B) (s : B -> Prop) : (term200 B f s) = (term201 B f s).
Proof. exact (MK_COMB (@lem4000324 B s f) (@lem4000322 B s)). Qed.
Lemma lem4000326 {B : Type'} (f : B -> B) (s : B -> Prop) : (term202 B f s) = (term200 B f s).
Proof. exact (@lem17045 (term95 B s f) (@FINITE B s)). Qed.
Lemma lem4000327 {B : Type'} (f : B -> B) (s : B -> Prop) : (term202 B f s) = (term201 B f s).
Proof. exact (TRANS (@lem4000326 B f s) (@lem4000325 B f s)). Qed.
Lemma lem4000328 {B : Type'} (f : B -> B) (s : B -> Prop) : ((term90 B f s) = (@CARD B s)) = ((term90 B f s) = (@CARD B s)).
Proof. exact (eq_refl ((term90 B f s) = (@CARD B s))). Qed.
Lemma lem4000329 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4000330 {B : Type'} (f : B -> B) (s : B -> Prop) : (term203 B f s) = (term204 B f s).
Proof. exact (MK_COMB (@lem4000329) (@lem4000327 B f s)). Qed.
Lemma lem4000331 {B : Type'} (f : B -> B) (s : B -> Prop) : (term205 B f s) = (term206 B f s).
Proof. exact (MK_COMB (@lem4000330 B f s) (@lem4000328 B f s)). Qed.
Lemma lem4000332 {B : Type'} (f : B -> B) (s : B -> Prop) : (term99 B f s) = (term205 B f s).
Proof. exact (@lem17265 (term97 B f s) ((term90 B f s) = (@CARD B s))). Qed.
Lemma lem4000333 {B : Type'} (f : B -> B) (s : B -> Prop) : (term99 B f s) = (term206 B f s).
Proof. exact (TRANS (@lem4000332 B f s) (@lem4000331 B f s)). Qed.
Lemma lem4000334 {B : Type'} (f : B -> B) : (term100 B f) = (term207 B f).
Proof. exact (fun_ext (fun s : B -> Prop => @lem4000333 B f s)). Qed.
Lemma lem4000335 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4000336 {B : Type'} (f : B -> B) : (term101 B f) = (term208 B f).
Proof. exact (MK_COMB (@lem4000335 B) (@lem4000334 B f)). Qed.
Lemma lem4000337 {B : Type'} : (term102 B) = (term209 B).
Proof. exact (fun_ext (fun f : B -> B => @lem4000336 B f)). Qed.
Lemma lem4000338 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem4000339 {B : Type'} : (term55 B) = (term210 B).
Proof. exact (MK_COMB (@lem4000338 B) (@lem4000337 B)). Qed.
Lemma lem4000446 {A : Type'} (P : A -> Prop) (Q : Prop) : (term211 A P Q) = (term212 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4000447 {B : Type'} (P : B -> Prop) (Q : Prop) : (term211 B P Q) = (term212 B P Q).
Proof. exact (@lem4000446 B P Q). Qed.
Lemma lem4000448 {B : Type'} (f : B -> B) (s : B -> Prop) : (term213 B f s) = (term214 B f s).
Proof. exact (@lem4000447 B (term195 B s f) (term197 B s)). Qed.
Lemma lem4000449 {B : Type'} (s : B -> Prop) (f : B -> B) (x : B) : (term215 B s f x) = (term189 B s f x).
Proof. exact (eq_refl (term215 B s f x)). Qed.
Lemma lem4000450 {B : Type'} (s : B -> Prop) (f : B -> B) : (term216 B s f) = (term195 B s f).
Proof. exact (fun_ext (fun x : B => @lem4000449 B s f x)). Qed.
Lemma lem4000451 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4000452 {B : Type'} (s : B -> Prop) (f : B -> B) : (term217 B s f) = (term196 B s f).
Proof. exact (MK_COMB (@lem4000451 B) (@lem4000450 B s f)). Qed.
Lemma lem4000453 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4000454 {B : Type'} (s : B -> Prop) (f : B -> B) : (term218 B s f) = (term199 B s f).
Proof. exact (MK_COMB (@lem4000453) (@lem4000452 B s f)). Qed.
Lemma lem4000455 {B : Type'} (s : B -> Prop) : (term197 B s) = (term197 B s).
Proof. exact (eq_refl (term197 B s)). Qed.
Lemma lem4000456 {B : Type'} (f : B -> B) (s : B -> Prop) : (term213 B f s) = (term201 B f s).
Proof. exact (MK_COMB (@lem4000454 B s f) (@lem4000455 B s)). Qed.
Lemma lem4000457 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4000458 {B : Type'} (f : B -> B) (s : B -> Prop) : (term219 B f s) = (term220 B f s).
Proof. exact (MK_COMB (@lem4000457) (@lem4000456 B f s)). Qed.
Lemma lem4000459 {B : Type'} (s : B -> Prop) (f : B -> B) (x : B) : (term215 B s f x) = (term189 B s f x).
Proof. exact (eq_refl (term215 B s f x)). Qed.
Lemma lem4000460 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4000461 {B : Type'} (s : B -> Prop) (f : B -> B) (x : B) : (term221 B s f x) = (term222 B s f x).
Proof. exact (MK_COMB (@lem4000460) (@lem4000459 B s f x)). Qed.
Lemma lem4000462 {B : Type'} (s : B -> Prop) : (term197 B s) = (term197 B s).
Proof. exact (eq_refl (term197 B s)). Qed.
Lemma lem4000463 {B : Type'} (f : B -> B) (x : B) (s : B -> Prop) : (term223 B f x s) = (term224 B f x s).
Proof. exact (MK_COMB (@lem4000461 B s f x) (@lem4000462 B s)). Qed.
Lemma lem4000464 {B : Type'} (f : B -> B) (s : B -> Prop) : (term225 B f s) = (term226 B f s).
Proof. exact (fun_ext (fun x : B => @lem4000463 B f x s)). Qed.
Lemma lem4000465 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4000466 {B : Type'} (f : B -> B) (s : B -> Prop) : (term214 B f s) = (term227 B f s).
Proof. exact (MK_COMB (@lem4000465 B) (@lem4000464 B f s)). Qed.
Lemma lem4000467 {B : Type'} (f : B -> B) (s : B -> Prop) : ((term213 B f s) = (term214 B f s)) = ((term201 B f s) = (term227 B f s)).
Proof. exact (MK_COMB (@lem4000458 B f s) (@lem4000466 B f s)). Qed.
Lemma lem4000468 {B : Type'} (f : B -> B) (s : B -> Prop) : (term201 B f s) = (term227 B f s).
Proof. exact (EQ_MP (@lem4000467 B f s) (@lem4000448 B f s)). Qed.
Lemma lem4000470 {A : Type'} (P : A -> Prop) (Q : Prop) : (term211 A P Q) = (term212 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4000471 {B : Type'} (P : B -> Prop) (Q : Prop) : (term211 B P Q) = (term212 B P Q).
Proof. exact (@lem4000470 B P Q). Qed.
Lemma lem4000472 {B : Type'} (f : B -> B) (x : B) (s : B -> Prop) : (term228 B f x s) = (term229 B f x s).
Proof. exact (@lem4000471 B (term188 B s f x) (term197 B s)). Qed.
Lemma lem4000473 {B : Type'} (s : B -> Prop) (f : B -> B) (x : B) (y : B) : (term230 B s f x y) = (term179 B s f x y).
Proof. exact (eq_refl (term230 B s f x y)). Qed.
Lemma lem4000474 {B : Type'} (s : B -> Prop) (f : B -> B) (x : B) : (term231 B s f x) = (term188 B s f x).
Proof. exact (fun_ext (fun y : B => @lem4000473 B s f x y)). Qed.
Lemma lem4000475 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4000476 {B : Type'} (s : B -> Prop) (f : B -> B) (x : B) : (term232 B s f x) = (term189 B s f x).
Proof. exact (MK_COMB (@lem4000475 B) (@lem4000474 B s f x)). Qed.
Lemma lem4000477 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4000478 {B : Type'} (s : B -> Prop) (f : B -> B) (x : B) : (term233 B s f x) = (term222 B s f x).
Proof. exact (MK_COMB (@lem4000477) (@lem4000476 B s f x)). Qed.
Lemma lem4000479 {B : Type'} (s : B -> Prop) : (term197 B s) = (term197 B s).
Proof. exact (eq_refl (term197 B s)). Qed.
Lemma lem4000480 {B : Type'} (f : B -> B) (x : B) (s : B -> Prop) : (term228 B f x s) = (term224 B f x s).
Proof. exact (MK_COMB (@lem4000478 B s f x) (@lem4000479 B s)). Qed.
Lemma lem4000481 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4000482 {B : Type'} (f : B -> B) (x : B) (s : B -> Prop) : (term234 B f x s) = (term235 B f x s).
Proof. exact (MK_COMB (@lem4000481) (@lem4000480 B f x s)). Qed.
Lemma lem4000483 {B : Type'} (s : B -> Prop) (f : B -> B) (x : B) (y : B) : (term230 B s f x y) = (term179 B s f x y).
Proof. exact (eq_refl (term230 B s f x y)). Qed.
Lemma lem4000484 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4000485 {B : Type'} (s : B -> Prop) (f : B -> B) (x : B) (y : B) : (term236 B s f x y) = (term237 B s f x y).
Proof. exact (MK_COMB (@lem4000484) (@lem4000483 B s f x y)). Qed.
Lemma lem4000486 {B : Type'} (s : B -> Prop) : (term197 B s) = (term197 B s).
Proof. exact (eq_refl (term197 B s)). Qed.
Lemma lem4000487 {B : Type'} (f : B -> B) (x : B) (y : B) (s : B -> Prop) : (term238 B f x y s) = (term239 B f x y s).
Proof. exact (MK_COMB (@lem4000485 B s f x y) (@lem4000486 B s)). Qed.
Lemma lem4000488 {B : Type'} (f : B -> B) (x : B) (s : B -> Prop) : (term240 B f x s) = (term241 B f x s).
Proof. exact (fun_ext (fun y : B => @lem4000487 B f x y s)). Qed.
Lemma lem4000489 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4000490 {B : Type'} (f : B -> B) (x : B) (s : B -> Prop) : (term229 B f x s) = (term242 B f x s).
Proof. exact (MK_COMB (@lem4000489 B) (@lem4000488 B f x s)). Qed.
Lemma lem4000491 {B : Type'} (f : B -> B) (x : B) (s : B -> Prop) : ((term228 B f x s) = (term229 B f x s)) = ((term224 B f x s) = (term242 B f x s)).
Proof. exact (MK_COMB (@lem4000482 B f x s) (@lem4000490 B f x s)). Qed.
Lemma lem4000492 {B : Type'} (f : B -> B) (x : B) (s : B -> Prop) : (term224 B f x s) = (term242 B f x s).
Proof. exact (EQ_MP (@lem4000491 B f x s) (@lem4000472 B f x s)). Qed.
Lemma lem4000493 {B : Type'} (f : B -> B) (s : B -> Prop) : (term226 B f s) = (term243 B f s).
Proof. exact (fun_ext (fun x : B => @lem4000492 B f x s)). Qed.
Lemma lem4000494 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4000495 {B : Type'} (f : B -> B) (s : B -> Prop) : (term227 B f s) = (term244 B f s).
Proof. exact (MK_COMB (@lem4000494 B) (@lem4000493 B f s)). Qed.
Lemma lem4000496 {B : Type'} (f : B -> B) (s : B -> Prop) : (term201 B f s) = (term244 B f s).
Proof. exact (TRANS (@lem4000468 B f s) (@lem4000495 B f s)). Qed.
Lemma lem4000497 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4000498 {B : Type'} (f : B -> B) (s : B -> Prop) : (term204 B f s) = (term245 B f s).
Proof. exact (MK_COMB (@lem4000497) (@lem4000496 B f s)). Qed.
Lemma lem4000499 {B : Type'} (f : B -> B) (s : B -> Prop) : ((term90 B f s) = (@CARD B s)) = ((term90 B f s) = (@CARD B s)).
Proof. exact (eq_refl ((term90 B f s) = (@CARD B s))). Qed.
Lemma lem4000500 {B : Type'} (f : B -> B) (s : B -> Prop) : (term206 B f s) = (term246 B f s).
Proof. exact (MK_COMB (@lem4000498 B f s) (@lem4000499 B f s)). Qed.
Lemma lem4000502 {A : Type'} (P : A -> Prop) (Q : Prop) : (term211 A P Q) = (term212 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4000503 {B : Type'} (P : B -> Prop) (Q : Prop) : (term211 B P Q) = (term212 B P Q).
Proof. exact (@lem4000502 B P Q). Qed.
Lemma lem4000504 {B : Type'} (f : B -> B) (s : B -> Prop) : (term247 B f s) = (term248 B f s).
Proof. exact (@lem4000503 B (term243 B f s) ((term90 B f s) = (@CARD B s))). Qed.
Lemma lem4000505 {B : Type'} (f : B -> B) (x : B) (s : B -> Prop) : (term249 B f s x) = (term242 B f x s).
Proof. exact (eq_refl (term249 B f s x)). Qed.
Lemma lem4000506 {B : Type'} (f : B -> B) (s : B -> Prop) : (term250 B f s) = (term243 B f s).
Proof. exact (fun_ext (fun x : B => @lem4000505 B f x s)). Qed.
Lemma lem4000507 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4000508 {B : Type'} (f : B -> B) (s : B -> Prop) : (term251 B f s) = (term244 B f s).
Proof. exact (MK_COMB (@lem4000507 B) (@lem4000506 B f s)). Qed.
Lemma lem4000509 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4000510 {B : Type'} (f : B -> B) (s : B -> Prop) : (term252 B f s) = (term245 B f s).
Proof. exact (MK_COMB (@lem4000509) (@lem4000508 B f s)). Qed.
Lemma lem4000511 {B : Type'} (f : B -> B) (s : B -> Prop) : ((term90 B f s) = (@CARD B s)) = ((term90 B f s) = (@CARD B s)).
Proof. exact (eq_refl ((term90 B f s) = (@CARD B s))). Qed.
Lemma lem4000512 {B : Type'} (f : B -> B) (s : B -> Prop) : (term247 B f s) = (term246 B f s).
Proof. exact (MK_COMB (@lem4000510 B f s) (@lem4000511 B f s)). Qed.
Lemma lem4000513 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4000514 {B : Type'} (f : B -> B) (s : B -> Prop) : (term253 B f s) = (term254 B f s).
Proof. exact (MK_COMB (@lem4000513) (@lem4000512 B f s)). Qed.
Lemma lem4000515 {B : Type'} (f : B -> B) (x : B) (s : B -> Prop) : (term249 B f s x) = (term242 B f x s).
Proof. exact (eq_refl (term249 B f s x)). Qed.
Lemma lem4000516 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4000517 {B : Type'} (f : B -> B) (x : B) (s : B -> Prop) : (term255 B f s x) = (term256 B f x s).
Proof. exact (MK_COMB (@lem4000516) (@lem4000515 B f x s)). Qed.
Lemma lem4000518 {B : Type'} (f : B -> B) (s : B -> Prop) : ((term90 B f s) = (@CARD B s)) = ((term90 B f s) = (@CARD B s)).
Proof. exact (eq_refl ((term90 B f s) = (@CARD B s))). Qed.
Lemma lem4000519 {B : Type'} (x : B) (f : B -> B) (s : B -> Prop) : (term257 B x f s) = (term258 B x f s).
Proof. exact (MK_COMB (@lem4000517 B f x s) (@lem4000518 B f s)). Qed.
Lemma lem4000520 {B : Type'} (f : B -> B) (s : B -> Prop) : (term259 B f s) = (term260 B f s).
Proof. exact (fun_ext (fun x : B => @lem4000519 B x f s)). Qed.
Lemma lem4000521 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4000522 {B : Type'} (f : B -> B) (s : B -> Prop) : (term248 B f s) = (term261 B f s).
Proof. exact (MK_COMB (@lem4000521 B) (@lem4000520 B f s)). Qed.
Lemma lem4000523 {B : Type'} (f : B -> B) (s : B -> Prop) : ((term247 B f s) = (term248 B f s)) = ((term246 B f s) = (term261 B f s)).
Proof. exact (MK_COMB (@lem4000514 B f s) (@lem4000522 B f s)). Qed.
Lemma lem4000524 {B : Type'} (f : B -> B) (s : B -> Prop) : (term246 B f s) = (term261 B f s).
Proof. exact (EQ_MP (@lem4000523 B f s) (@lem4000504 B f s)). Qed.
Lemma lem4000526 {A : Type'} (P : A -> Prop) (Q : Prop) : (term211 A P Q) = (term212 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4000527 {B : Type'} (P : B -> Prop) (Q : Prop) : (term211 B P Q) = (term212 B P Q).
Proof. exact (@lem4000526 B P Q). Qed.
Lemma lem4000528 {B : Type'} (x : B) (f : B -> B) (s : B -> Prop) : (term262 B x f s) = (term263 B x f s).
Proof. exact (@lem4000527 B (term241 B f x s) ((term90 B f s) = (@CARD B s))). Qed.
Lemma lem4000529 {B : Type'} (f : B -> B) (x : B) (y : B) (s : B -> Prop) : (term264 B f x s y) = (term239 B f x y s).
Proof. exact (eq_refl (term264 B f x s y)). Qed.
Lemma lem4000530 {B : Type'} (f : B -> B) (x : B) (s : B -> Prop) : (term265 B f x s) = (term241 B f x s).
Proof. exact (fun_ext (fun y : B => @lem4000529 B f x y s)). Qed.
Lemma lem4000531 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4000532 {B : Type'} (f : B -> B) (x : B) (s : B -> Prop) : (term266 B f x s) = (term242 B f x s).
Proof. exact (MK_COMB (@lem4000531 B) (@lem4000530 B f x s)). Qed.
Lemma lem4000533 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4000534 {B : Type'} (f : B -> B) (x : B) (s : B -> Prop) : (term267 B f x s) = (term256 B f x s).
Proof. exact (MK_COMB (@lem4000533) (@lem4000532 B f x s)). Qed.
Lemma lem4000535 {B : Type'} (f : B -> B) (s : B -> Prop) : ((term90 B f s) = (@CARD B s)) = ((term90 B f s) = (@CARD B s)).
Proof. exact (eq_refl ((term90 B f s) = (@CARD B s))). Qed.
Lemma lem4000536 {B : Type'} (x : B) (f : B -> B) (s : B -> Prop) : (term262 B x f s) = (term258 B x f s).
Proof. exact (MK_COMB (@lem4000534 B f x s) (@lem4000535 B f s)). Qed.
Lemma lem4000537 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4000538 {B : Type'} (x : B) (f : B -> B) (s : B -> Prop) : (term268 B x f s) = (term269 B x f s).
Proof. exact (MK_COMB (@lem4000537) (@lem4000536 B x f s)). Qed.
Lemma lem4000539 {B : Type'} (f : B -> B) (x : B) (y : B) (s : B -> Prop) : (term264 B f x s y) = (term239 B f x y s).
Proof. exact (eq_refl (term264 B f x s y)). Qed.
Lemma lem4000540 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4000541 {B : Type'} (f : B -> B) (x : B) (y : B) (s : B -> Prop) : (term270 B f x s y) = (term271 B f x y s).
Proof. exact (MK_COMB (@lem4000540) (@lem4000539 B f x y s)). Qed.
Lemma lem4000542 {B : Type'} (f : B -> B) (s : B -> Prop) : ((term90 B f s) = (@CARD B s)) = ((term90 B f s) = (@CARD B s)).
Proof. exact (eq_refl ((term90 B f s) = (@CARD B s))). Qed.
Lemma lem4000543 {B : Type'} (x : B) (y : B) (f : B -> B) (s : B -> Prop) : (term272 B x y f s) = (term273 B x y f s).
Proof. exact (MK_COMB (@lem4000541 B f x y s) (@lem4000542 B f s)). Qed.
Lemma lem4000544 {B : Type'} (x : B) (f : B -> B) (s : B -> Prop) : (term274 B x f s) = (term275 B x f s).
Proof. exact (fun_ext (fun y : B => @lem4000543 B x y f s)). Qed.
Lemma lem4000545 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4000546 {B : Type'} (x : B) (f : B -> B) (s : B -> Prop) : (term263 B x f s) = (term276 B x f s).
Proof. exact (MK_COMB (@lem4000545 B) (@lem4000544 B x f s)). Qed.
Lemma lem4000547 {B : Type'} (x : B) (f : B -> B) (s : B -> Prop) : ((term262 B x f s) = (term263 B x f s)) = ((term258 B x f s) = (term276 B x f s)).
Proof. exact (MK_COMB (@lem4000538 B x f s) (@lem4000546 B x f s)). Qed.
Lemma lem4000548 {B : Type'} (x : B) (f : B -> B) (s : B -> Prop) : (term258 B x f s) = (term276 B x f s).
Proof. exact (EQ_MP (@lem4000547 B x f s) (@lem4000528 B x f s)). Qed.
Lemma lem4000549 {B : Type'} (f : B -> B) (s : B -> Prop) : (term260 B f s) = (term277 B f s).
Proof. exact (fun_ext (fun x : B => @lem4000548 B x f s)). Qed.
Lemma lem4000550 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4000551 {B : Type'} (f : B -> B) (s : B -> Prop) : (term261 B f s) = (term278 B f s).
Proof. exact (MK_COMB (@lem4000550 B) (@lem4000549 B f s)). Qed.
Lemma lem4000552 {B : Type'} (f : B -> B) (s : B -> Prop) : (term246 B f s) = (term278 B f s).
Proof. exact (TRANS (@lem4000524 B f s) (@lem4000551 B f s)). Qed.
Lemma lem4000553 {B : Type'} (f : B -> B) (s : B -> Prop) : (term206 B f s) = (term278 B f s).
Proof. exact (TRANS (@lem4000500 B f s) (@lem4000552 B f s)). Qed.
Lemma lem4000554 {B : Type'} (f : B -> B) : (term207 B f) = (term279 B f).
Proof. exact (fun_ext (fun s : B -> Prop => @lem4000553 B f s)). Qed.
Lemma lem4000555 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4000556 {B : Type'} (f : B -> B) : (term208 B f) = (term280 B f).
Proof. exact (MK_COMB (@lem4000555 B) (@lem4000554 B f)). Qed.
Lemma lem4000558 {A B : Type'} (P : type1413 A B) : (term281 A B P) = (term282 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4000559 {B : Type'} (P : type672 B) : (term283 B P) = (term284 B P).
Proof. exact (@lem4000558 (B -> Prop) B P). Qed.
Lemma lem4000560 {B : Type'} (f : B -> B) : (term285 B f) = (term286 B f).
Proof. exact (@lem4000559 B (term287 B f)). Qed.
Lemma lem4000561 {B : Type'} (f : B -> B) (s : B -> Prop) : (term288 B f s) = (term277 B f s).
Proof. exact (eq_refl (term288 B f s)). Qed.
Lemma lem4000562 {B : Type'} (x : B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4000563 {B : Type'} (f : B -> B) (s : B -> Prop) (x : B) : (term289 B f s x) = (term290 B f s x).
Proof. exact (MK_COMB (@lem4000561 B f s) (@lem4000562 B x)). Qed.
Lemma lem4000564 {B : Type'} (x : B) (f : B -> B) (s : B -> Prop) : (term290 B f s x) = (term276 B x f s).
Proof. exact (eq_refl (term290 B f s x)). Qed.
Lemma lem4000565 {B : Type'} (x : B) (f : B -> B) (s : B -> Prop) : (term289 B f s x) = (term276 B x f s).
Proof. exact (TRANS (@lem4000563 B f s x) (@lem4000564 B x f s)). Qed.
Lemma lem4000566 {B : Type'} (f : B -> B) (s : B -> Prop) : (term291 B f s) = (term277 B f s).
Proof. exact (fun_ext (fun x : B => @lem4000565 B x f s)). Qed.
Lemma lem4000567 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4000568 {B : Type'} (f : B -> B) (s : B -> Prop) : (term292 B f s) = (term278 B f s).
Proof. exact (MK_COMB (@lem4000567 B) (@lem4000566 B f s)). Qed.
Lemma lem4000569 {B : Type'} (f : B -> B) : (term293 B f) = (term279 B f).
Proof. exact (fun_ext (fun s : B -> Prop => @lem4000568 B f s)). Qed.
Lemma lem4000570 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4000571 {B : Type'} (f : B -> B) : (term285 B f) = (term280 B f).
Proof. exact (MK_COMB (@lem4000570 B) (@lem4000569 B f)). Qed.
Lemma lem4000572 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4000573 {B : Type'} (f : B -> B) : (term294 B f) = (term295 B f).
Proof. exact (MK_COMB (@lem4000572) (@lem4000571 B f)). Qed.
Lemma lem4000574 {B : Type'} (f : B -> B) (s : B -> Prop) : (term288 B f s) = (term277 B f s).
Proof. exact (eq_refl (term288 B f s)). Qed.
Lemma lem4000575 {B : Type'} (x : type684 B) (s : B -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem4000576 {B : Type'} (f : B -> B) (x : type684 B) (s : B -> Prop) : (term296 B f x s) = (term297 B f x s).
Proof. exact (MK_COMB (@lem4000574 B f s) (@lem4000575 B x s)). Qed.
Lemma lem4000577 {B : Type'} (x : type684 B) (f : B -> B) (s : B -> Prop) : (term297 B f x s) = (term298 B x f s).
Proof. exact (eq_refl (term297 B f x s)). Qed.
Lemma lem4000578 {B : Type'} (x : type684 B) (f : B -> B) (s : B -> Prop) : (term296 B f x s) = (term298 B x f s).
Proof. exact (TRANS (@lem4000576 B f x s) (@lem4000577 B x f s)). Qed.
Lemma lem4000579 {B : Type'} (x : type684 B) (f : B -> B) : (term299 B f x) = (term300 B x f).
Proof. exact (fun_ext (fun s : B -> Prop => @lem4000578 B x f s)). Qed.
Lemma lem4000580 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4000581 {B : Type'} (x : type684 B) (f : B -> B) : (term301 B f x) = (term302 B x f).
Proof. exact (MK_COMB (@lem4000580 B) (@lem4000579 B x f)). Qed.
Lemma lem4000582 {B : Type'} (f : B -> B) : (term303 B f) = (term304 B f).
Proof. exact (fun_ext (fun x : type684 B => @lem4000581 B x f)). Qed.
Lemma lem4000583 {B : Type'} : (@ex ((B -> Prop) -> B)) = (@ex ((B -> Prop) -> B)).
Proof. exact (eq_refl (@ex ((B -> Prop) -> B))). Qed.
Lemma lem4000584 {B : Type'} (f : B -> B) : (term286 B f) = (term305 B f).
Proof. exact (MK_COMB (@lem4000583 B) (@lem4000582 B f)). Qed.
Lemma lem4000585 {B : Type'} (f : B -> B) : ((term285 B f) = (term286 B f)) = ((term280 B f) = (term305 B f)).
Proof. exact (MK_COMB (@lem4000573 B f) (@lem4000584 B f)). Qed.
Lemma lem4000586 {B : Type'} (f : B -> B) : (term280 B f) = (term305 B f).
Proof. exact (EQ_MP (@lem4000585 B f) (@lem4000560 B f)). Qed.
Lemma lem4000588 {A B : Type'} (P : type1413 A B) : (term281 A B P) = (term282 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4000589 {B : Type'} (P : type672 B) : (term283 B P) = (term284 B P).
Proof. exact (@lem4000588 (B -> Prop) B P). Qed.
Lemma lem4000590 {B : Type'} (x : type684 B) (f : B -> B) : (term306 B x f) = (term307 B x f).
Proof. exact (@lem4000589 B (term308 B x f)). Qed.
Lemma lem4000591 {B : Type'} (x : type684 B) (f : B -> B) (s : B -> Prop) : (term309 B x f s) = (term310 B x f s).
Proof. exact (eq_refl (term309 B x f s)). Qed.
Lemma lem4000592 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem4000593 {B : Type'} (x : type684 B) (f : B -> B) (s : B -> Prop) (y : B) : (term311 B x f s y) = (term312 B x f s y).
Proof. exact (MK_COMB (@lem4000591 B x f s) (@lem4000592 B y)). Qed.
Lemma lem4000594 {B : Type'} (x : type684 B) (y : B) (f : B -> B) (s : B -> Prop) : (term312 B x f s y) = (term313 B x y f s).
Proof. exact (eq_refl (term312 B x f s y)). Qed.
Lemma lem4000595 {B : Type'} (x : type684 B) (y : B) (f : B -> B) (s : B -> Prop) : (term311 B x f s y) = (term313 B x y f s).
Proof. exact (TRANS (@lem4000593 B x f s y) (@lem4000594 B x y f s)). Qed.
Lemma lem4000596 {B : Type'} (x : type684 B) (f : B -> B) (s : B -> Prop) : (term314 B x f s) = (term310 B x f s).
Proof. exact (fun_ext (fun y : B => @lem4000595 B x y f s)). Qed.
Lemma lem4000597 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4000598 {B : Type'} (x : type684 B) (f : B -> B) (s : B -> Prop) : (term315 B x f s) = (term298 B x f s).
Proof. exact (MK_COMB (@lem4000597 B) (@lem4000596 B x f s)). Qed.
Lemma lem4000599 {B : Type'} (x : type684 B) (f : B -> B) : (term316 B x f) = (term300 B x f).
Proof. exact (fun_ext (fun s : B -> Prop => @lem4000598 B x f s)). Qed.
Lemma lem4000600 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4000601 {B : Type'} (x : type684 B) (f : B -> B) : (term306 B x f) = (term302 B x f).
Proof. exact (MK_COMB (@lem4000600 B) (@lem4000599 B x f)). Qed.
Lemma lem4000602 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4000603 {B : Type'} (x : type684 B) (f : B -> B) : (term317 B x f) = (term318 B x f).
Proof. exact (MK_COMB (@lem4000602) (@lem4000601 B x f)). Qed.
Lemma lem4000604 {B : Type'} (x : type684 B) (f : B -> B) (s : B -> Prop) : (term309 B x f s) = (term310 B x f s).
Proof. exact (eq_refl (term309 B x f s)). Qed.
Lemma lem4000605 {B : Type'} (y : type684 B) (s : B -> Prop) : (y s) = (y s).
Proof. exact (eq_refl (y s)). Qed.
Lemma lem4000606 {B : Type'} (x : type684 B) (f : B -> B) (y : type684 B) (s : B -> Prop) : (term319 B x f y s) = (term320 B x f y s).
Proof. exact (MK_COMB (@lem4000604 B x f s) (@lem4000605 B y s)). Qed.
Lemma lem4000607 {B : Type'} (x : type684 B) (y : type684 B) (f : B -> B) (s : B -> Prop) : (term320 B x f y s) = (term321 B x y f s).
Proof. exact (eq_refl (term320 B x f y s)). Qed.
Lemma lem4000608 {B : Type'} (x : type684 B) (y : type684 B) (f : B -> B) (s : B -> Prop) : (term319 B x f y s) = (term321 B x y f s).
Proof. exact (TRANS (@lem4000606 B x f y s) (@lem4000607 B x y f s)). Qed.
Lemma lem4000609 {B : Type'} (x : type684 B) (y : type684 B) (f : B -> B) : (term322 B x f y) = (term323 B x y f).
Proof. exact (fun_ext (fun s : B -> Prop => @lem4000608 B x y f s)). Qed.
Lemma lem4000610 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4000611 {B : Type'} (x : type684 B) (y : type684 B) (f : B -> B) : (term324 B x f y) = (term325 B x y f).
Proof. exact (MK_COMB (@lem4000610 B) (@lem4000609 B x y f)). Qed.
Lemma lem4000612 {B : Type'} (x : type684 B) (f : B -> B) : (term326 B x f) = (term327 B x f).
Proof. exact (fun_ext (fun y : type684 B => @lem4000611 B x y f)). Qed.
Lemma lem4000613 {B : Type'} : (@ex ((B -> Prop) -> B)) = (@ex ((B -> Prop) -> B)).
Proof. exact (eq_refl (@ex ((B -> Prop) -> B))). Qed.
Lemma lem4000614 {B : Type'} (x : type684 B) (f : B -> B) : (term307 B x f) = (term328 B x f).
Proof. exact (MK_COMB (@lem4000613 B) (@lem4000612 B x f)). Qed.
Lemma lem4000615 {B : Type'} (x : type684 B) (f : B -> B) : ((term306 B x f) = (term307 B x f)) = ((term302 B x f) = (term328 B x f)).
Proof. exact (MK_COMB (@lem4000603 B x f) (@lem4000614 B x f)). Qed.
Lemma lem4000616 {B : Type'} (x : type684 B) (f : B -> B) : (term302 B x f) = (term328 B x f).
Proof. exact (EQ_MP (@lem4000615 B x f) (@lem4000590 B x f)). Qed.
Lemma lem4000617 {B : Type'} (f : B -> B) : (term304 B f) = (term329 B f).
Proof. exact (fun_ext (fun x : type684 B => @lem4000616 B x f)). Qed.
Lemma lem4000618 {B : Type'} : (@ex ((B -> Prop) -> B)) = (@ex ((B -> Prop) -> B)).
Proof. exact (eq_refl (@ex ((B -> Prop) -> B))). Qed.
Lemma lem4000619 {B : Type'} (f : B -> B) : (term305 B f) = (term330 B f).
Proof. exact (MK_COMB (@lem4000618 B) (@lem4000617 B f)). Qed.
Lemma lem4000620 {B : Type'} (f : B -> B) : (term280 B f) = (term330 B f).
Proof. exact (TRANS (@lem4000586 B f) (@lem4000619 B f)). Qed.
Lemma lem4000621 {B : Type'} (f : B -> B) : (term208 B f) = (term330 B f).
Proof. exact (TRANS (@lem4000556 B f) (@lem4000620 B f)). Qed.
Lemma lem4000622 {B : Type'} : (term209 B) = (term331 B).
Proof. exact (fun_ext (fun f : B -> B => @lem4000621 B f)). Qed.
Lemma lem4000623 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem4000624 {B : Type'} : (term210 B) = (term332 B).
Proof. exact (MK_COMB (@lem4000623 B) (@lem4000622 B)). Qed.
Lemma lem4000626 {A B : Type'} (P : type1413 A B) : (term281 A B P) = (term282 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4000627 {B : Type'} (P : type481 B) : (term333 B P) = (term334 B P).
Proof. exact (@lem4000626 (B -> B) (type684 B) P). Qed.
Lemma lem4000628 {B : Type'} : (term335 B) = (term336 B).
Proof. exact (@lem4000627 B (term337 B)). Qed.
Lemma lem4000629 {B : Type'} (f : B -> B) : (term338 B f) = (term329 B f).
Proof. exact (eq_refl (term338 B f)). Qed.
Lemma lem4000630 {B : Type'} (x : type684 B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4000631 {B : Type'} (f : B -> B) (x : type684 B) : (term339 B f x) = (term340 B f x).
Proof. exact (MK_COMB (@lem4000629 B f) (@lem4000630 B x)). Qed.
Lemma lem4000632 {B : Type'} (x : type684 B) (f : B -> B) : (term340 B f x) = (term328 B x f).
Proof. exact (eq_refl (term340 B f x)). Qed.
Lemma lem4000633 {B : Type'} (x : type684 B) (f : B -> B) : (term339 B f x) = (term328 B x f).
Proof. exact (TRANS (@lem4000631 B f x) (@lem4000632 B x f)). Qed.
Lemma lem4000634 {B : Type'} (f : B -> B) : (term341 B f) = (term329 B f).
Proof. exact (fun_ext (fun x : type684 B => @lem4000633 B x f)). Qed.
Lemma lem4000635 {B : Type'} : (@ex ((B -> Prop) -> B)) = (@ex ((B -> Prop) -> B)).
Proof. exact (eq_refl (@ex ((B -> Prop) -> B))). Qed.
Lemma lem4000636 {B : Type'} (f : B -> B) : (term342 B f) = (term330 B f).
Proof. exact (MK_COMB (@lem4000635 B) (@lem4000634 B f)). Qed.
Lemma lem4000637 {B : Type'} : (term343 B) = (term331 B).
Proof. exact (fun_ext (fun f : B -> B => @lem4000636 B f)). Qed.
Lemma lem4000638 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem4000639 {B : Type'} : (term335 B) = (term332 B).
Proof. exact (MK_COMB (@lem4000638 B) (@lem4000637 B)). Qed.
Lemma lem4000640 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4000641 {B : Type'} : (term344 B) = (term345 B).
Proof. exact (MK_COMB (@lem4000640) (@lem4000639 B)). Qed.
Lemma lem4000642 {B : Type'} (f : B -> B) : (term338 B f) = (term329 B f).
Proof. exact (eq_refl (term338 B f)). Qed.
Lemma lem4000643 {B : Type'} (x : type485 B) (f : B -> B) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem4000644 {B : Type'} (x : type485 B) (f : B -> B) : (term346 B x f) = (term347 B x f).
Proof. exact (MK_COMB (@lem4000642 B f) (@lem4000643 B x f)). Qed.
Lemma lem4000645 {B : Type'} (x : type485 B) (f : B -> B) : (term347 B x f) = (term348 B x f).
Proof. exact (eq_refl (term347 B x f)). Qed.
Lemma lem4000646 {B : Type'} (x : type485 B) (f : B -> B) : (term346 B x f) = (term348 B x f).
Proof. exact (TRANS (@lem4000644 B x f) (@lem4000645 B x f)). Qed.
Lemma lem4000647 {B : Type'} (x : type485 B) : (term349 B x) = (term350 B x).
Proof. exact (fun_ext (fun f : B -> B => @lem4000646 B x f)). Qed.
Lemma lem4000648 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem4000649 {B : Type'} (x : type485 B) : (term351 B x) = (term352 B x).
Proof. exact (MK_COMB (@lem4000648 B) (@lem4000647 B x)). Qed.
Lemma lem4000650 {B : Type'} : (term353 B) = (term354 B).
Proof. exact (fun_ext (fun x : type485 B => @lem4000649 B x)). Qed.
Lemma lem4000651 {B : Type'} : (@ex ((B -> B) -> (B -> Prop) -> B)) = (@ex ((B -> B) -> (B -> Prop) -> B)).
Proof. exact (eq_refl (@ex ((B -> B) -> (B -> Prop) -> B))). Qed.
Lemma lem4000652 {B : Type'} : (term336 B) = (term355 B).
Proof. exact (MK_COMB (@lem4000651 B) (@lem4000650 B)). Qed.
Lemma lem4000653 {B : Type'} : ((term335 B) = (term336 B)) = ((term332 B) = (term355 B)).
Proof. exact (MK_COMB (@lem4000641 B) (@lem4000652 B)). Qed.
Lemma lem4000654 {B : Type'} : (term332 B) = (term355 B).
Proof. exact (EQ_MP (@lem4000653 B) (@lem4000628 B)). Qed.
Lemma lem4000656 {A B : Type'} (P : type1413 A B) : (term281 A B P) = (term282 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4000657 {B : Type'} (P : type481 B) : (term333 B P) = (term334 B P).
Proof. exact (@lem4000656 (B -> B) (type684 B) P). Qed.
Lemma lem4000658 {B : Type'} (x : type485 B) : (term356 B x) = (term357 B x).
Proof. exact (@lem4000657 B (term358 B x)). Qed.
Lemma lem4000659 {B : Type'} (x : type485 B) (f : B -> B) : (term359 B x f) = (term360 B x f).
Proof. exact (eq_refl (term359 B x f)). Qed.
Lemma lem4000660 {B : Type'} (y : type684 B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem4000661 {B : Type'} (x : type485 B) (f : B -> B) (y : type684 B) : (term361 B x f y) = (term362 B x f y).
Proof. exact (MK_COMB (@lem4000659 B x f) (@lem4000660 B y)). Qed.
Lemma lem4000662 {B : Type'} (x : type485 B) (y : type684 B) (f : B -> B) : (term362 B x f y) = (term363 B x y f).
Proof. exact (eq_refl (term362 B x f y)). Qed.
Lemma lem4000663 {B : Type'} (x : type485 B) (y : type684 B) (f : B -> B) : (term361 B x f y) = (term363 B x y f).
Proof. exact (TRANS (@lem4000661 B x f y) (@lem4000662 B x y f)). Qed.
Lemma lem4000664 {B : Type'} (x : type485 B) (f : B -> B) : (term364 B x f) = (term360 B x f).
Proof. exact (fun_ext (fun y : type684 B => @lem4000663 B x y f)). Qed.
Lemma lem4000665 {B : Type'} : (@ex ((B -> Prop) -> B)) = (@ex ((B -> Prop) -> B)).
Proof. exact (eq_refl (@ex ((B -> Prop) -> B))). Qed.
Lemma lem4000666 {B : Type'} (x : type485 B) (f : B -> B) : (term365 B x f) = (term348 B x f).
Proof. exact (MK_COMB (@lem4000665 B) (@lem4000664 B x f)). Qed.
Lemma lem4000667 {B : Type'} (x : type485 B) : (term366 B x) = (term350 B x).
Proof. exact (fun_ext (fun f : B -> B => @lem4000666 B x f)). Qed.
Lemma lem4000668 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem4000669 {B : Type'} (x : type485 B) : (term356 B x) = (term352 B x).
Proof. exact (MK_COMB (@lem4000668 B) (@lem4000667 B x)). Qed.
Lemma lem4000670 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4000671 {B : Type'} (x : type485 B) : (term367 B x) = (term368 B x).
Proof. exact (MK_COMB (@lem4000670) (@lem4000669 B x)). Qed.
Lemma lem4000672 {B : Type'} (x : type485 B) (f : B -> B) : (term359 B x f) = (term360 B x f).
Proof. exact (eq_refl (term359 B x f)). Qed.
Lemma lem4000673 {B : Type'} (y : type485 B) (f : B -> B) : (y f) = (y f).
Proof. exact (eq_refl (y f)). Qed.
Lemma lem4000674 {B : Type'} (x : type485 B) (y : type485 B) (f : B -> B) : (term369 B x y f) = (term370 B x y f).
Proof. exact (MK_COMB (@lem4000672 B x f) (@lem4000673 B y f)). Qed.
Lemma lem4000675 {B : Type'} (x : type485 B) (y : type485 B) (f : B -> B) : (term370 B x y f) = (term371 B x y f).
Proof. exact (eq_refl (term370 B x y f)). Qed.
Lemma lem4000676 {B : Type'} (x : type485 B) (y : type485 B) (f : B -> B) : (term369 B x y f) = (term371 B x y f).
Proof. exact (TRANS (@lem4000674 B x y f) (@lem4000675 B x y f)). Qed.
Lemma lem4000677 {B : Type'} (x : type485 B) (y : type485 B) : (term372 B x y) = (term373 B x y).
Proof. exact (fun_ext (fun f : B -> B => @lem4000676 B x y f)). Qed.
Lemma lem4000678 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem4000679 {B : Type'} (x : type485 B) (y : type485 B) : (term374 B x y) = (term375 B x y).
Proof. exact (MK_COMB (@lem4000678 B) (@lem4000677 B x y)). Qed.
Lemma lem4000680 {B : Type'} (x : type485 B) : (term376 B x) = (term377 B x).
Proof. exact (fun_ext (fun y : type485 B => @lem4000679 B x y)). Qed.
Lemma lem4000681 {B : Type'} : (@ex ((B -> B) -> (B -> Prop) -> B)) = (@ex ((B -> B) -> (B -> Prop) -> B)).
Proof. exact (eq_refl (@ex ((B -> B) -> (B -> Prop) -> B))). Qed.
Lemma lem4000682 {B : Type'} (x : type485 B) : (term357 B x) = (term378 B x).
Proof. exact (MK_COMB (@lem4000681 B) (@lem4000680 B x)). Qed.
Lemma lem4000683 {B : Type'} (x : type485 B) : ((term356 B x) = (term357 B x)) = ((term352 B x) = (term378 B x)).
Proof. exact (MK_COMB (@lem4000671 B x) (@lem4000682 B x)). Qed.
Lemma lem4000684 {B : Type'} (x : type485 B) : (term352 B x) = (term378 B x).
Proof. exact (EQ_MP (@lem4000683 B x) (@lem4000658 B x)). Qed.
Lemma lem4000685 {B : Type'} : (term354 B) = (term379 B).
Proof. exact (fun_ext (fun x : type485 B => @lem4000684 B x)). Qed.
Lemma lem4000686 {B : Type'} : (@ex ((B -> B) -> (B -> Prop) -> B)) = (@ex ((B -> B) -> (B -> Prop) -> B)).
Proof. exact (eq_refl (@ex ((B -> B) -> (B -> Prop) -> B))). Qed.
Lemma lem4000687 {B : Type'} : (term355 B) = (term380 B).
Proof. exact (MK_COMB (@lem4000686 B) (@lem4000685 B)). Qed.
Lemma lem4000688 {B : Type'} : (term332 B) = (term380 B).
Proof. exact (TRANS (@lem4000654 B) (@lem4000687 B)). Qed.
Lemma lem4000690 {B : Type'} : (term210 B) = (term380 B).
Proof. exact (TRANS (@lem4000624 B) (@lem4000688 B)). Qed.
Lemma lem4000691 {B : Type'} : (term55 B) = (term380 B).
Proof. exact (TRANS (@lem4000339 B) (@lem4000690 B)). Qed.
Lemma lem4000692 {B : Type'} (h1 : term55 B) : term380 B.
Proof. exact (EQ_MP (@lem4000691 B) (@lem3998885 B h1)). Qed.
Lemma lem4000707 {B : Type'} (s : nat -> Prop) (f : nat -> B) (x : nat) (y : nat) : (term768 B s f x y) = (term769 B s f x y).
Proof. exact (@lem17362 (term770 B s x f y) (x = y)). Qed.
Lemma lem4000708 (P : nat -> Prop) : (term152 P) = (term153 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem4000709 {B : Type'} (s : nat -> Prop) (f : nat -> B) (x : nat) : (term771 B s f x) = (term772 B s f x).
Proof. exact (@lem4000708 (term79 B s f x)). Qed.
Lemma lem4000710 {B : Type'} (s : nat -> Prop) (f : nat -> B) (x : nat) (y : nat) : (term773 B s f x y) = (term78 B s f x y).
Proof. exact (eq_refl (term773 B s f x y)). Qed.
Lemma lem4000711 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4000712 {B : Type'} (s : nat -> Prop) (f : nat -> B) (x : nat) (y : nat) : (term774 B s f x y) = (term768 B s f x y).
Proof. exact (MK_COMB (@lem4000711) (@lem4000710 B s f x y)). Qed.
Lemma lem4000713 {B : Type'} (s : nat -> Prop) (f : nat -> B) (x : nat) (y : nat) : (term774 B s f x y) = (term769 B s f x y).
Proof. exact (TRANS (@lem4000712 B s f x y) (@lem4000707 B s f x y)). Qed.
Lemma lem4000714 {B : Type'} (s : nat -> Prop) (f : nat -> B) (x : nat) : (term775 B s f x) = (term776 B s f x).
Proof. exact (fun_ext (fun y : nat => @lem4000713 B s f x y)). Qed.
Lemma lem4000715 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4000716 {B : Type'} (s : nat -> Prop) (f : nat -> B) (x : nat) : (term772 B s f x) = (term777 B s f x).
Proof. exact (MK_COMB (@lem4000715) (@lem4000714 B s f x)). Qed.
Lemma lem4000717 {B : Type'} (s : nat -> Prop) (f : nat -> B) (x : nat) : (term771 B s f x) = (term777 B s f x).
Proof. exact (TRANS (@lem4000709 B s f x) (@lem4000716 B s f x)). Qed.
Lemma lem4000718 (P : nat -> Prop) : (term152 P) = (term153 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem4000719 {B : Type'} (s : nat -> Prop) (f : nat -> B) : (term778 B s f) = (term779 B s f).
Proof. exact (@lem4000718 (term81 B s f)). Qed.
Lemma lem4000720 {B : Type'} (s : nat -> Prop) (f : nat -> B) (x : nat) : (term780 B s f x) = (term80 B s f x).
Proof. exact (eq_refl (term780 B s f x)). Qed.
Lemma lem4000721 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4000722 {B : Type'} (s : nat -> Prop) (f : nat -> B) (x : nat) : (term781 B s f x) = (term771 B s f x).
Proof. exact (MK_COMB (@lem4000721) (@lem4000720 B s f x)). Qed.
Lemma lem4000723 {B : Type'} (s : nat -> Prop) (f : nat -> B) (x : nat) : (term781 B s f x) = (term777 B s f x).
Proof. exact (TRANS (@lem4000722 B s f x) (@lem4000717 B s f x)). Qed.
Lemma lem4000724 {B : Type'} (s : nat -> Prop) (f : nat -> B) : (term782 B s f) = (term783 B s f).
Proof. exact (fun_ext (fun x : nat => @lem4000723 B s f x)). Qed.
Lemma lem4000725 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4000726 {B : Type'} (s : nat -> Prop) (f : nat -> B) : (term779 B s f) = (term784 B s f).
Proof. exact (MK_COMB (@lem4000725) (@lem4000724 B s f)). Qed.
Lemma lem4000727 {B : Type'} (s : nat -> Prop) (f : nat -> B) : (term778 B s f) = (term784 B s f).
Proof. exact (TRANS (@lem4000719 B s f) (@lem4000726 B s f)). Qed.
Lemma lem4000728 (s : nat -> Prop) : (term785 s) = (term785 s).
Proof. exact (eq_refl (term785 s)). Qed.
Lemma lem4000729 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4000730 {B : Type'} (s : nat -> Prop) (f : nat -> B) : (term786 B s f) = (term787 B s f).
Proof. exact (MK_COMB (@lem4000729) (@lem4000727 B s f)). Qed.
Lemma lem4000731 {B : Type'} (f : nat -> B) (s : nat -> Prop) : (term788 B f s) = (term789 B f s).
Proof. exact (MK_COMB (@lem4000730 B s f) (@lem4000728 s)). Qed.
Lemma lem4000732 {B : Type'} (f : nat -> B) (s : nat -> Prop) : (term790 B f s) = (term788 B f s).
Proof. exact (@lem17045 (term82 B s f) (@FINITE nat s)). Qed.
Lemma lem4000733 {B : Type'} (f : nat -> B) (s : nat -> Prop) : (term790 B f s) = (term789 B f s).
Proof. exact (TRANS (@lem4000732 B f s) (@lem4000731 B f s)). Qed.
Lemma lem4000734 {B : Type'} (f : nat -> B) (s : nat -> Prop) : ((term77 B f s) = (@CARD nat s)) = ((term77 B f s) = (@CARD nat s)).
Proof. exact (eq_refl ((term77 B f s) = (@CARD nat s))). Qed.
Lemma lem4000735 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4000736 {B : Type'} (f : nat -> B) (s : nat -> Prop) : (term791 B f s) = (term792 B f s).
Proof. exact (MK_COMB (@lem4000735) (@lem4000733 B f s)). Qed.
Lemma lem4000737 {B : Type'} (f : nat -> B) (s : nat -> Prop) : (term793 B f s) = (term794 B f s).
Proof. exact (MK_COMB (@lem4000736 B f s) (@lem4000734 B f s)). Qed.
Lemma lem4000738 {B : Type'} (f : nat -> B) (s : nat -> Prop) : (term86 B f s) = (term793 B f s).
Proof. exact (@lem17265 (term84 B f s) ((term77 B f s) = (@CARD nat s))). Qed.
Lemma lem4000739 {B : Type'} (f : nat -> B) (s : nat -> Prop) : (term86 B f s) = (term794 B f s).
Proof. exact (TRANS (@lem4000738 B f s) (@lem4000737 B f s)). Qed.
Lemma lem4000740 {B : Type'} (f : nat -> B) : (term87 B f) = (term795 B f).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem4000739 B f s)). Qed.
Lemma lem4000741 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem4000742 {B : Type'} (f : nat -> B) : (term88 B f) = (term796 B f).
Proof. exact (MK_COMB (@lem4000741) (@lem4000740 B f)). Qed.
Lemma lem4000743 {B : Type'} : (term89 B) = (term797 B).
Proof. exact (fun_ext (fun f : nat -> B => @lem4000742 B f)). Qed.
Lemma lem4000744 {B : Type'} : (@all (nat -> B)) = (@all (nat -> B)).
Proof. exact (eq_refl (@all (nat -> B))). Qed.
Lemma lem4000745 {B : Type'} : (term57 B) = (term798 B).
Proof. exact (MK_COMB (@lem4000744 B) (@lem4000743 B)). Qed.
Lemma lem4000852 {A : Type'} (P : A -> Prop) (Q : Prop) : (term211 A P Q) = (term212 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4000853 (P : nat -> Prop) (Q : Prop) : (term799 P Q) = (term800 P Q).
Proof. exact (@lem4000852 nat P Q). Qed.
Lemma lem4000854 {B : Type'} (f : nat -> B) (s : nat -> Prop) : (term801 B f s) = (term802 B f s).
Proof. exact (@lem4000853 (term783 B s f) (term785 s)). Qed.
Lemma lem4000855 {B : Type'} (s : nat -> Prop) (f : nat -> B) (x : nat) : (term803 B s f x) = (term777 B s f x).
Proof. exact (eq_refl (term803 B s f x)). Qed.
Lemma lem4000856 {B : Type'} (s : nat -> Prop) (f : nat -> B) : (term804 B s f) = (term783 B s f).
Proof. exact (fun_ext (fun x : nat => @lem4000855 B s f x)). Qed.
Lemma lem4000857 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4000858 {B : Type'} (s : nat -> Prop) (f : nat -> B) : (term805 B s f) = (term784 B s f).
Proof. exact (MK_COMB (@lem4000857) (@lem4000856 B s f)). Qed.
Lemma lem4000859 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4000860 {B : Type'} (s : nat -> Prop) (f : nat -> B) : (term806 B s f) = (term787 B s f).
Proof. exact (MK_COMB (@lem4000859) (@lem4000858 B s f)). Qed.
Lemma lem4000861 (s : nat -> Prop) : (term785 s) = (term785 s).
Proof. exact (eq_refl (term785 s)). Qed.
Lemma lem4000862 {B : Type'} (f : nat -> B) (s : nat -> Prop) : (term801 B f s) = (term789 B f s).
Proof. exact (MK_COMB (@lem4000860 B s f) (@lem4000861 s)). Qed.
Lemma lem4000863 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4000864 {B : Type'} (f : nat -> B) (s : nat -> Prop) : (term807 B f s) = (term808 B f s).
Proof. exact (MK_COMB (@lem4000863) (@lem4000862 B f s)). Qed.
Lemma lem4000865 {B : Type'} (s : nat -> Prop) (f : nat -> B) (x : nat) : (term803 B s f x) = (term777 B s f x).
Proof. exact (eq_refl (term803 B s f x)). Qed.
Lemma lem4000866 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4000867 {B : Type'} (s : nat -> Prop) (f : nat -> B) (x : nat) : (term809 B s f x) = (term810 B s f x).
Proof. exact (MK_COMB (@lem4000866) (@lem4000865 B s f x)). Qed.
Lemma lem4000868 (s : nat -> Prop) : (term785 s) = (term785 s).
Proof. exact (eq_refl (term785 s)). Qed.
Lemma lem4000869 {B : Type'} (f : nat -> B) (x : nat) (s : nat -> Prop) : (term811 B f x s) = (term812 B f x s).
Proof. exact (MK_COMB (@lem4000867 B s f x) (@lem4000868 s)). Qed.
Lemma lem4000870 {B : Type'} (f : nat -> B) (s : nat -> Prop) : (term813 B f s) = (term814 B f s).
Proof. exact (fun_ext (fun x : nat => @lem4000869 B f x s)). Qed.
Lemma lem4000871 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4000872 {B : Type'} (f : nat -> B) (s : nat -> Prop) : (term802 B f s) = (term815 B f s).
Proof. exact (MK_COMB (@lem4000871) (@lem4000870 B f s)). Qed.
Lemma lem4000873 {B : Type'} (f : nat -> B) (s : nat -> Prop) : ((term801 B f s) = (term802 B f s)) = ((term789 B f s) = (term815 B f s)).
Proof. exact (MK_COMB (@lem4000864 B f s) (@lem4000872 B f s)). Qed.
Lemma lem4000874 {B : Type'} (f : nat -> B) (s : nat -> Prop) : (term789 B f s) = (term815 B f s).
Proof. exact (EQ_MP (@lem4000873 B f s) (@lem4000854 B f s)). Qed.
Lemma lem4000876 {A : Type'} (P : A -> Prop) (Q : Prop) : (term211 A P Q) = (term212 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4000877 (P : nat -> Prop) (Q : Prop) : (term799 P Q) = (term800 P Q).
Proof. exact (@lem4000876 nat P Q). Qed.
Lemma lem4000878 {B : Type'} (f : nat -> B) (x : nat) (s : nat -> Prop) : (term816 B f x s) = (term817 B f x s).
Proof. exact (@lem4000877 (term776 B s f x) (term785 s)). Qed.
Lemma lem4000879 {B : Type'} (s : nat -> Prop) (f : nat -> B) (x : nat) (y : nat) : (term818 B s f x y) = (term769 B s f x y).
Proof. exact (eq_refl (term818 B s f x y)). Qed.
Lemma lem4000880 {B : Type'} (s : nat -> Prop) (f : nat -> B) (x : nat) : (term819 B s f x) = (term776 B s f x).
Proof. exact (fun_ext (fun y : nat => @lem4000879 B s f x y)). Qed.
Lemma lem4000881 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4000882 {B : Type'} (s : nat -> Prop) (f : nat -> B) (x : nat) : (term820 B s f x) = (term777 B s f x).
Proof. exact (MK_COMB (@lem4000881) (@lem4000880 B s f x)). Qed.
Lemma lem4000883 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4000884 {B : Type'} (s : nat -> Prop) (f : nat -> B) (x : nat) : (term821 B s f x) = (term810 B s f x).
Proof. exact (MK_COMB (@lem4000883) (@lem4000882 B s f x)). Qed.
Lemma lem4000885 (s : nat -> Prop) : (term785 s) = (term785 s).
Proof. exact (eq_refl (term785 s)). Qed.
Lemma lem4000886 {B : Type'} (f : nat -> B) (x : nat) (s : nat -> Prop) : (term816 B f x s) = (term812 B f x s).
Proof. exact (MK_COMB (@lem4000884 B s f x) (@lem4000885 s)). Qed.
Lemma lem4000887 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4000888 {B : Type'} (f : nat -> B) (x : nat) (s : nat -> Prop) : (term822 B f x s) = (term823 B f x s).
Proof. exact (MK_COMB (@lem4000887) (@lem4000886 B f x s)). Qed.
Lemma lem4000889 {B : Type'} (s : nat -> Prop) (f : nat -> B) (x : nat) (y : nat) : (term818 B s f x y) = (term769 B s f x y).
Proof. exact (eq_refl (term818 B s f x y)). Qed.
Lemma lem4000890 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4000891 {B : Type'} (s : nat -> Prop) (f : nat -> B) (x : nat) (y : nat) : (term824 B s f x y) = (term825 B s f x y).
Proof. exact (MK_COMB (@lem4000890) (@lem4000889 B s f x y)). Qed.
Lemma lem4000892 (s : nat -> Prop) : (term785 s) = (term785 s).
Proof. exact (eq_refl (term785 s)). Qed.
Lemma lem4000893 {B : Type'} (f : nat -> B) (x : nat) (y : nat) (s : nat -> Prop) : (term826 B f x y s) = (term827 B f x y s).
Proof. exact (MK_COMB (@lem4000891 B s f x y) (@lem4000892 s)). Qed.
Lemma lem4000894 {B : Type'} (f : nat -> B) (x : nat) (s : nat -> Prop) : (term828 B f x s) = (term829 B f x s).
Proof. exact (fun_ext (fun y : nat => @lem4000893 B f x y s)). Qed.
Lemma lem4000895 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4000896 {B : Type'} (f : nat -> B) (x : nat) (s : nat -> Prop) : (term817 B f x s) = (term830 B f x s).
Proof. exact (MK_COMB (@lem4000895) (@lem4000894 B f x s)). Qed.
Lemma lem4000897 {B : Type'} (f : nat -> B) (x : nat) (s : nat -> Prop) : ((term816 B f x s) = (term817 B f x s)) = ((term812 B f x s) = (term830 B f x s)).
Proof. exact (MK_COMB (@lem4000888 B f x s) (@lem4000896 B f x s)). Qed.
Lemma lem4000898 {B : Type'} (f : nat -> B) (x : nat) (s : nat -> Prop) : (term812 B f x s) = (term830 B f x s).
Proof. exact (EQ_MP (@lem4000897 B f x s) (@lem4000878 B f x s)). Qed.
Lemma lem4000899 {B : Type'} (f : nat -> B) (s : nat -> Prop) : (term814 B f s) = (term831 B f s).
Proof. exact (fun_ext (fun x : nat => @lem4000898 B f x s)). Qed.
Lemma lem4000900 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4000901 {B : Type'} (f : nat -> B) (s : nat -> Prop) : (term815 B f s) = (term832 B f s).
Proof. exact (MK_COMB (@lem4000900) (@lem4000899 B f s)). Qed.
Lemma lem4000902 {B : Type'} (f : nat -> B) (s : nat -> Prop) : (term789 B f s) = (term832 B f s).
Proof. exact (TRANS (@lem4000874 B f s) (@lem4000901 B f s)). Qed.
Lemma lem4000903 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4000904 {B : Type'} (f : nat -> B) (s : nat -> Prop) : (term792 B f s) = (term833 B f s).
Proof. exact (MK_COMB (@lem4000903) (@lem4000902 B f s)). Qed.
Lemma lem4000905 {B : Type'} (f : nat -> B) (s : nat -> Prop) : ((term77 B f s) = (@CARD nat s)) = ((term77 B f s) = (@CARD nat s)).
Proof. exact (eq_refl ((term77 B f s) = (@CARD nat s))). Qed.
Lemma lem4000906 {B : Type'} (f : nat -> B) (s : nat -> Prop) : (term794 B f s) = (term834 B f s).
Proof. exact (MK_COMB (@lem4000904 B f s) (@lem4000905 B f s)). Qed.
Lemma lem4000908 {A : Type'} (P : A -> Prop) (Q : Prop) : (term211 A P Q) = (term212 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4000909 (P : nat -> Prop) (Q : Prop) : (term799 P Q) = (term800 P Q).
Proof. exact (@lem4000908 nat P Q). Qed.
Lemma lem4000910 {B : Type'} (f : nat -> B) (s : nat -> Prop) : (term835 B f s) = (term836 B f s).
Proof. exact (@lem4000909 (term831 B f s) ((term77 B f s) = (@CARD nat s))). Qed.
Lemma lem4000911 {B : Type'} (f : nat -> B) (x : nat) (s : nat -> Prop) : (term837 B f s x) = (term830 B f x s).
Proof. exact (eq_refl (term837 B f s x)). Qed.
Lemma lem4000912 {B : Type'} (f : nat -> B) (s : nat -> Prop) : (term838 B f s) = (term831 B f s).
Proof. exact (fun_ext (fun x : nat => @lem4000911 B f x s)). Qed.
Lemma lem4000913 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4000914 {B : Type'} (f : nat -> B) (s : nat -> Prop) : (term839 B f s) = (term832 B f s).
Proof. exact (MK_COMB (@lem4000913) (@lem4000912 B f s)). Qed.
Lemma lem4000915 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4000916 {B : Type'} (f : nat -> B) (s : nat -> Prop) : (term840 B f s) = (term833 B f s).
Proof. exact (MK_COMB (@lem4000915) (@lem4000914 B f s)). Qed.
Lemma lem4000917 {B : Type'} (f : nat -> B) (s : nat -> Prop) : ((term77 B f s) = (@CARD nat s)) = ((term77 B f s) = (@CARD nat s)).
Proof. exact (eq_refl ((term77 B f s) = (@CARD nat s))). Qed.
Lemma lem4000918 {B : Type'} (f : nat -> B) (s : nat -> Prop) : (term835 B f s) = (term834 B f s).
Proof. exact (MK_COMB (@lem4000916 B f s) (@lem4000917 B f s)). Qed.
Lemma lem4000919 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4000920 {B : Type'} (f : nat -> B) (s : nat -> Prop) : (term841 B f s) = (term842 B f s).
Proof. exact (MK_COMB (@lem4000919) (@lem4000918 B f s)). Qed.
Lemma lem4000921 {B : Type'} (f : nat -> B) (x : nat) (s : nat -> Prop) : (term837 B f s x) = (term830 B f x s).
Proof. exact (eq_refl (term837 B f s x)). Qed.
Lemma lem4000922 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4000923 {B : Type'} (f : nat -> B) (x : nat) (s : nat -> Prop) : (term843 B f s x) = (term844 B f x s).
Proof. exact (MK_COMB (@lem4000922) (@lem4000921 B f x s)). Qed.
Lemma lem4000924 {B : Type'} (f : nat -> B) (s : nat -> Prop) : ((term77 B f s) = (@CARD nat s)) = ((term77 B f s) = (@CARD nat s)).
Proof. exact (eq_refl ((term77 B f s) = (@CARD nat s))). Qed.
Lemma lem4000925 {B : Type'} (x : nat) (f : nat -> B) (s : nat -> Prop) : (term845 B x f s) = (term846 B x f s).
Proof. exact (MK_COMB (@lem4000923 B f x s) (@lem4000924 B f s)). Qed.
Lemma lem4000926 {B : Type'} (f : nat -> B) (s : nat -> Prop) : (term847 B f s) = (term848 B f s).
Proof. exact (fun_ext (fun x : nat => @lem4000925 B x f s)). Qed.
Lemma lem4000927 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4000928 {B : Type'} (f : nat -> B) (s : nat -> Prop) : (term836 B f s) = (term849 B f s).
Proof. exact (MK_COMB (@lem4000927) (@lem4000926 B f s)). Qed.
Lemma lem4000929 {B : Type'} (f : nat -> B) (s : nat -> Prop) : ((term835 B f s) = (term836 B f s)) = ((term834 B f s) = (term849 B f s)).
Proof. exact (MK_COMB (@lem4000920 B f s) (@lem4000928 B f s)). Qed.
Lemma lem4000930 {B : Type'} (f : nat -> B) (s : nat -> Prop) : (term834 B f s) = (term849 B f s).
Proof. exact (EQ_MP (@lem4000929 B f s) (@lem4000910 B f s)). Qed.
Lemma lem4000932 {A : Type'} (P : A -> Prop) (Q : Prop) : (term211 A P Q) = (term212 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4000933 (P : nat -> Prop) (Q : Prop) : (term799 P Q) = (term800 P Q).
Proof. exact (@lem4000932 nat P Q). Qed.
Lemma lem4000934 {B : Type'} (x : nat) (f : nat -> B) (s : nat -> Prop) : (term850 B x f s) = (term851 B x f s).
Proof. exact (@lem4000933 (term829 B f x s) ((term77 B f s) = (@CARD nat s))). Qed.
Lemma lem4000935 {B : Type'} (f : nat -> B) (x : nat) (y : nat) (s : nat -> Prop) : (term852 B f x s y) = (term827 B f x y s).
Proof. exact (eq_refl (term852 B f x s y)). Qed.
Lemma lem4000936 {B : Type'} (f : nat -> B) (x : nat) (s : nat -> Prop) : (term853 B f x s) = (term829 B f x s).
Proof. exact (fun_ext (fun y : nat => @lem4000935 B f x y s)). Qed.
Lemma lem4000937 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4000938 {B : Type'} (f : nat -> B) (x : nat) (s : nat -> Prop) : (term854 B f x s) = (term830 B f x s).
Proof. exact (MK_COMB (@lem4000937) (@lem4000936 B f x s)). Qed.
Lemma lem4000939 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4000940 {B : Type'} (f : nat -> B) (x : nat) (s : nat -> Prop) : (term855 B f x s) = (term844 B f x s).
Proof. exact (MK_COMB (@lem4000939) (@lem4000938 B f x s)). Qed.
Lemma lem4000941 {B : Type'} (f : nat -> B) (s : nat -> Prop) : ((term77 B f s) = (@CARD nat s)) = ((term77 B f s) = (@CARD nat s)).
Proof. exact (eq_refl ((term77 B f s) = (@CARD nat s))). Qed.
Lemma lem4000942 {B : Type'} (x : nat) (f : nat -> B) (s : nat -> Prop) : (term850 B x f s) = (term846 B x f s).
Proof. exact (MK_COMB (@lem4000940 B f x s) (@lem4000941 B f s)). Qed.
Lemma lem4000943 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4000944 {B : Type'} (x : nat) (f : nat -> B) (s : nat -> Prop) : (term856 B x f s) = (term857 B x f s).
Proof. exact (MK_COMB (@lem4000943) (@lem4000942 B x f s)). Qed.
Lemma lem4000945 {B : Type'} (f : nat -> B) (x : nat) (y : nat) (s : nat -> Prop) : (term852 B f x s y) = (term827 B f x y s).
Proof. exact (eq_refl (term852 B f x s y)). Qed.
Lemma lem4000946 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4000947 {B : Type'} (f : nat -> B) (x : nat) (y : nat) (s : nat -> Prop) : (term858 B f x s y) = (term859 B f x y s).
Proof. exact (MK_COMB (@lem4000946) (@lem4000945 B f x y s)). Qed.
Lemma lem4000948 {B : Type'} (f : nat -> B) (s : nat -> Prop) : ((term77 B f s) = (@CARD nat s)) = ((term77 B f s) = (@CARD nat s)).
Proof. exact (eq_refl ((term77 B f s) = (@CARD nat s))). Qed.
Lemma lem4000949 {B : Type'} (x : nat) (y : nat) (f : nat -> B) (s : nat -> Prop) : (term860 B x y f s) = (term861 B x y f s).
Proof. exact (MK_COMB (@lem4000947 B f x y s) (@lem4000948 B f s)). Qed.
Lemma lem4000950 {B : Type'} (x : nat) (f : nat -> B) (s : nat -> Prop) : (term862 B x f s) = (term863 B x f s).
Proof. exact (fun_ext (fun y : nat => @lem4000949 B x y f s)). Qed.
Lemma lem4000951 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4000952 {B : Type'} (x : nat) (f : nat -> B) (s : nat -> Prop) : (term851 B x f s) = (term864 B x f s).
Proof. exact (MK_COMB (@lem4000951) (@lem4000950 B x f s)). Qed.
Lemma lem4000953 {B : Type'} (x : nat) (f : nat -> B) (s : nat -> Prop) : ((term850 B x f s) = (term851 B x f s)) = ((term846 B x f s) = (term864 B x f s)).
Proof. exact (MK_COMB (@lem4000944 B x f s) (@lem4000952 B x f s)). Qed.
Lemma lem4000954 {B : Type'} (x : nat) (f : nat -> B) (s : nat -> Prop) : (term846 B x f s) = (term864 B x f s).
Proof. exact (EQ_MP (@lem4000953 B x f s) (@lem4000934 B x f s)). Qed.
Lemma lem4000955 {B : Type'} (f : nat -> B) (s : nat -> Prop) : (term848 B f s) = (term865 B f s).
Proof. exact (fun_ext (fun x : nat => @lem4000954 B x f s)). Qed.
Lemma lem4000956 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4000957 {B : Type'} (f : nat -> B) (s : nat -> Prop) : (term849 B f s) = (term866 B f s).
Proof. exact (MK_COMB (@lem4000956) (@lem4000955 B f s)). Qed.
Lemma lem4000958 {B : Type'} (f : nat -> B) (s : nat -> Prop) : (term834 B f s) = (term866 B f s).
Proof. exact (TRANS (@lem4000930 B f s) (@lem4000957 B f s)). Qed.
Lemma lem4000959 {B : Type'} (f : nat -> B) (s : nat -> Prop) : (term794 B f s) = (term866 B f s).
Proof. exact (TRANS (@lem4000906 B f s) (@lem4000958 B f s)). Qed.
Lemma lem4000960 {B : Type'} (f : nat -> B) : (term795 B f) = (term867 B f).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem4000959 B f s)). Qed.
Lemma lem4000961 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem4000962 {B : Type'} (f : nat -> B) : (term796 B f) = (term868 B f).
Proof. exact (MK_COMB (@lem4000961) (@lem4000960 B f)). Qed.
Lemma lem4000964 {A B : Type'} (P : type1413 A B) : (term281 A B P) = (term282 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4000965 (P : type991) : (term869 P) = (term870 P).
Proof. exact (@lem4000964 (nat -> Prop) nat P). Qed.
Lemma lem4000966 {B : Type'} (f : nat -> B) : (term871 B f) = (term872 B f).
Proof. exact (@lem4000965 (term873 B f)). Qed.
Lemma lem4000967 {B : Type'} (f : nat -> B) (s : nat -> Prop) : (term874 B f s) = (term865 B f s).
Proof. exact (eq_refl (term874 B f s)). Qed.
Lemma lem4000968 (x : nat) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4000969 {B : Type'} (f : nat -> B) (s : nat -> Prop) (x : nat) : (term875 B f s x) = (term876 B f s x).
Proof. exact (MK_COMB (@lem4000967 B f s) (@lem4000968 x)). Qed.
Lemma lem4000970 {B : Type'} (x : nat) (f : nat -> B) (s : nat -> Prop) : (term876 B f s x) = (term864 B x f s).
Proof. exact (eq_refl (term876 B f s x)). Qed.
Lemma lem4000971 {B : Type'} (x : nat) (f : nat -> B) (s : nat -> Prop) : (term875 B f s x) = (term864 B x f s).
Proof. exact (TRANS (@lem4000969 B f s x) (@lem4000970 B x f s)). Qed.
Lemma lem4000972 {B : Type'} (f : nat -> B) (s : nat -> Prop) : (term877 B f s) = (term865 B f s).
Proof. exact (fun_ext (fun x : nat => @lem4000971 B x f s)). Qed.
Lemma lem4000973 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4000974 {B : Type'} (f : nat -> B) (s : nat -> Prop) : (term878 B f s) = (term866 B f s).
Proof. exact (MK_COMB (@lem4000973) (@lem4000972 B f s)). Qed.
Lemma lem4000975 {B : Type'} (f : nat -> B) : (term879 B f) = (term867 B f).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem4000974 B f s)). Qed.
Lemma lem4000976 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem4000977 {B : Type'} (f : nat -> B) : (term871 B f) = (term868 B f).
Proof. exact (MK_COMB (@lem4000976) (@lem4000975 B f)). Qed.
Lemma lem4000978 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4000979 {B : Type'} (f : nat -> B) : (term880 B f) = (term881 B f).
Proof. exact (MK_COMB (@lem4000978) (@lem4000977 B f)). Qed.
Lemma lem4000980 {B : Type'} (f : nat -> B) (s : nat -> Prop) : (term874 B f s) = (term865 B f s).
Proof. exact (eq_refl (term874 B f s)). Qed.
Lemma lem4000981 (x : type994) (s : nat -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem4000982 {B : Type'} (f : nat -> B) (x : type994) (s : nat -> Prop) : (term882 B f x s) = (term883 B f x s).
Proof. exact (MK_COMB (@lem4000980 B f s) (@lem4000981 x s)). Qed.
Lemma lem4000983 {B : Type'} (x : type994) (f : nat -> B) (s : nat -> Prop) : (term883 B f x s) = (term884 B x f s).
Proof. exact (eq_refl (term883 B f x s)). Qed.
Lemma lem4000984 {B : Type'} (x : type994) (f : nat -> B) (s : nat -> Prop) : (term882 B f x s) = (term884 B x f s).
Proof. exact (TRANS (@lem4000982 B f x s) (@lem4000983 B x f s)). Qed.
Lemma lem4000985 {B : Type'} (x : type994) (f : nat -> B) : (term885 B f x) = (term886 B x f).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem4000984 B x f s)). Qed.
Lemma lem4000986 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem4000987 {B : Type'} (x : type994) (f : nat -> B) : (term887 B f x) = (term888 B x f).
Proof. exact (MK_COMB (@lem4000986) (@lem4000985 B x f)). Qed.
Lemma lem4000988 {B : Type'} (f : nat -> B) : (term889 B f) = (term890 B f).
Proof. exact (fun_ext (fun x : type994 => @lem4000987 B x f)). Qed.
Lemma lem4000989 : (@ex ((nat -> Prop) -> nat)) = (@ex ((nat -> Prop) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> Prop) -> nat))). Qed.
Lemma lem4000990 {B : Type'} (f : nat -> B) : (term872 B f) = (term891 B f).
Proof. exact (MK_COMB (@lem4000989) (@lem4000988 B f)). Qed.
Lemma lem4000991 {B : Type'} (f : nat -> B) : ((term871 B f) = (term872 B f)) = ((term868 B f) = (term891 B f)).
Proof. exact (MK_COMB (@lem4000979 B f) (@lem4000990 B f)). Qed.
Lemma lem4000992 {B : Type'} (f : nat -> B) : (term868 B f) = (term891 B f).
Proof. exact (EQ_MP (@lem4000991 B f) (@lem4000966 B f)). Qed.
Lemma lem4000994 {A B : Type'} (P : type1413 A B) : (term281 A B P) = (term282 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4000995 (P : type991) : (term869 P) = (term870 P).
Proof. exact (@lem4000994 (nat -> Prop) nat P). Qed.
Lemma lem4000996 {B : Type'} (x : type994) (f : nat -> B) : (term892 B x f) = (term893 B x f).
Proof. exact (@lem4000995 (term894 B x f)). Qed.
Lemma lem4000997 {B : Type'} (x : type994) (f : nat -> B) (s : nat -> Prop) : (term895 B x f s) = (term896 B x f s).
Proof. exact (eq_refl (term895 B x f s)). Qed.
Lemma lem4000998 (y : nat) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem4000999 {B : Type'} (x : type994) (f : nat -> B) (s : nat -> Prop) (y : nat) : (term897 B x f s y) = (term898 B x f s y).
Proof. exact (MK_COMB (@lem4000997 B x f s) (@lem4000998 y)). Qed.
Lemma lem4001000 {B : Type'} (x : type994) (y : nat) (f : nat -> B) (s : nat -> Prop) : (term898 B x f s y) = (term899 B x y f s).
Proof. exact (eq_refl (term898 B x f s y)). Qed.
Lemma lem4001001 {B : Type'} (x : type994) (y : nat) (f : nat -> B) (s : nat -> Prop) : (term897 B x f s y) = (term899 B x y f s).
Proof. exact (TRANS (@lem4000999 B x f s y) (@lem4001000 B x y f s)). Qed.
Lemma lem4001002 {B : Type'} (x : type994) (f : nat -> B) (s : nat -> Prop) : (term900 B x f s) = (term896 B x f s).
Proof. exact (fun_ext (fun y : nat => @lem4001001 B x y f s)). Qed.
Lemma lem4001003 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4001004 {B : Type'} (x : type994) (f : nat -> B) (s : nat -> Prop) : (term901 B x f s) = (term884 B x f s).
Proof. exact (MK_COMB (@lem4001003) (@lem4001002 B x f s)). Qed.
Lemma lem4001005 {B : Type'} (x : type994) (f : nat -> B) : (term902 B x f) = (term886 B x f).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem4001004 B x f s)). Qed.
Lemma lem4001006 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem4001007 {B : Type'} (x : type994) (f : nat -> B) : (term892 B x f) = (term888 B x f).
Proof. exact (MK_COMB (@lem4001006) (@lem4001005 B x f)). Qed.
Lemma lem4001008 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4001009 {B : Type'} (x : type994) (f : nat -> B) : (term903 B x f) = (term904 B x f).
Proof. exact (MK_COMB (@lem4001008) (@lem4001007 B x f)). Qed.
Lemma lem4001010 {B : Type'} (x : type994) (f : nat -> B) (s : nat -> Prop) : (term895 B x f s) = (term896 B x f s).
Proof. exact (eq_refl (term895 B x f s)). Qed.
Lemma lem4001011 (y : type994) (s : nat -> Prop) : (y s) = (y s).
Proof. exact (eq_refl (y s)). Qed.
Lemma lem4001012 {B : Type'} (x : type994) (f : nat -> B) (y : type994) (s : nat -> Prop) : (term905 B x f y s) = (term906 B x f y s).
Proof. exact (MK_COMB (@lem4001010 B x f s) (@lem4001011 y s)). Qed.
Lemma lem4001013 {B : Type'} (x : type994) (y : type994) (f : nat -> B) (s : nat -> Prop) : (term906 B x f y s) = (term907 B x y f s).
Proof. exact (eq_refl (term906 B x f y s)). Qed.
Lemma lem4001014 {B : Type'} (x : type994) (y : type994) (f : nat -> B) (s : nat -> Prop) : (term905 B x f y s) = (term907 B x y f s).
Proof. exact (TRANS (@lem4001012 B x f y s) (@lem4001013 B x y f s)). Qed.
Lemma lem4001015 {B : Type'} (x : type994) (y : type994) (f : nat -> B) : (term908 B x f y) = (term909 B x y f).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem4001014 B x y f s)). Qed.
Lemma lem4001016 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem4001017 {B : Type'} (x : type994) (y : type994) (f : nat -> B) : (term910 B x f y) = (term911 B x y f).
Proof. exact (MK_COMB (@lem4001016) (@lem4001015 B x y f)). Qed.
Lemma lem4001018 {B : Type'} (x : type994) (f : nat -> B) : (term912 B x f) = (term913 B x f).
Proof. exact (fun_ext (fun y : type994 => @lem4001017 B x y f)). Qed.
Lemma lem4001019 : (@ex ((nat -> Prop) -> nat)) = (@ex ((nat -> Prop) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> Prop) -> nat))). Qed.
Lemma lem4001020 {B : Type'} (x : type994) (f : nat -> B) : (term893 B x f) = (term914 B x f).
Proof. exact (MK_COMB (@lem4001019) (@lem4001018 B x f)). Qed.
Lemma lem4001021 {B : Type'} (x : type994) (f : nat -> B) : ((term892 B x f) = (term893 B x f)) = ((term888 B x f) = (term914 B x f)).
Proof. exact (MK_COMB (@lem4001009 B x f) (@lem4001020 B x f)). Qed.
Lemma lem4001022 {B : Type'} (x : type994) (f : nat -> B) : (term888 B x f) = (term914 B x f).
Proof. exact (EQ_MP (@lem4001021 B x f) (@lem4000996 B x f)). Qed.
Lemma lem4001023 {B : Type'} (f : nat -> B) : (term890 B f) = (term915 B f).
Proof. exact (fun_ext (fun x : type994 => @lem4001022 B x f)). Qed.
Lemma lem4001024 : (@ex ((nat -> Prop) -> nat)) = (@ex ((nat -> Prop) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> Prop) -> nat))). Qed.
Lemma lem4001025 {B : Type'} (f : nat -> B) : (term891 B f) = (term916 B f).
Proof. exact (MK_COMB (@lem4001024) (@lem4001023 B f)). Qed.
Lemma lem4001026 {B : Type'} (f : nat -> B) : (term868 B f) = (term916 B f).
Proof. exact (TRANS (@lem4000992 B f) (@lem4001025 B f)). Qed.
Lemma lem4001027 {B : Type'} (f : nat -> B) : (term796 B f) = (term916 B f).
Proof. exact (TRANS (@lem4000962 B f) (@lem4001026 B f)). Qed.
Lemma lem4001028 {B : Type'} : (term797 B) = (term917 B).
Proof. exact (fun_ext (fun f : nat -> B => @lem4001027 B f)). Qed.
Lemma lem4001029 {B : Type'} : (@all (nat -> B)) = (@all (nat -> B)).
Proof. exact (eq_refl (@all (nat -> B))). Qed.
Lemma lem4001030 {B : Type'} : (term798 B) = (term918 B).
Proof. exact (MK_COMB (@lem4001029 B) (@lem4001028 B)). Qed.
Lemma lem4001032 {A B : Type'} (P : type1413 A B) : (term281 A B P) = (term282 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4001033 {B : Type'} (P : type965 B) : (term919 B P) = (term920 B P).
Proof. exact (@lem4001032 (nat -> B) type994 P). Qed.
Lemma lem4001034 {B : Type'} : (term921 B) = (term922 B).
Proof. exact (@lem4001033 B (term923 B)). Qed.
Lemma lem4001035 {B : Type'} (f : nat -> B) : (term924 B f) = (term915 B f).
Proof. exact (eq_refl (term924 B f)). Qed.
Lemma lem4001036 (x : type994) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4001037 {B : Type'} (f : nat -> B) (x : type994) : (term925 B f x) = (term926 B f x).
Proof. exact (MK_COMB (@lem4001035 B f) (@lem4001036 x)). Qed.
Lemma lem4001038 {B : Type'} (x : type994) (f : nat -> B) : (term926 B f x) = (term914 B x f).
Proof. exact (eq_refl (term926 B f x)). Qed.
Lemma lem4001039 {B : Type'} (x : type994) (f : nat -> B) : (term925 B f x) = (term914 B x f).
Proof. exact (TRANS (@lem4001037 B f x) (@lem4001038 B x f)). Qed.
Lemma lem4001040 {B : Type'} (f : nat -> B) : (term927 B f) = (term915 B f).
Proof. exact (fun_ext (fun x : type994 => @lem4001039 B x f)). Qed.
Lemma lem4001041 : (@ex ((nat -> Prop) -> nat)) = (@ex ((nat -> Prop) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> Prop) -> nat))). Qed.
Lemma lem4001042 {B : Type'} (f : nat -> B) : (term928 B f) = (term916 B f).
Proof. exact (MK_COMB (@lem4001041) (@lem4001040 B f)). Qed.
Lemma lem4001043 {B : Type'} : (term929 B) = (term917 B).
Proof. exact (fun_ext (fun f : nat -> B => @lem4001042 B f)). Qed.
Lemma lem4001044 {B : Type'} : (@all (nat -> B)) = (@all (nat -> B)).
Proof. exact (eq_refl (@all (nat -> B))). Qed.
Lemma lem4001045 {B : Type'} : (term921 B) = (term918 B).
Proof. exact (MK_COMB (@lem4001044 B) (@lem4001043 B)). Qed.
Lemma lem4001046 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4001047 {B : Type'} : (term930 B) = (term931 B).
Proof. exact (MK_COMB (@lem4001046) (@lem4001045 B)). Qed.
Lemma lem4001048 {B : Type'} (f : nat -> B) : (term924 B f) = (term915 B f).
Proof. exact (eq_refl (term924 B f)). Qed.
Lemma lem4001049 {B : Type'} (x : type969 B) (f : nat -> B) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem4001050 {B : Type'} (x : type969 B) (f : nat -> B) : (term932 B x f) = (term933 B x f).
Proof. exact (MK_COMB (@lem4001048 B f) (@lem4001049 B x f)). Qed.
Lemma lem4001051 {B : Type'} (x : type969 B) (f : nat -> B) : (term933 B x f) = (term934 B x f).
Proof. exact (eq_refl (term933 B x f)). Qed.
Lemma lem4001052 {B : Type'} (x : type969 B) (f : nat -> B) : (term932 B x f) = (term934 B x f).
Proof. exact (TRANS (@lem4001050 B x f) (@lem4001051 B x f)). Qed.
Lemma lem4001053 {B : Type'} (x : type969 B) : (term935 B x) = (term936 B x).
Proof. exact (fun_ext (fun f : nat -> B => @lem4001052 B x f)). Qed.
Lemma lem4001054 {B : Type'} : (@all (nat -> B)) = (@all (nat -> B)).
Proof. exact (eq_refl (@all (nat -> B))). Qed.
Lemma lem4001055 {B : Type'} (x : type969 B) : (term937 B x) = (term938 B x).
Proof. exact (MK_COMB (@lem4001054 B) (@lem4001053 B x)). Qed.
Lemma lem4001056 {B : Type'} : (term939 B) = (term940 B).
Proof. exact (fun_ext (fun x : type969 B => @lem4001055 B x)). Qed.
Lemma lem4001057 {B : Type'} : (@ex ((nat -> B) -> (nat -> Prop) -> nat)) = (@ex ((nat -> B) -> (nat -> Prop) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> B) -> (nat -> Prop) -> nat))). Qed.
Lemma lem4001058 {B : Type'} : (term922 B) = (term941 B).
Proof. exact (MK_COMB (@lem4001057 B) (@lem4001056 B)). Qed.
Lemma lem4001059 {B : Type'} : ((term921 B) = (term922 B)) = ((term918 B) = (term941 B)).
Proof. exact (MK_COMB (@lem4001047 B) (@lem4001058 B)). Qed.
Lemma lem4001060 {B : Type'} : (term918 B) = (term941 B).
Proof. exact (EQ_MP (@lem4001059 B) (@lem4001034 B)). Qed.
Lemma lem4001062 {A B : Type'} (P : type1413 A B) : (term281 A B P) = (term282 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4001063 {B : Type'} (P : type965 B) : (term919 B P) = (term920 B P).
Proof. exact (@lem4001062 (nat -> B) type994 P). Qed.
Lemma lem4001064 {B : Type'} (x : type969 B) : (term942 B x) = (term943 B x).
Proof. exact (@lem4001063 B (term944 B x)). Qed.
Lemma lem4001065 {B : Type'} (x : type969 B) (f : nat -> B) : (term945 B x f) = (term946 B x f).
Proof. exact (eq_refl (term945 B x f)). Qed.
Lemma lem4001066 (y : type994) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem4001067 {B : Type'} (x : type969 B) (f : nat -> B) (y : type994) : (term947 B x f y) = (term948 B x f y).
Proof. exact (MK_COMB (@lem4001065 B x f) (@lem4001066 y)). Qed.
Lemma lem4001068 {B : Type'} (x : type969 B) (y : type994) (f : nat -> B) : (term948 B x f y) = (term949 B x y f).
Proof. exact (eq_refl (term948 B x f y)). Qed.
Lemma lem4001069 {B : Type'} (x : type969 B) (y : type994) (f : nat -> B) : (term947 B x f y) = (term949 B x y f).
Proof. exact (TRANS (@lem4001067 B x f y) (@lem4001068 B x y f)). Qed.
Lemma lem4001070 {B : Type'} (x : type969 B) (f : nat -> B) : (term950 B x f) = (term946 B x f).
Proof. exact (fun_ext (fun y : type994 => @lem4001069 B x y f)). Qed.
Lemma lem4001071 : (@ex ((nat -> Prop) -> nat)) = (@ex ((nat -> Prop) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> Prop) -> nat))). Qed.
Lemma lem4001072 {B : Type'} (x : type969 B) (f : nat -> B) : (term951 B x f) = (term934 B x f).
Proof. exact (MK_COMB (@lem4001071) (@lem4001070 B x f)). Qed.
Lemma lem4001073 {B : Type'} (x : type969 B) : (term952 B x) = (term936 B x).
Proof. exact (fun_ext (fun f : nat -> B => @lem4001072 B x f)). Qed.
Lemma lem4001074 {B : Type'} : (@all (nat -> B)) = (@all (nat -> B)).
Proof. exact (eq_refl (@all (nat -> B))). Qed.
Lemma lem4001075 {B : Type'} (x : type969 B) : (term942 B x) = (term938 B x).
Proof. exact (MK_COMB (@lem4001074 B) (@lem4001073 B x)). Qed.
Lemma lem4001076 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4001077 {B : Type'} (x : type969 B) : (term953 B x) = (term954 B x).
Proof. exact (MK_COMB (@lem4001076) (@lem4001075 B x)). Qed.
Lemma lem4001078 {B : Type'} (x : type969 B) (f : nat -> B) : (term945 B x f) = (term946 B x f).
Proof. exact (eq_refl (term945 B x f)). Qed.
Lemma lem4001079 {B : Type'} (y : type969 B) (f : nat -> B) : (y f) = (y f).
Proof. exact (eq_refl (y f)). Qed.
Lemma lem4001080 {B : Type'} (x : type969 B) (y : type969 B) (f : nat -> B) : (term955 B x y f) = (term956 B x y f).
Proof. exact (MK_COMB (@lem4001078 B x f) (@lem4001079 B y f)). Qed.
Lemma lem4001081 {B : Type'} (x : type969 B) (y : type969 B) (f : nat -> B) : (term956 B x y f) = (term957 B x y f).
Proof. exact (eq_refl (term956 B x y f)). Qed.
Lemma lem4001082 {B : Type'} (x : type969 B) (y : type969 B) (f : nat -> B) : (term955 B x y f) = (term957 B x y f).
Proof. exact (TRANS (@lem4001080 B x y f) (@lem4001081 B x y f)). Qed.
Lemma lem4001083 {B : Type'} (x : type969 B) (y : type969 B) : (term958 B x y) = (term959 B x y).
Proof. exact (fun_ext (fun f : nat -> B => @lem4001082 B x y f)). Qed.
Lemma lem4001084 {B : Type'} : (@all (nat -> B)) = (@all (nat -> B)).
Proof. exact (eq_refl (@all (nat -> B))). Qed.
Lemma lem4001085 {B : Type'} (x : type969 B) (y : type969 B) : (term960 B x y) = (term961 B x y).
Proof. exact (MK_COMB (@lem4001084 B) (@lem4001083 B x y)). Qed.
Lemma lem4001086 {B : Type'} (x : type969 B) : (term962 B x) = (term963 B x).
Proof. exact (fun_ext (fun y : type969 B => @lem4001085 B x y)). Qed.
Lemma lem4001087 {B : Type'} : (@ex ((nat -> B) -> (nat -> Prop) -> nat)) = (@ex ((nat -> B) -> (nat -> Prop) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> B) -> (nat -> Prop) -> nat))). Qed.
Lemma lem4001088 {B : Type'} (x : type969 B) : (term943 B x) = (term964 B x).
Proof. exact (MK_COMB (@lem4001087 B) (@lem4001086 B x)). Qed.
Lemma lem4001089 {B : Type'} (x : type969 B) : ((term942 B x) = (term943 B x)) = ((term938 B x) = (term964 B x)).
Proof. exact (MK_COMB (@lem4001077 B x) (@lem4001088 B x)). Qed.
Lemma lem4001090 {B : Type'} (x : type969 B) : (term938 B x) = (term964 B x).
Proof. exact (EQ_MP (@lem4001089 B x) (@lem4001064 B x)). Qed.
Lemma lem4001091 {B : Type'} : (term940 B) = (term965 B).
Proof. exact (fun_ext (fun x : type969 B => @lem4001090 B x)). Qed.
Lemma lem4001092 {B : Type'} : (@ex ((nat -> B) -> (nat -> Prop) -> nat)) = (@ex ((nat -> B) -> (nat -> Prop) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> B) -> (nat -> Prop) -> nat))). Qed.
Lemma lem4001093 {B : Type'} : (term941 B) = (term966 B).
Proof. exact (MK_COMB (@lem4001092 B) (@lem4001091 B)). Qed.
Lemma lem4001094 {B : Type'} : (term918 B) = (term966 B).
Proof. exact (TRANS (@lem4001060 B) (@lem4001093 B)). Qed.
Lemma lem4001096 {B : Type'} : (term798 B) = (term966 B).
Proof. exact (TRANS (@lem4001030 B) (@lem4001094 B)). Qed.
Lemma lem4001097 {B : Type'} : (term57 B) = (term966 B).
Proof. exact (TRANS (@lem4000745 B) (@lem4001096 B)). Qed.
Lemma lem4001098 {B : Type'} (h1 : term57 B) : term966 B.
Proof. exact (EQ_MP (@lem4001097 B) (@lem3998886 B h1)). Qed.
Lemma lem4001099 {B : Type'} (x : type969 B) (h1 : term964 B x) : term964 B x.
Proof. exact (h1). Qed.
Lemma lem4001101 {B : Type'} (x' : type485 B) (h1 : term378 B x') : term378 B x'.
Proof. exact (h1). Qed.
Lemma lem4001103 {A : Type'} (x'' : type694 A) (h1 : term765 A x'') : term765 A x''.
Proof. exact (h1). Qed.
Lemma lem4001105 {A B : Type'} (x''' : type529 A B) (h1 : term571 A B x''') : term571 A B x'''.
Proof. exact (h1). Qed.
Lemma lem4001106 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (h1 : term568 A B x''' y''') : term568 A B x''' y'''.
Proof. exact (h1). Qed.
Lemma lem4001107 {A : Type'} (x'''' : type485 A) (h1 : term378 A x'''') : term378 A x''''.
Proof. exact (h1). Qed.
Lemma lem4001109 {A B : Type'} (f : A -> B) (h1 : term169 A B f) : term169 A B f.
Proof. exact (h1). Qed.
Lemma lem4001110 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term160 A B f s) : term160 A B f s.
Proof. exact (h1). Qed.
Lemma lem4001111 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term150 A B f s n) : term150 A B f s n.
Proof. exact (h1). Qed.
Lemma lem4001781 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem4001782 {B : Type'} : (@CARD B) = (@CARD B).
Proof. exact (eq_refl (@CARD B)). Qed.
Lemma lem4001789 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4001790 {A B : Type'} (f : type528 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> Prop) -> B -> Prop) f x).
Proof. exact (@lem4001789 (A -> B) (type678 A B) f x). Qed.
Lemma lem4001791 {A B : Type'} (f : A -> B) : (@IMAGE A B f) = (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f).
Proof. exact (@lem4001790 A B (@IMAGE A B) f). Qed.
Lemma lem4001792 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4001793 {A B : Type'} (f : A -> B) (s : A -> Prop) : (@IMAGE A B f s) = (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f s).
Proof. exact (MK_COMB (@lem4001791 A B f) (@lem4001792 A s)). Qed.
Lemma lem4001795 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4001796 {A B : Type'} (f : type678 A B) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> B -> Prop) f x).
Proof. exact (@lem4001795 (A -> Prop) (B -> Prop) f x). Qed.
Lemma lem4001797 {A B : Type'} (f : A -> B) (s : A -> Prop) : (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f s) = (term967 A B f s).
Proof. exact (@lem4001796 A B (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f) s). Qed.
Lemma lem4001799 {A B : Type'} (f : A -> B) (s : A -> Prop) : (@IMAGE A B f s) = (term967 A B f s).
Proof. exact (TRANS (@lem4001793 A B f s) (@lem4001797 A B f s)). Qed.
Lemma lem4001800 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term33 A B f s) = (term968 A B f s).
Proof. exact (MK_COMB (@lem4001782 B) (@lem4001799 A B f s)). Qed.
Lemma lem4001802 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4001803 {B : Type'} (f : type687 B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> nat) f x).
Proof. exact (@lem4001802 (B -> Prop) nat f x). Qed.
Lemma lem4001804 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term968 A B f s) = (term969 A B f s).
Proof. exact (@lem4001803 B (@CARD B) (term967 A B f s)). Qed.
Lemma lem4001805 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term33 A B f s) = (term969 A B f s).
Proof. exact (TRANS (@lem4001800 A B f s) (@lem4001804 A B f s)). Qed.
Lemma lem4001810 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4001811 {A : Type'} (f : type687 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> nat) f x).
Proof. exact (@lem4001810 (A -> Prop) nat f x). Qed.
Lemma lem4001813 {A : Type'} (s : A -> Prop) : (@CARD A s) = (@I ((A -> Prop) -> nat) (@CARD A) s).
Proof. exact (@lem4001811 A (@CARD A) s). Qed.
Lemma lem4001814 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term970 A B f s) = (term971 A B f s).
Proof. exact (MK_COMB (@lem4001781) (@lem4001805 A B f s)). Qed.
Lemma lem4001815 {A B : Type'} (f : A -> B) (s : A -> Prop) : ((term33 A B f s) = (@CARD A s)) = ((term969 A B f s) = (@I ((A -> Prop) -> nat) (@CARD A) s)).
Proof. exact (MK_COMB (@lem4001814 A B f s) (@lem4001813 A s)). Qed.
Lemma lem4001816 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4001821 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4001822 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4001821 (A -> Prop) Prop f x). Qed.
Lemma lem4001824 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@I ((A -> Prop) -> Prop) (@FINITE A) s).
Proof. exact (@lem4001822 A (@FINITE A) s). Qed.
Lemma lem4001825 {A : Type'} (s : A -> Prop) : (term197 A s) = (term972 A s).
Proof. exact (MK_COMB (@lem4001816) (@lem4001824 A s)). Qed.
Lemma lem4001826 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4001827 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem4001834 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4001835 {A B : Type'} (f : type529 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> Prop) -> A) f x).
Proof. exact (@lem4001834 (A -> B) (type684 A) f x). Qed.
Lemma lem4001836 {A B : Type'} (x''' : type529 A B) (f : A -> B) : (x''' f) = (@I ((A -> B) -> (A -> Prop) -> A) x''' f).
Proof. exact (@lem4001835 A B x''' f). Qed.
Lemma lem4001837 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4001838 {A B : Type'} (x''' : type529 A B) (f : A -> B) (s : A -> Prop) : (x''' f s) = (@I ((A -> B) -> (A -> Prop) -> A) x''' f s).
Proof. exact (MK_COMB (@lem4001836 A B x''' f) (@lem4001837 A s)). Qed.
Lemma lem4001840 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4001841 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem4001840 (A -> Prop) A f x). Qed.
Lemma lem4001842 {A B : Type'} (x''' : type529 A B) (f : A -> B) (s : A -> Prop) : (@I ((A -> B) -> (A -> Prop) -> A) x''' f s) = (term973 A B x''' f s).
Proof. exact (@lem4001841 A (@I ((A -> B) -> (A -> Prop) -> A) x''' f) s). Qed.
Lemma lem4001844 {A B : Type'} (x''' : type529 A B) (f : A -> B) (s : A -> Prop) : (x''' f s) = (term973 A B x''' f s).
Proof. exact (TRANS (@lem4001838 A B x''' f s) (@lem4001842 A B x''' f s)). Qed.
Lemma lem4001851 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4001852 {A B : Type'} (f : type529 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> Prop) -> A) f x).
Proof. exact (@lem4001851 (A -> B) (type684 A) f x). Qed.
Lemma lem4001853 {A B : Type'} (y''' : type529 A B) (f : A -> B) : (y''' f) = (@I ((A -> B) -> (A -> Prop) -> A) y''' f).
Proof. exact (@lem4001852 A B y''' f). Qed.
Lemma lem4001854 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4001855 {A B : Type'} (y''' : type529 A B) (f : A -> B) (s : A -> Prop) : (y''' f s) = (@I ((A -> B) -> (A -> Prop) -> A) y''' f s).
Proof. exact (MK_COMB (@lem4001853 A B y''' f) (@lem4001854 A s)). Qed.
Lemma lem4001857 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4001858 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem4001857 (A -> Prop) A f x). Qed.
Lemma lem4001859 {A B : Type'} (y''' : type529 A B) (f : A -> B) (s : A -> Prop) : (@I ((A -> B) -> (A -> Prop) -> A) y''' f s) = (term973 A B y''' f s).
Proof. exact (@lem4001858 A (@I ((A -> B) -> (A -> Prop) -> A) y''' f) s). Qed.
Lemma lem4001861 {A B : Type'} (y''' : type529 A B) (f : A -> B) (s : A -> Prop) : (y''' f s) = (term973 A B y''' f s).
Proof. exact (TRANS (@lem4001855 A B y''' f s) (@lem4001859 A B y''' f s)). Qed.
Lemma lem4001862 {A B : Type'} (x''' : type529 A B) (f : A -> B) (s : A -> Prop) : (term974 A B x''' f s) = (term975 A B x''' f s).
Proof. exact (MK_COMB (@lem4001827 A) (@lem4001844 A B x''' f s)). Qed.
Lemma lem4001863 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (f : A -> B) (s : A -> Prop) : ((x''' f s) = (y''' f s)) = ((term973 A B x''' f s) = (term973 A B y''' f s)).
Proof. exact (MK_COMB (@lem4001862 A B x''' f s) (@lem4001861 A B y''' f s)). Qed.
Lemma lem4001864 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (f : A -> B) (s : A -> Prop) : (term976 A B x''' y''' f s) = (term977 A B x''' y''' f s).
Proof. exact (MK_COMB (@lem4001826) (@lem4001863 A B x''' y''' f s)). Qed.
Lemma lem4001865 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem4001866 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4001873 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4001874 {A B : Type'} (f : type529 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> Prop) -> A) f x).
Proof. exact (@lem4001873 (A -> B) (type684 A) f x). Qed.
Lemma lem4001875 {A B : Type'} (x''' : type529 A B) (f : A -> B) : (x''' f) = (@I ((A -> B) -> (A -> Prop) -> A) x''' f).
Proof. exact (@lem4001874 A B x''' f). Qed.
Lemma lem4001876 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4001877 {A B : Type'} (x''' : type529 A B) (f : A -> B) (s : A -> Prop) : (x''' f s) = (@I ((A -> B) -> (A -> Prop) -> A) x''' f s).
Proof. exact (MK_COMB (@lem4001875 A B x''' f) (@lem4001876 A s)). Qed.
Lemma lem4001879 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4001880 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem4001879 (A -> Prop) A f x). Qed.
Lemma lem4001881 {A B : Type'} (x''' : type529 A B) (f : A -> B) (s : A -> Prop) : (@I ((A -> B) -> (A -> Prop) -> A) x''' f s) = (term973 A B x''' f s).
Proof. exact (@lem4001880 A (@I ((A -> B) -> (A -> Prop) -> A) x''' f) s). Qed.
Lemma lem4001883 {A B : Type'} (x''' : type529 A B) (f : A -> B) (s : A -> Prop) : (x''' f s) = (term973 A B x''' f s).
Proof. exact (TRANS (@lem4001877 A B x''' f s) (@lem4001881 A B x''' f s)). Qed.
Lemma lem4001884 {A B : Type'} (x''' : type529 A B) (f : A -> B) (s : A -> Prop) : (term978 A B x''' f s) = (term979 A B x''' f s).
Proof. exact (MK_COMB (@lem4001866 A B f) (@lem4001883 A B x''' f s)). Qed.
Lemma lem4001886 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4001887 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem4001886 A B f x). Qed.
Lemma lem4001888 {A B : Type'} (x''' : type529 A B) (f : A -> B) (s : A -> Prop) : (term979 A B x''' f s) = (term980 A B x''' f s).
Proof. exact (@lem4001887 A B f (term973 A B x''' f s)). Qed.
Lemma lem4001889 {A B : Type'} (x''' : type529 A B) (f : A -> B) (s : A -> Prop) : (term978 A B x''' f s) = (term980 A B x''' f s).
Proof. exact (TRANS (@lem4001884 A B x''' f s) (@lem4001888 A B x''' f s)). Qed.
Lemma lem4001890 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4001897 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4001898 {A B : Type'} (f : type529 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> Prop) -> A) f x).
Proof. exact (@lem4001897 (A -> B) (type684 A) f x). Qed.
Lemma lem4001899 {A B : Type'} (y''' : type529 A B) (f : A -> B) : (y''' f) = (@I ((A -> B) -> (A -> Prop) -> A) y''' f).
Proof. exact (@lem4001898 A B y''' f). Qed.
Lemma lem4001900 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4001901 {A B : Type'} (y''' : type529 A B) (f : A -> B) (s : A -> Prop) : (y''' f s) = (@I ((A -> B) -> (A -> Prop) -> A) y''' f s).
Proof. exact (MK_COMB (@lem4001899 A B y''' f) (@lem4001900 A s)). Qed.
Lemma lem4001903 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4001904 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem4001903 (A -> Prop) A f x). Qed.
Lemma lem4001905 {A B : Type'} (y''' : type529 A B) (f : A -> B) (s : A -> Prop) : (@I ((A -> B) -> (A -> Prop) -> A) y''' f s) = (term973 A B y''' f s).
Proof. exact (@lem4001904 A (@I ((A -> B) -> (A -> Prop) -> A) y''' f) s). Qed.
Lemma lem4001907 {A B : Type'} (y''' : type529 A B) (f : A -> B) (s : A -> Prop) : (y''' f s) = (term973 A B y''' f s).
Proof. exact (TRANS (@lem4001901 A B y''' f s) (@lem4001905 A B y''' f s)). Qed.
Lemma lem4001908 {A B : Type'} (y''' : type529 A B) (f : A -> B) (s : A -> Prop) : (term978 A B y''' f s) = (term979 A B y''' f s).
Proof. exact (MK_COMB (@lem4001890 A B f) (@lem4001907 A B y''' f s)). Qed.
Lemma lem4001910 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4001911 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem4001910 A B f x). Qed.
Lemma lem4001912 {A B : Type'} (y''' : type529 A B) (f : A -> B) (s : A -> Prop) : (term979 A B y''' f s) = (term980 A B y''' f s).
Proof. exact (@lem4001911 A B f (term973 A B y''' f s)). Qed.
Lemma lem4001913 {A B : Type'} (y''' : type529 A B) (f : A -> B) (s : A -> Prop) : (term978 A B y''' f s) = (term980 A B y''' f s).
Proof. exact (TRANS (@lem4001908 A B y''' f s) (@lem4001912 A B y''' f s)). Qed.
Lemma lem4001914 {A B : Type'} (x''' : type529 A B) (f : A -> B) (s : A -> Prop) : (term981 A B x''' f s) = (term982 A B x''' f s).
Proof. exact (MK_COMB (@lem4001865 B) (@lem4001889 A B x''' f s)). Qed.
Lemma lem4001915 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (f : A -> B) (s : A -> Prop) : ((term978 A B x''' f s) = (term978 A B y''' f s)) = ((term980 A B x''' f s) = (term980 A B y''' f s)).
Proof. exact (MK_COMB (@lem4001914 A B x''' f s) (@lem4001913 A B y''' f s)). Qed.
Lemma lem4001916 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem4001923 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4001924 {A B : Type'} (f : type529 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> Prop) -> A) f x).
Proof. exact (@lem4001923 (A -> B) (type684 A) f x). Qed.
Lemma lem4001925 {A B : Type'} (y''' : type529 A B) (f : A -> B) : (y''' f) = (@I ((A -> B) -> (A -> Prop) -> A) y''' f).
Proof. exact (@lem4001924 A B y''' f). Qed.
Lemma lem4001926 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4001927 {A B : Type'} (y''' : type529 A B) (f : A -> B) (s : A -> Prop) : (y''' f s) = (@I ((A -> B) -> (A -> Prop) -> A) y''' f s).
Proof. exact (MK_COMB (@lem4001925 A B y''' f) (@lem4001926 A s)). Qed.
Lemma lem4001929 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4001930 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem4001929 (A -> Prop) A f x). Qed.
Lemma lem4001931 {A B : Type'} (y''' : type529 A B) (f : A -> B) (s : A -> Prop) : (@I ((A -> B) -> (A -> Prop) -> A) y''' f s) = (term973 A B y''' f s).
Proof. exact (@lem4001930 A (@I ((A -> B) -> (A -> Prop) -> A) y''' f) s). Qed.
Lemma lem4001933 {A B : Type'} (y''' : type529 A B) (f : A -> B) (s : A -> Prop) : (y''' f s) = (term973 A B y''' f s).
Proof. exact (TRANS (@lem4001927 A B y''' f s) (@lem4001931 A B y''' f s)). Qed.
Lemma lem4001934 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4001935 {A B : Type'} (y''' : type529 A B) (f : A -> B) (s : A -> Prop) : (term983 A B y''' f s) = (term984 A B y''' f s).
Proof. exact (MK_COMB (@lem4001916 A) (@lem4001933 A B y''' f s)). Qed.
Lemma lem4001936 {A B : Type'} (y''' : type529 A B) (f : A -> B) (s : A -> Prop) : (term985 A B y''' f s) = (term986 A B y''' f s).
Proof. exact (MK_COMB (@lem4001935 A B y''' f s) (@lem4001934 A s)). Qed.
Lemma lem4001938 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4001939 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4001938 A (type686 A) f x). Qed.
Lemma lem4001940 {A B : Type'} (y''' : type529 A B) (f : A -> B) (s : A -> Prop) : (term984 A B y''' f s) = (term987 A B y''' f s).
Proof. exact (@lem4001939 A (@IN A) (term973 A B y''' f s)). Qed.
Lemma lem4001941 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4001942 {A B : Type'} (y''' : type529 A B) (f : A -> B) (s : A -> Prop) : (term986 A B y''' f s) = (term988 A B y''' f s).
Proof. exact (MK_COMB (@lem4001940 A B y''' f s) (@lem4001941 A s)). Qed.
Lemma lem4001944 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4001945 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4001944 (A -> Prop) Prop f x). Qed.
Lemma lem4001946 {A B : Type'} (y''' : type529 A B) (f : A -> B) (s : A -> Prop) : (term988 A B y''' f s) = (term989 A B y''' f s).
Proof. exact (@lem4001945 A (term987 A B y''' f s) s). Qed.
Lemma lem4001947 {A B : Type'} (y''' : type529 A B) (f : A -> B) (s : A -> Prop) : (term986 A B y''' f s) = (term989 A B y''' f s).
Proof. exact (TRANS (@lem4001942 A B y''' f s) (@lem4001946 A B y''' f s)). Qed.
Lemma lem4001948 {A B : Type'} (y''' : type529 A B) (f : A -> B) (s : A -> Prop) : (term985 A B y''' f s) = (term989 A B y''' f s).
Proof. exact (TRANS (@lem4001936 A B y''' f s) (@lem4001947 A B y''' f s)). Qed.
Lemma lem4001949 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4001950 {A B : Type'} (y''' : type529 A B) (f : A -> B) (s : A -> Prop) : (term990 A B y''' f s) = (term991 A B y''' f s).
Proof. exact (MK_COMB (@lem4001949) (@lem4001948 A B y''' f s)). Qed.
Lemma lem4001951 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (f : A -> B) (s : A -> Prop) : (term992 A B x''' y''' f s) = (term993 A B x''' y''' f s).
Proof. exact (MK_COMB (@lem4001950 A B y''' f s) (@lem4001915 A B x''' y''' f s)). Qed.
Lemma lem4001952 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem4001959 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4001960 {A B : Type'} (f : type529 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> Prop) -> A) f x).
Proof. exact (@lem4001959 (A -> B) (type684 A) f x). Qed.
Lemma lem4001961 {A B : Type'} (x''' : type529 A B) (f : A -> B) : (x''' f) = (@I ((A -> B) -> (A -> Prop) -> A) x''' f).
Proof. exact (@lem4001960 A B x''' f). Qed.
Lemma lem4001962 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4001963 {A B : Type'} (x''' : type529 A B) (f : A -> B) (s : A -> Prop) : (x''' f s) = (@I ((A -> B) -> (A -> Prop) -> A) x''' f s).
Proof. exact (MK_COMB (@lem4001961 A B x''' f) (@lem4001962 A s)). Qed.
Lemma lem4001965 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4001966 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem4001965 (A -> Prop) A f x). Qed.
Lemma lem4001967 {A B : Type'} (x''' : type529 A B) (f : A -> B) (s : A -> Prop) : (@I ((A -> B) -> (A -> Prop) -> A) x''' f s) = (term973 A B x''' f s).
Proof. exact (@lem4001966 A (@I ((A -> B) -> (A -> Prop) -> A) x''' f) s). Qed.
Lemma lem4001969 {A B : Type'} (x''' : type529 A B) (f : A -> B) (s : A -> Prop) : (x''' f s) = (term973 A B x''' f s).
Proof. exact (TRANS (@lem4001963 A B x''' f s) (@lem4001967 A B x''' f s)). Qed.
Lemma lem4001970 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4001971 {A B : Type'} (x''' : type529 A B) (f : A -> B) (s : A -> Prop) : (term983 A B x''' f s) = (term984 A B x''' f s).
Proof. exact (MK_COMB (@lem4001952 A) (@lem4001969 A B x''' f s)). Qed.
Lemma lem4001972 {A B : Type'} (x''' : type529 A B) (f : A -> B) (s : A -> Prop) : (term985 A B x''' f s) = (term986 A B x''' f s).
Proof. exact (MK_COMB (@lem4001971 A B x''' f s) (@lem4001970 A s)). Qed.
Lemma lem4001974 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4001975 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4001974 A (type686 A) f x). Qed.
Lemma lem4001976 {A B : Type'} (x''' : type529 A B) (f : A -> B) (s : A -> Prop) : (term984 A B x''' f s) = (term987 A B x''' f s).
Proof. exact (@lem4001975 A (@IN A) (term973 A B x''' f s)). Qed.
Lemma lem4001977 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4001978 {A B : Type'} (x''' : type529 A B) (f : A -> B) (s : A -> Prop) : (term986 A B x''' f s) = (term988 A B x''' f s).
Proof. exact (MK_COMB (@lem4001976 A B x''' f s) (@lem4001977 A s)). Qed.
Lemma lem4001980 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4001981 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4001980 (A -> Prop) Prop f x). Qed.
Lemma lem4001982 {A B : Type'} (x''' : type529 A B) (f : A -> B) (s : A -> Prop) : (term988 A B x''' f s) = (term989 A B x''' f s).
Proof. exact (@lem4001981 A (term987 A B x''' f s) s). Qed.
Lemma lem4001983 {A B : Type'} (x''' : type529 A B) (f : A -> B) (s : A -> Prop) : (term986 A B x''' f s) = (term989 A B x''' f s).
Proof. exact (TRANS (@lem4001978 A B x''' f s) (@lem4001982 A B x''' f s)). Qed.
Lemma lem4001984 {A B : Type'} (x''' : type529 A B) (f : A -> B) (s : A -> Prop) : (term985 A B x''' f s) = (term989 A B x''' f s).
Proof. exact (TRANS (@lem4001972 A B x''' f s) (@lem4001983 A B x''' f s)). Qed.
Lemma lem4001985 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4001986 {A B : Type'} (x''' : type529 A B) (f : A -> B) (s : A -> Prop) : (term990 A B x''' f s) = (term991 A B x''' f s).
Proof. exact (MK_COMB (@lem4001985) (@lem4001984 A B x''' f s)). Qed.
Lemma lem4001987 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (f : A -> B) (s : A -> Prop) : (term994 A B x''' y''' f s) = (term995 A B x''' y''' f s).
Proof. exact (MK_COMB (@lem4001986 A B x''' f s) (@lem4001951 A B x''' y''' f s)). Qed.
Lemma lem4001988 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4001989 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (f : A -> B) (s : A -> Prop) : (term996 A B x''' y''' f s) = (term997 A B x''' y''' f s).
Proof. exact (MK_COMB (@lem4001988) (@lem4001987 A B x''' y''' f s)). Qed.
Lemma lem4001990 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (f : A -> B) (s : A -> Prop) : (term998 A B x''' y''' f s) = (term999 A B x''' y''' f s).
Proof. exact (MK_COMB (@lem4001989 A B x''' y''' f s) (@lem4001864 A B x''' y''' f s)). Qed.
Lemma lem4001991 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4001992 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (f : A -> B) (s : A -> Prop) : (term1000 A B x''' y''' f s) = (term1001 A B x''' y''' f s).
Proof. exact (MK_COMB (@lem4001991) (@lem4001990 A B x''' y''' f s)). Qed.
Lemma lem4001993 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (f : A -> B) (s : A -> Prop) : (term1002 A B x''' y''' f s) = (term1003 A B x''' y''' f s).
Proof. exact (MK_COMB (@lem4001992 A B x''' y''' f s) (@lem4001825 A s)). Qed.
Lemma lem4001994 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4001995 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (f : A -> B) (s : A -> Prop) : (term1004 A B x''' y''' f s) = (term1005 A B x''' y''' f s).
Proof. exact (MK_COMB (@lem4001994) (@lem4001993 A B x''' y''' f s)). Qed.
Lemma lem4001996 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (f : A -> B) (s : A -> Prop) : (term1006 A B x''' y''' f s) = (term1007 A B x''' y''' f s).
Proof. exact (MK_COMB (@lem4001995 A B x''' y''' f s) (@lem4001815 A B f s)). Qed.
Lemma lem4001997 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (f : A -> B) : (term1008 A B x''' y''' f) = (term1009 A B x''' y''' f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4001996 A B x''' y''' f s)). Qed.
Lemma lem4001998 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4001999 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (f : A -> B) : (term564 A B x''' y''' f) = (term1010 A B x''' y''' f).
Proof. exact (MK_COMB (@lem4001998 A) (@lem4001997 A B x''' y''' f)). Qed.
Lemma lem4002000 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) : (term566 A B x''' y''') = (term1011 A B x''' y''').
Proof. exact (fun_ext (fun f : A -> B => @lem4001999 A B x''' y''' f)). Qed.
Lemma lem4002001 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4002002 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) : (term568 A B x''' y''') = (term1012 A B x''' y''').
Proof. exact (MK_COMB (@lem4002001 A B) (@lem4002000 A B x''' y''')). Qed.
Lemma lem4002003 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (h1 : term568 A B x''' y''') : term1012 A B x''' y'''.
Proof. exact (EQ_MP (@lem4002002 A B x''' y''') (@lem4001106 A B x''' y''' h1)). Qed.
Lemma lem4002227 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4002228 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem4002229 {B : Type'} : (@CARD B) = (@CARD B).
Proof. exact (eq_refl (@CARD B)). Qed.
Lemma lem4002236 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4002237 {A B : Type'} (f : type528 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> Prop) -> B -> Prop) f x).
Proof. exact (@lem4002236 (A -> B) (type678 A B) f x). Qed.
Lemma lem4002238 {A B : Type'} (f : A -> B) : (@IMAGE A B f) = (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f).
Proof. exact (@lem4002237 A B (@IMAGE A B) f). Qed.
Lemma lem4002239 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4002240 {A B : Type'} (f : A -> B) (s : A -> Prop) : (@IMAGE A B f s) = (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f s).
Proof. exact (MK_COMB (@lem4002238 A B f) (@lem4002239 A s)). Qed.
Lemma lem4002242 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4002243 {A B : Type'} (f : type678 A B) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> B -> Prop) f x).
Proof. exact (@lem4002242 (A -> Prop) (B -> Prop) f x). Qed.
Lemma lem4002244 {A B : Type'} (f : A -> B) (s : A -> Prop) : (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f s) = (term967 A B f s).
Proof. exact (@lem4002243 A B (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f) s). Qed.
Lemma lem4002246 {A B : Type'} (f : A -> B) (s : A -> Prop) : (@IMAGE A B f s) = (term967 A B f s).
Proof. exact (TRANS (@lem4002240 A B f s) (@lem4002244 A B f s)). Qed.
Lemma lem4002247 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term33 A B f s) = (term968 A B f s).
Proof. exact (MK_COMB (@lem4002229 B) (@lem4002246 A B f s)). Qed.
Lemma lem4002249 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4002250 {B : Type'} (f : type687 B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> nat) f x).
Proof. exact (@lem4002249 (B -> Prop) nat f x). Qed.
Lemma lem4002251 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term968 A B f s) = (term969 A B f s).
Proof. exact (@lem4002250 B (@CARD B) (term967 A B f s)). Qed.
Lemma lem4002252 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term33 A B f s) = (term969 A B f s).
Proof. exact (TRANS (@lem4002247 A B f s) (@lem4002251 A B f s)). Qed.
Lemma lem4002253 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem4002254 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term970 A B f s) = (term971 A B f s).
Proof. exact (MK_COMB (@lem4002228) (@lem4002252 A B f s)). Qed.
Lemma lem4002255 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : ((term33 A B f s) = n) = ((term969 A B f s) = n).
Proof. exact (MK_COMB (@lem4002254 A B f s) (@lem4002253 n)). Qed.
Lemma lem4002256 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term146 A B f s n) = (term1013 A B f s n).
Proof. exact (MK_COMB (@lem4002227) (@lem4002255 A B f s n)). Qed.
Lemma lem4002257 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem4002262 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4002263 {A : Type'} (f : type687 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> nat) f x).
Proof. exact (@lem4002262 (A -> Prop) nat f x). Qed.
Lemma lem4002265 {A : Type'} (s : A -> Prop) : (@CARD A s) = (@I ((A -> Prop) -> nat) (@CARD A) s).
Proof. exact (@lem4002263 A (@CARD A) s). Qed.
Lemma lem4002266 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem4002267 {A : Type'} (s : A -> Prop) : (term1014 A s) = (term1015 A s).
Proof. exact (MK_COMB (@lem4002257) (@lem4002265 A s)). Qed.
Lemma lem4002268 {A : Type'} (s : A -> Prop) (n : nat) : ((@CARD A s) = n) = ((@I ((A -> Prop) -> nat) (@CARD A) s) = n).
Proof. exact (MK_COMB (@lem4002267 A s) (@lem4002266 n)). Qed.
Lemma lem4002273 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4002274 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4002273 (A -> Prop) Prop f x). Qed.
Lemma lem4002276 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@I ((A -> Prop) -> Prop) (@FINITE A) s).
Proof. exact (@lem4002274 A (@FINITE A) s). Qed.
Lemma lem4002277 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4002278 {A : Type'} (s : A -> Prop) : (term1016 A s) = (term1017 A s).
Proof. exact (MK_COMB (@lem4002277) (@lem4002276 A s)). Qed.
Lemma lem4002279 {A : Type'} (s : A -> Prop) (n : nat) : (term15 A s n) = (term1018 A s n).
Proof. exact (MK_COMB (@lem4002278 A s) (@lem4002268 A s n)). Qed.
Lemma lem4002284 {A : Type'} (x : A) (y : A) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem4002285 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4002286 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem4002291 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4002293 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem4002291 A B f x). Qed.
Lemma lem4002298 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4002299 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem4002298 A B f x). Qed.
Lemma lem4002301 {A B : Type'} (f : A -> B) (y : A) : (f y) = (@I (A -> B) f y).
Proof. exact (@lem4002299 A B f y). Qed.
Lemma lem4002302 {A B : Type'} (f : A -> B) (x : A) : (term1019 A B f x) = (term1020 A B f x).
Proof. exact (MK_COMB (@lem4002286 B) (@lem4002293 A B f x)). Qed.
Lemma lem4002303 {A B : Type'} (x : A) (f : A -> B) (y : A) : ((f x) = (f y)) = ((@I (A -> B) f x) = (@I (A -> B) f y)).
Proof. exact (MK_COMB (@lem4002302 A B f x) (@lem4002301 A B f y)). Qed.
Lemma lem4002304 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term1021 A B x f y) = (term1022 A B x f y).
Proof. exact (MK_COMB (@lem4002285) (@lem4002303 A B x f y)). Qed.
Lemma lem4002305 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4002312 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4002313 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4002312 A (type686 A) f x). Qed.
Lemma lem4002314 {A : Type'} (y : A) : (@IN A y) = (@I (A -> (A -> Prop) -> Prop) (@IN A) y).
Proof. exact (@lem4002313 A (@IN A) y). Qed.
Lemma lem4002315 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4002316 {A : Type'} (y : A) (s : A -> Prop) : (@IN A y s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) y s).
Proof. exact (MK_COMB (@lem4002314 A y) (@lem4002315 A s)). Qed.
Lemma lem4002318 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4002319 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4002318 (A -> Prop) Prop f x). Qed.
Lemma lem4002320 {A : Type'} (y : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) y s) = (term1023 A y s).
Proof. exact (@lem4002319 A (@I (A -> (A -> Prop) -> Prop) (@IN A) y) s). Qed.
Lemma lem4002322 {A : Type'} (y : A) (s : A -> Prop) : (@IN A y s) = (term1023 A y s).
Proof. exact (TRANS (@lem4002316 A y s) (@lem4002320 A y s)). Qed.
Lemma lem4002323 {A : Type'} (y : A) (s : A -> Prop) : (term1024 A y s) = (term1025 A y s).
Proof. exact (MK_COMB (@lem4002305) (@lem4002322 A y s)). Qed.
Lemma lem4002324 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4002325 {A : Type'} (y : A) (s : A -> Prop) : (term130 A y s) = (term1026 A y s).
Proof. exact (MK_COMB (@lem4002324) (@lem4002323 A y s)). Qed.
Lemma lem4002326 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term129 A B s x f y) = (term1027 A B s x f y).
Proof. exact (MK_COMB (@lem4002325 A y s) (@lem4002304 A B x f y)). Qed.
Lemma lem4002327 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4002334 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4002335 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4002334 A (type686 A) f x). Qed.
Lemma lem4002336 {A : Type'} (x : A) : (@IN A x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x).
Proof. exact (@lem4002335 A (@IN A) x). Qed.
Lemma lem4002337 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4002338 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x s).
Proof. exact (MK_COMB (@lem4002336 A x) (@lem4002337 A s)). Qed.
Lemma lem4002340 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4002341 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4002340 (A -> Prop) Prop f x). Qed.
Lemma lem4002342 {A : Type'} (x : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x s) = (term1023 A x s).
Proof. exact (@lem4002341 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x) s). Qed.
Lemma lem4002344 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (term1023 A x s).
Proof. exact (TRANS (@lem4002338 A x s) (@lem4002342 A x s)). Qed.
Lemma lem4002345 {A : Type'} (x : A) (s : A -> Prop) : (term1024 A x s) = (term1025 A x s).
Proof. exact (MK_COMB (@lem4002327) (@lem4002344 A x s)). Qed.
Lemma lem4002346 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4002347 {A : Type'} (x : A) (s : A -> Prop) : (term130 A x s) = (term1026 A x s).
Proof. exact (MK_COMB (@lem4002346) (@lem4002345 A x s)). Qed.
Lemma lem4002348 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term132 A B s x f y) = (term1028 A B s x f y).
Proof. exact (MK_COMB (@lem4002347 A x s) (@lem4002326 A B s x f y)). Qed.
Lemma lem4002349 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4002350 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term136 A B s x f y) = (term1029 A B s x f y).
Proof. exact (MK_COMB (@lem4002349) (@lem4002348 A B s x f y)). Qed.
Lemma lem4002351 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term138 A B s f x y) = (term1030 A B s f x y).
Proof. exact (MK_COMB (@lem4002350 A B s x f y) (@lem4002284 A x y)). Qed.
Lemma lem4002352 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term140 A B s f x) = (term1031 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem4002351 A B s f x y)). Qed.
Lemma lem4002353 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4002354 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term141 A B s f x) = (term1032 A B s f x).
Proof. exact (MK_COMB (@lem4002353 A) (@lem4002352 A B s f x)). Qed.
Lemma lem4002355 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term142 A B s f) = (term1033 A B s f).
Proof. exact (fun_ext (fun x : A => @lem4002354 A B s f x)). Qed.
Lemma lem4002356 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4002357 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term143 A B s f) = (term1034 A B s f).
Proof. exact (MK_COMB (@lem4002356 A) (@lem4002355 A B s f)). Qed.
Lemma lem4002358 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4002359 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term144 A B s f) = (term1035 A B s f).
Proof. exact (MK_COMB (@lem4002358) (@lem4002357 A B s f)). Qed.
Lemma lem4002360 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term145 A B f s n) = (term1036 A B f s n).
Proof. exact (MK_COMB (@lem4002359 A B s f) (@lem4002279 A s n)). Qed.
Lemma lem4002361 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4002362 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term148 A B f s n) = (term1037 A B f s n).
Proof. exact (MK_COMB (@lem4002361) (@lem4002360 A B f s n)). Qed.
Lemma lem4002363 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term150 A B f s n) = (term1038 A B f s n).
Proof. exact (MK_COMB (@lem4002362 A B f s n) (@lem4002256 A B f s n)). Qed.
Lemma lem4002364 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term150 A B f s n) : term1038 A B f s n.
Proof. exact (EQ_MP (@lem4002363 A B f s n) (@lem4001111 A B f s n h1)). Qed.
Lemma lem4002366 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term150 A B f s n) : term1036 A B f s n.
Proof. exact (proj1 (@lem4002364 A B f s n h1)). Qed.
Lemma lem4002367 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term150 A B f s n) : term1018 A s n.
Proof. exact (proj2 (@lem4002366 A B f s n h1)). Qed.
Lemma lem4002368 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term150 A B f s n) : term1034 A B s f.
Proof. exact (proj1 (@lem4002366 A B f s n h1)). Qed.
Lemma lem4002582 {A B : Type'} (f : A -> B) (s : A -> Prop) : ((term969 A B f s) = (@I ((A -> Prop) -> nat) (@CARD A) s)) = ((term969 A B f s) = (@I ((A -> Prop) -> nat) (@CARD A) s)).
Proof. exact (eq_refl ((term969 A B f s) = (@I ((A -> Prop) -> nat) (@CARD A) s))). Qed.
Lemma lem4002600 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (f : A -> B) (s : A -> Prop) : (term1003 A B x''' y''' f s) = (term1039 A B x''' y''' f s).
Proof. exact (@lem19699 (term995 A B x''' y''' f s) (term977 A B x''' y''' f s) (term972 A s)). Qed.
Lemma lem4002601 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (f : A -> B) (s : A -> Prop) : (term1040 A B x''' y''' f s) = (term1040 A B x''' y''' f s).
Proof. exact (eq_refl (term1040 A B x''' y''' f s)). Qed.
Lemma lem4002602 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (f : A -> B) (s : A -> Prop) : (term1041 A B x''' y''' f s) = (term1042 A B x''' y''' f s).
Proof. exact (@lem19699 (term989 A B x''' f s) (term993 A B x''' y''' f s) (term972 A s)). Qed.
Lemma lem4002609 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (f : A -> B) (s : A -> Prop) : (term1043 A B x''' y''' f s) = (term1044 A B x''' y''' f s).
Proof. exact (@lem19699 (term989 A B y''' f s) ((term980 A B x''' f s) = (term980 A B y''' f s)) (term972 A s)). Qed.
Lemma lem4002612 {A B : Type'} (x''' : type529 A B) (f : A -> B) (s : A -> Prop) : (term1045 A B x''' f s) = (term1045 A B x''' f s).
Proof. exact (eq_refl (term1045 A B x''' f s)). Qed.
Lemma lem4002613 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (f : A -> B) (s : A -> Prop) : (term1042 A B x''' y''' f s) = (term1046 A B x''' y''' f s).
Proof. exact (MK_COMB (@lem4002612 A B x''' f s) (@lem4002609 A B x''' y''' f s)). Qed.
Lemma lem4002614 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (f : A -> B) (s : A -> Prop) : (term1041 A B x''' y''' f s) = (term1046 A B x''' y''' f s).
Proof. exact (TRANS (@lem4002602 A B x''' y''' f s) (@lem4002613 A B x''' y''' f s)). Qed.
Lemma lem4002615 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4002616 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (f : A -> B) (s : A -> Prop) : (term1047 A B x''' y''' f s) = (term1048 A B x''' y''' f s).
Proof. exact (MK_COMB (@lem4002615) (@lem4002614 A B x''' y''' f s)). Qed.
Lemma lem4002617 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (f : A -> B) (s : A -> Prop) : (term1039 A B x''' y''' f s) = (term1049 A B x''' y''' f s).
Proof. exact (MK_COMB (@lem4002616 A B x''' y''' f s) (@lem4002601 A B x''' y''' f s)). Qed.
Lemma lem4002619 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (f : A -> B) (s : A -> Prop) : (term1003 A B x''' y''' f s) = (term1049 A B x''' y''' f s).
Proof. exact (TRANS (@lem4002600 A B x''' y''' f s) (@lem4002617 A B x''' y''' f s)). Qed.
Lemma lem4002620 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4002621 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (f : A -> B) (s : A -> Prop) : (term1005 A B x''' y''' f s) = (term1050 A B x''' y''' f s).
Proof. exact (MK_COMB (@lem4002620) (@lem4002619 A B x''' y''' f s)). Qed.
Lemma lem4002622 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (f : A -> B) (s : A -> Prop) : (term1007 A B x''' y''' f s) = (term1051 A B x''' y''' f s).
Proof. exact (MK_COMB (@lem4002621 A B x''' y''' f s) (@lem4002582 A B f s)). Qed.
Lemma lem4002623 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (f : A -> B) (s : A -> Prop) : (term1051 A B x''' y''' f s) = (term1052 A B x''' y''' f s).
Proof. exact (@lem19699 (term1046 A B x''' y''' f s) (term1040 A B x''' y''' f s) ((term969 A B f s) = (@I ((A -> Prop) -> nat) (@CARD A) s))). Qed.
Lemma lem4002624 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (f : A -> B) (s : A -> Prop) : (term1053 A B x''' y''' f s) = (term1053 A B x''' y''' f s).
Proof. exact (eq_refl (term1053 A B x''' y''' f s)). Qed.
Lemma lem4002625 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (f : A -> B) (s : A -> Prop) : (term1054 A B x''' y''' f s) = (term1055 A B x''' y''' f s).
Proof. exact (@lem19699 (term1056 A B x''' f s) (term1044 A B x''' y''' f s) ((term969 A B f s) = (@I ((A -> Prop) -> nat) (@CARD A) s))). Qed.
Lemma lem4002632 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (f : A -> B) (s : A -> Prop) : (term1057 A B x''' y''' f s) = (term1058 A B x''' y''' f s).
Proof. exact (@lem19699 (term1056 A B y''' f s) (term1059 A B x''' y''' f s) ((term969 A B f s) = (@I ((A -> Prop) -> nat) (@CARD A) s))). Qed.
Lemma lem4002635 {A B : Type'} (x''' : type529 A B) (f : A -> B) (s : A -> Prop) : (term1060 A B x''' f s) = (term1060 A B x''' f s).
Proof. exact (eq_refl (term1060 A B x''' f s)). Qed.
Lemma lem4002636 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (f : A -> B) (s : A -> Prop) : (term1055 A B x''' y''' f s) = (term1061 A B x''' y''' f s).
Proof. exact (MK_COMB (@lem4002635 A B x''' f s) (@lem4002632 A B x''' y''' f s)). Qed.
Lemma lem4002637 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (f : A -> B) (s : A -> Prop) : (term1054 A B x''' y''' f s) = (term1061 A B x''' y''' f s).
Proof. exact (TRANS (@lem4002625 A B x''' y''' f s) (@lem4002636 A B x''' y''' f s)). Qed.
Lemma lem4002638 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4002639 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (f : A -> B) (s : A -> Prop) : (term1062 A B x''' y''' f s) = (term1063 A B x''' y''' f s).
Proof. exact (MK_COMB (@lem4002638) (@lem4002637 A B x''' y''' f s)). Qed.
Lemma lem4002640 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (f : A -> B) (s : A -> Prop) : (term1052 A B x''' y''' f s) = (term1064 A B x''' y''' f s).
Proof. exact (MK_COMB (@lem4002639 A B x''' y''' f s) (@lem4002624 A B x''' y''' f s)). Qed.
Lemma lem4002641 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (f : A -> B) (s : A -> Prop) : (term1051 A B x''' y''' f s) = (term1064 A B x''' y''' f s).
Proof. exact (TRANS (@lem4002623 A B x''' y''' f s) (@lem4002640 A B x''' y''' f s)). Qed.
Lemma lem4002642 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (f : A -> B) (s : A -> Prop) : (term1007 A B x''' y''' f s) = (term1064 A B x''' y''' f s).
Proof. exact (TRANS (@lem4002622 A B x''' y''' f s) (@lem4002641 A B x''' y''' f s)). Qed.
Lemma lem4002643 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (f : A -> B) : (term1009 A B x''' y''' f) = (term1065 A B x''' y''' f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4002642 A B x''' y''' f s)). Qed.
Lemma lem4002644 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4002645 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (f : A -> B) : (term1010 A B x''' y''' f) = (term1066 A B x''' y''' f).
Proof. exact (MK_COMB (@lem4002644 A) (@lem4002643 A B x''' y''' f)). Qed.
Lemma lem4002646 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) : (term1011 A B x''' y''') = (term1067 A B x''' y''').
Proof. exact (fun_ext (fun f : A -> B => @lem4002645 A B x''' y''' f)). Qed.
Lemma lem4002647 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4002649 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) : (term1012 A B x''' y''') = (term1068 A B x''' y''').
Proof. exact (MK_COMB (@lem4002647 A B) (@lem4002646 A B x''' y''')). Qed.
Lemma lem4002650 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (h1 : term568 A B x''' y''') : term1068 A B x''' y'''.
Proof. exact (EQ_MP (@lem4002649 A B x''' y''') (@lem4002003 A B x''' y''' h1)). Qed.
Lemma lem4002744 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term1030 A B s f x y) = (term1030 A B s f x y).
Proof. exact (eq_refl (term1030 A B s f x y)). Qed.
Lemma lem4002745 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term1031 A B s f x) = (term1031 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem4002744 A B s f x y)). Qed.
Lemma lem4002746 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4002747 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term1032 A B s f x) = (term1032 A B s f x).
Proof. exact (MK_COMB (@lem4002746 A) (@lem4002745 A B s f x)). Qed.
Lemma lem4002748 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term1033 A B s f) = (term1033 A B s f).
Proof. exact (fun_ext (fun x : A => @lem4002747 A B s f x)). Qed.
Lemma lem4002749 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4002751 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term1034 A B s f) = (term1034 A B s f).
Proof. exact (MK_COMB (@lem4002749 A) (@lem4002748 A B s f)). Qed.
Lemma lem4002752 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term150 A B f s n) : term1034 A B s f.
Proof. exact (EQ_MP (@lem4002751 A B s f) (@lem4002368 A B f s n h1)). Qed.
Lemma lem4002779 {A B : Type'} (_46078 : A -> B) (x''' : type529 A B) (y''' : type529 A B) (h1 : term568 A B x''' y''') : term1069 A B x''' y''' _46078.
Proof. exact (@lem4002650 A B x''' y''' h1 _46078). Qed.
Lemma lem4002780 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (_46078 : A -> B) : (term1069 A B x''' y''' _46078) = (term1066 A B x''' y''' _46078).
Proof. exact (eq_refl (term1069 A B x''' y''' _46078)). Qed.
Lemma lem4002781 {A B : Type'} (_46078 : A -> B) (x''' : type529 A B) (y''' : type529 A B) (h1 : term568 A B x''' y''') : term1066 A B x''' y''' _46078.
Proof. exact (EQ_MP (@lem4002780 A B x''' y''' _46078) (@lem4002779 A B _46078 x''' y''' h1)). Qed.
Lemma lem4002782 {A B : Type'} (_46078 : A -> B) (_46079 : A -> Prop) (x''' : type529 A B) (y''' : type529 A B) (h1 : term568 A B x''' y''') : term1070 A B x''' y''' _46078 _46079.
Proof. exact (@lem4002781 A B _46078 x''' y''' h1 _46079). Qed.
Lemma lem4002783 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (_46078 : A -> B) (_46079 : A -> Prop) : (term1070 A B x''' y''' _46078 _46079) = (term1064 A B x''' y''' _46078 _46079).
Proof. exact (eq_refl (term1070 A B x''' y''' _46078 _46079)). Qed.
Lemma lem4002784 {A B : Type'} (_46078 : A -> B) (_46079 : A -> Prop) (x''' : type529 A B) (y''' : type529 A B) (h1 : term568 A B x''' y''') : term1064 A B x''' y''' _46078 _46079.
Proof. exact (EQ_MP (@lem4002783 A B x''' y''' _46078 _46079) (@lem4002782 A B _46078 _46079 x''' y''' h1)). Qed.
Lemma lem4002791 {A B : Type'} (_46082 : A) (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term150 A B f s n) : term1071 A B s f _46082.
Proof. exact (@lem4002752 A B f s n h1 _46082). Qed.
Lemma lem4002792 {A B : Type'} (s : A -> Prop) (f : A -> B) (_46082 : A) : (term1071 A B s f _46082) = (term1032 A B s f _46082).
Proof. exact (eq_refl (term1071 A B s f _46082)). Qed.
Lemma lem4002793 {A B : Type'} (_46082 : A) (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term150 A B f s n) : term1032 A B s f _46082.
Proof. exact (EQ_MP (@lem4002792 A B s f _46082) (@lem4002791 A B _46082 f s n h1)). Qed.
Lemma lem4002794 {A B : Type'} (_46082 : A) (_46083 : A) (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term150 A B f s n) : term1072 A B s f _46082 _46083.
Proof. exact (@lem4002793 A B _46082 f s n h1 _46083). Qed.
Lemma lem4002795 {A B : Type'} (s : A -> Prop) (f : A -> B) (_46082 : A) (_46083 : A) : (term1072 A B s f _46082 _46083) = (term1030 A B s f _46082 _46083).
Proof. exact (eq_refl (term1072 A B s f _46082 _46083)). Qed.
Lemma lem4002796 {A B : Type'} (_46082 : A) (_46083 : A) (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term150 A B f s n) : term1030 A B s f _46082 _46083.
Proof. exact (EQ_MP (@lem4002795 A B s f _46082 _46083) (@lem4002794 A B _46082 _46083 f s n h1)). Qed.
Lemma lem4002803 {A B : Type'} (_46078 : A -> B) (_46079 : A -> Prop) (x''' : type529 A B) (y''' : type529 A B) (h1 : term568 A B x''' y''') : term1053 A B x''' y''' _46078 _46079.
Proof. exact (proj2 (@lem4002784 A B _46078 _46079 x''' y''' h1)). Qed.
Lemma lem4002804 {A B : Type'} (_46078 : A -> B) (_46079 : A -> Prop) (x''' : type529 A B) (y''' : type529 A B) (h1 : term568 A B x''' y''') : term1061 A B x''' y''' _46078 _46079.
Proof. exact (proj1 (@lem4002784 A B _46078 _46079 x''' y''' h1)). Qed.
Lemma lem4002805 {A B : Type'} (_46078 : A -> B) (_46079 : A -> Prop) (x''' : type529 A B) (y''' : type529 A B) (h1 : term568 A B x''' y''') : term1058 A B x''' y''' _46078 _46079.
Proof. exact (proj2 (@lem4002804 A B _46078 _46079 x''' y''' h1)). Qed.
Lemma lem4002806 {A B : Type'} (_46078 : A -> B) (_46079 : A -> Prop) (x''' : type529 A B) (y''' : type529 A B) (h1 : term568 A B x''' y''') : term1073 A B x''' _46078 _46079.
Proof. exact (proj1 (@lem4002804 A B _46078 _46079 x''' y''' h1)). Qed.
Lemma lem4002807 {A B : Type'} (_46078 : A -> B) (_46079 : A -> Prop) (x''' : type529 A B) (y''' : type529 A B) (h1 : term568 A B x''' y''') : term1074 A B x''' y''' _46078 _46079.
Proof. exact (proj2 (@lem4002805 A B _46078 _46079 x''' y''' h1)). Qed.
Lemma lem4002808 {A B : Type'} (_46078 : A -> B) (_46079 : A -> Prop) (x''' : type529 A B) (y''' : type529 A B) (h1 : term568 A B x''' y''') : term1073 A B y''' _46078 _46079.
Proof. exact (proj1 (@lem4002805 A B _46078 _46079 x''' y''' h1)). Qed.
Lemma lem4002828 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term150 A B f s n) : term1013 A B f s n.
Proof. exact (proj2 (@lem4002364 A B f s n h1)). Qed.
Lemma lem4002832 {A B : Type'} (s : A -> Prop) (f : A -> B) (_46082 : A) (_46083 : A) : (term1030 A B s f _46082 _46083) = (term1075 A B s f _46082 _46083).
Proof. exact (@lem3996368 (term1025 A _46082 s) (term1027 A B s _46082 f _46083) (_46082 = _46083)). Qed.
Lemma lem4002839 {A B : Type'} (s : A -> Prop) (f : A -> B) (_46082 : A) (_46083 : A) : (term1076 A B s f _46082 _46083) = (term1077 A B s f _46082 _46083).
Proof. exact (@lem3996368 (term1025 A _46083 s) (term1022 A B _46082 f _46083) (_46082 = _46083)). Qed.
Lemma lem4002840 {A : Type'} (_46082 : A) (s : A -> Prop) : (term1026 A _46082 s) = (term1026 A _46082 s).
Proof. exact (eq_refl (term1026 A _46082 s)). Qed.
Lemma lem4002843 {A B : Type'} (s : A -> Prop) (f : A -> B) (_46082 : A) (_46083 : A) : (term1075 A B s f _46082 _46083) = (term1078 A B s f _46082 _46083).
Proof. exact (MK_COMB (@lem4002840 A _46082 s) (@lem4002839 A B s f _46082 _46083)). Qed.
Lemma lem4002845 {A B : Type'} (s : A -> Prop) (f : A -> B) (_46082 : A) (_46083 : A) : (term1030 A B s f _46082 _46083) = (term1078 A B s f _46082 _46083).
Proof. exact (TRANS (@lem4002832 A B s f _46082 _46083) (@lem4002843 A B s f _46082 _46083)). Qed.
Lemma lem4002850 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term150 A B f s n) : (@I ((A -> Prop) -> nat) (@CARD A) s) = n.
Proof. exact (proj2 (@lem4002367 A B f s n h1)). Qed.
Lemma lem4002909 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (_46078 : A -> B) (_46079 : A -> Prop) : (term1053 A B x''' y''' _46078 _46079) = (term1079 A B x''' y''' _46078 _46079).
Proof. exact (@lem3996368 (term977 A B x''' y''' _46078 _46079) (term972 A _46079) ((term969 A B _46078 _46079) = (@I ((A -> Prop) -> nat) (@CARD A) _46079))). Qed.
Lemma lem4002921 {A B : Type'} (x''' : type529 A B) (_46078 : A -> B) (_46079 : A -> Prop) : (term1073 A B x''' _46078 _46079) = (term1080 A B x''' _46078 _46079).
Proof. exact (@lem3996368 (term989 A B x''' _46078 _46079) (term972 A _46079) ((term969 A B _46078 _46079) = (@I ((A -> Prop) -> nat) (@CARD A) _46079))). Qed.
Lemma lem4002933 {A B : Type'} (y''' : type529 A B) (_46078 : A -> B) (_46079 : A -> Prop) : (term1073 A B y''' _46078 _46079) = (term1080 A B y''' _46078 _46079).
Proof. exact (@lem3996368 (term989 A B y''' _46078 _46079) (term972 A _46079) ((term969 A B _46078 _46079) = (@I ((A -> Prop) -> nat) (@CARD A) _46079))). Qed.
Lemma lem4002945 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (_46078 : A -> B) (_46079 : A -> Prop) : (term1074 A B x''' y''' _46078 _46079) = (term1081 A B x''' y''' _46078 _46079).
Proof. exact (@lem3996368 ((term980 A B x''' _46078 _46079) = (term980 A B y''' _46078 _46079)) (term972 A _46079) ((term969 A B _46078 _46079) = (@I ((A -> Prop) -> nat) (@CARD A) _46079))). Qed.
Lemma lem4003091 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term150 A B f s n) : n = (@I ((A -> Prop) -> nat) (@CARD A) s).
Proof. exact (SYM (@lem4002850 A B f s n h1)). Qed.
Lemma lem4003106 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term1082 A B f s) = (term1082 A B f s).
Proof. exact (eq_refl (term1082 A B f s)). Qed.
Lemma lem4003107 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term150 A B f s n) : (term1083 A B f s n) = (term1084 A B f s).
Proof. exact (MK_COMB (@lem4003106 A B f s) (@lem4003091 A B f s n h1)). Qed.
Lemma lem4003108 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term1084 A B f s) = (term1085 A B f s).
Proof. exact (eq_refl (term1084 A B f s)). Qed.
Lemma lem4003109 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term1086 A B f s n) = (term1086 A B f s n).
Proof. exact (eq_refl (term1086 A B f s n)). Qed.
Lemma lem4003110 {A B : Type'} (n : nat) (f : A -> B) (s : A -> Prop) : ((term1083 A B f s n) = (term1084 A B f s)) = ((term1083 A B f s n) = (term1085 A B f s)).
Proof. exact (MK_COMB (@lem4003109 A B f s n) (@lem4003108 A B f s)). Qed.
Lemma lem4003111 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term1083 A B f s n) = (term1013 A B f s n).
Proof. exact (eq_refl (term1083 A B f s n)). Qed.
Lemma lem4003112 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4003113 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term1086 A B f s n) = (term1087 A B f s n).
Proof. exact (MK_COMB (@lem4003112) (@lem4003111 A B f s n)). Qed.
Lemma lem4003114 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term1085 A B f s) = (term1085 A B f s).
Proof. exact (eq_refl (term1085 A B f s)). Qed.
Lemma lem4003115 {A B : Type'} (n : nat) (f : A -> B) (s : A -> Prop) : ((term1083 A B f s n) = (term1085 A B f s)) = ((term1013 A B f s n) = (term1085 A B f s)).
Proof. exact (MK_COMB (@lem4003113 A B f s n) (@lem4003114 A B f s)). Qed.
Lemma lem4003116 {A B : Type'} (n : nat) (f : A -> B) (s : A -> Prop) : ((term1083 A B f s n) = (term1084 A B f s)) = ((term1013 A B f s n) = (term1085 A B f s)).
Proof. exact (TRANS (@lem4003110 A B n f s) (@lem4003115 A B n f s)). Qed.
Lemma lem4003117 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term150 A B f s n) : (term1013 A B f s n) = (term1085 A B f s).
Proof. exact (EQ_MP (@lem4003116 A B n f s) (@lem4003107 A B f s n h1)). Qed.
Lemma lem4003118 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term150 A B f s n) : term1085 A B f s.
Proof. exact (EQ_MP (@lem4003117 A B f s n h1) (@lem4002828 A B f s n h1)). Qed.
Lemma lem4003132 {A B : Type'} (_46082 : A) (_46083 : A) (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term150 A B f s n) : term1078 A B s f _46082 _46083.
Proof. exact (EQ_MP (@lem4002845 A B s f _46082 _46083) (@lem4002796 A B _46082 _46083 f s n h1)). Qed.
Lemma lem4003216 {A B : Type'} (_46078 : A -> B) (_46079 : A -> Prop) (x''' : type529 A B) (y''' : type529 A B) (h1 : term568 A B x''' y''') : term1079 A B x''' y''' _46078 _46079.
Proof. exact (EQ_MP (@lem4002909 A B x''' y''' _46078 _46079) (@lem4002803 A B _46078 _46079 x''' y''' h1)). Qed.
Lemma lem4003230 {A B : Type'} (_46078 : A -> B) (_46079 : A -> Prop) (x''' : type529 A B) (y''' : type529 A B) (h1 : term568 A B x''' y''') : term1080 A B x''' _46078 _46079.
Proof. exact (EQ_MP (@lem4002921 A B x''' _46078 _46079) (@lem4002806 A B _46078 _46079 x''' y''' h1)). Qed.
Lemma lem4003244 {A B : Type'} (_46078 : A -> B) (_46079 : A -> Prop) (x''' : type529 A B) (y''' : type529 A B) (h1 : term568 A B x''' y''') : term1080 A B y''' _46078 _46079.
Proof. exact (EQ_MP (@lem4002933 A B y''' _46078 _46079) (@lem4002808 A B _46078 _46079 x''' y''' h1)). Qed.
Lemma lem4003258 {A B : Type'} (_46078 : A -> B) (_46079 : A -> Prop) (x''' : type529 A B) (y''' : type529 A B) (h1 : term568 A B x''' y''') : term1081 A B x''' y''' _46078 _46079.
Proof. exact (EQ_MP (@lem4002945 A B x''' y''' _46078 _46079) (@lem4002807 A B _46078 _46079 x''' y''' h1)). Qed.
Lemma lem4003979 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term150 A B f s n) : @I ((A -> Prop) -> Prop) (@FINITE A) s.
Proof. exact (proj1 (@lem4002367 A B f s n h1)). Qed.
Lemma lem4003980 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term150 A B f s n) : term1088 A s.
Proof. exact (fun h0 : term972 A s => @lem4003979 A B f s n h1). Qed.
Lemma lem4003982 (p : Prop) : (term1089 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4003983 {A : Type'} (s : A -> Prop) : (term1088 A s) = (@I ((A -> Prop) -> Prop) (@FINITE A) s).
Proof. exact (@lem4003982 (@I ((A -> Prop) -> Prop) (@FINITE A) s)). Qed.
Lemma lem4003984 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term150 A B f s n) : @I ((A -> Prop) -> Prop) (@FINITE A) s.
Proof. exact (EQ_MP (@lem4003983 A s) (@lem4003980 A B f s n h1)). Qed.
Lemma lem4003987 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term1085 A B f s) : term1085 A B f s.
Proof. exact (h1). Qed.
Lemma lem4003988 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term1085 A B f s) : term1090 A B f s.
Proof. exact (fun h0 : (term969 A B f s) = (@I ((A -> Prop) -> nat) (@CARD A) s) => @lem4003987 A B f s h1). Qed.
Lemma lem4003990 (p : Prop) : (term1091 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4003991 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term1090 A B f s) = (term1085 A B f s).
Proof. exact (@lem4003990 ((term969 A B f s) = (@I ((A -> Prop) -> nat) (@CARD A) s))). Qed.
Lemma lem4003992 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term1085 A B f s) : term1085 A B f s.
Proof. exact (EQ_MP (@lem4003991 A B f s) (@lem4003988 A B f s h1)). Qed.
Lemma lem4003994 (b : Prop) (a : Prop) : (a \/ b) = (term1092 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4003995 {A B : Type'} (x''' : type529 A B) (_46078 : A -> B) (_46079 : A -> Prop) : (term1080 A B x''' _46078 _46079) = (term1093 A B x''' _46078 _46079).
Proof. exact (@lem4003994 (term1094 A B _46078 _46079) (term989 A B x''' _46078 _46079)). Qed.
Lemma lem4003997 (a : Prop) (b : Prop) : (term1095 a b) = (term1096 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4003998 {A B : Type'} (_46078 : A -> B) (_46079 : A -> Prop) : (term1097 A B _46078 _46079) = (term1098 A B _46078 _46079).
Proof. exact (@lem4003997 (term972 A _46079) ((term969 A B _46078 _46079) = (@I ((A -> Prop) -> nat) (@CARD A) _46079))). Qed.
Lemma lem4004000 (a : Prop) : (term1099 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4004001 {A : Type'} (_46079 : A -> Prop) : (term1100 A _46079) = (@I ((A -> Prop) -> Prop) (@FINITE A) _46079).
Proof. exact (@lem4004000 (@I ((A -> Prop) -> Prop) (@FINITE A) _46079)). Qed.
Lemma lem4004002 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4004003 {A : Type'} (_46079 : A -> Prop) : (term1101 A _46079) = (term1017 A _46079).
Proof. exact (MK_COMB (@lem4004002) (@lem4004001 A _46079)). Qed.
Lemma lem4004004 {A B : Type'} (_46078 : A -> B) (_46079 : A -> Prop) : (term1085 A B _46078 _46079) = (term1085 A B _46078 _46079).
Proof. exact (eq_refl (term1085 A B _46078 _46079)). Qed.
Lemma lem4004005 {A B : Type'} (_46078 : A -> B) (_46079 : A -> Prop) : (term1098 A B _46078 _46079) = (term1102 A B _46078 _46079).
Proof. exact (MK_COMB (@lem4004003 A _46079) (@lem4004004 A B _46078 _46079)). Qed.
Lemma lem4004006 {A B : Type'} (_46078 : A -> B) (_46079 : A -> Prop) : (term1097 A B _46078 _46079) = (term1102 A B _46078 _46079).
Proof. exact (TRANS (@lem4003998 A B _46078 _46079) (@lem4004005 A B _46078 _46079)). Qed.
Lemma lem4004007 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4004008 {A B : Type'} (_46078 : A -> B) (_46079 : A -> Prop) : (term1103 A B _46078 _46079) = (term1104 A B _46078 _46079).
Proof. exact (MK_COMB (@lem4004007) (@lem4004006 A B _46078 _46079)). Qed.
Lemma lem4004009 {A B : Type'} (x''' : type529 A B) (_46078 : A -> B) (_46079 : A -> Prop) : (term989 A B x''' _46078 _46079) = (term989 A B x''' _46078 _46079).
Proof. exact (eq_refl (term989 A B x''' _46078 _46079)). Qed.
Lemma lem4004010 {A B : Type'} (x''' : type529 A B) (_46078 : A -> B) (_46079 : A -> Prop) : (term1093 A B x''' _46078 _46079) = (term1105 A B x''' _46078 _46079).
Proof. exact (MK_COMB (@lem4004008 A B _46078 _46079) (@lem4004009 A B x''' _46078 _46079)). Qed.
Lemma lem4004011 {A B : Type'} (x''' : type529 A B) (_46078 : A -> B) (_46079 : A -> Prop) : (term1080 A B x''' _46078 _46079) = (term1105 A B x''' _46078 _46079).
Proof. exact (TRANS (@lem4003995 A B x''' _46078 _46079) (@lem4004010 A B x''' _46078 _46079)). Qed.
Lemma lem4004013 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term1085 A B f s) (h2 : term150 A B f s n) : term1102 A B f s.
Proof. exact (conj (@lem4003984 A B f s n h2) (@lem4003992 A B f s h1)). Qed.
Lemma lem4004015 {A B : Type'} (_46078 : A -> B) (_46079 : A -> Prop) (x''' : type529 A B) (y''' : type529 A B) (h1 : term568 A B x''' y''') : term1105 A B x''' _46078 _46079.
Proof. exact (EQ_MP (@lem4004011 A B x''' _46078 _46079) (@lem4003230 A B _46078 _46079 x''' y''' h1)). Qed.
Lemma lem4004016 {A B : Type'} (_46078 : A -> B) (_46079 : A -> Prop) (x''' : type529 A B) (y''' : type529 A B) (h1 : term568 A B x''' y''') : term1105 A B x''' _46078 _46079.
Proof. exact (@lem4004015 A B _46078 _46079 x''' y''' h1). Qed.
Lemma lem4004017 {A B : Type'} (f : A -> B) (s : A -> Prop) (x''' : type529 A B) (y''' : type529 A B) (h1 : term568 A B x''' y''') : term1105 A B x''' f s.
Proof. exact (@lem4004016 A B f s x''' y''' h1). Qed.
Lemma lem4004020 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term568 A B x''' y''') (h2 : term1085 A B f s) (h3 : term150 A B f s n) : term989 A B x''' f s.
Proof. exact (@lem4004017 A B f s x''' y''' h1 (@lem4004013 A B f s n h2 h3)). Qed.
Lemma lem4004021 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term568 A B x''' y''') (h2 : term1085 A B f s) (h3 : term150 A B f s n) : term1106 A B x''' f s.
Proof. exact (fun h0 : term1107 A B x''' f s => @lem4004020 A B x''' y''' f s n h1 h2 h3). Qed.
Lemma lem4004023 (p : Prop) : (term1089 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4004024 {A B : Type'} (x''' : type529 A B) (f : A -> B) (s : A -> Prop) : (term1106 A B x''' f s) = (term989 A B x''' f s).
Proof. exact (@lem4004023 (term989 A B x''' f s)). Qed.
Lemma lem4004025 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term568 A B x''' y''') (h2 : term1085 A B f s) (h3 : term150 A B f s n) : term989 A B x''' f s.
Proof. exact (EQ_MP (@lem4004024 A B x''' f s) (@lem4004021 A B x''' y''' f s n h1 h2 h3)). Qed.
Lemma lem4004027 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term150 A B f s n) : @I ((A -> Prop) -> Prop) (@FINITE A) s.
Proof. exact (proj1 (@lem4002367 A B f s n h1)). Qed.
Lemma lem4004028 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term150 A B f s n) : term1088 A s.
Proof. exact (fun h0 : term972 A s => @lem4004027 A B f s n h1). Qed.
Lemma lem4004030 (p : Prop) : (term1089 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4004031 {A : Type'} (s : A -> Prop) : (term1088 A s) = (@I ((A -> Prop) -> Prop) (@FINITE A) s).
Proof. exact (@lem4004030 (@I ((A -> Prop) -> Prop) (@FINITE A) s)). Qed.
Lemma lem4004032 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term150 A B f s n) : @I ((A -> Prop) -> Prop) (@FINITE A) s.
Proof. exact (EQ_MP (@lem4004031 A s) (@lem4004028 A B f s n h1)). Qed.
Lemma lem4004035 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term1085 A B f s) : term1085 A B f s.
Proof. exact (h1). Qed.
Lemma lem4004036 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term1085 A B f s) : term1090 A B f s.
Proof. exact (fun h0 : (term969 A B f s) = (@I ((A -> Prop) -> nat) (@CARD A) s) => @lem4004035 A B f s h1). Qed.
Lemma lem4004038 (p : Prop) : (term1091 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4004039 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term1090 A B f s) = (term1085 A B f s).
Proof. exact (@lem4004038 ((term969 A B f s) = (@I ((A -> Prop) -> nat) (@CARD A) s))). Qed.
Lemma lem4004040 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term1085 A B f s) : term1085 A B f s.
Proof. exact (EQ_MP (@lem4004039 A B f s) (@lem4004036 A B f s h1)). Qed.
Lemma lem4004042 (b : Prop) (a : Prop) : (a \/ b) = (term1092 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4004043 {A B : Type'} (y''' : type529 A B) (_46078 : A -> B) (_46079 : A -> Prop) : (term1080 A B y''' _46078 _46079) = (term1093 A B y''' _46078 _46079).
Proof. exact (@lem4004042 (term1094 A B _46078 _46079) (term989 A B y''' _46078 _46079)). Qed.
Lemma lem4004045 (a : Prop) (b : Prop) : (term1095 a b) = (term1096 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4004046 {A B : Type'} (_46078 : A -> B) (_46079 : A -> Prop) : (term1097 A B _46078 _46079) = (term1098 A B _46078 _46079).
Proof. exact (@lem4004045 (term972 A _46079) ((term969 A B _46078 _46079) = (@I ((A -> Prop) -> nat) (@CARD A) _46079))). Qed.
Lemma lem4004048 (a : Prop) : (term1099 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4004049 {A : Type'} (_46079 : A -> Prop) : (term1100 A _46079) = (@I ((A -> Prop) -> Prop) (@FINITE A) _46079).
Proof. exact (@lem4004048 (@I ((A -> Prop) -> Prop) (@FINITE A) _46079)). Qed.
Lemma lem4004050 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4004051 {A : Type'} (_46079 : A -> Prop) : (term1101 A _46079) = (term1017 A _46079).
Proof. exact (MK_COMB (@lem4004050) (@lem4004049 A _46079)). Qed.
Lemma lem4004052 {A B : Type'} (_46078 : A -> B) (_46079 : A -> Prop) : (term1085 A B _46078 _46079) = (term1085 A B _46078 _46079).
Proof. exact (eq_refl (term1085 A B _46078 _46079)). Qed.
Lemma lem4004053 {A B : Type'} (_46078 : A -> B) (_46079 : A -> Prop) : (term1098 A B _46078 _46079) = (term1102 A B _46078 _46079).
Proof. exact (MK_COMB (@lem4004051 A _46079) (@lem4004052 A B _46078 _46079)). Qed.
Lemma lem4004054 {A B : Type'} (_46078 : A -> B) (_46079 : A -> Prop) : (term1097 A B _46078 _46079) = (term1102 A B _46078 _46079).
Proof. exact (TRANS (@lem4004046 A B _46078 _46079) (@lem4004053 A B _46078 _46079)). Qed.
Lemma lem4004055 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4004056 {A B : Type'} (_46078 : A -> B) (_46079 : A -> Prop) : (term1103 A B _46078 _46079) = (term1104 A B _46078 _46079).
Proof. exact (MK_COMB (@lem4004055) (@lem4004054 A B _46078 _46079)). Qed.
Lemma lem4004057 {A B : Type'} (y''' : type529 A B) (_46078 : A -> B) (_46079 : A -> Prop) : (term989 A B y''' _46078 _46079) = (term989 A B y''' _46078 _46079).
Proof. exact (eq_refl (term989 A B y''' _46078 _46079)). Qed.
Lemma lem4004058 {A B : Type'} (y''' : type529 A B) (_46078 : A -> B) (_46079 : A -> Prop) : (term1093 A B y''' _46078 _46079) = (term1105 A B y''' _46078 _46079).
Proof. exact (MK_COMB (@lem4004056 A B _46078 _46079) (@lem4004057 A B y''' _46078 _46079)). Qed.
Lemma lem4004059 {A B : Type'} (y''' : type529 A B) (_46078 : A -> B) (_46079 : A -> Prop) : (term1080 A B y''' _46078 _46079) = (term1105 A B y''' _46078 _46079).
Proof. exact (TRANS (@lem4004043 A B y''' _46078 _46079) (@lem4004058 A B y''' _46078 _46079)). Qed.
Lemma lem4004061 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term1085 A B f s) (h2 : term150 A B f s n) : term1102 A B f s.
Proof. exact (conj (@lem4004032 A B f s n h2) (@lem4004040 A B f s h1)). Qed.
Lemma lem4004063 {A B : Type'} (_46078 : A -> B) (_46079 : A -> Prop) (x''' : type529 A B) (y''' : type529 A B) (h1 : term568 A B x''' y''') : term1105 A B y''' _46078 _46079.
Proof. exact (EQ_MP (@lem4004059 A B y''' _46078 _46079) (@lem4003244 A B _46078 _46079 x''' y''' h1)). Qed.
Lemma lem4004064 {A B : Type'} (_46078 : A -> B) (_46079 : A -> Prop) (x''' : type529 A B) (y''' : type529 A B) (h1 : term568 A B x''' y''') : term1105 A B y''' _46078 _46079.
Proof. exact (@lem4004063 A B _46078 _46079 x''' y''' h1). Qed.
Lemma lem4004065 {A B : Type'} (f : A -> B) (s : A -> Prop) (x''' : type529 A B) (y''' : type529 A B) (h1 : term568 A B x''' y''') : term1105 A B y''' f s.
Proof. exact (@lem4004064 A B f s x''' y''' h1). Qed.
Lemma lem4004068 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term568 A B x''' y''') (h2 : term1085 A B f s) (h3 : term150 A B f s n) : term989 A B y''' f s.
Proof. exact (@lem4004065 A B f s x''' y''' h1 (@lem4004061 A B f s n h2 h3)). Qed.
Lemma lem4004069 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term568 A B x''' y''') (h2 : term1085 A B f s) (h3 : term150 A B f s n) : term1106 A B y''' f s.
Proof. exact (fun h0 : term1107 A B y''' f s => @lem4004068 A B x''' y''' f s n h1 h2 h3). Qed.
Lemma lem4004071 (p : Prop) : (term1089 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4004072 {A B : Type'} (y''' : type529 A B) (f : A -> B) (s : A -> Prop) : (term1106 A B y''' f s) = (term989 A B y''' f s).
Proof. exact (@lem4004071 (term989 A B y''' f s)). Qed.
Lemma lem4004073 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term568 A B x''' y''') (h2 : term1085 A B f s) (h3 : term150 A B f s n) : term989 A B y''' f s.
Proof. exact (EQ_MP (@lem4004072 A B y''' f s) (@lem4004069 A B x''' y''' f s n h1 h2 h3)). Qed.
Lemma lem4004075 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term150 A B f s n) : @I ((A -> Prop) -> Prop) (@FINITE A) s.
Proof. exact (proj1 (@lem4002367 A B f s n h1)). Qed.
Lemma lem4004076 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term150 A B f s n) : term1088 A s.
Proof. exact (fun h0 : term972 A s => @lem4004075 A B f s n h1). Qed.
Lemma lem4004078 (p : Prop) : (term1089 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4004079 {A : Type'} (s : A -> Prop) : (term1088 A s) = (@I ((A -> Prop) -> Prop) (@FINITE A) s).
Proof. exact (@lem4004078 (@I ((A -> Prop) -> Prop) (@FINITE A) s)). Qed.
Lemma lem4004080 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term150 A B f s n) : @I ((A -> Prop) -> Prop) (@FINITE A) s.
Proof. exact (EQ_MP (@lem4004079 A s) (@lem4004076 A B f s n h1)). Qed.
Lemma lem4004083 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term1085 A B f s) : term1085 A B f s.
Proof. exact (h1). Qed.
Lemma lem4004084 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term1085 A B f s) : term1090 A B f s.
Proof. exact (fun h0 : (term969 A B f s) = (@I ((A -> Prop) -> nat) (@CARD A) s) => @lem4004083 A B f s h1). Qed.
Lemma lem4004086 (p : Prop) : (term1091 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4004087 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term1090 A B f s) = (term1085 A B f s).
Proof. exact (@lem4004086 ((term969 A B f s) = (@I ((A -> Prop) -> nat) (@CARD A) s))). Qed.
Lemma lem4004088 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term1085 A B f s) : term1085 A B f s.
Proof. exact (EQ_MP (@lem4004087 A B f s) (@lem4004084 A B f s h1)). Qed.
Lemma lem4004090 (b : Prop) (a : Prop) : (a \/ b) = (term1092 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4004091 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (_46078 : A -> B) (_46079 : A -> Prop) : (term1079 A B x''' y''' _46078 _46079) = (term1108 A B x''' y''' _46078 _46079).
Proof. exact (@lem4004090 (term1094 A B _46078 _46079) (term977 A B x''' y''' _46078 _46079)). Qed.
Lemma lem4004093 (a : Prop) (b : Prop) : (term1095 a b) = (term1096 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4004094 {A B : Type'} (_46078 : A -> B) (_46079 : A -> Prop) : (term1097 A B _46078 _46079) = (term1098 A B _46078 _46079).
Proof. exact (@lem4004093 (term972 A _46079) ((term969 A B _46078 _46079) = (@I ((A -> Prop) -> nat) (@CARD A) _46079))). Qed.
Lemma lem4004096 (a : Prop) : (term1099 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4004097 {A : Type'} (_46079 : A -> Prop) : (term1100 A _46079) = (@I ((A -> Prop) -> Prop) (@FINITE A) _46079).
Proof. exact (@lem4004096 (@I ((A -> Prop) -> Prop) (@FINITE A) _46079)). Qed.
Lemma lem4004098 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4004099 {A : Type'} (_46079 : A -> Prop) : (term1101 A _46079) = (term1017 A _46079).
Proof. exact (MK_COMB (@lem4004098) (@lem4004097 A _46079)). Qed.
Lemma lem4004100 {A B : Type'} (_46078 : A -> B) (_46079 : A -> Prop) : (term1085 A B _46078 _46079) = (term1085 A B _46078 _46079).
Proof. exact (eq_refl (term1085 A B _46078 _46079)). Qed.
Lemma lem4004101 {A B : Type'} (_46078 : A -> B) (_46079 : A -> Prop) : (term1098 A B _46078 _46079) = (term1102 A B _46078 _46079).
Proof. exact (MK_COMB (@lem4004099 A _46079) (@lem4004100 A B _46078 _46079)). Qed.
Lemma lem4004102 {A B : Type'} (_46078 : A -> B) (_46079 : A -> Prop) : (term1097 A B _46078 _46079) = (term1102 A B _46078 _46079).
Proof. exact (TRANS (@lem4004094 A B _46078 _46079) (@lem4004101 A B _46078 _46079)). Qed.
Lemma lem4004103 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4004104 {A B : Type'} (_46078 : A -> B) (_46079 : A -> Prop) : (term1103 A B _46078 _46079) = (term1104 A B _46078 _46079).
Proof. exact (MK_COMB (@lem4004103) (@lem4004102 A B _46078 _46079)). Qed.
Lemma lem4004105 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (_46078 : A -> B) (_46079 : A -> Prop) : (term977 A B x''' y''' _46078 _46079) = (term977 A B x''' y''' _46078 _46079).
Proof. exact (eq_refl (term977 A B x''' y''' _46078 _46079)). Qed.
Lemma lem4004106 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (_46078 : A -> B) (_46079 : A -> Prop) : (term1108 A B x''' y''' _46078 _46079) = (term1109 A B x''' y''' _46078 _46079).
Proof. exact (MK_COMB (@lem4004104 A B _46078 _46079) (@lem4004105 A B x''' y''' _46078 _46079)). Qed.
Lemma lem4004107 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (_46078 : A -> B) (_46079 : A -> Prop) : (term1079 A B x''' y''' _46078 _46079) = (term1109 A B x''' y''' _46078 _46079).
Proof. exact (TRANS (@lem4004091 A B x''' y''' _46078 _46079) (@lem4004106 A B x''' y''' _46078 _46079)). Qed.
Lemma lem4004109 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term1085 A B f s) (h2 : term150 A B f s n) : term1102 A B f s.
Proof. exact (conj (@lem4004080 A B f s n h2) (@lem4004088 A B f s h1)). Qed.
Lemma lem4004111 {A B : Type'} (_46078 : A -> B) (_46079 : A -> Prop) (x''' : type529 A B) (y''' : type529 A B) (h1 : term568 A B x''' y''') : term1109 A B x''' y''' _46078 _46079.
Proof. exact (EQ_MP (@lem4004107 A B x''' y''' _46078 _46079) (@lem4003216 A B _46078 _46079 x''' y''' h1)). Qed.
Lemma lem4004112 {A B : Type'} (_46078 : A -> B) (_46079 : A -> Prop) (x''' : type529 A B) (y''' : type529 A B) (h1 : term568 A B x''' y''') : term1109 A B x''' y''' _46078 _46079.
Proof. exact (@lem4004111 A B _46078 _46079 x''' y''' h1). Qed.
Lemma lem4004113 {A B : Type'} (f : A -> B) (s : A -> Prop) (x''' : type529 A B) (y''' : type529 A B) (h1 : term568 A B x''' y''') : term1109 A B x''' y''' f s.
Proof. exact (@lem4004112 A B f s x''' y''' h1). Qed.
Lemma lem4004116 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term568 A B x''' y''') (h2 : term1085 A B f s) (h3 : term150 A B f s n) : term977 A B x''' y''' f s.
Proof. exact (@lem4004113 A B f s x''' y''' h1 (@lem4004109 A B f s n h2 h3)). Qed.
Lemma lem4004117 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term568 A B x''' y''') (h2 : term1085 A B f s) (h3 : term150 A B f s n) : term1110 A B x''' y''' f s.
Proof. exact (fun h0 : (term973 A B x''' f s) = (term973 A B y''' f s) => @lem4004116 A B x''' y''' f s n h1 h2 h3). Qed.
Lemma lem4004119 (p : Prop) : (term1091 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4004120 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (f : A -> B) (s : A -> Prop) : (term1110 A B x''' y''' f s) = (term977 A B x''' y''' f s).
Proof. exact (@lem4004119 ((term973 A B x''' f s) = (term973 A B y''' f s))). Qed.
Lemma lem4004121 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term568 A B x''' y''') (h2 : term1085 A B f s) (h3 : term150 A B f s n) : term977 A B x''' y''' f s.
Proof. exact (EQ_MP (@lem4004120 A B x''' y''' f s) (@lem4004117 A B x''' y''' f s n h1 h2 h3)). Qed.
Lemma lem4004137 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4004138 {A B : Type'} (f : A -> B) (s : A -> Prop) (_46082 : A) (_46083 : A) : (term1077 A B s f _46082 _46083) = (term1111 A B f s _46082 _46083).
Proof. exact (@lem4004137 (term1022 A B _46082 f _46083) (term1025 A _46083 s) (_46082 = _46083)). Qed.
Lemma lem4004154 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4004155 {A : Type'} (_46082 : A) (_46083 : A) (s : A -> Prop) : (term1112 A s _46082 _46083) = (term1113 A _46082 _46083 s).
Proof. exact (@lem4004154 (_46082 = _46083) (term1025 A _46083 s)). Qed.
Lemma lem4004163 {A B : Type'} (_46082 : A) (f : A -> B) (_46083 : A) : (term1114 A B _46082 f _46083) = (term1114 A B _46082 f _46083).
Proof. exact (eq_refl (term1114 A B _46082 f _46083)). Qed.
Lemma lem4004164 {A B : Type'} (f : A -> B) (_46082 : A) (_46083 : A) (s : A -> Prop) : (term1111 A B f s _46082 _46083) = (term1115 A B f _46082 _46083 s).
Proof. exact (MK_COMB (@lem4004163 A B _46082 f _46083) (@lem4004155 A _46082 _46083 s)). Qed.
Lemma lem4004168 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4004169 {A B : Type'} (_46082 : A) (f : A -> B) (_46083 : A) (s : A -> Prop) : (term1115 A B f _46082 _46083 s) = (term1116 A B _46082 f _46083 s).
Proof. exact (@lem4004168 (_46082 = _46083) (term1022 A B _46082 f _46083) (term1025 A _46083 s)). Qed.
Lemma lem4004189 {A B : Type'} (_46082 : A) (f : A -> B) (_46083 : A) (s : A -> Prop) : (term1111 A B f s _46082 _46083) = (term1116 A B _46082 f _46083 s).
Proof. exact (TRANS (@lem4004164 A B f _46082 _46083 s) (@lem4004169 A B _46082 f _46083 s)). Qed.
Lemma lem4004190 {A B : Type'} (_46082 : A) (f : A -> B) (_46083 : A) (s : A -> Prop) : (term1077 A B s f _46082 _46083) = (term1116 A B _46082 f _46083 s).
Proof. exact (TRANS (@lem4004138 A B f s _46082 _46083) (@lem4004189 A B _46082 f _46083 s)). Qed.
Lemma lem4004191 {A : Type'} (_46082 : A) (s : A -> Prop) : (term1026 A _46082 s) = (term1026 A _46082 s).
Proof. exact (eq_refl (term1026 A _46082 s)). Qed.
Lemma lem4004192 {A B : Type'} (_46082 : A) (f : A -> B) (_46083 : A) (s : A -> Prop) : (term1078 A B s f _46082 _46083) = (term1117 A B _46082 f _46083 s).
Proof. exact (MK_COMB (@lem4004191 A _46082 s) (@lem4004190 A B _46082 f _46083 s)). Qed.
Lemma lem4004196 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4004197 {A B : Type'} (_46082 : A) (f : A -> B) (_46083 : A) (s : A -> Prop) : (term1117 A B _46082 f _46083 s) = (term1118 A B _46082 f _46083 s).
Proof. exact (@lem4004196 (_46082 = _46083) (term1025 A _46082 s) (term1119 A B _46082 f _46083 s)). Qed.
Lemma lem4004213 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4004214 {A B : Type'} (f : A -> B) (_46082 : A) (_46083 : A) (s : A -> Prop) : (term1120 A B _46082 f _46083 s) = (term1121 A B f _46082 _46083 s).
Proof. exact (@lem4004213 (term1022 A B _46082 f _46083) (term1025 A _46082 s) (term1025 A _46083 s)). Qed.
Lemma lem4004232 {A : Type'} (_46082 : A) (_46083 : A) : (term1122 A _46082 _46083) = (term1122 A _46082 _46083).
Proof. exact (eq_refl (term1122 A _46082 _46083)). Qed.
Lemma lem4004233 {A B : Type'} (f : A -> B) (_46082 : A) (_46083 : A) (s : A -> Prop) : (term1118 A B _46082 f _46083 s) = (term1123 A B f _46082 _46083 s).
Proof. exact (MK_COMB (@lem4004232 A _46082 _46083) (@lem4004214 A B f _46082 _46083 s)). Qed.
Lemma lem4004244 {A B : Type'} (f : A -> B) (_46082 : A) (_46083 : A) (s : A -> Prop) : (term1117 A B _46082 f _46083 s) = (term1123 A B f _46082 _46083 s).
Proof. exact (TRANS (@lem4004197 A B _46082 f _46083 s) (@lem4004233 A B f _46082 _46083 s)). Qed.
Lemma lem4004245 {A B : Type'} (f : A -> B) (_46082 : A) (_46083 : A) (s : A -> Prop) : (term1078 A B s f _46082 _46083) = (term1123 A B f _46082 _46083 s).
Proof. exact (TRANS (@lem4004192 A B _46082 f _46083 s) (@lem4004244 A B f _46082 _46083 s)). Qed.
Lemma lem4004246 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4004247 {A B : Type'} (f : A -> B) (_46082 : A) (_46083 : A) (s : A -> Prop) : (term1124 A B s f _46082 _46083) = (term1125 A B f _46082 _46083 s).
Proof. exact (MK_COMB (@lem4004246) (@lem4004245 A B f _46082 _46083 s)). Qed.
Lemma lem4004273 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4004274 {A : Type'} (_46082 : A) (_46083 : A) (s : A -> Prop) : (term1112 A s _46082 _46083) = (term1113 A _46082 _46083 s).
Proof. exact (@lem4004273 (_46082 = _46083) (term1025 A _46083 s)). Qed.
Lemma lem4004282 {A : Type'} (_46082 : A) (s : A -> Prop) : (term1026 A _46082 s) = (term1026 A _46082 s).
Proof. exact (eq_refl (term1026 A _46082 s)). Qed.
Lemma lem4004283 {A : Type'} (_46082 : A) (_46083 : A) (s : A -> Prop) : (term1126 A s _46082 _46083) = (term1127 A _46082 _46083 s).
Proof. exact (MK_COMB (@lem4004282 A _46082 s) (@lem4004274 A _46082 _46083 s)). Qed.
Lemma lem4004287 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4004288 {A : Type'} (_46082 : A) (_46083 : A) (s : A -> Prop) : (term1127 A _46082 _46083 s) = (term1128 A _46082 _46083 s).
Proof. exact (@lem4004287 (_46082 = _46083) (term1025 A _46082 s) (term1025 A _46083 s)). Qed.
Lemma lem4004306 {A : Type'} (_46082 : A) (_46083 : A) (s : A -> Prop) : (term1126 A s _46082 _46083) = (term1128 A _46082 _46083 s).
Proof. exact (TRANS (@lem4004283 A _46082 _46083 s) (@lem4004288 A _46082 _46083 s)). Qed.
Lemma lem4004307 {A B : Type'} (_46082 : A) (f : A -> B) (_46083 : A) : (term1114 A B _46082 f _46083) = (term1114 A B _46082 f _46083).
Proof. exact (eq_refl (term1114 A B _46082 f _46083)). Qed.
Lemma lem4004308 {A B : Type'} (f : A -> B) (_46082 : A) (_46083 : A) (s : A -> Prop) : (term1129 A B f s _46082 _46083) = (term1130 A B f _46082 _46083 s).
Proof. exact (MK_COMB (@lem4004307 A B _46082 f _46083) (@lem4004306 A _46082 _46083 s)). Qed.
Lemma lem4004312 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4004313 {A B : Type'} (f : A -> B) (_46082 : A) (_46083 : A) (s : A -> Prop) : (term1130 A B f _46082 _46083 s) = (term1123 A B f _46082 _46083 s).
Proof. exact (@lem4004312 (_46082 = _46083) (term1022 A B _46082 f _46083) (term1131 A _46082 _46083 s)). Qed.
Lemma lem4004343 {A B : Type'} (f : A -> B) (_46082 : A) (_46083 : A) (s : A -> Prop) : (term1129 A B f s _46082 _46083) = (term1123 A B f _46082 _46083 s).
Proof. exact (TRANS (@lem4004308 A B f _46082 _46083 s) (@lem4004313 A B f _46082 _46083 s)). Qed.
Lemma lem4004344 {A B : Type'} (f : A -> B) (_46082 : A) (_46083 : A) (s : A -> Prop) : ((term1078 A B s f _46082 _46083) = (term1129 A B f s _46082 _46083)) = ((term1123 A B f _46082 _46083 s) = (term1123 A B f _46082 _46083 s)).
Proof. exact (MK_COMB (@lem4004247 A B f _46082 _46083 s) (@lem4004343 A B f _46082 _46083 s)). Qed.
Lemma lem4004346 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4004347 (x : Prop) : (x = x) = True.
Proof. exact (@lem4004346 Prop x). Qed.
Lemma lem4004348 {A B : Type'} (f : A -> B) (_46082 : A) (_46083 : A) (s : A -> Prop) : ((term1123 A B f _46082 _46083 s) = (term1123 A B f _46082 _46083 s)) = True.
Proof. exact (@lem4004347 (term1123 A B f _46082 _46083 s)). Qed.
Lemma lem4004349 {A B : Type'} (f : A -> B) (s : A -> Prop) (_46082 : A) (_46083 : A) : ((term1078 A B s f _46082 _46083) = (term1129 A B f s _46082 _46083)) = True.
Proof. exact (TRANS (@lem4004344 A B f _46082 _46083 s) (@lem4004348 A B f _46082 _46083 s)). Qed.
Lemma lem4004350 {A B : Type'} (f : A -> B) (s : A -> Prop) (_46082 : A) (_46083 : A) : True = ((term1078 A B s f _46082 _46083) = (term1129 A B f s _46082 _46083)).
Proof. exact (SYM (@lem4004349 A B f s _46082 _46083)). Qed.
Lemma lem4004351 {A B : Type'} (f : A -> B) (s : A -> Prop) (_46082 : A) (_46083 : A) : (term1078 A B s f _46082 _46083) = (term1129 A B f s _46082 _46083).
Proof. exact (EQ_MP (@lem4004350 A B f s _46082 _46083) (@lem0)). Qed.
Lemma lem4004352 {A B : Type'} (_46082 : A) (_46083 : A) (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term150 A B f s n) : term1129 A B f s _46082 _46083.
Proof. exact (EQ_MP (@lem4004351 A B f s _46082 _46083) (@lem4003132 A B _46082 _46083 f s n h1)). Qed.
Lemma lem4004354 (b : Prop) (a : Prop) : (a \/ b) = (term1092 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4004355 {A B : Type'} (s : A -> Prop) (_46082 : A) (f : A -> B) (_46083 : A) : (term1129 A B f s _46082 _46083) = (term1132 A B s _46082 f _46083).
Proof. exact (@lem4004354 (term1126 A s _46082 _46083) (term1022 A B _46082 f _46083)). Qed.
Lemma lem4004357 (a : Prop) (b : Prop) : (term1095 a b) = (term1096 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4004358 {A : Type'} (s : A -> Prop) (_46082 : A) (_46083 : A) : (term1133 A s _46082 _46083) = (term1134 A s _46082 _46083).
Proof. exact (@lem4004357 (term1025 A _46082 s) (term1112 A s _46082 _46083)). Qed.
Lemma lem4004360 (a : Prop) : (term1099 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4004361 {A : Type'} (_46082 : A) (s : A -> Prop) : (term1135 A _46082 s) = (term1023 A _46082 s).
Proof. exact (@lem4004360 (term1023 A _46082 s)). Qed.
Lemma lem4004362 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4004363 {A : Type'} (_46082 : A) (s : A -> Prop) : (term1136 A _46082 s) = (term1137 A _46082 s).
Proof. exact (MK_COMB (@lem4004362) (@lem4004361 A _46082 s)). Qed.
Lemma lem4004365 (a : Prop) (b : Prop) : (term1095 a b) = (term1096 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4004366 {A : Type'} (s : A -> Prop) (_46082 : A) (_46083 : A) : (term1138 A s _46082 _46083) = (term1139 A s _46082 _46083).
Proof. exact (@lem4004365 (term1025 A _46083 s) (_46082 = _46083)). Qed.
Lemma lem4004368 (a : Prop) : (term1099 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4004369 {A : Type'} (_46083 : A) (s : A -> Prop) : (term1135 A _46083 s) = (term1023 A _46083 s).
Proof. exact (@lem4004368 (term1023 A _46083 s)). Qed.
Lemma lem4004370 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4004371 {A : Type'} (_46083 : A) (s : A -> Prop) : (term1136 A _46083 s) = (term1137 A _46083 s).
Proof. exact (MK_COMB (@lem4004370) (@lem4004369 A _46083 s)). Qed.
Lemma lem4004372 {A : Type'} (_46082 : A) (_46083 : A) : (term1140 A _46082 _46083) = (term1140 A _46082 _46083).
Proof. exact (eq_refl (term1140 A _46082 _46083)). Qed.
Lemma lem4004373 {A : Type'} (s : A -> Prop) (_46082 : A) (_46083 : A) : (term1139 A s _46082 _46083) = (term1141 A s _46082 _46083).
Proof. exact (MK_COMB (@lem4004371 A _46083 s) (@lem4004372 A _46082 _46083)). Qed.
Lemma lem4004374 {A : Type'} (s : A -> Prop) (_46082 : A) (_46083 : A) : (term1138 A s _46082 _46083) = (term1141 A s _46082 _46083).
Proof. exact (TRANS (@lem4004366 A s _46082 _46083) (@lem4004373 A s _46082 _46083)). Qed.
Lemma lem4004375 {A : Type'} (s : A -> Prop) (_46082 : A) (_46083 : A) : (term1134 A s _46082 _46083) = (term1142 A s _46082 _46083).
Proof. exact (MK_COMB (@lem4004363 A _46082 s) (@lem4004374 A s _46082 _46083)). Qed.
Lemma lem4004376 {A : Type'} (s : A -> Prop) (_46082 : A) (_46083 : A) : (term1133 A s _46082 _46083) = (term1142 A s _46082 _46083).
Proof. exact (TRANS (@lem4004358 A s _46082 _46083) (@lem4004375 A s _46082 _46083)). Qed.
Lemma lem4004377 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4004378 {A : Type'} (s : A -> Prop) (_46082 : A) (_46083 : A) : (term1143 A s _46082 _46083) = (term1144 A s _46082 _46083).
Proof. exact (MK_COMB (@lem4004377) (@lem4004376 A s _46082 _46083)). Qed.
Lemma lem4004379 {A B : Type'} (_46082 : A) (f : A -> B) (_46083 : A) : (term1022 A B _46082 f _46083) = (term1022 A B _46082 f _46083).
Proof. exact (eq_refl (term1022 A B _46082 f _46083)). Qed.
Lemma lem4004380 {A B : Type'} (s : A -> Prop) (_46082 : A) (f : A -> B) (_46083 : A) : (term1132 A B s _46082 f _46083) = (term1145 A B s _46082 f _46083).
Proof. exact (MK_COMB (@lem4004378 A s _46082 _46083) (@lem4004379 A B _46082 f _46083)). Qed.
Lemma lem4004381 {A B : Type'} (s : A -> Prop) (_46082 : A) (f : A -> B) (_46083 : A) : (term1129 A B f s _46082 _46083) = (term1145 A B s _46082 f _46083).
Proof. exact (TRANS (@lem4004355 A B s _46082 f _46083) (@lem4004380 A B s _46082 f _46083)). Qed.
Lemma lem4004383 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term568 A B x''' y''') (h2 : term1085 A B f s) (h3 : term150 A B f s n) : term1146 A B x''' y''' f s.
Proof. exact (conj (@lem4004073 A B x''' y''' f s n h1 h2 h3) (@lem4004121 A B x''' y''' f s n h1 h2 h3)). Qed.
Lemma lem4004384 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term568 A B x''' y''') (h2 : term1085 A B f s) (h3 : term150 A B f s n) : term1147 A B x''' y''' f s.
Proof. exact (conj (@lem4004025 A B x''' y''' f s n h1 h2 h3) (@lem4004383 A B x''' y''' f s n h1 h2 h3)). Qed.
Lemma lem4004386 {A B : Type'} (_46082 : A) (_46083 : A) (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term150 A B f s n) : term1145 A B s _46082 f _46083.
Proof. exact (EQ_MP (@lem4004381 A B s _46082 f _46083) (@lem4004352 A B _46082 _46083 f s n h1)). Qed.
Lemma lem4004387 {A B : Type'} (_46082 : A) (_46083 : A) (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term150 A B f s n) : term1145 A B s _46082 f _46083.
Proof. exact (@lem4004386 A B _46082 _46083 f s n h1). Qed.
Lemma lem4004388 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term150 A B f s n) : term1148 A B x''' y''' f s.
Proof. exact (@lem4004387 A B (term973 A B x''' f s) (term973 A B y''' f s) f s n h1). Qed.
Lemma lem4004391 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term568 A B x''' y''') (h2 : term1085 A B f s) (h3 : term150 A B f s n) : term1149 A B x''' y''' f s.
Proof. exact (@lem4004388 A B x''' y''' f s n h3 (@lem4004384 A B x''' y''' f s n h1 h2 h3)). Qed.
Lemma lem4004392 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term568 A B x''' y''') (h2 : term1085 A B f s) (h3 : term150 A B f s n) : term1150 A B x''' y''' f s.
Proof. exact (fun h0 : (term980 A B x''' f s) = (term980 A B y''' f s) => @lem4004391 A B x''' y''' f s n h1 h2 h3). Qed.
Lemma lem4004394 (p : Prop) : (term1091 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4004395 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (f : A -> B) (s : A -> Prop) : (term1150 A B x''' y''' f s) = (term1149 A B x''' y''' f s).
Proof. exact (@lem4004394 ((term980 A B x''' f s) = (term980 A B y''' f s))). Qed.
Lemma lem4004396 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term568 A B x''' y''') (h2 : term1085 A B f s) (h3 : term150 A B f s n) : term1149 A B x''' y''' f s.
Proof. exact (EQ_MP (@lem4004395 A B x''' y''' f s) (@lem4004392 A B x''' y''' f s n h1 h2 h3)). Qed.
Lemma lem4004398 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term150 A B f s n) : @I ((A -> Prop) -> Prop) (@FINITE A) s.
Proof. exact (proj1 (@lem4002367 A B f s n h1)). Qed.
Lemma lem4004399 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term150 A B f s n) : term1088 A s.
Proof. exact (fun h0 : term972 A s => @lem4004398 A B f s n h1). Qed.
Lemma lem4004401 (p : Prop) : (term1089 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4004402 {A : Type'} (s : A -> Prop) : (term1088 A s) = (@I ((A -> Prop) -> Prop) (@FINITE A) s).
Proof. exact (@lem4004401 (@I ((A -> Prop) -> Prop) (@FINITE A) s)). Qed.
Lemma lem4004403 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term150 A B f s n) : @I ((A -> Prop) -> Prop) (@FINITE A) s.
Proof. exact (EQ_MP (@lem4004402 A s) (@lem4004399 A B f s n h1)). Qed.
Lemma lem4004421 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4004422 {A B : Type'} (_46078 : A -> B) (_46079 : A -> Prop) : (term1094 A B _46078 _46079) = (term1151 A B _46078 _46079).
Proof. exact (@lem4004421 ((term969 A B _46078 _46079) = (@I ((A -> Prop) -> nat) (@CARD A) _46079)) (term972 A _46079)). Qed.
Lemma lem4004430 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (_46078 : A -> B) (_46079 : A -> Prop) : (term1152 A B x''' y''' _46078 _46079) = (term1152 A B x''' y''' _46078 _46079).
Proof. exact (eq_refl (term1152 A B x''' y''' _46078 _46079)). Qed.
Lemma lem4004431 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (_46078 : A -> B) (_46079 : A -> Prop) : (term1081 A B x''' y''' _46078 _46079) = (term1153 A B x''' y''' _46078 _46079).
Proof. exact (MK_COMB (@lem4004430 A B x''' y''' _46078 _46079) (@lem4004422 A B _46078 _46079)). Qed.
Lemma lem4004442 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4004443 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (_46078 : A -> B) (_46079 : A -> Prop) : (term1154 A B x''' y''' _46078 _46079) = (term1155 A B x''' y''' _46078 _46079).
Proof. exact (MK_COMB (@lem4004442) (@lem4004431 A B x''' y''' _46078 _46079)). Qed.
Lemma lem4004447 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4004448 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (_46078 : A -> B) (_46079 : A -> Prop) : (term1156 A B x''' y''' _46078 _46079) = (term1153 A B x''' y''' _46078 _46079).
Proof. exact (@lem4004447 ((term980 A B x''' _46078 _46079) = (term980 A B y''' _46078 _46079)) ((term969 A B _46078 _46079) = (@I ((A -> Prop) -> nat) (@CARD A) _46079)) (term972 A _46079)). Qed.
Lemma lem4004468 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (_46078 : A -> B) (_46079 : A -> Prop) : ((term1081 A B x''' y''' _46078 _46079) = (term1156 A B x''' y''' _46078 _46079)) = ((term1153 A B x''' y''' _46078 _46079) = (term1153 A B x''' y''' _46078 _46079)).
Proof. exact (MK_COMB (@lem4004443 A B x''' y''' _46078 _46079) (@lem4004448 A B x''' y''' _46078 _46079)). Qed.
Lemma lem4004470 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4004471 (x : Prop) : (x = x) = True.
Proof. exact (@lem4004470 Prop x). Qed.
Lemma lem4004472 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (_46078 : A -> B) (_46079 : A -> Prop) : ((term1153 A B x''' y''' _46078 _46079) = (term1153 A B x''' y''' _46078 _46079)) = True.
Proof. exact (@lem4004471 (term1153 A B x''' y''' _46078 _46079)). Qed.
Lemma lem4004473 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (_46078 : A -> B) (_46079 : A -> Prop) : ((term1081 A B x''' y''' _46078 _46079) = (term1156 A B x''' y''' _46078 _46079)) = True.
Proof. exact (TRANS (@lem4004468 A B x''' y''' _46078 _46079) (@lem4004472 A B x''' y''' _46078 _46079)). Qed.
Lemma lem4004474 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (_46078 : A -> B) (_46079 : A -> Prop) : True = ((term1081 A B x''' y''' _46078 _46079) = (term1156 A B x''' y''' _46078 _46079)).
Proof. exact (SYM (@lem4004473 A B x''' y''' _46078 _46079)). Qed.
Lemma lem4004475 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (_46078 : A -> B) (_46079 : A -> Prop) : (term1081 A B x''' y''' _46078 _46079) = (term1156 A B x''' y''' _46078 _46079).
Proof. exact (EQ_MP (@lem4004474 A B x''' y''' _46078 _46079) (@lem0)). Qed.
Lemma lem4004476 {A B : Type'} (_46078 : A -> B) (_46079 : A -> Prop) (x''' : type529 A B) (y''' : type529 A B) (h1 : term568 A B x''' y''') : term1156 A B x''' y''' _46078 _46079.
Proof. exact (EQ_MP (@lem4004475 A B x''' y''' _46078 _46079) (@lem4003258 A B _46078 _46079 x''' y''' h1)). Qed.
Lemma lem4004478 (b : Prop) (a : Prop) : (a \/ b) = (term1092 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4004479 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (_46078 : A -> B) (_46079 : A -> Prop) : (term1156 A B x''' y''' _46078 _46079) = (term1157 A B x''' y''' _46078 _46079).
Proof. exact (@lem4004478 (term1059 A B x''' y''' _46078 _46079) ((term969 A B _46078 _46079) = (@I ((A -> Prop) -> nat) (@CARD A) _46079))). Qed.
Lemma lem4004481 (a : Prop) (b : Prop) : (term1095 a b) = (term1096 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4004482 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (_46078 : A -> B) (_46079 : A -> Prop) : (term1158 A B x''' y''' _46078 _46079) = (term1159 A B x''' y''' _46078 _46079).
Proof. exact (@lem4004481 ((term980 A B x''' _46078 _46079) = (term980 A B y''' _46078 _46079)) (term972 A _46079)). Qed.
Lemma lem4004484 (a : Prop) : (term1099 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4004485 {A : Type'} (_46079 : A -> Prop) : (term1100 A _46079) = (@I ((A -> Prop) -> Prop) (@FINITE A) _46079).
Proof. exact (@lem4004484 (@I ((A -> Prop) -> Prop) (@FINITE A) _46079)). Qed.
Lemma lem4004486 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (_46078 : A -> B) (_46079 : A -> Prop) : (term1160 A B x''' y''' _46078 _46079) = (term1160 A B x''' y''' _46078 _46079).
Proof. exact (eq_refl (term1160 A B x''' y''' _46078 _46079)). Qed.
Lemma lem4004487 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (_46078 : A -> B) (_46079 : A -> Prop) : (term1159 A B x''' y''' _46078 _46079) = (term1161 A B x''' y''' _46078 _46079).
Proof. exact (MK_COMB (@lem4004486 A B x''' y''' _46078 _46079) (@lem4004485 A _46079)). Qed.
Lemma lem4004488 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (_46078 : A -> B) (_46079 : A -> Prop) : (term1158 A B x''' y''' _46078 _46079) = (term1161 A B x''' y''' _46078 _46079).
Proof. exact (TRANS (@lem4004482 A B x''' y''' _46078 _46079) (@lem4004487 A B x''' y''' _46078 _46079)). Qed.
Lemma lem4004489 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4004490 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (_46078 : A -> B) (_46079 : A -> Prop) : (term1162 A B x''' y''' _46078 _46079) = (term1163 A B x''' y''' _46078 _46079).
Proof. exact (MK_COMB (@lem4004489) (@lem4004488 A B x''' y''' _46078 _46079)). Qed.
Lemma lem4004491 {A B : Type'} (_46078 : A -> B) (_46079 : A -> Prop) : ((term969 A B _46078 _46079) = (@I ((A -> Prop) -> nat) (@CARD A) _46079)) = ((term969 A B _46078 _46079) = (@I ((A -> Prop) -> nat) (@CARD A) _46079)).
Proof. exact (eq_refl ((term969 A B _46078 _46079) = (@I ((A -> Prop) -> nat) (@CARD A) _46079))). Qed.
Lemma lem4004492 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (_46078 : A -> B) (_46079 : A -> Prop) : (term1157 A B x''' y''' _46078 _46079) = (term1164 A B x''' y''' _46078 _46079).
Proof. exact (MK_COMB (@lem4004490 A B x''' y''' _46078 _46079) (@lem4004491 A B _46078 _46079)). Qed.
Lemma lem4004493 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (_46078 : A -> B) (_46079 : A -> Prop) : (term1156 A B x''' y''' _46078 _46079) = (term1164 A B x''' y''' _46078 _46079).
Proof. exact (TRANS (@lem4004479 A B x''' y''' _46078 _46079) (@lem4004492 A B x''' y''' _46078 _46079)). Qed.
Lemma lem4004495 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term568 A B x''' y''') (h2 : term1085 A B f s) (h3 : term150 A B f s n) : term1161 A B x''' y''' f s.
Proof. exact (conj (@lem4004396 A B x''' y''' f s n h1 h2 h3) (@lem4004403 A B f s n h3)). Qed.
Lemma lem4004497 {A B : Type'} (_46078 : A -> B) (_46079 : A -> Prop) (x''' : type529 A B) (y''' : type529 A B) (h1 : term568 A B x''' y''') : term1164 A B x''' y''' _46078 _46079.
Proof. exact (EQ_MP (@lem4004493 A B x''' y''' _46078 _46079) (@lem4004476 A B _46078 _46079 x''' y''' h1)). Qed.
Lemma lem4004498 {A B : Type'} (_46078 : A -> B) (_46079 : A -> Prop) (x''' : type529 A B) (y''' : type529 A B) (h1 : term568 A B x''' y''') : term1164 A B x''' y''' _46078 _46079.
Proof. exact (@lem4004497 A B _46078 _46079 x''' y''' h1). Qed.
Lemma lem4004499 {A B : Type'} (f : A -> B) (s : A -> Prop) (x''' : type529 A B) (y''' : type529 A B) (h1 : term568 A B x''' y''') : term1164 A B x''' y''' f s.
Proof. exact (@lem4004498 A B f s x''' y''' h1). Qed.
Lemma lem4004502 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term568 A B x''' y''') (h2 : term1085 A B f s) (h3 : term150 A B f s n) : (term969 A B f s) = (@I ((A -> Prop) -> nat) (@CARD A) s).
Proof. exact (@lem4004499 A B f s x''' y''' h1 (@lem4004495 A B x''' y''' f s n h1 h2 h3)). Qed.
Lemma lem4004503 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term568 A B x''' y''') (h2 : term150 A B f s n) : term1165 A B f s.
Proof. exact (fun h0 : term1085 A B f s => @lem4004502 A B x''' y''' f s n h1 h0 h2). Qed.
Lemma lem4004505 (p : Prop) : (term1089 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4004506 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term1165 A B f s) = ((term969 A B f s) = (@I ((A -> Prop) -> nat) (@CARD A) s)).
Proof. exact (@lem4004505 ((term969 A B f s) = (@I ((A -> Prop) -> nat) (@CARD A) s))). Qed.
Lemma lem4004507 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term568 A B x''' y''') (h2 : term150 A B f s n) : (term969 A B f s) = (@I ((A -> Prop) -> nat) (@CARD A) s).
Proof. exact (EQ_MP (@lem4004506 A B f s) (@lem4004503 A B x''' y''' f s n h1 h2)). Qed.
Lemma lem4004510 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4004512 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term1085 A B f s) = (term1166 A B f s).
Proof. exact (@lem4004510 ((term969 A B f s) = (@I ((A -> Prop) -> nat) (@CARD A) s))). Qed.
Lemma lem4004515 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term150 A B f s n) : term1166 A B f s.
Proof. exact (EQ_MP (@lem4004512 A B f s) (@lem4003118 A B f s n h1)). Qed.
Lemma lem4004518 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term568 A B x''' y''') (h2 : term150 A B f s n) : False.
Proof. exact (@lem4004515 A B f s n h2 (@lem4004507 A B x''' y''' f s n h1 h2)). Qed.
Lemma lem4004519 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term568 A B x''' y''') (h2 : term150 A B f s n) : term1167.
Proof. exact (fun h0 : ~ False => @lem4004518 A B x''' y''' f s n h1 h2). Qed.
Lemma lem4004521 (p : Prop) : (term1089 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4004522 : term1167 = False.
Proof. exact (@lem4004521 False). Qed.
Lemma lem4004524 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term568 A B x''' y''') (h2 : term150 A B f s n) : False.
Proof. exact (EQ_MP (@lem4004522) (@lem4004519 A B x''' y''' f s n h1 h2)). Qed.
Lemma lem4004525 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (f : A -> B) (s : A -> Prop) (h1 : term568 A B x''' y''') (h2 : term160 A B f s) : False.
Proof. exact (ex_elim (@lem4001110 A B f s h2) (fun n : nat => fun h0 : term159 A B f s n => @lem4004524 A B x''' y''' f s n h1 h0)). Qed.
Lemma lem4004526 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (f : A -> B) (h1 : term568 A B x''' y''') (h2 : term169 A B f) : False.
Proof. exact (ex_elim (@lem4001109 A B f h2) (fun s : A -> Prop => fun h0 : term168 A B f s => @lem4004525 A B x''' y''' f s h1 h0)). Qed.
Lemma lem4004527 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (h1 : term568 A B x''' y''') (h2 : term53 A B) : False.
Proof. exact (ex_elim (@lem3999068 A B h2) (fun f : A -> B => fun h0 : term176 A B f => @lem4004526 A B x''' y''' f h1 h0)). Qed.
Lemma lem4004528 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (x'''' : type485 A) (h1 : term568 A B x''' y''') (h2 : term378 A x'''') (h3 : term53 A B) : False.
Proof. exact (ex_elim (@lem4001107 A x'''' h2) (fun y'''' : type485 A => fun h0 : term377 A x'''' y'''' => @lem4004527 A B x''' y''' h1 h3)). Qed.
Lemma lem4004529 {A B : Type'} (x''' : type529 A B) (y''' : type529 A B) (h1 : term55 A) (h2 : term568 A B x''' y''') (h3 : term53 A B) : False.
Proof. exact (ex_elim (@lem3999474 A h1) (fun x'''' : type485 A => fun h0 : term379 A x'''' => @lem4004528 A B x''' y''' x'''' h2 h0 h3)). Qed.
Lemma lem4004530 {A B : Type'} (x''' : type529 A B) (h1 : term55 A) (h2 : term571 A B x''') (h3 : term53 A B) : False.
Proof. exact (ex_elim (@lem4001105 A B x''' h2) (fun y''' : type529 A B => fun h0 : term570 A B x''' y''' => @lem4004529 A B x''' y''' h1 h0 h3)). Qed.
Lemma lem4004531 {A B : Type'} (h1 : term55 A) (h2 : term54 A B) (h3 : term53 A B) : False.
Proof. exact (ex_elim (@lem3999880 A B h2) (fun x''' : type529 A B => fun h0 : term572 A B x''' => @lem4004530 A B x''' h1 h0 h3)). Qed.
Lemma lem4004532 {A B : Type'} (x'' : type694 A) (h1 : term55 A) (h2 : term54 A B) (h3 : term765 A x'') (h4 : term53 A B) : False.
Proof. exact (ex_elim (@lem4001103 A x'' h3) (fun y'' : type694 A => fun h0 : term764 A x'' y'' => @lem4004531 A B h1 h2 h4)). Qed.
Lemma lem4004533 {A B : Type'} (h1 : term55 A) (h2 : term54 A B) (h3 : term56 A) (h4 : term53 A B) : False.
Proof. exact (ex_elim (@lem4000286 A h3) (fun x'' : type694 A => fun h0 : term766 A x'' => @lem4004532 A B x'' h1 h2 h0 h4)). Qed.
Lemma lem4004534 {A B : Type'} (x' : type485 B) (h1 : term55 A) (h2 : term54 A B) (h3 : term56 A) (h4 : term378 B x') (h5 : term53 A B) : False.
Proof. exact (ex_elim (@lem4001101 B x' h4) (fun y' : type485 B => fun h0 : term377 B x' y' => @lem4004533 A B h1 h2 h3 h5)). Qed.
Lemma lem4004535 {A B : Type'} (h1 : term55 A) (h2 : term54 A B) (h3 : term56 A) (h4 : term55 B) (h5 : term53 A B) : False.
Proof. exact (ex_elim (@lem4000692 B h4) (fun x' : type485 B => fun h0 : term379 B x' => @lem4004534 A B x' h1 h2 h3 h0 h5)). Qed.
Lemma lem4004536 {A B : Type'} (x : type969 B) (h1 : term55 A) (h2 : term54 A B) (h3 : term56 A) (h4 : term55 B) (h5 : term964 B x) (h6 : term53 A B) : False.
Proof. exact (ex_elim (@lem4001099 B x h5) (fun y : type969 B => fun h0 : term963 B x y => @lem4004535 A B h1 h2 h3 h4 h6)). Qed.
Lemma lem4004537 {A B : Type'} (h1 : term55 A) (h2 : term54 A B) (h3 : term56 A) (h4 : term55 B) (h5 : term57 B) (h6 : term53 A B) : False.
Proof. exact (ex_elim (@lem4001098 B h5) (fun x : type969 B => fun h0 : term965 B x => @lem4004536 A B x h1 h2 h3 h4 h0 h6)). Qed.
Lemma lem4004538 {A B : Type'} (h1 : term55 A) (h2 : term54 A B) (h3 : term56 A) (h4 : term55 B) (h5 : term53 A B) : term62 B.
Proof. exact (fun h0 : term57 B => @lem4004537 A B h1 h2 h3 h4 h0 h5). Qed.
Lemma lem4004539 {B : Type'} : (term62 B) = (term63 B).
Proof. exact (@lem69 (term57 B)). Qed.
Lemma lem4004540 {A B : Type'} (h1 : term55 A) (h2 : term54 A B) (h3 : term56 A) (h4 : term55 B) (h5 : term53 A B) : term63 B.
Proof. exact (EQ_MP (@lem4004539 B) (@lem4004538 A B h1 h2 h3 h4 h5)). Qed.
Lemma lem4004541 {A B : Type'} (h1 : term55 A) (h2 : term54 A B) (h3 : term56 A) (h4 : term53 A B) : term66 B.
Proof. exact (fun h0 : term55 B => @lem4004540 A B h1 h2 h3 h0 h4). Qed.
Lemma lem4004542 {A B : Type'} (h1 : term55 A) (h2 : term54 A B) (h3 : term53 A B) : term69 A B.
Proof. exact (fun h0 : term56 A => @lem4004541 A B h1 h2 h0 h3). Qed.
Lemma lem4004543 {A B : Type'} (h1 : term55 A) (h2 : term53 A B) : term72 A B.
Proof. exact (fun h0 : term54 A B => @lem4004542 A B h1 h0 h2). Qed.
Lemma lem4004544 {A B : Type'} (h1 : term53 A B) : term74 A B.
Proof. exact (fun h0 : term55 A => @lem4004543 A B h0 h1). Qed.
Lemma lem4004545 {A B : Type'} : term76 A B.
Proof. exact (fun h0 : term53 A B => @lem4004544 A B h0). Qed.
Lemma lem4004546 {A B : Type'} : term58 A B.
Proof. exact (EQ_MP (@lem3998880 A B) (@lem4004545 A B)). Qed.
Lemma lem4004548 {A B : Type'} : term58 A B.
Proof. exact (@lem3998231 A B (@lem4004546 A B)). Qed.
Lemma lem4004549 {A B : Type'} (h1 : term53 A B) : term73 A B.
Proof. exact (@lem4004548 A B (@lem3998202 A B h1)). Qed.
Lemma lem4004550 {A B : Type'} (h1 : term53 A B) : term71 A B.
Proof. exact (@lem4004549 A B h1 (@lem3998205 A)). Qed.
Lemma lem4004551 {A B : Type'} (h1 : term53 A B) : term68 A B.
Proof. exact (@lem4004550 A B h1 (@lem3998203 A B)). Qed.
Lemma lem4004552 {A B : Type'} (h1 : term53 A B) : term65 B.
Proof. exact (@lem4004551 A B h1 (@lem3998206 A)). Qed.
Lemma lem4004553 {A B : Type'} (h1 : term53 A B) : term62 B.
Proof. exact (@lem4004552 A B h1 (@lem3998207 B)). Qed.
Lemma lem4004554 {A B : Type'} (h1 : term53 A B) : False.
Proof. exact (@lem4004553 A B h1 (@lem3998209 B)). Qed.
Lemma lem4004555 {A B : Type'} (h1 : term53 A B) : (term53 A B) = False.
Proof. exact (prop_ext (fun h2 : term53 A B => @lem4004554 A B h1) (fun h2 : False => @lem3998202 A B h1)). Qed.
Lemma lem4004556 {A B : Type'} (h1 : term53 A B) : False.
Proof. exact (EQ_MP (@lem4004555 A B h1) (@lem3998202 A B h1)). Qed.
Lemma lem4004557 {A B : Type'} : term52 A B.
Proof. exact (fun h0 : term53 A B => @lem4004556 A B h0). Qed.
Lemma lem4004558 {A B : Type'} : term50 A B.
Proof. exact (EQ_MP (@lem3998201 A B) (@lem4004557 A B)). Qed.
Lemma lem4004559 {A B : Type'} : term49 A B.
Proof. exact (EQ_MP (@lem3998197 A B) (@lem4004558 A B)). Qed.
