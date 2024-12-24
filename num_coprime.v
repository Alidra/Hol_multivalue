Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import num_coprime_term_abbrevs.
Require Import FST_spec.
Require Import SND_spec.
Lemma lem2838394 : num_coprime = term0.
Proof. exact (@num_coprime_def). Qed.
Lemma lem2838395 (_31172 : prod nat nat) : _31172 = _31172.
Proof. exact (eq_refl _31172). Qed.
Lemma lem2838396 (_31172 : prod nat nat) : (num_coprime _31172) = (term1 _31172).
Proof. exact (MK_COMB (@lem2838394) (@lem2838395 _31172)). Qed.
Lemma lem2838397 (_31172 : prod nat nat) : (term1 _31172) = (term2 _31172).
Proof. exact (eq_refl (term1 _31172)). Qed.
Lemma lem2838398 (_31172 : prod nat nat) : (num_coprime _31172) = (term2 _31172).
Proof. exact (TRANS (@lem2838396 _31172) (@lem2838397 _31172)). Qed.
Lemma lem2838399 : term3.
Proof. exact (fun _31172 : prod nat nat => @lem2838398 _31172). Qed.
Lemma lem2838400 (_31172 : prod nat nat) : term4 _31172.
Proof. exact (@lem2838399 _31172). Qed.
Lemma lem2838401 (_31172 : prod nat nat) : (term4 _31172) = ((num_coprime _31172) = (term2 _31172)).
Proof. exact (eq_refl (term4 _31172)). Qed.
Lemma lem2838402 (_31172 : prod nat nat) : (num_coprime _31172) = (term2 _31172).
Proof. exact (EQ_MP (@lem2838401 _31172) (@lem2838400 _31172)). Qed.
Lemma lem2838403 (a : nat) (b : nat) : (term5 a b) = (term6 a b).
Proof. exact (@lem2838402 (@pair nat nat a b)). Qed.
Lemma lem2838404 {A B : Type'} (x : A) : term7 A B x.
Proof. exact (@lem48019 A B x). Qed.
Lemma lem2838405 {A B : Type'} (x : A) : (term7 A B x) = (term8 A B x).
Proof. exact (eq_refl (term7 A B x)). Qed.
Lemma lem2838406 {A B : Type'} (x : A) : term8 A B x.
Proof. exact (EQ_MP (@lem2838405 A B x) (@lem2838404 A B x)). Qed.
Lemma lem2838407 {A B : Type'} (x : A) (y : B) : term9 A B x y.
Proof. exact (@lem2838406 A B x y). Qed.
Lemma lem2838408 {A B : Type'} (x : A) (y : B) : (term9 A B x y) = ((term10 A B x y) = y).
Proof. exact (eq_refl (term9 A B x y)). Qed.
Lemma lem2838410 {A B : Type'} (x : A) : term11 A B x.
Proof. exact (@lem47827 A B x). Qed.
Lemma lem2838411 {A B : Type'} (x : A) : (term11 A B x) = (term12 A B x).
Proof. exact (eq_refl (term11 A B x)). Qed.
Lemma lem2838412 {A B : Type'} (x : A) : term12 A B x.
Proof. exact (EQ_MP (@lem2838411 A B x) (@lem2838410 A B x)). Qed.
Lemma lem2838413 {A B : Type'} (x : A) (y : B) : term13 A B x y.
Proof. exact (@lem2838412 A B x y). Qed.
Lemma lem2838414 {A B : Type'} (y : B) (x : A) : (term13 A B x y) = ((term14 A B x y) = x).
Proof. exact (eq_refl (term13 A B x y)). Qed.
Lemma lem2838417 {A B : Type'} (y : B) (x : A) : (term14 A B x y) = x.
Proof. exact (EQ_MP (@lem2838414 A B y x) (@lem2838413 A B x y)). Qed.
Lemma lem2838418 (y : nat) (x : nat) : (term15 x y) = x.
Proof. exact (@lem2838417 nat nat y x). Qed.
Lemma lem2838419 (b : nat) (a : nat) : (term15 a b) = a.
Proof. exact (@lem2838418 b a). Qed.
Lemma lem2838420 (a : nat) (b : nat) : a = (term15 a b).
Proof. exact (SYM (@lem2838419 b a)). Qed.
Lemma lem2838422 {A B : Type'} (x : A) (y : B) : (term10 A B x y) = y.
Proof. exact (EQ_MP (@lem2838408 A B x y) (@lem2838407 A B x y)). Qed.
Lemma lem2838423 (x : nat) (y : nat) : (term16 x y) = y.
Proof. exact (@lem2838422 nat nat x y). Qed.
Lemma lem2838424 (a : nat) (b : nat) : (term16 a b) = b.
Proof. exact (@lem2838423 a b). Qed.
Lemma lem2838425 (a : nat) (b : nat) : b = (term16 a b).
Proof. exact (SYM (@lem2838424 a b)). Qed.
Lemma lem2838426 : term17 = term17.
Proof. exact (eq_refl term17). Qed.
Lemma lem2838427 (a : nat) (b : nat) : (term18 a) = (term19 a b).
Proof. exact (MK_COMB (@lem2838426) (@lem2838420 a b)). Qed.
Lemma lem2838428 (a : nat) (b : nat) : (term19 a b) = (term20 a b).
Proof. exact (eq_refl (term19 a b)). Qed.
Lemma lem2838429 (a : nat) : (term21 a) = (term21 a).
Proof. exact (eq_refl (term21 a)). Qed.
Lemma lem2838430 (a : nat) (b : nat) : ((term18 a) = (term19 a b)) = ((term18 a) = (term20 a b)).
Proof. exact (MK_COMB (@lem2838429 a) (@lem2838428 a b)). Qed.
Lemma lem2838431 (a : nat) : (term18 a) = (term22 a).
Proof. exact (eq_refl (term18 a)). Qed.
Lemma lem2838432 : (@eq (nat -> Prop)) = (@eq (nat -> Prop)).
Proof. exact (eq_refl (@eq (nat -> Prop))). Qed.
Lemma lem2838433 (a : nat) : (term21 a) = (term23 a).
Proof. exact (MK_COMB (@lem2838432) (@lem2838431 a)). Qed.
Lemma lem2838434 (a : nat) (b : nat) : (term20 a b) = (term20 a b).
Proof. exact (eq_refl (term20 a b)). Qed.
Lemma lem2838435 (a : nat) (b : nat) : ((term18 a) = (term20 a b)) = ((term22 a) = (term20 a b)).
Proof. exact (MK_COMB (@lem2838433 a) (@lem2838434 a b)). Qed.
Lemma lem2838436 (a : nat) (b : nat) : ((term18 a) = (term19 a b)) = ((term22 a) = (term20 a b)).
Proof. exact (TRANS (@lem2838430 a b) (@lem2838435 a b)). Qed.
Lemma lem2838437 (a : nat) (b : nat) : (term22 a) = (term20 a b).
Proof. exact (EQ_MP (@lem2838436 a b) (@lem2838427 a b)). Qed.
Lemma lem2838438 (a : nat) (b : nat) : (term24 a b) = (term25 a b).
Proof. exact (MK_COMB (@lem2838437 a b) (@lem2838425 a b)). Qed.
Lemma lem2838439 (a : nat) (b : nat) : (term25 a b) = (term6 a b).
Proof. exact (eq_refl (term25 a b)). Qed.
Lemma lem2838440 (a : nat) (b : nat) : (term26 a b) = (term26 a b).
Proof. exact (eq_refl (term26 a b)). Qed.
Lemma lem2838441 (a : nat) (b : nat) : ((term24 a b) = (term25 a b)) = ((term24 a b) = (term6 a b)).
Proof. exact (MK_COMB (@lem2838440 a b) (@lem2838439 a b)). Qed.
Lemma lem2838442 (a : nat) (b : nat) : (term24 a b) = (term27 a b).
Proof. exact (eq_refl (term24 a b)). Qed.
Lemma lem2838443 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2838444 (a : nat) (b : nat) : (term26 a b) = (term28 a b).
Proof. exact (MK_COMB (@lem2838443) (@lem2838442 a b)). Qed.
Lemma lem2838445 (a : nat) (b : nat) : (term6 a b) = (term6 a b).
Proof. exact (eq_refl (term6 a b)). Qed.
Lemma lem2838446 (a : nat) (b : nat) : ((term24 a b) = (term6 a b)) = ((term27 a b) = (term6 a b)).
Proof. exact (MK_COMB (@lem2838444 a b) (@lem2838445 a b)). Qed.
Lemma lem2838447 (a : nat) (b : nat) : ((term24 a b) = (term25 a b)) = ((term27 a b) = (term6 a b)).
Proof. exact (TRANS (@lem2838441 a b) (@lem2838446 a b)). Qed.
Lemma lem2838448 (a : nat) (b : nat) : (term27 a b) = (term6 a b).
Proof. exact (EQ_MP (@lem2838447 a b) (@lem2838438 a b)). Qed.
Lemma lem2838449 (a : nat) (b : nat) : (term6 a b) = (term27 a b).
Proof. exact (SYM (@lem2838448 a b)). Qed.
Lemma lem2838450 (a : nat) (b : nat) : (term5 a b) = (term27 a b).
Proof. exact (TRANS (@lem2838403 a b) (@lem2838449 a b)). Qed.
Lemma lem2838451 (a : nat) : term29 a.
Proof. exact (fun b : nat => @lem2838450 a b). Qed.
Lemma lem2838452 : term30.
Proof. exact (fun a : nat => @lem2838451 a). Qed.
