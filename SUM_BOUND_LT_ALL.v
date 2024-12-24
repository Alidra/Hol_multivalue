Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_BOUND_LT_ALL_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import MEMBER_NOT_EMPTY_spec.
Require Import REAL_LT_IMP_LE_spec.
Require Import SUM_BOUND_LT_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm19490_spec.
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
Require Import thm69_spec.
Lemma lem7138161 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem7138162 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem7138163 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem7138162 t1) (@lem7138161 t1)). Qed.
Lemma lem7138164 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem7138163 t1 t2). Qed.
Lemma lem7138165 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem7138166 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem7138165 t1 t2) (@lem7138164 t1 t2)). Qed.
Lemma lem7138167 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem7138166 t1 t2 t3). Qed.
Lemma lem7138168 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem7138169 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem7138168 t1 t2 t3) (@lem7138167 t1 t2 t3)). Qed.
Lemma lem7138170 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem7138169 t1 t2 t3)). Qed.
Lemma lem7138172 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7138173 {_133668 : Type'} : (term8 _133668) = (term9 _133668).
Proof. exact (@lem7138172 (term8 _133668)). Qed.
Lemma lem7138174 {_133668 : Type'} : (term9 _133668) = (term8 _133668).
Proof. exact (SYM (@lem7138173 _133668)). Qed.
Lemma lem7138175 {_133668 : Type'} (h1 : term10 _133668) : term10 _133668.
Proof. exact (h1). Qed.
Lemma lem7138176 {_133668 : Type'} : term11 _133668.
Proof. exact (@lem3216368 _133668). Qed.
Lemma lem7138179 {_133668 : Type'} : term12 _133668.
Proof. exact (@lem7138160 _133668). Qed.
Lemma lem7138185 {_133668 A : Type'} (h1 : term13 _133668 A) : term13 _133668 A.
Proof. exact (h1). Qed.
Lemma lem7138186 {_133668 A : Type'} : term14 _133668 A.
Proof. exact (fun h0 : term13 _133668 A => @lem7138185 _133668 A h0). Qed.
Lemma lem7138187 {_133668 A : Type'} (h1 : term14 _133668 A) : term14 _133668 A.
Proof. exact (h1). Qed.
Lemma lem7138188 {_133668 A : Type'} (h1 : term13 _133668 A) : term13 _133668 A.
Proof. exact (h1). Qed.
Lemma lem7138189 {_133668 A : Type'} (h1 : term13 _133668 A) (h2 : term14 _133668 A) : term13 _133668 A.
Proof. exact (@lem7138187 _133668 A h2 (@lem7138188 _133668 A h1)). Qed.
Lemma lem7138190 {_133668 A : Type'} (h1 : term13 _133668 A) : term15 _133668 A.
Proof. exact (fun h0 : term14 _133668 A => @lem7138189 _133668 A h1 h0). Qed.
Lemma lem7138191 {_133668 A : Type'} (h1 : term14 _133668 A) : term14 _133668 A.
Proof. exact (h1). Qed.
Lemma lem7138192 {_133668 A : Type'} (h1 : term13 _133668 A) (h2 : term14 _133668 A) : term13 _133668 A.
Proof. exact (@lem7138190 _133668 A h1 (@lem7138191 _133668 A h2)). Qed.
Lemma lem7138193 {_133668 A : Type'} (h1 : term14 _133668 A) : term14 _133668 A.
Proof. exact (fun h0 : term13 _133668 A => @lem7138192 _133668 A h0 h1). Qed.
Lemma lem7138194 {_133668 A : Type'} : term16 _133668 A.
Proof. exact (fun h0 : term14 _133668 A => @lem7138193 _133668 A h0). Qed.
Lemma lem7138197 {_133668 A : Type'} : term14 _133668 A.
Proof. exact (@lem7138194 _133668 A (@lem7138186 _133668 A)). Qed.
Lemma lem7138198 {_133668 A : Type'} : term14 _133668 A.
Proof. exact (@lem7138197 _133668 A). Qed.
Lemma lem7138390 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7138391 {_133668 : Type'} : (term17 _133668) = (term18 _133668).
Proof. exact (@lem7138390 (term11 _133668)). Qed.
Lemma lem7138400 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem7138401 {_133668 : Type'} : (term20 _133668) = (term21 _133668).
Proof. exact (MK_COMB (@lem7138400) (@lem7138391 _133668)). Qed.
Lemma lem7138404 {A : Type'} : (term22 A) = (term22 A).
Proof. exact (eq_refl (term22 A)). Qed.
Lemma lem7138405 {_133668 A : Type'} : (term23 _133668 A) = (term24 _133668 A).
Proof. exact (MK_COMB (@lem7138404 A) (@lem7138401 _133668)). Qed.
Lemma lem7138408 {_133668 : Type'} : (term22 _133668) = (term22 _133668).
Proof. exact (eq_refl (term22 _133668)). Qed.
Lemma lem7138409 {_133668 A : Type'} : (term25 _133668 A) = (term26 _133668 A).
Proof. exact (MK_COMB (@lem7138408 _133668) (@lem7138405 _133668 A)). Qed.
Lemma lem7138412 {_133668 : Type'} : (term27 _133668) = (term27 _133668).
Proof. exact (eq_refl (term27 _133668)). Qed.
Lemma lem7138419 {_133668 A : Type'} : (term13 _133668 A) = (term28 _133668 A).
Proof. exact (MK_COMB (@lem7138412 _133668) (@lem7138409 _133668 A)). Qed.
Lemma lem7138422 {_133668 : Type'} (s : _133668 -> Prop) : (term29 _133668 s) = (term29 _133668 s).
Proof. exact (eq_refl (term29 _133668 s)). Qed.
Lemma lem7138423 {_133668 : Type'} (x : _133668) (s : _133668 -> Prop) : (@IN _133668 x s) = (@IN _133668 x s).
Proof. exact (eq_refl (@IN _133668 x s)). Qed.
Lemma lem7138424 {_133668 : Type'} (s : _133668 -> Prop) : (term30 _133668 s) = (term30 _133668 s).
Proof. exact (fun_ext (fun x : _133668 => @lem7138423 _133668 x s)). Qed.
Lemma lem7138425 {_133668 : Type'} : (@ex _133668) = (@ex _133668).
Proof. exact (eq_refl (@ex _133668)). Qed.
Lemma lem7138426 {_133668 : Type'} (s : _133668 -> Prop) : (term31 _133668 s) = (term31 _133668 s).
Proof. exact (MK_COMB (@lem7138425 _133668) (@lem7138424 _133668 s)). Qed.
Lemma lem7138427 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7138428 {_133668 : Type'} (s : _133668 -> Prop) : (term32 _133668 s) = (term32 _133668 s).
Proof. exact (MK_COMB (@lem7138427) (@lem7138426 _133668 s)). Qed.
Lemma lem7138429 {_133668 : Type'} (s : _133668 -> Prop) : ((term31 _133668 s) = (term29 _133668 s)) = ((term31 _133668 s) = (term29 _133668 s)).
Proof. exact (MK_COMB (@lem7138428 _133668 s) (@lem7138422 _133668 s)). Qed.
Lemma lem7138430 {_133668 : Type'} : (term33 _133668) = (term33 _133668).
Proof. exact (fun_ext (fun s : _133668 -> Prop => @lem7138429 _133668 s)). Qed.
Lemma lem7138431 {_133668 : Type'} : (@all (_133668 -> Prop)) = (@all (_133668 -> Prop)).
Proof. exact (eq_refl (@all (_133668 -> Prop))). Qed.
Lemma lem7138432 {_133668 : Type'} : (term11 _133668) = (term11 _133668).
Proof. exact (MK_COMB (@lem7138431 _133668) (@lem7138430 _133668)). Qed.
Lemma lem7138433 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7138434 {_133668 : Type'} : (term18 _133668) = (term18 _133668).
Proof. exact (MK_COMB (@lem7138433) (@lem7138432 _133668)). Qed.
Lemma lem7138439 (x : real) (y : real) : (term34 x y) = (term34 x y).
Proof. exact (eq_refl (term34 x y)). Qed.
Lemma lem7138440 (x : real) : (term35 x) = (term35 x).
Proof. exact (fun_ext (fun y : real => @lem7138439 x y)). Qed.
Lemma lem7138441 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7138442 (x : real) : (term36 x) = (term36 x).
Proof. exact (MK_COMB (@lem7138441) (@lem7138440 x)). Qed.
Lemma lem7138443 : term37 = term37.
Proof. exact (fun_ext (fun x : real => @lem7138442 x)). Qed.
Lemma lem7138444 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7138445 : term38 = term38.
Proof. exact (MK_COMB (@lem7138444) (@lem7138443)). Qed.
Lemma lem7138446 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7138447 : term19 = term19.
Proof. exact (MK_COMB (@lem7138446) (@lem7138445)). Qed.
Lemma lem7138448 {_133668 : Type'} : (term21 _133668) = (term21 _133668).
Proof. exact (MK_COMB (@lem7138447) (@lem7138434 _133668)). Qed.
Lemma lem7138449 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term39 A f s b) = (term39 A f s b).
Proof. exact (eq_refl (term39 A f s b)). Qed.
Lemma lem7138454 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) : (term40 A s f x b) = (term40 A s f x b).
Proof. exact (eq_refl (term40 A s f x b)). Qed.
Lemma lem7138455 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term41 A s f b) = (term41 A s f b).
Proof. exact (fun_ext (fun x : A => @lem7138454 A s f x b)). Qed.
Lemma lem7138456 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7138457 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term42 A s f b) = (term42 A s f b).
Proof. exact (MK_COMB (@lem7138456 A) (@lem7138455 A s f b)). Qed.
Lemma lem7138462 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) : (term43 A s f x b) = (term43 A s f x b).
Proof. exact (eq_refl (term43 A s f x b)). Qed.
Lemma lem7138463 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term44 A s f b) = (term44 A s f b).
Proof. exact (fun_ext (fun x : A => @lem7138462 A s f x b)). Qed.
Lemma lem7138464 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7138465 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term45 A s f b) = (term45 A s f b).
Proof. exact (MK_COMB (@lem7138464 A) (@lem7138463 A s f b)). Qed.
Lemma lem7138466 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7138467 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term46 A s f b) = (term46 A s f b).
Proof. exact (MK_COMB (@lem7138466) (@lem7138465 A s f b)). Qed.
Lemma lem7138468 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term47 A s f b) = (term47 A s f b).
Proof. exact (MK_COMB (@lem7138467 A s f b) (@lem7138457 A s f b)). Qed.
Lemma lem7138471 {A : Type'} (s : A -> Prop) : (term48 A s) = (term48 A s).
Proof. exact (eq_refl (term48 A s)). Qed.
Lemma lem7138472 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term49 A s f b) = (term49 A s f b).
Proof. exact (MK_COMB (@lem7138471 A s) (@lem7138468 A s f b)). Qed.
Lemma lem7138473 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7138474 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term50 A s f b) = (term50 A s f b).
Proof. exact (MK_COMB (@lem7138473) (@lem7138472 A s f b)). Qed.
Lemma lem7138475 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term51 A f s b) = (term51 A f s b).
Proof. exact (MK_COMB (@lem7138474 A s f b) (@lem7138449 A f s b)). Qed.
Lemma lem7138476 {A : Type'} (f : A -> real) (s : A -> Prop) : (term52 A f s) = (term52 A f s).
Proof. exact (fun_ext (fun b : real => @lem7138475 A f s b)). Qed.
Lemma lem7138477 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7138478 {A : Type'} (f : A -> real) (s : A -> Prop) : (term53 A f s) = (term53 A f s).
Proof. exact (MK_COMB (@lem7138477) (@lem7138476 A f s)). Qed.
Lemma lem7138479 {A : Type'} (s : A -> Prop) : (term54 A s) = (term54 A s).
Proof. exact (fun_ext (fun f : A -> real => @lem7138478 A f s)). Qed.
Lemma lem7138480 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7138481 {A : Type'} (s : A -> Prop) : (term55 A s) = (term55 A s).
Proof. exact (MK_COMB (@lem7138480 A) (@lem7138479 A s)). Qed.
Lemma lem7138482 {A : Type'} : (term56 A) = (term56 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7138481 A s)). Qed.
Lemma lem7138483 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7138484 {A : Type'} : (term12 A) = (term12 A).
Proof. exact (MK_COMB (@lem7138483 A) (@lem7138482 A)). Qed.
Lemma lem7138485 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7138486 {A : Type'} : (term22 A) = (term22 A).
Proof. exact (MK_COMB (@lem7138485) (@lem7138484 A)). Qed.
Lemma lem7138487 {_133668 A : Type'} : (term24 _133668 A) = (term24 _133668 A).
Proof. exact (MK_COMB (@lem7138486 A) (@lem7138448 _133668)). Qed.
Lemma lem7138488 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term39 _133668 f s b) = (term39 _133668 f s b).
Proof. exact (eq_refl (term39 _133668 f s b)). Qed.
Lemma lem7138493 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (x : _133668) (b : real) : (term40 _133668 s f x b) = (term40 _133668 s f x b).
Proof. exact (eq_refl (term40 _133668 s f x b)). Qed.
Lemma lem7138494 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term41 _133668 s f b) = (term41 _133668 s f b).
Proof. exact (fun_ext (fun x : _133668 => @lem7138493 _133668 s f x b)). Qed.
Lemma lem7138495 {_133668 : Type'} : (@ex _133668) = (@ex _133668).
Proof. exact (eq_refl (@ex _133668)). Qed.
Lemma lem7138496 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term42 _133668 s f b) = (term42 _133668 s f b).
Proof. exact (MK_COMB (@lem7138495 _133668) (@lem7138494 _133668 s f b)). Qed.
Lemma lem7138501 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (x : _133668) (b : real) : (term43 _133668 s f x b) = (term43 _133668 s f x b).
Proof. exact (eq_refl (term43 _133668 s f x b)). Qed.
Lemma lem7138502 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term44 _133668 s f b) = (term44 _133668 s f b).
Proof. exact (fun_ext (fun x : _133668 => @lem7138501 _133668 s f x b)). Qed.
Lemma lem7138503 {_133668 : Type'} : (@all _133668) = (@all _133668).
Proof. exact (eq_refl (@all _133668)). Qed.
Lemma lem7138504 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term45 _133668 s f b) = (term45 _133668 s f b).
Proof. exact (MK_COMB (@lem7138503 _133668) (@lem7138502 _133668 s f b)). Qed.
Lemma lem7138505 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7138506 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term46 _133668 s f b) = (term46 _133668 s f b).
Proof. exact (MK_COMB (@lem7138505) (@lem7138504 _133668 s f b)). Qed.
Lemma lem7138507 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term47 _133668 s f b) = (term47 _133668 s f b).
Proof. exact (MK_COMB (@lem7138506 _133668 s f b) (@lem7138496 _133668 s f b)). Qed.
Lemma lem7138510 {_133668 : Type'} (s : _133668 -> Prop) : (term48 _133668 s) = (term48 _133668 s).
Proof. exact (eq_refl (term48 _133668 s)). Qed.
Lemma lem7138511 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term49 _133668 s f b) = (term49 _133668 s f b).
Proof. exact (MK_COMB (@lem7138510 _133668 s) (@lem7138507 _133668 s f b)). Qed.
Lemma lem7138512 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7138513 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term50 _133668 s f b) = (term50 _133668 s f b).
Proof. exact (MK_COMB (@lem7138512) (@lem7138511 _133668 s f b)). Qed.
Lemma lem7138514 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term51 _133668 f s b) = (term51 _133668 f s b).
Proof. exact (MK_COMB (@lem7138513 _133668 s f b) (@lem7138488 _133668 f s b)). Qed.
Lemma lem7138515 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) : (term52 _133668 f s) = (term52 _133668 f s).
Proof. exact (fun_ext (fun b : real => @lem7138514 _133668 f s b)). Qed.
Lemma lem7138516 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7138517 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) : (term53 _133668 f s) = (term53 _133668 f s).
Proof. exact (MK_COMB (@lem7138516) (@lem7138515 _133668 f s)). Qed.
Lemma lem7138518 {_133668 : Type'} (s : _133668 -> Prop) : (term54 _133668 s) = (term54 _133668 s).
Proof. exact (fun_ext (fun f : _133668 -> real => @lem7138517 _133668 f s)). Qed.
Lemma lem7138519 {_133668 : Type'} : (@all (_133668 -> real)) = (@all (_133668 -> real)).
Proof. exact (eq_refl (@all (_133668 -> real))). Qed.
Lemma lem7138520 {_133668 : Type'} (s : _133668 -> Prop) : (term55 _133668 s) = (term55 _133668 s).
Proof. exact (MK_COMB (@lem7138519 _133668) (@lem7138518 _133668 s)). Qed.
Lemma lem7138521 {_133668 : Type'} : (term56 _133668) = (term56 _133668).
Proof. exact (fun_ext (fun s : _133668 -> Prop => @lem7138520 _133668 s)). Qed.
Lemma lem7138522 {_133668 : Type'} : (@all (_133668 -> Prop)) = (@all (_133668 -> Prop)).
Proof. exact (eq_refl (@all (_133668 -> Prop))). Qed.
Lemma lem7138523 {_133668 : Type'} : (term12 _133668) = (term12 _133668).
Proof. exact (MK_COMB (@lem7138522 _133668) (@lem7138521 _133668)). Qed.
Lemma lem7138524 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7138525 {_133668 : Type'} : (term22 _133668) = (term22 _133668).
Proof. exact (MK_COMB (@lem7138524) (@lem7138523 _133668)). Qed.
Lemma lem7138526 {_133668 A : Type'} : (term26 _133668 A) = (term26 _133668 A).
Proof. exact (MK_COMB (@lem7138525 _133668) (@lem7138487 _133668 A)). Qed.
Lemma lem7138527 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term39 _133668 f s b) = (term39 _133668 f s b).
Proof. exact (eq_refl (term39 _133668 f s b)). Qed.
Lemma lem7138532 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (x : _133668) (b : real) : (term57 _133668 s f x b) = (term57 _133668 s f x b).
Proof. exact (eq_refl (term57 _133668 s f x b)). Qed.
Lemma lem7138533 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term58 _133668 s f b) = (term58 _133668 s f b).
Proof. exact (fun_ext (fun x : _133668 => @lem7138532 _133668 s f x b)). Qed.
Lemma lem7138534 {_133668 : Type'} : (@all _133668) = (@all _133668).
Proof. exact (eq_refl (@all _133668)). Qed.
Lemma lem7138535 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term59 _133668 s f b) = (term59 _133668 s f b).
Proof. exact (MK_COMB (@lem7138534 _133668) (@lem7138533 _133668 s f b)). Qed.
Lemma lem7138540 {_133668 : Type'} (s : _133668 -> Prop) : (term60 _133668 s) = (term60 _133668 s).
Proof. exact (eq_refl (term60 _133668 s)). Qed.
Lemma lem7138541 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term61 _133668 s f b) = (term61 _133668 s f b).
Proof. exact (MK_COMB (@lem7138540 _133668 s) (@lem7138535 _133668 s f b)). Qed.
Lemma lem7138544 {_133668 : Type'} (s : _133668 -> Prop) : (term48 _133668 s) = (term48 _133668 s).
Proof. exact (eq_refl (term48 _133668 s)). Qed.
Lemma lem7138545 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term62 _133668 s f b) = (term62 _133668 s f b).
Proof. exact (MK_COMB (@lem7138544 _133668 s) (@lem7138541 _133668 s f b)). Qed.
Lemma lem7138546 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7138547 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term63 _133668 s f b) = (term63 _133668 s f b).
Proof. exact (MK_COMB (@lem7138546) (@lem7138545 _133668 s f b)). Qed.
Lemma lem7138548 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term64 _133668 f s b) = (term64 _133668 f s b).
Proof. exact (MK_COMB (@lem7138547 _133668 s f b) (@lem7138527 _133668 f s b)). Qed.
Lemma lem7138549 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) : (term65 _133668 f s) = (term65 _133668 f s).
Proof. exact (fun_ext (fun b : real => @lem7138548 _133668 f s b)). Qed.
Lemma lem7138550 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7138551 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) : (term66 _133668 f s) = (term66 _133668 f s).
Proof. exact (MK_COMB (@lem7138550) (@lem7138549 _133668 f s)). Qed.
Lemma lem7138552 {_133668 : Type'} (s : _133668 -> Prop) : (term67 _133668 s) = (term67 _133668 s).
Proof. exact (fun_ext (fun f : _133668 -> real => @lem7138551 _133668 f s)). Qed.
Lemma lem7138553 {_133668 : Type'} : (@all (_133668 -> real)) = (@all (_133668 -> real)).
Proof. exact (eq_refl (@all (_133668 -> real))). Qed.
Lemma lem7138554 {_133668 : Type'} (s : _133668 -> Prop) : (term68 _133668 s) = (term68 _133668 s).
Proof. exact (MK_COMB (@lem7138553 _133668) (@lem7138552 _133668 s)). Qed.
Lemma lem7138555 {_133668 : Type'} : (term69 _133668) = (term69 _133668).
Proof. exact (fun_ext (fun s : _133668 -> Prop => @lem7138554 _133668 s)). Qed.
Lemma lem7138556 {_133668 : Type'} : (@all (_133668 -> Prop)) = (@all (_133668 -> Prop)).
Proof. exact (eq_refl (@all (_133668 -> Prop))). Qed.
Lemma lem7138557 {_133668 : Type'} : (term8 _133668) = (term8 _133668).
Proof. exact (MK_COMB (@lem7138556 _133668) (@lem7138555 _133668)). Qed.
Lemma lem7138558 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7138559 {_133668 : Type'} : (term10 _133668) = (term10 _133668).
Proof. exact (MK_COMB (@lem7138558) (@lem7138557 _133668)). Qed.
Lemma lem7138560 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7138561 {_133668 : Type'} : (term27 _133668) = (term27 _133668).
Proof. exact (MK_COMB (@lem7138560) (@lem7138559 _133668)). Qed.
Lemma lem7138562 {_133668 A : Type'} : (term28 _133668 A) = (term28 _133668 A).
Proof. exact (MK_COMB (@lem7138561 _133668) (@lem7138526 _133668 A)). Qed.
Lemma lem7138711 {_133668 A : Type'} : (term13 _133668 A) = (term28 _133668 A).
Proof. exact (TRANS (@lem7138419 _133668 A) (@lem7138562 _133668 A)). Qed.
Lemma lem7138712 {_133668 A : Type'} : (term28 _133668 A) = (term13 _133668 A).
Proof. exact (SYM (@lem7138711 _133668 A)). Qed.
Lemma lem7138713 {_133668 : Type'} (h1 : term10 _133668) : term10 _133668.
Proof. exact (h1). Qed.
Lemma lem7138714 {_133668 : Type'} (h1 : term12 _133668) : term12 _133668.
Proof. exact (h1). Qed.
Lemma lem7138715 {A : Type'} (h1 : term12 A) : term12 A.
Proof. exact (h1). Qed.
Lemma lem7138716 (h1 : term38) : term38.
Proof. exact (h1). Qed.
Lemma lem7138717 {_133668 : Type'} (h1 : term11 _133668) : term11 _133668.
Proof. exact (h1). Qed.
Lemma lem7138726 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (x : _133668) (b : real) : (term57 _133668 s f x b) = (term70 _133668 s f x b).
Proof. exact (@lem17265 (@IN _133668 x s) (term71 _133668 f x b)). Qed.
Lemma lem7138727 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term58 _133668 s f b) = (term72 _133668 s f b).
Proof. exact (fun_ext (fun x : _133668 => @lem7138726 _133668 s f x b)). Qed.
Lemma lem7138728 {_133668 : Type'} : (@all _133668) = (@all _133668).
Proof. exact (eq_refl (@all _133668)). Qed.
Lemma lem7138729 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term59 _133668 s f b) = (term73 _133668 s f b).
Proof. exact (MK_COMB (@lem7138728 _133668) (@lem7138727 _133668 s f b)). Qed.
Lemma lem7138731 {_133668 : Type'} (s : _133668 -> Prop) : (term60 _133668 s) = (term60 _133668 s).
Proof. exact (eq_refl (term60 _133668 s)). Qed.
Lemma lem7138732 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term61 _133668 s f b) = (term74 _133668 s f b).
Proof. exact (MK_COMB (@lem7138731 _133668 s) (@lem7138729 _133668 s f b)). Qed.
Lemma lem7138734 {_133668 : Type'} (s : _133668 -> Prop) : (term48 _133668 s) = (term48 _133668 s).
Proof. exact (eq_refl (term48 _133668 s)). Qed.
Lemma lem7138735 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term62 _133668 s f b) = (term75 _133668 s f b).
Proof. exact (MK_COMB (@lem7138734 _133668 s) (@lem7138732 _133668 s f b)). Qed.
Lemma lem7138736 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term76 _133668 f s b) = (term76 _133668 f s b).
Proof. exact (eq_refl (term76 _133668 f s b)). Qed.
Lemma lem7138737 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7138738 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term77 _133668 s f b) = (term78 _133668 s f b).
Proof. exact (MK_COMB (@lem7138737) (@lem7138735 _133668 s f b)). Qed.
Lemma lem7138739 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term79 _133668 f s b) = (term80 _133668 f s b).
Proof. exact (MK_COMB (@lem7138738 _133668 s f b) (@lem7138736 _133668 f s b)). Qed.
Lemma lem7138740 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term81 _133668 f s b) = (term79 _133668 f s b).
Proof. exact (@lem17362 (term62 _133668 s f b) (term39 _133668 f s b)). Qed.
Lemma lem7138741 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term81 _133668 f s b) = (term80 _133668 f s b).
Proof. exact (TRANS (@lem7138740 _133668 f s b) (@lem7138739 _133668 f s b)). Qed.
Lemma lem7138742 (P : real -> Prop) : (term82 P) = (term83 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem7138743 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) : (term84 _133668 f s) = (term85 _133668 f s).
Proof. exact (@lem7138742 (term65 _133668 f s)). Qed.
Lemma lem7138744 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term86 _133668 f s b) = (term64 _133668 f s b).
Proof. exact (eq_refl (term86 _133668 f s b)). Qed.
Lemma lem7138745 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7138746 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term87 _133668 f s b) = (term81 _133668 f s b).
Proof. exact (MK_COMB (@lem7138745) (@lem7138744 _133668 f s b)). Qed.
Lemma lem7138747 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term87 _133668 f s b) = (term80 _133668 f s b).
Proof. exact (TRANS (@lem7138746 _133668 f s b) (@lem7138741 _133668 f s b)). Qed.
Lemma lem7138748 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) : (term88 _133668 f s) = (term89 _133668 f s).
Proof. exact (fun_ext (fun b : real => @lem7138747 _133668 f s b)). Qed.
Lemma lem7138749 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7138750 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) : (term85 _133668 f s) = (term90 _133668 f s).
Proof. exact (MK_COMB (@lem7138749) (@lem7138748 _133668 f s)). Qed.
Lemma lem7138751 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) : (term84 _133668 f s) = (term90 _133668 f s).
Proof. exact (TRANS (@lem7138743 _133668 f s) (@lem7138750 _133668 f s)). Qed.
Lemma lem7138752 {_133668 : Type'} (P : type716 _133668) : (term91 _133668 P) = (term92 _133668 P).
Proof. exact (@lem18392 (_133668 -> real) P). Qed.
Lemma lem7138753 {_133668 : Type'} (s : _133668 -> Prop) : (term93 _133668 s) = (term94 _133668 s).
Proof. exact (@lem7138752 _133668 (term67 _133668 s)). Qed.
Lemma lem7138754 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) : (term95 _133668 s f) = (term66 _133668 f s).
Proof. exact (eq_refl (term95 _133668 s f)). Qed.
Lemma lem7138755 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7138756 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) : (term96 _133668 s f) = (term84 _133668 f s).
Proof. exact (MK_COMB (@lem7138755) (@lem7138754 _133668 f s)). Qed.
Lemma lem7138757 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) : (term96 _133668 s f) = (term90 _133668 f s).
Proof. exact (TRANS (@lem7138756 _133668 f s) (@lem7138751 _133668 f s)). Qed.
Lemma lem7138758 {_133668 : Type'} (s : _133668 -> Prop) : (term97 _133668 s) = (term98 _133668 s).
Proof. exact (fun_ext (fun f : _133668 -> real => @lem7138757 _133668 f s)). Qed.
Lemma lem7138759 {_133668 : Type'} : (@ex (_133668 -> real)) = (@ex (_133668 -> real)).
Proof. exact (eq_refl (@ex (_133668 -> real))). Qed.
Lemma lem7138760 {_133668 : Type'} (s : _133668 -> Prop) : (term94 _133668 s) = (term99 _133668 s).
Proof. exact (MK_COMB (@lem7138759 _133668) (@lem7138758 _133668 s)). Qed.
Lemma lem7138761 {_133668 : Type'} (s : _133668 -> Prop) : (term93 _133668 s) = (term99 _133668 s).
Proof. exact (TRANS (@lem7138753 _133668 s) (@lem7138760 _133668 s)). Qed.
Lemma lem7138762 {_133668 : Type'} (P : type686 _133668) : (term100 _133668 P) = (term101 _133668 P).
Proof. exact (@lem18392 (_133668 -> Prop) P). Qed.
Lemma lem7138763 {_133668 : Type'} : (term10 _133668) = (term102 _133668).
Proof. exact (@lem7138762 _133668 (term69 _133668)). Qed.
Lemma lem7138764 {_133668 : Type'} (s : _133668 -> Prop) : (term103 _133668 s) = (term68 _133668 s).
Proof. exact (eq_refl (term103 _133668 s)). Qed.
Lemma lem7138765 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7138766 {_133668 : Type'} (s : _133668 -> Prop) : (term104 _133668 s) = (term93 _133668 s).
Proof. exact (MK_COMB (@lem7138765) (@lem7138764 _133668 s)). Qed.
Lemma lem7138767 {_133668 : Type'} (s : _133668 -> Prop) : (term104 _133668 s) = (term99 _133668 s).
Proof. exact (TRANS (@lem7138766 _133668 s) (@lem7138761 _133668 s)). Qed.
Lemma lem7138768 {_133668 : Type'} : (term105 _133668) = (term106 _133668).
Proof. exact (fun_ext (fun s : _133668 -> Prop => @lem7138767 _133668 s)). Qed.
Lemma lem7138769 {_133668 : Type'} : (@ex (_133668 -> Prop)) = (@ex (_133668 -> Prop)).
Proof. exact (eq_refl (@ex (_133668 -> Prop))). Qed.
Lemma lem7138770 {_133668 : Type'} : (term102 _133668) = (term107 _133668).
Proof. exact (MK_COMB (@lem7138769 _133668) (@lem7138768 _133668)). Qed.
Lemma lem7138879 {_133668 : Type'} : (term10 _133668) = (term107 _133668).
Proof. exact (TRANS (@lem7138763 _133668) (@lem7138770 _133668)). Qed.
Lemma lem7138880 {_133668 : Type'} (h1 : term10 _133668) : term107 _133668.
Proof. exact (EQ_MP (@lem7138879 _133668) (@lem7138713 _133668 h1)). Qed.
Lemma lem7138888 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (x : _133668) (b : real) : (term108 _133668 s f x b) = (term109 _133668 s f x b).
Proof. exact (@lem17362 (@IN _133668 x s) (term110 _133668 f x b)). Qed.
Lemma lem7138889 {_133668 : Type'} (P : _133668 -> Prop) : (term111 _133668 P) = (term112 _133668 P).
Proof. exact (@lem18392 _133668 P). Qed.
Lemma lem7138890 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term113 _133668 s f b) = (term114 _133668 s f b).
Proof. exact (@lem7138889 _133668 (term44 _133668 s f b)). Qed.
Lemma lem7138891 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (x : _133668) (b : real) : (term115 _133668 s f b x) = (term43 _133668 s f x b).
Proof. exact (eq_refl (term115 _133668 s f b x)). Qed.
Lemma lem7138892 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7138893 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (x : _133668) (b : real) : (term116 _133668 s f b x) = (term108 _133668 s f x b).
Proof. exact (MK_COMB (@lem7138892) (@lem7138891 _133668 s f x b)). Qed.
Lemma lem7138894 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (x : _133668) (b : real) : (term116 _133668 s f b x) = (term109 _133668 s f x b).
Proof. exact (TRANS (@lem7138893 _133668 s f x b) (@lem7138888 _133668 s f x b)). Qed.
Lemma lem7138895 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term117 _133668 s f b) = (term118 _133668 s f b).
Proof. exact (fun_ext (fun x : _133668 => @lem7138894 _133668 s f x b)). Qed.
Lemma lem7138896 {_133668 : Type'} : (@ex _133668) = (@ex _133668).
Proof. exact (eq_refl (@ex _133668)). Qed.
Lemma lem7138897 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term114 _133668 s f b) = (term119 _133668 s f b).
Proof. exact (MK_COMB (@lem7138896 _133668) (@lem7138895 _133668 s f b)). Qed.
Lemma lem7138898 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term113 _133668 s f b) = (term119 _133668 s f b).
Proof. exact (TRANS (@lem7138890 _133668 s f b) (@lem7138897 _133668 s f b)). Qed.
Lemma lem7138905 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (x : _133668) (b : real) : (term120 _133668 s f x b) = (term121 _133668 s f x b).
Proof. exact (@lem17045 (@IN _133668 x s) (term71 _133668 f x b)). Qed.
Lemma lem7138906 {_133668 : Type'} (P : _133668 -> Prop) : (term122 _133668 P) = (term123 _133668 P).
Proof. exact (@lem18394 _133668 P). Qed.
Lemma lem7138907 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term124 _133668 s f b) = (term125 _133668 s f b).
Proof. exact (@lem7138906 _133668 (term41 _133668 s f b)). Qed.
Lemma lem7138908 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (x : _133668) (b : real) : (term126 _133668 s f b x) = (term40 _133668 s f x b).
Proof. exact (eq_refl (term126 _133668 s f b x)). Qed.
Lemma lem7138909 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7138910 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (x : _133668) (b : real) : (term127 _133668 s f b x) = (term120 _133668 s f x b).
Proof. exact (MK_COMB (@lem7138909) (@lem7138908 _133668 s f x b)). Qed.
Lemma lem7138911 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (x : _133668) (b : real) : (term127 _133668 s f b x) = (term121 _133668 s f x b).
Proof. exact (TRANS (@lem7138910 _133668 s f x b) (@lem7138905 _133668 s f x b)). Qed.
Lemma lem7138912 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term128 _133668 s f b) = (term129 _133668 s f b).
Proof. exact (fun_ext (fun x : _133668 => @lem7138911 _133668 s f x b)). Qed.
Lemma lem7138913 {_133668 : Type'} : (@all _133668) = (@all _133668).
Proof. exact (eq_refl (@all _133668)). Qed.
Lemma lem7138914 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term125 _133668 s f b) = (term130 _133668 s f b).
Proof. exact (MK_COMB (@lem7138913 _133668) (@lem7138912 _133668 s f b)). Qed.
Lemma lem7138915 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term124 _133668 s f b) = (term130 _133668 s f b).
Proof. exact (TRANS (@lem7138907 _133668 s f b) (@lem7138914 _133668 s f b)). Qed.
Lemma lem7138916 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7138917 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term131 _133668 s f b) = (term132 _133668 s f b).
Proof. exact (MK_COMB (@lem7138916) (@lem7138898 _133668 s f b)). Qed.
Lemma lem7138918 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term133 _133668 s f b) = (term134 _133668 s f b).
Proof. exact (MK_COMB (@lem7138917 _133668 s f b) (@lem7138915 _133668 s f b)). Qed.
Lemma lem7138919 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term135 _133668 s f b) = (term133 _133668 s f b).
Proof. exact (@lem17045 (term45 _133668 s f b) (term42 _133668 s f b)). Qed.
Lemma lem7138920 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term135 _133668 s f b) = (term134 _133668 s f b).
Proof. exact (TRANS (@lem7138919 _133668 s f b) (@lem7138918 _133668 s f b)). Qed.
Lemma lem7138922 {_133668 : Type'} (s : _133668 -> Prop) : (term136 _133668 s) = (term136 _133668 s).
Proof. exact (eq_refl (term136 _133668 s)). Qed.
Lemma lem7138923 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term137 _133668 s f b) = (term138 _133668 s f b).
Proof. exact (MK_COMB (@lem7138922 _133668 s) (@lem7138920 _133668 s f b)). Qed.
Lemma lem7138924 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term139 _133668 s f b) = (term137 _133668 s f b).
Proof. exact (@lem17045 (@FINITE _133668 s) (term47 _133668 s f b)). Qed.
Lemma lem7138925 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term139 _133668 s f b) = (term138 _133668 s f b).
Proof. exact (TRANS (@lem7138924 _133668 s f b) (@lem7138923 _133668 s f b)). Qed.
Lemma lem7138926 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term39 _133668 f s b) = (term39 _133668 f s b).
Proof. exact (eq_refl (term39 _133668 f s b)). Qed.
Lemma lem7138927 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7138928 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term140 _133668 s f b) = (term141 _133668 s f b).
Proof. exact (MK_COMB (@lem7138927) (@lem7138925 _133668 s f b)). Qed.
Lemma lem7138929 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term142 _133668 f s b) = (term143 _133668 f s b).
Proof. exact (MK_COMB (@lem7138928 _133668 s f b) (@lem7138926 _133668 f s b)). Qed.
Lemma lem7138930 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term51 _133668 f s b) = (term142 _133668 f s b).
Proof. exact (@lem17265 (term49 _133668 s f b) (term39 _133668 f s b)). Qed.
Lemma lem7138931 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term51 _133668 f s b) = (term143 _133668 f s b).
Proof. exact (TRANS (@lem7138930 _133668 f s b) (@lem7138929 _133668 f s b)). Qed.
Lemma lem7138932 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) : (term52 _133668 f s) = (term144 _133668 f s).
Proof. exact (fun_ext (fun b : real => @lem7138931 _133668 f s b)). Qed.
Lemma lem7138933 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7138934 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) : (term53 _133668 f s) = (term145 _133668 f s).
Proof. exact (MK_COMB (@lem7138933) (@lem7138932 _133668 f s)). Qed.
Lemma lem7138935 {_133668 : Type'} (s : _133668 -> Prop) : (term54 _133668 s) = (term146 _133668 s).
Proof. exact (fun_ext (fun f : _133668 -> real => @lem7138934 _133668 f s)). Qed.
Lemma lem7138936 {_133668 : Type'} : (@all (_133668 -> real)) = (@all (_133668 -> real)).
Proof. exact (eq_refl (@all (_133668 -> real))). Qed.
Lemma lem7138937 {_133668 : Type'} (s : _133668 -> Prop) : (term55 _133668 s) = (term147 _133668 s).
Proof. exact (MK_COMB (@lem7138936 _133668) (@lem7138935 _133668 s)). Qed.
Lemma lem7138938 {_133668 : Type'} : (term56 _133668) = (term148 _133668).
Proof. exact (fun_ext (fun s : _133668 -> Prop => @lem7138937 _133668 s)). Qed.
Lemma lem7138939 {_133668 : Type'} : (@all (_133668 -> Prop)) = (@all (_133668 -> Prop)).
Proof. exact (eq_refl (@all (_133668 -> Prop))). Qed.
Lemma lem7138940 {_133668 : Type'} : (term12 _133668) = (term149 _133668).
Proof. exact (MK_COMB (@lem7138939 _133668) (@lem7138938 _133668)). Qed.
Lemma lem7139095 {A : Type'} (P : A -> Prop) (Q : Prop) : (term150 A P Q) = (term151 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem7139096 {_133668 : Type'} (P : _133668 -> Prop) (Q : Prop) : (term150 _133668 P Q) = (term151 _133668 P Q).
Proof. exact (@lem7139095 _133668 P Q). Qed.
Lemma lem7139097 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term152 _133668 s f b) = (term153 _133668 s f b).
Proof. exact (@lem7139096 _133668 (term118 _133668 s f b) (term130 _133668 s f b)). Qed.
Lemma lem7139098 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (x : _133668) (b : real) : (term154 _133668 s f b x) = (term109 _133668 s f x b).
Proof. exact (eq_refl (term154 _133668 s f b x)). Qed.
Lemma lem7139099 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term155 _133668 s f b) = (term118 _133668 s f b).
Proof. exact (fun_ext (fun x : _133668 => @lem7139098 _133668 s f x b)). Qed.
Lemma lem7139100 {_133668 : Type'} : (@ex _133668) = (@ex _133668).
Proof. exact (eq_refl (@ex _133668)). Qed.
Lemma lem7139101 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term156 _133668 s f b) = (term119 _133668 s f b).
Proof. exact (MK_COMB (@lem7139100 _133668) (@lem7139099 _133668 s f b)). Qed.
Lemma lem7139102 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7139103 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term157 _133668 s f b) = (term132 _133668 s f b).
Proof. exact (MK_COMB (@lem7139102) (@lem7139101 _133668 s f b)). Qed.
Lemma lem7139104 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term130 _133668 s f b) = (term130 _133668 s f b).
Proof. exact (eq_refl (term130 _133668 s f b)). Qed.
Lemma lem7139105 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term152 _133668 s f b) = (term134 _133668 s f b).
Proof. exact (MK_COMB (@lem7139103 _133668 s f b) (@lem7139104 _133668 s f b)). Qed.
Lemma lem7139106 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7139107 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term158 _133668 s f b) = (term159 _133668 s f b).
Proof. exact (MK_COMB (@lem7139106) (@lem7139105 _133668 s f b)). Qed.
Lemma lem7139108 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (x : _133668) (b : real) : (term154 _133668 s f b x) = (term109 _133668 s f x b).
Proof. exact (eq_refl (term154 _133668 s f b x)). Qed.
Lemma lem7139109 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7139110 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (x : _133668) (b : real) : (term160 _133668 s f b x) = (term161 _133668 s f x b).
Proof. exact (MK_COMB (@lem7139109) (@lem7139108 _133668 s f x b)). Qed.
Lemma lem7139111 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term130 _133668 s f b) = (term130 _133668 s f b).
Proof. exact (eq_refl (term130 _133668 s f b)). Qed.
Lemma lem7139112 {_133668 : Type'} (x : _133668) (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term162 _133668 x s f b) = (term163 _133668 x s f b).
Proof. exact (MK_COMB (@lem7139110 _133668 s f x b) (@lem7139111 _133668 s f b)). Qed.
Lemma lem7139113 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term164 _133668 s f b) = (term165 _133668 s f b).
Proof. exact (fun_ext (fun x : _133668 => @lem7139112 _133668 x s f b)). Qed.
Lemma lem7139114 {_133668 : Type'} : (@ex _133668) = (@ex _133668).
Proof. exact (eq_refl (@ex _133668)). Qed.
Lemma lem7139115 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term153 _133668 s f b) = (term166 _133668 s f b).
Proof. exact (MK_COMB (@lem7139114 _133668) (@lem7139113 _133668 s f b)). Qed.
Lemma lem7139116 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : ((term152 _133668 s f b) = (term153 _133668 s f b)) = ((term134 _133668 s f b) = (term166 _133668 s f b)).
Proof. exact (MK_COMB (@lem7139107 _133668 s f b) (@lem7139115 _133668 s f b)). Qed.
Lemma lem7139117 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term134 _133668 s f b) = (term166 _133668 s f b).
Proof. exact (EQ_MP (@lem7139116 _133668 s f b) (@lem7139097 _133668 s f b)). Qed.
Lemma lem7139118 {_133668 : Type'} (s : _133668 -> Prop) : (term136 _133668 s) = (term136 _133668 s).
Proof. exact (eq_refl (term136 _133668 s)). Qed.
Lemma lem7139119 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term138 _133668 s f b) = (term167 _133668 s f b).
Proof. exact (MK_COMB (@lem7139118 _133668 s) (@lem7139117 _133668 s f b)). Qed.
Lemma lem7139121 {A : Type'} (P : Prop) (Q : A -> Prop) : (term168 A P Q) = (term169 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem7139122 {_133668 : Type'} (P : Prop) (Q : _133668 -> Prop) : (term168 _133668 P Q) = (term169 _133668 P Q).
Proof. exact (@lem7139121 _133668 P Q). Qed.
Lemma lem7139123 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term170 _133668 s f b) = (term171 _133668 s f b).
Proof. exact (@lem7139122 _133668 (term172 _133668 s) (term165 _133668 s f b)). Qed.
Lemma lem7139124 {_133668 : Type'} (x : _133668) (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term173 _133668 s f b x) = (term163 _133668 x s f b).
Proof. exact (eq_refl (term173 _133668 s f b x)). Qed.
Lemma lem7139125 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term174 _133668 s f b) = (term165 _133668 s f b).
Proof. exact (fun_ext (fun x : _133668 => @lem7139124 _133668 x s f b)). Qed.
Lemma lem7139126 {_133668 : Type'} : (@ex _133668) = (@ex _133668).
Proof. exact (eq_refl (@ex _133668)). Qed.
Lemma lem7139127 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term175 _133668 s f b) = (term166 _133668 s f b).
Proof. exact (MK_COMB (@lem7139126 _133668) (@lem7139125 _133668 s f b)). Qed.
Lemma lem7139128 {_133668 : Type'} (s : _133668 -> Prop) : (term136 _133668 s) = (term136 _133668 s).
Proof. exact (eq_refl (term136 _133668 s)). Qed.
Lemma lem7139129 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term170 _133668 s f b) = (term167 _133668 s f b).
Proof. exact (MK_COMB (@lem7139128 _133668 s) (@lem7139127 _133668 s f b)). Qed.
Lemma lem7139130 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7139131 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term176 _133668 s f b) = (term177 _133668 s f b).
Proof. exact (MK_COMB (@lem7139130) (@lem7139129 _133668 s f b)). Qed.
Lemma lem7139132 {_133668 : Type'} (x : _133668) (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term173 _133668 s f b x) = (term163 _133668 x s f b).
Proof. exact (eq_refl (term173 _133668 s f b x)). Qed.
Lemma lem7139133 {_133668 : Type'} (s : _133668 -> Prop) : (term136 _133668 s) = (term136 _133668 s).
Proof. exact (eq_refl (term136 _133668 s)). Qed.
Lemma lem7139134 {_133668 : Type'} (x : _133668) (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term178 _133668 s f b x) = (term179 _133668 x s f b).
Proof. exact (MK_COMB (@lem7139133 _133668 s) (@lem7139132 _133668 x s f b)). Qed.
Lemma lem7139135 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term180 _133668 s f b) = (term181 _133668 s f b).
Proof. exact (fun_ext (fun x : _133668 => @lem7139134 _133668 x s f b)). Qed.
Lemma lem7139136 {_133668 : Type'} : (@ex _133668) = (@ex _133668).
Proof. exact (eq_refl (@ex _133668)). Qed.
Lemma lem7139137 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term171 _133668 s f b) = (term182 _133668 s f b).
Proof. exact (MK_COMB (@lem7139136 _133668) (@lem7139135 _133668 s f b)). Qed.
Lemma lem7139138 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : ((term170 _133668 s f b) = (term171 _133668 s f b)) = ((term167 _133668 s f b) = (term182 _133668 s f b)).
Proof. exact (MK_COMB (@lem7139131 _133668 s f b) (@lem7139137 _133668 s f b)). Qed.
Lemma lem7139139 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term167 _133668 s f b) = (term182 _133668 s f b).
Proof. exact (EQ_MP (@lem7139138 _133668 s f b) (@lem7139123 _133668 s f b)). Qed.
Lemma lem7139140 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term138 _133668 s f b) = (term182 _133668 s f b).
Proof. exact (TRANS (@lem7139119 _133668 s f b) (@lem7139139 _133668 s f b)). Qed.
Lemma lem7139141 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7139142 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term141 _133668 s f b) = (term183 _133668 s f b).
Proof. exact (MK_COMB (@lem7139141) (@lem7139140 _133668 s f b)). Qed.
Lemma lem7139143 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term39 _133668 f s b) = (term39 _133668 f s b).
Proof. exact (eq_refl (term39 _133668 f s b)). Qed.
Lemma lem7139144 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term143 _133668 f s b) = (term184 _133668 f s b).
Proof. exact (MK_COMB (@lem7139142 _133668 s f b) (@lem7139143 _133668 f s b)). Qed.
Lemma lem7139146 {A : Type'} (P : A -> Prop) (Q : Prop) : (term150 A P Q) = (term151 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem7139147 {_133668 : Type'} (P : _133668 -> Prop) (Q : Prop) : (term150 _133668 P Q) = (term151 _133668 P Q).
Proof. exact (@lem7139146 _133668 P Q). Qed.
Lemma lem7139148 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term185 _133668 f s b) = (term186 _133668 f s b).
Proof. exact (@lem7139147 _133668 (term181 _133668 s f b) (term39 _133668 f s b)). Qed.
Lemma lem7139149 {_133668 : Type'} (x : _133668) (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term187 _133668 s f b x) = (term179 _133668 x s f b).
Proof. exact (eq_refl (term187 _133668 s f b x)). Qed.
Lemma lem7139150 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term188 _133668 s f b) = (term181 _133668 s f b).
Proof. exact (fun_ext (fun x : _133668 => @lem7139149 _133668 x s f b)). Qed.
Lemma lem7139151 {_133668 : Type'} : (@ex _133668) = (@ex _133668).
Proof. exact (eq_refl (@ex _133668)). Qed.
Lemma lem7139152 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term189 _133668 s f b) = (term182 _133668 s f b).
Proof. exact (MK_COMB (@lem7139151 _133668) (@lem7139150 _133668 s f b)). Qed.
Lemma lem7139153 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7139154 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term190 _133668 s f b) = (term183 _133668 s f b).
Proof. exact (MK_COMB (@lem7139153) (@lem7139152 _133668 s f b)). Qed.
Lemma lem7139155 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term39 _133668 f s b) = (term39 _133668 f s b).
Proof. exact (eq_refl (term39 _133668 f s b)). Qed.
Lemma lem7139156 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term185 _133668 f s b) = (term184 _133668 f s b).
Proof. exact (MK_COMB (@lem7139154 _133668 s f b) (@lem7139155 _133668 f s b)). Qed.
Lemma lem7139157 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7139158 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term191 _133668 f s b) = (term192 _133668 f s b).
Proof. exact (MK_COMB (@lem7139157) (@lem7139156 _133668 f s b)). Qed.
Lemma lem7139159 {_133668 : Type'} (x : _133668) (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term187 _133668 s f b x) = (term179 _133668 x s f b).
Proof. exact (eq_refl (term187 _133668 s f b x)). Qed.
Lemma lem7139160 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7139161 {_133668 : Type'} (x : _133668) (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term193 _133668 s f b x) = (term194 _133668 x s f b).
Proof. exact (MK_COMB (@lem7139160) (@lem7139159 _133668 x s f b)). Qed.
Lemma lem7139162 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term39 _133668 f s b) = (term39 _133668 f s b).
Proof. exact (eq_refl (term39 _133668 f s b)). Qed.
Lemma lem7139163 {_133668 : Type'} (x : _133668) (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term195 _133668 x f s b) = (term196 _133668 x f s b).
Proof. exact (MK_COMB (@lem7139161 _133668 x s f b) (@lem7139162 _133668 f s b)). Qed.
Lemma lem7139164 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term197 _133668 f s b) = (term198 _133668 f s b).
Proof. exact (fun_ext (fun x : _133668 => @lem7139163 _133668 x f s b)). Qed.
Lemma lem7139165 {_133668 : Type'} : (@ex _133668) = (@ex _133668).
Proof. exact (eq_refl (@ex _133668)). Qed.
Lemma lem7139166 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term186 _133668 f s b) = (term199 _133668 f s b).
Proof. exact (MK_COMB (@lem7139165 _133668) (@lem7139164 _133668 f s b)). Qed.
Lemma lem7139167 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : ((term185 _133668 f s b) = (term186 _133668 f s b)) = ((term184 _133668 f s b) = (term199 _133668 f s b)).
Proof. exact (MK_COMB (@lem7139158 _133668 f s b) (@lem7139166 _133668 f s b)). Qed.
Lemma lem7139168 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term184 _133668 f s b) = (term199 _133668 f s b).
Proof. exact (EQ_MP (@lem7139167 _133668 f s b) (@lem7139148 _133668 f s b)). Qed.
Lemma lem7139169 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term143 _133668 f s b) = (term199 _133668 f s b).
Proof. exact (TRANS (@lem7139144 _133668 f s b) (@lem7139168 _133668 f s b)). Qed.
Lemma lem7139170 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) : (term144 _133668 f s) = (term200 _133668 f s).
Proof. exact (fun_ext (fun b : real => @lem7139169 _133668 f s b)). Qed.
Lemma lem7139171 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7139172 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) : (term145 _133668 f s) = (term201 _133668 f s).
Proof. exact (MK_COMB (@lem7139171) (@lem7139170 _133668 f s)). Qed.
Lemma lem7139174 {A B : Type'} (P : type1413 A B) : (term202 A B P) = (term203 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7139175 {_133668 : Type'} (P : type1620 _133668) : (term204 _133668 P) = (term205 _133668 P).
Proof. exact (@lem7139174 real _133668 P). Qed.
Lemma lem7139176 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) : (term206 _133668 f s) = (term207 _133668 f s).
Proof. exact (@lem7139175 _133668 (term208 _133668 f s)). Qed.
Lemma lem7139177 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term209 _133668 f s b) = (term198 _133668 f s b).
Proof. exact (eq_refl (term209 _133668 f s b)). Qed.
Lemma lem7139178 {_133668 : Type'} (x : _133668) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7139179 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) (x : _133668) : (term210 _133668 f s b x) = (term211 _133668 f s b x).
Proof. exact (MK_COMB (@lem7139177 _133668 f s b) (@lem7139178 _133668 x)). Qed.
Lemma lem7139180 {_133668 : Type'} (x : _133668) (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term211 _133668 f s b x) = (term196 _133668 x f s b).
Proof. exact (eq_refl (term211 _133668 f s b x)). Qed.
Lemma lem7139181 {_133668 : Type'} (x : _133668) (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term210 _133668 f s b x) = (term196 _133668 x f s b).
Proof. exact (TRANS (@lem7139179 _133668 f s b x) (@lem7139180 _133668 x f s b)). Qed.
Lemma lem7139182 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term212 _133668 f s b) = (term198 _133668 f s b).
Proof. exact (fun_ext (fun x : _133668 => @lem7139181 _133668 x f s b)). Qed.
Lemma lem7139183 {_133668 : Type'} : (@ex _133668) = (@ex _133668).
Proof. exact (eq_refl (@ex _133668)). Qed.
Lemma lem7139184 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term213 _133668 f s b) = (term199 _133668 f s b).
Proof. exact (MK_COMB (@lem7139183 _133668) (@lem7139182 _133668 f s b)). Qed.
Lemma lem7139185 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) : (term214 _133668 f s) = (term200 _133668 f s).
Proof. exact (fun_ext (fun b : real => @lem7139184 _133668 f s b)). Qed.
Lemma lem7139186 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7139187 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) : (term206 _133668 f s) = (term201 _133668 f s).
Proof. exact (MK_COMB (@lem7139186) (@lem7139185 _133668 f s)). Qed.
Lemma lem7139188 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7139189 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) : (term215 _133668 f s) = (term216 _133668 f s).
Proof. exact (MK_COMB (@lem7139188) (@lem7139187 _133668 f s)). Qed.
Lemma lem7139190 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term209 _133668 f s b) = (term198 _133668 f s b).
Proof. exact (eq_refl (term209 _133668 f s b)). Qed.
Lemma lem7139191 {_133668 : Type'} (x : real -> _133668) (b : real) : (x b) = (x b).
Proof. exact (eq_refl (x b)). Qed.
Lemma lem7139192 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (x : real -> _133668) (b : real) : (term217 _133668 f s x b) = (term218 _133668 f s x b).
Proof. exact (MK_COMB (@lem7139190 _133668 f s b) (@lem7139191 _133668 x b)). Qed.
Lemma lem7139193 {_133668 : Type'} (x : real -> _133668) (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term218 _133668 f s x b) = (term219 _133668 x f s b).
Proof. exact (eq_refl (term218 _133668 f s x b)). Qed.
Lemma lem7139194 {_133668 : Type'} (x : real -> _133668) (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term217 _133668 f s x b) = (term219 _133668 x f s b).
Proof. exact (TRANS (@lem7139192 _133668 f s x b) (@lem7139193 _133668 x f s b)). Qed.
Lemma lem7139195 {_133668 : Type'} (x : real -> _133668) (f : _133668 -> real) (s : _133668 -> Prop) : (term220 _133668 f s x) = (term221 _133668 x f s).
Proof. exact (fun_ext (fun b : real => @lem7139194 _133668 x f s b)). Qed.
Lemma lem7139196 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7139197 {_133668 : Type'} (x : real -> _133668) (f : _133668 -> real) (s : _133668 -> Prop) : (term222 _133668 f s x) = (term223 _133668 x f s).
Proof. exact (MK_COMB (@lem7139196) (@lem7139195 _133668 x f s)). Qed.
Lemma lem7139198 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) : (term224 _133668 f s) = (term225 _133668 f s).
Proof. exact (fun_ext (fun x : real -> _133668 => @lem7139197 _133668 x f s)). Qed.
Lemma lem7139199 {_133668 : Type'} : (@ex (real -> _133668)) = (@ex (real -> _133668)).
Proof. exact (eq_refl (@ex (real -> _133668))). Qed.
Lemma lem7139200 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) : (term207 _133668 f s) = (term226 _133668 f s).
Proof. exact (MK_COMB (@lem7139199 _133668) (@lem7139198 _133668 f s)). Qed.
Lemma lem7139201 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) : ((term206 _133668 f s) = (term207 _133668 f s)) = ((term201 _133668 f s) = (term226 _133668 f s)).
Proof. exact (MK_COMB (@lem7139189 _133668 f s) (@lem7139200 _133668 f s)). Qed.
Lemma lem7139202 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) : (term201 _133668 f s) = (term226 _133668 f s).
Proof. exact (EQ_MP (@lem7139201 _133668 f s) (@lem7139176 _133668 f s)). Qed.
Lemma lem7139203 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) : (term145 _133668 f s) = (term226 _133668 f s).
Proof. exact (TRANS (@lem7139172 _133668 f s) (@lem7139202 _133668 f s)). Qed.
Lemma lem7139204 {_133668 : Type'} (s : _133668 -> Prop) : (term146 _133668 s) = (term227 _133668 s).
Proof. exact (fun_ext (fun f : _133668 -> real => @lem7139203 _133668 f s)). Qed.
Lemma lem7139205 {_133668 : Type'} : (@all (_133668 -> real)) = (@all (_133668 -> real)).
Proof. exact (eq_refl (@all (_133668 -> real))). Qed.
Lemma lem7139206 {_133668 : Type'} (s : _133668 -> Prop) : (term147 _133668 s) = (term228 _133668 s).
Proof. exact (MK_COMB (@lem7139205 _133668) (@lem7139204 _133668 s)). Qed.
Lemma lem7139208 {A B : Type'} (P : type1413 A B) : (term202 A B P) = (term203 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7139209 {_133668 : Type'} (P : type713 _133668) : (term229 _133668 P) = (term230 _133668 P).
Proof. exact (@lem7139208 (_133668 -> real) (real -> _133668) P). Qed.
Lemma lem7139210 {_133668 : Type'} (s : _133668 -> Prop) : (term231 _133668 s) = (term232 _133668 s).
Proof. exact (@lem7139209 _133668 (term233 _133668 s)). Qed.
Lemma lem7139211 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) : (term234 _133668 s f) = (term225 _133668 f s).
Proof. exact (eq_refl (term234 _133668 s f)). Qed.
Lemma lem7139212 {_133668 : Type'} (x : real -> _133668) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7139213 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (x : real -> _133668) : (term235 _133668 s f x) = (term236 _133668 f s x).
Proof. exact (MK_COMB (@lem7139211 _133668 f s) (@lem7139212 _133668 x)). Qed.
Lemma lem7139214 {_133668 : Type'} (x : real -> _133668) (f : _133668 -> real) (s : _133668 -> Prop) : (term236 _133668 f s x) = (term223 _133668 x f s).
Proof. exact (eq_refl (term236 _133668 f s x)). Qed.
Lemma lem7139215 {_133668 : Type'} (x : real -> _133668) (f : _133668 -> real) (s : _133668 -> Prop) : (term235 _133668 s f x) = (term223 _133668 x f s).
Proof. exact (TRANS (@lem7139213 _133668 f s x) (@lem7139214 _133668 x f s)). Qed.
Lemma lem7139216 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) : (term237 _133668 s f) = (term225 _133668 f s).
Proof. exact (fun_ext (fun x : real -> _133668 => @lem7139215 _133668 x f s)). Qed.
Lemma lem7139217 {_133668 : Type'} : (@ex (real -> _133668)) = (@ex (real -> _133668)).
Proof. exact (eq_refl (@ex (real -> _133668))). Qed.
Lemma lem7139218 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) : (term238 _133668 s f) = (term226 _133668 f s).
Proof. exact (MK_COMB (@lem7139217 _133668) (@lem7139216 _133668 f s)). Qed.
Lemma lem7139219 {_133668 : Type'} (s : _133668 -> Prop) : (term239 _133668 s) = (term227 _133668 s).
Proof. exact (fun_ext (fun f : _133668 -> real => @lem7139218 _133668 f s)). Qed.
Lemma lem7139220 {_133668 : Type'} : (@all (_133668 -> real)) = (@all (_133668 -> real)).
Proof. exact (eq_refl (@all (_133668 -> real))). Qed.
Lemma lem7139221 {_133668 : Type'} (s : _133668 -> Prop) : (term231 _133668 s) = (term228 _133668 s).
Proof. exact (MK_COMB (@lem7139220 _133668) (@lem7139219 _133668 s)). Qed.
Lemma lem7139222 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7139223 {_133668 : Type'} (s : _133668 -> Prop) : (term240 _133668 s) = (term241 _133668 s).
Proof. exact (MK_COMB (@lem7139222) (@lem7139221 _133668 s)). Qed.
Lemma lem7139224 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) : (term234 _133668 s f) = (term225 _133668 f s).
Proof. exact (eq_refl (term234 _133668 s f)). Qed.
Lemma lem7139225 {_133668 : Type'} (x : type715 _133668) (f : _133668 -> real) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem7139226 {_133668 : Type'} (s : _133668 -> Prop) (x : type715 _133668) (f : _133668 -> real) : (term242 _133668 s x f) = (term243 _133668 s x f).
Proof. exact (MK_COMB (@lem7139224 _133668 f s) (@lem7139225 _133668 x f)). Qed.
Lemma lem7139227 {_133668 : Type'} (x : type715 _133668) (f : _133668 -> real) (s : _133668 -> Prop) : (term243 _133668 s x f) = (term244 _133668 x f s).
Proof. exact (eq_refl (term243 _133668 s x f)). Qed.
Lemma lem7139228 {_133668 : Type'} (x : type715 _133668) (f : _133668 -> real) (s : _133668 -> Prop) : (term242 _133668 s x f) = (term244 _133668 x f s).
Proof. exact (TRANS (@lem7139226 _133668 s x f) (@lem7139227 _133668 x f s)). Qed.
Lemma lem7139229 {_133668 : Type'} (x : type715 _133668) (s : _133668 -> Prop) : (term245 _133668 s x) = (term246 _133668 x s).
Proof. exact (fun_ext (fun f : _133668 -> real => @lem7139228 _133668 x f s)). Qed.
Lemma lem7139230 {_133668 : Type'} : (@all (_133668 -> real)) = (@all (_133668 -> real)).
Proof. exact (eq_refl (@all (_133668 -> real))). Qed.
Lemma lem7139231 {_133668 : Type'} (x : type715 _133668) (s : _133668 -> Prop) : (term247 _133668 s x) = (term248 _133668 x s).
Proof. exact (MK_COMB (@lem7139230 _133668) (@lem7139229 _133668 x s)). Qed.
Lemma lem7139232 {_133668 : Type'} (s : _133668 -> Prop) : (term249 _133668 s) = (term250 _133668 s).
Proof. exact (fun_ext (fun x : type715 _133668 => @lem7139231 _133668 x s)). Qed.
Lemma lem7139233 {_133668 : Type'} : (@ex ((_133668 -> real) -> real -> _133668)) = (@ex ((_133668 -> real) -> real -> _133668)).
Proof. exact (eq_refl (@ex ((_133668 -> real) -> real -> _133668))). Qed.
Lemma lem7139234 {_133668 : Type'} (s : _133668 -> Prop) : (term232 _133668 s) = (term251 _133668 s).
Proof. exact (MK_COMB (@lem7139233 _133668) (@lem7139232 _133668 s)). Qed.
Lemma lem7139235 {_133668 : Type'} (s : _133668 -> Prop) : ((term231 _133668 s) = (term232 _133668 s)) = ((term228 _133668 s) = (term251 _133668 s)).
Proof. exact (MK_COMB (@lem7139223 _133668 s) (@lem7139234 _133668 s)). Qed.
Lemma lem7139236 {_133668 : Type'} (s : _133668 -> Prop) : (term228 _133668 s) = (term251 _133668 s).
Proof. exact (EQ_MP (@lem7139235 _133668 s) (@lem7139210 _133668 s)). Qed.
Lemma lem7139237 {_133668 : Type'} (s : _133668 -> Prop) : (term147 _133668 s) = (term251 _133668 s).
Proof. exact (TRANS (@lem7139206 _133668 s) (@lem7139236 _133668 s)). Qed.
Lemma lem7139238 {_133668 : Type'} : (term148 _133668) = (term252 _133668).
Proof. exact (fun_ext (fun s : _133668 -> Prop => @lem7139237 _133668 s)). Qed.
Lemma lem7139239 {_133668 : Type'} : (@all (_133668 -> Prop)) = (@all (_133668 -> Prop)).
Proof. exact (eq_refl (@all (_133668 -> Prop))). Qed.
Lemma lem7139240 {_133668 : Type'} : (term149 _133668) = (term253 _133668).
Proof. exact (MK_COMB (@lem7139239 _133668) (@lem7139238 _133668)). Qed.
Lemma lem7139242 {A B : Type'} (P : type1413 A B) : (term202 A B P) = (term203 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7139243 {_133668 : Type'} (P : type603 _133668) : (term254 _133668 P) = (term255 _133668 P).
Proof. exact (@lem7139242 (_133668 -> Prop) (type715 _133668) P). Qed.
Lemma lem7139244 {_133668 : Type'} : (term256 _133668) = (term257 _133668).
Proof. exact (@lem7139243 _133668 (term258 _133668)). Qed.
Lemma lem7139245 {_133668 : Type'} (s : _133668 -> Prop) : (term259 _133668 s) = (term250 _133668 s).
Proof. exact (eq_refl (term259 _133668 s)). Qed.
Lemma lem7139246 {_133668 : Type'} (x : type715 _133668) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7139247 {_133668 : Type'} (s : _133668 -> Prop) (x : type715 _133668) : (term260 _133668 s x) = (term261 _133668 s x).
Proof. exact (MK_COMB (@lem7139245 _133668 s) (@lem7139246 _133668 x)). Qed.
Lemma lem7139248 {_133668 : Type'} (x : type715 _133668) (s : _133668 -> Prop) : (term261 _133668 s x) = (term248 _133668 x s).
Proof. exact (eq_refl (term261 _133668 s x)). Qed.
Lemma lem7139249 {_133668 : Type'} (x : type715 _133668) (s : _133668 -> Prop) : (term260 _133668 s x) = (term248 _133668 x s).
Proof. exact (TRANS (@lem7139247 _133668 s x) (@lem7139248 _133668 x s)). Qed.
Lemma lem7139250 {_133668 : Type'} (s : _133668 -> Prop) : (term262 _133668 s) = (term250 _133668 s).
Proof. exact (fun_ext (fun x : type715 _133668 => @lem7139249 _133668 x s)). Qed.
Lemma lem7139251 {_133668 : Type'} : (@ex ((_133668 -> real) -> real -> _133668)) = (@ex ((_133668 -> real) -> real -> _133668)).
Proof. exact (eq_refl (@ex ((_133668 -> real) -> real -> _133668))). Qed.
Lemma lem7139252 {_133668 : Type'} (s : _133668 -> Prop) : (term263 _133668 s) = (term251 _133668 s).
Proof. exact (MK_COMB (@lem7139251 _133668) (@lem7139250 _133668 s)). Qed.
Lemma lem7139253 {_133668 : Type'} : (term264 _133668) = (term252 _133668).
Proof. exact (fun_ext (fun s : _133668 -> Prop => @lem7139252 _133668 s)). Qed.
Lemma lem7139254 {_133668 : Type'} : (@all (_133668 -> Prop)) = (@all (_133668 -> Prop)).
Proof. exact (eq_refl (@all (_133668 -> Prop))). Qed.
Lemma lem7139255 {_133668 : Type'} : (term256 _133668) = (term253 _133668).
Proof. exact (MK_COMB (@lem7139254 _133668) (@lem7139253 _133668)). Qed.
Lemma lem7139256 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7139257 {_133668 : Type'} : (term265 _133668) = (term266 _133668).
Proof. exact (MK_COMB (@lem7139256) (@lem7139255 _133668)). Qed.
Lemma lem7139258 {_133668 : Type'} (s : _133668 -> Prop) : (term259 _133668 s) = (term250 _133668 s).
Proof. exact (eq_refl (term259 _133668 s)). Qed.
Lemma lem7139259 {_133668 : Type'} (x : type645 _133668) (s : _133668 -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem7139260 {_133668 : Type'} (x : type645 _133668) (s : _133668 -> Prop) : (term267 _133668 x s) = (term268 _133668 x s).
Proof. exact (MK_COMB (@lem7139258 _133668 s) (@lem7139259 _133668 x s)). Qed.
Lemma lem7139261 {_133668 : Type'} (x : type645 _133668) (s : _133668 -> Prop) : (term268 _133668 x s) = (term269 _133668 x s).
Proof. exact (eq_refl (term268 _133668 x s)). Qed.
Lemma lem7139262 {_133668 : Type'} (x : type645 _133668) (s : _133668 -> Prop) : (term267 _133668 x s) = (term269 _133668 x s).
Proof. exact (TRANS (@lem7139260 _133668 x s) (@lem7139261 _133668 x s)). Qed.
Lemma lem7139263 {_133668 : Type'} (x : type645 _133668) : (term270 _133668 x) = (term271 _133668 x).
Proof. exact (fun_ext (fun s : _133668 -> Prop => @lem7139262 _133668 x s)). Qed.
Lemma lem7139264 {_133668 : Type'} : (@all (_133668 -> Prop)) = (@all (_133668 -> Prop)).
Proof. exact (eq_refl (@all (_133668 -> Prop))). Qed.
Lemma lem7139265 {_133668 : Type'} (x : type645 _133668) : (term272 _133668 x) = (term273 _133668 x).
Proof. exact (MK_COMB (@lem7139264 _133668) (@lem7139263 _133668 x)). Qed.
Lemma lem7139266 {_133668 : Type'} : (term274 _133668) = (term275 _133668).
Proof. exact (fun_ext (fun x : type645 _133668 => @lem7139265 _133668 x)). Qed.
Lemma lem7139267 {_133668 : Type'} : (@ex ((_133668 -> Prop) -> (_133668 -> real) -> real -> _133668)) = (@ex ((_133668 -> Prop) -> (_133668 -> real) -> real -> _133668)).
Proof. exact (eq_refl (@ex ((_133668 -> Prop) -> (_133668 -> real) -> real -> _133668))). Qed.
Lemma lem7139268 {_133668 : Type'} : (term257 _133668) = (term276 _133668).
Proof. exact (MK_COMB (@lem7139267 _133668) (@lem7139266 _133668)). Qed.
Lemma lem7139269 {_133668 : Type'} : ((term256 _133668) = (term257 _133668)) = ((term253 _133668) = (term276 _133668)).
Proof. exact (MK_COMB (@lem7139257 _133668) (@lem7139268 _133668)). Qed.
Lemma lem7139270 {_133668 : Type'} : (term253 _133668) = (term276 _133668).
Proof. exact (EQ_MP (@lem7139269 _133668) (@lem7139244 _133668)). Qed.
Lemma lem7139272 {_133668 : Type'} : (term149 _133668) = (term276 _133668).
Proof. exact (TRANS (@lem7139240 _133668) (@lem7139270 _133668)). Qed.
Lemma lem7139273 {_133668 : Type'} : (term12 _133668) = (term276 _133668).
Proof. exact (TRANS (@lem7138940 _133668) (@lem7139272 _133668)). Qed.
Lemma lem7139274 {_133668 : Type'} (h1 : term12 _133668) : term276 _133668.
Proof. exact (EQ_MP (@lem7139273 _133668) (@lem7138714 _133668 h1)). Qed.
Lemma lem7139282 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) : (term108 A s f x b) = (term109 A s f x b).
Proof. exact (@lem17362 (@IN A x s) (term110 A f x b)). Qed.
Lemma lem7139283 {A : Type'} (P : A -> Prop) : (term111 A P) = (term112 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem7139284 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term113 A s f b) = (term114 A s f b).
Proof. exact (@lem7139283 A (term44 A s f b)). Qed.
Lemma lem7139285 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) : (term115 A s f b x) = (term43 A s f x b).
Proof. exact (eq_refl (term115 A s f b x)). Qed.
Lemma lem7139286 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7139287 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) : (term116 A s f b x) = (term108 A s f x b).
Proof. exact (MK_COMB (@lem7139286) (@lem7139285 A s f x b)). Qed.
Lemma lem7139288 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) : (term116 A s f b x) = (term109 A s f x b).
Proof. exact (TRANS (@lem7139287 A s f x b) (@lem7139282 A s f x b)). Qed.
Lemma lem7139289 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term117 A s f b) = (term118 A s f b).
Proof. exact (fun_ext (fun x : A => @lem7139288 A s f x b)). Qed.
Lemma lem7139290 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7139291 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term114 A s f b) = (term119 A s f b).
Proof. exact (MK_COMB (@lem7139290 A) (@lem7139289 A s f b)). Qed.
Lemma lem7139292 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term113 A s f b) = (term119 A s f b).
Proof. exact (TRANS (@lem7139284 A s f b) (@lem7139291 A s f b)). Qed.
Lemma lem7139299 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) : (term120 A s f x b) = (term121 A s f x b).
Proof. exact (@lem17045 (@IN A x s) (term71 A f x b)). Qed.
Lemma lem7139300 {A : Type'} (P : A -> Prop) : (term122 A P) = (term123 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem7139301 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term124 A s f b) = (term125 A s f b).
Proof. exact (@lem7139300 A (term41 A s f b)). Qed.
Lemma lem7139302 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) : (term126 A s f b x) = (term40 A s f x b).
Proof. exact (eq_refl (term126 A s f b x)). Qed.
Lemma lem7139303 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7139304 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) : (term127 A s f b x) = (term120 A s f x b).
Proof. exact (MK_COMB (@lem7139303) (@lem7139302 A s f x b)). Qed.
Lemma lem7139305 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) : (term127 A s f b x) = (term121 A s f x b).
Proof. exact (TRANS (@lem7139304 A s f x b) (@lem7139299 A s f x b)). Qed.
Lemma lem7139306 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term128 A s f b) = (term129 A s f b).
Proof. exact (fun_ext (fun x : A => @lem7139305 A s f x b)). Qed.
Lemma lem7139307 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7139308 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term125 A s f b) = (term130 A s f b).
Proof. exact (MK_COMB (@lem7139307 A) (@lem7139306 A s f b)). Qed.
Lemma lem7139309 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term124 A s f b) = (term130 A s f b).
Proof. exact (TRANS (@lem7139301 A s f b) (@lem7139308 A s f b)). Qed.
Lemma lem7139310 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7139311 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term131 A s f b) = (term132 A s f b).
Proof. exact (MK_COMB (@lem7139310) (@lem7139292 A s f b)). Qed.
Lemma lem7139312 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term133 A s f b) = (term134 A s f b).
Proof. exact (MK_COMB (@lem7139311 A s f b) (@lem7139309 A s f b)). Qed.
Lemma lem7139313 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term135 A s f b) = (term133 A s f b).
Proof. exact (@lem17045 (term45 A s f b) (term42 A s f b)). Qed.
Lemma lem7139314 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term135 A s f b) = (term134 A s f b).
Proof. exact (TRANS (@lem7139313 A s f b) (@lem7139312 A s f b)). Qed.
Lemma lem7139316 {A : Type'} (s : A -> Prop) : (term136 A s) = (term136 A s).
Proof. exact (eq_refl (term136 A s)). Qed.
Lemma lem7139317 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term137 A s f b) = (term138 A s f b).
Proof. exact (MK_COMB (@lem7139316 A s) (@lem7139314 A s f b)). Qed.
Lemma lem7139318 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term139 A s f b) = (term137 A s f b).
Proof. exact (@lem17045 (@FINITE A s) (term47 A s f b)). Qed.
Lemma lem7139319 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term139 A s f b) = (term138 A s f b).
Proof. exact (TRANS (@lem7139318 A s f b) (@lem7139317 A s f b)). Qed.
Lemma lem7139320 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term39 A f s b) = (term39 A f s b).
Proof. exact (eq_refl (term39 A f s b)). Qed.
Lemma lem7139321 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7139322 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term140 A s f b) = (term141 A s f b).
Proof. exact (MK_COMB (@lem7139321) (@lem7139319 A s f b)). Qed.
Lemma lem7139323 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term142 A f s b) = (term143 A f s b).
Proof. exact (MK_COMB (@lem7139322 A s f b) (@lem7139320 A f s b)). Qed.
Lemma lem7139324 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term51 A f s b) = (term142 A f s b).
Proof. exact (@lem17265 (term49 A s f b) (term39 A f s b)). Qed.
Lemma lem7139325 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term51 A f s b) = (term143 A f s b).
Proof. exact (TRANS (@lem7139324 A f s b) (@lem7139323 A f s b)). Qed.
Lemma lem7139326 {A : Type'} (f : A -> real) (s : A -> Prop) : (term52 A f s) = (term144 A f s).
Proof. exact (fun_ext (fun b : real => @lem7139325 A f s b)). Qed.
Lemma lem7139327 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7139328 {A : Type'} (f : A -> real) (s : A -> Prop) : (term53 A f s) = (term145 A f s).
Proof. exact (MK_COMB (@lem7139327) (@lem7139326 A f s)). Qed.
Lemma lem7139329 {A : Type'} (s : A -> Prop) : (term54 A s) = (term146 A s).
Proof. exact (fun_ext (fun f : A -> real => @lem7139328 A f s)). Qed.
Lemma lem7139330 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7139331 {A : Type'} (s : A -> Prop) : (term55 A s) = (term147 A s).
Proof. exact (MK_COMB (@lem7139330 A) (@lem7139329 A s)). Qed.
Lemma lem7139332 {A : Type'} : (term56 A) = (term148 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7139331 A s)). Qed.
Lemma lem7139333 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7139334 {A : Type'} : (term12 A) = (term149 A).
Proof. exact (MK_COMB (@lem7139333 A) (@lem7139332 A)). Qed.
Lemma lem7139489 {A : Type'} (P : A -> Prop) (Q : Prop) : (term150 A P Q) = (term151 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem7139490 {A : Type'} (P : A -> Prop) (Q : Prop) : (term150 A P Q) = (term151 A P Q).
Proof. exact (@lem7139489 A P Q). Qed.
Lemma lem7139491 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term152 A s f b) = (term153 A s f b).
Proof. exact (@lem7139490 A (term118 A s f b) (term130 A s f b)). Qed.
Lemma lem7139492 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) : (term154 A s f b x) = (term109 A s f x b).
Proof. exact (eq_refl (term154 A s f b x)). Qed.
Lemma lem7139493 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term155 A s f b) = (term118 A s f b).
Proof. exact (fun_ext (fun x : A => @lem7139492 A s f x b)). Qed.
Lemma lem7139494 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7139495 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term156 A s f b) = (term119 A s f b).
Proof. exact (MK_COMB (@lem7139494 A) (@lem7139493 A s f b)). Qed.
Lemma lem7139496 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7139497 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term157 A s f b) = (term132 A s f b).
Proof. exact (MK_COMB (@lem7139496) (@lem7139495 A s f b)). Qed.
Lemma lem7139498 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term130 A s f b) = (term130 A s f b).
Proof. exact (eq_refl (term130 A s f b)). Qed.
Lemma lem7139499 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term152 A s f b) = (term134 A s f b).
Proof. exact (MK_COMB (@lem7139497 A s f b) (@lem7139498 A s f b)). Qed.
Lemma lem7139500 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7139501 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term158 A s f b) = (term159 A s f b).
Proof. exact (MK_COMB (@lem7139500) (@lem7139499 A s f b)). Qed.
Lemma lem7139502 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) : (term154 A s f b x) = (term109 A s f x b).
Proof. exact (eq_refl (term154 A s f b x)). Qed.
Lemma lem7139503 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7139504 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) : (term160 A s f b x) = (term161 A s f x b).
Proof. exact (MK_COMB (@lem7139503) (@lem7139502 A s f x b)). Qed.
Lemma lem7139505 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term130 A s f b) = (term130 A s f b).
Proof. exact (eq_refl (term130 A s f b)). Qed.
Lemma lem7139506 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term162 A x s f b) = (term163 A x s f b).
Proof. exact (MK_COMB (@lem7139504 A s f x b) (@lem7139505 A s f b)). Qed.
Lemma lem7139507 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term164 A s f b) = (term165 A s f b).
Proof. exact (fun_ext (fun x : A => @lem7139506 A x s f b)). Qed.
Lemma lem7139508 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7139509 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term153 A s f b) = (term166 A s f b).
Proof. exact (MK_COMB (@lem7139508 A) (@lem7139507 A s f b)). Qed.
Lemma lem7139510 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : ((term152 A s f b) = (term153 A s f b)) = ((term134 A s f b) = (term166 A s f b)).
Proof. exact (MK_COMB (@lem7139501 A s f b) (@lem7139509 A s f b)). Qed.
Lemma lem7139511 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term134 A s f b) = (term166 A s f b).
Proof. exact (EQ_MP (@lem7139510 A s f b) (@lem7139491 A s f b)). Qed.
Lemma lem7139512 {A : Type'} (s : A -> Prop) : (term136 A s) = (term136 A s).
Proof. exact (eq_refl (term136 A s)). Qed.
Lemma lem7139513 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term138 A s f b) = (term167 A s f b).
Proof. exact (MK_COMB (@lem7139512 A s) (@lem7139511 A s f b)). Qed.
Lemma lem7139515 {A : Type'} (P : Prop) (Q : A -> Prop) : (term168 A P Q) = (term169 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem7139516 {A : Type'} (P : Prop) (Q : A -> Prop) : (term168 A P Q) = (term169 A P Q).
Proof. exact (@lem7139515 A P Q). Qed.
Lemma lem7139517 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term170 A s f b) = (term171 A s f b).
Proof. exact (@lem7139516 A (term172 A s) (term165 A s f b)). Qed.
Lemma lem7139518 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term173 A s f b x) = (term163 A x s f b).
Proof. exact (eq_refl (term173 A s f b x)). Qed.
Lemma lem7139519 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term174 A s f b) = (term165 A s f b).
Proof. exact (fun_ext (fun x : A => @lem7139518 A x s f b)). Qed.
Lemma lem7139520 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7139521 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term175 A s f b) = (term166 A s f b).
Proof. exact (MK_COMB (@lem7139520 A) (@lem7139519 A s f b)). Qed.
Lemma lem7139522 {A : Type'} (s : A -> Prop) : (term136 A s) = (term136 A s).
Proof. exact (eq_refl (term136 A s)). Qed.
Lemma lem7139523 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term170 A s f b) = (term167 A s f b).
Proof. exact (MK_COMB (@lem7139522 A s) (@lem7139521 A s f b)). Qed.
Lemma lem7139524 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7139525 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term176 A s f b) = (term177 A s f b).
Proof. exact (MK_COMB (@lem7139524) (@lem7139523 A s f b)). Qed.
Lemma lem7139526 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term173 A s f b x) = (term163 A x s f b).
Proof. exact (eq_refl (term173 A s f b x)). Qed.
Lemma lem7139527 {A : Type'} (s : A -> Prop) : (term136 A s) = (term136 A s).
Proof. exact (eq_refl (term136 A s)). Qed.
Lemma lem7139528 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term178 A s f b x) = (term179 A x s f b).
Proof. exact (MK_COMB (@lem7139527 A s) (@lem7139526 A x s f b)). Qed.
Lemma lem7139529 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term180 A s f b) = (term181 A s f b).
Proof. exact (fun_ext (fun x : A => @lem7139528 A x s f b)). Qed.
Lemma lem7139530 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7139531 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term171 A s f b) = (term182 A s f b).
Proof. exact (MK_COMB (@lem7139530 A) (@lem7139529 A s f b)). Qed.
Lemma lem7139532 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : ((term170 A s f b) = (term171 A s f b)) = ((term167 A s f b) = (term182 A s f b)).
Proof. exact (MK_COMB (@lem7139525 A s f b) (@lem7139531 A s f b)). Qed.
Lemma lem7139533 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term167 A s f b) = (term182 A s f b).
Proof. exact (EQ_MP (@lem7139532 A s f b) (@lem7139517 A s f b)). Qed.
Lemma lem7139534 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term138 A s f b) = (term182 A s f b).
Proof. exact (TRANS (@lem7139513 A s f b) (@lem7139533 A s f b)). Qed.
Lemma lem7139535 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7139536 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term141 A s f b) = (term183 A s f b).
Proof. exact (MK_COMB (@lem7139535) (@lem7139534 A s f b)). Qed.
Lemma lem7139537 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term39 A f s b) = (term39 A f s b).
Proof. exact (eq_refl (term39 A f s b)). Qed.
Lemma lem7139538 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term143 A f s b) = (term184 A f s b).
Proof. exact (MK_COMB (@lem7139536 A s f b) (@lem7139537 A f s b)). Qed.
Lemma lem7139540 {A : Type'} (P : A -> Prop) (Q : Prop) : (term150 A P Q) = (term151 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem7139541 {A : Type'} (P : A -> Prop) (Q : Prop) : (term150 A P Q) = (term151 A P Q).
Proof. exact (@lem7139540 A P Q). Qed.
Lemma lem7139542 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term185 A f s b) = (term186 A f s b).
Proof. exact (@lem7139541 A (term181 A s f b) (term39 A f s b)). Qed.
Lemma lem7139543 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term187 A s f b x) = (term179 A x s f b).
Proof. exact (eq_refl (term187 A s f b x)). Qed.
Lemma lem7139544 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term188 A s f b) = (term181 A s f b).
Proof. exact (fun_ext (fun x : A => @lem7139543 A x s f b)). Qed.
Lemma lem7139545 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7139546 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term189 A s f b) = (term182 A s f b).
Proof. exact (MK_COMB (@lem7139545 A) (@lem7139544 A s f b)). Qed.
Lemma lem7139547 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7139548 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term190 A s f b) = (term183 A s f b).
Proof. exact (MK_COMB (@lem7139547) (@lem7139546 A s f b)). Qed.
Lemma lem7139549 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term39 A f s b) = (term39 A f s b).
Proof. exact (eq_refl (term39 A f s b)). Qed.
Lemma lem7139550 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term185 A f s b) = (term184 A f s b).
Proof. exact (MK_COMB (@lem7139548 A s f b) (@lem7139549 A f s b)). Qed.
Lemma lem7139551 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7139552 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term191 A f s b) = (term192 A f s b).
Proof. exact (MK_COMB (@lem7139551) (@lem7139550 A f s b)). Qed.
Lemma lem7139553 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term187 A s f b x) = (term179 A x s f b).
Proof. exact (eq_refl (term187 A s f b x)). Qed.
Lemma lem7139554 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7139555 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term193 A s f b x) = (term194 A x s f b).
Proof. exact (MK_COMB (@lem7139554) (@lem7139553 A x s f b)). Qed.
Lemma lem7139556 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term39 A f s b) = (term39 A f s b).
Proof. exact (eq_refl (term39 A f s b)). Qed.
Lemma lem7139557 {A : Type'} (x : A) (f : A -> real) (s : A -> Prop) (b : real) : (term195 A x f s b) = (term196 A x f s b).
Proof. exact (MK_COMB (@lem7139555 A x s f b) (@lem7139556 A f s b)). Qed.
Lemma lem7139558 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term197 A f s b) = (term198 A f s b).
Proof. exact (fun_ext (fun x : A => @lem7139557 A x f s b)). Qed.
Lemma lem7139559 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7139560 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term186 A f s b) = (term199 A f s b).
Proof. exact (MK_COMB (@lem7139559 A) (@lem7139558 A f s b)). Qed.
Lemma lem7139561 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : ((term185 A f s b) = (term186 A f s b)) = ((term184 A f s b) = (term199 A f s b)).
Proof. exact (MK_COMB (@lem7139552 A f s b) (@lem7139560 A f s b)). Qed.
Lemma lem7139562 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term184 A f s b) = (term199 A f s b).
Proof. exact (EQ_MP (@lem7139561 A f s b) (@lem7139542 A f s b)). Qed.
Lemma lem7139563 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term143 A f s b) = (term199 A f s b).
Proof. exact (TRANS (@lem7139538 A f s b) (@lem7139562 A f s b)). Qed.
Lemma lem7139564 {A : Type'} (f : A -> real) (s : A -> Prop) : (term144 A f s) = (term200 A f s).
Proof. exact (fun_ext (fun b : real => @lem7139563 A f s b)). Qed.
Lemma lem7139565 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7139566 {A : Type'} (f : A -> real) (s : A -> Prop) : (term145 A f s) = (term201 A f s).
Proof. exact (MK_COMB (@lem7139565) (@lem7139564 A f s)). Qed.
Lemma lem7139568 {A B : Type'} (P : type1413 A B) : (term202 A B P) = (term203 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7139569 {A : Type'} (P : type1620 A) : (term204 A P) = (term205 A P).
Proof. exact (@lem7139568 real A P). Qed.
Lemma lem7139570 {A : Type'} (f : A -> real) (s : A -> Prop) : (term206 A f s) = (term207 A f s).
Proof. exact (@lem7139569 A (term208 A f s)). Qed.
Lemma lem7139571 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term209 A f s b) = (term198 A f s b).
Proof. exact (eq_refl (term209 A f s b)). Qed.
Lemma lem7139572 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7139573 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) (x : A) : (term210 A f s b x) = (term211 A f s b x).
Proof. exact (MK_COMB (@lem7139571 A f s b) (@lem7139572 A x)). Qed.
Lemma lem7139574 {A : Type'} (x : A) (f : A -> real) (s : A -> Prop) (b : real) : (term211 A f s b x) = (term196 A x f s b).
Proof. exact (eq_refl (term211 A f s b x)). Qed.
Lemma lem7139575 {A : Type'} (x : A) (f : A -> real) (s : A -> Prop) (b : real) : (term210 A f s b x) = (term196 A x f s b).
Proof. exact (TRANS (@lem7139573 A f s b x) (@lem7139574 A x f s b)). Qed.
Lemma lem7139576 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term212 A f s b) = (term198 A f s b).
Proof. exact (fun_ext (fun x : A => @lem7139575 A x f s b)). Qed.
Lemma lem7139577 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7139578 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term213 A f s b) = (term199 A f s b).
Proof. exact (MK_COMB (@lem7139577 A) (@lem7139576 A f s b)). Qed.
Lemma lem7139579 {A : Type'} (f : A -> real) (s : A -> Prop) : (term214 A f s) = (term200 A f s).
Proof. exact (fun_ext (fun b : real => @lem7139578 A f s b)). Qed.
Lemma lem7139580 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7139581 {A : Type'} (f : A -> real) (s : A -> Prop) : (term206 A f s) = (term201 A f s).
Proof. exact (MK_COMB (@lem7139580) (@lem7139579 A f s)). Qed.
Lemma lem7139582 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7139583 {A : Type'} (f : A -> real) (s : A -> Prop) : (term215 A f s) = (term216 A f s).
Proof. exact (MK_COMB (@lem7139582) (@lem7139581 A f s)). Qed.
Lemma lem7139584 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term209 A f s b) = (term198 A f s b).
Proof. exact (eq_refl (term209 A f s b)). Qed.
Lemma lem7139585 {A : Type'} (x : real -> A) (b : real) : (x b) = (x b).
Proof. exact (eq_refl (x b)). Qed.
Lemma lem7139586 {A : Type'} (f : A -> real) (s : A -> Prop) (x : real -> A) (b : real) : (term217 A f s x b) = (term218 A f s x b).
Proof. exact (MK_COMB (@lem7139584 A f s b) (@lem7139585 A x b)). Qed.
Lemma lem7139587 {A : Type'} (x : real -> A) (f : A -> real) (s : A -> Prop) (b : real) : (term218 A f s x b) = (term219 A x f s b).
Proof. exact (eq_refl (term218 A f s x b)). Qed.
Lemma lem7139588 {A : Type'} (x : real -> A) (f : A -> real) (s : A -> Prop) (b : real) : (term217 A f s x b) = (term219 A x f s b).
Proof. exact (TRANS (@lem7139586 A f s x b) (@lem7139587 A x f s b)). Qed.
Lemma lem7139589 {A : Type'} (x : real -> A) (f : A -> real) (s : A -> Prop) : (term220 A f s x) = (term221 A x f s).
Proof. exact (fun_ext (fun b : real => @lem7139588 A x f s b)). Qed.
Lemma lem7139590 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7139591 {A : Type'} (x : real -> A) (f : A -> real) (s : A -> Prop) : (term222 A f s x) = (term223 A x f s).
Proof. exact (MK_COMB (@lem7139590) (@lem7139589 A x f s)). Qed.
Lemma lem7139592 {A : Type'} (f : A -> real) (s : A -> Prop) : (term224 A f s) = (term225 A f s).
Proof. exact (fun_ext (fun x : real -> A => @lem7139591 A x f s)). Qed.
Lemma lem7139593 {A : Type'} : (@ex (real -> A)) = (@ex (real -> A)).
Proof. exact (eq_refl (@ex (real -> A))). Qed.
Lemma lem7139594 {A : Type'} (f : A -> real) (s : A -> Prop) : (term207 A f s) = (term226 A f s).
Proof. exact (MK_COMB (@lem7139593 A) (@lem7139592 A f s)). Qed.
Lemma lem7139595 {A : Type'} (f : A -> real) (s : A -> Prop) : ((term206 A f s) = (term207 A f s)) = ((term201 A f s) = (term226 A f s)).
Proof. exact (MK_COMB (@lem7139583 A f s) (@lem7139594 A f s)). Qed.
Lemma lem7139596 {A : Type'} (f : A -> real) (s : A -> Prop) : (term201 A f s) = (term226 A f s).
Proof. exact (EQ_MP (@lem7139595 A f s) (@lem7139570 A f s)). Qed.
Lemma lem7139597 {A : Type'} (f : A -> real) (s : A -> Prop) : (term145 A f s) = (term226 A f s).
Proof. exact (TRANS (@lem7139566 A f s) (@lem7139596 A f s)). Qed.
Lemma lem7139598 {A : Type'} (s : A -> Prop) : (term146 A s) = (term227 A s).
Proof. exact (fun_ext (fun f : A -> real => @lem7139597 A f s)). Qed.
Lemma lem7139599 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7139600 {A : Type'} (s : A -> Prop) : (term147 A s) = (term228 A s).
Proof. exact (MK_COMB (@lem7139599 A) (@lem7139598 A s)). Qed.
Lemma lem7139602 {A B : Type'} (P : type1413 A B) : (term202 A B P) = (term203 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7139603 {A : Type'} (P : type713 A) : (term229 A P) = (term230 A P).
Proof. exact (@lem7139602 (A -> real) (real -> A) P). Qed.
Lemma lem7139604 {A : Type'} (s : A -> Prop) : (term231 A s) = (term232 A s).
Proof. exact (@lem7139603 A (term233 A s)). Qed.
Lemma lem7139605 {A : Type'} (f : A -> real) (s : A -> Prop) : (term234 A s f) = (term225 A f s).
Proof. exact (eq_refl (term234 A s f)). Qed.
Lemma lem7139606 {A : Type'} (x : real -> A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7139607 {A : Type'} (f : A -> real) (s : A -> Prop) (x : real -> A) : (term235 A s f x) = (term236 A f s x).
Proof. exact (MK_COMB (@lem7139605 A f s) (@lem7139606 A x)). Qed.
Lemma lem7139608 {A : Type'} (x : real -> A) (f : A -> real) (s : A -> Prop) : (term236 A f s x) = (term223 A x f s).
Proof. exact (eq_refl (term236 A f s x)). Qed.
Lemma lem7139609 {A : Type'} (x : real -> A) (f : A -> real) (s : A -> Prop) : (term235 A s f x) = (term223 A x f s).
Proof. exact (TRANS (@lem7139607 A f s x) (@lem7139608 A x f s)). Qed.
Lemma lem7139610 {A : Type'} (f : A -> real) (s : A -> Prop) : (term237 A s f) = (term225 A f s).
Proof. exact (fun_ext (fun x : real -> A => @lem7139609 A x f s)). Qed.
Lemma lem7139611 {A : Type'} : (@ex (real -> A)) = (@ex (real -> A)).
Proof. exact (eq_refl (@ex (real -> A))). Qed.
Lemma lem7139612 {A : Type'} (f : A -> real) (s : A -> Prop) : (term238 A s f) = (term226 A f s).
Proof. exact (MK_COMB (@lem7139611 A) (@lem7139610 A f s)). Qed.
Lemma lem7139613 {A : Type'} (s : A -> Prop) : (term239 A s) = (term227 A s).
Proof. exact (fun_ext (fun f : A -> real => @lem7139612 A f s)). Qed.
Lemma lem7139614 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7139615 {A : Type'} (s : A -> Prop) : (term231 A s) = (term228 A s).
Proof. exact (MK_COMB (@lem7139614 A) (@lem7139613 A s)). Qed.
Lemma lem7139616 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7139617 {A : Type'} (s : A -> Prop) : (term240 A s) = (term241 A s).
Proof. exact (MK_COMB (@lem7139616) (@lem7139615 A s)). Qed.
Lemma lem7139618 {A : Type'} (f : A -> real) (s : A -> Prop) : (term234 A s f) = (term225 A f s).
Proof. exact (eq_refl (term234 A s f)). Qed.
Lemma lem7139619 {A : Type'} (x : type715 A) (f : A -> real) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem7139620 {A : Type'} (s : A -> Prop) (x : type715 A) (f : A -> real) : (term242 A s x f) = (term243 A s x f).
Proof. exact (MK_COMB (@lem7139618 A f s) (@lem7139619 A x f)). Qed.
Lemma lem7139621 {A : Type'} (x : type715 A) (f : A -> real) (s : A -> Prop) : (term243 A s x f) = (term244 A x f s).
Proof. exact (eq_refl (term243 A s x f)). Qed.
Lemma lem7139622 {A : Type'} (x : type715 A) (f : A -> real) (s : A -> Prop) : (term242 A s x f) = (term244 A x f s).
Proof. exact (TRANS (@lem7139620 A s x f) (@lem7139621 A x f s)). Qed.
Lemma lem7139623 {A : Type'} (x : type715 A) (s : A -> Prop) : (term245 A s x) = (term246 A x s).
Proof. exact (fun_ext (fun f : A -> real => @lem7139622 A x f s)). Qed.
Lemma lem7139624 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7139625 {A : Type'} (x : type715 A) (s : A -> Prop) : (term247 A s x) = (term248 A x s).
Proof. exact (MK_COMB (@lem7139624 A) (@lem7139623 A x s)). Qed.
Lemma lem7139626 {A : Type'} (s : A -> Prop) : (term249 A s) = (term250 A s).
Proof. exact (fun_ext (fun x : type715 A => @lem7139625 A x s)). Qed.
Lemma lem7139627 {A : Type'} : (@ex ((A -> real) -> real -> A)) = (@ex ((A -> real) -> real -> A)).
Proof. exact (eq_refl (@ex ((A -> real) -> real -> A))). Qed.
Lemma lem7139628 {A : Type'} (s : A -> Prop) : (term232 A s) = (term251 A s).
Proof. exact (MK_COMB (@lem7139627 A) (@lem7139626 A s)). Qed.
Lemma lem7139629 {A : Type'} (s : A -> Prop) : ((term231 A s) = (term232 A s)) = ((term228 A s) = (term251 A s)).
Proof. exact (MK_COMB (@lem7139617 A s) (@lem7139628 A s)). Qed.
Lemma lem7139630 {A : Type'} (s : A -> Prop) : (term228 A s) = (term251 A s).
Proof. exact (EQ_MP (@lem7139629 A s) (@lem7139604 A s)). Qed.
Lemma lem7139631 {A : Type'} (s : A -> Prop) : (term147 A s) = (term251 A s).
Proof. exact (TRANS (@lem7139600 A s) (@lem7139630 A s)). Qed.
Lemma lem7139632 {A : Type'} : (term148 A) = (term252 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7139631 A s)). Qed.
Lemma lem7139633 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7139634 {A : Type'} : (term149 A) = (term253 A).
Proof. exact (MK_COMB (@lem7139633 A) (@lem7139632 A)). Qed.
Lemma lem7139636 {A B : Type'} (P : type1413 A B) : (term202 A B P) = (term203 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7139637 {A : Type'} (P : type603 A) : (term254 A P) = (term255 A P).
Proof. exact (@lem7139636 (A -> Prop) (type715 A) P). Qed.
Lemma lem7139638 {A : Type'} : (term256 A) = (term257 A).
Proof. exact (@lem7139637 A (term258 A)). Qed.
Lemma lem7139639 {A : Type'} (s : A -> Prop) : (term259 A s) = (term250 A s).
Proof. exact (eq_refl (term259 A s)). Qed.
Lemma lem7139640 {A : Type'} (x : type715 A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7139641 {A : Type'} (s : A -> Prop) (x : type715 A) : (term260 A s x) = (term261 A s x).
Proof. exact (MK_COMB (@lem7139639 A s) (@lem7139640 A x)). Qed.
Lemma lem7139642 {A : Type'} (x : type715 A) (s : A -> Prop) : (term261 A s x) = (term248 A x s).
Proof. exact (eq_refl (term261 A s x)). Qed.
Lemma lem7139643 {A : Type'} (x : type715 A) (s : A -> Prop) : (term260 A s x) = (term248 A x s).
Proof. exact (TRANS (@lem7139641 A s x) (@lem7139642 A x s)). Qed.
Lemma lem7139644 {A : Type'} (s : A -> Prop) : (term262 A s) = (term250 A s).
Proof. exact (fun_ext (fun x : type715 A => @lem7139643 A x s)). Qed.
Lemma lem7139645 {A : Type'} : (@ex ((A -> real) -> real -> A)) = (@ex ((A -> real) -> real -> A)).
Proof. exact (eq_refl (@ex ((A -> real) -> real -> A))). Qed.
Lemma lem7139646 {A : Type'} (s : A -> Prop) : (term263 A s) = (term251 A s).
Proof. exact (MK_COMB (@lem7139645 A) (@lem7139644 A s)). Qed.
Lemma lem7139647 {A : Type'} : (term264 A) = (term252 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7139646 A s)). Qed.
Lemma lem7139648 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7139649 {A : Type'} : (term256 A) = (term253 A).
Proof. exact (MK_COMB (@lem7139648 A) (@lem7139647 A)). Qed.
Lemma lem7139650 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7139651 {A : Type'} : (term265 A) = (term266 A).
Proof. exact (MK_COMB (@lem7139650) (@lem7139649 A)). Qed.
Lemma lem7139652 {A : Type'} (s : A -> Prop) : (term259 A s) = (term250 A s).
Proof. exact (eq_refl (term259 A s)). Qed.
Lemma lem7139653 {A : Type'} (x : type645 A) (s : A -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem7139654 {A : Type'} (x : type645 A) (s : A -> Prop) : (term267 A x s) = (term268 A x s).
Proof. exact (MK_COMB (@lem7139652 A s) (@lem7139653 A x s)). Qed.
Lemma lem7139655 {A : Type'} (x : type645 A) (s : A -> Prop) : (term268 A x s) = (term269 A x s).
Proof. exact (eq_refl (term268 A x s)). Qed.
Lemma lem7139656 {A : Type'} (x : type645 A) (s : A -> Prop) : (term267 A x s) = (term269 A x s).
Proof. exact (TRANS (@lem7139654 A x s) (@lem7139655 A x s)). Qed.
Lemma lem7139657 {A : Type'} (x : type645 A) : (term270 A x) = (term271 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7139656 A x s)). Qed.
Lemma lem7139658 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7139659 {A : Type'} (x : type645 A) : (term272 A x) = (term273 A x).
Proof. exact (MK_COMB (@lem7139658 A) (@lem7139657 A x)). Qed.
Lemma lem7139660 {A : Type'} : (term274 A) = (term275 A).
Proof. exact (fun_ext (fun x : type645 A => @lem7139659 A x)). Qed.
Lemma lem7139661 {A : Type'} : (@ex ((A -> Prop) -> (A -> real) -> real -> A)) = (@ex ((A -> Prop) -> (A -> real) -> real -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> real) -> real -> A))). Qed.
Lemma lem7139662 {A : Type'} : (term257 A) = (term276 A).
Proof. exact (MK_COMB (@lem7139661 A) (@lem7139660 A)). Qed.
Lemma lem7139663 {A : Type'} : ((term256 A) = (term257 A)) = ((term253 A) = (term276 A)).
Proof. exact (MK_COMB (@lem7139651 A) (@lem7139662 A)). Qed.
Lemma lem7139664 {A : Type'} : (term253 A) = (term276 A).
Proof. exact (EQ_MP (@lem7139663 A) (@lem7139638 A)). Qed.
Lemma lem7139666 {A : Type'} : (term149 A) = (term276 A).
Proof. exact (TRANS (@lem7139634 A) (@lem7139664 A)). Qed.
Lemma lem7139667 {A : Type'} : (term12 A) = (term276 A).
Proof. exact (TRANS (@lem7139334 A) (@lem7139666 A)). Qed.
Lemma lem7139668 {A : Type'} (h1 : term12 A) : term276 A.
Proof. exact (EQ_MP (@lem7139667 A) (@lem7138715 A h1)). Qed.
Lemma lem7139675 (x : real) (y : real) : (term34 x y) = (term277 x y).
Proof. exact (@lem17265 (real_lt x y) (real_le x y)). Qed.
Lemma lem7139676 (x : real) : (term35 x) = (term278 x).
Proof. exact (fun_ext (fun y : real => @lem7139675 x y)). Qed.
Lemma lem7139677 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7139678 (x : real) : (term36 x) = (term279 x).
Proof. exact (MK_COMB (@lem7139677) (@lem7139676 x)). Qed.
Lemma lem7139679 : term37 = term280.
Proof. exact (fun_ext (fun x : real => @lem7139678 x)). Qed.
Lemma lem7139680 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7139737 : term38 = term281.
Proof. exact (MK_COMB (@lem7139680) (@lem7139679)). Qed.
Lemma lem7139738 (h1 : term38) : term281.
Proof. exact (EQ_MP (@lem7139737) (@lem7138716 h1)). Qed.
Lemma lem7139740 {_133668 : Type'} (x : _133668) (s : _133668 -> Prop) : (@IN _133668 x s) = (@IN _133668 x s).
Proof. exact (eq_refl (@IN _133668 x s)). Qed.
Lemma lem7139741 {_133668 : Type'} (P : _133668 -> Prop) : (term122 _133668 P) = (term123 _133668 P).
Proof. exact (@lem18394 _133668 P). Qed.
Lemma lem7139742 {_133668 : Type'} (s : _133668 -> Prop) : (term282 _133668 s) = (term283 _133668 s).
Proof. exact (@lem7139741 _133668 (term30 _133668 s)). Qed.
Lemma lem7139743 {_133668 : Type'} (x : _133668) (s : _133668 -> Prop) : (term284 _133668 s x) = (@IN _133668 x s).
Proof. exact (eq_refl (term284 _133668 s x)). Qed.
Lemma lem7139744 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7139746 {_133668 : Type'} (x : _133668) (s : _133668 -> Prop) : (term285 _133668 s x) = (term286 _133668 x s).
Proof. exact (MK_COMB (@lem7139744) (@lem7139743 _133668 x s)). Qed.
Lemma lem7139747 {_133668 : Type'} (s : _133668 -> Prop) : (term287 _133668 s) = (term288 _133668 s).
Proof. exact (fun_ext (fun x : _133668 => @lem7139746 _133668 x s)). Qed.
Lemma lem7139748 {_133668 : Type'} : (@all _133668) = (@all _133668).
Proof. exact (eq_refl (@all _133668)). Qed.
Lemma lem7139749 {_133668 : Type'} (s : _133668 -> Prop) : (term283 _133668 s) = (term289 _133668 s).
Proof. exact (MK_COMB (@lem7139748 _133668) (@lem7139747 _133668 s)). Qed.
Lemma lem7139750 {_133668 : Type'} (s : _133668 -> Prop) : (term282 _133668 s) = (term289 _133668 s).
Proof. exact (TRANS (@lem7139742 _133668 s) (@lem7139749 _133668 s)). Qed.
Lemma lem7139751 {_133668 : Type'} (s : _133668 -> Prop) : (term30 _133668 s) = (term30 _133668 s).
Proof. exact (fun_ext (fun x : _133668 => @lem7139740 _133668 x s)). Qed.
Lemma lem7139752 {_133668 : Type'} : (@ex _133668) = (@ex _133668).
Proof. exact (eq_refl (@ex _133668)). Qed.
Lemma lem7139753 {_133668 : Type'} (s : _133668 -> Prop) : (term31 _133668 s) = (term31 _133668 s).
Proof. exact (MK_COMB (@lem7139752 _133668) (@lem7139751 _133668 s)). Qed.
Lemma lem7139754 {_133668 : Type'} (s : _133668 -> Prop) : (term29 _133668 s) = (term29 _133668 s).
Proof. exact (eq_refl (term29 _133668 s)). Qed.
Lemma lem7139757 {_133668 : Type'} (s : _133668 -> Prop) : (term290 _133668 s) = (s = (@EMPTY _133668)).
Proof. exact (@lem16933 (s = (@EMPTY _133668))). Qed.
Lemma lem7139758 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7139759 {_133668 : Type'} (s : _133668 -> Prop) : (term291 _133668 s) = (term292 _133668 s).
Proof. exact (MK_COMB (@lem7139758) (@lem7139750 _133668 s)). Qed.
Lemma lem7139760 {_133668 : Type'} (s : _133668 -> Prop) : (term293 _133668 s) = (term294 _133668 s).
Proof. exact (MK_COMB (@lem7139759 _133668 s) (@lem7139754 _133668 s)). Qed.
Lemma lem7139761 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7139762 {_133668 : Type'} (s : _133668 -> Prop) : (term295 _133668 s) = (term295 _133668 s).
Proof. exact (MK_COMB (@lem7139761) (@lem7139753 _133668 s)). Qed.
Lemma lem7139763 {_133668 : Type'} (s : _133668 -> Prop) : (term296 _133668 s) = (term297 _133668 s).
Proof. exact (MK_COMB (@lem7139762 _133668 s) (@lem7139757 _133668 s)). Qed.
Lemma lem7139764 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7139765 {_133668 : Type'} (s : _133668 -> Prop) : (term298 _133668 s) = (term299 _133668 s).
Proof. exact (MK_COMB (@lem7139764) (@lem7139763 _133668 s)). Qed.
Lemma lem7139766 {_133668 : Type'} (s : _133668 -> Prop) : (term300 _133668 s) = (term301 _133668 s).
Proof. exact (MK_COMB (@lem7139765 _133668 s) (@lem7139760 _133668 s)). Qed.
Lemma lem7139767 {_133668 : Type'} (s : _133668 -> Prop) : ((term31 _133668 s) = (term29 _133668 s)) = (term300 _133668 s).
Proof. exact (@lem17784 (term31 _133668 s) (term29 _133668 s)). Qed.
Lemma lem7139768 {_133668 : Type'} (s : _133668 -> Prop) : ((term31 _133668 s) = (term29 _133668 s)) = (term301 _133668 s).
Proof. exact (TRANS (@lem7139767 _133668 s) (@lem7139766 _133668 s)). Qed.
Lemma lem7139769 {_133668 : Type'} : (term33 _133668) = (term302 _133668).
Proof. exact (fun_ext (fun s : _133668 -> Prop => @lem7139768 _133668 s)). Qed.
Lemma lem7139770 {_133668 : Type'} : (@all (_133668 -> Prop)) = (@all (_133668 -> Prop)).
Proof. exact (eq_refl (@all (_133668 -> Prop))). Qed.
Lemma lem7139771 {_133668 : Type'} : (term11 _133668) = (term303 _133668).
Proof. exact (MK_COMB (@lem7139770 _133668) (@lem7139769 _133668)). Qed.
Lemma lem7139773 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term304 A P Q) = (term305 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7139774 {_133668 : Type'} (P : type686 _133668) (Q : type686 _133668) : (term306 _133668 P Q) = (term307 _133668 P Q).
Proof. exact (@lem7139773 (_133668 -> Prop) P Q). Qed.
Lemma lem7139775 {_133668 : Type'} : (term308 _133668) = (term309 _133668).
Proof. exact (@lem7139774 _133668 (term310 _133668) (term311 _133668)). Qed.
Lemma lem7139776 {_133668 : Type'} (s : _133668 -> Prop) : (term312 _133668 s) = (term297 _133668 s).
Proof. exact (eq_refl (term312 _133668 s)). Qed.
Lemma lem7139777 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7139778 {_133668 : Type'} (s : _133668 -> Prop) : (term313 _133668 s) = (term299 _133668 s).
Proof. exact (MK_COMB (@lem7139777) (@lem7139776 _133668 s)). Qed.
Lemma lem7139779 {_133668 : Type'} (s : _133668 -> Prop) : (term314 _133668 s) = (term294 _133668 s).
Proof. exact (eq_refl (term314 _133668 s)). Qed.
Lemma lem7139780 {_133668 : Type'} (s : _133668 -> Prop) : (term315 _133668 s) = (term301 _133668 s).
Proof. exact (MK_COMB (@lem7139778 _133668 s) (@lem7139779 _133668 s)). Qed.
Lemma lem7139781 {_133668 : Type'} : (term316 _133668) = (term302 _133668).
Proof. exact (fun_ext (fun s : _133668 -> Prop => @lem7139780 _133668 s)). Qed.
Lemma lem7139782 {_133668 : Type'} : (@all (_133668 -> Prop)) = (@all (_133668 -> Prop)).
Proof. exact (eq_refl (@all (_133668 -> Prop))). Qed.
Lemma lem7139783 {_133668 : Type'} : (term308 _133668) = (term303 _133668).
Proof. exact (MK_COMB (@lem7139782 _133668) (@lem7139781 _133668)). Qed.
Lemma lem7139784 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7139785 {_133668 : Type'} : (term317 _133668) = (term318 _133668).
Proof. exact (MK_COMB (@lem7139784) (@lem7139783 _133668)). Qed.
Lemma lem7139786 {_133668 : Type'} (s : _133668 -> Prop) : (term312 _133668 s) = (term297 _133668 s).
Proof. exact (eq_refl (term312 _133668 s)). Qed.
Lemma lem7139787 {_133668 : Type'} : (term319 _133668) = (term310 _133668).
Proof. exact (fun_ext (fun s : _133668 -> Prop => @lem7139786 _133668 s)). Qed.
Lemma lem7139788 {_133668 : Type'} : (@all (_133668 -> Prop)) = (@all (_133668 -> Prop)).
Proof. exact (eq_refl (@all (_133668 -> Prop))). Qed.
Lemma lem7139789 {_133668 : Type'} : (term320 _133668) = (term321 _133668).
Proof. exact (MK_COMB (@lem7139788 _133668) (@lem7139787 _133668)). Qed.
Lemma lem7139790 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7139791 {_133668 : Type'} : (term322 _133668) = (term323 _133668).
Proof. exact (MK_COMB (@lem7139790) (@lem7139789 _133668)). Qed.
Lemma lem7139792 {_133668 : Type'} (s : _133668 -> Prop) : (term314 _133668 s) = (term294 _133668 s).
Proof. exact (eq_refl (term314 _133668 s)). Qed.
Lemma lem7139793 {_133668 : Type'} : (term324 _133668) = (term311 _133668).
Proof. exact (fun_ext (fun s : _133668 -> Prop => @lem7139792 _133668 s)). Qed.
Lemma lem7139794 {_133668 : Type'} : (@all (_133668 -> Prop)) = (@all (_133668 -> Prop)).
Proof. exact (eq_refl (@all (_133668 -> Prop))). Qed.
Lemma lem7139795 {_133668 : Type'} : (term325 _133668) = (term326 _133668).
Proof. exact (MK_COMB (@lem7139794 _133668) (@lem7139793 _133668)). Qed.
Lemma lem7139796 {_133668 : Type'} : (term309 _133668) = (term327 _133668).
Proof. exact (MK_COMB (@lem7139791 _133668) (@lem7139795 _133668)). Qed.
Lemma lem7139797 {_133668 : Type'} : ((term308 _133668) = (term309 _133668)) = ((term303 _133668) = (term327 _133668)).
Proof. exact (MK_COMB (@lem7139785 _133668) (@lem7139796 _133668)). Qed.
Lemma lem7139798 {_133668 : Type'} : (term303 _133668) = (term327 _133668).
Proof. exact (EQ_MP (@lem7139797 _133668) (@lem7139775 _133668)). Qed.
Lemma lem7139904 {A : Type'} (P : A -> Prop) (Q : Prop) : (term150 A P Q) = (term151 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem7139905 {_133668 : Type'} (P : _133668 -> Prop) (Q : Prop) : (term150 _133668 P Q) = (term151 _133668 P Q).
Proof. exact (@lem7139904 _133668 P Q). Qed.
Lemma lem7139906 {_133668 : Type'} (s : _133668 -> Prop) : (term328 _133668 s) = (term329 _133668 s).
Proof. exact (@lem7139905 _133668 (term30 _133668 s) (s = (@EMPTY _133668))). Qed.
Lemma lem7139907 {_133668 : Type'} (x : _133668) (s : _133668 -> Prop) : (term284 _133668 s x) = (@IN _133668 x s).
Proof. exact (eq_refl (term284 _133668 s x)). Qed.
Lemma lem7139908 {_133668 : Type'} (s : _133668 -> Prop) : (term330 _133668 s) = (term30 _133668 s).
Proof. exact (fun_ext (fun x : _133668 => @lem7139907 _133668 x s)). Qed.
Lemma lem7139909 {_133668 : Type'} : (@ex _133668) = (@ex _133668).
Proof. exact (eq_refl (@ex _133668)). Qed.
Lemma lem7139910 {_133668 : Type'} (s : _133668 -> Prop) : (term331 _133668 s) = (term31 _133668 s).
Proof. exact (MK_COMB (@lem7139909 _133668) (@lem7139908 _133668 s)). Qed.
Lemma lem7139911 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7139912 {_133668 : Type'} (s : _133668 -> Prop) : (term332 _133668 s) = (term295 _133668 s).
Proof. exact (MK_COMB (@lem7139911) (@lem7139910 _133668 s)). Qed.
Lemma lem7139913 {_133668 : Type'} (s : _133668 -> Prop) : (s = (@EMPTY _133668)) = (s = (@EMPTY _133668)).
Proof. exact (eq_refl (s = (@EMPTY _133668))). Qed.
Lemma lem7139914 {_133668 : Type'} (s : _133668 -> Prop) : (term328 _133668 s) = (term297 _133668 s).
Proof. exact (MK_COMB (@lem7139912 _133668 s) (@lem7139913 _133668 s)). Qed.
Lemma lem7139915 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7139916 {_133668 : Type'} (s : _133668 -> Prop) : (term333 _133668 s) = (term334 _133668 s).
Proof. exact (MK_COMB (@lem7139915) (@lem7139914 _133668 s)). Qed.
Lemma lem7139917 {_133668 : Type'} (x : _133668) (s : _133668 -> Prop) : (term284 _133668 s x) = (@IN _133668 x s).
Proof. exact (eq_refl (term284 _133668 s x)). Qed.
Lemma lem7139918 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7139919 {_133668 : Type'} (x : _133668) (s : _133668 -> Prop) : (term335 _133668 s x) = (term336 _133668 x s).
Proof. exact (MK_COMB (@lem7139918) (@lem7139917 _133668 x s)). Qed.
Lemma lem7139920 {_133668 : Type'} (s : _133668 -> Prop) : (s = (@EMPTY _133668)) = (s = (@EMPTY _133668)).
Proof. exact (eq_refl (s = (@EMPTY _133668))). Qed.
Lemma lem7139921 {_133668 : Type'} (x : _133668) (s : _133668 -> Prop) : (term337 _133668 x s) = (term338 _133668 x s).
Proof. exact (MK_COMB (@lem7139919 _133668 x s) (@lem7139920 _133668 s)). Qed.
Lemma lem7139922 {_133668 : Type'} (s : _133668 -> Prop) : (term339 _133668 s) = (term340 _133668 s).
Proof. exact (fun_ext (fun x : _133668 => @lem7139921 _133668 x s)). Qed.
Lemma lem7139923 {_133668 : Type'} : (@ex _133668) = (@ex _133668).
Proof. exact (eq_refl (@ex _133668)). Qed.
Lemma lem7139924 {_133668 : Type'} (s : _133668 -> Prop) : (term329 _133668 s) = (term341 _133668 s).
Proof. exact (MK_COMB (@lem7139923 _133668) (@lem7139922 _133668 s)). Qed.
Lemma lem7139925 {_133668 : Type'} (s : _133668 -> Prop) : ((term328 _133668 s) = (term329 _133668 s)) = ((term297 _133668 s) = (term341 _133668 s)).
Proof. exact (MK_COMB (@lem7139916 _133668 s) (@lem7139924 _133668 s)). Qed.
Lemma lem7139926 {_133668 : Type'} (s : _133668 -> Prop) : (term297 _133668 s) = (term341 _133668 s).
Proof. exact (EQ_MP (@lem7139925 _133668 s) (@lem7139906 _133668 s)). Qed.
Lemma lem7139927 {_133668 : Type'} : (term310 _133668) = (term342 _133668).
Proof. exact (fun_ext (fun s : _133668 -> Prop => @lem7139926 _133668 s)). Qed.
Lemma lem7139928 {_133668 : Type'} : (@all (_133668 -> Prop)) = (@all (_133668 -> Prop)).
Proof. exact (eq_refl (@all (_133668 -> Prop))). Qed.
Lemma lem7139929 {_133668 : Type'} : (term321 _133668) = (term343 _133668).
Proof. exact (MK_COMB (@lem7139928 _133668) (@lem7139927 _133668)). Qed.
Lemma lem7139931 {A B : Type'} (P : type1413 A B) : (term202 A B P) = (term203 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7139932 {_133668 : Type'} (P : type672 _133668) : (term344 _133668 P) = (term345 _133668 P).
Proof. exact (@lem7139931 (_133668 -> Prop) _133668 P). Qed.
Lemma lem7139933 {_133668 : Type'} : (term346 _133668) = (term347 _133668).
Proof. exact (@lem7139932 _133668 (term348 _133668)). Qed.
Lemma lem7139934 {_133668 : Type'} (s : _133668 -> Prop) : (term349 _133668 s) = (term340 _133668 s).
Proof. exact (eq_refl (term349 _133668 s)). Qed.
Lemma lem7139935 {_133668 : Type'} (x : _133668) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7139936 {_133668 : Type'} (s : _133668 -> Prop) (x : _133668) : (term350 _133668 s x) = (term351 _133668 s x).
Proof. exact (MK_COMB (@lem7139934 _133668 s) (@lem7139935 _133668 x)). Qed.
Lemma lem7139937 {_133668 : Type'} (x : _133668) (s : _133668 -> Prop) : (term351 _133668 s x) = (term338 _133668 x s).
Proof. exact (eq_refl (term351 _133668 s x)). Qed.
Lemma lem7139938 {_133668 : Type'} (x : _133668) (s : _133668 -> Prop) : (term350 _133668 s x) = (term338 _133668 x s).
Proof. exact (TRANS (@lem7139936 _133668 s x) (@lem7139937 _133668 x s)). Qed.
Lemma lem7139939 {_133668 : Type'} (s : _133668 -> Prop) : (term352 _133668 s) = (term340 _133668 s).
Proof. exact (fun_ext (fun x : _133668 => @lem7139938 _133668 x s)). Qed.
Lemma lem7139940 {_133668 : Type'} : (@ex _133668) = (@ex _133668).
Proof. exact (eq_refl (@ex _133668)). Qed.
Lemma lem7139941 {_133668 : Type'} (s : _133668 -> Prop) : (term353 _133668 s) = (term341 _133668 s).
Proof. exact (MK_COMB (@lem7139940 _133668) (@lem7139939 _133668 s)). Qed.
Lemma lem7139942 {_133668 : Type'} : (term354 _133668) = (term342 _133668).
Proof. exact (fun_ext (fun s : _133668 -> Prop => @lem7139941 _133668 s)). Qed.
Lemma lem7139943 {_133668 : Type'} : (@all (_133668 -> Prop)) = (@all (_133668 -> Prop)).
Proof. exact (eq_refl (@all (_133668 -> Prop))). Qed.
Lemma lem7139944 {_133668 : Type'} : (term346 _133668) = (term343 _133668).
Proof. exact (MK_COMB (@lem7139943 _133668) (@lem7139942 _133668)). Qed.
Lemma lem7139945 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7139946 {_133668 : Type'} : (term355 _133668) = (term356 _133668).
Proof. exact (MK_COMB (@lem7139945) (@lem7139944 _133668)). Qed.
Lemma lem7139947 {_133668 : Type'} (s : _133668 -> Prop) : (term349 _133668 s) = (term340 _133668 s).
Proof. exact (eq_refl (term349 _133668 s)). Qed.
Lemma lem7139948 {_133668 : Type'} (x : type684 _133668) (s : _133668 -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem7139949 {_133668 : Type'} (x : type684 _133668) (s : _133668 -> Prop) : (term357 _133668 x s) = (term358 _133668 x s).
Proof. exact (MK_COMB (@lem7139947 _133668 s) (@lem7139948 _133668 x s)). Qed.
Lemma lem7139950 {_133668 : Type'} (x : type684 _133668) (s : _133668 -> Prop) : (term358 _133668 x s) = (term359 _133668 x s).
Proof. exact (eq_refl (term358 _133668 x s)). Qed.
Lemma lem7139951 {_133668 : Type'} (x : type684 _133668) (s : _133668 -> Prop) : (term357 _133668 x s) = (term359 _133668 x s).
Proof. exact (TRANS (@lem7139949 _133668 x s) (@lem7139950 _133668 x s)). Qed.
Lemma lem7139952 {_133668 : Type'} (x : type684 _133668) : (term360 _133668 x) = (term361 _133668 x).
Proof. exact (fun_ext (fun s : _133668 -> Prop => @lem7139951 _133668 x s)). Qed.
Lemma lem7139953 {_133668 : Type'} : (@all (_133668 -> Prop)) = (@all (_133668 -> Prop)).
Proof. exact (eq_refl (@all (_133668 -> Prop))). Qed.
Lemma lem7139954 {_133668 : Type'} (x : type684 _133668) : (term362 _133668 x) = (term363 _133668 x).
Proof. exact (MK_COMB (@lem7139953 _133668) (@lem7139952 _133668 x)). Qed.
Lemma lem7139955 {_133668 : Type'} : (term364 _133668) = (term365 _133668).
Proof. exact (fun_ext (fun x : type684 _133668 => @lem7139954 _133668 x)). Qed.
Lemma lem7139956 {_133668 : Type'} : (@ex ((_133668 -> Prop) -> _133668)) = (@ex ((_133668 -> Prop) -> _133668)).
Proof. exact (eq_refl (@ex ((_133668 -> Prop) -> _133668))). Qed.
Lemma lem7139957 {_133668 : Type'} : (term347 _133668) = (term366 _133668).
Proof. exact (MK_COMB (@lem7139956 _133668) (@lem7139955 _133668)). Qed.
Lemma lem7139958 {_133668 : Type'} : ((term346 _133668) = (term347 _133668)) = ((term343 _133668) = (term366 _133668)).
Proof. exact (MK_COMB (@lem7139946 _133668) (@lem7139957 _133668)). Qed.
Lemma lem7139959 {_133668 : Type'} : (term343 _133668) = (term366 _133668).
Proof. exact (EQ_MP (@lem7139958 _133668) (@lem7139933 _133668)). Qed.
Lemma lem7139960 {_133668 : Type'} : (term321 _133668) = (term366 _133668).
Proof. exact (TRANS (@lem7139929 _133668) (@lem7139959 _133668)). Qed.
Lemma lem7139961 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7139962 {_133668 : Type'} : (term323 _133668) = (term367 _133668).
Proof. exact (MK_COMB (@lem7139961) (@lem7139960 _133668)). Qed.
Lemma lem7139963 {_133668 : Type'} : (term326 _133668) = (term326 _133668).
Proof. exact (eq_refl (term326 _133668)). Qed.
Lemma lem7139964 {_133668 : Type'} : (term327 _133668) = (term368 _133668).
Proof. exact (MK_COMB (@lem7139962 _133668) (@lem7139963 _133668)). Qed.
Lemma lem7139966 {A : Type'} (P : A -> Prop) (Q : Prop) : (term369 A P Q) = (term370 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem7139967 {_133668 : Type'} (P : type162 _133668) (Q : Prop) : (term371 _133668 P Q) = (term372 _133668 P Q).
Proof. exact (@lem7139966 (type684 _133668) P Q). Qed.
Lemma lem7139968 {_133668 : Type'} : (term373 _133668) = (term374 _133668).
Proof. exact (@lem7139967 _133668 (term365 _133668) (term326 _133668)). Qed.
Lemma lem7139969 {_133668 : Type'} (x : type684 _133668) : (term375 _133668 x) = (term363 _133668 x).
Proof. exact (eq_refl (term375 _133668 x)). Qed.
Lemma lem7139970 {_133668 : Type'} : (term376 _133668) = (term365 _133668).
Proof. exact (fun_ext (fun x : type684 _133668 => @lem7139969 _133668 x)). Qed.
Lemma lem7139971 {_133668 : Type'} : (@ex ((_133668 -> Prop) -> _133668)) = (@ex ((_133668 -> Prop) -> _133668)).
Proof. exact (eq_refl (@ex ((_133668 -> Prop) -> _133668))). Qed.
Lemma lem7139972 {_133668 : Type'} : (term377 _133668) = (term366 _133668).
Proof. exact (MK_COMB (@lem7139971 _133668) (@lem7139970 _133668)). Qed.
Lemma lem7139973 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7139974 {_133668 : Type'} : (term378 _133668) = (term367 _133668).
Proof. exact (MK_COMB (@lem7139973) (@lem7139972 _133668)). Qed.
Lemma lem7139975 {_133668 : Type'} : (term326 _133668) = (term326 _133668).
Proof. exact (eq_refl (term326 _133668)). Qed.
Lemma lem7139976 {_133668 : Type'} : (term373 _133668) = (term368 _133668).
Proof. exact (MK_COMB (@lem7139974 _133668) (@lem7139975 _133668)). Qed.
Lemma lem7139977 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7139978 {_133668 : Type'} : (term379 _133668) = (term380 _133668).
Proof. exact (MK_COMB (@lem7139977) (@lem7139976 _133668)). Qed.
Lemma lem7139979 {_133668 : Type'} (x : type684 _133668) : (term375 _133668 x) = (term363 _133668 x).
Proof. exact (eq_refl (term375 _133668 x)). Qed.
Lemma lem7139980 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7139981 {_133668 : Type'} (x : type684 _133668) : (term381 _133668 x) = (term382 _133668 x).
Proof. exact (MK_COMB (@lem7139980) (@lem7139979 _133668 x)). Qed.
Lemma lem7139982 {_133668 : Type'} : (term326 _133668) = (term326 _133668).
Proof. exact (eq_refl (term326 _133668)). Qed.
Lemma lem7139983 {_133668 : Type'} (x : type684 _133668) : (term383 _133668 x) = (term384 _133668 x).
Proof. exact (MK_COMB (@lem7139981 _133668 x) (@lem7139982 _133668)). Qed.
Lemma lem7139984 {_133668 : Type'} : (term385 _133668) = (term386 _133668).
Proof. exact (fun_ext (fun x : type684 _133668 => @lem7139983 _133668 x)). Qed.
Lemma lem7139985 {_133668 : Type'} : (@ex ((_133668 -> Prop) -> _133668)) = (@ex ((_133668 -> Prop) -> _133668)).
Proof. exact (eq_refl (@ex ((_133668 -> Prop) -> _133668))). Qed.
Lemma lem7139986 {_133668 : Type'} : (term374 _133668) = (term387 _133668).
Proof. exact (MK_COMB (@lem7139985 _133668) (@lem7139984 _133668)). Qed.
Lemma lem7139987 {_133668 : Type'} : ((term373 _133668) = (term374 _133668)) = ((term368 _133668) = (term387 _133668)).
Proof. exact (MK_COMB (@lem7139978 _133668) (@lem7139986 _133668)). Qed.
Lemma lem7139988 {_133668 : Type'} : (term368 _133668) = (term387 _133668).
Proof. exact (EQ_MP (@lem7139987 _133668) (@lem7139968 _133668)). Qed.
Lemma lem7139989 {_133668 : Type'} : (term327 _133668) = (term387 _133668).
Proof. exact (TRANS (@lem7139964 _133668) (@lem7139988 _133668)). Qed.
Lemma lem7139990 {_133668 : Type'} : (term303 _133668) = (term387 _133668).
Proof. exact (TRANS (@lem7139798 _133668) (@lem7139989 _133668)). Qed.
Lemma lem7139991 {_133668 : Type'} : (term11 _133668) = (term387 _133668).
Proof. exact (TRANS (@lem7139771 _133668) (@lem7139990 _133668)). Qed.
Lemma lem7139992 {_133668 : Type'} (h1 : term11 _133668) : term387 _133668.
Proof. exact (EQ_MP (@lem7139991 _133668) (@lem7138717 _133668 h1)). Qed.
Lemma lem7139993 {_133668 : Type'} (x : type684 _133668) (h1 : term384 _133668 x) : term384 _133668 x.
Proof. exact (h1). Qed.
Lemma lem7139995 {_133668 : Type'} (x'' : type645 _133668) (h1 : term273 _133668 x'') : term273 _133668 x''.
Proof. exact (h1). Qed.
Lemma lem7139996 {_133668 : Type'} (s : _133668 -> Prop) (h1 : term99 _133668 s) : term99 _133668 s.
Proof. exact (h1). Qed.
Lemma lem7139997 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (h1 : term90 _133668 f s) : term90 _133668 f s.
Proof. exact (h1). Qed.
Lemma lem7139998 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) (h1 : term80 _133668 f s b) : term80 _133668 f s b.
Proof. exact (h1). Qed.
Lemma lem7140005 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7140006 (f : type1626) (x : real) : (f x) = (@I (real -> real -> Prop) f x).
Proof. exact (@lem7140005 real (real -> Prop) f x). Qed.
Lemma lem7140007 (x : real) : (real_le x) = (@I (real -> real -> Prop) real_le x).
Proof. exact (@lem7140006 real_le x). Qed.
Lemma lem7140008 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem7140009 (x : real) (y : real) : (real_le x y) = (@I (real -> real -> Prop) real_le x y).
Proof. exact (MK_COMB (@lem7140007 x) (@lem7140008 y)). Qed.
Lemma lem7140011 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7140012 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem7140011 real Prop f x). Qed.
Lemma lem7140013 (x : real) (y : real) : (@I (real -> real -> Prop) real_le x y) = (term388 x y).
Proof. exact (@lem7140012 (@I (real -> real -> Prop) real_le x) y). Qed.
Lemma lem7140015 (x : real) (y : real) : (real_le x y) = (term388 x y).
Proof. exact (TRANS (@lem7140009 x y) (@lem7140013 x y)). Qed.
Lemma lem7140016 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7140023 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7140024 (f : type1626) (x : real) : (f x) = (@I (real -> real -> Prop) f x).
Proof. exact (@lem7140023 real (real -> Prop) f x). Qed.
Lemma lem7140025 (x : real) : (real_lt x) = (@I (real -> real -> Prop) real_lt x).
Proof. exact (@lem7140024 real_lt x). Qed.
Lemma lem7140026 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem7140027 (x : real) (y : real) : (real_lt x y) = (@I (real -> real -> Prop) real_lt x y).
Proof. exact (MK_COMB (@lem7140025 x) (@lem7140026 y)). Qed.
Lemma lem7140029 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7140030 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem7140029 real Prop f x). Qed.
Lemma lem7140031 (x : real) (y : real) : (@I (real -> real -> Prop) real_lt x y) = (term389 x y).
Proof. exact (@lem7140030 (@I (real -> real -> Prop) real_lt x) y). Qed.
Lemma lem7140033 (x : real) (y : real) : (real_lt x y) = (term389 x y).
Proof. exact (TRANS (@lem7140027 x y) (@lem7140031 x y)). Qed.
Lemma lem7140034 (x : real) (y : real) : (term390 x y) = (term391 x y).
Proof. exact (MK_COMB (@lem7140016) (@lem7140033 x y)). Qed.
Lemma lem7140035 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7140036 (x : real) (y : real) : (term392 x y) = (term393 x y).
Proof. exact (MK_COMB (@lem7140035) (@lem7140034 x y)). Qed.
Lemma lem7140037 (x : real) (y : real) : (term277 x y) = (term394 x y).
Proof. exact (MK_COMB (@lem7140036 x y) (@lem7140015 x y)). Qed.
Lemma lem7140038 (x : real) : (term278 x) = (term395 x).
Proof. exact (fun_ext (fun y : real => @lem7140037 x y)). Qed.
Lemma lem7140039 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7140040 (x : real) : (term279 x) = (term396 x).
Proof. exact (MK_COMB (@lem7140039) (@lem7140038 x)). Qed.
Lemma lem7140041 : term280 = term397.
Proof. exact (fun_ext (fun x : real => @lem7140040 x)). Qed.
Lemma lem7140042 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7140043 : term281 = term398.
Proof. exact (MK_COMB (@lem7140042) (@lem7140041)). Qed.
Lemma lem7140044 (h1 : term38) : term398.
Proof. exact (EQ_MP (@lem7140043) (@lem7139738 h1)). Qed.
Lemma lem7140051 {_133668 : Type'} (s : _133668 -> Prop) : (term29 _133668 s) = (term29 _133668 s).
Proof. exact (eq_refl (term29 _133668 s)). Qed.
Lemma lem7140052 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7140059 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7140060 {_133668 : Type'} (f : type1364 _133668) (x : _133668) : (f x) = (@I (_133668 -> (_133668 -> Prop) -> Prop) f x).
Proof. exact (@lem7140059 _133668 (type686 _133668) f x). Qed.
Lemma lem7140061 {_133668 : Type'} (x : _133668) : (@IN _133668 x) = (@I (_133668 -> (_133668 -> Prop) -> Prop) (@IN _133668) x).
Proof. exact (@lem7140060 _133668 (@IN _133668) x). Qed.
Lemma lem7140062 {_133668 : Type'} (s : _133668 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7140063 {_133668 : Type'} (x : _133668) (s : _133668 -> Prop) : (@IN _133668 x s) = (@I (_133668 -> (_133668 -> Prop) -> Prop) (@IN _133668) x s).
Proof. exact (MK_COMB (@lem7140061 _133668 x) (@lem7140062 _133668 s)). Qed.
Lemma lem7140065 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7140066 {_133668 : Type'} (f : type686 _133668) (x : _133668 -> Prop) : (f x) = (@I ((_133668 -> Prop) -> Prop) f x).
Proof. exact (@lem7140065 (_133668 -> Prop) Prop f x). Qed.
Lemma lem7140067 {_133668 : Type'} (x : _133668) (s : _133668 -> Prop) : (@I (_133668 -> (_133668 -> Prop) -> Prop) (@IN _133668) x s) = (term399 _133668 x s).
Proof. exact (@lem7140066 _133668 (@I (_133668 -> (_133668 -> Prop) -> Prop) (@IN _133668) x) s). Qed.
Lemma lem7140069 {_133668 : Type'} (x : _133668) (s : _133668 -> Prop) : (@IN _133668 x s) = (term399 _133668 x s).
Proof. exact (TRANS (@lem7140063 _133668 x s) (@lem7140067 _133668 x s)). Qed.
Lemma lem7140070 {_133668 : Type'} (x : _133668) (s : _133668 -> Prop) : (term286 _133668 x s) = (term400 _133668 x s).
Proof. exact (MK_COMB (@lem7140052) (@lem7140069 _133668 x s)). Qed.
Lemma lem7140071 {_133668 : Type'} (s : _133668 -> Prop) : (term288 _133668 s) = (term401 _133668 s).
Proof. exact (fun_ext (fun x : _133668 => @lem7140070 _133668 x s)). Qed.
Lemma lem7140072 {_133668 : Type'} : (@all _133668) = (@all _133668).
Proof. exact (eq_refl (@all _133668)). Qed.
Lemma lem7140073 {_133668 : Type'} (s : _133668 -> Prop) : (term289 _133668 s) = (term402 _133668 s).
Proof. exact (MK_COMB (@lem7140072 _133668) (@lem7140071 _133668 s)). Qed.
Lemma lem7140074 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7140075 {_133668 : Type'} (s : _133668 -> Prop) : (term292 _133668 s) = (term403 _133668 s).
Proof. exact (MK_COMB (@lem7140074) (@lem7140073 _133668 s)). Qed.
Lemma lem7140076 {_133668 : Type'} (s : _133668 -> Prop) : (term294 _133668 s) = (term404 _133668 s).
Proof. exact (MK_COMB (@lem7140075 _133668 s) (@lem7140051 _133668 s)). Qed.
Lemma lem7140077 {_133668 : Type'} : (term311 _133668) = (term405 _133668).
Proof. exact (fun_ext (fun s : _133668 -> Prop => @lem7140076 _133668 s)). Qed.
Lemma lem7140078 {_133668 : Type'} : (@all (_133668 -> Prop)) = (@all (_133668 -> Prop)).
Proof. exact (eq_refl (@all (_133668 -> Prop))). Qed.
Lemma lem7140079 {_133668 : Type'} : (term326 _133668) = (term406 _133668).
Proof. exact (MK_COMB (@lem7140078 _133668) (@lem7140077 _133668)). Qed.
Lemma lem7140084 {_133668 : Type'} (s : _133668 -> Prop) : (s = (@EMPTY _133668)) = (s = (@EMPTY _133668)).
Proof. exact (eq_refl (s = (@EMPTY _133668))). Qed.
Lemma lem7140085 {_133668 : Type'} : (@IN _133668) = (@IN _133668).
Proof. exact (eq_refl (@IN _133668)). Qed.
Lemma lem7140090 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7140091 {_133668 : Type'} (f : type684 _133668) (x : _133668 -> Prop) : (f x) = (@I ((_133668 -> Prop) -> _133668) f x).
Proof. exact (@lem7140090 (_133668 -> Prop) _133668 f x). Qed.
Lemma lem7140093 {_133668 : Type'} (x : type684 _133668) (s : _133668 -> Prop) : (x s) = (@I ((_133668 -> Prop) -> _133668) x s).
Proof. exact (@lem7140091 _133668 x s). Qed.
Lemma lem7140094 {_133668 : Type'} (s : _133668 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7140095 {_133668 : Type'} (x : type684 _133668) (s : _133668 -> Prop) : (term407 _133668 x s) = (term408 _133668 x s).
Proof. exact (MK_COMB (@lem7140085 _133668) (@lem7140093 _133668 x s)). Qed.
Lemma lem7140096 {_133668 : Type'} (x : type684 _133668) (s : _133668 -> Prop) : (term409 _133668 x s) = (term410 _133668 x s).
Proof. exact (MK_COMB (@lem7140095 _133668 x s) (@lem7140094 _133668 s)). Qed.
Lemma lem7140098 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7140099 {_133668 : Type'} (f : type1364 _133668) (x : _133668) : (f x) = (@I (_133668 -> (_133668 -> Prop) -> Prop) f x).
Proof. exact (@lem7140098 _133668 (type686 _133668) f x). Qed.
Lemma lem7140100 {_133668 : Type'} (x : type684 _133668) (s : _133668 -> Prop) : (term408 _133668 x s) = (term411 _133668 x s).
Proof. exact (@lem7140099 _133668 (@IN _133668) (@I ((_133668 -> Prop) -> _133668) x s)). Qed.
Lemma lem7140101 {_133668 : Type'} (s : _133668 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7140102 {_133668 : Type'} (x : type684 _133668) (s : _133668 -> Prop) : (term410 _133668 x s) = (term412 _133668 x s).
Proof. exact (MK_COMB (@lem7140100 _133668 x s) (@lem7140101 _133668 s)). Qed.
Lemma lem7140104 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7140105 {_133668 : Type'} (f : type686 _133668) (x : _133668 -> Prop) : (f x) = (@I ((_133668 -> Prop) -> Prop) f x).
Proof. exact (@lem7140104 (_133668 -> Prop) Prop f x). Qed.
Lemma lem7140106 {_133668 : Type'} (x : type684 _133668) (s : _133668 -> Prop) : (term412 _133668 x s) = (term413 _133668 x s).
Proof. exact (@lem7140105 _133668 (term411 _133668 x s) s). Qed.
Lemma lem7140107 {_133668 : Type'} (x : type684 _133668) (s : _133668 -> Prop) : (term410 _133668 x s) = (term413 _133668 x s).
Proof. exact (TRANS (@lem7140102 _133668 x s) (@lem7140106 _133668 x s)). Qed.
Lemma lem7140108 {_133668 : Type'} (x : type684 _133668) (s : _133668 -> Prop) : (term409 _133668 x s) = (term413 _133668 x s).
Proof. exact (TRANS (@lem7140096 _133668 x s) (@lem7140107 _133668 x s)). Qed.
Lemma lem7140109 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7140110 {_133668 : Type'} (x : type684 _133668) (s : _133668 -> Prop) : (term414 _133668 x s) = (term415 _133668 x s).
Proof. exact (MK_COMB (@lem7140109) (@lem7140108 _133668 x s)). Qed.
Lemma lem7140111 {_133668 : Type'} (x : type684 _133668) (s : _133668 -> Prop) : (term359 _133668 x s) = (term416 _133668 x s).
Proof. exact (MK_COMB (@lem7140110 _133668 x s) (@lem7140084 _133668 s)). Qed.
Lemma lem7140112 {_133668 : Type'} (x : type684 _133668) : (term361 _133668 x) = (term417 _133668 x).
Proof. exact (fun_ext (fun s : _133668 -> Prop => @lem7140111 _133668 x s)). Qed.
Lemma lem7140113 {_133668 : Type'} : (@all (_133668 -> Prop)) = (@all (_133668 -> Prop)).
Proof. exact (eq_refl (@all (_133668 -> Prop))). Qed.
Lemma lem7140114 {_133668 : Type'} (x : type684 _133668) : (term363 _133668 x) = (term418 _133668 x).
Proof. exact (MK_COMB (@lem7140113 _133668) (@lem7140112 _133668 x)). Qed.
Lemma lem7140115 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7140116 {_133668 : Type'} (x : type684 _133668) : (term382 _133668 x) = (term419 _133668 x).
Proof. exact (MK_COMB (@lem7140115) (@lem7140114 _133668 x)). Qed.
Lemma lem7140117 {_133668 : Type'} (x : type684 _133668) : (term384 _133668 x) = (term420 _133668 x).
Proof. exact (MK_COMB (@lem7140116 _133668 x) (@lem7140079 _133668)). Qed.
Lemma lem7140118 {_133668 : Type'} (x : type684 _133668) (h1 : term384 _133668 x) : term420 _133668 x.
Proof. exact (EQ_MP (@lem7140117 _133668 x) (@lem7139993 _133668 x h1)). Qed.
Lemma lem7140357 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7140364 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7140365 {_133668 : Type'} (f : type646 _133668) (x : _133668 -> Prop) : (f x) = (@I ((_133668 -> Prop) -> (_133668 -> real) -> real) f x).
Proof. exact (@lem7140364 (_133668 -> Prop) (type717 _133668) f x). Qed.
Lemma lem7140366 {_133668 : Type'} (s : _133668 -> Prop) : (@sum _133668 s) = (@I ((_133668 -> Prop) -> (_133668 -> real) -> real) (@sum _133668) s).
Proof. exact (@lem7140365 _133668 (@sum _133668) s). Qed.
Lemma lem7140367 {_133668 : Type'} (f : _133668 -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7140368 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) : (@sum _133668 s f) = (@I ((_133668 -> Prop) -> (_133668 -> real) -> real) (@sum _133668) s f).
Proof. exact (MK_COMB (@lem7140366 _133668 s) (@lem7140367 _133668 f)). Qed.
Lemma lem7140370 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7140371 {_133668 : Type'} (f : type717 _133668) (x : _133668 -> real) : (f x) = (@I ((_133668 -> real) -> real) f x).
Proof. exact (@lem7140370 (_133668 -> real) real f x). Qed.
Lemma lem7140372 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) : (@I ((_133668 -> Prop) -> (_133668 -> real) -> real) (@sum _133668) s f) = (term421 _133668 s f).
Proof. exact (@lem7140371 _133668 (@I ((_133668 -> Prop) -> (_133668 -> real) -> real) (@sum _133668) s) f). Qed.
Lemma lem7140374 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) : (@sum _133668 s f) = (term421 _133668 s f).
Proof. exact (TRANS (@lem7140368 _133668 s f) (@lem7140372 _133668 s f)). Qed.
Lemma lem7140375 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7140376 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7140381 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7140382 {_133668 : Type'} (f : type687 _133668) (x : _133668 -> Prop) : (f x) = (@I ((_133668 -> Prop) -> nat) f x).
Proof. exact (@lem7140381 (_133668 -> Prop) nat f x). Qed.
Lemma lem7140384 {_133668 : Type'} (s : _133668 -> Prop) : (@CARD _133668 s) = (@I ((_133668 -> Prop) -> nat) (@CARD _133668) s).
Proof. exact (@lem7140382 _133668 (@CARD _133668) s). Qed.
Lemma lem7140385 {_133668 : Type'} (s : _133668 -> Prop) : (term422 _133668 s) = (term423 _133668 s).
Proof. exact (MK_COMB (@lem7140376) (@lem7140384 _133668 s)). Qed.
Lemma lem7140387 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7140388 (f : nat -> real) (x : nat) : (f x) = (@I (nat -> real) f x).
Proof. exact (@lem7140387 nat real f x). Qed.
Lemma lem7140389 {_133668 : Type'} (s : _133668 -> Prop) : (term423 _133668 s) = (term424 _133668 s).
Proof. exact (@lem7140388 real_of_num (@I ((_133668 -> Prop) -> nat) (@CARD _133668) s)). Qed.
Lemma lem7140390 {_133668 : Type'} (s : _133668 -> Prop) : (term422 _133668 s) = (term424 _133668 s).
Proof. exact (TRANS (@lem7140385 _133668 s) (@lem7140389 _133668 s)). Qed.
Lemma lem7140391 (b : real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem7140392 {_133668 : Type'} (s : _133668 -> Prop) : (term425 _133668 s) = (term426 _133668 s).
Proof. exact (MK_COMB (@lem7140375) (@lem7140390 _133668 s)). Qed.
Lemma lem7140393 {_133668 : Type'} (s : _133668 -> Prop) (b : real) : (term427 _133668 s b) = (term428 _133668 s b).
Proof. exact (MK_COMB (@lem7140392 _133668 s) (@lem7140391 b)). Qed.
Lemma lem7140395 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7140396 (f : type1627) (x : real) : (f x) = (@I (real -> real -> real) f x).
Proof. exact (@lem7140395 real (real -> real) f x). Qed.
Lemma lem7140397 {_133668 : Type'} (s : _133668 -> Prop) : (term426 _133668 s) = (term429 _133668 s).
Proof. exact (@lem7140396 real_mul (term424 _133668 s)). Qed.
Lemma lem7140398 (b : real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem7140399 {_133668 : Type'} (s : _133668 -> Prop) (b : real) : (term428 _133668 s b) = (term430 _133668 s b).
Proof. exact (MK_COMB (@lem7140397 _133668 s) (@lem7140398 b)). Qed.
Lemma lem7140401 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7140402 (f : real -> real) (x : real) : (f x) = (@I (real -> real) f x).
Proof. exact (@lem7140401 real real f x). Qed.
Lemma lem7140403 {_133668 : Type'} (s : _133668 -> Prop) (b : real) : (term430 _133668 s b) = (term431 _133668 s b).
Proof. exact (@lem7140402 (term429 _133668 s) b). Qed.
Lemma lem7140404 {_133668 : Type'} (s : _133668 -> Prop) (b : real) : (term428 _133668 s b) = (term431 _133668 s b).
Proof. exact (TRANS (@lem7140399 _133668 s b) (@lem7140403 _133668 s b)). Qed.
Lemma lem7140405 {_133668 : Type'} (s : _133668 -> Prop) (b : real) : (term427 _133668 s b) = (term431 _133668 s b).
Proof. exact (TRANS (@lem7140393 _133668 s b) (@lem7140404 _133668 s b)). Qed.
Lemma lem7140406 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) : (term432 _133668 s f) = (term433 _133668 s f).
Proof. exact (MK_COMB (@lem7140357) (@lem7140374 _133668 s f)). Qed.
Lemma lem7140407 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term39 _133668 f s b) = (term434 _133668 f s b).
Proof. exact (MK_COMB (@lem7140406 _133668 s f) (@lem7140405 _133668 s b)). Qed.
Lemma lem7140409 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7140410 (f : type1626) (x : real) : (f x) = (@I (real -> real -> Prop) f x).
Proof. exact (@lem7140409 real (real -> Prop) f x). Qed.
Lemma lem7140411 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) : (term433 _133668 s f) = (term435 _133668 s f).
Proof. exact (@lem7140410 real_lt (term421 _133668 s f)). Qed.
Lemma lem7140412 {_133668 : Type'} (s : _133668 -> Prop) (b : real) : (term431 _133668 s b) = (term431 _133668 s b).
Proof. exact (eq_refl (term431 _133668 s b)). Qed.
Lemma lem7140413 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term434 _133668 f s b) = (term436 _133668 f s b).
Proof. exact (MK_COMB (@lem7140411 _133668 s f) (@lem7140412 _133668 s b)). Qed.
Lemma lem7140415 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7140416 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem7140415 real Prop f x). Qed.
Lemma lem7140417 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term436 _133668 f s b) = (term437 _133668 f s b).
Proof. exact (@lem7140416 (term435 _133668 s f) (term431 _133668 s b)). Qed.
Lemma lem7140418 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term434 _133668 f s b) = (term437 _133668 f s b).
Proof. exact (TRANS (@lem7140413 _133668 f s b) (@lem7140417 _133668 f s b)). Qed.
Lemma lem7140419 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term39 _133668 f s b) = (term437 _133668 f s b).
Proof. exact (TRANS (@lem7140407 _133668 f s b) (@lem7140418 _133668 f s b)). Qed.
Lemma lem7140420 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7140421 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7140426 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7140428 {_133668 : Type'} (f : _133668 -> real) (x : _133668) : (f x) = (@I (_133668 -> real) f x).
Proof. exact (@lem7140426 _133668 real f x). Qed.
Lemma lem7140429 (b : real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem7140430 {_133668 : Type'} (f : _133668 -> real) (x : _133668) : (term438 _133668 f x) = (term439 _133668 f x).
Proof. exact (MK_COMB (@lem7140421) (@lem7140428 _133668 f x)). Qed.
Lemma lem7140431 {_133668 : Type'} (f : _133668 -> real) (x : _133668) (b : real) : (term71 _133668 f x b) = (term440 _133668 f x b).
Proof. exact (MK_COMB (@lem7140430 _133668 f x) (@lem7140429 b)). Qed.
Lemma lem7140433 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7140434 (f : type1626) (x : real) : (f x) = (@I (real -> real -> Prop) f x).
Proof. exact (@lem7140433 real (real -> Prop) f x). Qed.
Lemma lem7140435 {_133668 : Type'} (f : _133668 -> real) (x : _133668) : (term439 _133668 f x) = (term441 _133668 f x).
Proof. exact (@lem7140434 real_lt (@I (_133668 -> real) f x)). Qed.
Lemma lem7140436 (b : real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem7140437 {_133668 : Type'} (f : _133668 -> real) (x : _133668) (b : real) : (term440 _133668 f x b) = (term442 _133668 f x b).
Proof. exact (MK_COMB (@lem7140435 _133668 f x) (@lem7140436 b)). Qed.
Lemma lem7140439 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7140440 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem7140439 real Prop f x). Qed.
Lemma lem7140441 {_133668 : Type'} (f : _133668 -> real) (x : _133668) (b : real) : (term442 _133668 f x b) = (term443 _133668 f x b).
Proof. exact (@lem7140440 (term441 _133668 f x) b). Qed.
Lemma lem7140442 {_133668 : Type'} (f : _133668 -> real) (x : _133668) (b : real) : (term440 _133668 f x b) = (term443 _133668 f x b).
Proof. exact (TRANS (@lem7140437 _133668 f x b) (@lem7140441 _133668 f x b)). Qed.
Lemma lem7140443 {_133668 : Type'} (f : _133668 -> real) (x : _133668) (b : real) : (term71 _133668 f x b) = (term443 _133668 f x b).
Proof. exact (TRANS (@lem7140431 _133668 f x b) (@lem7140442 _133668 f x b)). Qed.
Lemma lem7140444 {_133668 : Type'} (f : _133668 -> real) (x : _133668) (b : real) : (term444 _133668 f x b) = (term445 _133668 f x b).
Proof. exact (MK_COMB (@lem7140420) (@lem7140443 _133668 f x b)). Qed.
Lemma lem7140445 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7140452 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7140453 {_133668 : Type'} (f : type1364 _133668) (x : _133668) : (f x) = (@I (_133668 -> (_133668 -> Prop) -> Prop) f x).
Proof. exact (@lem7140452 _133668 (type686 _133668) f x). Qed.
Lemma lem7140454 {_133668 : Type'} (x : _133668) : (@IN _133668 x) = (@I (_133668 -> (_133668 -> Prop) -> Prop) (@IN _133668) x).
Proof. exact (@lem7140453 _133668 (@IN _133668) x). Qed.
Lemma lem7140455 {_133668 : Type'} (s : _133668 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7140456 {_133668 : Type'} (x : _133668) (s : _133668 -> Prop) : (@IN _133668 x s) = (@I (_133668 -> (_133668 -> Prop) -> Prop) (@IN _133668) x s).
Proof. exact (MK_COMB (@lem7140454 _133668 x) (@lem7140455 _133668 s)). Qed.
Lemma lem7140458 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7140459 {_133668 : Type'} (f : type686 _133668) (x : _133668 -> Prop) : (f x) = (@I ((_133668 -> Prop) -> Prop) f x).
Proof. exact (@lem7140458 (_133668 -> Prop) Prop f x). Qed.
Lemma lem7140460 {_133668 : Type'} (x : _133668) (s : _133668 -> Prop) : (@I (_133668 -> (_133668 -> Prop) -> Prop) (@IN _133668) x s) = (term399 _133668 x s).
Proof. exact (@lem7140459 _133668 (@I (_133668 -> (_133668 -> Prop) -> Prop) (@IN _133668) x) s). Qed.
Lemma lem7140462 {_133668 : Type'} (x : _133668) (s : _133668 -> Prop) : (@IN _133668 x s) = (term399 _133668 x s).
Proof. exact (TRANS (@lem7140456 _133668 x s) (@lem7140460 _133668 x s)). Qed.
Lemma lem7140463 {_133668 : Type'} (x : _133668) (s : _133668 -> Prop) : (term286 _133668 x s) = (term400 _133668 x s).
Proof. exact (MK_COMB (@lem7140445) (@lem7140462 _133668 x s)). Qed.
Lemma lem7140464 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7140465 {_133668 : Type'} (x : _133668) (s : _133668 -> Prop) : (term446 _133668 x s) = (term447 _133668 x s).
Proof. exact (MK_COMB (@lem7140464) (@lem7140463 _133668 x s)). Qed.
Lemma lem7140466 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (x : _133668) (b : real) : (term121 _133668 s f x b) = (term448 _133668 s f x b).
Proof. exact (MK_COMB (@lem7140465 _133668 x s) (@lem7140444 _133668 f x b)). Qed.
Lemma lem7140467 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term129 _133668 s f b) = (term449 _133668 s f b).
Proof. exact (fun_ext (fun x : _133668 => @lem7140466 _133668 s f x b)). Qed.
Lemma lem7140468 {_133668 : Type'} : (@all _133668) = (@all _133668).
Proof. exact (eq_refl (@all _133668)). Qed.
Lemma lem7140469 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term130 _133668 s f b) = (term450 _133668 s f b).
Proof. exact (MK_COMB (@lem7140468 _133668) (@lem7140467 _133668 s f b)). Qed.
Lemma lem7140470 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7140471 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7140472 {_133668 : Type'} (f : _133668 -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7140481 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7140482 {_133668 : Type'} (f : type645 _133668) (x : _133668 -> Prop) : (f x) = (@I ((_133668 -> Prop) -> (_133668 -> real) -> real -> _133668) f x).
Proof. exact (@lem7140481 (_133668 -> Prop) (type715 _133668) f x). Qed.
Lemma lem7140483 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) : (x'' s) = (@I ((_133668 -> Prop) -> (_133668 -> real) -> real -> _133668) x'' s).
Proof. exact (@lem7140482 _133668 x'' s). Qed.
Lemma lem7140484 {_133668 : Type'} (f : _133668 -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7140485 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) (f : _133668 -> real) : (x'' s f) = (@I ((_133668 -> Prop) -> (_133668 -> real) -> real -> _133668) x'' s f).
Proof. exact (MK_COMB (@lem7140483 _133668 x'' s) (@lem7140484 _133668 f)). Qed.
Lemma lem7140487 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7140488 {_133668 : Type'} (f : type715 _133668) (x : _133668 -> real) : (f x) = (@I ((_133668 -> real) -> real -> _133668) f x).
Proof. exact (@lem7140487 (_133668 -> real) (real -> _133668) f x). Qed.
Lemma lem7140489 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) (f : _133668 -> real) : (@I ((_133668 -> Prop) -> (_133668 -> real) -> real -> _133668) x'' s f) = (term451 _133668 x'' s f).
Proof. exact (@lem7140488 _133668 (@I ((_133668 -> Prop) -> (_133668 -> real) -> real -> _133668) x'' s) f). Qed.
Lemma lem7140490 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) (f : _133668 -> real) : (x'' s f) = (term451 _133668 x'' s f).
Proof. exact (TRANS (@lem7140485 _133668 x'' s f) (@lem7140489 _133668 x'' s f)). Qed.
Lemma lem7140491 (b : real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem7140492 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (x'' s f b) = (term452 _133668 x'' s f b).
Proof. exact (MK_COMB (@lem7140490 _133668 x'' s f) (@lem7140491 b)). Qed.
Lemma lem7140494 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7140495 {_133668 : Type'} (f : real -> _133668) (x : real) : (f x) = (@I (real -> _133668) f x).
Proof. exact (@lem7140494 real _133668 f x). Qed.
Lemma lem7140496 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term452 _133668 x'' s f b) = (term453 _133668 x'' s f b).
Proof. exact (@lem7140495 _133668 (term451 _133668 x'' s f) b). Qed.
Lemma lem7140498 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (x'' s f b) = (term453 _133668 x'' s f b).
Proof. exact (TRANS (@lem7140492 _133668 x'' s f b) (@lem7140496 _133668 x'' s f b)). Qed.
Lemma lem7140499 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term454 _133668 x'' s f b) = (term455 _133668 x'' s f b).
Proof. exact (MK_COMB (@lem7140472 _133668 f) (@lem7140498 _133668 x'' s f b)). Qed.
Lemma lem7140501 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7140502 {_133668 : Type'} (f : _133668 -> real) (x : _133668) : (f x) = (@I (_133668 -> real) f x).
Proof. exact (@lem7140501 _133668 real f x). Qed.
Lemma lem7140503 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term455 _133668 x'' s f b) = (term456 _133668 x'' s f b).
Proof. exact (@lem7140502 _133668 f (term453 _133668 x'' s f b)). Qed.
Lemma lem7140504 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term454 _133668 x'' s f b) = (term456 _133668 x'' s f b).
Proof. exact (TRANS (@lem7140499 _133668 x'' s f b) (@lem7140503 _133668 x'' s f b)). Qed.
Lemma lem7140505 (b : real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem7140506 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term457 _133668 x'' s f b) = (term458 _133668 x'' s f b).
Proof. exact (MK_COMB (@lem7140471) (@lem7140504 _133668 x'' s f b)). Qed.
Lemma lem7140507 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term459 _133668 x'' s f b) = (term460 _133668 x'' s f b).
Proof. exact (MK_COMB (@lem7140506 _133668 x'' s f b) (@lem7140505 b)). Qed.
Lemma lem7140509 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7140510 (f : type1626) (x : real) : (f x) = (@I (real -> real -> Prop) f x).
Proof. exact (@lem7140509 real (real -> Prop) f x). Qed.
Lemma lem7140511 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term458 _133668 x'' s f b) = (term461 _133668 x'' s f b).
Proof. exact (@lem7140510 real_le (term456 _133668 x'' s f b)). Qed.
Lemma lem7140512 (b : real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem7140513 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term460 _133668 x'' s f b) = (term462 _133668 x'' s f b).
Proof. exact (MK_COMB (@lem7140511 _133668 x'' s f b) (@lem7140512 b)). Qed.
Lemma lem7140515 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7140516 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem7140515 real Prop f x). Qed.
Lemma lem7140517 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term462 _133668 x'' s f b) = (term463 _133668 x'' s f b).
Proof. exact (@lem7140516 (term461 _133668 x'' s f b) b). Qed.
Lemma lem7140518 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term460 _133668 x'' s f b) = (term463 _133668 x'' s f b).
Proof. exact (TRANS (@lem7140513 _133668 x'' s f b) (@lem7140517 _133668 x'' s f b)). Qed.
Lemma lem7140519 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term459 _133668 x'' s f b) = (term463 _133668 x'' s f b).
Proof. exact (TRANS (@lem7140507 _133668 x'' s f b) (@lem7140518 _133668 x'' s f b)). Qed.
Lemma lem7140520 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term464 _133668 x'' s f b) = (term465 _133668 x'' s f b).
Proof. exact (MK_COMB (@lem7140470) (@lem7140519 _133668 x'' s f b)). Qed.
Lemma lem7140521 {_133668 : Type'} : (@IN _133668) = (@IN _133668).
Proof. exact (eq_refl (@IN _133668)). Qed.
Lemma lem7140530 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7140531 {_133668 : Type'} (f : type645 _133668) (x : _133668 -> Prop) : (f x) = (@I ((_133668 -> Prop) -> (_133668 -> real) -> real -> _133668) f x).
Proof. exact (@lem7140530 (_133668 -> Prop) (type715 _133668) f x). Qed.
Lemma lem7140532 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) : (x'' s) = (@I ((_133668 -> Prop) -> (_133668 -> real) -> real -> _133668) x'' s).
Proof. exact (@lem7140531 _133668 x'' s). Qed.
Lemma lem7140533 {_133668 : Type'} (f : _133668 -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7140534 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) (f : _133668 -> real) : (x'' s f) = (@I ((_133668 -> Prop) -> (_133668 -> real) -> real -> _133668) x'' s f).
Proof. exact (MK_COMB (@lem7140532 _133668 x'' s) (@lem7140533 _133668 f)). Qed.
Lemma lem7140536 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7140537 {_133668 : Type'} (f : type715 _133668) (x : _133668 -> real) : (f x) = (@I ((_133668 -> real) -> real -> _133668) f x).
Proof. exact (@lem7140536 (_133668 -> real) (real -> _133668) f x). Qed.
Lemma lem7140538 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) (f : _133668 -> real) : (@I ((_133668 -> Prop) -> (_133668 -> real) -> real -> _133668) x'' s f) = (term451 _133668 x'' s f).
Proof. exact (@lem7140537 _133668 (@I ((_133668 -> Prop) -> (_133668 -> real) -> real -> _133668) x'' s) f). Qed.
Lemma lem7140539 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) (f : _133668 -> real) : (x'' s f) = (term451 _133668 x'' s f).
Proof. exact (TRANS (@lem7140534 _133668 x'' s f) (@lem7140538 _133668 x'' s f)). Qed.
Lemma lem7140540 (b : real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem7140541 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (x'' s f b) = (term452 _133668 x'' s f b).
Proof. exact (MK_COMB (@lem7140539 _133668 x'' s f) (@lem7140540 b)). Qed.
Lemma lem7140543 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7140544 {_133668 : Type'} (f : real -> _133668) (x : real) : (f x) = (@I (real -> _133668) f x).
Proof. exact (@lem7140543 real _133668 f x). Qed.
Lemma lem7140545 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term452 _133668 x'' s f b) = (term453 _133668 x'' s f b).
Proof. exact (@lem7140544 _133668 (term451 _133668 x'' s f) b). Qed.
Lemma lem7140547 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (x'' s f b) = (term453 _133668 x'' s f b).
Proof. exact (TRANS (@lem7140541 _133668 x'' s f b) (@lem7140545 _133668 x'' s f b)). Qed.
Lemma lem7140548 {_133668 : Type'} (s : _133668 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7140549 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term466 _133668 x'' s f b) = (term467 _133668 x'' s f b).
Proof. exact (MK_COMB (@lem7140521 _133668) (@lem7140547 _133668 x'' s f b)). Qed.
Lemma lem7140550 {_133668 : Type'} (x'' : type645 _133668) (f : _133668 -> real) (b : real) (s : _133668 -> Prop) : (term468 _133668 x'' f b s) = (term469 _133668 x'' f b s).
Proof. exact (MK_COMB (@lem7140549 _133668 x'' s f b) (@lem7140548 _133668 s)). Qed.
Lemma lem7140552 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7140553 {_133668 : Type'} (f : type1364 _133668) (x : _133668) : (f x) = (@I (_133668 -> (_133668 -> Prop) -> Prop) f x).
Proof. exact (@lem7140552 _133668 (type686 _133668) f x). Qed.
Lemma lem7140554 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term467 _133668 x'' s f b) = (term470 _133668 x'' s f b).
Proof. exact (@lem7140553 _133668 (@IN _133668) (term453 _133668 x'' s f b)). Qed.
Lemma lem7140555 {_133668 : Type'} (s : _133668 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7140556 {_133668 : Type'} (x'' : type645 _133668) (f : _133668 -> real) (b : real) (s : _133668 -> Prop) : (term469 _133668 x'' f b s) = (term471 _133668 x'' f b s).
Proof. exact (MK_COMB (@lem7140554 _133668 x'' s f b) (@lem7140555 _133668 s)). Qed.
Lemma lem7140558 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7140559 {_133668 : Type'} (f : type686 _133668) (x : _133668 -> Prop) : (f x) = (@I ((_133668 -> Prop) -> Prop) f x).
Proof. exact (@lem7140558 (_133668 -> Prop) Prop f x). Qed.
Lemma lem7140560 {_133668 : Type'} (x'' : type645 _133668) (f : _133668 -> real) (b : real) (s : _133668 -> Prop) : (term471 _133668 x'' f b s) = (term472 _133668 x'' f b s).
Proof. exact (@lem7140559 _133668 (term470 _133668 x'' s f b) s). Qed.
Lemma lem7140561 {_133668 : Type'} (x'' : type645 _133668) (f : _133668 -> real) (b : real) (s : _133668 -> Prop) : (term469 _133668 x'' f b s) = (term472 _133668 x'' f b s).
Proof. exact (TRANS (@lem7140556 _133668 x'' f b s) (@lem7140560 _133668 x'' f b s)). Qed.
Lemma lem7140562 {_133668 : Type'} (x'' : type645 _133668) (f : _133668 -> real) (b : real) (s : _133668 -> Prop) : (term468 _133668 x'' f b s) = (term472 _133668 x'' f b s).
Proof. exact (TRANS (@lem7140550 _133668 x'' f b s) (@lem7140561 _133668 x'' f b s)). Qed.
Lemma lem7140563 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7140564 {_133668 : Type'} (x'' : type645 _133668) (f : _133668 -> real) (b : real) (s : _133668 -> Prop) : (term473 _133668 x'' f b s) = (term474 _133668 x'' f b s).
Proof. exact (MK_COMB (@lem7140563) (@lem7140562 _133668 x'' f b s)). Qed.
Lemma lem7140565 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term475 _133668 x'' s f b) = (term476 _133668 x'' s f b).
Proof. exact (MK_COMB (@lem7140564 _133668 x'' f b s) (@lem7140520 _133668 x'' s f b)). Qed.
Lemma lem7140566 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7140567 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term477 _133668 x'' s f b) = (term478 _133668 x'' s f b).
Proof. exact (MK_COMB (@lem7140566) (@lem7140565 _133668 x'' s f b)). Qed.
Lemma lem7140568 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term479 _133668 x'' s f b) = (term480 _133668 x'' s f b).
Proof. exact (MK_COMB (@lem7140567 _133668 x'' s f b) (@lem7140469 _133668 s f b)). Qed.
Lemma lem7140569 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7140574 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7140575 {_133668 : Type'} (f : type686 _133668) (x : _133668 -> Prop) : (f x) = (@I ((_133668 -> Prop) -> Prop) f x).
Proof. exact (@lem7140574 (_133668 -> Prop) Prop f x). Qed.
Lemma lem7140577 {_133668 : Type'} (s : _133668 -> Prop) : (@FINITE _133668 s) = (@I ((_133668 -> Prop) -> Prop) (@FINITE _133668) s).
Proof. exact (@lem7140575 _133668 (@FINITE _133668) s). Qed.
Lemma lem7140578 {_133668 : Type'} (s : _133668 -> Prop) : (term172 _133668 s) = (term481 _133668 s).
Proof. exact (MK_COMB (@lem7140569) (@lem7140577 _133668 s)). Qed.
Lemma lem7140579 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7140580 {_133668 : Type'} (s : _133668 -> Prop) : (term136 _133668 s) = (term482 _133668 s).
Proof. exact (MK_COMB (@lem7140579) (@lem7140578 _133668 s)). Qed.
Lemma lem7140581 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term483 _133668 x'' s f b) = (term484 _133668 x'' s f b).
Proof. exact (MK_COMB (@lem7140580 _133668 s) (@lem7140568 _133668 x'' s f b)). Qed.
Lemma lem7140582 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7140583 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term485 _133668 x'' s f b) = (term486 _133668 x'' s f b).
Proof. exact (MK_COMB (@lem7140582) (@lem7140581 _133668 x'' s f b)). Qed.
Lemma lem7140584 {_133668 : Type'} (x'' : type645 _133668) (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term487 _133668 x'' f s b) = (term488 _133668 x'' f s b).
Proof. exact (MK_COMB (@lem7140583 _133668 x'' s f b) (@lem7140419 _133668 f s b)). Qed.
Lemma lem7140585 {_133668 : Type'} (x'' : type645 _133668) (f : _133668 -> real) (s : _133668 -> Prop) : (term489 _133668 x'' f s) = (term490 _133668 x'' f s).
Proof. exact (fun_ext (fun b : real => @lem7140584 _133668 x'' f s b)). Qed.
Lemma lem7140586 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7140587 {_133668 : Type'} (x'' : type645 _133668) (f : _133668 -> real) (s : _133668 -> Prop) : (term491 _133668 x'' f s) = (term492 _133668 x'' f s).
Proof. exact (MK_COMB (@lem7140586) (@lem7140585 _133668 x'' f s)). Qed.
Lemma lem7140588 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) : (term493 _133668 x'' s) = (term494 _133668 x'' s).
Proof. exact (fun_ext (fun f : _133668 -> real => @lem7140587 _133668 x'' f s)). Qed.
Lemma lem7140589 {_133668 : Type'} : (@all (_133668 -> real)) = (@all (_133668 -> real)).
Proof. exact (eq_refl (@all (_133668 -> real))). Qed.
Lemma lem7140590 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) : (term269 _133668 x'' s) = (term495 _133668 x'' s).
Proof. exact (MK_COMB (@lem7140589 _133668) (@lem7140588 _133668 x'' s)). Qed.
Lemma lem7140591 {_133668 : Type'} (x'' : type645 _133668) : (term271 _133668 x'') = (term496 _133668 x'').
Proof. exact (fun_ext (fun s : _133668 -> Prop => @lem7140590 _133668 x'' s)). Qed.
Lemma lem7140592 {_133668 : Type'} : (@all (_133668 -> Prop)) = (@all (_133668 -> Prop)).
Proof. exact (eq_refl (@all (_133668 -> Prop))). Qed.
Lemma lem7140593 {_133668 : Type'} (x'' : type645 _133668) : (term273 _133668 x'') = (term497 _133668 x'').
Proof. exact (MK_COMB (@lem7140592 _133668) (@lem7140591 _133668 x'')). Qed.
Lemma lem7140594 {_133668 : Type'} (x'' : type645 _133668) (h1 : term273 _133668 x'') : term497 _133668 x''.
Proof. exact (EQ_MP (@lem7140593 _133668 x'') (@lem7139995 _133668 x'' h1)). Qed.
Lemma lem7140595 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7140596 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7140603 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7140604 {_133668 : Type'} (f : type646 _133668) (x : _133668 -> Prop) : (f x) = (@I ((_133668 -> Prop) -> (_133668 -> real) -> real) f x).
Proof. exact (@lem7140603 (_133668 -> Prop) (type717 _133668) f x). Qed.
Lemma lem7140605 {_133668 : Type'} (s : _133668 -> Prop) : (@sum _133668 s) = (@I ((_133668 -> Prop) -> (_133668 -> real) -> real) (@sum _133668) s).
Proof. exact (@lem7140604 _133668 (@sum _133668) s). Qed.
Lemma lem7140606 {_133668 : Type'} (f : _133668 -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7140607 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) : (@sum _133668 s f) = (@I ((_133668 -> Prop) -> (_133668 -> real) -> real) (@sum _133668) s f).
Proof. exact (MK_COMB (@lem7140605 _133668 s) (@lem7140606 _133668 f)). Qed.
Lemma lem7140609 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7140610 {_133668 : Type'} (f : type717 _133668) (x : _133668 -> real) : (f x) = (@I ((_133668 -> real) -> real) f x).
Proof. exact (@lem7140609 (_133668 -> real) real f x). Qed.
Lemma lem7140611 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) : (@I ((_133668 -> Prop) -> (_133668 -> real) -> real) (@sum _133668) s f) = (term421 _133668 s f).
Proof. exact (@lem7140610 _133668 (@I ((_133668 -> Prop) -> (_133668 -> real) -> real) (@sum _133668) s) f). Qed.
Lemma lem7140613 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) : (@sum _133668 s f) = (term421 _133668 s f).
Proof. exact (TRANS (@lem7140607 _133668 s f) (@lem7140611 _133668 s f)). Qed.
Lemma lem7140614 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7140615 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7140620 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7140621 {_133668 : Type'} (f : type687 _133668) (x : _133668 -> Prop) : (f x) = (@I ((_133668 -> Prop) -> nat) f x).
Proof. exact (@lem7140620 (_133668 -> Prop) nat f x). Qed.
Lemma lem7140623 {_133668 : Type'} (s : _133668 -> Prop) : (@CARD _133668 s) = (@I ((_133668 -> Prop) -> nat) (@CARD _133668) s).
Proof. exact (@lem7140621 _133668 (@CARD _133668) s). Qed.
Lemma lem7140624 {_133668 : Type'} (s : _133668 -> Prop) : (term422 _133668 s) = (term423 _133668 s).
Proof. exact (MK_COMB (@lem7140615) (@lem7140623 _133668 s)). Qed.
Lemma lem7140626 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7140627 (f : nat -> real) (x : nat) : (f x) = (@I (nat -> real) f x).
Proof. exact (@lem7140626 nat real f x). Qed.
Lemma lem7140628 {_133668 : Type'} (s : _133668 -> Prop) : (term423 _133668 s) = (term424 _133668 s).
Proof. exact (@lem7140627 real_of_num (@I ((_133668 -> Prop) -> nat) (@CARD _133668) s)). Qed.
Lemma lem7140629 {_133668 : Type'} (s : _133668 -> Prop) : (term422 _133668 s) = (term424 _133668 s).
Proof. exact (TRANS (@lem7140624 _133668 s) (@lem7140628 _133668 s)). Qed.
Lemma lem7140630 (b : real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem7140631 {_133668 : Type'} (s : _133668 -> Prop) : (term425 _133668 s) = (term426 _133668 s).
Proof. exact (MK_COMB (@lem7140614) (@lem7140629 _133668 s)). Qed.
Lemma lem7140632 {_133668 : Type'} (s : _133668 -> Prop) (b : real) : (term427 _133668 s b) = (term428 _133668 s b).
Proof. exact (MK_COMB (@lem7140631 _133668 s) (@lem7140630 b)). Qed.
Lemma lem7140634 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7140635 (f : type1627) (x : real) : (f x) = (@I (real -> real -> real) f x).
Proof. exact (@lem7140634 real (real -> real) f x). Qed.
Lemma lem7140636 {_133668 : Type'} (s : _133668 -> Prop) : (term426 _133668 s) = (term429 _133668 s).
Proof. exact (@lem7140635 real_mul (term424 _133668 s)). Qed.
Lemma lem7140637 (b : real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem7140638 {_133668 : Type'} (s : _133668 -> Prop) (b : real) : (term428 _133668 s b) = (term430 _133668 s b).
Proof. exact (MK_COMB (@lem7140636 _133668 s) (@lem7140637 b)). Qed.
Lemma lem7140640 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7140641 (f : real -> real) (x : real) : (f x) = (@I (real -> real) f x).
Proof. exact (@lem7140640 real real f x). Qed.
Lemma lem7140642 {_133668 : Type'} (s : _133668 -> Prop) (b : real) : (term430 _133668 s b) = (term431 _133668 s b).
Proof. exact (@lem7140641 (term429 _133668 s) b). Qed.
Lemma lem7140643 {_133668 : Type'} (s : _133668 -> Prop) (b : real) : (term428 _133668 s b) = (term431 _133668 s b).
Proof. exact (TRANS (@lem7140638 _133668 s b) (@lem7140642 _133668 s b)). Qed.
Lemma lem7140644 {_133668 : Type'} (s : _133668 -> Prop) (b : real) : (term427 _133668 s b) = (term431 _133668 s b).
Proof. exact (TRANS (@lem7140632 _133668 s b) (@lem7140643 _133668 s b)). Qed.
Lemma lem7140645 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) : (term432 _133668 s f) = (term433 _133668 s f).
Proof. exact (MK_COMB (@lem7140596) (@lem7140613 _133668 s f)). Qed.
Lemma lem7140646 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term39 _133668 f s b) = (term434 _133668 f s b).
Proof. exact (MK_COMB (@lem7140645 _133668 s f) (@lem7140644 _133668 s b)). Qed.
Lemma lem7140648 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7140649 (f : type1626) (x : real) : (f x) = (@I (real -> real -> Prop) f x).
Proof. exact (@lem7140648 real (real -> Prop) f x). Qed.
Lemma lem7140650 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) : (term433 _133668 s f) = (term435 _133668 s f).
Proof. exact (@lem7140649 real_lt (term421 _133668 s f)). Qed.
Lemma lem7140651 {_133668 : Type'} (s : _133668 -> Prop) (b : real) : (term431 _133668 s b) = (term431 _133668 s b).
Proof. exact (eq_refl (term431 _133668 s b)). Qed.
Lemma lem7140652 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term434 _133668 f s b) = (term436 _133668 f s b).
Proof. exact (MK_COMB (@lem7140650 _133668 s f) (@lem7140651 _133668 s b)). Qed.
Lemma lem7140654 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7140655 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem7140654 real Prop f x). Qed.
Lemma lem7140656 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term436 _133668 f s b) = (term437 _133668 f s b).
Proof. exact (@lem7140655 (term435 _133668 s f) (term431 _133668 s b)). Qed.
Lemma lem7140657 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term434 _133668 f s b) = (term437 _133668 f s b).
Proof. exact (TRANS (@lem7140652 _133668 f s b) (@lem7140656 _133668 f s b)). Qed.
Lemma lem7140658 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term39 _133668 f s b) = (term437 _133668 f s b).
Proof. exact (TRANS (@lem7140646 _133668 f s b) (@lem7140657 _133668 f s b)). Qed.
Lemma lem7140659 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term76 _133668 f s b) = (term498 _133668 f s b).
Proof. exact (MK_COMB (@lem7140595) (@lem7140658 _133668 f s b)). Qed.
Lemma lem7140660 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7140665 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7140667 {_133668 : Type'} (f : _133668 -> real) (x : _133668) : (f x) = (@I (_133668 -> real) f x).
Proof. exact (@lem7140665 _133668 real f x). Qed.
Lemma lem7140668 (b : real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem7140669 {_133668 : Type'} (f : _133668 -> real) (x : _133668) : (term438 _133668 f x) = (term439 _133668 f x).
Proof. exact (MK_COMB (@lem7140660) (@lem7140667 _133668 f x)). Qed.
Lemma lem7140670 {_133668 : Type'} (f : _133668 -> real) (x : _133668) (b : real) : (term71 _133668 f x b) = (term440 _133668 f x b).
Proof. exact (MK_COMB (@lem7140669 _133668 f x) (@lem7140668 b)). Qed.
Lemma lem7140672 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7140673 (f : type1626) (x : real) : (f x) = (@I (real -> real -> Prop) f x).
Proof. exact (@lem7140672 real (real -> Prop) f x). Qed.
Lemma lem7140674 {_133668 : Type'} (f : _133668 -> real) (x : _133668) : (term439 _133668 f x) = (term441 _133668 f x).
Proof. exact (@lem7140673 real_lt (@I (_133668 -> real) f x)). Qed.
Lemma lem7140675 (b : real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem7140676 {_133668 : Type'} (f : _133668 -> real) (x : _133668) (b : real) : (term440 _133668 f x b) = (term442 _133668 f x b).
Proof. exact (MK_COMB (@lem7140674 _133668 f x) (@lem7140675 b)). Qed.
Lemma lem7140678 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7140679 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem7140678 real Prop f x). Qed.
Lemma lem7140680 {_133668 : Type'} (f : _133668 -> real) (x : _133668) (b : real) : (term442 _133668 f x b) = (term443 _133668 f x b).
Proof. exact (@lem7140679 (term441 _133668 f x) b). Qed.
Lemma lem7140681 {_133668 : Type'} (f : _133668 -> real) (x : _133668) (b : real) : (term440 _133668 f x b) = (term443 _133668 f x b).
Proof. exact (TRANS (@lem7140676 _133668 f x b) (@lem7140680 _133668 f x b)). Qed.
Lemma lem7140682 {_133668 : Type'} (f : _133668 -> real) (x : _133668) (b : real) : (term71 _133668 f x b) = (term443 _133668 f x b).
Proof. exact (TRANS (@lem7140670 _133668 f x b) (@lem7140681 _133668 f x b)). Qed.
Lemma lem7140683 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7140690 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7140691 {_133668 : Type'} (f : type1364 _133668) (x : _133668) : (f x) = (@I (_133668 -> (_133668 -> Prop) -> Prop) f x).
Proof. exact (@lem7140690 _133668 (type686 _133668) f x). Qed.
Lemma lem7140692 {_133668 : Type'} (x : _133668) : (@IN _133668 x) = (@I (_133668 -> (_133668 -> Prop) -> Prop) (@IN _133668) x).
Proof. exact (@lem7140691 _133668 (@IN _133668) x). Qed.
Lemma lem7140693 {_133668 : Type'} (s : _133668 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7140694 {_133668 : Type'} (x : _133668) (s : _133668 -> Prop) : (@IN _133668 x s) = (@I (_133668 -> (_133668 -> Prop) -> Prop) (@IN _133668) x s).
Proof. exact (MK_COMB (@lem7140692 _133668 x) (@lem7140693 _133668 s)). Qed.
Lemma lem7140696 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7140697 {_133668 : Type'} (f : type686 _133668) (x : _133668 -> Prop) : (f x) = (@I ((_133668 -> Prop) -> Prop) f x).
Proof. exact (@lem7140696 (_133668 -> Prop) Prop f x). Qed.
Lemma lem7140698 {_133668 : Type'} (x : _133668) (s : _133668 -> Prop) : (@I (_133668 -> (_133668 -> Prop) -> Prop) (@IN _133668) x s) = (term399 _133668 x s).
Proof. exact (@lem7140697 _133668 (@I (_133668 -> (_133668 -> Prop) -> Prop) (@IN _133668) x) s). Qed.
Lemma lem7140700 {_133668 : Type'} (x : _133668) (s : _133668 -> Prop) : (@IN _133668 x s) = (term399 _133668 x s).
Proof. exact (TRANS (@lem7140694 _133668 x s) (@lem7140698 _133668 x s)). Qed.
Lemma lem7140701 {_133668 : Type'} (x : _133668) (s : _133668 -> Prop) : (term286 _133668 x s) = (term400 _133668 x s).
Proof. exact (MK_COMB (@lem7140683) (@lem7140700 _133668 x s)). Qed.
Lemma lem7140702 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7140703 {_133668 : Type'} (x : _133668) (s : _133668 -> Prop) : (term446 _133668 x s) = (term447 _133668 x s).
Proof. exact (MK_COMB (@lem7140702) (@lem7140701 _133668 x s)). Qed.
Lemma lem7140704 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (x : _133668) (b : real) : (term70 _133668 s f x b) = (term499 _133668 s f x b).
Proof. exact (MK_COMB (@lem7140703 _133668 x s) (@lem7140682 _133668 f x b)). Qed.
Lemma lem7140705 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term72 _133668 s f b) = (term500 _133668 s f b).
Proof. exact (fun_ext (fun x : _133668 => @lem7140704 _133668 s f x b)). Qed.
Lemma lem7140706 {_133668 : Type'} : (@all _133668) = (@all _133668).
Proof. exact (eq_refl (@all _133668)). Qed.
Lemma lem7140707 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term73 _133668 s f b) = (term501 _133668 s f b).
Proof. exact (MK_COMB (@lem7140706 _133668) (@lem7140705 _133668 s f b)). Qed.
Lemma lem7140716 {_133668 : Type'} (s : _133668 -> Prop) : (term60 _133668 s) = (term60 _133668 s).
Proof. exact (eq_refl (term60 _133668 s)). Qed.
Lemma lem7140717 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term74 _133668 s f b) = (term502 _133668 s f b).
Proof. exact (MK_COMB (@lem7140716 _133668 s) (@lem7140707 _133668 s f b)). Qed.
Lemma lem7140722 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7140723 {_133668 : Type'} (f : type686 _133668) (x : _133668 -> Prop) : (f x) = (@I ((_133668 -> Prop) -> Prop) f x).
Proof. exact (@lem7140722 (_133668 -> Prop) Prop f x). Qed.
Lemma lem7140725 {_133668 : Type'} (s : _133668 -> Prop) : (@FINITE _133668 s) = (@I ((_133668 -> Prop) -> Prop) (@FINITE _133668) s).
Proof. exact (@lem7140723 _133668 (@FINITE _133668) s). Qed.
Lemma lem7140726 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7140727 {_133668 : Type'} (s : _133668 -> Prop) : (term48 _133668 s) = (term503 _133668 s).
Proof. exact (MK_COMB (@lem7140726) (@lem7140725 _133668 s)). Qed.
Lemma lem7140728 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term75 _133668 s f b) = (term504 _133668 s f b).
Proof. exact (MK_COMB (@lem7140727 _133668 s) (@lem7140717 _133668 s f b)). Qed.
Lemma lem7140729 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7140730 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term78 _133668 s f b) = (term505 _133668 s f b).
Proof. exact (MK_COMB (@lem7140729) (@lem7140728 _133668 s f b)). Qed.
Lemma lem7140731 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term80 _133668 f s b) = (term506 _133668 f s b).
Proof. exact (MK_COMB (@lem7140730 _133668 s f b) (@lem7140659 _133668 f s b)). Qed.
Lemma lem7140732 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) (h1 : term80 _133668 f s b) : term506 _133668 f s b.
Proof. exact (EQ_MP (@lem7140731 _133668 f s b) (@lem7139998 _133668 f s b h1)). Qed.
Lemma lem7140734 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) (h1 : term80 _133668 f s b) : term504 _133668 s f b.
Proof. exact (proj1 (@lem7140732 _133668 f s b h1)). Qed.
Lemma lem7140735 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) (h1 : term80 _133668 f s b) : term502 _133668 s f b.
Proof. exact (proj2 (@lem7140734 _133668 f s b h1)). Qed.
Lemma lem7140737 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) (h1 : term80 _133668 f s b) : term501 _133668 s f b.
Proof. exact (proj2 (@lem7140735 _133668 f s b h1)). Qed.
Lemma lem7140740 {_133668 : Type'} (x : type684 _133668) (h1 : term384 _133668 x) : term418 _133668 x.
Proof. exact (proj1 (@lem7140118 _133668 x h1)). Qed.
Lemma lem7140748 (x : real) (y : real) : (term394 x y) = (term394 x y).
Proof. exact (eq_refl (term394 x y)). Qed.
Lemma lem7140749 (x : real) : (term395 x) = (term395 x).
Proof. exact (fun_ext (fun y : real => @lem7140748 x y)). Qed.
Lemma lem7140750 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7140751 (x : real) : (term396 x) = (term396 x).
Proof. exact (MK_COMB (@lem7140750) (@lem7140749 x)). Qed.
Lemma lem7140752 : term397 = term397.
Proof. exact (fun_ext (fun x : real => @lem7140751 x)). Qed.
Lemma lem7140753 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7140755 : term398 = term398.
Proof. exact (MK_COMB (@lem7140753) (@lem7140752)). Qed.
Lemma lem7140756 (h1 : term38) : term398.
Proof. exact (EQ_MP (@lem7140755) (@lem7140044 h1)). Qed.
Lemma lem7140900 {A : Type'} (P : Prop) (Q : A -> Prop) : (term507 A P Q) = (term508 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem7140901 {_133668 : Type'} (P : Prop) (Q : _133668 -> Prop) : (term507 _133668 P Q) = (term508 _133668 P Q).
Proof. exact (@lem7140900 _133668 P Q). Qed.
Lemma lem7140902 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term509 _133668 x'' s f b) = (term510 _133668 x'' s f b).
Proof. exact (@lem7140901 _133668 (term476 _133668 x'' s f b) (term449 _133668 s f b)). Qed.
Lemma lem7140903 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (x : _133668) (b : real) : (term511 _133668 s f b x) = (term448 _133668 s f x b).
Proof. exact (eq_refl (term511 _133668 s f b x)). Qed.
Lemma lem7140904 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term512 _133668 s f b) = (term449 _133668 s f b).
Proof. exact (fun_ext (fun x : _133668 => @lem7140903 _133668 s f x b)). Qed.
Lemma lem7140905 {_133668 : Type'} : (@all _133668) = (@all _133668).
Proof. exact (eq_refl (@all _133668)). Qed.
Lemma lem7140906 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term513 _133668 s f b) = (term450 _133668 s f b).
Proof. exact (MK_COMB (@lem7140905 _133668) (@lem7140904 _133668 s f b)). Qed.
Lemma lem7140907 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term478 _133668 x'' s f b) = (term478 _133668 x'' s f b).
Proof. exact (eq_refl (term478 _133668 x'' s f b)). Qed.
Lemma lem7140908 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term509 _133668 x'' s f b) = (term480 _133668 x'' s f b).
Proof. exact (MK_COMB (@lem7140907 _133668 x'' s f b) (@lem7140906 _133668 s f b)). Qed.
Lemma lem7140909 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7140910 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term514 _133668 x'' s f b) = (term515 _133668 x'' s f b).
Proof. exact (MK_COMB (@lem7140909) (@lem7140908 _133668 x'' s f b)). Qed.
Lemma lem7140911 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (x : _133668) (b : real) : (term511 _133668 s f b x) = (term448 _133668 s f x b).
Proof. exact (eq_refl (term511 _133668 s f b x)). Qed.
Lemma lem7140912 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term478 _133668 x'' s f b) = (term478 _133668 x'' s f b).
Proof. exact (eq_refl (term478 _133668 x'' s f b)). Qed.
Lemma lem7140913 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) (f : _133668 -> real) (x : _133668) (b : real) : (term516 _133668 x'' s f b x) = (term517 _133668 x'' s f x b).
Proof. exact (MK_COMB (@lem7140912 _133668 x'' s f b) (@lem7140911 _133668 s f x b)). Qed.
Lemma lem7140914 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term518 _133668 x'' s f b) = (term519 _133668 x'' s f b).
Proof. exact (fun_ext (fun x : _133668 => @lem7140913 _133668 x'' s f x b)). Qed.
Lemma lem7140915 {_133668 : Type'} : (@all _133668) = (@all _133668).
Proof. exact (eq_refl (@all _133668)). Qed.
Lemma lem7140916 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term510 _133668 x'' s f b) = (term520 _133668 x'' s f b).
Proof. exact (MK_COMB (@lem7140915 _133668) (@lem7140914 _133668 x'' s f b)). Qed.
Lemma lem7140917 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : ((term509 _133668 x'' s f b) = (term510 _133668 x'' s f b)) = ((term480 _133668 x'' s f b) = (term520 _133668 x'' s f b)).
Proof. exact (MK_COMB (@lem7140910 _133668 x'' s f b) (@lem7140916 _133668 x'' s f b)). Qed.
Lemma lem7140918 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term480 _133668 x'' s f b) = (term520 _133668 x'' s f b).
Proof. exact (EQ_MP (@lem7140917 _133668 x'' s f b) (@lem7140902 _133668 x'' s f b)). Qed.
Lemma lem7140919 {_133668 : Type'} (s : _133668 -> Prop) : (term482 _133668 s) = (term482 _133668 s).
Proof. exact (eq_refl (term482 _133668 s)). Qed.
Lemma lem7140920 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term484 _133668 x'' s f b) = (term521 _133668 x'' s f b).
Proof. exact (MK_COMB (@lem7140919 _133668 s) (@lem7140918 _133668 x'' s f b)). Qed.
Lemma lem7140922 {A : Type'} (P : Prop) (Q : A -> Prop) : (term507 A P Q) = (term508 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem7140923 {_133668 : Type'} (P : Prop) (Q : _133668 -> Prop) : (term507 _133668 P Q) = (term508 _133668 P Q).
Proof. exact (@lem7140922 _133668 P Q). Qed.
Lemma lem7140924 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term522 _133668 x'' s f b) = (term523 _133668 x'' s f b).
Proof. exact (@lem7140923 _133668 (term481 _133668 s) (term519 _133668 x'' s f b)). Qed.
Lemma lem7140925 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) (f : _133668 -> real) (x : _133668) (b : real) : (term524 _133668 x'' s f b x) = (term517 _133668 x'' s f x b).
Proof. exact (eq_refl (term524 _133668 x'' s f b x)). Qed.
Lemma lem7140926 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term525 _133668 x'' s f b) = (term519 _133668 x'' s f b).
Proof. exact (fun_ext (fun x : _133668 => @lem7140925 _133668 x'' s f x b)). Qed.
Lemma lem7140927 {_133668 : Type'} : (@all _133668) = (@all _133668).
Proof. exact (eq_refl (@all _133668)). Qed.
Lemma lem7140928 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term526 _133668 x'' s f b) = (term520 _133668 x'' s f b).
Proof. exact (MK_COMB (@lem7140927 _133668) (@lem7140926 _133668 x'' s f b)). Qed.
Lemma lem7140929 {_133668 : Type'} (s : _133668 -> Prop) : (term482 _133668 s) = (term482 _133668 s).
Proof. exact (eq_refl (term482 _133668 s)). Qed.
Lemma lem7140930 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term522 _133668 x'' s f b) = (term521 _133668 x'' s f b).
Proof. exact (MK_COMB (@lem7140929 _133668 s) (@lem7140928 _133668 x'' s f b)). Qed.
Lemma lem7140931 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7140932 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term527 _133668 x'' s f b) = (term528 _133668 x'' s f b).
Proof. exact (MK_COMB (@lem7140931) (@lem7140930 _133668 x'' s f b)). Qed.
Lemma lem7140933 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) (f : _133668 -> real) (x : _133668) (b : real) : (term524 _133668 x'' s f b x) = (term517 _133668 x'' s f x b).
Proof. exact (eq_refl (term524 _133668 x'' s f b x)). Qed.
Lemma lem7140934 {_133668 : Type'} (s : _133668 -> Prop) : (term482 _133668 s) = (term482 _133668 s).
Proof. exact (eq_refl (term482 _133668 s)). Qed.
Lemma lem7140935 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) (f : _133668 -> real) (x : _133668) (b : real) : (term529 _133668 x'' s f b x) = (term530 _133668 x'' s f x b).
Proof. exact (MK_COMB (@lem7140934 _133668 s) (@lem7140933 _133668 x'' s f x b)). Qed.
Lemma lem7140936 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term531 _133668 x'' s f b) = (term532 _133668 x'' s f b).
Proof. exact (fun_ext (fun x : _133668 => @lem7140935 _133668 x'' s f x b)). Qed.
Lemma lem7140937 {_133668 : Type'} : (@all _133668) = (@all _133668).
Proof. exact (eq_refl (@all _133668)). Qed.
Lemma lem7140938 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term523 _133668 x'' s f b) = (term533 _133668 x'' s f b).
Proof. exact (MK_COMB (@lem7140937 _133668) (@lem7140936 _133668 x'' s f b)). Qed.
Lemma lem7140939 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : ((term522 _133668 x'' s f b) = (term523 _133668 x'' s f b)) = ((term521 _133668 x'' s f b) = (term533 _133668 x'' s f b)).
Proof. exact (MK_COMB (@lem7140932 _133668 x'' s f b) (@lem7140938 _133668 x'' s f b)). Qed.
Lemma lem7140940 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term521 _133668 x'' s f b) = (term533 _133668 x'' s f b).
Proof. exact (EQ_MP (@lem7140939 _133668 x'' s f b) (@lem7140924 _133668 x'' s f b)). Qed.
Lemma lem7140941 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term484 _133668 x'' s f b) = (term533 _133668 x'' s f b).
Proof. exact (TRANS (@lem7140920 _133668 x'' s f b) (@lem7140940 _133668 x'' s f b)). Qed.
Lemma lem7140942 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7140943 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term486 _133668 x'' s f b) = (term534 _133668 x'' s f b).
Proof. exact (MK_COMB (@lem7140942) (@lem7140941 _133668 x'' s f b)). Qed.
Lemma lem7140944 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term437 _133668 f s b) = (term437 _133668 f s b).
Proof. exact (eq_refl (term437 _133668 f s b)). Qed.
Lemma lem7140945 {_133668 : Type'} (x'' : type645 _133668) (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term488 _133668 x'' f s b) = (term535 _133668 x'' f s b).
Proof. exact (MK_COMB (@lem7140943 _133668 x'' s f b) (@lem7140944 _133668 f s b)). Qed.
Lemma lem7140947 {A : Type'} (P : A -> Prop) (Q : Prop) : (term536 A P Q) = (term537 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem7140948 {_133668 : Type'} (P : _133668 -> Prop) (Q : Prop) : (term536 _133668 P Q) = (term537 _133668 P Q).
Proof. exact (@lem7140947 _133668 P Q). Qed.
Lemma lem7140949 {_133668 : Type'} (x'' : type645 _133668) (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term538 _133668 x'' f s b) = (term539 _133668 x'' f s b).
Proof. exact (@lem7140948 _133668 (term532 _133668 x'' s f b) (term437 _133668 f s b)). Qed.
Lemma lem7140950 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) (f : _133668 -> real) (x : _133668) (b : real) : (term540 _133668 x'' s f b x) = (term530 _133668 x'' s f x b).
Proof. exact (eq_refl (term540 _133668 x'' s f b x)). Qed.
Lemma lem7140951 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term541 _133668 x'' s f b) = (term532 _133668 x'' s f b).
Proof. exact (fun_ext (fun x : _133668 => @lem7140950 _133668 x'' s f x b)). Qed.
Lemma lem7140952 {_133668 : Type'} : (@all _133668) = (@all _133668).
Proof. exact (eq_refl (@all _133668)). Qed.
Lemma lem7140953 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term542 _133668 x'' s f b) = (term533 _133668 x'' s f b).
Proof. exact (MK_COMB (@lem7140952 _133668) (@lem7140951 _133668 x'' s f b)). Qed.
Lemma lem7140954 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7140955 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term543 _133668 x'' s f b) = (term534 _133668 x'' s f b).
Proof. exact (MK_COMB (@lem7140954) (@lem7140953 _133668 x'' s f b)). Qed.
Lemma lem7140956 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term437 _133668 f s b) = (term437 _133668 f s b).
Proof. exact (eq_refl (term437 _133668 f s b)). Qed.
Lemma lem7140957 {_133668 : Type'} (x'' : type645 _133668) (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term538 _133668 x'' f s b) = (term535 _133668 x'' f s b).
Proof. exact (MK_COMB (@lem7140955 _133668 x'' s f b) (@lem7140956 _133668 f s b)). Qed.
Lemma lem7140958 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7140959 {_133668 : Type'} (x'' : type645 _133668) (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term544 _133668 x'' f s b) = (term545 _133668 x'' f s b).
Proof. exact (MK_COMB (@lem7140958) (@lem7140957 _133668 x'' f s b)). Qed.
Lemma lem7140960 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) (f : _133668 -> real) (x : _133668) (b : real) : (term540 _133668 x'' s f b x) = (term530 _133668 x'' s f x b).
Proof. exact (eq_refl (term540 _133668 x'' s f b x)). Qed.
Lemma lem7140961 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7140962 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) (f : _133668 -> real) (x : _133668) (b : real) : (term546 _133668 x'' s f b x) = (term547 _133668 x'' s f x b).
Proof. exact (MK_COMB (@lem7140961) (@lem7140960 _133668 x'' s f x b)). Qed.
Lemma lem7140963 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term437 _133668 f s b) = (term437 _133668 f s b).
Proof. exact (eq_refl (term437 _133668 f s b)). Qed.
Lemma lem7140964 {_133668 : Type'} (x'' : type645 _133668) (x : _133668) (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term548 _133668 x'' x f s b) = (term549 _133668 x'' x f s b).
Proof. exact (MK_COMB (@lem7140962 _133668 x'' s f x b) (@lem7140963 _133668 f s b)). Qed.
Lemma lem7140965 {_133668 : Type'} (x'' : type645 _133668) (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term550 _133668 x'' f s b) = (term551 _133668 x'' f s b).
Proof. exact (fun_ext (fun x : _133668 => @lem7140964 _133668 x'' x f s b)). Qed.
Lemma lem7140966 {_133668 : Type'} : (@all _133668) = (@all _133668).
Proof. exact (eq_refl (@all _133668)). Qed.
Lemma lem7140967 {_133668 : Type'} (x'' : type645 _133668) (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term539 _133668 x'' f s b) = (term552 _133668 x'' f s b).
Proof. exact (MK_COMB (@lem7140966 _133668) (@lem7140965 _133668 x'' f s b)). Qed.
Lemma lem7140968 {_133668 : Type'} (x'' : type645 _133668) (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : ((term538 _133668 x'' f s b) = (term539 _133668 x'' f s b)) = ((term535 _133668 x'' f s b) = (term552 _133668 x'' f s b)).
Proof. exact (MK_COMB (@lem7140959 _133668 x'' f s b) (@lem7140967 _133668 x'' f s b)). Qed.
Lemma lem7140969 {_133668 : Type'} (x'' : type645 _133668) (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term535 _133668 x'' f s b) = (term552 _133668 x'' f s b).
Proof. exact (EQ_MP (@lem7140968 _133668 x'' f s b) (@lem7140949 _133668 x'' f s b)). Qed.
Lemma lem7140970 {_133668 : Type'} (x'' : type645 _133668) (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term488 _133668 x'' f s b) = (term552 _133668 x'' f s b).
Proof. exact (TRANS (@lem7140945 _133668 x'' f s b) (@lem7140969 _133668 x'' f s b)). Qed.
Lemma lem7140971 {_133668 : Type'} (x'' : type645 _133668) (f : _133668 -> real) (s : _133668 -> Prop) : (term490 _133668 x'' f s) = (term553 _133668 x'' f s).
Proof. exact (fun_ext (fun b : real => @lem7140970 _133668 x'' f s b)). Qed.
Lemma lem7140972 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7140973 {_133668 : Type'} (x'' : type645 _133668) (f : _133668 -> real) (s : _133668 -> Prop) : (term492 _133668 x'' f s) = (term554 _133668 x'' f s).
Proof. exact (MK_COMB (@lem7140972) (@lem7140971 _133668 x'' f s)). Qed.
Lemma lem7140974 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) : (term494 _133668 x'' s) = (term555 _133668 x'' s).
Proof. exact (fun_ext (fun f : _133668 -> real => @lem7140973 _133668 x'' f s)). Qed.
Lemma lem7140975 {_133668 : Type'} : (@all (_133668 -> real)) = (@all (_133668 -> real)).
Proof. exact (eq_refl (@all (_133668 -> real))). Qed.
Lemma lem7140976 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) : (term495 _133668 x'' s) = (term556 _133668 x'' s).
Proof. exact (MK_COMB (@lem7140975 _133668) (@lem7140974 _133668 x'' s)). Qed.
Lemma lem7140977 {_133668 : Type'} (x'' : type645 _133668) : (term496 _133668 x'') = (term557 _133668 x'').
Proof. exact (fun_ext (fun s : _133668 -> Prop => @lem7140976 _133668 x'' s)). Qed.
Lemma lem7140978 {_133668 : Type'} : (@all (_133668 -> Prop)) = (@all (_133668 -> Prop)).
Proof. exact (eq_refl (@all (_133668 -> Prop))). Qed.
Lemma lem7140979 {_133668 : Type'} (x'' : type645 _133668) : (term497 _133668 x'') = (term558 _133668 x'').
Proof. exact (MK_COMB (@lem7140978 _133668) (@lem7140977 _133668 x'')). Qed.
Lemma lem7140980 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term437 _133668 f s b) = (term437 _133668 f s b).
Proof. exact (eq_refl (term437 _133668 f s b)). Qed.
Lemma lem7141003 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) (f : _133668 -> real) (x : _133668) (b : real) : (term517 _133668 x'' s f x b) = (term559 _133668 x'' s f x b).
Proof. exact (@lem19699 (term472 _133668 x'' f b s) (term465 _133668 x'' s f b) (term448 _133668 s f x b)). Qed.
Lemma lem7141006 {_133668 : Type'} (s : _133668 -> Prop) : (term482 _133668 s) = (term482 _133668 s).
Proof. exact (eq_refl (term482 _133668 s)). Qed.
Lemma lem7141007 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) (f : _133668 -> real) (x : _133668) (b : real) : (term530 _133668 x'' s f x b) = (term560 _133668 x'' s f x b).
Proof. exact (MK_COMB (@lem7141006 _133668 s) (@lem7141003 _133668 x'' s f x b)). Qed.
Lemma lem7141014 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) (f : _133668 -> real) (x : _133668) (b : real) : (term560 _133668 x'' s f x b) = (term561 _133668 x'' s f x b).
Proof. exact (@lem19490 (term562 _133668 x'' s f x b) (term481 _133668 s) (term563 _133668 x'' s f x b)). Qed.
Lemma lem7141015 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) (f : _133668 -> real) (x : _133668) (b : real) : (term530 _133668 x'' s f x b) = (term561 _133668 x'' s f x b).
Proof. exact (TRANS (@lem7141007 _133668 x'' s f x b) (@lem7141014 _133668 x'' s f x b)). Qed.
Lemma lem7141016 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7141017 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) (f : _133668 -> real) (x : _133668) (b : real) : (term547 _133668 x'' s f x b) = (term564 _133668 x'' s f x b).
Proof. exact (MK_COMB (@lem7141016) (@lem7141015 _133668 x'' s f x b)). Qed.
Lemma lem7141018 {_133668 : Type'} (x'' : type645 _133668) (x : _133668) (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term549 _133668 x'' x f s b) = (term565 _133668 x'' x f s b).
Proof. exact (MK_COMB (@lem7141017 _133668 x'' s f x b) (@lem7140980 _133668 f s b)). Qed.
Lemma lem7141025 {_133668 : Type'} (x'' : type645 _133668) (x : _133668) (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term565 _133668 x'' x f s b) = (term566 _133668 x'' x f s b).
Proof. exact (@lem19699 (term567 _133668 x'' s f x b) (term568 _133668 x'' s f x b) (term437 _133668 f s b)). Qed.
Lemma lem7141026 {_133668 : Type'} (x'' : type645 _133668) (x : _133668) (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term549 _133668 x'' x f s b) = (term566 _133668 x'' x f s b).
Proof. exact (TRANS (@lem7141018 _133668 x'' x f s b) (@lem7141025 _133668 x'' x f s b)). Qed.
Lemma lem7141027 {_133668 : Type'} (x'' : type645 _133668) (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term551 _133668 x'' f s b) = (term569 _133668 x'' f s b).
Proof. exact (fun_ext (fun x : _133668 => @lem7141026 _133668 x'' x f s b)). Qed.
Lemma lem7141028 {_133668 : Type'} : (@all _133668) = (@all _133668).
Proof. exact (eq_refl (@all _133668)). Qed.
Lemma lem7141029 {_133668 : Type'} (x'' : type645 _133668) (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term552 _133668 x'' f s b) = (term570 _133668 x'' f s b).
Proof. exact (MK_COMB (@lem7141028 _133668) (@lem7141027 _133668 x'' f s b)). Qed.
Lemma lem7141030 {_133668 : Type'} (x'' : type645 _133668) (f : _133668 -> real) (s : _133668 -> Prop) : (term553 _133668 x'' f s) = (term571 _133668 x'' f s).
Proof. exact (fun_ext (fun b : real => @lem7141029 _133668 x'' f s b)). Qed.
Lemma lem7141031 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7141032 {_133668 : Type'} (x'' : type645 _133668) (f : _133668 -> real) (s : _133668 -> Prop) : (term554 _133668 x'' f s) = (term572 _133668 x'' f s).
Proof. exact (MK_COMB (@lem7141031) (@lem7141030 _133668 x'' f s)). Qed.
Lemma lem7141033 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) : (term555 _133668 x'' s) = (term573 _133668 x'' s).
Proof. exact (fun_ext (fun f : _133668 -> real => @lem7141032 _133668 x'' f s)). Qed.
Lemma lem7141034 {_133668 : Type'} : (@all (_133668 -> real)) = (@all (_133668 -> real)).
Proof. exact (eq_refl (@all (_133668 -> real))). Qed.
Lemma lem7141035 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) : (term556 _133668 x'' s) = (term574 _133668 x'' s).
Proof. exact (MK_COMB (@lem7141034 _133668) (@lem7141033 _133668 x'' s)). Qed.
Lemma lem7141036 {_133668 : Type'} (x'' : type645 _133668) : (term557 _133668 x'') = (term575 _133668 x'').
Proof. exact (fun_ext (fun s : _133668 -> Prop => @lem7141035 _133668 x'' s)). Qed.
Lemma lem7141037 {_133668 : Type'} : (@all (_133668 -> Prop)) = (@all (_133668 -> Prop)).
Proof. exact (eq_refl (@all (_133668 -> Prop))). Qed.
Lemma lem7141038 {_133668 : Type'} (x'' : type645 _133668) : (term558 _133668 x'') = (term576 _133668 x'').
Proof. exact (MK_COMB (@lem7141037 _133668) (@lem7141036 _133668 x'')). Qed.
Lemma lem7141039 {_133668 : Type'} (x'' : type645 _133668) : (term497 _133668 x'') = (term576 _133668 x'').
Proof. exact (TRANS (@lem7140979 _133668 x'') (@lem7141038 _133668 x'')). Qed.
Lemma lem7141040 {_133668 : Type'} (x'' : type645 _133668) (h1 : term273 _133668 x'') : term576 _133668 x''.
Proof. exact (EQ_MP (@lem7141039 _133668 x'') (@lem7140594 _133668 x'' h1)). Qed.
Lemma lem7141060 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (x : _133668) (b : real) : (term499 _133668 s f x b) = (term499 _133668 s f x b).
Proof. exact (eq_refl (term499 _133668 s f x b)). Qed.
Lemma lem7141061 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term500 _133668 s f b) = (term500 _133668 s f b).
Proof. exact (fun_ext (fun x : _133668 => @lem7141060 _133668 s f x b)). Qed.
Lemma lem7141062 {_133668 : Type'} : (@all _133668) = (@all _133668).
Proof. exact (eq_refl (@all _133668)). Qed.
Lemma lem7141064 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term501 _133668 s f b) = (term501 _133668 s f b).
Proof. exact (MK_COMB (@lem7141062 _133668) (@lem7141061 _133668 s f b)). Qed.
Lemma lem7141065 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) (h1 : term80 _133668 f s b) : term501 _133668 s f b.
Proof. exact (EQ_MP (@lem7141064 _133668 s f b) (@lem7140737 _133668 f s b h1)). Qed.
Lemma lem7141073 {_133668 : Type'} (x : type684 _133668) (s : _133668 -> Prop) : (term416 _133668 x s) = (term416 _133668 x s).
Proof. exact (eq_refl (term416 _133668 x s)). Qed.
Lemma lem7141074 {_133668 : Type'} (x : type684 _133668) : (term417 _133668 x) = (term417 _133668 x).
Proof. exact (fun_ext (fun s : _133668 -> Prop => @lem7141073 _133668 x s)). Qed.
Lemma lem7141075 {_133668 : Type'} : (@all (_133668 -> Prop)) = (@all (_133668 -> Prop)).
Proof. exact (eq_refl (@all (_133668 -> Prop))). Qed.
Lemma lem7141077 {_133668 : Type'} (x : type684 _133668) : (term418 _133668 x) = (term418 _133668 x).
Proof. exact (MK_COMB (@lem7141075 _133668) (@lem7141074 _133668 x)). Qed.
Lemma lem7141078 {_133668 : Type'} (x : type684 _133668) (h1 : term384 _133668 x) : term418 _133668 x.
Proof. exact (EQ_MP (@lem7141077 _133668 x) (@lem7140740 _133668 x h1)). Qed.
Lemma lem7141121 (_95336 : real) (h1 : term38) : term577 _95336.
Proof. exact (@lem7140756 h1 _95336). Qed.
Lemma lem7141122 (_95336 : real) : (term577 _95336) = (term396 _95336).
Proof. exact (eq_refl (term577 _95336)). Qed.
Lemma lem7141123 (_95336 : real) (h1 : term38) : term396 _95336.
Proof. exact (EQ_MP (@lem7141122 _95336) (@lem7141121 _95336 h1)). Qed.
Lemma lem7141124 (_95336 : real) (_95337 : real) (h1 : term38) : term578 _95336 _95337.
Proof. exact (@lem7141123 _95336 h1 _95337). Qed.
Lemma lem7141125 (_95336 : real) (_95337 : real) : (term578 _95336 _95337) = (term394 _95336 _95337).
Proof. exact (eq_refl (term578 _95336 _95337)). Qed.
Lemma lem7141139 {_133668 : Type'} (_95342 : _133668 -> Prop) (x'' : type645 _133668) (h1 : term273 _133668 x'') : term579 _133668 x'' _95342.
Proof. exact (@lem7141040 _133668 x'' h1 _95342). Qed.
Lemma lem7141140 {_133668 : Type'} (x'' : type645 _133668) (_95342 : _133668 -> Prop) : (term579 _133668 x'' _95342) = (term574 _133668 x'' _95342).
Proof. exact (eq_refl (term579 _133668 x'' _95342)). Qed.
Lemma lem7141141 {_133668 : Type'} (_95342 : _133668 -> Prop) (x'' : type645 _133668) (h1 : term273 _133668 x'') : term574 _133668 x'' _95342.
Proof. exact (EQ_MP (@lem7141140 _133668 x'' _95342) (@lem7141139 _133668 _95342 x'' h1)). Qed.
Lemma lem7141142 {_133668 : Type'} (_95342 : _133668 -> Prop) (_95343 : _133668 -> real) (x'' : type645 _133668) (h1 : term273 _133668 x'') : term580 _133668 x'' _95342 _95343.
Proof. exact (@lem7141141 _133668 _95342 x'' h1 _95343). Qed.
Lemma lem7141143 {_133668 : Type'} (x'' : type645 _133668) (_95343 : _133668 -> real) (_95342 : _133668 -> Prop) : (term580 _133668 x'' _95342 _95343) = (term572 _133668 x'' _95343 _95342).
Proof. exact (eq_refl (term580 _133668 x'' _95342 _95343)). Qed.
Lemma lem7141144 {_133668 : Type'} (_95343 : _133668 -> real) (_95342 : _133668 -> Prop) (x'' : type645 _133668) (h1 : term273 _133668 x'') : term572 _133668 x'' _95343 _95342.
Proof. exact (EQ_MP (@lem7141143 _133668 x'' _95343 _95342) (@lem7141142 _133668 _95342 _95343 x'' h1)). Qed.
Lemma lem7141145 {_133668 : Type'} (_95343 : _133668 -> real) (_95342 : _133668 -> Prop) (_95344 : real) (x'' : type645 _133668) (h1 : term273 _133668 x'') : term581 _133668 x'' _95343 _95342 _95344.
Proof. exact (@lem7141144 _133668 _95343 _95342 x'' h1 _95344). Qed.
Lemma lem7141146 {_133668 : Type'} (x'' : type645 _133668) (_95343 : _133668 -> real) (_95342 : _133668 -> Prop) (_95344 : real) : (term581 _133668 x'' _95343 _95342 _95344) = (term570 _133668 x'' _95343 _95342 _95344).
Proof. exact (eq_refl (term581 _133668 x'' _95343 _95342 _95344)). Qed.
Lemma lem7141147 {_133668 : Type'} (_95343 : _133668 -> real) (_95342 : _133668 -> Prop) (_95344 : real) (x'' : type645 _133668) (h1 : term273 _133668 x'') : term570 _133668 x'' _95343 _95342 _95344.
Proof. exact (EQ_MP (@lem7141146 _133668 x'' _95343 _95342 _95344) (@lem7141145 _133668 _95343 _95342 _95344 x'' h1)). Qed.
Lemma lem7141148 {_133668 : Type'} (_95343 : _133668 -> real) (_95342 : _133668 -> Prop) (_95344 : real) (_95345 : _133668) (x'' : type645 _133668) (h1 : term273 _133668 x'') : term582 _133668 x'' _95343 _95342 _95344 _95345.
Proof. exact (@lem7141147 _133668 _95343 _95342 _95344 x'' h1 _95345). Qed.
Lemma lem7141149 {_133668 : Type'} (x'' : type645 _133668) (_95345 : _133668) (_95343 : _133668 -> real) (_95342 : _133668 -> Prop) (_95344 : real) : (term582 _133668 x'' _95343 _95342 _95344 _95345) = (term566 _133668 x'' _95345 _95343 _95342 _95344).
Proof. exact (eq_refl (term582 _133668 x'' _95343 _95342 _95344 _95345)). Qed.
Lemma lem7141150 {_133668 : Type'} (_95345 : _133668) (_95343 : _133668 -> real) (_95342 : _133668 -> Prop) (_95344 : real) (x'' : type645 _133668) (h1 : term273 _133668 x'') : term566 _133668 x'' _95345 _95343 _95342 _95344.
Proof. exact (EQ_MP (@lem7141149 _133668 x'' _95345 _95343 _95342 _95344) (@lem7141148 _133668 _95343 _95342 _95344 _95345 x'' h1)). Qed.
Lemma lem7141151 {_133668 : Type'} (_95346 : _133668) (f : _133668 -> real) (s : _133668 -> Prop) (b : real) (h1 : term80 _133668 f s b) : term583 _133668 s f b _95346.
Proof. exact (@lem7141065 _133668 f s b h1 _95346). Qed.
Lemma lem7141152 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (_95346 : _133668) (b : real) : (term583 _133668 s f b _95346) = (term499 _133668 s f _95346 b).
Proof. exact (eq_refl (term583 _133668 s f b _95346)). Qed.
Lemma lem7141154 {_133668 : Type'} (_95347 : _133668 -> Prop) (x : type684 _133668) (h1 : term384 _133668 x) : term584 _133668 x _95347.
Proof. exact (@lem7141078 _133668 x h1 _95347). Qed.
Lemma lem7141155 {_133668 : Type'} (x : type684 _133668) (_95347 : _133668 -> Prop) : (term584 _133668 x _95347) = (term416 _133668 x _95347).
Proof. exact (eq_refl (term584 _133668 x _95347)). Qed.
Lemma lem7141163 {_133668 : Type'} (_95345 : _133668) (_95343 : _133668 -> real) (_95342 : _133668 -> Prop) (_95344 : real) (x'' : type645 _133668) (h1 : term273 _133668 x'') : term585 _133668 x'' _95345 _95343 _95342 _95344.
Proof. exact (proj2 (@lem7141150 _133668 _95345 _95343 _95342 _95344 x'' h1)). Qed.
Lemma lem7141164 {_133668 : Type'} (_95345 : _133668) (_95343 : _133668 -> real) (_95342 : _133668 -> Prop) (_95344 : real) (x'' : type645 _133668) (h1 : term273 _133668 x'') : term586 _133668 x'' _95345 _95343 _95342 _95344.
Proof. exact (proj1 (@lem7141150 _133668 _95345 _95343 _95342 _95344 x'' h1)). Qed.
Lemma lem7141172 (_95336 : real) (_95337 : real) (h1 : term38) : term394 _95336 _95337.
Proof. exact (EQ_MP (@lem7141125 _95336 _95337) (@lem7141124 _95336 _95337 h1)). Qed.
Lemma lem7141178 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) (h1 : term80 _133668 f s b) : term29 _133668 s.
Proof. exact (proj1 (@lem7140735 _133668 f s b h1)). Qed.
Lemma lem7141184 {_133668 : Type'} (_95346 : _133668) (f : _133668 -> real) (s : _133668 -> Prop) (b : real) (h1 : term80 _133668 f s b) : term499 _133668 s f _95346 b.
Proof. exact (EQ_MP (@lem7141152 _133668 s f _95346 b) (@lem7141151 _133668 _95346 f s b h1)). Qed.
Lemma lem7141190 {_133668 : Type'} (_95347 : _133668 -> Prop) (x : type684 _133668) (h1 : term384 _133668 x) : term416 _133668 x _95347.
Proof. exact (EQ_MP (@lem7141155 _133668 x _95347) (@lem7141154 _133668 _95347 x h1)). Qed.
Lemma lem7141200 {_133668 : Type'} (x'' : type645 _133668) (_95345 : _133668) (_95343 : _133668 -> real) (_95342 : _133668 -> Prop) (_95344 : real) : (term586 _133668 x'' _95345 _95343 _95342 _95344) = (term587 _133668 x'' _95345 _95343 _95342 _95344).
Proof. exact (@lem7138170 (term481 _133668 _95342) (term562 _133668 x'' _95342 _95343 _95345 _95344) (term437 _133668 _95343 _95342 _95344)). Qed.
Lemma lem7141201 {_133668 : Type'} (x'' : type645 _133668) (_95345 : _133668) (_95343 : _133668 -> real) (_95342 : _133668 -> Prop) (_95344 : real) : (term588 _133668 x'' _95345 _95343 _95342 _95344) = (term589 _133668 x'' _95345 _95343 _95342 _95344).
Proof. exact (@lem7138170 (term472 _133668 x'' _95343 _95344 _95342) (term448 _133668 _95342 _95343 _95345 _95344) (term437 _133668 _95343 _95342 _95344)). Qed.
Lemma lem7141208 {_133668 : Type'} (_95345 : _133668) (_95343 : _133668 -> real) (_95342 : _133668 -> Prop) (_95344 : real) : (term590 _133668 _95345 _95343 _95342 _95344) = (term591 _133668 _95345 _95343 _95342 _95344).
Proof. exact (@lem7138170 (term400 _133668 _95345 _95342) (term445 _133668 _95343 _95345 _95344) (term437 _133668 _95343 _95342 _95344)). Qed.
Lemma lem7141209 {_133668 : Type'} (x'' : type645 _133668) (_95343 : _133668 -> real) (_95344 : real) (_95342 : _133668 -> Prop) : (term592 _133668 x'' _95343 _95344 _95342) = (term592 _133668 x'' _95343 _95344 _95342).
Proof. exact (eq_refl (term592 _133668 x'' _95343 _95344 _95342)). Qed.
Lemma lem7141212 {_133668 : Type'} (x'' : type645 _133668) (_95345 : _133668) (_95343 : _133668 -> real) (_95342 : _133668 -> Prop) (_95344 : real) : (term589 _133668 x'' _95345 _95343 _95342 _95344) = (term593 _133668 x'' _95345 _95343 _95342 _95344).
Proof. exact (MK_COMB (@lem7141209 _133668 x'' _95343 _95344 _95342) (@lem7141208 _133668 _95345 _95343 _95342 _95344)). Qed.
Lemma lem7141213 {_133668 : Type'} (x'' : type645 _133668) (_95345 : _133668) (_95343 : _133668 -> real) (_95342 : _133668 -> Prop) (_95344 : real) : (term588 _133668 x'' _95345 _95343 _95342 _95344) = (term593 _133668 x'' _95345 _95343 _95342 _95344).
Proof. exact (TRANS (@lem7141201 _133668 x'' _95345 _95343 _95342 _95344) (@lem7141212 _133668 x'' _95345 _95343 _95342 _95344)). Qed.
Lemma lem7141214 {_133668 : Type'} (_95342 : _133668 -> Prop) : (term482 _133668 _95342) = (term482 _133668 _95342).
Proof. exact (eq_refl (term482 _133668 _95342)). Qed.
Lemma lem7141217 {_133668 : Type'} (x'' : type645 _133668) (_95345 : _133668) (_95343 : _133668 -> real) (_95342 : _133668 -> Prop) (_95344 : real) : (term587 _133668 x'' _95345 _95343 _95342 _95344) = (term594 _133668 x'' _95345 _95343 _95342 _95344).
Proof. exact (MK_COMB (@lem7141214 _133668 _95342) (@lem7141213 _133668 x'' _95345 _95343 _95342 _95344)). Qed.
Lemma lem7141219 {_133668 : Type'} (x'' : type645 _133668) (_95345 : _133668) (_95343 : _133668 -> real) (_95342 : _133668 -> Prop) (_95344 : real) : (term586 _133668 x'' _95345 _95343 _95342 _95344) = (term594 _133668 x'' _95345 _95343 _95342 _95344).
Proof. exact (TRANS (@lem7141200 _133668 x'' _95345 _95343 _95342 _95344) (@lem7141217 _133668 x'' _95345 _95343 _95342 _95344)). Qed.
Lemma lem7141220 {_133668 : Type'} (_95345 : _133668) (_95343 : _133668 -> real) (_95342 : _133668 -> Prop) (_95344 : real) (x'' : type645 _133668) (h1 : term273 _133668 x'') : term594 _133668 x'' _95345 _95343 _95342 _95344.
Proof. exact (EQ_MP (@lem7141219 _133668 x'' _95345 _95343 _95342 _95344) (@lem7141164 _133668 _95345 _95343 _95342 _95344 x'' h1)). Qed.
Lemma lem7141224 {_133668 : Type'} (x'' : type645 _133668) (_95345 : _133668) (_95343 : _133668 -> real) (_95342 : _133668 -> Prop) (_95344 : real) : (term585 _133668 x'' _95345 _95343 _95342 _95344) = (term595 _133668 x'' _95345 _95343 _95342 _95344).
Proof. exact (@lem7138170 (term481 _133668 _95342) (term563 _133668 x'' _95342 _95343 _95345 _95344) (term437 _133668 _95343 _95342 _95344)). Qed.
Lemma lem7141225 {_133668 : Type'} (x'' : type645 _133668) (_95345 : _133668) (_95343 : _133668 -> real) (_95342 : _133668 -> Prop) (_95344 : real) : (term596 _133668 x'' _95345 _95343 _95342 _95344) = (term597 _133668 x'' _95345 _95343 _95342 _95344).
Proof. exact (@lem7138170 (term465 _133668 x'' _95342 _95343 _95344) (term448 _133668 _95342 _95343 _95345 _95344) (term437 _133668 _95343 _95342 _95344)). Qed.
Lemma lem7141232 {_133668 : Type'} (_95345 : _133668) (_95343 : _133668 -> real) (_95342 : _133668 -> Prop) (_95344 : real) : (term590 _133668 _95345 _95343 _95342 _95344) = (term591 _133668 _95345 _95343 _95342 _95344).
Proof. exact (@lem7138170 (term400 _133668 _95345 _95342) (term445 _133668 _95343 _95345 _95344) (term437 _133668 _95343 _95342 _95344)). Qed.
Lemma lem7141233 {_133668 : Type'} (x'' : type645 _133668) (_95342 : _133668 -> Prop) (_95343 : _133668 -> real) (_95344 : real) : (term598 _133668 x'' _95342 _95343 _95344) = (term598 _133668 x'' _95342 _95343 _95344).
Proof. exact (eq_refl (term598 _133668 x'' _95342 _95343 _95344)). Qed.
Lemma lem7141236 {_133668 : Type'} (x'' : type645 _133668) (_95345 : _133668) (_95343 : _133668 -> real) (_95342 : _133668 -> Prop) (_95344 : real) : (term597 _133668 x'' _95345 _95343 _95342 _95344) = (term599 _133668 x'' _95345 _95343 _95342 _95344).
Proof. exact (MK_COMB (@lem7141233 _133668 x'' _95342 _95343 _95344) (@lem7141232 _133668 _95345 _95343 _95342 _95344)). Qed.
Lemma lem7141237 {_133668 : Type'} (x'' : type645 _133668) (_95345 : _133668) (_95343 : _133668 -> real) (_95342 : _133668 -> Prop) (_95344 : real) : (term596 _133668 x'' _95345 _95343 _95342 _95344) = (term599 _133668 x'' _95345 _95343 _95342 _95344).
Proof. exact (TRANS (@lem7141225 _133668 x'' _95345 _95343 _95342 _95344) (@lem7141236 _133668 x'' _95345 _95343 _95342 _95344)). Qed.
Lemma lem7141238 {_133668 : Type'} (_95342 : _133668 -> Prop) : (term482 _133668 _95342) = (term482 _133668 _95342).
Proof. exact (eq_refl (term482 _133668 _95342)). Qed.
Lemma lem7141241 {_133668 : Type'} (x'' : type645 _133668) (_95345 : _133668) (_95343 : _133668 -> real) (_95342 : _133668 -> Prop) (_95344 : real) : (term595 _133668 x'' _95345 _95343 _95342 _95344) = (term600 _133668 x'' _95345 _95343 _95342 _95344).
Proof. exact (MK_COMB (@lem7141238 _133668 _95342) (@lem7141237 _133668 x'' _95345 _95343 _95342 _95344)). Qed.
Lemma lem7141243 {_133668 : Type'} (x'' : type645 _133668) (_95345 : _133668) (_95343 : _133668 -> real) (_95342 : _133668 -> Prop) (_95344 : real) : (term585 _133668 x'' _95345 _95343 _95342 _95344) = (term600 _133668 x'' _95345 _95343 _95342 _95344).
Proof. exact (TRANS (@lem7141224 _133668 x'' _95345 _95343 _95342 _95344) (@lem7141241 _133668 x'' _95345 _95343 _95342 _95344)). Qed.
Lemma lem7141244 {_133668 : Type'} (_95345 : _133668) (_95343 : _133668 -> real) (_95342 : _133668 -> Prop) (_95344 : real) (x'' : type645 _133668) (h1 : term273 _133668 x'') : term600 _133668 x'' _95345 _95343 _95342 _95344.
Proof. exact (EQ_MP (@lem7141243 _133668 x'' _95345 _95343 _95342 _95344) (@lem7141163 _133668 _95345 _95343 _95342 _95344 x'' h1)). Qed.
Lemma lem7141726 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) (h1 : term80 _133668 f s b) : @I ((_133668 -> Prop) -> Prop) (@FINITE _133668) s.
Proof. exact (proj1 (@lem7140734 _133668 f s b h1)). Qed.
Lemma lem7141727 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) (h1 : term80 _133668 f s b) : term601 _133668 s.
Proof. exact (fun h0 : term481 _133668 s => @lem7141726 _133668 f s b h1). Qed.
Lemma lem7141729 (p : Prop) : (term602 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7141730 {_133668 : Type'} (s : _133668 -> Prop) : (term601 _133668 s) = (@I ((_133668 -> Prop) -> Prop) (@FINITE _133668) s).
Proof. exact (@lem7141729 (@I ((_133668 -> Prop) -> Prop) (@FINITE _133668) s)). Qed.
Lemma lem7141731 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) (h1 : term80 _133668 f s b) : @I ((_133668 -> Prop) -> Prop) (@FINITE _133668) s.
Proof. exact (EQ_MP (@lem7141730 _133668 s) (@lem7141727 _133668 f s b h1)). Qed.
Lemma lem7141733 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) (h1 : term80 _133668 f s b) : @I ((_133668 -> Prop) -> Prop) (@FINITE _133668) s.
Proof. exact (proj1 (@lem7140734 _133668 f s b h1)). Qed.
Lemma lem7141734 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) (h1 : term80 _133668 f s b) : term601 _133668 s.
Proof. exact (fun h0 : term481 _133668 s => @lem7141733 _133668 f s b h1). Qed.
Lemma lem7141736 (p : Prop) : (term602 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7141737 {_133668 : Type'} (s : _133668 -> Prop) : (term601 _133668 s) = (@I ((_133668 -> Prop) -> Prop) (@FINITE _133668) s).
Proof. exact (@lem7141736 (@I ((_133668 -> Prop) -> Prop) (@FINITE _133668) s)). Qed.
Lemma lem7141738 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) (h1 : term80 _133668 f s b) : @I ((_133668 -> Prop) -> Prop) (@FINITE _133668) s.
Proof. exact (EQ_MP (@lem7141737 _133668 s) (@lem7141734 _133668 f s b h1)). Qed.
Lemma lem7141741 {_133668 : Type'} (s : _133668 -> Prop) (h1 : term29 _133668 s) : term29 _133668 s.
Proof. exact (h1). Qed.
Lemma lem7141742 {_133668 : Type'} (s : _133668 -> Prop) (h1 : term29 _133668 s) : term603 _133668 s.
Proof. exact (fun h0 : s = (@EMPTY _133668) => @lem7141741 _133668 s h1). Qed.
Lemma lem7141744 (p : Prop) : (term604 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7141745 {_133668 : Type'} (s : _133668 -> Prop) : (term603 _133668 s) = (term29 _133668 s).
Proof. exact (@lem7141744 (s = (@EMPTY _133668))). Qed.
Lemma lem7141746 {_133668 : Type'} (s : _133668 -> Prop) (h1 : term29 _133668 s) : term29 _133668 s.
Proof. exact (EQ_MP (@lem7141745 _133668 s) (@lem7141742 _133668 s h1)). Qed.
Lemma lem7141748 (b : Prop) (a : Prop) : (a \/ b) = (term605 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7141751 {_133668 : Type'} (x : type684 _133668) (_95347 : _133668 -> Prop) : (term416 _133668 x _95347) = (term606 _133668 x _95347).
Proof. exact (@lem7141748 (_95347 = (@EMPTY _133668)) (term413 _133668 x _95347)). Qed.
Lemma lem7141754 {_133668 : Type'} (_95347 : _133668 -> Prop) (x : type684 _133668) (h1 : term384 _133668 x) : term606 _133668 x _95347.
Proof. exact (EQ_MP (@lem7141751 _133668 x _95347) (@lem7141190 _133668 _95347 x h1)). Qed.
Lemma lem7141755 {_133668 : Type'} (_95347 : _133668 -> Prop) (x : type684 _133668) (h1 : term384 _133668 x) : term606 _133668 x _95347.
Proof. exact (@lem7141754 _133668 _95347 x h1). Qed.
Lemma lem7141756 {_133668 : Type'} (s : _133668 -> Prop) (x : type684 _133668) (h1 : term384 _133668 x) : term606 _133668 x s.
Proof. exact (@lem7141755 _133668 s x h1). Qed.
Lemma lem7141759 {_133668 : Type'} (s : _133668 -> Prop) (x : type684 _133668) (h1 : term29 _133668 s) (h2 : term384 _133668 x) : term413 _133668 x s.
Proof. exact (@lem7141756 _133668 s x h2 (@lem7141746 _133668 s h1)). Qed.
Lemma lem7141760 {_133668 : Type'} (s : _133668 -> Prop) (x : type684 _133668) (h1 : term29 _133668 s) (h2 : term384 _133668 x) : term607 _133668 x s.
Proof. exact (fun h0 : term608 _133668 x s => @lem7141759 _133668 s x h1 h2). Qed.
Lemma lem7141762 (p : Prop) : (term602 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7141763 {_133668 : Type'} (x : type684 _133668) (s : _133668 -> Prop) : (term607 _133668 x s) = (term413 _133668 x s).
Proof. exact (@lem7141762 (term413 _133668 x s)). Qed.
Lemma lem7141764 {_133668 : Type'} (s : _133668 -> Prop) (x : type684 _133668) (h1 : term29 _133668 s) (h2 : term384 _133668 x) : term413 _133668 x s.
Proof. exact (EQ_MP (@lem7141763 _133668 x s) (@lem7141760 _133668 s x h1 h2)). Qed.
Lemma lem7141767 {_133668 : Type'} (s : _133668 -> Prop) (h1 : term29 _133668 s) : term29 _133668 s.
Proof. exact (h1). Qed.
Lemma lem7141768 {_133668 : Type'} (s : _133668 -> Prop) (h1 : term29 _133668 s) : term603 _133668 s.
Proof. exact (fun h0 : s = (@EMPTY _133668) => @lem7141767 _133668 s h1). Qed.
Lemma lem7141770 (p : Prop) : (term604 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7141771 {_133668 : Type'} (s : _133668 -> Prop) : (term603 _133668 s) = (term29 _133668 s).
Proof. exact (@lem7141770 (s = (@EMPTY _133668))). Qed.
Lemma lem7141772 {_133668 : Type'} (s : _133668 -> Prop) (h1 : term29 _133668 s) : term29 _133668 s.
Proof. exact (EQ_MP (@lem7141771 _133668 s) (@lem7141768 _133668 s h1)). Qed.
Lemma lem7141774 {_133668 : Type'} (_95347 : _133668 -> Prop) (x : type684 _133668) (h1 : term384 _133668 x) : term606 _133668 x _95347.
Proof. exact (EQ_MP (@lem7141751 _133668 x _95347) (@lem7141190 _133668 _95347 x h1)). Qed.
Lemma lem7141775 {_133668 : Type'} (_95347 : _133668 -> Prop) (x : type684 _133668) (h1 : term384 _133668 x) : term606 _133668 x _95347.
Proof. exact (@lem7141774 _133668 _95347 x h1). Qed.
Lemma lem7141776 {_133668 : Type'} (s : _133668 -> Prop) (x : type684 _133668) (h1 : term384 _133668 x) : term606 _133668 x s.
Proof. exact (@lem7141775 _133668 s x h1). Qed.
Lemma lem7141779 {_133668 : Type'} (s : _133668 -> Prop) (x : type684 _133668) (h1 : term29 _133668 s) (h2 : term384 _133668 x) : term413 _133668 x s.
Proof. exact (@lem7141776 _133668 s x h2 (@lem7141772 _133668 s h1)). Qed.
Lemma lem7141780 {_133668 : Type'} (s : _133668 -> Prop) (x : type684 _133668) (h1 : term29 _133668 s) (h2 : term384 _133668 x) : term607 _133668 x s.
Proof. exact (fun h0 : term608 _133668 x s => @lem7141779 _133668 s x h1 h2). Qed.
Lemma lem7141782 (p : Prop) : (term602 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7141783 {_133668 : Type'} (x : type684 _133668) (s : _133668 -> Prop) : (term607 _133668 x s) = (term413 _133668 x s).
Proof. exact (@lem7141782 (term413 _133668 x s)). Qed.
Lemma lem7141784 {_133668 : Type'} (s : _133668 -> Prop) (x : type684 _133668) (h1 : term29 _133668 s) (h2 : term384 _133668 x) : term413 _133668 x s.
Proof. exact (EQ_MP (@lem7141783 _133668 x s) (@lem7141780 _133668 s x h1 h2)). Qed.
Lemma lem7141790 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7141791 {_133668 : Type'} (f : _133668 -> real) (b : real) (_95346 : _133668) (s : _133668 -> Prop) : (term499 _133668 s f _95346 b) = (term609 _133668 f b _95346 s).
Proof. exact (@lem7141790 (term443 _133668 f _95346 b) (term400 _133668 _95346 s)). Qed.
Lemma lem7141797 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7141798 {_133668 : Type'} (f : _133668 -> real) (b : real) (_95346 : _133668) (s : _133668 -> Prop) : (term610 _133668 s f _95346 b) = (term611 _133668 f b _95346 s).
Proof. exact (MK_COMB (@lem7141797) (@lem7141791 _133668 f b _95346 s)). Qed.
Lemma lem7141804 {_133668 : Type'} (f : _133668 -> real) (b : real) (_95346 : _133668) (s : _133668 -> Prop) : (term609 _133668 f b _95346 s) = (term609 _133668 f b _95346 s).
Proof. exact (eq_refl (term609 _133668 f b _95346 s)). Qed.
Lemma lem7141805 {_133668 : Type'} (f : _133668 -> real) (b : real) (_95346 : _133668) (s : _133668 -> Prop) : ((term499 _133668 s f _95346 b) = (term609 _133668 f b _95346 s)) = ((term609 _133668 f b _95346 s) = (term609 _133668 f b _95346 s)).
Proof. exact (MK_COMB (@lem7141798 _133668 f b _95346 s) (@lem7141804 _133668 f b _95346 s)). Qed.
Lemma lem7141807 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7141808 (x : Prop) : (x = x) = True.
Proof. exact (@lem7141807 Prop x). Qed.
Lemma lem7141809 {_133668 : Type'} (f : _133668 -> real) (b : real) (_95346 : _133668) (s : _133668 -> Prop) : ((term609 _133668 f b _95346 s) = (term609 _133668 f b _95346 s)) = True.
Proof. exact (@lem7141808 (term609 _133668 f b _95346 s)). Qed.
Lemma lem7141810 {_133668 : Type'} (f : _133668 -> real) (b : real) (_95346 : _133668) (s : _133668 -> Prop) : ((term499 _133668 s f _95346 b) = (term609 _133668 f b _95346 s)) = True.
Proof. exact (TRANS (@lem7141805 _133668 f b _95346 s) (@lem7141809 _133668 f b _95346 s)). Qed.
Lemma lem7141811 {_133668 : Type'} (f : _133668 -> real) (b : real) (_95346 : _133668) (s : _133668 -> Prop) : True = ((term499 _133668 s f _95346 b) = (term609 _133668 f b _95346 s)).
Proof. exact (SYM (@lem7141810 _133668 f b _95346 s)). Qed.
Lemma lem7141812 {_133668 : Type'} (f : _133668 -> real) (b : real) (_95346 : _133668) (s : _133668 -> Prop) : (term499 _133668 s f _95346 b) = (term609 _133668 f b _95346 s).
Proof. exact (EQ_MP (@lem7141811 _133668 f b _95346 s) (@lem0)). Qed.
Lemma lem7141813 {_133668 : Type'} (_95346 : _133668) (f : _133668 -> real) (s : _133668 -> Prop) (b : real) (h1 : term80 _133668 f s b) : term609 _133668 f b _95346 s.
Proof. exact (EQ_MP (@lem7141812 _133668 f b _95346 s) (@lem7141184 _133668 _95346 f s b h1)). Qed.
Lemma lem7141815 (b : Prop) (a : Prop) : (a \/ b) = (term605 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7141816 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (_95346 : _133668) (b : real) : (term609 _133668 f b _95346 s) = (term612 _133668 s f _95346 b).
Proof. exact (@lem7141815 (term400 _133668 _95346 s) (term443 _133668 f _95346 b)). Qed.
Lemma lem7141818 (a : Prop) : (term613 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7141819 {_133668 : Type'} (_95346 : _133668) (s : _133668 -> Prop) : (term614 _133668 _95346 s) = (term399 _133668 _95346 s).
Proof. exact (@lem7141818 (term399 _133668 _95346 s)). Qed.
Lemma lem7141820 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7141821 {_133668 : Type'} (_95346 : _133668) (s : _133668 -> Prop) : (term615 _133668 _95346 s) = (term616 _133668 _95346 s).
Proof. exact (MK_COMB (@lem7141820) (@lem7141819 _133668 _95346 s)). Qed.
Lemma lem7141822 {_133668 : Type'} (f : _133668 -> real) (_95346 : _133668) (b : real) : (term443 _133668 f _95346 b) = (term443 _133668 f _95346 b).
Proof. exact (eq_refl (term443 _133668 f _95346 b)). Qed.
Lemma lem7141823 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (_95346 : _133668) (b : real) : (term612 _133668 s f _95346 b) = (term617 _133668 s f _95346 b).
Proof. exact (MK_COMB (@lem7141821 _133668 _95346 s) (@lem7141822 _133668 f _95346 b)). Qed.
Lemma lem7141824 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (_95346 : _133668) (b : real) : (term609 _133668 f b _95346 s) = (term617 _133668 s f _95346 b).
Proof. exact (TRANS (@lem7141816 _133668 s f _95346 b) (@lem7141823 _133668 s f _95346 b)). Qed.
Lemma lem7141827 {_133668 : Type'} (_95346 : _133668) (f : _133668 -> real) (s : _133668 -> Prop) (b : real) (h1 : term80 _133668 f s b) : term617 _133668 s f _95346 b.
Proof. exact (EQ_MP (@lem7141824 _133668 s f _95346 b) (@lem7141813 _133668 _95346 f s b h1)). Qed.
Lemma lem7141828 {_133668 : Type'} (_95346 : _133668) (f : _133668 -> real) (s : _133668 -> Prop) (b : real) (h1 : term80 _133668 f s b) : term617 _133668 s f _95346 b.
Proof. exact (@lem7141827 _133668 _95346 f s b h1). Qed.
Lemma lem7141829 {_133668 : Type'} (x : type684 _133668) (f : _133668 -> real) (s : _133668 -> Prop) (b : real) (h1 : term80 _133668 f s b) : term618 _133668 f x s b.
Proof. exact (@lem7141828 _133668 (@I ((_133668 -> Prop) -> _133668) x s) f s b h1). Qed.
Lemma lem7141832 {_133668 : Type'} (x : type684 _133668) (f : _133668 -> real) (s : _133668 -> Prop) (b : real) (h1 : term29 _133668 s) (h2 : term384 _133668 x) (h3 : term80 _133668 f s b) : term619 _133668 f x s b.
Proof. exact (@lem7141829 _133668 x f s b h3 (@lem7141784 _133668 s x h1 h2)). Qed.
Lemma lem7141833 {_133668 : Type'} (x : type684 _133668) (f : _133668 -> real) (s : _133668 -> Prop) (b : real) (h1 : term29 _133668 s) (h2 : term384 _133668 x) (h3 : term80 _133668 f s b) : term620 _133668 f x s b.
Proof. exact (fun h0 : term621 _133668 f x s b => @lem7141832 _133668 x f s b h1 h2 h3). Qed.
Lemma lem7141835 (p : Prop) : (term602 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7141836 {_133668 : Type'} (f : _133668 -> real) (x : type684 _133668) (s : _133668 -> Prop) (b : real) : (term620 _133668 f x s b) = (term619 _133668 f x s b).
Proof. exact (@lem7141835 (term619 _133668 f x s b)). Qed.
Lemma lem7141837 {_133668 : Type'} (x : type684 _133668) (f : _133668 -> real) (s : _133668 -> Prop) (b : real) (h1 : term29 _133668 s) (h2 : term384 _133668 x) (h3 : term80 _133668 f s b) : term619 _133668 f x s b.
Proof. exact (EQ_MP (@lem7141836 _133668 f x s b) (@lem7141833 _133668 x f s b h1 h2 h3)). Qed.
Lemma lem7141839 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) (h1 : term80 _133668 f s b) : term498 _133668 f s b.
Proof. exact (proj2 (@lem7140732 _133668 f s b h1)). Qed.
Lemma lem7141840 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) (h1 : term80 _133668 f s b) : term622 _133668 f s b.
Proof. exact (fun h0 : term437 _133668 f s b => @lem7141839 _133668 f s b h1). Qed.
Lemma lem7141842 (p : Prop) : (term604 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7141843 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term622 _133668 f s b) = (term498 _133668 f s b).
Proof. exact (@lem7141842 (term437 _133668 f s b)). Qed.
Lemma lem7141844 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) (h1 : term80 _133668 f s b) : term498 _133668 f s b.
Proof. exact (EQ_MP (@lem7141843 _133668 f s b) (@lem7141840 _133668 f s b h1)). Qed.
Lemma lem7141850 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7141851 {_133668 : Type'} (x'' : type645 _133668) (_95345 : _133668) (_95343 : _133668 -> real) (_95342 : _133668 -> Prop) (_95344 : real) : (term594 _133668 x'' _95345 _95343 _95342 _95344) = (term623 _133668 x'' _95345 _95343 _95342 _95344).
Proof. exact (@lem7141850 (term472 _133668 x'' _95343 _95344 _95342) (term481 _133668 _95342) (term591 _133668 _95345 _95343 _95342 _95344)). Qed.
Lemma lem7141885 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7141886 {_133668 : Type'} (_95342 : _133668 -> Prop) (_95343 : _133668 -> real) (_95345 : _133668) (_95344 : real) : (term624 _133668 _95345 _95343 _95342 _95344) = (term625 _133668 _95342 _95343 _95345 _95344).
Proof. exact (@lem7141885 (term437 _133668 _95343 _95342 _95344) (term445 _133668 _95343 _95345 _95344)). Qed.
Lemma lem7141892 {_133668 : Type'} (_95345 : _133668) (_95342 : _133668 -> Prop) : (term447 _133668 _95345 _95342) = (term447 _133668 _95345 _95342).
Proof. exact (eq_refl (term447 _133668 _95345 _95342)). Qed.
Lemma lem7141893 {_133668 : Type'} (_95342 : _133668 -> Prop) (_95343 : _133668 -> real) (_95345 : _133668) (_95344 : real) : (term591 _133668 _95345 _95343 _95342 _95344) = (term626 _133668 _95342 _95343 _95345 _95344).
Proof. exact (MK_COMB (@lem7141892 _133668 _95345 _95342) (@lem7141886 _133668 _95342 _95343 _95345 _95344)). Qed.
Lemma lem7141897 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7141898 {_133668 : Type'} (_95342 : _133668 -> Prop) (_95343 : _133668 -> real) (_95345 : _133668) (_95344 : real) : (term626 _133668 _95342 _95343 _95345 _95344) = (term627 _133668 _95342 _95343 _95345 _95344).
Proof. exact (@lem7141897 (term437 _133668 _95343 _95342 _95344) (term400 _133668 _95345 _95342) (term445 _133668 _95343 _95345 _95344)). Qed.
Lemma lem7141914 {_133668 : Type'} (_95342 : _133668 -> Prop) (_95343 : _133668 -> real) (_95345 : _133668) (_95344 : real) : (term591 _133668 _95345 _95343 _95342 _95344) = (term627 _133668 _95342 _95343 _95345 _95344).
Proof. exact (TRANS (@lem7141893 _133668 _95342 _95343 _95345 _95344) (@lem7141898 _133668 _95342 _95343 _95345 _95344)). Qed.
Lemma lem7141915 {_133668 : Type'} (_95342 : _133668 -> Prop) : (term482 _133668 _95342) = (term482 _133668 _95342).
Proof. exact (eq_refl (term482 _133668 _95342)). Qed.
Lemma lem7141916 {_133668 : Type'} (_95342 : _133668 -> Prop) (_95343 : _133668 -> real) (_95345 : _133668) (_95344 : real) : (term628 _133668 _95345 _95343 _95342 _95344) = (term629 _133668 _95342 _95343 _95345 _95344).
Proof. exact (MK_COMB (@lem7141915 _133668 _95342) (@lem7141914 _133668 _95342 _95343 _95345 _95344)). Qed.
Lemma lem7141920 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7141921 {_133668 : Type'} (_95342 : _133668 -> Prop) (_95343 : _133668 -> real) (_95345 : _133668) (_95344 : real) : (term629 _133668 _95342 _95343 _95345 _95344) = (term630 _133668 _95342 _95343 _95345 _95344).
Proof. exact (@lem7141920 (term437 _133668 _95343 _95342 _95344) (term481 _133668 _95342) (term448 _133668 _95342 _95343 _95345 _95344)). Qed.
Lemma lem7141947 {_133668 : Type'} (_95342 : _133668 -> Prop) (_95343 : _133668 -> real) (_95345 : _133668) (_95344 : real) : (term628 _133668 _95345 _95343 _95342 _95344) = (term630 _133668 _95342 _95343 _95345 _95344).
Proof. exact (TRANS (@lem7141916 _133668 _95342 _95343 _95345 _95344) (@lem7141921 _133668 _95342 _95343 _95345 _95344)). Qed.
Lemma lem7141948 {_133668 : Type'} (x'' : type645 _133668) (_95343 : _133668 -> real) (_95344 : real) (_95342 : _133668 -> Prop) : (term592 _133668 x'' _95343 _95344 _95342) = (term592 _133668 x'' _95343 _95344 _95342).
Proof. exact (eq_refl (term592 _133668 x'' _95343 _95344 _95342)). Qed.
Lemma lem7141949 {_133668 : Type'} (x'' : type645 _133668) (_95342 : _133668 -> Prop) (_95343 : _133668 -> real) (_95345 : _133668) (_95344 : real) : (term623 _133668 x'' _95345 _95343 _95342 _95344) = (term631 _133668 x'' _95342 _95343 _95345 _95344).
Proof. exact (MK_COMB (@lem7141948 _133668 x'' _95343 _95344 _95342) (@lem7141947 _133668 _95342 _95343 _95345 _95344)). Qed.
Lemma lem7141960 {_133668 : Type'} (x'' : type645 _133668) (_95342 : _133668 -> Prop) (_95343 : _133668 -> real) (_95345 : _133668) (_95344 : real) : (term594 _133668 x'' _95345 _95343 _95342 _95344) = (term631 _133668 x'' _95342 _95343 _95345 _95344).
Proof. exact (TRANS (@lem7141851 _133668 x'' _95345 _95343 _95342 _95344) (@lem7141949 _133668 x'' _95342 _95343 _95345 _95344)). Qed.
Lemma lem7141961 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7141962 {_133668 : Type'} (x'' : type645 _133668) (_95342 : _133668 -> Prop) (_95343 : _133668 -> real) (_95345 : _133668) (_95344 : real) : (term632 _133668 x'' _95345 _95343 _95342 _95344) = (term633 _133668 x'' _95342 _95343 _95345 _95344).
Proof. exact (MK_COMB (@lem7141961) (@lem7141960 _133668 x'' _95342 _95343 _95345 _95344)). Qed.
Lemma lem7141996 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7141997 {_133668 : Type'} (_95342 : _133668 -> Prop) (_95343 : _133668 -> real) (_95345 : _133668) (_95344 : real) : (term624 _133668 _95345 _95343 _95342 _95344) = (term625 _133668 _95342 _95343 _95345 _95344).
Proof. exact (@lem7141996 (term437 _133668 _95343 _95342 _95344) (term445 _133668 _95343 _95345 _95344)). Qed.
Lemma lem7142003 {_133668 : Type'} (_95345 : _133668) (_95342 : _133668 -> Prop) : (term447 _133668 _95345 _95342) = (term447 _133668 _95345 _95342).
Proof. exact (eq_refl (term447 _133668 _95345 _95342)). Qed.
Lemma lem7142004 {_133668 : Type'} (_95342 : _133668 -> Prop) (_95343 : _133668 -> real) (_95345 : _133668) (_95344 : real) : (term591 _133668 _95345 _95343 _95342 _95344) = (term626 _133668 _95342 _95343 _95345 _95344).
Proof. exact (MK_COMB (@lem7142003 _133668 _95345 _95342) (@lem7141997 _133668 _95342 _95343 _95345 _95344)). Qed.
Lemma lem7142008 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7142009 {_133668 : Type'} (_95342 : _133668 -> Prop) (_95343 : _133668 -> real) (_95345 : _133668) (_95344 : real) : (term626 _133668 _95342 _95343 _95345 _95344) = (term627 _133668 _95342 _95343 _95345 _95344).
Proof. exact (@lem7142008 (term437 _133668 _95343 _95342 _95344) (term400 _133668 _95345 _95342) (term445 _133668 _95343 _95345 _95344)). Qed.
Lemma lem7142025 {_133668 : Type'} (_95342 : _133668 -> Prop) (_95343 : _133668 -> real) (_95345 : _133668) (_95344 : real) : (term591 _133668 _95345 _95343 _95342 _95344) = (term627 _133668 _95342 _95343 _95345 _95344).
Proof. exact (TRANS (@lem7142004 _133668 _95342 _95343 _95345 _95344) (@lem7142009 _133668 _95342 _95343 _95345 _95344)). Qed.
Lemma lem7142026 {_133668 : Type'} (_95342 : _133668 -> Prop) : (term482 _133668 _95342) = (term482 _133668 _95342).
Proof. exact (eq_refl (term482 _133668 _95342)). Qed.
Lemma lem7142027 {_133668 : Type'} (_95342 : _133668 -> Prop) (_95343 : _133668 -> real) (_95345 : _133668) (_95344 : real) : (term628 _133668 _95345 _95343 _95342 _95344) = (term629 _133668 _95342 _95343 _95345 _95344).
Proof. exact (MK_COMB (@lem7142026 _133668 _95342) (@lem7142025 _133668 _95342 _95343 _95345 _95344)). Qed.
Lemma lem7142031 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7142032 {_133668 : Type'} (_95342 : _133668 -> Prop) (_95343 : _133668 -> real) (_95345 : _133668) (_95344 : real) : (term629 _133668 _95342 _95343 _95345 _95344) = (term630 _133668 _95342 _95343 _95345 _95344).
Proof. exact (@lem7142031 (term437 _133668 _95343 _95342 _95344) (term481 _133668 _95342) (term448 _133668 _95342 _95343 _95345 _95344)). Qed.
Lemma lem7142058 {_133668 : Type'} (_95342 : _133668 -> Prop) (_95343 : _133668 -> real) (_95345 : _133668) (_95344 : real) : (term628 _133668 _95345 _95343 _95342 _95344) = (term630 _133668 _95342 _95343 _95345 _95344).
Proof. exact (TRANS (@lem7142027 _133668 _95342 _95343 _95345 _95344) (@lem7142032 _133668 _95342 _95343 _95345 _95344)). Qed.
Lemma lem7142059 {_133668 : Type'} (x'' : type645 _133668) (_95343 : _133668 -> real) (_95344 : real) (_95342 : _133668 -> Prop) : (term592 _133668 x'' _95343 _95344 _95342) = (term592 _133668 x'' _95343 _95344 _95342).
Proof. exact (eq_refl (term592 _133668 x'' _95343 _95344 _95342)). Qed.
Lemma lem7142060 {_133668 : Type'} (x'' : type645 _133668) (_95342 : _133668 -> Prop) (_95343 : _133668 -> real) (_95345 : _133668) (_95344 : real) : (term623 _133668 x'' _95345 _95343 _95342 _95344) = (term631 _133668 x'' _95342 _95343 _95345 _95344).
Proof. exact (MK_COMB (@lem7142059 _133668 x'' _95343 _95344 _95342) (@lem7142058 _133668 _95342 _95343 _95345 _95344)). Qed.
Lemma lem7142071 {_133668 : Type'} (x'' : type645 _133668) (_95342 : _133668 -> Prop) (_95343 : _133668 -> real) (_95345 : _133668) (_95344 : real) : ((term594 _133668 x'' _95345 _95343 _95342 _95344) = (term623 _133668 x'' _95345 _95343 _95342 _95344)) = ((term631 _133668 x'' _95342 _95343 _95345 _95344) = (term631 _133668 x'' _95342 _95343 _95345 _95344)).
Proof. exact (MK_COMB (@lem7141962 _133668 x'' _95342 _95343 _95345 _95344) (@lem7142060 _133668 x'' _95342 _95343 _95345 _95344)). Qed.
Lemma lem7142073 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7142074 (x : Prop) : (x = x) = True.
Proof. exact (@lem7142073 Prop x). Qed.
Lemma lem7142075 {_133668 : Type'} (x'' : type645 _133668) (_95342 : _133668 -> Prop) (_95343 : _133668 -> real) (_95345 : _133668) (_95344 : real) : ((term631 _133668 x'' _95342 _95343 _95345 _95344) = (term631 _133668 x'' _95342 _95343 _95345 _95344)) = True.
Proof. exact (@lem7142074 (term631 _133668 x'' _95342 _95343 _95345 _95344)). Qed.
Lemma lem7142076 {_133668 : Type'} (x'' : type645 _133668) (_95345 : _133668) (_95343 : _133668 -> real) (_95342 : _133668 -> Prop) (_95344 : real) : ((term594 _133668 x'' _95345 _95343 _95342 _95344) = (term623 _133668 x'' _95345 _95343 _95342 _95344)) = True.
Proof. exact (TRANS (@lem7142071 _133668 x'' _95342 _95343 _95345 _95344) (@lem7142075 _133668 x'' _95342 _95343 _95345 _95344)). Qed.
Lemma lem7142077 {_133668 : Type'} (x'' : type645 _133668) (_95345 : _133668) (_95343 : _133668 -> real) (_95342 : _133668 -> Prop) (_95344 : real) : True = ((term594 _133668 x'' _95345 _95343 _95342 _95344) = (term623 _133668 x'' _95345 _95343 _95342 _95344)).
Proof. exact (SYM (@lem7142076 _133668 x'' _95345 _95343 _95342 _95344)). Qed.
Lemma lem7142078 {_133668 : Type'} (x'' : type645 _133668) (_95345 : _133668) (_95343 : _133668 -> real) (_95342 : _133668 -> Prop) (_95344 : real) : (term594 _133668 x'' _95345 _95343 _95342 _95344) = (term623 _133668 x'' _95345 _95343 _95342 _95344).
Proof. exact (EQ_MP (@lem7142077 _133668 x'' _95345 _95343 _95342 _95344) (@lem0)). Qed.
Lemma lem7142079 {_133668 : Type'} (_95345 : _133668) (_95343 : _133668 -> real) (_95342 : _133668 -> Prop) (_95344 : real) (x'' : type645 _133668) (h1 : term273 _133668 x'') : term623 _133668 x'' _95345 _95343 _95342 _95344.
Proof. exact (EQ_MP (@lem7142078 _133668 x'' _95345 _95343 _95342 _95344) (@lem7141220 _133668 _95345 _95343 _95342 _95344 x'' h1)). Qed.
Lemma lem7142081 (b : Prop) (a : Prop) : (a \/ b) = (term605 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7142082 {_133668 : Type'} (_95345 : _133668) (x'' : type645 _133668) (_95343 : _133668 -> real) (_95344 : real) (_95342 : _133668 -> Prop) : (term623 _133668 x'' _95345 _95343 _95342 _95344) = (term634 _133668 _95345 x'' _95343 _95344 _95342).
Proof. exact (@lem7142081 (term628 _133668 _95345 _95343 _95342 _95344) (term472 _133668 x'' _95343 _95344 _95342)). Qed.
Lemma lem7142084 (a : Prop) (b : Prop) : (term635 a b) = (term636 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7142085 {_133668 : Type'} (_95345 : _133668) (_95343 : _133668 -> real) (_95342 : _133668 -> Prop) (_95344 : real) : (term637 _133668 _95345 _95343 _95342 _95344) = (term638 _133668 _95345 _95343 _95342 _95344).
Proof. exact (@lem7142084 (term481 _133668 _95342) (term591 _133668 _95345 _95343 _95342 _95344)). Qed.
Lemma lem7142087 (a : Prop) : (term613 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7142088 {_133668 : Type'} (_95342 : _133668 -> Prop) : (term639 _133668 _95342) = (@I ((_133668 -> Prop) -> Prop) (@FINITE _133668) _95342).
Proof. exact (@lem7142087 (@I ((_133668 -> Prop) -> Prop) (@FINITE _133668) _95342)). Qed.
Lemma lem7142089 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7142090 {_133668 : Type'} (_95342 : _133668 -> Prop) : (term640 _133668 _95342) = (term503 _133668 _95342).
Proof. exact (MK_COMB (@lem7142089) (@lem7142088 _133668 _95342)). Qed.
Lemma lem7142092 (a : Prop) (b : Prop) : (term635 a b) = (term636 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7142093 {_133668 : Type'} (_95345 : _133668) (_95343 : _133668 -> real) (_95342 : _133668 -> Prop) (_95344 : real) : (term641 _133668 _95345 _95343 _95342 _95344) = (term642 _133668 _95345 _95343 _95342 _95344).
Proof. exact (@lem7142092 (term400 _133668 _95345 _95342) (term624 _133668 _95345 _95343 _95342 _95344)). Qed.
Lemma lem7142095 (a : Prop) : (term613 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7142096 {_133668 : Type'} (_95345 : _133668) (_95342 : _133668 -> Prop) : (term614 _133668 _95345 _95342) = (term399 _133668 _95345 _95342).
Proof. exact (@lem7142095 (term399 _133668 _95345 _95342)). Qed.
Lemma lem7142097 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7142098 {_133668 : Type'} (_95345 : _133668) (_95342 : _133668 -> Prop) : (term643 _133668 _95345 _95342) = (term644 _133668 _95345 _95342).
Proof. exact (MK_COMB (@lem7142097) (@lem7142096 _133668 _95345 _95342)). Qed.
Lemma lem7142100 (a : Prop) (b : Prop) : (term635 a b) = (term636 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7142101 {_133668 : Type'} (_95345 : _133668) (_95343 : _133668 -> real) (_95342 : _133668 -> Prop) (_95344 : real) : (term645 _133668 _95345 _95343 _95342 _95344) = (term646 _133668 _95345 _95343 _95342 _95344).
Proof. exact (@lem7142100 (term445 _133668 _95343 _95345 _95344) (term437 _133668 _95343 _95342 _95344)). Qed.
Lemma lem7142103 (a : Prop) : (term613 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7142104 {_133668 : Type'} (_95343 : _133668 -> real) (_95345 : _133668) (_95344 : real) : (term647 _133668 _95343 _95345 _95344) = (term443 _133668 _95343 _95345 _95344).
Proof. exact (@lem7142103 (term443 _133668 _95343 _95345 _95344)). Qed.
Lemma lem7142105 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7142106 {_133668 : Type'} (_95343 : _133668 -> real) (_95345 : _133668) (_95344 : real) : (term648 _133668 _95343 _95345 _95344) = (term649 _133668 _95343 _95345 _95344).
Proof. exact (MK_COMB (@lem7142105) (@lem7142104 _133668 _95343 _95345 _95344)). Qed.
Lemma lem7142107 {_133668 : Type'} (_95343 : _133668 -> real) (_95342 : _133668 -> Prop) (_95344 : real) : (term498 _133668 _95343 _95342 _95344) = (term498 _133668 _95343 _95342 _95344).
Proof. exact (eq_refl (term498 _133668 _95343 _95342 _95344)). Qed.
Lemma lem7142108 {_133668 : Type'} (_95345 : _133668) (_95343 : _133668 -> real) (_95342 : _133668 -> Prop) (_95344 : real) : (term646 _133668 _95345 _95343 _95342 _95344) = (term650 _133668 _95345 _95343 _95342 _95344).
Proof. exact (MK_COMB (@lem7142106 _133668 _95343 _95345 _95344) (@lem7142107 _133668 _95343 _95342 _95344)). Qed.
Lemma lem7142109 {_133668 : Type'} (_95345 : _133668) (_95343 : _133668 -> real) (_95342 : _133668 -> Prop) (_95344 : real) : (term645 _133668 _95345 _95343 _95342 _95344) = (term650 _133668 _95345 _95343 _95342 _95344).
Proof. exact (TRANS (@lem7142101 _133668 _95345 _95343 _95342 _95344) (@lem7142108 _133668 _95345 _95343 _95342 _95344)). Qed.
Lemma lem7142110 {_133668 : Type'} (_95345 : _133668) (_95343 : _133668 -> real) (_95342 : _133668 -> Prop) (_95344 : real) : (term642 _133668 _95345 _95343 _95342 _95344) = (term651 _133668 _95345 _95343 _95342 _95344).
Proof. exact (MK_COMB (@lem7142098 _133668 _95345 _95342) (@lem7142109 _133668 _95345 _95343 _95342 _95344)). Qed.
Lemma lem7142111 {_133668 : Type'} (_95345 : _133668) (_95343 : _133668 -> real) (_95342 : _133668 -> Prop) (_95344 : real) : (term641 _133668 _95345 _95343 _95342 _95344) = (term651 _133668 _95345 _95343 _95342 _95344).
Proof. exact (TRANS (@lem7142093 _133668 _95345 _95343 _95342 _95344) (@lem7142110 _133668 _95345 _95343 _95342 _95344)). Qed.
Lemma lem7142112 {_133668 : Type'} (_95345 : _133668) (_95343 : _133668 -> real) (_95342 : _133668 -> Prop) (_95344 : real) : (term638 _133668 _95345 _95343 _95342 _95344) = (term652 _133668 _95345 _95343 _95342 _95344).
Proof. exact (MK_COMB (@lem7142090 _133668 _95342) (@lem7142111 _133668 _95345 _95343 _95342 _95344)). Qed.
Lemma lem7142113 {_133668 : Type'} (_95345 : _133668) (_95343 : _133668 -> real) (_95342 : _133668 -> Prop) (_95344 : real) : (term637 _133668 _95345 _95343 _95342 _95344) = (term652 _133668 _95345 _95343 _95342 _95344).
Proof. exact (TRANS (@lem7142085 _133668 _95345 _95343 _95342 _95344) (@lem7142112 _133668 _95345 _95343 _95342 _95344)). Qed.
Lemma lem7142114 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7142115 {_133668 : Type'} (_95345 : _133668) (_95343 : _133668 -> real) (_95342 : _133668 -> Prop) (_95344 : real) : (term653 _133668 _95345 _95343 _95342 _95344) = (term654 _133668 _95345 _95343 _95342 _95344).
Proof. exact (MK_COMB (@lem7142114) (@lem7142113 _133668 _95345 _95343 _95342 _95344)). Qed.
Lemma lem7142116 {_133668 : Type'} (x'' : type645 _133668) (_95343 : _133668 -> real) (_95344 : real) (_95342 : _133668 -> Prop) : (term472 _133668 x'' _95343 _95344 _95342) = (term472 _133668 x'' _95343 _95344 _95342).
Proof. exact (eq_refl (term472 _133668 x'' _95343 _95344 _95342)). Qed.
Lemma lem7142117 {_133668 : Type'} (_95345 : _133668) (x'' : type645 _133668) (_95343 : _133668 -> real) (_95344 : real) (_95342 : _133668 -> Prop) : (term634 _133668 _95345 x'' _95343 _95344 _95342) = (term655 _133668 _95345 x'' _95343 _95344 _95342).
Proof. exact (MK_COMB (@lem7142115 _133668 _95345 _95343 _95342 _95344) (@lem7142116 _133668 x'' _95343 _95344 _95342)). Qed.
Lemma lem7142118 {_133668 : Type'} (_95345 : _133668) (x'' : type645 _133668) (_95343 : _133668 -> real) (_95344 : real) (_95342 : _133668 -> Prop) : (term623 _133668 x'' _95345 _95343 _95342 _95344) = (term655 _133668 _95345 x'' _95343 _95344 _95342).
Proof. exact (TRANS (@lem7142082 _133668 _95345 x'' _95343 _95344 _95342) (@lem7142117 _133668 _95345 x'' _95343 _95344 _95342)). Qed.
Lemma lem7142120 {_133668 : Type'} (x : type684 _133668) (f : _133668 -> real) (s : _133668 -> Prop) (b : real) (h1 : term29 _133668 s) (h2 : term384 _133668 x) (h3 : term80 _133668 f s b) : term656 _133668 x f s b.
Proof. exact (conj (@lem7141837 _133668 x f s b h1 h2 h3) (@lem7141844 _133668 f s b h3)). Qed.
Lemma lem7142121 {_133668 : Type'} (x : type684 _133668) (f : _133668 -> real) (s : _133668 -> Prop) (b : real) (h1 : term29 _133668 s) (h2 : term384 _133668 x) (h3 : term80 _133668 f s b) : term657 _133668 x f s b.
Proof. exact (conj (@lem7141764 _133668 s x h1 h2) (@lem7142120 _133668 x f s b h1 h2 h3)). Qed.
Lemma lem7142122 {_133668 : Type'} (x : type684 _133668) (f : _133668 -> real) (s : _133668 -> Prop) (b : real) (h1 : term29 _133668 s) (h2 : term384 _133668 x) (h3 : term80 _133668 f s b) : term658 _133668 x f s b.
Proof. exact (conj (@lem7141738 _133668 f s b h3) (@lem7142121 _133668 x f s b h1 h2 h3)). Qed.
Lemma lem7142124 {_133668 : Type'} (_95345 : _133668) (_95343 : _133668 -> real) (_95344 : real) (_95342 : _133668 -> Prop) (x'' : type645 _133668) (h1 : term273 _133668 x'') : term655 _133668 _95345 x'' _95343 _95344 _95342.
Proof. exact (EQ_MP (@lem7142118 _133668 _95345 x'' _95343 _95344 _95342) (@lem7142079 _133668 _95345 _95343 _95342 _95344 x'' h1)). Qed.
Lemma lem7142125 {_133668 : Type'} (_95345 : _133668) (_95343 : _133668 -> real) (_95344 : real) (_95342 : _133668 -> Prop) (x'' : type645 _133668) (h1 : term273 _133668 x'') : term655 _133668 _95345 x'' _95343 _95344 _95342.
Proof. exact (@lem7142124 _133668 _95345 _95343 _95344 _95342 x'' h1). Qed.
Lemma lem7142126 {_133668 : Type'} (x : type684 _133668) (f : _133668 -> real) (b : real) (s : _133668 -> Prop) (x'' : type645 _133668) (h1 : term273 _133668 x'') : term659 _133668 x x'' f b s.
Proof. exact (@lem7142125 _133668 (@I ((_133668 -> Prop) -> _133668) x s) f b s x'' h1). Qed.
Lemma lem7142129 {_133668 : Type'} (x'' : type645 _133668) (x : type684 _133668) (f : _133668 -> real) (s : _133668 -> Prop) (b : real) (h1 : term273 _133668 x'') (h2 : term29 _133668 s) (h3 : term384 _133668 x) (h4 : term80 _133668 f s b) : term472 _133668 x'' f b s.
Proof. exact (@lem7142126 _133668 x f b s x'' h1 (@lem7142122 _133668 x f s b h2 h3 h4)). Qed.
Lemma lem7142130 {_133668 : Type'} (x'' : type645 _133668) (x : type684 _133668) (f : _133668 -> real) (s : _133668 -> Prop) (b : real) (h1 : term273 _133668 x'') (h2 : term29 _133668 s) (h3 : term384 _133668 x) (h4 : term80 _133668 f s b) : term660 _133668 x'' f b s.
Proof. exact (fun h0 : term661 _133668 x'' f b s => @lem7142129 _133668 x'' x f s b h1 h2 h3 h4). Qed.
Lemma lem7142132 (p : Prop) : (term602 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7142133 {_133668 : Type'} (x'' : type645 _133668) (f : _133668 -> real) (b : real) (s : _133668 -> Prop) : (term660 _133668 x'' f b s) = (term472 _133668 x'' f b s).
Proof. exact (@lem7142132 (term472 _133668 x'' f b s)). Qed.
Lemma lem7142134 {_133668 : Type'} (x'' : type645 _133668) (x : type684 _133668) (f : _133668 -> real) (s : _133668 -> Prop) (b : real) (h1 : term273 _133668 x'') (h2 : term29 _133668 s) (h3 : term384 _133668 x) (h4 : term80 _133668 f s b) : term472 _133668 x'' f b s.
Proof. exact (EQ_MP (@lem7142133 _133668 x'' f b s) (@lem7142130 _133668 x'' x f s b h1 h2 h3 h4)). Qed.
Lemma lem7142136 {_133668 : Type'} (_95346 : _133668) (f : _133668 -> real) (s : _133668 -> Prop) (b : real) (h1 : term80 _133668 f s b) : term617 _133668 s f _95346 b.
Proof. exact (EQ_MP (@lem7141824 _133668 s f _95346 b) (@lem7141813 _133668 _95346 f s b h1)). Qed.
Lemma lem7142137 {_133668 : Type'} (_95346 : _133668) (f : _133668 -> real) (s : _133668 -> Prop) (b : real) (h1 : term80 _133668 f s b) : term617 _133668 s f _95346 b.
Proof. exact (@lem7142136 _133668 _95346 f s b h1). Qed.
Lemma lem7142138 {_133668 : Type'} (x'' : type645 _133668) (f : _133668 -> real) (s : _133668 -> Prop) (b : real) (h1 : term80 _133668 f s b) : term662 _133668 x'' s f b.
Proof. exact (@lem7142137 _133668 (term453 _133668 x'' s f b) f s b h1). Qed.
Lemma lem7142141 {_133668 : Type'} (x'' : type645 _133668) (x : type684 _133668) (f : _133668 -> real) (s : _133668 -> Prop) (b : real) (h1 : term273 _133668 x'') (h2 : term29 _133668 s) (h3 : term384 _133668 x) (h4 : term80 _133668 f s b) : term663 _133668 x'' s f b.
Proof. exact (@lem7142138 _133668 x'' f s b h4 (@lem7142134 _133668 x'' x f s b h1 h2 h3 h4)). Qed.
Lemma lem7142142 {_133668 : Type'} (x'' : type645 _133668) (x : type684 _133668) (f : _133668 -> real) (s : _133668 -> Prop) (b : real) (h1 : term273 _133668 x'') (h2 : term29 _133668 s) (h3 : term384 _133668 x) (h4 : term80 _133668 f s b) : term664 _133668 x'' s f b.
Proof. exact (fun h0 : term665 _133668 x'' s f b => @lem7142141 _133668 x'' x f s b h1 h2 h3 h4). Qed.
Lemma lem7142144 (p : Prop) : (term602 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7142145 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term664 _133668 x'' s f b) = (term663 _133668 x'' s f b).
Proof. exact (@lem7142144 (term663 _133668 x'' s f b)). Qed.
Lemma lem7142146 {_133668 : Type'} (x'' : type645 _133668) (x : type684 _133668) (f : _133668 -> real) (s : _133668 -> Prop) (b : real) (h1 : term273 _133668 x'') (h2 : term29 _133668 s) (h3 : term384 _133668 x) (h4 : term80 _133668 f s b) : term663 _133668 x'' s f b.
Proof. exact (EQ_MP (@lem7142145 _133668 x'' s f b) (@lem7142142 _133668 x'' x f s b h1 h2 h3 h4)). Qed.
Lemma lem7142152 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7142153 (_95336 : real) (_95337 : real) : (term394 _95336 _95337) = (term666 _95336 _95337).
Proof. exact (@lem7142152 (term388 _95336 _95337) (term391 _95336 _95337)). Qed.
Lemma lem7142159 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7142160 (_95336 : real) (_95337 : real) : (term667 _95336 _95337) = (term668 _95336 _95337).
Proof. exact (MK_COMB (@lem7142159) (@lem7142153 _95336 _95337)). Qed.
Lemma lem7142166 (_95336 : real) (_95337 : real) : (term666 _95336 _95337) = (term666 _95336 _95337).
Proof. exact (eq_refl (term666 _95336 _95337)). Qed.
Lemma lem7142167 (_95336 : real) (_95337 : real) : ((term394 _95336 _95337) = (term666 _95336 _95337)) = ((term666 _95336 _95337) = (term666 _95336 _95337)).
Proof. exact (MK_COMB (@lem7142160 _95336 _95337) (@lem7142166 _95336 _95337)). Qed.
Lemma lem7142169 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7142170 (x : Prop) : (x = x) = True.
Proof. exact (@lem7142169 Prop x). Qed.
Lemma lem7142171 (_95336 : real) (_95337 : real) : ((term666 _95336 _95337) = (term666 _95336 _95337)) = True.
Proof. exact (@lem7142170 (term666 _95336 _95337)). Qed.
Lemma lem7142172 (_95336 : real) (_95337 : real) : ((term394 _95336 _95337) = (term666 _95336 _95337)) = True.
Proof. exact (TRANS (@lem7142167 _95336 _95337) (@lem7142171 _95336 _95337)). Qed.
Lemma lem7142173 (_95336 : real) (_95337 : real) : True = ((term394 _95336 _95337) = (term666 _95336 _95337)).
Proof. exact (SYM (@lem7142172 _95336 _95337)). Qed.
Lemma lem7142174 (_95336 : real) (_95337 : real) : (term394 _95336 _95337) = (term666 _95336 _95337).
Proof. exact (EQ_MP (@lem7142173 _95336 _95337) (@lem0)). Qed.
Lemma lem7142175 (_95336 : real) (_95337 : real) (h1 : term38) : term666 _95336 _95337.
Proof. exact (EQ_MP (@lem7142174 _95336 _95337) (@lem7141172 _95336 _95337 h1)). Qed.
Lemma lem7142177 (b : Prop) (a : Prop) : (a \/ b) = (term605 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7142178 (_95336 : real) (_95337 : real) : (term666 _95336 _95337) = (term669 _95336 _95337).
Proof. exact (@lem7142177 (term391 _95336 _95337) (term388 _95336 _95337)). Qed.
Lemma lem7142180 (a : Prop) : (term613 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7142181 (_95336 : real) (_95337 : real) : (term670 _95336 _95337) = (term389 _95336 _95337).
Proof. exact (@lem7142180 (term389 _95336 _95337)). Qed.
Lemma lem7142182 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7142183 (_95336 : real) (_95337 : real) : (term671 _95336 _95337) = (term672 _95336 _95337).
Proof. exact (MK_COMB (@lem7142182) (@lem7142181 _95336 _95337)). Qed.
Lemma lem7142184 (_95336 : real) (_95337 : real) : (term388 _95336 _95337) = (term388 _95336 _95337).
Proof. exact (eq_refl (term388 _95336 _95337)). Qed.
Lemma lem7142185 (_95336 : real) (_95337 : real) : (term669 _95336 _95337) = (term673 _95336 _95337).
Proof. exact (MK_COMB (@lem7142183 _95336 _95337) (@lem7142184 _95336 _95337)). Qed.
Lemma lem7142186 (_95336 : real) (_95337 : real) : (term666 _95336 _95337) = (term673 _95336 _95337).
Proof. exact (TRANS (@lem7142178 _95336 _95337) (@lem7142185 _95336 _95337)). Qed.
Lemma lem7142189 (_95336 : real) (_95337 : real) (h1 : term38) : term673 _95336 _95337.
Proof. exact (EQ_MP (@lem7142186 _95336 _95337) (@lem7142175 _95336 _95337 h1)). Qed.
Lemma lem7142190 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) (f : _133668 -> real) (b : real) (h1 : term38) : term674 _133668 x'' s f b.
Proof. exact (@lem7142189 (term456 _133668 x'' s f b) b h1). Qed.
Lemma lem7142193 {_133668 : Type'} (x'' : type645 _133668) (x : type684 _133668) (f : _133668 -> real) (s : _133668 -> Prop) (b : real) (h1 : term273 _133668 x'') (h2 : term38) (h3 : term29 _133668 s) (h4 : term384 _133668 x) (h5 : term80 _133668 f s b) : term463 _133668 x'' s f b.
Proof. exact (@lem7142190 _133668 x'' s f b h2 (@lem7142146 _133668 x'' x f s b h1 h3 h4 h5)). Qed.
Lemma lem7142194 {_133668 : Type'} (x'' : type645 _133668) (x : type684 _133668) (f : _133668 -> real) (s : _133668 -> Prop) (b : real) (h1 : term273 _133668 x'') (h2 : term38) (h3 : term29 _133668 s) (h4 : term384 _133668 x) (h5 : term80 _133668 f s b) : term675 _133668 x'' s f b.
Proof. exact (fun h0 : term465 _133668 x'' s f b => @lem7142193 _133668 x'' x f s b h1 h2 h3 h4 h5). Qed.
Lemma lem7142196 (p : Prop) : (term602 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7142197 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term675 _133668 x'' s f b) = (term463 _133668 x'' s f b).
Proof. exact (@lem7142196 (term463 _133668 x'' s f b)). Qed.
Lemma lem7142198 {_133668 : Type'} (x'' : type645 _133668) (x : type684 _133668) (f : _133668 -> real) (s : _133668 -> Prop) (b : real) (h1 : term273 _133668 x'') (h2 : term38) (h3 : term29 _133668 s) (h4 : term384 _133668 x) (h5 : term80 _133668 f s b) : term463 _133668 x'' s f b.
Proof. exact (EQ_MP (@lem7142197 _133668 x'' s f b) (@lem7142194 _133668 x'' x f s b h1 h2 h3 h4 h5)). Qed.
Lemma lem7142201 {_133668 : Type'} (s : _133668 -> Prop) (h1 : term29 _133668 s) : term29 _133668 s.
Proof. exact (h1). Qed.
Lemma lem7142202 {_133668 : Type'} (s : _133668 -> Prop) (h1 : term29 _133668 s) : term603 _133668 s.
Proof. exact (fun h0 : s = (@EMPTY _133668) => @lem7142201 _133668 s h1). Qed.
Lemma lem7142204 (p : Prop) : (term604 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7142205 {_133668 : Type'} (s : _133668 -> Prop) : (term603 _133668 s) = (term29 _133668 s).
Proof. exact (@lem7142204 (s = (@EMPTY _133668))). Qed.
Lemma lem7142206 {_133668 : Type'} (s : _133668 -> Prop) (h1 : term29 _133668 s) : term29 _133668 s.
Proof. exact (EQ_MP (@lem7142205 _133668 s) (@lem7142202 _133668 s h1)). Qed.
Lemma lem7142208 {_133668 : Type'} (_95347 : _133668 -> Prop) (x : type684 _133668) (h1 : term384 _133668 x) : term606 _133668 x _95347.
Proof. exact (EQ_MP (@lem7141751 _133668 x _95347) (@lem7141190 _133668 _95347 x h1)). Qed.
Lemma lem7142209 {_133668 : Type'} (_95347 : _133668 -> Prop) (x : type684 _133668) (h1 : term384 _133668 x) : term606 _133668 x _95347.
Proof. exact (@lem7142208 _133668 _95347 x h1). Qed.
Lemma lem7142210 {_133668 : Type'} (s : _133668 -> Prop) (x : type684 _133668) (h1 : term384 _133668 x) : term606 _133668 x s.
Proof. exact (@lem7142209 _133668 s x h1). Qed.
Lemma lem7142213 {_133668 : Type'} (s : _133668 -> Prop) (x : type684 _133668) (h1 : term29 _133668 s) (h2 : term384 _133668 x) : term413 _133668 x s.
Proof. exact (@lem7142210 _133668 s x h2 (@lem7142206 _133668 s h1)). Qed.
Lemma lem7142214 {_133668 : Type'} (s : _133668 -> Prop) (x : type684 _133668) (h1 : term29 _133668 s) (h2 : term384 _133668 x) : term607 _133668 x s.
Proof. exact (fun h0 : term608 _133668 x s => @lem7142213 _133668 s x h1 h2). Qed.
Lemma lem7142216 (p : Prop) : (term602 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7142217 {_133668 : Type'} (x : type684 _133668) (s : _133668 -> Prop) : (term607 _133668 x s) = (term413 _133668 x s).
Proof. exact (@lem7142216 (term413 _133668 x s)). Qed.
Lemma lem7142218 {_133668 : Type'} (s : _133668 -> Prop) (x : type684 _133668) (h1 : term29 _133668 s) (h2 : term384 _133668 x) : term413 _133668 x s.
Proof. exact (EQ_MP (@lem7142217 _133668 x s) (@lem7142214 _133668 s x h1 h2)). Qed.
Lemma lem7142220 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) (h1 : term80 _133668 f s b) : term498 _133668 f s b.
Proof. exact (proj2 (@lem7140732 _133668 f s b h1)). Qed.
Lemma lem7142221 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) (h1 : term80 _133668 f s b) : term622 _133668 f s b.
Proof. exact (fun h0 : term437 _133668 f s b => @lem7142220 _133668 f s b h1). Qed.
Lemma lem7142223 (p : Prop) : (term604 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7142224 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term622 _133668 f s b) = (term498 _133668 f s b).
Proof. exact (@lem7142223 (term437 _133668 f s b)). Qed.
Lemma lem7142225 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) (h1 : term80 _133668 f s b) : term498 _133668 f s b.
Proof. exact (EQ_MP (@lem7142224 _133668 f s b) (@lem7142221 _133668 f s b h1)). Qed.
Lemma lem7142241 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7142242 {_133668 : Type'} (x'' : type645 _133668) (_95345 : _133668) (_95343 : _133668 -> real) (_95342 : _133668 -> Prop) (_95344 : real) : (term599 _133668 x'' _95345 _95343 _95342 _95344) = (term676 _133668 x'' _95345 _95343 _95342 _95344).
Proof. exact (@lem7142241 (term400 _133668 _95345 _95342) (term465 _133668 x'' _95342 _95343 _95344) (term624 _133668 _95345 _95343 _95342 _95344)). Qed.
Lemma lem7142266 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7142267 {_133668 : Type'} (_95342 : _133668 -> Prop) (_95343 : _133668 -> real) (_95345 : _133668) (_95344 : real) : (term624 _133668 _95345 _95343 _95342 _95344) = (term625 _133668 _95342 _95343 _95345 _95344).
Proof. exact (@lem7142266 (term437 _133668 _95343 _95342 _95344) (term445 _133668 _95343 _95345 _95344)). Qed.
Lemma lem7142273 {_133668 : Type'} (x'' : type645 _133668) (_95342 : _133668 -> Prop) (_95343 : _133668 -> real) (_95344 : real) : (term598 _133668 x'' _95342 _95343 _95344) = (term598 _133668 x'' _95342 _95343 _95344).
Proof. exact (eq_refl (term598 _133668 x'' _95342 _95343 _95344)). Qed.
Lemma lem7142274 {_133668 : Type'} (x'' : type645 _133668) (_95342 : _133668 -> Prop) (_95343 : _133668 -> real) (_95345 : _133668) (_95344 : real) : (term677 _133668 x'' _95345 _95343 _95342 _95344) = (term678 _133668 x'' _95342 _95343 _95345 _95344).
Proof. exact (MK_COMB (@lem7142273 _133668 x'' _95342 _95343 _95344) (@lem7142267 _133668 _95342 _95343 _95345 _95344)). Qed.
Lemma lem7142278 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7142279 {_133668 : Type'} (x'' : type645 _133668) (_95342 : _133668 -> Prop) (_95343 : _133668 -> real) (_95345 : _133668) (_95344 : real) : (term678 _133668 x'' _95342 _95343 _95345 _95344) = (term679 _133668 x'' _95342 _95343 _95345 _95344).
Proof. exact (@lem7142278 (term437 _133668 _95343 _95342 _95344) (term465 _133668 x'' _95342 _95343 _95344) (term445 _133668 _95343 _95345 _95344)). Qed.
Lemma lem7142295 {_133668 : Type'} (x'' : type645 _133668) (_95342 : _133668 -> Prop) (_95343 : _133668 -> real) (_95345 : _133668) (_95344 : real) : (term677 _133668 x'' _95345 _95343 _95342 _95344) = (term679 _133668 x'' _95342 _95343 _95345 _95344).
Proof. exact (TRANS (@lem7142274 _133668 x'' _95342 _95343 _95345 _95344) (@lem7142279 _133668 x'' _95342 _95343 _95345 _95344)). Qed.
Lemma lem7142296 {_133668 : Type'} (_95345 : _133668) (_95342 : _133668 -> Prop) : (term447 _133668 _95345 _95342) = (term447 _133668 _95345 _95342).
Proof. exact (eq_refl (term447 _133668 _95345 _95342)). Qed.
Lemma lem7142297 {_133668 : Type'} (x'' : type645 _133668) (_95342 : _133668 -> Prop) (_95343 : _133668 -> real) (_95345 : _133668) (_95344 : real) : (term676 _133668 x'' _95345 _95343 _95342 _95344) = (term680 _133668 x'' _95342 _95343 _95345 _95344).
Proof. exact (MK_COMB (@lem7142296 _133668 _95345 _95342) (@lem7142295 _133668 x'' _95342 _95343 _95345 _95344)). Qed.
Lemma lem7142301 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7142302 {_133668 : Type'} (x'' : type645 _133668) (_95342 : _133668 -> Prop) (_95343 : _133668 -> real) (_95345 : _133668) (_95344 : real) : (term680 _133668 x'' _95342 _95343 _95345 _95344) = (term681 _133668 x'' _95342 _95343 _95345 _95344).
Proof. exact (@lem7142301 (term437 _133668 _95343 _95342 _95344) (term400 _133668 _95345 _95342) (term682 _133668 x'' _95342 _95343 _95345 _95344)). Qed.
Lemma lem7142328 {_133668 : Type'} (x'' : type645 _133668) (_95342 : _133668 -> Prop) (_95343 : _133668 -> real) (_95345 : _133668) (_95344 : real) : (term676 _133668 x'' _95345 _95343 _95342 _95344) = (term681 _133668 x'' _95342 _95343 _95345 _95344).
Proof. exact (TRANS (@lem7142297 _133668 x'' _95342 _95343 _95345 _95344) (@lem7142302 _133668 x'' _95342 _95343 _95345 _95344)). Qed.
Lemma lem7142329 {_133668 : Type'} (x'' : type645 _133668) (_95342 : _133668 -> Prop) (_95343 : _133668 -> real) (_95345 : _133668) (_95344 : real) : (term599 _133668 x'' _95345 _95343 _95342 _95344) = (term681 _133668 x'' _95342 _95343 _95345 _95344).
Proof. exact (TRANS (@lem7142242 _133668 x'' _95345 _95343 _95342 _95344) (@lem7142328 _133668 x'' _95342 _95343 _95345 _95344)). Qed.
Lemma lem7142330 {_133668 : Type'} (_95342 : _133668 -> Prop) : (term482 _133668 _95342) = (term482 _133668 _95342).
Proof. exact (eq_refl (term482 _133668 _95342)). Qed.
Lemma lem7142331 {_133668 : Type'} (x'' : type645 _133668) (_95342 : _133668 -> Prop) (_95343 : _133668 -> real) (_95345 : _133668) (_95344 : real) : (term600 _133668 x'' _95345 _95343 _95342 _95344) = (term683 _133668 x'' _95342 _95343 _95345 _95344).
Proof. exact (MK_COMB (@lem7142330 _133668 _95342) (@lem7142329 _133668 x'' _95342 _95343 _95345 _95344)). Qed.
Lemma lem7142335 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7142336 {_133668 : Type'} (x'' : type645 _133668) (_95342 : _133668 -> Prop) (_95343 : _133668 -> real) (_95345 : _133668) (_95344 : real) : (term683 _133668 x'' _95342 _95343 _95345 _95344) = (term684 _133668 x'' _95342 _95343 _95345 _95344).
Proof. exact (@lem7142335 (term437 _133668 _95343 _95342 _95344) (term481 _133668 _95342) (term685 _133668 x'' _95342 _95343 _95345 _95344)). Qed.
Lemma lem7142372 {_133668 : Type'} (x'' : type645 _133668) (_95342 : _133668 -> Prop) (_95343 : _133668 -> real) (_95345 : _133668) (_95344 : real) : (term600 _133668 x'' _95345 _95343 _95342 _95344) = (term684 _133668 x'' _95342 _95343 _95345 _95344).
Proof. exact (TRANS (@lem7142331 _133668 x'' _95342 _95343 _95345 _95344) (@lem7142336 _133668 x'' _95342 _95343 _95345 _95344)). Qed.
Lemma lem7142373 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7142374 {_133668 : Type'} (x'' : type645 _133668) (_95342 : _133668 -> Prop) (_95343 : _133668 -> real) (_95345 : _133668) (_95344 : real) : (term686 _133668 x'' _95345 _95343 _95342 _95344) = (term687 _133668 x'' _95342 _95343 _95345 _95344).
Proof. exact (MK_COMB (@lem7142373) (@lem7142372 _133668 x'' _95342 _95343 _95345 _95344)). Qed.
Lemma lem7142378 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7142379 {_133668 : Type'} (x'' : type645 _133668) (_95345 : _133668) (_95343 : _133668 -> real) (_95342 : _133668 -> Prop) (_95344 : real) : (term688 _133668 x'' _95345 _95343 _95342 _95344) = (term689 _133668 x'' _95345 _95343 _95342 _95344).
Proof. exact (@lem7142378 (term481 _133668 _95342) (term445 _133668 _95343 _95345 _95344) (term690 _133668 x'' _95345 _95343 _95342 _95344)). Qed.
Lemma lem7142393 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7142394 {_133668 : Type'} (x'' : type645 _133668) (_95345 : _133668) (_95343 : _133668 -> real) (_95342 : _133668 -> Prop) (_95344 : real) : (term691 _133668 x'' _95345 _95343 _95342 _95344) = (term692 _133668 x'' _95345 _95343 _95342 _95344).
Proof. exact (@lem7142393 (term465 _133668 x'' _95342 _95343 _95344) (term445 _133668 _95343 _95345 _95344) (term693 _133668 _95345 _95343 _95342 _95344)). Qed.
Lemma lem7142408 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7142409 {_133668 : Type'} (_95345 : _133668) (_95343 : _133668 -> real) (_95342 : _133668 -> Prop) (_95344 : real) : (term694 _133668 _95345 _95343 _95342 _95344) = (term591 _133668 _95345 _95343 _95342 _95344).
Proof. exact (@lem7142408 (term400 _133668 _95345 _95342) (term445 _133668 _95343 _95345 _95344) (term437 _133668 _95343 _95342 _95344)). Qed.
Lemma lem7142423 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7142424 {_133668 : Type'} (_95342 : _133668 -> Prop) (_95343 : _133668 -> real) (_95345 : _133668) (_95344 : real) : (term624 _133668 _95345 _95343 _95342 _95344) = (term625 _133668 _95342 _95343 _95345 _95344).
Proof. exact (@lem7142423 (term437 _133668 _95343 _95342 _95344) (term445 _133668 _95343 _95345 _95344)). Qed.
Lemma lem7142430 {_133668 : Type'} (_95345 : _133668) (_95342 : _133668 -> Prop) : (term447 _133668 _95345 _95342) = (term447 _133668 _95345 _95342).
Proof. exact (eq_refl (term447 _133668 _95345 _95342)). Qed.
Lemma lem7142431 {_133668 : Type'} (_95342 : _133668 -> Prop) (_95343 : _133668 -> real) (_95345 : _133668) (_95344 : real) : (term591 _133668 _95345 _95343 _95342 _95344) = (term626 _133668 _95342 _95343 _95345 _95344).
Proof. exact (MK_COMB (@lem7142430 _133668 _95345 _95342) (@lem7142424 _133668 _95342 _95343 _95345 _95344)). Qed.
Lemma lem7142435 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7142436 {_133668 : Type'} (_95342 : _133668 -> Prop) (_95343 : _133668 -> real) (_95345 : _133668) (_95344 : real) : (term626 _133668 _95342 _95343 _95345 _95344) = (term627 _133668 _95342 _95343 _95345 _95344).
Proof. exact (@lem7142435 (term437 _133668 _95343 _95342 _95344) (term400 _133668 _95345 _95342) (term445 _133668 _95343 _95345 _95344)). Qed.
Lemma lem7142452 {_133668 : Type'} (_95342 : _133668 -> Prop) (_95343 : _133668 -> real) (_95345 : _133668) (_95344 : real) : (term591 _133668 _95345 _95343 _95342 _95344) = (term627 _133668 _95342 _95343 _95345 _95344).
Proof. exact (TRANS (@lem7142431 _133668 _95342 _95343 _95345 _95344) (@lem7142436 _133668 _95342 _95343 _95345 _95344)). Qed.
Lemma lem7142453 {_133668 : Type'} (_95342 : _133668 -> Prop) (_95343 : _133668 -> real) (_95345 : _133668) (_95344 : real) : (term694 _133668 _95345 _95343 _95342 _95344) = (term627 _133668 _95342 _95343 _95345 _95344).
Proof. exact (TRANS (@lem7142409 _133668 _95345 _95343 _95342 _95344) (@lem7142452 _133668 _95342 _95343 _95345 _95344)). Qed.
Lemma lem7142454 {_133668 : Type'} (x'' : type645 _133668) (_95342 : _133668 -> Prop) (_95343 : _133668 -> real) (_95344 : real) : (term598 _133668 x'' _95342 _95343 _95344) = (term598 _133668 x'' _95342 _95343 _95344).
Proof. exact (eq_refl (term598 _133668 x'' _95342 _95343 _95344)). Qed.
Lemma lem7142455 {_133668 : Type'} (x'' : type645 _133668) (_95342 : _133668 -> Prop) (_95343 : _133668 -> real) (_95345 : _133668) (_95344 : real) : (term692 _133668 x'' _95345 _95343 _95342 _95344) = (term695 _133668 x'' _95342 _95343 _95345 _95344).
Proof. exact (MK_COMB (@lem7142454 _133668 x'' _95342 _95343 _95344) (@lem7142453 _133668 _95342 _95343 _95345 _95344)). Qed.
Lemma lem7142459 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7142460 {_133668 : Type'} (x'' : type645 _133668) (_95342 : _133668 -> Prop) (_95343 : _133668 -> real) (_95345 : _133668) (_95344 : real) : (term695 _133668 x'' _95342 _95343 _95345 _95344) = (term696 _133668 x'' _95342 _95343 _95345 _95344).
Proof. exact (@lem7142459 (term437 _133668 _95343 _95342 _95344) (term465 _133668 x'' _95342 _95343 _95344) (term448 _133668 _95342 _95343 _95345 _95344)). Qed.
Lemma lem7142474 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7142475 {_133668 : Type'} (x'' : type645 _133668) (_95342 : _133668 -> Prop) (_95343 : _133668 -> real) (_95345 : _133668) (_95344 : real) : (term563 _133668 x'' _95342 _95343 _95345 _95344) = (term685 _133668 x'' _95342 _95343 _95345 _95344).
Proof. exact (@lem7142474 (term400 _133668 _95345 _95342) (term465 _133668 x'' _95342 _95343 _95344) (term445 _133668 _95343 _95345 _95344)). Qed.
Lemma lem7142491 {_133668 : Type'} (_95343 : _133668 -> real) (_95342 : _133668 -> Prop) (_95344 : real) : (term697 _133668 _95343 _95342 _95344) = (term697 _133668 _95343 _95342 _95344).
Proof. exact (eq_refl (term697 _133668 _95343 _95342 _95344)). Qed.
Lemma lem7142492 {_133668 : Type'} (x'' : type645 _133668) (_95342 : _133668 -> Prop) (_95343 : _133668 -> real) (_95345 : _133668) (_95344 : real) : (term696 _133668 x'' _95342 _95343 _95345 _95344) = (term681 _133668 x'' _95342 _95343 _95345 _95344).
Proof. exact (MK_COMB (@lem7142491 _133668 _95343 _95342 _95344) (@lem7142475 _133668 x'' _95342 _95343 _95345 _95344)). Qed.
Lemma lem7142503 {_133668 : Type'} (x'' : type645 _133668) (_95342 : _133668 -> Prop) (_95343 : _133668 -> real) (_95345 : _133668) (_95344 : real) : (term695 _133668 x'' _95342 _95343 _95345 _95344) = (term681 _133668 x'' _95342 _95343 _95345 _95344).
Proof. exact (TRANS (@lem7142460 _133668 x'' _95342 _95343 _95345 _95344) (@lem7142492 _133668 x'' _95342 _95343 _95345 _95344)). Qed.
Lemma lem7142504 {_133668 : Type'} (x'' : type645 _133668) (_95342 : _133668 -> Prop) (_95343 : _133668 -> real) (_95345 : _133668) (_95344 : real) : (term692 _133668 x'' _95345 _95343 _95342 _95344) = (term681 _133668 x'' _95342 _95343 _95345 _95344).
Proof. exact (TRANS (@lem7142455 _133668 x'' _95342 _95343 _95345 _95344) (@lem7142503 _133668 x'' _95342 _95343 _95345 _95344)). Qed.
Lemma lem7142505 {_133668 : Type'} (x'' : type645 _133668) (_95342 : _133668 -> Prop) (_95343 : _133668 -> real) (_95345 : _133668) (_95344 : real) : (term691 _133668 x'' _95345 _95343 _95342 _95344) = (term681 _133668 x'' _95342 _95343 _95345 _95344).
Proof. exact (TRANS (@lem7142394 _133668 x'' _95345 _95343 _95342 _95344) (@lem7142504 _133668 x'' _95342 _95343 _95345 _95344)). Qed.
Lemma lem7142506 {_133668 : Type'} (_95342 : _133668 -> Prop) : (term482 _133668 _95342) = (term482 _133668 _95342).
Proof. exact (eq_refl (term482 _133668 _95342)). Qed.
Lemma lem7142507 {_133668 : Type'} (x'' : type645 _133668) (_95342 : _133668 -> Prop) (_95343 : _133668 -> real) (_95345 : _133668) (_95344 : real) : (term689 _133668 x'' _95345 _95343 _95342 _95344) = (term683 _133668 x'' _95342 _95343 _95345 _95344).
Proof. exact (MK_COMB (@lem7142506 _133668 _95342) (@lem7142505 _133668 x'' _95342 _95343 _95345 _95344)). Qed.
Lemma lem7142511 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7142512 {_133668 : Type'} (x'' : type645 _133668) (_95342 : _133668 -> Prop) (_95343 : _133668 -> real) (_95345 : _133668) (_95344 : real) : (term683 _133668 x'' _95342 _95343 _95345 _95344) = (term684 _133668 x'' _95342 _95343 _95345 _95344).
Proof. exact (@lem7142511 (term437 _133668 _95343 _95342 _95344) (term481 _133668 _95342) (term685 _133668 x'' _95342 _95343 _95345 _95344)). Qed.
Lemma lem7142548 {_133668 : Type'} (x'' : type645 _133668) (_95342 : _133668 -> Prop) (_95343 : _133668 -> real) (_95345 : _133668) (_95344 : real) : (term689 _133668 x'' _95345 _95343 _95342 _95344) = (term684 _133668 x'' _95342 _95343 _95345 _95344).
Proof. exact (TRANS (@lem7142507 _133668 x'' _95342 _95343 _95345 _95344) (@lem7142512 _133668 x'' _95342 _95343 _95345 _95344)). Qed.
Lemma lem7142549 {_133668 : Type'} (x'' : type645 _133668) (_95342 : _133668 -> Prop) (_95343 : _133668 -> real) (_95345 : _133668) (_95344 : real) : (term688 _133668 x'' _95345 _95343 _95342 _95344) = (term684 _133668 x'' _95342 _95343 _95345 _95344).
Proof. exact (TRANS (@lem7142379 _133668 x'' _95345 _95343 _95342 _95344) (@lem7142548 _133668 x'' _95342 _95343 _95345 _95344)). Qed.
Lemma lem7142550 {_133668 : Type'} (x'' : type645 _133668) (_95342 : _133668 -> Prop) (_95343 : _133668 -> real) (_95345 : _133668) (_95344 : real) : ((term600 _133668 x'' _95345 _95343 _95342 _95344) = (term688 _133668 x'' _95345 _95343 _95342 _95344)) = ((term684 _133668 x'' _95342 _95343 _95345 _95344) = (term684 _133668 x'' _95342 _95343 _95345 _95344)).
Proof. exact (MK_COMB (@lem7142374 _133668 x'' _95342 _95343 _95345 _95344) (@lem7142549 _133668 x'' _95342 _95343 _95345 _95344)). Qed.
Lemma lem7142552 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7142553 (x : Prop) : (x = x) = True.
Proof. exact (@lem7142552 Prop x). Qed.
Lemma lem7142554 {_133668 : Type'} (x'' : type645 _133668) (_95342 : _133668 -> Prop) (_95343 : _133668 -> real) (_95345 : _133668) (_95344 : real) : ((term684 _133668 x'' _95342 _95343 _95345 _95344) = (term684 _133668 x'' _95342 _95343 _95345 _95344)) = True.
Proof. exact (@lem7142553 (term684 _133668 x'' _95342 _95343 _95345 _95344)). Qed.
Lemma lem7142555 {_133668 : Type'} (x'' : type645 _133668) (_95345 : _133668) (_95343 : _133668 -> real) (_95342 : _133668 -> Prop) (_95344 : real) : ((term600 _133668 x'' _95345 _95343 _95342 _95344) = (term688 _133668 x'' _95345 _95343 _95342 _95344)) = True.
Proof. exact (TRANS (@lem7142550 _133668 x'' _95342 _95343 _95345 _95344) (@lem7142554 _133668 x'' _95342 _95343 _95345 _95344)). Qed.
Lemma lem7142556 {_133668 : Type'} (x'' : type645 _133668) (_95345 : _133668) (_95343 : _133668 -> real) (_95342 : _133668 -> Prop) (_95344 : real) : True = ((term600 _133668 x'' _95345 _95343 _95342 _95344) = (term688 _133668 x'' _95345 _95343 _95342 _95344)).
Proof. exact (SYM (@lem7142555 _133668 x'' _95345 _95343 _95342 _95344)). Qed.
Lemma lem7142557 {_133668 : Type'} (x'' : type645 _133668) (_95345 : _133668) (_95343 : _133668 -> real) (_95342 : _133668 -> Prop) (_95344 : real) : (term600 _133668 x'' _95345 _95343 _95342 _95344) = (term688 _133668 x'' _95345 _95343 _95342 _95344).
Proof. exact (EQ_MP (@lem7142556 _133668 x'' _95345 _95343 _95342 _95344) (@lem0)). Qed.
Lemma lem7142558 {_133668 : Type'} (_95345 : _133668) (_95343 : _133668 -> real) (_95342 : _133668 -> Prop) (_95344 : real) (x'' : type645 _133668) (h1 : term273 _133668 x'') : term688 _133668 x'' _95345 _95343 _95342 _95344.
Proof. exact (EQ_MP (@lem7142557 _133668 x'' _95345 _95343 _95342 _95344) (@lem7141244 _133668 _95345 _95343 _95342 _95344 x'' h1)). Qed.
Lemma lem7142560 (b : Prop) (a : Prop) : (a \/ b) = (term605 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7142561 {_133668 : Type'} (x'' : type645 _133668) (_95342 : _133668 -> Prop) (_95343 : _133668 -> real) (_95345 : _133668) (_95344 : real) : (term688 _133668 x'' _95345 _95343 _95342 _95344) = (term698 _133668 x'' _95342 _95343 _95345 _95344).
Proof. exact (@lem7142560 (term699 _133668 x'' _95345 _95343 _95342 _95344) (term445 _133668 _95343 _95345 _95344)). Qed.
Lemma lem7142563 (a : Prop) (b : Prop) : (term635 a b) = (term636 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7142564 {_133668 : Type'} (x'' : type645 _133668) (_95345 : _133668) (_95343 : _133668 -> real) (_95342 : _133668 -> Prop) (_95344 : real) : (term700 _133668 x'' _95345 _95343 _95342 _95344) = (term701 _133668 x'' _95345 _95343 _95342 _95344).
Proof. exact (@lem7142563 (term481 _133668 _95342) (term690 _133668 x'' _95345 _95343 _95342 _95344)). Qed.
Lemma lem7142566 (a : Prop) : (term613 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7142567 {_133668 : Type'} (_95342 : _133668 -> Prop) : (term639 _133668 _95342) = (@I ((_133668 -> Prop) -> Prop) (@FINITE _133668) _95342).
Proof. exact (@lem7142566 (@I ((_133668 -> Prop) -> Prop) (@FINITE _133668) _95342)). Qed.
Lemma lem7142568 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7142569 {_133668 : Type'} (_95342 : _133668 -> Prop) : (term640 _133668 _95342) = (term503 _133668 _95342).
Proof. exact (MK_COMB (@lem7142568) (@lem7142567 _133668 _95342)). Qed.
Lemma lem7142571 (a : Prop) (b : Prop) : (term635 a b) = (term636 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7142572 {_133668 : Type'} (x'' : type645 _133668) (_95345 : _133668) (_95343 : _133668 -> real) (_95342 : _133668 -> Prop) (_95344 : real) : (term702 _133668 x'' _95345 _95343 _95342 _95344) = (term703 _133668 x'' _95345 _95343 _95342 _95344).
Proof. exact (@lem7142571 (term465 _133668 x'' _95342 _95343 _95344) (term693 _133668 _95345 _95343 _95342 _95344)). Qed.
Lemma lem7142574 (a : Prop) : (term613 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7142575 {_133668 : Type'} (x'' : type645 _133668) (_95342 : _133668 -> Prop) (_95343 : _133668 -> real) (_95344 : real) : (term704 _133668 x'' _95342 _95343 _95344) = (term463 _133668 x'' _95342 _95343 _95344).
Proof. exact (@lem7142574 (term463 _133668 x'' _95342 _95343 _95344)). Qed.
Lemma lem7142576 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7142577 {_133668 : Type'} (x'' : type645 _133668) (_95342 : _133668 -> Prop) (_95343 : _133668 -> real) (_95344 : real) : (term705 _133668 x'' _95342 _95343 _95344) = (term706 _133668 x'' _95342 _95343 _95344).
Proof. exact (MK_COMB (@lem7142576) (@lem7142575 _133668 x'' _95342 _95343 _95344)). Qed.
Lemma lem7142579 (a : Prop) (b : Prop) : (term635 a b) = (term636 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7142580 {_133668 : Type'} (_95345 : _133668) (_95343 : _133668 -> real) (_95342 : _133668 -> Prop) (_95344 : real) : (term707 _133668 _95345 _95343 _95342 _95344) = (term708 _133668 _95345 _95343 _95342 _95344).
Proof. exact (@lem7142579 (term400 _133668 _95345 _95342) (term437 _133668 _95343 _95342 _95344)). Qed.
Lemma lem7142582 (a : Prop) : (term613 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7142583 {_133668 : Type'} (_95345 : _133668) (_95342 : _133668 -> Prop) : (term614 _133668 _95345 _95342) = (term399 _133668 _95345 _95342).
Proof. exact (@lem7142582 (term399 _133668 _95345 _95342)). Qed.
Lemma lem7142584 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7142585 {_133668 : Type'} (_95345 : _133668) (_95342 : _133668 -> Prop) : (term643 _133668 _95345 _95342) = (term644 _133668 _95345 _95342).
Proof. exact (MK_COMB (@lem7142584) (@lem7142583 _133668 _95345 _95342)). Qed.
Lemma lem7142586 {_133668 : Type'} (_95343 : _133668 -> real) (_95342 : _133668 -> Prop) (_95344 : real) : (term498 _133668 _95343 _95342 _95344) = (term498 _133668 _95343 _95342 _95344).
Proof. exact (eq_refl (term498 _133668 _95343 _95342 _95344)). Qed.
Lemma lem7142587 {_133668 : Type'} (_95345 : _133668) (_95343 : _133668 -> real) (_95342 : _133668 -> Prop) (_95344 : real) : (term708 _133668 _95345 _95343 _95342 _95344) = (term709 _133668 _95345 _95343 _95342 _95344).
Proof. exact (MK_COMB (@lem7142585 _133668 _95345 _95342) (@lem7142586 _133668 _95343 _95342 _95344)). Qed.
Lemma lem7142588 {_133668 : Type'} (_95345 : _133668) (_95343 : _133668 -> real) (_95342 : _133668 -> Prop) (_95344 : real) : (term707 _133668 _95345 _95343 _95342 _95344) = (term709 _133668 _95345 _95343 _95342 _95344).
Proof. exact (TRANS (@lem7142580 _133668 _95345 _95343 _95342 _95344) (@lem7142587 _133668 _95345 _95343 _95342 _95344)). Qed.
Lemma lem7142589 {_133668 : Type'} (x'' : type645 _133668) (_95345 : _133668) (_95343 : _133668 -> real) (_95342 : _133668 -> Prop) (_95344 : real) : (term703 _133668 x'' _95345 _95343 _95342 _95344) = (term710 _133668 x'' _95345 _95343 _95342 _95344).
Proof. exact (MK_COMB (@lem7142577 _133668 x'' _95342 _95343 _95344) (@lem7142588 _133668 _95345 _95343 _95342 _95344)). Qed.
Lemma lem7142590 {_133668 : Type'} (x'' : type645 _133668) (_95345 : _133668) (_95343 : _133668 -> real) (_95342 : _133668 -> Prop) (_95344 : real) : (term702 _133668 x'' _95345 _95343 _95342 _95344) = (term710 _133668 x'' _95345 _95343 _95342 _95344).
Proof. exact (TRANS (@lem7142572 _133668 x'' _95345 _95343 _95342 _95344) (@lem7142589 _133668 x'' _95345 _95343 _95342 _95344)). Qed.
Lemma lem7142591 {_133668 : Type'} (x'' : type645 _133668) (_95345 : _133668) (_95343 : _133668 -> real) (_95342 : _133668 -> Prop) (_95344 : real) : (term701 _133668 x'' _95345 _95343 _95342 _95344) = (term711 _133668 x'' _95345 _95343 _95342 _95344).
Proof. exact (MK_COMB (@lem7142569 _133668 _95342) (@lem7142590 _133668 x'' _95345 _95343 _95342 _95344)). Qed.
Lemma lem7142592 {_133668 : Type'} (x'' : type645 _133668) (_95345 : _133668) (_95343 : _133668 -> real) (_95342 : _133668 -> Prop) (_95344 : real) : (term700 _133668 x'' _95345 _95343 _95342 _95344) = (term711 _133668 x'' _95345 _95343 _95342 _95344).
Proof. exact (TRANS (@lem7142564 _133668 x'' _95345 _95343 _95342 _95344) (@lem7142591 _133668 x'' _95345 _95343 _95342 _95344)). Qed.
Lemma lem7142593 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7142594 {_133668 : Type'} (x'' : type645 _133668) (_95345 : _133668) (_95343 : _133668 -> real) (_95342 : _133668 -> Prop) (_95344 : real) : (term712 _133668 x'' _95345 _95343 _95342 _95344) = (term713 _133668 x'' _95345 _95343 _95342 _95344).
Proof. exact (MK_COMB (@lem7142593) (@lem7142592 _133668 x'' _95345 _95343 _95342 _95344)). Qed.
Lemma lem7142595 {_133668 : Type'} (_95343 : _133668 -> real) (_95345 : _133668) (_95344 : real) : (term445 _133668 _95343 _95345 _95344) = (term445 _133668 _95343 _95345 _95344).
Proof. exact (eq_refl (term445 _133668 _95343 _95345 _95344)). Qed.
Lemma lem7142596 {_133668 : Type'} (x'' : type645 _133668) (_95342 : _133668 -> Prop) (_95343 : _133668 -> real) (_95345 : _133668) (_95344 : real) : (term698 _133668 x'' _95342 _95343 _95345 _95344) = (term714 _133668 x'' _95342 _95343 _95345 _95344).
Proof. exact (MK_COMB (@lem7142594 _133668 x'' _95345 _95343 _95342 _95344) (@lem7142595 _133668 _95343 _95345 _95344)). Qed.
Lemma lem7142597 {_133668 : Type'} (x'' : type645 _133668) (_95342 : _133668 -> Prop) (_95343 : _133668 -> real) (_95345 : _133668) (_95344 : real) : (term688 _133668 x'' _95345 _95343 _95342 _95344) = (term714 _133668 x'' _95342 _95343 _95345 _95344).
Proof. exact (TRANS (@lem7142561 _133668 x'' _95342 _95343 _95345 _95344) (@lem7142596 _133668 x'' _95342 _95343 _95345 _95344)). Qed.
Lemma lem7142599 {_133668 : Type'} (x : type684 _133668) (f : _133668 -> real) (s : _133668 -> Prop) (b : real) (h1 : term29 _133668 s) (h2 : term384 _133668 x) (h3 : term80 _133668 f s b) : term715 _133668 x f s b.
Proof. exact (conj (@lem7142218 _133668 s x h1 h2) (@lem7142225 _133668 f s b h3)). Qed.
Lemma lem7142600 {_133668 : Type'} (x'' : type645 _133668) (x : type684 _133668) (f : _133668 -> real) (s : _133668 -> Prop) (b : real) (h1 : term273 _133668 x'') (h2 : term38) (h3 : term29 _133668 s) (h4 : term384 _133668 x) (h5 : term80 _133668 f s b) : term716 _133668 x'' x f s b.
Proof. exact (conj (@lem7142198 _133668 x'' x f s b h1 h2 h3 h4 h5) (@lem7142599 _133668 x f s b h3 h4 h5)). Qed.
Lemma lem7142601 {_133668 : Type'} (x'' : type645 _133668) (x : type684 _133668) (f : _133668 -> real) (s : _133668 -> Prop) (b : real) (h1 : term273 _133668 x'') (h2 : term38) (h3 : term29 _133668 s) (h4 : term384 _133668 x) (h5 : term80 _133668 f s b) : term717 _133668 x'' x f s b.
Proof. exact (conj (@lem7141731 _133668 f s b h5) (@lem7142600 _133668 x'' x f s b h1 h2 h3 h4 h5)). Qed.
Lemma lem7142603 {_133668 : Type'} (_95342 : _133668 -> Prop) (_95343 : _133668 -> real) (_95345 : _133668) (_95344 : real) (x'' : type645 _133668) (h1 : term273 _133668 x'') : term714 _133668 x'' _95342 _95343 _95345 _95344.
Proof. exact (EQ_MP (@lem7142597 _133668 x'' _95342 _95343 _95345 _95344) (@lem7142558 _133668 _95345 _95343 _95342 _95344 x'' h1)). Qed.
Lemma lem7142604 {_133668 : Type'} (_95342 : _133668 -> Prop) (_95343 : _133668 -> real) (_95345 : _133668) (_95344 : real) (x'' : type645 _133668) (h1 : term273 _133668 x'') : term714 _133668 x'' _95342 _95343 _95345 _95344.
Proof. exact (@lem7142603 _133668 _95342 _95343 _95345 _95344 x'' h1). Qed.
Lemma lem7142605 {_133668 : Type'} (f : _133668 -> real) (x : type684 _133668) (s : _133668 -> Prop) (b : real) (x'' : type645 _133668) (h1 : term273 _133668 x'') : term718 _133668 x'' f x s b.
Proof. exact (@lem7142604 _133668 s f (@I ((_133668 -> Prop) -> _133668) x s) b x'' h1). Qed.
Lemma lem7142608 {_133668 : Type'} (x'' : type645 _133668) (x : type684 _133668) (f : _133668 -> real) (s : _133668 -> Prop) (b : real) (h1 : term273 _133668 x'') (h2 : term38) (h3 : term29 _133668 s) (h4 : term384 _133668 x) (h5 : term80 _133668 f s b) : term621 _133668 f x s b.
Proof. exact (@lem7142605 _133668 f x s b x'' h1 (@lem7142601 _133668 x'' x f s b h1 h2 h3 h4 h5)). Qed.
Lemma lem7142609 {_133668 : Type'} (x'' : type645 _133668) (x : type684 _133668) (f : _133668 -> real) (s : _133668 -> Prop) (b : real) (h1 : term273 _133668 x'') (h2 : term38) (h3 : term29 _133668 s) (h4 : term384 _133668 x) (h5 : term80 _133668 f s b) : term719 _133668 f x s b.
Proof. exact (fun h0 : term619 _133668 f x s b => @lem7142608 _133668 x'' x f s b h1 h2 h3 h4 h5). Qed.
Lemma lem7142611 (p : Prop) : (term604 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7142612 {_133668 : Type'} (f : _133668 -> real) (x : type684 _133668) (s : _133668 -> Prop) (b : real) : (term719 _133668 f x s b) = (term621 _133668 f x s b).
Proof. exact (@lem7142611 (term619 _133668 f x s b)). Qed.
Lemma lem7142613 {_133668 : Type'} (x'' : type645 _133668) (x : type684 _133668) (f : _133668 -> real) (s : _133668 -> Prop) (b : real) (h1 : term273 _133668 x'') (h2 : term38) (h3 : term29 _133668 s) (h4 : term384 _133668 x) (h5 : term80 _133668 f s b) : term621 _133668 f x s b.
Proof. exact (EQ_MP (@lem7142612 _133668 f x s b) (@lem7142609 _133668 x'' x f s b h1 h2 h3 h4 h5)). Qed.
Lemma lem7142615 (b : Prop) (a : Prop) : (a \/ b) = (term605 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7142618 {_133668 : Type'} (f : _133668 -> real) (b : real) (_95346 : _133668) (s : _133668 -> Prop) : (term499 _133668 s f _95346 b) = (term720 _133668 f b _95346 s).
Proof. exact (@lem7142615 (term443 _133668 f _95346 b) (term400 _133668 _95346 s)). Qed.
Lemma lem7142621 {_133668 : Type'} (_95346 : _133668) (f : _133668 -> real) (s : _133668 -> Prop) (b : real) (h1 : term80 _133668 f s b) : term720 _133668 f b _95346 s.
Proof. exact (EQ_MP (@lem7142618 _133668 f b _95346 s) (@lem7141184 _133668 _95346 f s b h1)). Qed.
Lemma lem7142622 {_133668 : Type'} (_95346 : _133668) (f : _133668 -> real) (s : _133668 -> Prop) (b : real) (h1 : term80 _133668 f s b) : term720 _133668 f b _95346 s.
Proof. exact (@lem7142621 _133668 _95346 f s b h1). Qed.
Lemma lem7142623 {_133668 : Type'} (x : type684 _133668) (f : _133668 -> real) (s : _133668 -> Prop) (b : real) (h1 : term80 _133668 f s b) : term721 _133668 f b x s.
Proof. exact (@lem7142622 _133668 (@I ((_133668 -> Prop) -> _133668) x s) f s b h1). Qed.
Lemma lem7142626 {_133668 : Type'} (x'' : type645 _133668) (x : type684 _133668) (f : _133668 -> real) (s : _133668 -> Prop) (b : real) (h1 : term273 _133668 x'') (h2 : term38) (h3 : term29 _133668 s) (h4 : term384 _133668 x) (h5 : term80 _133668 f s b) : term608 _133668 x s.
Proof. exact (@lem7142623 _133668 x f s b h5 (@lem7142613 _133668 x'' x f s b h1 h2 h3 h4 h5)). Qed.
Lemma lem7142627 {_133668 : Type'} (x'' : type645 _133668) (x : type684 _133668) (f : _133668 -> real) (s : _133668 -> Prop) (b : real) (h1 : term273 _133668 x'') (h2 : term38) (h3 : term29 _133668 s) (h4 : term384 _133668 x) (h5 : term80 _133668 f s b) : term722 _133668 x s.
Proof. exact (fun h0 : term413 _133668 x s => @lem7142626 _133668 x'' x f s b h1 h2 h3 h4 h5). Qed.
Lemma lem7142629 (p : Prop) : (term604 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7142630 {_133668 : Type'} (x : type684 _133668) (s : _133668 -> Prop) : (term722 _133668 x s) = (term608 _133668 x s).
Proof. exact (@lem7142629 (term413 _133668 x s)). Qed.
Lemma lem7142631 {_133668 : Type'} (x'' : type645 _133668) (x : type684 _133668) (f : _133668 -> real) (s : _133668 -> Prop) (b : real) (h1 : term273 _133668 x'') (h2 : term38) (h3 : term29 _133668 s) (h4 : term384 _133668 x) (h5 : term80 _133668 f s b) : term608 _133668 x s.
Proof. exact (EQ_MP (@lem7142630 _133668 x s) (@lem7142627 _133668 x'' x f s b h1 h2 h3 h4 h5)). Qed.
Lemma lem7142637 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7142638 {_133668 : Type'} (x : type684 _133668) (_95347 : _133668 -> Prop) : (term416 _133668 x _95347) = (term723 _133668 x _95347).
Proof. exact (@lem7142637 (_95347 = (@EMPTY _133668)) (term413 _133668 x _95347)). Qed.
Lemma lem7142646 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7142647 {_133668 : Type'} (x : type684 _133668) (_95347 : _133668 -> Prop) : (term724 _133668 x _95347) = (term725 _133668 x _95347).
Proof. exact (MK_COMB (@lem7142646) (@lem7142638 _133668 x _95347)). Qed.
Lemma lem7142655 {_133668 : Type'} (x : type684 _133668) (_95347 : _133668 -> Prop) : (term723 _133668 x _95347) = (term723 _133668 x _95347).
Proof. exact (eq_refl (term723 _133668 x _95347)). Qed.
Lemma lem7142656 {_133668 : Type'} (x : type684 _133668) (_95347 : _133668 -> Prop) : ((term416 _133668 x _95347) = (term723 _133668 x _95347)) = ((term723 _133668 x _95347) = (term723 _133668 x _95347)).
Proof. exact (MK_COMB (@lem7142647 _133668 x _95347) (@lem7142655 _133668 x _95347)). Qed.
Lemma lem7142658 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7142659 (x : Prop) : (x = x) = True.
Proof. exact (@lem7142658 Prop x). Qed.
Lemma lem7142660 {_133668 : Type'} (x : type684 _133668) (_95347 : _133668 -> Prop) : ((term723 _133668 x _95347) = (term723 _133668 x _95347)) = True.
Proof. exact (@lem7142659 (term723 _133668 x _95347)). Qed.
Lemma lem7142661 {_133668 : Type'} (x : type684 _133668) (_95347 : _133668 -> Prop) : ((term416 _133668 x _95347) = (term723 _133668 x _95347)) = True.
Proof. exact (TRANS (@lem7142656 _133668 x _95347) (@lem7142660 _133668 x _95347)). Qed.
Lemma lem7142662 {_133668 : Type'} (x : type684 _133668) (_95347 : _133668 -> Prop) : True = ((term416 _133668 x _95347) = (term723 _133668 x _95347)).
Proof. exact (SYM (@lem7142661 _133668 x _95347)). Qed.
Lemma lem7142663 {_133668 : Type'} (x : type684 _133668) (_95347 : _133668 -> Prop) : (term416 _133668 x _95347) = (term723 _133668 x _95347).
Proof. exact (EQ_MP (@lem7142662 _133668 x _95347) (@lem0)). Qed.
Lemma lem7142664 {_133668 : Type'} (_95347 : _133668 -> Prop) (x : type684 _133668) (h1 : term384 _133668 x) : term723 _133668 x _95347.
Proof. exact (EQ_MP (@lem7142663 _133668 x _95347) (@lem7141190 _133668 _95347 x h1)). Qed.
Lemma lem7142666 (b : Prop) (a : Prop) : (a \/ b) = (term605 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7142669 {_133668 : Type'} (x : type684 _133668) (_95347 : _133668 -> Prop) : (term723 _133668 x _95347) = (term726 _133668 x _95347).
Proof. exact (@lem7142666 (term413 _133668 x _95347) (_95347 = (@EMPTY _133668))). Qed.
Lemma lem7142672 {_133668 : Type'} (_95347 : _133668 -> Prop) (x : type684 _133668) (h1 : term384 _133668 x) : term726 _133668 x _95347.
Proof. exact (EQ_MP (@lem7142669 _133668 x _95347) (@lem7142664 _133668 _95347 x h1)). Qed.
Lemma lem7142673 {_133668 : Type'} (_95347 : _133668 -> Prop) (x : type684 _133668) (h1 : term384 _133668 x) : term726 _133668 x _95347.
Proof. exact (@lem7142672 _133668 _95347 x h1). Qed.
Lemma lem7142674 {_133668 : Type'} (s : _133668 -> Prop) (x : type684 _133668) (h1 : term384 _133668 x) : term726 _133668 x s.
Proof. exact (@lem7142673 _133668 s x h1). Qed.
Lemma lem7142677 {_133668 : Type'} (x'' : type645 _133668) (x : type684 _133668) (f : _133668 -> real) (s : _133668 -> Prop) (b : real) (h1 : term273 _133668 x'') (h2 : term38) (h3 : term29 _133668 s) (h4 : term384 _133668 x) (h5 : term80 _133668 f s b) : s = (@EMPTY _133668).
Proof. exact (@lem7142674 _133668 s x h4 (@lem7142631 _133668 x'' x f s b h1 h2 h3 h4 h5)). Qed.
Lemma lem7142678 {_133668 : Type'} (x'' : type645 _133668) (x : type684 _133668) (f : _133668 -> real) (s : _133668 -> Prop) (b : real) (h1 : term273 _133668 x'') (h2 : term38) (h3 : term384 _133668 x) (h4 : term80 _133668 f s b) : term727 _133668 s.
Proof. exact (fun h0 : term29 _133668 s => @lem7142677 _133668 x'' x f s b h1 h2 h0 h3 h4). Qed.
Lemma lem7142680 (p : Prop) : (term602 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7142681 {_133668 : Type'} (s : _133668 -> Prop) : (term727 _133668 s) = (s = (@EMPTY _133668)).
Proof. exact (@lem7142680 (s = (@EMPTY _133668))). Qed.
Lemma lem7142682 {_133668 : Type'} (x'' : type645 _133668) (x : type684 _133668) (f : _133668 -> real) (s : _133668 -> Prop) (b : real) (h1 : term273 _133668 x'') (h2 : term38) (h3 : term384 _133668 x) (h4 : term80 _133668 f s b) : s = (@EMPTY _133668).
Proof. exact (EQ_MP (@lem7142681 _133668 s) (@lem7142678 _133668 x'' x f s b h1 h2 h3 h4)). Qed.
Lemma lem7142685 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7142687 {_133668 : Type'} (s : _133668 -> Prop) : (term29 _133668 s) = (term728 _133668 s).
Proof. exact (@lem7142685 (s = (@EMPTY _133668))). Qed.
Lemma lem7142690 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) (h1 : term80 _133668 f s b) : term728 _133668 s.
Proof. exact (EQ_MP (@lem7142687 _133668 s) (@lem7141178 _133668 f s b h1)). Qed.
Lemma lem7142693 {_133668 : Type'} (x'' : type645 _133668) (x : type684 _133668) (f : _133668 -> real) (s : _133668 -> Prop) (b : real) (h1 : term273 _133668 x'') (h2 : term38) (h3 : term384 _133668 x) (h4 : term80 _133668 f s b) : False.
Proof. exact (@lem7142690 _133668 f s b h4 (@lem7142682 _133668 x'' x f s b h1 h2 h3 h4)). Qed.
Lemma lem7142694 {_133668 : Type'} (x'' : type645 _133668) (x : type684 _133668) (f : _133668 -> real) (s : _133668 -> Prop) (b : real) (h1 : term273 _133668 x'') (h2 : term38) (h3 : term384 _133668 x) (h4 : term80 _133668 f s b) : term729.
Proof. exact (fun h0 : ~ False => @lem7142693 _133668 x'' x f s b h1 h2 h3 h4). Qed.
Lemma lem7142696 (p : Prop) : (term602 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7142697 : term729 = False.
Proof. exact (@lem7142696 False). Qed.
Lemma lem7142698 {_133668 : Type'} (x'' : type645 _133668) (x : type684 _133668) (f : _133668 -> real) (s : _133668 -> Prop) (b : real) (h1 : term273 _133668 x'') (h2 : term38) (h3 : term384 _133668 x) (h4 : term80 _133668 f s b) : False.
Proof. exact (EQ_MP (@lem7142697) (@lem7142694 _133668 x'' x f s b h1 h2 h3 h4)). Qed.
Lemma lem7142699 {_133668 : Type'} (x'' : type645 _133668) (f : _133668 -> real) (s : _133668 -> Prop) (x : type684 _133668) (h1 : term273 _133668 x'') (h2 : term38) (h3 : term90 _133668 f s) (h4 : term384 _133668 x) : False.
Proof. exact (ex_elim (@lem7139997 _133668 f s h3) (fun b : real => fun h0 : term89 _133668 f s b => @lem7142698 _133668 x'' x f s b h1 h2 h4 h0)). Qed.
Lemma lem7142700 {_133668 : Type'} (x'' : type645 _133668) (s : _133668 -> Prop) (x : type684 _133668) (h1 : term273 _133668 x'') (h2 : term38) (h3 : term99 _133668 s) (h4 : term384 _133668 x) : False.
Proof. exact (ex_elim (@lem7139996 _133668 s h3) (fun f : _133668 -> real => fun h0 : term98 _133668 s f => @lem7142699 _133668 x'' f s x h1 h2 h0 h4)). Qed.
Lemma lem7142701 {_133668 : Type'} (x'' : type645 _133668) (x : type684 _133668) (h1 : term273 _133668 x'') (h2 : term38) (h3 : term10 _133668) (h4 : term384 _133668 x) : False.
Proof. exact (ex_elim (@lem7138880 _133668 h3) (fun s : _133668 -> Prop => fun h0 : term106 _133668 s => @lem7142700 _133668 x'' s x h1 h2 h0 h4)). Qed.
Lemma lem7142702 {_133668 : Type'} (x : type684 _133668) (h1 : term12 _133668) (h2 : term38) (h3 : term10 _133668) (h4 : term384 _133668 x) : False.
Proof. exact (ex_elim (@lem7139274 _133668 h1) (fun x'' : type645 _133668 => fun h0 : term275 _133668 x'' => @lem7142701 _133668 x'' x h0 h2 h3 h4)). Qed.
Lemma lem7142703 {_133668 A : Type'} (x : type684 _133668) (h1 : term12 _133668) (h2 : term12 A) (h3 : term38) (h4 : term10 _133668) (h5 : term384 _133668 x) : False.
Proof. exact (ex_elim (@lem7139668 A h2) (fun x' : type645 A => fun h0 : term275 A x' => @lem7142702 _133668 x h1 h3 h4 h5)). Qed.
Lemma lem7142704 {_133668 A : Type'} (h1 : term12 _133668) (h2 : term11 _133668) (h3 : term12 A) (h4 : term38) (h5 : term10 _133668) : False.
Proof. exact (ex_elim (@lem7139992 _133668 h2) (fun x : type684 _133668 => fun h0 : term386 _133668 x => @lem7142703 _133668 A x h1 h3 h4 h5 h0)). Qed.
Lemma lem7142705 {_133668 A : Type'} (h1 : term12 _133668) (h2 : term12 A) (h3 : term38) (h4 : term10 _133668) : term17 _133668.
Proof. exact (fun h0 : term11 _133668 => @lem7142704 _133668 A h1 h0 h2 h3 h4). Qed.
Lemma lem7142706 {_133668 : Type'} : (term17 _133668) = (term18 _133668).
Proof. exact (@lem69 (term11 _133668)). Qed.
Lemma lem7142707 {_133668 A : Type'} (h1 : term12 _133668) (h2 : term12 A) (h3 : term38) (h4 : term10 _133668) : term18 _133668.
Proof. exact (EQ_MP (@lem7142706 _133668) (@lem7142705 _133668 A h1 h2 h3 h4)). Qed.
Lemma lem7142708 {_133668 A : Type'} (h1 : term12 _133668) (h2 : term12 A) (h3 : term10 _133668) : term21 _133668.
Proof. exact (fun h0 : term38 => @lem7142707 _133668 A h1 h2 h0 h3). Qed.
Lemma lem7142709 {_133668 A : Type'} (h1 : term12 _133668) (h2 : term10 _133668) : term24 _133668 A.
Proof. exact (fun h0 : term12 A => @lem7142708 _133668 A h1 h0 h2). Qed.
Lemma lem7142710 {_133668 A : Type'} (h1 : term10 _133668) : term26 _133668 A.
Proof. exact (fun h0 : term12 _133668 => @lem7142709 _133668 A h0 h1). Qed.
Lemma lem7142711 {_133668 A : Type'} : term28 _133668 A.
Proof. exact (fun h0 : term10 _133668 => @lem7142710 _133668 A h0). Qed.
Lemma lem7142712 {_133668 A : Type'} : term13 _133668 A.
Proof. exact (EQ_MP (@lem7138712 _133668 A) (@lem7142711 _133668 A)). Qed.
Lemma lem7142714 {_133668 A : Type'} : term13 _133668 A.
Proof. exact (@lem7138198 _133668 A (@lem7142712 _133668 A)). Qed.
Lemma lem7142715 {_133668 A : Type'} (h1 : term10 _133668) : term25 _133668 A.
Proof. exact (@lem7142714 _133668 A (@lem7138175 _133668 h1)). Qed.
Lemma lem7142716 {_133668 A : Type'} (h1 : term10 _133668) : term23 _133668 A.
Proof. exact (@lem7142715 _133668 A h1 (@lem7138179 _133668)). Qed.
Lemma lem7142717 {_133668 : Type'} (h1 : term10 _133668) : term20 _133668.
Proof. exact (@lem7142716 _133668 Prop h1 (@lem7138160 Prop)). Qed.
Lemma lem7142718 {_133668 : Type'} (h1 : term10 _133668) : term17 _133668.
Proof. exact (@lem7142717 _133668 h1 (@lem1369133)). Qed.
Lemma lem7142719 {_133668 : Type'} (h1 : term10 _133668) : False.
Proof. exact (@lem7142718 _133668 h1 (@lem7138176 _133668)). Qed.
Lemma lem7142720 {_133668 : Type'} (h1 : term10 _133668) : (term10 _133668) = False.
Proof. exact (prop_ext (fun h2 : term10 _133668 => @lem7142719 _133668 h1) (fun h2 : False => @lem7138175 _133668 h1)). Qed.
Lemma lem7142721 {_133668 : Type'} (h1 : term10 _133668) : False.
Proof. exact (EQ_MP (@lem7142720 _133668 h1) (@lem7138175 _133668 h1)). Qed.
Lemma lem7142722 {_133668 : Type'} : term9 _133668.
Proof. exact (fun h0 : term10 _133668 => @lem7142721 _133668 h0). Qed.
Lemma lem7142723 {_133668 : Type'} : term8 _133668.
Proof. exact (EQ_MP (@lem7138174 _133668) (@lem7142722 _133668)). Qed.
