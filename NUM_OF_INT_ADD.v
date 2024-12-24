Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NUM_OF_INT_ADD_term_abbrevs.
Require Import INT_FORALL_POS_spec.
Require Import INT_OF_NUM_ADD_spec.
Require Import NUM_OF_INT_OF_NUM_spec.
Require Import RIGHT_FORALL_IMP_THM_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm885_spec.
Require Import thm886_spec.
Lemma lem2835225 (P : int -> Prop) (h1 : (term0 P) = (term1 P)) : (term0 P) = (term1 P).
Proof. exact (h1). Qed.
Lemma lem2835226 (P : int -> Prop) (h1 : (term0 P) = (term1 P)) : (term1 P) = (term0 P).
Proof. exact (SYM (@lem2835225 P h1)). Qed.
Lemma lem2835227 (P : int -> Prop) (h1 : (term1 P) = (term0 P)) : (term1 P) = (term0 P).
Proof. exact (h1). Qed.
Lemma lem2835228 (P : int -> Prop) (h1 : (term1 P) = (term0 P)) : (term0 P) = (term1 P).
Proof. exact (SYM (@lem2835227 P h1)). Qed.
Lemma lem2835229 (P : int -> Prop) : ((term0 P) = (term1 P)) = ((term1 P) = (term0 P)).
Proof. exact (prop_ext (fun h1 : (term0 P) = (term1 P) => @lem2835226 P h1) (fun h1 : (term1 P) = (term0 P) => @lem2835228 P h1)). Qed.
Lemma lem2835230 : term2 = term3.
Proof. exact (fun_ext (fun P : int -> Prop => @lem2835229 P)). Qed.
Lemma lem2835231 : (@all (int -> Prop)) = (@all (int -> Prop)).
Proof. exact (eq_refl (@all (int -> Prop))). Qed.
Lemma lem2835232 : term4 = term5.
Proof. exact (MK_COMB (@lem2835231) (@lem2835230)). Qed.
Lemma lem2835233 : term5.
Proof. exact (EQ_MP (@lem2835232) (@lem2315380)). Qed.
Lemma lem2835234 (n : nat) : term6 n.
Proof. exact (@lem2833991 n). Qed.
Lemma lem2835235 (n : nat) : (term6 n) = ((term7 n) = n).
Proof. exact (eq_refl (term6 n)). Qed.
Lemma lem2835237 (m : nat) : term8 m.
Proof. exact (@lem2306816 m). Qed.
Lemma lem2835238 (m : nat) : (term8 m) = (term9 m).
Proof. exact (eq_refl (term8 m)). Qed.
Lemma lem2835239 (m : nat) : term9 m.
Proof. exact (EQ_MP (@lem2835238 m) (@lem2835237 m)). Qed.
Lemma lem2835240 (m : nat) (n : nat) : term10 m n.
Proof. exact (@lem2835239 m n). Qed.
Lemma lem2835241 (m : nat) (n : nat) : (term10 m n) = ((term11 m n) = (term12 m n)).
Proof. exact (eq_refl (term10 m n)). Qed.
Lemma lem2835243 (P : int -> Prop) : term13 P.
Proof. exact (@lem2835233 P). Qed.
Lemma lem2835244 (P : int -> Prop) : (term13 P) = ((term1 P) = (term0 P)).
Proof. exact (eq_refl (term13 P)). Qed.
Lemma lem2835246 {A : Type'} (P : Prop) : term14 A P.
Proof. exact (@lem6534 A P). Qed.
Lemma lem2835247 {A : Type'} (P : Prop) : (term14 A P) = (term15 A P).
Proof. exact (eq_refl (term14 A P)). Qed.
Lemma lem2835248 {A : Type'} (P : Prop) : term15 A P.
Proof. exact (EQ_MP (@lem2835247 A P) (@lem2835246 A P)). Qed.
Lemma lem2835249 {A : Type'} (P : Prop) (Q : A -> Prop) : term16 A P Q.
Proof. exact (@lem2835248 A P Q). Qed.
Lemma lem2835250 {A : Type'} (P : Prop) (Q : A -> Prop) : (term16 A P Q) = ((term17 A P Q) = (term18 A P Q)).
Proof. exact (eq_refl (term16 A P Q)). Qed.
Lemma lem2835281 (p : Prop) (q : Prop) (r : Prop) : (term19 p q r) = (term20 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem2835282 (x : int) (y : int) : (term21 x y) = (term22 x y).
Proof. exact (@lem2835281 (term23 x) (term23 y) ((term24 x y) = (term25 x y))). Qed.
Lemma lem2835289 (x : int) : (term26 x) = (term27 x).
Proof. exact (fun_ext (fun y : int => @lem2835282 x y)). Qed.
Lemma lem2835290 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2835291 (x : int) : (term28 x) = (term29 x).
Proof. exact (MK_COMB (@lem2835290) (@lem2835289 x)). Qed.
Lemma lem2835293 {A : Type'} (P : Prop) (Q : A -> Prop) : (term17 A P Q) = (term18 A P Q).
Proof. exact (EQ_MP (@lem2835250 A P Q) (@lem2835249 A P Q)). Qed.
Lemma lem2835294 (P : Prop) (Q : int -> Prop) : (term30 P Q) = (term31 P Q).
Proof. exact (@lem2835293 int P Q). Qed.
Lemma lem2835295 (x : int) : (term32 x) = (term33 x).
Proof. exact (@lem2835294 (term23 x) (term34 x)). Qed.
Lemma lem2835296 (x : int) (y : int) : (term35 x y) = (term36 x y).
Proof. exact (eq_refl (term35 x y)). Qed.
Lemma lem2835297 (x : int) : (term37 x) = (term37 x).
Proof. exact (eq_refl (term37 x)). Qed.
Lemma lem2835298 (x : int) (y : int) : (term38 x y) = (term22 x y).
Proof. exact (MK_COMB (@lem2835297 x) (@lem2835296 x y)). Qed.
Lemma lem2835299 (x : int) : (term39 x) = (term27 x).
Proof. exact (fun_ext (fun y : int => @lem2835298 x y)). Qed.
Lemma lem2835300 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2835301 (x : int) : (term32 x) = (term29 x).
Proof. exact (MK_COMB (@lem2835300) (@lem2835299 x)). Qed.
Lemma lem2835302 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2835303 (x : int) : (term40 x) = (term41 x).
Proof. exact (MK_COMB (@lem2835302) (@lem2835301 x)). Qed.
Lemma lem2835304 (x : int) (y : int) : (term35 x y) = (term36 x y).
Proof. exact (eq_refl (term35 x y)). Qed.
Lemma lem2835305 (x : int) : (term42 x) = (term34 x).
Proof. exact (fun_ext (fun y : int => @lem2835304 x y)). Qed.
Lemma lem2835306 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2835307 (x : int) : (term43 x) = (term44 x).
Proof. exact (MK_COMB (@lem2835306) (@lem2835305 x)). Qed.
Lemma lem2835308 (x : int) : (term37 x) = (term37 x).
Proof. exact (eq_refl (term37 x)). Qed.
Lemma lem2835309 (x : int) : (term33 x) = (term45 x).
Proof. exact (MK_COMB (@lem2835308 x) (@lem2835307 x)). Qed.
Lemma lem2835310 (x : int) : ((term32 x) = (term33 x)) = ((term29 x) = (term45 x)).
Proof. exact (MK_COMB (@lem2835303 x) (@lem2835309 x)). Qed.
Lemma lem2835311 (x : int) : (term29 x) = (term45 x).
Proof. exact (EQ_MP (@lem2835310 x) (@lem2835295 x)). Qed.
Lemma lem2835342 (x : int) : (term28 x) = (term45 x).
Proof. exact (TRANS (@lem2835291 x) (@lem2835311 x)). Qed.
Lemma lem2835343 : term46 = term47.
Proof. exact (fun_ext (fun x : int => @lem2835342 x)). Qed.
Lemma lem2835344 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2835345 : term48 = term49.
Proof. exact (MK_COMB (@lem2835344) (@lem2835343)). Qed.
Lemma lem2835370 : term49 = term48.
Proof. exact (SYM (@lem2835345)). Qed.
Lemma lem2835372 (P : int -> Prop) : (term1 P) = (term0 P).
Proof. exact (EQ_MP (@lem2835244 P) (@lem2835243 P)). Qed.
Lemma lem2835373 : term50 = term51.
Proof. exact (@lem2835372 term52). Qed.
Lemma lem2835374 (x : int) : (term53 x) = (term44 x).
Proof. exact (eq_refl (term53 x)). Qed.
Lemma lem2835375 (x : int) : (term37 x) = (term37 x).
Proof. exact (eq_refl (term37 x)). Qed.
Lemma lem2835376 (x : int) : (term54 x) = (term45 x).
Proof. exact (MK_COMB (@lem2835375 x) (@lem2835374 x)). Qed.
Lemma lem2835377 : term55 = term47.
Proof. exact (fun_ext (fun x : int => @lem2835376 x)). Qed.
Lemma lem2835378 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2835379 : term50 = term49.
Proof. exact (MK_COMB (@lem2835378) (@lem2835377)). Qed.
Lemma lem2835380 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2835381 : term56 = term57.
Proof. exact (MK_COMB (@lem2835380) (@lem2835379)). Qed.
Lemma lem2835382 (n : nat) : (term58 n) = (term59 n).
Proof. exact (eq_refl (term58 n)). Qed.
Lemma lem2835383 : term60 = term61.
Proof. exact (fun_ext (fun n : nat => @lem2835382 n)). Qed.
Lemma lem2835384 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2835385 : term51 = term62.
Proof. exact (MK_COMB (@lem2835384) (@lem2835383)). Qed.
Lemma lem2835386 : (term50 = term51) = (term49 = term62).
Proof. exact (MK_COMB (@lem2835381) (@lem2835385)). Qed.
Lemma lem2835387 : term49 = term62.
Proof. exact (EQ_MP (@lem2835386) (@lem2835373)). Qed.
Lemma lem2835393 (P : int -> Prop) : (term1 P) = (term0 P).
Proof. exact (EQ_MP (@lem2835244 P) (@lem2835243 P)). Qed.
Lemma lem2835394 (n : nat) : (term63 n) = (term64 n).
Proof. exact (@lem2835393 (term65 n)). Qed.
Lemma lem2835395 (n : nat) (y : int) : (term66 n y) = ((term67 n y) = (term68 n y)).
Proof. exact (eq_refl (term66 n y)). Qed.
Lemma lem2835396 (y : int) : (term37 y) = (term37 y).
Proof. exact (eq_refl (term37 y)). Qed.
Lemma lem2835397 (n : nat) (y : int) : (term69 n y) = (term70 n y).
Proof. exact (MK_COMB (@lem2835396 y) (@lem2835395 n y)). Qed.
Lemma lem2835398 (n : nat) : (term71 n) = (term72 n).
Proof. exact (fun_ext (fun y : int => @lem2835397 n y)). Qed.
Lemma lem2835399 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2835400 (n : nat) : (term63 n) = (term59 n).
Proof. exact (MK_COMB (@lem2835399) (@lem2835398 n)). Qed.
Lemma lem2835401 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2835402 (n : nat) : (term73 n) = (term74 n).
Proof. exact (MK_COMB (@lem2835401) (@lem2835400 n)). Qed.
Lemma lem2835403 (n : nat) (n' : nat) : (term75 n n') = ((term76 n n') = (term77 n n')).
Proof. exact (eq_refl (term75 n n')). Qed.
Lemma lem2835404 (n : nat) : (term78 n) = (term79 n).
Proof. exact (fun_ext (fun n' : nat => @lem2835403 n n')). Qed.
Lemma lem2835405 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2835406 (n : nat) : (term64 n) = (term80 n).
Proof. exact (MK_COMB (@lem2835405) (@lem2835404 n)). Qed.
Lemma lem2835407 (n : nat) : ((term63 n) = (term64 n)) = ((term59 n) = (term80 n)).
Proof. exact (MK_COMB (@lem2835402 n) (@lem2835406 n)). Qed.
Lemma lem2835408 (n : nat) : (term59 n) = (term80 n).
Proof. exact (EQ_MP (@lem2835407 n) (@lem2835394 n)). Qed.
Lemma lem2835416 (m : nat) (n : nat) : (term11 m n) = (term12 m n).
Proof. exact (EQ_MP (@lem2835241 m n) (@lem2835240 m n)). Qed.
Lemma lem2835417 (n : nat) (n' : nat) : (term11 n n') = (term12 n n').
Proof. exact (@lem2835416 n n'). Qed.
Lemma lem2835418 : num_of_int = num_of_int.
Proof. exact (eq_refl num_of_int). Qed.
Lemma lem2835419 (n : nat) (n' : nat) : (term76 n n') = (term81 n n').
Proof. exact (MK_COMB (@lem2835418) (@lem2835417 n n')). Qed.
Lemma lem2835421 (n : nat) : (term7 n) = n.
Proof. exact (EQ_MP (@lem2835235 n) (@lem2835234 n)). Qed.
Lemma lem2835422 (n : nat) (n' : nat) : (term81 n n') = (Nat.add n n').
Proof. exact (@lem2835421 (Nat.add n n')). Qed.
Lemma lem2835423 (n : nat) (n' : nat) : (term76 n n') = (Nat.add n n').
Proof. exact (TRANS (@lem2835419 n n') (@lem2835422 n n')). Qed.
Lemma lem2835424 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem2835425 (n : nat) (n' : nat) : (term82 n n') = (term83 n n').
Proof. exact (MK_COMB (@lem2835424) (@lem2835423 n n')). Qed.
Lemma lem2835427 (n : nat) : (term7 n) = n.
Proof. exact (EQ_MP (@lem2835235 n) (@lem2835234 n)). Qed.
Lemma lem2835428 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem2835429 (n : nat) : (term84 n) = (Nat.add n).
Proof. exact (MK_COMB (@lem2835428) (@lem2835427 n)). Qed.
Lemma lem2835431 (n : nat) : (term7 n) = n.
Proof. exact (EQ_MP (@lem2835235 n) (@lem2835234 n)). Qed.
Lemma lem2835432 (n' : nat) : (term7 n') = n'.
Proof. exact (@lem2835431 n'). Qed.
Lemma lem2835433 (n : nat) (n' : nat) : (term77 n n') = (Nat.add n n').
Proof. exact (MK_COMB (@lem2835429 n) (@lem2835432 n')). Qed.
Lemma lem2835434 (n : nat) (n' : nat) : ((term76 n n') = (term77 n n')) = ((Nat.add n n') = (Nat.add n n')).
Proof. exact (MK_COMB (@lem2835425 n n') (@lem2835433 n n')). Qed.
Lemma lem2835436 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2835437 (x : nat) : (x = x) = True.
Proof. exact (@lem2835436 nat x). Qed.
Lemma lem2835438 (n : nat) (n' : nat) : ((Nat.add n n') = (Nat.add n n')) = True.
Proof. exact (@lem2835437 (Nat.add n n')). Qed.
Lemma lem2835439 (n : nat) (n' : nat) : ((term76 n n') = (term77 n n')) = True.
Proof. exact (TRANS (@lem2835434 n n') (@lem2835438 n n')). Qed.
Lemma lem2835440 (n : nat) : (term79 n) = term85.
Proof. exact (fun_ext (fun n' : nat => @lem2835439 n n')). Qed.
Lemma lem2835441 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2835442 (n : nat) : (term80 n) = term86.
Proof. exact (MK_COMB (@lem2835441) (@lem2835440 n)). Qed.
Lemma lem2835444 {A : Type'} (t : Prop) : (term87 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2835445 (t : Prop) : (term88 t) = t.
Proof. exact (@lem2835444 nat t). Qed.
Lemma lem2835446 : term86 = True.
Proof. exact (@lem2835445 True). Qed.
Lemma lem2835447 (n : nat) : (term80 n) = True.
Proof. exact (TRANS (@lem2835442 n) (@lem2835446)). Qed.
Lemma lem2835448 (n : nat) : (term59 n) = True.
Proof. exact (TRANS (@lem2835408 n) (@lem2835447 n)). Qed.
Lemma lem2835449 : term61 = term85.
Proof. exact (fun_ext (fun n : nat => @lem2835448 n)). Qed.
Lemma lem2835450 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2835451 : term62 = term86.
Proof. exact (MK_COMB (@lem2835450) (@lem2835449)). Qed.
Lemma lem2835453 {A : Type'} (t : Prop) : (term87 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2835454 (t : Prop) : (term88 t) = t.
Proof. exact (@lem2835453 nat t). Qed.
Lemma lem2835455 : term86 = True.
Proof. exact (@lem2835454 True). Qed.
Lemma lem2835456 : term62 = True.
Proof. exact (TRANS (@lem2835451) (@lem2835455)). Qed.
Lemma lem2835457 : term49 = True.
Proof. exact (TRANS (@lem2835387) (@lem2835456)). Qed.
Lemma lem2835458 : True = term49.
Proof. exact (SYM (@lem2835457)). Qed.
Lemma lem2835459 : term49.
Proof. exact (EQ_MP (@lem2835458) (@lem0)). Qed.
Lemma lem2835460 : term48.
Proof. exact (EQ_MP (@lem2835370) (@lem2835459)). Qed.
