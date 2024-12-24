Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import WF_REC_WF_term_abbrevs.
Require Import NOT_IMP_spec.
Require Import num_WOP_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm13473_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17500_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1823_spec.
Require Import thm1831_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19728_spec.
Require Import thm19732_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm310219_spec.
Require Import thm316636_spec.
Require Import thm51_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Require Import thm89994_spec.
Require Import thm9425_spec.
Lemma lem339326 {A : Type'} (f : A -> nat) (x : nat -> A) : term0 A f x.
Proof. exact (@lem116994 (term1 A f x)). Qed.
Lemma lem339327 {A : Type'} (f : A -> nat) (x : nat -> A) : (term0 A f x) = ((term2 A f x) = (term3 A f x)).
Proof. exact (eq_refl (term0 A f x)). Qed.
Lemma lem339328 {A : Type'} (f : A -> nat) (x : nat -> A) : (term2 A f x) = (term3 A f x).
Proof. exact (EQ_MP (@lem339327 A f x) (@lem339326 A f x)). Qed.
Lemma lem339329 : term4.
Proof. exact (proj2 (@lem89994)). Qed.
Lemma lem339330 (m : nat) : term5 m.
Proof. exact (@lem339329 m). Qed.
Lemma lem339331 (m : nat) : (term5 m) = (term6 m).
Proof. exact (eq_refl (term5 m)). Qed.
Lemma lem339332 (m : nat) : term6 m.
Proof. exact (EQ_MP (@lem339331 m) (@lem339330 m)). Qed.
Lemma lem339333 (m : nat) (n : nat) : term7 m n.
Proof. exact (@lem339332 m n). Qed.
Lemma lem339334 (m : nat) (n : nat) : (term7 m n) = ((term8 m n) = (term9 m n)).
Proof. exact (eq_refl (term7 m n)). Qed.
Lemma lem339350 (t1 : Prop) : term10 t1.
Proof. exact (@lem10299 t1). Qed.
Lemma lem339351 (t1 : Prop) : (term10 t1) = (term11 t1).
Proof. exact (eq_refl (term10 t1)). Qed.
Lemma lem339352 (t1 : Prop) : term11 t1.
Proof. exact (EQ_MP (@lem339351 t1) (@lem339350 t1)). Qed.
Lemma lem339353 (t1 : Prop) (t2 : Prop) : term12 t1 t2.
Proof. exact (@lem339352 t1 t2). Qed.
Lemma lem339354 (t1 : Prop) (t2 : Prop) : (term12 t1 t2) = ((term13 t1 t2) = (term14 t1 t2)).
Proof. exact (eq_refl (term12 t1 t2)). Qed.
Lemma lem339366 {A : Type'} (lt2 : type1402 A) (h1 : term15 A lt2) : term15 A lt2.
Proof. exact (h1). Qed.
Lemma lem339368 {A : Type'} (lt2 : type1402 A) : (@WF A lt2) = (term16 A lt2).
Proof. exact (EQ_MP (@lem310219 A lt2) (@lem316636 A lt2)). Qed.
Lemma lem339369 {A : Type'} (lt2 : type1402 A) : (@WF A lt2) = (term16 A lt2).
Proof. exact (@lem339368 A lt2). Qed.
Lemma lem339378 {A : Type'} (lt2 : type1402 A) : (term16 A lt2) = (@WF A lt2).
Proof. exact (SYM (@lem339369 A lt2)). Qed.
Lemma lem339379 {A : Type'} (lt2 : type1402 A) (h1 : term17 A lt2) : term17 A lt2.
Proof. exact (h1). Qed.
Lemma lem339380 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (h1 : term18 A lt2 x) : term18 A lt2 x.
Proof. exact (h1). Qed.
Lemma lem339381 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (h1 : term19 A lt2 x) : term19 A lt2 x.
Proof. exact (h1). Qed.
Lemma lem339382 (P : nat -> Prop) : (term20 P) = (ex P).
Proof. exact (@lem9425 nat P). Qed.
Lemma lem339383 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) : (term21 A lt2 x n) = (term22 A lt2 x n).
Proof. exact (@lem339382 (term23 A lt2 x n)). Qed.
Lemma lem339384 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) : (term21 A lt2 x n) = (term24 A lt2 x n).
Proof. exact (eq_refl (term21 A lt2 x n)). Qed.
Lemma lem339385 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem339386 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) : (term25 A lt2 x n) = (term26 A lt2 x n).
Proof. exact (MK_COMB (@lem339385) (@lem339384 A lt2 x n)). Qed.
Lemma lem339387 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) : (term22 A lt2 x n) = (term22 A lt2 x n).
Proof. exact (eq_refl (term22 A lt2 x n)). Qed.
Lemma lem339388 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) : ((term21 A lt2 x n) = (term22 A lt2 x n)) = ((term24 A lt2 x n) = (term22 A lt2 x n)).
Proof. exact (MK_COMB (@lem339386 A lt2 x n) (@lem339387 A lt2 x n)). Qed.
Lemma lem339389 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) : (term24 A lt2 x n) = (term22 A lt2 x n).
Proof. exact (EQ_MP (@lem339388 A lt2 x n) (@lem339383 A lt2 x n)). Qed.
Lemma lem339390 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : (term27 A lt2 x) = (term28 A lt2 x).
Proof. exact (fun_ext (fun n : nat => @lem339389 A lt2 x n)). Qed.
Lemma lem339391 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem339392 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : (term19 A lt2 x) = (term29 A lt2 x).
Proof. exact (MK_COMB (@lem339391) (@lem339390 A lt2 x)). Qed.
Lemma lem339393 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : (term29 A lt2 x) = (term19 A lt2 x).
Proof. exact (SYM (@lem339392 A lt2 x)). Qed.
Lemma lem339395 (p : Prop) : p = (term30 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem339396 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : (term29 A lt2 x) = (term31 A lt2 x).
Proof. exact (@lem339395 (term29 A lt2 x)). Qed.
Lemma lem339397 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : (term31 A lt2 x) = (term29 A lt2 x).
Proof. exact (SYM (@lem339396 A lt2 x)). Qed.
Lemma lem339398 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (h1 : term32 A lt2 x) : term32 A lt2 x.
Proof. exact (h1). Qed.
Lemma lem339401 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (h1 : term33 A lt2 x) : term33 A lt2 x.
Proof. exact (h1). Qed.
Lemma lem339402 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : term34 A lt2 x.
Proof. exact (fun h0 : term33 A lt2 x => @lem339401 A lt2 x h0). Qed.
Lemma lem339403 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (h1 : term34 A lt2 x) : term34 A lt2 x.
Proof. exact (h1). Qed.
Lemma lem339404 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (h1 : term33 A lt2 x) : term33 A lt2 x.
Proof. exact (h1). Qed.
Lemma lem339405 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (h1 : term33 A lt2 x) (h2 : term34 A lt2 x) : term33 A lt2 x.
Proof. exact (@lem339403 A lt2 x h2 (@lem339404 A lt2 x h1)). Qed.
Lemma lem339406 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (h1 : term33 A lt2 x) : term35 A lt2 x.
Proof. exact (fun h0 : term34 A lt2 x => @lem339405 A lt2 x h1 h0). Qed.
Lemma lem339407 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (h1 : term34 A lt2 x) : term34 A lt2 x.
Proof. exact (h1). Qed.
Lemma lem339408 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (h1 : term33 A lt2 x) (h2 : term34 A lt2 x) : term33 A lt2 x.
Proof. exact (@lem339406 A lt2 x h1 (@lem339407 A lt2 x h2)). Qed.
Lemma lem339409 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (h1 : term34 A lt2 x) : term34 A lt2 x.
Proof. exact (fun h0 : term33 A lt2 x => @lem339408 A lt2 x h0 h1). Qed.
Lemma lem339410 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : term36 A lt2 x.
Proof. exact (fun h0 : term34 A lt2 x => @lem339409 A lt2 x h0). Qed.
Lemma lem339413 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : term34 A lt2 x.
Proof. exact (@lem339410 A lt2 x (@lem339402 A lt2 x)). Qed.
Lemma lem339414 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : term34 A lt2 x.
Proof. exact (@lem339413 A lt2 x). Qed.
Lemma lem339466 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem339467 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : (term31 A lt2 x) = (term37 A lt2 x).
Proof. exact (@lem339466 (term32 A lt2 x)). Qed.
Lemma lem339469 (t : Prop) : (term38 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem339470 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : (term37 A lt2 x) = (term29 A lt2 x).
Proof. exact (@lem339469 (term29 A lt2 x)). Qed.
Lemma lem339475 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : (term31 A lt2 x) = (term29 A lt2 x).
Proof. exact (TRANS (@lem339467 A lt2 x) (@lem339470 A lt2 x)). Qed.
Lemma lem339480 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : (term39 A lt2 x) = (term39 A lt2 x).
Proof. exact (eq_refl (term39 A lt2 x)). Qed.
Lemma lem339481 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : (term40 A lt2 x) = (term41 A lt2 x).
Proof. exact (MK_COMB (@lem339480 A lt2 x) (@lem339475 A lt2 x)). Qed.
Lemma lem339484 {A : Type'} (lt2 : type1402 A) : (term42 A lt2) = (term42 A lt2).
Proof. exact (eq_refl (term42 A lt2)). Qed.
Lemma lem339485 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : (term33 A lt2 x) = (term43 A lt2 x).
Proof. exact (MK_COMB (@lem339484 A lt2) (@lem339481 A lt2 x)). Qed.
Lemma lem339488 {A : Type'} (x : nat -> A) : (term44 A x) = (term45 A x).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem339485 A lt2 x)). Qed.
Lemma lem339489 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem339490 {A : Type'} (x : nat -> A) : (term46 A x) = (term47 A x).
Proof. exact (MK_COMB (@lem339489 A) (@lem339488 A x)). Qed.
Lemma lem339495 {A : Type'} : (term48 A) = (term49 A).
Proof. exact (fun_ext (fun x : nat -> A => @lem339490 A x)). Qed.
Lemma lem339496 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem339505 {A : Type'} : (term50 A) = (term51 A).
Proof. exact (MK_COMB (@lem339496 A) (@lem339495 A)). Qed.
Lemma lem339506 {A : Type'} (lt2 : type1402 A) (m : nat) (x : nat -> A) (n : nat) : (term52 A lt2 m x n) = (term52 A lt2 m x n).
Proof. exact (eq_refl (term52 A lt2 m x n)). Qed.
Lemma lem339507 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) : (term23 A lt2 x n) = (term23 A lt2 x n).
Proof. exact (fun_ext (fun m : nat => @lem339506 A lt2 m x n)). Qed.
Lemma lem339508 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem339509 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) : (term22 A lt2 x n) = (term22 A lt2 x n).
Proof. exact (MK_COMB (@lem339508) (@lem339507 A lt2 x n)). Qed.
Lemma lem339510 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : (term28 A lt2 x) = (term28 A lt2 x).
Proof. exact (fun_ext (fun n : nat => @lem339509 A lt2 x n)). Qed.
Lemma lem339511 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem339512 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : (term29 A lt2 x) = (term29 A lt2 x).
Proof. exact (MK_COMB (@lem339511) (@lem339510 A lt2 x)). Qed.
Lemma lem339513 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) : (term53 A lt2 x n) = (term53 A lt2 x n).
Proof. exact (eq_refl (term53 A lt2 x n)). Qed.
Lemma lem339514 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : (term54 A lt2 x) = (term54 A lt2 x).
Proof. exact (fun_ext (fun n : nat => @lem339513 A lt2 x n)). Qed.
Lemma lem339515 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem339516 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : (term18 A lt2 x) = (term18 A lt2 x).
Proof. exact (MK_COMB (@lem339515) (@lem339514 A lt2 x)). Qed.
Lemma lem339517 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem339518 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : (term39 A lt2 x) = (term39 A lt2 x).
Proof. exact (MK_COMB (@lem339517) (@lem339516 A lt2 x)). Qed.
Lemma lem339519 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : (term41 A lt2 x) = (term41 A lt2 x).
Proof. exact (MK_COMB (@lem339518 A lt2 x) (@lem339512 A lt2 x)). Qed.
Lemma lem339520 {A : Type'} (H : type700 A) (f : A -> nat) (x : A) : ((f x) = (H f x)) = ((f x) = (H f x)).
Proof. exact (eq_refl ((f x) = (H f x))). Qed.
Lemma lem339521 {A : Type'} (H : type700 A) (f : A -> nat) : (term55 A H f) = (term55 A H f).
Proof. exact (fun_ext (fun x : A => @lem339520 A H f x)). Qed.
Lemma lem339522 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem339523 {A : Type'} (H : type700 A) (f : A -> nat) : (term56 A H f) = (term56 A H f).
Proof. exact (MK_COMB (@lem339522 A) (@lem339521 A H f)). Qed.
Lemma lem339524 {A : Type'} (H : type700 A) : (term57 A H) = (term57 A H).
Proof. exact (fun_ext (fun f : A -> nat => @lem339523 A H f)). Qed.
Lemma lem339525 {A : Type'} : (@ex (A -> nat)) = (@ex (A -> nat)).
Proof. exact (eq_refl (@ex (A -> nat))). Qed.
Lemma lem339526 {A : Type'} (H : type700 A) : (term58 A H) = (term58 A H).
Proof. exact (MK_COMB (@lem339525 A) (@lem339524 A H)). Qed.
Lemma lem339527 {A : Type'} (f : A -> nat) (H : type700 A) (g : A -> nat) (x : A) : ((H f x) = (H g x)) = ((H f x) = (H g x)).
Proof. exact (eq_refl ((H f x) = (H g x))). Qed.
Lemma lem339532 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> nat) (g : A -> nat) (z : A) : (term59 A lt2 x f g z) = (term59 A lt2 x f g z).
Proof. exact (eq_refl (term59 A lt2 x f g z)). Qed.
Lemma lem339533 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> nat) (g : A -> nat) : (term60 A lt2 x f g) = (term60 A lt2 x f g).
Proof. exact (fun_ext (fun z : A => @lem339532 A lt2 x f g z)). Qed.
Lemma lem339534 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem339535 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> nat) (g : A -> nat) : (term61 A lt2 x f g) = (term61 A lt2 x f g).
Proof. exact (MK_COMB (@lem339534 A) (@lem339533 A lt2 x f g)). Qed.
Lemma lem339536 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem339537 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> nat) (g : A -> nat) : (term62 A lt2 x f g) = (term62 A lt2 x f g).
Proof. exact (MK_COMB (@lem339536) (@lem339535 A lt2 x f g)). Qed.
Lemma lem339538 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) (g : A -> nat) (x : A) : (term63 A lt2 f H g x) = (term63 A lt2 f H g x).
Proof. exact (MK_COMB (@lem339537 A lt2 x f g) (@lem339527 A f H g x)). Qed.
Lemma lem339539 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) (g : A -> nat) : (term64 A lt2 f H g) = (term64 A lt2 f H g).
Proof. exact (fun_ext (fun x : A => @lem339538 A lt2 f H g x)). Qed.
Lemma lem339540 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem339541 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) (g : A -> nat) : (term65 A lt2 f H g) = (term65 A lt2 f H g).
Proof. exact (MK_COMB (@lem339540 A) (@lem339539 A lt2 f H g)). Qed.
Lemma lem339542 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) : (term66 A lt2 f H) = (term66 A lt2 f H).
Proof. exact (fun_ext (fun g : A -> nat => @lem339541 A lt2 f H g)). Qed.
Lemma lem339543 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem339544 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) : (term67 A lt2 f H) = (term67 A lt2 f H).
Proof. exact (MK_COMB (@lem339543 A) (@lem339542 A lt2 f H)). Qed.
Lemma lem339545 {A : Type'} (lt2 : type1402 A) (H : type700 A) : (term68 A lt2 H) = (term68 A lt2 H).
Proof. exact (fun_ext (fun f : A -> nat => @lem339544 A lt2 f H)). Qed.
Lemma lem339546 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem339547 {A : Type'} (lt2 : type1402 A) (H : type700 A) : (term69 A lt2 H) = (term69 A lt2 H).
Proof. exact (MK_COMB (@lem339546 A) (@lem339545 A lt2 H)). Qed.
Lemma lem339548 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem339549 {A : Type'} (lt2 : type1402 A) (H : type700 A) : (term70 A lt2 H) = (term70 A lt2 H).
Proof. exact (MK_COMB (@lem339548) (@lem339547 A lt2 H)). Qed.
Lemma lem339550 {A : Type'} (lt2 : type1402 A) (H : type700 A) : (term71 A lt2 H) = (term71 A lt2 H).
Proof. exact (MK_COMB (@lem339549 A lt2 H) (@lem339526 A H)). Qed.
Lemma lem339551 {A : Type'} (lt2 : type1402 A) : (term72 A lt2) = (term72 A lt2).
Proof. exact (fun_ext (fun H : type700 A => @lem339550 A lt2 H)). Qed.
Lemma lem339552 {A : Type'} : (@all ((A -> nat) -> A -> nat)) = (@all ((A -> nat) -> A -> nat)).
Proof. exact (eq_refl (@all ((A -> nat) -> A -> nat))). Qed.
Lemma lem339553 {A : Type'} (lt2 : type1402 A) : (term15 A lt2) = (term15 A lt2).
Proof. exact (MK_COMB (@lem339552 A) (@lem339551 A lt2)). Qed.
Lemma lem339554 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem339555 {A : Type'} (lt2 : type1402 A) : (term42 A lt2) = (term42 A lt2).
Proof. exact (MK_COMB (@lem339554) (@lem339553 A lt2)). Qed.
Lemma lem339556 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : (term43 A lt2 x) = (term43 A lt2 x).
Proof. exact (MK_COMB (@lem339555 A lt2) (@lem339519 A lt2 x)). Qed.
Lemma lem339557 {A : Type'} (x : nat -> A) : (term45 A x) = (term45 A x).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem339556 A lt2 x)). Qed.
Lemma lem339558 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem339559 {A : Type'} (x : nat -> A) : (term47 A x) = (term47 A x).
Proof. exact (MK_COMB (@lem339558 A) (@lem339557 A x)). Qed.
Lemma lem339560 {A : Type'} : (term49 A) = (term49 A).
Proof. exact (fun_ext (fun x : nat -> A => @lem339559 A x)). Qed.
Lemma lem339561 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem339562 {A : Type'} : (term51 A) = (term51 A).
Proof. exact (MK_COMB (@lem339561 A) (@lem339560 A)). Qed.
Lemma lem339647 {A : Type'} : (term50 A) = (term51 A).
Proof. exact (TRANS (@lem339505 A) (@lem339562 A)). Qed.
Lemma lem339648 {A : Type'} : (term51 A) = (term50 A).
Proof. exact (SYM (@lem339647 A)). Qed.
Lemma lem339649 {A : Type'} (lt2 : type1402 A) (h1 : term15 A lt2) : term15 A lt2.
Proof. exact (h1). Qed.
Lemma lem339650 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (h1 : term18 A lt2 x) : term18 A lt2 x.
Proof. exact (h1). Qed.
Lemma lem339652 (p : Prop) : p = (term30 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem339653 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) : (term22 A lt2 x n) = (term73 A lt2 x n).
Proof. exact (@lem339652 (term22 A lt2 x n)). Qed.
Lemma lem339654 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) : (term73 A lt2 x n) = (term22 A lt2 x n).
Proof. exact (SYM (@lem339653 A lt2 x n)). Qed.
Lemma lem339655 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) (h1 : term74 A lt2 x n) : term74 A lt2 x n.
Proof. exact (h1). Qed.
Lemma lem339662 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> nat) (g : A -> nat) (z : A) : (term59 A lt2 x f g z) = (term75 A lt2 x f g z).
Proof. exact (@lem17265 (lt2 z x) ((f z) = (g z))). Qed.
Lemma lem339663 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> nat) (g : A -> nat) : (term60 A lt2 x f g) = (term76 A lt2 x f g).
Proof. exact (fun_ext (fun z : A => @lem339662 A lt2 x f g z)). Qed.
Lemma lem339664 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem339665 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> nat) (g : A -> nat) : (term61 A lt2 x f g) = (term77 A lt2 x f g).
Proof. exact (MK_COMB (@lem339664 A) (@lem339663 A lt2 x f g)). Qed.
Lemma lem339666 {A : Type'} (f : A -> nat) (H : type700 A) (g : A -> nat) (x : A) : (term78 A f H g x) = (term78 A f H g x).
Proof. exact (eq_refl (term78 A f H g x)). Qed.
Lemma lem339667 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem339668 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> nat) (g : A -> nat) : (term79 A lt2 x f g) = (term80 A lt2 x f g).
Proof. exact (MK_COMB (@lem339667) (@lem339665 A lt2 x f g)). Qed.
Lemma lem339669 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) (g : A -> nat) (x : A) : (term81 A lt2 f H g x) = (term82 A lt2 f H g x).
Proof. exact (MK_COMB (@lem339668 A lt2 x f g) (@lem339666 A f H g x)). Qed.
Lemma lem339670 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) (g : A -> nat) (x : A) : (term83 A lt2 f H g x) = (term81 A lt2 f H g x).
Proof. exact (@lem17362 (term61 A lt2 x f g) ((H f x) = (H g x))). Qed.
Lemma lem339671 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) (g : A -> nat) (x : A) : (term83 A lt2 f H g x) = (term82 A lt2 f H g x).
Proof. exact (TRANS (@lem339670 A lt2 f H g x) (@lem339669 A lt2 f H g x)). Qed.
Lemma lem339672 {A : Type'} (P : A -> Prop) : (term84 A P) = (term85 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem339673 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) (g : A -> nat) : (term86 A lt2 f H g) = (term87 A lt2 f H g).
Proof. exact (@lem339672 A (term64 A lt2 f H g)). Qed.
Lemma lem339674 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) (g : A -> nat) (x : A) : (term88 A lt2 f H g x) = (term63 A lt2 f H g x).
Proof. exact (eq_refl (term88 A lt2 f H g x)). Qed.
Lemma lem339675 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem339676 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) (g : A -> nat) (x : A) : (term89 A lt2 f H g x) = (term83 A lt2 f H g x).
Proof. exact (MK_COMB (@lem339675) (@lem339674 A lt2 f H g x)). Qed.
Lemma lem339677 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) (g : A -> nat) (x : A) : (term89 A lt2 f H g x) = (term82 A lt2 f H g x).
Proof. exact (TRANS (@lem339676 A lt2 f H g x) (@lem339671 A lt2 f H g x)). Qed.
Lemma lem339678 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) (g : A -> nat) : (term90 A lt2 f H g) = (term91 A lt2 f H g).
Proof. exact (fun_ext (fun x : A => @lem339677 A lt2 f H g x)). Qed.
Lemma lem339679 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem339680 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) (g : A -> nat) : (term87 A lt2 f H g) = (term92 A lt2 f H g).
Proof. exact (MK_COMB (@lem339679 A) (@lem339678 A lt2 f H g)). Qed.
Lemma lem339681 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) (g : A -> nat) : (term86 A lt2 f H g) = (term92 A lt2 f H g).
Proof. exact (TRANS (@lem339673 A lt2 f H g) (@lem339680 A lt2 f H g)). Qed.
Lemma lem339682 {A : Type'} (P : type704 A) : (term93 A P) = (term94 A P).
Proof. exact (@lem18392 (A -> nat) P). Qed.
Lemma lem339683 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) : (term95 A lt2 f H) = (term96 A lt2 f H).
Proof. exact (@lem339682 A (term66 A lt2 f H)). Qed.
Lemma lem339684 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) (g : A -> nat) : (term97 A lt2 f H g) = (term65 A lt2 f H g).
Proof. exact (eq_refl (term97 A lt2 f H g)). Qed.
Lemma lem339685 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem339686 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) (g : A -> nat) : (term98 A lt2 f H g) = (term86 A lt2 f H g).
Proof. exact (MK_COMB (@lem339685) (@lem339684 A lt2 f H g)). Qed.
Lemma lem339687 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) (g : A -> nat) : (term98 A lt2 f H g) = (term92 A lt2 f H g).
Proof. exact (TRANS (@lem339686 A lt2 f H g) (@lem339681 A lt2 f H g)). Qed.
Lemma lem339688 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) : (term99 A lt2 f H) = (term100 A lt2 f H).
Proof. exact (fun_ext (fun g : A -> nat => @lem339687 A lt2 f H g)). Qed.
Lemma lem339689 {A : Type'} : (@ex (A -> nat)) = (@ex (A -> nat)).
Proof. exact (eq_refl (@ex (A -> nat))). Qed.
Lemma lem339690 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) : (term96 A lt2 f H) = (term101 A lt2 f H).
Proof. exact (MK_COMB (@lem339689 A) (@lem339688 A lt2 f H)). Qed.
Lemma lem339691 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) : (term95 A lt2 f H) = (term101 A lt2 f H).
Proof. exact (TRANS (@lem339683 A lt2 f H) (@lem339690 A lt2 f H)). Qed.
Lemma lem339692 {A : Type'} (P : type704 A) : (term93 A P) = (term94 A P).
Proof. exact (@lem18392 (A -> nat) P). Qed.
Lemma lem339693 {A : Type'} (lt2 : type1402 A) (H : type700 A) : (term102 A lt2 H) = (term103 A lt2 H).
Proof. exact (@lem339692 A (term68 A lt2 H)). Qed.
Lemma lem339694 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) : (term104 A lt2 H f) = (term67 A lt2 f H).
Proof. exact (eq_refl (term104 A lt2 H f)). Qed.
Lemma lem339695 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem339696 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) : (term105 A lt2 H f) = (term95 A lt2 f H).
Proof. exact (MK_COMB (@lem339695) (@lem339694 A lt2 f H)). Qed.
Lemma lem339697 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) : (term105 A lt2 H f) = (term101 A lt2 f H).
Proof. exact (TRANS (@lem339696 A lt2 f H) (@lem339691 A lt2 f H)). Qed.
Lemma lem339698 {A : Type'} (lt2 : type1402 A) (H : type700 A) : (term106 A lt2 H) = (term107 A lt2 H).
Proof. exact (fun_ext (fun f : A -> nat => @lem339697 A lt2 f H)). Qed.
Lemma lem339699 {A : Type'} : (@ex (A -> nat)) = (@ex (A -> nat)).
Proof. exact (eq_refl (@ex (A -> nat))). Qed.
Lemma lem339700 {A : Type'} (lt2 : type1402 A) (H : type700 A) : (term103 A lt2 H) = (term108 A lt2 H).
Proof. exact (MK_COMB (@lem339699 A) (@lem339698 A lt2 H)). Qed.
Lemma lem339701 {A : Type'} (lt2 : type1402 A) (H : type700 A) : (term102 A lt2 H) = (term108 A lt2 H).
Proof. exact (TRANS (@lem339693 A lt2 H) (@lem339700 A lt2 H)). Qed.
Lemma lem339702 {A : Type'} (H : type700 A) (f : A -> nat) (x : A) : ((f x) = (H f x)) = ((f x) = (H f x)).
Proof. exact (eq_refl ((f x) = (H f x))). Qed.
Lemma lem339703 {A : Type'} (H : type700 A) (f : A -> nat) : (term55 A H f) = (term55 A H f).
Proof. exact (fun_ext (fun x : A => @lem339702 A H f x)). Qed.
Lemma lem339704 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem339705 {A : Type'} (H : type700 A) (f : A -> nat) : (term56 A H f) = (term56 A H f).
Proof. exact (MK_COMB (@lem339704 A) (@lem339703 A H f)). Qed.
Lemma lem339706 {A : Type'} (H : type700 A) : (term57 A H) = (term57 A H).
Proof. exact (fun_ext (fun f : A -> nat => @lem339705 A H f)). Qed.
Lemma lem339707 {A : Type'} : (@ex (A -> nat)) = (@ex (A -> nat)).
Proof. exact (eq_refl (@ex (A -> nat))). Qed.
Lemma lem339708 {A : Type'} (H : type700 A) : (term58 A H) = (term58 A H).
Proof. exact (MK_COMB (@lem339707 A) (@lem339706 A H)). Qed.
Lemma lem339709 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem339710 {A : Type'} (lt2 : type1402 A) (H : type700 A) : (term109 A lt2 H) = (term110 A lt2 H).
Proof. exact (MK_COMB (@lem339709) (@lem339701 A lt2 H)). Qed.
Lemma lem339711 {A : Type'} (lt2 : type1402 A) (H : type700 A) : (term111 A lt2 H) = (term112 A lt2 H).
Proof. exact (MK_COMB (@lem339710 A lt2 H) (@lem339708 A H)). Qed.
Lemma lem339712 {A : Type'} (lt2 : type1402 A) (H : type700 A) : (term71 A lt2 H) = (term111 A lt2 H).
Proof. exact (@lem17265 (term69 A lt2 H) (term58 A H)). Qed.
Lemma lem339713 {A : Type'} (lt2 : type1402 A) (H : type700 A) : (term71 A lt2 H) = (term112 A lt2 H).
Proof. exact (TRANS (@lem339712 A lt2 H) (@lem339711 A lt2 H)). Qed.
Lemma lem339714 {A : Type'} (lt2 : type1402 A) : (term72 A lt2) = (term113 A lt2).
Proof. exact (fun_ext (fun H : type700 A => @lem339713 A lt2 H)). Qed.
Lemma lem339715 {A : Type'} : (@all ((A -> nat) -> A -> nat)) = (@all ((A -> nat) -> A -> nat)).
Proof. exact (eq_refl (@all ((A -> nat) -> A -> nat))). Qed.
Lemma lem339716 {A : Type'} (lt2 : type1402 A) : (term15 A lt2) = (term114 A lt2).
Proof. exact (MK_COMB (@lem339715 A) (@lem339714 A lt2)). Qed.
Lemma lem339879 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term115 A P Q) = (term116 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem339880 {A : Type'} (P : type704 A) (Q : type704 A) : (term117 A P Q) = (term118 A P Q).
Proof. exact (@lem339879 (A -> nat) P Q). Qed.
Lemma lem339881 {A : Type'} (lt2 : type1402 A) (H : type700 A) : (term119 A lt2 H) = (term120 A lt2 H).
Proof. exact (@lem339880 A (term107 A lt2 H) (term57 A H)). Qed.
Lemma lem339882 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) : (term121 A lt2 H f) = (term101 A lt2 f H).
Proof. exact (eq_refl (term121 A lt2 H f)). Qed.
Lemma lem339883 {A : Type'} (lt2 : type1402 A) (H : type700 A) : (term122 A lt2 H) = (term107 A lt2 H).
Proof. exact (fun_ext (fun f : A -> nat => @lem339882 A lt2 f H)). Qed.
Lemma lem339884 {A : Type'} : (@ex (A -> nat)) = (@ex (A -> nat)).
Proof. exact (eq_refl (@ex (A -> nat))). Qed.
Lemma lem339885 {A : Type'} (lt2 : type1402 A) (H : type700 A) : (term123 A lt2 H) = (term108 A lt2 H).
Proof. exact (MK_COMB (@lem339884 A) (@lem339883 A lt2 H)). Qed.
Lemma lem339886 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem339887 {A : Type'} (lt2 : type1402 A) (H : type700 A) : (term124 A lt2 H) = (term110 A lt2 H).
Proof. exact (MK_COMB (@lem339886) (@lem339885 A lt2 H)). Qed.
Lemma lem339888 {A : Type'} (H : type700 A) (f : A -> nat) : (term125 A H f) = (term56 A H f).
Proof. exact (eq_refl (term125 A H f)). Qed.
Lemma lem339889 {A : Type'} (H : type700 A) : (term126 A H) = (term57 A H).
Proof. exact (fun_ext (fun f : A -> nat => @lem339888 A H f)). Qed.
Lemma lem339890 {A : Type'} : (@ex (A -> nat)) = (@ex (A -> nat)).
Proof. exact (eq_refl (@ex (A -> nat))). Qed.
Lemma lem339891 {A : Type'} (H : type700 A) : (term127 A H) = (term58 A H).
Proof. exact (MK_COMB (@lem339890 A) (@lem339889 A H)). Qed.
Lemma lem339892 {A : Type'} (lt2 : type1402 A) (H : type700 A) : (term119 A lt2 H) = (term112 A lt2 H).
Proof. exact (MK_COMB (@lem339887 A lt2 H) (@lem339891 A H)). Qed.
Lemma lem339893 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem339894 {A : Type'} (lt2 : type1402 A) (H : type700 A) : (term128 A lt2 H) = (term129 A lt2 H).
Proof. exact (MK_COMB (@lem339893) (@lem339892 A lt2 H)). Qed.
Lemma lem339895 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) : (term121 A lt2 H f) = (term101 A lt2 f H).
Proof. exact (eq_refl (term121 A lt2 H f)). Qed.
Lemma lem339896 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem339897 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) : (term130 A lt2 H f) = (term131 A lt2 f H).
Proof. exact (MK_COMB (@lem339896) (@lem339895 A lt2 f H)). Qed.
Lemma lem339898 {A : Type'} (H : type700 A) (f : A -> nat) : (term125 A H f) = (term56 A H f).
Proof. exact (eq_refl (term125 A H f)). Qed.
Lemma lem339899 {A : Type'} (lt2 : type1402 A) (H : type700 A) (f : A -> nat) : (term132 A lt2 H f) = (term133 A lt2 H f).
Proof. exact (MK_COMB (@lem339897 A lt2 f H) (@lem339898 A H f)). Qed.
Lemma lem339900 {A : Type'} (lt2 : type1402 A) (H : type700 A) : (term134 A lt2 H) = (term135 A lt2 H).
Proof. exact (fun_ext (fun f : A -> nat => @lem339899 A lt2 H f)). Qed.
Lemma lem339901 {A : Type'} : (@ex (A -> nat)) = (@ex (A -> nat)).
Proof. exact (eq_refl (@ex (A -> nat))). Qed.
Lemma lem339902 {A : Type'} (lt2 : type1402 A) (H : type700 A) : (term120 A lt2 H) = (term136 A lt2 H).
Proof. exact (MK_COMB (@lem339901 A) (@lem339900 A lt2 H)). Qed.
Lemma lem339903 {A : Type'} (lt2 : type1402 A) (H : type700 A) : ((term119 A lt2 H) = (term120 A lt2 H)) = ((term112 A lt2 H) = (term136 A lt2 H)).
Proof. exact (MK_COMB (@lem339894 A lt2 H) (@lem339902 A lt2 H)). Qed.
Lemma lem339904 {A : Type'} (lt2 : type1402 A) (H : type700 A) : (term112 A lt2 H) = (term136 A lt2 H).
Proof. exact (EQ_MP (@lem339903 A lt2 H) (@lem339881 A lt2 H)). Qed.
Lemma lem339906 {A : Type'} (P : A -> Prop) (Q : Prop) : (term137 A P Q) = (term138 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem339907 {A : Type'} (P : type704 A) (Q : Prop) : (term139 A P Q) = (term140 A P Q).
Proof. exact (@lem339906 (A -> nat) P Q). Qed.
Lemma lem339908 {A : Type'} (lt2 : type1402 A) (H : type700 A) (f : A -> nat) : (term141 A lt2 H f) = (term142 A lt2 H f).
Proof. exact (@lem339907 A (term100 A lt2 f H) (term56 A H f)). Qed.
Lemma lem339909 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) (g : A -> nat) : (term143 A lt2 f H g) = (term92 A lt2 f H g).
Proof. exact (eq_refl (term143 A lt2 f H g)). Qed.
Lemma lem339910 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) : (term144 A lt2 f H) = (term100 A lt2 f H).
Proof. exact (fun_ext (fun g : A -> nat => @lem339909 A lt2 f H g)). Qed.
Lemma lem339911 {A : Type'} : (@ex (A -> nat)) = (@ex (A -> nat)).
Proof. exact (eq_refl (@ex (A -> nat))). Qed.
Lemma lem339912 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) : (term145 A lt2 f H) = (term101 A lt2 f H).
Proof. exact (MK_COMB (@lem339911 A) (@lem339910 A lt2 f H)). Qed.
Lemma lem339913 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem339914 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) : (term146 A lt2 f H) = (term131 A lt2 f H).
Proof. exact (MK_COMB (@lem339913) (@lem339912 A lt2 f H)). Qed.
Lemma lem339915 {A : Type'} (H : type700 A) (f : A -> nat) : (term56 A H f) = (term56 A H f).
Proof. exact (eq_refl (term56 A H f)). Qed.
Lemma lem339916 {A : Type'} (lt2 : type1402 A) (H : type700 A) (f : A -> nat) : (term141 A lt2 H f) = (term133 A lt2 H f).
Proof. exact (MK_COMB (@lem339914 A lt2 f H) (@lem339915 A H f)). Qed.
Lemma lem339917 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem339918 {A : Type'} (lt2 : type1402 A) (H : type700 A) (f : A -> nat) : (term147 A lt2 H f) = (term148 A lt2 H f).
Proof. exact (MK_COMB (@lem339917) (@lem339916 A lt2 H f)). Qed.
Lemma lem339919 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) (g : A -> nat) : (term143 A lt2 f H g) = (term92 A lt2 f H g).
Proof. exact (eq_refl (term143 A lt2 f H g)). Qed.
Lemma lem339920 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem339921 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) (g : A -> nat) : (term149 A lt2 f H g) = (term150 A lt2 f H g).
Proof. exact (MK_COMB (@lem339920) (@lem339919 A lt2 f H g)). Qed.
Lemma lem339922 {A : Type'} (H : type700 A) (f : A -> nat) : (term56 A H f) = (term56 A H f).
Proof. exact (eq_refl (term56 A H f)). Qed.
Lemma lem339923 {A : Type'} (lt2 : type1402 A) (g : A -> nat) (H : type700 A) (f : A -> nat) : (term151 A lt2 g H f) = (term152 A lt2 g H f).
Proof. exact (MK_COMB (@lem339921 A lt2 f H g) (@lem339922 A H f)). Qed.
Lemma lem339924 {A : Type'} (lt2 : type1402 A) (H : type700 A) (f : A -> nat) : (term153 A lt2 H f) = (term154 A lt2 H f).
Proof. exact (fun_ext (fun g : A -> nat => @lem339923 A lt2 g H f)). Qed.
Lemma lem339925 {A : Type'} : (@ex (A -> nat)) = (@ex (A -> nat)).
Proof. exact (eq_refl (@ex (A -> nat))). Qed.
Lemma lem339926 {A : Type'} (lt2 : type1402 A) (H : type700 A) (f : A -> nat) : (term142 A lt2 H f) = (term155 A lt2 H f).
Proof. exact (MK_COMB (@lem339925 A) (@lem339924 A lt2 H f)). Qed.
Lemma lem339927 {A : Type'} (lt2 : type1402 A) (H : type700 A) (f : A -> nat) : ((term141 A lt2 H f) = (term142 A lt2 H f)) = ((term133 A lt2 H f) = (term155 A lt2 H f)).
Proof. exact (MK_COMB (@lem339918 A lt2 H f) (@lem339926 A lt2 H f)). Qed.
Lemma lem339928 {A : Type'} (lt2 : type1402 A) (H : type700 A) (f : A -> nat) : (term133 A lt2 H f) = (term155 A lt2 H f).
Proof. exact (EQ_MP (@lem339927 A lt2 H f) (@lem339908 A lt2 H f)). Qed.
Lemma lem339930 {A : Type'} (P : A -> Prop) (Q : Prop) : (term137 A P Q) = (term138 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem339931 {A : Type'} (P : A -> Prop) (Q : Prop) : (term137 A P Q) = (term138 A P Q).
Proof. exact (@lem339930 A P Q). Qed.
Lemma lem339932 {A : Type'} (lt2 : type1402 A) (g : A -> nat) (H : type700 A) (f : A -> nat) : (term156 A lt2 g H f) = (term157 A lt2 g H f).
Proof. exact (@lem339931 A (term91 A lt2 f H g) (term56 A H f)). Qed.
Lemma lem339933 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) (g : A -> nat) (x : A) : (term158 A lt2 f H g x) = (term82 A lt2 f H g x).
Proof. exact (eq_refl (term158 A lt2 f H g x)). Qed.
Lemma lem339934 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) (g : A -> nat) : (term159 A lt2 f H g) = (term91 A lt2 f H g).
Proof. exact (fun_ext (fun x : A => @lem339933 A lt2 f H g x)). Qed.
Lemma lem339935 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem339936 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) (g : A -> nat) : (term160 A lt2 f H g) = (term92 A lt2 f H g).
Proof. exact (MK_COMB (@lem339935 A) (@lem339934 A lt2 f H g)). Qed.
Lemma lem339937 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem339938 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) (g : A -> nat) : (term161 A lt2 f H g) = (term150 A lt2 f H g).
Proof. exact (MK_COMB (@lem339937) (@lem339936 A lt2 f H g)). Qed.
Lemma lem339939 {A : Type'} (H : type700 A) (f : A -> nat) : (term56 A H f) = (term56 A H f).
Proof. exact (eq_refl (term56 A H f)). Qed.
Lemma lem339940 {A : Type'} (lt2 : type1402 A) (g : A -> nat) (H : type700 A) (f : A -> nat) : (term156 A lt2 g H f) = (term152 A lt2 g H f).
Proof. exact (MK_COMB (@lem339938 A lt2 f H g) (@lem339939 A H f)). Qed.
Lemma lem339941 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem339942 {A : Type'} (lt2 : type1402 A) (g : A -> nat) (H : type700 A) (f : A -> nat) : (term162 A lt2 g H f) = (term163 A lt2 g H f).
Proof. exact (MK_COMB (@lem339941) (@lem339940 A lt2 g H f)). Qed.
Lemma lem339943 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) (g : A -> nat) (x : A) : (term158 A lt2 f H g x) = (term82 A lt2 f H g x).
Proof. exact (eq_refl (term158 A lt2 f H g x)). Qed.
Lemma lem339944 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem339945 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) (g : A -> nat) (x : A) : (term164 A lt2 f H g x) = (term165 A lt2 f H g x).
Proof. exact (MK_COMB (@lem339944) (@lem339943 A lt2 f H g x)). Qed.
Lemma lem339946 {A : Type'} (H : type700 A) (f : A -> nat) : (term56 A H f) = (term56 A H f).
Proof. exact (eq_refl (term56 A H f)). Qed.
Lemma lem339947 {A : Type'} (lt2 : type1402 A) (g : A -> nat) (x : A) (H : type700 A) (f : A -> nat) : (term166 A lt2 g x H f) = (term167 A lt2 g x H f).
Proof. exact (MK_COMB (@lem339945 A lt2 f H g x) (@lem339946 A H f)). Qed.
Lemma lem339948 {A : Type'} (lt2 : type1402 A) (g : A -> nat) (H : type700 A) (f : A -> nat) : (term168 A lt2 g H f) = (term169 A lt2 g H f).
Proof. exact (fun_ext (fun x : A => @lem339947 A lt2 g x H f)). Qed.
Lemma lem339949 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem339950 {A : Type'} (lt2 : type1402 A) (g : A -> nat) (H : type700 A) (f : A -> nat) : (term157 A lt2 g H f) = (term170 A lt2 g H f).
Proof. exact (MK_COMB (@lem339949 A) (@lem339948 A lt2 g H f)). Qed.
Lemma lem339951 {A : Type'} (lt2 : type1402 A) (g : A -> nat) (H : type700 A) (f : A -> nat) : ((term156 A lt2 g H f) = (term157 A lt2 g H f)) = ((term152 A lt2 g H f) = (term170 A lt2 g H f)).
Proof. exact (MK_COMB (@lem339942 A lt2 g H f) (@lem339950 A lt2 g H f)). Qed.
Lemma lem339952 {A : Type'} (lt2 : type1402 A) (g : A -> nat) (H : type700 A) (f : A -> nat) : (term152 A lt2 g H f) = (term170 A lt2 g H f).
Proof. exact (EQ_MP (@lem339951 A lt2 g H f) (@lem339932 A lt2 g H f)). Qed.
Lemma lem339953 {A : Type'} (lt2 : type1402 A) (H : type700 A) (f : A -> nat) : (term154 A lt2 H f) = (term171 A lt2 H f).
Proof. exact (fun_ext (fun g : A -> nat => @lem339952 A lt2 g H f)). Qed.
Lemma lem339954 {A : Type'} : (@ex (A -> nat)) = (@ex (A -> nat)).
Proof. exact (eq_refl (@ex (A -> nat))). Qed.
Lemma lem339955 {A : Type'} (lt2 : type1402 A) (H : type700 A) (f : A -> nat) : (term155 A lt2 H f) = (term172 A lt2 H f).
Proof. exact (MK_COMB (@lem339954 A) (@lem339953 A lt2 H f)). Qed.
Lemma lem339956 {A : Type'} (lt2 : type1402 A) (H : type700 A) (f : A -> nat) : (term133 A lt2 H f) = (term172 A lt2 H f).
Proof. exact (TRANS (@lem339928 A lt2 H f) (@lem339955 A lt2 H f)). Qed.
Lemma lem339957 {A : Type'} (lt2 : type1402 A) (H : type700 A) : (term135 A lt2 H) = (term173 A lt2 H).
Proof. exact (fun_ext (fun f : A -> nat => @lem339956 A lt2 H f)). Qed.
Lemma lem339958 {A : Type'} : (@ex (A -> nat)) = (@ex (A -> nat)).
Proof. exact (eq_refl (@ex (A -> nat))). Qed.
Lemma lem339959 {A : Type'} (lt2 : type1402 A) (H : type700 A) : (term136 A lt2 H) = (term174 A lt2 H).
Proof. exact (MK_COMB (@lem339958 A) (@lem339957 A lt2 H)). Qed.
Lemma lem339960 {A : Type'} (lt2 : type1402 A) (H : type700 A) : (term112 A lt2 H) = (term174 A lt2 H).
Proof. exact (TRANS (@lem339904 A lt2 H) (@lem339959 A lt2 H)). Qed.
Lemma lem339961 {A : Type'} (lt2 : type1402 A) : (term113 A lt2) = (term175 A lt2).
Proof. exact (fun_ext (fun H : type700 A => @lem339960 A lt2 H)). Qed.
Lemma lem339962 {A : Type'} : (@all ((A -> nat) -> A -> nat)) = (@all ((A -> nat) -> A -> nat)).
Proof. exact (eq_refl (@all ((A -> nat) -> A -> nat))). Qed.
Lemma lem339963 {A : Type'} (lt2 : type1402 A) : (term114 A lt2) = (term176 A lt2).
Proof. exact (MK_COMB (@lem339962 A) (@lem339961 A lt2)). Qed.
Lemma lem339965 {A B : Type'} (P : type1413 A B) : (term177 A B P) = (term178 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem339966 {A : Type'} (P : type182 A) : (term179 A P) = (term180 A P).
Proof. exact (@lem339965 (type700 A) (A -> nat) P). Qed.
Lemma lem339967 {A : Type'} (lt2 : type1402 A) : (term181 A lt2) = (term182 A lt2).
Proof. exact (@lem339966 A (term183 A lt2)). Qed.
Lemma lem339968 {A : Type'} (lt2 : type1402 A) (H : type700 A) : (term184 A lt2 H) = (term173 A lt2 H).
Proof. exact (eq_refl (term184 A lt2 H)). Qed.
Lemma lem339969 {A : Type'} (f : A -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem339970 {A : Type'} (lt2 : type1402 A) (H : type700 A) (f : A -> nat) : (term185 A lt2 H f) = (term186 A lt2 H f).
Proof. exact (MK_COMB (@lem339968 A lt2 H) (@lem339969 A f)). Qed.
Lemma lem339971 {A : Type'} (lt2 : type1402 A) (H : type700 A) (f : A -> nat) : (term186 A lt2 H f) = (term172 A lt2 H f).
Proof. exact (eq_refl (term186 A lt2 H f)). Qed.
Lemma lem339972 {A : Type'} (lt2 : type1402 A) (H : type700 A) (f : A -> nat) : (term185 A lt2 H f) = (term172 A lt2 H f).
Proof. exact (TRANS (@lem339970 A lt2 H f) (@lem339971 A lt2 H f)). Qed.
Lemma lem339973 {A : Type'} (lt2 : type1402 A) (H : type700 A) : (term187 A lt2 H) = (term173 A lt2 H).
Proof. exact (fun_ext (fun f : A -> nat => @lem339972 A lt2 H f)). Qed.
Lemma lem339974 {A : Type'} : (@ex (A -> nat)) = (@ex (A -> nat)).
Proof. exact (eq_refl (@ex (A -> nat))). Qed.
Lemma lem339975 {A : Type'} (lt2 : type1402 A) (H : type700 A) : (term188 A lt2 H) = (term174 A lt2 H).
Proof. exact (MK_COMB (@lem339974 A) (@lem339973 A lt2 H)). Qed.
Lemma lem339976 {A : Type'} (lt2 : type1402 A) : (term189 A lt2) = (term175 A lt2).
Proof. exact (fun_ext (fun H : type700 A => @lem339975 A lt2 H)). Qed.
Lemma lem339977 {A : Type'} : (@all ((A -> nat) -> A -> nat)) = (@all ((A -> nat) -> A -> nat)).
Proof. exact (eq_refl (@all ((A -> nat) -> A -> nat))). Qed.
Lemma lem339978 {A : Type'} (lt2 : type1402 A) : (term181 A lt2) = (term176 A lt2).
Proof. exact (MK_COMB (@lem339977 A) (@lem339976 A lt2)). Qed.
Lemma lem339979 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem339980 {A : Type'} (lt2 : type1402 A) : (term190 A lt2) = (term191 A lt2).
Proof. exact (MK_COMB (@lem339979) (@lem339978 A lt2)). Qed.
Lemma lem339981 {A : Type'} (lt2 : type1402 A) (H : type700 A) : (term184 A lt2 H) = (term173 A lt2 H).
Proof. exact (eq_refl (term184 A lt2 H)). Qed.
Lemma lem339982 {A : Type'} (f : type184 A) (H : type700 A) : (f H) = (f H).
Proof. exact (eq_refl (f H)). Qed.
Lemma lem339983 {A : Type'} (lt2 : type1402 A) (f : type184 A) (H : type700 A) : (term192 A lt2 f H) = (term193 A lt2 f H).
Proof. exact (MK_COMB (@lem339981 A lt2 H) (@lem339982 A f H)). Qed.
Lemma lem339984 {A : Type'} (lt2 : type1402 A) (f : type184 A) (H : type700 A) : (term193 A lt2 f H) = (term194 A lt2 f H).
Proof. exact (eq_refl (term193 A lt2 f H)). Qed.
Lemma lem339985 {A : Type'} (lt2 : type1402 A) (f : type184 A) (H : type700 A) : (term192 A lt2 f H) = (term194 A lt2 f H).
Proof. exact (TRANS (@lem339983 A lt2 f H) (@lem339984 A lt2 f H)). Qed.
Lemma lem339986 {A : Type'} (lt2 : type1402 A) (f : type184 A) : (term195 A lt2 f) = (term196 A lt2 f).
Proof. exact (fun_ext (fun H : type700 A => @lem339985 A lt2 f H)). Qed.
Lemma lem339987 {A : Type'} : (@all ((A -> nat) -> A -> nat)) = (@all ((A -> nat) -> A -> nat)).
Proof. exact (eq_refl (@all ((A -> nat) -> A -> nat))). Qed.
Lemma lem339988 {A : Type'} (lt2 : type1402 A) (f : type184 A) : (term197 A lt2 f) = (term198 A lt2 f).
Proof. exact (MK_COMB (@lem339987 A) (@lem339986 A lt2 f)). Qed.
Lemma lem339989 {A : Type'} (lt2 : type1402 A) : (term199 A lt2) = (term200 A lt2).
Proof. exact (fun_ext (fun f : type184 A => @lem339988 A lt2 f)). Qed.
Lemma lem339990 {A : Type'} : (@ex (((A -> nat) -> A -> nat) -> A -> nat)) = (@ex (((A -> nat) -> A -> nat) -> A -> nat)).
Proof. exact (eq_refl (@ex (((A -> nat) -> A -> nat) -> A -> nat))). Qed.
Lemma lem339991 {A : Type'} (lt2 : type1402 A) : (term182 A lt2) = (term201 A lt2).
Proof. exact (MK_COMB (@lem339990 A) (@lem339989 A lt2)). Qed.
Lemma lem339992 {A : Type'} (lt2 : type1402 A) : ((term181 A lt2) = (term182 A lt2)) = ((term176 A lt2) = (term201 A lt2)).
Proof. exact (MK_COMB (@lem339980 A lt2) (@lem339991 A lt2)). Qed.
Lemma lem339993 {A : Type'} (lt2 : type1402 A) : (term176 A lt2) = (term201 A lt2).
Proof. exact (EQ_MP (@lem339992 A lt2) (@lem339967 A lt2)). Qed.
Lemma lem339995 {A B : Type'} (P : type1413 A B) : (term177 A B P) = (term178 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem339996 {A : Type'} (P : type182 A) : (term179 A P) = (term180 A P).
Proof. exact (@lem339995 (type700 A) (A -> nat) P). Qed.
Lemma lem339997 {A : Type'} (lt2 : type1402 A) (f : type184 A) : (term202 A lt2 f) = (term203 A lt2 f).
Proof. exact (@lem339996 A (term204 A lt2 f)). Qed.
Lemma lem339998 {A : Type'} (lt2 : type1402 A) (f : type184 A) (H : type700 A) : (term205 A lt2 f H) = (term206 A lt2 f H).
Proof. exact (eq_refl (term205 A lt2 f H)). Qed.
Lemma lem339999 {A : Type'} (g : A -> nat) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem340000 {A : Type'} (lt2 : type1402 A) (f : type184 A) (H : type700 A) (g : A -> nat) : (term207 A lt2 f H g) = (term208 A lt2 f H g).
Proof. exact (MK_COMB (@lem339998 A lt2 f H) (@lem339999 A g)). Qed.
Lemma lem340001 {A : Type'} (lt2 : type1402 A) (g : A -> nat) (f : type184 A) (H : type700 A) : (term208 A lt2 f H g) = (term209 A lt2 g f H).
Proof. exact (eq_refl (term208 A lt2 f H g)). Qed.
Lemma lem340002 {A : Type'} (lt2 : type1402 A) (g : A -> nat) (f : type184 A) (H : type700 A) : (term207 A lt2 f H g) = (term209 A lt2 g f H).
Proof. exact (TRANS (@lem340000 A lt2 f H g) (@lem340001 A lt2 g f H)). Qed.
Lemma lem340003 {A : Type'} (lt2 : type1402 A) (f : type184 A) (H : type700 A) : (term210 A lt2 f H) = (term206 A lt2 f H).
Proof. exact (fun_ext (fun g : A -> nat => @lem340002 A lt2 g f H)). Qed.
Lemma lem340004 {A : Type'} : (@ex (A -> nat)) = (@ex (A -> nat)).
Proof. exact (eq_refl (@ex (A -> nat))). Qed.
Lemma lem340005 {A : Type'} (lt2 : type1402 A) (f : type184 A) (H : type700 A) : (term211 A lt2 f H) = (term194 A lt2 f H).
Proof. exact (MK_COMB (@lem340004 A) (@lem340003 A lt2 f H)). Qed.
Lemma lem340006 {A : Type'} (lt2 : type1402 A) (f : type184 A) : (term212 A lt2 f) = (term196 A lt2 f).
Proof. exact (fun_ext (fun H : type700 A => @lem340005 A lt2 f H)). Qed.
Lemma lem340007 {A : Type'} : (@all ((A -> nat) -> A -> nat)) = (@all ((A -> nat) -> A -> nat)).
Proof. exact (eq_refl (@all ((A -> nat) -> A -> nat))). Qed.
Lemma lem340008 {A : Type'} (lt2 : type1402 A) (f : type184 A) : (term202 A lt2 f) = (term198 A lt2 f).
Proof. exact (MK_COMB (@lem340007 A) (@lem340006 A lt2 f)). Qed.
Lemma lem340009 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem340010 {A : Type'} (lt2 : type1402 A) (f : type184 A) : (term213 A lt2 f) = (term214 A lt2 f).
Proof. exact (MK_COMB (@lem340009) (@lem340008 A lt2 f)). Qed.
Lemma lem340011 {A : Type'} (lt2 : type1402 A) (f : type184 A) (H : type700 A) : (term205 A lt2 f H) = (term206 A lt2 f H).
Proof. exact (eq_refl (term205 A lt2 f H)). Qed.
Lemma lem340012 {A : Type'} (g : type184 A) (H : type700 A) : (g H) = (g H).
Proof. exact (eq_refl (g H)). Qed.
Lemma lem340013 {A : Type'} (lt2 : type1402 A) (f : type184 A) (g : type184 A) (H : type700 A) : (term215 A lt2 f g H) = (term216 A lt2 f g H).
Proof. exact (MK_COMB (@lem340011 A lt2 f H) (@lem340012 A g H)). Qed.
Lemma lem340014 {A : Type'} (lt2 : type1402 A) (g : type184 A) (f : type184 A) (H : type700 A) : (term216 A lt2 f g H) = (term217 A lt2 g f H).
Proof. exact (eq_refl (term216 A lt2 f g H)). Qed.
Lemma lem340015 {A : Type'} (lt2 : type1402 A) (g : type184 A) (f : type184 A) (H : type700 A) : (term215 A lt2 f g H) = (term217 A lt2 g f H).
Proof. exact (TRANS (@lem340013 A lt2 f g H) (@lem340014 A lt2 g f H)). Qed.
Lemma lem340016 {A : Type'} (lt2 : type1402 A) (g : type184 A) (f : type184 A) : (term218 A lt2 f g) = (term219 A lt2 g f).
Proof. exact (fun_ext (fun H : type700 A => @lem340015 A lt2 g f H)). Qed.
Lemma lem340017 {A : Type'} : (@all ((A -> nat) -> A -> nat)) = (@all ((A -> nat) -> A -> nat)).
Proof. exact (eq_refl (@all ((A -> nat) -> A -> nat))). Qed.
Lemma lem340018 {A : Type'} (lt2 : type1402 A) (g : type184 A) (f : type184 A) : (term220 A lt2 f g) = (term221 A lt2 g f).
Proof. exact (MK_COMB (@lem340017 A) (@lem340016 A lt2 g f)). Qed.
Lemma lem340019 {A : Type'} (lt2 : type1402 A) (f : type184 A) : (term222 A lt2 f) = (term223 A lt2 f).
Proof. exact (fun_ext (fun g : type184 A => @lem340018 A lt2 g f)). Qed.
Lemma lem340020 {A : Type'} : (@ex (((A -> nat) -> A -> nat) -> A -> nat)) = (@ex (((A -> nat) -> A -> nat) -> A -> nat)).
Proof. exact (eq_refl (@ex (((A -> nat) -> A -> nat) -> A -> nat))). Qed.
Lemma lem340021 {A : Type'} (lt2 : type1402 A) (f : type184 A) : (term203 A lt2 f) = (term224 A lt2 f).
Proof. exact (MK_COMB (@lem340020 A) (@lem340019 A lt2 f)). Qed.
Lemma lem340022 {A : Type'} (lt2 : type1402 A) (f : type184 A) : ((term202 A lt2 f) = (term203 A lt2 f)) = ((term198 A lt2 f) = (term224 A lt2 f)).
Proof. exact (MK_COMB (@lem340010 A lt2 f) (@lem340021 A lt2 f)). Qed.
Lemma lem340023 {A : Type'} (lt2 : type1402 A) (f : type184 A) : (term198 A lt2 f) = (term224 A lt2 f).
Proof. exact (EQ_MP (@lem340022 A lt2 f) (@lem339997 A lt2 f)). Qed.
Lemma lem340025 {A B : Type'} (P : type1413 A B) : (term177 A B P) = (term178 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem340026 {A : Type'} (P : type183 A) : (term225 A P) = (term226 A P).
Proof. exact (@lem340025 (type700 A) A P). Qed.
Lemma lem340027 {A : Type'} (lt2 : type1402 A) (g : type184 A) (f : type184 A) : (term227 A lt2 g f) = (term228 A lt2 g f).
Proof. exact (@lem340026 A (term229 A lt2 g f)). Qed.
Lemma lem340028 {A : Type'} (lt2 : type1402 A) (g : type184 A) (f : type184 A) (H : type700 A) : (term230 A lt2 g f H) = (term231 A lt2 g f H).
Proof. exact (eq_refl (term230 A lt2 g f H)). Qed.
Lemma lem340029 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem340030 {A : Type'} (lt2 : type1402 A) (g : type184 A) (f : type184 A) (H : type700 A) (x : A) : (term232 A lt2 g f H x) = (term233 A lt2 g f H x).
Proof. exact (MK_COMB (@lem340028 A lt2 g f H) (@lem340029 A x)). Qed.
Lemma lem340031 {A : Type'} (lt2 : type1402 A) (g : type184 A) (x : A) (f : type184 A) (H : type700 A) : (term233 A lt2 g f H x) = (term234 A lt2 g x f H).
Proof. exact (eq_refl (term233 A lt2 g f H x)). Qed.
Lemma lem340032 {A : Type'} (lt2 : type1402 A) (g : type184 A) (x : A) (f : type184 A) (H : type700 A) : (term232 A lt2 g f H x) = (term234 A lt2 g x f H).
Proof. exact (TRANS (@lem340030 A lt2 g f H x) (@lem340031 A lt2 g x f H)). Qed.
Lemma lem340033 {A : Type'} (lt2 : type1402 A) (g : type184 A) (f : type184 A) (H : type700 A) : (term235 A lt2 g f H) = (term231 A lt2 g f H).
Proof. exact (fun_ext (fun x : A => @lem340032 A lt2 g x f H)). Qed.
Lemma lem340034 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem340035 {A : Type'} (lt2 : type1402 A) (g : type184 A) (f : type184 A) (H : type700 A) : (term236 A lt2 g f H) = (term217 A lt2 g f H).
Proof. exact (MK_COMB (@lem340034 A) (@lem340033 A lt2 g f H)). Qed.
Lemma lem340036 {A : Type'} (lt2 : type1402 A) (g : type184 A) (f : type184 A) : (term237 A lt2 g f) = (term219 A lt2 g f).
Proof. exact (fun_ext (fun H : type700 A => @lem340035 A lt2 g f H)). Qed.
Lemma lem340037 {A : Type'} : (@all ((A -> nat) -> A -> nat)) = (@all ((A -> nat) -> A -> nat)).
Proof. exact (eq_refl (@all ((A -> nat) -> A -> nat))). Qed.
Lemma lem340038 {A : Type'} (lt2 : type1402 A) (g : type184 A) (f : type184 A) : (term227 A lt2 g f) = (term221 A lt2 g f).
Proof. exact (MK_COMB (@lem340037 A) (@lem340036 A lt2 g f)). Qed.
Lemma lem340039 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem340040 {A : Type'} (lt2 : type1402 A) (g : type184 A) (f : type184 A) : (term238 A lt2 g f) = (term239 A lt2 g f).
Proof. exact (MK_COMB (@lem340039) (@lem340038 A lt2 g f)). Qed.
Lemma lem340041 {A : Type'} (lt2 : type1402 A) (g : type184 A) (f : type184 A) (H : type700 A) : (term230 A lt2 g f H) = (term231 A lt2 g f H).
Proof. exact (eq_refl (term230 A lt2 g f H)). Qed.
Lemma lem340042 {A : Type'} (x : type185 A) (H : type700 A) : (x H) = (x H).
Proof. exact (eq_refl (x H)). Qed.
Lemma lem340043 {A : Type'} (lt2 : type1402 A) (g : type184 A) (f : type184 A) (x : type185 A) (H : type700 A) : (term240 A lt2 g f x H) = (term241 A lt2 g f x H).
Proof. exact (MK_COMB (@lem340041 A lt2 g f H) (@lem340042 A x H)). Qed.
Lemma lem340044 {A : Type'} (lt2 : type1402 A) (g : type184 A) (x : type185 A) (f : type184 A) (H : type700 A) : (term241 A lt2 g f x H) = (term242 A lt2 g x f H).
Proof. exact (eq_refl (term241 A lt2 g f x H)). Qed.
Lemma lem340045 {A : Type'} (lt2 : type1402 A) (g : type184 A) (x : type185 A) (f : type184 A) (H : type700 A) : (term240 A lt2 g f x H) = (term242 A lt2 g x f H).
Proof. exact (TRANS (@lem340043 A lt2 g f x H) (@lem340044 A lt2 g x f H)). Qed.
Lemma lem340046 {A : Type'} (lt2 : type1402 A) (g : type184 A) (x : type185 A) (f : type184 A) : (term243 A lt2 g f x) = (term244 A lt2 g x f).
Proof. exact (fun_ext (fun H : type700 A => @lem340045 A lt2 g x f H)). Qed.
Lemma lem340047 {A : Type'} : (@all ((A -> nat) -> A -> nat)) = (@all ((A -> nat) -> A -> nat)).
Proof. exact (eq_refl (@all ((A -> nat) -> A -> nat))). Qed.
Lemma lem340048 {A : Type'} (lt2 : type1402 A) (g : type184 A) (x : type185 A) (f : type184 A) : (term245 A lt2 g f x) = (term246 A lt2 g x f).
Proof. exact (MK_COMB (@lem340047 A) (@lem340046 A lt2 g x f)). Qed.
Lemma lem340049 {A : Type'} (lt2 : type1402 A) (g : type184 A) (f : type184 A) : (term247 A lt2 g f) = (term248 A lt2 g f).
Proof. exact (fun_ext (fun x : type185 A => @lem340048 A lt2 g x f)). Qed.
Lemma lem340050 {A : Type'} : (@ex (((A -> nat) -> A -> nat) -> A)) = (@ex (((A -> nat) -> A -> nat) -> A)).
Proof. exact (eq_refl (@ex (((A -> nat) -> A -> nat) -> A))). Qed.
Lemma lem340051 {A : Type'} (lt2 : type1402 A) (g : type184 A) (f : type184 A) : (term228 A lt2 g f) = (term249 A lt2 g f).
Proof. exact (MK_COMB (@lem340050 A) (@lem340049 A lt2 g f)). Qed.
Lemma lem340052 {A : Type'} (lt2 : type1402 A) (g : type184 A) (f : type184 A) : ((term227 A lt2 g f) = (term228 A lt2 g f)) = ((term221 A lt2 g f) = (term249 A lt2 g f)).
Proof. exact (MK_COMB (@lem340040 A lt2 g f) (@lem340051 A lt2 g f)). Qed.
Lemma lem340053 {A : Type'} (lt2 : type1402 A) (g : type184 A) (f : type184 A) : (term221 A lt2 g f) = (term249 A lt2 g f).
Proof. exact (EQ_MP (@lem340052 A lt2 g f) (@lem340027 A lt2 g f)). Qed.
Lemma lem340054 {A : Type'} (lt2 : type1402 A) (f : type184 A) : (term223 A lt2 f) = (term250 A lt2 f).
Proof. exact (fun_ext (fun g : type184 A => @lem340053 A lt2 g f)). Qed.
Lemma lem340055 {A : Type'} : (@ex (((A -> nat) -> A -> nat) -> A -> nat)) = (@ex (((A -> nat) -> A -> nat) -> A -> nat)).
Proof. exact (eq_refl (@ex (((A -> nat) -> A -> nat) -> A -> nat))). Qed.
Lemma lem340056 {A : Type'} (lt2 : type1402 A) (f : type184 A) : (term224 A lt2 f) = (term251 A lt2 f).
Proof. exact (MK_COMB (@lem340055 A) (@lem340054 A lt2 f)). Qed.
Lemma lem340057 {A : Type'} (lt2 : type1402 A) (f : type184 A) : (term198 A lt2 f) = (term251 A lt2 f).
Proof. exact (TRANS (@lem340023 A lt2 f) (@lem340056 A lt2 f)). Qed.
Lemma lem340058 {A : Type'} (lt2 : type1402 A) : (term200 A lt2) = (term252 A lt2).
Proof. exact (fun_ext (fun f : type184 A => @lem340057 A lt2 f)). Qed.
Lemma lem340059 {A : Type'} : (@ex (((A -> nat) -> A -> nat) -> A -> nat)) = (@ex (((A -> nat) -> A -> nat) -> A -> nat)).
Proof. exact (eq_refl (@ex (((A -> nat) -> A -> nat) -> A -> nat))). Qed.
Lemma lem340060 {A : Type'} (lt2 : type1402 A) : (term201 A lt2) = (term253 A lt2).
Proof. exact (MK_COMB (@lem340059 A) (@lem340058 A lt2)). Qed.
Lemma lem340061 {A : Type'} (lt2 : type1402 A) : (term176 A lt2) = (term253 A lt2).
Proof. exact (TRANS (@lem339993 A lt2) (@lem340060 A lt2)). Qed.
Lemma lem340063 {A : Type'} (lt2 : type1402 A) : (term114 A lt2) = (term253 A lt2).
Proof. exact (TRANS (@lem339963 A lt2) (@lem340061 A lt2)). Qed.
Lemma lem340064 {A : Type'} (lt2 : type1402 A) : (term15 A lt2) = (term253 A lt2).
Proof. exact (TRANS (@lem339716 A lt2) (@lem340063 A lt2)). Qed.
Lemma lem340065 {A : Type'} (lt2 : type1402 A) (h1 : term15 A lt2) : term253 A lt2.
Proof. exact (EQ_MP (@lem340064 A lt2) (@lem339649 A lt2 h1)). Qed.
Lemma lem340066 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) : (term53 A lt2 x n) = (term53 A lt2 x n).
Proof. exact (eq_refl (term53 A lt2 x n)). Qed.
Lemma lem340067 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : (term54 A lt2 x) = (term54 A lt2 x).
Proof. exact (fun_ext (fun n : nat => @lem340066 A lt2 x n)). Qed.
Lemma lem340068 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem340077 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : (term18 A lt2 x) = (term18 A lt2 x).
Proof. exact (MK_COMB (@lem340068) (@lem340067 A lt2 x)). Qed.
Lemma lem340078 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (h1 : term18 A lt2 x) : term18 A lt2 x.
Proof. exact (EQ_MP (@lem340077 A lt2 x) (@lem339650 A lt2 x h1)). Qed.
Lemma lem340080 (P : nat -> Prop) : (term254 P) = (term255 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem340081 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) : (term74 A lt2 x n) = (term256 A lt2 x n).
Proof. exact (@lem340080 (term23 A lt2 x n)). Qed.
Lemma lem340082 {A : Type'} (lt2 : type1402 A) (m : nat) (x : nat -> A) (n : nat) : (term257 A lt2 x n m) = (term52 A lt2 m x n).
Proof. exact (eq_refl (term257 A lt2 x n m)). Qed.
Lemma lem340083 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem340085 {A : Type'} (lt2 : type1402 A) (m : nat) (x : nat -> A) (n : nat) : (term258 A lt2 x n m) = (term259 A lt2 m x n).
Proof. exact (MK_COMB (@lem340083) (@lem340082 A lt2 m x n)). Qed.
Lemma lem340086 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) : (term260 A lt2 x n) = (term261 A lt2 x n).
Proof. exact (fun_ext (fun m : nat => @lem340085 A lt2 m x n)). Qed.
Lemma lem340087 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem340088 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) : (term256 A lt2 x n) = (term262 A lt2 x n).
Proof. exact (MK_COMB (@lem340087) (@lem340086 A lt2 x n)). Qed.
Lemma lem340097 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) : (term74 A lt2 x n) = (term262 A lt2 x n).
Proof. exact (TRANS (@lem340081 A lt2 x n) (@lem340088 A lt2 x n)). Qed.
Lemma lem340098 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) (h1 : term74 A lt2 x n) : term262 A lt2 x n.
Proof. exact (EQ_MP (@lem340097 A lt2 x n) (@lem339655 A lt2 x n h1)). Qed.
Lemma lem340099 {A : Type'} (lt2 : type1402 A) (f : type184 A) (h1 : term251 A lt2 f) : term251 A lt2 f.
Proof. exact (h1). Qed.
Lemma lem340100 {A : Type'} (lt2 : type1402 A) (g : type184 A) (f : type184 A) (h1 : term249 A lt2 g f) : term249 A lt2 g f.
Proof. exact (h1). Qed.
Lemma lem340102 {A : Type'} (lt2 : type1402 A) : lt2 = lt2.
Proof. exact (eq_refl lt2). Qed.
Lemma lem340103 {A : Type'} (x : nat -> A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem340108 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem340109 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem340108 nat nat f x). Qed.
Lemma lem340111 (n : nat) : (S n) = (@I (nat -> nat) S n).
Proof. exact (@lem340109 S n). Qed.
Lemma lem340112 {A : Type'} (x : nat -> A) (n : nat) : (term263 A x n) = (term264 A x n).
Proof. exact (MK_COMB (@lem340103 A x) (@lem340111 n)). Qed.
Lemma lem340114 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem340115 {A : Type'} (f : nat -> A) (x : nat) : (f x) = (@I (nat -> A) f x).
Proof. exact (@lem340114 nat A f x). Qed.
Lemma lem340116 {A : Type'} (x : nat -> A) (n : nat) : (term264 A x n) = (term265 A x n).
Proof. exact (@lem340115 A x (@I (nat -> nat) S n)). Qed.
Lemma lem340117 {A : Type'} (x : nat -> A) (n : nat) : (term263 A x n) = (term265 A x n).
Proof. exact (TRANS (@lem340112 A x n) (@lem340116 A x n)). Qed.
Lemma lem340122 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem340123 {A : Type'} (f : nat -> A) (x : nat) : (f x) = (@I (nat -> A) f x).
Proof. exact (@lem340122 nat A f x). Qed.
Lemma lem340125 {A : Type'} (x : nat -> A) (n : nat) : (x n) = (@I (nat -> A) x n).
Proof. exact (@lem340123 A x n). Qed.
Lemma lem340126 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) : (term266 A lt2 x n) = (term267 A lt2 x n).
Proof. exact (MK_COMB (@lem340102 A lt2) (@lem340117 A x n)). Qed.
Lemma lem340127 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) : (term53 A lt2 x n) = (term268 A lt2 x n).
Proof. exact (MK_COMB (@lem340126 A lt2 x n) (@lem340125 A x n)). Qed.
Lemma lem340129 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem340130 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem340129 A (A -> Prop) f x). Qed.
Lemma lem340131 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) : (term267 A lt2 x n) = (term269 A lt2 x n).
Proof. exact (@lem340130 A lt2 (term265 A x n)). Qed.
Lemma lem340132 {A : Type'} (x : nat -> A) (n : nat) : (@I (nat -> A) x n) = (@I (nat -> A) x n).
Proof. exact (eq_refl (@I (nat -> A) x n)). Qed.
Lemma lem340133 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) : (term268 A lt2 x n) = (term270 A lt2 x n).
Proof. exact (MK_COMB (@lem340131 A lt2 x n) (@lem340132 A x n)). Qed.
Lemma lem340135 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem340136 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem340135 A Prop f x). Qed.
Lemma lem340137 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) : (term270 A lt2 x n) = (term271 A lt2 x n).
Proof. exact (@lem340136 A (term269 A lt2 x n) (@I (nat -> A) x n)). Qed.
Lemma lem340138 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) : (term268 A lt2 x n) = (term271 A lt2 x n).
Proof. exact (TRANS (@lem340133 A lt2 x n) (@lem340137 A lt2 x n)). Qed.
Lemma lem340139 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) : (term53 A lt2 x n) = (term271 A lt2 x n).
Proof. exact (TRANS (@lem340127 A lt2 x n) (@lem340138 A lt2 x n)). Qed.
Lemma lem340140 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : (term54 A lt2 x) = (term272 A lt2 x).
Proof. exact (fun_ext (fun n : nat => @lem340139 A lt2 x n)). Qed.
Lemma lem340141 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem340142 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : (term18 A lt2 x) = (term273 A lt2 x).
Proof. exact (MK_COMB (@lem340141) (@lem340140 A lt2 x)). Qed.
Lemma lem340143 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (h1 : term18 A lt2 x) : term273 A lt2 x.
Proof. exact (EQ_MP (@lem340142 A lt2 x) (@lem340078 A lt2 x h1)). Qed.
Lemma lem340144 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem340145 {A : Type'} (lt2 : type1402 A) : lt2 = lt2.
Proof. exact (eq_refl lt2). Qed.
Lemma lem340150 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem340151 {A : Type'} (f : nat -> A) (x : nat) : (f x) = (@I (nat -> A) f x).
Proof. exact (@lem340150 nat A f x). Qed.
Lemma lem340153 {A : Type'} (x : nat -> A) (m : nat) : (x m) = (@I (nat -> A) x m).
Proof. exact (@lem340151 A x m). Qed.
Lemma lem340158 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem340159 {A : Type'} (f : nat -> A) (x : nat) : (f x) = (@I (nat -> A) f x).
Proof. exact (@lem340158 nat A f x). Qed.
Lemma lem340161 {A : Type'} (x : nat -> A) (n : nat) : (x n) = (@I (nat -> A) x n).
Proof. exact (@lem340159 A x n). Qed.
Lemma lem340162 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (m : nat) : (term274 A lt2 x m) = (term275 A lt2 x m).
Proof. exact (MK_COMB (@lem340145 A lt2) (@lem340153 A x m)). Qed.
Lemma lem340163 {A : Type'} (lt2 : type1402 A) (m : nat) (x : nat -> A) (n : nat) : (term52 A lt2 m x n) = (term276 A lt2 m x n).
Proof. exact (MK_COMB (@lem340162 A lt2 x m) (@lem340161 A x n)). Qed.
Lemma lem340165 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem340166 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem340165 A (A -> Prop) f x). Qed.
Lemma lem340167 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (m : nat) : (term275 A lt2 x m) = (term277 A lt2 x m).
Proof. exact (@lem340166 A lt2 (@I (nat -> A) x m)). Qed.
Lemma lem340168 {A : Type'} (x : nat -> A) (n : nat) : (@I (nat -> A) x n) = (@I (nat -> A) x n).
Proof. exact (eq_refl (@I (nat -> A) x n)). Qed.
Lemma lem340169 {A : Type'} (lt2 : type1402 A) (m : nat) (x : nat -> A) (n : nat) : (term276 A lt2 m x n) = (term278 A lt2 m x n).
Proof. exact (MK_COMB (@lem340167 A lt2 x m) (@lem340168 A x n)). Qed.
Lemma lem340171 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem340172 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem340171 A Prop f x). Qed.
Lemma lem340173 {A : Type'} (lt2 : type1402 A) (m : nat) (x : nat -> A) (n : nat) : (term278 A lt2 m x n) = (term279 A lt2 m x n).
Proof. exact (@lem340172 A (term277 A lt2 x m) (@I (nat -> A) x n)). Qed.
Lemma lem340174 {A : Type'} (lt2 : type1402 A) (m : nat) (x : nat -> A) (n : nat) : (term276 A lt2 m x n) = (term279 A lt2 m x n).
Proof. exact (TRANS (@lem340169 A lt2 m x n) (@lem340173 A lt2 m x n)). Qed.
Lemma lem340175 {A : Type'} (lt2 : type1402 A) (m : nat) (x : nat -> A) (n : nat) : (term52 A lt2 m x n) = (term279 A lt2 m x n).
Proof. exact (TRANS (@lem340163 A lt2 m x n) (@lem340174 A lt2 m x n)). Qed.
Lemma lem340176 {A : Type'} (lt2 : type1402 A) (m : nat) (x : nat -> A) (n : nat) : (term259 A lt2 m x n) = (term280 A lt2 m x n).
Proof. exact (MK_COMB (@lem340144) (@lem340175 A lt2 m x n)). Qed.
Lemma lem340177 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) : (term261 A lt2 x n) = (term281 A lt2 x n).
Proof. exact (fun_ext (fun m : nat => @lem340176 A lt2 m x n)). Qed.
Lemma lem340178 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem340179 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) : (term262 A lt2 x n) = (term282 A lt2 x n).
Proof. exact (MK_COMB (@lem340178) (@lem340177 A lt2 x n)). Qed.
Lemma lem340180 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) (h1 : term74 A lt2 x n) : term282 A lt2 x n.
Proof. exact (EQ_MP (@lem340179 A lt2 x n) (@lem340098 A lt2 x n h1)). Qed.
Lemma lem340375 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) : (term271 A lt2 x n) = (term271 A lt2 x n).
Proof. exact (eq_refl (term271 A lt2 x n)). Qed.
Lemma lem340376 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : (term272 A lt2 x) = (term272 A lt2 x).
Proof. exact (fun_ext (fun n : nat => @lem340375 A lt2 x n)). Qed.
Lemma lem340377 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem340379 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : (term273 A lt2 x) = (term273 A lt2 x).
Proof. exact (MK_COMB (@lem340377) (@lem340376 A lt2 x)). Qed.
Lemma lem340380 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (h1 : term18 A lt2 x) : term273 A lt2 x.
Proof. exact (EQ_MP (@lem340379 A lt2 x) (@lem340143 A lt2 x h1)). Qed.
Lemma lem340382 {A : Type'} (lt2 : type1402 A) (m : nat) (x : nat -> A) (n : nat) : (term280 A lt2 m x n) = (term280 A lt2 m x n).
Proof. exact (eq_refl (term280 A lt2 m x n)). Qed.
Lemma lem340383 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) : (term281 A lt2 x n) = (term281 A lt2 x n).
Proof. exact (fun_ext (fun m : nat => @lem340382 A lt2 m x n)). Qed.
Lemma lem340384 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem340386 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) : (term282 A lt2 x n) = (term282 A lt2 x n).
Proof. exact (MK_COMB (@lem340384) (@lem340383 A lt2 x n)). Qed.
Lemma lem340387 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) (h1 : term74 A lt2 x n) : term282 A lt2 x n.
Proof. exact (EQ_MP (@lem340386 A lt2 x n) (@lem340180 A lt2 x n h1)). Qed.
Lemma lem340502 {A : Type'} (_7352 : nat) (lt2 : type1402 A) (x : nat -> A) (h1 : term18 A lt2 x) : term283 A lt2 x _7352.
Proof. exact (@lem340380 A lt2 x h1 _7352). Qed.
Lemma lem340503 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (_7352 : nat) : (term283 A lt2 x _7352) = (term271 A lt2 x _7352).
Proof. exact (eq_refl (term283 A lt2 x _7352)). Qed.
Lemma lem340505 {A : Type'} (_7353 : nat) (lt2 : type1402 A) (x : nat -> A) (n : nat) (h1 : term74 A lt2 x n) : term284 A lt2 x n _7353.
Proof. exact (@lem340387 A lt2 x n h1 _7353). Qed.
Lemma lem340506 {A : Type'} (lt2 : type1402 A) (_7353 : nat) (x : nat -> A) (n : nat) : (term284 A lt2 x n _7353) = (term280 A lt2 _7353 x n).
Proof. exact (eq_refl (term284 A lt2 x n _7353)). Qed.
Lemma lem340522 {A : Type'} (_7353 : nat) (lt2 : type1402 A) (x : nat -> A) (n : nat) (h1 : term74 A lt2 x n) : term280 A lt2 _7353 x n.
Proof. exact (EQ_MP (@lem340506 A lt2 _7353 x n) (@lem340505 A _7353 lt2 x n h1)). Qed.
Lemma lem340686 {A : Type'} (_7352 : nat) (lt2 : type1402 A) (x : nat -> A) (h1 : term18 A lt2 x) : term271 A lt2 x _7352.
Proof. exact (EQ_MP (@lem340503 A lt2 x _7352) (@lem340502 A _7352 lt2 x h1)). Qed.
Lemma lem340687 {A : Type'} (n : nat) (lt2 : type1402 A) (x : nat -> A) (h1 : term18 A lt2 x) : term271 A lt2 x n.
Proof. exact (@lem340686 A n lt2 x h1). Qed.
Lemma lem340688 {A : Type'} (n : nat) (lt2 : type1402 A) (x : nat -> A) (h1 : term18 A lt2 x) : term285 A lt2 x n.
Proof. exact (fun h0 : term286 A lt2 x n => @lem340687 A n lt2 x h1). Qed.
Lemma lem340690 (p : Prop) : (term287 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem340691 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) : (term285 A lt2 x n) = (term271 A lt2 x n).
Proof. exact (@lem340690 (term271 A lt2 x n)). Qed.
Lemma lem340692 {A : Type'} (n : nat) (lt2 : type1402 A) (x : nat -> A) (h1 : term18 A lt2 x) : term271 A lt2 x n.
Proof. exact (EQ_MP (@lem340691 A lt2 x n) (@lem340688 A n lt2 x h1)). Qed.
Lemma lem340695 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem340697 {A : Type'} (lt2 : type1402 A) (_7353 : nat) (x : nat -> A) (n : nat) : (term280 A lt2 _7353 x n) = (term288 A lt2 _7353 x n).
Proof. exact (@lem340695 (term279 A lt2 _7353 x n)). Qed.
Lemma lem340700 {A : Type'} (_7353 : nat) (lt2 : type1402 A) (x : nat -> A) (n : nat) (h1 : term74 A lt2 x n) : term288 A lt2 _7353 x n.
Proof. exact (EQ_MP (@lem340697 A lt2 _7353 x n) (@lem340522 A _7353 lt2 x n h1)). Qed.
Lemma lem340701 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) (h1 : term74 A lt2 x n) : term289 A lt2 x n.
Proof. exact (@lem340700 A (@I (nat -> nat) S n) lt2 x n h1). Qed.
Lemma lem340704 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) (h1 : term18 A lt2 x) (h2 : term74 A lt2 x n) : False.
Proof. exact (@lem340701 A lt2 x n h2 (@lem340692 A n lt2 x h1)). Qed.
Lemma lem340705 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) (h1 : term18 A lt2 x) (h2 : term74 A lt2 x n) : term290.
Proof. exact (fun h0 : ~ False => @lem340704 A lt2 x n h1 h2). Qed.
Lemma lem340707 (p : Prop) : (term287 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem340708 : term290 = False.
Proof. exact (@lem340707 False). Qed.
Lemma lem340709 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) (h1 : term18 A lt2 x) (h2 : term74 A lt2 x n) : False.
Proof. exact (EQ_MP (@lem340708) (@lem340705 A lt2 x n h1 h2)). Qed.
Lemma lem340710 {A : Type'} (g : type184 A) (f : type184 A) (lt2 : type1402 A) (x : nat -> A) (n : nat) (h1 : term18 A lt2 x) (h2 : term249 A lt2 g f) (h3 : term74 A lt2 x n) : False.
Proof. exact (ex_elim (@lem340100 A lt2 g f h2) (fun x' : type185 A => fun h0 : term248 A lt2 g f x' => @lem340709 A lt2 x n h1 h3)). Qed.
Lemma lem340711 {A : Type'} (f : type184 A) (lt2 : type1402 A) (x : nat -> A) (n : nat) (h1 : term18 A lt2 x) (h2 : term251 A lt2 f) (h3 : term74 A lt2 x n) : False.
Proof. exact (ex_elim (@lem340099 A lt2 f h2) (fun g : type184 A => fun h0 : term250 A lt2 f g => @lem340710 A g f lt2 x n h1 h0 h3)). Qed.
Lemma lem340712 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) (h1 : term15 A lt2) (h2 : term18 A lt2 x) (h3 : term74 A lt2 x n) : False.
Proof. exact (ex_elim (@lem340065 A lt2 h1) (fun f : type184 A => fun h0 : term252 A lt2 f => @lem340711 A f lt2 x n h2 h0 h3)). Qed.
Lemma lem340713 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) (h1 : term15 A lt2) (h2 : term18 A lt2 x) (h3 : term74 A lt2 x n) : (term18 A lt2 x) = False.
Proof. exact (prop_ext (fun h4 : term18 A lt2 x => @lem340712 A lt2 x n h1 h2 h3) (fun h4 : False => @lem340078 A lt2 x h2)). Qed.
Lemma lem340714 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) (h1 : term15 A lt2) (h2 : term18 A lt2 x) (h3 : term74 A lt2 x n) : False.
Proof. exact (EQ_MP (@lem340713 A lt2 x n h1 h2 h3) (@lem340078 A lt2 x h2)). Qed.
Lemma lem340715 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) (h1 : term15 A lt2) (h2 : term18 A lt2 x) (h3 : term74 A lt2 x n) : (term74 A lt2 x n) = False.
Proof. exact (prop_ext (fun h4 : term74 A lt2 x n => @lem340714 A lt2 x n h1 h2 h3) (fun h4 : False => @lem339655 A lt2 x n h3)). Qed.
Lemma lem340716 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) (h1 : term15 A lt2) (h2 : term18 A lt2 x) (h3 : term74 A lt2 x n) : False.
Proof. exact (EQ_MP (@lem340715 A lt2 x n h1 h2 h3) (@lem339655 A lt2 x n h3)). Qed.
Lemma lem340717 {A : Type'} (n : nat) (lt2 : type1402 A) (x : nat -> A) (h1 : term15 A lt2) (h2 : term18 A lt2 x) : term73 A lt2 x n.
Proof. exact (fun h0 : term74 A lt2 x n => @lem340716 A lt2 x n h1 h2 h0). Qed.
Lemma lem340718 {A : Type'} (n : nat) (lt2 : type1402 A) (x : nat -> A) (h1 : term15 A lt2) (h2 : term18 A lt2 x) : term22 A lt2 x n.
Proof. exact (EQ_MP (@lem339654 A lt2 x n) (@lem340717 A n lt2 x h1 h2)). Qed.
Lemma lem340723 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (h1 : term15 A lt2) (h2 : term18 A lt2 x) : term29 A lt2 x.
Proof. exact (fun n : nat => @lem340718 A n lt2 x h1 h2). Qed.
Lemma lem340724 {A : Type'} (x : nat -> A) (lt2 : type1402 A) (h1 : term15 A lt2) : term41 A lt2 x.
Proof. exact (fun h0 : term18 A lt2 x => @lem340723 A lt2 x h1 h0). Qed.
Lemma lem340725 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : term43 A lt2 x.
Proof. exact (fun h0 : term15 A lt2 => @lem340724 A x lt2 h0). Qed.
Lemma lem340730 {A : Type'} (x : nat -> A) : term47 A x.
Proof. exact (fun lt2 : type1402 A => @lem340725 A lt2 x). Qed.
Lemma lem340735 {A : Type'} : term51 A.
Proof. exact (fun x : nat -> A => @lem340730 A x). Qed.
Lemma lem340736 {A : Type'} : term50 A.
Proof. exact (EQ_MP (@lem339648 A) (@lem340735 A)). Qed.
Lemma lem340737 {A : Type'} (x : nat -> A) : term291 A x.
Proof. exact (@lem340736 A x). Qed.
Lemma lem340738 {A : Type'} (x : nat -> A) : (term291 A x) = (term46 A x).
Proof. exact (eq_refl (term291 A x)). Qed.
Lemma lem340739 {A : Type'} (x : nat -> A) : term46 A x.
Proof. exact (EQ_MP (@lem340738 A x) (@lem340737 A x)). Qed.
Lemma lem340740 {A : Type'} (x : nat -> A) (lt2 : type1402 A) : term292 A x lt2.
Proof. exact (@lem340739 A x lt2). Qed.
Lemma lem340741 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : (term292 A x lt2) = (term33 A lt2 x).
Proof. exact (eq_refl (term292 A x lt2)). Qed.
Lemma lem340742 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : term33 A lt2 x.
Proof. exact (EQ_MP (@lem340741 A lt2 x) (@lem340740 A x lt2)). Qed.
Lemma lem340744 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : term33 A lt2 x.
Proof. exact (@lem339414 A lt2 x (@lem340742 A lt2 x)). Qed.
Lemma lem340745 {A : Type'} (x : nat -> A) (lt2 : type1402 A) (h1 : term15 A lt2) : term40 A lt2 x.
Proof. exact (@lem340744 A lt2 x (@lem339366 A lt2 h1)). Qed.
Lemma lem340746 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (h1 : term15 A lt2) (h2 : term18 A lt2 x) : term31 A lt2 x.
Proof. exact (@lem340745 A x lt2 h1 (@lem339380 A lt2 x h2)). Qed.
Lemma lem340747 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (h1 : term15 A lt2) (h2 : term18 A lt2 x) (h3 : term32 A lt2 x) : False.
Proof. exact (@lem340746 A lt2 x h1 h2 (@lem339398 A lt2 x h3)). Qed.
Lemma lem340748 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (h1 : term15 A lt2) (h2 : term18 A lt2 x) (h3 : term32 A lt2 x) : (term32 A lt2 x) = False.
Proof. exact (prop_ext (fun h4 : term32 A lt2 x => @lem340747 A lt2 x h1 h2 h3) (fun h4 : False => @lem339398 A lt2 x h3)). Qed.
Lemma lem340749 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (h1 : term15 A lt2) (h2 : term18 A lt2 x) (h3 : term32 A lt2 x) : False.
Proof. exact (EQ_MP (@lem340748 A lt2 x h1 h2 h3) (@lem339398 A lt2 x h3)). Qed.
Lemma lem340750 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (h1 : term15 A lt2) (h2 : term18 A lt2 x) : term31 A lt2 x.
Proof. exact (fun h0 : term32 A lt2 x => @lem340749 A lt2 x h1 h2 h0). Qed.
Lemma lem340751 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (h1 : term15 A lt2) (h2 : term18 A lt2 x) : term29 A lt2 x.
Proof. exact (EQ_MP (@lem339397 A lt2 x) (@lem340750 A lt2 x h1 h2)). Qed.
Lemma lem340752 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (h1 : term15 A lt2) (h2 : term18 A lt2 x) : term19 A lt2 x.
Proof. exact (EQ_MP (@lem339393 A lt2 x) (@lem340751 A lt2 x h1 h2)). Qed.
Lemma lem340753 {A : Type'} (x : nat -> A) (lt2 : type1402 A) (h1 : term15 A lt2) : term293 A lt2 x.
Proof. exact (@lem339366 A lt2 h1 (term294 A lt2 x)). Qed.
Lemma lem340754 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : (term293 A lt2 x) = (term295 A lt2 x).
Proof. exact (eq_refl (term293 A lt2 x)). Qed.
Lemma lem340755 {A : Type'} (x : nat -> A) (lt2 : type1402 A) (h1 : term15 A lt2) : term295 A lt2 x.
Proof. exact (EQ_MP (@lem340754 A lt2 x) (@lem340753 A x lt2 h1)). Qed.
Lemma lem340757 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem340758 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : (term296 A lt2 x) = (term297 A lt2 x).
Proof. exact (@lem340757 (term295 A lt2 x)). Qed.
Lemma lem340760 (t1 : Prop) (t2 : Prop) : (term13 t1 t2) = (term14 t1 t2).
Proof. exact (EQ_MP (@lem339354 t1 t2) (@lem339353 t1 t2)). Qed.
Lemma lem340761 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : (term297 A lt2 x) = (term298 A lt2 x).
Proof. exact (@lem340760 (term299 A lt2 x) (term300 A lt2 x)). Qed.
Lemma lem340764 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : (term296 A lt2 x) = (term298 A lt2 x).
Proof. exact (TRANS (@lem340758 A lt2 x) (@lem340761 A lt2 x)). Qed.
Lemma lem340790 {A B : Type'} (f : A -> B) (y : A) : (term301 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem340791 {A : Type'} (f : type700 A) (y : A -> nat) : (term302 A f y) = (f y).
Proof. exact (@lem340790 (A -> nat) (A -> nat) f y). Qed.
Lemma lem340792 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (f : A -> nat) : (term303 A lt2 x f) = (term304 A lt2 x f).
Proof. exact (@lem340791 A (term294 A lt2 x) f). Qed.
Lemma lem340793 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) : (term304 A lt2 x f) = (term305 A f lt2 x).
Proof. exact (eq_refl (term304 A lt2 x f)). Qed.
Lemma lem340794 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : (term306 A lt2 x) = (term294 A lt2 x).
Proof. exact (fun_ext (fun f : A -> nat => @lem340793 A f lt2 x)). Qed.
Lemma lem340795 {A : Type'} (f : A -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem340796 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (f : A -> nat) : (term303 A lt2 x f) = (term304 A lt2 x f).
Proof. exact (MK_COMB (@lem340794 A lt2 x) (@lem340795 A f)). Qed.
Lemma lem340797 {A : Type'} : (@eq (A -> nat)) = (@eq (A -> nat)).
Proof. exact (eq_refl (@eq (A -> nat))). Qed.
Lemma lem340798 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (f : A -> nat) : (term307 A lt2 x f) = (term308 A lt2 x f).
Proof. exact (MK_COMB (@lem340797 A) (@lem340796 A lt2 x f)). Qed.
Lemma lem340799 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) : (term304 A lt2 x f) = (term305 A f lt2 x).
Proof. exact (eq_refl (term304 A lt2 x f)). Qed.
Lemma lem340800 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) : ((term303 A lt2 x f) = (term304 A lt2 x f)) = ((term304 A lt2 x f) = (term305 A f lt2 x)).
Proof. exact (MK_COMB (@lem340798 A lt2 x f) (@lem340799 A f lt2 x)). Qed.
Lemma lem340801 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) : (term304 A lt2 x f) = (term305 A f lt2 x).
Proof. exact (EQ_MP (@lem340800 A f lt2 x) (@lem340792 A lt2 x f)). Qed.
Lemma lem340808 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem340809 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (x' : A) : (term309 A lt2 x f x') = (term310 A f lt2 x x').
Proof. exact (MK_COMB (@lem340801 A f lt2 x) (@lem340808 A x')). Qed.
Lemma lem340811 {A B : Type'} (f : A -> B) (y : A) : (term301 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem340812 {A : Type'} (f : A -> nat) (y : A) : (term311 A f y) = (f y).
Proof. exact (@lem340811 A nat f y). Qed.
Lemma lem340813 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (x' : A) : (term312 A f lt2 x x') = (term310 A f lt2 x x').
Proof. exact (@lem340812 A (term305 A f lt2 x) x'). Qed.
Lemma lem340814 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (y : A) : (term310 A f lt2 x y) = (term313 A f lt2 x y).
Proof. exact (eq_refl (term310 A f lt2 x y)). Qed.
Lemma lem340815 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) : (term314 A f lt2 x) = (term305 A f lt2 x).
Proof. exact (fun_ext (fun y : A => @lem340814 A f lt2 x y)). Qed.
Lemma lem340816 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem340817 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (x' : A) : (term312 A f lt2 x x') = (term310 A f lt2 x x').
Proof. exact (MK_COMB (@lem340815 A f lt2 x) (@lem340816 A x')). Qed.
Lemma lem340818 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem340819 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (x' : A) : (term315 A f lt2 x x') = (term316 A f lt2 x x').
Proof. exact (MK_COMB (@lem340818) (@lem340817 A f lt2 x x')). Qed.
Lemma lem340820 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (x' : A) : (term310 A f lt2 x x') = (term313 A f lt2 x x').
Proof. exact (eq_refl (term310 A f lt2 x x')). Qed.
Lemma lem340821 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (x' : A) : ((term312 A f lt2 x x') = (term310 A f lt2 x x')) = ((term310 A f lt2 x x') = (term313 A f lt2 x x')).
Proof. exact (MK_COMB (@lem340819 A f lt2 x x') (@lem340820 A f lt2 x x')). Qed.
Lemma lem340822 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (x' : A) : (term310 A f lt2 x x') = (term313 A f lt2 x x').
Proof. exact (EQ_MP (@lem340821 A f lt2 x x') (@lem340813 A f lt2 x x')). Qed.
Lemma lem340829 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (x' : A) : (term309 A lt2 x f x') = (term313 A f lt2 x x').
Proof. exact (TRANS (@lem340809 A f lt2 x x') (@lem340822 A f lt2 x x')). Qed.
Lemma lem340830 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem340831 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (x' : A) : (term317 A lt2 x f x') = (term318 A f lt2 x x').
Proof. exact (MK_COMB (@lem340830) (@lem340829 A f lt2 x x')). Qed.
Lemma lem340833 {A B : Type'} (f : A -> B) (y : A) : (term301 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem340834 {A : Type'} (f : type700 A) (y : A -> nat) : (term302 A f y) = (f y).
Proof. exact (@lem340833 (A -> nat) (A -> nat) f y). Qed.
Lemma lem340835 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (g : A -> nat) : (term303 A lt2 x g) = (term304 A lt2 x g).
Proof. exact (@lem340834 A (term294 A lt2 x) g). Qed.
Lemma lem340836 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) : (term304 A lt2 x f) = (term305 A f lt2 x).
Proof. exact (eq_refl (term304 A lt2 x f)). Qed.
Lemma lem340837 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : (term306 A lt2 x) = (term294 A lt2 x).
Proof. exact (fun_ext (fun f : A -> nat => @lem340836 A f lt2 x)). Qed.
Lemma lem340838 {A : Type'} (g : A -> nat) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem340839 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (g : A -> nat) : (term303 A lt2 x g) = (term304 A lt2 x g).
Proof. exact (MK_COMB (@lem340837 A lt2 x) (@lem340838 A g)). Qed.
Lemma lem340840 {A : Type'} : (@eq (A -> nat)) = (@eq (A -> nat)).
Proof. exact (eq_refl (@eq (A -> nat))). Qed.
Lemma lem340841 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (g : A -> nat) : (term307 A lt2 x g) = (term308 A lt2 x g).
Proof. exact (MK_COMB (@lem340840 A) (@lem340839 A lt2 x g)). Qed.
Lemma lem340842 {A : Type'} (g : A -> nat) (lt2 : type1402 A) (x : nat -> A) : (term304 A lt2 x g) = (term305 A g lt2 x).
Proof. exact (eq_refl (term304 A lt2 x g)). Qed.
Lemma lem340843 {A : Type'} (g : A -> nat) (lt2 : type1402 A) (x : nat -> A) : ((term303 A lt2 x g) = (term304 A lt2 x g)) = ((term304 A lt2 x g) = (term305 A g lt2 x)).
Proof. exact (MK_COMB (@lem340841 A lt2 x g) (@lem340842 A g lt2 x)). Qed.
Lemma lem340844 {A : Type'} (g : A -> nat) (lt2 : type1402 A) (x : nat -> A) : (term304 A lt2 x g) = (term305 A g lt2 x).
Proof. exact (EQ_MP (@lem340843 A g lt2 x) (@lem340835 A lt2 x g)). Qed.
Lemma lem340851 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem340852 {A : Type'} (g : A -> nat) (lt2 : type1402 A) (x : nat -> A) (x' : A) : (term309 A lt2 x g x') = (term310 A g lt2 x x').
Proof. exact (MK_COMB (@lem340844 A g lt2 x) (@lem340851 A x')). Qed.
Lemma lem340854 {A B : Type'} (f : A -> B) (y : A) : (term301 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem340855 {A : Type'} (f : A -> nat) (y : A) : (term311 A f y) = (f y).
Proof. exact (@lem340854 A nat f y). Qed.
Lemma lem340856 {A : Type'} (g : A -> nat) (lt2 : type1402 A) (x : nat -> A) (x' : A) : (term312 A g lt2 x x') = (term310 A g lt2 x x').
Proof. exact (@lem340855 A (term305 A g lt2 x) x'). Qed.
Lemma lem340857 {A : Type'} (g : A -> nat) (lt2 : type1402 A) (x : nat -> A) (y : A) : (term310 A g lt2 x y) = (term313 A g lt2 x y).
Proof. exact (eq_refl (term310 A g lt2 x y)). Qed.
Lemma lem340858 {A : Type'} (g : A -> nat) (lt2 : type1402 A) (x : nat -> A) : (term314 A g lt2 x) = (term305 A g lt2 x).
Proof. exact (fun_ext (fun y : A => @lem340857 A g lt2 x y)). Qed.
Lemma lem340859 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem340860 {A : Type'} (g : A -> nat) (lt2 : type1402 A) (x : nat -> A) (x' : A) : (term312 A g lt2 x x') = (term310 A g lt2 x x').
Proof. exact (MK_COMB (@lem340858 A g lt2 x) (@lem340859 A x')). Qed.
Lemma lem340861 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem340862 {A : Type'} (g : A -> nat) (lt2 : type1402 A) (x : nat -> A) (x' : A) : (term315 A g lt2 x x') = (term316 A g lt2 x x').
Proof. exact (MK_COMB (@lem340861) (@lem340860 A g lt2 x x')). Qed.
Lemma lem340863 {A : Type'} (g : A -> nat) (lt2 : type1402 A) (x : nat -> A) (x' : A) : (term310 A g lt2 x x') = (term313 A g lt2 x x').
Proof. exact (eq_refl (term310 A g lt2 x x')). Qed.
Lemma lem340864 {A : Type'} (g : A -> nat) (lt2 : type1402 A) (x : nat -> A) (x' : A) : ((term312 A g lt2 x x') = (term310 A g lt2 x x')) = ((term310 A g lt2 x x') = (term313 A g lt2 x x')).
Proof. exact (MK_COMB (@lem340862 A g lt2 x x') (@lem340863 A g lt2 x x')). Qed.
Lemma lem340865 {A : Type'} (g : A -> nat) (lt2 : type1402 A) (x : nat -> A) (x' : A) : (term310 A g lt2 x x') = (term313 A g lt2 x x').
Proof. exact (EQ_MP (@lem340864 A g lt2 x x') (@lem340856 A g lt2 x x')). Qed.
Lemma lem340872 {A : Type'} (g : A -> nat) (lt2 : type1402 A) (x : nat -> A) (x' : A) : (term309 A lt2 x g x') = (term313 A g lt2 x x').
Proof. exact (TRANS (@lem340852 A g lt2 x x') (@lem340865 A g lt2 x x')). Qed.
Lemma lem340873 {A : Type'} (f : A -> nat) (g : A -> nat) (lt2 : type1402 A) (x : nat -> A) (x' : A) : ((term309 A lt2 x f x') = (term309 A lt2 x g x')) = ((term313 A f lt2 x x') = (term313 A g lt2 x x')).
Proof. exact (MK_COMB (@lem340831 A f lt2 x x') (@lem340872 A g lt2 x x')). Qed.
Lemma lem340876 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> nat) (g : A -> nat) : (term62 A lt2 x f g) = (term62 A lt2 x f g).
Proof. exact (eq_refl (term62 A lt2 x f g)). Qed.
Lemma lem340877 {A : Type'} (f : A -> nat) (g : A -> nat) (lt2 : type1402 A) (x : nat -> A) (x' : A) : (term319 A f lt2 x g x') = (term320 A f g lt2 x x').
Proof. exact (MK_COMB (@lem340876 A lt2 x' f g) (@lem340873 A f g lt2 x x')). Qed.
Lemma lem340880 {A : Type'} (f : A -> nat) (g : A -> nat) (lt2 : type1402 A) (x : nat -> A) : (term321 A f lt2 x g) = (term322 A f g lt2 x).
Proof. exact (fun_ext (fun x' : A => @lem340877 A f g lt2 x x')). Qed.
Lemma lem340881 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem340882 {A : Type'} (f : A -> nat) (g : A -> nat) (lt2 : type1402 A) (x : nat -> A) : (term323 A f lt2 x g) = (term324 A f g lt2 x).
Proof. exact (MK_COMB (@lem340881 A) (@lem340880 A f g lt2 x)). Qed.
Lemma lem340887 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) : (term325 A f lt2 x) = (term326 A f lt2 x).
Proof. exact (fun_ext (fun g : A -> nat => @lem340882 A f g lt2 x)). Qed.
Lemma lem340888 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem340889 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) : (term327 A f lt2 x) = (term328 A f lt2 x).
Proof. exact (MK_COMB (@lem340888 A) (@lem340887 A f lt2 x)). Qed.
Lemma lem340894 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : (term329 A lt2 x) = (term330 A lt2 x).
Proof. exact (fun_ext (fun f : A -> nat => @lem340889 A f lt2 x)). Qed.
Lemma lem340895 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem340896 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : (term299 A lt2 x) = (term331 A lt2 x).
Proof. exact (MK_COMB (@lem340895 A) (@lem340894 A lt2 x)). Qed.
Lemma lem340901 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem340902 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : (term332 A lt2 x) = (term333 A lt2 x).
Proof. exact (MK_COMB (@lem340901) (@lem340896 A lt2 x)). Qed.
Lemma lem340914 {A B : Type'} (f : A -> B) (y : A) : (term301 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem340915 {A : Type'} (f : type700 A) (y : A -> nat) : (term302 A f y) = (f y).
Proof. exact (@lem340914 (A -> nat) (A -> nat) f y). Qed.
Lemma lem340916 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (f : A -> nat) : (term303 A lt2 x f) = (term304 A lt2 x f).
Proof. exact (@lem340915 A (term294 A lt2 x) f). Qed.
Lemma lem340917 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) : (term304 A lt2 x f) = (term305 A f lt2 x).
Proof. exact (eq_refl (term304 A lt2 x f)). Qed.
Lemma lem340918 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : (term306 A lt2 x) = (term294 A lt2 x).
Proof. exact (fun_ext (fun f : A -> nat => @lem340917 A f lt2 x)). Qed.
Lemma lem340919 {A : Type'} (f : A -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem340920 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (f : A -> nat) : (term303 A lt2 x f) = (term304 A lt2 x f).
Proof. exact (MK_COMB (@lem340918 A lt2 x) (@lem340919 A f)). Qed.
Lemma lem340921 {A : Type'} : (@eq (A -> nat)) = (@eq (A -> nat)).
Proof. exact (eq_refl (@eq (A -> nat))). Qed.
Lemma lem340922 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (f : A -> nat) : (term307 A lt2 x f) = (term308 A lt2 x f).
Proof. exact (MK_COMB (@lem340921 A) (@lem340920 A lt2 x f)). Qed.
Lemma lem340923 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) : (term304 A lt2 x f) = (term305 A f lt2 x).
Proof. exact (eq_refl (term304 A lt2 x f)). Qed.
Lemma lem340924 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) : ((term303 A lt2 x f) = (term304 A lt2 x f)) = ((term304 A lt2 x f) = (term305 A f lt2 x)).
Proof. exact (MK_COMB (@lem340922 A lt2 x f) (@lem340923 A f lt2 x)). Qed.
Lemma lem340925 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) : (term304 A lt2 x f) = (term305 A f lt2 x).
Proof. exact (EQ_MP (@lem340924 A f lt2 x) (@lem340916 A lt2 x f)). Qed.
Lemma lem340932 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem340933 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (x' : A) : (term309 A lt2 x f x') = (term310 A f lt2 x x').
Proof. exact (MK_COMB (@lem340925 A f lt2 x) (@lem340932 A x')). Qed.
Lemma lem340935 {A B : Type'} (f : A -> B) (y : A) : (term301 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem340936 {A : Type'} (f : A -> nat) (y : A) : (term311 A f y) = (f y).
Proof. exact (@lem340935 A nat f y). Qed.
Lemma lem340937 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (x' : A) : (term312 A f lt2 x x') = (term310 A f lt2 x x').
Proof. exact (@lem340936 A (term305 A f lt2 x) x'). Qed.
Lemma lem340938 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (y : A) : (term310 A f lt2 x y) = (term313 A f lt2 x y).
Proof. exact (eq_refl (term310 A f lt2 x y)). Qed.
Lemma lem340939 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) : (term314 A f lt2 x) = (term305 A f lt2 x).
Proof. exact (fun_ext (fun y : A => @lem340938 A f lt2 x y)). Qed.
Lemma lem340940 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem340941 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (x' : A) : (term312 A f lt2 x x') = (term310 A f lt2 x x').
Proof. exact (MK_COMB (@lem340939 A f lt2 x) (@lem340940 A x')). Qed.
Lemma lem340942 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem340943 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (x' : A) : (term315 A f lt2 x x') = (term316 A f lt2 x x').
Proof. exact (MK_COMB (@lem340942) (@lem340941 A f lt2 x x')). Qed.
Lemma lem340944 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (x' : A) : (term310 A f lt2 x x') = (term313 A f lt2 x x').
Proof. exact (eq_refl (term310 A f lt2 x x')). Qed.
Lemma lem340945 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (x' : A) : ((term312 A f lt2 x x') = (term310 A f lt2 x x')) = ((term310 A f lt2 x x') = (term313 A f lt2 x x')).
Proof. exact (MK_COMB (@lem340943 A f lt2 x x') (@lem340944 A f lt2 x x')). Qed.
Lemma lem340946 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (x' : A) : (term310 A f lt2 x x') = (term313 A f lt2 x x').
Proof. exact (EQ_MP (@lem340945 A f lt2 x x') (@lem340937 A f lt2 x x')). Qed.
Lemma lem340953 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (x' : A) : (term309 A lt2 x f x') = (term313 A f lt2 x x').
Proof. exact (TRANS (@lem340933 A f lt2 x x') (@lem340946 A f lt2 x x')). Qed.
Lemma lem340954 {A : Type'} (f : A -> nat) (x : A) : (term334 A f x) = (term334 A f x).
Proof. exact (eq_refl (term334 A f x)). Qed.
Lemma lem340955 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (x' : A) : ((f x') = (term309 A lt2 x f x')) = ((f x') = (term313 A f lt2 x x')).
Proof. exact (MK_COMB (@lem340954 A f x') (@lem340953 A f lt2 x x')). Qed.
Lemma lem340958 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) : (term335 A lt2 x f) = (term336 A f lt2 x).
Proof. exact (fun_ext (fun x' : A => @lem340955 A f lt2 x x')). Qed.
Lemma lem340959 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem340960 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) : (term337 A lt2 x f) = (term338 A f lt2 x).
Proof. exact (MK_COMB (@lem340959 A) (@lem340958 A f lt2 x)). Qed.
Lemma lem340965 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : (term339 A lt2 x) = (term340 A lt2 x).
Proof. exact (fun_ext (fun f : A -> nat => @lem340960 A f lt2 x)). Qed.
Lemma lem340966 {A : Type'} : (@ex (A -> nat)) = (@ex (A -> nat)).
Proof. exact (eq_refl (@ex (A -> nat))). Qed.
Lemma lem340967 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : (term300 A lt2 x) = (term341 A lt2 x).
Proof. exact (MK_COMB (@lem340966 A) (@lem340965 A lt2 x)). Qed.
Lemma lem340972 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem340973 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : (term342 A lt2 x) = (term343 A lt2 x).
Proof. exact (MK_COMB (@lem340972) (@lem340967 A lt2 x)). Qed.
Lemma lem340974 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : (term298 A lt2 x) = (term344 A lt2 x).
Proof. exact (MK_COMB (@lem340902 A lt2 x) (@lem340973 A lt2 x)). Qed.
Lemma lem340977 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : (term296 A lt2 x) = (term344 A lt2 x).
Proof. exact (TRANS (@lem340764 A lt2 x) (@lem340974 A lt2 x)). Qed.
Lemma lem340978 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : (term344 A lt2 x) = (term296 A lt2 x).
Proof. exact (SYM (@lem340977 A lt2 x)). Qed.
Lemma lem340979 {A : Type'} (lt2 : type1402 A) (x' : A) (f : A -> nat) (g : A -> nat) (h1 : term61 A lt2 x' f g) : term61 A lt2 x' f g.
Proof. exact (h1). Qed.
Lemma lem340980 (_474 : nat) (_475 : Prop) (_476 : nat -> Prop) (_477 : nat) : (term345 _476 _475 _474 _477) = (term346 _474 _475 _476 _477).
Proof. exact (@lem13473 nat _474 _475 _476 _477). Qed.
Lemma lem340981 {A : Type'} (_474 : nat) (_475 : Prop) (g : A -> nat) (lt2 : type1402 A) (x : nat -> A) (x' : A) (_477 : nat) : (term347 A g lt2 x x' _475 _474 _477) = (term348 A _474 _475 g lt2 x x' _477).
Proof. exact (@lem340980 _474 _475 (term349 A g lt2 x x') _477). Qed.
Lemma lem340982 {A : Type'} (f : A -> nat) (g : A -> nat) (lt2 : type1402 A) (x : nat -> A) (x' : A) : (term350 A g f lt2 x x') = (term351 A f g lt2 x x').
Proof. exact (@lem340981 A (term352 A f lt2 x x') (term353 A x' x) g lt2 x x' (NUMERAL 0)). Qed.
Lemma lem340983 {A : Type'} (g : A -> nat) (lt2 : type1402 A) (x : nat -> A) (x' : A) : (term354 A g lt2 x x') = ((NUMERAL 0) = (term313 A g lt2 x x')).
Proof. exact (eq_refl (term354 A g lt2 x x')). Qed.
Lemma lem340984 {A : Type'} (x' : A) (x : nat -> A) : (term355 A x' x) = (term355 A x' x).
Proof. exact (eq_refl (term355 A x' x)). Qed.
Lemma lem340985 {A : Type'} (g : A -> nat) (lt2 : type1402 A) (x : nat -> A) (x' : A) : (term356 A g lt2 x x') = (term357 A g lt2 x x').
Proof. exact (MK_COMB (@lem340984 A x' x) (@lem340983 A g lt2 x x')). Qed.
Lemma lem340986 {A : Type'} (f : A -> nat) (g : A -> nat) (lt2 : type1402 A) (x : nat -> A) (x' : A) : (term358 A g f lt2 x x') = ((term352 A f lt2 x x') = (term313 A g lt2 x x')).
Proof. exact (eq_refl (term358 A g f lt2 x x')). Qed.
Lemma lem340987 {A : Type'} (x' : A) (x : nat -> A) : (term359 A x' x) = (term359 A x' x).
Proof. exact (eq_refl (term359 A x' x)). Qed.
Lemma lem340988 {A : Type'} (f : A -> nat) (g : A -> nat) (lt2 : type1402 A) (x : nat -> A) (x' : A) : (term360 A g f lt2 x x') = (term361 A f g lt2 x x').
Proof. exact (MK_COMB (@lem340987 A x' x) (@lem340986 A f g lt2 x x')). Qed.
Lemma lem340989 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem340990 {A : Type'} (f : A -> nat) (g : A -> nat) (lt2 : type1402 A) (x : nat -> A) (x' : A) : (term362 A g f lt2 x x') = (term363 A f g lt2 x x').
Proof. exact (MK_COMB (@lem340989) (@lem340988 A f g lt2 x x')). Qed.
Lemma lem340991 {A : Type'} (f : A -> nat) (g : A -> nat) (lt2 : type1402 A) (x : nat -> A) (x' : A) : (term351 A f g lt2 x x') = (term364 A f g lt2 x x').
Proof. exact (MK_COMB (@lem340990 A f g lt2 x x') (@lem340985 A g lt2 x x')). Qed.
Lemma lem340992 {A : Type'} (f : A -> nat) (g : A -> nat) (lt2 : type1402 A) (x : nat -> A) (x' : A) : (term350 A g f lt2 x x') = ((term313 A f lt2 x x') = (term313 A g lt2 x x')).
Proof. exact (eq_refl (term350 A g f lt2 x x')). Qed.
Lemma lem340993 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem340994 {A : Type'} (f : A -> nat) (g : A -> nat) (lt2 : type1402 A) (x : nat -> A) (x' : A) : (term365 A g f lt2 x x') = (term366 A f g lt2 x x').
Proof. exact (MK_COMB (@lem340993) (@lem340992 A f g lt2 x x')). Qed.
Lemma lem340995 {A : Type'} (f : A -> nat) (g : A -> nat) (lt2 : type1402 A) (x : nat -> A) (x' : A) : ((term350 A g f lt2 x x') = (term351 A f g lt2 x x')) = (((term313 A f lt2 x x') = (term313 A g lt2 x x')) = (term364 A f g lt2 x x')).
Proof. exact (MK_COMB (@lem340994 A f g lt2 x x') (@lem340991 A f g lt2 x x')). Qed.
Lemma lem340996 {A : Type'} (f : A -> nat) (g : A -> nat) (lt2 : type1402 A) (x : nat -> A) (x' : A) : ((term313 A f lt2 x x') = (term313 A g lt2 x x')) = (term364 A f g lt2 x x').
Proof. exact (EQ_MP (@lem340995 A f g lt2 x x') (@lem340982 A f g lt2 x x')). Qed.
Lemma lem340997 {A : Type'} (f : A -> nat) (g : A -> nat) (lt2 : type1402 A) (x : nat -> A) (x' : A) : (term364 A f g lt2 x x') = ((term313 A f lt2 x x') = (term313 A g lt2 x x')).
Proof. exact (SYM (@lem340996 A f g lt2 x x')). Qed.
Lemma lem340998 {A : Type'} (x' : A) (x : nat -> A) (h1 : term353 A x' x) : term353 A x' x.
Proof. exact (h1). Qed.
Lemma lem340999 {A : Type'} (x' : A) (x : nat -> A) : (term353 A x' x) = ((term353 A x' x) = True).
Proof. exact (@lem7 (term353 A x' x)). Qed.
Lemma lem341000 {A : Type'} (x' : A) (x : nat -> A) (h1 : term353 A x' x) : (term353 A x' x) = True.
Proof. exact (EQ_MP (@lem340999 A x' x) (@lem340998 A x' x h1)). Qed.
Lemma lem341001 {A : Type'} (f : A -> nat) (g : A -> nat) (lt2 : type1402 A) (x : nat -> A) (x' : A) : (term367 A f g lt2 x x') = (term367 A f g lt2 x x').
Proof. exact (eq_refl (term367 A f g lt2 x x')). Qed.
Lemma lem341002 {A : Type'} (f : A -> nat) (g : A -> nat) (lt2 : type1402 A) (x' : A) (x : nat -> A) (h1 : term353 A x' x) : (term368 A f g lt2 x' x) = (term369 A f g lt2 x x').
Proof. exact (MK_COMB (@lem341001 A f g lt2 x x') (@lem341000 A x' x h1)). Qed.
Lemma lem341003 {A : Type'} (f : A -> nat) (g : A -> nat) (lt2 : type1402 A) (x : nat -> A) (x' : A) : (term369 A f g lt2 x x') = ((term352 A f lt2 x x') = (term370 A g lt2 x x')).
Proof. exact (eq_refl (term369 A f g lt2 x x')). Qed.
Lemma lem341004 {A : Type'} (f : A -> nat) (g : A -> nat) (lt2 : type1402 A) (x' : A) (x : nat -> A) : (term371 A f g lt2 x' x) = (term371 A f g lt2 x' x).
Proof. exact (eq_refl (term371 A f g lt2 x' x)). Qed.
Lemma lem341005 {A : Type'} (f : A -> nat) (g : A -> nat) (lt2 : type1402 A) (x : nat -> A) (x' : A) : ((term368 A f g lt2 x' x) = (term369 A f g lt2 x x')) = ((term368 A f g lt2 x' x) = ((term352 A f lt2 x x') = (term370 A g lt2 x x'))).
Proof. exact (MK_COMB (@lem341004 A f g lt2 x' x) (@lem341003 A f g lt2 x x')). Qed.
Lemma lem341006 {A : Type'} (f : A -> nat) (g : A -> nat) (lt2 : type1402 A) (x : nat -> A) (x' : A) : (term368 A f g lt2 x' x) = ((term352 A f lt2 x x') = (term313 A g lt2 x x')).
Proof. exact (eq_refl (term368 A f g lt2 x' x)). Qed.
Lemma lem341007 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem341008 {A : Type'} (f : A -> nat) (g : A -> nat) (lt2 : type1402 A) (x : nat -> A) (x' : A) : (term371 A f g lt2 x' x) = (term372 A f g lt2 x x').
Proof. exact (MK_COMB (@lem341007) (@lem341006 A f g lt2 x x')). Qed.
Lemma lem341009 {A : Type'} (f : A -> nat) (g : A -> nat) (lt2 : type1402 A) (x : nat -> A) (x' : A) : ((term352 A f lt2 x x') = (term370 A g lt2 x x')) = ((term352 A f lt2 x x') = (term370 A g lt2 x x')).
Proof. exact (eq_refl ((term352 A f lt2 x x') = (term370 A g lt2 x x'))). Qed.
Lemma lem341010 {A : Type'} (f : A -> nat) (g : A -> nat) (lt2 : type1402 A) (x : nat -> A) (x' : A) : ((term368 A f g lt2 x' x) = ((term352 A f lt2 x x') = (term370 A g lt2 x x'))) = (((term352 A f lt2 x x') = (term313 A g lt2 x x')) = ((term352 A f lt2 x x') = (term370 A g lt2 x x'))).
Proof. exact (MK_COMB (@lem341008 A f g lt2 x x') (@lem341009 A f g lt2 x x')). Qed.
Lemma lem341011 {A : Type'} (f : A -> nat) (g : A -> nat) (lt2 : type1402 A) (x : nat -> A) (x' : A) : ((term368 A f g lt2 x' x) = (term369 A f g lt2 x x')) = (((term352 A f lt2 x x') = (term313 A g lt2 x x')) = ((term352 A f lt2 x x') = (term370 A g lt2 x x'))).
Proof. exact (TRANS (@lem341005 A f g lt2 x x') (@lem341010 A f g lt2 x x')). Qed.
Lemma lem341012 {A : Type'} (f : A -> nat) (g : A -> nat) (lt2 : type1402 A) (x' : A) (x : nat -> A) (h1 : term353 A x' x) : ((term352 A f lt2 x x') = (term313 A g lt2 x x')) = ((term352 A f lt2 x x') = (term370 A g lt2 x x')).
Proof. exact (EQ_MP (@lem341011 A f g lt2 x x') (@lem341002 A f g lt2 x' x h1)). Qed.
Lemma lem341013 {A : Type'} (f : A -> nat) (g : A -> nat) (lt2 : type1402 A) (x' : A) (x : nat -> A) (h1 : term353 A x' x) : ((term352 A f lt2 x x') = (term370 A g lt2 x x')) = ((term352 A f lt2 x x') = (term313 A g lt2 x x')).
Proof. exact (SYM (@lem341012 A f g lt2 x' x h1)). Qed.
Lemma lem341014 {A : Type'} (x' : A) (x : nat -> A) (h1 : term373 A x' x) : term373 A x' x.
Proof. exact (h1). Qed.
Lemma lem341015 {A : Type'} (x' : A) (x : nat -> A) : term374 A x' x.
Proof. exact (@lem82 (term353 A x' x)). Qed.
Lemma lem341016 {A : Type'} (x' : A) (x : nat -> A) (h1 : term373 A x' x) : (term353 A x' x) = False.
Proof. exact (@lem341015 A x' x (@lem341014 A x' x h1)). Qed.
Lemma lem341017 {A : Type'} (g : A -> nat) (lt2 : type1402 A) (x : nat -> A) (x' : A) : (term375 A g lt2 x x') = (term375 A g lt2 x x').
Proof. exact (eq_refl (term375 A g lt2 x x')). Qed.
Lemma lem341018 {A : Type'} (g : A -> nat) (lt2 : type1402 A) (x' : A) (x : nat -> A) (h1 : term373 A x' x) : (term376 A g lt2 x' x) = (term377 A g lt2 x x').
Proof. exact (MK_COMB (@lem341017 A g lt2 x x') (@lem341016 A x' x h1)). Qed.
Lemma lem341019 {A : Type'} (g : A -> nat) (lt2 : type1402 A) (x : nat -> A) (x' : A) : (term377 A g lt2 x x') = ((NUMERAL 0) = (term378 A g lt2 x x')).
Proof. exact (eq_refl (term377 A g lt2 x x')). Qed.
Lemma lem341020 {A : Type'} (g : A -> nat) (lt2 : type1402 A) (x' : A) (x : nat -> A) : (term379 A g lt2 x' x) = (term379 A g lt2 x' x).
Proof. exact (eq_refl (term379 A g lt2 x' x)). Qed.
Lemma lem341021 {A : Type'} (g : A -> nat) (lt2 : type1402 A) (x : nat -> A) (x' : A) : ((term376 A g lt2 x' x) = (term377 A g lt2 x x')) = ((term376 A g lt2 x' x) = ((NUMERAL 0) = (term378 A g lt2 x x'))).
Proof. exact (MK_COMB (@lem341020 A g lt2 x' x) (@lem341019 A g lt2 x x')). Qed.
Lemma lem341022 {A : Type'} (g : A -> nat) (lt2 : type1402 A) (x : nat -> A) (x' : A) : (term376 A g lt2 x' x) = ((NUMERAL 0) = (term313 A g lt2 x x')).
Proof. exact (eq_refl (term376 A g lt2 x' x)). Qed.
Lemma lem341023 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem341024 {A : Type'} (g : A -> nat) (lt2 : type1402 A) (x : nat -> A) (x' : A) : (term379 A g lt2 x' x) = (term380 A g lt2 x x').
Proof. exact (MK_COMB (@lem341023) (@lem341022 A g lt2 x x')). Qed.
Lemma lem341025 {A : Type'} (g : A -> nat) (lt2 : type1402 A) (x : nat -> A) (x' : A) : ((NUMERAL 0) = (term378 A g lt2 x x')) = ((NUMERAL 0) = (term378 A g lt2 x x')).
Proof. exact (eq_refl ((NUMERAL 0) = (term378 A g lt2 x x'))). Qed.
Lemma lem341026 {A : Type'} (g : A -> nat) (lt2 : type1402 A) (x : nat -> A) (x' : A) : ((term376 A g lt2 x' x) = ((NUMERAL 0) = (term378 A g lt2 x x'))) = (((NUMERAL 0) = (term313 A g lt2 x x')) = ((NUMERAL 0) = (term378 A g lt2 x x'))).
Proof. exact (MK_COMB (@lem341024 A g lt2 x x') (@lem341025 A g lt2 x x')). Qed.
Lemma lem341027 {A : Type'} (g : A -> nat) (lt2 : type1402 A) (x : nat -> A) (x' : A) : ((term376 A g lt2 x' x) = (term377 A g lt2 x x')) = (((NUMERAL 0) = (term313 A g lt2 x x')) = ((NUMERAL 0) = (term378 A g lt2 x x'))).
Proof. exact (TRANS (@lem341021 A g lt2 x x') (@lem341026 A g lt2 x x')). Qed.
Lemma lem341028 {A : Type'} (g : A -> nat) (lt2 : type1402 A) (x' : A) (x : nat -> A) (h1 : term373 A x' x) : ((NUMERAL 0) = (term313 A g lt2 x x')) = ((NUMERAL 0) = (term378 A g lt2 x x')).
Proof. exact (EQ_MP (@lem341027 A g lt2 x x') (@lem341018 A g lt2 x' x h1)). Qed.
Lemma lem341029 {A : Type'} (g : A -> nat) (lt2 : type1402 A) (x' : A) (x : nat -> A) (h1 : term373 A x' x) : ((NUMERAL 0) = (term378 A g lt2 x x')) = ((NUMERAL 0) = (term313 A g lt2 x x')).
Proof. exact (SYM (@lem341028 A g lt2 x' x h1)). Qed.
Lemma lem341033 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem341034 (t2 : nat) (t1 : nat) : (@COND nat True t1 t2) = t1.
Proof. exact (@lem341033 nat t2 t1). Qed.
Lemma lem341035 {A : Type'} (g : A -> nat) (lt2 : type1402 A) (x : nat -> A) (x' : A) : (term370 A g lt2 x x') = (term352 A g lt2 x x').
Proof. exact (@lem341034 (NUMERAL 0) (term352 A g lt2 x x')). Qed.
Lemma lem341036 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (x' : A) : (term381 A f lt2 x x') = (term381 A f lt2 x x').
Proof. exact (eq_refl (term381 A f lt2 x x')). Qed.
Lemma lem341037 {A : Type'} (f : A -> nat) (g : A -> nat) (lt2 : type1402 A) (x : nat -> A) (x' : A) : ((term352 A f lt2 x x') = (term370 A g lt2 x x')) = ((term352 A f lt2 x x') = (term352 A g lt2 x x')).
Proof. exact (MK_COMB (@lem341036 A f lt2 x x') (@lem341035 A g lt2 x x')). Qed.
Lemma lem341040 {A : Type'} (f : A -> nat) (g : A -> nat) (lt2 : type1402 A) (x : nat -> A) (x' : A) : ((term352 A f lt2 x x') = (term352 A g lt2 x x')) = ((term352 A f lt2 x x') = (term370 A g lt2 x x')).
Proof. exact (SYM (@lem341037 A f g lt2 x x')). Qed.
Lemma lem341044 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem341045 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem341044 nat t1 t2). Qed.
Lemma lem341046 {A : Type'} (g : A -> nat) (lt2 : type1402 A) (x : nat -> A) (x' : A) : (term378 A g lt2 x x') = (NUMERAL 0).
Proof. exact (@lem341045 (term352 A g lt2 x x') (NUMERAL 0)). Qed.
Lemma lem341047 : term382 = term382.
Proof. exact (eq_refl term382). Qed.
Lemma lem341048 {A : Type'} (g : A -> nat) (lt2 : type1402 A) (x : nat -> A) (x' : A) : ((NUMERAL 0) = (term378 A g lt2 x x')) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem341047) (@lem341046 A g lt2 x x')). Qed.
Lemma lem341050 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem341051 (x : nat) : (x = x) = True.
Proof. exact (@lem341050 nat x). Qed.
Lemma lem341052 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem341051 (NUMERAL 0)). Qed.
Lemma lem341053 {A : Type'} (g : A -> nat) (lt2 : type1402 A) (x : nat -> A) (x' : A) : ((NUMERAL 0) = (term378 A g lt2 x x')) = True.
Proof. exact (TRANS (@lem341048 A g lt2 x x') (@lem341052)). Qed.
Lemma lem341054 {A : Type'} (g : A -> nat) (lt2 : type1402 A) (x : nat -> A) (x' : A) : True = ((NUMERAL 0) = (term378 A g lt2 x x')).
Proof. exact (SYM (@lem341053 A g lt2 x x')). Qed.
Lemma lem341055 {A : Type'} (g : A -> nat) (lt2 : type1402 A) (x : nat -> A) (x' : A) : (NUMERAL 0) = (term378 A g lt2 x x').
Proof. exact (EQ_MP (@lem341054 A g lt2 x x') (@lem0)). Qed.
Lemma lem341056 {A : Type'} (x' : A) (x : nat -> A) (p : nat) (h1 : x' = (x p)) : x' = (x p).
Proof. exact (h1). Qed.
Lemma lem341057 {A : Type'} (f : A -> nat) (g : A -> nat) (lt2 : type1402 A) (x : nat -> A) : (term383 A f g lt2 x) = (term383 A f g lt2 x).
Proof. exact (eq_refl (term383 A f g lt2 x)). Qed.
Lemma lem341058 {A : Type'} (f : A -> nat) (g : A -> nat) (lt2 : type1402 A) (x' : A) (x : nat -> A) (p : nat) (h1 : x' = (x p)) : (term384 A f g lt2 x x') = (term385 A f g lt2 x p).
Proof. exact (MK_COMB (@lem341057 A f g lt2 x) (@lem341056 A x' x p h1)). Qed.
Lemma lem341059 {A : Type'} (f : A -> nat) (g : A -> nat) (lt2 : type1402 A) (x : nat -> A) (p : nat) : (term385 A f g lt2 x p) = ((term386 A f lt2 x p) = (term386 A g lt2 x p)).
Proof. exact (eq_refl (term385 A f g lt2 x p)). Qed.
Lemma lem341060 {A : Type'} (f : A -> nat) (g : A -> nat) (lt2 : type1402 A) (x : nat -> A) (x' : A) : (term387 A f g lt2 x x') = (term387 A f g lt2 x x').
Proof. exact (eq_refl (term387 A f g lt2 x x')). Qed.
Lemma lem341061 {A : Type'} (x' : A) (f : A -> nat) (g : A -> nat) (lt2 : type1402 A) (x : nat -> A) (p : nat) : ((term384 A f g lt2 x x') = (term385 A f g lt2 x p)) = ((term384 A f g lt2 x x') = ((term386 A f lt2 x p) = (term386 A g lt2 x p))).
Proof. exact (MK_COMB (@lem341060 A f g lt2 x x') (@lem341059 A f g lt2 x p)). Qed.
Lemma lem341062 {A : Type'} (f : A -> nat) (g : A -> nat) (lt2 : type1402 A) (x : nat -> A) (x' : A) : (term384 A f g lt2 x x') = ((term352 A f lt2 x x') = (term352 A g lt2 x x')).
Proof. exact (eq_refl (term384 A f g lt2 x x')). Qed.
Lemma lem341063 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem341064 {A : Type'} (f : A -> nat) (g : A -> nat) (lt2 : type1402 A) (x : nat -> A) (x' : A) : (term387 A f g lt2 x x') = (term388 A f g lt2 x x').
Proof. exact (MK_COMB (@lem341063) (@lem341062 A f g lt2 x x')). Qed.
Lemma lem341065 {A : Type'} (f : A -> nat) (g : A -> nat) (lt2 : type1402 A) (x : nat -> A) (p : nat) : ((term386 A f lt2 x p) = (term386 A g lt2 x p)) = ((term386 A f lt2 x p) = (term386 A g lt2 x p)).
Proof. exact (eq_refl ((term386 A f lt2 x p) = (term386 A g lt2 x p))). Qed.
Lemma lem341066 {A : Type'} (x' : A) (f : A -> nat) (g : A -> nat) (lt2 : type1402 A) (x : nat -> A) (p : nat) : ((term384 A f g lt2 x x') = ((term386 A f lt2 x p) = (term386 A g lt2 x p))) = (((term352 A f lt2 x x') = (term352 A g lt2 x x')) = ((term386 A f lt2 x p) = (term386 A g lt2 x p))).
Proof. exact (MK_COMB (@lem341064 A f g lt2 x x') (@lem341065 A f g lt2 x p)). Qed.
Lemma lem341067 {A : Type'} (x' : A) (f : A -> nat) (g : A -> nat) (lt2 : type1402 A) (x : nat -> A) (p : nat) : ((term384 A f g lt2 x x') = (term385 A f g lt2 x p)) = (((term352 A f lt2 x x') = (term352 A g lt2 x x')) = ((term386 A f lt2 x p) = (term386 A g lt2 x p))).
Proof. exact (TRANS (@lem341061 A x' f g lt2 x p) (@lem341066 A x' f g lt2 x p)). Qed.
Lemma lem341068 {A : Type'} (f : A -> nat) (g : A -> nat) (lt2 : type1402 A) (x' : A) (x : nat -> A) (p : nat) (h1 : x' = (x p)) : ((term352 A f lt2 x x') = (term352 A g lt2 x x')) = ((term386 A f lt2 x p) = (term386 A g lt2 x p)).
Proof. exact (EQ_MP (@lem341067 A x' f g lt2 x p) (@lem341058 A f g lt2 x' x p h1)). Qed.
Lemma lem341069 {A : Type'} (f : A -> nat) (g : A -> nat) (lt2 : type1402 A) (x' : A) (x : nat -> A) (p : nat) (h1 : x' = (x p)) : ((term386 A f lt2 x p) = (term386 A g lt2 x p)) = ((term352 A f lt2 x x') = (term352 A g lt2 x x')).
Proof. exact (SYM (@lem341068 A f g lt2 x' x p h1)). Qed.
Lemma lem341111 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (h1 : term19 A lt2 x) : term19 A lt2 x.
Proof. exact (h1). Qed.
Lemma lem341112 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (g : A -> nat) : (term389 A lt2 f g) = (term389 A lt2 f g).
Proof. exact (eq_refl (term389 A lt2 f g)). Qed.
Lemma lem341113 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (g : A -> nat) (x' : A) (x : nat -> A) (p : nat) (h1 : x' = (x p)) : (term390 A lt2 f g x') = (term391 A lt2 f g x p).
Proof. exact (MK_COMB (@lem341112 A lt2 f g) (@lem341056 A x' x p h1)). Qed.
Lemma lem341114 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (p : nat) (f : A -> nat) (g : A -> nat) : (term391 A lt2 f g x p) = (term392 A lt2 x p f g).
Proof. exact (eq_refl (term391 A lt2 f g x p)). Qed.
Lemma lem341115 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (g : A -> nat) (x' : A) : (term393 A lt2 f g x') = (term393 A lt2 f g x').
Proof. exact (eq_refl (term393 A lt2 f g x')). Qed.
Lemma lem341116 {A : Type'} (x' : A) (lt2 : type1402 A) (x : nat -> A) (p : nat) (f : A -> nat) (g : A -> nat) : ((term390 A lt2 f g x') = (term391 A lt2 f g x p)) = ((term390 A lt2 f g x') = (term392 A lt2 x p f g)).
Proof. exact (MK_COMB (@lem341115 A lt2 f g x') (@lem341114 A lt2 x p f g)). Qed.
Lemma lem341117 {A : Type'} (lt2 : type1402 A) (x' : A) (f : A -> nat) (g : A -> nat) : (term390 A lt2 f g x') = (term61 A lt2 x' f g).
Proof. exact (eq_refl (term390 A lt2 f g x')). Qed.
Lemma lem341118 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem341119 {A : Type'} (lt2 : type1402 A) (x' : A) (f : A -> nat) (g : A -> nat) : (term393 A lt2 f g x') = (term394 A lt2 x' f g).
Proof. exact (MK_COMB (@lem341118) (@lem341117 A lt2 x' f g)). Qed.
Lemma lem341120 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (p : nat) (f : A -> nat) (g : A -> nat) : (term392 A lt2 x p f g) = (term392 A lt2 x p f g).
Proof. exact (eq_refl (term392 A lt2 x p f g)). Qed.
Lemma lem341121 {A : Type'} (x' : A) (lt2 : type1402 A) (x : nat -> A) (p : nat) (f : A -> nat) (g : A -> nat) : ((term390 A lt2 f g x') = (term392 A lt2 x p f g)) = ((term61 A lt2 x' f g) = (term392 A lt2 x p f g)).
Proof. exact (MK_COMB (@lem341119 A lt2 x' f g) (@lem341120 A lt2 x p f g)). Qed.
Lemma lem341122 {A : Type'} (x' : A) (lt2 : type1402 A) (x : nat -> A) (p : nat) (f : A -> nat) (g : A -> nat) : ((term390 A lt2 f g x') = (term391 A lt2 f g x p)) = ((term61 A lt2 x' f g) = (term392 A lt2 x p f g)).
Proof. exact (TRANS (@lem341116 A x' lt2 x p f g) (@lem341121 A x' lt2 x p f g)). Qed.
Lemma lem341123 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (g : A -> nat) (x' : A) (x : nat -> A) (p : nat) (h1 : x' = (x p)) : (term61 A lt2 x' f g) = (term392 A lt2 x p f g).
Proof. exact (EQ_MP (@lem341122 A x' lt2 x p f g) (@lem341113 A lt2 f g x' x p h1)). Qed.
Lemma lem341124 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (g : A -> nat) (x' : A) (x : nat -> A) (p : nat) (h1 : term61 A lt2 x' f g) (h2 : x' = (x p)) : term392 A lt2 x p f g.
Proof. exact (EQ_MP (@lem341123 A lt2 f g x' x p h2) (@lem340979 A lt2 x' f g h1)). Qed.
Lemma lem341138 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem341139 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (p : nat) (f : A -> nat) (g : A -> nat) (h1 : term392 A lt2 x p f g) : term392 A lt2 x p f g.
Proof. exact (h1). Qed.
Lemma lem341140 {A : Type'} (z : A) (lt2 : type1402 A) (x : nat -> A) (p : nat) (f : A -> nat) (g : A -> nat) (h1 : term392 A lt2 x p f g) : term395 A lt2 x p f g z.
Proof. exact (@lem341139 A lt2 x p f g h1 z). Qed.
Lemma lem341141 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (p : nat) (f : A -> nat) (g : A -> nat) (z : A) : (term395 A lt2 x p f g z) = (term396 A lt2 x p f g z).
Proof. exact (eq_refl (term395 A lt2 x p f g z)). Qed.
Lemma lem341142 {A : Type'} (z : A) (lt2 : type1402 A) (x : nat -> A) (p : nat) (f : A -> nat) (g : A -> nat) (h1 : term392 A lt2 x p f g) : term396 A lt2 x p f g z.
Proof. exact (EQ_MP (@lem341141 A lt2 x p f g z) (@lem341140 A z lt2 x p f g h1)). Qed.
Lemma lem341143 {A : Type'} (lt2 : type1402 A) (z : A) (x : nat -> A) (p : nat) (h1 : term397 A lt2 z x p) : term397 A lt2 z x p.
Proof. exact (h1). Qed.
Lemma lem341144 {A : Type'} (f : A -> nat) (g : A -> nat) (lt2 : type1402 A) (z : A) (x : nat -> A) (p : nat) (h1 : term392 A lt2 x p f g) (h2 : term397 A lt2 z x p) : (f z) = (g z).
Proof. exact (@lem341142 A z lt2 x p f g h1 (@lem341143 A lt2 z x p h2)). Qed.
Lemma lem341145 {A : Type'} (f : A -> nat) (g : A -> nat) (lt2 : type1402 A) (z : A) (x : nat -> A) (p : nat) (h1 : term397 A lt2 z x p) : term398 A lt2 x p f g z.
Proof. exact (fun h0 : term392 A lt2 x p f g => @lem341144 A f g lt2 z x p h0 h1). Qed.
Lemma lem341146 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (p : nat) (f : A -> nat) (g : A -> nat) (h1 : term392 A lt2 x p f g) : term392 A lt2 x p f g.
Proof. exact (h1). Qed.
Lemma lem341147 {A : Type'} (f : A -> nat) (g : A -> nat) (lt2 : type1402 A) (z : A) (x : nat -> A) (p : nat) (h1 : term392 A lt2 x p f g) (h2 : term397 A lt2 z x p) : (f z) = (g z).
Proof. exact (@lem341145 A f g lt2 z x p h2 (@lem341146 A lt2 x p f g h1)). Qed.
Lemma lem341148 {A : Type'} (z : A) (lt2 : type1402 A) (x : nat -> A) (p : nat) (f : A -> nat) (g : A -> nat) (h1 : term392 A lt2 x p f g) : term396 A lt2 x p f g z.
Proof. exact (fun h0 : term397 A lt2 z x p => @lem341147 A f g lt2 z x p h1 h0). Qed.
Lemma lem341149 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (p : nat) (f : A -> nat) (g : A -> nat) (h1 : term392 A lt2 x p f g) : term392 A lt2 x p f g.
Proof. exact (fun z : A => @lem341148 A z lt2 x p f g h1). Qed.
Lemma lem341150 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (p : nat) (f : A -> nat) (g : A -> nat) : term399 A lt2 x p f g.
Proof. exact (fun h0 : term392 A lt2 x p f g => @lem341149 A lt2 x p f g h0). Qed.
Lemma lem341151 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (g : A -> nat) (x' : A) (x : nat -> A) (p : nat) (h1 : term61 A lt2 x' f g) (h2 : x' = (x p)) : term392 A lt2 x p f g.
Proof. exact (@lem341150 A lt2 x p f g (@lem341124 A lt2 f g x' x p h1 h2)). Qed.
Lemma lem341152 {A : Type'} (z : A) (lt2 : type1402 A) (f : A -> nat) (g : A -> nat) (x' : A) (x : nat -> A) (p : nat) (h1 : term61 A lt2 x' f g) (h2 : x' = (x p)) : term395 A lt2 x p f g z.
Proof. exact (@lem341151 A lt2 f g x' x p h1 h2 z). Qed.
Lemma lem341153 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (p : nat) (f : A -> nat) (g : A -> nat) (z : A) : (term395 A lt2 x p f g z) = (term396 A lt2 x p f g z).
Proof. exact (eq_refl (term395 A lt2 x p f g z)). Qed.
Lemma lem341156 {A : Type'} (z : A) (lt2 : type1402 A) (f : A -> nat) (g : A -> nat) (x' : A) (x : nat -> A) (p : nat) (h1 : term61 A lt2 x' f g) (h2 : x' = (x p)) : term396 A lt2 x p f g z.
Proof. exact (EQ_MP (@lem341153 A lt2 x p f g z) (@lem341152 A z lt2 f g x' x p h1 h2)). Qed.
Lemma lem341157 {A : Type'} (z : A) (lt2 : type1402 A) (f : A -> nat) (g : A -> nat) (x' : A) (x : nat -> A) (p : nat) (h1 : term61 A lt2 x' f g) (h2 : x' = (x p)) : term396 A lt2 x p f g z.
Proof. exact (@lem341156 A z lt2 f g x' x p h1 h2). Qed.
Lemma lem341158 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (g : A -> nat) (x' : A) (x : nat -> A) (p : nat) (h1 : term61 A lt2 x' f g) (h2 : x' = (x p)) : term400 A f g lt2 x p.
Proof. exact (@lem341157 A (term401 A lt2 x p) lt2 f g x' x p h1 h2). Qed.
Lemma lem341166 {A : Type'} (n : nat) (lt2 : type1402 A) (x : nat -> A) (h1 : term19 A lt2 x) : term402 A lt2 x n.
Proof. exact (@lem341111 A lt2 x h1 n). Qed.
Lemma lem341167 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) : (term402 A lt2 x n) = (term24 A lt2 x n).
Proof. exact (eq_refl (term402 A lt2 x n)). Qed.
Lemma lem341170 {A : Type'} (n : nat) (lt2 : type1402 A) (x : nat -> A) (h1 : term19 A lt2 x) : term24 A lt2 x n.
Proof. exact (EQ_MP (@lem341167 A lt2 x n) (@lem341166 A n lt2 x h1)). Qed.
Lemma lem341171 {A : Type'} (p : nat) (lt2 : type1402 A) (x : nat -> A) (h1 : term19 A lt2 x) : term24 A lt2 x p.
Proof. exact (@lem341170 A p lt2 x h1). Qed.
Lemma lem341172 {A : Type'} (f : A -> nat) (g : A -> nat) (lt2 : type1402 A) (x' : A) (x : nat -> A) (p : nat) (h1 : term61 A lt2 x' f g) (h2 : term19 A lt2 x) (h3 : x' = (x p)) : (term403 A f lt2 x p) = (term403 A g lt2 x p).
Proof. exact (@lem341158 A lt2 f g x' x p h1 h3 (@lem341171 A p lt2 x h2)). Qed.
Lemma lem341173 {A : Type'} (f : A -> nat) (g : A -> nat) (lt2 : type1402 A) (x' : A) (x : nat -> A) (p : nat) (h1 : term61 A lt2 x' f g) (h2 : term19 A lt2 x) (h3 : x' = (x p)) : (term386 A f lt2 x p) = (term386 A g lt2 x p).
Proof. exact (MK_COMB (@lem341138) (@lem341172 A f g lt2 x' x p h1 h2 h3)). Qed.
Lemma lem341174 {A : Type'} (f : A -> nat) (g : A -> nat) (lt2 : type1402 A) (x' : A) (x : nat -> A) (p : nat) (h1 : term61 A lt2 x' f g) (h2 : term19 A lt2 x) (h3 : x' = (x p)) : (term19 A lt2 x) = ((term386 A f lt2 x p) = (term386 A g lt2 x p)).
Proof. exact (prop_ext (fun h4 : term19 A lt2 x => @lem341173 A f g lt2 x' x p h1 h2 h3) (fun h4 : (term386 A f lt2 x p) = (term386 A g lt2 x p) => @lem341111 A lt2 x h2)). Qed.
Lemma lem341175 {A : Type'} (f : A -> nat) (g : A -> nat) (lt2 : type1402 A) (x' : A) (x : nat -> A) (p : nat) (h1 : term61 A lt2 x' f g) (h2 : term19 A lt2 x) (h3 : x' = (x p)) : (term386 A f lt2 x p) = (term386 A g lt2 x p).
Proof. exact (EQ_MP (@lem341174 A f g lt2 x' x p h1 h2 h3) (@lem341111 A lt2 x h2)). Qed.
Lemma lem341176 {A : Type'} (f : A -> nat) (g : A -> nat) (lt2 : type1402 A) (x' : A) (x : nat -> A) (p : nat) (h1 : term61 A lt2 x' f g) (h2 : term19 A lt2 x) (h3 : x' = (x p)) : (term352 A f lt2 x x') = (term352 A g lt2 x x').
Proof. exact (EQ_MP (@lem341069 A f g lt2 x' x p h3) (@lem341175 A f g lt2 x' x p h1 h2 h3)). Qed.
Lemma lem341177 {A : Type'} (f : A -> nat) (g : A -> nat) (lt2 : type1402 A) (x' : A) (x : nat -> A) (h1 : term61 A lt2 x' f g) (h2 : term19 A lt2 x) (h3 : term353 A x' x) : (term352 A f lt2 x x') = (term352 A g lt2 x x').
Proof. exact (ex_elim (@lem340998 A x' x h3) (fun p : nat => fun h0 : term404 A x' x p => @lem341176 A f g lt2 x' x p h1 h2 h0)). Qed.
Lemma lem341178 {A : Type'} (f : A -> nat) (g : A -> nat) (lt2 : type1402 A) (x' : A) (x : nat -> A) (h1 : term61 A lt2 x' f g) (h2 : term19 A lt2 x) (h3 : term353 A x' x) : (term352 A f lt2 x x') = (term370 A g lt2 x x').
Proof. exact (EQ_MP (@lem341040 A f g lt2 x x') (@lem341177 A f g lt2 x' x h1 h2 h3)). Qed.
Lemma lem341179 {A : Type'} (g : A -> nat) (lt2 : type1402 A) (x' : A) (x : nat -> A) (h1 : term373 A x' x) : (NUMERAL 0) = (term313 A g lt2 x x').
Proof. exact (EQ_MP (@lem341029 A g lt2 x' x h1) (@lem341055 A g lt2 x x')). Qed.
Lemma lem341180 {A : Type'} (g : A -> nat) (lt2 : type1402 A) (x' : A) (x : nat -> A) (h1 : term373 A x' x) : (term373 A x' x) = ((NUMERAL 0) = (term313 A g lt2 x x')).
Proof. exact (prop_ext (fun h2 : term373 A x' x => @lem341179 A g lt2 x' x h1) (fun h2 : (NUMERAL 0) = (term313 A g lt2 x x') => @lem341014 A x' x h1)). Qed.
Lemma lem341181 {A : Type'} (g : A -> nat) (lt2 : type1402 A) (x' : A) (x : nat -> A) (h1 : term373 A x' x) : (NUMERAL 0) = (term313 A g lt2 x x').
Proof. exact (EQ_MP (@lem341180 A g lt2 x' x h1) (@lem341014 A x' x h1)). Qed.
Lemma lem341182 {A : Type'} (g : A -> nat) (lt2 : type1402 A) (x : nat -> A) (x' : A) : term357 A g lt2 x x'.
Proof. exact (fun h0 : term373 A x' x => @lem341181 A g lt2 x' x h0). Qed.
Lemma lem341183 {A : Type'} (f : A -> nat) (g : A -> nat) (lt2 : type1402 A) (x' : A) (x : nat -> A) (h1 : term61 A lt2 x' f g) (h2 : term19 A lt2 x) (h3 : term353 A x' x) : (term352 A f lt2 x x') = (term313 A g lt2 x x').
Proof. exact (EQ_MP (@lem341013 A f g lt2 x' x h3) (@lem341178 A f g lt2 x' x h1 h2 h3)). Qed.
Lemma lem341184 {A : Type'} (f : A -> nat) (g : A -> nat) (lt2 : type1402 A) (x' : A) (x : nat -> A) (h1 : term61 A lt2 x' f g) (h2 : term19 A lt2 x) (h3 : term353 A x' x) : (term353 A x' x) = ((term352 A f lt2 x x') = (term313 A g lt2 x x')).
Proof. exact (prop_ext (fun h4 : term353 A x' x => @lem341183 A f g lt2 x' x h1 h2 h3) (fun h4 : (term352 A f lt2 x x') = (term313 A g lt2 x x') => @lem340998 A x' x h3)). Qed.
Lemma lem341185 {A : Type'} (f : A -> nat) (g : A -> nat) (lt2 : type1402 A) (x' : A) (x : nat -> A) (h1 : term61 A lt2 x' f g) (h2 : term19 A lt2 x) (h3 : term353 A x' x) : (term352 A f lt2 x x') = (term313 A g lt2 x x').
Proof. exact (EQ_MP (@lem341184 A f g lt2 x' x h1 h2 h3) (@lem340998 A x' x h3)). Qed.
Lemma lem341186 {A : Type'} (x' : A) (f : A -> nat) (g : A -> nat) (lt2 : type1402 A) (x : nat -> A) (h1 : term61 A lt2 x' f g) (h2 : term19 A lt2 x) : term361 A f g lt2 x x'.
Proof. exact (fun h0 : term353 A x' x => @lem341185 A f g lt2 x' x h1 h2 h0). Qed.
Lemma lem341187 {A : Type'} (x' : A) (f : A -> nat) (g : A -> nat) (lt2 : type1402 A) (x : nat -> A) (h1 : term61 A lt2 x' f g) (h2 : term19 A lt2 x) : term364 A f g lt2 x x'.
Proof. exact (conj (@lem341186 A x' f g lt2 x h1 h2) (@lem341182 A g lt2 x x')). Qed.
Lemma lem341188 {A : Type'} (x' : A) (f : A -> nat) (g : A -> nat) (lt2 : type1402 A) (x : nat -> A) (h1 : term61 A lt2 x' f g) (h2 : term19 A lt2 x) : (term313 A f lt2 x x') = (term313 A g lt2 x x').
Proof. exact (EQ_MP (@lem340997 A f g lt2 x x') (@lem341187 A x' f g lt2 x h1 h2)). Qed.
Lemma lem341189 {A : Type'} (x' : A) (f : A -> nat) (g : A -> nat) (lt2 : type1402 A) (x : nat -> A) (h1 : term61 A lt2 x' f g) (h2 : term19 A lt2 x) : (term61 A lt2 x' f g) = ((term313 A f lt2 x x') = (term313 A g lt2 x x')).
Proof. exact (prop_ext (fun h3 : term61 A lt2 x' f g => @lem341188 A x' f g lt2 x h1 h2) (fun h3 : (term313 A f lt2 x x') = (term313 A g lt2 x x') => @lem340979 A lt2 x' f g h1)). Qed.
Lemma lem341190 {A : Type'} (x' : A) (f : A -> nat) (g : A -> nat) (lt2 : type1402 A) (x : nat -> A) (h1 : term61 A lt2 x' f g) (h2 : term19 A lt2 x) : (term313 A f lt2 x x') = (term313 A g lt2 x x').
Proof. exact (EQ_MP (@lem341189 A x' f g lt2 x h1 h2) (@lem340979 A lt2 x' f g h1)). Qed.
Lemma lem341191 {A : Type'} (f : A -> nat) (g : A -> nat) (x' : A) (lt2 : type1402 A) (x : nat -> A) (h1 : term19 A lt2 x) : term320 A f g lt2 x x'.
Proof. exact (fun h0 : term61 A lt2 x' f g => @lem341190 A x' f g lt2 x h0 h1). Qed.
Lemma lem341196 {A : Type'} (f : A -> nat) (g : A -> nat) (lt2 : type1402 A) (x : nat -> A) (h1 : term19 A lt2 x) : term324 A f g lt2 x.
Proof. exact (fun x' : A => @lem341191 A f g x' lt2 x h1). Qed.
Lemma lem341201 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (h1 : term19 A lt2 x) : term328 A f lt2 x.
Proof. exact (fun g : A -> nat => @lem341196 A f g lt2 x h1). Qed.
Lemma lem341206 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (h1 : term19 A lt2 x) : term331 A lt2 x.
Proof. exact (fun f : A -> nat => @lem341201 A f lt2 x h1). Qed.
Lemma lem341207 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (h1 : term341 A lt2 x) : term341 A lt2 x.
Proof. exact (h1). Qed.
Lemma lem341208 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (h1 : term338 A f lt2 x) : term338 A f lt2 x.
Proof. exact (h1). Qed.
Lemma lem341209 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (h1 : term338 A f lt2 x) : term338 A f lt2 x.
Proof. exact (h1). Qed.
Lemma lem341210 {A : Type'} (n : nat) (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (h1 : term338 A f lt2 x) : term405 A f lt2 x n.
Proof. exact (@lem341209 A f lt2 x h1 (x n)). Qed.
Lemma lem341211 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (n : nat) : (term405 A f lt2 x n) = ((term406 A f x n) = (term407 A f lt2 x n)).
Proof. exact (eq_refl (term405 A f lt2 x n)). Qed.
Lemma lem341212 {A : Type'} (n : nat) (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (h1 : term338 A f lt2 x) : (term406 A f x n) = (term407 A f lt2 x n).
Proof. exact (EQ_MP (@lem341211 A f lt2 x n) (@lem341210 A n f lt2 x h1)). Qed.
Lemma lem341213 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (h1 : term338 A f lt2 x) : term408 A f lt2 x.
Proof. exact (fun n : nat => @lem341212 A n f lt2 x h1). Qed.
Lemma lem341214 {A : Type'} (x : nat -> A) (h1 : term409 A x) : term409 A x.
Proof. exact (h1). Qed.
Lemma lem341215 {A : Type'} (n : nat) (x : nat -> A) (h1 : term409 A x) : term410 A x n.
Proof. exact (@lem341214 A x h1 n). Qed.
Lemma lem341216 {A : Type'} (n : nat) (x : nat -> A) : (term410 A x n) = (term411 A n x).
Proof. exact (eq_refl (term410 A x n)). Qed.
Lemma lem341217 {A : Type'} (n : nat) (x : nat -> A) (h1 : term409 A x) : term411 A n x.
Proof. exact (EQ_MP (@lem341216 A n x) (@lem341215 A n x h1)). Qed.
Lemma lem341218 {A : Type'} (n : nat) (x : nat -> A) : (term411 A n x) = ((term411 A n x) = True).
Proof. exact (@lem7 (term411 A n x)). Qed.
Lemma lem341221 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem341222 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) : (term412 A f lt2 x) = (term413 A f lt2 x).
Proof. exact (@lem341221 (term408 A f lt2 x)). Qed.
Lemma lem341230 {A : Type'} (n : nat) (x : nat -> A) (h1 : term409 A x) : (term411 A n x) = True.
Proof. exact (EQ_MP (@lem341218 A n x) (@lem341217 A n x h1)). Qed.
Lemma lem341231 : (@COND nat) = (@COND nat).
Proof. exact (eq_refl (@COND nat)). Qed.
Lemma lem341232 {A : Type'} (n : nat) (x : nat -> A) (h1 : term409 A x) : (term414 A n x) = (@COND nat True).
Proof. exact (MK_COMB (@lem341231) (@lem341230 A n x h1)). Qed.
Lemma lem341233 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (n : nat) : (term386 A f lt2 x n) = (term386 A f lt2 x n).
Proof. exact (eq_refl (term386 A f lt2 x n)). Qed.
Lemma lem341234 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (n : nat) (x : nat -> A) (h1 : term409 A x) : (term415 A f lt2 x n) = (term416 A f lt2 x n).
Proof. exact (MK_COMB (@lem341232 A n x h1) (@lem341233 A f lt2 x n)). Qed.
Lemma lem341235 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem341236 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (n : nat) (x : nat -> A) (h1 : term409 A x) : (term407 A f lt2 x n) = (term417 A f lt2 x n).
Proof. exact (MK_COMB (@lem341234 A f lt2 n x h1) (@lem341235)). Qed.
Lemma lem341238 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem341239 (t2 : nat) (t1 : nat) : (@COND nat True t1 t2) = t1.
Proof. exact (@lem341238 nat t2 t1). Qed.
Lemma lem341240 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (n : nat) : (term417 A f lt2 x n) = (term386 A f lt2 x n).
Proof. exact (@lem341239 (NUMERAL 0) (term386 A f lt2 x n)). Qed.
Lemma lem341241 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (n : nat) (x : nat -> A) (h1 : term409 A x) : (term407 A f lt2 x n) = (term386 A f lt2 x n).
Proof. exact (TRANS (@lem341236 A f lt2 n x h1) (@lem341240 A f lt2 x n)). Qed.
Lemma lem341242 {A : Type'} (f : A -> nat) (x : nat -> A) (n : nat) : (term418 A f x n) = (term418 A f x n).
Proof. exact (eq_refl (term418 A f x n)). Qed.
Lemma lem341243 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (n : nat) (x : nat -> A) (h1 : term409 A x) : ((term406 A f x n) = (term407 A f lt2 x n)) = ((term406 A f x n) = (term386 A f lt2 x n)).
Proof. exact (MK_COMB (@lem341242 A f x n) (@lem341241 A f lt2 n x h1)). Qed.
Lemma lem341246 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (h1 : term409 A x) : (term419 A f lt2 x) = (term420 A f lt2 x).
Proof. exact (fun_ext (fun n : nat => @lem341243 A f lt2 n x h1)). Qed.
Lemma lem341247 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem341248 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (h1 : term409 A x) : (term408 A f lt2 x) = (term421 A f lt2 x).
Proof. exact (MK_COMB (@lem341247) (@lem341246 A f lt2 x h1)). Qed.
Lemma lem341253 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem341254 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (h1 : term409 A x) : (term413 A f lt2 x) = (term422 A f lt2 x).
Proof. exact (MK_COMB (@lem341253) (@lem341248 A f lt2 x h1)). Qed.
Lemma lem341255 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (h1 : term409 A x) : (term412 A f lt2 x) = (term422 A f lt2 x).
Proof. exact (TRANS (@lem341222 A f lt2 x) (@lem341254 A f lt2 x h1)). Qed.
Lemma lem341256 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (h1 : term409 A x) : (term422 A f lt2 x) = (term412 A f lt2 x).
Proof. exact (SYM (@lem341255 A f lt2 x h1)). Qed.
Lemma lem341258 (p : Prop) : p = (term30 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem341259 {A : Type'} (x : nat -> A) : (term409 A x) = (term423 A x).
Proof. exact (@lem341258 (term409 A x)). Qed.
Lemma lem341260 {A : Type'} (x : nat -> A) : (term423 A x) = (term409 A x).
Proof. exact (SYM (@lem341259 A x)). Qed.
Lemma lem341261 {A : Type'} (x : nat -> A) (h1 : term424 A x) : term424 A x.
Proof. exact (h1). Qed.
Lemma lem341264 {A : Type'} (x : nat -> A) (h1 : term423 A x) : term423 A x.
Proof. exact (h1). Qed.
Lemma lem341265 {A : Type'} (x : nat -> A) : term425 A x.
Proof. exact (fun h0 : term423 A x => @lem341264 A x h0). Qed.
Lemma lem341266 {A : Type'} (x : nat -> A) (h1 : term425 A x) : term425 A x.
Proof. exact (h1). Qed.
Lemma lem341267 {A : Type'} (x : nat -> A) (h1 : term423 A x) : term423 A x.
Proof. exact (h1). Qed.
Lemma lem341268 {A : Type'} (x : nat -> A) (h1 : term423 A x) (h2 : term425 A x) : term423 A x.
Proof. exact (@lem341266 A x h2 (@lem341267 A x h1)). Qed.
Lemma lem341269 {A : Type'} (x : nat -> A) (h1 : term423 A x) : term426 A x.
Proof. exact (fun h0 : term425 A x => @lem341268 A x h1 h0). Qed.
Lemma lem341270 {A : Type'} (x : nat -> A) (h1 : term425 A x) : term425 A x.
Proof. exact (h1). Qed.
Lemma lem341271 {A : Type'} (x : nat -> A) (h1 : term423 A x) (h2 : term425 A x) : term423 A x.
Proof. exact (@lem341269 A x h1 (@lem341270 A x h2)). Qed.
Lemma lem341272 {A : Type'} (x : nat -> A) (h1 : term425 A x) : term425 A x.
Proof. exact (fun h0 : term423 A x => @lem341271 A x h0 h1). Qed.
Lemma lem341273 {A : Type'} (x : nat -> A) : term427 A x.
Proof. exact (fun h0 : term425 A x => @lem341272 A x h0). Qed.
Lemma lem341276 {A : Type'} (x : nat -> A) : term425 A x.
Proof. exact (@lem341273 A x (@lem341265 A x)). Qed.
Lemma lem341282 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem341283 {A : Type'} (x : nat -> A) : (term423 A x) = (term428 A x).
Proof. exact (@lem341282 (term424 A x)). Qed.
Lemma lem341285 (t : Prop) : (term38 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem341286 {A : Type'} (x : nat -> A) : (term428 A x) = (term409 A x).
Proof. exact (@lem341285 (term409 A x)). Qed.
Lemma lem341291 {A : Type'} (x : nat -> A) : (term423 A x) = (term409 A x).
Proof. exact (TRANS (@lem341283 A x) (@lem341286 A x)). Qed.
Lemma lem341296 {A : Type'} : (term429 A) = (term430 A).
Proof. exact (fun_ext (fun x : nat -> A => @lem341291 A x)). Qed.
Lemma lem341297 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem341306 {A : Type'} : (term431 A) = (term432 A).
Proof. exact (MK_COMB (@lem341297 A) (@lem341296 A)). Qed.
Lemma lem341307 {A : Type'} (n : nat) (x : nat -> A) (p : nat) : ((x n) = (x p)) = ((x n) = (x p)).
Proof. exact (eq_refl ((x n) = (x p))). Qed.
Lemma lem341308 {A : Type'} (n : nat) (x : nat -> A) : (term433 A n x) = (term433 A n x).
Proof. exact (fun_ext (fun p : nat => @lem341307 A n x p)). Qed.
Lemma lem341309 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem341310 {A : Type'} (n : nat) (x : nat -> A) : (term411 A n x) = (term411 A n x).
Proof. exact (MK_COMB (@lem341309) (@lem341308 A n x)). Qed.
Lemma lem341311 {A : Type'} (x : nat -> A) : (term434 A x) = (term434 A x).
Proof. exact (fun_ext (fun n : nat => @lem341310 A n x)). Qed.
Lemma lem341312 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem341313 {A : Type'} (x : nat -> A) : (term409 A x) = (term409 A x).
Proof. exact (MK_COMB (@lem341312) (@lem341311 A x)). Qed.
Lemma lem341314 {A : Type'} : (term430 A) = (term430 A).
Proof. exact (fun_ext (fun x : nat -> A => @lem341313 A x)). Qed.
Lemma lem341315 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem341316 {A : Type'} : (term432 A) = (term432 A).
Proof. exact (MK_COMB (@lem341315 A) (@lem341314 A)). Qed.
Lemma lem341337 {A : Type'} : (term431 A) = (term432 A).
Proof. exact (TRANS (@lem341306 A) (@lem341316 A)). Qed.
Lemma lem341338 {A : Type'} : (term432 A) = (term431 A).
Proof. exact (SYM (@lem341337 A)). Qed.
Lemma lem341340 (p : Prop) : p = (term30 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem341341 {A : Type'} (n : nat) (x : nat -> A) : (term411 A n x) = (term435 A n x).
Proof. exact (@lem341340 (term411 A n x)). Qed.
Lemma lem341342 {A : Type'} (n : nat) (x : nat -> A) : (term435 A n x) = (term411 A n x).
Proof. exact (SYM (@lem341341 A n x)). Qed.
Lemma lem341343 {A : Type'} (n : nat) (x : nat -> A) (h1 : term436 A n x) : term436 A n x.
Proof. exact (h1). Qed.
Lemma lem341345 (P : nat -> Prop) : (term254 P) = (term255 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem341346 {A : Type'} (n : nat) (x : nat -> A) : (term436 A n x) = (term437 A n x).
Proof. exact (@lem341345 (term433 A n x)). Qed.
Lemma lem341347 {A : Type'} (n : nat) (x : nat -> A) (p : nat) : (term438 A n x p) = ((x n) = (x p)).
Proof. exact (eq_refl (term438 A n x p)). Qed.
Lemma lem341348 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem341350 {A : Type'} (n : nat) (x : nat -> A) (p : nat) : (term439 A n x p) = (term440 A n x p).
Proof. exact (MK_COMB (@lem341348) (@lem341347 A n x p)). Qed.
Lemma lem341351 {A : Type'} (n : nat) (x : nat -> A) : (term441 A n x) = (term442 A n x).
Proof. exact (fun_ext (fun p : nat => @lem341350 A n x p)). Qed.
Lemma lem341352 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem341353 {A : Type'} (n : nat) (x : nat -> A) : (term437 A n x) = (term443 A n x).
Proof. exact (MK_COMB (@lem341352) (@lem341351 A n x)). Qed.
Lemma lem341362 {A : Type'} (n : nat) (x : nat -> A) : (term436 A n x) = (term443 A n x).
Proof. exact (TRANS (@lem341346 A n x) (@lem341353 A n x)). Qed.
Lemma lem341363 {A : Type'} (n : nat) (x : nat -> A) (h1 : term436 A n x) : term443 A n x.
Proof. exact (EQ_MP (@lem341362 A n x) (@lem341343 A n x h1)). Qed.
Lemma lem341374 {A : Type'} (n : nat) (x : nat -> A) (p : nat) : (term440 A n x p) = (term440 A n x p).
Proof. exact (eq_refl (term440 A n x p)). Qed.
Lemma lem341375 {A : Type'} (n : nat) (x : nat -> A) : (term442 A n x) = (term442 A n x).
Proof. exact (fun_ext (fun p : nat => @lem341374 A n x p)). Qed.
Lemma lem341376 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem341377 {A : Type'} (n : nat) (x : nat -> A) : (term443 A n x) = (term443 A n x).
Proof. exact (MK_COMB (@lem341376) (@lem341375 A n x)). Qed.
Lemma lem341378 {A : Type'} (n : nat) (x : nat -> A) (h1 : term436 A n x) : term443 A n x.
Proof. exact (EQ_MP (@lem341377 A n x) (@lem341363 A n x h1)). Qed.
Lemma lem341380 {A : Type'} (n : nat) (x : nat -> A) (p : nat) : (term440 A n x p) = (term440 A n x p).
Proof. exact (eq_refl (term440 A n x p)). Qed.
Lemma lem341381 {A : Type'} (n : nat) (x : nat -> A) : (term442 A n x) = (term442 A n x).
Proof. exact (fun_ext (fun p : nat => @lem341380 A n x p)). Qed.
Lemma lem341382 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem341384 {A : Type'} (n : nat) (x : nat -> A) : (term443 A n x) = (term443 A n x).
Proof. exact (MK_COMB (@lem341382) (@lem341381 A n x)). Qed.
Lemma lem341385 {A : Type'} (n : nat) (x : nat -> A) (h1 : term436 A n x) : term443 A n x.
Proof. exact (EQ_MP (@lem341384 A n x) (@lem341378 A n x h1)). Qed.
Lemma lem341386 {A : Type'} (_7407 : nat) (n : nat) (x : nat -> A) (h1 : term436 A n x) : term444 A n x _7407.
Proof. exact (@lem341385 A n x h1 _7407). Qed.
Lemma lem341387 {A : Type'} (n : nat) (x : nat -> A) (_7407 : nat) : (term444 A n x _7407) = (term440 A n x _7407).
Proof. exact (eq_refl (term444 A n x _7407)). Qed.
Lemma lem341390 {A : Type'} (_7407 : nat) (n : nat) (x : nat -> A) (h1 : term436 A n x) : term440 A n x _7407.
Proof. exact (EQ_MP (@lem341387 A n x _7407) (@lem341386 A _7407 n x h1)). Qed.
Lemma lem341404 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem341405 {A : Type'} (x : A) : x = x.
Proof. exact (@lem341404 A x). Qed.
Lemma lem341406 {A : Type'} (x : nat -> A) (n : nat) : (x n) = (x n).
Proof. exact (@lem341405 A (x n)). Qed.
Lemma lem341407 {A : Type'} (x : nat -> A) (n : nat) : term445 A x n.
Proof. exact (fun h0 : term446 A x n => @lem341406 A x n). Qed.
Lemma lem341409 (p : Prop) : (term287 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem341410 {A : Type'} (x : nat -> A) (n : nat) : (term445 A x n) = ((x n) = (x n)).
Proof. exact (@lem341409 ((x n) = (x n))). Qed.
Lemma lem341411 {A : Type'} (x : nat -> A) (n : nat) : (x n) = (x n).
Proof. exact (EQ_MP (@lem341410 A x n) (@lem341407 A x n)). Qed.
Lemma lem341414 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem341416 {A : Type'} (n : nat) (x : nat -> A) (_7407 : nat) : (term440 A n x _7407) = (term447 A n x _7407).
Proof. exact (@lem341414 ((x n) = (x _7407))). Qed.
Lemma lem341419 {A : Type'} (_7407 : nat) (n : nat) (x : nat -> A) (h1 : term436 A n x) : term447 A n x _7407.
Proof. exact (EQ_MP (@lem341416 A n x _7407) (@lem341390 A _7407 n x h1)). Qed.
Lemma lem341420 {A : Type'} (n : nat) (x : nat -> A) (h1 : term436 A n x) : term448 A x n.
Proof. exact (@lem341419 A n n x h1). Qed.
Lemma lem341423 {A : Type'} (n : nat) (x : nat -> A) (h1 : term436 A n x) : False.
Proof. exact (@lem341420 A n x h1 (@lem341411 A x n)). Qed.
Lemma lem341424 {A : Type'} (n : nat) (x : nat -> A) (h1 : term436 A n x) : term290.
Proof. exact (fun h0 : ~ False => @lem341423 A n x h1). Qed.
Lemma lem341426 (p : Prop) : (term287 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem341427 : term290 = False.
Proof. exact (@lem341426 False). Qed.
Lemma lem341428 {A : Type'} (n : nat) (x : nat -> A) (h1 : term436 A n x) : False.
Proof. exact (EQ_MP (@lem341427) (@lem341424 A n x h1)). Qed.
Lemma lem341429 {A : Type'} (n : nat) (x : nat -> A) (h1 : term436 A n x) : (term436 A n x) = False.
Proof. exact (prop_ext (fun h2 : term436 A n x => @lem341428 A n x h1) (fun h2 : False => @lem341343 A n x h1)). Qed.
Lemma lem341430 {A : Type'} (n : nat) (x : nat -> A) (h1 : term436 A n x) : False.
Proof. exact (EQ_MP (@lem341429 A n x h1) (@lem341343 A n x h1)). Qed.
Lemma lem341431 {A : Type'} (n : nat) (x : nat -> A) : term435 A n x.
Proof. exact (fun h0 : term436 A n x => @lem341430 A n x h0). Qed.
Lemma lem341432 {A : Type'} (n : nat) (x : nat -> A) : term411 A n x.
Proof. exact (EQ_MP (@lem341342 A n x) (@lem341431 A n x)). Qed.
Lemma lem341437 {A : Type'} (x : nat -> A) : term409 A x.
Proof. exact (fun n : nat => @lem341432 A n x). Qed.
Lemma lem341442 {A : Type'} : term432 A.
Proof. exact (fun x : nat -> A => @lem341437 A x). Qed.
Lemma lem341443 {A : Type'} : term431 A.
Proof. exact (EQ_MP (@lem341338 A) (@lem341442 A)). Qed.
Lemma lem341444 {A : Type'} (x : nat -> A) : term449 A x.
Proof. exact (@lem341443 A x). Qed.
Lemma lem341445 {A : Type'} (x : nat -> A) : (term449 A x) = (term423 A x).
Proof. exact (eq_refl (term449 A x)). Qed.
Lemma lem341446 {A : Type'} (x : nat -> A) : term423 A x.
Proof. exact (EQ_MP (@lem341445 A x) (@lem341444 A x)). Qed.
Lemma lem341448 {A : Type'} (x : nat -> A) : term423 A x.
Proof. exact (@lem341276 A x (@lem341446 A x)). Qed.
Lemma lem341449 {A : Type'} (x : nat -> A) (h1 : term424 A x) : False.
Proof. exact (@lem341448 A x (@lem341261 A x h1)). Qed.
Lemma lem341450 {A : Type'} (x : nat -> A) (h1 : term424 A x) : (term424 A x) = False.
Proof. exact (prop_ext (fun h2 : term424 A x => @lem341449 A x h1) (fun h2 : False => @lem341261 A x h1)). Qed.
Lemma lem341451 {A : Type'} (x : nat -> A) (h1 : term424 A x) : False.
Proof. exact (EQ_MP (@lem341450 A x h1) (@lem341261 A x h1)). Qed.
Lemma lem341452 {A : Type'} (x : nat -> A) : term423 A x.
Proof. exact (fun h0 : term424 A x => @lem341451 A x h0). Qed.
Lemma lem341453 {A : Type'} (x : nat -> A) : term409 A x.
Proof. exact (EQ_MP (@lem341260 A x) (@lem341452 A x)). Qed.
Lemma lem341454 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (h1 : term421 A f lt2 x) : term421 A f lt2 x.
Proof. exact (h1). Qed.
Lemma lem341455 {A : Type'} (f : A -> nat) (x : nat -> A) (h1 : term450 A f x) : term450 A f x.
Proof. exact (h1). Qed.
Lemma lem341456 {A : Type'} (n : nat) (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (h1 : term421 A f lt2 x) : term451 A f lt2 x n.
Proof. exact (@lem341454 A f lt2 x h1 n). Qed.
Lemma lem341457 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (n : nat) : (term451 A f lt2 x n) = ((term406 A f x n) = (term386 A f lt2 x n)).
Proof. exact (eq_refl (term451 A f lt2 x n)). Qed.
Lemma lem341460 {A : Type'} (n : nat) (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (h1 : term421 A f lt2 x) : (term406 A f x n) = (term386 A f lt2 x n).
Proof. exact (EQ_MP (@lem341457 A f lt2 x n) (@lem341456 A n f lt2 x h1)). Qed.
Lemma lem341461 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (n : nat) : (term452 A f lt2 x n) = (term452 A f lt2 x n).
Proof. exact (eq_refl (term452 A f lt2 x n)). Qed.
Lemma lem341462 {A : Type'} (n : nat) (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (h1 : term421 A f lt2 x) : (term453 A lt2 f x n) = (term454 A f lt2 x n).
Proof. exact (MK_COMB (@lem341461 A f lt2 x n) (@lem341460 A n f lt2 x h1)). Qed.
Lemma lem341463 {A : Type'} (n : nat) (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (h1 : term421 A f lt2 x) : (term454 A f lt2 x n) = (term453 A lt2 f x n).
Proof. exact (SYM (@lem341462 A n f lt2 x h1)). Qed.
Lemma lem341465 (m : nat) (n : nat) : (term8 m n) = (term9 m n).
Proof. exact (EQ_MP (@lem339334 m n) (@lem339333 m n)). Qed.
Lemma lem341466 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (n : nat) : (term454 A f lt2 x n) = (term455 A f lt2 x n).
Proof. exact (@lem341465 (term403 A f lt2 x n) (term403 A f lt2 x n)). Qed.
Lemma lem341470 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem341471 (x : nat) : (x = x) = True.
Proof. exact (@lem341470 nat x). Qed.
Lemma lem341472 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (n : nat) : ((term403 A f lt2 x n) = (term403 A f lt2 x n)) = True.
Proof. exact (@lem341471 (term403 A f lt2 x n)). Qed.
Lemma lem341473 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem341474 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (n : nat) : (term456 A f lt2 x n) = (or True).
Proof. exact (MK_COMB (@lem341473) (@lem341472 A f lt2 x n)). Qed.
Lemma lem341475 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (n : nat) : (term457 A f lt2 x n) = (term457 A f lt2 x n).
Proof. exact (eq_refl (term457 A f lt2 x n)). Qed.
Lemma lem341476 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (n : nat) : (term455 A f lt2 x n) = (term458 A f lt2 x n).
Proof. exact (MK_COMB (@lem341474 A f lt2 x n) (@lem341475 A f lt2 x n)). Qed.
Lemma lem341478 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem341479 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (n : nat) : (term458 A f lt2 x n) = True.
Proof. exact (@lem341478 (term457 A f lt2 x n)). Qed.
Lemma lem341480 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (n : nat) : (term455 A f lt2 x n) = True.
Proof. exact (TRANS (@lem341476 A f lt2 x n) (@lem341479 A f lt2 x n)). Qed.
Lemma lem341481 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (n : nat) : (term454 A f lt2 x n) = True.
Proof. exact (TRANS (@lem341466 A f lt2 x n) (@lem341480 A f lt2 x n)). Qed.
Lemma lem341482 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (n : nat) : True = (term454 A f lt2 x n).
Proof. exact (SYM (@lem341481 A f lt2 x n)). Qed.
Lemma lem341483 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (n : nat) : term454 A f lt2 x n.
Proof. exact (EQ_MP (@lem341482 A f lt2 x n) (@lem0)). Qed.
Lemma lem341484 {A : Type'} (n : nat) (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (h1 : term421 A f lt2 x) : term453 A lt2 f x n.
Proof. exact (EQ_MP (@lem341463 A n f lt2 x h1) (@lem341483 A f lt2 x n)). Qed.
Lemma lem341485 {A : Type'} (n : nat) (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (h1 : term421 A f lt2 x) : term459 A f x n.
Proof. exact (ex_intro (term460 A f x n) (term461 A lt2 x n) (@lem341484 A n f lt2 x h1)). Qed.
Lemma lem341490 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (h1 : term421 A f lt2 x) : term450 A f x.
Proof. exact (fun n : nat => @lem341485 A n f lt2 x h1). Qed.
Lemma lem341494 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem341495 {A : Type'} (f : A -> nat) (x : nat -> A) : (term462 A f x) = (term463 A f x).
Proof. exact (@lem341494 ((term2 A f x) = (term3 A f x))). Qed.
Lemma lem341503 {A B : Type'} (f : A -> B) (y : A) : (term301 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem341504 (f : nat -> Prop) (y : nat) : (term464 f y) = (f y).
Proof. exact (@lem341503 nat Prop f y). Qed.
Lemma lem341505 {A : Type'} (f : A -> nat) (x : nat -> A) (n : nat) : (term465 A f x n) = (term466 A f x n).
Proof. exact (@lem341504 (term1 A f x) n). Qed.
Lemma lem341506 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term466 A f x n) = (term467 A n f x).
Proof. exact (eq_refl (term466 A f x n)). Qed.
Lemma lem341507 {A : Type'} (f : A -> nat) (x : nat -> A) : (term468 A f x) = (term1 A f x).
Proof. exact (fun_ext (fun n : nat => @lem341506 A n f x)). Qed.
Lemma lem341508 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem341509 {A : Type'} (f : A -> nat) (x : nat -> A) (n : nat) : (term465 A f x n) = (term466 A f x n).
Proof. exact (MK_COMB (@lem341507 A f x) (@lem341508 n)). Qed.
Lemma lem341510 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem341511 {A : Type'} (f : A -> nat) (x : nat -> A) (n : nat) : (term469 A f x n) = (term470 A f x n).
Proof. exact (MK_COMB (@lem341510) (@lem341509 A f x n)). Qed.
Lemma lem341512 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term466 A f x n) = (term467 A n f x).
Proof. exact (eq_refl (term466 A f x n)). Qed.
Lemma lem341513 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : ((term465 A f x n) = (term466 A f x n)) = ((term466 A f x n) = (term467 A n f x)).
Proof. exact (MK_COMB (@lem341511 A f x n) (@lem341512 A n f x)). Qed.
Lemma lem341514 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term466 A f x n) = (term467 A n f x).
Proof. exact (EQ_MP (@lem341513 A n f x) (@lem341505 A f x n)). Qed.
Lemma lem341521 {A : Type'} (f : A -> nat) (x : nat -> A) : (term468 A f x) = (term1 A f x).
Proof. exact (fun_ext (fun n : nat => @lem341514 A n f x)). Qed.
Lemma lem341522 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem341523 {A : Type'} (f : A -> nat) (x : nat -> A) : (term2 A f x) = (term471 A f x).
Proof. exact (MK_COMB (@lem341522) (@lem341521 A f x)). Qed.
Lemma lem341528 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem341529 {A : Type'} (f : A -> nat) (x : nat -> A) : (term472 A f x) = (term473 A f x).
Proof. exact (MK_COMB (@lem341528) (@lem341523 A f x)). Qed.
Lemma lem341537 {A B : Type'} (f : A -> B) (y : A) : (term301 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem341538 (f : nat -> Prop) (y : nat) : (term464 f y) = (f y).
Proof. exact (@lem341537 nat Prop f y). Qed.
Lemma lem341539 {A : Type'} (f : A -> nat) (x : nat -> A) (n : nat) : (term465 A f x n) = (term466 A f x n).
Proof. exact (@lem341538 (term1 A f x) n). Qed.
Lemma lem341540 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term466 A f x n) = (term467 A n f x).
Proof. exact (eq_refl (term466 A f x n)). Qed.
Lemma lem341541 {A : Type'} (f : A -> nat) (x : nat -> A) : (term468 A f x) = (term1 A f x).
Proof. exact (fun_ext (fun n : nat => @lem341540 A n f x)). Qed.
Lemma lem341542 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem341543 {A : Type'} (f : A -> nat) (x : nat -> A) (n : nat) : (term465 A f x n) = (term466 A f x n).
Proof. exact (MK_COMB (@lem341541 A f x) (@lem341542 n)). Qed.
Lemma lem341544 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem341545 {A : Type'} (f : A -> nat) (x : nat -> A) (n : nat) : (term469 A f x n) = (term470 A f x n).
Proof. exact (MK_COMB (@lem341544) (@lem341543 A f x n)). Qed.
Lemma lem341546 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term466 A f x n) = (term467 A n f x).
Proof. exact (eq_refl (term466 A f x n)). Qed.
Lemma lem341547 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : ((term465 A f x n) = (term466 A f x n)) = ((term466 A f x n) = (term467 A n f x)).
Proof. exact (MK_COMB (@lem341545 A f x n) (@lem341546 A n f x)). Qed.
Lemma lem341548 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term466 A f x n) = (term467 A n f x).
Proof. exact (EQ_MP (@lem341547 A n f x) (@lem341539 A f x n)). Qed.
Lemma lem341555 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem341556 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term474 A f x n) = (term475 A n f x).
Proof. exact (MK_COMB (@lem341555) (@lem341548 A n f x)). Qed.
Lemma lem341564 {A B : Type'} (f : A -> B) (y : A) : (term301 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem341565 (f : nat -> Prop) (y : nat) : (term464 f y) = (f y).
Proof. exact (@lem341564 nat Prop f y). Qed.
Lemma lem341566 {A : Type'} (f : A -> nat) (x : nat -> A) (m : nat) : (term465 A f x m) = (term466 A f x m).
Proof. exact (@lem341565 (term1 A f x) m). Qed.
Lemma lem341567 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term466 A f x n) = (term467 A n f x).
Proof. exact (eq_refl (term466 A f x n)). Qed.
Lemma lem341568 {A : Type'} (f : A -> nat) (x : nat -> A) : (term468 A f x) = (term1 A f x).
Proof. exact (fun_ext (fun n : nat => @lem341567 A n f x)). Qed.
Lemma lem341569 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem341570 {A : Type'} (f : A -> nat) (x : nat -> A) (m : nat) : (term465 A f x m) = (term466 A f x m).
Proof. exact (MK_COMB (@lem341568 A f x) (@lem341569 m)). Qed.
Lemma lem341571 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem341572 {A : Type'} (f : A -> nat) (x : nat -> A) (m : nat) : (term469 A f x m) = (term470 A f x m).
Proof. exact (MK_COMB (@lem341571) (@lem341570 A f x m)). Qed.
Lemma lem341573 {A : Type'} (m : nat) (f : A -> nat) (x : nat -> A) : (term466 A f x m) = (term467 A m f x).
Proof. exact (eq_refl (term466 A f x m)). Qed.
Lemma lem341574 {A : Type'} (m : nat) (f : A -> nat) (x : nat -> A) : ((term465 A f x m) = (term466 A f x m)) = ((term466 A f x m) = (term467 A m f x)).
Proof. exact (MK_COMB (@lem341572 A f x m) (@lem341573 A m f x)). Qed.
Lemma lem341575 {A : Type'} (m : nat) (f : A -> nat) (x : nat -> A) : (term466 A f x m) = (term467 A m f x).
Proof. exact (EQ_MP (@lem341574 A m f x) (@lem341566 A f x m)). Qed.
Lemma lem341582 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem341583 {A : Type'} (m : nat) (f : A -> nat) (x : nat -> A) : (term476 A f x m) = (term477 A m f x).
Proof. exact (MK_COMB (@lem341582) (@lem341575 A m f x)). Qed.
Lemma lem341584 (m : nat) (n : nat) : (term478 m n) = (term478 m n).
Proof. exact (eq_refl (term478 m n)). Qed.
Lemma lem341585 {A : Type'} (n : nat) (m : nat) (f : A -> nat) (x : nat -> A) : (term479 A n f x m) = (term480 A n m f x).
Proof. exact (MK_COMB (@lem341584 m n) (@lem341583 A m f x)). Qed.
Lemma lem341588 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term481 A n f x) = (term482 A n f x).
Proof. exact (fun_ext (fun m : nat => @lem341585 A n m f x)). Qed.
Lemma lem341589 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem341590 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term483 A n f x) = (term484 A n f x).
Proof. exact (MK_COMB (@lem341589) (@lem341588 A n f x)). Qed.
Lemma lem341595 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term485 A n f x) = (term486 A n f x).
Proof. exact (MK_COMB (@lem341556 A n f x) (@lem341590 A n f x)). Qed.
Lemma lem341598 {A : Type'} (f : A -> nat) (x : nat -> A) : (term487 A f x) = (term488 A f x).
Proof. exact (fun_ext (fun n : nat => @lem341595 A n f x)). Qed.
Lemma lem341599 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem341600 {A : Type'} (f : A -> nat) (x : nat -> A) : (term3 A f x) = (term489 A f x).
Proof. exact (MK_COMB (@lem341599) (@lem341598 A f x)). Qed.
Lemma lem341605 {A : Type'} (f : A -> nat) (x : nat -> A) : ((term2 A f x) = (term3 A f x)) = ((term471 A f x) = (term489 A f x)).
Proof. exact (MK_COMB (@lem341529 A f x) (@lem341600 A f x)). Qed.
Lemma lem341608 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem341609 {A : Type'} (f : A -> nat) (x : nat -> A) : (term463 A f x) = (term490 A f x).
Proof. exact (MK_COMB (@lem341608) (@lem341605 A f x)). Qed.
Lemma lem341610 {A : Type'} (f : A -> nat) (x : nat -> A) : (term462 A f x) = (term490 A f x).
Proof. exact (TRANS (@lem341495 A f x) (@lem341609 A f x)). Qed.
Lemma lem341611 {A : Type'} (f : A -> nat) (x : nat -> A) : (term490 A f x) = (term462 A f x).
Proof. exact (SYM (@lem341610 A f x)). Qed.
Lemma lem341612 {A : Type'} (f : A -> nat) (x : nat -> A) (h1 : (term471 A f x) = (term489 A f x)) : (term471 A f x) = (term489 A f x).
Proof. exact (h1). Qed.
Lemma lem341613 (P : nat -> Prop) : (term20 P) = (ex P).
Proof. exact (@lem19728 nat P). Qed.
Lemma lem341614 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) : (term21 A lt2 x n) = (term22 A lt2 x n).
Proof. exact (@lem341613 (term23 A lt2 x n)). Qed.
Lemma lem341615 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) : (term21 A lt2 x n) = (term24 A lt2 x n).
Proof. exact (eq_refl (term21 A lt2 x n)). Qed.
Lemma lem341616 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem341617 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) : (term25 A lt2 x n) = (term26 A lt2 x n).
Proof. exact (MK_COMB (@lem341616) (@lem341615 A lt2 x n)). Qed.
Lemma lem341618 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) : (term22 A lt2 x n) = (term22 A lt2 x n).
Proof. exact (eq_refl (term22 A lt2 x n)). Qed.
Lemma lem341619 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) : ((term21 A lt2 x n) = (term22 A lt2 x n)) = ((term24 A lt2 x n) = (term22 A lt2 x n)).
Proof. exact (MK_COMB (@lem341617 A lt2 x n) (@lem341618 A lt2 x n)). Qed.
Lemma lem341810 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) : (term24 A lt2 x n) = (term22 A lt2 x n).
Proof. exact (EQ_MP (@lem341619 A lt2 x n) (@lem341614 A lt2 x n)). Qed.
Lemma lem341835 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : (term27 A lt2 x) = (term28 A lt2 x).
Proof. exact (fun_ext (fun n : nat => @lem341810 A lt2 x n)). Qed.
Lemma lem341838 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem341839 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : (term19 A lt2 x) = (term29 A lt2 x).
Proof. exact (MK_COMB (@lem341838) (@lem341835 A lt2 x)). Qed.
Lemma lem341842 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem341843 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : (term491 A lt2 x) = (term492 A lt2 x).
Proof. exact (MK_COMB (@lem341842) (@lem341839 A lt2 x)). Qed.
Lemma lem342084 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (x : nat -> A) : (term493 A lt2 f x) = (term493 A lt2 f x).
Proof. exact (eq_refl (term493 A lt2 f x)). Qed.
Lemma lem342085 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (x : nat -> A) : (term494 A lt2 f x) = (term495 A lt2 f x).
Proof. exact (MK_COMB (@lem341843 A lt2 x) (@lem342084 A lt2 f x)). Qed.
Lemma lem342088 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : (term39 A lt2 x) = (term39 A lt2 x).
Proof. exact (eq_refl (term39 A lt2 x)). Qed.
Lemma lem342089 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (x : nat -> A) : (term496 A lt2 f x) = (term497 A lt2 f x).
Proof. exact (MK_COMB (@lem342088 A lt2 x) (@lem342085 A lt2 f x)). Qed.
Lemma lem342092 {A : Type'} (lt2 : type1402 A) : (term42 A lt2) = (term42 A lt2).
Proof. exact (eq_refl (term42 A lt2)). Qed.
Lemma lem342093 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (x : nat -> A) : (term498 A lt2 f x) = (term499 A lt2 f x).
Proof. exact (MK_COMB (@lem342092 A lt2) (@lem342089 A lt2 f x)). Qed.
Lemma lem342096 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (x : nat -> A) : (term499 A lt2 f x) = (term498 A lt2 f x).
Proof. exact (SYM (@lem342093 A lt2 f x)). Qed.
Lemma lem342097 (P : nat -> Prop) : term500 P.
Proof. exact (@lem19732 nat P). Qed.
Lemma lem342098 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) : term501 A lt2 x n.
Proof. exact (@lem342097 (term23 A lt2 x n)). Qed.
Lemma lem342099 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) : (term21 A lt2 x n) = (term24 A lt2 x n).
Proof. exact (eq_refl (term21 A lt2 x n)). Qed.
Lemma lem342100 {A : Type'} (lt2 : type1402 A) (x : nat) (x' : nat -> A) (n : nat) : (term257 A lt2 x' n x) = (term52 A lt2 x x' n).
Proof. exact (eq_refl (term257 A lt2 x' n x)). Qed.
Lemma lem342101 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem342102 {A : Type'} (lt2 : type1402 A) (x : nat) (x' : nat -> A) (n : nat) : (term502 A lt2 x' n x) = (term503 A lt2 x x' n).
Proof. exact (MK_COMB (@lem342101) (@lem342100 A lt2 x x' n)). Qed.
Lemma lem342103 {A : Type'} (x : nat) (lt2 : type1402 A) (x' : nat -> A) (n : nat) : (term504 A x lt2 x' n) = (term505 A x lt2 x' n).
Proof. exact (MK_COMB (@lem342102 A lt2 x x' n) (@lem342099 A lt2 x' n)). Qed.
Lemma lem342104 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) : (term506 A lt2 x n) = (term507 A lt2 x n).
Proof. exact (fun_ext (fun x' : nat => @lem342103 A x' lt2 x n)). Qed.
Lemma lem342105 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem342106 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) : (term501 A lt2 x n) = (term508 A lt2 x n).
Proof. exact (MK_COMB (@lem342105) (@lem342104 A lt2 x n)). Qed.
Lemma lem342107 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) : term508 A lt2 x n.
Proof. exact (EQ_MP (@lem342106 A lt2 x n) (@lem342098 A lt2 x n)). Qed.
Lemma lem342108 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : term509 A lt2 x.
Proof. exact (fun n : nat => @lem342107 A lt2 x n). Qed.
Lemma lem342109 {A : Type'} (lt2 : type1402 A) : term510 A lt2.
Proof. exact (fun x : nat -> A => @lem342108 A lt2 x). Qed.
Lemma lem342110 {A : Type'} : term511 A.
Proof. exact (fun lt2 : type1402 A => @lem342109 A lt2). Qed.
Lemma lem342111 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (x : nat -> A) (h1 : term512 A lt2 f x) : term512 A lt2 f x.
Proof. exact (h1). Qed.
Lemma lem342112 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (x : nat -> A) (h1 : term512 A lt2 f x) : term499 A lt2 f x.
Proof. exact (@lem342111 A lt2 f x h1 (@lem342110 A)). Qed.
Lemma lem342113 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (x : nat -> A) : term513 A lt2 f x.
Proof. exact (fun h0 : term512 A lt2 f x => @lem342112 A lt2 f x h0). Qed.
Lemma lem342114 {A : Type'} (_7410 : type414 A) (h1 : _7410 = (term514 A)) : _7410 = (term514 A).
Proof. exact (h1). Qed.
Lemma lem342115 {A : Type'} (lt2 : type1402 A) : lt2 = lt2.
Proof. exact (eq_refl lt2). Qed.
Lemma lem342116 {A : Type'} (lt2 : type1402 A) (_7410 : type414 A) (h1 : _7410 = (term514 A)) : (_7410 lt2) = (term515 A lt2).
Proof. exact (MK_COMB (@lem342114 A _7410 h1) (@lem342115 A lt2)). Qed.
Lemma lem342117 {A : Type'} (lt2 : type1402 A) : (term515 A lt2) = (term516 A lt2).
Proof. exact (eq_refl (term515 A lt2)). Qed.
Lemma lem342118 {A : Type'} (_7410 : type414 A) (lt2 : type1402 A) : (term517 A _7410 lt2) = (term517 A _7410 lt2).
Proof. exact (eq_refl (term517 A _7410 lt2)). Qed.
Lemma lem342119 {A : Type'} (_7410 : type414 A) (lt2 : type1402 A) : ((_7410 lt2) = (term515 A lt2)) = ((_7410 lt2) = (term516 A lt2)).
Proof. exact (MK_COMB (@lem342118 A _7410 lt2) (@lem342117 A lt2)). Qed.
Lemma lem342120 {A : Type'} (lt2 : type1402 A) (_7410 : type414 A) (h1 : _7410 = (term514 A)) : (_7410 lt2) = (term516 A lt2).
Proof. exact (EQ_MP (@lem342119 A _7410 lt2) (@lem342116 A lt2 _7410 h1)). Qed.
Lemma lem342121 {A : Type'} (x : nat -> A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem342122 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (_7410 : type414 A) (h1 : _7410 = (term514 A)) : (_7410 lt2 x) = (term518 A lt2 x).
Proof. exact (MK_COMB (@lem342120 A lt2 _7410 h1) (@lem342121 A x)). Qed.
Lemma lem342123 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : (term518 A lt2 x) = (term519 A lt2 x).
Proof. exact (eq_refl (term518 A lt2 x)). Qed.
Lemma lem342124 {A : Type'} (_7410 : type414 A) (lt2 : type1402 A) (x : nat -> A) : (term520 A _7410 lt2 x) = (term520 A _7410 lt2 x).
Proof. exact (eq_refl (term520 A _7410 lt2 x)). Qed.
Lemma lem342125 {A : Type'} (_7410 : type414 A) (lt2 : type1402 A) (x : nat -> A) : ((_7410 lt2 x) = (term518 A lt2 x)) = ((_7410 lt2 x) = (term519 A lt2 x)).
Proof. exact (MK_COMB (@lem342124 A _7410 lt2 x) (@lem342123 A lt2 x)). Qed.
Lemma lem342126 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (_7410 : type414 A) (h1 : _7410 = (term514 A)) : (_7410 lt2 x) = (term519 A lt2 x).
Proof. exact (EQ_MP (@lem342125 A _7410 lt2 x) (@lem342122 A lt2 x _7410 h1)). Qed.
Lemma lem342127 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem342128 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) (_7410 : type414 A) (h1 : _7410 = (term514 A)) : (_7410 lt2 x n) = (term521 A lt2 x n).
Proof. exact (MK_COMB (@lem342126 A lt2 x _7410 h1) (@lem342127 n)). Qed.
Lemma lem342129 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) : (term521 A lt2 x n) = (term461 A lt2 x n).
Proof. exact (eq_refl (term521 A lt2 x n)). Qed.
Lemma lem342130 {A : Type'} (_7410 : type414 A) (lt2 : type1402 A) (x : nat -> A) (n : nat) : (term522 A _7410 lt2 x n) = (term522 A _7410 lt2 x n).
Proof. exact (eq_refl (term522 A _7410 lt2 x n)). Qed.
Lemma lem342131 {A : Type'} (_7410 : type414 A) (lt2 : type1402 A) (x : nat -> A) (n : nat) : ((_7410 lt2 x n) = (term521 A lt2 x n)) = ((_7410 lt2 x n) = (term461 A lt2 x n)).
Proof. exact (MK_COMB (@lem342130 A _7410 lt2 x n) (@lem342129 A lt2 x n)). Qed.
Lemma lem342132 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) (_7410 : type414 A) (h1 : _7410 = (term514 A)) : (_7410 lt2 x n) = (term461 A lt2 x n).
Proof. exact (EQ_MP (@lem342131 A _7410 lt2 x n) (@lem342128 A lt2 x n _7410 h1)). Qed.
Lemma lem342133 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) (_7410 : type414 A) (h1 : _7410 = (term514 A)) : (term461 A lt2 x n) = (_7410 lt2 x n).
Proof. exact (SYM (@lem342132 A lt2 x n _7410 h1)). Qed.
Lemma lem342134 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (_7410 : type414 A) (h1 : _7410 = (term514 A)) : term523 A _7410 lt2 x.
Proof. exact (fun n : nat => @lem342133 A lt2 x n _7410 h1). Qed.
Lemma lem342135 {A : Type'} (lt2 : type1402 A) (_7410 : type414 A) (h1 : _7410 = (term514 A)) : term524 A _7410 lt2.
Proof. exact (fun x : nat -> A => @lem342134 A lt2 x _7410 h1). Qed.
Lemma lem342136 {A : Type'} (_7410 : type414 A) (h1 : _7410 = (term514 A)) : term525 A _7410.
Proof. exact (fun lt2 : type1402 A => @lem342135 A lt2 _7410 h1). Qed.
Lemma lem342137 {A : Type'} (lt2 : type1402 A) (_7410 : type414 A) (h1 : _7410 = (term514 A)) : term526 A _7410 lt2.
Proof. exact (@lem342136 A _7410 h1 lt2). Qed.
Lemma lem342138 {A : Type'} (_7410 : type414 A) (lt2 : type1402 A) : (term526 A _7410 lt2) = (term524 A _7410 lt2).
Proof. exact (eq_refl (term526 A _7410 lt2)). Qed.
Lemma lem342139 {A : Type'} (lt2 : type1402 A) (_7410 : type414 A) (h1 : _7410 = (term514 A)) : term524 A _7410 lt2.
Proof. exact (EQ_MP (@lem342138 A _7410 lt2) (@lem342137 A lt2 _7410 h1)). Qed.
Lemma lem342140 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (_7410 : type414 A) (h1 : _7410 = (term514 A)) : term527 A _7410 lt2 x.
Proof. exact (@lem342139 A lt2 _7410 h1 x). Qed.
Lemma lem342141 {A : Type'} (_7410 : type414 A) (lt2 : type1402 A) (x : nat -> A) : (term527 A _7410 lt2 x) = (term523 A _7410 lt2 x).
Proof. exact (eq_refl (term527 A _7410 lt2 x)). Qed.
Lemma lem342142 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (_7410 : type414 A) (h1 : _7410 = (term514 A)) : term523 A _7410 lt2 x.
Proof. exact (EQ_MP (@lem342141 A _7410 lt2 x) (@lem342140 A lt2 x _7410 h1)). Qed.
Lemma lem342143 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) (_7410 : type414 A) (h1 : _7410 = (term514 A)) : term528 A _7410 lt2 x n.
Proof. exact (@lem342142 A lt2 x _7410 h1 n). Qed.
Lemma lem342144 {A : Type'} (_7410 : type414 A) (lt2 : type1402 A) (x : nat -> A) (n : nat) : (term528 A _7410 lt2 x n) = ((term461 A lt2 x n) = (_7410 lt2 x n)).
Proof. exact (eq_refl (term528 A _7410 lt2 x n)). Qed.
Lemma lem342147 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) (_7410 : type414 A) (h1 : _7410 = (term514 A)) : (term461 A lt2 x n) = (_7410 lt2 x n).
Proof. exact (EQ_MP (@lem342144 A _7410 lt2 x n) (@lem342143 A lt2 x n _7410 h1)). Qed.
Lemma lem342148 {A : Type'} (x : nat -> A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem342149 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) (_7410 : type414 A) (h1 : _7410 = (term514 A)) : (term401 A lt2 x n) = (term529 A _7410 lt2 x n).
Proof. exact (MK_COMB (@lem342148 A x) (@lem342147 A lt2 x n _7410 h1)). Qed.
Lemma lem342150 {A : Type'} (lt2 : type1402 A) : lt2 = lt2.
Proof. exact (eq_refl lt2). Qed.
Lemma lem342151 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) (_7410 : type414 A) (h1 : _7410 = (term514 A)) : (term530 A lt2 x n) = (term531 A _7410 lt2 x n).
Proof. exact (MK_COMB (@lem342150 A lt2) (@lem342149 A lt2 x n _7410 h1)). Qed.
Lemma lem342152 {A : Type'} (x : nat -> A) (n : nat) : (x n) = (x n).
Proof. exact (eq_refl (x n)). Qed.
Lemma lem342153 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) (_7410 : type414 A) (h1 : _7410 = (term514 A)) : (term24 A lt2 x n) = (term532 A _7410 lt2 x n).
Proof. exact (MK_COMB (@lem342151 A lt2 x n _7410 h1) (@lem342152 A x n)). Qed.
Lemma lem342154 {A : Type'} (lt2 : type1402 A) (x : nat) (x' : nat -> A) (n : nat) : (term503 A lt2 x x' n) = (term503 A lt2 x x' n).
Proof. exact (eq_refl (term503 A lt2 x x' n)). Qed.
Lemma lem342155 {A : Type'} (x : nat) (lt2 : type1402 A) (x' : nat -> A) (n : nat) (_7410 : type414 A) (h1 : _7410 = (term514 A)) : (term505 A x lt2 x' n) = (term533 A x _7410 lt2 x' n).
Proof. exact (MK_COMB (@lem342154 A lt2 x x' n) (@lem342153 A lt2 x' n _7410 h1)). Qed.
Lemma lem342156 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) (_7410 : type414 A) (h1 : _7410 = (term514 A)) : (term507 A lt2 x n) = (term534 A _7410 lt2 x n).
Proof. exact (fun_ext (fun x' : nat => @lem342155 A x' lt2 x n _7410 h1)). Qed.
Lemma lem342157 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem342158 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) (_7410 : type414 A) (h1 : _7410 = (term514 A)) : (term508 A lt2 x n) = (term535 A _7410 lt2 x n).
Proof. exact (MK_COMB (@lem342157) (@lem342156 A lt2 x n _7410 h1)). Qed.
Lemma lem342159 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (_7410 : type414 A) (h1 : _7410 = (term514 A)) : (term536 A lt2 x) = (term537 A _7410 lt2 x).
Proof. exact (fun_ext (fun n : nat => @lem342158 A lt2 x n _7410 h1)). Qed.
Lemma lem342160 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem342161 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (_7410 : type414 A) (h1 : _7410 = (term514 A)) : (term509 A lt2 x) = (term538 A _7410 lt2 x).
Proof. exact (MK_COMB (@lem342160) (@lem342159 A lt2 x _7410 h1)). Qed.
Lemma lem342162 {A : Type'} (lt2 : type1402 A) (_7410 : type414 A) (h1 : _7410 = (term514 A)) : (term539 A lt2) = (term540 A _7410 lt2).
Proof. exact (fun_ext (fun x : nat -> A => @lem342161 A lt2 x _7410 h1)). Qed.
Lemma lem342163 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem342164 {A : Type'} (lt2 : type1402 A) (_7410 : type414 A) (h1 : _7410 = (term514 A)) : (term510 A lt2) = (term541 A _7410 lt2).
Proof. exact (MK_COMB (@lem342163 A) (@lem342162 A lt2 _7410 h1)). Qed.
Lemma lem342165 {A : Type'} (_7410 : type414 A) (h1 : _7410 = (term514 A)) : (term542 A) = (term543 A _7410).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem342164 A lt2 _7410 h1)). Qed.
Lemma lem342166 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem342167 {A : Type'} (_7410 : type414 A) (h1 : _7410 = (term514 A)) : (term511 A) = (term544 A _7410).
Proof. exact (MK_COMB (@lem342166 A) (@lem342165 A _7410 h1)). Qed.
Lemma lem342168 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem342169 {A : Type'} (_7410 : type414 A) (h1 : _7410 = (term514 A)) : (term545 A) = (term546 A _7410).
Proof. exact (MK_COMB (@lem342168) (@lem342167 A _7410 h1)). Qed.
Lemma lem342171 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) (_7410 : type414 A) (h1 : _7410 = (term514 A)) : (term461 A lt2 x n) = (_7410 lt2 x n).
Proof. exact (EQ_MP (@lem342144 A _7410 lt2 x n) (@lem342143 A lt2 x n _7410 h1)). Qed.
Lemma lem342172 {A : Type'} (x : nat -> A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem342173 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) (_7410 : type414 A) (h1 : _7410 = (term514 A)) : (term401 A lt2 x n) = (term529 A _7410 lt2 x n).
Proof. exact (MK_COMB (@lem342172 A x) (@lem342171 A lt2 x n _7410 h1)). Qed.
Lemma lem342174 {A : Type'} (f : A -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem342175 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (n : nat) (_7410 : type414 A) (h1 : _7410 = (term514 A)) : (term403 A f lt2 x n) = (term547 A f _7410 lt2 x n).
Proof. exact (MK_COMB (@lem342174 A f) (@lem342173 A lt2 x n _7410 h1)). Qed.
Lemma lem342176 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem342177 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (n : nat) (_7410 : type414 A) (h1 : _7410 = (term514 A)) : (term386 A f lt2 x n) = (term548 A f _7410 lt2 x n).
Proof. exact (MK_COMB (@lem342176) (@lem342175 A f lt2 x n _7410 h1)). Qed.
Lemma lem342178 {A : Type'} (f : A -> nat) (x : nat -> A) (n : nat) : (term418 A f x n) = (term418 A f x n).
Proof. exact (eq_refl (term418 A f x n)). Qed.
Lemma lem342179 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (n : nat) (_7410 : type414 A) (h1 : _7410 = (term514 A)) : ((term406 A f x n) = (term386 A f lt2 x n)) = ((term406 A f x n) = (term548 A f _7410 lt2 x n)).
Proof. exact (MK_COMB (@lem342178 A f x n) (@lem342177 A f lt2 x n _7410 h1)). Qed.
Lemma lem342180 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (_7410 : type414 A) (h1 : _7410 = (term514 A)) : (term420 A f lt2 x) = (term549 A f _7410 lt2 x).
Proof. exact (fun_ext (fun n : nat => @lem342179 A f lt2 x n _7410 h1)). Qed.
Lemma lem342181 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem342182 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (_7410 : type414 A) (h1 : _7410 = (term514 A)) : (term421 A f lt2 x) = (term550 A f _7410 lt2 x).
Proof. exact (MK_COMB (@lem342181) (@lem342180 A f lt2 x _7410 h1)). Qed.
Lemma lem342183 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem342184 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (_7410 : type414 A) (h1 : _7410 = (term514 A)) : (term551 A f lt2 x) = (term552 A f _7410 lt2 x).
Proof. exact (MK_COMB (@lem342183) (@lem342182 A f lt2 x _7410 h1)). Qed.
Lemma lem342185 {A : Type'} (f : A -> nat) (x : nat -> A) : (term553 A f x) = (term553 A f x).
Proof. exact (eq_refl (term553 A f x)). Qed.
Lemma lem342186 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (x : nat -> A) (_7410 : type414 A) (h1 : _7410 = (term514 A)) : (term493 A lt2 f x) = (term554 A _7410 lt2 f x).
Proof. exact (MK_COMB (@lem342184 A f lt2 x _7410 h1) (@lem342185 A f x)). Qed.
Lemma lem342187 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : (term492 A lt2 x) = (term492 A lt2 x).
Proof. exact (eq_refl (term492 A lt2 x)). Qed.
Lemma lem342188 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (x : nat -> A) (_7410 : type414 A) (h1 : _7410 = (term514 A)) : (term495 A lt2 f x) = (term555 A _7410 lt2 f x).
Proof. exact (MK_COMB (@lem342187 A lt2 x) (@lem342186 A lt2 f x _7410 h1)). Qed.
Lemma lem342189 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : (term39 A lt2 x) = (term39 A lt2 x).
Proof. exact (eq_refl (term39 A lt2 x)). Qed.
Lemma lem342190 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (x : nat -> A) (_7410 : type414 A) (h1 : _7410 = (term514 A)) : (term497 A lt2 f x) = (term556 A _7410 lt2 f x).
Proof. exact (MK_COMB (@lem342189 A lt2 x) (@lem342188 A lt2 f x _7410 h1)). Qed.
Lemma lem342191 {A : Type'} (lt2 : type1402 A) : (term42 A lt2) = (term42 A lt2).
Proof. exact (eq_refl (term42 A lt2)). Qed.
Lemma lem342192 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (x : nat -> A) (_7410 : type414 A) (h1 : _7410 = (term514 A)) : (term499 A lt2 f x) = (term557 A _7410 lt2 f x).
Proof. exact (MK_COMB (@lem342191 A lt2) (@lem342190 A lt2 f x _7410 h1)). Qed.
Lemma lem342193 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (x : nat -> A) (_7410 : type414 A) (h1 : _7410 = (term514 A)) : (term512 A lt2 f x) = (term558 A _7410 lt2 f x).
Proof. exact (MK_COMB (@lem342169 A _7410 h1) (@lem342192 A lt2 f x _7410 h1)). Qed.
Lemma lem342194 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (x : nat -> A) (h1 : term559 A lt2 f x) : term559 A lt2 f x.
Proof. exact (h1). Qed.
Lemma lem342195 {A : Type'} (_7410 : type414 A) (lt2 : type1402 A) (f : A -> nat) (x : nat -> A) (h1 : term559 A lt2 f x) : term560 A lt2 f x _7410.
Proof. exact (@lem342194 A lt2 f x h1 _7410). Qed.
Lemma lem342196 {A : Type'} (_7410 : type414 A) (lt2 : type1402 A) (f : A -> nat) (x : nat -> A) : (term560 A lt2 f x _7410) = (term558 A _7410 lt2 f x).
Proof. exact (eq_refl (term560 A lt2 f x _7410)). Qed.
Lemma lem342197 {A : Type'} (_7410 : type414 A) (lt2 : type1402 A) (f : A -> nat) (x : nat -> A) (h1 : term559 A lt2 f x) : term558 A _7410 lt2 f x.
Proof. exact (EQ_MP (@lem342196 A _7410 lt2 f x) (@lem342195 A _7410 lt2 f x h1)). Qed.
Lemma lem342198 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (x : nat -> A) (_7410 : type414 A) (h1 : _7410 = (term514 A)) : (term558 A _7410 lt2 f x) = (term512 A lt2 f x).
Proof. exact (SYM (@lem342193 A lt2 f x _7410 h1)). Qed.
Lemma lem342199 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (x : nat -> A) (_7410 : type414 A) (h1 : term559 A lt2 f x) (h2 : _7410 = (term514 A)) : term512 A lt2 f x.
Proof. exact (EQ_MP (@lem342198 A lt2 f x _7410 h2) (@lem342197 A _7410 lt2 f x h1)). Qed.
Lemma lem342200 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (x : nat -> A) (_7410 : type414 A) (h1 : _7410 = (term514 A)) : term561 A lt2 f x.
Proof. exact (fun h0 : term559 A lt2 f x => @lem342199 A lt2 f x _7410 h0 h1). Qed.
Lemma lem342201 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (x : nat -> A) : term562 A lt2 f x.
Proof. exact (@lem51 (term512 A lt2 f x) (term559 A lt2 f x) (term499 A lt2 f x)). Qed.
Lemma lem342202 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (x : nat -> A) (_7410 : type414 A) (h1 : _7410 = (term514 A)) : term563 A lt2 f x.
Proof. exact (@lem342201 A lt2 f x (@lem342200 A lt2 f x _7410 h1)). Qed.
Lemma lem342203 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (x : nat -> A) (_7410 : type414 A) (h1 : _7410 = (term514 A)) : term564 A lt2 f x.
Proof. exact (@lem342202 A lt2 f x _7410 h1 (@lem342113 A lt2 f x)). Qed.
Lemma lem342204 {A : Type'} : (term514 A) = (term514 A).
Proof. exact (eq_refl (term514 A)). Qed.
Lemma lem342205 {A : Type'} (_7410 : type414 A) (lt2 : type1402 A) (f : A -> nat) (x : nat -> A) : term565 A _7410 lt2 f x.
Proof. exact (fun h0 : _7410 = (term514 A) => @lem342203 A lt2 f x _7410 h0). Qed.
Lemma lem342206 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (x : nat -> A) : term566 A lt2 f x.
Proof. exact (@lem342205 A (term514 A) lt2 f x). Qed.
Lemma lem342207 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (x : nat -> A) : term564 A lt2 f x.
Proof. exact (@lem342206 A lt2 f x (@lem342204 A)). Qed.
Lemma lem342208 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (x : nat -> A) (h1 : term559 A lt2 f x) : term559 A lt2 f x.
Proof. exact (h1). Qed.
Lemma lem342209 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (x : nat -> A) : term567 A lt2 f x.
Proof. exact (fun h0 : term559 A lt2 f x => @lem342208 A lt2 f x h0). Qed.
Lemma lem342210 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (x : nat -> A) : term568 A lt2 f x.
Proof. exact (@lem51 (term559 A lt2 f x) (term559 A lt2 f x) (term499 A lt2 f x)). Qed.
Lemma lem342211 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (x : nat -> A) : term569 A lt2 f x.
Proof. exact (@lem342210 A lt2 f x (@lem342209 A lt2 f x)). Qed.
Lemma lem342212 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (x : nat -> A) : term564 A lt2 f x.
Proof. exact (@lem342211 A lt2 f x (@lem342207 A lt2 f x)). Qed.
Lemma lem342213 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (x : nat -> A) (h1 : term564 A lt2 f x) : term564 A lt2 f x.
Proof. exact (h1). Qed.
Lemma lem342214 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (x : nat -> A) (h1 : term559 A lt2 f x) : term559 A lt2 f x.
Proof. exact (h1). Qed.
Lemma lem342215 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (x : nat -> A) (h1 : term559 A lt2 f x) (h2 : term564 A lt2 f x) : term499 A lt2 f x.
Proof. exact (@lem342213 A lt2 f x h2 (@lem342214 A lt2 f x h1)). Qed.
Lemma lem342216 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (x : nat -> A) (h1 : term559 A lt2 f x) : term570 A lt2 f x.
Proof. exact (fun h0 : term564 A lt2 f x => @lem342215 A lt2 f x h1 h0). Qed.
Lemma lem342217 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (x : nat -> A) (h1 : term564 A lt2 f x) : term564 A lt2 f x.
Proof. exact (h1). Qed.
Lemma lem342218 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (x : nat -> A) (h1 : term559 A lt2 f x) (h2 : term564 A lt2 f x) : term499 A lt2 f x.
Proof. exact (@lem342216 A lt2 f x h1 (@lem342217 A lt2 f x h2)). Qed.
Lemma lem342219 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (x : nat -> A) (h1 : term564 A lt2 f x) : term564 A lt2 f x.
Proof. exact (fun h0 : term559 A lt2 f x => @lem342218 A lt2 f x h0 h1). Qed.
Lemma lem342220 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (x : nat -> A) : term569 A lt2 f x.
Proof. exact (fun h0 : term564 A lt2 f x => @lem342219 A lt2 f x h0). Qed.
Lemma lem342223 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (x : nat -> A) : term564 A lt2 f x.
Proof. exact (@lem342220 A lt2 f x (@lem342212 A lt2 f x)). Qed.
Lemma lem342224 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (x : nat -> A) : term564 A lt2 f x.
Proof. exact (@lem342223 A lt2 f x). Qed.
Lemma lem342330 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem342331 {A : Type'} (f : A -> nat) (x : nat -> A) : (term571 A f x) = (term490 A f x).
Proof. exact (@lem342330 ((term471 A f x) = (term489 A f x))). Qed.
Lemma lem342404 {A : Type'} (f : A -> nat) (x : nat -> A) : (term572 A f x) = (term572 A f x).
Proof. exact (eq_refl (term572 A f x)). Qed.
Lemma lem342405 {A : Type'} (f : A -> nat) (x : nat -> A) : (term553 A f x) = (term573 A f x).
Proof. exact (MK_COMB (@lem342404 A f x) (@lem342331 A f x)). Qed.
Lemma lem342408 {A : Type'} (f : A -> nat) (_7410 : type414 A) (lt2 : type1402 A) (x : nat -> A) : (term552 A f _7410 lt2 x) = (term552 A f _7410 lt2 x).
Proof. exact (eq_refl (term552 A f _7410 lt2 x)). Qed.
Lemma lem342409 {A : Type'} (_7410 : type414 A) (lt2 : type1402 A) (f : A -> nat) (x : nat -> A) : (term554 A _7410 lt2 f x) = (term574 A _7410 lt2 f x).
Proof. exact (MK_COMB (@lem342408 A f _7410 lt2 x) (@lem342405 A f x)). Qed.
Lemma lem342412 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : (term492 A lt2 x) = (term492 A lt2 x).
Proof. exact (eq_refl (term492 A lt2 x)). Qed.
Lemma lem342413 {A : Type'} (_7410 : type414 A) (lt2 : type1402 A) (f : A -> nat) (x : nat -> A) : (term555 A _7410 lt2 f x) = (term575 A _7410 lt2 f x).
Proof. exact (MK_COMB (@lem342412 A lt2 x) (@lem342409 A _7410 lt2 f x)). Qed.
Lemma lem342416 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : (term39 A lt2 x) = (term39 A lt2 x).
Proof. exact (eq_refl (term39 A lt2 x)). Qed.
Lemma lem342417 {A : Type'} (_7410 : type414 A) (lt2 : type1402 A) (f : A -> nat) (x : nat -> A) : (term556 A _7410 lt2 f x) = (term576 A _7410 lt2 f x).
Proof. exact (MK_COMB (@lem342416 A lt2 x) (@lem342413 A _7410 lt2 f x)). Qed.
Lemma lem342420 {A : Type'} (lt2 : type1402 A) : (term42 A lt2) = (term42 A lt2).
Proof. exact (eq_refl (term42 A lt2)). Qed.
Lemma lem342421 {A : Type'} (_7410 : type414 A) (lt2 : type1402 A) (f : A -> nat) (x : nat -> A) : (term557 A _7410 lt2 f x) = (term577 A _7410 lt2 f x).
Proof. exact (MK_COMB (@lem342420 A lt2) (@lem342417 A _7410 lt2 f x)). Qed.
Lemma lem342424 {A : Type'} (_7410 : type414 A) : (term546 A _7410) = (term546 A _7410).
Proof. exact (eq_refl (term546 A _7410)). Qed.
Lemma lem342425 {A : Type'} (_7410 : type414 A) (lt2 : type1402 A) (f : A -> nat) (x : nat -> A) : (term558 A _7410 lt2 f x) = (term578 A _7410 lt2 f x).
Proof. exact (MK_COMB (@lem342424 A _7410) (@lem342421 A _7410 lt2 f x)). Qed.
Lemma lem342428 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (x : nat -> A) : (term579 A lt2 f x) = (term580 A lt2 f x).
Proof. exact (fun_ext (fun _7410 : type414 A => @lem342425 A _7410 lt2 f x)). Qed.
Lemma lem342429 {A : Type'} : (@all ((A -> A -> Prop) -> (nat -> A) -> nat -> nat)) = (@all ((A -> A -> Prop) -> (nat -> A) -> nat -> nat)).
Proof. exact (eq_refl (@all ((A -> A -> Prop) -> (nat -> A) -> nat -> nat))). Qed.
Lemma lem342430 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (x : nat -> A) : (term559 A lt2 f x) = (term581 A lt2 f x).
Proof. exact (MK_COMB (@lem342429 A) (@lem342428 A lt2 f x)). Qed.
Lemma lem342435 {A : Type'} (f : A -> nat) (x : nat -> A) : (term582 A f x) = (term583 A f x).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem342430 A lt2 f x)). Qed.
Lemma lem342436 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem342437 {A : Type'} (f : A -> nat) (x : nat -> A) : (term584 A f x) = (term585 A f x).
Proof. exact (MK_COMB (@lem342436 A) (@lem342435 A f x)). Qed.
Lemma lem342442 {A : Type'} (x : nat -> A) : (term586 A x) = (term587 A x).
Proof. exact (fun_ext (fun f : A -> nat => @lem342437 A f x)). Qed.
Lemma lem342443 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem342444 {A : Type'} (x : nat -> A) : (term588 A x) = (term589 A x).
Proof. exact (MK_COMB (@lem342443 A) (@lem342442 A x)). Qed.
Lemma lem342449 {A : Type'} : (term590 A) = (term591 A).
Proof. exact (fun_ext (fun x : nat -> A => @lem342444 A x)). Qed.
Lemma lem342450 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem342459 {A : Type'} : (term592 A) = (term593 A).
Proof. exact (MK_COMB (@lem342450 A) (@lem342449 A)). Qed.
Lemma lem342460 {A : Type'} (m : nat) (f : A -> nat) (x : nat -> A) (i : nat) : (m = (term406 A f x i)) = (m = (term406 A f x i)).
Proof. exact (eq_refl (m = (term406 A f x i))). Qed.
Lemma lem342461 {A : Type'} (m : nat) (f : A -> nat) (x : nat -> A) : (term594 A m f x) = (term594 A m f x).
Proof. exact (fun_ext (fun i : nat => @lem342460 A m f x i)). Qed.
Lemma lem342462 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem342463 {A : Type'} (m : nat) (f : A -> nat) (x : nat -> A) : (term467 A m f x) = (term467 A m f x).
Proof. exact (MK_COMB (@lem342462) (@lem342461 A m f x)). Qed.
Lemma lem342464 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem342465 {A : Type'} (m : nat) (f : A -> nat) (x : nat -> A) : (term477 A m f x) = (term477 A m f x).
Proof. exact (MK_COMB (@lem342464) (@lem342463 A m f x)). Qed.
Lemma lem342468 (m : nat) (n : nat) : (term478 m n) = (term478 m n).
Proof. exact (eq_refl (term478 m n)). Qed.
Lemma lem342469 {A : Type'} (n : nat) (m : nat) (f : A -> nat) (x : nat -> A) : (term480 A n m f x) = (term480 A n m f x).
Proof. exact (MK_COMB (@lem342468 m n) (@lem342465 A m f x)). Qed.
Lemma lem342470 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term482 A n f x) = (term482 A n f x).
Proof. exact (fun_ext (fun m : nat => @lem342469 A n m f x)). Qed.
Lemma lem342471 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem342472 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term484 A n f x) = (term484 A n f x).
Proof. exact (MK_COMB (@lem342471) (@lem342470 A n f x)). Qed.
Lemma lem342473 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) (i : nat) : (n = (term406 A f x i)) = (n = (term406 A f x i)).
Proof. exact (eq_refl (n = (term406 A f x i))). Qed.
Lemma lem342474 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term594 A n f x) = (term594 A n f x).
Proof. exact (fun_ext (fun i : nat => @lem342473 A n f x i)). Qed.
Lemma lem342475 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem342476 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term467 A n f x) = (term467 A n f x).
Proof. exact (MK_COMB (@lem342475) (@lem342474 A n f x)). Qed.
Lemma lem342477 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem342478 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term475 A n f x) = (term475 A n f x).
Proof. exact (MK_COMB (@lem342477) (@lem342476 A n f x)). Qed.
Lemma lem342479 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term486 A n f x) = (term486 A n f x).
Proof. exact (MK_COMB (@lem342478 A n f x) (@lem342472 A n f x)). Qed.
Lemma lem342480 {A : Type'} (f : A -> nat) (x : nat -> A) : (term488 A f x) = (term488 A f x).
Proof. exact (fun_ext (fun n : nat => @lem342479 A n f x)). Qed.
Lemma lem342481 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem342482 {A : Type'} (f : A -> nat) (x : nat -> A) : (term489 A f x) = (term489 A f x).
Proof. exact (MK_COMB (@lem342481) (@lem342480 A f x)). Qed.
Lemma lem342483 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) (i : nat) : (n = (term406 A f x i)) = (n = (term406 A f x i)).
Proof. exact (eq_refl (n = (term406 A f x i))). Qed.
Lemma lem342484 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term594 A n f x) = (term594 A n f x).
Proof. exact (fun_ext (fun i : nat => @lem342483 A n f x i)). Qed.
Lemma lem342485 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem342486 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term467 A n f x) = (term467 A n f x).
Proof. exact (MK_COMB (@lem342485) (@lem342484 A n f x)). Qed.
Lemma lem342487 {A : Type'} (f : A -> nat) (x : nat -> A) : (term1 A f x) = (term1 A f x).
Proof. exact (fun_ext (fun n : nat => @lem342486 A n f x)). Qed.
Lemma lem342488 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem342489 {A : Type'} (f : A -> nat) (x : nat -> A) : (term471 A f x) = (term471 A f x).
Proof. exact (MK_COMB (@lem342488) (@lem342487 A f x)). Qed.
Lemma lem342490 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem342491 {A : Type'} (f : A -> nat) (x : nat -> A) : (term473 A f x) = (term473 A f x).
Proof. exact (MK_COMB (@lem342490) (@lem342489 A f x)). Qed.
Lemma lem342492 {A : Type'} (f : A -> nat) (x : nat -> A) : ((term471 A f x) = (term489 A f x)) = ((term471 A f x) = (term489 A f x)).
Proof. exact (MK_COMB (@lem342491 A f x) (@lem342482 A f x)). Qed.
Lemma lem342493 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem342494 {A : Type'} (f : A -> nat) (x : nat -> A) : (term490 A f x) = (term490 A f x).
Proof. exact (MK_COMB (@lem342493) (@lem342492 A f x)). Qed.
Lemma lem342495 {A : Type'} (k : nat) (f : A -> nat) (x : nat -> A) (n : nat) : (term595 A k f x n) = (term595 A k f x n).
Proof. exact (eq_refl (term595 A k f x n)). Qed.
Lemma lem342496 {A : Type'} (f : A -> nat) (x : nat -> A) (n : nat) : (term460 A f x n) = (term460 A f x n).
Proof. exact (fun_ext (fun k : nat => @lem342495 A k f x n)). Qed.
Lemma lem342497 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem342498 {A : Type'} (f : A -> nat) (x : nat -> A) (n : nat) : (term459 A f x n) = (term459 A f x n).
Proof. exact (MK_COMB (@lem342497) (@lem342496 A f x n)). Qed.
Lemma lem342499 {A : Type'} (f : A -> nat) (x : nat -> A) : (term596 A f x) = (term596 A f x).
Proof. exact (fun_ext (fun n : nat => @lem342498 A f x n)). Qed.
Lemma lem342500 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem342501 {A : Type'} (f : A -> nat) (x : nat -> A) : (term450 A f x) = (term450 A f x).
Proof. exact (MK_COMB (@lem342500) (@lem342499 A f x)). Qed.
Lemma lem342502 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem342503 {A : Type'} (f : A -> nat) (x : nat -> A) : (term572 A f x) = (term572 A f x).
Proof. exact (MK_COMB (@lem342502) (@lem342501 A f x)). Qed.
Lemma lem342504 {A : Type'} (f : A -> nat) (x : nat -> A) : (term573 A f x) = (term573 A f x).
Proof. exact (MK_COMB (@lem342503 A f x) (@lem342494 A f x)). Qed.
Lemma lem342505 {A : Type'} (f : A -> nat) (_7410 : type414 A) (lt2 : type1402 A) (x : nat -> A) (n : nat) : ((term406 A f x n) = (term548 A f _7410 lt2 x n)) = ((term406 A f x n) = (term548 A f _7410 lt2 x n)).
Proof. exact (eq_refl ((term406 A f x n) = (term548 A f _7410 lt2 x n))). Qed.
Lemma lem342506 {A : Type'} (f : A -> nat) (_7410 : type414 A) (lt2 : type1402 A) (x : nat -> A) : (term549 A f _7410 lt2 x) = (term549 A f _7410 lt2 x).
Proof. exact (fun_ext (fun n : nat => @lem342505 A f _7410 lt2 x n)). Qed.
Lemma lem342507 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem342508 {A : Type'} (f : A -> nat) (_7410 : type414 A) (lt2 : type1402 A) (x : nat -> A) : (term550 A f _7410 lt2 x) = (term550 A f _7410 lt2 x).
Proof. exact (MK_COMB (@lem342507) (@lem342506 A f _7410 lt2 x)). Qed.
Lemma lem342509 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem342510 {A : Type'} (f : A -> nat) (_7410 : type414 A) (lt2 : type1402 A) (x : nat -> A) : (term552 A f _7410 lt2 x) = (term552 A f _7410 lt2 x).
Proof. exact (MK_COMB (@lem342509) (@lem342508 A f _7410 lt2 x)). Qed.
Lemma lem342511 {A : Type'} (_7410 : type414 A) (lt2 : type1402 A) (f : A -> nat) (x : nat -> A) : (term574 A _7410 lt2 f x) = (term574 A _7410 lt2 f x).
Proof. exact (MK_COMB (@lem342510 A f _7410 lt2 x) (@lem342504 A f x)). Qed.
Lemma lem342512 {A : Type'} (lt2 : type1402 A) (m : nat) (x : nat -> A) (n : nat) : (term52 A lt2 m x n) = (term52 A lt2 m x n).
Proof. exact (eq_refl (term52 A lt2 m x n)). Qed.
Lemma lem342513 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) : (term23 A lt2 x n) = (term23 A lt2 x n).
Proof. exact (fun_ext (fun m : nat => @lem342512 A lt2 m x n)). Qed.
Lemma lem342514 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem342515 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) : (term22 A lt2 x n) = (term22 A lt2 x n).
Proof. exact (MK_COMB (@lem342514) (@lem342513 A lt2 x n)). Qed.
Lemma lem342516 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : (term28 A lt2 x) = (term28 A lt2 x).
Proof. exact (fun_ext (fun n : nat => @lem342515 A lt2 x n)). Qed.
Lemma lem342517 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem342518 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : (term29 A lt2 x) = (term29 A lt2 x).
Proof. exact (MK_COMB (@lem342517) (@lem342516 A lt2 x)). Qed.
Lemma lem342519 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem342520 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : (term492 A lt2 x) = (term492 A lt2 x).
Proof. exact (MK_COMB (@lem342519) (@lem342518 A lt2 x)). Qed.
Lemma lem342521 {A : Type'} (_7410 : type414 A) (lt2 : type1402 A) (f : A -> nat) (x : nat -> A) : (term575 A _7410 lt2 f x) = (term575 A _7410 lt2 f x).
Proof. exact (MK_COMB (@lem342520 A lt2 x) (@lem342511 A _7410 lt2 f x)). Qed.
Lemma lem342522 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) : (term53 A lt2 x n) = (term53 A lt2 x n).
Proof. exact (eq_refl (term53 A lt2 x n)). Qed.
Lemma lem342523 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : (term54 A lt2 x) = (term54 A lt2 x).
Proof. exact (fun_ext (fun n : nat => @lem342522 A lt2 x n)). Qed.
Lemma lem342524 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem342525 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : (term18 A lt2 x) = (term18 A lt2 x).
Proof. exact (MK_COMB (@lem342524) (@lem342523 A lt2 x)). Qed.
Lemma lem342526 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem342527 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : (term39 A lt2 x) = (term39 A lt2 x).
Proof. exact (MK_COMB (@lem342526) (@lem342525 A lt2 x)). Qed.
Lemma lem342528 {A : Type'} (_7410 : type414 A) (lt2 : type1402 A) (f : A -> nat) (x : nat -> A) : (term576 A _7410 lt2 f x) = (term576 A _7410 lt2 f x).
Proof. exact (MK_COMB (@lem342527 A lt2 x) (@lem342521 A _7410 lt2 f x)). Qed.
Lemma lem342529 {A : Type'} (H : type700 A) (f : A -> nat) (x : A) : ((f x) = (H f x)) = ((f x) = (H f x)).
Proof. exact (eq_refl ((f x) = (H f x))). Qed.
Lemma lem342530 {A : Type'} (H : type700 A) (f : A -> nat) : (term55 A H f) = (term55 A H f).
Proof. exact (fun_ext (fun x : A => @lem342529 A H f x)). Qed.
Lemma lem342531 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem342532 {A : Type'} (H : type700 A) (f : A -> nat) : (term56 A H f) = (term56 A H f).
Proof. exact (MK_COMB (@lem342531 A) (@lem342530 A H f)). Qed.
Lemma lem342533 {A : Type'} (H : type700 A) : (term57 A H) = (term57 A H).
Proof. exact (fun_ext (fun f : A -> nat => @lem342532 A H f)). Qed.
Lemma lem342534 {A : Type'} : (@ex (A -> nat)) = (@ex (A -> nat)).
Proof. exact (eq_refl (@ex (A -> nat))). Qed.
Lemma lem342535 {A : Type'} (H : type700 A) : (term58 A H) = (term58 A H).
Proof. exact (MK_COMB (@lem342534 A) (@lem342533 A H)). Qed.
Lemma lem342536 {A : Type'} (f : A -> nat) (H : type700 A) (g : A -> nat) (x : A) : ((H f x) = (H g x)) = ((H f x) = (H g x)).
Proof. exact (eq_refl ((H f x) = (H g x))). Qed.
Lemma lem342541 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> nat) (g : A -> nat) (z : A) : (term59 A lt2 x f g z) = (term59 A lt2 x f g z).
Proof. exact (eq_refl (term59 A lt2 x f g z)). Qed.
Lemma lem342542 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> nat) (g : A -> nat) : (term60 A lt2 x f g) = (term60 A lt2 x f g).
Proof. exact (fun_ext (fun z : A => @lem342541 A lt2 x f g z)). Qed.
Lemma lem342543 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem342544 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> nat) (g : A -> nat) : (term61 A lt2 x f g) = (term61 A lt2 x f g).
Proof. exact (MK_COMB (@lem342543 A) (@lem342542 A lt2 x f g)). Qed.
Lemma lem342545 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem342546 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> nat) (g : A -> nat) : (term62 A lt2 x f g) = (term62 A lt2 x f g).
Proof. exact (MK_COMB (@lem342545) (@lem342544 A lt2 x f g)). Qed.
Lemma lem342547 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) (g : A -> nat) (x : A) : (term63 A lt2 f H g x) = (term63 A lt2 f H g x).
Proof. exact (MK_COMB (@lem342546 A lt2 x f g) (@lem342536 A f H g x)). Qed.
Lemma lem342548 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) (g : A -> nat) : (term64 A lt2 f H g) = (term64 A lt2 f H g).
Proof. exact (fun_ext (fun x : A => @lem342547 A lt2 f H g x)). Qed.
Lemma lem342549 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem342550 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) (g : A -> nat) : (term65 A lt2 f H g) = (term65 A lt2 f H g).
Proof. exact (MK_COMB (@lem342549 A) (@lem342548 A lt2 f H g)). Qed.
Lemma lem342551 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) : (term66 A lt2 f H) = (term66 A lt2 f H).
Proof. exact (fun_ext (fun g : A -> nat => @lem342550 A lt2 f H g)). Qed.
Lemma lem342552 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem342553 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) : (term67 A lt2 f H) = (term67 A lt2 f H).
Proof. exact (MK_COMB (@lem342552 A) (@lem342551 A lt2 f H)). Qed.
Lemma lem342554 {A : Type'} (lt2 : type1402 A) (H : type700 A) : (term68 A lt2 H) = (term68 A lt2 H).
Proof. exact (fun_ext (fun f : A -> nat => @lem342553 A lt2 f H)). Qed.
Lemma lem342555 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem342556 {A : Type'} (lt2 : type1402 A) (H : type700 A) : (term69 A lt2 H) = (term69 A lt2 H).
Proof. exact (MK_COMB (@lem342555 A) (@lem342554 A lt2 H)). Qed.
Lemma lem342557 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem342558 {A : Type'} (lt2 : type1402 A) (H : type700 A) : (term70 A lt2 H) = (term70 A lt2 H).
Proof. exact (MK_COMB (@lem342557) (@lem342556 A lt2 H)). Qed.
Lemma lem342559 {A : Type'} (lt2 : type1402 A) (H : type700 A) : (term71 A lt2 H) = (term71 A lt2 H).
Proof. exact (MK_COMB (@lem342558 A lt2 H) (@lem342535 A H)). Qed.
Lemma lem342560 {A : Type'} (lt2 : type1402 A) : (term72 A lt2) = (term72 A lt2).
Proof. exact (fun_ext (fun H : type700 A => @lem342559 A lt2 H)). Qed.
Lemma lem342561 {A : Type'} : (@all ((A -> nat) -> A -> nat)) = (@all ((A -> nat) -> A -> nat)).
Proof. exact (eq_refl (@all ((A -> nat) -> A -> nat))). Qed.
Lemma lem342562 {A : Type'} (lt2 : type1402 A) : (term15 A lt2) = (term15 A lt2).
Proof. exact (MK_COMB (@lem342561 A) (@lem342560 A lt2)). Qed.
Lemma lem342563 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem342564 {A : Type'} (lt2 : type1402 A) : (term42 A lt2) = (term42 A lt2).
Proof. exact (MK_COMB (@lem342563) (@lem342562 A lt2)). Qed.
Lemma lem342565 {A : Type'} (_7410 : type414 A) (lt2 : type1402 A) (f : A -> nat) (x : nat -> A) : (term577 A _7410 lt2 f x) = (term577 A _7410 lt2 f x).
Proof. exact (MK_COMB (@lem342564 A lt2) (@lem342528 A _7410 lt2 f x)). Qed.
Lemma lem342570 {A : Type'} (x : nat) (_7410 : type414 A) (lt2 : type1402 A) (x' : nat -> A) (n : nat) : (term533 A x _7410 lt2 x' n) = (term533 A x _7410 lt2 x' n).
Proof. exact (eq_refl (term533 A x _7410 lt2 x' n)). Qed.
Lemma lem342571 {A : Type'} (_7410 : type414 A) (lt2 : type1402 A) (x : nat -> A) (n : nat) : (term534 A _7410 lt2 x n) = (term534 A _7410 lt2 x n).
Proof. exact (fun_ext (fun x' : nat => @lem342570 A x' _7410 lt2 x n)). Qed.
Lemma lem342572 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem342573 {A : Type'} (_7410 : type414 A) (lt2 : type1402 A) (x : nat -> A) (n : nat) : (term535 A _7410 lt2 x n) = (term535 A _7410 lt2 x n).
Proof. exact (MK_COMB (@lem342572) (@lem342571 A _7410 lt2 x n)). Qed.
Lemma lem342574 {A : Type'} (_7410 : type414 A) (lt2 : type1402 A) (x : nat -> A) : (term537 A _7410 lt2 x) = (term537 A _7410 lt2 x).
Proof. exact (fun_ext (fun n : nat => @lem342573 A _7410 lt2 x n)). Qed.
Lemma lem342575 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem342576 {A : Type'} (_7410 : type414 A) (lt2 : type1402 A) (x : nat -> A) : (term538 A _7410 lt2 x) = (term538 A _7410 lt2 x).
Proof. exact (MK_COMB (@lem342575) (@lem342574 A _7410 lt2 x)). Qed.
Lemma lem342577 {A : Type'} (_7410 : type414 A) (lt2 : type1402 A) : (term540 A _7410 lt2) = (term540 A _7410 lt2).
Proof. exact (fun_ext (fun x : nat -> A => @lem342576 A _7410 lt2 x)). Qed.
Lemma lem342578 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem342579 {A : Type'} (_7410 : type414 A) (lt2 : type1402 A) : (term541 A _7410 lt2) = (term541 A _7410 lt2).
Proof. exact (MK_COMB (@lem342578 A) (@lem342577 A _7410 lt2)). Qed.
Lemma lem342580 {A : Type'} (_7410 : type414 A) : (term543 A _7410) = (term543 A _7410).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem342579 A _7410 lt2)). Qed.
Lemma lem342581 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem342582 {A : Type'} (_7410 : type414 A) : (term544 A _7410) = (term544 A _7410).
Proof. exact (MK_COMB (@lem342581 A) (@lem342580 A _7410)). Qed.
Lemma lem342583 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem342584 {A : Type'} (_7410 : type414 A) : (term546 A _7410) = (term546 A _7410).
Proof. exact (MK_COMB (@lem342583) (@lem342582 A _7410)). Qed.
Lemma lem342585 {A : Type'} (_7410 : type414 A) (lt2 : type1402 A) (f : A -> nat) (x : nat -> A) : (term578 A _7410 lt2 f x) = (term578 A _7410 lt2 f x).
Proof. exact (MK_COMB (@lem342584 A _7410) (@lem342565 A _7410 lt2 f x)). Qed.
Lemma lem342586 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (x : nat -> A) : (term580 A lt2 f x) = (term580 A lt2 f x).
Proof. exact (fun_ext (fun _7410 : type414 A => @lem342585 A _7410 lt2 f x)). Qed.
Lemma lem342587 {A : Type'} : (@all ((A -> A -> Prop) -> (nat -> A) -> nat -> nat)) = (@all ((A -> A -> Prop) -> (nat -> A) -> nat -> nat)).
Proof. exact (eq_refl (@all ((A -> A -> Prop) -> (nat -> A) -> nat -> nat))). Qed.
Lemma lem342588 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (x : nat -> A) : (term581 A lt2 f x) = (term581 A lt2 f x).
Proof. exact (MK_COMB (@lem342587 A) (@lem342586 A lt2 f x)). Qed.
Lemma lem342589 {A : Type'} (f : A -> nat) (x : nat -> A) : (term583 A f x) = (term583 A f x).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem342588 A lt2 f x)). Qed.
Lemma lem342590 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem342591 {A : Type'} (f : A -> nat) (x : nat -> A) : (term585 A f x) = (term585 A f x).
Proof. exact (MK_COMB (@lem342590 A) (@lem342589 A f x)). Qed.
Lemma lem342592 {A : Type'} (x : nat -> A) : (term587 A x) = (term587 A x).
Proof. exact (fun_ext (fun f : A -> nat => @lem342591 A f x)). Qed.
Lemma lem342593 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem342594 {A : Type'} (x : nat -> A) : (term589 A x) = (term589 A x).
Proof. exact (MK_COMB (@lem342593 A) (@lem342592 A x)). Qed.
Lemma lem342595 {A : Type'} : (term591 A) = (term591 A).
Proof. exact (fun_ext (fun x : nat -> A => @lem342594 A x)). Qed.
Lemma lem342596 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem342597 {A : Type'} : (term593 A) = (term593 A).
Proof. exact (MK_COMB (@lem342596 A) (@lem342595 A)). Qed.
Lemma lem342786 {A : Type'} : (term592 A) = (term593 A).
Proof. exact (TRANS (@lem342459 A) (@lem342597 A)). Qed.
Lemma lem342787 {A : Type'} : (term593 A) = (term592 A).
Proof. exact (SYM (@lem342786 A)). Qed.
Lemma lem342789 {A : Type'} (lt2 : type1402 A) (h1 : term15 A lt2) : term15 A lt2.
Proof. exact (h1). Qed.
Lemma lem342791 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (h1 : term29 A lt2 x) : term29 A lt2 x.
Proof. exact (h1). Qed.
Lemma lem342793 {A : Type'} (f : A -> nat) (x : nat -> A) (h1 : term450 A f x) : term450 A f x.
Proof. exact (h1). Qed.
Lemma lem342794 {A : Type'} (f : A -> nat) (x : nat -> A) (h1 : (term471 A f x) = (term489 A f x)) : (term471 A f x) = (term489 A f x).
Proof. exact (h1). Qed.
Lemma lem342949 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> nat) (g : A -> nat) (z : A) : (term59 A lt2 x f g z) = (term75 A lt2 x f g z).
Proof. exact (@lem17265 (lt2 z x) ((f z) = (g z))). Qed.
Lemma lem342950 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> nat) (g : A -> nat) : (term60 A lt2 x f g) = (term76 A lt2 x f g).
Proof. exact (fun_ext (fun z : A => @lem342949 A lt2 x f g z)). Qed.
Lemma lem342951 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem342952 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> nat) (g : A -> nat) : (term61 A lt2 x f g) = (term77 A lt2 x f g).
Proof. exact (MK_COMB (@lem342951 A) (@lem342950 A lt2 x f g)). Qed.
Lemma lem342953 {A : Type'} (f : A -> nat) (H : type700 A) (g : A -> nat) (x : A) : (term78 A f H g x) = (term78 A f H g x).
Proof. exact (eq_refl (term78 A f H g x)). Qed.
Lemma lem342954 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem342955 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> nat) (g : A -> nat) : (term79 A lt2 x f g) = (term80 A lt2 x f g).
Proof. exact (MK_COMB (@lem342954) (@lem342952 A lt2 x f g)). Qed.
Lemma lem342956 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) (g : A -> nat) (x : A) : (term81 A lt2 f H g x) = (term82 A lt2 f H g x).
Proof. exact (MK_COMB (@lem342955 A lt2 x f g) (@lem342953 A f H g x)). Qed.
Lemma lem342957 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) (g : A -> nat) (x : A) : (term83 A lt2 f H g x) = (term81 A lt2 f H g x).
Proof. exact (@lem17362 (term61 A lt2 x f g) ((H f x) = (H g x))). Qed.
Lemma lem342958 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) (g : A -> nat) (x : A) : (term83 A lt2 f H g x) = (term82 A lt2 f H g x).
Proof. exact (TRANS (@lem342957 A lt2 f H g x) (@lem342956 A lt2 f H g x)). Qed.
Lemma lem342959 {A : Type'} (P : A -> Prop) : (term84 A P) = (term85 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem342960 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) (g : A -> nat) : (term86 A lt2 f H g) = (term87 A lt2 f H g).
Proof. exact (@lem342959 A (term64 A lt2 f H g)). Qed.
Lemma lem342961 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) (g : A -> nat) (x : A) : (term88 A lt2 f H g x) = (term63 A lt2 f H g x).
Proof. exact (eq_refl (term88 A lt2 f H g x)). Qed.
Lemma lem342962 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem342963 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) (g : A -> nat) (x : A) : (term89 A lt2 f H g x) = (term83 A lt2 f H g x).
Proof. exact (MK_COMB (@lem342962) (@lem342961 A lt2 f H g x)). Qed.
Lemma lem342964 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) (g : A -> nat) (x : A) : (term89 A lt2 f H g x) = (term82 A lt2 f H g x).
Proof. exact (TRANS (@lem342963 A lt2 f H g x) (@lem342958 A lt2 f H g x)). Qed.
Lemma lem342965 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) (g : A -> nat) : (term90 A lt2 f H g) = (term91 A lt2 f H g).
Proof. exact (fun_ext (fun x : A => @lem342964 A lt2 f H g x)). Qed.
Lemma lem342966 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem342967 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) (g : A -> nat) : (term87 A lt2 f H g) = (term92 A lt2 f H g).
Proof. exact (MK_COMB (@lem342966 A) (@lem342965 A lt2 f H g)). Qed.
Lemma lem342968 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) (g : A -> nat) : (term86 A lt2 f H g) = (term92 A lt2 f H g).
Proof. exact (TRANS (@lem342960 A lt2 f H g) (@lem342967 A lt2 f H g)). Qed.
Lemma lem342969 {A : Type'} (P : type704 A) : (term93 A P) = (term94 A P).
Proof. exact (@lem18392 (A -> nat) P). Qed.
Lemma lem342970 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) : (term95 A lt2 f H) = (term96 A lt2 f H).
Proof. exact (@lem342969 A (term66 A lt2 f H)). Qed.
Lemma lem342971 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) (g : A -> nat) : (term97 A lt2 f H g) = (term65 A lt2 f H g).
Proof. exact (eq_refl (term97 A lt2 f H g)). Qed.
Lemma lem342972 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem342973 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) (g : A -> nat) : (term98 A lt2 f H g) = (term86 A lt2 f H g).
Proof. exact (MK_COMB (@lem342972) (@lem342971 A lt2 f H g)). Qed.
Lemma lem342974 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) (g : A -> nat) : (term98 A lt2 f H g) = (term92 A lt2 f H g).
Proof. exact (TRANS (@lem342973 A lt2 f H g) (@lem342968 A lt2 f H g)). Qed.
Lemma lem342975 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) : (term99 A lt2 f H) = (term100 A lt2 f H).
Proof. exact (fun_ext (fun g : A -> nat => @lem342974 A lt2 f H g)). Qed.
Lemma lem342976 {A : Type'} : (@ex (A -> nat)) = (@ex (A -> nat)).
Proof. exact (eq_refl (@ex (A -> nat))). Qed.
Lemma lem342977 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) : (term96 A lt2 f H) = (term101 A lt2 f H).
Proof. exact (MK_COMB (@lem342976 A) (@lem342975 A lt2 f H)). Qed.
Lemma lem342978 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) : (term95 A lt2 f H) = (term101 A lt2 f H).
Proof. exact (TRANS (@lem342970 A lt2 f H) (@lem342977 A lt2 f H)). Qed.
Lemma lem342979 {A : Type'} (P : type704 A) : (term93 A P) = (term94 A P).
Proof. exact (@lem18392 (A -> nat) P). Qed.
Lemma lem342980 {A : Type'} (lt2 : type1402 A) (H : type700 A) : (term102 A lt2 H) = (term103 A lt2 H).
Proof. exact (@lem342979 A (term68 A lt2 H)). Qed.
Lemma lem342981 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) : (term104 A lt2 H f) = (term67 A lt2 f H).
Proof. exact (eq_refl (term104 A lt2 H f)). Qed.
Lemma lem342982 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem342983 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) : (term105 A lt2 H f) = (term95 A lt2 f H).
Proof. exact (MK_COMB (@lem342982) (@lem342981 A lt2 f H)). Qed.
Lemma lem342984 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) : (term105 A lt2 H f) = (term101 A lt2 f H).
Proof. exact (TRANS (@lem342983 A lt2 f H) (@lem342978 A lt2 f H)). Qed.
Lemma lem342985 {A : Type'} (lt2 : type1402 A) (H : type700 A) : (term106 A lt2 H) = (term107 A lt2 H).
Proof. exact (fun_ext (fun f : A -> nat => @lem342984 A lt2 f H)). Qed.
Lemma lem342986 {A : Type'} : (@ex (A -> nat)) = (@ex (A -> nat)).
Proof. exact (eq_refl (@ex (A -> nat))). Qed.
Lemma lem342987 {A : Type'} (lt2 : type1402 A) (H : type700 A) : (term103 A lt2 H) = (term108 A lt2 H).
Proof. exact (MK_COMB (@lem342986 A) (@lem342985 A lt2 H)). Qed.
Lemma lem342988 {A : Type'} (lt2 : type1402 A) (H : type700 A) : (term102 A lt2 H) = (term108 A lt2 H).
Proof. exact (TRANS (@lem342980 A lt2 H) (@lem342987 A lt2 H)). Qed.
Lemma lem342989 {A : Type'} (H : type700 A) (f : A -> nat) (x : A) : ((f x) = (H f x)) = ((f x) = (H f x)).
Proof. exact (eq_refl ((f x) = (H f x))). Qed.
Lemma lem342990 {A : Type'} (H : type700 A) (f : A -> nat) : (term55 A H f) = (term55 A H f).
Proof. exact (fun_ext (fun x : A => @lem342989 A H f x)). Qed.
Lemma lem342991 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem342992 {A : Type'} (H : type700 A) (f : A -> nat) : (term56 A H f) = (term56 A H f).
Proof. exact (MK_COMB (@lem342991 A) (@lem342990 A H f)). Qed.
Lemma lem342993 {A : Type'} (H : type700 A) : (term57 A H) = (term57 A H).
Proof. exact (fun_ext (fun f : A -> nat => @lem342992 A H f)). Qed.
Lemma lem342994 {A : Type'} : (@ex (A -> nat)) = (@ex (A -> nat)).
Proof. exact (eq_refl (@ex (A -> nat))). Qed.
Lemma lem342995 {A : Type'} (H : type700 A) : (term58 A H) = (term58 A H).
Proof. exact (MK_COMB (@lem342994 A) (@lem342993 A H)). Qed.
Lemma lem342996 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem342997 {A : Type'} (lt2 : type1402 A) (H : type700 A) : (term109 A lt2 H) = (term110 A lt2 H).
Proof. exact (MK_COMB (@lem342996) (@lem342988 A lt2 H)). Qed.
Lemma lem342998 {A : Type'} (lt2 : type1402 A) (H : type700 A) : (term111 A lt2 H) = (term112 A lt2 H).
Proof. exact (MK_COMB (@lem342997 A lt2 H) (@lem342995 A H)). Qed.
Lemma lem342999 {A : Type'} (lt2 : type1402 A) (H : type700 A) : (term71 A lt2 H) = (term111 A lt2 H).
Proof. exact (@lem17265 (term69 A lt2 H) (term58 A H)). Qed.
Lemma lem343000 {A : Type'} (lt2 : type1402 A) (H : type700 A) : (term71 A lt2 H) = (term112 A lt2 H).
Proof. exact (TRANS (@lem342999 A lt2 H) (@lem342998 A lt2 H)). Qed.
Lemma lem343001 {A : Type'} (lt2 : type1402 A) : (term72 A lt2) = (term113 A lt2).
Proof. exact (fun_ext (fun H : type700 A => @lem343000 A lt2 H)). Qed.
Lemma lem343002 {A : Type'} : (@all ((A -> nat) -> A -> nat)) = (@all ((A -> nat) -> A -> nat)).
Proof. exact (eq_refl (@all ((A -> nat) -> A -> nat))). Qed.
Lemma lem343003 {A : Type'} (lt2 : type1402 A) : (term15 A lt2) = (term114 A lt2).
Proof. exact (MK_COMB (@lem343002 A) (@lem343001 A lt2)). Qed.
Lemma lem343166 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term115 A P Q) = (term116 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem343167 {A : Type'} (P : type704 A) (Q : type704 A) : (term117 A P Q) = (term118 A P Q).
Proof. exact (@lem343166 (A -> nat) P Q). Qed.
Lemma lem343168 {A : Type'} (lt2 : type1402 A) (H : type700 A) : (term119 A lt2 H) = (term120 A lt2 H).
Proof. exact (@lem343167 A (term107 A lt2 H) (term57 A H)). Qed.
Lemma lem343169 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) : (term121 A lt2 H f) = (term101 A lt2 f H).
Proof. exact (eq_refl (term121 A lt2 H f)). Qed.
Lemma lem343170 {A : Type'} (lt2 : type1402 A) (H : type700 A) : (term122 A lt2 H) = (term107 A lt2 H).
Proof. exact (fun_ext (fun f : A -> nat => @lem343169 A lt2 f H)). Qed.
Lemma lem343171 {A : Type'} : (@ex (A -> nat)) = (@ex (A -> nat)).
Proof. exact (eq_refl (@ex (A -> nat))). Qed.
Lemma lem343172 {A : Type'} (lt2 : type1402 A) (H : type700 A) : (term123 A lt2 H) = (term108 A lt2 H).
Proof. exact (MK_COMB (@lem343171 A) (@lem343170 A lt2 H)). Qed.
Lemma lem343173 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem343174 {A : Type'} (lt2 : type1402 A) (H : type700 A) : (term124 A lt2 H) = (term110 A lt2 H).
Proof. exact (MK_COMB (@lem343173) (@lem343172 A lt2 H)). Qed.
Lemma lem343175 {A : Type'} (H : type700 A) (f : A -> nat) : (term125 A H f) = (term56 A H f).
Proof. exact (eq_refl (term125 A H f)). Qed.
Lemma lem343176 {A : Type'} (H : type700 A) : (term126 A H) = (term57 A H).
Proof. exact (fun_ext (fun f : A -> nat => @lem343175 A H f)). Qed.
Lemma lem343177 {A : Type'} : (@ex (A -> nat)) = (@ex (A -> nat)).
Proof. exact (eq_refl (@ex (A -> nat))). Qed.
Lemma lem343178 {A : Type'} (H : type700 A) : (term127 A H) = (term58 A H).
Proof. exact (MK_COMB (@lem343177 A) (@lem343176 A H)). Qed.
Lemma lem343179 {A : Type'} (lt2 : type1402 A) (H : type700 A) : (term119 A lt2 H) = (term112 A lt2 H).
Proof. exact (MK_COMB (@lem343174 A lt2 H) (@lem343178 A H)). Qed.
Lemma lem343180 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem343181 {A : Type'} (lt2 : type1402 A) (H : type700 A) : (term128 A lt2 H) = (term129 A lt2 H).
Proof. exact (MK_COMB (@lem343180) (@lem343179 A lt2 H)). Qed.
Lemma lem343182 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) : (term121 A lt2 H f) = (term101 A lt2 f H).
Proof. exact (eq_refl (term121 A lt2 H f)). Qed.
Lemma lem343183 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem343184 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) : (term130 A lt2 H f) = (term131 A lt2 f H).
Proof. exact (MK_COMB (@lem343183) (@lem343182 A lt2 f H)). Qed.
Lemma lem343185 {A : Type'} (H : type700 A) (f : A -> nat) : (term125 A H f) = (term56 A H f).
Proof. exact (eq_refl (term125 A H f)). Qed.
Lemma lem343186 {A : Type'} (lt2 : type1402 A) (H : type700 A) (f : A -> nat) : (term132 A lt2 H f) = (term133 A lt2 H f).
Proof. exact (MK_COMB (@lem343184 A lt2 f H) (@lem343185 A H f)). Qed.
Lemma lem343187 {A : Type'} (lt2 : type1402 A) (H : type700 A) : (term134 A lt2 H) = (term135 A lt2 H).
Proof. exact (fun_ext (fun f : A -> nat => @lem343186 A lt2 H f)). Qed.
Lemma lem343188 {A : Type'} : (@ex (A -> nat)) = (@ex (A -> nat)).
Proof. exact (eq_refl (@ex (A -> nat))). Qed.
Lemma lem343189 {A : Type'} (lt2 : type1402 A) (H : type700 A) : (term120 A lt2 H) = (term136 A lt2 H).
Proof. exact (MK_COMB (@lem343188 A) (@lem343187 A lt2 H)). Qed.
Lemma lem343190 {A : Type'} (lt2 : type1402 A) (H : type700 A) : ((term119 A lt2 H) = (term120 A lt2 H)) = ((term112 A lt2 H) = (term136 A lt2 H)).
Proof. exact (MK_COMB (@lem343181 A lt2 H) (@lem343189 A lt2 H)). Qed.
Lemma lem343191 {A : Type'} (lt2 : type1402 A) (H : type700 A) : (term112 A lt2 H) = (term136 A lt2 H).
Proof. exact (EQ_MP (@lem343190 A lt2 H) (@lem343168 A lt2 H)). Qed.
Lemma lem343193 {A : Type'} (P : A -> Prop) (Q : Prop) : (term137 A P Q) = (term138 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem343194 {A : Type'} (P : type704 A) (Q : Prop) : (term139 A P Q) = (term140 A P Q).
Proof. exact (@lem343193 (A -> nat) P Q). Qed.
Lemma lem343195 {A : Type'} (lt2 : type1402 A) (H : type700 A) (f : A -> nat) : (term141 A lt2 H f) = (term142 A lt2 H f).
Proof. exact (@lem343194 A (term100 A lt2 f H) (term56 A H f)). Qed.
Lemma lem343196 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) (g : A -> nat) : (term143 A lt2 f H g) = (term92 A lt2 f H g).
Proof. exact (eq_refl (term143 A lt2 f H g)). Qed.
Lemma lem343197 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) : (term144 A lt2 f H) = (term100 A lt2 f H).
Proof. exact (fun_ext (fun g : A -> nat => @lem343196 A lt2 f H g)). Qed.
Lemma lem343198 {A : Type'} : (@ex (A -> nat)) = (@ex (A -> nat)).
Proof. exact (eq_refl (@ex (A -> nat))). Qed.
Lemma lem343199 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) : (term145 A lt2 f H) = (term101 A lt2 f H).
Proof. exact (MK_COMB (@lem343198 A) (@lem343197 A lt2 f H)). Qed.
Lemma lem343200 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem343201 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) : (term146 A lt2 f H) = (term131 A lt2 f H).
Proof. exact (MK_COMB (@lem343200) (@lem343199 A lt2 f H)). Qed.
Lemma lem343202 {A : Type'} (H : type700 A) (f : A -> nat) : (term56 A H f) = (term56 A H f).
Proof. exact (eq_refl (term56 A H f)). Qed.
Lemma lem343203 {A : Type'} (lt2 : type1402 A) (H : type700 A) (f : A -> nat) : (term141 A lt2 H f) = (term133 A lt2 H f).
Proof. exact (MK_COMB (@lem343201 A lt2 f H) (@lem343202 A H f)). Qed.
Lemma lem343204 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem343205 {A : Type'} (lt2 : type1402 A) (H : type700 A) (f : A -> nat) : (term147 A lt2 H f) = (term148 A lt2 H f).
Proof. exact (MK_COMB (@lem343204) (@lem343203 A lt2 H f)). Qed.
Lemma lem343206 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) (g : A -> nat) : (term143 A lt2 f H g) = (term92 A lt2 f H g).
Proof. exact (eq_refl (term143 A lt2 f H g)). Qed.
Lemma lem343207 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem343208 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) (g : A -> nat) : (term149 A lt2 f H g) = (term150 A lt2 f H g).
Proof. exact (MK_COMB (@lem343207) (@lem343206 A lt2 f H g)). Qed.
Lemma lem343209 {A : Type'} (H : type700 A) (f : A -> nat) : (term56 A H f) = (term56 A H f).
Proof. exact (eq_refl (term56 A H f)). Qed.
Lemma lem343210 {A : Type'} (lt2 : type1402 A) (g : A -> nat) (H : type700 A) (f : A -> nat) : (term151 A lt2 g H f) = (term152 A lt2 g H f).
Proof. exact (MK_COMB (@lem343208 A lt2 f H g) (@lem343209 A H f)). Qed.
Lemma lem343211 {A : Type'} (lt2 : type1402 A) (H : type700 A) (f : A -> nat) : (term153 A lt2 H f) = (term154 A lt2 H f).
Proof. exact (fun_ext (fun g : A -> nat => @lem343210 A lt2 g H f)). Qed.
Lemma lem343212 {A : Type'} : (@ex (A -> nat)) = (@ex (A -> nat)).
Proof. exact (eq_refl (@ex (A -> nat))). Qed.
Lemma lem343213 {A : Type'} (lt2 : type1402 A) (H : type700 A) (f : A -> nat) : (term142 A lt2 H f) = (term155 A lt2 H f).
Proof. exact (MK_COMB (@lem343212 A) (@lem343211 A lt2 H f)). Qed.
Lemma lem343214 {A : Type'} (lt2 : type1402 A) (H : type700 A) (f : A -> nat) : ((term141 A lt2 H f) = (term142 A lt2 H f)) = ((term133 A lt2 H f) = (term155 A lt2 H f)).
Proof. exact (MK_COMB (@lem343205 A lt2 H f) (@lem343213 A lt2 H f)). Qed.
Lemma lem343215 {A : Type'} (lt2 : type1402 A) (H : type700 A) (f : A -> nat) : (term133 A lt2 H f) = (term155 A lt2 H f).
Proof. exact (EQ_MP (@lem343214 A lt2 H f) (@lem343195 A lt2 H f)). Qed.
Lemma lem343217 {A : Type'} (P : A -> Prop) (Q : Prop) : (term137 A P Q) = (term138 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem343218 {A : Type'} (P : A -> Prop) (Q : Prop) : (term137 A P Q) = (term138 A P Q).
Proof. exact (@lem343217 A P Q). Qed.
Lemma lem343219 {A : Type'} (lt2 : type1402 A) (g : A -> nat) (H : type700 A) (f : A -> nat) : (term156 A lt2 g H f) = (term157 A lt2 g H f).
Proof. exact (@lem343218 A (term91 A lt2 f H g) (term56 A H f)). Qed.
Lemma lem343220 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) (g : A -> nat) (x : A) : (term158 A lt2 f H g x) = (term82 A lt2 f H g x).
Proof. exact (eq_refl (term158 A lt2 f H g x)). Qed.
Lemma lem343221 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) (g : A -> nat) : (term159 A lt2 f H g) = (term91 A lt2 f H g).
Proof. exact (fun_ext (fun x : A => @lem343220 A lt2 f H g x)). Qed.
Lemma lem343222 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem343223 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) (g : A -> nat) : (term160 A lt2 f H g) = (term92 A lt2 f H g).
Proof. exact (MK_COMB (@lem343222 A) (@lem343221 A lt2 f H g)). Qed.
Lemma lem343224 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem343225 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) (g : A -> nat) : (term161 A lt2 f H g) = (term150 A lt2 f H g).
Proof. exact (MK_COMB (@lem343224) (@lem343223 A lt2 f H g)). Qed.
Lemma lem343226 {A : Type'} (H : type700 A) (f : A -> nat) : (term56 A H f) = (term56 A H f).
Proof. exact (eq_refl (term56 A H f)). Qed.
Lemma lem343227 {A : Type'} (lt2 : type1402 A) (g : A -> nat) (H : type700 A) (f : A -> nat) : (term156 A lt2 g H f) = (term152 A lt2 g H f).
Proof. exact (MK_COMB (@lem343225 A lt2 f H g) (@lem343226 A H f)). Qed.
Lemma lem343228 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem343229 {A : Type'} (lt2 : type1402 A) (g : A -> nat) (H : type700 A) (f : A -> nat) : (term162 A lt2 g H f) = (term163 A lt2 g H f).
Proof. exact (MK_COMB (@lem343228) (@lem343227 A lt2 g H f)). Qed.
Lemma lem343230 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) (g : A -> nat) (x : A) : (term158 A lt2 f H g x) = (term82 A lt2 f H g x).
Proof. exact (eq_refl (term158 A lt2 f H g x)). Qed.
Lemma lem343231 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem343232 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (H : type700 A) (g : A -> nat) (x : A) : (term164 A lt2 f H g x) = (term165 A lt2 f H g x).
Proof. exact (MK_COMB (@lem343231) (@lem343230 A lt2 f H g x)). Qed.
Lemma lem343233 {A : Type'} (H : type700 A) (f : A -> nat) : (term56 A H f) = (term56 A H f).
Proof. exact (eq_refl (term56 A H f)). Qed.
Lemma lem343234 {A : Type'} (lt2 : type1402 A) (g : A -> nat) (x : A) (H : type700 A) (f : A -> nat) : (term166 A lt2 g x H f) = (term167 A lt2 g x H f).
Proof. exact (MK_COMB (@lem343232 A lt2 f H g x) (@lem343233 A H f)). Qed.
Lemma lem343235 {A : Type'} (lt2 : type1402 A) (g : A -> nat) (H : type700 A) (f : A -> nat) : (term168 A lt2 g H f) = (term169 A lt2 g H f).
Proof. exact (fun_ext (fun x : A => @lem343234 A lt2 g x H f)). Qed.
Lemma lem343236 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem343237 {A : Type'} (lt2 : type1402 A) (g : A -> nat) (H : type700 A) (f : A -> nat) : (term157 A lt2 g H f) = (term170 A lt2 g H f).
Proof. exact (MK_COMB (@lem343236 A) (@lem343235 A lt2 g H f)). Qed.
Lemma lem343238 {A : Type'} (lt2 : type1402 A) (g : A -> nat) (H : type700 A) (f : A -> nat) : ((term156 A lt2 g H f) = (term157 A lt2 g H f)) = ((term152 A lt2 g H f) = (term170 A lt2 g H f)).
Proof. exact (MK_COMB (@lem343229 A lt2 g H f) (@lem343237 A lt2 g H f)). Qed.
Lemma lem343239 {A : Type'} (lt2 : type1402 A) (g : A -> nat) (H : type700 A) (f : A -> nat) : (term152 A lt2 g H f) = (term170 A lt2 g H f).
Proof. exact (EQ_MP (@lem343238 A lt2 g H f) (@lem343219 A lt2 g H f)). Qed.
Lemma lem343240 {A : Type'} (lt2 : type1402 A) (H : type700 A) (f : A -> nat) : (term154 A lt2 H f) = (term171 A lt2 H f).
Proof. exact (fun_ext (fun g : A -> nat => @lem343239 A lt2 g H f)). Qed.
Lemma lem343241 {A : Type'} : (@ex (A -> nat)) = (@ex (A -> nat)).
Proof. exact (eq_refl (@ex (A -> nat))). Qed.
Lemma lem343242 {A : Type'} (lt2 : type1402 A) (H : type700 A) (f : A -> nat) : (term155 A lt2 H f) = (term172 A lt2 H f).
Proof. exact (MK_COMB (@lem343241 A) (@lem343240 A lt2 H f)). Qed.
Lemma lem343243 {A : Type'} (lt2 : type1402 A) (H : type700 A) (f : A -> nat) : (term133 A lt2 H f) = (term172 A lt2 H f).
Proof. exact (TRANS (@lem343215 A lt2 H f) (@lem343242 A lt2 H f)). Qed.
Lemma lem343244 {A : Type'} (lt2 : type1402 A) (H : type700 A) : (term135 A lt2 H) = (term173 A lt2 H).
Proof. exact (fun_ext (fun f : A -> nat => @lem343243 A lt2 H f)). Qed.
Lemma lem343245 {A : Type'} : (@ex (A -> nat)) = (@ex (A -> nat)).
Proof. exact (eq_refl (@ex (A -> nat))). Qed.
Lemma lem343246 {A : Type'} (lt2 : type1402 A) (H : type700 A) : (term136 A lt2 H) = (term174 A lt2 H).
Proof. exact (MK_COMB (@lem343245 A) (@lem343244 A lt2 H)). Qed.
Lemma lem343247 {A : Type'} (lt2 : type1402 A) (H : type700 A) : (term112 A lt2 H) = (term174 A lt2 H).
Proof. exact (TRANS (@lem343191 A lt2 H) (@lem343246 A lt2 H)). Qed.
Lemma lem343248 {A : Type'} (lt2 : type1402 A) : (term113 A lt2) = (term175 A lt2).
Proof. exact (fun_ext (fun H : type700 A => @lem343247 A lt2 H)). Qed.
Lemma lem343249 {A : Type'} : (@all ((A -> nat) -> A -> nat)) = (@all ((A -> nat) -> A -> nat)).
Proof. exact (eq_refl (@all ((A -> nat) -> A -> nat))). Qed.
Lemma lem343250 {A : Type'} (lt2 : type1402 A) : (term114 A lt2) = (term176 A lt2).
Proof. exact (MK_COMB (@lem343249 A) (@lem343248 A lt2)). Qed.
Lemma lem343252 {A B : Type'} (P : type1413 A B) : (term177 A B P) = (term178 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem343253 {A : Type'} (P : type182 A) : (term179 A P) = (term180 A P).
Proof. exact (@lem343252 (type700 A) (A -> nat) P). Qed.
Lemma lem343254 {A : Type'} (lt2 : type1402 A) : (term181 A lt2) = (term182 A lt2).
Proof. exact (@lem343253 A (term183 A lt2)). Qed.
Lemma lem343255 {A : Type'} (lt2 : type1402 A) (H : type700 A) : (term184 A lt2 H) = (term173 A lt2 H).
Proof. exact (eq_refl (term184 A lt2 H)). Qed.
Lemma lem343256 {A : Type'} (f : A -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem343257 {A : Type'} (lt2 : type1402 A) (H : type700 A) (f : A -> nat) : (term185 A lt2 H f) = (term186 A lt2 H f).
Proof. exact (MK_COMB (@lem343255 A lt2 H) (@lem343256 A f)). Qed.
Lemma lem343258 {A : Type'} (lt2 : type1402 A) (H : type700 A) (f : A -> nat) : (term186 A lt2 H f) = (term172 A lt2 H f).
Proof. exact (eq_refl (term186 A lt2 H f)). Qed.
Lemma lem343259 {A : Type'} (lt2 : type1402 A) (H : type700 A) (f : A -> nat) : (term185 A lt2 H f) = (term172 A lt2 H f).
Proof. exact (TRANS (@lem343257 A lt2 H f) (@lem343258 A lt2 H f)). Qed.
Lemma lem343260 {A : Type'} (lt2 : type1402 A) (H : type700 A) : (term187 A lt2 H) = (term173 A lt2 H).
Proof. exact (fun_ext (fun f : A -> nat => @lem343259 A lt2 H f)). Qed.
Lemma lem343261 {A : Type'} : (@ex (A -> nat)) = (@ex (A -> nat)).
Proof. exact (eq_refl (@ex (A -> nat))). Qed.
Lemma lem343262 {A : Type'} (lt2 : type1402 A) (H : type700 A) : (term188 A lt2 H) = (term174 A lt2 H).
Proof. exact (MK_COMB (@lem343261 A) (@lem343260 A lt2 H)). Qed.
Lemma lem343263 {A : Type'} (lt2 : type1402 A) : (term189 A lt2) = (term175 A lt2).
Proof. exact (fun_ext (fun H : type700 A => @lem343262 A lt2 H)). Qed.
Lemma lem343264 {A : Type'} : (@all ((A -> nat) -> A -> nat)) = (@all ((A -> nat) -> A -> nat)).
Proof. exact (eq_refl (@all ((A -> nat) -> A -> nat))). Qed.
Lemma lem343265 {A : Type'} (lt2 : type1402 A) : (term181 A lt2) = (term176 A lt2).
Proof. exact (MK_COMB (@lem343264 A) (@lem343263 A lt2)). Qed.
Lemma lem343266 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem343267 {A : Type'} (lt2 : type1402 A) : (term190 A lt2) = (term191 A lt2).
Proof. exact (MK_COMB (@lem343266) (@lem343265 A lt2)). Qed.
Lemma lem343268 {A : Type'} (lt2 : type1402 A) (H : type700 A) : (term184 A lt2 H) = (term173 A lt2 H).
Proof. exact (eq_refl (term184 A lt2 H)). Qed.
Lemma lem343269 {A : Type'} (f : type184 A) (H : type700 A) : (f H) = (f H).
Proof. exact (eq_refl (f H)). Qed.
Lemma lem343270 {A : Type'} (lt2 : type1402 A) (f : type184 A) (H : type700 A) : (term192 A lt2 f H) = (term193 A lt2 f H).
Proof. exact (MK_COMB (@lem343268 A lt2 H) (@lem343269 A f H)). Qed.
Lemma lem343271 {A : Type'} (lt2 : type1402 A) (f : type184 A) (H : type700 A) : (term193 A lt2 f H) = (term194 A lt2 f H).
Proof. exact (eq_refl (term193 A lt2 f H)). Qed.
Lemma lem343272 {A : Type'} (lt2 : type1402 A) (f : type184 A) (H : type700 A) : (term192 A lt2 f H) = (term194 A lt2 f H).
Proof. exact (TRANS (@lem343270 A lt2 f H) (@lem343271 A lt2 f H)). Qed.
Lemma lem343273 {A : Type'} (lt2 : type1402 A) (f : type184 A) : (term195 A lt2 f) = (term196 A lt2 f).
Proof. exact (fun_ext (fun H : type700 A => @lem343272 A lt2 f H)). Qed.
Lemma lem343274 {A : Type'} : (@all ((A -> nat) -> A -> nat)) = (@all ((A -> nat) -> A -> nat)).
Proof. exact (eq_refl (@all ((A -> nat) -> A -> nat))). Qed.
Lemma lem343275 {A : Type'} (lt2 : type1402 A) (f : type184 A) : (term197 A lt2 f) = (term198 A lt2 f).
Proof. exact (MK_COMB (@lem343274 A) (@lem343273 A lt2 f)). Qed.
Lemma lem343276 {A : Type'} (lt2 : type1402 A) : (term199 A lt2) = (term200 A lt2).
Proof. exact (fun_ext (fun f : type184 A => @lem343275 A lt2 f)). Qed.
Lemma lem343277 {A : Type'} : (@ex (((A -> nat) -> A -> nat) -> A -> nat)) = (@ex (((A -> nat) -> A -> nat) -> A -> nat)).
Proof. exact (eq_refl (@ex (((A -> nat) -> A -> nat) -> A -> nat))). Qed.
Lemma lem343278 {A : Type'} (lt2 : type1402 A) : (term182 A lt2) = (term201 A lt2).
Proof. exact (MK_COMB (@lem343277 A) (@lem343276 A lt2)). Qed.
Lemma lem343279 {A : Type'} (lt2 : type1402 A) : ((term181 A lt2) = (term182 A lt2)) = ((term176 A lt2) = (term201 A lt2)).
Proof. exact (MK_COMB (@lem343267 A lt2) (@lem343278 A lt2)). Qed.
Lemma lem343280 {A : Type'} (lt2 : type1402 A) : (term176 A lt2) = (term201 A lt2).
Proof. exact (EQ_MP (@lem343279 A lt2) (@lem343254 A lt2)). Qed.
Lemma lem343282 {A B : Type'} (P : type1413 A B) : (term177 A B P) = (term178 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem343283 {A : Type'} (P : type182 A) : (term179 A P) = (term180 A P).
Proof. exact (@lem343282 (type700 A) (A -> nat) P). Qed.
Lemma lem343284 {A : Type'} (lt2 : type1402 A) (f : type184 A) : (term202 A lt2 f) = (term203 A lt2 f).
Proof. exact (@lem343283 A (term204 A lt2 f)). Qed.
Lemma lem343285 {A : Type'} (lt2 : type1402 A) (f : type184 A) (H : type700 A) : (term205 A lt2 f H) = (term206 A lt2 f H).
Proof. exact (eq_refl (term205 A lt2 f H)). Qed.
Lemma lem343286 {A : Type'} (g : A -> nat) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem343287 {A : Type'} (lt2 : type1402 A) (f : type184 A) (H : type700 A) (g : A -> nat) : (term207 A lt2 f H g) = (term208 A lt2 f H g).
Proof. exact (MK_COMB (@lem343285 A lt2 f H) (@lem343286 A g)). Qed.
Lemma lem343288 {A : Type'} (lt2 : type1402 A) (g : A -> nat) (f : type184 A) (H : type700 A) : (term208 A lt2 f H g) = (term209 A lt2 g f H).
Proof. exact (eq_refl (term208 A lt2 f H g)). Qed.
Lemma lem343289 {A : Type'} (lt2 : type1402 A) (g : A -> nat) (f : type184 A) (H : type700 A) : (term207 A lt2 f H g) = (term209 A lt2 g f H).
Proof. exact (TRANS (@lem343287 A lt2 f H g) (@lem343288 A lt2 g f H)). Qed.
Lemma lem343290 {A : Type'} (lt2 : type1402 A) (f : type184 A) (H : type700 A) : (term210 A lt2 f H) = (term206 A lt2 f H).
Proof. exact (fun_ext (fun g : A -> nat => @lem343289 A lt2 g f H)). Qed.
Lemma lem343291 {A : Type'} : (@ex (A -> nat)) = (@ex (A -> nat)).
Proof. exact (eq_refl (@ex (A -> nat))). Qed.
Lemma lem343292 {A : Type'} (lt2 : type1402 A) (f : type184 A) (H : type700 A) : (term211 A lt2 f H) = (term194 A lt2 f H).
Proof. exact (MK_COMB (@lem343291 A) (@lem343290 A lt2 f H)). Qed.
Lemma lem343293 {A : Type'} (lt2 : type1402 A) (f : type184 A) : (term212 A lt2 f) = (term196 A lt2 f).
Proof. exact (fun_ext (fun H : type700 A => @lem343292 A lt2 f H)). Qed.
Lemma lem343294 {A : Type'} : (@all ((A -> nat) -> A -> nat)) = (@all ((A -> nat) -> A -> nat)).
Proof. exact (eq_refl (@all ((A -> nat) -> A -> nat))). Qed.
Lemma lem343295 {A : Type'} (lt2 : type1402 A) (f : type184 A) : (term202 A lt2 f) = (term198 A lt2 f).
Proof. exact (MK_COMB (@lem343294 A) (@lem343293 A lt2 f)). Qed.
Lemma lem343296 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem343297 {A : Type'} (lt2 : type1402 A) (f : type184 A) : (term213 A lt2 f) = (term214 A lt2 f).
Proof. exact (MK_COMB (@lem343296) (@lem343295 A lt2 f)). Qed.
Lemma lem343298 {A : Type'} (lt2 : type1402 A) (f : type184 A) (H : type700 A) : (term205 A lt2 f H) = (term206 A lt2 f H).
Proof. exact (eq_refl (term205 A lt2 f H)). Qed.
Lemma lem343299 {A : Type'} (g : type184 A) (H : type700 A) : (g H) = (g H).
Proof. exact (eq_refl (g H)). Qed.
Lemma lem343300 {A : Type'} (lt2 : type1402 A) (f : type184 A) (g : type184 A) (H : type700 A) : (term215 A lt2 f g H) = (term216 A lt2 f g H).
Proof. exact (MK_COMB (@lem343298 A lt2 f H) (@lem343299 A g H)). Qed.
Lemma lem343301 {A : Type'} (lt2 : type1402 A) (g : type184 A) (f : type184 A) (H : type700 A) : (term216 A lt2 f g H) = (term217 A lt2 g f H).
Proof. exact (eq_refl (term216 A lt2 f g H)). Qed.
Lemma lem343302 {A : Type'} (lt2 : type1402 A) (g : type184 A) (f : type184 A) (H : type700 A) : (term215 A lt2 f g H) = (term217 A lt2 g f H).
Proof. exact (TRANS (@lem343300 A lt2 f g H) (@lem343301 A lt2 g f H)). Qed.
Lemma lem343303 {A : Type'} (lt2 : type1402 A) (g : type184 A) (f : type184 A) : (term218 A lt2 f g) = (term219 A lt2 g f).
Proof. exact (fun_ext (fun H : type700 A => @lem343302 A lt2 g f H)). Qed.
Lemma lem343304 {A : Type'} : (@all ((A -> nat) -> A -> nat)) = (@all ((A -> nat) -> A -> nat)).
Proof. exact (eq_refl (@all ((A -> nat) -> A -> nat))). Qed.
Lemma lem343305 {A : Type'} (lt2 : type1402 A) (g : type184 A) (f : type184 A) : (term220 A lt2 f g) = (term221 A lt2 g f).
Proof. exact (MK_COMB (@lem343304 A) (@lem343303 A lt2 g f)). Qed.
Lemma lem343306 {A : Type'} (lt2 : type1402 A) (f : type184 A) : (term222 A lt2 f) = (term223 A lt2 f).
Proof. exact (fun_ext (fun g : type184 A => @lem343305 A lt2 g f)). Qed.
Lemma lem343307 {A : Type'} : (@ex (((A -> nat) -> A -> nat) -> A -> nat)) = (@ex (((A -> nat) -> A -> nat) -> A -> nat)).
Proof. exact (eq_refl (@ex (((A -> nat) -> A -> nat) -> A -> nat))). Qed.
Lemma lem343308 {A : Type'} (lt2 : type1402 A) (f : type184 A) : (term203 A lt2 f) = (term224 A lt2 f).
Proof. exact (MK_COMB (@lem343307 A) (@lem343306 A lt2 f)). Qed.
Lemma lem343309 {A : Type'} (lt2 : type1402 A) (f : type184 A) : ((term202 A lt2 f) = (term203 A lt2 f)) = ((term198 A lt2 f) = (term224 A lt2 f)).
Proof. exact (MK_COMB (@lem343297 A lt2 f) (@lem343308 A lt2 f)). Qed.
Lemma lem343310 {A : Type'} (lt2 : type1402 A) (f : type184 A) : (term198 A lt2 f) = (term224 A lt2 f).
Proof. exact (EQ_MP (@lem343309 A lt2 f) (@lem343284 A lt2 f)). Qed.
Lemma lem343312 {A B : Type'} (P : type1413 A B) : (term177 A B P) = (term178 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem343313 {A : Type'} (P : type183 A) : (term225 A P) = (term226 A P).
Proof. exact (@lem343312 (type700 A) A P). Qed.
Lemma lem343314 {A : Type'} (lt2 : type1402 A) (g : type184 A) (f : type184 A) : (term227 A lt2 g f) = (term228 A lt2 g f).
Proof. exact (@lem343313 A (term229 A lt2 g f)). Qed.
Lemma lem343315 {A : Type'} (lt2 : type1402 A) (g : type184 A) (f : type184 A) (H : type700 A) : (term230 A lt2 g f H) = (term231 A lt2 g f H).
Proof. exact (eq_refl (term230 A lt2 g f H)). Qed.
Lemma lem343316 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem343317 {A : Type'} (lt2 : type1402 A) (g : type184 A) (f : type184 A) (H : type700 A) (x : A) : (term232 A lt2 g f H x) = (term233 A lt2 g f H x).
Proof. exact (MK_COMB (@lem343315 A lt2 g f H) (@lem343316 A x)). Qed.
Lemma lem343318 {A : Type'} (lt2 : type1402 A) (g : type184 A) (x : A) (f : type184 A) (H : type700 A) : (term233 A lt2 g f H x) = (term234 A lt2 g x f H).
Proof. exact (eq_refl (term233 A lt2 g f H x)). Qed.
Lemma lem343319 {A : Type'} (lt2 : type1402 A) (g : type184 A) (x : A) (f : type184 A) (H : type700 A) : (term232 A lt2 g f H x) = (term234 A lt2 g x f H).
Proof. exact (TRANS (@lem343317 A lt2 g f H x) (@lem343318 A lt2 g x f H)). Qed.
Lemma lem343320 {A : Type'} (lt2 : type1402 A) (g : type184 A) (f : type184 A) (H : type700 A) : (term235 A lt2 g f H) = (term231 A lt2 g f H).
Proof. exact (fun_ext (fun x : A => @lem343319 A lt2 g x f H)). Qed.
Lemma lem343321 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem343322 {A : Type'} (lt2 : type1402 A) (g : type184 A) (f : type184 A) (H : type700 A) : (term236 A lt2 g f H) = (term217 A lt2 g f H).
Proof. exact (MK_COMB (@lem343321 A) (@lem343320 A lt2 g f H)). Qed.
Lemma lem343323 {A : Type'} (lt2 : type1402 A) (g : type184 A) (f : type184 A) : (term237 A lt2 g f) = (term219 A lt2 g f).
Proof. exact (fun_ext (fun H : type700 A => @lem343322 A lt2 g f H)). Qed.
Lemma lem343324 {A : Type'} : (@all ((A -> nat) -> A -> nat)) = (@all ((A -> nat) -> A -> nat)).
Proof. exact (eq_refl (@all ((A -> nat) -> A -> nat))). Qed.
Lemma lem343325 {A : Type'} (lt2 : type1402 A) (g : type184 A) (f : type184 A) : (term227 A lt2 g f) = (term221 A lt2 g f).
Proof. exact (MK_COMB (@lem343324 A) (@lem343323 A lt2 g f)). Qed.
Lemma lem343326 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem343327 {A : Type'} (lt2 : type1402 A) (g : type184 A) (f : type184 A) : (term238 A lt2 g f) = (term239 A lt2 g f).
Proof. exact (MK_COMB (@lem343326) (@lem343325 A lt2 g f)). Qed.
Lemma lem343328 {A : Type'} (lt2 : type1402 A) (g : type184 A) (f : type184 A) (H : type700 A) : (term230 A lt2 g f H) = (term231 A lt2 g f H).
Proof. exact (eq_refl (term230 A lt2 g f H)). Qed.
Lemma lem343329 {A : Type'} (x : type185 A) (H : type700 A) : (x H) = (x H).
Proof. exact (eq_refl (x H)). Qed.
Lemma lem343330 {A : Type'} (lt2 : type1402 A) (g : type184 A) (f : type184 A) (x : type185 A) (H : type700 A) : (term240 A lt2 g f x H) = (term241 A lt2 g f x H).
Proof. exact (MK_COMB (@lem343328 A lt2 g f H) (@lem343329 A x H)). Qed.
Lemma lem343331 {A : Type'} (lt2 : type1402 A) (g : type184 A) (x : type185 A) (f : type184 A) (H : type700 A) : (term241 A lt2 g f x H) = (term242 A lt2 g x f H).
Proof. exact (eq_refl (term241 A lt2 g f x H)). Qed.
Lemma lem343332 {A : Type'} (lt2 : type1402 A) (g : type184 A) (x : type185 A) (f : type184 A) (H : type700 A) : (term240 A lt2 g f x H) = (term242 A lt2 g x f H).
Proof. exact (TRANS (@lem343330 A lt2 g f x H) (@lem343331 A lt2 g x f H)). Qed.
Lemma lem343333 {A : Type'} (lt2 : type1402 A) (g : type184 A) (x : type185 A) (f : type184 A) : (term243 A lt2 g f x) = (term244 A lt2 g x f).
Proof. exact (fun_ext (fun H : type700 A => @lem343332 A lt2 g x f H)). Qed.
Lemma lem343334 {A : Type'} : (@all ((A -> nat) -> A -> nat)) = (@all ((A -> nat) -> A -> nat)).
Proof. exact (eq_refl (@all ((A -> nat) -> A -> nat))). Qed.
Lemma lem343335 {A : Type'} (lt2 : type1402 A) (g : type184 A) (x : type185 A) (f : type184 A) : (term245 A lt2 g f x) = (term246 A lt2 g x f).
Proof. exact (MK_COMB (@lem343334 A) (@lem343333 A lt2 g x f)). Qed.
Lemma lem343336 {A : Type'} (lt2 : type1402 A) (g : type184 A) (f : type184 A) : (term247 A lt2 g f) = (term248 A lt2 g f).
Proof. exact (fun_ext (fun x : type185 A => @lem343335 A lt2 g x f)). Qed.
Lemma lem343337 {A : Type'} : (@ex (((A -> nat) -> A -> nat) -> A)) = (@ex (((A -> nat) -> A -> nat) -> A)).
Proof. exact (eq_refl (@ex (((A -> nat) -> A -> nat) -> A))). Qed.
Lemma lem343338 {A : Type'} (lt2 : type1402 A) (g : type184 A) (f : type184 A) : (term228 A lt2 g f) = (term249 A lt2 g f).
Proof. exact (MK_COMB (@lem343337 A) (@lem343336 A lt2 g f)). Qed.
Lemma lem343339 {A : Type'} (lt2 : type1402 A) (g : type184 A) (f : type184 A) : ((term227 A lt2 g f) = (term228 A lt2 g f)) = ((term221 A lt2 g f) = (term249 A lt2 g f)).
Proof. exact (MK_COMB (@lem343327 A lt2 g f) (@lem343338 A lt2 g f)). Qed.
Lemma lem343340 {A : Type'} (lt2 : type1402 A) (g : type184 A) (f : type184 A) : (term221 A lt2 g f) = (term249 A lt2 g f).
Proof. exact (EQ_MP (@lem343339 A lt2 g f) (@lem343314 A lt2 g f)). Qed.
Lemma lem343341 {A : Type'} (lt2 : type1402 A) (f : type184 A) : (term223 A lt2 f) = (term250 A lt2 f).
Proof. exact (fun_ext (fun g : type184 A => @lem343340 A lt2 g f)). Qed.
Lemma lem343342 {A : Type'} : (@ex (((A -> nat) -> A -> nat) -> A -> nat)) = (@ex (((A -> nat) -> A -> nat) -> A -> nat)).
Proof. exact (eq_refl (@ex (((A -> nat) -> A -> nat) -> A -> nat))). Qed.
Lemma lem343343 {A : Type'} (lt2 : type1402 A) (f : type184 A) : (term224 A lt2 f) = (term251 A lt2 f).
Proof. exact (MK_COMB (@lem343342 A) (@lem343341 A lt2 f)). Qed.
Lemma lem343344 {A : Type'} (lt2 : type1402 A) (f : type184 A) : (term198 A lt2 f) = (term251 A lt2 f).
Proof. exact (TRANS (@lem343310 A lt2 f) (@lem343343 A lt2 f)). Qed.
Lemma lem343345 {A : Type'} (lt2 : type1402 A) : (term200 A lt2) = (term252 A lt2).
Proof. exact (fun_ext (fun f : type184 A => @lem343344 A lt2 f)). Qed.
Lemma lem343346 {A : Type'} : (@ex (((A -> nat) -> A -> nat) -> A -> nat)) = (@ex (((A -> nat) -> A -> nat) -> A -> nat)).
Proof. exact (eq_refl (@ex (((A -> nat) -> A -> nat) -> A -> nat))). Qed.
Lemma lem343347 {A : Type'} (lt2 : type1402 A) : (term201 A lt2) = (term253 A lt2).
Proof. exact (MK_COMB (@lem343346 A) (@lem343345 A lt2)). Qed.
Lemma lem343348 {A : Type'} (lt2 : type1402 A) : (term176 A lt2) = (term253 A lt2).
Proof. exact (TRANS (@lem343280 A lt2) (@lem343347 A lt2)). Qed.
Lemma lem343350 {A : Type'} (lt2 : type1402 A) : (term114 A lt2) = (term253 A lt2).
Proof. exact (TRANS (@lem343250 A lt2) (@lem343348 A lt2)). Qed.
Lemma lem343351 {A : Type'} (lt2 : type1402 A) : (term15 A lt2) = (term253 A lt2).
Proof. exact (TRANS (@lem343003 A lt2) (@lem343350 A lt2)). Qed.
Lemma lem343352 {A : Type'} (lt2 : type1402 A) (h1 : term15 A lt2) : term253 A lt2.
Proof. exact (EQ_MP (@lem343351 A lt2) (@lem342789 A lt2 h1)). Qed.
Lemma lem343366 {A : Type'} (lt2 : type1402 A) (m : nat) (x : nat -> A) (n : nat) : (term52 A lt2 m x n) = (term52 A lt2 m x n).
Proof. exact (eq_refl (term52 A lt2 m x n)). Qed.
Lemma lem343367 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) : (term23 A lt2 x n) = (term23 A lt2 x n).
Proof. exact (fun_ext (fun m : nat => @lem343366 A lt2 m x n)). Qed.
Lemma lem343368 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem343369 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) : (term22 A lt2 x n) = (term22 A lt2 x n).
Proof. exact (MK_COMB (@lem343368) (@lem343367 A lt2 x n)). Qed.
Lemma lem343370 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : (term28 A lt2 x) = (term28 A lt2 x).
Proof. exact (fun_ext (fun n : nat => @lem343369 A lt2 x n)). Qed.
Lemma lem343371 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem343372 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : (term29 A lt2 x) = (term29 A lt2 x).
Proof. exact (MK_COMB (@lem343371) (@lem343370 A lt2 x)). Qed.
Lemma lem343383 {A B : Type'} (P : type1413 A B) : (term177 A B P) = (term178 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem343384 (P : type1605) : (term597 P) = (term598 P).
Proof. exact (@lem343383 nat nat P). Qed.
Lemma lem343385 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : (term599 A lt2 x) = (term600 A lt2 x).
Proof. exact (@lem343384 (term601 A lt2 x)). Qed.
Lemma lem343386 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) : (term602 A lt2 x n) = (term23 A lt2 x n).
Proof. exact (eq_refl (term602 A lt2 x n)). Qed.
Lemma lem343387 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem343388 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) (m : nat) : (term603 A lt2 x n m) = (term257 A lt2 x n m).
Proof. exact (MK_COMB (@lem343386 A lt2 x n) (@lem343387 m)). Qed.
Lemma lem343389 {A : Type'} (lt2 : type1402 A) (m : nat) (x : nat -> A) (n : nat) : (term257 A lt2 x n m) = (term52 A lt2 m x n).
Proof. exact (eq_refl (term257 A lt2 x n m)). Qed.
Lemma lem343390 {A : Type'} (lt2 : type1402 A) (m : nat) (x : nat -> A) (n : nat) : (term603 A lt2 x n m) = (term52 A lt2 m x n).
Proof. exact (TRANS (@lem343388 A lt2 x n m) (@lem343389 A lt2 m x n)). Qed.
Lemma lem343391 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) : (term604 A lt2 x n) = (term23 A lt2 x n).
Proof. exact (fun_ext (fun m : nat => @lem343390 A lt2 m x n)). Qed.
Lemma lem343392 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem343393 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) : (term605 A lt2 x n) = (term22 A lt2 x n).
Proof. exact (MK_COMB (@lem343392) (@lem343391 A lt2 x n)). Qed.
Lemma lem343394 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : (term606 A lt2 x) = (term28 A lt2 x).
Proof. exact (fun_ext (fun n : nat => @lem343393 A lt2 x n)). Qed.
Lemma lem343395 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem343396 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : (term599 A lt2 x) = (term29 A lt2 x).
Proof. exact (MK_COMB (@lem343395) (@lem343394 A lt2 x)). Qed.
Lemma lem343397 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem343398 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : (term607 A lt2 x) = (term608 A lt2 x).
Proof. exact (MK_COMB (@lem343397) (@lem343396 A lt2 x)). Qed.
Lemma lem343399 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (n : nat) : (term602 A lt2 x n) = (term23 A lt2 x n).
Proof. exact (eq_refl (term602 A lt2 x n)). Qed.
Lemma lem343400 (m : nat -> nat) (n : nat) : (m n) = (m n).
Proof. exact (eq_refl (m n)). Qed.
Lemma lem343401 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (m : nat -> nat) (n : nat) : (term609 A lt2 x m n) = (term610 A lt2 x m n).
Proof. exact (MK_COMB (@lem343399 A lt2 x n) (@lem343400 m n)). Qed.
Lemma lem343402 {A : Type'} (lt2 : type1402 A) (m : nat -> nat) (x : nat -> A) (n : nat) : (term610 A lt2 x m n) = (term611 A lt2 m x n).
Proof. exact (eq_refl (term610 A lt2 x m n)). Qed.
Lemma lem343403 {A : Type'} (lt2 : type1402 A) (m : nat -> nat) (x : nat -> A) (n : nat) : (term609 A lt2 x m n) = (term611 A lt2 m x n).
Proof. exact (TRANS (@lem343401 A lt2 x m n) (@lem343402 A lt2 m x n)). Qed.
Lemma lem343404 {A : Type'} (lt2 : type1402 A) (m : nat -> nat) (x : nat -> A) : (term612 A lt2 x m) = (term613 A lt2 m x).
Proof. exact (fun_ext (fun n : nat => @lem343403 A lt2 m x n)). Qed.
Lemma lem343405 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem343406 {A : Type'} (lt2 : type1402 A) (m : nat -> nat) (x : nat -> A) : (term614 A lt2 x m) = (term615 A lt2 m x).
Proof. exact (MK_COMB (@lem343405) (@lem343404 A lt2 m x)). Qed.
Lemma lem343407 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : (term616 A lt2 x) = (term617 A lt2 x).
Proof. exact (fun_ext (fun m : nat -> nat => @lem343406 A lt2 m x)). Qed.
Lemma lem343408 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem343409 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : (term600 A lt2 x) = (term618 A lt2 x).
Proof. exact (MK_COMB (@lem343408) (@lem343407 A lt2 x)). Qed.
Lemma lem343410 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : ((term599 A lt2 x) = (term600 A lt2 x)) = ((term29 A lt2 x) = (term618 A lt2 x)).
Proof. exact (MK_COMB (@lem343398 A lt2 x) (@lem343409 A lt2 x)). Qed.
Lemma lem343412 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : (term29 A lt2 x) = (term618 A lt2 x).
Proof. exact (EQ_MP (@lem343410 A lt2 x) (@lem343385 A lt2 x)). Qed.
Lemma lem343413 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : (term29 A lt2 x) = (term618 A lt2 x).
Proof. exact (TRANS (@lem343372 A lt2 x) (@lem343412 A lt2 x)). Qed.
Lemma lem343414 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (h1 : term29 A lt2 x) : term618 A lt2 x.
Proof. exact (EQ_MP (@lem343413 A lt2 x) (@lem342791 A lt2 x h1)). Qed.
Lemma lem343428 {A : Type'} (k : nat) (f : A -> nat) (x : nat -> A) (n : nat) : (term595 A k f x n) = (term595 A k f x n).
Proof. exact (eq_refl (term595 A k f x n)). Qed.
Lemma lem343429 {A : Type'} (f : A -> nat) (x : nat -> A) (n : nat) : (term460 A f x n) = (term460 A f x n).
Proof. exact (fun_ext (fun k : nat => @lem343428 A k f x n)). Qed.
Lemma lem343430 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem343431 {A : Type'} (f : A -> nat) (x : nat -> A) (n : nat) : (term459 A f x n) = (term459 A f x n).
Proof. exact (MK_COMB (@lem343430) (@lem343429 A f x n)). Qed.
Lemma lem343432 {A : Type'} (f : A -> nat) (x : nat -> A) : (term596 A f x) = (term596 A f x).
Proof. exact (fun_ext (fun n : nat => @lem343431 A f x n)). Qed.
Lemma lem343433 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem343434 {A : Type'} (f : A -> nat) (x : nat -> A) : (term450 A f x) = (term450 A f x).
Proof. exact (MK_COMB (@lem343433) (@lem343432 A f x)). Qed.
Lemma lem343445 {A B : Type'} (P : type1413 A B) : (term177 A B P) = (term178 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem343446 (P : type1605) : (term597 P) = (term598 P).
Proof. exact (@lem343445 nat nat P). Qed.
Lemma lem343447 {A : Type'} (f : A -> nat) (x : nat -> A) : (term619 A f x) = (term620 A f x).
Proof. exact (@lem343446 (term621 A f x)). Qed.
Lemma lem343448 {A : Type'} (f : A -> nat) (x : nat -> A) (n : nat) : (term622 A f x n) = (term460 A f x n).
Proof. exact (eq_refl (term622 A f x n)). Qed.
Lemma lem343449 (k : nat) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem343450 {A : Type'} (f : A -> nat) (x : nat -> A) (n : nat) (k : nat) : (term623 A f x n k) = (term624 A f x n k).
Proof. exact (MK_COMB (@lem343448 A f x n) (@lem343449 k)). Qed.
Lemma lem343451 {A : Type'} (k : nat) (f : A -> nat) (x : nat -> A) (n : nat) : (term624 A f x n k) = (term595 A k f x n).
Proof. exact (eq_refl (term624 A f x n k)). Qed.
Lemma lem343452 {A : Type'} (k : nat) (f : A -> nat) (x : nat -> A) (n : nat) : (term623 A f x n k) = (term595 A k f x n).
Proof. exact (TRANS (@lem343450 A f x n k) (@lem343451 A k f x n)). Qed.
Lemma lem343453 {A : Type'} (f : A -> nat) (x : nat -> A) (n : nat) : (term625 A f x n) = (term460 A f x n).
Proof. exact (fun_ext (fun k : nat => @lem343452 A k f x n)). Qed.
Lemma lem343454 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem343455 {A : Type'} (f : A -> nat) (x : nat -> A) (n : nat) : (term626 A f x n) = (term459 A f x n).
Proof. exact (MK_COMB (@lem343454) (@lem343453 A f x n)). Qed.
Lemma lem343456 {A : Type'} (f : A -> nat) (x : nat -> A) : (term627 A f x) = (term596 A f x).
Proof. exact (fun_ext (fun n : nat => @lem343455 A f x n)). Qed.
Lemma lem343457 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem343458 {A : Type'} (f : A -> nat) (x : nat -> A) : (term619 A f x) = (term450 A f x).
Proof. exact (MK_COMB (@lem343457) (@lem343456 A f x)). Qed.
Lemma lem343459 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem343460 {A : Type'} (f : A -> nat) (x : nat -> A) : (term628 A f x) = (term629 A f x).
Proof. exact (MK_COMB (@lem343459) (@lem343458 A f x)). Qed.
Lemma lem343461 {A : Type'} (f : A -> nat) (x : nat -> A) (n : nat) : (term622 A f x n) = (term460 A f x n).
Proof. exact (eq_refl (term622 A f x n)). Qed.
Lemma lem343462 (k : nat -> nat) (n : nat) : (k n) = (k n).
Proof. exact (eq_refl (k n)). Qed.
Lemma lem343463 {A : Type'} (f : A -> nat) (x : nat -> A) (k : nat -> nat) (n : nat) : (term630 A f x k n) = (term631 A f x k n).
Proof. exact (MK_COMB (@lem343461 A f x n) (@lem343462 k n)). Qed.
Lemma lem343464 {A : Type'} (k : nat -> nat) (f : A -> nat) (x : nat -> A) (n : nat) : (term631 A f x k n) = (term632 A k f x n).
Proof. exact (eq_refl (term631 A f x k n)). Qed.
Lemma lem343465 {A : Type'} (k : nat -> nat) (f : A -> nat) (x : nat -> A) (n : nat) : (term630 A f x k n) = (term632 A k f x n).
Proof. exact (TRANS (@lem343463 A f x k n) (@lem343464 A k f x n)). Qed.
Lemma lem343466 {A : Type'} (k : nat -> nat) (f : A -> nat) (x : nat -> A) : (term633 A f x k) = (term634 A k f x).
Proof. exact (fun_ext (fun n : nat => @lem343465 A k f x n)). Qed.
Lemma lem343467 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem343468 {A : Type'} (k : nat -> nat) (f : A -> nat) (x : nat -> A) : (term635 A f x k) = (term636 A k f x).
Proof. exact (MK_COMB (@lem343467) (@lem343466 A k f x)). Qed.
Lemma lem343469 {A : Type'} (f : A -> nat) (x : nat -> A) : (term637 A f x) = (term638 A f x).
Proof. exact (fun_ext (fun k : nat -> nat => @lem343468 A k f x)). Qed.
Lemma lem343470 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem343471 {A : Type'} (f : A -> nat) (x : nat -> A) : (term620 A f x) = (term639 A f x).
Proof. exact (MK_COMB (@lem343470) (@lem343469 A f x)). Qed.
Lemma lem343472 {A : Type'} (f : A -> nat) (x : nat -> A) : ((term619 A f x) = (term620 A f x)) = ((term450 A f x) = (term639 A f x)).
Proof. exact (MK_COMB (@lem343460 A f x) (@lem343471 A f x)). Qed.
Lemma lem343474 {A : Type'} (f : A -> nat) (x : nat -> A) : (term450 A f x) = (term639 A f x).
Proof. exact (EQ_MP (@lem343472 A f x) (@lem343447 A f x)). Qed.
Lemma lem343475 {A : Type'} (f : A -> nat) (x : nat -> A) : (term450 A f x) = (term639 A f x).
Proof. exact (TRANS (@lem343434 A f x) (@lem343474 A f x)). Qed.
Lemma lem343476 {A : Type'} (f : A -> nat) (x : nat -> A) (h1 : term450 A f x) : term639 A f x.
Proof. exact (EQ_MP (@lem343475 A f x) (@lem342793 A f x h1)). Qed.
Lemma lem343478 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) (i : nat) : (n = (term406 A f x i)) = (n = (term406 A f x i)).
Proof. exact (eq_refl (n = (term406 A f x i))). Qed.
Lemma lem343479 (P : nat -> Prop) : (term254 P) = (term255 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem343480 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term477 A n f x) = (term640 A n f x).
Proof. exact (@lem343479 (term594 A n f x)). Qed.
Lemma lem343481 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) (i : nat) : (term641 A n f x i) = (n = (term406 A f x i)).
Proof. exact (eq_refl (term641 A n f x i)). Qed.
Lemma lem343482 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem343484 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) (i : nat) : (term642 A n f x i) = (term643 A n f x i).
Proof. exact (MK_COMB (@lem343482) (@lem343481 A n f x i)). Qed.
Lemma lem343485 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term644 A n f x) = (term645 A n f x).
Proof. exact (fun_ext (fun i : nat => @lem343484 A n f x i)). Qed.
Lemma lem343486 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem343487 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term640 A n f x) = (term646 A n f x).
Proof. exact (MK_COMB (@lem343486) (@lem343485 A n f x)). Qed.
Lemma lem343488 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term477 A n f x) = (term646 A n f x).
Proof. exact (TRANS (@lem343480 A n f x) (@lem343487 A n f x)). Qed.
Lemma lem343489 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term594 A n f x) = (term594 A n f x).
Proof. exact (fun_ext (fun i : nat => @lem343478 A n f x i)). Qed.
Lemma lem343490 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem343491 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term467 A n f x) = (term467 A n f x).
Proof. exact (MK_COMB (@lem343490) (@lem343489 A n f x)). Qed.
Lemma lem343492 (P : nat -> Prop) : (term254 P) = (term255 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem343493 {A : Type'} (f : A -> nat) (x : nat -> A) : (term647 A f x) = (term648 A f x).
Proof. exact (@lem343492 (term1 A f x)). Qed.
Lemma lem343494 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term466 A f x n) = (term467 A n f x).
Proof. exact (eq_refl (term466 A f x n)). Qed.
Lemma lem343495 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem343496 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term476 A f x n) = (term477 A n f x).
Proof. exact (MK_COMB (@lem343495) (@lem343494 A n f x)). Qed.
Lemma lem343497 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term476 A f x n) = (term646 A n f x).
Proof. exact (TRANS (@lem343496 A n f x) (@lem343488 A n f x)). Qed.
Lemma lem343498 {A : Type'} (f : A -> nat) (x : nat -> A) : (term649 A f x) = (term650 A f x).
Proof. exact (fun_ext (fun n : nat => @lem343497 A n f x)). Qed.
Lemma lem343499 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem343500 {A : Type'} (f : A -> nat) (x : nat -> A) : (term648 A f x) = (term651 A f x).
Proof. exact (MK_COMB (@lem343499) (@lem343498 A f x)). Qed.
Lemma lem343501 {A : Type'} (f : A -> nat) (x : nat -> A) : (term647 A f x) = (term651 A f x).
Proof. exact (TRANS (@lem343493 A f x) (@lem343500 A f x)). Qed.
Lemma lem343502 {A : Type'} (f : A -> nat) (x : nat -> A) : (term1 A f x) = (term1 A f x).
Proof. exact (fun_ext (fun n : nat => @lem343491 A n f x)). Qed.
Lemma lem343503 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem343504 {A : Type'} (f : A -> nat) (x : nat -> A) : (term471 A f x) = (term471 A f x).
Proof. exact (MK_COMB (@lem343503) (@lem343502 A f x)). Qed.
Lemma lem343506 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) (i : nat) : (n = (term406 A f x i)) = (n = (term406 A f x i)).
Proof. exact (eq_refl (n = (term406 A f x i))). Qed.
Lemma lem343507 (P : nat -> Prop) : (term254 P) = (term255 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem343508 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term477 A n f x) = (term640 A n f x).
Proof. exact (@lem343507 (term594 A n f x)). Qed.
Lemma lem343509 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) (i : nat) : (term641 A n f x i) = (n = (term406 A f x i)).
Proof. exact (eq_refl (term641 A n f x i)). Qed.
Lemma lem343510 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem343512 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) (i : nat) : (term642 A n f x i) = (term643 A n f x i).
Proof. exact (MK_COMB (@lem343510) (@lem343509 A n f x i)). Qed.
Lemma lem343513 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term644 A n f x) = (term645 A n f x).
Proof. exact (fun_ext (fun i : nat => @lem343512 A n f x i)). Qed.
Lemma lem343514 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem343515 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term640 A n f x) = (term646 A n f x).
Proof. exact (MK_COMB (@lem343514) (@lem343513 A n f x)). Qed.
Lemma lem343516 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term477 A n f x) = (term646 A n f x).
Proof. exact (TRANS (@lem343508 A n f x) (@lem343515 A n f x)). Qed.
Lemma lem343517 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term594 A n f x) = (term594 A n f x).
Proof. exact (fun_ext (fun i : nat => @lem343506 A n f x i)). Qed.
Lemma lem343518 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem343519 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term467 A n f x) = (term467 A n f x).
Proof. exact (MK_COMB (@lem343518) (@lem343517 A n f x)). Qed.
Lemma lem343523 {A : Type'} (m : nat) (f : A -> nat) (x : nat -> A) (i : nat) : (m = (term406 A f x i)) = (m = (term406 A f x i)).
Proof. exact (eq_refl (m = (term406 A f x i))). Qed.
Lemma lem343524 (P : nat -> Prop) : (term254 P) = (term255 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem343525 {A : Type'} (m : nat) (f : A -> nat) (x : nat -> A) : (term477 A m f x) = (term640 A m f x).
Proof. exact (@lem343524 (term594 A m f x)). Qed.
Lemma lem343526 {A : Type'} (m : nat) (f : A -> nat) (x : nat -> A) (i : nat) : (term641 A m f x i) = (m = (term406 A f x i)).
Proof. exact (eq_refl (term641 A m f x i)). Qed.
Lemma lem343527 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem343529 {A : Type'} (m : nat) (f : A -> nat) (x : nat -> A) (i : nat) : (term642 A m f x i) = (term643 A m f x i).
Proof. exact (MK_COMB (@lem343527) (@lem343526 A m f x i)). Qed.
Lemma lem343530 {A : Type'} (m : nat) (f : A -> nat) (x : nat -> A) : (term644 A m f x) = (term645 A m f x).
Proof. exact (fun_ext (fun i : nat => @lem343529 A m f x i)). Qed.
Lemma lem343531 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem343532 {A : Type'} (m : nat) (f : A -> nat) (x : nat -> A) : (term640 A m f x) = (term646 A m f x).
Proof. exact (MK_COMB (@lem343531) (@lem343530 A m f x)). Qed.
Lemma lem343533 {A : Type'} (m : nat) (f : A -> nat) (x : nat -> A) : (term477 A m f x) = (term646 A m f x).
Proof. exact (TRANS (@lem343525 A m f x) (@lem343532 A m f x)). Qed.
Lemma lem343534 {A : Type'} (m : nat) (f : A -> nat) (x : nat -> A) : (term594 A m f x) = (term594 A m f x).
Proof. exact (fun_ext (fun i : nat => @lem343523 A m f x i)). Qed.
Lemma lem343535 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem343536 {A : Type'} (m : nat) (f : A -> nat) (x : nat -> A) : (term467 A m f x) = (term467 A m f x).
Proof. exact (MK_COMB (@lem343535) (@lem343534 A m f x)). Qed.
Lemma lem343537 {A : Type'} (m : nat) (f : A -> nat) (x : nat -> A) : (term652 A m f x) = (term467 A m f x).
Proof. exact (@lem16933 (term467 A m f x)). Qed.
Lemma lem343538 {A : Type'} (m : nat) (f : A -> nat) (x : nat -> A) : (term652 A m f x) = (term467 A m f x).
Proof. exact (TRANS (@lem343537 A m f x) (@lem343536 A m f x)). Qed.
Lemma lem343540 (m : nat) (n : nat) : (term653 m n) = (term653 m n).
Proof. exact (eq_refl (term653 m n)). Qed.
Lemma lem343541 {A : Type'} (n : nat) (m : nat) (f : A -> nat) (x : nat -> A) : (term654 A n m f x) = (term655 A n m f x).
Proof. exact (MK_COMB (@lem343540 m n) (@lem343538 A m f x)). Qed.
Lemma lem343542 {A : Type'} (n : nat) (m : nat) (f : A -> nat) (x : nat -> A) : (term656 A n m f x) = (term654 A n m f x).
Proof. exact (@lem17362 (Peano.lt m n) (term477 A m f x)). Qed.
Lemma lem343543 {A : Type'} (n : nat) (m : nat) (f : A -> nat) (x : nat -> A) : (term656 A n m f x) = (term655 A n m f x).
Proof. exact (TRANS (@lem343542 A n m f x) (@lem343541 A n m f x)). Qed.
Lemma lem343545 (m : nat) (n : nat) : (term657 m n) = (term657 m n).
Proof. exact (eq_refl (term657 m n)). Qed.
Lemma lem343546 {A : Type'} (n : nat) (m : nat) (f : A -> nat) (x : nat -> A) : (term658 A n m f x) = (term659 A n m f x).
Proof. exact (MK_COMB (@lem343545 m n) (@lem343533 A m f x)). Qed.
Lemma lem343547 {A : Type'} (n : nat) (m : nat) (f : A -> nat) (x : nat -> A) : (term480 A n m f x) = (term658 A n m f x).
Proof. exact (@lem17265 (Peano.lt m n) (term477 A m f x)). Qed.
Lemma lem343548 {A : Type'} (n : nat) (m : nat) (f : A -> nat) (x : nat -> A) : (term480 A n m f x) = (term659 A n m f x).
Proof. exact (TRANS (@lem343547 A n m f x) (@lem343546 A n m f x)). Qed.
Lemma lem343549 (P : nat -> Prop) : (term660 P) = (term661 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem343550 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term662 A n f x) = (term663 A n f x).
Proof. exact (@lem343549 (term482 A n f x)). Qed.
Lemma lem343551 {A : Type'} (n : nat) (m : nat) (f : A -> nat) (x : nat -> A) : (term664 A n f x m) = (term480 A n m f x).
Proof. exact (eq_refl (term664 A n f x m)). Qed.
Lemma lem343552 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem343553 {A : Type'} (n : nat) (m : nat) (f : A -> nat) (x : nat -> A) : (term665 A n f x m) = (term656 A n m f x).
Proof. exact (MK_COMB (@lem343552) (@lem343551 A n m f x)). Qed.
Lemma lem343554 {A : Type'} (n : nat) (m : nat) (f : A -> nat) (x : nat -> A) : (term665 A n f x m) = (term655 A n m f x).
Proof. exact (TRANS (@lem343553 A n m f x) (@lem343543 A n m f x)). Qed.
Lemma lem343555 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term666 A n f x) = (term667 A n f x).
Proof. exact (fun_ext (fun m : nat => @lem343554 A n m f x)). Qed.
Lemma lem343556 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem343557 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term663 A n f x) = (term668 A n f x).
Proof. exact (MK_COMB (@lem343556) (@lem343555 A n f x)). Qed.
Lemma lem343558 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term662 A n f x) = (term668 A n f x).
Proof. exact (TRANS (@lem343550 A n f x) (@lem343557 A n f x)). Qed.
Lemma lem343559 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term482 A n f x) = (term669 A n f x).
Proof. exact (fun_ext (fun m : nat => @lem343548 A n m f x)). Qed.
Lemma lem343560 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem343561 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term484 A n f x) = (term670 A n f x).
Proof. exact (MK_COMB (@lem343560) (@lem343559 A n f x)). Qed.
Lemma lem343562 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem343563 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term671 A n f x) = (term672 A n f x).
Proof. exact (MK_COMB (@lem343562) (@lem343516 A n f x)). Qed.
Lemma lem343564 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term673 A n f x) = (term674 A n f x).
Proof. exact (MK_COMB (@lem343563 A n f x) (@lem343558 A n f x)). Qed.
Lemma lem343565 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term675 A n f x) = (term673 A n f x).
Proof. exact (@lem17045 (term467 A n f x) (term484 A n f x)). Qed.
Lemma lem343566 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term675 A n f x) = (term674 A n f x).
Proof. exact (TRANS (@lem343565 A n f x) (@lem343564 A n f x)). Qed.
Lemma lem343567 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem343568 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term475 A n f x) = (term475 A n f x).
Proof. exact (MK_COMB (@lem343567) (@lem343519 A n f x)). Qed.
Lemma lem343569 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term486 A n f x) = (term676 A n f x).
Proof. exact (MK_COMB (@lem343568 A n f x) (@lem343561 A n f x)). Qed.
Lemma lem343570 (P : nat -> Prop) : (term254 P) = (term255 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem343571 {A : Type'} (f : A -> nat) (x : nat -> A) : (term677 A f x) = (term678 A f x).
Proof. exact (@lem343570 (term488 A f x)). Qed.
Lemma lem343572 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term679 A f x n) = (term486 A n f x).
Proof. exact (eq_refl (term679 A f x n)). Qed.
Lemma lem343573 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem343574 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term680 A f x n) = (term675 A n f x).
Proof. exact (MK_COMB (@lem343573) (@lem343572 A n f x)). Qed.
Lemma lem343575 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term680 A f x n) = (term674 A n f x).
Proof. exact (TRANS (@lem343574 A n f x) (@lem343566 A n f x)). Qed.
Lemma lem343576 {A : Type'} (f : A -> nat) (x : nat -> A) : (term681 A f x) = (term682 A f x).
Proof. exact (fun_ext (fun n : nat => @lem343575 A n f x)). Qed.
Lemma lem343577 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem343578 {A : Type'} (f : A -> nat) (x : nat -> A) : (term678 A f x) = (term683 A f x).
Proof. exact (MK_COMB (@lem343577) (@lem343576 A f x)). Qed.
Lemma lem343579 {A : Type'} (f : A -> nat) (x : nat -> A) : (term677 A f x) = (term683 A f x).
Proof. exact (TRANS (@lem343571 A f x) (@lem343578 A f x)). Qed.
Lemma lem343580 {A : Type'} (f : A -> nat) (x : nat -> A) : (term488 A f x) = (term684 A f x).
Proof. exact (fun_ext (fun n : nat => @lem343569 A n f x)). Qed.
Lemma lem343581 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem343582 {A : Type'} (f : A -> nat) (x : nat -> A) : (term489 A f x) = (term685 A f x).
Proof. exact (MK_COMB (@lem343581) (@lem343580 A f x)). Qed.
Lemma lem343583 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem343584 {A : Type'} (f : A -> nat) (x : nat -> A) : (term686 A f x) = (term687 A f x).
Proof. exact (MK_COMB (@lem343583) (@lem343501 A f x)). Qed.
Lemma lem343585 {A : Type'} (f : A -> nat) (x : nat -> A) : (term688 A f x) = (term689 A f x).
Proof. exact (MK_COMB (@lem343584 A f x) (@lem343579 A f x)). Qed.
Lemma lem343586 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem343587 {A : Type'} (f : A -> nat) (x : nat -> A) : (term690 A f x) = (term690 A f x).
Proof. exact (MK_COMB (@lem343586) (@lem343504 A f x)). Qed.
Lemma lem343588 {A : Type'} (f : A -> nat) (x : nat -> A) : (term691 A f x) = (term692 A f x).
Proof. exact (MK_COMB (@lem343587 A f x) (@lem343582 A f x)). Qed.
Lemma lem343589 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem343590 {A : Type'} (f : A -> nat) (x : nat -> A) : (term693 A f x) = (term694 A f x).
Proof. exact (MK_COMB (@lem343589) (@lem343588 A f x)). Qed.
Lemma lem343591 {A : Type'} (f : A -> nat) (x : nat -> A) : (term695 A f x) = (term696 A f x).
Proof. exact (MK_COMB (@lem343590 A f x) (@lem343585 A f x)). Qed.
Lemma lem343592 {A : Type'} (f : A -> nat) (x : nat -> A) : ((term471 A f x) = (term489 A f x)) = (term695 A f x).
Proof. exact (@lem17500 (term471 A f x) (term489 A f x)). Qed.
Lemma lem343593 {A : Type'} (f : A -> nat) (x : nat -> A) : ((term471 A f x) = (term489 A f x)) = (term696 A f x).
Proof. exact (TRANS (@lem343592 A f x) (@lem343591 A f x)). Qed.
Lemma lem343820 {A : Type'} (P : A -> Prop) (Q : Prop) : (term697 A P Q) = (term698 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem343821 (P : nat -> Prop) (Q : Prop) : (term699 P Q) = (term700 P Q).
Proof. exact (@lem343820 nat P Q). Qed.
Lemma lem343822 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term701 A n f x) = (term702 A n f x).
Proof. exact (@lem343821 (term594 A n f x) (term670 A n f x)). Qed.
Lemma lem343823 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) (i : nat) : (term641 A n f x i) = (n = (term406 A f x i)).
Proof. exact (eq_refl (term641 A n f x i)). Qed.
Lemma lem343824 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term703 A n f x) = (term594 A n f x).
Proof. exact (fun_ext (fun i : nat => @lem343823 A n f x i)). Qed.
Lemma lem343825 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem343826 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term704 A n f x) = (term467 A n f x).
Proof. exact (MK_COMB (@lem343825) (@lem343824 A n f x)). Qed.
Lemma lem343827 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem343828 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term705 A n f x) = (term475 A n f x).
Proof. exact (MK_COMB (@lem343827) (@lem343826 A n f x)). Qed.
Lemma lem343829 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term670 A n f x) = (term670 A n f x).
Proof. exact (eq_refl (term670 A n f x)). Qed.
Lemma lem343830 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term701 A n f x) = (term676 A n f x).
Proof. exact (MK_COMB (@lem343828 A n f x) (@lem343829 A n f x)). Qed.
Lemma lem343831 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem343832 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term706 A n f x) = (term707 A n f x).
Proof. exact (MK_COMB (@lem343831) (@lem343830 A n f x)). Qed.
Lemma lem343833 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) (i : nat) : (term641 A n f x i) = (n = (term406 A f x i)).
Proof. exact (eq_refl (term641 A n f x i)). Qed.
Lemma lem343834 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem343835 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) (i : nat) : (term708 A n f x i) = (term709 A n f x i).
Proof. exact (MK_COMB (@lem343834) (@lem343833 A n f x i)). Qed.
Lemma lem343836 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term670 A n f x) = (term670 A n f x).
Proof. exact (eq_refl (term670 A n f x)). Qed.
Lemma lem343837 {A : Type'} (i : nat) (n : nat) (f : A -> nat) (x : nat -> A) : (term710 A i n f x) = (term711 A i n f x).
Proof. exact (MK_COMB (@lem343835 A n f x i) (@lem343836 A n f x)). Qed.
Lemma lem343838 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term712 A n f x) = (term713 A n f x).
Proof. exact (fun_ext (fun i : nat => @lem343837 A i n f x)). Qed.
Lemma lem343839 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem343840 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term702 A n f x) = (term714 A n f x).
Proof. exact (MK_COMB (@lem343839) (@lem343838 A n f x)). Qed.
Lemma lem343841 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : ((term701 A n f x) = (term702 A n f x)) = ((term676 A n f x) = (term714 A n f x)).
Proof. exact (MK_COMB (@lem343832 A n f x) (@lem343840 A n f x)). Qed.
Lemma lem343842 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term676 A n f x) = (term714 A n f x).
Proof. exact (EQ_MP (@lem343841 A n f x) (@lem343822 A n f x)). Qed.
Lemma lem343843 {A : Type'} (f : A -> nat) (x : nat -> A) : (term684 A f x) = (term715 A f x).
Proof. exact (fun_ext (fun n : nat => @lem343842 A n f x)). Qed.
Lemma lem343844 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem343845 {A : Type'} (f : A -> nat) (x : nat -> A) : (term685 A f x) = (term716 A f x).
Proof. exact (MK_COMB (@lem343844) (@lem343843 A f x)). Qed.
Lemma lem343846 {A : Type'} (f : A -> nat) (x : nat -> A) : (term690 A f x) = (term690 A f x).
Proof. exact (eq_refl (term690 A f x)). Qed.
Lemma lem343847 {A : Type'} (f : A -> nat) (x : nat -> A) : (term692 A f x) = (term717 A f x).
Proof. exact (MK_COMB (@lem343846 A f x) (@lem343845 A f x)). Qed.
Lemma lem343849 {A : Type'} (P : A -> Prop) (Q : Prop) : (term697 A P Q) = (term698 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem343850 (P : nat -> Prop) (Q : Prop) : (term699 P Q) = (term700 P Q).
Proof. exact (@lem343849 nat P Q). Qed.
Lemma lem343851 {A : Type'} (f : A -> nat) (x : nat -> A) : (term718 A f x) = (term719 A f x).
Proof. exact (@lem343850 (term1 A f x) (term716 A f x)). Qed.
Lemma lem343852 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term466 A f x n) = (term467 A n f x).
Proof. exact (eq_refl (term466 A f x n)). Qed.
Lemma lem343853 {A : Type'} (f : A -> nat) (x : nat -> A) : (term468 A f x) = (term1 A f x).
Proof. exact (fun_ext (fun n : nat => @lem343852 A n f x)). Qed.
Lemma lem343854 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem343855 {A : Type'} (f : A -> nat) (x : nat -> A) : (term2 A f x) = (term471 A f x).
Proof. exact (MK_COMB (@lem343854) (@lem343853 A f x)). Qed.
Lemma lem343856 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem343857 {A : Type'} (f : A -> nat) (x : nat -> A) : (term720 A f x) = (term690 A f x).
Proof. exact (MK_COMB (@lem343856) (@lem343855 A f x)). Qed.
Lemma lem343858 {A : Type'} (f : A -> nat) (x : nat -> A) : (term716 A f x) = (term716 A f x).
Proof. exact (eq_refl (term716 A f x)). Qed.
Lemma lem343859 {A : Type'} (f : A -> nat) (x : nat -> A) : (term718 A f x) = (term717 A f x).
Proof. exact (MK_COMB (@lem343857 A f x) (@lem343858 A f x)). Qed.
Lemma lem343860 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem343861 {A : Type'} (f : A -> nat) (x : nat -> A) : (term721 A f x) = (term722 A f x).
Proof. exact (MK_COMB (@lem343860) (@lem343859 A f x)). Qed.
Lemma lem343862 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term466 A f x n) = (term467 A n f x).
Proof. exact (eq_refl (term466 A f x n)). Qed.
Lemma lem343863 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem343864 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term474 A f x n) = (term475 A n f x).
Proof. exact (MK_COMB (@lem343863) (@lem343862 A n f x)). Qed.
Lemma lem343865 {A : Type'} (f : A -> nat) (x : nat -> A) : (term716 A f x) = (term716 A f x).
Proof. exact (eq_refl (term716 A f x)). Qed.
Lemma lem343866 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term723 A n f x) = (term724 A n f x).
Proof. exact (MK_COMB (@lem343864 A n f x) (@lem343865 A f x)). Qed.
Lemma lem343867 {A : Type'} (f : A -> nat) (x : nat -> A) : (term725 A f x) = (term726 A f x).
Proof. exact (fun_ext (fun n : nat => @lem343866 A n f x)). Qed.
Lemma lem343868 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem343869 {A : Type'} (f : A -> nat) (x : nat -> A) : (term719 A f x) = (term727 A f x).
Proof. exact (MK_COMB (@lem343868) (@lem343867 A f x)). Qed.
Lemma lem343870 {A : Type'} (f : A -> nat) (x : nat -> A) : ((term718 A f x) = (term719 A f x)) = ((term717 A f x) = (term727 A f x)).
Proof. exact (MK_COMB (@lem343861 A f x) (@lem343869 A f x)). Qed.
Lemma lem343871 {A : Type'} (f : A -> nat) (x : nat -> A) : (term717 A f x) = (term727 A f x).
Proof. exact (EQ_MP (@lem343870 A f x) (@lem343851 A f x)). Qed.
Lemma lem343873 {A : Type'} (P : A -> Prop) (Q : Prop) : (term697 A P Q) = (term698 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem343874 (P : nat -> Prop) (Q : Prop) : (term699 P Q) = (term700 P Q).
Proof. exact (@lem343873 nat P Q). Qed.
Lemma lem343875 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term728 A n f x) = (term729 A n f x).
Proof. exact (@lem343874 (term594 A n f x) (term716 A f x)). Qed.
Lemma lem343876 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) (i : nat) : (term641 A n f x i) = (n = (term406 A f x i)).
Proof. exact (eq_refl (term641 A n f x i)). Qed.
Lemma lem343877 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term703 A n f x) = (term594 A n f x).
Proof. exact (fun_ext (fun i : nat => @lem343876 A n f x i)). Qed.
Lemma lem343878 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem343879 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term704 A n f x) = (term467 A n f x).
Proof. exact (MK_COMB (@lem343878) (@lem343877 A n f x)). Qed.
Lemma lem343880 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem343881 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term705 A n f x) = (term475 A n f x).
Proof. exact (MK_COMB (@lem343880) (@lem343879 A n f x)). Qed.
Lemma lem343882 {A : Type'} (f : A -> nat) (x : nat -> A) : (term716 A f x) = (term716 A f x).
Proof. exact (eq_refl (term716 A f x)). Qed.
Lemma lem343883 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term728 A n f x) = (term724 A n f x).
Proof. exact (MK_COMB (@lem343881 A n f x) (@lem343882 A f x)). Qed.
Lemma lem343884 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem343885 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term730 A n f x) = (term731 A n f x).
Proof. exact (MK_COMB (@lem343884) (@lem343883 A n f x)). Qed.
Lemma lem343886 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) (i : nat) : (term641 A n f x i) = (n = (term406 A f x i)).
Proof. exact (eq_refl (term641 A n f x i)). Qed.
Lemma lem343887 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem343888 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) (i : nat) : (term708 A n f x i) = (term709 A n f x i).
Proof. exact (MK_COMB (@lem343887) (@lem343886 A n f x i)). Qed.
Lemma lem343889 {A : Type'} (f : A -> nat) (x : nat -> A) : (term716 A f x) = (term716 A f x).
Proof. exact (eq_refl (term716 A f x)). Qed.
Lemma lem343890 {A : Type'} (n : nat) (i : nat) (f : A -> nat) (x : nat -> A) : (term732 A n i f x) = (term733 A n i f x).
Proof. exact (MK_COMB (@lem343888 A n f x i) (@lem343889 A f x)). Qed.
Lemma lem343891 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term734 A n f x) = (term735 A n f x).
Proof. exact (fun_ext (fun i : nat => @lem343890 A n i f x)). Qed.
Lemma lem343892 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem343893 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term729 A n f x) = (term736 A n f x).
Proof. exact (MK_COMB (@lem343892) (@lem343891 A n f x)). Qed.
Lemma lem343894 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : ((term728 A n f x) = (term729 A n f x)) = ((term724 A n f x) = (term736 A n f x)).
Proof. exact (MK_COMB (@lem343885 A n f x) (@lem343893 A n f x)). Qed.
Lemma lem343895 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term724 A n f x) = (term736 A n f x).
Proof. exact (EQ_MP (@lem343894 A n f x) (@lem343875 A n f x)). Qed.
Lemma lem343897 {A : Type'} (P : Prop) (Q : A -> Prop) : (term737 A P Q) = (term738 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem343898 (P : Prop) (Q : nat -> Prop) : (term739 P Q) = (term740 P Q).
Proof. exact (@lem343897 nat P Q). Qed.
Lemma lem343899 {A : Type'} (n : nat) (i : nat) (f : A -> nat) (x : nat -> A) : (term741 A n i f x) = (term742 A n i f x).
Proof. exact (@lem343898 (n = (term406 A f x i)) (term715 A f x)). Qed.
Lemma lem343900 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term743 A f x n) = (term714 A n f x).
Proof. exact (eq_refl (term743 A f x n)). Qed.
Lemma lem343901 {A : Type'} (f : A -> nat) (x : nat -> A) : (term744 A f x) = (term715 A f x).
Proof. exact (fun_ext (fun n : nat => @lem343900 A n f x)). Qed.
Lemma lem343902 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem343903 {A : Type'} (f : A -> nat) (x : nat -> A) : (term745 A f x) = (term716 A f x).
Proof. exact (MK_COMB (@lem343902) (@lem343901 A f x)). Qed.
Lemma lem343904 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) (i : nat) : (term709 A n f x i) = (term709 A n f x i).
Proof. exact (eq_refl (term709 A n f x i)). Qed.
Lemma lem343905 {A : Type'} (n : nat) (i : nat) (f : A -> nat) (x : nat -> A) : (term741 A n i f x) = (term733 A n i f x).
Proof. exact (MK_COMB (@lem343904 A n f x i) (@lem343903 A f x)). Qed.
Lemma lem343906 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem343907 {A : Type'} (n : nat) (i : nat) (f : A -> nat) (x : nat -> A) : (term746 A n i f x) = (term747 A n i f x).
Proof. exact (MK_COMB (@lem343906) (@lem343905 A n i f x)). Qed.
Lemma lem343908 {A : Type'} (n' : nat) (f : A -> nat) (x : nat -> A) : (term743 A f x n') = (term714 A n' f x).
Proof. exact (eq_refl (term743 A f x n')). Qed.
Lemma lem343909 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) (i : nat) : (term709 A n f x i) = (term709 A n f x i).
Proof. exact (eq_refl (term709 A n f x i)). Qed.
Lemma lem343910 {A : Type'} (n : nat) (i : nat) (n' : nat) (f : A -> nat) (x : nat -> A) : (term748 A n i f x n') = (term749 A n i n' f x).
Proof. exact (MK_COMB (@lem343909 A n f x i) (@lem343908 A n' f x)). Qed.
Lemma lem343911 {A : Type'} (n : nat) (i : nat) (f : A -> nat) (x : nat -> A) : (term750 A n i f x) = (term751 A n i f x).
Proof. exact (fun_ext (fun n' : nat => @lem343910 A n i n' f x)). Qed.
Lemma lem343912 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem343913 {A : Type'} (n : nat) (i : nat) (f : A -> nat) (x : nat -> A) : (term742 A n i f x) = (term752 A n i f x).
Proof. exact (MK_COMB (@lem343912) (@lem343911 A n i f x)). Qed.
Lemma lem343914 {A : Type'} (n : nat) (i : nat) (f : A -> nat) (x : nat -> A) : ((term741 A n i f x) = (term742 A n i f x)) = ((term733 A n i f x) = (term752 A n i f x)).
Proof. exact (MK_COMB (@lem343907 A n i f x) (@lem343913 A n i f x)). Qed.
Lemma lem343915 {A : Type'} (n : nat) (i : nat) (f : A -> nat) (x : nat -> A) : (term733 A n i f x) = (term752 A n i f x).
Proof. exact (EQ_MP (@lem343914 A n i f x) (@lem343899 A n i f x)). Qed.
Lemma lem343917 {A : Type'} (P : Prop) (Q : A -> Prop) : (term737 A P Q) = (term738 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem343918 (P : Prop) (Q : nat -> Prop) : (term739 P Q) = (term740 P Q).
Proof. exact (@lem343917 nat P Q). Qed.
Lemma lem343919 {A : Type'} (n : nat) (i : nat) (n' : nat) (f : A -> nat) (x : nat -> A) : (term753 A n i n' f x) = (term754 A n i n' f x).
Proof. exact (@lem343918 (n = (term406 A f x i)) (term713 A n' f x)). Qed.
Lemma lem343920 {A : Type'} (i : nat) (n' : nat) (f : A -> nat) (x : nat -> A) : (term755 A n' f x i) = (term711 A i n' f x).
Proof. exact (eq_refl (term755 A n' f x i)). Qed.
Lemma lem343921 {A : Type'} (n' : nat) (f : A -> nat) (x : nat -> A) : (term756 A n' f x) = (term713 A n' f x).
Proof. exact (fun_ext (fun i : nat => @lem343920 A i n' f x)). Qed.
Lemma lem343922 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem343923 {A : Type'} (n' : nat) (f : A -> nat) (x : nat -> A) : (term757 A n' f x) = (term714 A n' f x).
Proof. exact (MK_COMB (@lem343922) (@lem343921 A n' f x)). Qed.
Lemma lem343924 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) (i : nat) : (term709 A n f x i) = (term709 A n f x i).
Proof. exact (eq_refl (term709 A n f x i)). Qed.
Lemma lem343925 {A : Type'} (n : nat) (i : nat) (n' : nat) (f : A -> nat) (x : nat -> A) : (term753 A n i n' f x) = (term749 A n i n' f x).
Proof. exact (MK_COMB (@lem343924 A n f x i) (@lem343923 A n' f x)). Qed.
Lemma lem343926 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem343927 {A : Type'} (n : nat) (i : nat) (n' : nat) (f : A -> nat) (x : nat -> A) : (term758 A n i n' f x) = (term759 A n i n' f x).
Proof. exact (MK_COMB (@lem343926) (@lem343925 A n i n' f x)). Qed.
Lemma lem343928 {A : Type'} (i' : nat) (n' : nat) (f : A -> nat) (x : nat -> A) : (term755 A n' f x i') = (term711 A i' n' f x).
Proof. exact (eq_refl (term755 A n' f x i')). Qed.
Lemma lem343929 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) (i : nat) : (term709 A n f x i) = (term709 A n f x i).
Proof. exact (eq_refl (term709 A n f x i)). Qed.
Lemma lem343930 {A : Type'} (n : nat) (i : nat) (i' : nat) (n' : nat) (f : A -> nat) (x : nat -> A) : (term760 A n i n' f x i') = (term761 A n i i' n' f x).
Proof. exact (MK_COMB (@lem343929 A n f x i) (@lem343928 A i' n' f x)). Qed.
Lemma lem343931 {A : Type'} (n : nat) (i : nat) (n' : nat) (f : A -> nat) (x : nat -> A) : (term762 A n i n' f x) = (term763 A n i n' f x).
Proof. exact (fun_ext (fun i' : nat => @lem343930 A n i i' n' f x)). Qed.
Lemma lem343932 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem343933 {A : Type'} (n : nat) (i : nat) (n' : nat) (f : A -> nat) (x : nat -> A) : (term754 A n i n' f x) = (term764 A n i n' f x).
Proof. exact (MK_COMB (@lem343932) (@lem343931 A n i n' f x)). Qed.
Lemma lem343934 {A : Type'} (n : nat) (i : nat) (n' : nat) (f : A -> nat) (x : nat -> A) : ((term753 A n i n' f x) = (term754 A n i n' f x)) = ((term749 A n i n' f x) = (term764 A n i n' f x)).
Proof. exact (MK_COMB (@lem343927 A n i n' f x) (@lem343933 A n i n' f x)). Qed.
Lemma lem343935 {A : Type'} (n : nat) (i : nat) (n' : nat) (f : A -> nat) (x : nat -> A) : (term749 A n i n' f x) = (term764 A n i n' f x).
Proof. exact (EQ_MP (@lem343934 A n i n' f x) (@lem343919 A n i n' f x)). Qed.
Lemma lem343936 {A : Type'} (n : nat) (i : nat) (f : A -> nat) (x : nat -> A) : (term751 A n i f x) = (term765 A n i f x).
Proof. exact (fun_ext (fun n' : nat => @lem343935 A n i n' f x)). Qed.
Lemma lem343937 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem343938 {A : Type'} (n : nat) (i : nat) (f : A -> nat) (x : nat -> A) : (term752 A n i f x) = (term766 A n i f x).
Proof. exact (MK_COMB (@lem343937) (@lem343936 A n i f x)). Qed.
Lemma lem343939 {A : Type'} (n : nat) (i : nat) (f : A -> nat) (x : nat -> A) : (term733 A n i f x) = (term766 A n i f x).
Proof. exact (TRANS (@lem343915 A n i f x) (@lem343938 A n i f x)). Qed.
Lemma lem343940 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term735 A n f x) = (term767 A n f x).
Proof. exact (fun_ext (fun i : nat => @lem343939 A n i f x)). Qed.
Lemma lem343941 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem343942 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term736 A n f x) = (term768 A n f x).
Proof. exact (MK_COMB (@lem343941) (@lem343940 A n f x)). Qed.
Lemma lem343943 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term724 A n f x) = (term768 A n f x).
Proof. exact (TRANS (@lem343895 A n f x) (@lem343942 A n f x)). Qed.
Lemma lem343944 {A : Type'} (f : A -> nat) (x : nat -> A) : (term726 A f x) = (term769 A f x).
Proof. exact (fun_ext (fun n : nat => @lem343943 A n f x)). Qed.
Lemma lem343945 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem343946 {A : Type'} (f : A -> nat) (x : nat -> A) : (term727 A f x) = (term770 A f x).
Proof. exact (MK_COMB (@lem343945) (@lem343944 A f x)). Qed.
Lemma lem343947 {A : Type'} (f : A -> nat) (x : nat -> A) : (term717 A f x) = (term770 A f x).
Proof. exact (TRANS (@lem343871 A f x) (@lem343946 A f x)). Qed.
Lemma lem343948 {A : Type'} (f : A -> nat) (x : nat -> A) : (term692 A f x) = (term770 A f x).
Proof. exact (TRANS (@lem343847 A f x) (@lem343947 A f x)). Qed.
Lemma lem343949 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem343950 {A : Type'} (f : A -> nat) (x : nat -> A) : (term694 A f x) = (term771 A f x).
Proof. exact (MK_COMB (@lem343949) (@lem343948 A f x)). Qed.
Lemma lem343952 {A : Type'} (P : Prop) (Q : A -> Prop) : (term737 A P Q) = (term738 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem343953 (P : Prop) (Q : nat -> Prop) : (term739 P Q) = (term740 P Q).
Proof. exact (@lem343952 nat P Q). Qed.
Lemma lem343954 {A : Type'} (n : nat) (m : nat) (f : A -> nat) (x : nat -> A) : (term772 A n m f x) = (term773 A n m f x).
Proof. exact (@lem343953 (Peano.lt m n) (term594 A m f x)). Qed.
Lemma lem343955 {A : Type'} (m : nat) (f : A -> nat) (x : nat -> A) (i : nat) : (term641 A m f x i) = (m = (term406 A f x i)).
Proof. exact (eq_refl (term641 A m f x i)). Qed.
Lemma lem343956 {A : Type'} (m : nat) (f : A -> nat) (x : nat -> A) : (term703 A m f x) = (term594 A m f x).
Proof. exact (fun_ext (fun i : nat => @lem343955 A m f x i)). Qed.
Lemma lem343957 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem343958 {A : Type'} (m : nat) (f : A -> nat) (x : nat -> A) : (term704 A m f x) = (term467 A m f x).
Proof. exact (MK_COMB (@lem343957) (@lem343956 A m f x)). Qed.
Lemma lem343959 (m : nat) (n : nat) : (term653 m n) = (term653 m n).
Proof. exact (eq_refl (term653 m n)). Qed.
Lemma lem343960 {A : Type'} (n : nat) (m : nat) (f : A -> nat) (x : nat -> A) : (term772 A n m f x) = (term655 A n m f x).
Proof. exact (MK_COMB (@lem343959 m n) (@lem343958 A m f x)). Qed.
Lemma lem343961 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem343962 {A : Type'} (n : nat) (m : nat) (f : A -> nat) (x : nat -> A) : (term774 A n m f x) = (term775 A n m f x).
Proof. exact (MK_COMB (@lem343961) (@lem343960 A n m f x)). Qed.
Lemma lem343963 {A : Type'} (m : nat) (f : A -> nat) (x : nat -> A) (i : nat) : (term641 A m f x i) = (m = (term406 A f x i)).
Proof. exact (eq_refl (term641 A m f x i)). Qed.
Lemma lem343964 (m : nat) (n : nat) : (term653 m n) = (term653 m n).
Proof. exact (eq_refl (term653 m n)). Qed.
Lemma lem343965 {A : Type'} (n : nat) (m : nat) (f : A -> nat) (x : nat -> A) (i : nat) : (term776 A n m f x i) = (term777 A n m f x i).
Proof. exact (MK_COMB (@lem343964 m n) (@lem343963 A m f x i)). Qed.
Lemma lem343966 {A : Type'} (n : nat) (m : nat) (f : A -> nat) (x : nat -> A) : (term778 A n m f x) = (term779 A n m f x).
Proof. exact (fun_ext (fun i : nat => @lem343965 A n m f x i)). Qed.
Lemma lem343967 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem343968 {A : Type'} (n : nat) (m : nat) (f : A -> nat) (x : nat -> A) : (term773 A n m f x) = (term780 A n m f x).
Proof. exact (MK_COMB (@lem343967) (@lem343966 A n m f x)). Qed.
Lemma lem343969 {A : Type'} (n : nat) (m : nat) (f : A -> nat) (x : nat -> A) : ((term772 A n m f x) = (term773 A n m f x)) = ((term655 A n m f x) = (term780 A n m f x)).
Proof. exact (MK_COMB (@lem343962 A n m f x) (@lem343968 A n m f x)). Qed.
Lemma lem343970 {A : Type'} (n : nat) (m : nat) (f : A -> nat) (x : nat -> A) : (term655 A n m f x) = (term780 A n m f x).
Proof. exact (EQ_MP (@lem343969 A n m f x) (@lem343954 A n m f x)). Qed.
Lemma lem343971 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term667 A n f x) = (term781 A n f x).
Proof. exact (fun_ext (fun m : nat => @lem343970 A n m f x)). Qed.
Lemma lem343972 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem343973 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term668 A n f x) = (term782 A n f x).
Proof. exact (MK_COMB (@lem343972) (@lem343971 A n f x)). Qed.
Lemma lem343974 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term672 A n f x) = (term672 A n f x).
Proof. exact (eq_refl (term672 A n f x)). Qed.
Lemma lem343975 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term674 A n f x) = (term783 A n f x).
Proof. exact (MK_COMB (@lem343974 A n f x) (@lem343973 A n f x)). Qed.
Lemma lem343977 {A : Type'} (P : Prop) (Q : A -> Prop) : (term784 A P Q) = (term785 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem343978 (P : Prop) (Q : nat -> Prop) : (term786 P Q) = (term787 P Q).
Proof. exact (@lem343977 nat P Q). Qed.
Lemma lem343979 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term788 A n f x) = (term789 A n f x).
Proof. exact (@lem343978 (term646 A n f x) (term781 A n f x)). Qed.
Lemma lem343980 {A : Type'} (n : nat) (m : nat) (f : A -> nat) (x : nat -> A) : (term790 A n f x m) = (term780 A n m f x).
Proof. exact (eq_refl (term790 A n f x m)). Qed.
Lemma lem343981 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term791 A n f x) = (term781 A n f x).
Proof. exact (fun_ext (fun m : nat => @lem343980 A n m f x)). Qed.
Lemma lem343982 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem343983 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term792 A n f x) = (term782 A n f x).
Proof. exact (MK_COMB (@lem343982) (@lem343981 A n f x)). Qed.
Lemma lem343984 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term672 A n f x) = (term672 A n f x).
Proof. exact (eq_refl (term672 A n f x)). Qed.
Lemma lem343985 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term788 A n f x) = (term783 A n f x).
Proof. exact (MK_COMB (@lem343984 A n f x) (@lem343983 A n f x)). Qed.
Lemma lem343986 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem343987 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term793 A n f x) = (term794 A n f x).
Proof. exact (MK_COMB (@lem343986) (@lem343985 A n f x)). Qed.
Lemma lem343988 {A : Type'} (n : nat) (m : nat) (f : A -> nat) (x : nat -> A) : (term790 A n f x m) = (term780 A n m f x).
Proof. exact (eq_refl (term790 A n f x m)). Qed.
Lemma lem343989 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term672 A n f x) = (term672 A n f x).
Proof. exact (eq_refl (term672 A n f x)). Qed.
Lemma lem343990 {A : Type'} (n : nat) (m : nat) (f : A -> nat) (x : nat -> A) : (term795 A n f x m) = (term796 A n m f x).
Proof. exact (MK_COMB (@lem343989 A n f x) (@lem343988 A n m f x)). Qed.
Lemma lem343991 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term797 A n f x) = (term798 A n f x).
Proof. exact (fun_ext (fun m : nat => @lem343990 A n m f x)). Qed.
Lemma lem343992 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem343993 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term789 A n f x) = (term799 A n f x).
Proof. exact (MK_COMB (@lem343992) (@lem343991 A n f x)). Qed.
Lemma lem343994 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : ((term788 A n f x) = (term789 A n f x)) = ((term783 A n f x) = (term799 A n f x)).
Proof. exact (MK_COMB (@lem343987 A n f x) (@lem343993 A n f x)). Qed.
Lemma lem343995 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term783 A n f x) = (term799 A n f x).
Proof. exact (EQ_MP (@lem343994 A n f x) (@lem343979 A n f x)). Qed.
Lemma lem343997 {A : Type'} (P : Prop) (Q : A -> Prop) : (term784 A P Q) = (term785 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem343998 (P : Prop) (Q : nat -> Prop) : (term786 P Q) = (term787 P Q).
Proof. exact (@lem343997 nat P Q). Qed.
Lemma lem343999 {A : Type'} (n : nat) (m : nat) (f : A -> nat) (x : nat -> A) : (term800 A n m f x) = (term801 A n m f x).
Proof. exact (@lem343998 (term646 A n f x) (term779 A n m f x)). Qed.
Lemma lem344000 {A : Type'} (n : nat) (m : nat) (f : A -> nat) (x : nat -> A) (i : nat) : (term802 A n m f x i) = (term777 A n m f x i).
Proof. exact (eq_refl (term802 A n m f x i)). Qed.
Lemma lem344001 {A : Type'} (n : nat) (m : nat) (f : A -> nat) (x : nat -> A) : (term803 A n m f x) = (term779 A n m f x).
Proof. exact (fun_ext (fun i : nat => @lem344000 A n m f x i)). Qed.
Lemma lem344002 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem344003 {A : Type'} (n : nat) (m : nat) (f : A -> nat) (x : nat -> A) : (term804 A n m f x) = (term780 A n m f x).
Proof. exact (MK_COMB (@lem344002) (@lem344001 A n m f x)). Qed.
Lemma lem344004 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term672 A n f x) = (term672 A n f x).
Proof. exact (eq_refl (term672 A n f x)). Qed.
Lemma lem344005 {A : Type'} (n : nat) (m : nat) (f : A -> nat) (x : nat -> A) : (term800 A n m f x) = (term796 A n m f x).
Proof. exact (MK_COMB (@lem344004 A n f x) (@lem344003 A n m f x)). Qed.
Lemma lem344006 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem344007 {A : Type'} (n : nat) (m : nat) (f : A -> nat) (x : nat -> A) : (term805 A n m f x) = (term806 A n m f x).
Proof. exact (MK_COMB (@lem344006) (@lem344005 A n m f x)). Qed.
Lemma lem344008 {A : Type'} (n : nat) (m : nat) (f : A -> nat) (x : nat -> A) (i : nat) : (term802 A n m f x i) = (term777 A n m f x i).
Proof. exact (eq_refl (term802 A n m f x i)). Qed.
Lemma lem344009 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term672 A n f x) = (term672 A n f x).
Proof. exact (eq_refl (term672 A n f x)). Qed.
Lemma lem344010 {A : Type'} (n : nat) (m : nat) (f : A -> nat) (x : nat -> A) (i : nat) : (term807 A n m f x i) = (term808 A n m f x i).
Proof. exact (MK_COMB (@lem344009 A n f x) (@lem344008 A n m f x i)). Qed.
Lemma lem344011 {A : Type'} (n : nat) (m : nat) (f : A -> nat) (x : nat -> A) : (term809 A n m f x) = (term810 A n m f x).
Proof. exact (fun_ext (fun i : nat => @lem344010 A n m f x i)). Qed.
Lemma lem344012 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem344013 {A : Type'} (n : nat) (m : nat) (f : A -> nat) (x : nat -> A) : (term801 A n m f x) = (term811 A n m f x).
Proof. exact (MK_COMB (@lem344012) (@lem344011 A n m f x)). Qed.
Lemma lem344014 {A : Type'} (n : nat) (m : nat) (f : A -> nat) (x : nat -> A) : ((term800 A n m f x) = (term801 A n m f x)) = ((term796 A n m f x) = (term811 A n m f x)).
Proof. exact (MK_COMB (@lem344007 A n m f x) (@lem344013 A n m f x)). Qed.
Lemma lem344015 {A : Type'} (n : nat) (m : nat) (f : A -> nat) (x : nat -> A) : (term796 A n m f x) = (term811 A n m f x).
Proof. exact (EQ_MP (@lem344014 A n m f x) (@lem343999 A n m f x)). Qed.
Lemma lem344016 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term798 A n f x) = (term812 A n f x).
Proof. exact (fun_ext (fun m : nat => @lem344015 A n m f x)). Qed.
Lemma lem344017 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem344018 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term799 A n f x) = (term813 A n f x).
Proof. exact (MK_COMB (@lem344017) (@lem344016 A n f x)). Qed.
Lemma lem344019 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term783 A n f x) = (term813 A n f x).
Proof. exact (TRANS (@lem343995 A n f x) (@lem344018 A n f x)). Qed.
Lemma lem344020 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term674 A n f x) = (term813 A n f x).
Proof. exact (TRANS (@lem343975 A n f x) (@lem344019 A n f x)). Qed.
Lemma lem344021 {A : Type'} (f : A -> nat) (x : nat -> A) : (term682 A f x) = (term814 A f x).
Proof. exact (fun_ext (fun n : nat => @lem344020 A n f x)). Qed.
Lemma lem344022 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem344023 {A : Type'} (f : A -> nat) (x : nat -> A) : (term683 A f x) = (term815 A f x).
Proof. exact (MK_COMB (@lem344022) (@lem344021 A f x)). Qed.
Lemma lem344025 {A B : Type'} (P : type1413 A B) : (term177 A B P) = (term178 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem344026 (P : type1605) : (term597 P) = (term598 P).
Proof. exact (@lem344025 nat nat P). Qed.
Lemma lem344027 {A : Type'} (f : A -> nat) (x : nat -> A) : (term816 A f x) = (term817 A f x).
Proof. exact (@lem344026 (term818 A f x)). Qed.
Lemma lem344028 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term819 A f x n) = (term812 A n f x).
Proof. exact (eq_refl (term819 A f x n)). Qed.
Lemma lem344029 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem344030 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) (m : nat) : (term820 A f x n m) = (term821 A n f x m).
Proof. exact (MK_COMB (@lem344028 A n f x) (@lem344029 m)). Qed.
Lemma lem344031 {A : Type'} (n : nat) (m : nat) (f : A -> nat) (x : nat -> A) : (term821 A n f x m) = (term811 A n m f x).
Proof. exact (eq_refl (term821 A n f x m)). Qed.
Lemma lem344032 {A : Type'} (n : nat) (m : nat) (f : A -> nat) (x : nat -> A) : (term820 A f x n m) = (term811 A n m f x).
Proof. exact (TRANS (@lem344030 A n f x m) (@lem344031 A n m f x)). Qed.
Lemma lem344033 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term822 A f x n) = (term812 A n f x).
Proof. exact (fun_ext (fun m : nat => @lem344032 A n m f x)). Qed.
Lemma lem344034 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem344035 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term823 A f x n) = (term813 A n f x).
Proof. exact (MK_COMB (@lem344034) (@lem344033 A n f x)). Qed.
Lemma lem344036 {A : Type'} (f : A -> nat) (x : nat -> A) : (term824 A f x) = (term814 A f x).
Proof. exact (fun_ext (fun n : nat => @lem344035 A n f x)). Qed.
Lemma lem344037 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem344038 {A : Type'} (f : A -> nat) (x : nat -> A) : (term816 A f x) = (term815 A f x).
Proof. exact (MK_COMB (@lem344037) (@lem344036 A f x)). Qed.
Lemma lem344039 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem344040 {A : Type'} (f : A -> nat) (x : nat -> A) : (term825 A f x) = (term826 A f x).
Proof. exact (MK_COMB (@lem344039) (@lem344038 A f x)). Qed.
Lemma lem344041 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term819 A f x n) = (term812 A n f x).
Proof. exact (eq_refl (term819 A f x n)). Qed.
Lemma lem344042 (m : nat -> nat) (n : nat) : (m n) = (m n).
Proof. exact (eq_refl (m n)). Qed.
Lemma lem344043 {A : Type'} (f : A -> nat) (x : nat -> A) (m : nat -> nat) (n : nat) : (term827 A f x m n) = (term828 A f x m n).
Proof. exact (MK_COMB (@lem344041 A n f x) (@lem344042 m n)). Qed.
Lemma lem344044 {A : Type'} (m : nat -> nat) (n : nat) (f : A -> nat) (x : nat -> A) : (term828 A f x m n) = (term829 A m n f x).
Proof. exact (eq_refl (term828 A f x m n)). Qed.
Lemma lem344045 {A : Type'} (m : nat -> nat) (n : nat) (f : A -> nat) (x : nat -> A) : (term827 A f x m n) = (term829 A m n f x).
Proof. exact (TRANS (@lem344043 A f x m n) (@lem344044 A m n f x)). Qed.
Lemma lem344046 {A : Type'} (m : nat -> nat) (f : A -> nat) (x : nat -> A) : (term830 A f x m) = (term831 A m f x).
Proof. exact (fun_ext (fun n : nat => @lem344045 A m n f x)). Qed.
Lemma lem344047 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem344048 {A : Type'} (m : nat -> nat) (f : A -> nat) (x : nat -> A) : (term832 A f x m) = (term833 A m f x).
Proof. exact (MK_COMB (@lem344047) (@lem344046 A m f x)). Qed.
Lemma lem344049 {A : Type'} (f : A -> nat) (x : nat -> A) : (term834 A f x) = (term835 A f x).
Proof. exact (fun_ext (fun m : nat -> nat => @lem344048 A m f x)). Qed.
Lemma lem344050 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem344051 {A : Type'} (f : A -> nat) (x : nat -> A) : (term817 A f x) = (term836 A f x).
Proof. exact (MK_COMB (@lem344050) (@lem344049 A f x)). Qed.
Lemma lem344052 {A : Type'} (f : A -> nat) (x : nat -> A) : ((term816 A f x) = (term817 A f x)) = ((term815 A f x) = (term836 A f x)).
Proof. exact (MK_COMB (@lem344040 A f x) (@lem344051 A f x)). Qed.
Lemma lem344053 {A : Type'} (f : A -> nat) (x : nat -> A) : (term815 A f x) = (term836 A f x).
Proof. exact (EQ_MP (@lem344052 A f x) (@lem344027 A f x)). Qed.
Lemma lem344055 {A B : Type'} (P : type1413 A B) : (term177 A B P) = (term178 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem344056 (P : type1605) : (term597 P) = (term598 P).
Proof. exact (@lem344055 nat nat P). Qed.
Lemma lem344057 {A : Type'} (m : nat -> nat) (f : A -> nat) (x : nat -> A) : (term837 A m f x) = (term838 A m f x).
Proof. exact (@lem344056 (term839 A m f x)). Qed.
Lemma lem344058 {A : Type'} (m : nat -> nat) (n : nat) (f : A -> nat) (x : nat -> A) : (term840 A m f x n) = (term841 A m n f x).
Proof. exact (eq_refl (term840 A m f x n)). Qed.
Lemma lem344059 (i : nat) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem344060 {A : Type'} (m : nat -> nat) (n : nat) (f : A -> nat) (x : nat -> A) (i : nat) : (term842 A m f x n i) = (term843 A m n f x i).
Proof. exact (MK_COMB (@lem344058 A m n f x) (@lem344059 i)). Qed.
Lemma lem344061 {A : Type'} (m : nat -> nat) (n : nat) (f : A -> nat) (x : nat -> A) (i : nat) : (term843 A m n f x i) = (term844 A m n f x i).
Proof. exact (eq_refl (term843 A m n f x i)). Qed.
Lemma lem344062 {A : Type'} (m : nat -> nat) (n : nat) (f : A -> nat) (x : nat -> A) (i : nat) : (term842 A m f x n i) = (term844 A m n f x i).
Proof. exact (TRANS (@lem344060 A m n f x i) (@lem344061 A m n f x i)). Qed.
Lemma lem344063 {A : Type'} (m : nat -> nat) (n : nat) (f : A -> nat) (x : nat -> A) : (term845 A m f x n) = (term841 A m n f x).
Proof. exact (fun_ext (fun i : nat => @lem344062 A m n f x i)). Qed.
Lemma lem344064 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem344065 {A : Type'} (m : nat -> nat) (n : nat) (f : A -> nat) (x : nat -> A) : (term846 A m f x n) = (term829 A m n f x).
Proof. exact (MK_COMB (@lem344064) (@lem344063 A m n f x)). Qed.
Lemma lem344066 {A : Type'} (m : nat -> nat) (f : A -> nat) (x : nat -> A) : (term847 A m f x) = (term831 A m f x).
Proof. exact (fun_ext (fun n : nat => @lem344065 A m n f x)). Qed.
Lemma lem344067 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem344068 {A : Type'} (m : nat -> nat) (f : A -> nat) (x : nat -> A) : (term837 A m f x) = (term833 A m f x).
Proof. exact (MK_COMB (@lem344067) (@lem344066 A m f x)). Qed.
Lemma lem344069 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem344070 {A : Type'} (m : nat -> nat) (f : A -> nat) (x : nat -> A) : (term848 A m f x) = (term849 A m f x).
Proof. exact (MK_COMB (@lem344069) (@lem344068 A m f x)). Qed.
Lemma lem344071 {A : Type'} (m : nat -> nat) (n : nat) (f : A -> nat) (x : nat -> A) : (term840 A m f x n) = (term841 A m n f x).
Proof. exact (eq_refl (term840 A m f x n)). Qed.
Lemma lem344072 (i : nat -> nat) (n : nat) : (i n) = (i n).
Proof. exact (eq_refl (i n)). Qed.
Lemma lem344073 {A : Type'} (m : nat -> nat) (f : A -> nat) (x : nat -> A) (i : nat -> nat) (n : nat) : (term850 A m f x i n) = (term851 A m f x i n).
Proof. exact (MK_COMB (@lem344071 A m n f x) (@lem344072 i n)). Qed.
Lemma lem344074 {A : Type'} (m : nat -> nat) (f : A -> nat) (x : nat -> A) (i : nat -> nat) (n : nat) : (term851 A m f x i n) = (term852 A m f x i n).
Proof. exact (eq_refl (term851 A m f x i n)). Qed.
Lemma lem344075 {A : Type'} (m : nat -> nat) (f : A -> nat) (x : nat -> A) (i : nat -> nat) (n : nat) : (term850 A m f x i n) = (term852 A m f x i n).
Proof. exact (TRANS (@lem344073 A m f x i n) (@lem344074 A m f x i n)). Qed.
Lemma lem344076 {A : Type'} (m : nat -> nat) (f : A -> nat) (x : nat -> A) (i : nat -> nat) : (term853 A m f x i) = (term854 A m f x i).
Proof. exact (fun_ext (fun n : nat => @lem344075 A m f x i n)). Qed.
Lemma lem344077 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem344078 {A : Type'} (m : nat -> nat) (f : A -> nat) (x : nat -> A) (i : nat -> nat) : (term855 A m f x i) = (term856 A m f x i).
Proof. exact (MK_COMB (@lem344077) (@lem344076 A m f x i)). Qed.
Lemma lem344079 {A : Type'} (m : nat -> nat) (f : A -> nat) (x : nat -> A) : (term857 A m f x) = (term858 A m f x).
Proof. exact (fun_ext (fun i : nat -> nat => @lem344078 A m f x i)). Qed.
Lemma lem344080 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem344081 {A : Type'} (m : nat -> nat) (f : A -> nat) (x : nat -> A) : (term838 A m f x) = (term859 A m f x).
Proof. exact (MK_COMB (@lem344080) (@lem344079 A m f x)). Qed.
Lemma lem344082 {A : Type'} (m : nat -> nat) (f : A -> nat) (x : nat -> A) : ((term837 A m f x) = (term838 A m f x)) = ((term833 A m f x) = (term859 A m f x)).
Proof. exact (MK_COMB (@lem344070 A m f x) (@lem344081 A m f x)). Qed.
Lemma lem344083 {A : Type'} (m : nat -> nat) (f : A -> nat) (x : nat -> A) : (term833 A m f x) = (term859 A m f x).
Proof. exact (EQ_MP (@lem344082 A m f x) (@lem344057 A m f x)). Qed.
Lemma lem344084 {A : Type'} (f : A -> nat) (x : nat -> A) : (term835 A f x) = (term860 A f x).
Proof. exact (fun_ext (fun m : nat -> nat => @lem344083 A m f x)). Qed.
Lemma lem344085 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem344086 {A : Type'} (f : A -> nat) (x : nat -> A) : (term836 A f x) = (term861 A f x).
Proof. exact (MK_COMB (@lem344085) (@lem344084 A f x)). Qed.
Lemma lem344087 {A : Type'} (f : A -> nat) (x : nat -> A) : (term815 A f x) = (term861 A f x).
Proof. exact (TRANS (@lem344053 A f x) (@lem344086 A f x)). Qed.
Lemma lem344088 {A : Type'} (f : A -> nat) (x : nat -> A) : (term683 A f x) = (term861 A f x).
Proof. exact (TRANS (@lem344023 A f x) (@lem344087 A f x)). Qed.
Lemma lem344089 {A : Type'} (f : A -> nat) (x : nat -> A) : (term687 A f x) = (term687 A f x).
Proof. exact (eq_refl (term687 A f x)). Qed.
Lemma lem344090 {A : Type'} (f : A -> nat) (x : nat -> A) : (term689 A f x) = (term862 A f x).
Proof. exact (MK_COMB (@lem344089 A f x) (@lem344088 A f x)). Qed.
Lemma lem344092 {A : Type'} (P : Prop) (Q : A -> Prop) : (term737 A P Q) = (term738 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem344093 (P : Prop) (Q : type1002) : (term863 P Q) = (term864 P Q).
Proof. exact (@lem344092 (nat -> nat) P Q). Qed.
Lemma lem344094 {A : Type'} (f : A -> nat) (x : nat -> A) : (term865 A f x) = (term866 A f x).
Proof. exact (@lem344093 (term651 A f x) (term860 A f x)). Qed.
Lemma lem344095 {A : Type'} (m : nat -> nat) (f : A -> nat) (x : nat -> A) : (term867 A f x m) = (term859 A m f x).
Proof. exact (eq_refl (term867 A f x m)). Qed.
Lemma lem344096 {A : Type'} (f : A -> nat) (x : nat -> A) : (term868 A f x) = (term860 A f x).
Proof. exact (fun_ext (fun m : nat -> nat => @lem344095 A m f x)). Qed.
Lemma lem344097 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem344098 {A : Type'} (f : A -> nat) (x : nat -> A) : (term869 A f x) = (term861 A f x).
Proof. exact (MK_COMB (@lem344097) (@lem344096 A f x)). Qed.
Lemma lem344099 {A : Type'} (f : A -> nat) (x : nat -> A) : (term687 A f x) = (term687 A f x).
Proof. exact (eq_refl (term687 A f x)). Qed.
Lemma lem344100 {A : Type'} (f : A -> nat) (x : nat -> A) : (term865 A f x) = (term862 A f x).
Proof. exact (MK_COMB (@lem344099 A f x) (@lem344098 A f x)). Qed.
Lemma lem344101 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem344102 {A : Type'} (f : A -> nat) (x : nat -> A) : (term870 A f x) = (term871 A f x).
Proof. exact (MK_COMB (@lem344101) (@lem344100 A f x)). Qed.
Lemma lem344103 {A : Type'} (m : nat -> nat) (f : A -> nat) (x : nat -> A) : (term867 A f x m) = (term859 A m f x).
Proof. exact (eq_refl (term867 A f x m)). Qed.
Lemma lem344104 {A : Type'} (f : A -> nat) (x : nat -> A) : (term687 A f x) = (term687 A f x).
Proof. exact (eq_refl (term687 A f x)). Qed.
Lemma lem344105 {A : Type'} (m : nat -> nat) (f : A -> nat) (x : nat -> A) : (term872 A f x m) = (term873 A m f x).
Proof. exact (MK_COMB (@lem344104 A f x) (@lem344103 A m f x)). Qed.
Lemma lem344106 {A : Type'} (f : A -> nat) (x : nat -> A) : (term874 A f x) = (term875 A f x).
Proof. exact (fun_ext (fun m : nat -> nat => @lem344105 A m f x)). Qed.
Lemma lem344107 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem344108 {A : Type'} (f : A -> nat) (x : nat -> A) : (term866 A f x) = (term876 A f x).
Proof. exact (MK_COMB (@lem344107) (@lem344106 A f x)). Qed.
Lemma lem344109 {A : Type'} (f : A -> nat) (x : nat -> A) : ((term865 A f x) = (term866 A f x)) = ((term862 A f x) = (term876 A f x)).
Proof. exact (MK_COMB (@lem344102 A f x) (@lem344108 A f x)). Qed.
Lemma lem344110 {A : Type'} (f : A -> nat) (x : nat -> A) : (term862 A f x) = (term876 A f x).
Proof. exact (EQ_MP (@lem344109 A f x) (@lem344094 A f x)). Qed.
Lemma lem344112 {A : Type'} (P : Prop) (Q : A -> Prop) : (term737 A P Q) = (term738 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem344113 (P : Prop) (Q : type1002) : (term863 P Q) = (term864 P Q).
Proof. exact (@lem344112 (nat -> nat) P Q). Qed.
Lemma lem344114 {A : Type'} (m : nat -> nat) (f : A -> nat) (x : nat -> A) : (term877 A m f x) = (term878 A m f x).
Proof. exact (@lem344113 (term651 A f x) (term858 A m f x)). Qed.
Lemma lem344115 {A : Type'} (m : nat -> nat) (f : A -> nat) (x : nat -> A) (i : nat -> nat) : (term879 A m f x i) = (term856 A m f x i).
Proof. exact (eq_refl (term879 A m f x i)). Qed.
Lemma lem344116 {A : Type'} (m : nat -> nat) (f : A -> nat) (x : nat -> A) : (term880 A m f x) = (term858 A m f x).
Proof. exact (fun_ext (fun i : nat -> nat => @lem344115 A m f x i)). Qed.
Lemma lem344117 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem344118 {A : Type'} (m : nat -> nat) (f : A -> nat) (x : nat -> A) : (term881 A m f x) = (term859 A m f x).
Proof. exact (MK_COMB (@lem344117) (@lem344116 A m f x)). Qed.
Lemma lem344119 {A : Type'} (f : A -> nat) (x : nat -> A) : (term687 A f x) = (term687 A f x).
Proof. exact (eq_refl (term687 A f x)). Qed.
Lemma lem344120 {A : Type'} (m : nat -> nat) (f : A -> nat) (x : nat -> A) : (term877 A m f x) = (term873 A m f x).
Proof. exact (MK_COMB (@lem344119 A f x) (@lem344118 A m f x)). Qed.
Lemma lem344121 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem344122 {A : Type'} (m : nat -> nat) (f : A -> nat) (x : nat -> A) : (term882 A m f x) = (term883 A m f x).
Proof. exact (MK_COMB (@lem344121) (@lem344120 A m f x)). Qed.
Lemma lem344123 {A : Type'} (m : nat -> nat) (f : A -> nat) (x : nat -> A) (i : nat -> nat) : (term879 A m f x i) = (term856 A m f x i).
Proof. exact (eq_refl (term879 A m f x i)). Qed.
Lemma lem344124 {A : Type'} (f : A -> nat) (x : nat -> A) : (term687 A f x) = (term687 A f x).
Proof. exact (eq_refl (term687 A f x)). Qed.
Lemma lem344125 {A : Type'} (m : nat -> nat) (f : A -> nat) (x : nat -> A) (i : nat -> nat) : (term884 A m f x i) = (term885 A m f x i).
Proof. exact (MK_COMB (@lem344124 A f x) (@lem344123 A m f x i)). Qed.
Lemma lem344126 {A : Type'} (m : nat -> nat) (f : A -> nat) (x : nat -> A) : (term886 A m f x) = (term887 A m f x).
Proof. exact (fun_ext (fun i : nat -> nat => @lem344125 A m f x i)). Qed.
Lemma lem344127 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem344128 {A : Type'} (m : nat -> nat) (f : A -> nat) (x : nat -> A) : (term878 A m f x) = (term888 A m f x).
Proof. exact (MK_COMB (@lem344127) (@lem344126 A m f x)). Qed.
Lemma lem344129 {A : Type'} (m : nat -> nat) (f : A -> nat) (x : nat -> A) : ((term877 A m f x) = (term878 A m f x)) = ((term873 A m f x) = (term888 A m f x)).
Proof. exact (MK_COMB (@lem344122 A m f x) (@lem344128 A m f x)). Qed.
Lemma lem344130 {A : Type'} (m : nat -> nat) (f : A -> nat) (x : nat -> A) : (term873 A m f x) = (term888 A m f x).
Proof. exact (EQ_MP (@lem344129 A m f x) (@lem344114 A m f x)). Qed.
Lemma lem344131 {A : Type'} (f : A -> nat) (x : nat -> A) : (term875 A f x) = (term889 A f x).
Proof. exact (fun_ext (fun m : nat -> nat => @lem344130 A m f x)). Qed.
Lemma lem344132 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem344133 {A : Type'} (f : A -> nat) (x : nat -> A) : (term876 A f x) = (term890 A f x).
Proof. exact (MK_COMB (@lem344132) (@lem344131 A f x)). Qed.
Lemma lem344134 {A : Type'} (f : A -> nat) (x : nat -> A) : (term862 A f x) = (term890 A f x).
Proof. exact (TRANS (@lem344110 A f x) (@lem344133 A f x)). Qed.
Lemma lem344135 {A : Type'} (f : A -> nat) (x : nat -> A) : (term689 A f x) = (term890 A f x).
Proof. exact (TRANS (@lem344090 A f x) (@lem344134 A f x)). Qed.
Lemma lem344136 {A : Type'} (f : A -> nat) (x : nat -> A) : (term696 A f x) = (term891 A f x).
Proof. exact (MK_COMB (@lem343950 A f x) (@lem344135 A f x)). Qed.
Lemma lem344140 {A : Type'} (P : A -> Prop) (Q : Prop) : (term137 A P Q) = (term138 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem344141 (P : nat -> Prop) (Q : Prop) : (term892 P Q) = (term893 P Q).
Proof. exact (@lem344140 nat P Q). Qed.
Lemma lem344142 {A : Type'} (f : A -> nat) (x : nat -> A) : (term894 A f x) = (term895 A f x).
Proof. exact (@lem344141 (term769 A f x) (term890 A f x)). Qed.
Lemma lem344143 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term896 A f x n) = (term768 A n f x).
Proof. exact (eq_refl (term896 A f x n)). Qed.
Lemma lem344144 {A : Type'} (f : A -> nat) (x : nat -> A) : (term897 A f x) = (term769 A f x).
Proof. exact (fun_ext (fun n : nat => @lem344143 A n f x)). Qed.
Lemma lem344145 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem344146 {A : Type'} (f : A -> nat) (x : nat -> A) : (term898 A f x) = (term770 A f x).
Proof. exact (MK_COMB (@lem344145) (@lem344144 A f x)). Qed.
Lemma lem344147 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem344148 {A : Type'} (f : A -> nat) (x : nat -> A) : (term899 A f x) = (term771 A f x).
Proof. exact (MK_COMB (@lem344147) (@lem344146 A f x)). Qed.
Lemma lem344149 {A : Type'} (f : A -> nat) (x : nat -> A) : (term890 A f x) = (term890 A f x).
Proof. exact (eq_refl (term890 A f x)). Qed.
Lemma lem344150 {A : Type'} (f : A -> nat) (x : nat -> A) : (term894 A f x) = (term891 A f x).
Proof. exact (MK_COMB (@lem344148 A f x) (@lem344149 A f x)). Qed.
Lemma lem344151 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem344152 {A : Type'} (f : A -> nat) (x : nat -> A) : (term900 A f x) = (term901 A f x).
Proof. exact (MK_COMB (@lem344151) (@lem344150 A f x)). Qed.
Lemma lem344153 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term896 A f x n) = (term768 A n f x).
Proof. exact (eq_refl (term896 A f x n)). Qed.
Lemma lem344154 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem344155 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term902 A f x n) = (term903 A n f x).
Proof. exact (MK_COMB (@lem344154) (@lem344153 A n f x)). Qed.
Lemma lem344156 {A : Type'} (f : A -> nat) (x : nat -> A) : (term890 A f x) = (term890 A f x).
Proof. exact (eq_refl (term890 A f x)). Qed.
Lemma lem344157 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term904 A n f x) = (term905 A n f x).
Proof. exact (MK_COMB (@lem344155 A n f x) (@lem344156 A f x)). Qed.
Lemma lem344158 {A : Type'} (f : A -> nat) (x : nat -> A) : (term906 A f x) = (term907 A f x).
Proof. exact (fun_ext (fun n : nat => @lem344157 A n f x)). Qed.
Lemma lem344159 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem344160 {A : Type'} (f : A -> nat) (x : nat -> A) : (term895 A f x) = (term908 A f x).
Proof. exact (MK_COMB (@lem344159) (@lem344158 A f x)). Qed.
Lemma lem344161 {A : Type'} (f : A -> nat) (x : nat -> A) : ((term894 A f x) = (term895 A f x)) = ((term891 A f x) = (term908 A f x)).
Proof. exact (MK_COMB (@lem344152 A f x) (@lem344160 A f x)). Qed.
Lemma lem344162 {A : Type'} (f : A -> nat) (x : nat -> A) : (term891 A f x) = (term908 A f x).
Proof. exact (EQ_MP (@lem344161 A f x) (@lem344142 A f x)). Qed.
Lemma lem344166 {A : Type'} (P : A -> Prop) (Q : Prop) : (term137 A P Q) = (term138 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem344167 (P : nat -> Prop) (Q : Prop) : (term892 P Q) = (term893 P Q).
Proof. exact (@lem344166 nat P Q). Qed.
Lemma lem344168 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term909 A n f x) = (term910 A n f x).
Proof. exact (@lem344167 (term767 A n f x) (term890 A f x)). Qed.
Lemma lem344169 {A : Type'} (n : nat) (i : nat) (f : A -> nat) (x : nat -> A) : (term911 A n f x i) = (term766 A n i f x).
Proof. exact (eq_refl (term911 A n f x i)). Qed.
Lemma lem344170 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term912 A n f x) = (term767 A n f x).
Proof. exact (fun_ext (fun i : nat => @lem344169 A n i f x)). Qed.
Lemma lem344171 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem344172 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term913 A n f x) = (term768 A n f x).
Proof. exact (MK_COMB (@lem344171) (@lem344170 A n f x)). Qed.
Lemma lem344173 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem344174 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term914 A n f x) = (term903 A n f x).
Proof. exact (MK_COMB (@lem344173) (@lem344172 A n f x)). Qed.
Lemma lem344175 {A : Type'} (f : A -> nat) (x : nat -> A) : (term890 A f x) = (term890 A f x).
Proof. exact (eq_refl (term890 A f x)). Qed.
Lemma lem344176 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term909 A n f x) = (term905 A n f x).
Proof. exact (MK_COMB (@lem344174 A n f x) (@lem344175 A f x)). Qed.
Lemma lem344177 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem344178 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term915 A n f x) = (term916 A n f x).
Proof. exact (MK_COMB (@lem344177) (@lem344176 A n f x)). Qed.
Lemma lem344179 {A : Type'} (n : nat) (i : nat) (f : A -> nat) (x : nat -> A) : (term911 A n f x i) = (term766 A n i f x).
Proof. exact (eq_refl (term911 A n f x i)). Qed.
Lemma lem344180 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem344181 {A : Type'} (n : nat) (i : nat) (f : A -> nat) (x : nat -> A) : (term917 A n f x i) = (term918 A n i f x).
Proof. exact (MK_COMB (@lem344180) (@lem344179 A n i f x)). Qed.
Lemma lem344182 {A : Type'} (f : A -> nat) (x : nat -> A) : (term890 A f x) = (term890 A f x).
Proof. exact (eq_refl (term890 A f x)). Qed.
Lemma lem344183 {A : Type'} (n : nat) (i : nat) (f : A -> nat) (x : nat -> A) : (term919 A n i f x) = (term920 A n i f x).
Proof. exact (MK_COMB (@lem344181 A n i f x) (@lem344182 A f x)). Qed.
Lemma lem344184 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term921 A n f x) = (term922 A n f x).
Proof. exact (fun_ext (fun i : nat => @lem344183 A n i f x)). Qed.
Lemma lem344185 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem344186 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term910 A n f x) = (term923 A n f x).
Proof. exact (MK_COMB (@lem344185) (@lem344184 A n f x)). Qed.
Lemma lem344187 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : ((term909 A n f x) = (term910 A n f x)) = ((term905 A n f x) = (term923 A n f x)).
Proof. exact (MK_COMB (@lem344178 A n f x) (@lem344186 A n f x)). Qed.
Lemma lem344188 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term905 A n f x) = (term923 A n f x).
Proof. exact (EQ_MP (@lem344187 A n f x) (@lem344168 A n f x)). Qed.
Lemma lem344192 {A : Type'} (P : A -> Prop) (Q : Prop) : (term137 A P Q) = (term138 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem344193 (P : nat -> Prop) (Q : Prop) : (term892 P Q) = (term893 P Q).
Proof. exact (@lem344192 nat P Q). Qed.
Lemma lem344194 {A : Type'} (n : nat) (i : nat) (f : A -> nat) (x : nat -> A) : (term924 A n i f x) = (term925 A n i f x).
Proof. exact (@lem344193 (term765 A n i f x) (term890 A f x)). Qed.
Lemma lem344195 {A : Type'} (n : nat) (i : nat) (n' : nat) (f : A -> nat) (x : nat -> A) : (term926 A n i f x n') = (term764 A n i n' f x).
Proof. exact (eq_refl (term926 A n i f x n')). Qed.
Lemma lem344196 {A : Type'} (n : nat) (i : nat) (f : A -> nat) (x : nat -> A) : (term927 A n i f x) = (term765 A n i f x).
Proof. exact (fun_ext (fun n' : nat => @lem344195 A n i n' f x)). Qed.
Lemma lem344197 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem344198 {A : Type'} (n : nat) (i : nat) (f : A -> nat) (x : nat -> A) : (term928 A n i f x) = (term766 A n i f x).
Proof. exact (MK_COMB (@lem344197) (@lem344196 A n i f x)). Qed.
Lemma lem344199 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem344200 {A : Type'} (n : nat) (i : nat) (f : A -> nat) (x : nat -> A) : (term929 A n i f x) = (term918 A n i f x).
Proof. exact (MK_COMB (@lem344199) (@lem344198 A n i f x)). Qed.
Lemma lem344201 {A : Type'} (f : A -> nat) (x : nat -> A) : (term890 A f x) = (term890 A f x).
Proof. exact (eq_refl (term890 A f x)). Qed.
Lemma lem344202 {A : Type'} (n : nat) (i : nat) (f : A -> nat) (x : nat -> A) : (term924 A n i f x) = (term920 A n i f x).
Proof. exact (MK_COMB (@lem344200 A n i f x) (@lem344201 A f x)). Qed.
Lemma lem344203 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem344204 {A : Type'} (n : nat) (i : nat) (f : A -> nat) (x : nat -> A) : (term930 A n i f x) = (term931 A n i f x).
Proof. exact (MK_COMB (@lem344203) (@lem344202 A n i f x)). Qed.
Lemma lem344205 {A : Type'} (n : nat) (i : nat) (n' : nat) (f : A -> nat) (x : nat -> A) : (term926 A n i f x n') = (term764 A n i n' f x).
Proof. exact (eq_refl (term926 A n i f x n')). Qed.
Lemma lem344206 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem344207 {A : Type'} (n : nat) (i : nat) (n' : nat) (f : A -> nat) (x : nat -> A) : (term932 A n i f x n') = (term933 A n i n' f x).
Proof. exact (MK_COMB (@lem344206) (@lem344205 A n i n' f x)). Qed.
Lemma lem344208 {A : Type'} (f : A -> nat) (x : nat -> A) : (term890 A f x) = (term890 A f x).
Proof. exact (eq_refl (term890 A f x)). Qed.
Lemma lem344209 {A : Type'} (n : nat) (i : nat) (n' : nat) (f : A -> nat) (x : nat -> A) : (term934 A n i n' f x) = (term935 A n i n' f x).
Proof. exact (MK_COMB (@lem344207 A n i n' f x) (@lem344208 A f x)). Qed.
Lemma lem344210 {A : Type'} (n : nat) (i : nat) (f : A -> nat) (x : nat -> A) : (term936 A n i f x) = (term937 A n i f x).
Proof. exact (fun_ext (fun n' : nat => @lem344209 A n i n' f x)). Qed.
Lemma lem344211 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem344212 {A : Type'} (n : nat) (i : nat) (f : A -> nat) (x : nat -> A) : (term925 A n i f x) = (term938 A n i f x).
Proof. exact (MK_COMB (@lem344211) (@lem344210 A n i f x)). Qed.
Lemma lem344213 {A : Type'} (n : nat) (i : nat) (f : A -> nat) (x : nat -> A) : ((term924 A n i f x) = (term925 A n i f x)) = ((term920 A n i f x) = (term938 A n i f x)).
Proof. exact (MK_COMB (@lem344204 A n i f x) (@lem344212 A n i f x)). Qed.
Lemma lem344214 {A : Type'} (n : nat) (i : nat) (f : A -> nat) (x : nat -> A) : (term920 A n i f x) = (term938 A n i f x).
Proof. exact (EQ_MP (@lem344213 A n i f x) (@lem344194 A n i f x)). Qed.
Lemma lem344218 {A : Type'} (P : A -> Prop) (Q : Prop) : (term137 A P Q) = (term138 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem344219 (P : nat -> Prop) (Q : Prop) : (term892 P Q) = (term893 P Q).
Proof. exact (@lem344218 nat P Q). Qed.
Lemma lem344220 {A : Type'} (n : nat) (i : nat) (n' : nat) (f : A -> nat) (x : nat -> A) : (term939 A n i n' f x) = (term940 A n i n' f x).
Proof. exact (@lem344219 (term763 A n i n' f x) (term890 A f x)). Qed.
Lemma lem344221 {A : Type'} (n : nat) (i : nat) (i' : nat) (n' : nat) (f : A -> nat) (x : nat -> A) : (term941 A n i n' f x i') = (term761 A n i i' n' f x).
Proof. exact (eq_refl (term941 A n i n' f x i')). Qed.
Lemma lem344222 {A : Type'} (n : nat) (i : nat) (n' : nat) (f : A -> nat) (x : nat -> A) : (term942 A n i n' f x) = (term763 A n i n' f x).
Proof. exact (fun_ext (fun i' : nat => @lem344221 A n i i' n' f x)). Qed.
Lemma lem344223 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem344224 {A : Type'} (n : nat) (i : nat) (n' : nat) (f : A -> nat) (x : nat -> A) : (term943 A n i n' f x) = (term764 A n i n' f x).
Proof. exact (MK_COMB (@lem344223) (@lem344222 A n i n' f x)). Qed.
Lemma lem344225 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem344226 {A : Type'} (n : nat) (i : nat) (n' : nat) (f : A -> nat) (x : nat -> A) : (term944 A n i n' f x) = (term933 A n i n' f x).
Proof. exact (MK_COMB (@lem344225) (@lem344224 A n i n' f x)). Qed.
Lemma lem344227 {A : Type'} (f : A -> nat) (x : nat -> A) : (term890 A f x) = (term890 A f x).
Proof. exact (eq_refl (term890 A f x)). Qed.
Lemma lem344228 {A : Type'} (n : nat) (i : nat) (n' : nat) (f : A -> nat) (x : nat -> A) : (term939 A n i n' f x) = (term935 A n i n' f x).
Proof. exact (MK_COMB (@lem344226 A n i n' f x) (@lem344227 A f x)). Qed.
Lemma lem344229 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem344230 {A : Type'} (n : nat) (i : nat) (n' : nat) (f : A -> nat) (x : nat -> A) : (term945 A n i n' f x) = (term946 A n i n' f x).
Proof. exact (MK_COMB (@lem344229) (@lem344228 A n i n' f x)). Qed.
Lemma lem344231 {A : Type'} (n : nat) (i : nat) (i' : nat) (n' : nat) (f : A -> nat) (x : nat -> A) : (term941 A n i n' f x i') = (term761 A n i i' n' f x).
Proof. exact (eq_refl (term941 A n i n' f x i')). Qed.
Lemma lem344232 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem344233 {A : Type'} (n : nat) (i : nat) (i' : nat) (n' : nat) (f : A -> nat) (x : nat -> A) : (term947 A n i n' f x i') = (term948 A n i i' n' f x).
Proof. exact (MK_COMB (@lem344232) (@lem344231 A n i i' n' f x)). Qed.
Lemma lem344234 {A : Type'} (f : A -> nat) (x : nat -> A) : (term890 A f x) = (term890 A f x).
Proof. exact (eq_refl (term890 A f x)). Qed.
Lemma lem344235 {A : Type'} (n : nat) (i : nat) (i' : nat) (n' : nat) (f : A -> nat) (x : nat -> A) : (term949 A n i n' i' f x) = (term950 A n i i' n' f x).
Proof. exact (MK_COMB (@lem344233 A n i i' n' f x) (@lem344234 A f x)). Qed.
Lemma lem344236 {A : Type'} (n : nat) (i : nat) (n' : nat) (f : A -> nat) (x : nat -> A) : (term951 A n i n' f x) = (term952 A n i n' f x).
Proof. exact (fun_ext (fun i' : nat => @lem344235 A n i i' n' f x)). Qed.
Lemma lem344237 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem344238 {A : Type'} (n : nat) (i : nat) (n' : nat) (f : A -> nat) (x : nat -> A) : (term940 A n i n' f x) = (term953 A n i n' f x).
Proof. exact (MK_COMB (@lem344237) (@lem344236 A n i n' f x)). Qed.
Lemma lem344239 {A : Type'} (n : nat) (i : nat) (n' : nat) (f : A -> nat) (x : nat -> A) : ((term939 A n i n' f x) = (term940 A n i n' f x)) = ((term935 A n i n' f x) = (term953 A n i n' f x)).
Proof. exact (MK_COMB (@lem344230 A n i n' f x) (@lem344238 A n i n' f x)). Qed.
Lemma lem344240 {A : Type'} (n : nat) (i : nat) (n' : nat) (f : A -> nat) (x : nat -> A) : (term935 A n i n' f x) = (term953 A n i n' f x).
Proof. exact (EQ_MP (@lem344239 A n i n' f x) (@lem344220 A n i n' f x)). Qed.
Lemma lem344242 {A : Type'} (P : Prop) (Q : A -> Prop) : (term784 A P Q) = (term785 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem344243 (P : Prop) (Q : type1002) : (term954 P Q) = (term955 P Q).
Proof. exact (@lem344242 (nat -> nat) P Q). Qed.
Lemma lem344244 {A : Type'} (n : nat) (i : nat) (i' : nat) (n' : nat) (f : A -> nat) (x : nat -> A) : (term956 A n i i' n' f x) = (term957 A n i i' n' f x).
Proof. exact (@lem344243 (term761 A n i i' n' f x) (term889 A f x)). Qed.
Lemma lem344245 {A : Type'} (m : nat -> nat) (f : A -> nat) (x : nat -> A) : (term958 A f x m) = (term888 A m f x).
Proof. exact (eq_refl (term958 A f x m)). Qed.
Lemma lem344246 {A : Type'} (f : A -> nat) (x : nat -> A) : (term959 A f x) = (term889 A f x).
Proof. exact (fun_ext (fun m : nat -> nat => @lem344245 A m f x)). Qed.
Lemma lem344247 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem344248 {A : Type'} (f : A -> nat) (x : nat -> A) : (term960 A f x) = (term890 A f x).
Proof. exact (MK_COMB (@lem344247) (@lem344246 A f x)). Qed.
Lemma lem344249 {A : Type'} (n : nat) (i : nat) (i' : nat) (n' : nat) (f : A -> nat) (x : nat -> A) : (term948 A n i i' n' f x) = (term948 A n i i' n' f x).
Proof. exact (eq_refl (term948 A n i i' n' f x)). Qed.
Lemma lem344250 {A : Type'} (n : nat) (i : nat) (i' : nat) (n' : nat) (f : A -> nat) (x : nat -> A) : (term956 A n i i' n' f x) = (term950 A n i i' n' f x).
Proof. exact (MK_COMB (@lem344249 A n i i' n' f x) (@lem344248 A f x)). Qed.
Lemma lem344251 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem344252 {A : Type'} (n : nat) (i : nat) (i' : nat) (n' : nat) (f : A -> nat) (x : nat -> A) : (term961 A n i i' n' f x) = (term962 A n i i' n' f x).
Proof. exact (MK_COMB (@lem344251) (@lem344250 A n i i' n' f x)). Qed.
Lemma lem344253 {A : Type'} (m : nat -> nat) (f : A -> nat) (x : nat -> A) : (term958 A f x m) = (term888 A m f x).
Proof. exact (eq_refl (term958 A f x m)). Qed.
Lemma lem344254 {A : Type'} (n : nat) (i : nat) (i' : nat) (n' : nat) (f : A -> nat) (x : nat -> A) : (term948 A n i i' n' f x) = (term948 A n i i' n' f x).
Proof. exact (eq_refl (term948 A n i i' n' f x)). Qed.
Lemma lem344255 {A : Type'} (n : nat) (i : nat) (i' : nat) (n' : nat) (m : nat -> nat) (f : A -> nat) (x : nat -> A) : (term963 A n i i' n' f x m) = (term964 A n i i' n' m f x).
Proof. exact (MK_COMB (@lem344254 A n i i' n' f x) (@lem344253 A m f x)). Qed.
Lemma lem344256 {A : Type'} (n : nat) (i : nat) (i' : nat) (n' : nat) (f : A -> nat) (x : nat -> A) : (term965 A n i i' n' f x) = (term966 A n i i' n' f x).
Proof. exact (fun_ext (fun m : nat -> nat => @lem344255 A n i i' n' m f x)). Qed.
Lemma lem344257 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem344258 {A : Type'} (n : nat) (i : nat) (i' : nat) (n' : nat) (f : A -> nat) (x : nat -> A) : (term957 A n i i' n' f x) = (term967 A n i i' n' f x).
Proof. exact (MK_COMB (@lem344257) (@lem344256 A n i i' n' f x)). Qed.
Lemma lem344259 {A : Type'} (n : nat) (i : nat) (i' : nat) (n' : nat) (f : A -> nat) (x : nat -> A) : ((term956 A n i i' n' f x) = (term957 A n i i' n' f x)) = ((term950 A n i i' n' f x) = (term967 A n i i' n' f x)).
Proof. exact (MK_COMB (@lem344252 A n i i' n' f x) (@lem344258 A n i i' n' f x)). Qed.
Lemma lem344260 {A : Type'} (n : nat) (i : nat) (i' : nat) (n' : nat) (f : A -> nat) (x : nat -> A) : (term950 A n i i' n' f x) = (term967 A n i i' n' f x).
Proof. exact (EQ_MP (@lem344259 A n i i' n' f x) (@lem344244 A n i i' n' f x)). Qed.
Lemma lem344262 {A : Type'} (P : Prop) (Q : A -> Prop) : (term784 A P Q) = (term785 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem344263 (P : Prop) (Q : type1002) : (term954 P Q) = (term955 P Q).
Proof. exact (@lem344262 (nat -> nat) P Q). Qed.
Lemma lem344264 {A : Type'} (n : nat) (i : nat) (i' : nat) (n' : nat) (m : nat -> nat) (f : A -> nat) (x : nat -> A) : (term968 A n i i' n' m f x) = (term969 A n i i' n' m f x).
Proof. exact (@lem344263 (term761 A n i i' n' f x) (term887 A m f x)). Qed.
Lemma lem344265 {A : Type'} (m : nat -> nat) (f : A -> nat) (x : nat -> A) (i : nat -> nat) : (term970 A m f x i) = (term885 A m f x i).
Proof. exact (eq_refl (term970 A m f x i)). Qed.
Lemma lem344266 {A : Type'} (m : nat -> nat) (f : A -> nat) (x : nat -> A) : (term971 A m f x) = (term887 A m f x).
Proof. exact (fun_ext (fun i : nat -> nat => @lem344265 A m f x i)). Qed.
Lemma lem344267 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem344268 {A : Type'} (m : nat -> nat) (f : A -> nat) (x : nat -> A) : (term972 A m f x) = (term888 A m f x).
Proof. exact (MK_COMB (@lem344267) (@lem344266 A m f x)). Qed.
Lemma lem344269 {A : Type'} (n : nat) (i : nat) (i' : nat) (n' : nat) (f : A -> nat) (x : nat -> A) : (term948 A n i i' n' f x) = (term948 A n i i' n' f x).
Proof. exact (eq_refl (term948 A n i i' n' f x)). Qed.
Lemma lem344270 {A : Type'} (n : nat) (i : nat) (i' : nat) (n' : nat) (m : nat -> nat) (f : A -> nat) (x : nat -> A) : (term968 A n i i' n' m f x) = (term964 A n i i' n' m f x).
Proof. exact (MK_COMB (@lem344269 A n i i' n' f x) (@lem344268 A m f x)). Qed.
Lemma lem344271 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem344272 {A : Type'} (n : nat) (i : nat) (i' : nat) (n' : nat) (m : nat -> nat) (f : A -> nat) (x : nat -> A) : (term973 A n i i' n' m f x) = (term974 A n i i' n' m f x).
Proof. exact (MK_COMB (@lem344271) (@lem344270 A n i i' n' m f x)). Qed.
Lemma lem344273 {A : Type'} (m : nat -> nat) (f : A -> nat) (x : nat -> A) (i : nat -> nat) : (term970 A m f x i) = (term885 A m f x i).
Proof. exact (eq_refl (term970 A m f x i)). Qed.
Lemma lem344274 {A : Type'} (n : nat) (i : nat) (i' : nat) (n' : nat) (f : A -> nat) (x : nat -> A) : (term948 A n i i' n' f x) = (term948 A n i i' n' f x).
Proof. exact (eq_refl (term948 A n i i' n' f x)). Qed.
Lemma lem344275 {A : Type'} (n : nat) (i : nat) (i' : nat) (n' : nat) (m : nat -> nat) (f : A -> nat) (x : nat -> A) (i'' : nat -> nat) : (term975 A n i i' n' m f x i'') = (term976 A n i i' n' m f x i'').
Proof. exact (MK_COMB (@lem344274 A n i i' n' f x) (@lem344273 A m f x i'')). Qed.
Lemma lem344276 {A : Type'} (n : nat) (i : nat) (i' : nat) (n' : nat) (m : nat -> nat) (f : A -> nat) (x : nat -> A) : (term977 A n i i' n' m f x) = (term978 A n i i' n' m f x).
Proof. exact (fun_ext (fun i'' : nat -> nat => @lem344275 A n i i' n' m f x i'')). Qed.
Lemma lem344277 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem344278 {A : Type'} (n : nat) (i : nat) (i' : nat) (n' : nat) (m : nat -> nat) (f : A -> nat) (x : nat -> A) : (term969 A n i i' n' m f x) = (term979 A n i i' n' m f x).
Proof. exact (MK_COMB (@lem344277) (@lem344276 A n i i' n' m f x)). Qed.
Lemma lem344279 {A : Type'} (n : nat) (i : nat) (i' : nat) (n' : nat) (m : nat -> nat) (f : A -> nat) (x : nat -> A) : ((term968 A n i i' n' m f x) = (term969 A n i i' n' m f x)) = ((term964 A n i i' n' m f x) = (term979 A n i i' n' m f x)).
Proof. exact (MK_COMB (@lem344272 A n i i' n' m f x) (@lem344278 A n i i' n' m f x)). Qed.
Lemma lem344280 {A : Type'} (n : nat) (i : nat) (i' : nat) (n' : nat) (m : nat -> nat) (f : A -> nat) (x : nat -> A) : (term964 A n i i' n' m f x) = (term979 A n i i' n' m f x).
Proof. exact (EQ_MP (@lem344279 A n i i' n' m f x) (@lem344264 A n i i' n' m f x)). Qed.
Lemma lem344281 {A : Type'} (n : nat) (i : nat) (i' : nat) (n' : nat) (f : A -> nat) (x : nat -> A) : (term966 A n i i' n' f x) = (term980 A n i i' n' f x).
Proof. exact (fun_ext (fun m : nat -> nat => @lem344280 A n i i' n' m f x)). Qed.
Lemma lem344282 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem344283 {A : Type'} (n : nat) (i : nat) (i' : nat) (n' : nat) (f : A -> nat) (x : nat -> A) : (term967 A n i i' n' f x) = (term981 A n i i' n' f x).
Proof. exact (MK_COMB (@lem344282) (@lem344281 A n i i' n' f x)). Qed.
Lemma lem344284 {A : Type'} (n : nat) (i : nat) (i' : nat) (n' : nat) (f : A -> nat) (x : nat -> A) : (term950 A n i i' n' f x) = (term981 A n i i' n' f x).
Proof. exact (TRANS (@lem344260 A n i i' n' f x) (@lem344283 A n i i' n' f x)). Qed.
Lemma lem344285 {A : Type'} (n : nat) (i : nat) (n' : nat) (f : A -> nat) (x : nat -> A) : (term952 A n i n' f x) = (term982 A n i n' f x).
Proof. exact (fun_ext (fun i' : nat => @lem344284 A n i i' n' f x)). Qed.
Lemma lem344286 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem344287 {A : Type'} (n : nat) (i : nat) (n' : nat) (f : A -> nat) (x : nat -> A) : (term953 A n i n' f x) = (term983 A n i n' f x).
Proof. exact (MK_COMB (@lem344286) (@lem344285 A n i n' f x)). Qed.
Lemma lem344288 {A : Type'} (n : nat) (i : nat) (n' : nat) (f : A -> nat) (x : nat -> A) : (term935 A n i n' f x) = (term983 A n i n' f x).
Proof. exact (TRANS (@lem344240 A n i n' f x) (@lem344287 A n i n' f x)). Qed.
Lemma lem344289 {A : Type'} (n : nat) (i : nat) (f : A -> nat) (x : nat -> A) : (term937 A n i f x) = (term984 A n i f x).
Proof. exact (fun_ext (fun n' : nat => @lem344288 A n i n' f x)). Qed.
Lemma lem344290 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem344291 {A : Type'} (n : nat) (i : nat) (f : A -> nat) (x : nat -> A) : (term938 A n i f x) = (term985 A n i f x).
Proof. exact (MK_COMB (@lem344290) (@lem344289 A n i f x)). Qed.
Lemma lem344292 {A : Type'} (n : nat) (i : nat) (f : A -> nat) (x : nat -> A) : (term920 A n i f x) = (term985 A n i f x).
Proof. exact (TRANS (@lem344214 A n i f x) (@lem344291 A n i f x)). Qed.
Lemma lem344293 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term922 A n f x) = (term986 A n f x).
Proof. exact (fun_ext (fun i : nat => @lem344292 A n i f x)). Qed.
Lemma lem344294 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem344295 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term923 A n f x) = (term987 A n f x).
Proof. exact (MK_COMB (@lem344294) (@lem344293 A n f x)). Qed.
Lemma lem344296 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term905 A n f x) = (term987 A n f x).
Proof. exact (TRANS (@lem344188 A n f x) (@lem344295 A n f x)). Qed.
Lemma lem344297 {A : Type'} (f : A -> nat) (x : nat -> A) : (term907 A f x) = (term988 A f x).
Proof. exact (fun_ext (fun n : nat => @lem344296 A n f x)). Qed.
Lemma lem344298 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem344299 {A : Type'} (f : A -> nat) (x : nat -> A) : (term908 A f x) = (term989 A f x).
Proof. exact (MK_COMB (@lem344298) (@lem344297 A f x)). Qed.
Lemma lem344300 {A : Type'} (f : A -> nat) (x : nat -> A) : (term891 A f x) = (term989 A f x).
Proof. exact (TRANS (@lem344162 A f x) (@lem344299 A f x)). Qed.
Lemma lem344302 {A : Type'} (f : A -> nat) (x : nat -> A) : (term696 A f x) = (term989 A f x).
Proof. exact (TRANS (@lem344136 A f x) (@lem344300 A f x)). Qed.
Lemma lem344303 {A : Type'} (f : A -> nat) (x : nat -> A) : ((term471 A f x) = (term489 A f x)) = (term989 A f x).
Proof. exact (TRANS (@lem343593 A f x) (@lem344302 A f x)). Qed.
Lemma lem344304 {A : Type'} (f : A -> nat) (x : nat -> A) (h1 : (term471 A f x) = (term489 A f x)) : term989 A f x.
Proof. exact (EQ_MP (@lem344303 A f x) (@lem342794 A f x h1)). Qed.
Lemma lem344305 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) (h1 : term987 A n f x) : term987 A n f x.
Proof. exact (h1). Qed.
Lemma lem344306 {A : Type'} (n : nat) (i : nat) (f : A -> nat) (x : nat -> A) (h1 : term985 A n i f x) : term985 A n i f x.
Proof. exact (h1). Qed.
Lemma lem344307 {A : Type'} (n : nat) (i : nat) (n' : nat) (f : A -> nat) (x : nat -> A) (h1 : term983 A n i n' f x) : term983 A n i n' f x.
Proof. exact (h1). Qed.
Lemma lem344308 {A : Type'} (n : nat) (i : nat) (i' : nat) (n' : nat) (f : A -> nat) (x : nat -> A) (h1 : term981 A n i i' n' f x) : term981 A n i i' n' f x.
Proof. exact (h1). Qed.
Lemma lem344309 {A : Type'} (n : nat) (i : nat) (i' : nat) (n' : nat) (m : nat -> nat) (f : A -> nat) (x : nat -> A) (h1 : term979 A n i i' n' m f x) : term979 A n i i' n' m f x.
Proof. exact (h1). Qed.
Lemma lem344310 {A : Type'} (n : nat) (i : nat) (i' : nat) (n' : nat) (m : nat -> nat) (f : A -> nat) (x : nat -> A) (i'' : nat -> nat) (h1 : term976 A n i i' n' m f x i'') : term976 A n i i' n' m f x i''.
Proof. exact (h1). Qed.
Lemma lem344311 {A : Type'} (k : nat -> nat) (f : A -> nat) (x : nat -> A) (h1 : term636 A k f x) : term636 A k f x.
Proof. exact (h1). Qed.
Lemma lem344313 {A : Type'} (lt2 : type1402 A) (f' : type184 A) (h1 : term251 A lt2 f') : term251 A lt2 f'.
Proof. exact (h1). Qed.
Lemma lem344314 {A : Type'} (lt2 : type1402 A) (g : type184 A) (f' : type184 A) (h1 : term249 A lt2 g f') : term249 A lt2 g f'.
Proof. exact (h1). Qed.
Lemma lem344532 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem344537 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem344538 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem344537 nat nat f x). Qed.
Lemma lem344540 (m : nat -> nat) (n : nat) : (m n) = (@I (nat -> nat) m n).
Proof. exact (@lem344538 m n). Qed.
Lemma lem344541 {A : Type'} (f : A -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem344542 {A : Type'} (x : nat -> A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem344547 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem344548 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem344547 nat nat f x). Qed.
Lemma lem344550 (i'' : nat -> nat) (n : nat) : (i'' n) = (@I (nat -> nat) i'' n).
Proof. exact (@lem344548 i'' n). Qed.
Lemma lem344551 {A : Type'} (x : nat -> A) (i'' : nat -> nat) (n : nat) : (term990 A x i'' n) = (term991 A x i'' n).
Proof. exact (MK_COMB (@lem344542 A x) (@lem344550 i'' n)). Qed.
Lemma lem344553 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem344554 {A : Type'} (f : nat -> A) (x : nat) : (f x) = (@I (nat -> A) f x).
Proof. exact (@lem344553 nat A f x). Qed.
Lemma lem344555 {A : Type'} (x : nat -> A) (i'' : nat -> nat) (n : nat) : (term991 A x i'' n) = (term992 A x i'' n).
Proof. exact (@lem344554 A x (@I (nat -> nat) i'' n)). Qed.
Lemma lem344556 {A : Type'} (x : nat -> A) (i'' : nat -> nat) (n : nat) : (term990 A x i'' n) = (term992 A x i'' n).
Proof. exact (TRANS (@lem344551 A x i'' n) (@lem344555 A x i'' n)). Qed.
Lemma lem344557 {A : Type'} (f : A -> nat) (x : nat -> A) (i'' : nat -> nat) (n : nat) : (term993 A f x i'' n) = (term994 A f x i'' n).
Proof. exact (MK_COMB (@lem344541 A f) (@lem344556 A x i'' n)). Qed.
Lemma lem344559 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem344560 {A : Type'} (f : A -> nat) (x : A) : (f x) = (@I (A -> nat) f x).
Proof. exact (@lem344559 A nat f x). Qed.
Lemma lem344561 {A : Type'} (f : A -> nat) (x : nat -> A) (i'' : nat -> nat) (n : nat) : (term994 A f x i'' n) = (term995 A f x i'' n).
Proof. exact (@lem344560 A f (term992 A x i'' n)). Qed.
Lemma lem344562 {A : Type'} (f : A -> nat) (x : nat -> A) (i'' : nat -> nat) (n : nat) : (term993 A f x i'' n) = (term995 A f x i'' n).
Proof. exact (TRANS (@lem344557 A f x i'' n) (@lem344561 A f x i'' n)). Qed.
Lemma lem344563 (m : nat -> nat) (n : nat) : (term996 m n) = (term997 m n).
Proof. exact (MK_COMB (@lem344532) (@lem344540 m n)). Qed.
Lemma lem344564 {A : Type'} (m : nat -> nat) (f : A -> nat) (x : nat -> A) (i'' : nat -> nat) (n : nat) : ((m n) = (term993 A f x i'' n)) = ((@I (nat -> nat) m n) = (term995 A f x i'' n)).
Proof. exact (MK_COMB (@lem344563 m n) (@lem344562 A f x i'' n)). Qed.
Lemma lem344565 : Peano.lt = Peano.lt.
Proof. exact (eq_refl Peano.lt). Qed.
Lemma lem344570 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem344571 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem344570 nat nat f x). Qed.
Lemma lem344573 (m : nat -> nat) (n : nat) : (m n) = (@I (nat -> nat) m n).
Proof. exact (@lem344571 m n). Qed.
Lemma lem344574 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem344575 (m : nat -> nat) (n : nat) : (term998 m n) = (term999 m n).
Proof. exact (MK_COMB (@lem344565) (@lem344573 m n)). Qed.
Lemma lem344576 (m : nat -> nat) (n : nat) : (term1000 m n) = (term1001 m n).
Proof. exact (MK_COMB (@lem344575 m n) (@lem344574 n)). Qed.
Lemma lem344578 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem344579 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem344578 nat (nat -> Prop) f x). Qed.
Lemma lem344580 (m : nat -> nat) (n : nat) : (term999 m n) = (term1002 m n).
Proof. exact (@lem344579 Peano.lt (@I (nat -> nat) m n)). Qed.
Lemma lem344581 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem344582 (m : nat -> nat) (n : nat) : (term1001 m n) = (term1003 m n).
Proof. exact (MK_COMB (@lem344580 m n) (@lem344581 n)). Qed.
Lemma lem344584 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem344585 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem344584 nat Prop f x). Qed.
Lemma lem344586 (m : nat -> nat) (n : nat) : (term1003 m n) = (term1004 m n).
Proof. exact (@lem344585 (term1002 m n) n). Qed.
Lemma lem344587 (m : nat -> nat) (n : nat) : (term1001 m n) = (term1004 m n).
Proof. exact (TRANS (@lem344582 m n) (@lem344586 m n)). Qed.
Lemma lem344588 (m : nat -> nat) (n : nat) : (term1000 m n) = (term1004 m n).
Proof. exact (TRANS (@lem344576 m n) (@lem344587 m n)). Qed.
Lemma lem344589 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem344590 (m : nat -> nat) (n : nat) : (term1005 m n) = (term1006 m n).
Proof. exact (MK_COMB (@lem344589) (@lem344588 m n)). Qed.
Lemma lem344591 {A : Type'} (m : nat -> nat) (f : A -> nat) (x : nat -> A) (i'' : nat -> nat) (n : nat) : (term1007 A m f x i'' n) = (term1008 A m f x i'' n).
Proof. exact (MK_COMB (@lem344590 m n) (@lem344564 A m f x i'' n)). Qed.
Lemma lem344592 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem344595 {A : Type'} (f : A -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem344600 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem344601 {A : Type'} (f : nat -> A) (x : nat) : (f x) = (@I (nat -> A) f x).
Proof. exact (@lem344600 nat A f x). Qed.
Lemma lem344603 {A : Type'} (x : nat -> A) (i : nat) : (x i) = (@I (nat -> A) x i).
Proof. exact (@lem344601 A x i). Qed.
Lemma lem344604 {A : Type'} (f : A -> nat) (x : nat -> A) (i : nat) : (term406 A f x i) = (term1009 A f x i).
Proof. exact (MK_COMB (@lem344595 A f) (@lem344603 A x i)). Qed.
Lemma lem344606 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem344607 {A : Type'} (f : A -> nat) (x : A) : (f x) = (@I (A -> nat) f x).
Proof. exact (@lem344606 A nat f x). Qed.
Lemma lem344608 {A : Type'} (f : A -> nat) (x : nat -> A) (i : nat) : (term1009 A f x i) = (term1010 A f x i).
Proof. exact (@lem344607 A f (@I (nat -> A) x i)). Qed.
Lemma lem344609 {A : Type'} (f : A -> nat) (x : nat -> A) (i : nat) : (term406 A f x i) = (term1010 A f x i).
Proof. exact (TRANS (@lem344604 A f x i) (@lem344608 A f x i)). Qed.
Lemma lem344610 (n : nat) : (@eq nat n) = (@eq nat n).
Proof. exact (eq_refl (@eq nat n)). Qed.
Lemma lem344611 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) (i : nat) : (n = (term406 A f x i)) = (n = (term1010 A f x i)).
Proof. exact (MK_COMB (@lem344610 n) (@lem344609 A f x i)). Qed.
Lemma lem344612 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) (i : nat) : (term643 A n f x i) = (term1011 A n f x i).
Proof. exact (MK_COMB (@lem344592) (@lem344611 A n f x i)). Qed.
Lemma lem344613 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term645 A n f x) = (term1012 A n f x).
Proof. exact (fun_ext (fun i : nat => @lem344612 A n f x i)). Qed.
Lemma lem344614 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem344615 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term646 A n f x) = (term1013 A n f x).
Proof. exact (MK_COMB (@lem344614) (@lem344613 A n f x)). Qed.
Lemma lem344616 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem344617 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term672 A n f x) = (term1014 A n f x).
Proof. exact (MK_COMB (@lem344616) (@lem344615 A n f x)). Qed.
Lemma lem344618 {A : Type'} (m : nat -> nat) (f : A -> nat) (x : nat -> A) (i'' : nat -> nat) (n : nat) : (term852 A m f x i'' n) = (term1015 A m f x i'' n).
Proof. exact (MK_COMB (@lem344617 A n f x) (@lem344591 A m f x i'' n)). Qed.
Lemma lem344619 {A : Type'} (m : nat -> nat) (f : A -> nat) (x : nat -> A) (i'' : nat -> nat) : (term854 A m f x i'') = (term1016 A m f x i'').
Proof. exact (fun_ext (fun n : nat => @lem344618 A m f x i'' n)). Qed.
Lemma lem344620 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem344621 {A : Type'} (m : nat -> nat) (f : A -> nat) (x : nat -> A) (i'' : nat -> nat) : (term856 A m f x i'') = (term1017 A m f x i'').
Proof. exact (MK_COMB (@lem344620) (@lem344619 A m f x i'')). Qed.
Lemma lem344622 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem344625 {A : Type'} (f : A -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem344630 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem344631 {A : Type'} (f : nat -> A) (x : nat) : (f x) = (@I (nat -> A) f x).
Proof. exact (@lem344630 nat A f x). Qed.
Lemma lem344633 {A : Type'} (x : nat -> A) (i : nat) : (x i) = (@I (nat -> A) x i).
Proof. exact (@lem344631 A x i). Qed.
Lemma lem344634 {A : Type'} (f : A -> nat) (x : nat -> A) (i : nat) : (term406 A f x i) = (term1009 A f x i).
Proof. exact (MK_COMB (@lem344625 A f) (@lem344633 A x i)). Qed.
Lemma lem344636 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem344637 {A : Type'} (f : A -> nat) (x : A) : (f x) = (@I (A -> nat) f x).
Proof. exact (@lem344636 A nat f x). Qed.
Lemma lem344638 {A : Type'} (f : A -> nat) (x : nat -> A) (i : nat) : (term1009 A f x i) = (term1010 A f x i).
Proof. exact (@lem344637 A f (@I (nat -> A) x i)). Qed.
Lemma lem344639 {A : Type'} (f : A -> nat) (x : nat -> A) (i : nat) : (term406 A f x i) = (term1010 A f x i).
Proof. exact (TRANS (@lem344634 A f x i) (@lem344638 A f x i)). Qed.
Lemma lem344640 (n : nat) : (@eq nat n) = (@eq nat n).
Proof. exact (eq_refl (@eq nat n)). Qed.
Lemma lem344641 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) (i : nat) : (n = (term406 A f x i)) = (n = (term1010 A f x i)).
Proof. exact (MK_COMB (@lem344640 n) (@lem344639 A f x i)). Qed.
Lemma lem344642 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) (i : nat) : (term643 A n f x i) = (term1011 A n f x i).
Proof. exact (MK_COMB (@lem344622) (@lem344641 A n f x i)). Qed.
Lemma lem344643 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term645 A n f x) = (term1012 A n f x).
Proof. exact (fun_ext (fun i : nat => @lem344642 A n f x i)). Qed.
Lemma lem344644 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem344645 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term646 A n f x) = (term1013 A n f x).
Proof. exact (MK_COMB (@lem344644) (@lem344643 A n f x)). Qed.
Lemma lem344646 {A : Type'} (f : A -> nat) (x : nat -> A) : (term650 A f x) = (term1018 A f x).
Proof. exact (fun_ext (fun n : nat => @lem344645 A n f x)). Qed.
Lemma lem344647 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem344648 {A : Type'} (f : A -> nat) (x : nat -> A) : (term651 A f x) = (term1019 A f x).
Proof. exact (MK_COMB (@lem344647) (@lem344646 A f x)). Qed.
Lemma lem344649 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem344650 {A : Type'} (f : A -> nat) (x : nat -> A) : (term687 A f x) = (term1020 A f x).
Proof. exact (MK_COMB (@lem344649) (@lem344648 A f x)). Qed.
Lemma lem344651 {A : Type'} (m : nat -> nat) (f : A -> nat) (x : nat -> A) (i'' : nat -> nat) : (term885 A m f x i'') = (term1021 A m f x i'').
Proof. exact (MK_COMB (@lem344650 A f x) (@lem344621 A m f x i'')). Qed.
Lemma lem344652 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem344655 {A : Type'} (f : A -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem344660 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem344661 {A : Type'} (f : nat -> A) (x : nat) : (f x) = (@I (nat -> A) f x).
Proof. exact (@lem344660 nat A f x). Qed.
Lemma lem344663 {A : Type'} (x : nat -> A) (i : nat) : (x i) = (@I (nat -> A) x i).
Proof. exact (@lem344661 A x i). Qed.
Lemma lem344664 {A : Type'} (f : A -> nat) (x : nat -> A) (i : nat) : (term406 A f x i) = (term1009 A f x i).
Proof. exact (MK_COMB (@lem344655 A f) (@lem344663 A x i)). Qed.
Lemma lem344666 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem344667 {A : Type'} (f : A -> nat) (x : A) : (f x) = (@I (A -> nat) f x).
Proof. exact (@lem344666 A nat f x). Qed.
Lemma lem344668 {A : Type'} (f : A -> nat) (x : nat -> A) (i : nat) : (term1009 A f x i) = (term1010 A f x i).
Proof. exact (@lem344667 A f (@I (nat -> A) x i)). Qed.
Lemma lem344669 {A : Type'} (f : A -> nat) (x : nat -> A) (i : nat) : (term406 A f x i) = (term1010 A f x i).
Proof. exact (TRANS (@lem344664 A f x i) (@lem344668 A f x i)). Qed.
Lemma lem344670 (m : nat) : (@eq nat m) = (@eq nat m).
Proof. exact (eq_refl (@eq nat m)). Qed.
Lemma lem344671 {A : Type'} (m : nat) (f : A -> nat) (x : nat -> A) (i : nat) : (m = (term406 A f x i)) = (m = (term1010 A f x i)).
Proof. exact (MK_COMB (@lem344670 m) (@lem344669 A f x i)). Qed.
Lemma lem344672 {A : Type'} (m : nat) (f : A -> nat) (x : nat -> A) (i : nat) : (term643 A m f x i) = (term1011 A m f x i).
Proof. exact (MK_COMB (@lem344652) (@lem344671 A m f x i)). Qed.
Lemma lem344673 {A : Type'} (m : nat) (f : A -> nat) (x : nat -> A) : (term645 A m f x) = (term1012 A m f x).
Proof. exact (fun_ext (fun i : nat => @lem344672 A m f x i)). Qed.
Lemma lem344674 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem344675 {A : Type'} (m : nat) (f : A -> nat) (x : nat -> A) : (term646 A m f x) = (term1013 A m f x).
Proof. exact (MK_COMB (@lem344674) (@lem344673 A m f x)). Qed.
Lemma lem344676 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem344683 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem344684 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem344683 nat (nat -> Prop) f x). Qed.
Lemma lem344685 (m : nat) : (Peano.lt m) = (@I (nat -> nat -> Prop) Peano.lt m).
Proof. exact (@lem344684 Peano.lt m). Qed.
Lemma lem344686 (n' : nat) : n' = n'.
Proof. exact (eq_refl n'). Qed.
Lemma lem344687 (m : nat) (n' : nat) : (Peano.lt m n') = (@I (nat -> nat -> Prop) Peano.lt m n').
Proof. exact (MK_COMB (@lem344685 m) (@lem344686 n')). Qed.
Lemma lem344689 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem344690 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem344689 nat Prop f x). Qed.
Lemma lem344691 (m : nat) (n' : nat) : (@I (nat -> nat -> Prop) Peano.lt m n') = (term1022 m n').
Proof. exact (@lem344690 (@I (nat -> nat -> Prop) Peano.lt m) n'). Qed.
Lemma lem344693 (m : nat) (n' : nat) : (Peano.lt m n') = (term1022 m n').
Proof. exact (TRANS (@lem344687 m n') (@lem344691 m n')). Qed.
Lemma lem344694 (m : nat) (n' : nat) : (term1023 m n') = (term1024 m n').
Proof. exact (MK_COMB (@lem344676) (@lem344693 m n')). Qed.
Lemma lem344695 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem344696 (m : nat) (n' : nat) : (term657 m n') = (term1025 m n').
Proof. exact (MK_COMB (@lem344695) (@lem344694 m n')). Qed.
Lemma lem344697 {A : Type'} (n' : nat) (m : nat) (f : A -> nat) (x : nat -> A) : (term659 A n' m f x) = (term1026 A n' m f x).
Proof. exact (MK_COMB (@lem344696 m n') (@lem344675 A m f x)). Qed.
Lemma lem344698 {A : Type'} (n' : nat) (f : A -> nat) (x : nat -> A) : (term669 A n' f x) = (term1027 A n' f x).
Proof. exact (fun_ext (fun m : nat => @lem344697 A n' m f x)). Qed.
Lemma lem344699 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem344700 {A : Type'} (n' : nat) (f : A -> nat) (x : nat -> A) : (term670 A n' f x) = (term1028 A n' f x).
Proof. exact (MK_COMB (@lem344699) (@lem344698 A n' f x)). Qed.
Lemma lem344703 {A : Type'} (f : A -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem344708 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem344709 {A : Type'} (f : nat -> A) (x : nat) : (f x) = (@I (nat -> A) f x).
Proof. exact (@lem344708 nat A f x). Qed.
Lemma lem344711 {A : Type'} (x : nat -> A) (i' : nat) : (x i') = (@I (nat -> A) x i').
Proof. exact (@lem344709 A x i'). Qed.
Lemma lem344712 {A : Type'} (f : A -> nat) (x : nat -> A) (i' : nat) : (term406 A f x i') = (term1009 A f x i').
Proof. exact (MK_COMB (@lem344703 A f) (@lem344711 A x i')). Qed.
Lemma lem344714 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem344715 {A : Type'} (f : A -> nat) (x : A) : (f x) = (@I (A -> nat) f x).
Proof. exact (@lem344714 A nat f x). Qed.
Lemma lem344716 {A : Type'} (f : A -> nat) (x : nat -> A) (i' : nat) : (term1009 A f x i') = (term1010 A f x i').
Proof. exact (@lem344715 A f (@I (nat -> A) x i')). Qed.
Lemma lem344717 {A : Type'} (f : A -> nat) (x : nat -> A) (i' : nat) : (term406 A f x i') = (term1010 A f x i').
Proof. exact (TRANS (@lem344712 A f x i') (@lem344716 A f x i')). Qed.
Lemma lem344718 (n' : nat) : (@eq nat n') = (@eq nat n').
Proof. exact (eq_refl (@eq nat n')). Qed.
Lemma lem344719 {A : Type'} (n' : nat) (f : A -> nat) (x : nat -> A) (i' : nat) : (n' = (term406 A f x i')) = (n' = (term1010 A f x i')).
Proof. exact (MK_COMB (@lem344718 n') (@lem344717 A f x i')). Qed.
Lemma lem344720 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem344721 {A : Type'} (n' : nat) (f : A -> nat) (x : nat -> A) (i' : nat) : (term709 A n' f x i') = (term1029 A n' f x i').
Proof. exact (MK_COMB (@lem344720) (@lem344719 A n' f x i')). Qed.
Lemma lem344722 {A : Type'} (i' : nat) (n' : nat) (f : A -> nat) (x : nat -> A) : (term711 A i' n' f x) = (term1030 A i' n' f x).
Proof. exact (MK_COMB (@lem344721 A n' f x i') (@lem344700 A n' f x)). Qed.
Lemma lem344725 {A : Type'} (f : A -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem344730 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem344731 {A : Type'} (f : nat -> A) (x : nat) : (f x) = (@I (nat -> A) f x).
Proof. exact (@lem344730 nat A f x). Qed.
Lemma lem344733 {A : Type'} (x : nat -> A) (i : nat) : (x i) = (@I (nat -> A) x i).
Proof. exact (@lem344731 A x i). Qed.
Lemma lem344734 {A : Type'} (f : A -> nat) (x : nat -> A) (i : nat) : (term406 A f x i) = (term1009 A f x i).
Proof. exact (MK_COMB (@lem344725 A f) (@lem344733 A x i)). Qed.
Lemma lem344736 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem344737 {A : Type'} (f : A -> nat) (x : A) : (f x) = (@I (A -> nat) f x).
Proof. exact (@lem344736 A nat f x). Qed.
Lemma lem344738 {A : Type'} (f : A -> nat) (x : nat -> A) (i : nat) : (term1009 A f x i) = (term1010 A f x i).
Proof. exact (@lem344737 A f (@I (nat -> A) x i)). Qed.
Lemma lem344739 {A : Type'} (f : A -> nat) (x : nat -> A) (i : nat) : (term406 A f x i) = (term1010 A f x i).
Proof. exact (TRANS (@lem344734 A f x i) (@lem344738 A f x i)). Qed.
Lemma lem344740 (n : nat) : (@eq nat n) = (@eq nat n).
Proof. exact (eq_refl (@eq nat n)). Qed.
Lemma lem344741 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) (i : nat) : (n = (term406 A f x i)) = (n = (term1010 A f x i)).
Proof. exact (MK_COMB (@lem344740 n) (@lem344739 A f x i)). Qed.
Lemma lem344742 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem344743 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) (i : nat) : (term709 A n f x i) = (term1029 A n f x i).
Proof. exact (MK_COMB (@lem344742) (@lem344741 A n f x i)). Qed.
Lemma lem344744 {A : Type'} (n : nat) (i : nat) (i' : nat) (n' : nat) (f : A -> nat) (x : nat -> A) : (term761 A n i i' n' f x) = (term1031 A n i i' n' f x).
Proof. exact (MK_COMB (@lem344743 A n f x i) (@lem344722 A i' n' f x)). Qed.
Lemma lem344745 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem344746 {A : Type'} (n : nat) (i : nat) (i' : nat) (n' : nat) (f : A -> nat) (x : nat -> A) : (term948 A n i i' n' f x) = (term1032 A n i i' n' f x).
Proof. exact (MK_COMB (@lem344745) (@lem344744 A n i i' n' f x)). Qed.
Lemma lem344747 {A : Type'} (n : nat) (i : nat) (i' : nat) (n' : nat) (m : nat -> nat) (f : A -> nat) (x : nat -> A) (i'' : nat -> nat) : (term976 A n i i' n' m f x i'') = (term1033 A n i i' n' m f x i'').
Proof. exact (MK_COMB (@lem344746 A n i i' n' f x) (@lem344651 A m f x i'')). Qed.
Lemma lem344748 {A : Type'} (n : nat) (i : nat) (i' : nat) (n' : nat) (m : nat -> nat) (f : A -> nat) (x : nat -> A) (i'' : nat -> nat) (h1 : term976 A n i i' n' m f x i'') : term1033 A n i i' n' m f x i''.
Proof. exact (EQ_MP (@lem344747 A n i i' n' m f x i'') (@lem344310 A n i i' n' m f x i'' h1)). Qed.
Lemma lem344749 : Peano.lt = Peano.lt.
Proof. exact (eq_refl Peano.lt). Qed.
Lemma lem344750 {A : Type'} (f : A -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem344751 {A : Type'} (x : nat -> A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem344756 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem344757 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem344756 nat nat f x). Qed.
Lemma lem344759 (k : nat -> nat) (n : nat) : (k n) = (@I (nat -> nat) k n).
Proof. exact (@lem344757 k n). Qed.
Lemma lem344760 {A : Type'} (x : nat -> A) (k : nat -> nat) (n : nat) : (term990 A x k n) = (term991 A x k n).
Proof. exact (MK_COMB (@lem344751 A x) (@lem344759 k n)). Qed.
Lemma lem344762 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem344763 {A : Type'} (f : nat -> A) (x : nat) : (f x) = (@I (nat -> A) f x).
Proof. exact (@lem344762 nat A f x). Qed.
Lemma lem344764 {A : Type'} (x : nat -> A) (k : nat -> nat) (n : nat) : (term991 A x k n) = (term992 A x k n).
Proof. exact (@lem344763 A x (@I (nat -> nat) k n)). Qed.
Lemma lem344765 {A : Type'} (x : nat -> A) (k : nat -> nat) (n : nat) : (term990 A x k n) = (term992 A x k n).
Proof. exact (TRANS (@lem344760 A x k n) (@lem344764 A x k n)). Qed.
Lemma lem344766 {A : Type'} (f : A -> nat) (x : nat -> A) (k : nat -> nat) (n : nat) : (term993 A f x k n) = (term994 A f x k n).
Proof. exact (MK_COMB (@lem344750 A f) (@lem344765 A x k n)). Qed.
Lemma lem344768 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem344769 {A : Type'} (f : A -> nat) (x : A) : (f x) = (@I (A -> nat) f x).
Proof. exact (@lem344768 A nat f x). Qed.
Lemma lem344770 {A : Type'} (f : A -> nat) (x : nat -> A) (k : nat -> nat) (n : nat) : (term994 A f x k n) = (term995 A f x k n).
Proof. exact (@lem344769 A f (term992 A x k n)). Qed.
Lemma lem344771 {A : Type'} (f : A -> nat) (x : nat -> A) (k : nat -> nat) (n : nat) : (term993 A f x k n) = (term995 A f x k n).
Proof. exact (TRANS (@lem344766 A f x k n) (@lem344770 A f x k n)). Qed.
Lemma lem344772 {A : Type'} (f : A -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem344777 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem344778 {A : Type'} (f : nat -> A) (x : nat) : (f x) = (@I (nat -> A) f x).
Proof. exact (@lem344777 nat A f x). Qed.
Lemma lem344780 {A : Type'} (x : nat -> A) (n : nat) : (x n) = (@I (nat -> A) x n).
Proof. exact (@lem344778 A x n). Qed.
Lemma lem344781 {A : Type'} (f : A -> nat) (x : nat -> A) (n : nat) : (term406 A f x n) = (term1009 A f x n).
Proof. exact (MK_COMB (@lem344772 A f) (@lem344780 A x n)). Qed.
Lemma lem344783 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem344784 {A : Type'} (f : A -> nat) (x : A) : (f x) = (@I (A -> nat) f x).
Proof. exact (@lem344783 A nat f x). Qed.
Lemma lem344785 {A : Type'} (f : A -> nat) (x : nat -> A) (n : nat) : (term1009 A f x n) = (term1010 A f x n).
Proof. exact (@lem344784 A f (@I (nat -> A) x n)). Qed.
Lemma lem344786 {A : Type'} (f : A -> nat) (x : nat -> A) (n : nat) : (term406 A f x n) = (term1010 A f x n).
Proof. exact (TRANS (@lem344781 A f x n) (@lem344785 A f x n)). Qed.
Lemma lem344787 {A : Type'} (f : A -> nat) (x : nat -> A) (k : nat -> nat) (n : nat) : (term1034 A f x k n) = (term1035 A f x k n).
Proof. exact (MK_COMB (@lem344749) (@lem344771 A f x k n)). Qed.
Lemma lem344788 {A : Type'} (k : nat -> nat) (f : A -> nat) (x : nat -> A) (n : nat) : (term632 A k f x n) = (term1036 A k f x n).
Proof. exact (MK_COMB (@lem344787 A f x k n) (@lem344786 A f x n)). Qed.
Lemma lem344790 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem344791 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem344790 nat (nat -> Prop) f x). Qed.
Lemma lem344792 {A : Type'} (f : A -> nat) (x : nat -> A) (k : nat -> nat) (n : nat) : (term1035 A f x k n) = (term1037 A f x k n).
Proof. exact (@lem344791 Peano.lt (term995 A f x k n)). Qed.
Lemma lem344793 {A : Type'} (f : A -> nat) (x : nat -> A) (n : nat) : (term1010 A f x n) = (term1010 A f x n).
Proof. exact (eq_refl (term1010 A f x n)). Qed.
Lemma lem344794 {A : Type'} (k : nat -> nat) (f : A -> nat) (x : nat -> A) (n : nat) : (term1036 A k f x n) = (term1038 A k f x n).
Proof. exact (MK_COMB (@lem344792 A f x k n) (@lem344793 A f x n)). Qed.
Lemma lem344796 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem344797 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem344796 nat Prop f x). Qed.
Lemma lem344798 {A : Type'} (k : nat -> nat) (f : A -> nat) (x : nat -> A) (n : nat) : (term1038 A k f x n) = (term1039 A k f x n).
Proof. exact (@lem344797 (term1037 A f x k n) (term1010 A f x n)). Qed.
Lemma lem344799 {A : Type'} (k : nat -> nat) (f : A -> nat) (x : nat -> A) (n : nat) : (term1036 A k f x n) = (term1039 A k f x n).
Proof. exact (TRANS (@lem344794 A k f x n) (@lem344798 A k f x n)). Qed.
Lemma lem344800 {A : Type'} (k : nat -> nat) (f : A -> nat) (x : nat -> A) (n : nat) : (term632 A k f x n) = (term1039 A k f x n).
Proof. exact (TRANS (@lem344788 A k f x n) (@lem344799 A k f x n)). Qed.
Lemma lem344801 {A : Type'} (k : nat -> nat) (f : A -> nat) (x : nat -> A) : (term634 A k f x) = (term1040 A k f x).
Proof. exact (fun_ext (fun n : nat => @lem344800 A k f x n)). Qed.
Lemma lem344802 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem344803 {A : Type'} (k : nat -> nat) (f : A -> nat) (x : nat -> A) : (term636 A k f x) = (term1041 A k f x).
Proof. exact (MK_COMB (@lem344802) (@lem344801 A k f x)). Qed.
Lemma lem344804 {A : Type'} (k : nat -> nat) (f : A -> nat) (x : nat -> A) (h1 : term636 A k f x) : term1041 A k f x.
Proof. exact (EQ_MP (@lem344803 A k f x) (@lem344311 A k f x h1)). Qed.
Lemma lem345040 {A : Type'} (n : nat) (i : nat) (i' : nat) (n' : nat) (f : A -> nat) (x : nat -> A) (h1 : term1031 A n i i' n' f x) : term1031 A n i i' n' f x.
Proof. exact (h1). Qed.
Lemma lem345041 {A : Type'} (m : nat -> nat) (f : A -> nat) (x : nat -> A) (i'' : nat -> nat) (h1 : term1021 A m f x i'') : term1021 A m f x i''.
Proof. exact (h1). Qed.
Lemma lem345042 {A : Type'} (n : nat) (i : nat) (i' : nat) (n' : nat) (f : A -> nat) (x : nat -> A) (h1 : term1031 A n i i' n' f x) : term1030 A i' n' f x.
Proof. exact (proj2 (@lem345040 A n i i' n' f x h1)). Qed.
Lemma lem345044 {A : Type'} (n : nat) (i : nat) (i' : nat) (n' : nat) (f : A -> nat) (x : nat -> A) (h1 : term1031 A n i i' n' f x) : term1028 A n' f x.
Proof. exact (proj2 (@lem345042 A n i i' n' f x h1)). Qed.
Lemma lem345047 {A : Type'} (m : nat -> nat) (f : A -> nat) (x : nat -> A) (i'' : nat -> nat) (h1 : term1021 A m f x i'') : term1019 A f x.
Proof. exact (proj1 (@lem345041 A m f x i'' h1)). Qed.
Lemma lem345117 {A : Type'} (k : nat -> nat) (f : A -> nat) (x : nat -> A) (n : nat) : (term1039 A k f x n) = (term1039 A k f x n).
Proof. exact (eq_refl (term1039 A k f x n)). Qed.
Lemma lem345118 {A : Type'} (k : nat -> nat) (f : A -> nat) (x : nat -> A) : (term1040 A k f x) = (term1040 A k f x).
Proof. exact (fun_ext (fun n : nat => @lem345117 A k f x n)). Qed.
Lemma lem345119 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem345121 {A : Type'} (k : nat -> nat) (f : A -> nat) (x : nat -> A) : (term1041 A k f x) = (term1041 A k f x).
Proof. exact (MK_COMB (@lem345119) (@lem345118 A k f x)). Qed.
Lemma lem345122 {A : Type'} (k : nat -> nat) (f : A -> nat) (x : nat -> A) (h1 : term636 A k f x) : term1041 A k f x.
Proof. exact (EQ_MP (@lem345121 A k f x) (@lem344804 A k f x h1)). Qed.
Lemma lem345253 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1042 A P Q) = (term1043 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem345254 (P : Prop) (Q : nat -> Prop) : (term1044 P Q) = (term1045 P Q).
Proof. exact (@lem345253 nat P Q). Qed.
Lemma lem345255 {A : Type'} (n' : nat) (m : nat) (f : A -> nat) (x : nat -> A) : (term1046 A n' m f x) = (term1047 A n' m f x).
Proof. exact (@lem345254 (term1024 m n') (term1012 A m f x)). Qed.
Lemma lem345256 {A : Type'} (m : nat) (f : A -> nat) (x : nat -> A) (i : nat) : (term1048 A m f x i) = (term1011 A m f x i).
Proof. exact (eq_refl (term1048 A m f x i)). Qed.
Lemma lem345257 {A : Type'} (m : nat) (f : A -> nat) (x : nat -> A) : (term1049 A m f x) = (term1012 A m f x).
Proof. exact (fun_ext (fun i : nat => @lem345256 A m f x i)). Qed.
Lemma lem345258 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem345259 {A : Type'} (m : nat) (f : A -> nat) (x : nat -> A) : (term1050 A m f x) = (term1013 A m f x).
Proof. exact (MK_COMB (@lem345258) (@lem345257 A m f x)). Qed.
Lemma lem345260 (m : nat) (n' : nat) : (term1025 m n') = (term1025 m n').
Proof. exact (eq_refl (term1025 m n')). Qed.
Lemma lem345261 {A : Type'} (n' : nat) (m : nat) (f : A -> nat) (x : nat -> A) : (term1046 A n' m f x) = (term1026 A n' m f x).
Proof. exact (MK_COMB (@lem345260 m n') (@lem345259 A m f x)). Qed.
Lemma lem345262 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem345263 {A : Type'} (n' : nat) (m : nat) (f : A -> nat) (x : nat -> A) : (term1051 A n' m f x) = (term1052 A n' m f x).
Proof. exact (MK_COMB (@lem345262) (@lem345261 A n' m f x)). Qed.
Lemma lem345264 {A : Type'} (m : nat) (f : A -> nat) (x : nat -> A) (i : nat) : (term1048 A m f x i) = (term1011 A m f x i).
Proof. exact (eq_refl (term1048 A m f x i)). Qed.
Lemma lem345265 (m : nat) (n' : nat) : (term1025 m n') = (term1025 m n').
Proof. exact (eq_refl (term1025 m n')). Qed.
Lemma lem345266 {A : Type'} (n' : nat) (m : nat) (f : A -> nat) (x : nat -> A) (i : nat) : (term1053 A n' m f x i) = (term1054 A n' m f x i).
Proof. exact (MK_COMB (@lem345265 m n') (@lem345264 A m f x i)). Qed.
Lemma lem345267 {A : Type'} (n' : nat) (m : nat) (f : A -> nat) (x : nat -> A) : (term1055 A n' m f x) = (term1056 A n' m f x).
Proof. exact (fun_ext (fun i : nat => @lem345266 A n' m f x i)). Qed.
Lemma lem345268 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem345269 {A : Type'} (n' : nat) (m : nat) (f : A -> nat) (x : nat -> A) : (term1047 A n' m f x) = (term1057 A n' m f x).
Proof. exact (MK_COMB (@lem345268) (@lem345267 A n' m f x)). Qed.
Lemma lem345270 {A : Type'} (n' : nat) (m : nat) (f : A -> nat) (x : nat -> A) : ((term1046 A n' m f x) = (term1047 A n' m f x)) = ((term1026 A n' m f x) = (term1057 A n' m f x)).
Proof. exact (MK_COMB (@lem345263 A n' m f x) (@lem345269 A n' m f x)). Qed.
Lemma lem345271 {A : Type'} (n' : nat) (m : nat) (f : A -> nat) (x : nat -> A) : (term1026 A n' m f x) = (term1057 A n' m f x).
Proof. exact (EQ_MP (@lem345270 A n' m f x) (@lem345255 A n' m f x)). Qed.
Lemma lem345272 {A : Type'} (n' : nat) (f : A -> nat) (x : nat -> A) : (term1027 A n' f x) = (term1058 A n' f x).
Proof. exact (fun_ext (fun m : nat => @lem345271 A n' m f x)). Qed.
Lemma lem345273 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem345274 {A : Type'} (n' : nat) (f : A -> nat) (x : nat -> A) : (term1028 A n' f x) = (term1059 A n' f x).
Proof. exact (MK_COMB (@lem345273) (@lem345272 A n' f x)). Qed.
Lemma lem345281 {A : Type'} (n' : nat) (m : nat) (f : A -> nat) (x : nat -> A) (i : nat) : (term1054 A n' m f x i) = (term1054 A n' m f x i).
Proof. exact (eq_refl (term1054 A n' m f x i)). Qed.
Lemma lem345282 {A : Type'} (n' : nat) (m : nat) (f : A -> nat) (x : nat -> A) : (term1056 A n' m f x) = (term1056 A n' m f x).
Proof. exact (fun_ext (fun i : nat => @lem345281 A n' m f x i)). Qed.
Lemma lem345283 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem345284 {A : Type'} (n' : nat) (m : nat) (f : A -> nat) (x : nat -> A) : (term1057 A n' m f x) = (term1057 A n' m f x).
Proof. exact (MK_COMB (@lem345283) (@lem345282 A n' m f x)). Qed.
Lemma lem345285 {A : Type'} (n' : nat) (f : A -> nat) (x : nat -> A) : (term1058 A n' f x) = (term1058 A n' f x).
Proof. exact (fun_ext (fun m : nat => @lem345284 A n' m f x)). Qed.
Lemma lem345286 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem345287 {A : Type'} (n' : nat) (f : A -> nat) (x : nat -> A) : (term1059 A n' f x) = (term1059 A n' f x).
Proof. exact (MK_COMB (@lem345286) (@lem345285 A n' f x)). Qed.
Lemma lem345288 {A : Type'} (n' : nat) (f : A -> nat) (x : nat -> A) : (term1028 A n' f x) = (term1059 A n' f x).
Proof. exact (TRANS (@lem345274 A n' f x) (@lem345287 A n' f x)). Qed.
Lemma lem345289 {A : Type'} (n : nat) (i : nat) (i' : nat) (n' : nat) (f : A -> nat) (x : nat -> A) (h1 : term1031 A n i i' n' f x) : term1059 A n' f x.
Proof. exact (EQ_MP (@lem345288 A n' f x) (@lem345044 A n i i' n' f x h1)). Qed.
Lemma lem345487 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) (i : nat) : (term1011 A n f x i) = (term1011 A n f x i).
Proof. exact (eq_refl (term1011 A n f x i)). Qed.
Lemma lem345488 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term1012 A n f x) = (term1012 A n f x).
Proof. exact (fun_ext (fun i : nat => @lem345487 A n f x i)). Qed.
Lemma lem345489 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem345490 {A : Type'} (n : nat) (f : A -> nat) (x : nat -> A) : (term1013 A n f x) = (term1013 A n f x).
Proof. exact (MK_COMB (@lem345489) (@lem345488 A n f x)). Qed.
Lemma lem345491 {A : Type'} (f : A -> nat) (x : nat -> A) : (term1018 A f x) = (term1018 A f x).
Proof. exact (fun_ext (fun n : nat => @lem345490 A n f x)). Qed.
Lemma lem345492 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem345494 {A : Type'} (f : A -> nat) (x : nat -> A) : (term1019 A f x) = (term1019 A f x).
Proof. exact (MK_COMB (@lem345492) (@lem345491 A f x)). Qed.
Lemma lem345495 {A : Type'} (m : nat -> nat) (f : A -> nat) (x : nat -> A) (i'' : nat -> nat) (h1 : term1021 A m f x i'') : term1019 A f x.
Proof. exact (EQ_MP (@lem345494 A f x) (@lem345047 A m f x i'' h1)). Qed.
Lemma lem345566 {A : Type'} (_7417 : nat) (k : nat -> nat) (f : A -> nat) (x : nat -> A) (h1 : term636 A k f x) : term1060 A k f x _7417.
Proof. exact (@lem345122 A k f x h1 _7417). Qed.
Lemma lem345567 {A : Type'} (k : nat -> nat) (f : A -> nat) (x : nat -> A) (_7417 : nat) : (term1060 A k f x _7417) = (term1039 A k f x _7417).
Proof. exact (eq_refl (term1060 A k f x _7417)). Qed.
Lemma lem345581 {A : Type'} (_7422 : nat) (n : nat) (i : nat) (i' : nat) (n' : nat) (f : A -> nat) (x : nat -> A) (h1 : term1031 A n i i' n' f x) : term1061 A n' f x _7422.
Proof. exact (@lem345289 A n i i' n' f x h1 _7422). Qed.
Lemma lem345582 {A : Type'} (n' : nat) (_7422 : nat) (f : A -> nat) (x : nat -> A) : (term1061 A n' f x _7422) = (term1057 A n' _7422 f x).
Proof. exact (eq_refl (term1061 A n' f x _7422)). Qed.
Lemma lem345583 {A : Type'} (_7422 : nat) (n : nat) (i : nat) (i' : nat) (n' : nat) (f : A -> nat) (x : nat -> A) (h1 : term1031 A n i i' n' f x) : term1057 A n' _7422 f x.
Proof. exact (EQ_MP (@lem345582 A n' _7422 f x) (@lem345581 A _7422 n i i' n' f x h1)). Qed.
Lemma lem345584 {A : Type'} (_7422 : nat) (_7423 : nat) (n : nat) (i : nat) (i' : nat) (n' : nat) (f : A -> nat) (x : nat -> A) (h1 : term1031 A n i i' n' f x) : term1062 A n' _7422 f x _7423.
Proof. exact (@lem345583 A _7422 n i i' n' f x h1 _7423). Qed.
Lemma lem345585 {A : Type'} (n' : nat) (_7422 : nat) (f : A -> nat) (x : nat -> A) (_7423 : nat) : (term1062 A n' _7422 f x _7423) = (term1054 A n' _7422 f x _7423).
Proof. exact (eq_refl (term1062 A n' _7422 f x _7423)). Qed.
Lemma lem345620 {A : Type'} (_7435 : nat) (m : nat -> nat) (f : A -> nat) (x : nat -> A) (i'' : nat -> nat) (h1 : term1021 A m f x i'') : term1063 A f x _7435.
Proof. exact (@lem345495 A m f x i'' h1 _7435). Qed.
Lemma lem345621 {A : Type'} (_7435 : nat) (f : A -> nat) (x : nat -> A) : (term1063 A f x _7435) = (term1013 A _7435 f x).
Proof. exact (eq_refl (term1063 A f x _7435)). Qed.
Lemma lem345622 {A : Type'} (_7435 : nat) (m : nat -> nat) (f : A -> nat) (x : nat -> A) (i'' : nat -> nat) (h1 : term1021 A m f x i'') : term1013 A _7435 f x.
Proof. exact (EQ_MP (@lem345621 A _7435 f x) (@lem345620 A _7435 m f x i'' h1)). Qed.
Lemma lem345623 {A : Type'} (_7435 : nat) (_7436 : nat) (m : nat -> nat) (f : A -> nat) (x : nat -> A) (i'' : nat -> nat) (h1 : term1021 A m f x i'') : term1048 A _7435 f x _7436.
Proof. exact (@lem345622 A _7435 m f x i'' h1 _7436). Qed.
Lemma lem345624 {A : Type'} (_7435 : nat) (f : A -> nat) (x : nat -> A) (_7436 : nat) : (term1048 A _7435 f x _7436) = (term1011 A _7435 f x _7436).
Proof. exact (eq_refl (term1048 A _7435 f x _7436)). Qed.
Lemma lem345655 {A : Type'} (n : nat) (i : nat) (i' : nat) (n' : nat) (f : A -> nat) (x : nat -> A) (h1 : term1031 A n i i' n' f x) : n' = (term1010 A f x i').
Proof. exact (proj1 (@lem345042 A n i i' n' f x h1)). Qed.
Lemma lem345661 {A : Type'} (_7422 : nat) (_7423 : nat) (n : nat) (i : nat) (i' : nat) (n' : nat) (f : A -> nat) (x : nat -> A) (h1 : term1031 A n i i' n' f x) : term1054 A n' _7422 f x _7423.
Proof. exact (EQ_MP (@lem345585 A n' _7422 f x _7423) (@lem345584 A _7422 _7423 n i i' n' f x h1)). Qed.
Lemma lem345695 {A : Type'} (_7435 : nat) (_7436 : nat) (m : nat -> nat) (f : A -> nat) (x : nat -> A) (i'' : nat -> nat) (h1 : term1021 A m f x i'') : term1011 A _7435 f x _7436.
Proof. exact (EQ_MP (@lem345624 A _7435 f x _7436) (@lem345623 A _7435 _7436 m f x i'' h1)). Qed.
Lemma lem345824 {A : Type'} (_7422 : nat) (f : A -> nat) (x : nat -> A) (_7423 : nat) : (term1064 A _7422 f x _7423) = (term1064 A _7422 f x _7423).
Proof. exact (eq_refl (term1064 A _7422 f x _7423)). Qed.
Lemma lem345825 {A : Type'} (_7422 : nat) (_7423 : nat) (n : nat) (i : nat) (i' : nat) (n' : nat) (f : A -> nat) (x : nat -> A) (h1 : term1031 A n i i' n' f x) : (term1065 A _7422 f x _7423 n') = (term1066 A _7422 _7423 f x i').
Proof. exact (MK_COMB (@lem345824 A _7422 f x _7423) (@lem345655 A n i i' n' f x h1)). Qed.
Lemma lem345826 {A : Type'} (i' : nat) (_7422 : nat) (f : A -> nat) (x : nat -> A) (_7423 : nat) : (term1066 A _7422 _7423 f x i') = (term1067 A i' _7422 f x _7423).
Proof. exact (eq_refl (term1066 A _7422 _7423 f x i')). Qed.
Lemma lem345827 {A : Type'} (_7422 : nat) (f : A -> nat) (x : nat -> A) (_7423 : nat) (n' : nat) : (term1068 A _7422 f x _7423 n') = (term1068 A _7422 f x _7423 n').
Proof. exact (eq_refl (term1068 A _7422 f x _7423 n')). Qed.
Lemma lem345828 {A : Type'} (n' : nat) (i' : nat) (_7422 : nat) (f : A -> nat) (x : nat -> A) (_7423 : nat) : ((term1065 A _7422 f x _7423 n') = (term1066 A _7422 _7423 f x i')) = ((term1065 A _7422 f x _7423 n') = (term1067 A i' _7422 f x _7423)).
Proof. exact (MK_COMB (@lem345827 A _7422 f x _7423 n') (@lem345826 A i' _7422 f x _7423)). Qed.
Lemma lem345829 {A : Type'} (n' : nat) (_7422 : nat) (f : A -> nat) (x : nat -> A) (_7423 : nat) : (term1065 A _7422 f x _7423 n') = (term1054 A n' _7422 f x _7423).
Proof. exact (eq_refl (term1065 A _7422 f x _7423 n')). Qed.
Lemma lem345830 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem345831 {A : Type'} (n' : nat) (_7422 : nat) (f : A -> nat) (x : nat -> A) (_7423 : nat) : (term1068 A _7422 f x _7423 n') = (term1069 A n' _7422 f x _7423).
Proof. exact (MK_COMB (@lem345830) (@lem345829 A n' _7422 f x _7423)). Qed.
Lemma lem345832 {A : Type'} (i' : nat) (_7422 : nat) (f : A -> nat) (x : nat -> A) (_7423 : nat) : (term1067 A i' _7422 f x _7423) = (term1067 A i' _7422 f x _7423).
Proof. exact (eq_refl (term1067 A i' _7422 f x _7423)). Qed.
Lemma lem345833 {A : Type'} (n' : nat) (i' : nat) (_7422 : nat) (f : A -> nat) (x : nat -> A) (_7423 : nat) : ((term1065 A _7422 f x _7423 n') = (term1067 A i' _7422 f x _7423)) = ((term1054 A n' _7422 f x _7423) = (term1067 A i' _7422 f x _7423)).
Proof. exact (MK_COMB (@lem345831 A n' _7422 f x _7423) (@lem345832 A i' _7422 f x _7423)). Qed.
Lemma lem345834 {A : Type'} (n' : nat) (i' : nat) (_7422 : nat) (f : A -> nat) (x : nat -> A) (_7423 : nat) : ((term1065 A _7422 f x _7423 n') = (term1066 A _7422 _7423 f x i')) = ((term1054 A n' _7422 f x _7423) = (term1067 A i' _7422 f x _7423)).
Proof. exact (TRANS (@lem345828 A n' i' _7422 f x _7423) (@lem345833 A n' i' _7422 f x _7423)). Qed.
Lemma lem345835 {A : Type'} (_7422 : nat) (_7423 : nat) (n : nat) (i : nat) (i' : nat) (n' : nat) (f : A -> nat) (x : nat -> A) (h1 : term1031 A n i i' n' f x) : (term1054 A n' _7422 f x _7423) = (term1067 A i' _7422 f x _7423).
Proof. exact (EQ_MP (@lem345834 A n' i' _7422 f x _7423) (@lem345825 A _7422 _7423 n i i' n' f x h1)). Qed.
Lemma lem345962 {A : Type'} (_7422 : nat) (_7423 : nat) (n : nat) (i : nat) (i' : nat) (n' : nat) (f : A -> nat) (x : nat -> A) (h1 : term1031 A n i i' n' f x) : term1067 A i' _7422 f x _7423.
Proof. exact (EQ_MP (@lem345835 A _7422 _7423 n i i' n' f x h1) (@lem345661 A _7422 _7423 n i i' n' f x h1)). Qed.
Lemma lem346208 {A : Type'} (_7417 : nat) (k : nat -> nat) (f : A -> nat) (x : nat -> A) (h1 : term636 A k f x) : term1039 A k f x _7417.
Proof. exact (EQ_MP (@lem345567 A k f x _7417) (@lem345566 A _7417 k f x h1)). Qed.
Lemma lem346209 {A : Type'} (i' : nat) (k : nat -> nat) (f : A -> nat) (x : nat -> A) (h1 : term636 A k f x) : term1039 A k f x i'.
Proof. exact (@lem346208 A i' k f x h1). Qed.
Lemma lem346210 {A : Type'} (i' : nat) (k : nat -> nat) (f : A -> nat) (x : nat -> A) (h1 : term636 A k f x) : term1070 A k f x i'.
Proof. exact (fun h0 : term1071 A k f x i' => @lem346209 A i' k f x h1). Qed.
Lemma lem346212 (p : Prop) : (term287 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem346213 {A : Type'} (k : nat -> nat) (f : A -> nat) (x : nat -> A) (i' : nat) : (term1070 A k f x i') = (term1039 A k f x i').
Proof. exact (@lem346212 (term1039 A k f x i')). Qed.
Lemma lem346214 {A : Type'} (i' : nat) (k : nat -> nat) (f : A -> nat) (x : nat -> A) (h1 : term636 A k f x) : term1039 A k f x i'.
Proof. exact (EQ_MP (@lem346213 A k f x i') (@lem346210 A i' k f x h1)). Qed.
Lemma lem346216 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem346217 {A : Type'} (f : A -> nat) (x : nat -> A) (k : nat -> nat) (i' : nat) : (term995 A f x k i') = (term995 A f x k i').
Proof. exact (@lem346216 (term995 A f x k i')). Qed.
Lemma lem346218 {A : Type'} (f : A -> nat) (x : nat -> A) (k : nat -> nat) (i' : nat) : term1072 A f x k i'.
Proof. exact (fun h0 : term1073 A f x k i' => @lem346217 A f x k i'). Qed.
Lemma lem346220 (p : Prop) : (term287 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem346221 {A : Type'} (f : A -> nat) (x : nat -> A) (k : nat -> nat) (i' : nat) : (term1072 A f x k i') = ((term995 A f x k i') = (term995 A f x k i')).
Proof. exact (@lem346220 ((term995 A f x k i') = (term995 A f x k i'))). Qed.
Lemma lem346222 {A : Type'} (f : A -> nat) (x : nat -> A) (k : nat -> nat) (i' : nat) : (term995 A f x k i') = (term995 A f x k i').
Proof. exact (EQ_MP (@lem346221 A f x k i') (@lem346218 A f x k i')). Qed.
Lemma lem346224 (a : Prop) (b : Prop) : (term1074 a b) = (term1075 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem346225 {A : Type'} (i' : nat) (_7422 : nat) (f : A -> nat) (x : nat -> A) (_7423 : nat) : (term1067 A i' _7422 f x _7423) = (term1076 A i' _7422 f x _7423).
Proof. exact (@lem346224 (term1077 A _7422 f x i') (_7422 = (term1010 A f x _7423))). Qed.
Lemma lem346227 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem346228 {A : Type'} (i' : nat) (_7422 : nat) (f : A -> nat) (x : nat -> A) (_7423 : nat) : (term1076 A i' _7422 f x _7423) = (term1078 A i' _7422 f x _7423).
Proof. exact (@lem346227 (term1079 A i' _7422 f x _7423)). Qed.
Lemma lem346229 {A : Type'} (i' : nat) (_7422 : nat) (f : A -> nat) (x : nat -> A) (_7423 : nat) : (term1067 A i' _7422 f x _7423) = (term1078 A i' _7422 f x _7423).
Proof. exact (TRANS (@lem346225 A i' _7422 f x _7423) (@lem346228 A i' _7422 f x _7423)). Qed.
Lemma lem346231 {A : Type'} (i' : nat) (k : nat -> nat) (f : A -> nat) (x : nat -> A) (h1 : term636 A k f x) : term1080 A f x k i'.
Proof. exact (conj (@lem346214 A i' k f x h1) (@lem346222 A f x k i')). Qed.
Lemma lem346233 {A : Type'} (_7422 : nat) (_7423 : nat) (n : nat) (i : nat) (i' : nat) (n' : nat) (f : A -> nat) (x : nat -> A) (h1 : term1031 A n i i' n' f x) : term1078 A i' _7422 f x _7423.
Proof. exact (EQ_MP (@lem346229 A i' _7422 f x _7423) (@lem345962 A _7422 _7423 n i i' n' f x h1)). Qed.
Lemma lem346234 {A : Type'} (k : nat -> nat) (n : nat) (i : nat) (i' : nat) (n' : nat) (f : A -> nat) (x : nat -> A) (h1 : term1031 A n i i' n' f x) : term1081 A f x k i'.
Proof. exact (@lem346233 A (term995 A f x k i') (@I (nat -> nat) k i') n i i' n' f x h1). Qed.
Lemma lem346237 {A : Type'} (k : nat -> nat) (n : nat) (i : nat) (i' : nat) (n' : nat) (f : A -> nat) (x : nat -> A) (h1 : term636 A k f x) (h2 : term1031 A n i i' n' f x) : False.
Proof. exact (@lem346234 A k n i i' n' f x h2 (@lem346231 A i' k f x h1)). Qed.
Lemma lem346238 {A : Type'} (k : nat -> nat) (n : nat) (i : nat) (i' : nat) (n' : nat) (f : A -> nat) (x : nat -> A) (h1 : term636 A k f x) (h2 : term1031 A n i i' n' f x) : term290.
Proof. exact (fun h0 : ~ False => @lem346237 A k n i i' n' f x h1 h2). Qed.
Lemma lem346240 (p : Prop) : (term287 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem346241 : term290 = False.
Proof. exact (@lem346240 False). Qed.
Lemma lem346460 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem346461 {A : Type'} (f : A -> nat) (x : nat -> A) (_7573 : nat) : (term1010 A f x _7573) = (term1010 A f x _7573).
Proof. exact (@lem346460 (term1010 A f x _7573)). Qed.
Lemma lem346462 {A : Type'} (f : A -> nat) (x : nat -> A) (_7573 : nat) : term1082 A f x _7573.
Proof. exact (fun h0 : term1083 A f x _7573 => @lem346461 A f x _7573). Qed.
Lemma lem346464 (p : Prop) : (term287 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem346465 {A : Type'} (f : A -> nat) (x : nat -> A) (_7573 : nat) : (term1082 A f x _7573) = ((term1010 A f x _7573) = (term1010 A f x _7573)).
Proof. exact (@lem346464 ((term1010 A f x _7573) = (term1010 A f x _7573))). Qed.
Lemma lem346466 {A : Type'} (f : A -> nat) (x : nat -> A) (_7573 : nat) : (term1010 A f x _7573) = (term1010 A f x _7573).
Proof. exact (EQ_MP (@lem346465 A f x _7573) (@lem346462 A f x _7573)). Qed.
Lemma lem346469 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem346471 {A : Type'} (_7435 : nat) (f : A -> nat) (x : nat -> A) (_7436 : nat) : (term1011 A _7435 f x _7436) = (term1084 A _7435 f x _7436).
Proof. exact (@lem346469 (_7435 = (term1010 A f x _7436))). Qed.
Lemma lem346474 {A : Type'} (_7435 : nat) (_7436 : nat) (m : nat -> nat) (f : A -> nat) (x : nat -> A) (i'' : nat -> nat) (h1 : term1021 A m f x i'') : term1084 A _7435 f x _7436.
Proof. exact (EQ_MP (@lem346471 A _7435 f x _7436) (@lem345695 A _7435 _7436 m f x i'' h1)). Qed.
Lemma lem346475 {A : Type'} (_7573 : nat) (m : nat -> nat) (f : A -> nat) (x : nat -> A) (i'' : nat -> nat) (h1 : term1021 A m f x i'') : term1085 A f x _7573.
Proof. exact (@lem346474 A (term1010 A f x _7573) _7573 m f x i'' h1). Qed.
Lemma lem346478 {A : Type'} (m : nat -> nat) (f : A -> nat) (x : nat -> A) (i'' : nat -> nat) (h1 : term1021 A m f x i'') : False.
Proof. exact (@lem346475 A (@el nat) m f x i'' h1 (@lem346466 A f x (@el nat))). Qed.
Lemma lem346479 {A : Type'} (m : nat -> nat) (f : A -> nat) (x : nat -> A) (i'' : nat -> nat) (h1 : term1021 A m f x i'') : term290.
Proof. exact (fun h0 : ~ False => @lem346478 A m f x i'' h1). Qed.
Lemma lem346481 (p : Prop) : (term287 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem346482 : term290 = False.
Proof. exact (@lem346481 False). Qed.
Lemma lem346483 {A : Type'} (m : nat -> nat) (f : A -> nat) (x : nat -> A) (i'' : nat -> nat) (h1 : term1021 A m f x i'') : False.
Proof. exact (EQ_MP (@lem346482) (@lem346479 A m f x i'' h1)). Qed.
Lemma lem346485 {A : Type'} (k : nat -> nat) (n : nat) (i : nat) (i' : nat) (n' : nat) (f : A -> nat) (x : nat -> A) (h1 : term636 A k f x) (h2 : term1031 A n i i' n' f x) : False.
Proof. exact (EQ_MP (@lem346241) (@lem346238 A k n i i' n' f x h1 h2)). Qed.
Lemma lem346486 {A : Type'} (k : nat -> nat) (n : nat) (i : nat) (i' : nat) (n' : nat) (m : nat -> nat) (f : A -> nat) (x : nat -> A) (i'' : nat -> nat) (h1 : term636 A k f x) (h2 : term976 A n i i' n' m f x i'') : False.
Proof. exact (or_elim (@lem344748 A n i i' n' m f x i'' h2) (fun h0 : term1031 A n i i' n' f x => @lem346485 A k n i i' n' f x h1 h0) (fun h0 : term1021 A m f x i'' => @lem346483 A m f x i'' h0)). Qed.
Lemma lem346487 {A : Type'} (k : nat -> nat) (lt2 : type1402 A) (g : type184 A) (f' : type184 A) (n : nat) (i : nat) (i' : nat) (n' : nat) (m : nat -> nat) (f : A -> nat) (x : nat -> A) (i'' : nat -> nat) (h1 : term636 A k f x) (h2 : term249 A lt2 g f') (h3 : term976 A n i i' n' m f x i'') : False.
Proof. exact (ex_elim (@lem344314 A lt2 g f' h2) (fun x' : type185 A => fun h0 : term248 A lt2 g f' x' => @lem346486 A k n i i' n' m f x i'' h1 h3)). Qed.
Lemma lem346488 {A : Type'} (k : nat -> nat) (lt2 : type1402 A) (f' : type184 A) (n : nat) (i : nat) (i' : nat) (n' : nat) (m : nat -> nat) (f : A -> nat) (x : nat -> A) (i'' : nat -> nat) (h1 : term636 A k f x) (h2 : term251 A lt2 f') (h3 : term976 A n i i' n' m f x i'') : False.
Proof. exact (ex_elim (@lem344313 A lt2 f' h2) (fun g : type184 A => fun h0 : term250 A lt2 f' g => @lem346487 A k lt2 g f' n i i' n' m f x i'' h1 h0 h3)). Qed.
Lemma lem346489 {A : Type'} (lt2 : type1402 A) (k : nat -> nat) (n : nat) (i : nat) (i' : nat) (n' : nat) (m : nat -> nat) (f : A -> nat) (x : nat -> A) (i'' : nat -> nat) (h1 : term15 A lt2) (h2 : term636 A k f x) (h3 : term976 A n i i' n' m f x i'') : False.
Proof. exact (ex_elim (@lem343352 A lt2 h1) (fun f' : type184 A => fun h0 : term252 A lt2 f' => @lem346488 A k lt2 f' n i i' n' m f x i'' h2 h0 h3)). Qed.
Lemma lem346490 {A : Type'} (lt2 : type1402 A) (k : nat -> nat) (n : nat) (i : nat) (i' : nat) (n' : nat) (m : nat -> nat) (f : A -> nat) (x : nat -> A) (i'' : nat -> nat) (h1 : term15 A lt2) (h2 : term29 A lt2 x) (h3 : term636 A k f x) (h4 : term976 A n i i' n' m f x i'') : False.
Proof. exact (ex_elim (@lem343414 A lt2 x h2) (fun m' : nat -> nat => fun h0 : term617 A lt2 x m' => @lem346489 A lt2 k n i i' n' m f x i'' h1 h3 h4)). Qed.
Lemma lem346491 {A : Type'} (lt2 : type1402 A) (n : nat) (i : nat) (i' : nat) (n' : nat) (m : nat -> nat) (f : A -> nat) (x : nat -> A) (i'' : nat -> nat) (h1 : term15 A lt2) (h2 : term450 A f x) (h3 : term29 A lt2 x) (h4 : term976 A n i i' n' m f x i'') : False.
Proof. exact (ex_elim (@lem343476 A f x h2) (fun k : nat -> nat => fun h0 : term638 A f x k => @lem346490 A lt2 k n i i' n' m f x i'' h1 h3 h0 h4)). Qed.
Lemma lem346492 {A : Type'} (lt2 : type1402 A) (n : nat) (i : nat) (i' : nat) (n' : nat) (m : nat -> nat) (f : A -> nat) (x : nat -> A) (h1 : term15 A lt2) (h2 : term450 A f x) (h3 : term29 A lt2 x) (h4 : term979 A n i i' n' m f x) : False.
Proof. exact (ex_elim (@lem344309 A n i i' n' m f x h4) (fun i'' : nat -> nat => fun h0 : term978 A n i i' n' m f x i'' => @lem346491 A lt2 n i i' n' m f x i'' h1 h2 h3 h0)). Qed.
Lemma lem346493 {A : Type'} (lt2 : type1402 A) (n : nat) (i : nat) (i' : nat) (n' : nat) (f : A -> nat) (x : nat -> A) (h1 : term15 A lt2) (h2 : term450 A f x) (h3 : term29 A lt2 x) (h4 : term981 A n i i' n' f x) : False.
Proof. exact (ex_elim (@lem344308 A n i i' n' f x h4) (fun m : nat -> nat => fun h0 : term980 A n i i' n' f x m => @lem346492 A lt2 n i i' n' m f x h1 h2 h3 h0)). Qed.
Lemma lem346494 {A : Type'} (lt2 : type1402 A) (n : nat) (i : nat) (n' : nat) (f : A -> nat) (x : nat -> A) (h1 : term15 A lt2) (h2 : term450 A f x) (h3 : term29 A lt2 x) (h4 : term983 A n i n' f x) : False.
Proof. exact (ex_elim (@lem344307 A n i n' f x h4) (fun i' : nat => fun h0 : term982 A n i n' f x i' => @lem346493 A lt2 n i i' n' f x h1 h2 h3 h0)). Qed.
Lemma lem346495 {A : Type'} (lt2 : type1402 A) (n : nat) (i : nat) (f : A -> nat) (x : nat -> A) (h1 : term15 A lt2) (h2 : term450 A f x) (h3 : term29 A lt2 x) (h4 : term985 A n i f x) : False.
Proof. exact (ex_elim (@lem344306 A n i f x h4) (fun n' : nat => fun h0 : term984 A n i f x n' => @lem346494 A lt2 n i n' f x h1 h2 h3 h0)). Qed.
Lemma lem346496 {A : Type'} (lt2 : type1402 A) (n : nat) (f : A -> nat) (x : nat -> A) (h1 : term15 A lt2) (h2 : term450 A f x) (h3 : term29 A lt2 x) (h4 : term987 A n f x) : False.
Proof. exact (ex_elim (@lem344305 A n f x h4) (fun i : nat => fun h0 : term986 A n f x i => @lem346495 A lt2 n i f x h1 h2 h3 h0)). Qed.
Lemma lem346497 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (x : nat -> A) (h1 : term15 A lt2) (h2 : term450 A f x) (h3 : term29 A lt2 x) (h4 : (term471 A f x) = (term489 A f x)) : False.
Proof. exact (ex_elim (@lem344304 A f x h4) (fun n : nat => fun h0 : term988 A f x n => @lem346496 A lt2 n f x h1 h2 h3 h0)). Qed.
Lemma lem346498 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (h1 : term15 A lt2) (h2 : term450 A f x) (h3 : term29 A lt2 x) : term571 A f x.
Proof. exact (fun h0 : (term471 A f x) = (term489 A f x) => @lem346497 A lt2 f x h1 h2 h3 h0). Qed.
Lemma lem346499 {A : Type'} (f : A -> nat) (x : nat -> A) : (term571 A f x) = (term490 A f x).
Proof. exact (@lem69 ((term471 A f x) = (term489 A f x))). Qed.
Lemma lem346500 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (h1 : term15 A lt2) (h2 : term450 A f x) (h3 : term29 A lt2 x) : term490 A f x.
Proof. exact (EQ_MP (@lem346499 A f x) (@lem346498 A f lt2 x h1 h2 h3)). Qed.
Lemma lem346501 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (h1 : term15 A lt2) (h2 : term29 A lt2 x) : term573 A f x.
Proof. exact (fun h0 : term450 A f x => @lem346500 A f lt2 x h1 h0 h2). Qed.
Lemma lem346502 {A : Type'} (_7410 : type414 A) (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (h1 : term15 A lt2) (h2 : term29 A lt2 x) : term574 A _7410 lt2 f x.
Proof. exact (fun h0 : term550 A f _7410 lt2 x => @lem346501 A f lt2 x h1 h2). Qed.
Lemma lem346503 {A : Type'} (_7410 : type414 A) (f : A -> nat) (x : nat -> A) (lt2 : type1402 A) (h1 : term15 A lt2) : term575 A _7410 lt2 f x.
Proof. exact (fun h0 : term29 A lt2 x => @lem346502 A _7410 f lt2 x h1 h0). Qed.
Lemma lem346504 {A : Type'} (_7410 : type414 A) (f : A -> nat) (x : nat -> A) (lt2 : type1402 A) (h1 : term15 A lt2) : term576 A _7410 lt2 f x.
Proof. exact (fun h0 : term18 A lt2 x => @lem346503 A _7410 f x lt2 h1). Qed.
Lemma lem346505 {A : Type'} (_7410 : type414 A) (lt2 : type1402 A) (f : A -> nat) (x : nat -> A) : term577 A _7410 lt2 f x.
Proof. exact (fun h0 : term15 A lt2 => @lem346504 A _7410 f x lt2 h0). Qed.
Lemma lem346506 {A : Type'} (_7410 : type414 A) (lt2 : type1402 A) (f : A -> nat) (x : nat -> A) : term578 A _7410 lt2 f x.
Proof. exact (fun h0 : term544 A _7410 => @lem346505 A _7410 lt2 f x). Qed.
Lemma lem346511 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (x : nat -> A) : term581 A lt2 f x.
Proof. exact (fun _7410 : type414 A => @lem346506 A _7410 lt2 f x). Qed.
Lemma lem346516 {A : Type'} (f : A -> nat) (x : nat -> A) : term585 A f x.
Proof. exact (fun lt2 : type1402 A => @lem346511 A lt2 f x). Qed.
Lemma lem346521 {A : Type'} (x : nat -> A) : term589 A x.
Proof. exact (fun f : A -> nat => @lem346516 A f x). Qed.
Lemma lem346526 {A : Type'} : term593 A.
Proof. exact (fun x : nat -> A => @lem346521 A x). Qed.
Lemma lem346527 {A : Type'} : term592 A.
Proof. exact (EQ_MP (@lem342787 A) (@lem346526 A)). Qed.
Lemma lem346528 {A : Type'} (x : nat -> A) : term1086 A x.
Proof. exact (@lem346527 A x). Qed.
Lemma lem346529 {A : Type'} (x : nat -> A) : (term1086 A x) = (term588 A x).
Proof. exact (eq_refl (term1086 A x)). Qed.
Lemma lem346530 {A : Type'} (x : nat -> A) : term588 A x.
Proof. exact (EQ_MP (@lem346529 A x) (@lem346528 A x)). Qed.
Lemma lem346531 {A : Type'} (x : nat -> A) (f : A -> nat) : term1087 A x f.
Proof. exact (@lem346530 A x f). Qed.
Lemma lem346532 {A : Type'} (f : A -> nat) (x : nat -> A) : (term1087 A x f) = (term584 A f x).
Proof. exact (eq_refl (term1087 A x f)). Qed.
Lemma lem346533 {A : Type'} (f : A -> nat) (x : nat -> A) : term584 A f x.
Proof. exact (EQ_MP (@lem346532 A f x) (@lem346531 A x f)). Qed.
Lemma lem346534 {A : Type'} (f : A -> nat) (x : nat -> A) (lt2 : type1402 A) : term1088 A f x lt2.
Proof. exact (@lem346533 A f x lt2). Qed.
Lemma lem346535 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (x : nat -> A) : (term1088 A f x lt2) = (term559 A lt2 f x).
Proof. exact (eq_refl (term1088 A f x lt2)). Qed.
Lemma lem346536 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (x : nat -> A) : term559 A lt2 f x.
Proof. exact (EQ_MP (@lem346535 A lt2 f x) (@lem346534 A f x lt2)). Qed.
Lemma lem346537 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (x : nat -> A) : term499 A lt2 f x.
Proof. exact (@lem342224 A lt2 f x (@lem346536 A lt2 f x)). Qed.
Lemma lem346538 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (x : nat -> A) : term498 A lt2 f x.
Proof. exact (EQ_MP (@lem342096 A lt2 f x) (@lem346537 A lt2 f x)). Qed.
Lemma lem346539 {A : Type'} (f : A -> nat) (x : nat -> A) (lt2 : type1402 A) (h1 : term15 A lt2) : term496 A lt2 f x.
Proof. exact (@lem346538 A lt2 f x (@lem339366 A lt2 h1)). Qed.
Lemma lem346540 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (h1 : term15 A lt2) (h2 : term18 A lt2 x) : term494 A lt2 f x.
Proof. exact (@lem346539 A f x lt2 h1 (@lem339380 A lt2 x h2)). Qed.
Lemma lem346541 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (h1 : term15 A lt2) (h2 : term19 A lt2 x) (h3 : term18 A lt2 x) : term493 A lt2 f x.
Proof. exact (@lem346540 A f lt2 x h1 h3 (@lem339381 A lt2 x h2)). Qed.
Lemma lem346542 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (h1 : term15 A lt2) (h2 : term421 A f lt2 x) (h3 : term19 A lt2 x) (h4 : term18 A lt2 x) : term553 A f x.
Proof. exact (@lem346541 A f lt2 x h1 h3 h4 (@lem341454 A f lt2 x h2)). Qed.
Lemma lem346543 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (h1 : term15 A lt2) (h2 : term450 A f x) (h3 : term421 A f lt2 x) (h4 : term19 A lt2 x) (h5 : term18 A lt2 x) : term571 A f x.
Proof. exact (@lem346542 A f lt2 x h1 h3 h4 h5 (@lem341455 A f x h2)). Qed.
Lemma lem346544 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (x : nat -> A) (h1 : term15 A lt2) (h2 : term450 A f x) (h3 : term421 A f lt2 x) (h4 : term19 A lt2 x) (h5 : term18 A lt2 x) (h6 : (term471 A f x) = (term489 A f x)) : False.
Proof. exact (@lem346543 A f lt2 x h1 h2 h3 h4 h5 (@lem341612 A f x h6)). Qed.
Lemma lem346545 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (x : nat -> A) (h1 : term15 A lt2) (h2 : term450 A f x) (h3 : term421 A f lt2 x) (h4 : term19 A lt2 x) (h5 : term18 A lt2 x) (h6 : (term471 A f x) = (term489 A f x)) : ((term471 A f x) = (term489 A f x)) = False.
Proof. exact (prop_ext (fun h7 : (term471 A f x) = (term489 A f x) => @lem346544 A lt2 f x h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem341612 A f x h6)). Qed.
Lemma lem346546 {A : Type'} (lt2 : type1402 A) (f : A -> nat) (x : nat -> A) (h1 : term15 A lt2) (h2 : term450 A f x) (h3 : term421 A f lt2 x) (h4 : term19 A lt2 x) (h5 : term18 A lt2 x) (h6 : (term471 A f x) = (term489 A f x)) : False.
Proof. exact (EQ_MP (@lem346545 A lt2 f x h1 h2 h3 h4 h5 h6) (@lem341612 A f x h6)). Qed.
Lemma lem346547 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (h1 : term15 A lt2) (h2 : term450 A f x) (h3 : term421 A f lt2 x) (h4 : term19 A lt2 x) (h5 : term18 A lt2 x) : term571 A f x.
Proof. exact (fun h0 : (term471 A f x) = (term489 A f x) => @lem346546 A lt2 f x h1 h2 h3 h4 h5 h0). Qed.
Lemma lem346548 {A : Type'} (f : A -> nat) (x : nat -> A) : (term571 A f x) = (term490 A f x).
Proof. exact (@lem69 ((term471 A f x) = (term489 A f x))). Qed.
Lemma lem346549 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (h1 : term15 A lt2) (h2 : term450 A f x) (h3 : term421 A f lt2 x) (h4 : term19 A lt2 x) (h5 : term18 A lt2 x) : term490 A f x.
Proof. exact (EQ_MP (@lem346548 A f x) (@lem346547 A f lt2 x h1 h2 h3 h4 h5)). Qed.
Lemma lem346550 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (h1 : term15 A lt2) (h2 : term450 A f x) (h3 : term421 A f lt2 x) (h4 : term19 A lt2 x) (h5 : term18 A lt2 x) : term462 A f x.
Proof. exact (EQ_MP (@lem341611 A f x) (@lem346549 A f lt2 x h1 h2 h3 h4 h5)). Qed.
Lemma lem346551 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (h1 : term15 A lt2) (h2 : term450 A f x) (h3 : term421 A f lt2 x) (h4 : term19 A lt2 x) (h5 : term18 A lt2 x) : False.
Proof. exact (@lem346550 A f lt2 x h1 h2 h3 h4 h5 (@lem339328 A f x)). Qed.
Lemma lem346552 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (h1 : term15 A lt2) (h2 : term450 A f x) (h3 : term421 A f lt2 x) (h4 : term19 A lt2 x) (h5 : term18 A lt2 x) : (term450 A f x) = False.
Proof. exact (prop_ext (fun h6 : term450 A f x => @lem346551 A f lt2 x h1 h2 h3 h4 h5) (fun h6 : False => @lem341455 A f x h2)). Qed.
Lemma lem346553 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (h1 : term15 A lt2) (h2 : term450 A f x) (h3 : term421 A f lt2 x) (h4 : term19 A lt2 x) (h5 : term18 A lt2 x) : False.
Proof. exact (EQ_MP (@lem346552 A f lt2 x h1 h2 h3 h4 h5) (@lem341455 A f x h2)). Qed.
Lemma lem346554 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (h1 : term15 A lt2) (h2 : term421 A f lt2 x) (h3 : term19 A lt2 x) (h4 : term18 A lt2 x) : (term450 A f x) = False.
Proof. exact (prop_ext (fun h5 : term450 A f x => @lem346553 A f lt2 x h1 h5 h2 h3 h4) (fun h5 : False => @lem341490 A f lt2 x h2)). Qed.
Lemma lem346555 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (h1 : term15 A lt2) (h2 : term421 A f lt2 x) (h3 : term19 A lt2 x) (h4 : term18 A lt2 x) : False.
Proof. exact (EQ_MP (@lem346554 A f lt2 x h1 h2 h3 h4) (@lem341490 A f lt2 x h2)). Qed.
Lemma lem346556 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (h1 : term15 A lt2) (h2 : term19 A lt2 x) (h3 : term18 A lt2 x) : term1089 A f lt2 x.
Proof. exact (fun h0 : term421 A f lt2 x => @lem346555 A f lt2 x h1 h0 h2 h3). Qed.
Lemma lem346557 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) : (term1089 A f lt2 x) = (term422 A f lt2 x).
Proof. exact (@lem69 (term421 A f lt2 x)). Qed.
Lemma lem346558 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (h1 : term15 A lt2) (h2 : term19 A lt2 x) (h3 : term18 A lt2 x) : term422 A f lt2 x.
Proof. exact (EQ_MP (@lem346557 A f lt2 x) (@lem346556 A f lt2 x h1 h2 h3)). Qed.
Lemma lem346559 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (h1 : term15 A lt2) (h2 : term409 A x) (h3 : term19 A lt2 x) (h4 : term18 A lt2 x) : term412 A f lt2 x.
Proof. exact (EQ_MP (@lem341256 A f lt2 x h2) (@lem346558 A f lt2 x h1 h3 h4)). Qed.
Lemma lem346560 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (h1 : term15 A lt2) (h2 : term19 A lt2 x) (h3 : term18 A lt2 x) : (term409 A x) = (term412 A f lt2 x).
Proof. exact (prop_ext (fun h4 : term409 A x => @lem346559 A f lt2 x h1 h4 h2 h3) (fun h4 : term412 A f lt2 x => @lem341453 A x)). Qed.
Lemma lem346561 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (h1 : term15 A lt2) (h2 : term19 A lt2 x) (h3 : term18 A lt2 x) : term412 A f lt2 x.
Proof. exact (EQ_MP (@lem346560 A f lt2 x h1 h2 h3) (@lem341453 A x)). Qed.
Lemma lem346562 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (h1 : term338 A f lt2 x) (h2 : term15 A lt2) (h3 : term19 A lt2 x) (h4 : term18 A lt2 x) : False.
Proof. exact (@lem346561 A f lt2 x h2 h3 h4 (@lem341213 A f lt2 x h1)). Qed.
Lemma lem346563 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (h1 : term15 A lt2) (h2 : term19 A lt2 x) (h3 : term18 A lt2 x) : term1090 A f lt2 x.
Proof. exact (fun h0 : term338 A f lt2 x => @lem346562 A f lt2 x h0 h1 h2 h3). Qed.
Lemma lem346564 {A : Type'} (f : A -> nat) (lt2 : type1402 A) (x : nat -> A) (h1 : term338 A f lt2 x) (h2 : term15 A lt2) (h3 : term19 A lt2 x) (h4 : term18 A lt2 x) : False.
Proof. exact (@lem346563 A f lt2 x h2 h3 h4 (@lem341208 A f lt2 x h1)). Qed.
Lemma lem346565 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (h1 : term15 A lt2) (h2 : term19 A lt2 x) (h3 : term18 A lt2 x) (h4 : term341 A lt2 x) : False.
Proof. exact (ex_elim (@lem341207 A lt2 x h4) (fun f : A -> nat => fun h0 : term340 A lt2 x f => @lem346564 A f lt2 x h0 h1 h2 h3)). Qed.
Lemma lem346566 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (h1 : term15 A lt2) (h2 : term19 A lt2 x) (h3 : term18 A lt2 x) : term1091 A lt2 x.
Proof. exact (fun h0 : term341 A lt2 x => @lem346565 A lt2 x h1 h2 h3 h0). Qed.
Lemma lem346567 {A : Type'} (lt2 : type1402 A) (x : nat -> A) : (term1091 A lt2 x) = (term343 A lt2 x).
Proof. exact (@lem69 (term341 A lt2 x)). Qed.
Lemma lem346568 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (h1 : term15 A lt2) (h2 : term19 A lt2 x) (h3 : term18 A lt2 x) : term343 A lt2 x.
Proof. exact (EQ_MP (@lem346567 A lt2 x) (@lem346566 A lt2 x h1 h2 h3)). Qed.
Lemma lem346569 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (h1 : term15 A lt2) (h2 : term19 A lt2 x) (h3 : term18 A lt2 x) : term344 A lt2 x.
Proof. exact (conj (@lem341206 A lt2 x h2) (@lem346568 A lt2 x h1 h2 h3)). Qed.
Lemma lem346570 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (h1 : term15 A lt2) (h2 : term19 A lt2 x) (h3 : term18 A lt2 x) : term296 A lt2 x.
Proof. exact (EQ_MP (@lem340978 A lt2 x) (@lem346569 A lt2 x h1 h2 h3)). Qed.
Lemma lem346571 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (h1 : term15 A lt2) (h2 : term19 A lt2 x) (h3 : term18 A lt2 x) : False.
Proof. exact (@lem346570 A lt2 x h1 h2 h3 (@lem340755 A x lt2 h1)). Qed.
Lemma lem346572 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (h1 : term15 A lt2) (h2 : term19 A lt2 x) (h3 : term18 A lt2 x) : (term19 A lt2 x) = False.
Proof. exact (prop_ext (fun h4 : term19 A lt2 x => @lem346571 A lt2 x h1 h2 h3) (fun h4 : False => @lem339381 A lt2 x h2)). Qed.
Lemma lem346573 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (h1 : term15 A lt2) (h2 : term19 A lt2 x) (h3 : term18 A lt2 x) : False.
Proof. exact (EQ_MP (@lem346572 A lt2 x h1 h2 h3) (@lem339381 A lt2 x h2)). Qed.
Lemma lem346574 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (h1 : term15 A lt2) (h2 : term18 A lt2 x) : (term19 A lt2 x) = False.
Proof. exact (prop_ext (fun h3 : term19 A lt2 x => @lem346573 A lt2 x h1 h3 h2) (fun h3 : False => @lem340752 A lt2 x h1 h2)). Qed.
Lemma lem346575 {A : Type'} (lt2 : type1402 A) (x : nat -> A) (h1 : term15 A lt2) (h2 : term18 A lt2 x) : False.
Proof. exact (EQ_MP (@lem346574 A lt2 x h1 h2) (@lem340752 A lt2 x h1 h2)). Qed.
Lemma lem346576 {A : Type'} (lt2 : type1402 A) (h1 : term15 A lt2) (h2 : term17 A lt2) : False.
Proof. exact (ex_elim (@lem339379 A lt2 h2) (fun x : nat -> A => fun h0 : term1092 A lt2 x => @lem346575 A lt2 x h1 h0)). Qed.
Lemma lem346577 {A : Type'} (lt2 : type1402 A) (h1 : term15 A lt2) : term1093 A lt2.
Proof. exact (fun h0 : term17 A lt2 => @lem346576 A lt2 h1 h0). Qed.
Lemma lem346578 {A : Type'} (lt2 : type1402 A) : (term1093 A lt2) = (term16 A lt2).
Proof. exact (@lem69 (term17 A lt2)). Qed.
Lemma lem346579 {A : Type'} (lt2 : type1402 A) (h1 : term15 A lt2) : term16 A lt2.
Proof. exact (EQ_MP (@lem346578 A lt2) (@lem346577 A lt2 h1)). Qed.
Lemma lem346580 {A : Type'} (lt2 : type1402 A) (h1 : term15 A lt2) : @WF A lt2.
Proof. exact (EQ_MP (@lem339378 A lt2) (@lem346579 A lt2 h1)). Qed.
Lemma lem346581 {A : Type'} (lt2 : type1402 A) : term1094 A lt2.
Proof. exact (fun h0 : term15 A lt2 => @lem346580 A lt2 h0). Qed.
