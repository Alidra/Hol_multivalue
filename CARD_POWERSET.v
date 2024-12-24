Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CARD_POWERSET_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import HAS_SIZE_spec.
Require Import HAS_SIZE_POWERSET_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19490_spec.
Require Import thm19792_spec.
Require Import thm20230_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm69_spec.
Lemma lem4597301 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4597302 {A : Type'} : (term1 A) = (term2 A).
Proof. exact (@lem4597301 (term1 A)). Qed.
Lemma lem4597303 {A : Type'} : (term2 A) = (term1 A).
Proof. exact (SYM (@lem4597302 A)). Qed.
Lemma lem4597304 {A : Type'} (h1 : term3 A) : term3 A.
Proof. exact (h1). Qed.
Lemma lem4597305 {A : Type'} : term4 A.
Proof. exact (@lem4597289 A). Qed.
Lemma lem4597309 {A : Type'} : term5 A.
Proof. exact (@lem3863773 A). Qed.
Lemma lem4597310 {A : Type'} : term6 A.
Proof. exact (@lem3863773 (A -> Prop)). Qed.
Lemma lem4597316 {_100044 A : Type'} (h1 : term7 _100044 A) : term7 _100044 A.
Proof. exact (h1). Qed.
Lemma lem4597317 {_100044 A : Type'} : term8 _100044 A.
Proof. exact (fun h0 : term7 _100044 A => @lem4597316 _100044 A h0). Qed.
Lemma lem4597318 {_100044 A : Type'} (h1 : term8 _100044 A) : term8 _100044 A.
Proof. exact (h1). Qed.
Lemma lem4597319 {_100044 A : Type'} (h1 : term7 _100044 A) : term7 _100044 A.
Proof. exact (h1). Qed.
Lemma lem4597320 {_100044 A : Type'} (h1 : term7 _100044 A) (h2 : term8 _100044 A) : term7 _100044 A.
Proof. exact (@lem4597318 _100044 A h2 (@lem4597319 _100044 A h1)). Qed.
Lemma lem4597321 {_100044 A : Type'} (h1 : term7 _100044 A) : term9 _100044 A.
Proof. exact (fun h0 : term8 _100044 A => @lem4597320 _100044 A h1 h0). Qed.
Lemma lem4597322 {_100044 A : Type'} (h1 : term8 _100044 A) : term8 _100044 A.
Proof. exact (h1). Qed.
Lemma lem4597323 {_100044 A : Type'} (h1 : term7 _100044 A) (h2 : term8 _100044 A) : term7 _100044 A.
Proof. exact (@lem4597321 _100044 A h1 (@lem4597322 _100044 A h2)). Qed.
Lemma lem4597324 {_100044 A : Type'} (h1 : term8 _100044 A) : term8 _100044 A.
Proof. exact (fun h0 : term7 _100044 A => @lem4597323 _100044 A h0 h1). Qed.
Lemma lem4597325 {_100044 A : Type'} : term10 _100044 A.
Proof. exact (fun h0 : term8 _100044 A => @lem4597324 _100044 A h0). Qed.
Lemma lem4597328 {_100044 A : Type'} : term8 _100044 A.
Proof. exact (@lem4597325 _100044 A (@lem4597317 _100044 A)). Qed.
Lemma lem4597329 {_100044 A : Type'} : term8 _100044 A.
Proof. exact (@lem4597328 _100044 A). Qed.
Lemma lem4597379 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4597380 {A : Type'} : (term11 A) = (term12 A).
Proof. exact (@lem4597379 (term4 A)). Qed.
Lemma lem4597395 {A : Type'} : (term13 A) = (term13 A).
Proof. exact (eq_refl (term13 A)). Qed.
Lemma lem4597396 {A : Type'} : (term14 A) = (term15 A).
Proof. exact (MK_COMB (@lem4597395 A) (@lem4597380 A)). Qed.
Lemma lem4597399 {A : Type'} : (term16 A) = (term16 A).
Proof. exact (eq_refl (term16 A)). Qed.
Lemma lem4597400 {A : Type'} : (term17 A) = (term18 A).
Proof. exact (MK_COMB (@lem4597399 A) (@lem4597396 A)). Qed.
Lemma lem4597403 {_100044 : Type'} : (term16 _100044) = (term16 _100044).
Proof. exact (eq_refl (term16 _100044)). Qed.
Lemma lem4597404 {_100044 A : Type'} : (term19 _100044 A) = (term20 _100044 A).
Proof. exact (MK_COMB (@lem4597403 _100044) (@lem4597400 A)). Qed.
Lemma lem4597407 {A : Type'} : (term21 A) = (term21 A).
Proof. exact (eq_refl (term21 A)). Qed.
Lemma lem4597412 {_100044 A : Type'} : (term7 _100044 A) = (term22 _100044 A).
Proof. exact (MK_COMB (@lem4597407 A) (@lem4597404 _100044 A)). Qed.
Lemma lem4597413 {A : Type'} (_55215 : type639 A) (h1 : _55215 = (term23 A)) : _55215 = (term23 A).
Proof. exact (h1). Qed.
Lemma lem4597414 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4597415 {A : Type'} (s : A -> Prop) (_55215 : type639 A) (h1 : _55215 = (term23 A)) : (_55215 s) = (term24 A s).
Proof. exact (MK_COMB (@lem4597413 A _55215 h1) (@lem4597414 A s)). Qed.
Lemma lem4597416 {A : Type'} (s : A -> Prop) : (term24 A s) = (term25 A s).
Proof. exact (eq_refl (term24 A s)). Qed.
Lemma lem4597417 {A : Type'} (_55215 : type639 A) (s : A -> Prop) : (term26 A _55215 s) = (term26 A _55215 s).
Proof. exact (eq_refl (term26 A _55215 s)). Qed.
Lemma lem4597418 {A : Type'} (_55215 : type639 A) (s : A -> Prop) : ((_55215 s) = (term24 A s)) = ((_55215 s) = (term25 A s)).
Proof. exact (MK_COMB (@lem4597417 A _55215 s) (@lem4597416 A s)). Qed.
Lemma lem4597419 {A : Type'} (s : A -> Prop) (_55215 : type639 A) (h1 : _55215 = (term23 A)) : (_55215 s) = (term25 A s).
Proof. exact (EQ_MP (@lem4597418 A _55215 s) (@lem4597415 A s _55215 h1)). Qed.
Lemma lem4597431 (n : nat) : (term27 n) = (term27 n).
Proof. exact (eq_refl (term27 n)). Qed.
Lemma lem4597433 {A : Type'} (s : A -> Prop) (_55215 : type639 A) (h1 : _55215 = (term23 A)) : (term25 A s) = (_55215 s).
Proof. exact (SYM (@lem4597419 A s _55215 h1)). Qed.
Lemma lem4597434 {A : Type'} (s : A -> Prop) (_55215 : type639 A) (h1 : _55215 = (term23 A)) : (term25 A s) = (_55215 s).
Proof. exact (@lem4597433 A s _55215 h1). Qed.
Lemma lem4597435 {A : Type'} : (@GSPEC (A -> Prop)) = (@GSPEC (A -> Prop)).
Proof. exact (eq_refl (@GSPEC (A -> Prop))). Qed.
Lemma lem4597436 {A : Type'} (s : A -> Prop) (_55215 : type639 A) (h1 : _55215 = (term23 A)) : (term28 A s) = (term29 A _55215 s).
Proof. exact (MK_COMB (@lem4597435 A) (@lem4597434 A s _55215 h1)). Qed.
Lemma lem4597437 {A : Type'} : (@HAS_SIZE (A -> Prop)) = (@HAS_SIZE (A -> Prop)).
Proof. exact (eq_refl (@HAS_SIZE (A -> Prop))). Qed.
Lemma lem4597438 {A : Type'} (s : A -> Prop) (_55215 : type639 A) (h1 : _55215 = (term23 A)) : (term30 A s) = (term31 A _55215 s).
Proof. exact (MK_COMB (@lem4597437 A) (@lem4597436 A s _55215 h1)). Qed.
Lemma lem4597439 {A : Type'} (s : A -> Prop) (n : nat) (_55215 : type639 A) (h1 : _55215 = (term23 A)) : (term32 A s n) = (term33 A _55215 s n).
Proof. exact (MK_COMB (@lem4597438 A s _55215 h1) (@lem4597431 n)). Qed.
Lemma lem4597446 {A : Type'} (s : A -> Prop) (n : nat) : (term34 A s n) = (term34 A s n).
Proof. exact (eq_refl (term34 A s n)). Qed.
Lemma lem4597447 {A : Type'} (s : A -> Prop) (n : nat) (_55215 : type639 A) (h1 : _55215 = (term23 A)) : (term35 A s n) = (term36 A _55215 s n).
Proof. exact (MK_COMB (@lem4597446 A s n) (@lem4597439 A s n _55215 h1)). Qed.
Lemma lem4597448 {A : Type'} (s : A -> Prop) (_55215 : type639 A) (h1 : _55215 = (term23 A)) : (term37 A s) = (term38 A _55215 s).
Proof. exact (fun_ext (fun n : nat => @lem4597447 A s n _55215 h1)). Qed.
Lemma lem4597449 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4597450 {A : Type'} (s : A -> Prop) (_55215 : type639 A) (h1 : _55215 = (term23 A)) : (term39 A s) = (term40 A _55215 s).
Proof. exact (MK_COMB (@lem4597449) (@lem4597448 A s _55215 h1)). Qed.
Lemma lem4597451 {A : Type'} (_55215 : type639 A) (h1 : _55215 = (term23 A)) : (term41 A) = (term42 A _55215).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4597450 A s _55215 h1)). Qed.
Lemma lem4597452 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4597453 {A : Type'} (_55215 : type639 A) (h1 : _55215 = (term23 A)) : (term4 A) = (term43 A _55215).
Proof. exact (MK_COMB (@lem4597452 A) (@lem4597451 A _55215 h1)). Qed.
Lemma lem4597454 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4597455 {A : Type'} (_55215 : type639 A) (h1 : _55215 = (term23 A)) : (term12 A) = (term44 A _55215).
Proof. exact (MK_COMB (@lem4597454) (@lem4597453 A _55215 h1)). Qed.
Lemma lem4597476 {A : Type'} (s : type686 A) (n : nat) : ((@HAS_SIZE (A -> Prop) s n) = (term45 A s n)) = ((@HAS_SIZE (A -> Prop) s n) = (term45 A s n)).
Proof. exact (eq_refl ((@HAS_SIZE (A -> Prop) s n) = (term45 A s n))). Qed.
Lemma lem4597477 {A : Type'} (s : type686 A) : (term46 A s) = (term46 A s).
Proof. exact (fun_ext (fun n : nat => @lem4597476 A s n)). Qed.
Lemma lem4597478 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4597479 {A : Type'} (s : type686 A) : (term47 A s) = (term47 A s).
Proof. exact (MK_COMB (@lem4597478) (@lem4597477 A s)). Qed.
Lemma lem4597480 {A : Type'} : (term48 A) = (term48 A).
Proof. exact (fun_ext (fun s : type686 A => @lem4597479 A s)). Qed.
Lemma lem4597481 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4597482 {A : Type'} : (term6 A) = (term6 A).
Proof. exact (MK_COMB (@lem4597481 A) (@lem4597480 A)). Qed.
Lemma lem4597483 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4597484 {A : Type'} : (term13 A) = (term13 A).
Proof. exact (MK_COMB (@lem4597483) (@lem4597482 A)). Qed.
Lemma lem4597485 {A : Type'} (_55215 : type639 A) (h1 : _55215 = (term23 A)) : (term15 A) = (term49 A _55215).
Proof. exact (MK_COMB (@lem4597484 A) (@lem4597455 A _55215 h1)). Qed.
Lemma lem4597506 {A : Type'} (s : A -> Prop) (n : nat) : ((@HAS_SIZE A s n) = (term50 A s n)) = ((@HAS_SIZE A s n) = (term50 A s n)).
Proof. exact (eq_refl ((@HAS_SIZE A s n) = (term50 A s n))). Qed.
Lemma lem4597507 {A : Type'} (s : A -> Prop) : (term51 A s) = (term51 A s).
Proof. exact (fun_ext (fun n : nat => @lem4597506 A s n)). Qed.
Lemma lem4597508 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4597509 {A : Type'} (s : A -> Prop) : (term52 A s) = (term52 A s).
Proof. exact (MK_COMB (@lem4597508) (@lem4597507 A s)). Qed.
Lemma lem4597510 {A : Type'} : (term53 A) = (term53 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4597509 A s)). Qed.
Lemma lem4597511 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4597512 {A : Type'} : (term5 A) = (term5 A).
Proof. exact (MK_COMB (@lem4597511 A) (@lem4597510 A)). Qed.
Lemma lem4597513 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4597514 {A : Type'} : (term16 A) = (term16 A).
Proof. exact (MK_COMB (@lem4597513) (@lem4597512 A)). Qed.
Lemma lem4597515 {A : Type'} (_55215 : type639 A) (h1 : _55215 = (term23 A)) : (term18 A) = (term54 A _55215).
Proof. exact (MK_COMB (@lem4597514 A) (@lem4597485 A _55215 h1)). Qed.
Lemma lem4597536 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : ((@HAS_SIZE _100044 s n) = (term50 _100044 s n)) = ((@HAS_SIZE _100044 s n) = (term50 _100044 s n)).
Proof. exact (eq_refl ((@HAS_SIZE _100044 s n) = (term50 _100044 s n))). Qed.
Lemma lem4597537 {_100044 : Type'} (s : _100044 -> Prop) : (term51 _100044 s) = (term51 _100044 s).
Proof. exact (fun_ext (fun n : nat => @lem4597536 _100044 s n)). Qed.
Lemma lem4597538 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4597539 {_100044 : Type'} (s : _100044 -> Prop) : (term52 _100044 s) = (term52 _100044 s).
Proof. exact (MK_COMB (@lem4597538) (@lem4597537 _100044 s)). Qed.
Lemma lem4597540 {_100044 : Type'} : (term53 _100044) = (term53 _100044).
Proof. exact (fun_ext (fun s : _100044 -> Prop => @lem4597539 _100044 s)). Qed.
Lemma lem4597541 {_100044 : Type'} : (@all (_100044 -> Prop)) = (@all (_100044 -> Prop)).
Proof. exact (eq_refl (@all (_100044 -> Prop))). Qed.
Lemma lem4597542 {_100044 : Type'} : (term5 _100044) = (term5 _100044).
Proof. exact (MK_COMB (@lem4597541 _100044) (@lem4597540 _100044)). Qed.
Lemma lem4597543 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4597544 {_100044 : Type'} : (term16 _100044) = (term16 _100044).
Proof. exact (MK_COMB (@lem4597543) (@lem4597542 _100044)). Qed.
Lemma lem4597545 {_100044 A : Type'} (_55215 : type639 A) (h1 : _55215 = (term23 A)) : (term20 _100044 A) = (term55 _100044 A _55215).
Proof. exact (MK_COMB (@lem4597544 _100044) (@lem4597515 A _55215 h1)). Qed.
Lemma lem4597558 {A : Type'} (s : A -> Prop) : (term56 A s) = (term56 A s).
Proof. exact (eq_refl (term56 A s)). Qed.
Lemma lem4597560 {A : Type'} (s : A -> Prop) (_55215 : type639 A) (h1 : _55215 = (term23 A)) : (term25 A s) = (_55215 s).
Proof. exact (SYM (@lem4597419 A s _55215 h1)). Qed.
Lemma lem4597561 {A : Type'} (s : A -> Prop) (_55215 : type639 A) (h1 : _55215 = (term23 A)) : (term25 A s) = (_55215 s).
Proof. exact (@lem4597560 A s _55215 h1). Qed.
Lemma lem4597562 {A : Type'} : (@GSPEC (A -> Prop)) = (@GSPEC (A -> Prop)).
Proof. exact (eq_refl (@GSPEC (A -> Prop))). Qed.
Lemma lem4597563 {A : Type'} (s : A -> Prop) (_55215 : type639 A) (h1 : _55215 = (term23 A)) : (term28 A s) = (term29 A _55215 s).
Proof. exact (MK_COMB (@lem4597562 A) (@lem4597561 A s _55215 h1)). Qed.
Lemma lem4597564 {A : Type'} : (@CARD (A -> Prop)) = (@CARD (A -> Prop)).
Proof. exact (eq_refl (@CARD (A -> Prop))). Qed.
Lemma lem4597565 {A : Type'} (s : A -> Prop) (_55215 : type639 A) (h1 : _55215 = (term23 A)) : (term57 A s) = (term58 A _55215 s).
Proof. exact (MK_COMB (@lem4597564 A) (@lem4597563 A s _55215 h1)). Qed.
Lemma lem4597566 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem4597567 {A : Type'} (s : A -> Prop) (_55215 : type639 A) (h1 : _55215 = (term23 A)) : (term59 A s) = (term60 A _55215 s).
Proof. exact (MK_COMB (@lem4597566) (@lem4597565 A s _55215 h1)). Qed.
Lemma lem4597568 {A : Type'} (s : A -> Prop) (_55215 : type639 A) (h1 : _55215 = (term23 A)) : ((term57 A s) = (term56 A s)) = ((term58 A _55215 s) = (term56 A s)).
Proof. exact (MK_COMB (@lem4597567 A s _55215 h1) (@lem4597558 A s)). Qed.
Lemma lem4597573 {A : Type'} (s : A -> Prop) : (term61 A s) = (term61 A s).
Proof. exact (eq_refl (term61 A s)). Qed.
Lemma lem4597574 {A : Type'} (s : A -> Prop) (_55215 : type639 A) (h1 : _55215 = (term23 A)) : (term62 A s) = (term63 A _55215 s).
Proof. exact (MK_COMB (@lem4597573 A s) (@lem4597568 A s _55215 h1)). Qed.
Lemma lem4597575 {A : Type'} (_55215 : type639 A) (h1 : _55215 = (term23 A)) : (term64 A) = (term65 A _55215).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4597574 A s _55215 h1)). Qed.
Lemma lem4597576 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4597577 {A : Type'} (_55215 : type639 A) (h1 : _55215 = (term23 A)) : (term1 A) = (term66 A _55215).
Proof. exact (MK_COMB (@lem4597576 A) (@lem4597575 A _55215 h1)). Qed.
Lemma lem4597578 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4597579 {A : Type'} (_55215 : type639 A) (h1 : _55215 = (term23 A)) : (term3 A) = (term67 A _55215).
Proof. exact (MK_COMB (@lem4597578) (@lem4597577 A _55215 h1)). Qed.
Lemma lem4597580 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4597581 {A : Type'} (_55215 : type639 A) (h1 : _55215 = (term23 A)) : (term21 A) = (term68 A _55215).
Proof. exact (MK_COMB (@lem4597580) (@lem4597579 A _55215 h1)). Qed.
Lemma lem4597582 {_100044 A : Type'} (_55215 : type639 A) (h1 : _55215 = (term23 A)) : (term22 _100044 A) = (term69 _100044 A _55215).
Proof. exact (MK_COMB (@lem4597581 A _55215 h1) (@lem4597545 _100044 A _55215 h1)). Qed.
Lemma lem4597583 {_100044 A : Type'} (_55215 : type639 A) : term70 _100044 A _55215.
Proof. exact (fun h0 : _55215 = (term23 A) => @lem4597582 _100044 A _55215 h0). Qed.
Lemma lem4597584 {_100044 A : Type'} : term71 _100044 A.
Proof. exact (fun _55215 : type639 A => @lem4597583 _100044 A _55215). Qed.
Lemma lem4597586 {_3603 : Type'} (P : Prop) (c : _3603) (Q : _3603 -> Prop) : term72 _3603 P c Q.
Proof. exact (EQ_MP (@lem20230 _3603 P c Q) (@lem0)). Qed.
Lemma lem4597587 {A : Type'} (P : Prop) (c : type639 A) (Q : type141 A) : term73 A P c Q.
Proof. exact (@lem4597586 (type639 A) P c Q). Qed.
Lemma lem4597588 {_100044 A : Type'} : term74 _100044 A.
Proof. exact (@lem4597587 A (term22 _100044 A) (term23 A) (term75 _100044 A)). Qed.
Lemma lem4597589 {_100044 A : Type'} (_55215 : type639 A) : (term76 _100044 A _55215) = (term69 _100044 A _55215).
Proof. exact (eq_refl (term76 _100044 A _55215)). Qed.
Lemma lem4597590 {_100044 A : Type'} : (term77 _100044 A) = (term77 _100044 A).
Proof. exact (eq_refl (term77 _100044 A)). Qed.
Lemma lem4597591 {_100044 A : Type'} (_55215 : type639 A) : ((term22 _100044 A) = (term76 _100044 A _55215)) = ((term22 _100044 A) = (term69 _100044 A _55215)).
Proof. exact (MK_COMB (@lem4597590 _100044 A) (@lem4597589 _100044 A _55215)). Qed.
Lemma lem4597592 {A : Type'} (_55215 : type639 A) : (term78 A _55215) = (term78 A _55215).
Proof. exact (eq_refl (term78 A _55215)). Qed.
Lemma lem4597593 {_100044 A : Type'} (_55215 : type639 A) : (term79 _100044 A _55215) = (term70 _100044 A _55215).
Proof. exact (MK_COMB (@lem4597592 A _55215) (@lem4597591 _100044 A _55215)). Qed.
Lemma lem4597594 {_100044 A : Type'} : (term80 _100044 A) = (term81 _100044 A).
Proof. exact (fun_ext (fun _55215 : type639 A => @lem4597593 _100044 A _55215)). Qed.
Lemma lem4597595 {A : Type'} : (@all ((A -> Prop) -> (A -> Prop) -> Prop)) = (@all ((A -> Prop) -> (A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> (A -> Prop) -> Prop))). Qed.
Lemma lem4597596 {_100044 A : Type'} : (term82 _100044 A) = (term71 _100044 A).
Proof. exact (MK_COMB (@lem4597595 A) (@lem4597594 _100044 A)). Qed.
Lemma lem4597597 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4597598 {_100044 A : Type'} : (term83 _100044 A) = (term84 _100044 A).
Proof. exact (MK_COMB (@lem4597597) (@lem4597596 _100044 A)). Qed.
Lemma lem4597599 {_100044 A : Type'} (_55215 : type639 A) : (term76 _100044 A _55215) = (term69 _100044 A _55215).
Proof. exact (eq_refl (term76 _100044 A _55215)). Qed.
Lemma lem4597600 {A : Type'} (_55215 : type639 A) : (term78 A _55215) = (term78 A _55215).
Proof. exact (eq_refl (term78 A _55215)). Qed.
Lemma lem4597601 {_100044 A : Type'} (_55215 : type639 A) : (term85 _100044 A _55215) = (term86 _100044 A _55215).
Proof. exact (MK_COMB (@lem4597600 A _55215) (@lem4597599 _100044 A _55215)). Qed.
Lemma lem4597602 {_100044 A : Type'} : (term87 _100044 A) = (term88 _100044 A).
Proof. exact (fun_ext (fun _55215 : type639 A => @lem4597601 _100044 A _55215)). Qed.
Lemma lem4597603 {A : Type'} : (@all ((A -> Prop) -> (A -> Prop) -> Prop)) = (@all ((A -> Prop) -> (A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> (A -> Prop) -> Prop))). Qed.
Lemma lem4597604 {_100044 A : Type'} : (term89 _100044 A) = (term90 _100044 A).
Proof. exact (MK_COMB (@lem4597603 A) (@lem4597602 _100044 A)). Qed.
Lemma lem4597605 {_100044 A : Type'} : (term77 _100044 A) = (term77 _100044 A).
Proof. exact (eq_refl (term77 _100044 A)). Qed.
Lemma lem4597606 {_100044 A : Type'} : ((term22 _100044 A) = (term89 _100044 A)) = ((term22 _100044 A) = (term90 _100044 A)).
Proof. exact (MK_COMB (@lem4597605 _100044 A) (@lem4597604 _100044 A)). Qed.
Lemma lem4597607 {_100044 A : Type'} : (term74 _100044 A) = (term91 _100044 A).
Proof. exact (MK_COMB (@lem4597598 _100044 A) (@lem4597606 _100044 A)). Qed.
Lemma lem4597608 {_100044 A : Type'} : term91 _100044 A.
Proof. exact (EQ_MP (@lem4597607 _100044 A) (@lem4597588 _100044 A)). Qed.
Lemma lem4597609 {_100044 A : Type'} : (term22 _100044 A) = (term90 _100044 A).
Proof. exact (@lem4597608 _100044 A (@lem4597584 _100044 A)). Qed.
Lemma lem4597611 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term92 _3571 _3575 t)) = (term93 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem4597612 {A : Type'} (s : type639 A) (t : type639 A) : (s = (term94 A t)) = (term95 A s t).
Proof. exact (@lem4597611 (type686 A) (A -> Prop) s t). Qed.
Lemma lem4597613 {A : Type'} (_55215 : type639 A) : (_55215 = (term96 A)) = (term97 A _55215).
Proof. exact (@lem4597612 A _55215 (term23 A)). Qed.
Lemma lem4597614 {A : Type'} (s : A -> Prop) : (term24 A s) = (term25 A s).
Proof. exact (eq_refl (term24 A s)). Qed.
Lemma lem4597615 {A : Type'} : (term96 A) = (term23 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4597614 A s)). Qed.
Lemma lem4597616 {A : Type'} (_55215 : type639 A) : (@eq ((A -> Prop) -> (A -> Prop) -> Prop) _55215) = (@eq ((A -> Prop) -> (A -> Prop) -> Prop) _55215).
Proof. exact (eq_refl (@eq ((A -> Prop) -> (A -> Prop) -> Prop) _55215)). Qed.
Lemma lem4597617 {A : Type'} (_55215 : type639 A) : (_55215 = (term96 A)) = (_55215 = (term23 A)).
Proof. exact (MK_COMB (@lem4597616 A _55215) (@lem4597615 A)). Qed.
Lemma lem4597618 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4597619 {A : Type'} (_55215 : type639 A) : (term98 A _55215) = (term99 A _55215).
Proof. exact (MK_COMB (@lem4597618) (@lem4597617 A _55215)). Qed.
Lemma lem4597620 {A : Type'} (s : A -> Prop) : (term24 A s) = (term25 A s).
Proof. exact (eq_refl (term24 A s)). Qed.
Lemma lem4597621 {A : Type'} (_55215 : type639 A) (s : A -> Prop) : (term26 A _55215 s) = (term26 A _55215 s).
Proof. exact (eq_refl (term26 A _55215 s)). Qed.
Lemma lem4597622 {A : Type'} (_55215 : type639 A) (s : A -> Prop) : ((_55215 s) = (term24 A s)) = ((_55215 s) = (term25 A s)).
Proof. exact (MK_COMB (@lem4597621 A _55215 s) (@lem4597620 A s)). Qed.
Lemma lem4597623 {A : Type'} (_55215 : type639 A) : (term100 A _55215) = (term101 A _55215).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4597622 A _55215 s)). Qed.
Lemma lem4597624 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4597625 {A : Type'} (_55215 : type639 A) : (term97 A _55215) = (term102 A _55215).
Proof. exact (MK_COMB (@lem4597624 A) (@lem4597623 A _55215)). Qed.
Lemma lem4597626 {A : Type'} (_55215 : type639 A) : ((_55215 = (term96 A)) = (term97 A _55215)) = ((_55215 = (term23 A)) = (term102 A _55215)).
Proof. exact (MK_COMB (@lem4597619 A _55215) (@lem4597625 A _55215)). Qed.
Lemma lem4597627 {A : Type'} (_55215 : type639 A) : (_55215 = (term23 A)) = (term102 A _55215).
Proof. exact (EQ_MP (@lem4597626 A _55215) (@lem4597613 A _55215)). Qed.
Lemma lem4597629 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term92 _3571 _3575 t)) = (term93 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem4597630 {A : Type'} (s : type686 A) (t : type686 A) : (s = (term103 A t)) = (term104 A s t).
Proof. exact (@lem4597629 Prop (A -> Prop) s t). Qed.
Lemma lem4597631 {A : Type'} (_55215 : type639 A) (s : A -> Prop) : ((_55215 s) = (term105 A s)) = (term106 A _55215 s).
Proof. exact (@lem4597630 A (_55215 s) (term25 A s)). Qed.
Lemma lem4597632 {A : Type'} (GEN_PVAR_154 : A -> Prop) (s : A -> Prop) : (term107 A s GEN_PVAR_154) = (term108 A GEN_PVAR_154 s).
Proof. exact (eq_refl (term107 A s GEN_PVAR_154)). Qed.
Lemma lem4597633 {A : Type'} (s : A -> Prop) : (term105 A s) = (term25 A s).
Proof. exact (fun_ext (fun GEN_PVAR_154 : A -> Prop => @lem4597632 A GEN_PVAR_154 s)). Qed.
Lemma lem4597634 {A : Type'} (_55215 : type639 A) (s : A -> Prop) : (term26 A _55215 s) = (term26 A _55215 s).
Proof. exact (eq_refl (term26 A _55215 s)). Qed.
Lemma lem4597635 {A : Type'} (_55215 : type639 A) (s : A -> Prop) : ((_55215 s) = (term105 A s)) = ((_55215 s) = (term25 A s)).
Proof. exact (MK_COMB (@lem4597634 A _55215 s) (@lem4597633 A s)). Qed.
Lemma lem4597636 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4597637 {A : Type'} (_55215 : type639 A) (s : A -> Prop) : (term109 A _55215 s) = (term110 A _55215 s).
Proof. exact (MK_COMB (@lem4597636) (@lem4597635 A _55215 s)). Qed.
Lemma lem4597638 {A : Type'} (GEN_PVAR_154 : A -> Prop) (s : A -> Prop) : (term107 A s GEN_PVAR_154) = (term108 A GEN_PVAR_154 s).
Proof. exact (eq_refl (term107 A s GEN_PVAR_154)). Qed.
Lemma lem4597639 {A : Type'} (_55215 : type639 A) (s : A -> Prop) (GEN_PVAR_154 : A -> Prop) : (term111 A _55215 s GEN_PVAR_154) = (term111 A _55215 s GEN_PVAR_154).
Proof. exact (eq_refl (term111 A _55215 s GEN_PVAR_154)). Qed.
Lemma lem4597640 {A : Type'} (_55215 : type639 A) (GEN_PVAR_154 : A -> Prop) (s : A -> Prop) : ((_55215 s GEN_PVAR_154) = (term107 A s GEN_PVAR_154)) = ((_55215 s GEN_PVAR_154) = (term108 A GEN_PVAR_154 s)).
Proof. exact (MK_COMB (@lem4597639 A _55215 s GEN_PVAR_154) (@lem4597638 A GEN_PVAR_154 s)). Qed.
Lemma lem4597641 {A : Type'} (_55215 : type639 A) (s : A -> Prop) : (term112 A _55215 s) = (term113 A _55215 s).
Proof. exact (fun_ext (fun GEN_PVAR_154 : A -> Prop => @lem4597640 A _55215 GEN_PVAR_154 s)). Qed.
Lemma lem4597642 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4597643 {A : Type'} (_55215 : type639 A) (s : A -> Prop) : (term106 A _55215 s) = (term114 A _55215 s).
Proof. exact (MK_COMB (@lem4597642 A) (@lem4597641 A _55215 s)). Qed.
Lemma lem4597644 {A : Type'} (_55215 : type639 A) (s : A -> Prop) : (((_55215 s) = (term105 A s)) = (term106 A _55215 s)) = (((_55215 s) = (term25 A s)) = (term114 A _55215 s)).
Proof. exact (MK_COMB (@lem4597637 A _55215 s) (@lem4597643 A _55215 s)). Qed.
Lemma lem4597645 {A : Type'} (_55215 : type639 A) (s : A -> Prop) : ((_55215 s) = (term25 A s)) = (term114 A _55215 s).
Proof. exact (EQ_MP (@lem4597644 A _55215 s) (@lem4597631 A _55215 s)). Qed.
Lemma lem4597646 {A : Type'} (_55215 : type639 A) (GEN_PVAR_154 : A -> Prop) (s : A -> Prop) : ((_55215 s GEN_PVAR_154) = (term108 A GEN_PVAR_154 s)) = ((_55215 s GEN_PVAR_154) = (term108 A GEN_PVAR_154 s)).
Proof. exact (eq_refl ((_55215 s GEN_PVAR_154) = (term108 A GEN_PVAR_154 s))). Qed.
Lemma lem4597647 {A : Type'} (_55215 : type639 A) (s : A -> Prop) : (term113 A _55215 s) = (term113 A _55215 s).
Proof. exact (fun_ext (fun GEN_PVAR_154 : A -> Prop => @lem4597646 A _55215 GEN_PVAR_154 s)). Qed.
Lemma lem4597648 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4597649 {A : Type'} (_55215 : type639 A) (s : A -> Prop) : (term114 A _55215 s) = (term114 A _55215 s).
Proof. exact (MK_COMB (@lem4597648 A) (@lem4597647 A _55215 s)). Qed.
Lemma lem4597650 {A : Type'} (_55215 : type639 A) (s : A -> Prop) : ((_55215 s) = (term25 A s)) = (term114 A _55215 s).
Proof. exact (TRANS (@lem4597645 A _55215 s) (@lem4597649 A _55215 s)). Qed.
Lemma lem4597651 {A : Type'} (_55215 : type639 A) : (term101 A _55215) = (term115 A _55215).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4597650 A _55215 s)). Qed.
Lemma lem4597652 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4597653 {A : Type'} (_55215 : type639 A) : (term102 A _55215) = (term116 A _55215).
Proof. exact (MK_COMB (@lem4597652 A) (@lem4597651 A _55215)). Qed.
Lemma lem4597654 {A : Type'} (_55215 : type639 A) : (_55215 = (term23 A)) = (term116 A _55215).
Proof. exact (TRANS (@lem4597627 A _55215) (@lem4597653 A _55215)). Qed.
Lemma lem4597655 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4597656 {A : Type'} (_55215 : type639 A) : (term78 A _55215) = (term117 A _55215).
Proof. exact (MK_COMB (@lem4597655) (@lem4597654 A _55215)). Qed.
Lemma lem4597657 {_100044 A : Type'} (_55215 : type639 A) : (term69 _100044 A _55215) = (term69 _100044 A _55215).
Proof. exact (eq_refl (term69 _100044 A _55215)). Qed.
Lemma lem4597658 {_100044 A : Type'} (_55215 : type639 A) : (term86 _100044 A _55215) = (term118 _100044 A _55215).
Proof. exact (MK_COMB (@lem4597656 A _55215) (@lem4597657 _100044 A _55215)). Qed.
Lemma lem4597659 {_100044 A : Type'} : (term88 _100044 A) = (term119 _100044 A).
Proof. exact (fun_ext (fun _55215 : type639 A => @lem4597658 _100044 A _55215)). Qed.
Lemma lem4597660 {A : Type'} : (@all ((A -> Prop) -> (A -> Prop) -> Prop)) = (@all ((A -> Prop) -> (A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> (A -> Prop) -> Prop))). Qed.
Lemma lem4597661 {_100044 A : Type'} : (term90 _100044 A) = (term120 _100044 A).
Proof. exact (MK_COMB (@lem4597660 A) (@lem4597659 _100044 A)). Qed.
Lemma lem4597662 {_100044 A : Type'} : (term77 _100044 A) = (term77 _100044 A).
Proof. exact (eq_refl (term77 _100044 A)). Qed.
Lemma lem4597663 {_100044 A : Type'} : ((term22 _100044 A) = (term90 _100044 A)) = ((term22 _100044 A) = (term120 _100044 A)).
Proof. exact (MK_COMB (@lem4597662 _100044 A) (@lem4597661 _100044 A)). Qed.
Lemma lem4597666 {_100044 A : Type'} : (term22 _100044 A) = (term120 _100044 A).
Proof. exact (EQ_MP (@lem4597663 _100044 A) (@lem4597609 _100044 A)). Qed.
Lemma lem4597667 {_100044 A : Type'} : (term7 _100044 A) = (term120 _100044 A).
Proof. exact (TRANS (@lem4597412 _100044 A) (@lem4597666 _100044 A)). Qed.
Lemma lem4597672 {A : Type'} (_55215 : type639 A) (s : A -> Prop) (n : nat) : (term36 A _55215 s n) = (term36 A _55215 s n).
Proof. exact (eq_refl (term36 A _55215 s n)). Qed.
Lemma lem4597673 {A : Type'} (_55215 : type639 A) (s : A -> Prop) : (term38 A _55215 s) = (term38 A _55215 s).
Proof. exact (fun_ext (fun n : nat => @lem4597672 A _55215 s n)). Qed.
Lemma lem4597674 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4597675 {A : Type'} (_55215 : type639 A) (s : A -> Prop) : (term40 A _55215 s) = (term40 A _55215 s).
Proof. exact (MK_COMB (@lem4597674) (@lem4597673 A _55215 s)). Qed.
Lemma lem4597676 {A : Type'} (_55215 : type639 A) : (term42 A _55215) = (term42 A _55215).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4597675 A _55215 s)). Qed.
Lemma lem4597677 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4597678 {A : Type'} (_55215 : type639 A) : (term43 A _55215) = (term43 A _55215).
Proof. exact (MK_COMB (@lem4597677 A) (@lem4597676 A _55215)). Qed.
Lemma lem4597679 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4597680 {A : Type'} (_55215 : type639 A) : (term44 A _55215) = (term44 A _55215).
Proof. exact (MK_COMB (@lem4597679) (@lem4597678 A _55215)). Qed.
Lemma lem4597689 {A : Type'} (s : type686 A) (n : nat) : ((@HAS_SIZE (A -> Prop) s n) = (term45 A s n)) = ((@HAS_SIZE (A -> Prop) s n) = (term45 A s n)).
Proof. exact (eq_refl ((@HAS_SIZE (A -> Prop) s n) = (term45 A s n))). Qed.
Lemma lem4597690 {A : Type'} (s : type686 A) : (term46 A s) = (term46 A s).
Proof. exact (fun_ext (fun n : nat => @lem4597689 A s n)). Qed.
Lemma lem4597691 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4597692 {A : Type'} (s : type686 A) : (term47 A s) = (term47 A s).
Proof. exact (MK_COMB (@lem4597691) (@lem4597690 A s)). Qed.
Lemma lem4597693 {A : Type'} : (term48 A) = (term48 A).
Proof. exact (fun_ext (fun s : type686 A => @lem4597692 A s)). Qed.
Lemma lem4597694 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4597695 {A : Type'} : (term6 A) = (term6 A).
Proof. exact (MK_COMB (@lem4597694 A) (@lem4597693 A)). Qed.
Lemma lem4597696 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4597697 {A : Type'} : (term13 A) = (term13 A).
Proof. exact (MK_COMB (@lem4597696) (@lem4597695 A)). Qed.
Lemma lem4597698 {A : Type'} (_55215 : type639 A) : (term49 A _55215) = (term49 A _55215).
Proof. exact (MK_COMB (@lem4597697 A) (@lem4597680 A _55215)). Qed.
Lemma lem4597707 {A : Type'} (s : A -> Prop) (n : nat) : ((@HAS_SIZE A s n) = (term50 A s n)) = ((@HAS_SIZE A s n) = (term50 A s n)).
Proof. exact (eq_refl ((@HAS_SIZE A s n) = (term50 A s n))). Qed.
Lemma lem4597708 {A : Type'} (s : A -> Prop) : (term51 A s) = (term51 A s).
Proof. exact (fun_ext (fun n : nat => @lem4597707 A s n)). Qed.
Lemma lem4597709 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4597710 {A : Type'} (s : A -> Prop) : (term52 A s) = (term52 A s).
Proof. exact (MK_COMB (@lem4597709) (@lem4597708 A s)). Qed.
Lemma lem4597711 {A : Type'} : (term53 A) = (term53 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4597710 A s)). Qed.
Lemma lem4597712 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4597713 {A : Type'} : (term5 A) = (term5 A).
Proof. exact (MK_COMB (@lem4597712 A) (@lem4597711 A)). Qed.
Lemma lem4597714 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4597715 {A : Type'} : (term16 A) = (term16 A).
Proof. exact (MK_COMB (@lem4597714) (@lem4597713 A)). Qed.
Lemma lem4597716 {A : Type'} (_55215 : type639 A) : (term54 A _55215) = (term54 A _55215).
Proof. exact (MK_COMB (@lem4597715 A) (@lem4597698 A _55215)). Qed.
Lemma lem4597725 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : ((@HAS_SIZE _100044 s n) = (term50 _100044 s n)) = ((@HAS_SIZE _100044 s n) = (term50 _100044 s n)).
Proof. exact (eq_refl ((@HAS_SIZE _100044 s n) = (term50 _100044 s n))). Qed.
Lemma lem4597726 {_100044 : Type'} (s : _100044 -> Prop) : (term51 _100044 s) = (term51 _100044 s).
Proof. exact (fun_ext (fun n : nat => @lem4597725 _100044 s n)). Qed.
Lemma lem4597727 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4597728 {_100044 : Type'} (s : _100044 -> Prop) : (term52 _100044 s) = (term52 _100044 s).
Proof. exact (MK_COMB (@lem4597727) (@lem4597726 _100044 s)). Qed.
Lemma lem4597729 {_100044 : Type'} : (term53 _100044) = (term53 _100044).
Proof. exact (fun_ext (fun s : _100044 -> Prop => @lem4597728 _100044 s)). Qed.
Lemma lem4597730 {_100044 : Type'} : (@all (_100044 -> Prop)) = (@all (_100044 -> Prop)).
Proof. exact (eq_refl (@all (_100044 -> Prop))). Qed.
Lemma lem4597731 {_100044 : Type'} : (term5 _100044) = (term5 _100044).
Proof. exact (MK_COMB (@lem4597730 _100044) (@lem4597729 _100044)). Qed.
Lemma lem4597732 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4597733 {_100044 : Type'} : (term16 _100044) = (term16 _100044).
Proof. exact (MK_COMB (@lem4597732) (@lem4597731 _100044)). Qed.
Lemma lem4597734 {_100044 A : Type'} (_55215 : type639 A) : (term55 _100044 A _55215) = (term55 _100044 A _55215).
Proof. exact (MK_COMB (@lem4597733 _100044) (@lem4597716 A _55215)). Qed.
Lemma lem4597739 {A : Type'} (_55215 : type639 A) (s : A -> Prop) : (term63 A _55215 s) = (term63 A _55215 s).
Proof. exact (eq_refl (term63 A _55215 s)). Qed.
Lemma lem4597740 {A : Type'} (_55215 : type639 A) : (term65 A _55215) = (term65 A _55215).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4597739 A _55215 s)). Qed.
Lemma lem4597741 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4597742 {A : Type'} (_55215 : type639 A) : (term66 A _55215) = (term66 A _55215).
Proof. exact (MK_COMB (@lem4597741 A) (@lem4597740 A _55215)). Qed.
Lemma lem4597743 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4597744 {A : Type'} (_55215 : type639 A) : (term67 A _55215) = (term67 A _55215).
Proof. exact (MK_COMB (@lem4597743) (@lem4597742 A _55215)). Qed.
Lemma lem4597745 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4597746 {A : Type'} (_55215 : type639 A) : (term68 A _55215) = (term68 A _55215).
Proof. exact (MK_COMB (@lem4597745) (@lem4597744 A _55215)). Qed.
Lemma lem4597747 {_100044 A : Type'} (_55215 : type639 A) : (term69 _100044 A _55215) = (term69 _100044 A _55215).
Proof. exact (MK_COMB (@lem4597746 A _55215) (@lem4597734 _100044 A _55215)). Qed.
Lemma lem4597748 {A : Type'} (GEN_PVAR_154 : A -> Prop) (s : A -> Prop) (t : A -> Prop) : (term121 A GEN_PVAR_154 s t) = (term121 A GEN_PVAR_154 s t).
Proof. exact (eq_refl (term121 A GEN_PVAR_154 s t)). Qed.
Lemma lem4597749 {A : Type'} (GEN_PVAR_154 : A -> Prop) (s : A -> Prop) : (term122 A GEN_PVAR_154 s) = (term122 A GEN_PVAR_154 s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4597748 A GEN_PVAR_154 s t)). Qed.
Lemma lem4597750 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4597751 {A : Type'} (GEN_PVAR_154 : A -> Prop) (s : A -> Prop) : (term108 A GEN_PVAR_154 s) = (term108 A GEN_PVAR_154 s).
Proof. exact (MK_COMB (@lem4597750 A) (@lem4597749 A GEN_PVAR_154 s)). Qed.
Lemma lem4597754 {A : Type'} (_55215 : type639 A) (s : A -> Prop) (GEN_PVAR_154 : A -> Prop) : (term111 A _55215 s GEN_PVAR_154) = (term111 A _55215 s GEN_PVAR_154).
Proof. exact (eq_refl (term111 A _55215 s GEN_PVAR_154)). Qed.
Lemma lem4597755 {A : Type'} (_55215 : type639 A) (GEN_PVAR_154 : A -> Prop) (s : A -> Prop) : ((_55215 s GEN_PVAR_154) = (term108 A GEN_PVAR_154 s)) = ((_55215 s GEN_PVAR_154) = (term108 A GEN_PVAR_154 s)).
Proof. exact (MK_COMB (@lem4597754 A _55215 s GEN_PVAR_154) (@lem4597751 A GEN_PVAR_154 s)). Qed.
Lemma lem4597756 {A : Type'} (_55215 : type639 A) (s : A -> Prop) : (term113 A _55215 s) = (term113 A _55215 s).
Proof. exact (fun_ext (fun GEN_PVAR_154 : A -> Prop => @lem4597755 A _55215 GEN_PVAR_154 s)). Qed.
Lemma lem4597757 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4597758 {A : Type'} (_55215 : type639 A) (s : A -> Prop) : (term114 A _55215 s) = (term114 A _55215 s).
Proof. exact (MK_COMB (@lem4597757 A) (@lem4597756 A _55215 s)). Qed.
Lemma lem4597759 {A : Type'} (_55215 : type639 A) : (term115 A _55215) = (term115 A _55215).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4597758 A _55215 s)). Qed.
Lemma lem4597760 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4597761 {A : Type'} (_55215 : type639 A) : (term116 A _55215) = (term116 A _55215).
Proof. exact (MK_COMB (@lem4597760 A) (@lem4597759 A _55215)). Qed.
Lemma lem4597762 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4597763 {A : Type'} (_55215 : type639 A) : (term117 A _55215) = (term117 A _55215).
Proof. exact (MK_COMB (@lem4597762) (@lem4597761 A _55215)). Qed.
Lemma lem4597764 {_100044 A : Type'} (_55215 : type639 A) : (term118 _100044 A _55215) = (term118 _100044 A _55215).
Proof. exact (MK_COMB (@lem4597763 A _55215) (@lem4597747 _100044 A _55215)). Qed.
Lemma lem4597765 {_100044 A : Type'} : (term119 _100044 A) = (term119 _100044 A).
Proof. exact (fun_ext (fun _55215 : type639 A => @lem4597764 _100044 A _55215)). Qed.
Lemma lem4597766 {A : Type'} : (@all ((A -> Prop) -> (A -> Prop) -> Prop)) = (@all ((A -> Prop) -> (A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> (A -> Prop) -> Prop))). Qed.
Lemma lem4597767 {_100044 A : Type'} : (term120 _100044 A) = (term120 _100044 A).
Proof. exact (MK_COMB (@lem4597766 A) (@lem4597765 _100044 A)). Qed.
Lemma lem4597868 {_100044 A : Type'} : (term7 _100044 A) = (term120 _100044 A).
Proof. exact (TRANS (@lem4597667 _100044 A) (@lem4597767 _100044 A)). Qed.
Lemma lem4597869 {_100044 A : Type'} : (term120 _100044 A) = (term7 _100044 A).
Proof. exact (SYM (@lem4597868 _100044 A)). Qed.
Lemma lem4597870 {A : Type'} (_55215 : type639 A) (h1 : term116 A _55215) : term116 A _55215.
Proof. exact (h1). Qed.
Lemma lem4597871 {A : Type'} (_55215 : type639 A) (h1 : term67 A _55215) : term67 A _55215.
Proof. exact (h1). Qed.
Lemma lem4597873 {A : Type'} (h1 : term5 A) : term5 A.
Proof. exact (h1). Qed.
Lemma lem4597874 {A : Type'} (h1 : term6 A) : term6 A.
Proof. exact (h1). Qed.
Lemma lem4597875 {A : Type'} (_55215 : type639 A) (h1 : term43 A _55215) : term43 A _55215.
Proof. exact (h1). Qed.
Lemma lem4597879 {A : Type'} (GEN_PVAR_154 : A -> Prop) (s : A -> Prop) (t : A -> Prop) : (term121 A GEN_PVAR_154 s t) = (term121 A GEN_PVAR_154 s t).
Proof. exact (eq_refl (term121 A GEN_PVAR_154 s t)). Qed.
Lemma lem4597880 {A : Type'} (P : type686 A) : (term123 A P) = (term124 A P).
Proof. exact (@lem18394 (A -> Prop) P). Qed.
Lemma lem4597881 {A : Type'} (GEN_PVAR_154 : A -> Prop) (s : A -> Prop) : (term125 A GEN_PVAR_154 s) = (term126 A GEN_PVAR_154 s).
Proof. exact (@lem4597880 A (term122 A GEN_PVAR_154 s)). Qed.
Lemma lem4597882 {A : Type'} (GEN_PVAR_154 : A -> Prop) (s : A -> Prop) (t : A -> Prop) : (term127 A GEN_PVAR_154 s t) = (term121 A GEN_PVAR_154 s t).
Proof. exact (eq_refl (term127 A GEN_PVAR_154 s t)). Qed.
Lemma lem4597883 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4597885 {A : Type'} (GEN_PVAR_154 : A -> Prop) (s : A -> Prop) (t : A -> Prop) : (term128 A GEN_PVAR_154 s t) = (term129 A GEN_PVAR_154 s t).
Proof. exact (MK_COMB (@lem4597883) (@lem4597882 A GEN_PVAR_154 s t)). Qed.
Lemma lem4597886 {A : Type'} (GEN_PVAR_154 : A -> Prop) (s : A -> Prop) : (term130 A GEN_PVAR_154 s) = (term131 A GEN_PVAR_154 s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4597885 A GEN_PVAR_154 s t)). Qed.
Lemma lem4597887 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4597888 {A : Type'} (GEN_PVAR_154 : A -> Prop) (s : A -> Prop) : (term126 A GEN_PVAR_154 s) = (term132 A GEN_PVAR_154 s).
Proof. exact (MK_COMB (@lem4597887 A) (@lem4597886 A GEN_PVAR_154 s)). Qed.
Lemma lem4597889 {A : Type'} (GEN_PVAR_154 : A -> Prop) (s : A -> Prop) : (term125 A GEN_PVAR_154 s) = (term132 A GEN_PVAR_154 s).
Proof. exact (TRANS (@lem4597881 A GEN_PVAR_154 s) (@lem4597888 A GEN_PVAR_154 s)). Qed.
Lemma lem4597890 {A : Type'} (GEN_PVAR_154 : A -> Prop) (s : A -> Prop) : (term122 A GEN_PVAR_154 s) = (term122 A GEN_PVAR_154 s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4597879 A GEN_PVAR_154 s t)). Qed.
Lemma lem4597891 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4597892 {A : Type'} (GEN_PVAR_154 : A -> Prop) (s : A -> Prop) : (term108 A GEN_PVAR_154 s) = (term108 A GEN_PVAR_154 s).
Proof. exact (MK_COMB (@lem4597891 A) (@lem4597890 A GEN_PVAR_154 s)). Qed.
Lemma lem4597894 {A : Type'} (_55215 : type639 A) (s : A -> Prop) (GEN_PVAR_154 : A -> Prop) : (term133 A _55215 s GEN_PVAR_154) = (term133 A _55215 s GEN_PVAR_154).
Proof. exact (eq_refl (term133 A _55215 s GEN_PVAR_154)). Qed.
Lemma lem4597895 {A : Type'} (_55215 : type639 A) (GEN_PVAR_154 : A -> Prop) (s : A -> Prop) : (term134 A _55215 GEN_PVAR_154 s) = (term134 A _55215 GEN_PVAR_154 s).
Proof. exact (MK_COMB (@lem4597894 A _55215 s GEN_PVAR_154) (@lem4597892 A GEN_PVAR_154 s)). Qed.
Lemma lem4597897 {A : Type'} (_55215 : type639 A) (s : A -> Prop) (GEN_PVAR_154 : A -> Prop) : (term135 A _55215 s GEN_PVAR_154) = (term135 A _55215 s GEN_PVAR_154).
Proof. exact (eq_refl (term135 A _55215 s GEN_PVAR_154)). Qed.
Lemma lem4597898 {A : Type'} (_55215 : type639 A) (GEN_PVAR_154 : A -> Prop) (s : A -> Prop) : (term136 A _55215 GEN_PVAR_154 s) = (term137 A _55215 GEN_PVAR_154 s).
Proof. exact (MK_COMB (@lem4597897 A _55215 s GEN_PVAR_154) (@lem4597889 A GEN_PVAR_154 s)). Qed.
Lemma lem4597899 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4597900 {A : Type'} (_55215 : type639 A) (GEN_PVAR_154 : A -> Prop) (s : A -> Prop) : (term138 A _55215 GEN_PVAR_154 s) = (term139 A _55215 GEN_PVAR_154 s).
Proof. exact (MK_COMB (@lem4597899) (@lem4597898 A _55215 GEN_PVAR_154 s)). Qed.
Lemma lem4597901 {A : Type'} (_55215 : type639 A) (GEN_PVAR_154 : A -> Prop) (s : A -> Prop) : (term140 A _55215 GEN_PVAR_154 s) = (term141 A _55215 GEN_PVAR_154 s).
Proof. exact (MK_COMB (@lem4597900 A _55215 GEN_PVAR_154 s) (@lem4597895 A _55215 GEN_PVAR_154 s)). Qed.
Lemma lem4597902 {A : Type'} (_55215 : type639 A) (GEN_PVAR_154 : A -> Prop) (s : A -> Prop) : ((_55215 s GEN_PVAR_154) = (term108 A GEN_PVAR_154 s)) = (term140 A _55215 GEN_PVAR_154 s).
Proof. exact (@lem17784 (_55215 s GEN_PVAR_154) (term108 A GEN_PVAR_154 s)). Qed.
Lemma lem4597903 {A : Type'} (_55215 : type639 A) (GEN_PVAR_154 : A -> Prop) (s : A -> Prop) : ((_55215 s GEN_PVAR_154) = (term108 A GEN_PVAR_154 s)) = (term141 A _55215 GEN_PVAR_154 s).
Proof. exact (TRANS (@lem4597902 A _55215 GEN_PVAR_154 s) (@lem4597901 A _55215 GEN_PVAR_154 s)). Qed.
Lemma lem4597904 {A : Type'} (_55215 : type639 A) (s : A -> Prop) : (term113 A _55215 s) = (term142 A _55215 s).
Proof. exact (fun_ext (fun GEN_PVAR_154 : A -> Prop => @lem4597903 A _55215 GEN_PVAR_154 s)). Qed.
Lemma lem4597905 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4597906 {A : Type'} (_55215 : type639 A) (s : A -> Prop) : (term114 A _55215 s) = (term143 A _55215 s).
Proof. exact (MK_COMB (@lem4597905 A) (@lem4597904 A _55215 s)). Qed.
Lemma lem4597907 {A : Type'} (_55215 : type639 A) : (term115 A _55215) = (term144 A _55215).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4597906 A _55215 s)). Qed.
Lemma lem4597908 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4597909 {A : Type'} (_55215 : type639 A) : (term116 A _55215) = (term145 A _55215).
Proof. exact (MK_COMB (@lem4597908 A) (@lem4597907 A _55215)). Qed.
Lemma lem4597915 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term146 A P Q) = (term147 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4597916 {A : Type'} (P : type686 A) (Q : type686 A) : (term148 A P Q) = (term149 A P Q).
Proof. exact (@lem4597915 (A -> Prop) P Q). Qed.
Lemma lem4597917 {A : Type'} (_55215 : type639 A) (s : A -> Prop) : (term150 A _55215 s) = (term151 A _55215 s).
Proof. exact (@lem4597916 A (term152 A _55215 s) (term153 A _55215 s)). Qed.
Lemma lem4597918 {A : Type'} (_55215 : type639 A) (GEN_PVAR_154 : A -> Prop) (s : A -> Prop) : (term154 A _55215 s GEN_PVAR_154) = (term137 A _55215 GEN_PVAR_154 s).
Proof. exact (eq_refl (term154 A _55215 s GEN_PVAR_154)). Qed.
Lemma lem4597919 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4597920 {A : Type'} (_55215 : type639 A) (GEN_PVAR_154 : A -> Prop) (s : A -> Prop) : (term155 A _55215 s GEN_PVAR_154) = (term139 A _55215 GEN_PVAR_154 s).
Proof. exact (MK_COMB (@lem4597919) (@lem4597918 A _55215 GEN_PVAR_154 s)). Qed.
Lemma lem4597921 {A : Type'} (_55215 : type639 A) (GEN_PVAR_154 : A -> Prop) (s : A -> Prop) : (term156 A _55215 s GEN_PVAR_154) = (term134 A _55215 GEN_PVAR_154 s).
Proof. exact (eq_refl (term156 A _55215 s GEN_PVAR_154)). Qed.
Lemma lem4597922 {A : Type'} (_55215 : type639 A) (GEN_PVAR_154 : A -> Prop) (s : A -> Prop) : (term157 A _55215 s GEN_PVAR_154) = (term141 A _55215 GEN_PVAR_154 s).
Proof. exact (MK_COMB (@lem4597920 A _55215 GEN_PVAR_154 s) (@lem4597921 A _55215 GEN_PVAR_154 s)). Qed.
Lemma lem4597923 {A : Type'} (_55215 : type639 A) (s : A -> Prop) : (term158 A _55215 s) = (term142 A _55215 s).
Proof. exact (fun_ext (fun GEN_PVAR_154 : A -> Prop => @lem4597922 A _55215 GEN_PVAR_154 s)). Qed.
Lemma lem4597924 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4597925 {A : Type'} (_55215 : type639 A) (s : A -> Prop) : (term150 A _55215 s) = (term143 A _55215 s).
Proof. exact (MK_COMB (@lem4597924 A) (@lem4597923 A _55215 s)). Qed.
Lemma lem4597926 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4597927 {A : Type'} (_55215 : type639 A) (s : A -> Prop) : (term159 A _55215 s) = (term160 A _55215 s).
Proof. exact (MK_COMB (@lem4597926) (@lem4597925 A _55215 s)). Qed.
Lemma lem4597928 {A : Type'} (_55215 : type639 A) (GEN_PVAR_154 : A -> Prop) (s : A -> Prop) : (term154 A _55215 s GEN_PVAR_154) = (term137 A _55215 GEN_PVAR_154 s).
Proof. exact (eq_refl (term154 A _55215 s GEN_PVAR_154)). Qed.
Lemma lem4597929 {A : Type'} (_55215 : type639 A) (s : A -> Prop) : (term161 A _55215 s) = (term152 A _55215 s).
Proof. exact (fun_ext (fun GEN_PVAR_154 : A -> Prop => @lem4597928 A _55215 GEN_PVAR_154 s)). Qed.
Lemma lem4597930 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4597931 {A : Type'} (_55215 : type639 A) (s : A -> Prop) : (term162 A _55215 s) = (term163 A _55215 s).
Proof. exact (MK_COMB (@lem4597930 A) (@lem4597929 A _55215 s)). Qed.
Lemma lem4597932 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4597933 {A : Type'} (_55215 : type639 A) (s : A -> Prop) : (term164 A _55215 s) = (term165 A _55215 s).
Proof. exact (MK_COMB (@lem4597932) (@lem4597931 A _55215 s)). Qed.
Lemma lem4597934 {A : Type'} (_55215 : type639 A) (GEN_PVAR_154 : A -> Prop) (s : A -> Prop) : (term156 A _55215 s GEN_PVAR_154) = (term134 A _55215 GEN_PVAR_154 s).
Proof. exact (eq_refl (term156 A _55215 s GEN_PVAR_154)). Qed.
Lemma lem4597935 {A : Type'} (_55215 : type639 A) (s : A -> Prop) : (term166 A _55215 s) = (term153 A _55215 s).
Proof. exact (fun_ext (fun GEN_PVAR_154 : A -> Prop => @lem4597934 A _55215 GEN_PVAR_154 s)). Qed.
Lemma lem4597936 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4597937 {A : Type'} (_55215 : type639 A) (s : A -> Prop) : (term167 A _55215 s) = (term168 A _55215 s).
Proof. exact (MK_COMB (@lem4597936 A) (@lem4597935 A _55215 s)). Qed.
Lemma lem4597938 {A : Type'} (_55215 : type639 A) (s : A -> Prop) : (term151 A _55215 s) = (term169 A _55215 s).
Proof. exact (MK_COMB (@lem4597933 A _55215 s) (@lem4597937 A _55215 s)). Qed.
Lemma lem4597939 {A : Type'} (_55215 : type639 A) (s : A -> Prop) : ((term150 A _55215 s) = (term151 A _55215 s)) = ((term143 A _55215 s) = (term169 A _55215 s)).
Proof. exact (MK_COMB (@lem4597927 A _55215 s) (@lem4597938 A _55215 s)). Qed.
Lemma lem4597940 {A : Type'} (_55215 : type639 A) (s : A -> Prop) : (term143 A _55215 s) = (term169 A _55215 s).
Proof. exact (EQ_MP (@lem4597939 A _55215 s) (@lem4597917 A _55215 s)). Qed.
Lemma lem4598045 {A : Type'} (_55215 : type639 A) : (term144 A _55215) = (term170 A _55215).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4597940 A _55215 s)). Qed.
Lemma lem4598046 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4598047 {A : Type'} (_55215 : type639 A) : (term145 A _55215) = (term171 A _55215).
Proof. exact (MK_COMB (@lem4598046 A) (@lem4598045 A _55215)). Qed.
Lemma lem4598049 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term146 A P Q) = (term147 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4598050 {A : Type'} (P : type686 A) (Q : type686 A) : (term148 A P Q) = (term149 A P Q).
Proof. exact (@lem4598049 (A -> Prop) P Q). Qed.
Lemma lem4598051 {A : Type'} (_55215 : type639 A) : (term172 A _55215) = (term173 A _55215).
Proof. exact (@lem4598050 A (term174 A _55215) (term175 A _55215)). Qed.
Lemma lem4598052 {A : Type'} (_55215 : type639 A) (s : A -> Prop) : (term176 A _55215 s) = (term163 A _55215 s).
Proof. exact (eq_refl (term176 A _55215 s)). Qed.
Lemma lem4598053 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4598054 {A : Type'} (_55215 : type639 A) (s : A -> Prop) : (term177 A _55215 s) = (term165 A _55215 s).
Proof. exact (MK_COMB (@lem4598053) (@lem4598052 A _55215 s)). Qed.
Lemma lem4598055 {A : Type'} (_55215 : type639 A) (s : A -> Prop) : (term178 A _55215 s) = (term168 A _55215 s).
Proof. exact (eq_refl (term178 A _55215 s)). Qed.
Lemma lem4598056 {A : Type'} (_55215 : type639 A) (s : A -> Prop) : (term179 A _55215 s) = (term169 A _55215 s).
Proof. exact (MK_COMB (@lem4598054 A _55215 s) (@lem4598055 A _55215 s)). Qed.
Lemma lem4598057 {A : Type'} (_55215 : type639 A) : (term180 A _55215) = (term170 A _55215).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4598056 A _55215 s)). Qed.
Lemma lem4598058 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4598059 {A : Type'} (_55215 : type639 A) : (term172 A _55215) = (term171 A _55215).
Proof. exact (MK_COMB (@lem4598058 A) (@lem4598057 A _55215)). Qed.
Lemma lem4598060 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4598061 {A : Type'} (_55215 : type639 A) : (term181 A _55215) = (term182 A _55215).
Proof. exact (MK_COMB (@lem4598060) (@lem4598059 A _55215)). Qed.
Lemma lem4598062 {A : Type'} (_55215 : type639 A) (s : A -> Prop) : (term176 A _55215 s) = (term163 A _55215 s).
Proof. exact (eq_refl (term176 A _55215 s)). Qed.
Lemma lem4598063 {A : Type'} (_55215 : type639 A) : (term183 A _55215) = (term174 A _55215).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4598062 A _55215 s)). Qed.
Lemma lem4598064 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4598065 {A : Type'} (_55215 : type639 A) : (term184 A _55215) = (term185 A _55215).
Proof. exact (MK_COMB (@lem4598064 A) (@lem4598063 A _55215)). Qed.
Lemma lem4598066 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4598067 {A : Type'} (_55215 : type639 A) : (term186 A _55215) = (term187 A _55215).
Proof. exact (MK_COMB (@lem4598066) (@lem4598065 A _55215)). Qed.
Lemma lem4598068 {A : Type'} (_55215 : type639 A) (s : A -> Prop) : (term178 A _55215 s) = (term168 A _55215 s).
Proof. exact (eq_refl (term178 A _55215 s)). Qed.
Lemma lem4598069 {A : Type'} (_55215 : type639 A) : (term188 A _55215) = (term175 A _55215).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4598068 A _55215 s)). Qed.
Lemma lem4598070 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4598071 {A : Type'} (_55215 : type639 A) : (term189 A _55215) = (term190 A _55215).
Proof. exact (MK_COMB (@lem4598070 A) (@lem4598069 A _55215)). Qed.
Lemma lem4598072 {A : Type'} (_55215 : type639 A) : (term173 A _55215) = (term191 A _55215).
Proof. exact (MK_COMB (@lem4598067 A _55215) (@lem4598071 A _55215)). Qed.
Lemma lem4598073 {A : Type'} (_55215 : type639 A) : ((term172 A _55215) = (term173 A _55215)) = ((term171 A _55215) = (term191 A _55215)).
Proof. exact (MK_COMB (@lem4598061 A _55215) (@lem4598072 A _55215)). Qed.
Lemma lem4598074 {A : Type'} (_55215 : type639 A) : (term171 A _55215) = (term191 A _55215).
Proof. exact (EQ_MP (@lem4598073 A _55215) (@lem4598051 A _55215)). Qed.
Lemma lem4598187 {A : Type'} (_55215 : type639 A) : (term145 A _55215) = (term191 A _55215).
Proof. exact (TRANS (@lem4598047 A _55215) (@lem4598074 A _55215)). Qed.
Lemma lem4598189 {A : Type'} (P : Prop) (Q : A -> Prop) : (term192 A P Q) = (term193 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4598190 {A : Type'} (P : Prop) (Q : type686 A) : (term194 A P Q) = (term195 A P Q).
Proof. exact (@lem4598189 (A -> Prop) P Q). Qed.
Lemma lem4598191 {A : Type'} (_55215 : type639 A) (GEN_PVAR_154 : A -> Prop) (s : A -> Prop) : (term196 A _55215 GEN_PVAR_154 s) = (term197 A _55215 GEN_PVAR_154 s).
Proof. exact (@lem4598190 A (term198 A _55215 s GEN_PVAR_154) (term122 A GEN_PVAR_154 s)). Qed.
Lemma lem4598192 {A : Type'} (GEN_PVAR_154 : A -> Prop) (s : A -> Prop) (t : A -> Prop) : (term127 A GEN_PVAR_154 s t) = (term121 A GEN_PVAR_154 s t).
Proof. exact (eq_refl (term127 A GEN_PVAR_154 s t)). Qed.
Lemma lem4598193 {A : Type'} (GEN_PVAR_154 : A -> Prop) (s : A -> Prop) : (term199 A GEN_PVAR_154 s) = (term122 A GEN_PVAR_154 s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4598192 A GEN_PVAR_154 s t)). Qed.
Lemma lem4598194 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4598195 {A : Type'} (GEN_PVAR_154 : A -> Prop) (s : A -> Prop) : (term200 A GEN_PVAR_154 s) = (term108 A GEN_PVAR_154 s).
Proof. exact (MK_COMB (@lem4598194 A) (@lem4598193 A GEN_PVAR_154 s)). Qed.
Lemma lem4598196 {A : Type'} (_55215 : type639 A) (s : A -> Prop) (GEN_PVAR_154 : A -> Prop) : (term133 A _55215 s GEN_PVAR_154) = (term133 A _55215 s GEN_PVAR_154).
Proof. exact (eq_refl (term133 A _55215 s GEN_PVAR_154)). Qed.
Lemma lem4598197 {A : Type'} (_55215 : type639 A) (GEN_PVAR_154 : A -> Prop) (s : A -> Prop) : (term196 A _55215 GEN_PVAR_154 s) = (term134 A _55215 GEN_PVAR_154 s).
Proof. exact (MK_COMB (@lem4598196 A _55215 s GEN_PVAR_154) (@lem4598195 A GEN_PVAR_154 s)). Qed.
Lemma lem4598198 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4598199 {A : Type'} (_55215 : type639 A) (GEN_PVAR_154 : A -> Prop) (s : A -> Prop) : (term201 A _55215 GEN_PVAR_154 s) = (term202 A _55215 GEN_PVAR_154 s).
Proof. exact (MK_COMB (@lem4598198) (@lem4598197 A _55215 GEN_PVAR_154 s)). Qed.
Lemma lem4598200 {A : Type'} (GEN_PVAR_154 : A -> Prop) (s : A -> Prop) (t : A -> Prop) : (term127 A GEN_PVAR_154 s t) = (term121 A GEN_PVAR_154 s t).
Proof. exact (eq_refl (term127 A GEN_PVAR_154 s t)). Qed.
Lemma lem4598201 {A : Type'} (_55215 : type639 A) (s : A -> Prop) (GEN_PVAR_154 : A -> Prop) : (term133 A _55215 s GEN_PVAR_154) = (term133 A _55215 s GEN_PVAR_154).
Proof. exact (eq_refl (term133 A _55215 s GEN_PVAR_154)). Qed.
Lemma lem4598202 {A : Type'} (_55215 : type639 A) (GEN_PVAR_154 : A -> Prop) (s : A -> Prop) (t : A -> Prop) : (term203 A _55215 GEN_PVAR_154 s t) = (term204 A _55215 GEN_PVAR_154 s t).
Proof. exact (MK_COMB (@lem4598201 A _55215 s GEN_PVAR_154) (@lem4598200 A GEN_PVAR_154 s t)). Qed.
Lemma lem4598203 {A : Type'} (_55215 : type639 A) (GEN_PVAR_154 : A -> Prop) (s : A -> Prop) : (term205 A _55215 GEN_PVAR_154 s) = (term206 A _55215 GEN_PVAR_154 s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4598202 A _55215 GEN_PVAR_154 s t)). Qed.
Lemma lem4598204 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4598205 {A : Type'} (_55215 : type639 A) (GEN_PVAR_154 : A -> Prop) (s : A -> Prop) : (term197 A _55215 GEN_PVAR_154 s) = (term207 A _55215 GEN_PVAR_154 s).
Proof. exact (MK_COMB (@lem4598204 A) (@lem4598203 A _55215 GEN_PVAR_154 s)). Qed.
Lemma lem4598206 {A : Type'} (_55215 : type639 A) (GEN_PVAR_154 : A -> Prop) (s : A -> Prop) : ((term196 A _55215 GEN_PVAR_154 s) = (term197 A _55215 GEN_PVAR_154 s)) = ((term134 A _55215 GEN_PVAR_154 s) = (term207 A _55215 GEN_PVAR_154 s)).
Proof. exact (MK_COMB (@lem4598199 A _55215 GEN_PVAR_154 s) (@lem4598205 A _55215 GEN_PVAR_154 s)). Qed.
Lemma lem4598207 {A : Type'} (_55215 : type639 A) (GEN_PVAR_154 : A -> Prop) (s : A -> Prop) : (term134 A _55215 GEN_PVAR_154 s) = (term207 A _55215 GEN_PVAR_154 s).
Proof. exact (EQ_MP (@lem4598206 A _55215 GEN_PVAR_154 s) (@lem4598191 A _55215 GEN_PVAR_154 s)). Qed.
Lemma lem4598208 {A : Type'} (_55215 : type639 A) (s : A -> Prop) : (term153 A _55215 s) = (term208 A _55215 s).
Proof. exact (fun_ext (fun GEN_PVAR_154 : A -> Prop => @lem4598207 A _55215 GEN_PVAR_154 s)). Qed.
Lemma lem4598209 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4598210 {A : Type'} (_55215 : type639 A) (s : A -> Prop) : (term168 A _55215 s) = (term209 A _55215 s).
Proof. exact (MK_COMB (@lem4598209 A) (@lem4598208 A _55215 s)). Qed.
Lemma lem4598212 {A B : Type'} (P : type1413 A B) : (term210 A B P) = (term211 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4598213 {A : Type'} (P : type639 A) : (term212 A P) = (term213 A P).
Proof. exact (@lem4598212 (A -> Prop) (A -> Prop) P). Qed.
Lemma lem4598214 {A : Type'} (_55215 : type639 A) (s : A -> Prop) : (term214 A _55215 s) = (term215 A _55215 s).
Proof. exact (@lem4598213 A (term216 A _55215 s)). Qed.
Lemma lem4598215 {A : Type'} (_55215 : type639 A) (GEN_PVAR_154 : A -> Prop) (s : A -> Prop) : (term217 A _55215 s GEN_PVAR_154) = (term206 A _55215 GEN_PVAR_154 s).
Proof. exact (eq_refl (term217 A _55215 s GEN_PVAR_154)). Qed.
Lemma lem4598216 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4598217 {A : Type'} (_55215 : type639 A) (GEN_PVAR_154 : A -> Prop) (s : A -> Prop) (t : A -> Prop) : (term218 A _55215 s GEN_PVAR_154 t) = (term219 A _55215 GEN_PVAR_154 s t).
Proof. exact (MK_COMB (@lem4598215 A _55215 GEN_PVAR_154 s) (@lem4598216 A t)). Qed.
Lemma lem4598218 {A : Type'} (_55215 : type639 A) (GEN_PVAR_154 : A -> Prop) (s : A -> Prop) (t : A -> Prop) : (term219 A _55215 GEN_PVAR_154 s t) = (term204 A _55215 GEN_PVAR_154 s t).
Proof. exact (eq_refl (term219 A _55215 GEN_PVAR_154 s t)). Qed.
Lemma lem4598219 {A : Type'} (_55215 : type639 A) (GEN_PVAR_154 : A -> Prop) (s : A -> Prop) (t : A -> Prop) : (term218 A _55215 s GEN_PVAR_154 t) = (term204 A _55215 GEN_PVAR_154 s t).
Proof. exact (TRANS (@lem4598217 A _55215 GEN_PVAR_154 s t) (@lem4598218 A _55215 GEN_PVAR_154 s t)). Qed.
Lemma lem4598220 {A : Type'} (_55215 : type639 A) (GEN_PVAR_154 : A -> Prop) (s : A -> Prop) : (term220 A _55215 s GEN_PVAR_154) = (term206 A _55215 GEN_PVAR_154 s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4598219 A _55215 GEN_PVAR_154 s t)). Qed.
Lemma lem4598221 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4598222 {A : Type'} (_55215 : type639 A) (GEN_PVAR_154 : A -> Prop) (s : A -> Prop) : (term221 A _55215 s GEN_PVAR_154) = (term207 A _55215 GEN_PVAR_154 s).
Proof. exact (MK_COMB (@lem4598221 A) (@lem4598220 A _55215 GEN_PVAR_154 s)). Qed.
Lemma lem4598223 {A : Type'} (_55215 : type639 A) (s : A -> Prop) : (term222 A _55215 s) = (term208 A _55215 s).
Proof. exact (fun_ext (fun GEN_PVAR_154 : A -> Prop => @lem4598222 A _55215 GEN_PVAR_154 s)). Qed.
Lemma lem4598224 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4598225 {A : Type'} (_55215 : type639 A) (s : A -> Prop) : (term214 A _55215 s) = (term209 A _55215 s).
Proof. exact (MK_COMB (@lem4598224 A) (@lem4598223 A _55215 s)). Qed.
Lemma lem4598226 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4598227 {A : Type'} (_55215 : type639 A) (s : A -> Prop) : (term223 A _55215 s) = (term224 A _55215 s).
Proof. exact (MK_COMB (@lem4598226) (@lem4598225 A _55215 s)). Qed.
Lemma lem4598228 {A : Type'} (_55215 : type639 A) (GEN_PVAR_154 : A -> Prop) (s : A -> Prop) : (term217 A _55215 s GEN_PVAR_154) = (term206 A _55215 GEN_PVAR_154 s).
Proof. exact (eq_refl (term217 A _55215 s GEN_PVAR_154)). Qed.
Lemma lem4598229 {A : Type'} (t : type672 A) (GEN_PVAR_154 : A -> Prop) : (t GEN_PVAR_154) = (t GEN_PVAR_154).
Proof. exact (eq_refl (t GEN_PVAR_154)). Qed.
Lemma lem4598230 {A : Type'} (_55215 : type639 A) (s : A -> Prop) (t : type672 A) (GEN_PVAR_154 : A -> Prop) : (term225 A _55215 s t GEN_PVAR_154) = (term226 A _55215 s t GEN_PVAR_154).
Proof. exact (MK_COMB (@lem4598228 A _55215 GEN_PVAR_154 s) (@lem4598229 A t GEN_PVAR_154)). Qed.
Lemma lem4598231 {A : Type'} (_55215 : type639 A) (s : A -> Prop) (t : type672 A) (GEN_PVAR_154 : A -> Prop) : (term226 A _55215 s t GEN_PVAR_154) = (term227 A _55215 s t GEN_PVAR_154).
Proof. exact (eq_refl (term226 A _55215 s t GEN_PVAR_154)). Qed.
Lemma lem4598232 {A : Type'} (_55215 : type639 A) (s : A -> Prop) (t : type672 A) (GEN_PVAR_154 : A -> Prop) : (term225 A _55215 s t GEN_PVAR_154) = (term227 A _55215 s t GEN_PVAR_154).
Proof. exact (TRANS (@lem4598230 A _55215 s t GEN_PVAR_154) (@lem4598231 A _55215 s t GEN_PVAR_154)). Qed.
Lemma lem4598233 {A : Type'} (_55215 : type639 A) (s : A -> Prop) (t : type672 A) : (term228 A _55215 s t) = (term229 A _55215 s t).
Proof. exact (fun_ext (fun GEN_PVAR_154 : A -> Prop => @lem4598232 A _55215 s t GEN_PVAR_154)). Qed.
Lemma lem4598234 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4598235 {A : Type'} (_55215 : type639 A) (s : A -> Prop) (t : type672 A) : (term230 A _55215 s t) = (term231 A _55215 s t).
Proof. exact (MK_COMB (@lem4598234 A) (@lem4598233 A _55215 s t)). Qed.
Lemma lem4598236 {A : Type'} (_55215 : type639 A) (s : A -> Prop) : (term232 A _55215 s) = (term233 A _55215 s).
Proof. exact (fun_ext (fun t : type672 A => @lem4598235 A _55215 s t)). Qed.
Lemma lem4598237 {A : Type'} : (@ex ((A -> Prop) -> A -> Prop)) = (@ex ((A -> Prop) -> A -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A -> Prop))). Qed.
Lemma lem4598238 {A : Type'} (_55215 : type639 A) (s : A -> Prop) : (term215 A _55215 s) = (term234 A _55215 s).
Proof. exact (MK_COMB (@lem4598237 A) (@lem4598236 A _55215 s)). Qed.
Lemma lem4598239 {A : Type'} (_55215 : type639 A) (s : A -> Prop) : ((term214 A _55215 s) = (term215 A _55215 s)) = ((term209 A _55215 s) = (term234 A _55215 s)).
Proof. exact (MK_COMB (@lem4598227 A _55215 s) (@lem4598238 A _55215 s)). Qed.
Lemma lem4598240 {A : Type'} (_55215 : type639 A) (s : A -> Prop) : (term209 A _55215 s) = (term234 A _55215 s).
Proof. exact (EQ_MP (@lem4598239 A _55215 s) (@lem4598214 A _55215 s)). Qed.
Lemma lem4598241 {A : Type'} (_55215 : type639 A) (s : A -> Prop) : (term168 A _55215 s) = (term234 A _55215 s).
Proof. exact (TRANS (@lem4598210 A _55215 s) (@lem4598240 A _55215 s)). Qed.
Lemma lem4598242 {A : Type'} (_55215 : type639 A) : (term175 A _55215) = (term235 A _55215).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4598241 A _55215 s)). Qed.
Lemma lem4598243 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4598244 {A : Type'} (_55215 : type639 A) : (term190 A _55215) = (term236 A _55215).
Proof. exact (MK_COMB (@lem4598243 A) (@lem4598242 A _55215)). Qed.
Lemma lem4598246 {A B : Type'} (P : type1413 A B) : (term210 A B P) = (term211 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4598247 {A : Type'} (P : type596 A) : (term237 A P) = (term238 A P).
Proof. exact (@lem4598246 (A -> Prop) (type672 A) P). Qed.
Lemma lem4598248 {A : Type'} (_55215 : type639 A) : (term239 A _55215) = (term240 A _55215).
Proof. exact (@lem4598247 A (term241 A _55215)). Qed.
Lemma lem4598249 {A : Type'} (_55215 : type639 A) (s : A -> Prop) : (term242 A _55215 s) = (term233 A _55215 s).
Proof. exact (eq_refl (term242 A _55215 s)). Qed.
Lemma lem4598250 {A : Type'} (t : type672 A) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4598251 {A : Type'} (_55215 : type639 A) (s : A -> Prop) (t : type672 A) : (term243 A _55215 s t) = (term244 A _55215 s t).
Proof. exact (MK_COMB (@lem4598249 A _55215 s) (@lem4598250 A t)). Qed.
Lemma lem4598252 {A : Type'} (_55215 : type639 A) (s : A -> Prop) (t : type672 A) : (term244 A _55215 s t) = (term231 A _55215 s t).
Proof. exact (eq_refl (term244 A _55215 s t)). Qed.
Lemma lem4598253 {A : Type'} (_55215 : type639 A) (s : A -> Prop) (t : type672 A) : (term243 A _55215 s t) = (term231 A _55215 s t).
Proof. exact (TRANS (@lem4598251 A _55215 s t) (@lem4598252 A _55215 s t)). Qed.
Lemma lem4598254 {A : Type'} (_55215 : type639 A) (s : A -> Prop) : (term245 A _55215 s) = (term233 A _55215 s).
Proof. exact (fun_ext (fun t : type672 A => @lem4598253 A _55215 s t)). Qed.
Lemma lem4598255 {A : Type'} : (@ex ((A -> Prop) -> A -> Prop)) = (@ex ((A -> Prop) -> A -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A -> Prop))). Qed.
Lemma lem4598256 {A : Type'} (_55215 : type639 A) (s : A -> Prop) : (term246 A _55215 s) = (term234 A _55215 s).
Proof. exact (MK_COMB (@lem4598255 A) (@lem4598254 A _55215 s)). Qed.
Lemma lem4598257 {A : Type'} (_55215 : type639 A) : (term247 A _55215) = (term235 A _55215).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4598256 A _55215 s)). Qed.
Lemma lem4598258 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4598259 {A : Type'} (_55215 : type639 A) : (term239 A _55215) = (term236 A _55215).
Proof. exact (MK_COMB (@lem4598258 A) (@lem4598257 A _55215)). Qed.
Lemma lem4598260 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4598261 {A : Type'} (_55215 : type639 A) : (term248 A _55215) = (term249 A _55215).
Proof. exact (MK_COMB (@lem4598260) (@lem4598259 A _55215)). Qed.
Lemma lem4598262 {A : Type'} (_55215 : type639 A) (s : A -> Prop) : (term242 A _55215 s) = (term233 A _55215 s).
Proof. exact (eq_refl (term242 A _55215 s)). Qed.
Lemma lem4598263 {A : Type'} (t : type636 A) (s : A -> Prop) : (t s) = (t s).
Proof. exact (eq_refl (t s)). Qed.
Lemma lem4598264 {A : Type'} (_55215 : type639 A) (t : type636 A) (s : A -> Prop) : (term250 A _55215 t s) = (term251 A _55215 t s).
Proof. exact (MK_COMB (@lem4598262 A _55215 s) (@lem4598263 A t s)). Qed.
Lemma lem4598265 {A : Type'} (_55215 : type639 A) (t : type636 A) (s : A -> Prop) : (term251 A _55215 t s) = (term252 A _55215 t s).
Proof. exact (eq_refl (term251 A _55215 t s)). Qed.
Lemma lem4598266 {A : Type'} (_55215 : type639 A) (t : type636 A) (s : A -> Prop) : (term250 A _55215 t s) = (term252 A _55215 t s).
Proof. exact (TRANS (@lem4598264 A _55215 t s) (@lem4598265 A _55215 t s)). Qed.
Lemma lem4598267 {A : Type'} (_55215 : type639 A) (t : type636 A) : (term253 A _55215 t) = (term254 A _55215 t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4598266 A _55215 t s)). Qed.
Lemma lem4598268 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4598269 {A : Type'} (_55215 : type639 A) (t : type636 A) : (term255 A _55215 t) = (term256 A _55215 t).
Proof. exact (MK_COMB (@lem4598268 A) (@lem4598267 A _55215 t)). Qed.
Lemma lem4598270 {A : Type'} (_55215 : type639 A) : (term257 A _55215) = (term258 A _55215).
Proof. exact (fun_ext (fun t : type636 A => @lem4598269 A _55215 t)). Qed.
Lemma lem4598271 {A : Type'} : (@ex ((A -> Prop) -> (A -> Prop) -> A -> Prop)) = (@ex ((A -> Prop) -> (A -> Prop) -> A -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> Prop) -> A -> Prop))). Qed.
Lemma lem4598272 {A : Type'} (_55215 : type639 A) : (term240 A _55215) = (term259 A _55215).
Proof. exact (MK_COMB (@lem4598271 A) (@lem4598270 A _55215)). Qed.
Lemma lem4598273 {A : Type'} (_55215 : type639 A) : ((term239 A _55215) = (term240 A _55215)) = ((term236 A _55215) = (term259 A _55215)).
Proof. exact (MK_COMB (@lem4598261 A _55215) (@lem4598272 A _55215)). Qed.
Lemma lem4598274 {A : Type'} (_55215 : type639 A) : (term236 A _55215) = (term259 A _55215).
Proof. exact (EQ_MP (@lem4598273 A _55215) (@lem4598248 A _55215)). Qed.
Lemma lem4598275 {A : Type'} (_55215 : type639 A) : (term190 A _55215) = (term259 A _55215).
Proof. exact (TRANS (@lem4598244 A _55215) (@lem4598274 A _55215)). Qed.
Lemma lem4598276 {A : Type'} (_55215 : type639 A) : (term187 A _55215) = (term187 A _55215).
Proof. exact (eq_refl (term187 A _55215)). Qed.
Lemma lem4598277 {A : Type'} (_55215 : type639 A) : (term191 A _55215) = (term260 A _55215).
Proof. exact (MK_COMB (@lem4598276 A _55215) (@lem4598275 A _55215)). Qed.
Lemma lem4598279 {A : Type'} (P : Prop) (Q : A -> Prop) : (term261 A P Q) = (term262 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4598280 {A : Type'} (P : Prop) (Q : type138 A) : (term263 A P Q) = (term264 A P Q).
Proof. exact (@lem4598279 (type636 A) P Q). Qed.
Lemma lem4598281 {A : Type'} (_55215 : type639 A) : (term265 A _55215) = (term266 A _55215).
Proof. exact (@lem4598280 A (term185 A _55215) (term258 A _55215)). Qed.
Lemma lem4598282 {A : Type'} (_55215 : type639 A) (t : type636 A) : (term267 A _55215 t) = (term256 A _55215 t).
Proof. exact (eq_refl (term267 A _55215 t)). Qed.
Lemma lem4598283 {A : Type'} (_55215 : type639 A) : (term268 A _55215) = (term258 A _55215).
Proof. exact (fun_ext (fun t : type636 A => @lem4598282 A _55215 t)). Qed.
Lemma lem4598284 {A : Type'} : (@ex ((A -> Prop) -> (A -> Prop) -> A -> Prop)) = (@ex ((A -> Prop) -> (A -> Prop) -> A -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> Prop) -> A -> Prop))). Qed.
Lemma lem4598285 {A : Type'} (_55215 : type639 A) : (term269 A _55215) = (term259 A _55215).
Proof. exact (MK_COMB (@lem4598284 A) (@lem4598283 A _55215)). Qed.
Lemma lem4598286 {A : Type'} (_55215 : type639 A) : (term187 A _55215) = (term187 A _55215).
Proof. exact (eq_refl (term187 A _55215)). Qed.
Lemma lem4598287 {A : Type'} (_55215 : type639 A) : (term265 A _55215) = (term260 A _55215).
Proof. exact (MK_COMB (@lem4598286 A _55215) (@lem4598285 A _55215)). Qed.
Lemma lem4598288 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4598289 {A : Type'} (_55215 : type639 A) : (term270 A _55215) = (term271 A _55215).
Proof. exact (MK_COMB (@lem4598288) (@lem4598287 A _55215)). Qed.
Lemma lem4598290 {A : Type'} (_55215 : type639 A) (t : type636 A) : (term267 A _55215 t) = (term256 A _55215 t).
Proof. exact (eq_refl (term267 A _55215 t)). Qed.
Lemma lem4598291 {A : Type'} (_55215 : type639 A) : (term187 A _55215) = (term187 A _55215).
Proof. exact (eq_refl (term187 A _55215)). Qed.
Lemma lem4598292 {A : Type'} (_55215 : type639 A) (t : type636 A) : (term272 A _55215 t) = (term273 A _55215 t).
Proof. exact (MK_COMB (@lem4598291 A _55215) (@lem4598290 A _55215 t)). Qed.
Lemma lem4598293 {A : Type'} (_55215 : type639 A) : (term274 A _55215) = (term275 A _55215).
Proof. exact (fun_ext (fun t : type636 A => @lem4598292 A _55215 t)). Qed.
Lemma lem4598294 {A : Type'} : (@ex ((A -> Prop) -> (A -> Prop) -> A -> Prop)) = (@ex ((A -> Prop) -> (A -> Prop) -> A -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> Prop) -> A -> Prop))). Qed.
Lemma lem4598295 {A : Type'} (_55215 : type639 A) : (term266 A _55215) = (term276 A _55215).
Proof. exact (MK_COMB (@lem4598294 A) (@lem4598293 A _55215)). Qed.
Lemma lem4598296 {A : Type'} (_55215 : type639 A) : ((term265 A _55215) = (term266 A _55215)) = ((term260 A _55215) = (term276 A _55215)).
Proof. exact (MK_COMB (@lem4598289 A _55215) (@lem4598295 A _55215)). Qed.
Lemma lem4598297 {A : Type'} (_55215 : type639 A) : (term260 A _55215) = (term276 A _55215).
Proof. exact (EQ_MP (@lem4598296 A _55215) (@lem4598281 A _55215)). Qed.
Lemma lem4598298 {A : Type'} (_55215 : type639 A) : (term191 A _55215) = (term276 A _55215).
Proof. exact (TRANS (@lem4598277 A _55215) (@lem4598297 A _55215)). Qed.
Lemma lem4598299 {A : Type'} (_55215 : type639 A) : (term145 A _55215) = (term276 A _55215).
Proof. exact (TRANS (@lem4598187 A _55215) (@lem4598298 A _55215)). Qed.
Lemma lem4598300 {A : Type'} (_55215 : type639 A) : (term116 A _55215) = (term276 A _55215).
Proof. exact (TRANS (@lem4597909 A _55215) (@lem4598299 A _55215)). Qed.
Lemma lem4598301 {A : Type'} (_55215 : type639 A) (h1 : term116 A _55215) : term276 A _55215.
Proof. exact (EQ_MP (@lem4598300 A _55215) (@lem4597870 A _55215 h1)). Qed.
Lemma lem4598308 {A : Type'} (_55215 : type639 A) (s : A -> Prop) : (term277 A _55215 s) = (term278 A _55215 s).
Proof. exact (@lem17362 (@FINITE A s) ((term58 A _55215 s) = (term56 A s))). Qed.
Lemma lem4598309 {A : Type'} (P : type686 A) : (term279 A P) = (term280 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem4598310 {A : Type'} (_55215 : type639 A) : (term67 A _55215) = (term281 A _55215).
Proof. exact (@lem4598309 A (term65 A _55215)). Qed.
Lemma lem4598311 {A : Type'} (_55215 : type639 A) (s : A -> Prop) : (term282 A _55215 s) = (term63 A _55215 s).
Proof. exact (eq_refl (term282 A _55215 s)). Qed.
Lemma lem4598312 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4598313 {A : Type'} (_55215 : type639 A) (s : A -> Prop) : (term283 A _55215 s) = (term277 A _55215 s).
Proof. exact (MK_COMB (@lem4598312) (@lem4598311 A _55215 s)). Qed.
Lemma lem4598314 {A : Type'} (_55215 : type639 A) (s : A -> Prop) : (term283 A _55215 s) = (term278 A _55215 s).
Proof. exact (TRANS (@lem4598313 A _55215 s) (@lem4598308 A _55215 s)). Qed.
Lemma lem4598315 {A : Type'} (_55215 : type639 A) : (term284 A _55215) = (term285 A _55215).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4598314 A _55215 s)). Qed.
Lemma lem4598316 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4598317 {A : Type'} (_55215 : type639 A) : (term281 A _55215) = (term286 A _55215).
Proof. exact (MK_COMB (@lem4598316 A) (@lem4598315 A _55215)). Qed.
Lemma lem4598350 {A : Type'} (_55215 : type639 A) : (term67 A _55215) = (term286 A _55215).
Proof. exact (TRANS (@lem4598310 A _55215) (@lem4598317 A _55215)). Qed.
Lemma lem4598351 {A : Type'} (_55215 : type639 A) (h1 : term67 A _55215) : term286 A _55215.
Proof. exact (EQ_MP (@lem4598350 A _55215) (@lem4597871 A _55215 h1)). Qed.
Lemma lem4598659 {A : Type'} (s : A -> Prop) (n : nat) : (term287 A s n) = (term288 A s n).
Proof. exact (@lem17045 (@FINITE A s) ((@CARD A s) = n)). Qed.
Lemma lem4598665 {A : Type'} (s : A -> Prop) (n : nat) : (term289 A s n) = (term289 A s n).
Proof. exact (eq_refl (term289 A s n)). Qed.
Lemma lem4598667 {A : Type'} (s : A -> Prop) (n : nat) : (term290 A s n) = (term290 A s n).
Proof. exact (eq_refl (term290 A s n)). Qed.
Lemma lem4598668 {A : Type'} (s : A -> Prop) (n : nat) : (term291 A s n) = (term292 A s n).
Proof. exact (MK_COMB (@lem4598667 A s n) (@lem4598659 A s n)). Qed.
Lemma lem4598669 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4598670 {A : Type'} (s : A -> Prop) (n : nat) : (term293 A s n) = (term294 A s n).
Proof. exact (MK_COMB (@lem4598669) (@lem4598668 A s n)). Qed.
Lemma lem4598671 {A : Type'} (s : A -> Prop) (n : nat) : (term295 A s n) = (term296 A s n).
Proof. exact (MK_COMB (@lem4598670 A s n) (@lem4598665 A s n)). Qed.
Lemma lem4598672 {A : Type'} (s : A -> Prop) (n : nat) : ((@HAS_SIZE A s n) = (term50 A s n)) = (term295 A s n).
Proof. exact (@lem17784 (@HAS_SIZE A s n) (term50 A s n)). Qed.
Lemma lem4598673 {A : Type'} (s : A -> Prop) (n : nat) : ((@HAS_SIZE A s n) = (term50 A s n)) = (term296 A s n).
Proof. exact (TRANS (@lem4598672 A s n) (@lem4598671 A s n)). Qed.
Lemma lem4598674 {A : Type'} (s : A -> Prop) : (term51 A s) = (term297 A s).
Proof. exact (fun_ext (fun n : nat => @lem4598673 A s n)). Qed.
Lemma lem4598675 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4598676 {A : Type'} (s : A -> Prop) : (term52 A s) = (term298 A s).
Proof. exact (MK_COMB (@lem4598675) (@lem4598674 A s)). Qed.
Lemma lem4598677 {A : Type'} : (term53 A) = (term299 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4598676 A s)). Qed.
Lemma lem4598678 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4598679 {A : Type'} : (term5 A) = (term300 A).
Proof. exact (MK_COMB (@lem4598678 A) (@lem4598677 A)). Qed.
Lemma lem4598685 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term146 A P Q) = (term147 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4598686 (P : nat -> Prop) (Q : nat -> Prop) : (term301 P Q) = (term302 P Q).
Proof. exact (@lem4598685 nat P Q). Qed.
Lemma lem4598687 {A : Type'} (s : A -> Prop) : (term303 A s) = (term304 A s).
Proof. exact (@lem4598686 (term305 A s) (term306 A s)). Qed.
Lemma lem4598688 {A : Type'} (s : A -> Prop) (n : nat) : (term307 A s n) = (term292 A s n).
Proof. exact (eq_refl (term307 A s n)). Qed.
Lemma lem4598689 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4598690 {A : Type'} (s : A -> Prop) (n : nat) : (term308 A s n) = (term294 A s n).
Proof. exact (MK_COMB (@lem4598689) (@lem4598688 A s n)). Qed.
Lemma lem4598691 {A : Type'} (s : A -> Prop) (n : nat) : (term309 A s n) = (term289 A s n).
Proof. exact (eq_refl (term309 A s n)). Qed.
Lemma lem4598692 {A : Type'} (s : A -> Prop) (n : nat) : (term310 A s n) = (term296 A s n).
Proof. exact (MK_COMB (@lem4598690 A s n) (@lem4598691 A s n)). Qed.
Lemma lem4598693 {A : Type'} (s : A -> Prop) : (term311 A s) = (term297 A s).
Proof. exact (fun_ext (fun n : nat => @lem4598692 A s n)). Qed.
Lemma lem4598694 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4598695 {A : Type'} (s : A -> Prop) : (term303 A s) = (term298 A s).
Proof. exact (MK_COMB (@lem4598694) (@lem4598693 A s)). Qed.
Lemma lem4598696 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4598697 {A : Type'} (s : A -> Prop) : (term312 A s) = (term313 A s).
Proof. exact (MK_COMB (@lem4598696) (@lem4598695 A s)). Qed.
Lemma lem4598698 {A : Type'} (s : A -> Prop) (n : nat) : (term307 A s n) = (term292 A s n).
Proof. exact (eq_refl (term307 A s n)). Qed.
Lemma lem4598699 {A : Type'} (s : A -> Prop) : (term314 A s) = (term305 A s).
Proof. exact (fun_ext (fun n : nat => @lem4598698 A s n)). Qed.
Lemma lem4598700 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4598701 {A : Type'} (s : A -> Prop) : (term315 A s) = (term316 A s).
Proof. exact (MK_COMB (@lem4598700) (@lem4598699 A s)). Qed.
Lemma lem4598702 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4598703 {A : Type'} (s : A -> Prop) : (term317 A s) = (term318 A s).
Proof. exact (MK_COMB (@lem4598702) (@lem4598701 A s)). Qed.
Lemma lem4598704 {A : Type'} (s : A -> Prop) (n : nat) : (term309 A s n) = (term289 A s n).
Proof. exact (eq_refl (term309 A s n)). Qed.
Lemma lem4598705 {A : Type'} (s : A -> Prop) : (term319 A s) = (term306 A s).
Proof. exact (fun_ext (fun n : nat => @lem4598704 A s n)). Qed.
Lemma lem4598706 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4598707 {A : Type'} (s : A -> Prop) : (term320 A s) = (term321 A s).
Proof. exact (MK_COMB (@lem4598706) (@lem4598705 A s)). Qed.
Lemma lem4598708 {A : Type'} (s : A -> Prop) : (term304 A s) = (term322 A s).
Proof. exact (MK_COMB (@lem4598703 A s) (@lem4598707 A s)). Qed.
Lemma lem4598709 {A : Type'} (s : A -> Prop) : ((term303 A s) = (term304 A s)) = ((term298 A s) = (term322 A s)).
Proof. exact (MK_COMB (@lem4598697 A s) (@lem4598708 A s)). Qed.
Lemma lem4598710 {A : Type'} (s : A -> Prop) : (term298 A s) = (term322 A s).
Proof. exact (EQ_MP (@lem4598709 A s) (@lem4598687 A s)). Qed.
Lemma lem4598807 {A : Type'} : (term299 A) = (term323 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4598710 A s)). Qed.
Lemma lem4598808 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4598809 {A : Type'} : (term300 A) = (term324 A).
Proof. exact (MK_COMB (@lem4598808 A) (@lem4598807 A)). Qed.
Lemma lem4598811 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term146 A P Q) = (term147 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4598812 {A : Type'} (P : type686 A) (Q : type686 A) : (term148 A P Q) = (term149 A P Q).
Proof. exact (@lem4598811 (A -> Prop) P Q). Qed.
Lemma lem4598813 {A : Type'} : (term325 A) = (term326 A).
Proof. exact (@lem4598812 A (term327 A) (term328 A)). Qed.
Lemma lem4598814 {A : Type'} (s : A -> Prop) : (term329 A s) = (term316 A s).
Proof. exact (eq_refl (term329 A s)). Qed.
Lemma lem4598815 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4598816 {A : Type'} (s : A -> Prop) : (term330 A s) = (term318 A s).
Proof. exact (MK_COMB (@lem4598815) (@lem4598814 A s)). Qed.
Lemma lem4598817 {A : Type'} (s : A -> Prop) : (term331 A s) = (term321 A s).
Proof. exact (eq_refl (term331 A s)). Qed.
Lemma lem4598818 {A : Type'} (s : A -> Prop) : (term332 A s) = (term322 A s).
Proof. exact (MK_COMB (@lem4598816 A s) (@lem4598817 A s)). Qed.
Lemma lem4598819 {A : Type'} : (term333 A) = (term323 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4598818 A s)). Qed.
Lemma lem4598820 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4598821 {A : Type'} : (term325 A) = (term324 A).
Proof. exact (MK_COMB (@lem4598820 A) (@lem4598819 A)). Qed.
Lemma lem4598822 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4598823 {A : Type'} : (term334 A) = (term335 A).
Proof. exact (MK_COMB (@lem4598822) (@lem4598821 A)). Qed.
Lemma lem4598824 {A : Type'} (s : A -> Prop) : (term329 A s) = (term316 A s).
Proof. exact (eq_refl (term329 A s)). Qed.
Lemma lem4598825 {A : Type'} : (term336 A) = (term327 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4598824 A s)). Qed.
Lemma lem4598826 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4598827 {A : Type'} : (term337 A) = (term338 A).
Proof. exact (MK_COMB (@lem4598826 A) (@lem4598825 A)). Qed.
Lemma lem4598828 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4598829 {A : Type'} : (term339 A) = (term340 A).
Proof. exact (MK_COMB (@lem4598828) (@lem4598827 A)). Qed.
Lemma lem4598830 {A : Type'} (s : A -> Prop) : (term331 A s) = (term321 A s).
Proof. exact (eq_refl (term331 A s)). Qed.
Lemma lem4598831 {A : Type'} : (term341 A) = (term328 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4598830 A s)). Qed.
Lemma lem4598832 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4598833 {A : Type'} : (term342 A) = (term343 A).
Proof. exact (MK_COMB (@lem4598832 A) (@lem4598831 A)). Qed.
Lemma lem4598834 {A : Type'} : (term326 A) = (term344 A).
Proof. exact (MK_COMB (@lem4598829 A) (@lem4598833 A)). Qed.
Lemma lem4598835 {A : Type'} : ((term325 A) = (term326 A)) = ((term324 A) = (term344 A)).
Proof. exact (MK_COMB (@lem4598823 A) (@lem4598834 A)). Qed.
Lemma lem4598836 {A : Type'} : (term324 A) = (term344 A).
Proof. exact (EQ_MP (@lem4598835 A) (@lem4598813 A)). Qed.
Lemma lem4598943 {A : Type'} : (term300 A) = (term344 A).
Proof. exact (TRANS (@lem4598809 A) (@lem4598836 A)). Qed.
Lemma lem4598944 {A : Type'} : (term5 A) = (term344 A).
Proof. exact (TRANS (@lem4598679 A) (@lem4598943 A)). Qed.
Lemma lem4598945 {A : Type'} (h1 : term5 A) : term344 A.
Proof. exact (EQ_MP (@lem4598944 A) (@lem4597873 A h1)). Qed.
Lemma lem4598956 {A : Type'} (s : type686 A) (n : nat) : (term345 A s n) = (term346 A s n).
Proof. exact (@lem17045 (@FINITE (A -> Prop) s) ((@CARD (A -> Prop) s) = n)). Qed.
Lemma lem4598962 {A : Type'} (s : type686 A) (n : nat) : (term347 A s n) = (term347 A s n).
Proof. exact (eq_refl (term347 A s n)). Qed.
Lemma lem4598964 {A : Type'} (s : type686 A) (n : nat) : (term348 A s n) = (term348 A s n).
Proof. exact (eq_refl (term348 A s n)). Qed.
Lemma lem4598965 {A : Type'} (s : type686 A) (n : nat) : (term349 A s n) = (term350 A s n).
Proof. exact (MK_COMB (@lem4598964 A s n) (@lem4598956 A s n)). Qed.
Lemma lem4598966 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4598967 {A : Type'} (s : type686 A) (n : nat) : (term351 A s n) = (term352 A s n).
Proof. exact (MK_COMB (@lem4598966) (@lem4598965 A s n)). Qed.
Lemma lem4598968 {A : Type'} (s : type686 A) (n : nat) : (term353 A s n) = (term354 A s n).
Proof. exact (MK_COMB (@lem4598967 A s n) (@lem4598962 A s n)). Qed.
Lemma lem4598969 {A : Type'} (s : type686 A) (n : nat) : ((@HAS_SIZE (A -> Prop) s n) = (term45 A s n)) = (term353 A s n).
Proof. exact (@lem17784 (@HAS_SIZE (A -> Prop) s n) (term45 A s n)). Qed.
Lemma lem4598970 {A : Type'} (s : type686 A) (n : nat) : ((@HAS_SIZE (A -> Prop) s n) = (term45 A s n)) = (term354 A s n).
Proof. exact (TRANS (@lem4598969 A s n) (@lem4598968 A s n)). Qed.
Lemma lem4598971 {A : Type'} (s : type686 A) : (term46 A s) = (term355 A s).
Proof. exact (fun_ext (fun n : nat => @lem4598970 A s n)). Qed.
Lemma lem4598972 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4598973 {A : Type'} (s : type686 A) : (term47 A s) = (term356 A s).
Proof. exact (MK_COMB (@lem4598972) (@lem4598971 A s)). Qed.
Lemma lem4598974 {A : Type'} : (term48 A) = (term357 A).
Proof. exact (fun_ext (fun s : type686 A => @lem4598973 A s)). Qed.
Lemma lem4598975 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4598976 {A : Type'} : (term6 A) = (term358 A).
Proof. exact (MK_COMB (@lem4598975 A) (@lem4598974 A)). Qed.
Lemma lem4598982 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term146 A P Q) = (term147 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4598983 (P : nat -> Prop) (Q : nat -> Prop) : (term301 P Q) = (term302 P Q).
Proof. exact (@lem4598982 nat P Q). Qed.
Lemma lem4598984 {A : Type'} (s : type686 A) : (term359 A s) = (term360 A s).
Proof. exact (@lem4598983 (term361 A s) (term362 A s)). Qed.
Lemma lem4598985 {A : Type'} (s : type686 A) (n : nat) : (term363 A s n) = (term350 A s n).
Proof. exact (eq_refl (term363 A s n)). Qed.
Lemma lem4598986 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4598987 {A : Type'} (s : type686 A) (n : nat) : (term364 A s n) = (term352 A s n).
Proof. exact (MK_COMB (@lem4598986) (@lem4598985 A s n)). Qed.
Lemma lem4598988 {A : Type'} (s : type686 A) (n : nat) : (term365 A s n) = (term347 A s n).
Proof. exact (eq_refl (term365 A s n)). Qed.
Lemma lem4598989 {A : Type'} (s : type686 A) (n : nat) : (term366 A s n) = (term354 A s n).
Proof. exact (MK_COMB (@lem4598987 A s n) (@lem4598988 A s n)). Qed.
Lemma lem4598990 {A : Type'} (s : type686 A) : (term367 A s) = (term355 A s).
Proof. exact (fun_ext (fun n : nat => @lem4598989 A s n)). Qed.
Lemma lem4598991 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4598992 {A : Type'} (s : type686 A) : (term359 A s) = (term356 A s).
Proof. exact (MK_COMB (@lem4598991) (@lem4598990 A s)). Qed.
Lemma lem4598993 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4598994 {A : Type'} (s : type686 A) : (term368 A s) = (term369 A s).
Proof. exact (MK_COMB (@lem4598993) (@lem4598992 A s)). Qed.
Lemma lem4598995 {A : Type'} (s : type686 A) (n : nat) : (term363 A s n) = (term350 A s n).
Proof. exact (eq_refl (term363 A s n)). Qed.
Lemma lem4598996 {A : Type'} (s : type686 A) : (term370 A s) = (term361 A s).
Proof. exact (fun_ext (fun n : nat => @lem4598995 A s n)). Qed.
Lemma lem4598997 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4598998 {A : Type'} (s : type686 A) : (term371 A s) = (term372 A s).
Proof. exact (MK_COMB (@lem4598997) (@lem4598996 A s)). Qed.
Lemma lem4598999 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4599000 {A : Type'} (s : type686 A) : (term373 A s) = (term374 A s).
Proof. exact (MK_COMB (@lem4598999) (@lem4598998 A s)). Qed.
Lemma lem4599001 {A : Type'} (s : type686 A) (n : nat) : (term365 A s n) = (term347 A s n).
Proof. exact (eq_refl (term365 A s n)). Qed.
Lemma lem4599002 {A : Type'} (s : type686 A) : (term375 A s) = (term362 A s).
Proof. exact (fun_ext (fun n : nat => @lem4599001 A s n)). Qed.
Lemma lem4599003 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4599004 {A : Type'} (s : type686 A) : (term376 A s) = (term377 A s).
Proof. exact (MK_COMB (@lem4599003) (@lem4599002 A s)). Qed.
Lemma lem4599005 {A : Type'} (s : type686 A) : (term360 A s) = (term378 A s).
Proof. exact (MK_COMB (@lem4599000 A s) (@lem4599004 A s)). Qed.
Lemma lem4599006 {A : Type'} (s : type686 A) : ((term359 A s) = (term360 A s)) = ((term356 A s) = (term378 A s)).
Proof. exact (MK_COMB (@lem4598994 A s) (@lem4599005 A s)). Qed.
Lemma lem4599007 {A : Type'} (s : type686 A) : (term356 A s) = (term378 A s).
Proof. exact (EQ_MP (@lem4599006 A s) (@lem4598984 A s)). Qed.
Lemma lem4599104 {A : Type'} : (term357 A) = (term379 A).
Proof. exact (fun_ext (fun s : type686 A => @lem4599007 A s)). Qed.
Lemma lem4599105 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4599106 {A : Type'} : (term358 A) = (term380 A).
Proof. exact (MK_COMB (@lem4599105 A) (@lem4599104 A)). Qed.
Lemma lem4599108 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term146 A P Q) = (term147 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4599109 {A : Type'} (P : type180 A) (Q : type180 A) : (term381 A P Q) = (term382 A P Q).
Proof. exact (@lem4599108 (type686 A) P Q). Qed.
Lemma lem4599110 {A : Type'} : (term383 A) = (term384 A).
Proof. exact (@lem4599109 A (term385 A) (term386 A)). Qed.
Lemma lem4599111 {A : Type'} (s : type686 A) : (term387 A s) = (term372 A s).
Proof. exact (eq_refl (term387 A s)). Qed.
Lemma lem4599112 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4599113 {A : Type'} (s : type686 A) : (term388 A s) = (term374 A s).
Proof. exact (MK_COMB (@lem4599112) (@lem4599111 A s)). Qed.
Lemma lem4599114 {A : Type'} (s : type686 A) : (term389 A s) = (term377 A s).
Proof. exact (eq_refl (term389 A s)). Qed.
Lemma lem4599115 {A : Type'} (s : type686 A) : (term390 A s) = (term378 A s).
Proof. exact (MK_COMB (@lem4599113 A s) (@lem4599114 A s)). Qed.
Lemma lem4599116 {A : Type'} : (term391 A) = (term379 A).
Proof. exact (fun_ext (fun s : type686 A => @lem4599115 A s)). Qed.
Lemma lem4599117 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4599118 {A : Type'} : (term383 A) = (term380 A).
Proof. exact (MK_COMB (@lem4599117 A) (@lem4599116 A)). Qed.
Lemma lem4599119 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4599120 {A : Type'} : (term392 A) = (term393 A).
Proof. exact (MK_COMB (@lem4599119) (@lem4599118 A)). Qed.
Lemma lem4599121 {A : Type'} (s : type686 A) : (term387 A s) = (term372 A s).
Proof. exact (eq_refl (term387 A s)). Qed.
Lemma lem4599122 {A : Type'} : (term394 A) = (term385 A).
Proof. exact (fun_ext (fun s : type686 A => @lem4599121 A s)). Qed.
Lemma lem4599123 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4599124 {A : Type'} : (term395 A) = (term396 A).
Proof. exact (MK_COMB (@lem4599123 A) (@lem4599122 A)). Qed.
Lemma lem4599125 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4599126 {A : Type'} : (term397 A) = (term398 A).
Proof. exact (MK_COMB (@lem4599125) (@lem4599124 A)). Qed.
Lemma lem4599127 {A : Type'} (s : type686 A) : (term389 A s) = (term377 A s).
Proof. exact (eq_refl (term389 A s)). Qed.
Lemma lem4599128 {A : Type'} : (term399 A) = (term386 A).
Proof. exact (fun_ext (fun s : type686 A => @lem4599127 A s)). Qed.
Lemma lem4599129 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4599130 {A : Type'} : (term400 A) = (term401 A).
Proof. exact (MK_COMB (@lem4599129 A) (@lem4599128 A)). Qed.
Lemma lem4599131 {A : Type'} : (term384 A) = (term402 A).
Proof. exact (MK_COMB (@lem4599126 A) (@lem4599130 A)). Qed.
Lemma lem4599132 {A : Type'} : ((term383 A) = (term384 A)) = ((term380 A) = (term402 A)).
Proof. exact (MK_COMB (@lem4599120 A) (@lem4599131 A)). Qed.
Lemma lem4599133 {A : Type'} : (term380 A) = (term402 A).
Proof. exact (EQ_MP (@lem4599132 A) (@lem4599110 A)). Qed.
Lemma lem4599240 {A : Type'} : (term358 A) = (term402 A).
Proof. exact (TRANS (@lem4599106 A) (@lem4599133 A)). Qed.
Lemma lem4599241 {A : Type'} : (term6 A) = (term402 A).
Proof. exact (TRANS (@lem4598976 A) (@lem4599240 A)). Qed.
Lemma lem4599242 {A : Type'} (h1 : term6 A) : term402 A.
Proof. exact (EQ_MP (@lem4599241 A) (@lem4597874 A h1)). Qed.
Lemma lem4599249 {A : Type'} (_55215 : type639 A) (s : A -> Prop) (n : nat) : (term36 A _55215 s n) = (term403 A _55215 s n).
Proof. exact (@lem17265 (@HAS_SIZE A s n) (term33 A _55215 s n)). Qed.
Lemma lem4599250 {A : Type'} (_55215 : type639 A) (s : A -> Prop) : (term38 A _55215 s) = (term404 A _55215 s).
Proof. exact (fun_ext (fun n : nat => @lem4599249 A _55215 s n)). Qed.
Lemma lem4599251 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4599252 {A : Type'} (_55215 : type639 A) (s : A -> Prop) : (term40 A _55215 s) = (term405 A _55215 s).
Proof. exact (MK_COMB (@lem4599251) (@lem4599250 A _55215 s)). Qed.
Lemma lem4599253 {A : Type'} (_55215 : type639 A) : (term42 A _55215) = (term406 A _55215).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4599252 A _55215 s)). Qed.
Lemma lem4599254 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4599311 {A : Type'} (_55215 : type639 A) : (term43 A _55215) = (term407 A _55215).
Proof. exact (MK_COMB (@lem4599254 A) (@lem4599253 A _55215)). Qed.
Lemma lem4599312 {A : Type'} (_55215 : type639 A) (h1 : term43 A _55215) : term407 A _55215.
Proof. exact (EQ_MP (@lem4599311 A _55215) (@lem4597875 A _55215 h1)). Qed.
Lemma lem4599401 {A : Type'} (s : A -> Prop) (n : nat) : (term289 A s n) = (term289 A s n).
Proof. exact (eq_refl (term289 A s n)). Qed.
Lemma lem4599402 {A : Type'} (s : A -> Prop) : (term306 A s) = (term306 A s).
Proof. exact (fun_ext (fun n : nat => @lem4599401 A s n)). Qed.
Lemma lem4599403 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4599404 {A : Type'} (s : A -> Prop) : (term321 A s) = (term321 A s).
Proof. exact (MK_COMB (@lem4599403) (@lem4599402 A s)). Qed.
Lemma lem4599405 {A : Type'} : (term328 A) = (term328 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4599404 A s)). Qed.
Lemma lem4599406 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4599407 {A : Type'} : (term343 A) = (term343 A).
Proof. exact (MK_COMB (@lem4599406 A) (@lem4599405 A)). Qed.
Lemma lem4599432 {A : Type'} (s : A -> Prop) (n : nat) : (term292 A s n) = (term292 A s n).
Proof. exact (eq_refl (term292 A s n)). Qed.
Lemma lem4599433 {A : Type'} (s : A -> Prop) : (term305 A s) = (term305 A s).
Proof. exact (fun_ext (fun n : nat => @lem4599432 A s n)). Qed.
Lemma lem4599434 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4599435 {A : Type'} (s : A -> Prop) : (term316 A s) = (term316 A s).
Proof. exact (MK_COMB (@lem4599434) (@lem4599433 A s)). Qed.
Lemma lem4599436 {A : Type'} : (term327 A) = (term327 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4599435 A s)). Qed.
Lemma lem4599437 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4599438 {A : Type'} : (term338 A) = (term338 A).
Proof. exact (MK_COMB (@lem4599437 A) (@lem4599436 A)). Qed.
Lemma lem4599439 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4599440 {A : Type'} : (term340 A) = (term340 A).
Proof. exact (MK_COMB (@lem4599439) (@lem4599438 A)). Qed.
Lemma lem4599441 {A : Type'} : (term344 A) = (term344 A).
Proof. exact (MK_COMB (@lem4599440 A) (@lem4599407 A)). Qed.
Lemma lem4599442 {A : Type'} (h1 : term5 A) : term344 A.
Proof. exact (EQ_MP (@lem4599441 A) (@lem4598945 A h1)). Qed.
Lemma lem4599465 {A : Type'} (s : type686 A) (n : nat) : (term347 A s n) = (term347 A s n).
Proof. exact (eq_refl (term347 A s n)). Qed.
Lemma lem4599466 {A : Type'} (s : type686 A) : (term362 A s) = (term362 A s).
Proof. exact (fun_ext (fun n : nat => @lem4599465 A s n)). Qed.
Lemma lem4599467 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4599468 {A : Type'} (s : type686 A) : (term377 A s) = (term377 A s).
Proof. exact (MK_COMB (@lem4599467) (@lem4599466 A s)). Qed.
Lemma lem4599469 {A : Type'} : (term386 A) = (term386 A).
Proof. exact (fun_ext (fun s : type686 A => @lem4599468 A s)). Qed.
Lemma lem4599470 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4599471 {A : Type'} : (term401 A) = (term401 A).
Proof. exact (MK_COMB (@lem4599470 A) (@lem4599469 A)). Qed.
Lemma lem4599496 {A : Type'} (s : type686 A) (n : nat) : (term350 A s n) = (term350 A s n).
Proof. exact (eq_refl (term350 A s n)). Qed.
Lemma lem4599497 {A : Type'} (s : type686 A) : (term361 A s) = (term361 A s).
Proof. exact (fun_ext (fun n : nat => @lem4599496 A s n)). Qed.
Lemma lem4599498 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4599499 {A : Type'} (s : type686 A) : (term372 A s) = (term372 A s).
Proof. exact (MK_COMB (@lem4599498) (@lem4599497 A s)). Qed.
Lemma lem4599500 {A : Type'} : (term385 A) = (term385 A).
Proof. exact (fun_ext (fun s : type686 A => @lem4599499 A s)). Qed.
Lemma lem4599501 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4599502 {A : Type'} : (term396 A) = (term396 A).
Proof. exact (MK_COMB (@lem4599501 A) (@lem4599500 A)). Qed.
Lemma lem4599503 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4599504 {A : Type'} : (term398 A) = (term398 A).
Proof. exact (MK_COMB (@lem4599503) (@lem4599502 A)). Qed.
Lemma lem4599505 {A : Type'} : (term402 A) = (term402 A).
Proof. exact (MK_COMB (@lem4599504 A) (@lem4599471 A)). Qed.
Lemma lem4599506 {A : Type'} (h1 : term6 A) : term402 A.
Proof. exact (EQ_MP (@lem4599505 A) (@lem4599242 A h1)). Qed.
Lemma lem4599535 {A : Type'} (_55215 : type639 A) (s : A -> Prop) (n : nat) : (term403 A _55215 s n) = (term403 A _55215 s n).
Proof. exact (eq_refl (term403 A _55215 s n)). Qed.
Lemma lem4599536 {A : Type'} (_55215 : type639 A) (s : A -> Prop) : (term404 A _55215 s) = (term404 A _55215 s).
Proof. exact (fun_ext (fun n : nat => @lem4599535 A _55215 s n)). Qed.
Lemma lem4599537 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4599538 {A : Type'} (_55215 : type639 A) (s : A -> Prop) : (term405 A _55215 s) = (term405 A _55215 s).
Proof. exact (MK_COMB (@lem4599537) (@lem4599536 A _55215 s)). Qed.
Lemma lem4599539 {A : Type'} (_55215 : type639 A) : (term406 A _55215) = (term406 A _55215).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4599538 A _55215 s)). Qed.
Lemma lem4599540 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4599541 {A : Type'} (_55215 : type639 A) : (term407 A _55215) = (term407 A _55215).
Proof. exact (MK_COMB (@lem4599540 A) (@lem4599539 A _55215)). Qed.
Lemma lem4599542 {A : Type'} (_55215 : type639 A) (h1 : term43 A _55215) : term407 A _55215.
Proof. exact (EQ_MP (@lem4599541 A _55215) (@lem4599312 A _55215 h1)). Qed.
Lemma lem4599574 {A : Type'} (_55215 : type639 A) (s : A -> Prop) (h1 : term278 A _55215 s) : term278 A _55215 s.
Proof. exact (h1). Qed.
Lemma lem4599658 {A : Type'} (h1 : term6 A) : term401 A.
Proof. exact (proj2 (@lem4599506 A h1)). Qed.
Lemma lem4599661 {A : Type'} (h1 : term5 A) : term338 A.
Proof. exact (proj1 (@lem4599442 A h1)). Qed.
Lemma lem4599671 {A : Type'} (_55215 : type639 A) (s : A -> Prop) (n : nat) : (term403 A _55215 s n) = (term403 A _55215 s n).
Proof. exact (eq_refl (term403 A _55215 s n)). Qed.
Lemma lem4599672 {A : Type'} (_55215 : type639 A) (s : A -> Prop) : (term404 A _55215 s) = (term404 A _55215 s).
Proof. exact (fun_ext (fun n : nat => @lem4599671 A _55215 s n)). Qed.
Lemma lem4599673 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4599674 {A : Type'} (_55215 : type639 A) (s : A -> Prop) : (term405 A _55215 s) = (term405 A _55215 s).
Proof. exact (MK_COMB (@lem4599673) (@lem4599672 A _55215 s)). Qed.
Lemma lem4599675 {A : Type'} (_55215 : type639 A) : (term406 A _55215) = (term406 A _55215).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4599674 A _55215 s)). Qed.
Lemma lem4599676 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4599678 {A : Type'} (_55215 : type639 A) : (term407 A _55215) = (term407 A _55215).
Proof. exact (MK_COMB (@lem4599676 A) (@lem4599675 A _55215)). Qed.
Lemma lem4599679 {A : Type'} (_55215 : type639 A) (h1 : term43 A _55215) : term407 A _55215.
Proof. exact (EQ_MP (@lem4599678 A _55215) (@lem4599542 A _55215 h1)). Qed.
Lemma lem4599787 {A : Type'} (s : type686 A) (n : nat) : (term347 A s n) = (term408 A s n).
Proof. exact (@lem19490 (@FINITE (A -> Prop) s) (term409 A s n) ((@CARD (A -> Prop) s) = n)). Qed.
Lemma lem4599788 {A : Type'} (s : type686 A) : (term362 A s) = (term410 A s).
Proof. exact (fun_ext (fun n : nat => @lem4599787 A s n)). Qed.
Lemma lem4599789 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4599790 {A : Type'} (s : type686 A) : (term377 A s) = (term411 A s).
Proof. exact (MK_COMB (@lem4599789) (@lem4599788 A s)). Qed.
Lemma lem4599791 {A : Type'} : (term386 A) = (term412 A).
Proof. exact (fun_ext (fun s : type686 A => @lem4599790 A s)). Qed.
Lemma lem4599792 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4599794 {A : Type'} : (term401 A) = (term413 A).
Proof. exact (MK_COMB (@lem4599792 A) (@lem4599791 A)). Qed.
Lemma lem4599795 {A : Type'} (h1 : term6 A) : term413 A.
Proof. exact (EQ_MP (@lem4599794 A) (@lem4599658 A h1)). Qed.
Lemma lem4599809 {A : Type'} (s : A -> Prop) (n : nat) : (term292 A s n) = (term292 A s n).
Proof. exact (eq_refl (term292 A s n)). Qed.
Lemma lem4599810 {A : Type'} (s : A -> Prop) : (term305 A s) = (term305 A s).
Proof. exact (fun_ext (fun n : nat => @lem4599809 A s n)). Qed.
Lemma lem4599811 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4599812 {A : Type'} (s : A -> Prop) : (term316 A s) = (term316 A s).
Proof. exact (MK_COMB (@lem4599811) (@lem4599810 A s)). Qed.
Lemma lem4599813 {A : Type'} : (term327 A) = (term327 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4599812 A s)). Qed.
Lemma lem4599814 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4599816 {A : Type'} : (term338 A) = (term338 A).
Proof. exact (MK_COMB (@lem4599814 A) (@lem4599813 A)). Qed.
Lemma lem4599817 {A : Type'} (h1 : term5 A) : term338 A.
Proof. exact (EQ_MP (@lem4599816 A) (@lem4599661 A h1)). Qed.
Lemma lem4599892 {A : Type'} (_55216 : A -> Prop) (_55215 : type639 A) (h1 : term43 A _55215) : term414 A _55215 _55216.
Proof. exact (@lem4599679 A _55215 h1 _55216). Qed.
Lemma lem4599893 {A : Type'} (_55215 : type639 A) (_55216 : A -> Prop) : (term414 A _55215 _55216) = (term405 A _55215 _55216).
Proof. exact (eq_refl (term414 A _55215 _55216)). Qed.
Lemma lem4599894 {A : Type'} (_55216 : A -> Prop) (_55215 : type639 A) (h1 : term43 A _55215) : term405 A _55215 _55216.
Proof. exact (EQ_MP (@lem4599893 A _55215 _55216) (@lem4599892 A _55216 _55215 h1)). Qed.
Lemma lem4599895 {A : Type'} (_55216 : A -> Prop) (_55217 : nat) (_55215 : type639 A) (h1 : term43 A _55215) : term415 A _55215 _55216 _55217.
Proof. exact (@lem4599894 A _55216 _55215 h1 _55217). Qed.
Lemma lem4599896 {A : Type'} (_55215 : type639 A) (_55216 : A -> Prop) (_55217 : nat) : (term415 A _55215 _55216 _55217) = (term403 A _55215 _55216 _55217).
Proof. exact (eq_refl (term415 A _55215 _55216 _55217)). Qed.
Lemma lem4599919 {A : Type'} (_55225 : type686 A) (h1 : term6 A) : term416 A _55225.
Proof. exact (@lem4599795 A h1 _55225). Qed.
Lemma lem4599920 {A : Type'} (_55225 : type686 A) : (term416 A _55225) = (term411 A _55225).
Proof. exact (eq_refl (term416 A _55225)). Qed.
Lemma lem4599921 {A : Type'} (_55225 : type686 A) (h1 : term6 A) : term411 A _55225.
Proof. exact (EQ_MP (@lem4599920 A _55225) (@lem4599919 A _55225 h1)). Qed.
Lemma lem4599922 {A : Type'} (_55225 : type686 A) (_55226 : nat) (h1 : term6 A) : term417 A _55225 _55226.
Proof. exact (@lem4599921 A _55225 h1 _55226). Qed.
Lemma lem4599923 {A : Type'} (_55225 : type686 A) (_55226 : nat) : (term417 A _55225 _55226) = (term408 A _55225 _55226).
Proof. exact (eq_refl (term417 A _55225 _55226)). Qed.
Lemma lem4599924 {A : Type'} (_55225 : type686 A) (_55226 : nat) (h1 : term6 A) : term408 A _55225 _55226.
Proof. exact (EQ_MP (@lem4599923 A _55225 _55226) (@lem4599922 A _55225 _55226 h1)). Qed.
Lemma lem4599925 {A : Type'} (_55227 : A -> Prop) (h1 : term5 A) : term329 A _55227.
Proof. exact (@lem4599817 A h1 _55227). Qed.
Lemma lem4599926 {A : Type'} (_55227 : A -> Prop) : (term329 A _55227) = (term316 A _55227).
Proof. exact (eq_refl (term329 A _55227)). Qed.
Lemma lem4599927 {A : Type'} (_55227 : A -> Prop) (h1 : term5 A) : term316 A _55227.
Proof. exact (EQ_MP (@lem4599926 A _55227) (@lem4599925 A _55227 h1)). Qed.
Lemma lem4599928 {A : Type'} (_55227 : A -> Prop) (_55228 : nat) (h1 : term5 A) : term307 A _55227 _55228.
Proof. exact (@lem4599927 A _55227 h1 _55228). Qed.
Lemma lem4599929 {A : Type'} (_55227 : A -> Prop) (_55228 : nat) : (term307 A _55227 _55228) = (term292 A _55227 _55228).
Proof. exact (eq_refl (term307 A _55227 _55228)). Qed.
Lemma lem4599960 {A : Type'} (_55216 : A -> Prop) (_55217 : nat) (_55215 : type639 A) (h1 : term43 A _55215) : term403 A _55215 _55216 _55217.
Proof. exact (EQ_MP (@lem4599896 A _55215 _55216 _55217) (@lem4599895 A _55216 _55217 _55215 h1)). Qed.
Lemma lem4599976 {A : Type'} (_55215 : type639 A) (s : A -> Prop) (h1 : term278 A _55215 s) : term418 A _55215 s.
Proof. exact (proj2 (@lem4599574 A _55215 s h1)). Qed.
Lemma lem4599996 {A : Type'} (_55227 : A -> Prop) (_55228 : nat) (h1 : term5 A) : term292 A _55227 _55228.
Proof. exact (EQ_MP (@lem4599929 A _55227 _55228) (@lem4599928 A _55227 _55228 h1)). Qed.
Lemma lem4600042 {A : Type'} (_55225 : type686 A) (_55226 : nat) (h1 : term6 A) : term419 A _55225 _55226.
Proof. exact (proj2 (@lem4599924 A _55225 _55226 h1)). Qed.
Lemma lem4600299 {A : Type'} (_55215 : type639 A) (s : A -> Prop) (h1 : term278 A _55215 s) : @FINITE A s.
Proof. exact (proj1 (@lem4599574 A _55215 s h1)). Qed.
Lemma lem4600300 {A : Type'} (_55215 : type639 A) (s : A -> Prop) (h1 : term278 A _55215 s) : term420 A s.
Proof. exact (fun h0 : term421 A s => @lem4600299 A _55215 s h1). Qed.
Lemma lem4600302 (p : Prop) : (term422 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4600303 {A : Type'} (s : A -> Prop) : (term420 A s) = (@FINITE A s).
Proof. exact (@lem4600302 (@FINITE A s)). Qed.
Lemma lem4600304 {A : Type'} (_55215 : type639 A) (s : A -> Prop) (h1 : term278 A _55215 s) : @FINITE A s.
Proof. exact (EQ_MP (@lem4600303 A s) (@lem4600300 A _55215 s h1)). Qed.
Lemma lem4600306 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem4600307 {A : Type'} (s : A -> Prop) : (@CARD A s) = (@CARD A s).
Proof. exact (@lem4600306 (@CARD A s)). Qed.
Lemma lem4600308 {A : Type'} (s : A -> Prop) : term423 A s.
Proof. exact (fun h0 : term424 A s => @lem4600307 A s). Qed.
Lemma lem4600310 (p : Prop) : (term422 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4600311 {A : Type'} (s : A -> Prop) : (term423 A s) = ((@CARD A s) = (@CARD A s)).
Proof. exact (@lem4600310 ((@CARD A s) = (@CARD A s))). Qed.
Lemma lem4600312 {A : Type'} (s : A -> Prop) : (@CARD A s) = (@CARD A s).
Proof. exact (EQ_MP (@lem4600311 A s) (@lem4600308 A s)). Qed.
Lemma lem4600314 (b : Prop) (a : Prop) : (a \/ b) = (term425 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4600315 {A : Type'} (_55227 : A -> Prop) (_55228 : nat) : (term292 A _55227 _55228) = (term426 A _55227 _55228).
Proof. exact (@lem4600314 (term288 A _55227 _55228) (@HAS_SIZE A _55227 _55228)). Qed.
Lemma lem4600317 (a : Prop) (b : Prop) : (term427 a b) = (term428 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4600318 {A : Type'} (_55227 : A -> Prop) (_55228 : nat) : (term429 A _55227 _55228) = (term430 A _55227 _55228).
Proof. exact (@lem4600317 (term421 A _55227) (term431 A _55227 _55228)). Qed.
Lemma lem4600320 (a : Prop) : (term432 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4600321 {A : Type'} (_55227 : A -> Prop) : (term433 A _55227) = (@FINITE A _55227).
Proof. exact (@lem4600320 (@FINITE A _55227)). Qed.
Lemma lem4600322 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4600323 {A : Type'} (_55227 : A -> Prop) : (term434 A _55227) = (term435 A _55227).
Proof. exact (MK_COMB (@lem4600322) (@lem4600321 A _55227)). Qed.
Lemma lem4600325 (a : Prop) : (term432 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4600326 {A : Type'} (_55227 : A -> Prop) (_55228 : nat) : (term436 A _55227 _55228) = ((@CARD A _55227) = _55228).
Proof. exact (@lem4600325 ((@CARD A _55227) = _55228)). Qed.
Lemma lem4600327 {A : Type'} (_55227 : A -> Prop) (_55228 : nat) : (term430 A _55227 _55228) = (term50 A _55227 _55228).
Proof. exact (MK_COMB (@lem4600323 A _55227) (@lem4600326 A _55227 _55228)). Qed.
Lemma lem4600328 {A : Type'} (_55227 : A -> Prop) (_55228 : nat) : (term429 A _55227 _55228) = (term50 A _55227 _55228).
Proof. exact (TRANS (@lem4600318 A _55227 _55228) (@lem4600327 A _55227 _55228)). Qed.
Lemma lem4600329 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4600330 {A : Type'} (_55227 : A -> Prop) (_55228 : nat) : (term437 A _55227 _55228) = (term438 A _55227 _55228).
Proof. exact (MK_COMB (@lem4600329) (@lem4600328 A _55227 _55228)). Qed.
Lemma lem4600331 {A : Type'} (_55227 : A -> Prop) (_55228 : nat) : (@HAS_SIZE A _55227 _55228) = (@HAS_SIZE A _55227 _55228).
Proof. exact (eq_refl (@HAS_SIZE A _55227 _55228)). Qed.
Lemma lem4600332 {A : Type'} (_55227 : A -> Prop) (_55228 : nat) : (term426 A _55227 _55228) = (term439 A _55227 _55228).
Proof. exact (MK_COMB (@lem4600330 A _55227 _55228) (@lem4600331 A _55227 _55228)). Qed.
Lemma lem4600333 {A : Type'} (_55227 : A -> Prop) (_55228 : nat) : (term292 A _55227 _55228) = (term439 A _55227 _55228).
Proof. exact (TRANS (@lem4600315 A _55227 _55228) (@lem4600332 A _55227 _55228)). Qed.
Lemma lem4600335 {A : Type'} (_55215 : type639 A) (s : A -> Prop) (h1 : term278 A _55215 s) : term440 A s.
Proof. exact (conj (@lem4600304 A _55215 s h1) (@lem4600312 A s)). Qed.
Lemma lem4600337 {A : Type'} (_55227 : A -> Prop) (_55228 : nat) (h1 : term5 A) : term439 A _55227 _55228.
Proof. exact (EQ_MP (@lem4600333 A _55227 _55228) (@lem4599996 A _55227 _55228 h1)). Qed.
Lemma lem4600338 {A : Type'} (_55227 : A -> Prop) (_55228 : nat) (h1 : term5 A) : term439 A _55227 _55228.
Proof. exact (@lem4600337 A _55227 _55228 h1). Qed.
Lemma lem4600339 {A : Type'} (s : A -> Prop) (h1 : term5 A) : term441 A s.
Proof. exact (@lem4600338 A s (@CARD A s) h1). Qed.
Lemma lem4600342 {A : Type'} (_55215 : type639 A) (s : A -> Prop) (h1 : term5 A) (h2 : term278 A _55215 s) : term442 A s.
Proof. exact (@lem4600339 A s h1 (@lem4600335 A _55215 s h2)). Qed.
Lemma lem4600343 {A : Type'} (_55215 : type639 A) (s : A -> Prop) (h1 : term5 A) (h2 : term278 A _55215 s) : term443 A s.
Proof. exact (fun h0 : term444 A s => @lem4600342 A _55215 s h1 h2). Qed.
Lemma lem4600345 (p : Prop) : (term422 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4600346 {A : Type'} (s : A -> Prop) : (term443 A s) = (term442 A s).
Proof. exact (@lem4600345 (term442 A s)). Qed.
Lemma lem4600347 {A : Type'} (_55215 : type639 A) (s : A -> Prop) (h1 : term5 A) (h2 : term278 A _55215 s) : term442 A s.
Proof. exact (EQ_MP (@lem4600346 A s) (@lem4600343 A _55215 s h1 h2)). Qed.
Lemma lem4600353 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4600354 {A : Type'} (_55215 : type639 A) (_55216 : A -> Prop) (_55217 : nat) : (term403 A _55215 _55216 _55217) = (term445 A _55215 _55216 _55217).
Proof. exact (@lem4600353 (term33 A _55215 _55216 _55217) (term446 A _55216 _55217)). Qed.
Lemma lem4600360 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4600361 {A : Type'} (_55215 : type639 A) (_55216 : A -> Prop) (_55217 : nat) : (term447 A _55215 _55216 _55217) = (term448 A _55215 _55216 _55217).
Proof. exact (MK_COMB (@lem4600360) (@lem4600354 A _55215 _55216 _55217)). Qed.
Lemma lem4600367 {A : Type'} (_55215 : type639 A) (_55216 : A -> Prop) (_55217 : nat) : (term445 A _55215 _55216 _55217) = (term445 A _55215 _55216 _55217).
Proof. exact (eq_refl (term445 A _55215 _55216 _55217)). Qed.
Lemma lem4600368 {A : Type'} (_55215 : type639 A) (_55216 : A -> Prop) (_55217 : nat) : ((term403 A _55215 _55216 _55217) = (term445 A _55215 _55216 _55217)) = ((term445 A _55215 _55216 _55217) = (term445 A _55215 _55216 _55217)).
Proof. exact (MK_COMB (@lem4600361 A _55215 _55216 _55217) (@lem4600367 A _55215 _55216 _55217)). Qed.
Lemma lem4600370 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4600371 (x : Prop) : (x = x) = True.
Proof. exact (@lem4600370 Prop x). Qed.
Lemma lem4600372 {A : Type'} (_55215 : type639 A) (_55216 : A -> Prop) (_55217 : nat) : ((term445 A _55215 _55216 _55217) = (term445 A _55215 _55216 _55217)) = True.
Proof. exact (@lem4600371 (term445 A _55215 _55216 _55217)). Qed.
Lemma lem4600373 {A : Type'} (_55215 : type639 A) (_55216 : A -> Prop) (_55217 : nat) : ((term403 A _55215 _55216 _55217) = (term445 A _55215 _55216 _55217)) = True.
Proof. exact (TRANS (@lem4600368 A _55215 _55216 _55217) (@lem4600372 A _55215 _55216 _55217)). Qed.
Lemma lem4600374 {A : Type'} (_55215 : type639 A) (_55216 : A -> Prop) (_55217 : nat) : True = ((term403 A _55215 _55216 _55217) = (term445 A _55215 _55216 _55217)).
Proof. exact (SYM (@lem4600373 A _55215 _55216 _55217)). Qed.
Lemma lem4600375 {A : Type'} (_55215 : type639 A) (_55216 : A -> Prop) (_55217 : nat) : (term403 A _55215 _55216 _55217) = (term445 A _55215 _55216 _55217).
Proof. exact (EQ_MP (@lem4600374 A _55215 _55216 _55217) (@lem0)). Qed.
Lemma lem4600376 {A : Type'} (_55216 : A -> Prop) (_55217 : nat) (_55215 : type639 A) (h1 : term43 A _55215) : term445 A _55215 _55216 _55217.
Proof. exact (EQ_MP (@lem4600375 A _55215 _55216 _55217) (@lem4599960 A _55216 _55217 _55215 h1)). Qed.
Lemma lem4600378 (b : Prop) (a : Prop) : (a \/ b) = (term425 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4600379 {A : Type'} (_55215 : type639 A) (_55216 : A -> Prop) (_55217 : nat) : (term445 A _55215 _55216 _55217) = (term449 A _55215 _55216 _55217).
Proof. exact (@lem4600378 (term446 A _55216 _55217) (term33 A _55215 _55216 _55217)). Qed.
Lemma lem4600381 (a : Prop) : (term432 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4600382 {A : Type'} (_55216 : A -> Prop) (_55217 : nat) : (term450 A _55216 _55217) = (@HAS_SIZE A _55216 _55217).
Proof. exact (@lem4600381 (@HAS_SIZE A _55216 _55217)). Qed.
Lemma lem4600383 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4600384 {A : Type'} (_55216 : A -> Prop) (_55217 : nat) : (term451 A _55216 _55217) = (term34 A _55216 _55217).
Proof. exact (MK_COMB (@lem4600383) (@lem4600382 A _55216 _55217)). Qed.
Lemma lem4600385 {A : Type'} (_55215 : type639 A) (_55216 : A -> Prop) (_55217 : nat) : (term33 A _55215 _55216 _55217) = (term33 A _55215 _55216 _55217).
Proof. exact (eq_refl (term33 A _55215 _55216 _55217)). Qed.
Lemma lem4600386 {A : Type'} (_55215 : type639 A) (_55216 : A -> Prop) (_55217 : nat) : (term449 A _55215 _55216 _55217) = (term36 A _55215 _55216 _55217).
Proof. exact (MK_COMB (@lem4600384 A _55216 _55217) (@lem4600385 A _55215 _55216 _55217)). Qed.
Lemma lem4600387 {A : Type'} (_55215 : type639 A) (_55216 : A -> Prop) (_55217 : nat) : (term445 A _55215 _55216 _55217) = (term36 A _55215 _55216 _55217).
Proof. exact (TRANS (@lem4600379 A _55215 _55216 _55217) (@lem4600386 A _55215 _55216 _55217)). Qed.
Lemma lem4600390 {A : Type'} (_55216 : A -> Prop) (_55217 : nat) (_55215 : type639 A) (h1 : term43 A _55215) : term36 A _55215 _55216 _55217.
Proof. exact (EQ_MP (@lem4600387 A _55215 _55216 _55217) (@lem4600376 A _55216 _55217 _55215 h1)). Qed.
Lemma lem4600391 {A : Type'} (_55216 : A -> Prop) (_55217 : nat) (_55215 : type639 A) (h1 : term43 A _55215) : term36 A _55215 _55216 _55217.
Proof. exact (@lem4600390 A _55216 _55217 _55215 h1). Qed.
Lemma lem4600392 {A : Type'} (s : A -> Prop) (_55215 : type639 A) (h1 : term43 A _55215) : term452 A _55215 s.
Proof. exact (@lem4600391 A s (@CARD A s) _55215 h1). Qed.
Lemma lem4600395 {A : Type'} (_55215 : type639 A) (s : A -> Prop) (h1 : term5 A) (h2 : term43 A _55215) (h3 : term278 A _55215 s) : term453 A _55215 s.
Proof. exact (@lem4600392 A s _55215 h2 (@lem4600347 A _55215 s h1 h3)). Qed.
Lemma lem4600396 {A : Type'} (_55215 : type639 A) (s : A -> Prop) (h1 : term5 A) (h2 : term43 A _55215) (h3 : term278 A _55215 s) : term454 A _55215 s.
Proof. exact (fun h0 : term455 A _55215 s => @lem4600395 A _55215 s h1 h2 h3). Qed.
Lemma lem4600398 (p : Prop) : (term422 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4600399 {A : Type'} (_55215 : type639 A) (s : A -> Prop) : (term454 A _55215 s) = (term453 A _55215 s).
Proof. exact (@lem4600398 (term453 A _55215 s)). Qed.
Lemma lem4600400 {A : Type'} (_55215 : type639 A) (s : A -> Prop) (h1 : term5 A) (h2 : term43 A _55215) (h3 : term278 A _55215 s) : term453 A _55215 s.
Proof. exact (EQ_MP (@lem4600399 A _55215 s) (@lem4600396 A _55215 s h1 h2 h3)). Qed.
Lemma lem4600406 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4600407 {A : Type'} (_55225 : type686 A) (_55226 : nat) : (term419 A _55225 _55226) = (term456 A _55225 _55226).
Proof. exact (@lem4600406 ((@CARD (A -> Prop) _55225) = _55226) (term409 A _55225 _55226)). Qed.
Lemma lem4600415 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4600416 {A : Type'} (_55225 : type686 A) (_55226 : nat) : (term457 A _55225 _55226) = (term458 A _55225 _55226).
Proof. exact (MK_COMB (@lem4600415) (@lem4600407 A _55225 _55226)). Qed.
Lemma lem4600424 {A : Type'} (_55225 : type686 A) (_55226 : nat) : (term456 A _55225 _55226) = (term456 A _55225 _55226).
Proof. exact (eq_refl (term456 A _55225 _55226)). Qed.
Lemma lem4600425 {A : Type'} (_55225 : type686 A) (_55226 : nat) : ((term419 A _55225 _55226) = (term456 A _55225 _55226)) = ((term456 A _55225 _55226) = (term456 A _55225 _55226)).
Proof. exact (MK_COMB (@lem4600416 A _55225 _55226) (@lem4600424 A _55225 _55226)). Qed.
Lemma lem4600427 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4600428 (x : Prop) : (x = x) = True.
Proof. exact (@lem4600427 Prop x). Qed.
Lemma lem4600429 {A : Type'} (_55225 : type686 A) (_55226 : nat) : ((term456 A _55225 _55226) = (term456 A _55225 _55226)) = True.
Proof. exact (@lem4600428 (term456 A _55225 _55226)). Qed.
Lemma lem4600430 {A : Type'} (_55225 : type686 A) (_55226 : nat) : ((term419 A _55225 _55226) = (term456 A _55225 _55226)) = True.
Proof. exact (TRANS (@lem4600425 A _55225 _55226) (@lem4600429 A _55225 _55226)). Qed.
Lemma lem4600431 {A : Type'} (_55225 : type686 A) (_55226 : nat) : True = ((term419 A _55225 _55226) = (term456 A _55225 _55226)).
Proof. exact (SYM (@lem4600430 A _55225 _55226)). Qed.
Lemma lem4600432 {A : Type'} (_55225 : type686 A) (_55226 : nat) : (term419 A _55225 _55226) = (term456 A _55225 _55226).
Proof. exact (EQ_MP (@lem4600431 A _55225 _55226) (@lem0)). Qed.
Lemma lem4600433 {A : Type'} (_55225 : type686 A) (_55226 : nat) (h1 : term6 A) : term456 A _55225 _55226.
Proof. exact (EQ_MP (@lem4600432 A _55225 _55226) (@lem4600042 A _55225 _55226 h1)). Qed.
Lemma lem4600435 (b : Prop) (a : Prop) : (a \/ b) = (term425 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4600436 {A : Type'} (_55225 : type686 A) (_55226 : nat) : (term456 A _55225 _55226) = (term459 A _55225 _55226).
Proof. exact (@lem4600435 (term409 A _55225 _55226) ((@CARD (A -> Prop) _55225) = _55226)). Qed.
Lemma lem4600438 (a : Prop) : (term432 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4600439 {A : Type'} (_55225 : type686 A) (_55226 : nat) : (term460 A _55225 _55226) = (@HAS_SIZE (A -> Prop) _55225 _55226).
Proof. exact (@lem4600438 (@HAS_SIZE (A -> Prop) _55225 _55226)). Qed.
Lemma lem4600440 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4600441 {A : Type'} (_55225 : type686 A) (_55226 : nat) : (term461 A _55225 _55226) = (term462 A _55225 _55226).
Proof. exact (MK_COMB (@lem4600440) (@lem4600439 A _55225 _55226)). Qed.
Lemma lem4600442 {A : Type'} (_55225 : type686 A) (_55226 : nat) : ((@CARD (A -> Prop) _55225) = _55226) = ((@CARD (A -> Prop) _55225) = _55226).
Proof. exact (eq_refl ((@CARD (A -> Prop) _55225) = _55226)). Qed.
Lemma lem4600443 {A : Type'} (_55225 : type686 A) (_55226 : nat) : (term459 A _55225 _55226) = (term463 A _55225 _55226).
Proof. exact (MK_COMB (@lem4600441 A _55225 _55226) (@lem4600442 A _55225 _55226)). Qed.
Lemma lem4600444 {A : Type'} (_55225 : type686 A) (_55226 : nat) : (term456 A _55225 _55226) = (term463 A _55225 _55226).
Proof. exact (TRANS (@lem4600436 A _55225 _55226) (@lem4600443 A _55225 _55226)). Qed.
Lemma lem4600447 {A : Type'} (_55225 : type686 A) (_55226 : nat) (h1 : term6 A) : term463 A _55225 _55226.
Proof. exact (EQ_MP (@lem4600444 A _55225 _55226) (@lem4600433 A _55225 _55226 h1)). Qed.
Lemma lem4600448 {A : Type'} (_55225 : type686 A) (_55226 : nat) (h1 : term6 A) : term463 A _55225 _55226.
Proof. exact (@lem4600447 A _55225 _55226 h1). Qed.
Lemma lem4600449 {A : Type'} (_55215 : type639 A) (s : A -> Prop) (h1 : term6 A) : term464 A _55215 s.
Proof. exact (@lem4600448 A (term29 A _55215 s) (term56 A s) h1). Qed.
Lemma lem4600452 {A : Type'} (_55215 : type639 A) (s : A -> Prop) (h1 : term5 A) (h2 : term43 A _55215) (h3 : term6 A) (h4 : term278 A _55215 s) : (term58 A _55215 s) = (term56 A s).
Proof. exact (@lem4600449 A _55215 s h3 (@lem4600400 A _55215 s h1 h2 h4)). Qed.
Lemma lem4600453 {A : Type'} (_55215 : type639 A) (s : A -> Prop) (h1 : term5 A) (h2 : term43 A _55215) (h3 : term6 A) (h4 : term278 A _55215 s) : term465 A _55215 s.
Proof. exact (fun h0 : term418 A _55215 s => @lem4600452 A _55215 s h1 h2 h3 h4). Qed.
Lemma lem4600455 (p : Prop) : (term422 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4600456 {A : Type'} (_55215 : type639 A) (s : A -> Prop) : (term465 A _55215 s) = ((term58 A _55215 s) = (term56 A s)).
Proof. exact (@lem4600455 ((term58 A _55215 s) = (term56 A s))). Qed.
Lemma lem4600457 {A : Type'} (_55215 : type639 A) (s : A -> Prop) (h1 : term5 A) (h2 : term43 A _55215) (h3 : term6 A) (h4 : term278 A _55215 s) : (term58 A _55215 s) = (term56 A s).
Proof. exact (EQ_MP (@lem4600456 A _55215 s) (@lem4600453 A _55215 s h1 h2 h3 h4)). Qed.
Lemma lem4600460 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4600462 {A : Type'} (_55215 : type639 A) (s : A -> Prop) : (term418 A _55215 s) = (term466 A _55215 s).
Proof. exact (@lem4600460 ((term58 A _55215 s) = (term56 A s))). Qed.
Lemma lem4600465 {A : Type'} (_55215 : type639 A) (s : A -> Prop) (h1 : term278 A _55215 s) : term466 A _55215 s.
Proof. exact (EQ_MP (@lem4600462 A _55215 s) (@lem4599976 A _55215 s h1)). Qed.
Lemma lem4600468 {A : Type'} (_55215 : type639 A) (s : A -> Prop) (h1 : term5 A) (h2 : term43 A _55215) (h3 : term6 A) (h4 : term278 A _55215 s) : False.
Proof. exact (@lem4600465 A _55215 s h4 (@lem4600457 A _55215 s h1 h2 h3 h4)). Qed.
Lemma lem4600469 {A : Type'} (_55215 : type639 A) (s : A -> Prop) (h1 : term5 A) (h2 : term43 A _55215) (h3 : term6 A) (h4 : term278 A _55215 s) : term467.
Proof. exact (fun h0 : ~ False => @lem4600468 A _55215 s h1 h2 h3 h4). Qed.
Lemma lem4600471 (p : Prop) : (term422 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4600472 : term467 = False.
Proof. exact (@lem4600471 False). Qed.
Lemma lem4600473 {A : Type'} (_55215 : type639 A) (s : A -> Prop) (h1 : term5 A) (h2 : term43 A _55215) (h3 : term6 A) (h4 : term278 A _55215 s) : False.
Proof. exact (EQ_MP (@lem4600472) (@lem4600469 A _55215 s h1 h2 h3 h4)). Qed.
Lemma lem4600474 {A : Type'} (_55215 : type639 A) (s : A -> Prop) (h1 : term5 A) (h2 : term43 A _55215) (h3 : term6 A) (h4 : term278 A _55215 s) : (term278 A _55215 s) = False.
Proof. exact (prop_ext (fun h5 : term278 A _55215 s => @lem4600473 A _55215 s h1 h2 h3 h4) (fun h5 : False => @lem4599574 A _55215 s h4)). Qed.
Lemma lem4600475 {A : Type'} (_55215 : type639 A) (s : A -> Prop) (h1 : term5 A) (h2 : term43 A _55215) (h3 : term6 A) (h4 : term278 A _55215 s) : False.
Proof. exact (EQ_MP (@lem4600474 A _55215 s h1 h2 h3 h4) (@lem4599574 A _55215 s h4)). Qed.
Lemma lem4600476 {A : Type'} (_55215 : type639 A) (s : A -> Prop) (h1 : term116 A _55215) (h2 : term5 A) (h3 : term43 A _55215) (h4 : term6 A) (h5 : term278 A _55215 s) : False.
Proof. exact (ex_elim (@lem4598301 A _55215 h1) (fun t : type636 A => fun h0 : term275 A _55215 t => @lem4600475 A _55215 s h2 h3 h4 h5)). Qed.
Lemma lem4600477 {A : Type'} (_55215 : type639 A) (h1 : term116 A _55215) (h2 : term5 A) (h3 : term43 A _55215) (h4 : term6 A) (h5 : term67 A _55215) : False.
Proof. exact (ex_elim (@lem4598351 A _55215 h5) (fun s : A -> Prop => fun h0 : term285 A _55215 s => @lem4600476 A _55215 s h1 h2 h3 h4 h0)). Qed.
Lemma lem4600478 {A : Type'} (_55215 : type639 A) (h1 : term116 A _55215) (h2 : term5 A) (h3 : term6 A) (h4 : term67 A _55215) : term468 A _55215.
Proof. exact (fun h0 : term43 A _55215 => @lem4600477 A _55215 h1 h2 h0 h3 h4). Qed.
Lemma lem4600479 {A : Type'} (_55215 : type639 A) : (term468 A _55215) = (term44 A _55215).
Proof. exact (@lem69 (term43 A _55215)). Qed.
Lemma lem4600480 {A : Type'} (_55215 : type639 A) (h1 : term116 A _55215) (h2 : term5 A) (h3 : term6 A) (h4 : term67 A _55215) : term44 A _55215.
Proof. exact (EQ_MP (@lem4600479 A _55215) (@lem4600478 A _55215 h1 h2 h3 h4)). Qed.
Lemma lem4600481 {A : Type'} (_55215 : type639 A) (h1 : term116 A _55215) (h2 : term5 A) (h3 : term67 A _55215) : term49 A _55215.
Proof. exact (fun h0 : term6 A => @lem4600480 A _55215 h1 h2 h0 h3). Qed.
Lemma lem4600482 {A : Type'} (_55215 : type639 A) (h1 : term116 A _55215) (h2 : term67 A _55215) : term54 A _55215.
Proof. exact (fun h0 : term5 A => @lem4600481 A _55215 h1 h0 h2). Qed.
Lemma lem4600483 {_100044 A : Type'} (_55215 : type639 A) (h1 : term116 A _55215) (h2 : term67 A _55215) : term55 _100044 A _55215.
Proof. exact (fun h0 : term5 _100044 => @lem4600482 A _55215 h1 h2). Qed.
Lemma lem4600484 {_100044 A : Type'} (_55215 : type639 A) (h1 : term116 A _55215) : term69 _100044 A _55215.
Proof. exact (fun h0 : term67 A _55215 => @lem4600483 _100044 A _55215 h1 h0). Qed.
Lemma lem4600485 {_100044 A : Type'} (_55215 : type639 A) : term118 _100044 A _55215.
Proof. exact (fun h0 : term116 A _55215 => @lem4600484 _100044 A _55215 h0). Qed.
Lemma lem4600490 {_100044 A : Type'} : term120 _100044 A.
Proof. exact (fun _55215 : type639 A => @lem4600485 _100044 A _55215). Qed.
Lemma lem4600491 {_100044 A : Type'} : term7 _100044 A.
Proof. exact (EQ_MP (@lem4597869 _100044 A) (@lem4600490 _100044 A)). Qed.
Lemma lem4600493 {_100044 A : Type'} : term7 _100044 A.
Proof. exact (@lem4597329 _100044 A (@lem4600491 _100044 A)). Qed.
Lemma lem4600494 {_100044 A : Type'} (h1 : term3 A) : term19 _100044 A.
Proof. exact (@lem4600493 _100044 A (@lem4597304 A h1)). Qed.
Lemma lem4600495 {A : Type'} (h1 : term3 A) : term17 A.
Proof. exact (@lem4600494 Prop A h1 (@lem3863773 Prop)). Qed.
Lemma lem4600496 {A : Type'} (h1 : term3 A) : term14 A.
Proof. exact (@lem4600495 A h1 (@lem4597309 A)). Qed.
Lemma lem4600497 {A : Type'} (h1 : term3 A) : term11 A.
Proof. exact (@lem4600496 A h1 (@lem4597310 A)). Qed.
Lemma lem4600498 {A : Type'} (h1 : term3 A) : False.
Proof. exact (@lem4600497 A h1 (@lem4597305 A)). Qed.
Lemma lem4600499 {A : Type'} (h1 : term3 A) : (term3 A) = False.
Proof. exact (prop_ext (fun h2 : term3 A => @lem4600498 A h1) (fun h2 : False => @lem4597304 A h1)). Qed.
Lemma lem4600500 {A : Type'} (h1 : term3 A) : False.
Proof. exact (EQ_MP (@lem4600499 A h1) (@lem4597304 A h1)). Qed.
Lemma lem4600501 {A : Type'} : term2 A.
Proof. exact (fun h0 : term3 A => @lem4600500 A h0). Qed.
Lemma lem4600502 {A : Type'} : term1 A.
Proof. exact (EQ_MP (@lem4597303 A) (@lem4600501 A)). Qed.
