Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_MUL_BOUND_term_abbrevs.
Require Import IN_DIFF_spec.
Require Import REAL_LE_RMUL_spec.
Require Import SING_SUBSET_spec.
Require Import SUM_LE_spec.
Require Import SUM_LMUL_spec.
Require Import SUM_SING_spec.
Require Import SUM_SUBSET_SIMPLE_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem7177446 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem7177447 {A : Type'} (u : A -> Prop) (h1 : term0 A) : term1 A u.
Proof. exact (@lem7177446 A h1 u). Qed.
Lemma lem7177448 {A : Type'} (u : A -> Prop) : (term1 A u) = (term2 A u).
Proof. exact (eq_refl (term1 A u)). Qed.
Lemma lem7177449 {A : Type'} (u : A -> Prop) (h1 : term0 A) : term2 A u.
Proof. exact (EQ_MP (@lem7177448 A u) (@lem7177447 A u h1)). Qed.
Lemma lem7177450 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term0 A) : term3 A u v.
Proof. exact (@lem7177449 A u h1 v). Qed.
Lemma lem7177451 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term3 A u v) = (term4 A u v).
Proof. exact (eq_refl (term3 A u v)). Qed.
Lemma lem7177452 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term0 A) : term4 A u v.
Proof. exact (EQ_MP (@lem7177451 A u v) (@lem7177450 A u v h1)). Qed.
Lemma lem7177453 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term0 A) : term5 A u v f.
Proof. exact (@lem7177452 A u v h1 f). Qed.
Lemma lem7177454 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term5 A u v f) = (term6 A u v f).
Proof. exact (eq_refl (term5 A u v f)). Qed.
Lemma lem7177455 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term0 A) : term6 A u v f.
Proof. exact (EQ_MP (@lem7177454 A u v f) (@lem7177453 A u v f h1)). Qed.
Lemma lem7177456 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term7 A v u f) : term7 A v u f.
Proof. exact (h1). Qed.
Lemma lem7177457 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term0 A) (h2 : term7 A v u f) : term8 A u v f.
Proof. exact (@lem7177455 A u v f h1 (@lem7177456 A v u f h2)). Qed.
Lemma lem7177458 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term7 A v u f) : term9 A u v f.
Proof. exact (fun h0 : term0 A => @lem7177457 A v u f h0 h1). Qed.
Lemma lem7177459 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem7177460 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term0 A) (h2 : term7 A v u f) : term8 A u v f.
Proof. exact (@lem7177458 A v u f h2 (@lem7177459 A h1)). Qed.
Lemma lem7177461 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term0 A) : term6 A u v f.
Proof. exact (fun h0 : term7 A v u f => @lem7177460 A v u f h1 h0). Qed.
Lemma lem7177462 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term0 A) : term4 A u v.
Proof. exact (fun f : A -> real => @lem7177461 A u v f h1). Qed.
Lemma lem7177463 {A : Type'} (u : A -> Prop) (h1 : term0 A) : term2 A u.
Proof. exact (fun v : A -> Prop => @lem7177462 A u v h1). Qed.
Lemma lem7177464 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (fun u : A -> Prop => @lem7177463 A u h1). Qed.
Lemma lem7177465 {A : Type'} : term10 A.
Proof. exact (fun h0 : term0 A => @lem7177464 A h0). Qed.
Lemma lem7177466 {A : Type'} : term0 A.
Proof. exact (@lem7177465 A (@lem7177445 A)). Qed.
Lemma lem7177467 {A : Type'} (u : A -> Prop) : term1 A u.
Proof. exact (@lem7177466 A u). Qed.
Lemma lem7177468 {A : Type'} (u : A -> Prop) : (term1 A u) = (term2 A u).
Proof. exact (eq_refl (term1 A u)). Qed.
Lemma lem7177469 {A : Type'} (u : A -> Prop) : term2 A u.
Proof. exact (EQ_MP (@lem7177468 A u) (@lem7177467 A u)). Qed.
Lemma lem7177470 {A : Type'} (u : A -> Prop) (v : A -> Prop) : term3 A u v.
Proof. exact (@lem7177469 A u v). Qed.
Lemma lem7177471 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term3 A u v) = (term4 A u v).
Proof. exact (eq_refl (term3 A u v)). Qed.
Lemma lem7177472 {A : Type'} (u : A -> Prop) (v : A -> Prop) : term4 A u v.
Proof. exact (EQ_MP (@lem7177471 A u v) (@lem7177470 A u v)). Qed.
Lemma lem7177473 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : term5 A u v f.
Proof. exact (@lem7177472 A u v f). Qed.
Lemma lem7177474 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term5 A u v f) = (term6 A u v f).
Proof. exact (eq_refl (term5 A u v f)). Qed.
Lemma lem7177478 {_133036 : Type'} (f : _133036 -> real) (x : _133036) (h1 : (term11 _133036 x f) = (f x)) : (term11 _133036 x f) = (f x).
Proof. exact (h1). Qed.
Lemma lem7177479 {_133036 : Type'} (f : _133036 -> real) (x : _133036) (h1 : (term11 _133036 x f) = (f x)) : (f x) = (term11 _133036 x f).
Proof. exact (SYM (@lem7177478 _133036 f x h1)). Qed.
Lemma lem7177480 {_133036 : Type'} (x : _133036) (f : _133036 -> real) (h1 : (f x) = (term11 _133036 x f)) : (f x) = (term11 _133036 x f).
Proof. exact (h1). Qed.
Lemma lem7177481 {_133036 : Type'} (x : _133036) (f : _133036 -> real) (h1 : (f x) = (term11 _133036 x f)) : (term11 _133036 x f) = (f x).
Proof. exact (SYM (@lem7177480 _133036 x f h1)). Qed.
Lemma lem7177482 {_133036 : Type'} (x : _133036) (f : _133036 -> real) : ((term11 _133036 x f) = (f x)) = ((f x) = (term11 _133036 x f)).
Proof. exact (prop_ext (fun h1 : (term11 _133036 x f) = (f x) => @lem7177479 _133036 f x h1) (fun h1 : (f x) = (term11 _133036 x f) => @lem7177481 _133036 x f h1)). Qed.
Lemma lem7177483 {_133036 : Type'} (f : _133036 -> real) : (term12 _133036 f) = (term13 _133036 f).
Proof. exact (fun_ext (fun x : _133036 => @lem7177482 _133036 x f)). Qed.
Lemma lem7177484 {_133036 : Type'} : (@all _133036) = (@all _133036).
Proof. exact (eq_refl (@all _133036)). Qed.
Lemma lem7177485 {_133036 : Type'} (f : _133036 -> real) : (term14 _133036 f) = (term15 _133036 f).
Proof. exact (MK_COMB (@lem7177484 _133036) (@lem7177483 _133036 f)). Qed.
Lemma lem7177486 {_133036 : Type'} : (term16 _133036) = (term17 _133036).
Proof. exact (fun_ext (fun f : _133036 -> real => @lem7177485 _133036 f)). Qed.
Lemma lem7177487 {_133036 : Type'} : (@all (_133036 -> real)) = (@all (_133036 -> real)).
Proof. exact (eq_refl (@all (_133036 -> real))). Qed.
Lemma lem7177488 {_133036 : Type'} : (term18 _133036) = (term19 _133036).
Proof. exact (MK_COMB (@lem7177487 _133036) (@lem7177486 _133036)). Qed.
Lemma lem7177489 {_133036 : Type'} : term19 _133036.
Proof. exact (EQ_MP (@lem7177488 _133036) (@lem7123532 _133036)). Qed.
Lemma lem7177490 {_133036 : Type'} (f : _133036 -> real) : term20 _133036 f.
Proof. exact (@lem7177489 _133036 f). Qed.
Lemma lem7177491 {_133036 : Type'} (f : _133036 -> real) : (term20 _133036 f) = (term15 _133036 f).
Proof. exact (eq_refl (term20 _133036 f)). Qed.
Lemma lem7177492 {_133036 : Type'} (f : _133036 -> real) : term15 _133036 f.
Proof. exact (EQ_MP (@lem7177491 _133036 f) (@lem7177490 _133036 f)). Qed.
Lemma lem7177493 {_133036 : Type'} (f : _133036 -> real) (x : _133036) : term21 _133036 f x.
Proof. exact (@lem7177492 _133036 f x). Qed.
Lemma lem7177494 {_133036 : Type'} (x : _133036) (f : _133036 -> real) : (term21 _133036 f x) = ((f x) = (term11 _133036 x f)).
Proof. exact (eq_refl (term21 _133036 f x)). Qed.
Lemma lem7177496 (h1 : term22) : term22.
Proof. exact (h1). Qed.
Lemma lem7177497 (x : real) (h1 : term22) : term23 x.
Proof. exact (@lem7177496 h1 x). Qed.
Lemma lem7177498 (x : real) : (term23 x) = (term24 x).
Proof. exact (eq_refl (term23 x)). Qed.
Lemma lem7177499 (x : real) (h1 : term22) : term24 x.
Proof. exact (EQ_MP (@lem7177498 x) (@lem7177497 x h1)). Qed.
Lemma lem7177500 (x : real) (y : real) (h1 : term22) : term25 x y.
Proof. exact (@lem7177499 x h1 y). Qed.
Lemma lem7177501 (x : real) (y : real) : (term25 x y) = (term26 x y).
Proof. exact (eq_refl (term25 x y)). Qed.
Lemma lem7177502 (x : real) (y : real) (h1 : term22) : term26 x y.
Proof. exact (EQ_MP (@lem7177501 x y) (@lem7177500 x y h1)). Qed.
Lemma lem7177503 (x : real) (y : real) (z : real) (h1 : term22) : term27 x y z.
Proof. exact (@lem7177502 x y h1 z). Qed.
Lemma lem7177504 (x : real) (y : real) (z : real) : (term27 x y z) = (term28 x y z).
Proof. exact (eq_refl (term27 x y z)). Qed.
Lemma lem7177505 (x : real) (y : real) (z : real) (h1 : term22) : term28 x y z.
Proof. exact (EQ_MP (@lem7177504 x y z) (@lem7177503 x y z h1)). Qed.
Lemma lem7177506 (x : real) (y : real) (z : real) (h1 : term29 x y z) : term29 x y z.
Proof. exact (h1). Qed.
Lemma lem7177507 (x : real) (y : real) (z : real) (h1 : term22) (h2 : term29 x y z) : term30 x y z.
Proof. exact (@lem7177505 x y z h1 (@lem7177506 x y z h2)). Qed.
Lemma lem7177508 (x : real) (y : real) (z : real) (h1 : term29 x y z) : term31 x y z.
Proof. exact (fun h0 : term22 => @lem7177507 x y z h0 h1). Qed.
Lemma lem7177509 (h1 : term22) : term22.
Proof. exact (h1). Qed.
Lemma lem7177510 (x : real) (y : real) (z : real) (h1 : term22) (h2 : term29 x y z) : term30 x y z.
Proof. exact (@lem7177508 x y z h2 (@lem7177509 h1)). Qed.
Lemma lem7177511 (x : real) (y : real) (z : real) (h1 : term22) : term28 x y z.
Proof. exact (fun h0 : term29 x y z => @lem7177510 x y z h1 h0). Qed.
Lemma lem7177512 (x : real) (y : real) (h1 : term22) : term26 x y.
Proof. exact (fun z : real => @lem7177511 x y z h1). Qed.
Lemma lem7177513 (x : real) (h1 : term22) : term24 x.
Proof. exact (fun y : real => @lem7177512 x y h1). Qed.
Lemma lem7177514 (h1 : term22) : term22.
Proof. exact (fun x : real => @lem7177513 x h1). Qed.
Lemma lem7177515 : term32.
Proof. exact (fun h0 : term22 => @lem7177514 h0). Qed.
Lemma lem7177516 : term22.
Proof. exact (@lem7177515 (@lem1584226)). Qed.
Lemma lem7177517 (x : real) : term23 x.
Proof. exact (@lem7177516 x). Qed.
Lemma lem7177518 (x : real) : (term23 x) = (term24 x).
Proof. exact (eq_refl (term23 x)). Qed.
Lemma lem7177519 (x : real) : term24 x.
Proof. exact (EQ_MP (@lem7177518 x) (@lem7177517 x)). Qed.
Lemma lem7177520 (x : real) (y : real) : term25 x y.
Proof. exact (@lem7177519 x y). Qed.
Lemma lem7177521 (x : real) (y : real) : (term25 x y) = (term26 x y).
Proof. exact (eq_refl (term25 x y)). Qed.
Lemma lem7177522 (x : real) (y : real) : term26 x y.
Proof. exact (EQ_MP (@lem7177521 x y) (@lem7177520 x y)). Qed.
Lemma lem7177523 (x : real) (y : real) (z : real) : term27 x y z.
Proof. exact (@lem7177522 x y z). Qed.
Lemma lem7177524 (x : real) (y : real) (z : real) : (term27 x y z) = (term28 x y z).
Proof. exact (eq_refl (term27 x y z)). Qed.
Lemma lem7177526 {_132081 : Type'} (h1 : term33 _132081) : term33 _132081.
Proof. exact (h1). Qed.
Lemma lem7177527 {_132081 : Type'} (f : _132081 -> real) (h1 : term33 _132081) : term34 _132081 f.
Proof. exact (@lem7177526 _132081 h1 f). Qed.
Lemma lem7177528 {_132081 : Type'} (f : _132081 -> real) : (term34 _132081 f) = (term35 _132081 f).
Proof. exact (eq_refl (term34 _132081 f)). Qed.
Lemma lem7177529 {_132081 : Type'} (f : _132081 -> real) (h1 : term33 _132081) : term35 _132081 f.
Proof. exact (EQ_MP (@lem7177528 _132081 f) (@lem7177527 _132081 f h1)). Qed.
Lemma lem7177530 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (h1 : term33 _132081) : term36 _132081 f g.
Proof. exact (@lem7177529 _132081 f h1 g). Qed.
Lemma lem7177531 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) : (term36 _132081 f g) = (term37 _132081 f g).
Proof. exact (eq_refl (term36 _132081 f g)). Qed.
Lemma lem7177532 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (h1 : term33 _132081) : term37 _132081 f g.
Proof. exact (EQ_MP (@lem7177531 _132081 f g) (@lem7177530 _132081 f g h1)). Qed.
Lemma lem7177533 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (s : _132081 -> Prop) (h1 : term33 _132081) : term38 _132081 f g s.
Proof. exact (@lem7177532 _132081 f g h1 s). Qed.
Lemma lem7177534 {_132081 : Type'} (f : _132081 -> real) (s : _132081 -> Prop) (g : _132081 -> real) : (term38 _132081 f g s) = (term39 _132081 f s g).
Proof. exact (eq_refl (term38 _132081 f g s)). Qed.
Lemma lem7177535 {_132081 : Type'} (f : _132081 -> real) (s : _132081 -> Prop) (g : _132081 -> real) (h1 : term33 _132081) : term39 _132081 f s g.
Proof. exact (EQ_MP (@lem7177534 _132081 f s g) (@lem7177533 _132081 f g s h1)). Qed.
Lemma lem7177536 {_132081 : Type'} (s : _132081 -> Prop) (f : _132081 -> real) (g : _132081 -> real) (h1 : term40 _132081 s f g) : term40 _132081 s f g.
Proof. exact (h1). Qed.
Lemma lem7177537 {_132081 : Type'} (s : _132081 -> Prop) (f : _132081 -> real) (g : _132081 -> real) (h1 : term33 _132081) (h2 : term40 _132081 s f g) : term41 _132081 f s g.
Proof. exact (@lem7177535 _132081 f s g h1 (@lem7177536 _132081 s f g h2)). Qed.
Lemma lem7177538 {_132081 : Type'} (s : _132081 -> Prop) (f : _132081 -> real) (g : _132081 -> real) (h1 : term40 _132081 s f g) : term42 _132081 f s g.
Proof. exact (fun h0 : term33 _132081 => @lem7177537 _132081 s f g h0 h1). Qed.
Lemma lem7177539 {_132081 : Type'} (h1 : term33 _132081) : term33 _132081.
Proof. exact (h1). Qed.
Lemma lem7177540 {_132081 : Type'} (s : _132081 -> Prop) (f : _132081 -> real) (g : _132081 -> real) (h1 : term33 _132081) (h2 : term40 _132081 s f g) : term41 _132081 f s g.
Proof. exact (@lem7177538 _132081 s f g h2 (@lem7177539 _132081 h1)). Qed.
Lemma lem7177541 {_132081 : Type'} (f : _132081 -> real) (s : _132081 -> Prop) (g : _132081 -> real) (h1 : term33 _132081) : term39 _132081 f s g.
Proof. exact (fun h0 : term40 _132081 s f g => @lem7177540 _132081 s f g h1 h0). Qed.
Lemma lem7177542 {_132081 : Type'} (f : _132081 -> real) (s : _132081 -> Prop) (h1 : term33 _132081) : term43 _132081 f s.
Proof. exact (fun g : _132081 -> real => @lem7177541 _132081 f s g h1). Qed.
Lemma lem7177543 {_132081 : Type'} (f : _132081 -> real) (h1 : term33 _132081) : term44 _132081 f.
Proof. exact (fun s : _132081 -> Prop => @lem7177542 _132081 f s h1). Qed.
Lemma lem7177544 {_132081 : Type'} (h1 : term33 _132081) : term45 _132081.
Proof. exact (fun f : _132081 -> real => @lem7177543 _132081 f h1). Qed.
Lemma lem7177545 {_132081 : Type'} : term46 _132081.
Proof. exact (fun h0 : term33 _132081 => @lem7177544 _132081 h0). Qed.
Lemma lem7177546 {_132081 : Type'} : term45 _132081.
Proof. exact (@lem7177545 _132081 (@lem7071845 _132081)). Qed.
Lemma lem7177547 {_132081 : Type'} (f : _132081 -> real) : term47 _132081 f.
Proof. exact (@lem7177546 _132081 f). Qed.
Lemma lem7177548 {_132081 : Type'} (f : _132081 -> real) : (term47 _132081 f) = (term44 _132081 f).
Proof. exact (eq_refl (term47 _132081 f)). Qed.
Lemma lem7177549 {_132081 : Type'} (f : _132081 -> real) : term44 _132081 f.
Proof. exact (EQ_MP (@lem7177548 _132081 f) (@lem7177547 _132081 f)). Qed.
Lemma lem7177550 {_132081 : Type'} (f : _132081 -> real) (s : _132081 -> Prop) : term48 _132081 f s.
Proof. exact (@lem7177549 _132081 f s). Qed.
Lemma lem7177551 {_132081 : Type'} (f : _132081 -> real) (s : _132081 -> Prop) : (term48 _132081 f s) = (term43 _132081 f s).
Proof. exact (eq_refl (term48 _132081 f s)). Qed.
Lemma lem7177552 {_132081 : Type'} (f : _132081 -> real) (s : _132081 -> Prop) : term43 _132081 f s.
Proof. exact (EQ_MP (@lem7177551 _132081 f s) (@lem7177550 _132081 f s)). Qed.
Lemma lem7177553 {_132081 : Type'} (f : _132081 -> real) (s : _132081 -> Prop) (g : _132081 -> real) : term49 _132081 f s g.
Proof. exact (@lem7177552 _132081 f s g). Qed.
Lemma lem7177554 {_132081 : Type'} (f : _132081 -> real) (s : _132081 -> Prop) (g : _132081 -> real) : (term49 _132081 f s g) = (term39 _132081 f s g).
Proof. exact (eq_refl (term49 _132081 f s g)). Qed.
Lemma lem7177559 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) (h1 : (term50 A s c f) = (term51 A c s f)) : (term50 A s c f) = (term51 A c s f).
Proof. exact (h1). Qed.
Lemma lem7177560 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) (h1 : (term50 A s c f) = (term51 A c s f)) : (term51 A c s f) = (term50 A s c f).
Proof. exact (SYM (@lem7177559 A c s f h1)). Qed.
Lemma lem7177561 {A : Type'} (s : A -> Prop) (c : real) (f : A -> real) (h1 : (term51 A c s f) = (term50 A s c f)) : (term51 A c s f) = (term50 A s c f).
Proof. exact (h1). Qed.
Lemma lem7177562 {A : Type'} (s : A -> Prop) (c : real) (f : A -> real) (h1 : (term51 A c s f) = (term50 A s c f)) : (term50 A s c f) = (term51 A c s f).
Proof. exact (SYM (@lem7177561 A s c f h1)). Qed.
Lemma lem7177563 {A : Type'} (s : A -> Prop) (c : real) (f : A -> real) : ((term50 A s c f) = (term51 A c s f)) = ((term51 A c s f) = (term50 A s c f)).
Proof. exact (prop_ext (fun h1 : (term50 A s c f) = (term51 A c s f) => @lem7177560 A c s f h1) (fun h1 : (term51 A c s f) = (term50 A s c f) => @lem7177562 A s c f h1)). Qed.
Lemma lem7177564 {A : Type'} (c : real) (f : A -> real) : (term52 A c f) = (term53 A c f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7177563 A s c f)). Qed.
Lemma lem7177565 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7177566 {A : Type'} (c : real) (f : A -> real) : (term54 A c f) = (term55 A c f).
Proof. exact (MK_COMB (@lem7177565 A) (@lem7177564 A c f)). Qed.
Lemma lem7177567 {A : Type'} (f : A -> real) : (term56 A f) = (term57 A f).
Proof. exact (fun_ext (fun c : real => @lem7177566 A c f)). Qed.
Lemma lem7177568 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7177569 {A : Type'} (f : A -> real) : (term58 A f) = (term59 A f).
Proof. exact (MK_COMB (@lem7177568) (@lem7177567 A f)). Qed.
Lemma lem7177570 {A : Type'} : (term60 A) = (term61 A).
Proof. exact (fun_ext (fun f : A -> real => @lem7177569 A f)). Qed.
Lemma lem7177571 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7177572 {A : Type'} : (term62 A) = (term63 A).
Proof. exact (MK_COMB (@lem7177571 A) (@lem7177570 A)). Qed.
Lemma lem7177573 {A : Type'} : term63 A.
Proof. exact (EQ_MP (@lem7177572 A) (@lem7070264 A)). Qed.
Lemma lem7177574 {A : Type'} (f : A -> real) : term64 A f.
Proof. exact (@lem7177573 A f). Qed.
Lemma lem7177575 {A : Type'} (f : A -> real) : (term64 A f) = (term59 A f).
Proof. exact (eq_refl (term64 A f)). Qed.
Lemma lem7177576 {A : Type'} (f : A -> real) : term59 A f.
Proof. exact (EQ_MP (@lem7177575 A f) (@lem7177574 A f)). Qed.
Lemma lem7177577 {A : Type'} (f : A -> real) (c : real) : term65 A f c.
Proof. exact (@lem7177576 A f c). Qed.
Lemma lem7177578 {A : Type'} (c : real) (f : A -> real) : (term65 A f c) = (term55 A c f).
Proof. exact (eq_refl (term65 A f c)). Qed.
Lemma lem7177579 {A : Type'} (c : real) (f : A -> real) : term55 A c f.
Proof. exact (EQ_MP (@lem7177578 A c f) (@lem7177577 A f c)). Qed.
Lemma lem7177580 {A : Type'} (c : real) (f : A -> real) (s : A -> Prop) : term66 A c f s.
Proof. exact (@lem7177579 A c f s). Qed.
Lemma lem7177581 {A : Type'} (s : A -> Prop) (c : real) (f : A -> real) : (term66 A c f s) = ((term51 A c s f) = (term50 A s c f)).
Proof. exact (eq_refl (term66 A c f s)). Qed.
Lemma lem7177583 {A : Type'} (s : A -> Prop) (a : A -> real) (b : A -> real) (h1 : term67 A s a b) : term67 A s a b.
Proof. exact (h1). Qed.
Lemma lem7177584 {A : Type'} (s : A -> Prop) (a : A -> real) (b : A -> real) (h1 : term68 A s a b) : term68 A s a b.
Proof. exact (h1). Qed.
Lemma lem7177585 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem7177587 {A : Type'} (s : A -> Prop) (c : real) (f : A -> real) : (term51 A c s f) = (term50 A s c f).
Proof. exact (EQ_MP (@lem7177581 A s c f) (@lem7177580 A c f s)). Qed.
Lemma lem7177588 {A : Type'} (s : A -> Prop) (c : real) (f : A -> real) : (term51 A c s f) = (term50 A s c f).
Proof. exact (@lem7177587 A s c f). Qed.
Lemma lem7177589 {A : Type'} (s : A -> Prop) (a : A -> real) (b : A -> real) : (term69 A a s b) = (term70 A s a b).
Proof. exact (@lem7177588 A s (@sum A s a) b). Qed.
Lemma lem7177590 {A : Type'} (s : A -> Prop) (a : A -> real) (b : A -> real) : (term71 A s a b) = (term71 A s a b).
Proof. exact (eq_refl (term71 A s a b)). Qed.
Lemma lem7177591 {A : Type'} (s : A -> Prop) (a : A -> real) (b : A -> real) : (term72 A a s b) = (term73 A s a b).
Proof. exact (MK_COMB (@lem7177590 A s a b) (@lem7177589 A s a b)). Qed.
Lemma lem7177592 {A : Type'} (a : A -> real) (s : A -> Prop) (b : A -> real) : (term73 A s a b) = (term72 A a s b).
Proof. exact (SYM (@lem7177591 A s a b)). Qed.
Lemma lem7177594 {_132081 : Type'} (f : _132081 -> real) (s : _132081 -> Prop) (g : _132081 -> real) : term39 _132081 f s g.
Proof. exact (EQ_MP (@lem7177554 _132081 f s g) (@lem7177553 _132081 f s g)). Qed.
Lemma lem7177595 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) : term39 A f s g.
Proof. exact (@lem7177594 A f s g). Qed.
Lemma lem7177596 {A : Type'} (s : A -> Prop) (a : A -> real) (b : A -> real) : term74 A s a b.
Proof. exact (@lem7177595 A (term75 A a b) s (term76 A s a b)). Qed.
Lemma lem7177597 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem7177607 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem7177597 A s) (@lem7177585 A s h1)). Qed.
Lemma lem7177608 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7177609 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (term77 A s) = (and True).
Proof. exact (MK_COMB (@lem7177608) (@lem7177607 A s h1)). Qed.
Lemma lem7177617 {A B : Type'} (f : A -> B) (y : A) : (term78 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7177618 {A : Type'} (f : A -> real) (y : A) : (term79 A f y) = (f y).
Proof. exact (@lem7177617 A real f y). Qed.
Lemma lem7177619 {A : Type'} (a : A -> real) (b : A -> real) (x : A) : (term80 A a b x) = (term81 A a b x).
Proof. exact (@lem7177618 A (term75 A a b) x). Qed.
Lemma lem7177620 {A : Type'} (a : A -> real) (b : A -> real) (i : A) : (term81 A a b i) = (term82 A a b i).
Proof. exact (eq_refl (term81 A a b i)). Qed.
Lemma lem7177621 {A : Type'} (a : A -> real) (b : A -> real) : (term83 A a b) = (term75 A a b).
Proof. exact (fun_ext (fun i : A => @lem7177620 A a b i)). Qed.
Lemma lem7177622 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7177623 {A : Type'} (a : A -> real) (b : A -> real) (x : A) : (term80 A a b x) = (term81 A a b x).
Proof. exact (MK_COMB (@lem7177621 A a b) (@lem7177622 A x)). Qed.
Lemma lem7177624 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7177625 {A : Type'} (a : A -> real) (b : A -> real) (x : A) : (term84 A a b x) = (term85 A a b x).
Proof. exact (MK_COMB (@lem7177624) (@lem7177623 A a b x)). Qed.
Lemma lem7177626 {A : Type'} (a : A -> real) (b : A -> real) (x : A) : (term81 A a b x) = (term82 A a b x).
Proof. exact (eq_refl (term81 A a b x)). Qed.
Lemma lem7177627 {A : Type'} (a : A -> real) (b : A -> real) (x : A) : ((term80 A a b x) = (term81 A a b x)) = ((term81 A a b x) = (term82 A a b x)).
Proof. exact (MK_COMB (@lem7177625 A a b x) (@lem7177626 A a b x)). Qed.
Lemma lem7177628 {A : Type'} (a : A -> real) (b : A -> real) (x : A) : (term81 A a b x) = (term82 A a b x).
Proof. exact (EQ_MP (@lem7177627 A a b x) (@lem7177619 A a b x)). Qed.
Lemma lem7177629 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7177630 {A : Type'} (a : A -> real) (b : A -> real) (x : A) : (term86 A a b x) = (term87 A a b x).
Proof. exact (MK_COMB (@lem7177629) (@lem7177628 A a b x)). Qed.
Lemma lem7177632 {A B : Type'} (f : A -> B) (y : A) : (term78 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7177633 {A : Type'} (f : A -> real) (y : A) : (term79 A f y) = (f y).
Proof. exact (@lem7177632 A real f y). Qed.
Lemma lem7177634 {A : Type'} (s : A -> Prop) (a : A -> real) (b : A -> real) (x : A) : (term88 A s a b x) = (term89 A s a b x).
Proof. exact (@lem7177633 A (term76 A s a b) x). Qed.
Lemma lem7177635 {A : Type'} (s : A -> Prop) (a : A -> real) (b : A -> real) (x : A) : (term89 A s a b x) = (term90 A s a b x).
Proof. exact (eq_refl (term89 A s a b x)). Qed.
Lemma lem7177636 {A : Type'} (s : A -> Prop) (a : A -> real) (b : A -> real) : (term91 A s a b) = (term76 A s a b).
Proof. exact (fun_ext (fun x : A => @lem7177635 A s a b x)). Qed.
Lemma lem7177637 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7177638 {A : Type'} (s : A -> Prop) (a : A -> real) (b : A -> real) (x : A) : (term88 A s a b x) = (term89 A s a b x).
Proof. exact (MK_COMB (@lem7177636 A s a b) (@lem7177637 A x)). Qed.
Lemma lem7177639 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7177640 {A : Type'} (s : A -> Prop) (a : A -> real) (b : A -> real) (x : A) : (term92 A s a b x) = (term93 A s a b x).
Proof. exact (MK_COMB (@lem7177639) (@lem7177638 A s a b x)). Qed.
Lemma lem7177641 {A : Type'} (s : A -> Prop) (a : A -> real) (b : A -> real) (x : A) : (term89 A s a b x) = (term90 A s a b x).
Proof. exact (eq_refl (term89 A s a b x)). Qed.
Lemma lem7177642 {A : Type'} (s : A -> Prop) (a : A -> real) (b : A -> real) (x : A) : ((term88 A s a b x) = (term89 A s a b x)) = ((term89 A s a b x) = (term90 A s a b x)).
Proof. exact (MK_COMB (@lem7177640 A s a b x) (@lem7177641 A s a b x)). Qed.
Lemma lem7177643 {A : Type'} (s : A -> Prop) (a : A -> real) (b : A -> real) (x : A) : (term89 A s a b x) = (term90 A s a b x).
Proof. exact (EQ_MP (@lem7177642 A s a b x) (@lem7177634 A s a b x)). Qed.
Lemma lem7177644 {A : Type'} (s : A -> Prop) (a : A -> real) (b : A -> real) (x : A) : (term94 A s a b x) = (term95 A s a b x).
Proof. exact (MK_COMB (@lem7177630 A a b x) (@lem7177643 A s a b x)). Qed.
Lemma lem7177645 {A : Type'} (x : A) (s : A -> Prop) : (term96 A x s) = (term96 A x s).
Proof. exact (eq_refl (term96 A x s)). Qed.
Lemma lem7177646 {A : Type'} (s : A -> Prop) (a : A -> real) (b : A -> real) (x : A) : (term97 A s a b x) = (term98 A s a b x).
Proof. exact (MK_COMB (@lem7177645 A x s) (@lem7177644 A s a b x)). Qed.
Lemma lem7177649 {A : Type'} (s : A -> Prop) (a : A -> real) (b : A -> real) : (term99 A s a b) = (term100 A s a b).
Proof. exact (fun_ext (fun x : A => @lem7177646 A s a b x)). Qed.
Lemma lem7177650 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7177651 {A : Type'} (s : A -> Prop) (a : A -> real) (b : A -> real) : (term101 A s a b) = (term102 A s a b).
Proof. exact (MK_COMB (@lem7177650 A) (@lem7177649 A s a b)). Qed.
Lemma lem7177656 {A : Type'} (a : A -> real) (b : A -> real) (s : A -> Prop) (h1 : @FINITE A s) : (term103 A s a b) = (term104 A s a b).
Proof. exact (MK_COMB (@lem7177609 A s h1) (@lem7177651 A s a b)). Qed.
Lemma lem7177658 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7177659 {A : Type'} (s : A -> Prop) (a : A -> real) (b : A -> real) : (term104 A s a b) = (term102 A s a b).
Proof. exact (@lem7177658 (term102 A s a b)). Qed.
Lemma lem7177666 {A : Type'} (a : A -> real) (b : A -> real) (s : A -> Prop) (h1 : @FINITE A s) : (term103 A s a b) = (term102 A s a b).
Proof. exact (TRANS (@lem7177656 A a b s h1) (@lem7177659 A s a b)). Qed.
Lemma lem7177667 {A : Type'} (a : A -> real) (b : A -> real) (s : A -> Prop) (h1 : @FINITE A s) : (term102 A s a b) = (term103 A s a b).
Proof. exact (SYM (@lem7177666 A a b s h1)). Qed.
Lemma lem7177668 {A : Type'} (i : A) (s : A -> Prop) (h1 : @IN A i s) : @IN A i s.
Proof. exact (h1). Qed.
Lemma lem7177670 (x : real) (y : real) (z : real) : term28 x y z.
Proof. exact (EQ_MP (@lem7177524 x y z) (@lem7177523 x y z)). Qed.
Lemma lem7177671 {A : Type'} (s : A -> Prop) (a : A -> real) (b : A -> real) (i : A) : term105 A s a b i.
Proof. exact (@lem7177670 (a i) (@sum A s a) (b i)). Qed.
Lemma lem7177674 {A : Type'} (i : A) (s : A -> Prop) (a : A -> real) (b : A -> real) (h1 : term68 A s a b) : term106 A s a b i.
Proof. exact (@lem7177584 A s a b h1 i). Qed.
Lemma lem7177675 {A : Type'} (s : A -> Prop) (a : A -> real) (b : A -> real) (i : A) : (term106 A s a b i) = (term107 A s a b i).
Proof. exact (eq_refl (term106 A s a b i)). Qed.
Lemma lem7177676 {A : Type'} (i : A) (s : A -> Prop) (a : A -> real) (b : A -> real) (h1 : term68 A s a b) : term107 A s a b i.
Proof. exact (EQ_MP (@lem7177675 A s a b i) (@lem7177674 A i s a b h1)). Qed.
Lemma lem7177677 {A : Type'} (i : A) (s : A -> Prop) (h1 : @IN A i s) : @IN A i s.
Proof. exact (h1). Qed.
Lemma lem7177678 {A : Type'} (a : A -> real) (b : A -> real) (i : A) (s : A -> Prop) (h1 : term68 A s a b) (h2 : @IN A i s) : term108 A a b i.
Proof. exact (@lem7177676 A i s a b h1 (@lem7177677 A i s h2)). Qed.
Lemma lem7177679 {A : Type'} (a : A -> real) (b : A -> real) (i : A) (s : A -> Prop) (h1 : term68 A s a b) (h2 : @IN A i s) : term109 A b i.
Proof. exact (proj2 (@lem7177678 A a b i s h1 h2)). Qed.
Lemma lem7177680 {A : Type'} (b : A -> real) (i : A) : (term109 A b i) = ((term109 A b i) = True).
Proof. exact (@lem7 (term109 A b i)). Qed.
Lemma lem7177681 {A : Type'} (a : A -> real) (b : A -> real) (i : A) (s : A -> Prop) (h1 : term68 A s a b) (h2 : @IN A i s) : (term109 A b i) = True.
Proof. exact (EQ_MP (@lem7177680 A b i) (@lem7177679 A a b i s h1 h2)). Qed.
Lemma lem7177695 {A : Type'} (i : A) (s : A -> Prop) : (@IN A i s) = ((@IN A i s) = True).
Proof. exact (@lem7 (@IN A i s)). Qed.
Lemma lem7177700 {A : Type'} (i : A) (s : A -> Prop) (a : A -> real) (b : A -> real) (h1 : term68 A s a b) : term110 A s b i.
Proof. exact (fun h0 : @IN A i s => @lem7177681 A a b i s h1 h0). Qed.
Lemma lem7177701 {A : Type'} (i : A) (s : A -> Prop) (a : A -> real) (b : A -> real) (h1 : term68 A s a b) : term110 A s b i.
Proof. exact (@lem7177700 A i s a b h1). Qed.
Lemma lem7177703 {A : Type'} (i : A) (s : A -> Prop) (h1 : @IN A i s) : (@IN A i s) = True.
Proof. exact (EQ_MP (@lem7177695 A i s) (@lem7177668 A i s h1)). Qed.
Lemma lem7177704 {A : Type'} (i : A) (s : A -> Prop) (h1 : @IN A i s) : True = (@IN A i s).
Proof. exact (SYM (@lem7177703 A i s h1)). Qed.
Lemma lem7177705 {A : Type'} (i : A) (s : A -> Prop) (h1 : @IN A i s) : @IN A i s.
Proof. exact (EQ_MP (@lem7177704 A i s h1) (@lem0)). Qed.
Lemma lem7177706 {A : Type'} (a : A -> real) (b : A -> real) (i : A) (s : A -> Prop) (h1 : term68 A s a b) (h2 : @IN A i s) : (term109 A b i) = True.
Proof. exact (@lem7177701 A i s a b h1 (@lem7177705 A i s h2)). Qed.
Lemma lem7177707 {A : Type'} (i : A) (s : A -> Prop) (a : A -> real) : (term111 A i s a) = (term111 A i s a).
Proof. exact (eq_refl (term111 A i s a)). Qed.
Lemma lem7177708 {A : Type'} (a : A -> real) (b : A -> real) (i : A) (s : A -> Prop) (h1 : term68 A s a b) (h2 : @IN A i s) : (term112 A s a b i) = (term113 A i s a).
Proof. exact (MK_COMB (@lem7177707 A i s a) (@lem7177706 A a b i s h1 h2)). Qed.
Lemma lem7177710 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem7177711 {A : Type'} (i : A) (s : A -> Prop) (a : A -> real) : (term113 A i s a) = (term114 A i s a).
Proof. exact (@lem7177710 (term114 A i s a)). Qed.
Lemma lem7177712 {A : Type'} (a : A -> real) (b : A -> real) (i : A) (s : A -> Prop) (h1 : term68 A s a b) (h2 : @IN A i s) : (term112 A s a b i) = (term114 A i s a).
Proof. exact (TRANS (@lem7177708 A a b i s h1 h2) (@lem7177711 A i s a)). Qed.
Lemma lem7177713 {A : Type'} (a : A -> real) (b : A -> real) (i : A) (s : A -> Prop) (h1 : term68 A s a b) (h2 : @IN A i s) : (term114 A i s a) = (term112 A s a b i).
Proof. exact (SYM (@lem7177712 A a b i s h1 h2)). Qed.
Lemma lem7177715 {_133036 : Type'} (x : _133036) (f : _133036 -> real) : (f x) = (term11 _133036 x f).
Proof. exact (EQ_MP (@lem7177494 _133036 x f) (@lem7177493 _133036 f x)). Qed.
Lemma lem7177716 {A : Type'} (x : A) (f : A -> real) : (f x) = (term11 A x f).
Proof. exact (@lem7177715 A x f). Qed.
Lemma lem7177717 {A : Type'} (i : A) (a : A -> real) : (a i) = (term11 A i a).
Proof. exact (@lem7177716 A i a). Qed.
Lemma lem7177718 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7177719 {A : Type'} (i : A) (a : A -> real) : (term115 A a i) = (term116 A i a).
Proof. exact (MK_COMB (@lem7177718) (@lem7177717 A i a)). Qed.
Lemma lem7177720 {A : Type'} (s : A -> Prop) (a : A -> real) : (@sum A s a) = (@sum A s a).
Proof. exact (eq_refl (@sum A s a)). Qed.
Lemma lem7177721 {A : Type'} (i : A) (s : A -> Prop) (a : A -> real) : (term114 A i s a) = (term117 A i s a).
Proof. exact (MK_COMB (@lem7177719 A i a) (@lem7177720 A s a)). Qed.
Lemma lem7177722 {A : Type'} (i : A) (s : A -> Prop) (a : A -> real) : (term117 A i s a) = (term114 A i s a).
Proof. exact (SYM (@lem7177721 A i s a)). Qed.
Lemma lem7177724 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : term6 A u v f.
Proof. exact (EQ_MP (@lem7177474 A u v f) (@lem7177473 A u v f)). Qed.
Lemma lem7177725 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : term6 A u v f.
Proof. exact (@lem7177724 A u v f). Qed.
Lemma lem7177726 {A : Type'} (i : A) (s : A -> Prop) (a : A -> real) : term118 A i s a.
Proof. exact (@lem7177725 A (@INSERT A i (@EMPTY A)) s a). Qed.
Lemma lem7177727 {A : Type'} (s : A -> Prop) : term119 A s.
Proof. exact (@lem3205495 A s). Qed.
Lemma lem7177728 {A : Type'} (s : A -> Prop) : (term119 A s) = (term120 A s).
Proof. exact (eq_refl (term119 A s)). Qed.
Lemma lem7177729 {A : Type'} (s : A -> Prop) : term120 A s.
Proof. exact (EQ_MP (@lem7177728 A s) (@lem7177727 A s)). Qed.
Lemma lem7177730 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term121 A s t.
Proof. exact (@lem7177729 A s t). Qed.
Lemma lem7177731 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term121 A s t) = (term122 A s t).
Proof. exact (eq_refl (term121 A s t)). Qed.
Lemma lem7177732 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term122 A s t.
Proof. exact (EQ_MP (@lem7177731 A s t) (@lem7177730 A s t)). Qed.
Lemma lem7177733 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : term123 A s t x.
Proof. exact (@lem7177732 A s t x). Qed.
Lemma lem7177734 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term123 A s t x) = ((term124 A x s t) = (term125 A s x t)).
Proof. exact (eq_refl (term123 A s t x)). Qed.
Lemma lem7177736 {_84443 : Type'} (s : _84443 -> Prop) : term126 _84443 s.
Proof. exact (@lem3221020 _84443 s). Qed.
Lemma lem7177737 {_84443 : Type'} (s : _84443 -> Prop) : (term126 _84443 s) = (term127 _84443 s).
Proof. exact (eq_refl (term126 _84443 s)). Qed.
Lemma lem7177738 {_84443 : Type'} (s : _84443 -> Prop) : term127 _84443 s.
Proof. exact (EQ_MP (@lem7177737 _84443 s) (@lem7177736 _84443 s)). Qed.
Lemma lem7177739 {_84443 : Type'} (s : _84443 -> Prop) (x : _84443) : term128 _84443 s x.
Proof. exact (@lem7177738 _84443 s x). Qed.
Lemma lem7177740 {_84443 : Type'} (x : _84443) (s : _84443 -> Prop) : (term128 _84443 s x) = ((term129 _84443 x s) = (@IN _84443 x s)).
Proof. exact (eq_refl (term128 _84443 s x)). Qed.
Lemma lem7177742 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem7177744 {A : Type'} (i : A) (s : A -> Prop) (a : A -> real) (b : A -> real) (h1 : term68 A s a b) : term106 A s a b i.
Proof. exact (@lem7177584 A s a b h1 i). Qed.
Lemma lem7177745 {A : Type'} (s : A -> Prop) (a : A -> real) (b : A -> real) (i : A) : (term106 A s a b i) = (term107 A s a b i).
Proof. exact (eq_refl (term106 A s a b i)). Qed.
Lemma lem7177746 {A : Type'} (i : A) (s : A -> Prop) (a : A -> real) (b : A -> real) (h1 : term68 A s a b) : term107 A s a b i.
Proof. exact (EQ_MP (@lem7177745 A s a b i) (@lem7177744 A i s a b h1)). Qed.
Lemma lem7177747 {A : Type'} (i : A) (s : A -> Prop) (h1 : @IN A i s) : @IN A i s.
Proof. exact (h1). Qed.
Lemma lem7177748 {A : Type'} (a : A -> real) (b : A -> real) (i : A) (s : A -> Prop) (h1 : term68 A s a b) (h2 : @IN A i s) : term108 A a b i.
Proof. exact (@lem7177746 A i s a b h1 (@lem7177747 A i s h2)). Qed.
Lemma lem7177757 {A : Type'} (a : A -> real) (b : A -> real) (i : A) (s : A -> Prop) (h1 : term68 A s a b) (h2 : @IN A i s) : term109 A a i.
Proof. exact (proj1 (@lem7177748 A a b i s h1 h2)). Qed.
Lemma lem7177758 {A : Type'} (a : A -> real) (i : A) : (term109 A a i) = ((term109 A a i) = True).
Proof. exact (@lem7 (term109 A a i)). Qed.
Lemma lem7177759 {A : Type'} (a : A -> real) (b : A -> real) (i : A) (s : A -> Prop) (h1 : term68 A s a b) (h2 : @IN A i s) : (term109 A a i) = True.
Proof. exact (EQ_MP (@lem7177758 A a i) (@lem7177757 A a b i s h1 h2)). Qed.
Lemma lem7177765 {A : Type'} (i : A) (s : A -> Prop) : (@IN A i s) = ((@IN A i s) = True).
Proof. exact (@lem7 (@IN A i s)). Qed.
Lemma lem7177770 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem7177742 A s) (@lem7177585 A s h1)). Qed.
Lemma lem7177771 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7177772 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (term77 A s) = (and True).
Proof. exact (MK_COMB (@lem7177771) (@lem7177770 A s h1)). Qed.
Lemma lem7177776 {_84443 : Type'} (x : _84443) (s : _84443 -> Prop) : (term129 _84443 x s) = (@IN _84443 x s).
Proof. exact (EQ_MP (@lem7177740 _84443 x s) (@lem7177739 _84443 s x)). Qed.
Lemma lem7177777 {A : Type'} (x : A) (s : A -> Prop) : (term129 A x s) = (@IN A x s).
Proof. exact (@lem7177776 A x s). Qed.
Lemma lem7177778 {A : Type'} (i : A) (s : A -> Prop) : (term129 A i s) = (@IN A i s).
Proof. exact (@lem7177777 A i s). Qed.
Lemma lem7177780 {A : Type'} (i : A) (s : A -> Prop) (h1 : @IN A i s) : (@IN A i s) = True.
Proof. exact (EQ_MP (@lem7177765 A i s) (@lem7177668 A i s h1)). Qed.
Lemma lem7177781 {A : Type'} (i : A) (s : A -> Prop) (h1 : @IN A i s) : (term129 A i s) = True.
Proof. exact (TRANS (@lem7177778 A i s) (@lem7177780 A i s h1)). Qed.
Lemma lem7177782 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7177783 {A : Type'} (i : A) (s : A -> Prop) (h1 : @IN A i s) : (term130 A i s) = (and True).
Proof. exact (MK_COMB (@lem7177782) (@lem7177781 A i s h1)). Qed.
Lemma lem7177791 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term131 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7177792 (p : Prop) (q : Prop) (p' : Prop) : term132 p q p'.
Proof. exact (fun q' : Prop => @lem7177791 p q p' q'). Qed.
Lemma lem7177793 (p : Prop) (q : Prop) : term133 p q.
Proof. exact (fun p' : Prop => @lem7177792 p q p'). Qed.
Lemma lem7177794 {A : Type'} (s : A -> Prop) (i : A) (a : A -> real) (x : A) : term134 A s i a x.
Proof. exact (@lem7177793 (term135 A x s i) (term109 A a x)). Qed.
Lemma lem7177795 {A : Type'} (s : A -> Prop) (i : A) (a : A -> real) (x : A) (p' : Prop) : term136 A s i a x p'.
Proof. exact (@lem7177794 A s i a x p'). Qed.
Lemma lem7177796 {A : Type'} (s : A -> Prop) (i : A) (a : A -> real) (x : A) (p' : Prop) : (term136 A s i a x p') = (term137 A s i a x p').
Proof. exact (eq_refl (term136 A s i a x p')). Qed.
Lemma lem7177797 {A : Type'} (s : A -> Prop) (i : A) (a : A -> real) (x : A) (p' : Prop) : term137 A s i a x p'.
Proof. exact (EQ_MP (@lem7177796 A s i a x p') (@lem7177795 A s i a x p')). Qed.
Lemma lem7177798 {A : Type'} (s : A -> Prop) (i : A) (a : A -> real) (x : A) (p' : Prop) (q' : Prop) : term138 A s i a x p' q'.
Proof. exact (@lem7177797 A s i a x p' q'). Qed.
Lemma lem7177799 {A : Type'} (s : A -> Prop) (i : A) (a : A -> real) (x : A) (p' : Prop) (q' : Prop) : (term138 A s i a x p' q') = (term139 A s i a x p' q').
Proof. exact (eq_refl (term138 A s i a x p' q')). Qed.
Lemma lem7177800 {A : Type'} (s : A -> Prop) (i : A) (a : A -> real) (x : A) (p' : Prop) (q' : Prop) : term139 A s i a x p' q'.
Proof. exact (EQ_MP (@lem7177799 A s i a x p' q') (@lem7177798 A s i a x p' q')). Qed.
Lemma lem7177802 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term124 A x s t) = (term125 A s x t).
Proof. exact (EQ_MP (@lem7177734 A s x t) (@lem7177733 A s t x)). Qed.
Lemma lem7177803 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term124 A x s t) = (term125 A s x t).
Proof. exact (@lem7177802 A s x t). Qed.
Lemma lem7177804 {A : Type'} (s : A -> Prop) (x : A) (i : A) : (term135 A x s i) = (term140 A s x i).
Proof. exact (@lem7177803 A s x (@INSERT A i (@EMPTY A))). Qed.
Lemma lem7177807 {A : Type'} (a : A -> real) (s : A -> Prop) (x : A) (i : A) (q' : Prop) : term141 A a s x i q'.
Proof. exact (@lem7177800 A s i a x (term140 A s x i) q'). Qed.
Lemma lem7177808 {A : Type'} (a : A -> real) (s : A -> Prop) (x : A) (i : A) (q' : Prop) : term142 A a s x i q'.
Proof. exact (@lem7177807 A a s x i q' (@lem7177804 A s x i)). Qed.
Lemma lem7177809 {A : Type'} (s : A -> Prop) (x : A) (i : A) (h1 : term140 A s x i) : term140 A s x i.
Proof. exact (h1). Qed.
Lemma lem7177813 {A : Type'} (s : A -> Prop) (x : A) (i : A) (h1 : term140 A s x i) : @IN A x s.
Proof. exact (proj1 (@lem7177809 A s x i h1)). Qed.
Lemma lem7177814 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = ((@IN A x s) = True).
Proof. exact (@lem7 (@IN A x s)). Qed.
Lemma lem7177817 {A : Type'} (i : A) (s : A -> Prop) (a : A -> real) (b : A -> real) (h1 : term68 A s a b) : term110 A s a i.
Proof. exact (fun h0 : @IN A i s => @lem7177759 A a b i s h1 h0). Qed.
Lemma lem7177818 {A : Type'} (i : A) (s : A -> Prop) (a : A -> real) (b : A -> real) (h1 : term68 A s a b) : term110 A s a i.
Proof. exact (@lem7177817 A i s a b h1). Qed.
Lemma lem7177819 {A : Type'} (x : A) (s : A -> Prop) (a : A -> real) (b : A -> real) (h1 : term68 A s a b) : term110 A s a x.
Proof. exact (@lem7177818 A x s a b h1). Qed.
Lemma lem7177821 {A : Type'} (s : A -> Prop) (x : A) (i : A) (h1 : term140 A s x i) : (@IN A x s) = True.
Proof. exact (EQ_MP (@lem7177814 A x s) (@lem7177813 A s x i h1)). Qed.
Lemma lem7177822 {A : Type'} (s : A -> Prop) (x : A) (i : A) (h1 : term140 A s x i) : True = (@IN A x s).
Proof. exact (SYM (@lem7177821 A s x i h1)). Qed.
Lemma lem7177823 {A : Type'} (s : A -> Prop) (x : A) (i : A) (h1 : term140 A s x i) : @IN A x s.
Proof. exact (EQ_MP (@lem7177822 A s x i h1) (@lem0)). Qed.
Lemma lem7177824 {A : Type'} (a : A -> real) (b : A -> real) (s : A -> Prop) (x : A) (i : A) (h1 : term68 A s a b) (h2 : term140 A s x i) : (term109 A a x) = True.
Proof. exact (@lem7177819 A x s a b h1 (@lem7177823 A s x i h2)). Qed.
Lemma lem7177825 {A : Type'} (i : A) (x : A) (s : A -> Prop) (a : A -> real) (b : A -> real) (h1 : term68 A s a b) : term143 A s i a x.
Proof. exact (fun h0 : term140 A s x i => @lem7177824 A a b s x i h1 h0). Qed.
Lemma lem7177826 {A : Type'} (a : A -> real) (s : A -> Prop) (x : A) (i : A) : term144 A a s x i.
Proof. exact (@lem7177808 A a s x i True). Qed.
Lemma lem7177827 {A : Type'} (x : A) (i : A) (s : A -> Prop) (a : A -> real) (b : A -> real) (h1 : term68 A s a b) : (term145 A s i a x) = (term146 A s x i).
Proof. exact (@lem7177826 A a s x i (@lem7177825 A i x s a b h1)). Qed.
Lemma lem7177829 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7177830 {A : Type'} (s : A -> Prop) (x : A) (i : A) : (term146 A s x i) = True.
Proof. exact (@lem7177829 (term140 A s x i)). Qed.
Lemma lem7177831 {A : Type'} (i : A) (x : A) (s : A -> Prop) (a : A -> real) (b : A -> real) (h1 : term68 A s a b) : (term145 A s i a x) = True.
Proof. exact (TRANS (@lem7177827 A x i s a b h1) (@lem7177830 A s x i)). Qed.
Lemma lem7177832 {A : Type'} (i : A) (s : A -> Prop) (a : A -> real) (b : A -> real) (h1 : term68 A s a b) : (term147 A s i a) = (term148 A).
Proof. exact (fun_ext (fun x : A => @lem7177831 A i x s a b h1)). Qed.
Lemma lem7177833 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7177834 {A : Type'} (i : A) (s : A -> Prop) (a : A -> real) (b : A -> real) (h1 : term68 A s a b) : (term149 A s i a) = (term150 A).
Proof. exact (MK_COMB (@lem7177833 A) (@lem7177832 A i s a b h1)). Qed.
Lemma lem7177836 {A : Type'} (t : Prop) : (term151 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7177837 {A : Type'} (t : Prop) : (term151 A t) = t.
Proof. exact (@lem7177836 A t). Qed.
Lemma lem7177838 {A : Type'} : (term150 A) = True.
Proof. exact (@lem7177837 A True). Qed.
Lemma lem7177839 {A : Type'} (i : A) (s : A -> Prop) (a : A -> real) (b : A -> real) (h1 : term68 A s a b) : (term149 A s i a) = True.
Proof. exact (TRANS (@lem7177834 A i s a b h1) (@lem7177838 A)). Qed.
Lemma lem7177840 {A : Type'} (a : A -> real) (b : A -> real) (i : A) (s : A -> Prop) (h1 : term68 A s a b) (h2 : @IN A i s) : (term152 A s i a) = (True /\ True).
Proof. exact (MK_COMB (@lem7177783 A i s h2) (@lem7177839 A i s a b h1)). Qed.
Lemma lem7177842 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7177843 : (True /\ True) = True.
Proof. exact (@lem7177842 True). Qed.
Lemma lem7177844 {A : Type'} (a : A -> real) (b : A -> real) (i : A) (s : A -> Prop) (h1 : term68 A s a b) (h2 : @IN A i s) : (term152 A s i a) = True.
Proof. exact (TRANS (@lem7177840 A a b i s h1 h2) (@lem7177843)). Qed.
Lemma lem7177845 {A : Type'} (a : A -> real) (b : A -> real) (i : A) (s : A -> Prop) (h1 : term68 A s a b) (h2 : @FINITE A s) (h3 : @IN A i s) : (term153 A s i a) = (True /\ True).
Proof. exact (MK_COMB (@lem7177772 A s h2) (@lem7177844 A a b i s h1 h3)). Qed.
Lemma lem7177847 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7177848 : (True /\ True) = True.
Proof. exact (@lem7177847 True). Qed.
Lemma lem7177849 {A : Type'} (a : A -> real) (b : A -> real) (i : A) (s : A -> Prop) (h1 : term68 A s a b) (h2 : @FINITE A s) (h3 : @IN A i s) : (term153 A s i a) = True.
Proof. exact (TRANS (@lem7177845 A a b i s h1 h2 h3) (@lem7177848)). Qed.
Lemma lem7177850 {A : Type'} (a : A -> real) (b : A -> real) (i : A) (s : A -> Prop) (h1 : term68 A s a b) (h2 : @FINITE A s) (h3 : @IN A i s) : True = (term153 A s i a).
Proof. exact (SYM (@lem7177849 A a b i s h1 h2 h3)). Qed.
Lemma lem7177851 {A : Type'} (a : A -> real) (b : A -> real) (i : A) (s : A -> Prop) (h1 : term68 A s a b) (h2 : @FINITE A s) (h3 : @IN A i s) : term153 A s i a.
Proof. exact (EQ_MP (@lem7177850 A a b i s h1 h2 h3) (@lem0)). Qed.
Lemma lem7177852 {A : Type'} (a : A -> real) (b : A -> real) (i : A) (s : A -> Prop) (h1 : term68 A s a b) (h2 : @FINITE A s) (h3 : @IN A i s) : term117 A i s a.
Proof. exact (@lem7177726 A i s a (@lem7177851 A a b i s h1 h2 h3)). Qed.
Lemma lem7177853 {A : Type'} (a : A -> real) (b : A -> real) (i : A) (s : A -> Prop) (h1 : term68 A s a b) (h2 : @FINITE A s) (h3 : @IN A i s) : term114 A i s a.
Proof. exact (EQ_MP (@lem7177722 A i s a) (@lem7177852 A a b i s h1 h2 h3)). Qed.
Lemma lem7177854 {A : Type'} (a : A -> real) (b : A -> real) (i : A) (s : A -> Prop) (h1 : term68 A s a b) (h2 : @FINITE A s) (h3 : @IN A i s) : term112 A s a b i.
Proof. exact (EQ_MP (@lem7177713 A a b i s h1 h3) (@lem7177853 A a b i s h1 h2 h3)). Qed.
Lemma lem7177855 {A : Type'} (a : A -> real) (b : A -> real) (i : A) (s : A -> Prop) (h1 : term68 A s a b) (h2 : @FINITE A s) (h3 : @IN A i s) : term95 A s a b i.
Proof. exact (@lem7177671 A s a b i (@lem7177854 A a b i s h1 h2 h3)). Qed.
Lemma lem7177856 {A : Type'} (i : A) (a : A -> real) (b : A -> real) (s : A -> Prop) (h1 : term68 A s a b) (h2 : @FINITE A s) : term98 A s a b i.
Proof. exact (fun h0 : @IN A i s => @lem7177855 A a b i s h1 h2 h0). Qed.
Lemma lem7177861 {A : Type'} (a : A -> real) (b : A -> real) (s : A -> Prop) (h1 : term68 A s a b) (h2 : @FINITE A s) : term102 A s a b.
Proof. exact (fun i : A => @lem7177856 A i a b s h1 h2). Qed.
Lemma lem7177862 {A : Type'} (a : A -> real) (b : A -> real) (s : A -> Prop) (h1 : term68 A s a b) (h2 : @FINITE A s) : term103 A s a b.
Proof. exact (EQ_MP (@lem7177667 A a b s h2) (@lem7177861 A a b s h1 h2)). Qed.
Lemma lem7177863 {A : Type'} (a : A -> real) (b : A -> real) (s : A -> Prop) (h1 : term68 A s a b) (h2 : @FINITE A s) : term73 A s a b.
Proof. exact (@lem7177596 A s a b (@lem7177862 A a b s h1 h2)). Qed.
Lemma lem7177864 {A : Type'} (a : A -> real) (b : A -> real) (s : A -> Prop) (h1 : term68 A s a b) (h2 : @FINITE A s) : term72 A a s b.
Proof. exact (EQ_MP (@lem7177592 A a s b) (@lem7177863 A a b s h1 h2)). Qed.
Lemma lem7177865 {A : Type'} (s : A -> Prop) (a : A -> real) (b : A -> real) (h1 : term67 A s a b) : term68 A s a b.
Proof. exact (proj2 (@lem7177583 A s a b h1)). Qed.
Lemma lem7177866 {A : Type'} (s : A -> Prop) (a : A -> real) (b : A -> real) (h1 : term67 A s a b) : @FINITE A s.
Proof. exact (proj1 (@lem7177583 A s a b h1)). Qed.
Lemma lem7177867 {A : Type'} (a : A -> real) (b : A -> real) (s : A -> Prop) (h1 : term68 A s a b) (h2 : @FINITE A s) : (term68 A s a b) = (term72 A a s b).
Proof. exact (prop_ext (fun h3 : term68 A s a b => @lem7177864 A a b s h1 h2) (fun h3 : term72 A a s b => @lem7177584 A s a b h1)). Qed.
Lemma lem7177868 {A : Type'} (a : A -> real) (b : A -> real) (s : A -> Prop) (h1 : term68 A s a b) (h2 : @FINITE A s) : term72 A a s b.
Proof. exact (EQ_MP (@lem7177867 A a b s h1 h2) (@lem7177584 A s a b h1)). Qed.
Lemma lem7177869 {A : Type'} (a : A -> real) (b : A -> real) (s : A -> Prop) (h1 : term68 A s a b) (h2 : @FINITE A s) : (@FINITE A s) = (term72 A a s b).
Proof. exact (prop_ext (fun h3 : @FINITE A s => @lem7177868 A a b s h1 h2) (fun h3 : term72 A a s b => @lem7177585 A s h2)). Qed.
Lemma lem7177870 {A : Type'} (a : A -> real) (b : A -> real) (s : A -> Prop) (h1 : term68 A s a b) (h2 : @FINITE A s) : term72 A a s b.
Proof. exact (EQ_MP (@lem7177869 A a b s h1 h2) (@lem7177585 A s h2)). Qed.
Lemma lem7177871 {A : Type'} (s : A -> Prop) (a : A -> real) (b : A -> real) (h1 : @FINITE A s) (h2 : term67 A s a b) : (term68 A s a b) = (term72 A a s b).
Proof. exact (prop_ext (fun h3 : term68 A s a b => @lem7177870 A a b s h3 h1) (fun h3 : term72 A a s b => @lem7177865 A s a b h2)). Qed.
Lemma lem7177872 {A : Type'} (s : A -> Prop) (a : A -> real) (b : A -> real) (h1 : @FINITE A s) (h2 : term67 A s a b) : term72 A a s b.
Proof. exact (EQ_MP (@lem7177871 A s a b h1 h2) (@lem7177865 A s a b h2)). Qed.
Lemma lem7177873 {A : Type'} (s : A -> Prop) (a : A -> real) (b : A -> real) (h1 : term67 A s a b) : (@FINITE A s) = (term72 A a s b).
Proof. exact (prop_ext (fun h2 : @FINITE A s => @lem7177872 A s a b h2 h1) (fun h2 : term72 A a s b => @lem7177866 A s a b h1)). Qed.
Lemma lem7177874 {A : Type'} (s : A -> Prop) (a : A -> real) (b : A -> real) (h1 : term67 A s a b) : term72 A a s b.
Proof. exact (EQ_MP (@lem7177873 A s a b h1) (@lem7177866 A s a b h1)). Qed.
Lemma lem7177875 {A : Type'} (a : A -> real) (s : A -> Prop) (b : A -> real) : term154 A a s b.
Proof. exact (fun h0 : term67 A s a b => @lem7177874 A s a b h0). Qed.
Lemma lem7177880 {A : Type'} (a : A -> real) (b : A -> real) : term155 A a b.
Proof. exact (fun s : A -> Prop => @lem7177875 A a s b). Qed.
Lemma lem7177885 {A : Type'} (a : A -> real) : term156 A a.
Proof. exact (fun b : A -> real => @lem7177880 A a b). Qed.
Lemma lem7177890 {A : Type'} : term157 A.
Proof. exact (fun a : A -> real => @lem7177885 A a). Qed.
