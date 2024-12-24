Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import WLOG_RELATION_term_abbrevs.
Require Import MONO_FORALL_spec.
Require Import thm0_spec.
Require Import thm7_spec.
Lemma lem7402 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (h1). Qed.
Lemma lem7403 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term1 A P Q) : term1 A P Q.
Proof. exact (h1). Qed.
Lemma lem7404 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term1 A P Q) (h2 : term0 A P Q) : term2 A P Q.
Proof. exact (@lem7402 A P Q h2 (@lem7403 A P Q h1)). Qed.
Lemma lem7405 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term1 A P Q) : term3 A P Q.
Proof. exact (fun h0 : term0 A P Q => @lem7404 A P Q h1 h0). Qed.
Lemma lem7406 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (h1). Qed.
Lemma lem7407 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term1 A P Q) (h2 : term0 A P Q) : term2 A P Q.
Proof. exact (@lem7405 A P Q h1 (@lem7406 A P Q h2)). Qed.
Lemma lem7408 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (fun h0 : term1 A P Q => @lem7407 A P Q h0 h1). Qed.
Lemma lem7409 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term4 A P Q.
Proof. exact (fun h0 : term0 A P Q => @lem7408 A P Q h0). Qed.
Lemma lem7411 {_1718 : Type'} (R : type1402 _1718) (P : type1402 _1718) (h1 : term5 _1718 R P) : term5 _1718 R P.
Proof. exact (h1). Qed.
Lemma lem7412 {_1718 : Type'} (R : type1402 _1718) (P : type1402 _1718) (h1 : term6 _1718 R P) : term6 _1718 R P.
Proof. exact (h1). Qed.
Lemma lem7413 {_1718 : Type'} (P : type1402 _1718) (h1 : term7 _1718 P) : term7 _1718 P.
Proof. exact (h1). Qed.
Lemma lem7414 {_1718 : Type'} (R : type1402 _1718) (P : type1402 _1718) (h1 : term8 _1718 R P) : term8 _1718 R P.
Proof. exact (h1). Qed.
Lemma lem7415 {_1718 : Type'} (R : type1402 _1718) (h1 : term9 _1718 R) : term9 _1718 R.
Proof. exact (h1). Qed.
Lemma lem7417 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term0 A P Q.
Proof. exact (@lem7409 A P Q (@lem7363 A P Q)). Qed.
Lemma lem7418 {_1718 : Type'} (P : _1718 -> Prop) (Q : _1718 -> Prop) : term0 _1718 P Q.
Proof. exact (@lem7417 _1718 P Q). Qed.
Lemma lem7419 {_1718 : Type'} (R : type1402 _1718) (P : type1402 _1718) : term10 _1718 R P.
Proof. exact (@lem7418 _1718 (term11 _1718 R) (term12 _1718 P)). Qed.
Lemma lem7420 {_1718 : Type'} (R : type1402 _1718) (x : _1718) : (term13 _1718 R x) = (term14 _1718 R x).
Proof. exact (eq_refl (term13 _1718 R x)). Qed.
Lemma lem7421 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7422 {_1718 : Type'} (R : type1402 _1718) (x : _1718) : (term15 _1718 R x) = (term16 _1718 R x).
Proof. exact (MK_COMB (@lem7421) (@lem7420 _1718 R x)). Qed.
Lemma lem7423 {_1718 : Type'} (P : type1402 _1718) (x : _1718) : (term17 _1718 P x) = (term18 _1718 P x).
Proof. exact (eq_refl (term17 _1718 P x)). Qed.
Lemma lem7424 {_1718 : Type'} (R : type1402 _1718) (P : type1402 _1718) (x : _1718) : (term19 _1718 R P x) = (term20 _1718 R P x).
Proof. exact (MK_COMB (@lem7422 _1718 R x) (@lem7423 _1718 P x)). Qed.
Lemma lem7425 {_1718 : Type'} (R : type1402 _1718) (P : type1402 _1718) : (term21 _1718 R P) = (term22 _1718 R P).
Proof. exact (fun_ext (fun x : _1718 => @lem7424 _1718 R P x)). Qed.
Lemma lem7426 {_1718 : Type'} : (@all _1718) = (@all _1718).
Proof. exact (eq_refl (@all _1718)). Qed.
Lemma lem7427 {_1718 : Type'} (R : type1402 _1718) (P : type1402 _1718) : (term23 _1718 R P) = (term24 _1718 R P).
Proof. exact (MK_COMB (@lem7426 _1718) (@lem7425 _1718 R P)). Qed.
Lemma lem7428 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7429 {_1718 : Type'} (R : type1402 _1718) (P : type1402 _1718) : (term25 _1718 R P) = (term26 _1718 R P).
Proof. exact (MK_COMB (@lem7428) (@lem7427 _1718 R P)). Qed.
Lemma lem7430 {_1718 : Type'} (R : type1402 _1718) (x : _1718) : (term13 _1718 R x) = (term14 _1718 R x).
Proof. exact (eq_refl (term13 _1718 R x)). Qed.
Lemma lem7431 {_1718 : Type'} (R : type1402 _1718) : (term27 _1718 R) = (term11 _1718 R).
Proof. exact (fun_ext (fun x : _1718 => @lem7430 _1718 R x)). Qed.
Lemma lem7432 {_1718 : Type'} : (@all _1718) = (@all _1718).
Proof. exact (eq_refl (@all _1718)). Qed.
Lemma lem7433 {_1718 : Type'} (R : type1402 _1718) : (term28 _1718 R) = (term9 _1718 R).
Proof. exact (MK_COMB (@lem7432 _1718) (@lem7431 _1718 R)). Qed.
Lemma lem7434 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7435 {_1718 : Type'} (R : type1402 _1718) : (term29 _1718 R) = (term30 _1718 R).
Proof. exact (MK_COMB (@lem7434) (@lem7433 _1718 R)). Qed.
Lemma lem7436 {_1718 : Type'} (P : type1402 _1718) (x : _1718) : (term17 _1718 P x) = (term18 _1718 P x).
Proof. exact (eq_refl (term17 _1718 P x)). Qed.
Lemma lem7437 {_1718 : Type'} (P : type1402 _1718) : (term31 _1718 P) = (term12 _1718 P).
Proof. exact (fun_ext (fun x : _1718 => @lem7436 _1718 P x)). Qed.
Lemma lem7438 {_1718 : Type'} : (@all _1718) = (@all _1718).
Proof. exact (eq_refl (@all _1718)). Qed.
Lemma lem7439 {_1718 : Type'} (P : type1402 _1718) : (term32 _1718 P) = (term33 _1718 P).
Proof. exact (MK_COMB (@lem7438 _1718) (@lem7437 _1718 P)). Qed.
Lemma lem7440 {_1718 : Type'} (R : type1402 _1718) (P : type1402 _1718) : (term34 _1718 R P) = (term35 _1718 R P).
Proof. exact (MK_COMB (@lem7435 _1718 R) (@lem7439 _1718 P)). Qed.
Lemma lem7441 {_1718 : Type'} (R : type1402 _1718) (P : type1402 _1718) : (term10 _1718 R P) = (term36 _1718 R P).
Proof. exact (MK_COMB (@lem7429 _1718 R P) (@lem7440 _1718 R P)). Qed.
Lemma lem7442 {_1718 : Type'} (R : type1402 _1718) (P : type1402 _1718) : term36 _1718 R P.
Proof. exact (EQ_MP (@lem7441 _1718 R P) (@lem7419 _1718 R P)). Qed.
Lemma lem7444 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term0 A P Q.
Proof. exact (@lem7409 A P Q (@lem7363 A P Q)). Qed.
Lemma lem7445 {_1718 : Type'} (P : _1718 -> Prop) (Q : _1718 -> Prop) : term0 _1718 P Q.
Proof. exact (@lem7444 _1718 P Q). Qed.
Lemma lem7446 {_1718 : Type'} (R : type1402 _1718) (P : type1402 _1718) (x : _1718) : term37 _1718 R P x.
Proof. exact (@lem7445 _1718 (term38 _1718 R x) (term39 _1718 P x)). Qed.
Lemma lem7447 {_1718 : Type'} (R : type1402 _1718) (y : _1718) (x : _1718) : (term40 _1718 R x y) = (term41 _1718 R y x).
Proof. exact (eq_refl (term40 _1718 R x y)). Qed.
Lemma lem7448 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7449 {_1718 : Type'} (R : type1402 _1718) (y : _1718) (x : _1718) : (term42 _1718 R x y) = (term43 _1718 R y x).
Proof. exact (MK_COMB (@lem7448) (@lem7447 _1718 R y x)). Qed.
Lemma lem7450 {_1718 : Type'} (P : type1402 _1718) (x : _1718) (y : _1718) : (term44 _1718 P x y) = (P x y).
Proof. exact (eq_refl (term44 _1718 P x y)). Qed.
Lemma lem7451 {_1718 : Type'} (R : type1402 _1718) (P : type1402 _1718) (x : _1718) (y : _1718) : (term45 _1718 R P x y) = (term46 _1718 R P x y).
Proof. exact (MK_COMB (@lem7449 _1718 R y x) (@lem7450 _1718 P x y)). Qed.
Lemma lem7452 {_1718 : Type'} (R : type1402 _1718) (P : type1402 _1718) (x : _1718) : (term47 _1718 R P x) = (term48 _1718 R P x).
Proof. exact (fun_ext (fun y : _1718 => @lem7451 _1718 R P x y)). Qed.
Lemma lem7453 {_1718 : Type'} : (@all _1718) = (@all _1718).
Proof. exact (eq_refl (@all _1718)). Qed.
Lemma lem7454 {_1718 : Type'} (R : type1402 _1718) (P : type1402 _1718) (x : _1718) : (term49 _1718 R P x) = (term50 _1718 R P x).
Proof. exact (MK_COMB (@lem7453 _1718) (@lem7452 _1718 R P x)). Qed.
Lemma lem7455 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7456 {_1718 : Type'} (R : type1402 _1718) (P : type1402 _1718) (x : _1718) : (term51 _1718 R P x) = (term52 _1718 R P x).
Proof. exact (MK_COMB (@lem7455) (@lem7454 _1718 R P x)). Qed.
Lemma lem7457 {_1718 : Type'} (R : type1402 _1718) (y : _1718) (x : _1718) : (term40 _1718 R x y) = (term41 _1718 R y x).
Proof. exact (eq_refl (term40 _1718 R x y)). Qed.
Lemma lem7458 {_1718 : Type'} (R : type1402 _1718) (x : _1718) : (term53 _1718 R x) = (term38 _1718 R x).
Proof. exact (fun_ext (fun y : _1718 => @lem7457 _1718 R y x)). Qed.
Lemma lem7459 {_1718 : Type'} : (@all _1718) = (@all _1718).
Proof. exact (eq_refl (@all _1718)). Qed.
Lemma lem7460 {_1718 : Type'} (R : type1402 _1718) (x : _1718) : (term54 _1718 R x) = (term14 _1718 R x).
Proof. exact (MK_COMB (@lem7459 _1718) (@lem7458 _1718 R x)). Qed.
Lemma lem7461 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7462 {_1718 : Type'} (R : type1402 _1718) (x : _1718) : (term55 _1718 R x) = (term16 _1718 R x).
Proof. exact (MK_COMB (@lem7461) (@lem7460 _1718 R x)). Qed.
Lemma lem7463 {_1718 : Type'} (P : type1402 _1718) (x : _1718) (y : _1718) : (term44 _1718 P x y) = (P x y).
Proof. exact (eq_refl (term44 _1718 P x y)). Qed.
Lemma lem7464 {_1718 : Type'} (P : type1402 _1718) (x : _1718) : (term56 _1718 P x) = (term39 _1718 P x).
Proof. exact (fun_ext (fun y : _1718 => @lem7463 _1718 P x y)). Qed.
Lemma lem7465 {_1718 : Type'} : (@all _1718) = (@all _1718).
Proof. exact (eq_refl (@all _1718)). Qed.
Lemma lem7466 {_1718 : Type'} (P : type1402 _1718) (x : _1718) : (term57 _1718 P x) = (term18 _1718 P x).
Proof. exact (MK_COMB (@lem7465 _1718) (@lem7464 _1718 P x)). Qed.
Lemma lem7467 {_1718 : Type'} (R : type1402 _1718) (P : type1402 _1718) (x : _1718) : (term58 _1718 R P x) = (term20 _1718 R P x).
Proof. exact (MK_COMB (@lem7462 _1718 R x) (@lem7466 _1718 P x)). Qed.
Lemma lem7468 {_1718 : Type'} (R : type1402 _1718) (P : type1402 _1718) (x : _1718) : (term37 _1718 R P x) = (term59 _1718 R P x).
Proof. exact (MK_COMB (@lem7456 _1718 R P x) (@lem7467 _1718 R P x)). Qed.
Lemma lem7469 {_1718 : Type'} (R : type1402 _1718) (P : type1402 _1718) (x : _1718) : term59 _1718 R P x.
Proof. exact (EQ_MP (@lem7468 _1718 R P x) (@lem7446 _1718 R P x)). Qed.
Lemma lem7472 {_1718 : Type'} (R : type1402 _1718) (y : _1718) (x : _1718) (h1 : term41 _1718 R y x) : term41 _1718 R y x.
Proof. exact (h1). Qed.
Lemma lem7473 {_1718 : Type'} (R : type1402 _1718) (x : _1718) (y : _1718) (h1 : R x y) : R x y.
Proof. exact (h1). Qed.
Lemma lem7474 {_1718 : Type'} (R : type1402 _1718) (y : _1718) (x : _1718) (h1 : R y x) : R y x.
Proof. exact (h1). Qed.
Lemma lem7475 {_1718 : Type'} (x : _1718) (P : type1402 _1718) (h1 : term7 _1718 P) : term60 _1718 P x.
Proof. exact (@lem7413 _1718 P h1 x). Qed.
Lemma lem7476 {_1718 : Type'} (P : type1402 _1718) (x : _1718) : (term60 _1718 P x) = (term61 _1718 P x).
Proof. exact (eq_refl (term60 _1718 P x)). Qed.
Lemma lem7477 {_1718 : Type'} (x : _1718) (P : type1402 _1718) (h1 : term7 _1718 P) : term61 _1718 P x.
Proof. exact (EQ_MP (@lem7476 _1718 P x) (@lem7475 _1718 x P h1)). Qed.
Lemma lem7478 {_1718 : Type'} (x : _1718) (y : _1718) (P : type1402 _1718) (h1 : term7 _1718 P) : term62 _1718 P x y.
Proof. exact (@lem7477 _1718 x P h1 y). Qed.
Lemma lem7479 {_1718 : Type'} (P : type1402 _1718) (y : _1718) (x : _1718) : (term62 _1718 P x y) = (term63 _1718 P y x).
Proof. exact (eq_refl (term62 _1718 P x y)). Qed.
Lemma lem7480 {_1718 : Type'} (y : _1718) (x : _1718) (P : type1402 _1718) (h1 : term7 _1718 P) : term63 _1718 P y x.
Proof. exact (EQ_MP (@lem7479 _1718 P y x) (@lem7478 _1718 x y P h1)). Qed.
Lemma lem7481 {_1718 : Type'} (P : type1402 _1718) (x : _1718) (y : _1718) (h1 : P x y) : P x y.
Proof. exact (h1). Qed.
Lemma lem7482 {_1718 : Type'} (P : type1402 _1718) (x : _1718) (y : _1718) (h1 : term7 _1718 P) (h2 : P x y) : P y x.
Proof. exact (@lem7480 _1718 y x P h1 (@lem7481 _1718 P x y h2)). Qed.
Lemma lem7483 {_1718 : Type'} (P : type1402 _1718) (y : _1718) (x : _1718) : (P y x) = ((P y x) = True).
Proof. exact (@lem7 (P y x)). Qed.
Lemma lem7484 {_1718 : Type'} (P : type1402 _1718) (x : _1718) (y : _1718) (h1 : term7 _1718 P) (h2 : P x y) : (P y x) = True.
Proof. exact (EQ_MP (@lem7483 _1718 P y x) (@lem7482 _1718 P x y h1 h2)). Qed.
Lemma lem7490 {_1718 : Type'} (x : _1718) (R : type1402 _1718) (P : type1402 _1718) (h1 : term8 _1718 R P) : term64 _1718 R P x.
Proof. exact (@lem7414 _1718 R P h1 x). Qed.
Lemma lem7491 {_1718 : Type'} (R : type1402 _1718) (P : type1402 _1718) (x : _1718) : (term64 _1718 R P x) = (term65 _1718 R P x).
Proof. exact (eq_refl (term64 _1718 R P x)). Qed.
Lemma lem7492 {_1718 : Type'} (x : _1718) (R : type1402 _1718) (P : type1402 _1718) (h1 : term8 _1718 R P) : term65 _1718 R P x.
Proof. exact (EQ_MP (@lem7491 _1718 R P x) (@lem7490 _1718 x R P h1)). Qed.
Lemma lem7493 {_1718 : Type'} (x : _1718) (y : _1718) (R : type1402 _1718) (P : type1402 _1718) (h1 : term8 _1718 R P) : term66 _1718 R P x y.
Proof. exact (@lem7492 _1718 x R P h1 y). Qed.
Lemma lem7494 {_1718 : Type'} (R : type1402 _1718) (P : type1402 _1718) (x : _1718) (y : _1718) : (term66 _1718 R P x y) = (term67 _1718 R P x y).
Proof. exact (eq_refl (term66 _1718 R P x y)). Qed.
Lemma lem7495 {_1718 : Type'} (x : _1718) (y : _1718) (R : type1402 _1718) (P : type1402 _1718) (h1 : term8 _1718 R P) : term67 _1718 R P x y.
Proof. exact (EQ_MP (@lem7494 _1718 R P x y) (@lem7493 _1718 x y R P h1)). Qed.
Lemma lem7496 {_1718 : Type'} (R : type1402 _1718) (x : _1718) (y : _1718) (h1 : R x y) : R x y.
Proof. exact (h1). Qed.
Lemma lem7497 {_1718 : Type'} (P : type1402 _1718) (R : type1402 _1718) (x : _1718) (y : _1718) (h1 : term8 _1718 R P) (h2 : R x y) : P x y.
Proof. exact (@lem7495 _1718 x y R P h1 (@lem7496 _1718 R x y h2)). Qed.
Lemma lem7498 {_1718 : Type'} (P : type1402 _1718) (x : _1718) (y : _1718) : (P x y) = ((P x y) = True).
Proof. exact (@lem7 (P x y)). Qed.
Lemma lem7499 {_1718 : Type'} (P : type1402 _1718) (R : type1402 _1718) (x : _1718) (y : _1718) (h1 : term8 _1718 R P) (h2 : R x y) : (P x y) = True.
Proof. exact (EQ_MP (@lem7498 _1718 P x y) (@lem7497 _1718 P R x y h1 h2)). Qed.
Lemma lem7505 {_1718 : Type'} (R : type1402 _1718) (x : _1718) (y : _1718) : (R x y) = ((R x y) = True).
Proof. exact (@lem7 (R x y)). Qed.
Lemma lem7508 {_1718 : Type'} (y : _1718) (x : _1718) (P : type1402 _1718) (h1 : term7 _1718 P) : term68 _1718 P y x.
Proof. exact (fun h0 : P x y => @lem7484 _1718 P x y h1 h0). Qed.
Lemma lem7509 {_1718 : Type'} (y : _1718) (x : _1718) (P : type1402 _1718) (h1 : term7 _1718 P) : term68 _1718 P y x.
Proof. exact (@lem7508 _1718 y x P h1). Qed.
Lemma lem7510 {_1718 : Type'} (x : _1718) (y : _1718) (P : type1402 _1718) (h1 : term7 _1718 P) : term68 _1718 P x y.
Proof. exact (@lem7509 _1718 x y P h1). Qed.
Lemma lem7512 {_1718 : Type'} (y : _1718) (x : _1718) (P : type1402 _1718) (h1 : term7 _1718 P) : term68 _1718 P y x.
Proof. exact (fun h0 : P x y => @lem7484 _1718 P x y h1 h0). Qed.
Lemma lem7513 {_1718 : Type'} (y : _1718) (x : _1718) (P : type1402 _1718) (h1 : term7 _1718 P) : term68 _1718 P y x.
Proof. exact (@lem7512 _1718 y x P h1). Qed.
Lemma lem7528 {_1718 : Type'} (x : _1718) (y : _1718) (R : type1402 _1718) (P : type1402 _1718) (h1 : term8 _1718 R P) : term69 _1718 R P x y.
Proof. exact (fun h0 : R x y => @lem7499 _1718 P R x y h1 h0). Qed.
Lemma lem7529 {_1718 : Type'} (x : _1718) (y : _1718) (R : type1402 _1718) (P : type1402 _1718) (h1 : term8 _1718 R P) : term69 _1718 R P x y.
Proof. exact (@lem7528 _1718 x y R P h1). Qed.
Lemma lem7531 {_1718 : Type'} (R : type1402 _1718) (x : _1718) (y : _1718) (h1 : R x y) : (R x y) = True.
Proof. exact (EQ_MP (@lem7505 _1718 R x y) (@lem7473 _1718 R x y h1)). Qed.
Lemma lem7532 {_1718 : Type'} (R : type1402 _1718) (x : _1718) (y : _1718) (h1 : R x y) : True = (R x y).
Proof. exact (SYM (@lem7531 _1718 R x y h1)). Qed.
Lemma lem7533 {_1718 : Type'} (R : type1402 _1718) (x : _1718) (y : _1718) (h1 : R x y) : R x y.
Proof. exact (EQ_MP (@lem7532 _1718 R x y h1) (@lem0)). Qed.
Lemma lem7534 {_1718 : Type'} (P : type1402 _1718) (R : type1402 _1718) (x : _1718) (y : _1718) (h1 : term8 _1718 R P) (h2 : R x y) : (P x y) = True.
Proof. exact (@lem7529 _1718 x y R P h1 (@lem7533 _1718 R x y h2)). Qed.
Lemma lem7535 {_1718 : Type'} (P : type1402 _1718) (R : type1402 _1718) (x : _1718) (y : _1718) (h1 : term8 _1718 R P) (h2 : R x y) : True = (P x y).
Proof. exact (SYM (@lem7534 _1718 P R x y h1 h2)). Qed.
Lemma lem7536 {_1718 : Type'} (P : type1402 _1718) (R : type1402 _1718) (x : _1718) (y : _1718) (h1 : term8 _1718 R P) (h2 : R x y) : P x y.
Proof. exact (EQ_MP (@lem7535 _1718 P R x y h1 h2) (@lem0)). Qed.
Lemma lem7537 {_1718 : Type'} (P : type1402 _1718) (R : type1402 _1718) (x : _1718) (y : _1718) (h1 : term7 _1718 P) (h2 : term8 _1718 R P) (h3 : R x y) : (P y x) = True.
Proof. exact (@lem7513 _1718 y x P h1 (@lem7536 _1718 P R x y h2 h3)). Qed.
Lemma lem7538 {_1718 : Type'} (P : type1402 _1718) (R : type1402 _1718) (x : _1718) (y : _1718) (h1 : term7 _1718 P) (h2 : term8 _1718 R P) (h3 : R x y) : True = (P y x).
Proof. exact (SYM (@lem7537 _1718 P R x y h1 h2 h3)). Qed.
Lemma lem7539 {_1718 : Type'} (P : type1402 _1718) (R : type1402 _1718) (x : _1718) (y : _1718) (h1 : term7 _1718 P) (h2 : term8 _1718 R P) (h3 : R x y) : P y x.
Proof. exact (EQ_MP (@lem7538 _1718 P R x y h1 h2 h3) (@lem0)). Qed.
Lemma lem7540 {_1718 : Type'} (P : type1402 _1718) (R : type1402 _1718) (x : _1718) (y : _1718) (h1 : term7 _1718 P) (h2 : term8 _1718 R P) (h3 : R x y) : (P x y) = True.
Proof. exact (@lem7510 _1718 x y P h1 (@lem7539 _1718 P R x y h1 h2 h3)). Qed.
Lemma lem7541 {_1718 : Type'} (P : type1402 _1718) (R : type1402 _1718) (x : _1718) (y : _1718) (h1 : term7 _1718 P) (h2 : term8 _1718 R P) (h3 : R x y) : True = (P x y).
Proof. exact (SYM (@lem7540 _1718 P R x y h1 h2 h3)). Qed.
Lemma lem7542 {_1718 : Type'} (P : type1402 _1718) (R : type1402 _1718) (x : _1718) (y : _1718) (h1 : term7 _1718 P) (h2 : term8 _1718 R P) (h3 : R x y) : P x y.
Proof. exact (EQ_MP (@lem7541 _1718 P R x y h1 h2 h3) (@lem0)). Qed.
Lemma lem7543 {_1718 : Type'} (x : _1718) (P : type1402 _1718) (h1 : term7 _1718 P) : term60 _1718 P x.
Proof. exact (@lem7413 _1718 P h1 x). Qed.
Lemma lem7544 {_1718 : Type'} (P : type1402 _1718) (x : _1718) : (term60 _1718 P x) = (term61 _1718 P x).
Proof. exact (eq_refl (term60 _1718 P x)). Qed.
Lemma lem7545 {_1718 : Type'} (x : _1718) (P : type1402 _1718) (h1 : term7 _1718 P) : term61 _1718 P x.
Proof. exact (EQ_MP (@lem7544 _1718 P x) (@lem7543 _1718 x P h1)). Qed.
Lemma lem7546 {_1718 : Type'} (x : _1718) (y : _1718) (P : type1402 _1718) (h1 : term7 _1718 P) : term62 _1718 P x y.
Proof. exact (@lem7545 _1718 x P h1 y). Qed.
Lemma lem7547 {_1718 : Type'} (P : type1402 _1718) (y : _1718) (x : _1718) : (term62 _1718 P x y) = (term63 _1718 P y x).
Proof. exact (eq_refl (term62 _1718 P x y)). Qed.
Lemma lem7548 {_1718 : Type'} (y : _1718) (x : _1718) (P : type1402 _1718) (h1 : term7 _1718 P) : term63 _1718 P y x.
Proof. exact (EQ_MP (@lem7547 _1718 P y x) (@lem7546 _1718 x y P h1)). Qed.
Lemma lem7549 {_1718 : Type'} (P : type1402 _1718) (x : _1718) (y : _1718) (h1 : P x y) : P x y.
Proof. exact (h1). Qed.
Lemma lem7550 {_1718 : Type'} (P : type1402 _1718) (x : _1718) (y : _1718) (h1 : term7 _1718 P) (h2 : P x y) : P y x.
Proof. exact (@lem7548 _1718 y x P h1 (@lem7549 _1718 P x y h2)). Qed.
Lemma lem7551 {_1718 : Type'} (P : type1402 _1718) (y : _1718) (x : _1718) : (P y x) = ((P y x) = True).
Proof. exact (@lem7 (P y x)). Qed.
Lemma lem7552 {_1718 : Type'} (P : type1402 _1718) (x : _1718) (y : _1718) (h1 : term7 _1718 P) (h2 : P x y) : (P y x) = True.
Proof. exact (EQ_MP (@lem7551 _1718 P y x) (@lem7550 _1718 P x y h1 h2)). Qed.
Lemma lem7558 {_1718 : Type'} (x : _1718) (R : type1402 _1718) (P : type1402 _1718) (h1 : term8 _1718 R P) : term64 _1718 R P x.
Proof. exact (@lem7414 _1718 R P h1 x). Qed.
Lemma lem7559 {_1718 : Type'} (R : type1402 _1718) (P : type1402 _1718) (x : _1718) : (term64 _1718 R P x) = (term65 _1718 R P x).
Proof. exact (eq_refl (term64 _1718 R P x)). Qed.
Lemma lem7560 {_1718 : Type'} (x : _1718) (R : type1402 _1718) (P : type1402 _1718) (h1 : term8 _1718 R P) : term65 _1718 R P x.
Proof. exact (EQ_MP (@lem7559 _1718 R P x) (@lem7558 _1718 x R P h1)). Qed.
Lemma lem7561 {_1718 : Type'} (x : _1718) (y : _1718) (R : type1402 _1718) (P : type1402 _1718) (h1 : term8 _1718 R P) : term66 _1718 R P x y.
Proof. exact (@lem7560 _1718 x R P h1 y). Qed.
Lemma lem7562 {_1718 : Type'} (R : type1402 _1718) (P : type1402 _1718) (x : _1718) (y : _1718) : (term66 _1718 R P x y) = (term67 _1718 R P x y).
Proof. exact (eq_refl (term66 _1718 R P x y)). Qed.
Lemma lem7563 {_1718 : Type'} (x : _1718) (y : _1718) (R : type1402 _1718) (P : type1402 _1718) (h1 : term8 _1718 R P) : term67 _1718 R P x y.
Proof. exact (EQ_MP (@lem7562 _1718 R P x y) (@lem7561 _1718 x y R P h1)). Qed.
Lemma lem7564 {_1718 : Type'} (R : type1402 _1718) (x : _1718) (y : _1718) (h1 : R x y) : R x y.
Proof. exact (h1). Qed.
Lemma lem7565 {_1718 : Type'} (P : type1402 _1718) (R : type1402 _1718) (x : _1718) (y : _1718) (h1 : term8 _1718 R P) (h2 : R x y) : P x y.
Proof. exact (@lem7563 _1718 x y R P h1 (@lem7564 _1718 R x y h2)). Qed.
Lemma lem7566 {_1718 : Type'} (P : type1402 _1718) (x : _1718) (y : _1718) : (P x y) = ((P x y) = True).
Proof. exact (@lem7 (P x y)). Qed.
Lemma lem7567 {_1718 : Type'} (P : type1402 _1718) (R : type1402 _1718) (x : _1718) (y : _1718) (h1 : term8 _1718 R P) (h2 : R x y) : (P x y) = True.
Proof. exact (EQ_MP (@lem7566 _1718 P x y) (@lem7565 _1718 P R x y h1 h2)). Qed.
Lemma lem7573 {_1718 : Type'} (R : type1402 _1718) (y : _1718) (x : _1718) : (R y x) = ((R y x) = True).
Proof. exact (@lem7 (R y x)). Qed.
Lemma lem7576 {_1718 : Type'} (y : _1718) (x : _1718) (P : type1402 _1718) (h1 : term7 _1718 P) : term68 _1718 P y x.
Proof. exact (fun h0 : P x y => @lem7552 _1718 P x y h1 h0). Qed.
Lemma lem7577 {_1718 : Type'} (y : _1718) (x : _1718) (P : type1402 _1718) (h1 : term7 _1718 P) : term68 _1718 P y x.
Proof. exact (@lem7576 _1718 y x P h1). Qed.
Lemma lem7578 {_1718 : Type'} (x : _1718) (y : _1718) (P : type1402 _1718) (h1 : term7 _1718 P) : term68 _1718 P x y.
Proof. exact (@lem7577 _1718 x y P h1). Qed.
Lemma lem7603 {_1718 : Type'} (x : _1718) (y : _1718) (R : type1402 _1718) (P : type1402 _1718) (h1 : term8 _1718 R P) : term69 _1718 R P x y.
Proof. exact (fun h0 : R x y => @lem7567 _1718 P R x y h1 h0). Qed.
Lemma lem7604 {_1718 : Type'} (x : _1718) (y : _1718) (R : type1402 _1718) (P : type1402 _1718) (h1 : term8 _1718 R P) : term69 _1718 R P x y.
Proof. exact (@lem7603 _1718 x y R P h1). Qed.
Lemma lem7605 {_1718 : Type'} (y : _1718) (x : _1718) (R : type1402 _1718) (P : type1402 _1718) (h1 : term8 _1718 R P) : term69 _1718 R P y x.
Proof. exact (@lem7604 _1718 y x R P h1). Qed.
Lemma lem7607 {_1718 : Type'} (R : type1402 _1718) (y : _1718) (x : _1718) (h1 : R y x) : (R y x) = True.
Proof. exact (EQ_MP (@lem7573 _1718 R y x) (@lem7474 _1718 R y x h1)). Qed.
Lemma lem7608 {_1718 : Type'} (R : type1402 _1718) (y : _1718) (x : _1718) (h1 : R y x) : True = (R y x).
Proof. exact (SYM (@lem7607 _1718 R y x h1)). Qed.
Lemma lem7609 {_1718 : Type'} (R : type1402 _1718) (y : _1718) (x : _1718) (h1 : R y x) : R y x.
Proof. exact (EQ_MP (@lem7608 _1718 R y x h1) (@lem0)). Qed.
Lemma lem7610 {_1718 : Type'} (P : type1402 _1718) (R : type1402 _1718) (y : _1718) (x : _1718) (h1 : term8 _1718 R P) (h2 : R y x) : (P y x) = True.
Proof. exact (@lem7605 _1718 y x R P h1 (@lem7609 _1718 R y x h2)). Qed.
Lemma lem7611 {_1718 : Type'} (P : type1402 _1718) (R : type1402 _1718) (y : _1718) (x : _1718) (h1 : term8 _1718 R P) (h2 : R y x) : True = (P y x).
Proof. exact (SYM (@lem7610 _1718 P R y x h1 h2)). Qed.
Lemma lem7612 {_1718 : Type'} (P : type1402 _1718) (R : type1402 _1718) (y : _1718) (x : _1718) (h1 : term8 _1718 R P) (h2 : R y x) : P y x.
Proof. exact (EQ_MP (@lem7611 _1718 P R y x h1 h2) (@lem0)). Qed.
Lemma lem7613 {_1718 : Type'} (P : type1402 _1718) (R : type1402 _1718) (y : _1718) (x : _1718) (h1 : term7 _1718 P) (h2 : term8 _1718 R P) (h3 : R y x) : (P x y) = True.
Proof. exact (@lem7578 _1718 x y P h1 (@lem7612 _1718 P R y x h2 h3)). Qed.
Lemma lem7614 {_1718 : Type'} (P : type1402 _1718) (R : type1402 _1718) (y : _1718) (x : _1718) (h1 : term7 _1718 P) (h2 : term8 _1718 R P) (h3 : R y x) : True = (P x y).
Proof. exact (SYM (@lem7613 _1718 P R y x h1 h2 h3)). Qed.
Lemma lem7615 {_1718 : Type'} (P : type1402 _1718) (R : type1402 _1718) (y : _1718) (x : _1718) (h1 : term7 _1718 P) (h2 : term8 _1718 R P) (h3 : R y x) : P x y.
Proof. exact (EQ_MP (@lem7614 _1718 P R y x h1 h2 h3) (@lem0)). Qed.
Lemma lem7616 {_1718 : Type'} (P : type1402 _1718) (R : type1402 _1718) (y : _1718) (x : _1718) (h1 : term7 _1718 P) (h2 : term8 _1718 R P) (h3 : R y x) : (R y x) = (P x y).
Proof. exact (prop_ext (fun h4 : R y x => @lem7615 _1718 P R y x h1 h2 h3) (fun h4 : P x y => @lem7474 _1718 R y x h3)). Qed.
Lemma lem7617 {_1718 : Type'} (P : type1402 _1718) (R : type1402 _1718) (y : _1718) (x : _1718) (h1 : term7 _1718 P) (h2 : term8 _1718 R P) (h3 : R y x) : P x y.
Proof. exact (EQ_MP (@lem7616 _1718 P R y x h1 h2 h3) (@lem7474 _1718 R y x h3)). Qed.
Lemma lem7618 {_1718 : Type'} (P : type1402 _1718) (R : type1402 _1718) (x : _1718) (y : _1718) (h1 : term7 _1718 P) (h2 : term8 _1718 R P) (h3 : R x y) : (R x y) = (P x y).
Proof. exact (prop_ext (fun h4 : R x y => @lem7542 _1718 P R x y h1 h2 h3) (fun h4 : P x y => @lem7473 _1718 R x y h3)). Qed.
Lemma lem7619 {_1718 : Type'} (P : type1402 _1718) (R : type1402 _1718) (x : _1718) (y : _1718) (h1 : term7 _1718 P) (h2 : term8 _1718 R P) (h3 : R x y) : P x y.
Proof. exact (EQ_MP (@lem7618 _1718 P R x y h1 h2 h3) (@lem7473 _1718 R x y h3)). Qed.
Lemma lem7620 {_1718 : Type'} (P : type1402 _1718) (R : type1402 _1718) (y : _1718) (x : _1718) (h1 : term7 _1718 P) (h2 : term8 _1718 R P) (h3 : term41 _1718 R y x) : P x y.
Proof. exact (or_elim (@lem7472 _1718 R y x h3) (fun h0 : R x y => @lem7619 _1718 P R x y h1 h2 h0) (fun h0 : R y x => @lem7617 _1718 P R y x h1 h2 h0)). Qed.
Lemma lem7621 {_1718 : Type'} (x : _1718) (y : _1718) (R : type1402 _1718) (P : type1402 _1718) (h1 : term7 _1718 P) (h2 : term8 _1718 R P) : term46 _1718 R P x y.
Proof. exact (fun h0 : term41 _1718 R y x => @lem7620 _1718 P R y x h1 h2 h0). Qed.
Lemma lem7626 {_1718 : Type'} (x : _1718) (R : type1402 _1718) (P : type1402 _1718) (h1 : term7 _1718 P) (h2 : term8 _1718 R P) : term50 _1718 R P x.
Proof. exact (fun y : _1718 => @lem7621 _1718 x y R P h1 h2). Qed.
Lemma lem7627 {_1718 : Type'} (x : _1718) (R : type1402 _1718) (P : type1402 _1718) (h1 : term7 _1718 P) (h2 : term8 _1718 R P) : term20 _1718 R P x.
Proof. exact (@lem7469 _1718 R P x (@lem7626 _1718 x R P h1 h2)). Qed.
Lemma lem7632 {_1718 : Type'} (R : type1402 _1718) (P : type1402 _1718) (h1 : term7 _1718 P) (h2 : term8 _1718 R P) : term24 _1718 R P.
Proof. exact (fun x : _1718 => @lem7627 _1718 x R P h1 h2). Qed.
Lemma lem7633 {_1718 : Type'} (R : type1402 _1718) (P : type1402 _1718) (h1 : term7 _1718 P) (h2 : term8 _1718 R P) : term35 _1718 R P.
Proof. exact (@lem7442 _1718 R P (@lem7632 _1718 R P h1 h2)). Qed.
Lemma lem7634 {_1718 : Type'} (R : type1402 _1718) (P : type1402 _1718) (h1 : term5 _1718 R P) : term6 _1718 R P.
Proof. exact (proj2 (@lem7411 _1718 R P h1)). Qed.
Lemma lem7635 {_1718 : Type'} (R : type1402 _1718) (P : type1402 _1718) (h1 : term5 _1718 R P) : term7 _1718 P.
Proof. exact (proj1 (@lem7411 _1718 R P h1)). Qed.
Lemma lem7636 {_1718 : Type'} (R : type1402 _1718) (P : type1402 _1718) (h1 : term6 _1718 R P) : term8 _1718 R P.
Proof. exact (proj2 (@lem7412 _1718 R P h1)). Qed.
Lemma lem7637 {_1718 : Type'} (R : type1402 _1718) (P : type1402 _1718) (h1 : term6 _1718 R P) : term9 _1718 R.
Proof. exact (proj1 (@lem7412 _1718 R P h1)). Qed.
Lemma lem7638 {_1718 : Type'} (R : type1402 _1718) (P : type1402 _1718) (h1 : term7 _1718 P) (h2 : term8 _1718 R P) : (term8 _1718 R P) = (term35 _1718 R P).
Proof. exact (prop_ext (fun h3 : term8 _1718 R P => @lem7633 _1718 R P h1 h2) (fun h3 : term35 _1718 R P => @lem7414 _1718 R P h2)). Qed.
Lemma lem7639 {_1718 : Type'} (R : type1402 _1718) (P : type1402 _1718) (h1 : term7 _1718 P) (h2 : term8 _1718 R P) : term35 _1718 R P.
Proof. exact (EQ_MP (@lem7638 _1718 R P h1 h2) (@lem7414 _1718 R P h2)). Qed.
Lemma lem7640 {_1718 : Type'} (P : type1402 _1718) (R : type1402 _1718) (h1 : term7 _1718 P) (h2 : term8 _1718 R P) (h3 : term9 _1718 R) : term33 _1718 P.
Proof. exact (@lem7639 _1718 R P h1 h2 (@lem7415 _1718 R h3)). Qed.
Lemma lem7641 {_1718 : Type'} (R : type1402 _1718) (P : type1402 _1718) (h1 : term7 _1718 P) (h2 : term9 _1718 R) (h3 : term6 _1718 R P) : (term8 _1718 R P) = (term33 _1718 P).
Proof. exact (prop_ext (fun h4 : term8 _1718 R P => @lem7640 _1718 P R h1 h4 h2) (fun h4 : term33 _1718 P => @lem7636 _1718 R P h3)). Qed.
Lemma lem7642 {_1718 : Type'} (R : type1402 _1718) (P : type1402 _1718) (h1 : term7 _1718 P) (h2 : term9 _1718 R) (h3 : term6 _1718 R P) : term33 _1718 P.
Proof. exact (EQ_MP (@lem7641 _1718 R P h1 h2 h3) (@lem7636 _1718 R P h3)). Qed.
Lemma lem7643 {_1718 : Type'} (R : type1402 _1718) (P : type1402 _1718) (h1 : term7 _1718 P) (h2 : term6 _1718 R P) : (term9 _1718 R) = (term33 _1718 P).
Proof. exact (prop_ext (fun h3 : term9 _1718 R => @lem7642 _1718 R P h1 h3 h2) (fun h3 : term33 _1718 P => @lem7637 _1718 R P h2)). Qed.
Lemma lem7644 {_1718 : Type'} (R : type1402 _1718) (P : type1402 _1718) (h1 : term7 _1718 P) (h2 : term6 _1718 R P) : term33 _1718 P.
Proof. exact (EQ_MP (@lem7643 _1718 R P h1 h2) (@lem7637 _1718 R P h2)). Qed.
Lemma lem7645 {_1718 : Type'} (R : type1402 _1718) (P : type1402 _1718) (h1 : term7 _1718 P) (h2 : term6 _1718 R P) : (term7 _1718 P) = (term33 _1718 P).
Proof. exact (prop_ext (fun h3 : term7 _1718 P => @lem7644 _1718 R P h1 h2) (fun h3 : term33 _1718 P => @lem7413 _1718 P h1)). Qed.
Lemma lem7646 {_1718 : Type'} (R : type1402 _1718) (P : type1402 _1718) (h1 : term7 _1718 P) (h2 : term6 _1718 R P) : term33 _1718 P.
Proof. exact (EQ_MP (@lem7645 _1718 R P h1 h2) (@lem7413 _1718 P h1)). Qed.
Lemma lem7647 {_1718 : Type'} (R : type1402 _1718) (P : type1402 _1718) (h1 : term7 _1718 P) (h2 : term5 _1718 R P) : (term6 _1718 R P) = (term33 _1718 P).
Proof. exact (prop_ext (fun h3 : term6 _1718 R P => @lem7646 _1718 R P h1 h3) (fun h3 : term33 _1718 P => @lem7634 _1718 R P h2)). Qed.
Lemma lem7648 {_1718 : Type'} (R : type1402 _1718) (P : type1402 _1718) (h1 : term7 _1718 P) (h2 : term5 _1718 R P) : term33 _1718 P.
Proof. exact (EQ_MP (@lem7647 _1718 R P h1 h2) (@lem7634 _1718 R P h2)). Qed.
Lemma lem7649 {_1718 : Type'} (R : type1402 _1718) (P : type1402 _1718) (h1 : term5 _1718 R P) : (term7 _1718 P) = (term33 _1718 P).
Proof. exact (prop_ext (fun h2 : term7 _1718 P => @lem7648 _1718 R P h2 h1) (fun h2 : term33 _1718 P => @lem7635 _1718 R P h1)). Qed.
Lemma lem7650 {_1718 : Type'} (R : type1402 _1718) (P : type1402 _1718) (h1 : term5 _1718 R P) : term33 _1718 P.
Proof. exact (EQ_MP (@lem7649 _1718 R P h1) (@lem7635 _1718 R P h1)). Qed.
Lemma lem7651 {_1718 : Type'} (R : type1402 _1718) (P : type1402 _1718) : term70 _1718 R P.
Proof. exact (fun h0 : term5 _1718 R P => @lem7650 _1718 R P h0). Qed.
Lemma lem7656 {_1718 : Type'} (R : type1402 _1718) : term71 _1718 R.
Proof. exact (fun P : type1402 _1718 => @lem7651 _1718 R P). Qed.
Lemma lem7661 {_1718 : Type'} : term72 _1718.
Proof. exact (fun R : type1402 _1718 => @lem7656 _1718 R). Qed.
