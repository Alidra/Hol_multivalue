Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EXISTS_CURRY_term_abbrevs.
Require Import EXISTS_UNCURRY_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm52758_spec.
Require Import thm52761_spec.
Lemma lem53496 {_5264 _5271 _5272 : Type'} : term0 _5264 _5271 _5272.
Proof. exact (EQ_MP (@lem52761 _5264 _5271 _5272) (@lem52758 _5264 _5271 _5272)). Qed.
Lemma lem53497 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) : term1 _5264 _5271 _5272 f.
Proof. exact (@lem53496 _5264 _5271 _5272 f). Qed.
Lemma lem53498 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) : (term1 _5264 _5271 _5272 f) = ((term2 _5264 _5271 _5272 f) = f).
Proof. exact (eq_refl (term1 _5264 _5271 _5272 f)). Qed.
Lemma lem53500 {A B C : Type'} (P : type443 A B C) : term3 A B C P.
Proof. exact (@lem53486 A B C P). Qed.
Lemma lem53501 {A B C : Type'} (P : type443 A B C) : (term3 A B C P) = ((term4 A B C P) = (term5 A B C P)).
Proof. exact (eq_refl (term3 A B C P)). Qed.
Lemma lem53520 {A B C : Type'} (P : type443 A B C) : (term4 A B C P) = (term5 A B C P).
Proof. exact (EQ_MP (@lem53501 A B C P) (@lem53500 A B C P)). Qed.
Lemma lem53521 {_5431 _5437 _5438 : Type'} (P : type876 _5431 _5437 _5438) : (term6 _5431 _5437 _5438 P) = (term7 _5431 _5437 _5438 P).
Proof. exact (@lem53520 _5438 _5437 _5431 P). Qed.
Lemma lem53522 {_5431 _5437 _5438 : Type'} (P : type333 _5431 _5437 _5438) : (term8 _5431 _5437 _5438 P) = (term9 _5431 _5437 _5438 P).
Proof. exact (@lem53521 _5431 _5437 _5438 (term10 _5431 _5437 _5438 P)). Qed.
Lemma lem53523 {_5431 _5437 _5438 : Type'} (P : type333 _5431 _5437 _5438) (f : type1518 _5431 _5437 _5438) : (term11 _5431 _5437 _5438 P f) = (term12 _5431 _5437 _5438 P f).
Proof. exact (eq_refl (term11 _5431 _5437 _5438 P f)). Qed.
Lemma lem53524 {_5431 _5437 _5438 : Type'} (P : type333 _5431 _5437 _5438) : (term13 _5431 _5437 _5438 P) = (term10 _5431 _5437 _5438 P).
Proof. exact (fun_ext (fun f : type1518 _5431 _5437 _5438 => @lem53523 _5431 _5437 _5438 P f)). Qed.
Lemma lem53525 {_5431 _5437 _5438 : Type'} : (@ex (_5438 -> _5437 -> _5431)) = (@ex (_5438 -> _5437 -> _5431)).
Proof. exact (eq_refl (@ex (_5438 -> _5437 -> _5431))). Qed.
Lemma lem53526 {_5431 _5437 _5438 : Type'} (P : type333 _5431 _5437 _5438) : (term8 _5431 _5437 _5438 P) = (term14 _5431 _5437 _5438 P).
Proof. exact (MK_COMB (@lem53525 _5431 _5437 _5438) (@lem53524 _5431 _5437 _5438 P)). Qed.
Lemma lem53527 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem53528 {_5431 _5437 _5438 : Type'} (P : type333 _5431 _5437 _5438) : (term15 _5431 _5437 _5438 P) = (term16 _5431 _5437 _5438 P).
Proof. exact (MK_COMB (@lem53527) (@lem53526 _5431 _5437 _5438 P)). Qed.
Lemma lem53529 {_5431 _5437 _5438 : Type'} (P : type333 _5431 _5437 _5438) (f : type1228 _5431 _5437 _5438) : (term17 _5431 _5437 _5438 P f) = (term18 _5431 _5437 _5438 P f).
Proof. exact (eq_refl (term17 _5431 _5437 _5438 P f)). Qed.
Lemma lem53530 {_5431 _5437 _5438 : Type'} (P : type333 _5431 _5437 _5438) : (term19 _5431 _5437 _5438 P) = (term20 _5431 _5437 _5438 P).
Proof. exact (fun_ext (fun f : type1228 _5431 _5437 _5438 => @lem53529 _5431 _5437 _5438 P f)). Qed.
Lemma lem53531 {_5431 _5437 _5438 : Type'} : (@ex ((prod _5438 _5437) -> _5431)) = (@ex ((prod _5438 _5437) -> _5431)).
Proof. exact (eq_refl (@ex ((prod _5438 _5437) -> _5431))). Qed.
Lemma lem53532 {_5431 _5437 _5438 : Type'} (P : type333 _5431 _5437 _5438) : (term9 _5431 _5437 _5438 P) = (term21 _5431 _5437 _5438 P).
Proof. exact (MK_COMB (@lem53531 _5431 _5437 _5438) (@lem53530 _5431 _5437 _5438 P)). Qed.
Lemma lem53533 {_5431 _5437 _5438 : Type'} (P : type333 _5431 _5437 _5438) : ((term8 _5431 _5437 _5438 P) = (term9 _5431 _5437 _5438 P)) = ((term14 _5431 _5437 _5438 P) = (term21 _5431 _5437 _5438 P)).
Proof. exact (MK_COMB (@lem53528 _5431 _5437 _5438 P) (@lem53532 _5431 _5437 _5438 P)). Qed.
Lemma lem53534 {_5431 _5437 _5438 : Type'} (P : type333 _5431 _5437 _5438) : (term14 _5431 _5437 _5438 P) = (term21 _5431 _5437 _5438 P).
Proof. exact (EQ_MP (@lem53533 _5431 _5437 _5438 P) (@lem53522 _5431 _5437 _5438 P)). Qed.
Lemma lem53571 {A B : Type'} (f : A -> B) (y : A) : (term22 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem53572 {_5431 _5437 _5438 : Type'} (f : type1518 _5431 _5437 _5438) (y : _5438) : (term23 _5431 _5437 _5438 f y) = (f y).
Proof. exact (@lem53571 _5438 (_5437 -> _5431) f y). Qed.
Lemma lem53573 {_5431 _5437 _5438 : Type'} (f : type1228 _5431 _5437 _5438) (a : _5438) : (term24 _5431 _5437 _5438 f a) = (term25 _5431 _5437 _5438 f a).
Proof. exact (@lem53572 _5431 _5437 _5438 (term26 _5431 _5437 _5438 f) a). Qed.
Lemma lem53574 {_5431 _5437 _5438 : Type'} (f : type1228 _5431 _5437 _5438) (a : _5438) : (term25 _5431 _5437 _5438 f a) = (term27 _5431 _5437 _5438 f a).
Proof. exact (eq_refl (term25 _5431 _5437 _5438 f a)). Qed.
Lemma lem53575 {_5431 _5437 _5438 : Type'} (f : type1228 _5431 _5437 _5438) : (term28 _5431 _5437 _5438 f) = (term26 _5431 _5437 _5438 f).
Proof. exact (fun_ext (fun a : _5438 => @lem53574 _5431 _5437 _5438 f a)). Qed.
Lemma lem53576 {_5438 : Type'} (a : _5438) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem53577 {_5431 _5437 _5438 : Type'} (f : type1228 _5431 _5437 _5438) (a : _5438) : (term24 _5431 _5437 _5438 f a) = (term25 _5431 _5437 _5438 f a).
Proof. exact (MK_COMB (@lem53575 _5431 _5437 _5438 f) (@lem53576 _5438 a)). Qed.
Lemma lem53578 {_5431 _5437 : Type'} : (@eq (_5437 -> _5431)) = (@eq (_5437 -> _5431)).
Proof. exact (eq_refl (@eq (_5437 -> _5431))). Qed.
Lemma lem53579 {_5431 _5437 _5438 : Type'} (f : type1228 _5431 _5437 _5438) (a : _5438) : (term29 _5431 _5437 _5438 f a) = (term30 _5431 _5437 _5438 f a).
Proof. exact (MK_COMB (@lem53578 _5431 _5437) (@lem53577 _5431 _5437 _5438 f a)). Qed.
Lemma lem53580 {_5431 _5437 _5438 : Type'} (f : type1228 _5431 _5437 _5438) (a : _5438) : (term25 _5431 _5437 _5438 f a) = (term27 _5431 _5437 _5438 f a).
Proof. exact (eq_refl (term25 _5431 _5437 _5438 f a)). Qed.
Lemma lem53581 {_5431 _5437 _5438 : Type'} (f : type1228 _5431 _5437 _5438) (a : _5438) : ((term24 _5431 _5437 _5438 f a) = (term25 _5431 _5437 _5438 f a)) = ((term25 _5431 _5437 _5438 f a) = (term27 _5431 _5437 _5438 f a)).
Proof. exact (MK_COMB (@lem53579 _5431 _5437 _5438 f a) (@lem53580 _5431 _5437 _5438 f a)). Qed.
Lemma lem53582 {_5431 _5437 _5438 : Type'} (f : type1228 _5431 _5437 _5438) (a : _5438) : (term25 _5431 _5437 _5438 f a) = (term27 _5431 _5437 _5438 f a).
Proof. exact (EQ_MP (@lem53581 _5431 _5437 _5438 f a) (@lem53573 _5431 _5437 _5438 f a)). Qed.
Lemma lem53583 {_5437 : Type'} (b : _5437) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem53584 {_5431 _5437 _5438 : Type'} (f : type1228 _5431 _5437 _5438) (a : _5438) (b : _5437) : (term31 _5431 _5437 _5438 f a b) = (term32 _5431 _5437 _5438 f a b).
Proof. exact (MK_COMB (@lem53582 _5431 _5437 _5438 f a) (@lem53583 _5437 b)). Qed.
Lemma lem53586 {A B : Type'} (f : A -> B) (y : A) : (term22 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem53587 {_5431 _5437 : Type'} (f : _5437 -> _5431) (y : _5437) : (term33 _5431 _5437 f y) = (f y).
Proof. exact (@lem53586 _5437 _5431 f y). Qed.
Lemma lem53588 {_5431 _5437 _5438 : Type'} (f : type1228 _5431 _5437 _5438) (a : _5438) (b : _5437) : (term34 _5431 _5437 _5438 f a b) = (term32 _5431 _5437 _5438 f a b).
Proof. exact (@lem53587 _5431 _5437 (term27 _5431 _5437 _5438 f a) b). Qed.
Lemma lem53589 {_5431 _5437 _5438 : Type'} (f : type1228 _5431 _5437 _5438) (a : _5438) (b : _5437) : (term32 _5431 _5437 _5438 f a b) = (term35 _5431 _5437 _5438 f a b).
Proof. exact (eq_refl (term32 _5431 _5437 _5438 f a b)). Qed.
Lemma lem53590 {_5431 _5437 _5438 : Type'} (f : type1228 _5431 _5437 _5438) (a : _5438) : (term36 _5431 _5437 _5438 f a) = (term27 _5431 _5437 _5438 f a).
Proof. exact (fun_ext (fun b : _5437 => @lem53589 _5431 _5437 _5438 f a b)). Qed.
Lemma lem53591 {_5437 : Type'} (b : _5437) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem53592 {_5431 _5437 _5438 : Type'} (f : type1228 _5431 _5437 _5438) (a : _5438) (b : _5437) : (term34 _5431 _5437 _5438 f a b) = (term32 _5431 _5437 _5438 f a b).
Proof. exact (MK_COMB (@lem53590 _5431 _5437 _5438 f a) (@lem53591 _5437 b)). Qed.
Lemma lem53593 {_5431 : Type'} : (@eq _5431) = (@eq _5431).
Proof. exact (eq_refl (@eq _5431)). Qed.
Lemma lem53594 {_5431 _5437 _5438 : Type'} (f : type1228 _5431 _5437 _5438) (a : _5438) (b : _5437) : (term37 _5431 _5437 _5438 f a b) = (term38 _5431 _5437 _5438 f a b).
Proof. exact (MK_COMB (@lem53593 _5431) (@lem53592 _5431 _5437 _5438 f a b)). Qed.
Lemma lem53595 {_5431 _5437 _5438 : Type'} (f : type1228 _5431 _5437 _5438) (a : _5438) (b : _5437) : (term32 _5431 _5437 _5438 f a b) = (term35 _5431 _5437 _5438 f a b).
Proof. exact (eq_refl (term32 _5431 _5437 _5438 f a b)). Qed.
Lemma lem53596 {_5431 _5437 _5438 : Type'} (f : type1228 _5431 _5437 _5438) (a : _5438) (b : _5437) : ((term34 _5431 _5437 _5438 f a b) = (term32 _5431 _5437 _5438 f a b)) = ((term32 _5431 _5437 _5438 f a b) = (term35 _5431 _5437 _5438 f a b)).
Proof. exact (MK_COMB (@lem53594 _5431 _5437 _5438 f a b) (@lem53595 _5431 _5437 _5438 f a b)). Qed.
Lemma lem53597 {_5431 _5437 _5438 : Type'} (f : type1228 _5431 _5437 _5438) (a : _5438) (b : _5437) : (term32 _5431 _5437 _5438 f a b) = (term35 _5431 _5437 _5438 f a b).
Proof. exact (EQ_MP (@lem53596 _5431 _5437 _5438 f a b) (@lem53588 _5431 _5437 _5438 f a b)). Qed.
Lemma lem53598 {_5431 _5437 _5438 : Type'} (f : type1228 _5431 _5437 _5438) (a : _5438) (b : _5437) : (term31 _5431 _5437 _5438 f a b) = (term35 _5431 _5437 _5438 f a b).
Proof. exact (TRANS (@lem53584 _5431 _5437 _5438 f a b) (@lem53597 _5431 _5437 _5438 f a b)). Qed.
Lemma lem53599 {_5431 _5437 _5438 : Type'} (f' : type1228 _5431 _5437 _5438) (a : _5438) (b : _5437) : (term39 _5431 _5437 _5438 f' a b) = (term39 _5431 _5437 _5438 f' a b).
Proof. exact (eq_refl (term39 _5431 _5437 _5438 f' a b)). Qed.
Lemma lem53600 {_5431 _5437 _5438 : Type'} (f' : type1228 _5431 _5437 _5438) (f : type1228 _5431 _5437 _5438) (a : _5438) (b : _5437) : (term40 _5431 _5437 _5438 f' f a b) = (term41 _5431 _5437 _5438 f' f a b).
Proof. exact (MK_COMB (@lem53599 _5431 _5437 _5438 f' a b) (@lem53598 _5431 _5437 _5438 f a b)). Qed.
Lemma lem53601 {_5431 _5437 _5438 : Type'} (f' : type1228 _5431 _5437 _5438) (f : type1228 _5431 _5437 _5438) (a : _5438) : (term42 _5431 _5437 _5438 f' f a) = (term43 _5431 _5437 _5438 f' f a).
Proof. exact (fun_ext (fun b : _5437 => @lem53600 _5431 _5437 _5438 f' f a b)). Qed.
Lemma lem53602 {_5437 : Type'} : (@all _5437) = (@all _5437).
Proof. exact (eq_refl (@all _5437)). Qed.
Lemma lem53603 {_5431 _5437 _5438 : Type'} (f' : type1228 _5431 _5437 _5438) (f : type1228 _5431 _5437 _5438) (a : _5438) : (term44 _5431 _5437 _5438 f' f a) = (term45 _5431 _5437 _5438 f' f a).
Proof. exact (MK_COMB (@lem53602 _5437) (@lem53601 _5431 _5437 _5438 f' f a)). Qed.
Lemma lem53608 {_5431 _5437 _5438 : Type'} (f' : type1228 _5431 _5437 _5438) (f : type1228 _5431 _5437 _5438) : (term46 _5431 _5437 _5438 f' f) = (term47 _5431 _5437 _5438 f' f).
Proof. exact (fun_ext (fun a : _5438 => @lem53603 _5431 _5437 _5438 f' f a)). Qed.
Lemma lem53609 {_5438 : Type'} : (@all _5438) = (@all _5438).
Proof. exact (eq_refl (@all _5438)). Qed.
Lemma lem53610 {_5431 _5437 _5438 : Type'} (f' : type1228 _5431 _5437 _5438) (f : type1228 _5431 _5437 _5438) : (term48 _5431 _5437 _5438 f' f) = (term49 _5431 _5437 _5438 f' f).
Proof. exact (MK_COMB (@lem53609 _5438) (@lem53608 _5431 _5437 _5438 f' f)). Qed.
Lemma lem53615 {_5431 _5437 _5438 : Type'} (f : type1228 _5431 _5437 _5438) : (term50 _5431 _5437 _5438 f) = (term51 _5431 _5437 _5438 f).
Proof. exact (fun_ext (fun f' : type1228 _5431 _5437 _5438 => @lem53610 _5431 _5437 _5438 f' f)). Qed.
Lemma lem53616 {_5431 _5437 _5438 : Type'} : (@GABS ((prod _5438 _5437) -> _5431)) = (@GABS ((prod _5438 _5437) -> _5431)).
Proof. exact (eq_refl (@GABS ((prod _5438 _5437) -> _5431))). Qed.
Lemma lem53617 {_5431 _5437 _5438 : Type'} (f : type1228 _5431 _5437 _5438) : (term52 _5431 _5437 _5438 f) = (term2 _5431 _5437 _5438 f).
Proof. exact (MK_COMB (@lem53616 _5431 _5437 _5438) (@lem53615 _5431 _5437 _5438 f)). Qed.
Lemma lem53619 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) : (term2 _5264 _5271 _5272 f) = f.
Proof. exact (EQ_MP (@lem53498 _5264 _5271 _5272 f) (@lem53497 _5264 _5271 _5272 f)). Qed.
Lemma lem53620 {_5431 _5437 _5438 : Type'} (f : type1228 _5431 _5437 _5438) : (term2 _5431 _5437 _5438 f) = f.
Proof. exact (@lem53619 _5431 _5437 _5438 f). Qed.
Lemma lem53621 {_5431 _5437 _5438 : Type'} (f : type1228 _5431 _5437 _5438) : (term52 _5431 _5437 _5438 f) = f.
Proof. exact (TRANS (@lem53617 _5431 _5437 _5438 f) (@lem53620 _5431 _5437 _5438 f)). Qed.
Lemma lem53622 {_5431 _5437 _5438 : Type'} (P : type333 _5431 _5437 _5438) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem53623 {_5431 _5437 _5438 : Type'} (P : type333 _5431 _5437 _5438) (f : type1228 _5431 _5437 _5438) : (term18 _5431 _5437 _5438 P f) = (P f).
Proof. exact (MK_COMB (@lem53622 _5431 _5437 _5438 P) (@lem53621 _5431 _5437 _5438 f)). Qed.
Lemma lem53624 {_5431 _5437 _5438 : Type'} (P : type333 _5431 _5437 _5438) : (term20 _5431 _5437 _5438 P) = (term53 _5431 _5437 _5438 P).
Proof. exact (fun_ext (fun f : type1228 _5431 _5437 _5438 => @lem53623 _5431 _5437 _5438 P f)). Qed.
Lemma lem53625 {_5431 _5437 _5438 : Type'} : (@ex ((prod _5438 _5437) -> _5431)) = (@ex ((prod _5438 _5437) -> _5431)).
Proof. exact (eq_refl (@ex ((prod _5438 _5437) -> _5431))). Qed.
Lemma lem53626 {_5431 _5437 _5438 : Type'} (P : type333 _5431 _5437 _5438) : (term21 _5431 _5437 _5438 P) = (term54 _5431 _5437 _5438 P).
Proof. exact (MK_COMB (@lem53625 _5431 _5437 _5438) (@lem53624 _5431 _5437 _5438 P)). Qed.
Lemma lem53633 {_5431 _5437 _5438 : Type'} (P : type333 _5431 _5437 _5438) : (term14 _5431 _5437 _5438 P) = (term54 _5431 _5437 _5438 P).
Proof. exact (TRANS (@lem53534 _5431 _5437 _5438 P) (@lem53626 _5431 _5437 _5438 P)). Qed.
Lemma lem53634 {_5431 _5437 _5438 : Type'} (P : type333 _5431 _5437 _5438) : (term55 _5431 _5437 _5438 P) = (term55 _5431 _5437 _5438 P).
Proof. exact (eq_refl (term55 _5431 _5437 _5438 P)). Qed.
Lemma lem53635 {_5431 _5437 _5438 : Type'} (P : type333 _5431 _5437 _5438) : ((term54 _5431 _5437 _5438 P) = (term14 _5431 _5437 _5438 P)) = ((term54 _5431 _5437 _5438 P) = (term54 _5431 _5437 _5438 P)).
Proof. exact (MK_COMB (@lem53634 _5431 _5437 _5438 P) (@lem53633 _5431 _5437 _5438 P)). Qed.
Lemma lem53637 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem53638 (x : Prop) : (x = x) = True.
Proof. exact (@lem53637 Prop x). Qed.
Lemma lem53639 {_5431 _5437 _5438 : Type'} (P : type333 _5431 _5437 _5438) : ((term54 _5431 _5437 _5438 P) = (term54 _5431 _5437 _5438 P)) = True.
Proof. exact (@lem53638 (term54 _5431 _5437 _5438 P)). Qed.
Lemma lem53640 {_5431 _5437 _5438 : Type'} (P : type333 _5431 _5437 _5438) : ((term54 _5431 _5437 _5438 P) = (term14 _5431 _5437 _5438 P)) = True.
Proof. exact (TRANS (@lem53635 _5431 _5437 _5438 P) (@lem53639 _5431 _5437 _5438 P)). Qed.
Lemma lem53641 {_5431 _5437 _5438 : Type'} : (term56 _5431 _5437 _5438) = (term57 _5431 _5437 _5438).
Proof. exact (fun_ext (fun P : type333 _5431 _5437 _5438 => @lem53640 _5431 _5437 _5438 P)). Qed.
Lemma lem53642 {_5431 _5437 _5438 : Type'} : (@all (((prod _5438 _5437) -> _5431) -> Prop)) = (@all (((prod _5438 _5437) -> _5431) -> Prop)).
Proof. exact (eq_refl (@all (((prod _5438 _5437) -> _5431) -> Prop))). Qed.
Lemma lem53643 {_5431 _5437 _5438 : Type'} : (term58 _5431 _5437 _5438) = (term59 _5431 _5437 _5438).
Proof. exact (MK_COMB (@lem53642 _5431 _5437 _5438) (@lem53641 _5431 _5437 _5438)). Qed.
Lemma lem53645 {A : Type'} (t : Prop) : (term60 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem53646 {_5431 _5437 _5438 : Type'} (t : Prop) : (term61 _5431 _5437 _5438 t) = t.
Proof. exact (@lem53645 (type333 _5431 _5437 _5438) t). Qed.
Lemma lem53647 {_5431 _5437 _5438 : Type'} : (term59 _5431 _5437 _5438) = True.
Proof. exact (@lem53646 _5431 _5437 _5438 True). Qed.
Lemma lem53648 {_5431 _5437 _5438 : Type'} : (term58 _5431 _5437 _5438) = True.
Proof. exact (TRANS (@lem53643 _5431 _5437 _5438) (@lem53647 _5431 _5437 _5438)). Qed.
Lemma lem53649 {_5431 _5437 _5438 : Type'} : True = (term58 _5431 _5437 _5438).
Proof. exact (SYM (@lem53648 _5431 _5437 _5438)). Qed.
Lemma lem53650 {_5431 _5437 _5438 : Type'} : term58 _5431 _5437 _5438.
Proof. exact (EQ_MP (@lem53649 _5431 _5437 _5438) (@lem0)). Qed.
