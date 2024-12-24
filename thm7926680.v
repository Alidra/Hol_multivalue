Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7926680_term_abbrevs.
Require Import CONSTR_REC_spec.
Require Import thm1066568_spec.
Require Import thm1066569_spec.
Require Import thm7925100_spec.
Require Import thm7925131_spec.
Require Import thm7925135_spec.
Require Import thm7926442_spec.
Require Import thm9102_spec.
Lemma lem7926529 {A Z : Type'} (fn : type1344 A Z) (fn' : type1330 A Z) (h1 : fn = (term0 A Z fn')) : fn = (term0 A Z fn').
Proof. exact (h1). Qed.
Lemma lem7926530 {A Z : Type'} (a : finite_sum A A) (_103783' : type45 A) (fn : type1344 A Z) (fn' : type1330 A Z) (h1 : _103783' = (term1 A)) (h2 : fn = (term0 A Z fn')) : (term2 A Z fn a) = (term3 A Z fn' _103783' a).
Proof. exact (MK_COMB (@lem7926529 A Z fn fn' h2) (@lem7926442 A a _103783' h1)). Qed.
Lemma lem7926531 {A Z : Type'} (fn : type1330 A Z) (_103783' : type45 A) (a : finite_sum A A) : (term3 A Z fn _103783' a) = (term4 A Z fn _103783' a).
Proof. exact (eq_refl (term3 A Z fn _103783' a)). Qed.
Lemma lem7926532 {A Z : Type'} (a : finite_sum A A) (_103783' : type45 A) (fn : type1344 A Z) (fn' : type1330 A Z) (h1 : _103783' = (term1 A)) (h2 : fn = (term0 A Z fn')) : (term2 A Z fn a) = (term4 A Z fn' _103783' a).
Proof. exact (TRANS (@lem7926530 A Z a _103783' fn fn' h1 h2) (@lem7926531 A Z fn' _103783' a)). Qed.
Lemma lem7926540 {A : Type'} (a : finite_sum A A) (tybit0' : type1331 A) (_103783' : type45 A) (h1 : tybit0' = (term5 A _103783')) : term6 A tybit0' _103783' a.
Proof. exact (@lem7925100 A tybit0' _103783' h1 a). Qed.
Lemma lem7926541 {A : Type'} (tybit0' : type1331 A) (_103783' : type45 A) (a : finite_sum A A) : (term6 A tybit0' _103783' a) = (term7 A tybit0' _103783' a).
Proof. exact (eq_refl (term6 A tybit0' _103783' a)). Qed.
Lemma lem7926544 {A : Type'} (a : finite_sum A A) (tybit0' : type1331 A) (_103783' : type45 A) (h1 : tybit0' = (term5 A _103783')) : term7 A tybit0' _103783' a.
Proof. exact (EQ_MP (@lem7926541 A tybit0' _103783' a) (@lem7926540 A a tybit0' _103783' h1)). Qed.
Lemma lem7926545 {A : Type'} (a : finite_sum A A) (tybit0' : type1331 A) (_103783' : type45 A) (h1 : tybit0' = (term5 A _103783')) : term7 A tybit0' _103783' a.
Proof. exact (@lem7926544 A a tybit0' _103783' h1). Qed.
Lemma lem7926547 {A : Type'} (r : type1676 A) (tybit0' : type1331 A) (_103783' : type45 A) (h1 : _103783' = (term1 A)) (h2 : tybit0' = (term5 A _103783')) : (tybit0' r) = ((term8 A r) = r).
Proof. exact (TRANS (@lem7925135 A r tybit0' _103783' h1 h2) (@lem7925131 A r)). Qed.
Lemma lem7926548 {A : Type'} (r : type1676 A) (tybit0' : type1331 A) (_103783' : type45 A) (h1 : _103783' = (term1 A)) (h2 : tybit0' = (term5 A _103783')) : (tybit0' r) = ((term8 A r) = r).
Proof. exact (@lem7926547 A r tybit0' _103783' h1 h2). Qed.
Lemma lem7926549 {A : Type'} (a : finite_sum A A) (tybit0' : type1331 A) (_103783' : type45 A) (h1 : _103783' = (term1 A)) (h2 : tybit0' = (term5 A _103783')) : (term7 A tybit0' _103783' a) = ((term9 A _103783' a) = (_103783' a)).
Proof. exact (@lem7926548 A (_103783' a) tybit0' _103783' h1 h2). Qed.
Lemma lem7926550 {A : Type'} (a : finite_sum A A) (tybit0' : type1331 A) (_103783' : type45 A) (h1 : _103783' = (term1 A)) (h2 : tybit0' = (term5 A _103783')) : (term9 A _103783' a) = (_103783' a).
Proof. exact (EQ_MP (@lem7926549 A a tybit0' _103783' h1 h2) (@lem7926545 A a tybit0' _103783' h2)). Qed.
Lemma lem7926551 {A Z : Type'} (fn : type1330 A Z) : fn = fn.
Proof. exact (eq_refl fn). Qed.
Lemma lem7926552 {A Z : Type'} (fn : type1330 A Z) (a : finite_sum A A) (tybit0' : type1331 A) (_103783' : type45 A) (h1 : _103783' = (term1 A)) (h2 : tybit0' = (term5 A _103783')) : (term4 A Z fn _103783' a) = (term10 A Z fn _103783' a).
Proof. exact (MK_COMB (@lem7926551 A Z fn) (@lem7926550 A a tybit0' _103783' h1 h2)). Qed.
Lemma lem7926553 {A Z : Type'} (a : finite_sum A A) (tybit0' : type1331 A) (_103783' : type45 A) (fn : type1344 A Z) (fn' : type1330 A Z) (h1 : _103783' = (term1 A)) (h2 : tybit0' = (term5 A _103783')) (h3 : fn = (term0 A Z fn')) : (term2 A Z fn a) = (term10 A Z fn' _103783' a).
Proof. exact (TRANS (@lem7926532 A Z a _103783' fn fn' h1 h3) (@lem7926552 A Z fn' a tybit0' _103783' h1 h2)). Qed.
Lemma lem7926554 {A : Type'} (_103783' : type45 A) (h1 : _103783' = (term1 A)) : _103783' = (term1 A).
Proof. exact (h1). Qed.
Lemma lem7926555 {A : Type'} (a : finite_sum A A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem7926556 {A : Type'} (a : finite_sum A A) (_103783' : type45 A) (h1 : _103783' = (term1 A)) : (_103783' a) = (term11 A a).
Proof. exact (MK_COMB (@lem7926554 A _103783' h1) (@lem7926555 A a)). Qed.
Lemma lem7926557 {A : Type'} (a : finite_sum A A) : (term11 A a) = (term12 A a).
Proof. exact (eq_refl (term11 A a)). Qed.
Lemma lem7926558 {A : Type'} (_103783' : type45 A) (a : finite_sum A A) : (term13 A _103783' a) = (term13 A _103783' a).
Proof. exact (eq_refl (term13 A _103783' a)). Qed.
Lemma lem7926559 {A : Type'} (_103783' : type45 A) (a : finite_sum A A) : ((_103783' a) = (term11 A a)) = ((_103783' a) = (term12 A a)).
Proof. exact (MK_COMB (@lem7926558 A _103783' a) (@lem7926557 A a)). Qed.
Lemma lem7926560 {A : Type'} (a : finite_sum A A) (_103783' : type45 A) (h1 : _103783' = (term1 A)) : (_103783' a) = (term12 A a).
Proof. exact (EQ_MP (@lem7926559 A _103783' a) (@lem7926556 A a _103783' h1)). Qed.
Lemma lem7926561 {A Z : Type'} (fn : type1330 A Z) : fn = fn.
Proof. exact (eq_refl fn). Qed.
Lemma lem7926562 {A Z : Type'} (fn : type1330 A Z) (a : finite_sum A A) (_103783' : type45 A) (h1 : _103783' = (term1 A)) : (term10 A Z fn _103783' a) = (term14 A Z fn a).
Proof. exact (MK_COMB (@lem7926561 A Z fn) (@lem7926560 A a _103783' h1)). Qed.
Lemma lem7926563 {A Z : Type'} (a : finite_sum A A) (tybit0' : type1331 A) (_103783' : type45 A) (fn : type1344 A Z) (fn' : type1330 A Z) (h1 : _103783' = (term1 A)) (h2 : tybit0' = (term5 A _103783')) (h3 : fn = (term0 A Z fn')) : (term2 A Z fn a) = (term14 A Z fn' a).
Proof. exact (TRANS (@lem7926553 A Z a tybit0' _103783' fn fn' h1 h2 h3) (@lem7926562 A Z fn' a _103783' h1)). Qed.
Lemma lem7926564 {A Z : Type'} (tybit0' : type1331 A) (a : finite_sum A A) (_103783' : type45 A) (fn : type1344 A Z) (fn' : type1330 A Z) (h1 : _103783' = (term1 A)) (h2 : fn = (term0 A Z fn')) : term15 A Z tybit0' _103783' fn fn' a.
Proof. exact (fun h0 : tybit0' = (term5 A _103783') => @lem7926563 A Z a tybit0' _103783' fn fn' h1 h0 h2). Qed.
Lemma lem7926565 {A : Type'} : (term1 A) = (term1 A).
Proof. exact (eq_refl (term1 A)). Qed.
Lemma lem7926566 {A Z : Type'} (tybit0' : type1331 A) (_103783' : type45 A) (a : finite_sum A A) (fn : type1344 A Z) (fn' : type1330 A Z) (h1 : fn = (term0 A Z fn')) : term16 A Z tybit0' _103783' fn fn' a.
Proof. exact (fun h0 : _103783' = (term1 A) => @lem7926564 A Z tybit0' a _103783' fn fn' h0 h1). Qed.
Lemma lem7926567 {A Z : Type'} (tybit0' : type1331 A) (a : finite_sum A A) (fn : type1344 A Z) (fn' : type1330 A Z) (h1 : fn = (term0 A Z fn')) : term17 A Z tybit0' fn fn' a.
Proof. exact (@lem7926566 A Z tybit0' (term1 A) a fn fn' h1). Qed.
Lemma lem7926568 {A Z : Type'} (tybit0' : type1331 A) (a : finite_sum A A) (fn : type1344 A Z) (fn' : type1330 A Z) (h1 : fn = (term0 A Z fn')) : term18 A Z tybit0' fn fn' a.
Proof. exact (@lem7926567 A Z tybit0' a fn fn' h1 (@lem7926565 A)). Qed.
Lemma lem7926569 {A : Type'} (tybit0' : type1331 A) (h1 : tybit0' = (term19 A)) : tybit0' = (term19 A).
Proof. exact (h1). Qed.
Lemma lem7926570 {A Z : Type'} (a : finite_sum A A) (tybit0' : type1331 A) (fn : type1344 A Z) (fn' : type1330 A Z) (h1 : tybit0' = (term19 A)) (h2 : fn = (term0 A Z fn')) : (term2 A Z fn a) = (term14 A Z fn' a).
Proof. exact (@lem7926568 A Z tybit0' a fn fn' h2 (@lem7926569 A tybit0' h1)). Qed.
Lemma lem7926571 {A : Type'} : (term19 A) = (term19 A).
Proof. exact (eq_refl (term19 A)). Qed.
Lemma lem7926572 {A Z : Type'} (tybit0' : type1331 A) (a : finite_sum A A) (fn : type1344 A Z) (fn' : type1330 A Z) (h1 : fn = (term0 A Z fn')) : term18 A Z tybit0' fn fn' a.
Proof. exact (fun h0 : tybit0' = (term19 A) => @lem7926570 A Z a tybit0' fn fn' h0 h1). Qed.
Lemma lem7926573 {A Z : Type'} (a : finite_sum A A) (fn : type1344 A Z) (fn' : type1330 A Z) (h1 : fn = (term0 A Z fn')) : term20 A Z fn fn' a.
Proof. exact (@lem7926572 A Z (term19 A) a fn fn' h1). Qed.
Lemma lem7926574 {A Z : Type'} (a : finite_sum A A) (fn : type1344 A Z) (fn' : type1330 A Z) (h1 : fn = (term0 A Z fn')) : (term2 A Z fn a) = (term14 A Z fn' a).
Proof. exact (@lem7926573 A Z a fn fn' h1 (@lem7926571 A)). Qed.
Lemma lem7926576 {A Z : Type'} : term21 A Z.
Proof. exact (@lem1065430 (finite_sum A A) Z). Qed.
Lemma lem7926577 {A Z : Type'} (_103783' : type47 A Z) : term22 A Z _103783'.
Proof. exact (@lem7926576 A Z (term23 A Z _103783')). Qed.
Lemma lem7926578 {A Z : Type'} (_103783' : type47 A Z) : (term22 A Z _103783') = (term24 A Z _103783').
Proof. exact (eq_refl (term22 A Z _103783')). Qed.
Lemma lem7926579 {A Z : Type'} (_103783' : type47 A Z) : term24 A Z _103783'.
Proof. exact (EQ_MP (@lem7926578 A Z _103783') (@lem7926577 A Z _103783')). Qed.
Lemma lem7926580 {A Z : Type'} (_103783' : type47 A Z) (fn : type1330 A Z) (h1 : term25 A Z _103783' fn) : term25 A Z _103783' fn.
Proof. exact (h1). Qed.
Lemma lem7926581 {A Z : Type'} (c : nat) (_103783' : type47 A Z) (fn : type1330 A Z) (h1 : term25 A Z _103783' fn) : term26 A Z _103783' fn c.
Proof. exact (@lem7926580 A Z _103783' fn h1 c). Qed.
Lemma lem7926582 {A Z : Type'} (_103783' : type47 A Z) (c : nat) (fn : type1330 A Z) : (term26 A Z _103783' fn c) = (term27 A Z _103783' c fn).
Proof. exact (eq_refl (term26 A Z _103783' fn c)). Qed.
Lemma lem7926583 {A Z : Type'} (c : nat) (_103783' : type47 A Z) (fn : type1330 A Z) (h1 : term25 A Z _103783' fn) : term27 A Z _103783' c fn.
Proof. exact (EQ_MP (@lem7926582 A Z _103783' c fn) (@lem7926581 A Z c _103783' fn h1)). Qed.
Lemma lem7926584 {A Z : Type'} (c : nat) (i : finite_sum A A) (_103783' : type47 A Z) (fn : type1330 A Z) (h1 : term25 A Z _103783' fn) : term28 A Z _103783' c fn i.
Proof. exact (@lem7926583 A Z c _103783' fn h1 i). Qed.
Lemma lem7926585 {A Z : Type'} (_103783' : type47 A Z) (c : nat) (i : finite_sum A A) (fn : type1330 A Z) : (term28 A Z _103783' c fn i) = (term29 A Z _103783' c i fn).
Proof. exact (eq_refl (term28 A Z _103783' c fn i)). Qed.
Lemma lem7926586 {A Z : Type'} (c : nat) (i : finite_sum A A) (_103783' : type47 A Z) (fn : type1330 A Z) (h1 : term25 A Z _103783' fn) : term29 A Z _103783' c i fn.
Proof. exact (EQ_MP (@lem7926585 A Z _103783' c i fn) (@lem7926584 A Z c i _103783' fn h1)). Qed.
Lemma lem7926587 {A Z : Type'} (c : nat) (i : finite_sum A A) (r : type1611 A) (_103783' : type47 A Z) (fn : type1330 A Z) (h1 : term25 A Z _103783' fn) : term30 A Z _103783' c i fn r.
Proof. exact (@lem7926586 A Z c i _103783' fn h1 r). Qed.
Lemma lem7926588 {A Z : Type'} (_103783' : type47 A Z) (c : nat) (i : finite_sum A A) (fn : type1330 A Z) (r : type1611 A) : (term30 A Z _103783' c i fn r) = ((term31 A Z fn c i r) = (term32 A Z _103783' c i fn r)).
Proof. exact (eq_refl (term30 A Z _103783' c i fn r)). Qed.
Lemma lem7926634 {A Z : Type'} (c : nat) (i : finite_sum A A) (r : type1611 A) (_103783' : type47 A Z) (fn : type1330 A Z) (h1 : term25 A Z _103783' fn) : (term31 A Z fn c i r) = (term32 A Z _103783' c i fn r).
Proof. exact (EQ_MP (@lem7926588 A Z _103783' c i fn r) (@lem7926587 A Z c i r _103783' fn h1)). Qed.
Lemma lem7926635 {A Z : Type'} (c : nat) (i : finite_sum A A) (r : type1611 A) (_103783' : type47 A Z) (fn : type1330 A Z) (h1 : term25 A Z _103783' fn) : (term31 A Z fn c i r) = (term32 A Z _103783' c i fn r).
Proof. exact (@lem7926634 A Z c i r _103783' fn h1). Qed.
Lemma lem7926636 {A Z : Type'} (a : finite_sum A A) (_103783' : type47 A Z) (fn : type1330 A Z) (h1 : term25 A Z _103783' fn) : (term14 A Z fn a) = (term33 A Z _103783' a fn).
Proof. exact (@lem7926635 A Z (NUMERAL 0) a (term34 A) _103783' fn h1). Qed.
Lemma lem7926637 {A Z : Type'} (a : finite_sum A A) (_103783' : type47 A Z) (fn : type1344 A Z) (fn' : type1330 A Z) (h1 : term25 A Z _103783' fn') (h2 : fn = (term0 A Z fn')) : (term2 A Z fn a) = (term33 A Z _103783' a fn').
Proof. exact (TRANS (@lem7926574 A Z a fn fn' h2) (@lem7926636 A Z a _103783' fn' h1)). Qed.
Lemma lem7926639 {A : Type'} (f : nat -> A) (a : A) : (term35 A a f) = a.
Proof. exact (EQ_MP (@lem1066569 A f a) (@lem1066568 A a f)). Qed.
Lemma lem7926640 {A Z : Type'} (f : type1562 A Z) (a : type44 A Z) : (term36 A Z a f) = a.
Proof. exact (@lem7926639 (type44 A Z) f a). Qed.
Lemma lem7926643 {A Z : Type'} (_103783' : type47 A Z) : (term37 A Z _103783') = (term38 A Z _103783').
Proof. exact (@lem7926640 A Z (@FNIL ((finite_sum A A) -> (nat -> recspace (finite_sum A A)) -> (nat -> Z) -> Z)) (term38 A Z _103783')). Qed.
Lemma lem7926644 {A : Type'} (a : finite_sum A A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem7926645 {A Z : Type'} (_103783' : type47 A Z) (a : finite_sum A A) : (term39 A Z _103783' a) = (term40 A Z _103783' a).
Proof. exact (MK_COMB (@lem7926643 A Z _103783') (@lem7926644 A a)). Qed.
Lemma lem7926646 {A : Type'} : (term34 A) = (term34 A).
Proof. exact (eq_refl (term34 A)). Qed.
Lemma lem7926647 {A Z : Type'} (_103783' : type47 A Z) (a : finite_sum A A) : (term41 A Z _103783' a) = (term42 A Z _103783' a).
Proof. exact (MK_COMB (@lem7926645 A Z _103783' a) (@lem7926646 A)). Qed.
Lemma lem7926648 {A Z : Type'} (fn : type1330 A Z) : (term43 A Z fn) = (term43 A Z fn).
Proof. exact (eq_refl (term43 A Z fn)). Qed.
Lemma lem7926649 {A Z : Type'} (_103783' : type47 A Z) (a : finite_sum A A) (fn : type1330 A Z) : (term33 A Z _103783' a fn) = (term44 A Z _103783' a fn).
Proof. exact (MK_COMB (@lem7926647 A Z _103783' a) (@lem7926648 A Z fn)). Qed.
Lemma lem7926650 {A Z : Type'} (a : finite_sum A A) (_103783' : type47 A Z) (fn : type1344 A Z) (fn' : type1330 A Z) (h1 : term25 A Z _103783' fn') (h2 : fn = (term0 A Z fn')) : (term2 A Z fn a) = (term44 A Z _103783' a fn').
Proof. exact (TRANS (@lem7926637 A Z a _103783' fn fn' h1 h2) (@lem7926649 A Z _103783' a fn')). Qed.
Lemma lem7926651 {A Z : Type'} (_103783' : type47 A Z) (a : finite_sum A A) : (term40 A Z _103783' a) = (term45 A Z _103783' a).
Proof. exact (eq_refl (term40 A Z _103783' a)). Qed.
Lemma lem7926652 {A : Type'} : (term34 A) = (term34 A).
Proof. exact (eq_refl (term34 A)). Qed.
Lemma lem7926653 {A Z : Type'} (_103783' : type47 A Z) (a : finite_sum A A) : (term42 A Z _103783' a) = (term46 A Z _103783' a).
Proof. exact (MK_COMB (@lem7926651 A Z _103783' a) (@lem7926652 A)). Qed.
Lemma lem7926654 {A Z : Type'} (fn : type1330 A Z) : (term43 A Z fn) = (term43 A Z fn).
Proof. exact (eq_refl (term43 A Z fn)). Qed.
Lemma lem7926655 {A Z : Type'} (_103783' : type47 A Z) (a : finite_sum A A) (fn : type1330 A Z) : (term44 A Z _103783' a fn) = (term47 A Z _103783' a fn).
Proof. exact (MK_COMB (@lem7926653 A Z _103783' a) (@lem7926654 A Z fn)). Qed.
Lemma lem7926656 {A Z : Type'} (a : finite_sum A A) (_103783' : type47 A Z) (fn : type1344 A Z) (fn' : type1330 A Z) (h1 : term25 A Z _103783' fn') (h2 : fn = (term0 A Z fn')) : (term2 A Z fn a) = (term47 A Z _103783' a fn').
Proof. exact (TRANS (@lem7926650 A Z a _103783' fn fn' h1 h2) (@lem7926655 A Z _103783' a fn')). Qed.
Lemma lem7926657 {A Z : Type'} (_103783' : type47 A Z) (a : finite_sum A A) : (term46 A Z _103783' a) = (term48 A Z _103783' a).
Proof. exact (eq_refl (term46 A Z _103783' a)). Qed.
Lemma lem7926658 {A Z : Type'} (fn : type1330 A Z) : (term43 A Z fn) = (term43 A Z fn).
Proof. exact (eq_refl (term43 A Z fn)). Qed.
Lemma lem7926659 {A Z : Type'} (_103783' : type47 A Z) (a : finite_sum A A) (fn : type1330 A Z) : (term47 A Z _103783' a fn) = (term49 A Z _103783' a fn).
Proof. exact (MK_COMB (@lem7926657 A Z _103783' a) (@lem7926658 A Z fn)). Qed.
Lemma lem7926660 {A Z : Type'} (a : finite_sum A A) (_103783' : type47 A Z) (fn : type1344 A Z) (fn' : type1330 A Z) (h1 : term25 A Z _103783' fn') (h2 : fn = (term0 A Z fn')) : (term2 A Z fn a) = (term49 A Z _103783' a fn').
Proof. exact (TRANS (@lem7926656 A Z a _103783' fn fn' h1 h2) (@lem7926659 A Z _103783' a fn')). Qed.
Lemma lem7926661 {A Z : Type'} (fn : type1330 A Z) (_103783' : type47 A Z) (a : finite_sum A A) : (term49 A Z _103783' a fn) = (_103783' a).
Proof. exact (eq_refl (term49 A Z _103783' a fn)). Qed.
Lemma lem7926664 {A Z : Type'} (a : finite_sum A A) (_103783' : type47 A Z) (fn : type1344 A Z) (fn' : type1330 A Z) (h1 : term25 A Z _103783' fn') (h2 : fn = (term0 A Z fn')) : (term2 A Z fn a) = (_103783' a).
Proof. exact (TRANS (@lem7926660 A Z a _103783' fn fn' h1 h2) (@lem7926661 A Z fn' _103783' a)). Qed.
Lemma lem7926665 {A Z : Type'} (_103783' : type47 A Z) (fn : type1344 A Z) (fn' : type1330 A Z) (h1 : term25 A Z _103783' fn') (h2 : fn = (term0 A Z fn')) : term50 A Z fn _103783'.
Proof. exact (fun a : finite_sum A A => @lem7926664 A Z a _103783' fn fn' h1 h2). Qed.
Lemma lem7926666 {A Z : Type'} (fn : type1344 A Z) (_103783' : type47 A Z) : (term51 A Z _103783' fn) = (term50 A Z fn _103783').
Proof. exact (eq_refl (term51 A Z _103783' fn)). Qed.
Lemma lem7926667 {A Z : Type'} : term52 A Z.
Proof. exact (@lem9102 (type1344 A Z)). Qed.
Lemma lem7926668 {A Z : Type'} (_103783' : type47 A Z) : term53 A Z _103783'.
Proof. exact (@lem7926667 A Z (term54 A Z _103783')). Qed.
Lemma lem7926669 {A Z : Type'} (_103783' : type47 A Z) : (term53 A Z _103783') = (term55 A Z _103783').
Proof. exact (eq_refl (term53 A Z _103783')). Qed.
Lemma lem7926670 {A Z : Type'} (_103783' : type47 A Z) : term55 A Z _103783'.
Proof. exact (EQ_MP (@lem7926669 A Z _103783') (@lem7926668 A Z _103783')). Qed.
Lemma lem7926671 {A Z : Type'} (_103783' : type47 A Z) (fn : type1330 A Z) : term56 A Z _103783' fn.
Proof. exact (@lem7926670 A Z _103783' (term0 A Z fn)). Qed.
Lemma lem7926672 {A Z : Type'} (fn : type1330 A Z) (_103783' : type47 A Z) : (term56 A Z _103783' fn) = (term57 A Z fn _103783').
Proof. exact (eq_refl (term56 A Z _103783' fn)). Qed.
Lemma lem7926673 {A Z : Type'} (fn : type1330 A Z) (_103783' : type47 A Z) : term57 A Z fn _103783'.
Proof. exact (EQ_MP (@lem7926672 A Z fn _103783') (@lem7926671 A Z _103783' fn)). Qed.
Lemma lem7926674 {A Z : Type'} (_103783' : type47 A Z) (fn : type1344 A Z) : (term50 A Z fn _103783') = (term51 A Z _103783' fn).
Proof. exact (SYM (@lem7926666 A Z fn _103783')). Qed.
Lemma lem7926675 {A Z : Type'} (_103783' : type47 A Z) (fn : type1344 A Z) (fn' : type1330 A Z) (h1 : term25 A Z _103783' fn') (h2 : fn = (term0 A Z fn')) : term51 A Z _103783' fn.
Proof. exact (EQ_MP (@lem7926674 A Z _103783' fn) (@lem7926665 A Z _103783' fn fn' h1 h2)). Qed.
Lemma lem7926676 {A Z : Type'} (fn : type1344 A Z) (_103783' : type47 A Z) (fn' : type1330 A Z) (h1 : term25 A Z _103783' fn') : term58 A Z fn' _103783' fn.
Proof. exact (fun h0 : fn = (term0 A Z fn') => @lem7926675 A Z _103783' fn fn' h1 h0). Qed.
Lemma lem7926677 {A Z : Type'} (_103783' : type47 A Z) (fn : type1330 A Z) (h1 : term25 A Z _103783' fn) : term59 A Z fn _103783'.
Proof. exact (fun fn' : type1344 A Z => @lem7926676 A Z fn' _103783' fn h1). Qed.
Lemma lem7926678 {A Z : Type'} (_103783' : type47 A Z) (fn : type1330 A Z) (h1 : term25 A Z _103783' fn) : term60 A Z _103783'.
Proof. exact (@lem7926673 A Z fn _103783' (@lem7926677 A Z _103783' fn h1)). Qed.
Lemma lem7926679 {A Z : Type'} (_103783' : type47 A Z) : term60 A Z _103783'.
Proof. exact (ex_elim (@lem7926579 A Z _103783') (fun fn : type1330 A Z => fun h0 : term61 A Z _103783' fn => @lem7926678 A Z _103783' fn h0)). Qed.
Lemma lem7926680 {A Z : Type'} : term62 A Z.
Proof. exact (fun _103783' : type47 A Z => @lem7926679 A Z _103783'). Qed.
