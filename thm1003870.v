Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1003870_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import EXP_2_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17646_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm69_spec.
Lemma lem1003175 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1003176 (m : nat) (p : nat) : (((term1 m) = p) = ((Nat.mul m m) = p)) = (term2 m p).
Proof. exact (@lem1003175 (((term1 m) = p) = ((Nat.mul m m) = p))). Qed.
Lemma lem1003177 (m : nat) (p : nat) : (term2 m p) = (((term1 m) = p) = ((Nat.mul m m) = p)).
Proof. exact (SYM (@lem1003176 m p)). Qed.
Lemma lem1003178 (m : nat) (p : nat) (h1 : term3 m p) : term3 m p.
Proof. exact (h1). Qed.
Lemma lem1003181 (m : nat) (p : nat) (h1 : term4 m p) : term4 m p.
Proof. exact (h1). Qed.
Lemma lem1003182 (m : nat) (p : nat) : term5 m p.
Proof. exact (fun h0 : term4 m p => @lem1003181 m p h0). Qed.
Lemma lem1003183 (m : nat) (p : nat) (h1 : term5 m p) : term5 m p.
Proof. exact (h1). Qed.
Lemma lem1003184 (m : nat) (p : nat) (h1 : term4 m p) : term4 m p.
Proof. exact (h1). Qed.
Lemma lem1003185 (m : nat) (p : nat) (h1 : term4 m p) (h2 : term5 m p) : term4 m p.
Proof. exact (@lem1003183 m p h2 (@lem1003184 m p h1)). Qed.
Lemma lem1003186 (m : nat) (p : nat) (h1 : term4 m p) : term6 m p.
Proof. exact (fun h0 : term5 m p => @lem1003185 m p h1 h0). Qed.
Lemma lem1003187 (m : nat) (p : nat) (h1 : term5 m p) : term5 m p.
Proof. exact (h1). Qed.
Lemma lem1003188 (m : nat) (p : nat) (h1 : term4 m p) (h2 : term5 m p) : term4 m p.
Proof. exact (@lem1003186 m p h1 (@lem1003187 m p h2)). Qed.
Lemma lem1003189 (m : nat) (p : nat) (h1 : term5 m p) : term5 m p.
Proof. exact (fun h0 : term4 m p => @lem1003188 m p h0 h1). Qed.
Lemma lem1003190 (m : nat) (p : nat) : term7 m p.
Proof. exact (fun h0 : term5 m p => @lem1003189 m p h0). Qed.
Lemma lem1003193 (m : nat) (p : nat) : term5 m p.
Proof. exact (@lem1003190 m p (@lem1003182 m p)). Qed.
Lemma lem1003205 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1003206 : term8 = term9.
Proof. exact (@lem1003205 term10). Qed.
Lemma lem1003211 (m : nat) (p : nat) : (term11 m p) = (term11 m p).
Proof. exact (eq_refl (term11 m p)). Qed.
Lemma lem1003212 (m : nat) (p : nat) : (term4 m p) = (term12 m p).
Proof. exact (MK_COMB (@lem1003211 m p) (@lem1003206)). Qed.
Lemma lem1003215 (p : nat) : (term13 p) = (term14 p).
Proof. exact (fun_ext (fun m : nat => @lem1003212 m p)). Qed.
Lemma lem1003216 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1003217 (p : nat) : (term15 p) = (term16 p).
Proof. exact (MK_COMB (@lem1003216) (@lem1003215 p)). Qed.
Lemma lem1003222 : term17 = term18.
Proof. exact (fun_ext (fun p : nat => @lem1003217 p)). Qed.
Lemma lem1003223 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1003232 : term19 = term20.
Proof. exact (MK_COMB (@lem1003223) (@lem1003222)). Qed.
Lemma lem1003233 (n : nat) : ((term1 n) = (Nat.mul n n)) = ((term1 n) = (Nat.mul n n)).
Proof. exact (eq_refl ((term1 n) = (Nat.mul n n))). Qed.
Lemma lem1003234 : term21 = term21.
Proof. exact (fun_ext (fun n : nat => @lem1003233 n)). Qed.
Lemma lem1003235 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1003236 : term10 = term10.
Proof. exact (MK_COMB (@lem1003235) (@lem1003234)). Qed.
Lemma lem1003237 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1003238 : term9 = term9.
Proof. exact (MK_COMB (@lem1003237) (@lem1003236)). Qed.
Lemma lem1003247 (m : nat) (p : nat) : (term11 m p) = (term11 m p).
Proof. exact (eq_refl (term11 m p)). Qed.
Lemma lem1003248 (m : nat) (p : nat) : (term12 m p) = (term12 m p).
Proof. exact (MK_COMB (@lem1003247 m p) (@lem1003238)). Qed.
Lemma lem1003249 (p : nat) : (term14 p) = (term14 p).
Proof. exact (fun_ext (fun m : nat => @lem1003248 m p)). Qed.
Lemma lem1003250 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1003251 (p : nat) : (term16 p) = (term16 p).
Proof. exact (MK_COMB (@lem1003250) (@lem1003249 p)). Qed.
Lemma lem1003252 : term18 = term18.
Proof. exact (fun_ext (fun p : nat => @lem1003251 p)). Qed.
Lemma lem1003253 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1003254 : term20 = term20.
Proof. exact (MK_COMB (@lem1003253) (@lem1003252)). Qed.
Lemma lem1003277 : term19 = term20.
Proof. exact (TRANS (@lem1003232) (@lem1003254)). Qed.
Lemma lem1003278 : term20 = term19.
Proof. exact (SYM (@lem1003277)). Qed.
Lemma lem1003279 (m : nat) (p : nat) (h1 : term3 m p) : term3 m p.
Proof. exact (h1). Qed.
Lemma lem1003280 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1003299 (m : nat) (p : nat) : (term3 m p) = (term22 m p).
Proof. exact (@lem17646 ((term1 m) = p) ((Nat.mul m m) = p)). Qed.
Lemma lem1003301 (n : nat) : ((term1 n) = (Nat.mul n n)) = ((term1 n) = (Nat.mul n n)).
Proof. exact (eq_refl ((term1 n) = (Nat.mul n n))). Qed.
Lemma lem1003302 : term21 = term21.
Proof. exact (fun_ext (fun n : nat => @lem1003301 n)). Qed.
Lemma lem1003303 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1003312 : term10 = term10.
Proof. exact (MK_COMB (@lem1003303) (@lem1003302)). Qed.
Lemma lem1003313 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1003312) (@lem1003280 h1)). Qed.
Lemma lem1003375 (m : nat) (p : nat) (h1 : term3 m p) : term22 m p.
Proof. exact (EQ_MP (@lem1003299 m p) (@lem1003279 m p h1)). Qed.
Lemma lem1003394 (n : nat) : ((term1 n) = (Nat.mul n n)) = ((term1 n) = (Nat.mul n n)).
Proof. exact (eq_refl ((term1 n) = (Nat.mul n n))). Qed.
Lemma lem1003395 : term21 = term21.
Proof. exact (fun_ext (fun n : nat => @lem1003394 n)). Qed.
Lemma lem1003396 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1003397 : term10 = term10.
Proof. exact (MK_COMB (@lem1003396) (@lem1003395)). Qed.
Lemma lem1003398 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1003397) (@lem1003313 h1)). Qed.
Lemma lem1003399 (m : nat) (p : nat) (h1 : term23 m p) : term23 m p.
Proof. exact (h1). Qed.
Lemma lem1003400 (m : nat) (p : nat) (h1 : term24 m p) : term24 m p.
Proof. exact (h1). Qed.
Lemma lem1003406 (n : nat) : ((term1 n) = (Nat.mul n n)) = ((term1 n) = (Nat.mul n n)).
Proof. exact (eq_refl ((term1 n) = (Nat.mul n n))). Qed.
Lemma lem1003407 : term21 = term21.
Proof. exact (fun_ext (fun n : nat => @lem1003406 n)). Qed.
Lemma lem1003408 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1003410 : term10 = term10.
Proof. exact (MK_COMB (@lem1003408) (@lem1003407)). Qed.
Lemma lem1003411 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1003410) (@lem1003398 h1)). Qed.
Lemma lem1003421 (n : nat) : ((term1 n) = (Nat.mul n n)) = ((term1 n) = (Nat.mul n n)).
Proof. exact (eq_refl ((term1 n) = (Nat.mul n n))). Qed.
Lemma lem1003422 : term21 = term21.
Proof. exact (fun_ext (fun n : nat => @lem1003421 n)). Qed.
Lemma lem1003423 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1003425 : term10 = term10.
Proof. exact (MK_COMB (@lem1003423) (@lem1003422)). Qed.
Lemma lem1003426 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1003425) (@lem1003398 h1)). Qed.
Lemma lem1003435 (_16230 : nat) (h1 : term10) : term25 _16230.
Proof. exact (@lem1003411 h1 _16230). Qed.
Lemma lem1003436 (_16230 : nat) : (term25 _16230) = ((term1 _16230) = (Nat.mul _16230 _16230)).
Proof. exact (eq_refl (term25 _16230)). Qed.
Lemma lem1003438 (_16231 : nat) (h1 : term10) : term25 _16231.
Proof. exact (@lem1003426 h1 _16231). Qed.
Lemma lem1003439 (_16231 : nat) : (term25 _16231) = ((term1 _16231) = (Nat.mul _16231 _16231)).
Proof. exact (eq_refl (term25 _16231)). Qed.
Lemma lem1003444 (m : nat) (p : nat) (h1 : term23 m p) : (term1 m) = p.
Proof. exact (proj1 (@lem1003399 m p h1)). Qed.
Lemma lem1003446 (m : nat) (p : nat) (h1 : term23 m p) : term26 m p.
Proof. exact (proj2 (@lem1003399 m p h1)). Qed.
Lemma lem1003450 (m : nat) (p : nat) (h1 : term24 m p) : term27 m p.
Proof. exact (proj1 (@lem1003400 m p h1)). Qed.
Lemma lem1003452 (m : nat) (p : nat) (h1 : term24 m p) : (Nat.mul m m) = p.
Proof. exact (proj2 (@lem1003400 m p h1)). Qed.
Lemma lem1003453 (m : nat) (p : nat) (h1 : term23 m p) : p = (term1 m).
Proof. exact (SYM (@lem1003444 m p h1)). Qed.
Lemma lem1003482 (m : nat) : (term28 m) = (term28 m).
Proof. exact (eq_refl (term28 m)). Qed.
Lemma lem1003483 (m : nat) (p : nat) (h1 : term23 m p) : (term29 m p) = (term30 m).
Proof. exact (MK_COMB (@lem1003482 m) (@lem1003453 m p h1)). Qed.
Lemma lem1003484 (m : nat) : (term30 m) = (term31 m).
Proof. exact (eq_refl (term30 m)). Qed.
Lemma lem1003485 (m : nat) (p : nat) : (term32 m p) = (term32 m p).
Proof. exact (eq_refl (term32 m p)). Qed.
Lemma lem1003486 (p : nat) (m : nat) : ((term29 m p) = (term30 m)) = ((term29 m p) = (term31 m)).
Proof. exact (MK_COMB (@lem1003485 m p) (@lem1003484 m)). Qed.
Lemma lem1003487 (m : nat) (p : nat) : (term29 m p) = (term26 m p).
Proof. exact (eq_refl (term29 m p)). Qed.
Lemma lem1003488 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1003489 (m : nat) (p : nat) : (term32 m p) = (term33 m p).
Proof. exact (MK_COMB (@lem1003488) (@lem1003487 m p)). Qed.
Lemma lem1003490 (m : nat) : (term31 m) = (term31 m).
Proof. exact (eq_refl (term31 m)). Qed.
Lemma lem1003491 (p : nat) (m : nat) : ((term29 m p) = (term31 m)) = ((term26 m p) = (term31 m)).
Proof. exact (MK_COMB (@lem1003489 m p) (@lem1003490 m)). Qed.
Lemma lem1003492 (p : nat) (m : nat) : ((term29 m p) = (term30 m)) = ((term26 m p) = (term31 m)).
Proof. exact (TRANS (@lem1003486 p m) (@lem1003491 p m)). Qed.
Lemma lem1003493 (m : nat) (p : nat) (h1 : term23 m p) : (term26 m p) = (term31 m).
Proof. exact (EQ_MP (@lem1003492 p m) (@lem1003483 m p h1)). Qed.
Lemma lem1003494 (m : nat) (p : nat) (h1 : term23 m p) : term31 m.
Proof. exact (EQ_MP (@lem1003493 m p h1) (@lem1003446 m p h1)). Qed.
Lemma lem1003495 (m : nat) (p : nat) (h1 : term24 m p) : p = (Nat.mul m m).
Proof. exact (SYM (@lem1003452 m p h1)). Qed.
Lemma lem1003524 (m : nat) : (term34 m) = (term34 m).
Proof. exact (eq_refl (term34 m)). Qed.
Lemma lem1003525 (m : nat) (p : nat) (h1 : term24 m p) : (term35 m p) = (term36 m).
Proof. exact (MK_COMB (@lem1003524 m) (@lem1003495 m p h1)). Qed.
Lemma lem1003526 (m : nat) : (term36 m) = (term37 m).
Proof. exact (eq_refl (term36 m)). Qed.
Lemma lem1003527 (m : nat) (p : nat) : (term38 m p) = (term38 m p).
Proof. exact (eq_refl (term38 m p)). Qed.
Lemma lem1003528 (p : nat) (m : nat) : ((term35 m p) = (term36 m)) = ((term35 m p) = (term37 m)).
Proof. exact (MK_COMB (@lem1003527 m p) (@lem1003526 m)). Qed.
Lemma lem1003529 (m : nat) (p : nat) : (term35 m p) = (term27 m p).
Proof. exact (eq_refl (term35 m p)). Qed.
Lemma lem1003530 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1003531 (m : nat) (p : nat) : (term38 m p) = (term39 m p).
Proof. exact (MK_COMB (@lem1003530) (@lem1003529 m p)). Qed.
Lemma lem1003532 (m : nat) : (term37 m) = (term37 m).
Proof. exact (eq_refl (term37 m)). Qed.
Lemma lem1003533 (p : nat) (m : nat) : ((term35 m p) = (term37 m)) = ((term27 m p) = (term37 m)).
Proof. exact (MK_COMB (@lem1003531 m p) (@lem1003532 m)). Qed.
Lemma lem1003534 (p : nat) (m : nat) : ((term35 m p) = (term36 m)) = ((term27 m p) = (term37 m)).
Proof. exact (TRANS (@lem1003528 p m) (@lem1003533 p m)). Qed.
Lemma lem1003535 (m : nat) (p : nat) (h1 : term24 m p) : (term27 m p) = (term37 m).
Proof. exact (EQ_MP (@lem1003534 p m) (@lem1003525 m p h1)). Qed.
Lemma lem1003536 (m : nat) (p : nat) (h1 : term24 m p) : term37 m.
Proof. exact (EQ_MP (@lem1003535 m p h1) (@lem1003450 m p h1)). Qed.
Lemma lem1003592 (x : nat) (y : nat) (z : nat) : term40 x y z.
Proof. exact (@lem21385 nat x y z). Qed.
Lemma lem1003594 (_16230 : nat) (h1 : term10) : (term1 _16230) = (Nat.mul _16230 _16230).
Proof. exact (EQ_MP (@lem1003436 _16230) (@lem1003435 _16230 h1)). Qed.
Lemma lem1003595 (m : nat) (h1 : term10) : (term1 m) = (Nat.mul m m).
Proof. exact (@lem1003594 m h1). Qed.
Lemma lem1003596 (m : nat) (h1 : term10) : term41 m.
Proof. exact (fun h0 : term37 m => @lem1003595 m h1). Qed.
Lemma lem1003598 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1003599 (m : nat) : (term41 m) = ((term1 m) = (Nat.mul m m)).
Proof. exact (@lem1003598 ((term1 m) = (Nat.mul m m))). Qed.
Lemma lem1003600 (m : nat) (h1 : term10) : (term1 m) = (Nat.mul m m).
Proof. exact (EQ_MP (@lem1003599 m) (@lem1003596 m h1)). Qed.
Lemma lem1003602 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem1003603 (m : nat) : (term1 m) = (term1 m).
Proof. exact (@lem1003602 (term1 m)). Qed.
Lemma lem1003604 (m : nat) : term43 m.
Proof. exact (fun h0 : term44 m => @lem1003603 m). Qed.
Lemma lem1003606 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1003607 (m : nat) : (term43 m) = ((term1 m) = (term1 m)).
Proof. exact (@lem1003606 ((term1 m) = (term1 m))). Qed.
Lemma lem1003608 (m : nat) : (term1 m) = (term1 m).
Proof. exact (EQ_MP (@lem1003607 m) (@lem1003604 m)). Qed.
Lemma lem1003626 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1003627 (y : nat) (x : nat) (z : nat) : (term45 x y z) = (term46 y x z).
Proof. exact (@lem1003626 (y = z) (term47 x z)). Qed.
Lemma lem1003637 (x : nat) (y : nat) : (term48 x y) = (term48 x y).
Proof. exact (eq_refl (term48 x y)). Qed.
Lemma lem1003638 (y : nat) (x : nat) (z : nat) : (term40 x y z) = (term49 y x z).
Proof. exact (MK_COMB (@lem1003637 x y) (@lem1003627 y x z)). Qed.
Lemma lem1003642 (q : Prop) (p : Prop) (r : Prop) : (term50 p q r) = (term50 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1003643 (y : nat) (x : nat) (z : nat) : (term49 y x z) = (term51 y x z).
Proof. exact (@lem1003642 (y = z) (term47 x y) (term47 x z)). Qed.
Lemma lem1003665 (y : nat) (x : nat) (z : nat) : (term40 x y z) = (term51 y x z).
Proof. exact (TRANS (@lem1003638 y x z) (@lem1003643 y x z)). Qed.
Lemma lem1003666 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1003667 (y : nat) (x : nat) (z : nat) : (term52 x y z) = (term53 y x z).
Proof. exact (MK_COMB (@lem1003666) (@lem1003665 y x z)). Qed.
Lemma lem1003689 (y : nat) (x : nat) (z : nat) : (term51 y x z) = (term51 y x z).
Proof. exact (eq_refl (term51 y x z)). Qed.
Lemma lem1003690 (y : nat) (x : nat) (z : nat) : ((term40 x y z) = (term51 y x z)) = ((term51 y x z) = (term51 y x z)).
Proof. exact (MK_COMB (@lem1003667 y x z) (@lem1003689 y x z)). Qed.
Lemma lem1003692 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1003693 (x : Prop) : (x = x) = True.
Proof. exact (@lem1003692 Prop x). Qed.
Lemma lem1003694 (y : nat) (x : nat) (z : nat) : ((term51 y x z) = (term51 y x z)) = True.
Proof. exact (@lem1003693 (term51 y x z)). Qed.
Lemma lem1003695 (y : nat) (x : nat) (z : nat) : ((term40 x y z) = (term51 y x z)) = True.
Proof. exact (TRANS (@lem1003690 y x z) (@lem1003694 y x z)). Qed.
Lemma lem1003696 (y : nat) (x : nat) (z : nat) : True = ((term40 x y z) = (term51 y x z)).
Proof. exact (SYM (@lem1003695 y x z)). Qed.
Lemma lem1003697 (y : nat) (x : nat) (z : nat) : (term40 x y z) = (term51 y x z).
Proof. exact (EQ_MP (@lem1003696 y x z) (@lem0)). Qed.
Lemma lem1003698 (y : nat) (x : nat) (z : nat) : term51 y x z.
Proof. exact (EQ_MP (@lem1003697 y x z) (@lem1003592 x y z)). Qed.
Lemma lem1003700 (b : Prop) (a : Prop) : (a \/ b) = (term54 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1003701 (x : nat) (y : nat) (z : nat) : (term51 y x z) = (term55 x y z).
Proof. exact (@lem1003700 (term56 y x z) (y = z)). Qed.
Lemma lem1003703 (a : Prop) (b : Prop) : (term57 a b) = (term58 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1003704 (y : nat) (x : nat) (z : nat) : (term59 y x z) = (term60 y x z).
Proof. exact (@lem1003703 (term47 x y) (term47 x z)). Qed.
Lemma lem1003706 (a : Prop) : (term61 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1003707 (x : nat) (y : nat) : (term62 x y) = (x = y).
Proof. exact (@lem1003706 (x = y)). Qed.
Lemma lem1003708 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1003709 (x : nat) (y : nat) : (term63 x y) = (term64 x y).
Proof. exact (MK_COMB (@lem1003708) (@lem1003707 x y)). Qed.
Lemma lem1003711 (a : Prop) : (term61 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1003712 (x : nat) (z : nat) : (term62 x z) = (x = z).
Proof. exact (@lem1003711 (x = z)). Qed.
Lemma lem1003713 (y : nat) (x : nat) (z : nat) : (term60 y x z) = (term65 y x z).
Proof. exact (MK_COMB (@lem1003709 x y) (@lem1003712 x z)). Qed.
Lemma lem1003714 (y : nat) (x : nat) (z : nat) : (term59 y x z) = (term65 y x z).
Proof. exact (TRANS (@lem1003704 y x z) (@lem1003713 y x z)). Qed.
Lemma lem1003715 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1003716 (y : nat) (x : nat) (z : nat) : (term66 y x z) = (term67 y x z).
Proof. exact (MK_COMB (@lem1003715) (@lem1003714 y x z)). Qed.
Lemma lem1003717 (y : nat) (z : nat) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1003718 (x : nat) (y : nat) (z : nat) : (term55 x y z) = (term68 x y z).
Proof. exact (MK_COMB (@lem1003716 y x z) (@lem1003717 y z)). Qed.
Lemma lem1003719 (x : nat) (y : nat) (z : nat) : (term51 y x z) = (term68 x y z).
Proof. exact (TRANS (@lem1003701 x y z) (@lem1003718 x y z)). Qed.
Lemma lem1003721 (m : nat) (h1 : term10) : term69 m.
Proof. exact (conj (@lem1003600 m h1) (@lem1003608 m)). Qed.
Lemma lem1003723 (x : nat) (y : nat) (z : nat) : term68 x y z.
Proof. exact (EQ_MP (@lem1003719 x y z) (@lem1003698 y x z)). Qed.
Lemma lem1003724 (m : nat) : term70 m.
Proof. exact (@lem1003723 (term1 m) (Nat.mul m m) (term1 m)). Qed.
Lemma lem1003727 (m : nat) (h1 : term10) : (Nat.mul m m) = (term1 m).
Proof. exact (@lem1003724 m (@lem1003721 m h1)). Qed.
Lemma lem1003728 (m : nat) (h1 : term10) : term71 m.
Proof. exact (fun h0 : term31 m => @lem1003727 m h1). Qed.
Lemma lem1003730 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1003731 (m : nat) : (term71 m) = ((Nat.mul m m) = (term1 m)).
Proof. exact (@lem1003730 ((Nat.mul m m) = (term1 m))). Qed.
Lemma lem1003732 (m : nat) (h1 : term10) : (Nat.mul m m) = (term1 m).
Proof. exact (EQ_MP (@lem1003731 m) (@lem1003728 m h1)). Qed.
Lemma lem1003735 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1003737 (m : nat) : (term31 m) = (term72 m).
Proof. exact (@lem1003735 ((Nat.mul m m) = (term1 m))). Qed.
Lemma lem1003740 (m : nat) (p : nat) (h1 : term23 m p) : term72 m.
Proof. exact (EQ_MP (@lem1003737 m) (@lem1003494 m p h1)). Qed.
Lemma lem1003743 (m : nat) (p : nat) (h1 : term10) (h2 : term23 m p) : False.
Proof. exact (@lem1003740 m p h2 (@lem1003732 m h1)). Qed.
Lemma lem1003744 (m : nat) (p : nat) (h1 : term10) (h2 : term23 m p) : term73.
Proof. exact (fun h0 : ~ False => @lem1003743 m p h1 h2). Qed.
Lemma lem1003746 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1003747 : term73 = False.
Proof. exact (@lem1003746 False). Qed.
Lemma lem1003806 (_16231 : nat) (h1 : term10) : (term1 _16231) = (Nat.mul _16231 _16231).
Proof. exact (EQ_MP (@lem1003439 _16231) (@lem1003438 _16231 h1)). Qed.
Lemma lem1003807 (m : nat) (h1 : term10) : (term1 m) = (Nat.mul m m).
Proof. exact (@lem1003806 m h1). Qed.
Lemma lem1003808 (m : nat) (h1 : term10) : term41 m.
Proof. exact (fun h0 : term37 m => @lem1003807 m h1). Qed.
Lemma lem1003810 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1003811 (m : nat) : (term41 m) = ((term1 m) = (Nat.mul m m)).
Proof. exact (@lem1003810 ((term1 m) = (Nat.mul m m))). Qed.
Lemma lem1003812 (m : nat) (h1 : term10) : (term1 m) = (Nat.mul m m).
Proof. exact (EQ_MP (@lem1003811 m) (@lem1003808 m h1)). Qed.
Lemma lem1003815 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1003817 (m : nat) : (term37 m) = (term74 m).
Proof. exact (@lem1003815 ((term1 m) = (Nat.mul m m))). Qed.
Lemma lem1003820 (m : nat) (p : nat) (h1 : term24 m p) : term74 m.
Proof. exact (EQ_MP (@lem1003817 m) (@lem1003536 m p h1)). Qed.
Lemma lem1003823 (m : nat) (p : nat) (h1 : term10) (h2 : term24 m p) : False.
Proof. exact (@lem1003820 m p h2 (@lem1003812 m h1)). Qed.
Lemma lem1003824 (m : nat) (p : nat) (h1 : term10) (h2 : term24 m p) : term73.
Proof. exact (fun h0 : ~ False => @lem1003823 m p h1 h2). Qed.
Lemma lem1003826 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1003827 : term73 = False.
Proof. exact (@lem1003826 False). Qed.
Lemma lem1003829 (m : nat) (p : nat) (h1 : term10) (h2 : term24 m p) : False.
Proof. exact (EQ_MP (@lem1003827) (@lem1003824 m p h1 h2)). Qed.
Lemma lem1003830 (m : nat) (p : nat) (h1 : term10) (h2 : term23 m p) : False.
Proof. exact (EQ_MP (@lem1003747) (@lem1003744 m p h1 h2)). Qed.
Lemma lem1003831 (m : nat) (p : nat) (h1 : term10) (h2 : term24 m p) : term10 = False.
Proof. exact (prop_ext (fun h3 : term10 => @lem1003829 m p h1 h2) (fun h3 : False => @lem1003426 h1)). Qed.
Lemma lem1003832 (m : nat) (p : nat) (h1 : term10) (h2 : term24 m p) : False.
Proof. exact (EQ_MP (@lem1003831 m p h1 h2) (@lem1003426 h1)). Qed.
Lemma lem1003833 (m : nat) (p : nat) (h1 : term10) (h2 : term23 m p) : term10 = False.
Proof. exact (prop_ext (fun h3 : term10 => @lem1003830 m p h1 h2) (fun h3 : False => @lem1003411 h1)). Qed.
Lemma lem1003834 (m : nat) (p : nat) (h1 : term10) (h2 : term23 m p) : False.
Proof. exact (EQ_MP (@lem1003833 m p h1 h2) (@lem1003411 h1)). Qed.
Lemma lem1003835 (m : nat) (p : nat) (h1 : term10) (h2 : term3 m p) : False.
Proof. exact (or_elim (@lem1003375 m p h2) (fun h0 : term23 m p => @lem1003834 m p h1 h0) (fun h0 : term24 m p => @lem1003832 m p h1 h0)). Qed.
Lemma lem1003836 (m : nat) (p : nat) (h1 : term10) (h2 : term3 m p) : term10 = False.
Proof. exact (prop_ext (fun h3 : term10 => @lem1003835 m p h1 h2) (fun h3 : False => @lem1003398 h1)). Qed.
Lemma lem1003837 (m : nat) (p : nat) (h1 : term10) (h2 : term3 m p) : False.
Proof. exact (EQ_MP (@lem1003836 m p h1 h2) (@lem1003398 h1)). Qed.
Lemma lem1003838 (m : nat) (p : nat) (h1 : term10) (h2 : term3 m p) : term10 = False.
Proof. exact (prop_ext (fun h3 : term10 => @lem1003837 m p h1 h2) (fun h3 : False => @lem1003313 h1)). Qed.
Lemma lem1003839 (m : nat) (p : nat) (h1 : term10) (h2 : term3 m p) : False.
Proof. exact (EQ_MP (@lem1003838 m p h1 h2) (@lem1003313 h1)). Qed.
Lemma lem1003840 (m : nat) (p : nat) (h1 : term3 m p) : term8.
Proof. exact (fun h0 : term10 => @lem1003839 m p h0 h1). Qed.
Lemma lem1003841 : term8 = term9.
Proof. exact (@lem69 term10). Qed.
Lemma lem1003842 (m : nat) (p : nat) (h1 : term3 m p) : term9.
Proof. exact (EQ_MP (@lem1003841) (@lem1003840 m p h1)). Qed.
Lemma lem1003843 (m : nat) (p : nat) : term12 m p.
Proof. exact (fun h0 : term3 m p => @lem1003842 m p h0). Qed.
Lemma lem1003848 (p : nat) : term16 p.
Proof. exact (fun m : nat => @lem1003843 m p). Qed.
Lemma lem1003853 : term20.
Proof. exact (fun p : nat => @lem1003848 p). Qed.
Lemma lem1003854 : term19.
Proof. exact (EQ_MP (@lem1003278) (@lem1003853)). Qed.
Lemma lem1003855 (p : nat) : term75 p.
Proof. exact (@lem1003854 p). Qed.
Lemma lem1003856 (p : nat) : (term75 p) = (term15 p).
Proof. exact (eq_refl (term75 p)). Qed.
Lemma lem1003857 (p : nat) : term15 p.
Proof. exact (EQ_MP (@lem1003856 p) (@lem1003855 p)). Qed.
Lemma lem1003858 (p : nat) (m : nat) : term76 p m.
Proof. exact (@lem1003857 p m). Qed.
Lemma lem1003859 (m : nat) (p : nat) : (term76 p m) = (term4 m p).
Proof. exact (eq_refl (term76 p m)). Qed.
Lemma lem1003860 (m : nat) (p : nat) : term4 m p.
Proof. exact (EQ_MP (@lem1003859 m p) (@lem1003858 p m)). Qed.
Lemma lem1003862 (m : nat) (p : nat) : term4 m p.
Proof. exact (@lem1003193 m p (@lem1003860 m p)). Qed.
Lemma lem1003863 (m : nat) (p : nat) (h1 : term3 m p) : term8.
Proof. exact (@lem1003862 m p (@lem1003178 m p h1)). Qed.
Lemma lem1003864 (m : nat) (p : nat) (h1 : term3 m p) : False.
Proof. exact (@lem1003863 m p h1 (@lem88196)). Qed.
Lemma lem1003865 (m : nat) (p : nat) (h1 : term3 m p) : (term3 m p) = False.
Proof. exact (prop_ext (fun h2 : term3 m p => @lem1003864 m p h1) (fun h2 : False => @lem1003178 m p h1)). Qed.
Lemma lem1003866 (m : nat) (p : nat) (h1 : term3 m p) : False.
Proof. exact (EQ_MP (@lem1003865 m p h1) (@lem1003178 m p h1)). Qed.
Lemma lem1003867 (m : nat) (p : nat) : term2 m p.
Proof. exact (fun h0 : term3 m p => @lem1003866 m p h0). Qed.
Lemma lem1003870 (m : nat) (p : nat) : ((term1 m) = p) = ((Nat.mul m m) = p).
Proof. exact (EQ_MP (@lem1003177 m p) (@lem1003867 m p)). Qed.
