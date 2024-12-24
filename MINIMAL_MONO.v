Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MINIMAL_MONO_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import LE_MINIMAL_spec.
Require Import LE_REFL_spec.
Require Import LE_TRANS_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm18394_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm4211_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Lemma lem282183 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem282184 (m : nat) (n : nat) : (term1 m n) = (term2 m n).
Proof. exact (@lem282183 (term1 m n)). Qed.
Lemma lem282185 (m : nat) (n : nat) : (term2 m n) = (term1 m n).
Proof. exact (SYM (@lem282184 m n)). Qed.
Lemma lem282186 (m : nat) (n : nat) (h1 : term3 m n) : term3 m n.
Proof. exact (h1). Qed.
Lemma lem282189 (m : nat) (n : nat) (h1 : term4 m n) : term4 m n.
Proof. exact (h1). Qed.
Lemma lem282190 (m : nat) (n : nat) : term5 m n.
Proof. exact (fun h0 : term4 m n => @lem282189 m n h0). Qed.
Lemma lem282191 (m : nat) (n : nat) (h1 : term5 m n) : term5 m n.
Proof. exact (h1). Qed.
Lemma lem282192 (m : nat) (n : nat) (h1 : term4 m n) : term4 m n.
Proof. exact (h1). Qed.
Lemma lem282193 (m : nat) (n : nat) (h1 : term4 m n) (h2 : term5 m n) : term4 m n.
Proof. exact (@lem282191 m n h2 (@lem282192 m n h1)). Qed.
Lemma lem282194 (m : nat) (n : nat) (h1 : term4 m n) : term6 m n.
Proof. exact (fun h0 : term5 m n => @lem282193 m n h1 h0). Qed.
Lemma lem282195 (m : nat) (n : nat) (h1 : term5 m n) : term5 m n.
Proof. exact (h1). Qed.
Lemma lem282196 (m : nat) (n : nat) (h1 : term4 m n) (h2 : term5 m n) : term4 m n.
Proof. exact (@lem282194 m n h1 (@lem282195 m n h2)). Qed.
Lemma lem282197 (m : nat) (n : nat) (h1 : term5 m n) : term5 m n.
Proof. exact (fun h0 : term4 m n => @lem282196 m n h0 h1). Qed.
Lemma lem282198 (m : nat) (n : nat) : term7 m n.
Proof. exact (fun h0 : term5 m n => @lem282197 m n h0). Qed.
Lemma lem282201 (m : nat) (n : nat) : term5 m n.
Proof. exact (@lem282198 m n (@lem282190 m n)). Qed.
Lemma lem282227 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem282228 : term8 = term9.
Proof. exact (@lem282227 term10). Qed.
Lemma lem282245 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem282246 : term12 = term13.
Proof. exact (MK_COMB (@lem282245) (@lem282228)). Qed.
Lemma lem282249 (m : nat) (n : nat) : (term14 m n) = (term14 m n).
Proof. exact (eq_refl (term14 m n)). Qed.
Lemma lem282250 (m : nat) (n : nat) : (term4 m n) = (term15 m n).
Proof. exact (MK_COMB (@lem282249 m n) (@lem282246)). Qed.
Lemma lem282253 (n : nat) : (term16 n) = (term17 n).
Proof. exact (fun_ext (fun m : nat => @lem282250 m n)). Qed.
Lemma lem282254 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem282255 (n : nat) : (term18 n) = (term19 n).
Proof. exact (MK_COMB (@lem282254) (@lem282253 n)). Qed.
Lemma lem282260 : term20 = term21.
Proof. exact (fun_ext (fun n : nat => @lem282255 n)). Qed.
Lemma lem282261 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem282270 : term22 = term23.
Proof. exact (MK_COMB (@lem282261) (@lem282260)). Qed.
Lemma lem282279 (n : nat) (m : nat) (p : nat) : (term24 n m p) = (term24 n m p).
Proof. exact (eq_refl (term24 n m p)). Qed.
Lemma lem282280 (n : nat) (m : nat) : (term25 n m) = (term25 n m).
Proof. exact (fun_ext (fun p : nat => @lem282279 n m p)). Qed.
Lemma lem282281 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem282282 (n : nat) (m : nat) : (term26 n m) = (term26 n m).
Proof. exact (MK_COMB (@lem282281) (@lem282280 n m)). Qed.
Lemma lem282283 (m : nat) : (term27 m) = (term27 m).
Proof. exact (fun_ext (fun n : nat => @lem282282 n m)). Qed.
Lemma lem282284 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem282285 (m : nat) : (term28 m) = (term28 m).
Proof. exact (MK_COMB (@lem282284) (@lem282283 m)). Qed.
Lemma lem282286 : term29 = term29.
Proof. exact (fun_ext (fun m : nat => @lem282285 m)). Qed.
Lemma lem282287 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem282288 : term10 = term10.
Proof. exact (MK_COMB (@lem282287) (@lem282286)). Qed.
Lemma lem282289 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem282290 : term9 = term9.
Proof. exact (MK_COMB (@lem282289) (@lem282288)). Qed.
Lemma lem282291 (n : nat) : (Peano.le n n) = (Peano.le n n).
Proof. exact (eq_refl (Peano.le n n)). Qed.
Lemma lem282292 : term30 = term30.
Proof. exact (fun_ext (fun n : nat => @lem282291 n)). Qed.
Lemma lem282293 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem282294 : term31 = term31.
Proof. exact (MK_COMB (@lem282293) (@lem282292)). Qed.
Lemma lem282295 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem282296 : term11 = term11.
Proof. exact (MK_COMB (@lem282295) (@lem282294)). Qed.
Lemma lem282297 : term13 = term13.
Proof. exact (MK_COMB (@lem282296) (@lem282290)). Qed.
Lemma lem282298 (m : nat) (n : nat) : (Peano.le m n) = (Peano.le m n).
Proof. exact (eq_refl (Peano.le m n)). Qed.
Lemma lem282303 (m : nat) (p : nat) (n : nat) : (term32 m p n) = (term32 m p n).
Proof. exact (eq_refl (term32 m p n)). Qed.
Lemma lem282304 (m : nat) (n : nat) : (term33 m n) = (term33 m n).
Proof. exact (fun_ext (fun p : nat => @lem282303 m p n)). Qed.
Lemma lem282305 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem282306 (m : nat) (n : nat) : (term34 m n) = (term34 m n).
Proof. exact (MK_COMB (@lem282305) (@lem282304 m n)). Qed.
Lemma lem282307 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem282308 (m : nat) (n : nat) : (term35 m n) = (term35 m n).
Proof. exact (MK_COMB (@lem282307) (@lem282306 m n)). Qed.
Lemma lem282309 (m : nat) (n : nat) : (term1 m n) = (term1 m n).
Proof. exact (MK_COMB (@lem282308 m n) (@lem282298 m n)). Qed.
Lemma lem282310 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem282311 (m : nat) (n : nat) : (term3 m n) = (term3 m n).
Proof. exact (MK_COMB (@lem282310) (@lem282309 m n)). Qed.
Lemma lem282312 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem282313 (m : nat) (n : nat) : (term14 m n) = (term14 m n).
Proof. exact (MK_COMB (@lem282312) (@lem282311 m n)). Qed.
Lemma lem282314 (m : nat) (n : nat) : (term15 m n) = (term15 m n).
Proof. exact (MK_COMB (@lem282313 m n) (@lem282297)). Qed.
Lemma lem282315 (n : nat) : (term17 n) = (term17 n).
Proof. exact (fun_ext (fun m : nat => @lem282314 m n)). Qed.
Lemma lem282316 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem282317 (n : nat) : (term19 n) = (term19 n).
Proof. exact (MK_COMB (@lem282316) (@lem282315 n)). Qed.
Lemma lem282318 : term21 = term21.
Proof. exact (fun_ext (fun n : nat => @lem282317 n)). Qed.
Lemma lem282319 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem282320 : term23 = term23.
Proof. exact (MK_COMB (@lem282319) (@lem282318)). Qed.
Lemma lem282377 : term22 = term23.
Proof. exact (TRANS (@lem282270) (@lem282320)). Qed.
Lemma lem282378 : term23 = term22.
Proof. exact (SYM (@lem282377)). Qed.
Lemma lem282379 (m : nat) (n : nat) (h1 : term3 m n) : term3 m n.
Proof. exact (h1). Qed.
Lemma lem282380 (h1 : term31) : term31.
Proof. exact (h1). Qed.
Lemma lem282388 (m : nat) (p : nat) (n : nat) : (term32 m p n) = (term36 m p n).
Proof. exact (@lem17265 (Peano.le p m) (Peano.le p n)). Qed.
Lemma lem282389 (m : nat) (n : nat) : (term33 m n) = (term37 m n).
Proof. exact (fun_ext (fun p : nat => @lem282388 m p n)). Qed.
Lemma lem282390 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem282391 (m : nat) (n : nat) : (term34 m n) = (term38 m n).
Proof. exact (MK_COMB (@lem282390) (@lem282389 m n)). Qed.
Lemma lem282392 (m : nat) (n : nat) : (term39 m n) = (term39 m n).
Proof. exact (eq_refl (term39 m n)). Qed.
Lemma lem282393 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem282394 (m : nat) (n : nat) : (term40 m n) = (term41 m n).
Proof. exact (MK_COMB (@lem282393) (@lem282391 m n)). Qed.
Lemma lem282395 (m : nat) (n : nat) : (term42 m n) = (term43 m n).
Proof. exact (MK_COMB (@lem282394 m n) (@lem282392 m n)). Qed.
Lemma lem282396 (m : nat) (n : nat) : (term3 m n) = (term42 m n).
Proof. exact (@lem17362 (term34 m n) (Peano.le m n)). Qed.
Lemma lem282449 (m : nat) (n : nat) : (term3 m n) = (term43 m n).
Proof. exact (TRANS (@lem282396 m n) (@lem282395 m n)). Qed.
Lemma lem282450 (m : nat) (n : nat) (h1 : term3 m n) : term43 m n.
Proof. exact (EQ_MP (@lem282449 m n) (@lem282379 m n h1)). Qed.
Lemma lem282451 (n : nat) : (Peano.le n n) = (Peano.le n n).
Proof. exact (eq_refl (Peano.le n n)). Qed.
Lemma lem282452 : term30 = term30.
Proof. exact (fun_ext (fun n : nat => @lem282451 n)). Qed.
Lemma lem282453 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem282462 : term31 = term31.
Proof. exact (MK_COMB (@lem282453) (@lem282452)). Qed.
Lemma lem282463 (h1 : term31) : term31.
Proof. exact (EQ_MP (@lem282462) (@lem282380 h1)). Qed.
Lemma lem282553 (m : nat) (n : nat) : (term39 m n) = (term39 m n).
Proof. exact (eq_refl (term39 m n)). Qed.
Lemma lem282568 (m : nat) (p : nat) (n : nat) : (term36 m p n) = (term36 m p n).
Proof. exact (eq_refl (term36 m p n)). Qed.
Lemma lem282569 (m : nat) (n : nat) : (term37 m n) = (term37 m n).
Proof. exact (fun_ext (fun p : nat => @lem282568 m p n)). Qed.
Lemma lem282570 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem282571 (m : nat) (n : nat) : (term38 m n) = (term38 m n).
Proof. exact (MK_COMB (@lem282570) (@lem282569 m n)). Qed.
Lemma lem282572 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem282573 (m : nat) (n : nat) : (term41 m n) = (term41 m n).
Proof. exact (MK_COMB (@lem282572) (@lem282571 m n)). Qed.
Lemma lem282574 (m : nat) (n : nat) : (term43 m n) = (term43 m n).
Proof. exact (MK_COMB (@lem282573 m n) (@lem282553 m n)). Qed.
Lemma lem282575 (m : nat) (n : nat) (h1 : term3 m n) : term43 m n.
Proof. exact (EQ_MP (@lem282574 m n) (@lem282450 m n h1)). Qed.
Lemma lem282580 (n : nat) : (Peano.le n n) = (Peano.le n n).
Proof. exact (eq_refl (Peano.le n n)). Qed.
Lemma lem282581 : term30 = term30.
Proof. exact (fun_ext (fun n : nat => @lem282580 n)). Qed.
Lemma lem282582 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem282583 : term31 = term31.
Proof. exact (MK_COMB (@lem282582) (@lem282581)). Qed.
Lemma lem282584 (h1 : term31) : term31.
Proof. exact (EQ_MP (@lem282583) (@lem282463 h1)). Qed.
Lemma lem282621 (m : nat) (n : nat) (h1 : term3 m n) : term38 m n.
Proof. exact (proj1 (@lem282575 m n h1)). Qed.
Lemma lem282623 (n : nat) : (Peano.le n n) = (Peano.le n n).
Proof. exact (eq_refl (Peano.le n n)). Qed.
Lemma lem282624 : term30 = term30.
Proof. exact (fun_ext (fun n : nat => @lem282623 n)). Qed.
Lemma lem282625 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem282627 : term31 = term31.
Proof. exact (MK_COMB (@lem282625) (@lem282624)). Qed.
Lemma lem282628 (h1 : term31) : term31.
Proof. exact (EQ_MP (@lem282627) (@lem282584 h1)). Qed.
Lemma lem282661 (m : nat) (p : nat) (n : nat) : (term36 m p n) = (term36 m p n).
Proof. exact (eq_refl (term36 m p n)). Qed.
Lemma lem282662 (m : nat) (n : nat) : (term37 m n) = (term37 m n).
Proof. exact (fun_ext (fun p : nat => @lem282661 m p n)). Qed.
Lemma lem282663 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem282665 (m : nat) (n : nat) : (term38 m n) = (term38 m n).
Proof. exact (MK_COMB (@lem282663) (@lem282662 m n)). Qed.
Lemma lem282666 (m : nat) (n : nat) (h1 : term3 m n) : term38 m n.
Proof. exact (EQ_MP (@lem282665 m n) (@lem282621 m n h1)). Qed.
Lemma lem282671 (_6462 : nat) (h1 : term31) : term44 _6462.
Proof. exact (@lem282628 h1 _6462). Qed.
Lemma lem282672 (_6462 : nat) : (term44 _6462) = (Peano.le _6462 _6462).
Proof. exact (eq_refl (term44 _6462)). Qed.
Lemma lem282683 (_6466 : nat) (m : nat) (n : nat) (h1 : term3 m n) : term45 m n _6466.
Proof. exact (@lem282666 m n h1 _6466). Qed.
Lemma lem282684 (m : nat) (_6466 : nat) (n : nat) : (term45 m n _6466) = (term36 m _6466 n).
Proof. exact (eq_refl (term45 m n _6466)). Qed.
Lemma lem282705 (_6466 : nat) (m : nat) (n : nat) (h1 : term3 m n) : term36 m _6466 n.
Proof. exact (EQ_MP (@lem282684 m _6466 n) (@lem282683 _6466 m n h1)). Qed.
Lemma lem282707 (m : nat) (n : nat) (h1 : term3 m n) : term39 m n.
Proof. exact (proj2 (@lem282575 m n h1)). Qed.
Lemma lem282709 (_6462 : nat) (h1 : term31) : Peano.le _6462 _6462.
Proof. exact (EQ_MP (@lem282672 _6462) (@lem282671 _6462 h1)). Qed.
Lemma lem282710 (m : nat) (h1 : term31) : Peano.le m m.
Proof. exact (@lem282709 m h1). Qed.
Lemma lem282711 (m : nat) (h1 : term31) : term46 m.
Proof. exact (fun h0 : term47 m => @lem282710 m h1). Qed.
Lemma lem282713 (p : Prop) : (term48 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem282714 (m : nat) : (term46 m) = (Peano.le m m).
Proof. exact (@lem282713 (Peano.le m m)). Qed.
Lemma lem282715 (m : nat) (h1 : term31) : Peano.le m m.
Proof. exact (EQ_MP (@lem282714 m) (@lem282711 m h1)). Qed.
Lemma lem282721 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem282722 (n : nat) (_6466 : nat) (m : nat) : (term36 m _6466 n) = (term49 n _6466 m).
Proof. exact (@lem282721 (Peano.le _6466 n) (term39 _6466 m)). Qed.
Lemma lem282728 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem282729 (n : nat) (_6466 : nat) (m : nat) : (term50 m _6466 n) = (term51 n _6466 m).
Proof. exact (MK_COMB (@lem282728) (@lem282722 n _6466 m)). Qed.
Lemma lem282735 (n : nat) (_6466 : nat) (m : nat) : (term49 n _6466 m) = (term49 n _6466 m).
Proof. exact (eq_refl (term49 n _6466 m)). Qed.
Lemma lem282736 (n : nat) (_6466 : nat) (m : nat) : ((term36 m _6466 n) = (term49 n _6466 m)) = ((term49 n _6466 m) = (term49 n _6466 m)).
Proof. exact (MK_COMB (@lem282729 n _6466 m) (@lem282735 n _6466 m)). Qed.
Lemma lem282738 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem282739 (x : Prop) : (x = x) = True.
Proof. exact (@lem282738 Prop x). Qed.
Lemma lem282740 (n : nat) (_6466 : nat) (m : nat) : ((term49 n _6466 m) = (term49 n _6466 m)) = True.
Proof. exact (@lem282739 (term49 n _6466 m)). Qed.
Lemma lem282741 (n : nat) (_6466 : nat) (m : nat) : ((term36 m _6466 n) = (term49 n _6466 m)) = True.
Proof. exact (TRANS (@lem282736 n _6466 m) (@lem282740 n _6466 m)). Qed.
Lemma lem282742 (n : nat) (_6466 : nat) (m : nat) : True = ((term36 m _6466 n) = (term49 n _6466 m)).
Proof. exact (SYM (@lem282741 n _6466 m)). Qed.
Lemma lem282743 (n : nat) (_6466 : nat) (m : nat) : (term36 m _6466 n) = (term49 n _6466 m).
Proof. exact (EQ_MP (@lem282742 n _6466 m) (@lem0)). Qed.
Lemma lem282744 (_6466 : nat) (m : nat) (n : nat) (h1 : term3 m n) : term49 n _6466 m.
Proof. exact (EQ_MP (@lem282743 n _6466 m) (@lem282705 _6466 m n h1)). Qed.
Lemma lem282746 (b : Prop) (a : Prop) : (a \/ b) = (term52 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem282747 (m : nat) (_6466 : nat) (n : nat) : (term49 n _6466 m) = (term53 m _6466 n).
Proof. exact (@lem282746 (term39 _6466 m) (Peano.le _6466 n)). Qed.
Lemma lem282749 (a : Prop) : (term54 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem282750 (_6466 : nat) (m : nat) : (term55 _6466 m) = (Peano.le _6466 m).
Proof. exact (@lem282749 (Peano.le _6466 m)). Qed.
Lemma lem282751 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem282752 (_6466 : nat) (m : nat) : (term56 _6466 m) = (term57 _6466 m).
Proof. exact (MK_COMB (@lem282751) (@lem282750 _6466 m)). Qed.
Lemma lem282753 (_6466 : nat) (n : nat) : (Peano.le _6466 n) = (Peano.le _6466 n).
Proof. exact (eq_refl (Peano.le _6466 n)). Qed.
Lemma lem282754 (m : nat) (_6466 : nat) (n : nat) : (term53 m _6466 n) = (term32 m _6466 n).
Proof. exact (MK_COMB (@lem282752 _6466 m) (@lem282753 _6466 n)). Qed.
Lemma lem282755 (m : nat) (_6466 : nat) (n : nat) : (term49 n _6466 m) = (term32 m _6466 n).
Proof. exact (TRANS (@lem282747 m _6466 n) (@lem282754 m _6466 n)). Qed.
Lemma lem282758 (_6466 : nat) (m : nat) (n : nat) (h1 : term3 m n) : term32 m _6466 n.
Proof. exact (EQ_MP (@lem282755 m _6466 n) (@lem282744 _6466 m n h1)). Qed.
Lemma lem282759 (m : nat) (n : nat) (h1 : term3 m n) : term58 m n.
Proof. exact (@lem282758 m m n h1). Qed.
Lemma lem282762 (m : nat) (n : nat) (h1 : term31) (h2 : term3 m n) : Peano.le m n.
Proof. exact (@lem282759 m n h2 (@lem282715 m h1)). Qed.
Lemma lem282763 (m : nat) (n : nat) (h1 : term31) (h2 : term3 m n) : term59 m n.
Proof. exact (fun h0 : term39 m n => @lem282762 m n h1 h2). Qed.
Lemma lem282765 (p : Prop) : (term48 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem282766 (m : nat) (n : nat) : (term59 m n) = (Peano.le m n).
Proof. exact (@lem282765 (Peano.le m n)). Qed.
Lemma lem282767 (m : nat) (n : nat) (h1 : term31) (h2 : term3 m n) : Peano.le m n.
Proof. exact (EQ_MP (@lem282766 m n) (@lem282763 m n h1 h2)). Qed.
Lemma lem282770 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem282772 (m : nat) (n : nat) : (term39 m n) = (term60 m n).
Proof. exact (@lem282770 (Peano.le m n)). Qed.
Lemma lem282775 (m : nat) (n : nat) (h1 : term3 m n) : term60 m n.
Proof. exact (EQ_MP (@lem282772 m n) (@lem282707 m n h1)). Qed.
Lemma lem282778 (m : nat) (n : nat) (h1 : term31) (h2 : term3 m n) : False.
Proof. exact (@lem282775 m n h2 (@lem282767 m n h1 h2)). Qed.
Lemma lem282779 (m : nat) (n : nat) (h1 : term31) (h2 : term3 m n) : term61.
Proof. exact (fun h0 : ~ False => @lem282778 m n h1 h2). Qed.
Lemma lem282781 (p : Prop) : (term48 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem282782 : term61 = False.
Proof. exact (@lem282781 False). Qed.
Lemma lem282783 (m : nat) (n : nat) (h1 : term31) (h2 : term3 m n) : False.
Proof. exact (EQ_MP (@lem282782) (@lem282779 m n h1 h2)). Qed.
Lemma lem282784 (m : nat) (n : nat) (h1 : term31) (h2 : term3 m n) : term31 = False.
Proof. exact (prop_ext (fun h3 : term31 => @lem282783 m n h1 h2) (fun h3 : False => @lem282628 h1)). Qed.
Lemma lem282785 (m : nat) (n : nat) (h1 : term31) (h2 : term3 m n) : False.
Proof. exact (EQ_MP (@lem282784 m n h1 h2) (@lem282628 h1)). Qed.
Lemma lem282786 (m : nat) (n : nat) (h1 : term31) (h2 : term3 m n) : term31 = False.
Proof. exact (prop_ext (fun h3 : term31 => @lem282785 m n h1 h2) (fun h3 : False => @lem282584 h1)). Qed.
Lemma lem282787 (m : nat) (n : nat) (h1 : term31) (h2 : term3 m n) : False.
Proof. exact (EQ_MP (@lem282786 m n h1 h2) (@lem282584 h1)). Qed.
Lemma lem282788 (m : nat) (n : nat) (h1 : term31) (h2 : term3 m n) : term31 = False.
Proof. exact (prop_ext (fun h3 : term31 => @lem282787 m n h1 h2) (fun h3 : False => @lem282463 h1)). Qed.
Lemma lem282789 (m : nat) (n : nat) (h1 : term31) (h2 : term3 m n) : False.
Proof. exact (EQ_MP (@lem282788 m n h1 h2) (@lem282463 h1)). Qed.
Lemma lem282790 (m : nat) (n : nat) (h1 : term31) (h2 : term3 m n) : term8.
Proof. exact (fun h0 : term10 => @lem282789 m n h1 h2). Qed.
Lemma lem282791 : term8 = term9.
Proof. exact (@lem69 term10). Qed.
Lemma lem282792 (m : nat) (n : nat) (h1 : term31) (h2 : term3 m n) : term9.
Proof. exact (EQ_MP (@lem282791) (@lem282790 m n h1 h2)). Qed.
Lemma lem282793 (m : nat) (n : nat) (h1 : term3 m n) : term13.
Proof. exact (fun h0 : term31 => @lem282792 m n h0 h1). Qed.
Lemma lem282794 (m : nat) (n : nat) : term15 m n.
Proof. exact (fun h0 : term3 m n => @lem282793 m n h0). Qed.
Lemma lem282799 (n : nat) : term19 n.
Proof. exact (fun m : nat => @lem282794 m n). Qed.
Lemma lem282804 : term23.
Proof. exact (fun n : nat => @lem282799 n). Qed.
Lemma lem282805 : term22.
Proof. exact (EQ_MP (@lem282378) (@lem282804)). Qed.
Lemma lem282806 (n : nat) : term62 n.
Proof. exact (@lem282805 n). Qed.
Lemma lem282807 (n : nat) : (term62 n) = (term18 n).
Proof. exact (eq_refl (term62 n)). Qed.
Lemma lem282808 (n : nat) : term18 n.
Proof. exact (EQ_MP (@lem282807 n) (@lem282806 n)). Qed.
Lemma lem282809 (n : nat) (m : nat) : term63 n m.
Proof. exact (@lem282808 n m). Qed.
Lemma lem282810 (m : nat) (n : nat) : (term63 n m) = (term4 m n).
Proof. exact (eq_refl (term63 n m)). Qed.
Lemma lem282811 (m : nat) (n : nat) : term4 m n.
Proof. exact (EQ_MP (@lem282810 m n) (@lem282809 n m)). Qed.
Lemma lem282813 (m : nat) (n : nat) : term4 m n.
Proof. exact (@lem282201 m n (@lem282811 m n)). Qed.
Lemma lem282814 (m : nat) (n : nat) (h1 : term3 m n) : term12.
Proof. exact (@lem282813 m n (@lem282186 m n h1)). Qed.
Lemma lem282815 (m : nat) (n : nat) (h1 : term3 m n) : term8.
Proof. exact (@lem282814 m n h1 (@lem91603)). Qed.
Lemma lem282816 (m : nat) (n : nat) (h1 : term3 m n) : False.
Proof. exact (@lem282815 m n h1 (@lem93743)). Qed.
Lemma lem282817 (m : nat) (n : nat) (h1 : term3 m n) : (term3 m n) = False.
Proof. exact (prop_ext (fun h2 : term3 m n => @lem282816 m n h1) (fun h2 : False => @lem282186 m n h1)). Qed.
Lemma lem282818 (m : nat) (n : nat) (h1 : term3 m n) : False.
Proof. exact (EQ_MP (@lem282817 m n h1) (@lem282186 m n h1)). Qed.
Lemma lem282819 (m : nat) (n : nat) : term2 m n.
Proof. exact (fun h0 : term3 m n => @lem282818 m n h0). Qed.
Lemma lem282820 (m : nat) (n : nat) : term1 m n.
Proof. exact (EQ_MP (@lem282185 m n) (@lem282819 m n)). Qed.
Lemma lem282821 (m : nat) (n : nat) (h1 : term1 m n) : term1 m n.
Proof. exact (h1). Qed.
Lemma lem282822 (m : nat) (n : nat) (h1 : term34 m n) : term34 m n.
Proof. exact (h1). Qed.
Lemma lem282823 (m : nat) (n : nat) (h1 : term34 m n) (h2 : term1 m n) : Peano.le m n.
Proof. exact (@lem282821 m n h2 (@lem282822 m n h1)). Qed.
Lemma lem282824 (m : nat) (n : nat) (h1 : term34 m n) : term64 m n.
Proof. exact (fun h0 : term1 m n => @lem282823 m n h1 h0). Qed.
Lemma lem282825 (m : nat) (n : nat) (h1 : term1 m n) : term1 m n.
Proof. exact (h1). Qed.
Lemma lem282826 (m : nat) (n : nat) (h1 : term34 m n) (h2 : term1 m n) : Peano.le m n.
Proof. exact (@lem282824 m n h1 (@lem282825 m n h2)). Qed.
Lemma lem282827 (m : nat) (n : nat) (h1 : term1 m n) : term1 m n.
Proof. exact (fun h0 : term34 m n => @lem282826 m n h0 h1). Qed.
Lemma lem282828 (m : nat) (n : nat) : term65 m n.
Proof. exact (fun h0 : term1 m n => @lem282827 m n h0). Qed.
Lemma lem282840 (P : nat -> Prop) (Q : nat -> Prop) (h1 : term66 P Q) : term66 P Q.
Proof. exact (h1). Qed.
Lemma lem282841 (P : nat -> Prop) (Q : nat -> Prop) (h1 : term67 P Q) : term67 P Q.
Proof. exact (h1). Qed.
Lemma lem282842 (P : nat -> Prop) (h1 : term68 P) : term68 P.
Proof. exact (h1). Qed.
Lemma lem282843 (Q : nat -> Prop) (h1 : term68 Q) : term68 Q.
Proof. exact (h1). Qed.
Lemma lem282845 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem282846 (Q : nat -> Prop) : (term68 Q) = (term69 Q).
Proof. exact (@lem282845 (term68 Q)). Qed.
Lemma lem282847 (Q : nat -> Prop) : (term69 Q) = (term68 Q).
Proof. exact (SYM (@lem282846 Q)). Qed.
Lemma lem282848 (Q : nat -> Prop) (h1 : term70 Q) : term70 Q.
Proof. exact (h1). Qed.
Lemma lem282851 (P : nat -> Prop) (Q : nat -> Prop) (h1 : term71 P Q) : term71 P Q.
Proof. exact (h1). Qed.
Lemma lem282852 (P : nat -> Prop) (Q : nat -> Prop) : term72 P Q.
Proof. exact (fun h0 : term71 P Q => @lem282851 P Q h0). Qed.
Lemma lem282853 (P : nat -> Prop) (Q : nat -> Prop) (h1 : term72 P Q) : term72 P Q.
Proof. exact (h1). Qed.
Lemma lem282854 (P : nat -> Prop) (Q : nat -> Prop) (h1 : term71 P Q) : term71 P Q.
Proof. exact (h1). Qed.
Lemma lem282855 (P : nat -> Prop) (Q : nat -> Prop) (h1 : term71 P Q) (h2 : term72 P Q) : term71 P Q.
Proof. exact (@lem282853 P Q h2 (@lem282854 P Q h1)). Qed.
Lemma lem282856 (P : nat -> Prop) (Q : nat -> Prop) (h1 : term71 P Q) : term73 P Q.
Proof. exact (fun h0 : term72 P Q => @lem282855 P Q h1 h0). Qed.
Lemma lem282857 (P : nat -> Prop) (Q : nat -> Prop) (h1 : term72 P Q) : term72 P Q.
Proof. exact (h1). Qed.
Lemma lem282858 (P : nat -> Prop) (Q : nat -> Prop) (h1 : term71 P Q) (h2 : term72 P Q) : term71 P Q.
Proof. exact (@lem282856 P Q h1 (@lem282857 P Q h2)). Qed.
Lemma lem282859 (P : nat -> Prop) (Q : nat -> Prop) (h1 : term72 P Q) : term72 P Q.
Proof. exact (fun h0 : term71 P Q => @lem282858 P Q h0 h1). Qed.
Lemma lem282860 (P : nat -> Prop) (Q : nat -> Prop) : term74 P Q.
Proof. exact (fun h0 : term72 P Q => @lem282859 P Q h0). Qed.
Lemma lem282863 (P : nat -> Prop) (Q : nat -> Prop) : term72 P Q.
Proof. exact (@lem282860 P Q (@lem282852 P Q)). Qed.
Lemma lem282887 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem282888 (Q : nat -> Prop) : (term69 Q) = (term75 Q).
Proof. exact (@lem282887 (term70 Q)). Qed.
Lemma lem282890 (t : Prop) : (term54 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem282891 (Q : nat -> Prop) : (term75 Q) = (term68 Q).
Proof. exact (@lem282890 (term68 Q)). Qed.
Lemma lem282896 (Q : nat -> Prop) : (term69 Q) = (term68 Q).
Proof. exact (TRANS (@lem282888 Q) (@lem282891 Q)). Qed.
Lemma lem282897 (P : nat -> Prop) (Q : nat -> Prop) : (term76 P Q) = (term76 P Q).
Proof. exact (eq_refl (term76 P Q)). Qed.
Lemma lem282898 (P : nat -> Prop) (Q : nat -> Prop) : (term77 P Q) = (term78 P Q).
Proof. exact (MK_COMB (@lem282897 P Q) (@lem282896 Q)). Qed.
Lemma lem282901 (P : nat -> Prop) : (term79 P) = (term79 P).
Proof. exact (eq_refl (term79 P)). Qed.
Lemma lem282902 (P : nat -> Prop) (Q : nat -> Prop) : (term71 P Q) = (term80 P Q).
Proof. exact (MK_COMB (@lem282901 P) (@lem282898 P Q)). Qed.
Lemma lem282905 (Q : nat -> Prop) : (term81 Q) = (term82 Q).
Proof. exact (fun_ext (fun P : nat -> Prop => @lem282902 P Q)). Qed.
Lemma lem282906 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem282907 (Q : nat -> Prop) : (term83 Q) = (term84 Q).
Proof. exact (MK_COMB (@lem282906) (@lem282905 Q)). Qed.
Lemma lem282912 : term85 = term86.
Proof. exact (fun_ext (fun Q : nat -> Prop => @lem282907 Q)). Qed.
Lemma lem282913 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem282922 : term87 = term88.
Proof. exact (MK_COMB (@lem282913) (@lem282912)). Qed.
Lemma lem282923 (Q : nat -> Prop) (n : nat) : (Q n) = (Q n).
Proof. exact (eq_refl (Q n)). Qed.
Lemma lem282924 (Q : nat -> Prop) : (term89 Q) = (term89 Q).
Proof. exact (fun_ext (fun n : nat => @lem282923 Q n)). Qed.
Lemma lem282925 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem282926 (Q : nat -> Prop) : (term68 Q) = (term68 Q).
Proof. exact (MK_COMB (@lem282925) (@lem282924 Q)). Qed.
Lemma lem282931 (P : nat -> Prop) (Q : nat -> Prop) (n : nat) : (term90 P Q n) = (term90 P Q n).
Proof. exact (eq_refl (term90 P Q n)). Qed.
Lemma lem282932 (P : nat -> Prop) (Q : nat -> Prop) : (term91 P Q) = (term91 P Q).
Proof. exact (fun_ext (fun n : nat => @lem282931 P Q n)). Qed.
Lemma lem282933 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem282934 (P : nat -> Prop) (Q : nat -> Prop) : (term67 P Q) = (term67 P Q).
Proof. exact (MK_COMB (@lem282933) (@lem282932 P Q)). Qed.
Lemma lem282935 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem282936 (P : nat -> Prop) (Q : nat -> Prop) : (term76 P Q) = (term76 P Q).
Proof. exact (MK_COMB (@lem282935) (@lem282934 P Q)). Qed.
Lemma lem282937 (P : nat -> Prop) (Q : nat -> Prop) : (term78 P Q) = (term78 P Q).
Proof. exact (MK_COMB (@lem282936 P Q) (@lem282926 Q)). Qed.
Lemma lem282938 (P : nat -> Prop) (n : nat) : (P n) = (P n).
Proof. exact (eq_refl (P n)). Qed.
Lemma lem282939 (P : nat -> Prop) : (term89 P) = (term89 P).
Proof. exact (fun_ext (fun n : nat => @lem282938 P n)). Qed.
Lemma lem282940 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem282941 (P : nat -> Prop) : (term68 P) = (term68 P).
Proof. exact (MK_COMB (@lem282940) (@lem282939 P)). Qed.
Lemma lem282942 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem282943 (P : nat -> Prop) : (term79 P) = (term79 P).
Proof. exact (MK_COMB (@lem282942) (@lem282941 P)). Qed.
Lemma lem282944 (P : nat -> Prop) (Q : nat -> Prop) : (term80 P Q) = (term80 P Q).
Proof. exact (MK_COMB (@lem282943 P) (@lem282937 P Q)). Qed.
Lemma lem282945 (Q : nat -> Prop) : (term82 Q) = (term82 Q).
Proof. exact (fun_ext (fun P : nat -> Prop => @lem282944 P Q)). Qed.
Lemma lem282946 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem282947 (Q : nat -> Prop) : (term84 Q) = (term84 Q).
Proof. exact (MK_COMB (@lem282946) (@lem282945 Q)). Qed.
Lemma lem282948 : term86 = term86.
Proof. exact (fun_ext (fun Q : nat -> Prop => @lem282947 Q)). Qed.
Lemma lem282949 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem282950 : term88 = term88.
Proof. exact (MK_COMB (@lem282949) (@lem282948)). Qed.
Lemma lem282989 : term87 = term88.
Proof. exact (TRANS (@lem282922) (@lem282950)). Qed.
Lemma lem282990 : term88 = term87.
Proof. exact (SYM (@lem282989)). Qed.
Lemma lem282991 (P : nat -> Prop) (h1 : term68 P) : term68 P.
Proof. exact (h1). Qed.
Lemma lem282992 (P : nat -> Prop) (Q : nat -> Prop) (h1 : term67 P Q) : term67 P Q.
Proof. exact (h1). Qed.
Lemma lem282994 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem282995 (Q : nat -> Prop) : (term68 Q) = (term69 Q).
Proof. exact (@lem282994 (term68 Q)). Qed.
Lemma lem282996 (Q : nat -> Prop) : (term69 Q) = (term68 Q).
Proof. exact (SYM (@lem282995 Q)). Qed.
Lemma lem282997 (Q : nat -> Prop) (h1 : term70 Q) : term70 Q.
Proof. exact (h1). Qed.
Lemma lem282998 (P : nat -> Prop) (n : nat) : (P n) = (P n).
Proof. exact (eq_refl (P n)). Qed.
Lemma lem282999 (P : nat -> Prop) : (term89 P) = (term89 P).
Proof. exact (fun_ext (fun n : nat => @lem282998 P n)). Qed.
Lemma lem283000 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem283009 (P : nat -> Prop) : (term68 P) = (term68 P).
Proof. exact (MK_COMB (@lem283000) (@lem282999 P)). Qed.
Lemma lem283010 (P : nat -> Prop) (h1 : term68 P) : term68 P.
Proof. exact (EQ_MP (@lem283009 P) (@lem282991 P h1)). Qed.
Lemma lem283017 (P : nat -> Prop) (Q : nat -> Prop) (n : nat) : (term90 P Q n) = (term92 P Q n).
Proof. exact (@lem17265 (P n) (Q n)). Qed.
Lemma lem283018 (P : nat -> Prop) (Q : nat -> Prop) : (term91 P Q) = (term93 P Q).
Proof. exact (fun_ext (fun n : nat => @lem283017 P Q n)). Qed.
Lemma lem283019 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem283056 (P : nat -> Prop) (Q : nat -> Prop) : (term67 P Q) = (term94 P Q).
Proof. exact (MK_COMB (@lem283019) (@lem283018 P Q)). Qed.
Lemma lem283057 (P : nat -> Prop) (Q : nat -> Prop) (h1 : term67 P Q) : term94 P Q.
Proof. exact (EQ_MP (@lem283056 P Q) (@lem282992 P Q h1)). Qed.
Lemma lem283059 (P : nat -> Prop) : (term95 P) = (term96 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem283060 (Q : nat -> Prop) : (term70 Q) = (term97 Q).
Proof. exact (@lem283059 (term89 Q)). Qed.
Lemma lem283061 (Q : nat -> Prop) (n : nat) : (term98 Q n) = (Q n).
Proof. exact (eq_refl (term98 Q n)). Qed.
Lemma lem283062 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem283064 (Q : nat -> Prop) (n : nat) : (term99 Q n) = (term100 Q n).
Proof. exact (MK_COMB (@lem283062) (@lem283061 Q n)). Qed.
Lemma lem283065 (Q : nat -> Prop) : (term101 Q) = (term102 Q).
Proof. exact (fun_ext (fun n : nat => @lem283064 Q n)). Qed.
Lemma lem283066 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem283067 (Q : nat -> Prop) : (term97 Q) = (term96 Q).
Proof. exact (MK_COMB (@lem283066) (@lem283065 Q)). Qed.
Lemma lem283076 (Q : nat -> Prop) : (term70 Q) = (term96 Q).
Proof. exact (TRANS (@lem283060 Q) (@lem283067 Q)). Qed.
Lemma lem283077 (Q : nat -> Prop) (h1 : term70 Q) : term96 Q.
Proof. exact (EQ_MP (@lem283076 Q) (@lem282997 Q h1)). Qed.
Lemma lem283089 (P : nat -> Prop) (Q : nat -> Prop) (n : nat) : (term92 P Q n) = (term92 P Q n).
Proof. exact (eq_refl (term92 P Q n)). Qed.
Lemma lem283090 (P : nat -> Prop) (Q : nat -> Prop) : (term93 P Q) = (term93 P Q).
Proof. exact (fun_ext (fun n : nat => @lem283089 P Q n)). Qed.
Lemma lem283091 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem283092 (P : nat -> Prop) (Q : nat -> Prop) : (term94 P Q) = (term94 P Q).
Proof. exact (MK_COMB (@lem283091) (@lem283090 P Q)). Qed.
Lemma lem283093 (P : nat -> Prop) (Q : nat -> Prop) (h1 : term67 P Q) : term94 P Q.
Proof. exact (EQ_MP (@lem283092 P Q) (@lem283057 P Q h1)). Qed.
Lemma lem283098 (Q : nat -> Prop) (n : nat) : (term100 Q n) = (term100 Q n).
Proof. exact (eq_refl (term100 Q n)). Qed.
Lemma lem283099 (Q : nat -> Prop) : (term102 Q) = (term102 Q).
Proof. exact (fun_ext (fun n : nat => @lem283098 Q n)). Qed.
Lemma lem283100 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem283101 (Q : nat -> Prop) : (term96 Q) = (term96 Q).
Proof. exact (MK_COMB (@lem283100) (@lem283099 Q)). Qed.
Lemma lem283102 (Q : nat -> Prop) (h1 : term70 Q) : term96 Q.
Proof. exact (EQ_MP (@lem283101 Q) (@lem283077 Q h1)). Qed.
Lemma lem283106 (P : nat -> Prop) (n : nat) (h1 : P n) : P n.
Proof. exact (h1). Qed.
Lemma lem283114 (P : nat -> Prop) (Q : nat -> Prop) (n : nat) : (term92 P Q n) = (term92 P Q n).
Proof. exact (eq_refl (term92 P Q n)). Qed.
Lemma lem283115 (P : nat -> Prop) (Q : nat -> Prop) : (term93 P Q) = (term93 P Q).
Proof. exact (fun_ext (fun n : nat => @lem283114 P Q n)). Qed.
Lemma lem283116 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem283118 (P : nat -> Prop) (Q : nat -> Prop) : (term94 P Q) = (term94 P Q).
Proof. exact (MK_COMB (@lem283116) (@lem283115 P Q)). Qed.
Lemma lem283119 (P : nat -> Prop) (Q : nat -> Prop) (h1 : term67 P Q) : term94 P Q.
Proof. exact (EQ_MP (@lem283118 P Q) (@lem283093 P Q h1)). Qed.
Lemma lem283121 (Q : nat -> Prop) (n : nat) : (term100 Q n) = (term100 Q n).
Proof. exact (eq_refl (term100 Q n)). Qed.
Lemma lem283122 (Q : nat -> Prop) : (term102 Q) = (term102 Q).
Proof. exact (fun_ext (fun n : nat => @lem283121 Q n)). Qed.
Lemma lem283123 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem283125 (Q : nat -> Prop) : (term96 Q) = (term96 Q).
Proof. exact (MK_COMB (@lem283123) (@lem283122 Q)). Qed.
Lemma lem283126 (Q : nat -> Prop) (h1 : term70 Q) : term96 Q.
Proof. exact (EQ_MP (@lem283125 Q) (@lem283102 Q h1)). Qed.
Lemma lem283130 (P : nat -> Prop) (n : nat) (h1 : P n) : P n.
Proof. exact (h1). Qed.
Lemma lem283131 (_6467 : nat) (P : nat -> Prop) (Q : nat -> Prop) (h1 : term67 P Q) : term103 P Q _6467.
Proof. exact (@lem283119 P Q h1 _6467). Qed.
Lemma lem283132 (P : nat -> Prop) (Q : nat -> Prop) (_6467 : nat) : (term103 P Q _6467) = (term92 P Q _6467).
Proof. exact (eq_refl (term103 P Q _6467)). Qed.
Lemma lem283134 (_6468 : nat) (Q : nat -> Prop) (h1 : term70 Q) : term104 Q _6468.
Proof. exact (@lem283126 Q h1 _6468). Qed.
Lemma lem283135 (Q : nat -> Prop) (_6468 : nat) : (term104 Q _6468) = (term100 Q _6468).
Proof. exact (eq_refl (term104 Q _6468)). Qed.
Lemma lem283142 (_6467 : nat) (P : nat -> Prop) (Q : nat -> Prop) (h1 : term67 P Q) : term92 P Q _6467.
Proof. exact (EQ_MP (@lem283132 P Q _6467) (@lem283131 _6467 P Q h1)). Qed.
Lemma lem283144 (_6468 : nat) (Q : nat -> Prop) (h1 : term70 Q) : term100 Q _6468.
Proof. exact (EQ_MP (@lem283135 Q _6468) (@lem283134 _6468 Q h1)). Qed.
Lemma lem283146 (P : nat -> Prop) (n : nat) (h1 : P n) : P n.
Proof. exact (h1). Qed.
Lemma lem283148 (P : nat -> Prop) (n : nat) (h1 : P n) : P n.
Proof. exact (h1). Qed.
Lemma lem283149 (P : nat -> Prop) (n : nat) (h1 : P n) : term105 P n.
Proof. exact (fun h0 : term100 P n => @lem283148 P n h1). Qed.
Lemma lem283151 (p : Prop) : (term48 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem283152 (P : nat -> Prop) (n : nat) : (term105 P n) = (P n).
Proof. exact (@lem283151 (P n)). Qed.
Lemma lem283153 (P : nat -> Prop) (n : nat) (h1 : P n) : P n.
Proof. exact (EQ_MP (@lem283152 P n) (@lem283149 P n h1)). Qed.
Lemma lem283159 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem283160 (Q : nat -> Prop) (P : nat -> Prop) (_6467 : nat) : (term92 P Q _6467) = (term106 Q P _6467).
Proof. exact (@lem283159 (Q _6467) (term100 P _6467)). Qed.
Lemma lem283166 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem283167 (Q : nat -> Prop) (P : nat -> Prop) (_6467 : nat) : (term107 P Q _6467) = (term108 Q P _6467).
Proof. exact (MK_COMB (@lem283166) (@lem283160 Q P _6467)). Qed.
Lemma lem283173 (Q : nat -> Prop) (P : nat -> Prop) (_6467 : nat) : (term106 Q P _6467) = (term106 Q P _6467).
Proof. exact (eq_refl (term106 Q P _6467)). Qed.
Lemma lem283174 (Q : nat -> Prop) (P : nat -> Prop) (_6467 : nat) : ((term92 P Q _6467) = (term106 Q P _6467)) = ((term106 Q P _6467) = (term106 Q P _6467)).
Proof. exact (MK_COMB (@lem283167 Q P _6467) (@lem283173 Q P _6467)). Qed.
Lemma lem283176 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem283177 (x : Prop) : (x = x) = True.
Proof. exact (@lem283176 Prop x). Qed.
Lemma lem283178 (Q : nat -> Prop) (P : nat -> Prop) (_6467 : nat) : ((term106 Q P _6467) = (term106 Q P _6467)) = True.
Proof. exact (@lem283177 (term106 Q P _6467)). Qed.
Lemma lem283179 (Q : nat -> Prop) (P : nat -> Prop) (_6467 : nat) : ((term92 P Q _6467) = (term106 Q P _6467)) = True.
Proof. exact (TRANS (@lem283174 Q P _6467) (@lem283178 Q P _6467)). Qed.
Lemma lem283180 (Q : nat -> Prop) (P : nat -> Prop) (_6467 : nat) : True = ((term92 P Q _6467) = (term106 Q P _6467)).
Proof. exact (SYM (@lem283179 Q P _6467)). Qed.
Lemma lem283181 (Q : nat -> Prop) (P : nat -> Prop) (_6467 : nat) : (term92 P Q _6467) = (term106 Q P _6467).
Proof. exact (EQ_MP (@lem283180 Q P _6467) (@lem0)). Qed.
Lemma lem283182 (_6467 : nat) (P : nat -> Prop) (Q : nat -> Prop) (h1 : term67 P Q) : term106 Q P _6467.
Proof. exact (EQ_MP (@lem283181 Q P _6467) (@lem283142 _6467 P Q h1)). Qed.
Lemma lem283184 (b : Prop) (a : Prop) : (a \/ b) = (term52 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem283185 (P : nat -> Prop) (Q : nat -> Prop) (_6467 : nat) : (term106 Q P _6467) = (term109 P Q _6467).
Proof. exact (@lem283184 (term100 P _6467) (Q _6467)). Qed.
Lemma lem283187 (a : Prop) : (term54 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem283188 (P : nat -> Prop) (_6467 : nat) : (term110 P _6467) = (P _6467).
Proof. exact (@lem283187 (P _6467)). Qed.
Lemma lem283189 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem283190 (P : nat -> Prop) (_6467 : nat) : (term111 P _6467) = (term112 P _6467).
Proof. exact (MK_COMB (@lem283189) (@lem283188 P _6467)). Qed.
Lemma lem283191 (Q : nat -> Prop) (_6467 : nat) : (Q _6467) = (Q _6467).
Proof. exact (eq_refl (Q _6467)). Qed.
Lemma lem283192 (P : nat -> Prop) (Q : nat -> Prop) (_6467 : nat) : (term109 P Q _6467) = (term90 P Q _6467).
Proof. exact (MK_COMB (@lem283190 P _6467) (@lem283191 Q _6467)). Qed.
Lemma lem283193 (P : nat -> Prop) (Q : nat -> Prop) (_6467 : nat) : (term106 Q P _6467) = (term90 P Q _6467).
Proof. exact (TRANS (@lem283185 P Q _6467) (@lem283192 P Q _6467)). Qed.
Lemma lem283196 (_6467 : nat) (P : nat -> Prop) (Q : nat -> Prop) (h1 : term67 P Q) : term90 P Q _6467.
Proof. exact (EQ_MP (@lem283193 P Q _6467) (@lem283182 _6467 P Q h1)). Qed.
Lemma lem283197 (n : nat) (P : nat -> Prop) (Q : nat -> Prop) (h1 : term67 P Q) : term90 P Q n.
Proof. exact (@lem283196 n P Q h1). Qed.
Lemma lem283200 (Q : nat -> Prop) (P : nat -> Prop) (n : nat) (h1 : term67 P Q) (h2 : P n) : Q n.
Proof. exact (@lem283197 n P Q h1 (@lem283153 P n h2)). Qed.
Lemma lem283201 (Q : nat -> Prop) (P : nat -> Prop) (n : nat) (h1 : term67 P Q) (h2 : P n) : term105 Q n.
Proof. exact (fun h0 : term100 Q n => @lem283200 Q P n h1 h2). Qed.
Lemma lem283203 (p : Prop) : (term48 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem283204 (Q : nat -> Prop) (n : nat) : (term105 Q n) = (Q n).
Proof. exact (@lem283203 (Q n)). Qed.
Lemma lem283205 (Q : nat -> Prop) (P : nat -> Prop) (n : nat) (h1 : term67 P Q) (h2 : P n) : Q n.
Proof. exact (EQ_MP (@lem283204 Q n) (@lem283201 Q P n h1 h2)). Qed.
Lemma lem283208 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem283210 (Q : nat -> Prop) (_6468 : nat) : (term100 Q _6468) = (term113 Q _6468).
Proof. exact (@lem283208 (Q _6468)). Qed.
Lemma lem283213 (_6468 : nat) (Q : nat -> Prop) (h1 : term70 Q) : term113 Q _6468.
Proof. exact (EQ_MP (@lem283210 Q _6468) (@lem283144 _6468 Q h1)). Qed.
Lemma lem283214 (n : nat) (Q : nat -> Prop) (h1 : term70 Q) : term113 Q n.
Proof. exact (@lem283213 n Q h1). Qed.
Lemma lem283217 (Q : nat -> Prop) (P : nat -> Prop) (n : nat) (h1 : term67 P Q) (h2 : term70 Q) (h3 : P n) : False.
Proof. exact (@lem283214 n Q h2 (@lem283205 Q P n h1 h3)). Qed.
Lemma lem283218 (Q : nat -> Prop) (P : nat -> Prop) (n : nat) (h1 : term67 P Q) (h2 : term70 Q) (h3 : P n) : term61.
Proof. exact (fun h0 : ~ False => @lem283217 Q P n h1 h2 h3). Qed.
Lemma lem283220 (p : Prop) : (term48 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem283221 : term61 = False.
Proof. exact (@lem283220 False). Qed.
Lemma lem283222 (Q : nat -> Prop) (P : nat -> Prop) (n : nat) (h1 : term67 P Q) (h2 : term70 Q) (h3 : P n) : False.
Proof. exact (EQ_MP (@lem283221) (@lem283218 Q P n h1 h2 h3)). Qed.
Lemma lem283223 (Q : nat -> Prop) (P : nat -> Prop) (n : nat) (h1 : term67 P Q) (h2 : term70 Q) (h3 : P n) : (P n) = False.
Proof. exact (prop_ext (fun h4 : P n => @lem283222 Q P n h1 h2 h3) (fun h4 : False => @lem283146 P n h3)). Qed.
Lemma lem283224 (Q : nat -> Prop) (P : nat -> Prop) (n : nat) (h1 : term67 P Q) (h2 : term70 Q) (h3 : P n) : False.
Proof. exact (EQ_MP (@lem283223 Q P n h1 h2 h3) (@lem283146 P n h3)). Qed.
Lemma lem283225 (Q : nat -> Prop) (P : nat -> Prop) (n : nat) (h1 : term67 P Q) (h2 : term70 Q) (h3 : P n) : (P n) = False.
Proof. exact (prop_ext (fun h4 : P n => @lem283224 Q P n h1 h2 h3) (fun h4 : False => @lem283130 P n h3)). Qed.
Lemma lem283226 (Q : nat -> Prop) (P : nat -> Prop) (n : nat) (h1 : term67 P Q) (h2 : term70 Q) (h3 : P n) : False.
Proof. exact (EQ_MP (@lem283225 Q P n h1 h2 h3) (@lem283130 P n h3)). Qed.
Lemma lem283227 (Q : nat -> Prop) (P : nat -> Prop) (n : nat) (h1 : term67 P Q) (h2 : term70 Q) (h3 : P n) : (P n) = False.
Proof. exact (prop_ext (fun h4 : P n => @lem283226 Q P n h1 h2 h3) (fun h4 : False => @lem283130 P n h3)). Qed.
Lemma lem283228 (Q : nat -> Prop) (P : nat -> Prop) (n : nat) (h1 : term67 P Q) (h2 : term70 Q) (h3 : P n) : False.
Proof. exact (EQ_MP (@lem283227 Q P n h1 h2 h3) (@lem283130 P n h3)). Qed.
Lemma lem283229 (Q : nat -> Prop) (P : nat -> Prop) (n : nat) (h1 : term67 P Q) (h2 : term70 Q) (h3 : P n) : (P n) = False.
Proof. exact (prop_ext (fun h4 : P n => @lem283228 Q P n h1 h2 h3) (fun h4 : False => @lem283106 P n h3)). Qed.
Lemma lem283230 (Q : nat -> Prop) (P : nat -> Prop) (n : nat) (h1 : term67 P Q) (h2 : term70 Q) (h3 : P n) : False.
Proof. exact (EQ_MP (@lem283229 Q P n h1 h2 h3) (@lem283106 P n h3)). Qed.
Lemma lem283231 (P : nat -> Prop) (Q : nat -> Prop) (h1 : term67 P Q) (h2 : term68 P) (h3 : term70 Q) : False.
Proof. exact (ex_elim (@lem283010 P h2) (fun n : nat => fun h0 : term89 P n => @lem283230 Q P n h1 h3 h0)). Qed.
Lemma lem283232 (P : nat -> Prop) (Q : nat -> Prop) (h1 : term67 P Q) (h2 : term68 P) (h3 : term70 Q) : (term68 P) = False.
Proof. exact (prop_ext (fun h4 : term68 P => @lem283231 P Q h1 h2 h3) (fun h4 : False => @lem283010 P h2)). Qed.
Lemma lem283233 (P : nat -> Prop) (Q : nat -> Prop) (h1 : term67 P Q) (h2 : term68 P) (h3 : term70 Q) : False.
Proof. exact (EQ_MP (@lem283232 P Q h1 h2 h3) (@lem283010 P h2)). Qed.
Lemma lem283234 (P : nat -> Prop) (Q : nat -> Prop) (h1 : term67 P Q) (h2 : term68 P) (h3 : term70 Q) : (term70 Q) = False.
Proof. exact (prop_ext (fun h4 : term70 Q => @lem283233 P Q h1 h2 h3) (fun h4 : False => @lem282997 Q h3)). Qed.
Lemma lem283235 (P : nat -> Prop) (Q : nat -> Prop) (h1 : term67 P Q) (h2 : term68 P) (h3 : term70 Q) : False.
Proof. exact (EQ_MP (@lem283234 P Q h1 h2 h3) (@lem282997 Q h3)). Qed.
Lemma lem283236 (Q : nat -> Prop) (P : nat -> Prop) (h1 : term67 P Q) (h2 : term68 P) : term69 Q.
Proof. exact (fun h0 : term70 Q => @lem283235 P Q h1 h2 h0). Qed.
Lemma lem283237 (Q : nat -> Prop) (P : nat -> Prop) (h1 : term67 P Q) (h2 : term68 P) : term68 Q.
Proof. exact (EQ_MP (@lem282996 Q) (@lem283236 Q P h1 h2)). Qed.
Lemma lem283238 (Q : nat -> Prop) (P : nat -> Prop) (h1 : term68 P) : term78 P Q.
Proof. exact (fun h0 : term67 P Q => @lem283237 Q P h0 h1). Qed.
Lemma lem283239 (P : nat -> Prop) (Q : nat -> Prop) : term80 P Q.
Proof. exact (fun h0 : term68 P => @lem283238 Q P h0). Qed.
Lemma lem283244 (Q : nat -> Prop) : term84 Q.
Proof. exact (fun P : nat -> Prop => @lem283239 P Q). Qed.
Lemma lem283249 : term88.
Proof. exact (fun Q : nat -> Prop => @lem283244 Q). Qed.
Lemma lem283250 : term87.
Proof. exact (EQ_MP (@lem282990) (@lem283249)). Qed.
Lemma lem283251 (Q : nat -> Prop) : term114 Q.
Proof. exact (@lem283250 Q). Qed.
Lemma lem283252 (Q : nat -> Prop) : (term114 Q) = (term83 Q).
Proof. exact (eq_refl (term114 Q)). Qed.
Lemma lem283253 (Q : nat -> Prop) : term83 Q.
Proof. exact (EQ_MP (@lem283252 Q) (@lem283251 Q)). Qed.
Lemma lem283254 (Q : nat -> Prop) (P : nat -> Prop) : term115 Q P.
Proof. exact (@lem283253 Q P). Qed.
Lemma lem283255 (P : nat -> Prop) (Q : nat -> Prop) : (term115 Q P) = (term71 P Q).
Proof. exact (eq_refl (term115 Q P)). Qed.
Lemma lem283256 (P : nat -> Prop) (Q : nat -> Prop) : term71 P Q.
Proof. exact (EQ_MP (@lem283255 P Q) (@lem283254 Q P)). Qed.
Lemma lem283258 (P : nat -> Prop) (Q : nat -> Prop) : term71 P Q.
Proof. exact (@lem282863 P Q (@lem283256 P Q)). Qed.
Lemma lem283259 (Q : nat -> Prop) (P : nat -> Prop) (h1 : term68 P) : term77 P Q.
Proof. exact (@lem283258 P Q (@lem282842 P h1)). Qed.
Lemma lem283260 (Q : nat -> Prop) (P : nat -> Prop) (h1 : term67 P Q) (h2 : term68 P) : term69 Q.
Proof. exact (@lem283259 Q P h2 (@lem282841 P Q h1)). Qed.
Lemma lem283261 (P : nat -> Prop) (Q : nat -> Prop) (h1 : term67 P Q) (h2 : term68 P) (h3 : term70 Q) : False.
Proof. exact (@lem283260 Q P h1 h2 (@lem282848 Q h3)). Qed.
Lemma lem283262 (P : nat -> Prop) (Q : nat -> Prop) (h1 : term67 P Q) (h2 : term68 P) (h3 : term70 Q) : (term70 Q) = False.
Proof. exact (prop_ext (fun h4 : term70 Q => @lem283261 P Q h1 h2 h3) (fun h4 : False => @lem282848 Q h3)). Qed.
Lemma lem283263 (P : nat -> Prop) (Q : nat -> Prop) (h1 : term67 P Q) (h2 : term68 P) (h3 : term70 Q) : False.
Proof. exact (EQ_MP (@lem283262 P Q h1 h2 h3) (@lem282848 Q h3)). Qed.
Lemma lem283264 (Q : nat -> Prop) (P : nat -> Prop) (h1 : term67 P Q) (h2 : term68 P) : term69 Q.
Proof. exact (fun h0 : term70 Q => @lem283263 P Q h1 h2 h0). Qed.
Lemma lem283265 (Q : nat -> Prop) (P : nat -> Prop) (h1 : term67 P Q) (h2 : term68 P) : term68 Q.
Proof. exact (EQ_MP (@lem282847 Q) (@lem283264 Q P h1 h2)). Qed.
Lemma lem283267 (m : nat) (n : nat) : term1 m n.
Proof. exact (@lem282828 m n (@lem282820 m n)). Qed.
Lemma lem283268 (Q : nat -> Prop) (P : nat -> Prop) : term116 Q P.
Proof. exact (@lem283267 (minimal Q) (minimal P)). Qed.
Lemma lem283269 (P : nat -> Prop) : term117 P.
Proof. exact (@lem276690 P). Qed.
Lemma lem283270 (P : nat -> Prop) : (term117 P) = (term118 P).
Proof. exact (eq_refl (term117 P)). Qed.
Lemma lem283271 (P : nat -> Prop) : term118 P.
Proof. exact (EQ_MP (@lem283270 P) (@lem283269 P)). Qed.
Lemma lem283272 (P : nat -> Prop) (n : nat) : term119 P n.
Proof. exact (@lem283271 P n). Qed.
Lemma lem283273 (P : nat -> Prop) (n : nat) : (term119 P n) = (term120 P n).
Proof. exact (eq_refl (term119 P n)). Qed.
Lemma lem283274 (P : nat -> Prop) (n : nat) : term120 P n.
Proof. exact (EQ_MP (@lem283273 P n) (@lem283272 P n)). Qed.
Lemma lem283275 (P : nat -> Prop) (h1 : term68 P) : term68 P.
Proof. exact (h1). Qed.
Lemma lem283276 (n : nat) (P : nat -> Prop) (h1 : term68 P) : (term121 n P) = (term122 P n).
Proof. exact (@lem283274 P n (@lem283275 P h1)). Qed.
Lemma lem283282 (P : nat -> Prop) : (term68 P) = ((term68 P) = True).
Proof. exact (@lem7 (term68 P)). Qed.
Lemma lem283284 (n : nat) (P : nat -> Prop) (Q : nat -> Prop) (h1 : term67 P Q) : term123 P Q n.
Proof. exact (@lem282841 P Q h1 n). Qed.
Lemma lem283285 (P : nat -> Prop) (Q : nat -> Prop) (n : nat) : (term123 P Q n) = (term90 P Q n).
Proof. exact (eq_refl (term123 P Q n)). Qed.
Lemma lem283286 (n : nat) (P : nat -> Prop) (Q : nat -> Prop) (h1 : term67 P Q) : term90 P Q n.
Proof. exact (EQ_MP (@lem283285 P Q n) (@lem283284 n P Q h1)). Qed.
Lemma lem283287 (P : nat -> Prop) (n : nat) (h1 : P n) : P n.
Proof. exact (h1). Qed.
Lemma lem283288 (Q : nat -> Prop) (P : nat -> Prop) (n : nat) (h1 : term67 P Q) (h2 : P n) : Q n.
Proof. exact (@lem283286 n P Q h1 (@lem283287 P n h2)). Qed.
Lemma lem283289 (Q : nat -> Prop) (n : nat) : (Q n) = ((Q n) = True).
Proof. exact (@lem7 (Q n)). Qed.
Lemma lem283290 (Q : nat -> Prop) (P : nat -> Prop) (n : nat) (h1 : term67 P Q) (h2 : P n) : (Q n) = True.
Proof. exact (EQ_MP (@lem283289 Q n) (@lem283288 Q P n h1 h2)). Qed.
Lemma lem283296 (Q : nat -> Prop) : (term68 Q) = ((term68 Q) = True).
Proof. exact (@lem7 (term68 Q)). Qed.
Lemma lem283305 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term124 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem283306 (p : Prop) (q : Prop) (p' : Prop) : term125 p q p'.
Proof. exact (fun q' : Prop => @lem283305 p q p' q'). Qed.
Lemma lem283307 (p : Prop) (q : Prop) : term126 p q.
Proof. exact (fun p' : Prop => @lem283306 p q p'). Qed.
Lemma lem283308 (Q : nat -> Prop) (p : nat) (P : nat -> Prop) : term127 Q p P.
Proof. exact (@lem283307 (term121 p Q) (term121 p P)). Qed.
Lemma lem283309 (Q : nat -> Prop) (p : nat) (P : nat -> Prop) (p' : Prop) : term128 Q p P p'.
Proof. exact (@lem283308 Q p P p'). Qed.
Lemma lem283310 (Q : nat -> Prop) (p : nat) (P : nat -> Prop) (p' : Prop) : (term128 Q p P p') = (term129 Q p P p').
Proof. exact (eq_refl (term128 Q p P p')). Qed.
Lemma lem283311 (Q : nat -> Prop) (p : nat) (P : nat -> Prop) (p' : Prop) : term129 Q p P p'.
Proof. exact (EQ_MP (@lem283310 Q p P p') (@lem283309 Q p P p')). Qed.
Lemma lem283312 (Q : nat -> Prop) (p : nat) (P : nat -> Prop) (p' : Prop) (q' : Prop) : term130 Q p P p' q'.
Proof. exact (@lem283311 Q p P p' q'). Qed.
Lemma lem283313 (Q : nat -> Prop) (p : nat) (P : nat -> Prop) (p' : Prop) (q' : Prop) : (term130 Q p P p' q') = (term131 Q p P p' q').
Proof. exact (eq_refl (term130 Q p P p' q')). Qed.
Lemma lem283314 (Q : nat -> Prop) (p : nat) (P : nat -> Prop) (p' : Prop) (q' : Prop) : term131 Q p P p' q'.
Proof. exact (EQ_MP (@lem283313 Q p P p' q') (@lem283312 Q p P p' q')). Qed.
Lemma lem283316 (P : nat -> Prop) (n : nat) : term120 P n.
Proof. exact (fun h0 : term68 P => @lem283276 n P h0). Qed.
Lemma lem283317 (Q : nat -> Prop) (p : nat) : term120 Q p.
Proof. exact (@lem283316 Q p). Qed.
Lemma lem283319 (Q : nat -> Prop) (h1 : term68 Q) : (term68 Q) = True.
Proof. exact (EQ_MP (@lem283296 Q) (@lem282843 Q h1)). Qed.
Lemma lem283320 (Q : nat -> Prop) (h1 : term68 Q) : True = (term68 Q).
Proof. exact (SYM (@lem283319 Q h1)). Qed.
Lemma lem283321 (Q : nat -> Prop) (h1 : term68 Q) : term68 Q.
Proof. exact (EQ_MP (@lem283320 Q h1) (@lem0)). Qed.
Lemma lem283322 (p : nat) (Q : nat -> Prop) (h1 : term68 Q) : (term121 p Q) = (term122 Q p).
Proof. exact (@lem283317 Q p (@lem283321 Q h1)). Qed.
Lemma lem283360 (P : nat -> Prop) (Q : nat -> Prop) (p : nat) (q' : Prop) : term132 P Q p q'.
Proof. exact (@lem283314 Q p P (term122 Q p) q'). Qed.
Lemma lem283361 (P : nat -> Prop) (p : nat) (q' : Prop) (Q : nat -> Prop) (h1 : term68 Q) : term133 P Q p q'.
Proof. exact (@lem283360 P Q p q' (@lem283322 p Q h1)). Qed.
Lemma lem283362 (Q : nat -> Prop) (p : nat) (h1 : term122 Q p) : term122 Q p.
Proof. exact (h1). Qed.
Lemma lem283363 (i : nat) (Q : nat -> Prop) (p : nat) (h1 : term122 Q p) : term134 Q p i.
Proof. exact (@lem283362 Q p h1 i). Qed.
Lemma lem283364 (Q : nat -> Prop) (p : nat) (i : nat) : (term134 Q p i) = (term135 Q p i).
Proof. exact (eq_refl (term134 Q p i)). Qed.
Lemma lem283365 (i : nat) (Q : nat -> Prop) (p : nat) (h1 : term122 Q p) : term135 Q p i.
Proof. exact (EQ_MP (@lem283364 Q p i) (@lem283363 i Q p h1)). Qed.
Lemma lem283366 (Q : nat -> Prop) (i : nat) (h1 : Q i) : Q i.
Proof. exact (h1). Qed.
Lemma lem283367 (p : nat) (Q : nat -> Prop) (i : nat) (h1 : term122 Q p) (h2 : Q i) : Peano.le p i.
Proof. exact (@lem283365 i Q p h1 (@lem283366 Q i h2)). Qed.
Lemma lem283368 (p : nat) (i : nat) : (Peano.le p i) = ((Peano.le p i) = True).
Proof. exact (@lem7 (Peano.le p i)). Qed.
Lemma lem283369 (p : nat) (Q : nat -> Prop) (i : nat) (h1 : term122 Q p) (h2 : Q i) : (Peano.le p i) = True.
Proof. exact (EQ_MP (@lem283368 p i) (@lem283367 p Q i h1 h2)). Qed.
Lemma lem283386 (P : nat -> Prop) (n : nat) : term120 P n.
Proof. exact (fun h0 : term68 P => @lem283276 n P h0). Qed.
Lemma lem283387 (P : nat -> Prop) (p : nat) : term120 P p.
Proof. exact (@lem283386 P p). Qed.
Lemma lem283389 (P : nat -> Prop) (h1 : term68 P) : (term68 P) = True.
Proof. exact (EQ_MP (@lem283282 P) (@lem282842 P h1)). Qed.
Lemma lem283390 (P : nat -> Prop) (h1 : term68 P) : True = (term68 P).
Proof. exact (SYM (@lem283389 P h1)). Qed.
Lemma lem283391 (P : nat -> Prop) (h1 : term68 P) : term68 P.
Proof. exact (EQ_MP (@lem283390 P h1) (@lem0)). Qed.
Lemma lem283392 (p : nat) (P : nat -> Prop) (h1 : term68 P) : (term121 p P) = (term122 P p).
Proof. exact (@lem283387 P p (@lem283391 P h1)). Qed.
Lemma lem283400 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term124 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem283401 (p : Prop) (q : Prop) (p' : Prop) : term125 p q p'.
Proof. exact (fun q' : Prop => @lem283400 p q p' q'). Qed.
Lemma lem283402 (p : Prop) (q : Prop) : term126 p q.
Proof. exact (fun p' : Prop => @lem283401 p q p'). Qed.
Lemma lem283403 (P : nat -> Prop) (p : nat) (i : nat) : term136 P p i.
Proof. exact (@lem283402 (P i) (Peano.le p i)). Qed.
Lemma lem283404 (P : nat -> Prop) (p : nat) (i : nat) (p' : Prop) : term137 P p i p'.
Proof. exact (@lem283403 P p i p'). Qed.
Lemma lem283405 (P : nat -> Prop) (p : nat) (i : nat) (p' : Prop) : (term137 P p i p') = (term138 P p i p').
Proof. exact (eq_refl (term137 P p i p')). Qed.
Lemma lem283406 (P : nat -> Prop) (p : nat) (i : nat) (p' : Prop) : term138 P p i p'.
Proof. exact (EQ_MP (@lem283405 P p i p') (@lem283404 P p i p')). Qed.
Lemma lem283407 (P : nat -> Prop) (p : nat) (i : nat) (p' : Prop) (q' : Prop) : term139 P p i p' q'.
Proof. exact (@lem283406 P p i p' q'). Qed.
Lemma lem283408 (P : nat -> Prop) (p : nat) (i : nat) (p' : Prop) (q' : Prop) : (term139 P p i p' q') = (term140 P p i p' q').
Proof. exact (eq_refl (term139 P p i p' q')). Qed.
Lemma lem283409 (P : nat -> Prop) (p : nat) (i : nat) (p' : Prop) (q' : Prop) : term140 P p i p' q'.
Proof. exact (EQ_MP (@lem283408 P p i p' q') (@lem283407 P p i p' q')). Qed.
Lemma lem283410 (P : nat -> Prop) (i : nat) : (P i) = (P i).
Proof. exact (eq_refl (P i)). Qed.
Lemma lem283411 (p : nat) (P : nat -> Prop) (i : nat) (q' : Prop) : term141 p P i q'.
Proof. exact (@lem283409 P p i (P i) q'). Qed.
Lemma lem283412 (p : nat) (P : nat -> Prop) (i : nat) (q' : Prop) : term142 p P i q'.
Proof. exact (@lem283411 p P i q' (@lem283410 P i)). Qed.
Lemma lem283413 (P : nat -> Prop) (i : nat) (h1 : P i) : P i.
Proof. exact (h1). Qed.
Lemma lem283414 (P : nat -> Prop) (i : nat) : (P i) = ((P i) = True).
Proof. exact (@lem7 (P i)). Qed.
Lemma lem283417 (i : nat) (Q : nat -> Prop) (p : nat) (h1 : term122 Q p) : term143 Q p i.
Proof. exact (fun h0 : Q i => @lem283369 p Q i h1 h0). Qed.
Lemma lem283419 (n : nat) (P : nat -> Prop) (Q : nat -> Prop) (h1 : term67 P Q) : term144 P Q n.
Proof. exact (fun h0 : P n => @lem283290 Q P n h1 h0). Qed.
Lemma lem283420 (i : nat) (P : nat -> Prop) (Q : nat -> Prop) (h1 : term67 P Q) : term144 P Q i.
Proof. exact (@lem283419 i P Q h1). Qed.
Lemma lem283422 (P : nat -> Prop) (i : nat) (h1 : P i) : (P i) = True.
Proof. exact (EQ_MP (@lem283414 P i) (@lem283413 P i h1)). Qed.
Lemma lem283423 (P : nat -> Prop) (i : nat) (h1 : P i) : True = (P i).
Proof. exact (SYM (@lem283422 P i h1)). Qed.
Lemma lem283424 (P : nat -> Prop) (i : nat) (h1 : P i) : P i.
Proof. exact (EQ_MP (@lem283423 P i h1) (@lem0)). Qed.
Lemma lem283425 (Q : nat -> Prop) (P : nat -> Prop) (i : nat) (h1 : term67 P Q) (h2 : P i) : (Q i) = True.
Proof. exact (@lem283420 i P Q h1 (@lem283424 P i h2)). Qed.
Lemma lem283426 (Q : nat -> Prop) (P : nat -> Prop) (i : nat) (h1 : term67 P Q) (h2 : P i) : True = (Q i).
Proof. exact (SYM (@lem283425 Q P i h1 h2)). Qed.
Lemma lem283427 (Q : nat -> Prop) (P : nat -> Prop) (i : nat) (h1 : term67 P Q) (h2 : P i) : Q i.
Proof. exact (EQ_MP (@lem283426 Q P i h1 h2) (@lem0)). Qed.
Lemma lem283428 (Q : nat -> Prop) (p : nat) (P : nat -> Prop) (i : nat) (h1 : term67 P Q) (h2 : term122 Q p) (h3 : P i) : (Peano.le p i) = True.
Proof. exact (@lem283417 i Q p h2 (@lem283427 Q P i h1 h3)). Qed.
Lemma lem283429 (i : nat) (P : nat -> Prop) (Q : nat -> Prop) (p : nat) (h1 : term67 P Q) (h2 : term122 Q p) : term143 P p i.
Proof. exact (fun h0 : P i => @lem283428 Q p P i h1 h2 h0). Qed.
Lemma lem283430 (p : nat) (P : nat -> Prop) (i : nat) : term145 p P i.
Proof. exact (@lem283412 p P i True). Qed.
Lemma lem283431 (i : nat) (P : nat -> Prop) (Q : nat -> Prop) (p : nat) (h1 : term67 P Q) (h2 : term122 Q p) : (term135 P p i) = (term146 P i).
Proof. exact (@lem283430 p P i (@lem283429 i P Q p h1 h2)). Qed.
Lemma lem283433 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem283434 (P : nat -> Prop) (i : nat) : (term146 P i) = True.
Proof. exact (@lem283433 (P i)). Qed.
Lemma lem283435 (i : nat) (P : nat -> Prop) (Q : nat -> Prop) (p : nat) (h1 : term67 P Q) (h2 : term122 Q p) : (term135 P p i) = True.
Proof. exact (TRANS (@lem283431 i P Q p h1 h2) (@lem283434 P i)). Qed.
Lemma lem283436 (P : nat -> Prop) (Q : nat -> Prop) (p : nat) (h1 : term67 P Q) (h2 : term122 Q p) : (term147 P p) = term148.
Proof. exact (fun_ext (fun i : nat => @lem283435 i P Q p h1 h2)). Qed.
Lemma lem283437 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem283438 (P : nat -> Prop) (Q : nat -> Prop) (p : nat) (h1 : term67 P Q) (h2 : term122 Q p) : (term122 P p) = term149.
Proof. exact (MK_COMB (@lem283437) (@lem283436 P Q p h1 h2)). Qed.
Lemma lem283440 {A : Type'} (t : Prop) : (term150 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem283441 (t : Prop) : (term151 t) = t.
Proof. exact (@lem283440 nat t). Qed.
Lemma lem283442 : term149 = True.
Proof. exact (@lem283441 True). Qed.
Lemma lem283443 (P : nat -> Prop) (Q : nat -> Prop) (p : nat) (h1 : term67 P Q) (h2 : term122 Q p) : (term122 P p) = True.
Proof. exact (TRANS (@lem283438 P Q p h1 h2) (@lem283442)). Qed.
Lemma lem283444 (Q : nat -> Prop) (p : nat) (P : nat -> Prop) (h1 : term67 P Q) (h2 : term122 Q p) (h3 : term68 P) : (term121 p P) = True.
Proof. exact (TRANS (@lem283392 p P h3) (@lem283443 P Q p h1 h2)). Qed.
Lemma lem283445 (p : nat) (Q : nat -> Prop) (P : nat -> Prop) (h1 : term67 P Q) (h2 : term68 P) : term152 Q p P.
Proof. exact (fun h0 : term122 Q p => @lem283444 Q p P h1 h0 h2). Qed.
Lemma lem283446 (P : nat -> Prop) (p : nat) (Q : nat -> Prop) (h1 : term68 Q) : term153 P Q p.
Proof. exact (@lem283361 P p True Q h1). Qed.
Lemma lem283447 (p : nat) (P : nat -> Prop) (Q : nat -> Prop) (h1 : term67 P Q) (h2 : term68 P) (h3 : term68 Q) : (term154 Q p P) = (term155 Q p).
Proof. exact (@lem283446 P p Q h3 (@lem283445 p Q P h1 h2)). Qed.
Lemma lem283449 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem283450 (Q : nat -> Prop) (p : nat) : (term155 Q p) = True.
Proof. exact (@lem283449 (term122 Q p)). Qed.
Lemma lem283451 (p : nat) (P : nat -> Prop) (Q : nat -> Prop) (h1 : term67 P Q) (h2 : term68 P) (h3 : term68 Q) : (term154 Q p P) = True.
Proof. exact (TRANS (@lem283447 p P Q h1 h2 h3) (@lem283450 Q p)). Qed.
Lemma lem283452 (P : nat -> Prop) (Q : nat -> Prop) (h1 : term67 P Q) (h2 : term68 P) (h3 : term68 Q) : (term156 Q P) = term148.
Proof. exact (fun_ext (fun p : nat => @lem283451 p P Q h1 h2 h3)). Qed.
Lemma lem283453 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem283454 (P : nat -> Prop) (Q : nat -> Prop) (h1 : term67 P Q) (h2 : term68 P) (h3 : term68 Q) : (term157 Q P) = term149.
Proof. exact (MK_COMB (@lem283453) (@lem283452 P Q h1 h2 h3)). Qed.
Lemma lem283456 {A : Type'} (t : Prop) : (term150 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem283457 (t : Prop) : (term151 t) = t.
Proof. exact (@lem283456 nat t). Qed.
Lemma lem283458 : term149 = True.
Proof. exact (@lem283457 True). Qed.
Lemma lem283459 (P : nat -> Prop) (Q : nat -> Prop) (h1 : term67 P Q) (h2 : term68 P) (h3 : term68 Q) : (term157 Q P) = True.
Proof. exact (TRANS (@lem283454 P Q h1 h2 h3) (@lem283458)). Qed.
Lemma lem283460 (P : nat -> Prop) (Q : nat -> Prop) (h1 : term67 P Q) (h2 : term68 P) (h3 : term68 Q) : True = (term157 Q P).
Proof. exact (SYM (@lem283459 P Q h1 h2 h3)). Qed.
Lemma lem283461 (P : nat -> Prop) (Q : nat -> Prop) (h1 : term67 P Q) (h2 : term68 P) (h3 : term68 Q) : term157 Q P.
Proof. exact (EQ_MP (@lem283460 P Q h1 h2 h3) (@lem0)). Qed.
Lemma lem283462 (P : nat -> Prop) (Q : nat -> Prop) (h1 : term67 P Q) (h2 : term68 P) (h3 : term68 Q) : term158 Q P.
Proof. exact (@lem283268 Q P (@lem283461 P Q h1 h2 h3)). Qed.
Lemma lem283463 (P : nat -> Prop) (Q : nat -> Prop) (h1 : term67 P Q) (h2 : term68 P) (h3 : term68 Q) : (term68 Q) = (term158 Q P).
Proof. exact (prop_ext (fun h4 : term68 Q => @lem283462 P Q h1 h2 h3) (fun h4 : term158 Q P => @lem282843 Q h3)). Qed.
Lemma lem283464 (P : nat -> Prop) (Q : nat -> Prop) (h1 : term67 P Q) (h2 : term68 P) (h3 : term68 Q) : term158 Q P.
Proof. exact (EQ_MP (@lem283463 P Q h1 h2 h3) (@lem282843 Q h3)). Qed.
Lemma lem283465 (Q : nat -> Prop) (P : nat -> Prop) (h1 : term67 P Q) (h2 : term68 P) : (term68 Q) = (term158 Q P).
Proof. exact (prop_ext (fun h3 : term68 Q => @lem283464 P Q h1 h2 h3) (fun h3 : term158 Q P => @lem283265 Q P h1 h2)). Qed.
Lemma lem283466 (Q : nat -> Prop) (P : nat -> Prop) (h1 : term67 P Q) (h2 : term68 P) : term158 Q P.
Proof. exact (EQ_MP (@lem283465 Q P h1 h2) (@lem283265 Q P h1 h2)). Qed.
Lemma lem283467 (P : nat -> Prop) (Q : nat -> Prop) (h1 : term66 P Q) : term67 P Q.
Proof. exact (proj2 (@lem282840 P Q h1)). Qed.
Lemma lem283468 (P : nat -> Prop) (Q : nat -> Prop) (h1 : term66 P Q) : term68 P.
Proof. exact (proj1 (@lem282840 P Q h1)). Qed.
Lemma lem283469 (Q : nat -> Prop) (P : nat -> Prop) (h1 : term67 P Q) (h2 : term68 P) : (term67 P Q) = (term158 Q P).
Proof. exact (prop_ext (fun h3 : term67 P Q => @lem283466 Q P h1 h2) (fun h3 : term158 Q P => @lem282841 P Q h1)). Qed.
Lemma lem283470 (Q : nat -> Prop) (P : nat -> Prop) (h1 : term67 P Q) (h2 : term68 P) : term158 Q P.
Proof. exact (EQ_MP (@lem283469 Q P h1 h2) (@lem282841 P Q h1)). Qed.
Lemma lem283471 (Q : nat -> Prop) (P : nat -> Prop) (h1 : term67 P Q) (h2 : term68 P) : (term68 P) = (term158 Q P).
Proof. exact (prop_ext (fun h3 : term68 P => @lem283470 Q P h1 h2) (fun h3 : term158 Q P => @lem282842 P h2)). Qed.
Lemma lem283472 (Q : nat -> Prop) (P : nat -> Prop) (h1 : term67 P Q) (h2 : term68 P) : term158 Q P.
Proof. exact (EQ_MP (@lem283471 Q P h1 h2) (@lem282842 P h2)). Qed.
Lemma lem283473 (P : nat -> Prop) (Q : nat -> Prop) (h1 : term68 P) (h2 : term66 P Q) : (term67 P Q) = (term158 Q P).
Proof. exact (prop_ext (fun h3 : term67 P Q => @lem283472 Q P h3 h1) (fun h3 : term158 Q P => @lem283467 P Q h2)). Qed.
Lemma lem283474 (P : nat -> Prop) (Q : nat -> Prop) (h1 : term68 P) (h2 : term66 P Q) : term158 Q P.
Proof. exact (EQ_MP (@lem283473 P Q h1 h2) (@lem283467 P Q h2)). Qed.
Lemma lem283475 (P : nat -> Prop) (Q : nat -> Prop) (h1 : term66 P Q) : (term68 P) = (term158 Q P).
Proof. exact (prop_ext (fun h2 : term68 P => @lem283474 P Q h2 h1) (fun h2 : term158 Q P => @lem283468 P Q h1)). Qed.
Lemma lem283476 (P : nat -> Prop) (Q : nat -> Prop) (h1 : term66 P Q) : term158 Q P.
Proof. exact (EQ_MP (@lem283475 P Q h1) (@lem283468 P Q h1)). Qed.
Lemma lem283477 (Q : nat -> Prop) (P : nat -> Prop) : term159 Q P.
Proof. exact (fun h0 : term66 P Q => @lem283476 P Q h0). Qed.
Lemma lem283482 (P : nat -> Prop) : term160 P.
Proof. exact (fun Q : nat -> Prop => @lem283477 Q P). Qed.
Lemma lem283487 : term161.
Proof. exact (fun P : nat -> Prop => @lem283482 P). Qed.
