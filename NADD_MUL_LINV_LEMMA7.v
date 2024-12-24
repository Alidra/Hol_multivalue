Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NADD_MUL_LINV_LEMMA7_term_abbrevs.
Require Import LE_ADD_spec.
Require Import LE_ADDR_spec.
Require Import LE_MULT2_spec.
Require Import LE_MULT_LCANCEL_spec.
Require Import LE_SUC_LT_spec.
Require Import LE_TRANS_spec.
Require Import MULT_AC_spec.
Require Import NADD_MUL_LINV_LEMMA6_spec.
Require Import NOT_LE_spec.
Require Import REFL_CLAUSE_spec.
Require Import thm0_spec.
Require Import thm10568_spec.
Require Import thm1842_spec.
Require Import thm512818_spec.
Require Import thm513079_spec.
Require Import thm513870_spec.
Require Import thm514290_spec.
Require Import thm514761_spec.
Require Import thm515543_spec.
Require Import thm521920_spec.
Require Import thm522075_spec.
Require Import thm7_spec.
Require Import thm89498_spec.
Lemma lem1304594 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1304595 (m : nat) (h1 : term0) : term1 m.
Proof. exact (@lem1304594 h1 m). Qed.
Lemma lem1304596 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem1304597 (m : nat) (h1 : term0) : term2 m.
Proof. exact (EQ_MP (@lem1304596 m) (@lem1304595 m h1)). Qed.
Lemma lem1304598 (m : nat) (n : nat) (h1 : term0) : term3 m n.
Proof. exact (@lem1304597 m h1 n). Qed.
Lemma lem1304599 (n : nat) (m : nat) : (term3 m n) = (term4 n m).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem1304600 (n : nat) (m : nat) (h1 : term0) : term4 n m.
Proof. exact (EQ_MP (@lem1304599 n m) (@lem1304598 m n h1)). Qed.
Lemma lem1304601 (n : nat) (m : nat) (p : nat) (h1 : term0) : term5 n m p.
Proof. exact (@lem1304600 n m h1 p). Qed.
Lemma lem1304602 (n : nat) (m : nat) (p : nat) : (term5 n m p) = (term6 n m p).
Proof. exact (eq_refl (term5 n m p)). Qed.
Lemma lem1304603 (n : nat) (m : nat) (p : nat) (h1 : term0) : term6 n m p.
Proof. exact (EQ_MP (@lem1304602 n m p) (@lem1304601 n m p h1)). Qed.
Lemma lem1304604 (m : nat) (n : nat) (p : nat) (h1 : term7 m n p) : term7 m n p.
Proof. exact (h1). Qed.
Lemma lem1304605 (m : nat) (n : nat) (p : nat) (h1 : term0) (h2 : term7 m n p) : Peano.le m p.
Proof. exact (@lem1304603 n m p h1 (@lem1304604 m n p h2)). Qed.
Lemma lem1304606 (m : nat) (n : nat) (p : nat) (h1 : term7 m n p) : term8 m p.
Proof. exact (fun h0 : term0 => @lem1304605 m n p h0 h1). Qed.
Lemma lem1304607 (m : nat) (p : nat) (h1 : term9 m p) : term9 m p.
Proof. exact (h1). Qed.
Lemma lem1304608 (m : nat) (p : nat) (h1 : term9 m p) : term8 m p.
Proof. exact (ex_elim (@lem1304607 m p h1) (fun n : nat => fun h0 : term10 m p n => @lem1304606 m n p h0)). Qed.
Lemma lem1304609 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1304610 (m : nat) (p : nat) (h1 : term0) (h2 : term9 m p) : Peano.le m p.
Proof. exact (@lem1304608 m p h2 (@lem1304609 h1)). Qed.
Lemma lem1304611 (m : nat) (p : nat) (h1 : term0) : term11 m p.
Proof. exact (fun h0 : term9 m p => @lem1304610 m p h1 h0). Qed.
Lemma lem1304612 (m : nat) (h1 : term0) : term12 m.
Proof. exact (fun p : nat => @lem1304611 m p h1). Qed.
Lemma lem1304613 (h1 : term0) : term13.
Proof. exact (fun m : nat => @lem1304612 m h1). Qed.
Lemma lem1304614 : term14.
Proof. exact (fun h0 : term0 => @lem1304613 h0). Qed.
Lemma lem1304615 : term13.
Proof. exact (@lem1304614 (@lem93743)). Qed.
Lemma lem1304616 (m : nat) : term15 m.
Proof. exact (@lem1304615 m). Qed.
Lemma lem1304617 (m : nat) : (term15 m) = (term12 m).
Proof. exact (eq_refl (term15 m)). Qed.
Lemma lem1304618 (m : nat) : term12 m.
Proof. exact (EQ_MP (@lem1304617 m) (@lem1304616 m)). Qed.
Lemma lem1304619 (m : nat) (p : nat) : term16 m p.
Proof. exact (@lem1304618 m p). Qed.
Lemma lem1304620 (m : nat) (p : nat) : (term16 m p) = (term11 m p).
Proof. exact (eq_refl (term16 m p)). Qed.
Lemma lem1304622 (h1 : term17) : term17.
Proof. exact (h1). Qed.
Lemma lem1304623 (m : nat) (h1 : term17) : term18 m.
Proof. exact (@lem1304622 h1 m). Qed.
Lemma lem1304624 (m : nat) : (term18 m) = (term19 m).
Proof. exact (eq_refl (term18 m)). Qed.
Lemma lem1304625 (m : nat) (h1 : term17) : term19 m.
Proof. exact (EQ_MP (@lem1304624 m) (@lem1304623 m h1)). Qed.
Lemma lem1304626 (m : nat) (n : nat) (h1 : term17) : term20 m n.
Proof. exact (@lem1304625 m h1 n). Qed.
Lemma lem1304627 (m : nat) (n : nat) : (term20 m n) = (term21 m n).
Proof. exact (eq_refl (term20 m n)). Qed.
Lemma lem1304628 (m : nat) (n : nat) (h1 : term17) : term21 m n.
Proof. exact (EQ_MP (@lem1304627 m n) (@lem1304626 m n h1)). Qed.
Lemma lem1304629 (m : nat) (n : nat) (p : nat) (h1 : term17) : term22 m n p.
Proof. exact (@lem1304628 m n h1 p). Qed.
Lemma lem1304630 (m : nat) (p : nat) (n : nat) : (term22 m n p) = (term23 m p n).
Proof. exact (eq_refl (term22 m n p)). Qed.
Lemma lem1304631 (m : nat) (p : nat) (n : nat) (h1 : term17) : term23 m p n.
Proof. exact (EQ_MP (@lem1304630 m p n) (@lem1304629 m n p h1)). Qed.
Lemma lem1304632 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term17) : term24 m p n q.
Proof. exact (@lem1304631 m p n h1 q). Qed.
Lemma lem1304633 (m : nat) (p : nat) (n : nat) (q : nat) : (term24 m p n q) = (term25 m p n q).
Proof. exact (eq_refl (term24 m p n q)). Qed.
Lemma lem1304634 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term17) : term25 m p n q.
Proof. exact (EQ_MP (@lem1304633 m p n q) (@lem1304632 m p n q h1)). Qed.
Lemma lem1304635 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term26 m n p q) : term26 m n p q.
Proof. exact (h1). Qed.
Lemma lem1304636 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term17) (h2 : term26 m n p q) : term27 m p n q.
Proof. exact (@lem1304634 m p n q h1 (@lem1304635 m n p q h2)). Qed.
Lemma lem1304637 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term26 m n p q) : term28 m p n q.
Proof. exact (fun h0 : term17 => @lem1304636 m n p q h0 h1). Qed.
Lemma lem1304638 (h1 : term17) : term17.
Proof. exact (h1). Qed.
Lemma lem1304639 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term17) (h2 : term26 m n p q) : term27 m p n q.
Proof. exact (@lem1304637 m n p q h2 (@lem1304638 h1)). Qed.
Lemma lem1304640 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term17) : term25 m p n q.
Proof. exact (fun h0 : term26 m n p q => @lem1304639 m n p q h1 h0). Qed.
Lemma lem1304641 (m : nat) (p : nat) (n : nat) (h1 : term17) : term23 m p n.
Proof. exact (fun q : nat => @lem1304640 m p n q h1). Qed.
Lemma lem1304642 (m : nat) (p : nat) (h1 : term17) : term29 m p.
Proof. exact (fun n : nat => @lem1304641 m p n h1). Qed.
Lemma lem1304643 (m : nat) (h1 : term17) : term30 m.
Proof. exact (fun p : nat => @lem1304642 m p h1). Qed.
Lemma lem1304644 (h1 : term17) : term31.
Proof. exact (fun m : nat => @lem1304643 m h1). Qed.
Lemma lem1304645 : term32.
Proof. exact (fun h0 : term17 => @lem1304644 h0). Qed.
Lemma lem1304646 : term31.
Proof. exact (@lem1304645 (@lem102387)). Qed.
Lemma lem1304647 (m : nat) : term33 m.
Proof. exact (@lem1304646 m). Qed.
Lemma lem1304648 (m : nat) : (term33 m) = (term30 m).
Proof. exact (eq_refl (term33 m)). Qed.
Lemma lem1304649 (m : nat) : term30 m.
Proof. exact (EQ_MP (@lem1304648 m) (@lem1304647 m)). Qed.
Lemma lem1304650 (m : nat) (p : nat) : term34 m p.
Proof. exact (@lem1304649 m p). Qed.
Lemma lem1304651 (m : nat) (p : nat) : (term34 m p) = (term29 m p).
Proof. exact (eq_refl (term34 m p)). Qed.
Lemma lem1304652 (m : nat) (p : nat) : term29 m p.
Proof. exact (EQ_MP (@lem1304651 m p) (@lem1304650 m p)). Qed.
Lemma lem1304653 (m : nat) (p : nat) (n : nat) : term35 m p n.
Proof. exact (@lem1304652 m p n). Qed.
Lemma lem1304654 (m : nat) (p : nat) (n : nat) : (term35 m p n) = (term23 m p n).
Proof. exact (eq_refl (term35 m p n)). Qed.
Lemma lem1304655 (m : nat) (p : nat) (n : nat) : term23 m p n.
Proof. exact (EQ_MP (@lem1304654 m p n) (@lem1304653 m p n)). Qed.
Lemma lem1304656 (m : nat) (p : nat) (n : nat) (q : nat) : term24 m p n q.
Proof. exact (@lem1304655 m p n q). Qed.
Lemma lem1304657 (m : nat) (p : nat) (n : nat) (q : nat) : (term24 m p n q) = (term25 m p n q).
Proof. exact (eq_refl (term24 m p n q)). Qed.
Lemma lem1304992 : term36.
Proof. exact (EQ_MP (@lem521920) (@lem522075)). Qed.
Lemma lem1304993 : term37.
Proof. exact (proj2 (@lem1304992)). Qed.
Lemma lem1304994 : term38.
Proof. exact (proj2 (@lem1304993)). Qed.
Lemma lem1304995 : term39.
Proof. exact (proj2 (@lem1304994)). Qed.
Lemma lem1304996 : term40.
Proof. exact (proj2 (@lem1304995)). Qed.
Lemma lem1304997 : term41.
Proof. exact (proj2 (@lem1304996)). Qed.
Lemma lem1304998 : term42.
Proof. exact (proj2 (@lem1304997)). Qed.
Lemma lem1304999 : term43.
Proof. exact (proj2 (@lem1304998)). Qed.
Lemma lem1305000 : term44.
Proof. exact (proj2 (@lem1304999)). Qed.
Lemma lem1305001 : term45.
Proof. exact (proj2 (@lem1305000)). Qed.
Lemma lem1305002 (m : nat) : term46 m.
Proof. exact (@lem1305001 m). Qed.
Lemma lem1305003 (m : nat) : (term46 m) = (term47 m).
Proof. exact (eq_refl (term46 m)). Qed.
Lemma lem1305004 (m : nat) : term47 m.
Proof. exact (EQ_MP (@lem1305003 m) (@lem1305002 m)). Qed.
Lemma lem1305005 (m : nat) (n : nat) : term48 m n.
Proof. exact (@lem1305004 m n). Qed.
Lemma lem1305006 (m : nat) (n : nat) : (term48 m n) = (((BIT1 m) = (BIT1 n)) = (m = n)).
Proof. exact (eq_refl (term48 m n)). Qed.
Lemma lem1305046 : term49.
Proof. exact (proj1 (@lem1304992)). Qed.
Lemma lem1305047 (m : nat) : term50 m.
Proof. exact (@lem1305046 m). Qed.
Lemma lem1305048 (m : nat) : (term50 m) = (term51 m).
Proof. exact (eq_refl (term50 m)). Qed.
Lemma lem1305049 (m : nat) : term51 m.
Proof. exact (EQ_MP (@lem1305048 m) (@lem1305047 m)). Qed.
Lemma lem1305050 (m : nat) (n : nat) : term52 m n.
Proof. exact (@lem1305049 m n). Qed.
Lemma lem1305051 (m : nat) (n : nat) : (term52 m n) = (((NUMERAL m) = (NUMERAL n)) = (m = n)).
Proof. exact (eq_refl (term52 m n)). Qed.
Lemma lem1305146 : term53.
Proof. exact (EQ_MP (@lem514761) (@lem515543)). Qed.
Lemma lem1305147 : term54.
Proof. exact (proj2 (@lem1305146)). Qed.
Lemma lem1305148 : term55.
Proof. exact (proj2 (@lem1305147)). Qed.
Lemma lem1305149 : term56.
Proof. exact (proj2 (@lem1305148)). Qed.
Lemma lem1305150 : term57.
Proof. exact (proj2 (@lem1305149)). Qed.
Lemma lem1305151 : term58.
Proof. exact (proj2 (@lem1305150)). Qed.
Lemma lem1305152 : term59.
Proof. exact (proj2 (@lem1305151)). Qed.
Lemma lem1305153 : term60.
Proof. exact (proj2 (@lem1305152)). Qed.
Lemma lem1305154 : term61.
Proof. exact (proj2 (@lem1305153)). Qed.
Lemma lem1305155 : term62.
Proof. exact (proj2 (@lem1305154)). Qed.
Lemma lem1305156 (m : nat) : term63 m.
Proof. exact (@lem1305155 m). Qed.
Lemma lem1305157 (m : nat) : (term63 m) = (term64 m).
Proof. exact (eq_refl (term63 m)). Qed.
Lemma lem1305158 (m : nat) : term64 m.
Proof. exact (EQ_MP (@lem1305157 m) (@lem1305156 m)). Qed.
Lemma lem1305159 (m : nat) (n : nat) : term65 m n.
Proof. exact (@lem1305158 m n). Qed.
Lemma lem1305160 (m : nat) (n : nat) : (term65 m n) = ((term66 m n) = (term67 m n)).
Proof. exact (eq_refl (term65 m n)). Qed.
Lemma lem1305200 : term68.
Proof. exact (proj1 (@lem1305146)). Qed.
Lemma lem1305201 (m : nat) : term69 m.
Proof. exact (@lem1305200 m). Qed.
Lemma lem1305202 (m : nat) : (term69 m) = (term70 m).
Proof. exact (eq_refl (term69 m)). Qed.
Lemma lem1305203 (m : nat) : term70 m.
Proof. exact (EQ_MP (@lem1305202 m) (@lem1305201 m)). Qed.
Lemma lem1305204 (m : nat) (n : nat) : term71 m n.
Proof. exact (@lem1305203 m n). Qed.
Lemma lem1305205 (m : nat) (n : nat) : (term71 m n) = ((term72 m n) = (term73 m n)).
Proof. exact (eq_refl (term71 m n)). Qed.
Lemma lem1305207 : term74.
Proof. exact (EQ_MP (@lem513870) (@lem514290)). Qed.
Lemma lem1305208 : term75.
Proof. exact (proj2 (@lem1305207)). Qed.
Lemma lem1305209 : term76.
Proof. exact (proj2 (@lem1305208)). Qed.
Lemma lem1305210 : term77.
Proof. exact (proj2 (@lem1305209)). Qed.
Lemma lem1305211 : term78.
Proof. exact (proj2 (@lem1305210)). Qed.
Lemma lem1305212 : term79.
Proof. exact (proj2 (@lem1305211)). Qed.
Lemma lem1305213 : term80.
Proof. exact (proj2 (@lem1305212)). Qed.
Lemma lem1305237 : term81.
Proof. exact (proj1 (@lem1305213)). Qed.
Lemma lem1305238 (m : nat) : term82 m.
Proof. exact (@lem1305237 m). Qed.
Lemma lem1305239 (m : nat) : (term82 m) = (term83 m).
Proof. exact (eq_refl (term82 m)). Qed.
Lemma lem1305240 (m : nat) : term83 m.
Proof. exact (EQ_MP (@lem1305239 m) (@lem1305238 m)). Qed.
Lemma lem1305241 (m : nat) (n : nat) : term84 m n.
Proof. exact (@lem1305240 m n). Qed.
Lemma lem1305242 (m : nat) (n : nat) : (term84 m n) = ((term85 m n) = (term86 m n)).
Proof. exact (eq_refl (term84 m n)). Qed.
Lemma lem1305244 : term87.
Proof. exact (proj1 (@lem1305212)). Qed.
Lemma lem1305245 (n : nat) : term88 n.
Proof. exact (@lem1305244 n). Qed.
Lemma lem1305246 (n : nat) : (term88 n) = ((term89 n) = (BIT1 n)).
Proof. exact (eq_refl (term88 n)). Qed.
Lemma lem1305256 : term90.
Proof. exact (proj1 (@lem1305209)). Qed.
Lemma lem1305257 (n : nat) : term91 n.
Proof. exact (@lem1305256 n). Qed.
Lemma lem1305258 (n : nat) : (term91 n) = ((term92 n) = (BIT0 n)).
Proof. exact (eq_refl (term91 n)). Qed.
Lemma lem1305284 : term93.
Proof. exact (EQ_MP (@lem513079) (@lem0)). Qed.
Lemma lem1305285 : term94.
Proof. exact (proj2 (@lem1305284)). Qed.
Lemma lem1305296 : term95.
Proof. exact (proj1 (@lem1305284)). Qed.
Lemma lem1305297 (n : nat) : term96 n.
Proof. exact (@lem1305296 n). Qed.
Lemma lem1305298 (n : nat) : (term96 n) = ((term97 n) = (term98 n)).
Proof. exact (eq_refl (term96 n)). Qed.
Lemma lem1305300 : term99.
Proof. exact (EQ_MP (@lem512818) (@lem0)). Qed.
Lemma lem1305306 (n : nat) : (term97 n) = (term98 n).
Proof. exact (EQ_MP (@lem1305298 n) (@lem1305297 n)). Qed.
Lemma lem1305307 : term100 = term101.
Proof. exact (@lem1305306 0). Qed.
Lemma lem1305309 : (S 0) = (BIT1 0).
Proof. exact (proj1 (@lem1305285)). Qed.
Lemma lem1305310 : NUMERAL = NUMERAL.
Proof. exact (eq_refl NUMERAL). Qed.
Lemma lem1305311 : term101 = term102.
Proof. exact (MK_COMB (@lem1305310) (@lem1305309)). Qed.
Lemma lem1305312 : term100 = term102.
Proof. exact (TRANS (@lem1305307) (@lem1305311)). Qed.
Lemma lem1305313 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1305314 : term103 = term104.
Proof. exact (MK_COMB (@lem1305313) (@lem1305312)). Qed.
Lemma lem1305316 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (EQ_MP (@lem1305205 m n) (@lem1305204 m n)). Qed.
Lemma lem1305317 : term105 = term106.
Proof. exact (@lem1305316 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1305319 (m : nat) (n : nat) : (term66 m n) = (term67 m n).
Proof. exact (EQ_MP (@lem1305160 m n) (@lem1305159 m n)). Qed.
Lemma lem1305320 : term107 = term108.
Proof. exact (@lem1305319 0 0). Qed.
Lemma lem1305322 (m : nat) (n : nat) : (term85 m n) = (term86 m n).
Proof. exact (EQ_MP (@lem1305242 m n) (@lem1305241 m n)). Qed.
Lemma lem1305323 : term109 = term110.
Proof. exact (@lem1305322 0 term111). Qed.
Lemma lem1305325 (n : nat) : (term92 n) = (BIT0 n).
Proof. exact (EQ_MP (@lem1305258 n) (@lem1305257 n)). Qed.
Lemma lem1305326 : term112 = term111.
Proof. exact (@lem1305325 (Nat.mul 0 0)). Qed.
Lemma lem1305328 : (Nat.mul 0 0) = 0.
Proof. exact (proj1 (@lem1305147)). Qed.
Lemma lem1305329 : BIT0 = BIT0.
Proof. exact (eq_refl BIT0). Qed.
Lemma lem1305330 : term111 = (BIT0 0).
Proof. exact (MK_COMB (@lem1305329) (@lem1305328)). Qed.
Lemma lem1305332 : (BIT0 0) = 0.
Proof. exact (proj2 (@lem1305300)). Qed.
Lemma lem1305333 : term111 = 0.
Proof. exact (TRANS (@lem1305330) (@lem1305332)). Qed.
Lemma lem1305334 : term112 = 0.
Proof. exact (TRANS (@lem1305326) (@lem1305333)). Qed.
Lemma lem1305335 : BIT0 = BIT0.
Proof. exact (eq_refl BIT0). Qed.
Lemma lem1305336 : term110 = (BIT0 0).
Proof. exact (MK_COMB (@lem1305335) (@lem1305334)). Qed.
Lemma lem1305338 : (BIT0 0) = 0.
Proof. exact (proj2 (@lem1305300)). Qed.
Lemma lem1305339 : term110 = 0.
Proof. exact (TRANS (@lem1305336) (@lem1305338)). Qed.
Lemma lem1305340 : term109 = 0.
Proof. exact (TRANS (@lem1305323) (@lem1305339)). Qed.
Lemma lem1305341 : term113 = term113.
Proof. exact (eq_refl term113). Qed.
Lemma lem1305342 : term108 = term114.
Proof. exact (MK_COMB (@lem1305341) (@lem1305340)). Qed.
Lemma lem1305344 (n : nat) : (term89 n) = (BIT1 n).
Proof. exact (EQ_MP (@lem1305246 n) (@lem1305245 n)). Qed.
Lemma lem1305345 : term114 = (BIT1 0).
Proof. exact (@lem1305344 0). Qed.
Lemma lem1305346 : term108 = (BIT1 0).
Proof. exact (TRANS (@lem1305342) (@lem1305345)). Qed.
Lemma lem1305347 : term107 = (BIT1 0).
Proof. exact (TRANS (@lem1305320) (@lem1305346)). Qed.
Lemma lem1305348 : NUMERAL = NUMERAL.
Proof. exact (eq_refl NUMERAL). Qed.
Lemma lem1305349 : term106 = term102.
Proof. exact (MK_COMB (@lem1305348) (@lem1305347)). Qed.
Lemma lem1305350 : term105 = term102.
Proof. exact (TRANS (@lem1305317) (@lem1305349)). Qed.
Lemma lem1305351 : (term100 = term105) = (term102 = term102).
Proof. exact (MK_COMB (@lem1305314) (@lem1305350)). Qed.
Lemma lem1305353 (m : nat) (n : nat) : ((NUMERAL m) = (NUMERAL n)) = (m = n).
Proof. exact (EQ_MP (@lem1305051 m n) (@lem1305050 m n)). Qed.
Lemma lem1305354 : (term102 = term102) = ((BIT1 0) = (BIT1 0)).
Proof. exact (@lem1305353 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1305356 (m : nat) (n : nat) : ((BIT1 m) = (BIT1 n)) = (m = n).
Proof. exact (EQ_MP (@lem1305006 m n) (@lem1305005 m n)). Qed.
Lemma lem1305357 : ((BIT1 0) = (BIT1 0)) = (0 = 0).
Proof. exact (@lem1305356 0 0). Qed.
Lemma lem1305359 : (0 = 0) = True.
Proof. exact (proj1 (@lem1304993)). Qed.
Lemma lem1305360 : ((BIT1 0) = (BIT1 0)) = True.
Proof. exact (TRANS (@lem1305357) (@lem1305359)). Qed.
Lemma lem1305361 : (term102 = term102) = True.
Proof. exact (TRANS (@lem1305354) (@lem1305360)). Qed.
Lemma lem1305362 : (term100 = term105) = True.
Proof. exact (TRANS (@lem1305351) (@lem1305361)). Qed.
Lemma lem1305363 : True = (term100 = term105).
Proof. exact (SYM (@lem1305362)). Qed.
Lemma lem1305367 (m : nat) (n : nat) (h1 : (term115 m n) = (Peano.lt m n)) : (term115 m n) = (Peano.lt m n).
Proof. exact (h1). Qed.
Lemma lem1305368 (m : nat) (n : nat) (h1 : (term115 m n) = (Peano.lt m n)) : (Peano.lt m n) = (term115 m n).
Proof. exact (SYM (@lem1305367 m n h1)). Qed.
Lemma lem1305369 (m : nat) (n : nat) (h1 : (Peano.lt m n) = (term115 m n)) : (Peano.lt m n) = (term115 m n).
Proof. exact (h1). Qed.
Lemma lem1305370 (m : nat) (n : nat) (h1 : (Peano.lt m n) = (term115 m n)) : (term115 m n) = (Peano.lt m n).
Proof. exact (SYM (@lem1305369 m n h1)). Qed.
Lemma lem1305371 (m : nat) (n : nat) : ((term115 m n) = (Peano.lt m n)) = ((Peano.lt m n) = (term115 m n)).
Proof. exact (prop_ext (fun h1 : (term115 m n) = (Peano.lt m n) => @lem1305368 m n h1) (fun h1 : (Peano.lt m n) = (term115 m n) => @lem1305370 m n h1)). Qed.
Lemma lem1305372 (m : nat) : (term116 m) = (term117 m).
Proof. exact (fun_ext (fun n : nat => @lem1305371 m n)). Qed.
Lemma lem1305373 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1305374 (m : nat) : (term118 m) = (term119 m).
Proof. exact (MK_COMB (@lem1305373) (@lem1305372 m)). Qed.
Lemma lem1305375 : term120 = term121.
Proof. exact (fun_ext (fun m : nat => @lem1305374 m)). Qed.
Lemma lem1305376 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1305377 : term122 = term123.
Proof. exact (MK_COMB (@lem1305376) (@lem1305375)). Qed.
Lemma lem1305378 : term123.
Proof. exact (EQ_MP (@lem1305377) (@lem91144)). Qed.
Lemma lem1305379 (m : nat) : term124 m.
Proof. exact (@lem1305378 m). Qed.
Lemma lem1305380 (m : nat) : (term124 m) = (term119 m).
Proof. exact (eq_refl (term124 m)). Qed.
Lemma lem1305381 (m : nat) : term119 m.
Proof. exact (EQ_MP (@lem1305380 m) (@lem1305379 m)). Qed.
Lemma lem1305382 (m : nat) (n : nat) : term125 m n.
Proof. exact (@lem1305381 m n). Qed.
Lemma lem1305383 (m : nat) (n : nat) : (term125 m n) = ((Peano.lt m n) = (term115 m n)).
Proof. exact (eq_refl (term125 m n)). Qed.
Lemma lem1305385 (m : nat) : term126 m.
Proof. exact (@lem97961 m). Qed.
Lemma lem1305386 (m : nat) : (term126 m) = (term127 m).
Proof. exact (eq_refl (term126 m)). Qed.
Lemma lem1305387 (m : nat) : term127 m.
Proof. exact (EQ_MP (@lem1305386 m) (@lem1305385 m)). Qed.
Lemma lem1305388 (m : nat) (n : nat) : term128 m n.
Proof. exact (@lem1305387 m n). Qed.
Lemma lem1305389 (n : nat) (m : nat) : (term128 m n) = ((term129 m n) = (Peano.lt n m)).
Proof. exact (eq_refl (term128 m n)). Qed.
Lemma lem1305391 : term130.
Proof. exact (proj1 (@lem89498)). Qed.
Lemma lem1305393 (m : nat) (h1 : (term131 m) = (m = (NUMERAL 0))) : (term131 m) = (m = (NUMERAL 0)).
Proof. exact (h1). Qed.
Lemma lem1305394 (m : nat) (h1 : (term131 m) = (m = (NUMERAL 0))) : (m = (NUMERAL 0)) = (term131 m).
Proof. exact (SYM (@lem1305393 m h1)). Qed.
Lemma lem1305395 (m : nat) (h1 : (m = (NUMERAL 0)) = (term131 m)) : (m = (NUMERAL 0)) = (term131 m).
Proof. exact (h1). Qed.
Lemma lem1305396 (m : nat) (h1 : (m = (NUMERAL 0)) = (term131 m)) : (term131 m) = (m = (NUMERAL 0)).
Proof. exact (SYM (@lem1305395 m h1)). Qed.
Lemma lem1305397 (m : nat) : ((term131 m) = (m = (NUMERAL 0))) = ((m = (NUMERAL 0)) = (term131 m)).
Proof. exact (prop_ext (fun h1 : (term131 m) = (m = (NUMERAL 0)) => @lem1305394 m h1) (fun h1 : (m = (NUMERAL 0)) = (term131 m) => @lem1305396 m h1)). Qed.
Lemma lem1305398 : term132 = term133.
Proof. exact (fun_ext (fun m : nat => @lem1305397 m)). Qed.
Lemma lem1305399 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1305400 : term130 = term134.
Proof. exact (MK_COMB (@lem1305399) (@lem1305398)). Qed.
Lemma lem1305401 : term134.
Proof. exact (EQ_MP (@lem1305400) (@lem1305391)). Qed.
Lemma lem1305402 (m : nat) : term135 m.
Proof. exact (@lem1305401 m). Qed.
Lemma lem1305403 (m : nat) : (term135 m) = ((m = (NUMERAL 0)) = (term131 m)).
Proof. exact (eq_refl (term135 m)). Qed.
Lemma lem1305405 (m : nat) : term136 m.
Proof. exact (@lem104208 m). Qed.
Lemma lem1305406 (m : nat) : (term136 m) = (term137 m).
Proof. exact (eq_refl (term136 m)). Qed.
Lemma lem1305407 (m : nat) : term137 m.
Proof. exact (EQ_MP (@lem1305406 m) (@lem1305405 m)). Qed.
Lemma lem1305408 (m : nat) (n : nat) : term138 m n.
Proof. exact (@lem1305407 m n). Qed.
Lemma lem1305409 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (eq_refl (term138 m n)). Qed.
Lemma lem1305410 (m : nat) (n : nat) : term139 m n.
Proof. exact (EQ_MP (@lem1305409 m n) (@lem1305408 m n)). Qed.
Lemma lem1305411 (m : nat) (n : nat) (p : nat) : term140 m n p.
Proof. exact (@lem1305410 m n p). Qed.
Lemma lem1305412 (m : nat) (n : nat) (p : nat) : (term140 m n p) = ((term141 n m p) = (term142 m n p)).
Proof. exact (eq_refl (term140 m n p)). Qed.
Lemma lem1305414 {A : Type'} (x : A) : term143 A x.
Proof. exact (@lem317 A x). Qed.
Lemma lem1305415 {A : Type'} (x : A) : (term143 A x) = ((x = x) = True).
Proof. exact (eq_refl (term143 A x)). Qed.
Lemma lem1305417 (n : nat) (m : nat) (p : nat) : term144 n m p.
Proof. exact (proj2 (@lem83517 n m p)). Qed.
Lemma lem1305433 (n : nat) (m : nat) (p : nat) : (term145 m n p) = (term145 n m p).
Proof. exact (proj2 (@lem1305417 n m p)). Qed.
Lemma lem1305434 (a : nat) (b : nat) (c : nat) : (term145 b a c) = (term145 a b c).
Proof. exact (@lem1305433 a b c). Qed.
Lemma lem1305444 (a : nat) (b : nat) (c : nat) : (term146 a b c) = (term146 a b c).
Proof. exact (eq_refl (term146 a b c)). Qed.
Lemma lem1305445 (a : nat) (b : nat) (c : nat) : ((term145 a b c) = (term145 b a c)) = ((term145 a b c) = (term145 a b c)).
Proof. exact (MK_COMB (@lem1305444 a b c) (@lem1305434 a b c)). Qed.
Lemma lem1305447 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1305415 A x) (@lem1305414 A x)). Qed.
Lemma lem1305448 (x : nat) : (x = x) = True.
Proof. exact (@lem1305447 nat x). Qed.
Lemma lem1305449 (a : nat) (b : nat) (c : nat) : ((term145 a b c) = (term145 a b c)) = True.
Proof. exact (@lem1305448 (term145 a b c)). Qed.
Lemma lem1305450 (b : nat) (a : nat) (c : nat) : ((term145 a b c) = (term145 b a c)) = True.
Proof. exact (TRANS (@lem1305445 a b c) (@lem1305449 a b c)). Qed.
Lemma lem1305451 (b : nat) (a : nat) (c : nat) : True = ((term145 a b c) = (term145 b a c)).
Proof. exact (SYM (@lem1305450 b a c)). Qed.
Lemma lem1305453 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1305454 (m : nat) (h1 : term0) : term1 m.
Proof. exact (@lem1305453 h1 m). Qed.
Lemma lem1305455 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem1305456 (m : nat) (h1 : term0) : term2 m.
Proof. exact (EQ_MP (@lem1305455 m) (@lem1305454 m h1)). Qed.
Lemma lem1305457 (m : nat) (n : nat) (h1 : term0) : term3 m n.
Proof. exact (@lem1305456 m h1 n). Qed.
Lemma lem1305458 (n : nat) (m : nat) : (term3 m n) = (term4 n m).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem1305459 (n : nat) (m : nat) (h1 : term0) : term4 n m.
Proof. exact (EQ_MP (@lem1305458 n m) (@lem1305457 m n h1)). Qed.
Lemma lem1305460 (n : nat) (m : nat) (p : nat) (h1 : term0) : term5 n m p.
Proof. exact (@lem1305459 n m h1 p). Qed.
Lemma lem1305461 (n : nat) (m : nat) (p : nat) : (term5 n m p) = (term6 n m p).
Proof. exact (eq_refl (term5 n m p)). Qed.
Lemma lem1305462 (n : nat) (m : nat) (p : nat) (h1 : term0) : term6 n m p.
Proof. exact (EQ_MP (@lem1305461 n m p) (@lem1305460 n m p h1)). Qed.
Lemma lem1305463 (m : nat) (n : nat) (p : nat) (h1 : term7 m n p) : term7 m n p.
Proof. exact (h1). Qed.
Lemma lem1305464 (m : nat) (n : nat) (p : nat) (h1 : term0) (h2 : term7 m n p) : Peano.le m p.
Proof. exact (@lem1305462 n m p h1 (@lem1305463 m n p h2)). Qed.
Lemma lem1305465 (m : nat) (n : nat) (p : nat) (h1 : term7 m n p) : term8 m p.
Proof. exact (fun h0 : term0 => @lem1305464 m n p h0 h1). Qed.
Lemma lem1305466 (m : nat) (p : nat) (h1 : term9 m p) : term9 m p.
Proof. exact (h1). Qed.
Lemma lem1305467 (m : nat) (p : nat) (h1 : term9 m p) : term8 m p.
Proof. exact (ex_elim (@lem1305466 m p h1) (fun n : nat => fun h0 : term10 m p n => @lem1305465 m n p h0)). Qed.
Lemma lem1305468 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1305469 (m : nat) (p : nat) (h1 : term0) (h2 : term9 m p) : Peano.le m p.
Proof. exact (@lem1305467 m p h2 (@lem1305468 h1)). Qed.
Lemma lem1305470 (m : nat) (p : nat) (h1 : term0) : term11 m p.
Proof. exact (fun h0 : term9 m p => @lem1305469 m p h1 h0). Qed.
Lemma lem1305471 (m : nat) (h1 : term0) : term12 m.
Proof. exact (fun p : nat => @lem1305470 m p h1). Qed.
Lemma lem1305472 (h1 : term0) : term13.
Proof. exact (fun m : nat => @lem1305471 m h1). Qed.
Lemma lem1305473 : term14.
Proof. exact (fun h0 : term0 => @lem1305472 h0). Qed.
Lemma lem1305474 : term13.
Proof. exact (@lem1305473 (@lem93743)). Qed.
Lemma lem1305475 (m : nat) : term15 m.
Proof. exact (@lem1305474 m). Qed.
Lemma lem1305476 (m : nat) : (term15 m) = (term12 m).
Proof. exact (eq_refl (term15 m)). Qed.
Lemma lem1305477 (m : nat) : term12 m.
Proof. exact (EQ_MP (@lem1305476 m) (@lem1305475 m)). Qed.
Lemma lem1305478 (m : nat) (p : nat) : term16 m p.
Proof. exact (@lem1305477 m p). Qed.
Lemma lem1305479 (m : nat) (p : nat) : (term16 m p) = (term11 m p).
Proof. exact (eq_refl (term16 m p)). Qed.
Lemma lem1305481 (x : nadd) : term147 x.
Proof. exact (@lem1304593 x). Qed.
Lemma lem1305482 (x : nadd) : (term147 x) = (term148 x).
Proof. exact (eq_refl (term147 x)). Qed.
Lemma lem1305484 (x : nadd) (h1 : term149 x) : term149 x.
Proof. exact (h1). Qed.
Lemma lem1305486 (x : nadd) : term148 x.
Proof. exact (EQ_MP (@lem1305482 x) (@lem1305481 x)). Qed.
Lemma lem1305487 (x : nadd) (h1 : term149 x) : term150 x.
Proof. exact (@lem1305486 x (@lem1305484 x h1)). Qed.
Lemma lem1305488 (x : nadd) (h1 : term150 x) : term150 x.
Proof. exact (h1). Qed.
Lemma lem1305489 (x : nadd) (B : nat) (h1 : term151 x B) : term151 x B.
Proof. exact (h1). Qed.
Lemma lem1305490 (N : nat) (x : nadd) (B : nat) (h1 : term152 N x B) : term152 N x B.
Proof. exact (h1). Qed.
Lemma lem1305491 (m : nat) (N : nat) (n : nat) (h1 : term153 m N n) : term153 m N n.
Proof. exact (h1). Qed.
Lemma lem1305492 (N : nat) (n : nat) (h1 : term154 N n) : term154 N n.
Proof. exact (h1). Qed.
Lemma lem1305493 (N : nat) (m : nat) (h1 : term154 N m) : term154 N m.
Proof. exact (h1). Qed.
Lemma lem1305494 (m : nat) (N : nat) (n : nat) (h1 : term155 m N n) : term155 m N n.
Proof. exact (h1). Qed.
Lemma lem1305496 (m : nat) (p : nat) : term11 m p.
Proof. exact (EQ_MP (@lem1305479 m p) (@lem1305478 m p)). Qed.
Lemma lem1305497 (N : nat) (m : nat) : term11 N m.
Proof. exact (@lem1305496 N m). Qed.
Lemma lem1305499 (m : nat) (p : nat) : term11 m p.
Proof. exact (EQ_MP (@lem1305479 m p) (@lem1305478 m p)). Qed.
Lemma lem1305500 (N : nat) (n : nat) : term11 N n.
Proof. exact (@lem1305499 N n). Qed.
Lemma lem1305501 (m : nat) : term156 m.
Proof. exact (@lem100517 m). Qed.
Lemma lem1305502 (m : nat) : (term156 m) = (term157 m).
Proof. exact (eq_refl (term156 m)). Qed.
Lemma lem1305503 (m : nat) : term157 m.
Proof. exact (EQ_MP (@lem1305502 m) (@lem1305501 m)). Qed.
Lemma lem1305504 (m : nat) (n : nat) : term158 m n.
Proof. exact (@lem1305503 m n). Qed.
Lemma lem1305505 (m : nat) (n : nat) : (term158 m n) = (term159 m n).
Proof. exact (eq_refl (term158 m n)). Qed.
Lemma lem1305506 (m : nat) (n : nat) : term159 m n.
Proof. exact (EQ_MP (@lem1305505 m n) (@lem1305504 m n)). Qed.
Lemma lem1305507 (m : nat) (n : nat) : (term159 m n) = ((term159 m n) = True).
Proof. exact (@lem7 (term159 m n)). Qed.
Lemma lem1305517 (N : nat) (m : nat) : (term154 N m) = ((term154 N m) = True).
Proof. exact (@lem7 (term154 N m)). Qed.
Lemma lem1305524 (m : nat) (n : nat) : (term159 m n) = True.
Proof. exact (EQ_MP (@lem1305507 m n) (@lem1305506 m n)). Qed.
Lemma lem1305525 (N : nat) : (term160 N) = True.
Proof. exact (@lem1305524 N term102). Qed.
Lemma lem1305526 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1305527 (N : nat) : (term161 N) = (and True).
Proof. exact (MK_COMB (@lem1305526) (@lem1305525 N)). Qed.
Lemma lem1305529 (N : nat) (m : nat) (h1 : term154 N m) : (term154 N m) = True.
Proof. exact (EQ_MP (@lem1305517 N m) (@lem1305493 N m h1)). Qed.
Lemma lem1305530 (N : nat) (m : nat) (h1 : term154 N m) : (term162 N m) = (True /\ True).
Proof. exact (MK_COMB (@lem1305527 N) (@lem1305529 N m h1)). Qed.
Lemma lem1305532 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1305533 : (True /\ True) = True.
Proof. exact (@lem1305532 True). Qed.
Lemma lem1305534 (N : nat) (m : nat) (h1 : term154 N m) : (term162 N m) = True.
Proof. exact (TRANS (@lem1305530 N m h1) (@lem1305533)). Qed.
Lemma lem1305535 (N : nat) (m : nat) (h1 : term154 N m) : True = (term162 N m).
Proof. exact (SYM (@lem1305534 N m h1)). Qed.
Lemma lem1305536 (N : nat) (m : nat) (h1 : term154 N m) : term162 N m.
Proof. exact (EQ_MP (@lem1305535 N m h1) (@lem0)). Qed.
Lemma lem1305537 (m : nat) : term156 m.
Proof. exact (@lem100517 m). Qed.
Lemma lem1305538 (m : nat) : (term156 m) = (term157 m).
Proof. exact (eq_refl (term156 m)). Qed.
Lemma lem1305539 (m : nat) : term157 m.
Proof. exact (EQ_MP (@lem1305538 m) (@lem1305537 m)). Qed.
Lemma lem1305540 (m : nat) (n : nat) : term158 m n.
Proof. exact (@lem1305539 m n). Qed.
Lemma lem1305541 (m : nat) (n : nat) : (term158 m n) = (term159 m n).
Proof. exact (eq_refl (term158 m n)). Qed.
Lemma lem1305542 (m : nat) (n : nat) : term159 m n.
Proof. exact (EQ_MP (@lem1305541 m n) (@lem1305540 m n)). Qed.
Lemma lem1305543 (m : nat) (n : nat) : (term159 m n) = ((term159 m n) = True).
Proof. exact (@lem7 (term159 m n)). Qed.
Lemma lem1305555 (N : nat) (n : nat) : (term154 N n) = ((term154 N n) = True).
Proof. exact (@lem7 (term154 N n)). Qed.
Lemma lem1305560 (m : nat) (n : nat) : (term159 m n) = True.
Proof. exact (EQ_MP (@lem1305543 m n) (@lem1305542 m n)). Qed.
Lemma lem1305561 (N : nat) : (term160 N) = True.
Proof. exact (@lem1305560 N term102). Qed.
Lemma lem1305562 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1305563 (N : nat) : (term161 N) = (and True).
Proof. exact (MK_COMB (@lem1305562) (@lem1305561 N)). Qed.
Lemma lem1305565 (N : nat) (n : nat) (h1 : term154 N n) : (term154 N n) = True.
Proof. exact (EQ_MP (@lem1305555 N n) (@lem1305492 N n h1)). Qed.
Lemma lem1305566 (N : nat) (n : nat) (h1 : term154 N n) : (term162 N n) = (True /\ True).
Proof. exact (MK_COMB (@lem1305563 N) (@lem1305565 N n h1)). Qed.
Lemma lem1305568 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1305569 : (True /\ True) = True.
Proof. exact (@lem1305568 True). Qed.
Lemma lem1305570 (N : nat) (n : nat) (h1 : term154 N n) : (term162 N n) = True.
Proof. exact (TRANS (@lem1305566 N n h1) (@lem1305569)). Qed.
Lemma lem1305571 (N : nat) (n : nat) (h1 : term154 N n) : True = (term162 N n).
Proof. exact (SYM (@lem1305570 N n h1)). Qed.
Lemma lem1305572 (N : nat) (n : nat) (h1 : term154 N n) : term162 N n.
Proof. exact (EQ_MP (@lem1305571 N n h1) (@lem0)). Qed.
Lemma lem1305573 (N : nat) (n : nat) (h1 : term154 N n) : term9 N n.
Proof. exact (ex_intro (term10 N n) (term163 N) (@lem1305572 N n h1)). Qed.
Lemma lem1305574 (N : nat) (m : nat) (h1 : term154 N m) : term9 N m.
Proof. exact (ex_intro (term10 N m) (term163 N) (@lem1305536 N m h1)). Qed.
Lemma lem1305575 (N : nat) (n : nat) (h1 : term154 N n) : Peano.le N n.
Proof. exact (@lem1305500 N n (@lem1305573 N n h1)). Qed.
Lemma lem1305576 (N : nat) (m : nat) (h1 : term154 N m) : Peano.le N m.
Proof. exact (@lem1305497 N m (@lem1305574 N m h1)). Qed.
Lemma lem1305577 (m : nat) (N : nat) (n : nat) (h1 : term154 N m) (h2 : term154 N n) : term155 m N n.
Proof. exact (conj (@lem1305576 N m h1) (@lem1305575 N n h2)). Qed.
Lemma lem1305578 (m : nat) (N : nat) (n : nat) (h1 : term155 m N n) : term155 m N n.
Proof. exact (h1). Qed.
Lemma lem1305579 (m : nat) (N : nat) (x : nadd) (B : nat) (h1 : term152 N x B) : term164 N x B m.
Proof. exact (@lem1305490 N x B h1 m). Qed.
Lemma lem1305580 (N : nat) (x : nadd) (B : nat) (m : nat) : (term164 N x B m) = (term165 N x B m).
Proof. exact (eq_refl (term164 N x B m)). Qed.
Lemma lem1305581 (m : nat) (N : nat) (x : nadd) (B : nat) (h1 : term152 N x B) : term165 N x B m.
Proof. exact (EQ_MP (@lem1305580 N x B m) (@lem1305579 m N x B h1)). Qed.
Lemma lem1305582 (m : nat) (n : nat) (N : nat) (x : nadd) (B : nat) (h1 : term152 N x B) : term166 N x B m n.
Proof. exact (@lem1305581 m N x B h1 n). Qed.
Lemma lem1305583 (N : nat) (x : nadd) (B : nat) (m : nat) (n : nat) : (term166 N x B m n) = (term167 N x B m n).
Proof. exact (eq_refl (term166 N x B m n)). Qed.
Lemma lem1305586 (m : nat) (n : nat) (N : nat) (x : nadd) (B : nat) (h1 : term152 N x B) : term167 N x B m n.
Proof. exact (EQ_MP (@lem1305583 N x B m n) (@lem1305582 m n N x B h1)). Qed.
Lemma lem1305587 (x : nadd) (B : nat) (m : nat) (N : nat) (n : nat) (h1 : term152 N x B) (h2 : term155 m N n) : term168 x B m n.
Proof. exact (@lem1305586 m n N x B h1 (@lem1305578 m N n h2)). Qed.
Lemma lem1305591 (b : nat) (a : nat) (c : nat) : (term145 a b c) = (term145 b a c).
Proof. exact (EQ_MP (@lem1305451 b a c) (@lem0)). Qed.
Lemma lem1305592 (B : nat) (m : nat) (n : nat) : (term169 B m n) = (term170 B m n).
Proof. exact (@lem1305591 (Nat.mul m n) B (Nat.add m n)). Qed.
Lemma lem1305593 (n : nat) (x : nadd) (m : nat) : (term171 n x m) = (term171 n x m).
Proof. exact (eq_refl (term171 n x m)). Qed.
Lemma lem1305594 (x : nadd) (B : nat) (m : nat) (n : nat) : (term168 x B m n) = (term172 x B m n).
Proof. exact (MK_COMB (@lem1305593 n x m) (@lem1305592 B m n)). Qed.
Lemma lem1305595 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1305596 (x : nadd) (B : nat) (m : nat) (n : nat) : (term173 x B m n) = (term174 x B m n).
Proof. exact (MK_COMB (@lem1305595) (@lem1305594 x B m n)). Qed.
Lemma lem1305597 (x : nadd) (B : nat) (m : nat) (n : nat) : (term175 x B m n) = (term175 x B m n).
Proof. exact (eq_refl (term175 x B m n)). Qed.
Lemma lem1305598 (x : nadd) (B : nat) (m : nat) (n : nat) : (term176 x B m n) = (term177 x B m n).
Proof. exact (MK_COMB (@lem1305596 x B m n) (@lem1305597 x B m n)). Qed.
Lemma lem1305599 (x : nadd) (B : nat) (m : nat) (n : nat) : (term177 x B m n) = (term176 x B m n).
Proof. exact (SYM (@lem1305598 x B m n)). Qed.
Lemma lem1305603 (m : nat) (n : nat) (p : nat) : (term141 n m p) = (term142 m n p).
Proof. exact (EQ_MP (@lem1305412 m n p) (@lem1305411 m n p)). Qed.
Lemma lem1305604 (x : nadd) (B : nat) (m : nat) (n : nat) : (term172 x B m n) = (term178 x B m n).
Proof. exact (@lem1305603 (Nat.mul m n) (term179 n x m) (term180 B m n)). Qed.
Lemma lem1305609 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1305610 (x : nadd) (B : nat) (m : nat) (n : nat) : (term174 x B m n) = (term181 x B m n).
Proof. exact (MK_COMB (@lem1305609) (@lem1305604 x B m n)). Qed.
Lemma lem1305611 (x : nadd) (B : nat) (m : nat) (n : nat) : (term175 x B m n) = (term175 x B m n).
Proof. exact (eq_refl (term175 x B m n)). Qed.
Lemma lem1305612 (x : nadd) (B : nat) (m : nat) (n : nat) : (term177 x B m n) = (term182 x B m n).
Proof. exact (MK_COMB (@lem1305610 x B m n) (@lem1305611 x B m n)). Qed.
Lemma lem1305615 (x : nadd) (B : nat) (m : nat) (n : nat) : (term182 x B m n) = (term177 x B m n).
Proof. exact (SYM (@lem1305612 x B m n)). Qed.
Lemma lem1305616 (x : nadd) (B : nat) (m : nat) (n : nat) (h1 : term178 x B m n) : term178 x B m n.
Proof. exact (h1). Qed.
Lemma lem1305617 (m : nat) (n : nat) (h1 : (Nat.mul m n) = (NUMERAL 0)) : (Nat.mul m n) = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1305618 (x : nadd) (B : nat) (m : nat) (n : nat) (h1 : term175 x B m n) : term175 x B m n.
Proof. exact (h1). Qed.
Lemma lem1305619 (x : nadd) (B : nat) (m : nat) (n : nat) : (term183 x B m n) = (term184 x B m n).
Proof. exact (@lem10568 (term175 x B m n) ((Nat.mul m n) = (NUMERAL 0))). Qed.
Lemma lem1305620 (x : nadd) (B : nat) (m : nat) (n : nat) : (term184 x B m n) = (term183 x B m n).
Proof. exact (SYM (@lem1305619 x B m n)). Qed.
Lemma lem1305623 (m : nat) : (m = (NUMERAL 0)) = (term131 m).
Proof. exact (EQ_MP (@lem1305403 m) (@lem1305402 m)). Qed.
Lemma lem1305624 (m : nat) (n : nat) : ((Nat.mul m n) = (NUMERAL 0)) = (term185 m n).
Proof. exact (@lem1305623 (Nat.mul m n)). Qed.
Lemma lem1305625 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1305626 (m : nat) (n : nat) : (term186 m n) = (term187 m n).
Proof. exact (MK_COMB (@lem1305625) (@lem1305624 m n)). Qed.
Lemma lem1305627 (m : nat) (n : nat) : (term187 m n) = (term186 m n).
Proof. exact (SYM (@lem1305626 m n)). Qed.
Lemma lem1305629 (n : nat) (m : nat) : (term129 m n) = (Peano.lt n m).
Proof. exact (EQ_MP (@lem1305389 n m) (@lem1305388 m n)). Qed.
Lemma lem1305630 (m : nat) (n : nat) : (term187 m n) = (term188 m n).
Proof. exact (@lem1305629 (NUMERAL 0) (Nat.mul m n)). Qed.
Lemma lem1305632 (m : nat) (n : nat) : (Peano.lt m n) = (term115 m n).
Proof. exact (EQ_MP (@lem1305383 m n) (@lem1305382 m n)). Qed.
Lemma lem1305633 (m : nat) (n : nat) : (term188 m n) = (term189 m n).
Proof. exact (@lem1305632 (NUMERAL 0) (Nat.mul m n)). Qed.
Lemma lem1305634 (m : nat) (n : nat) : (term187 m n) = (term189 m n).
Proof. exact (TRANS (@lem1305630 m n) (@lem1305633 m n)). Qed.
Lemma lem1305635 (m : nat) (n : nat) : (term189 m n) = (term187 m n).
Proof. exact (SYM (@lem1305634 m n)). Qed.
Lemma lem1305637 : term100 = term105.
Proof. exact (EQ_MP (@lem1305363) (@lem0)). Qed.
Lemma lem1305638 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1305639 : term190 = term191.
Proof. exact (MK_COMB (@lem1305638) (@lem1305637)). Qed.
Lemma lem1305640 (m : nat) (n : nat) : (Nat.mul m n) = (Nat.mul m n).
Proof. exact (eq_refl (Nat.mul m n)). Qed.
Lemma lem1305641 (m : nat) (n : nat) : (term189 m n) = (term192 m n).
Proof. exact (MK_COMB (@lem1305639) (@lem1305640 m n)). Qed.
Lemma lem1305642 (m : nat) (n : nat) : (term192 m n) = (term189 m n).
Proof. exact (SYM (@lem1305641 m n)). Qed.
Lemma lem1305644 (m : nat) (p : nat) (n : nat) (q : nat) : term25 m p n q.
Proof. exact (EQ_MP (@lem1304657 m p n q) (@lem1304656 m p n q)). Qed.
Lemma lem1305645 (m : nat) (n : nat) : term193 m n.
Proof. exact (@lem1305644 term102 term102 m n). Qed.
Lemma lem1305647 (m : nat) (p : nat) : term11 m p.
Proof. exact (EQ_MP (@lem1304620 m p) (@lem1304619 m p)). Qed.
Lemma lem1305648 (m : nat) : term194 m.
Proof. exact (@lem1305647 term102 m). Qed.
Lemma lem1305650 (m : nat) (p : nat) : term11 m p.
Proof. exact (EQ_MP (@lem1304620 m p) (@lem1304619 m p)). Qed.
Lemma lem1305651 (n : nat) : term194 n.
Proof. exact (@lem1305650 term102 n). Qed.
Lemma lem1305652 (m : nat) : term195 m.
Proof. exact (@lem100562 m). Qed.
Lemma lem1305653 (m : nat) : (term195 m) = (term196 m).
Proof. exact (eq_refl (term195 m)). Qed.
Lemma lem1305654 (m : nat) : term196 m.
Proof. exact (EQ_MP (@lem1305653 m) (@lem1305652 m)). Qed.
Lemma lem1305655 (m : nat) (n : nat) : term197 m n.
Proof. exact (@lem1305654 m n). Qed.
Lemma lem1305656 (m : nat) (n : nat) : (term197 m n) = (term198 m n).
Proof. exact (eq_refl (term197 m n)). Qed.
Lemma lem1305657 (m : nat) (n : nat) : term198 m n.
Proof. exact (EQ_MP (@lem1305656 m n) (@lem1305655 m n)). Qed.
Lemma lem1305658 (m : nat) (n : nat) : (term198 m n) = ((term198 m n) = True).
Proof. exact (@lem7 (term198 m n)). Qed.
Lemma lem1305668 (N : nat) (m : nat) : (term154 N m) = ((term154 N m) = True).
Proof. exact (@lem7 (term154 N m)). Qed.
Lemma lem1305675 (m : nat) (n : nat) : (term198 m n) = True.
Proof. exact (EQ_MP (@lem1305658 m n) (@lem1305657 m n)). Qed.
Lemma lem1305676 (N : nat) : (term199 N) = True.
Proof. exact (@lem1305675 N term102). Qed.
Lemma lem1305677 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1305678 (N : nat) : (term200 N) = (and True).
Proof. exact (MK_COMB (@lem1305677) (@lem1305676 N)). Qed.
Lemma lem1305680 (N : nat) (m : nat) (h1 : term154 N m) : (term154 N m) = True.
Proof. exact (EQ_MP (@lem1305668 N m) (@lem1305493 N m h1)). Qed.
Lemma lem1305681 (N : nat) (m : nat) (h1 : term154 N m) : (term201 N m) = (True /\ True).
Proof. exact (MK_COMB (@lem1305678 N) (@lem1305680 N m h1)). Qed.
Lemma lem1305683 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1305684 : (True /\ True) = True.
Proof. exact (@lem1305683 True). Qed.
Lemma lem1305685 (N : nat) (m : nat) (h1 : term154 N m) : (term201 N m) = True.
Proof. exact (TRANS (@lem1305681 N m h1) (@lem1305684)). Qed.
Lemma lem1305686 (N : nat) (m : nat) (h1 : term154 N m) : True = (term201 N m).
Proof. exact (SYM (@lem1305685 N m h1)). Qed.
Lemma lem1305687 (N : nat) (m : nat) (h1 : term154 N m) : term201 N m.
Proof. exact (EQ_MP (@lem1305686 N m h1) (@lem0)). Qed.
Lemma lem1305688 (m : nat) : term195 m.
Proof. exact (@lem100562 m). Qed.
Lemma lem1305689 (m : nat) : (term195 m) = (term196 m).
Proof. exact (eq_refl (term195 m)). Qed.
Lemma lem1305690 (m : nat) : term196 m.
Proof. exact (EQ_MP (@lem1305689 m) (@lem1305688 m)). Qed.
Lemma lem1305691 (m : nat) (n : nat) : term197 m n.
Proof. exact (@lem1305690 m n). Qed.
Lemma lem1305692 (m : nat) (n : nat) : (term197 m n) = (term198 m n).
Proof. exact (eq_refl (term197 m n)). Qed.
Lemma lem1305693 (m : nat) (n : nat) : term198 m n.
Proof. exact (EQ_MP (@lem1305692 m n) (@lem1305691 m n)). Qed.
Lemma lem1305694 (m : nat) (n : nat) : (term198 m n) = ((term198 m n) = True).
Proof. exact (@lem7 (term198 m n)). Qed.
Lemma lem1305706 (N : nat) (n : nat) : (term154 N n) = ((term154 N n) = True).
Proof. exact (@lem7 (term154 N n)). Qed.
Lemma lem1305711 (m : nat) (n : nat) : (term198 m n) = True.
Proof. exact (EQ_MP (@lem1305694 m n) (@lem1305693 m n)). Qed.
Lemma lem1305712 (N : nat) : (term199 N) = True.
Proof. exact (@lem1305711 N term102). Qed.
Lemma lem1305713 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1305714 (N : nat) : (term200 N) = (and True).
Proof. exact (MK_COMB (@lem1305713) (@lem1305712 N)). Qed.
Lemma lem1305716 (N : nat) (n : nat) (h1 : term154 N n) : (term154 N n) = True.
Proof. exact (EQ_MP (@lem1305706 N n) (@lem1305492 N n h1)). Qed.
Lemma lem1305717 (N : nat) (n : nat) (h1 : term154 N n) : (term201 N n) = (True /\ True).
Proof. exact (MK_COMB (@lem1305714 N) (@lem1305716 N n h1)). Qed.
Lemma lem1305719 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1305720 : (True /\ True) = True.
Proof. exact (@lem1305719 True). Qed.
Lemma lem1305721 (N : nat) (n : nat) (h1 : term154 N n) : (term201 N n) = True.
Proof. exact (TRANS (@lem1305717 N n h1) (@lem1305720)). Qed.
Lemma lem1305722 (N : nat) (n : nat) (h1 : term154 N n) : True = (term201 N n).
Proof. exact (SYM (@lem1305721 N n h1)). Qed.
Lemma lem1305723 (N : nat) (n : nat) (h1 : term154 N n) : term201 N n.
Proof. exact (EQ_MP (@lem1305722 N n h1) (@lem0)). Qed.
Lemma lem1305724 (N : nat) (n : nat) (h1 : term154 N n) : term202 n.
Proof. exact (ex_intro (term203 n) (term163 N) (@lem1305723 N n h1)). Qed.
Lemma lem1305725 (N : nat) (m : nat) (h1 : term154 N m) : term202 m.
Proof. exact (ex_intro (term203 m) (term163 N) (@lem1305687 N m h1)). Qed.
Lemma lem1305726 (N : nat) (n : nat) (h1 : term154 N n) : term204 n.
Proof. exact (@lem1305651 n (@lem1305724 N n h1)). Qed.
Lemma lem1305727 (N : nat) (m : nat) (h1 : term154 N m) : term204 m.
Proof. exact (@lem1305648 m (@lem1305725 N m h1)). Qed.
Lemma lem1305728 (m : nat) (N : nat) (n : nat) (h1 : term154 N m) (h2 : term154 N n) : term205 m n.
Proof. exact (conj (@lem1305727 N m h1) (@lem1305726 N n h2)). Qed.
Lemma lem1305729 (m : nat) (N : nat) (n : nat) (h1 : term154 N m) (h2 : term154 N n) : term192 m n.
Proof. exact (@lem1305645 m n (@lem1305728 m N n h1 h2)). Qed.
Lemma lem1305730 (m : nat) (N : nat) (n : nat) (h1 : term154 N m) (h2 : term154 N n) : term189 m n.
Proof. exact (EQ_MP (@lem1305642 m n) (@lem1305729 m N n h1 h2)). Qed.
Lemma lem1305731 (m : nat) (N : nat) (n : nat) (h1 : term154 N m) (h2 : term154 N n) : term187 m n.
Proof. exact (EQ_MP (@lem1305635 m n) (@lem1305730 m N n h1 h2)). Qed.
Lemma lem1305732 (m : nat) (N : nat) (n : nat) (h1 : term154 N m) (h2 : term154 N n) : term186 m n.
Proof. exact (EQ_MP (@lem1305627 m n) (@lem1305731 m N n h1 h2)). Qed.
Lemma lem1305733 (x : nadd) (B : nat) (m : nat) (N : nat) (n : nat) (h1 : term154 N m) (h2 : term154 N n) : term184 x B m n.
Proof. exact (fun h0 : term206 x B m n => @lem1305732 m N n h1 h2). Qed.
Lemma lem1305734 (x : nadd) (B : nat) (m : nat) (N : nat) (n : nat) (h1 : term154 N m) (h2 : term154 N n) : term183 x B m n.
Proof. exact (EQ_MP (@lem1305620 x B m n) (@lem1305733 x B m N n h1 h2)). Qed.
Lemma lem1305735 (x : nadd) (B : nat) (N : nat) (m : nat) (n : nat) (h1 : term154 N m) (h2 : term154 N n) (h3 : (Nat.mul m n) = (NUMERAL 0)) : term175 x B m n.
Proof. exact (@lem1305734 x B m N n h1 h2 (@lem1305617 m n h3)). Qed.
Lemma lem1305736 (N : nat) (x : nadd) (B : nat) (m : nat) (n : nat) (h1 : term154 N m) (h2 : term154 N n) (h3 : term178 x B m n) : term175 x B m n.
Proof. exact (or_elim (@lem1305616 x B m n h3) (fun h0 : (Nat.mul m n) = (NUMERAL 0) => @lem1305735 x B N m n h1 h2 h0) (fun h0 : term175 x B m n => @lem1305618 x B m n h0)). Qed.
Lemma lem1305737 (x : nadd) (B : nat) (m : nat) (N : nat) (n : nat) (h1 : term154 N m) (h2 : term154 N n) : term182 x B m n.
Proof. exact (fun h0 : term178 x B m n => @lem1305736 N x B m n h1 h2 h0). Qed.
Lemma lem1305738 (x : nadd) (B : nat) (m : nat) (N : nat) (n : nat) (h1 : term154 N m) (h2 : term154 N n) : term177 x B m n.
Proof. exact (EQ_MP (@lem1305615 x B m n) (@lem1305737 x B m N n h1 h2)). Qed.
Lemma lem1305739 (x : nadd) (B : nat) (m : nat) (N : nat) (n : nat) (h1 : term154 N m) (h2 : term154 N n) : term176 x B m n.
Proof. exact (EQ_MP (@lem1305599 x B m n) (@lem1305738 x B m N n h1 h2)). Qed.
Lemma lem1305740 (x : nadd) (B : nat) (m : nat) (N : nat) (n : nat) (h1 : term152 N x B) (h2 : term155 m N n) (h3 : term154 N m) (h4 : term154 N n) : term175 x B m n.
Proof. exact (@lem1305739 x B m N n h3 h4 (@lem1305587 x B m N n h1 h2)). Qed.
Lemma lem1305741 (x : nadd) (B : nat) (m : nat) (N : nat) (n : nat) (h1 : term152 N x B) (h2 : term154 N m) (h3 : term154 N n) : term207 N x B m n.
Proof. exact (fun h0 : term155 m N n => @lem1305740 x B m N n h1 h0 h2 h3). Qed.
Lemma lem1305742 (x : nadd) (B : nat) (m : nat) (N : nat) (n : nat) (h1 : term152 N x B) (h2 : term155 m N n) (h3 : term154 N m) (h4 : term154 N n) : term175 x B m n.
Proof. exact (@lem1305741 x B m N n h1 h3 h4 (@lem1305494 m N n h2)). Qed.
Lemma lem1305743 (x : nadd) (B : nat) (m : nat) (N : nat) (n : nat) (h1 : term152 N x B) (h2 : term154 N m) (h3 : term154 N n) : (term155 m N n) = (term175 x B m n).
Proof. exact (prop_ext (fun h4 : term155 m N n => @lem1305742 x B m N n h1 h4 h2 h3) (fun h4 : term175 x B m n => @lem1305577 m N n h2 h3)). Qed.
Lemma lem1305744 (x : nadd) (B : nat) (m : nat) (N : nat) (n : nat) (h1 : term152 N x B) (h2 : term154 N m) (h3 : term154 N n) : term175 x B m n.
Proof. exact (EQ_MP (@lem1305743 x B m N n h1 h2 h3) (@lem1305577 m N n h2 h3)). Qed.
Lemma lem1305745 (m : nat) (N : nat) (n : nat) (h1 : term153 m N n) : term154 N n.
Proof. exact (proj2 (@lem1305491 m N n h1)). Qed.
Lemma lem1305746 (m : nat) (N : nat) (n : nat) (h1 : term153 m N n) : term154 N m.
Proof. exact (proj1 (@lem1305491 m N n h1)). Qed.
Lemma lem1305747 (x : nadd) (B : nat) (m : nat) (N : nat) (n : nat) (h1 : term152 N x B) (h2 : term154 N m) (h3 : term154 N n) : (term154 N n) = (term175 x B m n).
Proof. exact (prop_ext (fun h4 : term154 N n => @lem1305744 x B m N n h1 h2 h3) (fun h4 : term175 x B m n => @lem1305492 N n h3)). Qed.
Lemma lem1305748 (x : nadd) (B : nat) (m : nat) (N : nat) (n : nat) (h1 : term152 N x B) (h2 : term154 N m) (h3 : term154 N n) : term175 x B m n.
Proof. exact (EQ_MP (@lem1305747 x B m N n h1 h2 h3) (@lem1305492 N n h3)). Qed.
Lemma lem1305749 (x : nadd) (B : nat) (m : nat) (N : nat) (n : nat) (h1 : term152 N x B) (h2 : term154 N m) (h3 : term154 N n) : (term154 N m) = (term175 x B m n).
Proof. exact (prop_ext (fun h4 : term154 N m => @lem1305748 x B m N n h1 h2 h3) (fun h4 : term175 x B m n => @lem1305493 N m h2)). Qed.
Lemma lem1305750 (x : nadd) (B : nat) (m : nat) (N : nat) (n : nat) (h1 : term152 N x B) (h2 : term154 N m) (h3 : term154 N n) : term175 x B m n.
Proof. exact (EQ_MP (@lem1305749 x B m N n h1 h2 h3) (@lem1305493 N m h2)). Qed.
Lemma lem1305751 (x : nadd) (B : nat) (n : nat) (N : nat) (m : nat) (h1 : term152 N x B) (h2 : term153 m N n) (h3 : term154 N m) : (term154 N n) = (term175 x B m n).
Proof. exact (prop_ext (fun h4 : term154 N n => @lem1305750 x B m N n h1 h3 h4) (fun h4 : term175 x B m n => @lem1305745 m N n h2)). Qed.
Lemma lem1305752 (x : nadd) (B : nat) (n : nat) (N : nat) (m : nat) (h1 : term152 N x B) (h2 : term153 m N n) (h3 : term154 N m) : term175 x B m n.
Proof. exact (EQ_MP (@lem1305751 x B n N m h1 h2 h3) (@lem1305745 m N n h2)). Qed.
Lemma lem1305753 (x : nadd) (B : nat) (m : nat) (N : nat) (n : nat) (h1 : term152 N x B) (h2 : term153 m N n) : (term154 N m) = (term175 x B m n).
Proof. exact (prop_ext (fun h3 : term154 N m => @lem1305752 x B n N m h1 h2 h3) (fun h3 : term175 x B m n => @lem1305746 m N n h2)). Qed.
Lemma lem1305754 (x : nadd) (B : nat) (m : nat) (N : nat) (n : nat) (h1 : term152 N x B) (h2 : term153 m N n) : term175 x B m n.
Proof. exact (EQ_MP (@lem1305753 x B m N n h1 h2) (@lem1305746 m N n h2)). Qed.
Lemma lem1305755 (m : nat) (n : nat) (N : nat) (x : nadd) (B : nat) (h1 : term152 N x B) : term208 N x B m n.
Proof. exact (fun h0 : term153 m N n => @lem1305754 x B m N n h1 h0). Qed.
Lemma lem1305760 (m : nat) (N : nat) (x : nadd) (B : nat) (h1 : term152 N x B) : term209 N x B m.
Proof. exact (fun n : nat => @lem1305755 m n N x B h1). Qed.
Lemma lem1305765 (N : nat) (x : nadd) (B : nat) (h1 : term152 N x B) : term210 N x B.
Proof. exact (fun m : nat => @lem1305760 m N x B h1). Qed.
Lemma lem1305766 (N : nat) (x : nadd) (B : nat) (h1 : term152 N x B) : term211 x B.
Proof. exact (ex_intro (term212 x B) (term163 N) (@lem1305765 N x B h1)). Qed.
Lemma lem1305767 (N : nat) (x : nadd) (B : nat) (h1 : term152 N x B) : term213 x.
Proof. exact (ex_intro (term214 x) B (@lem1305766 N x B h1)). Qed.
Lemma lem1305768 (x : nadd) (B : nat) (h1 : term151 x B) : term213 x.
Proof. exact (ex_elim (@lem1305489 x B h1) (fun N : nat => fun h0 : term215 x B N => @lem1305767 N x B h0)). Qed.
Lemma lem1305769 (x : nadd) (h1 : term150 x) : term213 x.
Proof. exact (ex_elim (@lem1305488 x h1) (fun B : nat => fun h0 : term216 x B => @lem1305768 x B h0)). Qed.
Lemma lem1305770 (x : nadd) : term217 x.
Proof. exact (fun h0 : term150 x => @lem1305769 x h0). Qed.
Lemma lem1305771 (x : nadd) (h1 : term149 x) : term213 x.
Proof. exact (@lem1305770 x (@lem1305487 x h1)). Qed.
Lemma lem1305772 (x : nadd) : term218 x.
Proof. exact (fun h0 : term149 x => @lem1305771 x h0). Qed.
Lemma lem1305777 : term219.
Proof. exact (fun x : nadd => @lem1305772 x). Qed.
