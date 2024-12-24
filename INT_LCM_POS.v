Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LCM_POS_term_abbrevs.
Require Import INT_ABS_POS_spec.
Require Import INT_LE_DIV_spec.
Require Import INT_POS_spec.
Require Import int_lcm_spec.
Require Import thm0_spec.
Require Import thm13473_spec.
Require Import thm1842_spec.
Require Import thm2801880_spec.
Require Import thm7_spec.
Lemma lem2806105 (m : int) : term0 m.
Proof. exact (@lem2802699 m). Qed.
Lemma lem2806106 (m : int) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem2806107 (m : int) : term1 m.
Proof. exact (EQ_MP (@lem2806106 m) (@lem2806105 m)). Qed.
Lemma lem2806108 (m : int) (n : int) : term2 m n.
Proof. exact (@lem2806107 m n). Qed.
Lemma lem2806109 (m : int) (n : int) : (term2 m n) = ((term3 m n) = (term4 m n)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem2806112 (m : int) (n : int) : (term3 m n) = (term4 m n).
Proof. exact (EQ_MP (@lem2806109 m n) (@lem2806108 m n)). Qed.
Lemma lem2806117 : term5 = term5.
Proof. exact (eq_refl term5). Qed.
Lemma lem2806118 (m : int) (n : int) : (term6 m n) = (term7 m n).
Proof. exact (MK_COMB (@lem2806117) (@lem2806112 m n)). Qed.
Lemma lem2806119 (m : int) (n : int) : (term7 m n) = (term6 m n).
Proof. exact (SYM (@lem2806118 m n)). Qed.
Lemma lem2806120 (_474 : int) (_475 : Prop) (_476 : int -> Prop) (_477 : int) : (term8 _476 _475 _474 _477) = (term9 _474 _475 _476 _477).
Proof. exact (@lem13473 int _474 _475 _476 _477). Qed.
Lemma lem2806121 (_474 : int) (_475 : Prop) (_477 : int) : (term10 _475 _474 _477) = (term11 _474 _475 _477).
Proof. exact (@lem2806120 _474 _475 term12 _477). Qed.
Lemma lem2806122 (m : int) (n : int) : (term13 m n) = (term14 m n).
Proof. exact (@lem2806121 term15 ((int_mul m n) = term15) (term16 m n)). Qed.
Lemma lem2806123 (m : int) (n : int) : (term17 m n) = (term18 m n).
Proof. exact (eq_refl (term17 m n)). Qed.
Lemma lem2806124 (m : int) (n : int) : (term19 m n) = (term19 m n).
Proof. exact (eq_refl (term19 m n)). Qed.
Lemma lem2806125 (m : int) (n : int) : (term20 m n) = (term21 m n).
Proof. exact (MK_COMB (@lem2806124 m n) (@lem2806123 m n)). Qed.
Lemma lem2806126 : term22 = term23.
Proof. exact (eq_refl term22). Qed.
Lemma lem2806127 (m : int) (n : int) : (term24 m n) = (term24 m n).
Proof. exact (eq_refl (term24 m n)). Qed.
Lemma lem2806128 (m : int) (n : int) : (term25 m n) = (term26 m n).
Proof. exact (MK_COMB (@lem2806127 m n) (@lem2806126)). Qed.
Lemma lem2806129 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2806130 (m : int) (n : int) : (term27 m n) = (term28 m n).
Proof. exact (MK_COMB (@lem2806129) (@lem2806128 m n)). Qed.
Lemma lem2806131 (m : int) (n : int) : (term14 m n) = (term29 m n).
Proof. exact (MK_COMB (@lem2806130 m n) (@lem2806125 m n)). Qed.
Lemma lem2806132 (m : int) (n : int) : (term13 m n) = (term7 m n).
Proof. exact (eq_refl (term13 m n)). Qed.
Lemma lem2806133 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2806134 (m : int) (n : int) : (term30 m n) = (term31 m n).
Proof. exact (MK_COMB (@lem2806133) (@lem2806132 m n)). Qed.
Lemma lem2806135 (m : int) (n : int) : ((term13 m n) = (term14 m n)) = ((term7 m n) = (term29 m n)).
Proof. exact (MK_COMB (@lem2806134 m n) (@lem2806131 m n)). Qed.
Lemma lem2806136 (m : int) (n : int) : (term7 m n) = (term29 m n).
Proof. exact (EQ_MP (@lem2806135 m n) (@lem2806122 m n)). Qed.
Lemma lem2806137 (m : int) (n : int) : (term29 m n) = (term7 m n).
Proof. exact (SYM (@lem2806136 m n)). Qed.
Lemma lem2806212 (n : nat) : term32 n.
Proof. exact (@lem2307535 n). Qed.
Lemma lem2806213 (n : nat) : (term32 n) = (term33 n).
Proof. exact (eq_refl (term32 n)). Qed.
Lemma lem2806214 (n : nat) : term33 n.
Proof. exact (EQ_MP (@lem2806213 n) (@lem2806212 n)). Qed.
Lemma lem2806215 (n : nat) : (term33 n) = ((term33 n) = True).
Proof. exact (@lem7 (term33 n)). Qed.
Lemma lem2806218 (n : nat) : (term33 n) = True.
Proof. exact (EQ_MP (@lem2806215 n) (@lem2806214 n)). Qed.
Lemma lem2806219 : term23 = True.
Proof. exact (@lem2806218 (NUMERAL 0)). Qed.
Lemma lem2806220 : True = term23.
Proof. exact (SYM (@lem2806219)). Qed.
Lemma lem2806222 (a : int) : term34 a.
Proof. exact (@lem2801880 a). Qed.
Lemma lem2806223 (a : int) : (term34 a) = (term35 a).
Proof. exact (eq_refl (term34 a)). Qed.
Lemma lem2806224 (a : int) : term35 a.
Proof. exact (EQ_MP (@lem2806223 a) (@lem2806222 a)). Qed.
Lemma lem2806225 (a : int) (b : int) : term36 a b.
Proof. exact (@lem2806224 a b). Qed.
Lemma lem2806226 (a : int) (b : int) : (term36 a b) = (term37 a b).
Proof. exact (eq_refl (term36 a b)). Qed.
Lemma lem2806227 (a : int) (b : int) : term37 a b.
Proof. exact (EQ_MP (@lem2806226 a b) (@lem2806225 a b)). Qed.
Lemma lem2806239 (a : int) (b : int) : term38 a b.
Proof. exact (proj1 (@lem2806227 a b)). Qed.
Lemma lem2806240 (a : int) (b : int) : (term38 a b) = ((term38 a b) = True).
Proof. exact (@lem7 (term38 a b)). Qed.
Lemma lem2806242 (m : int) : term39 m.
Proof. exact (@lem2651667 m). Qed.
Lemma lem2806243 (m : int) : (term39 m) = (term40 m).
Proof. exact (eq_refl (term39 m)). Qed.
Lemma lem2806244 (m : int) : term40 m.
Proof. exact (EQ_MP (@lem2806243 m) (@lem2806242 m)). Qed.
Lemma lem2806245 (m : int) (n : int) : term41 m n.
Proof. exact (@lem2806244 m n). Qed.
Lemma lem2806246 (m : int) (n : int) : (term41 m n) = (term42 m n).
Proof. exact (eq_refl (term41 m n)). Qed.
Lemma lem2806247 (m : int) (n : int) : term42 m n.
Proof. exact (EQ_MP (@lem2806246 m n) (@lem2806245 m n)). Qed.
Lemma lem2806248 (m : int) (n : int) (h1 : term43 m n) : term43 m n.
Proof. exact (h1). Qed.
Lemma lem2806249 (m : int) (n : int) (h1 : term43 m n) : term44 m n.
Proof. exact (@lem2806247 m n (@lem2806248 m n h1)). Qed.
Lemma lem2806250 (m : int) (n : int) : (term44 m n) = ((term44 m n) = True).
Proof. exact (@lem7 (term44 m n)). Qed.
Lemma lem2806251 (m : int) (n : int) (h1 : term43 m n) : (term44 m n) = True.
Proof. exact (EQ_MP (@lem2806250 m n) (@lem2806249 m n h1)). Qed.
Lemma lem2806257 (x : int) : term45 x.
Proof. exact (@lem2300522 x). Qed.
Lemma lem2806258 (x : int) : (term45 x) = (term46 x).
Proof. exact (eq_refl (term45 x)). Qed.
Lemma lem2806259 (x : int) : term46 x.
Proof. exact (EQ_MP (@lem2806258 x) (@lem2806257 x)). Qed.
Lemma lem2806260 (x : int) : (term46 x) = ((term46 x) = True).
Proof. exact (@lem7 (term46 x)). Qed.
Lemma lem2806281 (m : int) (n : int) : term47 m n.
Proof. exact (fun h0 : term43 m n => @lem2806251 m n h0). Qed.
Lemma lem2806282 (m : int) (n : int) : term48 m n.
Proof. exact (@lem2806281 (term49 m n) (term50 m n)). Qed.
Lemma lem2806286 (x : int) : (term46 x) = True.
Proof. exact (EQ_MP (@lem2806260 x) (@lem2806259 x)). Qed.
Lemma lem2806287 (m : int) (n : int) : (term51 m n) = True.
Proof. exact (@lem2806286 (int_mul m n)). Qed.
Lemma lem2806288 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2806289 (m : int) (n : int) : (term52 m n) = (and True).
Proof. exact (MK_COMB (@lem2806288) (@lem2806287 m n)). Qed.
Lemma lem2806291 (a : int) (b : int) : (term38 a b) = True.
Proof. exact (EQ_MP (@lem2806240 a b) (@lem2806239 a b)). Qed.
Lemma lem2806292 (m : int) (n : int) : (term38 m n) = True.
Proof. exact (@lem2806291 m n). Qed.
Lemma lem2806293 (m : int) (n : int) : (term53 m n) = (True /\ True).
Proof. exact (MK_COMB (@lem2806289 m n) (@lem2806292 m n)). Qed.
Lemma lem2806295 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem2806296 : (True /\ True) = True.
Proof. exact (@lem2806295 True). Qed.
Lemma lem2806297 (m : int) (n : int) : (term53 m n) = True.
Proof. exact (TRANS (@lem2806293 m n) (@lem2806296)). Qed.
Lemma lem2806298 (m : int) (n : int) : True = (term53 m n).
Proof. exact (SYM (@lem2806297 m n)). Qed.
Lemma lem2806299 (m : int) (n : int) : term53 m n.
Proof. exact (EQ_MP (@lem2806298 m n) (@lem0)). Qed.
Lemma lem2806300 (m : int) (n : int) : (term18 m n) = True.
Proof. exact (@lem2806282 m n (@lem2806299 m n)). Qed.
Lemma lem2806301 (m : int) (n : int) : True = (term18 m n).
Proof. exact (SYM (@lem2806300 m n)). Qed.
Lemma lem2806303 (m : int) (n : int) : term18 m n.
Proof. exact (EQ_MP (@lem2806301 m n) (@lem0)). Qed.
Lemma lem2806304 (m : int) (n : int) : term21 m n.
Proof. exact (fun h0 : term54 m n => @lem2806303 m n). Qed.
Lemma lem2806305 : term23.
Proof. exact (EQ_MP (@lem2806220) (@lem0)). Qed.
Lemma lem2806306 (m : int) (n : int) : term26 m n.
Proof. exact (fun h0 : (int_mul m n) = term15 => @lem2806305). Qed.
Lemma lem2806307 (m : int) (n : int) : term29 m n.
Proof. exact (conj (@lem2806306 m n) (@lem2806304 m n)). Qed.
Lemma lem2806308 (m : int) (n : int) : term7 m n.
Proof. exact (EQ_MP (@lem2806137 m n) (@lem2806307 m n)). Qed.
Lemma lem2806309 (m : int) (n : int) : term6 m n.
Proof. exact (EQ_MP (@lem2806119 m n) (@lem2806308 m n)). Qed.
Lemma lem2806314 (m : int) : term55 m.
Proof. exact (fun n : int => @lem2806309 m n). Qed.
Lemma lem2806319 : term56.
Proof. exact (fun m : int => @lem2806314 m). Qed.
