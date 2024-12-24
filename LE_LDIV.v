Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LE_LDIV_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import LEFT_ADD_DISTRIB_spec.
Require Import LET_TRANS_spec.
Require Import LE_LDIV_EQ_spec.
Require Import LT_ADD_spec.
Require Import LT_NZ_spec.
Require Import MULT_CLAUSES_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm4211_spec.
Require Import thm69_spec.
Require Import thm82_spec.
Lemma lem189311 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem189312 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem189313 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem189312 t1) (@lem189311 t1)). Qed.
Lemma lem189314 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem189313 t1 t2). Qed.
Lemma lem189315 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem189316 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem189315 t1 t2) (@lem189314 t1 t2)). Qed.
Lemma lem189317 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem189316 t1 t2 t3). Qed.
Lemma lem189318 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem189319 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem189318 t1 t2 t3) (@lem189317 t1 t2 t3)). Qed.
Lemma lem189320 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem189319 t1 t2 t3)). Qed.
Lemma lem189321 : term7.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem189322 : term8.
Proof. exact (proj2 (@lem189321)). Qed.
Lemma lem189323 : term9.
Proof. exact (proj2 (@lem189322)). Qed.
Lemma lem189339 : term10.
Proof. exact (proj1 (@lem189323)). Qed.
Lemma lem189340 (m : nat) : term11 m.
Proof. exact (@lem189339 m). Qed.
Lemma lem189341 (m : nat) : (term11 m) = ((term12 m) = m).
Proof. exact (eq_refl (term11 m)). Qed.
Lemma lem189355 (m : nat) : term13 m.
Proof. exact (@lem82055 m). Qed.
Lemma lem189356 (m : nat) : (term13 m) = (term14 m).
Proof. exact (eq_refl (term13 m)). Qed.
Lemma lem189357 (m : nat) : term14 m.
Proof. exact (EQ_MP (@lem189356 m) (@lem189355 m)). Qed.
Lemma lem189358 (m : nat) (n : nat) : term15 m n.
Proof. exact (@lem189357 m n). Qed.
Lemma lem189359 (n : nat) (m : nat) : (term15 m n) = (term16 n m).
Proof. exact (eq_refl (term15 m n)). Qed.
Lemma lem189360 (n : nat) (m : nat) : term16 n m.
Proof. exact (EQ_MP (@lem189359 n m) (@lem189358 m n)). Qed.
Lemma lem189361 (n : nat) (m : nat) (p : nat) : term17 n m p.
Proof. exact (@lem189360 n m p). Qed.
Lemma lem189362 (n : nat) (m : nat) (p : nat) : (term17 n m p) = ((term18 m n p) = (term19 n m p)).
Proof. exact (eq_refl (term17 n m p)). Qed.
Lemma lem189364 (a : nat) : term20 a.
Proof. exact (@lem189160 a). Qed.
Lemma lem189365 (a : nat) : (term20 a) = (term21 a).
Proof. exact (eq_refl (term20 a)). Qed.
Lemma lem189366 (a : nat) : term21 a.
Proof. exact (EQ_MP (@lem189365 a) (@lem189364 a)). Qed.
Lemma lem189367 (a : nat) (b : nat) : term22 a b.
Proof. exact (@lem189366 a b). Qed.
Lemma lem189368 (b : nat) (a : nat) : (term22 a b) = (term23 b a).
Proof. exact (eq_refl (term22 a b)). Qed.
Lemma lem189369 (b : nat) (a : nat) : term23 b a.
Proof. exact (EQ_MP (@lem189368 b a) (@lem189367 a b)). Qed.
Lemma lem189370 (b : nat) (a : nat) (n : nat) : term24 b a n.
Proof. exact (@lem189369 b a n). Qed.
Lemma lem189371 (b : nat) (a : nat) (n : nat) : (term24 b a n) = (term25 b a n).
Proof. exact (eq_refl (term24 b a n)). Qed.
Lemma lem189372 (b : nat) (a : nat) (n : nat) : term25 b a n.
Proof. exact (EQ_MP (@lem189371 b a n) (@lem189370 b a n)). Qed.
Lemma lem189373 (a : nat) (h1 : term26 a) : term26 a.
Proof. exact (h1). Qed.
Lemma lem189374 (b : nat) (n : nat) (a : nat) (h1 : term26 a) : (term27 b a n) = (term28 b a n).
Proof. exact (@lem189372 b a n (@lem189373 a h1)). Qed.
Lemma lem189395 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term29 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem189396 (p : Prop) (q : Prop) (p' : Prop) : term30 p q p'.
Proof. exact (fun q' : Prop => @lem189395 p q p' q'). Qed.
Lemma lem189397 (p : Prop) (q : Prop) : term31 p q.
Proof. exact (fun p' : Prop => @lem189396 p q p'). Qed.
Lemma lem189398 (b : nat) (a : nat) (n : nat) : term32 b a n.
Proof. exact (@lem189397 (term33 b a n) (term27 b a n)). Qed.
Lemma lem189399 (b : nat) (a : nat) (n : nat) (p' : Prop) : term34 b a n p'.
Proof. exact (@lem189398 b a n p'). Qed.
Lemma lem189400 (b : nat) (a : nat) (n : nat) (p' : Prop) : (term34 b a n p') = (term35 b a n p').
Proof. exact (eq_refl (term34 b a n p')). Qed.
Lemma lem189401 (b : nat) (a : nat) (n : nat) (p' : Prop) : term35 b a n p'.
Proof. exact (EQ_MP (@lem189400 b a n p') (@lem189399 b a n p')). Qed.
Lemma lem189402 (b : nat) (a : nat) (n : nat) (p' : Prop) (q' : Prop) : term36 b a n p' q'.
Proof. exact (@lem189401 b a n p' q'). Qed.
Lemma lem189403 (b : nat) (a : nat) (n : nat) (p' : Prop) (q' : Prop) : (term36 b a n p' q') = (term37 b a n p' q').
Proof. exact (eq_refl (term36 b a n p' q')). Qed.
Lemma lem189404 (b : nat) (a : nat) (n : nat) (p' : Prop) (q' : Prop) : term37 b a n p' q'.
Proof. exact (EQ_MP (@lem189403 b a n p' q') (@lem189402 b a n p' q')). Qed.
Lemma lem189409 (b : nat) (a : nat) (n : nat) : (term33 b a n) = (term33 b a n).
Proof. exact (eq_refl (term33 b a n)). Qed.
Lemma lem189410 (b : nat) (a : nat) (n : nat) (q' : Prop) : term38 b a n q'.
Proof. exact (@lem189404 b a n (term33 b a n) q'). Qed.
Lemma lem189411 (b : nat) (a : nat) (n : nat) (q' : Prop) : term39 b a n q'.
Proof. exact (@lem189410 b a n q' (@lem189409 b a n)). Qed.
Lemma lem189412 (b : nat) (a : nat) (n : nat) (h1 : term33 b a n) : term33 b a n.
Proof. exact (h1). Qed.
Lemma lem189416 (b : nat) (a : nat) (n : nat) (h1 : term33 b a n) : term26 a.
Proof. exact (proj1 (@lem189412 b a n h1)). Qed.
Lemma lem189417 (a : nat) : term40 a.
Proof. exact (@lem82 (a = (NUMERAL 0))). Qed.
Lemma lem189431 (b : nat) (a : nat) (n : nat) : term25 b a n.
Proof. exact (fun h0 : term26 a => @lem189374 b n a h0). Qed.
Lemma lem189433 (b : nat) (a : nat) (n : nat) (h1 : term33 b a n) : (a = (NUMERAL 0)) = False.
Proof. exact (@lem189417 a (@lem189416 b a n h1)). Qed.
Lemma lem189434 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem189435 (b : nat) (a : nat) (n : nat) (h1 : term33 b a n) : (term26 a) = (~ False).
Proof. exact (MK_COMB (@lem189434) (@lem189433 b a n h1)). Qed.
Lemma lem189437 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem189438 (b : nat) (a : nat) (n : nat) (h1 : term33 b a n) : (term26 a) = True.
Proof. exact (TRANS (@lem189435 b a n h1) (@lem189437)). Qed.
Lemma lem189439 (b : nat) (a : nat) (n : nat) (h1 : term33 b a n) : True = (term26 a).
Proof. exact (SYM (@lem189438 b a n h1)). Qed.
Lemma lem189440 (b : nat) (a : nat) (n : nat) (h1 : term33 b a n) : term26 a.
Proof. exact (EQ_MP (@lem189439 b a n h1) (@lem0)). Qed.
Lemma lem189441 (b : nat) (a : nat) (n : nat) (h1 : term33 b a n) : (term27 b a n) = (term28 b a n).
Proof. exact (@lem189431 b a n (@lem189440 b a n h1)). Qed.
Lemma lem189443 (n : nat) (m : nat) (p : nat) : (term18 m n p) = (term19 n m p).
Proof. exact (EQ_MP (@lem189362 n m p) (@lem189361 n m p)). Qed.
Lemma lem189444 (n : nat) (a : nat) : (term41 a n) = (term42 n a).
Proof. exact (@lem189443 n a term43). Qed.
Lemma lem189446 (m : nat) : (term12 m) = m.
Proof. exact (EQ_MP (@lem189341 m) (@lem189340 m)). Qed.
Lemma lem189447 (a : nat) : (term12 a) = a.
Proof. exact (@lem189446 a). Qed.
Lemma lem189448 (a : nat) (n : nat) : (term44 a n) = (term44 a n).
Proof. exact (eq_refl (term44 a n)). Qed.
Lemma lem189449 (n : nat) (a : nat) : (term42 n a) = (term45 n a).
Proof. exact (MK_COMB (@lem189448 a n) (@lem189447 a)). Qed.
Lemma lem189450 (n : nat) (a : nat) : (term41 a n) = (term45 n a).
Proof. exact (TRANS (@lem189444 n a) (@lem189449 n a)). Qed.
Lemma lem189451 (b : nat) : (Peano.lt b) = (Peano.lt b).
Proof. exact (eq_refl (Peano.lt b)). Qed.
Lemma lem189452 (b : nat) (n : nat) (a : nat) : (term28 b a n) = (term46 b n a).
Proof. exact (MK_COMB (@lem189451 b) (@lem189450 n a)). Qed.
Lemma lem189453 (b : nat) (a : nat) (n : nat) (h1 : term33 b a n) : (term27 b a n) = (term46 b n a).
Proof. exact (TRANS (@lem189441 b a n h1) (@lem189452 b n a)). Qed.
Lemma lem189454 (b : nat) (n : nat) (a : nat) : term47 b n a.
Proof. exact (fun h0 : term33 b a n => @lem189453 b a n h0). Qed.
Lemma lem189455 (b : nat) (n : nat) (a : nat) : term48 b n a.
Proof. exact (@lem189411 b a n (term46 b n a)). Qed.
Lemma lem189456 (b : nat) (n : nat) (a : nat) : (term49 b a n) = (term50 b n a).
Proof. exact (@lem189455 b n a (@lem189454 b n a)). Qed.
Lemma lem189503 (b : nat) (a : nat) : (term51 b a) = (term52 b a).
Proof. exact (fun_ext (fun n : nat => @lem189456 b n a)). Qed.
Lemma lem189550 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem189551 (b : nat) (a : nat) : (term53 b a) = (term54 b a).
Proof. exact (MK_COMB (@lem189550) (@lem189503 b a)). Qed.
Lemma lem189602 (a : nat) : (term55 a) = (term56 a).
Proof. exact (fun_ext (fun b : nat => @lem189551 b a)). Qed.
Lemma lem189653 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem189654 (a : nat) : (term57 a) = (term58 a).
Proof. exact (MK_COMB (@lem189653) (@lem189602 a)). Qed.
Lemma lem189709 : term59 = term60.
Proof. exact (fun_ext (fun a : nat => @lem189654 a)). Qed.
Lemma lem189764 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem189765 : term61 = term62.
Proof. exact (MK_COMB (@lem189764) (@lem189709)). Qed.
Lemma lem189824 : term62 = term61.
Proof. exact (SYM (@lem189765)). Qed.
Lemma lem189826 (p : Prop) : p = (term63 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem189827 : term62 = term64.
Proof. exact (@lem189826 term62). Qed.
Lemma lem189828 : term64 = term62.
Proof. exact (SYM (@lem189827)). Qed.
Lemma lem189829 (h1 : term65) : term65.
Proof. exact (h1). Qed.
Lemma lem189832 (h1 : term66) : term66.
Proof. exact (h1). Qed.
Lemma lem189833 : term67.
Proof. exact (fun h0 : term66 => @lem189832 h0). Qed.
Lemma lem189834 (h1 : term67) : term67.
Proof. exact (h1). Qed.
Lemma lem189835 (h1 : term66) : term66.
Proof. exact (h1). Qed.
Lemma lem189836 (h1 : term66) (h2 : term67) : term66.
Proof. exact (@lem189834 h2 (@lem189835 h1)). Qed.
Lemma lem189837 (h1 : term66) : term68.
Proof. exact (fun h0 : term67 => @lem189836 h1 h0). Qed.
Lemma lem189838 (h1 : term67) : term67.
Proof. exact (h1). Qed.
Lemma lem189839 (h1 : term66) (h2 : term67) : term66.
Proof. exact (@lem189837 h1 (@lem189838 h2)). Qed.
Lemma lem189840 (h1 : term67) : term67.
Proof. exact (fun h0 : term66 => @lem189839 h0 h1). Qed.
Lemma lem189841 : term69.
Proof. exact (fun h0 : term67 => @lem189840 h0). Qed.
Lemma lem189844 : term67.
Proof. exact (@lem189841 (@lem189833)). Qed.
Lemma lem189888 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem189889 : term70 = term71.
Proof. exact (@lem189888 term72). Qed.
Lemma lem189898 : term73 = term73.
Proof. exact (eq_refl term73). Qed.
Lemma lem189899 : term74 = term75.
Proof. exact (MK_COMB (@lem189898) (@lem189889)). Qed.
Lemma lem189902 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem189903 : term77 = term78.
Proof. exact (MK_COMB (@lem189902) (@lem189899)). Qed.
Lemma lem189906 : term79 = term79.
Proof. exact (eq_refl term79). Qed.
Lemma lem189913 : term66 = term80.
Proof. exact (MK_COMB (@lem189906) (@lem189903)). Qed.
Lemma lem189918 (m : nat) (n : nat) : ((term81 m n) = (term82 n)) = ((term81 m n) = (term82 n)).
Proof. exact (eq_refl ((term81 m n) = (term82 n))). Qed.
Lemma lem189919 (m : nat) : (term83 m) = (term83 m).
Proof. exact (fun_ext (fun n : nat => @lem189918 m n)). Qed.
Lemma lem189920 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem189921 (m : nat) : (term84 m) = (term84 m).
Proof. exact (MK_COMB (@lem189920) (@lem189919 m)). Qed.
Lemma lem189922 : term85 = term85.
Proof. exact (fun_ext (fun m : nat => @lem189921 m)). Qed.
Lemma lem189923 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem189924 : term72 = term72.
Proof. exact (MK_COMB (@lem189923) (@lem189922)). Qed.
Lemma lem189925 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem189926 : term71 = term71.
Proof. exact (MK_COMB (@lem189925) (@lem189924)). Qed.
Lemma lem189933 (n : nat) : ((term82 n) = (term26 n)) = ((term82 n) = (term26 n)).
Proof. exact (eq_refl ((term82 n) = (term26 n))). Qed.
Lemma lem189934 : term86 = term86.
Proof. exact (fun_ext (fun n : nat => @lem189933 n)). Qed.
Lemma lem189935 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem189936 : term87 = term87.
Proof. exact (MK_COMB (@lem189935) (@lem189934)). Qed.
Lemma lem189937 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem189938 : term73 = term73.
Proof. exact (MK_COMB (@lem189937) (@lem189936)). Qed.
Lemma lem189939 : term75 = term75.
Proof. exact (MK_COMB (@lem189938) (@lem189926)). Qed.
Lemma lem189948 (n : nat) (m : nat) (p : nat) : (term88 n m p) = (term88 n m p).
Proof. exact (eq_refl (term88 n m p)). Qed.
Lemma lem189949 (n : nat) (m : nat) : (term89 n m) = (term89 n m).
Proof. exact (fun_ext (fun p : nat => @lem189948 n m p)). Qed.
Lemma lem189950 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem189951 (n : nat) (m : nat) : (term90 n m) = (term90 n m).
Proof. exact (MK_COMB (@lem189950) (@lem189949 n m)). Qed.
Lemma lem189952 (m : nat) : (term91 m) = (term91 m).
Proof. exact (fun_ext (fun n : nat => @lem189951 n m)). Qed.
Lemma lem189953 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem189954 (m : nat) : (term92 m) = (term92 m).
Proof. exact (MK_COMB (@lem189953) (@lem189952 m)). Qed.
Lemma lem189955 : term93 = term93.
Proof. exact (fun_ext (fun m : nat => @lem189954 m)). Qed.
Lemma lem189956 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem189957 : term94 = term94.
Proof. exact (MK_COMB (@lem189956) (@lem189955)). Qed.
Lemma lem189958 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem189959 : term76 = term76.
Proof. exact (MK_COMB (@lem189958) (@lem189957)). Qed.
Lemma lem189960 : term78 = term78.
Proof. exact (MK_COMB (@lem189959) (@lem189939)). Qed.
Lemma lem189971 (b : nat) (n : nat) (a : nat) : (term50 b n a) = (term50 b n a).
Proof. exact (eq_refl (term50 b n a)). Qed.
Lemma lem189972 (b : nat) (a : nat) : (term52 b a) = (term52 b a).
Proof. exact (fun_ext (fun n : nat => @lem189971 b n a)). Qed.
Lemma lem189973 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem189974 (b : nat) (a : nat) : (term54 b a) = (term54 b a).
Proof. exact (MK_COMB (@lem189973) (@lem189972 b a)). Qed.
Lemma lem189975 (a : nat) : (term56 a) = (term56 a).
Proof. exact (fun_ext (fun b : nat => @lem189974 b a)). Qed.
Lemma lem189976 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem189977 (a : nat) : (term58 a) = (term58 a).
Proof. exact (MK_COMB (@lem189976) (@lem189975 a)). Qed.
Lemma lem189978 : term60 = term60.
Proof. exact (fun_ext (fun a : nat => @lem189977 a)). Qed.
Lemma lem189979 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem189980 : term62 = term62.
Proof. exact (MK_COMB (@lem189979) (@lem189978)). Qed.
Lemma lem189981 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem189982 : term65 = term65.
Proof. exact (MK_COMB (@lem189981) (@lem189980)). Qed.
Lemma lem189983 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem189984 : term79 = term79.
Proof. exact (MK_COMB (@lem189983) (@lem189982)). Qed.
Lemma lem189985 : term80 = term80.
Proof. exact (MK_COMB (@lem189984) (@lem189960)). Qed.
Lemma lem190056 : term66 = term80.
Proof. exact (TRANS (@lem189913) (@lem189985)). Qed.
Lemma lem190057 : term80 = term66.
Proof. exact (SYM (@lem190056)). Qed.
Lemma lem190058 (h1 : term65) : term65.
Proof. exact (h1). Qed.
Lemma lem190059 (h1 : term94) : term94.
Proof. exact (h1). Qed.
Lemma lem190060 (h1 : term87) : term87.
Proof. exact (h1). Qed.
Lemma lem190061 (h1 : term72) : term72.
Proof. exact (h1). Qed.
Lemma lem190072 (b : nat) (n : nat) (a : nat) : (term95 b n a) = (term96 b n a).
Proof. exact (@lem17362 (term33 b a n) (term46 b n a)). Qed.
Lemma lem190073 (P : nat -> Prop) : (term97 P) = (term98 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem190074 (b : nat) (a : nat) : (term99 b a) = (term100 b a).
Proof. exact (@lem190073 (term52 b a)). Qed.
Lemma lem190075 (b : nat) (n : nat) (a : nat) : (term101 b a n) = (term50 b n a).
Proof. exact (eq_refl (term101 b a n)). Qed.
Lemma lem190076 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem190077 (b : nat) (n : nat) (a : nat) : (term102 b a n) = (term95 b n a).
Proof. exact (MK_COMB (@lem190076) (@lem190075 b n a)). Qed.
Lemma lem190078 (b : nat) (n : nat) (a : nat) : (term102 b a n) = (term96 b n a).
Proof. exact (TRANS (@lem190077 b n a) (@lem190072 b n a)). Qed.
Lemma lem190079 (b : nat) (a : nat) : (term103 b a) = (term104 b a).
Proof. exact (fun_ext (fun n : nat => @lem190078 b n a)). Qed.
Lemma lem190080 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem190081 (b : nat) (a : nat) : (term100 b a) = (term105 b a).
Proof. exact (MK_COMB (@lem190080) (@lem190079 b a)). Qed.
Lemma lem190082 (b : nat) (a : nat) : (term99 b a) = (term105 b a).
Proof. exact (TRANS (@lem190074 b a) (@lem190081 b a)). Qed.
Lemma lem190083 (P : nat -> Prop) : (term97 P) = (term98 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem190084 (a : nat) : (term106 a) = (term107 a).
Proof. exact (@lem190083 (term56 a)). Qed.
Lemma lem190085 (b : nat) (a : nat) : (term108 a b) = (term54 b a).
Proof. exact (eq_refl (term108 a b)). Qed.
Lemma lem190086 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem190087 (b : nat) (a : nat) : (term109 a b) = (term99 b a).
Proof. exact (MK_COMB (@lem190086) (@lem190085 b a)). Qed.
Lemma lem190088 (b : nat) (a : nat) : (term109 a b) = (term105 b a).
Proof. exact (TRANS (@lem190087 b a) (@lem190082 b a)). Qed.
Lemma lem190089 (a : nat) : (term110 a) = (term111 a).
Proof. exact (fun_ext (fun b : nat => @lem190088 b a)). Qed.
Lemma lem190090 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem190091 (a : nat) : (term107 a) = (term112 a).
Proof. exact (MK_COMB (@lem190090) (@lem190089 a)). Qed.
Lemma lem190092 (a : nat) : (term106 a) = (term112 a).
Proof. exact (TRANS (@lem190084 a) (@lem190091 a)). Qed.
Lemma lem190093 (P : nat -> Prop) : (term97 P) = (term98 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem190094 : term65 = term113.
Proof. exact (@lem190093 term60). Qed.
Lemma lem190095 (a : nat) : (term114 a) = (term58 a).
Proof. exact (eq_refl (term114 a)). Qed.
Lemma lem190096 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem190097 (a : nat) : (term115 a) = (term106 a).
Proof. exact (MK_COMB (@lem190096) (@lem190095 a)). Qed.
Lemma lem190098 (a : nat) : (term115 a) = (term112 a).
Proof. exact (TRANS (@lem190097 a) (@lem190092 a)). Qed.
Lemma lem190099 : term116 = term117.
Proof. exact (fun_ext (fun a : nat => @lem190098 a)). Qed.
Lemma lem190100 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem190101 : term113 = term118.
Proof. exact (MK_COMB (@lem190100) (@lem190099)). Qed.
Lemma lem190162 : term65 = term118.
Proof. exact (TRANS (@lem190094) (@lem190101)). Qed.
Lemma lem190163 (h1 : term65) : term118.
Proof. exact (EQ_MP (@lem190162) (@lem190058 h1)). Qed.
Lemma lem190170 (m : nat) (n : nat) (p : nat) : (term119 m n p) = (term120 m n p).
Proof. exact (@lem17045 (Peano.le m n) (Peano.lt n p)). Qed.
Lemma lem190171 (m : nat) (p : nat) : (Peano.lt m p) = (Peano.lt m p).
Proof. exact (eq_refl (Peano.lt m p)). Qed.
Lemma lem190172 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem190173 (m : nat) (n : nat) (p : nat) : (term121 m n p) = (term122 m n p).
Proof. exact (MK_COMB (@lem190172) (@lem190170 m n p)). Qed.
Lemma lem190174 (n : nat) (m : nat) (p : nat) : (term123 n m p) = (term124 n m p).
Proof. exact (MK_COMB (@lem190173 m n p) (@lem190171 m p)). Qed.
Lemma lem190175 (n : nat) (m : nat) (p : nat) : (term88 n m p) = (term123 n m p).
Proof. exact (@lem17265 (term125 m n p) (Peano.lt m p)). Qed.
Lemma lem190176 (n : nat) (m : nat) (p : nat) : (term88 n m p) = (term124 n m p).
Proof. exact (TRANS (@lem190175 n m p) (@lem190174 n m p)). Qed.
Lemma lem190177 (n : nat) (m : nat) : (term89 n m) = (term126 n m).
Proof. exact (fun_ext (fun p : nat => @lem190176 n m p)). Qed.
Lemma lem190178 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem190179 (n : nat) (m : nat) : (term90 n m) = (term127 n m).
Proof. exact (MK_COMB (@lem190178) (@lem190177 n m)). Qed.
Lemma lem190180 (m : nat) : (term91 m) = (term128 m).
Proof. exact (fun_ext (fun n : nat => @lem190179 n m)). Qed.
Lemma lem190181 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem190182 (m : nat) : (term92 m) = (term129 m).
Proof. exact (MK_COMB (@lem190181) (@lem190180 m)). Qed.
Lemma lem190183 : term93 = term130.
Proof. exact (fun_ext (fun m : nat => @lem190182 m)). Qed.
Lemma lem190184 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem190245 : term94 = term131.
Proof. exact (MK_COMB (@lem190184) (@lem190183)). Qed.
Lemma lem190246 (h1 : term94) : term131.
Proof. exact (EQ_MP (@lem190245) (@lem190059 h1)). Qed.
Lemma lem190252 (n : nat) : (term132 n) = (n = (NUMERAL 0)).
Proof. exact (@lem16933 (n = (NUMERAL 0))). Qed.
Lemma lem190255 (n : nat) : (term133 n) = (term133 n).
Proof. exact (eq_refl (term133 n)). Qed.
Lemma lem190257 (n : nat) : (term134 n) = (term134 n).
Proof. exact (eq_refl (term134 n)). Qed.
Lemma lem190258 (n : nat) : (term135 n) = (term136 n).
Proof. exact (MK_COMB (@lem190257 n) (@lem190252 n)). Qed.
Lemma lem190259 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem190260 (n : nat) : (term137 n) = (term138 n).
Proof. exact (MK_COMB (@lem190259) (@lem190258 n)). Qed.
Lemma lem190261 (n : nat) : (term139 n) = (term140 n).
Proof. exact (MK_COMB (@lem190260 n) (@lem190255 n)). Qed.
Lemma lem190262 (n : nat) : ((term82 n) = (term26 n)) = (term139 n).
Proof. exact (@lem17784 (term82 n) (term26 n)). Qed.
Lemma lem190263 (n : nat) : ((term82 n) = (term26 n)) = (term140 n).
Proof. exact (TRANS (@lem190262 n) (@lem190261 n)). Qed.
Lemma lem190264 : term86 = term141.
Proof. exact (fun_ext (fun n : nat => @lem190263 n)). Qed.
Lemma lem190265 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem190266 : term87 = term142.
Proof. exact (MK_COMB (@lem190265) (@lem190264)). Qed.
Lemma lem190268 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term143 A P Q) = (term144 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem190269 (P : nat -> Prop) (Q : nat -> Prop) : (term145 P Q) = (term146 P Q).
Proof. exact (@lem190268 nat P Q). Qed.
Lemma lem190270 : term147 = term148.
Proof. exact (@lem190269 term149 term150). Qed.
Lemma lem190271 (n : nat) : (term151 n) = (term136 n).
Proof. exact (eq_refl (term151 n)). Qed.
Lemma lem190272 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem190273 (n : nat) : (term152 n) = (term138 n).
Proof. exact (MK_COMB (@lem190272) (@lem190271 n)). Qed.
Lemma lem190274 (n : nat) : (term153 n) = (term133 n).
Proof. exact (eq_refl (term153 n)). Qed.
Lemma lem190275 (n : nat) : (term154 n) = (term140 n).
Proof. exact (MK_COMB (@lem190273 n) (@lem190274 n)). Qed.
Lemma lem190276 : term155 = term141.
Proof. exact (fun_ext (fun n : nat => @lem190275 n)). Qed.
Lemma lem190277 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem190278 : term147 = term142.
Proof. exact (MK_COMB (@lem190277) (@lem190276)). Qed.
Lemma lem190279 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem190280 : term156 = term157.
Proof. exact (MK_COMB (@lem190279) (@lem190278)). Qed.
Lemma lem190281 (n : nat) : (term151 n) = (term136 n).
Proof. exact (eq_refl (term151 n)). Qed.
Lemma lem190282 : term158 = term149.
Proof. exact (fun_ext (fun n : nat => @lem190281 n)). Qed.
Lemma lem190283 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem190284 : term159 = term160.
Proof. exact (MK_COMB (@lem190283) (@lem190282)). Qed.
Lemma lem190285 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem190286 : term161 = term162.
Proof. exact (MK_COMB (@lem190285) (@lem190284)). Qed.
Lemma lem190287 (n : nat) : (term153 n) = (term133 n).
Proof. exact (eq_refl (term153 n)). Qed.
Lemma lem190288 : term163 = term150.
Proof. exact (fun_ext (fun n : nat => @lem190287 n)). Qed.
Lemma lem190289 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem190290 : term164 = term165.
Proof. exact (MK_COMB (@lem190289) (@lem190288)). Qed.
Lemma lem190291 : term148 = term166.
Proof. exact (MK_COMB (@lem190286) (@lem190290)). Qed.
Lemma lem190292 : (term147 = term148) = (term142 = term166).
Proof. exact (MK_COMB (@lem190280) (@lem190291)). Qed.
Lemma lem190391 : term142 = term166.
Proof. exact (EQ_MP (@lem190292) (@lem190270)). Qed.
Lemma lem190392 : term87 = term166.
Proof. exact (TRANS (@lem190266) (@lem190391)). Qed.
Lemma lem190393 (h1 : term87) : term166.
Proof. exact (EQ_MP (@lem190392) (@lem190060 h1)). Qed.
Lemma lem190408 (m : nat) (n : nat) : ((term81 m n) = (term82 n)) = (term167 m n).
Proof. exact (@lem17784 (term81 m n) (term82 n)). Qed.
Lemma lem190409 (m : nat) : (term83 m) = (term168 m).
Proof. exact (fun_ext (fun n : nat => @lem190408 m n)). Qed.
Lemma lem190410 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem190411 (m : nat) : (term84 m) = (term169 m).
Proof. exact (MK_COMB (@lem190410) (@lem190409 m)). Qed.
Lemma lem190412 : term85 = term170.
Proof. exact (fun_ext (fun m : nat => @lem190411 m)). Qed.
Lemma lem190413 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem190414 : term72 = term171.
Proof. exact (MK_COMB (@lem190413) (@lem190412)). Qed.
Lemma lem190420 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term143 A P Q) = (term144 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem190421 (P : nat -> Prop) (Q : nat -> Prop) : (term145 P Q) = (term146 P Q).
Proof. exact (@lem190420 nat P Q). Qed.
Lemma lem190422 (m : nat) : (term172 m) = (term173 m).
Proof. exact (@lem190421 (term174 m) (term175 m)). Qed.
Lemma lem190423 (m : nat) (n : nat) : (term176 m n) = (term177 m n).
Proof. exact (eq_refl (term176 m n)). Qed.
Lemma lem190424 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem190425 (m : nat) (n : nat) : (term178 m n) = (term179 m n).
Proof. exact (MK_COMB (@lem190424) (@lem190423 m n)). Qed.
Lemma lem190426 (m : nat) (n : nat) : (term180 m n) = (term181 m n).
Proof. exact (eq_refl (term180 m n)). Qed.
Lemma lem190427 (m : nat) (n : nat) : (term182 m n) = (term167 m n).
Proof. exact (MK_COMB (@lem190425 m n) (@lem190426 m n)). Qed.
Lemma lem190428 (m : nat) : (term183 m) = (term168 m).
Proof. exact (fun_ext (fun n : nat => @lem190427 m n)). Qed.
Lemma lem190429 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem190430 (m : nat) : (term172 m) = (term169 m).
Proof. exact (MK_COMB (@lem190429) (@lem190428 m)). Qed.
Lemma lem190431 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem190432 (m : nat) : (term184 m) = (term185 m).
Proof. exact (MK_COMB (@lem190431) (@lem190430 m)). Qed.
Lemma lem190433 (m : nat) (n : nat) : (term176 m n) = (term177 m n).
Proof. exact (eq_refl (term176 m n)). Qed.
Lemma lem190434 (m : nat) : (term186 m) = (term174 m).
Proof. exact (fun_ext (fun n : nat => @lem190433 m n)). Qed.
Lemma lem190435 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem190436 (m : nat) : (term187 m) = (term188 m).
Proof. exact (MK_COMB (@lem190435) (@lem190434 m)). Qed.
Lemma lem190437 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem190438 (m : nat) : (term189 m) = (term190 m).
Proof. exact (MK_COMB (@lem190437) (@lem190436 m)). Qed.
Lemma lem190439 (m : nat) (n : nat) : (term180 m n) = (term181 m n).
Proof. exact (eq_refl (term180 m n)). Qed.
Lemma lem190440 (m : nat) : (term191 m) = (term175 m).
Proof. exact (fun_ext (fun n : nat => @lem190439 m n)). Qed.
Lemma lem190441 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem190442 (m : nat) : (term192 m) = (term193 m).
Proof. exact (MK_COMB (@lem190441) (@lem190440 m)). Qed.
Lemma lem190443 (m : nat) : (term173 m) = (term194 m).
Proof. exact (MK_COMB (@lem190438 m) (@lem190442 m)). Qed.
Lemma lem190444 (m : nat) : ((term172 m) = (term173 m)) = ((term169 m) = (term194 m)).
Proof. exact (MK_COMB (@lem190432 m) (@lem190443 m)). Qed.
Lemma lem190445 (m : nat) : (term169 m) = (term194 m).
Proof. exact (EQ_MP (@lem190444 m) (@lem190422 m)). Qed.
Lemma lem190542 : term170 = term195.
Proof. exact (fun_ext (fun m : nat => @lem190445 m)). Qed.
Lemma lem190543 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem190544 : term171 = term196.
Proof. exact (MK_COMB (@lem190543) (@lem190542)). Qed.
Lemma lem190546 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term143 A P Q) = (term144 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem190547 (P : nat -> Prop) (Q : nat -> Prop) : (term145 P Q) = (term146 P Q).
Proof. exact (@lem190546 nat P Q). Qed.
Lemma lem190548 : term197 = term198.
Proof. exact (@lem190547 term199 term200). Qed.
Lemma lem190549 (m : nat) : (term201 m) = (term188 m).
Proof. exact (eq_refl (term201 m)). Qed.
Lemma lem190550 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem190551 (m : nat) : (term202 m) = (term190 m).
Proof. exact (MK_COMB (@lem190550) (@lem190549 m)). Qed.
Lemma lem190552 (m : nat) : (term203 m) = (term193 m).
Proof. exact (eq_refl (term203 m)). Qed.
Lemma lem190553 (m : nat) : (term204 m) = (term194 m).
Proof. exact (MK_COMB (@lem190551 m) (@lem190552 m)). Qed.
Lemma lem190554 : term205 = term195.
Proof. exact (fun_ext (fun m : nat => @lem190553 m)). Qed.
Lemma lem190555 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem190556 : term197 = term196.
Proof. exact (MK_COMB (@lem190555) (@lem190554)). Qed.
Lemma lem190557 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem190558 : term206 = term207.
Proof. exact (MK_COMB (@lem190557) (@lem190556)). Qed.
Lemma lem190559 (m : nat) : (term201 m) = (term188 m).
Proof. exact (eq_refl (term201 m)). Qed.
Lemma lem190560 : term208 = term199.
Proof. exact (fun_ext (fun m : nat => @lem190559 m)). Qed.
Lemma lem190561 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem190562 : term209 = term210.
Proof. exact (MK_COMB (@lem190561) (@lem190560)). Qed.
Lemma lem190563 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem190564 : term211 = term212.
Proof. exact (MK_COMB (@lem190563) (@lem190562)). Qed.
Lemma lem190565 (m : nat) : (term203 m) = (term193 m).
Proof. exact (eq_refl (term203 m)). Qed.
Lemma lem190566 : term213 = term200.
Proof. exact (fun_ext (fun m : nat => @lem190565 m)). Qed.
Lemma lem190567 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem190568 : term214 = term215.
Proof. exact (MK_COMB (@lem190567) (@lem190566)). Qed.
Lemma lem190569 : term198 = term216.
Proof. exact (MK_COMB (@lem190564) (@lem190568)). Qed.
Lemma lem190570 : (term197 = term198) = (term196 = term216).
Proof. exact (MK_COMB (@lem190558) (@lem190569)). Qed.
Lemma lem190571 : term196 = term216.
Proof. exact (EQ_MP (@lem190570) (@lem190548)). Qed.
Lemma lem190678 : term171 = term216.
Proof. exact (TRANS (@lem190544) (@lem190571)). Qed.
Lemma lem190679 : term72 = term216.
Proof. exact (TRANS (@lem190414) (@lem190678)). Qed.
Lemma lem190680 (h1 : term72) : term216.
Proof. exact (EQ_MP (@lem190679) (@lem190061 h1)). Qed.
Lemma lem190681 (a : nat) (h1 : term112 a) : term112 a.
Proof. exact (h1). Qed.
Lemma lem190682 (b : nat) (a : nat) (h1 : term105 b a) : term105 b a.
Proof. exact (h1). Qed.
Lemma lem190708 (n : nat) (m : nat) (p : nat) : (term124 n m p) = (term124 n m p).
Proof. exact (eq_refl (term124 n m p)). Qed.
Lemma lem190709 (n : nat) (m : nat) : (term126 n m) = (term126 n m).
Proof. exact (fun_ext (fun p : nat => @lem190708 n m p)). Qed.
Lemma lem190710 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem190711 (n : nat) (m : nat) : (term127 n m) = (term127 n m).
Proof. exact (MK_COMB (@lem190710) (@lem190709 n m)). Qed.
Lemma lem190712 (m : nat) : (term128 m) = (term128 m).
Proof. exact (fun_ext (fun n : nat => @lem190711 n m)). Qed.
Lemma lem190713 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem190714 (m : nat) : (term129 m) = (term129 m).
Proof. exact (MK_COMB (@lem190713) (@lem190712 m)). Qed.
Lemma lem190715 : term130 = term130.
Proof. exact (fun_ext (fun m : nat => @lem190714 m)). Qed.
Lemma lem190716 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem190717 : term131 = term131.
Proof. exact (MK_COMB (@lem190716) (@lem190715)). Qed.
Lemma lem190718 (h1 : term94) : term131.
Proof. exact (EQ_MP (@lem190717) (@lem190246 h1)). Qed.
Lemma lem190739 (n : nat) : (term133 n) = (term133 n).
Proof. exact (eq_refl (term133 n)). Qed.
Lemma lem190740 : term150 = term150.
Proof. exact (fun_ext (fun n : nat => @lem190739 n)). Qed.
Lemma lem190741 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem190742 : term165 = term165.
Proof. exact (MK_COMB (@lem190741) (@lem190740)). Qed.
Lemma lem190759 (n : nat) : (term136 n) = (term136 n).
Proof. exact (eq_refl (term136 n)). Qed.
Lemma lem190760 : term149 = term149.
Proof. exact (fun_ext (fun n : nat => @lem190759 n)). Qed.
Lemma lem190761 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem190762 : term160 = term160.
Proof. exact (MK_COMB (@lem190761) (@lem190760)). Qed.
Lemma lem190763 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem190764 : term162 = term162.
Proof. exact (MK_COMB (@lem190763) (@lem190762)). Qed.
Lemma lem190765 : term166 = term166.
Proof. exact (MK_COMB (@lem190764) (@lem190742)). Qed.
Lemma lem190766 (h1 : term87) : term166.
Proof. exact (EQ_MP (@lem190765) (@lem190393 h1)). Qed.
Lemma lem190787 (m : nat) (n : nat) : (term181 m n) = (term181 m n).
Proof. exact (eq_refl (term181 m n)). Qed.
Lemma lem190788 (m : nat) : (term175 m) = (term175 m).
Proof. exact (fun_ext (fun n : nat => @lem190787 m n)). Qed.
Lemma lem190789 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem190790 (m : nat) : (term193 m) = (term193 m).
Proof. exact (MK_COMB (@lem190789) (@lem190788 m)). Qed.
Lemma lem190791 : term200 = term200.
Proof. exact (fun_ext (fun m : nat => @lem190790 m)). Qed.
Lemma lem190792 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem190793 : term215 = term215.
Proof. exact (MK_COMB (@lem190792) (@lem190791)). Qed.
Lemma lem190814 (m : nat) (n : nat) : (term177 m n) = (term177 m n).
Proof. exact (eq_refl (term177 m n)). Qed.
Lemma lem190815 (m : nat) : (term174 m) = (term174 m).
Proof. exact (fun_ext (fun n : nat => @lem190814 m n)). Qed.
Lemma lem190816 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem190817 (m : nat) : (term188 m) = (term188 m).
Proof. exact (MK_COMB (@lem190816) (@lem190815 m)). Qed.
Lemma lem190818 : term199 = term199.
Proof. exact (fun_ext (fun m : nat => @lem190817 m)). Qed.
Lemma lem190819 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem190820 : term210 = term210.
Proof. exact (MK_COMB (@lem190819) (@lem190818)). Qed.
Lemma lem190821 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem190822 : term212 = term212.
Proof. exact (MK_COMB (@lem190821) (@lem190820)). Qed.
Lemma lem190823 : term216 = term216.
Proof. exact (MK_COMB (@lem190822) (@lem190793)). Qed.
Lemma lem190824 (h1 : term72) : term216.
Proof. exact (EQ_MP (@lem190823) (@lem190680 h1)). Qed.
Lemma lem190864 (b : nat) (n : nat) (a : nat) (h1 : term96 b n a) : term96 b n a.
Proof. exact (h1). Qed.
Lemma lem190866 (b : nat) (n : nat) (a : nat) (h1 : term96 b n a) : term33 b a n.
Proof. exact (proj1 (@lem190864 b n a h1)). Qed.
Lemma lem190870 (h1 : term72) : term210.
Proof. exact (proj1 (@lem190824 h1)). Qed.
Lemma lem190872 (h1 : term87) : term160.
Proof. exact (proj1 (@lem190766 h1)). Qed.
Lemma lem190886 (n : nat) (m : nat) (p : nat) : (term124 n m p) = (term124 n m p).
Proof. exact (eq_refl (term124 n m p)). Qed.
Lemma lem190887 (n : nat) (m : nat) : (term126 n m) = (term126 n m).
Proof. exact (fun_ext (fun p : nat => @lem190886 n m p)). Qed.
Lemma lem190888 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem190889 (n : nat) (m : nat) : (term127 n m) = (term127 n m).
Proof. exact (MK_COMB (@lem190888) (@lem190887 n m)). Qed.
Lemma lem190890 (m : nat) : (term128 m) = (term128 m).
Proof. exact (fun_ext (fun n : nat => @lem190889 n m)). Qed.
Lemma lem190891 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem190892 (m : nat) : (term129 m) = (term129 m).
Proof. exact (MK_COMB (@lem190891) (@lem190890 m)). Qed.
Lemma lem190893 : term130 = term130.
Proof. exact (fun_ext (fun m : nat => @lem190892 m)). Qed.
Lemma lem190894 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem190896 : term131 = term131.
Proof. exact (MK_COMB (@lem190894) (@lem190893)). Qed.
Lemma lem190897 (h1 : term94) : term131.
Proof. exact (EQ_MP (@lem190896) (@lem190718 h1)). Qed.
Lemma lem190917 (m : nat) (n : nat) : (term177 m n) = (term177 m n).
Proof. exact (eq_refl (term177 m n)). Qed.
Lemma lem190918 (m : nat) : (term174 m) = (term174 m).
Proof. exact (fun_ext (fun n : nat => @lem190917 m n)). Qed.
Lemma lem190919 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem190920 (m : nat) : (term188 m) = (term188 m).
Proof. exact (MK_COMB (@lem190919) (@lem190918 m)). Qed.
Lemma lem190921 : term199 = term199.
Proof. exact (fun_ext (fun m : nat => @lem190920 m)). Qed.
Lemma lem190922 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem190924 : term210 = term210.
Proof. exact (MK_COMB (@lem190922) (@lem190921)). Qed.
Lemma lem190925 (h1 : term72) : term210.
Proof. exact (EQ_MP (@lem190924) (@lem190870 h1)). Qed.
Lemma lem190949 (n : nat) : (term136 n) = (term136 n).
Proof. exact (eq_refl (term136 n)). Qed.
Lemma lem190950 : term149 = term149.
Proof. exact (fun_ext (fun n : nat => @lem190949 n)). Qed.
Lemma lem190951 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem190953 : term160 = term160.
Proof. exact (MK_COMB (@lem190951) (@lem190950)). Qed.
Lemma lem190954 (h1 : term87) : term160.
Proof. exact (EQ_MP (@lem190953) (@lem190872 h1)). Qed.
Lemma lem190968 (_3857 : nat) (h1 : term94) : term217 _3857.
Proof. exact (@lem190897 h1 _3857). Qed.
Lemma lem190969 (_3857 : nat) : (term217 _3857) = (term129 _3857).
Proof. exact (eq_refl (term217 _3857)). Qed.
Lemma lem190970 (_3857 : nat) (h1 : term94) : term129 _3857.
Proof. exact (EQ_MP (@lem190969 _3857) (@lem190968 _3857 h1)). Qed.
Lemma lem190971 (_3857 : nat) (_3858 : nat) (h1 : term94) : term218 _3857 _3858.
Proof. exact (@lem190970 _3857 h1 _3858). Qed.
Lemma lem190972 (_3858 : nat) (_3857 : nat) : (term218 _3857 _3858) = (term127 _3858 _3857).
Proof. exact (eq_refl (term218 _3857 _3858)). Qed.
Lemma lem190973 (_3858 : nat) (_3857 : nat) (h1 : term94) : term127 _3858 _3857.
Proof. exact (EQ_MP (@lem190972 _3858 _3857) (@lem190971 _3857 _3858 h1)). Qed.
Lemma lem190974 (_3858 : nat) (_3857 : nat) (_3859 : nat) (h1 : term94) : term219 _3858 _3857 _3859.
Proof. exact (@lem190973 _3858 _3857 h1 _3859). Qed.
Lemma lem190975 (_3858 : nat) (_3857 : nat) (_3859 : nat) : (term219 _3858 _3857 _3859) = (term124 _3858 _3857 _3859).
Proof. exact (eq_refl (term219 _3858 _3857 _3859)). Qed.
Lemma lem190976 (_3858 : nat) (_3857 : nat) (_3859 : nat) (h1 : term94) : term124 _3858 _3857 _3859.
Proof. exact (EQ_MP (@lem190975 _3858 _3857 _3859) (@lem190974 _3858 _3857 _3859 h1)). Qed.
Lemma lem190977 (_3860 : nat) (h1 : term72) : term201 _3860.
Proof. exact (@lem190925 h1 _3860). Qed.
Lemma lem190978 (_3860 : nat) : (term201 _3860) = (term188 _3860).
Proof. exact (eq_refl (term201 _3860)). Qed.
Lemma lem190979 (_3860 : nat) (h1 : term72) : term188 _3860.
Proof. exact (EQ_MP (@lem190978 _3860) (@lem190977 _3860 h1)). Qed.
Lemma lem190980 (_3860 : nat) (_3861 : nat) (h1 : term72) : term176 _3860 _3861.
Proof. exact (@lem190979 _3860 h1 _3861). Qed.
Lemma lem190981 (_3860 : nat) (_3861 : nat) : (term176 _3860 _3861) = (term177 _3860 _3861).
Proof. exact (eq_refl (term176 _3860 _3861)). Qed.
Lemma lem190989 (_3864 : nat) (h1 : term87) : term151 _3864.
Proof. exact (@lem190954 h1 _3864). Qed.
Lemma lem190990 (_3864 : nat) : (term151 _3864) = (term136 _3864).
Proof. exact (eq_refl (term151 _3864)). Qed.
Lemma lem191005 (_3858 : nat) (_3857 : nat) (_3859 : nat) : (term124 _3858 _3857 _3859) = (term220 _3858 _3857 _3859).
Proof. exact (@lem189320 (term221 _3857 _3858) (term222 _3858 _3859) (Peano.lt _3857 _3859)). Qed.
Lemma lem191006 (_3858 : nat) (_3857 : nat) (_3859 : nat) (h1 : term94) : term220 _3858 _3857 _3859.
Proof. exact (EQ_MP (@lem191005 _3858 _3857 _3859) (@lem190976 _3858 _3857 _3859 h1)). Qed.
Lemma lem191010 (b : nat) (n : nat) (a : nat) (h1 : term96 b n a) : term26 a.
Proof. exact (proj1 (@lem190866 b n a h1)). Qed.
Lemma lem191018 (_3860 : nat) (_3861 : nat) (h1 : term72) : term177 _3860 _3861.
Proof. exact (EQ_MP (@lem190981 _3860 _3861) (@lem190980 _3860 _3861 h1)). Qed.
Lemma lem191030 (_3864 : nat) (h1 : term87) : term136 _3864.
Proof. exact (EQ_MP (@lem190990 _3864) (@lem190989 _3864 h1)). Qed.
Lemma lem191116 (b : nat) (n : nat) (a : nat) (h1 : term96 b n a) : term223 b a n.
Proof. exact (proj2 (@lem190866 b n a h1)). Qed.
Lemma lem191117 (b : nat) (n : nat) (a : nat) (h1 : term96 b n a) : term224 b a n.
Proof. exact (fun h0 : term225 b a n => @lem191116 b n a h1). Qed.
Lemma lem191119 (p : Prop) : (term226 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem191120 (b : nat) (a : nat) (n : nat) : (term224 b a n) = (term223 b a n).
Proof. exact (@lem191119 (term223 b a n)). Qed.
Lemma lem191121 (b : nat) (n : nat) (a : nat) (h1 : term96 b n a) : term223 b a n.
Proof. exact (EQ_MP (@lem191120 b a n) (@lem191117 b n a h1)). Qed.
Lemma lem191123 (b : nat) (n : nat) (a : nat) (h1 : term96 b n a) : term227 b n a.
Proof. exact (proj2 (@lem190864 b n a h1)). Qed.
Lemma lem191124 (b : nat) (n : nat) (a : nat) (h1 : term96 b n a) : term228 b n a.
Proof. exact (fun h0 : term46 b n a => @lem191123 b n a h1). Qed.
Lemma lem191126 (p : Prop) : (term229 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem191127 (b : nat) (n : nat) (a : nat) : (term228 b n a) = (term227 b n a).
Proof. exact (@lem191126 (term46 b n a)). Qed.
Lemma lem191128 (b : nat) (n : nat) (a : nat) (h1 : term96 b n a) : term227 b n a.
Proof. exact (EQ_MP (@lem191127 b n a) (@lem191124 b n a h1)). Qed.
Lemma lem191134 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem191135 (_3858 : nat) (_3857 : nat) (_3859 : nat) : (term220 _3858 _3857 _3859) = (term230 _3858 _3857 _3859).
Proof. exact (@lem191134 (term222 _3858 _3859) (term221 _3857 _3858) (Peano.lt _3857 _3859)). Qed.
Lemma lem191149 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem191150 (_3859 : nat) (_3857 : nat) (_3858 : nat) : (term231 _3858 _3857 _3859) = (term232 _3859 _3857 _3858).
Proof. exact (@lem191149 (Peano.lt _3857 _3859) (term221 _3857 _3858)). Qed.
Lemma lem191156 (_3858 : nat) (_3859 : nat) : (term233 _3858 _3859) = (term233 _3858 _3859).
Proof. exact (eq_refl (term233 _3858 _3859)). Qed.
Lemma lem191157 (_3859 : nat) (_3857 : nat) (_3858 : nat) : (term230 _3858 _3857 _3859) = (term234 _3859 _3857 _3858).
Proof. exact (MK_COMB (@lem191156 _3858 _3859) (@lem191150 _3859 _3857 _3858)). Qed.
Lemma lem191161 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem191162 (_3859 : nat) (_3857 : nat) (_3858 : nat) : (term234 _3859 _3857 _3858) = (term235 _3859 _3857 _3858).
Proof. exact (@lem191161 (Peano.lt _3857 _3859) (term222 _3858 _3859) (term221 _3857 _3858)). Qed.
Lemma lem191178 (_3859 : nat) (_3857 : nat) (_3858 : nat) : (term230 _3858 _3857 _3859) = (term235 _3859 _3857 _3858).
Proof. exact (TRANS (@lem191157 _3859 _3857 _3858) (@lem191162 _3859 _3857 _3858)). Qed.
Lemma lem191179 (_3859 : nat) (_3857 : nat) (_3858 : nat) : (term220 _3858 _3857 _3859) = (term235 _3859 _3857 _3858).
Proof. exact (TRANS (@lem191135 _3858 _3857 _3859) (@lem191178 _3859 _3857 _3858)). Qed.
Lemma lem191180 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem191181 (_3859 : nat) (_3857 : nat) (_3858 : nat) : (term236 _3858 _3857 _3859) = (term237 _3859 _3857 _3858).
Proof. exact (MK_COMB (@lem191180) (@lem191179 _3859 _3857 _3858)). Qed.
Lemma lem191195 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem191196 (_3859 : nat) (_3857 : nat) (_3858 : nat) : (term231 _3858 _3857 _3859) = (term232 _3859 _3857 _3858).
Proof. exact (@lem191195 (Peano.lt _3857 _3859) (term221 _3857 _3858)). Qed.
Lemma lem191202 (_3858 : nat) (_3859 : nat) : (term233 _3858 _3859) = (term233 _3858 _3859).
Proof. exact (eq_refl (term233 _3858 _3859)). Qed.
Lemma lem191203 (_3859 : nat) (_3857 : nat) (_3858 : nat) : (term230 _3858 _3857 _3859) = (term234 _3859 _3857 _3858).
Proof. exact (MK_COMB (@lem191202 _3858 _3859) (@lem191196 _3859 _3857 _3858)). Qed.
Lemma lem191207 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem191208 (_3859 : nat) (_3857 : nat) (_3858 : nat) : (term234 _3859 _3857 _3858) = (term235 _3859 _3857 _3858).
Proof. exact (@lem191207 (Peano.lt _3857 _3859) (term222 _3858 _3859) (term221 _3857 _3858)). Qed.
Lemma lem191224 (_3859 : nat) (_3857 : nat) (_3858 : nat) : (term230 _3858 _3857 _3859) = (term235 _3859 _3857 _3858).
Proof. exact (TRANS (@lem191203 _3859 _3857 _3858) (@lem191208 _3859 _3857 _3858)). Qed.
Lemma lem191225 (_3859 : nat) (_3857 : nat) (_3858 : nat) : ((term220 _3858 _3857 _3859) = (term230 _3858 _3857 _3859)) = ((term235 _3859 _3857 _3858) = (term235 _3859 _3857 _3858)).
Proof. exact (MK_COMB (@lem191181 _3859 _3857 _3858) (@lem191224 _3859 _3857 _3858)). Qed.
Lemma lem191227 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem191228 (x : Prop) : (x = x) = True.
Proof. exact (@lem191227 Prop x). Qed.
Lemma lem191229 (_3859 : nat) (_3857 : nat) (_3858 : nat) : ((term235 _3859 _3857 _3858) = (term235 _3859 _3857 _3858)) = True.
Proof. exact (@lem191228 (term235 _3859 _3857 _3858)). Qed.
Lemma lem191230 (_3858 : nat) (_3857 : nat) (_3859 : nat) : ((term220 _3858 _3857 _3859) = (term230 _3858 _3857 _3859)) = True.
Proof. exact (TRANS (@lem191225 _3859 _3857 _3858) (@lem191229 _3859 _3857 _3858)). Qed.
Lemma lem191231 (_3858 : nat) (_3857 : nat) (_3859 : nat) : True = ((term220 _3858 _3857 _3859) = (term230 _3858 _3857 _3859)).
Proof. exact (SYM (@lem191230 _3858 _3857 _3859)). Qed.
Lemma lem191232 (_3858 : nat) (_3857 : nat) (_3859 : nat) : (term220 _3858 _3857 _3859) = (term230 _3858 _3857 _3859).
Proof. exact (EQ_MP (@lem191231 _3858 _3857 _3859) (@lem0)). Qed.
Lemma lem191233 (_3858 : nat) (_3857 : nat) (_3859 : nat) (h1 : term94) : term230 _3858 _3857 _3859.
Proof. exact (EQ_MP (@lem191232 _3858 _3857 _3859) (@lem191006 _3858 _3857 _3859 h1)). Qed.
Lemma lem191235 (b : Prop) (a : Prop) : (a \/ b) = (term238 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem191236 (_3857 : nat) (_3858 : nat) (_3859 : nat) : (term230 _3858 _3857 _3859) = (term239 _3857 _3858 _3859).
Proof. exact (@lem191235 (term231 _3858 _3857 _3859) (term222 _3858 _3859)). Qed.
Lemma lem191238 (a : Prop) (b : Prop) : (term240 a b) = (term241 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem191239 (_3858 : nat) (_3857 : nat) (_3859 : nat) : (term242 _3858 _3857 _3859) = (term243 _3858 _3857 _3859).
Proof. exact (@lem191238 (term221 _3857 _3858) (Peano.lt _3857 _3859)). Qed.
Lemma lem191241 (a : Prop) : (term244 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem191242 (_3857 : nat) (_3858 : nat) : (term245 _3857 _3858) = (Peano.le _3857 _3858).
Proof. exact (@lem191241 (Peano.le _3857 _3858)). Qed.
Lemma lem191243 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem191244 (_3857 : nat) (_3858 : nat) : (term246 _3857 _3858) = (term247 _3857 _3858).
Proof. exact (MK_COMB (@lem191243) (@lem191242 _3857 _3858)). Qed.
Lemma lem191245 (_3857 : nat) (_3859 : nat) : (term222 _3857 _3859) = (term222 _3857 _3859).
Proof. exact (eq_refl (term222 _3857 _3859)). Qed.
Lemma lem191246 (_3858 : nat) (_3857 : nat) (_3859 : nat) : (term243 _3858 _3857 _3859) = (term248 _3858 _3857 _3859).
Proof. exact (MK_COMB (@lem191244 _3857 _3858) (@lem191245 _3857 _3859)). Qed.
Lemma lem191247 (_3858 : nat) (_3857 : nat) (_3859 : nat) : (term242 _3858 _3857 _3859) = (term248 _3858 _3857 _3859).
Proof. exact (TRANS (@lem191239 _3858 _3857 _3859) (@lem191246 _3858 _3857 _3859)). Qed.
Lemma lem191248 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem191249 (_3858 : nat) (_3857 : nat) (_3859 : nat) : (term249 _3858 _3857 _3859) = (term250 _3858 _3857 _3859).
Proof. exact (MK_COMB (@lem191248) (@lem191247 _3858 _3857 _3859)). Qed.
Lemma lem191250 (_3858 : nat) (_3859 : nat) : (term222 _3858 _3859) = (term222 _3858 _3859).
Proof. exact (eq_refl (term222 _3858 _3859)). Qed.
Lemma lem191251 (_3857 : nat) (_3858 : nat) (_3859 : nat) : (term239 _3857 _3858 _3859) = (term251 _3857 _3858 _3859).
Proof. exact (MK_COMB (@lem191249 _3858 _3857 _3859) (@lem191250 _3858 _3859)). Qed.
Lemma lem191252 (_3857 : nat) (_3858 : nat) (_3859 : nat) : (term230 _3858 _3857 _3859) = (term251 _3857 _3858 _3859).
Proof. exact (TRANS (@lem191236 _3857 _3858 _3859) (@lem191251 _3857 _3858 _3859)). Qed.
Lemma lem191254 (b : nat) (n : nat) (a : nat) (h1 : term96 b n a) : term252 b n a.
Proof. exact (conj (@lem191121 b n a h1) (@lem191128 b n a h1)). Qed.
Lemma lem191256 (_3857 : nat) (_3858 : nat) (_3859 : nat) (h1 : term94) : term251 _3857 _3858 _3859.
Proof. exact (EQ_MP (@lem191252 _3857 _3858 _3859) (@lem191233 _3858 _3857 _3859 h1)). Qed.
Lemma lem191257 (b : nat) (n : nat) (a : nat) (h1 : term94) : term253 b n a.
Proof. exact (@lem191256 b (Nat.mul a n) (term45 n a) h1). Qed.
Lemma lem191260 (b : nat) (n : nat) (a : nat) (h1 : term94) (h2 : term96 b n a) : term254 n a.
Proof. exact (@lem191257 b n a h1 (@lem191254 b n a h2)). Qed.
Lemma lem191261 (b : nat) (n : nat) (a : nat) (h1 : term94) (h2 : term96 b n a) : term255 n a.
Proof. exact (fun h0 : term256 n a => @lem191260 b n a h1 h2). Qed.
Lemma lem191263 (p : Prop) : (term229 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem191264 (n : nat) (a : nat) : (term255 n a) = (term254 n a).
Proof. exact (@lem191263 (term256 n a)). Qed.
Lemma lem191265 (b : nat) (n : nat) (a : nat) (h1 : term94) (h2 : term96 b n a) : term254 n a.
Proof. exact (EQ_MP (@lem191264 n a) (@lem191261 b n a h1 h2)). Qed.
Lemma lem191276 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem191277 (_3860 : nat) (_3861 : nat) : (term257 _3860 _3861) = (term177 _3860 _3861).
Proof. exact (@lem191276 (term81 _3860 _3861) (term258 _3861)). Qed.
Lemma lem191283 (_3860 : nat) (_3861 : nat) : (term259 _3860 _3861) = (term259 _3860 _3861).
Proof. exact (eq_refl (term259 _3860 _3861)). Qed.
Lemma lem191284 (_3860 : nat) (_3861 : nat) : ((term177 _3860 _3861) = (term257 _3860 _3861)) = ((term177 _3860 _3861) = (term177 _3860 _3861)).
Proof. exact (MK_COMB (@lem191283 _3860 _3861) (@lem191277 _3860 _3861)). Qed.
Lemma lem191286 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem191287 (x : Prop) : (x = x) = True.
Proof. exact (@lem191286 Prop x). Qed.
Lemma lem191288 (_3860 : nat) (_3861 : nat) : ((term177 _3860 _3861) = (term177 _3860 _3861)) = True.
Proof. exact (@lem191287 (term177 _3860 _3861)). Qed.
Lemma lem191289 (_3860 : nat) (_3861 : nat) : ((term177 _3860 _3861) = (term257 _3860 _3861)) = True.
Proof. exact (TRANS (@lem191284 _3860 _3861) (@lem191288 _3860 _3861)). Qed.
Lemma lem191290 (_3860 : nat) (_3861 : nat) : True = ((term177 _3860 _3861) = (term257 _3860 _3861)).
Proof. exact (SYM (@lem191289 _3860 _3861)). Qed.
Lemma lem191291 (_3860 : nat) (_3861 : nat) : (term177 _3860 _3861) = (term257 _3860 _3861).
Proof. exact (EQ_MP (@lem191290 _3860 _3861) (@lem0)). Qed.
Lemma lem191292 (_3860 : nat) (_3861 : nat) (h1 : term72) : term257 _3860 _3861.
Proof. exact (EQ_MP (@lem191291 _3860 _3861) (@lem191018 _3860 _3861 h1)). Qed.
Lemma lem191294 (b : Prop) (a : Prop) : (a \/ b) = (term238 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem191297 (_3860 : nat) (_3861 : nat) : (term257 _3860 _3861) = (term260 _3860 _3861).
Proof. exact (@lem191294 (term81 _3860 _3861) (term258 _3861)). Qed.
Lemma lem191300 (_3860 : nat) (_3861 : nat) (h1 : term72) : term260 _3860 _3861.
Proof. exact (EQ_MP (@lem191297 _3860 _3861) (@lem191292 _3860 _3861 h1)). Qed.
Lemma lem191301 (n : nat) (a : nat) (h1 : term72) : term261 n a.
Proof. exact (@lem191300 (Nat.mul a n) a h1). Qed.
Lemma lem191304 (b : nat) (n : nat) (a : nat) (h1 : term94) (h2 : term72) (h3 : term96 b n a) : term258 a.
Proof. exact (@lem191301 n a h2 (@lem191265 b n a h1 h3)). Qed.
Lemma lem191305 (b : nat) (n : nat) (a : nat) (h1 : term94) (h2 : term72) (h3 : term96 b n a) : term262 a.
Proof. exact (fun h0 : term82 a => @lem191304 b n a h1 h2 h3). Qed.
Lemma lem191307 (p : Prop) : (term229 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem191308 (a : nat) : (term262 a) = (term258 a).
Proof. exact (@lem191307 (term82 a)). Qed.
Lemma lem191309 (b : nat) (n : nat) (a : nat) (h1 : term94) (h2 : term72) (h3 : term96 b n a) : term258 a.
Proof. exact (EQ_MP (@lem191308 a) (@lem191305 b n a h1 h2 h3)). Qed.
Lemma lem191322 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem191323 (_3864 : nat) : (term263 _3864) = (term136 _3864).
Proof. exact (@lem191322 (term82 _3864) (_3864 = (NUMERAL 0))). Qed.
Lemma lem191331 (_3864 : nat) : (term264 _3864) = (term264 _3864).
Proof. exact (eq_refl (term264 _3864)). Qed.
Lemma lem191332 (_3864 : nat) : ((term136 _3864) = (term263 _3864)) = ((term136 _3864) = (term136 _3864)).
Proof. exact (MK_COMB (@lem191331 _3864) (@lem191323 _3864)). Qed.
Lemma lem191334 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem191335 (x : Prop) : (x = x) = True.
Proof. exact (@lem191334 Prop x). Qed.
Lemma lem191336 (_3864 : nat) : ((term136 _3864) = (term136 _3864)) = True.
Proof. exact (@lem191335 (term136 _3864)). Qed.
Lemma lem191337 (_3864 : nat) : ((term136 _3864) = (term263 _3864)) = True.
Proof. exact (TRANS (@lem191332 _3864) (@lem191336 _3864)). Qed.
Lemma lem191338 (_3864 : nat) : True = ((term136 _3864) = (term263 _3864)).
Proof. exact (SYM (@lem191337 _3864)). Qed.
Lemma lem191339 (_3864 : nat) : (term136 _3864) = (term263 _3864).
Proof. exact (EQ_MP (@lem191338 _3864) (@lem0)). Qed.
Lemma lem191340 (_3864 : nat) (h1 : term87) : term263 _3864.
Proof. exact (EQ_MP (@lem191339 _3864) (@lem191030 _3864 h1)). Qed.
Lemma lem191342 (b : Prop) (a : Prop) : (a \/ b) = (term238 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem191345 (_3864 : nat) : (term263 _3864) = (term265 _3864).
Proof. exact (@lem191342 (term82 _3864) (_3864 = (NUMERAL 0))). Qed.
Lemma lem191348 (_3864 : nat) (h1 : term87) : term265 _3864.
Proof. exact (EQ_MP (@lem191345 _3864) (@lem191340 _3864 h1)). Qed.
Lemma lem191349 (a : nat) (h1 : term87) : term265 a.
Proof. exact (@lem191348 a h1). Qed.
Lemma lem191352 (b : nat) (n : nat) (a : nat) (h1 : term94) (h2 : term72) (h3 : term87) (h4 : term96 b n a) : a = (NUMERAL 0).
Proof. exact (@lem191349 a h3 (@lem191309 b n a h1 h2 h4)). Qed.
Lemma lem191353 (b : nat) (n : nat) (a : nat) (h1 : term94) (h2 : term72) (h3 : term87) (h4 : term96 b n a) : term266 a.
Proof. exact (fun h0 : term26 a => @lem191352 b n a h1 h2 h3 h4). Qed.
Lemma lem191355 (p : Prop) : (term226 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem191356 (a : nat) : (term266 a) = (a = (NUMERAL 0)).
Proof. exact (@lem191355 (a = (NUMERAL 0))). Qed.
Lemma lem191357 (b : nat) (n : nat) (a : nat) (h1 : term94) (h2 : term72) (h3 : term87) (h4 : term96 b n a) : a = (NUMERAL 0).
Proof. exact (EQ_MP (@lem191356 a) (@lem191353 b n a h1 h2 h3 h4)). Qed.
Lemma lem191360 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem191362 (a : nat) : (term26 a) = (term267 a).
Proof. exact (@lem191360 (a = (NUMERAL 0))). Qed.
Lemma lem191365 (b : nat) (n : nat) (a : nat) (h1 : term96 b n a) : term267 a.
Proof. exact (EQ_MP (@lem191362 a) (@lem191010 b n a h1)). Qed.
Lemma lem191368 (b : nat) (n : nat) (a : nat) (h1 : term94) (h2 : term72) (h3 : term87) (h4 : term96 b n a) : False.
Proof. exact (@lem191365 b n a h4 (@lem191357 b n a h1 h2 h3 h4)). Qed.
Lemma lem191369 (b : nat) (n : nat) (a : nat) (h1 : term94) (h2 : term72) (h3 : term87) (h4 : term96 b n a) : term268.
Proof. exact (fun h0 : ~ False => @lem191368 b n a h1 h2 h3 h4). Qed.
Lemma lem191371 (p : Prop) : (term226 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem191372 : term268 = False.
Proof. exact (@lem191371 False). Qed.
Lemma lem191373 (b : nat) (n : nat) (a : nat) (h1 : term94) (h2 : term72) (h3 : term87) (h4 : term96 b n a) : False.
Proof. exact (EQ_MP (@lem191372) (@lem191369 b n a h1 h2 h3 h4)). Qed.
Lemma lem191374 (b : nat) (n : nat) (a : nat) (h1 : term94) (h2 : term72) (h3 : term87) (h4 : term96 b n a) : (term96 b n a) = False.
Proof. exact (prop_ext (fun h5 : term96 b n a => @lem191373 b n a h1 h2 h3 h4) (fun h5 : False => @lem190864 b n a h4)). Qed.
Lemma lem191375 (b : nat) (n : nat) (a : nat) (h1 : term94) (h2 : term72) (h3 : term87) (h4 : term96 b n a) : False.
Proof. exact (EQ_MP (@lem191374 b n a h1 h2 h3 h4) (@lem190864 b n a h4)). Qed.
Lemma lem191376 (b : nat) (a : nat) (h1 : term94) (h2 : term72) (h3 : term87) (h4 : term105 b a) : False.
Proof. exact (ex_elim (@lem190682 b a h4) (fun n : nat => fun h0 : term104 b a n => @lem191375 b n a h1 h2 h3 h0)). Qed.
Lemma lem191377 (a : nat) (h1 : term94) (h2 : term72) (h3 : term87) (h4 : term112 a) : False.
Proof. exact (ex_elim (@lem190681 a h4) (fun b : nat => fun h0 : term111 a b => @lem191376 b a h1 h2 h3 h0)). Qed.
Lemma lem191378 (h1 : term94) (h2 : term72) (h3 : term87) (h4 : term65) : False.
Proof. exact (ex_elim (@lem190163 h4) (fun a : nat => fun h0 : term117 a => @lem191377 a h1 h2 h3 h0)). Qed.
Lemma lem191379 (h1 : term94) (h2 : term87) (h3 : term65) : term70.
Proof. exact (fun h0 : term72 => @lem191378 h1 h0 h2 h3). Qed.
Lemma lem191380 : term70 = term71.
Proof. exact (@lem69 term72). Qed.
Lemma lem191381 (h1 : term94) (h2 : term87) (h3 : term65) : term71.
Proof. exact (EQ_MP (@lem191380) (@lem191379 h1 h2 h3)). Qed.
Lemma lem191382 (h1 : term94) (h2 : term65) : term75.
Proof. exact (fun h0 : term87 => @lem191381 h1 h0 h2). Qed.
Lemma lem191383 (h1 : term65) : term78.
Proof. exact (fun h0 : term94 => @lem191382 h0 h1). Qed.
Lemma lem191384 : term80.
Proof. exact (fun h0 : term65 => @lem191383 h0). Qed.
Lemma lem191385 : term66.
Proof. exact (EQ_MP (@lem190057) (@lem191384)). Qed.
Lemma lem191387 : term66.
Proof. exact (@lem189844 (@lem191385)). Qed.
Lemma lem191388 (h1 : term65) : term77.
Proof. exact (@lem191387 (@lem189829 h1)). Qed.
Lemma lem191389 (h1 : term65) : term74.
Proof. exact (@lem191388 h1 (@lem95173)). Qed.
Lemma lem191390 (h1 : term65) : term70.
Proof. exact (@lem191389 h1 (@lem98731)). Qed.
Lemma lem191391 (h1 : term65) : False.
Proof. exact (@lem191390 h1 (@lem100722)). Qed.
Lemma lem191392 (h1 : term65) : term65 = False.
Proof. exact (prop_ext (fun h2 : term65 => @lem191391 h1) (fun h2 : False => @lem189829 h1)). Qed.
Lemma lem191393 (h1 : term65) : False.
Proof. exact (EQ_MP (@lem191392 h1) (@lem189829 h1)). Qed.
Lemma lem191394 : term64.
Proof. exact (fun h0 : term65 => @lem191393 h0). Qed.
Lemma lem191395 : term62.
Proof. exact (EQ_MP (@lem189828) (@lem191394)). Qed.
Lemma lem191396 : term61.
Proof. exact (EQ_MP (@lem189824) (@lem191395)). Qed.
