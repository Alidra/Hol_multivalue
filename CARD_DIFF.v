Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CARD_DIFF_term_abbrevs.
Require Import CARD_UNION_EQ_spec.
Require Import DISJ_ACI_spec.
Require Import INT_POS_spec.
Require Import thm0_spec.
Require Import thm1006570_spec.
Require Import thm1007663_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm1032781_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1365106_spec.
Require Import thm1365406_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1367763_spec.
Require Import thm1386578_spec.
Require Import thm1393126_spec.
Require Import thm1396750_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm1842_spec.
Require Import thm1857_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm19158_spec.
Require Import thm19367_spec.
Require Import thm1980010_spec.
Require Import thm1980011_spec.
Require Import thm1980026_spec.
Require Import thm1980255_spec.
Require Import thm1980259_spec.
Require Import thm1980260_spec.
Require Import thm1980265_spec.
Require Import thm1980266_spec.
Require Import thm1981473_spec.
Require Import thm1981474_spec.
Require Import thm1981475_spec.
Require Import thm1981613_spec.
Require Import thm1982627_spec.
Require Import thm1982628_spec.
Require Import thm1982709_spec.
Require Import thm1982713_spec.
Require Import thm1982715_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982723_spec.
Require Import thm1982733_spec.
Require Import thm1982749_spec.
Require Import thm1982753_spec.
Require Import thm1982755_spec.
Require Import thm1982757_spec.
Require Import thm1982759_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm1988293_spec.
Require Import thm1988330_spec.
Require Import thm1988332_spec.
Require Import thm1988336_spec.
Require Import thm1988342_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm2318497_spec.
Require Import thm2318538_spec.
Require Import thm2318539_spec.
Require Import thm2318544_spec.
Require Import thm2318545_spec.
Require Import thm2318568_spec.
Require Import thm2318569_spec.
Require Import thm2318574_spec.
Require Import thm2318575_spec.
Require Import thm2318604_spec.
Require Import thm2841383_spec.
Require Import thm2841384_spec.
Require Import thm2841401_spec.
Require Import thm2841402_spec.
Require Import thm2841413_spec.
Require Import thm2841414_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211701_spec.
Require Import thm3211702_spec.
Require Import thm3211710_spec.
Require Import thm3211711_spec.
Require Import thm3211719_spec.
Require Import thm3211720_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm7_spec.
Require Import thm706885_spec.
Require Import thm912739_spec.
Require Import thm912803_spec.
Require Import thm940073_spec.
Require Import thm996237_spec.
Lemma lem3848247 {_99816 : Type'} (h1 : term0 _99816) : term0 _99816.
Proof. exact (h1). Qed.
Lemma lem3848248 {_99816 : Type'} (s : _99816 -> Prop) (h1 : term0 _99816) : term1 _99816 s.
Proof. exact (@lem3848247 _99816 h1 s). Qed.
Lemma lem3848249 {_99816 : Type'} (s : _99816 -> Prop) : (term1 _99816 s) = (term2 _99816 s).
Proof. exact (eq_refl (term1 _99816 s)). Qed.
Lemma lem3848250 {_99816 : Type'} (s : _99816 -> Prop) (h1 : term0 _99816) : term2 _99816 s.
Proof. exact (EQ_MP (@lem3848249 _99816 s) (@lem3848248 _99816 s h1)). Qed.
Lemma lem3848251 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (h1 : term0 _99816) : term3 _99816 s t.
Proof. exact (@lem3848250 _99816 s h1 t). Qed.
Lemma lem3848252 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) : (term3 _99816 s t) = (term4 _99816 s t).
Proof. exact (eq_refl (term3 _99816 s t)). Qed.
Lemma lem3848253 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (h1 : term0 _99816) : term4 _99816 s t.
Proof. exact (EQ_MP (@lem3848252 _99816 s t) (@lem3848251 _99816 s t h1)). Qed.
Lemma lem3848254 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) (h1 : term0 _99816) : term5 _99816 s t u.
Proof. exact (@lem3848253 _99816 s t h1 u). Qed.
Lemma lem3848255 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) : (term5 _99816 s t u) = (term6 _99816 s t u).
Proof. exact (eq_refl (term5 _99816 s t u)). Qed.
Lemma lem3848256 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) (h1 : term0 _99816) : term6 _99816 s t u.
Proof. exact (EQ_MP (@lem3848255 _99816 s t u) (@lem3848254 _99816 s t u h1)). Qed.
Lemma lem3848257 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) (h1 : term7 _99816 s t u) : term7 _99816 s t u.
Proof. exact (h1). Qed.
Lemma lem3848258 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) (h1 : term0 _99816) (h2 : term7 _99816 s t u) : (term8 _99816 s t) = (@CARD _99816 u).
Proof. exact (@lem3848256 _99816 s t u h1 (@lem3848257 _99816 s t u h2)). Qed.
Lemma lem3848259 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) (h1 : term7 _99816 s t u) : term9 _99816 s t u.
Proof. exact (fun h0 : term0 _99816 => @lem3848258 _99816 s t u h0 h1). Qed.
Lemma lem3848260 {_99816 : Type'} (h1 : term0 _99816) : term0 _99816.
Proof. exact (h1). Qed.
Lemma lem3848261 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) (h1 : term0 _99816) (h2 : term7 _99816 s t u) : (term8 _99816 s t) = (@CARD _99816 u).
Proof. exact (@lem3848259 _99816 s t u h2 (@lem3848260 _99816 h1)). Qed.
Lemma lem3848262 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) (h1 : term0 _99816) : term6 _99816 s t u.
Proof. exact (fun h0 : term7 _99816 s t u => @lem3848261 _99816 s t u h1 h0). Qed.
Lemma lem3848263 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (h1 : term0 _99816) : term4 _99816 s t.
Proof. exact (fun u : _99816 -> Prop => @lem3848262 _99816 s t u h1). Qed.
Lemma lem3848264 {_99816 : Type'} (s : _99816 -> Prop) (h1 : term0 _99816) : term2 _99816 s.
Proof. exact (fun t : _99816 -> Prop => @lem3848263 _99816 s t h1). Qed.
Lemma lem3848265 {_99816 : Type'} (h1 : term0 _99816) : term0 _99816.
Proof. exact (fun s : _99816 -> Prop => @lem3848264 _99816 s h1). Qed.
Lemma lem3848266 {_99816 : Type'} : term10 _99816.
Proof. exact (fun h0 : term0 _99816 => @lem3848265 _99816 h0). Qed.
Lemma lem3848267 {_99816 : Type'} : term0 _99816.
Proof. exact (@lem3848266 _99816 (@lem3848246 _99816)). Qed.
Lemma lem3848268 {_99816 : Type'} (s : _99816 -> Prop) : term1 _99816 s.
Proof. exact (@lem3848267 _99816 s). Qed.
Lemma lem3848269 {_99816 : Type'} (s : _99816 -> Prop) : (term1 _99816 s) = (term2 _99816 s).
Proof. exact (eq_refl (term1 _99816 s)). Qed.
Lemma lem3848270 {_99816 : Type'} (s : _99816 -> Prop) : term2 _99816 s.
Proof. exact (EQ_MP (@lem3848269 _99816 s) (@lem3848268 _99816 s)). Qed.
Lemma lem3848271 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) : term3 _99816 s t.
Proof. exact (@lem3848270 _99816 s t). Qed.
Lemma lem3848272 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) : (term3 _99816 s t) = (term4 _99816 s t).
Proof. exact (eq_refl (term3 _99816 s t)). Qed.
Lemma lem3848273 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) : term4 _99816 s t.
Proof. exact (EQ_MP (@lem3848272 _99816 s t) (@lem3848271 _99816 s t)). Qed.
Lemma lem3848274 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) : term5 _99816 s t u.
Proof. exact (@lem3848273 _99816 s t u). Qed.
Lemma lem3848275 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) : (term5 _99816 s t u) = (term6 _99816 s t u).
Proof. exact (eq_refl (term5 _99816 s t u)). Qed.
Lemma lem3848299 (a : nat) (c : nat) (b : nat) : (term11 a c b) = (term12 a c b).
Proof. exact (@lem17265 ((Nat.add a b) = c) (a = (Nat.sub c b))). Qed.
Lemma lem3848300 (b : nat) (c : nat) (a : nat) : (term13 a c b) = (term14 b c a).
Proof. exact (@lem1032781 c b (term15 b c a)). Qed.
Lemma lem3848301 (b : nat) (c : nat) (a : nat) (d : nat) : (term16 b c a d) = (term17 b c a d).
Proof. exact (eq_refl (term16 b c a d)). Qed.
Lemma lem3848302 (c : nat) (b : nat) (d : nat) : (term18 c b d) = (term18 c b d).
Proof. exact (eq_refl (term18 c b d)). Qed.
Lemma lem3848303 (b : nat) (c : nat) (a : nat) (d : nat) : (term19 b c a d) = (term20 b c a d).
Proof. exact (MK_COMB (@lem3848302 c b d) (@lem3848301 b c a d)). Qed.
Lemma lem3848304 (b : nat) (c : nat) (a : nat) : (term21 b c a) = (term22 b c a).
Proof. exact (fun_ext (fun d : nat => @lem3848303 b c a d)). Qed.
Lemma lem3848305 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3848306 (b : nat) (c : nat) (a : nat) : (term14 b c a) = (term23 b c a).
Proof. exact (MK_COMB (@lem3848305) (@lem3848304 b c a)). Qed.
Lemma lem3848307 (a : nat) (c : nat) (b : nat) : (term13 a c b) = (term12 a c b).
Proof. exact (eq_refl (term13 a c b)). Qed.
Lemma lem3848308 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3848309 (a : nat) (c : nat) (b : nat) : (term24 a c b) = (term25 a c b).
Proof. exact (MK_COMB (@lem3848308) (@lem3848307 a c b)). Qed.
Lemma lem3848310 (b : nat) (c : nat) (a : nat) : ((term13 a c b) = (term14 b c a)) = ((term12 a c b) = (term23 b c a)).
Proof. exact (MK_COMB (@lem3848309 a c b) (@lem3848306 b c a)). Qed.
Lemma lem3848311 (b : nat) (c : nat) (a : nat) : (term12 a c b) = (term23 b c a).
Proof. exact (EQ_MP (@lem3848310 b c a) (@lem3848300 b c a)). Qed.
Lemma lem3848312 (b : nat) (c : nat) (a : nat) (d : nat) : (term20 b c a d) = (term20 b c a d).
Proof. exact (eq_refl (term20 b c a d)). Qed.
Lemma lem3848313 (b : nat) (c : nat) (a : nat) : (term22 b c a) = (term22 b c a).
Proof. exact (fun_ext (fun d : nat => @lem3848312 b c a d)). Qed.
Lemma lem3848314 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3848315 (b : nat) (c : nat) (a : nat) : (term23 b c a) = (term23 b c a).
Proof. exact (MK_COMB (@lem3848314) (@lem3848313 b c a)). Qed.
Lemma lem3848316 (a : nat) (c : nat) (b : nat) : (term25 a c b) = (term25 a c b).
Proof. exact (eq_refl (term25 a c b)). Qed.
Lemma lem3848317 (b : nat) (c : nat) (a : nat) : ((term12 a c b) = (term23 b c a)) = ((term12 a c b) = (term23 b c a)).
Proof. exact (MK_COMB (@lem3848316 a c b) (@lem3848315 b c a)). Qed.
Lemma lem3848318 (b : nat) (c : nat) (a : nat) : (term12 a c b) = (term23 b c a).
Proof. exact (EQ_MP (@lem3848317 b c a) (@lem3848311 b c a)). Qed.
Lemma lem3848345 (b : nat) (c : nat) (a : nat) : (term11 a c b) = (term23 b c a).
Proof. exact (TRANS (@lem3848299 a c b) (@lem3848318 b c a)). Qed.
Lemma lem3848402 (b : nat) (c : nat) (a : nat) (d : nat) : (term20 b c a d) = (term20 b c a d).
Proof. exact (eq_refl (term20 b c a d)). Qed.
Lemma lem3848403 (b : nat) (c : nat) (a : nat) : (term22 b c a) = (term22 b c a).
Proof. exact (fun_ext (fun d : nat => @lem3848402 b c a d)). Qed.
Lemma lem3848404 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3848405 (b : nat) (c : nat) (a : nat) : (term23 b c a) = (term23 b c a).
Proof. exact (MK_COMB (@lem3848404) (@lem3848403 b c a)). Qed.
Lemma lem3848408 (b : nat) (c : nat) (a : nat) : (term11 a c b) = (term23 b c a).
Proof. exact (TRANS (@lem3848345 b c a) (@lem3848405 b c a)). Qed.
Lemma lem3848410 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem3848411 (c : nat) (b : nat) (d : nat) : (c = (Nat.add b d)) = ((int_of_num c) = (term26 b d)).
Proof. exact (@lem3848410 c (Nat.add b d)). Qed.
Lemma lem3848415 (m : nat) (n : nat) : (term26 m n) = (term27 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem3848416 (b : nat) (d : nat) : (term26 b d) = (term27 b d).
Proof. exact (@lem3848415 b d). Qed.
Lemma lem3848417 (c : nat) : (term28 c) = (term28 c).
Proof. exact (eq_refl (term28 c)). Qed.
Lemma lem3848418 (c : nat) (b : nat) (d : nat) : ((int_of_num c) = (term26 b d)) = ((int_of_num c) = (term27 b d)).
Proof. exact (MK_COMB (@lem3848417 c) (@lem3848416 b d)). Qed.
Lemma lem3848419 (c : nat) (b : nat) (d : nat) : (c = (Nat.add b d)) = ((int_of_num c) = (term27 b d)).
Proof. exact (TRANS (@lem3848411 c b d) (@lem3848418 c b d)). Qed.
Lemma lem3848420 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3848421 (c : nat) (b : nat) (d : nat) : (term29 c b d) = (term30 c b d).
Proof. exact (MK_COMB (@lem3848420) (@lem3848419 c b d)). Qed.
Lemma lem3848422 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3848423 (c : nat) (b : nat) (d : nat) : (term31 c b d) = (term32 c b d).
Proof. exact (MK_COMB (@lem3848422) (@lem3848421 c b d)). Qed.
Lemma lem3848425 (m : nat) (n : nat) : (Peano.lt m n) = (term33 m n).
Proof. exact (EQ_MP (@lem2841402 m n) (@lem2841401 m n)). Qed.
Lemma lem3848426 (c : nat) (b : nat) : (Peano.lt c b) = (term33 c b).
Proof. exact (@lem3848425 c b). Qed.
Lemma lem3848427 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3848428 (c : nat) (b : nat) : (term34 c b) = (term35 c b).
Proof. exact (MK_COMB (@lem3848427) (@lem3848426 c b)). Qed.
Lemma lem3848429 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3848430 (c : nat) (b : nat) : (term36 c b) = (term37 c b).
Proof. exact (MK_COMB (@lem3848429) (@lem3848428 c b)). Qed.
Lemma lem3848432 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem3848433 (d : nat) : (d = (NUMERAL 0)) = ((int_of_num d) = term38).
Proof. exact (@lem3848432 d (NUMERAL 0)). Qed.
Lemma lem3848436 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3848437 (d : nat) : (term39 d) = (term40 d).
Proof. exact (MK_COMB (@lem3848436) (@lem3848433 d)). Qed.
Lemma lem3848438 (c : nat) (b : nat) (d : nat) : (term41 c b d) = (term42 c b d).
Proof. exact (MK_COMB (@lem3848430 c b) (@lem3848437 d)). Qed.
Lemma lem3848439 (c : nat) (b : nat) (d : nat) : (term43 c b d) = (term44 c b d).
Proof. exact (MK_COMB (@lem3848423 c b d) (@lem3848438 c b d)). Qed.
Lemma lem3848440 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3848441 (c : nat) (b : nat) (d : nat) : (term18 c b d) = (term45 c b d).
Proof. exact (MK_COMB (@lem3848440) (@lem3848439 c b d)). Qed.
Lemma lem3848443 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem3848444 (a : nat) (b : nat) (c : nat) : ((Nat.add a b) = c) = ((term26 a b) = (int_of_num c)).
Proof. exact (@lem3848443 (Nat.add a b) c). Qed.
Lemma lem3848448 (m : nat) (n : nat) : (term26 m n) = (term27 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem3848449 (a : nat) (b : nat) : (term26 a b) = (term27 a b).
Proof. exact (@lem3848448 a b). Qed.
Lemma lem3848450 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem3848451 (a : nat) (b : nat) : (term46 a b) = (term47 a b).
Proof. exact (MK_COMB (@lem3848450) (@lem3848449 a b)). Qed.
Lemma lem3848452 (c : nat) : (int_of_num c) = (int_of_num c).
Proof. exact (eq_refl (int_of_num c)). Qed.
Lemma lem3848453 (a : nat) (b : nat) (c : nat) : ((term26 a b) = (int_of_num c)) = ((term27 a b) = (int_of_num c)).
Proof. exact (MK_COMB (@lem3848451 a b) (@lem3848452 c)). Qed.
Lemma lem3848454 (a : nat) (b : nat) (c : nat) : ((Nat.add a b) = c) = ((term27 a b) = (int_of_num c)).
Proof. exact (TRANS (@lem3848444 a b c) (@lem3848453 a b c)). Qed.
Lemma lem3848455 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3848456 (a : nat) (b : nat) (c : nat) : (term48 a b c) = (term49 a b c).
Proof. exact (MK_COMB (@lem3848455) (@lem3848454 a b c)). Qed.
Lemma lem3848457 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3848458 (a : nat) (b : nat) (c : nat) : (term50 a b c) = (term51 a b c).
Proof. exact (MK_COMB (@lem3848457) (@lem3848456 a b c)). Qed.
Lemma lem3848460 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem3848461 (a : nat) (d : nat) : (a = d) = ((int_of_num a) = (int_of_num d)).
Proof. exact (@lem3848460 a d). Qed.
Lemma lem3848464 (b : nat) (c : nat) (a : nat) (d : nat) : (term17 b c a d) = (term52 b c a d).
Proof. exact (MK_COMB (@lem3848458 a b c) (@lem3848461 a d)). Qed.
Lemma lem3848465 (b : nat) (c : nat) (a : nat) (d : nat) : (term20 b c a d) = (term53 b c a d).
Proof. exact (MK_COMB (@lem3848441 c b d) (@lem3848464 b c a d)). Qed.
Lemma lem3848466 (b : nat) (c : nat) (a : nat) : (term22 b c a) = (term54 b c a).
Proof. exact (fun_ext (fun d : nat => @lem3848465 b c a d)). Qed.
Lemma lem3848467 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3848468 (b : nat) (c : nat) (a : nat) : (term23 b c a) = (term55 b c a).
Proof. exact (MK_COMB (@lem3848467) (@lem3848466 b c a)). Qed.
Lemma lem3848469 (b : nat) (c : nat) (a : nat) : (term11 a c b) = (term55 b c a).
Proof. exact (TRANS (@lem3848408 b c a) (@lem3848468 b c a)). Qed.
Lemma lem3848470 (a : nat) : term56 a.
Proof. exact (@lem2307535 a). Qed.
Lemma lem3848471 (a : nat) : (term56 a) = (term57 a).
Proof. exact (eq_refl (term56 a)). Qed.
Lemma lem3848472 (a : nat) : term57 a.
Proof. exact (EQ_MP (@lem3848471 a) (@lem3848470 a)). Qed.
Lemma lem3848473 (b : nat) : term56 b.
Proof. exact (@lem2307535 b). Qed.
Lemma lem3848474 (b : nat) : (term56 b) = (term57 b).
Proof. exact (eq_refl (term56 b)). Qed.
Lemma lem3848475 (b : nat) : term57 b.
Proof. exact (EQ_MP (@lem3848474 b) (@lem3848473 b)). Qed.
Lemma lem3848476 (c : nat) : term56 c.
Proof. exact (@lem2307535 c). Qed.
Lemma lem3848477 (c : nat) : (term56 c) = (term57 c).
Proof. exact (eq_refl (term56 c)). Qed.
Lemma lem3848478 (c : nat) : term57 c.
Proof. exact (EQ_MP (@lem3848477 c) (@lem3848476 c)). Qed.
Lemma lem3848479 (d : nat) : term56 d.
Proof. exact (@lem2307535 d). Qed.
Lemma lem3848480 (d : nat) : (term56 d) = (term57 d).
Proof. exact (eq_refl (term56 d)). Qed.
Lemma lem3848481 (d : nat) : term57 d.
Proof. exact (EQ_MP (@lem3848480 d) (@lem3848479 d)). Qed.
Lemma lem3848482 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term58 _44735 _44736 _44734 _44737) = (term59 _44735 _44736 _44734 _44737).
Proof. exact (@lem2318604 (term59 _44735 _44736 _44734 _44737)). Qed.
Lemma lem3848510 (_44736 : int) (_44735 : int) (_44737 : int) : (term60 _44736 _44735 _44737) = (_44736 = (int_add _44735 _44737)).
Proof. exact (@lem16933 (_44736 = (int_add _44735 _44737))). Qed.
Lemma lem3848513 (_44736 : int) (_44735 : int) : (term61 _44736 _44735) = (int_lt _44736 _44735).
Proof. exact (@lem16933 (int_lt _44736 _44735)). Qed.
Lemma lem3848516 (_44737 : int) : (term62 _44737) = (_44737 = term38).
Proof. exact (@lem16933 (_44737 = term38)). Qed.
Lemma lem3848517 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3848518 (_44736 : int) (_44735 : int) : (term63 _44736 _44735) = (term64 _44736 _44735).
Proof. exact (MK_COMB (@lem3848517) (@lem3848513 _44736 _44735)). Qed.
Lemma lem3848519 (_44736 : int) (_44735 : int) (_44737 : int) : (term65 _44736 _44735 _44737) = (term66 _44736 _44735 _44737).
Proof. exact (MK_COMB (@lem3848518 _44736 _44735) (@lem3848516 _44737)). Qed.
Lemma lem3848520 (_44736 : int) (_44735 : int) (_44737 : int) : (term67 _44736 _44735 _44737) = (term65 _44736 _44735 _44737).
Proof. exact (@lem17160 (term68 _44736 _44735) (term69 _44737)). Qed.
Lemma lem3848521 (_44736 : int) (_44735 : int) (_44737 : int) : (term67 _44736 _44735 _44737) = (term66 _44736 _44735 _44737).
Proof. exact (TRANS (@lem3848520 _44736 _44735 _44737) (@lem3848519 _44736 _44735 _44737)). Qed.
Lemma lem3848522 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3848523 (_44736 : int) (_44735 : int) (_44737 : int) : (term70 _44736 _44735 _44737) = (term71 _44736 _44735 _44737).
Proof. exact (MK_COMB (@lem3848522) (@lem3848510 _44736 _44735 _44737)). Qed.
Lemma lem3848524 (_44736 : int) (_44735 : int) (_44737 : int) : (term72 _44736 _44735 _44737) = (term73 _44736 _44735 _44737).
Proof. exact (MK_COMB (@lem3848523 _44736 _44735 _44737) (@lem3848521 _44736 _44735 _44737)). Qed.
Lemma lem3848525 (_44736 : int) (_44735 : int) (_44737 : int) : (term74 _44736 _44735 _44737) = (term72 _44736 _44735 _44737).
Proof. exact (@lem17045 (term75 _44736 _44735 _44737) (term76 _44736 _44735 _44737)). Qed.
Lemma lem3848526 (_44736 : int) (_44735 : int) (_44737 : int) : (term74 _44736 _44735 _44737) = (term73 _44736 _44735 _44737).
Proof. exact (TRANS (@lem3848525 _44736 _44735 _44737) (@lem3848524 _44736 _44735 _44737)). Qed.
Lemma lem3848529 (_44734 : int) (_44735 : int) (_44736 : int) : (term77 _44734 _44735 _44736) = ((int_add _44734 _44735) = _44736).
Proof. exact (@lem16933 ((int_add _44734 _44735) = _44736)). Qed.
Lemma lem3848530 (_44734 : int) (_44737 : int) : (term78 _44734 _44737) = (term78 _44734 _44737).
Proof. exact (eq_refl (term78 _44734 _44737)). Qed.
Lemma lem3848531 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3848532 (_44734 : int) (_44735 : int) (_44736 : int) : (term79 _44734 _44735 _44736) = (term80 _44734 _44735 _44736).
Proof. exact (MK_COMB (@lem3848531) (@lem3848529 _44734 _44735 _44736)). Qed.
Lemma lem3848533 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term81 _44735 _44736 _44734 _44737) = (term82 _44735 _44736 _44734 _44737).
Proof. exact (MK_COMB (@lem3848532 _44734 _44735 _44736) (@lem3848530 _44734 _44737)). Qed.
Lemma lem3848534 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term83 _44735 _44736 _44734 _44737) = (term81 _44735 _44736 _44734 _44737).
Proof. exact (@lem17160 (term84 _44734 _44735 _44736) (_44734 = _44737)). Qed.
Lemma lem3848535 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term83 _44735 _44736 _44734 _44737) = (term82 _44735 _44736 _44734 _44737).
Proof. exact (TRANS (@lem3848534 _44735 _44736 _44734 _44737) (@lem3848533 _44735 _44736 _44734 _44737)). Qed.
Lemma lem3848536 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3848537 (_44736 : int) (_44735 : int) (_44737 : int) : (term85 _44736 _44735 _44737) = (term86 _44736 _44735 _44737).
Proof. exact (MK_COMB (@lem3848536) (@lem3848526 _44736 _44735 _44737)). Qed.
Lemma lem3848538 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term87 _44735 _44736 _44734 _44737) = (term88 _44735 _44736 _44734 _44737).
Proof. exact (MK_COMB (@lem3848537 _44736 _44735 _44737) (@lem3848535 _44735 _44736 _44734 _44737)). Qed.
Lemma lem3848539 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term89 _44735 _44736 _44734 _44737) = (term87 _44735 _44736 _44734 _44737).
Proof. exact (@lem17160 (term90 _44736 _44735 _44737) (term91 _44735 _44736 _44734 _44737)). Qed.
Lemma lem3848540 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term89 _44735 _44736 _44734 _44737) = (term88 _44735 _44736 _44734 _44737).
Proof. exact (TRANS (@lem3848539 _44735 _44736 _44734 _44737) (@lem3848538 _44735 _44736 _44734 _44737)). Qed.
Lemma lem3848542 (_44737 : int) : (term92 _44737) = (term92 _44737).
Proof. exact (eq_refl (term92 _44737)). Qed.
Lemma lem3848543 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term93 _44735 _44736 _44734 _44737) = (term94 _44735 _44736 _44734 _44737).
Proof. exact (MK_COMB (@lem3848542 _44737) (@lem3848540 _44735 _44736 _44734 _44737)). Qed.
Lemma lem3848544 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term95 _44735 _44736 _44734 _44737) = (term93 _44735 _44736 _44734 _44737).
Proof. exact (@lem17362 (term96 _44737) (term97 _44735 _44736 _44734 _44737)). Qed.
Lemma lem3848545 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term95 _44735 _44736 _44734 _44737) = (term94 _44735 _44736 _44734 _44737).
Proof. exact (TRANS (@lem3848544 _44735 _44736 _44734 _44737) (@lem3848543 _44735 _44736 _44734 _44737)). Qed.
Lemma lem3848547 (_44736 : int) : (term92 _44736) = (term92 _44736).
Proof. exact (eq_refl (term92 _44736)). Qed.
Lemma lem3848548 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term98 _44735 _44736 _44734 _44737) = (term99 _44735 _44736 _44734 _44737).
Proof. exact (MK_COMB (@lem3848547 _44736) (@lem3848545 _44735 _44736 _44734 _44737)). Qed.
Lemma lem3848549 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term100 _44735 _44736 _44734 _44737) = (term98 _44735 _44736 _44734 _44737).
Proof. exact (@lem17362 (term96 _44736) (term101 _44735 _44736 _44734 _44737)). Qed.
Lemma lem3848550 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term100 _44735 _44736 _44734 _44737) = (term99 _44735 _44736 _44734 _44737).
Proof. exact (TRANS (@lem3848549 _44735 _44736 _44734 _44737) (@lem3848548 _44735 _44736 _44734 _44737)). Qed.
Lemma lem3848552 (_44735 : int) : (term92 _44735) = (term92 _44735).
Proof. exact (eq_refl (term92 _44735)). Qed.
Lemma lem3848553 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term102 _44735 _44736 _44734 _44737) = (term103 _44735 _44736 _44734 _44737).
Proof. exact (MK_COMB (@lem3848552 _44735) (@lem3848550 _44735 _44736 _44734 _44737)). Qed.
Lemma lem3848554 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term104 _44735 _44736 _44734 _44737) = (term102 _44735 _44736 _44734 _44737).
Proof. exact (@lem17362 (term96 _44735) (term105 _44735 _44736 _44734 _44737)). Qed.
Lemma lem3848555 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term104 _44735 _44736 _44734 _44737) = (term103 _44735 _44736 _44734 _44737).
Proof. exact (TRANS (@lem3848554 _44735 _44736 _44734 _44737) (@lem3848553 _44735 _44736 _44734 _44737)). Qed.
Lemma lem3848557 (_44734 : int) : (term92 _44734) = (term92 _44734).
Proof. exact (eq_refl (term92 _44734)). Qed.
Lemma lem3848558 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term106 _44735 _44736 _44734 _44737) = (term107 _44735 _44736 _44734 _44737).
Proof. exact (MK_COMB (@lem3848557 _44734) (@lem3848555 _44735 _44736 _44734 _44737)). Qed.
Lemma lem3848559 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term108 _44735 _44736 _44734 _44737) = (term106 _44735 _44736 _44734 _44737).
Proof. exact (@lem17362 (term96 _44734) (term109 _44735 _44736 _44734 _44737)). Qed.
Lemma lem3848597 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term108 _44735 _44736 _44734 _44737) = (term107 _44735 _44736 _44734 _44737).
Proof. exact (TRANS (@lem3848559 _44735 _44736 _44734 _44737) (@lem3848558 _44735 _44736 _44734 _44737)). Qed.
Lemma lem3848600 (x : int) (y : int) : (int_le x y) = (term110 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3848601 (_44734 : int) : (term96 _44734) = (term111 _44734).
Proof. exact (@lem3848600 term38 _44734). Qed.
Lemma lem3848603 (n : nat) : (term112 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3848604 : term113 = term114.
Proof. exact (@lem3848603 (NUMERAL 0)). Qed.
Lemma lem3848605 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3848606 : term115 = term116.
Proof. exact (MK_COMB (@lem3848605) (@lem3848604)). Qed.
Lemma lem3848607 (_44734 : int) : (real_of_int _44734) = (real_of_int _44734).
Proof. exact (eq_refl (real_of_int _44734)). Qed.
Lemma lem3848608 (_44734 : int) : (term111 _44734) = (term117 _44734).
Proof. exact (MK_COMB (@lem3848606) (@lem3848607 _44734)). Qed.
Lemma lem3848610 (_44734 : int) : (term96 _44734) = (term117 _44734).
Proof. exact (TRANS (@lem3848601 _44734) (@lem3848608 _44734)). Qed.
Lemma lem3848613 (x : int) (y : int) : (int_le x y) = (term110 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3848614 (_44735 : int) : (term96 _44735) = (term111 _44735).
Proof. exact (@lem3848613 term38 _44735). Qed.
Lemma lem3848616 (n : nat) : (term112 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3848617 : term113 = term114.
Proof. exact (@lem3848616 (NUMERAL 0)). Qed.
Lemma lem3848618 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3848619 : term115 = term116.
Proof. exact (MK_COMB (@lem3848618) (@lem3848617)). Qed.
Lemma lem3848620 (_44735 : int) : (real_of_int _44735) = (real_of_int _44735).
Proof. exact (eq_refl (real_of_int _44735)). Qed.
Lemma lem3848621 (_44735 : int) : (term111 _44735) = (term117 _44735).
Proof. exact (MK_COMB (@lem3848619) (@lem3848620 _44735)). Qed.
Lemma lem3848623 (_44735 : int) : (term96 _44735) = (term117 _44735).
Proof. exact (TRANS (@lem3848614 _44735) (@lem3848621 _44735)). Qed.
Lemma lem3848626 (x : int) (y : int) : (int_le x y) = (term110 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3848627 (_44736 : int) : (term96 _44736) = (term111 _44736).
Proof. exact (@lem3848626 term38 _44736). Qed.
Lemma lem3848629 (n : nat) : (term112 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3848630 : term113 = term114.
Proof. exact (@lem3848629 (NUMERAL 0)). Qed.
Lemma lem3848631 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3848632 : term115 = term116.
Proof. exact (MK_COMB (@lem3848631) (@lem3848630)). Qed.
Lemma lem3848633 (_44736 : int) : (real_of_int _44736) = (real_of_int _44736).
Proof. exact (eq_refl (real_of_int _44736)). Qed.
Lemma lem3848634 (_44736 : int) : (term111 _44736) = (term117 _44736).
Proof. exact (MK_COMB (@lem3848632) (@lem3848633 _44736)). Qed.
Lemma lem3848636 (_44736 : int) : (term96 _44736) = (term117 _44736).
Proof. exact (TRANS (@lem3848627 _44736) (@lem3848634 _44736)). Qed.
Lemma lem3848639 (x : int) (y : int) : (int_le x y) = (term110 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3848640 (_44737 : int) : (term96 _44737) = (term111 _44737).
Proof. exact (@lem3848639 term38 _44737). Qed.
Lemma lem3848642 (n : nat) : (term112 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3848643 : term113 = term114.
Proof. exact (@lem3848642 (NUMERAL 0)). Qed.
Lemma lem3848644 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3848645 : term115 = term116.
Proof. exact (MK_COMB (@lem3848644) (@lem3848643)). Qed.
Lemma lem3848646 (_44737 : int) : (real_of_int _44737) = (real_of_int _44737).
Proof. exact (eq_refl (real_of_int _44737)). Qed.
Lemma lem3848647 (_44737 : int) : (term111 _44737) = (term117 _44737).
Proof. exact (MK_COMB (@lem3848645) (@lem3848646 _44737)). Qed.
Lemma lem3848649 (_44737 : int) : (term96 _44737) = (term117 _44737).
Proof. exact (TRANS (@lem3848640 _44737) (@lem3848647 _44737)). Qed.
Lemma lem3848652 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem3848653 (_44736 : int) (_44735 : int) (_44737 : int) : (_44736 = (int_add _44735 _44737)) = ((real_of_int _44736) = (term118 _44735 _44737)).
Proof. exact (@lem3848652 _44736 (int_add _44735 _44737)). Qed.
Lemma lem3848657 (x : int) (y : int) : (term118 x y) = (term119 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem3848658 (_44735 : int) (_44737 : int) : (term118 _44735 _44737) = (term119 _44735 _44737).
Proof. exact (@lem3848657 _44735 _44737). Qed.
Lemma lem3848659 (_44736 : int) : (term120 _44736) = (term120 _44736).
Proof. exact (eq_refl (term120 _44736)). Qed.
Lemma lem3848660 (_44736 : int) (_44735 : int) (_44737 : int) : ((real_of_int _44736) = (term118 _44735 _44737)) = ((real_of_int _44736) = (term119 _44735 _44737)).
Proof. exact (MK_COMB (@lem3848659 _44736) (@lem3848658 _44735 _44737)). Qed.
Lemma lem3848662 (_44736 : int) (_44735 : int) (_44737 : int) : (_44736 = (int_add _44735 _44737)) = ((real_of_int _44736) = (term119 _44735 _44737)).
Proof. exact (TRANS (@lem3848653 _44736 _44735 _44737) (@lem3848660 _44736 _44735 _44737)). Qed.
Lemma lem3848664 (x : int) (y : int) : (int_lt x y) = (term121 x y).
Proof. exact (proj2 (@lem2318497 x y)). Qed.
Lemma lem3848665 (_44736 : int) (_44735 : int) : (int_lt _44736 _44735) = (term121 _44736 _44735).
Proof. exact (@lem3848664 _44736 _44735). Qed.
Lemma lem3848667 (x : int) (y : int) : (int_le x y) = (term110 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3848668 (_44736 : int) (_44735 : int) : (term121 _44736 _44735) = (term122 _44736 _44735).
Proof. exact (@lem3848667 (term123 _44736) _44735). Qed.
Lemma lem3848670 (x : int) (y : int) : (term118 x y) = (term119 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem3848671 (_44736 : int) : (term124 _44736) = (term125 _44736).
Proof. exact (@lem3848670 _44736 term126). Qed.
Lemma lem3848673 (n : nat) : (term112 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3848674 : term127 = term128.
Proof. exact (@lem3848673 term129). Qed.
Lemma lem3848675 (_44736 : int) : (term130 _44736) = (term130 _44736).
Proof. exact (eq_refl (term130 _44736)). Qed.
Lemma lem3848676 (_44736 : int) : (term125 _44736) = (term131 _44736).
Proof. exact (MK_COMB (@lem3848675 _44736) (@lem3848674)). Qed.
Lemma lem3848677 (_44736 : int) : (term124 _44736) = (term131 _44736).
Proof. exact (TRANS (@lem3848671 _44736) (@lem3848676 _44736)). Qed.
Lemma lem3848678 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3848679 (_44736 : int) : (term132 _44736) = (term133 _44736).
Proof. exact (MK_COMB (@lem3848678) (@lem3848677 _44736)). Qed.
Lemma lem3848680 (_44735 : int) : (real_of_int _44735) = (real_of_int _44735).
Proof. exact (eq_refl (real_of_int _44735)). Qed.
Lemma lem3848681 (_44736 : int) (_44735 : int) : (term122 _44736 _44735) = (term134 _44736 _44735).
Proof. exact (MK_COMB (@lem3848679 _44736) (@lem3848680 _44735)). Qed.
Lemma lem3848682 (_44736 : int) (_44735 : int) : (term121 _44736 _44735) = (term134 _44736 _44735).
Proof. exact (TRANS (@lem3848668 _44736 _44735) (@lem3848681 _44736 _44735)). Qed.
Lemma lem3848683 (_44736 : int) (_44735 : int) : (int_lt _44736 _44735) = (term134 _44736 _44735).
Proof. exact (TRANS (@lem3848665 _44736 _44735) (@lem3848682 _44736 _44735)). Qed.
Lemma lem3848686 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem3848687 (_44737 : int) : (_44737 = term38) = ((real_of_int _44737) = term113).
Proof. exact (@lem3848686 _44737 term38). Qed.
Lemma lem3848691 (n : nat) : (term112 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3848692 : term113 = term114.
Proof. exact (@lem3848691 (NUMERAL 0)). Qed.
Lemma lem3848693 (_44737 : int) : (term120 _44737) = (term120 _44737).
Proof. exact (eq_refl (term120 _44737)). Qed.
Lemma lem3848694 (_44737 : int) : ((real_of_int _44737) = term113) = ((real_of_int _44737) = term114).
Proof. exact (MK_COMB (@lem3848693 _44737) (@lem3848692)). Qed.
Lemma lem3848696 (_44737 : int) : (_44737 = term38) = ((real_of_int _44737) = term114).
Proof. exact (TRANS (@lem3848687 _44737) (@lem3848694 _44737)). Qed.
Lemma lem3848697 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3848698 (_44736 : int) (_44735 : int) : (term64 _44736 _44735) = (term135 _44736 _44735).
Proof. exact (MK_COMB (@lem3848697) (@lem3848683 _44736 _44735)). Qed.
Lemma lem3848699 (_44736 : int) (_44735 : int) (_44737 : int) : (term66 _44736 _44735 _44737) = (term136 _44736 _44735 _44737).
Proof. exact (MK_COMB (@lem3848698 _44736 _44735) (@lem3848696 _44737)). Qed.
Lemma lem3848700 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3848701 (_44736 : int) (_44735 : int) (_44737 : int) : (term71 _44736 _44735 _44737) = (term137 _44736 _44735 _44737).
Proof. exact (MK_COMB (@lem3848700) (@lem3848662 _44736 _44735 _44737)). Qed.
Lemma lem3848702 (_44736 : int) (_44735 : int) (_44737 : int) : (term73 _44736 _44735 _44737) = (term138 _44736 _44735 _44737).
Proof. exact (MK_COMB (@lem3848701 _44736 _44735 _44737) (@lem3848699 _44736 _44735 _44737)). Qed.
Lemma lem3848705 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem3848706 (_44734 : int) (_44735 : int) (_44736 : int) : ((int_add _44734 _44735) = _44736) = ((term118 _44734 _44735) = (real_of_int _44736)).
Proof. exact (@lem3848705 (int_add _44734 _44735) _44736). Qed.
Lemma lem3848710 (x : int) (y : int) : (term118 x y) = (term119 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem3848711 (_44734 : int) (_44735 : int) : (term118 _44734 _44735) = (term119 _44734 _44735).
Proof. exact (@lem3848710 _44734 _44735). Qed.
Lemma lem3848712 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3848713 (_44734 : int) (_44735 : int) : (term139 _44734 _44735) = (term140 _44734 _44735).
Proof. exact (MK_COMB (@lem3848712) (@lem3848711 _44734 _44735)). Qed.
Lemma lem3848714 (_44736 : int) : (real_of_int _44736) = (real_of_int _44736).
Proof. exact (eq_refl (real_of_int _44736)). Qed.
Lemma lem3848715 (_44734 : int) (_44735 : int) (_44736 : int) : ((term118 _44734 _44735) = (real_of_int _44736)) = ((term119 _44734 _44735) = (real_of_int _44736)).
Proof. exact (MK_COMB (@lem3848713 _44734 _44735) (@lem3848714 _44736)). Qed.
Lemma lem3848717 (_44734 : int) (_44735 : int) (_44736 : int) : ((int_add _44734 _44735) = _44736) = ((term119 _44734 _44735) = (real_of_int _44736)).
Proof. exact (TRANS (@lem3848706 _44734 _44735 _44736) (@lem3848715 _44734 _44735 _44736)). Qed.
Lemma lem3848719 (y : int) (x : int) : (term78 x y) = (term141 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem3848720 (_44737 : int) (_44734 : int) : (term78 _44734 _44737) = (term141 _44737 _44734).
Proof. exact (@lem3848719 _44737 _44734). Qed.
Lemma lem3848722 (x : int) (y : int) : (int_le x y) = (term110 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3848723 (_44734 : int) (_44737 : int) : (term121 _44734 _44737) = (term122 _44734 _44737).
Proof. exact (@lem3848722 (term123 _44734) _44737). Qed.
Lemma lem3848725 (x : int) (y : int) : (term118 x y) = (term119 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem3848726 (_44734 : int) : (term124 _44734) = (term125 _44734).
Proof. exact (@lem3848725 _44734 term126). Qed.
Lemma lem3848728 (n : nat) : (term112 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3848729 : term127 = term128.
Proof. exact (@lem3848728 term129). Qed.
Lemma lem3848730 (_44734 : int) : (term130 _44734) = (term130 _44734).
Proof. exact (eq_refl (term130 _44734)). Qed.
Lemma lem3848731 (_44734 : int) : (term125 _44734) = (term131 _44734).
Proof. exact (MK_COMB (@lem3848730 _44734) (@lem3848729)). Qed.
Lemma lem3848732 (_44734 : int) : (term124 _44734) = (term131 _44734).
Proof. exact (TRANS (@lem3848726 _44734) (@lem3848731 _44734)). Qed.
Lemma lem3848733 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3848734 (_44734 : int) : (term132 _44734) = (term133 _44734).
Proof. exact (MK_COMB (@lem3848733) (@lem3848732 _44734)). Qed.
Lemma lem3848735 (_44737 : int) : (real_of_int _44737) = (real_of_int _44737).
Proof. exact (eq_refl (real_of_int _44737)). Qed.
Lemma lem3848736 (_44734 : int) (_44737 : int) : (term122 _44734 _44737) = (term134 _44734 _44737).
Proof. exact (MK_COMB (@lem3848734 _44734) (@lem3848735 _44737)). Qed.
Lemma lem3848737 (_44734 : int) (_44737 : int) : (term121 _44734 _44737) = (term134 _44734 _44737).
Proof. exact (TRANS (@lem3848723 _44734 _44737) (@lem3848736 _44734 _44737)). Qed.
Lemma lem3848738 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3848739 (_44734 : int) (_44737 : int) : (term142 _44734 _44737) = (term143 _44734 _44737).
Proof. exact (MK_COMB (@lem3848738) (@lem3848737 _44734 _44737)). Qed.
Lemma lem3848741 (x : int) (y : int) : (int_le x y) = (term110 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3848742 (_44737 : int) (_44734 : int) : (term121 _44737 _44734) = (term122 _44737 _44734).
Proof. exact (@lem3848741 (term123 _44737) _44734). Qed.
Lemma lem3848744 (x : int) (y : int) : (term118 x y) = (term119 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem3848745 (_44737 : int) : (term124 _44737) = (term125 _44737).
Proof. exact (@lem3848744 _44737 term126). Qed.
Lemma lem3848747 (n : nat) : (term112 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3848748 : term127 = term128.
Proof. exact (@lem3848747 term129). Qed.
Lemma lem3848749 (_44737 : int) : (term130 _44737) = (term130 _44737).
Proof. exact (eq_refl (term130 _44737)). Qed.
Lemma lem3848750 (_44737 : int) : (term125 _44737) = (term131 _44737).
Proof. exact (MK_COMB (@lem3848749 _44737) (@lem3848748)). Qed.
Lemma lem3848751 (_44737 : int) : (term124 _44737) = (term131 _44737).
Proof. exact (TRANS (@lem3848745 _44737) (@lem3848750 _44737)). Qed.
Lemma lem3848752 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3848753 (_44737 : int) : (term132 _44737) = (term133 _44737).
Proof. exact (MK_COMB (@lem3848752) (@lem3848751 _44737)). Qed.
Lemma lem3848754 (_44734 : int) : (real_of_int _44734) = (real_of_int _44734).
Proof. exact (eq_refl (real_of_int _44734)). Qed.
Lemma lem3848755 (_44737 : int) (_44734 : int) : (term122 _44737 _44734) = (term134 _44737 _44734).
Proof. exact (MK_COMB (@lem3848753 _44737) (@lem3848754 _44734)). Qed.
Lemma lem3848756 (_44737 : int) (_44734 : int) : (term121 _44737 _44734) = (term134 _44737 _44734).
Proof. exact (TRANS (@lem3848742 _44737 _44734) (@lem3848755 _44737 _44734)). Qed.
Lemma lem3848757 (_44737 : int) (_44734 : int) : (term141 _44737 _44734) = (term144 _44737 _44734).
Proof. exact (MK_COMB (@lem3848739 _44734 _44737) (@lem3848756 _44737 _44734)). Qed.
Lemma lem3848758 (_44737 : int) (_44734 : int) : (term78 _44734 _44737) = (term144 _44737 _44734).
Proof. exact (TRANS (@lem3848720 _44737 _44734) (@lem3848757 _44737 _44734)). Qed.
Lemma lem3848759 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3848760 (_44734 : int) (_44735 : int) (_44736 : int) : (term80 _44734 _44735 _44736) = (term145 _44734 _44735 _44736).
Proof. exact (MK_COMB (@lem3848759) (@lem3848717 _44734 _44735 _44736)). Qed.
Lemma lem3848761 (_44735 : int) (_44736 : int) (_44737 : int) (_44734 : int) : (term82 _44735 _44736 _44734 _44737) = (term146 _44735 _44736 _44737 _44734).
Proof. exact (MK_COMB (@lem3848760 _44734 _44735 _44736) (@lem3848758 _44737 _44734)). Qed.
Lemma lem3848762 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3848763 (_44736 : int) (_44735 : int) (_44737 : int) : (term86 _44736 _44735 _44737) = (term147 _44736 _44735 _44737).
Proof. exact (MK_COMB (@lem3848762) (@lem3848702 _44736 _44735 _44737)). Qed.
Lemma lem3848764 (_44735 : int) (_44736 : int) (_44737 : int) (_44734 : int) : (term88 _44735 _44736 _44734 _44737) = (term148 _44735 _44736 _44737 _44734).
Proof. exact (MK_COMB (@lem3848763 _44736 _44735 _44737) (@lem3848761 _44735 _44736 _44737 _44734)). Qed.
Lemma lem3848765 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3848766 (_44737 : int) : (term92 _44737) = (term149 _44737).
Proof. exact (MK_COMB (@lem3848765) (@lem3848649 _44737)). Qed.
Lemma lem3848767 (_44735 : int) (_44736 : int) (_44737 : int) (_44734 : int) : (term94 _44735 _44736 _44734 _44737) = (term150 _44735 _44736 _44737 _44734).
Proof. exact (MK_COMB (@lem3848766 _44737) (@lem3848764 _44735 _44736 _44737 _44734)). Qed.
Lemma lem3848768 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3848769 (_44736 : int) : (term92 _44736) = (term149 _44736).
Proof. exact (MK_COMB (@lem3848768) (@lem3848636 _44736)). Qed.
Lemma lem3848770 (_44735 : int) (_44736 : int) (_44737 : int) (_44734 : int) : (term99 _44735 _44736 _44734 _44737) = (term151 _44735 _44736 _44737 _44734).
Proof. exact (MK_COMB (@lem3848769 _44736) (@lem3848767 _44735 _44736 _44737 _44734)). Qed.
Lemma lem3848771 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3848772 (_44735 : int) : (term92 _44735) = (term149 _44735).
Proof. exact (MK_COMB (@lem3848771) (@lem3848623 _44735)). Qed.
Lemma lem3848773 (_44735 : int) (_44736 : int) (_44737 : int) (_44734 : int) : (term103 _44735 _44736 _44734 _44737) = (term152 _44735 _44736 _44737 _44734).
Proof. exact (MK_COMB (@lem3848772 _44735) (@lem3848770 _44735 _44736 _44737 _44734)). Qed.
Lemma lem3848774 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3848775 (_44734 : int) : (term92 _44734) = (term149 _44734).
Proof. exact (MK_COMB (@lem3848774) (@lem3848610 _44734)). Qed.
Lemma lem3848776 (_44735 : int) (_44736 : int) (_44737 : int) (_44734 : int) : (term107 _44735 _44736 _44734 _44737) = (term153 _44735 _44736 _44737 _44734).
Proof. exact (MK_COMB (@lem3848775 _44734) (@lem3848773 _44735 _44736 _44737 _44734)). Qed.
Lemma lem3848777 (_44735 : int) (_44736 : int) (_44737 : int) (_44734 : int) : (term108 _44735 _44736 _44734 _44737) = (term153 _44735 _44736 _44737 _44734).
Proof. exact (TRANS (@lem3848597 _44735 _44736 _44734 _44737) (@lem3848776 _44735 _44736 _44737 _44734)). Qed.
Lemma lem3848781 (t : Prop) : (term154 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3848877 (_44735 : int) (_44736 : int) (_44737 : int) (_44734 : int) : (term155 _44735 _44736 _44737 _44734) = (term153 _44735 _44736 _44737 _44734).
Proof. exact (@lem3848781 (term153 _44735 _44736 _44737 _44734)). Qed.
Lemma lem3848878 (_44734 : int) : (term117 _44734) = (term156 _44734).
Proof. exact (@lem1988287 (real_of_int _44734) term114). Qed.
Lemma lem3848884 (_44734 : int) : (term157 _44734) = (term158 _44734).
Proof. exact (@lem1982792 (real_of_int _44734) term114). Qed.
Lemma lem3848886 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3848887 : term114 = term160.
Proof. exact (@lem3848886 (NUMERAL 0)). Qed.
Lemma lem3848889 (x : nat) : (term161 x) = (term162 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3848890 : term163 = term164.
Proof. exact (@lem3848889 term129). Qed.
Lemma lem3848891 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3848892 : term165 = term166.
Proof. exact (MK_COMB (@lem3848891) (@lem3848890)). Qed.
Lemma lem3848893 : term167 = term168.
Proof. exact (MK_COMB (@lem3848892) (@lem3848887)). Qed.
Lemma lem3848894 : term168 = term169.
Proof. exact (@lem1981613 term163 term114 term128 term128). Qed.
Lemma lem3848896 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3848897 : term172 = term173.
Proof. exact (@lem3848896 term129 term129). Qed.
Lemma lem3848898 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3848899 : term175 = term129.
Proof. exact (EQ_MP (@lem3848898) (@lem940073)). Qed.
Lemma lem3848900 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3848901 : term173 = term128.
Proof. exact (MK_COMB (@lem3848900) (@lem3848899)). Qed.
Lemma lem3848902 : term172 = term128.
Proof. exact (TRANS (@lem3848897) (@lem3848901)). Qed.
Lemma lem3848904 (x : nat) : (term176 x) = term114.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem3848905 : term167 = term114.
Proof. exact (@lem3848904 term129). Qed.
Lemma lem3848906 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3848907 : term177 = term178.
Proof. exact (MK_COMB (@lem3848906) (@lem3848905)). Qed.
Lemma lem3848908 : term169 = term160.
Proof. exact (MK_COMB (@lem3848907) (@lem3848902)). Qed.
Lemma lem3848909 : term168 = term160.
Proof. exact (TRANS (@lem3848894) (@lem3848908)). Qed.
Lemma lem3848910 : term167 = term160.
Proof. exact (TRANS (@lem3848893) (@lem3848909)). Qed.
Lemma lem3848912 (x : real) : (term179 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3848913 : term160 = term114.
Proof. exact (@lem3848912 term114). Qed.
Lemma lem3848914 : term167 = term114.
Proof. exact (TRANS (@lem3848910) (@lem3848913)). Qed.
Lemma lem3848915 (_44734 : int) : (term130 _44734) = (term130 _44734).
Proof. exact (eq_refl (term130 _44734)). Qed.
Lemma lem3848916 (_44734 : int) : (term158 _44734) = (term180 _44734).
Proof. exact (MK_COMB (@lem3848915 _44734) (@lem3848914)). Qed.
Lemma lem3848917 (_44734 : int) : (term180 _44734) = (real_of_int _44734).
Proof. exact (@lem1982723 (real_of_int _44734)). Qed.
Lemma lem3848918 (_44734 : int) : (term158 _44734) = (real_of_int _44734).
Proof. exact (TRANS (@lem3848916 _44734) (@lem3848917 _44734)). Qed.
Lemma lem3848920 (_44734 : int) : (term157 _44734) = (real_of_int _44734).
Proof. exact (TRANS (@lem3848884 _44734) (@lem3848918 _44734)). Qed.
Lemma lem3848921 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3848922 (_44734 : int) : (term181 _44734) = (term182 _44734).
Proof. exact (MK_COMB (@lem3848921) (@lem3848920 _44734)). Qed.
Lemma lem3848923 : term114 = term114.
Proof. exact (eq_refl term114). Qed.
Lemma lem3848924 (_44734 : int) : (term156 _44734) = (term183 _44734).
Proof. exact (MK_COMB (@lem3848922 _44734) (@lem3848923)). Qed.
Lemma lem3848925 (_44734 : int) : (term117 _44734) = (term183 _44734).
Proof. exact (TRANS (@lem3848878 _44734) (@lem3848924 _44734)). Qed.
Lemma lem3848926 (_44735 : int) : (term117 _44735) = (term156 _44735).
Proof. exact (@lem1988287 (real_of_int _44735) term114). Qed.
Lemma lem3848932 (_44735 : int) : (term157 _44735) = (term158 _44735).
Proof. exact (@lem1982792 (real_of_int _44735) term114). Qed.
Lemma lem3848934 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3848935 : term114 = term160.
Proof. exact (@lem3848934 (NUMERAL 0)). Qed.
Lemma lem3848937 (x : nat) : (term161 x) = (term162 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3848938 : term163 = term164.
Proof. exact (@lem3848937 term129). Qed.
Lemma lem3848939 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3848940 : term165 = term166.
Proof. exact (MK_COMB (@lem3848939) (@lem3848938)). Qed.
Lemma lem3848941 : term167 = term168.
Proof. exact (MK_COMB (@lem3848940) (@lem3848935)). Qed.
Lemma lem3848942 : term168 = term169.
Proof. exact (@lem1981613 term163 term114 term128 term128). Qed.
Lemma lem3848944 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3848945 : term172 = term173.
Proof. exact (@lem3848944 term129 term129). Qed.
Lemma lem3848946 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3848947 : term175 = term129.
Proof. exact (EQ_MP (@lem3848946) (@lem940073)). Qed.
Lemma lem3848948 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3848949 : term173 = term128.
Proof. exact (MK_COMB (@lem3848948) (@lem3848947)). Qed.
Lemma lem3848950 : term172 = term128.
Proof. exact (TRANS (@lem3848945) (@lem3848949)). Qed.
Lemma lem3848952 (x : nat) : (term176 x) = term114.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem3848953 : term167 = term114.
Proof. exact (@lem3848952 term129). Qed.
Lemma lem3848954 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3848955 : term177 = term178.
Proof. exact (MK_COMB (@lem3848954) (@lem3848953)). Qed.
Lemma lem3848956 : term169 = term160.
Proof. exact (MK_COMB (@lem3848955) (@lem3848950)). Qed.
Lemma lem3848957 : term168 = term160.
Proof. exact (TRANS (@lem3848942) (@lem3848956)). Qed.
Lemma lem3848958 : term167 = term160.
Proof. exact (TRANS (@lem3848941) (@lem3848957)). Qed.
Lemma lem3848960 (x : real) : (term179 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3848961 : term160 = term114.
Proof. exact (@lem3848960 term114). Qed.
Lemma lem3848962 : term167 = term114.
Proof. exact (TRANS (@lem3848958) (@lem3848961)). Qed.
Lemma lem3848963 (_44735 : int) : (term130 _44735) = (term130 _44735).
Proof. exact (eq_refl (term130 _44735)). Qed.
Lemma lem3848964 (_44735 : int) : (term158 _44735) = (term180 _44735).
Proof. exact (MK_COMB (@lem3848963 _44735) (@lem3848962)). Qed.
Lemma lem3848965 (_44735 : int) : (term180 _44735) = (real_of_int _44735).
Proof. exact (@lem1982723 (real_of_int _44735)). Qed.
Lemma lem3848966 (_44735 : int) : (term158 _44735) = (real_of_int _44735).
Proof. exact (TRANS (@lem3848964 _44735) (@lem3848965 _44735)). Qed.
Lemma lem3848968 (_44735 : int) : (term157 _44735) = (real_of_int _44735).
Proof. exact (TRANS (@lem3848932 _44735) (@lem3848966 _44735)). Qed.
Lemma lem3848969 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3848970 (_44735 : int) : (term181 _44735) = (term182 _44735).
Proof. exact (MK_COMB (@lem3848969) (@lem3848968 _44735)). Qed.
Lemma lem3848971 : term114 = term114.
Proof. exact (eq_refl term114). Qed.
Lemma lem3848972 (_44735 : int) : (term156 _44735) = (term183 _44735).
Proof. exact (MK_COMB (@lem3848970 _44735) (@lem3848971)). Qed.
Lemma lem3848973 (_44735 : int) : (term117 _44735) = (term183 _44735).
Proof. exact (TRANS (@lem3848926 _44735) (@lem3848972 _44735)). Qed.
Lemma lem3848974 (_44736 : int) : (term117 _44736) = (term156 _44736).
Proof. exact (@lem1988287 (real_of_int _44736) term114). Qed.
Lemma lem3848980 (_44736 : int) : (term157 _44736) = (term158 _44736).
Proof. exact (@lem1982792 (real_of_int _44736) term114). Qed.
Lemma lem3848982 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3848983 : term114 = term160.
Proof. exact (@lem3848982 (NUMERAL 0)). Qed.
Lemma lem3848985 (x : nat) : (term161 x) = (term162 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3848986 : term163 = term164.
Proof. exact (@lem3848985 term129). Qed.
Lemma lem3848987 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3848988 : term165 = term166.
Proof. exact (MK_COMB (@lem3848987) (@lem3848986)). Qed.
Lemma lem3848989 : term167 = term168.
Proof. exact (MK_COMB (@lem3848988) (@lem3848983)). Qed.
Lemma lem3848990 : term168 = term169.
Proof. exact (@lem1981613 term163 term114 term128 term128). Qed.
Lemma lem3848992 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3848993 : term172 = term173.
Proof. exact (@lem3848992 term129 term129). Qed.
Lemma lem3848994 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3848995 : term175 = term129.
Proof. exact (EQ_MP (@lem3848994) (@lem940073)). Qed.
Lemma lem3848996 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3848997 : term173 = term128.
Proof. exact (MK_COMB (@lem3848996) (@lem3848995)). Qed.
Lemma lem3848998 : term172 = term128.
Proof. exact (TRANS (@lem3848993) (@lem3848997)). Qed.
Lemma lem3849000 (x : nat) : (term176 x) = term114.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem3849001 : term167 = term114.
Proof. exact (@lem3849000 term129). Qed.
Lemma lem3849002 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3849003 : term177 = term178.
Proof. exact (MK_COMB (@lem3849002) (@lem3849001)). Qed.
Lemma lem3849004 : term169 = term160.
Proof. exact (MK_COMB (@lem3849003) (@lem3848998)). Qed.
Lemma lem3849005 : term168 = term160.
Proof. exact (TRANS (@lem3848990) (@lem3849004)). Qed.
Lemma lem3849006 : term167 = term160.
Proof. exact (TRANS (@lem3848989) (@lem3849005)). Qed.
Lemma lem3849008 (x : real) : (term179 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3849009 : term160 = term114.
Proof. exact (@lem3849008 term114). Qed.
Lemma lem3849010 : term167 = term114.
Proof. exact (TRANS (@lem3849006) (@lem3849009)). Qed.
Lemma lem3849011 (_44736 : int) : (term130 _44736) = (term130 _44736).
Proof. exact (eq_refl (term130 _44736)). Qed.
Lemma lem3849012 (_44736 : int) : (term158 _44736) = (term180 _44736).
Proof. exact (MK_COMB (@lem3849011 _44736) (@lem3849010)). Qed.
Lemma lem3849013 (_44736 : int) : (term180 _44736) = (real_of_int _44736).
Proof. exact (@lem1982723 (real_of_int _44736)). Qed.
Lemma lem3849014 (_44736 : int) : (term158 _44736) = (real_of_int _44736).
Proof. exact (TRANS (@lem3849012 _44736) (@lem3849013 _44736)). Qed.
Lemma lem3849016 (_44736 : int) : (term157 _44736) = (real_of_int _44736).
Proof. exact (TRANS (@lem3848980 _44736) (@lem3849014 _44736)). Qed.
Lemma lem3849017 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3849018 (_44736 : int) : (term181 _44736) = (term182 _44736).
Proof. exact (MK_COMB (@lem3849017) (@lem3849016 _44736)). Qed.
Lemma lem3849019 : term114 = term114.
Proof. exact (eq_refl term114). Qed.
Lemma lem3849020 (_44736 : int) : (term156 _44736) = (term183 _44736).
Proof. exact (MK_COMB (@lem3849018 _44736) (@lem3849019)). Qed.
Lemma lem3849021 (_44736 : int) : (term117 _44736) = (term183 _44736).
Proof. exact (TRANS (@lem3848974 _44736) (@lem3849020 _44736)). Qed.
Lemma lem3849022 (_44737 : int) : (term117 _44737) = (term156 _44737).
Proof. exact (@lem1988287 (real_of_int _44737) term114). Qed.
Lemma lem3849028 (_44737 : int) : (term157 _44737) = (term158 _44737).
Proof. exact (@lem1982792 (real_of_int _44737) term114). Qed.
Lemma lem3849030 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3849031 : term114 = term160.
Proof. exact (@lem3849030 (NUMERAL 0)). Qed.
Lemma lem3849033 (x : nat) : (term161 x) = (term162 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3849034 : term163 = term164.
Proof. exact (@lem3849033 term129). Qed.
Lemma lem3849035 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3849036 : term165 = term166.
Proof. exact (MK_COMB (@lem3849035) (@lem3849034)). Qed.
Lemma lem3849037 : term167 = term168.
Proof. exact (MK_COMB (@lem3849036) (@lem3849031)). Qed.
Lemma lem3849038 : term168 = term169.
Proof. exact (@lem1981613 term163 term114 term128 term128). Qed.
Lemma lem3849040 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3849041 : term172 = term173.
Proof. exact (@lem3849040 term129 term129). Qed.
Lemma lem3849042 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3849043 : term175 = term129.
Proof. exact (EQ_MP (@lem3849042) (@lem940073)). Qed.
Lemma lem3849044 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3849045 : term173 = term128.
Proof. exact (MK_COMB (@lem3849044) (@lem3849043)). Qed.
Lemma lem3849046 : term172 = term128.
Proof. exact (TRANS (@lem3849041) (@lem3849045)). Qed.
Lemma lem3849048 (x : nat) : (term176 x) = term114.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem3849049 : term167 = term114.
Proof. exact (@lem3849048 term129). Qed.
Lemma lem3849050 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3849051 : term177 = term178.
Proof. exact (MK_COMB (@lem3849050) (@lem3849049)). Qed.
Lemma lem3849052 : term169 = term160.
Proof. exact (MK_COMB (@lem3849051) (@lem3849046)). Qed.
Lemma lem3849053 : term168 = term160.
Proof. exact (TRANS (@lem3849038) (@lem3849052)). Qed.
Lemma lem3849054 : term167 = term160.
Proof. exact (TRANS (@lem3849037) (@lem3849053)). Qed.
Lemma lem3849056 (x : real) : (term179 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3849057 : term160 = term114.
Proof. exact (@lem3849056 term114). Qed.
Lemma lem3849058 : term167 = term114.
Proof. exact (TRANS (@lem3849054) (@lem3849057)). Qed.
Lemma lem3849059 (_44737 : int) : (term130 _44737) = (term130 _44737).
Proof. exact (eq_refl (term130 _44737)). Qed.
Lemma lem3849060 (_44737 : int) : (term158 _44737) = (term180 _44737).
Proof. exact (MK_COMB (@lem3849059 _44737) (@lem3849058)). Qed.
Lemma lem3849061 (_44737 : int) : (term180 _44737) = (real_of_int _44737).
Proof. exact (@lem1982723 (real_of_int _44737)). Qed.
Lemma lem3849062 (_44737 : int) : (term158 _44737) = (real_of_int _44737).
Proof. exact (TRANS (@lem3849060 _44737) (@lem3849061 _44737)). Qed.
Lemma lem3849064 (_44737 : int) : (term157 _44737) = (real_of_int _44737).
Proof. exact (TRANS (@lem3849028 _44737) (@lem3849062 _44737)). Qed.
Lemma lem3849065 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3849066 (_44737 : int) : (term181 _44737) = (term182 _44737).
Proof. exact (MK_COMB (@lem3849065) (@lem3849064 _44737)). Qed.
Lemma lem3849067 : term114 = term114.
Proof. exact (eq_refl term114). Qed.
Lemma lem3849068 (_44737 : int) : (term156 _44737) = (term183 _44737).
Proof. exact (MK_COMB (@lem3849066 _44737) (@lem3849067)). Qed.
Lemma lem3849069 (_44737 : int) : (term117 _44737) = (term183 _44737).
Proof. exact (TRANS (@lem3849022 _44737) (@lem3849068 _44737)). Qed.
Lemma lem3849070 (_44736 : int) (_44735 : int) (_44737 : int) : ((real_of_int _44736) = (term119 _44735 _44737)) = ((term184 _44736 _44735 _44737) = term114).
Proof. exact (@lem1988293 (real_of_int _44736) (term119 _44735 _44737)). Qed.
Lemma lem3849082 (_44736 : int) (_44735 : int) (_44737 : int) : (term184 _44736 _44735 _44737) = (term185 _44736 _44735 _44737).
Proof. exact (@lem1982792 (real_of_int _44736) (term119 _44735 _44737)). Qed.
Lemma lem3849089 (_44735 : int) (_44737 : int) : (term186 _44735 _44737) = (term187 _44735 _44737).
Proof. exact (@lem1982781 (real_of_int _44735) term163 (real_of_int _44737)). Qed.
Lemma lem3849090 (_44736 : int) : (term130 _44736) = (term130 _44736).
Proof. exact (eq_refl (term130 _44736)). Qed.
Lemma lem3849091 (_44736 : int) (_44735 : int) (_44737 : int) : (term185 _44736 _44735 _44737) = (term188 _44736 _44735 _44737).
Proof. exact (MK_COMB (@lem3849090 _44736) (@lem3849089 _44735 _44737)). Qed.
Lemma lem3849096 (_44735 : int) (_44736 : int) (_44737 : int) : (term188 _44736 _44735 _44737) = (term189 _44735 _44736 _44737).
Proof. exact (@lem1982757 (term190 _44735) (real_of_int _44736) (term190 _44737)). Qed.
Lemma lem3849097 (_44735 : int) (_44736 : int) (_44737 : int) : (term185 _44736 _44735 _44737) = (term189 _44735 _44736 _44737).
Proof. exact (TRANS (@lem3849091 _44736 _44735 _44737) (@lem3849096 _44735 _44736 _44737)). Qed.
Lemma lem3849099 (_44735 : int) (_44736 : int) (_44737 : int) : (term184 _44736 _44735 _44737) = (term189 _44735 _44736 _44737).
Proof. exact (TRANS (@lem3849082 _44736 _44735 _44737) (@lem3849097 _44735 _44736 _44737)). Qed.
Lemma lem3849100 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3849101 (_44735 : int) (_44736 : int) (_44737 : int) : (term191 _44736 _44735 _44737) = (term192 _44735 _44736 _44737).
Proof. exact (MK_COMB (@lem3849100) (@lem3849099 _44735 _44736 _44737)). Qed.
Lemma lem3849102 : term114 = term114.
Proof. exact (eq_refl term114). Qed.
Lemma lem3849103 (_44735 : int) (_44736 : int) (_44737 : int) : ((term184 _44736 _44735 _44737) = term114) = ((term189 _44735 _44736 _44737) = term114).
Proof. exact (MK_COMB (@lem3849101 _44735 _44736 _44737) (@lem3849102)). Qed.
Lemma lem3849104 (_44735 : int) (_44736 : int) (_44737 : int) : ((real_of_int _44736) = (term119 _44735 _44737)) = ((term189 _44735 _44736 _44737) = term114).
Proof. exact (TRANS (@lem3849070 _44736 _44735 _44737) (@lem3849103 _44735 _44736 _44737)). Qed.
Lemma lem3849105 (_44735 : int) (_44736 : int) : (term134 _44736 _44735) = (term193 _44735 _44736).
Proof. exact (@lem1988287 (real_of_int _44735) (term131 _44736)). Qed.
Lemma lem3849117 (_44735 : int) (_44736 : int) : (term194 _44735 _44736) = (term195 _44735 _44736).
Proof. exact (@lem1982792 (real_of_int _44735) (term131 _44736)). Qed.
Lemma lem3849118 (_44736 : int) : (term196 _44736) = (term197 _44736).
Proof. exact (@lem1982781 (real_of_int _44736) term163 term128). Qed.
Lemma lem3849120 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3849121 : term128 = term198.
Proof. exact (@lem3849120 term129). Qed.
Lemma lem3849123 (x : nat) : (term161 x) = (term162 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3849124 : term163 = term164.
Proof. exact (@lem3849123 term129). Qed.
Lemma lem3849125 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3849126 : term165 = term166.
Proof. exact (MK_COMB (@lem3849125) (@lem3849124)). Qed.
Lemma lem3849127 : term199 = term200.
Proof. exact (MK_COMB (@lem3849126) (@lem3849121)). Qed.
Lemma lem3849128 : term200 = term201.
Proof. exact (@lem1981613 term163 term128 term128 term128). Qed.
Lemma lem3849130 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3849131 : term172 = term173.
Proof. exact (@lem3849130 term129 term129). Qed.
Lemma lem3849132 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3849133 : term175 = term129.
Proof. exact (EQ_MP (@lem3849132) (@lem940073)). Qed.
Lemma lem3849134 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3849135 : term173 = term128.
Proof. exact (MK_COMB (@lem3849134) (@lem3849133)). Qed.
Lemma lem3849136 : term172 = term128.
Proof. exact (TRANS (@lem3849131) (@lem3849135)). Qed.
Lemma lem3849138 (m : nat) (n : nat) : (term202 m n) = (term203 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3849139 : term199 = term204.
Proof. exact (@lem3849138 term129 term129). Qed.
Lemma lem3849140 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3849141 : term175 = term129.
Proof. exact (EQ_MP (@lem3849140) (@lem940073)). Qed.
Lemma lem3849142 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3849143 : term173 = term128.
Proof. exact (MK_COMB (@lem3849142) (@lem3849141)). Qed.
Lemma lem3849144 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3849145 : term204 = term163.
Proof. exact (MK_COMB (@lem3849144) (@lem3849143)). Qed.
Lemma lem3849146 : term199 = term163.
Proof. exact (TRANS (@lem3849139) (@lem3849145)). Qed.
Lemma lem3849147 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3849148 : term205 = term206.
Proof. exact (MK_COMB (@lem3849147) (@lem3849146)). Qed.
Lemma lem3849149 : term201 = term164.
Proof. exact (MK_COMB (@lem3849148) (@lem3849136)). Qed.
Lemma lem3849150 : term200 = term164.
Proof. exact (TRANS (@lem3849128) (@lem3849149)). Qed.
Lemma lem3849151 : term199 = term164.
Proof. exact (TRANS (@lem3849127) (@lem3849150)). Qed.
Lemma lem3849153 (x : real) : (term179 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3849154 : term164 = term163.
Proof. exact (@lem3849153 term163). Qed.
Lemma lem3849155 : term199 = term163.
Proof. exact (TRANS (@lem3849151) (@lem3849154)). Qed.
Lemma lem3849158 (_44736 : int) : (term207 _44736) = (term207 _44736).
Proof. exact (eq_refl (term207 _44736)). Qed.
Lemma lem3849159 (_44736 : int) : (term197 _44736) = (term208 _44736).
Proof. exact (MK_COMB (@lem3849158 _44736) (@lem3849155)). Qed.
Lemma lem3849160 (_44736 : int) : (term196 _44736) = (term208 _44736).
Proof. exact (TRANS (@lem3849118 _44736) (@lem3849159 _44736)). Qed.
Lemma lem3849161 (_44735 : int) : (term130 _44735) = (term130 _44735).
Proof. exact (eq_refl (term130 _44735)). Qed.
Lemma lem3849164 (_44735 : int) (_44736 : int) : (term195 _44735 _44736) = (term209 _44735 _44736).
Proof. exact (MK_COMB (@lem3849161 _44735) (@lem3849160 _44736)). Qed.
Lemma lem3849166 (_44735 : int) (_44736 : int) : (term194 _44735 _44736) = (term209 _44735 _44736).
Proof. exact (TRANS (@lem3849117 _44735 _44736) (@lem3849164 _44735 _44736)). Qed.
Lemma lem3849167 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3849168 (_44735 : int) (_44736 : int) : (term210 _44735 _44736) = (term211 _44735 _44736).
Proof. exact (MK_COMB (@lem3849167) (@lem3849166 _44735 _44736)). Qed.
Lemma lem3849169 : term114 = term114.
Proof. exact (eq_refl term114). Qed.
Lemma lem3849170 (_44735 : int) (_44736 : int) : (term193 _44735 _44736) = (term212 _44735 _44736).
Proof. exact (MK_COMB (@lem3849168 _44735 _44736) (@lem3849169)). Qed.
Lemma lem3849171 (_44735 : int) (_44736 : int) : (term134 _44736 _44735) = (term212 _44735 _44736).
Proof. exact (TRANS (@lem3849105 _44735 _44736) (@lem3849170 _44735 _44736)). Qed.
Lemma lem3849172 (_44737 : int) : ((real_of_int _44737) = term114) = ((term157 _44737) = term114).
Proof. exact (@lem1988293 (real_of_int _44737) term114). Qed.
Lemma lem3849178 (_44737 : int) : (term157 _44737) = (term158 _44737).
Proof. exact (@lem1982792 (real_of_int _44737) term114). Qed.
Lemma lem3849180 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3849181 : term114 = term160.
Proof. exact (@lem3849180 (NUMERAL 0)). Qed.
Lemma lem3849183 (x : nat) : (term161 x) = (term162 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3849184 : term163 = term164.
Proof. exact (@lem3849183 term129). Qed.
Lemma lem3849185 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3849186 : term165 = term166.
Proof. exact (MK_COMB (@lem3849185) (@lem3849184)). Qed.
Lemma lem3849187 : term167 = term168.
Proof. exact (MK_COMB (@lem3849186) (@lem3849181)). Qed.
Lemma lem3849188 : term168 = term169.
Proof. exact (@lem1981613 term163 term114 term128 term128). Qed.
Lemma lem3849190 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3849191 : term172 = term173.
Proof. exact (@lem3849190 term129 term129). Qed.
Lemma lem3849192 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3849193 : term175 = term129.
Proof. exact (EQ_MP (@lem3849192) (@lem940073)). Qed.
Lemma lem3849194 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3849195 : term173 = term128.
Proof. exact (MK_COMB (@lem3849194) (@lem3849193)). Qed.
Lemma lem3849196 : term172 = term128.
Proof. exact (TRANS (@lem3849191) (@lem3849195)). Qed.
Lemma lem3849198 (x : nat) : (term176 x) = term114.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem3849199 : term167 = term114.
Proof. exact (@lem3849198 term129). Qed.
Lemma lem3849200 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3849201 : term177 = term178.
Proof. exact (MK_COMB (@lem3849200) (@lem3849199)). Qed.
Lemma lem3849202 : term169 = term160.
Proof. exact (MK_COMB (@lem3849201) (@lem3849196)). Qed.
Lemma lem3849203 : term168 = term160.
Proof. exact (TRANS (@lem3849188) (@lem3849202)). Qed.
Lemma lem3849204 : term167 = term160.
Proof. exact (TRANS (@lem3849187) (@lem3849203)). Qed.
Lemma lem3849206 (x : real) : (term179 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3849207 : term160 = term114.
Proof. exact (@lem3849206 term114). Qed.
Lemma lem3849208 : term167 = term114.
Proof. exact (TRANS (@lem3849204) (@lem3849207)). Qed.
Lemma lem3849209 (_44737 : int) : (term130 _44737) = (term130 _44737).
Proof. exact (eq_refl (term130 _44737)). Qed.
Lemma lem3849210 (_44737 : int) : (term158 _44737) = (term180 _44737).
Proof. exact (MK_COMB (@lem3849209 _44737) (@lem3849208)). Qed.
Lemma lem3849211 (_44737 : int) : (term180 _44737) = (real_of_int _44737).
Proof. exact (@lem1982723 (real_of_int _44737)). Qed.
Lemma lem3849212 (_44737 : int) : (term158 _44737) = (real_of_int _44737).
Proof. exact (TRANS (@lem3849210 _44737) (@lem3849211 _44737)). Qed.
Lemma lem3849214 (_44737 : int) : (term157 _44737) = (real_of_int _44737).
Proof. exact (TRANS (@lem3849178 _44737) (@lem3849212 _44737)). Qed.
Lemma lem3849215 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3849216 (_44737 : int) : (term213 _44737) = (term120 _44737).
Proof. exact (MK_COMB (@lem3849215) (@lem3849214 _44737)). Qed.
Lemma lem3849217 : term114 = term114.
Proof. exact (eq_refl term114). Qed.
Lemma lem3849218 (_44737 : int) : ((term157 _44737) = term114) = ((real_of_int _44737) = term114).
Proof. exact (MK_COMB (@lem3849216 _44737) (@lem3849217)). Qed.
Lemma lem3849219 (_44737 : int) : ((real_of_int _44737) = term114) = ((real_of_int _44737) = term114).
Proof. exact (TRANS (@lem3849172 _44737) (@lem3849218 _44737)). Qed.
Lemma lem3849220 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3849221 (_44735 : int) (_44736 : int) : (term135 _44736 _44735) = (term214 _44735 _44736).
Proof. exact (MK_COMB (@lem3849220) (@lem3849171 _44735 _44736)). Qed.
Lemma lem3849222 (_44735 : int) (_44736 : int) (_44737 : int) : (term136 _44736 _44735 _44737) = (term215 _44735 _44736 _44737).
Proof. exact (MK_COMB (@lem3849221 _44735 _44736) (@lem3849219 _44737)). Qed.
Lemma lem3849223 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3849224 (_44735 : int) (_44736 : int) (_44737 : int) : (term137 _44736 _44735 _44737) = (term216 _44735 _44736 _44737).
Proof. exact (MK_COMB (@lem3849223) (@lem3849104 _44735 _44736 _44737)). Qed.
Lemma lem3849225 (_44735 : int) (_44736 : int) (_44737 : int) : (term138 _44736 _44735 _44737) = (term217 _44735 _44736 _44737).
Proof. exact (MK_COMB (@lem3849224 _44735 _44736 _44737) (@lem3849222 _44735 _44736 _44737)). Qed.
Lemma lem3849226 (_44734 : int) (_44735 : int) (_44736 : int) : ((term119 _44734 _44735) = (real_of_int _44736)) = ((term218 _44734 _44735 _44736) = term114).
Proof. exact (@lem1988293 (term119 _44734 _44735) (real_of_int _44736)). Qed.
Lemma lem3849238 (_44734 : int) (_44735 : int) (_44736 : int) : (term218 _44734 _44735 _44736) = (term219 _44734 _44735 _44736).
Proof. exact (@lem1982792 (term119 _44734 _44735) (real_of_int _44736)). Qed.
Lemma lem3849247 (_44734 : int) (_44735 : int) (_44736 : int) : (term219 _44734 _44735 _44736) = (term220 _44734 _44735 _44736).
Proof. exact (@lem1982755 (real_of_int _44734) (real_of_int _44735) (term190 _44736)). Qed.
Lemma lem3849249 (_44734 : int) (_44735 : int) (_44736 : int) : (term218 _44734 _44735 _44736) = (term220 _44734 _44735 _44736).
Proof. exact (TRANS (@lem3849238 _44734 _44735 _44736) (@lem3849247 _44734 _44735 _44736)). Qed.
Lemma lem3849250 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3849251 (_44734 : int) (_44735 : int) (_44736 : int) : (term221 _44734 _44735 _44736) = (term222 _44734 _44735 _44736).
Proof. exact (MK_COMB (@lem3849250) (@lem3849249 _44734 _44735 _44736)). Qed.
Lemma lem3849252 : term114 = term114.
Proof. exact (eq_refl term114). Qed.
Lemma lem3849253 (_44734 : int) (_44735 : int) (_44736 : int) : ((term218 _44734 _44735 _44736) = term114) = ((term220 _44734 _44735 _44736) = term114).
Proof. exact (MK_COMB (@lem3849251 _44734 _44735 _44736) (@lem3849252)). Qed.
Lemma lem3849254 (_44734 : int) (_44735 : int) (_44736 : int) : ((term119 _44734 _44735) = (real_of_int _44736)) = ((term220 _44734 _44735 _44736) = term114).
Proof. exact (TRANS (@lem3849226 _44734 _44735 _44736) (@lem3849253 _44734 _44735 _44736)). Qed.
Lemma lem3849255 (_44737 : int) (_44734 : int) : (term134 _44734 _44737) = (term193 _44737 _44734).
Proof. exact (@lem1988287 (real_of_int _44737) (term131 _44734)). Qed.
Lemma lem3849267 (_44737 : int) (_44734 : int) : (term194 _44737 _44734) = (term195 _44737 _44734).
Proof. exact (@lem1982792 (real_of_int _44737) (term131 _44734)). Qed.
Lemma lem3849268 (_44734 : int) : (term196 _44734) = (term197 _44734).
Proof. exact (@lem1982781 (real_of_int _44734) term163 term128). Qed.
Lemma lem3849270 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3849271 : term128 = term198.
Proof. exact (@lem3849270 term129). Qed.
Lemma lem3849273 (x : nat) : (term161 x) = (term162 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3849274 : term163 = term164.
Proof. exact (@lem3849273 term129). Qed.
Lemma lem3849275 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3849276 : term165 = term166.
Proof. exact (MK_COMB (@lem3849275) (@lem3849274)). Qed.
Lemma lem3849277 : term199 = term200.
Proof. exact (MK_COMB (@lem3849276) (@lem3849271)). Qed.
Lemma lem3849278 : term200 = term201.
Proof. exact (@lem1981613 term163 term128 term128 term128). Qed.
Lemma lem3849280 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3849281 : term172 = term173.
Proof. exact (@lem3849280 term129 term129). Qed.
Lemma lem3849282 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3849283 : term175 = term129.
Proof. exact (EQ_MP (@lem3849282) (@lem940073)). Qed.
Lemma lem3849284 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3849285 : term173 = term128.
Proof. exact (MK_COMB (@lem3849284) (@lem3849283)). Qed.
Lemma lem3849286 : term172 = term128.
Proof. exact (TRANS (@lem3849281) (@lem3849285)). Qed.
Lemma lem3849288 (m : nat) (n : nat) : (term202 m n) = (term203 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3849289 : term199 = term204.
Proof. exact (@lem3849288 term129 term129). Qed.
Lemma lem3849290 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3849291 : term175 = term129.
Proof. exact (EQ_MP (@lem3849290) (@lem940073)). Qed.
Lemma lem3849292 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3849293 : term173 = term128.
Proof. exact (MK_COMB (@lem3849292) (@lem3849291)). Qed.
Lemma lem3849294 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3849295 : term204 = term163.
Proof. exact (MK_COMB (@lem3849294) (@lem3849293)). Qed.
Lemma lem3849296 : term199 = term163.
Proof. exact (TRANS (@lem3849289) (@lem3849295)). Qed.
Lemma lem3849297 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3849298 : term205 = term206.
Proof. exact (MK_COMB (@lem3849297) (@lem3849296)). Qed.
Lemma lem3849299 : term201 = term164.
Proof. exact (MK_COMB (@lem3849298) (@lem3849286)). Qed.
Lemma lem3849300 : term200 = term164.
Proof. exact (TRANS (@lem3849278) (@lem3849299)). Qed.
Lemma lem3849301 : term199 = term164.
Proof. exact (TRANS (@lem3849277) (@lem3849300)). Qed.
Lemma lem3849303 (x : real) : (term179 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3849304 : term164 = term163.
Proof. exact (@lem3849303 term163). Qed.
Lemma lem3849305 : term199 = term163.
Proof. exact (TRANS (@lem3849301) (@lem3849304)). Qed.
Lemma lem3849308 (_44734 : int) : (term207 _44734) = (term207 _44734).
Proof. exact (eq_refl (term207 _44734)). Qed.
Lemma lem3849309 (_44734 : int) : (term197 _44734) = (term208 _44734).
Proof. exact (MK_COMB (@lem3849308 _44734) (@lem3849305)). Qed.
Lemma lem3849310 (_44734 : int) : (term196 _44734) = (term208 _44734).
Proof. exact (TRANS (@lem3849268 _44734) (@lem3849309 _44734)). Qed.
Lemma lem3849311 (_44737 : int) : (term130 _44737) = (term130 _44737).
Proof. exact (eq_refl (term130 _44737)). Qed.
Lemma lem3849312 (_44737 : int) (_44734 : int) : (term195 _44737 _44734) = (term209 _44737 _44734).
Proof. exact (MK_COMB (@lem3849311 _44737) (@lem3849310 _44734)). Qed.
Lemma lem3849317 (_44734 : int) (_44737 : int) : (term209 _44737 _44734) = (term223 _44734 _44737).
Proof. exact (@lem1982757 (term190 _44734) (real_of_int _44737) term163). Qed.
Lemma lem3849318 (_44734 : int) (_44737 : int) : (term195 _44737 _44734) = (term223 _44734 _44737).
Proof. exact (TRANS (@lem3849312 _44737 _44734) (@lem3849317 _44734 _44737)). Qed.
Lemma lem3849320 (_44734 : int) (_44737 : int) : (term194 _44737 _44734) = (term223 _44734 _44737).
Proof. exact (TRANS (@lem3849267 _44737 _44734) (@lem3849318 _44734 _44737)). Qed.
Lemma lem3849321 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3849322 (_44734 : int) (_44737 : int) : (term210 _44737 _44734) = (term224 _44734 _44737).
Proof. exact (MK_COMB (@lem3849321) (@lem3849320 _44734 _44737)). Qed.
Lemma lem3849323 : term114 = term114.
Proof. exact (eq_refl term114). Qed.
Lemma lem3849324 (_44734 : int) (_44737 : int) : (term193 _44737 _44734) = (term225 _44734 _44737).
Proof. exact (MK_COMB (@lem3849322 _44734 _44737) (@lem3849323)). Qed.
Lemma lem3849325 (_44734 : int) (_44737 : int) : (term134 _44734 _44737) = (term225 _44734 _44737).
Proof. exact (TRANS (@lem3849255 _44737 _44734) (@lem3849324 _44734 _44737)). Qed.
Lemma lem3849326 (_44734 : int) (_44737 : int) : (term134 _44737 _44734) = (term193 _44734 _44737).
Proof. exact (@lem1988287 (real_of_int _44734) (term131 _44737)). Qed.
Lemma lem3849338 (_44734 : int) (_44737 : int) : (term194 _44734 _44737) = (term195 _44734 _44737).
Proof. exact (@lem1982792 (real_of_int _44734) (term131 _44737)). Qed.
Lemma lem3849339 (_44737 : int) : (term196 _44737) = (term197 _44737).
Proof. exact (@lem1982781 (real_of_int _44737) term163 term128). Qed.
Lemma lem3849341 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3849342 : term128 = term198.
Proof. exact (@lem3849341 term129). Qed.
Lemma lem3849344 (x : nat) : (term161 x) = (term162 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3849345 : term163 = term164.
Proof. exact (@lem3849344 term129). Qed.
Lemma lem3849346 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3849347 : term165 = term166.
Proof. exact (MK_COMB (@lem3849346) (@lem3849345)). Qed.
Lemma lem3849348 : term199 = term200.
Proof. exact (MK_COMB (@lem3849347) (@lem3849342)). Qed.
Lemma lem3849349 : term200 = term201.
Proof. exact (@lem1981613 term163 term128 term128 term128). Qed.
Lemma lem3849351 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3849352 : term172 = term173.
Proof. exact (@lem3849351 term129 term129). Qed.
Lemma lem3849353 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3849354 : term175 = term129.
Proof. exact (EQ_MP (@lem3849353) (@lem940073)). Qed.
Lemma lem3849355 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3849356 : term173 = term128.
Proof. exact (MK_COMB (@lem3849355) (@lem3849354)). Qed.
Lemma lem3849357 : term172 = term128.
Proof. exact (TRANS (@lem3849352) (@lem3849356)). Qed.
Lemma lem3849359 (m : nat) (n : nat) : (term202 m n) = (term203 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3849360 : term199 = term204.
Proof. exact (@lem3849359 term129 term129). Qed.
Lemma lem3849361 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3849362 : term175 = term129.
Proof. exact (EQ_MP (@lem3849361) (@lem940073)). Qed.
Lemma lem3849363 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3849364 : term173 = term128.
Proof. exact (MK_COMB (@lem3849363) (@lem3849362)). Qed.
Lemma lem3849365 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3849366 : term204 = term163.
Proof. exact (MK_COMB (@lem3849365) (@lem3849364)). Qed.
Lemma lem3849367 : term199 = term163.
Proof. exact (TRANS (@lem3849360) (@lem3849366)). Qed.
Lemma lem3849368 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3849369 : term205 = term206.
Proof. exact (MK_COMB (@lem3849368) (@lem3849367)). Qed.
Lemma lem3849370 : term201 = term164.
Proof. exact (MK_COMB (@lem3849369) (@lem3849357)). Qed.
Lemma lem3849371 : term200 = term164.
Proof. exact (TRANS (@lem3849349) (@lem3849370)). Qed.
Lemma lem3849372 : term199 = term164.
Proof. exact (TRANS (@lem3849348) (@lem3849371)). Qed.
Lemma lem3849374 (x : real) : (term179 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3849375 : term164 = term163.
Proof. exact (@lem3849374 term163). Qed.
Lemma lem3849376 : term199 = term163.
Proof. exact (TRANS (@lem3849372) (@lem3849375)). Qed.
Lemma lem3849379 (_44737 : int) : (term207 _44737) = (term207 _44737).
Proof. exact (eq_refl (term207 _44737)). Qed.
Lemma lem3849380 (_44737 : int) : (term197 _44737) = (term208 _44737).
Proof. exact (MK_COMB (@lem3849379 _44737) (@lem3849376)). Qed.
Lemma lem3849381 (_44737 : int) : (term196 _44737) = (term208 _44737).
Proof. exact (TRANS (@lem3849339 _44737) (@lem3849380 _44737)). Qed.
Lemma lem3849382 (_44734 : int) : (term130 _44734) = (term130 _44734).
Proof. exact (eq_refl (term130 _44734)). Qed.
Lemma lem3849385 (_44734 : int) (_44737 : int) : (term195 _44734 _44737) = (term209 _44734 _44737).
Proof. exact (MK_COMB (@lem3849382 _44734) (@lem3849381 _44737)). Qed.
Lemma lem3849387 (_44734 : int) (_44737 : int) : (term194 _44734 _44737) = (term209 _44734 _44737).
Proof. exact (TRANS (@lem3849338 _44734 _44737) (@lem3849385 _44734 _44737)). Qed.
Lemma lem3849388 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3849389 (_44734 : int) (_44737 : int) : (term210 _44734 _44737) = (term211 _44734 _44737).
Proof. exact (MK_COMB (@lem3849388) (@lem3849387 _44734 _44737)). Qed.
Lemma lem3849390 : term114 = term114.
Proof. exact (eq_refl term114). Qed.
Lemma lem3849391 (_44734 : int) (_44737 : int) : (term193 _44734 _44737) = (term212 _44734 _44737).
Proof. exact (MK_COMB (@lem3849389 _44734 _44737) (@lem3849390)). Qed.
Lemma lem3849392 (_44734 : int) (_44737 : int) : (term134 _44737 _44734) = (term212 _44734 _44737).
Proof. exact (TRANS (@lem3849326 _44734 _44737) (@lem3849391 _44734 _44737)). Qed.
Lemma lem3849393 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3849394 (_44734 : int) (_44737 : int) : (term143 _44734 _44737) = (term226 _44734 _44737).
Proof. exact (MK_COMB (@lem3849393) (@lem3849325 _44734 _44737)). Qed.
Lemma lem3849395 (_44734 : int) (_44737 : int) : (term144 _44737 _44734) = (term227 _44734 _44737).
Proof. exact (MK_COMB (@lem3849394 _44734 _44737) (@lem3849392 _44734 _44737)). Qed.
Lemma lem3849396 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3849397 (_44734 : int) (_44735 : int) (_44736 : int) : (term145 _44734 _44735 _44736) = (term228 _44734 _44735 _44736).
Proof. exact (MK_COMB (@lem3849396) (@lem3849254 _44734 _44735 _44736)). Qed.
Lemma lem3849398 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term146 _44735 _44736 _44737 _44734) = (term229 _44735 _44736 _44734 _44737).
Proof. exact (MK_COMB (@lem3849397 _44734 _44735 _44736) (@lem3849395 _44734 _44737)). Qed.
Lemma lem3849399 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3849400 (_44735 : int) (_44736 : int) (_44737 : int) : (term147 _44736 _44735 _44737) = (term230 _44735 _44736 _44737).
Proof. exact (MK_COMB (@lem3849399) (@lem3849225 _44735 _44736 _44737)). Qed.
Lemma lem3849401 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term148 _44735 _44736 _44737 _44734) = (term231 _44735 _44736 _44734 _44737).
Proof. exact (MK_COMB (@lem3849400 _44735 _44736 _44737) (@lem3849398 _44735 _44736 _44734 _44737)). Qed.
Lemma lem3849402 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3849403 (_44737 : int) : (term149 _44737) = (term232 _44737).
Proof. exact (MK_COMB (@lem3849402) (@lem3849069 _44737)). Qed.
Lemma lem3849404 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term150 _44735 _44736 _44737 _44734) = (term233 _44735 _44736 _44734 _44737).
Proof. exact (MK_COMB (@lem3849403 _44737) (@lem3849401 _44735 _44736 _44734 _44737)). Qed.
Lemma lem3849405 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3849406 (_44736 : int) : (term149 _44736) = (term232 _44736).
Proof. exact (MK_COMB (@lem3849405) (@lem3849021 _44736)). Qed.
Lemma lem3849407 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term151 _44735 _44736 _44737 _44734) = (term234 _44735 _44736 _44734 _44737).
Proof. exact (MK_COMB (@lem3849406 _44736) (@lem3849404 _44735 _44736 _44734 _44737)). Qed.
Lemma lem3849408 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3849409 (_44735 : int) : (term149 _44735) = (term232 _44735).
Proof. exact (MK_COMB (@lem3849408) (@lem3848973 _44735)). Qed.
Lemma lem3849410 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term152 _44735 _44736 _44737 _44734) = (term235 _44735 _44736 _44734 _44737).
Proof. exact (MK_COMB (@lem3849409 _44735) (@lem3849407 _44735 _44736 _44734 _44737)). Qed.
Lemma lem3849411 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3849412 (_44734 : int) : (term149 _44734) = (term232 _44734).
Proof. exact (MK_COMB (@lem3849411) (@lem3848925 _44734)). Qed.
Lemma lem3849413 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term153 _44735 _44736 _44737 _44734) = (term236 _44735 _44736 _44734 _44737).
Proof. exact (MK_COMB (@lem3849412 _44734) (@lem3849410 _44735 _44736 _44734 _44737)). Qed.
Lemma lem3849420 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term155 _44735 _44736 _44737 _44734) = (term236 _44735 _44736 _44734 _44737).
Proof. exact (TRANS (@lem3848877 _44735 _44736 _44737 _44734) (@lem3849413 _44735 _44736 _44734 _44737)). Qed.
Lemma lem3849437 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term229 _44735 _44736 _44734 _44737) = (term237 _44735 _44736 _44734 _44737).
Proof. exact (@lem19158 (term225 _44734 _44737) ((term220 _44734 _44735 _44736) = term114) (term212 _44734 _44737)). Qed.
Lemma lem3849450 (_44735 : int) (_44736 : int) (_44737 : int) : (term230 _44735 _44736 _44737) = (term230 _44735 _44736 _44737).
Proof. exact (eq_refl (term230 _44735 _44736 _44737)). Qed.
Lemma lem3849451 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term231 _44735 _44736 _44734 _44737) = (term238 _44735 _44736 _44734 _44737).
Proof. exact (MK_COMB (@lem3849450 _44735 _44736 _44737) (@lem3849437 _44735 _44736 _44734 _44737)). Qed.
Lemma lem3849452 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term238 _44735 _44736 _44734 _44737) = (term239 _44735 _44736 _44734 _44737).
Proof. exact (@lem19158 (term240 _44735 _44736 _44734 _44737) (term217 _44735 _44736 _44737) (term241 _44735 _44736 _44734 _44737)). Qed.
Lemma lem3849459 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term242 _44735 _44736 _44734 _44737) = (term243 _44735 _44736 _44734 _44737).
Proof. exact (@lem19367 ((term189 _44735 _44736 _44737) = term114) (term215 _44735 _44736 _44737) (term241 _44735 _44736 _44734 _44737)). Qed.
Lemma lem3849466 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term244 _44735 _44736 _44734 _44737) = (term245 _44735 _44736 _44734 _44737).
Proof. exact (@lem19367 ((term189 _44735 _44736 _44737) = term114) (term215 _44735 _44736 _44737) (term240 _44735 _44736 _44734 _44737)). Qed.
Lemma lem3849467 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3849468 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term246 _44735 _44736 _44734 _44737) = (term247 _44735 _44736 _44734 _44737).
Proof. exact (MK_COMB (@lem3849467) (@lem3849466 _44735 _44736 _44734 _44737)). Qed.
Lemma lem3849469 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term239 _44735 _44736 _44734 _44737) = (term248 _44735 _44736 _44734 _44737).
Proof. exact (MK_COMB (@lem3849468 _44735 _44736 _44734 _44737) (@lem3849459 _44735 _44736 _44734 _44737)). Qed.
Lemma lem3849470 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term238 _44735 _44736 _44734 _44737) = (term248 _44735 _44736 _44734 _44737).
Proof. exact (TRANS (@lem3849452 _44735 _44736 _44734 _44737) (@lem3849469 _44735 _44736 _44734 _44737)). Qed.
Lemma lem3849471 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term231 _44735 _44736 _44734 _44737) = (term248 _44735 _44736 _44734 _44737).
Proof. exact (TRANS (@lem3849451 _44735 _44736 _44734 _44737) (@lem3849470 _44735 _44736 _44734 _44737)). Qed.
Lemma lem3849474 (_44737 : int) : (term232 _44737) = (term232 _44737).
Proof. exact (eq_refl (term232 _44737)). Qed.
Lemma lem3849475 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term233 _44735 _44736 _44734 _44737) = (term249 _44735 _44736 _44734 _44737).
Proof. exact (MK_COMB (@lem3849474 _44737) (@lem3849471 _44735 _44736 _44734 _44737)). Qed.
Lemma lem3849476 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term249 _44735 _44736 _44734 _44737) = (term250 _44735 _44736 _44734 _44737).
Proof. exact (@lem19158 (term245 _44735 _44736 _44734 _44737) (term183 _44737) (term243 _44735 _44736 _44734 _44737)). Qed.
Lemma lem3849483 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term251 _44735 _44736 _44734 _44737) = (term252 _44735 _44736 _44734 _44737).
Proof. exact (@lem19158 (term253 _44735 _44736 _44734 _44737) (term183 _44737) (term254 _44735 _44736 _44734 _44737)). Qed.
Lemma lem3849490 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term255 _44735 _44736 _44734 _44737) = (term256 _44735 _44736 _44734 _44737).
Proof. exact (@lem19158 (term257 _44735 _44736 _44734 _44737) (term183 _44737) (term258 _44735 _44736 _44734 _44737)). Qed.
Lemma lem3849491 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3849492 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term259 _44735 _44736 _44734 _44737) = (term260 _44735 _44736 _44734 _44737).
Proof. exact (MK_COMB (@lem3849491) (@lem3849490 _44735 _44736 _44734 _44737)). Qed.
Lemma lem3849493 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term250 _44735 _44736 _44734 _44737) = (term261 _44735 _44736 _44734 _44737).
Proof. exact (MK_COMB (@lem3849492 _44735 _44736 _44734 _44737) (@lem3849483 _44735 _44736 _44734 _44737)). Qed.
Lemma lem3849494 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term249 _44735 _44736 _44734 _44737) = (term261 _44735 _44736 _44734 _44737).
Proof. exact (TRANS (@lem3849476 _44735 _44736 _44734 _44737) (@lem3849493 _44735 _44736 _44734 _44737)). Qed.
Lemma lem3849495 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term233 _44735 _44736 _44734 _44737) = (term261 _44735 _44736 _44734 _44737).
Proof. exact (TRANS (@lem3849475 _44735 _44736 _44734 _44737) (@lem3849494 _44735 _44736 _44734 _44737)). Qed.
Lemma lem3849498 (_44736 : int) : (term232 _44736) = (term232 _44736).
Proof. exact (eq_refl (term232 _44736)). Qed.
Lemma lem3849499 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term234 _44735 _44736 _44734 _44737) = (term262 _44735 _44736 _44734 _44737).
Proof. exact (MK_COMB (@lem3849498 _44736) (@lem3849495 _44735 _44736 _44734 _44737)). Qed.
Lemma lem3849500 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term262 _44735 _44736 _44734 _44737) = (term263 _44735 _44736 _44734 _44737).
Proof. exact (@lem19158 (term256 _44735 _44736 _44734 _44737) (term183 _44736) (term252 _44735 _44736 _44734 _44737)). Qed.
Lemma lem3849507 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term264 _44735 _44736 _44734 _44737) = (term265 _44735 _44736 _44734 _44737).
Proof. exact (@lem19158 (term266 _44735 _44736 _44734 _44737) (term183 _44736) (term267 _44735 _44736 _44734 _44737)). Qed.
Lemma lem3849514 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term268 _44735 _44736 _44734 _44737) = (term269 _44735 _44736 _44734 _44737).
Proof. exact (@lem19158 (term270 _44735 _44736 _44734 _44737) (term183 _44736) (term271 _44735 _44736 _44734 _44737)). Qed.
Lemma lem3849515 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3849516 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term272 _44735 _44736 _44734 _44737) = (term273 _44735 _44736 _44734 _44737).
Proof. exact (MK_COMB (@lem3849515) (@lem3849514 _44735 _44736 _44734 _44737)). Qed.
Lemma lem3849517 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term263 _44735 _44736 _44734 _44737) = (term274 _44735 _44736 _44734 _44737).
Proof. exact (MK_COMB (@lem3849516 _44735 _44736 _44734 _44737) (@lem3849507 _44735 _44736 _44734 _44737)). Qed.
Lemma lem3849518 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term262 _44735 _44736 _44734 _44737) = (term274 _44735 _44736 _44734 _44737).
Proof. exact (TRANS (@lem3849500 _44735 _44736 _44734 _44737) (@lem3849517 _44735 _44736 _44734 _44737)). Qed.
Lemma lem3849519 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term234 _44735 _44736 _44734 _44737) = (term274 _44735 _44736 _44734 _44737).
Proof. exact (TRANS (@lem3849499 _44735 _44736 _44734 _44737) (@lem3849518 _44735 _44736 _44734 _44737)). Qed.
Lemma lem3849522 (_44735 : int) : (term232 _44735) = (term232 _44735).
Proof. exact (eq_refl (term232 _44735)). Qed.
Lemma lem3849523 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term235 _44735 _44736 _44734 _44737) = (term275 _44735 _44736 _44734 _44737).
Proof. exact (MK_COMB (@lem3849522 _44735) (@lem3849519 _44735 _44736 _44734 _44737)). Qed.
Lemma lem3849524 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term275 _44735 _44736 _44734 _44737) = (term276 _44735 _44736 _44734 _44737).
Proof. exact (@lem19158 (term269 _44735 _44736 _44734 _44737) (term183 _44735) (term265 _44735 _44736 _44734 _44737)). Qed.
Lemma lem3849531 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term277 _44735 _44736 _44734 _44737) = (term278 _44735 _44736 _44734 _44737).
Proof. exact (@lem19158 (term279 _44735 _44736 _44734 _44737) (term183 _44735) (term280 _44735 _44736 _44734 _44737)). Qed.
Lemma lem3849538 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term281 _44735 _44736 _44734 _44737) = (term282 _44735 _44736 _44734 _44737).
Proof. exact (@lem19158 (term283 _44735 _44736 _44734 _44737) (term183 _44735) (term284 _44735 _44736 _44734 _44737)). Qed.
Lemma lem3849539 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3849540 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term285 _44735 _44736 _44734 _44737) = (term286 _44735 _44736 _44734 _44737).
Proof. exact (MK_COMB (@lem3849539) (@lem3849538 _44735 _44736 _44734 _44737)). Qed.
Lemma lem3849541 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term276 _44735 _44736 _44734 _44737) = (term287 _44735 _44736 _44734 _44737).
Proof. exact (MK_COMB (@lem3849540 _44735 _44736 _44734 _44737) (@lem3849531 _44735 _44736 _44734 _44737)). Qed.
Lemma lem3849542 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term275 _44735 _44736 _44734 _44737) = (term287 _44735 _44736 _44734 _44737).
Proof. exact (TRANS (@lem3849524 _44735 _44736 _44734 _44737) (@lem3849541 _44735 _44736 _44734 _44737)). Qed.
Lemma lem3849543 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term235 _44735 _44736 _44734 _44737) = (term287 _44735 _44736 _44734 _44737).
Proof. exact (TRANS (@lem3849523 _44735 _44736 _44734 _44737) (@lem3849542 _44735 _44736 _44734 _44737)). Qed.
Lemma lem3849546 (_44734 : int) : (term232 _44734) = (term232 _44734).
Proof. exact (eq_refl (term232 _44734)). Qed.
Lemma lem3849547 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term236 _44735 _44736 _44734 _44737) = (term288 _44735 _44736 _44734 _44737).
Proof. exact (MK_COMB (@lem3849546 _44734) (@lem3849543 _44735 _44736 _44734 _44737)). Qed.
Lemma lem3849548 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term288 _44735 _44736 _44734 _44737) = (term289 _44735 _44736 _44734 _44737).
Proof. exact (@lem19158 (term282 _44735 _44736 _44734 _44737) (term183 _44734) (term278 _44735 _44736 _44734 _44737)). Qed.
Lemma lem3849555 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term290 _44735 _44736 _44734 _44737) = (term291 _44735 _44736 _44734 _44737).
Proof. exact (@lem19158 (term292 _44735 _44736 _44734 _44737) (term183 _44734) (term293 _44735 _44736 _44734 _44737)). Qed.
Lemma lem3849562 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term294 _44735 _44736 _44734 _44737) = (term295 _44735 _44736 _44734 _44737).
Proof. exact (@lem19158 (term296 _44735 _44736 _44734 _44737) (term183 _44734) (term297 _44735 _44736 _44734 _44737)). Qed.
Lemma lem3849563 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3849564 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term298 _44735 _44736 _44734 _44737) = (term299 _44735 _44736 _44734 _44737).
Proof. exact (MK_COMB (@lem3849563) (@lem3849562 _44735 _44736 _44734 _44737)). Qed.
Lemma lem3849565 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term289 _44735 _44736 _44734 _44737) = (term300 _44735 _44736 _44734 _44737).
Proof. exact (MK_COMB (@lem3849564 _44735 _44736 _44734 _44737) (@lem3849555 _44735 _44736 _44734 _44737)). Qed.
Lemma lem3849566 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term288 _44735 _44736 _44734 _44737) = (term300 _44735 _44736 _44734 _44737).
Proof. exact (TRANS (@lem3849548 _44735 _44736 _44734 _44737) (@lem3849565 _44735 _44736 _44734 _44737)). Qed.
Lemma lem3849567 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term236 _44735 _44736 _44734 _44737) = (term300 _44735 _44736 _44734 _44737).
Proof. exact (TRANS (@lem3849547 _44735 _44736 _44734 _44737) (@lem3849566 _44735 _44736 _44734 _44737)). Qed.
Lemma lem3849568 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term155 _44735 _44736 _44737 _44734) = (term300 _44735 _44736 _44734 _44737).
Proof. exact (TRANS (@lem3849420 _44735 _44736 _44734 _44737) (@lem3849567 _44735 _44736 _44734 _44737)). Qed.
Lemma lem3849590 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term300 _44735 _44736 _44734 _44737) : term300 _44735 _44736 _44734 _44737.
Proof. exact (h1). Qed.
Lemma lem3849591 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term295 _44735 _44736 _44734 _44737) : term295 _44735 _44736 _44734 _44737.
Proof. exact (h1). Qed.
Lemma lem3849592 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term301 _44735 _44736 _44734 _44737) : term301 _44735 _44736 _44734 _44737.
Proof. exact (h1). Qed.
Lemma lem3849593 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term301 _44735 _44736 _44734 _44737) : term296 _44735 _44736 _44734 _44737.
Proof. exact (proj2 (@lem3849592 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3849595 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term301 _44735 _44736 _44734 _44737) : term283 _44735 _44736 _44734 _44737.
Proof. exact (proj2 (@lem3849593 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3849597 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term301 _44735 _44736 _44734 _44737) : term270 _44735 _44736 _44734 _44737.
Proof. exact (proj2 (@lem3849595 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3849599 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term301 _44735 _44736 _44734 _44737) : term257 _44735 _44736 _44734 _44737.
Proof. exact (proj2 (@lem3849597 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3849601 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term301 _44735 _44736 _44734 _44737) : term240 _44735 _44736 _44734 _44737.
Proof. exact (proj2 (@lem3849599 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3849602 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term301 _44735 _44736 _44734 _44737) : (term189 _44735 _44736 _44737) = term114.
Proof. exact (proj1 (@lem3849599 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3849603 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term301 _44735 _44736 _44734 _44737) : term225 _44734 _44737.
Proof. exact (proj2 (@lem3849601 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3849604 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term301 _44735 _44736 _44734 _44737) : (term220 _44734 _44735 _44736) = term114.
Proof. exact (proj1 (@lem3849601 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3849606 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3849607 : term302 = term303.
Proof. exact (@lem3849606 term114 term128). Qed.
Lemma lem3849609 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3849610 : term128 = term198.
Proof. exact (@lem3849609 term129). Qed.
Lemma lem3849612 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3849613 : term114 = term160.
Proof. exact (@lem3849612 (NUMERAL 0)). Qed.
Lemma lem3849614 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3849615 : term304 = term305.
Proof. exact (MK_COMB (@lem3849614) (@lem3849613)). Qed.
Lemma lem3849616 : term303 = term306.
Proof. exact (MK_COMB (@lem3849615) (@lem3849610)). Qed.
Lemma lem3849617 : term307.
Proof. exact (@lem1980255 term114 term128 term128 term128). Qed.
Lemma lem3849619 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3849620 : term303 = term309.
Proof. exact (@lem3849619 (NUMERAL 0) term129). Qed.
Lemma lem3849621 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3849622 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3849623 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3849622 h1) (fun h1 : term309 = True => @lem3849621)). Qed.
Lemma lem3849624 : term309 = True.
Proof. exact (EQ_MP (@lem3849623) (@lem3849621)). Qed.
Lemma lem3849625 : term303 = True.
Proof. exact (TRANS (@lem3849620) (@lem3849624)). Qed.
Lemma lem3849626 : True = term303.
Proof. exact (SYM (@lem3849625)). Qed.
Lemma lem3849627 : term303.
Proof. exact (EQ_MP (@lem3849626) (@lem0)). Qed.
Lemma lem3849628 : term311.
Proof. exact (@lem3849617 (@lem3849627)). Qed.
Lemma lem3849630 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3849631 : term303 = term309.
Proof. exact (@lem3849630 (NUMERAL 0) term129). Qed.
Lemma lem3849632 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3849633 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3849634 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3849633 h1) (fun h1 : term309 = True => @lem3849632)). Qed.
Lemma lem3849635 : term309 = True.
Proof. exact (EQ_MP (@lem3849634) (@lem3849632)). Qed.
Lemma lem3849636 : term303 = True.
Proof. exact (TRANS (@lem3849631) (@lem3849635)). Qed.
Lemma lem3849637 : True = term303.
Proof. exact (SYM (@lem3849636)). Qed.
Lemma lem3849638 : term303.
Proof. exact (EQ_MP (@lem3849637) (@lem0)). Qed.
Lemma lem3849639 : term306 = term312.
Proof. exact (@lem3849628 (@lem3849638)). Qed.
Lemma lem3849641 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3849642 : term172 = term173.
Proof. exact (@lem3849641 term129 term129). Qed.
Lemma lem3849643 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3849644 : term175 = term129.
Proof. exact (EQ_MP (@lem3849643) (@lem940073)). Qed.
Lemma lem3849645 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3849646 : term173 = term128.
Proof. exact (MK_COMB (@lem3849645) (@lem3849644)). Qed.
Lemma lem3849647 : term172 = term128.
Proof. exact (TRANS (@lem3849642) (@lem3849646)). Qed.
Lemma lem3849649 (x : nat) : (term313 x) = term114.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3849650 : term314 = term114.
Proof. exact (@lem3849649 term129). Qed.
Lemma lem3849651 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3849652 : term315 = term304.
Proof. exact (MK_COMB (@lem3849651) (@lem3849650)). Qed.
Lemma lem3849653 : term312 = term303.
Proof. exact (MK_COMB (@lem3849652) (@lem3849647)). Qed.
Lemma lem3849655 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3849656 : term303 = term309.
Proof. exact (@lem3849655 (NUMERAL 0) term129). Qed.
Lemma lem3849657 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3849658 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3849659 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3849658 h1) (fun h1 : term309 = True => @lem3849657)). Qed.
Lemma lem3849660 : term309 = True.
Proof. exact (EQ_MP (@lem3849659) (@lem3849657)). Qed.
Lemma lem3849661 : term303 = True.
Proof. exact (TRANS (@lem3849656) (@lem3849660)). Qed.
Lemma lem3849662 : term312 = True.
Proof. exact (TRANS (@lem3849653) (@lem3849661)). Qed.
Lemma lem3849663 : term306 = True.
Proof. exact (TRANS (@lem3849639) (@lem3849662)). Qed.
Lemma lem3849664 : term303 = True.
Proof. exact (TRANS (@lem3849616) (@lem3849663)). Qed.
Lemma lem3849665 : term302 = True.
Proof. exact (TRANS (@lem3849607) (@lem3849664)). Qed.
Lemma lem3849666 : True = term302.
Proof. exact (SYM (@lem3849665)). Qed.
Lemma lem3849667 : term302.
Proof. exact (EQ_MP (@lem3849666) (@lem0)). Qed.
Lemma lem3849668 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term301 _44735 _44736 _44734 _44737) : term316 _44734 _44737.
Proof. exact (conj (@lem3849667) (@lem3849603 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3849670 (x : real) (y : real) : term317 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3849671 (_44734 : int) (_44737 : int) : term318 _44734 _44737.
Proof. exact (@lem3849670 term128 (term223 _44734 _44737)). Qed.
Lemma lem3849672 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term301 _44735 _44736 _44734 _44737) : term319 _44734 _44737.
Proof. exact (@lem3849671 _44734 _44737 (@lem3849668 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3849673 (_44734 : int) (_44737 : int) : (term320 _44734 _44737) = (term223 _44734 _44737).
Proof. exact (@lem1982733 (term223 _44734 _44737)). Qed.
Lemma lem3849674 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3849675 (_44734 : int) (_44737 : int) : (term321 _44734 _44737) = (term224 _44734 _44737).
Proof. exact (MK_COMB (@lem3849674) (@lem3849673 _44734 _44737)). Qed.
Lemma lem3849676 : term114 = term114.
Proof. exact (eq_refl term114). Qed.
Lemma lem3849677 (_44734 : int) (_44737 : int) : (term319 _44734 _44737) = (term225 _44734 _44737).
Proof. exact (MK_COMB (@lem3849675 _44734 _44737) (@lem3849676)). Qed.
Lemma lem3849678 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term301 _44735 _44736 _44734 _44737) : term225 _44734 _44737.
Proof. exact (EQ_MP (@lem3849677 _44734 _44737) (@lem3849672 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3849680 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3849681 : term302 = term303.
Proof. exact (@lem3849680 term114 term128). Qed.
Lemma lem3849683 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3849684 : term128 = term198.
Proof. exact (@lem3849683 term129). Qed.
Lemma lem3849686 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3849687 : term114 = term160.
Proof. exact (@lem3849686 (NUMERAL 0)). Qed.
Lemma lem3849688 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3849689 : term304 = term305.
Proof. exact (MK_COMB (@lem3849688) (@lem3849687)). Qed.
Lemma lem3849690 : term303 = term306.
Proof. exact (MK_COMB (@lem3849689) (@lem3849684)). Qed.
Lemma lem3849691 : term307.
Proof. exact (@lem1980255 term114 term128 term128 term128). Qed.
Lemma lem3849693 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3849694 : term303 = term309.
Proof. exact (@lem3849693 (NUMERAL 0) term129). Qed.
Lemma lem3849695 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3849696 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3849697 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3849696 h1) (fun h1 : term309 = True => @lem3849695)). Qed.
Lemma lem3849698 : term309 = True.
Proof. exact (EQ_MP (@lem3849697) (@lem3849695)). Qed.
Lemma lem3849699 : term303 = True.
Proof. exact (TRANS (@lem3849694) (@lem3849698)). Qed.
Lemma lem3849700 : True = term303.
Proof. exact (SYM (@lem3849699)). Qed.
Lemma lem3849701 : term303.
Proof. exact (EQ_MP (@lem3849700) (@lem0)). Qed.
Lemma lem3849702 : term311.
Proof. exact (@lem3849691 (@lem3849701)). Qed.
Lemma lem3849704 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3849705 : term303 = term309.
Proof. exact (@lem3849704 (NUMERAL 0) term129). Qed.
Lemma lem3849706 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3849707 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3849708 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3849707 h1) (fun h1 : term309 = True => @lem3849706)). Qed.
Lemma lem3849709 : term309 = True.
Proof. exact (EQ_MP (@lem3849708) (@lem3849706)). Qed.
Lemma lem3849710 : term303 = True.
Proof. exact (TRANS (@lem3849705) (@lem3849709)). Qed.
Lemma lem3849711 : True = term303.
Proof. exact (SYM (@lem3849710)). Qed.
Lemma lem3849712 : term303.
Proof. exact (EQ_MP (@lem3849711) (@lem0)). Qed.
Lemma lem3849713 : term306 = term312.
Proof. exact (@lem3849702 (@lem3849712)). Qed.
Lemma lem3849715 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3849716 : term172 = term173.
Proof. exact (@lem3849715 term129 term129). Qed.
Lemma lem3849717 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3849718 : term175 = term129.
Proof. exact (EQ_MP (@lem3849717) (@lem940073)). Qed.
Lemma lem3849719 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3849720 : term173 = term128.
Proof. exact (MK_COMB (@lem3849719) (@lem3849718)). Qed.
Lemma lem3849721 : term172 = term128.
Proof. exact (TRANS (@lem3849716) (@lem3849720)). Qed.
Lemma lem3849723 (x : nat) : (term313 x) = term114.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3849724 : term314 = term114.
Proof. exact (@lem3849723 term129). Qed.
Lemma lem3849725 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3849726 : term315 = term304.
Proof. exact (MK_COMB (@lem3849725) (@lem3849724)). Qed.
Lemma lem3849727 : term312 = term303.
Proof. exact (MK_COMB (@lem3849726) (@lem3849721)). Qed.
Lemma lem3849729 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3849730 : term303 = term309.
Proof. exact (@lem3849729 (NUMERAL 0) term129). Qed.
Lemma lem3849731 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3849732 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3849733 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3849732 h1) (fun h1 : term309 = True => @lem3849731)). Qed.
Lemma lem3849734 : term309 = True.
Proof. exact (EQ_MP (@lem3849733) (@lem3849731)). Qed.
Lemma lem3849735 : term303 = True.
Proof. exact (TRANS (@lem3849730) (@lem3849734)). Qed.
Lemma lem3849736 : term312 = True.
Proof. exact (TRANS (@lem3849727) (@lem3849735)). Qed.
Lemma lem3849737 : term306 = True.
Proof. exact (TRANS (@lem3849713) (@lem3849736)). Qed.
Lemma lem3849738 : term303 = True.
Proof. exact (TRANS (@lem3849690) (@lem3849737)). Qed.
Lemma lem3849739 : term302 = True.
Proof. exact (TRANS (@lem3849681) (@lem3849738)). Qed.
Lemma lem3849740 : True = term302.
Proof. exact (SYM (@lem3849739)). Qed.
Lemma lem3849741 : term302.
Proof. exact (EQ_MP (@lem3849740) (@lem0)). Qed.
Lemma lem3849742 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term301 _44735 _44736 _44734 _44737) : term322 _44735 _44736 _44737.
Proof. exact (conj (@lem3849741) (@lem3849602 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3849744 (x : real) (y : real) : term323 x y.
Proof. exact (proj1 (@lem1988330 x y)). Qed.
Lemma lem3849745 (_44735 : int) (_44736 : int) (_44737 : int) : term324 _44735 _44736 _44737.
Proof. exact (@lem3849744 term128 (term189 _44735 _44736 _44737)). Qed.
Lemma lem3849746 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term301 _44735 _44736 _44734 _44737) : (term325 _44735 _44736 _44737) = term114.
Proof. exact (@lem3849745 _44735 _44736 _44737 (@lem3849742 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3849747 (_44735 : int) (_44736 : int) (_44737 : int) : (term325 _44735 _44736 _44737) = (term189 _44735 _44736 _44737).
Proof. exact (@lem1982733 (term189 _44735 _44736 _44737)). Qed.
Lemma lem3849748 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3849749 (_44735 : int) (_44736 : int) (_44737 : int) : (term326 _44735 _44736 _44737) = (term192 _44735 _44736 _44737).
Proof. exact (MK_COMB (@lem3849748) (@lem3849747 _44735 _44736 _44737)). Qed.
Lemma lem3849750 : term114 = term114.
Proof. exact (eq_refl term114). Qed.
Lemma lem3849751 (_44735 : int) (_44736 : int) (_44737 : int) : ((term325 _44735 _44736 _44737) = term114) = ((term189 _44735 _44736 _44737) = term114).
Proof. exact (MK_COMB (@lem3849749 _44735 _44736 _44737) (@lem3849750)). Qed.
Lemma lem3849752 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term301 _44735 _44736 _44734 _44737) : (term189 _44735 _44736 _44737) = term114.
Proof. exact (EQ_MP (@lem3849751 _44735 _44736 _44737) (@lem3849746 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3849754 (y : real) : term327 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem3849755 (_44734 : int) (_44735 : int) (_44736 : int) : term328 _44734 _44735 _44736.
Proof. exact (@lem3849754 (term220 _44734 _44735 _44736)). Qed.
Lemma lem3849756 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term301 _44735 _44736 _44734 _44737) : term329 _44734 _44735 _44736.
Proof. exact (@lem3849755 _44734 _44735 _44736 (@lem3849604 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3849757 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term301 _44735 _44736 _44734 _44737) : term330 _44734 _44735 _44736.
Proof. exact (@lem3849756 _44735 _44736 _44734 _44737 h1 term128). Qed.
Lemma lem3849758 (_44734 : int) (_44735 : int) (_44736 : int) : (term330 _44734 _44735 _44736) = ((term331 _44734 _44735 _44736) = term114).
Proof. exact (eq_refl (term330 _44734 _44735 _44736)). Qed.
Lemma lem3849759 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term301 _44735 _44736 _44734 _44737) : (term331 _44734 _44735 _44736) = term114.
Proof. exact (EQ_MP (@lem3849758 _44734 _44735 _44736) (@lem3849757 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3849760 (_44734 : int) (_44735 : int) (_44736 : int) : (term331 _44734 _44735 _44736) = (term220 _44734 _44735 _44736).
Proof. exact (@lem1982733 (term220 _44734 _44735 _44736)). Qed.
Lemma lem3849761 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3849762 (_44734 : int) (_44735 : int) (_44736 : int) : (term332 _44734 _44735 _44736) = (term222 _44734 _44735 _44736).
Proof. exact (MK_COMB (@lem3849761) (@lem3849760 _44734 _44735 _44736)). Qed.
Lemma lem3849763 : term114 = term114.
Proof. exact (eq_refl term114). Qed.
Lemma lem3849764 (_44734 : int) (_44735 : int) (_44736 : int) : ((term331 _44734 _44735 _44736) = term114) = ((term220 _44734 _44735 _44736) = term114).
Proof. exact (MK_COMB (@lem3849762 _44734 _44735 _44736) (@lem3849763)). Qed.
Lemma lem3849765 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term301 _44735 _44736 _44734 _44737) : (term220 _44734 _44735 _44736) = term114.
Proof. exact (EQ_MP (@lem3849764 _44734 _44735 _44736) (@lem3849759 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3849766 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term301 _44735 _44736 _44734 _44737) : term333 _44734 _44735 _44736 _44737.
Proof. exact (conj (@lem3849765 _44735 _44736 _44734 _44737 h1) (@lem3849752 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3849768 (x : real) (y : real) : term334 x y.
Proof. exact (proj1 (@lem1393126 x y)). Qed.
Lemma lem3849769 (_44734 : int) (_44735 : int) (_44736 : int) (_44737 : int) : term335 _44734 _44735 _44736 _44737.
Proof. exact (@lem3849768 (term220 _44734 _44735 _44736) (term189 _44735 _44736 _44737)). Qed.
Lemma lem3849770 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term301 _44735 _44736 _44734 _44737) : (term336 _44734 _44735 _44736 _44737) = term114.
Proof. exact (@lem3849769 _44734 _44735 _44736 _44737 (@lem3849766 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3849771 (_44734 : int) (_44735 : int) (_44736 : int) (_44737 : int) : (term336 _44734 _44735 _44736 _44737) = (term337 _44734 _44735 _44736 _44737).
Proof. exact (@lem1982755 (real_of_int _44734) (term338 _44735 _44736) (term189 _44735 _44736 _44737)). Qed.
Lemma lem3849772 (_44735 : int) (_44736 : int) (_44737 : int) : (term339 _44735 _44736 _44737) = (term340 _44735 _44736 _44737).
Proof. exact (@lem1982753 (real_of_int _44735) (term190 _44735) (term190 _44736) (term338 _44736 _44737)). Qed.
Lemma lem3849773 (_44735 : int) : (term341 _44735) = (term342 _44735).
Proof. exact (@lem1982715 term163 (real_of_int _44735)). Qed.
Lemma lem3849775 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3849776 : term128 = term198.
Proof. exact (@lem3849775 term129). Qed.
Lemma lem3849778 (x : nat) : (term161 x) = (term162 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3849779 : term163 = term164.
Proof. exact (@lem3849778 term129). Qed.
Lemma lem3849780 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3849781 : term343 = term344.
Proof. exact (MK_COMB (@lem3849780) (@lem3849779)). Qed.
Lemma lem3849782 : term345 = term346.
Proof. exact (MK_COMB (@lem3849781) (@lem3849776)). Qed.
Lemma lem3849783 : term347.
Proof. exact (@lem1981473 term163 term128 term128 term128 term114 term128). Qed.
Lemma lem3849785 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3849786 : term303 = term309.
Proof. exact (@lem3849785 (NUMERAL 0) term129). Qed.
Lemma lem3849787 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3849788 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3849789 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3849788 h1) (fun h1 : term309 = True => @lem3849787)). Qed.
Lemma lem3849790 : term309 = True.
Proof. exact (EQ_MP (@lem3849789) (@lem3849787)). Qed.
Lemma lem3849791 : term303 = True.
Proof. exact (TRANS (@lem3849786) (@lem3849790)). Qed.
Lemma lem3849792 : True = term303.
Proof. exact (SYM (@lem3849791)). Qed.
Lemma lem3849793 : term303.
Proof. exact (EQ_MP (@lem3849792) (@lem0)). Qed.
Lemma lem3849794 : term348.
Proof. exact (@lem3849783 (@lem3849793)). Qed.
Lemma lem3849796 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3849797 : term303 = term309.
Proof. exact (@lem3849796 (NUMERAL 0) term129). Qed.
Lemma lem3849798 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3849799 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3849800 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3849799 h1) (fun h1 : term309 = True => @lem3849798)). Qed.
Lemma lem3849801 : term309 = True.
Proof. exact (EQ_MP (@lem3849800) (@lem3849798)). Qed.
Lemma lem3849802 : term303 = True.
Proof. exact (TRANS (@lem3849797) (@lem3849801)). Qed.
Lemma lem3849803 : True = term303.
Proof. exact (SYM (@lem3849802)). Qed.
Lemma lem3849804 : term303.
Proof. exact (EQ_MP (@lem3849803) (@lem0)). Qed.
Lemma lem3849805 : term349.
Proof. exact (@lem3849794 (@lem3849804)). Qed.
Lemma lem3849807 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3849808 : term303 = term309.
Proof. exact (@lem3849807 (NUMERAL 0) term129). Qed.
Lemma lem3849809 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3849810 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3849811 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3849810 h1) (fun h1 : term309 = True => @lem3849809)). Qed.
Lemma lem3849812 : term309 = True.
Proof. exact (EQ_MP (@lem3849811) (@lem3849809)). Qed.
Lemma lem3849813 : term303 = True.
Proof. exact (TRANS (@lem3849808) (@lem3849812)). Qed.
Lemma lem3849814 : True = term303.
Proof. exact (SYM (@lem3849813)). Qed.
Lemma lem3849815 : term303.
Proof. exact (EQ_MP (@lem3849814) (@lem0)). Qed.
Lemma lem3849816 : term350.
Proof. exact (@lem3849805 (@lem3849815)). Qed.
Lemma lem3849818 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3849819 : term172 = term173.
Proof. exact (@lem3849818 term129 term129). Qed.
Lemma lem3849820 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3849821 : term175 = term129.
Proof. exact (EQ_MP (@lem3849820) (@lem940073)). Qed.
Lemma lem3849822 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3849823 : term173 = term128.
Proof. exact (MK_COMB (@lem3849822) (@lem3849821)). Qed.
Lemma lem3849824 : term172 = term128.
Proof. exact (TRANS (@lem3849819) (@lem3849823)). Qed.
Lemma lem3849826 (m : nat) (n : nat) : (term202 m n) = (term203 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3849827 : term199 = term204.
Proof. exact (@lem3849826 term129 term129). Qed.
Lemma lem3849828 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3849829 : term175 = term129.
Proof. exact (EQ_MP (@lem3849828) (@lem940073)). Qed.
Lemma lem3849830 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3849831 : term173 = term128.
Proof. exact (MK_COMB (@lem3849830) (@lem3849829)). Qed.
Lemma lem3849832 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3849833 : term204 = term163.
Proof. exact (MK_COMB (@lem3849832) (@lem3849831)). Qed.
Lemma lem3849834 : term199 = term163.
Proof. exact (TRANS (@lem3849827) (@lem3849833)). Qed.
Lemma lem3849835 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3849836 : term351 = term343.
Proof. exact (MK_COMB (@lem3849835) (@lem3849834)). Qed.
Lemma lem3849837 : term352 = term345.
Proof. exact (MK_COMB (@lem3849836) (@lem3849824)). Qed.
Lemma lem3849839 (m : nat) : (term353 m) = term114.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3849840 : term345 = term114.
Proof. exact (@lem3849839 term129). Qed.
Lemma lem3849841 : term352 = term114.
Proof. exact (TRANS (@lem3849837) (@lem3849840)). Qed.
Lemma lem3849842 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3849843 : term354 = term355.
Proof. exact (MK_COMB (@lem3849842) (@lem3849841)). Qed.
Lemma lem3849844 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem3849845 : term356 = term314.
Proof. exact (MK_COMB (@lem3849843) (@lem3849844)). Qed.
Lemma lem3849847 (x : nat) : (term313 x) = term114.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3849848 : term314 = term114.
Proof. exact (@lem3849847 term129). Qed.
Lemma lem3849849 : term356 = term114.
Proof. exact (TRANS (@lem3849845) (@lem3849848)). Qed.
Lemma lem3849851 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3849852 : term172 = term173.
Proof. exact (@lem3849851 term129 term129). Qed.
Lemma lem3849853 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3849854 : term175 = term129.
Proof. exact (EQ_MP (@lem3849853) (@lem940073)). Qed.
Lemma lem3849855 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3849856 : term173 = term128.
Proof. exact (MK_COMB (@lem3849855) (@lem3849854)). Qed.
Lemma lem3849857 : term172 = term128.
Proof. exact (TRANS (@lem3849852) (@lem3849856)). Qed.
Lemma lem3849858 : term355 = term355.
Proof. exact (eq_refl term355). Qed.
Lemma lem3849859 : term357 = term314.
Proof. exact (MK_COMB (@lem3849858) (@lem3849857)). Qed.
Lemma lem3849861 (x : nat) : (term313 x) = term114.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3849862 : term314 = term114.
Proof. exact (@lem3849861 term129). Qed.
Lemma lem3849863 : term357 = term114.
Proof. exact (TRANS (@lem3849859) (@lem3849862)). Qed.
Lemma lem3849864 : term114 = term357.
Proof. exact (SYM (@lem3849863)). Qed.
Lemma lem3849865 : term356 = term357.
Proof. exact (TRANS (@lem3849849) (@lem3849864)). Qed.
Lemma lem3849866 : term346 = term160.
Proof. exact (@lem3849816 (@lem3849865)). Qed.
Lemma lem3849867 : term345 = term160.
Proof. exact (TRANS (@lem3849782) (@lem3849866)). Qed.
Lemma lem3849869 (x : real) : (term179 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3849870 : term160 = term114.
Proof. exact (@lem3849869 term114). Qed.
Lemma lem3849871 : term345 = term114.
Proof. exact (TRANS (@lem3849867) (@lem3849870)). Qed.
Lemma lem3849872 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3849873 : term358 = term355.
Proof. exact (MK_COMB (@lem3849872) (@lem3849871)). Qed.
Lemma lem3849874 (_44735 : int) : (real_of_int _44735) = (real_of_int _44735).
Proof. exact (eq_refl (real_of_int _44735)). Qed.
Lemma lem3849875 (_44735 : int) : (term342 _44735) = (term359 _44735).
Proof. exact (MK_COMB (@lem3849873) (@lem3849874 _44735)). Qed.
Lemma lem3849876 (_44735 : int) : (term341 _44735) = (term359 _44735).
Proof. exact (TRANS (@lem3849773 _44735) (@lem3849875 _44735)). Qed.
Lemma lem3849877 (_44735 : int) : (term359 _44735) = term114.
Proof. exact (@lem1982719 (real_of_int _44735)). Qed.
Lemma lem3849878 (_44735 : int) : (term341 _44735) = term114.
Proof. exact (TRANS (@lem3849876 _44735) (@lem3849877 _44735)). Qed.
Lemma lem3849879 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3849880 (_44735 : int) : (term360 _44735) = term361.
Proof. exact (MK_COMB (@lem3849879) (@lem3849878 _44735)). Qed.
Lemma lem3849881 (_44736 : int) (_44737 : int) : (term362 _44736 _44737) = (term363 _44736 _44737).
Proof. exact (@lem1982763 (term190 _44736) (real_of_int _44736) (term190 _44737)). Qed.
Lemma lem3849882 (_44736 : int) : (term364 _44736) = (term342 _44736).
Proof. exact (@lem1982713 term163 (real_of_int _44736)). Qed.
Lemma lem3849884 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3849885 : term128 = term198.
Proof. exact (@lem3849884 term129). Qed.
Lemma lem3849887 (x : nat) : (term161 x) = (term162 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3849888 : term163 = term164.
Proof. exact (@lem3849887 term129). Qed.
Lemma lem3849889 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3849890 : term343 = term344.
Proof. exact (MK_COMB (@lem3849889) (@lem3849888)). Qed.
Lemma lem3849891 : term345 = term346.
Proof. exact (MK_COMB (@lem3849890) (@lem3849885)). Qed.
Lemma lem3849892 : term347.
Proof. exact (@lem1981473 term163 term128 term128 term128 term114 term128). Qed.
Lemma lem3849894 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3849895 : term303 = term309.
Proof. exact (@lem3849894 (NUMERAL 0) term129). Qed.
Lemma lem3849896 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3849897 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3849898 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3849897 h1) (fun h1 : term309 = True => @lem3849896)). Qed.
Lemma lem3849899 : term309 = True.
Proof. exact (EQ_MP (@lem3849898) (@lem3849896)). Qed.
Lemma lem3849900 : term303 = True.
Proof. exact (TRANS (@lem3849895) (@lem3849899)). Qed.
Lemma lem3849901 : True = term303.
Proof. exact (SYM (@lem3849900)). Qed.
Lemma lem3849902 : term303.
Proof. exact (EQ_MP (@lem3849901) (@lem0)). Qed.
Lemma lem3849903 : term348.
Proof. exact (@lem3849892 (@lem3849902)). Qed.
Lemma lem3849905 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3849906 : term303 = term309.
Proof. exact (@lem3849905 (NUMERAL 0) term129). Qed.
Lemma lem3849907 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3849908 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3849909 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3849908 h1) (fun h1 : term309 = True => @lem3849907)). Qed.
Lemma lem3849910 : term309 = True.
Proof. exact (EQ_MP (@lem3849909) (@lem3849907)). Qed.
Lemma lem3849911 : term303 = True.
Proof. exact (TRANS (@lem3849906) (@lem3849910)). Qed.
Lemma lem3849912 : True = term303.
Proof. exact (SYM (@lem3849911)). Qed.
Lemma lem3849913 : term303.
Proof. exact (EQ_MP (@lem3849912) (@lem0)). Qed.
Lemma lem3849914 : term349.
Proof. exact (@lem3849903 (@lem3849913)). Qed.
Lemma lem3849916 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3849917 : term303 = term309.
Proof. exact (@lem3849916 (NUMERAL 0) term129). Qed.
Lemma lem3849918 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3849919 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3849920 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3849919 h1) (fun h1 : term309 = True => @lem3849918)). Qed.
Lemma lem3849921 : term309 = True.
Proof. exact (EQ_MP (@lem3849920) (@lem3849918)). Qed.
Lemma lem3849922 : term303 = True.
Proof. exact (TRANS (@lem3849917) (@lem3849921)). Qed.
Lemma lem3849923 : True = term303.
Proof. exact (SYM (@lem3849922)). Qed.
Lemma lem3849924 : term303.
Proof. exact (EQ_MP (@lem3849923) (@lem0)). Qed.
Lemma lem3849925 : term350.
Proof. exact (@lem3849914 (@lem3849924)). Qed.
Lemma lem3849927 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3849928 : term172 = term173.
Proof. exact (@lem3849927 term129 term129). Qed.
Lemma lem3849929 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3849930 : term175 = term129.
Proof. exact (EQ_MP (@lem3849929) (@lem940073)). Qed.
Lemma lem3849931 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3849932 : term173 = term128.
Proof. exact (MK_COMB (@lem3849931) (@lem3849930)). Qed.
Lemma lem3849933 : term172 = term128.
Proof. exact (TRANS (@lem3849928) (@lem3849932)). Qed.
Lemma lem3849935 (m : nat) (n : nat) : (term202 m n) = (term203 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3849936 : term199 = term204.
Proof. exact (@lem3849935 term129 term129). Qed.
Lemma lem3849937 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3849938 : term175 = term129.
Proof. exact (EQ_MP (@lem3849937) (@lem940073)). Qed.
Lemma lem3849939 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3849940 : term173 = term128.
Proof. exact (MK_COMB (@lem3849939) (@lem3849938)). Qed.
Lemma lem3849941 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3849942 : term204 = term163.
Proof. exact (MK_COMB (@lem3849941) (@lem3849940)). Qed.
Lemma lem3849943 : term199 = term163.
Proof. exact (TRANS (@lem3849936) (@lem3849942)). Qed.
Lemma lem3849944 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3849945 : term351 = term343.
Proof. exact (MK_COMB (@lem3849944) (@lem3849943)). Qed.
Lemma lem3849946 : term352 = term345.
Proof. exact (MK_COMB (@lem3849945) (@lem3849933)). Qed.
Lemma lem3849948 (m : nat) : (term353 m) = term114.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3849949 : term345 = term114.
Proof. exact (@lem3849948 term129). Qed.
Lemma lem3849950 : term352 = term114.
Proof. exact (TRANS (@lem3849946) (@lem3849949)). Qed.
Lemma lem3849951 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3849952 : term354 = term355.
Proof. exact (MK_COMB (@lem3849951) (@lem3849950)). Qed.
Lemma lem3849953 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem3849954 : term356 = term314.
Proof. exact (MK_COMB (@lem3849952) (@lem3849953)). Qed.
Lemma lem3849956 (x : nat) : (term313 x) = term114.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3849957 : term314 = term114.
Proof. exact (@lem3849956 term129). Qed.
Lemma lem3849958 : term356 = term114.
Proof. exact (TRANS (@lem3849954) (@lem3849957)). Qed.
Lemma lem3849960 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3849961 : term172 = term173.
Proof. exact (@lem3849960 term129 term129). Qed.
Lemma lem3849962 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3849963 : term175 = term129.
Proof. exact (EQ_MP (@lem3849962) (@lem940073)). Qed.
Lemma lem3849964 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3849965 : term173 = term128.
Proof. exact (MK_COMB (@lem3849964) (@lem3849963)). Qed.
Lemma lem3849966 : term172 = term128.
Proof. exact (TRANS (@lem3849961) (@lem3849965)). Qed.
Lemma lem3849967 : term355 = term355.
Proof. exact (eq_refl term355). Qed.
Lemma lem3849968 : term357 = term314.
Proof. exact (MK_COMB (@lem3849967) (@lem3849966)). Qed.
Lemma lem3849970 (x : nat) : (term313 x) = term114.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3849971 : term314 = term114.
Proof. exact (@lem3849970 term129). Qed.
Lemma lem3849972 : term357 = term114.
Proof. exact (TRANS (@lem3849968) (@lem3849971)). Qed.
Lemma lem3849973 : term114 = term357.
Proof. exact (SYM (@lem3849972)). Qed.
Lemma lem3849974 : term356 = term357.
Proof. exact (TRANS (@lem3849958) (@lem3849973)). Qed.
Lemma lem3849975 : term346 = term160.
Proof. exact (@lem3849925 (@lem3849974)). Qed.
Lemma lem3849976 : term345 = term160.
Proof. exact (TRANS (@lem3849891) (@lem3849975)). Qed.
Lemma lem3849978 (x : real) : (term179 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3849979 : term160 = term114.
Proof. exact (@lem3849978 term114). Qed.
Lemma lem3849980 : term345 = term114.
Proof. exact (TRANS (@lem3849976) (@lem3849979)). Qed.
Lemma lem3849981 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3849982 : term358 = term355.
Proof. exact (MK_COMB (@lem3849981) (@lem3849980)). Qed.
Lemma lem3849983 (_44736 : int) : (real_of_int _44736) = (real_of_int _44736).
Proof. exact (eq_refl (real_of_int _44736)). Qed.
Lemma lem3849984 (_44736 : int) : (term342 _44736) = (term359 _44736).
Proof. exact (MK_COMB (@lem3849982) (@lem3849983 _44736)). Qed.
Lemma lem3849985 (_44736 : int) : (term364 _44736) = (term359 _44736).
Proof. exact (TRANS (@lem3849882 _44736) (@lem3849984 _44736)). Qed.
Lemma lem3849986 (_44736 : int) : (term359 _44736) = term114.
Proof. exact (@lem1982719 (real_of_int _44736)). Qed.
Lemma lem3849987 (_44736 : int) : (term364 _44736) = term114.
Proof. exact (TRANS (@lem3849985 _44736) (@lem3849986 _44736)). Qed.
Lemma lem3849988 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3849989 (_44736 : int) : (term365 _44736) = term361.
Proof. exact (MK_COMB (@lem3849988) (@lem3849987 _44736)). Qed.
Lemma lem3849990 (_44737 : int) : (term190 _44737) = (term190 _44737).
Proof. exact (eq_refl (term190 _44737)). Qed.
Lemma lem3849991 (_44736 : int) (_44737 : int) : (term363 _44736 _44737) = (term366 _44737).
Proof. exact (MK_COMB (@lem3849989 _44736) (@lem3849990 _44737)). Qed.
Lemma lem3849992 (_44736 : int) (_44737 : int) : (term362 _44736 _44737) = (term366 _44737).
Proof. exact (TRANS (@lem3849881 _44736 _44737) (@lem3849991 _44736 _44737)). Qed.
Lemma lem3849993 (_44737 : int) : (term366 _44737) = (term190 _44737).
Proof. exact (@lem1982721 (term190 _44737)). Qed.
Lemma lem3849994 (_44736 : int) (_44737 : int) : (term362 _44736 _44737) = (term190 _44737).
Proof. exact (TRANS (@lem3849992 _44736 _44737) (@lem3849993 _44737)). Qed.
Lemma lem3849995 (_44735 : int) (_44736 : int) (_44737 : int) : (term340 _44735 _44736 _44737) = (term366 _44737).
Proof. exact (MK_COMB (@lem3849880 _44735) (@lem3849994 _44736 _44737)). Qed.
Lemma lem3849996 (_44735 : int) (_44736 : int) (_44737 : int) : (term339 _44735 _44736 _44737) = (term366 _44737).
Proof. exact (TRANS (@lem3849772 _44735 _44736 _44737) (@lem3849995 _44735 _44736 _44737)). Qed.
Lemma lem3849997 (_44737 : int) : (term366 _44737) = (term190 _44737).
Proof. exact (@lem1982721 (term190 _44737)). Qed.
Lemma lem3849998 (_44735 : int) (_44736 : int) (_44737 : int) : (term339 _44735 _44736 _44737) = (term190 _44737).
Proof. exact (TRANS (@lem3849996 _44735 _44736 _44737) (@lem3849997 _44737)). Qed.
Lemma lem3849999 (_44734 : int) : (term130 _44734) = (term130 _44734).
Proof. exact (eq_refl (term130 _44734)). Qed.
Lemma lem3850000 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term337 _44734 _44735 _44736 _44737) = (term338 _44734 _44737).
Proof. exact (MK_COMB (@lem3849999 _44734) (@lem3849998 _44735 _44736 _44737)). Qed.
Lemma lem3850001 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term336 _44734 _44735 _44736 _44737) = (term338 _44734 _44737).
Proof. exact (TRANS (@lem3849771 _44734 _44735 _44736 _44737) (@lem3850000 _44735 _44736 _44734 _44737)). Qed.
Lemma lem3850002 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3850003 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term367 _44734 _44735 _44736 _44737) = (term368 _44734 _44737).
Proof. exact (MK_COMB (@lem3850002) (@lem3850001 _44735 _44736 _44734 _44737)). Qed.
Lemma lem3850004 : term114 = term114.
Proof. exact (eq_refl term114). Qed.
Lemma lem3850005 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : ((term336 _44734 _44735 _44736 _44737) = term114) = ((term338 _44734 _44737) = term114).
Proof. exact (MK_COMB (@lem3850003 _44735 _44736 _44734 _44737) (@lem3850004)). Qed.
Lemma lem3850006 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term301 _44735 _44736 _44734 _44737) : (term338 _44734 _44737) = term114.
Proof. exact (EQ_MP (@lem3850005 _44735 _44736 _44734 _44737) (@lem3849770 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3850008 (y : real) : term327 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem3850009 (_44734 : int) (_44737 : int) : term369 _44734 _44737.
Proof. exact (@lem3850008 (term338 _44734 _44737)). Qed.
Lemma lem3850010 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term301 _44735 _44736 _44734 _44737) : term370 _44734 _44737.
Proof. exact (@lem3850009 _44734 _44737 (@lem3850006 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3850011 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term301 _44735 _44736 _44734 _44737) : term371 _44734 _44737.
Proof. exact (@lem3850010 _44735 _44736 _44734 _44737 h1 term128). Qed.
Lemma lem3850012 (_44734 : int) (_44737 : int) : (term371 _44734 _44737) = ((term372 _44734 _44737) = term114).
Proof. exact (eq_refl (term371 _44734 _44737)). Qed.
Lemma lem3850013 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term301 _44735 _44736 _44734 _44737) : (term372 _44734 _44737) = term114.
Proof. exact (EQ_MP (@lem3850012 _44734 _44737) (@lem3850011 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3850014 (_44734 : int) (_44737 : int) : (term372 _44734 _44737) = (term338 _44734 _44737).
Proof. exact (@lem1982733 (term338 _44734 _44737)). Qed.
Lemma lem3850015 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3850016 (_44734 : int) (_44737 : int) : (term373 _44734 _44737) = (term368 _44734 _44737).
Proof. exact (MK_COMB (@lem3850015) (@lem3850014 _44734 _44737)). Qed.
Lemma lem3850017 : term114 = term114.
Proof. exact (eq_refl term114). Qed.
Lemma lem3850018 (_44734 : int) (_44737 : int) : ((term372 _44734 _44737) = term114) = ((term338 _44734 _44737) = term114).
Proof. exact (MK_COMB (@lem3850016 _44734 _44737) (@lem3850017)). Qed.
Lemma lem3850019 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term301 _44735 _44736 _44734 _44737) : (term338 _44734 _44737) = term114.
Proof. exact (EQ_MP (@lem3850018 _44734 _44737) (@lem3850013 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3850020 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term301 _44735 _44736 _44734 _44737) : term374 _44734 _44737.
Proof. exact (conj (@lem3850019 _44735 _44736 _44734 _44737 h1) (@lem3849678 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3850022 (x : real) (y : real) : term375 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem3850023 (_44734 : int) (_44737 : int) : term376 _44734 _44737.
Proof. exact (@lem3850022 (term338 _44734 _44737) (term223 _44734 _44737)). Qed.
Lemma lem3850024 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term301 _44735 _44736 _44734 _44737) : term377 _44734 _44737.
Proof. exact (@lem3850023 _44734 _44737 (@lem3850020 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3850025 (_44734 : int) (_44737 : int) : (term378 _44734 _44737) = (term379 _44734 _44737).
Proof. exact (@lem1982753 (real_of_int _44734) (term190 _44734) (term190 _44737) (term380 _44737)). Qed.
Lemma lem3850026 (_44734 : int) : (term341 _44734) = (term342 _44734).
Proof. exact (@lem1982715 term163 (real_of_int _44734)). Qed.
Lemma lem3850028 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3850029 : term128 = term198.
Proof. exact (@lem3850028 term129). Qed.
Lemma lem3850031 (x : nat) : (term161 x) = (term162 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3850032 : term163 = term164.
Proof. exact (@lem3850031 term129). Qed.
Lemma lem3850033 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3850034 : term343 = term344.
Proof. exact (MK_COMB (@lem3850033) (@lem3850032)). Qed.
Lemma lem3850035 : term345 = term346.
Proof. exact (MK_COMB (@lem3850034) (@lem3850029)). Qed.
Lemma lem3850036 : term347.
Proof. exact (@lem1981473 term163 term128 term128 term128 term114 term128). Qed.
Lemma lem3850038 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3850039 : term303 = term309.
Proof. exact (@lem3850038 (NUMERAL 0) term129). Qed.
Lemma lem3850040 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3850041 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3850042 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3850041 h1) (fun h1 : term309 = True => @lem3850040)). Qed.
Lemma lem3850043 : term309 = True.
Proof. exact (EQ_MP (@lem3850042) (@lem3850040)). Qed.
Lemma lem3850044 : term303 = True.
Proof. exact (TRANS (@lem3850039) (@lem3850043)). Qed.
Lemma lem3850045 : True = term303.
Proof. exact (SYM (@lem3850044)). Qed.
Lemma lem3850046 : term303.
Proof. exact (EQ_MP (@lem3850045) (@lem0)). Qed.
Lemma lem3850047 : term348.
Proof. exact (@lem3850036 (@lem3850046)). Qed.
Lemma lem3850049 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3850050 : term303 = term309.
Proof. exact (@lem3850049 (NUMERAL 0) term129). Qed.
Lemma lem3850051 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3850052 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3850053 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3850052 h1) (fun h1 : term309 = True => @lem3850051)). Qed.
Lemma lem3850054 : term309 = True.
Proof. exact (EQ_MP (@lem3850053) (@lem3850051)). Qed.
Lemma lem3850055 : term303 = True.
Proof. exact (TRANS (@lem3850050) (@lem3850054)). Qed.
Lemma lem3850056 : True = term303.
Proof. exact (SYM (@lem3850055)). Qed.
Lemma lem3850057 : term303.
Proof. exact (EQ_MP (@lem3850056) (@lem0)). Qed.
Lemma lem3850058 : term349.
Proof. exact (@lem3850047 (@lem3850057)). Qed.
Lemma lem3850060 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3850061 : term303 = term309.
Proof. exact (@lem3850060 (NUMERAL 0) term129). Qed.
Lemma lem3850062 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3850063 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3850064 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3850063 h1) (fun h1 : term309 = True => @lem3850062)). Qed.
Lemma lem3850065 : term309 = True.
Proof. exact (EQ_MP (@lem3850064) (@lem3850062)). Qed.
Lemma lem3850066 : term303 = True.
Proof. exact (TRANS (@lem3850061) (@lem3850065)). Qed.
Lemma lem3850067 : True = term303.
Proof. exact (SYM (@lem3850066)). Qed.
Lemma lem3850068 : term303.
Proof. exact (EQ_MP (@lem3850067) (@lem0)). Qed.
Lemma lem3850069 : term350.
Proof. exact (@lem3850058 (@lem3850068)). Qed.
Lemma lem3850071 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3850072 : term172 = term173.
Proof. exact (@lem3850071 term129 term129). Qed.
Lemma lem3850073 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3850074 : term175 = term129.
Proof. exact (EQ_MP (@lem3850073) (@lem940073)). Qed.
Lemma lem3850075 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3850076 : term173 = term128.
Proof. exact (MK_COMB (@lem3850075) (@lem3850074)). Qed.
Lemma lem3850077 : term172 = term128.
Proof. exact (TRANS (@lem3850072) (@lem3850076)). Qed.
Lemma lem3850079 (m : nat) (n : nat) : (term202 m n) = (term203 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3850080 : term199 = term204.
Proof. exact (@lem3850079 term129 term129). Qed.
Lemma lem3850081 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3850082 : term175 = term129.
Proof. exact (EQ_MP (@lem3850081) (@lem940073)). Qed.
Lemma lem3850083 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3850084 : term173 = term128.
Proof. exact (MK_COMB (@lem3850083) (@lem3850082)). Qed.
Lemma lem3850085 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3850086 : term204 = term163.
Proof. exact (MK_COMB (@lem3850085) (@lem3850084)). Qed.
Lemma lem3850087 : term199 = term163.
Proof. exact (TRANS (@lem3850080) (@lem3850086)). Qed.
Lemma lem3850088 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3850089 : term351 = term343.
Proof. exact (MK_COMB (@lem3850088) (@lem3850087)). Qed.
Lemma lem3850090 : term352 = term345.
Proof. exact (MK_COMB (@lem3850089) (@lem3850077)). Qed.
Lemma lem3850092 (m : nat) : (term353 m) = term114.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3850093 : term345 = term114.
Proof. exact (@lem3850092 term129). Qed.
Lemma lem3850094 : term352 = term114.
Proof. exact (TRANS (@lem3850090) (@lem3850093)). Qed.
Lemma lem3850095 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3850096 : term354 = term355.
Proof. exact (MK_COMB (@lem3850095) (@lem3850094)). Qed.
Lemma lem3850097 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem3850098 : term356 = term314.
Proof. exact (MK_COMB (@lem3850096) (@lem3850097)). Qed.
Lemma lem3850100 (x : nat) : (term313 x) = term114.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3850101 : term314 = term114.
Proof. exact (@lem3850100 term129). Qed.
Lemma lem3850102 : term356 = term114.
Proof. exact (TRANS (@lem3850098) (@lem3850101)). Qed.
Lemma lem3850104 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3850105 : term172 = term173.
Proof. exact (@lem3850104 term129 term129). Qed.
Lemma lem3850106 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3850107 : term175 = term129.
Proof. exact (EQ_MP (@lem3850106) (@lem940073)). Qed.
Lemma lem3850108 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3850109 : term173 = term128.
Proof. exact (MK_COMB (@lem3850108) (@lem3850107)). Qed.
Lemma lem3850110 : term172 = term128.
Proof. exact (TRANS (@lem3850105) (@lem3850109)). Qed.
Lemma lem3850111 : term355 = term355.
Proof. exact (eq_refl term355). Qed.
Lemma lem3850112 : term357 = term314.
Proof. exact (MK_COMB (@lem3850111) (@lem3850110)). Qed.
Lemma lem3850114 (x : nat) : (term313 x) = term114.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3850115 : term314 = term114.
Proof. exact (@lem3850114 term129). Qed.
Lemma lem3850116 : term357 = term114.
Proof. exact (TRANS (@lem3850112) (@lem3850115)). Qed.
Lemma lem3850117 : term114 = term357.
Proof. exact (SYM (@lem3850116)). Qed.
Lemma lem3850118 : term356 = term357.
Proof. exact (TRANS (@lem3850102) (@lem3850117)). Qed.
Lemma lem3850119 : term346 = term160.
Proof. exact (@lem3850069 (@lem3850118)). Qed.
Lemma lem3850120 : term345 = term160.
Proof. exact (TRANS (@lem3850035) (@lem3850119)). Qed.
Lemma lem3850122 (x : real) : (term179 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3850123 : term160 = term114.
Proof. exact (@lem3850122 term114). Qed.
Lemma lem3850124 : term345 = term114.
Proof. exact (TRANS (@lem3850120) (@lem3850123)). Qed.
Lemma lem3850125 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3850126 : term358 = term355.
Proof. exact (MK_COMB (@lem3850125) (@lem3850124)). Qed.
Lemma lem3850127 (_44734 : int) : (real_of_int _44734) = (real_of_int _44734).
Proof. exact (eq_refl (real_of_int _44734)). Qed.
Lemma lem3850128 (_44734 : int) : (term342 _44734) = (term359 _44734).
Proof. exact (MK_COMB (@lem3850126) (@lem3850127 _44734)). Qed.
Lemma lem3850129 (_44734 : int) : (term341 _44734) = (term359 _44734).
Proof. exact (TRANS (@lem3850026 _44734) (@lem3850128 _44734)). Qed.
Lemma lem3850130 (_44734 : int) : (term359 _44734) = term114.
Proof. exact (@lem1982719 (real_of_int _44734)). Qed.
Lemma lem3850131 (_44734 : int) : (term341 _44734) = term114.
Proof. exact (TRANS (@lem3850129 _44734) (@lem3850130 _44734)). Qed.
Lemma lem3850132 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3850133 (_44734 : int) : (term360 _44734) = term361.
Proof. exact (MK_COMB (@lem3850132) (@lem3850131 _44734)). Qed.
Lemma lem3850134 (_44737 : int) : (term381 _44737) = (term382 _44737).
Proof. exact (@lem1982763 (term190 _44737) (real_of_int _44737) term163). Qed.
Lemma lem3850135 (_44737 : int) : (term364 _44737) = (term342 _44737).
Proof. exact (@lem1982713 term163 (real_of_int _44737)). Qed.
Lemma lem3850137 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3850138 : term128 = term198.
Proof. exact (@lem3850137 term129). Qed.
Lemma lem3850140 (x : nat) : (term161 x) = (term162 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3850141 : term163 = term164.
Proof. exact (@lem3850140 term129). Qed.
Lemma lem3850142 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3850143 : term343 = term344.
Proof. exact (MK_COMB (@lem3850142) (@lem3850141)). Qed.
Lemma lem3850144 : term345 = term346.
Proof. exact (MK_COMB (@lem3850143) (@lem3850138)). Qed.
Lemma lem3850145 : term347.
Proof. exact (@lem1981473 term163 term128 term128 term128 term114 term128). Qed.
Lemma lem3850147 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3850148 : term303 = term309.
Proof. exact (@lem3850147 (NUMERAL 0) term129). Qed.
Lemma lem3850149 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3850150 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3850151 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3850150 h1) (fun h1 : term309 = True => @lem3850149)). Qed.
Lemma lem3850152 : term309 = True.
Proof. exact (EQ_MP (@lem3850151) (@lem3850149)). Qed.
Lemma lem3850153 : term303 = True.
Proof. exact (TRANS (@lem3850148) (@lem3850152)). Qed.
Lemma lem3850154 : True = term303.
Proof. exact (SYM (@lem3850153)). Qed.
Lemma lem3850155 : term303.
Proof. exact (EQ_MP (@lem3850154) (@lem0)). Qed.
Lemma lem3850156 : term348.
Proof. exact (@lem3850145 (@lem3850155)). Qed.
Lemma lem3850158 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3850159 : term303 = term309.
Proof. exact (@lem3850158 (NUMERAL 0) term129). Qed.
Lemma lem3850160 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3850161 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3850162 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3850161 h1) (fun h1 : term309 = True => @lem3850160)). Qed.
Lemma lem3850163 : term309 = True.
Proof. exact (EQ_MP (@lem3850162) (@lem3850160)). Qed.
Lemma lem3850164 : term303 = True.
Proof. exact (TRANS (@lem3850159) (@lem3850163)). Qed.
Lemma lem3850165 : True = term303.
Proof. exact (SYM (@lem3850164)). Qed.
Lemma lem3850166 : term303.
Proof. exact (EQ_MP (@lem3850165) (@lem0)). Qed.
Lemma lem3850167 : term349.
Proof. exact (@lem3850156 (@lem3850166)). Qed.
Lemma lem3850169 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3850170 : term303 = term309.
Proof. exact (@lem3850169 (NUMERAL 0) term129). Qed.
Lemma lem3850171 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3850172 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3850173 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3850172 h1) (fun h1 : term309 = True => @lem3850171)). Qed.
Lemma lem3850174 : term309 = True.
Proof. exact (EQ_MP (@lem3850173) (@lem3850171)). Qed.
Lemma lem3850175 : term303 = True.
Proof. exact (TRANS (@lem3850170) (@lem3850174)). Qed.
Lemma lem3850176 : True = term303.
Proof. exact (SYM (@lem3850175)). Qed.
Lemma lem3850177 : term303.
Proof. exact (EQ_MP (@lem3850176) (@lem0)). Qed.
Lemma lem3850178 : term350.
Proof. exact (@lem3850167 (@lem3850177)). Qed.
Lemma lem3850180 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3850181 : term172 = term173.
Proof. exact (@lem3850180 term129 term129). Qed.
Lemma lem3850182 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3850183 : term175 = term129.
Proof. exact (EQ_MP (@lem3850182) (@lem940073)). Qed.
Lemma lem3850184 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3850185 : term173 = term128.
Proof. exact (MK_COMB (@lem3850184) (@lem3850183)). Qed.
Lemma lem3850186 : term172 = term128.
Proof. exact (TRANS (@lem3850181) (@lem3850185)). Qed.
Lemma lem3850188 (m : nat) (n : nat) : (term202 m n) = (term203 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3850189 : term199 = term204.
Proof. exact (@lem3850188 term129 term129). Qed.
Lemma lem3850190 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3850191 : term175 = term129.
Proof. exact (EQ_MP (@lem3850190) (@lem940073)). Qed.
Lemma lem3850192 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3850193 : term173 = term128.
Proof. exact (MK_COMB (@lem3850192) (@lem3850191)). Qed.
Lemma lem3850194 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3850195 : term204 = term163.
Proof. exact (MK_COMB (@lem3850194) (@lem3850193)). Qed.
Lemma lem3850196 : term199 = term163.
Proof. exact (TRANS (@lem3850189) (@lem3850195)). Qed.
Lemma lem3850197 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3850198 : term351 = term343.
Proof. exact (MK_COMB (@lem3850197) (@lem3850196)). Qed.
Lemma lem3850199 : term352 = term345.
Proof. exact (MK_COMB (@lem3850198) (@lem3850186)). Qed.
Lemma lem3850201 (m : nat) : (term353 m) = term114.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3850202 : term345 = term114.
Proof. exact (@lem3850201 term129). Qed.
Lemma lem3850203 : term352 = term114.
Proof. exact (TRANS (@lem3850199) (@lem3850202)). Qed.
Lemma lem3850204 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3850205 : term354 = term355.
Proof. exact (MK_COMB (@lem3850204) (@lem3850203)). Qed.
Lemma lem3850206 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem3850207 : term356 = term314.
Proof. exact (MK_COMB (@lem3850205) (@lem3850206)). Qed.
Lemma lem3850209 (x : nat) : (term313 x) = term114.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3850210 : term314 = term114.
Proof. exact (@lem3850209 term129). Qed.
Lemma lem3850211 : term356 = term114.
Proof. exact (TRANS (@lem3850207) (@lem3850210)). Qed.
Lemma lem3850213 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3850214 : term172 = term173.
Proof. exact (@lem3850213 term129 term129). Qed.
Lemma lem3850215 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3850216 : term175 = term129.
Proof. exact (EQ_MP (@lem3850215) (@lem940073)). Qed.
Lemma lem3850217 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3850218 : term173 = term128.
Proof. exact (MK_COMB (@lem3850217) (@lem3850216)). Qed.
Lemma lem3850219 : term172 = term128.
Proof. exact (TRANS (@lem3850214) (@lem3850218)). Qed.
Lemma lem3850220 : term355 = term355.
Proof. exact (eq_refl term355). Qed.
Lemma lem3850221 : term357 = term314.
Proof. exact (MK_COMB (@lem3850220) (@lem3850219)). Qed.
Lemma lem3850223 (x : nat) : (term313 x) = term114.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3850224 : term314 = term114.
Proof. exact (@lem3850223 term129). Qed.
Lemma lem3850225 : term357 = term114.
Proof. exact (TRANS (@lem3850221) (@lem3850224)). Qed.
Lemma lem3850226 : term114 = term357.
Proof. exact (SYM (@lem3850225)). Qed.
Lemma lem3850227 : term356 = term357.
Proof. exact (TRANS (@lem3850211) (@lem3850226)). Qed.
Lemma lem3850228 : term346 = term160.
Proof. exact (@lem3850178 (@lem3850227)). Qed.
Lemma lem3850229 : term345 = term160.
Proof. exact (TRANS (@lem3850144) (@lem3850228)). Qed.
Lemma lem3850231 (x : real) : (term179 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3850232 : term160 = term114.
Proof. exact (@lem3850231 term114). Qed.
Lemma lem3850233 : term345 = term114.
Proof. exact (TRANS (@lem3850229) (@lem3850232)). Qed.
Lemma lem3850234 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3850235 : term358 = term355.
Proof. exact (MK_COMB (@lem3850234) (@lem3850233)). Qed.
Lemma lem3850236 (_44737 : int) : (real_of_int _44737) = (real_of_int _44737).
Proof. exact (eq_refl (real_of_int _44737)). Qed.
Lemma lem3850237 (_44737 : int) : (term342 _44737) = (term359 _44737).
Proof. exact (MK_COMB (@lem3850235) (@lem3850236 _44737)). Qed.
Lemma lem3850238 (_44737 : int) : (term364 _44737) = (term359 _44737).
Proof. exact (TRANS (@lem3850135 _44737) (@lem3850237 _44737)). Qed.
Lemma lem3850239 (_44737 : int) : (term359 _44737) = term114.
Proof. exact (@lem1982719 (real_of_int _44737)). Qed.
Lemma lem3850240 (_44737 : int) : (term364 _44737) = term114.
Proof. exact (TRANS (@lem3850238 _44737) (@lem3850239 _44737)). Qed.
Lemma lem3850241 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3850242 (_44737 : int) : (term365 _44737) = term361.
Proof. exact (MK_COMB (@lem3850241) (@lem3850240 _44737)). Qed.
Lemma lem3850243 : term163 = term163.
Proof. exact (eq_refl term163). Qed.
Lemma lem3850244 (_44737 : int) : (term382 _44737) = term383.
Proof. exact (MK_COMB (@lem3850242 _44737) (@lem3850243)). Qed.
Lemma lem3850245 (_44737 : int) : (term381 _44737) = term383.
Proof. exact (TRANS (@lem3850134 _44737) (@lem3850244 _44737)). Qed.
Lemma lem3850246 : term383 = term163.
Proof. exact (@lem1982721 term163). Qed.
Lemma lem3850247 (_44737 : int) : (term381 _44737) = term163.
Proof. exact (TRANS (@lem3850245 _44737) (@lem3850246)). Qed.
Lemma lem3850248 (_44734 : int) (_44737 : int) : (term379 _44734 _44737) = term383.
Proof. exact (MK_COMB (@lem3850133 _44734) (@lem3850247 _44737)). Qed.
Lemma lem3850249 (_44734 : int) (_44737 : int) : (term378 _44734 _44737) = term383.
Proof. exact (TRANS (@lem3850025 _44734 _44737) (@lem3850248 _44734 _44737)). Qed.
Lemma lem3850250 : term383 = term163.
Proof. exact (@lem1982721 term163). Qed.
Lemma lem3850251 (_44734 : int) (_44737 : int) : (term378 _44734 _44737) = term163.
Proof. exact (TRANS (@lem3850249 _44734 _44737) (@lem3850250)). Qed.
Lemma lem3850252 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3850253 (_44734 : int) (_44737 : int) : (term384 _44734 _44737) = term385.
Proof. exact (MK_COMB (@lem3850252) (@lem3850251 _44734 _44737)). Qed.
Lemma lem3850254 : term114 = term114.
Proof. exact (eq_refl term114). Qed.
Lemma lem3850255 (_44734 : int) (_44737 : int) : (term377 _44734 _44737) = term386.
Proof. exact (MK_COMB (@lem3850253 _44734 _44737) (@lem3850254)). Qed.
Lemma lem3850256 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term301 _44735 _44736 _44734 _44737) : term386.
Proof. exact (EQ_MP (@lem3850255 _44734 _44737) (@lem3850024 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3850258 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3850259 : term386 = term387.
Proof. exact (@lem3850258 term114 term163). Qed.
Lemma lem3850261 (x : nat) : (term161 x) = (term162 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3850262 : term163 = term164.
Proof. exact (@lem3850261 term129). Qed.
Lemma lem3850264 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3850265 : term114 = term160.
Proof. exact (@lem3850264 (NUMERAL 0)). Qed.
Lemma lem3850266 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3850267 : term116 = term388.
Proof. exact (MK_COMB (@lem3850266) (@lem3850265)). Qed.
Lemma lem3850268 : term387 = term389.
Proof. exact (MK_COMB (@lem3850267) (@lem3850262)). Qed.
Lemma lem3850269 : term390.
Proof. exact (@lem1980026 term114 term128 term163 term128). Qed.
Lemma lem3850271 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3850272 : term303 = term309.
Proof. exact (@lem3850271 (NUMERAL 0) term129). Qed.
Lemma lem3850273 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3850274 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3850275 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3850274 h1) (fun h1 : term309 = True => @lem3850273)). Qed.
Lemma lem3850276 : term309 = True.
Proof. exact (EQ_MP (@lem3850275) (@lem3850273)). Qed.
Lemma lem3850277 : term303 = True.
Proof. exact (TRANS (@lem3850272) (@lem3850276)). Qed.
Lemma lem3850278 : True = term303.
Proof. exact (SYM (@lem3850277)). Qed.
Lemma lem3850279 : term303.
Proof. exact (EQ_MP (@lem3850278) (@lem0)). Qed.
Lemma lem3850280 : term391.
Proof. exact (@lem3850269 (@lem3850279)). Qed.
Lemma lem3850282 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3850283 : term303 = term309.
Proof. exact (@lem3850282 (NUMERAL 0) term129). Qed.
Lemma lem3850284 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3850285 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3850286 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3850285 h1) (fun h1 : term309 = True => @lem3850284)). Qed.
Lemma lem3850287 : term309 = True.
Proof. exact (EQ_MP (@lem3850286) (@lem3850284)). Qed.
Lemma lem3850288 : term303 = True.
Proof. exact (TRANS (@lem3850283) (@lem3850287)). Qed.
Lemma lem3850289 : True = term303.
Proof. exact (SYM (@lem3850288)). Qed.
Lemma lem3850290 : term303.
Proof. exact (EQ_MP (@lem3850289) (@lem0)). Qed.
Lemma lem3850291 : term389 = term392.
Proof. exact (@lem3850280 (@lem3850290)). Qed.
Lemma lem3850293 (m : nat) (n : nat) : (term202 m n) = (term203 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3850294 : term199 = term204.
Proof. exact (@lem3850293 term129 term129). Qed.
Lemma lem3850295 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3850296 : term175 = term129.
Proof. exact (EQ_MP (@lem3850295) (@lem940073)). Qed.
Lemma lem3850297 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3850298 : term173 = term128.
Proof. exact (MK_COMB (@lem3850297) (@lem3850296)). Qed.
Lemma lem3850299 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3850300 : term204 = term163.
Proof. exact (MK_COMB (@lem3850299) (@lem3850298)). Qed.
Lemma lem3850301 : term199 = term163.
Proof. exact (TRANS (@lem3850294) (@lem3850300)). Qed.
Lemma lem3850303 (x : nat) : (term313 x) = term114.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3850304 : term314 = term114.
Proof. exact (@lem3850303 term129). Qed.
Lemma lem3850305 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3850306 : term393 = term116.
Proof. exact (MK_COMB (@lem3850305) (@lem3850304)). Qed.
Lemma lem3850307 : term392 = term387.
Proof. exact (MK_COMB (@lem3850306) (@lem3850301)). Qed.
Lemma lem3850309 (m : nat) (n : nat) : (term394 m n) = (term395 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3850310 : term387 = term396.
Proof. exact (@lem3850309 (NUMERAL 0) term129). Qed.
Lemma lem3850311 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3850312 (h1 : term310 = (BIT1 0)) : (term129 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3850313 : (term310 = (BIT1 0)) = ((term129 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3850312 h1) (fun h1 : (term129 = (NUMERAL 0)) = False => @lem3850311)). Qed.
Lemma lem3850314 : (term129 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3850313) (@lem3850311)). Qed.
Lemma lem3850315 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3850316 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3850317 : term397 = (and True).
Proof. exact (MK_COMB (@lem3850316) (@lem3850315)). Qed.
Lemma lem3850318 : term396 = (True /\ False).
Proof. exact (MK_COMB (@lem3850317) (@lem3850314)). Qed.
Lemma lem3850320 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3850321 : term396 = False.
Proof. exact (TRANS (@lem3850318) (@lem3850320)). Qed.
Lemma lem3850322 : term387 = False.
Proof. exact (TRANS (@lem3850310) (@lem3850321)). Qed.
Lemma lem3850323 : term392 = False.
Proof. exact (TRANS (@lem3850307) (@lem3850322)). Qed.
Lemma lem3850324 : term389 = False.
Proof. exact (TRANS (@lem3850291) (@lem3850323)). Qed.
Lemma lem3850325 : term387 = False.
Proof. exact (TRANS (@lem3850268) (@lem3850324)). Qed.
Lemma lem3850326 : term386 = False.
Proof. exact (TRANS (@lem3850259) (@lem3850325)). Qed.
Lemma lem3850327 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term301 _44735 _44736 _44734 _44737) : False.
Proof. exact (EQ_MP (@lem3850326) (@lem3850256 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3850328 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term398 _44735 _44736 _44734 _44737) : term398 _44735 _44736 _44734 _44737.
Proof. exact (h1). Qed.
Lemma lem3850329 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term398 _44735 _44736 _44734 _44737) : term297 _44735 _44736 _44734 _44737.
Proof. exact (proj2 (@lem3850328 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3850330 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term398 _44735 _44736 _44734 _44737) : term183 _44734.
Proof. exact (proj1 (@lem3850328 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3850331 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term398 _44735 _44736 _44734 _44737) : term284 _44735 _44736 _44734 _44737.
Proof. exact (proj2 (@lem3850329 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3850333 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term398 _44735 _44736 _44734 _44737) : term271 _44735 _44736 _44734 _44737.
Proof. exact (proj2 (@lem3850331 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3850335 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term398 _44735 _44736 _44734 _44737) : term258 _44735 _44736 _44734 _44737.
Proof. exact (proj2 (@lem3850333 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3850337 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term398 _44735 _44736 _44734 _44737) : term240 _44735 _44736 _44734 _44737.
Proof. exact (proj2 (@lem3850335 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3850338 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term398 _44735 _44736 _44734 _44737) : term215 _44735 _44736 _44737.
Proof. exact (proj1 (@lem3850335 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3850339 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term398 _44735 _44736 _44734 _44737) : (real_of_int _44737) = term114.
Proof. exact (proj2 (@lem3850338 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3850341 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term398 _44735 _44736 _44734 _44737) : term225 _44734 _44737.
Proof. exact (proj2 (@lem3850337 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3850344 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3850345 : term302 = term303.
Proof. exact (@lem3850344 term114 term128). Qed.
Lemma lem3850347 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3850348 : term128 = term198.
Proof. exact (@lem3850347 term129). Qed.
Lemma lem3850350 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3850351 : term114 = term160.
Proof. exact (@lem3850350 (NUMERAL 0)). Qed.
Lemma lem3850352 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3850353 : term304 = term305.
Proof. exact (MK_COMB (@lem3850352) (@lem3850351)). Qed.
Lemma lem3850354 : term303 = term306.
Proof. exact (MK_COMB (@lem3850353) (@lem3850348)). Qed.
Lemma lem3850355 : term307.
Proof. exact (@lem1980255 term114 term128 term128 term128). Qed.
Lemma lem3850357 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3850358 : term303 = term309.
Proof. exact (@lem3850357 (NUMERAL 0) term129). Qed.
Lemma lem3850359 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3850360 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3850361 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3850360 h1) (fun h1 : term309 = True => @lem3850359)). Qed.
Lemma lem3850362 : term309 = True.
Proof. exact (EQ_MP (@lem3850361) (@lem3850359)). Qed.
Lemma lem3850363 : term303 = True.
Proof. exact (TRANS (@lem3850358) (@lem3850362)). Qed.
Lemma lem3850364 : True = term303.
Proof. exact (SYM (@lem3850363)). Qed.
Lemma lem3850365 : term303.
Proof. exact (EQ_MP (@lem3850364) (@lem0)). Qed.
Lemma lem3850366 : term311.
Proof. exact (@lem3850355 (@lem3850365)). Qed.
Lemma lem3850368 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3850369 : term303 = term309.
Proof. exact (@lem3850368 (NUMERAL 0) term129). Qed.
Lemma lem3850370 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3850371 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3850372 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3850371 h1) (fun h1 : term309 = True => @lem3850370)). Qed.
Lemma lem3850373 : term309 = True.
Proof. exact (EQ_MP (@lem3850372) (@lem3850370)). Qed.
Lemma lem3850374 : term303 = True.
Proof. exact (TRANS (@lem3850369) (@lem3850373)). Qed.
Lemma lem3850375 : True = term303.
Proof. exact (SYM (@lem3850374)). Qed.
Lemma lem3850376 : term303.
Proof. exact (EQ_MP (@lem3850375) (@lem0)). Qed.
Lemma lem3850377 : term306 = term312.
Proof. exact (@lem3850366 (@lem3850376)). Qed.
Lemma lem3850379 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3850380 : term172 = term173.
Proof. exact (@lem3850379 term129 term129). Qed.
Lemma lem3850381 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3850382 : term175 = term129.
Proof. exact (EQ_MP (@lem3850381) (@lem940073)). Qed.
Lemma lem3850383 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3850384 : term173 = term128.
Proof. exact (MK_COMB (@lem3850383) (@lem3850382)). Qed.
Lemma lem3850385 : term172 = term128.
Proof. exact (TRANS (@lem3850380) (@lem3850384)). Qed.
Lemma lem3850387 (x : nat) : (term313 x) = term114.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3850388 : term314 = term114.
Proof. exact (@lem3850387 term129). Qed.
Lemma lem3850389 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3850390 : term315 = term304.
Proof. exact (MK_COMB (@lem3850389) (@lem3850388)). Qed.
Lemma lem3850391 : term312 = term303.
Proof. exact (MK_COMB (@lem3850390) (@lem3850385)). Qed.
Lemma lem3850393 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3850394 : term303 = term309.
Proof. exact (@lem3850393 (NUMERAL 0) term129). Qed.
Lemma lem3850395 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3850396 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3850397 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3850396 h1) (fun h1 : term309 = True => @lem3850395)). Qed.
Lemma lem3850398 : term309 = True.
Proof. exact (EQ_MP (@lem3850397) (@lem3850395)). Qed.
Lemma lem3850399 : term303 = True.
Proof. exact (TRANS (@lem3850394) (@lem3850398)). Qed.
Lemma lem3850400 : term312 = True.
Proof. exact (TRANS (@lem3850391) (@lem3850399)). Qed.
Lemma lem3850401 : term306 = True.
Proof. exact (TRANS (@lem3850377) (@lem3850400)). Qed.
Lemma lem3850402 : term303 = True.
Proof. exact (TRANS (@lem3850354) (@lem3850401)). Qed.
Lemma lem3850403 : term302 = True.
Proof. exact (TRANS (@lem3850345) (@lem3850402)). Qed.
Lemma lem3850404 : True = term302.
Proof. exact (SYM (@lem3850403)). Qed.
Lemma lem3850405 : term302.
Proof. exact (EQ_MP (@lem3850404) (@lem0)). Qed.
Lemma lem3850406 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term398 _44735 _44736 _44734 _44737) : term399 _44734.
Proof. exact (conj (@lem3850405) (@lem3850330 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3850408 (x : real) (y : real) : term317 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3850409 (_44734 : int) : term400 _44734.
Proof. exact (@lem3850408 term128 (real_of_int _44734)). Qed.
Lemma lem3850410 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term398 _44735 _44736 _44734 _44737) : term401 _44734.
Proof. exact (@lem3850409 _44734 (@lem3850406 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3850411 (_44734 : int) : (term402 _44734) = (real_of_int _44734).
Proof. exact (@lem1982733 (real_of_int _44734)). Qed.
Lemma lem3850412 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3850413 (_44734 : int) : (term403 _44734) = (term182 _44734).
Proof. exact (MK_COMB (@lem3850412) (@lem3850411 _44734)). Qed.
Lemma lem3850414 : term114 = term114.
Proof. exact (eq_refl term114). Qed.
Lemma lem3850415 (_44734 : int) : (term401 _44734) = (term183 _44734).
Proof. exact (MK_COMB (@lem3850413 _44734) (@lem3850414)). Qed.
Lemma lem3850416 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term398 _44735 _44736 _44734 _44737) : term183 _44734.
Proof. exact (EQ_MP (@lem3850415 _44734) (@lem3850410 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3850418 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3850419 : term302 = term303.
Proof. exact (@lem3850418 term114 term128). Qed.
Lemma lem3850421 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3850422 : term128 = term198.
Proof. exact (@lem3850421 term129). Qed.
Lemma lem3850424 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3850425 : term114 = term160.
Proof. exact (@lem3850424 (NUMERAL 0)). Qed.
Lemma lem3850426 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3850427 : term304 = term305.
Proof. exact (MK_COMB (@lem3850426) (@lem3850425)). Qed.
Lemma lem3850428 : term303 = term306.
Proof. exact (MK_COMB (@lem3850427) (@lem3850422)). Qed.
Lemma lem3850429 : term307.
Proof. exact (@lem1980255 term114 term128 term128 term128). Qed.
Lemma lem3850431 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3850432 : term303 = term309.
Proof. exact (@lem3850431 (NUMERAL 0) term129). Qed.
Lemma lem3850433 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3850434 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3850435 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3850434 h1) (fun h1 : term309 = True => @lem3850433)). Qed.
Lemma lem3850436 : term309 = True.
Proof. exact (EQ_MP (@lem3850435) (@lem3850433)). Qed.
Lemma lem3850437 : term303 = True.
Proof. exact (TRANS (@lem3850432) (@lem3850436)). Qed.
Lemma lem3850438 : True = term303.
Proof. exact (SYM (@lem3850437)). Qed.
Lemma lem3850439 : term303.
Proof. exact (EQ_MP (@lem3850438) (@lem0)). Qed.
Lemma lem3850440 : term311.
Proof. exact (@lem3850429 (@lem3850439)). Qed.
Lemma lem3850442 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3850443 : term303 = term309.
Proof. exact (@lem3850442 (NUMERAL 0) term129). Qed.
Lemma lem3850444 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3850445 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3850446 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3850445 h1) (fun h1 : term309 = True => @lem3850444)). Qed.
Lemma lem3850447 : term309 = True.
Proof. exact (EQ_MP (@lem3850446) (@lem3850444)). Qed.
Lemma lem3850448 : term303 = True.
Proof. exact (TRANS (@lem3850443) (@lem3850447)). Qed.
Lemma lem3850449 : True = term303.
Proof. exact (SYM (@lem3850448)). Qed.
Lemma lem3850450 : term303.
Proof. exact (EQ_MP (@lem3850449) (@lem0)). Qed.
Lemma lem3850451 : term306 = term312.
Proof. exact (@lem3850440 (@lem3850450)). Qed.
Lemma lem3850453 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3850454 : term172 = term173.
Proof. exact (@lem3850453 term129 term129). Qed.
Lemma lem3850455 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3850456 : term175 = term129.
Proof. exact (EQ_MP (@lem3850455) (@lem940073)). Qed.
Lemma lem3850457 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3850458 : term173 = term128.
Proof. exact (MK_COMB (@lem3850457) (@lem3850456)). Qed.
Lemma lem3850459 : term172 = term128.
Proof. exact (TRANS (@lem3850454) (@lem3850458)). Qed.
Lemma lem3850461 (x : nat) : (term313 x) = term114.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3850462 : term314 = term114.
Proof. exact (@lem3850461 term129). Qed.
Lemma lem3850463 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3850464 : term315 = term304.
Proof. exact (MK_COMB (@lem3850463) (@lem3850462)). Qed.
Lemma lem3850465 : term312 = term303.
Proof. exact (MK_COMB (@lem3850464) (@lem3850459)). Qed.
Lemma lem3850467 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3850468 : term303 = term309.
Proof. exact (@lem3850467 (NUMERAL 0) term129). Qed.
Lemma lem3850469 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3850470 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3850471 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3850470 h1) (fun h1 : term309 = True => @lem3850469)). Qed.
Lemma lem3850472 : term309 = True.
Proof. exact (EQ_MP (@lem3850471) (@lem3850469)). Qed.
Lemma lem3850473 : term303 = True.
Proof. exact (TRANS (@lem3850468) (@lem3850472)). Qed.
Lemma lem3850474 : term312 = True.
Proof. exact (TRANS (@lem3850465) (@lem3850473)). Qed.
Lemma lem3850475 : term306 = True.
Proof. exact (TRANS (@lem3850451) (@lem3850474)). Qed.
Lemma lem3850476 : term303 = True.
Proof. exact (TRANS (@lem3850428) (@lem3850475)). Qed.
Lemma lem3850477 : term302 = True.
Proof. exact (TRANS (@lem3850419) (@lem3850476)). Qed.
Lemma lem3850478 : True = term302.
Proof. exact (SYM (@lem3850477)). Qed.
Lemma lem3850479 : term302.
Proof. exact (EQ_MP (@lem3850478) (@lem0)). Qed.
Lemma lem3850480 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term398 _44735 _44736 _44734 _44737) : term316 _44734 _44737.
Proof. exact (conj (@lem3850479) (@lem3850341 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3850482 (x : real) (y : real) : term317 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3850483 (_44734 : int) (_44737 : int) : term318 _44734 _44737.
Proof. exact (@lem3850482 term128 (term223 _44734 _44737)). Qed.
Lemma lem3850484 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term398 _44735 _44736 _44734 _44737) : term319 _44734 _44737.
Proof. exact (@lem3850483 _44734 _44737 (@lem3850480 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3850485 (_44734 : int) (_44737 : int) : (term320 _44734 _44737) = (term223 _44734 _44737).
Proof. exact (@lem1982733 (term223 _44734 _44737)). Qed.
Lemma lem3850486 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3850487 (_44734 : int) (_44737 : int) : (term321 _44734 _44737) = (term224 _44734 _44737).
Proof. exact (MK_COMB (@lem3850486) (@lem3850485 _44734 _44737)). Qed.
Lemma lem3850488 : term114 = term114.
Proof. exact (eq_refl term114). Qed.
Lemma lem3850489 (_44734 : int) (_44737 : int) : (term319 _44734 _44737) = (term225 _44734 _44737).
Proof. exact (MK_COMB (@lem3850487 _44734 _44737) (@lem3850488)). Qed.
Lemma lem3850490 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term398 _44735 _44736 _44734 _44737) : term225 _44734 _44737.
Proof. exact (EQ_MP (@lem3850489 _44734 _44737) (@lem3850484 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3850492 (y : real) : term327 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem3850493 (_44737 : int) : term404 _44737.
Proof. exact (@lem3850492 (real_of_int _44737)). Qed.
Lemma lem3850494 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term398 _44735 _44736 _44734 _44737) : term405 _44737.
Proof. exact (@lem3850493 _44737 (@lem3850339 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3850495 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term398 _44735 _44736 _44734 _44737) : term406 _44737.
Proof. exact (@lem3850494 _44735 _44736 _44734 _44737 h1 term163). Qed.
Lemma lem3850496 (_44737 : int) : (term406 _44737) = ((term190 _44737) = term114).
Proof. exact (eq_refl (term406 _44737)). Qed.
Lemma lem3850503 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term398 _44735 _44736 _44734 _44737) : (term190 _44737) = term114.
Proof. exact (EQ_MP (@lem3850496 _44737) (@lem3850495 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3850504 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term398 _44735 _44736 _44734 _44737) : term407 _44734 _44737.
Proof. exact (conj (@lem3850503 _44735 _44736 _44734 _44737 h1) (@lem3850490 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3850506 (x : real) (y : real) : term375 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem3850507 (_44734 : int) (_44737 : int) : term408 _44734 _44737.
Proof. exact (@lem3850506 (term190 _44737) (term223 _44734 _44737)). Qed.
Lemma lem3850508 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term398 _44735 _44736 _44734 _44737) : term409 _44734 _44737.
Proof. exact (@lem3850507 _44734 _44737 (@lem3850504 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3850509 (_44734 : int) (_44737 : int) : (term410 _44734 _44737) = (term411 _44734 _44737).
Proof. exact (@lem1982757 (term190 _44734) (term190 _44737) (term380 _44737)). Qed.
Lemma lem3850510 (_44737 : int) : (term381 _44737) = (term382 _44737).
Proof. exact (@lem1982763 (term190 _44737) (real_of_int _44737) term163). Qed.
Lemma lem3850511 (_44737 : int) : (term364 _44737) = (term342 _44737).
Proof. exact (@lem1982713 term163 (real_of_int _44737)). Qed.
Lemma lem3850513 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3850514 : term128 = term198.
Proof. exact (@lem3850513 term129). Qed.
Lemma lem3850516 (x : nat) : (term161 x) = (term162 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3850517 : term163 = term164.
Proof. exact (@lem3850516 term129). Qed.
Lemma lem3850518 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3850519 : term343 = term344.
Proof. exact (MK_COMB (@lem3850518) (@lem3850517)). Qed.
Lemma lem3850520 : term345 = term346.
Proof. exact (MK_COMB (@lem3850519) (@lem3850514)). Qed.
Lemma lem3850521 : term347.
Proof. exact (@lem1981473 term163 term128 term128 term128 term114 term128). Qed.
Lemma lem3850523 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3850524 : term303 = term309.
Proof. exact (@lem3850523 (NUMERAL 0) term129). Qed.
Lemma lem3850525 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3850526 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3850527 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3850526 h1) (fun h1 : term309 = True => @lem3850525)). Qed.
Lemma lem3850528 : term309 = True.
Proof. exact (EQ_MP (@lem3850527) (@lem3850525)). Qed.
Lemma lem3850529 : term303 = True.
Proof. exact (TRANS (@lem3850524) (@lem3850528)). Qed.
Lemma lem3850530 : True = term303.
Proof. exact (SYM (@lem3850529)). Qed.
Lemma lem3850531 : term303.
Proof. exact (EQ_MP (@lem3850530) (@lem0)). Qed.
Lemma lem3850532 : term348.
Proof. exact (@lem3850521 (@lem3850531)). Qed.
Lemma lem3850534 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3850535 : term303 = term309.
Proof. exact (@lem3850534 (NUMERAL 0) term129). Qed.
Lemma lem3850536 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3850537 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3850538 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3850537 h1) (fun h1 : term309 = True => @lem3850536)). Qed.
Lemma lem3850539 : term309 = True.
Proof. exact (EQ_MP (@lem3850538) (@lem3850536)). Qed.
Lemma lem3850540 : term303 = True.
Proof. exact (TRANS (@lem3850535) (@lem3850539)). Qed.
Lemma lem3850541 : True = term303.
Proof. exact (SYM (@lem3850540)). Qed.
Lemma lem3850542 : term303.
Proof. exact (EQ_MP (@lem3850541) (@lem0)). Qed.
Lemma lem3850543 : term349.
Proof. exact (@lem3850532 (@lem3850542)). Qed.
Lemma lem3850545 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3850546 : term303 = term309.
Proof. exact (@lem3850545 (NUMERAL 0) term129). Qed.
Lemma lem3850547 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3850548 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3850549 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3850548 h1) (fun h1 : term309 = True => @lem3850547)). Qed.
Lemma lem3850550 : term309 = True.
Proof. exact (EQ_MP (@lem3850549) (@lem3850547)). Qed.
Lemma lem3850551 : term303 = True.
Proof. exact (TRANS (@lem3850546) (@lem3850550)). Qed.
Lemma lem3850552 : True = term303.
Proof. exact (SYM (@lem3850551)). Qed.
Lemma lem3850553 : term303.
Proof. exact (EQ_MP (@lem3850552) (@lem0)). Qed.
Lemma lem3850554 : term350.
Proof. exact (@lem3850543 (@lem3850553)). Qed.
Lemma lem3850556 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3850557 : term172 = term173.
Proof. exact (@lem3850556 term129 term129). Qed.
Lemma lem3850558 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3850559 : term175 = term129.
Proof. exact (EQ_MP (@lem3850558) (@lem940073)). Qed.
Lemma lem3850560 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3850561 : term173 = term128.
Proof. exact (MK_COMB (@lem3850560) (@lem3850559)). Qed.
Lemma lem3850562 : term172 = term128.
Proof. exact (TRANS (@lem3850557) (@lem3850561)). Qed.
Lemma lem3850564 (m : nat) (n : nat) : (term202 m n) = (term203 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3850565 : term199 = term204.
Proof. exact (@lem3850564 term129 term129). Qed.
Lemma lem3850566 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3850567 : term175 = term129.
Proof. exact (EQ_MP (@lem3850566) (@lem940073)). Qed.
Lemma lem3850568 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3850569 : term173 = term128.
Proof. exact (MK_COMB (@lem3850568) (@lem3850567)). Qed.
Lemma lem3850570 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3850571 : term204 = term163.
Proof. exact (MK_COMB (@lem3850570) (@lem3850569)). Qed.
Lemma lem3850572 : term199 = term163.
Proof. exact (TRANS (@lem3850565) (@lem3850571)). Qed.
Lemma lem3850573 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3850574 : term351 = term343.
Proof. exact (MK_COMB (@lem3850573) (@lem3850572)). Qed.
Lemma lem3850575 : term352 = term345.
Proof. exact (MK_COMB (@lem3850574) (@lem3850562)). Qed.
Lemma lem3850577 (m : nat) : (term353 m) = term114.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3850578 : term345 = term114.
Proof. exact (@lem3850577 term129). Qed.
Lemma lem3850579 : term352 = term114.
Proof. exact (TRANS (@lem3850575) (@lem3850578)). Qed.
Lemma lem3850580 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3850581 : term354 = term355.
Proof. exact (MK_COMB (@lem3850580) (@lem3850579)). Qed.
Lemma lem3850582 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem3850583 : term356 = term314.
Proof. exact (MK_COMB (@lem3850581) (@lem3850582)). Qed.
Lemma lem3850585 (x : nat) : (term313 x) = term114.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3850586 : term314 = term114.
Proof. exact (@lem3850585 term129). Qed.
Lemma lem3850587 : term356 = term114.
Proof. exact (TRANS (@lem3850583) (@lem3850586)). Qed.
Lemma lem3850589 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3850590 : term172 = term173.
Proof. exact (@lem3850589 term129 term129). Qed.
Lemma lem3850591 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3850592 : term175 = term129.
Proof. exact (EQ_MP (@lem3850591) (@lem940073)). Qed.
Lemma lem3850593 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3850594 : term173 = term128.
Proof. exact (MK_COMB (@lem3850593) (@lem3850592)). Qed.
Lemma lem3850595 : term172 = term128.
Proof. exact (TRANS (@lem3850590) (@lem3850594)). Qed.
Lemma lem3850596 : term355 = term355.
Proof. exact (eq_refl term355). Qed.
Lemma lem3850597 : term357 = term314.
Proof. exact (MK_COMB (@lem3850596) (@lem3850595)). Qed.
Lemma lem3850599 (x : nat) : (term313 x) = term114.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3850600 : term314 = term114.
Proof. exact (@lem3850599 term129). Qed.
Lemma lem3850601 : term357 = term114.
Proof. exact (TRANS (@lem3850597) (@lem3850600)). Qed.
Lemma lem3850602 : term114 = term357.
Proof. exact (SYM (@lem3850601)). Qed.
Lemma lem3850603 : term356 = term357.
Proof. exact (TRANS (@lem3850587) (@lem3850602)). Qed.
Lemma lem3850604 : term346 = term160.
Proof. exact (@lem3850554 (@lem3850603)). Qed.
Lemma lem3850605 : term345 = term160.
Proof. exact (TRANS (@lem3850520) (@lem3850604)). Qed.
Lemma lem3850607 (x : real) : (term179 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3850608 : term160 = term114.
Proof. exact (@lem3850607 term114). Qed.
Lemma lem3850609 : term345 = term114.
Proof. exact (TRANS (@lem3850605) (@lem3850608)). Qed.
Lemma lem3850610 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3850611 : term358 = term355.
Proof. exact (MK_COMB (@lem3850610) (@lem3850609)). Qed.
Lemma lem3850612 (_44737 : int) : (real_of_int _44737) = (real_of_int _44737).
Proof. exact (eq_refl (real_of_int _44737)). Qed.
Lemma lem3850613 (_44737 : int) : (term342 _44737) = (term359 _44737).
Proof. exact (MK_COMB (@lem3850611) (@lem3850612 _44737)). Qed.
Lemma lem3850614 (_44737 : int) : (term364 _44737) = (term359 _44737).
Proof. exact (TRANS (@lem3850511 _44737) (@lem3850613 _44737)). Qed.
Lemma lem3850615 (_44737 : int) : (term359 _44737) = term114.
Proof. exact (@lem1982719 (real_of_int _44737)). Qed.
Lemma lem3850616 (_44737 : int) : (term364 _44737) = term114.
Proof. exact (TRANS (@lem3850614 _44737) (@lem3850615 _44737)). Qed.
Lemma lem3850617 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3850618 (_44737 : int) : (term365 _44737) = term361.
Proof. exact (MK_COMB (@lem3850617) (@lem3850616 _44737)). Qed.
Lemma lem3850619 : term163 = term163.
Proof. exact (eq_refl term163). Qed.
Lemma lem3850620 (_44737 : int) : (term382 _44737) = term383.
Proof. exact (MK_COMB (@lem3850618 _44737) (@lem3850619)). Qed.
Lemma lem3850621 (_44737 : int) : (term381 _44737) = term383.
Proof. exact (TRANS (@lem3850510 _44737) (@lem3850620 _44737)). Qed.
Lemma lem3850622 : term383 = term163.
Proof. exact (@lem1982721 term163). Qed.
Lemma lem3850623 (_44737 : int) : (term381 _44737) = term163.
Proof. exact (TRANS (@lem3850621 _44737) (@lem3850622)). Qed.
Lemma lem3850624 (_44734 : int) : (term207 _44734) = (term207 _44734).
Proof. exact (eq_refl (term207 _44734)). Qed.
Lemma lem3850625 (_44737 : int) (_44734 : int) : (term411 _44734 _44737) = (term208 _44734).
Proof. exact (MK_COMB (@lem3850624 _44734) (@lem3850623 _44737)). Qed.
Lemma lem3850626 (_44737 : int) (_44734 : int) : (term410 _44734 _44737) = (term208 _44734).
Proof. exact (TRANS (@lem3850509 _44734 _44737) (@lem3850625 _44737 _44734)). Qed.
Lemma lem3850627 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3850628 (_44737 : int) (_44734 : int) : (term412 _44734 _44737) = (term413 _44734).
Proof. exact (MK_COMB (@lem3850627) (@lem3850626 _44737 _44734)). Qed.
Lemma lem3850629 : term114 = term114.
Proof. exact (eq_refl term114). Qed.
Lemma lem3850630 (_44737 : int) (_44734 : int) : (term409 _44734 _44737) = (term414 _44734).
Proof. exact (MK_COMB (@lem3850628 _44737 _44734) (@lem3850629)). Qed.
Lemma lem3850631 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term398 _44735 _44736 _44734 _44737) : term414 _44734.
Proof. exact (EQ_MP (@lem3850630 _44737 _44734) (@lem3850508 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3850633 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3850634 : term302 = term303.
Proof. exact (@lem3850633 term114 term128). Qed.
Lemma lem3850636 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3850637 : term128 = term198.
Proof. exact (@lem3850636 term129). Qed.
Lemma lem3850639 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3850640 : term114 = term160.
Proof. exact (@lem3850639 (NUMERAL 0)). Qed.
Lemma lem3850641 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3850642 : term304 = term305.
Proof. exact (MK_COMB (@lem3850641) (@lem3850640)). Qed.
Lemma lem3850643 : term303 = term306.
Proof. exact (MK_COMB (@lem3850642) (@lem3850637)). Qed.
Lemma lem3850644 : term307.
Proof. exact (@lem1980255 term114 term128 term128 term128). Qed.
Lemma lem3850646 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3850647 : term303 = term309.
Proof. exact (@lem3850646 (NUMERAL 0) term129). Qed.
Lemma lem3850648 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3850649 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3850650 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3850649 h1) (fun h1 : term309 = True => @lem3850648)). Qed.
Lemma lem3850651 : term309 = True.
Proof. exact (EQ_MP (@lem3850650) (@lem3850648)). Qed.
Lemma lem3850652 : term303 = True.
Proof. exact (TRANS (@lem3850647) (@lem3850651)). Qed.
Lemma lem3850653 : True = term303.
Proof. exact (SYM (@lem3850652)). Qed.
Lemma lem3850654 : term303.
Proof. exact (EQ_MP (@lem3850653) (@lem0)). Qed.
Lemma lem3850655 : term311.
Proof. exact (@lem3850644 (@lem3850654)). Qed.
Lemma lem3850657 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3850658 : term303 = term309.
Proof. exact (@lem3850657 (NUMERAL 0) term129). Qed.
Lemma lem3850659 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3850660 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3850661 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3850660 h1) (fun h1 : term309 = True => @lem3850659)). Qed.
Lemma lem3850662 : term309 = True.
Proof. exact (EQ_MP (@lem3850661) (@lem3850659)). Qed.
Lemma lem3850663 : term303 = True.
Proof. exact (TRANS (@lem3850658) (@lem3850662)). Qed.
Lemma lem3850664 : True = term303.
Proof. exact (SYM (@lem3850663)). Qed.
Lemma lem3850665 : term303.
Proof. exact (EQ_MP (@lem3850664) (@lem0)). Qed.
Lemma lem3850666 : term306 = term312.
Proof. exact (@lem3850655 (@lem3850665)). Qed.
Lemma lem3850668 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3850669 : term172 = term173.
Proof. exact (@lem3850668 term129 term129). Qed.
Lemma lem3850670 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3850671 : term175 = term129.
Proof. exact (EQ_MP (@lem3850670) (@lem940073)). Qed.
Lemma lem3850672 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3850673 : term173 = term128.
Proof. exact (MK_COMB (@lem3850672) (@lem3850671)). Qed.
Lemma lem3850674 : term172 = term128.
Proof. exact (TRANS (@lem3850669) (@lem3850673)). Qed.
Lemma lem3850676 (x : nat) : (term313 x) = term114.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3850677 : term314 = term114.
Proof. exact (@lem3850676 term129). Qed.
Lemma lem3850678 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3850679 : term315 = term304.
Proof. exact (MK_COMB (@lem3850678) (@lem3850677)). Qed.
Lemma lem3850680 : term312 = term303.
Proof. exact (MK_COMB (@lem3850679) (@lem3850674)). Qed.
Lemma lem3850682 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3850683 : term303 = term309.
Proof. exact (@lem3850682 (NUMERAL 0) term129). Qed.
Lemma lem3850684 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3850685 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3850686 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3850685 h1) (fun h1 : term309 = True => @lem3850684)). Qed.
Lemma lem3850687 : term309 = True.
Proof. exact (EQ_MP (@lem3850686) (@lem3850684)). Qed.
Lemma lem3850688 : term303 = True.
Proof. exact (TRANS (@lem3850683) (@lem3850687)). Qed.
Lemma lem3850689 : term312 = True.
Proof. exact (TRANS (@lem3850680) (@lem3850688)). Qed.
Lemma lem3850690 : term306 = True.
Proof. exact (TRANS (@lem3850666) (@lem3850689)). Qed.
Lemma lem3850691 : term303 = True.
Proof. exact (TRANS (@lem3850643) (@lem3850690)). Qed.
Lemma lem3850692 : term302 = True.
Proof. exact (TRANS (@lem3850634) (@lem3850691)). Qed.
Lemma lem3850693 : True = term302.
Proof. exact (SYM (@lem3850692)). Qed.
Lemma lem3850694 : term302.
Proof. exact (EQ_MP (@lem3850693) (@lem0)). Qed.
Lemma lem3850695 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term398 _44735 _44736 _44734 _44737) : term415 _44734.
Proof. exact (conj (@lem3850694) (@lem3850631 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3850697 (x : real) (y : real) : term317 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3850698 (_44734 : int) : term416 _44734.
Proof. exact (@lem3850697 term128 (term208 _44734)). Qed.
Lemma lem3850699 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term398 _44735 _44736 _44734 _44737) : term417 _44734.
Proof. exact (@lem3850698 _44734 (@lem3850695 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3850700 (_44734 : int) : (term418 _44734) = (term208 _44734).
Proof. exact (@lem1982733 (term208 _44734)). Qed.
Lemma lem3850701 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3850702 (_44734 : int) : (term419 _44734) = (term413 _44734).
Proof. exact (MK_COMB (@lem3850701) (@lem3850700 _44734)). Qed.
Lemma lem3850703 : term114 = term114.
Proof. exact (eq_refl term114). Qed.
Lemma lem3850704 (_44734 : int) : (term417 _44734) = (term414 _44734).
Proof. exact (MK_COMB (@lem3850702 _44734) (@lem3850703)). Qed.
Lemma lem3850705 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term398 _44735 _44736 _44734 _44737) : term414 _44734.
Proof. exact (EQ_MP (@lem3850704 _44734) (@lem3850699 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3850706 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term398 _44735 _44736 _44734 _44737) : term420 _44734.
Proof. exact (conj (@lem3850705 _44735 _44736 _44734 _44737 h1) (@lem3850416 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3850708 (x : real) (y : real) : term421 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem3850709 (_44734 : int) : term422 _44734.
Proof. exact (@lem3850708 (term208 _44734) (real_of_int _44734)). Qed.
Lemma lem3850710 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term398 _44735 _44736 _44734 _44737) : term423 _44734.
Proof. exact (@lem3850709 _44734 (@lem3850706 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3850711 (_44734 : int) : (term424 _44734) = (term382 _44734).
Proof. exact (@lem1982759 (term190 _44734) (real_of_int _44734) term163). Qed.
Lemma lem3850712 (_44734 : int) : (term364 _44734) = (term342 _44734).
Proof. exact (@lem1982713 term163 (real_of_int _44734)). Qed.
Lemma lem3850714 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3850715 : term128 = term198.
Proof. exact (@lem3850714 term129). Qed.
Lemma lem3850717 (x : nat) : (term161 x) = (term162 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3850718 : term163 = term164.
Proof. exact (@lem3850717 term129). Qed.
Lemma lem3850719 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3850720 : term343 = term344.
Proof. exact (MK_COMB (@lem3850719) (@lem3850718)). Qed.
Lemma lem3850721 : term345 = term346.
Proof. exact (MK_COMB (@lem3850720) (@lem3850715)). Qed.
Lemma lem3850722 : term347.
Proof. exact (@lem1981473 term163 term128 term128 term128 term114 term128). Qed.
Lemma lem3850724 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3850725 : term303 = term309.
Proof. exact (@lem3850724 (NUMERAL 0) term129). Qed.
Lemma lem3850726 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3850727 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3850728 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3850727 h1) (fun h1 : term309 = True => @lem3850726)). Qed.
Lemma lem3850729 : term309 = True.
Proof. exact (EQ_MP (@lem3850728) (@lem3850726)). Qed.
Lemma lem3850730 : term303 = True.
Proof. exact (TRANS (@lem3850725) (@lem3850729)). Qed.
Lemma lem3850731 : True = term303.
Proof. exact (SYM (@lem3850730)). Qed.
Lemma lem3850732 : term303.
Proof. exact (EQ_MP (@lem3850731) (@lem0)). Qed.
Lemma lem3850733 : term348.
Proof. exact (@lem3850722 (@lem3850732)). Qed.
Lemma lem3850735 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3850736 : term303 = term309.
Proof. exact (@lem3850735 (NUMERAL 0) term129). Qed.
Lemma lem3850737 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3850738 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3850739 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3850738 h1) (fun h1 : term309 = True => @lem3850737)). Qed.
Lemma lem3850740 : term309 = True.
Proof. exact (EQ_MP (@lem3850739) (@lem3850737)). Qed.
Lemma lem3850741 : term303 = True.
Proof. exact (TRANS (@lem3850736) (@lem3850740)). Qed.
Lemma lem3850742 : True = term303.
Proof. exact (SYM (@lem3850741)). Qed.
Lemma lem3850743 : term303.
Proof. exact (EQ_MP (@lem3850742) (@lem0)). Qed.
Lemma lem3850744 : term349.
Proof. exact (@lem3850733 (@lem3850743)). Qed.
Lemma lem3850746 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3850747 : term303 = term309.
Proof. exact (@lem3850746 (NUMERAL 0) term129). Qed.
Lemma lem3850748 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3850749 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3850750 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3850749 h1) (fun h1 : term309 = True => @lem3850748)). Qed.
Lemma lem3850751 : term309 = True.
Proof. exact (EQ_MP (@lem3850750) (@lem3850748)). Qed.
Lemma lem3850752 : term303 = True.
Proof. exact (TRANS (@lem3850747) (@lem3850751)). Qed.
Lemma lem3850753 : True = term303.
Proof. exact (SYM (@lem3850752)). Qed.
Lemma lem3850754 : term303.
Proof. exact (EQ_MP (@lem3850753) (@lem0)). Qed.
Lemma lem3850755 : term350.
Proof. exact (@lem3850744 (@lem3850754)). Qed.
Lemma lem3850757 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3850758 : term172 = term173.
Proof. exact (@lem3850757 term129 term129). Qed.
Lemma lem3850759 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3850760 : term175 = term129.
Proof. exact (EQ_MP (@lem3850759) (@lem940073)). Qed.
Lemma lem3850761 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3850762 : term173 = term128.
Proof. exact (MK_COMB (@lem3850761) (@lem3850760)). Qed.
Lemma lem3850763 : term172 = term128.
Proof. exact (TRANS (@lem3850758) (@lem3850762)). Qed.
Lemma lem3850765 (m : nat) (n : nat) : (term202 m n) = (term203 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3850766 : term199 = term204.
Proof. exact (@lem3850765 term129 term129). Qed.
Lemma lem3850767 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3850768 : term175 = term129.
Proof. exact (EQ_MP (@lem3850767) (@lem940073)). Qed.
Lemma lem3850769 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3850770 : term173 = term128.
Proof. exact (MK_COMB (@lem3850769) (@lem3850768)). Qed.
Lemma lem3850771 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3850772 : term204 = term163.
Proof. exact (MK_COMB (@lem3850771) (@lem3850770)). Qed.
Lemma lem3850773 : term199 = term163.
Proof. exact (TRANS (@lem3850766) (@lem3850772)). Qed.
Lemma lem3850774 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3850775 : term351 = term343.
Proof. exact (MK_COMB (@lem3850774) (@lem3850773)). Qed.
Lemma lem3850776 : term352 = term345.
Proof. exact (MK_COMB (@lem3850775) (@lem3850763)). Qed.
Lemma lem3850778 (m : nat) : (term353 m) = term114.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3850779 : term345 = term114.
Proof. exact (@lem3850778 term129). Qed.
Lemma lem3850780 : term352 = term114.
Proof. exact (TRANS (@lem3850776) (@lem3850779)). Qed.
Lemma lem3850781 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3850782 : term354 = term355.
Proof. exact (MK_COMB (@lem3850781) (@lem3850780)). Qed.
Lemma lem3850783 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem3850784 : term356 = term314.
Proof. exact (MK_COMB (@lem3850782) (@lem3850783)). Qed.
Lemma lem3850786 (x : nat) : (term313 x) = term114.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3850787 : term314 = term114.
Proof. exact (@lem3850786 term129). Qed.
Lemma lem3850788 : term356 = term114.
Proof. exact (TRANS (@lem3850784) (@lem3850787)). Qed.
Lemma lem3850790 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3850791 : term172 = term173.
Proof. exact (@lem3850790 term129 term129). Qed.
Lemma lem3850792 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3850793 : term175 = term129.
Proof. exact (EQ_MP (@lem3850792) (@lem940073)). Qed.
Lemma lem3850794 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3850795 : term173 = term128.
Proof. exact (MK_COMB (@lem3850794) (@lem3850793)). Qed.
Lemma lem3850796 : term172 = term128.
Proof. exact (TRANS (@lem3850791) (@lem3850795)). Qed.
Lemma lem3850797 : term355 = term355.
Proof. exact (eq_refl term355). Qed.
Lemma lem3850798 : term357 = term314.
Proof. exact (MK_COMB (@lem3850797) (@lem3850796)). Qed.
Lemma lem3850800 (x : nat) : (term313 x) = term114.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3850801 : term314 = term114.
Proof. exact (@lem3850800 term129). Qed.
Lemma lem3850802 : term357 = term114.
Proof. exact (TRANS (@lem3850798) (@lem3850801)). Qed.
Lemma lem3850803 : term114 = term357.
Proof. exact (SYM (@lem3850802)). Qed.
Lemma lem3850804 : term356 = term357.
Proof. exact (TRANS (@lem3850788) (@lem3850803)). Qed.
Lemma lem3850805 : term346 = term160.
Proof. exact (@lem3850755 (@lem3850804)). Qed.
Lemma lem3850806 : term345 = term160.
Proof. exact (TRANS (@lem3850721) (@lem3850805)). Qed.
Lemma lem3850808 (x : real) : (term179 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3850809 : term160 = term114.
Proof. exact (@lem3850808 term114). Qed.
Lemma lem3850810 : term345 = term114.
Proof. exact (TRANS (@lem3850806) (@lem3850809)). Qed.
Lemma lem3850811 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3850812 : term358 = term355.
Proof. exact (MK_COMB (@lem3850811) (@lem3850810)). Qed.
Lemma lem3850813 (_44734 : int) : (real_of_int _44734) = (real_of_int _44734).
Proof. exact (eq_refl (real_of_int _44734)). Qed.
Lemma lem3850814 (_44734 : int) : (term342 _44734) = (term359 _44734).
Proof. exact (MK_COMB (@lem3850812) (@lem3850813 _44734)). Qed.
Lemma lem3850815 (_44734 : int) : (term364 _44734) = (term359 _44734).
Proof. exact (TRANS (@lem3850712 _44734) (@lem3850814 _44734)). Qed.
Lemma lem3850816 (_44734 : int) : (term359 _44734) = term114.
Proof. exact (@lem1982719 (real_of_int _44734)). Qed.
Lemma lem3850817 (_44734 : int) : (term364 _44734) = term114.
Proof. exact (TRANS (@lem3850815 _44734) (@lem3850816 _44734)). Qed.
Lemma lem3850818 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3850819 (_44734 : int) : (term365 _44734) = term361.
Proof. exact (MK_COMB (@lem3850818) (@lem3850817 _44734)). Qed.
Lemma lem3850820 : term163 = term163.
Proof. exact (eq_refl term163). Qed.
Lemma lem3850821 (_44734 : int) : (term382 _44734) = term383.
Proof. exact (MK_COMB (@lem3850819 _44734) (@lem3850820)). Qed.
Lemma lem3850822 (_44734 : int) : (term424 _44734) = term383.
Proof. exact (TRANS (@lem3850711 _44734) (@lem3850821 _44734)). Qed.
Lemma lem3850823 : term383 = term163.
Proof. exact (@lem1982721 term163). Qed.
Lemma lem3850824 (_44734 : int) : (term424 _44734) = term163.
Proof. exact (TRANS (@lem3850822 _44734) (@lem3850823)). Qed.
Lemma lem3850825 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3850826 (_44734 : int) : (term425 _44734) = term385.
Proof. exact (MK_COMB (@lem3850825) (@lem3850824 _44734)). Qed.
Lemma lem3850827 : term114 = term114.
Proof. exact (eq_refl term114). Qed.
Lemma lem3850828 (_44734 : int) : (term423 _44734) = term386.
Proof. exact (MK_COMB (@lem3850826 _44734) (@lem3850827)). Qed.
Lemma lem3850829 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term398 _44735 _44736 _44734 _44737) : term386.
Proof. exact (EQ_MP (@lem3850828 _44734) (@lem3850710 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3850831 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3850832 : term386 = term387.
Proof. exact (@lem3850831 term114 term163). Qed.
Lemma lem3850834 (x : nat) : (term161 x) = (term162 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3850835 : term163 = term164.
Proof. exact (@lem3850834 term129). Qed.
Lemma lem3850837 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3850838 : term114 = term160.
Proof. exact (@lem3850837 (NUMERAL 0)). Qed.
Lemma lem3850839 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3850840 : term116 = term388.
Proof. exact (MK_COMB (@lem3850839) (@lem3850838)). Qed.
Lemma lem3850841 : term387 = term389.
Proof. exact (MK_COMB (@lem3850840) (@lem3850835)). Qed.
Lemma lem3850842 : term390.
Proof. exact (@lem1980026 term114 term128 term163 term128). Qed.
Lemma lem3850844 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3850845 : term303 = term309.
Proof. exact (@lem3850844 (NUMERAL 0) term129). Qed.
Lemma lem3850846 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3850847 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3850848 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3850847 h1) (fun h1 : term309 = True => @lem3850846)). Qed.
Lemma lem3850849 : term309 = True.
Proof. exact (EQ_MP (@lem3850848) (@lem3850846)). Qed.
Lemma lem3850850 : term303 = True.
Proof. exact (TRANS (@lem3850845) (@lem3850849)). Qed.
Lemma lem3850851 : True = term303.
Proof. exact (SYM (@lem3850850)). Qed.
Lemma lem3850852 : term303.
Proof. exact (EQ_MP (@lem3850851) (@lem0)). Qed.
Lemma lem3850853 : term391.
Proof. exact (@lem3850842 (@lem3850852)). Qed.
Lemma lem3850855 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3850856 : term303 = term309.
Proof. exact (@lem3850855 (NUMERAL 0) term129). Qed.
Lemma lem3850857 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3850858 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3850859 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3850858 h1) (fun h1 : term309 = True => @lem3850857)). Qed.
Lemma lem3850860 : term309 = True.
Proof. exact (EQ_MP (@lem3850859) (@lem3850857)). Qed.
Lemma lem3850861 : term303 = True.
Proof. exact (TRANS (@lem3850856) (@lem3850860)). Qed.
Lemma lem3850862 : True = term303.
Proof. exact (SYM (@lem3850861)). Qed.
Lemma lem3850863 : term303.
Proof. exact (EQ_MP (@lem3850862) (@lem0)). Qed.
Lemma lem3850864 : term389 = term392.
Proof. exact (@lem3850853 (@lem3850863)). Qed.
Lemma lem3850866 (m : nat) (n : nat) : (term202 m n) = (term203 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3850867 : term199 = term204.
Proof. exact (@lem3850866 term129 term129). Qed.
Lemma lem3850868 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3850869 : term175 = term129.
Proof. exact (EQ_MP (@lem3850868) (@lem940073)). Qed.
Lemma lem3850870 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3850871 : term173 = term128.
Proof. exact (MK_COMB (@lem3850870) (@lem3850869)). Qed.
Lemma lem3850872 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3850873 : term204 = term163.
Proof. exact (MK_COMB (@lem3850872) (@lem3850871)). Qed.
Lemma lem3850874 : term199 = term163.
Proof. exact (TRANS (@lem3850867) (@lem3850873)). Qed.
Lemma lem3850876 (x : nat) : (term313 x) = term114.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3850877 : term314 = term114.
Proof. exact (@lem3850876 term129). Qed.
Lemma lem3850878 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3850879 : term393 = term116.
Proof. exact (MK_COMB (@lem3850878) (@lem3850877)). Qed.
Lemma lem3850880 : term392 = term387.
Proof. exact (MK_COMB (@lem3850879) (@lem3850874)). Qed.
Lemma lem3850882 (m : nat) (n : nat) : (term394 m n) = (term395 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3850883 : term387 = term396.
Proof. exact (@lem3850882 (NUMERAL 0) term129). Qed.
Lemma lem3850884 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3850885 (h1 : term310 = (BIT1 0)) : (term129 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3850886 : (term310 = (BIT1 0)) = ((term129 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3850885 h1) (fun h1 : (term129 = (NUMERAL 0)) = False => @lem3850884)). Qed.
Lemma lem3850887 : (term129 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3850886) (@lem3850884)). Qed.
Lemma lem3850888 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3850889 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3850890 : term397 = (and True).
Proof. exact (MK_COMB (@lem3850889) (@lem3850888)). Qed.
Lemma lem3850891 : term396 = (True /\ False).
Proof. exact (MK_COMB (@lem3850890) (@lem3850887)). Qed.
Lemma lem3850893 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3850894 : term396 = False.
Proof. exact (TRANS (@lem3850891) (@lem3850893)). Qed.
Lemma lem3850895 : term387 = False.
Proof. exact (TRANS (@lem3850883) (@lem3850894)). Qed.
Lemma lem3850896 : term392 = False.
Proof. exact (TRANS (@lem3850880) (@lem3850895)). Qed.
Lemma lem3850897 : term389 = False.
Proof. exact (TRANS (@lem3850864) (@lem3850896)). Qed.
Lemma lem3850898 : term387 = False.
Proof. exact (TRANS (@lem3850841) (@lem3850897)). Qed.
Lemma lem3850899 : term386 = False.
Proof. exact (TRANS (@lem3850832) (@lem3850898)). Qed.
Lemma lem3850900 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term398 _44735 _44736 _44734 _44737) : False.
Proof. exact (EQ_MP (@lem3850899) (@lem3850829 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3850901 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term295 _44735 _44736 _44734 _44737) : False.
Proof. exact (or_elim (@lem3849591 _44735 _44736 _44734 _44737 h1) (fun h0 : term301 _44735 _44736 _44734 _44737 => @lem3850327 _44735 _44736 _44734 _44737 h0) (fun h0 : term398 _44735 _44736 _44734 _44737 => @lem3850900 _44735 _44736 _44734 _44737 h0)). Qed.
Lemma lem3850902 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term291 _44735 _44736 _44734 _44737) : term291 _44735 _44736 _44734 _44737.
Proof. exact (h1). Qed.
Lemma lem3850903 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term426 _44735 _44736 _44734 _44737) : term426 _44735 _44736 _44734 _44737.
Proof. exact (h1). Qed.
Lemma lem3850904 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term426 _44735 _44736 _44734 _44737) : term292 _44735 _44736 _44734 _44737.
Proof. exact (proj2 (@lem3850903 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3850906 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term426 _44735 _44736 _44734 _44737) : term279 _44735 _44736 _44734 _44737.
Proof. exact (proj2 (@lem3850904 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3850908 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term426 _44735 _44736 _44734 _44737) : term266 _44735 _44736 _44734 _44737.
Proof. exact (proj2 (@lem3850906 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3850910 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term426 _44735 _44736 _44734 _44737) : term253 _44735 _44736 _44734 _44737.
Proof. exact (proj2 (@lem3850908 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3850912 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term426 _44735 _44736 _44734 _44737) : term241 _44735 _44736 _44734 _44737.
Proof. exact (proj2 (@lem3850910 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3850913 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term426 _44735 _44736 _44734 _44737) : (term189 _44735 _44736 _44737) = term114.
Proof. exact (proj1 (@lem3850910 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3850914 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term426 _44735 _44736 _44734 _44737) : term212 _44734 _44737.
Proof. exact (proj2 (@lem3850912 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3850915 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term426 _44735 _44736 _44734 _44737) : (term220 _44734 _44735 _44736) = term114.
Proof. exact (proj1 (@lem3850912 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3850917 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3850918 : term302 = term303.
Proof. exact (@lem3850917 term114 term128). Qed.
Lemma lem3850920 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3850921 : term128 = term198.
Proof. exact (@lem3850920 term129). Qed.
Lemma lem3850923 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3850924 : term114 = term160.
Proof. exact (@lem3850923 (NUMERAL 0)). Qed.
Lemma lem3850925 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3850926 : term304 = term305.
Proof. exact (MK_COMB (@lem3850925) (@lem3850924)). Qed.
Lemma lem3850927 : term303 = term306.
Proof. exact (MK_COMB (@lem3850926) (@lem3850921)). Qed.
Lemma lem3850928 : term307.
Proof. exact (@lem1980255 term114 term128 term128 term128). Qed.
Lemma lem3850930 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3850931 : term303 = term309.
Proof. exact (@lem3850930 (NUMERAL 0) term129). Qed.
Lemma lem3850932 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3850933 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3850934 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3850933 h1) (fun h1 : term309 = True => @lem3850932)). Qed.
Lemma lem3850935 : term309 = True.
Proof. exact (EQ_MP (@lem3850934) (@lem3850932)). Qed.
Lemma lem3850936 : term303 = True.
Proof. exact (TRANS (@lem3850931) (@lem3850935)). Qed.
Lemma lem3850937 : True = term303.
Proof. exact (SYM (@lem3850936)). Qed.
Lemma lem3850938 : term303.
Proof. exact (EQ_MP (@lem3850937) (@lem0)). Qed.
Lemma lem3850939 : term311.
Proof. exact (@lem3850928 (@lem3850938)). Qed.
Lemma lem3850941 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3850942 : term303 = term309.
Proof. exact (@lem3850941 (NUMERAL 0) term129). Qed.
Lemma lem3850943 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3850944 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3850945 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3850944 h1) (fun h1 : term309 = True => @lem3850943)). Qed.
Lemma lem3850946 : term309 = True.
Proof. exact (EQ_MP (@lem3850945) (@lem3850943)). Qed.
Lemma lem3850947 : term303 = True.
Proof. exact (TRANS (@lem3850942) (@lem3850946)). Qed.
Lemma lem3850948 : True = term303.
Proof. exact (SYM (@lem3850947)). Qed.
Lemma lem3850949 : term303.
Proof. exact (EQ_MP (@lem3850948) (@lem0)). Qed.
Lemma lem3850950 : term306 = term312.
Proof. exact (@lem3850939 (@lem3850949)). Qed.
Lemma lem3850952 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3850953 : term172 = term173.
Proof. exact (@lem3850952 term129 term129). Qed.
Lemma lem3850954 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3850955 : term175 = term129.
Proof. exact (EQ_MP (@lem3850954) (@lem940073)). Qed.
Lemma lem3850956 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3850957 : term173 = term128.
Proof. exact (MK_COMB (@lem3850956) (@lem3850955)). Qed.
Lemma lem3850958 : term172 = term128.
Proof. exact (TRANS (@lem3850953) (@lem3850957)). Qed.
Lemma lem3850960 (x : nat) : (term313 x) = term114.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3850961 : term314 = term114.
Proof. exact (@lem3850960 term129). Qed.
Lemma lem3850962 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3850963 : term315 = term304.
Proof. exact (MK_COMB (@lem3850962) (@lem3850961)). Qed.
Lemma lem3850964 : term312 = term303.
Proof. exact (MK_COMB (@lem3850963) (@lem3850958)). Qed.
Lemma lem3850966 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3850967 : term303 = term309.
Proof. exact (@lem3850966 (NUMERAL 0) term129). Qed.
Lemma lem3850968 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3850969 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3850970 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3850969 h1) (fun h1 : term309 = True => @lem3850968)). Qed.
Lemma lem3850971 : term309 = True.
Proof. exact (EQ_MP (@lem3850970) (@lem3850968)). Qed.
Lemma lem3850972 : term303 = True.
Proof. exact (TRANS (@lem3850967) (@lem3850971)). Qed.
Lemma lem3850973 : term312 = True.
Proof. exact (TRANS (@lem3850964) (@lem3850972)). Qed.
Lemma lem3850974 : term306 = True.
Proof. exact (TRANS (@lem3850950) (@lem3850973)). Qed.
Lemma lem3850975 : term303 = True.
Proof. exact (TRANS (@lem3850927) (@lem3850974)). Qed.
Lemma lem3850976 : term302 = True.
Proof. exact (TRANS (@lem3850918) (@lem3850975)). Qed.
Lemma lem3850977 : True = term302.
Proof. exact (SYM (@lem3850976)). Qed.
Lemma lem3850978 : term302.
Proof. exact (EQ_MP (@lem3850977) (@lem0)). Qed.
Lemma lem3850979 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term426 _44735 _44736 _44734 _44737) : term427 _44734 _44737.
Proof. exact (conj (@lem3850978) (@lem3850914 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3850981 (x : real) (y : real) : term317 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3850982 (_44734 : int) (_44737 : int) : term428 _44734 _44737.
Proof. exact (@lem3850981 term128 (term209 _44734 _44737)). Qed.
Lemma lem3850983 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term426 _44735 _44736 _44734 _44737) : term429 _44734 _44737.
Proof. exact (@lem3850982 _44734 _44737 (@lem3850979 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3850984 (_44734 : int) (_44737 : int) : (term430 _44734 _44737) = (term209 _44734 _44737).
Proof. exact (@lem1982733 (term209 _44734 _44737)). Qed.
Lemma lem3850985 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3850986 (_44734 : int) (_44737 : int) : (term431 _44734 _44737) = (term211 _44734 _44737).
Proof. exact (MK_COMB (@lem3850985) (@lem3850984 _44734 _44737)). Qed.
Lemma lem3850987 : term114 = term114.
Proof. exact (eq_refl term114). Qed.
Lemma lem3850988 (_44734 : int) (_44737 : int) : (term429 _44734 _44737) = (term212 _44734 _44737).
Proof. exact (MK_COMB (@lem3850986 _44734 _44737) (@lem3850987)). Qed.
Lemma lem3850989 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term426 _44735 _44736 _44734 _44737) : term212 _44734 _44737.
Proof. exact (EQ_MP (@lem3850988 _44734 _44737) (@lem3850983 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3850991 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3850992 : term302 = term303.
Proof. exact (@lem3850991 term114 term128). Qed.
Lemma lem3850994 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3850995 : term128 = term198.
Proof. exact (@lem3850994 term129). Qed.
Lemma lem3850997 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3850998 : term114 = term160.
Proof. exact (@lem3850997 (NUMERAL 0)). Qed.
Lemma lem3850999 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3851000 : term304 = term305.
Proof. exact (MK_COMB (@lem3850999) (@lem3850998)). Qed.
Lemma lem3851001 : term303 = term306.
Proof. exact (MK_COMB (@lem3851000) (@lem3850995)). Qed.
Lemma lem3851002 : term307.
Proof. exact (@lem1980255 term114 term128 term128 term128). Qed.
Lemma lem3851004 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3851005 : term303 = term309.
Proof. exact (@lem3851004 (NUMERAL 0) term129). Qed.
Lemma lem3851006 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3851007 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3851008 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3851007 h1) (fun h1 : term309 = True => @lem3851006)). Qed.
Lemma lem3851009 : term309 = True.
Proof. exact (EQ_MP (@lem3851008) (@lem3851006)). Qed.
Lemma lem3851010 : term303 = True.
Proof. exact (TRANS (@lem3851005) (@lem3851009)). Qed.
Lemma lem3851011 : True = term303.
Proof. exact (SYM (@lem3851010)). Qed.
Lemma lem3851012 : term303.
Proof. exact (EQ_MP (@lem3851011) (@lem0)). Qed.
Lemma lem3851013 : term311.
Proof. exact (@lem3851002 (@lem3851012)). Qed.
Lemma lem3851015 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3851016 : term303 = term309.
Proof. exact (@lem3851015 (NUMERAL 0) term129). Qed.
Lemma lem3851017 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3851018 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3851019 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3851018 h1) (fun h1 : term309 = True => @lem3851017)). Qed.
Lemma lem3851020 : term309 = True.
Proof. exact (EQ_MP (@lem3851019) (@lem3851017)). Qed.
Lemma lem3851021 : term303 = True.
Proof. exact (TRANS (@lem3851016) (@lem3851020)). Qed.
Lemma lem3851022 : True = term303.
Proof. exact (SYM (@lem3851021)). Qed.
Lemma lem3851023 : term303.
Proof. exact (EQ_MP (@lem3851022) (@lem0)). Qed.
Lemma lem3851024 : term306 = term312.
Proof. exact (@lem3851013 (@lem3851023)). Qed.
Lemma lem3851026 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3851027 : term172 = term173.
Proof. exact (@lem3851026 term129 term129). Qed.
Lemma lem3851028 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3851029 : term175 = term129.
Proof. exact (EQ_MP (@lem3851028) (@lem940073)). Qed.
Lemma lem3851030 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3851031 : term173 = term128.
Proof. exact (MK_COMB (@lem3851030) (@lem3851029)). Qed.
Lemma lem3851032 : term172 = term128.
Proof. exact (TRANS (@lem3851027) (@lem3851031)). Qed.
Lemma lem3851034 (x : nat) : (term313 x) = term114.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3851035 : term314 = term114.
Proof. exact (@lem3851034 term129). Qed.
Lemma lem3851036 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3851037 : term315 = term304.
Proof. exact (MK_COMB (@lem3851036) (@lem3851035)). Qed.
Lemma lem3851038 : term312 = term303.
Proof. exact (MK_COMB (@lem3851037) (@lem3851032)). Qed.
Lemma lem3851040 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3851041 : term303 = term309.
Proof. exact (@lem3851040 (NUMERAL 0) term129). Qed.
Lemma lem3851042 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3851043 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3851044 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3851043 h1) (fun h1 : term309 = True => @lem3851042)). Qed.
Lemma lem3851045 : term309 = True.
Proof. exact (EQ_MP (@lem3851044) (@lem3851042)). Qed.
Lemma lem3851046 : term303 = True.
Proof. exact (TRANS (@lem3851041) (@lem3851045)). Qed.
Lemma lem3851047 : term312 = True.
Proof. exact (TRANS (@lem3851038) (@lem3851046)). Qed.
Lemma lem3851048 : term306 = True.
Proof. exact (TRANS (@lem3851024) (@lem3851047)). Qed.
Lemma lem3851049 : term303 = True.
Proof. exact (TRANS (@lem3851001) (@lem3851048)). Qed.
Lemma lem3851050 : term302 = True.
Proof. exact (TRANS (@lem3850992) (@lem3851049)). Qed.
Lemma lem3851051 : True = term302.
Proof. exact (SYM (@lem3851050)). Qed.
Lemma lem3851052 : term302.
Proof. exact (EQ_MP (@lem3851051) (@lem0)). Qed.
Lemma lem3851053 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term426 _44735 _44736 _44734 _44737) : term322 _44735 _44736 _44737.
Proof. exact (conj (@lem3851052) (@lem3850913 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3851055 (x : real) (y : real) : term323 x y.
Proof. exact (proj1 (@lem1988330 x y)). Qed.
Lemma lem3851056 (_44735 : int) (_44736 : int) (_44737 : int) : term324 _44735 _44736 _44737.
Proof. exact (@lem3851055 term128 (term189 _44735 _44736 _44737)). Qed.
Lemma lem3851057 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term426 _44735 _44736 _44734 _44737) : (term325 _44735 _44736 _44737) = term114.
Proof. exact (@lem3851056 _44735 _44736 _44737 (@lem3851053 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3851058 (_44735 : int) (_44736 : int) (_44737 : int) : (term325 _44735 _44736 _44737) = (term189 _44735 _44736 _44737).
Proof. exact (@lem1982733 (term189 _44735 _44736 _44737)). Qed.
Lemma lem3851059 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3851060 (_44735 : int) (_44736 : int) (_44737 : int) : (term326 _44735 _44736 _44737) = (term192 _44735 _44736 _44737).
Proof. exact (MK_COMB (@lem3851059) (@lem3851058 _44735 _44736 _44737)). Qed.
Lemma lem3851061 : term114 = term114.
Proof. exact (eq_refl term114). Qed.
Lemma lem3851062 (_44735 : int) (_44736 : int) (_44737 : int) : ((term325 _44735 _44736 _44737) = term114) = ((term189 _44735 _44736 _44737) = term114).
Proof. exact (MK_COMB (@lem3851060 _44735 _44736 _44737) (@lem3851061)). Qed.
Lemma lem3851063 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term426 _44735 _44736 _44734 _44737) : (term189 _44735 _44736 _44737) = term114.
Proof. exact (EQ_MP (@lem3851062 _44735 _44736 _44737) (@lem3851057 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3851065 (y : real) : term327 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem3851066 (_44734 : int) (_44735 : int) (_44736 : int) : term328 _44734 _44735 _44736.
Proof. exact (@lem3851065 (term220 _44734 _44735 _44736)). Qed.
Lemma lem3851067 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term426 _44735 _44736 _44734 _44737) : term329 _44734 _44735 _44736.
Proof. exact (@lem3851066 _44734 _44735 _44736 (@lem3850915 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3851068 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term426 _44735 _44736 _44734 _44737) : term330 _44734 _44735 _44736.
Proof. exact (@lem3851067 _44735 _44736 _44734 _44737 h1 term128). Qed.
Lemma lem3851069 (_44734 : int) (_44735 : int) (_44736 : int) : (term330 _44734 _44735 _44736) = ((term331 _44734 _44735 _44736) = term114).
Proof. exact (eq_refl (term330 _44734 _44735 _44736)). Qed.
Lemma lem3851070 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term426 _44735 _44736 _44734 _44737) : (term331 _44734 _44735 _44736) = term114.
Proof. exact (EQ_MP (@lem3851069 _44734 _44735 _44736) (@lem3851068 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3851071 (_44734 : int) (_44735 : int) (_44736 : int) : (term331 _44734 _44735 _44736) = (term220 _44734 _44735 _44736).
Proof. exact (@lem1982733 (term220 _44734 _44735 _44736)). Qed.
Lemma lem3851072 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3851073 (_44734 : int) (_44735 : int) (_44736 : int) : (term332 _44734 _44735 _44736) = (term222 _44734 _44735 _44736).
Proof. exact (MK_COMB (@lem3851072) (@lem3851071 _44734 _44735 _44736)). Qed.
Lemma lem3851074 : term114 = term114.
Proof. exact (eq_refl term114). Qed.
Lemma lem3851075 (_44734 : int) (_44735 : int) (_44736 : int) : ((term331 _44734 _44735 _44736) = term114) = ((term220 _44734 _44735 _44736) = term114).
Proof. exact (MK_COMB (@lem3851073 _44734 _44735 _44736) (@lem3851074)). Qed.
Lemma lem3851076 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term426 _44735 _44736 _44734 _44737) : (term220 _44734 _44735 _44736) = term114.
Proof. exact (EQ_MP (@lem3851075 _44734 _44735 _44736) (@lem3851070 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3851077 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term426 _44735 _44736 _44734 _44737) : term333 _44734 _44735 _44736 _44737.
Proof. exact (conj (@lem3851076 _44735 _44736 _44734 _44737 h1) (@lem3851063 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3851079 (x : real) (y : real) : term334 x y.
Proof. exact (proj1 (@lem1393126 x y)). Qed.
Lemma lem3851080 (_44734 : int) (_44735 : int) (_44736 : int) (_44737 : int) : term335 _44734 _44735 _44736 _44737.
Proof. exact (@lem3851079 (term220 _44734 _44735 _44736) (term189 _44735 _44736 _44737)). Qed.
Lemma lem3851081 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term426 _44735 _44736 _44734 _44737) : (term336 _44734 _44735 _44736 _44737) = term114.
Proof. exact (@lem3851080 _44734 _44735 _44736 _44737 (@lem3851077 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3851082 (_44734 : int) (_44735 : int) (_44736 : int) (_44737 : int) : (term336 _44734 _44735 _44736 _44737) = (term337 _44734 _44735 _44736 _44737).
Proof. exact (@lem1982755 (real_of_int _44734) (term338 _44735 _44736) (term189 _44735 _44736 _44737)). Qed.
Lemma lem3851083 (_44735 : int) (_44736 : int) (_44737 : int) : (term339 _44735 _44736 _44737) = (term340 _44735 _44736 _44737).
Proof. exact (@lem1982753 (real_of_int _44735) (term190 _44735) (term190 _44736) (term338 _44736 _44737)). Qed.
Lemma lem3851084 (_44735 : int) : (term341 _44735) = (term342 _44735).
Proof. exact (@lem1982715 term163 (real_of_int _44735)). Qed.
Lemma lem3851086 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3851087 : term128 = term198.
Proof. exact (@lem3851086 term129). Qed.
Lemma lem3851089 (x : nat) : (term161 x) = (term162 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3851090 : term163 = term164.
Proof. exact (@lem3851089 term129). Qed.
Lemma lem3851091 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3851092 : term343 = term344.
Proof. exact (MK_COMB (@lem3851091) (@lem3851090)). Qed.
Lemma lem3851093 : term345 = term346.
Proof. exact (MK_COMB (@lem3851092) (@lem3851087)). Qed.
Lemma lem3851094 : term347.
Proof. exact (@lem1981473 term163 term128 term128 term128 term114 term128). Qed.
Lemma lem3851096 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3851097 : term303 = term309.
Proof. exact (@lem3851096 (NUMERAL 0) term129). Qed.
Lemma lem3851098 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3851099 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3851100 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3851099 h1) (fun h1 : term309 = True => @lem3851098)). Qed.
Lemma lem3851101 : term309 = True.
Proof. exact (EQ_MP (@lem3851100) (@lem3851098)). Qed.
Lemma lem3851102 : term303 = True.
Proof. exact (TRANS (@lem3851097) (@lem3851101)). Qed.
Lemma lem3851103 : True = term303.
Proof. exact (SYM (@lem3851102)). Qed.
Lemma lem3851104 : term303.
Proof. exact (EQ_MP (@lem3851103) (@lem0)). Qed.
Lemma lem3851105 : term348.
Proof. exact (@lem3851094 (@lem3851104)). Qed.
Lemma lem3851107 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3851108 : term303 = term309.
Proof. exact (@lem3851107 (NUMERAL 0) term129). Qed.
Lemma lem3851109 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3851110 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3851111 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3851110 h1) (fun h1 : term309 = True => @lem3851109)). Qed.
Lemma lem3851112 : term309 = True.
Proof. exact (EQ_MP (@lem3851111) (@lem3851109)). Qed.
Lemma lem3851113 : term303 = True.
Proof. exact (TRANS (@lem3851108) (@lem3851112)). Qed.
Lemma lem3851114 : True = term303.
Proof. exact (SYM (@lem3851113)). Qed.
Lemma lem3851115 : term303.
Proof. exact (EQ_MP (@lem3851114) (@lem0)). Qed.
Lemma lem3851116 : term349.
Proof. exact (@lem3851105 (@lem3851115)). Qed.
Lemma lem3851118 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3851119 : term303 = term309.
Proof. exact (@lem3851118 (NUMERAL 0) term129). Qed.
Lemma lem3851120 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3851121 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3851122 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3851121 h1) (fun h1 : term309 = True => @lem3851120)). Qed.
Lemma lem3851123 : term309 = True.
Proof. exact (EQ_MP (@lem3851122) (@lem3851120)). Qed.
Lemma lem3851124 : term303 = True.
Proof. exact (TRANS (@lem3851119) (@lem3851123)). Qed.
Lemma lem3851125 : True = term303.
Proof. exact (SYM (@lem3851124)). Qed.
Lemma lem3851126 : term303.
Proof. exact (EQ_MP (@lem3851125) (@lem0)). Qed.
Lemma lem3851127 : term350.
Proof. exact (@lem3851116 (@lem3851126)). Qed.
Lemma lem3851129 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3851130 : term172 = term173.
Proof. exact (@lem3851129 term129 term129). Qed.
Lemma lem3851131 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3851132 : term175 = term129.
Proof. exact (EQ_MP (@lem3851131) (@lem940073)). Qed.
Lemma lem3851133 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3851134 : term173 = term128.
Proof. exact (MK_COMB (@lem3851133) (@lem3851132)). Qed.
Lemma lem3851135 : term172 = term128.
Proof. exact (TRANS (@lem3851130) (@lem3851134)). Qed.
Lemma lem3851137 (m : nat) (n : nat) : (term202 m n) = (term203 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3851138 : term199 = term204.
Proof. exact (@lem3851137 term129 term129). Qed.
Lemma lem3851139 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3851140 : term175 = term129.
Proof. exact (EQ_MP (@lem3851139) (@lem940073)). Qed.
Lemma lem3851141 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3851142 : term173 = term128.
Proof. exact (MK_COMB (@lem3851141) (@lem3851140)). Qed.
Lemma lem3851143 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3851144 : term204 = term163.
Proof. exact (MK_COMB (@lem3851143) (@lem3851142)). Qed.
Lemma lem3851145 : term199 = term163.
Proof. exact (TRANS (@lem3851138) (@lem3851144)). Qed.
Lemma lem3851146 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3851147 : term351 = term343.
Proof. exact (MK_COMB (@lem3851146) (@lem3851145)). Qed.
Lemma lem3851148 : term352 = term345.
Proof. exact (MK_COMB (@lem3851147) (@lem3851135)). Qed.
Lemma lem3851150 (m : nat) : (term353 m) = term114.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3851151 : term345 = term114.
Proof. exact (@lem3851150 term129). Qed.
Lemma lem3851152 : term352 = term114.
Proof. exact (TRANS (@lem3851148) (@lem3851151)). Qed.
Lemma lem3851153 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3851154 : term354 = term355.
Proof. exact (MK_COMB (@lem3851153) (@lem3851152)). Qed.
Lemma lem3851155 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem3851156 : term356 = term314.
Proof. exact (MK_COMB (@lem3851154) (@lem3851155)). Qed.
Lemma lem3851158 (x : nat) : (term313 x) = term114.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3851159 : term314 = term114.
Proof. exact (@lem3851158 term129). Qed.
Lemma lem3851160 : term356 = term114.
Proof. exact (TRANS (@lem3851156) (@lem3851159)). Qed.
Lemma lem3851162 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3851163 : term172 = term173.
Proof. exact (@lem3851162 term129 term129). Qed.
Lemma lem3851164 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3851165 : term175 = term129.
Proof. exact (EQ_MP (@lem3851164) (@lem940073)). Qed.
Lemma lem3851166 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3851167 : term173 = term128.
Proof. exact (MK_COMB (@lem3851166) (@lem3851165)). Qed.
Lemma lem3851168 : term172 = term128.
Proof. exact (TRANS (@lem3851163) (@lem3851167)). Qed.
Lemma lem3851169 : term355 = term355.
Proof. exact (eq_refl term355). Qed.
Lemma lem3851170 : term357 = term314.
Proof. exact (MK_COMB (@lem3851169) (@lem3851168)). Qed.
Lemma lem3851172 (x : nat) : (term313 x) = term114.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3851173 : term314 = term114.
Proof. exact (@lem3851172 term129). Qed.
Lemma lem3851174 : term357 = term114.
Proof. exact (TRANS (@lem3851170) (@lem3851173)). Qed.
Lemma lem3851175 : term114 = term357.
Proof. exact (SYM (@lem3851174)). Qed.
Lemma lem3851176 : term356 = term357.
Proof. exact (TRANS (@lem3851160) (@lem3851175)). Qed.
Lemma lem3851177 : term346 = term160.
Proof. exact (@lem3851127 (@lem3851176)). Qed.
Lemma lem3851178 : term345 = term160.
Proof. exact (TRANS (@lem3851093) (@lem3851177)). Qed.
Lemma lem3851180 (x : real) : (term179 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3851181 : term160 = term114.
Proof. exact (@lem3851180 term114). Qed.
Lemma lem3851182 : term345 = term114.
Proof. exact (TRANS (@lem3851178) (@lem3851181)). Qed.
Lemma lem3851183 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3851184 : term358 = term355.
Proof. exact (MK_COMB (@lem3851183) (@lem3851182)). Qed.
Lemma lem3851185 (_44735 : int) : (real_of_int _44735) = (real_of_int _44735).
Proof. exact (eq_refl (real_of_int _44735)). Qed.
Lemma lem3851186 (_44735 : int) : (term342 _44735) = (term359 _44735).
Proof. exact (MK_COMB (@lem3851184) (@lem3851185 _44735)). Qed.
Lemma lem3851187 (_44735 : int) : (term341 _44735) = (term359 _44735).
Proof. exact (TRANS (@lem3851084 _44735) (@lem3851186 _44735)). Qed.
Lemma lem3851188 (_44735 : int) : (term359 _44735) = term114.
Proof. exact (@lem1982719 (real_of_int _44735)). Qed.
Lemma lem3851189 (_44735 : int) : (term341 _44735) = term114.
Proof. exact (TRANS (@lem3851187 _44735) (@lem3851188 _44735)). Qed.
Lemma lem3851190 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3851191 (_44735 : int) : (term360 _44735) = term361.
Proof. exact (MK_COMB (@lem3851190) (@lem3851189 _44735)). Qed.
Lemma lem3851192 (_44736 : int) (_44737 : int) : (term362 _44736 _44737) = (term363 _44736 _44737).
Proof. exact (@lem1982763 (term190 _44736) (real_of_int _44736) (term190 _44737)). Qed.
Lemma lem3851193 (_44736 : int) : (term364 _44736) = (term342 _44736).
Proof. exact (@lem1982713 term163 (real_of_int _44736)). Qed.
Lemma lem3851195 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3851196 : term128 = term198.
Proof. exact (@lem3851195 term129). Qed.
Lemma lem3851198 (x : nat) : (term161 x) = (term162 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3851199 : term163 = term164.
Proof. exact (@lem3851198 term129). Qed.
Lemma lem3851200 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3851201 : term343 = term344.
Proof. exact (MK_COMB (@lem3851200) (@lem3851199)). Qed.
Lemma lem3851202 : term345 = term346.
Proof. exact (MK_COMB (@lem3851201) (@lem3851196)). Qed.
Lemma lem3851203 : term347.
Proof. exact (@lem1981473 term163 term128 term128 term128 term114 term128). Qed.
Lemma lem3851205 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3851206 : term303 = term309.
Proof. exact (@lem3851205 (NUMERAL 0) term129). Qed.
Lemma lem3851207 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3851208 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3851209 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3851208 h1) (fun h1 : term309 = True => @lem3851207)). Qed.
Lemma lem3851210 : term309 = True.
Proof. exact (EQ_MP (@lem3851209) (@lem3851207)). Qed.
Lemma lem3851211 : term303 = True.
Proof. exact (TRANS (@lem3851206) (@lem3851210)). Qed.
Lemma lem3851212 : True = term303.
Proof. exact (SYM (@lem3851211)). Qed.
Lemma lem3851213 : term303.
Proof. exact (EQ_MP (@lem3851212) (@lem0)). Qed.
Lemma lem3851214 : term348.
Proof. exact (@lem3851203 (@lem3851213)). Qed.
Lemma lem3851216 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3851217 : term303 = term309.
Proof. exact (@lem3851216 (NUMERAL 0) term129). Qed.
Lemma lem3851218 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3851219 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3851220 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3851219 h1) (fun h1 : term309 = True => @lem3851218)). Qed.
Lemma lem3851221 : term309 = True.
Proof. exact (EQ_MP (@lem3851220) (@lem3851218)). Qed.
Lemma lem3851222 : term303 = True.
Proof. exact (TRANS (@lem3851217) (@lem3851221)). Qed.
Lemma lem3851223 : True = term303.
Proof. exact (SYM (@lem3851222)). Qed.
Lemma lem3851224 : term303.
Proof. exact (EQ_MP (@lem3851223) (@lem0)). Qed.
Lemma lem3851225 : term349.
Proof. exact (@lem3851214 (@lem3851224)). Qed.
Lemma lem3851227 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3851228 : term303 = term309.
Proof. exact (@lem3851227 (NUMERAL 0) term129). Qed.
Lemma lem3851229 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3851230 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3851231 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3851230 h1) (fun h1 : term309 = True => @lem3851229)). Qed.
Lemma lem3851232 : term309 = True.
Proof. exact (EQ_MP (@lem3851231) (@lem3851229)). Qed.
Lemma lem3851233 : term303 = True.
Proof. exact (TRANS (@lem3851228) (@lem3851232)). Qed.
Lemma lem3851234 : True = term303.
Proof. exact (SYM (@lem3851233)). Qed.
Lemma lem3851235 : term303.
Proof. exact (EQ_MP (@lem3851234) (@lem0)). Qed.
Lemma lem3851236 : term350.
Proof. exact (@lem3851225 (@lem3851235)). Qed.
Lemma lem3851238 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3851239 : term172 = term173.
Proof. exact (@lem3851238 term129 term129). Qed.
Lemma lem3851240 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3851241 : term175 = term129.
Proof. exact (EQ_MP (@lem3851240) (@lem940073)). Qed.
Lemma lem3851242 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3851243 : term173 = term128.
Proof. exact (MK_COMB (@lem3851242) (@lem3851241)). Qed.
Lemma lem3851244 : term172 = term128.
Proof. exact (TRANS (@lem3851239) (@lem3851243)). Qed.
Lemma lem3851246 (m : nat) (n : nat) : (term202 m n) = (term203 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3851247 : term199 = term204.
Proof. exact (@lem3851246 term129 term129). Qed.
Lemma lem3851248 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3851249 : term175 = term129.
Proof. exact (EQ_MP (@lem3851248) (@lem940073)). Qed.
Lemma lem3851250 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3851251 : term173 = term128.
Proof. exact (MK_COMB (@lem3851250) (@lem3851249)). Qed.
Lemma lem3851252 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3851253 : term204 = term163.
Proof. exact (MK_COMB (@lem3851252) (@lem3851251)). Qed.
Lemma lem3851254 : term199 = term163.
Proof. exact (TRANS (@lem3851247) (@lem3851253)). Qed.
Lemma lem3851255 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3851256 : term351 = term343.
Proof. exact (MK_COMB (@lem3851255) (@lem3851254)). Qed.
Lemma lem3851257 : term352 = term345.
Proof. exact (MK_COMB (@lem3851256) (@lem3851244)). Qed.
Lemma lem3851259 (m : nat) : (term353 m) = term114.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3851260 : term345 = term114.
Proof. exact (@lem3851259 term129). Qed.
Lemma lem3851261 : term352 = term114.
Proof. exact (TRANS (@lem3851257) (@lem3851260)). Qed.
Lemma lem3851262 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3851263 : term354 = term355.
Proof. exact (MK_COMB (@lem3851262) (@lem3851261)). Qed.
Lemma lem3851264 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem3851265 : term356 = term314.
Proof. exact (MK_COMB (@lem3851263) (@lem3851264)). Qed.
Lemma lem3851267 (x : nat) : (term313 x) = term114.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3851268 : term314 = term114.
Proof. exact (@lem3851267 term129). Qed.
Lemma lem3851269 : term356 = term114.
Proof. exact (TRANS (@lem3851265) (@lem3851268)). Qed.
Lemma lem3851271 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3851272 : term172 = term173.
Proof. exact (@lem3851271 term129 term129). Qed.
Lemma lem3851273 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3851274 : term175 = term129.
Proof. exact (EQ_MP (@lem3851273) (@lem940073)). Qed.
Lemma lem3851275 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3851276 : term173 = term128.
Proof. exact (MK_COMB (@lem3851275) (@lem3851274)). Qed.
Lemma lem3851277 : term172 = term128.
Proof. exact (TRANS (@lem3851272) (@lem3851276)). Qed.
Lemma lem3851278 : term355 = term355.
Proof. exact (eq_refl term355). Qed.
Lemma lem3851279 : term357 = term314.
Proof. exact (MK_COMB (@lem3851278) (@lem3851277)). Qed.
Lemma lem3851281 (x : nat) : (term313 x) = term114.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3851282 : term314 = term114.
Proof. exact (@lem3851281 term129). Qed.
Lemma lem3851283 : term357 = term114.
Proof. exact (TRANS (@lem3851279) (@lem3851282)). Qed.
Lemma lem3851284 : term114 = term357.
Proof. exact (SYM (@lem3851283)). Qed.
Lemma lem3851285 : term356 = term357.
Proof. exact (TRANS (@lem3851269) (@lem3851284)). Qed.
Lemma lem3851286 : term346 = term160.
Proof. exact (@lem3851236 (@lem3851285)). Qed.
Lemma lem3851287 : term345 = term160.
Proof. exact (TRANS (@lem3851202) (@lem3851286)). Qed.
Lemma lem3851289 (x : real) : (term179 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3851290 : term160 = term114.
Proof. exact (@lem3851289 term114). Qed.
Lemma lem3851291 : term345 = term114.
Proof. exact (TRANS (@lem3851287) (@lem3851290)). Qed.
Lemma lem3851292 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3851293 : term358 = term355.
Proof. exact (MK_COMB (@lem3851292) (@lem3851291)). Qed.
Lemma lem3851294 (_44736 : int) : (real_of_int _44736) = (real_of_int _44736).
Proof. exact (eq_refl (real_of_int _44736)). Qed.
Lemma lem3851295 (_44736 : int) : (term342 _44736) = (term359 _44736).
Proof. exact (MK_COMB (@lem3851293) (@lem3851294 _44736)). Qed.
Lemma lem3851296 (_44736 : int) : (term364 _44736) = (term359 _44736).
Proof. exact (TRANS (@lem3851193 _44736) (@lem3851295 _44736)). Qed.
Lemma lem3851297 (_44736 : int) : (term359 _44736) = term114.
Proof. exact (@lem1982719 (real_of_int _44736)). Qed.
Lemma lem3851298 (_44736 : int) : (term364 _44736) = term114.
Proof. exact (TRANS (@lem3851296 _44736) (@lem3851297 _44736)). Qed.
Lemma lem3851299 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3851300 (_44736 : int) : (term365 _44736) = term361.
Proof. exact (MK_COMB (@lem3851299) (@lem3851298 _44736)). Qed.
Lemma lem3851301 (_44737 : int) : (term190 _44737) = (term190 _44737).
Proof. exact (eq_refl (term190 _44737)). Qed.
Lemma lem3851302 (_44736 : int) (_44737 : int) : (term363 _44736 _44737) = (term366 _44737).
Proof. exact (MK_COMB (@lem3851300 _44736) (@lem3851301 _44737)). Qed.
Lemma lem3851303 (_44736 : int) (_44737 : int) : (term362 _44736 _44737) = (term366 _44737).
Proof. exact (TRANS (@lem3851192 _44736 _44737) (@lem3851302 _44736 _44737)). Qed.
Lemma lem3851304 (_44737 : int) : (term366 _44737) = (term190 _44737).
Proof. exact (@lem1982721 (term190 _44737)). Qed.
Lemma lem3851305 (_44736 : int) (_44737 : int) : (term362 _44736 _44737) = (term190 _44737).
Proof. exact (TRANS (@lem3851303 _44736 _44737) (@lem3851304 _44737)). Qed.
Lemma lem3851306 (_44735 : int) (_44736 : int) (_44737 : int) : (term340 _44735 _44736 _44737) = (term366 _44737).
Proof. exact (MK_COMB (@lem3851191 _44735) (@lem3851305 _44736 _44737)). Qed.
Lemma lem3851307 (_44735 : int) (_44736 : int) (_44737 : int) : (term339 _44735 _44736 _44737) = (term366 _44737).
Proof. exact (TRANS (@lem3851083 _44735 _44736 _44737) (@lem3851306 _44735 _44736 _44737)). Qed.
Lemma lem3851308 (_44737 : int) : (term366 _44737) = (term190 _44737).
Proof. exact (@lem1982721 (term190 _44737)). Qed.
Lemma lem3851309 (_44735 : int) (_44736 : int) (_44737 : int) : (term339 _44735 _44736 _44737) = (term190 _44737).
Proof. exact (TRANS (@lem3851307 _44735 _44736 _44737) (@lem3851308 _44737)). Qed.
Lemma lem3851310 (_44734 : int) : (term130 _44734) = (term130 _44734).
Proof. exact (eq_refl (term130 _44734)). Qed.
Lemma lem3851311 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term337 _44734 _44735 _44736 _44737) = (term338 _44734 _44737).
Proof. exact (MK_COMB (@lem3851310 _44734) (@lem3851309 _44735 _44736 _44737)). Qed.
Lemma lem3851312 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term336 _44734 _44735 _44736 _44737) = (term338 _44734 _44737).
Proof. exact (TRANS (@lem3851082 _44734 _44735 _44736 _44737) (@lem3851311 _44735 _44736 _44734 _44737)). Qed.
Lemma lem3851313 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3851314 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term367 _44734 _44735 _44736 _44737) = (term368 _44734 _44737).
Proof. exact (MK_COMB (@lem3851313) (@lem3851312 _44735 _44736 _44734 _44737)). Qed.
Lemma lem3851315 : term114 = term114.
Proof. exact (eq_refl term114). Qed.
Lemma lem3851316 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : ((term336 _44734 _44735 _44736 _44737) = term114) = ((term338 _44734 _44737) = term114).
Proof. exact (MK_COMB (@lem3851314 _44735 _44736 _44734 _44737) (@lem3851315)). Qed.
Lemma lem3851317 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term426 _44735 _44736 _44734 _44737) : (term338 _44734 _44737) = term114.
Proof. exact (EQ_MP (@lem3851316 _44735 _44736 _44734 _44737) (@lem3851081 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3851319 (y : real) : term327 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem3851320 (_44734 : int) (_44737 : int) : term369 _44734 _44737.
Proof. exact (@lem3851319 (term338 _44734 _44737)). Qed.
Lemma lem3851321 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term426 _44735 _44736 _44734 _44737) : term370 _44734 _44737.
Proof. exact (@lem3851320 _44734 _44737 (@lem3851317 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3851322 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term426 _44735 _44736 _44734 _44737) : term432 _44734 _44737.
Proof. exact (@lem3851321 _44735 _44736 _44734 _44737 h1 term163). Qed.
Lemma lem3851323 (_44734 : int) (_44737 : int) : (term432 _44734 _44737) = ((term433 _44734 _44737) = term114).
Proof. exact (eq_refl (term432 _44734 _44737)). Qed.
Lemma lem3851324 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term426 _44735 _44736 _44734 _44737) : (term433 _44734 _44737) = term114.
Proof. exact (EQ_MP (@lem3851323 _44734 _44737) (@lem3851322 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3851325 (_44734 : int) (_44737 : int) : (term433 _44734 _44737) = (term434 _44734 _44737).
Proof. exact (@lem1982781 (real_of_int _44734) term163 (term190 _44737)). Qed.
Lemma lem3851326 (_44737 : int) : (term435 _44737) = (term436 _44737).
Proof. exact (@lem1982749 term163 term163 (real_of_int _44737)). Qed.
Lemma lem3851328 (x : nat) : (term161 x) = (term162 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3851329 : term163 = term164.
Proof. exact (@lem3851328 term129). Qed.
Lemma lem3851331 (x : nat) : (term161 x) = (term162 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3851332 : term163 = term164.
Proof. exact (@lem3851331 term129). Qed.
Lemma lem3851333 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3851334 : term165 = term166.
Proof. exact (MK_COMB (@lem3851333) (@lem3851332)). Qed.
Lemma lem3851335 : term437 = term438.
Proof. exact (MK_COMB (@lem3851334) (@lem3851329)). Qed.
Lemma lem3851336 : term438 = term439.
Proof. exact (@lem1981613 term163 term163 term128 term128). Qed.
Lemma lem3851338 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3851339 : term172 = term173.
Proof. exact (@lem3851338 term129 term129). Qed.
Lemma lem3851340 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3851341 : term175 = term129.
Proof. exact (EQ_MP (@lem3851340) (@lem940073)). Qed.
Lemma lem3851342 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3851343 : term173 = term128.
Proof. exact (MK_COMB (@lem3851342) (@lem3851341)). Qed.
Lemma lem3851344 : term172 = term128.
Proof. exact (TRANS (@lem3851339) (@lem3851343)). Qed.
Lemma lem3851346 (m : nat) (n : nat) : (term440 m n) = (term171 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem3851347 : term437 = term173.
Proof. exact (@lem3851346 term129 term129). Qed.
Lemma lem3851348 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3851349 : term175 = term129.
Proof. exact (EQ_MP (@lem3851348) (@lem940073)). Qed.
Lemma lem3851350 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3851351 : term173 = term128.
Proof. exact (MK_COMB (@lem3851350) (@lem3851349)). Qed.
Lemma lem3851352 : term437 = term128.
Proof. exact (TRANS (@lem3851347) (@lem3851351)). Qed.
Lemma lem3851353 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3851354 : term441 = term442.
Proof. exact (MK_COMB (@lem3851353) (@lem3851352)). Qed.
Lemma lem3851355 : term439 = term198.
Proof. exact (MK_COMB (@lem3851354) (@lem3851344)). Qed.
Lemma lem3851356 : term438 = term198.
Proof. exact (TRANS (@lem3851336) (@lem3851355)). Qed.
Lemma lem3851357 : term437 = term198.
Proof. exact (TRANS (@lem3851335) (@lem3851356)). Qed.
Lemma lem3851359 (x : real) : (term179 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3851360 : term198 = term128.
Proof. exact (@lem3851359 term128). Qed.
Lemma lem3851361 : term437 = term128.
Proof. exact (TRANS (@lem3851357) (@lem3851360)). Qed.
Lemma lem3851362 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3851363 : term443 = term444.
Proof. exact (MK_COMB (@lem3851362) (@lem3851361)). Qed.
Lemma lem3851364 (_44737 : int) : (real_of_int _44737) = (real_of_int _44737).
Proof. exact (eq_refl (real_of_int _44737)). Qed.
Lemma lem3851365 (_44737 : int) : (term436 _44737) = (term402 _44737).
Proof. exact (MK_COMB (@lem3851363) (@lem3851364 _44737)). Qed.
Lemma lem3851366 (_44737 : int) : (term435 _44737) = (term402 _44737).
Proof. exact (TRANS (@lem3851326 _44737) (@lem3851365 _44737)). Qed.
Lemma lem3851367 (_44737 : int) : (term402 _44737) = (real_of_int _44737).
Proof. exact (@lem1982709 (real_of_int _44737)). Qed.
Lemma lem3851368 (_44737 : int) : (term435 _44737) = (real_of_int _44737).
Proof. exact (TRANS (@lem3851366 _44737) (@lem3851367 _44737)). Qed.
Lemma lem3851371 (_44734 : int) : (term207 _44734) = (term207 _44734).
Proof. exact (eq_refl (term207 _44734)). Qed.
Lemma lem3851372 (_44734 : int) (_44737 : int) : (term434 _44734 _44737) = (term445 _44734 _44737).
Proof. exact (MK_COMB (@lem3851371 _44734) (@lem3851368 _44737)). Qed.
Lemma lem3851373 (_44734 : int) (_44737 : int) : (term433 _44734 _44737) = (term445 _44734 _44737).
Proof. exact (TRANS (@lem3851325 _44734 _44737) (@lem3851372 _44734 _44737)). Qed.
Lemma lem3851374 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3851375 (_44734 : int) (_44737 : int) : (term446 _44734 _44737) = (term447 _44734 _44737).
Proof. exact (MK_COMB (@lem3851374) (@lem3851373 _44734 _44737)). Qed.
Lemma lem3851376 : term114 = term114.
Proof. exact (eq_refl term114). Qed.
Lemma lem3851377 (_44734 : int) (_44737 : int) : ((term433 _44734 _44737) = term114) = ((term445 _44734 _44737) = term114).
Proof. exact (MK_COMB (@lem3851375 _44734 _44737) (@lem3851376)). Qed.
Lemma lem3851378 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term426 _44735 _44736 _44734 _44737) : (term445 _44734 _44737) = term114.
Proof. exact (EQ_MP (@lem3851377 _44734 _44737) (@lem3851324 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3851379 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term426 _44735 _44736 _44734 _44737) : term448 _44734 _44737.
Proof. exact (conj (@lem3851378 _44735 _44736 _44734 _44737 h1) (@lem3850989 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3851381 (x : real) (y : real) : term375 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem3851382 (_44734 : int) (_44737 : int) : term449 _44734 _44737.
Proof. exact (@lem3851381 (term445 _44734 _44737) (term209 _44734 _44737)). Qed.
Lemma lem3851383 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term426 _44735 _44736 _44734 _44737) : term450 _44734 _44737.
Proof. exact (@lem3851382 _44734 _44737 (@lem3851379 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3851384 (_44734 : int) (_44737 : int) : (term451 _44734 _44737) = (term452 _44734 _44737).
Proof. exact (@lem1982753 (term190 _44734) (real_of_int _44734) (real_of_int _44737) (term208 _44737)). Qed.
Lemma lem3851385 (_44734 : int) : (term364 _44734) = (term342 _44734).
Proof. exact (@lem1982713 term163 (real_of_int _44734)). Qed.
Lemma lem3851387 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3851388 : term128 = term198.
Proof. exact (@lem3851387 term129). Qed.
Lemma lem3851390 (x : nat) : (term161 x) = (term162 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3851391 : term163 = term164.
Proof. exact (@lem3851390 term129). Qed.
Lemma lem3851392 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3851393 : term343 = term344.
Proof. exact (MK_COMB (@lem3851392) (@lem3851391)). Qed.
Lemma lem3851394 : term345 = term346.
Proof. exact (MK_COMB (@lem3851393) (@lem3851388)). Qed.
Lemma lem3851395 : term347.
Proof. exact (@lem1981473 term163 term128 term128 term128 term114 term128). Qed.
Lemma lem3851397 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3851398 : term303 = term309.
Proof. exact (@lem3851397 (NUMERAL 0) term129). Qed.
Lemma lem3851399 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3851400 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3851401 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3851400 h1) (fun h1 : term309 = True => @lem3851399)). Qed.
Lemma lem3851402 : term309 = True.
Proof. exact (EQ_MP (@lem3851401) (@lem3851399)). Qed.
Lemma lem3851403 : term303 = True.
Proof. exact (TRANS (@lem3851398) (@lem3851402)). Qed.
Lemma lem3851404 : True = term303.
Proof. exact (SYM (@lem3851403)). Qed.
Lemma lem3851405 : term303.
Proof. exact (EQ_MP (@lem3851404) (@lem0)). Qed.
Lemma lem3851406 : term348.
Proof. exact (@lem3851395 (@lem3851405)). Qed.
Lemma lem3851408 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3851409 : term303 = term309.
Proof. exact (@lem3851408 (NUMERAL 0) term129). Qed.
Lemma lem3851410 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3851411 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3851412 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3851411 h1) (fun h1 : term309 = True => @lem3851410)). Qed.
Lemma lem3851413 : term309 = True.
Proof. exact (EQ_MP (@lem3851412) (@lem3851410)). Qed.
Lemma lem3851414 : term303 = True.
Proof. exact (TRANS (@lem3851409) (@lem3851413)). Qed.
Lemma lem3851415 : True = term303.
Proof. exact (SYM (@lem3851414)). Qed.
Lemma lem3851416 : term303.
Proof. exact (EQ_MP (@lem3851415) (@lem0)). Qed.
Lemma lem3851417 : term349.
Proof. exact (@lem3851406 (@lem3851416)). Qed.
Lemma lem3851419 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3851420 : term303 = term309.
Proof. exact (@lem3851419 (NUMERAL 0) term129). Qed.
Lemma lem3851421 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3851422 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3851423 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3851422 h1) (fun h1 : term309 = True => @lem3851421)). Qed.
Lemma lem3851424 : term309 = True.
Proof. exact (EQ_MP (@lem3851423) (@lem3851421)). Qed.
Lemma lem3851425 : term303 = True.
Proof. exact (TRANS (@lem3851420) (@lem3851424)). Qed.
Lemma lem3851426 : True = term303.
Proof. exact (SYM (@lem3851425)). Qed.
Lemma lem3851427 : term303.
Proof. exact (EQ_MP (@lem3851426) (@lem0)). Qed.
Lemma lem3851428 : term350.
Proof. exact (@lem3851417 (@lem3851427)). Qed.
Lemma lem3851430 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3851431 : term172 = term173.
Proof. exact (@lem3851430 term129 term129). Qed.
Lemma lem3851432 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3851433 : term175 = term129.
Proof. exact (EQ_MP (@lem3851432) (@lem940073)). Qed.
Lemma lem3851434 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3851435 : term173 = term128.
Proof. exact (MK_COMB (@lem3851434) (@lem3851433)). Qed.
Lemma lem3851436 : term172 = term128.
Proof. exact (TRANS (@lem3851431) (@lem3851435)). Qed.
Lemma lem3851438 (m : nat) (n : nat) : (term202 m n) = (term203 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3851439 : term199 = term204.
Proof. exact (@lem3851438 term129 term129). Qed.
Lemma lem3851440 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3851441 : term175 = term129.
Proof. exact (EQ_MP (@lem3851440) (@lem940073)). Qed.
Lemma lem3851442 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3851443 : term173 = term128.
Proof. exact (MK_COMB (@lem3851442) (@lem3851441)). Qed.
Lemma lem3851444 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3851445 : term204 = term163.
Proof. exact (MK_COMB (@lem3851444) (@lem3851443)). Qed.
Lemma lem3851446 : term199 = term163.
Proof. exact (TRANS (@lem3851439) (@lem3851445)). Qed.
Lemma lem3851447 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3851448 : term351 = term343.
Proof. exact (MK_COMB (@lem3851447) (@lem3851446)). Qed.
Lemma lem3851449 : term352 = term345.
Proof. exact (MK_COMB (@lem3851448) (@lem3851436)). Qed.
Lemma lem3851451 (m : nat) : (term353 m) = term114.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3851452 : term345 = term114.
Proof. exact (@lem3851451 term129). Qed.
Lemma lem3851453 : term352 = term114.
Proof. exact (TRANS (@lem3851449) (@lem3851452)). Qed.
Lemma lem3851454 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3851455 : term354 = term355.
Proof. exact (MK_COMB (@lem3851454) (@lem3851453)). Qed.
Lemma lem3851456 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem3851457 : term356 = term314.
Proof. exact (MK_COMB (@lem3851455) (@lem3851456)). Qed.
Lemma lem3851459 (x : nat) : (term313 x) = term114.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3851460 : term314 = term114.
Proof. exact (@lem3851459 term129). Qed.
Lemma lem3851461 : term356 = term114.
Proof. exact (TRANS (@lem3851457) (@lem3851460)). Qed.
Lemma lem3851463 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3851464 : term172 = term173.
Proof. exact (@lem3851463 term129 term129). Qed.
Lemma lem3851465 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3851466 : term175 = term129.
Proof. exact (EQ_MP (@lem3851465) (@lem940073)). Qed.
Lemma lem3851467 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3851468 : term173 = term128.
Proof. exact (MK_COMB (@lem3851467) (@lem3851466)). Qed.
Lemma lem3851469 : term172 = term128.
Proof. exact (TRANS (@lem3851464) (@lem3851468)). Qed.
Lemma lem3851470 : term355 = term355.
Proof. exact (eq_refl term355). Qed.
Lemma lem3851471 : term357 = term314.
Proof. exact (MK_COMB (@lem3851470) (@lem3851469)). Qed.
Lemma lem3851473 (x : nat) : (term313 x) = term114.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3851474 : term314 = term114.
Proof. exact (@lem3851473 term129). Qed.
Lemma lem3851475 : term357 = term114.
Proof. exact (TRANS (@lem3851471) (@lem3851474)). Qed.
Lemma lem3851476 : term114 = term357.
Proof. exact (SYM (@lem3851475)). Qed.
Lemma lem3851477 : term356 = term357.
Proof. exact (TRANS (@lem3851461) (@lem3851476)). Qed.
Lemma lem3851478 : term346 = term160.
Proof. exact (@lem3851428 (@lem3851477)). Qed.
Lemma lem3851479 : term345 = term160.
Proof. exact (TRANS (@lem3851394) (@lem3851478)). Qed.
Lemma lem3851481 (x : real) : (term179 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3851482 : term160 = term114.
Proof. exact (@lem3851481 term114). Qed.
Lemma lem3851483 : term345 = term114.
Proof. exact (TRANS (@lem3851479) (@lem3851482)). Qed.
Lemma lem3851484 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3851485 : term358 = term355.
Proof. exact (MK_COMB (@lem3851484) (@lem3851483)). Qed.
Lemma lem3851486 (_44734 : int) : (real_of_int _44734) = (real_of_int _44734).
Proof. exact (eq_refl (real_of_int _44734)). Qed.
Lemma lem3851487 (_44734 : int) : (term342 _44734) = (term359 _44734).
Proof. exact (MK_COMB (@lem3851485) (@lem3851486 _44734)). Qed.
Lemma lem3851488 (_44734 : int) : (term364 _44734) = (term359 _44734).
Proof. exact (TRANS (@lem3851385 _44734) (@lem3851487 _44734)). Qed.
Lemma lem3851489 (_44734 : int) : (term359 _44734) = term114.
Proof. exact (@lem1982719 (real_of_int _44734)). Qed.
Lemma lem3851490 (_44734 : int) : (term364 _44734) = term114.
Proof. exact (TRANS (@lem3851488 _44734) (@lem3851489 _44734)). Qed.
Lemma lem3851491 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3851492 (_44734 : int) : (term365 _44734) = term361.
Proof. exact (MK_COMB (@lem3851491) (@lem3851490 _44734)). Qed.
Lemma lem3851493 (_44737 : int) : (term453 _44737) = (term454 _44737).
Proof. exact (@lem1982763 (real_of_int _44737) (term190 _44737) term163). Qed.
Lemma lem3851494 (_44737 : int) : (term341 _44737) = (term342 _44737).
Proof. exact (@lem1982715 term163 (real_of_int _44737)). Qed.
Lemma lem3851496 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3851497 : term128 = term198.
Proof. exact (@lem3851496 term129). Qed.
Lemma lem3851499 (x : nat) : (term161 x) = (term162 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3851500 : term163 = term164.
Proof. exact (@lem3851499 term129). Qed.
Lemma lem3851501 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3851502 : term343 = term344.
Proof. exact (MK_COMB (@lem3851501) (@lem3851500)). Qed.
Lemma lem3851503 : term345 = term346.
Proof. exact (MK_COMB (@lem3851502) (@lem3851497)). Qed.
Lemma lem3851504 : term347.
Proof. exact (@lem1981473 term163 term128 term128 term128 term114 term128). Qed.
Lemma lem3851506 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3851507 : term303 = term309.
Proof. exact (@lem3851506 (NUMERAL 0) term129). Qed.
Lemma lem3851508 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3851509 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3851510 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3851509 h1) (fun h1 : term309 = True => @lem3851508)). Qed.
Lemma lem3851511 : term309 = True.
Proof. exact (EQ_MP (@lem3851510) (@lem3851508)). Qed.
Lemma lem3851512 : term303 = True.
Proof. exact (TRANS (@lem3851507) (@lem3851511)). Qed.
Lemma lem3851513 : True = term303.
Proof. exact (SYM (@lem3851512)). Qed.
Lemma lem3851514 : term303.
Proof. exact (EQ_MP (@lem3851513) (@lem0)). Qed.
Lemma lem3851515 : term348.
Proof. exact (@lem3851504 (@lem3851514)). Qed.
Lemma lem3851517 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3851518 : term303 = term309.
Proof. exact (@lem3851517 (NUMERAL 0) term129). Qed.
Lemma lem3851519 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3851520 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3851521 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3851520 h1) (fun h1 : term309 = True => @lem3851519)). Qed.
Lemma lem3851522 : term309 = True.
Proof. exact (EQ_MP (@lem3851521) (@lem3851519)). Qed.
Lemma lem3851523 : term303 = True.
Proof. exact (TRANS (@lem3851518) (@lem3851522)). Qed.
Lemma lem3851524 : True = term303.
Proof. exact (SYM (@lem3851523)). Qed.
Lemma lem3851525 : term303.
Proof. exact (EQ_MP (@lem3851524) (@lem0)). Qed.
Lemma lem3851526 : term349.
Proof. exact (@lem3851515 (@lem3851525)). Qed.
Lemma lem3851528 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3851529 : term303 = term309.
Proof. exact (@lem3851528 (NUMERAL 0) term129). Qed.
Lemma lem3851530 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3851531 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3851532 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3851531 h1) (fun h1 : term309 = True => @lem3851530)). Qed.
Lemma lem3851533 : term309 = True.
Proof. exact (EQ_MP (@lem3851532) (@lem3851530)). Qed.
Lemma lem3851534 : term303 = True.
Proof. exact (TRANS (@lem3851529) (@lem3851533)). Qed.
Lemma lem3851535 : True = term303.
Proof. exact (SYM (@lem3851534)). Qed.
Lemma lem3851536 : term303.
Proof. exact (EQ_MP (@lem3851535) (@lem0)). Qed.
Lemma lem3851537 : term350.
Proof. exact (@lem3851526 (@lem3851536)). Qed.
Lemma lem3851539 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3851540 : term172 = term173.
Proof. exact (@lem3851539 term129 term129). Qed.
Lemma lem3851541 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3851542 : term175 = term129.
Proof. exact (EQ_MP (@lem3851541) (@lem940073)). Qed.
Lemma lem3851543 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3851544 : term173 = term128.
Proof. exact (MK_COMB (@lem3851543) (@lem3851542)). Qed.
Lemma lem3851545 : term172 = term128.
Proof. exact (TRANS (@lem3851540) (@lem3851544)). Qed.
Lemma lem3851547 (m : nat) (n : nat) : (term202 m n) = (term203 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3851548 : term199 = term204.
Proof. exact (@lem3851547 term129 term129). Qed.
Lemma lem3851549 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3851550 : term175 = term129.
Proof. exact (EQ_MP (@lem3851549) (@lem940073)). Qed.
Lemma lem3851551 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3851552 : term173 = term128.
Proof. exact (MK_COMB (@lem3851551) (@lem3851550)). Qed.
Lemma lem3851553 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3851554 : term204 = term163.
Proof. exact (MK_COMB (@lem3851553) (@lem3851552)). Qed.
Lemma lem3851555 : term199 = term163.
Proof. exact (TRANS (@lem3851548) (@lem3851554)). Qed.
Lemma lem3851556 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3851557 : term351 = term343.
Proof. exact (MK_COMB (@lem3851556) (@lem3851555)). Qed.
Lemma lem3851558 : term352 = term345.
Proof. exact (MK_COMB (@lem3851557) (@lem3851545)). Qed.
Lemma lem3851560 (m : nat) : (term353 m) = term114.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3851561 : term345 = term114.
Proof. exact (@lem3851560 term129). Qed.
Lemma lem3851562 : term352 = term114.
Proof. exact (TRANS (@lem3851558) (@lem3851561)). Qed.
Lemma lem3851563 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3851564 : term354 = term355.
Proof. exact (MK_COMB (@lem3851563) (@lem3851562)). Qed.
Lemma lem3851565 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem3851566 : term356 = term314.
Proof. exact (MK_COMB (@lem3851564) (@lem3851565)). Qed.
Lemma lem3851568 (x : nat) : (term313 x) = term114.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3851569 : term314 = term114.
Proof. exact (@lem3851568 term129). Qed.
Lemma lem3851570 : term356 = term114.
Proof. exact (TRANS (@lem3851566) (@lem3851569)). Qed.
Lemma lem3851572 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3851573 : term172 = term173.
Proof. exact (@lem3851572 term129 term129). Qed.
Lemma lem3851574 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3851575 : term175 = term129.
Proof. exact (EQ_MP (@lem3851574) (@lem940073)). Qed.
Lemma lem3851576 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3851577 : term173 = term128.
Proof. exact (MK_COMB (@lem3851576) (@lem3851575)). Qed.
Lemma lem3851578 : term172 = term128.
Proof. exact (TRANS (@lem3851573) (@lem3851577)). Qed.
Lemma lem3851579 : term355 = term355.
Proof. exact (eq_refl term355). Qed.
Lemma lem3851580 : term357 = term314.
Proof. exact (MK_COMB (@lem3851579) (@lem3851578)). Qed.
Lemma lem3851582 (x : nat) : (term313 x) = term114.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3851583 : term314 = term114.
Proof. exact (@lem3851582 term129). Qed.
Lemma lem3851584 : term357 = term114.
Proof. exact (TRANS (@lem3851580) (@lem3851583)). Qed.
Lemma lem3851585 : term114 = term357.
Proof. exact (SYM (@lem3851584)). Qed.
Lemma lem3851586 : term356 = term357.
Proof. exact (TRANS (@lem3851570) (@lem3851585)). Qed.
Lemma lem3851587 : term346 = term160.
Proof. exact (@lem3851537 (@lem3851586)). Qed.
Lemma lem3851588 : term345 = term160.
Proof. exact (TRANS (@lem3851503) (@lem3851587)). Qed.
Lemma lem3851590 (x : real) : (term179 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3851591 : term160 = term114.
Proof. exact (@lem3851590 term114). Qed.
Lemma lem3851592 : term345 = term114.
Proof. exact (TRANS (@lem3851588) (@lem3851591)). Qed.
Lemma lem3851593 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3851594 : term358 = term355.
Proof. exact (MK_COMB (@lem3851593) (@lem3851592)). Qed.
Lemma lem3851595 (_44737 : int) : (real_of_int _44737) = (real_of_int _44737).
Proof. exact (eq_refl (real_of_int _44737)). Qed.
Lemma lem3851596 (_44737 : int) : (term342 _44737) = (term359 _44737).
Proof. exact (MK_COMB (@lem3851594) (@lem3851595 _44737)). Qed.
Lemma lem3851597 (_44737 : int) : (term341 _44737) = (term359 _44737).
Proof. exact (TRANS (@lem3851494 _44737) (@lem3851596 _44737)). Qed.
Lemma lem3851598 (_44737 : int) : (term359 _44737) = term114.
Proof. exact (@lem1982719 (real_of_int _44737)). Qed.
Lemma lem3851599 (_44737 : int) : (term341 _44737) = term114.
Proof. exact (TRANS (@lem3851597 _44737) (@lem3851598 _44737)). Qed.
Lemma lem3851600 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3851601 (_44737 : int) : (term360 _44737) = term361.
Proof. exact (MK_COMB (@lem3851600) (@lem3851599 _44737)). Qed.
Lemma lem3851602 : term163 = term163.
Proof. exact (eq_refl term163). Qed.
Lemma lem3851603 (_44737 : int) : (term454 _44737) = term383.
Proof. exact (MK_COMB (@lem3851601 _44737) (@lem3851602)). Qed.
Lemma lem3851604 (_44737 : int) : (term453 _44737) = term383.
Proof. exact (TRANS (@lem3851493 _44737) (@lem3851603 _44737)). Qed.
Lemma lem3851605 : term383 = term163.
Proof. exact (@lem1982721 term163). Qed.
Lemma lem3851606 (_44737 : int) : (term453 _44737) = term163.
Proof. exact (TRANS (@lem3851604 _44737) (@lem3851605)). Qed.
Lemma lem3851607 (_44734 : int) (_44737 : int) : (term452 _44734 _44737) = term383.
Proof. exact (MK_COMB (@lem3851492 _44734) (@lem3851606 _44737)). Qed.
Lemma lem3851608 (_44734 : int) (_44737 : int) : (term451 _44734 _44737) = term383.
Proof. exact (TRANS (@lem3851384 _44734 _44737) (@lem3851607 _44734 _44737)). Qed.
Lemma lem3851609 : term383 = term163.
Proof. exact (@lem1982721 term163). Qed.
Lemma lem3851610 (_44734 : int) (_44737 : int) : (term451 _44734 _44737) = term163.
Proof. exact (TRANS (@lem3851608 _44734 _44737) (@lem3851609)). Qed.
Lemma lem3851611 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3851612 (_44734 : int) (_44737 : int) : (term455 _44734 _44737) = term385.
Proof. exact (MK_COMB (@lem3851611) (@lem3851610 _44734 _44737)). Qed.
Lemma lem3851613 : term114 = term114.
Proof. exact (eq_refl term114). Qed.
Lemma lem3851614 (_44734 : int) (_44737 : int) : (term450 _44734 _44737) = term386.
Proof. exact (MK_COMB (@lem3851612 _44734 _44737) (@lem3851613)). Qed.
Lemma lem3851615 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term426 _44735 _44736 _44734 _44737) : term386.
Proof. exact (EQ_MP (@lem3851614 _44734 _44737) (@lem3851383 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3851617 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3851618 : term386 = term387.
Proof. exact (@lem3851617 term114 term163). Qed.
Lemma lem3851620 (x : nat) : (term161 x) = (term162 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3851621 : term163 = term164.
Proof. exact (@lem3851620 term129). Qed.
Lemma lem3851623 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3851624 : term114 = term160.
Proof. exact (@lem3851623 (NUMERAL 0)). Qed.
Lemma lem3851625 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3851626 : term116 = term388.
Proof. exact (MK_COMB (@lem3851625) (@lem3851624)). Qed.
Lemma lem3851627 : term387 = term389.
Proof. exact (MK_COMB (@lem3851626) (@lem3851621)). Qed.
Lemma lem3851628 : term390.
Proof. exact (@lem1980026 term114 term128 term163 term128). Qed.
Lemma lem3851630 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3851631 : term303 = term309.
Proof. exact (@lem3851630 (NUMERAL 0) term129). Qed.
Lemma lem3851632 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3851633 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3851634 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3851633 h1) (fun h1 : term309 = True => @lem3851632)). Qed.
Lemma lem3851635 : term309 = True.
Proof. exact (EQ_MP (@lem3851634) (@lem3851632)). Qed.
Lemma lem3851636 : term303 = True.
Proof. exact (TRANS (@lem3851631) (@lem3851635)). Qed.
Lemma lem3851637 : True = term303.
Proof. exact (SYM (@lem3851636)). Qed.
Lemma lem3851638 : term303.
Proof. exact (EQ_MP (@lem3851637) (@lem0)). Qed.
Lemma lem3851639 : term391.
Proof. exact (@lem3851628 (@lem3851638)). Qed.
Lemma lem3851641 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3851642 : term303 = term309.
Proof. exact (@lem3851641 (NUMERAL 0) term129). Qed.
Lemma lem3851643 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3851644 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3851645 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3851644 h1) (fun h1 : term309 = True => @lem3851643)). Qed.
Lemma lem3851646 : term309 = True.
Proof. exact (EQ_MP (@lem3851645) (@lem3851643)). Qed.
Lemma lem3851647 : term303 = True.
Proof. exact (TRANS (@lem3851642) (@lem3851646)). Qed.
Lemma lem3851648 : True = term303.
Proof. exact (SYM (@lem3851647)). Qed.
Lemma lem3851649 : term303.
Proof. exact (EQ_MP (@lem3851648) (@lem0)). Qed.
Lemma lem3851650 : term389 = term392.
Proof. exact (@lem3851639 (@lem3851649)). Qed.
Lemma lem3851652 (m : nat) (n : nat) : (term202 m n) = (term203 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3851653 : term199 = term204.
Proof. exact (@lem3851652 term129 term129). Qed.
Lemma lem3851654 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3851655 : term175 = term129.
Proof. exact (EQ_MP (@lem3851654) (@lem940073)). Qed.
Lemma lem3851656 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3851657 : term173 = term128.
Proof. exact (MK_COMB (@lem3851656) (@lem3851655)). Qed.
Lemma lem3851658 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3851659 : term204 = term163.
Proof. exact (MK_COMB (@lem3851658) (@lem3851657)). Qed.
Lemma lem3851660 : term199 = term163.
Proof. exact (TRANS (@lem3851653) (@lem3851659)). Qed.
Lemma lem3851662 (x : nat) : (term313 x) = term114.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3851663 : term314 = term114.
Proof. exact (@lem3851662 term129). Qed.
Lemma lem3851664 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3851665 : term393 = term116.
Proof. exact (MK_COMB (@lem3851664) (@lem3851663)). Qed.
Lemma lem3851666 : term392 = term387.
Proof. exact (MK_COMB (@lem3851665) (@lem3851660)). Qed.
Lemma lem3851668 (m : nat) (n : nat) : (term394 m n) = (term395 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3851669 : term387 = term396.
Proof. exact (@lem3851668 (NUMERAL 0) term129). Qed.
Lemma lem3851670 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3851671 (h1 : term310 = (BIT1 0)) : (term129 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3851672 : (term310 = (BIT1 0)) = ((term129 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3851671 h1) (fun h1 : (term129 = (NUMERAL 0)) = False => @lem3851670)). Qed.
Lemma lem3851673 : (term129 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3851672) (@lem3851670)). Qed.
Lemma lem3851674 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3851675 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3851676 : term397 = (and True).
Proof. exact (MK_COMB (@lem3851675) (@lem3851674)). Qed.
Lemma lem3851677 : term396 = (True /\ False).
Proof. exact (MK_COMB (@lem3851676) (@lem3851673)). Qed.
Lemma lem3851679 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3851680 : term396 = False.
Proof. exact (TRANS (@lem3851677) (@lem3851679)). Qed.
Lemma lem3851681 : term387 = False.
Proof. exact (TRANS (@lem3851669) (@lem3851680)). Qed.
Lemma lem3851682 : term392 = False.
Proof. exact (TRANS (@lem3851666) (@lem3851681)). Qed.
Lemma lem3851683 : term389 = False.
Proof. exact (TRANS (@lem3851650) (@lem3851682)). Qed.
Lemma lem3851684 : term387 = False.
Proof. exact (TRANS (@lem3851627) (@lem3851683)). Qed.
Lemma lem3851685 : term386 = False.
Proof. exact (TRANS (@lem3851618) (@lem3851684)). Qed.
Lemma lem3851686 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term426 _44735 _44736 _44734 _44737) : False.
Proof. exact (EQ_MP (@lem3851685) (@lem3851615 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3851687 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term456 _44735 _44736 _44734 _44737) : term456 _44735 _44736 _44734 _44737.
Proof. exact (h1). Qed.
Lemma lem3851688 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term456 _44735 _44736 _44734 _44737) : term293 _44735 _44736 _44734 _44737.
Proof. exact (proj2 (@lem3851687 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3851690 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term456 _44735 _44736 _44734 _44737) : term280 _44735 _44736 _44734 _44737.
Proof. exact (proj2 (@lem3851688 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3851692 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term456 _44735 _44736 _44734 _44737) : term267 _44735 _44736 _44734 _44737.
Proof. exact (proj2 (@lem3851690 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3851694 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term456 _44735 _44736 _44734 _44737) : term254 _44735 _44736 _44734 _44737.
Proof. exact (proj2 (@lem3851692 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3851696 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term456 _44735 _44736 _44734 _44737) : term241 _44735 _44736 _44734 _44737.
Proof. exact (proj2 (@lem3851694 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3851697 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term456 _44735 _44736 _44734 _44737) : term215 _44735 _44736 _44737.
Proof. exact (proj1 (@lem3851694 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3851698 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term456 _44735 _44736 _44734 _44737) : (real_of_int _44737) = term114.
Proof. exact (proj2 (@lem3851697 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3851699 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term456 _44735 _44736 _44734 _44737) : term212 _44735 _44736.
Proof. exact (proj1 (@lem3851697 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3851700 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term456 _44735 _44736 _44734 _44737) : term212 _44734 _44737.
Proof. exact (proj2 (@lem3851696 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3851701 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term456 _44735 _44736 _44734 _44737) : (term220 _44734 _44735 _44736) = term114.
Proof. exact (proj1 (@lem3851696 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3851703 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3851704 : term302 = term303.
Proof. exact (@lem3851703 term114 term128). Qed.
Lemma lem3851706 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3851707 : term128 = term198.
Proof. exact (@lem3851706 term129). Qed.
Lemma lem3851709 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3851710 : term114 = term160.
Proof. exact (@lem3851709 (NUMERAL 0)). Qed.
Lemma lem3851711 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3851712 : term304 = term305.
Proof. exact (MK_COMB (@lem3851711) (@lem3851710)). Qed.
Lemma lem3851713 : term303 = term306.
Proof. exact (MK_COMB (@lem3851712) (@lem3851707)). Qed.
Lemma lem3851714 : term307.
Proof. exact (@lem1980255 term114 term128 term128 term128). Qed.
Lemma lem3851716 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3851717 : term303 = term309.
Proof. exact (@lem3851716 (NUMERAL 0) term129). Qed.
Lemma lem3851718 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3851719 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3851720 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3851719 h1) (fun h1 : term309 = True => @lem3851718)). Qed.
Lemma lem3851721 : term309 = True.
Proof. exact (EQ_MP (@lem3851720) (@lem3851718)). Qed.
Lemma lem3851722 : term303 = True.
Proof. exact (TRANS (@lem3851717) (@lem3851721)). Qed.
Lemma lem3851723 : True = term303.
Proof. exact (SYM (@lem3851722)). Qed.
Lemma lem3851724 : term303.
Proof. exact (EQ_MP (@lem3851723) (@lem0)). Qed.
Lemma lem3851725 : term311.
Proof. exact (@lem3851714 (@lem3851724)). Qed.
Lemma lem3851727 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3851728 : term303 = term309.
Proof. exact (@lem3851727 (NUMERAL 0) term129). Qed.
Lemma lem3851729 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3851730 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3851731 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3851730 h1) (fun h1 : term309 = True => @lem3851729)). Qed.
Lemma lem3851732 : term309 = True.
Proof. exact (EQ_MP (@lem3851731) (@lem3851729)). Qed.
Lemma lem3851733 : term303 = True.
Proof. exact (TRANS (@lem3851728) (@lem3851732)). Qed.
Lemma lem3851734 : True = term303.
Proof. exact (SYM (@lem3851733)). Qed.
Lemma lem3851735 : term303.
Proof. exact (EQ_MP (@lem3851734) (@lem0)). Qed.
Lemma lem3851736 : term306 = term312.
Proof. exact (@lem3851725 (@lem3851735)). Qed.
Lemma lem3851738 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3851739 : term172 = term173.
Proof. exact (@lem3851738 term129 term129). Qed.
Lemma lem3851740 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3851741 : term175 = term129.
Proof. exact (EQ_MP (@lem3851740) (@lem940073)). Qed.
Lemma lem3851742 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3851743 : term173 = term128.
Proof. exact (MK_COMB (@lem3851742) (@lem3851741)). Qed.
Lemma lem3851744 : term172 = term128.
Proof. exact (TRANS (@lem3851739) (@lem3851743)). Qed.
Lemma lem3851746 (x : nat) : (term313 x) = term114.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3851747 : term314 = term114.
Proof. exact (@lem3851746 term129). Qed.
Lemma lem3851748 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3851749 : term315 = term304.
Proof. exact (MK_COMB (@lem3851748) (@lem3851747)). Qed.
Lemma lem3851750 : term312 = term303.
Proof. exact (MK_COMB (@lem3851749) (@lem3851744)). Qed.
Lemma lem3851752 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3851753 : term303 = term309.
Proof. exact (@lem3851752 (NUMERAL 0) term129). Qed.
Lemma lem3851754 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3851755 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3851756 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3851755 h1) (fun h1 : term309 = True => @lem3851754)). Qed.
Lemma lem3851757 : term309 = True.
Proof. exact (EQ_MP (@lem3851756) (@lem3851754)). Qed.
Lemma lem3851758 : term303 = True.
Proof. exact (TRANS (@lem3851753) (@lem3851757)). Qed.
Lemma lem3851759 : term312 = True.
Proof. exact (TRANS (@lem3851750) (@lem3851758)). Qed.
Lemma lem3851760 : term306 = True.
Proof. exact (TRANS (@lem3851736) (@lem3851759)). Qed.
Lemma lem3851761 : term303 = True.
Proof. exact (TRANS (@lem3851713) (@lem3851760)). Qed.
Lemma lem3851762 : term302 = True.
Proof. exact (TRANS (@lem3851704) (@lem3851761)). Qed.
Lemma lem3851763 : True = term302.
Proof. exact (SYM (@lem3851762)). Qed.
Lemma lem3851764 : term302.
Proof. exact (EQ_MP (@lem3851763) (@lem0)). Qed.
Lemma lem3851765 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term456 _44735 _44736 _44734 _44737) : term427 _44734 _44737.
Proof. exact (conj (@lem3851764) (@lem3851700 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3851767 (x : real) (y : real) : term317 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3851768 (_44734 : int) (_44737 : int) : term428 _44734 _44737.
Proof. exact (@lem3851767 term128 (term209 _44734 _44737)). Qed.
Lemma lem3851769 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term456 _44735 _44736 _44734 _44737) : term429 _44734 _44737.
Proof. exact (@lem3851768 _44734 _44737 (@lem3851765 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3851770 (_44734 : int) (_44737 : int) : (term430 _44734 _44737) = (term209 _44734 _44737).
Proof. exact (@lem1982733 (term209 _44734 _44737)). Qed.
Lemma lem3851771 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3851772 (_44734 : int) (_44737 : int) : (term431 _44734 _44737) = (term211 _44734 _44737).
Proof. exact (MK_COMB (@lem3851771) (@lem3851770 _44734 _44737)). Qed.
Lemma lem3851773 : term114 = term114.
Proof. exact (eq_refl term114). Qed.
Lemma lem3851774 (_44734 : int) (_44737 : int) : (term429 _44734 _44737) = (term212 _44734 _44737).
Proof. exact (MK_COMB (@lem3851772 _44734 _44737) (@lem3851773)). Qed.
Lemma lem3851775 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term456 _44735 _44736 _44734 _44737) : term212 _44734 _44737.
Proof. exact (EQ_MP (@lem3851774 _44734 _44737) (@lem3851769 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3851777 (y : real) : term327 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem3851778 (_44737 : int) : term404 _44737.
Proof. exact (@lem3851777 (real_of_int _44737)). Qed.
Lemma lem3851779 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term456 _44735 _44736 _44734 _44737) : term405 _44737.
Proof. exact (@lem3851778 _44737 (@lem3851698 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3851780 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term456 _44735 _44736 _44734 _44737) : term457 _44737.
Proof. exact (@lem3851779 _44735 _44736 _44734 _44737 h1 term128). Qed.
Lemma lem3851781 (_44737 : int) : (term457 _44737) = ((term402 _44737) = term114).
Proof. exact (eq_refl (term457 _44737)). Qed.
Lemma lem3851782 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term456 _44735 _44736 _44734 _44737) : (term402 _44737) = term114.
Proof. exact (EQ_MP (@lem3851781 _44737) (@lem3851780 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3851783 (_44737 : int) : (term402 _44737) = (real_of_int _44737).
Proof. exact (@lem1982733 (real_of_int _44737)). Qed.
Lemma lem3851784 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3851785 (_44737 : int) : (term458 _44737) = (term120 _44737).
Proof. exact (MK_COMB (@lem3851784) (@lem3851783 _44737)). Qed.
Lemma lem3851786 : term114 = term114.
Proof. exact (eq_refl term114). Qed.
Lemma lem3851787 (_44737 : int) : ((term402 _44737) = term114) = ((real_of_int _44737) = term114).
Proof. exact (MK_COMB (@lem3851785 _44737) (@lem3851786)). Qed.
Lemma lem3851788 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term456 _44735 _44736 _44734 _44737) : (real_of_int _44737) = term114.
Proof. exact (EQ_MP (@lem3851787 _44737) (@lem3851782 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3851789 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term456 _44735 _44736 _44734 _44737) : term459 _44734 _44737.
Proof. exact (conj (@lem3851788 _44735 _44736 _44734 _44737 h1) (@lem3851775 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3851791 (x : real) (y : real) : term375 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem3851792 (_44734 : int) (_44737 : int) : term460 _44734 _44737.
Proof. exact (@lem3851791 (real_of_int _44737) (term209 _44734 _44737)). Qed.
Lemma lem3851793 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term456 _44735 _44736 _44734 _44737) : term461 _44734 _44737.
Proof. exact (@lem3851792 _44734 _44737 (@lem3851789 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3851794 (_44734 : int) (_44737 : int) : (term462 _44734 _44737) = (term463 _44734 _44737).
Proof. exact (@lem1982757 (real_of_int _44734) (real_of_int _44737) (term208 _44737)). Qed.
Lemma lem3851795 (_44737 : int) : (term453 _44737) = (term454 _44737).
Proof. exact (@lem1982763 (real_of_int _44737) (term190 _44737) term163). Qed.
Lemma lem3851796 (_44737 : int) : (term341 _44737) = (term342 _44737).
Proof. exact (@lem1982715 term163 (real_of_int _44737)). Qed.
Lemma lem3851798 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3851799 : term128 = term198.
Proof. exact (@lem3851798 term129). Qed.
Lemma lem3851801 (x : nat) : (term161 x) = (term162 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3851802 : term163 = term164.
Proof. exact (@lem3851801 term129). Qed.
Lemma lem3851803 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3851804 : term343 = term344.
Proof. exact (MK_COMB (@lem3851803) (@lem3851802)). Qed.
Lemma lem3851805 : term345 = term346.
Proof. exact (MK_COMB (@lem3851804) (@lem3851799)). Qed.
Lemma lem3851806 : term347.
Proof. exact (@lem1981473 term163 term128 term128 term128 term114 term128). Qed.
Lemma lem3851808 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3851809 : term303 = term309.
Proof. exact (@lem3851808 (NUMERAL 0) term129). Qed.
Lemma lem3851810 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3851811 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3851812 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3851811 h1) (fun h1 : term309 = True => @lem3851810)). Qed.
Lemma lem3851813 : term309 = True.
Proof. exact (EQ_MP (@lem3851812) (@lem3851810)). Qed.
Lemma lem3851814 : term303 = True.
Proof. exact (TRANS (@lem3851809) (@lem3851813)). Qed.
Lemma lem3851815 : True = term303.
Proof. exact (SYM (@lem3851814)). Qed.
Lemma lem3851816 : term303.
Proof. exact (EQ_MP (@lem3851815) (@lem0)). Qed.
Lemma lem3851817 : term348.
Proof. exact (@lem3851806 (@lem3851816)). Qed.
Lemma lem3851819 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3851820 : term303 = term309.
Proof. exact (@lem3851819 (NUMERAL 0) term129). Qed.
Lemma lem3851821 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3851822 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3851823 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3851822 h1) (fun h1 : term309 = True => @lem3851821)). Qed.
Lemma lem3851824 : term309 = True.
Proof. exact (EQ_MP (@lem3851823) (@lem3851821)). Qed.
Lemma lem3851825 : term303 = True.
Proof. exact (TRANS (@lem3851820) (@lem3851824)). Qed.
Lemma lem3851826 : True = term303.
Proof. exact (SYM (@lem3851825)). Qed.
Lemma lem3851827 : term303.
Proof. exact (EQ_MP (@lem3851826) (@lem0)). Qed.
Lemma lem3851828 : term349.
Proof. exact (@lem3851817 (@lem3851827)). Qed.
Lemma lem3851830 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3851831 : term303 = term309.
Proof. exact (@lem3851830 (NUMERAL 0) term129). Qed.
Lemma lem3851832 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3851833 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3851834 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3851833 h1) (fun h1 : term309 = True => @lem3851832)). Qed.
Lemma lem3851835 : term309 = True.
Proof. exact (EQ_MP (@lem3851834) (@lem3851832)). Qed.
Lemma lem3851836 : term303 = True.
Proof. exact (TRANS (@lem3851831) (@lem3851835)). Qed.
Lemma lem3851837 : True = term303.
Proof. exact (SYM (@lem3851836)). Qed.
Lemma lem3851838 : term303.
Proof. exact (EQ_MP (@lem3851837) (@lem0)). Qed.
Lemma lem3851839 : term350.
Proof. exact (@lem3851828 (@lem3851838)). Qed.
Lemma lem3851841 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3851842 : term172 = term173.
Proof. exact (@lem3851841 term129 term129). Qed.
Lemma lem3851843 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3851844 : term175 = term129.
Proof. exact (EQ_MP (@lem3851843) (@lem940073)). Qed.
Lemma lem3851845 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3851846 : term173 = term128.
Proof. exact (MK_COMB (@lem3851845) (@lem3851844)). Qed.
Lemma lem3851847 : term172 = term128.
Proof. exact (TRANS (@lem3851842) (@lem3851846)). Qed.
Lemma lem3851849 (m : nat) (n : nat) : (term202 m n) = (term203 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3851850 : term199 = term204.
Proof. exact (@lem3851849 term129 term129). Qed.
Lemma lem3851851 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3851852 : term175 = term129.
Proof. exact (EQ_MP (@lem3851851) (@lem940073)). Qed.
Lemma lem3851853 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3851854 : term173 = term128.
Proof. exact (MK_COMB (@lem3851853) (@lem3851852)). Qed.
Lemma lem3851855 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3851856 : term204 = term163.
Proof. exact (MK_COMB (@lem3851855) (@lem3851854)). Qed.
Lemma lem3851857 : term199 = term163.
Proof. exact (TRANS (@lem3851850) (@lem3851856)). Qed.
Lemma lem3851858 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3851859 : term351 = term343.
Proof. exact (MK_COMB (@lem3851858) (@lem3851857)). Qed.
Lemma lem3851860 : term352 = term345.
Proof. exact (MK_COMB (@lem3851859) (@lem3851847)). Qed.
Lemma lem3851862 (m : nat) : (term353 m) = term114.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3851863 : term345 = term114.
Proof. exact (@lem3851862 term129). Qed.
Lemma lem3851864 : term352 = term114.
Proof. exact (TRANS (@lem3851860) (@lem3851863)). Qed.
Lemma lem3851865 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3851866 : term354 = term355.
Proof. exact (MK_COMB (@lem3851865) (@lem3851864)). Qed.
Lemma lem3851867 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem3851868 : term356 = term314.
Proof. exact (MK_COMB (@lem3851866) (@lem3851867)). Qed.
Lemma lem3851870 (x : nat) : (term313 x) = term114.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3851871 : term314 = term114.
Proof. exact (@lem3851870 term129). Qed.
Lemma lem3851872 : term356 = term114.
Proof. exact (TRANS (@lem3851868) (@lem3851871)). Qed.
Lemma lem3851874 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3851875 : term172 = term173.
Proof. exact (@lem3851874 term129 term129). Qed.
Lemma lem3851876 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3851877 : term175 = term129.
Proof. exact (EQ_MP (@lem3851876) (@lem940073)). Qed.
Lemma lem3851878 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3851879 : term173 = term128.
Proof. exact (MK_COMB (@lem3851878) (@lem3851877)). Qed.
Lemma lem3851880 : term172 = term128.
Proof. exact (TRANS (@lem3851875) (@lem3851879)). Qed.
Lemma lem3851881 : term355 = term355.
Proof. exact (eq_refl term355). Qed.
Lemma lem3851882 : term357 = term314.
Proof. exact (MK_COMB (@lem3851881) (@lem3851880)). Qed.
Lemma lem3851884 (x : nat) : (term313 x) = term114.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3851885 : term314 = term114.
Proof. exact (@lem3851884 term129). Qed.
Lemma lem3851886 : term357 = term114.
Proof. exact (TRANS (@lem3851882) (@lem3851885)). Qed.
Lemma lem3851887 : term114 = term357.
Proof. exact (SYM (@lem3851886)). Qed.
Lemma lem3851888 : term356 = term357.
Proof. exact (TRANS (@lem3851872) (@lem3851887)). Qed.
Lemma lem3851889 : term346 = term160.
Proof. exact (@lem3851839 (@lem3851888)). Qed.
Lemma lem3851890 : term345 = term160.
Proof. exact (TRANS (@lem3851805) (@lem3851889)). Qed.
Lemma lem3851892 (x : real) : (term179 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3851893 : term160 = term114.
Proof. exact (@lem3851892 term114). Qed.
Lemma lem3851894 : term345 = term114.
Proof. exact (TRANS (@lem3851890) (@lem3851893)). Qed.
Lemma lem3851895 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3851896 : term358 = term355.
Proof. exact (MK_COMB (@lem3851895) (@lem3851894)). Qed.
Lemma lem3851897 (_44737 : int) : (real_of_int _44737) = (real_of_int _44737).
Proof. exact (eq_refl (real_of_int _44737)). Qed.
Lemma lem3851898 (_44737 : int) : (term342 _44737) = (term359 _44737).
Proof. exact (MK_COMB (@lem3851896) (@lem3851897 _44737)). Qed.
Lemma lem3851899 (_44737 : int) : (term341 _44737) = (term359 _44737).
Proof. exact (TRANS (@lem3851796 _44737) (@lem3851898 _44737)). Qed.
Lemma lem3851900 (_44737 : int) : (term359 _44737) = term114.
Proof. exact (@lem1982719 (real_of_int _44737)). Qed.
Lemma lem3851901 (_44737 : int) : (term341 _44737) = term114.
Proof. exact (TRANS (@lem3851899 _44737) (@lem3851900 _44737)). Qed.
Lemma lem3851902 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3851903 (_44737 : int) : (term360 _44737) = term361.
Proof. exact (MK_COMB (@lem3851902) (@lem3851901 _44737)). Qed.
Lemma lem3851904 : term163 = term163.
Proof. exact (eq_refl term163). Qed.
Lemma lem3851905 (_44737 : int) : (term454 _44737) = term383.
Proof. exact (MK_COMB (@lem3851903 _44737) (@lem3851904)). Qed.
Lemma lem3851906 (_44737 : int) : (term453 _44737) = term383.
Proof. exact (TRANS (@lem3851795 _44737) (@lem3851905 _44737)). Qed.
Lemma lem3851907 : term383 = term163.
Proof. exact (@lem1982721 term163). Qed.
Lemma lem3851908 (_44737 : int) : (term453 _44737) = term163.
Proof. exact (TRANS (@lem3851906 _44737) (@lem3851907)). Qed.
Lemma lem3851909 (_44734 : int) : (term130 _44734) = (term130 _44734).
Proof. exact (eq_refl (term130 _44734)). Qed.
Lemma lem3851910 (_44737 : int) (_44734 : int) : (term463 _44734 _44737) = (term380 _44734).
Proof. exact (MK_COMB (@lem3851909 _44734) (@lem3851908 _44737)). Qed.
Lemma lem3851911 (_44737 : int) (_44734 : int) : (term462 _44734 _44737) = (term380 _44734).
Proof. exact (TRANS (@lem3851794 _44734 _44737) (@lem3851910 _44737 _44734)). Qed.
Lemma lem3851912 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3851913 (_44737 : int) (_44734 : int) : (term464 _44734 _44737) = (term465 _44734).
Proof. exact (MK_COMB (@lem3851912) (@lem3851911 _44737 _44734)). Qed.
Lemma lem3851914 : term114 = term114.
Proof. exact (eq_refl term114). Qed.
Lemma lem3851915 (_44737 : int) (_44734 : int) : (term461 _44734 _44737) = (term466 _44734).
Proof. exact (MK_COMB (@lem3851913 _44737 _44734) (@lem3851914)). Qed.
Lemma lem3851916 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term456 _44735 _44736 _44734 _44737) : term466 _44734.
Proof. exact (EQ_MP (@lem3851915 _44737 _44734) (@lem3851793 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3851918 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3851919 : term302 = term303.
Proof. exact (@lem3851918 term114 term128). Qed.
Lemma lem3851921 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3851922 : term128 = term198.
Proof. exact (@lem3851921 term129). Qed.
Lemma lem3851924 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3851925 : term114 = term160.
Proof. exact (@lem3851924 (NUMERAL 0)). Qed.
Lemma lem3851926 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3851927 : term304 = term305.
Proof. exact (MK_COMB (@lem3851926) (@lem3851925)). Qed.
Lemma lem3851928 : term303 = term306.
Proof. exact (MK_COMB (@lem3851927) (@lem3851922)). Qed.
Lemma lem3851929 : term307.
Proof. exact (@lem1980255 term114 term128 term128 term128). Qed.
Lemma lem3851931 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3851932 : term303 = term309.
Proof. exact (@lem3851931 (NUMERAL 0) term129). Qed.
Lemma lem3851933 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3851934 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3851935 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3851934 h1) (fun h1 : term309 = True => @lem3851933)). Qed.
Lemma lem3851936 : term309 = True.
Proof. exact (EQ_MP (@lem3851935) (@lem3851933)). Qed.
Lemma lem3851937 : term303 = True.
Proof. exact (TRANS (@lem3851932) (@lem3851936)). Qed.
Lemma lem3851938 : True = term303.
Proof. exact (SYM (@lem3851937)). Qed.
Lemma lem3851939 : term303.
Proof. exact (EQ_MP (@lem3851938) (@lem0)). Qed.
Lemma lem3851940 : term311.
Proof. exact (@lem3851929 (@lem3851939)). Qed.
Lemma lem3851942 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3851943 : term303 = term309.
Proof. exact (@lem3851942 (NUMERAL 0) term129). Qed.
Lemma lem3851944 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3851945 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3851946 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3851945 h1) (fun h1 : term309 = True => @lem3851944)). Qed.
Lemma lem3851947 : term309 = True.
Proof. exact (EQ_MP (@lem3851946) (@lem3851944)). Qed.
Lemma lem3851948 : term303 = True.
Proof. exact (TRANS (@lem3851943) (@lem3851947)). Qed.
Lemma lem3851949 : True = term303.
Proof. exact (SYM (@lem3851948)). Qed.
Lemma lem3851950 : term303.
Proof. exact (EQ_MP (@lem3851949) (@lem0)). Qed.
Lemma lem3851951 : term306 = term312.
Proof. exact (@lem3851940 (@lem3851950)). Qed.
Lemma lem3851953 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3851954 : term172 = term173.
Proof. exact (@lem3851953 term129 term129). Qed.
Lemma lem3851955 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3851956 : term175 = term129.
Proof. exact (EQ_MP (@lem3851955) (@lem940073)). Qed.
Lemma lem3851957 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3851958 : term173 = term128.
Proof. exact (MK_COMB (@lem3851957) (@lem3851956)). Qed.
Lemma lem3851959 : term172 = term128.
Proof. exact (TRANS (@lem3851954) (@lem3851958)). Qed.
Lemma lem3851961 (x : nat) : (term313 x) = term114.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3851962 : term314 = term114.
Proof. exact (@lem3851961 term129). Qed.
Lemma lem3851963 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3851964 : term315 = term304.
Proof. exact (MK_COMB (@lem3851963) (@lem3851962)). Qed.
Lemma lem3851965 : term312 = term303.
Proof. exact (MK_COMB (@lem3851964) (@lem3851959)). Qed.
Lemma lem3851967 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3851968 : term303 = term309.
Proof. exact (@lem3851967 (NUMERAL 0) term129). Qed.
Lemma lem3851969 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3851970 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3851971 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3851970 h1) (fun h1 : term309 = True => @lem3851969)). Qed.
Lemma lem3851972 : term309 = True.
Proof. exact (EQ_MP (@lem3851971) (@lem3851969)). Qed.
Lemma lem3851973 : term303 = True.
Proof. exact (TRANS (@lem3851968) (@lem3851972)). Qed.
Lemma lem3851974 : term312 = True.
Proof. exact (TRANS (@lem3851965) (@lem3851973)). Qed.
Lemma lem3851975 : term306 = True.
Proof. exact (TRANS (@lem3851951) (@lem3851974)). Qed.
Lemma lem3851976 : term303 = True.
Proof. exact (TRANS (@lem3851928) (@lem3851975)). Qed.
Lemma lem3851977 : term302 = True.
Proof. exact (TRANS (@lem3851919) (@lem3851976)). Qed.
Lemma lem3851978 : True = term302.
Proof. exact (SYM (@lem3851977)). Qed.
Lemma lem3851979 : term302.
Proof. exact (EQ_MP (@lem3851978) (@lem0)). Qed.
Lemma lem3851980 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term456 _44735 _44736 _44734 _44737) : term467 _44734.
Proof. exact (conj (@lem3851979) (@lem3851916 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3851982 (x : real) (y : real) : term317 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3851983 (_44734 : int) : term468 _44734.
Proof. exact (@lem3851982 term128 (term380 _44734)). Qed.
Lemma lem3851984 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term456 _44735 _44736 _44734 _44737) : term469 _44734.
Proof. exact (@lem3851983 _44734 (@lem3851980 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3851985 (_44734 : int) : (term470 _44734) = (term380 _44734).
Proof. exact (@lem1982733 (term380 _44734)). Qed.
Lemma lem3851986 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3851987 (_44734 : int) : (term471 _44734) = (term465 _44734).
Proof. exact (MK_COMB (@lem3851986) (@lem3851985 _44734)). Qed.
Lemma lem3851988 : term114 = term114.
Proof. exact (eq_refl term114). Qed.
Lemma lem3851989 (_44734 : int) : (term469 _44734) = (term466 _44734).
Proof. exact (MK_COMB (@lem3851987 _44734) (@lem3851988)). Qed.
Lemma lem3851990 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term456 _44735 _44736 _44734 _44737) : term466 _44734.
Proof. exact (EQ_MP (@lem3851989 _44734) (@lem3851984 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3851992 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3851993 : term302 = term303.
Proof. exact (@lem3851992 term114 term128). Qed.
Lemma lem3851995 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3851996 : term128 = term198.
Proof. exact (@lem3851995 term129). Qed.
Lemma lem3851998 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3851999 : term114 = term160.
Proof. exact (@lem3851998 (NUMERAL 0)). Qed.
Lemma lem3852000 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3852001 : term304 = term305.
Proof. exact (MK_COMB (@lem3852000) (@lem3851999)). Qed.
Lemma lem3852002 : term303 = term306.
Proof. exact (MK_COMB (@lem3852001) (@lem3851996)). Qed.
Lemma lem3852003 : term307.
Proof. exact (@lem1980255 term114 term128 term128 term128). Qed.
Lemma lem3852005 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3852006 : term303 = term309.
Proof. exact (@lem3852005 (NUMERAL 0) term129). Qed.
Lemma lem3852007 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3852008 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3852009 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3852008 h1) (fun h1 : term309 = True => @lem3852007)). Qed.
Lemma lem3852010 : term309 = True.
Proof. exact (EQ_MP (@lem3852009) (@lem3852007)). Qed.
Lemma lem3852011 : term303 = True.
Proof. exact (TRANS (@lem3852006) (@lem3852010)). Qed.
Lemma lem3852012 : True = term303.
Proof. exact (SYM (@lem3852011)). Qed.
Lemma lem3852013 : term303.
Proof. exact (EQ_MP (@lem3852012) (@lem0)). Qed.
Lemma lem3852014 : term311.
Proof. exact (@lem3852003 (@lem3852013)). Qed.
Lemma lem3852016 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3852017 : term303 = term309.
Proof. exact (@lem3852016 (NUMERAL 0) term129). Qed.
Lemma lem3852018 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3852019 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3852020 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3852019 h1) (fun h1 : term309 = True => @lem3852018)). Qed.
Lemma lem3852021 : term309 = True.
Proof. exact (EQ_MP (@lem3852020) (@lem3852018)). Qed.
Lemma lem3852022 : term303 = True.
Proof. exact (TRANS (@lem3852017) (@lem3852021)). Qed.
Lemma lem3852023 : True = term303.
Proof. exact (SYM (@lem3852022)). Qed.
Lemma lem3852024 : term303.
Proof. exact (EQ_MP (@lem3852023) (@lem0)). Qed.
Lemma lem3852025 : term306 = term312.
Proof. exact (@lem3852014 (@lem3852024)). Qed.
Lemma lem3852027 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3852028 : term172 = term173.
Proof. exact (@lem3852027 term129 term129). Qed.
Lemma lem3852029 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3852030 : term175 = term129.
Proof. exact (EQ_MP (@lem3852029) (@lem940073)). Qed.
Lemma lem3852031 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3852032 : term173 = term128.
Proof. exact (MK_COMB (@lem3852031) (@lem3852030)). Qed.
Lemma lem3852033 : term172 = term128.
Proof. exact (TRANS (@lem3852028) (@lem3852032)). Qed.
Lemma lem3852035 (x : nat) : (term313 x) = term114.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3852036 : term314 = term114.
Proof. exact (@lem3852035 term129). Qed.
Lemma lem3852037 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3852038 : term315 = term304.
Proof. exact (MK_COMB (@lem3852037) (@lem3852036)). Qed.
Lemma lem3852039 : term312 = term303.
Proof. exact (MK_COMB (@lem3852038) (@lem3852033)). Qed.
Lemma lem3852041 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3852042 : term303 = term309.
Proof. exact (@lem3852041 (NUMERAL 0) term129). Qed.
Lemma lem3852043 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3852044 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3852045 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3852044 h1) (fun h1 : term309 = True => @lem3852043)). Qed.
Lemma lem3852046 : term309 = True.
Proof. exact (EQ_MP (@lem3852045) (@lem3852043)). Qed.
Lemma lem3852047 : term303 = True.
Proof. exact (TRANS (@lem3852042) (@lem3852046)). Qed.
Lemma lem3852048 : term312 = True.
Proof. exact (TRANS (@lem3852039) (@lem3852047)). Qed.
Lemma lem3852049 : term306 = True.
Proof. exact (TRANS (@lem3852025) (@lem3852048)). Qed.
Lemma lem3852050 : term303 = True.
Proof. exact (TRANS (@lem3852002) (@lem3852049)). Qed.
Lemma lem3852051 : term302 = True.
Proof. exact (TRANS (@lem3851993) (@lem3852050)). Qed.
Lemma lem3852052 : True = term302.
Proof. exact (SYM (@lem3852051)). Qed.
Lemma lem3852053 : term302.
Proof. exact (EQ_MP (@lem3852052) (@lem0)). Qed.
Lemma lem3852054 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term456 _44735 _44736 _44734 _44737) : term427 _44735 _44736.
Proof. exact (conj (@lem3852053) (@lem3851699 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3852056 (x : real) (y : real) : term317 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3852057 (_44735 : int) (_44736 : int) : term428 _44735 _44736.
Proof. exact (@lem3852056 term128 (term209 _44735 _44736)). Qed.
Lemma lem3852058 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term456 _44735 _44736 _44734 _44737) : term429 _44735 _44736.
Proof. exact (@lem3852057 _44735 _44736 (@lem3852054 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3852059 (_44735 : int) (_44736 : int) : (term430 _44735 _44736) = (term209 _44735 _44736).
Proof. exact (@lem1982733 (term209 _44735 _44736)). Qed.
Lemma lem3852060 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3852061 (_44735 : int) (_44736 : int) : (term431 _44735 _44736) = (term211 _44735 _44736).
Proof. exact (MK_COMB (@lem3852060) (@lem3852059 _44735 _44736)). Qed.
Lemma lem3852062 : term114 = term114.
Proof. exact (eq_refl term114). Qed.
Lemma lem3852063 (_44735 : int) (_44736 : int) : (term429 _44735 _44736) = (term212 _44735 _44736).
Proof. exact (MK_COMB (@lem3852061 _44735 _44736) (@lem3852062)). Qed.
Lemma lem3852064 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term456 _44735 _44736 _44734 _44737) : term212 _44735 _44736.
Proof. exact (EQ_MP (@lem3852063 _44735 _44736) (@lem3852058 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3852066 (y : real) : term327 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem3852067 (_44734 : int) (_44735 : int) (_44736 : int) : term328 _44734 _44735 _44736.
Proof. exact (@lem3852066 (term220 _44734 _44735 _44736)). Qed.
Lemma lem3852068 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term456 _44735 _44736 _44734 _44737) : term329 _44734 _44735 _44736.
Proof. exact (@lem3852067 _44734 _44735 _44736 (@lem3851701 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3852069 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term456 _44735 _44736 _44734 _44737) : term472 _44734 _44735 _44736.
Proof. exact (@lem3852068 _44735 _44736 _44734 _44737 h1 term163). Qed.
Lemma lem3852070 (_44734 : int) (_44735 : int) (_44736 : int) : (term472 _44734 _44735 _44736) = ((term473 _44734 _44735 _44736) = term114).
Proof. exact (eq_refl (term472 _44734 _44735 _44736)). Qed.
Lemma lem3852071 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term456 _44735 _44736 _44734 _44737) : (term473 _44734 _44735 _44736) = term114.
Proof. exact (EQ_MP (@lem3852070 _44734 _44735 _44736) (@lem3852069 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3852072 (_44734 : int) (_44735 : int) (_44736 : int) : (term473 _44734 _44735 _44736) = (term474 _44734 _44735 _44736).
Proof. exact (@lem1982781 (real_of_int _44734) term163 (term338 _44735 _44736)). Qed.
Lemma lem3852073 (_44735 : int) (_44736 : int) : (term433 _44735 _44736) = (term434 _44735 _44736).
Proof. exact (@lem1982781 (real_of_int _44735) term163 (term190 _44736)). Qed.
Lemma lem3852074 (_44736 : int) : (term435 _44736) = (term436 _44736).
Proof. exact (@lem1982749 term163 term163 (real_of_int _44736)). Qed.
Lemma lem3852076 (x : nat) : (term161 x) = (term162 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3852077 : term163 = term164.
Proof. exact (@lem3852076 term129). Qed.
Lemma lem3852079 (x : nat) : (term161 x) = (term162 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3852080 : term163 = term164.
Proof. exact (@lem3852079 term129). Qed.
Lemma lem3852081 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3852082 : term165 = term166.
Proof. exact (MK_COMB (@lem3852081) (@lem3852080)). Qed.
Lemma lem3852083 : term437 = term438.
Proof. exact (MK_COMB (@lem3852082) (@lem3852077)). Qed.
Lemma lem3852084 : term438 = term439.
Proof. exact (@lem1981613 term163 term163 term128 term128). Qed.
Lemma lem3852086 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3852087 : term172 = term173.
Proof. exact (@lem3852086 term129 term129). Qed.
Lemma lem3852088 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3852089 : term175 = term129.
Proof. exact (EQ_MP (@lem3852088) (@lem940073)). Qed.
Lemma lem3852090 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3852091 : term173 = term128.
Proof. exact (MK_COMB (@lem3852090) (@lem3852089)). Qed.
Lemma lem3852092 : term172 = term128.
Proof. exact (TRANS (@lem3852087) (@lem3852091)). Qed.
Lemma lem3852094 (m : nat) (n : nat) : (term440 m n) = (term171 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem3852095 : term437 = term173.
Proof. exact (@lem3852094 term129 term129). Qed.
Lemma lem3852096 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3852097 : term175 = term129.
Proof. exact (EQ_MP (@lem3852096) (@lem940073)). Qed.
Lemma lem3852098 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3852099 : term173 = term128.
Proof. exact (MK_COMB (@lem3852098) (@lem3852097)). Qed.
Lemma lem3852100 : term437 = term128.
Proof. exact (TRANS (@lem3852095) (@lem3852099)). Qed.
Lemma lem3852101 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3852102 : term441 = term442.
Proof. exact (MK_COMB (@lem3852101) (@lem3852100)). Qed.
Lemma lem3852103 : term439 = term198.
Proof. exact (MK_COMB (@lem3852102) (@lem3852092)). Qed.
Lemma lem3852104 : term438 = term198.
Proof. exact (TRANS (@lem3852084) (@lem3852103)). Qed.
Lemma lem3852105 : term437 = term198.
Proof. exact (TRANS (@lem3852083) (@lem3852104)). Qed.
Lemma lem3852107 (x : real) : (term179 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3852108 : term198 = term128.
Proof. exact (@lem3852107 term128). Qed.
Lemma lem3852109 : term437 = term128.
Proof. exact (TRANS (@lem3852105) (@lem3852108)). Qed.
Lemma lem3852110 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3852111 : term443 = term444.
Proof. exact (MK_COMB (@lem3852110) (@lem3852109)). Qed.
Lemma lem3852112 (_44736 : int) : (real_of_int _44736) = (real_of_int _44736).
Proof. exact (eq_refl (real_of_int _44736)). Qed.
Lemma lem3852113 (_44736 : int) : (term436 _44736) = (term402 _44736).
Proof. exact (MK_COMB (@lem3852111) (@lem3852112 _44736)). Qed.
Lemma lem3852114 (_44736 : int) : (term435 _44736) = (term402 _44736).
Proof. exact (TRANS (@lem3852074 _44736) (@lem3852113 _44736)). Qed.
Lemma lem3852115 (_44736 : int) : (term402 _44736) = (real_of_int _44736).
Proof. exact (@lem1982709 (real_of_int _44736)). Qed.
Lemma lem3852116 (_44736 : int) : (term435 _44736) = (real_of_int _44736).
Proof. exact (TRANS (@lem3852114 _44736) (@lem3852115 _44736)). Qed.
Lemma lem3852119 (_44735 : int) : (term207 _44735) = (term207 _44735).
Proof. exact (eq_refl (term207 _44735)). Qed.
Lemma lem3852120 (_44735 : int) (_44736 : int) : (term434 _44735 _44736) = (term445 _44735 _44736).
Proof. exact (MK_COMB (@lem3852119 _44735) (@lem3852116 _44736)). Qed.
Lemma lem3852121 (_44735 : int) (_44736 : int) : (term433 _44735 _44736) = (term445 _44735 _44736).
Proof. exact (TRANS (@lem3852073 _44735 _44736) (@lem3852120 _44735 _44736)). Qed.
Lemma lem3852124 (_44734 : int) : (term207 _44734) = (term207 _44734).
Proof. exact (eq_refl (term207 _44734)). Qed.
Lemma lem3852125 (_44734 : int) (_44735 : int) (_44736 : int) : (term474 _44734 _44735 _44736) = (term475 _44734 _44735 _44736).
Proof. exact (MK_COMB (@lem3852124 _44734) (@lem3852121 _44735 _44736)). Qed.
Lemma lem3852126 (_44734 : int) (_44735 : int) (_44736 : int) : (term473 _44734 _44735 _44736) = (term475 _44734 _44735 _44736).
Proof. exact (TRANS (@lem3852072 _44734 _44735 _44736) (@lem3852125 _44734 _44735 _44736)). Qed.
Lemma lem3852127 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3852128 (_44734 : int) (_44735 : int) (_44736 : int) : (term476 _44734 _44735 _44736) = (term477 _44734 _44735 _44736).
Proof. exact (MK_COMB (@lem3852127) (@lem3852126 _44734 _44735 _44736)). Qed.
Lemma lem3852129 : term114 = term114.
Proof. exact (eq_refl term114). Qed.
Lemma lem3852130 (_44734 : int) (_44735 : int) (_44736 : int) : ((term473 _44734 _44735 _44736) = term114) = ((term475 _44734 _44735 _44736) = term114).
Proof. exact (MK_COMB (@lem3852128 _44734 _44735 _44736) (@lem3852129)). Qed.
Lemma lem3852131 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term456 _44735 _44736 _44734 _44737) : (term475 _44734 _44735 _44736) = term114.
Proof. exact (EQ_MP (@lem3852130 _44734 _44735 _44736) (@lem3852071 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3852132 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term456 _44735 _44736 _44734 _44737) : term478 _44734 _44735 _44736.
Proof. exact (conj (@lem3852131 _44735 _44736 _44734 _44737 h1) (@lem3852064 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3852134 (x : real) (y : real) : term375 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem3852135 (_44734 : int) (_44735 : int) (_44736 : int) : term479 _44734 _44735 _44736.
Proof. exact (@lem3852134 (term475 _44734 _44735 _44736) (term209 _44735 _44736)). Qed.
Lemma lem3852136 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term456 _44735 _44736 _44734 _44737) : term480 _44734 _44735 _44736.
Proof. exact (@lem3852135 _44734 _44735 _44736 (@lem3852132 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3852137 (_44734 : int) (_44735 : int) (_44736 : int) : (term481 _44734 _44735 _44736) = (term482 _44734 _44735 _44736).
Proof. exact (@lem1982755 (term190 _44734) (term445 _44735 _44736) (term209 _44735 _44736)). Qed.
Lemma lem3852138 (_44735 : int) (_44736 : int) : (term451 _44735 _44736) = (term452 _44735 _44736).
Proof. exact (@lem1982753 (term190 _44735) (real_of_int _44735) (real_of_int _44736) (term208 _44736)). Qed.
Lemma lem3852139 (_44735 : int) : (term364 _44735) = (term342 _44735).
Proof. exact (@lem1982713 term163 (real_of_int _44735)). Qed.
Lemma lem3852141 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3852142 : term128 = term198.
Proof. exact (@lem3852141 term129). Qed.
Lemma lem3852144 (x : nat) : (term161 x) = (term162 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3852145 : term163 = term164.
Proof. exact (@lem3852144 term129). Qed.
Lemma lem3852146 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3852147 : term343 = term344.
Proof. exact (MK_COMB (@lem3852146) (@lem3852145)). Qed.
Lemma lem3852148 : term345 = term346.
Proof. exact (MK_COMB (@lem3852147) (@lem3852142)). Qed.
Lemma lem3852149 : term347.
Proof. exact (@lem1981473 term163 term128 term128 term128 term114 term128). Qed.
Lemma lem3852151 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3852152 : term303 = term309.
Proof. exact (@lem3852151 (NUMERAL 0) term129). Qed.
Lemma lem3852153 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3852154 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3852155 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3852154 h1) (fun h1 : term309 = True => @lem3852153)). Qed.
Lemma lem3852156 : term309 = True.
Proof. exact (EQ_MP (@lem3852155) (@lem3852153)). Qed.
Lemma lem3852157 : term303 = True.
Proof. exact (TRANS (@lem3852152) (@lem3852156)). Qed.
Lemma lem3852158 : True = term303.
Proof. exact (SYM (@lem3852157)). Qed.
Lemma lem3852159 : term303.
Proof. exact (EQ_MP (@lem3852158) (@lem0)). Qed.
Lemma lem3852160 : term348.
Proof. exact (@lem3852149 (@lem3852159)). Qed.
Lemma lem3852162 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3852163 : term303 = term309.
Proof. exact (@lem3852162 (NUMERAL 0) term129). Qed.
Lemma lem3852164 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3852165 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3852166 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3852165 h1) (fun h1 : term309 = True => @lem3852164)). Qed.
Lemma lem3852167 : term309 = True.
Proof. exact (EQ_MP (@lem3852166) (@lem3852164)). Qed.
Lemma lem3852168 : term303 = True.
Proof. exact (TRANS (@lem3852163) (@lem3852167)). Qed.
Lemma lem3852169 : True = term303.
Proof. exact (SYM (@lem3852168)). Qed.
Lemma lem3852170 : term303.
Proof. exact (EQ_MP (@lem3852169) (@lem0)). Qed.
Lemma lem3852171 : term349.
Proof. exact (@lem3852160 (@lem3852170)). Qed.
Lemma lem3852173 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3852174 : term303 = term309.
Proof. exact (@lem3852173 (NUMERAL 0) term129). Qed.
Lemma lem3852175 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3852176 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3852177 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3852176 h1) (fun h1 : term309 = True => @lem3852175)). Qed.
Lemma lem3852178 : term309 = True.
Proof. exact (EQ_MP (@lem3852177) (@lem3852175)). Qed.
Lemma lem3852179 : term303 = True.
Proof. exact (TRANS (@lem3852174) (@lem3852178)). Qed.
Lemma lem3852180 : True = term303.
Proof. exact (SYM (@lem3852179)). Qed.
Lemma lem3852181 : term303.
Proof. exact (EQ_MP (@lem3852180) (@lem0)). Qed.
Lemma lem3852182 : term350.
Proof. exact (@lem3852171 (@lem3852181)). Qed.
Lemma lem3852184 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3852185 : term172 = term173.
Proof. exact (@lem3852184 term129 term129). Qed.
Lemma lem3852186 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3852187 : term175 = term129.
Proof. exact (EQ_MP (@lem3852186) (@lem940073)). Qed.
Lemma lem3852188 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3852189 : term173 = term128.
Proof. exact (MK_COMB (@lem3852188) (@lem3852187)). Qed.
Lemma lem3852190 : term172 = term128.
Proof. exact (TRANS (@lem3852185) (@lem3852189)). Qed.
Lemma lem3852192 (m : nat) (n : nat) : (term202 m n) = (term203 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3852193 : term199 = term204.
Proof. exact (@lem3852192 term129 term129). Qed.
Lemma lem3852194 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3852195 : term175 = term129.
Proof. exact (EQ_MP (@lem3852194) (@lem940073)). Qed.
Lemma lem3852196 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3852197 : term173 = term128.
Proof. exact (MK_COMB (@lem3852196) (@lem3852195)). Qed.
Lemma lem3852198 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3852199 : term204 = term163.
Proof. exact (MK_COMB (@lem3852198) (@lem3852197)). Qed.
Lemma lem3852200 : term199 = term163.
Proof. exact (TRANS (@lem3852193) (@lem3852199)). Qed.
Lemma lem3852201 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3852202 : term351 = term343.
Proof. exact (MK_COMB (@lem3852201) (@lem3852200)). Qed.
Lemma lem3852203 : term352 = term345.
Proof. exact (MK_COMB (@lem3852202) (@lem3852190)). Qed.
Lemma lem3852205 (m : nat) : (term353 m) = term114.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3852206 : term345 = term114.
Proof. exact (@lem3852205 term129). Qed.
Lemma lem3852207 : term352 = term114.
Proof. exact (TRANS (@lem3852203) (@lem3852206)). Qed.
Lemma lem3852208 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3852209 : term354 = term355.
Proof. exact (MK_COMB (@lem3852208) (@lem3852207)). Qed.
Lemma lem3852210 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem3852211 : term356 = term314.
Proof. exact (MK_COMB (@lem3852209) (@lem3852210)). Qed.
Lemma lem3852213 (x : nat) : (term313 x) = term114.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3852214 : term314 = term114.
Proof. exact (@lem3852213 term129). Qed.
Lemma lem3852215 : term356 = term114.
Proof. exact (TRANS (@lem3852211) (@lem3852214)). Qed.
Lemma lem3852217 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3852218 : term172 = term173.
Proof. exact (@lem3852217 term129 term129). Qed.
Lemma lem3852219 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3852220 : term175 = term129.
Proof. exact (EQ_MP (@lem3852219) (@lem940073)). Qed.
Lemma lem3852221 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3852222 : term173 = term128.
Proof. exact (MK_COMB (@lem3852221) (@lem3852220)). Qed.
Lemma lem3852223 : term172 = term128.
Proof. exact (TRANS (@lem3852218) (@lem3852222)). Qed.
Lemma lem3852224 : term355 = term355.
Proof. exact (eq_refl term355). Qed.
Lemma lem3852225 : term357 = term314.
Proof. exact (MK_COMB (@lem3852224) (@lem3852223)). Qed.
Lemma lem3852227 (x : nat) : (term313 x) = term114.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3852228 : term314 = term114.
Proof. exact (@lem3852227 term129). Qed.
Lemma lem3852229 : term357 = term114.
Proof. exact (TRANS (@lem3852225) (@lem3852228)). Qed.
Lemma lem3852230 : term114 = term357.
Proof. exact (SYM (@lem3852229)). Qed.
Lemma lem3852231 : term356 = term357.
Proof. exact (TRANS (@lem3852215) (@lem3852230)). Qed.
Lemma lem3852232 : term346 = term160.
Proof. exact (@lem3852182 (@lem3852231)). Qed.
Lemma lem3852233 : term345 = term160.
Proof. exact (TRANS (@lem3852148) (@lem3852232)). Qed.
Lemma lem3852235 (x : real) : (term179 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3852236 : term160 = term114.
Proof. exact (@lem3852235 term114). Qed.
Lemma lem3852237 : term345 = term114.
Proof. exact (TRANS (@lem3852233) (@lem3852236)). Qed.
Lemma lem3852238 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3852239 : term358 = term355.
Proof. exact (MK_COMB (@lem3852238) (@lem3852237)). Qed.
Lemma lem3852240 (_44735 : int) : (real_of_int _44735) = (real_of_int _44735).
Proof. exact (eq_refl (real_of_int _44735)). Qed.
Lemma lem3852241 (_44735 : int) : (term342 _44735) = (term359 _44735).
Proof. exact (MK_COMB (@lem3852239) (@lem3852240 _44735)). Qed.
Lemma lem3852242 (_44735 : int) : (term364 _44735) = (term359 _44735).
Proof. exact (TRANS (@lem3852139 _44735) (@lem3852241 _44735)). Qed.
Lemma lem3852243 (_44735 : int) : (term359 _44735) = term114.
Proof. exact (@lem1982719 (real_of_int _44735)). Qed.
Lemma lem3852244 (_44735 : int) : (term364 _44735) = term114.
Proof. exact (TRANS (@lem3852242 _44735) (@lem3852243 _44735)). Qed.
Lemma lem3852245 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3852246 (_44735 : int) : (term365 _44735) = term361.
Proof. exact (MK_COMB (@lem3852245) (@lem3852244 _44735)). Qed.
Lemma lem3852247 (_44736 : int) : (term453 _44736) = (term454 _44736).
Proof. exact (@lem1982763 (real_of_int _44736) (term190 _44736) term163). Qed.
Lemma lem3852248 (_44736 : int) : (term341 _44736) = (term342 _44736).
Proof. exact (@lem1982715 term163 (real_of_int _44736)). Qed.
Lemma lem3852250 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3852251 : term128 = term198.
Proof. exact (@lem3852250 term129). Qed.
Lemma lem3852253 (x : nat) : (term161 x) = (term162 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3852254 : term163 = term164.
Proof. exact (@lem3852253 term129). Qed.
Lemma lem3852255 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3852256 : term343 = term344.
Proof. exact (MK_COMB (@lem3852255) (@lem3852254)). Qed.
Lemma lem3852257 : term345 = term346.
Proof. exact (MK_COMB (@lem3852256) (@lem3852251)). Qed.
Lemma lem3852258 : term347.
Proof. exact (@lem1981473 term163 term128 term128 term128 term114 term128). Qed.
Lemma lem3852260 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3852261 : term303 = term309.
Proof. exact (@lem3852260 (NUMERAL 0) term129). Qed.
Lemma lem3852262 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3852263 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3852264 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3852263 h1) (fun h1 : term309 = True => @lem3852262)). Qed.
Lemma lem3852265 : term309 = True.
Proof. exact (EQ_MP (@lem3852264) (@lem3852262)). Qed.
Lemma lem3852266 : term303 = True.
Proof. exact (TRANS (@lem3852261) (@lem3852265)). Qed.
Lemma lem3852267 : True = term303.
Proof. exact (SYM (@lem3852266)). Qed.
Lemma lem3852268 : term303.
Proof. exact (EQ_MP (@lem3852267) (@lem0)). Qed.
Lemma lem3852269 : term348.
Proof. exact (@lem3852258 (@lem3852268)). Qed.
Lemma lem3852271 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3852272 : term303 = term309.
Proof. exact (@lem3852271 (NUMERAL 0) term129). Qed.
Lemma lem3852273 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3852274 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3852275 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3852274 h1) (fun h1 : term309 = True => @lem3852273)). Qed.
Lemma lem3852276 : term309 = True.
Proof. exact (EQ_MP (@lem3852275) (@lem3852273)). Qed.
Lemma lem3852277 : term303 = True.
Proof. exact (TRANS (@lem3852272) (@lem3852276)). Qed.
Lemma lem3852278 : True = term303.
Proof. exact (SYM (@lem3852277)). Qed.
Lemma lem3852279 : term303.
Proof. exact (EQ_MP (@lem3852278) (@lem0)). Qed.
Lemma lem3852280 : term349.
Proof. exact (@lem3852269 (@lem3852279)). Qed.
Lemma lem3852282 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3852283 : term303 = term309.
Proof. exact (@lem3852282 (NUMERAL 0) term129). Qed.
Lemma lem3852284 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3852285 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3852286 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3852285 h1) (fun h1 : term309 = True => @lem3852284)). Qed.
Lemma lem3852287 : term309 = True.
Proof. exact (EQ_MP (@lem3852286) (@lem3852284)). Qed.
Lemma lem3852288 : term303 = True.
Proof. exact (TRANS (@lem3852283) (@lem3852287)). Qed.
Lemma lem3852289 : True = term303.
Proof. exact (SYM (@lem3852288)). Qed.
Lemma lem3852290 : term303.
Proof. exact (EQ_MP (@lem3852289) (@lem0)). Qed.
Lemma lem3852291 : term350.
Proof. exact (@lem3852280 (@lem3852290)). Qed.
Lemma lem3852293 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3852294 : term172 = term173.
Proof. exact (@lem3852293 term129 term129). Qed.
Lemma lem3852295 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3852296 : term175 = term129.
Proof. exact (EQ_MP (@lem3852295) (@lem940073)). Qed.
Lemma lem3852297 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3852298 : term173 = term128.
Proof. exact (MK_COMB (@lem3852297) (@lem3852296)). Qed.
Lemma lem3852299 : term172 = term128.
Proof. exact (TRANS (@lem3852294) (@lem3852298)). Qed.
Lemma lem3852301 (m : nat) (n : nat) : (term202 m n) = (term203 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3852302 : term199 = term204.
Proof. exact (@lem3852301 term129 term129). Qed.
Lemma lem3852303 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3852304 : term175 = term129.
Proof. exact (EQ_MP (@lem3852303) (@lem940073)). Qed.
Lemma lem3852305 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3852306 : term173 = term128.
Proof. exact (MK_COMB (@lem3852305) (@lem3852304)). Qed.
Lemma lem3852307 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3852308 : term204 = term163.
Proof. exact (MK_COMB (@lem3852307) (@lem3852306)). Qed.
Lemma lem3852309 : term199 = term163.
Proof. exact (TRANS (@lem3852302) (@lem3852308)). Qed.
Lemma lem3852310 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3852311 : term351 = term343.
Proof. exact (MK_COMB (@lem3852310) (@lem3852309)). Qed.
Lemma lem3852312 : term352 = term345.
Proof. exact (MK_COMB (@lem3852311) (@lem3852299)). Qed.
Lemma lem3852314 (m : nat) : (term353 m) = term114.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3852315 : term345 = term114.
Proof. exact (@lem3852314 term129). Qed.
Lemma lem3852316 : term352 = term114.
Proof. exact (TRANS (@lem3852312) (@lem3852315)). Qed.
Lemma lem3852317 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3852318 : term354 = term355.
Proof. exact (MK_COMB (@lem3852317) (@lem3852316)). Qed.
Lemma lem3852319 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem3852320 : term356 = term314.
Proof. exact (MK_COMB (@lem3852318) (@lem3852319)). Qed.
Lemma lem3852322 (x : nat) : (term313 x) = term114.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3852323 : term314 = term114.
Proof. exact (@lem3852322 term129). Qed.
Lemma lem3852324 : term356 = term114.
Proof. exact (TRANS (@lem3852320) (@lem3852323)). Qed.
Lemma lem3852326 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3852327 : term172 = term173.
Proof. exact (@lem3852326 term129 term129). Qed.
Lemma lem3852328 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3852329 : term175 = term129.
Proof. exact (EQ_MP (@lem3852328) (@lem940073)). Qed.
Lemma lem3852330 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3852331 : term173 = term128.
Proof. exact (MK_COMB (@lem3852330) (@lem3852329)). Qed.
Lemma lem3852332 : term172 = term128.
Proof. exact (TRANS (@lem3852327) (@lem3852331)). Qed.
Lemma lem3852333 : term355 = term355.
Proof. exact (eq_refl term355). Qed.
Lemma lem3852334 : term357 = term314.
Proof. exact (MK_COMB (@lem3852333) (@lem3852332)). Qed.
Lemma lem3852336 (x : nat) : (term313 x) = term114.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3852337 : term314 = term114.
Proof. exact (@lem3852336 term129). Qed.
Lemma lem3852338 : term357 = term114.
Proof. exact (TRANS (@lem3852334) (@lem3852337)). Qed.
Lemma lem3852339 : term114 = term357.
Proof. exact (SYM (@lem3852338)). Qed.
Lemma lem3852340 : term356 = term357.
Proof. exact (TRANS (@lem3852324) (@lem3852339)). Qed.
Lemma lem3852341 : term346 = term160.
Proof. exact (@lem3852291 (@lem3852340)). Qed.
Lemma lem3852342 : term345 = term160.
Proof. exact (TRANS (@lem3852257) (@lem3852341)). Qed.
Lemma lem3852344 (x : real) : (term179 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3852345 : term160 = term114.
Proof. exact (@lem3852344 term114). Qed.
Lemma lem3852346 : term345 = term114.
Proof. exact (TRANS (@lem3852342) (@lem3852345)). Qed.
Lemma lem3852347 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3852348 : term358 = term355.
Proof. exact (MK_COMB (@lem3852347) (@lem3852346)). Qed.
Lemma lem3852349 (_44736 : int) : (real_of_int _44736) = (real_of_int _44736).
Proof. exact (eq_refl (real_of_int _44736)). Qed.
Lemma lem3852350 (_44736 : int) : (term342 _44736) = (term359 _44736).
Proof. exact (MK_COMB (@lem3852348) (@lem3852349 _44736)). Qed.
Lemma lem3852351 (_44736 : int) : (term341 _44736) = (term359 _44736).
Proof. exact (TRANS (@lem3852248 _44736) (@lem3852350 _44736)). Qed.
Lemma lem3852352 (_44736 : int) : (term359 _44736) = term114.
Proof. exact (@lem1982719 (real_of_int _44736)). Qed.
Lemma lem3852353 (_44736 : int) : (term341 _44736) = term114.
Proof. exact (TRANS (@lem3852351 _44736) (@lem3852352 _44736)). Qed.
Lemma lem3852354 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3852355 (_44736 : int) : (term360 _44736) = term361.
Proof. exact (MK_COMB (@lem3852354) (@lem3852353 _44736)). Qed.
Lemma lem3852356 : term163 = term163.
Proof. exact (eq_refl term163). Qed.
Lemma lem3852357 (_44736 : int) : (term454 _44736) = term383.
Proof. exact (MK_COMB (@lem3852355 _44736) (@lem3852356)). Qed.
Lemma lem3852358 (_44736 : int) : (term453 _44736) = term383.
Proof. exact (TRANS (@lem3852247 _44736) (@lem3852357 _44736)). Qed.
Lemma lem3852359 : term383 = term163.
Proof. exact (@lem1982721 term163). Qed.
Lemma lem3852360 (_44736 : int) : (term453 _44736) = term163.
Proof. exact (TRANS (@lem3852358 _44736) (@lem3852359)). Qed.
Lemma lem3852361 (_44735 : int) (_44736 : int) : (term452 _44735 _44736) = term383.
Proof. exact (MK_COMB (@lem3852246 _44735) (@lem3852360 _44736)). Qed.
Lemma lem3852362 (_44735 : int) (_44736 : int) : (term451 _44735 _44736) = term383.
Proof. exact (TRANS (@lem3852138 _44735 _44736) (@lem3852361 _44735 _44736)). Qed.
Lemma lem3852363 : term383 = term163.
Proof. exact (@lem1982721 term163). Qed.
Lemma lem3852364 (_44735 : int) (_44736 : int) : (term451 _44735 _44736) = term163.
Proof. exact (TRANS (@lem3852362 _44735 _44736) (@lem3852363)). Qed.
Lemma lem3852365 (_44734 : int) : (term207 _44734) = (term207 _44734).
Proof. exact (eq_refl (term207 _44734)). Qed.
Lemma lem3852366 (_44735 : int) (_44736 : int) (_44734 : int) : (term482 _44734 _44735 _44736) = (term208 _44734).
Proof. exact (MK_COMB (@lem3852365 _44734) (@lem3852364 _44735 _44736)). Qed.
Lemma lem3852367 (_44735 : int) (_44736 : int) (_44734 : int) : (term481 _44734 _44735 _44736) = (term208 _44734).
Proof. exact (TRANS (@lem3852137 _44734 _44735 _44736) (@lem3852366 _44735 _44736 _44734)). Qed.
Lemma lem3852368 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3852369 (_44735 : int) (_44736 : int) (_44734 : int) : (term483 _44734 _44735 _44736) = (term413 _44734).
Proof. exact (MK_COMB (@lem3852368) (@lem3852367 _44735 _44736 _44734)). Qed.
Lemma lem3852370 : term114 = term114.
Proof. exact (eq_refl term114). Qed.
Lemma lem3852371 (_44735 : int) (_44736 : int) (_44734 : int) : (term480 _44734 _44735 _44736) = (term414 _44734).
Proof. exact (MK_COMB (@lem3852369 _44735 _44736 _44734) (@lem3852370)). Qed.
Lemma lem3852372 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term456 _44735 _44736 _44734 _44737) : term414 _44734.
Proof. exact (EQ_MP (@lem3852371 _44735 _44736 _44734) (@lem3852136 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3852374 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3852375 : term302 = term303.
Proof. exact (@lem3852374 term114 term128). Qed.
Lemma lem3852377 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3852378 : term128 = term198.
Proof. exact (@lem3852377 term129). Qed.
Lemma lem3852380 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3852381 : term114 = term160.
Proof. exact (@lem3852380 (NUMERAL 0)). Qed.
Lemma lem3852382 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3852383 : term304 = term305.
Proof. exact (MK_COMB (@lem3852382) (@lem3852381)). Qed.
Lemma lem3852384 : term303 = term306.
Proof. exact (MK_COMB (@lem3852383) (@lem3852378)). Qed.
Lemma lem3852385 : term307.
Proof. exact (@lem1980255 term114 term128 term128 term128). Qed.
Lemma lem3852387 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3852388 : term303 = term309.
Proof. exact (@lem3852387 (NUMERAL 0) term129). Qed.
Lemma lem3852389 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3852390 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3852391 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3852390 h1) (fun h1 : term309 = True => @lem3852389)). Qed.
Lemma lem3852392 : term309 = True.
Proof. exact (EQ_MP (@lem3852391) (@lem3852389)). Qed.
Lemma lem3852393 : term303 = True.
Proof. exact (TRANS (@lem3852388) (@lem3852392)). Qed.
Lemma lem3852394 : True = term303.
Proof. exact (SYM (@lem3852393)). Qed.
Lemma lem3852395 : term303.
Proof. exact (EQ_MP (@lem3852394) (@lem0)). Qed.
Lemma lem3852396 : term311.
Proof. exact (@lem3852385 (@lem3852395)). Qed.
Lemma lem3852398 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3852399 : term303 = term309.
Proof. exact (@lem3852398 (NUMERAL 0) term129). Qed.
Lemma lem3852400 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3852401 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3852402 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3852401 h1) (fun h1 : term309 = True => @lem3852400)). Qed.
Lemma lem3852403 : term309 = True.
Proof. exact (EQ_MP (@lem3852402) (@lem3852400)). Qed.
Lemma lem3852404 : term303 = True.
Proof. exact (TRANS (@lem3852399) (@lem3852403)). Qed.
Lemma lem3852405 : True = term303.
Proof. exact (SYM (@lem3852404)). Qed.
Lemma lem3852406 : term303.
Proof. exact (EQ_MP (@lem3852405) (@lem0)). Qed.
Lemma lem3852407 : term306 = term312.
Proof. exact (@lem3852396 (@lem3852406)). Qed.
Lemma lem3852409 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3852410 : term172 = term173.
Proof. exact (@lem3852409 term129 term129). Qed.
Lemma lem3852411 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3852412 : term175 = term129.
Proof. exact (EQ_MP (@lem3852411) (@lem940073)). Qed.
Lemma lem3852413 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3852414 : term173 = term128.
Proof. exact (MK_COMB (@lem3852413) (@lem3852412)). Qed.
Lemma lem3852415 : term172 = term128.
Proof. exact (TRANS (@lem3852410) (@lem3852414)). Qed.
Lemma lem3852417 (x : nat) : (term313 x) = term114.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3852418 : term314 = term114.
Proof. exact (@lem3852417 term129). Qed.
Lemma lem3852419 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3852420 : term315 = term304.
Proof. exact (MK_COMB (@lem3852419) (@lem3852418)). Qed.
Lemma lem3852421 : term312 = term303.
Proof. exact (MK_COMB (@lem3852420) (@lem3852415)). Qed.
Lemma lem3852423 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3852424 : term303 = term309.
Proof. exact (@lem3852423 (NUMERAL 0) term129). Qed.
Lemma lem3852425 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3852426 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3852427 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3852426 h1) (fun h1 : term309 = True => @lem3852425)). Qed.
Lemma lem3852428 : term309 = True.
Proof. exact (EQ_MP (@lem3852427) (@lem3852425)). Qed.
Lemma lem3852429 : term303 = True.
Proof. exact (TRANS (@lem3852424) (@lem3852428)). Qed.
Lemma lem3852430 : term312 = True.
Proof. exact (TRANS (@lem3852421) (@lem3852429)). Qed.
Lemma lem3852431 : term306 = True.
Proof. exact (TRANS (@lem3852407) (@lem3852430)). Qed.
Lemma lem3852432 : term303 = True.
Proof. exact (TRANS (@lem3852384) (@lem3852431)). Qed.
Lemma lem3852433 : term302 = True.
Proof. exact (TRANS (@lem3852375) (@lem3852432)). Qed.
Lemma lem3852434 : True = term302.
Proof. exact (SYM (@lem3852433)). Qed.
Lemma lem3852435 : term302.
Proof. exact (EQ_MP (@lem3852434) (@lem0)). Qed.
Lemma lem3852436 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term456 _44735 _44736 _44734 _44737) : term415 _44734.
Proof. exact (conj (@lem3852435) (@lem3852372 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3852438 (x : real) (y : real) : term317 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3852439 (_44734 : int) : term416 _44734.
Proof. exact (@lem3852438 term128 (term208 _44734)). Qed.
Lemma lem3852440 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term456 _44735 _44736 _44734 _44737) : term417 _44734.
Proof. exact (@lem3852439 _44734 (@lem3852436 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3852441 (_44734 : int) : (term418 _44734) = (term208 _44734).
Proof. exact (@lem1982733 (term208 _44734)). Qed.
Lemma lem3852442 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3852443 (_44734 : int) : (term419 _44734) = (term413 _44734).
Proof. exact (MK_COMB (@lem3852442) (@lem3852441 _44734)). Qed.
Lemma lem3852444 : term114 = term114.
Proof. exact (eq_refl term114). Qed.
Lemma lem3852445 (_44734 : int) : (term417 _44734) = (term414 _44734).
Proof. exact (MK_COMB (@lem3852443 _44734) (@lem3852444)). Qed.
Lemma lem3852446 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term456 _44735 _44736 _44734 _44737) : term414 _44734.
Proof. exact (EQ_MP (@lem3852445 _44734) (@lem3852440 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3852447 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term456 _44735 _44736 _44734 _44737) : term484 _44734.
Proof. exact (conj (@lem3852446 _44735 _44736 _44734 _44737 h1) (@lem3851990 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3852449 (x : real) (y : real) : term421 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem3852450 (_44734 : int) : term485 _44734.
Proof. exact (@lem3852449 (term208 _44734) (term380 _44734)). Qed.
Lemma lem3852451 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term456 _44735 _44736 _44734 _44737) : term486 _44734.
Proof. exact (@lem3852450 _44734 (@lem3852447 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3852452 (_44734 : int) : (term487 _44734) = (term488 _44734).
Proof. exact (@lem1982753 (term190 _44734) (real_of_int _44734) term163 term163). Qed.
Lemma lem3852453 (_44734 : int) : (term364 _44734) = (term342 _44734).
Proof. exact (@lem1982713 term163 (real_of_int _44734)). Qed.
Lemma lem3852455 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3852456 : term128 = term198.
Proof. exact (@lem3852455 term129). Qed.
Lemma lem3852458 (x : nat) : (term161 x) = (term162 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3852459 : term163 = term164.
Proof. exact (@lem3852458 term129). Qed.
Lemma lem3852460 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3852461 : term343 = term344.
Proof. exact (MK_COMB (@lem3852460) (@lem3852459)). Qed.
Lemma lem3852462 : term345 = term346.
Proof. exact (MK_COMB (@lem3852461) (@lem3852456)). Qed.
Lemma lem3852463 : term347.
Proof. exact (@lem1981473 term163 term128 term128 term128 term114 term128). Qed.
Lemma lem3852465 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3852466 : term303 = term309.
Proof. exact (@lem3852465 (NUMERAL 0) term129). Qed.
Lemma lem3852467 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3852468 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3852469 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3852468 h1) (fun h1 : term309 = True => @lem3852467)). Qed.
Lemma lem3852470 : term309 = True.
Proof. exact (EQ_MP (@lem3852469) (@lem3852467)). Qed.
Lemma lem3852471 : term303 = True.
Proof. exact (TRANS (@lem3852466) (@lem3852470)). Qed.
Lemma lem3852472 : True = term303.
Proof. exact (SYM (@lem3852471)). Qed.
Lemma lem3852473 : term303.
Proof. exact (EQ_MP (@lem3852472) (@lem0)). Qed.
Lemma lem3852474 : term348.
Proof. exact (@lem3852463 (@lem3852473)). Qed.
Lemma lem3852476 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3852477 : term303 = term309.
Proof. exact (@lem3852476 (NUMERAL 0) term129). Qed.
Lemma lem3852478 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3852479 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3852480 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3852479 h1) (fun h1 : term309 = True => @lem3852478)). Qed.
Lemma lem3852481 : term309 = True.
Proof. exact (EQ_MP (@lem3852480) (@lem3852478)). Qed.
Lemma lem3852482 : term303 = True.
Proof. exact (TRANS (@lem3852477) (@lem3852481)). Qed.
Lemma lem3852483 : True = term303.
Proof. exact (SYM (@lem3852482)). Qed.
Lemma lem3852484 : term303.
Proof. exact (EQ_MP (@lem3852483) (@lem0)). Qed.
Lemma lem3852485 : term349.
Proof. exact (@lem3852474 (@lem3852484)). Qed.
Lemma lem3852487 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3852488 : term303 = term309.
Proof. exact (@lem3852487 (NUMERAL 0) term129). Qed.
Lemma lem3852489 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3852490 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3852491 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3852490 h1) (fun h1 : term309 = True => @lem3852489)). Qed.
Lemma lem3852492 : term309 = True.
Proof. exact (EQ_MP (@lem3852491) (@lem3852489)). Qed.
Lemma lem3852493 : term303 = True.
Proof. exact (TRANS (@lem3852488) (@lem3852492)). Qed.
Lemma lem3852494 : True = term303.
Proof. exact (SYM (@lem3852493)). Qed.
Lemma lem3852495 : term303.
Proof. exact (EQ_MP (@lem3852494) (@lem0)). Qed.
Lemma lem3852496 : term350.
Proof. exact (@lem3852485 (@lem3852495)). Qed.
Lemma lem3852498 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3852499 : term172 = term173.
Proof. exact (@lem3852498 term129 term129). Qed.
Lemma lem3852500 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3852501 : term175 = term129.
Proof. exact (EQ_MP (@lem3852500) (@lem940073)). Qed.
Lemma lem3852502 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3852503 : term173 = term128.
Proof. exact (MK_COMB (@lem3852502) (@lem3852501)). Qed.
Lemma lem3852504 : term172 = term128.
Proof. exact (TRANS (@lem3852499) (@lem3852503)). Qed.
Lemma lem3852506 (m : nat) (n : nat) : (term202 m n) = (term203 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3852507 : term199 = term204.
Proof. exact (@lem3852506 term129 term129). Qed.
Lemma lem3852508 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3852509 : term175 = term129.
Proof. exact (EQ_MP (@lem3852508) (@lem940073)). Qed.
Lemma lem3852510 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3852511 : term173 = term128.
Proof. exact (MK_COMB (@lem3852510) (@lem3852509)). Qed.
Lemma lem3852512 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3852513 : term204 = term163.
Proof. exact (MK_COMB (@lem3852512) (@lem3852511)). Qed.
Lemma lem3852514 : term199 = term163.
Proof. exact (TRANS (@lem3852507) (@lem3852513)). Qed.
Lemma lem3852515 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3852516 : term351 = term343.
Proof. exact (MK_COMB (@lem3852515) (@lem3852514)). Qed.
Lemma lem3852517 : term352 = term345.
Proof. exact (MK_COMB (@lem3852516) (@lem3852504)). Qed.
Lemma lem3852519 (m : nat) : (term353 m) = term114.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3852520 : term345 = term114.
Proof. exact (@lem3852519 term129). Qed.
Lemma lem3852521 : term352 = term114.
Proof. exact (TRANS (@lem3852517) (@lem3852520)). Qed.
Lemma lem3852522 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3852523 : term354 = term355.
Proof. exact (MK_COMB (@lem3852522) (@lem3852521)). Qed.
Lemma lem3852524 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem3852525 : term356 = term314.
Proof. exact (MK_COMB (@lem3852523) (@lem3852524)). Qed.
Lemma lem3852527 (x : nat) : (term313 x) = term114.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3852528 : term314 = term114.
Proof. exact (@lem3852527 term129). Qed.
Lemma lem3852529 : term356 = term114.
Proof. exact (TRANS (@lem3852525) (@lem3852528)). Qed.
Lemma lem3852531 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3852532 : term172 = term173.
Proof. exact (@lem3852531 term129 term129). Qed.
Lemma lem3852533 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3852534 : term175 = term129.
Proof. exact (EQ_MP (@lem3852533) (@lem940073)). Qed.
Lemma lem3852535 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3852536 : term173 = term128.
Proof. exact (MK_COMB (@lem3852535) (@lem3852534)). Qed.
Lemma lem3852537 : term172 = term128.
Proof. exact (TRANS (@lem3852532) (@lem3852536)). Qed.
Lemma lem3852538 : term355 = term355.
Proof. exact (eq_refl term355). Qed.
Lemma lem3852539 : term357 = term314.
Proof. exact (MK_COMB (@lem3852538) (@lem3852537)). Qed.
Lemma lem3852541 (x : nat) : (term313 x) = term114.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3852542 : term314 = term114.
Proof. exact (@lem3852541 term129). Qed.
Lemma lem3852543 : term357 = term114.
Proof. exact (TRANS (@lem3852539) (@lem3852542)). Qed.
Lemma lem3852544 : term114 = term357.
Proof. exact (SYM (@lem3852543)). Qed.
Lemma lem3852545 : term356 = term357.
Proof. exact (TRANS (@lem3852529) (@lem3852544)). Qed.
Lemma lem3852546 : term346 = term160.
Proof. exact (@lem3852496 (@lem3852545)). Qed.
Lemma lem3852547 : term345 = term160.
Proof. exact (TRANS (@lem3852462) (@lem3852546)). Qed.
Lemma lem3852549 (x : real) : (term179 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3852550 : term160 = term114.
Proof. exact (@lem3852549 term114). Qed.
Lemma lem3852551 : term345 = term114.
Proof. exact (TRANS (@lem3852547) (@lem3852550)). Qed.
Lemma lem3852552 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3852553 : term358 = term355.
Proof. exact (MK_COMB (@lem3852552) (@lem3852551)). Qed.
Lemma lem3852554 (_44734 : int) : (real_of_int _44734) = (real_of_int _44734).
Proof. exact (eq_refl (real_of_int _44734)). Qed.
Lemma lem3852555 (_44734 : int) : (term342 _44734) = (term359 _44734).
Proof. exact (MK_COMB (@lem3852553) (@lem3852554 _44734)). Qed.
Lemma lem3852556 (_44734 : int) : (term364 _44734) = (term359 _44734).
Proof. exact (TRANS (@lem3852453 _44734) (@lem3852555 _44734)). Qed.
Lemma lem3852557 (_44734 : int) : (term359 _44734) = term114.
Proof. exact (@lem1982719 (real_of_int _44734)). Qed.
Lemma lem3852558 (_44734 : int) : (term364 _44734) = term114.
Proof. exact (TRANS (@lem3852556 _44734) (@lem3852557 _44734)). Qed.
Lemma lem3852559 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3852560 (_44734 : int) : (term365 _44734) = term361.
Proof. exact (MK_COMB (@lem3852559) (@lem3852558 _44734)). Qed.
Lemma lem3852562 (x : nat) : (term161 x) = (term162 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3852563 : term163 = term164.
Proof. exact (@lem3852562 term129). Qed.
Lemma lem3852565 (x : nat) : (term161 x) = (term162 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3852566 : term163 = term164.
Proof. exact (@lem3852565 term129). Qed.
Lemma lem3852567 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3852568 : term343 = term344.
Proof. exact (MK_COMB (@lem3852567) (@lem3852566)). Qed.
Lemma lem3852569 : term489 = term490.
Proof. exact (MK_COMB (@lem3852568) (@lem3852563)). Qed.
Lemma lem3852570 : term491.
Proof. exact (@lem1981473 term163 term128 term163 term128 term492 term128). Qed.
Lemma lem3852572 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3852573 : term303 = term309.
Proof. exact (@lem3852572 (NUMERAL 0) term129). Qed.
Lemma lem3852574 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3852575 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3852576 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3852575 h1) (fun h1 : term309 = True => @lem3852574)). Qed.
Lemma lem3852577 : term309 = True.
Proof. exact (EQ_MP (@lem3852576) (@lem3852574)). Qed.
Lemma lem3852578 : term303 = True.
Proof. exact (TRANS (@lem3852573) (@lem3852577)). Qed.
Lemma lem3852579 : True = term303.
Proof. exact (SYM (@lem3852578)). Qed.
Lemma lem3852580 : term303.
Proof. exact (EQ_MP (@lem3852579) (@lem0)). Qed.
Lemma lem3852581 : term493.
Proof. exact (@lem3852570 (@lem3852580)). Qed.
Lemma lem3852583 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3852584 : term303 = term309.
Proof. exact (@lem3852583 (NUMERAL 0) term129). Qed.
Lemma lem3852585 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3852586 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3852587 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3852586 h1) (fun h1 : term309 = True => @lem3852585)). Qed.
Lemma lem3852588 : term309 = True.
Proof. exact (EQ_MP (@lem3852587) (@lem3852585)). Qed.
Lemma lem3852589 : term303 = True.
Proof. exact (TRANS (@lem3852584) (@lem3852588)). Qed.
Lemma lem3852590 : True = term303.
Proof. exact (SYM (@lem3852589)). Qed.
Lemma lem3852591 : term303.
Proof. exact (EQ_MP (@lem3852590) (@lem0)). Qed.
Lemma lem3852592 : term494.
Proof. exact (@lem3852581 (@lem3852591)). Qed.
Lemma lem3852594 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3852595 : term303 = term309.
Proof. exact (@lem3852594 (NUMERAL 0) term129). Qed.
Lemma lem3852596 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3852597 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3852598 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3852597 h1) (fun h1 : term309 = True => @lem3852596)). Qed.
Lemma lem3852599 : term309 = True.
Proof. exact (EQ_MP (@lem3852598) (@lem3852596)). Qed.
Lemma lem3852600 : term303 = True.
Proof. exact (TRANS (@lem3852595) (@lem3852599)). Qed.
Lemma lem3852601 : True = term303.
Proof. exact (SYM (@lem3852600)). Qed.
Lemma lem3852602 : term303.
Proof. exact (EQ_MP (@lem3852601) (@lem0)). Qed.
Lemma lem3852603 : term495.
Proof. exact (@lem3852592 (@lem3852602)). Qed.
Lemma lem3852605 (m : nat) (n : nat) : (term202 m n) = (term203 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3852606 : term199 = term204.
Proof. exact (@lem3852605 term129 term129). Qed.
Lemma lem3852607 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3852608 : term175 = term129.
Proof. exact (EQ_MP (@lem3852607) (@lem940073)). Qed.
Lemma lem3852609 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3852610 : term173 = term128.
Proof. exact (MK_COMB (@lem3852609) (@lem3852608)). Qed.
Lemma lem3852611 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3852612 : term204 = term163.
Proof. exact (MK_COMB (@lem3852611) (@lem3852610)). Qed.
Lemma lem3852613 : term199 = term163.
Proof. exact (TRANS (@lem3852606) (@lem3852612)). Qed.
Lemma lem3852615 (m : nat) (n : nat) : (term202 m n) = (term203 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3852616 : term199 = term204.
Proof. exact (@lem3852615 term129 term129). Qed.
Lemma lem3852617 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3852618 : term175 = term129.
Proof. exact (EQ_MP (@lem3852617) (@lem940073)). Qed.
Lemma lem3852619 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3852620 : term173 = term128.
Proof. exact (MK_COMB (@lem3852619) (@lem3852618)). Qed.
Lemma lem3852621 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3852622 : term204 = term163.
Proof. exact (MK_COMB (@lem3852621) (@lem3852620)). Qed.
Lemma lem3852623 : term199 = term163.
Proof. exact (TRANS (@lem3852616) (@lem3852622)). Qed.
Lemma lem3852624 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3852625 : term351 = term343.
Proof. exact (MK_COMB (@lem3852624) (@lem3852623)). Qed.
Lemma lem3852626 : term496 = term489.
Proof. exact (MK_COMB (@lem3852625) (@lem3852613)). Qed.
Lemma lem3852627 : term489 = term497.
Proof. exact (@lem1367763 term129 term129). Qed.
Lemma lem3852628 : term498 = term499.
Proof. exact (@lem706885). Qed.
Lemma lem3852629 : (term498 = term499) = (term500 = term501).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term499). Qed.
Lemma lem3852630 : term500 = term501.
Proof. exact (EQ_MP (@lem3852629) (@lem3852628)). Qed.
Lemma lem3852631 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3852632 : term502 = term503.
Proof. exact (MK_COMB (@lem3852631) (@lem3852630)). Qed.
Lemma lem3852633 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3852634 : term497 = term492.
Proof. exact (MK_COMB (@lem3852633) (@lem3852632)). Qed.
Lemma lem3852635 : term489 = term492.
Proof. exact (TRANS (@lem3852627) (@lem3852634)). Qed.
Lemma lem3852636 : term496 = term492.
Proof. exact (TRANS (@lem3852626) (@lem3852635)). Qed.
Lemma lem3852637 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3852638 : term504 = term505.
Proof. exact (MK_COMB (@lem3852637) (@lem3852636)). Qed.
Lemma lem3852639 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem3852640 : term506 = term507.
Proof. exact (MK_COMB (@lem3852638) (@lem3852639)). Qed.
Lemma lem3852642 (m : nat) (n : nat) : (term202 m n) = (term203 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3852643 : term507 = term508.
Proof. exact (@lem3852642 term501 term129). Qed.
Lemma lem3852644 : term509 = term499.
Proof. exact (@lem996237 term499). Qed.
Lemma lem3852645 : (term509 = term499) = (term510 = term501).
Proof. exact (@lem1007663 term499 (BIT1 0) term499). Qed.
Lemma lem3852646 : term510 = term501.
Proof. exact (EQ_MP (@lem3852645) (@lem3852644)). Qed.
Lemma lem3852647 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3852648 : term511 = term503.
Proof. exact (MK_COMB (@lem3852647) (@lem3852646)). Qed.
Lemma lem3852649 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3852650 : term508 = term492.
Proof. exact (MK_COMB (@lem3852649) (@lem3852648)). Qed.
Lemma lem3852651 : term507 = term492.
Proof. exact (TRANS (@lem3852643) (@lem3852650)). Qed.
Lemma lem3852652 : term506 = term492.
Proof. exact (TRANS (@lem3852640) (@lem3852651)). Qed.
Lemma lem3852654 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3852655 : term172 = term173.
Proof. exact (@lem3852654 term129 term129). Qed.
Lemma lem3852656 : (term174 = (BIT1 0)) = (term175 = term129).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3852657 : term175 = term129.
Proof. exact (EQ_MP (@lem3852656) (@lem940073)). Qed.
Lemma lem3852658 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3852659 : term173 = term128.
Proof. exact (MK_COMB (@lem3852658) (@lem3852657)). Qed.
Lemma lem3852660 : term172 = term128.
Proof. exact (TRANS (@lem3852655) (@lem3852659)). Qed.
Lemma lem3852661 : term505 = term505.
Proof. exact (eq_refl term505). Qed.
Lemma lem3852662 : term512 = term507.
Proof. exact (MK_COMB (@lem3852661) (@lem3852660)). Qed.
Lemma lem3852664 (m : nat) (n : nat) : (term202 m n) = (term203 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3852665 : term507 = term508.
Proof. exact (@lem3852664 term501 term129). Qed.
Lemma lem3852666 : term509 = term499.
Proof. exact (@lem996237 term499). Qed.
Lemma lem3852667 : (term509 = term499) = (term510 = term501).
Proof. exact (@lem1007663 term499 (BIT1 0) term499). Qed.
Lemma lem3852668 : term510 = term501.
Proof. exact (EQ_MP (@lem3852667) (@lem3852666)). Qed.
Lemma lem3852669 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3852670 : term511 = term503.
Proof. exact (MK_COMB (@lem3852669) (@lem3852668)). Qed.
Lemma lem3852671 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3852672 : term508 = term492.
Proof. exact (MK_COMB (@lem3852671) (@lem3852670)). Qed.
Lemma lem3852673 : term507 = term492.
Proof. exact (TRANS (@lem3852665) (@lem3852672)). Qed.
Lemma lem3852674 : term512 = term492.
Proof. exact (TRANS (@lem3852662) (@lem3852673)). Qed.
Lemma lem3852675 : term492 = term512.
Proof. exact (SYM (@lem3852674)). Qed.
Lemma lem3852676 : term506 = term512.
Proof. exact (TRANS (@lem3852652) (@lem3852675)). Qed.
Lemma lem3852677 : term490 = term513.
Proof. exact (@lem3852603 (@lem3852676)). Qed.
Lemma lem3852678 : term489 = term513.
Proof. exact (TRANS (@lem3852569) (@lem3852677)). Qed.
Lemma lem3852680 (x : real) : (term179 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3852681 : term513 = term492.
Proof. exact (@lem3852680 term492). Qed.
Lemma lem3852682 : term489 = term492.
Proof. exact (TRANS (@lem3852678) (@lem3852681)). Qed.
Lemma lem3852683 (_44734 : int) : (term488 _44734) = term514.
Proof. exact (MK_COMB (@lem3852560 _44734) (@lem3852682)). Qed.
Lemma lem3852684 (_44734 : int) : (term487 _44734) = term514.
Proof. exact (TRANS (@lem3852452 _44734) (@lem3852683 _44734)). Qed.
Lemma lem3852685 : term514 = term492.
Proof. exact (@lem1982721 term492). Qed.
Lemma lem3852686 (_44734 : int) : (term487 _44734) = term492.
Proof. exact (TRANS (@lem3852684 _44734) (@lem3852685)). Qed.
Lemma lem3852687 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3852688 (_44734 : int) : (term515 _44734) = term516.
Proof. exact (MK_COMB (@lem3852687) (@lem3852686 _44734)). Qed.
Lemma lem3852689 : term114 = term114.
Proof. exact (eq_refl term114). Qed.
Lemma lem3852690 (_44734 : int) : (term486 _44734) = term517.
Proof. exact (MK_COMB (@lem3852688 _44734) (@lem3852689)). Qed.
Lemma lem3852691 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term456 _44735 _44736 _44734 _44737) : term517.
Proof. exact (EQ_MP (@lem3852690 _44734) (@lem3852451 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3852693 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3852694 : term517 = term518.
Proof. exact (@lem3852693 term114 term492). Qed.
Lemma lem3852696 (x : nat) : (term161 x) = (term162 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3852697 : term492 = term513.
Proof. exact (@lem3852696 term501). Qed.
Lemma lem3852699 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3852700 : term114 = term160.
Proof. exact (@lem3852699 (NUMERAL 0)). Qed.
Lemma lem3852701 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3852702 : term116 = term388.
Proof. exact (MK_COMB (@lem3852701) (@lem3852700)). Qed.
Lemma lem3852703 : term518 = term519.
Proof. exact (MK_COMB (@lem3852702) (@lem3852697)). Qed.
Lemma lem3852704 : term520.
Proof. exact (@lem1980026 term114 term128 term492 term128). Qed.
Lemma lem3852706 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3852707 : term303 = term309.
Proof. exact (@lem3852706 (NUMERAL 0) term129). Qed.
Lemma lem3852708 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3852709 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3852710 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3852709 h1) (fun h1 : term309 = True => @lem3852708)). Qed.
Lemma lem3852711 : term309 = True.
Proof. exact (EQ_MP (@lem3852710) (@lem3852708)). Qed.
Lemma lem3852712 : term303 = True.
Proof. exact (TRANS (@lem3852707) (@lem3852711)). Qed.
Lemma lem3852713 : True = term303.
Proof. exact (SYM (@lem3852712)). Qed.
Lemma lem3852714 : term303.
Proof. exact (EQ_MP (@lem3852713) (@lem0)). Qed.
Lemma lem3852715 : term521.
Proof. exact (@lem3852704 (@lem3852714)). Qed.
Lemma lem3852717 (m : nat) (n : nat) : (term308 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3852718 : term303 = term309.
Proof. exact (@lem3852717 (NUMERAL 0) term129). Qed.
Lemma lem3852719 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3852720 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3852721 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem3852720 h1) (fun h1 : term309 = True => @lem3852719)). Qed.
Lemma lem3852722 : term309 = True.
Proof. exact (EQ_MP (@lem3852721) (@lem3852719)). Qed.
Lemma lem3852723 : term303 = True.
Proof. exact (TRANS (@lem3852718) (@lem3852722)). Qed.
Lemma lem3852724 : True = term303.
Proof. exact (SYM (@lem3852723)). Qed.
Lemma lem3852725 : term303.
Proof. exact (EQ_MP (@lem3852724) (@lem0)). Qed.
Lemma lem3852726 : term519 = term522.
Proof. exact (@lem3852715 (@lem3852725)). Qed.
Lemma lem3852728 (m : nat) (n : nat) : (term202 m n) = (term203 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3852729 : term507 = term508.
Proof. exact (@lem3852728 term501 term129). Qed.
Lemma lem3852730 : term509 = term499.
Proof. exact (@lem996237 term499). Qed.
Lemma lem3852731 : (term509 = term499) = (term510 = term501).
Proof. exact (@lem1007663 term499 (BIT1 0) term499). Qed.
Lemma lem3852732 : term510 = term501.
Proof. exact (EQ_MP (@lem3852731) (@lem3852730)). Qed.
Lemma lem3852733 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3852734 : term511 = term503.
Proof. exact (MK_COMB (@lem3852733) (@lem3852732)). Qed.
Lemma lem3852735 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3852736 : term508 = term492.
Proof. exact (MK_COMB (@lem3852735) (@lem3852734)). Qed.
Lemma lem3852737 : term507 = term492.
Proof. exact (TRANS (@lem3852729) (@lem3852736)). Qed.
Lemma lem3852739 (x : nat) : (term313 x) = term114.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3852740 : term314 = term114.
Proof. exact (@lem3852739 term129). Qed.
Lemma lem3852741 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3852742 : term393 = term116.
Proof. exact (MK_COMB (@lem3852741) (@lem3852740)). Qed.
Lemma lem3852743 : term522 = term518.
Proof. exact (MK_COMB (@lem3852742) (@lem3852737)). Qed.
Lemma lem3852745 (m : nat) (n : nat) : (term394 m n) = (term395 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3852746 : term518 = term523.
Proof. exact (@lem3852745 (NUMERAL 0) term501). Qed.
Lemma lem3852747 : term524 = term499.
Proof. exact (@lem912803). Qed.
Lemma lem3852748 (h1 : term524 = term499) : (term501 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 (BIT1 0) 0 term499 h1). Qed.
Lemma lem3852749 : (term524 = term499) = ((term501 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term524 = term499 => @lem3852748 h1) (fun h1 : (term501 = (NUMERAL 0)) = False => @lem3852747)). Qed.
Lemma lem3852750 : (term501 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3852749) (@lem3852747)). Qed.
Lemma lem3852751 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3852752 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3852753 : term397 = (and True).
Proof. exact (MK_COMB (@lem3852752) (@lem3852751)). Qed.
Lemma lem3852754 : term523 = (True /\ False).
Proof. exact (MK_COMB (@lem3852753) (@lem3852750)). Qed.
Lemma lem3852756 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3852757 : term523 = False.
Proof. exact (TRANS (@lem3852754) (@lem3852756)). Qed.
Lemma lem3852758 : term518 = False.
Proof. exact (TRANS (@lem3852746) (@lem3852757)). Qed.
Lemma lem3852759 : term522 = False.
Proof. exact (TRANS (@lem3852743) (@lem3852758)). Qed.
Lemma lem3852760 : term519 = False.
Proof. exact (TRANS (@lem3852726) (@lem3852759)). Qed.
Lemma lem3852761 : term518 = False.
Proof. exact (TRANS (@lem3852703) (@lem3852760)). Qed.
Lemma lem3852762 : term517 = False.
Proof. exact (TRANS (@lem3852694) (@lem3852761)). Qed.
Lemma lem3852763 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term456 _44735 _44736 _44734 _44737) : False.
Proof. exact (EQ_MP (@lem3852762) (@lem3852691 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3852764 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term291 _44735 _44736 _44734 _44737) : False.
Proof. exact (or_elim (@lem3850902 _44735 _44736 _44734 _44737 h1) (fun h0 : term426 _44735 _44736 _44734 _44737 => @lem3851686 _44735 _44736 _44734 _44737 h0) (fun h0 : term456 _44735 _44736 _44734 _44737 => @lem3852763 _44735 _44736 _44734 _44737 h0)). Qed.
Lemma lem3852765 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term300 _44735 _44736 _44734 _44737) : False.
Proof. exact (or_elim (@lem3849590 _44735 _44736 _44734 _44737 h1) (fun h0 : term295 _44735 _44736 _44734 _44737 => @lem3850901 _44735 _44736 _44734 _44737 h0) (fun h0 : term291 _44735 _44736 _44734 _44737 => @lem3852764 _44735 _44736 _44734 _44737 h0)). Qed.
Lemma lem3852767 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term300 _44735 _44736 _44734 _44737) : term300 _44735 _44736 _44734 _44737.
Proof. exact (h1). Qed.
Lemma lem3852768 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term300 _44735 _44736 _44734 _44737) : (term300 _44735 _44736 _44734 _44737) = False.
Proof. exact (prop_ext (fun h2 : term300 _44735 _44736 _44734 _44737 => @lem3852765 _44735 _44736 _44734 _44737 h1) (fun h2 : False => @lem3852767 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3852769 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) (h1 : term300 _44735 _44736 _44734 _44737) : False.
Proof. exact (EQ_MP (@lem3852768 _44735 _44736 _44734 _44737 h1) (@lem3852767 _44735 _44736 _44734 _44737 h1)). Qed.
Lemma lem3852770 (_44735 : int) (_44736 : int) (_44737 : int) (_44734 : int) (h1 : term155 _44735 _44736 _44737 _44734) : term155 _44735 _44736 _44737 _44734.
Proof. exact (h1). Qed.
Lemma lem3852771 (_44735 : int) (_44736 : int) (_44737 : int) (_44734 : int) (h1 : term155 _44735 _44736 _44737 _44734) : term300 _44735 _44736 _44734 _44737.
Proof. exact (EQ_MP (@lem3849568 _44735 _44736 _44734 _44737) (@lem3852770 _44735 _44736 _44737 _44734 h1)). Qed.
Lemma lem3852772 (_44735 : int) (_44736 : int) (_44737 : int) (_44734 : int) (h1 : term155 _44735 _44736 _44737 _44734) : (term300 _44735 _44736 _44734 _44737) = False.
Proof. exact (prop_ext (fun h2 : term300 _44735 _44736 _44734 _44737 => @lem3852769 _44735 _44736 _44734 _44737 h2) (fun h2 : False => @lem3852771 _44735 _44736 _44737 _44734 h1)). Qed.
Lemma lem3852773 (_44735 : int) (_44736 : int) (_44737 : int) (_44734 : int) (h1 : term155 _44735 _44736 _44737 _44734) : False.
Proof. exact (EQ_MP (@lem3852772 _44735 _44736 _44737 _44734 h1) (@lem3852771 _44735 _44736 _44737 _44734 h1)). Qed.
Lemma lem3852774 (_44735 : int) (_44736 : int) (_44737 : int) (_44734 : int) : term525 _44735 _44736 _44737 _44734.
Proof. exact (fun h0 : term155 _44735 _44736 _44737 _44734 => @lem3852773 _44735 _44736 _44737 _44734 h0). Qed.
Lemma lem3852775 (_44735 : int) (_44736 : int) (_44737 : int) (_44734 : int) : term526 _44735 _44736 _44737 _44734.
Proof. exact (@lem1386578 (term527 _44735 _44736 _44737 _44734)). Qed.
Lemma lem3852778 (_44735 : int) (_44736 : int) (_44737 : int) (_44734 : int) : term527 _44735 _44736 _44737 _44734.
Proof. exact (@lem3852775 _44735 _44736 _44737 _44734 (@lem3852774 _44735 _44736 _44737 _44734)). Qed.
Lemma lem3852779 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term153 _44735 _44736 _44737 _44734) = (term108 _44735 _44736 _44734 _44737).
Proof. exact (SYM (@lem3848777 _44735 _44736 _44737 _44734)). Qed.
Lemma lem3852780 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3852781 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : (term527 _44735 _44736 _44737 _44734) = (term58 _44735 _44736 _44734 _44737).
Proof. exact (MK_COMB (@lem3852780) (@lem3852779 _44735 _44736 _44734 _44737)). Qed.
Lemma lem3852782 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : term58 _44735 _44736 _44734 _44737.
Proof. exact (EQ_MP (@lem3852781 _44735 _44736 _44734 _44737) (@lem3852778 _44735 _44736 _44737 _44734)). Qed.
Lemma lem3852783 (_44735 : int) (_44736 : int) (_44734 : int) (_44737 : int) : term59 _44735 _44736 _44734 _44737.
Proof. exact (EQ_MP (@lem3848482 _44735 _44736 _44734 _44737) (@lem3852782 _44735 _44736 _44734 _44737)). Qed.
Lemma lem3852784 (b : nat) (c : nat) (a : nat) (d : nat) : term528 b c a d.
Proof. exact (@lem3852783 (int_of_num b) (int_of_num c) (int_of_num a) (int_of_num d)). Qed.
Lemma lem3852785 (b : nat) (c : nat) (a : nat) (d : nat) : term529 b c a d.
Proof. exact (@lem3852784 b c a d (@lem3848472 a)). Qed.
Lemma lem3852786 (b : nat) (c : nat) (a : nat) (d : nat) : term530 b c a d.
Proof. exact (@lem3852785 b c a d (@lem3848475 b)). Qed.
Lemma lem3852787 (b : nat) (c : nat) (a : nat) (d : nat) : term531 b c a d.
Proof. exact (@lem3852786 b c a d (@lem3848478 c)). Qed.
Lemma lem3852788 (b : nat) (c : nat) (a : nat) (d : nat) : term53 b c a d.
Proof. exact (@lem3852787 b c a d (@lem3848481 d)). Qed.
Lemma lem3852789 (b : nat) (c : nat) (a : nat) : term55 b c a.
Proof. exact (fun d : nat => @lem3852788 b c a d). Qed.
Lemma lem3852790 (a : nat) (c : nat) (b : nat) : (term55 b c a) = (term11 a c b).
Proof. exact (SYM (@lem3848469 b c a)). Qed.
Lemma lem3852791 (a : nat) (c : nat) (b : nat) : term11 a c b.
Proof. exact (EQ_MP (@lem3852790 a c b) (@lem3852789 b c a)). Qed.
Lemma lem3852792 (a : nat) (c : nat) (b : nat) (h1 : term11 a c b) : term11 a c b.
Proof. exact (h1). Qed.
Lemma lem3852793 (a : nat) (b : nat) (c : nat) (h1 : (Nat.add a b) = c) : (Nat.add a b) = c.
Proof. exact (h1). Qed.
Lemma lem3852794 (a : nat) (c : nat) (b : nat) (h1 : (Nat.add a b) = c) (h2 : term11 a c b) : a = (Nat.sub c b).
Proof. exact (@lem3852792 a c b h2 (@lem3852793 a b c h1)). Qed.
Lemma lem3852795 (a : nat) (b : nat) (c : nat) (h1 : (Nat.add a b) = c) : term532 a c b.
Proof. exact (fun h0 : term11 a c b => @lem3852794 a c b h1 h0). Qed.
Lemma lem3852796 (a : nat) (c : nat) (b : nat) (h1 : term11 a c b) : term11 a c b.
Proof. exact (h1). Qed.
Lemma lem3852797 (a : nat) (c : nat) (b : nat) (h1 : (Nat.add a b) = c) (h2 : term11 a c b) : a = (Nat.sub c b).
Proof. exact (@lem3852795 a b c h1 (@lem3852796 a c b h2)). Qed.
Lemma lem3852798 (a : nat) (c : nat) (b : nat) (h1 : term11 a c b) : term11 a c b.
Proof. exact (fun h0 : (Nat.add a b) = c => @lem3852797 a c b h0 h1). Qed.
Lemma lem3852799 (a : nat) (c : nat) (b : nat) : term533 a c b.
Proof. exact (fun h0 : term11 a c b => @lem3852798 a c b h0). Qed.
Lemma lem3852801 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (h1 : term534 _99873 t s) : term534 _99873 t s.
Proof. exact (h1). Qed.
Lemma lem3852802 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (h1 : @SUBSET _99873 t s) : @SUBSET _99873 t s.
Proof. exact (h1). Qed.
Lemma lem3852803 {_99873 : Type'} (s : _99873 -> Prop) (h1 : @FINITE _99873 s) : @FINITE _99873 s.
Proof. exact (h1). Qed.
Lemma lem3852805 (a : nat) (c : nat) (b : nat) : term11 a c b.
Proof. exact (@lem3852799 a c b (@lem3852791 a c b)). Qed.
Lemma lem3852806 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) : term535 _99873 s t.
Proof. exact (@lem3852805 (term536 _99873 s t) (@CARD _99873 s) (@CARD _99873 t)). Qed.
Lemma lem3852808 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) : term6 _99816 s t u.
Proof. exact (EQ_MP (@lem3848275 _99816 s t u) (@lem3848274 _99816 s t u)). Qed.
Lemma lem3852809 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) (u : _99873 -> Prop) : term6 _99873 s t u.
Proof. exact (@lem3852808 _99873 s t u). Qed.
Lemma lem3852810 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : term537 _99873 t s.
Proof. exact (@lem3852809 _99873 (@DIFF _99873 s t) t s). Qed.
Lemma lem3852811 {_99873 : Type'} (s : _99873 -> Prop) : (@FINITE _99873 s) = ((@FINITE _99873 s) = True).
Proof. exact (@lem7 (@FINITE _99873 s)). Qed.
Lemma lem3852818 {_99873 : Type'} (s : _99873 -> Prop) (h1 : @FINITE _99873 s) : (@FINITE _99873 s) = True.
Proof. exact (EQ_MP (@lem3852811 _99873 s) (@lem3852803 _99873 s h1)). Qed.
Lemma lem3852819 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3852820 {_99873 : Type'} (s : _99873 -> Prop) (h1 : @FINITE _99873 s) : (term538 _99873 s) = (and True).
Proof. exact (MK_COMB (@lem3852819) (@lem3852818 _99873 s h1)). Qed.
Lemma lem3852827 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term539 _99873 t s) = (term539 _99873 t s).
Proof. exact (eq_refl (term539 _99873 t s)). Qed.
Lemma lem3852828 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (h1 : @FINITE _99873 s) : (term540 _99873 t s) = (term541 _99873 t s).
Proof. exact (MK_COMB (@lem3852820 _99873 s h1) (@lem3852827 _99873 t s)). Qed.
Lemma lem3852830 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3852831 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term541 _99873 t s) = (term539 _99873 t s).
Proof. exact (@lem3852830 (term539 _99873 t s)). Qed.
Lemma lem3852838 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (h1 : @FINITE _99873 s) : (term540 _99873 t s) = (term539 _99873 t s).
Proof. exact (TRANS (@lem3852828 _99873 t s h1) (@lem3852831 _99873 t s)). Qed.
Lemma lem3852839 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (h1 : @FINITE _99873 s) : (term539 _99873 t s) = (term540 _99873 t s).
Proof. exact (SYM (@lem3852838 _99873 t s h1)). Qed.
Lemma lem3852850 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (h1 : @FINITE _99873 s) (h2 : @SUBSET _99873 t s) : term542 _99873 t s.
Proof. exact (conj (@lem3852802 _99873 t s h2) (@lem3852803 _99873 s h1)). Qed.
Lemma lem3852856 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term543 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3852857 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) : (@SUBSET _99873 s t) = (term543 _99873 s t).
Proof. exact (@lem3852856 _99873 s t). Qed.
Lemma lem3852858 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (@SUBSET _99873 t s) = (term543 _99873 t s).
Proof. exact (@lem3852857 _99873 t s). Qed.
Lemma lem3852865 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3852866 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term544 _99873 t s) = (term545 _99873 t s).
Proof. exact (MK_COMB (@lem3852865) (@lem3852858 _99873 t s)). Qed.
Lemma lem3852867 {_99873 : Type'} (s : _99873 -> Prop) : (@FINITE _99873 s) = (@FINITE _99873 s).
Proof. exact (eq_refl (@FINITE _99873 s)). Qed.
Lemma lem3852868 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term542 _99873 t s) = (term546 _99873 t s).
Proof. exact (MK_COMB (@lem3852866 _99873 t s) (@lem3852867 _99873 s)). Qed.
Lemma lem3852871 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3852872 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term547 _99873 t s) = (term548 _99873 t s).
Proof. exact (MK_COMB (@lem3852871) (@lem3852868 _99873 t s)). Qed.
Lemma lem3852878 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term549 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3852879 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) : (s = t) = (term549 _99873 s t).
Proof. exact (@lem3852878 _99873 s t). Qed.
Lemma lem3852880 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) : ((term550 _99873 s t) = (@EMPTY _99873)) = (term551 _99873 s t).
Proof. exact (@lem3852879 _99873 (term550 _99873 s t) (@EMPTY _99873)). Qed.
Lemma lem3852889 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3852890 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) : (term552 _99873 s t) = (term553 _99873 s t).
Proof. exact (MK_COMB (@lem3852889) (@lem3852880 _99873 s t)). Qed.
Lemma lem3852894 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term549 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3852895 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) : (s = t) = (term549 _99873 s t).
Proof. exact (@lem3852894 _99873 s t). Qed.
Lemma lem3852896 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : ((term554 _99873 s t) = s) = (term555 _99873 t s).
Proof. exact (@lem3852895 _99873 (term554 _99873 s t) s). Qed.
Lemma lem3852905 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term539 _99873 t s) = (term556 _99873 t s).
Proof. exact (MK_COMB (@lem3852890 _99873 s t) (@lem3852896 _99873 t s)). Qed.
Lemma lem3852908 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term557 _99873 t s) = (term558 _99873 t s).
Proof. exact (MK_COMB (@lem3852872 _99873 t s) (@lem3852905 _99873 t s)). Qed.
Lemma lem3852911 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term558 _99873 t s) = (term557 _99873 t s).
Proof. exact (SYM (@lem3852908 _99873 t s)). Qed.
Lemma lem3852923 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3852924 {_99873 : Type'} (P : _99873 -> Prop) (x : _99873) : (@IN _99873 x P) = (P x).
Proof. exact (@lem3852923 _99873 P x). Qed.
Lemma lem3852925 {_99873 : Type'} (t : _99873 -> Prop) (x : _99873) : (@IN _99873 x t) = (t x).
Proof. exact (@lem3852924 _99873 t x). Qed.
Lemma lem3852926 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3852927 {_99873 : Type'} (t : _99873 -> Prop) (x : _99873) : (term559 _99873 x t) = (term560 _99873 t x).
Proof. exact (MK_COMB (@lem3852926) (@lem3852925 _99873 t x)). Qed.
Lemma lem3852929 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3852930 {_99873 : Type'} (P : _99873 -> Prop) (x : _99873) : (@IN _99873 x P) = (P x).
Proof. exact (@lem3852929 _99873 P x). Qed.
Lemma lem3852931 {_99873 : Type'} (s : _99873 -> Prop) (x : _99873) : (@IN _99873 x s) = (s x).
Proof. exact (@lem3852930 _99873 s x). Qed.
Lemma lem3852932 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) : (term561 _99873 t x s) = (term562 _99873 t s x).
Proof. exact (MK_COMB (@lem3852927 _99873 t x) (@lem3852931 _99873 s x)). Qed.
Lemma lem3852935 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term563 _99873 t s) = (term564 _99873 t s).
Proof. exact (fun_ext (fun x : _99873 => @lem3852932 _99873 t s x)). Qed.
Lemma lem3852936 {_99873 : Type'} : (@all _99873) = (@all _99873).
Proof. exact (eq_refl (@all _99873)). Qed.
Lemma lem3852937 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term543 _99873 t s) = (term565 _99873 t s).
Proof. exact (MK_COMB (@lem3852936 _99873) (@lem3852935 _99873 t s)). Qed.
Lemma lem3852942 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3852943 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term545 _99873 t s) = (term566 _99873 t s).
Proof. exact (MK_COMB (@lem3852942) (@lem3852937 _99873 t s)). Qed.
Lemma lem3852944 {_99873 : Type'} (s : _99873 -> Prop) : (@FINITE _99873 s) = (@FINITE _99873 s).
Proof. exact (eq_refl (@FINITE _99873 s)). Qed.
Lemma lem3852945 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term546 _99873 t s) = (term567 _99873 t s).
Proof. exact (MK_COMB (@lem3852943 _99873 t s) (@lem3852944 _99873 s)). Qed.
Lemma lem3852948 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3852949 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term548 _99873 t s) = (term568 _99873 t s).
Proof. exact (MK_COMB (@lem3852948) (@lem3852945 _99873 t s)). Qed.
Lemma lem3852959 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term569 A x s t) = (term570 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3852960 {_99873 : Type'} (s : _99873 -> Prop) (x : _99873) (t : _99873 -> Prop) : (term569 _99873 x s t) = (term570 _99873 s x t).
Proof. exact (@lem3852959 _99873 s x t). Qed.
Lemma lem3852961 {_99873 : Type'} (s : _99873 -> Prop) (x : _99873) (t : _99873 -> Prop) : (term571 _99873 x s t) = (term572 _99873 s x t).
Proof. exact (@lem3852960 _99873 (@DIFF _99873 s t) x t). Qed.
Lemma lem3852965 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term573 A x s t) = (term574 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem3852966 {_99873 : Type'} (s : _99873 -> Prop) (x : _99873) (t : _99873 -> Prop) : (term573 _99873 x s t) = (term574 _99873 s x t).
Proof. exact (@lem3852965 _99873 s x t). Qed.
Lemma lem3852970 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3852971 {_99873 : Type'} (P : _99873 -> Prop) (x : _99873) : (@IN _99873 x P) = (P x).
Proof. exact (@lem3852970 _99873 P x). Qed.
Lemma lem3852972 {_99873 : Type'} (s : _99873 -> Prop) (x : _99873) : (@IN _99873 x s) = (s x).
Proof. exact (@lem3852971 _99873 s x). Qed.
Lemma lem3852973 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3852974 {_99873 : Type'} (s : _99873 -> Prop) (x : _99873) : (term575 _99873 x s) = (term576 _99873 s x).
Proof. exact (MK_COMB (@lem3852973) (@lem3852972 _99873 s x)). Qed.
Lemma lem3852976 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3852977 {_99873 : Type'} (P : _99873 -> Prop) (x : _99873) : (@IN _99873 x P) = (P x).
Proof. exact (@lem3852976 _99873 P x). Qed.
Lemma lem3852978 {_99873 : Type'} (t : _99873 -> Prop) (x : _99873) : (@IN _99873 x t) = (t x).
Proof. exact (@lem3852977 _99873 t x). Qed.
Lemma lem3852979 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3852980 {_99873 : Type'} (t : _99873 -> Prop) (x : _99873) : (term577 _99873 x t) = (term578 _99873 t x).
Proof. exact (MK_COMB (@lem3852979) (@lem3852978 _99873 t x)). Qed.
Lemma lem3852981 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) (x : _99873) : (term574 _99873 s x t) = (term579 _99873 s t x).
Proof. exact (MK_COMB (@lem3852974 _99873 s x) (@lem3852980 _99873 t x)). Qed.
Lemma lem3852984 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) (x : _99873) : (term573 _99873 x s t) = (term579 _99873 s t x).
Proof. exact (TRANS (@lem3852966 _99873 s x t) (@lem3852981 _99873 s t x)). Qed.
Lemma lem3852985 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3852986 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) (x : _99873) : (term580 _99873 x s t) = (term581 _99873 s t x).
Proof. exact (MK_COMB (@lem3852985) (@lem3852984 _99873 s t x)). Qed.
Lemma lem3852988 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3852989 {_99873 : Type'} (P : _99873 -> Prop) (x : _99873) : (@IN _99873 x P) = (P x).
Proof. exact (@lem3852988 _99873 P x). Qed.
Lemma lem3852990 {_99873 : Type'} (t : _99873 -> Prop) (x : _99873) : (@IN _99873 x t) = (t x).
Proof. exact (@lem3852989 _99873 t x). Qed.
Lemma lem3852991 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) (x : _99873) : (term572 _99873 s x t) = (term582 _99873 s t x).
Proof. exact (MK_COMB (@lem3852986 _99873 s t x) (@lem3852990 _99873 t x)). Qed.
Lemma lem3852994 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) (x : _99873) : (term571 _99873 x s t) = (term582 _99873 s t x).
Proof. exact (TRANS (@lem3852961 _99873 s x t) (@lem3852991 _99873 s t x)). Qed.
Lemma lem3852995 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3852996 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) (x : _99873) : (term583 _99873 x s t) = (term584 _99873 s t x).
Proof. exact (MK_COMB (@lem3852995) (@lem3852994 _99873 s t x)). Qed.
Lemma lem3852998 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3852999 {_99873 : Type'} (x : _99873) : (@IN _99873 x (@EMPTY _99873)) = False.
Proof. exact (@lem3852998 _99873 x). Qed.
Lemma lem3853000 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) (x : _99873) : ((term571 _99873 x s t) = (@IN _99873 x (@EMPTY _99873))) = ((term582 _99873 s t x) = False).
Proof. exact (MK_COMB (@lem3852996 _99873 s t x) (@lem3852999 _99873 x)). Qed.
Lemma lem3853002 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem3853003 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) (x : _99873) : ((term582 _99873 s t x) = False) = (term585 _99873 s t x).
Proof. exact (@lem3853002 (term582 _99873 s t x)). Qed.
Lemma lem3853008 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) (x : _99873) : ((term571 _99873 x s t) = (@IN _99873 x (@EMPTY _99873))) = (term585 _99873 s t x).
Proof. exact (TRANS (@lem3853000 _99873 s t x) (@lem3853003 _99873 s t x)). Qed.
Lemma lem3853009 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) : (term586 _99873 s t) = (term587 _99873 s t).
Proof. exact (fun_ext (fun x : _99873 => @lem3853008 _99873 s t x)). Qed.
Lemma lem3853010 {_99873 : Type'} : (@all _99873) = (@all _99873).
Proof. exact (eq_refl (@all _99873)). Qed.
Lemma lem3853011 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) : (term551 _99873 s t) = (term588 _99873 s t).
Proof. exact (MK_COMB (@lem3853010 _99873) (@lem3853009 _99873 s t)). Qed.
Lemma lem3853016 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3853017 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) : (term553 _99873 s t) = (term589 _99873 s t).
Proof. exact (MK_COMB (@lem3853016) (@lem3853011 _99873 s t)). Qed.
Lemma lem3853025 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term590 A x s t) = (term591 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem3853026 {_99873 : Type'} (s : _99873 -> Prop) (x : _99873) (t : _99873 -> Prop) : (term590 _99873 x s t) = (term591 _99873 s x t).
Proof. exact (@lem3853025 _99873 s x t). Qed.
Lemma lem3853027 {_99873 : Type'} (s : _99873 -> Prop) (x : _99873) (t : _99873 -> Prop) : (term592 _99873 x s t) = (term593 _99873 s x t).
Proof. exact (@lem3853026 _99873 (@DIFF _99873 s t) x t). Qed.
Lemma lem3853031 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term573 A x s t) = (term574 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem3853032 {_99873 : Type'} (s : _99873 -> Prop) (x : _99873) (t : _99873 -> Prop) : (term573 _99873 x s t) = (term574 _99873 s x t).
Proof. exact (@lem3853031 _99873 s x t). Qed.
Lemma lem3853036 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3853037 {_99873 : Type'} (P : _99873 -> Prop) (x : _99873) : (@IN _99873 x P) = (P x).
Proof. exact (@lem3853036 _99873 P x). Qed.
Lemma lem3853038 {_99873 : Type'} (s : _99873 -> Prop) (x : _99873) : (@IN _99873 x s) = (s x).
Proof. exact (@lem3853037 _99873 s x). Qed.
Lemma lem3853039 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3853040 {_99873 : Type'} (s : _99873 -> Prop) (x : _99873) : (term575 _99873 x s) = (term576 _99873 s x).
Proof. exact (MK_COMB (@lem3853039) (@lem3853038 _99873 s x)). Qed.
Lemma lem3853042 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3853043 {_99873 : Type'} (P : _99873 -> Prop) (x : _99873) : (@IN _99873 x P) = (P x).
Proof. exact (@lem3853042 _99873 P x). Qed.
Lemma lem3853044 {_99873 : Type'} (t : _99873 -> Prop) (x : _99873) : (@IN _99873 x t) = (t x).
Proof. exact (@lem3853043 _99873 t x). Qed.
Lemma lem3853045 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3853046 {_99873 : Type'} (t : _99873 -> Prop) (x : _99873) : (term577 _99873 x t) = (term578 _99873 t x).
Proof. exact (MK_COMB (@lem3853045) (@lem3853044 _99873 t x)). Qed.
Lemma lem3853047 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) (x : _99873) : (term574 _99873 s x t) = (term579 _99873 s t x).
Proof. exact (MK_COMB (@lem3853040 _99873 s x) (@lem3853046 _99873 t x)). Qed.
Lemma lem3853050 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) (x : _99873) : (term573 _99873 x s t) = (term579 _99873 s t x).
Proof. exact (TRANS (@lem3853032 _99873 s x t) (@lem3853047 _99873 s t x)). Qed.
Lemma lem3853051 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3853052 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) (x : _99873) : (term594 _99873 x s t) = (term595 _99873 s t x).
Proof. exact (MK_COMB (@lem3853051) (@lem3853050 _99873 s t x)). Qed.
Lemma lem3853054 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3853055 {_99873 : Type'} (P : _99873 -> Prop) (x : _99873) : (@IN _99873 x P) = (P x).
Proof. exact (@lem3853054 _99873 P x). Qed.
Lemma lem3853056 {_99873 : Type'} (t : _99873 -> Prop) (x : _99873) : (@IN _99873 x t) = (t x).
Proof. exact (@lem3853055 _99873 t x). Qed.
Lemma lem3853057 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) (x : _99873) : (term593 _99873 s x t) = (term596 _99873 s t x).
Proof. exact (MK_COMB (@lem3853052 _99873 s t x) (@lem3853056 _99873 t x)). Qed.
Lemma lem3853060 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) (x : _99873) : (term592 _99873 x s t) = (term596 _99873 s t x).
Proof. exact (TRANS (@lem3853027 _99873 s x t) (@lem3853057 _99873 s t x)). Qed.
Lemma lem3853061 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3853062 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) (x : _99873) : (term597 _99873 x s t) = (term598 _99873 s t x).
Proof. exact (MK_COMB (@lem3853061) (@lem3853060 _99873 s t x)). Qed.
Lemma lem3853064 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3853065 {_99873 : Type'} (P : _99873 -> Prop) (x : _99873) : (@IN _99873 x P) = (P x).
Proof. exact (@lem3853064 _99873 P x). Qed.
Lemma lem3853066 {_99873 : Type'} (s : _99873 -> Prop) (x : _99873) : (@IN _99873 x s) = (s x).
Proof. exact (@lem3853065 _99873 s x). Qed.
Lemma lem3853067 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) : ((term592 _99873 x s t) = (@IN _99873 x s)) = ((term596 _99873 s t x) = (s x)).
Proof. exact (MK_COMB (@lem3853062 _99873 s t x) (@lem3853066 _99873 s x)). Qed.
Lemma lem3853070 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term599 _99873 t s) = (term600 _99873 t s).
Proof. exact (fun_ext (fun x : _99873 => @lem3853067 _99873 t s x)). Qed.
Lemma lem3853071 {_99873 : Type'} : (@all _99873) = (@all _99873).
Proof. exact (eq_refl (@all _99873)). Qed.
Lemma lem3853072 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term555 _99873 t s) = (term601 _99873 t s).
Proof. exact (MK_COMB (@lem3853071 _99873) (@lem3853070 _99873 t s)). Qed.
Lemma lem3853077 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term556 _99873 t s) = (term602 _99873 t s).
Proof. exact (MK_COMB (@lem3853017 _99873 s t) (@lem3853072 _99873 t s)). Qed.
Lemma lem3853080 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term558 _99873 t s) = (term603 _99873 t s).
Proof. exact (MK_COMB (@lem3852949 _99873 t s) (@lem3853077 _99873 t s)). Qed.
Lemma lem3853083 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term603 _99873 t s) = (term558 _99873 t s).
Proof. exact (SYM (@lem3853080 _99873 t s)). Qed.
Lemma lem3853085 (p : Prop) : p = (term604 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3853086 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term603 _99873 t s) = (term605 _99873 t s).
Proof. exact (@lem3853085 (term603 _99873 t s)). Qed.
Lemma lem3853087 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term605 _99873 t s) = (term603 _99873 t s).
Proof. exact (SYM (@lem3853086 _99873 t s)). Qed.
Lemma lem3853088 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (h1 : term606 _99873 t s) : term606 _99873 t s.
Proof. exact (h1). Qed.
Lemma lem3853091 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (h1 : term605 _99873 t s) : term605 _99873 t s.
Proof. exact (h1). Qed.
Lemma lem3853092 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : term607 _99873 t s.
Proof. exact (fun h0 : term605 _99873 t s => @lem3853091 _99873 t s h0). Qed.
Lemma lem3853093 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (h1 : term607 _99873 t s) : term607 _99873 t s.
Proof. exact (h1). Qed.
Lemma lem3853094 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (h1 : term605 _99873 t s) : term605 _99873 t s.
Proof. exact (h1). Qed.
Lemma lem3853095 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (h1 : term605 _99873 t s) (h2 : term607 _99873 t s) : term605 _99873 t s.
Proof. exact (@lem3853093 _99873 t s h2 (@lem3853094 _99873 t s h1)). Qed.
Lemma lem3853096 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (h1 : term605 _99873 t s) : term608 _99873 t s.
Proof. exact (fun h0 : term607 _99873 t s => @lem3853095 _99873 t s h1 h0). Qed.
Lemma lem3853097 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (h1 : term607 _99873 t s) : term607 _99873 t s.
Proof. exact (h1). Qed.
Lemma lem3853098 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (h1 : term605 _99873 t s) (h2 : term607 _99873 t s) : term605 _99873 t s.
Proof. exact (@lem3853096 _99873 t s h1 (@lem3853097 _99873 t s h2)). Qed.
Lemma lem3853099 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (h1 : term607 _99873 t s) : term607 _99873 t s.
Proof. exact (fun h0 : term605 _99873 t s => @lem3853098 _99873 t s h0 h1). Qed.
Lemma lem3853100 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : term609 _99873 t s.
Proof. exact (fun h0 : term607 _99873 t s => @lem3853099 _99873 t s h0). Qed.
Lemma lem3853103 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : term607 _99873 t s.
Proof. exact (@lem3853100 _99873 t s (@lem3853092 _99873 t s)). Qed.
Lemma lem3853104 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : term607 _99873 t s.
Proof. exact (@lem3853103 _99873 t s). Qed.
Lemma lem3853114 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3853115 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term605 _99873 t s) = (term610 _99873 t s).
Proof. exact (@lem3853114 (term606 _99873 t s)). Qed.
Lemma lem3853117 (t : Prop) : (term154 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3853118 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term610 _99873 t s) = (term603 _99873 t s).
Proof. exact (@lem3853117 (term603 _99873 t s)). Qed.
Lemma lem3853121 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term605 _99873 t s) = (term603 _99873 t s).
Proof. exact (TRANS (@lem3853115 _99873 t s) (@lem3853118 _99873 t s)). Qed.
Lemma lem3853148 {_99873 : Type'} (s : _99873 -> Prop) : (term611 _99873 s) = (term612 _99873 s).
Proof. exact (fun_ext (fun t : _99873 -> Prop => @lem3853121 _99873 t s)). Qed.
Lemma lem3853149 {_99873 : Type'} : (@all (_99873 -> Prop)) = (@all (_99873 -> Prop)).
Proof. exact (eq_refl (@all (_99873 -> Prop))). Qed.
Lemma lem3853150 {_99873 : Type'} (s : _99873 -> Prop) : (term613 _99873 s) = (term614 _99873 s).
Proof. exact (MK_COMB (@lem3853149 _99873) (@lem3853148 _99873 s)). Qed.
Lemma lem3853155 {_99873 : Type'} : (term615 _99873) = (term616 _99873).
Proof. exact (fun_ext (fun s : _99873 -> Prop => @lem3853150 _99873 s)). Qed.
Lemma lem3853156 {_99873 : Type'} : (@all (_99873 -> Prop)) = (@all (_99873 -> Prop)).
Proof. exact (eq_refl (@all (_99873 -> Prop))). Qed.
Lemma lem3853165 {_99873 : Type'} : (term617 _99873) = (term618 _99873).
Proof. exact (MK_COMB (@lem3853156 _99873) (@lem3853155 _99873)). Qed.
Lemma lem3853180 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) : ((term596 _99873 s t x) = (s x)) = ((term596 _99873 s t x) = (s x)).
Proof. exact (eq_refl ((term596 _99873 s t x) = (s x))). Qed.
Lemma lem3853181 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term600 _99873 t s) = (term600 _99873 t s).
Proof. exact (fun_ext (fun x : _99873 => @lem3853180 _99873 t s x)). Qed.
Lemma lem3853182 {_99873 : Type'} : (@all _99873) = (@all _99873).
Proof. exact (eq_refl (@all _99873)). Qed.
Lemma lem3853183 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term601 _99873 t s) = (term601 _99873 t s).
Proof. exact (MK_COMB (@lem3853182 _99873) (@lem3853181 _99873 t s)). Qed.
Lemma lem3853196 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) (x : _99873) : (term585 _99873 s t x) = (term585 _99873 s t x).
Proof. exact (eq_refl (term585 _99873 s t x)). Qed.
Lemma lem3853197 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) : (term587 _99873 s t) = (term587 _99873 s t).
Proof. exact (fun_ext (fun x : _99873 => @lem3853196 _99873 s t x)). Qed.
Lemma lem3853198 {_99873 : Type'} : (@all _99873) = (@all _99873).
Proof. exact (eq_refl (@all _99873)). Qed.
Lemma lem3853199 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) : (term588 _99873 s t) = (term588 _99873 s t).
Proof. exact (MK_COMB (@lem3853198 _99873) (@lem3853197 _99873 s t)). Qed.
Lemma lem3853200 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3853201 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) : (term589 _99873 s t) = (term589 _99873 s t).
Proof. exact (MK_COMB (@lem3853200) (@lem3853199 _99873 s t)). Qed.
Lemma lem3853202 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term602 _99873 t s) = (term602 _99873 t s).
Proof. exact (MK_COMB (@lem3853201 _99873 s t) (@lem3853183 _99873 t s)). Qed.
Lemma lem3853203 {_99873 : Type'} (s : _99873 -> Prop) : (@FINITE _99873 s) = (@FINITE _99873 s).
Proof. exact (eq_refl (@FINITE _99873 s)). Qed.
Lemma lem3853208 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) : (term562 _99873 t s x) = (term562 _99873 t s x).
Proof. exact (eq_refl (term562 _99873 t s x)). Qed.
Lemma lem3853209 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term564 _99873 t s) = (term564 _99873 t s).
Proof. exact (fun_ext (fun x : _99873 => @lem3853208 _99873 t s x)). Qed.
Lemma lem3853210 {_99873 : Type'} : (@all _99873) = (@all _99873).
Proof. exact (eq_refl (@all _99873)). Qed.
Lemma lem3853211 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term565 _99873 t s) = (term565 _99873 t s).
Proof. exact (MK_COMB (@lem3853210 _99873) (@lem3853209 _99873 t s)). Qed.
Lemma lem3853212 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3853213 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term566 _99873 t s) = (term566 _99873 t s).
Proof. exact (MK_COMB (@lem3853212) (@lem3853211 _99873 t s)). Qed.
Lemma lem3853214 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term567 _99873 t s) = (term567 _99873 t s).
Proof. exact (MK_COMB (@lem3853213 _99873 t s) (@lem3853203 _99873 s)). Qed.
Lemma lem3853215 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3853216 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term568 _99873 t s) = (term568 _99873 t s).
Proof. exact (MK_COMB (@lem3853215) (@lem3853214 _99873 t s)). Qed.
Lemma lem3853217 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term603 _99873 t s) = (term603 _99873 t s).
Proof. exact (MK_COMB (@lem3853216 _99873 t s) (@lem3853202 _99873 t s)). Qed.
Lemma lem3853218 {_99873 : Type'} (s : _99873 -> Prop) : (term612 _99873 s) = (term612 _99873 s).
Proof. exact (fun_ext (fun t : _99873 -> Prop => @lem3853217 _99873 t s)). Qed.
Lemma lem3853219 {_99873 : Type'} : (@all (_99873 -> Prop)) = (@all (_99873 -> Prop)).
Proof. exact (eq_refl (@all (_99873 -> Prop))). Qed.
Lemma lem3853220 {_99873 : Type'} (s : _99873 -> Prop) : (term614 _99873 s) = (term614 _99873 s).
Proof. exact (MK_COMB (@lem3853219 _99873) (@lem3853218 _99873 s)). Qed.
Lemma lem3853221 {_99873 : Type'} : (term616 _99873) = (term616 _99873).
Proof. exact (fun_ext (fun s : _99873 -> Prop => @lem3853220 _99873 s)). Qed.
Lemma lem3853222 {_99873 : Type'} : (@all (_99873 -> Prop)) = (@all (_99873 -> Prop)).
Proof. exact (eq_refl (@all (_99873 -> Prop))). Qed.
Lemma lem3853223 {_99873 : Type'} : (term618 _99873) = (term618 _99873).
Proof. exact (MK_COMB (@lem3853222 _99873) (@lem3853221 _99873)). Qed.
Lemma lem3853272 {_99873 : Type'} : (term617 _99873) = (term618 _99873).
Proof. exact (TRANS (@lem3853165 _99873) (@lem3853223 _99873)). Qed.
Lemma lem3853273 {_99873 : Type'} : (term618 _99873) = (term617 _99873).
Proof. exact (SYM (@lem3853272 _99873)). Qed.
Lemma lem3853274 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (h1 : term567 _99873 t s) : term567 _99873 t s.
Proof. exact (h1). Qed.
Lemma lem3853276 (p : Prop) : p = (term604 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3853277 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term602 _99873 t s) = (term619 _99873 t s).
Proof. exact (@lem3853276 (term602 _99873 t s)). Qed.
Lemma lem3853278 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term619 _99873 t s) = (term602 _99873 t s).
Proof. exact (SYM (@lem3853277 _99873 t s)). Qed.
Lemma lem3853279 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (h1 : term620 _99873 t s) : term620 _99873 t s.
Proof. exact (h1). Qed.
Lemma lem3853286 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) : (term562 _99873 t s x) = (term621 _99873 t s x).
Proof. exact (@lem17265 (t x) (s x)). Qed.
Lemma lem3853287 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term564 _99873 t s) = (term622 _99873 t s).
Proof. exact (fun_ext (fun x : _99873 => @lem3853286 _99873 t s x)). Qed.
Lemma lem3853288 {_99873 : Type'} : (@all _99873) = (@all _99873).
Proof. exact (eq_refl (@all _99873)). Qed.
Lemma lem3853289 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term565 _99873 t s) = (term623 _99873 t s).
Proof. exact (MK_COMB (@lem3853288 _99873) (@lem3853287 _99873 t s)). Qed.
Lemma lem3853290 {_99873 : Type'} (s : _99873 -> Prop) : (@FINITE _99873 s) = (@FINITE _99873 s).
Proof. exact (eq_refl (@FINITE _99873 s)). Qed.
Lemma lem3853291 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3853292 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term566 _99873 t s) = (term624 _99873 t s).
Proof. exact (MK_COMB (@lem3853291) (@lem3853289 _99873 t s)). Qed.
Lemma lem3853329 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term567 _99873 t s) = (term625 _99873 t s).
Proof. exact (MK_COMB (@lem3853292 _99873 t s) (@lem3853290 _99873 s)). Qed.
Lemma lem3853330 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (h1 : term567 _99873 t s) : term625 _99873 t s.
Proof. exact (EQ_MP (@lem3853329 _99873 t s) (@lem3853274 _99873 t s h1)). Qed.
Lemma lem3853341 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) (x : _99873) : (term626 _99873 s t x) = (term582 _99873 s t x).
Proof. exact (@lem16933 (term582 _99873 s t x)). Qed.
Lemma lem3853342 {_99873 : Type'} (P : _99873 -> Prop) : (term627 _99873 P) = (term628 _99873 P).
Proof. exact (@lem18392 _99873 P). Qed.
Lemma lem3853343 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) : (term629 _99873 s t) = (term630 _99873 s t).
Proof. exact (@lem3853342 _99873 (term587 _99873 s t)). Qed.
Lemma lem3853344 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) (x : _99873) : (term631 _99873 s t x) = (term585 _99873 s t x).
Proof. exact (eq_refl (term631 _99873 s t x)). Qed.
Lemma lem3853345 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3853346 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) (x : _99873) : (term632 _99873 s t x) = (term626 _99873 s t x).
Proof. exact (MK_COMB (@lem3853345) (@lem3853344 _99873 s t x)). Qed.
Lemma lem3853347 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) (x : _99873) : (term632 _99873 s t x) = (term582 _99873 s t x).
Proof. exact (TRANS (@lem3853346 _99873 s t x) (@lem3853341 _99873 s t x)). Qed.
Lemma lem3853348 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) : (term633 _99873 s t) = (term634 _99873 s t).
Proof. exact (fun_ext (fun x : _99873 => @lem3853347 _99873 s t x)). Qed.
Lemma lem3853349 {_99873 : Type'} : (@ex _99873) = (@ex _99873).
Proof. exact (eq_refl (@ex _99873)). Qed.
Lemma lem3853350 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) : (term630 _99873 s t) = (term635 _99873 s t).
Proof. exact (MK_COMB (@lem3853349 _99873) (@lem3853348 _99873 s t)). Qed.
Lemma lem3853351 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) : (term629 _99873 s t) = (term635 _99873 s t).
Proof. exact (TRANS (@lem3853343 _99873 s t) (@lem3853350 _99873 s t)). Qed.
Lemma lem3853357 {_99873 : Type'} (t : _99873 -> Prop) (x : _99873) : (term636 _99873 t x) = (t x).
Proof. exact (@lem16933 (t x)). Qed.
Lemma lem3853359 {_99873 : Type'} (s : _99873 -> Prop) (x : _99873) : (term637 _99873 s x) = (term637 _99873 s x).
Proof. exact (eq_refl (term637 _99873 s x)). Qed.
Lemma lem3853360 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) (x : _99873) : (term638 _99873 s t x) = (term621 _99873 s t x).
Proof. exact (MK_COMB (@lem3853359 _99873 s x) (@lem3853357 _99873 t x)). Qed.
Lemma lem3853361 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) (x : _99873) : (term639 _99873 s t x) = (term638 _99873 s t x).
Proof. exact (@lem17045 (s x) (term578 _99873 t x)). Qed.
Lemma lem3853362 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) (x : _99873) : (term639 _99873 s t x) = (term621 _99873 s t x).
Proof. exact (TRANS (@lem3853361 _99873 s t x) (@lem3853360 _99873 s t x)). Qed.
Lemma lem3853366 {_99873 : Type'} (t : _99873 -> Prop) (x : _99873) : (term578 _99873 t x) = (term578 _99873 t x).
Proof. exact (eq_refl (term578 _99873 t x)). Qed.
Lemma lem3853368 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3853369 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) (x : _99873) : (term640 _99873 s t x) = (term641 _99873 s t x).
Proof. exact (MK_COMB (@lem3853368) (@lem3853362 _99873 s t x)). Qed.
Lemma lem3853370 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) (x : _99873) : (term642 _99873 s t x) = (term643 _99873 s t x).
Proof. exact (MK_COMB (@lem3853369 _99873 s t x) (@lem3853366 _99873 t x)). Qed.
Lemma lem3853371 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) (x : _99873) : (term644 _99873 s t x) = (term642 _99873 s t x).
Proof. exact (@lem17160 (term579 _99873 s t x) (t x)). Qed.
Lemma lem3853372 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) (x : _99873) : (term644 _99873 s t x) = (term643 _99873 s t x).
Proof. exact (TRANS (@lem3853371 _99873 s t x) (@lem3853370 _99873 s t x)). Qed.
Lemma lem3853377 {_99873 : Type'} (s : _99873 -> Prop) (x : _99873) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem3853378 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3853379 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) (x : _99873) : (term645 _99873 s t x) = (term646 _99873 s t x).
Proof. exact (MK_COMB (@lem3853378) (@lem3853372 _99873 s t x)). Qed.
Lemma lem3853380 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) : (term647 _99873 t s x) = (term648 _99873 t s x).
Proof. exact (MK_COMB (@lem3853379 _99873 s t x) (@lem3853377 _99873 s x)). Qed.
Lemma lem3853385 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) : (term649 _99873 t s x) = (term649 _99873 t s x).
Proof. exact (eq_refl (term649 _99873 t s x)). Qed.
Lemma lem3853386 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) : (term650 _99873 t s x) = (term651 _99873 t s x).
Proof. exact (MK_COMB (@lem3853385 _99873 t s x) (@lem3853380 _99873 t s x)). Qed.
Lemma lem3853387 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) : (term652 _99873 t s x) = (term650 _99873 t s x).
Proof. exact (@lem17646 (term596 _99873 s t x) (s x)). Qed.
Lemma lem3853388 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) : (term652 _99873 t s x) = (term651 _99873 t s x).
Proof. exact (TRANS (@lem3853387 _99873 t s x) (@lem3853386 _99873 t s x)). Qed.
Lemma lem3853389 {_99873 : Type'} (P : _99873 -> Prop) : (term627 _99873 P) = (term628 _99873 P).
Proof. exact (@lem18392 _99873 P). Qed.
Lemma lem3853390 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term653 _99873 t s) = (term654 _99873 t s).
Proof. exact (@lem3853389 _99873 (term600 _99873 t s)). Qed.
Lemma lem3853391 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) : (term655 _99873 t s x) = ((term596 _99873 s t x) = (s x)).
Proof. exact (eq_refl (term655 _99873 t s x)). Qed.
Lemma lem3853392 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3853393 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) : (term656 _99873 t s x) = (term652 _99873 t s x).
Proof. exact (MK_COMB (@lem3853392) (@lem3853391 _99873 t s x)). Qed.
Lemma lem3853394 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) : (term656 _99873 t s x) = (term651 _99873 t s x).
Proof. exact (TRANS (@lem3853393 _99873 t s x) (@lem3853388 _99873 t s x)). Qed.
Lemma lem3853395 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term657 _99873 t s) = (term658 _99873 t s).
Proof. exact (fun_ext (fun x : _99873 => @lem3853394 _99873 t s x)). Qed.
Lemma lem3853396 {_99873 : Type'} : (@ex _99873) = (@ex _99873).
Proof. exact (eq_refl (@ex _99873)). Qed.
Lemma lem3853397 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term654 _99873 t s) = (term659 _99873 t s).
Proof. exact (MK_COMB (@lem3853396 _99873) (@lem3853395 _99873 t s)). Qed.
Lemma lem3853398 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term653 _99873 t s) = (term659 _99873 t s).
Proof. exact (TRANS (@lem3853390 _99873 t s) (@lem3853397 _99873 t s)). Qed.
Lemma lem3853399 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3853400 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) : (term660 _99873 s t) = (term661 _99873 s t).
Proof. exact (MK_COMB (@lem3853399) (@lem3853351 _99873 s t)). Qed.
Lemma lem3853401 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term662 _99873 t s) = (term663 _99873 t s).
Proof. exact (MK_COMB (@lem3853400 _99873 s t) (@lem3853398 _99873 t s)). Qed.
Lemma lem3853402 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term620 _99873 t s) = (term662 _99873 t s).
Proof. exact (@lem17045 (term588 _99873 s t) (term601 _99873 t s)). Qed.
Lemma lem3853403 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term620 _99873 t s) = (term663 _99873 t s).
Proof. exact (TRANS (@lem3853402 _99873 t s) (@lem3853401 _99873 t s)). Qed.
Lemma lem3853437 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term664 A P Q) = (term665 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3853438 {_99873 : Type'} (P : _99873 -> Prop) (Q : _99873 -> Prop) : (term664 _99873 P Q) = (term665 _99873 P Q).
Proof. exact (@lem3853437 _99873 P Q). Qed.
Lemma lem3853439 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term666 _99873 t s) = (term667 _99873 t s).
Proof. exact (@lem3853438 _99873 (term668 _99873 t s) (term669 _99873 t s)). Qed.
Lemma lem3853440 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) : (term670 _99873 t s x) = (term671 _99873 t s x).
Proof. exact (eq_refl (term670 _99873 t s x)). Qed.
Lemma lem3853441 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3853442 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) : (term672 _99873 t s x) = (term649 _99873 t s x).
Proof. exact (MK_COMB (@lem3853441) (@lem3853440 _99873 t s x)). Qed.
Lemma lem3853443 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) : (term673 _99873 t s x) = (term648 _99873 t s x).
Proof. exact (eq_refl (term673 _99873 t s x)). Qed.
Lemma lem3853444 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) : (term674 _99873 t s x) = (term651 _99873 t s x).
Proof. exact (MK_COMB (@lem3853442 _99873 t s x) (@lem3853443 _99873 t s x)). Qed.
Lemma lem3853445 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term675 _99873 t s) = (term658 _99873 t s).
Proof. exact (fun_ext (fun x : _99873 => @lem3853444 _99873 t s x)). Qed.
Lemma lem3853446 {_99873 : Type'} : (@ex _99873) = (@ex _99873).
Proof. exact (eq_refl (@ex _99873)). Qed.
Lemma lem3853447 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term666 _99873 t s) = (term659 _99873 t s).
Proof. exact (MK_COMB (@lem3853446 _99873) (@lem3853445 _99873 t s)). Qed.
Lemma lem3853448 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3853449 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term676 _99873 t s) = (term677 _99873 t s).
Proof. exact (MK_COMB (@lem3853448) (@lem3853447 _99873 t s)). Qed.
Lemma lem3853450 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) : (term670 _99873 t s x) = (term671 _99873 t s x).
Proof. exact (eq_refl (term670 _99873 t s x)). Qed.
Lemma lem3853451 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term678 _99873 t s) = (term668 _99873 t s).
Proof. exact (fun_ext (fun x : _99873 => @lem3853450 _99873 t s x)). Qed.
Lemma lem3853452 {_99873 : Type'} : (@ex _99873) = (@ex _99873).
Proof. exact (eq_refl (@ex _99873)). Qed.
Lemma lem3853453 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term679 _99873 t s) = (term680 _99873 t s).
Proof. exact (MK_COMB (@lem3853452 _99873) (@lem3853451 _99873 t s)). Qed.
Lemma lem3853454 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3853455 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term681 _99873 t s) = (term682 _99873 t s).
Proof. exact (MK_COMB (@lem3853454) (@lem3853453 _99873 t s)). Qed.
Lemma lem3853456 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) : (term673 _99873 t s x) = (term648 _99873 t s x).
Proof. exact (eq_refl (term673 _99873 t s x)). Qed.
Lemma lem3853457 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term683 _99873 t s) = (term669 _99873 t s).
Proof. exact (fun_ext (fun x : _99873 => @lem3853456 _99873 t s x)). Qed.
Lemma lem3853458 {_99873 : Type'} : (@ex _99873) = (@ex _99873).
Proof. exact (eq_refl (@ex _99873)). Qed.
Lemma lem3853459 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term684 _99873 t s) = (term685 _99873 t s).
Proof. exact (MK_COMB (@lem3853458 _99873) (@lem3853457 _99873 t s)). Qed.
Lemma lem3853460 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term667 _99873 t s) = (term686 _99873 t s).
Proof. exact (MK_COMB (@lem3853455 _99873 t s) (@lem3853459 _99873 t s)). Qed.
Lemma lem3853461 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : ((term666 _99873 t s) = (term667 _99873 t s)) = ((term659 _99873 t s) = (term686 _99873 t s)).
Proof. exact (MK_COMB (@lem3853449 _99873 t s) (@lem3853460 _99873 t s)). Qed.
Lemma lem3853462 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term659 _99873 t s) = (term686 _99873 t s).
Proof. exact (EQ_MP (@lem3853461 _99873 t s) (@lem3853439 _99873 t s)). Qed.
Lemma lem3853543 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) : (term661 _99873 s t) = (term661 _99873 s t).
Proof. exact (eq_refl (term661 _99873 s t)). Qed.
Lemma lem3853544 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term663 _99873 t s) = (term687 _99873 t s).
Proof. exact (MK_COMB (@lem3853543 _99873 s t) (@lem3853462 _99873 t s)). Qed.
Lemma lem3853546 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term665 A P Q) = (term664 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3853547 {_99873 : Type'} (P : _99873 -> Prop) (Q : _99873 -> Prop) : (term665 _99873 P Q) = (term664 _99873 P Q).
Proof. exact (@lem3853546 _99873 P Q). Qed.
Lemma lem3853548 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term667 _99873 t s) = (term666 _99873 t s).
Proof. exact (@lem3853547 _99873 (term668 _99873 t s) (term669 _99873 t s)). Qed.
Lemma lem3853549 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) : (term670 _99873 t s x) = (term671 _99873 t s x).
Proof. exact (eq_refl (term670 _99873 t s x)). Qed.
Lemma lem3853550 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term678 _99873 t s) = (term668 _99873 t s).
Proof. exact (fun_ext (fun x : _99873 => @lem3853549 _99873 t s x)). Qed.
Lemma lem3853551 {_99873 : Type'} : (@ex _99873) = (@ex _99873).
Proof. exact (eq_refl (@ex _99873)). Qed.
Lemma lem3853552 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term679 _99873 t s) = (term680 _99873 t s).
Proof. exact (MK_COMB (@lem3853551 _99873) (@lem3853550 _99873 t s)). Qed.
Lemma lem3853553 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3853554 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term681 _99873 t s) = (term682 _99873 t s).
Proof. exact (MK_COMB (@lem3853553) (@lem3853552 _99873 t s)). Qed.
Lemma lem3853555 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) : (term673 _99873 t s x) = (term648 _99873 t s x).
Proof. exact (eq_refl (term673 _99873 t s x)). Qed.
Lemma lem3853556 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term683 _99873 t s) = (term669 _99873 t s).
Proof. exact (fun_ext (fun x : _99873 => @lem3853555 _99873 t s x)). Qed.
Lemma lem3853557 {_99873 : Type'} : (@ex _99873) = (@ex _99873).
Proof. exact (eq_refl (@ex _99873)). Qed.
Lemma lem3853558 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term684 _99873 t s) = (term685 _99873 t s).
Proof. exact (MK_COMB (@lem3853557 _99873) (@lem3853556 _99873 t s)). Qed.
Lemma lem3853559 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term667 _99873 t s) = (term686 _99873 t s).
Proof. exact (MK_COMB (@lem3853554 _99873 t s) (@lem3853558 _99873 t s)). Qed.
Lemma lem3853560 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3853561 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term688 _99873 t s) = (term689 _99873 t s).
Proof. exact (MK_COMB (@lem3853560) (@lem3853559 _99873 t s)). Qed.
Lemma lem3853562 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) : (term670 _99873 t s x) = (term671 _99873 t s x).
Proof. exact (eq_refl (term670 _99873 t s x)). Qed.
Lemma lem3853563 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3853564 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) : (term672 _99873 t s x) = (term649 _99873 t s x).
Proof. exact (MK_COMB (@lem3853563) (@lem3853562 _99873 t s x)). Qed.
Lemma lem3853565 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) : (term673 _99873 t s x) = (term648 _99873 t s x).
Proof. exact (eq_refl (term673 _99873 t s x)). Qed.
Lemma lem3853566 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) : (term674 _99873 t s x) = (term651 _99873 t s x).
Proof. exact (MK_COMB (@lem3853564 _99873 t s x) (@lem3853565 _99873 t s x)). Qed.
Lemma lem3853567 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term675 _99873 t s) = (term658 _99873 t s).
Proof. exact (fun_ext (fun x : _99873 => @lem3853566 _99873 t s x)). Qed.
Lemma lem3853568 {_99873 : Type'} : (@ex _99873) = (@ex _99873).
Proof. exact (eq_refl (@ex _99873)). Qed.
Lemma lem3853569 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term666 _99873 t s) = (term659 _99873 t s).
Proof. exact (MK_COMB (@lem3853568 _99873) (@lem3853567 _99873 t s)). Qed.
Lemma lem3853570 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : ((term667 _99873 t s) = (term666 _99873 t s)) = ((term686 _99873 t s) = (term659 _99873 t s)).
Proof. exact (MK_COMB (@lem3853561 _99873 t s) (@lem3853569 _99873 t s)). Qed.
Lemma lem3853571 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term686 _99873 t s) = (term659 _99873 t s).
Proof. exact (EQ_MP (@lem3853570 _99873 t s) (@lem3853548 _99873 t s)). Qed.
Lemma lem3853572 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) : (term661 _99873 s t) = (term661 _99873 s t).
Proof. exact (eq_refl (term661 _99873 s t)). Qed.
Lemma lem3853573 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term687 _99873 t s) = (term663 _99873 t s).
Proof. exact (MK_COMB (@lem3853572 _99873 s t) (@lem3853571 _99873 t s)). Qed.
Lemma lem3853575 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term665 A P Q) = (term664 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3853576 {_99873 : Type'} (P : _99873 -> Prop) (Q : _99873 -> Prop) : (term665 _99873 P Q) = (term664 _99873 P Q).
Proof. exact (@lem3853575 _99873 P Q). Qed.
Lemma lem3853577 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term690 _99873 t s) = (term691 _99873 t s).
Proof. exact (@lem3853576 _99873 (term634 _99873 s t) (term658 _99873 t s)). Qed.
Lemma lem3853578 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) (x : _99873) : (term692 _99873 s t x) = (term582 _99873 s t x).
Proof. exact (eq_refl (term692 _99873 s t x)). Qed.
Lemma lem3853579 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) : (term693 _99873 s t) = (term634 _99873 s t).
Proof. exact (fun_ext (fun x : _99873 => @lem3853578 _99873 s t x)). Qed.
Lemma lem3853580 {_99873 : Type'} : (@ex _99873) = (@ex _99873).
Proof. exact (eq_refl (@ex _99873)). Qed.
Lemma lem3853581 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) : (term694 _99873 s t) = (term635 _99873 s t).
Proof. exact (MK_COMB (@lem3853580 _99873) (@lem3853579 _99873 s t)). Qed.
Lemma lem3853582 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3853583 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) : (term695 _99873 s t) = (term661 _99873 s t).
Proof. exact (MK_COMB (@lem3853582) (@lem3853581 _99873 s t)). Qed.
Lemma lem3853584 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) : (term696 _99873 t s x) = (term651 _99873 t s x).
Proof. exact (eq_refl (term696 _99873 t s x)). Qed.
Lemma lem3853585 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term697 _99873 t s) = (term658 _99873 t s).
Proof. exact (fun_ext (fun x : _99873 => @lem3853584 _99873 t s x)). Qed.
Lemma lem3853586 {_99873 : Type'} : (@ex _99873) = (@ex _99873).
Proof. exact (eq_refl (@ex _99873)). Qed.
Lemma lem3853587 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term698 _99873 t s) = (term659 _99873 t s).
Proof. exact (MK_COMB (@lem3853586 _99873) (@lem3853585 _99873 t s)). Qed.
Lemma lem3853588 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term690 _99873 t s) = (term663 _99873 t s).
Proof. exact (MK_COMB (@lem3853583 _99873 s t) (@lem3853587 _99873 t s)). Qed.
Lemma lem3853589 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3853590 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term699 _99873 t s) = (term700 _99873 t s).
Proof. exact (MK_COMB (@lem3853589) (@lem3853588 _99873 t s)). Qed.
Lemma lem3853591 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) (x : _99873) : (term692 _99873 s t x) = (term582 _99873 s t x).
Proof. exact (eq_refl (term692 _99873 s t x)). Qed.
Lemma lem3853592 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3853593 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) (x : _99873) : (term701 _99873 s t x) = (term702 _99873 s t x).
Proof. exact (MK_COMB (@lem3853592) (@lem3853591 _99873 s t x)). Qed.
Lemma lem3853594 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) : (term696 _99873 t s x) = (term651 _99873 t s x).
Proof. exact (eq_refl (term696 _99873 t s x)). Qed.
Lemma lem3853595 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) : (term703 _99873 t s x) = (term704 _99873 t s x).
Proof. exact (MK_COMB (@lem3853593 _99873 s t x) (@lem3853594 _99873 t s x)). Qed.
Lemma lem3853596 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term705 _99873 t s) = (term706 _99873 t s).
Proof. exact (fun_ext (fun x : _99873 => @lem3853595 _99873 t s x)). Qed.
Lemma lem3853597 {_99873 : Type'} : (@ex _99873) = (@ex _99873).
Proof. exact (eq_refl (@ex _99873)). Qed.
Lemma lem3853598 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term691 _99873 t s) = (term707 _99873 t s).
Proof. exact (MK_COMB (@lem3853597 _99873) (@lem3853596 _99873 t s)). Qed.
Lemma lem3853599 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : ((term690 _99873 t s) = (term691 _99873 t s)) = ((term663 _99873 t s) = (term707 _99873 t s)).
Proof. exact (MK_COMB (@lem3853590 _99873 t s) (@lem3853598 _99873 t s)). Qed.
Lemma lem3853600 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term663 _99873 t s) = (term707 _99873 t s).
Proof. exact (EQ_MP (@lem3853599 _99873 t s) (@lem3853577 _99873 t s)). Qed.
Lemma lem3853601 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term687 _99873 t s) = (term707 _99873 t s).
Proof. exact (TRANS (@lem3853573 _99873 t s) (@lem3853600 _99873 t s)). Qed.
Lemma lem3853602 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term663 _99873 t s) = (term707 _99873 t s).
Proof. exact (TRANS (@lem3853544 _99873 t s) (@lem3853601 _99873 t s)). Qed.
Lemma lem3853603 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term620 _99873 t s) = (term707 _99873 t s).
Proof. exact (TRANS (@lem3853403 _99873 t s) (@lem3853602 _99873 t s)). Qed.
Lemma lem3853604 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (h1 : term620 _99873 t s) : term707 _99873 t s.
Proof. exact (EQ_MP (@lem3853603 _99873 t s) (@lem3853279 _99873 t s h1)). Qed.
Lemma lem3853605 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) (h1 : term704 _99873 t s x) : term704 _99873 t s x.
Proof. exact (h1). Qed.
Lemma lem3853608 {_99873 : Type'} (s : _99873 -> Prop) : (@FINITE _99873 s) = (@FINITE _99873 s).
Proof. exact (eq_refl (@FINITE _99873 s)). Qed.
Lemma lem3853613 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3853614 {_99873 : Type'} (f : _99873 -> Prop) (x : _99873) : (f x) = (@I (_99873 -> Prop) f x).
Proof. exact (@lem3853613 _99873 Prop f x). Qed.
Lemma lem3853616 {_99873 : Type'} (s : _99873 -> Prop) (x : _99873) : (s x) = (@I (_99873 -> Prop) s x).
Proof. exact (@lem3853614 _99873 s x). Qed.
Lemma lem3853623 {_99873 : Type'} (t : _99873 -> Prop) (x : _99873) : (term637 _99873 t x) = (term637 _99873 t x).
Proof. exact (eq_refl (term637 _99873 t x)). Qed.
Lemma lem3853624 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) : (term621 _99873 t s x) = (term708 _99873 t s x).
Proof. exact (MK_COMB (@lem3853623 _99873 t x) (@lem3853616 _99873 s x)). Qed.
Lemma lem3853625 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term622 _99873 t s) = (term709 _99873 t s).
Proof. exact (fun_ext (fun x : _99873 => @lem3853624 _99873 t s x)). Qed.
Lemma lem3853626 {_99873 : Type'} : (@all _99873) = (@all _99873).
Proof. exact (eq_refl (@all _99873)). Qed.
Lemma lem3853627 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term623 _99873 t s) = (term710 _99873 t s).
Proof. exact (MK_COMB (@lem3853626 _99873) (@lem3853625 _99873 t s)). Qed.
Lemma lem3853628 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3853629 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term624 _99873 t s) = (term711 _99873 t s).
Proof. exact (MK_COMB (@lem3853628) (@lem3853627 _99873 t s)). Qed.
Lemma lem3853630 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term625 _99873 t s) = (term712 _99873 t s).
Proof. exact (MK_COMB (@lem3853629 _99873 t s) (@lem3853608 _99873 s)). Qed.
Lemma lem3853631 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (h1 : term567 _99873 t s) : term712 _99873 t s.
Proof. exact (EQ_MP (@lem3853630 _99873 t s) (@lem3853330 _99873 t s h1)). Qed.
Lemma lem3853636 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3853637 {_99873 : Type'} (f : _99873 -> Prop) (x : _99873) : (f x) = (@I (_99873 -> Prop) f x).
Proof. exact (@lem3853636 _99873 Prop f x). Qed.
Lemma lem3853639 {_99873 : Type'} (s : _99873 -> Prop) (x : _99873) : (s x) = (@I (_99873 -> Prop) s x).
Proof. exact (@lem3853637 _99873 s x). Qed.
Lemma lem3853644 {_99873 : Type'} (t : _99873 -> Prop) (x : _99873) : (term578 _99873 t x) = (term578 _99873 t x).
Proof. exact (eq_refl (term578 _99873 t x)). Qed.
Lemma lem3853647 {_99873 : Type'} (t : _99873 -> Prop) (x : _99873) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem3853648 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3853653 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3853654 {_99873 : Type'} (f : _99873 -> Prop) (x : _99873) : (f x) = (@I (_99873 -> Prop) f x).
Proof. exact (@lem3853653 _99873 Prop f x). Qed.
Lemma lem3853656 {_99873 : Type'} (s : _99873 -> Prop) (x : _99873) : (s x) = (@I (_99873 -> Prop) s x).
Proof. exact (@lem3853654 _99873 s x). Qed.
Lemma lem3853657 {_99873 : Type'} (s : _99873 -> Prop) (x : _99873) : (term578 _99873 s x) = (term713 _99873 s x).
Proof. exact (MK_COMB (@lem3853648) (@lem3853656 _99873 s x)). Qed.
Lemma lem3853658 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3853659 {_99873 : Type'} (s : _99873 -> Prop) (x : _99873) : (term637 _99873 s x) = (term714 _99873 s x).
Proof. exact (MK_COMB (@lem3853658) (@lem3853657 _99873 s x)). Qed.
Lemma lem3853660 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) (x : _99873) : (term621 _99873 s t x) = (term715 _99873 s t x).
Proof. exact (MK_COMB (@lem3853659 _99873 s x) (@lem3853647 _99873 t x)). Qed.
Lemma lem3853661 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3853662 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) (x : _99873) : (term641 _99873 s t x) = (term716 _99873 s t x).
Proof. exact (MK_COMB (@lem3853661) (@lem3853660 _99873 s t x)). Qed.
Lemma lem3853663 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) (x : _99873) : (term643 _99873 s t x) = (term717 _99873 s t x).
Proof. exact (MK_COMB (@lem3853662 _99873 s t x) (@lem3853644 _99873 t x)). Qed.
Lemma lem3853664 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3853665 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) (x : _99873) : (term646 _99873 s t x) = (term718 _99873 s t x).
Proof. exact (MK_COMB (@lem3853664) (@lem3853663 _99873 s t x)). Qed.
Lemma lem3853666 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) : (term648 _99873 t s x) = (term719 _99873 t s x).
Proof. exact (MK_COMB (@lem3853665 _99873 s t x) (@lem3853639 _99873 s x)). Qed.
Lemma lem3853667 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3853672 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3853673 {_99873 : Type'} (f : _99873 -> Prop) (x : _99873) : (f x) = (@I (_99873 -> Prop) f x).
Proof. exact (@lem3853672 _99873 Prop f x). Qed.
Lemma lem3853675 {_99873 : Type'} (s : _99873 -> Prop) (x : _99873) : (s x) = (@I (_99873 -> Prop) s x).
Proof. exact (@lem3853673 _99873 s x). Qed.
Lemma lem3853676 {_99873 : Type'} (s : _99873 -> Prop) (x : _99873) : (term578 _99873 s x) = (term713 _99873 s x).
Proof. exact (MK_COMB (@lem3853667) (@lem3853675 _99873 s x)). Qed.
Lemma lem3853679 {_99873 : Type'} (t : _99873 -> Prop) (x : _99873) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem3853684 {_99873 : Type'} (t : _99873 -> Prop) (x : _99873) : (term578 _99873 t x) = (term578 _99873 t x).
Proof. exact (eq_refl (term578 _99873 t x)). Qed.
Lemma lem3853689 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3853690 {_99873 : Type'} (f : _99873 -> Prop) (x : _99873) : (f x) = (@I (_99873 -> Prop) f x).
Proof. exact (@lem3853689 _99873 Prop f x). Qed.
Lemma lem3853692 {_99873 : Type'} (s : _99873 -> Prop) (x : _99873) : (s x) = (@I (_99873 -> Prop) s x).
Proof. exact (@lem3853690 _99873 s x). Qed.
Lemma lem3853693 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3853694 {_99873 : Type'} (s : _99873 -> Prop) (x : _99873) : (term576 _99873 s x) = (term720 _99873 s x).
Proof. exact (MK_COMB (@lem3853693) (@lem3853692 _99873 s x)). Qed.
Lemma lem3853695 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) (x : _99873) : (term579 _99873 s t x) = (term721 _99873 s t x).
Proof. exact (MK_COMB (@lem3853694 _99873 s x) (@lem3853684 _99873 t x)). Qed.
Lemma lem3853696 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3853697 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) (x : _99873) : (term595 _99873 s t x) = (term722 _99873 s t x).
Proof. exact (MK_COMB (@lem3853696) (@lem3853695 _99873 s t x)). Qed.
Lemma lem3853698 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) (x : _99873) : (term596 _99873 s t x) = (term723 _99873 s t x).
Proof. exact (MK_COMB (@lem3853697 _99873 s t x) (@lem3853679 _99873 t x)). Qed.
Lemma lem3853699 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3853700 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) (x : _99873) : (term724 _99873 s t x) = (term725 _99873 s t x).
Proof. exact (MK_COMB (@lem3853699) (@lem3853698 _99873 s t x)). Qed.
Lemma lem3853701 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) : (term671 _99873 t s x) = (term726 _99873 t s x).
Proof. exact (MK_COMB (@lem3853700 _99873 s t x) (@lem3853676 _99873 s x)). Qed.
Lemma lem3853702 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3853703 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) : (term649 _99873 t s x) = (term727 _99873 t s x).
Proof. exact (MK_COMB (@lem3853702) (@lem3853701 _99873 t s x)). Qed.
Lemma lem3853704 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) : (term651 _99873 t s x) = (term728 _99873 t s x).
Proof. exact (MK_COMB (@lem3853703 _99873 t s x) (@lem3853666 _99873 t s x)). Qed.
Lemma lem3853707 {_99873 : Type'} (t : _99873 -> Prop) (x : _99873) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem3853712 {_99873 : Type'} (t : _99873 -> Prop) (x : _99873) : (term578 _99873 t x) = (term578 _99873 t x).
Proof. exact (eq_refl (term578 _99873 t x)). Qed.
Lemma lem3853717 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3853718 {_99873 : Type'} (f : _99873 -> Prop) (x : _99873) : (f x) = (@I (_99873 -> Prop) f x).
Proof. exact (@lem3853717 _99873 Prop f x). Qed.
Lemma lem3853720 {_99873 : Type'} (s : _99873 -> Prop) (x : _99873) : (s x) = (@I (_99873 -> Prop) s x).
Proof. exact (@lem3853718 _99873 s x). Qed.
Lemma lem3853721 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3853722 {_99873 : Type'} (s : _99873 -> Prop) (x : _99873) : (term576 _99873 s x) = (term720 _99873 s x).
Proof. exact (MK_COMB (@lem3853721) (@lem3853720 _99873 s x)). Qed.
Lemma lem3853723 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) (x : _99873) : (term579 _99873 s t x) = (term721 _99873 s t x).
Proof. exact (MK_COMB (@lem3853722 _99873 s x) (@lem3853712 _99873 t x)). Qed.
Lemma lem3853724 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3853725 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) (x : _99873) : (term581 _99873 s t x) = (term729 _99873 s t x).
Proof. exact (MK_COMB (@lem3853724) (@lem3853723 _99873 s t x)). Qed.
Lemma lem3853726 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) (x : _99873) : (term582 _99873 s t x) = (term730 _99873 s t x).
Proof. exact (MK_COMB (@lem3853725 _99873 s t x) (@lem3853707 _99873 t x)). Qed.
Lemma lem3853727 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3853728 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) (x : _99873) : (term702 _99873 s t x) = (term731 _99873 s t x).
Proof. exact (MK_COMB (@lem3853727) (@lem3853726 _99873 s t x)). Qed.
Lemma lem3853729 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) : (term704 _99873 t s x) = (term732 _99873 t s x).
Proof. exact (MK_COMB (@lem3853728 _99873 s t x) (@lem3853704 _99873 t s x)). Qed.
Lemma lem3853730 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) (h1 : term704 _99873 t s x) : term732 _99873 t s x.
Proof. exact (EQ_MP (@lem3853729 _99873 t s x) (@lem3853605 _99873 t s x h1)). Qed.
Lemma lem3853732 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (h1 : term567 _99873 t s) : term710 _99873 t s.
Proof. exact (proj1 (@lem3853631 _99873 t s h1)). Qed.
Lemma lem3853733 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) (x : _99873) (h1 : term730 _99873 s t x) : term730 _99873 s t x.
Proof. exact (h1). Qed.
Lemma lem3853734 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) (h1 : term728 _99873 t s x) : term728 _99873 t s x.
Proof. exact (h1). Qed.
Lemma lem3853736 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) (x : _99873) (h1 : term730 _99873 s t x) : term721 _99873 s t x.
Proof. exact (proj1 (@lem3853733 _99873 s t x h1)). Qed.
Lemma lem3853739 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) (h1 : term726 _99873 t s x) : term726 _99873 t s x.
Proof. exact (h1). Qed.
Lemma lem3853740 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) (h1 : term719 _99873 t s x) : term719 _99873 t s x.
Proof. exact (h1). Qed.
Lemma lem3853742 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) (h1 : term726 _99873 t s x) : term723 _99873 s t x.
Proof. exact (proj1 (@lem3853739 _99873 t s x h1)). Qed.
Lemma lem3853743 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) (x : _99873) (h1 : term721 _99873 s t x) : term721 _99873 s t x.
Proof. exact (h1). Qed.
Lemma lem3853748 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) (h1 : term719 _99873 t s x) : term717 _99873 s t x.
Proof. exact (proj1 (@lem3853740 _99873 t s x h1)). Qed.
Lemma lem3853750 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) (h1 : term719 _99873 t s x) : term715 _99873 s t x.
Proof. exact (proj1 (@lem3853748 _99873 t s x h1)). Qed.
Lemma lem3853818 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) : (term708 _99873 t s x) = (term708 _99873 t s x).
Proof. exact (eq_refl (term708 _99873 t s x)). Qed.
Lemma lem3853819 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term709 _99873 t s) = (term709 _99873 t s).
Proof. exact (fun_ext (fun x : _99873 => @lem3853818 _99873 t s x)). Qed.
Lemma lem3853820 {_99873 : Type'} : (@all _99873) = (@all _99873).
Proof. exact (eq_refl (@all _99873)). Qed.
Lemma lem3853822 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term710 _99873 t s) = (term710 _99873 t s).
Proof. exact (MK_COMB (@lem3853820 _99873) (@lem3853819 _99873 t s)). Qed.
Lemma lem3853823 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (h1 : term567 _99873 t s) : term710 _99873 t s.
Proof. exact (EQ_MP (@lem3853822 _99873 t s) (@lem3853732 _99873 t s h1)). Qed.
Lemma lem3853835 {_99873 : Type'} (t : _99873 -> Prop) (x : _99873) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3853864 {_99873 : Type'} (s : _99873 -> Prop) (x : _99873) (h1 : term713 _99873 s x) : term713 _99873 s x.
Proof. exact (h1). Qed.
Lemma lem3853893 {_99873 : Type'} (t : _99873 -> Prop) (x : _99873) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3853900 {_99873 : Type'} (_44744 : _99873) (t : _99873 -> Prop) (s : _99873 -> Prop) (h1 : term567 _99873 t s) : term733 _99873 t s _44744.
Proof. exact (@lem3853823 _99873 t s h1 _44744). Qed.
Lemma lem3853901 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (_44744 : _99873) : (term733 _99873 t s _44744) = (term708 _99873 t s _44744).
Proof. exact (eq_refl (term733 _99873 t s _44744)). Qed.
Lemma lem3853922 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) (x : _99873) (h1 : term730 _99873 s t x) : term578 _99873 t x.
Proof. exact (proj2 (@lem3853736 _99873 s t x h1)). Qed.
Lemma lem3853932 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) (h1 : term726 _99873 t s x) : term713 _99873 s x.
Proof. exact (proj2 (@lem3853739 _99873 t s x h1)). Qed.
Lemma lem3853942 {_99873 : Type'} (_44744 : _99873) (t : _99873 -> Prop) (s : _99873 -> Prop) (h1 : term567 _99873 t s) : term708 _99873 t s _44744.
Proof. exact (EQ_MP (@lem3853901 _99873 t s _44744) (@lem3853900 _99873 _44744 t s h1)). Qed.
Lemma lem3853946 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) (h1 : term726 _99873 t s x) : term713 _99873 s x.
Proof. exact (proj2 (@lem3853739 _99873 t s x h1)). Qed.
Lemma lem3853948 {_99873 : Type'} (t : _99873 -> Prop) (x : _99873) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3853962 {_99873 : Type'} (s : _99873 -> Prop) (x : _99873) (h1 : term713 _99873 s x) : term713 _99873 s x.
Proof. exact (h1). Qed.
Lemma lem3853974 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) (h1 : term719 _99873 t s x) : term578 _99873 t x.
Proof. exact (proj2 (@lem3853748 _99873 t s x h1)). Qed.
Lemma lem3853976 {_99873 : Type'} (t : _99873 -> Prop) (x : _99873) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3853978 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) (x : _99873) (h1 : term730 _99873 s t x) : t x.
Proof. exact (proj2 (@lem3853733 _99873 s t x h1)). Qed.
Lemma lem3853979 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) (x : _99873) (h1 : term730 _99873 s t x) : term734 _99873 t x.
Proof. exact (fun h0 : term578 _99873 t x => @lem3853978 _99873 s t x h1). Qed.
Lemma lem3853981 (p : Prop) : (term735 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3853982 {_99873 : Type'} (t : _99873 -> Prop) (x : _99873) : (term734 _99873 t x) = (t x).
Proof. exact (@lem3853981 (t x)). Qed.
Lemma lem3853983 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) (x : _99873) (h1 : term730 _99873 s t x) : t x.
Proof. exact (EQ_MP (@lem3853982 _99873 t x) (@lem3853979 _99873 s t x h1)). Qed.
Lemma lem3853986 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3853988 {_99873 : Type'} (t : _99873 -> Prop) (x : _99873) : (term578 _99873 t x) = (term736 _99873 t x).
Proof. exact (@lem3853986 (t x)). Qed.
Lemma lem3853991 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) (x : _99873) (h1 : term730 _99873 s t x) : term736 _99873 t x.
Proof. exact (EQ_MP (@lem3853988 _99873 t x) (@lem3853922 _99873 s t x h1)). Qed.
Lemma lem3853994 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) (x : _99873) (h1 : term730 _99873 s t x) : False.
Proof. exact (@lem3853991 _99873 s t x h1 (@lem3853983 _99873 s t x h1)). Qed.
Lemma lem3853995 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) (x : _99873) (h1 : term730 _99873 s t x) : term737.
Proof. exact (fun h0 : ~ False => @lem3853994 _99873 s t x h1). Qed.
Lemma lem3853997 (p : Prop) : (term735 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3853998 : term737 = False.
Proof. exact (@lem3853997 False). Qed.
Lemma lem3853999 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) (x : _99873) (h1 : term730 _99873 s t x) : False.
Proof. exact (EQ_MP (@lem3853998) (@lem3853995 _99873 s t x h1)). Qed.
Lemma lem3854001 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) (x : _99873) (h1 : term721 _99873 s t x) : @I (_99873 -> Prop) s x.
Proof. exact (proj1 (@lem3853743 _99873 s t x h1)). Qed.
Lemma lem3854002 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) (x : _99873) (h1 : term721 _99873 s t x) : term738 _99873 s x.
Proof. exact (fun h0 : term713 _99873 s x => @lem3854001 _99873 s t x h1). Qed.
Lemma lem3854004 (p : Prop) : (term735 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3854005 {_99873 : Type'} (s : _99873 -> Prop) (x : _99873) : (term738 _99873 s x) = (@I (_99873 -> Prop) s x).
Proof. exact (@lem3854004 (@I (_99873 -> Prop) s x)). Qed.
Lemma lem3854006 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) (x : _99873) (h1 : term721 _99873 s t x) : @I (_99873 -> Prop) s x.
Proof. exact (EQ_MP (@lem3854005 _99873 s x) (@lem3854002 _99873 s t x h1)). Qed.
Lemma lem3854009 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3854011 {_99873 : Type'} (s : _99873 -> Prop) (x : _99873) : (term713 _99873 s x) = (term739 _99873 s x).
Proof. exact (@lem3854009 (@I (_99873 -> Prop) s x)). Qed.
Lemma lem3854014 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) (h1 : term726 _99873 t s x) : term739 _99873 s x.
Proof. exact (EQ_MP (@lem3854011 _99873 s x) (@lem3853932 _99873 t s x h1)). Qed.
Lemma lem3854017 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) (h1 : term721 _99873 s t x) (h2 : term726 _99873 t s x) : False.
Proof. exact (@lem3854014 _99873 t s x h2 (@lem3854006 _99873 s t x h1)). Qed.
Lemma lem3854018 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) (h1 : term721 _99873 s t x) (h2 : term726 _99873 t s x) : term737.
Proof. exact (fun h0 : ~ False => @lem3854017 _99873 t s x h1 h2). Qed.
Lemma lem3854020 (p : Prop) : (term735 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3854021 : term737 = False.
Proof. exact (@lem3854020 False). Qed.
Lemma lem3854022 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) (h1 : term721 _99873 s t x) (h2 : term726 _99873 t s x) : False.
Proof. exact (EQ_MP (@lem3854021) (@lem3854018 _99873 t s x h1 h2)). Qed.
Lemma lem3854024 {_99873 : Type'} (t : _99873 -> Prop) (x : _99873) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3854025 {_99873 : Type'} (t : _99873 -> Prop) (x : _99873) (h1 : t x) : term734 _99873 t x.
Proof. exact (fun h0 : term578 _99873 t x => @lem3854024 _99873 t x h1). Qed.
Lemma lem3854027 (p : Prop) : (term735 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3854028 {_99873 : Type'} (t : _99873 -> Prop) (x : _99873) : (term734 _99873 t x) = (t x).
Proof. exact (@lem3854027 (t x)). Qed.
Lemma lem3854029 {_99873 : Type'} (t : _99873 -> Prop) (x : _99873) (h1 : t x) : t x.
Proof. exact (EQ_MP (@lem3854028 _99873 t x) (@lem3854025 _99873 t x h1)). Qed.
Lemma lem3854035 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3854036 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) (_44744 : _99873) : (term708 _99873 t s _44744) = (term740 _99873 s t _44744).
Proof. exact (@lem3854035 (@I (_99873 -> Prop) s _44744) (term578 _99873 t _44744)). Qed.
Lemma lem3854042 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3854043 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) (_44744 : _99873) : (term741 _99873 t s _44744) = (term742 _99873 s t _44744).
Proof. exact (MK_COMB (@lem3854042) (@lem3854036 _99873 s t _44744)). Qed.
Lemma lem3854049 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) (_44744 : _99873) : (term740 _99873 s t _44744) = (term740 _99873 s t _44744).
Proof. exact (eq_refl (term740 _99873 s t _44744)). Qed.
Lemma lem3854050 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) (_44744 : _99873) : ((term708 _99873 t s _44744) = (term740 _99873 s t _44744)) = ((term740 _99873 s t _44744) = (term740 _99873 s t _44744)).
Proof. exact (MK_COMB (@lem3854043 _99873 s t _44744) (@lem3854049 _99873 s t _44744)). Qed.
Lemma lem3854052 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3854053 (x : Prop) : (x = x) = True.
Proof. exact (@lem3854052 Prop x). Qed.
Lemma lem3854054 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) (_44744 : _99873) : ((term740 _99873 s t _44744) = (term740 _99873 s t _44744)) = True.
Proof. exact (@lem3854053 (term740 _99873 s t _44744)). Qed.
Lemma lem3854055 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) (_44744 : _99873) : ((term708 _99873 t s _44744) = (term740 _99873 s t _44744)) = True.
Proof. exact (TRANS (@lem3854050 _99873 s t _44744) (@lem3854054 _99873 s t _44744)). Qed.
Lemma lem3854056 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) (_44744 : _99873) : True = ((term708 _99873 t s _44744) = (term740 _99873 s t _44744)).
Proof. exact (SYM (@lem3854055 _99873 s t _44744)). Qed.
Lemma lem3854057 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) (_44744 : _99873) : (term708 _99873 t s _44744) = (term740 _99873 s t _44744).
Proof. exact (EQ_MP (@lem3854056 _99873 s t _44744) (@lem0)). Qed.
Lemma lem3854058 {_99873 : Type'} (_44744 : _99873) (t : _99873 -> Prop) (s : _99873 -> Prop) (h1 : term567 _99873 t s) : term740 _99873 s t _44744.
Proof. exact (EQ_MP (@lem3854057 _99873 s t _44744) (@lem3853942 _99873 _44744 t s h1)). Qed.
Lemma lem3854060 (b : Prop) (a : Prop) : (a \/ b) = (term743 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3854061 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (_44744 : _99873) : (term740 _99873 s t _44744) = (term744 _99873 t s _44744).
Proof. exact (@lem3854060 (term578 _99873 t _44744) (@I (_99873 -> Prop) s _44744)). Qed.
Lemma lem3854063 (a : Prop) : (term154 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3854064 {_99873 : Type'} (t : _99873 -> Prop) (_44744 : _99873) : (term636 _99873 t _44744) = (t _44744).
Proof. exact (@lem3854063 (t _44744)). Qed.
Lemma lem3854065 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3854066 {_99873 : Type'} (t : _99873 -> Prop) (_44744 : _99873) : (term745 _99873 t _44744) = (term560 _99873 t _44744).
Proof. exact (MK_COMB (@lem3854065) (@lem3854064 _99873 t _44744)). Qed.
Lemma lem3854067 {_99873 : Type'} (s : _99873 -> Prop) (_44744 : _99873) : (@I (_99873 -> Prop) s _44744) = (@I (_99873 -> Prop) s _44744).
Proof. exact (eq_refl (@I (_99873 -> Prop) s _44744)). Qed.
Lemma lem3854068 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (_44744 : _99873) : (term744 _99873 t s _44744) = (term746 _99873 t s _44744).
Proof. exact (MK_COMB (@lem3854066 _99873 t _44744) (@lem3854067 _99873 s _44744)). Qed.
Lemma lem3854069 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (_44744 : _99873) : (term740 _99873 s t _44744) = (term746 _99873 t s _44744).
Proof. exact (TRANS (@lem3854061 _99873 t s _44744) (@lem3854068 _99873 t s _44744)). Qed.
Lemma lem3854072 {_99873 : Type'} (_44744 : _99873) (t : _99873 -> Prop) (s : _99873 -> Prop) (h1 : term567 _99873 t s) : term746 _99873 t s _44744.
Proof. exact (EQ_MP (@lem3854069 _99873 t s _44744) (@lem3854058 _99873 _44744 t s h1)). Qed.
Lemma lem3854073 {_99873 : Type'} (_44744 : _99873) (t : _99873 -> Prop) (s : _99873 -> Prop) (h1 : term567 _99873 t s) : term746 _99873 t s _44744.
Proof. exact (@lem3854072 _99873 _44744 t s h1). Qed.
Lemma lem3854074 {_99873 : Type'} (x : _99873) (t : _99873 -> Prop) (s : _99873 -> Prop) (h1 : term567 _99873 t s) : term746 _99873 t s x.
Proof. exact (@lem3854073 _99873 x t s h1). Qed.
Lemma lem3854077 {_99873 : Type'} (x : _99873) (t : _99873 -> Prop) (s : _99873 -> Prop) (h1 : t x) (h2 : term567 _99873 t s) : @I (_99873 -> Prop) s x.
Proof. exact (@lem3854074 _99873 x t s h2 (@lem3854029 _99873 t x h1)). Qed.
Lemma lem3854078 {_99873 : Type'} (x : _99873) (t : _99873 -> Prop) (s : _99873 -> Prop) (h1 : t x) (h2 : term567 _99873 t s) : term738 _99873 s x.
Proof. exact (fun h0 : term713 _99873 s x => @lem3854077 _99873 x t s h1 h2). Qed.
Lemma lem3854080 (p : Prop) : (term735 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3854081 {_99873 : Type'} (s : _99873 -> Prop) (x : _99873) : (term738 _99873 s x) = (@I (_99873 -> Prop) s x).
Proof. exact (@lem3854080 (@I (_99873 -> Prop) s x)). Qed.
Lemma lem3854082 {_99873 : Type'} (x : _99873) (t : _99873 -> Prop) (s : _99873 -> Prop) (h1 : t x) (h2 : term567 _99873 t s) : @I (_99873 -> Prop) s x.
Proof. exact (EQ_MP (@lem3854081 _99873 s x) (@lem3854078 _99873 x t s h1 h2)). Qed.
Lemma lem3854085 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3854087 {_99873 : Type'} (s : _99873 -> Prop) (x : _99873) : (term713 _99873 s x) = (term739 _99873 s x).
Proof. exact (@lem3854085 (@I (_99873 -> Prop) s x)). Qed.
Lemma lem3854090 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) (h1 : term726 _99873 t s x) : term739 _99873 s x.
Proof. exact (EQ_MP (@lem3854087 _99873 s x) (@lem3853946 _99873 t s x h1)). Qed.
Lemma lem3854093 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) (h1 : t x) (h2 : term567 _99873 t s) (h3 : term726 _99873 t s x) : False.
Proof. exact (@lem3854090 _99873 t s x h3 (@lem3854082 _99873 x t s h1 h2)). Qed.
Lemma lem3854094 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) (h1 : t x) (h2 : term567 _99873 t s) (h3 : term726 _99873 t s x) : term737.
Proof. exact (fun h0 : ~ False => @lem3854093 _99873 t s x h1 h2 h3). Qed.
Lemma lem3854096 (p : Prop) : (term735 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3854097 : term737 = False.
Proof. exact (@lem3854096 False). Qed.
Lemma lem3854098 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) (h1 : t x) (h2 : term567 _99873 t s) (h3 : term726 _99873 t s x) : False.
Proof. exact (EQ_MP (@lem3854097) (@lem3854094 _99873 t s x h1 h2 h3)). Qed.
Lemma lem3854100 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) (h1 : term719 _99873 t s x) : @I (_99873 -> Prop) s x.
Proof. exact (proj2 (@lem3853740 _99873 t s x h1)). Qed.
Lemma lem3854101 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) (h1 : term719 _99873 t s x) : term738 _99873 s x.
Proof. exact (fun h0 : term713 _99873 s x => @lem3854100 _99873 t s x h1). Qed.
Lemma lem3854103 (p : Prop) : (term735 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3854104 {_99873 : Type'} (s : _99873 -> Prop) (x : _99873) : (term738 _99873 s x) = (@I (_99873 -> Prop) s x).
Proof. exact (@lem3854103 (@I (_99873 -> Prop) s x)). Qed.
Lemma lem3854105 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) (h1 : term719 _99873 t s x) : @I (_99873 -> Prop) s x.
Proof. exact (EQ_MP (@lem3854104 _99873 s x) (@lem3854101 _99873 t s x h1)). Qed.
Lemma lem3854108 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3854110 {_99873 : Type'} (s : _99873 -> Prop) (x : _99873) : (term713 _99873 s x) = (term739 _99873 s x).
Proof. exact (@lem3854108 (@I (_99873 -> Prop) s x)). Qed.
Lemma lem3854113 {_99873 : Type'} (s : _99873 -> Prop) (x : _99873) (h1 : term713 _99873 s x) : term739 _99873 s x.
Proof. exact (EQ_MP (@lem3854110 _99873 s x) (@lem3853962 _99873 s x h1)). Qed.
Lemma lem3854116 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) (h1 : term713 _99873 s x) (h2 : term719 _99873 t s x) : False.
Proof. exact (@lem3854113 _99873 s x h1 (@lem3854105 _99873 t s x h2)). Qed.
Lemma lem3854117 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) (h1 : term713 _99873 s x) (h2 : term719 _99873 t s x) : term737.
Proof. exact (fun h0 : ~ False => @lem3854116 _99873 t s x h1 h2). Qed.
Lemma lem3854119 (p : Prop) : (term735 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3854120 : term737 = False.
Proof. exact (@lem3854119 False). Qed.
Lemma lem3854121 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) (h1 : term713 _99873 s x) (h2 : term719 _99873 t s x) : False.
Proof. exact (EQ_MP (@lem3854120) (@lem3854117 _99873 t s x h1 h2)). Qed.
Lemma lem3854123 {_99873 : Type'} (t : _99873 -> Prop) (x : _99873) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3854124 {_99873 : Type'} (t : _99873 -> Prop) (x : _99873) (h1 : t x) : term734 _99873 t x.
Proof. exact (fun h0 : term578 _99873 t x => @lem3854123 _99873 t x h1). Qed.
Lemma lem3854126 (p : Prop) : (term735 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3854127 {_99873 : Type'} (t : _99873 -> Prop) (x : _99873) : (term734 _99873 t x) = (t x).
Proof. exact (@lem3854126 (t x)). Qed.
Lemma lem3854128 {_99873 : Type'} (t : _99873 -> Prop) (x : _99873) (h1 : t x) : t x.
Proof. exact (EQ_MP (@lem3854127 _99873 t x) (@lem3854124 _99873 t x h1)). Qed.
Lemma lem3854131 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3854133 {_99873 : Type'} (t : _99873 -> Prop) (x : _99873) : (term578 _99873 t x) = (term736 _99873 t x).
Proof. exact (@lem3854131 (t x)). Qed.
Lemma lem3854136 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) (h1 : term719 _99873 t s x) : term736 _99873 t x.
Proof. exact (EQ_MP (@lem3854133 _99873 t x) (@lem3853974 _99873 t s x h1)). Qed.
Lemma lem3854139 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) (h1 : t x) (h2 : term719 _99873 t s x) : False.
Proof. exact (@lem3854136 _99873 t s x h2 (@lem3854128 _99873 t x h1)). Qed.
Lemma lem3854140 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) (h1 : t x) (h2 : term719 _99873 t s x) : term737.
Proof. exact (fun h0 : ~ False => @lem3854139 _99873 t s x h1 h2). Qed.
Lemma lem3854142 (p : Prop) : (term735 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3854143 : term737 = False.
Proof. exact (@lem3854142 False). Qed.
Lemma lem3854144 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) (h1 : t x) (h2 : term719 _99873 t s x) : False.
Proof. exact (EQ_MP (@lem3854143) (@lem3854140 _99873 t s x h1 h2)). Qed.
Lemma lem3854145 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) (h1 : t x) (h2 : term719 _99873 t s x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3854144 _99873 t s x h1 h2) (fun h3 : False => @lem3853976 _99873 t x h1)). Qed.
Lemma lem3854146 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) (h1 : t x) (h2 : term719 _99873 t s x) : False.
Proof. exact (EQ_MP (@lem3854145 _99873 t s x h1 h2) (@lem3853976 _99873 t x h1)). Qed.
Lemma lem3854147 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) (h1 : term713 _99873 s x) (h2 : term719 _99873 t s x) : (term713 _99873 s x) = False.
Proof. exact (prop_ext (fun h3 : term713 _99873 s x => @lem3854121 _99873 t s x h1 h2) (fun h3 : False => @lem3853962 _99873 s x h1)). Qed.
Lemma lem3854148 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) (h1 : term713 _99873 s x) (h2 : term719 _99873 t s x) : False.
Proof. exact (EQ_MP (@lem3854147 _99873 t s x h1 h2) (@lem3853962 _99873 s x h1)). Qed.
Lemma lem3854149 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) (h1 : t x) (h2 : term567 _99873 t s) (h3 : term726 _99873 t s x) : (t x) = False.
Proof. exact (prop_ext (fun h4 : t x => @lem3854098 _99873 t s x h1 h2 h3) (fun h4 : False => @lem3853948 _99873 t x h1)). Qed.
Lemma lem3854150 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) (h1 : t x) (h2 : term567 _99873 t s) (h3 : term726 _99873 t s x) : False.
Proof. exact (EQ_MP (@lem3854149 _99873 t s x h1 h2 h3) (@lem3853948 _99873 t x h1)). Qed.
Lemma lem3854151 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) (h1 : t x) (h2 : term719 _99873 t s x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3854146 _99873 t s x h1 h2) (fun h3 : False => @lem3853893 _99873 t x h1)). Qed.
Lemma lem3854152 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) (h1 : t x) (h2 : term719 _99873 t s x) : False.
Proof. exact (EQ_MP (@lem3854151 _99873 t s x h1 h2) (@lem3853893 _99873 t x h1)). Qed.
Lemma lem3854153 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) (h1 : term713 _99873 s x) (h2 : term719 _99873 t s x) : (term713 _99873 s x) = False.
Proof. exact (prop_ext (fun h3 : term713 _99873 s x => @lem3854148 _99873 t s x h1 h2) (fun h3 : False => @lem3853864 _99873 s x h1)). Qed.
Lemma lem3854154 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) (h1 : term713 _99873 s x) (h2 : term719 _99873 t s x) : False.
Proof. exact (EQ_MP (@lem3854153 _99873 t s x h1 h2) (@lem3853864 _99873 s x h1)). Qed.
Lemma lem3854155 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) (h1 : t x) (h2 : term567 _99873 t s) (h3 : term726 _99873 t s x) : (t x) = False.
Proof. exact (prop_ext (fun h4 : t x => @lem3854150 _99873 t s x h1 h2 h3) (fun h4 : False => @lem3853835 _99873 t x h1)). Qed.
Lemma lem3854156 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) (h1 : t x) (h2 : term567 _99873 t s) (h3 : term726 _99873 t s x) : False.
Proof. exact (EQ_MP (@lem3854155 _99873 t s x h1 h2 h3) (@lem3853835 _99873 t x h1)). Qed.
Lemma lem3854157 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) (h1 : t x) (h2 : term719 _99873 t s x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3854152 _99873 t s x h1 h2) (fun h3 : False => @lem3853893 _99873 t x h1)). Qed.
Lemma lem3854158 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) (h1 : t x) (h2 : term719 _99873 t s x) : False.
Proof. exact (EQ_MP (@lem3854157 _99873 t s x h1 h2) (@lem3853893 _99873 t x h1)). Qed.
Lemma lem3854159 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) (h1 : term713 _99873 s x) (h2 : term719 _99873 t s x) : (term713 _99873 s x) = False.
Proof. exact (prop_ext (fun h3 : term713 _99873 s x => @lem3854154 _99873 t s x h1 h2) (fun h3 : False => @lem3853864 _99873 s x h1)). Qed.
Lemma lem3854160 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) (h1 : term713 _99873 s x) (h2 : term719 _99873 t s x) : False.
Proof. exact (EQ_MP (@lem3854159 _99873 t s x h1 h2) (@lem3853864 _99873 s x h1)). Qed.
Lemma lem3854161 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) (h1 : t x) (h2 : term567 _99873 t s) (h3 : term726 _99873 t s x) : (t x) = False.
Proof. exact (prop_ext (fun h4 : t x => @lem3854156 _99873 t s x h1 h2 h3) (fun h4 : False => @lem3853835 _99873 t x h1)). Qed.
Lemma lem3854162 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) (h1 : t x) (h2 : term567 _99873 t s) (h3 : term726 _99873 t s x) : False.
Proof. exact (EQ_MP (@lem3854161 _99873 t s x h1 h2 h3) (@lem3853835 _99873 t x h1)). Qed.
Lemma lem3854163 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) (h1 : term719 _99873 t s x) : False.
Proof. exact (or_elim (@lem3853750 _99873 t s x h1) (fun h0 : term713 _99873 s x => @lem3854160 _99873 t s x h0 h1) (fun h0 : t x => @lem3854158 _99873 t s x h0 h1)). Qed.
Lemma lem3854164 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) (h1 : term567 _99873 t s) (h2 : term726 _99873 t s x) : False.
Proof. exact (or_elim (@lem3853742 _99873 t s x h2) (fun h0 : term721 _99873 s t x => @lem3854022 _99873 t s x h0 h2) (fun h0 : t x => @lem3854162 _99873 t s x h0 h1 h2)). Qed.
Lemma lem3854165 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) (h1 : term567 _99873 t s) (h2 : term728 _99873 t s x) : False.
Proof. exact (or_elim (@lem3853734 _99873 t s x h2) (fun h0 : term726 _99873 t s x => @lem3854164 _99873 t s x h1 h0) (fun h0 : term719 _99873 t s x => @lem3854163 _99873 t s x h0)). Qed.
Lemma lem3854166 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (x : _99873) (h1 : term567 _99873 t s) (h2 : term704 _99873 t s x) : False.
Proof. exact (or_elim (@lem3853730 _99873 t s x h2) (fun h0 : term730 _99873 s t x => @lem3853999 _99873 s t x h0) (fun h0 : term728 _99873 t s x => @lem3854165 _99873 t s x h1 h0)). Qed.
Lemma lem3854167 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (h1 : term620 _99873 t s) (h2 : term567 _99873 t s) : False.
Proof. exact (ex_elim (@lem3853604 _99873 t s h1) (fun x : _99873 => fun h0 : term706 _99873 t s x => @lem3854166 _99873 t s x h2 h0)). Qed.
Lemma lem3854168 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (h1 : term620 _99873 t s) (h2 : term567 _99873 t s) : (term620 _99873 t s) = False.
Proof. exact (prop_ext (fun h3 : term620 _99873 t s => @lem3854167 _99873 t s h1 h2) (fun h3 : False => @lem3853279 _99873 t s h1)). Qed.
Lemma lem3854169 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (h1 : term620 _99873 t s) (h2 : term567 _99873 t s) : False.
Proof. exact (EQ_MP (@lem3854168 _99873 t s h1 h2) (@lem3853279 _99873 t s h1)). Qed.
Lemma lem3854170 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (h1 : term567 _99873 t s) : term619 _99873 t s.
Proof. exact (fun h0 : term620 _99873 t s => @lem3854169 _99873 t s h0 h1). Qed.
Lemma lem3854171 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (h1 : term567 _99873 t s) : term602 _99873 t s.
Proof. exact (EQ_MP (@lem3853278 _99873 t s) (@lem3854170 _99873 t s h1)). Qed.
Lemma lem3854172 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : term603 _99873 t s.
Proof. exact (fun h0 : term567 _99873 t s => @lem3854171 _99873 t s h0). Qed.
Lemma lem3854177 {_99873 : Type'} (s : _99873 -> Prop) : term614 _99873 s.
Proof. exact (fun t : _99873 -> Prop => @lem3854172 _99873 t s). Qed.
Lemma lem3854182 {_99873 : Type'} : term618 _99873.
Proof. exact (fun s : _99873 -> Prop => @lem3854177 _99873 s). Qed.
Lemma lem3854183 {_99873 : Type'} : term617 _99873.
Proof. exact (EQ_MP (@lem3853273 _99873) (@lem3854182 _99873)). Qed.
Lemma lem3854184 {_99873 : Type'} (s : _99873 -> Prop) : term747 _99873 s.
Proof. exact (@lem3854183 _99873 s). Qed.
Lemma lem3854185 {_99873 : Type'} (s : _99873 -> Prop) : (term747 _99873 s) = (term613 _99873 s).
Proof. exact (eq_refl (term747 _99873 s)). Qed.
Lemma lem3854186 {_99873 : Type'} (s : _99873 -> Prop) : term613 _99873 s.
Proof. exact (EQ_MP (@lem3854185 _99873 s) (@lem3854184 _99873 s)). Qed.
Lemma lem3854187 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) : term748 _99873 s t.
Proof. exact (@lem3854186 _99873 s t). Qed.
Lemma lem3854188 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : (term748 _99873 s t) = (term605 _99873 t s).
Proof. exact (eq_refl (term748 _99873 s t)). Qed.
Lemma lem3854189 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : term605 _99873 t s.
Proof. exact (EQ_MP (@lem3854188 _99873 t s) (@lem3854187 _99873 s t)). Qed.
Lemma lem3854191 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : term605 _99873 t s.
Proof. exact (@lem3853104 _99873 t s (@lem3854189 _99873 t s)). Qed.
Lemma lem3854192 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (h1 : term606 _99873 t s) : False.
Proof. exact (@lem3854191 _99873 t s (@lem3853088 _99873 t s h1)). Qed.
Lemma lem3854193 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (h1 : term606 _99873 t s) : (term606 _99873 t s) = False.
Proof. exact (prop_ext (fun h2 : term606 _99873 t s => @lem3854192 _99873 t s h1) (fun h2 : False => @lem3853088 _99873 t s h1)). Qed.
Lemma lem3854194 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (h1 : term606 _99873 t s) : False.
Proof. exact (EQ_MP (@lem3854193 _99873 t s h1) (@lem3853088 _99873 t s h1)). Qed.
Lemma lem3854195 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : term605 _99873 t s.
Proof. exact (fun h0 : term606 _99873 t s => @lem3854194 _99873 t s h0). Qed.
Lemma lem3854196 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : term603 _99873 t s.
Proof. exact (EQ_MP (@lem3853087 _99873 t s) (@lem3854195 _99873 t s)). Qed.
Lemma lem3854197 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : term558 _99873 t s.
Proof. exact (EQ_MP (@lem3853083 _99873 t s) (@lem3854196 _99873 t s)). Qed.
Lemma lem3854198 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) : term557 _99873 t s.
Proof. exact (EQ_MP (@lem3852911 _99873 t s) (@lem3854197 _99873 t s)). Qed.
Lemma lem3854199 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (h1 : @FINITE _99873 s) (h2 : @SUBSET _99873 t s) : term539 _99873 t s.
Proof. exact (@lem3854198 _99873 t s (@lem3852850 _99873 t s h1 h2)). Qed.
Lemma lem3854200 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (h1 : @FINITE _99873 s) (h2 : @SUBSET _99873 t s) : term540 _99873 t s.
Proof. exact (EQ_MP (@lem3852839 _99873 t s h1) (@lem3854199 _99873 t s h1 h2)). Qed.
Lemma lem3854201 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (h1 : @FINITE _99873 s) (h2 : @SUBSET _99873 t s) : (term749 _99873 s t) = (@CARD _99873 s).
Proof. exact (@lem3852810 _99873 t s (@lem3854200 _99873 t s h1 h2)). Qed.
Lemma lem3854202 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (h1 : @FINITE _99873 s) (h2 : @SUBSET _99873 t s) : (term536 _99873 s t) = (term750 _99873 s t).
Proof. exact (@lem3852806 _99873 s t (@lem3854201 _99873 t s h1 h2)). Qed.
Lemma lem3854203 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (h1 : term534 _99873 t s) : @SUBSET _99873 t s.
Proof. exact (proj2 (@lem3852801 _99873 t s h1)). Qed.
Lemma lem3854204 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (h1 : term534 _99873 t s) : @FINITE _99873 s.
Proof. exact (proj1 (@lem3852801 _99873 t s h1)). Qed.
Lemma lem3854205 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (h1 : @FINITE _99873 s) (h2 : @SUBSET _99873 t s) : (@SUBSET _99873 t s) = ((term536 _99873 s t) = (term750 _99873 s t)).
Proof. exact (prop_ext (fun h3 : @SUBSET _99873 t s => @lem3854202 _99873 t s h1 h2) (fun h3 : (term536 _99873 s t) = (term750 _99873 s t) => @lem3852802 _99873 t s h2)). Qed.
Lemma lem3854206 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (h1 : @FINITE _99873 s) (h2 : @SUBSET _99873 t s) : (term536 _99873 s t) = (term750 _99873 s t).
Proof. exact (EQ_MP (@lem3854205 _99873 t s h1 h2) (@lem3852802 _99873 t s h2)). Qed.
Lemma lem3854207 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (h1 : @FINITE _99873 s) (h2 : @SUBSET _99873 t s) : (@FINITE _99873 s) = ((term536 _99873 s t) = (term750 _99873 s t)).
Proof. exact (prop_ext (fun h3 : @FINITE _99873 s => @lem3854206 _99873 t s h1 h2) (fun h3 : (term536 _99873 s t) = (term750 _99873 s t) => @lem3852803 _99873 s h1)). Qed.
Lemma lem3854208 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (h1 : @FINITE _99873 s) (h2 : @SUBSET _99873 t s) : (term536 _99873 s t) = (term750 _99873 s t).
Proof. exact (EQ_MP (@lem3854207 _99873 t s h1 h2) (@lem3852803 _99873 s h1)). Qed.
Lemma lem3854209 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (h1 : @FINITE _99873 s) (h2 : term534 _99873 t s) : (@SUBSET _99873 t s) = ((term536 _99873 s t) = (term750 _99873 s t)).
Proof. exact (prop_ext (fun h3 : @SUBSET _99873 t s => @lem3854208 _99873 t s h1 h3) (fun h3 : (term536 _99873 s t) = (term750 _99873 s t) => @lem3854203 _99873 t s h2)). Qed.
Lemma lem3854210 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (h1 : @FINITE _99873 s) (h2 : term534 _99873 t s) : (term536 _99873 s t) = (term750 _99873 s t).
Proof. exact (EQ_MP (@lem3854209 _99873 t s h1 h2) (@lem3854203 _99873 t s h2)). Qed.
Lemma lem3854211 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (h1 : term534 _99873 t s) : (@FINITE _99873 s) = ((term536 _99873 s t) = (term750 _99873 s t)).
Proof. exact (prop_ext (fun h2 : @FINITE _99873 s => @lem3854210 _99873 t s h2 h1) (fun h2 : (term536 _99873 s t) = (term750 _99873 s t) => @lem3854204 _99873 t s h1)). Qed.
Lemma lem3854212 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (h1 : term534 _99873 t s) : (term536 _99873 s t) = (term750 _99873 s t).
Proof. exact (EQ_MP (@lem3854211 _99873 t s h1) (@lem3854204 _99873 t s h1)). Qed.
Lemma lem3854213 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) : term751 _99873 s t.
Proof. exact (fun h0 : term534 _99873 t s => @lem3854212 _99873 t s h0). Qed.
Lemma lem3854218 {_99873 : Type'} (s : _99873 -> Prop) : term752 _99873 s.
Proof. exact (fun t : _99873 -> Prop => @lem3854213 _99873 s t). Qed.
Lemma lem3854223 {_99873 : Type'} : term753 _99873.
Proof. exact (fun s : _99873 -> Prop => @lem3854218 _99873 s). Qed.
