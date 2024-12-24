Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm938648_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
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
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm514761_spec.
Require Import thm515543_spec.
Require Import thm515916_spec.
Require Import thm516204_spec.
Require Import thm69_spec.
Require Import thm75543_spec.
Lemma lem937834 : term0.
Proof. exact (EQ_MP (@lem515916) (@lem516204)). Qed.
Lemma lem937835 : term1.
Proof. exact (proj2 (@lem937834)). Qed.
Lemma lem937836 : term2.
Proof. exact (proj2 (@lem937835)). Qed.
Lemma lem937837 : term3.
Proof. exact (proj2 (@lem937836)). Qed.
Lemma lem937838 : term4.
Proof. exact (proj2 (@lem937837)). Qed.
Lemma lem937839 : term5.
Proof. exact (proj2 (@lem937838)). Qed.
Lemma lem937840 : term6.
Proof. exact (proj2 (@lem937839)). Qed.
Lemma lem937841 : term7.
Proof. exact (proj2 (@lem937840)). Qed.
Lemma lem937857 : term8.
Proof. exact (proj1 (@lem937841)). Qed.
Lemma lem937858 (n : nat) : term9 n.
Proof. exact (@lem937857 n). Qed.
Lemma lem937859 (n : nat) : (term9 n) = ((term10 n) = 0).
Proof. exact (eq_refl (term9 n)). Qed.
Lemma lem937875 : term11.
Proof. exact (proj1 (@lem937838)). Qed.
Lemma lem937876 (n : nat) : term12 n.
Proof. exact (@lem937875 n). Qed.
Lemma lem937877 (n : nat) : (term12 n) = ((term13 n) = (term14 n)).
Proof. exact (eq_refl (term12 n)). Qed.
Lemma lem937888 : term15.
Proof. exact (proj1 (@lem937834)). Qed.
Lemma lem937889 (m : nat) : term16 m.
Proof. exact (@lem937888 m). Qed.
Lemma lem937890 (m : nat) : (term16 m) = (term17 m).
Proof. exact (eq_refl (term16 m)). Qed.
Lemma lem937891 (m : nat) : term17 m.
Proof. exact (EQ_MP (@lem937890 m) (@lem937889 m)). Qed.
Lemma lem937892 (m : nat) (n : nat) : term18 m n.
Proof. exact (@lem937891 m n). Qed.
Lemma lem937893 (m : nat) (n : nat) : (term18 m n) = ((term19 m n) = (term20 m n)).
Proof. exact (eq_refl (term18 m n)). Qed.
Lemma lem937895 : term21.
Proof. exact (EQ_MP (@lem514761) (@lem515543)). Qed.
Lemma lem937896 : term22.
Proof. exact (proj2 (@lem937895)). Qed.
Lemma lem938053 (m : nat) (n : nat) : (term19 m n) = (term20 m n).
Proof. exact (EQ_MP (@lem937893 m n) (@lem937892 m n)). Qed.
Lemma lem938054 : term23 = term24.
Proof. exact (@lem938053 0 term25). Qed.
Lemma lem938056 (n : nat) : (term13 n) = (term14 n).
Proof. exact (EQ_MP (@lem937877 n) (@lem937876 n)). Qed.
Lemma lem938057 : term26 = term27.
Proof. exact (@lem938056 (BIT1 0)). Qed.
Lemma lem938059 (n : nat) : (term10 n) = 0.
Proof. exact (EQ_MP (@lem937859 n) (@lem937858 n)). Qed.
Lemma lem938060 : term28 = 0.
Proof. exact (@lem938059 0). Qed.
Lemma lem938061 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem938062 : term29 = (Nat.mul 0).
Proof. exact (MK_COMB (@lem938061) (@lem938060)). Qed.
Lemma lem938064 (n : nat) : (term10 n) = 0.
Proof. exact (EQ_MP (@lem937859 n) (@lem937858 n)). Qed.
Lemma lem938065 : term28 = 0.
Proof. exact (@lem938064 0). Qed.
Lemma lem938066 : term27 = (Nat.mul 0 0).
Proof. exact (MK_COMB (@lem938062) (@lem938065)). Qed.
Lemma lem938068 : (Nat.mul 0 0) = 0.
Proof. exact (proj1 (@lem937896)). Qed.
Lemma lem938069 : term27 = 0.
Proof. exact (TRANS (@lem938066) (@lem938068)). Qed.
Lemma lem938070 : term26 = 0.
Proof. exact (TRANS (@lem938057) (@lem938069)). Qed.
Lemma lem938071 : NUMERAL = NUMERAL.
Proof. exact (eq_refl NUMERAL). Qed.
Lemma lem938072 : term24 = (NUMERAL 0).
Proof. exact (MK_COMB (@lem938071) (@lem938070)). Qed.
Lemma lem938073 : term23 = (NUMERAL 0).
Proof. exact (TRANS (@lem938054) (@lem938072)). Qed.
Lemma lem938085 (p : Prop) : p = (term30 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem938086 : (term31 = 0) = term32.
Proof. exact (@lem938085 (term31 = 0)). Qed.
Lemma lem938087 : term32 = (term31 = 0).
Proof. exact (SYM (@lem938086)). Qed.
Lemma lem938088 (h1 : term33) : term33.
Proof. exact (h1). Qed.
Lemma lem938091 (h1 : term34) : term34.
Proof. exact (h1). Qed.
Lemma lem938092 : term35.
Proof. exact (fun h0 : term34 => @lem938091 h0). Qed.
Lemma lem938093 (h1 : term35) : term35.
Proof. exact (h1). Qed.
Lemma lem938094 (h1 : term34) : term34.
Proof. exact (h1). Qed.
Lemma lem938095 (h1 : term34) (h2 : term35) : term34.
Proof. exact (@lem938093 h2 (@lem938094 h1)). Qed.
Lemma lem938096 (h1 : term34) : term36.
Proof. exact (fun h0 : term35 => @lem938095 h1 h0). Qed.
Lemma lem938097 (h1 : term35) : term35.
Proof. exact (h1). Qed.
Lemma lem938098 (h1 : term34) (h2 : term35) : term34.
Proof. exact (@lem938096 h1 (@lem938097 h2)). Qed.
Lemma lem938099 (h1 : term35) : term35.
Proof. exact (fun h0 : term34 => @lem938098 h0 h1). Qed.
Lemma lem938100 : term37.
Proof. exact (fun h0 : term35 => @lem938099 h0). Qed.
Lemma lem938103 : term35.
Proof. exact (@lem938100 (@lem938092)). Qed.
Lemma lem938109 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem938110 : term38 = term39.
Proof. exact (@lem938109 term40). Qed.
Lemma lem938115 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem938116 : term42 = term43.
Proof. exact (MK_COMB (@lem938115) (@lem938110)). Qed.
Lemma lem938119 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem938126 : term34 = term45.
Proof. exact (MK_COMB (@lem938119) (@lem938116)). Qed.
Lemma lem938127 (n : nat) : ((NUMERAL n) = n) = ((NUMERAL n) = n).
Proof. exact (eq_refl ((NUMERAL n) = n)). Qed.
Lemma lem938128 : term46 = term46.
Proof. exact (fun_ext (fun n : nat => @lem938127 n)). Qed.
Lemma lem938129 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem938130 : term40 = term40.
Proof. exact (MK_COMB (@lem938129) (@lem938128)). Qed.
Lemma lem938131 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem938132 : term39 = term39.
Proof. exact (MK_COMB (@lem938131) (@lem938130)). Qed.
Lemma lem938135 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem938136 : term43 = term43.
Proof. exact (MK_COMB (@lem938135) (@lem938132)). Qed.
Lemma lem938141 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem938142 : term45 = term45.
Proof. exact (MK_COMB (@lem938141) (@lem938136)). Qed.
Lemma lem938155 : term34 = term45.
Proof. exact (TRANS (@lem938126) (@lem938142)). Qed.
Lemma lem938156 : term45 = term34.
Proof. exact (SYM (@lem938155)). Qed.
Lemma lem938159 (h1 : term40) : term40.
Proof. exact (h1). Qed.
Lemma lem938165 (h1 : term33) : term33.
Proof. exact (h1). Qed.
Lemma lem938171 (h1 : term23 = (NUMERAL 0)) : term23 = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem938172 (n : nat) : ((NUMERAL n) = n) = ((NUMERAL n) = n).
Proof. exact (eq_refl ((NUMERAL n) = n)). Qed.
Lemma lem938173 : term46 = term46.
Proof. exact (fun_ext (fun n : nat => @lem938172 n)). Qed.
Lemma lem938174 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem938183 : term40 = term40.
Proof. exact (MK_COMB (@lem938174) (@lem938173)). Qed.
Lemma lem938184 (h1 : term40) : term40.
Proof. exact (EQ_MP (@lem938183) (@lem938159 h1)). Qed.
Lemma lem938202 (h1 : term33) : term33.
Proof. exact (h1). Qed.
Lemma lem938222 (h1 : term23 = (NUMERAL 0)) : term23 = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem938229 (n : nat) : ((NUMERAL n) = n) = ((NUMERAL n) = n).
Proof. exact (eq_refl ((NUMERAL n) = n)). Qed.
Lemma lem938230 : term46 = term46.
Proof. exact (fun_ext (fun n : nat => @lem938229 n)). Qed.
Lemma lem938231 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem938232 : term40 = term40.
Proof. exact (MK_COMB (@lem938231) (@lem938230)). Qed.
Lemma lem938233 (h1 : term40) : term40.
Proof. exact (EQ_MP (@lem938232) (@lem938184 h1)). Qed.
Lemma lem938237 (h1 : term33) : term33.
Proof. exact (h1). Qed.
Lemma lem938241 (h1 : term23 = (NUMERAL 0)) : term23 = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem938243 (n : nat) : ((NUMERAL n) = n) = ((NUMERAL n) = n).
Proof. exact (eq_refl ((NUMERAL n) = n)). Qed.
Lemma lem938244 : term46 = term46.
Proof. exact (fun_ext (fun n : nat => @lem938243 n)). Qed.
Lemma lem938245 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem938247 : term40 = term40.
Proof. exact (MK_COMB (@lem938245) (@lem938244)). Qed.
Lemma lem938248 (h1 : term40) : term40.
Proof. exact (EQ_MP (@lem938247) (@lem938233 h1)). Qed.
Lemma lem938249 (_15918 : nat) (h1 : term40) : term47 _15918.
Proof. exact (@lem938248 h1 _15918). Qed.
Lemma lem938250 (_15918 : nat) : (term47 _15918) = ((NUMERAL _15918) = _15918).
Proof. exact (eq_refl (term47 _15918)). Qed.
Lemma lem938253 (h1 : term33) : term33.
Proof. exact (h1). Qed.
Lemma lem938255 (h1 : term23 = (NUMERAL 0)) : term23 = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem938282 : Nat.pow = Nat.pow.
Proof. exact (eq_refl Nat.pow). Qed.
Lemma lem938283 (_15925 : nat) (_15927 : nat) (h1 : _15925 = _15927) : _15925 = _15927.
Proof. exact (h1). Qed.
Lemma lem938284 (_15926 : nat) (_15928 : nat) (h1 : _15926 = _15928) : _15926 = _15928.
Proof. exact (h1). Qed.
Lemma lem938285 (_15925 : nat) (_15927 : nat) (h1 : _15925 = _15927) : (Nat.pow _15925) = (Nat.pow _15927).
Proof. exact (MK_COMB (@lem938282) (@lem938283 _15925 _15927 h1)). Qed.
Lemma lem938286 (_15925 : nat) (_15927 : nat) (_15926 : nat) (_15928 : nat) (h1 : _15925 = _15927) (h2 : _15926 = _15928) : (Nat.pow _15925 _15926) = (Nat.pow _15927 _15928).
Proof. exact (MK_COMB (@lem938285 _15925 _15927 h1) (@lem938284 _15926 _15928 h2)). Qed.
Lemma lem938287 (_15926 : nat) (_15928 : nat) (_15925 : nat) (_15927 : nat) (h1 : _15925 = _15927) : term48 _15925 _15926 _15927 _15928.
Proof. exact (fun h0 : _15926 = _15928 => @lem938286 _15925 _15927 _15926 _15928 h1 h0). Qed.
Lemma lem938289 (a : Prop) (b : Prop) : (a -> b) = (term49 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem938290 (_15925 : nat) (_15926 : nat) (_15927 : nat) (_15928 : nat) : (term48 _15925 _15926 _15927 _15928) = (term50 _15925 _15926 _15927 _15928).
Proof. exact (@lem938289 (_15926 = _15928) ((Nat.pow _15925 _15926) = (Nat.pow _15927 _15928))). Qed.
Lemma lem938291 (_15926 : nat) (_15928 : nat) (_15925 : nat) (_15927 : nat) (h1 : _15925 = _15927) : term50 _15925 _15926 _15927 _15928.
Proof. exact (EQ_MP (@lem938290 _15925 _15926 _15927 _15928) (@lem938287 _15926 _15928 _15925 _15927 h1)). Qed.
Lemma lem938292 (_15925 : nat) (_15926 : nat) (_15927 : nat) (_15928 : nat) : term51 _15925 _15926 _15927 _15928.
Proof. exact (fun h0 : _15925 = _15927 => @lem938291 _15926 _15928 _15925 _15927 h0). Qed.
Lemma lem938294 (a : Prop) (b : Prop) : (a -> b) = (term49 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem938295 (_15925 : nat) (_15926 : nat) (_15927 : nat) (_15928 : nat) : (term51 _15925 _15926 _15927 _15928) = (term52 _15925 _15926 _15927 _15928).
Proof. exact (@lem938294 (_15925 = _15927) (term50 _15925 _15926 _15927 _15928)). Qed.
Lemma lem938296 (_15925 : nat) (_15926 : nat) (_15927 : nat) (_15928 : nat) : term52 _15925 _15926 _15927 _15928.
Proof. exact (EQ_MP (@lem938295 _15925 _15926 _15927 _15928) (@lem938292 _15925 _15926 _15927 _15928)). Qed.
Lemma lem938298 (x : nat) (y : nat) (z : nat) : term53 x y z.
Proof. exact (@lem21385 nat x y z). Qed.
Lemma lem938300 (h1 : term23 = (NUMERAL 0)) : term23 = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem938301 (h1 : term23 = (NUMERAL 0)) : term54.
Proof. exact (fun h0 : term55 => @lem938300 h1). Qed.
Lemma lem938303 (p : Prop) : (term56 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem938304 : term54 = (term23 = (NUMERAL 0)).
Proof. exact (@lem938303 (term23 = (NUMERAL 0))). Qed.
Lemma lem938305 (h1 : term23 = (NUMERAL 0)) : term23 = (NUMERAL 0).
Proof. exact (EQ_MP (@lem938304) (@lem938301 h1)). Qed.
Lemma lem938307 (_15918 : nat) (h1 : term40) : (NUMERAL _15918) = _15918.
Proof. exact (EQ_MP (@lem938250 _15918) (@lem938249 _15918 h1)). Qed.
Lemma lem938308 (h1 : term40) : (NUMERAL 0) = 0.
Proof. exact (@lem938307 0 h1). Qed.
Lemma lem938309 (h1 : term40) : term57.
Proof. exact (fun h0 : term58 => @lem938308 h1). Qed.
Lemma lem938311 (p : Prop) : (term56 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem938312 : term57 = ((NUMERAL 0) = 0).
Proof. exact (@lem938311 ((NUMERAL 0) = 0)). Qed.
Lemma lem938313 (h1 : term40) : (NUMERAL 0) = 0.
Proof. exact (EQ_MP (@lem938312) (@lem938309 h1)). Qed.
Lemma lem938315 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem938316 : term59 = term59.
Proof. exact (@lem938315 term59). Qed.
Lemma lem938317 : term60.
Proof. exact (fun h0 : term61 => @lem938316). Qed.
Lemma lem938319 (p : Prop) : (term56 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem938320 : term60 = (term59 = term59).
Proof. exact (@lem938319 (term59 = term59)). Qed.
Lemma lem938321 : term59 = term59.
Proof. exact (EQ_MP (@lem938320) (@lem938317)). Qed.
Lemma lem938339 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem938340 (_15925 : nat) (_15927 : nat) (_15926 : nat) (_15928 : nat) : (term50 _15925 _15926 _15927 _15928) = (term62 _15925 _15927 _15926 _15928).
Proof. exact (@lem938339 ((Nat.pow _15925 _15926) = (Nat.pow _15927 _15928)) (term63 _15926 _15928)). Qed.
Lemma lem938350 (_15925 : nat) (_15927 : nat) : (term64 _15925 _15927) = (term64 _15925 _15927).
Proof. exact (eq_refl (term64 _15925 _15927)). Qed.
Lemma lem938351 (_15925 : nat) (_15927 : nat) (_15926 : nat) (_15928 : nat) : (term52 _15925 _15926 _15927 _15928) = (term65 _15925 _15927 _15926 _15928).
Proof. exact (MK_COMB (@lem938350 _15925 _15927) (@lem938340 _15925 _15927 _15926 _15928)). Qed.
Lemma lem938355 (q : Prop) (p : Prop) (r : Prop) : (term66 p q r) = (term66 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem938356 (_15925 : nat) (_15927 : nat) (_15926 : nat) (_15928 : nat) : (term65 _15925 _15927 _15926 _15928) = (term67 _15925 _15927 _15926 _15928).
Proof. exact (@lem938355 ((Nat.pow _15925 _15926) = (Nat.pow _15927 _15928)) (term63 _15925 _15927) (term63 _15926 _15928)). Qed.
Lemma lem938378 (_15925 : nat) (_15927 : nat) (_15926 : nat) (_15928 : nat) : (term52 _15925 _15926 _15927 _15928) = (term67 _15925 _15927 _15926 _15928).
Proof. exact (TRANS (@lem938351 _15925 _15927 _15926 _15928) (@lem938356 _15925 _15927 _15926 _15928)). Qed.
Lemma lem938379 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem938380 (_15925 : nat) (_15927 : nat) (_15926 : nat) (_15928 : nat) : (term68 _15925 _15926 _15927 _15928) = (term69 _15925 _15927 _15926 _15928).
Proof. exact (MK_COMB (@lem938379) (@lem938378 _15925 _15927 _15926 _15928)). Qed.
Lemma lem938402 (_15925 : nat) (_15927 : nat) (_15926 : nat) (_15928 : nat) : (term67 _15925 _15927 _15926 _15928) = (term67 _15925 _15927 _15926 _15928).
Proof. exact (eq_refl (term67 _15925 _15927 _15926 _15928)). Qed.
Lemma lem938403 (_15925 : nat) (_15927 : nat) (_15926 : nat) (_15928 : nat) : ((term52 _15925 _15926 _15927 _15928) = (term67 _15925 _15927 _15926 _15928)) = ((term67 _15925 _15927 _15926 _15928) = (term67 _15925 _15927 _15926 _15928)).
Proof. exact (MK_COMB (@lem938380 _15925 _15927 _15926 _15928) (@lem938402 _15925 _15927 _15926 _15928)). Qed.
Lemma lem938405 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem938406 (x : Prop) : (x = x) = True.
Proof. exact (@lem938405 Prop x). Qed.
Lemma lem938407 (_15925 : nat) (_15927 : nat) (_15926 : nat) (_15928 : nat) : ((term67 _15925 _15927 _15926 _15928) = (term67 _15925 _15927 _15926 _15928)) = True.
Proof. exact (@lem938406 (term67 _15925 _15927 _15926 _15928)). Qed.
Lemma lem938408 (_15925 : nat) (_15927 : nat) (_15926 : nat) (_15928 : nat) : ((term52 _15925 _15926 _15927 _15928) = (term67 _15925 _15927 _15926 _15928)) = True.
Proof. exact (TRANS (@lem938403 _15925 _15927 _15926 _15928) (@lem938407 _15925 _15927 _15926 _15928)). Qed.
Lemma lem938409 (_15925 : nat) (_15927 : nat) (_15926 : nat) (_15928 : nat) : True = ((term52 _15925 _15926 _15927 _15928) = (term67 _15925 _15927 _15926 _15928)).
Proof. exact (SYM (@lem938408 _15925 _15927 _15926 _15928)). Qed.
Lemma lem938410 (_15925 : nat) (_15927 : nat) (_15926 : nat) (_15928 : nat) : (term52 _15925 _15926 _15927 _15928) = (term67 _15925 _15927 _15926 _15928).
Proof. exact (EQ_MP (@lem938409 _15925 _15927 _15926 _15928) (@lem0)). Qed.
Lemma lem938411 (_15925 : nat) (_15927 : nat) (_15926 : nat) (_15928 : nat) : term67 _15925 _15927 _15926 _15928.
Proof. exact (EQ_MP (@lem938410 _15925 _15927 _15926 _15928) (@lem938296 _15925 _15926 _15927 _15928)). Qed.
Lemma lem938413 (b : Prop) (a : Prop) : (a \/ b) = (term70 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem938414 (_15925 : nat) (_15926 : nat) (_15927 : nat) (_15928 : nat) : (term67 _15925 _15927 _15926 _15928) = (term71 _15925 _15926 _15927 _15928).
Proof. exact (@lem938413 (term72 _15925 _15927 _15926 _15928) ((Nat.pow _15925 _15926) = (Nat.pow _15927 _15928))). Qed.
Lemma lem938416 (a : Prop) (b : Prop) : (term73 a b) = (term74 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem938417 (_15925 : nat) (_15927 : nat) (_15926 : nat) (_15928 : nat) : (term75 _15925 _15927 _15926 _15928) = (term76 _15925 _15927 _15926 _15928).
Proof. exact (@lem938416 (term63 _15925 _15927) (term63 _15926 _15928)). Qed.
Lemma lem938419 (a : Prop) : (term77 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem938420 (_15925 : nat) (_15927 : nat) : (term78 _15925 _15927) = (_15925 = _15927).
Proof. exact (@lem938419 (_15925 = _15927)). Qed.
Lemma lem938421 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem938422 (_15925 : nat) (_15927 : nat) : (term79 _15925 _15927) = (term80 _15925 _15927).
Proof. exact (MK_COMB (@lem938421) (@lem938420 _15925 _15927)). Qed.
Lemma lem938424 (a : Prop) : (term77 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem938425 (_15926 : nat) (_15928 : nat) : (term78 _15926 _15928) = (_15926 = _15928).
Proof. exact (@lem938424 (_15926 = _15928)). Qed.
Lemma lem938426 (_15925 : nat) (_15927 : nat) (_15926 : nat) (_15928 : nat) : (term76 _15925 _15927 _15926 _15928) = (term81 _15925 _15927 _15926 _15928).
Proof. exact (MK_COMB (@lem938422 _15925 _15927) (@lem938425 _15926 _15928)). Qed.
Lemma lem938427 (_15925 : nat) (_15927 : nat) (_15926 : nat) (_15928 : nat) : (term75 _15925 _15927 _15926 _15928) = (term81 _15925 _15927 _15926 _15928).
Proof. exact (TRANS (@lem938417 _15925 _15927 _15926 _15928) (@lem938426 _15925 _15927 _15926 _15928)). Qed.
Lemma lem938428 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem938429 (_15925 : nat) (_15927 : nat) (_15926 : nat) (_15928 : nat) : (term82 _15925 _15927 _15926 _15928) = (term83 _15925 _15927 _15926 _15928).
Proof. exact (MK_COMB (@lem938428) (@lem938427 _15925 _15927 _15926 _15928)). Qed.
Lemma lem938430 (_15925 : nat) (_15926 : nat) (_15927 : nat) (_15928 : nat) : ((Nat.pow _15925 _15926) = (Nat.pow _15927 _15928)) = ((Nat.pow _15925 _15926) = (Nat.pow _15927 _15928)).
Proof. exact (eq_refl ((Nat.pow _15925 _15926) = (Nat.pow _15927 _15928))). Qed.
Lemma lem938431 (_15925 : nat) (_15926 : nat) (_15927 : nat) (_15928 : nat) : (term71 _15925 _15926 _15927 _15928) = (term84 _15925 _15926 _15927 _15928).
Proof. exact (MK_COMB (@lem938429 _15925 _15927 _15926 _15928) (@lem938430 _15925 _15926 _15927 _15928)). Qed.
Lemma lem938432 (_15925 : nat) (_15926 : nat) (_15927 : nat) (_15928 : nat) : (term67 _15925 _15927 _15926 _15928) = (term84 _15925 _15926 _15927 _15928).
Proof. exact (TRANS (@lem938414 _15925 _15926 _15927 _15928) (@lem938431 _15925 _15926 _15927 _15928)). Qed.
Lemma lem938434 (h1 : term40) : term85.
Proof. exact (conj (@lem938313 h1) (@lem938321)). Qed.
Lemma lem938436 (_15925 : nat) (_15926 : nat) (_15927 : nat) (_15928 : nat) : term84 _15925 _15926 _15927 _15928.
Proof. exact (EQ_MP (@lem938432 _15925 _15926 _15927 _15928) (@lem938411 _15925 _15927 _15926 _15928)). Qed.
Lemma lem938437 : term86.
Proof. exact (@lem938436 (NUMERAL 0) term59 0 term59). Qed.
Lemma lem938440 (h1 : term40) : term23 = term31.
Proof. exact (@lem938437 (@lem938434 h1)). Qed.
Lemma lem938441 (h1 : term40) : term87.
Proof. exact (fun h0 : term88 => @lem938440 h1). Qed.
Lemma lem938443 (p : Prop) : (term56 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem938444 : term87 = (term23 = term31).
Proof. exact (@lem938443 (term23 = term31)). Qed.
Lemma lem938445 (h1 : term40) : term23 = term31.
Proof. exact (EQ_MP (@lem938444) (@lem938441 h1)). Qed.
Lemma lem938463 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem938464 (y : nat) (x : nat) (z : nat) : (term89 x y z) = (term90 y x z).
Proof. exact (@lem938463 (y = z) (term63 x z)). Qed.
Lemma lem938474 (x : nat) (y : nat) : (term64 x y) = (term64 x y).
Proof. exact (eq_refl (term64 x y)). Qed.
Lemma lem938475 (y : nat) (x : nat) (z : nat) : (term53 x y z) = (term91 y x z).
Proof. exact (MK_COMB (@lem938474 x y) (@lem938464 y x z)). Qed.
Lemma lem938479 (q : Prop) (p : Prop) (r : Prop) : (term66 p q r) = (term66 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem938480 (y : nat) (x : nat) (z : nat) : (term91 y x z) = (term92 y x z).
Proof. exact (@lem938479 (y = z) (term63 x y) (term63 x z)). Qed.
Lemma lem938502 (y : nat) (x : nat) (z : nat) : (term53 x y z) = (term92 y x z).
Proof. exact (TRANS (@lem938475 y x z) (@lem938480 y x z)). Qed.
Lemma lem938503 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem938504 (y : nat) (x : nat) (z : nat) : (term93 x y z) = (term94 y x z).
Proof. exact (MK_COMB (@lem938503) (@lem938502 y x z)). Qed.
Lemma lem938526 (y : nat) (x : nat) (z : nat) : (term92 y x z) = (term92 y x z).
Proof. exact (eq_refl (term92 y x z)). Qed.
Lemma lem938527 (y : nat) (x : nat) (z : nat) : ((term53 x y z) = (term92 y x z)) = ((term92 y x z) = (term92 y x z)).
Proof. exact (MK_COMB (@lem938504 y x z) (@lem938526 y x z)). Qed.
Lemma lem938529 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem938530 (x : Prop) : (x = x) = True.
Proof. exact (@lem938529 Prop x). Qed.
Lemma lem938531 (y : nat) (x : nat) (z : nat) : ((term92 y x z) = (term92 y x z)) = True.
Proof. exact (@lem938530 (term92 y x z)). Qed.
Lemma lem938532 (y : nat) (x : nat) (z : nat) : ((term53 x y z) = (term92 y x z)) = True.
Proof. exact (TRANS (@lem938527 y x z) (@lem938531 y x z)). Qed.
Lemma lem938533 (y : nat) (x : nat) (z : nat) : True = ((term53 x y z) = (term92 y x z)).
Proof. exact (SYM (@lem938532 y x z)). Qed.
Lemma lem938534 (y : nat) (x : nat) (z : nat) : (term53 x y z) = (term92 y x z).
Proof. exact (EQ_MP (@lem938533 y x z) (@lem0)). Qed.
Lemma lem938535 (y : nat) (x : nat) (z : nat) : term92 y x z.
Proof. exact (EQ_MP (@lem938534 y x z) (@lem938298 x y z)). Qed.
Lemma lem938537 (b : Prop) (a : Prop) : (a \/ b) = (term70 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem938538 (x : nat) (y : nat) (z : nat) : (term92 y x z) = (term95 x y z).
Proof. exact (@lem938537 (term96 y x z) (y = z)). Qed.
Lemma lem938540 (a : Prop) (b : Prop) : (term73 a b) = (term74 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem938541 (y : nat) (x : nat) (z : nat) : (term97 y x z) = (term98 y x z).
Proof. exact (@lem938540 (term63 x y) (term63 x z)). Qed.
Lemma lem938543 (a : Prop) : (term77 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem938544 (x : nat) (y : nat) : (term78 x y) = (x = y).
Proof. exact (@lem938543 (x = y)). Qed.
Lemma lem938545 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem938546 (x : nat) (y : nat) : (term79 x y) = (term80 x y).
Proof. exact (MK_COMB (@lem938545) (@lem938544 x y)). Qed.
Lemma lem938548 (a : Prop) : (term77 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem938549 (x : nat) (z : nat) : (term78 x z) = (x = z).
Proof. exact (@lem938548 (x = z)). Qed.
Lemma lem938550 (y : nat) (x : nat) (z : nat) : (term98 y x z) = (term99 y x z).
Proof. exact (MK_COMB (@lem938546 x y) (@lem938549 x z)). Qed.
Lemma lem938551 (y : nat) (x : nat) (z : nat) : (term97 y x z) = (term99 y x z).
Proof. exact (TRANS (@lem938541 y x z) (@lem938550 y x z)). Qed.
Lemma lem938552 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem938553 (y : nat) (x : nat) (z : nat) : (term100 y x z) = (term101 y x z).
Proof. exact (MK_COMB (@lem938552) (@lem938551 y x z)). Qed.
Lemma lem938554 (y : nat) (z : nat) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem938555 (x : nat) (y : nat) (z : nat) : (term95 x y z) = (term102 x y z).
Proof. exact (MK_COMB (@lem938553 y x z) (@lem938554 y z)). Qed.
Lemma lem938556 (x : nat) (y : nat) (z : nat) : (term92 y x z) = (term102 x y z).
Proof. exact (TRANS (@lem938538 x y z) (@lem938555 x y z)). Qed.
Lemma lem938558 (h1 : term40) (h2 : term23 = (NUMERAL 0)) : term103.
Proof. exact (conj (@lem938305 h2) (@lem938445 h1)). Qed.
Lemma lem938560 (x : nat) (y : nat) (z : nat) : term102 x y z.
Proof. exact (EQ_MP (@lem938556 x y z) (@lem938535 y x z)). Qed.
Lemma lem938561 : term104.
Proof. exact (@lem938560 term23 (NUMERAL 0) term31). Qed.
Lemma lem938564 (h1 : term40) (h2 : term23 = (NUMERAL 0)) : (NUMERAL 0) = term31.
Proof. exact (@lem938561 (@lem938558 h1 h2)). Qed.
Lemma lem938565 (h1 : term40) (h2 : term23 = (NUMERAL 0)) : term105.
Proof. exact (fun h0 : term106 => @lem938564 h1 h2). Qed.
Lemma lem938567 (p : Prop) : (term56 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem938568 : term105 = ((NUMERAL 0) = term31).
Proof. exact (@lem938567 ((NUMERAL 0) = term31)). Qed.
Lemma lem938569 (h1 : term40) (h2 : term23 = (NUMERAL 0)) : (NUMERAL 0) = term31.
Proof. exact (EQ_MP (@lem938568) (@lem938565 h1 h2)). Qed.
Lemma lem938571 (_15918 : nat) (h1 : term40) : (NUMERAL _15918) = _15918.
Proof. exact (EQ_MP (@lem938250 _15918) (@lem938249 _15918 h1)). Qed.
Lemma lem938572 (h1 : term40) : (NUMERAL 0) = 0.
Proof. exact (@lem938571 0 h1). Qed.
Lemma lem938573 (h1 : term40) : term57.
Proof. exact (fun h0 : term58 => @lem938572 h1). Qed.
Lemma lem938575 (p : Prop) : (term56 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem938576 : term57 = ((NUMERAL 0) = 0).
Proof. exact (@lem938575 ((NUMERAL 0) = 0)). Qed.
Lemma lem938577 (h1 : term40) : (NUMERAL 0) = 0.
Proof. exact (EQ_MP (@lem938576) (@lem938573 h1)). Qed.
Lemma lem938578 (h1 : term40) (h2 : term23 = (NUMERAL 0)) : term107.
Proof. exact (conj (@lem938569 h1 h2) (@lem938577 h1)). Qed.
Lemma lem938580 (x : nat) (y : nat) (z : nat) : term102 x y z.
Proof. exact (EQ_MP (@lem938556 x y z) (@lem938535 y x z)). Qed.
Lemma lem938581 : term108.
Proof. exact (@lem938580 (NUMERAL 0) term31 0). Qed.
Lemma lem938584 (h1 : term40) (h2 : term23 = (NUMERAL 0)) : term31 = 0.
Proof. exact (@lem938581 (@lem938578 h1 h2)). Qed.
Lemma lem938585 (h1 : term40) (h2 : term23 = (NUMERAL 0)) : term109.
Proof. exact (fun h0 : term33 => @lem938584 h1 h2). Qed.
Lemma lem938587 (p : Prop) : (term56 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem938588 : term109 = (term31 = 0).
Proof. exact (@lem938587 (term31 = 0)). Qed.
Lemma lem938589 (h1 : term40) (h2 : term23 = (NUMERAL 0)) : term31 = 0.
Proof. exact (EQ_MP (@lem938588) (@lem938585 h1 h2)). Qed.
Lemma lem938592 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem938594 : term33 = term110.
Proof. exact (@lem938592 (term31 = 0)). Qed.
Lemma lem938597 (h1 : term33) : term110.
Proof. exact (EQ_MP (@lem938594) (@lem938253 h1)). Qed.
Lemma lem938600 (h1 : term40) (h2 : term33) (h3 : term23 = (NUMERAL 0)) : False.
Proof. exact (@lem938597 h2 (@lem938589 h1 h3)). Qed.
Lemma lem938601 (h1 : term40) (h2 : term33) (h3 : term23 = (NUMERAL 0)) : term111.
Proof. exact (fun h0 : ~ False => @lem938600 h1 h2 h3). Qed.
Lemma lem938603 (p : Prop) : (term56 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem938604 : term111 = False.
Proof. exact (@lem938603 False). Qed.
Lemma lem938605 (h1 : term40) (h2 : term33) (h3 : term23 = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem938604) (@lem938601 h1 h2 h3)). Qed.
Lemma lem938606 (h1 : term40) (h2 : term33) (h3 : term23 = (NUMERAL 0)) : (term23 = (NUMERAL 0)) = False.
Proof. exact (prop_ext (fun h4 : term23 = (NUMERAL 0) => @lem938605 h1 h2 h3) (fun h4 : False => @lem938255 h3)). Qed.
Lemma lem938607 (h1 : term40) (h2 : term33) (h3 : term23 = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem938606 h1 h2 h3) (@lem938255 h3)). Qed.
Lemma lem938608 (h1 : term40) (h2 : term33) (h3 : term23 = (NUMERAL 0)) : term33 = False.
Proof. exact (prop_ext (fun h4 : term33 => @lem938607 h1 h2 h3) (fun h4 : False => @lem938253 h2)). Qed.
Lemma lem938609 (h1 : term40) (h2 : term33) (h3 : term23 = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem938608 h1 h2 h3) (@lem938253 h2)). Qed.
Lemma lem938610 (h1 : term40) (h2 : term33) (h3 : term23 = (NUMERAL 0)) : (term23 = (NUMERAL 0)) = False.
Proof. exact (prop_ext (fun h4 : term23 = (NUMERAL 0) => @lem938609 h1 h2 h3) (fun h4 : False => @lem938241 h3)). Qed.
Lemma lem938611 (h1 : term40) (h2 : term33) (h3 : term23 = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem938610 h1 h2 h3) (@lem938241 h3)). Qed.
Lemma lem938612 (h1 : term40) (h2 : term33) (h3 : term23 = (NUMERAL 0)) : term33 = False.
Proof. exact (prop_ext (fun h4 : term33 => @lem938611 h1 h2 h3) (fun h4 : False => @lem938237 h2)). Qed.
Lemma lem938613 (h1 : term40) (h2 : term33) (h3 : term23 = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem938612 h1 h2 h3) (@lem938237 h2)). Qed.
Lemma lem938614 (h1 : term40) (h2 : term33) (h3 : term23 = (NUMERAL 0)) : term40 = False.
Proof. exact (prop_ext (fun h4 : term40 => @lem938613 h1 h2 h3) (fun h4 : False => @lem938248 h1)). Qed.
Lemma lem938615 (h1 : term40) (h2 : term33) (h3 : term23 = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem938614 h1 h2 h3) (@lem938248 h1)). Qed.
Lemma lem938616 (h1 : term40) (h2 : term33) (h3 : term23 = (NUMERAL 0)) : (term23 = (NUMERAL 0)) = False.
Proof. exact (prop_ext (fun h4 : term23 = (NUMERAL 0) => @lem938615 h1 h2 h3) (fun h4 : False => @lem938241 h3)). Qed.
Lemma lem938617 (h1 : term40) (h2 : term33) (h3 : term23 = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem938616 h1 h2 h3) (@lem938241 h3)). Qed.
Lemma lem938618 (h1 : term40) (h2 : term33) (h3 : term23 = (NUMERAL 0)) : term33 = False.
Proof. exact (prop_ext (fun h4 : term33 => @lem938617 h1 h2 h3) (fun h4 : False => @lem938237 h2)). Qed.
Lemma lem938619 (h1 : term40) (h2 : term33) (h3 : term23 = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem938618 h1 h2 h3) (@lem938237 h2)). Qed.
Lemma lem938620 (h1 : term40) (h2 : term33) (h3 : term23 = (NUMERAL 0)) : term40 = False.
Proof. exact (prop_ext (fun h4 : term40 => @lem938619 h1 h2 h3) (fun h4 : False => @lem938233 h1)). Qed.
Lemma lem938621 (h1 : term40) (h2 : term33) (h3 : term23 = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem938620 h1 h2 h3) (@lem938233 h1)). Qed.
Lemma lem938622 (h1 : term40) (h2 : term33) (h3 : term23 = (NUMERAL 0)) : (term23 = (NUMERAL 0)) = False.
Proof. exact (prop_ext (fun h4 : term23 = (NUMERAL 0) => @lem938621 h1 h2 h3) (fun h4 : False => @lem938222 h3)). Qed.
Lemma lem938623 (h1 : term40) (h2 : term33) (h3 : term23 = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem938622 h1 h2 h3) (@lem938222 h3)). Qed.
Lemma lem938624 (h1 : term40) (h2 : term33) (h3 : term23 = (NUMERAL 0)) : term33 = False.
Proof. exact (prop_ext (fun h4 : term33 => @lem938623 h1 h2 h3) (fun h4 : False => @lem938202 h2)). Qed.
Lemma lem938625 (h1 : term40) (h2 : term33) (h3 : term23 = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem938624 h1 h2 h3) (@lem938202 h2)). Qed.
Lemma lem938626 (h1 : term40) (h2 : term33) (h3 : term23 = (NUMERAL 0)) : term40 = False.
Proof. exact (prop_ext (fun h4 : term40 => @lem938625 h1 h2 h3) (fun h4 : False => @lem938184 h1)). Qed.
Lemma lem938627 (h1 : term40) (h2 : term33) (h3 : term23 = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem938626 h1 h2 h3) (@lem938184 h1)). Qed.
Lemma lem938628 (h1 : term40) (h2 : term33) (h3 : term23 = (NUMERAL 0)) : (term23 = (NUMERAL 0)) = False.
Proof. exact (prop_ext (fun h4 : term23 = (NUMERAL 0) => @lem938627 h1 h2 h3) (fun h4 : False => @lem938171 h3)). Qed.
Lemma lem938629 (h1 : term40) (h2 : term33) (h3 : term23 = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem938628 h1 h2 h3) (@lem938171 h3)). Qed.
Lemma lem938630 (h1 : term40) (h2 : term33) (h3 : term23 = (NUMERAL 0)) : term33 = False.
Proof. exact (prop_ext (fun h4 : term33 => @lem938629 h1 h2 h3) (fun h4 : False => @lem938165 h2)). Qed.
Lemma lem938631 (h1 : term40) (h2 : term33) (h3 : term23 = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem938630 h1 h2 h3) (@lem938165 h2)). Qed.
Lemma lem938632 (h1 : term33) (h2 : term23 = (NUMERAL 0)) : term38.
Proof. exact (fun h0 : term40 => @lem938631 h0 h1 h2). Qed.
Lemma lem938633 : term38 = term39.
Proof. exact (@lem69 term40). Qed.
Lemma lem938634 (h1 : term33) (h2 : term23 = (NUMERAL 0)) : term39.
Proof. exact (EQ_MP (@lem938633) (@lem938632 h1 h2)). Qed.
Lemma lem938635 (h1 : term33) : term43.
Proof. exact (fun h0 : term23 = (NUMERAL 0) => @lem938634 h1 h0). Qed.
Lemma lem938636 : term45.
Proof. exact (fun h0 : term33 => @lem938635 h0). Qed.
Lemma lem938637 : term34.
Proof. exact (EQ_MP (@lem938156) (@lem938636)). Qed.
Lemma lem938639 : term34.
Proof. exact (@lem938103 (@lem938637)). Qed.
Lemma lem938640 (h1 : term33) : term42.
Proof. exact (@lem938639 (@lem938088 h1)). Qed.
Lemma lem938641 (h1 : term33) : term38.
Proof. exact (@lem938640 h1 (@lem938073)). Qed.
Lemma lem938642 (h1 : term33) : False.
Proof. exact (@lem938641 h1 (@lem75543)). Qed.
Lemma lem938643 (h1 : term33) : term33 = False.
Proof. exact (prop_ext (fun h2 : term33 => @lem938642 h1) (fun h2 : False => @lem938088 h1)). Qed.
Lemma lem938644 (h1 : term33) : False.
Proof. exact (EQ_MP (@lem938643 h1) (@lem938088 h1)). Qed.
Lemma lem938645 : term32.
Proof. exact (fun h0 : term33 => @lem938644 h0). Qed.
Lemma lem938648 : term31 = 0.
Proof. exact (EQ_MP (@lem938087) (@lem938645)). Qed.
