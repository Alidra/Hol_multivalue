Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1005477_term_abbrevs.
Require Import ADD_CLAUSES_spec.
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
Require Import thm69_spec.
Require Import thm75543_spec.
Lemma lem1003881 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1003883 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1003884 (m : nat) : ((term1 m) = (term2 m)) = (term3 m).
Proof. exact (@lem1003883 ((term1 m) = (term2 m))). Qed.
Lemma lem1003885 (m : nat) : (term3 m) = ((term1 m) = (term2 m)).
Proof. exact (SYM (@lem1003884 m)). Qed.
Lemma lem1003886 (m : nat) (h1 : term4 m) : term4 m.
Proof. exact (h1). Qed.
Lemma lem1003889 (m : nat) (h1 : term5 m) : term5 m.
Proof. exact (h1). Qed.
Lemma lem1003890 (m : nat) : term6 m.
Proof. exact (fun h0 : term5 m => @lem1003889 m h0). Qed.
Lemma lem1003891 (m : nat) (h1 : term6 m) : term6 m.
Proof. exact (h1). Qed.
Lemma lem1003892 (m : nat) (h1 : term5 m) : term5 m.
Proof. exact (h1). Qed.
Lemma lem1003893 (m : nat) (h1 : term5 m) (h2 : term6 m) : term5 m.
Proof. exact (@lem1003891 m h2 (@lem1003892 m h1)). Qed.
Lemma lem1003894 (m : nat) (h1 : term5 m) : term7 m.
Proof. exact (fun h0 : term6 m => @lem1003893 m h1 h0). Qed.
Lemma lem1003895 (m : nat) (h1 : term6 m) : term6 m.
Proof. exact (h1). Qed.
Lemma lem1003896 (m : nat) (h1 : term5 m) (h2 : term6 m) : term5 m.
Proof. exact (@lem1003894 m h1 (@lem1003895 m h2)). Qed.
Lemma lem1003897 (m : nat) (h1 : term6 m) : term6 m.
Proof. exact (fun h0 : term5 m => @lem1003896 m h0 h1). Qed.
Lemma lem1003898 (m : nat) : term8 m.
Proof. exact (fun h0 : term6 m => @lem1003897 m h0). Qed.
Lemma lem1003901 (m : nat) : term6 m.
Proof. exact (@lem1003898 m (@lem1003890 m)). Qed.
Lemma lem1003941 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1003942 : term9 = term10.
Proof. exact (@lem1003941 term11). Qed.
Lemma lem1003947 : term12 = term12.
Proof. exact (eq_refl term12). Qed.
Lemma lem1003948 : term13 = term14.
Proof. exact (MK_COMB (@lem1003947) (@lem1003942)). Qed.
Lemma lem1003951 (m : nat) : (term15 m) = (term15 m).
Proof. exact (eq_refl (term15 m)). Qed.
Lemma lem1003952 (m : nat) : (term5 m) = (term16 m).
Proof. exact (MK_COMB (@lem1003951 m) (@lem1003948)). Qed.
Lemma lem1003955 : term17 = term18.
Proof. exact (fun_ext (fun m : nat => @lem1003952 m)). Qed.
Lemma lem1003956 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1003965 : term19 = term20.
Proof. exact (MK_COMB (@lem1003956) (@lem1003955)). Qed.
Lemma lem1003966 (n : nat) : ((NUMERAL n) = n) = ((NUMERAL n) = n).
Proof. exact (eq_refl ((NUMERAL n) = n)). Qed.
Lemma lem1003967 : term21 = term21.
Proof. exact (fun_ext (fun n : nat => @lem1003966 n)). Qed.
Lemma lem1003968 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1003969 : term11 = term11.
Proof. exact (MK_COMB (@lem1003968) (@lem1003967)). Qed.
Lemma lem1003970 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1003971 : term10 = term10.
Proof. exact (MK_COMB (@lem1003970) (@lem1003969)). Qed.
Lemma lem1003972 (m : nat) (n : nat) : ((term22 m n) = (term23 m n)) = ((term22 m n) = (term23 m n)).
Proof. exact (eq_refl ((term22 m n) = (term23 m n))). Qed.
Lemma lem1003973 (m : nat) : (term24 m) = (term24 m).
Proof. exact (fun_ext (fun n : nat => @lem1003972 m n)). Qed.
Lemma lem1003974 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1003975 (m : nat) : (term25 m) = (term25 m).
Proof. exact (MK_COMB (@lem1003974) (@lem1003973 m)). Qed.
Lemma lem1003976 : term26 = term26.
Proof. exact (fun_ext (fun m : nat => @lem1003975 m)). Qed.
Lemma lem1003977 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1003978 : term27 = term27.
Proof. exact (MK_COMB (@lem1003977) (@lem1003976)). Qed.
Lemma lem1003979 (m : nat) (n : nat) : ((term28 m n) = (term23 m n)) = ((term28 m n) = (term23 m n)).
Proof. exact (eq_refl ((term28 m n) = (term23 m n))). Qed.
Lemma lem1003980 (m : nat) : (term29 m) = (term29 m).
Proof. exact (fun_ext (fun n : nat => @lem1003979 m n)). Qed.
Lemma lem1003981 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1003982 (m : nat) : (term30 m) = (term30 m).
Proof. exact (MK_COMB (@lem1003981) (@lem1003980 m)). Qed.
Lemma lem1003983 : term31 = term31.
Proof. exact (fun_ext (fun m : nat => @lem1003982 m)). Qed.
Lemma lem1003984 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1003985 : term32 = term32.
Proof. exact (MK_COMB (@lem1003984) (@lem1003983)). Qed.
Lemma lem1003986 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1003987 : term33 = term33.
Proof. exact (MK_COMB (@lem1003986) (@lem1003985)). Qed.
Lemma lem1003988 : term34 = term34.
Proof. exact (MK_COMB (@lem1003987) (@lem1003978)). Qed.
Lemma lem1003989 (m : nat) : ((term35 m) = m) = ((term35 m) = m).
Proof. exact (eq_refl ((term35 m) = m)). Qed.
Lemma lem1003990 : term36 = term36.
Proof. exact (fun_ext (fun m : nat => @lem1003989 m)). Qed.
Lemma lem1003991 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1003992 : term37 = term37.
Proof. exact (MK_COMB (@lem1003991) (@lem1003990)). Qed.
Lemma lem1003993 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1003994 : term38 = term38.
Proof. exact (MK_COMB (@lem1003993) (@lem1003992)). Qed.
Lemma lem1003995 : term39 = term39.
Proof. exact (MK_COMB (@lem1003994) (@lem1003988)). Qed.
Lemma lem1003996 (n : nat) : ((term40 n) = n) = ((term40 n) = n).
Proof. exact (eq_refl ((term40 n) = n)). Qed.
Lemma lem1003997 : term41 = term41.
Proof. exact (fun_ext (fun n : nat => @lem1003996 n)). Qed.
Lemma lem1003998 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1003999 : term42 = term42.
Proof. exact (MK_COMB (@lem1003998) (@lem1003997)). Qed.
Lemma lem1004000 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1004001 : term43 = term43.
Proof. exact (MK_COMB (@lem1004000) (@lem1003999)). Qed.
Lemma lem1004002 : term44 = term44.
Proof. exact (MK_COMB (@lem1004001) (@lem1003995)). Qed.
Lemma lem1004003 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1004004 : term12 = term12.
Proof. exact (MK_COMB (@lem1004003) (@lem1004002)). Qed.
Lemma lem1004005 : term14 = term14.
Proof. exact (MK_COMB (@lem1004004) (@lem1003971)). Qed.
Lemma lem1004010 (m : nat) : (term15 m) = (term15 m).
Proof. exact (eq_refl (term15 m)). Qed.
Lemma lem1004011 (m : nat) : (term16 m) = (term16 m).
Proof. exact (MK_COMB (@lem1004010 m) (@lem1004005)). Qed.
Lemma lem1004012 : term18 = term18.
Proof. exact (fun_ext (fun m : nat => @lem1004011 m)). Qed.
Lemma lem1004013 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1004014 : term20 = term20.
Proof. exact (MK_COMB (@lem1004013) (@lem1004012)). Qed.
Lemma lem1004075 : term19 = term20.
Proof. exact (TRANS (@lem1003965) (@lem1004014)). Qed.
Lemma lem1004076 : term20 = term19.
Proof. exact (SYM (@lem1004075)). Qed.
Lemma lem1004078 (h1 : term44) : term44.
Proof. exact (h1). Qed.
Lemma lem1004079 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem1004085 (m : nat) (h1 : term4 m) : term4 m.
Proof. exact (h1). Qed.
Lemma lem1004086 (n : nat) : ((term40 n) = n) = ((term40 n) = n).
Proof. exact (eq_refl ((term40 n) = n)). Qed.
Lemma lem1004087 : term41 = term41.
Proof. exact (fun_ext (fun n : nat => @lem1004086 n)). Qed.
Lemma lem1004088 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1004089 : term42 = term42.
Proof. exact (MK_COMB (@lem1004088) (@lem1004087)). Qed.
Lemma lem1004090 (m : nat) : ((term35 m) = m) = ((term35 m) = m).
Proof. exact (eq_refl ((term35 m) = m)). Qed.
Lemma lem1004091 : term36 = term36.
Proof. exact (fun_ext (fun m : nat => @lem1004090 m)). Qed.
Lemma lem1004092 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1004093 : term37 = term37.
Proof. exact (MK_COMB (@lem1004092) (@lem1004091)). Qed.
Lemma lem1004094 (m : nat) (n : nat) : ((term28 m n) = (term23 m n)) = ((term28 m n) = (term23 m n)).
Proof. exact (eq_refl ((term28 m n) = (term23 m n))). Qed.
Lemma lem1004095 (m : nat) : (term29 m) = (term29 m).
Proof. exact (fun_ext (fun n : nat => @lem1004094 m n)). Qed.
Lemma lem1004096 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1004097 (m : nat) : (term30 m) = (term30 m).
Proof. exact (MK_COMB (@lem1004096) (@lem1004095 m)). Qed.
Lemma lem1004098 : term31 = term31.
Proof. exact (fun_ext (fun m : nat => @lem1004097 m)). Qed.
Lemma lem1004099 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1004100 : term32 = term32.
Proof. exact (MK_COMB (@lem1004099) (@lem1004098)). Qed.
Lemma lem1004101 (m : nat) (n : nat) : ((term22 m n) = (term23 m n)) = ((term22 m n) = (term23 m n)).
Proof. exact (eq_refl ((term22 m n) = (term23 m n))). Qed.
Lemma lem1004102 (m : nat) : (term24 m) = (term24 m).
Proof. exact (fun_ext (fun n : nat => @lem1004101 m n)). Qed.
Lemma lem1004103 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1004104 (m : nat) : (term25 m) = (term25 m).
Proof. exact (MK_COMB (@lem1004103) (@lem1004102 m)). Qed.
Lemma lem1004105 : term26 = term26.
Proof. exact (fun_ext (fun m : nat => @lem1004104 m)). Qed.
Lemma lem1004106 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1004107 : term27 = term27.
Proof. exact (MK_COMB (@lem1004106) (@lem1004105)). Qed.
Lemma lem1004108 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1004109 : term33 = term33.
Proof. exact (MK_COMB (@lem1004108) (@lem1004100)). Qed.
Lemma lem1004110 : term34 = term34.
Proof. exact (MK_COMB (@lem1004109) (@lem1004107)). Qed.
Lemma lem1004111 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1004112 : term38 = term38.
Proof. exact (MK_COMB (@lem1004111) (@lem1004093)). Qed.
Lemma lem1004113 : term39 = term39.
Proof. exact (MK_COMB (@lem1004112) (@lem1004110)). Qed.
Lemma lem1004114 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1004115 : term43 = term43.
Proof. exact (MK_COMB (@lem1004114) (@lem1004089)). Qed.
Lemma lem1004144 : term44 = term44.
Proof. exact (MK_COMB (@lem1004115) (@lem1004113)). Qed.
Lemma lem1004145 (h1 : term44) : term44.
Proof. exact (EQ_MP (@lem1004144) (@lem1004078 h1)). Qed.
Lemma lem1004146 (n : nat) : ((NUMERAL n) = n) = ((NUMERAL n) = n).
Proof. exact (eq_refl ((NUMERAL n) = n)). Qed.
Lemma lem1004147 : term21 = term21.
Proof. exact (fun_ext (fun n : nat => @lem1004146 n)). Qed.
Lemma lem1004148 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1004157 : term11 = term11.
Proof. exact (MK_COMB (@lem1004148) (@lem1004147)). Qed.
Lemma lem1004158 (h1 : term11) : term11.
Proof. exact (EQ_MP (@lem1004157) (@lem1004079 h1)). Qed.
Lemma lem1004176 (m : nat) (h1 : term4 m) : term4 m.
Proof. exact (h1). Qed.
Lemma lem1004193 (m : nat) (n : nat) : ((term22 m n) = (term23 m n)) = ((term22 m n) = (term23 m n)).
Proof. exact (eq_refl ((term22 m n) = (term23 m n))). Qed.
Lemma lem1004194 (m : nat) : (term24 m) = (term24 m).
Proof. exact (fun_ext (fun n : nat => @lem1004193 m n)). Qed.
Lemma lem1004195 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1004196 (m : nat) : (term25 m) = (term25 m).
Proof. exact (MK_COMB (@lem1004195) (@lem1004194 m)). Qed.
Lemma lem1004197 : term26 = term26.
Proof. exact (fun_ext (fun m : nat => @lem1004196 m)). Qed.
Lemma lem1004198 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1004199 : term27 = term27.
Proof. exact (MK_COMB (@lem1004198) (@lem1004197)). Qed.
Lemma lem1004216 (m : nat) (n : nat) : ((term28 m n) = (term23 m n)) = ((term28 m n) = (term23 m n)).
Proof. exact (eq_refl ((term28 m n) = (term23 m n))). Qed.
Lemma lem1004217 (m : nat) : (term29 m) = (term29 m).
Proof. exact (fun_ext (fun n : nat => @lem1004216 m n)). Qed.
Lemma lem1004218 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1004219 (m : nat) : (term30 m) = (term30 m).
Proof. exact (MK_COMB (@lem1004218) (@lem1004217 m)). Qed.
Lemma lem1004220 : term31 = term31.
Proof. exact (fun_ext (fun m : nat => @lem1004219 m)). Qed.
Lemma lem1004221 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1004222 : term32 = term32.
Proof. exact (MK_COMB (@lem1004221) (@lem1004220)). Qed.
Lemma lem1004223 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1004224 : term33 = term33.
Proof. exact (MK_COMB (@lem1004223) (@lem1004222)). Qed.
Lemma lem1004225 : term34 = term34.
Proof. exact (MK_COMB (@lem1004224) (@lem1004199)). Qed.
Lemma lem1004236 (m : nat) : ((term35 m) = m) = ((term35 m) = m).
Proof. exact (eq_refl ((term35 m) = m)). Qed.
Lemma lem1004237 : term36 = term36.
Proof. exact (fun_ext (fun m : nat => @lem1004236 m)). Qed.
Lemma lem1004238 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1004239 : term37 = term37.
Proof. exact (MK_COMB (@lem1004238) (@lem1004237)). Qed.
Lemma lem1004240 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1004241 : term38 = term38.
Proof. exact (MK_COMB (@lem1004240) (@lem1004239)). Qed.
Lemma lem1004242 : term39 = term39.
Proof. exact (MK_COMB (@lem1004241) (@lem1004225)). Qed.
Lemma lem1004253 (n : nat) : ((term40 n) = n) = ((term40 n) = n).
Proof. exact (eq_refl ((term40 n) = n)). Qed.
Lemma lem1004254 : term41 = term41.
Proof. exact (fun_ext (fun n : nat => @lem1004253 n)). Qed.
Lemma lem1004255 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1004256 : term42 = term42.
Proof. exact (MK_COMB (@lem1004255) (@lem1004254)). Qed.
Lemma lem1004257 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1004258 : term43 = term43.
Proof. exact (MK_COMB (@lem1004257) (@lem1004256)). Qed.
Lemma lem1004259 : term44 = term44.
Proof. exact (MK_COMB (@lem1004258) (@lem1004242)). Qed.
Lemma lem1004260 (h1 : term44) : term44.
Proof. exact (EQ_MP (@lem1004259) (@lem1004145 h1)). Qed.
Lemma lem1004267 (n : nat) : ((NUMERAL n) = n) = ((NUMERAL n) = n).
Proof. exact (eq_refl ((NUMERAL n) = n)). Qed.
Lemma lem1004268 : term21 = term21.
Proof. exact (fun_ext (fun n : nat => @lem1004267 n)). Qed.
Lemma lem1004269 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1004270 : term11 = term11.
Proof. exact (MK_COMB (@lem1004269) (@lem1004268)). Qed.
Lemma lem1004271 (h1 : term11) : term11.
Proof. exact (EQ_MP (@lem1004270) (@lem1004158 h1)). Qed.
Lemma lem1004273 (h1 : term44) : term42.
Proof. exact (proj1 (@lem1004260 h1)). Qed.
Lemma lem1004281 (m : nat) (h1 : term4 m) : term4 m.
Proof. exact (h1). Qed.
Lemma lem1004283 (n : nat) : ((NUMERAL n) = n) = ((NUMERAL n) = n).
Proof. exact (eq_refl ((NUMERAL n) = n)). Qed.
Lemma lem1004284 : term21 = term21.
Proof. exact (fun_ext (fun n : nat => @lem1004283 n)). Qed.
Lemma lem1004285 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1004287 : term11 = term11.
Proof. exact (MK_COMB (@lem1004285) (@lem1004284)). Qed.
Lemma lem1004288 (h1 : term11) : term11.
Proof. exact (EQ_MP (@lem1004287) (@lem1004271 h1)). Qed.
Lemma lem1004290 (n : nat) : ((term40 n) = n) = ((term40 n) = n).
Proof. exact (eq_refl ((term40 n) = n)). Qed.
Lemma lem1004291 : term41 = term41.
Proof. exact (fun_ext (fun n : nat => @lem1004290 n)). Qed.
Lemma lem1004292 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1004294 : term42 = term42.
Proof. exact (MK_COMB (@lem1004292) (@lem1004291)). Qed.
Lemma lem1004295 (h1 : term44) : term42.
Proof. exact (EQ_MP (@lem1004294) (@lem1004273 h1)). Qed.
Lemma lem1004323 (_16272 : nat) (h1 : term11) : term45 _16272.
Proof. exact (@lem1004288 h1 _16272). Qed.
Lemma lem1004324 (_16272 : nat) : (term45 _16272) = ((NUMERAL _16272) = _16272).
Proof. exact (eq_refl (term45 _16272)). Qed.
Lemma lem1004326 (_16273 : nat) (h1 : term44) : term46 _16273.
Proof. exact (@lem1004295 h1 _16273). Qed.
Lemma lem1004327 (_16273 : nat) : (term46 _16273) = ((term40 _16273) = _16273).
Proof. exact (eq_refl (term46 _16273)). Qed.
Lemma lem1004345 (m : nat) (h1 : term4 m) : term4 m.
Proof. exact (h1). Qed.
Lemma lem1004356 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1004357 (_16279 : nat) (_16281 : nat) (h1 : _16279 = _16281) : _16279 = _16281.
Proof. exact (h1). Qed.
Lemma lem1004358 (_16280 : nat) (_16282 : nat) (h1 : _16280 = _16282) : _16280 = _16282.
Proof. exact (h1). Qed.
Lemma lem1004359 (_16279 : nat) (_16281 : nat) (h1 : _16279 = _16281) : (Nat.add _16279) = (Nat.add _16281).
Proof. exact (MK_COMB (@lem1004356) (@lem1004357 _16279 _16281 h1)). Qed.
Lemma lem1004360 (_16279 : nat) (_16281 : nat) (_16280 : nat) (_16282 : nat) (h1 : _16279 = _16281) (h2 : _16280 = _16282) : (Nat.add _16279 _16280) = (Nat.add _16281 _16282).
Proof. exact (MK_COMB (@lem1004359 _16279 _16281 h1) (@lem1004358 _16280 _16282 h2)). Qed.
Lemma lem1004361 (_16280 : nat) (_16282 : nat) (_16279 : nat) (_16281 : nat) (h1 : _16279 = _16281) : term47 _16279 _16280 _16281 _16282.
Proof. exact (fun h0 : _16280 = _16282 => @lem1004360 _16279 _16281 _16280 _16282 h1 h0). Qed.
Lemma lem1004363 (a : Prop) (b : Prop) : (a -> b) = (term48 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1004364 (_16279 : nat) (_16280 : nat) (_16281 : nat) (_16282 : nat) : (term47 _16279 _16280 _16281 _16282) = (term49 _16279 _16280 _16281 _16282).
Proof. exact (@lem1004363 (_16280 = _16282) ((Nat.add _16279 _16280) = (Nat.add _16281 _16282))). Qed.
Lemma lem1004365 (_16280 : nat) (_16282 : nat) (_16279 : nat) (_16281 : nat) (h1 : _16279 = _16281) : term49 _16279 _16280 _16281 _16282.
Proof. exact (EQ_MP (@lem1004364 _16279 _16280 _16281 _16282) (@lem1004361 _16280 _16282 _16279 _16281 h1)). Qed.
Lemma lem1004366 (_16279 : nat) (_16280 : nat) (_16281 : nat) (_16282 : nat) : term50 _16279 _16280 _16281 _16282.
Proof. exact (fun h0 : _16279 = _16281 => @lem1004365 _16280 _16282 _16279 _16281 h0). Qed.
Lemma lem1004368 (a : Prop) (b : Prop) : (a -> b) = (term48 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1004369 (_16279 : nat) (_16280 : nat) (_16281 : nat) (_16282 : nat) : (term50 _16279 _16280 _16281 _16282) = (term51 _16279 _16280 _16281 _16282).
Proof. exact (@lem1004368 (_16279 = _16281) (term49 _16279 _16280 _16281 _16282)). Qed.
Lemma lem1004370 (_16279 : nat) (_16280 : nat) (_16281 : nat) (_16282 : nat) : term51 _16279 _16280 _16281 _16282.
Proof. exact (EQ_MP (@lem1004369 _16279 _16280 _16281 _16282) (@lem1004366 _16279 _16280 _16281 _16282)). Qed.
Lemma lem1004379 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem1004380 (_16285 : nat) (_16286 : nat) (h1 : _16285 = _16286) : _16285 = _16286.
Proof. exact (h1). Qed.
Lemma lem1004381 (_16285 : nat) (_16286 : nat) (h1 : _16285 = _16286) : (S _16285) = (S _16286).
Proof. exact (MK_COMB (@lem1004379) (@lem1004380 _16285 _16286 h1)). Qed.
Lemma lem1004382 (_16285 : nat) (_16286 : nat) : term52 _16285 _16286.
Proof. exact (fun h0 : _16285 = _16286 => @lem1004381 _16285 _16286 h0). Qed.
Lemma lem1004384 (a : Prop) (b : Prop) : (a -> b) = (term48 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1004385 (_16285 : nat) (_16286 : nat) : (term52 _16285 _16286) = (term53 _16285 _16286).
Proof. exact (@lem1004384 (_16285 = _16286) ((S _16285) = (S _16286))). Qed.
Lemma lem1004386 (_16285 : nat) (_16286 : nat) : term53 _16285 _16286.
Proof. exact (EQ_MP (@lem1004385 _16285 _16286) (@lem1004382 _16285 _16286)). Qed.
Lemma lem1004388 (x : nat) (y : nat) (z : nat) : term54 x y z.
Proof. exact (@lem21385 nat x y z). Qed.
Lemma lem1004390 (_16272 : nat) (h1 : term11) : (NUMERAL _16272) = _16272.
Proof. exact (EQ_MP (@lem1004324 _16272) (@lem1004323 _16272 h1)). Qed.
Lemma lem1004391 (h1 : term11) : (NUMERAL 0) = 0.
Proof. exact (@lem1004390 0 h1). Qed.
Lemma lem1004392 (h1 : term11) : term55.
Proof. exact (fun h0 : term56 => @lem1004391 h1). Qed.
Lemma lem1004394 (p : Prop) : (term57 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1004395 : term55 = ((NUMERAL 0) = 0).
Proof. exact (@lem1004394 ((NUMERAL 0) = 0)). Qed.
Lemma lem1004396 (h1 : term11) : (NUMERAL 0) = 0.
Proof. exact (EQ_MP (@lem1004395) (@lem1004392 h1)). Qed.
Lemma lem1004398 (_16272 : nat) (h1 : term11) : (NUMERAL _16272) = _16272.
Proof. exact (EQ_MP (@lem1004324 _16272) (@lem1004323 _16272 h1)). Qed.
Lemma lem1004399 (m : nat) (h1 : term11) : (NUMERAL m) = m.
Proof. exact (@lem1004398 m h1). Qed.
Lemma lem1004400 (m : nat) (h1 : term11) : term58 m.
Proof. exact (fun h0 : term59 m => @lem1004399 m h1). Qed.
Lemma lem1004402 (p : Prop) : (term57 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1004403 (m : nat) : (term58 m) = ((NUMERAL m) = m).
Proof. exact (@lem1004402 ((NUMERAL m) = m)). Qed.
Lemma lem1004404 (m : nat) (h1 : term11) : (NUMERAL m) = m.
Proof. exact (EQ_MP (@lem1004403 m) (@lem1004400 m h1)). Qed.
Lemma lem1004422 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1004423 (_16279 : nat) (_16281 : nat) (_16280 : nat) (_16282 : nat) : (term49 _16279 _16280 _16281 _16282) = (term60 _16279 _16281 _16280 _16282).
Proof. exact (@lem1004422 ((Nat.add _16279 _16280) = (Nat.add _16281 _16282)) (term61 _16280 _16282)). Qed.
Lemma lem1004433 (_16279 : nat) (_16281 : nat) : (term62 _16279 _16281) = (term62 _16279 _16281).
Proof. exact (eq_refl (term62 _16279 _16281)). Qed.
Lemma lem1004434 (_16279 : nat) (_16281 : nat) (_16280 : nat) (_16282 : nat) : (term51 _16279 _16280 _16281 _16282) = (term63 _16279 _16281 _16280 _16282).
Proof. exact (MK_COMB (@lem1004433 _16279 _16281) (@lem1004423 _16279 _16281 _16280 _16282)). Qed.
Lemma lem1004438 (q : Prop) (p : Prop) (r : Prop) : (term64 p q r) = (term64 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1004439 (_16279 : nat) (_16281 : nat) (_16280 : nat) (_16282 : nat) : (term63 _16279 _16281 _16280 _16282) = (term65 _16279 _16281 _16280 _16282).
Proof. exact (@lem1004438 ((Nat.add _16279 _16280) = (Nat.add _16281 _16282)) (term61 _16279 _16281) (term61 _16280 _16282)). Qed.
Lemma lem1004461 (_16279 : nat) (_16281 : nat) (_16280 : nat) (_16282 : nat) : (term51 _16279 _16280 _16281 _16282) = (term65 _16279 _16281 _16280 _16282).
Proof. exact (TRANS (@lem1004434 _16279 _16281 _16280 _16282) (@lem1004439 _16279 _16281 _16280 _16282)). Qed.
Lemma lem1004462 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1004463 (_16279 : nat) (_16281 : nat) (_16280 : nat) (_16282 : nat) : (term66 _16279 _16280 _16281 _16282) = (term67 _16279 _16281 _16280 _16282).
Proof. exact (MK_COMB (@lem1004462) (@lem1004461 _16279 _16281 _16280 _16282)). Qed.
Lemma lem1004485 (_16279 : nat) (_16281 : nat) (_16280 : nat) (_16282 : nat) : (term65 _16279 _16281 _16280 _16282) = (term65 _16279 _16281 _16280 _16282).
Proof. exact (eq_refl (term65 _16279 _16281 _16280 _16282)). Qed.
Lemma lem1004486 (_16279 : nat) (_16281 : nat) (_16280 : nat) (_16282 : nat) : ((term51 _16279 _16280 _16281 _16282) = (term65 _16279 _16281 _16280 _16282)) = ((term65 _16279 _16281 _16280 _16282) = (term65 _16279 _16281 _16280 _16282)).
Proof. exact (MK_COMB (@lem1004463 _16279 _16281 _16280 _16282) (@lem1004485 _16279 _16281 _16280 _16282)). Qed.
Lemma lem1004488 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1004489 (x : Prop) : (x = x) = True.
Proof. exact (@lem1004488 Prop x). Qed.
Lemma lem1004490 (_16279 : nat) (_16281 : nat) (_16280 : nat) (_16282 : nat) : ((term65 _16279 _16281 _16280 _16282) = (term65 _16279 _16281 _16280 _16282)) = True.
Proof. exact (@lem1004489 (term65 _16279 _16281 _16280 _16282)). Qed.
Lemma lem1004491 (_16279 : nat) (_16281 : nat) (_16280 : nat) (_16282 : nat) : ((term51 _16279 _16280 _16281 _16282) = (term65 _16279 _16281 _16280 _16282)) = True.
Proof. exact (TRANS (@lem1004486 _16279 _16281 _16280 _16282) (@lem1004490 _16279 _16281 _16280 _16282)). Qed.
Lemma lem1004492 (_16279 : nat) (_16281 : nat) (_16280 : nat) (_16282 : nat) : True = ((term51 _16279 _16280 _16281 _16282) = (term65 _16279 _16281 _16280 _16282)).
Proof. exact (SYM (@lem1004491 _16279 _16281 _16280 _16282)). Qed.
Lemma lem1004493 (_16279 : nat) (_16281 : nat) (_16280 : nat) (_16282 : nat) : (term51 _16279 _16280 _16281 _16282) = (term65 _16279 _16281 _16280 _16282).
Proof. exact (EQ_MP (@lem1004492 _16279 _16281 _16280 _16282) (@lem0)). Qed.
Lemma lem1004494 (_16279 : nat) (_16281 : nat) (_16280 : nat) (_16282 : nat) : term65 _16279 _16281 _16280 _16282.
Proof. exact (EQ_MP (@lem1004493 _16279 _16281 _16280 _16282) (@lem1004370 _16279 _16280 _16281 _16282)). Qed.
Lemma lem1004496 (b : Prop) (a : Prop) : (a \/ b) = (term68 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1004497 (_16279 : nat) (_16280 : nat) (_16281 : nat) (_16282 : nat) : (term65 _16279 _16281 _16280 _16282) = (term69 _16279 _16280 _16281 _16282).
Proof. exact (@lem1004496 (term70 _16279 _16281 _16280 _16282) ((Nat.add _16279 _16280) = (Nat.add _16281 _16282))). Qed.
Lemma lem1004499 (a : Prop) (b : Prop) : (term71 a b) = (term72 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1004500 (_16279 : nat) (_16281 : nat) (_16280 : nat) (_16282 : nat) : (term73 _16279 _16281 _16280 _16282) = (term74 _16279 _16281 _16280 _16282).
Proof. exact (@lem1004499 (term61 _16279 _16281) (term61 _16280 _16282)). Qed.
Lemma lem1004502 (a : Prop) : (term75 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1004503 (_16279 : nat) (_16281 : nat) : (term76 _16279 _16281) = (_16279 = _16281).
Proof. exact (@lem1004502 (_16279 = _16281)). Qed.
Lemma lem1004504 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1004505 (_16279 : nat) (_16281 : nat) : (term77 _16279 _16281) = (term78 _16279 _16281).
Proof. exact (MK_COMB (@lem1004504) (@lem1004503 _16279 _16281)). Qed.
Lemma lem1004507 (a : Prop) : (term75 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1004508 (_16280 : nat) (_16282 : nat) : (term76 _16280 _16282) = (_16280 = _16282).
Proof. exact (@lem1004507 (_16280 = _16282)). Qed.
Lemma lem1004509 (_16279 : nat) (_16281 : nat) (_16280 : nat) (_16282 : nat) : (term74 _16279 _16281 _16280 _16282) = (term79 _16279 _16281 _16280 _16282).
Proof. exact (MK_COMB (@lem1004505 _16279 _16281) (@lem1004508 _16280 _16282)). Qed.
Lemma lem1004510 (_16279 : nat) (_16281 : nat) (_16280 : nat) (_16282 : nat) : (term73 _16279 _16281 _16280 _16282) = (term79 _16279 _16281 _16280 _16282).
Proof. exact (TRANS (@lem1004500 _16279 _16281 _16280 _16282) (@lem1004509 _16279 _16281 _16280 _16282)). Qed.
Lemma lem1004511 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1004512 (_16279 : nat) (_16281 : nat) (_16280 : nat) (_16282 : nat) : (term80 _16279 _16281 _16280 _16282) = (term81 _16279 _16281 _16280 _16282).
Proof. exact (MK_COMB (@lem1004511) (@lem1004510 _16279 _16281 _16280 _16282)). Qed.
Lemma lem1004513 (_16279 : nat) (_16280 : nat) (_16281 : nat) (_16282 : nat) : ((Nat.add _16279 _16280) = (Nat.add _16281 _16282)) = ((Nat.add _16279 _16280) = (Nat.add _16281 _16282)).
Proof. exact (eq_refl ((Nat.add _16279 _16280) = (Nat.add _16281 _16282))). Qed.
Lemma lem1004514 (_16279 : nat) (_16280 : nat) (_16281 : nat) (_16282 : nat) : (term69 _16279 _16280 _16281 _16282) = (term82 _16279 _16280 _16281 _16282).
Proof. exact (MK_COMB (@lem1004512 _16279 _16281 _16280 _16282) (@lem1004513 _16279 _16280 _16281 _16282)). Qed.
Lemma lem1004515 (_16279 : nat) (_16280 : nat) (_16281 : nat) (_16282 : nat) : (term65 _16279 _16281 _16280 _16282) = (term82 _16279 _16280 _16281 _16282).
Proof. exact (TRANS (@lem1004497 _16279 _16280 _16281 _16282) (@lem1004514 _16279 _16280 _16281 _16282)). Qed.
Lemma lem1004517 (m : nat) (h1 : term11) : term83 m.
Proof. exact (conj (@lem1004396 h1) (@lem1004404 m h1)). Qed.
Lemma lem1004519 (_16279 : nat) (_16280 : nat) (_16281 : nat) (_16282 : nat) : term82 _16279 _16280 _16281 _16282.
Proof. exact (EQ_MP (@lem1004515 _16279 _16280 _16281 _16282) (@lem1004494 _16279 _16281 _16280 _16282)). Qed.
Lemma lem1004520 (m : nat) : term84 m.
Proof. exact (@lem1004519 (NUMERAL 0) (NUMERAL m) 0 m). Qed.
Lemma lem1004523 (m : nat) (h1 : term11) : (term85 m) = (Nat.add 0 m).
Proof. exact (@lem1004520 m (@lem1004517 m h1)). Qed.
Lemma lem1004524 (m : nat) (h1 : term11) : term86 m.
Proof. exact (fun h0 : term87 m => @lem1004523 m h1). Qed.
Lemma lem1004526 (p : Prop) : (term57 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1004527 (m : nat) : (term86 m) = ((term85 m) = (Nat.add 0 m)).
Proof. exact (@lem1004526 ((term85 m) = (Nat.add 0 m))). Qed.
Lemma lem1004528 (m : nat) (h1 : term11) : (term85 m) = (Nat.add 0 m).
Proof. exact (EQ_MP (@lem1004527 m) (@lem1004524 m h1)). Qed.
Lemma lem1004530 (_16273 : nat) (h1 : term44) : (term40 _16273) = _16273.
Proof. exact (EQ_MP (@lem1004327 _16273) (@lem1004326 _16273 h1)). Qed.
Lemma lem1004531 (m : nat) (h1 : term44) : (term85 m) = (NUMERAL m).
Proof. exact (@lem1004530 (NUMERAL m) h1). Qed.
Lemma lem1004532 (m : nat) (h1 : term44) : term88 m.
Proof. exact (fun h0 : term89 m => @lem1004531 m h1). Qed.
Lemma lem1004534 (p : Prop) : (term57 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1004535 (m : nat) : (term88 m) = ((term85 m) = (NUMERAL m)).
Proof. exact (@lem1004534 ((term85 m) = (NUMERAL m))). Qed.
Lemma lem1004536 (m : nat) (h1 : term44) : (term85 m) = (NUMERAL m).
Proof. exact (EQ_MP (@lem1004535 m) (@lem1004532 m h1)). Qed.
Lemma lem1004554 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1004555 (y : nat) (x : nat) (z : nat) : (term90 x y z) = (term91 y x z).
Proof. exact (@lem1004554 (y = z) (term61 x z)). Qed.
Lemma lem1004565 (x : nat) (y : nat) : (term62 x y) = (term62 x y).
Proof. exact (eq_refl (term62 x y)). Qed.
Lemma lem1004566 (y : nat) (x : nat) (z : nat) : (term54 x y z) = (term92 y x z).
Proof. exact (MK_COMB (@lem1004565 x y) (@lem1004555 y x z)). Qed.
Lemma lem1004570 (q : Prop) (p : Prop) (r : Prop) : (term64 p q r) = (term64 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1004571 (y : nat) (x : nat) (z : nat) : (term92 y x z) = (term93 y x z).
Proof. exact (@lem1004570 (y = z) (term61 x y) (term61 x z)). Qed.
Lemma lem1004593 (y : nat) (x : nat) (z : nat) : (term54 x y z) = (term93 y x z).
Proof. exact (TRANS (@lem1004566 y x z) (@lem1004571 y x z)). Qed.
Lemma lem1004594 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1004595 (y : nat) (x : nat) (z : nat) : (term94 x y z) = (term95 y x z).
Proof. exact (MK_COMB (@lem1004594) (@lem1004593 y x z)). Qed.
Lemma lem1004617 (y : nat) (x : nat) (z : nat) : (term93 y x z) = (term93 y x z).
Proof. exact (eq_refl (term93 y x z)). Qed.
Lemma lem1004618 (y : nat) (x : nat) (z : nat) : ((term54 x y z) = (term93 y x z)) = ((term93 y x z) = (term93 y x z)).
Proof. exact (MK_COMB (@lem1004595 y x z) (@lem1004617 y x z)). Qed.
Lemma lem1004620 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1004621 (x : Prop) : (x = x) = True.
Proof. exact (@lem1004620 Prop x). Qed.
Lemma lem1004622 (y : nat) (x : nat) (z : nat) : ((term93 y x z) = (term93 y x z)) = True.
Proof. exact (@lem1004621 (term93 y x z)). Qed.
Lemma lem1004623 (y : nat) (x : nat) (z : nat) : ((term54 x y z) = (term93 y x z)) = True.
Proof. exact (TRANS (@lem1004618 y x z) (@lem1004622 y x z)). Qed.
Lemma lem1004624 (y : nat) (x : nat) (z : nat) : True = ((term54 x y z) = (term93 y x z)).
Proof. exact (SYM (@lem1004623 y x z)). Qed.
Lemma lem1004625 (y : nat) (x : nat) (z : nat) : (term54 x y z) = (term93 y x z).
Proof. exact (EQ_MP (@lem1004624 y x z) (@lem0)). Qed.
Lemma lem1004626 (y : nat) (x : nat) (z : nat) : term93 y x z.
Proof. exact (EQ_MP (@lem1004625 y x z) (@lem1004388 x y z)). Qed.
Lemma lem1004628 (b : Prop) (a : Prop) : (a \/ b) = (term68 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1004629 (x : nat) (y : nat) (z : nat) : (term93 y x z) = (term96 x y z).
Proof. exact (@lem1004628 (term97 y x z) (y = z)). Qed.
Lemma lem1004631 (a : Prop) (b : Prop) : (term71 a b) = (term72 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1004632 (y : nat) (x : nat) (z : nat) : (term98 y x z) = (term99 y x z).
Proof. exact (@lem1004631 (term61 x y) (term61 x z)). Qed.
Lemma lem1004634 (a : Prop) : (term75 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1004635 (x : nat) (y : nat) : (term76 x y) = (x = y).
Proof. exact (@lem1004634 (x = y)). Qed.
Lemma lem1004636 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1004637 (x : nat) (y : nat) : (term77 x y) = (term78 x y).
Proof. exact (MK_COMB (@lem1004636) (@lem1004635 x y)). Qed.
Lemma lem1004639 (a : Prop) : (term75 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1004640 (x : nat) (z : nat) : (term76 x z) = (x = z).
Proof. exact (@lem1004639 (x = z)). Qed.
Lemma lem1004641 (y : nat) (x : nat) (z : nat) : (term99 y x z) = (term100 y x z).
Proof. exact (MK_COMB (@lem1004637 x y) (@lem1004640 x z)). Qed.
Lemma lem1004642 (y : nat) (x : nat) (z : nat) : (term98 y x z) = (term100 y x z).
Proof. exact (TRANS (@lem1004632 y x z) (@lem1004641 y x z)). Qed.
Lemma lem1004643 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1004644 (y : nat) (x : nat) (z : nat) : (term101 y x z) = (term102 y x z).
Proof. exact (MK_COMB (@lem1004643) (@lem1004642 y x z)). Qed.
Lemma lem1004645 (y : nat) (z : nat) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1004646 (x : nat) (y : nat) (z : nat) : (term96 x y z) = (term103 x y z).
Proof. exact (MK_COMB (@lem1004644 y x z) (@lem1004645 y z)). Qed.
Lemma lem1004647 (x : nat) (y : nat) (z : nat) : (term93 y x z) = (term103 x y z).
Proof. exact (TRANS (@lem1004629 x y z) (@lem1004646 x y z)). Qed.
Lemma lem1004649 (m : nat) (h1 : term11) (h2 : term44) : term104 m.
Proof. exact (conj (@lem1004528 m h1) (@lem1004536 m h2)). Qed.
Lemma lem1004651 (x : nat) (y : nat) (z : nat) : term103 x y z.
Proof. exact (EQ_MP (@lem1004647 x y z) (@lem1004626 y x z)). Qed.
Lemma lem1004652 (m : nat) : term105 m.
Proof. exact (@lem1004651 (term85 m) (Nat.add 0 m) (NUMERAL m)). Qed.
Lemma lem1004655 (m : nat) (h1 : term11) (h2 : term44) : (Nat.add 0 m) = (NUMERAL m).
Proof. exact (@lem1004652 m (@lem1004649 m h1 h2)). Qed.
Lemma lem1004656 (m : nat) (h1 : term11) (h2 : term44) : term106 m.
Proof. exact (fun h0 : term107 m => @lem1004655 m h1 h2). Qed.
Lemma lem1004658 (p : Prop) : (term57 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1004659 (m : nat) : (term106 m) = ((Nat.add 0 m) = (NUMERAL m)).
Proof. exact (@lem1004658 ((Nat.add 0 m) = (NUMERAL m))). Qed.
Lemma lem1004660 (m : nat) (h1 : term11) (h2 : term44) : (Nat.add 0 m) = (NUMERAL m).
Proof. exact (EQ_MP (@lem1004659 m) (@lem1004656 m h1 h2)). Qed.
Lemma lem1004666 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1004667 (_16285 : nat) (_16286 : nat) : (term53 _16285 _16286) = (term108 _16285 _16286).
Proof. exact (@lem1004666 ((S _16285) = (S _16286)) (term61 _16285 _16286)). Qed.
Lemma lem1004677 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1004678 (_16285 : nat) (_16286 : nat) : (term109 _16285 _16286) = (term110 _16285 _16286).
Proof. exact (MK_COMB (@lem1004677) (@lem1004667 _16285 _16286)). Qed.
Lemma lem1004688 (_16285 : nat) (_16286 : nat) : (term108 _16285 _16286) = (term108 _16285 _16286).
Proof. exact (eq_refl (term108 _16285 _16286)). Qed.
Lemma lem1004689 (_16285 : nat) (_16286 : nat) : ((term53 _16285 _16286) = (term108 _16285 _16286)) = ((term108 _16285 _16286) = (term108 _16285 _16286)).
Proof. exact (MK_COMB (@lem1004678 _16285 _16286) (@lem1004688 _16285 _16286)). Qed.
Lemma lem1004691 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1004692 (x : Prop) : (x = x) = True.
Proof. exact (@lem1004691 Prop x). Qed.
Lemma lem1004693 (_16285 : nat) (_16286 : nat) : ((term108 _16285 _16286) = (term108 _16285 _16286)) = True.
Proof. exact (@lem1004692 (term108 _16285 _16286)). Qed.
Lemma lem1004694 (_16285 : nat) (_16286 : nat) : ((term53 _16285 _16286) = (term108 _16285 _16286)) = True.
Proof. exact (TRANS (@lem1004689 _16285 _16286) (@lem1004693 _16285 _16286)). Qed.
Lemma lem1004695 (_16285 : nat) (_16286 : nat) : True = ((term53 _16285 _16286) = (term108 _16285 _16286)).
Proof. exact (SYM (@lem1004694 _16285 _16286)). Qed.
Lemma lem1004696 (_16285 : nat) (_16286 : nat) : (term53 _16285 _16286) = (term108 _16285 _16286).
Proof. exact (EQ_MP (@lem1004695 _16285 _16286) (@lem0)). Qed.
Lemma lem1004697 (_16285 : nat) (_16286 : nat) : term108 _16285 _16286.
Proof. exact (EQ_MP (@lem1004696 _16285 _16286) (@lem1004386 _16285 _16286)). Qed.
Lemma lem1004699 (b : Prop) (a : Prop) : (a \/ b) = (term68 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1004700 (_16285 : nat) (_16286 : nat) : (term108 _16285 _16286) = (term111 _16285 _16286).
Proof. exact (@lem1004699 (term61 _16285 _16286) ((S _16285) = (S _16286))). Qed.
Lemma lem1004702 (a : Prop) : (term75 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1004703 (_16285 : nat) (_16286 : nat) : (term76 _16285 _16286) = (_16285 = _16286).
Proof. exact (@lem1004702 (_16285 = _16286)). Qed.
Lemma lem1004704 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1004705 (_16285 : nat) (_16286 : nat) : (term112 _16285 _16286) = (term113 _16285 _16286).
Proof. exact (MK_COMB (@lem1004704) (@lem1004703 _16285 _16286)). Qed.
Lemma lem1004706 (_16285 : nat) (_16286 : nat) : ((S _16285) = (S _16286)) = ((S _16285) = (S _16286)).
Proof. exact (eq_refl ((S _16285) = (S _16286))). Qed.
Lemma lem1004707 (_16285 : nat) (_16286 : nat) : (term111 _16285 _16286) = (term52 _16285 _16286).
Proof. exact (MK_COMB (@lem1004705 _16285 _16286) (@lem1004706 _16285 _16286)). Qed.
Lemma lem1004708 (_16285 : nat) (_16286 : nat) : (term108 _16285 _16286) = (term52 _16285 _16286).
Proof. exact (TRANS (@lem1004700 _16285 _16286) (@lem1004707 _16285 _16286)). Qed.
Lemma lem1004711 (_16285 : nat) (_16286 : nat) : term52 _16285 _16286.
Proof. exact (EQ_MP (@lem1004708 _16285 _16286) (@lem1004697 _16285 _16286)). Qed.
Lemma lem1004712 (m : nat) : term114 m.
Proof. exact (@lem1004711 (Nat.add 0 m) (NUMERAL m)). Qed.
Lemma lem1004715 (m : nat) (h1 : term11) (h2 : term44) : (term1 m) = (term2 m).
Proof. exact (@lem1004712 m (@lem1004660 m h1 h2)). Qed.
Lemma lem1004716 (m : nat) (h1 : term11) (h2 : term44) : term115 m.
Proof. exact (fun h0 : term4 m => @lem1004715 m h1 h2). Qed.
Lemma lem1004718 (p : Prop) : (term57 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1004719 (m : nat) : (term115 m) = ((term1 m) = (term2 m)).
Proof. exact (@lem1004718 ((term1 m) = (term2 m))). Qed.
Lemma lem1004720 (m : nat) (h1 : term11) (h2 : term44) : (term1 m) = (term2 m).
Proof. exact (EQ_MP (@lem1004719 m) (@lem1004716 m h1 h2)). Qed.
Lemma lem1004723 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1004725 (m : nat) : (term4 m) = (term116 m).
Proof. exact (@lem1004723 ((term1 m) = (term2 m))). Qed.
Lemma lem1004728 (m : nat) (h1 : term4 m) : term116 m.
Proof. exact (EQ_MP (@lem1004725 m) (@lem1004345 m h1)). Qed.
Lemma lem1004731 (m : nat) (h1 : term11) (h2 : term4 m) (h3 : term44) : False.
Proof. exact (@lem1004728 m h2 (@lem1004720 m h1 h3)). Qed.
Lemma lem1004732 (m : nat) (h1 : term11) (h2 : term4 m) (h3 : term44) : term117.
Proof. exact (fun h0 : ~ False => @lem1004731 m h1 h2 h3). Qed.
Lemma lem1004734 (p : Prop) : (term57 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1004735 : term117 = False.
Proof. exact (@lem1004734 False). Qed.
Lemma lem1004736 (m : nat) (h1 : term11) (h2 : term4 m) (h3 : term44) : False.
Proof. exact (EQ_MP (@lem1004735) (@lem1004732 m h1 h2 h3)). Qed.
Lemma lem1004737 (m : nat) (h1 : term11) (h2 : term4 m) (h3 : term44) : (term4 m) = False.
Proof. exact (prop_ext (fun h4 : term4 m => @lem1004736 m h1 h2 h3) (fun h4 : False => @lem1004345 m h2)). Qed.
Lemma lem1004738 (m : nat) (h1 : term11) (h2 : term4 m) (h3 : term44) : False.
Proof. exact (EQ_MP (@lem1004737 m h1 h2 h3) (@lem1004345 m h2)). Qed.
Lemma lem1004739 (m : nat) (h1 : term11) (h2 : term4 m) (h3 : term44) : (term4 m) = False.
Proof. exact (prop_ext (fun h4 : term4 m => @lem1004738 m h1 h2 h3) (fun h4 : False => @lem1004281 m h2)). Qed.
Lemma lem1004740 (m : nat) (h1 : term11) (h2 : term4 m) (h3 : term44) : False.
Proof. exact (EQ_MP (@lem1004739 m h1 h2 h3) (@lem1004281 m h2)). Qed.
Lemma lem1004741 (m : nat) (h1 : term11) (h2 : term4 m) (h3 : term44) : term11 = False.
Proof. exact (prop_ext (fun h4 : term11 => @lem1004740 m h1 h2 h3) (fun h4 : False => @lem1004288 h1)). Qed.
Lemma lem1004742 (m : nat) (h1 : term11) (h2 : term4 m) (h3 : term44) : False.
Proof. exact (EQ_MP (@lem1004741 m h1 h2 h3) (@lem1004288 h1)). Qed.
Lemma lem1004743 (m : nat) (h1 : term11) (h2 : term4 m) (h3 : term44) : (term4 m) = False.
Proof. exact (prop_ext (fun h4 : term4 m => @lem1004742 m h1 h2 h3) (fun h4 : False => @lem1004281 m h2)). Qed.
Lemma lem1004744 (m : nat) (h1 : term11) (h2 : term4 m) (h3 : term44) : False.
Proof. exact (EQ_MP (@lem1004743 m h1 h2 h3) (@lem1004281 m h2)). Qed.
Lemma lem1004745 (m : nat) (h1 : term11) (h2 : term4 m) (h3 : term44) : term11 = False.
Proof. exact (prop_ext (fun h4 : term11 => @lem1004744 m h1 h2 h3) (fun h4 : False => @lem1004271 h1)). Qed.
Lemma lem1004746 (m : nat) (h1 : term11) (h2 : term4 m) (h3 : term44) : False.
Proof. exact (EQ_MP (@lem1004745 m h1 h2 h3) (@lem1004271 h1)). Qed.
Lemma lem1004747 (m : nat) (h1 : term11) (h2 : term4 m) (h3 : term44) : term44 = False.
Proof. exact (prop_ext (fun h4 : term44 => @lem1004746 m h1 h2 h3) (fun h4 : False => @lem1004260 h3)). Qed.
Lemma lem1004748 (m : nat) (h1 : term11) (h2 : term4 m) (h3 : term44) : False.
Proof. exact (EQ_MP (@lem1004747 m h1 h2 h3) (@lem1004260 h3)). Qed.
Lemma lem1004749 (m : nat) (h1 : term11) (h2 : term4 m) (h3 : term44) : (term4 m) = False.
Proof. exact (prop_ext (fun h4 : term4 m => @lem1004748 m h1 h2 h3) (fun h4 : False => @lem1004176 m h2)). Qed.
Lemma lem1004750 (m : nat) (h1 : term11) (h2 : term4 m) (h3 : term44) : False.
Proof. exact (EQ_MP (@lem1004749 m h1 h2 h3) (@lem1004176 m h2)). Qed.
Lemma lem1004751 (m : nat) (h1 : term11) (h2 : term4 m) (h3 : term44) : term11 = False.
Proof. exact (prop_ext (fun h4 : term11 => @lem1004750 m h1 h2 h3) (fun h4 : False => @lem1004158 h1)). Qed.
Lemma lem1004752 (m : nat) (h1 : term11) (h2 : term4 m) (h3 : term44) : False.
Proof. exact (EQ_MP (@lem1004751 m h1 h2 h3) (@lem1004158 h1)). Qed.
Lemma lem1004753 (m : nat) (h1 : term11) (h2 : term4 m) (h3 : term44) : term44 = False.
Proof. exact (prop_ext (fun h4 : term44 => @lem1004752 m h1 h2 h3) (fun h4 : False => @lem1004145 h3)). Qed.
Lemma lem1004754 (m : nat) (h1 : term11) (h2 : term4 m) (h3 : term44) : False.
Proof. exact (EQ_MP (@lem1004753 m h1 h2 h3) (@lem1004145 h3)). Qed.
Lemma lem1004755 (m : nat) (h1 : term11) (h2 : term4 m) (h3 : term44) : (term4 m) = False.
Proof. exact (prop_ext (fun h4 : term4 m => @lem1004754 m h1 h2 h3) (fun h4 : False => @lem1004085 m h2)). Qed.
Lemma lem1004756 (m : nat) (h1 : term11) (h2 : term4 m) (h3 : term44) : False.
Proof. exact (EQ_MP (@lem1004755 m h1 h2 h3) (@lem1004085 m h2)). Qed.
Lemma lem1004757 (m : nat) (h1 : term4 m) (h2 : term44) : term9.
Proof. exact (fun h0 : term11 => @lem1004756 m h0 h1 h2). Qed.
Lemma lem1004758 : term9 = term10.
Proof. exact (@lem69 term11). Qed.
Lemma lem1004759 (m : nat) (h1 : term4 m) (h2 : term44) : term10.
Proof. exact (EQ_MP (@lem1004758) (@lem1004757 m h1 h2)). Qed.
Lemma lem1004760 (m : nat) (h1 : term4 m) : term14.
Proof. exact (fun h0 : term44 => @lem1004759 m h1 h0). Qed.
Lemma lem1004761 (m : nat) : term16 m.
Proof. exact (fun h0 : term4 m => @lem1004760 m h0). Qed.
Lemma lem1004766 : term20.
Proof. exact (fun m : nat => @lem1004761 m). Qed.
Lemma lem1004767 : term19.
Proof. exact (EQ_MP (@lem1004076) (@lem1004766)). Qed.
Lemma lem1004768 (m : nat) : term118 m.
Proof. exact (@lem1004767 m). Qed.
Lemma lem1004769 (m : nat) : (term118 m) = (term5 m).
Proof. exact (eq_refl (term118 m)). Qed.
Lemma lem1004770 (m : nat) : term5 m.
Proof. exact (EQ_MP (@lem1004769 m) (@lem1004768 m)). Qed.
Lemma lem1004772 (m : nat) : term5 m.
Proof. exact (@lem1003901 m (@lem1004770 m)). Qed.
Lemma lem1004773 (m : nat) (h1 : term4 m) : term13.
Proof. exact (@lem1004772 m (@lem1003886 m h1)). Qed.
Lemma lem1004774 (m : nat) (h1 : term4 m) : term9.
Proof. exact (@lem1004773 m h1 (@lem77629)). Qed.
Lemma lem1004775 (m : nat) (h1 : term4 m) : False.
Proof. exact (@lem1004774 m h1 (@lem75543)). Qed.
Lemma lem1004776 (m : nat) (h1 : term4 m) : (term4 m) = False.
Proof. exact (prop_ext (fun h2 : term4 m => @lem1004775 m h1) (fun h2 : False => @lem1003886 m h1)). Qed.
Lemma lem1004777 (m : nat) (h1 : term4 m) : False.
Proof. exact (EQ_MP (@lem1004776 m h1) (@lem1003886 m h1)). Qed.
Lemma lem1004778 (m : nat) : term3 m.
Proof. exact (fun h0 : term4 m => @lem1004777 m h0). Qed.
Lemma lem1004779 (m : nat) : (term1 m) = (term2 m).
Proof. exact (EQ_MP (@lem1003885 m) (@lem1004778 m)). Qed.
Lemma lem1004781 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1004782 (n : nat) : (n = (NUMERAL n)) = (term119 n).
Proof. exact (@lem1004781 (n = (NUMERAL n))). Qed.
Lemma lem1004783 (n : nat) : (term119 n) = (n = (NUMERAL n)).
Proof. exact (SYM (@lem1004782 n)). Qed.
Lemma lem1004784 (n : nat) (h1 : term120 n) : term120 n.
Proof. exact (h1). Qed.
Lemma lem1004787 (n : nat) (h1 : term121 n) : term121 n.
Proof. exact (h1). Qed.
Lemma lem1004788 (n : nat) : term122 n.
Proof. exact (fun h0 : term121 n => @lem1004787 n h0). Qed.
Lemma lem1004789 (n : nat) (h1 : term122 n) : term122 n.
Proof. exact (h1). Qed.
Lemma lem1004790 (n : nat) (h1 : term121 n) : term121 n.
Proof. exact (h1). Qed.
Lemma lem1004791 (n : nat) (h1 : term121 n) (h2 : term122 n) : term121 n.
Proof. exact (@lem1004789 n h2 (@lem1004790 n h1)). Qed.
Lemma lem1004792 (n : nat) (h1 : term121 n) : term123 n.
Proof. exact (fun h0 : term122 n => @lem1004791 n h1 h0). Qed.
Lemma lem1004793 (n : nat) (h1 : term122 n) : term122 n.
Proof. exact (h1). Qed.
Lemma lem1004794 (n : nat) (h1 : term121 n) (h2 : term122 n) : term121 n.
Proof. exact (@lem1004792 n h1 (@lem1004793 n h2)). Qed.
Lemma lem1004795 (n : nat) (h1 : term122 n) : term122 n.
Proof. exact (fun h0 : term121 n => @lem1004794 n h0 h1). Qed.
Lemma lem1004796 (n : nat) : term124 n.
Proof. exact (fun h0 : term122 n => @lem1004795 n h0). Qed.
Lemma lem1004799 (n : nat) : term122 n.
Proof. exact (@lem1004796 n (@lem1004788 n)). Qed.
Lemma lem1004839 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1004840 : term9 = term10.
Proof. exact (@lem1004839 term11). Qed.
Lemma lem1004845 : term12 = term12.
Proof. exact (eq_refl term12). Qed.
Lemma lem1004846 : term13 = term14.
Proof. exact (MK_COMB (@lem1004845) (@lem1004840)). Qed.
Lemma lem1004849 (n : nat) : (term125 n) = (term125 n).
Proof. exact (eq_refl (term125 n)). Qed.
Lemma lem1004850 (n : nat) : (term121 n) = (term126 n).
Proof. exact (MK_COMB (@lem1004849 n) (@lem1004846)). Qed.
Lemma lem1004853 : term127 = term128.
Proof. exact (fun_ext (fun n : nat => @lem1004850 n)). Qed.
Lemma lem1004854 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1004863 : term129 = term130.
Proof. exact (MK_COMB (@lem1004854) (@lem1004853)). Qed.
Lemma lem1004864 (n : nat) : ((NUMERAL n) = n) = ((NUMERAL n) = n).
Proof. exact (eq_refl ((NUMERAL n) = n)). Qed.
Lemma lem1004865 : term21 = term21.
Proof. exact (fun_ext (fun n : nat => @lem1004864 n)). Qed.
Lemma lem1004866 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1004867 : term11 = term11.
Proof. exact (MK_COMB (@lem1004866) (@lem1004865)). Qed.
Lemma lem1004868 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1004869 : term10 = term10.
Proof. exact (MK_COMB (@lem1004868) (@lem1004867)). Qed.
Lemma lem1004870 (m : nat) (n : nat) : ((term22 m n) = (term23 m n)) = ((term22 m n) = (term23 m n)).
Proof. exact (eq_refl ((term22 m n) = (term23 m n))). Qed.
Lemma lem1004871 (m : nat) : (term24 m) = (term24 m).
Proof. exact (fun_ext (fun n : nat => @lem1004870 m n)). Qed.
Lemma lem1004872 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1004873 (m : nat) : (term25 m) = (term25 m).
Proof. exact (MK_COMB (@lem1004872) (@lem1004871 m)). Qed.
Lemma lem1004874 : term26 = term26.
Proof. exact (fun_ext (fun m : nat => @lem1004873 m)). Qed.
Lemma lem1004875 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1004876 : term27 = term27.
Proof. exact (MK_COMB (@lem1004875) (@lem1004874)). Qed.
Lemma lem1004877 (m : nat) (n : nat) : ((term28 m n) = (term23 m n)) = ((term28 m n) = (term23 m n)).
Proof. exact (eq_refl ((term28 m n) = (term23 m n))). Qed.
Lemma lem1004878 (m : nat) : (term29 m) = (term29 m).
Proof. exact (fun_ext (fun n : nat => @lem1004877 m n)). Qed.
Lemma lem1004879 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1004880 (m : nat) : (term30 m) = (term30 m).
Proof. exact (MK_COMB (@lem1004879) (@lem1004878 m)). Qed.
Lemma lem1004881 : term31 = term31.
Proof. exact (fun_ext (fun m : nat => @lem1004880 m)). Qed.
Lemma lem1004882 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1004883 : term32 = term32.
Proof. exact (MK_COMB (@lem1004882) (@lem1004881)). Qed.
Lemma lem1004884 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1004885 : term33 = term33.
Proof. exact (MK_COMB (@lem1004884) (@lem1004883)). Qed.
Lemma lem1004886 : term34 = term34.
Proof. exact (MK_COMB (@lem1004885) (@lem1004876)). Qed.
Lemma lem1004887 (m : nat) : ((term35 m) = m) = ((term35 m) = m).
Proof. exact (eq_refl ((term35 m) = m)). Qed.
Lemma lem1004888 : term36 = term36.
Proof. exact (fun_ext (fun m : nat => @lem1004887 m)). Qed.
Lemma lem1004889 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1004890 : term37 = term37.
Proof. exact (MK_COMB (@lem1004889) (@lem1004888)). Qed.
Lemma lem1004891 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1004892 : term38 = term38.
Proof. exact (MK_COMB (@lem1004891) (@lem1004890)). Qed.
Lemma lem1004893 : term39 = term39.
Proof. exact (MK_COMB (@lem1004892) (@lem1004886)). Qed.
Lemma lem1004894 (n : nat) : ((term40 n) = n) = ((term40 n) = n).
Proof. exact (eq_refl ((term40 n) = n)). Qed.
Lemma lem1004895 : term41 = term41.
Proof. exact (fun_ext (fun n : nat => @lem1004894 n)). Qed.
Lemma lem1004896 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1004897 : term42 = term42.
Proof. exact (MK_COMB (@lem1004896) (@lem1004895)). Qed.
Lemma lem1004898 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1004899 : term43 = term43.
Proof. exact (MK_COMB (@lem1004898) (@lem1004897)). Qed.
Lemma lem1004900 : term44 = term44.
Proof. exact (MK_COMB (@lem1004899) (@lem1004893)). Qed.
Lemma lem1004901 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1004902 : term12 = term12.
Proof. exact (MK_COMB (@lem1004901) (@lem1004900)). Qed.
Lemma lem1004903 : term14 = term14.
Proof. exact (MK_COMB (@lem1004902) (@lem1004869)). Qed.
Lemma lem1004908 (n : nat) : (term125 n) = (term125 n).
Proof. exact (eq_refl (term125 n)). Qed.
Lemma lem1004909 (n : nat) : (term126 n) = (term126 n).
Proof. exact (MK_COMB (@lem1004908 n) (@lem1004903)). Qed.
Lemma lem1004910 : term128 = term128.
Proof. exact (fun_ext (fun n : nat => @lem1004909 n)). Qed.
Lemma lem1004911 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1004912 : term130 = term130.
Proof. exact (MK_COMB (@lem1004911) (@lem1004910)). Qed.
Lemma lem1004973 : term129 = term130.
Proof. exact (TRANS (@lem1004863) (@lem1004912)). Qed.
Lemma lem1004974 : term130 = term129.
Proof. exact (SYM (@lem1004973)). Qed.
Lemma lem1004977 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem1004983 (n : nat) (h1 : term120 n) : term120 n.
Proof. exact (h1). Qed.
Lemma lem1005044 (n : nat) : ((NUMERAL n) = n) = ((NUMERAL n) = n).
Proof. exact (eq_refl ((NUMERAL n) = n)). Qed.
Lemma lem1005045 : term21 = term21.
Proof. exact (fun_ext (fun n : nat => @lem1005044 n)). Qed.
Lemma lem1005046 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1005055 : term11 = term11.
Proof. exact (MK_COMB (@lem1005046) (@lem1005045)). Qed.
Lemma lem1005056 (h1 : term11) : term11.
Proof. exact (EQ_MP (@lem1005055) (@lem1004977 h1)). Qed.
Lemma lem1005066 (n : nat) (h1 : term120 n) : term120 n.
Proof. exact (h1). Qed.
Lemma lem1005157 (n : nat) : ((NUMERAL n) = n) = ((NUMERAL n) = n).
Proof. exact (eq_refl ((NUMERAL n) = n)). Qed.
Lemma lem1005158 : term21 = term21.
Proof. exact (fun_ext (fun n : nat => @lem1005157 n)). Qed.
Lemma lem1005159 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1005160 : term11 = term11.
Proof. exact (MK_COMB (@lem1005159) (@lem1005158)). Qed.
Lemma lem1005161 (h1 : term11) : term11.
Proof. exact (EQ_MP (@lem1005160) (@lem1005056 h1)). Qed.
Lemma lem1005171 (n : nat) (h1 : term120 n) : term120 n.
Proof. exact (h1). Qed.
Lemma lem1005173 (n : nat) : ((NUMERAL n) = n) = ((NUMERAL n) = n).
Proof. exact (eq_refl ((NUMERAL n) = n)). Qed.
Lemma lem1005174 : term21 = term21.
Proof. exact (fun_ext (fun n : nat => @lem1005173 n)). Qed.
Lemma lem1005175 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1005177 : term11 = term11.
Proof. exact (MK_COMB (@lem1005175) (@lem1005174)). Qed.
Lemma lem1005178 (h1 : term11) : term11.
Proof. exact (EQ_MP (@lem1005177) (@lem1005161 h1)). Qed.
Lemma lem1005213 (_16287 : nat) (h1 : term11) : term45 _16287.
Proof. exact (@lem1005178 h1 _16287). Qed.
Lemma lem1005214 (_16287 : nat) : (term45 _16287) = ((NUMERAL _16287) = _16287).
Proof. exact (eq_refl (term45 _16287)). Qed.
Lemma lem1005235 (n : nat) (h1 : term120 n) : term120 n.
Proof. exact (h1). Qed.
Lemma lem1005278 (x : nat) (y : nat) (z : nat) : term54 x y z.
Proof. exact (@lem21385 nat x y z). Qed.
Lemma lem1005280 (_16287 : nat) (h1 : term11) : (NUMERAL _16287) = _16287.
Proof. exact (EQ_MP (@lem1005214 _16287) (@lem1005213 _16287 h1)). Qed.
Lemma lem1005281 (n : nat) (h1 : term11) : (NUMERAL n) = n.
Proof. exact (@lem1005280 n h1). Qed.
Lemma lem1005282 (n : nat) (h1 : term11) : term58 n.
Proof. exact (fun h0 : term59 n => @lem1005281 n h1). Qed.
Lemma lem1005284 (p : Prop) : (term57 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1005285 (n : nat) : (term58 n) = ((NUMERAL n) = n).
Proof. exact (@lem1005284 ((NUMERAL n) = n)). Qed.
Lemma lem1005286 (n : nat) (h1 : term11) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem1005285 n) (@lem1005282 n h1)). Qed.
Lemma lem1005288 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem1005289 (n : nat) : (NUMERAL n) = (NUMERAL n).
Proof. exact (@lem1005288 (NUMERAL n)). Qed.
Lemma lem1005290 (n : nat) : term131 n.
Proof. exact (fun h0 : term132 n => @lem1005289 n). Qed.
Lemma lem1005292 (p : Prop) : (term57 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1005293 (n : nat) : (term131 n) = ((NUMERAL n) = (NUMERAL n)).
Proof. exact (@lem1005292 ((NUMERAL n) = (NUMERAL n))). Qed.
Lemma lem1005294 (n : nat) : (NUMERAL n) = (NUMERAL n).
Proof. exact (EQ_MP (@lem1005293 n) (@lem1005290 n)). Qed.
Lemma lem1005312 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1005313 (y : nat) (x : nat) (z : nat) : (term90 x y z) = (term91 y x z).
Proof. exact (@lem1005312 (y = z) (term61 x z)). Qed.
Lemma lem1005323 (x : nat) (y : nat) : (term62 x y) = (term62 x y).
Proof. exact (eq_refl (term62 x y)). Qed.
Lemma lem1005324 (y : nat) (x : nat) (z : nat) : (term54 x y z) = (term92 y x z).
Proof. exact (MK_COMB (@lem1005323 x y) (@lem1005313 y x z)). Qed.
Lemma lem1005328 (q : Prop) (p : Prop) (r : Prop) : (term64 p q r) = (term64 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1005329 (y : nat) (x : nat) (z : nat) : (term92 y x z) = (term93 y x z).
Proof. exact (@lem1005328 (y = z) (term61 x y) (term61 x z)). Qed.
Lemma lem1005351 (y : nat) (x : nat) (z : nat) : (term54 x y z) = (term93 y x z).
Proof. exact (TRANS (@lem1005324 y x z) (@lem1005329 y x z)). Qed.
Lemma lem1005352 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1005353 (y : nat) (x : nat) (z : nat) : (term94 x y z) = (term95 y x z).
Proof. exact (MK_COMB (@lem1005352) (@lem1005351 y x z)). Qed.
Lemma lem1005375 (y : nat) (x : nat) (z : nat) : (term93 y x z) = (term93 y x z).
Proof. exact (eq_refl (term93 y x z)). Qed.
Lemma lem1005376 (y : nat) (x : nat) (z : nat) : ((term54 x y z) = (term93 y x z)) = ((term93 y x z) = (term93 y x z)).
Proof. exact (MK_COMB (@lem1005353 y x z) (@lem1005375 y x z)). Qed.
Lemma lem1005378 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1005379 (x : Prop) : (x = x) = True.
Proof. exact (@lem1005378 Prop x). Qed.
Lemma lem1005380 (y : nat) (x : nat) (z : nat) : ((term93 y x z) = (term93 y x z)) = True.
Proof. exact (@lem1005379 (term93 y x z)). Qed.
Lemma lem1005381 (y : nat) (x : nat) (z : nat) : ((term54 x y z) = (term93 y x z)) = True.
Proof. exact (TRANS (@lem1005376 y x z) (@lem1005380 y x z)). Qed.
Lemma lem1005382 (y : nat) (x : nat) (z : nat) : True = ((term54 x y z) = (term93 y x z)).
Proof. exact (SYM (@lem1005381 y x z)). Qed.
Lemma lem1005383 (y : nat) (x : nat) (z : nat) : (term54 x y z) = (term93 y x z).
Proof. exact (EQ_MP (@lem1005382 y x z) (@lem0)). Qed.
Lemma lem1005384 (y : nat) (x : nat) (z : nat) : term93 y x z.
Proof. exact (EQ_MP (@lem1005383 y x z) (@lem1005278 x y z)). Qed.
Lemma lem1005386 (b : Prop) (a : Prop) : (a \/ b) = (term68 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1005387 (x : nat) (y : nat) (z : nat) : (term93 y x z) = (term96 x y z).
Proof. exact (@lem1005386 (term97 y x z) (y = z)). Qed.
Lemma lem1005389 (a : Prop) (b : Prop) : (term71 a b) = (term72 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1005390 (y : nat) (x : nat) (z : nat) : (term98 y x z) = (term99 y x z).
Proof. exact (@lem1005389 (term61 x y) (term61 x z)). Qed.
Lemma lem1005392 (a : Prop) : (term75 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1005393 (x : nat) (y : nat) : (term76 x y) = (x = y).
Proof. exact (@lem1005392 (x = y)). Qed.
Lemma lem1005394 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1005395 (x : nat) (y : nat) : (term77 x y) = (term78 x y).
Proof. exact (MK_COMB (@lem1005394) (@lem1005393 x y)). Qed.
Lemma lem1005397 (a : Prop) : (term75 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1005398 (x : nat) (z : nat) : (term76 x z) = (x = z).
Proof. exact (@lem1005397 (x = z)). Qed.
Lemma lem1005399 (y : nat) (x : nat) (z : nat) : (term99 y x z) = (term100 y x z).
Proof. exact (MK_COMB (@lem1005395 x y) (@lem1005398 x z)). Qed.
Lemma lem1005400 (y : nat) (x : nat) (z : nat) : (term98 y x z) = (term100 y x z).
Proof. exact (TRANS (@lem1005390 y x z) (@lem1005399 y x z)). Qed.
Lemma lem1005401 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1005402 (y : nat) (x : nat) (z : nat) : (term101 y x z) = (term102 y x z).
Proof. exact (MK_COMB (@lem1005401) (@lem1005400 y x z)). Qed.
Lemma lem1005403 (y : nat) (z : nat) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1005404 (x : nat) (y : nat) (z : nat) : (term96 x y z) = (term103 x y z).
Proof. exact (MK_COMB (@lem1005402 y x z) (@lem1005403 y z)). Qed.
Lemma lem1005405 (x : nat) (y : nat) (z : nat) : (term93 y x z) = (term103 x y z).
Proof. exact (TRANS (@lem1005387 x y z) (@lem1005404 x y z)). Qed.
Lemma lem1005407 (n : nat) (h1 : term11) : term133 n.
Proof. exact (conj (@lem1005286 n h1) (@lem1005294 n)). Qed.
Lemma lem1005409 (x : nat) (y : nat) (z : nat) : term103 x y z.
Proof. exact (EQ_MP (@lem1005405 x y z) (@lem1005384 y x z)). Qed.
Lemma lem1005410 (n : nat) : term134 n.
Proof. exact (@lem1005409 (NUMERAL n) n (NUMERAL n)). Qed.
Lemma lem1005413 (n : nat) (h1 : term11) : n = (NUMERAL n).
Proof. exact (@lem1005410 n (@lem1005407 n h1)). Qed.
Lemma lem1005414 (n : nat) (h1 : term11) : term135 n.
Proof. exact (fun h0 : term120 n => @lem1005413 n h1). Qed.
Lemma lem1005416 (p : Prop) : (term57 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1005417 (n : nat) : (term135 n) = (n = (NUMERAL n)).
Proof. exact (@lem1005416 (n = (NUMERAL n))). Qed.
Lemma lem1005418 (n : nat) (h1 : term11) : n = (NUMERAL n).
Proof. exact (EQ_MP (@lem1005417 n) (@lem1005414 n h1)). Qed.
Lemma lem1005421 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1005423 (n : nat) : (term120 n) = (term136 n).
Proof. exact (@lem1005421 (n = (NUMERAL n))). Qed.
Lemma lem1005426 (n : nat) (h1 : term120 n) : term136 n.
Proof. exact (EQ_MP (@lem1005423 n) (@lem1005235 n h1)). Qed.
Lemma lem1005429 (n : nat) (h1 : term11) (h2 : term120 n) : False.
Proof. exact (@lem1005426 n h2 (@lem1005418 n h1)). Qed.
Lemma lem1005430 (n : nat) (h1 : term11) (h2 : term120 n) : term117.
Proof. exact (fun h0 : ~ False => @lem1005429 n h1 h2). Qed.
Lemma lem1005432 (p : Prop) : (term57 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1005433 : term117 = False.
Proof. exact (@lem1005432 False). Qed.
Lemma lem1005434 (n : nat) (h1 : term11) (h2 : term120 n) : False.
Proof. exact (EQ_MP (@lem1005433) (@lem1005430 n h1 h2)). Qed.
Lemma lem1005435 (n : nat) (h1 : term11) (h2 : term120 n) : (term120 n) = False.
Proof. exact (prop_ext (fun h3 : term120 n => @lem1005434 n h1 h2) (fun h3 : False => @lem1005235 n h2)). Qed.
Lemma lem1005436 (n : nat) (h1 : term11) (h2 : term120 n) : False.
Proof. exact (EQ_MP (@lem1005435 n h1 h2) (@lem1005235 n h2)). Qed.
Lemma lem1005437 (n : nat) (h1 : term11) (h2 : term120 n) : (term120 n) = False.
Proof. exact (prop_ext (fun h3 : term120 n => @lem1005436 n h1 h2) (fun h3 : False => @lem1005171 n h2)). Qed.
Lemma lem1005438 (n : nat) (h1 : term11) (h2 : term120 n) : False.
Proof. exact (EQ_MP (@lem1005437 n h1 h2) (@lem1005171 n h2)). Qed.
Lemma lem1005439 (n : nat) (h1 : term11) (h2 : term120 n) : term11 = False.
Proof. exact (prop_ext (fun h3 : term11 => @lem1005438 n h1 h2) (fun h3 : False => @lem1005178 h1)). Qed.
Lemma lem1005440 (n : nat) (h1 : term11) (h2 : term120 n) : False.
Proof. exact (EQ_MP (@lem1005439 n h1 h2) (@lem1005178 h1)). Qed.
Lemma lem1005441 (n : nat) (h1 : term11) (h2 : term120 n) : (term120 n) = False.
Proof. exact (prop_ext (fun h3 : term120 n => @lem1005440 n h1 h2) (fun h3 : False => @lem1005171 n h2)). Qed.
Lemma lem1005442 (n : nat) (h1 : term11) (h2 : term120 n) : False.
Proof. exact (EQ_MP (@lem1005441 n h1 h2) (@lem1005171 n h2)). Qed.
Lemma lem1005443 (n : nat) (h1 : term11) (h2 : term120 n) : term11 = False.
Proof. exact (prop_ext (fun h3 : term11 => @lem1005442 n h1 h2) (fun h3 : False => @lem1005161 h1)). Qed.
Lemma lem1005444 (n : nat) (h1 : term11) (h2 : term120 n) : False.
Proof. exact (EQ_MP (@lem1005443 n h1 h2) (@lem1005161 h1)). Qed.
Lemma lem1005445 (n : nat) (h1 : term11) (h2 : term120 n) : (term120 n) = False.
Proof. exact (prop_ext (fun h3 : term120 n => @lem1005444 n h1 h2) (fun h3 : False => @lem1005066 n h2)). Qed.
Lemma lem1005446 (n : nat) (h1 : term11) (h2 : term120 n) : False.
Proof. exact (EQ_MP (@lem1005445 n h1 h2) (@lem1005066 n h2)). Qed.
Lemma lem1005447 (n : nat) (h1 : term11) (h2 : term120 n) : term11 = False.
Proof. exact (prop_ext (fun h3 : term11 => @lem1005446 n h1 h2) (fun h3 : False => @lem1005056 h1)). Qed.
Lemma lem1005448 (n : nat) (h1 : term11) (h2 : term120 n) : False.
Proof. exact (EQ_MP (@lem1005447 n h1 h2) (@lem1005056 h1)). Qed.
Lemma lem1005449 (n : nat) (h1 : term11) (h2 : term120 n) : (term120 n) = False.
Proof. exact (prop_ext (fun h3 : term120 n => @lem1005448 n h1 h2) (fun h3 : False => @lem1004983 n h2)). Qed.
Lemma lem1005450 (n : nat) (h1 : term11) (h2 : term120 n) : False.
Proof. exact (EQ_MP (@lem1005449 n h1 h2) (@lem1004983 n h2)). Qed.
Lemma lem1005451 (n : nat) (h1 : term120 n) : term9.
Proof. exact (fun h0 : term11 => @lem1005450 n h0 h1). Qed.
Lemma lem1005452 : term9 = term10.
Proof. exact (@lem69 term11). Qed.
Lemma lem1005453 (n : nat) (h1 : term120 n) : term10.
Proof. exact (EQ_MP (@lem1005452) (@lem1005451 n h1)). Qed.
Lemma lem1005454 (n : nat) (h1 : term120 n) : term14.
Proof. exact (fun h0 : term44 => @lem1005453 n h1). Qed.
Lemma lem1005455 (n : nat) : term126 n.
Proof. exact (fun h0 : term120 n => @lem1005454 n h0). Qed.
Lemma lem1005460 : term130.
Proof. exact (fun n : nat => @lem1005455 n). Qed.
Lemma lem1005461 : term129.
Proof. exact (EQ_MP (@lem1004974) (@lem1005460)). Qed.
Lemma lem1005462 (n : nat) : term137 n.
Proof. exact (@lem1005461 n). Qed.
Lemma lem1005463 (n : nat) : (term137 n) = (term121 n).
Proof. exact (eq_refl (term137 n)). Qed.
Lemma lem1005464 (n : nat) : term121 n.
Proof. exact (EQ_MP (@lem1005463 n) (@lem1005462 n)). Qed.
Lemma lem1005466 (n : nat) : term121 n.
Proof. exact (@lem1004799 n (@lem1005464 n)). Qed.
Lemma lem1005467 (n : nat) (h1 : term120 n) : term13.
Proof. exact (@lem1005466 n (@lem1004784 n h1)). Qed.
Lemma lem1005468 (n : nat) (h1 : term120 n) : term9.
Proof. exact (@lem1005467 n h1 (@lem77629)). Qed.
Lemma lem1005469 (n : nat) (h1 : term120 n) : False.
Proof. exact (@lem1005468 n h1 (@lem75543)). Qed.
Lemma lem1005470 (n : nat) (h1 : term120 n) : (term120 n) = False.
Proof. exact (prop_ext (fun h2 : term120 n => @lem1005469 n h1) (fun h2 : False => @lem1004784 n h1)). Qed.
Lemma lem1005471 (n : nat) (h1 : term120 n) : False.
Proof. exact (EQ_MP (@lem1005470 n h1) (@lem1004784 n h1)). Qed.
Lemma lem1005472 (n : nat) : term119 n.
Proof. exact (fun h0 : term120 n => @lem1005471 n h0). Qed.
Lemma lem1005473 (n : nat) : n = (NUMERAL n).
Proof. exact (EQ_MP (@lem1004783 n) (@lem1005472 n)). Qed.
Lemma lem1005474 (m : nat) : (term138 m) = (term139 m).
Proof. exact (MK_COMB (@lem1003881) (@lem1004779 m)). Qed.
Lemma lem1005477 (m : nat) (n : nat) : ((term1 m) = n) = ((term2 m) = (NUMERAL n)).
Proof. exact (MK_COMB (@lem1005474 m) (@lem1005473 n)). Qed.
