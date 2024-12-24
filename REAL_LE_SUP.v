Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LE_SUP_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import MEMBER_NOT_EMPTY_spec.
Require Import SUP_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1339577_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm18964_spec.
Require Import thm18965_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm19030_spec.
Require Import thm19031_spec.
Require Import thm19490_spec.
Require Import thm19699_spec.
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
Require Import thm69_spec.
Lemma lem5180945 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem5180946 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem5180947 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem5180946 t1) (@lem5180945 t1)). Qed.
Lemma lem5180948 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem5180947 t1 t2). Qed.
Lemma lem5180949 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem5180950 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem5180949 t1 t2) (@lem5180948 t1 t2)). Qed.
Lemma lem5180951 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem5180950 t1 t2 t3). Qed.
Lemma lem5180952 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem5180953 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem5180952 t1 t2 t3) (@lem5180951 t1 t2 t3)). Qed.
Lemma lem5180954 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem5180953 t1 t2 t3)). Qed.
Lemma lem5180956 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5180957 : term8 = term9.
Proof. exact (@lem5180956 term8). Qed.
Lemma lem5180958 : term9 = term8.
Proof. exact (SYM (@lem5180957)). Qed.
Lemma lem5180959 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem5180960 : term11.
Proof. exact (@lem3216368 real). Qed.
Lemma lem5180965 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem5180966 : term13.
Proof. exact (fun h0 : term12 => @lem5180965 h0). Qed.
Lemma lem5180967 (h1 : term13) : term13.
Proof. exact (h1). Qed.
Lemma lem5180968 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem5180969 (h1 : term12) (h2 : term13) : term12.
Proof. exact (@lem5180967 h2 (@lem5180968 h1)). Qed.
Lemma lem5180970 (h1 : term12) : term14.
Proof. exact (fun h0 : term13 => @lem5180969 h1 h0). Qed.
Lemma lem5180971 (h1 : term13) : term13.
Proof. exact (h1). Qed.
Lemma lem5180972 (h1 : term12) (h2 : term13) : term12.
Proof. exact (@lem5180970 h1 (@lem5180971 h2)). Qed.
Lemma lem5180973 (h1 : term13) : term13.
Proof. exact (fun h0 : term12 => @lem5180972 h0 h1). Qed.
Lemma lem5180974 : term15.
Proof. exact (fun h0 : term13 => @lem5180973 h0). Qed.
Lemma lem5180977 : term13.
Proof. exact (@lem5180974 (@lem5180966)). Qed.
Lemma lem5181037 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5181038 : term16 = term17.
Proof. exact (@lem5181037 term18). Qed.
Lemma lem5181077 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem5181078 : term20 = term21.
Proof. exact (MK_COMB (@lem5181077) (@lem5181038)). Qed.
Lemma lem5181081 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem5181082 : term23 = term24.
Proof. exact (MK_COMB (@lem5181081) (@lem5181078)). Qed.
Lemma lem5181085 : term25 = term25.
Proof. exact (eq_refl term25). Qed.
Lemma lem5181092 : term12 = term26.
Proof. exact (MK_COMB (@lem5181085) (@lem5181082)). Qed.
Lemma lem5181093 (s : real -> Prop) (b : real) : (term27 s b) = (term27 s b).
Proof. exact (eq_refl (term27 s b)). Qed.
Lemma lem5181098 (s : real -> Prop) (x : real) (b : real) : (term28 s x b) = (term28 s x b).
Proof. exact (eq_refl (term28 s x b)). Qed.
Lemma lem5181099 (s : real -> Prop) (b : real) : (term29 s b) = (term29 s b).
Proof. exact (fun_ext (fun x : real => @lem5181098 s x b)). Qed.
Lemma lem5181100 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5181101 (s : real -> Prop) (b : real) : (term30 s b) = (term30 s b).
Proof. exact (MK_COMB (@lem5181100) (@lem5181099 s b)). Qed.
Lemma lem5181102 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5181103 (s : real -> Prop) (b : real) : (term31 s b) = (term31 s b).
Proof. exact (MK_COMB (@lem5181102) (@lem5181101 s b)). Qed.
Lemma lem5181104 (s : real -> Prop) (b : real) : (term32 s b) = (term32 s b).
Proof. exact (MK_COMB (@lem5181103 s b) (@lem5181093 s b)). Qed.
Lemma lem5181105 (s : real -> Prop) : (term33 s) = (term33 s).
Proof. exact (fun_ext (fun b : real => @lem5181104 s b)). Qed.
Lemma lem5181106 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5181107 (s : real -> Prop) : (term34 s) = (term34 s).
Proof. exact (MK_COMB (@lem5181106) (@lem5181105 s)). Qed.
Lemma lem5181112 (x : real) (s : real -> Prop) : (term35 x s) = (term35 x s).
Proof. exact (eq_refl (term35 x s)). Qed.
Lemma lem5181113 (s : real -> Prop) : (term36 s) = (term36 s).
Proof. exact (fun_ext (fun x : real => @lem5181112 x s)). Qed.
Lemma lem5181114 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5181115 (s : real -> Prop) : (term37 s) = (term37 s).
Proof. exact (MK_COMB (@lem5181114) (@lem5181113 s)). Qed.
Lemma lem5181116 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5181117 (s : real -> Prop) : (term38 s) = (term38 s).
Proof. exact (MK_COMB (@lem5181116) (@lem5181115 s)). Qed.
Lemma lem5181118 (s : real -> Prop) : (term39 s) = (term39 s).
Proof. exact (MK_COMB (@lem5181117 s) (@lem5181107 s)). Qed.
Lemma lem5181123 (s : real -> Prop) (x : real) (b : real) : (term28 s x b) = (term28 s x b).
Proof. exact (eq_refl (term28 s x b)). Qed.
Lemma lem5181124 (s : real -> Prop) (b : real) : (term29 s b) = (term29 s b).
Proof. exact (fun_ext (fun x : real => @lem5181123 s x b)). Qed.
Lemma lem5181125 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5181126 (s : real -> Prop) (b : real) : (term30 s b) = (term30 s b).
Proof. exact (MK_COMB (@lem5181125) (@lem5181124 s b)). Qed.
Lemma lem5181127 (s : real -> Prop) : (term40 s) = (term40 s).
Proof. exact (fun_ext (fun b : real => @lem5181126 s b)). Qed.
Lemma lem5181128 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5181129 (s : real -> Prop) : (term41 s) = (term41 s).
Proof. exact (MK_COMB (@lem5181128) (@lem5181127 s)). Qed.
Lemma lem5181134 (s : real -> Prop) : (term42 s) = (term42 s).
Proof. exact (eq_refl (term42 s)). Qed.
Lemma lem5181135 (s : real -> Prop) : (term43 s) = (term43 s).
Proof. exact (MK_COMB (@lem5181134 s) (@lem5181129 s)). Qed.
Lemma lem5181136 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5181137 (s : real -> Prop) : (term44 s) = (term44 s).
Proof. exact (MK_COMB (@lem5181136) (@lem5181135 s)). Qed.
Lemma lem5181138 (s : real -> Prop) : (term45 s) = (term45 s).
Proof. exact (MK_COMB (@lem5181137 s) (@lem5181118 s)). Qed.
Lemma lem5181139 : term46 = term46.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5181138 s)). Qed.
Lemma lem5181140 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5181141 : term18 = term18.
Proof. exact (MK_COMB (@lem5181140) (@lem5181139)). Qed.
Lemma lem5181142 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5181143 : term17 = term17.
Proof. exact (MK_COMB (@lem5181142) (@lem5181141)). Qed.
Lemma lem5181146 (s : real -> Prop) : (term47 s) = (term47 s).
Proof. exact (eq_refl (term47 s)). Qed.
Lemma lem5181147 (x : real) (s : real -> Prop) : (@IN real x s) = (@IN real x s).
Proof. exact (eq_refl (@IN real x s)). Qed.
Lemma lem5181148 (s : real -> Prop) : (term48 s) = (term48 s).
Proof. exact (fun_ext (fun x : real => @lem5181147 x s)). Qed.
Lemma lem5181149 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5181150 (s : real -> Prop) : (term49 s) = (term49 s).
Proof. exact (MK_COMB (@lem5181149) (@lem5181148 s)). Qed.
Lemma lem5181151 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5181152 (s : real -> Prop) : (term50 s) = (term50 s).
Proof. exact (MK_COMB (@lem5181151) (@lem5181150 s)). Qed.
Lemma lem5181153 (s : real -> Prop) : ((term49 s) = (term47 s)) = ((term49 s) = (term47 s)).
Proof. exact (MK_COMB (@lem5181152 s) (@lem5181146 s)). Qed.
Lemma lem5181154 : term51 = term51.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5181153 s)). Qed.
Lemma lem5181155 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5181156 : term11 = term11.
Proof. exact (MK_COMB (@lem5181155) (@lem5181154)). Qed.
Lemma lem5181157 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5181158 : term19 = term19.
Proof. exact (MK_COMB (@lem5181157) (@lem5181156)). Qed.
Lemma lem5181159 : term21 = term21.
Proof. exact (MK_COMB (@lem5181158) (@lem5181143)). Qed.
Lemma lem5181168 (y : real) (x : real) (z : real) : (term52 y x z) = (term52 y x z).
Proof. exact (eq_refl (term52 y x z)). Qed.
Lemma lem5181169 (y : real) (x : real) : (term53 y x) = (term53 y x).
Proof. exact (fun_ext (fun z : real => @lem5181168 y x z)). Qed.
Lemma lem5181170 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5181171 (y : real) (x : real) : (term54 y x) = (term54 y x).
Proof. exact (MK_COMB (@lem5181170) (@lem5181169 y x)). Qed.
Lemma lem5181172 (x : real) : (term55 x) = (term55 x).
Proof. exact (fun_ext (fun y : real => @lem5181171 y x)). Qed.
Lemma lem5181173 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5181174 (x : real) : (term56 x) = (term56 x).
Proof. exact (MK_COMB (@lem5181173) (@lem5181172 x)). Qed.
Lemma lem5181175 : term57 = term57.
Proof. exact (fun_ext (fun x : real => @lem5181174 x)). Qed.
Lemma lem5181176 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5181177 : term58 = term58.
Proof. exact (MK_COMB (@lem5181176) (@lem5181175)). Qed.
Lemma lem5181178 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5181179 : term22 = term22.
Proof. exact (MK_COMB (@lem5181178) (@lem5181177)). Qed.
Lemma lem5181180 : term24 = term24.
Proof. exact (MK_COMB (@lem5181179) (@lem5181159)). Qed.
Lemma lem5181181 (a : real) (s : real -> Prop) : (term59 a s) = (term59 a s).
Proof. exact (eq_refl (term59 a s)). Qed.
Lemma lem5181186 (s : real -> Prop) (x : real) (b : real) : (term28 s x b) = (term28 s x b).
Proof. exact (eq_refl (term28 s x b)). Qed.
Lemma lem5181187 (s : real -> Prop) (b : real) : (term29 s b) = (term29 s b).
Proof. exact (fun_ext (fun x : real => @lem5181186 s x b)). Qed.
Lemma lem5181188 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5181189 (s : real -> Prop) (b : real) : (term30 s b) = (term30 s b).
Proof. exact (MK_COMB (@lem5181188) (@lem5181187 s b)). Qed.
Lemma lem5181192 (a : real) (y : real) : (term60 a y) = (term60 a y).
Proof. exact (eq_refl (term60 a y)). Qed.
Lemma lem5181193 (a : real) (y : real) (s : real -> Prop) (b : real) : (term61 a y s b) = (term61 a y s b).
Proof. exact (MK_COMB (@lem5181192 a y) (@lem5181189 s b)). Qed.
Lemma lem5181196 (y : real) (s : real -> Prop) : (term62 y s) = (term62 y s).
Proof. exact (eq_refl (term62 y s)). Qed.
Lemma lem5181197 (a : real) (y : real) (s : real -> Prop) (b : real) : (term63 a y s b) = (term63 a y s b).
Proof. exact (MK_COMB (@lem5181196 y s) (@lem5181193 a y s b)). Qed.
Lemma lem5181198 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5181199 (a : real) (y : real) (s : real -> Prop) (b : real) : (term64 a y s b) = (term64 a y s b).
Proof. exact (MK_COMB (@lem5181198) (@lem5181197 a y s b)). Qed.
Lemma lem5181200 (y : real) (b : real) (a : real) (s : real -> Prop) : (term65 y b a s) = (term65 y b a s).
Proof. exact (MK_COMB (@lem5181199 a y s b) (@lem5181181 a s)). Qed.
Lemma lem5181201 (b : real) (a : real) (s : real -> Prop) : (term66 b a s) = (term66 b a s).
Proof. exact (fun_ext (fun y : real => @lem5181200 y b a s)). Qed.
Lemma lem5181202 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5181203 (b : real) (a : real) (s : real -> Prop) : (term67 b a s) = (term67 b a s).
Proof. exact (MK_COMB (@lem5181202) (@lem5181201 b a s)). Qed.
Lemma lem5181204 (a : real) (s : real -> Prop) : (term68 a s) = (term68 a s).
Proof. exact (fun_ext (fun b : real => @lem5181203 b a s)). Qed.
Lemma lem5181205 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5181206 (a : real) (s : real -> Prop) : (term69 a s) = (term69 a s).
Proof. exact (MK_COMB (@lem5181205) (@lem5181204 a s)). Qed.
Lemma lem5181207 (s : real -> Prop) : (term70 s) = (term70 s).
Proof. exact (fun_ext (fun a : real => @lem5181206 a s)). Qed.
Lemma lem5181208 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5181209 (s : real -> Prop) : (term71 s) = (term71 s).
Proof. exact (MK_COMB (@lem5181208) (@lem5181207 s)). Qed.
Lemma lem5181210 : term72 = term72.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5181209 s)). Qed.
Lemma lem5181211 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5181212 : term8 = term8.
Proof. exact (MK_COMB (@lem5181211) (@lem5181210)). Qed.
Lemma lem5181213 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5181214 : term10 = term10.
Proof. exact (MK_COMB (@lem5181213) (@lem5181212)). Qed.
Lemma lem5181215 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5181216 : term25 = term25.
Proof. exact (MK_COMB (@lem5181215) (@lem5181214)). Qed.
Lemma lem5181217 : term26 = term26.
Proof. exact (MK_COMB (@lem5181216) (@lem5181180)). Qed.
Lemma lem5181348 : term12 = term26.
Proof. exact (TRANS (@lem5181092) (@lem5181217)). Qed.
Lemma lem5181349 : term26 = term12.
Proof. exact (SYM (@lem5181348)). Qed.
Lemma lem5181350 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem5181351 (h1 : term58) : term58.
Proof. exact (h1). Qed.
Lemma lem5181352 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem5181353 (h1 : term18) : term18.
Proof. exact (h1). Qed.
Lemma lem5181362 (s : real -> Prop) (x : real) (b : real) : (term28 s x b) = (term73 s x b).
Proof. exact (@lem17265 (@IN real x s) (real_le x b)). Qed.
Lemma lem5181363 (s : real -> Prop) (b : real) : (term29 s b) = (term74 s b).
Proof. exact (fun_ext (fun x : real => @lem5181362 s x b)). Qed.
Lemma lem5181364 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5181365 (s : real -> Prop) (b : real) : (term30 s b) = (term75 s b).
Proof. exact (MK_COMB (@lem5181364) (@lem5181363 s b)). Qed.
Lemma lem5181367 (a : real) (y : real) : (term60 a y) = (term60 a y).
Proof. exact (eq_refl (term60 a y)). Qed.
Lemma lem5181368 (a : real) (y : real) (s : real -> Prop) (b : real) : (term61 a y s b) = (term76 a y s b).
Proof. exact (MK_COMB (@lem5181367 a y) (@lem5181365 s b)). Qed.
Lemma lem5181370 (y : real) (s : real -> Prop) : (term62 y s) = (term62 y s).
Proof. exact (eq_refl (term62 y s)). Qed.
Lemma lem5181371 (a : real) (y : real) (s : real -> Prop) (b : real) : (term63 a y s b) = (term77 a y s b).
Proof. exact (MK_COMB (@lem5181370 y s) (@lem5181368 a y s b)). Qed.
Lemma lem5181372 (a : real) (s : real -> Prop) : (term78 a s) = (term78 a s).
Proof. exact (eq_refl (term78 a s)). Qed.
Lemma lem5181373 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5181374 (a : real) (y : real) (s : real -> Prop) (b : real) : (term79 a y s b) = (term80 a y s b).
Proof. exact (MK_COMB (@lem5181373) (@lem5181371 a y s b)). Qed.
Lemma lem5181375 (y : real) (b : real) (a : real) (s : real -> Prop) : (term81 y b a s) = (term82 y b a s).
Proof. exact (MK_COMB (@lem5181374 a y s b) (@lem5181372 a s)). Qed.
Lemma lem5181376 (y : real) (b : real) (a : real) (s : real -> Prop) : (term83 y b a s) = (term81 y b a s).
Proof. exact (@lem17362 (term63 a y s b) (term59 a s)). Qed.
Lemma lem5181377 (y : real) (b : real) (a : real) (s : real -> Prop) : (term83 y b a s) = (term82 y b a s).
Proof. exact (TRANS (@lem5181376 y b a s) (@lem5181375 y b a s)). Qed.
Lemma lem5181378 (P : real -> Prop) : (term84 P) = (term85 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5181379 (b : real) (a : real) (s : real -> Prop) : (term86 b a s) = (term87 b a s).
Proof. exact (@lem5181378 (term66 b a s)). Qed.
Lemma lem5181380 (y : real) (b : real) (a : real) (s : real -> Prop) : (term88 b a s y) = (term65 y b a s).
Proof. exact (eq_refl (term88 b a s y)). Qed.
Lemma lem5181381 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5181382 (y : real) (b : real) (a : real) (s : real -> Prop) : (term89 b a s y) = (term83 y b a s).
Proof. exact (MK_COMB (@lem5181381) (@lem5181380 y b a s)). Qed.
Lemma lem5181383 (y : real) (b : real) (a : real) (s : real -> Prop) : (term89 b a s y) = (term82 y b a s).
Proof. exact (TRANS (@lem5181382 y b a s) (@lem5181377 y b a s)). Qed.
Lemma lem5181384 (b : real) (a : real) (s : real -> Prop) : (term90 b a s) = (term91 b a s).
Proof. exact (fun_ext (fun y : real => @lem5181383 y b a s)). Qed.
Lemma lem5181385 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5181386 (b : real) (a : real) (s : real -> Prop) : (term87 b a s) = (term92 b a s).
Proof. exact (MK_COMB (@lem5181385) (@lem5181384 b a s)). Qed.
Lemma lem5181387 (b : real) (a : real) (s : real -> Prop) : (term86 b a s) = (term92 b a s).
Proof. exact (TRANS (@lem5181379 b a s) (@lem5181386 b a s)). Qed.
Lemma lem5181388 (P : real -> Prop) : (term84 P) = (term85 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5181389 (a : real) (s : real -> Prop) : (term93 a s) = (term94 a s).
Proof. exact (@lem5181388 (term68 a s)). Qed.
Lemma lem5181390 (b : real) (a : real) (s : real -> Prop) : (term95 a s b) = (term67 b a s).
Proof. exact (eq_refl (term95 a s b)). Qed.
Lemma lem5181391 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5181392 (b : real) (a : real) (s : real -> Prop) : (term96 a s b) = (term86 b a s).
Proof. exact (MK_COMB (@lem5181391) (@lem5181390 b a s)). Qed.
Lemma lem5181393 (b : real) (a : real) (s : real -> Prop) : (term96 a s b) = (term92 b a s).
Proof. exact (TRANS (@lem5181392 b a s) (@lem5181387 b a s)). Qed.
Lemma lem5181394 (a : real) (s : real -> Prop) : (term97 a s) = (term98 a s).
Proof. exact (fun_ext (fun b : real => @lem5181393 b a s)). Qed.
Lemma lem5181395 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5181396 (a : real) (s : real -> Prop) : (term94 a s) = (term99 a s).
Proof. exact (MK_COMB (@lem5181395) (@lem5181394 a s)). Qed.
Lemma lem5181397 (a : real) (s : real -> Prop) : (term93 a s) = (term99 a s).
Proof. exact (TRANS (@lem5181389 a s) (@lem5181396 a s)). Qed.
Lemma lem5181398 (P : real -> Prop) : (term84 P) = (term85 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5181399 (s : real -> Prop) : (term100 s) = (term101 s).
Proof. exact (@lem5181398 (term70 s)). Qed.
Lemma lem5181400 (a : real) (s : real -> Prop) : (term102 s a) = (term69 a s).
Proof. exact (eq_refl (term102 s a)). Qed.
Lemma lem5181401 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5181402 (a : real) (s : real -> Prop) : (term103 s a) = (term93 a s).
Proof. exact (MK_COMB (@lem5181401) (@lem5181400 a s)). Qed.
Lemma lem5181403 (a : real) (s : real -> Prop) : (term103 s a) = (term99 a s).
Proof. exact (TRANS (@lem5181402 a s) (@lem5181397 a s)). Qed.
Lemma lem5181404 (s : real -> Prop) : (term104 s) = (term105 s).
Proof. exact (fun_ext (fun a : real => @lem5181403 a s)). Qed.
Lemma lem5181405 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5181406 (s : real -> Prop) : (term101 s) = (term106 s).
Proof. exact (MK_COMB (@lem5181405) (@lem5181404 s)). Qed.
Lemma lem5181407 (s : real -> Prop) : (term100 s) = (term106 s).
Proof. exact (TRANS (@lem5181399 s) (@lem5181406 s)). Qed.
Lemma lem5181408 (P : type1022) : (term107 P) = (term108 P).
Proof. exact (@lem18392 (real -> Prop) P). Qed.
Lemma lem5181409 : term10 = term109.
Proof. exact (@lem5181408 term72). Qed.
Lemma lem5181410 (s : real -> Prop) : (term110 s) = (term71 s).
Proof. exact (eq_refl (term110 s)). Qed.
Lemma lem5181411 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5181412 (s : real -> Prop) : (term111 s) = (term100 s).
Proof. exact (MK_COMB (@lem5181411) (@lem5181410 s)). Qed.
Lemma lem5181413 (s : real -> Prop) : (term111 s) = (term106 s).
Proof. exact (TRANS (@lem5181412 s) (@lem5181407 s)). Qed.
Lemma lem5181414 : term112 = term113.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5181413 s)). Qed.
Lemma lem5181415 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5181416 : term109 = term114.
Proof. exact (MK_COMB (@lem5181415) (@lem5181414)). Qed.
Lemma lem5181417 : term10 = term114.
Proof. exact (TRANS (@lem5181409) (@lem5181416)). Qed.
Lemma lem5181451 {A : Type'} (P : A -> Prop) (Q : Prop) : (term115 A P Q) = (term116 A P Q).
Proof. exact (EQ_MP (@lem18965 A P Q) (@lem18964 A P Q)). Qed.
Lemma lem5181452 (P : real -> Prop) (Q : Prop) : (term117 P Q) = (term118 P Q).
Proof. exact (@lem5181451 real P Q). Qed.
Lemma lem5181453 (b : real) (a : real) (s : real -> Prop) : (term119 b a s) = (term120 b a s).
Proof. exact (@lem5181452 (term121 a s b) (term78 a s)). Qed.
Lemma lem5181454 (a : real) (y : real) (s : real -> Prop) (b : real) : (term122 a s b y) = (term77 a y s b).
Proof. exact (eq_refl (term122 a s b y)). Qed.
Lemma lem5181455 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5181456 (a : real) (y : real) (s : real -> Prop) (b : real) : (term123 a s b y) = (term80 a y s b).
Proof. exact (MK_COMB (@lem5181455) (@lem5181454 a y s b)). Qed.
Lemma lem5181457 (a : real) (s : real -> Prop) : (term78 a s) = (term78 a s).
Proof. exact (eq_refl (term78 a s)). Qed.
Lemma lem5181458 (y : real) (b : real) (a : real) (s : real -> Prop) : (term124 b y a s) = (term82 y b a s).
Proof. exact (MK_COMB (@lem5181456 a y s b) (@lem5181457 a s)). Qed.
Lemma lem5181459 (b : real) (a : real) (s : real -> Prop) : (term125 b a s) = (term91 b a s).
Proof. exact (fun_ext (fun y : real => @lem5181458 y b a s)). Qed.
Lemma lem5181460 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5181461 (b : real) (a : real) (s : real -> Prop) : (term119 b a s) = (term92 b a s).
Proof. exact (MK_COMB (@lem5181460) (@lem5181459 b a s)). Qed.
Lemma lem5181462 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5181463 (b : real) (a : real) (s : real -> Prop) : (term126 b a s) = (term127 b a s).
Proof. exact (MK_COMB (@lem5181462) (@lem5181461 b a s)). Qed.
Lemma lem5181464 (a : real) (y : real) (s : real -> Prop) (b : real) : (term122 a s b y) = (term77 a y s b).
Proof. exact (eq_refl (term122 a s b y)). Qed.
Lemma lem5181465 (a : real) (s : real -> Prop) (b : real) : (term128 a s b) = (term121 a s b).
Proof. exact (fun_ext (fun y : real => @lem5181464 a y s b)). Qed.
Lemma lem5181466 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5181467 (a : real) (s : real -> Prop) (b : real) : (term129 a s b) = (term130 a s b).
Proof. exact (MK_COMB (@lem5181466) (@lem5181465 a s b)). Qed.
Lemma lem5181468 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5181469 (a : real) (s : real -> Prop) (b : real) : (term131 a s b) = (term132 a s b).
Proof. exact (MK_COMB (@lem5181468) (@lem5181467 a s b)). Qed.
Lemma lem5181470 (a : real) (s : real -> Prop) : (term78 a s) = (term78 a s).
Proof. exact (eq_refl (term78 a s)). Qed.
Lemma lem5181471 (b : real) (a : real) (s : real -> Prop) : (term120 b a s) = (term133 b a s).
Proof. exact (MK_COMB (@lem5181469 a s b) (@lem5181470 a s)). Qed.
Lemma lem5181472 (b : real) (a : real) (s : real -> Prop) : ((term119 b a s) = (term120 b a s)) = ((term92 b a s) = (term133 b a s)).
Proof. exact (MK_COMB (@lem5181463 b a s) (@lem5181471 b a s)). Qed.
Lemma lem5181473 (b : real) (a : real) (s : real -> Prop) : (term92 b a s) = (term133 b a s).
Proof. exact (EQ_MP (@lem5181472 b a s) (@lem5181453 b a s)). Qed.
Lemma lem5181570 (a : real) (s : real -> Prop) : (term98 a s) = (term134 a s).
Proof. exact (fun_ext (fun b : real => @lem5181473 b a s)). Qed.
Lemma lem5181571 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5181572 (a : real) (s : real -> Prop) : (term99 a s) = (term135 a s).
Proof. exact (MK_COMB (@lem5181571) (@lem5181570 a s)). Qed.
Lemma lem5181594 {A : Type'} (P : A -> Prop) (Q : Prop) : (term115 A P Q) = (term116 A P Q).
Proof. exact (EQ_MP (@lem18965 A P Q) (@lem18964 A P Q)). Qed.
Lemma lem5181595 (P : real -> Prop) (Q : Prop) : (term117 P Q) = (term118 P Q).
Proof. exact (@lem5181594 real P Q). Qed.
Lemma lem5181596 (a : real) (s : real -> Prop) : (term136 a s) = (term137 a s).
Proof. exact (@lem5181595 (term138 a s) (term78 a s)). Qed.
Lemma lem5181597 (a : real) (s : real -> Prop) (b : real) : (term139 a s b) = (term130 a s b).
Proof. exact (eq_refl (term139 a s b)). Qed.
Lemma lem5181598 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5181599 (a : real) (s : real -> Prop) (b : real) : (term140 a s b) = (term132 a s b).
Proof. exact (MK_COMB (@lem5181598) (@lem5181597 a s b)). Qed.
Lemma lem5181600 (a : real) (s : real -> Prop) : (term78 a s) = (term78 a s).
Proof. exact (eq_refl (term78 a s)). Qed.
Lemma lem5181601 (b : real) (a : real) (s : real -> Prop) : (term141 b a s) = (term133 b a s).
Proof. exact (MK_COMB (@lem5181599 a s b) (@lem5181600 a s)). Qed.
Lemma lem5181602 (a : real) (s : real -> Prop) : (term142 a s) = (term134 a s).
Proof. exact (fun_ext (fun b : real => @lem5181601 b a s)). Qed.
Lemma lem5181603 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5181604 (a : real) (s : real -> Prop) : (term136 a s) = (term135 a s).
Proof. exact (MK_COMB (@lem5181603) (@lem5181602 a s)). Qed.
Lemma lem5181605 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5181606 (a : real) (s : real -> Prop) : (term143 a s) = (term144 a s).
Proof. exact (MK_COMB (@lem5181605) (@lem5181604 a s)). Qed.
Lemma lem5181607 (a : real) (s : real -> Prop) (b : real) : (term139 a s b) = (term130 a s b).
Proof. exact (eq_refl (term139 a s b)). Qed.
Lemma lem5181608 (a : real) (s : real -> Prop) : (term145 a s) = (term138 a s).
Proof. exact (fun_ext (fun b : real => @lem5181607 a s b)). Qed.
Lemma lem5181609 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5181610 (a : real) (s : real -> Prop) : (term146 a s) = (term147 a s).
Proof. exact (MK_COMB (@lem5181609) (@lem5181608 a s)). Qed.
Lemma lem5181611 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5181612 (a : real) (s : real -> Prop) : (term148 a s) = (term149 a s).
Proof. exact (MK_COMB (@lem5181611) (@lem5181610 a s)). Qed.
Lemma lem5181613 (a : real) (s : real -> Prop) : (term78 a s) = (term78 a s).
Proof. exact (eq_refl (term78 a s)). Qed.
Lemma lem5181614 (a : real) (s : real -> Prop) : (term137 a s) = (term150 a s).
Proof. exact (MK_COMB (@lem5181612 a s) (@lem5181613 a s)). Qed.
Lemma lem5181615 (a : real) (s : real -> Prop) : ((term136 a s) = (term137 a s)) = ((term135 a s) = (term150 a s)).
Proof. exact (MK_COMB (@lem5181606 a s) (@lem5181614 a s)). Qed.
Lemma lem5181616 (a : real) (s : real -> Prop) : (term135 a s) = (term150 a s).
Proof. exact (EQ_MP (@lem5181615 a s) (@lem5181596 a s)). Qed.
Lemma lem5181717 (a : real) (s : real -> Prop) : (term99 a s) = (term150 a s).
Proof. exact (TRANS (@lem5181572 a s) (@lem5181616 a s)). Qed.
Lemma lem5181718 (s : real -> Prop) : (term105 s) = (term151 s).
Proof. exact (fun_ext (fun a : real => @lem5181717 a s)). Qed.
Lemma lem5181719 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5181720 (s : real -> Prop) : (term106 s) = (term152 s).
Proof. exact (MK_COMB (@lem5181719) (@lem5181718 s)). Qed.
Lemma lem5181769 : term113 = term153.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5181720 s)). Qed.
Lemma lem5181770 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5181771 : term114 = term154.
Proof. exact (MK_COMB (@lem5181770) (@lem5181769)). Qed.
Lemma lem5181777 {A : Type'} (P : A -> Prop) (Q : Prop) : (term116 A P Q) = (term115 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5181778 (P : real -> Prop) (Q : Prop) : (term118 P Q) = (term117 P Q).
Proof. exact (@lem5181777 real P Q). Qed.
Lemma lem5181779 (a : real) (s : real -> Prop) : (term137 a s) = (term136 a s).
Proof. exact (@lem5181778 (term138 a s) (term78 a s)). Qed.
Lemma lem5181780 (a : real) (s : real -> Prop) (b : real) : (term139 a s b) = (term130 a s b).
Proof. exact (eq_refl (term139 a s b)). Qed.
Lemma lem5181781 (a : real) (s : real -> Prop) : (term145 a s) = (term138 a s).
Proof. exact (fun_ext (fun b : real => @lem5181780 a s b)). Qed.
Lemma lem5181782 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5181783 (a : real) (s : real -> Prop) : (term146 a s) = (term147 a s).
Proof. exact (MK_COMB (@lem5181782) (@lem5181781 a s)). Qed.
Lemma lem5181784 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5181785 (a : real) (s : real -> Prop) : (term148 a s) = (term149 a s).
Proof. exact (MK_COMB (@lem5181784) (@lem5181783 a s)). Qed.
Lemma lem5181786 (a : real) (s : real -> Prop) : (term78 a s) = (term78 a s).
Proof. exact (eq_refl (term78 a s)). Qed.
Lemma lem5181787 (a : real) (s : real -> Prop) : (term137 a s) = (term150 a s).
Proof. exact (MK_COMB (@lem5181785 a s) (@lem5181786 a s)). Qed.
Lemma lem5181788 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5181789 (a : real) (s : real -> Prop) : (term155 a s) = (term156 a s).
Proof. exact (MK_COMB (@lem5181788) (@lem5181787 a s)). Qed.
Lemma lem5181790 (a : real) (s : real -> Prop) (b : real) : (term139 a s b) = (term130 a s b).
Proof. exact (eq_refl (term139 a s b)). Qed.
Lemma lem5181791 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5181792 (a : real) (s : real -> Prop) (b : real) : (term140 a s b) = (term132 a s b).
Proof. exact (MK_COMB (@lem5181791) (@lem5181790 a s b)). Qed.
Lemma lem5181793 (a : real) (s : real -> Prop) : (term78 a s) = (term78 a s).
Proof. exact (eq_refl (term78 a s)). Qed.
Lemma lem5181794 (b : real) (a : real) (s : real -> Prop) : (term141 b a s) = (term133 b a s).
Proof. exact (MK_COMB (@lem5181792 a s b) (@lem5181793 a s)). Qed.
Lemma lem5181795 (a : real) (s : real -> Prop) : (term142 a s) = (term134 a s).
Proof. exact (fun_ext (fun b : real => @lem5181794 b a s)). Qed.
Lemma lem5181796 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5181797 (a : real) (s : real -> Prop) : (term136 a s) = (term135 a s).
Proof. exact (MK_COMB (@lem5181796) (@lem5181795 a s)). Qed.
Lemma lem5181798 (a : real) (s : real -> Prop) : ((term137 a s) = (term136 a s)) = ((term150 a s) = (term135 a s)).
Proof. exact (MK_COMB (@lem5181789 a s) (@lem5181797 a s)). Qed.
Lemma lem5181799 (a : real) (s : real -> Prop) : (term150 a s) = (term135 a s).
Proof. exact (EQ_MP (@lem5181798 a s) (@lem5181779 a s)). Qed.
Lemma lem5181801 {A : Type'} (P : A -> Prop) (Q : Prop) : (term116 A P Q) = (term115 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5181802 (P : real -> Prop) (Q : Prop) : (term118 P Q) = (term117 P Q).
Proof. exact (@lem5181801 real P Q). Qed.
Lemma lem5181803 (b : real) (a : real) (s : real -> Prop) : (term120 b a s) = (term119 b a s).
Proof. exact (@lem5181802 (term121 a s b) (term78 a s)). Qed.
Lemma lem5181804 (a : real) (y : real) (s : real -> Prop) (b : real) : (term122 a s b y) = (term77 a y s b).
Proof. exact (eq_refl (term122 a s b y)). Qed.
Lemma lem5181805 (a : real) (s : real -> Prop) (b : real) : (term128 a s b) = (term121 a s b).
Proof. exact (fun_ext (fun y : real => @lem5181804 a y s b)). Qed.
Lemma lem5181806 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5181807 (a : real) (s : real -> Prop) (b : real) : (term129 a s b) = (term130 a s b).
Proof. exact (MK_COMB (@lem5181806) (@lem5181805 a s b)). Qed.
Lemma lem5181808 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5181809 (a : real) (s : real -> Prop) (b : real) : (term131 a s b) = (term132 a s b).
Proof. exact (MK_COMB (@lem5181808) (@lem5181807 a s b)). Qed.
Lemma lem5181810 (a : real) (s : real -> Prop) : (term78 a s) = (term78 a s).
Proof. exact (eq_refl (term78 a s)). Qed.
Lemma lem5181811 (b : real) (a : real) (s : real -> Prop) : (term120 b a s) = (term133 b a s).
Proof. exact (MK_COMB (@lem5181809 a s b) (@lem5181810 a s)). Qed.
Lemma lem5181812 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5181813 (b : real) (a : real) (s : real -> Prop) : (term157 b a s) = (term158 b a s).
Proof. exact (MK_COMB (@lem5181812) (@lem5181811 b a s)). Qed.
Lemma lem5181814 (a : real) (y : real) (s : real -> Prop) (b : real) : (term122 a s b y) = (term77 a y s b).
Proof. exact (eq_refl (term122 a s b y)). Qed.
Lemma lem5181815 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5181816 (a : real) (y : real) (s : real -> Prop) (b : real) : (term123 a s b y) = (term80 a y s b).
Proof. exact (MK_COMB (@lem5181815) (@lem5181814 a y s b)). Qed.
Lemma lem5181817 (a : real) (s : real -> Prop) : (term78 a s) = (term78 a s).
Proof. exact (eq_refl (term78 a s)). Qed.
Lemma lem5181818 (y : real) (b : real) (a : real) (s : real -> Prop) : (term124 b y a s) = (term82 y b a s).
Proof. exact (MK_COMB (@lem5181816 a y s b) (@lem5181817 a s)). Qed.
Lemma lem5181819 (b : real) (a : real) (s : real -> Prop) : (term125 b a s) = (term91 b a s).
Proof. exact (fun_ext (fun y : real => @lem5181818 y b a s)). Qed.
Lemma lem5181820 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5181821 (b : real) (a : real) (s : real -> Prop) : (term119 b a s) = (term92 b a s).
Proof. exact (MK_COMB (@lem5181820) (@lem5181819 b a s)). Qed.
Lemma lem5181822 (b : real) (a : real) (s : real -> Prop) : ((term120 b a s) = (term119 b a s)) = ((term133 b a s) = (term92 b a s)).
Proof. exact (MK_COMB (@lem5181813 b a s) (@lem5181821 b a s)). Qed.
Lemma lem5181823 (b : real) (a : real) (s : real -> Prop) : (term133 b a s) = (term92 b a s).
Proof. exact (EQ_MP (@lem5181822 b a s) (@lem5181803 b a s)). Qed.
Lemma lem5181824 (a : real) (s : real -> Prop) : (term134 a s) = (term98 a s).
Proof. exact (fun_ext (fun b : real => @lem5181823 b a s)). Qed.
Lemma lem5181825 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5181826 (a : real) (s : real -> Prop) : (term135 a s) = (term99 a s).
Proof. exact (MK_COMB (@lem5181825) (@lem5181824 a s)). Qed.
Lemma lem5181827 (a : real) (s : real -> Prop) : (term150 a s) = (term99 a s).
Proof. exact (TRANS (@lem5181799 a s) (@lem5181826 a s)). Qed.
Lemma lem5181828 (s : real -> Prop) : (term151 s) = (term105 s).
Proof. exact (fun_ext (fun a : real => @lem5181827 a s)). Qed.
Lemma lem5181829 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5181830 (s : real -> Prop) : (term152 s) = (term106 s).
Proof. exact (MK_COMB (@lem5181829) (@lem5181828 s)). Qed.
Lemma lem5181831 : term153 = term113.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5181830 s)). Qed.
Lemma lem5181832 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5181833 : term154 = term114.
Proof. exact (MK_COMB (@lem5181832) (@lem5181831)). Qed.
Lemma lem5181834 : term114 = term114.
Proof. exact (TRANS (@lem5181771) (@lem5181833)). Qed.
Lemma lem5181835 : term10 = term114.
Proof. exact (TRANS (@lem5181417) (@lem5181834)). Qed.
Lemma lem5181836 (h1 : term10) : term114.
Proof. exact (EQ_MP (@lem5181835) (@lem5181350 h1)). Qed.
Lemma lem5181843 (x : real) (y : real) (z : real) : (term159 x y z) = (term160 x y z).
Proof. exact (@lem17045 (real_le x y) (real_le y z)). Qed.
Lemma lem5181844 (x : real) (z : real) : (real_le x z) = (real_le x z).
Proof. exact (eq_refl (real_le x z)). Qed.
Lemma lem5181845 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5181846 (x : real) (y : real) (z : real) : (term161 x y z) = (term162 x y z).
Proof. exact (MK_COMB (@lem5181845) (@lem5181843 x y z)). Qed.
Lemma lem5181847 (y : real) (x : real) (z : real) : (term163 y x z) = (term164 y x z).
Proof. exact (MK_COMB (@lem5181846 x y z) (@lem5181844 x z)). Qed.
Lemma lem5181848 (y : real) (x : real) (z : real) : (term52 y x z) = (term163 y x z).
Proof. exact (@lem17265 (term165 x y z) (real_le x z)). Qed.
Lemma lem5181849 (y : real) (x : real) (z : real) : (term52 y x z) = (term164 y x z).
Proof. exact (TRANS (@lem5181848 y x z) (@lem5181847 y x z)). Qed.
Lemma lem5181850 (y : real) (x : real) : (term53 y x) = (term166 y x).
Proof. exact (fun_ext (fun z : real => @lem5181849 y x z)). Qed.
Lemma lem5181851 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5181852 (y : real) (x : real) : (term54 y x) = (term167 y x).
Proof. exact (MK_COMB (@lem5181851) (@lem5181850 y x)). Qed.
Lemma lem5181853 (x : real) : (term55 x) = (term168 x).
Proof. exact (fun_ext (fun y : real => @lem5181852 y x)). Qed.
Lemma lem5181854 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5181855 (x : real) : (term56 x) = (term169 x).
Proof. exact (MK_COMB (@lem5181854) (@lem5181853 x)). Qed.
Lemma lem5181856 : term57 = term170.
Proof. exact (fun_ext (fun x : real => @lem5181855 x)). Qed.
Lemma lem5181857 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5181918 : term58 = term171.
Proof. exact (MK_COMB (@lem5181857) (@lem5181856)). Qed.
Lemma lem5181919 (h1 : term58) : term171.
Proof. exact (EQ_MP (@lem5181918) (@lem5181351 h1)). Qed.
Lemma lem5181921 (x : real) (s : real -> Prop) : (@IN real x s) = (@IN real x s).
Proof. exact (eq_refl (@IN real x s)). Qed.
Lemma lem5181922 (P : real -> Prop) : (term172 P) = (term173 P).
Proof. exact (@lem18394 real P). Qed.
Lemma lem5181923 (s : real -> Prop) : (term174 s) = (term175 s).
Proof. exact (@lem5181922 (term48 s)). Qed.
Lemma lem5181924 (x : real) (s : real -> Prop) : (term176 s x) = (@IN real x s).
Proof. exact (eq_refl (term176 s x)). Qed.
Lemma lem5181925 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5181927 (x : real) (s : real -> Prop) : (term177 s x) = (term178 x s).
Proof. exact (MK_COMB (@lem5181925) (@lem5181924 x s)). Qed.
Lemma lem5181928 (s : real -> Prop) : (term179 s) = (term180 s).
Proof. exact (fun_ext (fun x : real => @lem5181927 x s)). Qed.
Lemma lem5181929 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5181930 (s : real -> Prop) : (term175 s) = (term181 s).
Proof. exact (MK_COMB (@lem5181929) (@lem5181928 s)). Qed.
Lemma lem5181931 (s : real -> Prop) : (term174 s) = (term181 s).
Proof. exact (TRANS (@lem5181923 s) (@lem5181930 s)). Qed.
Lemma lem5181932 (s : real -> Prop) : (term48 s) = (term48 s).
Proof. exact (fun_ext (fun x : real => @lem5181921 x s)). Qed.
Lemma lem5181933 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5181934 (s : real -> Prop) : (term49 s) = (term49 s).
Proof. exact (MK_COMB (@lem5181933) (@lem5181932 s)). Qed.
Lemma lem5181935 (s : real -> Prop) : (term47 s) = (term47 s).
Proof. exact (eq_refl (term47 s)). Qed.
Lemma lem5181938 (s : real -> Prop) : (term182 s) = (s = (@EMPTY real)).
Proof. exact (@lem16933 (s = (@EMPTY real))). Qed.
Lemma lem5181939 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5181940 (s : real -> Prop) : (term183 s) = (term184 s).
Proof. exact (MK_COMB (@lem5181939) (@lem5181931 s)). Qed.
Lemma lem5181941 (s : real -> Prop) : (term185 s) = (term186 s).
Proof. exact (MK_COMB (@lem5181940 s) (@lem5181935 s)). Qed.
Lemma lem5181942 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5181943 (s : real -> Prop) : (term187 s) = (term187 s).
Proof. exact (MK_COMB (@lem5181942) (@lem5181934 s)). Qed.
Lemma lem5181944 (s : real -> Prop) : (term188 s) = (term189 s).
Proof. exact (MK_COMB (@lem5181943 s) (@lem5181938 s)). Qed.
Lemma lem5181945 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5181946 (s : real -> Prop) : (term190 s) = (term191 s).
Proof. exact (MK_COMB (@lem5181945) (@lem5181944 s)). Qed.
Lemma lem5181947 (s : real -> Prop) : (term192 s) = (term193 s).
Proof. exact (MK_COMB (@lem5181946 s) (@lem5181941 s)). Qed.
Lemma lem5181948 (s : real -> Prop) : ((term49 s) = (term47 s)) = (term192 s).
Proof. exact (@lem17784 (term49 s) (term47 s)). Qed.
Lemma lem5181949 (s : real -> Prop) : ((term49 s) = (term47 s)) = (term193 s).
Proof. exact (TRANS (@lem5181948 s) (@lem5181947 s)). Qed.
Lemma lem5181950 : term51 = term194.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5181949 s)). Qed.
Lemma lem5181951 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5181952 : term11 = term195.
Proof. exact (MK_COMB (@lem5181951) (@lem5181950)). Qed.
Lemma lem5181954 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term196 A P Q) = (term197 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5181955 (P : type1022) (Q : type1022) : (term198 P Q) = (term199 P Q).
Proof. exact (@lem5181954 (real -> Prop) P Q). Qed.
Lemma lem5181956 : term200 = term201.
Proof. exact (@lem5181955 term202 term203). Qed.
Lemma lem5181957 (s : real -> Prop) : (term204 s) = (term189 s).
Proof. exact (eq_refl (term204 s)). Qed.
Lemma lem5181958 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5181959 (s : real -> Prop) : (term205 s) = (term191 s).
Proof. exact (MK_COMB (@lem5181958) (@lem5181957 s)). Qed.
Lemma lem5181960 (s : real -> Prop) : (term206 s) = (term186 s).
Proof. exact (eq_refl (term206 s)). Qed.
Lemma lem5181961 (s : real -> Prop) : (term207 s) = (term193 s).
Proof. exact (MK_COMB (@lem5181959 s) (@lem5181960 s)). Qed.
Lemma lem5181962 : term208 = term194.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5181961 s)). Qed.
Lemma lem5181963 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5181964 : term200 = term195.
Proof. exact (MK_COMB (@lem5181963) (@lem5181962)). Qed.
Lemma lem5181965 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5181966 : term209 = term210.
Proof. exact (MK_COMB (@lem5181965) (@lem5181964)). Qed.
Lemma lem5181967 (s : real -> Prop) : (term204 s) = (term189 s).
Proof. exact (eq_refl (term204 s)). Qed.
Lemma lem5181968 : term211 = term202.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5181967 s)). Qed.
Lemma lem5181969 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5181970 : term212 = term213.
Proof. exact (MK_COMB (@lem5181969) (@lem5181968)). Qed.
Lemma lem5181971 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5181972 : term214 = term215.
Proof. exact (MK_COMB (@lem5181971) (@lem5181970)). Qed.
Lemma lem5181973 (s : real -> Prop) : (term206 s) = (term186 s).
Proof. exact (eq_refl (term206 s)). Qed.
Lemma lem5181974 : term216 = term203.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5181973 s)). Qed.
Lemma lem5181975 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5181976 : term217 = term218.
Proof. exact (MK_COMB (@lem5181975) (@lem5181974)). Qed.
Lemma lem5181977 : term201 = term219.
Proof. exact (MK_COMB (@lem5181972) (@lem5181976)). Qed.
Lemma lem5181978 : (term200 = term201) = (term195 = term219).
Proof. exact (MK_COMB (@lem5181966) (@lem5181977)). Qed.
Lemma lem5181979 : term195 = term219.
Proof. exact (EQ_MP (@lem5181978) (@lem5181956)). Qed.
Lemma lem5182085 {A : Type'} (P : A -> Prop) (Q : Prop) : (term220 A P Q) = (term221 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5182086 (P : real -> Prop) (Q : Prop) : (term222 P Q) = (term223 P Q).
Proof. exact (@lem5182085 real P Q). Qed.
Lemma lem5182087 (s : real -> Prop) : (term224 s) = (term225 s).
Proof. exact (@lem5182086 (term48 s) (s = (@EMPTY real))). Qed.
Lemma lem5182088 (x : real) (s : real -> Prop) : (term176 s x) = (@IN real x s).
Proof. exact (eq_refl (term176 s x)). Qed.
Lemma lem5182089 (s : real -> Prop) : (term226 s) = (term48 s).
Proof. exact (fun_ext (fun x : real => @lem5182088 x s)). Qed.
Lemma lem5182090 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5182091 (s : real -> Prop) : (term227 s) = (term49 s).
Proof. exact (MK_COMB (@lem5182090) (@lem5182089 s)). Qed.
Lemma lem5182092 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5182093 (s : real -> Prop) : (term228 s) = (term187 s).
Proof. exact (MK_COMB (@lem5182092) (@lem5182091 s)). Qed.
Lemma lem5182094 (s : real -> Prop) : (s = (@EMPTY real)) = (s = (@EMPTY real)).
Proof. exact (eq_refl (s = (@EMPTY real))). Qed.
Lemma lem5182095 (s : real -> Prop) : (term224 s) = (term189 s).
Proof. exact (MK_COMB (@lem5182093 s) (@lem5182094 s)). Qed.
Lemma lem5182096 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5182097 (s : real -> Prop) : (term229 s) = (term230 s).
Proof. exact (MK_COMB (@lem5182096) (@lem5182095 s)). Qed.
Lemma lem5182098 (x : real) (s : real -> Prop) : (term176 s x) = (@IN real x s).
Proof. exact (eq_refl (term176 s x)). Qed.
Lemma lem5182099 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5182100 (x : real) (s : real -> Prop) : (term231 s x) = (term232 x s).
Proof. exact (MK_COMB (@lem5182099) (@lem5182098 x s)). Qed.
Lemma lem5182101 (s : real -> Prop) : (s = (@EMPTY real)) = (s = (@EMPTY real)).
Proof. exact (eq_refl (s = (@EMPTY real))). Qed.
Lemma lem5182102 (x : real) (s : real -> Prop) : (term233 x s) = (term234 x s).
Proof. exact (MK_COMB (@lem5182100 x s) (@lem5182101 s)). Qed.
Lemma lem5182103 (s : real -> Prop) : (term235 s) = (term236 s).
Proof. exact (fun_ext (fun x : real => @lem5182102 x s)). Qed.
Lemma lem5182104 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5182105 (s : real -> Prop) : (term225 s) = (term237 s).
Proof. exact (MK_COMB (@lem5182104) (@lem5182103 s)). Qed.
Lemma lem5182106 (s : real -> Prop) : ((term224 s) = (term225 s)) = ((term189 s) = (term237 s)).
Proof. exact (MK_COMB (@lem5182097 s) (@lem5182105 s)). Qed.
Lemma lem5182107 (s : real -> Prop) : (term189 s) = (term237 s).
Proof. exact (EQ_MP (@lem5182106 s) (@lem5182087 s)). Qed.
Lemma lem5182108 : term202 = term238.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5182107 s)). Qed.
Lemma lem5182109 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5182110 : term213 = term239.
Proof. exact (MK_COMB (@lem5182109) (@lem5182108)). Qed.
Lemma lem5182112 {A B : Type'} (P : type1413 A B) : (term240 A B P) = (term241 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5182113 (P : type1020) : (term242 P) = (term243 P).
Proof. exact (@lem5182112 (real -> Prop) real P). Qed.
Lemma lem5182114 : term244 = term245.
Proof. exact (@lem5182113 term246). Qed.
Lemma lem5182115 (s : real -> Prop) : (term247 s) = (term236 s).
Proof. exact (eq_refl (term247 s)). Qed.
Lemma lem5182116 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5182117 (s : real -> Prop) (x : real) : (term248 s x) = (term249 s x).
Proof. exact (MK_COMB (@lem5182115 s) (@lem5182116 x)). Qed.
Lemma lem5182118 (x : real) (s : real -> Prop) : (term249 s x) = (term234 x s).
Proof. exact (eq_refl (term249 s x)). Qed.
Lemma lem5182119 (x : real) (s : real -> Prop) : (term248 s x) = (term234 x s).
Proof. exact (TRANS (@lem5182117 s x) (@lem5182118 x s)). Qed.
Lemma lem5182120 (s : real -> Prop) : (term250 s) = (term236 s).
Proof. exact (fun_ext (fun x : real => @lem5182119 x s)). Qed.
Lemma lem5182121 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5182122 (s : real -> Prop) : (term251 s) = (term237 s).
Proof. exact (MK_COMB (@lem5182121) (@lem5182120 s)). Qed.
Lemma lem5182123 : term252 = term238.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5182122 s)). Qed.
Lemma lem5182124 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5182125 : term244 = term239.
Proof. exact (MK_COMB (@lem5182124) (@lem5182123)). Qed.
Lemma lem5182126 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5182127 : term253 = term254.
Proof. exact (MK_COMB (@lem5182126) (@lem5182125)). Qed.
Lemma lem5182128 (s : real -> Prop) : (term247 s) = (term236 s).
Proof. exact (eq_refl (term247 s)). Qed.
Lemma lem5182129 (x : type1023) (s : real -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem5182130 (x : type1023) (s : real -> Prop) : (term255 x s) = (term256 x s).
Proof. exact (MK_COMB (@lem5182128 s) (@lem5182129 x s)). Qed.
Lemma lem5182131 (x : type1023) (s : real -> Prop) : (term256 x s) = (term257 x s).
Proof. exact (eq_refl (term256 x s)). Qed.
Lemma lem5182132 (x : type1023) (s : real -> Prop) : (term255 x s) = (term257 x s).
Proof. exact (TRANS (@lem5182130 x s) (@lem5182131 x s)). Qed.
Lemma lem5182133 (x : type1023) : (term258 x) = (term259 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5182132 x s)). Qed.
Lemma lem5182134 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5182135 (x : type1023) : (term260 x) = (term261 x).
Proof. exact (MK_COMB (@lem5182134) (@lem5182133 x)). Qed.
Lemma lem5182136 : term262 = term263.
Proof. exact (fun_ext (fun x : type1023 => @lem5182135 x)). Qed.
Lemma lem5182137 : (@ex ((real -> Prop) -> real)) = (@ex ((real -> Prop) -> real)).
Proof. exact (eq_refl (@ex ((real -> Prop) -> real))). Qed.
Lemma lem5182138 : term245 = term264.
Proof. exact (MK_COMB (@lem5182137) (@lem5182136)). Qed.
Lemma lem5182139 : (term244 = term245) = (term239 = term264).
Proof. exact (MK_COMB (@lem5182127) (@lem5182138)). Qed.
Lemma lem5182140 : term239 = term264.
Proof. exact (EQ_MP (@lem5182139) (@lem5182114)). Qed.
Lemma lem5182141 : term213 = term264.
Proof. exact (TRANS (@lem5182110) (@lem5182140)). Qed.
Lemma lem5182142 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5182143 : term215 = term265.
Proof. exact (MK_COMB (@lem5182142) (@lem5182141)). Qed.
Lemma lem5182144 : term218 = term218.
Proof. exact (eq_refl term218). Qed.
Lemma lem5182145 : term219 = term266.
Proof. exact (MK_COMB (@lem5182143) (@lem5182144)). Qed.
Lemma lem5182147 {A : Type'} (P : A -> Prop) (Q : Prop) : (term116 A P Q) = (term115 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5182148 (P : type257) (Q : Prop) : (term267 P Q) = (term268 P Q).
Proof. exact (@lem5182147 type1023 P Q). Qed.
Lemma lem5182149 : term269 = term270.
Proof. exact (@lem5182148 term263 term218). Qed.
Lemma lem5182150 (x : type1023) : (term271 x) = (term261 x).
Proof. exact (eq_refl (term271 x)). Qed.
Lemma lem5182151 : term272 = term263.
Proof. exact (fun_ext (fun x : type1023 => @lem5182150 x)). Qed.
Lemma lem5182152 : (@ex ((real -> Prop) -> real)) = (@ex ((real -> Prop) -> real)).
Proof. exact (eq_refl (@ex ((real -> Prop) -> real))). Qed.
Lemma lem5182153 : term273 = term264.
Proof. exact (MK_COMB (@lem5182152) (@lem5182151)). Qed.
Lemma lem5182154 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5182155 : term274 = term265.
Proof. exact (MK_COMB (@lem5182154) (@lem5182153)). Qed.
Lemma lem5182156 : term218 = term218.
Proof. exact (eq_refl term218). Qed.
Lemma lem5182157 : term269 = term266.
Proof. exact (MK_COMB (@lem5182155) (@lem5182156)). Qed.
Lemma lem5182158 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5182159 : term275 = term276.
Proof. exact (MK_COMB (@lem5182158) (@lem5182157)). Qed.
Lemma lem5182160 (x : type1023) : (term271 x) = (term261 x).
Proof. exact (eq_refl (term271 x)). Qed.
Lemma lem5182161 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5182162 (x : type1023) : (term277 x) = (term278 x).
Proof. exact (MK_COMB (@lem5182161) (@lem5182160 x)). Qed.
Lemma lem5182163 : term218 = term218.
Proof. exact (eq_refl term218). Qed.
Lemma lem5182164 (x : type1023) : (term279 x) = (term280 x).
Proof. exact (MK_COMB (@lem5182162 x) (@lem5182163)). Qed.
Lemma lem5182165 : term281 = term282.
Proof. exact (fun_ext (fun x : type1023 => @lem5182164 x)). Qed.
Lemma lem5182166 : (@ex ((real -> Prop) -> real)) = (@ex ((real -> Prop) -> real)).
Proof. exact (eq_refl (@ex ((real -> Prop) -> real))). Qed.
Lemma lem5182167 : term270 = term283.
Proof. exact (MK_COMB (@lem5182166) (@lem5182165)). Qed.
Lemma lem5182168 : (term269 = term270) = (term266 = term283).
Proof. exact (MK_COMB (@lem5182159) (@lem5182167)). Qed.
Lemma lem5182169 : term266 = term283.
Proof. exact (EQ_MP (@lem5182168) (@lem5182149)). Qed.
Lemma lem5182170 : term219 = term283.
Proof. exact (TRANS (@lem5182145) (@lem5182169)). Qed.
Lemma lem5182171 : term195 = term283.
Proof. exact (TRANS (@lem5181979) (@lem5182170)). Qed.
Lemma lem5182172 : term11 = term283.
Proof. exact (TRANS (@lem5181952) (@lem5182171)). Qed.
Lemma lem5182173 (h1 : term11) : term283.
Proof. exact (EQ_MP (@lem5182172) (@lem5181352 h1)). Qed.
Lemma lem5182176 (s : real -> Prop) : (term182 s) = (s = (@EMPTY real)).
Proof. exact (@lem16933 (s = (@EMPTY real))). Qed.
Lemma lem5182183 (s : real -> Prop) (x : real) (b : real) : (term284 s x b) = (term285 s x b).
Proof. exact (@lem17362 (@IN real x s) (real_le x b)). Qed.
Lemma lem5182184 (P : real -> Prop) : (term84 P) = (term85 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5182185 (s : real -> Prop) (b : real) : (term286 s b) = (term287 s b).
Proof. exact (@lem5182184 (term29 s b)). Qed.
Lemma lem5182186 (s : real -> Prop) (x : real) (b : real) : (term288 s b x) = (term28 s x b).
Proof. exact (eq_refl (term288 s b x)). Qed.
Lemma lem5182187 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5182188 (s : real -> Prop) (x : real) (b : real) : (term289 s b x) = (term284 s x b).
Proof. exact (MK_COMB (@lem5182187) (@lem5182186 s x b)). Qed.
Lemma lem5182189 (s : real -> Prop) (x : real) (b : real) : (term289 s b x) = (term285 s x b).
Proof. exact (TRANS (@lem5182188 s x b) (@lem5182183 s x b)). Qed.
Lemma lem5182190 (s : real -> Prop) (b : real) : (term290 s b) = (term291 s b).
Proof. exact (fun_ext (fun x : real => @lem5182189 s x b)). Qed.
Lemma lem5182191 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5182192 (s : real -> Prop) (b : real) : (term287 s b) = (term292 s b).
Proof. exact (MK_COMB (@lem5182191) (@lem5182190 s b)). Qed.
Lemma lem5182193 (s : real -> Prop) (b : real) : (term286 s b) = (term292 s b).
Proof. exact (TRANS (@lem5182185 s b) (@lem5182192 s b)). Qed.
Lemma lem5182194 (P : real -> Prop) : (term172 P) = (term173 P).
Proof. exact (@lem18394 real P). Qed.
Lemma lem5182195 (s : real -> Prop) : (term293 s) = (term294 s).
Proof. exact (@lem5182194 (term40 s)). Qed.
Lemma lem5182196 (s : real -> Prop) (b : real) : (term295 s b) = (term30 s b).
Proof. exact (eq_refl (term295 s b)). Qed.
Lemma lem5182197 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5182198 (s : real -> Prop) (b : real) : (term296 s b) = (term286 s b).
Proof. exact (MK_COMB (@lem5182197) (@lem5182196 s b)). Qed.
Lemma lem5182199 (s : real -> Prop) (b : real) : (term296 s b) = (term292 s b).
Proof. exact (TRANS (@lem5182198 s b) (@lem5182193 s b)). Qed.
Lemma lem5182200 (s : real -> Prop) : (term297 s) = (term298 s).
Proof. exact (fun_ext (fun b : real => @lem5182199 s b)). Qed.
Lemma lem5182201 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5182202 (s : real -> Prop) : (term294 s) = (term299 s).
Proof. exact (MK_COMB (@lem5182201) (@lem5182200 s)). Qed.
Lemma lem5182203 (s : real -> Prop) : (term293 s) = (term299 s).
Proof. exact (TRANS (@lem5182195 s) (@lem5182202 s)). Qed.
Lemma lem5182204 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5182205 (s : real -> Prop) : (term300 s) = (term301 s).
Proof. exact (MK_COMB (@lem5182204) (@lem5182176 s)). Qed.
Lemma lem5182206 (s : real -> Prop) : (term302 s) = (term303 s).
Proof. exact (MK_COMB (@lem5182205 s) (@lem5182203 s)). Qed.
Lemma lem5182207 (s : real -> Prop) : (term304 s) = (term302 s).
Proof. exact (@lem17045 (term47 s) (term41 s)). Qed.
Lemma lem5182208 (s : real -> Prop) : (term304 s) = (term303 s).
Proof. exact (TRANS (@lem5182207 s) (@lem5182206 s)). Qed.
Lemma lem5182215 (x : real) (s : real -> Prop) : (term35 x s) = (term305 x s).
Proof. exact (@lem17265 (@IN real x s) (term59 x s)). Qed.
Lemma lem5182216 (s : real -> Prop) : (term36 s) = (term306 s).
Proof. exact (fun_ext (fun x : real => @lem5182215 x s)). Qed.
Lemma lem5182217 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5182218 (s : real -> Prop) : (term37 s) = (term307 s).
Proof. exact (MK_COMB (@lem5182217) (@lem5182216 s)). Qed.
Lemma lem5182225 (s : real -> Prop) (x : real) (b : real) : (term284 s x b) = (term285 s x b).
Proof. exact (@lem17362 (@IN real x s) (real_le x b)). Qed.
Lemma lem5182226 (P : real -> Prop) : (term84 P) = (term85 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5182227 (s : real -> Prop) (b : real) : (term286 s b) = (term287 s b).
Proof. exact (@lem5182226 (term29 s b)). Qed.
Lemma lem5182228 (s : real -> Prop) (x : real) (b : real) : (term288 s b x) = (term28 s x b).
Proof. exact (eq_refl (term288 s b x)). Qed.
Lemma lem5182229 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5182230 (s : real -> Prop) (x : real) (b : real) : (term289 s b x) = (term284 s x b).
Proof. exact (MK_COMB (@lem5182229) (@lem5182228 s x b)). Qed.
Lemma lem5182231 (s : real -> Prop) (x : real) (b : real) : (term289 s b x) = (term285 s x b).
Proof. exact (TRANS (@lem5182230 s x b) (@lem5182225 s x b)). Qed.
Lemma lem5182232 (s : real -> Prop) (b : real) : (term290 s b) = (term291 s b).
Proof. exact (fun_ext (fun x : real => @lem5182231 s x b)). Qed.
Lemma lem5182233 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5182234 (s : real -> Prop) (b : real) : (term287 s b) = (term292 s b).
Proof. exact (MK_COMB (@lem5182233) (@lem5182232 s b)). Qed.
Lemma lem5182235 (s : real -> Prop) (b : real) : (term286 s b) = (term292 s b).
Proof. exact (TRANS (@lem5182227 s b) (@lem5182234 s b)). Qed.
Lemma lem5182236 (s : real -> Prop) (b : real) : (term27 s b) = (term27 s b).
Proof. exact (eq_refl (term27 s b)). Qed.
Lemma lem5182237 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5182238 (s : real -> Prop) (b : real) : (term308 s b) = (term309 s b).
Proof. exact (MK_COMB (@lem5182237) (@lem5182235 s b)). Qed.
Lemma lem5182239 (s : real -> Prop) (b : real) : (term310 s b) = (term311 s b).
Proof. exact (MK_COMB (@lem5182238 s b) (@lem5182236 s b)). Qed.
Lemma lem5182240 (s : real -> Prop) (b : real) : (term32 s b) = (term310 s b).
Proof. exact (@lem17265 (term30 s b) (term27 s b)). Qed.
Lemma lem5182241 (s : real -> Prop) (b : real) : (term32 s b) = (term311 s b).
Proof. exact (TRANS (@lem5182240 s b) (@lem5182239 s b)). Qed.
Lemma lem5182242 (s : real -> Prop) : (term33 s) = (term312 s).
Proof. exact (fun_ext (fun b : real => @lem5182241 s b)). Qed.
Lemma lem5182243 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5182244 (s : real -> Prop) : (term34 s) = (term313 s).
Proof. exact (MK_COMB (@lem5182243) (@lem5182242 s)). Qed.
Lemma lem5182245 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5182246 (s : real -> Prop) : (term38 s) = (term314 s).
Proof. exact (MK_COMB (@lem5182245) (@lem5182218 s)). Qed.
Lemma lem5182247 (s : real -> Prop) : (term39 s) = (term315 s).
Proof. exact (MK_COMB (@lem5182246 s) (@lem5182244 s)). Qed.
Lemma lem5182248 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5182249 (s : real -> Prop) : (term316 s) = (term317 s).
Proof. exact (MK_COMB (@lem5182248) (@lem5182208 s)). Qed.
Lemma lem5182250 (s : real -> Prop) : (term318 s) = (term319 s).
Proof. exact (MK_COMB (@lem5182249 s) (@lem5182247 s)). Qed.
Lemma lem5182251 (s : real -> Prop) : (term45 s) = (term318 s).
Proof. exact (@lem17265 (term43 s) (term39 s)). Qed.
Lemma lem5182252 (s : real -> Prop) : (term45 s) = (term319 s).
Proof. exact (TRANS (@lem5182251 s) (@lem5182250 s)). Qed.
Lemma lem5182253 : term46 = term320.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5182252 s)). Qed.
Lemma lem5182254 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5182255 : term18 = term321.
Proof. exact (MK_COMB (@lem5182254) (@lem5182253)). Qed.
Lemma lem5182502 {A B : Type'} (P : type1413 A B) : (term240 A B P) = (term241 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5182503 (P : type1626) : (term322 P) = (term323 P).
Proof. exact (@lem5182502 real real P). Qed.
Lemma lem5182504 (s : real -> Prop) : (term324 s) = (term325 s).
Proof. exact (@lem5182503 (term326 s)). Qed.
Lemma lem5182505 (s : real -> Prop) (b : real) : (term327 s b) = (term291 s b).
Proof. exact (eq_refl (term327 s b)). Qed.
Lemma lem5182506 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5182507 (s : real -> Prop) (b : real) (x : real) : (term328 s b x) = (term329 s b x).
Proof. exact (MK_COMB (@lem5182505 s b) (@lem5182506 x)). Qed.
Lemma lem5182508 (s : real -> Prop) (x : real) (b : real) : (term329 s b x) = (term285 s x b).
Proof. exact (eq_refl (term329 s b x)). Qed.
Lemma lem5182509 (s : real -> Prop) (x : real) (b : real) : (term328 s b x) = (term285 s x b).
Proof. exact (TRANS (@lem5182507 s b x) (@lem5182508 s x b)). Qed.
Lemma lem5182510 (s : real -> Prop) (b : real) : (term330 s b) = (term291 s b).
Proof. exact (fun_ext (fun x : real => @lem5182509 s x b)). Qed.
Lemma lem5182511 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5182512 (s : real -> Prop) (b : real) : (term331 s b) = (term292 s b).
Proof. exact (MK_COMB (@lem5182511) (@lem5182510 s b)). Qed.
Lemma lem5182513 (s : real -> Prop) : (term332 s) = (term298 s).
Proof. exact (fun_ext (fun b : real => @lem5182512 s b)). Qed.
Lemma lem5182514 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5182515 (s : real -> Prop) : (term324 s) = (term299 s).
Proof. exact (MK_COMB (@lem5182514) (@lem5182513 s)). Qed.
Lemma lem5182516 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5182517 (s : real -> Prop) : (term333 s) = (term334 s).
Proof. exact (MK_COMB (@lem5182516) (@lem5182515 s)). Qed.
Lemma lem5182518 (s : real -> Prop) (b : real) : (term327 s b) = (term291 s b).
Proof. exact (eq_refl (term327 s b)). Qed.
Lemma lem5182519 (x : real -> real) (b : real) : (x b) = (x b).
Proof. exact (eq_refl (x b)). Qed.
Lemma lem5182520 (s : real -> Prop) (x : real -> real) (b : real) : (term335 s x b) = (term336 s x b).
Proof. exact (MK_COMB (@lem5182518 s b) (@lem5182519 x b)). Qed.
Lemma lem5182521 (s : real -> Prop) (x : real -> real) (b : real) : (term336 s x b) = (term337 s x b).
Proof. exact (eq_refl (term336 s x b)). Qed.
Lemma lem5182522 (s : real -> Prop) (x : real -> real) (b : real) : (term335 s x b) = (term337 s x b).
Proof. exact (TRANS (@lem5182520 s x b) (@lem5182521 s x b)). Qed.
Lemma lem5182523 (s : real -> Prop) (x : real -> real) : (term338 s x) = (term339 s x).
Proof. exact (fun_ext (fun b : real => @lem5182522 s x b)). Qed.
Lemma lem5182524 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5182525 (s : real -> Prop) (x : real -> real) : (term340 s x) = (term341 s x).
Proof. exact (MK_COMB (@lem5182524) (@lem5182523 s x)). Qed.
Lemma lem5182526 (s : real -> Prop) : (term342 s) = (term343 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5182525 s x)). Qed.
Lemma lem5182527 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5182528 (s : real -> Prop) : (term325 s) = (term344 s).
Proof. exact (MK_COMB (@lem5182527) (@lem5182526 s)). Qed.
Lemma lem5182529 (s : real -> Prop) : ((term324 s) = (term325 s)) = ((term299 s) = (term344 s)).
Proof. exact (MK_COMB (@lem5182517 s) (@lem5182528 s)). Qed.
Lemma lem5182530 (s : real -> Prop) : (term299 s) = (term344 s).
Proof. exact (EQ_MP (@lem5182529 s) (@lem5182504 s)). Qed.
Lemma lem5182531 (s : real -> Prop) : (term301 s) = (term301 s).
Proof. exact (eq_refl (term301 s)). Qed.
Lemma lem5182532 (s : real -> Prop) : (term303 s) = (term345 s).
Proof. exact (MK_COMB (@lem5182531 s) (@lem5182530 s)). Qed.
Lemma lem5182534 {A : Type'} (P : Prop) (Q : A -> Prop) : (term346 A P Q) = (term347 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5182535 (P : Prop) (Q : type1028) : (term348 P Q) = (term349 P Q).
Proof. exact (@lem5182534 (real -> real) P Q). Qed.
Lemma lem5182536 (s : real -> Prop) : (term350 s) = (term351 s).
Proof. exact (@lem5182535 (s = (@EMPTY real)) (term343 s)). Qed.
Lemma lem5182537 (s : real -> Prop) (x : real -> real) : (term352 s x) = (term341 s x).
Proof. exact (eq_refl (term352 s x)). Qed.
Lemma lem5182538 (s : real -> Prop) : (term353 s) = (term343 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5182537 s x)). Qed.
Lemma lem5182539 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5182540 (s : real -> Prop) : (term354 s) = (term344 s).
Proof. exact (MK_COMB (@lem5182539) (@lem5182538 s)). Qed.
Lemma lem5182541 (s : real -> Prop) : (term301 s) = (term301 s).
Proof. exact (eq_refl (term301 s)). Qed.
Lemma lem5182542 (s : real -> Prop) : (term350 s) = (term345 s).
Proof. exact (MK_COMB (@lem5182541 s) (@lem5182540 s)). Qed.
Lemma lem5182543 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5182544 (s : real -> Prop) : (term355 s) = (term356 s).
Proof. exact (MK_COMB (@lem5182543) (@lem5182542 s)). Qed.
Lemma lem5182545 (s : real -> Prop) (x : real -> real) : (term352 s x) = (term341 s x).
Proof. exact (eq_refl (term352 s x)). Qed.
Lemma lem5182546 (s : real -> Prop) : (term301 s) = (term301 s).
Proof. exact (eq_refl (term301 s)). Qed.
Lemma lem5182547 (s : real -> Prop) (x : real -> real) : (term357 s x) = (term358 s x).
Proof. exact (MK_COMB (@lem5182546 s) (@lem5182545 s x)). Qed.
Lemma lem5182548 (s : real -> Prop) : (term359 s) = (term360 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5182547 s x)). Qed.
Lemma lem5182549 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5182550 (s : real -> Prop) : (term351 s) = (term361 s).
Proof. exact (MK_COMB (@lem5182549) (@lem5182548 s)). Qed.
Lemma lem5182551 (s : real -> Prop) : ((term350 s) = (term351 s)) = ((term345 s) = (term361 s)).
Proof. exact (MK_COMB (@lem5182544 s) (@lem5182550 s)). Qed.
Lemma lem5182552 (s : real -> Prop) : (term345 s) = (term361 s).
Proof. exact (EQ_MP (@lem5182551 s) (@lem5182536 s)). Qed.
Lemma lem5182553 (s : real -> Prop) : (term303 s) = (term361 s).
Proof. exact (TRANS (@lem5182532 s) (@lem5182552 s)). Qed.
Lemma lem5182554 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5182555 (s : real -> Prop) : (term317 s) = (term362 s).
Proof. exact (MK_COMB (@lem5182554) (@lem5182553 s)). Qed.
Lemma lem5182557 {A : Type'} (P : A -> Prop) (Q : Prop) : (term220 A P Q) = (term221 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5182558 (P : real -> Prop) (Q : Prop) : (term222 P Q) = (term223 P Q).
Proof. exact (@lem5182557 real P Q). Qed.
Lemma lem5182559 (s : real -> Prop) (b : real) : (term363 s b) = (term364 s b).
Proof. exact (@lem5182558 (term291 s b) (term27 s b)). Qed.
Lemma lem5182560 (s : real -> Prop) (x : real) (b : real) : (term329 s b x) = (term285 s x b).
Proof. exact (eq_refl (term329 s b x)). Qed.
Lemma lem5182561 (s : real -> Prop) (b : real) : (term365 s b) = (term291 s b).
Proof. exact (fun_ext (fun x : real => @lem5182560 s x b)). Qed.
Lemma lem5182562 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5182563 (s : real -> Prop) (b : real) : (term366 s b) = (term292 s b).
Proof. exact (MK_COMB (@lem5182562) (@lem5182561 s b)). Qed.
Lemma lem5182564 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5182565 (s : real -> Prop) (b : real) : (term367 s b) = (term309 s b).
Proof. exact (MK_COMB (@lem5182564) (@lem5182563 s b)). Qed.
Lemma lem5182566 (s : real -> Prop) (b : real) : (term27 s b) = (term27 s b).
Proof. exact (eq_refl (term27 s b)). Qed.
Lemma lem5182567 (s : real -> Prop) (b : real) : (term363 s b) = (term311 s b).
Proof. exact (MK_COMB (@lem5182565 s b) (@lem5182566 s b)). Qed.
Lemma lem5182568 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5182569 (s : real -> Prop) (b : real) : (term368 s b) = (term369 s b).
Proof. exact (MK_COMB (@lem5182568) (@lem5182567 s b)). Qed.
Lemma lem5182570 (s : real -> Prop) (x : real) (b : real) : (term329 s b x) = (term285 s x b).
Proof. exact (eq_refl (term329 s b x)). Qed.
Lemma lem5182571 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5182572 (s : real -> Prop) (x : real) (b : real) : (term370 s b x) = (term371 s x b).
Proof. exact (MK_COMB (@lem5182571) (@lem5182570 s x b)). Qed.
Lemma lem5182573 (s : real -> Prop) (b : real) : (term27 s b) = (term27 s b).
Proof. exact (eq_refl (term27 s b)). Qed.
Lemma lem5182574 (x : real) (s : real -> Prop) (b : real) : (term372 x s b) = (term373 x s b).
Proof. exact (MK_COMB (@lem5182572 s x b) (@lem5182573 s b)). Qed.
Lemma lem5182575 (s : real -> Prop) (b : real) : (term374 s b) = (term375 s b).
Proof. exact (fun_ext (fun x : real => @lem5182574 x s b)). Qed.
Lemma lem5182576 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5182577 (s : real -> Prop) (b : real) : (term364 s b) = (term376 s b).
Proof. exact (MK_COMB (@lem5182576) (@lem5182575 s b)). Qed.
Lemma lem5182578 (s : real -> Prop) (b : real) : ((term363 s b) = (term364 s b)) = ((term311 s b) = (term376 s b)).
Proof. exact (MK_COMB (@lem5182569 s b) (@lem5182577 s b)). Qed.
Lemma lem5182579 (s : real -> Prop) (b : real) : (term311 s b) = (term376 s b).
Proof. exact (EQ_MP (@lem5182578 s b) (@lem5182559 s b)). Qed.
Lemma lem5182580 (s : real -> Prop) : (term312 s) = (term377 s).
Proof. exact (fun_ext (fun b : real => @lem5182579 s b)). Qed.
Lemma lem5182581 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5182582 (s : real -> Prop) : (term313 s) = (term378 s).
Proof. exact (MK_COMB (@lem5182581) (@lem5182580 s)). Qed.
Lemma lem5182584 {A B : Type'} (P : type1413 A B) : (term240 A B P) = (term241 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5182585 (P : type1626) : (term322 P) = (term323 P).
Proof. exact (@lem5182584 real real P). Qed.
Lemma lem5182586 (s : real -> Prop) : (term379 s) = (term380 s).
Proof. exact (@lem5182585 (term381 s)). Qed.
Lemma lem5182587 (s : real -> Prop) (b : real) : (term382 s b) = (term375 s b).
Proof. exact (eq_refl (term382 s b)). Qed.
Lemma lem5182588 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5182589 (s : real -> Prop) (b : real) (x : real) : (term383 s b x) = (term384 s b x).
Proof. exact (MK_COMB (@lem5182587 s b) (@lem5182588 x)). Qed.
Lemma lem5182590 (x : real) (s : real -> Prop) (b : real) : (term384 s b x) = (term373 x s b).
Proof. exact (eq_refl (term384 s b x)). Qed.
Lemma lem5182591 (x : real) (s : real -> Prop) (b : real) : (term383 s b x) = (term373 x s b).
Proof. exact (TRANS (@lem5182589 s b x) (@lem5182590 x s b)). Qed.
Lemma lem5182592 (s : real -> Prop) (b : real) : (term385 s b) = (term375 s b).
Proof. exact (fun_ext (fun x : real => @lem5182591 x s b)). Qed.
Lemma lem5182593 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5182594 (s : real -> Prop) (b : real) : (term386 s b) = (term376 s b).
Proof. exact (MK_COMB (@lem5182593) (@lem5182592 s b)). Qed.
Lemma lem5182595 (s : real -> Prop) : (term387 s) = (term377 s).
Proof. exact (fun_ext (fun b : real => @lem5182594 s b)). Qed.
Lemma lem5182596 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5182597 (s : real -> Prop) : (term379 s) = (term378 s).
Proof. exact (MK_COMB (@lem5182596) (@lem5182595 s)). Qed.
Lemma lem5182598 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5182599 (s : real -> Prop) : (term388 s) = (term389 s).
Proof. exact (MK_COMB (@lem5182598) (@lem5182597 s)). Qed.
Lemma lem5182600 (s : real -> Prop) (b : real) : (term382 s b) = (term375 s b).
Proof. exact (eq_refl (term382 s b)). Qed.
Lemma lem5182601 (x : real -> real) (b : real) : (x b) = (x b).
Proof. exact (eq_refl (x b)). Qed.
Lemma lem5182602 (s : real -> Prop) (x : real -> real) (b : real) : (term390 s x b) = (term391 s x b).
Proof. exact (MK_COMB (@lem5182600 s b) (@lem5182601 x b)). Qed.
Lemma lem5182603 (x : real -> real) (s : real -> Prop) (b : real) : (term391 s x b) = (term392 x s b).
Proof. exact (eq_refl (term391 s x b)). Qed.
Lemma lem5182604 (x : real -> real) (s : real -> Prop) (b : real) : (term390 s x b) = (term392 x s b).
Proof. exact (TRANS (@lem5182602 s x b) (@lem5182603 x s b)). Qed.
Lemma lem5182605 (x : real -> real) (s : real -> Prop) : (term393 s x) = (term394 x s).
Proof. exact (fun_ext (fun b : real => @lem5182604 x s b)). Qed.
Lemma lem5182606 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5182607 (x : real -> real) (s : real -> Prop) : (term395 s x) = (term396 x s).
Proof. exact (MK_COMB (@lem5182606) (@lem5182605 x s)). Qed.
Lemma lem5182608 (s : real -> Prop) : (term397 s) = (term398 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5182607 x s)). Qed.
Lemma lem5182609 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5182610 (s : real -> Prop) : (term380 s) = (term399 s).
Proof. exact (MK_COMB (@lem5182609) (@lem5182608 s)). Qed.
Lemma lem5182611 (s : real -> Prop) : ((term379 s) = (term380 s)) = ((term378 s) = (term399 s)).
Proof. exact (MK_COMB (@lem5182599 s) (@lem5182610 s)). Qed.
Lemma lem5182612 (s : real -> Prop) : (term378 s) = (term399 s).
Proof. exact (EQ_MP (@lem5182611 s) (@lem5182586 s)). Qed.
Lemma lem5182613 (s : real -> Prop) : (term313 s) = (term399 s).
Proof. exact (TRANS (@lem5182582 s) (@lem5182612 s)). Qed.
Lemma lem5182614 (s : real -> Prop) : (term314 s) = (term314 s).
Proof. exact (eq_refl (term314 s)). Qed.
Lemma lem5182615 (s : real -> Prop) : (term315 s) = (term400 s).
Proof. exact (MK_COMB (@lem5182614 s) (@lem5182613 s)). Qed.
Lemma lem5182617 {A : Type'} (P : Prop) (Q : A -> Prop) : (term401 A P Q) = (term402 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5182618 (P : Prop) (Q : type1028) : (term403 P Q) = (term404 P Q).
Proof. exact (@lem5182617 (real -> real) P Q). Qed.
Lemma lem5182619 (s : real -> Prop) : (term405 s) = (term406 s).
Proof. exact (@lem5182618 (term307 s) (term398 s)). Qed.
Lemma lem5182620 (x : real -> real) (s : real -> Prop) : (term407 s x) = (term396 x s).
Proof. exact (eq_refl (term407 s x)). Qed.
Lemma lem5182621 (s : real -> Prop) : (term408 s) = (term398 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5182620 x s)). Qed.
Lemma lem5182622 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5182623 (s : real -> Prop) : (term409 s) = (term399 s).
Proof. exact (MK_COMB (@lem5182622) (@lem5182621 s)). Qed.
Lemma lem5182624 (s : real -> Prop) : (term314 s) = (term314 s).
Proof. exact (eq_refl (term314 s)). Qed.
Lemma lem5182625 (s : real -> Prop) : (term405 s) = (term400 s).
Proof. exact (MK_COMB (@lem5182624 s) (@lem5182623 s)). Qed.
Lemma lem5182626 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5182627 (s : real -> Prop) : (term410 s) = (term411 s).
Proof. exact (MK_COMB (@lem5182626) (@lem5182625 s)). Qed.
Lemma lem5182628 (x : real -> real) (s : real -> Prop) : (term407 s x) = (term396 x s).
Proof. exact (eq_refl (term407 s x)). Qed.
Lemma lem5182629 (s : real -> Prop) : (term314 s) = (term314 s).
Proof. exact (eq_refl (term314 s)). Qed.
Lemma lem5182630 (x : real -> real) (s : real -> Prop) : (term412 s x) = (term413 x s).
Proof. exact (MK_COMB (@lem5182629 s) (@lem5182628 x s)). Qed.
Lemma lem5182631 (s : real -> Prop) : (term414 s) = (term415 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5182630 x s)). Qed.
Lemma lem5182632 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5182633 (s : real -> Prop) : (term406 s) = (term416 s).
Proof. exact (MK_COMB (@lem5182632) (@lem5182631 s)). Qed.
Lemma lem5182634 (s : real -> Prop) : ((term405 s) = (term406 s)) = ((term400 s) = (term416 s)).
Proof. exact (MK_COMB (@lem5182627 s) (@lem5182633 s)). Qed.
Lemma lem5182635 (s : real -> Prop) : (term400 s) = (term416 s).
Proof. exact (EQ_MP (@lem5182634 s) (@lem5182619 s)). Qed.
Lemma lem5182636 (s : real -> Prop) : (term315 s) = (term416 s).
Proof. exact (TRANS (@lem5182615 s) (@lem5182635 s)). Qed.
Lemma lem5182637 (s : real -> Prop) : (term319 s) = (term417 s).
Proof. exact (MK_COMB (@lem5182555 s) (@lem5182636 s)). Qed.
Lemma lem5182639 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term418 A P Q) = (term419 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5182640 (P : type1028) (Q : type1028) : (term420 P Q) = (term421 P Q).
Proof. exact (@lem5182639 (real -> real) P Q). Qed.
Lemma lem5182641 (s : real -> Prop) : (term422 s) = (term423 s).
Proof. exact (@lem5182640 (term360 s) (term415 s)). Qed.
Lemma lem5182642 (s : real -> Prop) (x : real -> real) : (term424 s x) = (term358 s x).
Proof. exact (eq_refl (term424 s x)). Qed.
Lemma lem5182643 (s : real -> Prop) : (term425 s) = (term360 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5182642 s x)). Qed.
Lemma lem5182644 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5182645 (s : real -> Prop) : (term426 s) = (term361 s).
Proof. exact (MK_COMB (@lem5182644) (@lem5182643 s)). Qed.
Lemma lem5182646 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5182647 (s : real -> Prop) : (term427 s) = (term362 s).
Proof. exact (MK_COMB (@lem5182646) (@lem5182645 s)). Qed.
Lemma lem5182648 (x : real -> real) (s : real -> Prop) : (term428 s x) = (term413 x s).
Proof. exact (eq_refl (term428 s x)). Qed.
Lemma lem5182649 (s : real -> Prop) : (term429 s) = (term415 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5182648 x s)). Qed.
Lemma lem5182650 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5182651 (s : real -> Prop) : (term430 s) = (term416 s).
Proof. exact (MK_COMB (@lem5182650) (@lem5182649 s)). Qed.
Lemma lem5182652 (s : real -> Prop) : (term422 s) = (term417 s).
Proof. exact (MK_COMB (@lem5182647 s) (@lem5182651 s)). Qed.
Lemma lem5182653 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5182654 (s : real -> Prop) : (term431 s) = (term432 s).
Proof. exact (MK_COMB (@lem5182653) (@lem5182652 s)). Qed.
Lemma lem5182655 (s : real -> Prop) (x : real -> real) : (term424 s x) = (term358 s x).
Proof. exact (eq_refl (term424 s x)). Qed.
Lemma lem5182656 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5182657 (s : real -> Prop) (x : real -> real) : (term433 s x) = (term434 s x).
Proof. exact (MK_COMB (@lem5182656) (@lem5182655 s x)). Qed.
Lemma lem5182658 (x : real -> real) (s : real -> Prop) : (term428 s x) = (term413 x s).
Proof. exact (eq_refl (term428 s x)). Qed.
Lemma lem5182659 (x : real -> real) (s : real -> Prop) : (term435 s x) = (term436 x s).
Proof. exact (MK_COMB (@lem5182657 s x) (@lem5182658 x s)). Qed.
Lemma lem5182660 (s : real -> Prop) : (term437 s) = (term438 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5182659 x s)). Qed.
Lemma lem5182661 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5182662 (s : real -> Prop) : (term423 s) = (term439 s).
Proof. exact (MK_COMB (@lem5182661) (@lem5182660 s)). Qed.
Lemma lem5182663 (s : real -> Prop) : ((term422 s) = (term423 s)) = ((term417 s) = (term439 s)).
Proof. exact (MK_COMB (@lem5182654 s) (@lem5182662 s)). Qed.
Lemma lem5182664 (s : real -> Prop) : (term417 s) = (term439 s).
Proof. exact (EQ_MP (@lem5182663 s) (@lem5182641 s)). Qed.
Lemma lem5182665 (s : real -> Prop) : (term319 s) = (term439 s).
Proof. exact (TRANS (@lem5182637 s) (@lem5182664 s)). Qed.
Lemma lem5182666 : term320 = term440.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5182665 s)). Qed.
Lemma lem5182667 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5182668 : term321 = term441.
Proof. exact (MK_COMB (@lem5182667) (@lem5182666)). Qed.
Lemma lem5182670 {A B : Type'} (P : type1413 A B) : (term240 A B P) = (term241 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5182671 (P : type1017) : (term442 P) = (term443 P).
Proof. exact (@lem5182670 (real -> Prop) (real -> real) P). Qed.
Lemma lem5182672 : term444 = term445.
Proof. exact (@lem5182671 term446). Qed.
Lemma lem5182673 (s : real -> Prop) : (term447 s) = (term438 s).
Proof. exact (eq_refl (term447 s)). Qed.
Lemma lem5182674 (x : real -> real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5182675 (s : real -> Prop) (x : real -> real) : (term448 s x) = (term449 s x).
Proof. exact (MK_COMB (@lem5182673 s) (@lem5182674 x)). Qed.
Lemma lem5182676 (x : real -> real) (s : real -> Prop) : (term449 s x) = (term436 x s).
Proof. exact (eq_refl (term449 s x)). Qed.
Lemma lem5182677 (x : real -> real) (s : real -> Prop) : (term448 s x) = (term436 x s).
Proof. exact (TRANS (@lem5182675 s x) (@lem5182676 x s)). Qed.
Lemma lem5182678 (s : real -> Prop) : (term450 s) = (term438 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5182677 x s)). Qed.
Lemma lem5182679 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5182680 (s : real -> Prop) : (term451 s) = (term439 s).
Proof. exact (MK_COMB (@lem5182679) (@lem5182678 s)). Qed.
Lemma lem5182681 : term452 = term440.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5182680 s)). Qed.
Lemma lem5182682 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5182683 : term444 = term441.
Proof. exact (MK_COMB (@lem5182682) (@lem5182681)). Qed.
Lemma lem5182684 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5182685 : term453 = term454.
Proof. exact (MK_COMB (@lem5182684) (@lem5182683)). Qed.
Lemma lem5182686 (s : real -> Prop) : (term447 s) = (term438 s).
Proof. exact (eq_refl (term447 s)). Qed.
Lemma lem5182687 (x : type1021) (s : real -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem5182688 (x : type1021) (s : real -> Prop) : (term455 x s) = (term456 x s).
Proof. exact (MK_COMB (@lem5182686 s) (@lem5182687 x s)). Qed.
Lemma lem5182689 (x : type1021) (s : real -> Prop) : (term456 x s) = (term457 x s).
Proof. exact (eq_refl (term456 x s)). Qed.
Lemma lem5182690 (x : type1021) (s : real -> Prop) : (term455 x s) = (term457 x s).
Proof. exact (TRANS (@lem5182688 x s) (@lem5182689 x s)). Qed.
Lemma lem5182691 (x : type1021) : (term458 x) = (term459 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5182690 x s)). Qed.
Lemma lem5182692 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5182693 (x : type1021) : (term460 x) = (term461 x).
Proof. exact (MK_COMB (@lem5182692) (@lem5182691 x)). Qed.
Lemma lem5182694 : term462 = term463.
Proof. exact (fun_ext (fun x : type1021 => @lem5182693 x)). Qed.
Lemma lem5182695 : (@ex ((real -> Prop) -> real -> real)) = (@ex ((real -> Prop) -> real -> real)).
Proof. exact (eq_refl (@ex ((real -> Prop) -> real -> real))). Qed.
Lemma lem5182696 : term445 = term464.
Proof. exact (MK_COMB (@lem5182695) (@lem5182694)). Qed.
Lemma lem5182697 : (term444 = term445) = (term441 = term464).
Proof. exact (MK_COMB (@lem5182685) (@lem5182696)). Qed.
Lemma lem5182698 : term441 = term464.
Proof. exact (EQ_MP (@lem5182697) (@lem5182672)). Qed.
Lemma lem5182700 : term321 = term464.
Proof. exact (TRANS (@lem5182668) (@lem5182698)). Qed.
Lemma lem5182701 : term18 = term464.
Proof. exact (TRANS (@lem5182255) (@lem5182700)). Qed.
Lemma lem5182702 (h1 : term18) : term464.
Proof. exact (EQ_MP (@lem5182701) (@lem5181353 h1)). Qed.
Lemma lem5182703 (x : type1021) (h1 : term461 x) : term461 x.
Proof. exact (h1). Qed.
Lemma lem5182704 (x' : type1023) (h1 : term280 x') : term280 x'.
Proof. exact (h1). Qed.
Lemma lem5182705 (s : real -> Prop) (h1 : term106 s) : term106 s.
Proof. exact (h1). Qed.
Lemma lem5182706 (a : real) (s : real -> Prop) (h1 : term99 a s) : term99 a s.
Proof. exact (h1). Qed.
Lemma lem5182707 (b : real) (a : real) (s : real -> Prop) (h1 : term92 b a s) : term92 b a s.
Proof. exact (h1). Qed.
Lemma lem5182708 (y : real) (b : real) (a : real) (s : real -> Prop) (h1 : term82 y b a s) : term82 y b a s.
Proof. exact (h1). Qed.
Lemma lem5182733 (y : real) (x : real) (z : real) : (term164 y x z) = (term164 y x z).
Proof. exact (eq_refl (term164 y x z)). Qed.
Lemma lem5182734 (y : real) (x : real) : (term166 y x) = (term166 y x).
Proof. exact (fun_ext (fun z : real => @lem5182733 y x z)). Qed.
Lemma lem5182735 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5182736 (y : real) (x : real) : (term167 y x) = (term167 y x).
Proof. exact (MK_COMB (@lem5182735) (@lem5182734 y x)). Qed.
Lemma lem5182737 (x : real) : (term168 x) = (term168 x).
Proof. exact (fun_ext (fun y : real => @lem5182736 y x)). Qed.
Lemma lem5182738 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5182739 (x : real) : (term169 x) = (term169 x).
Proof. exact (MK_COMB (@lem5182738) (@lem5182737 x)). Qed.
Lemma lem5182740 : term170 = term170.
Proof. exact (fun_ext (fun x : real => @lem5182739 x)). Qed.
Lemma lem5182741 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5182742 : term171 = term171.
Proof. exact (MK_COMB (@lem5182741) (@lem5182740)). Qed.
Lemma lem5182743 (h1 : term58) : term171.
Proof. exact (EQ_MP (@lem5182742) (@lem5181919 h1)). Qed.
Lemma lem5182776 (x : type1021) (s : real -> Prop) (b : real) : (term465 x s b) = (term465 x s b).
Proof. exact (eq_refl (term465 x s b)). Qed.
Lemma lem5182777 (x : type1021) (s : real -> Prop) : (term466 x s) = (term466 x s).
Proof. exact (fun_ext (fun b : real => @lem5182776 x s b)). Qed.
Lemma lem5182778 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5182779 (x : type1021) (s : real -> Prop) : (term467 x s) = (term467 x s).
Proof. exact (MK_COMB (@lem5182778) (@lem5182777 x s)). Qed.
Lemma lem5182796 (x : real) (s : real -> Prop) : (term305 x s) = (term305 x s).
Proof. exact (eq_refl (term305 x s)). Qed.
Lemma lem5182797 (s : real -> Prop) : (term306 s) = (term306 s).
Proof. exact (fun_ext (fun x : real => @lem5182796 x s)). Qed.
Lemma lem5182798 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5182799 (s : real -> Prop) : (term307 s) = (term307 s).
Proof. exact (MK_COMB (@lem5182798) (@lem5182797 s)). Qed.
Lemma lem5182800 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5182801 (s : real -> Prop) : (term314 s) = (term314 s).
Proof. exact (MK_COMB (@lem5182800) (@lem5182799 s)). Qed.
Lemma lem5182802 (x : type1021) (s : real -> Prop) : (term468 x s) = (term468 x s).
Proof. exact (MK_COMB (@lem5182801 s) (@lem5182779 x s)). Qed.
Lemma lem5182825 (x : type1021) (s : real -> Prop) (b : real) : (term469 x s b) = (term469 x s b).
Proof. exact (eq_refl (term469 x s b)). Qed.
Lemma lem5182826 (x : type1021) (s : real -> Prop) : (term470 x s) = (term470 x s).
Proof. exact (fun_ext (fun b : real => @lem5182825 x s b)). Qed.
Lemma lem5182827 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5182828 (x : type1021) (s : real -> Prop) : (term471 x s) = (term471 x s).
Proof. exact (MK_COMB (@lem5182827) (@lem5182826 x s)). Qed.
Lemma lem5182835 (s : real -> Prop) : (term301 s) = (term301 s).
Proof. exact (eq_refl (term301 s)). Qed.
Lemma lem5182836 (x : type1021) (s : real -> Prop) : (term472 x s) = (term472 x s).
Proof. exact (MK_COMB (@lem5182835 s) (@lem5182828 x s)). Qed.
Lemma lem5182837 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5182838 (x : type1021) (s : real -> Prop) : (term473 x s) = (term473 x s).
Proof. exact (MK_COMB (@lem5182837) (@lem5182836 x s)). Qed.
Lemma lem5182839 (x : type1021) (s : real -> Prop) : (term457 x s) = (term457 x s).
Proof. exact (MK_COMB (@lem5182838 x s) (@lem5182802 x s)). Qed.
Lemma lem5182840 (x : type1021) : (term459 x) = (term459 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5182839 x s)). Qed.
Lemma lem5182841 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5182842 (x : type1021) : (term461 x) = (term461 x).
Proof. exact (MK_COMB (@lem5182841) (@lem5182840 x)). Qed.
Lemma lem5182843 (x : type1021) (h1 : term461 x) : term461 x.
Proof. exact (EQ_MP (@lem5182842 x) (@lem5182703 x h1)). Qed.
Lemma lem5182850 (s : real -> Prop) : (term47 s) = (term47 s).
Proof. exact (eq_refl (term47 s)). Qed.
Lemma lem5182857 (x : real) (s : real -> Prop) : (term178 x s) = (term178 x s).
Proof. exact (eq_refl (term178 x s)). Qed.
Lemma lem5182858 (s : real -> Prop) : (term180 s) = (term180 s).
Proof. exact (fun_ext (fun x : real => @lem5182857 x s)). Qed.
Lemma lem5182859 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5182860 (s : real -> Prop) : (term181 s) = (term181 s).
Proof. exact (MK_COMB (@lem5182859) (@lem5182858 s)). Qed.
Lemma lem5182861 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5182862 (s : real -> Prop) : (term184 s) = (term184 s).
Proof. exact (MK_COMB (@lem5182861) (@lem5182860 s)). Qed.
Lemma lem5182863 (s : real -> Prop) : (term186 s) = (term186 s).
Proof. exact (MK_COMB (@lem5182862 s) (@lem5182850 s)). Qed.
Lemma lem5182864 : term203 = term203.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5182863 s)). Qed.
Lemma lem5182865 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5182866 : term218 = term218.
Proof. exact (MK_COMB (@lem5182865) (@lem5182864)). Qed.
Lemma lem5182881 (x' : type1023) (s : real -> Prop) : (term257 x' s) = (term257 x' s).
Proof. exact (eq_refl (term257 x' s)). Qed.
Lemma lem5182882 (x' : type1023) : (term259 x') = (term259 x').
Proof. exact (fun_ext (fun s : real -> Prop => @lem5182881 x' s)). Qed.
Lemma lem5182883 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5182884 (x' : type1023) : (term261 x') = (term261 x').
Proof. exact (MK_COMB (@lem5182883) (@lem5182882 x')). Qed.
Lemma lem5182885 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5182886 (x' : type1023) : (term278 x') = (term278 x').
Proof. exact (MK_COMB (@lem5182885) (@lem5182884 x')). Qed.
Lemma lem5182887 (x' : type1023) : (term280 x') = (term280 x').
Proof. exact (MK_COMB (@lem5182886 x') (@lem5182866)). Qed.
Lemma lem5182888 (x' : type1023) (h1 : term280 x') : term280 x'.
Proof. exact (EQ_MP (@lem5182887 x') (@lem5182704 x' h1)). Qed.
Lemma lem5182897 (a : real) (s : real -> Prop) : (term78 a s) = (term78 a s).
Proof. exact (eq_refl (term78 a s)). Qed.
Lemma lem5182912 (s : real -> Prop) (x : real) (b : real) : (term73 s x b) = (term73 s x b).
Proof. exact (eq_refl (term73 s x b)). Qed.
Lemma lem5182913 (s : real -> Prop) (b : real) : (term74 s b) = (term74 s b).
Proof. exact (fun_ext (fun x : real => @lem5182912 s x b)). Qed.
Lemma lem5182914 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5182915 (s : real -> Prop) (b : real) : (term75 s b) = (term75 s b).
Proof. exact (MK_COMB (@lem5182914) (@lem5182913 s b)). Qed.
Lemma lem5182922 (a : real) (y : real) : (term60 a y) = (term60 a y).
Proof. exact (eq_refl (term60 a y)). Qed.
Lemma lem5182923 (a : real) (y : real) (s : real -> Prop) (b : real) : (term76 a y s b) = (term76 a y s b).
Proof. exact (MK_COMB (@lem5182922 a y) (@lem5182915 s b)). Qed.
Lemma lem5182930 (y : real) (s : real -> Prop) : (term62 y s) = (term62 y s).
Proof. exact (eq_refl (term62 y s)). Qed.
Lemma lem5182931 (a : real) (y : real) (s : real -> Prop) (b : real) : (term77 a y s b) = (term77 a y s b).
Proof. exact (MK_COMB (@lem5182930 y s) (@lem5182923 a y s b)). Qed.
Lemma lem5182932 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5182933 (a : real) (y : real) (s : real -> Prop) (b : real) : (term80 a y s b) = (term80 a y s b).
Proof. exact (MK_COMB (@lem5182932) (@lem5182931 a y s b)). Qed.
Lemma lem5182934 (y : real) (b : real) (a : real) (s : real -> Prop) : (term82 y b a s) = (term82 y b a s).
Proof. exact (MK_COMB (@lem5182933 a y s b) (@lem5182897 a s)). Qed.
Lemma lem5182935 (y : real) (b : real) (a : real) (s : real -> Prop) (h1 : term82 y b a s) : term82 y b a s.
Proof. exact (EQ_MP (@lem5182934 y b a s) (@lem5182708 y b a s h1)). Qed.
Lemma lem5182937 (y : real) (b : real) (a : real) (s : real -> Prop) (h1 : term82 y b a s) : term77 a y s b.
Proof. exact (proj1 (@lem5182935 y b a s h1)). Qed.
Lemma lem5182938 (y : real) (b : real) (a : real) (s : real -> Prop) (h1 : term82 y b a s) : term76 a y s b.
Proof. exact (proj2 (@lem5182937 y b a s h1)). Qed.
Lemma lem5182940 (y : real) (b : real) (a : real) (s : real -> Prop) (h1 : term82 y b a s) : term75 s b.
Proof. exact (proj2 (@lem5182938 y b a s h1)). Qed.
Lemma lem5182942 (x' : type1023) (h1 : term280 x') : term218.
Proof. exact (proj2 (@lem5182888 x' h1)). Qed.
Lemma lem5182957 (y : real) (x : real) (z : real) : (term164 y x z) = (term164 y x z).
Proof. exact (eq_refl (term164 y x z)). Qed.
Lemma lem5182958 (y : real) (x : real) : (term166 y x) = (term166 y x).
Proof. exact (fun_ext (fun z : real => @lem5182957 y x z)). Qed.
Lemma lem5182959 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5182960 (y : real) (x : real) : (term167 y x) = (term167 y x).
Proof. exact (MK_COMB (@lem5182959) (@lem5182958 y x)). Qed.
Lemma lem5182961 (x : real) : (term168 x) = (term168 x).
Proof. exact (fun_ext (fun y : real => @lem5182960 y x)). Qed.
Lemma lem5182962 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5182963 (x : real) : (term169 x) = (term169 x).
Proof. exact (MK_COMB (@lem5182962) (@lem5182961 x)). Qed.
Lemma lem5182964 : term170 = term170.
Proof. exact (fun_ext (fun x : real => @lem5182963 x)). Qed.
Lemma lem5182965 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5182967 : term171 = term171.
Proof. exact (MK_COMB (@lem5182965) (@lem5182964)). Qed.
Lemma lem5182968 (h1 : term58) : term171.
Proof. exact (EQ_MP (@lem5182967) (@lem5182743 h1)). Qed.
Lemma lem5182970 {A : Type'} (P : Prop) (Q : A -> Prop) : (term474 A P Q) = (term475 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5182971 (P : Prop) (Q : real -> Prop) : (term476 P Q) = (term477 P Q).
Proof. exact (@lem5182970 real P Q). Qed.
Lemma lem5182972 (x : type1021) (s : real -> Prop) : (term478 x s) = (term479 x s).
Proof. exact (@lem5182971 (s = (@EMPTY real)) (term470 x s)). Qed.
Lemma lem5182973 (x : type1021) (s : real -> Prop) (b : real) : (term480 x s b) = (term469 x s b).
Proof. exact (eq_refl (term480 x s b)). Qed.
Lemma lem5182974 (x : type1021) (s : real -> Prop) : (term481 x s) = (term470 x s).
Proof. exact (fun_ext (fun b : real => @lem5182973 x s b)). Qed.
Lemma lem5182975 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5182976 (x : type1021) (s : real -> Prop) : (term482 x s) = (term471 x s).
Proof. exact (MK_COMB (@lem5182975) (@lem5182974 x s)). Qed.
Lemma lem5182977 (s : real -> Prop) : (term301 s) = (term301 s).
Proof. exact (eq_refl (term301 s)). Qed.
Lemma lem5182978 (x : type1021) (s : real -> Prop) : (term478 x s) = (term472 x s).
Proof. exact (MK_COMB (@lem5182977 s) (@lem5182976 x s)). Qed.
Lemma lem5182979 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5182980 (x : type1021) (s : real -> Prop) : (term483 x s) = (term484 x s).
Proof. exact (MK_COMB (@lem5182979) (@lem5182978 x s)). Qed.
Lemma lem5182981 (x : type1021) (s : real -> Prop) (b : real) : (term480 x s b) = (term469 x s b).
Proof. exact (eq_refl (term480 x s b)). Qed.
Lemma lem5182982 (s : real -> Prop) : (term301 s) = (term301 s).
Proof. exact (eq_refl (term301 s)). Qed.
Lemma lem5182983 (x : type1021) (s : real -> Prop) (b : real) : (term485 x s b) = (term486 x s b).
Proof. exact (MK_COMB (@lem5182982 s) (@lem5182981 x s b)). Qed.
Lemma lem5182984 (x : type1021) (s : real -> Prop) : (term487 x s) = (term488 x s).
Proof. exact (fun_ext (fun b : real => @lem5182983 x s b)). Qed.
Lemma lem5182985 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5182986 (x : type1021) (s : real -> Prop) : (term479 x s) = (term489 x s).
Proof. exact (MK_COMB (@lem5182985) (@lem5182984 x s)). Qed.
Lemma lem5182987 (x : type1021) (s : real -> Prop) : ((term478 x s) = (term479 x s)) = ((term472 x s) = (term489 x s)).
Proof. exact (MK_COMB (@lem5182980 x s) (@lem5182986 x s)). Qed.
Lemma lem5182988 (x : type1021) (s : real -> Prop) : (term472 x s) = (term489 x s).
Proof. exact (EQ_MP (@lem5182987 x s) (@lem5182972 x s)). Qed.
Lemma lem5182989 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5182990 (x : type1021) (s : real -> Prop) : (term473 x s) = (term490 x s).
Proof. exact (MK_COMB (@lem5182989) (@lem5182988 x s)). Qed.
Lemma lem5182992 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term197 A P Q) = (term196 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem5182993 (P : real -> Prop) (Q : real -> Prop) : (term491 P Q) = (term492 P Q).
Proof. exact (@lem5182992 real P Q). Qed.
Lemma lem5182994 (x : type1021) (s : real -> Prop) : (term493 x s) = (term494 x s).
Proof. exact (@lem5182993 (term306 s) (term466 x s)). Qed.
Lemma lem5182995 (b : real) (s : real -> Prop) : (term495 s b) = (term305 b s).
Proof. exact (eq_refl (term495 s b)). Qed.
Lemma lem5182996 (s : real -> Prop) : (term496 s) = (term306 s).
Proof. exact (fun_ext (fun b : real => @lem5182995 b s)). Qed.
Lemma lem5182997 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5182998 (s : real -> Prop) : (term497 s) = (term307 s).
Proof. exact (MK_COMB (@lem5182997) (@lem5182996 s)). Qed.
Lemma lem5182999 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5183000 (s : real -> Prop) : (term498 s) = (term314 s).
Proof. exact (MK_COMB (@lem5182999) (@lem5182998 s)). Qed.
Lemma lem5183001 (x : type1021) (s : real -> Prop) (b : real) : (term499 x s b) = (term465 x s b).
Proof. exact (eq_refl (term499 x s b)). Qed.
Lemma lem5183002 (x : type1021) (s : real -> Prop) : (term500 x s) = (term466 x s).
Proof. exact (fun_ext (fun b : real => @lem5183001 x s b)). Qed.
Lemma lem5183003 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5183004 (x : type1021) (s : real -> Prop) : (term501 x s) = (term467 x s).
Proof. exact (MK_COMB (@lem5183003) (@lem5183002 x s)). Qed.
Lemma lem5183005 (x : type1021) (s : real -> Prop) : (term493 x s) = (term468 x s).
Proof. exact (MK_COMB (@lem5183000 s) (@lem5183004 x s)). Qed.
Lemma lem5183006 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5183007 (x : type1021) (s : real -> Prop) : (term502 x s) = (term503 x s).
Proof. exact (MK_COMB (@lem5183006) (@lem5183005 x s)). Qed.
Lemma lem5183008 (b : real) (s : real -> Prop) : (term495 s b) = (term305 b s).
Proof. exact (eq_refl (term495 s b)). Qed.
Lemma lem5183009 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5183010 (b : real) (s : real -> Prop) : (term504 s b) = (term505 b s).
Proof. exact (MK_COMB (@lem5183009) (@lem5183008 b s)). Qed.
Lemma lem5183011 (x : type1021) (s : real -> Prop) (b : real) : (term499 x s b) = (term465 x s b).
Proof. exact (eq_refl (term499 x s b)). Qed.
Lemma lem5183012 (x : type1021) (s : real -> Prop) (b : real) : (term506 x s b) = (term507 x s b).
Proof. exact (MK_COMB (@lem5183010 b s) (@lem5183011 x s b)). Qed.
Lemma lem5183013 (x : type1021) (s : real -> Prop) : (term508 x s) = (term509 x s).
Proof. exact (fun_ext (fun b : real => @lem5183012 x s b)). Qed.
Lemma lem5183014 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5183015 (x : type1021) (s : real -> Prop) : (term494 x s) = (term510 x s).
Proof. exact (MK_COMB (@lem5183014) (@lem5183013 x s)). Qed.
Lemma lem5183016 (x : type1021) (s : real -> Prop) : ((term493 x s) = (term494 x s)) = ((term468 x s) = (term510 x s)).
Proof. exact (MK_COMB (@lem5183007 x s) (@lem5183015 x s)). Qed.
Lemma lem5183017 (x : type1021) (s : real -> Prop) : (term468 x s) = (term510 x s).
Proof. exact (EQ_MP (@lem5183016 x s) (@lem5182994 x s)). Qed.
Lemma lem5183020 (x : type1021) (s : real -> Prop) : (term511 x s) = (term511 x s).
Proof. exact (eq_refl (term511 x s)). Qed.
Lemma lem5183021 (x : type1021) (s : real -> Prop) : (term511 x s) = ((term468 x s) = (term510 x s)).
Proof. exact (eq_refl (term511 x s)). Qed.
Lemma lem5183022 (x : type1021) (s : real -> Prop) : (term512 x s) = (term512 x s).
Proof. exact (eq_refl (term512 x s)). Qed.
Lemma lem5183023 (x : type1021) (s : real -> Prop) : ((term511 x s) = (term511 x s)) = ((term511 x s) = ((term468 x s) = (term510 x s))).
Proof. exact (MK_COMB (@lem5183022 x s) (@lem5183021 x s)). Qed.
Lemma lem5183024 (x : type1021) (s : real -> Prop) : (term511 x s) = ((term468 x s) = (term510 x s)).
Proof. exact (eq_refl (term511 x s)). Qed.
Lemma lem5183025 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5183026 (x : type1021) (s : real -> Prop) : (term512 x s) = (term513 x s).
Proof. exact (MK_COMB (@lem5183025) (@lem5183024 x s)). Qed.
Lemma lem5183027 (x : type1021) (s : real -> Prop) : ((term468 x s) = (term510 x s)) = ((term468 x s) = (term510 x s)).
Proof. exact (eq_refl ((term468 x s) = (term510 x s))). Qed.
Lemma lem5183028 (x : type1021) (s : real -> Prop) : ((term511 x s) = ((term468 x s) = (term510 x s))) = (((term468 x s) = (term510 x s)) = ((term468 x s) = (term510 x s))).
Proof. exact (MK_COMB (@lem5183026 x s) (@lem5183027 x s)). Qed.
Lemma lem5183029 (x : type1021) (s : real -> Prop) : ((term511 x s) = (term511 x s)) = (((term468 x s) = (term510 x s)) = ((term468 x s) = (term510 x s))).
Proof. exact (TRANS (@lem5183023 x s) (@lem5183028 x s)). Qed.
Lemma lem5183030 (x : type1021) (s : real -> Prop) : ((term468 x s) = (term510 x s)) = ((term468 x s) = (term510 x s)).
Proof. exact (EQ_MP (@lem5183029 x s) (@lem5183020 x s)). Qed.
Lemma lem5183031 (x : type1021) (s : real -> Prop) : (term468 x s) = (term510 x s).
Proof. exact (EQ_MP (@lem5183030 x s) (@lem5183017 x s)). Qed.
Lemma lem5183032 (x : type1021) (s : real -> Prop) : (term457 x s) = (term514 x s).
Proof. exact (MK_COMB (@lem5182990 x s) (@lem5183031 x s)). Qed.
Lemma lem5183034 {A : Type'} (P : A -> Prop) (Q : Prop) : (term515 A P Q) = (term516 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem5183035 (P : real -> Prop) (Q : Prop) : (term517 P Q) = (term518 P Q).
Proof. exact (@lem5183034 real P Q). Qed.
Lemma lem5183036 (x : type1021) (s : real -> Prop) : (term519 x s) = (term520 x s).
Proof. exact (@lem5183035 (term488 x s) (term510 x s)). Qed.
Lemma lem5183037 (x : type1021) (s : real -> Prop) (b : real) : (term521 x s b) = (term486 x s b).
Proof. exact (eq_refl (term521 x s b)). Qed.
Lemma lem5183038 (x : type1021) (s : real -> Prop) : (term522 x s) = (term488 x s).
Proof. exact (fun_ext (fun b : real => @lem5183037 x s b)). Qed.
Lemma lem5183039 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5183040 (x : type1021) (s : real -> Prop) : (term523 x s) = (term489 x s).
Proof. exact (MK_COMB (@lem5183039) (@lem5183038 x s)). Qed.
Lemma lem5183041 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5183042 (x : type1021) (s : real -> Prop) : (term524 x s) = (term490 x s).
Proof. exact (MK_COMB (@lem5183041) (@lem5183040 x s)). Qed.
Lemma lem5183043 (x : type1021) (s : real -> Prop) : (term510 x s) = (term510 x s).
Proof. exact (eq_refl (term510 x s)). Qed.
Lemma lem5183044 (x : type1021) (s : real -> Prop) : (term519 x s) = (term514 x s).
Proof. exact (MK_COMB (@lem5183042 x s) (@lem5183043 x s)). Qed.
Lemma lem5183045 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5183046 (x : type1021) (s : real -> Prop) : (term525 x s) = (term526 x s).
Proof. exact (MK_COMB (@lem5183045) (@lem5183044 x s)). Qed.
Lemma lem5183047 (x : type1021) (s : real -> Prop) (b : real) : (term521 x s b) = (term486 x s b).
Proof. exact (eq_refl (term521 x s b)). Qed.
Lemma lem5183048 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5183049 (x : type1021) (s : real -> Prop) (b : real) : (term527 x s b) = (term528 x s b).
Proof. exact (MK_COMB (@lem5183048) (@lem5183047 x s b)). Qed.
Lemma lem5183050 (x : type1021) (s : real -> Prop) : (term510 x s) = (term510 x s).
Proof. exact (eq_refl (term510 x s)). Qed.
Lemma lem5183051 (b : real) (x : type1021) (s : real -> Prop) : (term529 b x s) = (term530 b x s).
Proof. exact (MK_COMB (@lem5183049 x s b) (@lem5183050 x s)). Qed.
Lemma lem5183052 (x : type1021) (s : real -> Prop) : (term531 x s) = (term532 x s).
Proof. exact (fun_ext (fun b : real => @lem5183051 b x s)). Qed.
Lemma lem5183053 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5183054 (x : type1021) (s : real -> Prop) : (term520 x s) = (term533 x s).
Proof. exact (MK_COMB (@lem5183053) (@lem5183052 x s)). Qed.
Lemma lem5183055 (x : type1021) (s : real -> Prop) : ((term519 x s) = (term520 x s)) = ((term514 x s) = (term533 x s)).
Proof. exact (MK_COMB (@lem5183046 x s) (@lem5183054 x s)). Qed.
Lemma lem5183056 (x : type1021) (s : real -> Prop) : (term514 x s) = (term533 x s).
Proof. exact (EQ_MP (@lem5183055 x s) (@lem5183036 x s)). Qed.
Lemma lem5183058 {A : Type'} (P : Prop) (Q : A -> Prop) : (term474 A P Q) = (term475 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5183059 (P : Prop) (Q : real -> Prop) : (term476 P Q) = (term477 P Q).
Proof. exact (@lem5183058 real P Q). Qed.
Lemma lem5183060 (b : real) (x : type1021) (s : real -> Prop) : (term534 b x s) = (term535 b x s).
Proof. exact (@lem5183059 (term486 x s b) (term509 x s)). Qed.
Lemma lem5183061 (x : type1021) (s : real -> Prop) (b : real) : (term536 x s b) = (term507 x s b).
Proof. exact (eq_refl (term536 x s b)). Qed.
Lemma lem5183062 (x : type1021) (s : real -> Prop) : (term537 x s) = (term509 x s).
Proof. exact (fun_ext (fun b : real => @lem5183061 x s b)). Qed.
Lemma lem5183063 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5183064 (x : type1021) (s : real -> Prop) : (term538 x s) = (term510 x s).
Proof. exact (MK_COMB (@lem5183063) (@lem5183062 x s)). Qed.
Lemma lem5183065 (x : type1021) (s : real -> Prop) (b : real) : (term528 x s b) = (term528 x s b).
Proof. exact (eq_refl (term528 x s b)). Qed.
Lemma lem5183066 (b : real) (x : type1021) (s : real -> Prop) : (term534 b x s) = (term530 b x s).
Proof. exact (MK_COMB (@lem5183065 x s b) (@lem5183064 x s)). Qed.
Lemma lem5183067 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5183068 (b : real) (x : type1021) (s : real -> Prop) : (term539 b x s) = (term540 b x s).
Proof. exact (MK_COMB (@lem5183067) (@lem5183066 b x s)). Qed.
Lemma lem5183069 (x : type1021) (s : real -> Prop) (b' : real) : (term536 x s b') = (term507 x s b').
Proof. exact (eq_refl (term536 x s b')). Qed.
Lemma lem5183070 (x : type1021) (s : real -> Prop) (b : real) : (term528 x s b) = (term528 x s b).
Proof. exact (eq_refl (term528 x s b)). Qed.
Lemma lem5183071 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term541 b x s b') = (term542 b x s b').
Proof. exact (MK_COMB (@lem5183070 x s b) (@lem5183069 x s b')). Qed.
Lemma lem5183072 (b : real) (x : type1021) (s : real -> Prop) : (term543 b x s) = (term544 b x s).
Proof. exact (fun_ext (fun b' : real => @lem5183071 b x s b')). Qed.
Lemma lem5183073 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5183074 (b : real) (x : type1021) (s : real -> Prop) : (term535 b x s) = (term545 b x s).
Proof. exact (MK_COMB (@lem5183073) (@lem5183072 b x s)). Qed.
Lemma lem5183075 (b : real) (x : type1021) (s : real -> Prop) : ((term534 b x s) = (term535 b x s)) = ((term530 b x s) = (term545 b x s)).
Proof. exact (MK_COMB (@lem5183068 b x s) (@lem5183074 b x s)). Qed.
Lemma lem5183076 (b : real) (x : type1021) (s : real -> Prop) : (term530 b x s) = (term545 b x s).
Proof. exact (EQ_MP (@lem5183075 b x s) (@lem5183060 b x s)). Qed.
Lemma lem5183077 (x : type1021) (s : real -> Prop) : (term532 x s) = (term546 x s).
Proof. exact (fun_ext (fun b : real => @lem5183076 b x s)). Qed.
Lemma lem5183078 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5183079 (x : type1021) (s : real -> Prop) : (term533 x s) = (term547 x s).
Proof. exact (MK_COMB (@lem5183078) (@lem5183077 x s)). Qed.
Lemma lem5183080 (x : type1021) (s : real -> Prop) : (term514 x s) = (term547 x s).
Proof. exact (TRANS (@lem5183056 x s) (@lem5183079 x s)). Qed.
Lemma lem5183081 (x : type1021) (s : real -> Prop) : (term457 x s) = (term547 x s).
Proof. exact (TRANS (@lem5183032 x s) (@lem5183080 x s)). Qed.
Lemma lem5183082 (x : type1021) : (term459 x) = (term548 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5183081 x s)). Qed.
Lemma lem5183083 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5183084 (x : type1021) : (term461 x) = (term549 x).
Proof. exact (MK_COMB (@lem5183083) (@lem5183082 x)). Qed.
Lemma lem5183101 (x : type1021) (s : real -> Prop) (b' : real) : (term465 x s b') = (term550 x s b').
Proof. exact (@lem19699 (term551 x b' s) (term552 x s b') (term27 s b')). Qed.
Lemma lem5183110 (b' : real) (s : real -> Prop) : (term505 b' s) = (term505 b' s).
Proof. exact (eq_refl (term505 b' s)). Qed.
Lemma lem5183111 (x : type1021) (s : real -> Prop) (b' : real) : (term507 x s b') = (term553 x s b').
Proof. exact (MK_COMB (@lem5183110 b' s) (@lem5183101 x s b')). Qed.
Lemma lem5183128 (x : type1021) (s : real -> Prop) (b : real) : (term486 x s b) = (term554 x s b).
Proof. exact (@lem19490 (term551 x b s) (s = (@EMPTY real)) (term552 x s b)). Qed.
Lemma lem5183129 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5183130 (x : type1021) (s : real -> Prop) (b : real) : (term528 x s b) = (term555 x s b).
Proof. exact (MK_COMB (@lem5183129) (@lem5183128 x s b)). Qed.
Lemma lem5183131 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term542 b x s b') = (term556 b x s b').
Proof. exact (MK_COMB (@lem5183130 x s b) (@lem5183111 x s b')). Qed.
Lemma lem5183132 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term556 b x s b') = (term557 b x s b').
Proof. exact (@lem19490 (term305 b' s) (term554 x s b) (term550 x s b')). Qed.
Lemma lem5183133 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term558 b x s b') = (term559 b x s b').
Proof. exact (@lem19490 (term560 x s b') (term554 x s b) (term561 x s b')). Qed.
Lemma lem5183140 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term562 b x s b') = (term563 b x s b').
Proof. exact (@lem19699 (term564 x b s) (term565 x s b) (term561 x s b')). Qed.
Lemma lem5183147 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term566 b x s b') = (term567 b x s b').
Proof. exact (@lem19699 (term564 x b s) (term565 x s b) (term560 x s b')). Qed.
Lemma lem5183148 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5183149 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term568 b x s b') = (term569 b x s b').
Proof. exact (MK_COMB (@lem5183148) (@lem5183147 b x s b')). Qed.
Lemma lem5183150 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term559 b x s b') = (term570 b x s b').
Proof. exact (MK_COMB (@lem5183149 b x s b') (@lem5183140 b x s b')). Qed.
Lemma lem5183151 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term558 b x s b') = (term570 b x s b').
Proof. exact (TRANS (@lem5183133 b x s b') (@lem5183150 b x s b')). Qed.
Lemma lem5183158 (x : type1021) (b : real) (b' : real) (s : real -> Prop) : (term571 x b b' s) = (term572 x b b' s).
Proof. exact (@lem19699 (term564 x b s) (term565 x s b) (term305 b' s)). Qed.
Lemma lem5183159 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5183160 (x : type1021) (b : real) (b' : real) (s : real -> Prop) : (term573 x b b' s) = (term574 x b b' s).
Proof. exact (MK_COMB (@lem5183159) (@lem5183158 x b b' s)). Qed.
Lemma lem5183161 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term557 b x s b') = (term575 b x s b').
Proof. exact (MK_COMB (@lem5183160 x b b' s) (@lem5183151 b x s b')). Qed.
Lemma lem5183162 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term556 b x s b') = (term575 b x s b').
Proof. exact (TRANS (@lem5183132 b x s b') (@lem5183161 b x s b')). Qed.
Lemma lem5183163 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term542 b x s b') = (term575 b x s b').
Proof. exact (TRANS (@lem5183131 b x s b') (@lem5183162 b x s b')). Qed.
Lemma lem5183164 (b : real) (x : type1021) (s : real -> Prop) : (term544 b x s) = (term576 b x s).
Proof. exact (fun_ext (fun b' : real => @lem5183163 b x s b')). Qed.
Lemma lem5183165 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5183166 (b : real) (x : type1021) (s : real -> Prop) : (term545 b x s) = (term577 b x s).
Proof. exact (MK_COMB (@lem5183165) (@lem5183164 b x s)). Qed.
Lemma lem5183167 (x : type1021) (s : real -> Prop) : (term546 x s) = (term578 x s).
Proof. exact (fun_ext (fun b : real => @lem5183166 b x s)). Qed.
Lemma lem5183168 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5183169 (x : type1021) (s : real -> Prop) : (term547 x s) = (term579 x s).
Proof. exact (MK_COMB (@lem5183168) (@lem5183167 x s)). Qed.
Lemma lem5183170 (x : type1021) : (term548 x) = (term580 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5183169 x s)). Qed.
Lemma lem5183171 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5183172 (x : type1021) : (term549 x) = (term581 x).
Proof. exact (MK_COMB (@lem5183171) (@lem5183170 x)). Qed.
Lemma lem5183173 (x : type1021) : (term461 x) = (term581 x).
Proof. exact (TRANS (@lem5183084 x) (@lem5183172 x)). Qed.
Lemma lem5183174 (x : type1021) (h1 : term461 x) : term581 x.
Proof. exact (EQ_MP (@lem5183173 x) (@lem5182843 x h1)). Qed.
Lemma lem5183194 (s : real -> Prop) (x : real) (b : real) : (term73 s x b) = (term73 s x b).
Proof. exact (eq_refl (term73 s x b)). Qed.
Lemma lem5183195 (s : real -> Prop) (b : real) : (term74 s b) = (term74 s b).
Proof. exact (fun_ext (fun x : real => @lem5183194 s x b)). Qed.
Lemma lem5183196 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5183198 (s : real -> Prop) (b : real) : (term75 s b) = (term75 s b).
Proof. exact (MK_COMB (@lem5183196) (@lem5183195 s b)). Qed.
Lemma lem5183199 (y : real) (b : real) (a : real) (s : real -> Prop) (h1 : term82 y b a s) : term75 s b.
Proof. exact (EQ_MP (@lem5183198 s b) (@lem5182940 y b a s h1)). Qed.
Lemma lem5183214 {A : Type'} (P : A -> Prop) (Q : Prop) : (term515 A P Q) = (term516 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem5183215 (P : real -> Prop) (Q : Prop) : (term517 P Q) = (term518 P Q).
Proof. exact (@lem5183214 real P Q). Qed.
Lemma lem5183216 (s : real -> Prop) : (term582 s) = (term583 s).
Proof. exact (@lem5183215 (term180 s) (term47 s)). Qed.
Lemma lem5183217 (x : real) (s : real -> Prop) : (term584 s x) = (term178 x s).
Proof. exact (eq_refl (term584 s x)). Qed.
Lemma lem5183218 (s : real -> Prop) : (term585 s) = (term180 s).
Proof. exact (fun_ext (fun x : real => @lem5183217 x s)). Qed.
Lemma lem5183219 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5183220 (s : real -> Prop) : (term586 s) = (term181 s).
Proof. exact (MK_COMB (@lem5183219) (@lem5183218 s)). Qed.
Lemma lem5183221 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5183222 (s : real -> Prop) : (term587 s) = (term184 s).
Proof. exact (MK_COMB (@lem5183221) (@lem5183220 s)). Qed.
Lemma lem5183223 (s : real -> Prop) : (term47 s) = (term47 s).
Proof. exact (eq_refl (term47 s)). Qed.
Lemma lem5183224 (s : real -> Prop) : (term582 s) = (term186 s).
Proof. exact (MK_COMB (@lem5183222 s) (@lem5183223 s)). Qed.
Lemma lem5183225 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5183226 (s : real -> Prop) : (term588 s) = (term589 s).
Proof. exact (MK_COMB (@lem5183225) (@lem5183224 s)). Qed.
Lemma lem5183227 (x : real) (s : real -> Prop) : (term584 s x) = (term178 x s).
Proof. exact (eq_refl (term584 s x)). Qed.
Lemma lem5183228 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5183229 (x : real) (s : real -> Prop) : (term590 s x) = (term591 x s).
Proof. exact (MK_COMB (@lem5183228) (@lem5183227 x s)). Qed.
Lemma lem5183230 (s : real -> Prop) : (term47 s) = (term47 s).
Proof. exact (eq_refl (term47 s)). Qed.
Lemma lem5183231 (x : real) (s : real -> Prop) : (term592 x s) = (term593 x s).
Proof. exact (MK_COMB (@lem5183229 x s) (@lem5183230 s)). Qed.
Lemma lem5183232 (s : real -> Prop) : (term594 s) = (term595 s).
Proof. exact (fun_ext (fun x : real => @lem5183231 x s)). Qed.
Lemma lem5183233 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5183234 (s : real -> Prop) : (term583 s) = (term596 s).
Proof. exact (MK_COMB (@lem5183233) (@lem5183232 s)). Qed.
Lemma lem5183235 (s : real -> Prop) : ((term582 s) = (term583 s)) = ((term186 s) = (term596 s)).
Proof. exact (MK_COMB (@lem5183226 s) (@lem5183234 s)). Qed.
Lemma lem5183236 (s : real -> Prop) : (term186 s) = (term596 s).
Proof. exact (EQ_MP (@lem5183235 s) (@lem5183216 s)). Qed.
Lemma lem5183237 : term203 = term597.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5183236 s)). Qed.
Lemma lem5183238 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5183239 : term218 = term598.
Proof. exact (MK_COMB (@lem5183238) (@lem5183237)). Qed.
Lemma lem5183246 (x : real) (s : real -> Prop) : (term593 x s) = (term593 x s).
Proof. exact (eq_refl (term593 x s)). Qed.
Lemma lem5183247 (s : real -> Prop) : (term595 s) = (term595 s).
Proof. exact (fun_ext (fun x : real => @lem5183246 x s)). Qed.
Lemma lem5183248 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5183249 (s : real -> Prop) : (term596 s) = (term596 s).
Proof. exact (MK_COMB (@lem5183248) (@lem5183247 s)). Qed.
Lemma lem5183250 : term597 = term597.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5183249 s)). Qed.
Lemma lem5183251 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5183252 : term598 = term598.
Proof. exact (MK_COMB (@lem5183251) (@lem5183250)). Qed.
Lemma lem5183253 : term218 = term598.
Proof. exact (TRANS (@lem5183239) (@lem5183252)). Qed.
Lemma lem5183254 (x' : type1023) (h1 : term280 x') : term598.
Proof. exact (EQ_MP (@lem5183253) (@lem5182942 x' h1)). Qed.
Lemma lem5183255 (_67653 : real) (h1 : term58) : term599 _67653.
Proof. exact (@lem5182968 h1 _67653). Qed.
Lemma lem5183256 (_67653 : real) : (term599 _67653) = (term169 _67653).
Proof. exact (eq_refl (term599 _67653)). Qed.
Lemma lem5183257 (_67653 : real) (h1 : term58) : term169 _67653.
Proof. exact (EQ_MP (@lem5183256 _67653) (@lem5183255 _67653 h1)). Qed.
Lemma lem5183258 (_67653 : real) (_67654 : real) (h1 : term58) : term600 _67653 _67654.
Proof. exact (@lem5183257 _67653 h1 _67654). Qed.
Lemma lem5183259 (_67654 : real) (_67653 : real) : (term600 _67653 _67654) = (term167 _67654 _67653).
Proof. exact (eq_refl (term600 _67653 _67654)). Qed.
Lemma lem5183260 (_67654 : real) (_67653 : real) (h1 : term58) : term167 _67654 _67653.
Proof. exact (EQ_MP (@lem5183259 _67654 _67653) (@lem5183258 _67653 _67654 h1)). Qed.
Lemma lem5183261 (_67654 : real) (_67653 : real) (_67655 : real) (h1 : term58) : term601 _67654 _67653 _67655.
Proof. exact (@lem5183260 _67654 _67653 h1 _67655). Qed.
Lemma lem5183262 (_67654 : real) (_67653 : real) (_67655 : real) : (term601 _67654 _67653 _67655) = (term164 _67654 _67653 _67655).
Proof. exact (eq_refl (term601 _67654 _67653 _67655)). Qed.
Lemma lem5183263 (_67654 : real) (_67653 : real) (_67655 : real) (h1 : term58) : term164 _67654 _67653 _67655.
Proof. exact (EQ_MP (@lem5183262 _67654 _67653 _67655) (@lem5183261 _67654 _67653 _67655 h1)). Qed.
Lemma lem5183264 (_67656 : real -> Prop) (x : type1021) (h1 : term461 x) : term602 x _67656.
Proof. exact (@lem5183174 x h1 _67656). Qed.
Lemma lem5183265 (x : type1021) (_67656 : real -> Prop) : (term602 x _67656) = (term579 x _67656).
Proof. exact (eq_refl (term602 x _67656)). Qed.
Lemma lem5183266 (_67656 : real -> Prop) (x : type1021) (h1 : term461 x) : term579 x _67656.
Proof. exact (EQ_MP (@lem5183265 x _67656) (@lem5183264 _67656 x h1)). Qed.
Lemma lem5183267 (_67656 : real -> Prop) (_67657 : real) (x : type1021) (h1 : term461 x) : term603 x _67656 _67657.
Proof. exact (@lem5183266 _67656 x h1 _67657). Qed.
Lemma lem5183268 (_67657 : real) (x : type1021) (_67656 : real -> Prop) : (term603 x _67656 _67657) = (term577 _67657 x _67656).
Proof. exact (eq_refl (term603 x _67656 _67657)). Qed.
Lemma lem5183269 (_67657 : real) (_67656 : real -> Prop) (x : type1021) (h1 : term461 x) : term577 _67657 x _67656.
Proof. exact (EQ_MP (@lem5183268 _67657 x _67656) (@lem5183267 _67656 _67657 x h1)). Qed.
Lemma lem5183270 (_67657 : real) (_67656 : real -> Prop) (_67658 : real) (x : type1021) (h1 : term461 x) : term604 _67657 x _67656 _67658.
Proof. exact (@lem5183269 _67657 _67656 x h1 _67658). Qed.
Lemma lem5183271 (_67657 : real) (x : type1021) (_67656 : real -> Prop) (_67658 : real) : (term604 _67657 x _67656 _67658) = (term575 _67657 x _67656 _67658).
Proof. exact (eq_refl (term604 _67657 x _67656 _67658)). Qed.
Lemma lem5183272 (_67657 : real) (_67656 : real -> Prop) (_67658 : real) (x : type1021) (h1 : term461 x) : term575 _67657 x _67656 _67658.
Proof. exact (EQ_MP (@lem5183271 _67657 x _67656 _67658) (@lem5183270 _67657 _67656 _67658 x h1)). Qed.
Lemma lem5183273 (_67659 : real) (y : real) (b : real) (a : real) (s : real -> Prop) (h1 : term82 y b a s) : term605 s b _67659.
Proof. exact (@lem5183199 y b a s h1 _67659). Qed.
Lemma lem5183274 (s : real -> Prop) (_67659 : real) (b : real) : (term605 s b _67659) = (term73 s _67659 b).
Proof. exact (eq_refl (term605 s b _67659)). Qed.
Lemma lem5183279 (_67661 : real -> Prop) (x' : type1023) (h1 : term280 x') : term606 _67661.
Proof. exact (@lem5183254 x' h1 _67661). Qed.
Lemma lem5183280 (_67661 : real -> Prop) : (term606 _67661) = (term596 _67661).
Proof. exact (eq_refl (term606 _67661)). Qed.
Lemma lem5183281 (_67661 : real -> Prop) (x' : type1023) (h1 : term280 x') : term596 _67661.
Proof. exact (EQ_MP (@lem5183280 _67661) (@lem5183279 _67661 x' h1)). Qed.
Lemma lem5183282 (_67661 : real -> Prop) (_67662 : real) (x' : type1023) (h1 : term280 x') : term607 _67661 _67662.
Proof. exact (@lem5183281 _67661 x' h1 _67662). Qed.
Lemma lem5183283 (_67662 : real) (_67661 : real -> Prop) : (term607 _67661 _67662) = (term593 _67662 _67661).
Proof. exact (eq_refl (term607 _67661 _67662)). Qed.
Lemma lem5183286 (_67657 : real) (_67658 : real) (_67656 : real -> Prop) (x : type1021) (h1 : term461 x) : term572 x _67657 _67658 _67656.
Proof. exact (proj1 (@lem5183272 _67657 _67656 _67658 x h1)). Qed.
Lemma lem5183293 (_67657 : real) (_67658 : real) (_67656 : real -> Prop) (x : type1021) (h1 : term461 x) : term608 x _67657 _67658 _67656.
Proof. exact (proj2 (@lem5183286 _67657 _67658 _67656 x h1)). Qed.
Lemma lem5183294 (_67657 : real) (_67658 : real) (_67656 : real -> Prop) (x : type1021) (h1 : term461 x) : term609 x _67657 _67658 _67656.
Proof. exact (proj1 (@lem5183286 _67657 _67658 _67656 x h1)). Qed.
Lemma lem5183305 (_67654 : real) (_67653 : real) (_67655 : real) : (term164 _67654 _67653 _67655) = (term610 _67654 _67653 _67655).
Proof. exact (@lem5180954 (term611 _67653 _67654) (term611 _67654 _67655) (real_le _67653 _67655)). Qed.
Lemma lem5183306 (_67654 : real) (_67653 : real) (_67655 : real) (h1 : term58) : term610 _67654 _67653 _67655.
Proof. exact (EQ_MP (@lem5183305 _67654 _67653 _67655) (@lem5183263 _67654 _67653 _67655 h1)). Qed.
Lemma lem5183308 (y : real) (b : real) (a : real) (s : real -> Prop) (h1 : term82 y b a s) : term78 a s.
Proof. exact (proj2 (@lem5182935 y b a s h1)). Qed.
Lemma lem5183318 (_67659 : real) (y : real) (b : real) (a : real) (s : real -> Prop) (h1 : term82 y b a s) : term73 s _67659 b.
Proof. exact (EQ_MP (@lem5183274 s _67659 b) (@lem5183273 _67659 y b a s h1)). Qed.
Lemma lem5183330 (_67662 : real) (_67661 : real -> Prop) (x' : type1023) (h1 : term280 x') : term593 _67662 _67661.
Proof. exact (EQ_MP (@lem5183283 _67662 _67661) (@lem5183282 _67661 _67662 x' h1)). Qed.
Lemma lem5183409 (x : type1021) (_67657 : real) (_67658 : real) (_67656 : real -> Prop) : (term609 x _67657 _67658 _67656) = (term612 x _67657 _67658 _67656).
Proof. exact (@lem5180954 (_67656 = (@EMPTY real)) (term551 x _67657 _67656) (term305 _67658 _67656)). Qed.
Lemma lem5183410 (_67657 : real) (_67658 : real) (_67656 : real -> Prop) (x : type1021) (h1 : term461 x) : term612 x _67657 _67658 _67656.
Proof. exact (EQ_MP (@lem5183409 x _67657 _67658 _67656) (@lem5183294 _67657 _67658 _67656 x h1)). Qed.
Lemma lem5183425 (x : type1021) (_67657 : real) (_67658 : real) (_67656 : real -> Prop) : (term608 x _67657 _67658 _67656) = (term613 x _67657 _67658 _67656).
Proof. exact (@lem5180954 (_67656 = (@EMPTY real)) (term552 x _67656 _67657) (term305 _67658 _67656)). Qed.
Lemma lem5183426 (_67657 : real) (_67658 : real) (_67656 : real -> Prop) (x : type1021) (h1 : term461 x) : term613 x _67657 _67658 _67656.
Proof. exact (EQ_MP (@lem5183425 x _67657 _67658 _67656) (@lem5183293 _67657 _67658 _67656 x h1)). Qed.
Lemma lem5183501 (y : real) (b : real) (a : real) (s : real -> Prop) (h1 : term82 y b a s) : real_le a y.
Proof. exact (proj1 (@lem5182938 y b a s h1)). Qed.
Lemma lem5183502 (y : real) (b : real) (a : real) (s : real -> Prop) (h1 : term82 y b a s) : term614 a y.
Proof. exact (fun h0 : term611 a y => @lem5183501 y b a s h1). Qed.
Lemma lem5183504 (p : Prop) : (term615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5183505 (a : real) (y : real) : (term614 a y) = (real_le a y).
Proof. exact (@lem5183504 (real_le a y)). Qed.
Lemma lem5183506 (y : real) (b : real) (a : real) (s : real -> Prop) (h1 : term82 y b a s) : real_le a y.
Proof. exact (EQ_MP (@lem5183505 a y) (@lem5183502 y b a s h1)). Qed.
Lemma lem5183508 (y : real) (b : real) (a : real) (s : real -> Prop) (h1 : term82 y b a s) : @IN real y s.
Proof. exact (proj1 (@lem5182937 y b a s h1)). Qed.
Lemma lem5183509 (y : real) (b : real) (a : real) (s : real -> Prop) (h1 : term82 y b a s) : term616 y s.
Proof. exact (fun h0 : term178 y s => @lem5183508 y b a s h1). Qed.
Lemma lem5183511 (p : Prop) : (term615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5183512 (y : real) (s : real -> Prop) : (term616 y s) = (@IN real y s).
Proof. exact (@lem5183511 (@IN real y s)). Qed.
Lemma lem5183513 (y : real) (b : real) (a : real) (s : real -> Prop) (h1 : term82 y b a s) : @IN real y s.
Proof. exact (EQ_MP (@lem5183512 y s) (@lem5183509 y b a s h1)). Qed.
Lemma lem5183519 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5183520 (_67662 : real) (_67661 : real -> Prop) : (term593 _67662 _67661) = (term617 _67662 _67661).
Proof. exact (@lem5183519 (term47 _67661) (term178 _67662 _67661)). Qed.
Lemma lem5183528 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5183529 (_67662 : real) (_67661 : real -> Prop) : (term618 _67662 _67661) = (term619 _67662 _67661).
Proof. exact (MK_COMB (@lem5183528) (@lem5183520 _67662 _67661)). Qed.
Lemma lem5183537 (_67662 : real) (_67661 : real -> Prop) : (term617 _67662 _67661) = (term617 _67662 _67661).
Proof. exact (eq_refl (term617 _67662 _67661)). Qed.
Lemma lem5183538 (_67662 : real) (_67661 : real -> Prop) : ((term593 _67662 _67661) = (term617 _67662 _67661)) = ((term617 _67662 _67661) = (term617 _67662 _67661)).
Proof. exact (MK_COMB (@lem5183529 _67662 _67661) (@lem5183537 _67662 _67661)). Qed.
Lemma lem5183540 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5183541 (x : Prop) : (x = x) = True.
Proof. exact (@lem5183540 Prop x). Qed.
Lemma lem5183542 (_67662 : real) (_67661 : real -> Prop) : ((term617 _67662 _67661) = (term617 _67662 _67661)) = True.
Proof. exact (@lem5183541 (term617 _67662 _67661)). Qed.
Lemma lem5183543 (_67662 : real) (_67661 : real -> Prop) : ((term593 _67662 _67661) = (term617 _67662 _67661)) = True.
Proof. exact (TRANS (@lem5183538 _67662 _67661) (@lem5183542 _67662 _67661)). Qed.
Lemma lem5183544 (_67662 : real) (_67661 : real -> Prop) : True = ((term593 _67662 _67661) = (term617 _67662 _67661)).
Proof. exact (SYM (@lem5183543 _67662 _67661)). Qed.
Lemma lem5183545 (_67662 : real) (_67661 : real -> Prop) : (term593 _67662 _67661) = (term617 _67662 _67661).
Proof. exact (EQ_MP (@lem5183544 _67662 _67661) (@lem0)). Qed.
Lemma lem5183546 (_67662 : real) (_67661 : real -> Prop) (x' : type1023) (h1 : term280 x') : term617 _67662 _67661.
Proof. exact (EQ_MP (@lem5183545 _67662 _67661) (@lem5183330 _67662 _67661 x' h1)). Qed.
Lemma lem5183548 (b : Prop) (a : Prop) : (a \/ b) = (term620 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5183549 (_67662 : real) (_67661 : real -> Prop) : (term617 _67662 _67661) = (term621 _67662 _67661).
Proof. exact (@lem5183548 (term178 _67662 _67661) (term47 _67661)). Qed.
Lemma lem5183551 (a : Prop) : (term622 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5183552 (_67662 : real) (_67661 : real -> Prop) : (term623 _67662 _67661) = (@IN real _67662 _67661).
Proof. exact (@lem5183551 (@IN real _67662 _67661)). Qed.
Lemma lem5183553 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5183554 (_67662 : real) (_67661 : real -> Prop) : (term624 _67662 _67661) = (term625 _67662 _67661).
Proof. exact (MK_COMB (@lem5183553) (@lem5183552 _67662 _67661)). Qed.
Lemma lem5183555 (_67661 : real -> Prop) : (term47 _67661) = (term47 _67661).
Proof. exact (eq_refl (term47 _67661)). Qed.
Lemma lem5183556 (_67662 : real) (_67661 : real -> Prop) : (term621 _67662 _67661) = (term626 _67662 _67661).
Proof. exact (MK_COMB (@lem5183554 _67662 _67661) (@lem5183555 _67661)). Qed.
Lemma lem5183557 (_67662 : real) (_67661 : real -> Prop) : (term617 _67662 _67661) = (term626 _67662 _67661).
Proof. exact (TRANS (@lem5183549 _67662 _67661) (@lem5183556 _67662 _67661)). Qed.
Lemma lem5183560 (_67662 : real) (_67661 : real -> Prop) (x' : type1023) (h1 : term280 x') : term626 _67662 _67661.
Proof. exact (EQ_MP (@lem5183557 _67662 _67661) (@lem5183546 _67662 _67661 x' h1)). Qed.
Lemma lem5183561 (y : real) (s : real -> Prop) (x' : type1023) (h1 : term280 x') : term626 y s.
Proof. exact (@lem5183560 y s x' h1). Qed.
Lemma lem5183564 (x' : type1023) (y : real) (b : real) (a : real) (s : real -> Prop) (h1 : term280 x') (h2 : term82 y b a s) : term47 s.
Proof. exact (@lem5183561 y s x' h1 (@lem5183513 y b a s h2)). Qed.
Lemma lem5183565 (x' : type1023) (y : real) (b : real) (a : real) (s : real -> Prop) (h1 : term280 x') (h2 : term82 y b a s) : term627 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5183564 x' y b a s h1 h2). Qed.
Lemma lem5183567 (p : Prop) : (term628 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5183568 (s : real -> Prop) : (term627 s) = (term47 s).
Proof. exact (@lem5183567 (s = (@EMPTY real))). Qed.
Lemma lem5183569 (x' : type1023) (y : real) (b : real) (a : real) (s : real -> Prop) (h1 : term280 x') (h2 : term82 y b a s) : term47 s.
Proof. exact (EQ_MP (@lem5183568 s) (@lem5183565 x' y b a s h1 h2)). Qed.
Lemma lem5183571 (y : real) (b : real) (a : real) (s : real -> Prop) (h1 : term82 y b a s) : @IN real y s.
Proof. exact (proj1 (@lem5182937 y b a s h1)). Qed.
Lemma lem5183572 (y : real) (b : real) (a : real) (s : real -> Prop) (h1 : term82 y b a s) : term616 y s.
Proof. exact (fun h0 : term178 y s => @lem5183571 y b a s h1). Qed.
Lemma lem5183574 (p : Prop) : (term615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5183575 (y : real) (s : real -> Prop) : (term616 y s) = (@IN real y s).
Proof. exact (@lem5183574 (@IN real y s)). Qed.
Lemma lem5183576 (y : real) (b : real) (a : real) (s : real -> Prop) (h1 : term82 y b a s) : @IN real y s.
Proof. exact (EQ_MP (@lem5183575 y s) (@lem5183572 y b a s h1)). Qed.
Lemma lem5183578 (_67662 : real) (_67661 : real -> Prop) (x' : type1023) (h1 : term280 x') : term626 _67662 _67661.
Proof. exact (EQ_MP (@lem5183557 _67662 _67661) (@lem5183546 _67662 _67661 x' h1)). Qed.
Lemma lem5183579 (y : real) (s : real -> Prop) (x' : type1023) (h1 : term280 x') : term626 y s.
Proof. exact (@lem5183578 y s x' h1). Qed.
Lemma lem5183582 (x' : type1023) (y : real) (b : real) (a : real) (s : real -> Prop) (h1 : term280 x') (h2 : term82 y b a s) : term47 s.
Proof. exact (@lem5183579 y s x' h1 (@lem5183576 y b a s h2)). Qed.
Lemma lem5183583 (x' : type1023) (y : real) (b : real) (a : real) (s : real -> Prop) (h1 : term280 x') (h2 : term82 y b a s) : term627 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5183582 x' y b a s h1 h2). Qed.
Lemma lem5183585 (p : Prop) : (term628 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5183586 (s : real -> Prop) : (term627 s) = (term47 s).
Proof. exact (@lem5183585 (s = (@EMPTY real))). Qed.
Lemma lem5183587 (x' : type1023) (y : real) (b : real) (a : real) (s : real -> Prop) (h1 : term280 x') (h2 : term82 y b a s) : term47 s.
Proof. exact (EQ_MP (@lem5183586 s) (@lem5183583 x' y b a s h1 h2)). Qed.
Lemma lem5183589 (y : real) (b : real) (a : real) (s : real -> Prop) (h1 : term82 y b a s) : @IN real y s.
Proof. exact (proj1 (@lem5182937 y b a s h1)). Qed.
Lemma lem5183590 (y : real) (b : real) (a : real) (s : real -> Prop) (h1 : term82 y b a s) : term616 y s.
Proof. exact (fun h0 : term178 y s => @lem5183589 y b a s h1). Qed.
Lemma lem5183592 (p : Prop) : (term615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5183593 (y : real) (s : real -> Prop) : (term616 y s) = (@IN real y s).
Proof. exact (@lem5183592 (@IN real y s)). Qed.
Lemma lem5183594 (y : real) (b : real) (a : real) (s : real -> Prop) (h1 : term82 y b a s) : @IN real y s.
Proof. exact (EQ_MP (@lem5183593 y s) (@lem5183590 y b a s h1)). Qed.
Lemma lem5183597 (y : real) (s : real -> Prop) (h1 : term78 y s) : term78 y s.
Proof. exact (h1). Qed.
Lemma lem5183598 (y : real) (s : real -> Prop) (h1 : term78 y s) : term629 y s.
Proof. exact (fun h0 : term59 y s => @lem5183597 y s h1). Qed.
Lemma lem5183600 (p : Prop) : (term628 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5183601 (y : real) (s : real -> Prop) : (term629 y s) = (term78 y s).
Proof. exact (@lem5183600 (term59 y s)). Qed.
Lemma lem5183602 (y : real) (s : real -> Prop) (h1 : term78 y s) : term78 y s.
Proof. exact (EQ_MP (@lem5183601 y s) (@lem5183598 y s h1)). Qed.
Lemma lem5183630 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5183631 (_67658 : real) (_67656 : real -> Prop) : (term305 _67658 _67656) = (term630 _67658 _67656).
Proof. exact (@lem5183630 (term59 _67658 _67656) (term178 _67658 _67656)). Qed.
Lemma lem5183637 (x : type1021) (_67657 : real) (_67656 : real -> Prop) : (term631 x _67657 _67656) = (term631 x _67657 _67656).
Proof. exact (eq_refl (term631 x _67657 _67656)). Qed.
Lemma lem5183638 (x : type1021) (_67657 : real) (_67658 : real) (_67656 : real -> Prop) : (term632 x _67657 _67658 _67656) = (term633 x _67657 _67658 _67656).
Proof. exact (MK_COMB (@lem5183637 x _67657 _67656) (@lem5183631 _67658 _67656)). Qed.
Lemma lem5183649 (_67656 : real -> Prop) : (term301 _67656) = (term301 _67656).
Proof. exact (eq_refl (term301 _67656)). Qed.
Lemma lem5183650 (x : type1021) (_67657 : real) (_67658 : real) (_67656 : real -> Prop) : (term612 x _67657 _67658 _67656) = (term634 x _67657 _67658 _67656).
Proof. exact (MK_COMB (@lem5183649 _67656) (@lem5183638 x _67657 _67658 _67656)). Qed.
Lemma lem5183661 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5183662 (x : type1021) (_67657 : real) (_67658 : real) (_67656 : real -> Prop) : (term635 x _67657 _67658 _67656) = (term636 x _67657 _67658 _67656).
Proof. exact (MK_COMB (@lem5183661) (@lem5183650 x _67657 _67658 _67656)). Qed.
Lemma lem5183666 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5183667 (x : type1021) (_67657 : real) (_67658 : real) (_67656 : real -> Prop) : (term637 x _67657 _67658 _67656) = (term612 x _67657 _67658 _67656).
Proof. exact (@lem5183666 (_67656 = (@EMPTY real)) (term551 x _67657 _67656) (term305 _67658 _67656)). Qed.
Lemma lem5183693 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5183694 (_67658 : real) (_67656 : real -> Prop) : (term305 _67658 _67656) = (term630 _67658 _67656).
Proof. exact (@lem5183693 (term59 _67658 _67656) (term178 _67658 _67656)). Qed.
Lemma lem5183700 (x : type1021) (_67657 : real) (_67656 : real -> Prop) : (term631 x _67657 _67656) = (term631 x _67657 _67656).
Proof. exact (eq_refl (term631 x _67657 _67656)). Qed.
Lemma lem5183701 (x : type1021) (_67657 : real) (_67658 : real) (_67656 : real -> Prop) : (term632 x _67657 _67658 _67656) = (term633 x _67657 _67658 _67656).
Proof. exact (MK_COMB (@lem5183700 x _67657 _67656) (@lem5183694 _67658 _67656)). Qed.
Lemma lem5183712 (_67656 : real -> Prop) : (term301 _67656) = (term301 _67656).
Proof. exact (eq_refl (term301 _67656)). Qed.
Lemma lem5183713 (x : type1021) (_67657 : real) (_67658 : real) (_67656 : real -> Prop) : (term612 x _67657 _67658 _67656) = (term634 x _67657 _67658 _67656).
Proof. exact (MK_COMB (@lem5183712 _67656) (@lem5183701 x _67657 _67658 _67656)). Qed.
Lemma lem5183724 (x : type1021) (_67657 : real) (_67658 : real) (_67656 : real -> Prop) : (term637 x _67657 _67658 _67656) = (term634 x _67657 _67658 _67656).
Proof. exact (TRANS (@lem5183667 x _67657 _67658 _67656) (@lem5183713 x _67657 _67658 _67656)). Qed.
Lemma lem5183725 (x : type1021) (_67657 : real) (_67658 : real) (_67656 : real -> Prop) : ((term612 x _67657 _67658 _67656) = (term637 x _67657 _67658 _67656)) = ((term634 x _67657 _67658 _67656) = (term634 x _67657 _67658 _67656)).
Proof. exact (MK_COMB (@lem5183662 x _67657 _67658 _67656) (@lem5183724 x _67657 _67658 _67656)). Qed.
Lemma lem5183727 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5183728 (x : Prop) : (x = x) = True.
Proof. exact (@lem5183727 Prop x). Qed.
Lemma lem5183729 (x : type1021) (_67657 : real) (_67658 : real) (_67656 : real -> Prop) : ((term634 x _67657 _67658 _67656) = (term634 x _67657 _67658 _67656)) = True.
Proof. exact (@lem5183728 (term634 x _67657 _67658 _67656)). Qed.
Lemma lem5183730 (x : type1021) (_67657 : real) (_67658 : real) (_67656 : real -> Prop) : ((term612 x _67657 _67658 _67656) = (term637 x _67657 _67658 _67656)) = True.
Proof. exact (TRANS (@lem5183725 x _67657 _67658 _67656) (@lem5183729 x _67657 _67658 _67656)). Qed.
Lemma lem5183731 (x : type1021) (_67657 : real) (_67658 : real) (_67656 : real -> Prop) : True = ((term612 x _67657 _67658 _67656) = (term637 x _67657 _67658 _67656)).
Proof. exact (SYM (@lem5183730 x _67657 _67658 _67656)). Qed.
Lemma lem5183732 (x : type1021) (_67657 : real) (_67658 : real) (_67656 : real -> Prop) : (term612 x _67657 _67658 _67656) = (term637 x _67657 _67658 _67656).
Proof. exact (EQ_MP (@lem5183731 x _67657 _67658 _67656) (@lem0)). Qed.
Lemma lem5183733 (_67657 : real) (_67658 : real) (_67656 : real -> Prop) (x : type1021) (h1 : term461 x) : term637 x _67657 _67658 _67656.
Proof. exact (EQ_MP (@lem5183732 x _67657 _67658 _67656) (@lem5183410 _67657 _67658 _67656 x h1)). Qed.
Lemma lem5183735 (b : Prop) (a : Prop) : (a \/ b) = (term620 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5183736 (_67658 : real) (x : type1021) (_67657 : real) (_67656 : real -> Prop) : (term637 x _67657 _67658 _67656) = (term638 _67658 x _67657 _67656).
Proof. exact (@lem5183735 (term639 _67658 _67656) (term551 x _67657 _67656)). Qed.
Lemma lem5183738 (a : Prop) (b : Prop) : (term640 a b) = (term641 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5183739 (_67658 : real) (_67656 : real -> Prop) : (term642 _67658 _67656) = (term643 _67658 _67656).
Proof. exact (@lem5183738 (_67656 = (@EMPTY real)) (term305 _67658 _67656)). Qed.
Lemma lem5183741 (a : Prop) (b : Prop) : (term640 a b) = (term641 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5183742 (_67658 : real) (_67656 : real -> Prop) : (term644 _67658 _67656) = (term645 _67658 _67656).
Proof. exact (@lem5183741 (term178 _67658 _67656) (term59 _67658 _67656)). Qed.
Lemma lem5183744 (a : Prop) : (term622 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5183745 (_67658 : real) (_67656 : real -> Prop) : (term623 _67658 _67656) = (@IN real _67658 _67656).
Proof. exact (@lem5183744 (@IN real _67658 _67656)). Qed.
Lemma lem5183746 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5183747 (_67658 : real) (_67656 : real -> Prop) : (term646 _67658 _67656) = (term62 _67658 _67656).
Proof. exact (MK_COMB (@lem5183746) (@lem5183745 _67658 _67656)). Qed.
Lemma lem5183748 (_67658 : real) (_67656 : real -> Prop) : (term78 _67658 _67656) = (term78 _67658 _67656).
Proof. exact (eq_refl (term78 _67658 _67656)). Qed.
Lemma lem5183749 (_67658 : real) (_67656 : real -> Prop) : (term645 _67658 _67656) = (term647 _67658 _67656).
Proof. exact (MK_COMB (@lem5183747 _67658 _67656) (@lem5183748 _67658 _67656)). Qed.
Lemma lem5183750 (_67658 : real) (_67656 : real -> Prop) : (term644 _67658 _67656) = (term647 _67658 _67656).
Proof. exact (TRANS (@lem5183742 _67658 _67656) (@lem5183749 _67658 _67656)). Qed.
Lemma lem5183751 (_67656 : real -> Prop) : (term42 _67656) = (term42 _67656).
Proof. exact (eq_refl (term42 _67656)). Qed.
Lemma lem5183752 (_67658 : real) (_67656 : real -> Prop) : (term643 _67658 _67656) = (term648 _67658 _67656).
Proof. exact (MK_COMB (@lem5183751 _67656) (@lem5183750 _67658 _67656)). Qed.
Lemma lem5183753 (_67658 : real) (_67656 : real -> Prop) : (term642 _67658 _67656) = (term648 _67658 _67656).
Proof. exact (TRANS (@lem5183739 _67658 _67656) (@lem5183752 _67658 _67656)). Qed.
Lemma lem5183754 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5183755 (_67658 : real) (_67656 : real -> Prop) : (term649 _67658 _67656) = (term650 _67658 _67656).
Proof. exact (MK_COMB (@lem5183754) (@lem5183753 _67658 _67656)). Qed.
Lemma lem5183756 (x : type1021) (_67657 : real) (_67656 : real -> Prop) : (term551 x _67657 _67656) = (term551 x _67657 _67656).
Proof. exact (eq_refl (term551 x _67657 _67656)). Qed.
Lemma lem5183757 (_67658 : real) (x : type1021) (_67657 : real) (_67656 : real -> Prop) : (term638 _67658 x _67657 _67656) = (term651 _67658 x _67657 _67656).
Proof. exact (MK_COMB (@lem5183755 _67658 _67656) (@lem5183756 x _67657 _67656)). Qed.
Lemma lem5183758 (_67658 : real) (x : type1021) (_67657 : real) (_67656 : real -> Prop) : (term637 x _67657 _67658 _67656) = (term651 _67658 x _67657 _67656).
Proof. exact (TRANS (@lem5183736 _67658 x _67657 _67656) (@lem5183757 _67658 x _67657 _67656)). Qed.
Lemma lem5183760 (y : real) (b : real) (a : real) (s : real -> Prop) (h1 : term78 y s) (h2 : term82 y b a s) : term647 y s.
Proof. exact (conj (@lem5183594 y b a s h2) (@lem5183602 y s h1)). Qed.
Lemma lem5183761 (x' : type1023) (y : real) (b : real) (a : real) (s : real -> Prop) (h1 : term78 y s) (h2 : term280 x') (h3 : term82 y b a s) : term648 y s.
Proof. exact (conj (@lem5183587 x' y b a s h2 h3) (@lem5183760 y b a s h1 h3)). Qed.
Lemma lem5183763 (_67658 : real) (_67657 : real) (_67656 : real -> Prop) (x : type1021) (h1 : term461 x) : term651 _67658 x _67657 _67656.
Proof. exact (EQ_MP (@lem5183758 _67658 x _67657 _67656) (@lem5183733 _67657 _67658 _67656 x h1)). Qed.
Lemma lem5183764 (y : real) (_67657 : real) (s : real -> Prop) (x : type1021) (h1 : term461 x) : term651 y x _67657 s.
Proof. exact (@lem5183763 y _67657 s x h1). Qed.
Lemma lem5183767 (_67657 : real) (x : type1021) (x' : type1023) (y : real) (b : real) (a : real) (s : real -> Prop) (h1 : term461 x) (h2 : term78 y s) (h3 : term280 x') (h4 : term82 y b a s) : term551 x _67657 s.
Proof. exact (@lem5183764 y _67657 s x h1 (@lem5183761 x' y b a s h2 h3 h4)). Qed.
Lemma lem5183768 (x : type1021) (x' : type1023) (y : real) (b : real) (a : real) (s : real -> Prop) (h1 : term461 x) (h2 : term78 y s) (h3 : term280 x') (h4 : term82 y b a s) : term551 x b s.
Proof. exact (@lem5183767 b x x' y b a s h1 h2 h3 h4). Qed.
Lemma lem5183769 (x : type1021) (x' : type1023) (y : real) (b : real) (a : real) (s : real -> Prop) (h1 : term461 x) (h2 : term78 y s) (h3 : term280 x') (h4 : term82 y b a s) : term652 x b s.
Proof. exact (fun h0 : term653 x b s => @lem5183768 x x' y b a s h1 h2 h3 h4). Qed.
Lemma lem5183771 (p : Prop) : (term615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5183772 (x : type1021) (b : real) (s : real -> Prop) : (term652 x b s) = (term551 x b s).
Proof. exact (@lem5183771 (term551 x b s)). Qed.
Lemma lem5183773 (x : type1021) (x' : type1023) (y : real) (b : real) (a : real) (s : real -> Prop) (h1 : term461 x) (h2 : term78 y s) (h3 : term280 x') (h4 : term82 y b a s) : term551 x b s.
Proof. exact (EQ_MP (@lem5183772 x b s) (@lem5183769 x x' y b a s h1 h2 h3 h4)). Qed.
Lemma lem5183779 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5183780 (b : real) (_67659 : real) (s : real -> Prop) : (term73 s _67659 b) = (term654 b _67659 s).
Proof. exact (@lem5183779 (real_le _67659 b) (term178 _67659 s)). Qed.
Lemma lem5183786 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5183787 (b : real) (_67659 : real) (s : real -> Prop) : (term655 s _67659 b) = (term656 b _67659 s).
Proof. exact (MK_COMB (@lem5183786) (@lem5183780 b _67659 s)). Qed.
Lemma lem5183793 (b : real) (_67659 : real) (s : real -> Prop) : (term654 b _67659 s) = (term654 b _67659 s).
Proof. exact (eq_refl (term654 b _67659 s)). Qed.
Lemma lem5183794 (b : real) (_67659 : real) (s : real -> Prop) : ((term73 s _67659 b) = (term654 b _67659 s)) = ((term654 b _67659 s) = (term654 b _67659 s)).
Proof. exact (MK_COMB (@lem5183787 b _67659 s) (@lem5183793 b _67659 s)). Qed.
Lemma lem5183796 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5183797 (x : Prop) : (x = x) = True.
Proof. exact (@lem5183796 Prop x). Qed.
Lemma lem5183798 (b : real) (_67659 : real) (s : real -> Prop) : ((term654 b _67659 s) = (term654 b _67659 s)) = True.
Proof. exact (@lem5183797 (term654 b _67659 s)). Qed.
Lemma lem5183799 (b : real) (_67659 : real) (s : real -> Prop) : ((term73 s _67659 b) = (term654 b _67659 s)) = True.
Proof. exact (TRANS (@lem5183794 b _67659 s) (@lem5183798 b _67659 s)). Qed.
Lemma lem5183800 (b : real) (_67659 : real) (s : real -> Prop) : True = ((term73 s _67659 b) = (term654 b _67659 s)).
Proof. exact (SYM (@lem5183799 b _67659 s)). Qed.
Lemma lem5183801 (b : real) (_67659 : real) (s : real -> Prop) : (term73 s _67659 b) = (term654 b _67659 s).
Proof. exact (EQ_MP (@lem5183800 b _67659 s) (@lem0)). Qed.
Lemma lem5183802 (_67659 : real) (y : real) (b : real) (a : real) (s : real -> Prop) (h1 : term82 y b a s) : term654 b _67659 s.
Proof. exact (EQ_MP (@lem5183801 b _67659 s) (@lem5183318 _67659 y b a s h1)). Qed.
Lemma lem5183804 (b : Prop) (a : Prop) : (a \/ b) = (term620 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5183805 (s : real -> Prop) (_67659 : real) (b : real) : (term654 b _67659 s) = (term657 s _67659 b).
Proof. exact (@lem5183804 (term178 _67659 s) (real_le _67659 b)). Qed.
Lemma lem5183807 (a : Prop) : (term622 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5183808 (_67659 : real) (s : real -> Prop) : (term623 _67659 s) = (@IN real _67659 s).
Proof. exact (@lem5183807 (@IN real _67659 s)). Qed.
Lemma lem5183809 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5183810 (_67659 : real) (s : real -> Prop) : (term624 _67659 s) = (term625 _67659 s).
Proof. exact (MK_COMB (@lem5183809) (@lem5183808 _67659 s)). Qed.
Lemma lem5183811 (_67659 : real) (b : real) : (real_le _67659 b) = (real_le _67659 b).
Proof. exact (eq_refl (real_le _67659 b)). Qed.
Lemma lem5183812 (s : real -> Prop) (_67659 : real) (b : real) : (term657 s _67659 b) = (term28 s _67659 b).
Proof. exact (MK_COMB (@lem5183810 _67659 s) (@lem5183811 _67659 b)). Qed.
Lemma lem5183813 (s : real -> Prop) (_67659 : real) (b : real) : (term654 b _67659 s) = (term28 s _67659 b).
Proof. exact (TRANS (@lem5183805 s _67659 b) (@lem5183812 s _67659 b)). Qed.
Lemma lem5183816 (_67659 : real) (y : real) (b : real) (a : real) (s : real -> Prop) (h1 : term82 y b a s) : term28 s _67659 b.
Proof. exact (EQ_MP (@lem5183813 s _67659 b) (@lem5183802 _67659 y b a s h1)). Qed.
Lemma lem5183817 (x : type1021) (y : real) (b : real) (a : real) (s : real -> Prop) (h1 : term82 y b a s) : term658 x s b.
Proof. exact (@lem5183816 (x s b) y b a s h1). Qed.
Lemma lem5183820 (x : type1021) (x' : type1023) (y : real) (b : real) (a : real) (s : real -> Prop) (h1 : term461 x) (h2 : term78 y s) (h3 : term280 x') (h4 : term82 y b a s) : term659 x s b.
Proof. exact (@lem5183817 x y b a s h4 (@lem5183773 x x' y b a s h1 h2 h3 h4)). Qed.
Lemma lem5183821 (x : type1021) (x' : type1023) (y : real) (b : real) (a : real) (s : real -> Prop) (h1 : term461 x) (h2 : term78 y s) (h3 : term280 x') (h4 : term82 y b a s) : term660 x s b.
Proof. exact (fun h0 : term552 x s b => @lem5183820 x x' y b a s h1 h2 h3 h4). Qed.
Lemma lem5183823 (p : Prop) : (term615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5183824 (x : type1021) (s : real -> Prop) (b : real) : (term660 x s b) = (term659 x s b).
Proof. exact (@lem5183823 (term659 x s b)). Qed.
Lemma lem5183825 (x : type1021) (x' : type1023) (y : real) (b : real) (a : real) (s : real -> Prop) (h1 : term461 x) (h2 : term78 y s) (h3 : term280 x') (h4 : term82 y b a s) : term659 x s b.
Proof. exact (EQ_MP (@lem5183824 x s b) (@lem5183821 x x' y b a s h1 h2 h3 h4)). Qed.
Lemma lem5183827 (y : real) (b : real) (a : real) (s : real -> Prop) (h1 : term82 y b a s) : @IN real y s.
Proof. exact (proj1 (@lem5182937 y b a s h1)). Qed.
Lemma lem5183828 (y : real) (b : real) (a : real) (s : real -> Prop) (h1 : term82 y b a s) : term616 y s.
Proof. exact (fun h0 : term178 y s => @lem5183827 y b a s h1). Qed.
Lemma lem5183830 (p : Prop) : (term615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5183831 (y : real) (s : real -> Prop) : (term616 y s) = (@IN real y s).
Proof. exact (@lem5183830 (@IN real y s)). Qed.
Lemma lem5183832 (y : real) (b : real) (a : real) (s : real -> Prop) (h1 : term82 y b a s) : @IN real y s.
Proof. exact (EQ_MP (@lem5183831 y s) (@lem5183828 y b a s h1)). Qed.
Lemma lem5183850 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5183851 (x : type1021) (_67657 : real) (_67658 : real) (_67656 : real -> Prop) : (term661 x _67657 _67658 _67656) = (term662 x _67657 _67658 _67656).
Proof. exact (@lem5183850 (term178 _67658 _67656) (term552 x _67656 _67657) (term59 _67658 _67656)). Qed.
Lemma lem5183865 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5183866 (_67658 : real) (x : type1021) (_67656 : real -> Prop) (_67657 : real) : (term663 x _67657 _67658 _67656) = (term664 _67658 x _67656 _67657).
Proof. exact (@lem5183865 (term59 _67658 _67656) (term552 x _67656 _67657)). Qed.
Lemma lem5183872 (_67658 : real) (_67656 : real -> Prop) : (term591 _67658 _67656) = (term591 _67658 _67656).
Proof. exact (eq_refl (term591 _67658 _67656)). Qed.
Lemma lem5183873 (_67658 : real) (x : type1021) (_67656 : real -> Prop) (_67657 : real) : (term662 x _67657 _67658 _67656) = (term665 _67658 x _67656 _67657).
Proof. exact (MK_COMB (@lem5183872 _67658 _67656) (@lem5183866 _67658 x _67656 _67657)). Qed.
Lemma lem5183877 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5183878 (_67658 : real) (x : type1021) (_67656 : real -> Prop) (_67657 : real) : (term665 _67658 x _67656 _67657) = (term666 _67658 x _67656 _67657).
Proof. exact (@lem5183877 (term59 _67658 _67656) (term178 _67658 _67656) (term552 x _67656 _67657)). Qed.
Lemma lem5183894 (_67658 : real) (x : type1021) (_67656 : real -> Prop) (_67657 : real) : (term662 x _67657 _67658 _67656) = (term666 _67658 x _67656 _67657).
Proof. exact (TRANS (@lem5183873 _67658 x _67656 _67657) (@lem5183878 _67658 x _67656 _67657)). Qed.
Lemma lem5183895 (_67658 : real) (x : type1021) (_67656 : real -> Prop) (_67657 : real) : (term661 x _67657 _67658 _67656) = (term666 _67658 x _67656 _67657).
Proof. exact (TRANS (@lem5183851 x _67657 _67658 _67656) (@lem5183894 _67658 x _67656 _67657)). Qed.
Lemma lem5183896 (_67656 : real -> Prop) : (term301 _67656) = (term301 _67656).
Proof. exact (eq_refl (term301 _67656)). Qed.
Lemma lem5183897 (_67658 : real) (x : type1021) (_67656 : real -> Prop) (_67657 : real) : (term613 x _67657 _67658 _67656) = (term667 _67658 x _67656 _67657).
Proof. exact (MK_COMB (@lem5183896 _67656) (@lem5183895 _67658 x _67656 _67657)). Qed.
Lemma lem5183908 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5183909 (_67658 : real) (x : type1021) (_67656 : real -> Prop) (_67657 : real) : (term668 x _67657 _67658 _67656) = (term669 _67658 x _67656 _67657).
Proof. exact (MK_COMB (@lem5183908) (@lem5183897 _67658 x _67656 _67657)). Qed.
Lemma lem5183913 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5183914 (x : type1021) (_67657 : real) (_67658 : real) (_67656 : real -> Prop) : (term670 x _67657 _67658 _67656) = (term671 x _67657 _67658 _67656).
Proof. exact (@lem5183913 (_67656 = (@EMPTY real)) (term59 _67658 _67656) (term672 x _67657 _67658 _67656)). Qed.
Lemma lem5183940 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5183941 (_67658 : real) (x : type1021) (_67656 : real -> Prop) (_67657 : real) : (term672 x _67657 _67658 _67656) = (term673 _67658 x _67656 _67657).
Proof. exact (@lem5183940 (term178 _67658 _67656) (term552 x _67656 _67657)). Qed.
Lemma lem5183947 (_67658 : real) (_67656 : real -> Prop) : (term674 _67658 _67656) = (term674 _67658 _67656).
Proof. exact (eq_refl (term674 _67658 _67656)). Qed.
Lemma lem5183948 (_67658 : real) (x : type1021) (_67656 : real -> Prop) (_67657 : real) : (term675 x _67657 _67658 _67656) = (term666 _67658 x _67656 _67657).
Proof. exact (MK_COMB (@lem5183947 _67658 _67656) (@lem5183941 _67658 x _67656 _67657)). Qed.
Lemma lem5183959 (_67656 : real -> Prop) : (term301 _67656) = (term301 _67656).
Proof. exact (eq_refl (term301 _67656)). Qed.
Lemma lem5183960 (_67658 : real) (x : type1021) (_67656 : real -> Prop) (_67657 : real) : (term671 x _67657 _67658 _67656) = (term667 _67658 x _67656 _67657).
Proof. exact (MK_COMB (@lem5183959 _67656) (@lem5183948 _67658 x _67656 _67657)). Qed.
Lemma lem5183971 (_67658 : real) (x : type1021) (_67656 : real -> Prop) (_67657 : real) : (term670 x _67657 _67658 _67656) = (term667 _67658 x _67656 _67657).
Proof. exact (TRANS (@lem5183914 x _67657 _67658 _67656) (@lem5183960 _67658 x _67656 _67657)). Qed.
Lemma lem5183972 (_67658 : real) (x : type1021) (_67656 : real -> Prop) (_67657 : real) : ((term613 x _67657 _67658 _67656) = (term670 x _67657 _67658 _67656)) = ((term667 _67658 x _67656 _67657) = (term667 _67658 x _67656 _67657)).
Proof. exact (MK_COMB (@lem5183909 _67658 x _67656 _67657) (@lem5183971 _67658 x _67656 _67657)). Qed.
Lemma lem5183974 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5183975 (x : Prop) : (x = x) = True.
Proof. exact (@lem5183974 Prop x). Qed.
Lemma lem5183976 (_67658 : real) (x : type1021) (_67656 : real -> Prop) (_67657 : real) : ((term667 _67658 x _67656 _67657) = (term667 _67658 x _67656 _67657)) = True.
Proof. exact (@lem5183975 (term667 _67658 x _67656 _67657)). Qed.
Lemma lem5183977 (x : type1021) (_67657 : real) (_67658 : real) (_67656 : real -> Prop) : ((term613 x _67657 _67658 _67656) = (term670 x _67657 _67658 _67656)) = True.
Proof. exact (TRANS (@lem5183972 _67658 x _67656 _67657) (@lem5183976 _67658 x _67656 _67657)). Qed.
Lemma lem5183978 (x : type1021) (_67657 : real) (_67658 : real) (_67656 : real -> Prop) : True = ((term613 x _67657 _67658 _67656) = (term670 x _67657 _67658 _67656)).
Proof. exact (SYM (@lem5183977 x _67657 _67658 _67656)). Qed.
Lemma lem5183979 (x : type1021) (_67657 : real) (_67658 : real) (_67656 : real -> Prop) : (term613 x _67657 _67658 _67656) = (term670 x _67657 _67658 _67656).
Proof. exact (EQ_MP (@lem5183978 x _67657 _67658 _67656) (@lem0)). Qed.
Lemma lem5183980 (_67657 : real) (_67658 : real) (_67656 : real -> Prop) (x : type1021) (h1 : term461 x) : term670 x _67657 _67658 _67656.
Proof. exact (EQ_MP (@lem5183979 x _67657 _67658 _67656) (@lem5183426 _67657 _67658 _67656 x h1)). Qed.
Lemma lem5183982 (b : Prop) (a : Prop) : (a \/ b) = (term620 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5183983 (x : type1021) (_67657 : real) (_67658 : real) (_67656 : real -> Prop) : (term670 x _67657 _67658 _67656) = (term676 x _67657 _67658 _67656).
Proof. exact (@lem5183982 (term677 x _67657 _67658 _67656) (term59 _67658 _67656)). Qed.
Lemma lem5183985 (a : Prop) (b : Prop) : (term640 a b) = (term641 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5183986 (x : type1021) (_67657 : real) (_67658 : real) (_67656 : real -> Prop) : (term678 x _67657 _67658 _67656) = (term679 x _67657 _67658 _67656).
Proof. exact (@lem5183985 (_67656 = (@EMPTY real)) (term672 x _67657 _67658 _67656)). Qed.
Lemma lem5183988 (a : Prop) (b : Prop) : (term640 a b) = (term641 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5183989 (x : type1021) (_67657 : real) (_67658 : real) (_67656 : real -> Prop) : (term680 x _67657 _67658 _67656) = (term681 x _67657 _67658 _67656).
Proof. exact (@lem5183988 (term552 x _67656 _67657) (term178 _67658 _67656)). Qed.
Lemma lem5183991 (a : Prop) : (term622 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5183992 (x : type1021) (_67656 : real -> Prop) (_67657 : real) : (term682 x _67656 _67657) = (term659 x _67656 _67657).
Proof. exact (@lem5183991 (term659 x _67656 _67657)). Qed.
Lemma lem5183993 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5183994 (x : type1021) (_67656 : real -> Prop) (_67657 : real) : (term683 x _67656 _67657) = (term684 x _67656 _67657).
Proof. exact (MK_COMB (@lem5183993) (@lem5183992 x _67656 _67657)). Qed.
Lemma lem5183996 (a : Prop) : (term622 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5183997 (_67658 : real) (_67656 : real -> Prop) : (term623 _67658 _67656) = (@IN real _67658 _67656).
Proof. exact (@lem5183996 (@IN real _67658 _67656)). Qed.
Lemma lem5183998 (x : type1021) (_67657 : real) (_67658 : real) (_67656 : real -> Prop) : (term681 x _67657 _67658 _67656) = (term685 x _67657 _67658 _67656).
Proof. exact (MK_COMB (@lem5183994 x _67656 _67657) (@lem5183997 _67658 _67656)). Qed.
Lemma lem5183999 (x : type1021) (_67657 : real) (_67658 : real) (_67656 : real -> Prop) : (term680 x _67657 _67658 _67656) = (term685 x _67657 _67658 _67656).
Proof. exact (TRANS (@lem5183989 x _67657 _67658 _67656) (@lem5183998 x _67657 _67658 _67656)). Qed.
Lemma lem5184000 (_67656 : real -> Prop) : (term42 _67656) = (term42 _67656).
Proof. exact (eq_refl (term42 _67656)). Qed.
Lemma lem5184001 (x : type1021) (_67657 : real) (_67658 : real) (_67656 : real -> Prop) : (term679 x _67657 _67658 _67656) = (term686 x _67657 _67658 _67656).
Proof. exact (MK_COMB (@lem5184000 _67656) (@lem5183999 x _67657 _67658 _67656)). Qed.
Lemma lem5184002 (x : type1021) (_67657 : real) (_67658 : real) (_67656 : real -> Prop) : (term678 x _67657 _67658 _67656) = (term686 x _67657 _67658 _67656).
Proof. exact (TRANS (@lem5183986 x _67657 _67658 _67656) (@lem5184001 x _67657 _67658 _67656)). Qed.
Lemma lem5184003 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5184004 (x : type1021) (_67657 : real) (_67658 : real) (_67656 : real -> Prop) : (term687 x _67657 _67658 _67656) = (term688 x _67657 _67658 _67656).
Proof. exact (MK_COMB (@lem5184003) (@lem5184002 x _67657 _67658 _67656)). Qed.
Lemma lem5184005 (_67658 : real) (_67656 : real -> Prop) : (term59 _67658 _67656) = (term59 _67658 _67656).
Proof. exact (eq_refl (term59 _67658 _67656)). Qed.
Lemma lem5184006 (x : type1021) (_67657 : real) (_67658 : real) (_67656 : real -> Prop) : (term676 x _67657 _67658 _67656) = (term689 x _67657 _67658 _67656).
Proof. exact (MK_COMB (@lem5184004 x _67657 _67658 _67656) (@lem5184005 _67658 _67656)). Qed.
Lemma lem5184007 (x : type1021) (_67657 : real) (_67658 : real) (_67656 : real -> Prop) : (term670 x _67657 _67658 _67656) = (term689 x _67657 _67658 _67656).
Proof. exact (TRANS (@lem5183983 x _67657 _67658 _67656) (@lem5184006 x _67657 _67658 _67656)). Qed.
Lemma lem5184009 (x : type1021) (x' : type1023) (y : real) (b : real) (a : real) (s : real -> Prop) (h1 : term461 x) (h2 : term78 y s) (h3 : term280 x') (h4 : term82 y b a s) : term685 x b y s.
Proof. exact (conj (@lem5183825 x x' y b a s h1 h2 h3 h4) (@lem5183832 y b a s h4)). Qed.
Lemma lem5184010 (x : type1021) (x' : type1023) (y : real) (b : real) (a : real) (s : real -> Prop) (h1 : term461 x) (h2 : term78 y s) (h3 : term280 x') (h4 : term82 y b a s) : term686 x b y s.
Proof. exact (conj (@lem5183569 x' y b a s h3 h4) (@lem5184009 x x' y b a s h1 h2 h3 h4)). Qed.
Lemma lem5184012 (_67657 : real) (_67658 : real) (_67656 : real -> Prop) (x : type1021) (h1 : term461 x) : term689 x _67657 _67658 _67656.
Proof. exact (EQ_MP (@lem5184007 x _67657 _67658 _67656) (@lem5183980 _67657 _67658 _67656 x h1)). Qed.
Lemma lem5184013 (b : real) (y : real) (s : real -> Prop) (x : type1021) (h1 : term461 x) : term689 x b y s.
Proof. exact (@lem5184012 b y s x h1). Qed.
Lemma lem5184016 (x : type1021) (x' : type1023) (y : real) (b : real) (a : real) (s : real -> Prop) (h1 : term461 x) (h2 : term78 y s) (h3 : term280 x') (h4 : term82 y b a s) : term59 y s.
Proof. exact (@lem5184013 b y s x h1 (@lem5184010 x x' y b a s h1 h2 h3 h4)). Qed.
Lemma lem5184017 (x : type1021) (x' : type1023) (y : real) (b : real) (a : real) (s : real -> Prop) (h1 : term461 x) (h2 : term280 x') (h3 : term82 y b a s) : term690 y s.
Proof. exact (fun h0 : term78 y s => @lem5184016 x x' y b a s h1 h0 h2 h3). Qed.
Lemma lem5184019 (p : Prop) : (term615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5184020 (y : real) (s : real -> Prop) : (term690 y s) = (term59 y s).
Proof. exact (@lem5184019 (term59 y s)). Qed.
Lemma lem5184021 (x : type1021) (x' : type1023) (y : real) (b : real) (a : real) (s : real -> Prop) (h1 : term461 x) (h2 : term280 x') (h3 : term82 y b a s) : term59 y s.
Proof. exact (EQ_MP (@lem5184020 y s) (@lem5184017 x x' y b a s h1 h2 h3)). Qed.
Lemma lem5184037 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5184038 (_67653 : real) (_67654 : real) (_67655 : real) : (term691 _67654 _67653 _67655) = (term692 _67653 _67654 _67655).
Proof. exact (@lem5184037 (real_le _67653 _67655) (term611 _67654 _67655)). Qed.
Lemma lem5184044 (_67653 : real) (_67654 : real) : (term693 _67653 _67654) = (term693 _67653 _67654).
Proof. exact (eq_refl (term693 _67653 _67654)). Qed.
Lemma lem5184045 (_67653 : real) (_67654 : real) (_67655 : real) : (term610 _67654 _67653 _67655) = (term694 _67653 _67654 _67655).
Proof. exact (MK_COMB (@lem5184044 _67653 _67654) (@lem5184038 _67653 _67654 _67655)). Qed.
Lemma lem5184049 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5184050 (_67653 : real) (_67654 : real) (_67655 : real) : (term694 _67653 _67654 _67655) = (term695 _67653 _67654 _67655).
Proof. exact (@lem5184049 (real_le _67653 _67655) (term611 _67653 _67654) (term611 _67654 _67655)). Qed.
Lemma lem5184066 (_67653 : real) (_67654 : real) (_67655 : real) : (term610 _67654 _67653 _67655) = (term695 _67653 _67654 _67655).
Proof. exact (TRANS (@lem5184045 _67653 _67654 _67655) (@lem5184050 _67653 _67654 _67655)). Qed.
Lemma lem5184067 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5184068 (_67653 : real) (_67654 : real) (_67655 : real) : (term696 _67654 _67653 _67655) = (term697 _67653 _67654 _67655).
Proof. exact (MK_COMB (@lem5184067) (@lem5184066 _67653 _67654 _67655)). Qed.
Lemma lem5184084 (_67653 : real) (_67654 : real) (_67655 : real) : (term695 _67653 _67654 _67655) = (term695 _67653 _67654 _67655).
Proof. exact (eq_refl (term695 _67653 _67654 _67655)). Qed.
Lemma lem5184085 (_67653 : real) (_67654 : real) (_67655 : real) : ((term610 _67654 _67653 _67655) = (term695 _67653 _67654 _67655)) = ((term695 _67653 _67654 _67655) = (term695 _67653 _67654 _67655)).
Proof. exact (MK_COMB (@lem5184068 _67653 _67654 _67655) (@lem5184084 _67653 _67654 _67655)). Qed.
Lemma lem5184087 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5184088 (x : Prop) : (x = x) = True.
Proof. exact (@lem5184087 Prop x). Qed.
Lemma lem5184089 (_67653 : real) (_67654 : real) (_67655 : real) : ((term695 _67653 _67654 _67655) = (term695 _67653 _67654 _67655)) = True.
Proof. exact (@lem5184088 (term695 _67653 _67654 _67655)). Qed.
Lemma lem5184090 (_67653 : real) (_67654 : real) (_67655 : real) : ((term610 _67654 _67653 _67655) = (term695 _67653 _67654 _67655)) = True.
Proof. exact (TRANS (@lem5184085 _67653 _67654 _67655) (@lem5184089 _67653 _67654 _67655)). Qed.
Lemma lem5184091 (_67653 : real) (_67654 : real) (_67655 : real) : True = ((term610 _67654 _67653 _67655) = (term695 _67653 _67654 _67655)).
Proof. exact (SYM (@lem5184090 _67653 _67654 _67655)). Qed.
Lemma lem5184092 (_67653 : real) (_67654 : real) (_67655 : real) : (term610 _67654 _67653 _67655) = (term695 _67653 _67654 _67655).
Proof. exact (EQ_MP (@lem5184091 _67653 _67654 _67655) (@lem0)). Qed.
Lemma lem5184093 (_67653 : real) (_67654 : real) (_67655 : real) (h1 : term58) : term695 _67653 _67654 _67655.
Proof. exact (EQ_MP (@lem5184092 _67653 _67654 _67655) (@lem5183306 _67654 _67653 _67655 h1)). Qed.
Lemma lem5184095 (b : Prop) (a : Prop) : (a \/ b) = (term620 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5184096 (_67654 : real) (_67653 : real) (_67655 : real) : (term695 _67653 _67654 _67655) = (term698 _67654 _67653 _67655).
Proof. exact (@lem5184095 (term160 _67653 _67654 _67655) (real_le _67653 _67655)). Qed.
Lemma lem5184098 (a : Prop) (b : Prop) : (term640 a b) = (term641 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5184099 (_67653 : real) (_67654 : real) (_67655 : real) : (term699 _67653 _67654 _67655) = (term700 _67653 _67654 _67655).
Proof. exact (@lem5184098 (term611 _67653 _67654) (term611 _67654 _67655)). Qed.
Lemma lem5184101 (a : Prop) : (term622 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5184102 (_67653 : real) (_67654 : real) : (term701 _67653 _67654) = (real_le _67653 _67654).
Proof. exact (@lem5184101 (real_le _67653 _67654)). Qed.
Lemma lem5184103 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5184104 (_67653 : real) (_67654 : real) : (term702 _67653 _67654) = (term60 _67653 _67654).
Proof. exact (MK_COMB (@lem5184103) (@lem5184102 _67653 _67654)). Qed.
Lemma lem5184106 (a : Prop) : (term622 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5184107 (_67654 : real) (_67655 : real) : (term701 _67654 _67655) = (real_le _67654 _67655).
Proof. exact (@lem5184106 (real_le _67654 _67655)). Qed.
Lemma lem5184108 (_67653 : real) (_67654 : real) (_67655 : real) : (term700 _67653 _67654 _67655) = (term165 _67653 _67654 _67655).
Proof. exact (MK_COMB (@lem5184104 _67653 _67654) (@lem5184107 _67654 _67655)). Qed.
Lemma lem5184109 (_67653 : real) (_67654 : real) (_67655 : real) : (term699 _67653 _67654 _67655) = (term165 _67653 _67654 _67655).
Proof. exact (TRANS (@lem5184099 _67653 _67654 _67655) (@lem5184108 _67653 _67654 _67655)). Qed.
Lemma lem5184110 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5184111 (_67653 : real) (_67654 : real) (_67655 : real) : (term703 _67653 _67654 _67655) = (term704 _67653 _67654 _67655).
Proof. exact (MK_COMB (@lem5184110) (@lem5184109 _67653 _67654 _67655)). Qed.
Lemma lem5184112 (_67653 : real) (_67655 : real) : (real_le _67653 _67655) = (real_le _67653 _67655).
Proof. exact (eq_refl (real_le _67653 _67655)). Qed.
Lemma lem5184113 (_67654 : real) (_67653 : real) (_67655 : real) : (term698 _67654 _67653 _67655) = (term52 _67654 _67653 _67655).
Proof. exact (MK_COMB (@lem5184111 _67653 _67654 _67655) (@lem5184112 _67653 _67655)). Qed.
Lemma lem5184114 (_67654 : real) (_67653 : real) (_67655 : real) : (term695 _67653 _67654 _67655) = (term52 _67654 _67653 _67655).
Proof. exact (TRANS (@lem5184096 _67654 _67653 _67655) (@lem5184113 _67654 _67653 _67655)). Qed.
Lemma lem5184116 (x : type1021) (x' : type1023) (y : real) (b : real) (a : real) (s : real -> Prop) (h1 : term461 x) (h2 : term280 x') (h3 : term82 y b a s) : term705 a y s.
Proof. exact (conj (@lem5183506 y b a s h3) (@lem5184021 x x' y b a s h1 h2 h3)). Qed.
Lemma lem5184118 (_67654 : real) (_67653 : real) (_67655 : real) (h1 : term58) : term52 _67654 _67653 _67655.
Proof. exact (EQ_MP (@lem5184114 _67654 _67653 _67655) (@lem5184093 _67653 _67654 _67655 h1)). Qed.
Lemma lem5184119 (y : real) (a : real) (s : real -> Prop) (h1 : term58) : term706 y a s.
Proof. exact (@lem5184118 y a (sup s) h1). Qed.
Lemma lem5184122 (x : type1021) (x' : type1023) (y : real) (b : real) (a : real) (s : real -> Prop) (h1 : term461 x) (h2 : term58) (h3 : term280 x') (h4 : term82 y b a s) : term59 a s.
Proof. exact (@lem5184119 y a s h2 (@lem5184116 x x' y b a s h1 h3 h4)). Qed.
Lemma lem5184123 (x : type1021) (x' : type1023) (y : real) (b : real) (a : real) (s : real -> Prop) (h1 : term461 x) (h2 : term58) (h3 : term280 x') (h4 : term82 y b a s) : term690 a s.
Proof. exact (fun h0 : term78 a s => @lem5184122 x x' y b a s h1 h2 h3 h4). Qed.
Lemma lem5184125 (p : Prop) : (term615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5184126 (a : real) (s : real -> Prop) : (term690 a s) = (term59 a s).
Proof. exact (@lem5184125 (term59 a s)). Qed.
Lemma lem5184127 (x : type1021) (x' : type1023) (y : real) (b : real) (a : real) (s : real -> Prop) (h1 : term461 x) (h2 : term58) (h3 : term280 x') (h4 : term82 y b a s) : term59 a s.
Proof. exact (EQ_MP (@lem5184126 a s) (@lem5184123 x x' y b a s h1 h2 h3 h4)). Qed.
Lemma lem5184130 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5184132 (a : real) (s : real -> Prop) : (term78 a s) = (term707 a s).
Proof. exact (@lem5184130 (term59 a s)). Qed.
Lemma lem5184135 (y : real) (b : real) (a : real) (s : real -> Prop) (h1 : term82 y b a s) : term707 a s.
Proof. exact (EQ_MP (@lem5184132 a s) (@lem5183308 y b a s h1)). Qed.
Lemma lem5184138 (x : type1021) (x' : type1023) (y : real) (b : real) (a : real) (s : real -> Prop) (h1 : term461 x) (h2 : term58) (h3 : term280 x') (h4 : term82 y b a s) : False.
Proof. exact (@lem5184135 y b a s h4 (@lem5184127 x x' y b a s h1 h2 h3 h4)). Qed.
Lemma lem5184139 (x : type1021) (x' : type1023) (y : real) (b : real) (a : real) (s : real -> Prop) (h1 : term461 x) (h2 : term58) (h3 : term280 x') (h4 : term82 y b a s) : term708.
Proof. exact (fun h0 : ~ False => @lem5184138 x x' y b a s h1 h2 h3 h4). Qed.
Lemma lem5184141 (p : Prop) : (term615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5184142 : term708 = False.
Proof. exact (@lem5184141 False). Qed.
Lemma lem5184143 (x : type1021) (x' : type1023) (y : real) (b : real) (a : real) (s : real -> Prop) (h1 : term461 x) (h2 : term58) (h3 : term280 x') (h4 : term82 y b a s) : False.
Proof. exact (EQ_MP (@lem5184142) (@lem5184139 x x' y b a s h1 h2 h3 h4)). Qed.
Lemma lem5184144 (x : type1021) (x' : type1023) (y : real) (b : real) (a : real) (s : real -> Prop) (h1 : term461 x) (h2 : term58) (h3 : term280 x') (h4 : term82 y b a s) : (term82 y b a s) = False.
Proof. exact (prop_ext (fun h5 : term82 y b a s => @lem5184143 x x' y b a s h1 h2 h3 h4) (fun h5 : False => @lem5182935 y b a s h4)). Qed.
Lemma lem5184145 (x : type1021) (x' : type1023) (y : real) (b : real) (a : real) (s : real -> Prop) (h1 : term461 x) (h2 : term58) (h3 : term280 x') (h4 : term82 y b a s) : False.
Proof. exact (EQ_MP (@lem5184144 x x' y b a s h1 h2 h3 h4) (@lem5182935 y b a s h4)). Qed.
Lemma lem5184146 (x : type1021) (x' : type1023) (y : real) (b : real) (a : real) (s : real -> Prop) (h1 : term461 x) (h2 : term58) (h3 : term280 x') (h4 : term82 y b a s) : (term280 x') = False.
Proof. exact (prop_ext (fun h5 : term280 x' => @lem5184145 x x' y b a s h1 h2 h3 h4) (fun h5 : False => @lem5182888 x' h3)). Qed.
Lemma lem5184147 (x : type1021) (x' : type1023) (y : real) (b : real) (a : real) (s : real -> Prop) (h1 : term461 x) (h2 : term58) (h3 : term280 x') (h4 : term82 y b a s) : False.
Proof. exact (EQ_MP (@lem5184146 x x' y b a s h1 h2 h3 h4) (@lem5182888 x' h3)). Qed.
Lemma lem5184148 (x : type1021) (x' : type1023) (y : real) (b : real) (a : real) (s : real -> Prop) (h1 : term461 x) (h2 : term58) (h3 : term280 x') (h4 : term82 y b a s) : (term461 x) = False.
Proof. exact (prop_ext (fun h5 : term461 x => @lem5184147 x x' y b a s h1 h2 h3 h4) (fun h5 : False => @lem5182843 x h1)). Qed.
Lemma lem5184149 (x : type1021) (x' : type1023) (y : real) (b : real) (a : real) (s : real -> Prop) (h1 : term461 x) (h2 : term58) (h3 : term280 x') (h4 : term82 y b a s) : False.
Proof. exact (EQ_MP (@lem5184148 x x' y b a s h1 h2 h3 h4) (@lem5182843 x h1)). Qed.
Lemma lem5184150 (x : type1021) (b : real) (a : real) (s : real -> Prop) (x' : type1023) (h1 : term461 x) (h2 : term58) (h3 : term92 b a s) (h4 : term280 x') : False.
Proof. exact (ex_elim (@lem5182707 b a s h3) (fun y : real => fun h0 : term91 b a s y => @lem5184149 x x' y b a s h1 h2 h4 h0)). Qed.
Lemma lem5184151 (x : type1021) (a : real) (s : real -> Prop) (x' : type1023) (h1 : term461 x) (h2 : term58) (h3 : term99 a s) (h4 : term280 x') : False.
Proof. exact (ex_elim (@lem5182706 a s h3) (fun b : real => fun h0 : term98 a s b => @lem5184150 x b a s x' h1 h2 h0 h4)). Qed.
Lemma lem5184152 (x : type1021) (s : real -> Prop) (x' : type1023) (h1 : term461 x) (h2 : term58) (h3 : term106 s) (h4 : term280 x') : False.
Proof. exact (ex_elim (@lem5182705 s h3) (fun a : real => fun h0 : term105 s a => @lem5184151 x a s x' h1 h2 h0 h4)). Qed.
Lemma lem5184153 (x : type1021) (x' : type1023) (h1 : term461 x) (h2 : term58) (h3 : term10) (h4 : term280 x') : False.
Proof. exact (ex_elim (@lem5181836 h3) (fun s : real -> Prop => fun h0 : term113 s => @lem5184152 x s x' h1 h2 h0 h4)). Qed.
Lemma lem5184154 (x : type1021) (h1 : term11) (h2 : term461 x) (h3 : term58) (h4 : term10) : False.
Proof. exact (ex_elim (@lem5182173 h1) (fun x' : type1023 => fun h0 : term282 x' => @lem5184153 x x' h2 h3 h4 h0)). Qed.
Lemma lem5184155 (h1 : term11) (h2 : term18) (h3 : term58) (h4 : term10) : False.
Proof. exact (ex_elim (@lem5182702 h2) (fun x : type1021 => fun h0 : term463 x => @lem5184154 x h1 h0 h3 h4)). Qed.
Lemma lem5184156 (h1 : term11) (h2 : term58) (h3 : term10) : term16.
Proof. exact (fun h0 : term18 => @lem5184155 h1 h0 h2 h3). Qed.
Lemma lem5184157 : term16 = term17.
Proof. exact (@lem69 term18). Qed.
Lemma lem5184158 (h1 : term11) (h2 : term58) (h3 : term10) : term17.
Proof. exact (EQ_MP (@lem5184157) (@lem5184156 h1 h2 h3)). Qed.
Lemma lem5184159 (h1 : term58) (h2 : term10) : term21.
Proof. exact (fun h0 : term11 => @lem5184158 h0 h1 h2). Qed.
Lemma lem5184160 (h1 : term10) : term24.
Proof. exact (fun h0 : term58 => @lem5184159 h0 h1). Qed.
Lemma lem5184161 : term26.
Proof. exact (fun h0 : term10 => @lem5184160 h0). Qed.
Lemma lem5184162 : term12.
Proof. exact (EQ_MP (@lem5181349) (@lem5184161)). Qed.
Lemma lem5184164 : term12.
Proof. exact (@lem5180977 (@lem5184162)). Qed.
Lemma lem5184165 (h1 : term10) : term23.
Proof. exact (@lem5184164 (@lem5180959 h1)). Qed.
Lemma lem5184166 (h1 : term10) : term20.
Proof. exact (@lem5184165 h1 (@lem1339577)). Qed.
Lemma lem5184167 (h1 : term10) : term16.
Proof. exact (@lem5184166 h1 (@lem5180960)). Qed.
Lemma lem5184168 (h1 : term10) : False.
Proof. exact (@lem5184167 h1 (@lem5136700)). Qed.
Lemma lem5184169 (h1 : term10) : term10 = False.
Proof. exact (prop_ext (fun h2 : term10 => @lem5184168 h1) (fun h2 : False => @lem5180959 h1)). Qed.
Lemma lem5184170 (h1 : term10) : False.
Proof. exact (EQ_MP (@lem5184169 h1) (@lem5180959 h1)). Qed.
Lemma lem5184171 : term9.
Proof. exact (fun h0 : term10 => @lem5184170 h0). Qed.
Lemma lem5184172 : term8.
Proof. exact (EQ_MP (@lem5180958) (@lem5184171)). Qed.
